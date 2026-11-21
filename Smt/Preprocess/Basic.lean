/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Basic
public meta import Lean.Meta.Basic
public meta import Lean.Meta.Tactic.Simp
public import Lean.Meta.InferType
public meta import Lean.Meta.InferType

public meta section

namespace Smt.Preprocess

open Lean

structure Result where
  map : Std.HashMap Expr (Array Expr)
  hs : Array Expr
  mv : MVarId

/-- Give each non-local hint a local declaration so that it can be reverted. Record
the first declaration for each expression, including when the same hint occurs twice. -/
def assertHints (mv : MVarId) (hs : Array Expr) :
    MetaM (Array FVarId × Std.HashMap Expr Expr × MVarId) := do
  let (locals, others) := hs.partition Expr.isFVar
  let hypotheses ← others.mapM fun h => do
    return { userName := .anonymous, type := ← Meta.inferType h, value := h : Meta.Hypothesis }
  let (fresh, mv) ← mv.assertHypotheses hypotheses
  let mut originalToLocal : Std.HashMap Expr Expr := {}
  for h in locals do originalToLocal := originalToLocal.insert h h
  for (h, fv) in others.zip fresh do originalToLocal := originalToLocal.insertIfNew h (.fvar fv)
  return (locals.map Expr.fvarId! ++ fresh, originalToLocal, mv)

/-- Translate selected hints to their reintroduced declarations and preserve provenance
for unsat cores. The two maps straddle reversion and reintroduction. -/
def restoreHints (hs : Array Expr) (originalToLocal localToNew : Std.HashMap Expr Expr) :
    Array Expr × Std.HashMap Expr (Array Expr) := Id.run do
  let originalToNew := originalToLocal.fold (init := localToNew) fun map h localHint =>
    map.insert h (map.getD localHint localHint)
  let provenance := originalToNew.fold (init := {}) fun map h h' => map.insert h' #[h]
  return (hs.map fun h => originalToNew.getD h h, provenance)

/-- Run the ordered base and optional Fin rewrites in one pass over the target. -/
def simpTargetWithExtensions (mv : MVarId) (base fin : Name) (enableFin : Bool) : MetaM MVarId := do
  let names := if enableFin then #[base, fin] else #[base]
  let mut theorems := #[]
  let mut simprocs := #[]
  for name in names do
    let some thms ← Meta.getSimpExtension? name | throwError "missing {name} simp extension"
    let some procs ← Meta.Simp.getSimprocExtension? name | throwError "missing {name} simproc extension"
    theorems := theorems.push (← thms.getTheorems)
    simprocs := simprocs.push (← procs.getSimprocs)
  let ctx ← Meta.Simp.mkContext { zeta := false, singlePass := true } theorems (← Meta.getSimpCongrTheorems)
  let (some mv, _) ← Meta.simpTarget mv ctx simprocs (mayCloseGoal := false)
    | throwError "[{base}] simplification failed"
  return mv

/-- Return all propositions in the local context. -/
def getPropHyps : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail do
      if ← pure !(isNonEmpty localDecl.type) <&&> Meta.isProp localDecl.type then
        result := result.push localDecl.fvarId
  return result
where
  isNonEmpty (e : Expr) : Bool :=
  match e with
  | .app (.const ``Nonempty _) _ => true
  | .forallE _ _ b _ => isNonEmpty b
  | _ => false

def traceApplySteps (r : Except Exception Result) : MetaM MessageData :=
  return match r with
    | .ok r    => m!"after steps: {r.mv}"
    | .error _ => m!"{bombEmoji}"

def applySteps (mv : MVarId) (hs : Array Expr) (steps : Array (MVarId → Array Expr → MetaM Result)) : MetaM Result :=
  withTraceNode `smt.preprocess traceApplySteps do
  if h : 0 < steps.size then
    let mut { map, hs, mv } ← steps[0] mv hs
    for step in steps[1:] do
      let ⟨map', hs', mv'⟩ ← step mv hs
      map := compose map map'
      hs := hs'
      mv := mv'
    return { map, hs, mv }
  else
    return Result.mk {} #[] mv
where
  compose (m₁ m₂ : Std.HashMap Expr (Array Expr)) : Std.HashMap Expr (Array Expr) :=
    m₂.fold (init := m₁) fun map k v =>
      map.insert k (v.map fun x => m₁.getD x #[x]).flatten

end Smt.Preprocess
