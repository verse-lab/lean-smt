/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp
public import Smt.Preprocess.Basic
public meta import Smt.Preprocess.Basic
public import Smt.Preprocess.Embedding.Attribute
public meta import Smt.Preprocess.Embedding.Attribute

public meta section

private def Lean.Expr.contains (e : Expr) (p : Expr → Bool) : Bool :=
  (e.find? p).isSome

namespace Smt.Preprocess

open Lean

private def isFin (e : Expr) : Bool := e.isAppOfArity ``Fin 1

def hasType (e : Expr) (p : Expr → Bool) : Bool :=
  match e with
  | .forallE _ t b _ => p t || hasType b p
  | _                => p e

def hasReturnType (e : Expr) (p : Expr → Bool) : Bool :=
  match e with
  | .forallE _ _ b _ => hasReturnType b p
  | _                => p e

/-- Even an unused `x : Fin n` witnesses `0 < n`. -/
def finWitnesses : MetaM (Array FVarId) := do
  return (← getLCtx).foldl (init := #[]) fun ids decl =>
    if isFin decl.type then ids.push decl.fvarId else ids

def embedding (mv : MVarId) (hs : Array Expr) : MetaM Result := mv.withContext do
  -- Find all free vars to revert in `hs` and `mv`.
  let ts ← hs.mapM Meta.inferType
  let used := (ts.push (← mv.getType) ++ (← finWitnesses).map Expr.fvar).foldl Lean.collectFVars {}
  -- A symbolic Fin bound can occur only in the type of a function argument.
  let used ← used.addDependencies
  -- Check if we need to do anything.
  let bts := if (← getEnv).contains `Real then  #[``Nat, ``Rat, ``Bool] else #[``Nat, ``Bool]
  let fvts ← used.fvarIds.mapM FVarId.getType
  if !(fvts ++ ts.push (← mv.getType)).any (·.contains fun e => isFin e || (bts.map (.const · [])).contains e) then
    return ⟨{}, hs, mv⟩
  let hasFin := (fvts ++ ts.push (← mv.getType)).any (·.contains isFin)
  -- Register actual witnesses of abstract argument types before reverting their values.
  -- The instances have type `Nonempty α` and stay available while simplifying under binders.
  let mut witnesses : Array Meta.Hypothesis := #[]
  if hasFin then
    for fv in used.fvarIds do
      let α ← fv.getType
      if α.isFVar && (← Meta.inferType α).isType && !witnesses.any (·.type.appArg! == α) then
        let value ← Meta.mkAppM ``Nonempty.intro #[.fvar fv]
        witnesses := witnesses.push {
          userName := .anonymous, type := ← Meta.inferType value, value, binderInfo := .instImplicit }
  let (_, mv) ← mv.assertHypotheses witnesses
  -- Find the embedding simp theorems.
  let some thmsExt ← Meta.getSimpExtension? `embedding | throwError "embedding simp extension not found"
  let some procsExt ← Meta.Simp.getSimprocExtension? `embedding | throwError "embedding simproc extension not found"
  let simpTheorems := #[← thmsExt.getTheorems]
  let simpProcs := #[← procsExt.getSimprocs]
  -- Assert all hypotheses that are not free vars.
  let (hs₁, hs₂) := hs.partition Expr.isFVar
  let ts₂ ← hs₂.mapM Meta.inferType
  let as₂ : Array Meta.Hypothesis := (hs₂.zip ts₂).map fun (h, t) => { userName := .anonymous, type := t, value := h }
  let (fvs₂, mv) ← mv.assertHypotheses as₂
  -- Build map from new hypotheses to old ones.
  let inverseMap₁ : Std.HashMap Expr Expr := hs.foldl (init := {}) fun map h =>
    match hs₂.findIdx? (· == h) with
    | some idx => map.insert h (.fvar fvs₂[idx]!)
    | none => map.insert h h
  -- Revert free vars in `hs` and `mv`.
  let used := (hs₁ ++ fvs₂.map Expr.fvar).foldl Lean.collectFVars used
  -- Revert all dependencies in local-context order, including instance arguments.
  let fvs ← mv.withContext <| used.fvarIds.filterM fun fv => do
    let ty ← fv.getType
    return !(hasFin && ty.isSort && !ty.isProp)
  let (fvs, mv) ← mv.revert fvs false
  -- Simplify the goal using the embedding theorems.
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx ← Meta.Simp.mkContext { zeta := false, singlePass := true } simpTheorems congrTheorems
  let (some mv, _) ← Meta.simpTarget mv ctx simpProcs (mayCloseGoal := false) | throwError "[embedding] simplification failed"
  -- SMT sorts are inhabited. Sending a residual `Fin` as an uninterpreted sort could
  -- therefore change the meaning of an unsupported higher-order or dependent signature.
  if let some fin := (← mv.getType).find? isFin then
    throwError "[embedding] unsupported occurrence of {fin} after embedding"
  -- Extend `fvs` to account for `nonneg` assumptions.
  let bts := bts.pop -- Do not consider `Bool` for assumptions.
  let mut fvs' : Array (Option FVarId) := #[]
  for fv in fvs do
    fvs' := fvs'.push (some fv)
    let t ← fv.getType
    if hasReturnType t (fun e => isFin e || (bts.map (.const · [])).contains e) then
      fvs' := fvs'.push none
  -- Re-introduce all free vars (and their `nonneg` assumptions).
  let (fvs'', mv) ← mv.introNP fvs'.size
  -- Compose the final map from new free vars to old ones.
  -- We do not need to map `nonneg` assumptions. Since `nonneg` assumptions are auxiliary,
  -- We can always provide all of them to the SMT solver without affecting the unsat core.
  let (inverseMap₂, hs') := (fvs'.zip fvs'').foldl (init := ({}, #[])) fun (map, hs') (of, to) =>
    match of with
    | some of => (map.insert (.fvar of) (.fvar to), hs')
    | none    => (map, hs'.push (.fvar to))
  let inverseMap := compose inverseMap₁ inverseMap₂
  let hs' := hs' ++ hs.map fun h => inverseMap[h]?.getD h
  let map := (inverse inverseMap).fold (init := {}) fun map k v => map.insert k #[v]
  return { map := map, hs := hs', mv }
where
  compose (m₁ m₂ : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m₁.fold (init := m₂) fun map k v =>
      map.insert k (map[v]?.getD v)
  inverse (m : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m.fold (init := {}) fun map k v =>
      map.insert v k

end Smt.Preprocess
