/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Assumption
public meta import Lean.Meta.Tactic.Delta
public meta import Lean.Meta.LitValues
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

/-- Inspect a first-order function signature without introducing hypothetical instances from
its arguments. Unfold type aliases on the arrow spine and at the result. -/
def functionSignature (type : Expr) : MetaM (Option (Array Expr × Expr)) := do
  let mut result ← Meta.whnf type
  let mut domains := #[]
  while let .forallE _ domain body _ := result do
    if body.hasLooseBVars then return none
    domains := domains.push domain
    result ← Meta.whnf body
  return some (domains, result)

-- Fin type aliases may occur solely under a quantifier, including an unused binder.
private partial def namesFin (env : Environment) (name : Name) (seen : NameSet := {}) : Bool := Id.run do
  if (``Fin).isPrefixOf name then return true
  if seen.contains name then return false
  let some (.defnInfo info) := env.find? name | return false
  let codomain := info.type.getForallBody
  unless codomain.isSort && !codomain.isProp do return false
  let seen := seen.insert name
  return (info.value.find? fun e => e.constName?.any (fun n => namesFin env n seen)).isSome

private def mentionsFin (es : Array Expr) : MetaM Bool := do
  let env ← getEnv
  return es.any (·.contains fun e => e.constName?.any (fun n => namesFin env n))

/-- A Fin value witnesses a positive bound. A Fin-valued function does so when each of its
arguments has a witness. Keep that evidence through cleanup, including unused local values. -/
def finContext (roots : Array Expr) : MetaM (Bool × Array FVarId) := do
  let used ← (roots.foldl Lean.collectFVars {}).addDependencies
  let types ← used.fvarIds.mapM FVarId.getType
  let mut finite ← mentionsFin (roots ++ types)
  let mut keep := #[]
  for decl in ← getLCtx do
    if !finite && decl.type.hasAnyFVar used.fvarSet.contains then
      finite ← mentionsFin #[decl.type]
    if ← Meta.isProp decl.type then continue
    let some (domains, result) ← functionSignature decl.type | continue
    unless isFin result && domains.size ≤ 5 do continue
    let bound := result.appArg!
    unless used.fvarSet.contains decl.fvarId || bound.hasAnyFVar used.fvarSet.contains ||
        (!bound.hasFVar && (← Meta.getNatValue? bound) == some 0) do continue
    let mut witnesses := #[decl.fvarId]
    for domain in domains do
      if let some fv ← Meta.findLocalDeclWithType? domain then
        witnesses := witnesses.push fv
        continue
      let nonempty ← Meta.mkAppM ``Nonempty #[domain]
      if let some fv ← Meta.findLocalDeclWithType? nonempty then
        witnesses := witnesses.push fv
      else if let some inst ← Meta.synthInstance? nonempty then
        witnesses := witnesses ++ (Lean.collectFVars {} inst).fvarIds
      else
        witnesses := #[]
        break
    keep := keep ++ witnesses
  -- Reconstruction can need an otherwise unused witness of an abstract SMT sort.
  -- Only preserve witnesses of type parameters occurring in this Fin query.
  if finite || !keep.isEmpty then
    for decl in ← getLCtx do
      let t := decl.type
      let carrier := if t.isAppOfArity ``Nonempty 1 || t.isAppOfArity ``Inhabited 1 then t.appArg! else t
      if carrier.isFVar && used.fvarSet.contains carrier.fvarId! && (← Meta.inferType carrier).isType then
        keep := keep.push decl.fvarId
  return (finite || !keep.isEmpty, keep)

private def addWitness (e : Expr) : StateRefT (Array Meta.Hypothesis) MetaM Unit := do
  let t ← Meta.inferType e
  let value ← if t.isAppOfArity ``Nonempty 1 then pure e
    else if t.isType then
      let some inst ← Meta.synthInstance? (← Meta.mkAppM ``Nonempty #[e]) | return
      pure inst
    else if t.isFVar && (← Meta.inferType t).isType then Meta.mkAppM ``Nonempty.intro #[e]
    else return
  let type ← Meta.inferType value
  unless (← get).any (·.type == type) do
    modify (·.push { userName := .anonymous, type, value, binderInfo := .instImplicit })

def embeddingWithFin (enableFin : Bool) (mv : MVarId) (hs : Array Expr) : MetaM Result := mv.withContext do
  -- Find all free vars to revert in `hs` and `mv`.
  let ts ← hs.mapM Meta.inferType
  let roots := (ts.push (← mv.getType)).foldl Lean.collectFVars {}
  let (hasFin, finite) ← if enableFin then finContext (ts.push (← mv.getType)) else pure (false, #[])
  -- A symbolic Fin bound can occur only in the type of a function argument.
  let used ← ((finite.map Expr.fvar).foldl Lean.collectFVars roots).addDependencies
  -- Check if we need to do anything.
  let bts := if (← getEnv).contains `Real then  #[``Nat, ``Rat, ``Bool] else #[``Nat, ``Bool]
  let fvts ← used.fvarIds.mapM FVarId.getType
  let types := fvts ++ ts.push (← mv.getType)
  unless hasFin || types.any (·.contains ((bts.map (.const · [])).contains ·)) do
    return { map := {}, hs, mv }
  -- Register actual witnesses of abstract argument types before reverting their values.
  -- The instances have type `Nonempty α` and stay available while simplifying under binders.
  let collect : StateRefT (Array Meta.Hypothesis) MetaM Unit := do
    if hasFin then
      for fv in used.fvarIds do addWitness (.fvar fv)
      for h in hs do addWitness h
      -- Even when f : Fin n → α is the only field with codomain α, an actual f i
      -- witnesses α. Applications containing bound variables cannot supply that evidence.
      if fvts.any Expr.isType then
        for t in ts.push (← mv.getType) do
          t.forEach fun e => do
            if e.isApp && e.getAppFn.isFVar && !e.hasLooseBVars then addWitness e
  let (_, witnesses) ← collect.run #[]
  let (_, mv) ← mv.assertHypotheses witnesses
  -- Find the embedding simp theorems.
  let some thmsExt ← Meta.getSimpExtension? `embedding | throwError "embedding simp extension not found"
  let some procsExt ← Meta.Simp.getSimprocExtension? `embedding | throwError "embedding simproc extension not found"
  let mut simpTheorems := #[← thmsExt.getTheorems]
  let mut simpProcs := #[← procsExt.getSimprocs]
  if hasFin then
    let some finThms ← Meta.getSimpExtension? `fin_embedding | throwError "missing fin_embedding simp extension"
    let some finProcs ← Meta.Simp.getSimprocExtension? `fin_embedding | throwError "missing fin_embedding simprocs"
    simpTheorems := simpTheorems.push (← finThms.getTheorems)
    simpProcs := simpProcs.push (← finProcs.getSimprocs)
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
  let env ← getEnv
  let mv ← if hasFin then mv.deltaTarget (fun n => !(``Fin).isPrefixOf n && namesFin env n)
    else pure mv
  -- Simplify the goal using the embedding theorems.
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx ← Meta.Simp.mkContext { zeta := false, singlePass := true } simpTheorems congrTheorems
  let (some mv, _) ← Meta.simpTarget mv ctx simpProcs (mayCloseGoal := false) | throwError "[embedding] simplification failed"
  -- SMT sorts are inhabited. Sending a residual `Fin` as an uninterpreted sort could
  -- therefore change the meaning of an unsupported higher-order or dependent signature.
  let residual := (← mv.getType).find? isFin
  -- Extend `fvs` to account for `nonneg` assumptions.
  let bts := bts.pop -- Do not consider `Bool` for assumptions.
  let mut fvs' : Array (Option FVarId) := #[]
  for fv in fvs do
    fvs' := fvs'.push (some fv)
    let t ← fv.getType
    let result ← if hasFin then pure ((← functionSignature t).map (·.2)) else pure none
    if hasReturnType t ((bts.map (.const · [])).contains ·) || result.any isFin then
      fvs' := fvs'.push none
  -- Re-introduce all free vars (and their `nonneg` assumptions).
  let (fvs'', mv) ← try mv.introNP fvs'.size catch ex =>
    if let some fin := residual then throwError "[embedding] unsupported occurrence of {fin} after embedding"
    throw ex
  -- Compose the final map from new free vars to old ones.
  -- We do not need to map `nonneg` assumptions. Since `nonneg` assumptions are auxiliary,
  -- We can always provide all of them to the SMT solver without affecting the unsat core.
  let (inverseMap₂, hs') := (fvs'.zip fvs'').foldl (init := ({}, #[])) fun (map, hs') (of, to) =>
    match of with
    | some of => (map.insert (.fvar of) (.fvar to), hs')
    | none    => (map, hs'.push (.fvar to))
  let inverseMap := compose inverseMap₁ inverseMap₂
  -- Use Nonempty evidence through the local instances above. There is no SMT predicate
  -- for Lean's universe-polymorphic Nonempty.
  let hs ← if hasFin then hs.filterM (fun h => do return !(← Meta.inferType h).isAppOfArity ``Nonempty 1)
    else pure hs
  let hs' := hs' ++ hs.map fun h => inverseMap[h]?.getD h
  if residual.isSome then mv.withContext do
    -- Reverting a symbolic bound also reverts unused dependent declarations (for
    -- example representation instances). Only the selected facts and their dependencies
    -- reach the solver. Check those declarations after restoring the local context.
    let roots := (← hs'.mapM Meta.inferType) ++ hs'.push (← mv.getType)
    let used ← (roots.foldl Lean.collectFVars {}).addDependencies
    let mut terms := roots
    for fv in used.fvarIds do
      let decl ← fv.getDecl
      terms := terms.push decl.type
      if let some value := decl.value? then terms := terms.push value
    for term in terms do
      if let some fin := term.find? isFin then
        throwError "[embedding] unsupported occurrence of {fin} after embedding"
  let map := (inverse inverseMap).fold (init := {}) fun map k v => map.insert k #[v]
  return { map := map, hs := hs', mv }
where
  compose (m₁ m₂ : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m₁.fold (init := m₂) fun map k v =>
      map.insert k (map[v]?.getD v)
  inverse (m : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m.fold (init := {}) fun map k v =>
      map.insert v k

def embedding := embeddingWithFin true

end Smt.Preprocess
