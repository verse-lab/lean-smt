/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean.Meta.Tactic.Simp
import Smt.Preprocess.Basic
import Smt.Preprocess.Embedding.Attribute

private def Lean.Expr.contains (e : Expr) (p : Expr → Bool) : Bool :=
  (e.find? p).isSome

namespace Smt.Preprocess

open Lean

private def isFinType (e : Expr) : Bool :=
  match e.consumeMData with
  | .app (.const ``Fin []) _ => true
  | _                        => false

private def isIntType (e : Expr) : Bool :=
  e.consumeMData.isConstOf ``Int

private def isNatType (e : Expr) : Bool :=
  e.consumeMData.isConstOf ``Nat

private def isBoolType (e : Expr) : Bool :=
  e.consumeMData.isConstOf ``Bool

private def isPropType (e : Expr) : Bool :=
  e.consumeMData.isProp

private def isRatType (e : Expr) : Bool :=
  e.consumeMData.isConstOf ``Rat

private def isRealType (e : Expr) : Bool :=
  e.consumeMData.isConstOf `Real

private def isKnownModelType (e : Expr) : Bool :=
  isPropType e ||
  isBoolType e ||
  isIntType e ||
  isNatType e ||
  isRatType e ||
  isRealType e ||
  isFinType e

private partial def isUninterpretedModelType (e : Expr) : Bool :=
  match e.consumeMData with
  | .fvar _ | .sort _ => true
  | .forallE _ arg body _ =>
    isUninterpretedModelType arg && isUninterpretedModelType body
  | _ => false

private def isEmbeddingType (includeRat : Bool) (e : Expr) : Bool :=
  e.consumeMData.isConstOf ``Nat ||
  e.consumeMData.isConstOf ``Bool ||
  (includeRat && e.consumeMData.isConstOf ``Rat) ||
  isFinType e

private def isEmbeddingAssumptionType (includeRat : Bool) (e : Expr) : Bool :=
  e.consumeMData.isConstOf ``Nat ||
  (includeRat && e.consumeMData.isConstOf ``Rat) ||
  isFinType e

private partial def mayHaveEmbeddedModelOrigin (valueType originType : Expr) : Bool :=
  let valueType := valueType.consumeMData
  let originType := originType.consumeMData
  valueType == originType ||
  (isPropType valueType && isBoolType originType) ||
  (isBoolType valueType && isPropType originType) ||
  (isIntType valueType && isNatType originType) ||
  (isNatType valueType && isIntType originType) ||
  (isIntType valueType && isFinType originType) ||
  (isFinType valueType && isIntType originType) ||
  (isRealType valueType && isRatType originType) ||
  (isRatType valueType && isRealType originType) ||
  (!isKnownModelType valueType && !isKnownModelType originType &&
    isUninterpretedModelType valueType && isUninterpretedModelType originType) ||
  match valueType, originType with
  | .forallE _ valueArg valueRet _, .forallE _ originArg originRet _ =>
    mayHaveEmbeddedModelOrigin originArg valueArg &&
    mayHaveEmbeddedModelOrigin valueRet originRet
  | _, _ => false

private def containsFVarId (fvs : Array FVarId) (fv : FVarId) : Bool :=
  fvs.any (· == fv)

private def collectModelOrigins
    (proofFvs : Array FVarId) (oldFvs : Array (Option (FVarId × Expr))) :
    Array (FVarId × Expr) :=
  oldFvs.filterMap fun
    | some (oldFv, oldType) =>
      if containsFVarId proofFvs oldFv then none else some (oldFv, oldType)
    | none => none

private def buildModelMap
    (proofFvs : Array FVarId) (oldFvs : Array (Option (FVarId × Expr))) (newFvs : Array FVarId) :
    MetaM (Std.HashMap Expr Expr) := do
  let mut map := {}
  let origins := collectModelOrigins proofFvs oldFvs
  let mut originIdx := 0
  for newFv in newFvs do
    if originIdx < origins.size then
      let (oldFv, oldType) := origins[originIdx]!
      let newType ← newFv.getType
      if mayHaveEmbeddedModelOrigin newType oldType then
        map := map.insert (.fvar newFv) (.fvar oldFv)
        originIdx := originIdx + 1
      else
        trace[smt.preprocess]
          "dropping auxiliary model binder {Expr.fvar newFv} : {newType}; next origin is {Expr.fvar oldFv} : {oldType}"
  return map

def hasType (e : Expr) (p : Expr → Bool) : Bool :=
  match e with
  | .forallE _ t b _ => p t || hasType b p
  | _                => p e

def hasReturnType (e : Expr) (p : Expr → Bool) : Bool :=
  match e with
  | .forallE _ _ b _ => hasReturnType b p
  | _                => p e

def embedding (mv : MVarId) (hs : Array Expr) : MetaM Result :=
  withTraceNode (`smt.perf.preprocess ++ `embedding) (fun _ => return "embedding") do
  mv.withContext do
  -- Find all free vars to revert in `hs` and `mv`.
  let ts ← hs.mapM Meta.inferType
  let ⟨_, _, fvs⟩ := (ts.push (← mv.getType)).foldl Lean.collectFVars {}
  let fvs ← Meta.sortFVarIds fvs
  -- Check if we need to do anything.
  let includeRat := (← getEnv).contains `Real
  let fvts ← fvs.mapM FVarId.getType
  if !(fvts ++ ts.push (← mv.getType)).any (·.contains (isEmbeddingType includeRat)) then
    return { map := {}, modelMap := {}, hs, mv }
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
  let proofFvs := hs₁.map Expr.fvarId! ++ fvs₂
  -- Build map from new hypotheses to old ones.
  let inverseMap₁ : Std.HashMap Expr Expr := hs.foldl (init := {}) fun map h =>
    match hs₂.findIdx? (· == h) with
    | some idx => map.insert h (.fvar fvs₂[idx]!)
    | none => map.insert h h
  -- Revert free vars in `hs` and `mv`.
  let fvs ← Meta.sortFVarIds <| fvs ++ hs₁.map Expr.fvarId! ++ fvs₂
  let (fvs, mv) ← mv.revert fvs true
  -- Simplify the goal using the embedding theorems.
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx ← Meta.Simp.mkContext { zeta := false, singlePass := true } simpTheorems congrTheorems
  let (some mv, _) ← Meta.simpTarget mv ctx simpProcs (mayCloseGoal := false) | throwError "[embedding] simplification failed"
  -- Extend `fvs` to account for `nonneg` assumptions.
  let mut fvs' : Array (Option (FVarId × Expr)) := #[]
  for fv in fvs do
    let t ← fv.getType
    fvs' := fvs'.push (some (fv, t))
    if hasReturnType t (isEmbeddingAssumptionType includeRat) then
      fvs' := fvs'.push none
  -- Re-introduce all free vars (and their `nonneg` assumptions).
  let (fvs'', mv) ← mv.introNP fvs'.size
  -- Compose the final map from new free vars to old ones.
  -- We do not need to map `nonneg` assumptions. Since `nonneg` assumptions are auxiliary,
  -- We can always provide all of them to the SMT solver without affecting the unsat core.
  let (inverseMap₂, hs') := (fvs'.zip fvs'').foldl (init := ({}, #[])) fun (map, hs') (of, to) =>
    match of with
    | some (of, _) => (map.insert (.fvar of) (.fvar to), hs')
    | none    => (map, hs'.push (.fvar to))
  let inverseMap := compose inverseMap₁ inverseMap₂
  let hs' := hs' ++ hs.map fun h => inverseMap[h]?.getD h
  let modelMap ← mv.withContext <| buildModelMap proofFvs fvs' fvs''
  let map := (inverse inverseMap).fold (init := {}) fun map k v => map.insert k #[v]
  return { map := map, modelMap, hs := hs', mv }
where
  compose (m₁ m₂ : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m₁.fold (init := m₂) fun map k v =>
      map.insert k (map[v]?.getD v)
  inverse (m : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m.fold (init := {}) fun map k v =>
      map.insert v k

end Smt.Preprocess
