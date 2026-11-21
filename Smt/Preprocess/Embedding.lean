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

/-- Selects which base types the embedding step lifts into SMT-friendly types. -/
structure EmbeddingConfig where
  /-- Whether to embed `Nat` into `Int`. -/
  embedNat : Bool := true
  /-- Whether to embed `Rat` into `Real`. Only takes effect when `Real` is available. -/
  embedRat : Bool := true
  /-- Whether to embed `Bool` into `Prop`. -/
  embedBool : Bool := true

/-- The base types selected by `cfg`, in embedding order. -/
def EmbeddingConfig.baseTypes (cfg : EmbeddingConfig) : MetaM (Array Name) := do
  let mut bts := #[]
  if cfg.embedNat then
    bts := bts.push ``Nat
  if cfg.embedRat && (← getEnv).contains `Real then
    bts := bts.push ``Rat
  if cfg.embedBool then
    bts := bts.push ``Bool
  return bts

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

/-- Maximum position of an embedded Fin input, or arity of a Fin-valued function. -/
abbrev finArityLimit : Nat := 5

private def domainNonempty? (domain : Expr) : MetaM (Option Expr) := do
  if let some fv ← Meta.findLocalDeclWithType? domain then
    return some (← Meta.mkAppM ``Nonempty.intro #[.fvar fv])
  let nonempty ← Meta.mkAppM ``Nonempty #[domain]
  if let some fv ← Meta.findLocalDeclWithType? nonempty then return some (.fvar fv)
  Meta.synthInstance? nonempty

structure FinContext where
  usesFin : Bool := false
  keep : Array FVarId := #[]
  domainEvidence : Array Expr := #[]

/-- A Fin-valued function witnesses a positive bound when each domain has a value.
Keep the dependencies of those proofs through cleanup, then register the proofs from
the current context before embedding reverts the function. -/
def finContext (roots : Array Expr) : MetaM FinContext := do
  let used ← (roots.foldl Lean.collectFVars {}).addDependencies
  let types ← used.fvarIds.mapM FVarId.getType
  let mut finite ← mentionsFin (roots ++ types)
  let mut keep := #[]
  let mut domainEvidence := #[]
  for decl in ← getLCtx do
    if !finite && decl.type.hasAnyFVar used.fvarSet.contains then
      finite ← mentionsFin #[decl.type]
    if ← Meta.isProp decl.type then continue
    let some (domains, result) ← functionSignature decl.type | continue
    unless isFin result && domains.size ≤ finArityLimit do continue
    let bound := result.appArg!
    unless used.fvarSet.contains decl.fvarId || bound.hasAnyFVar used.fvarSet.contains ||
        (!bound.hasFVar && (← Meta.getNatValue? bound) == some 0) do continue
    let some evidence ← (domains.mapM fun d => OptionT.mk (domainNonempty? d)).run | continue
    keep := (keep.push decl.fvarId) ++ (evidence.foldl Lean.collectFVars {}).fvarIds
    -- A Fin domain is encoded by its bounds. Only domains passed through to SMT
    -- need a Nonempty instance while simplifying a Fin-valued function.
    for (domain, proof) in domains.zip evidence do
      unless isFin (← Meta.whnf domain) do domainEvidence := domainEvidence.push proof
  -- Reconstruction can need an otherwise unused witness of an abstract SMT sort.
  -- Only preserve witnesses of type parameters occurring in this Fin query.
  if finite || !keep.isEmpty then
    for decl in ← getLCtx do
      let t := decl.type
      let carrier := if t.isAppOfArity ``Nonempty 1 || t.isAppOfArity ``Inhabited 1 then t.appArg! else t
      if carrier.isFVar && used.fvarSet.contains carrier.fvarId! && (← Meta.inferType carrier).isType then
        keep := keep.push decl.fvarId
  return { usesFin := finite || !keep.isEmpty, keep, domainEvidence }

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

/-- Only selected facts and their dependencies reach SMT. Reverting a symbolic bound
can also revert unused representation instances with Fin in their types. -/
private def checkReachableFin (mv : MVarId) (hs : Array Expr) : MetaM Unit := mv.withContext do
  let roots := (← hs.mapM Meta.inferType) ++ hs.push (← mv.getType)
  let used ← (roots.foldl Lean.collectFVars {}).addDependencies
  let mut terms := roots
  for fv in used.fvarIds do
    let decl ← fv.getDecl
    terms := terms.push decl.type
    if let some value := decl.value? then terms := terms.push value
  for term in terms do
    if let some fin := term.find? isFin then
      throwError "[embedding] unsupported occurrence of {fin} after embedding"

def embeddingWithConfigAndFin (cfg : EmbeddingConfig) (enableFin : Bool) (mv : MVarId) (hs : Array Expr) : MetaM Result := mv.withContext do
  -- Find all free vars to revert in `hs` and `mv`.
  let ts ← hs.mapM Meta.inferType
  let roots := ts.push (← mv.getType)
  let fin ← if enableFin then finContext roots else pure {}
  let hasFin := fin.usesFin
  -- A symbolic Fin bound can occur only in the type of a function argument.
  let used ← ((roots ++ fin.keep.map Expr.fvar).foldl Lean.collectFVars {}).addDependencies
  -- Check if we need to do anything.
  let bts ← cfg.baseTypes
  if bts.isEmpty then return ⟨{}, hs, mv⟩
  let fvts ← used.fvarIds.mapM FVarId.getType
  let types := fvts ++ roots
  unless hasFin || types.any (·.contains ((bts.map (.const · [])).contains ·)) do
    return { map := {}, hs, mv }
  -- Register actual witnesses of abstract argument types before reverting their values.
  -- The instances have type `Nonempty α` and stay available while simplifying under binders.
  let collect : StateRefT (Array Meta.Hypothesis) MetaM Unit := do
    if hasFin then
      for proof in fin.domainEvidence do addWitness proof
      for fv in used.fvarIds do addWitness (.fvar fv)
      for h in hs do addWitness h
      -- Even when f : Fin n → α is the only field with codomain α, an actual f i
      -- witnesses α. Applications containing bound variables cannot supply that evidence.
      if fvts.any Expr.isType then
        for t in roots do
          t.forEach fun e => do
            if e.isApp && e.getAppFn.isFVar && !e.hasLooseBVars then addWitness e
  let (_, witnesses) ← collect.run #[]
  let (_, mv) ← mv.assertHypotheses witnesses
  let (hintIds, originalToLocal, mv) ← assertHints mv hs
  -- Revert free vars in `hs` and `mv`.
  let used := (hintIds.map Expr.fvar).foldl Lean.collectFVars used
  -- Revert all dependencies in local-context order, including instance arguments.
  let fvs ← mv.withContext <| used.fvarIds.filterM fun fv => do
    let ty ← fv.getType
    return !(hasFin && ty.isSort && !ty.isProp)
  let (fvs, mv) ← mv.revert fvs false
  let env ← getEnv
  let mv ← if hasFin then mv.deltaTarget (fun n => !(``Fin).isPrefixOf n && namesFin env n)
    else pure mv
  -- Simplify the goal using the embedding theorems.
  let mv ← simpTargetWithExtensions mv `embedding `fin_embedding hasFin
  -- SMT sorts are inhabited. Sending a residual `Fin` as an uninterpreted sort could
  -- therefore change the meaning of an unsupported higher-order or dependent signature.
  let residual := (← mv.getType).find? isFin
  -- Extend `fvs` to account for `nonneg` assumptions.
  let bts := bts.filter (· != ``Bool) -- Do not consider `Bool` for assumptions.
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
  let (localToNew, hs') := (fvs'.zip fvs'').foldl (init := ({}, #[])) fun (map, hs') (of, to) =>
    match of with
    | some of => (map.insert (.fvar of) (.fvar to), hs')
    | none    => (map, hs'.push (.fvar to))
  -- Use Nonempty evidence through the local instances above. There is no SMT predicate
  -- for Lean's universe-polymorphic Nonempty.
  let hs ← if hasFin then hs.filterM (fun h => do return !(← Meta.inferType h).isAppOfArity ``Nonempty 1)
    else pure hs
  let (restored, map) := restoreHints hs originalToLocal localToNew
  let hs' := hs' ++ restored
  if hasFin || residual.isSome then checkReachableFin mv hs'
  return { map := map, hs := hs', mv }

def embeddingWithConfig (cfg : EmbeddingConfig) := embeddingWithConfigAndFin cfg cfg.embedNat

def embedding (mv : MVarId) (hs : Array Expr) : MetaM Result :=
  embeddingWithConfig {} mv hs

end Smt.Preprocess
