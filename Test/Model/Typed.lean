import Smt
import Smt.Real

open Lean Elab Tactic

private def checkTypedModel (model : Smt.Model) : TacticM Unit := do
  if model.values.isEmpty then
    throwError "expected a non-empty SMT model"
  checkNoProofModelSymbols model
  for (symbol, value) in model.values do
    let symbolType ← Meta.reduceAll (← Meta.inferType symbol)
    let valueType ← Meta.reduceAll (← Meta.inferType value)
    unless ← Meta.isDefEq valueType symbolType do
      throwError "model value has the wrong type\nsymbol: {symbol}\nsymbol type: {symbolType}\nvalue: {value}\nvalue type: {valueType}"
where
  checkNoProofModelSymbols (model : Smt.Model) : TacticM Unit := do
    for (symbol, value) in model.values do
      let symbolType ← Meta.reduceAll (← Meta.inferType symbol)
      let valueType ← Meta.reduceAll (← Meta.inferType value)
      if ← Meta.isProp symbolType then
        throwError "proof-valued symbol leaked into SMT model\nsymbol: {symbol}\nsymbol type: {symbolType}\nvalue: {value}\nvalue type: {valueType}"

syntax (name := guardTypedSatModel) "guard_typed_sat_model" : tactic

@[tactic guardTypedSatModel] def evalGuardTypedSatModel : Tactic := fun _ => withMainContext do
  let mv ← getMainGoal
  let hs := (← Smt.Preprocess.getPropHyps).map Expr.fvar
  let result ← Smt.smt { model := true, extraSolverOptions := [("finite-model-find", "true")] } mv hs
  match result with
  | .sat (.some model) =>
    checkTypedModel model
    mv.admit
    replaceMainGoal []
  | .sat none =>
    throwError "expected SMT solver to produce a model"
  | .unsat .. =>
    throwError "expected a satisfiable counterexample query"
  | .unknown reason =>
    throwError "expected a satisfiable counterexample query, got unknown: {reason}"

syntax (name := guardRawSatModel) "guard_raw_sat_model" : tactic

@[tactic guardRawSatModel] def evalGuardRawSatModel : Tactic := fun _ => withMainContext do
  let mv ← getMainGoal
  let hs := (← Smt.Preprocess.getPropHyps).map Expr.fvar
  let result ← Smt.smt { model := true, extraSolverOptions := [("finite-model-find", "true")] } mv hs
  match result with
  | .sat (.some model) =>
    if model.values.isEmpty then
      throwError "expected a non-empty SMT model"
    checkTypedModel.checkNoProofModelSymbols model
    mv.admit
    replaceMainGoal []
  | .sat none =>
    throwError "expected SMT solver to produce a model"
  | .unsat .. =>
    throwError "expected a satisfiable counterexample query"
  | .unknown reason =>
    throwError "expected a satisfiable counterexample query, got unknown: {reason}"

opaque U : Type

syntax (name := guardModelOriginPredicates) "guard_model_origin_predicates" : tactic

@[tactic guardModelOriginPredicates] def evalGuardModelOriginPredicates : Tactic := fun _ => withMainContext do
  let propType := mkSort levelZero
  let finType := mkApp (mkConst ``Fin) (mkNatLit 10)
  if ← Smt.ModelAdapter.mayHaveModelOrigin propType finType then
    throwError "Prop-valued model entries must not be mapped to Fin origins"
  let unknownType := mkConst ``U
  let finOneType := mkApp (mkConst ``Fin) (mkNatLit 1)
  unless ← Smt.ModelAdapter.mayHaveModelOrigin finOneType unknownType do
    throwError "Fin-valued model entries should be allowed for unknown downstream sorts"
  let mv ← getMainGoal
  mv.admit
  replaceMainGoal []

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : True := by
  guard_model_origin_predicates

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (p : Bool) : p = !p := by
  guard_typed_sat_model

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x : Nat) : x ≠ 0 := by
  guard_typed_sat_model

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x : Fin 5) : x = 0 := by
  guard_typed_sat_model

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (f : Fin 5 → Bool) : f 0 = f 1 := by
  guard_typed_sat_model

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (f : Bool → Fin 5) : f true = f false := by
  guard_typed_sat_model

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (f : Nat → Fin 5) : f 0 = f 1 := by
  guard_typed_sat_model

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x : Rat) : x = 0 := by
  guard_typed_sat_model

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : U) : x = y := by
  guard_raw_sat_model

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (latestPlan otherPlan : Fin 4) (guard : Bool) (enabled : Fin 4 → Bool) :
    enabled latestPlan = guard ∧ latestPlan = otherPlan := by
  guard_typed_sat_model

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (EnactorPC : Type)
    (Receive Apply Cleanup RemoveActiveDNS : EnactorPC)
    (_EnactorPC_Enum_distinct : distinctN [Receive, Apply, Cleanup, RemoveActiveDNS])
    (x : Fin 5) : x = 0 := by
  guard_raw_sat_model

theorem AWSDnsRace_EnactorApply_DnsConsistent_extracted_1_5 (Enactor EnactorPC PlanId : Type) [LT PlanId] (NoPlan : PlanId) (self : Enactor)
  (st_dns_valid : Bool) (hinv : st_dns_valid = true) (st_plan_deleted : PlanId → Bool)
  (st_enactor_processing : Enactor → PlanId) (st_enactor_pc : Enactor → EnactorPC)
  (st_enactor_snapshot_current : Enactor → PlanId)
  (EnactorPC_Enum_Receive EnactorPC_Enum_Apply EnactorPC_Enum_Cleanup EnactorPC_Enum_RemoveActiveDNS : EnactorPC)
  (EnactorPC_Enum_distinct :
    distinctN [EnactorPC_Enum_Receive, EnactorPC_Enum_Apply, EnactorPC_Enum_Cleanup, EnactorPC_Enum_RemoveActiveDNS])
  (EnactorPC_Enum_complete :
    ∀ (__veil_x : EnactorPC),
      __veil_x = EnactorPC_Enum_Receive ∨
        __veil_x = EnactorPC_Enum_Apply ∨
          __veil_x = EnactorPC_Enum_Cleanup ∨ __veil_x = EnactorPC_Enum_RemoveActiveDNS) :
  st_enactor_pc self = EnactorPC_Enum_Apply →
    (st_enactor_snapshot_current self < st_enactor_processing self ∨ st_enactor_snapshot_current self = NoPlan →
        st_plan_deleted (st_enactor_processing self) = true) →
      st_dns_valid = true := by smt +mono [*]
