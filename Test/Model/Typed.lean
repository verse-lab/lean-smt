import Smt
import Smt.Real

open Lean Elab Tactic

private def checkTypedModel (model : Smt.Model) : TacticM Unit := do
  if model.values.isEmpty then
    throwError "expected a non-empty SMT model"
  for (symbol, value) in model.values do
    let symbolType ← Meta.reduceAll (← Meta.inferType symbol)
    let valueType ← Meta.reduceAll (← Meta.inferType value)
    unless ← Meta.isDefEq valueType symbolType do
      throwError "model value has the wrong type\nsymbol: {symbol}\nsymbol type: {symbolType}\nvalue: {value}\nvalue type: {valueType}"

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
    mv.admit
    replaceMainGoal []
  | .sat none =>
    throwError "expected SMT solver to produce a model"
  | .unsat .. =>
    throwError "expected a satisfiable counterexample query"
  | .unknown reason =>
    throwError "expected a satisfiable counterexample query, got unknown: {reason}"

opaque U : Type

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
