import Smt

open Lean Elab Meta

elab "#check_smt_model_context" : command => Command.liftTermElabM do
  let model ← withLocalDeclD `x (mkConst ``Int) fun x => do
    let goal ← mkFreshExprMVar (← mkEq x (mkIntLit 0))
    match ← Smt.smt { model := true } goal.mvarId! #[] with
    | .sat (some model) => return model
    | _ => throwError "expected a satisfiable result with a model"
  unless model.sorts.isEmpty do
    throwError "expected no uninterpreted sort interpretations"
  unless model.values.size == 1 do
    throwError "expected exactly one value interpretation"
  unless model.entries.size == model.sorts.size + model.values.size do
    throwError "model entries are inconsistent with the structured model"
  if model.isEmpty then
    throwError "expected a nonempty model"
  let some (value, _) := model.values[0]? |
    throwError "expected a value interpretation"
  if (← getLCtx).containsFVar value then
    throwError "the model expression unexpectedly remains in the current local context"
  let valueHasIntType ← liftM (m := IO) <| model.ctx.runMetaM do
    Meta.isDefEq (← Meta.inferType value) (mkConst ``Int)
  unless valueHasIntType do
    throwError "failed to process the model after leaving its original local context"
  let model ← withLocalDeclD `U (.sort (.succ .zero)) fun U =>
    withLocalDecl `inst .instImplicit (mkApp (mkConst ``Nonempty [.zero]) U) fun inst => do
      let instDecl ← getFVarLocalDecl inst
      Meta.withLocalInstances [instDecl] do
        withLocalDeclD `x U fun x =>
          withLocalDeclD `y U fun y => do
            let goal ← mkFreshExprMVar (← mkEq x y)
            match ← Smt.smt { model := true } goal.mvarId! #[] with
            | .sat (some model) => return model
            | _ => throwError "expected an uninterpreted-sort model"
  unless model.sorts.size == 1 do
    throwError "expected exactly one uninterpreted sort interpretation"
  unless model.values.size == 2 do
    throwError "expected exactly two value interpretations"

#check_smt_model_context
