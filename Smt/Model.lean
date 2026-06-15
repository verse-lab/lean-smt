/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Pîrlea
-/

import Lean
import Smt.Preprocess.Embedding.Fin

namespace Smt.ModelAdapter

open Lean

def normalizeModelExpr (e : Expr) : MetaM Expr :=
  Meta.reduceAll e

private def Expr.isNatType (e : Expr) : Bool :=
  e.consumeMData.isConstOf ``Nat

private def Expr.isIntType (e : Expr) : Bool :=
  e.consumeMData.isConstOf ``Int

private def Expr.isBoolType (e : Expr) : Bool :=
  e.consumeMData.isConstOf ``Bool

private def Expr.isPropType (e : Expr) : Bool :=
  e.consumeMData.isProp

private def Expr.isRatType (e : Expr) : Bool :=
  e.consumeMData.isConstOf ``Rat

private def Expr.isRealType (e : Expr) : Bool :=
  e.consumeMData.isConstOf `Real

private def Expr.finSize? (e : Expr) : Option Expr :=
  match e.consumeMData with
  | .app (.const ``Fin _) n => some n
  | _ => none

private def mkBoolAsProp (value : Expr) : MetaM Expr :=
  Meta.mkEq value (mkConst ``Bool.true)

private def mkPropAsBool (value : Expr) : MetaM Expr :=
  Meta.mkAppOptM ``decide #[some value, none]

private def mkNatAsInt (value : Expr) : MetaM Expr :=
  Meta.mkAppM ``Int.ofNat #[value]

private def mkIntAsNat (value : Expr) : MetaM Expr :=
  Meta.mkAppM ``Int.toNat #[value]

private def mkFinAsInt (value : Expr) : MetaM Expr := do
  let value ← Meta.mkAppM ``Fin.val #[value]
  mkNatAsInt value

private def mkIntAsFin (value n : Expr) : MetaM Expr :=
  Meta.mkAppM `Smt.Preprocess.Embedding.ofIntFinTotal #[n, value]

private def mkRatAsReal (value : Expr) : MetaM Expr :=
  Meta.mkAppOptM `Rat.cast #[some (mkConst `Real), none, some value]

private def mkRealAsRat (value : Expr) : MetaM Expr :=
  Meta.mkAppM `Real.toRat #[value]

def replaceModelFVars (modelMap : Std.HashMap Expr Expr) (e : Expr) : Expr :=
  let (froms, tos) := modelMap.fold (init := (#[], #[])) fun (froms, tos) src dst =>
    (froms.push src, tos.push dst)
  e.replaceFVars froms tos

def modelExprInContext (e : Expr) : MetaM Bool :=
  match e with
  | .fvar fvarId => return (← getLCtx).contains fvarId
  | _ => return true

partial def adaptModelValue (value fromType toType : Expr) : MetaM Expr := do
  let fromType ← normalizeModelExpr fromType
  let toType ← normalizeModelExpr toType
  if ← Meta.isDefEq fromType toType then
    return value
  if (← Meta.whnf toType).isForall then
    Meta.forallTelescopeReducing toType fun toArgs toRetType => do
      Meta.forallTelescopeReducing fromType fun fromArgs _ => do
        if toArgs.size > fromArgs.size then
          throwError "could not adapt SMT model expression: expected function arity {toArgs.size}, but SMT value has arity {fromArgs.size}"
        let mut app := value
        for i in [:toArgs.size] do
          let toArg := toArgs[i]!
          let toArgType ← normalizeModelExpr (← Meta.inferType toArg)
          let fromArgType ← normalizeModelExpr (← Meta.inferType fromArgs[i]!)
          let arg ← adaptModelValue toArg toArgType fromArgType
          app := mkApp app arg
        let body ← adaptModelValue app (← Meta.inferType app) toRetType
        Meta.mkLambdaFVars toArgs body
  else if Expr.isPropType fromType && Expr.isBoolType toType then
    mkPropAsBool value
  else if Expr.isBoolType fromType && Expr.isPropType toType then
    mkBoolAsProp value
  else if Expr.isIntType fromType && Expr.isNatType toType then
    mkIntAsNat value
  else if Expr.isNatType fromType && Expr.isIntType toType then
    mkNatAsInt value
  else if let some n := Expr.finSize? toType then
    if Expr.isIntType fromType then
      mkIntAsFin value n
    else
      throwError "could not adapt SMT model expression of type\n  {fromType}\nto expected type\n  {toType}"
  else if let some _ := Expr.finSize? fromType then
    if Expr.isIntType toType then
      mkFinAsInt value
    else
      throwError "could not adapt SMT model expression of type\n  {fromType}\nto expected type\n  {toType}"
  else if Expr.isRealType fromType && Expr.isRatType toType then
    mkRealAsRat value
  else if Expr.isRatType fromType && Expr.isRealType toType then
    mkRatAsReal value
  else
    throwError "could not adapt SMT model expression of type\n  {fromType}\nto expected type\n  {toType}"

def ensureModelValueType (symbol value : Expr) : MetaM Unit := do
  let symbolType ← normalizeModelExpr (← Meta.inferType symbol)
  let valueType ← normalizeModelExpr (← Meta.inferType value)
  unless ← Meta.isDefEq valueType symbolType do
    throwError "SMT model reconstruction produced a value with the wrong type\nsymbol:\n  {symbol}\nsymbol type:\n  {symbolType}\nvalue:\n  {value}\nvalue type:\n  {valueType}"

end Smt.ModelAdapter
