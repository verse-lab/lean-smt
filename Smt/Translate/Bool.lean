/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Smt.Recognizers
import Smt.Translate

namespace Smt.Translate.Bool

open Translator Term

private def mkBool : Lean.Expr :=
  .const ``Bool []

@[scoped smt_translate] def translateType : Translator := fun e => match e with
  | .const ``Bool _ => return symbolT "Bool"
  | _               => return none

@[scoped smt_translate] def translateBool : Translator := fun e => do
  if let .const ``true _ := e then
    return symbolT "true"
  else if let .const ``false _ := e then
    return symbolT "false"
  else if let .some b := e.app1? ``not then
    return appT (symbolT "not") (← applyTranslators! b)
  else if let some (a, b) := e.app2? ``and then
    return mkApp2 (symbolT "and") (← applyTranslators! a) (← applyTranslators! b)
  else if let some (a, b) := e.app2? ``or then
    return mkApp2 (symbolT "or") (← applyTranslators! a) (← applyTranslators! b)
  else if let some (a, b) := e.app2? ``xor then
    return mkApp2 (symbolT "xor") (← applyTranslators! a) (← applyTranslators! b)
  else if let some (_, x, y) := e.beq? then
    return mkApp2 (symbolT "=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (_, x, y) := e.bne? then
    return mkApp2 (symbolT "distinct") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

@[scoped smt_translate] def translateProp : Translator := fun e => do
  let .app (.app (.app f (.const ``Bool _)) a) b := e | return none
  if f.isConstOf ``Eq then
    match a.constName? with
    | ``true => applyTranslators! b
    | ``false => return appT (symbolT "not") (← applyTranslators! b)
    | _ =>
      match b.constName? with
      | ``true => applyTranslators! a
      | ``false => return appT (symbolT "not") (← applyTranslators! a)
      | _ => return mkApp2 (symbolT "=") (← applyTranslators! a) (← applyTranslators! b)
  else if f.isConstOf ``Ne then
    match a.constName? with
    | ``true => return appT (symbolT "not") (← applyTranslators! b)
    | ``false => applyTranslators! b
    | _ =>
      match b.constName? with
      | ``true => return appT (symbolT "not") (← applyTranslators! a)
      | ``false => applyTranslators! a
      | _ => return mkApp2 (symbolT "distinct") (← applyTranslators! a) (← applyTranslators! b)
  else
    return none

end Smt.Translate.Bool
