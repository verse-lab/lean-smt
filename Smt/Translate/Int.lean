/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

module

public import Smt.Recognizers
public meta import Smt.Recognizers
public import Smt.Translate
public meta import Smt.Translate

public meta section

namespace Smt.Translate.Int

open Lean Translator Term

private def mkInt : Lean.Expr :=
  .const ``Int []

/-- Use the canonical Int type in recognizer arguments, which may contain aliases. -/
private def unfoldIntTypeArgs (e : Expr) (arity typeArgs : Nat) : MetaM Expr := do
  unless e.getAppNumArgs == arity do return e
  let args := e.getAppArgs
  let mut unfolded := args
  for i in [:typeArgs] do
    let arg := args[i]!
    if arg != mkInt && (← Meta.whnf arg) == mkInt then
      unfolded := unfolded.set! i mkInt
  return mkAppN e.getAppFn unfolded

@[smt_translate] def translateType : Translator := fun e => match e with
  | .const ``Int _ => return symbolT "Int"
  | _              => return none

@[smt_translate] def translateInt : Translator := fun e => do
  let e ← match e.getAppFn.constName? with
    | some ``OfNat.ofNat | some ``Neg.neg => unfoldIntTypeArgs e 3 1
    | some ``HAdd.hAdd | some ``HSub.hSub | some ``HMul.hMul
    | some ``HDiv.hDiv | some ``HMod.hMod => unfoldIntTypeArgs e 6 2
    | _ => pure e
  if let some n := e.natLitOf? mkInt then
    return literalT (toString n)
  else if let some x := e.negOf? mkInt then
    return appT (symbolT "-") (← applyTranslators! x)
  else if let some (x, y) := e.hAddOf? mkInt mkInt then
    return mkApp2 (symbolT "+") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hSubOf? mkInt mkInt then
    return mkApp2 (symbolT "-") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hMulOf? mkInt mkInt then
    return mkApp2 (symbolT "*") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hDivOf? mkInt mkInt then
    return mkApp2 (symbolT "div") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hModOf? mkInt mkInt then
    return mkApp2 (symbolT "mod") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

@[smt_translate] def translateProp : Translator := fun e => do
  let e ← match e.getAppFn.constName? with
    | some ``LT.lt | some ``LE.le | some ``GE.ge | some ``GT.gt => unfoldIntTypeArgs e 4 1
    | _ => pure e
  if let some (x, y) := e.ltOf? mkInt then
    return mkApp2 (symbolT "<") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.leOf? mkInt then
    return mkApp2 (symbolT "<=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.geOf? mkInt then
    return mkApp2 (symbolT ">=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.gtOf? mkInt then
    return mkApp2 (symbolT ">") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

end Smt.Translate.Int
