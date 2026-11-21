import Smt

/-! Bound and free variables must not capture global constants with the same name. -/

def p : Prop := False
def q : Prop := True

-- A bound variable must not capture a constant: this is false, since `_root_.q` is `True`.
theorem bound_capture : ∃ q : Prop, ¬ _root_.q := by
  fail_if_success smt +trust
  sorry

-- The same, for a binder in a hint: `g True` is false, since `_root_.p` is `False`.
def g (p : Prop) : Prop := p ∧ _root_.p
theorem hint_capture : g True := by
  fail_if_success smt +trust [g]
  sorry

-- A free variable and a constant with the same name must stay distinct.
theorem fvar_clash (p : Prop) (h : p) : _root_.p := by
  fail_if_success smt +trust [h]
  sorry

example : ∃ q : Prop, ¬ _root_.q ∨ q := by
  smt +showQuery
  sorry

example (p : Prop) (h : p) : p ∨ _root_.p := by
  smt +showQuery [h]
  sorry

-- Valid goals still go through, with proof reconstruction.
example (p : Prop) (h : p) : p ∨ _root_.p := by
  smt [h]

example (p : Prop) (h : _root_.p) : p → _root_.p := by
  smt [h]

example : ∀ q : Prop, q ∨ ¬ q := by
  smt

-- Variables named after SMT-LIB builtins or reserved words are renamed.
example (exp «mod» «let» : Int) (h : exp < «mod») (h' : «mod» < «let») : exp < «let» := by
  smt +showQuery [h, h']
  sorry

example (exp «mod» «let» : Int) (h : exp < «mod») (h' : «mod» < «let») : exp < «let» := by
  smt [h, h']

opaque x : Int
opaque rel : Int → Int → Prop

-- Keep both quantifiers in the query.
example (h : ∀ x, rel x _root_.x) : ∀ x : Int, rel x _root_.x ∧ ∃ x : Int, rel x _root_.x := by
  smt -intros [h]

example (h : ∀ x, rel x _root_.x) (y : Int) : rel y _root_.x := by
  smt [h]

example (h : rel 0 _root_.x) : ∃ x, rel x _root_.x := by
  smt [h]

-- Keep the let-expression through preprocessing.
example (h : rel 0 _root_.x) : (let x : Int := 0; rel x _root_.x) := by
  smt -intros -normalize -embeddings [h]

example (h : rel 0 _root_.x) : (have x : Int := 0; rel x _root_.x) := by
  smt -intros -normalize -embeddings [h]

-- A local definition hint goes through define-fun, using the parameter name from its type.
example (y : Int) : y + _root_.x = _root_.x + y := by
  let f : (x : Int) → Int := fun x => x + _root_.x
  change f y = _root_.x + y
  smt -normalize -embeddings [f]

namespace Foo
opaque x : Int
opaque opened : Int
end Foo

-- Surface binders must be atomic. Metaprograms can give a local a hierarchical name.
open Lean Elab Tactic in
elab "renameForSmt " x:ident " to " n:ident : tactic => withMainContext do
  let d ← Meta.getLocalDeclFromUserName x.getId
  replaceMainGoal [← (← getMainGoal).rename d.fvarId n.getId]

example (y : Int) (h : y < Foo.x) : y ≠ Foo.x := by
  renameForSmt y to Foo.x
  smt [h]

example («Foo.x» : Int) (h : «Foo.x» < Foo.x) : «Foo.x» ≠ Foo.x := by
  smt [h]

open Foo in
example (x : Int) (h : x < opened) : x ≠ Foo.opened := by
  smt [h]

-- Both the inaccessible first x and the visible second x are needed.
example (f : Int → Int) (x : Int) (h : f x = 0) (x : Int) (h' : f x = 1) :
    ∃ y, f y ≠ f x := by
  smt [h, h']

macro "introAndSolve" : tactic => `(tactic| (intro x; smt))
example : ∀ y : Int, y ≤ y := by introAndSolve

-- A fresh suffix is already the source name of another local.
example (x x_1 : Int) (h : x < x_1) (h' : x_1 < _root_.x) : x < _root_.x := by
  smt [h, h']

-- The same free subterm occurs in a hypothesis and under a binder with its emitted name.
example (x : Int) (h : rel x _root_.x) : ∃ x_1 : Int, x_1 = 0 ∧ rel x _root_.x := by
  smt [h]

-- Reconstruction must retain the level parameter of both the sort and its inhabitant.
universe u
axiom Poly.{v} : Type v
axiom point.{v} : Poly.{v}
example (point : Poly.{u}) (f : Poly.{u} → Int) (h : point = _root_.point.{u}) :
    f point = f _root_.point.{u} := by
  smt [h]

inductive Token where
  | endOfInput
  | payload (val : Int)

example (Token : _root_.Token) (h : Token = _root_.Token.payload 0) : Token ≠ _root_.Token.endOfInput := by
  smt [h]

example (t : Token) (h : t = Token.payload 0) : t ≠ Token.endOfInput := by
  renameForSmt t to Token.endOfInput
  smt [h]

example (k : Int) : Token.payload k ≠ Token.endOfInput := by
  renameForSmt k to Token.payload.val
  smt

-- Exercise the Nat-specific quantifier translator before the usual embeddings.
example : ∀ x : Nat, x + 1 > x ∧ _root_.x ≤ _root_.x := by
  smt -intros -normalize -embeddings +showQuery
  smt

-- Check each theory name independently, including a hierarchical name for the string operator.
example (bvadd : Int) : bvadd ≤ bvadd := by smt
example (len : Int) : len ≤ len := by
  renameForSmt len to str.len
  smt
example (select : Int) : select ≤ select := by smt
example (abs : Int) : abs ≤ abs := by smt
example (exp : Int) : exp ≤ exp := by smt

example (RegLan : Type) (a b : RegLan) (f : RegLan → Int) (h : a = b) : f a = f b := by
  smt [h]

-- Omit the final hypothesis to request a counterexample to the partial query.
/--
error: unable to prove goal, either it is false or you need to provide more facts. Here is a potential counter-example:

  exp = 0
-/
#guard_msgs in
example (exp : Int) (_h : exp ≠ 0) : exp ≠ 0 := by
  smt +model

-- Lossy SMT pipe quoting must not identify distinct Lean names.
example («a|b» «a\b» : Int) (h : «a|b» < «a\b») : «a|b» ≠ «a\b» := by
  smt [h]

opaque «a|b» : Int
example («a\b» : Int) (h : «a\b» < «a|b») : «a\b» ≠ «a|b» := by
  smt [h]

-- The pretty-printer can emit the same string for two distinct programmatic names.
opaque «a.b» : Int
open Lean Elab Tactic in
example (y : Int) (h : y < «a.b») : y ≠ «a.b» := by
  run_tac
    let d ← Meta.getLocalDeclFromUserName `y
    let n := Name.mkSimple "«a.b»"
    guard (n != `«a.b» && n.toString == (`«a.b»).toString)
    replaceMainGoal [← (← getMainGoal).rename d.fvarId n]
  smt [h]
