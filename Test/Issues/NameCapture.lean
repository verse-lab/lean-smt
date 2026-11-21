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
