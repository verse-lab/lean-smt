import Smt

-- A proposition `∀ _ : α, p` over a non-`Prop` domain is a quantified formula, not a function
-- type, although its body does not mention the bound variable. It was translated as an arrow
-- sort, `(α -> p)`, which cvc5 rejects ("Symbol '->' not declared as a variable").
theorem forall_non_dependent {α : Type} [Nonempty α] (p : Prop) (h : ∀ _ : α, p) : p := by
  smt [h]

theorem forall_non_dependent_conj {α : Type} [Nonempty α] (q : Prop) (h : q ∧ ∀ _ : α, ¬ False) : q := by
  smt [h]

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem forall_non_dependent_trusted {α : Type} [Inhabited α] (p : Prop)
    (_h : ∀ _ : α, p) : p := by
  smt +trust [_h]

-- On an empty type the hypothesis is true. Treating the sort as inhabited would let
-- the solver refute the hypothesis and trusted mode admit False.
/--
error: cannot translate a potentially empty sort α to SMT-LIB
Lean could not prove Nonempty α in the goal context. SMT-LIB sorts are nonempty.
If you have a witness `x`, add `haveI : Nonempty _ := ⟨x⟩` before `smt`.
If the instance is derivable before preprocessing, declare it with `haveI` before `smt`.
-/
#guard_msgs in
example (α : Type) (h : ∀ _ : α, False) : False := by
  smt +trust [h]

namespace NonemptyScope

def EmptyDomain := Empty

class HasEmptyDomain where
  witness : EmptyDomain

instance [inst : HasEmptyDomain] : Nonempty EmptyDomain := ⟨inst.witness⟩

-- Inside the existential, the binder can supply Nonempty EmptyDomain. It must not enable
-- caching the same vacuous quantifier for use outside the existential. Taking q := True
-- makes the hypothesis true, so an admitted conclusion would give a closed proof of False.
/--
error: cannot translate a potentially empty sort EmptyDomain to SMT-LIB
Lean could not prove Nonempty EmptyDomain in the goal context. SMT-LIB sorts are nonempty.
If you have a witness `x`, add `haveI : Nonempty _ := ⟨x⟩` before `smt`.
If the instance is derivable before preprocessing, declare it with `haveI` before `smt`.
-/
#guard_msgs in
example (q : Prop) (_h : ((∃ _ : HasEmptyDomain, ∀ _ : EmptyDomain, False) ∨ q) ∧
    (∀ _ : EmptyDomain, False)) : False := by
  smt +trust [_h]

end NonemptyScope
