import Smt

namespace FinBoundaries

@[irreducible] private def HiddenIndex : Type := Fin 0
private structure WrappedIndex where
  index : Fin 0

-- Hiding an empty index behind a definition or a structure must not introduce a witness.
example : True := by
  fail_if_success have bad : ∃ _ : HiddenIndex, True := by smt +trust
  fail_if_success have bad : ∃ _ : HiddenIndex, True := by smt -embeddings +trust
  fail_if_success have bad : ∃ _ : WrappedIndex, True := by smt +trust
  fail_if_success have bad : ∃ _ : WrappedIndex, True := by smt -embeddings +trust
  trivial

example (n : Nat) [NeZero n] (i : Fin n) : (0 : Fin n).val ≤ i.val := by smt
example (n : Nat) [NeZero n] : (5 : Fin n).val < n := by smt
example (n : Nat) [NeZero n] : ((5 : Fin n).val : Int) < (n : Int) := by smt

-- An unused function into the empty index type is contradictory if its domain is inhabited.
example (α : Type) [Inhabited α] (_f : α → Fin 0) : False := by smt
example (α : Type) [Inhabited α] (_f : α → Fin 0) : False := by smt +trust

private class Witness (α : Type) where value : α
private instance [w : Witness α] : Inhabited α := ⟨w.value⟩
example (α : Type) [Witness α] (_f : α → Fin 0) : False := by smt

-- The subtraction in a symbolic bound is truncated at zero.
example (n : Nat) : ∀ i : Fin (n - 1), i.val + 1 < n := by smt
example : True := by
  fail_if_success have bad (n : Nat) : ∃ _ : Fin (n - 5), True := by smt +trust
  fail_if_success have bad (n : Nat) : (1 : Fin (n + 1)).val = 1 := by smt +trust
  fail_if_success have bad : (1 : Fin 1).val = 1 := by smt +trust
  trivial

-- A custom order or literal instance need not agree with the standard one.
section
local instance (priority := high) : LT (Fin 3) := ⟨fun _ _ => False⟩

example : True := by
  fail_if_success have bad : (0 : Fin 3) < 1 := by smt +trust
  trivial
end

example : True := by
  fail_if_success
    have bad (inst : OfNat (Fin 3) 5) : (@OfNat.ofNat (Fin 3) 5 inst).val = 2 := by smt +trust
  trivial

-- A tactic used while constructing a Fin value still sees an ordinary Nat goal.
private def three : Fin 5 := ⟨3, by smt⟩

example (x : Nat) (h : x = 2) : x + 1 = 3 := by
  let _i : Fin 3 := 1
  smt [h]

-- A local value also witnesses an opaque named domain.
private opaque Carrier : Type := Unit
example (w : Carrier) (f : Carrier → Fin 0) : False := by smt

end FinBoundaries
