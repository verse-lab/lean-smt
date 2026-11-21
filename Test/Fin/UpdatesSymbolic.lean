import Smt

namespace FinUpdatesSymbolic

-- Reverting the symbolic bound can also revert unused representation instances.
private class Representation (α : Type) where
  encode : α → Nat
private class LawfulRepresentation (α : Type) (r : Representation α) : Prop where
  injective : Function.Injective r.encode

private theorem representationHint {α : Type} (_r : Representation α) : True := trivial

theorem representedBound (n : Nat) [r : Representation (Fin (n + 1))]
    [LawfulRepresentation _ r] (i : Fin (n + 1)) : i.val ≤ n := by smt [representationHint r]

-- A whole-field assignment is used pointwise when proving an invariant.
theorem boundedUpdate (n k : Nat) (hk : k < n) (old next : Fin n → Nat)
    (bounded : ∀ i, old i ≤ 3)
    (update : next = fun i => if (⟨k, hk⟩ : Fin n) = i then 3 else old i) (j : Fin n) :
    next j ≤ 3 := by smt [hk, bounded, update]

-- An actual application witnesses the abstract codomain, even without a local α.
theorem abstractRead (α : Type) (n : Nat) (f : Fin n → α) (i : Fin n) :
    f i = f i := by smt

example : True := by
  fail_if_success
    have bad (α : Type) (f : Fin 0 → α) : ∃ a : α, ∀ i, f i = a := by smt +trust
  fail_if_success
    have bad (r : Representation (Fin 0)) : ∃ i, r.encode i = r.encode i := by smt +trust
  trivial

end FinUpdatesSymbolic
