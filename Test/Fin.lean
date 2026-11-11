import Smt

theorem nat_embedding (f : Nat → Nat → Bool) : f 0 0 = false := by smt

theorem fin_embedding (f : Fin 4 → Fin 4 → Bool) : f 0 0 = false := by smt

theorem fin_bound_free (x : Fin 4) : (x : Nat) < 4 := by smt

theorem fin_bound_output (g : Nat → Fin 4) (a : Nat) : ((g a : Fin 4) : Nat) < 4 := by smt

theorem fin_input_literal (f : Fin 4 → Fin 4 → Bool) : f 0 0 = f 0 0 := by smt

-- A symbolic bound `n`: there is no `NeZero n` instance, so functions over `Fin n` are rewritten to
-- functions over `Int` using `Inhabited` of the result type instead.
theorem fin_symbolic_forall (n : Nat) : ∀ i j : Fin n, i = j → (i : Nat) = j := by smt

theorem fin_symbolic_input (n : Nat) (p : Fin n → Bool) :
    ∀ i : Fin n, p i = true → (i : Nat) < n := by smt

theorem fin_symbolic_nat_field (n : Nat) (c : Fin n → Nat) (h : ∀ i, c i ≤ 3) :
    ∀ i : Fin n, c i ≤ 3 := by smt [h]

theorem fin_symbolic_two_args (n : Nat) (r : Nat → Fin n → Bool) (h : ∀ k i, r k i = true → (i : Nat) < k) :
    ∀ k : Nat, ∀ i : Fin n, r k i = true → (i : Nat) < k + 1 := by smt [h]

-- Both sides of the update are in range: the new bound holds for the written index and for the rest.
theorem fin_symbolic_update (n : Nat) (present : Fin n → Bool) (nextId : Nat) (id : Fin n)
    (hid : (id : Nat) = nextId) (inv : ∀ i : Fin n, present i = true → (i : Nat) < nextId) :
    ∀ i : Fin n, (i = id ∨ present i = true) → (i : Nat) < nextId + 1 := by smt [hid, inv]

-- Intentional failure: the claim is false for `i = id`.
theorem fin_symbolic_false (n : Nat) (present : Fin n → Bool) (id : Fin n) :
    ∀ i : Fin n, present i = true → i = id := by smt
