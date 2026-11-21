import Smt

example (n : Nat) : (∃ _ : Fin n, True) ↔ 0 < n := by smt
example (n : Nat) (h : n = 0) : ¬ ∃ i : Fin n, i.val = 0 := by smt [h]
example (i j : Fin 1) : i = j := by smt
example (n : Nat) (i : Fin (n + 1)) : i.val ≤ n := by smt
example (m n : Nat) (i : Fin m) (j : Fin n) (h : m ≤ n) :
    i.val < n ∧ j.val < n := by smt [h]
example : ∀ n, ∀ i : Fin n, ∀ j : Fin i.val, j.val < n := by smt
example (size : Bool → Nat) (i : Fin (size true)) : i.val < size true := by smt
example (n : Nat) (i : Fin n) : ∃ j : Fin n, ∀ k : Fin n, k = j → k = i := by smt
example : ∃ i j : Fin 2, i ≠ j := by smt
