import Smt

example (x y : Nat) : 1 ≤ max x y + 1 := by
  smt

example (x y : Nat) (h : y ≤ x) : max x y = x := by
  smt [h]
