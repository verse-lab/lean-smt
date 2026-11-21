import Smt

-- Widening an index preserves its position. Moving to its successor advances it.
example (n : Nat) (i : Fin n) : i.castSucc < i.succ := by smt
example (n : Nat) (i : Fin n) : i.succ.val = i.val + 1 := by smt
example (m n : Nat) (h : m ≤ n) (i : Fin m) : (i.castLE h).val = i.val := by smt
example (m n : Nat) (h : m = n) (i : Fin m) : (i.cast h).val = i.val := by smt
example (m n : Nat) (i : Fin m) (h : i.val < n) : (i.castLT h).val = i.val := by smt
example (n : Nat) : (Fin.last n).val = n := by smt

-- Bounded addition and subtraction wrap at either end of the interval.
example (i : Fin 4) (h : i = 3) : i + 1 = 0 := by smt [h]
example (i : Fin 5) : i + 1 ≠ i := by smt
example (i j : Fin 4) (hi : i = 0) (hj : j = 1) : i - j = 3 := by smt [hi, hj]
example (n : Nat) (i j : Fin n) (h : i.val + j.val < n) :
    (i + j).val = i.val + j.val := by smt [h]
example (n : Nat) (i j : Fin n) (h : j ≤ i) : (i - j).val = i.val - j.val := by smt [h]
example (i j : Fin 5) : (i * j).val = (i.val * j.val) % 5 := by smt
example (i j : Fin 5) : (i % j).val = i.val % j.val := by smt

-- A wrapped counter can decrease.
example : ∃ i : Fin 4, i + 1 < i := by smt
example : True := by
  fail_if_success have bad (i : Fin 4) : i < i + 1 := by smt +trust
  trivial

-- Nonstandard operations must retain their Lean semantics when projected.
example : True := by
  fail_if_success
    have bad (op : HAdd (Fin 4) (Fin 4) (Fin 4)) (i : Fin 4) :
        (@HAdd.hAdd _ _ _ op i i).val = (i.val + i.val) % 4 := by smt +trust
  fail_if_success
    have bad (op : HSub (Fin 3) (Fin 3) (Fin 3)) (i : Fin 3) :
        (@HSub.hSub _ _ _ op i i).val = 0 := by smt +trust
  trivial
