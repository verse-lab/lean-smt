import Smt

-- Keep this global name: the Fin encoding also introduces a quantified variable named x.
def x : Int := 0

example : ∃ i : Fin 2, (i.val : Int) ≠ x := ⟨1, by decide⟩

example : ¬ (∀ (rel : LT Int) (i : Fin 1), @LT.lt Int rel (i.val : Int) 1) :=
  fun h => h ⟨fun _ _ => False⟩ 0

example : True := by
  fail_if_success have : ¬ ∃ i : Fin 2, (i.val : Int) ≠ x := by smt -trust
  fail_if_success have (rel : LT Int) (i : Fin 1) : @LT.lt Int rel (i.val : Int) 1 := by smt -trust
  trivial

-- Expected failures until SMT binder hygiene and integer order recognition are fixed.
-- Remove the corresponding diagnostic from the golden file when each rejection succeeds.
example : True := by
  fail_if_success have : ¬ ∃ i : Fin 2, (i.val : Int) ≠ x := by smt +trust
  trivial

example : True := by
  fail_if_success have (rel : LT Int) (i : Fin 1) : @LT.lt Int rel (i.val : Int) 1 := by smt +trust
  trivial
