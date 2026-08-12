import Smt

example : ∀ p : Bool,
  p = true →
  p = false →
  p ≠ true →
  p ≠ false →
  ¬ p = true →
  ¬ p = false →
  True := by
  smt +showQuery -embedBool
  intros ; apply True.intro
