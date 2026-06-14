import Smt

example : ∀ p : Bool,
  p = true →
  p = false →
  p ≠ true →
  p ≠ false →
  ¬ p = true →
  ¬ p = false →
  True := by
  smt (config := { showQuery := true, embedBool := false })
  intros ; apply True.intro
