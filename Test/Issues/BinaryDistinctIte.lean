import Smt

attribute [local instance] Classical.propDecidable

example (p q r : Prop) (h : q) :
    (if p ≠ True then r → q else q) := by
  smt [h]
