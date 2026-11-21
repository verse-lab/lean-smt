import Smt

attribute [local instance] Classical.propDecidable

example (a b : Prop) (f : Prop → Prop)
    (h : ∀ x : Prop, (if x then a else b) = f x) :
    (if True then a else b) = f True := by
  smt [h]

example (a b : Prop) (f : Prop → Prop)
    (h : ∀ x : Prop, (if x then a else b) = f x) :
    (if False then a else b) = f False := by
  smt [h]
