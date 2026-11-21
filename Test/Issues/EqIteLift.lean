import Smt

example (p q : Prop) [Decidable p] (hq : q) :
    (if p then True else q) = True := by
  smt [hq]

example (b g : Bool) (hg : g = true) : (if b then true else g) = true := by
  smt [hg]
