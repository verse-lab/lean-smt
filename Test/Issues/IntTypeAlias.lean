import Smt

@[reducible] def FieldType (domains : List Type) (codomain : Type) : Type :=
  domains.foldr (· → ·) codomain

example (x : Int) (hx : 0 ≤ x) : x + 1 > 0 := by
  change @HAdd.hAdd Int (FieldType [] Int) Int (@instHAdd Int Int.instAdd) x
      (@OfNat.ofNat (FieldType [] Int) (nat_lit 1) (@instOfNat (nat_lit 1))) > 0
  smt [hx]
