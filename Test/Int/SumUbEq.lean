import Smt

-- cvc5 adds the two equalities with ARITH_SUM_UB, whose conclusion is `≤` also when every premise is `=`.
example (x y : Int) (h₁ : x + -1 * y = 0) (h₂ : -1 * x + y = -1) : False := by
  smt [h₁, h₂]
