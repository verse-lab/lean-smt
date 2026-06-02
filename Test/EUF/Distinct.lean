import Smt

example [Nonempty U] {a b c : U} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    distinctN [a, b, c] := by
  smt_show [hab, hac, hbc]
  exact ⟨hab, hac, hbc⟩

example [Nonempty U] {a b c : U} (h : distinctN [a, b, c]) : a ≠ c := by
  smt [h]
