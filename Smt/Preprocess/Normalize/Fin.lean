module

public import Smt.Preprocess.Normalize.Attribute
public import Init.Data.Fin.Lemmas
import Lean.Elab.Tactic.Omega

public section

namespace Smt.Preprocess.Normalize

attribute [fin_normalize ↓] Fin.ext_iff Fin.le_def Fin.lt_def
attribute [fin_normalize ↓ ←] Fin.val_ne_iff
attribute [fin_normalize ↓] Fin.val_succ Fin.val_last Fin.val_cast Fin.val_castLE Fin.val_castLT Fin.val_castSucc
attribute [fin_normalize ↓] Fin.val_mul Fin.val_mod

-- The sum of two indices can wrap at most once. Keeping the resulting constraint
-- linear lets the arithmetic proof reconstructor handle symbolic bounds.
@[fin_normalize ↓] theorem finValAdd (i j : Fin n) : (i + j).val =
    if i.val + j.val < n then i.val + j.val else i.val + j.val - n := by
  rw [Fin.val_add]
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt ‹_›)]
    apply Nat.mod_eq_of_lt
    have := i.isLt
    have := j.isLt
    omega

@[fin_normalize ↓] theorem finValSub (i j : Fin n) : (i - j).val =
    if j.val ≤ i.val then i.val - j.val else n + i.val - j.val := by
  split
  · exact Fin.sub_val_of_le ‹_›
  · exact Fin.coe_sub_iff_lt.mpr (Nat.lt_of_not_ge ‹_›)

end Smt.Preprocess.Normalize
