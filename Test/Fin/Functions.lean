import Smt

-- Each side can have its own symbolic bound. The same index may occur twice,
-- and Nat and Bool arguments can occur on either side of a finite argument.
example (m n : Nat) (r : Fin m → Fin n → Bool) (i : Fin m) (j : Fin n)
    (h : ∀ a b, r a b = true → a.val < b.val) (on : r i j = true) :
    i.val < j.val := by smt [h, on]

example (n : Nat) (f : Nat → Fin n → Bool → Nat) (i : Fin n) (b : Bool)
    (h : ∀ a j k, f a j k ≤ a + j.val) : f 2 i b < n + 2 := by smt [h]

example (m n : Nat) (f : Nat → Fin m → Fin n → Fin n) (i : Fin m) (j : Fin n) :
    (f 0 i j).val < n := by smt

example (n : Nat) (r : Nat → Fin n → Nat → Fin n → Bool) (i j : Fin n)
    (h : ∀ a b, r 2 a 3 b = true → a ≠ b) (on : r 2 i 3 j = true) :
    i.val ≠ j.val := by smt [h, on]

example (n : Nat) (r : Nat → Bool → Nat → Bool → Fin n → Bool)
    (h : ∀ i, r 0 true 0 false i = true) (j : Fin n) :
    r 0 true 0 false j = true := by smt [h]

-- A field over an empty index set satisfies the pointwise bound vacuously.
example (read : Fin 0 → Nat) : ∀ i, read i < 3 := by smt

-- Fin input support depends on the position of the index, even for a longer field.
example (n : Nat) (f : Fin n → Int → Int → Int → Int → Int → Int)
    (h : ∀ i, f i 0 0 0 0 0 ≤ 1) (i : Fin n) : f i 0 0 0 0 0 ≤ 1 := by smt [h]

/-- error: [embedding] Fin in this function signature requires support beyond five arguments -/
#guard_msgs in
example (n : Nat) (f : Int → Int → Int → Int → Int → Fin n → Int)
    (h : ∀ i, f 0 0 0 0 0 i ≤ 1) (i : Fin n) : f 0 0 0 0 0 i ≤ 1 := by smt [h]
