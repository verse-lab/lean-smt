import Smt

namespace FinVeil

-- Reset one cell of a two-dimensional field while preserving a global bound.
theorem writePair (m n : Nat) (row : Fin m) (col : Fin n)
    (old : Fin m → Fin n → Nat) (h : ∀ i j, old i j ≤ 3) (i : Fin m) (j : Fin n) :
    (if i = row ∧ j = col then 2 else old i j) ≤ 3 := by
  smt [h]

-- A transition relation records both the write and its frame condition.
theorem frame (n : Nat) (old next : Fin n → Nat) (idx : Fin n)
    (step : ∀ i, next i = if i = idx then 1 else old i) :
    ∀ i, i ≠ idx → next i = old i := by smt [step]

-- Different field types participate in one transition.
theorem activate (n : Nat) (marked : Fin n → Bool) (value : Fin n → Nat)
    (safe : ∀ i, marked i = true → value i < 5) (idx j : Fin n)
    (post : (if j = idx then true else marked j) = true) :
    (if j = idx then 4 else value j) < 5 := by smt [safe, post]

-- A finite identifier returned by one field indexes another.
theorem route (m n : Nat) (owner : Fin m → Fin n) (ready : Fin n → Bool)
    (allReady : ∀ j, ready j = true) (i : Fin m) : ready (owner i) = true := by smt [allReady]

-- A quantified transition produces a successor state bounded by the same invariant.
theorem writeBound (m n : Nat) (old next : Fin m → Fin n → Nat) (r : Fin m) (c : Fin n)
    (bounded : ∀ i j, old i j ≤ 3)
    (step : ∀ i j, next i j = if i = r ∧ j = c then 3 else old i j) :
    ∀ i j, next i j ≤ 3 := by smt [bounded, step]

-- Fin-valued fields and conditional indices occur when updating an identifier map.
theorem writeOwner (n : Nat) (key value : Fin n) (old next : Fin n → Fin n)
    (step : ∀ i, next i = if i = key then value else old i) : (next key).val = value.val := by
  smt [step]

theorem readEither (n : Nat) (i j : Fin n) (useFirst : Bool)
    (count : Fin n → Nat) (bounded : ∀ k, count k ≤ 3) :
    count (if useFirst then i else j) ≤ 3 := by smt [bounded]

-- An assignment at a distinct index leaves a concrete counterexample to the converse.
theorem writeDoesNotSetEveryCell :
    ∃ key other : Fin 2, key ≠ other ∧ (if key = other then 3 else 0) ≠ 3 := by smt

private abbrev Index := Fin 4

-- Normalizing the bounded expression to Nat must not erase the fact that a
-- later user-sort query needs a proof of existence in Lean.
example : True := by
  fail_if_success
    have bad (α : Type) (p : Nat → α → Prop) (i : Index) :
        ∃ x, p (i + 1).val x ∨ ¬ p (i + 1).val x := by smt +trust
  trivial

theorem withWitness (α : Type) (_w : α) (p : Nat → α → Prop) (i : Index) :
    ∃ x, p (i + 1).val x ∨ ¬ p (i + 1).val x := by smt +trust

end FinVeil

-- SMT must reconstruct each state proof; an admitted goal also compiles in Lean.
open Lean in
run_cmd do
  for name in [``FinVeil.writePair, ``FinVeil.frame, ``FinVeil.activate, ``FinVeil.route,
      ``FinVeil.writeBound, ``FinVeil.writeOwner, ``FinVeil.readEither,
      ``FinVeil.writeDoesNotSetEveryCell, ``FinVeil.withWitness] do
    let unexpected := (← collectAxioms name).filter (!#[``propext, ``Classical.choice, ``Quot.sound].contains ·)
    unless unexpected.isEmpty do
      throwError "{name} uses unexpected axioms {unexpected}"
