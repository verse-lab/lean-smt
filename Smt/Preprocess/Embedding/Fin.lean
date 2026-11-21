/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Pîrlea
-/

module

public meta import Smt.Preprocess.Embedding
public import Smt.Preprocess.Embedding.Attribute
public meta import Smt.Preprocess.Embedding.Attribute

public import Lean
public meta import Lean

public section

attribute [fin_embedding ↓] Fin.ext_iff
attribute [fin_embedding ↓ ←] Fin.val_ne_iff
attribute [fin_embedding ↓] Fin.val_zero
attribute [fin_embedding ↓] Fin.val_one
attribute [fin_embedding ↓] Fin.val_ofNat
attribute [fin_embedding ↓] Fin.mk.injEq
attribute [fin_embedding ↓] Fin.val_mk
attribute [fin_embedding ↓] Fin.le_def
attribute [fin_embedding ↓] Fin.lt_def

namespace Smt.Preprocess.Embedding

def ofIntFin (n : Nat) (x : Int) (h : 0 ≤ x ∧ x < n) : Fin n :=
  ⟨x.toNat, (Int.toNat_lt h.1).2 h.2⟩

@[fin_embedding ↓]
theorem Int.natCast_ofIntFin {n : Nat} {x : Int} {h : 0 ≤ x ∧ x < n} :
    (((ofIntFin n x h : Fin n) : Nat) : Int) = x :=
  Int.toNat_of_nonneg h.1

@[fin_embedding ↓]
theorem intValOfNat (m n : Nat) [NeZero n] :
    (((no_index (OfNat.ofNat m : Fin n)).val : Nat) : Int) = (OfNat.ofNat m : Int) % n :=
  Int.natCast_emod m n

@[fin_embedding ↓]
theorem intValIte (c : Prop) [Decidable c] (i j : Fin n) :
    (((if c then i else j).val : Nat) : Int) = if c then (i.val : Int) else (j.val : Int) := by
  split <;> rfl

theorem fin_bounds {n : Nat} (x : Fin n) : 0 ≤ (x.val : Int) ∧ (x.val : Int) < n :=
  ⟨Int.natCast_nonneg x.val, Int.ofNat_lt.mpr x.isLt⟩

theorem ofIntFin_of_fin {n : Nat} (x : Fin n)
    (h : 0 ≤ ((x : Nat) : Int) ∧ ((x : Nat) : Int) < n) :
    ofIntFin n ((x : Nat) : Int) h = x := by
  apply Fin.ext
  simp [ofIntFin]

@[fin_embedding ↓]
theorem forall_fin_as_int {n : Nat} {p : Fin n → Prop} :
    (∀ x : Fin n, p x) ↔
    (∀ x : Int, (h : 0 ≤ x ∧ x < n) → p (ofIntFin n x h)) := by
  constructor
  · intro h x hx
    exact h (ofIntFin n x hx)
  · intro h x
    have hx := h ((x : Nat) : Int) (fin_bounds x)
    simpa [ofIntFin_of_fin] using hx

@[fin_embedding ↓]
theorem exists_fin_as_int {n : Nat} {p : Fin n → Prop} :
    (∃ x : Fin n, p x) ↔
    (∃ x : Int, (0 ≤ x ∧ x < n) ∧ ∀ h, p (ofIntFin n x h)) := by
  constructor
  · intro ⟨x, hx⟩
    refine ⟨(x : Nat), ?_, ?_⟩
    · exact fin_bounds x
    · intro h
      simpa [ofIntFin_of_fin] using hx
  · intro ⟨x, hx, hp⟩
    exact ⟨ofIntFin n x hx, hp hx⟩

theorem forall_fin_out_as_int₁ {n : Nat} {p : (α₁ → Fin n) → Prop} :
    (∀ f : α₁ → Fin n, p f) ↔
    (∀ f : α₁ → Int, (hf : ∀ a₁, 0 ≤ f a₁ ∧ f a₁ < n) →
      p (fun a₁ => ofIntFin n (f a₁) (hf a₁))) := by
  constructor
  · intro h f hf
    exact h (fun a₁ => ofIntFin n (f a₁) (hf a₁))
  · intro h f
    have hf := h (fun a₁ => ((f a₁ : Nat) : Int)) (fun a₁ => fin_bounds (f a₁))
    simpa [ofIntFin_of_fin] using hf

theorem forall_fin_out_as_int₂ {n : Nat} {p : (α₁ → α₂ → Fin n) → Prop} :
    (∀ f : α₁ → α₂ → Fin n, p f) ↔
    (∀ f : α₁ → α₂ → Int, (hf : ∀ a₁ a₂, 0 ≤ f a₁ a₂ ∧ f a₁ a₂ < n) →
      p (fun a₁ a₂ => ofIntFin n (f a₁ a₂) (hf a₁ a₂))) := by
  constructor
  · intro h f hf
    exact h (fun a₁ a₂ => ofIntFin n (f a₁ a₂) (hf a₁ a₂))
  · intro h f
    have hf := h (fun a₁ a₂ => ((f a₁ a₂ : Nat) : Int)) (fun a₁ a₂ => fin_bounds (f a₁ a₂))
    simpa [ofIntFin_of_fin] using hf

theorem forall_fin_out_as_int₃ {n : Nat} {p : (α₁ → α₂ → α₃ → Fin n) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → Fin n, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → Int,
      (hf : ∀ a₁ a₂ a₃, 0 ≤ f a₁ a₂ a₃ ∧ f a₁ a₂ a₃ < n) →
      p (fun a₁ a₂ a₃ => ofIntFin n (f a₁ a₂ a₃) (hf a₁ a₂ a₃))) := by
  constructor
  · intro h f hf
    exact h (fun a₁ a₂ a₃ => ofIntFin n (f a₁ a₂ a₃) (hf a₁ a₂ a₃))
  · intro h f
    have hf := h (fun a₁ a₂ a₃ => ((f a₁ a₂ a₃ : Nat) : Int)) (fun a₁ a₂ a₃ => fin_bounds (f a₁ a₂ a₃))
    simpa [ofIntFin_of_fin] using hf

theorem forall_fin_out_as_int₄ {n : Nat} {p : (α₁ → α₂ → α₃ → α₄ → Fin n) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → Fin n, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → Int,
      (hf : ∀ a₁ a₂ a₃ a₄, 0 ≤ f a₁ a₂ a₃ a₄ ∧ f a₁ a₂ a₃ a₄ < n) →
      p (fun a₁ a₂ a₃ a₄ => ofIntFin n (f a₁ a₂ a₃ a₄) (hf a₁ a₂ a₃ a₄))) := by
  constructor
  · intro h f hf
    exact h (fun a₁ a₂ a₃ a₄ => ofIntFin n (f a₁ a₂ a₃ a₄) (hf a₁ a₂ a₃ a₄))
  · intro h f
    have hf := h (fun a₁ a₂ a₃ a₄ => ((f a₁ a₂ a₃ a₄ : Nat) : Int)) (fun a₁ a₂ a₃ a₄ => fin_bounds (f a₁ a₂ a₃ a₄))
    simpa [ofIntFin_of_fin] using hf

theorem forall_fin_out_as_int₅ {n : Nat} {p : (α₁ → α₂ → α₃ → α₄ → α₅ → Fin n) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Fin n, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → α₅ → Int,
      (hf : ∀ a₁ a₂ a₃ a₄ a₅, 0 ≤ f a₁ a₂ a₃ a₄ a₅ ∧ f a₁ a₂ a₃ a₄ a₅ < n) →
      p (fun a₁ a₂ a₃ a₄ a₅ => ofIntFin n (f a₁ a₂ a₃ a₄ a₅) (hf a₁ a₂ a₃ a₄ a₅))) := by
  constructor
  · intro h f hf
    exact h (fun a₁ a₂ a₃ a₄ a₅ => ofIntFin n (f a₁ a₂ a₃ a₄ a₅) (hf a₁ a₂ a₃ a₄ a₅))
  · intro h f
    have hf := h (fun a₁ a₂ a₃ a₄ a₅ => ((f a₁ a₂ a₃ a₄ a₅ : Nat) : Int))
      (fun a₁ a₂ a₃ a₄ a₅ => fin_bounds (f a₁ a₂ a₃ a₄ a₅))
    simpa [ofIntFin_of_fin] using hf

/-- To extend a function outside the interval, use an element of its domain or codomain.
This condition matters when `n = 0` and the codomain is empty. -/
class FinExtension (n : Nat) (β : Sort u) : Prop where
  existsDefault : (Fin n → β) → Nonempty β

instance [Nonempty β] : FinExtension n β := ⟨fun _ => ‹Nonempty β›⟩
instance [NeZero n] : FinExtension n β := ⟨fun f => ⟨f 0⟩⟩

noncomputable def extFin {n : Nat} {β : Sort u} [FinExtension n β] (f : Fin n → β) (b : Int) : β :=
  if hb : 0 ≤ b ∧ b < n then f (ofIntFin n b hb) else Classical.choice (FinExtension.existsDefault f)

theorem extFin_cast {n : Nat} {β : Sort u} [FinExtension n β] (f : Fin n → β) (a : Fin n) :
    extFin f ((a : Nat) : Int) = f a := by
  have hb := fin_bounds a
  unfold extFin
  split
  · exact congrArg f (ofIntFin_of_fin a _)
  · rename_i hn
    exact absurd hb hn

@[fin_embedding ↓]
theorem forall_fin_in_as_int₁ {n : Nat} [FinExtension n α₁] {p : (Fin n → α₁) → Prop} :
    (∀ f : Fin n → α₁, p f) ↔
    (∀ f : Int → α₁, p (fun a => f ((a : Nat) : Int))) := by
  constructor
  · intro h f
    exact h (fun a => f ((a : Nat) : Int))
  · intro h f
    have hf := h (extFin f)
    simpa [extFin_cast] using hf

@[fin_embedding ↓]
theorem forall_fin_in_as_int₂ {n : Nat} [FinExtension n α₂]
    {p : (α₁ → Fin n → α₂) → Prop} :
    (∀ f : α₁ → Fin n → α₂, p f) ↔
    (∀ f : α₁ → Int → α₂, p (fun a₁ a => f a₁ ((a : Nat) : Int))) := by
  constructor
  · intro h f
    exact h (fun a₁ a => f a₁ ((a : Nat) : Int))
  · intro h f
    have hf := h (fun a₁ => extFin (f a₁))
    simpa [extFin_cast] using hf

@[fin_embedding ↓]
theorem forall_fin_in_as_int₃ {n : Nat} [FinExtension n α₃]
    {p : (α₁ → α₂ → Fin n → α₃) → Prop} :
    (∀ f : α₁ → α₂ → Fin n → α₃, p f) ↔
    (∀ f : α₁ → α₂ → Int → α₃, p (fun a₁ a₂ a => f a₁ a₂ ((a : Nat) : Int))) := by
  constructor
  · intro h f
    exact h (fun a₁ a₂ a => f a₁ a₂ ((a : Nat) : Int))
  · intro h f
    have hf := h (fun a₁ a₂ => extFin (f a₁ a₂))
    simpa [extFin_cast] using hf

@[fin_embedding ↓]
theorem forall_fin_in_as_int₄ {n : Nat} [FinExtension n α₄]
    {p : (α₁ → α₂ → α₃ → Fin n → α₄) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → Fin n → α₄, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → Int → α₄, p (fun a₁ a₂ a₃ a => f a₁ a₂ a₃ ((a : Nat) : Int))) := by
  constructor
  · intro h f
    exact h (fun a₁ a₂ a₃ a => f a₁ a₂ a₃ ((a : Nat) : Int))
  · intro h f
    have hf := h (fun a₁ a₂ a₃ => extFin (f a₁ a₂ a₃))
    simpa [extFin_cast] using hf

@[fin_embedding ↓]
theorem forall_fin_in_as_int₅ {n : Nat} [FinExtension n α₅]
    {p : (α₁ → α₂ → α₃ → α₄ → Fin n → α₅) → Prop} :
    (∀ f : α₁ → α₂ → α₃ → α₄ → Fin n → α₅, p f) ↔
    (∀ f : α₁ → α₂ → α₃ → α₄ → Int → α₅,
      p (fun a₁ a₂ a₃ a₄ a => f a₁ a₂ a₃ a₄ ((a : Nat) : Int))) := by
  constructor
  · intro h f
    exact h (fun a₁ a₂ a₃ a₄ a => f a₁ a₂ a₃ a₄ ((a : Nat) : Int))
  · intro h f
    have hf := h (fun a₁ a₂ a₃ a₄ => extFin (f a₁ a₂ a₃ a₄))
    simpa [extFin_cast] using hf

public meta section

open Lean Meta Simp

/-- Fin domains have their own bounded encoding. Every other argument sort in a synthesized
range constraint must be inhabited: in SMT, `∀ a, 0 ≤ f a ∧ f a < 0` is contradictory,
while Lean admits such a function on an empty domain. Check the actual signature whenever
applying an output rule, including rules exposed by earlier simplification. -/
simproc ↓ [fin_embedding] embed_fin_output (∀ _ : _ → _, _) := fun e => do
  let .forallE _ ty _ _ := e | return .continue
  let arities := #[``forall_fin_out_as_int₁, ``forall_fin_out_as_int₂, ``forall_fin_out_as_int₃,
    ``forall_fin_out_as_int₄, ``forall_fin_out_as_int₅]
  let some (domains, result) ← Smt.Preprocess.functionSignature ty | return .continue
  if domains.size > arities.size then
    if result.isAppOfArity ``Fin 1 || (← (domains.extract arities.size domains.size).anyM
        fun d => return (← whnf d).isAppOfArity ``Fin 1) then
      throwError "[embedding] Fin in this function signature requires support beyond five arguments"
    return .continue
  unless result.isAppOfArity ``Fin 1 && !domains.isEmpty do return .continue
  let thm := arities[domains.size - 1]!
  -- Inspect the arrow spine without introducing hypothetical instances from its arguments.
  for domain in domains do
    unless (← whnf domain).isAppOfArity ``Fin 1 do
      unless (← synthInstance? (← mkAppM ``Nonempty #[domain])).isSome do
        throwError "[embedding] Fin-valued function needs an inhabited argument type, got {domain}"
  let proof ← mkConstWithFreshMVarLevels thm
  let (args, _, type) ← forallMetaTelescope (← inferType proof)
  let some (lhs, rhs) := type.iff? | return .continue
  unless ← isDefEq lhs e do return .continue
  return .visit { expr := ← instantiateMVars rhs, proof? := ← mkAppM ``propext #[mkAppN proof args] }

end

end Smt.Preprocess.Embedding
