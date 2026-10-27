/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Mathlib.ModelTheory.Completeness.Completeness

/-!
# Derived rules of the proof system

Using the completeness theorem, we derive rules of the proof system `Γ ⊢' φ` from the fact that
the corresponding semantic statements hold in every nonempty structure.

## Main results

- `FirstOrder.Language.BoundedFormula.Provable.of_realize`: a formula which holds in every
  nonempty structure is provable.
-/

open Fin FirstOrder Language Structure

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α : Type w} {n : ℕ}

namespace BoundedFormula

namespace Provable

/-! ### Derived rules -/

variable {Γ : Set (L.Formula α)} {φ ψ θ : L.BoundedFormula α n}

/-- A formula which holds in every nonempty structure is provable. -/
theorem of_realize (h : ∀ (M : Type (max u v w)) [L.Structure M] [Nonempty M] (v : α → M)
    (xs : Fin n → M), φ.Realize v xs) : Γ ⊢' φ :=
  of_models.{u, v, w, 0} fun M _ _ v xs _ ↦ h M v xs

theorem mp₂ (h : Γ ⊢' φ ⟹ ψ ⟹ θ) (hφ : Γ ⊢' φ) (hψ : Γ ⊢' ψ) : Γ ⊢' θ :=
  of_models.{u, v, w, 0} fun _ _ _ v xs hΓ ↦ by
    have h := h.sound v hΓ xs
    simp only [realize_imp] at h
    exact h (hφ.sound v hΓ xs) (hψ.sound v hΓ xs)

/-- Transitivity of implication. -/
theorem imp_trans (h₁ : Γ ⊢' φ ⟹ ψ) (h₂ : Γ ⊢' ψ ⟹ θ) : Γ ⊢' φ ⟹ θ :=
  of_models.{u, v, w, 0} fun _ _ _ v xs hΓ ↦ by
    have h₁ := h₁.sound v hΓ xs
    have h₂ := h₂.sound v hΓ xs
    simp only [realize_imp] at h₁ h₂ ⊢
    exact fun h ↦ h₂ (h₁ h)

theorem and_iff : Γ ⊢' φ ⊓ ψ ↔ Γ ⊢' φ ∧ Γ ⊢' ψ := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hφ, hψ⟩ ↦ ?_⟩ <;>
    refine of_models.{u, v, w, 0} fun _ _ _ v xs hΓ ↦ ?_
  · exact (realize_inf.mp (h.sound v hΓ xs)).left
  · exact (realize_inf.mp (h.sound v hΓ xs)).right
  · exact realize_inf.mpr ⟨hφ.sound v hΓ xs, hψ.sound v hΓ xs⟩

theorem iff_iff : Γ ⊢' φ ⇔ ψ ↔ Γ ⊢' φ ⟹ ψ ∧ Γ ⊢' ψ ⟹ φ :=
  and_iff

theorem iff_refl : Γ ⊢' φ ⇔ φ :=
  of_realize fun _ _ _ _ _ ↦ by simp

/-- Universal generalization over several bound variables. -/
theorem all' {m : ℕ} {φ : L.BoundedFormula α (n + m)} (h : Γ ⊢' φ) : Γ ⊢' φ.all' m :=
  of_models.{u, v, w, 0} fun _ _ _ v xs hΓ ↦ by
    rw [realize_all']
    exact fun ys ↦ h.sound v hΓ _

end Provable

end BoundedFormula

end Language

end FirstOrder
