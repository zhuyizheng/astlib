/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Order.StrictWellOrder
/-!
# Pullbacks of relations

`pullback τ R S` is the relation `R` pulled back along `τ` to `S`. It is a strict well-order on
`S` if `R` is a strict well-order and `τ` is injective (`IsStrictWellOrder.pullback`).
-/

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin RudimentaryTerm MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] {R S T a τ x y : M}

section Pullback

variable [ModelsKP M]

/-- The class of pairs `z` with `τ ﹫ left z [R] τ ﹫ right z` -/
def PullbackClass (τ R : M) : Class M := fun z ↦ (τ ﹫ left z) [R] (τ ﹫ right z)

/-- `PullbackClass τ R` is defined by a `Δ₀` formula with parameters `τ` and `R` -/
theorem pullbackClass_eq (τ R : M) : PullbackClass τ R = (((&0 ∈₀ &1).substBoundRud
    ![ᵣ((ᵣ1) ﹫ (ᵣ0).left, (ᵣ1) ﹫ (ᵣ0).right), ᵣ2] : L.DeltaZeroBoundedFormula 3)
      |>.toBoundedFormula.multiclass.slice ![τ, R] : Class M) := by
  funext z
  rw [Multiclass.toClass_iff, Multiclass.slice, Fin.append_vec₁_vec₂, BoundedFormula.multiclass,
    DeltaZeroBoundedFormula.realize_substBoundRud]
  simp [PullbackClass]

instance (τ R : M) : (PullbackClass τ R).DeltaZero Set.univ := by
  rw [pullbackClass_eq]
  infer_instance

/-- The relation `R` pulled back along `τ` to `S` -/
noncomputable def pullback (τ R S : M) : M := (S ×ˢ S) ∩₀ PullbackClass τ R

theorem rel_pullback_iff : y [pullback τ R S] x ↔ (y ∈ S ∧ x ∈ S) ∧ (τ ﹫ y) [R] (τ ﹫ x) := by
  simp [pullback, PullbackClass]

theorem isRelationOn_pullback : IsRelationOn (pullback τ R S) S :=
  (isRelationOn_sprod S).subset (comprehension_subset _ _)

/-- A strict well-order pulled back along an injection is a strict well-order -/
theorem IsStrictWellOrder.pullback (hR : IsStrictWellOrder R T) (hτ : τ !: S ↪ T) :
    IsStrictWellOrder (pullback τ R S) S := by
  have hlin : IsStrictLinearOrder R T := hR.isStrictLinearOrder
  have hτT {x : M} (hx : x ∈ S) : τ ﹫ x ∈ T := hτ.isFunctionFromTo.val_mem hx
  refine IsStrictWellFounded.isStrictWellOrder ⟨isRelationOn_pullback, fun b hbS hb ↦ ?_⟩
    (fun x hx y hy z hz hxy hyz ↦ ?_) fun x hx y hy ↦ ?_
  · -- an `R`-minimal element of the image of `b`
    have hτb {y : M} (hy : y ∈ b) : τ ﹫ y ∈ τ '' b := by
      simp only [mem_image_iff]
      exact ⟨y, hy, rel_val hτ.isFunctionFromTo.isFunction (hτ.isFunctionFromTo.dom_eq ▸ hbS hy)⟩
    simp only [ne_empty_iff b] at hb
    obtain ⟨x, hx⟩ := hb
    have himage : τ '' b ⊆ T := by
      intro t ht
      simp only [mem_image_iff] at ht
      obtain ⟨y, hy, hyt⟩ := ht
      rw [← hτ.isFunctionFromTo.isFunction.val_eq_of_rel hyt]
      exact hτT (hbS hy)
    obtain ⟨t, ht, hmin⟩ := hR.isStrictWellFounded.exists_minimal himage (hτb hx)
    simp only [mem_image_iff] at ht
    obtain ⟨m, hm, hmt⟩ := ht
    rw [← hτ.isFunctionFromTo.isFunction.val_eq_of_rel hmt] at hmin
    refine ⟨m, hm, fun y hy hym ↦ ?_⟩
    simp only [rel_pullback_iff] at hym
    exact hmin _ (hτb hy) hym.right
  · grind [rel_pullback_iff, hlin.trans]
  · grind [rel_pullback_iff, hlin.trichotomous (hτT hx) (hτT hy), hτ.eq hx hy]

end Pullback

end FirstOrder.Language.MemStructure
