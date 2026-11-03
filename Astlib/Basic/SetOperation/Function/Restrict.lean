/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Function.FromTo
/-!
# Restrictions and images

Restrictions `f ↾ a` of functions and images `f '' a`.
-/

open Fin FirstOrder Language MemStructure RudimentaryTerm DeltaZeroBoundedFormula

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M]

section Restrict

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.restrict₀
  {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 2 :=
  (ᵣ0 : L.RudimentaryTerm 2) ∩ ((ᵣ1 : L.RudimentaryTerm 2) ×ˢ (ᵣ0 : L.RudimentaryTerm 2).ran)

@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.restrict
  {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r s : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  restrict₀.substBoundRud ![r, s]

infix:88 " ↾ " => FirstOrder.Language.RudimentaryTerm.restrict

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
  (restrict₀ : L.RudimentaryTerm 2).CharFree := by
  unfold restrict₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] : (r ↾ s).CharFree := by
  unfold restrict; infer_instance

noncomputable def restrict (f a : M) := restrict₀ 〘f, a〙₂
-- noncomputable def restrict (f a : M) := (∃'∈ &0 (&2).eqLeft &1) 〘a, ∈ f〙₀

infix:88 " ↾ " => FirstOrder.Language.MemStructure.restrict

omit [RudClosed M] in
@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_restrict₀ (xs : Fin 2 → M) :
    restrict₀〘xs〙 = (xs 0 ↾ xs 1 : M) := by
  simp only [restrict]
  rw [Matrix.vec_fin_two_eq]

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ ys 0 ↾ ys 1) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ restrict₀ fun _ _ ↦ rfl

theorem restrict_eq (f a : M) :
    f ↾ a = f ∩ (a ×ˢ ran f) := by
  simp [restrict, restrict₀]
  -- congr 2

theorem mem_restrict_iff (f a z : M) :
    z ∈ f ↾ a ↔ z ∈ f ∧ ∃ x ∈ a, ∃ y, z = !(x, y) := by
  simp only [restrict_eq, mem_inter_iff, mem_sprod_iff, and_congr_right_iff]
  grind

theorem rel_restrict_iff (f x y : M) :
    x [f ↾ a] y ↔ x [f] y ∧ x ∈ a := by
  grind [mem_restrict_iff]

theorem restrict_subset (f a : M) : f ↾ a ⊆ f := by
  grind [mem_restrict_iff]

@[simp, grind =]
theorem empty_restrict (a : M) : (∅ : M) ↾ a = ∅ := by
  grind [restrict_subset]

@[simp, grind .]
theorem IsFunction.restrict {f : M} (hf : IsFunction f) (a : M) :
    IsFunction (f ↾ a) :=
  hf.subset (restrict_subset _ _)

@[simp, grind .]
theorem dom_restrict {f : M} (hf : IsFunction f) (a : M) :
    dom (f ↾ a) = dom f ∩ a := by
  ext; grind [rel_restrict_iff]

@[simp, grind .]
theorem val_restrict (f : M) (hf : IsFunction f)
    {x a : M} (hx : x ∈ a) (hx' : x ∈ dom f) :
    (f ↾ a) ﹫ x = f ﹫ x := by
  grind [show x [f ↾ a] (f ﹫ x) by grind [rel_restrict_iff] ]

theorem restrict_eq_inter_sprod (f a : M) :
    f ↾ a = f ∩ (a ×ˢ ran f) := by
  ext
  simp only [mem_inter_iff]
  grind [mem_restrict_iff]

@[simp, grind =]
theorem restrict_restrict
    (f a b : M) : (f ↾ a) ↾ b = f ↾ (a ∩ b) := by
  ext
  simp only [mem_restrict_iff, mem_inter_iff]
  grind

theorem restrict_inter
    (f a b : M) : f ↾ (a ∩ b) = f ↾ a ∩ f ↾ b := by
  ext
  simp only [mem_restrict_iff, mem_inter_iff]
  grind

theorem restrict_union
    (f a b : M) : f ↾ (a ∪ b) = f ↾ a ∪ f ↾ b := by
  ext; grind [mem_restrict_iff]

theorem restrict_sUnion
    (f X z : M) : z ∈ f ↾ ⋃₀ X ↔ ∃ a ∈ X, z ∈ f ↾ a := by
  grind [mem_restrict_iff]

@[simp, grind =]
theorem restrict_empty (f : M) : (f ↾ ∅) = ∅ := by
  ext; grind [mem_restrict_iff]

@[simp, grind =]
theorem restrict_dom {f : M} (hf : IsFunction f) : (f ↾ dom f) = f := by
  apply hf.restrict (dom f) |>.ext hf <;> grind

theorem dom_restrict_of_subset {f a : M} (hf : IsFunction f) (ha : a ⊆ dom f) :
    dom (f ↾ a) = a := by
  ext; grind

/-- A function `a → b` restricts to a function `a' → b` for `a' ⊆ a` -/
theorem IsFunctionFromTo.restrict {f a b a' : M} (hf : f !: a → b) (ha : a' ⊆ a) :
    f ↾ a' !: a' → b := by
  refine ⟨hf.isFunction.restrict a', dom_restrict_of_subset hf.isFunction (by grind), ?_⟩
  grind [rel_restrict_iff]

/-- An injection `a ↪ b` restricts to an injection `a' ↪ b'` for `a' ⊆ a` and `b ⊆ b'` -/
theorem IsInjectionFromTo.restrict {f a b a' b' : M} (hf : f !: a ↪ b) (ha : a' ⊆ a)
    (hb : b ⊆ b') : f ↾ a' !: a' ↪ b' := by
  refine isInjectionFromTo_of_val (hf.isFunction.restrict a')
    (dom_restrict_of_subset hf.isFunction (by grind)) (fun z hz ↦ ?_)
    fun z hz z' hz' h ↦ ?_ <;> grind

/-- Two functions agreeing on a common subset of their domains have the same restriction to it -/
theorem IsFunction.restrict_eq_restrict {f g a : M} (hf : IsFunction f) (hg : IsFunction g)
    (hfa : a ⊆ dom f) (hga : a ⊆ dom g) (h : ∀ x ∈ a, f ﹫ x = g ﹫ x) : f ↾ a = g ↾ a := by
  apply (hf.restrict a).ext (hg.restrict a)
  · simp [hf, hfa, hg, hga]
  · intro x hx
    simp only [hf, dom_restrict, hfa, inter_of_subset_left] at hx
    simp [val_restrict, hf, hg, h, hx, hfa hx, hga hx]

end Restrict

section Image

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

noncomputable def image (f a : M) := ran (f ↾ a)

infix:88 " '' " => FirstOrder.Language.MemStructure.image

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ ys 0 '' ys 1) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ (restrict₀.substBoundRud ![ᵣ0, ᵣ1]).ran fun _ _ ↦ by
    simp [image]

@[simp, grind =]
theorem image_empty (f : M) : f '' ∅ = ∅ := by
  grind [image]

@[simp, grind =]
theorem image_dom (f : M) : f '' (dom f) = ran f := by
  ext; grind [image, mem_restrict_iff]

theorem image_union (f a b : M) : f '' (a ∪ b) = f '' a ∪ f '' b := by
  grind [image, restrict_union, ran_union]

@[simp]
theorem mem_image_iff (f a y : M) : y ∈ f '' a ↔ ∃ x ∈ a, x [f] y := by
  simp only [image, mem_ran_iff, rel_restrict_iff]
  grind

theorem mem_image_sUnion_iff (f X z : M) :
    z ∈ f '' (⋃₀ X) ↔ ∃ a ∈ X, z ∈ f '' a := by
  grind [image, restrict_sUnion]

end Image

end FirstOrder.Language.MemStructure
