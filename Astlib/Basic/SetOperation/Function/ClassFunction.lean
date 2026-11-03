/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Function.Update
/-!
# Set functions from class functions

Set functions from class functions:

* `IsSetRestrictedTo G x`: the restriction `G ↾₀ x` of the class function `G` to `x` is a set;
* `compLeft`; `Δ₀` instances for `IsFunction`, `IsFunctionFromTo` and its variants.
-/

open Fin FirstOrder Language MemStructure RudimentaryTerm DeltaZeroBoundedFormula

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M]

section ClassFunction

variable [L.ExtraConstantsUnaryRelationsOnly]

def IsSetRestrictedTo (G : ClassFunction M) (x : M) :=
  ∃ f : M, IsFunction f ∧ dom f = x ∧ ∀ y ∈ x, f ﹫ y = G y

noncomputable instance (G : ClassFunction M) : Decidable (IsSetRestrictedTo G x) :=
  Classical.propDecidable _

noncomputable def toSetRestrictedTo (G : ClassFunction M) (x : M) :=
  dite (IsSetRestrictedTo G x) Classical.choose default

infix:88 " ↾₀ " => FirstOrder.Language.MemStructure.toSetRestrictedTo

theorem toSetRestrictedTo_spec {G : ClassFunction M} {x : M}
    (h : IsSetRestrictedTo G x) :
    IsFunction (G ↾₀ x) ∧ dom (G ↾₀ x) = x ∧ ∀ y ∈ x, (G ↾₀ x) ﹫ y = G y := by
  simp only [toSetRestrictedTo] at h ⊢
  convert Classical.choose_spec h <;> simp [h]

@[simp]
theorem isFunction_toSetRestrictedTo {G : ClassFunction M} {x : M}
    (h : IsSetRestrictedTo G x) :
    IsFunction (G ↾₀ x) :=
  toSetRestrictedTo_spec h |>.left

@[simp]
theorem dom_toSetRestrictedTo {G : ClassFunction M} {x : M}
    (h : IsSetRestrictedTo G x) :
    dom (G ↾₀ x) = x :=
  toSetRestrictedTo_spec h |>.right.left

@[simp]
theorem val_toSetRestrictedTo {G : ClassFunction M} {x y : M}
    (h : IsSetRestrictedTo G x) (hy : y ∈ x) :
    (G ↾₀ x) ﹫ y = G y :=
  toSetRestrictedTo_spec h |>.right.right y hy

/-- The restriction of `G` to `x` is the unique function on `x` agreeing with `G` -/
theorem toSetRestrictedTo_eq [Extensional M] [RudClosed M] {G : ClassFunction M} {x f : M}
    (hf : IsFunction f) (hdom : dom f = x) (hval : ∀ y ∈ x, f ﹫ y = G y) : G ↾₀ x = f := by
  have h : IsSetRestrictedTo G x := ⟨f, hf, hdom, hval⟩
  grind [dom_toSetRestrictedTo, val_toSetRestrictedTo, isFunction_toSetRestrictedTo]

@[simp]
theorem mem_ran_toSetRestrictedTo_iff [Extensional M] [RudClosed M] {G : ClassFunction M}
    {x y : M} (h : IsSetRestrictedTo G x) : y ∈ ran (G ↾₀ x) ↔ ∃ z ∈ x, G z = y := by
  rw [(isFunction_toSetRestrictedTo h).mem_ran_iff, dom_toSetRestrictedTo h]
  exact exists_congr fun z ↦ and_congr_right fun hz ↦ by rw [val_toSetRestrictedTo h hz]

theorem mem_ran_restrict_toSetRestrictedTo_iff [Extensional M] [RudClosed M]
    {G : ClassFunction M} {x s y : M} (h : IsSetRestrictedTo G x) (hs : s ⊆ x) :
    y ∈ ran ((G ↾₀ x) ↾ s) ↔ ∃ z ∈ s, G z = y := by
  have hf : IsFunction (G ↾₀ x) := isFunction_toSetRestrictedTo h
  have hsd : s ⊆ dom (G ↾₀ x) := by rwa [dom_toSetRestrictedTo h]
  rw [(hf.restrict s).mem_ran_iff, dom_restrict_of_subset hf hsd]
  refine exists_congr fun z ↦ and_congr_right fun hz ↦ ?_
  rw [val_restrict _ hf hz (hsd hz), val_toSetRestrictedTo h (hs hz)]

theorem isFunctionFromTo_toSetRestrictedTo [Extensional M] [RudClosed M] {G : ClassFunction M}
    {a b : M} (h : IsSetRestrictedTo G a) (hG : ∀ x ∈ a, G x ∈ b) : G ↾₀ a !: a → b := by
  refine ⟨isFunction_toSetRestrictedTo h, dom_toSetRestrictedTo h, fun y hy ↦ ?_⟩
  simp only [mem_ran_toSetRestrictedTo_iff, h] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hG x hx

theorem isInjectionFromTo_toSetRestrictedTo [Extensional M] [RudClosed M] {G : ClassFunction M}
    {a b : M} (h : IsSetRestrictedTo G a) (hG : ∀ x ∈ a, G x ∈ b)
    (hinj : ∀ x ∈ a, ∀ y ∈ a, G x = G y → x = y) : G ↾₀ a !: a ↪ b := by
  refine ⟨isFunctionFromTo_toSetRestrictedTo h hG, fun x y hx hy hxy ↦ hinj x hx y hy ?_⟩
  rwa [val_toSetRestrictedTo h hx, val_toSetRestrictedTo h hy] at hxy

theorem isSurjectionFromTo_toSetRestrictedTo [Extensional M] [RudClosed M] {G : ClassFunction M}
    {a b : M} (h : IsSetRestrictedTo G a) (hG : ∀ y, y ∈ b ↔ ∃ x ∈ a, G x = y) :
    G ↾₀ a !: a ↠ b := by
  refine ⟨isFunctionFromTo_toSetRestrictedTo h fun x hx ↦ ?_, ?_⟩
  · rw [hG]
    exact ⟨x, hx, rfl⟩
  ext y
  simp only [mem_ran_toSetRestrictedTo_iff, h, hG]

end ClassFunction

section CompLeft

variable [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [RudClosed M]

/-- Composing with an injection is left-cancellative -/
theorem IsInjectionFromTo.comp_left_cancel {f a b c s s' : M} (hf : f !: b ↪ c)
    (hs : s !: a → b) (hs' : s' !: a → b) (h : f !∘ s = f !∘ s') : s = s' := by
  refine hs.isFunction.ext hs'.isFunction (by rw [hs.dom_eq, hs'.dom_eq]) fun k hk ↦ ?_
  rw [hs.dom_eq] at hk
  -- by injectivity of `f`, it suffices to show `f (s k) = f (s' k)`
  refine hf.eq (hs.val_mem hk) (hs'.val_mem hk) ?_
  rw [← comp_val hf.isFunction hs.isFunction (by grind),
    ← comp_val hf.isFunction hs'.isFunction (by grind), h]

/-- `s ↦ f !∘ s` on a set `D` of functions -/
noncomputable def compLeft (f D : M) : M := (fun s ↦ f !∘ s) ↾₀ D

/-- Composing with an injection `f !: b ↪ c` injects a set `D` of functions into `b` into any
set `E` containing their composites with `f` -/
theorem IsInjectionFromTo.compLeft {f b c D E : M} (hf : f !: b ↪ c)
    (hr : IsSetRestrictedTo (fun s ↦ f !∘ s) D) (hD : ∀ s ∈ D, s !: dom s → b)
    (hDE : ∀ s ∈ D, f !∘ s ∈ E) : MemStructure.compLeft f D !: D ↪ E := by
  refine isInjectionFromTo_toSetRestrictedTo hr hDE fun s hs s' hs' h ↦ ?_
  have hdom : dom s = dom s' := by
    rw [← ((hD s hs).comp hf.isFunctionFromTo).dom_eq, h,
      ((hD s' hs').comp hf.isFunctionFromTo).dom_eq]
  refine hf.comp_left_cancel (hD s hs) ?_ h
  rw [hdom]
  exact hD s' hs'

/-- Composing with a bijection `f !: b ↔ c` is a bijection `D ↔ E` between sets of functions
into `b` and into `c` that are closed under composing with `f` and `f⁻¹` respectively -/
theorem IsBijectionFromTo.compLeft {f b c D E : M} (hf : f !: b ↔ c)
    (hr : IsSetRestrictedTo (fun s ↦ f !∘ s) D) (hD : ∀ s ∈ D, s !: dom s → b)
    (hE : ∀ t ∈ E, t !: dom t → c) (hDE : ∀ s ∈ D, f !∘ s ∈ E)
    (hED : ∀ t ∈ E, f⁻¹ !∘ t ∈ D) : MemStructure.compLeft f D !: D ↔ E := by
  have hinj := hf.isInjectionFromTo.compLeft hr hD hDE
  refine ⟨hinj, (isSurjectionFromTo_iff_of_isFunctionFromTo hinj.isFunctionFromTo).mpr
    fun t ht ↦ ⟨_, hED t ht, ?_⟩⟩
  rw [MemStructure.compLeft, val_toSetRestrictedTo hr (hED t ht), ← comp_assoc, hf.comp_inv,
    (hE t ht).isFunction.id_comp (hE t ht).ran_subset]

end CompLeft

section Lambda

/-! ### `Δ₀` base cases for lambda notation -/

variable [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [RudClosed M]

/-- `IsFunction` is `Δ₀` -/
instance : Multiclass.DeltaZero (fun ys : Fin 1 → M ↦ IsFunction (ys 0)) Set.univ := by
  have h : (fun ys : Fin 1 → M ↦ IsFunction (ys 0)) =
      ((ᵣ0 : L.RudimentaryTerm 1).isFunction.toBoundedFormula.multiclass : Multiclass M 1) := by
    funext ys
    simp
  rw [h]
  infer_instance

/-- `IsFunctionFromTo` is `Δ₀` -/
instance : Multiclass.DeltaZero
    (fun ys : Fin 3 → M ↦ IsFunctionFromTo (ys 0) (ys 1) (ys 2)) Set.univ := by
  have h : (fun ys : Fin 3 → M ↦ IsFunctionFromTo (ys 0) (ys 1) (ys 2)) =
      ((ᵣ0 : L.RudimentaryTerm 3).isFunctionFromTo (ᵣ1) (ᵣ2)).toBoundedFormula.multiclass := by
    funext ys
    simp
  rw [h]
  infer_instance

/-- `IsInjectionFromTo` is `Δ₀` -/
instance : Multiclass.DeltaZero
    (fun ys : Fin 3 → M ↦ IsInjectionFromTo (ys 0) (ys 1) (ys 2)) Set.univ := by
  have h : (fun ys : Fin 3 → M ↦ IsInjectionFromTo (ys 0) (ys 1) (ys 2)) =
      ((ᵣ0 : L.RudimentaryTerm 3).isInjectionFromTo (ᵣ1) (ᵣ2)).toBoundedFormula.multiclass := by
    funext ys
    simp
  rw [h]
  infer_instance

/-- `IsSurjectionFromTo` is `Δ₀` -/
instance : Multiclass.DeltaZero
    (fun ys : Fin 3 → M ↦ IsSurjectionFromTo (ys 0) (ys 1) (ys 2)) Set.univ := by
  have h : (fun ys : Fin 3 → M ↦ IsSurjectionFromTo (ys 0) (ys 1) (ys 2)) =
      ((ᵣ0 : L.RudimentaryTerm 3).isSurjectionFromTo (ᵣ1) (ᵣ2)).toBoundedFormula.multiclass := by
    funext ys
    simp
  rw [h]
  infer_instance

/-- `IsBijectionFromTo` is `Δ₀` -/
instance : Multiclass.DeltaZero
    (fun ys : Fin 3 → M ↦ IsBijectionFromTo (ys 0) (ys 1) (ys 2)) Set.univ := by
  unfold IsBijectionFromTo
  infer_instance

end Lambda

end FirstOrder.Language.MemStructure
