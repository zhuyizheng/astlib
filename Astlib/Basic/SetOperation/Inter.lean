/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
-- import Astlib.Basic.SetOperation.Comprehension
import Astlib.Basic.SetOperation.Union
import Astlib.Basic.SetOperation.Rudimentary.Semantics
/-!
file docstring
-/

open FirstOrder Language BoundedFormula RudimentaryTerm

namespace FirstOrder.Language

def RudimentaryTerm.inter₀ {L : FirstOrder.Language} [L.HasMem] : L.RudimentaryTerm 2 :=
  ᵣ0 \ (ᵣ0 \ ᵣ1)

instance {n} {L : FirstOrder.Language} [L.HasMem] :
  Inter (L.RudimentaryTerm n) := ⟨fun r₁ r₂ ↦ inter₀.substBoundRud ![r₁, r₂]⟩

@[simp]
theorem RudimentaryTerm.inter_def {L : FirstOrder.Language} [L.HasMem]
    (r₁ r₂ : L.RudimentaryTerm n) :
    r₁ ∩ r₂ = inter₀.substBoundRud ![r₁, r₂] := rfl

instance {L : Language} [L.HasMem] :
  (inter₀ : L.RudimentaryTerm 2).CharFree := by
  unfold inter₀; infer_instance

instance {L : Language} [L.HasMem] (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] :
  (r ∩ s).CharFree := by
  rw [inter_def]; infer_instance

namespace MemStructure

variable {L : Language.{u, v}} {M : Type max u v}
  [L.MemStructure M] [Inhabited M]
  (x y z : M)

-- variable (M) in
-- noncomputable instance : Inter M := ⟨fun x y ↦ inter x y⟩

-- variable [M.ClosedUnderDeltaZeroComprehension]

-- @[simp, grind =]
-- theorem mem_inter_iff : x ∈ y ∩ z ↔ x ∈ y ∧ x ∈ z := by
--   simp [Inter.inter]
noncomputable instance : Inter M := ⟨fun x y ↦ x \ (x \ y)⟩

@[grind =]
theorem inter_eq : x ∩ y = x \ (x \ y) := by
  simp [Inter.inter]

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_inter₀ (xs : Fin 2 → M) :
    inter₀〘xs〙 = xs 0 ∩ xs 1 := by
  simp [inter_eq, inter₀]

variable [SDiffClosed M] [PairClosed M]

@[simp, grind =]
theorem mem_inter_iff : x ∈ y ∩ z ↔ x ∈ y ∧ x ∈ z := by
  grind

@[grind =]
theorem inter_comm [Extensional M] : x ∩ y = y ∩ x := by
  ext; grind

variable (M) in
instance [Extensional M] :
  Std.Commutative (α := M) Inter.inter where
  comm := fun x y ↦ inter_comm x y

@[grind =]
theorem inter_assoc [Extensional M] :
    (x ∩ y) ∩ z = x ∩ (y ∩ z) := by
  ext; grind

variable (M) in
instance [Extensional M] :
  Std.Associative (α := M) Inter.inter where
  assoc := fun x y z ↦ inter_assoc x y z

@[simp, grind ., push]
theorem notin_of_inter_empty_mem_left (h : x ∩ y = ∅) (hz : z ∈ x) : z ∉ y := by
  by_contra!
  have : z ∈ x ∩ y := by grind
  grind

@[simp, grind ., push]
theorem notin_of_inter_empty_mem_right (h : x ∩ y = ∅) (hz : z ∈ y) : z ∉ x := by
  grind

@[simp, grind =, push]
theorem empty_inter [Extensional M] :
    (∅ : M) ∩ x = ∅ := by
  ext; grind

@[simp, grind =, push]
theorem inter_empty [Extensional M] :
    x ∩ (∅ : M) = ∅ := by
  grind

@[simp, grind =, push]
theorem inter_self [Extensional M] :
    x ∩ x = x := by
  ext; grind

@[grind! .]
theorem inter_subset_left :
    x ∩ y ⊆ x := by
  grind

@[grind! .]
theorem inter_subset_right :
    x ∩ y ⊆ y := by
  grind

variable [Extensional M]

@[simp, grind =]
theorem inter_of_subset_right
    {x y : M} (h : x ⊆ y) : x ∩ y = x := by
  ext z; simp only [mem_inter_iff, and_iff_left_iff_imp]
  exact fun hz ↦ h hz

@[simp, grind =]
theorem inter_of_subset_left
    {x y : M} (h : y ⊆ x) : x ∩ y = y := by
  ext z; simp only [mem_inter_iff, and_iff_right_iff_imp]
  exact fun hz ↦ h hz

@[simp, grind ., push]
theorem inter_eq_right_iff_subset :
    x ∩ y = y ↔ y ⊆ x := by
  grind

@[simp, grind ., push]
theorem inter_eq_left_iff_subset :
    x ∩ y = x ↔ x ⊆ y := by
  grind

omit [PairClosed M] [SDiffClosed M]
variable [RudClosed M]

theorem inter_union_distrib_left : x ∩ (y ∪ z) = x ∩ y ∪ x ∩ z := by
  ext; grind

theorem union_inter_distrib_right : (x ∪ y) ∩ z = x ∩ z ∪ y ∩ z := by
  ext; grind

theorem union_inter_distrib_left : x ∪ y ∩ z = (x ∪ y) ∩ (x ∪ z) := by
  ext; grind

theorem inter_union_distrib_right : x ∩ y ∪ z = (x ∪ z) ∩ (y ∪ z) := by
  ext; grind

end FirstOrder.Language.MemStructure
