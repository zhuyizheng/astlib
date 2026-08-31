/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
-- import Astlib.Basic.SetOperation.Comprehension
import Astlib.Basic.SetOperation.Union
/-!
file docstring
-/

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language

instance {n} {L : FirstOrder.Language} [L.HasMem] :
  Inter (L.RudimentaryTerm n) := ⟨fun r₁ r₂ ↦ r₁ \ (r₁ \ r₂)⟩

@[simp]
theorem RudimentaryTerm.castLHom_inter {M : MemStructure} (r₁ r₂ : M.L'.RudimentaryTerm n) :
    (r₁ ∩ r₂).castLHom = r₁.castLHom ∩ r₂.castLHom := by
  simp [Inter.inter]

namespace MemStructure

variable {M : MemStructure} (x y z : M)

-- variable (M) in
-- noncomputable instance : Inter M := ⟨fun x y ↦ inter x y⟩

-- variable [M.ClosedUnderDeltaZeroComprehension]

-- @[simp, grind =]
-- theorem mem_inter_iff : x ∈ y ∩ z ↔ x ∈ y ∧ x ∈ z := by
--   simp [Inter.inter]
noncomputable instance : Inter M := ⟨fun x y ↦ (ᵣ0 ∩ ᵣ1)〘x, y〙₂⟩

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_inter (xs : Fin n → M) : (r₁ ∩ r₂)〘xs〙 = r₁〘xs〙 ∩ r₂〘xs〙 := by
  simp [Inter.inter]

@[grind =]
theorem inter_eq : x ∩ y = x \ (x \ y) := by
  simp only [Inter.inter, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  rfl

variable [M.RudClosed]

@[simp, grind =]
theorem mem_inter_iff : x ∈ y ∩ z ↔ x ∈ y ∧ x ∈ z := by
  grind

@[grind =]
theorem inter_comm [M.Extensional] : x ∩ y = y ∩ x := by
  ext; grind

variable (M) in
instance [M.Extensional] :
  Std.Commutative (α := M) Inter.inter where
  comm := fun x y ↦ inter_comm x y

@[grind =]
theorem inter_assoc [M.Extensional] :
    (x ∩ y) ∩ z = x ∩ (y ∩ z) := by
  ext; grind

variable (M) in
instance [M.Extensional] :
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
theorem empty_inter [M.Extensional] :
    (∅ : M) ∩ x = ∅ := by
  ext; grind

@[simp, grind =, push]
theorem inter_empty [M.Extensional] :
    x ∩ (∅ : M) = ∅ := by
  grind

@[simp, grind =, push]
theorem inter_self [M.Extensional] :
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

variable [M.Extensional]

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

-- variable [M.ClosedUnderSUnion] [M.ClosedUnderPair]

theorem inter_union_distrib_left : x ∩ (y ∪ z) = x ∩ y ∪ x ∩ z := by
  ext; grind

theorem union_inter_distrib_right : (x ∪ y) ∩ z = x ∩ z ∪ y ∩ z := by
  ext; grind

theorem union_inter_distrib_left : x ∪ y ∩ z = (x ∪ y) ∩ (x ∪ z) := by
  ext; grind

theorem inter_union_distrib_right : x ∩ y ∪ z = (x ∪ z) ∩ (y ∪ z) := by
  ext; grind

end FirstOrder.Language.MemStructure
