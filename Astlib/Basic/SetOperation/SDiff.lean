/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Inter
/-!
file docstring
-/

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} [M.RudClosed] (x y z : M)

@[simp, grind =, push]
theorem empty_sdiff [M.Extensional] :
    (∅ : M) \ x = ∅ := by
  ext; grind

@[simp, grind =, push]
theorem sdiff_empty [M.Extensional] :
    x \ (∅ : M) = x := by
  ext; grind

@[simp, grind =, push]
theorem sdiff_self [M.Extensional] :
    x \ x = ∅ := by
  ext; grind

@[grind! .]
theorem sdiff_subset_left :
    x \ y ⊆ x := by
  grind

@[simp, grind! ., push]
theorem sdiff_inter_right [M.Extensional] :
    (x \ y) ∩ y = ∅ := by
  ext; grind

@[simp, grind! ., push]
theorem sdiff_union_right [M.Extensional] :
    (x \ y) ∪ (x ∩ y) = x := by
  ext; grind

variable [M.Extensional]

@[simp, grind =]
theorem sdiff_empty_of_subset {x y : M} (h : x ⊆ y) : x \ y = ∅ := by
  ext; grind

@[grind →]
theorem subset_of_sdiff_empty {x y : M} (h : x \ y = ∅) : x ⊆ y := by
  intro z hz
  contrapose! h
  rw [ne_empty_iff]
  exact ⟨z, by grind⟩

@[simp]
theorem sdiff_empty_iff_subset {x y : M} : x \ y = ∅ ↔ x ⊆ y := by
  grind

@[simp, grind =]
theorem sdiff_eq_left_of_inter_empty {x y : M} (h : x ∩ y = ∅) : x \ y = x := by
  ext; grind

@[simp, grind =]
theorem inter_empty_of_sdiff_eq_left {x y : M} (h : x \ y = x) : x ∩ y = ∅ := by
  ext; grind

@[simp, grind ., push]
theorem sdiff_eq_left_iff_inter_empty :
    x \ y = x ↔ x ∩ y = ∅ := by
  grind

-- variable [M.ClosedUnderPair]

theorem sdiff_union_sdiff_inter_sdiff : x \ (y ∪ z) = (x \ y) ∩ (x \ z) := by
  ext; grind

theorem sdiff_union_sdiff_sdiff : x \ (y ∪ z) = (x \ y) \ z := by
  ext; grind

theorem union_sdiff_distrib : (x ∪ y) \ z = x \ z ∪ y \ z := by
  ext; grind

theorem sdiff_inter_sdiff_union_sdiff : x \ (y ∩ z) = (x \ y) ∪ (x \ z) := by
  ext; grind

theorem inter_sdiff_distrib : (x ∩ y) \ z = (x \ z) ∩ (y \ z) := by
  ext; grind

@[simp, grind =]
theorem sdiff_union_sdiff_empty_iff {x y : M} : (x \ y) ∪ (y \ x) = ∅ ↔ x = y := by
  refine ⟨?_, by grind⟩
  simp only [union_empty_iff, sdiff_empty_iff_subset, and_imp]
  grind

end FirstOrder.Language.MemStructure
