import Astlib.Basic.SetOperation.Inter

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} [M.ClosedUnderDeltaZeroComprehension] (x y z : M)

variable (M) in
noncomputable instance : SDiff M where
  sdiff x y := {∈ x | ∼(&2 ∈' &0) 〘y〙₀}

@[simp, grind =]
theorem mem_sdiff : x ∈ y \ z ↔ x ∈ y ∧ x ∉ z := by
  simp [SDiff.sdiff]

@[simp, grind =, push]
theorem empty_sdiff [M.Extensional] [M.HasEmpty] :
    (∅ : M) \ x = ∅ := by
  ext; grind

@[simp, grind =, push]
theorem sdiff_empty [M.Extensional] [M.HasEmpty] :
    x \ (∅ : M) = x := by
  ext; grind

@[simp, grind =, push]
theorem sdiff_self [M.Extensional] [M.HasEmpty] :
    x \ x = ∅ := by
  ext; grind

@[grind! .]
theorem sdiff_subset_left [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    x \ y ⊆ x := by
  grind

@[simp, grind! ., push]
theorem sdiff_inter_right [M.Extensional] [M.HasEmpty] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    (x \ y) ∩ y = ∅ := by
  ext; grind

@[simp, grind! ., push]
theorem sdiff_union_right [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    (x \ y) ∪ (x ∩ y) = x := by
  ext; grind

variable [M.Extensional]

@[simp, grind =]
theorem sdiff_empty_of_subset [M.HasEmpty] {x y : M} (h : x ⊆ y) : x \ y = ∅ := by
  ext; grind

@[grind →]
theorem subset_of_sdiff_empty [M.HasEmpty] {x y : M} (h : x \ y = ∅) : x ⊆ y := by
  intro z hz
  contrapose! h
  rw [ne_empty_iff]
  exact ⟨z, by grind⟩

theorem sdiff_empty_iff_subset [M.HasEmpty] {x y : M} : x \ y = ∅ ↔ x ⊆ y := by
  grind

@[simp, grind =]
theorem sdiff_eq_left_of_inter_empty [M.HasEmpty] {x y : M} (h : x ∩ y = ∅) : x \ y = x := by
  ext; grind

@[simp, grind =]
theorem inter_empty_of_sdiff_eq_left [M.HasEmpty] {x y : M} (h : x \ y = x) : x ∩ y = ∅ := by
  ext; grind

@[simp, grind ., push]
theorem sdiff_eq_left_iff_inter_empty [M.HasEmpty] :
    x \ y = x ↔ x ∩ y = ∅ := by
  grind

variable [M.ClosedUnderSUnion] [M.ClosedUnderPair]

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

end FirstOrder.Language.MemStructure
