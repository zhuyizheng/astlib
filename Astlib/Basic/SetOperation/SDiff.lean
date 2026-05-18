import Astlib.Basic.SetOperation.Inter

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} [ClosedUnderDeltaZeroComprehension M] (x y z : M)

variable (M) in
noncomputable instance : SDiff M where
  sdiff x y := {∈ x | ∼(&2 ∈' &0) 〘y〙}

@[simp, grind =]
theorem mem_sdiff : x ∈ y \ z ↔ x ∈ y ∧ x ∉ z := by
  simp [SDiff.sdiff]

@[simp, grind =, push]
theorem empty_sdiff [Extensional M] [HasEmpty M] :
    (∅ : M) \ x = ∅ := by
  ext; grind

@[simp, grind =, push]
theorem sdiff_empty [Extensional M] [HasEmpty M] :
    x \ (∅ : M) = x := by
  ext; grind

@[simp, grind =, push]
theorem sdiff_self [Extensional M] [HasEmpty M] :
    x \ x = ∅ := by
  ext; grind

@[grind! .]
theorem sdiff_subset_left [ClosedUnderSUnion M] [ClosedUnderPair M] :
    x \ y ⊆ x := by
  grind

@[simp, grind! ., push]
theorem sdiff_inter_right [Extensional M] [HasEmpty M] [ClosedUnderSUnion M] [ClosedUnderPair M] :
    (x \ y) ∩ y = ∅ := by
  ext; grind

@[simp, grind! ., push]
theorem sdiff_union_right [Extensional M] [ClosedUnderSUnion M] [ClosedUnderPair M] :
    (x \ y) ∪ (x ∩ y) = x := by
  ext; grind

variable [Extensional M]

@[simp, grind =]
theorem sdiff_of_subset_right [HasEmpty M]
    {x y : M} (h : x ⊆ y) : x \ y = ∅ := by
  ext; grind

@[simp, grind =]
theorem sdiff_of_inter_empty [HasEmpty M]
    {x y : M} (h : x ∩ y = ∅) : x \ y = x := by
  ext; grind

-- @[simp, grind ., push]
-- theorem inter_eq_right_iff_subset :
--     x ∩ y = y ↔ y ⊆ x := by
--   grind

-- @[simp, grind ., push]
-- theorem inter_eq_left_iff_subset :
--     x ∩ y = x ↔ x ⊆ y := by
--   grind

-- variable [ClosedUnderSUnion M] [ClosedUnderPair M]

-- theorem inter_union_distrib_left : x ∩ (y ∪ z) = x ∩ y ∪ x ∩ z := by
--   ext; grind

-- theorem union_inter_distrib_right : (x ∪ y) ∩ z = x ∩ z ∪ y ∩ z := by
--   ext; grind

-- theorem union_inter_distrib_left : x ∪ y ∩ z = (x ∪ y) ∩ (x ∪ z) := by
--   ext; grind

-- theorem inter_union_distrib_right : x ∩ y ∪ z = (x ∪ z) ∩ (y ∪ z) := by
--   ext; grind

end FirstOrder.Language.MemStructure
