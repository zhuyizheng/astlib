import Astlib.Basic.SetOperation.Pair

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y : M)

variable (M) in
noncomputable instance : Singleton M M where
  singleton x := unorderedPair x x

@[simp, grind =, push]
theorem mem_singleton_iff [M.ClosedUnderPair] : y ∈ ({x} : M) ↔ y = x := by
  convert mem_unorderedPair_iff x x y using 1
  tauto

theorem notMem_singleton_iff [M.ClosedUnderPair] : y ∉ ({x} : M) ↔ y ≠ x := by simp

theorem mem_singleton [M.ClosedUnderPair] : x ∈ ({x} : M) := by simp

@[simp, grind =, push]
theorem singleton_eq_singleton_iff [M.ClosedUnderPair] : ({x} : M) = {y} ↔ x = y := by
  grind [mem_singleton]

@[simp]
theorem singleton_ne_empty [M.HasEmpty] [M.ClosedUnderPair] : ({x} : M) ≠ ∅ := by
  grind [mem_singleton]

@[simp, grind =]
theorem singleton_subset_iff [M.ClosedUnderPair] : ({x} : M) ⊆ y ↔ x ∈ y := by
  simp [Subset, MemStructure.Subset]

@[gcongr]
theorem singleton_subset_singleton [M.ClosedUnderPair] : ({x} : M) ⊆ {y} ↔ x = y := by
  grind [mem_singleton]

@[simp, grind =, push]
theorem sUnion_singleton [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] : ⋃₀ {x} = x := by
  ext; grind

end FirstOrder.Language.MemStructure
