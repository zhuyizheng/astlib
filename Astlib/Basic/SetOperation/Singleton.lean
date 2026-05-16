import Astlib.Basic.SetOperation.Pair

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y : M)

variable (M) in
instance [HasUnorderedPair M] : Singleton M M where
  singleton x := unorderedPair x x

@[simp, grind =, push]
theorem mem_singleton_iff [HasUnorderedPair M] : y ∈ ({x} : M) ↔ y = x := by
  convert mem_unorderedPair_iff x x y using 1
  tauto

theorem notMem_singleton_iff [HasUnorderedPair M] : y ∉ ({x} : M) ↔ y ≠ x := by simp

theorem mem_singleton [HasUnorderedPair M] : x ∈ ({x} : M) := by simp

@[simp, grind =, push]
theorem singleton_eq_singleton_iff [HasUnorderedPair M] : ({x} : M) = {y} ↔ x = y := by
  grind [mem_singleton]

@[simp]
theorem singleton_ne_empty [HasEmpty M] [HasUnorderedPair M] : ({x} : M) ≠ ∅ := by
  grind [mem_singleton]

@[simp, grind =]
theorem singleton_subset_iff [HasUnorderedPair M] : ({x} : M) ⊆ y ↔ x ∈ y := by
  simp [Subset, MemStructure.Subset]

@[gcongr]
theorem singleton_subset_singleton [HasUnorderedPair M] : ({x} : M) ⊆ {y} ↔ x = y := by
  grind [mem_singleton]

@[simp, grind =, push]
theorem sUnion_singleton [Extensional M] [HasSUnion M] [HasUnorderedPair M] : ⋃₀ {x} = x := by
  ext; grind

end FirstOrder.Language.MemStructure
