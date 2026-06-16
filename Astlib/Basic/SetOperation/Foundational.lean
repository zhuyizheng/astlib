import Astlib.Basic.SetOperation.Insert

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y : M)

abbrev IsMemMin (a x : M) := a ∈ x ∧ ∀ y ∈ a, y ∉ x

noncomputable instance : Decidable (∃ a, IsMemMin a x) :=
  Classical.propDecidable _

noncomputable def memMin (x : M) := dite (∃ a, IsMemMin a x) Classical.choose default

variable (M) in
/- `M` is closed under `⋃` -/
class Foundational : Prop where
  protected hasMemMin : ∀ (x : M), x ≠ ∅ → ∃ a, IsMemMin a x

@[simp]
theorem isMemMin_memMin [Foundational M] {x : M} (hx : x ≠ ∅) : IsMemMin (memMin x) x := by
  simp only [memMin, Foundational.hasMemMin x hx, ↓reduceDIte]
  grind

@[simp, grind .]
theorem memMin_mem [Foundational M] {x : M} (hx : x ≠ ∅) : memMin x ∈ x := by
  grind [isMemMin_memMin]

@[simp, grind .]
theorem notMem_memMin [M.HasEmpty] [Foundational M] {x y : M} (hy : y ∈ x) :
    y ∉ memMin x := by
  have : x ≠ ∅ := by grind
  grind [isMemMin_memMin]

@[simp]
theorem notMem_of_mem_memMin [M.HasEmpty] [Foundational M] {x y : M} (hy : y ∈ memMin x) :
    y ∉ x := by
  grind

@[simp, grind .]
theorem notMem_self [M.HasEmpty] [M.ClosedUnderPair] [Foundational M] : x ∉ x := by
  have := memMin_mem (x := ({x} : M)) (by simp)
  grind

@[simp, grind .]
theorem succ_neq [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair] [M.ClosedUnderSUnion]
    [Foundational M] :
    succ x ≠ x := by
  grind

end FirstOrder.Language.MemStructure
