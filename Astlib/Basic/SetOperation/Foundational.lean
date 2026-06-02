import Astlib.Basic.SetOperation.Insert

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y : M)

noncomputable instance : Decidable (∃ a ∈ x, ∀ y ∈ a, y ∉ x) :=
  Classical.propDecidable _

noncomputable def memMin (x : M) := dite (∃ a ∈ x, ∀ y ∈ a, y ∉ x) Classical.choose default

variable (M) in
/- `M` is closed under `⋃` -/
class Foundational : Prop where
  protected memMin_prop : ∀ (x : M), x ≠ ∅ → memMin x ∈ x ∧ ∀ y ∈ memMin x, y ∉ x

noncomputable instance instFoundational
    (h : ∀ x : M, x ≠ ∅ → ∃ a ∈ x, ∀ y ∈ a, y ∉ x) : M.Foundational :=
  ⟨fun x hx ↦ by
    specialize h x hx
    suffices memMin x = Classical.choose h by convert Classical.choose_spec h
    simp only [memMin]; split_ifs; simp⟩

@[simp, grind .]
theorem memMin_mem [Foundational M] {x : M} (hx : x ≠ ∅) : memMin x ∈ x :=
  Foundational.memMin_prop x hx |>.left

@[simp, grind →, grind .]
theorem notMem_memMin [M.HasEmpty] [Foundational M] {x y : M} (hy : y ∈ x) :
    y ∉ memMin x := by
  have : x ≠ ∅ := by grind
  grind [Foundational.memMin_prop]

@[simp, grind →]
theorem notMem_of_mem_memMin [M.HasEmpty] [Foundational M] {x y : M} (hy : y ∈ memMin x) :
    y ∉ x := by
  grind

@[simp, grind .]
theorem notMem_self [M.HasEmpty] [M.ClosedUnderPair] [Foundational M] : x ∉ x := by
  have := memMin_mem (x := ({x} : M)) (by simp)
  grind

@[simp, grind .]
theorem insert_neq [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair] [M.ClosedUnderSUnion]
    [Foundational M] :
    succ x ≠ x := by
  grind

end FirstOrder.Language.MemStructure
