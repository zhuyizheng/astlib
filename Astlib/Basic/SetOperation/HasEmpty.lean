import Astlib.Basic.SetOperation.Extensional


namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x : M)

variable (M) in
/- `M` has an empty set `∅` -/
class HasEmpty extends EmptyCollection M where
  empty_prop : ∀ x : M, x ∉ (∅ : M)

noncomputable instance (hM : M ⊨ M.L.exEmptyset) : HasEmpty M where
  emptyCollection := Classical.choose (exists_of_ex hM)
  empty_prop := by simpa [Term.isEmpty] using Classical.choose_spec (exists_of_ex hM)

@[grind .]
theorem notin_empty [HasEmpty M] : x ∉ (∅ : M) := HasEmpty.empty_prop x

theorem empty_iff [Extensional M] [HasEmpty M] : x = ∅ ↔ ∀ y, y ∉ x :=
  ⟨by grind, fun _ ↦ by ext; grind⟩

theorem ne_empty_iff [Extensional M] [HasEmpty M] : x ≠ ∅ ↔ ∃ y, y ∈ x := by
  simp [empty_iff]

@[grind .]
theorem empty_subset [HasEmpty M] : ∅ ⊆ x := by grind

theorem test (M : MemStructure) [Extensional M] [HasEmpty M] :
    ∃! x : M, (∀ z : M, z ∉ x) := by
  use ∅
  constructor
  · grind
  · intro y hy
    ext
    -- ext
    -- apply extensional y empty
    -- intro z
    -- have : ∀ z : M, z ∉ empty := by grind
    grind

end FirstOrder.Language.MemStructure
