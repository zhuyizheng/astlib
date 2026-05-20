import Astlib.Basic.SetOperation.Extensional
import Astlib.Mathlib.Sum.Basic


namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x : M)

variable (M) in
/- `M` has an empty set `∅` -/
class HasEmpty extends EmptyCollection M where
  protected empty_prop : ∀ x : M, x ∉ (∅ : M)

@[simp, grind .]
theorem notin_empty [M.HasEmpty] : x ∉ (∅ : M) := HasEmpty.empty_prop x

theorem empty_iff [M.Extensional] [M.HasEmpty] : x = ∅ ↔ ∀ y, y ∉ x := by
  rw [eq_iff]; grind

theorem ne_empty_iff [M.Extensional] [M.HasEmpty] : x ≠ ∅ ↔ ∃ y, y ∈ x := by
  simp [empty_iff]

@[grind .]
theorem empty_subset [M.HasEmpty] : ∅ ⊆ x := by grind

theorem test (M : MemStructure) [M.Extensional] [M.HasEmpty] :
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

end MemStructure

variable {L : FirstOrder.Language} [HasMem L]

/-- `t = ∅` -/
abbrev Term.isEmpty (t : L.Term (α ⊕ Fin n)) : L.BoundedFormula α n :=
  ∀'∈ t ⊥

/-- There exists an empty set -/
def exEmptyset : L.Sentence := ∃' ((&0).isEmpty)

variable {M : MemStructure}

noncomputable instance (hM : M ⊨ M.L.exEmptyset) : M.HasEmpty where
  emptyCollection := Classical.choose (exists_of_ex hM)
  empty_prop := by simpa using Classical.choose_spec (exists_of_ex hM)

@[simp 1100]
theorem Term.isEmpty_iff [M.Extensional] [M.HasEmpty]
    (t : M.L.Term (α ⊕ Fin n))
    (v : α → M) (xs : Fin n → M) :
    t.isEmpty.Realize v xs ↔ t.realize (Sum.elim v xs) = (∅ : M) := by
  simp [M.empty_iff]

end FirstOrder.Language
