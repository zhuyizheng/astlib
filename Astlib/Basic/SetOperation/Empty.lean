import Astlib.Basic.SetOperation.Extensional
import Astlib.Mathlib.Sum.Basic
import Astlib.ModelTheory.Semantics

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x : M)

noncomputable instance : Decidable (∃ a : M, ∀ (x : M), x ∉ a) :=
  Classical.propDecidable _

noncomputable instance : EmptyCollection M :=
  ⟨dite (∃ a : M, ∀ x, x ∉ a) Classical.choose default⟩

variable (M) in
/- `M` has an empty set `∅` -/
class HasEmpty : Prop where
  protected empty_prop : ∀ x : M, x ∉ (∅ : M)

noncomputable instance instHasEmpty (h : ∃ a : M, ∀ x, x ∉ a) : M.HasEmpty :=
  ⟨by convert Classical.choose_spec h; simp [EmptyCollection.emptyCollection, h]⟩

@[simp, grind .]
theorem notin_empty [M.HasEmpty] : x ∉ (∅ : M) := HasEmpty.empty_prop x

theorem empty_iff [M.Extensional] [M.HasEmpty] : x = ∅ ↔ ∀ y, y ∉ x := by
  rw [eq_iff]; grind

theorem ne_empty_iff [M.Extensional] [M.HasEmpty] : x ≠ ∅ ↔ ∃ y, y ∈ x := by
  simp [empty_iff]

@[grind .]
theorem empty_subset [M.HasEmpty] : ∅ ⊆ x := by grind

end MemStructure

variable {L : FirstOrder.Language} [HasMem L]

/-- `t = ∅` -/
abbrev Term.isEmpty (t : L.Term (α ⊕ Fin n)) : L.BoundedFormula α n :=
  ∀'∈ t ⊥

instance (t : L.Term (α ⊕ Fin n)) : (t.isEmpty).DeltaZero := by infer_instance

-- /-- There exists an empty set -/
-- def exEmptyset : L.Sentence := ∃' ((&0).isEmpty)

variable {M : MemStructure}

-- theorem Sentence.Realize.exists_empty_of_exEmptyset (hM : M ⊨ M.L.exEmptyset) :
--     ∃ a : M, ∀ x, x ∉ a := by
--   use Classical.choose (exists_of_ex hM)
--   simpa using Classical.choose_spec (exists_of_ex hM)

-- noncomputable instance (hM : M ⊨ M.L.exEmptyset) : M.HasEmpty :=
--   MemStructure.instHasEmpty hM.exists_empty_of_exEmptyset

@[simp 1100]
theorem Term.isEmpty_iff [M.Extensional] [M.HasEmpty]
    (t : M.L.Term (α ⊕ Fin n))
    (v : α → M) (xs : Fin n → M) :
    t.isEmpty.Realize v xs ↔ t.realize' v xs = (∅ : M) := by
  simp [M.empty_iff, Fin.castLE_succ_castSucc]

end FirstOrder.Language
