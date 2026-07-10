/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Extensional
import Astlib.Mathlib.Sum.Basic
import Astlib.ModelTheory.Semantics
/-!
file docstring
-/

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x : M)

def IsEmpty (a : M) := ∀ (x : M), x ∉ a

noncomputable instance : Decidable (∃ a : M, IsEmpty a) :=
  Classical.propDecidable _

noncomputable instance : EmptyCollection M :=
  ⟨dite (∃ a : M, IsEmpty a) Classical.choose default⟩

variable (M) in
/- `M` has an empty set `∅` -/
class HasEmpty : Prop where
  protected hasEmpty : ∃ a : M, IsEmpty a

@[simp, grind .]
theorem notin_empty [hM : M.HasEmpty] : x ∉ (∅ : M) := by
  convert Classical.choose_spec hM.hasEmpty x
  simp [EmptyCollection.emptyCollection, HasEmpty.hasEmpty]

theorem empty_iff [M.Extensional] [M.HasEmpty] : x = ∅ ↔ ∀ y, y ∉ x := by
  rw [eq_iff]; grind

theorem ne_empty_iff [M.Extensional] [M.HasEmpty] : x ≠ ∅ ↔ ∃ y, y ∈ x := by
  simp [empty_iff]

@[grind .]
theorem empty_subset [M.HasEmpty] : ∅ ⊆ x := by grind

end MemStructure

section Syntax

variable {L : FirstOrder.Language} [HasMem L] {α : Type*} {n : ℕ}

/-- `t = ∅` -/
def Term.isEmpty (t : L.Term (α ⊕ Fin n)) : L.BoundedFormula α n :=
  ∀'∈ t ⊥

theorem Term.isDeltaZero_isEmpty (t : L.Term (α ⊕ Fin n)) : (t.isEmpty).IsDeltaZero := by
  rw [isEmpty]
  exact BoundedFormula.DeltaZero.isDeltaZero

instance (t : L.Term (α ⊕ Fin n)) : (t.isEmpty).DeltaZero := ⟨Term.isDeltaZero_isEmpty _⟩

-- /-- There exists an empty set -/
-- def exEmptyset : L.Sentence := ∃' ((&0).isEmpty)

variable {M : MemStructure}

-- theorem Sentence.Realize.exists_empty_of_exEmptyset (hM : M ⊨ M.L.exEmptyset) :
--     ∃ a : M, ∀ x, x ∉ a := by
--   use Classical.choose (exists_of_ex hM)
--   simpa using Classical.choose_spec (exists_of_ex hM)

-- noncomputable instance (hM : M ⊨ M.L.exEmptyset) : M.HasEmpty :=
--   MemStructure.instHasEmpty hM.exists_empty_of_exEmptyset

@[simp]
theorem Term.isEmpty_iff [M.Extensional] [M.HasEmpty]
    (t : M.L.Term (α ⊕ Fin n))
    (v : α → M) (xs : Fin n → M) :
    t.isEmpty〘v, xs〙 ↔ t〘v, xs〙 = (∅ : M) := by
  simp [M.empty_iff, isEmpty]

end Syntax

end FirstOrder.Language
