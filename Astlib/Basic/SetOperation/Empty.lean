/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Extensional
import Astlib.Mathlib.Sum.Basic
import Astlib.Basic.SetOperation.Rudimentary.Semantics
/-!
file docstring
-/

namespace FirstOrder.Language
namespace MemStructure

variable {M : MemStructure} [M.RudClosed] (x : M)



@[simp, grind .]
theorem notin_empty : x ∉ (∅ : M) := by
  simp [EmptyCollection.emptyCollection]

theorem empty_iff [M.Extensional] : x = ∅ ↔ ∀ y, y ∉ x := by
  rw [eq_iff]; grind

theorem ne_empty_iff [M.Extensional] : x ≠ ∅ ↔ ∃ y, y ∈ x := by
  simp [empty_iff]

@[grind .]
theorem empty_subset : ∅ ⊆ x := by grind

end MemStructure


namespace RudimentaryTerm

variable {L : FirstOrder.Language} [L.HasMem]

instance [NeZero n] : Inhabited (L.RudimentaryTerm n) := ⟨ᵣ0⟩

instance [NeZero n] : EmptyCollection (L.RudimentaryTerm n) :=
  ⟨ᵣ0 \ ᵣ0⟩

@[simp]
theorem castLHom_empty {M : MemStructure} [NeZero n] :
    (∅ : M.L'.RudimentaryTerm n).castLHom = (∅ : M.L.RudimentaryTerm n) := by
  simp [EmptyCollection.emptyCollection]

variable {M : MemStructure} {n : ℕ} (xs : Fin n → M)

@[simp, grind =]
theorem realize_empty [NeZero n] [M.Extensional] [M.RudClosed] :
    (∅ : M.L.RudimentaryTerm n)〘xs〙 = ∅ := by
  ext
  simp [EmptyCollection.emptyCollection]

end RudimentaryTerm
-- section Syntax

-- variable {L : FirstOrder.Language} [L.HasMem] {α : Type*} {n : ℕ}

-- /-- `t = ∅` -/
-- def Term.isEmpty (t : L.Term (α ⊕ Fin n)) : L.BoundedFormula α n :=
--   ∀'∈ t ⊥

-- theorem Term.isDeltaZero_isEmpty (t : L.Term (α ⊕ Fin n)) : (t.isEmpty).IsDeltaZero := by
--   rw [isEmpty]
--   exact BoundedFormula.DeltaZero.isDeltaZero

-- instance (t : L.Term (α ⊕ Fin n)) : (t.isEmpty).DeltaZero := ⟨Term.isDeltaZero_isEmpty _⟩

-- /-- There exists an empty set -/
-- def exEmptyset : L.Sentence := ∃' ((&0).isEmpty)

-- variable {M : MemStructure}

-- -- theorem Sentence.Realize.exists_empty_of_exEmptyset (hM : M ⊨ M.L.exEmptyset) :
-- --     ∃ a : M, ∀ x, x ∉ a := by
-- --   use Classical.choose (exists_of_ex hM)
-- --   simpa using Classical.choose_spec (exists_of_ex hM)

-- -- noncomputable instance (hM : M ⊨ M.L.exEmptyset) : M.HasEmpty :=
-- --   MemStructure.instHasEmpty hM.exists_empty_of_exEmptyset

-- @[simp]
-- theorem Term.isEmpty_iff [M.Extensional] [M.HasEmpty]
--     (t : M.L.Term (α ⊕ Fin n))
--     (v : α → M) (xs : Fin n → M) :
--     t.isEmpty〘v, xs〙 ↔ t〘v, xs〙 = (∅ : M) := by
--   simp [M.empty_iff, isEmpty]

-- end Syntax

end FirstOrder.Language
