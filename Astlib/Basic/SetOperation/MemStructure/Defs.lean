/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/

import Astlib.Basic.SetOperation.MemStructure.Syntax
import Astlib.Mathlib.ModelTheory.Semantics
import Astlib.Mathlib.Fin.Basic
import Astlib.Mathlib.ModelTheory.LanguageMap

/-!
file docstring
-/

open FirstOrder Language BoundedFormula Fin

variable (L : Language) {M : Type*}

namespace FirstOrder.Language

/-- `MemStructure L M` means that `L` has the symbol `∈` and `M` is an `L`-structure -/
class MemStructure (L : outParam Language) (M : Type*) extends
  L.Structure M, L.HasMem
namespace MemStructure

end MemStructure

namespace MemStructure

variable {L}
variable [L.MemStructure M]

instance : Membership M M := ⟨fun x y ↦ Structure.RelMap (memSymb (L := L)) ![y, x]⟩

@[simp]
theorem realize'_mem {n : ℕ} (t₁ t₂ : L.Term' n) (xs : Fin n → M) :
    (t₁ ∈' t₂)〘xs〙 ↔ t₁〘xs〙 ∈ t₂〘xs〙 := by
  simp [mem_boundedFormula, Membership.mem]

@[simp]
theorem realize_mem {n : ℕ} (t₁ t₂ : L.Term' n)
    (v : Empty → M) (xs : Fin n → M) :
    BoundedFormula.Realize (t₁ ∈' t₂) v xs ↔ t₁〘xs〙 ∈ t₂〘xs〙 := by
  convert realize'_mem t₁ t₂ xs
  rw [Realize', Unique.uniq _ v]

end MemStructure

end FirstOrder.Language




section ExUnique

variable {L} [L.MemStructure M]

variable {α : Type*} {n : ℕ} {φ : L.BoundedFormula' n}

-- theorem exists_of_ex {φ : L.BoundedFormula' (n + 1)} {v : α → M}
--     {xs : Fin n → M} (h : (∃' φ)〘v, xs〙) :
--     ∃ a, φ〘v, snoc xs a〙 := by
--   simpa using h

theorem existsUnique_of_exUnique {φ : L.BoundedFormula' (n + 1)}
    {xs : Fin n → M} (h : (∃!' φ)〘xs〙) :
    ∃! a, φ〘snoc xs a〙 := by
  simp only [BoundedFormula.exUnique, Function.comp_apply, realize'_ex, realize'_inf, realize'_all,
    realize'_imp, realize'_substBoundBound, snoc_snoc_comp_snoc_castAdd_two_last, realize'_bdEqual,
    Term.realize'_var', snoc_last, snoc_snoc_castAdd_one_last] at h
  exact h

theorem existsUnique_of_exUnique_sentence {φ : L.BoundedFormula Empty 1}
    {xs : Fin 0 → M} (h : (∃!' φ)〘xs〙) :
    ∃! a : M, φ〘![a]〙 := by
  convert existsUnique_of_exUnique h
  ext i
  simp [snoc]

end ExUnique
