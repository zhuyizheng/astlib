/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Pair.Basic
/-!
file docstring
-/

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language

namespace MemStructure

variable {M : MemStructure} (x y : M)

variable (M) in
noncomputable instance : Singleton M M := ⟨fun x ↦ {ᵣ0}〘x〙₁⟩

@[grind =]
theorem singleton_eq : {x} = unorderedPair x x := by
  simp only [Singleton.singleton, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  rfl

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_singleton
    (r : M.L.RudimentaryTerm n) (xs : Fin n → M) :
    {r}〘xs〙 = {r〘xs〙} := by
  simp [singleton]

variable [M.RudClosed]

@[simp, grind =, push]
theorem mem_singleton_iff : y ∈ ({x} : M) ↔ y = x := by
  convert mem_unorderedPair_iff y x x using 1
  · rfl
  · tauto

theorem notMem_singleton_iff : y ∉ ({x} : M) ↔ y ≠ x := by simp

theorem mem_singleton : x ∈ ({x} : M) := by simp

@[simp, grind =, push]
theorem singleton_eq_singleton_iff : ({x} : M) = {y} ↔ x = y := by
  grind [mem_singleton]

theorem eq_singleton_iff [M.Extensional] : y = ({x} : M) ↔ (∀ z, z ∈ y ↔ z = x) := by
  simp [MemStructure.ext_iff]

@[simp]
theorem singleton_ne_empty : ({x} : M) ≠ ∅ := by
  grind [mem_singleton]

@[simp, grind =]
theorem singleton_subset_iff : ({x} : M) ⊆ y ↔ x ∈ y := by
  simp [Subset, MemStructure.Subset]

@[gcongr]
theorem singleton_subset_singleton : ({x} : M) ⊆ {y} ↔ x = y := by
  grind [mem_singleton]

@[grind =]
theorem subset_singleton_iff [M.Extensional] : x ⊆ {y} ↔ x = ∅ ∨ x = {y} := by
  refine ⟨fun hx ↦ ?_, by grind⟩
  by_cases hx₁ : x = ∅
  · exact Or.inl hx₁
  right
  ext z
  exact ⟨fun hz ↦ hx hz, by grind [ne_empty_iff]⟩

@[simp, grind =, push]
theorem sUnion_singleton [M.Extensional] :
    ⋃₀ {x} = x := by
  ext; grind

end FirstOrder.Language.MemStructure
