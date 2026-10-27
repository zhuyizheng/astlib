/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Rudimentary.DeltaZero
import Astlib.Basic.SetOperation.Pair.Basic
/-!
file docstring
-/

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language

namespace MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M]
  (x y : M)

variable (M) in
noncomputable instance : Singleton M M := ⟨fun x ↦ RudimentaryTerm.singleton₀〘x〙₁⟩

instance [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [RudClosed M] :
    ClassFunction.DeltaZero (fun x ↦ ({x} : M)) Set.univ :=
  ClassFunction.deltaZero_of_eq RudimentaryTerm.singleton₀ fun _ ↦ rfl

@[grind =]
theorem singleton_eq : {x} = unorderedPair x x := by
  simp [Singleton.singleton, RudimentaryTerm.singleton₀]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_singleton₀ (xs : Fin 1 → M) :
    RudimentaryTerm.singleton₀〘xs〙 = {xs 0} := by
  simp [singleton_eq, RudimentaryTerm.singleton₀]

variable [PairClosed M] [SDiffClosed M]

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

-- theorem eq_singleton_iff [Extensional M] : y = ({x} : M) ↔ (∀ z, z ∈ y ↔ z = x) := by
--   simp [MemStructure.ext_iff]

-- @[simp]
theorem all_mem_iff_eq_iff_singleton [Extensional M] (u w : M) :
    (∀ (v : M), v ∈ u ↔ v = w) ↔ u = {w} := by
  simp [eq_iff]

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
theorem subset_singleton_iff [Extensional M] : x ⊆ {y} ↔ x = ∅ ∨ x = {y} := by
  refine ⟨fun hx ↦ ?_, by grind⟩
  by_cases hx₁ : x = ∅
  · tauto
  right
  ext z
  exact ⟨fun hz ↦ hx hz, by grind [ne_empty_iff]⟩

omit [PairClosed M] [SDiffClosed M]

variable [RudClosed M]

@[simp, grind =, push]
theorem sUnion_singleton [Extensional M] :
    ⋃₀ {x} = x := by
  ext; grind


end FirstOrder.Language.MemStructure
