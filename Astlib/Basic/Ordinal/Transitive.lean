/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Function
import Astlib.Basic.SetOperation.Foundational
/-!
file docstring
-/

namespace FirstOrder.Language

open FirstOrder Language BoundedFormula Fin DeltaZeroBoundedFormula RudimentaryTerm

namespace RudimentaryTerm

variable {L : Language.{u, v}} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]

variable {n : ℕ}

noncomputable def isTransitive (t : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  ∀₀∈ &0 (&1 ⊆₀ &0) |>.substBoundRud ![t]

@[simp]
theorem isRelFree_isTransitive {t : L.RudimentaryTerm n} (ht : t.IsCharFree) :
    (t.isTransitive).IsRelFree := by
  simp only [isTransitive, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply]
  apply isRelFree_substBoundRud <;> simp [ht]

end RudimentaryTerm

namespace MemStructure

variable {L : Language.{u, v}} {M : Type max u v}
  [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly]
  [Inhabited M] [Extensional M] [RudClosed M] (x y : M)

open FirstOrder Language BoundedFormula Fin DeltaZeroBoundedFormula RudimentaryTerm Term

variable {n : ℕ}

@[grind]
def Transitive : Class M := fun a ↦ ∀ x ∈ a, x ⊆ a

@[simp]
theorem realize_isTransisitive (t : L.RudimentaryTerm n) (ht : t.IsCharFree) (xs : Fin n → M) :
    t.isTransitive.toBoundedFormula 〘xs〙 ↔ Transitive (t〘xs〙 : M) := by
  simp [isTransitive, Transitive, ht, snoc]

@[simp, grind .]
theorem isTransitive_empty : Transitive (∅ : M) := by
  simp [Transitive]

theorem transitive_succ {a : M} (ha : Transitive a) : Transitive (succ a) := by
  simp only [Transitive, subset_iff, mem_succ_iff, forall_eq_or_imp] at ha ⊢
  tauto

@[simp, grind =]
theorem transitive_succ_iff [Foundational M] (a : M) :
    Transitive (succ a) ↔ Transitive a := by
  refine ⟨?_, transitive_succ⟩
  intro h x hx y hy
  specialize h x (by simp [succ, hx]) hy
  grind [notMem_of_mem]

theorem transitive_inter
    {a b : M} (ha : Transitive a) (hb : Transitive b) : Transitive (a ∩ b) := by
  simp only [Transitive, subset_iff, mem_inter_iff, and_imp] at ha hb ⊢
  tauto

theorem transitive_union
    {a b : M} (ha : Transitive a) (hb : Transitive b) : Transitive (a ∪ b) := by
  simp only [Transitive, subset_iff, mem_union_iff] at ha hb ⊢
  tauto

theorem transitive_sUnion
    {a : M} (ha : ∀ x ∈ a, Transitive x) : Transitive (⋃₀ a) := by
  simp only [Transitive, subset_iff, mem_sUnion_iff] at ha ⊢
  tauto

theorem exists_min_class_of_mem_transitive [Foundational M]
    {A : Class M} {x y : M} (hAx : A x) (hxy : x ∈ y) (hy : Transitive y)
    [HasComprehension y A] :
    ∃ x, (A x ∧ ∀ y ∈ x, ¬A y) := by
  have hyA₀ : y ∩₀ A ≠ ∅ := by
    simp only [exists_prop, ne_eq, comprehension_eq_empty_iff, not_forall, not_not]
    use x
  use memMin (y ∩₀ A)
  have hyA₁ := memMin_mem hyA₀
  simp only [mem_comprehension_iff] at hyA₁
  refine ⟨hyA₁.right, fun z hz ↦ ?_⟩
  have := notMem_of_mem_memMin hz
  simp only [mem_comprehension_iff, not_and] at this
  grind

end FirstOrder.Language.MemStructure
