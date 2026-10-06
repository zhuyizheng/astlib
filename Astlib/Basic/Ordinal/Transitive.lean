/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Function
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

def Transitive : Class M := fun a ↦  ∀ x ∈ a, x ⊆ a

@[simp]
theorem realize_isTransisitive (t : L.RudimentaryTerm n) (ht : t.IsCharFree) (xs : Fin n → M) :
    t.isTransitive.toBoundedFormula 〘xs〙 ↔ Transitive (t〘xs〙 : M) := by
  simp [isTransitive, Transitive, ht, snoc]

theorem transitive_succ {a : M} (ha : Transitive a) : Transitive (succ a) := by
  simp only [Transitive, subset_iff, mem_succ_iff, forall_eq_or_imp] at ha ⊢
  tauto

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


end FirstOrder.Language.MemStructure
