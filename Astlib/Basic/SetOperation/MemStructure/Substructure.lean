/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.ModelTheory.Substructures

import Astlib.Mathlib.ModelTheory.Semantics
import Astlib.Basic.SetOperation.MemStructure.Defs
import Astlib.Basic.SetOperation.Multiclass.Defs
import Astlib.Mathlib.Fin.Basic
import Astlib.Mathlib.Sum.Basic
/-!
file docstring
-/

open Fin FirstOrder Language MemStructure

namespace FirstOrder

namespace Language

variable {m n : ℕ} {L : Language} {M : Type*} [L.MemStructure M]
  -- (t : L.Term' n) (φ : L.BoundedFormula' (n + 1))
  -- {xs : Fin n → M}

namespace MemStructure

@[coe]
def toClass (a : M) : Class M := {x | x ∈ a}

instance : Coe M (Class M) := ⟨toClass⟩

theorem toClass_subset {a b : M} (hab : a ⊆ b) : (a : Class M) ⊆ (b : Class M) := by
  norm_cast

@[grind .]
theorem Class.trans {A B C : Class M} (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C :=
  fun x hx ↦ hBC x (hAB x hx)

instance : IsTrans (Class M) Subset := ⟨@Class.trans _ _ _⟩

theorem Class.mem_trans {x : M} {A B : Class M} (hxA : A x) (hAB : A ⊆ B) : B x :=
  hAB x hxA

instance : Trans (α := M) (β := Class M) (γ := Class M)
  (fun x A ↦ A x) Subset (fun x B ↦ B x) :=
  ⟨fun hxy hyz ↦ hyz _ hxy⟩

variable [L.ExtraConstantsUnaryRelationsOnly]
-- noncomputable instance (a : M) : Decidable (∀ (c : L.Constants), L.constantMap c ∈ a) :=
  -- Classical.propDecidable _

noncomputable def toSubstructure (N : Class M) : L.Substructure M :=
  ⟨{x | N x} ∪ {↑c | c : L.Constants}, by
    intro n f
    cases n with
    | zero => exact fun _ _ ↦ Or.inr ⟨f, funMap_eq_coe_constants.symm⟩
    | succ n => exact IsEmpty.elim' (by infer_instance) f
  ⟩

noncomputable instance (N : Class M) : MemStructure L (toSubstructure N) where

-- @[simp]
theorem union_constants_eq {N : Class M} (hN : ∀ c : L.Constants, N ↑c) :
    {x | N x} ∪ {↑c | c : L.Constants} = {x | N x} := by
  ext
  grind

-- @[simp]
theorem mem_toSubstructure_of_mem {N : Class M} {x : M} (hx : N x) :
    x ∈ toSubstructure N := by
  simp only [toSubstructure]
  rw [← Substructure.mem_carrier]
  push_cast
  simp only [Set.mem_union]
  left
  exact hx

theorem toSubstructure_eq_of_constants_mem {N : Class M} (hN : ∀ c : L.Constants, N ↑c) :
    (toSubstructure N : Set M) = {x | N x} := by
  rw [← union_constants_eq hN]
  simp [toSubstructure]
  norm_cast


-- @[simp]
-- theorem mem_toSubstructure_of_constants_mem {N : Set M} (hN : ∀ c : L.Constants, ↑c ∈ N) (x : M) :
--     x ∈ (toSubstructure N : Set M)↔ x ∈ N := by
--   simp only [SetLike.mem_coe]
--   nth_rw 2 [← toSubstructure_eq_of_constants_mem hN]
--   norm_cast


theorem mem_toSubstructure_of_forall {N : Class M}
    {xs : Fin n → M} (hxs : ∀ i, N (xs i)) (i : Fin n) :
    xs i ∈ toSubstructure N := by
  apply mem_toSubstructure_of_mem
  exact hxs _

def toSubstructureTuple {N : Class M}
  {xs : Fin n → M} (hxs : ∀ i, N (xs i)) (i : Fin n) :
  toSubstructure N :=
  ⟨xs i, mem_toSubstructure_of_forall hxs i⟩

@[simp]
theorem toSubstructure_eq_iff {N : Class M} {x y : toSubstructure N} :
    x = y ↔ x.val = y.val := by
  simp

@[simp]
theorem toSubstructure_mem_iff {N : Class M} {x y : toSubstructure N} :
    x ∈ y ↔ x.val ∈ y.val := by
  dsimp only [Membership.mem, Structure.RelMap]
  rw [← eq_iff_iff]
  congr
  ext i; fin_cases i <;> simp

-- @[simp]
-- theorem mem_toSubstructure_iff {N : Set M} {x y : M} (hx : x ∈ N) (hy : y ∈ N) :
--     (⟨x, mem_toSubstructure_of_mem hx⟩ : toSubstructure N) ∈ (⟨y, mem_toSubstructure_of_mem hy⟩ : toSubstructure N) ↔ x ∈ y := by
--   simp


end MemStructure

end Language

end FirstOrder
