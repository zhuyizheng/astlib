/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Rudimentary.DeltaZero
import Astlib.Basic.SetOperation.Singleton
import Astlib.Basic.SetOperation.Union
/-!
file docstring
-/

open FirstOrder Language BoundedFormula RudimentaryTerm

namespace FirstOrder.Language

def RudimentaryTerm.insert₀ {L : FirstOrder.Language} [L.HasMem] : L.RudimentaryTerm 2 :=
  {ᵣ0} ∪ ᵣ1

instance {n} {L : FirstOrder.Language} [L.HasMem] :
  Insert (L.RudimentaryTerm n) (L.RudimentaryTerm n) :=
  ⟨fun r₁ r₂ ↦ insert₀.substBoundRud ![r₁, r₂]⟩

@[simp]
theorem RudimentaryTerm.insert_def {L : FirstOrder.Language} [L.HasMem]
    (r₁ r₂ : L.RudimentaryTerm n) :
    insert r₁ r₂ = insert₀.substBoundRud ![r₁, r₂] := rfl

instance {L : Language} [L.HasMem] :
  (insert₀ : L.RudimentaryTerm 2).CharFree := by
  unfold insert₀; infer_instance

instance {L : Language} [L.HasMem]
  (r₁ r₂ : L.RudimentaryTerm n) [r₁.CharFree] [r₂.CharFree] :
  (insert r₁ r₂ : L.RudimentaryTerm n).CharFree := by
  rw [insert_def]; infer_instance

namespace MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M]
  (x y z : M)

noncomputable instance : Insert M M := ⟨fun x y ↦ insert₀〘x, y〙₂⟩

instance [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [RudClosed M] :
    MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ insert (ys 0) (ys 1)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ insert₀ fun _ _ ↦ rfl

@[grind =]
theorem insert_eq : insert x y = {x} ∪ y := by
  simp [insert, insert₀]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_insert₀ (xs : Fin 2 → M) :
    RudimentaryTerm.insert₀〘xs〙 = insert (xs 0) (xs 1) := by
  simp [insert_eq, insert₀]

variable [RudClosed M]

@[simp, grind! .]
theorem mem_insert : x ∈ insert x y := by
  grind

@[simp]
theorem insert_ne_empty [Extensional M] :
    insert x y ≠ ∅ := by
  grind

@[simp, grind! .]
theorem subset_insert : y ⊆ insert x y := by
  grind

@[simp, grind =]
theorem mem_insert_iff :
    z ∈ insert x y ↔ z = x ∨ z ∈ y := by
  grind

@[simp, grind .]
theorem insert_eq_self_iff [Extensional M] :
    insert x y = y ↔ x ∈ y :=
  ⟨by grind, fun _ ↦ by ext; grind⟩

@[simp, grind =]
theorem insert_eq_self [Extensional M] {x y : M} (h : x ∈ y) : insert x y = y :=
  (insert_eq_self_iff x y).mpr h

@[simp, grind =]
theorem insert_subset_iff :
    insert x y ⊆ z ↔ x ∈ z ∧ y ⊆ z := by
  grind

theorem insert_subset_insert {y z : M} (h : y ⊆ z) :
    insert x y ⊆ insert x z := by
  grind

theorem union_insert [Extensional M] :
    x ∪ insert y z = insert y (x ∪ z) := by
  ext
  grind

theorem sUnion_insert [Extensional M] : ⋃₀ (insert x y : M) = x ∪ ⋃₀ y := by
  ext
  simp [or_and_right, exists_or]

noncomputable def succ : ClassFunction M := fun x ↦ insert x x

@[simp, grind =]
theorem mem_succ_iff :
    z ∈ succ x ↔ z = x ∨ z ∈ x := by
  simp [succ]

@[simp, grind .]
theorem succ_ne_empty : succ x ≠ ∅ := fun h ↦ by simpa [h] using mem_succ_iff x x

@[simp, grind .]
theorem mem_succ_self : x ∈ succ x := by simp

theorem mem_succ_of_mem {a b : M} (h : a ∈ b) : a ∈ succ b := by simp [h]

/-- Case split on membership in a successor -/
theorem mem_or_eq_of_mem_succ {x z : M} (h : z ∈ succ x) : z ∈ x ∨ z = x := by grind

theorem succ_empty [Extensional M] : succ (∅ : M) = {∅} := by
  ext z
  simp

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.succ₀
    {L : Language} [L.HasMem] : L.RudimentaryTerm 1 := insert (ᵣ0) (ᵣ0)

@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.succ
    {L : Language} [L.HasMem] (r : L.RudimentaryTerm n) :
  L.RudimentaryTerm n := succ₀.substBoundRud ![r]

instance {L : Language} [L.HasMem] :
  (succ₀ : L.RudimentaryTerm 1).CharFree := by
  unfold succ₀; infer_instance

instance [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] :
    (succ : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq RudimentaryTerm.succ₀ fun _ ↦ by simp [succ, succ₀]

instance {L : Language} [L.HasMem]
  (r : L.RudimentaryTerm n) [r.CharFree] : r.succ.CharFree := by
  unfold RudimentaryTerm.succ; infer_instance

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_succ₀ (xs : Fin 1 → M) :
    succ₀〘xs〙 = succ (xs 0) := by
  simp [succ₀, succ]

-- source
-- theorem Set.insert_subset {α : Type u_1} {s t : Set α} {a : α} (ha : a ∈ t) (hs : s ⊆ t) :
-- insert a s ⊆ t
-- source
-- theorem Set.insert_subset_insert {α : Type u_1} {s t : Set α} {a : α} (h : s ⊆ t) :
-- insert a s ⊆ insert a t

-- @[simp, grind! .]
-- theorem mem_two_iff (x₁ x₂ y : M) :
--     y ∈ ({x₁, x₂} : M) ↔ y = x₁ ∨ y = x₂ := by
--   simp

-- @[simp, grind! .]
-- theorem mem_three_iff (x₁ x₂ y : M) :
--     y ∈ ({x₁, x₂} : M) ↔ y = x₁ ∨ y = x₂ := by
--   simp


end FirstOrder.Language.MemStructure
