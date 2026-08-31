/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Singleton
import Astlib.Basic.SetOperation.Union
/-!
file docstring
-/

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language

instance {n} {L : FirstOrder.Language} [L.HasMem] :
  Insert (L.RudimentaryTerm n) (L.RudimentaryTerm n) := ⟨fun r₁ r₂ ↦ {r₁} ∪ r₂⟩

namespace MemStructure

variable {M : MemStructure} (x y z : M)

noncomputable instance : Insert M M := ⟨fun x y ↦ ({ᵣ0} ∪ ᵣ1)〘x, y〙₂⟩

@[grind =]
theorem insert_eq : insert x y = {x} ∪ y := by
  simp only [singleton, union_eq, sUnion_eq]
  rfl

variable [M.RudClosed]

@[simp, grind! .]
theorem mem_insert : x ∈ insert x y := by
  grind

@[simp]
theorem insert_ne_empty [M.Extensional] :
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
theorem insert_eq_self [M.Extensional] :
    insert x y = y ↔ x ∈ y :=
  ⟨by grind, fun _ ↦ by ext; grind⟩

@[simp, grind =]
theorem insert_subset_iff :
    insert x y ⊆ z ↔ x ∈ z ∧ y ⊆ z := by
  grind

theorem insert_subset_insert {y z : M} (h : y ⊆ z) :
    insert x y ⊆ insert x z := by
  grind

noncomputable def succ (x : M) := insert x x

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
