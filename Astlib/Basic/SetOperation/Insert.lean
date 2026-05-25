import Astlib.Basic.SetOperation.Singleton
import Astlib.Basic.SetOperation.Union

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y z : M)

noncomputable instance : Insert M M where
  insert x y := {x} ∪ y

@[simp, grind! .]
theorem mem_insert [M.ClosedUnderSUnion] [M.ClosedUnderPair] : x ∈ insert x y := by
  simp [Insert.insert]

@[simp]
theorem insert_ne_empty [M.Extensional] [M.HasEmpty] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    insert x y ≠ ∅ := by
  grind

@[simp, grind! .]
theorem subset_insert [M.ClosedUnderSUnion] [M.ClosedUnderPair] : y ⊆ insert x y := by
  simp only [Insert.insert]
  grind

@[simp, grind =]
theorem mem_insert_iff [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    z ∈ insert x y ↔ z = x ∨ z ∈ y := by
  simp [Insert.insert]

@[simp, grind .]
theorem insert_eq_self [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    insert x y = y ↔ x ∈ y :=
  ⟨by grind, fun _ ↦ by ext; grind⟩

@[simp, grind =]
theorem insert_subset_iff [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    insert x y ⊆ z ↔ x ∈ z ∧ y ⊆ z := by
  grind

theorem insert_subset_insert [M.ClosedUnderSUnion] [M.ClosedUnderPair] {y z : M} (h : y ⊆ z) :
    insert x y ⊆ insert x z := by
  grind

noncomputable abbrev succ (x : M) := insert x x

-- source
-- theorem Set.insert_subset {α : Type u_1} {s t : Set α} {a : α} (ha : a ∈ t) (hs : s ⊆ t) :
-- insert a s ⊆ t
-- source
-- theorem Set.insert_subset_insert {α : Type u_1} {s t : Set α} {a : α} (h : s ⊆ t) :
-- insert a s ⊆ insert a t

-- @[simp, grind! .]
-- theorem mem_two_iff [M.ClosedUnderSUnion] [M.ClosedUnderPair] (x₁ x₂ y : M) :
--     y ∈ ({x₁, x₂} : M) ↔ y = x₁ ∨ y = x₂ := by
--   simp

-- @[simp, grind! .]
-- theorem mem_three_iff [M.ClosedUnderSUnion] [M.ClosedUnderPair] (x₁ x₂ y : M) :
--     y ∈ ({x₁, x₂} : M) ↔ y = x₁ ∨ y = x₂ := by
--   simp


end FirstOrder.Language.MemStructure
