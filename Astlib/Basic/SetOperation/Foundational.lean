/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Insert
import Astlib.Basic.SetOperation.Multiclass.Defs
import Astlib.Basic.SetOperation.Comprehension
/-!
file docstring
-/

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M]
  (x y : M)

def IsMemMin (a x : M) := a ∈ x ∧ ∀ y ∈ a, y ∉ x

noncomputable instance : Decidable (∃ a, IsMemMin a x) :=
  Classical.propDecidable _

noncomputable def memMin : ClassFunction M := fun x ↦ dite (∃ a, IsMemMin a x) Classical.choose default

variable (M) in
/- `M` is closed under `⋃` -/
class Foundational : Prop where
  protected hasMemMin : ∀ (x : M), x ≠ ∅ → ∃ a, IsMemMin a x

@[simp]
theorem isMemMin_memMin [Foundational M] {x : M} (hx : x ≠ ∅) : IsMemMin (memMin x) x := by
  simp only [memMin, Foundational.hasMemMin x hx, ↓reduceDIte]
  grind

@[simp, grind .]
theorem memMin_mem [Foundational M] {x : M} (hx : x ≠ ∅) : memMin x ∈ x := by
  grind [isMemMin_memMin, IsMemMin]

@[simp, grind .]
theorem notMem_memMin [RudClosed M] [Foundational M] {x y : M} (hy : y ∈ x) :
    y ∉ memMin x := by
  have : x ≠ ∅ := by grind
  grind [isMemMin_memMin, IsMemMin]

@[simp]
theorem notMem_of_mem_memMin [RudClosed M] [Foundational M] {x y : M} (hy : y ∈ memMin x) :
    y ∉ x := by
  grind

@[simp, grind .]
theorem notMem_self [RudClosed M] [Foundational M] : x ∉ x := by
  have := memMin_mem (x := ({x} : M)) (by simp)
  grind

-- @[simp, grind .]
-- theorem not_mem_mem [Extensional M] [RudClosed M] [Foundational M] : ¬(x ∈ y ∧ y ∈ x) := by
--   have := memMin_mem (by simp)
--   grind

theorem notMem_of_mem [Extensional M] [RudClosed M] [Foundational M] {x y : M} (h : x ∈ y) : y ∉ x := by
  have := memMin_mem (x := ({x, y} : M)) (by simp)
  grind

theorem ne_of_mem [RudClosed M] [Foundational M] {x y : M} (h : x ∈ y) : x ≠ y := by
  rintro rfl
  exact notMem_self _ h

theorem notMem_of_mem_of_mem [Extensional M] [RudClosed M] [Foundational M] {x y z : M} (h : x ∈ y) (h' : y ∈ z) : z ∉ x := by
  obtain ⟨h₁, h₂⟩ := isMemMin_memMin (x := ({x, y, z} : M)) (by simp)
  grind

@[simp, grind .]
theorem succ_neq [RudClosed M] [Extensional M]
    [Foundational M] :
    succ x ≠ x := by
  grind [succ]

end FirstOrder.Language.MemStructure
