import Mathlib.ModelTheory.Semantics

import Astlib.Basic.SetOperation.Empty

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y a : M)

variable (M) in
/- `M` is closed under `⋃` -/
class ClosedUnderSUnion where
  /-- `⋃ x` in set theory, denoted by `⋃₀ x` in lean -/
  sUnion : M → M
  sUnion_prop : ∀ x y : M, y ∈ sUnion x ↔ (∃ z ∈ x, y ∈ z)

export ClosedUnderSUnion (sUnion sUnion_prop)

@[inherit_doc] prefix:110 "⋃₀ " => sUnion

noncomputable instance (hM : M ⊨ M.L.allExSUnion) : ClosedUnderSUnion M where
  sUnion x := Classical.choose (exists_of_ex (realize_all.mp hM x))
  sUnion_prop := fun x ↦ by simpa using Classical.choose_spec (exists_of_ex (realize_all.mp hM x))

@[simp, grind =, push]
theorem mem_sUnion_iff [ClosedUnderSUnion M] : x ∈ ⋃₀ a ↔ ∃ y ∈ a, x ∈ y :=
  sUnion_prop _ _

@[simp, grind! ., push]
theorem sUnion_empty [Extensional M] [HasEmpty M] [ClosedUnderSUnion M] : ⋃₀ (∅ : M) = ∅ := by
  ext; grind

theorem sUnion_mono [HasEmpty M] [ClosedUnderSUnion M] {x y : M} (h : x ⊆ y) : ⋃₀ x ⊆ ⋃₀ y := by
  intro z
  simp only [mem_sUnion_iff]
  exact fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, h hw₁, hw₂⟩

end FirstOrder.Language.MemStructure
