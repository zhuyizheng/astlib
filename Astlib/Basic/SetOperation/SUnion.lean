import Mathlib.ModelTheory.Semantics

import Astlib.Basic.SetOperation.HasEmpty

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable (M : MemStructure)

/- `M` is closed under `⋃` -/
class HasSUnion where
  /-- `⋃ x` in set theory, denoted by `⋃₀ x` in lean -/
  sUnion : M → M
  sUnion_prop : ∀ x y : M, y ∈ sUnion x ↔ (∃ z ∈ x, y ∈ z)

export HasSUnion (sUnion sUnion_prop)

@[inherit_doc] prefix:110 "⋃₀ " => sUnion

noncomputable instance (hM : M ⊨ M.L.exSUnion) : HasSUnion M where
  sUnion x := Classical.choose (exists_of_ex (realize_all.mp hM x))
  sUnion_prop := fun x ↦ by simpa using Classical.choose_spec (exists_of_ex (realize_all.mp hM x))

variable {M}

@[simp, grind =, push]
theorem mem_sUnion_iff [HasSUnion M] (x a : M) : x ∈ ⋃₀ a ↔ ∃ y ∈ a, x ∈ y :=
  sUnion_prop _ _

@[simp, grind! ., push]
theorem sUnion_empty [Extensional M] [HasEmpty M] [HasSUnion M] :
    ⋃₀ (∅ : M) = ∅ := by
  ext; grind

end FirstOrder.Language.MemStructure
