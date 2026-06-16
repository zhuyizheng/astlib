import Astlib.ModelTheory.Semantics

import Astlib.Basic.SetOperation.Empty

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y a : M)

abbrev IsSUnion (a x : M) := ∀ y, y ∈ a ↔ (∃ z ∈ x, y ∈ z)

noncomputable instance : Decidable (∃ a : M, IsSUnion a x) :=
  Classical.propDecidable _

/-- `⋃ x` in set theory, denoted by `⋃₀ x` in lean -/
noncomputable def sUnion (x : M) :=
  dite (∃ a : M, IsSUnion a x) Classical.choose default

@[inherit_doc] prefix:110 "⋃₀ " => sUnion

variable (M) in
/- `M` is closed under `⋃` -/
class ClosedUnderSUnion : Prop where
  protected closedUnderSUnion (x : M) : ∃ a : M, IsSUnion a x

@[simp, grind =, push]
theorem mem_sUnion_iff [M.ClosedUnderSUnion] : x ∈ ⋃₀ a ↔ ∃ y ∈ a, x ∈ y := by
  simp only [sUnion, ClosedUnderSUnion.closedUnderSUnion]
  grind

theorem eq_sUnion_iff [M.Extensional] [M.ClosedUnderSUnion] : x = ⋃₀ a ↔
    (∀ z ∈ x, ∃ y ∈ a, z ∈ y) ∧ ∀ y ∈ a, ∀ z ∈ y, z ∈ x :=
  ⟨by grind, fun _ ↦ by ext; grind⟩

@[simp, grind! ., push]
theorem sUnion_empty [M.Extensional] [M.HasEmpty] [M.ClosedUnderSUnion] : ⋃₀ (∅ : M) = ∅ := by
  ext; grind

theorem sUnion_mono [M.HasEmpty] [M.ClosedUnderSUnion] {x y : M} (h : x ⊆ y) : ⋃₀ x ⊆ ⋃₀ y := by
  intro z
  simp only [mem_sUnion_iff]
  exact fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, h hw₁, hw₂⟩

end MemStructure

variable {L : FirstOrder.Language} [HasMem L] (t₁ t₂ : L.Term (α ⊕ Fin n))
  (v : α → M) (xs : Fin n → M)

/-- `t₁ ∈ ⋃₀ t₂` -/
abbrev Term.memSUnion :=
  ∃'∈ t₂ t₁.castSucc ∈' &-1

instance : (t₁.memSUnion t₂).DeltaZero := by infer_instance

/-- `t₁ = ⋃₀ t₂` -/
abbrev Term.eqSUnion :=
  (∀'∈ t₁ (&-1).memSUnion t₂.castSucc) ⊓ ∀'∈ t₂ ∀'∈ &-1 (&-1 ∈' t₁.castSucc.castSucc)

instance : (t₁.eqSUnion t₂).DeltaZero := by infer_instance

variable {M : MemStructure} (v : α → M) (xs : Fin n → M)

variable (t₁ t₂ : M.L.Term (α ⊕ Fin n))

@[simp 1100]
theorem Term.memSUnion_iff : (t₁.memSUnion t₂).Realize v xs ↔
    ∃ y ∈ t₂.realize' v xs, t₁.realize' v xs ∈ y := by
  simp

@[simp 1100]
theorem Term.eqSUnion_iff [M.Extensional] [M.ClosedUnderSUnion] : (t₁.eqSUnion t₂).Realize v xs ↔
    t₁.realize' v xs = ⋃₀ t₂.realize' v xs := by
  simp [Fin.castLE_add_two_castSucc, M.eq_sUnion_iff]

end FirstOrder.Language
