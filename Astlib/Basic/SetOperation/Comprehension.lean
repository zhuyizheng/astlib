import Astlib.Basic.SetOperation.Insert
import Astlib.Mathlib.ModelTheory.Semantics

open Fin

namespace FirstOrder.Language.MemStructure

variable {α : Type*} {M : MemStructure} (x y z : M)

abbrev IsComprehension (a x : M) (φ : M.L.BoundedFormula α (n + 2))
  (v : α → M) (xs : Fin n → M) := ∀ z, z ∈ a ↔ z ∈ x ∧ φ.Realize v (snoc (snoc xs x) z)

noncomputable instance (x : M) (φ : M.L.BoundedFormula α (n + 2)) (v : α → M) (xs : Fin n → M) :
  Decidable (∃ a : M, IsComprehension a x φ v xs) :=
  Classical.propDecidable _

/-- The subset of `x` containing `z` for which `φ.Realize v (snoc (snoc xs x) z)` holds -/
noncomputable def comprehension (x : M) (φ : M.L.BoundedFormula α (n + 2))
  (v : α → M) (xs : Fin n → M) :=
  dite (∃ a : M, IsComprehension a x φ v xs)
    Classical.choose default

/-- The subset of `x` containing `z` for which `φ.Realize default (snoc (snoc xs x) z)` holds -/
noncomputable abbrev comprehension_empty (x : M)
    (φ : M.L.BoundedFormula Empty (n + 2))
    (xs : Fin n → M) :=
  comprehension x φ default xs

/-- The subset of `x` containing `z` for which `φ.Realize default ![x, z]` holds -/
noncomputable abbrev comprehension_empty_two (x : M)
    (φ : M.L.BoundedFormula Empty 2) :=
  comprehension x φ default default

/-- The subset of `x` containing `z` for which `φ.Realize default ![w, x, z]` holds -/
noncomputable abbrev comprehension_empty_three (x : M)
    (φ : M.L.BoundedFormula Empty 3) (w : M) :=
  comprehension x φ default ![w]

@[inherit_doc] scoped[FirstOrder.Language] notation:max
  "{∈" x " | " φ "〘"v ", " xs "〙}" => MemStructure.comprehension x φ v xs

@[inherit_doc] scoped[FirstOrder.Language] notation:max
  "{∈" x " | " φ "〘" xs "〙}" => MemStructure.comprehension_empty x φ xs

@[inherit_doc] scoped[FirstOrder.Language] notation:max
  "{∈" x " | " φ "}" => MemStructure.comprehension_empty_two x φ

@[inherit_doc] scoped[FirstOrder.Language] notation:max
  "{∈" x " | " φ "〘" w "〙₀}" => MemStructure.comprehension_empty_three x φ w

class HasComprehension (x : M) (φ : M.L.BoundedFormula α (n + 2))
  (v : α → M) (xs : Fin n → M) : Prop where
  protected hasComprehension :
    ∃ a : M, ∀ z, z ∈ a ↔ z ∈ x ∧ φ.Realize v (snoc (snoc xs x) z)

@[simp, grind =, push]
theorem mem_comprehension_iff (x : M) (φ : M.L.BoundedFormula α (n + 2))
    (v : α → M) (xs : Fin n → M) [hx : HasComprehension x φ v xs] (z : M) :
    z ∈ {∈ x | φ 〘v, xs〙} ↔ z ∈ x ∧ φ.Realize v (snoc (snoc xs x) z) := by
  simp only [comprehension, HasComprehension.hasComprehension, ↓reduceDIte]
  grind

@[simp, grind =, push]
theorem mem_comprehension_iff₀ (x : M) (φ : M.L.BoundedFormula Empty 2)
    [HasComprehension x φ default default] (z : M) :
    z ∈ {∈ x | φ } ↔ z ∈ x ∧ φ.Realize default (snoc (snoc default x) z) :=
  mem_comprehension_iff x φ default default z

theorem comprehension_subset (x : M) (φ : M.L.BoundedFormula α (n + 2))
    (v : α → M) (xs : Fin n → M) [HasComprehension x φ v xs] :
    {∈ x | φ 〘v, xs〙} ⊆ x := by
  grind

theorem comprehension_top [M.Extensional] (x : M)
    (v : α → M) (xs : Fin n → M) [HasComprehension x ⊤ v xs] :
    {∈ x | ⊤ 〘v, xs〙} = x := by
  ext; simp

theorem comprehension_bot [M.Extensional] [M.HasEmpty] {x : M}
    (v : α → M) (xs : Fin n → M) [HasComprehension x ⊥ v xs] :
    {∈ x | ⊥ 〘v, xs〙} = ∅ := by
  ext; simp

theorem comprehension_eq_iff [M.Extensional] (x : M) (φ ψ : M.L.BoundedFormula α (n + 2))
    (v w : α → M) (xs ys : Fin n → M) [HasComprehension x φ v xs] [HasComprehension x ψ w ys] :
    {∈ x | φ 〘v, xs〙} = {∈ x | ψ 〘w, ys〙} ↔
      ∀ z ∈ x, φ.Realize v (snoc (snoc xs x) z) ↔ ψ.Realize w (snoc (snoc ys x ) z) := by
  simp [eq_iff]

theorem comprehension_eq_univ_iff [M.Extensional] (x : M) (φ : M.L.BoundedFormula α (n + 2))
    (v : α → M) (xs : Fin n → M) [HasComprehension x φ v xs] :
    {∈ x | φ 〘v, xs〙} = x ↔
      ∀ z ∈ x, φ.Realize v (snoc (snoc xs x) z) := by
  simp [eq_iff]

theorem comprehension_eq_empty_iff [M.Extensional] [M.HasEmpty] (x : M)
    (φ : M.L.BoundedFormula α (n + 2))
    (v : α → M) (xs : Fin n → M) [HasComprehension x φ v xs] :
    {∈ x | φ 〘v, xs〙} = ∅ ↔
      ∀ z ∈ x, ¬φ.Realize v (snoc (snoc xs x) z) := by
  simp [eq_iff]

variable (M) in
class ClosedUnderDeltaZeroComprehension : Prop where
  closedUnderDeltaZeroComprehension {n} (x : M) (φ : M.L.BoundedFormula Empty (n + 2)) [φ.DeltaZero]
    (xs : Fin n → M) :
    ∃ a : M, IsComprehension a x φ default xs

export ClosedUnderDeltaZeroComprehension (closedUnderDeltaZeroComprehension)

instance [M.ClosedUnderDeltaZeroComprehension] (x : M)
  (φ : M.L.BoundedFormula Empty (n + 2)) [φ.DeltaZero] (xs : Fin n → M) :
  HasComprehension x φ default xs := ⟨closedUnderDeltaZeroComprehension x φ xs⟩

instance [M.ClosedUnderDeltaZeroComprehension] : M.HasEmpty :=
  ⟨⟨{∈ default | ⊥}, by simp [IsEmpty]⟩⟩

variable (M) in
class ClosedUnderComprehension : Prop where
  closedUnderComprehension (x : M) (φ : M.L.BoundedFormula Empty (n + 2))
    (xs : Fin n → M) :
    ∃ a : M, IsComprehension a x φ default xs

export ClosedUnderComprehension (closedUnderComprehension)

instance [M.ClosedUnderComprehension] : M.ClosedUnderDeltaZeroComprehension :=
  ⟨fun x φ _ xs ↦ closedUnderComprehension x φ xs⟩

instance [M.ClosedUnderComprehension] (x : M)
  {φ : M.L.BoundedFormula Empty (n + 2)} (xs : Fin n → M) :
  HasComprehension x φ default xs := ⟨closedUnderComprehension x φ xs⟩

end FirstOrder.Language.MemStructure
