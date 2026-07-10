/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Insert
import Astlib.Mathlib.ModelTheory.Semantics
/-!
file docstring
-/

open Fin

namespace FirstOrder.Language.MemStructure

variable {α : Type*} {M : MemStructure} (x y z : M) {n : ℕ}

def IsComprehension (a x : M) (φ : M.L.BoundedFormula α (n + 1))
  (v : α → M) (xs : Fin n → M) := ∀ z, z ∈ a ↔ z ∈ x ∧ φ〘v, snoc xs z〙

noncomputable instance (x : M) (φ : M.L.BoundedFormula α (n + 1)) (v : α → M) (xs : Fin n → M) :
  Decidable (∃ a : M, IsComprehension a x φ v xs) :=
  Classical.propDecidable _

/-- The subset of `x` containing `z` for which `φ〘v, snoc xs z〙` holds -/
noncomputable def comprehension (x : M) (φ : M.L.BoundedFormula α (n + 1))
  (v : α → M) (xs : Fin n → M) :=
  dite (∃ a : M, IsComprehension a x φ v xs)
    Classical.choose default

/-- The subset of `x` containing `z` for which `φ〘default, snoc xs z〙` holds -/
noncomputable def comprehension_empty (x : M)
    (φ : M.L.BoundedFormula Empty (n + 1))
    (xs : Fin n → M) :=
  comprehension x φ default xs

/-- The subset of `x` containing `z` for which `φ〘default, ![z]〙` holds -/
noncomputable def comprehension_empty_one (x : M)
    (φ : M.L.BoundedFormula Empty 1) :=
  comprehension x φ default default

/-- The subset of `x` containing `z` for which `φ〘default, ![w,z]〙` holds -/
noncomputable def comprehension_empty_two (x : M)
    (φ : M.L.BoundedFormula Empty 2) (w : M) :=
  comprehension x φ default ![w]

@[inherit_doc] scoped[FirstOrder.Language] notation:max
  φ "〘"v ", " xs "," " ∈ " x "〙" => MemStructure.comprehension x φ v xs

@[inherit_doc] scoped[FirstOrder.Language] notation:max
  φ "〘" xs "," " ∈ " x "〙" => MemStructure.comprehension_empty x φ xs

@[inherit_doc] scoped[FirstOrder.Language] notation:max
  φ "〘" " ∈ " x "〙" => MemStructure.comprehension_empty_one x φ

@[inherit_doc] scoped[FirstOrder.Language] notation:max
  φ "〘" w "," " ∈ " x "〙₀" => MemStructure.comprehension_empty_two x φ w

class HasComprehension (x : M) (φ : M.L.BoundedFormula α (n + 1))
  (v : α → M) (xs : Fin n → M) : Prop where
  protected hasComprehension : ∃ a : M, IsComprehension a x φ v xs

@[simp, grind =, push]
theorem mem_comprehension_iff (x : M) (φ : M.L.BoundedFormula α (n + 1))
    (v : α → M) (xs : Fin n → M) [hx : HasComprehension x φ v xs] (z : M) :
    z ∈ φ 〘v, xs, ∈ x〙 ↔ z ∈ x ∧ φ〘v, snoc xs z〙 := by
  convert Classical.choose_spec hx.hasComprehension z
  simp [MemStructure.comprehension, HasComprehension.hasComprehension]


@[simp, grind =, push]
theorem mem_comprehension_empty_iff (x : M) (φ : M.L.BoundedFormula Empty (n + 1))
    (xs : Fin n → M) [hx : HasComprehension x φ default xs] (z : M) :
    z ∈ φ〘xs, ∈ x〙 ↔ z ∈ x ∧ φ〘default, snoc xs z〙 :=
  mem_comprehension_iff x φ default xs z

@[simp, grind =, push]
theorem mem_comprehension_empty_one_iff (x : M) (φ : M.L.BoundedFormula Empty 1)
    [HasComprehension x φ default default] (z : M) :
    z ∈ φ〘∈ x〙 ↔ z ∈ x ∧ φ〘default, snoc default z〙 :=
  mem_comprehension_empty_iff x φ default z

@[simp, grind =, push]
theorem mem_comprehension_empty_two_iff (x : M) (φ : M.L.BoundedFormula Empty 2)
    (w : M) [hx : HasComprehension x φ default ![w] ] (z : M) :
    z ∈ φ〘w, ∈ x〙₀ ↔ z ∈ x ∧ φ〘default, ![w, z]〙 := by
  convert mem_comprehension_empty_iff x φ ![w] z
  · rfl
  · simp

theorem comprehension_subset (x : M) (φ : M.L.BoundedFormula α (n + 1))
    (v : α → M) (xs : Fin n → M) [HasComprehension x φ v xs] :
    φ 〘v, xs, ∈ x〙 ⊆ x := by
  grind

theorem comprehension_top [M.Extensional] (x : M)
    (v : α → M) (xs : Fin n → M) [HasComprehension x ⊤ v xs] :
    ⊤ 〘v, xs, ∈ x〙 = x := by
  ext; simp

theorem comprehension_bot [M.Extensional] [M.HasEmpty] {x : M}
    (v : α → M) (xs : Fin n → M) [HasComprehension x ⊥ v xs] :
    ⊥ 〘v, xs, ∈ x〙 = ∅ := by
  ext; simp

theorem comprehension_eq_iff [M.Extensional] (x : M) (φ ψ : M.L.BoundedFormula α (n + 1))
    (v w : α → M) (xs ys : Fin n → M) [HasComprehension x φ v xs] [HasComprehension x ψ w ys] :
    φ 〘v, xs, ∈ x〙 = ψ 〘w, ys, ∈ x〙 ↔ ∀ z ∈ x, φ〘v, snoc xs z〙 ↔ ψ〘w, snoc ys z〙 := by
  simp [eq_iff]

theorem comprehension_eq_univ_iff [M.Extensional] (x : M) (φ : M.L.BoundedFormula α (n + 1))
    (v : α → M) (xs : Fin n → M) [HasComprehension x φ v xs] :
    φ 〘v, xs, ∈ x〙 = x ↔ ∀ z ∈ x, φ〘v, snoc xs z〙 := by
  simp [eq_iff]

theorem comprehension_eq_empty_iff [M.Extensional] [M.HasEmpty] (x : M)
    (φ : M.L.BoundedFormula α (n + 1))
    (v : α → M) (xs : Fin n → M) [HasComprehension x φ v xs] :
    φ 〘v, xs, ∈ x〙 = ∅ ↔ ∀ z ∈ x, ¬φ〘v, snoc xs z〙 := by
  simp [eq_iff]

variable (M) in
class ClosedUnderDeltaZeroComprehension : Prop where
  closedUnderDeltaZeroComprehension {n : ℕ} (x : M) (φ : M.L.BoundedFormula Empty (n + 1))
    [φ.DeltaZero]
    (xs : Fin n → M) :
    ∃ a : M, IsComprehension a x φ default xs

export ClosedUnderDeltaZeroComprehension (closedUnderDeltaZeroComprehension)

instance [M.ClosedUnderDeltaZeroComprehension] (x : M)
  (φ : M.L.BoundedFormula Empty (n + 1)) [φ.DeltaZero] (xs : Fin n → M) :
  HasComprehension x φ default xs := ⟨closedUnderDeltaZeroComprehension x φ xs⟩

instance [M.ClosedUnderDeltaZeroComprehension] : M.HasEmpty :=
  ⟨⟨⊥〘∈ default〙, by simp [IsEmpty]⟩⟩

variable (M) in
class ClosedUnderComprehension : Prop where
  closedUnderComprehension {n : ℕ} (x : M) (φ : M.L.BoundedFormula Empty (n + 1))
    (xs : Fin n → M) :
    ∃ a : M, IsComprehension a x φ default xs

export ClosedUnderComprehension (closedUnderComprehension)

instance [M.ClosedUnderComprehension] : M.ClosedUnderDeltaZeroComprehension :=
  ⟨fun x φ _ xs ↦ closedUnderComprehension x φ xs⟩

instance [M.ClosedUnderComprehension] (x : M)
  {φ : M.L.BoundedFormula Empty (n + 1)} (xs : Fin n → M) :
  HasComprehension x φ default xs := ⟨closedUnderComprehension x φ xs⟩

end FirstOrder.Language.MemStructure
