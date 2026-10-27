/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.SUnion
/-!
file docstring
-/

open FirstOrder Language BoundedFormula MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M] [PairClosed M] [SDiffClosed M] (x : M)

namespace FirstOrder.Language

namespace RudimentaryTerm

def orderedPair {L : FirstOrder.Language} [L.HasMem]
  (r₁ r₂ : L.RudimentaryTerm n) := ᵣ{ᵣ{r₁, r₁}, ᵣ{r₁, r₂}}

@[inherit_doc] scoped[FirstOrder] notation:max "ᵣ(" x ", " y ")" =>
  FirstOrder.Language.RudimentaryTerm.orderedPair x y

instance {n} {L : FirstOrder.Language} [L.HasMem]
  (r₁ r₂ : L.RudimentaryTerm n) [r₁.CharFree] [r₂.CharFree] :
  ᵣ(r₁, r₂).CharFree := by
  unfold orderedPair; infer_instance

end RudimentaryTerm

namespace MemStructure

theorem eq_unorderedPair_iff [Extensional M] (x y z : M) :
    z = unorderedPair x y ↔ (∀ w ∈ z, (w = x ∨ w = y)) ∧ x ∈ z ∧ y ∈ z :=
  ⟨by grind, fun _ ↦ by ext; grind⟩

@[grind! .]
theorem mem_unorderedPair_left (x y : M) :
    x ∈ unorderedPair x y := by grind

@[grind! .]
theorem mem_unorderedPair_right (x y : M) :
    y ∈ unorderedPair x y := by grind

@[grind =]
theorem unorderedPair_comm [Extensional M] (x y : M) :
    unorderedPair x y = unorderedPair y x := by
  ext; grind

@[simp]
theorem unorderedPair_ne_empty [Extensional M] (x y : M) :
    unorderedPair x y ≠ ∅ := by
  simp [ne_empty_iff]

variable (M) in
instance [Extensional M] :
  Std.Commutative (α := M) unorderedPair where
  comm := fun x y ↦ unorderedPair_comm x y

theorem unorderedPair_eq_iff₀ [Extensional M] (x y₁ y₂ : M) :
    unorderedPair x y₁ = unorderedPair x y₂ ↔ y₁ = y₂ := by
  grind

theorem unorderedPair_eq_iff [Extensional M] (x₁ y₁ x₂ y₂ : M) :
    unorderedPair x₁ y₁ = unorderedPair x₂ y₂ ↔ (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = y₂ ∧ x₂ = y₁) := by
  grind

/-- The ordered pair `(x, y)` -/
@[grind]
noncomputable def orderedPair (x y : M) :=
-- ᵣ(ᵣ0, ᵣ1) 〘x, y〙₂
  unorderedPair (unorderedPair x x) (unorderedPair x y)

@[inherit_doc] scoped[FirstOrder.Language] notation:max "!(" x ", " y ")" =>
  MemStructure.orderedPair x y

@[grind]
def IsOrderedPair : Class M := fun z ↦ ∃ x y, z = !(x, y)

omit [PairClosed M] [SDiffClosed M] in
@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_orderedPair
    (r₁ r₂ : L.RudimentaryTerm n) (xs : Fin n → M) :
    ᵣ(r₁, r₂)〘xs〙 = (!(r₁〘xs〙, r₂〘xs〙) : M) := by
  simp [orderedPair, RudimentaryTerm.orderedPair]

instance [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [RudClosed M] :
    MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ !(ys 0, ys 1)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ ᵣ(ᵣ0, ᵣ1) fun _ _ ↦ by simp

-- omit [PairClosed M] [SDiffClosed M] in
-- @[grind =]
-- theorem orderedPair_eq (x y : M) :
--    !(x, y) = unorderedPair (unorderedPair x x) (unorderedPair x y) := by
--   simp [orderedPair, RudimentaryTerm.orderedPair]

@[simp, grind =]
theorem mem_orderedPair_iff (x y z : M) :
    z ∈ !(x, y) ↔ (z = unorderedPair x x ∨ z = unorderedPair x y) := by
  grind

theorem eq_orderedPair_iff [Extensional M] (x y z : M) :
    z = orderedPair x y ↔
      (∀ w ∈ z, w = unorderedPair x x ∨ w = unorderedPair x y) ∧
      unorderedPair x x ∈ z ∧ unorderedPair x y ∈ z :=
  ⟨by grind [orderedPair], fun _ ↦ by ext; grind [orderedPair]⟩

@[simp, push, grind =]
theorem orderedPair_eq_orderedPair_iff [Extensional M] (x₁ y₁ x₂ y₂ : M) :
    !(x₁, y₁) = !(x₂, y₂) ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  grind [orderedPair]

section LeftRight

variable [Extensional M]

noncomputable instance (a : M) : Decidable (∃ x y, a = !(x, y)) := by exact Classical.propDecidable _

/-- The left component of `a` if `a` is an ordered pair, `∅` otherwise -/
noncomputable def left : ClassFunction M := fun a ↦ dite (∃ x y, a = !(x, y)) Classical.choose fun _ ↦ ∅

@[simp]
theorem left_of_not_isOrderedPair {a : M} (ha : ¬IsOrderedPair a) :
    left a = ∅ := by
  have : ¬∃ x y, a = !(x, y) := by grind
  simp [left, this]

@[simp]
theorem left_orderedPair {a b : M} :
    left !(a, b) = a := by
  simp [left]

noncomputable instance (a : M) : Decidable (∃ y x, a = !(x, y)) := by exact Classical.propDecidable _

/-- The right component of `a` if `a` is an ordered pair, `∅` otherwise -/
noncomputable def right : ClassFunction M := fun a ↦ dite (∃ y x, a = !(x, y)) Classical.choose fun _ ↦ ∅

@[simp]
theorem right_of_not_isOrderedPair {a : M} (ha : ¬IsOrderedPair a) :
    right a = ∅ := by
  have : ¬∃ y x, a = !(x, y) := by grind
  simp [right, this]

@[simp]
theorem right_orderedPair {a b : M} :
    right !(a, b) = b := by
  simp [right]

end LeftRight

end MemStructure

end FirstOrder.Language
