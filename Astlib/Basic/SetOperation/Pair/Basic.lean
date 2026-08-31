/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.SUnion
/-!
file docstring
-/

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language

namespace RudimentaryTerm

variable {L : FirstOrder.Language} [L.HasMem]

def orderedPair (r₁ r₂ : L.RudimentaryTerm n) := ᵣ{ᵣ{r₁, r₁}, ᵣ{r₁, r₂}}

@[inherit_doc] scoped[FirstOrder] notation:max "ᵣ(" x ", " y ")" =>
  FirstOrder.Language.RudimentaryTerm.orderedPair x y

@[simp]
theorem castLHom_orderedPair {M : MemStructure}
    (r₁ r₂ : M.L'.RudimentaryTerm n) :
    ᵣ(r₁, r₂).castLHom = ᵣ(r₁.castLHom, r₂.castLHom) := by
  simp [orderedPair]

end RudimentaryTerm

namespace MemStructure

variable {M : MemStructure} [M.RudClosed]

theorem eq_unorderedPair_iff [M.Extensional] (x y z : M) :
    z = unorderedPair x y ↔ (∀ w ∈ z, (w = x ∨ w = y)) ∧ x ∈ z ∧ y ∈ z :=
  ⟨by grind, fun _ ↦ by ext; grind⟩

@[grind! .]
theorem mem_unorderedPair_left (x y : M) :
    x ∈ unorderedPair x y := by grind

@[grind! .]
theorem mem_unorderedPair_right (x y : M) :
    y ∈ unorderedPair x y := by grind

@[grind =]
theorem unorderedPair_comm [M.Extensional] (x y : M) :
    unorderedPair x y = unorderedPair y x := by
  ext; grind

@[simp]
theorem unorderedPair_ne_empty [M.Extensional] (x y : M) :
    unorderedPair x y ≠ ∅ := by
  simp [ne_empty_iff]

variable (M) in
instance instCommutativeUnodrederPair [M.Extensional] :
  Std.Commutative (α := M) unorderedPair where
  comm := fun x y ↦ unorderedPair_comm x y

theorem unorderedPair_eq_iff₀ [M.Extensional] (x y₁ y₂ : M) :
    unorderedPair x y₁ = unorderedPair x y₂ ↔ y₁ = y₂ := by
  grind

theorem unorderedPair_eq_iff [M.Extensional] (x₁ y₁ x₂ y₂ : M) :
    unorderedPair x₁ y₁ = unorderedPair x₂ y₂ ↔ (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = y₂ ∧ x₂ = y₁) := by
  grind

/-- The ordered pair `(x, y)` -/
noncomputable def orderedPair (x y : M) := ᵣ(ᵣ0, ᵣ1) 〘x, y〙₂
  -- unorderedPair (unorderedPair x x) (unorderedPair x y)

@[inherit_doc] scoped[FirstOrder.Language] notation:max "!(" x ", " y ")" =>
  MemStructure.orderedPair x y

@[grind]
def IsOrderedPair (z : M) := ∃ x y, z = !(x, y)

omit [M.RudClosed] in
@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_orderedPair
    (r₁ r₂ : M.L.RudimentaryTerm n) (xs : Fin n → M) :
    ᵣ(r₁, r₂)〘xs〙 = !(r₁〘xs〙, r₂〘xs〙) := by
  simp [orderedPair, RudimentaryTerm.orderedPair]

omit [M.RudClosed] in
@[grind =]
theorem orderedPair_eq (x y : M) :
   !(x, y) = unorderedPair (unorderedPair x x) (unorderedPair x y) := by
  simp [orderedPair, RudimentaryTerm.orderedPair]

@[simp, grind =]
theorem mem_orderedPair_iff (x y z : M) :
    z ∈ !(x, y) ↔ (z = unorderedPair x x ∨ z = unorderedPair x y) := by
  grind

theorem eq_orderedPair_iff [M.Extensional] (x y z : M) :
    z = orderedPair x y ↔
      (∀ w ∈ z, w = unorderedPair x x ∨ w = unorderedPair x y) ∧
      unorderedPair x x ∈ z ∧ unorderedPair x y ∈ z :=
  ⟨by grind [orderedPair], fun _ ↦ by ext; grind [orderedPair]⟩

@[simp, push, grind =]
theorem orderedPair_eq_orderedPair_iff [M.Extensional] (x₁ y₁ x₂ y₂ : M) :
    !(x₁, y₁) = !(x₂, y₂) ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  grind [orderedPair]

end MemStructure

end FirstOrder.Language
