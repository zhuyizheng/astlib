/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Pair.Basic
/-!
file docstring
-/

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language

instance {L : FirstOrder.Language} [L.HasMem] :
  Union (L.RudimentaryTerm n) := ⟨fun r₁ r₂ => ᵣ⋃₀ ᵣ{r₁, r₂}⟩

@[simp]
theorem castLHom_union (M : MemStructure) (r₁ r₂ : M.L'.RudimentaryTerm n) :
    (r₁ ∪ r₂).castLHom = r₁.castLHom ∪ r₂.castLHom := by
  simp [Union.union]

namespace MemStructure

variable {M : MemStructure} (x y z : M)

variable (M) in
noncomputable instance : Union M := ⟨fun x y ↦ (ᵣ0 ∪ ᵣ1)〘x, y〙₂⟩

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_union
    (r₁ r₂ : M.L.RudimentaryTerm n) (xs : Fin n → M) :
    (r₁ ∪ r₂)〘xs〙 = r₁〘xs〙 ∪ r₂〘xs〙 := by
  simp [Union.union, RudimentaryTerm.realize_sUnion]

@[grind =]
theorem union_eq : x ∪ y = sUnion (unorderedPair x y) := by
  simp only [Union.union, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, sUnion_eq]
  rfl

variable [M.RudClosed]

@[simp, grind =]
theorem mem_union_iff : x ∈ y ∪ z ↔ x ∈ y ∨ x ∈ z := by
  grind

@[grind =]
theorem union_comm [M.Extensional] : x ∪ y = y ∪ x := by
  ext; grind

variable (M) in
instance [M.Extensional] :
  Std.Commutative (α := M) Union.union where
  comm := fun x y ↦ union_comm x y

@[grind =]
theorem union_assoc [M.Extensional] :
    (x ∪ y) ∪ z = x ∪ (y ∪ z) := by
  ext; grind

variable (M) in
instance [M.Extensional] :
  Std.Associative (α := M) Union.union where
  assoc := fun x y z ↦ union_assoc x y z

@[simp, grind =, push]
theorem empty_union [M.Extensional] :
    (∅ : M) ∪ x = x := by
  ext; grind

@[simp, grind =, push]
theorem union_empty [M.Extensional] :
    x ∪ (∅ : M) = x := by
  grind

@[simp, grind =, push]
theorem union_self [M.Extensional] :
    x ∪ x = x := by
  ext; grind

@[grind! .]
theorem left_subset_union :
    x ⊆ x ∪ y := by
  grind

@[grind! .]
theorem right_subset_union :
    y ⊆ x ∪ y := by
  grind

@[simp, grind =]
theorem union_of_subset_right [M.Extensional]
    {x y : M} (h : x ⊆ y) : x ∪ y = y := by
  ext z; simp only [mem_union_iff, or_iff_right_iff_imp]
  exact fun hz ↦ h hz

@[simp, grind =]
theorem union_of_subset_left [M.Extensional]
    {x y : M} (h : y ⊆ x) : x ∪ y = x := by
  ext z; simp only [mem_union_iff, or_iff_left_iff_imp]
  exact fun hz ↦ h hz

@[simp, grind ., push]
theorem union_eq_right_iff_subset [M.Extensional] :
    x ∪ y = y ↔ x ⊆ y := by
  grind

@[simp, grind ., push]
theorem union_eq_left_iff_subset [M.Extensional] :
    x ∪ y = x ↔ y ⊆ x := by
  grind

@[simp, grind ., push]
theorem union_empty_iff [M.Extensional] :
    x ∪ y = ∅ ↔ x = ∅ ∧ y = ∅ := by
  grind

end FirstOrder.Language.MemStructure
