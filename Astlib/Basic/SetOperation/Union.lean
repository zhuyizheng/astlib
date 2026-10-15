/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Pair.Basic
/-!
file docstring
-/

open FirstOrder Language BoundedFormula RudimentaryTerm

namespace FirstOrder.Language

def RudimentaryTerm.union₀ {L : FirstOrder.Language} [L.HasMem] : L.RudimentaryTerm 2 :=
  ᵣ⋃₀ ᵣ{ᵣ0, ᵣ1}

instance {L : FirstOrder.Language} [L.HasMem] :
  Union (L.RudimentaryTerm n) := ⟨fun r₁ r₂ => union₀.substBoundRud ![r₁, r₂]⟩

@[simp]
theorem RudimentaryTerm.union_def {L : FirstOrder.Language} [L.HasMem]
    (r₁ r₂ : L.RudimentaryTerm n) :
    r₁ ∪ r₂ = union₀.substBoundRud ![r₁, r₂] := rfl

instance {L : Language} [L.HasMem] :
  (union₀ : L.RudimentaryTerm 2).CharFree := by
  unfold union₀; infer_instance

instance {L : Language} [L.HasMem]
  (r₁ r₂ : L.RudimentaryTerm n) [r₁.CharFree] [r₂.CharFree] :
  (r₁ ∪ r₂).CharFree := by
  rw [union_def]; infer_instance

namespace MemStructure

variable {L : Language.{u, v}} {M : Type max u v}
  [L.MemStructure M] [Inhabited M] (x : M)
  (x y z : M)

variable (M) in
noncomputable instance : Union M := ⟨fun x y ↦ RudimentaryTerm.union₀〘x, y〙₂⟩

@[grind =]
theorem union_eq : x ∪ y = sUnion (unorderedPair x y) := by
  simp [Union.union, union₀]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_union₀ (xs : Fin 2 → M) :
    union₀〘xs〙 = xs 0 ∪ xs 1 := by
  simp [union_eq, union₀]

variable [RudClosed M]

@[simp, grind =]
theorem mem_union_iff : x ∈ y ∪ z ↔ x ∈ y ∨ x ∈ z := by
  grind

@[grind =]
theorem union_comm [Extensional M] : x ∪ y = y ∪ x := by
  ext; grind

variable (M) in
instance [Extensional M] :
  Std.Commutative (α := M) Union.union where
  comm := fun x y ↦ union_comm x y

@[grind =]
theorem union_assoc [Extensional M] :
    (x ∪ y) ∪ z = x ∪ (y ∪ z) := by
  ext; grind

variable (M) in
instance [Extensional M] :
  Std.Associative (α := M) Union.union where
  assoc := fun x y z ↦ union_assoc x y z

@[simp, grind =, push]
theorem empty_union [Extensional M] :
    (∅ : M) ∪ x = x := by
  ext; grind

@[simp, grind =, push]
theorem union_empty [Extensional M] :
    x ∪ (∅ : M) = x := by
  grind

@[simp, grind =, push]
theorem union_self [Extensional M] :
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
theorem union_of_subset_right [Extensional M]
    {x y : M} (h : x ⊆ y) : x ∪ y = y := by
  ext z; simp only [mem_union_iff, or_iff_right_iff_imp]
  exact fun hz ↦ h hz

@[simp, grind =]
theorem union_of_subset_left [Extensional M]
    {x y : M} (h : y ⊆ x) : x ∪ y = x := by
  ext z; simp only [mem_union_iff, or_iff_left_iff_imp]
  exact fun hz ↦ h hz

@[simp, grind ., push]
theorem union_eq_right_iff_subset [Extensional M] :
    x ∪ y = y ↔ x ⊆ y := by
  grind

@[simp, grind ., push]
theorem union_eq_left_iff_subset [Extensional M] :
    x ∪ y = x ↔ y ⊆ x := by
  grind

@[simp, grind ., push]
theorem union_empty_iff [Extensional M] :
    x ∪ y = ∅ ↔ x = ∅ ∧ y = ∅ := by
  grind

end FirstOrder.Language.MemStructure
