/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Comprehension
/-!
file docstring
-/

open FirstOrder Language BoundedFormula MemStructure RudimentaryTerm Fin

namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type max u v}
  [L.MemStructure M] [Inhabited M] [L.ExtraConstantsUnaryRelationsOnly]
  [RudClosed M] [Extensional M]

namespace RudimentaryTerm

noncomputable def isOrderedPair {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r : L.RudimentaryTerm n) :
  L.DeltaZeroBoundedFormula n :=
  ∃₀∈ &0 ∃₀∈ &0 ((&0 =₀ &1).substBoundRud ![ᵣ1, ᵣ(ᵣ2, ᵣ3)]) |>.substBoundRud ![ᵣ⋃₀ r, r]

@[simp]
theorem isRelFree_isOrderedPair {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r : L.RudimentaryTerm n)
    (hr : r.IsCharFree) :
    r.isOrderedPair.IsRelFree := by
  simp only [isOrderedPair, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply]
  apply DeltaZeroBoundedFormula.isRelFree_substBoundRud <;> simp [hr]


-- noncomputable abbrev isOrderedPair1 {M : MemStructure} (r : L.RudimentaryTerm n) :
--   L.BoundedFormula' n :=
--   r.isOrderedPair.castLHom.toBoundedFormula

@[simp]
theorem realize_isOrderedPair (r : L.RudimentaryTerm n)
    (hr : r.IsCharFree) (xs : Fin n → M) :
    r.isOrderedPair.toBoundedFormula 〘xs〙 ↔ IsOrderedPair (r〘xs〙 : M) := by
  simp only [isOrderedPair, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    IsOrderedPair]
  rw [DeltaZeroBoundedFormula.realize_substBoundRud (hφ := by simp) (hrs := by simp [hr])]
  suffices (∃ a ∈ ⋃₀ (r〘xs〙 : M), ∃ a_1 ∈ ⋃₀ (r〘xs〙 : M), r〘xs〙 = !(a, a_1)) ↔ ∃ x y, r〘xs〙 = !(x, y) by
    simpa [isOrderedPair, IsOrderedPair, Fin.snoc_nat, realize_sUnion]
  grind

end RudimentaryTerm

noncomputable def RudimentaryTerm.left {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r : L.RudimentaryTerm n) :
  L.RudimentaryTerm n :=
  ᵣ⋃₀ (∃₀∈ &2 ((&0 =₀ &1).substBoundRud ![ᵣ1, ᵣ(ᵣ0, ᵣ3)])
    |>.comprehensionRudimentaryTerm |>.substBoundRud ![ᵣ0, ᵣ⋃₀ ᵣ0, ᵣ⋃₀ ᵣ0])
    |>.substBoundRud ![r]

@[simp]
theorem isCharFree_left {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r : L.RudimentaryTerm n)
    (hr : r.IsCharFree) :
    r.left.IsCharFree := by
  simp only [left, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply]
  apply isCharFree_sUnion
  simp only [Nat.reduceAdd, reduceLast, isValue, Matrix.cons_val_fin_one, isCharFree_iUnion]
  constructor
  · apply isCharFree_sUnion
    exact hr
  · apply isCharFree_substBoundRud
    · apply isCharFree_substBoundRud
      · apply isCharFree_ifTrue <;> simp
      · intro i; fin_cases i <;> simp [snoc_nat]
    · intro i; fin_cases i <;> simp [snoc_nat, hr]

noncomputable instance (a : M) : Decidable (∃ x y, a = !(x, y)) := by exact Classical.propDecidable _

noncomputable def MemStructure.left (a : M) : M := dite (∃ x y, a = !(x, y)) Classical.choose fun _ ↦ ∅

@[simp]
theorem left_of_not_isOrderedPair {a : M} (ha : ¬IsOrderedPair a) :
    left a = ∅ := by
  have : ¬∃ x y, a = !(x, y) := by grind
  simp [MemStructure.left, this]

@[simp]
theorem left_orderedPair {a b : M} :
    left !(a, b) = a := by
  simp [MemStructure.left]


@[simp]
theorem realize_left {r : L.RudimentaryTerm n} {xs : Fin n → M} :
    r.left〘xs〙 = left (r〘xs〙 : M) := by
  simp only [RudimentaryTerm.left, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    realize_substBoundRud, Matrix.cons_val_fin_one, realize_sUnion]
  by_cases h : IsOrderedPair (r〘xs〙 : M)
  · obtain ⟨x, y, hxy⟩ := h
    simp only [isValue, hxy, left_orderedPair]
    convert sUnion_singleton x
    ext z
    suffices (z = x ∨ z = y) ∧ (x = z ∧ y = x ∨ x = z) ↔ z = x by
      simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
    tauto
  · simp only [isValue, h, not_false_eq_true, left_of_not_isOrderedPair]
    convert sUnion_empty (M := M)
    ext z
    suffices ∀ x ∈ r〘xs〙, z ∈ x → ∀ (x x_1 : M), x_1 ∈ r〘xs〙 → x ∈ x_1 → ¬r〘xs〙 = !(z, x) by
      simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
    grind [IsOrderedPair]

noncomputable def RudimentaryTerm.right  {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r : L.RudimentaryTerm n) :=
  ᵣ⋃₀ (∃₀∈ &2 ((&0 =₀ &1).substBoundRud ![ᵣ1, ᵣ(ᵣ3, ᵣ0)])
    |>.comprehensionRudimentaryTerm |>.substBoundRud ![ᵣ0, ᵣ⋃₀ ᵣ0, ᵣ⋃₀ ᵣ0])
    |>.substBoundRud ![r]

@[simp]
theorem isCharFree_right {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r : L.RudimentaryTerm n)
    (hr : r.IsCharFree) :
    r.right.IsCharFree := by
  simp only [right, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply]
  apply isCharFree_sUnion
  simp only [Nat.reduceAdd, reduceLast, isValue, Matrix.cons_val_fin_one, isCharFree_iUnion]
  constructor
  · apply isCharFree_sUnion
    exact hr
  · apply isCharFree_substBoundRud
    · apply isCharFree_substBoundRud
      · apply isCharFree_ifTrue <;> simp
      · intro i; fin_cases i <;> simp [snoc_nat]
    · intro i; fin_cases i <;> simp [snoc_nat, hr]

noncomputable instance (a : M) : Decidable (∃ y x, a = !(x, y)) := by exact Classical.propDecidable _

noncomputable def MemStructure.right (a : M) : M := dite (∃ y x, a = !(x, y)) Classical.choose fun _ ↦ ∅

@[simp]
theorem right_of_not_isOrderedPair {a : M} (ha : ¬IsOrderedPair a) :
    right a = ∅ := by
  have : ¬∃ y x, a = !(x, y) := by grind
  simp [MemStructure.right, this]

@[simp]
theorem right_orderedPair {a b : M} :
    right !(a, b) = b := by
  simp [MemStructure.right]

@[simp]
theorem realize_right {r : L.RudimentaryTerm n} {xs : Fin n → M} :
    r.right〘xs〙 = right (r〘xs〙 : M) := by
  simp only [RudimentaryTerm.right, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    realize_substBoundRud, Matrix.cons_val_fin_one, realize_sUnion]
  by_cases h : IsOrderedPair (r〘xs〙 : M)
  · obtain ⟨x, y, hxy⟩ := h
    simp only [isValue, hxy, right_orderedPair]
    convert sUnion_singleton y
    ext z
    suffices (z = x ∨ z = y) ∧ (y = z ∨ x = y ∧ y = z) ↔ z = y by
      simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
    tauto
  · simp only [isValue, h, not_false_eq_true, right_of_not_isOrderedPair]
    convert sUnion_empty (M := M)
    ext z
    suffices ∀ x ∈ r〘xs〙, z ∈ x → ∀ (x x_1 : M), x_1 ∈ r〘xs〙 → x ∈ x_1 → ¬r〘xs〙 = !(x, z) by
      simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
    grind [IsOrderedPair]

end FirstOrder.Language
