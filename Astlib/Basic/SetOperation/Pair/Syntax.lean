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

@[simp]
theorem realize_left_of_not_isOrderedPair {r : L.RudimentaryTerm n} {xs : Fin n → M}
    (h : ¬IsOrderedPair (r〘xs〙 : M)) :
    r.left〘xs〙 = ∅ := by
  simp only [left, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    realize_substBoundRud, Matrix.cons_val_fin_one, realize_sUnion]
  convert sUnion_empty (M := M)
  ext z
  suffices ∀ x ∈ r〘xs〙, z ∈ x → ∀ (x x_1 : M), x_1 ∈ r〘xs〙 → x ∈ x_1 → ¬r〘xs〙 = !(z, x) by
    simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
  grind [IsOrderedPair]

@[simp]
theorem realize_left {x y : M} {r : L.RudimentaryTerm n} {xs : Fin n → M}
    (h : r〘xs〙 = !(x, y)) :
    r.left〘xs〙 = x := by
  simp only [left, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    realize_substBoundRud, Matrix.cons_val_fin_one, h, realize_sUnion]
  convert sUnion_singleton x
  ext z
  suffices (z = x ∨ z = y) ∧ (x = z ∧ y = x ∨ x = z) ↔ z = x by
    simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
  tauto

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

@[simp]
theorem realize_right_of_not_isOrderedPair {r : L.RudimentaryTerm n} {xs : Fin n → M}
    (h : ¬IsOrderedPair (r〘xs〙 : M)) :
    r.right〘xs〙 = ∅ := by
  simp only [right, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    realize_substBoundRud, Matrix.cons_val_fin_one, realize_sUnion]
  convert sUnion_empty (M := M)
  ext z
  suffices ∀ x ∈ r〘xs〙, z ∈ x → ∀ (x x_1 : M), x_1 ∈ r〘xs〙 → x ∈ x_1 → ¬r〘xs〙 = !(x, z) by
    simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
  grind [IsOrderedPair]

@[simp]
theorem realize_right {x y : M} {r : L.RudimentaryTerm n} {xs : Fin n → M}
    (h : r〘xs〙 = !(x, y)) :
    r.right〘xs〙 = y := by
  simp only [right, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    realize_substBoundRud, Matrix.cons_val_fin_one, h, realize_sUnion]
  convert sUnion_singleton y
  ext z
  suffices (z = x ∨ z = y) ∧ (y = z ∨ x = y ∧ y = z) ↔ z = y by
    simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
  tauto

end FirstOrder.Language
