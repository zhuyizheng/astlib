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


variable {L : Language} [L.HasMem] {M : MemStructure}
  [M.Extensional] [M.RudClosed]

variable {L' : Language} [L'.HasMem] [L'.ExtraConstantsOnly]

namespace RudimentaryTerm

noncomputable def isOrderedPair (r : L'.RudimentaryTerm n) :
  L'.DeltaZeroBoundedFormula n :=
  ∃₀∈ &0 ∃₀∈ &0 ((&0 =₀ &1).substBoundRud ![ᵣ1, ᵣ(ᵣ2, ᵣ3)]) |>.substBoundRud ![ᵣ⋃₀ r, r]

-- noncomputable abbrev isOrderedPair1 {M : MemStructure} (r : M.L'.RudimentaryTerm n) :
--   M.L.BoundedFormula' n :=
--   r.isOrderedPair.castLHom.toBoundedFormula

@[simp]
theorem realize_isOrderedPair (r : M.L'.RudimentaryTerm n) (xs : Fin n → M) :
    r.isOrderedPair.castLHom.toBoundedFormula 〘xs〙 ↔ IsOrderedPair (r.castLHom〘xs〙) := by
  suffices (∃ a ∈ ⋃₀ r.castLHom〘xs〙, ∃ a_1 ∈ ⋃₀ r.castLHom〘xs〙, r.castLHom〘xs〙 = !(a, a_1)) ↔ ∃ x y, r.castLHom〘xs〙 = !(x, y) by
    simpa [isOrderedPair, IsOrderedPair, Fin.snoc_nat, realize_sUnion]
  grind

end RudimentaryTerm

noncomputable def RudimentaryTerm.left (r : L'.RudimentaryTerm n) : L'.RudimentaryTerm n :=
  ᵣ⋃₀ (∃₀∈ &2 ((&0 =₀ &1).substBoundRud ![ᵣ1, ᵣ(ᵣ0, ᵣ3)])
    |>.comprehensionRudimentaryTerm |>.substBoundRud ![ᵣ0, ᵣ⋃₀ ᵣ0, ᵣ⋃₀ ᵣ0])
    |>.substBoundRud ![r]

variable [M.L.ExtraConstantsUnaryRelationsOnly]

@[simp]
theorem realize_left_of_not_isOrderedPair {r : M.L'.RudimentaryTerm n} {xs : Fin n → M}
    (h : ¬IsOrderedPair r.castLHom〘xs〙) :
    r.left.castLHom〘xs〙 = ∅ := by
  simp only [left, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    castLHom_substBoundRud, castLHom_sUnion,
    DeltaZeroBoundedFormula.castLHom_comprehensionRudimentaryTerm,
    DeltaZeroBoundedFormula.castLHom_exMem, Term.castLHom_var', Matrix.cons_val_fin_one,
    realize_substBoundRud, realize_sUnion]
  convert sUnion_empty (M := M)
  ext z
  set s := r.castLHom
  suffices ∀ x ∈ s〘xs〙, z ∈ x → ∀ (x x_1 : M), x_1 ∈ s〘xs〙 → x ∈ x_1 → ¬s〘xs〙 = !(z, x) by
    simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
  grind [IsOrderedPair]

@[simp]
theorem realize_left {x y : M} {r : M.L'.RudimentaryTerm n} {xs : Fin n → M}
    (h : r.castLHom〘xs〙 = !(x, y)) :
    r.left.castLHom〘xs〙 = x := by
  simp only [left, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    castLHom_substBoundRud, castLHom_sUnion,
    DeltaZeroBoundedFormula.castLHom_comprehensionRudimentaryTerm,
    DeltaZeroBoundedFormula.castLHom_exMem, Term.castLHom_var', Matrix.cons_val_fin_one,
    realize_substBoundRud, h, realize_sUnion]
  convert sUnion_singleton x
  ext z
  suffices (z = x ∨ z = y) ∧ (x = z ∧ y = x ∨ x = z) ↔ z = x by
    simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
  tauto

noncomputable def RudimentaryTerm.right (r : L'.RudimentaryTerm n) : L'.RudimentaryTerm n :=
  ᵣ⋃₀ (∃₀∈ &2 ((&0 =₀ &1).substBoundRud ![ᵣ1, ᵣ(ᵣ3, ᵣ0)])
    |>.comprehensionRudimentaryTerm |>.substBoundRud ![ᵣ0, ᵣ⋃₀ ᵣ0, ᵣ⋃₀ ᵣ0])
    |>.substBoundRud ![r]

@[simp]
theorem realize_right_of_not_isOrderedPair {r : M.L'.RudimentaryTerm n} {xs : Fin n → M}
    (h : ¬IsOrderedPair r.castLHom〘xs〙) :
    r.right.castLHom〘xs〙 = ∅ := by
  simp only [right, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    castLHom_substBoundRud, castLHom_sUnion,
    DeltaZeroBoundedFormula.castLHom_comprehensionRudimentaryTerm,
    DeltaZeroBoundedFormula.castLHom_exMem, Term.castLHom_var', Matrix.cons_val_fin_one,
    realize_substBoundRud, realize_sUnion]
  convert sUnion_empty (M := M)
  ext z
  set s := r.castLHom
  suffices ∀ x ∈ s〘xs〙, z ∈ x → ∀ (x x_1 : M), x_1 ∈ s〘xs〙 → x ∈ x_1 → ¬s〘xs〙 = !(x, z) by
    simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
  grind [IsOrderedPair]

@[simp]
theorem realize_right {x y : M} {r : M.L'.RudimentaryTerm n} {xs : Fin n → M}
    (h : r.castLHom〘xs〙 = !(x, y)) :
    r.right.castLHom〘xs〙 = y := by
  simp only [right, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    castLHom_substBoundRud, castLHom_sUnion,
    DeltaZeroBoundedFormula.castLHom_comprehensionRudimentaryTerm,
    DeltaZeroBoundedFormula.castLHom_exMem, Term.castLHom_var', Matrix.cons_val_fin_one,
    realize_substBoundRud, h, realize_sUnion]
  convert sUnion_singleton y
  ext z
  suffices (z = x ∨ z = y) ∧ (y = z ∨ x = y ∧ y = z) ↔ z = y by
    simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
  tauto

end FirstOrder.Language
