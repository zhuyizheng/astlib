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

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r : L.RudimentaryTerm n) [r.CharFree] :
  r.isOrderedPair.RelFree := by
  unfold isOrderedPair; infer_instance


-- noncomputable abbrev isOrderedPair1 {M : MemStructure} (r : L.RudimentaryTerm n) :
--   L.BoundedFormula' n :=
--   r.isOrderedPair.castLHom.toBoundedFormula

@[simp]
theorem realize_isOrderedPair (r : L.RudimentaryTerm n) [r.CharFree] (xs : Fin n → M) :
    r.isOrderedPair.toBoundedFormula 〘xs〙 ↔ IsOrderedPair (r〘xs〙 : M) := by
  simp only [isOrderedPair, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    IsOrderedPair]
  rw [DeltaZeroBoundedFormula.realize_substBoundRud]
  suffices (∃ a ∈ ⋃₀ (r〘xs〙 : M), ∃ a_1 ∈ ⋃₀ (r〘xs〙 : M), r〘xs〙 = !(a, a_1)) ↔ ∃ x y, r〘xs〙 = !(x, y) by
    simpa [isOrderedPair, IsOrderedPair, Fin.snoc_nat]
  grind

end RudimentaryTerm

noncomputable def RudimentaryTerm.left₀ {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
  L.RudimentaryTerm 1 :=
  ᵣ⋃₀ (∃₀∈ &2 ((&0 =₀ &1).substBoundRud ![ᵣ1, ᵣ(ᵣ0, ᵣ3)])
    |>.comprehensionRudimentaryTerm |>.substBoundRud ![ᵣ0, ᵣ⋃₀ ᵣ0, ᵣ⋃₀ ᵣ0])

@[simp]
noncomputable def RudimentaryTerm.left {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r : L.RudimentaryTerm n) :
  L.RudimentaryTerm n :=
  left₀.substBoundRud ![r]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
  (left₀ : L.RudimentaryTerm 1).CharFree := by
  unfold left₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r : L.RudimentaryTerm n) [r.CharFree] : r.left.CharFree := by
  unfold RudimentaryTerm.left; infer_instance



@[simp]
theorem RudimentaryTerm.realize_left₀ (xs : Fin 1 → M) :
    left₀〘xs〙 = MemStructure.left (xs 0) := by
  obtain ⟨a, rfl⟩ : ∃ a, xs = ![a] := ⟨xs 0, by ext i; fin_cases i; rfl⟩
  simp only [RudimentaryTerm.left₀, Nat.succ_eq_add_one, Nat.reduceAdd, isValue,
    Function.comp_apply, RudimentaryTerm.sUnion, realize_substBoundRud, Matrix.cons_val_fin_one,
    realize_sUnion₀]
  by_cases h : IsOrderedPair a
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
    suffices ∀ x ∈ a, z ∈ x → ∀ (x x_1 : M), x_1 ∈ a → x ∈ x_1 → ¬a = !(z, x) by
      simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
    grind [IsOrderedPair]

noncomputable def RudimentaryTerm.right₀ {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
  L.RudimentaryTerm 1 :=
  ᵣ⋃₀ (∃₀∈ &2 ((&0 =₀ &1).substBoundRud ![ᵣ1, ᵣ(ᵣ3, ᵣ0)])
    |>.comprehensionRudimentaryTerm |>.substBoundRud ![ᵣ0, ᵣ⋃₀ ᵣ0, ᵣ⋃₀ ᵣ0])

@[simp]
noncomputable def RudimentaryTerm.right {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r : L.RudimentaryTerm n) :=
  right₀.substBoundRud ![r]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
  (right₀ : L.RudimentaryTerm 1).CharFree := by
  unfold right₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r : L.RudimentaryTerm n) [r.CharFree] : r.right.CharFree := by
  unfold RudimentaryTerm.right; infer_instance


@[simp]
theorem RudimentaryTerm.realize_right₀ (xs : Fin 1 → M) :
    right₀〘xs〙 = MemStructure.right (xs 0) := by
  obtain ⟨a, rfl⟩ : ∃ a, xs = ![a] := ⟨xs 0, by ext i; fin_cases i; rfl⟩
  simp only [RudimentaryTerm.right₀, Nat.succ_eq_add_one, Nat.reduceAdd, isValue,
    Function.comp_apply, RudimentaryTerm.sUnion, realize_substBoundRud, Matrix.cons_val_fin_one,
    realize_sUnion₀]
  by_cases h : IsOrderedPair a
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
    suffices ∀ x ∈ a, z ∈ x → ∀ (x x_1 : M), x_1 ∈ a → x ∈ x_1 → ¬a = !(x, z) by
      simpa [snoc_nat, cons_nat, init_def, RudimentaryTerm.sUnion]
    grind [IsOrderedPair]

namespace DeltaZeroBoundedFormula

/-- Substituting the left component of the last variable -/
theorem realize_substBoundRud_snoc_left (φ : L.DeltaZeroBoundedFormula (n + 1))
    [φ.RelFree] (xs : Fin n → M) (p : M) :
    (φ.substBoundRud (snoc (fun i ↦ ᵣi.castSucc) (ᵣ-1).left)).toBoundedFormula〘snoc xs p〙 ↔
    φ.toBoundedFormula〘snoc xs (left p)〙 := by
  rw [realize_substBoundRud]
  apply iff_of_eq
  congr 1
  funext i
  revert i
  simp [Fin.forall_iff_castSucc]

/-- Substituting the right component of the last variable -/
theorem realize_substBoundRud_snoc_right (φ : L.DeltaZeroBoundedFormula (n + 1))
    [φ.RelFree] (xs : Fin n → M) (p : M) :
    (φ.substBoundRud (snoc (fun i ↦ ᵣi.castSucc) (ᵣ-1).right)).toBoundedFormula〘snoc xs p〙 ↔
    φ.toBoundedFormula〘snoc xs (right p)〙 := by
  rw [realize_substBoundRud]
  apply iff_of_eq
  congr 1
  funext i
  revert i
  simp [Fin.forall_iff_castSucc]

/-- Substituting the left and right components of the last variable -/
theorem realize_substBoundRud_snoc_left_right (φ : L.DeltaZeroBoundedFormula (n + 2))
    [φ.RelFree] (xs : Fin n → M) (p : M) :
    (φ.substBoundRud (snoc (snoc (fun i ↦ ᵣi.castSucc) (ᵣ-1).left)
      (ᵣ-1).right)).toBoundedFormula〘snoc xs p〙 ↔
    φ.toBoundedFormula〘snoc (snoc xs (left p)) (right p)〙 := by
  rw [realize_substBoundRud]
  apply iff_of_eq
  congr 1
  funext i
  revert i
  simp [Fin.forall_iff_castSucc]

end DeltaZeroBoundedFormula

end FirstOrder.Language
