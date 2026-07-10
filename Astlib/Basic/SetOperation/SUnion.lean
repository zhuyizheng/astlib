/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.ModelTheory.Semantics
import Astlib.Basic.SetOperation.Empty
/-!
file docstring
-/

open FirstOrder.Language.BoundedFormula Fin

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y a : M)

def IsSUnion (a x : M) := ∀ y, y ∈ a ↔ (∃ z ∈ x, y ∈ z)

noncomputable instance : Decidable (∃ a : M, IsSUnion a x) :=
  Classical.propDecidable _

/-- `⋃ x` in set theory, denoted by `⋃₀ x` in lean -/
noncomputable def sUnion (x : M) :=
  dite (∃ a : M, IsSUnion a x) Classical.choose default

@[inherit_doc] prefix:110 "⋃₀ " => sUnion

variable (M) in
/- `M` is closed under `⋃` -/
class ClosedUnderSUnion : Prop where
  protected closedUnderSUnion (x : M) : ∃ a : M, IsSUnion a x

@[grind =]
theorem mem_sUnion_iff [hM : M.ClosedUnderSUnion] : x ∈ ⋃₀ a ↔ ∃ y ∈ a, x ∈ y := by
  convert Classical.choose_spec (hM.closedUnderSUnion a) x
  simp [sUnion, ClosedUnderSUnion.closedUnderSUnion]

theorem eq_sUnion_iff [M.Extensional] [M.ClosedUnderSUnion] : x = ⋃₀ a ↔
    (∀ z ∈ x, ∃ y ∈ a, z ∈ y) ∧ ∀ y ∈ a, ∀ z ∈ y, z ∈ x :=
  ⟨by grind, fun _ ↦ by ext; grind⟩

@[simp, grind! ., push]
theorem sUnion_empty [M.Extensional] [M.HasEmpty] [M.ClosedUnderSUnion] : ⋃₀ (∅ : M) = ∅ := by
  ext; grind

theorem sUnion_mono [M.HasEmpty] [M.ClosedUnderSUnion] {x y : M} (h : x ⊆ y) : ⋃₀ x ⊆ ⋃₀ y := by
  intro z
  simp only [mem_sUnion_iff]
  exact fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, h hw₁, hw₂⟩

end MemStructure

section Syntax

variable {α : Type*} {n : ℕ} {M : MemStructure}
  {L : FirstOrder.Language} [HasMem L] (t₁ t₂ : L.Term (α ⊕ Fin n))
  (v : α → M) (xs : Fin n → M)

/-- `∀ x ∈ ⋃₀ t, φ (..., x)` -/
def BoundedFormula.allMemSUnion
  (t : L.Term (α ⊕ Fin n)) (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  ∀'∈ t ∀'∈ &-1 (φ.liftAt 1 n)

notation "∀'∈⋃₀ " x:arg y:50 => FirstOrder.Language.BoundedFormula.allMemSUnion x y

theorem BoundedFormula.isDeltaZero_allMemSUnion (t : L.Term (α ⊕ Fin n))
    (φ : L.BoundedFormula α (n + 1)) [φ.DeltaZero] : (∀'∈⋃₀ t φ).IsDeltaZero := by
  simp only [allMemSUnion]
  exact DeltaZero.isDeltaZero

instance (t : L.Term (α ⊕ Fin n)) (φ : L.BoundedFormula α (n + 1)) [φ.DeltaZero] :
  (∀'∈⋃₀ t φ).DeltaZero := ⟨φ.isDeltaZero_allMemSUnion t⟩

@[simp]
theorem realize_allMemSUnion {M : MemStructure} [M.ClosedUnderSUnion]
    (t : M.L.Term (α ⊕ Fin n)) (φ : M.L.BoundedFormula α (n + 1))
    {v : α → M} {xs : Fin n → M} :
    (∀'∈⋃₀t φ)〘v, xs〙 ↔ ∀ a ∈ ⋃₀(t〘v, xs〙), φ〘v, snoc xs a〙 := by
  simp only [allMemSUnion, Function.comp_apply, realize_allMem, Term.realize'_var', snoc_last,
    le_add_iff_nonneg_right, _root_.zero_le, realize_liftAt, addNat_one, snoc_snoc_comp_gap_one,
    MemStructure.mem_sUnion_iff, forall_exists_index, and_imp]
  tauto

/-- `∃ x ∈ ⋃₀ t, φ (..., x)` -/
def BoundedFormula.exMemSUnion
  (t : L.Term (α ⊕ Fin n)) (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  ∃'∈ t ∃'∈ &-1 (φ.liftAt 1 n)

notation "∃'∈⋃₀ " x:arg y:50 => FirstOrder.Language.BoundedFormula.exMemSUnion x y


theorem BoundedFormula.isDeltaZero_exMemSUnion (t : L.Term (α ⊕ Fin n))
    (φ : L.BoundedFormula α (n + 1)) [φ.DeltaZero] : (∃'∈⋃₀ t φ).IsDeltaZero := by
  simp only [exMemSUnion]
  exact DeltaZero.isDeltaZero

instance (t : L.Term (α ⊕ Fin n)) (φ : L.BoundedFormula α (n + 1)) [φ.DeltaZero] :
  (∃'∈⋃₀ t φ).DeltaZero := ⟨φ.isDeltaZero_exMemSUnion t⟩

@[simp]
theorem realize_exMemSUnion {M : MemStructure} [M.ClosedUnderSUnion]
    (t : M.L.Term (α ⊕ Fin n)) (φ : M.L.BoundedFormula α (n + 1))
    {v : α → M} {xs : Fin n → M} :
    (∃'∈⋃₀t φ)〘v, xs〙 ↔ ∃ a ∈ ⋃₀(t〘v, xs〙), φ〘v, snoc xs a〙 := by
  simp only [exMemSUnion, Function.comp_apply, realize_exMem, Term.realize'_var', snoc_last,
    le_add_iff_nonneg_right, _root_.zero_le, realize_liftAt, addNat_one, snoc_snoc_comp_gap_one,
    MemStructure.mem_sUnion_iff]
  tauto

/-- `t₁ ∈ ⋃₀ t₂` -/
def Term.memSUnion := ∃'∈ t₂ t₁.castSucc ∈' &-1

theorem Term.isDeltaZero_memSUnion : (t₁.memSUnion t₂).IsDeltaZero := by
  simp only [memSUnion]
  exact DeltaZero.isDeltaZero

instance : (t₁.memSUnion t₂).DeltaZero := ⟨t₁.isDeltaZero_memSUnion t₂⟩

/-- `t₁ = ⋃₀ t₂` -/
def Term.eqSUnion :=
  (∀'∈ t₁ (&-1).memSUnion t₂.castSucc) ⊓ ∀'∈⋃₀ t₂ (&-1 ∈' t₁.castSucc)

theorem Term.isDeltaZero_eqSUnion : (t₁.eqSUnion t₂).IsDeltaZero := by
  simp only [eqSUnion]
  exact DeltaZero.isDeltaZero

instance : (t₁.eqSUnion t₂).DeltaZero := ⟨t₁.isDeltaZero_eqSUnion t₂⟩

variable (v : α → M) (xs : Fin n → M) (t₁ t₂ : M.L.Term (α ⊕ Fin n))

@[simp]
theorem Term.memSUnion_iff [M.ClosedUnderSUnion] : (t₁.memSUnion t₂)〘v, xs〙 ↔
    t₁〘v, xs〙 ∈ ⋃₀ t₂〘v, xs〙 := by
  simp [memSUnion, MemStructure.mem_sUnion_iff]

@[simp]
theorem Term.eqSUnion_iff [M.Extensional] [M.ClosedUnderSUnion] :
    (t₁.eqSUnion t₂)〘v, xs〙 ↔ t₁〘v, xs〙 = ⋃₀ t₂〘v, xs〙 := by
  simp only [eqSUnion, Function.comp_apply, castSucc, Nat.succ_eq_add_one, realize_inf,
    realize_allMem, memSUnion_iff, realize'_castLE, castLE_succ_castSucc, snoc_comp_castSucc,
    realize'_var', snoc_last, realize_allMemSUnion, MemStructure.realize_mem, MemStructure.ext_iff]
  grind

end Syntax

end FirstOrder.Language
