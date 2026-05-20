import Mathlib
import Mathlib.ModelTheory.Semantics

import Astlib.Basic.SetOperation.Empty

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y a : M)

variable (M) in
/- `M` is closed under `⋃` -/
class ClosedUnderSUnion where
  /-- `⋃ x` in set theory, denoted by `⋃₀ x` in lean -/
  sUnion : M → M
  protected sUnion_prop : ∀ x y : M, y ∈ sUnion x ↔ (∃ z ∈ x, y ∈ z)

export ClosedUnderSUnion (sUnion)

@[inherit_doc] prefix:110 "⋃₀ " => sUnion

@[simp, grind =, push]
theorem mem_sUnion_iff [M.ClosedUnderSUnion] : x ∈ ⋃₀ a ↔ ∃ y ∈ a, x ∈ y :=
  ClosedUnderSUnion.sUnion_prop _ _

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

variable {L : FirstOrder.Language} [HasMem L] (t₁ t₂ : L.Term (α ⊕ Fin n))
  (v : α → M) (xs : Fin n → M)

/-- `t₁ ∈ ⋃₀ t₂` -/
abbrev Term.memSUnion :=
  ∃'∈ t₂ t₁.castSucc ∈' &-1

/-- `t₁ = ⋃₀ t₂` -/
abbrev Term.eqSUnion :=
  (∀'∈ t₁ (&-1).memSUnion t₂.castSucc) ⊓ ∀'∈ t₂ ∀'∈ &-1 (&-1 ∈' t₁.castSucc.castSucc)

/-- Every set has a union -/
def allExSUnion : L.Sentence := ∀' ∃' (&1).eqSUnion &0

variable {M : MemStructure} (v : α → M) (xs : Fin n → M)

noncomputable instance (hM : M ⊨ M.L.allExSUnion) : M.ClosedUnderSUnion where
  sUnion x := Classical.choose (exists_of_ex (realize_all.mp hM x))
  sUnion_prop := fun x ↦ by
    have := Classical.choose_spec (exists_of_ex (realize_all.mp hM x))
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_inf,
      Fin.reduceLast, Term.castSucc, Term.castLE_var_inr, Fin.castLE_zero, realize_all,
      Fin.reduceCastLE, realize_imp, MemStructure.realize_mem, Term.realize_var, Sum.elim_inr,
      Fin.snoc, Fin.coe_ofNat_eq_mod, Nat.one_mod, Order.lt_two_iff, Std.le_refl, ↓reduceDIte,
      Fin.reduceCastLT, Fin.castSucc_one, Nat.mod_succ, lt_self_iff_false, cast_eq, realize_not,
      Nat.zero_mod, Nat.ofNat_pos, Fin.castSucc_zero, zero_le, Order.lt_one_iff,
      Nat.reduceMod, Nat.lt_add_one, Fin.reduceCastSucc, not_forall, not_not,
      Nat.one_lt_ofNat] at this ⊢
    grind

variable (t₁ t₂ : M.L.Term (α ⊕ Fin n))

@[simp 1100]
theorem Term.memSUnion_iff : (t₁.memSUnion t₂).Realize v xs ↔
      ∃ y ∈ t₂.realize (Sum.elim v xs), t₁.realize (Sum.elim v xs) ∈ y := by
  simp only [realize_not, Term.castSucc, Nat.succ_eq_add_one, Function.comp_apply, realize_all,
    realize_imp, MemStructure.realize_mem, Term.realize_castLE, Fin.castLE_succ_castSucc,
    Sum.elim_comp_map, CompTriple.comp_eq, Fin.snoc_comp_castSucc, Term.realize_var, Sum.elim_inr,
    Fin.snoc_last, not_forall, not_not]
  congr!; grind [Fin.snoc_nat]

@[simp 1100]
theorem Term.eqSUnion_iff [M.Extensional] [M.ClosedUnderSUnion] : (t₁.eqSUnion t₂).Realize v xs ↔
      t₁.realize (Sum.elim v xs) = ⋃₀ t₂.realize (Sum.elim v xs) := by
  simp only [realize_inf, Function.comp_apply, Term.castSucc, Nat.succ_eq_add_one, realize_all,
    realize_imp, MemStructure.realize_mem, Term.realize_castLE, Fin.castLE_succ_castSucc,
    Sum.elim_comp_map_castSucc, Term.realize_var, Sum.elim_inr, Fin.snoc_last, realize_not,
    Term.castLE_var_inr, Term.castLE_castLE, Fin.snoc_castSucc, not_forall,
    not_not]
  simp only [exists_prop, M.eq_sUnion_iff]
  congr! <;> grind [Fin.snoc_nat]

end FirstOrder.Language
