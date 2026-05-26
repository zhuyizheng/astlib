import Astlib.ModelTheory.Semantics

import Astlib.Basic.SetOperation.Empty

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y a : M)

noncomputable instance : Decidable (∃ a : M, ∀ y, y ∈ a ↔ (∃ z ∈ x, y ∈ z)) :=
  Classical.propDecidable _

/-- `⋃ x` in set theory, denoted by `⋃₀ x` in lean -/
noncomputable def sUnion (x : M) :=
  dite (∃ a : M, ∀ y, y ∈ a ↔ (∃ z ∈ x, y ∈ z)) Classical.choose default

@[inherit_doc] prefix:110 "⋃₀ " => sUnion

variable (M) in
/- `M` is closed under `⋃` -/
class ClosedUnderSUnion : Prop where
  protected closedUnderSUnion (x y : M) : y ∈ ⋃₀ x ↔ ∃ z ∈ x, y ∈ z

noncomputable instance instClosedUnderSUnion
    (h : ∀ x : M, ∃ a : M, ∀ y, y ∈ a ↔ (∃ z ∈ x, y ∈ z)) : M.ClosedUnderSUnion :=
  ⟨fun x ↦ by convert Classical.choose_spec (h x); simp [sUnion, h]⟩

@[simp, grind =, push]
theorem mem_sUnion_iff [M.ClosedUnderSUnion] : x ∈ ⋃₀ a ↔ ∃ y ∈ a, x ∈ y :=
  ClosedUnderSUnion.closedUnderSUnion _ _

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

instance : (t₁.memSUnion t₂).DeltaZero := by infer_instance

/-- `t₁ = ⋃₀ t₂` -/
abbrev Term.eqSUnion :=
  (∀'∈ t₁ (&-1).memSUnion t₂.castSucc) ⊓ ∀'∈ t₂ ∀'∈ &-1 (&-1 ∈' t₁.castSucc.castSucc)

instance : (t₁.eqSUnion t₂).DeltaZero := by infer_instance

-- /-- Every set has a union -/
-- def allExSUnion : L.Sentence := ∀' ∃' (&1).eqSUnion &0

variable {M : MemStructure} (v : α → M) (xs : Fin n → M)

-- noncomputable instance (hM : M ⊨ M.L.allExSUnion) : M.ClosedUnderSUnion where
--   sUnion x := Classical.choose (exists_of_ex (realize_all.mp hM x))
--   sUnion_prop := fun x ↦ by
--     have := Classical.choose_spec (exists_of_ex (realize_all.mp hM x))
--     simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_inf,
--       Fin.reduceLast, Term.castSucc, Term.castLE_var_inr, Fin.castLE_zero, realize_all,
--       Fin.castLE_succ_castSucc, Fin.castSucc_one, realize_imp, MemStructure.realize_mem,
--       Term.realize_var, Sum.elim_inr, Fin.snoc, Fin.coe_ofNat_eq_mod, Nat.one_mod, Order.lt_two_iff,
--       Std.le_refl, ↓reduceDIte, Fin.reduceCastLT, Nat.mod_succ, lt_self_iff_false, cast_eq,
--       realize_not, Fin.reduceCastSucc, Nat.zero_mod, zero_lt_three, Fin.castSucc_zero, zero_le,
--       Order.lt_one_iff, Nat.reduceMod, Nat.lt_add_one, not_forall,
--       not_not, Nat.one_lt_ofNat] at this ⊢
--     grind

variable (t₁ t₂ : M.L.Term (α ⊕ Fin n))

@[simp 1100]
theorem Term.memSUnion_iff : (t₁.memSUnion t₂).Realize v xs ↔
    ∃ y ∈ t₂.realize' v xs, t₁.realize' v xs ∈ y := by
  simp

@[simp 1100]
theorem Term.eqSUnion_iff [M.Extensional] [M.ClosedUnderSUnion] : (t₁.eqSUnion t₂).Realize v xs ↔
    t₁.realize' v xs = ⋃₀ t₂.realize' v xs := by
  simp [Fin.castLE_add_two_castSucc, M.eq_sUnion_iff]

end FirstOrder.Language
