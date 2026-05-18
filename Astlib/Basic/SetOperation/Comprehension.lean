import Astlib.Basic.SetOperation.Insert
import Astlib.Mathlib.ModelTheory.Semantics

open Fin

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y z : M)

class HasComprehension (x : M) (φ : M.L.BoundedFormula α (n + 2)) (v : α → M) (xs : Fin n → M) where
  hasComprehension : ∃ y : M, ∀ z, z ∈ y ↔ z ∈ x ∧ φ.Realize v (snoc (snoc xs x) z)

export HasComprehension (hasComprehension)

/-- The subset of `x` containing `z` for which `φ.Realize v (snoc (snoc xs x) z)` holds -/
noncomputable def subsetComprehension (x : M) (φ : M.L.BoundedFormula α (n + 2))
    (v : α → M) (xs : Fin n → M) [hx : HasComprehension x φ v xs] :=
  Classical.choose hx.hasComprehension

/-- The subset of `x` containing `z` for which `φ.Realize default (snoc (snoc xs x) z)` holds -/
noncomputable abbrev subsetComprehension_empty (x : M)
    (φ : M.L.BoundedFormula Empty (n + 2))
    (xs : Fin n → M) [HasComprehension x φ default xs] :=
  subsetComprehension x φ default xs

/-- The subset of `x` containing `z` for which `φ.Realize default ![x, z]` holds -/
noncomputable abbrev subsetComprehension_empty_two (x : M)
    (φ : M.L.BoundedFormula Empty 2)
    [HasComprehension x φ default default] :=
  subsetComprehension x φ default default

/-- The subset of `x` containing `z` for which `φ.Realize default ![w, x, z]` holds -/
noncomputable abbrev subsetComprehension_empty_three (x : M)
    (φ : M.L.BoundedFormula Empty 3) (w : M)
    [HasComprehension x φ default ![w] ] :=
  subsetComprehension x φ default ![w]

@[inherit_doc] scoped[FirstOrder.Language.MemStructure] notation:max
  "{∈" x " | " φ "〘"v ", " xs "〙}" => subsetComprehension x φ v xs

@[inherit_doc] scoped[FirstOrder.Language.MemStructure] notation:max
  "{∈" x " | " φ "〘" xs "〙}" => subsetComprehension_empty x φ xs

@[inherit_doc] scoped[FirstOrder.Language.MemStructure] notation:max
  "{∈" x " | " φ "}" => subsetComprehension_empty_two x φ

@[inherit_doc] scoped[FirstOrder.Language.MemStructure] notation:max
  "{∈" x " | " φ "〘" w "〙}" => subsetComprehension_empty_three x φ w

@[simp, grind =, push]
theorem mem_subsetComprehension_iff (x : M) (φ : M.L.BoundedFormula α (n + 2))
    (v : α → M) (xs : Fin n → M) [hx : HasComprehension x φ v xs] (z : M) :
    z ∈ {∈ x | φ 〘v, xs〙} ↔ z ∈ x ∧ φ.Realize v (snoc (snoc xs x) z) :=
  Classical.choose_spec hx.hasComprehension z

@[simp, grind =, push]
theorem mem_subsetComprehension_iff₀ (x : M) (φ : M.L.BoundedFormula Empty 2)
    [HasComprehension x φ default default] (z : M) :
    z ∈ {∈ x | φ } ↔ z ∈ x ∧ φ.Realize default (snoc (snoc default x) z) :=
  mem_subsetComprehension_iff x φ default default z

theorem subsetComprehension_subset (x : M) (φ : M.L.BoundedFormula α (n + 2))
    (v : α → M) (xs : Fin n → M) [HasComprehension x φ v xs] :
    {∈ x | φ 〘v, xs〙} ⊆ x := by
  grind

theorem subsetComprehension_top [Extensional M] (x : M)
    (v : α → M) (xs : Fin n → M) [HasComprehension x ⊤ v xs] :
    {∈ x | ⊤ 〘v, xs〙} = x := by
  ext; simp

theorem subsetComprehension_bot [Extensional M] [HasEmpty M] {x : M}
    (v : α → M) (xs : Fin n → M) [HasComprehension x ⊥ v xs] :
    {∈ x | ⊥ 〘v, xs〙} = ∅ := by
  ext; simp

theorem subsetComprehension_eq_iff [Extensional M] (x : M) (φ ψ : M.L.BoundedFormula α (n + 2))
    (v w : α → M) (xs ys : Fin n → M) [HasComprehension x φ v xs] [HasComprehension x ψ w ys] :
    {∈ x | φ 〘v, xs〙} = {∈ x | ψ 〘w, ys〙} ↔
      ∀ z ∈ x, φ.Realize v (snoc (snoc xs x) z) ↔ ψ.Realize w (snoc (snoc ys x ) z) := by
  simp [eq_iff]

theorem subsetComprehension_eq_univ_iff [Extensional M] (x : M) (φ : M.L.BoundedFormula α (n + 2))
    (v : α → M) (xs : Fin n → M) [HasComprehension x φ v xs] :
    {∈ x | φ 〘v, xs〙} = x ↔
      ∀ z ∈ x, φ.Realize v (snoc (snoc xs x) z) := by
  simp [eq_iff]

theorem subsetComprehension_eq_empty_iff [Extensional M] [HasEmpty M] (x : M)
    (φ : M.L.BoundedFormula α (n + 2))
    (v : α → M) (xs : Fin n → M) [HasComprehension x φ v xs] :
    {∈ x | φ 〘v, xs〙} = ∅ ↔
      ∀ z ∈ x, ¬φ.Realize v (snoc (snoc xs x) z) := by
  simp [eq_iff]

variable (M) in
class ClosedUnderDeltaZeroComprehension where
  hasDeltaZeroComprehension (x : M) (φ : M.L.BoundedFormula Empty (n + 2)) [φ.DeltaZero]
    (xs : Fin n → M) : ∃ y : M, ∀ z, z ∈ y ↔ z ∈ x ∧ φ.Realize default (snoc (snoc xs x) z)

export ClosedUnderDeltaZeroComprehension (hasDeltaZeroComprehension)

instance instHasComprehension_of_deltaZero [ClosedUnderDeltaZeroComprehension M] (x : M)
  (φ : M.L.BoundedFormula Empty (n + 2)) [φ.DeltaZero] (xs : Fin n → M) :
  HasComprehension x φ default xs where
  hasComprehension := hasDeltaZeroComprehension x φ xs

instance instClosedUnderDeltaZeroComprehension (hM : M ⊨ M.L.deltaZeroComprehensionSchema) :
  ClosedUnderDeltaZeroComprehension M where
  hasDeltaZeroComprehension := by
    intro n x φ hφ xs
    simp +contextual only [deltaZeroComprehensionSchema, BoundedFormula.comprehension,
      Function.comp_apply, Theory.model_iff, Set.mem_setOf_eq, Sentence.Realize,
      forall_exists_index, BoundedFormula.realize_alls, BoundedFormula.realize_ex,
      Nat.succ_eq_add_one, BoundedFormula.realize_all, BoundedFormula.realize_iff, realize_mem,
      Term.realize_var, Sum.elim_inr, snoc, val_last_plus_one_minus_one, lt_add_iff_pos_right,
      Order.lt_one_iff, ↓reduceDIte, castSucc_castLT, val_castLT, lt_self_iff_false, cast_eq,
      val_last, BoundedFormula.realize_inf, val_last_plus_two_minus_two, Order.lt_add_one_iff,
      le_add_iff_nonneg_right, _root_.zero_le, BoundedFormula.realize_liftAt', addNat_one,
      and_imp] at hM
    specialize hM (φ.comprehension) n φ hφ rfl (snoc xs x)
    simp only [snoc, val_castLT, val_last_plus_two_minus_two, lt_self_iff_false, ↓reduceDIte,
      cast_eq, Pi.default_def] at hM ⊢
    convert hM
    grind [Fin.snoc_nat]

variable (M) in
class ClosedUnderComprehension where
  hasComprehension (x : M) (φ : M.L.BoundedFormula Empty (n + 2))
    (xs : Fin n → M) : ∃ y : M, ∀ z, z ∈ y ↔ z ∈ x ∧ φ.Realize default (snoc (snoc xs x) z)

export ClosedUnderComprehension (hasComprehension)

instance instHasComprehension [ClosedUnderComprehension M] (x : M)
  {φ : M.L.BoundedFormula Empty (n + 2)} (xs : Fin n → M) :
  HasComprehension x φ default xs where
  hasComprehension := hasComprehension x φ xs

instance instClosedUnderComprehension (hM : M ⊨ M.L.comprehensionSchema) :
  ClosedUnderComprehension M where
  hasComprehension := by
    intro n x φ xs
    simp +contextual only [comprehensionSchema, BoundedFormula.comprehension, Function.comp_apply,
      Theory.model_iff, Set.mem_setOf_eq, Sentence.Realize, forall_exists_index,
      BoundedFormula.realize_alls, BoundedFormula.realize_ex, Nat.succ_eq_add_one,
      BoundedFormula.realize_all, BoundedFormula.realize_iff, realize_mem, Term.realize_var,
      Sum.elim_inr, snoc, val_last_plus_one_minus_one, lt_add_iff_pos_right, Order.lt_one_iff,
      ↓reduceDIte, castSucc_castLT, val_castLT, lt_self_iff_false, cast_eq, val_last,
      BoundedFormula.realize_inf, val_last_plus_two_minus_two, Order.lt_add_one_iff,
      le_add_iff_nonneg_right, _root_.zero_le, BoundedFormula.realize_liftAt', addNat_one] at hM
    specialize hM (φ.comprehension) n φ rfl (snoc xs x)
    simp only [snoc, val_castLT, val_last_plus_two_minus_two, lt_self_iff_false, ↓reduceDIte,
      cast_eq, Pi.default_def] at hM ⊢
    convert hM
    grind [Fin.snoc_nat]


-- noncomputable instance instHasEmpty (x : M)
--     [hx : HasComprehension (α := Empty) (n := 0) x ⊥ default default] : HasEmpty M where
--   emptyCollection := {∈ x | ⊥}
--   empty_prop (x) := by simp


end FirstOrder.Language.MemStructure
