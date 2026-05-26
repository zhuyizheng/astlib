import Astlib.Basic.SetOperation.Insert
import Astlib.Mathlib.ModelTheory.Semantics

open Fin

namespace FirstOrder.Language.MemStructure

variable {α : Type*} {M : MemStructure} (x y z : M)


noncomputable instance (x : M) (φ : M.L.BoundedFormula α (n + 2)) (v : α → M) (xs : Fin n → M) :
  Decidable (∃ a : M, ∀ z, z ∈ a ↔ z ∈ x ∧ φ.Realize v (snoc (snoc xs x) z)) :=
  Classical.propDecidable _

/-- The subset of `x` containing `z` for which `φ.Realize v (snoc (snoc xs x) z)` holds -/
noncomputable def comprehension (x : M) (φ : M.L.BoundedFormula α (n + 2))
  (v : α → M) (xs : Fin n → M) :=
  dite (∃ a : M, ∀ z, z ∈ a ↔ z ∈ x ∧ φ.Realize v (snoc (snoc xs x) z))
    Classical.choose default

/-- The subset of `x` containing `z` for which `φ.Realize default (snoc (snoc xs x) z)` holds -/
noncomputable abbrev comprehension_empty (x : M)
    (φ : M.L.BoundedFormula Empty (n + 2))
    (xs : Fin n → M) :=
  comprehension x φ default xs

/-- The subset of `x` containing `z` for which `φ.Realize default ![x, z]` holds -/
noncomputable abbrev comprehension_empty_two (x : M)
    (φ : M.L.BoundedFormula Empty 2) :=
  comprehension x φ default default

/-- The subset of `x` containing `z` for which `φ.Realize default ![w, x, z]` holds -/
noncomputable abbrev comprehension_empty_three (x : M)
    (φ : M.L.BoundedFormula Empty 3) (w : M) :=
  comprehension x φ default ![w]

@[inherit_doc] scoped[FirstOrder.Language] notation:max
  "{∈" x " | " φ "〘"v ", " xs "〙}" => MemStructure.comprehension x φ v xs

@[inherit_doc] scoped[FirstOrder.Language] notation:max
  "{∈" x " | " φ "〘" xs "〙}" => MemStructure.comprehension_empty x φ xs

@[inherit_doc] scoped[FirstOrder.Language] notation:max
  "{∈" x " | " φ "}" => MemStructure.comprehension_empty_two x φ

@[inherit_doc] scoped[FirstOrder.Language] notation:max
  "{∈" x " | " φ "〘" w "〙₀}" => MemStructure.comprehension_empty_three x φ w

class HasComprehension (x : M) (φ : M.L.BoundedFormula α (n + 2))
  (v : α → M) (xs : Fin n → M) : Prop where
  protected comprehension_prop : ∀ z, z ∈ comprehension x φ v xs ↔
    z ∈ x ∧ φ.Realize v (snoc (snoc xs x) z)

export HasComprehension (comprehension_prop)

noncomputable instance instHasComprehension
    (x : M) (φ : M.L.BoundedFormula α (n + 2)) (v : α → M) (xs : Fin n → M)
    (h : ∃ a : M, ∀ z, z ∈ a ↔ z ∈ x ∧ φ.Realize v (snoc (snoc xs x) z)) :
    M.HasComprehension x φ v xs :=
  ⟨by convert Classical.choose_spec h; simp [comprehension, h]⟩

@[simp, grind =, push]
theorem mem_comprehension_iff (x : M) (φ : M.L.BoundedFormula α (n + 2))
    (v : α → M) (xs : Fin n → M) [hx : HasComprehension x φ v xs] (z : M) :
    z ∈ {∈ x | φ 〘v, xs〙} ↔ z ∈ x ∧ φ.Realize v (snoc (snoc xs x) z) :=
  M.comprehension_prop _

@[simp, grind =, push]
theorem mem_comprehension_iff₀ (x : M) (φ : M.L.BoundedFormula Empty 2)
    [HasComprehension x φ default default] (z : M) :
    z ∈ {∈ x | φ } ↔ z ∈ x ∧ φ.Realize default (snoc (snoc default x) z) :=
  mem_comprehension_iff x φ default default z

theorem comprehension_subset (x : M) (φ : M.L.BoundedFormula α (n + 2))
    (v : α → M) (xs : Fin n → M) [HasComprehension x φ v xs] :
    {∈ x | φ 〘v, xs〙} ⊆ x := by
  grind

theorem comprehension_top [M.Extensional] (x : M)
    (v : α → M) (xs : Fin n → M) [HasComprehension x ⊤ v xs] :
    {∈ x | ⊤ 〘v, xs〙} = x := by
  ext; simp

theorem comprehension_bot [M.Extensional] [M.HasEmpty] {x : M}
    (v : α → M) (xs : Fin n → M) [HasComprehension x ⊥ v xs] :
    {∈ x | ⊥ 〘v, xs〙} = ∅ := by
  ext; simp

theorem comprehension_eq_iff [M.Extensional] (x : M) (φ ψ : M.L.BoundedFormula α (n + 2))
    (v w : α → M) (xs ys : Fin n → M) [HasComprehension x φ v xs] [HasComprehension x ψ w ys] :
    {∈ x | φ 〘v, xs〙} = {∈ x | ψ 〘w, ys〙} ↔
      ∀ z ∈ x, φ.Realize v (snoc (snoc xs x) z) ↔ ψ.Realize w (snoc (snoc ys x ) z) := by
  simp [eq_iff]

theorem comprehension_eq_univ_iff [M.Extensional] (x : M) (φ : M.L.BoundedFormula α (n + 2))
    (v : α → M) (xs : Fin n → M) [HasComprehension x φ v xs] :
    {∈ x | φ 〘v, xs〙} = x ↔
      ∀ z ∈ x, φ.Realize v (snoc (snoc xs x) z) := by
  simp [eq_iff]

theorem comprehension_eq_empty_iff [M.Extensional] [M.HasEmpty] (x : M)
    (φ : M.L.BoundedFormula α (n + 2))
    (v : α → M) (xs : Fin n → M) [HasComprehension x φ v xs] :
    {∈ x | φ 〘v, xs〙} = ∅ ↔
      ∀ z ∈ x, ¬φ.Realize v (snoc (snoc xs x) z) := by
  simp [eq_iff]

variable (M) in
class ClosedUnderDeltaZeroComprehension : Prop where
  closedUnderDeltaZeroComprehension {n} (x : M) (φ : M.L.BoundedFormula Empty (n + 2)) [φ.DeltaZero]
    (xs : Fin n → M) :
    ∀ z, z ∈ comprehension x φ v xs ↔ z ∈ x ∧ φ.Realize default (snoc (snoc xs x) z)

export ClosedUnderDeltaZeroComprehension (closedUnderDeltaZeroComprehension)

instance [M.ClosedUnderDeltaZeroComprehension] (x : M)
  (φ : M.L.BoundedFormula Empty (n + 2)) [φ.DeltaZero] (xs : Fin n → M) :
  HasComprehension x φ default xs := ⟨closedUnderDeltaZeroComprehension x φ xs⟩

variable (M) in
class ClosedUnderComprehension : Prop where
  closedUnderComprehension (x : M) (φ : M.L.BoundedFormula Empty (n + 2))
    (xs : Fin n → M) :
    ∀ z, z ∈ comprehension x φ v xs ↔ z ∈ x ∧ φ.Realize default (snoc (snoc xs x) z)

export ClosedUnderComprehension (closedUnderComprehension)

instance [M.ClosedUnderComprehension] :
  M.ClosedUnderDeltaZeroComprehension  := ⟨fun x φ _ xs ↦ closedUnderComprehension x φ xs⟩

instance [M.ClosedUnderComprehension] (x : M)
  {φ : M.L.BoundedFormula Empty (n + 2)} (xs : Fin n → M) :
  HasComprehension x φ default xs := ⟨closedUnderComprehension x φ xs⟩

end MemStructure

variable {L : FirstOrder.Language} [HasMem L]

/-- The comprehension axiom -/
def BoundedFormula.comprehension (φ : L.BoundedFormula α (n + 2)) : L.Formula α :=
  ∀'' ∃' ∀' (&-1 ∈' &-2 ⇔ (&-1 ∈' &-3 ⊓ φ.liftAt 1 (n + 1)))

def deltaZeroComprehensionSchema : Set (L.Sentence) :=
  {ψ | ∃ n, ∃ φ : L.BoundedFormula Empty (n + 2), ∃ _ : φ.DeltaZero, ψ = φ.comprehension}
  -- {ψ | ∃ n, ∃ φ : L.BoundedFormula Empty (n + 2), DeltaZero φ ∧ ψ = φ.comprehension}

def comprehensionSchema : Set (L.Sentence) :=
  {ψ | ∃ n, ∃ φ : L.BoundedFormula Empty (n + 2), ψ = φ.comprehension}

variable {M : MemStructure}

-- instance (hM : M ⊨ M.L.deltaZeroComprehensionSchema) :
--   M.ClosedUnderDeltaZeroComprehension where
--   closedUnderDeltaZeroComprehension := by
--     intro _ n x φ hφ xs
--     simp +contextual only [deltaZeroComprehensionSchema, BoundedFormula.comprehension,
--       Function.comp_apply, exists_prop, Theory.model_iff, Set.mem_setOf_eq, Sentence.Realize,
--       forall_exists_index, BoundedFormula.realize_alls, BoundedFormula.realize_ex,
--       Nat.succ_eq_add_one, BoundedFormula.realize_all, BoundedFormula.realize_iff,
--       MemStructure.realize_mem, Term.realize_var, Sum.elim_inr, snoc, val_last_plus_one_minus_one,
--       lt_add_iff_pos_right, Order.lt_one_iff, ↓reduceDIte, castSucc_castLT, val_castLT,
--       lt_self_iff_false, cast_eq, val_last, BoundedFormula.realize_inf, val_last_plus_two_minus_two,
--       Order.lt_add_one_iff, le_add_iff_nonneg_right, _root_.zero_le, BoundedFormula.realize_liftAt',
--       addNat_one, and_imp] at hM
--     specialize hM (φ.comprehension) n φ hφ rfl (snoc xs x)
--     simp only [snoc, val_castLT, val_last_plus_two_minus_two, lt_self_iff_false, ↓reduceDIte,
--       cast_eq, Pi.default_def] at hM ⊢
--     convert hM
--     grind [Fin.snoc_nat]

-- instance (hM : M ⊨ M.L.comprehensionSchema) :
--   M.ClosedUnderComprehension where
--   closedUnderComprehension := by
--     intro n x φ xs
--     simp +contextual only [comprehensionSchema, BoundedFormula.comprehension, Function.comp_apply,
--       Theory.model_iff, Set.mem_setOf_eq, Sentence.Realize, forall_exists_index,
--       BoundedFormula.realize_alls, BoundedFormula.realize_ex, Nat.succ_eq_add_one,
--       BoundedFormula.realize_all, BoundedFormula.realize_iff, MemStructure.realize_mem,
--       Term.realize_var, Sum.elim_inr, snoc, val_last_plus_one_minus_one, lt_add_iff_pos_right,
--       Order.lt_one_iff, ↓reduceDIte, castSucc_castLT, val_castLT, lt_self_iff_false, cast_eq,
--       val_last, BoundedFormula.realize_inf, val_last_plus_two_minus_two, Order.lt_add_one_iff,
--       le_add_iff_nonneg_right, _root_.zero_le, BoundedFormula.realize_liftAt', addNat_one] at hM
--     specialize hM (φ.comprehension) n φ rfl (snoc xs x)
--     simp only [snoc, val_castLT, val_last_plus_two_minus_two, lt_self_iff_false, ↓reduceDIte,
--       cast_eq, Pi.default_def] at hM ⊢
--     convert hM
--     grind [Fin.snoc_nat]

-- noncomputable instance (x : M)
--     [hx : M.HasComprehension (α := Empty) (n := 0) x ⊥ default default] : M.HasEmpty where
--   emptyCollection := {∈ x | ⊥}
--   empty_prop (x) := by simp


end FirstOrder.Language
