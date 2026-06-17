import Astlib.Basic.SetOperation.Foundational
import Astlib.Basic.SetOperation.Choice
import Astlib.Mathlib.Fin.Basic

namespace FirstOrder

namespace Language

open FirstOrder Language BoundedFormula Fin

variable {L : FirstOrder.Language} [L.HasMem] {M : MemStructure}

/-- The extensionalityAxiom axiom -/
def extensionalityAxiom {L : FirstOrder.Language} [L.HasMem] : L.Sentence :=
  ∀' ∀' (∀' (&2 ∈' &0 ⇔ &2 ∈' &1) ⟹ &0 =' &1)

class MemStructure.ModelsExtensionality [HasMem M.L] : Prop where
  protected modelsExtensionality : M ⊨ M.L.extensionalityAxiom

instance [hM : M.ModelsExtensionality] : M.Extensional :=
  ⟨by simpa [Sentence.Realize, Formula.Realize, extensionalityAxiom] using hM.modelsExtensionality⟩

/-- The comprehension axiom -/
def BoundedFormula.comprehension (φ : L.BoundedFormula α (n + 2)) : L.Formula α :=
  ∀'' ∃' ∀' (&-1 ∈' &-2 ⇔ (&-1 ∈' &-3 ⊓ φ.liftAt 1 (n + 1)))

/-- DeltaZero comprehension schema -/
def deltaZeroComprehensionSchema : Set (L.Sentence) :=
  {ψ | ∃ n, ∃ φ : L.BoundedFormula Empty (n + 2), ∃ _ : φ.DeltaZero, ψ = φ.comprehension}
  -- {ψ | ∃ n, ∃ φ : L.BoundedFormula Empty (n + 2), DeltaZero φ ∧ ψ = φ.comprehension}

class MemStructure.ModelsDeltaZeroComprehension [HasMem M.L] : Prop where
  protected modelsDeltaZeroComprehension : M ⊨ M.L.deltaZeroComprehensionSchema

theorem MemStructure.exists_isComprehension_of_models {n} (x : M)
    (φ : M.L.BoundedFormula Empty (n + 2)) (xs : Fin n → M) (hM : M ⊨ φ.comprehension) :
    ∃ a : M, M.IsComprehension a x φ default xs := by
  simp only [Sentence.Realize, BoundedFormula.comprehension, Function.comp_apply, realize_alls,
    realize_ex,
    Nat.succ_eq_add_one, realize_all, realize_iff, MemStructure.realize_mem, Term.realize_var,
    Sum.elim_inr, snoc, val_last_plus_one_minus_one, lt_add_iff_pos_right, Order.lt_one_iff,
    ↓reduceDIte, castSucc_castLT, val_castLT, lt_self_iff_false, cast_eq, val_last, realize_inf,
    val_last_plus_two_minus_two, Order.lt_add_one_iff, le_add_iff_nonneg_right,
    _root_.zero_le] at hM
  specialize hM (snoc xs x)
  convert hM using 5
  · simp [snoc_nat]
  · simp only [le_add_iff_nonneg_right, _root_.zero_le, realize_liftAt', Order.lt_add_one_iff,
      addNat_one]
    rw [← eq_iff_iff]
    congr 1
    · grind
    · grind [snoc_nat]

theorem MemStructure.closedUnderDeltaZeroComprehension_of_modelsDeltaZeroComprehension
    [hM : M.ModelsDeltaZeroComprehension] {n} (x : M) (φ : M.L.BoundedFormula Empty (n + 2))
    [φ.DeltaZero]
    (xs : Fin n → M) :
    ∃ a : M, M.IsComprehension a x φ default xs := by
  replace hM := hM.modelsDeltaZeroComprehension
  simp only [deltaZeroComprehensionSchema, exists_prop, Theory.model_iff, Set.mem_setOf_eq,
    forall_exists_index, and_imp] at hM
  exact M.exists_isComprehension_of_models _ _ _ (hM φ.comprehension n φ (by infer_instance) rfl)

instance [M.ModelsDeltaZeroComprehension] : M.ClosedUnderDeltaZeroComprehension :=
  ⟨M.closedUnderDeltaZeroComprehension_of_modelsDeltaZeroComprehension⟩

instance [M.ModelsDeltaZeroComprehension] : M.HasEmpty := by infer_instance

/-- Full comprehension schema -/
def comprehensionSchema : Set (L.Sentence) :=
  {ψ | ∃ n, ∃ φ : L.BoundedFormula Empty (n + 2), ψ = φ.comprehension}

class MemStructure.ModelsComprehension [HasMem M.L] : Prop where
  protected modelsComprehension : M ⊨ M.L.comprehensionSchema

theorem MemStructure.closedUnderComprehension_of_modelsComprehension
    [hM : M.ModelsComprehension] {n} (x : M) (φ : M.L.BoundedFormula Empty (n + 2))
    (xs : Fin n → M) :
    ∃ a : M, M.IsComprehension a x φ default xs := by
  replace hM := hM.modelsComprehension
  simp only [comprehensionSchema, Theory.model_iff, Set.mem_setOf_eq, forall_exists_index] at hM
  exact M.exists_isComprehension_of_models _ _ _ (hM φ.comprehension n φ rfl)

instance [M.ModelsComprehension] : M.ClosedUnderComprehension :=
  ⟨M.closedUnderComprehension_of_modelsComprehension⟩

/-- The union axiom -/
def sUnionAxiom : L.Sentence := ∀' ∃' ∀' ∀' ((&3 ∈' &2 ⊓ &2 ∈' &0) ⟹ &3 ∈' &1)

class MemStructure.ModelsSUnion [HasMem M.L] : Prop where
  protected modelsSUnion : M ⊨ M.L.sUnionAxiom

theorem MemStructure.exists_isSUnion [hM₁ : M.ModelsSUnion]
    [hM₂ : M.ModelsDeltaZeroComprehension] (x : M) :
    ∃ a : M, M.IsSUnion a x := by
  replace hM₁ := hM₁.modelsSUnion
  simp only [Sentence.Realize, Formula.Realize, sUnionAxiom, Nat.reduceAdd, isValue,
    Function.comp_apply, realize_all, Nat.succ_eq_add_one, realize_ex, realize_imp, realize_inf,
    realize_mem, Term.realize_var, Sum.elim_inr, snoc, coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.lt_add_one, ↓reduceDIte, reduceCastLT, reduceCastSucc, Nat.mod_succ, lt_self_iff_false,
    reduceLast, cast_eq, Nat.zero_mod, zero_lt_three, castSucc_zero, Order.lt_two_iff,
    _root_.zero_le, Order.lt_one_iff, val_eq_zero, Nat.one_mod, Nat.one_lt_ofNat, castSucc_one,
    Std.le_refl, and_imp] at hM₁
  specialize hM₁ x
  obtain ⟨b, hb⟩ := hM₁
  use {∈ b | ((&2).memSUnion &0) 〘x〙₀}
  simp only [IsSUnion]
  intro y
  simp only [isValue, Function.comp_apply, mem_comprehension_iff, Nat.reduceAdd, Pi.default_def,
    Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty, Term.memSUnion_iff, Term.realize_var,
    Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val, and_iff_right_iff_imp, forall_exists_index,
    and_imp]
  grind

instance [M.ModelsSUnion] [M.ModelsDeltaZeroComprehension] : M.ClosedUnderSUnion :=
  ⟨M.exists_isSUnion⟩

/-- The pairing axiom -/
def pairAxiom : L.Sentence := ∀' ∀' ∃' (&0 ∈' &2 ⊓ &1 ∈' &2)

class MemStructure.ModelsPair [HasMem M.L] : Prop where
  protected modelsPair : M ⊨ M.L.pairAxiom

theorem MemStructure.exists_isUnorderedPair [hM₁ : M.ModelsPair]
    [hM₂ : M.ModelsDeltaZeroComprehension] (x y : M) :
    ∃ a : M, M.IsUnorderedPair a x y := by
  replace hM₁ := hM₁.modelsPair
  simp only [Sentence.Realize, Formula.Realize, pairAxiom, Nat.reduceAdd, isValue,
    Function.comp_apply, realize_all, Nat.succ_eq_add_one, realize_ex, realize_inf, realize_mem,
    Term.realize_var, Sum.elim_inr, snoc, coe_ofNat_eq_mod, Nat.mod_succ, lt_self_iff_false,
    ↓reduceDIte, reduceLast, cast_eq, Nat.zero_mod, Order.lt_two_iff, _root_.zero_le, reduceCastLT,
    castSucc_zero, Order.lt_one_iff, val_eq_zero, Nat.one_mod, Std.le_refl, castSucc_one] at hM₁
  specialize hM₁ x y
  obtain ⟨b, hb⟩ := hM₁
  use {∈ b | ((&3).memUnorderedPair &0 &1) 〘![x, y]〙}
  simp only [IsUnorderedPair]
  intro z
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    mem_comprehension_iff, Pi.default_def, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty,
    Term.memUnorderedPair_iff, Term.realize_var, Sum.elim_inr, Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, and_iff_right_iff_imp]
  grind

instance [M.ModelsPair] [M.ModelsDeltaZeroComprehension] : M.ClosedUnderPair :=
  ⟨M.exists_isUnorderedPair⟩

/-- The power set axiom -/
def powersetAxiom : L.Sentence := ∀' ∃' ∀' (&2 ⊆' &0 ⟹ &2 ∈' &1)

class MemStructure.ModelsPowerset [HasMem M.L] : Prop where
  protected modelsPowerset : M ⊨ M.L.powersetAxiom

theorem MemStructure.exists_isPowerset [hM₁ : M.ModelsPowerset]
    [hM₂ : M.ModelsDeltaZeroComprehension] (x : M) :
    ∃ a : M, M.IsPowerset a x := by
  replace hM₁ := hM₁.modelsPowerset
  simp only [Sentence.Realize, Formula.Realize, powersetAxiom, Nat.reduceAdd, isValue,
    Function.comp_apply, realize_all, Nat.succ_eq_add_one, realize_ex, realize_imp, Term.subset_iff,
    Term.realize_var, Sum.elim_inr, snoc, coe_ofNat_eq_mod, Nat.mod_succ, lt_self_iff_false,
    ↓reduceDIte, reduceLast, cast_eq, Nat.zero_mod, Order.lt_two_iff, _root_.zero_le, reduceCastLT,
    castSucc_zero, Order.lt_one_iff, val_eq_zero, realize_mem, Nat.one_mod, Std.le_refl,
    castSucc_one] at hM₁
  simp only [Term.castSucc, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Term.castLE_var_inr,
    castLE_succ_castSucc, reduceCastSucc, Term.realize_var, Sum.elim_inr, snoc, coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.lt_add_one, ↓reduceDIte, reduceCastLT, Nat.mod_succ, lt_self_iff_false,
    reduceLast, cast_eq, castLE_zero, Nat.zero_mod, zero_lt_three, castSucc_zero, Order.lt_two_iff,
    _root_.zero_le, Order.lt_one_iff, val_eq_zero] at hM₁
  specialize hM₁ x
  obtain ⟨b, hb⟩ := hM₁
  use {∈ b | ((&2).subset &0) 〘x〙₀}
  simp only [IsPowerset]
  intro y
  simp only [isValue, Function.comp_apply, mem_comprehension_iff, Nat.reduceAdd, Pi.default_def,
    Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty, Term.subset_iff, Term.realize_var,
    Sum.elim_inr, Matrix.cons_val, Matrix.cons_val_zero, and_iff_right_iff_imp]
  grind

instance [M.ModelsPowerset] [M.ModelsDeltaZeroComprehension] : M.ClosedUnderPowerset :=
  ⟨M.exists_isPowerset⟩

/-- The foundation axiom -/
def foundation : L.Sentence := ∀' ((&0).isEmpty ⊔ ∃'∈ &0 ∼(∃'∈ &0 (&2 ∈' &1)))

theorem exists_memMin [M.Extensional] [M.HasEmpty] (hM : M ⊨ M.L.foundation) (x : M)
    (hx : x ≠ ∅) :
    ∃ y : M, (y ∈ x ∧ ∀ z ∈ y, z ∉ x) := by
  have : ∀ (a : ↑M), a = ∅ ∨ ∃ x ∈ a, ∀ x_1 ∈ a, x_1 ∉ x := by
    simpa [foundation, Sentence.Realize, Formula.Realize, Fin.snoc] using hM
  specialize this x
  grind

-- noncomputable instance [M.Extensional] [M.HasEmpty]
--     (hM : M ⊨ M.L.foundation) : M.Foundational :=
--   M.instFoundational (fun x ↦ exists_memMin hM x)

-- noncomputable instance (hM : M ⊨ M.L.allExSUnion) : M.ClosedUnderSUnion where

-- def comprehension' (φ : L.BoundedFormula α (n + 2)) : L.BoundedFormula α (n + 2) :=
--   ∀' (&-1 ∈' &-2 ⇔ (&-1 ∈' &0 ⊓ φ.liftAt 1 (n + 1)))


-- /-- The pairing axiom -/
-- def pair : L.Sentence := ∀' ∀' ∃' (&2 ∈' &0 ⊔ &2 ∈' &1)

-- /-- The union axiom -/
-- def sUnion : L.Sentence := ∀' ∃' ∀' ∀' ((&3 ∈' &2 ⊓ &2 ∈' &0) ⟹ &3 ∈' &1)

-- /-- The replacement axiom -/
-- def replacement (φ : L.BoundedFormula α (n + 3)) : L.Formula α :=
--   ∀'' ((∀'∈ &0 ∃!' φ) ⟹ ∃' (∀'∈ &0 ∃'∈ &-3 (φ.liftAt 1 (n + 1))))

-- /-- The infinity axiom -/
-- def infinity : L.Sentence := ∃' ((∃'∈ &0 (&1).isEmpty) ⊓ ∀'∈ &0 (∃'∈ &0 ((&2).eqSucc &1)))

-- /-- The foundation axiom -/
-- def foundation : L.Sentence := ∀' ((&0).isEmpty ⊔ ∃'∈ &0 ∼(∃'∈ &0 (&2 ∈' &1)))

-- /-- The power set axiom -/
-- def power : L.Sentence := ∀' ∃' ∀' (&2 ⊆' &0 ⟹ &2 ∈' &1)

-- /-- The axiom of choice -/
-- def choice : L.Sentence :=
--   ∀' (∼(&-1).isEmpty ⟹ ∃' ((&-2).isFun ⊓ (&-1).eqDom (&-2) ⊓
--     ∀' ∃' ((&-3).memDom (&-2) ⟹ ∼(&-3).isEmpty ⟹ ((&-4).eqVal &-2 &-3 ⊓ &-4 ∈' &-3))))

-- /-- There exists an empty set -/
-- def exEmptyset : L.Sentence := ∃' ((&0).isEmpty)

-- /-- Every set has a union -/
-- def allExSUnion : L.Sentence := ∀' ∃' ∀' (&2 ∈' &1 ⇔ ∃' ((&3 ∈' &0 ⊓ &2 ∈' &3)))

-- /-- Closed under unordered pairing -/
-- def allAllExPair : L.Sentence := ∀' ∀' ∃' ∀' (&3 ∈' &2 ⇔ (&3 =' &0 ⊔ &3 =' &1))

-- /-- Closed under power set -/
-- def allExPowerset : L.Sentence := ∀' ∃' ∀' (&2 ∈' &1 ⇔ &2 ⊆' &0)


end Language

end FirstOrder
