/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Foundational
import Astlib.Basic.SetOperation.Choice
import Astlib.Mathlib.Fin.Basic
/-!
file docstring
-/

namespace FirstOrder

namespace Language

open FirstOrder Language BoundedFormula Fin

variable {L : FirstOrder.Language} [L.HasMem] {M : MemStructure} {α : Type*} (n : ℕ)

/-- The extensionalityAxiom axiom -/
def extensionalityAxiom {L : FirstOrder.Language} [L.HasMem] : L.Sentence :=
  ∀' ∀' (∀' (&2 ∈' &0 ⇔ &2 ∈' &1) ⟹ &0 =' &1)

class MemStructure.ModelsExtensionality [HasMem M.L] : Prop where
  protected modelsExtensionality : M ⊨ M.L.extensionalityAxiom

instance [hM : M.ModelsExtensionality] : M.Extensional :=
  ⟨by simpa [extensionalityAxiom, snoc] using hM.modelsExtensionality⟩

/-- The comprehension axiom -/
def BoundedFormula.comprehension (φ : L.BoundedFormula' (n + 1)) : L.Sentence :=
  ∀'' ∃' ∀' (&-1 ∈' &-2 ⇔ (&-1 ∈' &-3 ⊓ φ.substBoundBound (snoc (castAdd 3) (last _))))

/-- DeltaZero comprehension schema -/
def deltaZeroComprehensionSchema : Set (L.Sentence) :=
  {ψ | ∃ n, ∃ φ : L.BoundedFormula' (n + 1), ∃ _ : φ.DeltaZero, ψ = φ.comprehension}

class MemStructure.ModelsDeltaZeroComprehension [HasMem M.L] : Prop where
  protected modelsDeltaZeroComprehension : M ⊨ M.L.deltaZeroComprehensionSchema

theorem MemStructure.exists_isComprehension_of_models {n} (x : M)
    (φ : M.L.BoundedFormula' (n + 1)) (xs : Fin n → M) (hM : M ⊨ φ.comprehension) :
    ∃ a : M, M.IsComprehension a x (φ.switchBound.multiclass.slice xs) := by
  simp only [Sentence.Realize, BoundedFormula.comprehension, Function.comp_apply, realize_alls,
    realize_ex, Nat.succ_eq_add_one, realize_all, realize_iff, realize_mem, Term.realize'_var',
    snoc, val_castAdd, val_last, lt_add_iff_pos_right, Order.lt_one_iff, ↓reduceDIte,
    castLT_castAdd, lt_self_iff_false, cast_eq, realize_inf, Order.lt_add_one_iff,
    le_add_iff_nonneg_right, _root_.zero_le, castSucc_castLT, val_castLT,
    realize_substBoundBound] at hM
  simp only [IsComprehension]
  specialize hM (snoc xs x)
  convert hM using 5
  · simp [snoc_nat]
  · sorry
  -- · simp only [Multiclass.toClass, Equiv.arrowCongr_apply, Equiv.coe_refl,
  --   Equiv.funUnique_symm_apply, Function.comp_apply, Multiclass.slice, multiclass,
  --   realize'_switchBound, id_eq, ← eq_iff_iff]
  --   congr 1
  --   ext i
  --   cases i using lastCases with
  --   | last => simp [append_nat]
  --   | cast j => grind [append_nat, snoc_nat]

-- theorem MemStructure.closedUnderDeltaZeroComprehension_of_modelsDeltaZeroComprehension
--     [hM : M.ModelsDeltaZeroComprehension] {n} (x : M) (φ : M.L.BoundedFormula Empty (n + 1))
--     [φ.DeltaZero]
--     (xs : Fin n → M) :
--     ∃ a : M, M.IsComprehension a x φ default xs := by
--   replace hM := hM.modelsDeltaZeroComprehension
--   simp only [deltaZeroComprehensionSchema, exists_prop, Theory.model_iff, Set.mem_setOf_eq,
--     forall_exists_index, and_imp] at hM
--   exact M.exists_isComprehension_of_models _ _ _ (hM φ.comprehension n φ (by infer_instance) rfl)

-- instance [M.ModelsDeltaZeroComprehension] : M.ClosedUnderDeltaZeroComprehension :=
--   ⟨M.closedUnderDeltaZeroComprehension_of_modelsDeltaZeroComprehension⟩

-- instance [M.ModelsDeltaZeroComprehension] : M.HasEmpty := by infer_instance

/-- Full comprehension schema -/
def comprehensionSchema : Set (L.Sentence) :=
  {ψ | ∃ n, ∃ φ : L.BoundedFormula' (n + 1), ψ = φ.comprehension}

class MemStructure.ModelsComprehension [HasMem M.L] : Prop where
  protected modelsComprehension : M ⊨ M.L.comprehensionSchema

theorem MemStructure.exists_isComprehension_of_modelsComprehension
    [hM : M.ModelsComprehension] (x : M) (A : M.Class) [hA : A.Definable Set.univ] :
    ∃ a : M, M.IsComprehension a x A := by
  replace hM := hM.modelsComprehension
  simp only [comprehensionSchema, Theory.model_iff, Set.mem_setOf_eq, forall_exists_index] at hM
  obtain ⟨n, φ, vs, -, hφ⟩ := hA.isDefinable
  convert M.exists_isComprehension_of_models _ _ vs (hM φ.switchBound.comprehension n φ.switchBound rfl)
  simp only [switchBound, substBoundBound_substBoundBound, append_comp_append_natAdd_castAdd,
    multiclass_remap]
  funext x
  apply_fun (fun B ↦ B ![x]) at hφ
  convert hφ
  · norm_cast
  · sorry
  -- · simp? [Multiclass.toClass, Equiv.arrowCongr_apply, Equiv.coe_refl,
  --   Equiv.funUnique_symm_apply, Function.comp_apply, Multiclass.slice, Multiclass.remap, multiclass,
  --   append_comp_append_natAdd, append_comp_castAdd, id_eq, ← eq_iff_iff]
  --   congr
  --   ext i; fin_cases i; rfl

instance [M.ModelsComprehension] : M.ClosedUnderDefinableComprehension :=
  ⟨M.exists_isComprehension_of_modelsComprehension⟩

/-- The union axiom -/
def sUnionAxiom : L.Sentence := ∀' ∃' ∀' ∀' ((&3 ∈' &2 ⊓ &2 ∈' &0) ⟹ &3 ∈' &1)

class MemStructure.ModelsSUnion [HasMem M.L] : Prop where
  protected modelsSUnion : M ⊨ M.L.sUnionAxiom

-- theorem MemStructure.exists_isSUnion [hM₁ : M.ModelsSUnion]
--     [hM₂ : M.ModelsDeltaZeroComprehension] (x : M) :
--     ∃ a : M, M.IsSUnion a x := by
--   replace hM₁ := hM₁.modelsSUnion
--   have : ∀ (a : ↑M), ∃ a_1 : M, ∀ (a_2 a_3 : ↑M), a_3 ∈ a_2 → a_2 ∈ a → a_3 ∈ a_1 := by
--     simpa [Sentence.Realize, Formula.Realize, sUnionAxiom, snoc] using hM₁
--   obtain ⟨b, hb⟩ := this x
--   use ((&1).memSUnion &0)〘x, ∈b〙₀
--   suffices ∀ (y x_1 : ↑M), x_1 ∈ x → y ∈ x_1 → y ∈ b by simpa [IsSUnion, Term.memSUnion]
--   grind

-- instance [M.ModelsSUnion] [M.ModelsDeltaZeroComprehension] : M.ClosedUnderSUnion :=
  -- ⟨M.exists_isSUnion⟩

/-- The pairing axiom -/
def pairAxiom : L.Sentence := ∀' ∀' ∃' (&0 ∈' &2 ⊓ &1 ∈' &2)

class MemStructure.ModelsPair [HasMem M.L] : Prop where
  protected modelsPair : M ⊨ M.L.pairAxiom

-- theorem MemStructure.exists_isUnorderedPair [hM₁ : M.ModelsPair]
--     [hM₂ : M.ModelsDeltaZeroComprehension] (x y : M) :
--     ∃ a : M, M.IsUnorderedPair a x y := by
--   replace hM₁ := hM₁.modelsPair
--   have :  ∀ (a a_1 : ↑M), ∃ a_2 : M, a ∈ a_2 ∧ a_1 ∈ a_2 := by
--     simpa [Sentence.Realize, Formula.Realize, pairAxiom, snoc] using hM₁
--   obtain ⟨b, hb⟩ := this x y
--   use ((&2).memUnorderedPair &0 &1) 〘![x, y], ∈ b〙
--   simpa [IsUnorderedPair, Term.memUnorderedPair]

-- instance [M.ModelsPair] [M.ModelsDeltaZeroComprehension] : M.ClosedUnderPair :=
--   ⟨M.exists_isUnorderedPair⟩

/-- The power set axiom -/
def powersetAxiom : L.Sentence := ∀' ∃' ∀' (&2 ⊆' &0 ⟹ &2 ∈' &1)

class MemStructure.ModelsPowerset [HasMem M.L] : Prop where
  protected modelsPowerset : M ⊨ M.L.powersetAxiom

-- theorem MemStructure.exists_isPowerset [hM₁ : M.ModelsPowerset]
--     [hM₂ : M.ModelsDeltaZeroComprehension] (x : M) :
--     ∃ a : M, M.IsPowerset a x := by
--   replace hM₁ := hM₁.modelsPowerset
--   simp [powersetAxiom, snoc, IsPowerset]
--   have : ∀ (a : ↑M), ∃ a_1 : M, ∀ a_2 ⊆ a, a_2 ∈ a_1 := by
--     simp [powersetAxiom, snoc]
--   obtain ⟨b, hb⟩ := this x
--   use ((&1).subset &0) 〘x, ∈ b〙₀
--   suffices ∀ z ⊆ x, z ∈ b by simpa [IsPowerset]
--   grind

-- instance [M.ModelsPowerset] [M.ModelsDeltaZeroComprehension] : M.ClosedUnderPowerset :=
--   ⟨M.exists_isPowerset⟩

/-- The foundation axiom -/
def foundationAxiom : L.Sentence := ∀'((∃'(&1 ∈' &0)) ⟹ ∃'∈ &0 ∀'∈ &1 ∼(&2 ∈' &0))

class MemStructure.ModelsFoundation [HasMem M.L] : Prop where
  protected modelsFoundation : M ⊨ M.L.foundationAxiom

-- theorem MemStructure.exists_isMemMin [hM : M.ModelsFoundation]
--     [M.ModelsDeltaZeroComprehension] [M.ModelsExtensionality] (x : M) (hx : x ≠ ∅) :
--     ∃ a : M, M.IsMemMin a x := by
--   replace hM := hM.modelsFoundation
--   have : ∀ (y x : ↑M), x ∈ y → ∃ a ∈ y, ∀ a_1 ∈ a, a_1 ∉ y := by
--     simpa [foundationAxiom, snoc] using hM
--   simp [IsMemMin]
--   rw [ne_empty_iff] at hx

  -- using this x hx

-- instance [M.ModelsFoundation] [M.ModelsDeltaZeroComprehension] [M.ModelsExtensionality] :
--   M.Foundational := ⟨M.exists_isMemMin⟩

-- /-- The replacement axiom -/
-- def replacement (φ : L.BoundedFormula α (n + 3)) : L.Formula α :=
--   ∀'' ((∀'∈ &0 ∃!' φ) ⟹ ∃' (∀'∈ &0 ∃'∈ &-3 (φ.liftAt 1 (n + 1))))

-- /-- The infinity axiom -/
-- def infinity : L.Sentence := ∃' ((∃'∈ &0 (&1).isEmpty) ⊓ ∀'∈ &0 (∃'∈ &0 ((&2).eqSucc &1)))

-- /-- The axiom of choice -/
-- def choice : L.Sentence :=
--   ∀' (∼(&-1).isEmpty ⟹ ∃' ((&-2).isFun ⊓ (&-1).eqDom (&-2) ⊓
--     ∀' ∃' ((&-3).memDom (&-2) ⟹ ∼(&-3).isEmpty ⟹ ((&-4).eqVal &-2 &-3 ⊓ &-4 ∈' &-3))))

end Language

end FirstOrder
