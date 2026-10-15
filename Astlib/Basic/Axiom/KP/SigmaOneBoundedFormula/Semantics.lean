/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
-- import Astlib.Basic.SetOperation.MemStructure.Levy
import Astlib.Basic.Axiom.KP.SigmaOneBoundedFormula.Syntax
import Astlib.Basic.Axiom.KP.Semantics
import Astlib.Basic.SetOperation.Rudimentary.Semantics
import Astlib.Basic.SetOperation.Function
import Astlib.Basic.SetOperation.Foundational
import Astlib.Basic.SetOperation.Rudimentary.KP
import Astlib.Mathlib.Fin.Tuple.Basic
/-!
file docstring
-/

open FirstOrder Language BoundedFormula Theory Fin MemStructure DeltaZeroBoundedFormula

variable {L : FirstOrder.Language.{u, v}} {M : Type max u v}
  [L.MemStructure M] (x : M) (xs : Fin n → M)

namespace FirstOrder

namespace Language

namespace DeltaZeroBoundedFormula

variable [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [Extensional M]

/-- `φ.mergeLastTwo` holds at `p` iff `p` is the pair of some `y₁, y₂` at which `φ` holds. -/
theorem realize_mergeLastTwo [RudClosed M] (φ : L.DeltaZeroBoundedFormula (n + 2)) (y : M) :
    φ.mergeLastTwo.toBoundedFormula 〘snoc xs y〙 ↔
      ∃ y₁ y₂, y = !(y₁, y₂) ∧ φ.toBoundedFormula 〘snoc (snoc xs y₁) y₂〙 := by
  simp only [mergeLastTwo, Function.comp_apply, castAdd_add_one, Nat.add_zero, castAdd_zero,
    cast_eq_self, realize_exMemSUnion, Term.realize'_var', snoc_last, snoc_castSucc,
    toBoundedFormula_inf, coe_substBoundBound, realize'_inf, Term.realize_eqOrderedPair,
    realize'_substBoundBound, snoc_snoc_snoc_comp_snoc_snoc_castAdd_three]
  grind

/-- `φ.mergeLast m` holds at `p` iff `p` is an `(m + 1)`-tuple whose entries satisfy `φ`. -/
theorem realize_mergeLast [RudBasisClosed M] {n : ℕ} (m : ℕ) (φ : L.DeltaZeroBoundedFormula (n + m + 1))
    (xs : Fin n → M) (p : M) :
    (φ.mergeLast m).toBoundedFormula 〘snoc xs p〙 ↔
      IsTuple p (m + 1) ∧
        φ.toBoundedFormula 〘(append xs (tupleVal p) : Fin (n + (m + 1)) → M)〙 := by
  induction m generalizing n p with
  | zero =>
    simp [mergeLast, tupleVal_one, append_right_eq_snoc]
  | succ m ih =>
    simp only [mergeLast, realize_mergeLastTwo, coe_substBoundBound, realize'_substBoundBound,
      snoc_snoc_comp_snoc_snoc_castAdd_two, ih]
    constructor
    · rintro ⟨p', y, rfl, hp', h⟩
      simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        isTuple_unorderedPair_iff]
      simp only [append_snoc_comp_snoc_append_castAdd_natAdd] at h
      refine ⟨hp', ?_⟩
      rwa [tupleVal_orderedPair_eq_snoc_tupleval _ _ (by omega), append_snoc]
    · rintro ⟨⟨ys, rfl⟩, h⟩
      rw [tuple_succ] at h ⊢
      rw [tupleVal_orderedPair_eq_snoc_tupleval _ _ (by omega), append_snoc] at h
      refine ⟨_, _, rfl, isTuple_tuple _, ?_⟩
      rwa [append_snoc_comp_snoc_append_castAdd_natAdd]

end DeltaZeroBoundedFormula

namespace SigmaOneBoundedFormula

variable (φ ψ : L.SigmaOneBoundedFormula n)

@[simp]
theorem realize_top [Inhabited M] : (⊤ : L.SigmaOneBoundedFormula n).toBoundedFormula 〘xs〙 := by
  simp [toBoundedFormula, Top.top]

@[simp]
theorem realize_bot : ¬(⊥ : L.SigmaOneBoundedFormula n).toBoundedFormula 〘xs〙 := by
  simp [toBoundedFormula]

@[simp]
theorem realize_sup : (φ ⊔ ψ).toBoundedFormula 〘xs〙 ↔ φ.toBoundedFormula 〘xs〙 ∨ ψ.toBoundedFormula 〘xs〙 := by
  simp only [toBoundedFormula, max, sup, toBoundedFormula_sup', realize'_ex, realize'_imp,
    realize'_not]
  grind

-- /-- The relation defined by a `Σ₁` formula with parameters `vs` -/
-- def toMulticlass (φ : L.SigmaOneBoundedFormula (n + 2)) (vs : Fin n → M) : Multiclass M 2 :=
--   (switchBound (n := n) (p := 2) φ.toBoundedFormula).multiclass.slice vs

-- -- @[simp]
-- theorem toMulticlass_iff (φ : L.SigmaOneBoundedFormula (n + 2)) (vs : Fin n → M) (u w : M) :
--     φ.toMulticlass vs ![u, w] ↔ φ.toBoundedFormula〘snoc (snoc vs u) w〙 := by
--   simp [toMulticlass, snoc_snoc_eq_append]

@[simp]
theorem realize_allMem [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] (φ : L.SigmaOneBoundedFormula (n + 1)) (t : L.Term' n) :
    (∀₁∈ t φ).toBoundedFormula 〘xs〙 ↔ ∀ y ∈ t〘xs〙, φ.toBoundedFormula 〘snoc xs y〙 := by
  simp only [toBoundedFormula, allMem, Term.castSucc, Term.castAdd, Term.castLE,
    castLE_succ_castSucc, Function.comp_apply, DeltaZeroBoundedFormula.toBoundedFormula,
    toBoundedFormula_exMem, coe_substBoundBound, realize'_ex, BoundedFormula.realize_allMem,
    Term.realize'_substBoundBound, snoc_comp_castSucc, realize_exMem, Term.realize'_var',
    snoc_snoc_castAdd_one_last, realize'_substBoundBound,
    snoc_snoc_snoc_comp_snoc_snoc_castAdd_three]
  refine ⟨by grind, fun h ↦ ?_⟩
  simpa [snoc_snoc_eq_append] using exists_collection_of_modelsKP
    ((switchBound (n := n) (p := 2) φ.deltaZeroBody.toBoundedFormula).multiclass.slice xs)
    t〘xs〙 (by simpa [snoc_snoc_eq_append] using h)

theorem realize_iff_deltaZeroBody :
    φ.toBoundedFormula 〘xs〙 ↔ ∃ y, φ.deltaZeroBody.toBoundedFormula 〘snoc xs y〙 := by
  simp [toBoundedFormula]

@[simp]
theorem realize_toSigmaOneBoundedFormula [Inhabited M] (ψ : L.DeltaZeroBoundedFormula n) :
    ψ.toSigmaOneBoundedFormula.toBoundedFormula 〘xs〙 ↔ ψ.toBoundedFormula 〘xs〙 := by
  simp [toBoundedFormula, toSigmaOneBoundedFormula, Function.comp_def]

@[simp]
theorem realize_substBoundBound (f : Fin n → Fin m) (xs : Fin m → M) :
    (φ.substBoundBound f).toBoundedFormula 〘xs〙 ↔ φ.toBoundedFormula 〘xs ∘ f〙 := by
  simp [toBoundedFormula, substBoundBound]

instance (φ : L.SigmaOneBoundedFormula n) : φ.toBoundedFormula.Sigma 1 := by
  unfold toBoundedFormula
  infer_instance

-- instance (φ : L.SigmaOneBoundedFormula (n + 2)) (vs : Fin n → M) :
--     (φ.toMulticlass vs).Sigma 1 Set.univ := by
--   unfold toMulticlass
--   infer_instance

section

variable [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [Extensional M] [RudClosed M]

@[simp]
theorem realize_ex (φ : L.SigmaOneBoundedFormula (n + 1)) :
    (∃₁ φ).toBoundedFormula 〘xs〙 ↔ ∃ y, φ.toBoundedFormula 〘snoc xs y〙 := by
  simp only [toBoundedFormula, ex, realize'_ex, realize_mergeLastTwo]
  grind

@[simp]
theorem realize_inf (φ ψ : L.SigmaOneBoundedFormula n) :
    (φ ⊓ ψ).toBoundedFormula 〘xs〙 ↔ φ.toBoundedFormula 〘xs〙 ∧ ψ.toBoundedFormula 〘xs〙 := by
  simp [min, toBoundedFormula, inf, realize_mergeLastTwo]

@[simp]
theorem realize_ex' (m : ℕ) (φ : L.SigmaOneBoundedFormula (n + m)) :
    (ex' m φ).toBoundedFormula 〘xs〙 ↔ ∃ ys : Fin m → M, φ.toBoundedFormula 〘append xs ys〙 := by
  induction m with
  | zero => simp [ex', append_right_nil]
  | succ m ih => simp [ex', ih, exists_fin_succ_pi', append_snoc]

end

end SigmaOneBoundedFormula

namespace MemStructure

variable [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M]

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] in
/-- `∈`-induction -/
theorem induction_of_modelsKP [hM : ModelsKP M] {A : Class M} [hA : A.Definable Set.univ]
    (h : ∀ x, (∀ y ∈ x, A y) → A x) (x : M) : A x := by
  obtain ⟨n, φ, vs, -, hφ⟩ := hA.isDefinable
  simp only [Class.iff_toMulticlass, hφ, Multiclass.slice, multiclass] at h ⊢
  replace hM := hM.modelsKP
  simp only [KP, model_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    realize_iff_realize'] at hM
  have : φ.switchBound.recursion ∈ recursionSchema := ⟨n, φ.switchBound, rfl⟩
  specialize hM φ.switchBound.recursion (by simp [this])
  simp only [recursion, Function.comp_apply, realize'_alls, realize'_imp, realize'_all,
    realize_allMem, Term.realize'_var', snoc_last, realize'_substBoundBound,
    snoc_snoc_comp_snoc_castAdd_two_last] at hM
  simp only [snoc_eq_append, realize'_switchBound] at hM
  exact hM vs h x

instance [ModelsKP M] : Foundational M where
  hasMemMin x hx := by
    have := induction_of_modelsKP (A := ∼(toClass x))
    contrapose! this
    simp only [IsMemMin, not_and, not_forall, not_not] at this
    simp only [toClass, Class.not_iff, Class.mem_iff, not_not]
    exact ⟨by grind, by rwa [ne_empty_iff] at hx⟩

/-- A `Σ₁` relation is defined by a `Σ₁` formula with finitely many parameters. -/
theorem Multiclass.exists_sigmaOneBoundedFormula [Extensional M] [RudClosed M] {n : ℕ} (F : Multiclass M n)
    [hF : F.Sigma 1 Set.univ] :
    ∃ (k : ℕ) (θ : L.SigmaOneBoundedFormula (n + k)) (vs : Fin k → M),
      F = θ.toBoundedFormula.multiclass.slice vs := by
  obtain ⟨k, φ, hφ, vs, -, rfl⟩ := hF.isSigma
  obtain ⟨l, ψ, hψ, rfl⟩ := hφ.isSigma.exists_Pi_ex'
  obtain ⟨ψ₀, rfl⟩ : ψ.IsDeltaZero := by simpa using hψ
  refine ⟨k, ψ₀.toSigmaOneBoundedFormula.ex' l, vs, ?_⟩
  funext xs
  simp

/-- Every `Σ₁` relation is defined by a `Σ₁` formula with a single parameter. -/
theorem Multiclass.exists_sigmaOneBoundedFormula_add_one [Extensional M] [RudBasisClosed M] {n : ℕ} (F : Multiclass M n)
    [F.Sigma 1 Set.univ] :
    ∃ (θ : L.SigmaOneBoundedFormula (n + 1)) (v : M),
      F = θ.toBoundedFormula.multiclass.slice₀ v := by
  obtain ⟨k, θ, vs, rfl⟩ := Multiclass.exists_sigmaOneBoundedFormula F
  cases k with
  | zero =>
    refine ⟨θ.substBoundBound castSucc, ∅, ?_⟩
    funext xs
    simp [Multiclass.slice₀, append_right_eq_snoc, append_right_nil]
  | succ k =>
    refine ⟨⟨((θ.deltaZeroBody.switchBoundRight.castAssoc' :
      L.DeltaZeroBoundedFormula (n + 1 + (k + 1))).mergeLast k).substBoundBound
        (snoc (snoc (castAdd 2) (last _)) (last _).castSucc)⟩, tuple vs, ?_⟩
    funext xs
    simp only [Multiclass.slice₀, Multiclass.slice, multiclass,
      SigmaOneBoundedFormula.toBoundedFormula, realize'_ex, coe_substBoundBound,
      realize'_substBoundBound, append_right_eq_snoc, Matrix.cons_val_fin_one,
      snoc_snoc_comp_snoc_snoc_castAdd_two, realize_mergeLast, isTuple_tuple, tupleVal_tuple,
      true_and]
    simp only [snoc_eq_append, coe_castAssoc', coe_switchBoundRight, realize'_castAssoc',
      realize'_switchBoundRight]
    simp [append_assoc]

/-- Strong `Σ₁`-collection -/
theorem exists_strong_collection_of_modelsKP [ModelsKP M] (F : Multiclass M 2)
    [F.Sigma 1 Set.univ] (a : M) (h : ∀ u ∈ a, ∃ w, F ![u, w]) :
    ∃ b : M, (∀ u ∈ a, ∃ w ∈ b, F ![u, w]) ∧ ∀ w ∈ b, ∃ u ∈ a, F ![u, w] := by
  obtain ⟨φ, v, rfl⟩ := Multiclass.exists_sigmaOneBoundedFormula_add_one F
  simp only [Multiclass.slice₀, Multiclass.slice, multiclass, Nat.reduceAdd,
    SigmaOneBoundedFormula.toBoundedFormula, append_right_eq_snoc, isValue, Matrix.cons_val_fin_one,
    Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty, realize'_ex] at h ⊢
  -- collect sets `c` containing some `w` and a witness `q` of the `Δ₀` body of `φ(u, w, v)`
  obtain ⟨b₀, hb₀⟩ := exists_collection_of_modelsKP
    ((∃₀∈ &1 ∃₀∈ &1 (φ.deltaZeroBody.substBoundBound ![0, 3, 2, 4])).toBoundedFormula.multiclass.slice₀ v) a (fun u hu ↦ by
        obtain ⟨w, q, hq⟩ := h u hu
        refine ⟨!{w, q}, ?_⟩
        simp [append_right_eq_snoc, Matrix.empty_eq, hq])
  simp only [Multiclass.slice₀, Multiclass.slice, multiclass, Nat.reduceAdd, isValue,
    Function.comp_apply, toBoundedFormula_exMem, coe_substBoundBound, append_right_eq_snoc,
    Matrix.cons_val_fin_one, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty, realize_exMem,
    Term.realize'_var', Matrix.cons_val_one, Matrix.cons_val_zero, realize'_substBoundBound,
    Matrix.comp_vecCons, Matrix.cons_val, Matrix.empty_eq] at hb₀
  -- separate the `w ∈ ⋃₀ b₀` with some `u ∈ a` and `q ∈ ⋃₀ b₀` witnessing `φ(u, w, v)`
  refine ⟨⋃₀ b₀ ∩₀ (((switchBound
    (∃₀∈ &0 ∃₀∈⋃₀ &1 (φ.deltaZeroBody.substBoundBound ![4, 3, 2, 5])).toBoundedFormula).multiclass.slice ![a, b₀, v] :
        Multiclass M 1) : Class M), ?_, ?_⟩
  all_goals simp only [Nat.reduceAdd, isValue, Function.comp_apply, toBoundedFormula_exMem,
    mem_comprehension_iff, Multiclass.toClass_iff, Multiclass.slice, multiclass,
    realize'_switchBound, append_right_eq_snoc, Matrix.cons_val_fin_one, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty, realize_exMem, Term.realize'_var', Matrix.cons_val_zero,
    realize_exMemSUnion, Matrix.cons_val_one, coe_substBoundBound, realize'_substBoundBound,
    Matrix.comp_vecCons, Matrix.cons_val, Matrix.empty_eq, and_imp, forall_exists_index]
  all_goals grind

/-- `Σ₁`-replacement -/
instance [ModelsKP M] (x : M) (F : Multiclass M 2) [F.Sigma 1 Set.univ] :
  HasReplacement x F where
  hasReplacement hFx := by
    obtain ⟨b, hb₁, hb₂⟩ := exists_strong_collection_of_modelsKP F x fun u hu ↦ (hFx u hu).exists
    refine ⟨b, fun z ↦ ⟨hb₂ z, fun ⟨u, hu, hz⟩ ↦ ?_⟩⟩
    obtain ⟨w, hw, hw'⟩ := hb₁ u hu
    rwa [(hFx u hu).unique hz hw']

/-- `Δ₁`-comprehension -/
instance [ModelsKP M] (x : M) (A : Class M) [A.Delta 1 Set.univ] : HasComprehension x A where
  hasComprehension := by
    -- `G` maps `u` to `{u}` if `A u`, and to `∅` otherwise
    let G : Multiclass M 2 :=
      ((A : Multiclass M 1).remap ![0] ⊓ ((&1).eqSingleton &0).toBoundedFormula.multiclass) ⊔
        ((∼(A : Multiclass M 1)).remap ![0] ⊓ (∀₀∈ &1 ⊥).toBoundedFormula.multiclass)
    have hG (u w : M) : G ![u, w] ↔ (A u ∧ w = {u}) ∨ (¬A u ∧ w = ∅) := by
      simp [G, empty_iff]
    have hGx : ∀ u ∈ x, ∃! w, G ![u, w] := by
      intro u hu
      by_cases hu : A u
      · exact ⟨{u}, by grind⟩
      · exact ⟨∅, by grind⟩
    refine ⟨⋃₀ (G ''₀ x), fun z ↦ ?_⟩
    simp only [mem_sUnion_iff, mem_replacement_iff hGx, hG]
    grind

end MemStructure

end FirstOrder.Language
