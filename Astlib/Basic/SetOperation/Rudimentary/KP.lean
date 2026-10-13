/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Axiom.KP.Semantics
import Astlib.Basic.SetOperation.Rudimentary.Basis.Semantics
import Astlib.Basic.SetOperation.Replacement
/-!
file docstring
-/

namespace FirstOrder

namespace Language

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin MemStructure RudimentaryTerm

namespace MemStructure

variable {L : FirstOrder.Language.{u, v}} {M : Type max u v}
  [L.MemStructure M] [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M]

instance [hM : ModelsKP M] : Extensional M where
  extensional := by
    replace hM := hM.modelsKP
    simp only [KP, Theory.model_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      realize_iff_realize'] at hM
    specialize hM extensionalityAxiom (by simp)
    simpa [extensionalityAxiom, snoc_nat] using hM

instance [hM : ModelsKP M] (A : Class M) [hA : A.DeltaZero Set.univ] : HasComprehension x A where
  hasComprehension := by
    replace hM := hM.modelsKP
    simp only [KP, Theory.model_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      realize_iff_realize'] at hM
    obtain ⟨n, φ, _, vs, _, hA⟩ := hA.toDeltaZero
    have : φ.switchBound.comprehension ∈ deltaZeroComprehensionSchema :=
      ⟨n, φ.switchBound, by infer_instance, rfl⟩
    specialize hM φ.switchBound.comprehension (by simp [this])
    simp only [BoundedFormula.comprehension, Function.comp_apply, realize'_alls, realize'_ex,
      realize'_all, realize'_iff, realize'_mem, Term.realize'_var', snoc_snoc_castAdd_one_last,
      snoc_last, realize'_inf, realize'_substBoundBound] at hM
    obtain ⟨a, ha⟩ := hM (snoc vs x)
    use a
    intro z
    rw [ha]
    simp only [snoc_nat, val_castAdd, val_last, Order.lt_add_one_iff, le_add_iff_nonneg_right,
      _root_.zero_le, ↓reduceDIte, lt_add_iff_pos_right, Order.lt_one_iff, lt_self_iff_false,
      snoc_snoc_snoc_comp_snoc_castAdd_three_last, and_congr_right_iff]
    simp only [snoc_eq_append, Nat.reduceAdd, realize'_switchBound, Class.iff_toMulticlass, hA,
      Multiclass.slice, multiclass]
    intro _
    rfl

theorem sdiffClosed_of_modelsKP [hM : ModelsKP M] (x y : M) : ∃ a, IsSDiff a x y :=
  ⟨x ∩₀ ∼(toClass y), by simp [IsSDiff, toClass]⟩

instance [hM : ModelsKP M] : SDiffClosed M := ⟨sdiffClosed_of_modelsKP⟩

theorem pairClosed_of_modelsKP [hM : ModelsKP M] (x y : M) : ∃ a, IsUnorderedPair a x y := by
  have hM := hM.modelsKP
  simp only [KP, Theory.model_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    realize_iff_realize'] at hM
  specialize hM pairAxiom (by simp)
  simp only [pairAxiom, Nat.reduceAdd, isValue, Function.comp_apply, realize'_all, realize'_ex,
    realize'_inf, realize'_mem, Term.realize'_var', snoc_nat, coe_ofNat_eq_mod, Nat.mod_succ,
    lt_self_iff_false, ↓reduceDIte, Nat.zero_mod, Order.lt_two_iff, _root_.zero_le, zero_eta,
    Order.lt_one_iff, Nat.one_mod, Std.le_refl, mk_one] at hM
  obtain ⟨b, hb⟩ := hM x y
  use b ∩₀ (Class.Eq x ⊔ Class.Eq y)
  intro z
  simp only [mem_comprehension_iff, Class.sup_iff, Class.eq_iff, and_iff_right_iff_imp]
  grind

instance [hM : ModelsKP M] : PairClosed M := ⟨pairClosed_of_modelsKP⟩


/-- Δ₀-collection, stated for formulas -/
theorem exists_collection_of_modelsKP [hM : ModelsKP M] {n : ℕ}
    (φ : L.BoundedFormula' (n + 2)) [hφ : φ.DeltaZero] (vs : Fin n → M) (a : M)
    (h : ∀ u ∈ a, ∃ w, φ〘snoc (snoc vs u) w〙) :
    ∃ b : M, ∀ u ∈ a, ∃ w ∈ b, φ〘snoc (snoc vs u) w〙 := by
  replace hM := hM.modelsKP
  simp only [KP, Theory.model_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    realize_iff_realize'] at hM
  have : φ.collection ∈ deltaZeroCollectionSchema := ⟨n, φ, hφ, rfl⟩
  specialize hM φ.collection (by simp [this])
  simp only [BoundedFormula.collection, realize'_alls, realize'_ex, realize'_imp,
    BoundedFormula.realize_allMem, BoundedFormula.realize_exMem, realize'_substBoundBound] at hM
  simpa using hM (snoc vs a) (by simpa using h)

theorem hasReplacement_of_modelsKP [ModelsKP M] (x : M) (F : Multiclass M 2)
    [hF : F.DeltaZero Set.univ] (hFx : F.IsFunctionalOn x) : HasReplacement x F := by
  obtain ⟨m, φ, hφ, vs, -, rfl⟩ := hF.isDeltaZero
  have hφ (u w : M) : (φ.multiclass.slice vs : Multiclass M 2) ![u, w] ↔
      φ.switchBound〘snoc (snoc vs u) w〙 := by
    simp [snoc_snoc_eq_append]
  obtain ⟨b, hb⟩ := exists_collection_of_modelsKP φ.switchBound vs x
    (fun u hu ↦ (hFx u hu).exists.imp fun w hw ↦ (hφ u w).1 hw)
  -- `g` sends the variables `(u, w, vs)` of `φ` to their positions in `(z, vs, x, u)`
  let g : Fin (2 + m) → Fin (1 + (m + 1) + 1) :=
    append ![last _, (Fin.castAdd (m + 1) 0).castSucc]
      (fun i ↦ ((i.castSucc).natAdd 1).castSucc)
  have hg (z u : M) : snoc (append ![z] (snoc vs x)) u ∘ g = append ![u, z] vs := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · fin_cases j <;>
        simp [g, snoc_castSucc (α := fun _ ↦ M), append_left]
    · simp only [g, Function.comp_apply, append_right, snoc_castSucc (α := fun _ ↦ M)]
  let χ : L.BoundedFormula' (1 + (m + 1)) := ∃'∈ &(natAdd 1 (last m)) (φ.substBoundBound g)
  refine ⟨⟨b ∩₀ χ.multiclass.slice (snoc vs x), fun z ↦ ?_⟩⟩
  rw [mem_comprehension_iff, Multiclass.toClass_iff]
  simp only [Multiclass.slice, BoundedFormula.multiclass] at hφ
  simp only [Multiclass.slice, BoundedFormula.multiclass, χ, BoundedFormula.realize_exMem,
    realize'_substBoundBound, hg, Term.realize'_var', Function.comp_apply, append_right, snoc_last,
    and_iff_right_iff_imp, forall_exists_index, and_imp]
  intro u hu hz
  obtain ⟨w, hwb, hw⟩ := hb u hu
  obtain rfl : w = z := (hFx u hu).unique (by simpa [hφ] using hw) (by simpa [hφ] using hz)
  exact hwb

instance [ModelsKP M] (x : M) (F : Multiclass M 2) [F.DeltaZero Set.univ]
    [hFx : Fact (F.IsFunctionalOn x)] : HasReplacement x F :=
  hasReplacement_of_modelsKP x F hFx.out

/-- `∃ x ∈ ⋃₀ t, φ (..., x)`, i.e. `∃ u ∈ t, ∃ x ∈ u, φ (..., x)` -/
def _root_.FirstOrder.Language.DeltaZeroBoundedFormula.exMemSUnion {L : Language} [L.HasMem]
    {n : ℕ} (t : L.Term' n) (φ : L.DeltaZeroBoundedFormula (n + 1)) :
    L.DeltaZeroBoundedFormula n :=
  ∃₀∈ t (∃₀∈ &-1 (φ.substBoundBound (snoc (castAdd 2) (last _))))

@[inherit_doc] scoped[FirstOrder]
notation "∃₀∈⋃₀ " x:arg y:50 => FirstOrder.Language.DeltaZeroBoundedFormula.exMemSUnion x y

/-- `∀ x ∈ ⋃₀ t, φ (..., x)`, i.e. `∀ u ∈ t, ∀ x ∈ u, φ (..., x)` -/
def _root_.FirstOrder.Language.DeltaZeroBoundedFormula.allMemSUnion {L : Language} [L.HasMem]
    {n : ℕ} (t : L.Term' n) (φ : L.DeltaZeroBoundedFormula (n + 1)) :
    L.DeltaZeroBoundedFormula n :=
  ∀₀∈ t (∀₀∈ &-1 (φ.substBoundBound (snoc (castAdd 2) (last _))))

@[inherit_doc] scoped[FirstOrder]
notation "∀₀∈⋃₀ " x:arg y:50 => FirstOrder.Language.DeltaZeroBoundedFormula.allMemSUnion x y

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] in
@[simp]
theorem realize_exMemSUnion {n : ℕ} (t : L.Term' n) (φ : L.DeltaZeroBoundedFormula (n + 1))
    (xs : Fin n → M) :
    (∃₀∈⋃₀ t φ).toBoundedFormula〘xs〙 ↔ ∃ u ∈ t〘xs〙, ∃ x ∈ u, φ.toBoundedFormula〘snoc xs x〙 := by
  simp [DeltaZeroBoundedFormula.exMemSUnion]

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] in
@[simp]
theorem realize_allMemSUnion {n : ℕ} (t : L.Term' n) (φ : L.DeltaZeroBoundedFormula (n + 1))
    (xs : Fin n → M) :
    (∀₀∈⋃₀ t φ).toBoundedFormula〘xs〙 ↔ ∀ u ∈ t〘xs〙, ∀ x ∈ u, φ.toBoundedFormula〘snoc xs x〙 := by
  simp [DeltaZeroBoundedFormula.allMemSUnion]

/-- The Δ₀ formula `t₁ = {t₂, t₃}` -/
def _root_.FirstOrder.Language.Term.eqUnorderedPair {L : Language} [L.HasMem] {n : ℕ}
    (t₁ t₂ t₃ : L.Term' n) : L.DeltaZeroBoundedFormula n :=
  (∀₀∈ t₁ (&-1 =₀ t₂.castSucc ⊔ &-1 =₀ t₃.castSucc)) ⊓ (t₂ ∈₀ t₁ ⊓ t₃ ∈₀ t₁)

/-- The Δ₀ formula `t₁ = (t₂, t₃)` -/
def _root_.FirstOrder.Language.Term.eqOrderedPair {L : Language} [L.HasMem] {n : ℕ}
    (t₁ t₂ t₃ : L.Term' n) : L.DeltaZeroBoundedFormula n :=
  (∀₀∈ t₁ ((&-1).eqUnorderedPair t₂.castSucc t₂.castSucc ⊔
      (&-1).eqUnorderedPair t₂.castSucc t₃.castSucc)) ⊓
    ((∃₀∈ t₁ (&-1).eqUnorderedPair t₂.castSucc t₂.castSucc) ⊓
      (∃₀∈ t₁ (&-1).eqUnorderedPair t₂.castSucc t₃.castSucc))

@[simp]
theorem realize_eqUnorderedPair [PairClosed M] [SDiffClosed M] [Extensional M] {n : ℕ}
    (t₁ t₂ t₃ : L.Term' n) (xs : Fin n → M) :
    (t₁.eqUnorderedPair t₂ t₃).toBoundedFormula〘xs〙 ↔ t₁〘xs〙 = !{(t₂〘xs〙 : M), t₃〘xs〙} := by
  simp [Term.eqUnorderedPair, eq_unorderedPair_iff (t₂〘xs〙 : M) (t₃〘xs〙) (t₁〘xs〙)]

@[simp]
theorem realize_eqOrderedPair [PairClosed M] [SDiffClosed M] [Extensional M] {n : ℕ}
    (t₁ t₂ t₃ : L.Term' n) (xs : Fin n → M) :
    (t₁.eqOrderedPair t₂ t₃).toBoundedFormula〘xs〙 ↔ t₁〘xs〙 = !((t₂〘xs〙 : M), t₃〘xs〙) := by
  simp [Term.eqOrderedPair, eq_orderedPair_iff]

/-- The Δ₀ formula `t = ((t₁, t₂), t₃)` -/
def _root_.FirstOrder.Language.Term.eqTriple {L : Language} [L.HasMem] {n : ℕ}
    (t t₁ t₂ t₃ : L.Term' n) : L.DeltaZeroBoundedFormula n :=
  ∃₀∈⋃₀ t ((&-1).eqOrderedPair t₁.castSucc t₂.castSucc ⊓ t.castSucc.eqOrderedPair &-1 t₃.castSucc)

@[simp]
theorem realize_eqTriple [PairClosed M] [SDiffClosed M] [Extensional M] {n : ℕ}
    (t t₁ t₂ t₃ : L.Term' n) (xs : Fin n → M) :
    (t.eqTriple t₁ t₂ t₃).toBoundedFormula〘xs〙 ↔ t〘xs〙 = !(!((t₁〘xs〙 : M), t₂〘xs〙), t₃〘xs〙) := by
  simp only [Term.eqTriple, realize_exMemSUnion, toBoundedFormula_inf, realize'_inf,
    realize_eqOrderedPair]
  simp only [Function.comp_apply, Term.realize'_var', snoc_last, Term.castSucc, Term.castAdd,
    Term.castLE, castLE_succ_castSucc, Term.realize'_substBoundBound, snoc_comp_castSucc,
    ↓existsAndEq, true_and]
  refine ⟨fun ⟨_, _, _, h⟩ ↦ h,
    fun h ↦ ⟨!{!((t₁〘xs〙 : M), t₂〘xs〙), !((t₁〘xs〙 : M), t₂〘xs〙)}, ?_, by simp, h⟩⟩
  simp [h]

theorem sUnionClosed_of_modelsKP [hM : ModelsKP M] (x : M) : ∃ a, IsSUnion₀ a x := by
  have hM := hM.modelsKP
  simp only [KP, Theory.model_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    realize_iff_realize'] at hM
  specialize hM sUnionAxiom (by simp)
  simp only [sUnionAxiom, Function.comp_apply, realize'_all, realize'_ex, realize'_imp,
    realize'_inf, realize'_mem, Term.realize'_var'] at hM
  obtain ⟨b, hb⟩ := hM x
  simp only [snoc_nat] at hb
  refine ⟨b ∩₀ (∃₀∈ &1 (&0 ∈₀ &2) : L.DeltaZeroBoundedFormula 2).toBoundedFormula.multiclass.slice₀
    x, fun z ↦ ?_⟩
  rw [mem_comprehension_iff, Multiclass.toClass_iff]
  simp only [Multiclass.slice₀, Multiclass.slice, BoundedFormula.multiclass]
  simp only [isValue, Function.comp_apply, Nat.reduceAdd, toBoundedFormula_exMem, toBoundedFormula,
    append_right_eq_snoc, Matrix.cons_val_fin_one, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty, BoundedFormula.realize_exMem, Term.realize'_var', Matrix.cons_val_one,
    realize'_mem, Matrix.cons_val, Matrix.cons_val_zero, and_iff_right_iff_imp, forall_exists_index,
    and_imp]
  exact fun u hu hzu ↦ hb u z ⟨hzu, hu⟩

theorem exists_sprod_of_modelsKP [hM : ModelsKP M] (x y : M) :
    ∃ a : M, ∀ z, z ∈ a ↔ ∃ u ∈ x, ∃ v ∈ y, z = !(u, v) := by
  -- `F u` maps `v` to `(u, v)`
  let F (u : M) :=
    ((&1).eqOrderedPair &2 &0 : L.DeltaZeroBoundedFormula 3).toBoundedFormula.multiclass.slice₀ u
  have hF (u v w : M) : F u ![v, w] ↔ w = !(u, v) := by
    simp only [F, Multiclass.slice₀, Multiclass.slice, BoundedFormula.multiclass]
    simp [append_right_eq_snoc]
  have (u : M) : HasReplacement y (F u) := hasReplacement_of_modelsKP y (F u)
    fun v _ ↦ ⟨!(u, v), by simp [hF], fun w hw ↦ by simpa [hF] using hw⟩
  have hFy (u t : M) : t ∈ F u ''₀ y ↔ ∃ v ∈ y, t = !(u, v) := by simp [hF]
  -- `G` maps `u` to `{(u, v) | v ∈ y}`
  let G := ((∀₀∈ &1 (∃₀∈ &2 ((&3).eqOrderedPair &0 &4))) ⊓
      (∀₀∈ &2 (∃₀∈ &1 ((&4).eqOrderedPair &0 &3))) :
    L.DeltaZeroBoundedFormula 3).toBoundedFormula.multiclass.slice₀ y
  have hG (u c : M) : G ![u, c] ↔ ∀ t, t ∈ c ↔ ∃ v ∈ y, t = !(u, v) := by
    simp only [G, Multiclass.slice₀, Multiclass.slice, BoundedFormula.multiclass]
    simp only [isValue, Function.comp_apply, Nat.reduceAdd, toBoundedFormula_inf, toBoundedFormula,
      toBoundedFormula_exMem, append_right_eq_snoc, Matrix.cons_val_fin_one,
      Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty, realize'_inf,
      BoundedFormula.realize_allMem, Term.realize'_var', Matrix.cons_val_one, Matrix.cons_val_zero,
      BoundedFormula.realize_exMem, Matrix.cons_val, realize_eqOrderedPair, exists_eq_right]
    grind
  have : HasReplacement x G := hasReplacement_of_modelsKP x G
    fun u _ ↦ ⟨F u ''₀ y, (hG _ _).mpr (hFy u),
      fun c hc ↦ by ext t; rw [(hG _ _).mp hc, hFy]⟩
  obtain ⟨S, hS⟩ := sUnionClosed_of_modelsKP (G ''₀ x)
  refine ⟨S, fun z ↦ ?_⟩
  rw [hS z]
  simp only [mem_replacement_iff, hG]
  refine ⟨by grind, ?_⟩
  rintro ⟨u, hu, v, hv, rfl⟩
  exact ⟨F u ''₀ y, ⟨u, hu, hFy u⟩, (hFy u _).2 ⟨v, hv, rfl⟩⟩

theorem sprodClosed_of_modelsKP [hM : ModelsKP M] (x y : M) : ∃ a, IsSProd₀ a x y :=
  exists_sprod_of_modelsKP x y

theorem switchClosed_of_modelsKP [hM : ModelsKP M] (x y : M) : ∃ a, IsSwitch₀ a x y := by
  obtain ⟨Ux, hUx⟩ := sUnionClosed_of_modelsKP x
  obtain ⟨UUx, hUUx⟩ := sUnionClosed_of_modelsKP Ux
  obtain ⟨UUx_y, hUUx_y⟩ := exists_sprod_of_modelsKP UUx y
  obtain ⟨UUx_y_UUx, hUUx_y_UUx⟩ := exists_sprod_of_modelsKP UUx_y UUx
  refine ⟨UUx_y_UUx ∩₀ (∃₀∈ &1 (∃₀∈⋃₀ &3 (∃₀∈⋃₀ &3 (∃₀∈ &2
      ((&3).eqOrderedPair &4 &5 ⊓ (&0).eqTriple &4 &6 &5)))) :
      L.DeltaZeroBoundedFormula 3).toBoundedFormula.multiclass.slice
    ![x, y], fun z ↦ ?_⟩
  rw [mem_comprehension_iff, Multiclass.toClass_iff]
  simp only [Multiclass.slice, BoundedFormula.multiclass]
  simp only [isValue, Function.comp_apply, Nat.reduceAdd, toBoundedFormula_exMem,
    Nat.succ_eq_add_one, append_left_eq_cons, Matrix.cons_val_fin_one, Matrix.Fin.cons_vecCons,
    cast_refl, Function.comp_id, BoundedFormula.realize_exMem, Term.realize'_var',
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty,
    realize_exMemSUnion, Matrix.cons_val, toBoundedFormula_inf, realize'_inf, realize_eqOrderedPair,
    realize_eqTriple, ↓existsAndEq, mem_orderedPair_iff, true_and, exists_and_left]
  refine ⟨by grind, ?_⟩
  rintro ⟨u, v, w, hw, huv, rfl⟩
  have hu : u ∈ UUx := (hUUx u).mpr ⟨!{u, v}, (hUx _).mpr ⟨!(u, v), huv, by simp⟩, by simp⟩
  have hv : v ∈ UUx := (hUUx v).mpr ⟨!{u, v}, (hUx _).mpr ⟨!(u, v), huv, by simp⟩, by simp⟩
  grind

theorem rotateClosed_of_modelsKP [hM : ModelsKP M] (x y : M) : ∃ a, IsRotate₀ a x y := by
  obtain ⟨Ux, hUx⟩ := sUnionClosed_of_modelsKP x
  obtain ⟨UUx, hUUx⟩ := sUnionClosed_of_modelsKP Ux
  obtain ⟨y_UUx, hy_UUx⟩ := exists_sprod_of_modelsKP y UUx
  obtain ⟨y_UUx_UUx, hy_UUx_UUx⟩ := exists_sprod_of_modelsKP y_UUx UUx
  refine ⟨y_UUx_UUx ∩₀ (∃₀∈ &1 (∃₀∈⋃₀ &3 (∃₀∈⋃₀ &3 (∃₀∈ &2
      ((&3).eqOrderedPair &4 &5 ⊓ (&0).eqTriple &6 &4 &5)))) :
      L.DeltaZeroBoundedFormula 3).toBoundedFormula.multiclass.slice
    ![x, y], fun z ↦ ?_⟩
  rw [mem_comprehension_iff, Multiclass.toClass_iff]
  simp only [Multiclass.slice, BoundedFormula.multiclass]
  simp only [isValue, Function.comp_apply, Nat.reduceAdd, toBoundedFormula_exMem,
    Nat.succ_eq_add_one, append_left_eq_cons, Matrix.cons_val_fin_one, Matrix.Fin.cons_vecCons,
    cast_refl, Function.comp_id, BoundedFormula.realize_exMem, Term.realize'_var',
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty,
    realize_exMemSUnion, Matrix.cons_val, toBoundedFormula_inf, realize'_inf, realize_eqOrderedPair,
    realize_eqTriple, ↓existsAndEq, mem_orderedPair_iff, true_and, exists_and_left]
  refine ⟨by grind, ?_⟩
  rintro ⟨u, v, w, hw, huv, rfl⟩
  have hu : u ∈ UUx := (hUUx u).mpr ⟨!{u, v}, (hUx _).mpr ⟨!(u, v), huv, by simp⟩, by simp⟩
  have hv : v ∈ UUx := (hUUx v).mpr ⟨!{u, v}, (hUx _).mpr ⟨!(u, v), huv, by simp⟩, by simp⟩
  grind

theorem domClosed_of_modelsKP [hM : ModelsKP M] (x : M) : ∃ a, IsDom₀ a x := by
  obtain ⟨Ux, hUx⟩ := sUnionClosed_of_modelsKP x
  obtain ⟨UUx, hUUx⟩ := sUnionClosed_of_modelsKP Ux
  refine ⟨UUx ∩₀ (∃₀∈ &1 (∃₀∈⋃₀ &2 ((&2).eqOrderedPair &0 &3)) :
      L.DeltaZeroBoundedFormula 2).toBoundedFormula.multiclass.slice₀
    x, fun z ↦ ?_⟩
  rw [mem_comprehension_iff, Multiclass.toClass_iff]
  simp only [Multiclass.slice₀, Multiclass.slice, BoundedFormula.multiclass]
  simp only [isValue, Function.comp_apply, Nat.reduceAdd, toBoundedFormula_exMem,
    append_right_eq_snoc, Matrix.cons_val_fin_one, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty, BoundedFormula.realize_exMem, Term.realize'_var', Matrix.cons_val_one,
    realize_exMemSUnion, Matrix.cons_val, realize_eqOrderedPair, Matrix.cons_val_zero, ↓existsAndEq,
    mem_orderedPair_iff, and_true]
  refine ⟨by grind, ?_⟩
  rintro ⟨v, hv⟩
  exact ⟨(hUUx z).mpr ⟨!{z, v}, (hUx _).mpr ⟨!(z, v), hv, by simp⟩, by simp⟩, !{z, v}, v, hv,
    Or.inr rfl, by simp⟩

theorem invMemGraphClosed_of_modelsKP [hM : ModelsKP M] (x : M) : ∃ a, IsInvMemGraph₀ a x := by
  obtain ⟨Ux, hUx⟩ := sUnionClosed_of_modelsKP x
  obtain ⟨x_Ux, hx_Ux⟩ := exists_sprod_of_modelsKP x Ux
  refine ⟨x_Ux ∩₀ (∃₀∈ &1 (∃₀∈ &2 ((&0).eqOrderedPair &2 &3)) :
      L.DeltaZeroBoundedFormula 2).toBoundedFormula.multiclass.slice₀
    x, fun z ↦ ?_⟩
  rw [mem_comprehension_iff, Multiclass.toClass_iff]
  simp only [Multiclass.slice₀, Multiclass.slice, BoundedFormula.multiclass]
  simp only [isValue, Function.comp_apply, Nat.reduceAdd, toBoundedFormula_exMem,
    append_right_eq_snoc, Matrix.cons_val_fin_one, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty, BoundedFormula.realize_exMem, Term.realize'_var', Matrix.cons_val_one,
    Matrix.cons_val, realize_eqOrderedPair, Matrix.cons_val_zero, and_iff_right_iff_imp,
    forall_exists_index, and_imp]
  rintro u hu v hv rfl
  exact (hx_Ux _).mpr ⟨u, hu, v, (hUx v).mpr ⟨u, hu, hv⟩, rfl⟩

/-- The Δ₀ formula `∀ v, v ∈ &1 ↔ (&0, v) ∈ &2` -/
def _root_.FirstOrder.Language.DeltaZeroBoundedFormula.eqSlice {L : Language} [L.HasMem] :
    L.DeltaZeroBoundedFormula 3 :=
  (∀₀∈ &1 (∃₀∈ &2 ((&4).eqOrderedPair &0 &3))) ⊓
    (∀₀∈ &2 (∀₀∈⋃₀ &3 ((&3).eqOrderedPair &0 &4 ⟹ &4 ∈₀ &1)))

@[simp]
theorem realize_eqSlice [PairClosed M] [SDiffClosed M] [Extensional M] (xs : Fin 3 → M) :
    (eqSlice : L.DeltaZeroBoundedFormula 3).toBoundedFormula〘xs〙 ↔
      ∀ v, v ∈ xs 1 ↔ !(xs 0, v) ∈ xs 2 := by
  simp only [eqSlice, isValue, Function.comp_apply, Nat.reduceAdd, toBoundedFormula_inf,
    toBoundedFormula, toBoundedFormula_exMem, realize'_inf, BoundedFormula.realize_allMem,
    Term.realize'_var', BoundedFormula.realize_exMem, snoc_nat, coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.lt_add_one, ↓reduceDIte, reduceFinMk, realize_eqOrderedPair, Nat.mod_succ,
    lt_self_iff_false, Nat.zero_mod, zero_lt_four, zero_eta, zero_lt_three, exists_eq_right,
    realize_allMemSUnion, realize'_imp, realize'_mem, Nat.one_mod, Nat.one_lt_ofNat, mk_one]
  grind

theorem sliceSetClosed_of_modelsKP [hM : ModelsKP M] (x y : M) : ∃ a, IsSliceSet₀ a x y := by
  obtain ⟨Ux, hUx⟩ := sUnionClosed_of_modelsKP x
  obtain ⟨UUx, hUUx⟩ := sUnionClosed_of_modelsKP Ux
  -- `S u = {v | (u, v) ∈ x}`
  let S (u : M) := UUx ∩₀ (∃₀∈ &1 ((&3).eqOrderedPair &2 &0) :
    L.DeltaZeroBoundedFormula 3).toBoundedFormula.multiclass.slice ![x, u]
  have hS (u v : M) : v ∈ S u ↔ !(u, v) ∈ x := by
    rw [mem_comprehension_iff, Multiclass.toClass_iff]
    simp only [Multiclass.slice, BoundedFormula.multiclass]
    simp only [isValue, Function.comp_apply, Nat.reduceAdd, toBoundedFormula_exMem,
      Nat.succ_eq_add_one, append_left_eq_cons, Matrix.cons_val_fin_one, Matrix.Fin.cons_vecCons,
      cast_refl, Function.comp_id, BoundedFormula.realize_exMem, Term.realize'_var',
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty,
      realize_eqOrderedPair, Matrix.cons_val, exists_eq_right, and_iff_right_iff_imp]
    exact fun h ↦ (hUUx v).mpr ⟨!{u, v}, (hUx _).mpr ⟨!(u, v), h, by simp⟩, by simp⟩
  let G := (eqSlice : L.DeltaZeroBoundedFormula 3).toBoundedFormula.multiclass.slice₀ x
  have hG (u w : M) : G ![u, w] ↔ ∀ v, v ∈ w ↔ !(u, v) ∈ x := by
    simp only [G, Multiclass.slice₀, Multiclass.slice, BoundedFormula.multiclass, realize_eqSlice]
    simp [append_right_eq_snoc]
  have : HasReplacement y G := hasReplacement_of_modelsKP y G
    fun u _ ↦ ⟨S u, (hG _ _).mpr (hS u), fun w hw ↦ by ext v; rw [(hG _ _).1 hw, hS]⟩
  exact ⟨G ''₀ y, fun z ↦ by simp [hG]⟩

theorem interRelClosed_of_modelsKP [hM : ModelsKP M] (x : M) (R : L.Relations 1) :
    ∃ a, IsInterRel₀ a x R :=
  ⟨x ∩₀ Class.Rel R, by simp [IsInterRel₀]⟩

instance [hM : ModelsKP M] : RudBasisClosed M where
  sprodClosed := sprodClosed_of_modelsKP
  switchClosed := switchClosed_of_modelsKP
  rotateClosed := rotateClosed_of_modelsKP
  sUnionClosed := sUnionClosed_of_modelsKP
  domClosed := domClosed_of_modelsKP
  invMemGraphClosed := invMemGraphClosed_of_modelsKP
  sliceSetClosed := sliceSetClosed_of_modelsKP
  interRelClosed := interRelClosed_of_modelsKP

instance [hM : ModelsKP M] : RudClosed M := by infer_instance


-- instance [M.ModelsComprehension] : M.ClosedUnderDefinableComprehension :=
--   ⟨M.exists_isComprehension_of_modelsComprehension⟩

-- /-- The union axiom -/
-- def sUnionAxiom : L.Sentence := ∀' ∃' ∀' ∀' ((&3 ∈' &2 ⊓ &2 ∈' &0) ⟹ &3 ∈' &1)

-- /-- The power set axiom -/
-- def powersetAxiom : L.Sentence := ∀' ∃' ∀' (&2 ⊆' &0 ⟹ &2 ∈' &1)

-- class MemStructure.ModelsPowerset [HasMem M.L] : Prop where
--   protected modelsPowerset : M ⊨ M.L.powersetAxiom

-- -- theorem MemStructure.exists_isPowerset [hM₁ : M.ModelsPowerset]
-- --     [hM₂ : M.ModelsDeltaZeroComprehension] (x : M) :
-- --     ∃ a : M, M.IsPowerset a x := by
-- --   replace hM₁ := hM₁.modelsPowerset
-- --   simp [powersetAxiom, snoc, IsPowerset]
-- --   have : ∀ (a : ↑M), ∃ a_1 : M, ∀ a_2 ⊆ a, a_2 ∈ a_1 := by
-- --     simp [powersetAxiom, snoc]
-- --   obtain ⟨b, hb⟩ := this x
-- --   use ((&1).subset &0) 〘x, ∈ b〙₀
-- --   suffices ∀ z ⊆ x, z ∈ b by simpa [IsPowerset]
-- --   grind

-- -- instance [M.ModelsPowerset] [M.ModelsDeltaZeroComprehension] : M.ClosedUnderPowerset :=
-- --   ⟨M.exists_isPowerset⟩

-- /-- The foundation axiom -/
-- def foundationAxiom : L.Sentence := ∀'((∃'(&1 ∈' &0)) ⟹ ∃'∈ &0 ∀'∈ &1 ∼(&2 ∈' &0))

-- class MemStructure.ModelsFoundation [HasMem M.L] : Prop where
--   protected modelsFoundation : M ⊨ M.L.foundationAxiom

-- -- theorem MemStructure.exists_isMemMin [hM : M.ModelsFoundation]
-- --     [M.ModelsDeltaZeroComprehension] [M.ModelsExtensionality] (x : M) (hx : x ≠ ∅) :
-- --     ∃ a : M, M.IsMemMin a x := by
-- --   replace hM := hM.modelsFoundation
-- --   have : ∀ (y x : ↑M), x ∈ y → ∃ a ∈ y, ∀ a_1 ∈ a, a_1 ∉ y := by
-- --     simpa [foundationAxiom, snoc] using hM
-- --   simp [IsMemMin]
-- --   rw [ne_empty_iff] at hx

--   -- using this x hx

-- -- instance [M.ModelsFoundation] [M.ModelsDeltaZeroComprehension] [M.ModelsExtensionality] :
-- --   M.Foundational := ⟨M.exists_isMemMin⟩

-- -- /-- The replacement axiom -/
-- -- def replacement (φ : L.BoundedFormula α (n + 3)) : L.Formula α :=
-- --   ∀'' ((∀'∈ &0 ∃!' φ) ⟹ ∃' (∀'∈ &0 ∃'∈ &-3 (φ.liftAt 1 (n + 1))))

-- -- /-- The infinity axiom -/
-- -- def infinity : L.Sentence := ∃' ((∃'∈ &0 (&1).isEmpty) ⊓ ∀'∈ &0 (∃'∈ &0 ((&2).eqSucc &1)))

-- -- /-- The axiom of choice -/
-- -- def choice : L.Sentence :=
-- --   ∀' (∼(&-1).isEmpty ⟹ ∃' ((&-2).isFun ⊓ (&-1).eqDom (&-2) ⊓
-- --     ∀' ∃' ((&-3).memDom (&-2) ⟹ ∼(&-3).isEmpty ⟹ ((&-4).eqVal &-2 &-3 ⊓ &-4 ∈' &-3))))

end MemStructure

end Language

end FirstOrder
