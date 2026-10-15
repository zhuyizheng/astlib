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
    refine ⟨a, fun z ↦ ?_⟩
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
  refine ⟨b ∩₀ (Class.Eq x ⊔ Class.Eq y), fun z ↦ ?_⟩
  simp only [mem_comprehension_iff, Class.sup_iff, Class.eq_iff, and_iff_right_iff_imp]
  grind

instance [hM : ModelsKP M] : PairClosed M := ⟨pairClosed_of_modelsKP⟩

/-- `Δ₀`-replacement -/
instance [ModelsKP M] (x : M) (F : Multiclass M 2) [hF : F.DeltaZero Set.univ] :
  HasReplacement x F where
  hasReplacement hFx := by
    obtain ⟨m, φ, hφ, vs, -, rfl⟩ := hF.isDeltaZero
    obtain ⟨b, hb⟩ := exists_collection_of_modelsKP (φ.multiclass.slice vs) x
      (fun u hu ↦ (hFx u hu).exists)
    -- `χ(z, vs, x)` says `∃ u ∈ x, φ(u, z, vs)`
    let χ : L.BoundedFormula' (1 + (m + 1)) := ∃'∈ &-1
      φ.castAssoc.switchBound.substBoundBound (snoc (castAdd 2) (last (1 + m + 1)))
    refine ⟨b ∩₀ χ.multiclass.slice (snoc vs x), fun z ↦ ?_⟩
    simp only [mem_comprehension_iff, Multiclass.toClass_iff]
    simp only [Multiclass.slice, BoundedFormula.multiclass, χ, append_snoc,
      BoundedFormula.realize_exMem, realize'_substBoundBound, Term.realize'_var', snoc_last,
      snoc_snoc_comp_snoc_castAdd_two_last, Function.comp_apply, Nat.add_eq]
    simp only [snoc_eq_append, realize'_switchBound, realize'_castAssoc]
    simp only [append_left_eq_cons, Fin.cast_refl, Function.comp_id]
    simp only [Multiclass.slice, BoundedFormula.multiclass] at hb hFx
    refine ⟨fun ⟨_, u, hu, hz⟩ ↦ ⟨u, hu, hz⟩, fun ⟨u, hu, hz⟩ ↦ ⟨?_, u, hu, hz⟩⟩
    obtain ⟨w, hwb, hw⟩ := hb u hu
    rwa [(hFx u hu).unique hz hw]

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
theorem _root_.FirstOrder.Language.DeltaZeroBoundedFormula.realize_exMemSUnion {n : ℕ} (t : L.Term' n) (φ : L.DeltaZeroBoundedFormula (n + 1))
    (xs : Fin n → M) :
    (∃₀∈⋃₀ t φ).toBoundedFormula〘xs〙 ↔ ∃ u ∈ t〘xs〙, ∃ x ∈ u, φ.toBoundedFormula〘snoc xs x〙 := by
  simp [DeltaZeroBoundedFormula.exMemSUnion]

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] in
@[simp]
theorem _root_.FirstOrder.Language.DeltaZeroBoundedFormula.realize_allMemSUnion {n : ℕ} (t : L.Term' n) (φ : L.DeltaZeroBoundedFormula (n + 1))
    (xs : Fin n → M) :
    (∀₀∈⋃₀ t φ).toBoundedFormula〘xs〙 ↔ ∀ u ∈ t〘xs〙, ∀ x ∈ u, φ.toBoundedFormula〘snoc xs x〙 := by
  simp [DeltaZeroBoundedFormula.allMemSUnion]

/-- The Δ₀ formula `t₁ = {t₂, t₃}` -/
def _root_.FirstOrder.Language.Term.eqUnorderedPair {L : Language} [L.HasMem] {n : ℕ}
    (t₁ t₂ t₃ : L.Term' n) : L.DeltaZeroBoundedFormula n :=
  (∀₀∈ t₁ (&-1 =₀ t₂.castSucc ⊔ &-1 =₀ t₃.castSucc)) ⊓ (t₂ ∈₀ t₁ ⊓ t₃ ∈₀ t₁)

/-- The Δ₀ formula `t₁ = {t₂}` -/
def _root_.FirstOrder.Language.Term.eqSingleton {L : Language} [L.HasMem] {n : ℕ}
    (t₁ t₂ : L.Term' n) : L.DeltaZeroBoundedFormula n :=
  t₁.eqUnorderedPair t₂ t₂

/-- The Δ₀ formula `t₁ = (t₂, t₃)` -/
def _root_.FirstOrder.Language.Term.eqOrderedPair {L : Language} [L.HasMem] {n : ℕ}
    (t₁ t₂ t₃ : L.Term' n) : L.DeltaZeroBoundedFormula n :=
  (∀₀∈ t₁ ((&-1).eqSingleton t₂.castSucc ⊔ (&-1).eqUnorderedPair t₂.castSucc t₃.castSucc)) ⊓
    ((∃₀∈ t₁ (&-1).eqSingleton t₂.castSucc) ⊓
      (∃₀∈ t₁ (&-1).eqUnorderedPair t₂.castSucc t₃.castSucc))

@[simp]
theorem _root_.FirstOrder.Language.Term.realize_eqUnorderedPair [PairClosed M] [SDiffClosed M] [Extensional M] {n : ℕ}
    (t₁ t₂ t₃ : L.Term' n) (xs : Fin n → M) :
    (t₁.eqUnorderedPair t₂ t₃).toBoundedFormula〘xs〙 ↔ t₁〘xs〙 = !{(t₂〘xs〙 : M), t₃〘xs〙} := by
  simp [Term.eqUnorderedPair, eq_unorderedPair_iff (t₂〘xs〙 : M) (t₃〘xs〙) (t₁〘xs〙)]

@[simp]
theorem _root_.FirstOrder.Language.Term.realize_eqSingleton [PairClosed M] [SDiffClosed M] [Extensional M] {n : ℕ}
    (t₁ t₂ : L.Term' n) (xs : Fin n → M) :
    (t₁.eqSingleton t₂).toBoundedFormula〘xs〙 ↔ t₁〘xs〙 = {(t₂〘xs〙 : M)} := by
  simp only [Term.eqSingleton, Term.realize_eqUnorderedPair]
  rfl

@[simp]
theorem _root_.FirstOrder.Language.Term.realize_eqOrderedPair [PairClosed M] [SDiffClosed M] [Extensional M] {n : ℕ}
    (t₁ t₂ t₃ : L.Term' n) (xs : Fin n → M) :
    (t₁.eqOrderedPair t₂ t₃).toBoundedFormula〘xs〙 ↔ t₁〘xs〙 = !((t₂〘xs〙 : M), t₃〘xs〙) := by
  simp [Term.eqOrderedPair, Term.eqSingleton, eq_orderedPair_iff]

/-- The Δ₀ formula `t = ((t₁, t₂), t₃)` -/
def _root_.FirstOrder.Language.Term.eqTriple {L : Language} [L.HasMem] {n : ℕ}
    (t t₁ t₂ t₃ : L.Term' n) : L.DeltaZeroBoundedFormula n :=
  ∃₀∈⋃₀ t ((&-1).eqOrderedPair t₁.castSucc t₂.castSucc ⊓ t.castSucc.eqOrderedPair &-1 t₃.castSucc)

@[simp]
theorem _root_.FirstOrder.Language.Term.realize_eqTriple [PairClosed M] [SDiffClosed M] [Extensional M] {n : ℕ}
    (t t₁ t₂ t₃ : L.Term' n) (xs : Fin n → M) :
    (t.eqTriple t₁ t₂ t₃).toBoundedFormula〘xs〙 ↔ t〘xs〙 = !(!((t₁〘xs〙 : M), t₂〘xs〙), t₃〘xs〙) := by
  simp only [Term.eqTriple, realize_exMemSUnion, toBoundedFormula_inf, realize'_inf,
    Term.realize_eqOrderedPair]
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

/-- The double union `⋃₀ ⋃₀ x` exists -/
theorem exists_sUnion_sUnion_of_modelsKP [ModelsKP M] (x : M) :
    ∃ a : M, IsSUnion₀SUnion₀ a x := by
  obtain ⟨Ux, _⟩ := sUnionClosed_of_modelsKP x
  obtain ⟨UUx, _⟩ := sUnionClosed_of_modelsKP Ux
  exact ⟨UUx, by grind [IsSUnion₀, IsSUnion₀SUnion₀]⟩

/-- The first component of an ordered pair in `x` belongs to the double union of `x` -/
theorem IsSUnion₀SUnion₀.left_mem [PairClosed M] [SDiffClosed M] {a x u v : M}
    (ha : IsSUnion₀SUnion₀ a x) (h : !(u, v) ∈ x) : u ∈ a := by
  grind [IsSUnion₀SUnion₀]

/-- The second component of an ordered pair in `x` belongs to the double union of `x` -/
theorem IsSUnion₀SUnion₀.right_mem [PairClosed M] [SDiffClosed M] {a x u v : M}
    (ha : IsSUnion₀SUnion₀ a x) (h : !(u, v) ∈ x) : v ∈ a := by
  grind [IsSUnion₀SUnion₀]

theorem exists_sprod_of_modelsKP [hM : ModelsKP M] (x y : M) :
    ∃ a : M, ∀ z, z ∈ a ↔ ∃ u ∈ x, ∃ v ∈ y, z = !(u, v) := by
  -- `F u` maps `v` to `(u, v)`
  let F (u : M) :=
    ((&1).eqOrderedPair &2 &0 : L.DeltaZeroBoundedFormula 3).toBoundedFormula.multiclass.slice₀ u
  have hF (u v w : M) : F u ![v, w] ↔ w = !(u, v) := by
    simp only [F, Multiclass.slice₀, Multiclass.slice, BoundedFormula.multiclass]
    simp [append_right_eq_snoc]
  have hFy (u t : M) : t ∈ F u ''₀ y ↔ ∃ v ∈ y, t = !(u, v) := by
    rw [mem_replacement_iff
      (fun v _ ↦ ⟨!(u, v), by simp [hF], fun w hw ↦ by simpa [hF] using hw⟩)]
    simp [hF]
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
      BoundedFormula.realize_exMem, Matrix.cons_val, Term.realize_eqOrderedPair, exists_eq_right]
    grind
  have hGx : ∀ u ∈ x, ∃! c, G ![u, c] := fun u _ ↦
    ⟨F u ''₀ y, by grind, by intros; ext; grind⟩
  obtain ⟨S, hS⟩ := sUnionClosed_of_modelsKP (G ''₀ x)
  refine ⟨S, fun z ↦ ?_⟩
  rw [hS z]
  simp only [mem_replacement_iff hGx, hG]
  refine ⟨by grind, ?_⟩
  rintro ⟨u, hu, v, hv, rfl⟩
  exact ⟨F u ''₀ y, by grind⟩

theorem sprodClosed_of_modelsKP [hM : ModelsKP M] (x y : M) : ∃ a, IsSProd₀ a x y :=
  exists_sprod_of_modelsKP x y

theorem switchClosed_of_modelsKP [hM : ModelsKP M] (x y : M) : ∃ a, IsSwitch₀ a x y := by
  obtain ⟨UUx, hUUx⟩ := exists_sUnion_sUnion_of_modelsKP x
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
    realize_exMemSUnion, Matrix.cons_val, toBoundedFormula_inf, realize'_inf, Term.realize_eqOrderedPair,
    Term.realize_eqTriple, ↓existsAndEq, mem_orderedPair_iff, true_and, exists_and_left]
  grind [hUUx.left_mem, hUUx.right_mem]


theorem rotateClosed_of_modelsKP [hM : ModelsKP M] (x y : M) : ∃ a, IsRotate₀ a x y := by
  obtain ⟨UUx, hUUx⟩ := exists_sUnion_sUnion_of_modelsKP x
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
    realize_exMemSUnion, Matrix.cons_val, toBoundedFormula_inf, realize'_inf, Term.realize_eqOrderedPair,
    Term.realize_eqTriple, ↓existsAndEq, mem_orderedPair_iff, true_and, exists_and_left]
  grind [hUUx.left_mem, hUUx.right_mem]

theorem domClosed_of_modelsKP [hM : ModelsKP M] (x : M) : ∃ a, IsDom₀ a x := by
  obtain ⟨UUx, hUUx⟩ := exists_sUnion_sUnion_of_modelsKP x
  refine ⟨UUx ∩₀ (∃₀∈ &1 (∃₀∈⋃₀ &2 ((&2).eqOrderedPair &0 &3)) :
      L.DeltaZeroBoundedFormula 2).toBoundedFormula.multiclass.slice₀
    x, fun z ↦ ?_⟩
  rw [mem_comprehension_iff, Multiclass.toClass_iff]
  simp only [Multiclass.slice₀, Multiclass.slice, BoundedFormula.multiclass]
  simp only [isValue, Function.comp_apply, Nat.reduceAdd, toBoundedFormula_exMem,
    append_right_eq_snoc, Matrix.cons_val_fin_one, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty, BoundedFormula.realize_exMem, Term.realize'_var', Matrix.cons_val_one,
    realize_exMemSUnion, Matrix.cons_val, Term.realize_eqOrderedPair, Matrix.cons_val_zero, ↓existsAndEq,
    mem_orderedPair_iff, and_true]
  grind [hUUx.left_mem, hUUx.right_mem]

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
    Matrix.cons_val, Term.realize_eqOrderedPair, Matrix.cons_val_zero, and_iff_right_iff_imp,
    forall_exists_index, and_imp]
  rintro u hu v hv rfl
  grind [IsSUnion₀]

/-- The Δ₀ formula `∀ v, v ∈ &0 ↔ (&2, v) ∈ &1` -/
def _root_.FirstOrder.Language.DeltaZeroBoundedFormula.eqSlice {L : Language} [L.HasMem] :
    L.DeltaZeroBoundedFormula 3 :=
  (∀₀∈ &0 (∃₀∈ &1 ((&4).eqOrderedPair &2 &3))) ⊓
    (∀₀∈ &1 (∀₀∈⋃₀ &3 ((&3).eqOrderedPair &2 &4 ⟹ &4 ∈₀ &0)))

@[simp]
theorem _root_.FirstOrder.Language.DeltaZeroBoundedFormula.realize_eqSlice [PairClosed M] [SDiffClosed M] [Extensional M] (xs : Fin 3 → M) :
    (eqSlice : L.DeltaZeroBoundedFormula 3).toBoundedFormula〘xs〙 ↔
      ∀ v, v ∈ xs 0 ↔ !(xs 2, v) ∈ xs 1 := by
  simp only [eqSlice, isValue, Function.comp_apply, Nat.reduceAdd, toBoundedFormula_inf,
    toBoundedFormula, toBoundedFormula_exMem, realize'_inf, BoundedFormula.realize_allMem,
    Term.realize'_var', BoundedFormula.realize_exMem, snoc_nat, coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.lt_add_one, ↓reduceDIte, reduceFinMk, Term.realize_eqOrderedPair, Nat.mod_succ,
    lt_self_iff_false, Nat.zero_mod, zero_lt_four, zero_eta, zero_lt_three,
    realize_allMemSUnion, realize'_imp, realize'_mem, Nat.one_mod, Nat.one_lt_ofNat, mk_one]
  grind

theorem sliceSetClosed_of_modelsKP [hM : ModelsKP M] (x y : M) : ∃ a, IsSliceSet₀ a x y := by
  obtain ⟨UUx, hUUx⟩ := exists_sUnion_sUnion_of_modelsKP x
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
      Term.realize_eqOrderedPair, Matrix.cons_val, exists_eq_right, and_iff_right_iff_imp]
    exact hUUx.right_mem
  let G : Multiclass M 2 :=
    (eqSlice.toBoundedFormula.multiclass.remap (![1, 2, 0])).slice₀ x
  have hG (u w : M) : G ![u, w] ↔ ∀ v, v ∈ w ↔ !(u, v) ∈ x := by
    simp only [G, Multiclass.slice₀, Multiclass.slice, Multiclass.remap,
      BoundedFormula.multiclass, realize_eqSlice]
    simp [append_right_eq_snoc]
  have hGy (u : M) (hu : u ∈ y) : ∃! w, G ![u, w] := ⟨S u, by grind, fun _ _ ↦ by ext; grind⟩
  exact ⟨G ''₀ y, fun z ↦ by simp [mem_replacement_iff hGy, hG]⟩

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
