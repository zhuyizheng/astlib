/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Ordinal.Transitive
/-!
file docstring
-/

namespace FirstOrder.Language

open FirstOrder Language BoundedFormula Fin DeltaZeroBoundedFormula RudimentaryTerm

namespace RudimentaryTerm

variable {L : Language.{u, v}} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]

variable {n : ℕ}

noncomputable def isOrdinal (t : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  t.isTransitive ⊓ (∀₀∈ &0 ∀₀∈ &0 (&1 ∈₀ &2 ⊔ &1 =₀ &2 ⊔ &2 ∈₀ &1)).substBoundRud ![t]

instance (t : L.RudimentaryTerm n) [t.CharFree] :
  t.isOrdinal.RelFree := by
  unfold isOrdinal; infer_instance

noncomputable def isZero (t : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (&0 =₀ &1).substBoundRud ![ᵣ0, ∅] |>.substBoundRud ![t]

noncomputable def isSuccOrdinal (t : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (ᵣ0).isOrdinal ⊓ ∃₀∈ &0 (&1 =₀ &2).substBoundRud ![ᵣ0, ᵣ0, (ᵣ1).succ] |>.substBoundRud ![t]

noncomputable def isLimOrdinal (t : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (ᵣ0).isOrdinal ⊓ ∼(ᵣ0).isSuccOrdinal |>.substBoundRud ![t]

noncomputable def isNonZeroLimOrdinal (t : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (ᵣ0).isLimOrdinal ⊓ ∼(ᵣ0).isZero |>.substBoundRud ![t]

instance (t : L.RudimentaryTerm n) [t.CharFree] : t.isZero.RelFree := by
  unfold isZero; infer_instance

instance (t : L.RudimentaryTerm n) [t.CharFree] :
  t.isSuccOrdinal.RelFree := by
  unfold isSuccOrdinal; infer_instance

instance (t : L.RudimentaryTerm n) [t.CharFree] :
  t.isLimOrdinal.RelFree := by
  unfold isLimOrdinal; infer_instance

instance (t : L.RudimentaryTerm n) [t.CharFree] :
  t.isNonZeroLimOrdinal.RelFree := by
  unfold isNonZeroLimOrdinal; infer_instance



  -- (&0 =₀ &1).substBoundRud ![ᵣ0, ∅] |>.substBound ![t]


-- def allTrans₀ {L : Language} [L.HasMem] (t : L.Term' n) : L.DeltaZeroBoundedFormula n :=
--   ∀₀∈ t (isTransitive &-1)

-- def isSuccOrEmpty₀ {L : Language} [L.HasMem] (t : L.Term' n) : L.DeltaZeroBoundedFormula n :=
--   (∀₀∈ t ⊥) ⊔ ∃₀∈ t (∀₀∈ t.castSucc (&-1 ∈₀ &-2 ⊔ &-1 =₀ &-2))

-- def allSuccOrEmpty₀ {L : Language} [L.HasMem] (t : L.Term' n) : L.DeltaZeroBoundedFormula n :=
--   ∀₀∈ t (isSuccOrEmpty₀ &-1)

-- def natFormula {L : Language} [L.HasMem] : L.DeltaZeroBoundedFormula 2 :=
--   isTransitive &0 ⊓ allTrans₀ &0 ⊓ isSuccOrEmpty₀ &0 ⊓
--     allSuccOrEmpty₀ &0 ⊓ (&0 ⊆₀ &1)

end RudimentaryTerm

namespace MemStructure

variable {L : Language.{u, v}} {M : Type max u v}
  [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly]
  [Inhabited M] [Extensional M] [RudClosed M] (x y : M)

open FirstOrder Language BoundedFormula Fin DeltaZeroBoundedFormula RudimentaryTerm Term

variable {n : ℕ}

@[grind]
def Ordinal : Class M := fun a ↦ Transitive a ∧ ∀ x ∈ a, ∀ y ∈ a, x ∈ y ∨ x = y ∨ y ∈ x

def SuccOrdinal : Class M := fun a ↦ Ordinal a ∧ ∃ x, a = succ x

def LimOrdinal : Class M := fun a ↦ Ordinal a ∧ ¬SuccOrdinal a

def NonZeroLimOrdinal : Class M := fun a ↦ LimOrdinal a ∧ a ≠ ∅

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isOrdinal (t : L.RudimentaryTerm n) [t.CharFree] (xs : Fin n → M) :
    t.isOrdinal.toBoundedFormula 〘xs〙 ↔ Ordinal (t〘xs〙 : M) := by
  simp only [isOrdinal, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    toBoundedFormula_inf, realize'_inf, realize_isTransisitive, Matrix.cons_val_fin_one,
    DeltaZeroBoundedFormula.realize_substBoundRud, toBoundedFormula, toBoundedFormula_sup,
    BoundedFormula.realize_allMem, realize'_var', snoc_nat, coe_ofNat_eq_mod, Nat.zero_mod,
    Order.lt_one_iff, ↓reduceDIte, realize'_sup, realize'_mem, Nat.mod_succ, lt_self_iff_false,
    Nat.one_mod, Order.lt_two_iff, Std.le_refl, mk_one, realize'_bdEqual, Ordinal,
    and_congr_right_iff]
  grind

@[simp, grind .]
theorem ordinal_empty : Ordinal (∅ : M) := by
  simp [Ordinal]

theorem ordinal_succ {a : M} (ha : Ordinal a) : Ordinal (succ a) := by
  simp only [Ordinal, mem_succ_iff, forall_eq_or_imp, true_or, or_true, true_and] at ha ⊢
  simp only [ha, transitive_succ, true_and]
  grind

@[simp, grind =]
theorem ordinal_succ_iff [Foundational M] (a : M) :
    Ordinal (succ a) ↔ Ordinal a := by
  refine ⟨?_, ordinal_succ⟩
  simp only [Ordinal, transitive_succ_iff, mem_succ_iff, forall_eq_or_imp, notMem_self, or_false,
    or_true, true_and, and_imp]
  grind

theorem ordinal_inter
    {a b : M} (ha : Ordinal a) (hb : Ordinal b) : Ordinal (a ∩ b) := by
  simp only [Ordinal, mem_inter_iff, and_imp] at ha hb ⊢
  refine ⟨transitive_inter ha.left hb.left, ?_⟩
  grind

@[grind .]
theorem ordinal_of_mem [Foundational M]
    {a b : M} (ha : Ordinal a) (hba : b ∈ a) : Ordinal b := by
  simp only [Ordinal] at hba ⊢
  refine ⟨fun x hx z hz ↦ ?_, fun x hx y hy ↦ ha.right x (ha.left b hba hx) y (ha.left b hba hy)⟩
  rcases ha.right z (by grind) b (by grind) with h | h | h
  · exact h
  · grind [notMem_of_mem]
  · grind [notMem_of_mem_of_mem]

@[grind .]
theorem mem_of_ordinal_of_subset_of_ne [Foundational M]
    {a b : M} (ha : Ordinal a) (hb : Ordinal b) (hab₁ : a ⊆ b) (hab₂ : a ≠ b) : a ∈ b := by
  obtain ⟨hc, hc'⟩ := isMemMin_memMin (x := (b \ a : M)) (by grind)
  simp only [mem_sdiff_iff] at hc
  convert hc.left
  ext x
  grind

theorem ordinal_compatible [Foundational M]
    {a b : M} (ha : Ordinal a) (hb : Ordinal b) : a ∈ b ∨ a = b ∨ b ∈ a := by
  have hab := ordinal_inter ha hb
  grind

theorem ordinal_union [Foundational M]
    {a b : M} (ha : Ordinal a) (hb : Ordinal b) : Ordinal (a ∪ b) := by
  grind [ordinal_compatible]

theorem ordinal_sUnion [Foundational M]
    {a : M} (ha : ∀ x ∈ a, Ordinal x) : Ordinal (⋃₀ a) := by
  simp only [Ordinal] at ha ⊢
  refine ⟨transitive_sUnion (fun x hx ↦ (ha x hx).left), ?_⟩
  intro x hx y hy
  simp only [mem_sUnion_iff] at hx hy
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  apply ordinal_compatible <;> grind

-- omit [Inhabited M] in
-- @[simp]
-- theorem realize_allTrans₀ (t : L.Term' n) (xs : Fin n → M) :
--     (allTrans₀ t).toBoundedFormula 〘xs〙 ↔ ∀ y ∈ t〘xs〙, ∀ z ∈ y, z ⊆ y := by
--   simp only [allTrans₀, DeltaZeroBoundedFormula.toBoundedFormula, BoundedFormula.realize_allMem]
--   simp [realize_isTrans₀]

-- omit [Inhabited M] in
-- @[simp]
-- theorem realize_isSuccOrEmpty₀ (t : L.Term' n) (xs : Fin n → M) :
--     (isSuccOrEmpty₀ t).toBoundedFormula 〘xs〙 ↔
--       (∀ y ∈ t〘xs〙, False) ∨
--         (∃ k ∈ t〘xs〙, ∀ w ∈ t〘xs〙, w ∈ k ∨ w = k) := by
--   simp [isSuccOrEmpty₀]

-- omit [Inhabited M] in
-- @[simp]
-- theorem realize_allSuccOrEmpty₀ (t : L.Term' n) (xs : Fin n → M) :
--     (allSuccOrEmpty₀ t).toBoundedFormula 〘xs〙 ↔
--       ∀ y ∈ t〘xs〙, (∀ z ∈ y, False) ∨
--         (∃ k ∈ y, ∀ w ∈ y, w ∈ k ∨ w = k) := by
--   simp [allSuccOrEmpty₀]

end FirstOrder.Language.MemStructure
