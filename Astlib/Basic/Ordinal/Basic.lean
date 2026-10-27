/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Transitive.Basic
import Astlib.Basic.Axiom.KP.SigmaOneBoundedFormula.Semantics
/-!
file docstring
-/

namespace FirstOrder.Language

open FirstOrder Language BoundedFormula Fin DeltaZeroBoundedFormula RudimentaryTerm

namespace RudimentaryTerm

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]

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

variable {L : Language} {M : Type*}
  [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly]
  [Inhabited M] [Extensional M] [RudClosed M] (x y : M)

open FirstOrder Language BoundedFormula Fin DeltaZeroBoundedFormula RudimentaryTerm Term

variable {n : ℕ}

@[grind]
def Ordinal : Class M := fun a ↦ Transitive a ∧ ∀ x ∈ a, ∀ y ∈ a, x ∈ y ∨ x = y ∨ y ∈ x

noncomputable instance (a : M) : Decidable (Ordinal a) := Classical.propDecidable _

def SuccOrdinal : Class M := fun a ↦ Ordinal a ∧ ∃ x, a = succ x

def LimOrdinal : Class M := fun a ↦ Ordinal a ∧ ¬SuccOrdinal a

def NonZeroLimOrdinal : Class M := fun a ↦ LimOrdinal a ∧ a ≠ ∅

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [Extensional M] [RudClosed M] in
@[simp, grind .]
theorem Ordinal.transitive {a : M} (ha : Ordinal a) : Transitive a := ha.left

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [Extensional M] [RudClosed M] in
theorem Ordinal.compatible {a : M} (ha : Ordinal a) :
    ∀ x ∈ a, ∀ y ∈ a, x ∈ y ∨ x = y ∨ y ∈ x :=
  ha.right

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

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isZero (t : L.RudimentaryTerm n)
    [t.CharFree] (xs : Fin n → M) : t.isZero.toBoundedFormula 〘xs〙 ↔ t〘xs〙 = (∅ : M) := by
  simp [isZero, DeltaZeroBoundedFormula.toBoundedFormula]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isSuccOrdinal (t : L.RudimentaryTerm n)
    [t.CharFree] (xs : Fin n → M) :
    t.isSuccOrdinal.toBoundedFormula 〘xs〙 ↔ SuccOrdinal (t〘xs〙 : M) := by
  simp [isSuccOrdinal, SuccOrdinal, toBoundedFormula, snoc_nat]
  grind

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isLimOrdinal (t : L.RudimentaryTerm n)
    [t.CharFree] (xs : Fin n → M) :
    t.isLimOrdinal.toBoundedFormula 〘xs〙 ↔ LimOrdinal (t〘xs〙 : M) := by
  simp [isLimOrdinal, LimOrdinal]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isNonZeroLimOrdinal
    (t : L.RudimentaryTerm n) [t.CharFree] (xs : Fin n → M) :
    t.isNonZeroLimOrdinal.toBoundedFormula 〘xs〙 ↔ NonZeroLimOrdinal (t〘xs〙 : M) := by
  simp [isNonZeroLimOrdinal, NonZeroLimOrdinal]

instance : (Ordinal : Class M).DeltaZero Set.univ := by
  unfold Ordinal Transitive
  infer_instance

instance : (NonZeroLimOrdinal : Class M).DeltaZero Set.univ := by
  have h : (NonZeroLimOrdinal : Class M) =
      (((ᵣ0).isNonZeroLimOrdinal.toBoundedFormula.multiclass : Multiclass M 1) : Class M) := by
    funext x
    simp
  rw [h]
  infer_instance

@[simp, grind .]
theorem ordinal_empty : Ordinal (∅ : M) := by
  simp [Ordinal]

@[grind .]
theorem ordinal_succ {a : M} (ha : Ordinal a) : Ordinal (succ a) := by
  simp only [Ordinal, mem_succ_iff, forall_eq_or_imp, true_or, or_true, true_and] at ha ⊢
  simp only [ha, transitive_succ, true_and]
  grind

@[simp, grind =]
theorem ordinal_succ_iff [Foundational M] (a : M) :
    Ordinal (succ a) ↔ Ordinal a := by
  grind

@[simp]
theorem not_succOrdinal_empty : ¬SuccOrdinal (∅ : M) :=
  fun ⟨_, x, h⟩ ↦ succ_ne_empty x h.symm

@[simp]
theorem not_nonZeroLimOrdinal_empty : ¬NonZeroLimOrdinal (∅ : M) := by
  simp [NonZeroLimOrdinal]

@[simp]
theorem succOrdinal_succ {a : M} (ha : Ordinal a) : SuccOrdinal (succ a) :=
  ⟨ordinal_succ ha, a, rfl⟩

@[simp]
theorem not_nonZeroLimOrdinal_succ (a : M) : ¬NonZeroLimOrdinal (succ a) := by
  simp [NonZeroLimOrdinal, LimOrdinal, SuccOrdinal]

@[simp, grind →]
theorem NonZeroLimOrdinal.ordinal {a : M} (ha : NonZeroLimOrdinal a) : Ordinal a :=
  ha.left.left

@[grind .]
theorem NonZeroLimOrdinal.not_succOrdinal {a : M} (ha : NonZeroLimOrdinal a) : ¬SuccOrdinal a :=
  ha.left.right

@[grind .]
theorem NonZeroLimOrdinal.ne_empty {a : M} (ha : NonZeroLimOrdinal a) : a ≠ ∅ :=
  ha.right

theorem ordinal_inter
    {a b : M} (ha : Ordinal a) (hb : Ordinal b) : Ordinal (a ∩ b) := by
  have := transitive_inter ha.transitive hb.transitive
  simp only [Ordinal, mem_inter_iff, and_imp] at ha hb ⊢
  grind

@[simp, grind .]
theorem ordinal_of_mem [Foundational M]
    {a b : M} (ha : Ordinal a) (hba : b ∈ a) : Ordinal b := by
  simp only [Ordinal] at hba ⊢
  refine ⟨fun x hx z hz ↦ ?_, fun x hx y hy ↦
    ha.compatible x (ha.transitive b hba hx) y (ha.transitive b hba hy)⟩
  rcases ha.compatible z (by grind) b (by grind) with h | h | h
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
  have hab : Ordinal (a ∩ b) := ordinal_inter ha hb
  grind

/-- Two distinct ordinals are comparable by `∈` -/
theorem mem_or_mem_of_ne [Foundational M] {a b : M} (ha : Ordinal a) (hb : Ordinal b)
    (hab : a ≠ b) : a ∈ b ∨ b ∈ a := by
  grind [ordinal_compatible ha hb]

/-- Every ordinal is zero, a successor or a nonzero limit -/
theorem Ordinal.cases [Foundational M] {a : M} (ha : Ordinal a) :
    a = ∅ ∨ (∃ b, Ordinal b ∧ a = succ b) ∨ NonZeroLimOrdinal a := by
  grind [SuccOrdinal, NonZeroLimOrdinal, LimOrdinal]

/-- A nonzero ordinal is a successor or a nonzero limit -/
theorem Ordinal.cases_of_ne_empty [Foundational M] {a : M} (ha : Ordinal a) (h : a ≠ ∅) :
    (∃ b, Ordinal b ∧ a = succ b) ∨ NonZeroLimOrdinal a := by
  grind [ha.cases]

/-- An ordinal that is not a nonzero limit is zero or a successor -/
theorem Ordinal.cases_of_not_nonZeroLimOrdinal [Foundational M] {a : M} (ha : Ordinal a)
    (h : ¬NonZeroLimOrdinal a) : a = ∅ ∨ ∃ b, Ordinal b ∧ a = succ b := by
  grind [ha.cases]

/-- A nonzero ordinal that is not a nonzero limit is a successor -/
theorem Ordinal.exists_eq_succ [Foundational M] {a : M} (ha : Ordinal a) (h₀ : a ≠ ∅)
    (hl : ¬NonZeroLimOrdinal a) : ∃ b, Ordinal b ∧ a = succ b := by
  grind [ha.cases]

/-- A nonzero ordinal that is not a successor is a nonzero limit -/
theorem Ordinal.nonZeroLimOrdinal_of_ne_empty [Foundational M] {a : M} (ha : Ordinal a)
    (h₀ : a ≠ ∅) (hs : ¬SuccOrdinal a) : NonZeroLimOrdinal a := by
  grind [ha.cases, SuccOrdinal]

/-- An ordinal that is neither a successor nor a nonzero limit is zero -/
theorem Ordinal.eq_empty_of_not_succOrdinal [Foundational M] {a : M} (ha : Ordinal a)
    (hs : ¬SuccOrdinal a) (hl : ¬NonZeroLimOrdinal a) : a = ∅ := by
  grind [ha.cases, SuccOrdinal]

/-- An ordinal that is not a successor is zero or a nonzero limit -/
theorem Ordinal.cases_of_not_succOrdinal [Foundational M] {a : M} (ha : Ordinal a)
    (h : ¬SuccOrdinal a) : a = ∅ ∨ NonZeroLimOrdinal a := by
  grind [ha.cases, SuccOrdinal]

theorem empty_mem_of_ordinal_of_ne_empty [Foundational M] {a : M} (ha : Ordinal a)
    (ha' : a ≠ ∅) : ∅ ∈ a := by
  grind

@[grind .]
theorem NonZeroLimOrdinal.empty_mem [Foundational M] {a : M} (ha : NonZeroLimOrdinal a) : ∅ ∈ a :=
  empty_mem_of_ordinal_of_ne_empty ha.ordinal ha.ne_empty

@[grind .]
theorem NonZeroLimOrdinal.succ_mem [Foundational M] {a b : M} (ha : NonZeroLimOrdinal a)
    (hb : b ∈ a) : succ b ∈ a := by
  have := ordinal_compatible (ordinal_succ (ordinal_of_mem ha.ordinal hb)) ha.ordinal
  grind [NonZeroLimOrdinal, LimOrdinal, SuccOrdinal]

theorem succ_mem_succ [Foundational M] {a b : M} (hb : Ordinal b) (hab : a ∈ b) :
    succ a ∈ succ b := by
  grind

theorem ordinal_union [Foundational M]
    {a b : M} (ha : Ordinal a) (hb : Ordinal b) : Ordinal (a ∪ b) := by
  grind [ordinal_compatible]

theorem union_mem_of_mem [Foundational M] {α a b : M} (hα : Ordinal α) (ha : a ∈ α)
    (hb : b ∈ α) : a ∪ b ∈ α := by
  grind

/-- An ordinal contained in an element of an ordinal `c` lies in `c` -/
theorem mem_of_subset_of_mem [Foundational M] {a b c : M} (hc : Ordinal c) (ha : Ordinal a)
    (hb : b ∈ c) (h : a ⊆ b) : a ∈ c := by
  have := ordinal_compatible ha (ordinal_of_mem hc hb)
  grind

/-- For ordinals, `a ∉ b` implies `b ⊆ a` -/
theorem Ordinal.subset_of_notMem [Foundational M] {a b : M} (ha : Ordinal a) (hb : Ordinal b)
    (h : a ∉ b) : b ⊆ a := by
  have := ordinal_compatible ha hb
  grind

theorem mem_succ_of_subset [Foundational M] {a b : M} (ha : Ordinal a) (hb : Ordinal b)
    (h : a ⊆ b) : a ∈ succ b := by
  grind

@[grind .]
theorem ordinal_sUnion [Foundational M]
    {a : M} (ha : ∀ x ∈ a, Ordinal x) : Ordinal (⋃₀ a) := by
  refine ⟨transitive_sUnion (fun x hx ↦ (ha x hx).transitive), ?_⟩
  intro x hx y hy
  simp only [mem_sUnion_iff] at hx hy
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  grind [ordinal_compatible]

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

namespace FirstOrder.Language.MemStructure

open FirstOrder Language BoundedFormula RudimentaryTerm

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M]

end FirstOrder.Language.MemStructure
