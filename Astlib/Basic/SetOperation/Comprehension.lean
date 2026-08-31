/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Rudimentary.Semantics
import Astlib.Basic.SetOperation.Insert
import Astlib.Basic.SetOperation.SDiff
import Astlib.Basic.SetOperation.Multiclass.Levy
-- import Astlib.Mathlib.ModelTheory.Semantics
/-!
file docstring
-/

open Fin

namespace FirstOrder.Language

variable {M : MemStructure}
variable {L : Language} [L.HasMem]

namespace MemStructure

variable (x y z : M) {n : ℕ}

def IsComprehension (a x : M) (A : M.Class) := ∀ z, z ∈ a ↔ z ∈ x ∧ A z

noncomputable instance (x : M) (A : M.Class) :
  Decidable (∃ a : M, IsComprehension a x A) :=
  Classical.propDecidable _

/-- The subset of `x` containing `z` for which `φ〘v, snoc xs z〙` holds -/
noncomputable def comprehension (x : M) (A : M.Class) :=
  dite (∃ a : M, IsComprehension a x A)
    Classical.choose default

@[inherit_doc] scoped[FirstOrder.Language]
infix:88 " ∩₀ " => FirstOrder.Language.MemStructure.comprehension

class HasComprehension (x : M) (A : M.Class) : Prop where
  protected hasComprehension : ∃ a : M, IsComprehension a x A

@[simp, grind =, push]
theorem mem_comprehension_iff (x : M) (A : M.Class) [hx : HasComprehension x A] (z : M) :
    z ∈ x ∩₀ A ↔ z ∈ x ∧ A z := by
  convert Classical.choose_spec hx.hasComprehension z
  simp [MemStructure.comprehension, HasComprehension.hasComprehension]

theorem comprehension_subset (x : M) (A : M.Class) [HasComprehension x A] :
    x ∩₀ A ⊆ x := by
  grind

@[simp]
theorem comprehension_eq_iff [M.Extensional] (x : M) (A B : M.Class)
    [HasComprehension x A] [HasComprehension x B] :
    x ∩₀ A = x ∩₀ B ↔ ∀ z ∈ x, A z ↔ B z := by
  simp [eq_iff]

@[simp]
theorem comprehension_eq_univ_iff [M.Extensional] (x : M) (A : M.Class) [HasComprehension x A] :
    x ∩₀ A = x ↔ ∀ z ∈ x, A z := by
  simp [eq_iff]

@[simp]
theorem comprehension_eq_empty_iff [M.Extensional] [M.RudClosed] (x : M) (A : M.Class)
    [HasComprehension x A] :
    x ∩₀ A = ∅ ↔ ∀ z ∈ x, ¬A z := by
  simp [eq_iff]

variable (M) in
class ClosedUnderDefinableComprehension : Prop where
  closedUnderDefinableComprehension (x : M) (A : M.Class)
    [A.Definable Set.univ] :
    ∃ a : M, IsComprehension a x A

export ClosedUnderDefinableComprehension (closedUnderDefinableComprehension)

instance [M.ClosedUnderDefinableComprehension] (A : M.Class) [A.Definable Set.univ] :
  HasComprehension x A :=
  ⟨closedUnderDefinableComprehension x A⟩

variable [M.RudClosed] [M.Extensional]

def IsZeroOrOne (x : M) := x = ∅ ∨ x = {∅}

@[grind =]
theorem isZeroOrOne_iff_subset_singleton_empty {x : M} :
    IsZeroOrOne x ↔ x ⊆ {∅} := by
  grind [IsZeroOrOne]

omit [M.Extensional] in
@[simp, grind .]
theorem IsZeroOrOne.singleton_empty_iff_ne_empty {x : M} (hx : IsZeroOrOne x) :
    x = {∅} ↔ x ≠ ∅ := by
  grind [IsZeroOrOne]

omit [M.Extensional] in
@[grind .]
theorem IsZeroOrOne.empty_of_mem {x z : M} (hx : IsZeroOrOne x) (hz : z ∈ x) : z = ∅ := by
  grind [IsZeroOrOne]

end MemStructure


namespace RudimentaryTerm

open MemStructure

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]

/-- The rudimentary term that maps `xs` to `1` is `t〘xs〙 ≠ ∅`, `0` otherwise -/
def isNonempty (r : L.RudimentaryTerm n) := r.iUnion {∅}

def not [NeZero n] (r : L.RudimentaryTerm n) := {∅} \ r

def isEmpty [NeZero n] (r : L.RudimentaryTerm n) := r.isNonempty.not

def eqChar [NeZero n] (r₁ r₂ : L.RudimentaryTerm n) :=
  ((r₁ \ r₂) ∪ (r₂ \ r₁)).isEmpty

/-- If `r_truth〘xs〙 ≠ ∅`, then takes value `r〘xs〙`, else `∅` -/
def ifNonempty (r : L.RudimentaryTerm n) (r_truth : L.RudimentaryTerm n) :=
  r_truth.iUnion r.castSucc

variable {M : MemStructure} (r r₁ r₂ : M.L'.RudimentaryTerm n)

@[simp]
theorem castLHom_isNonempty :
    r.isNonempty.castLHom = r.castLHom.isNonempty := by
  simp [isNonempty]

@[simp]
theorem castLHom_not [NeZero n] :
    r.not.castLHom = r.castLHom.not := by
  simp [not]

@[simp]
theorem castLHom_isEmpty [NeZero n] :
    r.isEmpty.castLHom = r.castLHom.isEmpty := by
  simp [isEmpty]

@[simp]
theorem castLHom_eqChar [NeZero n] :
    (r₁.eqChar r₂).castLHom = r₁.castLHom.eqChar r₂.castLHom := by
  simp [eqChar]

@[simp]
theorem castLHom_ifNonempty [NeZero n] :
    (r₁.ifNonempty r₂).castLHom = r₁.castLHom.ifNonempty r₂.castLHom := by
  simp [ifNonempty]

variable [M.RudClosed]
variable [M.Extensional]

-- @[simp, grind =]
theorem realize_isNonempty_of_ne_empty {t : M.L.RudimentaryTerm n} {xs : Fin n → M}
    (h : t〘xs〙 ≠ ∅) :
    (t.isNonempty)〘xs〙 = {∅} := by
  rw [ne_empty_iff] at h
  ext z
  simp [isNonempty, h]

-- @[simp, grind =]
theorem realize_isNonempty_of_empty {t : M.L.RudimentaryTerm n} {xs : Fin n → M}
    (h : t〘xs〙 = ∅) :
    (t.isNonempty)〘xs〙 = ∅ := by
  rw [empty_iff] at h
  ext z
  simp [isNonempty, singleton, h]

@[simp, grind .]
theorem isZeroOrOne_realize_isNonempty [NeZero n]
    {t : M.L.RudimentaryTerm n}
    {xs : Fin n → M} :
    IsZeroOrOne (t.isNonempty)〘xs〙 := by
  grind [IsZeroOrOne, realize_isNonempty_of_ne_empty, realize_isNonempty_of_empty]

@[simp, grind =]
theorem realize_isNonempty_empty_iff [NeZero n]
    {t : M.L.RudimentaryTerm n}
    {xs : Fin n → M} :
    (t.isNonempty)〘xs〙 = ∅ ↔ t〘xs〙 = ∅ := by
  grind [realize_isNonempty_of_ne_empty, realize_isNonempty_of_empty]

@[simp, grind =]
theorem realize_not_of_singleton_empty [NeZero n]
    {t : M.L.RudimentaryTerm n} {xs : Fin n → M}
    (h : t〘xs〙 = {∅}) :
    (t.not)〘xs〙 = ∅ := by
  simp [not, h, singleton]

@[simp, grind =]
theorem realize_not_of_empty [NeZero n]
    {t : M.L.RudimentaryTerm n} {xs : Fin n → M}
    (h : t〘xs〙 = ∅) :
    (t.not)〘xs〙 = {∅} := by
  simp [not, h, singleton]

@[simp, grind .]
theorem isZeroOrOne_realize_not [NeZero n]
    (t : M.L.RudimentaryTerm n)
    (xs : Fin n → M) :
    IsZeroOrOne (t.not)〘xs〙 := by
  rw [isZeroOrOne_iff_subset_singleton_empty]
  simp only [not, realize_sdiff, realize_singleton, realize_empty]
  grind

-- @[simp, grind =]
theorem realize_isEmpty_of_ne_empty [NeZero n] {t : M.L.RudimentaryTerm n}
    {xs : Fin n → M}
    (h : t〘xs〙 ≠ ∅) :
    (t.isEmpty)〘xs〙 = ∅ := by
  simp [isEmpty, h]

-- @[simp, grind =]
theorem realize_isEmpty_of_empty [NeZero n] {t : M.L.RudimentaryTerm n}
    {xs : Fin n → M}
    (h : t〘xs〙 = ∅) :
    (t.isEmpty)〘xs〙 = {∅} := by
  simp [isEmpty, h]

@[simp, grind .]
theorem isZeroOrOne_realize_isEmpty [NeZero n]
    (t : M.L.RudimentaryTerm n)
    (xs : Fin n → M) :
    IsZeroOrOne (t.isEmpty)〘xs〙 :=
  isZeroOrOne_realize_not _ _

@[simp, grind =]
theorem realize_isEmpty_empty_iff [NeZero n]
    {t : M.L.RudimentaryTerm n}
    {xs : Fin n → M} :
    (t.isEmpty)〘xs〙 = ∅ ↔ t〘xs〙 ≠ ∅ := by
  grind [realize_isEmpty_of_ne_empty, realize_isEmpty_of_empty]

-- @[simp, grind =]
theorem realize_eqChar_of_eq [NeZero n] {t₁ t₂ : M.L.RudimentaryTerm n}
    {xs : Fin n → M}
    (h : t₁〘xs〙 = t₂〘xs〙) :
    (t₁.eqChar t₂)〘xs〙 = {∅} := by
  simp [eqChar, h]

theorem realize_eqChar_of_ne [NeZero n] {t₁ t₂ : M.L.RudimentaryTerm n}
    {xs : Fin n → M}
    (h : t₁〘xs〙 ≠ t₂〘xs〙) :
    (t₁.eqChar t₂)〘xs〙 = ∅ := by
  simp only [eqChar, realize_isEmpty_empty_iff, realize_union, realize_sdiff]
  grind

@[simp, grind .]
theorem isZeroOrOne_realize_eqChar [NeZero n]
    (t₁ t₂ : M.L.RudimentaryTerm n)
    (xs : Fin n → M) :
    IsZeroOrOne (t₁.eqChar t₂)〘xs〙 :=
  isZeroOrOne_realize_not _ _

@[simp, grind =]
theorem realize_eqChar_empty_iff [NeZero n]
    (t₁ t₂ : M.L.RudimentaryTerm n)
    (xs : Fin n → M) :
    (t₁.eqChar t₂)〘xs〙 = ∅ ↔ t₁〘xs〙 ≠ t₂〘xs〙 := by
  grind [realize_eqChar_of_eq, realize_eqChar_of_ne]

@[simp]
theorem realize_ifNonempty_of_empty (r : M.L.RudimentaryTerm n)
    {r_truth : M.L.RudimentaryTerm n}
    {xs : Fin n → M} (h : r_truth〘xs〙 = ∅) :
    (r.ifNonempty r_truth)〘xs〙 = ∅ := by
  simp only [ifNonempty]
  ext z
  simp only [mem_realize_iUnion_iff]
  grind [ne_empty_iff]

@[simp]
theorem realize_ifNonempty_of_ne_empty (r : M.L.RudimentaryTerm n)
    {r_truth : M.L.RudimentaryTerm n}
    {xs : Fin n → M} (h : r_truth〘xs〙 ≠ ∅) :
    (r.ifNonempty r_truth)〘xs〙 = r〘xs〙 := by
  rw [ne_empty_iff] at h
  simp only [ifNonempty]
  ext z
  simp only [mem_realize_iUnion_iff, realize_castSucc]
  grind

@[simp]
theorem realize_ifNonempty_subset {r : M.L.RudimentaryTerm n}
    {r_truth : M.L.RudimentaryTerm n}
    {xs : Fin n → M} :
    (r.ifNonempty r_truth)〘xs〙 ⊆ r〘xs〙 := by
  by_cases r_truth〘xs〙 = ∅ <;> grind [realize_ifNonempty_of_empty, realize_ifNonempty_of_ne_empty]

@[simp]
theorem mem_realize_ifNonempty_iff (r : M.L.RudimentaryTerm n)
    (r_truth : M.L.RudimentaryTerm n)
    (xs : Fin n → M)
    (z : M) :
    z ∈ (r.ifNonempty r_truth)〘xs〙 ↔ z ∈ r〘xs〙 ∧ r_truth〘xs〙 ≠ ∅ := by
  grind [realize_ifNonempty_of_empty, realize_ifNonempty_of_ne_empty, realize_ifNonempty_subset]

end RudimentaryTerm

namespace DeltaZeroBoundedFormula

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] {n m k : ℕ}
  {M : MemStructure} [M.L.ExtraConstantsUnaryRelationsOnly] [M.Extensional] [M.RudClosed]

open MemStructure RudimentaryTerm

/-- The characteristic function of `φ` that maps `xs` to `1` if `φ〘xs〙` holds, `0` otherwise -/
noncomputable def charRudimentaryTerm {n : ℕ} [NeZero n]
  (φ : L.DeltaZeroBoundedFormula n) :
  L.RudimentaryTerm n :=
  match φ with
  | falsum => ∅
  | equal t₁ t₂ => t₁.toRudimentaryTerm.eqChar t₂.toRudimentaryTerm
  | mem t₁ t₂ => t₂.toRudimentaryTerm.iUnion (t₁.toRudimentaryTerm.castSucc.eqChar ᵣ-1)
  | imp φ₁ φ₂ => φ₁.charRudimentaryTerm.not ∪ φ₂.charRudimentaryTerm
  | allMem t ψ => (t.toRudimentaryTerm.iUnion ψ.charRudimentaryTerm.not).not
  | rel R t => .char R t.toRudimentaryTerm

omit [M.Extensional] [M.RudClosed] in
@[simp]
theorem castLHom_charRudimentaryTerm {n : ℕ}
    [NeZero n]
    (φ : M.L'.DeltaZeroBoundedFormula n) :
    (φ.charRudimentaryTerm : M.L'.RudimentaryTerm n).castLHom = φ.castLHom.charRudimentaryTerm := by
  cases φ with
  | falsum => simp [charRudimentaryTerm]
  | equal t₁ t₂ => simp [charRudimentaryTerm]
  | mem t₁ t₂ => simp [charRudimentaryTerm]
  | imp φ₁ φ₂ =>
    simp [charRudimentaryTerm, φ₁.castLHom_charRudimentaryTerm, φ₂.castLHom_charRudimentaryTerm]
  | allMem t ψ => simp [charRudimentaryTerm, ψ.castLHom_charRudimentaryTerm]
  | rel R t => simp [charRudimentaryTerm, castLHom]

  -- revert n φ
  -- induction φ with
  -- | falsum =>
  --   simp [charRudimentaryTerm]
  --   convert castLHom_empty
  --   · rfl
  --   · rfl
  --   · rfl
  -- r_truth.iUnion r.castSucc

mutual
  theorem realize_charRudimentaryTerm_of_realize {n : ℕ} [NeZero n]
      {φ : M.L.DeltaZeroBoundedFormula n} {xs : Fin n → M}
      (h : φ.toBoundedFormula〘xs〙) :
      φ.charRudimentaryTerm 〘xs〙 = {∅} := match φ with
    | falsum => by simp at h
    | equal t₁ t₂ => by simpa [charRudimentaryTerm]
    | mem t₁ t₂ => by
      simp only [toBoundedFormula, realize'_mem] at h
      simp only [charRudimentaryTerm, eq_singleton_iff, mem_realize_iUnion_iff,
        Term.realize_toRudimentaryTerm]
      intro z
      refine ⟨fun ⟨w, hw₁, hw₂⟩ ↦ IsZeroOrOne.empty_of_mem (by simp) hw₂, ?_⟩
      rintro rfl
      refine ⟨t₁〘xs〙, h, ?_⟩
      convert mem_singleton (∅ : M)
      simp
    | imp φ₁ φ₂ => by
      simp only [toBoundedFormula, BoundedFormula.realize'_imp] at h
      simp only [charRudimentaryTerm, RudimentaryTerm.realize_union]
      by_cases h₁ : φ₁.toBoundedFormula〘xs〙
      · simp [realize_charRudimentaryTerm_of_realize (h h₁),
          realize_charRudimentaryTerm_of_realize h₁]
      by_cases h₂ : φ₂.toBoundedFormula〘xs〙
      · simp [realize_charRudimentaryTerm_of_not_realize h₁,
          realize_charRudimentaryTerm_of_realize h₂]
      · simp [realize_charRudimentaryTerm_of_not_realize h₁,
          realize_charRudimentaryTerm_of_not_realize h₂]
    | allMem t ψ => by
      simp only [toBoundedFormula, BoundedFormula.realize_allMem] at h
      simp only [charRudimentaryTerm]
      apply RudimentaryTerm.realize_not_of_empty
      simp only [empty_iff, mem_realize_iUnion_iff, Term.realize_toRudimentaryTerm, not_exists,
        not_and]
      intro y z hz
      specialize h z hz
      have := realize_charRudimentaryTerm_of_realize h
      grind
    | rel R t => by
      simp only [toBoundedFormula, BoundedFormula.realize'_rel₁] at h
      simp [charRudimentaryTerm, h, singleton_eq]

  theorem realize_charRudimentaryTerm_of_not_realize {n : ℕ} [NeZero n]
      {φ : M.L.DeltaZeroBoundedFormula n} {xs : Fin n → M}
      (h : ¬φ.toBoundedFormula〘xs〙) :
      φ.charRudimentaryTerm 〘xs〙 = ∅ := match φ with
    | falsum => by simp [charRudimentaryTerm]
    | equal t₁ t₂ => by simpa [charRudimentaryTerm]
    | mem t₁ t₂ => by
      simp only [toBoundedFormula, realize'_mem] at h
      simp only [charRudimentaryTerm, empty_iff, mem_realize_iUnion_iff,
        Term.realize_toRudimentaryTerm, not_exists, not_and]
      intro z v hv
      suffices ((Term.toRudimentaryTerm t₁).castSucc.eqChar (ᵣlast n))〘snoc xs v〙 = ∅ by
        simp [this]
      simp only [RudimentaryTerm.realize_eqChar_empty_iff, RudimentaryTerm.realize_castSucc,
        Term.realize_toRudimentaryTerm, RudimentaryTerm.realize_basic, snoc_last, ne_eq]
      grind
    | imp φ₁ φ₂ => by
      simp only [toBoundedFormula, BoundedFormula.realize'_imp, Classical.not_imp] at h
      simp only [charRudimentaryTerm, RudimentaryTerm.realize_union, union_empty_iff]
      simp [realize_charRudimentaryTerm_of_realize h.left,
          realize_charRudimentaryTerm_of_not_realize h.right]
    | allMem t ψ => by
      simp only [toBoundedFormula, BoundedFormula.realize_allMem, not_forall,
        exists_prop] at h
      simp only [charRudimentaryTerm]
      apply RudimentaryTerm.realize_not_of_singleton_empty
      simp only [eq_singleton_iff, mem_realize_iUnion_iff, Term.realize_toRudimentaryTerm]
      obtain ⟨y, hy₁, hy₂⟩ := h
      have := realize_charRudimentaryTerm_of_not_realize hy₂
      exact fun z ↦ ⟨fun ⟨v, hv₁, hv₂⟩ ↦ IsZeroOrOne.empty_of_mem (by simp) hv₂,
        fun hz ↦ by grind⟩
    | rel R t => by
      simp only [toBoundedFormula, BoundedFormula.realize'_rel₁] at h
      simp [charRudimentaryTerm, h]
end

@[grind .]
theorem isZeroOrOne_charRudimentaryTerm {n : ℕ} [NeZero n]
    (φ : M.L.DeltaZeroBoundedFormula n) (xs : Fin n → M) :
    IsZeroOrOne φ.charRudimentaryTerm〘xs〙 := by
  grind [realize_charRudimentaryTerm_of_realize, realize_charRudimentaryTerm_of_not_realize]

@[simp, grind .]
theorem realize_charRudimentaryTerm_empty_iff {n : ℕ} [NeZero n]
    (φ : M.L.DeltaZeroBoundedFormula n) (xs : Fin n → M) :
    φ.charRudimentaryTerm〘xs〙 = ∅ ↔ ¬φ.toBoundedFormula〘xs〙 := by
  grind [realize_charRudimentaryTerm_of_realize, realize_charRudimentaryTerm_of_not_realize]

end DeltaZeroBoundedFormula

namespace RudimentaryTerm

variable [L.ExtraConstantsUnaryRelationsOnly] [M.L.ExtraConstantsUnaryRelationsOnly]

/-- If `r_truth〘xs〙 ≠ ∅`, then takes value `r〘xs〙`, else `∅` -/
noncomputable def ifTrue
  [NeZero n]
  (r : L.RudimentaryTerm n) (φ : L.DeltaZeroBoundedFormula n) :=
  r.ifNonempty φ.charRudimentaryTerm
  -- r_truth.iUnion r.castSucc


@[simp]
theorem castLHom_ifTrue
    [NeZero n]
    (r : M.L'.RudimentaryTerm n) (φ : M.L'.DeltaZeroBoundedFormula n) :
    (r.ifTrue φ).castLHom = r.castLHom.ifTrue φ.castLHom := by
  simp [ifTrue]

variable [M.Extensional] [M.RudClosed]

@[simp]
theorem realize_ifTrue_of_false [NeZero n] (r : M.L.RudimentaryTerm n)
    {φ : M.L.DeltaZeroBoundedFormula n}
    {xs : Fin n → M} (h : ¬φ.toBoundedFormula〘xs〙) :
    (r.ifTrue φ)〘xs〙 = ∅ := by
  simp only [ifTrue]
  convert realize_ifNonempty_of_empty _ _ (M := M)
  simp [h]

@[simp]
theorem realize_ifTrue_of_true [NeZero n] (r : M.L.RudimentaryTerm n)
    {φ : M.L.DeltaZeroBoundedFormula n}
    {xs : Fin n → M} (h : φ.toBoundedFormula〘xs〙) :
    (r.ifTrue φ)〘xs〙 = r〘xs〙 := by
  simp only [ifTrue]
  convert realize_ifNonempty_of_ne_empty _ _ (M := M)
  simp [h]

@[simp]
theorem realize_ifTrue_subset [NeZero n] (r : M.L.RudimentaryTerm n)
    {φ : M.L.DeltaZeroBoundedFormula n}
    {xs : Fin n → M} :
    (r.ifTrue φ)〘xs〙 ⊆ r〘xs〙 := by
  simp [ifTrue]

@[simp]
theorem mem_realize_ifTrue_iff [NeZero n] (r : M.L.RudimentaryTerm n)
    (φ : M.L.DeltaZeroBoundedFormula n)
    (xs : Fin n → M)
    (z : M) :
    z ∈ (r.ifTrue φ)〘xs〙 ↔ z ∈ r〘xs〙 ∧ φ.toBoundedFormula〘xs〙 := by
  simp [ifTrue]

end RudimentaryTerm

namespace DeltaZeroBoundedFormula

variable [L.ExtraConstantsUnaryRelationsOnly] [M.L.ExtraConstantsUnaryRelationsOnly]
variable [M.Extensional] [M.RudClosed]

noncomputable def comprehensionRudimentaryTerm (φ : L.DeltaZeroBoundedFormula (n + 1)) :
  L.RudimentaryTerm (n + 1) :=
  (ᵣ-1).iUnion <| ({ᵣ-1} : L.RudimentaryTerm (n + 2)).ifTrue <|
    (φ.substBoundBound (cons (last _) (castAdd 2)))
  -- φ.charRudimentaryTerm.iUnion {ᵣ0}

@[simp]
theorem mem_realize_comprehensionRudimentaryTerm_iff
    (φ : M.L.DeltaZeroBoundedFormula (n + 1))
    (xs : Fin (n + 1) → M) (z : M) :
    z ∈ φ.comprehensionRudimentaryTerm 〘xs〙 ↔
      z ∈ xs (last _) ∧ φ.toBoundedFormula 〘cons z (init xs)〙 := by
  nth_rw 1 [← Fin.snoc_init_self xs]
  set ys := init xs
  simp [comprehensionRudimentaryTerm]

@[simp]
theorem mem_realize_comprehensionRudimentaryTerm_iff_snoc
    (φ : M.L.DeltaZeroBoundedFormula (n + 1))
    (x : M) (xs : Fin n → M) (z : M) :
    z ∈ φ.comprehensionRudimentaryTerm 〘snoc xs x〙 ↔ z ∈ x ∧ φ.toBoundedFormula 〘cons z xs〙 := by
  convert mem_realize_comprehensionRudimentaryTerm_iff (M := M) _ _ _ <;> simp

@[simp]
theorem castLHom_comprehensionRudimentaryTerm (φ : M.L'.DeltaZeroBoundedFormula (n + 1)) :
    φ.comprehensionRudimentaryTerm.castLHom = φ.castLHom.comprehensionRudimentaryTerm := by
  simp [comprehensionRudimentaryTerm]

end DeltaZeroBoundedFormula

namespace MemStructure

open RudimentaryTerm Structure

variable [L.ExtraConstantsUnaryRelationsOnly]

variable [M.L.ExtraConstantsUnaryRelationsOnly] [M.Extensional] [M.RudClosed]
  (x y z : M) {n : ℕ}

instance (A : M.Class) [hA : A.DeltaZero Set.univ] : HasComprehension x A where
  hasComprehension := by
    obtain ⟨n, _, ⟨φ, rfl⟩, vs, -, hvs⟩ := hA.toDeltaZero
    use (φ.cast (by omega)).comprehensionRudimentaryTerm 〘snoc vs x〙
    simp only [IsComprehension,
      DeltaZeroBoundedFormula.mem_realize_comprehensionRudimentaryTerm_iff, snoc_last,
      DeltaZeroBoundedFormula.coe_cast, BoundedFormula.cast, init_snoc,
      BoundedFormula.realize'_substBoundBound, and_congr_right_iff]
    simp [Class.iff_toMulticlass, hvs, append_left_eq_cons]

@[simp]
theorem comprehension_top (x : M) :
    x ∩₀ ⊤ = x := by
  ext; simp

@[simp]
theorem comprehension_bot (x : M) :
    x ∩₀ ⊥ = ∅ := by
  ext; simp

end MemStructure

end FirstOrder.Language
