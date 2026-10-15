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

open Fin FirstOrder Language MemStructure

namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type max u v}
  [L.MemStructure M] [Inhabited M]
namespace MemStructure

variable (x y z : M) {n : ℕ}

def IsComprehension (a x : M) (A : Class M) := ∀ z, z ∈ a ↔ z ∈ x ∧ A z

noncomputable instance (x : M) (A : Class M) :
  Decidable (∃ a : M, IsComprehension a x A) :=
  Classical.propDecidable _

/-- The subset of `x` containing `z` for which `φ〘v, snoc xs z〙` holds -/
noncomputable def comprehension (x : M) (A : Class M) :=
  dite (∃ a : M, IsComprehension a x A)
    Classical.choose default

@[inherit_doc] scoped[FirstOrder.Language]
infix:88 " ∩₀ " => FirstOrder.Language.MemStructure.comprehension

class HasComprehension (x : M) (A : Class M) : Prop where
  protected hasComprehension : ∃ a : M, IsComprehension a x A

@[simp, grind =, push]
theorem mem_comprehension_iff (x : M) (A : Class M) [hx : HasComprehension x A] (z : M) :
    z ∈ x ∩₀ A ↔ z ∈ x ∧ A z := by
  convert Classical.choose_spec hx.hasComprehension z
  simp [MemStructure.comprehension, HasComprehension.hasComprehension]

theorem comprehension_subset (x : M) (A : Class M) [HasComprehension x A] :
    x ∩₀ A ⊆ x := by
  grind

@[simp]
theorem comprehension_eq_iff [Extensional M] (x : M) (A B : Class M)
    [HasComprehension x A] [HasComprehension x B] :
    x ∩₀ A = x ∩₀ B ↔ ∀ z ∈ x, A z ↔ B z := by
  simp [eq_iff]

@[simp]
theorem comprehension_eq_univ_iff [Extensional M] (x : M) (A : Class M) [HasComprehension x A] :
    x ∩₀ A = x ↔ ∀ z ∈ x, A z := by
  simp [eq_iff]

@[simp]
theorem comprehension_eq_empty_iff [Extensional M] [RudClosed M] (x : M) (A : Class M)
    [HasComprehension x A] :
    x ∩₀ A = ∅ ↔ ∀ z ∈ x, ¬A z := by
  simp [eq_iff]

variable (M) in
class ClosedUnderDefinableComprehension : Prop where
  closedUnderDefinableComprehension (x : M) (A : Class M)
    [A.Definable Set.univ] :
    ∃ a : M, IsComprehension a x A

-- export ClosedUnderDefinableComprehension (closedUnderDefinableComprehension)

instance [ClosedUnderDefinableComprehension M] (A : Class M) [A.Definable Set.univ] :
  HasComprehension x A :=
  ⟨ClosedUnderDefinableComprehension.closedUnderDefinableComprehension x A⟩

variable [RudClosed M] [Extensional M]

def IsZeroOrOne (x : M) := x = ∅ ∨ x = {∅}

@[grind =]
theorem isZeroOrOne_iff_subset_singleton_empty {x : M} :
    IsZeroOrOne x ↔ x ⊆ {∅} := by
  grind [IsZeroOrOne]

omit [Extensional M] in
@[simp, grind .]
theorem IsZeroOrOne.singleton_empty_iff_ne_empty {x : M} (hx : IsZeroOrOne x) :
    x = {∅} ↔ x ≠ ∅ := by
  grind [IsZeroOrOne]

omit [Extensional M] in
@[grind .]
theorem IsZeroOrOne.empty_of_mem {x z : M} (hx : IsZeroOrOne x) (hz : z ∈ x) : z = ∅ := by
  grind [IsZeroOrOne]

end MemStructure


namespace RudimentaryTerm

open MemStructure

-- variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]

/-- The rudimentary term that maps `x` to `1` is `x ≠ ∅`, `0` otherwise -/
def isNonempty₀ {L : Language} [L.HasMem] : L.RudimentaryTerm 1 := (ᵣ0).iUnion {∅}

/-- The rudimentary term that maps `xs` to `1` is `t〘xs〙 ≠ ∅`, `0` otherwise -/
@[simp]
def isNonempty {L : Language} [L.HasMem] (r : L.RudimentaryTerm n) :=
  isNonempty₀.substBoundRud ![r]

def not₀ {L : Language} [L.HasMem] : L.RudimentaryTerm 1 := {∅} \ ᵣ0

@[simp]
def not {L : Language} [L.HasMem] (r : L.RudimentaryTerm n) := not₀.substBoundRud ![r]

def isEmpty₀ {L : Language} [L.HasMem] : L.RudimentaryTerm 1 := (ᵣ0).isNonempty.not

@[simp]
def isEmpty {L : Language} [L.HasMem] (r : L.RudimentaryTerm n) := isEmpty₀.substBoundRud ![r]

def eqChar₀ {L : Language} [L.HasMem] : L.RudimentaryTerm 2 :=
  ((ᵣ0 \ ᵣ1) ∪ (ᵣ1 \ ᵣ0)).isEmpty

@[simp]
def eqChar {L : Language} [L.HasMem] (r₁ r₂ : L.RudimentaryTerm n) :=
  eqChar₀.substBoundRud ![r₁, r₂]

/-- If `xs 1 ≠ ∅`, then takes value `xs 0`, else `∅` -/
def ifNonempty₀ {L : Language} [L.HasMem] : L.RudimentaryTerm 2 := (ᵣ1).iUnion (ᵣ0)

/-- If `r_truth〘xs〙 ≠ ∅`, then takes value `r〘xs〙`, else `∅` -/
@[simp]
def ifNonempty {L : Language} [L.HasMem] (r : L.RudimentaryTerm n) (r_truth : L.RudimentaryTerm n) :=
  ifNonempty₀.substBoundRud ![r, r_truth]

instance {L : Language} [L.HasMem] :
  (isNonempty₀ : L.RudimentaryTerm 1).CharFree := by
  unfold isNonempty₀; infer_instance

instance {L : Language} [L.HasMem] (r : L.RudimentaryTerm n) [r.CharFree] :
  r.isNonempty.CharFree := by
  unfold isNonempty; infer_instance

instance {L : Language} [L.HasMem] :
  (not₀ : L.RudimentaryTerm 1).CharFree := by
  unfold not₀; infer_instance

instance {L : Language} [L.HasMem] (r : L.RudimentaryTerm n) [r.CharFree] :
  r.not.CharFree := by
  unfold not; infer_instance

instance {L : Language} [L.HasMem] :
  (isEmpty₀ : L.RudimentaryTerm 1).CharFree := by
  unfold isEmpty₀; infer_instance

instance {L : Language} [L.HasMem] (r : L.RudimentaryTerm n) [r.CharFree] :
  r.isEmpty.CharFree := by
  unfold isEmpty; infer_instance

instance {L : Language} [L.HasMem] :
  (eqChar₀ : L.RudimentaryTerm 2).CharFree := by
  unfold eqChar₀; infer_instance

instance {L : Language} [L.HasMem] (r₁ r₂ : L.RudimentaryTerm n)
  [r₁.CharFree] [r₂.CharFree] : (r₁.eqChar r₂).CharFree := by
  unfold eqChar; infer_instance

instance {L : Language} [L.HasMem] :
  (ifNonempty₀ : L.RudimentaryTerm 2).CharFree := by
  unfold ifNonempty₀; infer_instance

instance {L : Language} [L.HasMem] (r₁ r₂ : L.RudimentaryTerm n)
  [r₁.CharFree] [r₂.CharFree] : (r₁.ifNonempty r₂).CharFree := by
  unfold ifNonempty; infer_instance

variable [RudClosed M] [Extensional M] {xs : Fin 1 → M} {ys : Fin 2 → M}

-- @[simp, grind =]
theorem realize_isNonempty₀_of_ne_empty (h : xs 0 ≠ ∅) :
    isNonempty₀〘xs〙 = {∅} := by
  rw [ne_empty_iff] at h
  ext z
  simp [isNonempty₀, h]

-- @[simp, grind =]
theorem realize_isNonempty₀_of_empty (h : xs 0 = ∅) :
    isNonempty₀〘xs〙 = ∅ := by
  rw [empty_iff] at h
  ext z
  simp [isNonempty₀, h]

@[simp, grind .]
theorem isZeroOrOne_realize_isNonempty₀ :
    IsZeroOrOne (isNonempty₀〘xs〙 : M) := by
  grind [IsZeroOrOne, realize_isNonempty₀_of_ne_empty, realize_isNonempty₀_of_empty]

@[simp, grind =]
theorem realize_isNonempty₀_empty_iff :
    isNonempty₀〘xs〙 = ∅ ↔ xs 0 = ∅ := by
  grind [realize_isNonempty₀_of_ne_empty, realize_isNonempty₀_of_empty]

@[simp, grind =]
theorem realize_not₀_of_singleton_empty (h : xs 0 = {∅}) :
    not₀〘xs〙 = ∅ := by
  simp [not₀, h]

@[simp, grind =]
theorem realize_not₀_of_empty (h : xs 0 = ∅) :
    not₀〘xs〙 = {∅} := by
  simp [not₀, h]

@[simp, grind .]
theorem isZeroOrOne_realize_not₀ :
    IsZeroOrOne (not₀〘xs〙 : M) := by
  rw [isZeroOrOne_iff_subset_singleton_empty]
  simp only [not₀, realize_sdiff, singleton_def, realize_substBoundRud, realize_singleton₀,
    Matrix.cons_val_zero, realize_empty]
  grind

-- @[simp, grind =]
theorem realize_isEmpty₀_of_ne_empty (h : xs 0 ≠ ∅) :
    isEmpty₀〘xs〙 = ∅ := by
  simp [isEmpty₀, realize_isNonempty₀_of_ne_empty, h]

-- @[simp, grind =]
theorem realize_isEmpty₀_of_empty (h : xs 0 = ∅) :
    isEmpty₀〘xs〙 = {∅} := by
  simp [isEmpty₀, realize_isNonempty₀_of_empty, h]

@[simp, grind .]
theorem isZeroOrOne_realize_isEmpty₀ :
    IsZeroOrOne (isEmpty₀〘xs〙 : M) := by
  simp [isEmpty₀]

@[simp, grind =]
theorem realize_isEmpty₀_empty_iff :
    isEmpty₀〘xs〙 = ∅ ↔ xs 0 ≠ ∅ := by
  grind [realize_isEmpty₀_of_ne_empty, realize_isEmpty₀_of_empty]

-- @[simp, grind =]
theorem realize_eqChar₀_of_eq (h : ys 0 = ys 1) :
    eqChar₀〘ys〙 = {∅} := by
  simp [eqChar₀, h, realize_isEmpty₀_of_empty]

theorem realize_eqChar₀_of_ne (h : ys 0 ≠ ys 1) :
    eqChar₀〘ys〙 = ∅ := by
  simp only [eqChar₀]
  simp
  grind

@[simp, grind .]
theorem isZeroOrOne_realize_eqChar₀ :
    IsZeroOrOne (eqChar₀〘ys〙 : M) := by
  simp [eqChar₀]

@[simp, grind =]
theorem realize_eqChar₀_empty_iff :
    eqChar₀〘ys〙 = ∅ ↔ ys 0 ≠ ys 1 := by
  grind [realize_eqChar₀_of_eq, realize_eqChar₀_of_ne]

@[simp]
theorem realize_ifNonempty₀_of_empty (h : ys 1 = ∅) :
    ifNonempty₀〘ys〙 = ∅ := by
  ext z
  simp only [ifNonempty₀, mem_realize_iUnion_iff]
  grind [ne_empty_iff]

@[simp]
theorem realize_ifNonempty₀_of_ne_empty (h : ys 1 ≠ ∅) :
    ifNonempty₀〘ys〙 = ys 0 := by
  rw [ne_empty_iff] at h
  ext z
  simp only [ifNonempty₀, mem_realize_iUnion_iff, realize_basic]
  simp only [Fin.snoc, Fin.val_zero]
  grind

@[simp]
theorem realize_ifNonempty₀_subset :
    ifNonempty₀〘ys〙 ⊆ ys 0 := by
  by_cases ys 1 = ∅ <;> grind [realize_ifNonempty₀_of_empty, realize_ifNonempty₀_of_ne_empty]

@[simp]
theorem mem_realize_ifNonempty₀_iff (z : M) :
    z ∈ ifNonempty₀〘ys〙 ↔ z ∈ ys 0 ∧ ys 1 ≠ ∅ := by
  grind [realize_ifNonempty₀_of_empty, realize_ifNonempty₀_of_ne_empty, realize_ifNonempty₀_subset]

end RudimentaryTerm

namespace DeltaZeroBoundedFormula

variable [L.ExtraConstantsUnaryRelationsOnly]
  [Extensional M] [RudClosed M]
variable {n m k : ℕ}

open MemStructure RudimentaryTerm

/-- The characteristic function of `φ` that maps `xs` to `1` if `φ〘xs〙` holds, `0` otherwise -/
noncomputable def charRudimentaryTerm {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  {n : ℕ} [NeZero n]
  (φ : L.DeltaZeroBoundedFormula n) :
  L.RudimentaryTerm n :=
  match φ with
  | falsum => ∅
  | equal t₁ t₂ => t₁.toRudimentaryTerm.eqChar t₂.toRudimentaryTerm
  | mem t₁ t₂ => t₂.toRudimentaryTerm.iUnion (t₁.toRudimentaryTerm.castSucc.eqChar ᵣ-1)
  | imp φ₁ φ₂ => φ₁.charRudimentaryTerm.not ∪ φ₂.charRudimentaryTerm
  | allMem t ψ => (t.toRudimentaryTerm.iUnion ψ.charRudimentaryTerm.not).not
  | rel R t => .char R t.toRudimentaryTerm

instance {L : Language} [L.HasMem]
  [L.ExtraConstantsUnaryRelationsOnly] {n : ℕ} [hn : NeZero n]
  (φ : L.DeltaZeroBoundedFormula n) [hφ : φ.RelFree] :
  φ.charRudimentaryTerm.CharFree := by
  induction hφ using relFreeCases generalizing hn with
  | falsum => simp only [charRudimentaryTerm]; infer_instance
  | equal t₁ t₂ => simp only [charRudimentaryTerm]; infer_instance
  | mem t₁ t₂ => simp only [charRudimentaryTerm]; infer_instance
  | imp φ₁ φ₂ _ _ _ ih₁ ih₂ =>
    simp only [charRudimentaryTerm]; infer_instance
  | allMem t ψ _ _ ih =>
    simp only [charRudimentaryTerm]; infer_instance

mutual
  theorem realize_charRudimentaryTerm_of_realize {n : ℕ} [NeZero n]
      {φ : L.DeltaZeroBoundedFormula n} {xs : Fin n → M}
      (h : φ.toBoundedFormula〘xs〙) :
      φ.charRudimentaryTerm 〘xs〙 = {∅} := match φ with
    | falsum => by simp at h
    | equal t₁ t₂ => by simpa [charRudimentaryTerm]
    | mem t₁ t₂ => by
      simp only [toBoundedFormula, realize'_mem] at h
      simp only [charRudimentaryTerm, ← all_mem_iff_eq_iff_singleton, mem_realize_iUnion_iff,
        Term.realize_toRudimentaryTerm]
      intro z
      refine ⟨fun ⟨w, hw₁, hw₂⟩ ↦ IsZeroOrOne.empty_of_mem (by simp) hw₂, ?_⟩
      rintro rfl
      refine ⟨t₁〘xs〙, h, ?_⟩
      convert mem_singleton (∅ : M)
      simp
    | imp φ₁ φ₂ => by
      simp only [toBoundedFormula, BoundedFormula.realize'_imp] at h
      simp only [charRudimentaryTerm]
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
      simp only [charRudimentaryTerm, RudimentaryTerm.not, RudimentaryTerm.realize_substBoundRud]
      apply realize_not₀_of_empty
      simp only [Matrix.cons_val_zero, empty_iff, mem_realize_iUnion_iff, Term.realize_toRudimentaryTerm, not_exists,
        not_and]
      intro y z hz
      specialize h z hz
      simp [realize_charRudimentaryTerm_of_realize h]
    | rel R t => by
      simp only [toBoundedFormula, BoundedFormula.realize'_rel₁] at h
      simp [charRudimentaryTerm, h, singleton_eq]

  theorem realize_charRudimentaryTerm_of_not_realize {n : ℕ} [NeZero n]
      {φ : L.DeltaZeroBoundedFormula n} {xs : Fin n → M}
      (h : ¬φ.toBoundedFormula〘xs〙) :
      φ.charRudimentaryTerm 〘xs〙 = ∅ := match φ with
    | falsum => by simp [charRudimentaryTerm]
    | equal t₁ t₂ => by simpa [charRudimentaryTerm]
    | mem t₁ t₂ => by
      simp only [toBoundedFormula, realize'_mem] at h
      simp only [charRudimentaryTerm, empty_iff, mem_realize_iUnion_iff,
        Term.realize_toRudimentaryTerm, not_exists, not_and]
      intro z v hv
      suffices (t₁.toRudimentaryTerm.castSucc.eqChar (ᵣlast n))〘snoc xs v〙 = ∅ by
        rw [this]; simp
      simp only [eqChar, RudimentaryTerm.realize_substBoundRud, realize_eqChar₀_empty_iff, Matrix.cons_val_zero,
        Matrix.cons_val_one, RudimentaryTerm.realize_castSucc,
        Term.realize_toRudimentaryTerm, RudimentaryTerm.realize_basic, snoc_last, ne_eq]
      grind
    | imp φ₁ φ₂ => by
      simp only [toBoundedFormula, BoundedFormula.realize'_imp, Classical.not_imp] at h
      simp [charRudimentaryTerm, realize_charRudimentaryTerm_of_realize h.left,
          realize_charRudimentaryTerm_of_not_realize h.right]
    | allMem t ψ => by
      simp only [toBoundedFormula, BoundedFormula.realize_allMem, not_forall,
        exists_prop] at h
      simp only [charRudimentaryTerm, RudimentaryTerm.not, RudimentaryTerm.realize_substBoundRud]
      apply realize_not₀_of_singleton_empty
      simp only [Matrix.cons_val_zero, ← all_mem_iff_eq_iff_singleton, mem_realize_iUnion_iff, Term.realize_toRudimentaryTerm]
      obtain ⟨y, hy₁, hy₂⟩ := h
      have := realize_charRudimentaryTerm_of_not_realize hy₂
      exact fun z ↦ ⟨fun ⟨v, hv₁, hv₂⟩ ↦ IsZeroOrOne.empty_of_mem (by simp) hv₂,
        fun hz ↦ ⟨y, hy₁, by simp [this, hz]⟩⟩
    | rel R t => by
      simp only [toBoundedFormula, BoundedFormula.realize'_rel₁] at h
      simp [charRudimentaryTerm, h]
end

@[grind .]
theorem isZeroOrOne_charRudimentaryTerm {n : ℕ} [NeZero n]
    (φ : L.DeltaZeroBoundedFormula n) (xs : Fin n → M) :
    IsZeroOrOne (φ.charRudimentaryTerm〘xs〙 : M) := by
  grind [realize_charRudimentaryTerm_of_realize, realize_charRudimentaryTerm_of_not_realize]

@[simp, grind .]
theorem realize_charRudimentaryTerm_empty_iff {n : ℕ} [NeZero n]
    (φ : L.DeltaZeroBoundedFormula n) (xs : Fin n → M) :
    φ.charRudimentaryTerm〘xs〙 = ∅ ↔ ¬φ.toBoundedFormula〘xs〙 := by
  grind [realize_charRudimentaryTerm_of_realize, realize_charRudimentaryTerm_of_not_realize]

end DeltaZeroBoundedFormula

namespace RudimentaryTerm

-- variable [L.ExtraConstantsUnaryRelationsOnly]

/-- If `r_truth〘xs〙 ≠ ∅`, then takes value `r〘xs〙`, else `∅` -/
noncomputable def ifTrue {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  [NeZero n]
  (r : L.RudimentaryTerm n) (φ : L.DeltaZeroBoundedFormula n) :=
  r.ifNonempty φ.charRudimentaryTerm


instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] [NeZero n]
  (r : L.RudimentaryTerm n) (φ : L.DeltaZeroBoundedFormula n)
  [r.CharFree] [φ.RelFree] :
  (r.ifTrue φ).CharFree := by
  unfold ifTrue; infer_instance

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

@[simp]
theorem realize_ifTrue_of_false [NeZero n] (r : L.RudimentaryTerm n)
    {φ : L.DeltaZeroBoundedFormula n}
    {xs : Fin n → M} (h : ¬φ.toBoundedFormula〘xs〙) :
    (r.ifTrue φ)〘xs〙 = ∅ := by
  simp only [ifTrue, ifNonempty, realize_substBoundRud]
  apply realize_ifNonempty₀_of_empty
  simp [h]

@[simp]
theorem realize_ifTrue_of_true [NeZero n] (r : L.RudimentaryTerm n)
    {φ : L.DeltaZeroBoundedFormula n}
    {xs : Fin n → M} (h : φ.toBoundedFormula〘xs〙) :
    (r.ifTrue φ)〘xs〙 = r〘xs〙 := by
  simp only [ifTrue, ifNonempty, realize_substBoundRud]
  apply realize_ifNonempty₀_of_ne_empty
  simp [h]

@[simp]
theorem realize_ifTrue_subset [NeZero n] (r : L.RudimentaryTerm n)
    {φ : L.DeltaZeroBoundedFormula n}
    {xs : Fin n → M} :
    (r.ifTrue φ)〘xs〙 ⊆ r〘xs〙 := by
  simp only [ifTrue, ifNonempty, realize_substBoundRud]
  exact realize_ifNonempty₀_subset

@[simp]
theorem mem_realize_ifTrue_iff [NeZero n] (r : L.RudimentaryTerm n)
    (φ : L.DeltaZeroBoundedFormula n)
    (xs : Fin n → M)
    (z : M) :
    z ∈ (r.ifTrue φ)〘xs〙 ↔ z ∈ r〘xs〙 ∧ φ.toBoundedFormula〘xs〙 := by
  simp [ifTrue]

end RudimentaryTerm

namespace DeltaZeroBoundedFormula

noncomputable def comprehensionRudimentaryTerm {L : Language} [L.HasMem]
  [L.ExtraConstantsUnaryRelationsOnly]
  (φ : L.DeltaZeroBoundedFormula (n + 1)) :
  L.RudimentaryTerm (n + 1) :=
  (ᵣ-1).iUnion <| ({ᵣ-1} : L.RudimentaryTerm (n + 2)).ifTrue <|
    (φ.substBoundBound (cons (last _) (castAdd 2)))
  -- φ.charRudimentaryTerm.iUnion {ᵣ0}

instance {L : Language} [L.HasMem]
  [L.ExtraConstantsUnaryRelationsOnly]
  (φ : L.DeltaZeroBoundedFormula (n + 1)) [φ.RelFree] :
  φ.comprehensionRudimentaryTerm.CharFree := by
  unfold comprehensionRudimentaryTerm; infer_instance

variable [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M]

@[simp]
theorem mem_realize_comprehensionRudimentaryTerm_iff
    (φ : L.DeltaZeroBoundedFormula (n + 1))
    (xs : Fin (n + 1) → M) (z : M) :
    z ∈ φ.comprehensionRudimentaryTerm 〘xs〙 ↔
      z ∈ xs (last _) ∧ φ.toBoundedFormula 〘cons z (init xs)〙 := by
  nth_rw 1 [← Fin.snoc_init_self xs]
  set ys := init xs
  simp [comprehensionRudimentaryTerm]

@[simp]
theorem mem_realize_comprehensionRudimentaryTerm_iff_snoc
    (φ : L.DeltaZeroBoundedFormula (n + 1))
    (x : M) (xs : Fin n → M) (z : M) :
    z ∈ φ.comprehensionRudimentaryTerm 〘snoc xs x〙 ↔ z ∈ x ∧ φ.toBoundedFormula 〘cons z xs〙 := by
  convert mem_realize_comprehensionRudimentaryTerm_iff (M := M) _ _ _ <;> simp

end DeltaZeroBoundedFormula

namespace MemStructure

open RudimentaryTerm Structure

-- variable [L.ExtraConstantsUnaryRelationsOnly]

variable [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M]
  (x y z : M) {n : ℕ}

instance (A : Class M) [hA : A.DeltaZero Set.univ] : HasComprehension x A where
  hasComprehension := by
    obtain ⟨n, _, ⟨φ, rfl⟩, vs, -, hvs⟩ := hA.toDeltaZero
    use (φ.cast (by omega)).comprehensionRudimentaryTerm 〘snoc vs x〙
    simp only [IsComprehension,
      DeltaZeroBoundedFormula.mem_realize_comprehensionRudimentaryTerm_iff, snoc_last,
      DeltaZeroBoundedFormula.coe_cast, BoundedFormula.cast, init_snoc,
      BoundedFormula.realize'_substBoundBound, and_congr_right_iff]
    simp [Class.toMulticlass_eq_iff.mp hvs, append_left_eq_cons]

@[simp]
theorem comprehension_top (x : M) :
    x ∩₀ ⊤ = x := by
  ext; simp

@[simp]
theorem comprehension_bot [RudClosed M] (x : M) :
    x ∩₀ ⊥ = ∅ := by
  ext; simp

end MemStructure

end FirstOrder.Language
