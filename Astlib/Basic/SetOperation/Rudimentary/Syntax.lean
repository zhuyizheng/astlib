/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Astlib.Basic.SetOperation.MemStructure.Levy
/-!
file docstring
-/
open FirstOrder Language BoundedFormula Fin Term BoundedFormula


namespace FirstOrder.Language

variable {L : FirstOrder.Language.{u, v}} [L.HasMem]
--  [L.ExtraConstantsUnaryRelationsOnly]
  -- [L.ExtraConstantsOnly]

inductive RudimentaryTerm [L.HasMem] : ℕ → Type max u v
  | var : Fin n → RudimentaryTerm n
  | const (c : L.Constants) : RudimentaryTerm n
  | unorderedPair (r₁ r₂ : RudimentaryTerm n) : RudimentaryTerm n
  | sdiff (r₁ r₂ : RudimentaryTerm n) : RudimentaryTerm n
  | iUnion (ri : RudimentaryTerm n) (rf : RudimentaryTerm (n + 1)) :
    RudimentaryTerm n
  | char (R : L.Relations 1) (r : RudimentaryTerm n) : RudimentaryTerm n

@[inherit_doc] scoped[FirstOrder] prefix:110 "ᵣ" => FirstOrder.Language.RudimentaryTerm.var

/-- The largest index of the bounded variables -/
scoped[FirstOrder] notation "ᵣ-1" => ᵣ(last _)

/-- The second largest index of the bounded variables -/
scoped[FirstOrder] notation "ᵣ-2" => ᵣ(castAdd 1 (last _))

/-- The third largest index of the bounded variables -/
scoped[FirstOrder] notation "ᵣ-3" => ᵣ(castAdd 2 (last _))

/-- The fourth largest index of the bounded variables -/
scoped[FirstOrder] notation "ᵣ-4" => ᵣ(castAdd 3 (last _))

@[inherit_doc] scoped[FirstOrder] notation:max "ᵣ{" x ", " y "}" =>
  FirstOrder.Language.RudimentaryTerm.unorderedPair x y


  -- reverseInduction last (fun i _ => cast i) i
namespace RudimentaryTerm


def depth (r : L.RudimentaryTerm n) : ℕ := match r with
  | var _ => 0
  | const _ => 0
  | unorderedPair r₁ r₂ => (max r₁.depth r₂.depth) + 1
  | sdiff r₁ r₂ => (max r₁.depth r₂.depth) + 1
  | iUnion ri rf => (max ri.depth rf.depth) + 1
  | char _ r => r.depth + 1

/-- Whether `r` does not contain any characteristic function of a unary relation -/
def isCharFree (r : L.RudimentaryTerm n) : Prop := match r with
  | var _ => True
  | const _ => True
  | unorderedPair r₁ r₂ => r₁.isCharFree ∧ r₂.isCharFree
  | sdiff r₁ r₂ => r₁.isCharFree ∧ r₂.isCharFree
  | iUnion ri rf => ri.isCharFree ∧ rf.isCharFree
  | char _ _ => False

/-- `r` does not contain any characteristic function of a unary relation -/
class CharFree (r : L.RudimentaryTerm n) : Prop where
  charFree : r.isCharFree

theorem charFree_iff_isCharFree (r : L.RudimentaryTerm n) : r.CharFree ↔ r.isCharFree :=
  ⟨fun h ↦ h.charFree, fun h ↦ ⟨h⟩⟩

instance (i : Fin n) : (ᵣi : L.RudimentaryTerm n).CharFree := ⟨trivial⟩

instance (c : L.Constants) : (const c : L.RudimentaryTerm n).CharFree := ⟨trivial⟩

theorem charFree_unorderedPair_iff (r₁ r₂ : L.RudimentaryTerm n) :
    (unorderedPair r₁ r₂).CharFree ↔ r₁.CharFree ∧ r₂.CharFree := by
  simp [charFree_iff_isCharFree, isCharFree]

instance (r₁ r₂ : L.RudimentaryTerm n) [r₁.CharFree] [r₂.CharFree] :
  (unorderedPair r₁ r₂).CharFree :=
  (charFree_unorderedPair_iff _ _).mpr ⟨inferInstance, inferInstance⟩

theorem CharFree.of_unorderedPair_left (r₁ r₂ : L.RudimentaryTerm n)
    [h : (unorderedPair r₁ r₂).CharFree] : r₁.CharFree :=
  ((charFree_unorderedPair_iff _ _).mp h).left

theorem CharFree.of_unorderedPair_right (r₁ r₂ : L.RudimentaryTerm n)
    [h : (unorderedPair r₁ r₂).CharFree] : r₂.CharFree :=
  ((charFree_unorderedPair_iff _ _).mp h).right

theorem charFree_sdiff_iff (r₁ r₂ : L.RudimentaryTerm n) :
    (sdiff r₁ r₂).CharFree ↔ r₁.CharFree ∧ r₂.CharFree := by
  simp [charFree_iff_isCharFree, isCharFree]

instance (r₁ r₂ : L.RudimentaryTerm n) [r₁.CharFree] [r₂.CharFree] :
  (sdiff r₁ r₂).CharFree :=
  (charFree_sdiff_iff _ _).mpr ⟨inferInstance, inferInstance⟩

theorem CharFree.of_sdiff_left (r₁ r₂ : L.RudimentaryTerm n)
    [h : (sdiff r₁ r₂).CharFree] : r₁.CharFree :=
  ((charFree_sdiff_iff _ _).mp h).left

theorem CharFree.of_sdiff_right (r₁ r₂ : L.RudimentaryTerm n)
    [h : (sdiff r₁ r₂).CharFree] : r₂.CharFree :=
  ((charFree_sdiff_iff _ _).mp h).right

theorem charFree_iUnion_iff (ri : L.RudimentaryTerm n) (rf : L.RudimentaryTerm (n + 1)) :
    (iUnion ri rf).CharFree ↔ ri.CharFree ∧ rf.CharFree := by
  simp [charFree_iff_isCharFree, isCharFree]

instance (ri : L.RudimentaryTerm n) (rf : L.RudimentaryTerm (n + 1)) [ri.CharFree] [rf.CharFree] :
  (iUnion ri rf).CharFree :=
  (charFree_iUnion_iff _ _).mpr ⟨inferInstance, inferInstance⟩

theorem CharFree.of_iUnion_index (ri : L.RudimentaryTerm n) (rf : L.RudimentaryTerm (n + 1))
    [h : (iUnion ri rf).CharFree] : ri.CharFree :=
  ((charFree_iUnion_iff _ _).mp h).left

theorem CharFree.of_iUnion_function (ri : L.RudimentaryTerm n) (rf : L.RudimentaryTerm (n + 1))
    [h : (iUnion ri rf).CharFree] : rf.CharFree :=
  ((charFree_iUnion_iff _ _).mp h).right

@[simp, grind .]
theorem not_charFree_char (R : L.Relations 1) (r : L.RudimentaryTerm n) :
    ¬(char R r).CharFree := by
  simp [charFree_iff_isCharFree, isCharFree]

instance {k : ℕ} (r : L.RudimentaryTerm n) (rs : Fin k → L.RudimentaryTerm n)
  [r.CharFree] [∀ i, (rs i).CharFree] (i : Fin (k + 1)) :
  (Matrix.vecCons r rs i).CharFree := by
  cases i using Fin.cases
  · rw [Matrix.cons_val_zero]; infer_instance
  · rw [Matrix.cons_val_succ]; infer_instance

instance {k l : ℕ} (f : L.RudimentaryTerm k → L.RudimentaryTerm n)
  (rs : Fin l → L.RudimentaryTerm k) [h : ∀ i, (f (rs i)).CharFree] (i : Fin l) :
  ((f ∘ rs) i).CharFree :=
  h i

instance (i : Fin 0) : (Matrix.vecEmpty i : L.RudimentaryTerm n).CharFree :=
  i.elim0

instance {k : ℕ} (rs : Fin k → L.RudimentaryTerm n) (r : L.RudimentaryTerm n)
  [∀ i, (rs i).CharFree] [r.CharFree] (i : Fin (k + 1)) :
  (snoc (α := fun _ ↦ L.RudimentaryTerm n) rs r i).CharFree := by
  cases i using lastCases
  · rw [snoc_last]; infer_instance
  · rw [snoc_castSucc]; infer_instance

@[elab_as_elim] def charFreeCases
  {motive : ∀ {n}, ∀ {r : L.RudimentaryTerm n}, r.CharFree → Sort _}
  (var : ∀ {n}, ∀ i : Fin n, ∀ h : (ᵣi : L.RudimentaryTerm n).CharFree, motive h)
  (const : ∀ {n}, ∀ c : L.Constants, ∀ h : (const c : L.RudimentaryTerm n).CharFree, motive h)
  (unorderedPair : ∀ {n}, ∀ r₁ r₂ : L.RudimentaryTerm n, ∀ hr₁ : r₁.CharFree, ∀ hr₂ : r₂.CharFree,
    ∀ hr : (unorderedPair r₁ r₂).CharFree,
    motive hr₁ → motive hr₂ → motive hr)
  (sdiff : ∀ {n}, ∀ r₁ r₂ : L.RudimentaryTerm n, ∀ hr₁ : r₁.CharFree, ∀ hr₂ : r₂.CharFree,
    ∀ hr : (sdiff r₁ r₂).CharFree,
    motive hr₁ → motive hr₂ → motive hr)
  (iUnion : ∀ {n}, ∀ ri : L.RudimentaryTerm n, ∀ rf : L.RudimentaryTerm (n + 1),
    ∀ hri : ri.CharFree, ∀ hrf : rf.CharFree,
    ∀ hr : (iUnion ri rf).CharFree,
    motive hri → motive hrf → motive hr)
  {n} {r : L.RudimentaryTerm n} (hr : r.CharFree) :
  motive hr := by
  cases r with
  | var i => exact var _ hr
  | const i => exact const _ hr
  | unorderedPair r₁ r₂ =>
    have h₁ := CharFree.of_unorderedPair_left r₁ r₂
    have h₂ := CharFree.of_unorderedPair_right r₁ r₂
    exact unorderedPair _ _ h₁ h₂ _ (charFreeCases var const unorderedPair sdiff iUnion h₁)
      (charFreeCases var const unorderedPair sdiff iUnion h₂)
  | sdiff r₁ r₂ =>
    have h₁ := CharFree.of_sdiff_left r₁ r₂
    have h₂ := CharFree.of_sdiff_right r₁ r₂
    exact sdiff _ _ h₁ h₂ _ (charFreeCases var const unorderedPair sdiff iUnion h₁)
      (charFreeCases var const unorderedPair sdiff iUnion h₂)
  | iUnion ri rf =>
    have h₁ := CharFree.of_iUnion_index ri rf
    have h₂ := CharFree.of_iUnion_function ri rf
    exact iUnion _ _ h₁ h₂ _ (charFreeCases var const unorderedPair sdiff iUnion h₁)
      (charFreeCases var const unorderedPair sdiff iUnion h₂)
  | char R r => simp at hr

def substBoundBound {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n)
    (f : Fin n → Fin m) :
    L.RudimentaryTerm m :=
  match r with
  | .var i => var (f i)
  | .unorderedPair r₁ r₂ => unorderedPair (r₁.substBoundBound f) (r₂.substBoundBound f)
  | .sdiff r₁ r₂ => sdiff (r₁.substBoundBound f) (r₂.substBoundBound f)
  | .iUnion ri rf =>
    iUnion (ri.substBoundBound f) (rf.substBoundBound (snoc (fun i ↦ (f i).castSucc) (last _)))
  | char R r => char R (r.substBoundBound f)
  | const c => const c

@[simp]
theorem depth_substBoundBound {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n)
    (f : Fin n → Fin m) :
    (r.substBoundBound f).depth = r.depth := by
  induction r generalizing m with
  | var _ => simp [depth, substBoundBound]
  | unorderedPair r₁ r₂ ih₁ ih₂ => simp [depth, substBoundBound, ih₁, ih₂]
  | sdiff r₁ r₂ ih₁ ih₂ => simp [depth, substBoundBound, ih₁, ih₂]
  | iUnion ri rf ihi ihf => simp [depth, substBoundBound, ihi, ihf]
  | const c => simp [depth, substBoundBound]
  | char R r ih => simp [depth, substBoundBound, ih]

@[simp]
theorem isCharFree_substBoundBound {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n)
    (f : Fin n → Fin m) :
    (r.substBoundBound f).isCharFree ↔ r.isCharFree := by
  induction r generalizing m with
  | var _ => simp [isCharFree, substBoundBound]
  | unorderedPair r₁ r₂ ih₁ ih₂ => simp [isCharFree, substBoundBound, ih₁, ih₂]
  | sdiff r₁ r₂ ih₁ ih₂ => simp [isCharFree, substBoundBound, ih₁, ih₂]
  | iUnion ri rf ihi ihf => simp [isCharFree, substBoundBound, ihi, ihf]
  | const c => simp [isCharFree, substBoundBound]
  | char R r _ => simp [isCharFree, substBoundBound]

def substBoundRud {L : Language} [L.HasMem] {n : ℕ} (r : L.RudimentaryTerm n)
    (rs : Fin n → L.RudimentaryTerm m) :
    L.RudimentaryTerm m :=
  match r with
  | .var i => rs i
  | .unorderedPair r₁ r₂ => unorderedPair (r₁.substBoundRud rs) (r₂.substBoundRud rs)
  | .sdiff r₁ r₂ => sdiff (r₁.substBoundRud rs) (r₂.substBoundRud rs)
  | .iUnion ri rf =>
    iUnion (ri.substBoundRud rs)
      (rf.substBoundRud (snoc (fun i ↦ (rs i).substBoundBound castSucc) (var (last _))))
  | .const c => const c
  | .char R r => char R (r.substBoundRud rs)

def castLE {L : Language} [L.HasMem] {n m : ℕ} (r : L.RudimentaryTerm n) (h : n ≤ m) :
    L.RudimentaryTerm m := r.substBoundBound (Fin.castLE h)

def castAdd {L : Language} [L.HasMem] {n : ℕ} (r : L.RudimentaryTerm n) (m : ℕ) :
    L.RudimentaryTerm (n + m) := r.castLE (n.le_add_right m)

def castSucc {L : Language} [L.HasMem] {n : ℕ} (r : L.RudimentaryTerm n) :
    L.RudimentaryTerm (n + 1) := r.castAdd 1

theorem charFree_substBoundBound_iff {L : Language} [L.HasMem] {m n : ℕ}
    (r : L.RudimentaryTerm n) (f : Fin n → Fin m) :
    (r.substBoundBound f).CharFree ↔ r.CharFree := by
  simp [charFree_iff_isCharFree]

instance {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n) [r.CharFree]
  (f : Fin n → Fin m) : (r.substBoundBound f).CharFree :=
  (charFree_substBoundBound_iff _ _).mpr inferInstance

instance {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n) [r.CharFree]
  (h : n ≤ m) : (r.castLE h).CharFree := by
  unfold castLE; infer_instance

instance {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n) [r.CharFree] :
  (r.castAdd m).CharFree := by
  unfold castAdd; infer_instance

instance {L : Language} [L.HasMem] {n : ℕ} (r : L.RudimentaryTerm n) [r.CharFree] :
  r.castSucc.CharFree := by
  unfold castSucc; infer_instance

instance {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n)
  [hr : r.CharFree]
  (rs : Fin n → L.RudimentaryTerm m) [hrs : ∀ i, (rs i).CharFree] :
  (r.substBoundRud rs).CharFree := by
  induction hr using charFreeCases generalizing m <;>
    (simp only [substBoundRud]; infer_instance)

def _root_.Fin.lowerAt (i : Fin (n + 1)) {k : Fin (n + 1)} (h : i ≠ k) : Fin n :=
  if hi : i.val < k.val then i.castPred (ne_last_of_lt hi)
  else i.pred (val_ne_zero_iff.mp (by omega))

variable [L.ExtraConstantsUnaryRelationsOnly]

def _root_.FirstOrder.Language.Term.lowerAt
  (t : L.Term' (n + 1)) {k : Fin (n + 1)} (h : t ≠ &k) : L.Term' n :=
  match t with
  | .var (Sum.inr i) => .var (Sum.inr (Fin.lowerAt i
      (Ne.intro fun a ↦ h (congrArg _ (congrArg _ a)))))
  | .func F _ (l := 0) => .func F elim0
  | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F

noncomputable instance : DecidableEq (L.Functions n) := Classical.typeDecidableEq _

mutual
noncomputable def hasMem {n : ℕ} (r : L.RudimentaryTerm n) (t : L.Term' n) :
  L.DeltaZeroBoundedFormula n :=
  match r with
  | .var i => t ∈₀ &i
  | .const c => t ∈₀ c.term
  | .unorderedPair r₁ r₂ => r₁.eq t ⊔ r₂.eq t
  | .sdiff r₁ r₂ => r₁.hasMem t ⊓ ∼(r₂.hasMem t)
  | .iUnion ri rf => ri.exMem (rf.hasMem t.castSucc)
  | .char _ _ => ⊥
  termination_by (r.depth, 1, 0)
  decreasing_by all_goals simp [depth, Prod.lex_def]

noncomputable def eq {n : ℕ} (r : L.RudimentaryTerm n) (t : L.Term' n) :
  L.DeltaZeroBoundedFormula n :=
  match r with
  | .var i => t =₀ &i
  | .const c => t =₀ c.term
  | .unorderedPair r₁ r₂ =>
    r₁.mem t ⊓ r₂.mem t ⊓ ∀₀∈ t (r₁.castSucc.eq &-1 ⊔ r₂.castSucc.eq &-1)
  | .sdiff r₁ r₂ =>
    (∀₀∈ t (r₁.castSucc.hasMem &-1 ⊓ ∼(r₂.castSucc.hasMem &-1))) ⊓
      r₁.allMem (r₂.castSucc.hasMem &-1 ⊔ &-1 ∈₀ t.castSucc)
  | .iUnion ri rf =>
    (∀₀∈ t ri.castSucc.exMem ((rf.substBoundBound (snoc (Fin.castAdd 2) (last _))).hasMem &-2)) ⊓
      ri.allMem (rf.allMem (&-1 ∈₀ (t.castAdd 2)))
  | .char _ _ => ⊥
  termination_by (r.depth, 1, 0)
  decreasing_by all_goals simp [depth, castSucc, castAdd, castLE, Prod.lex_def]

noncomputable def mem {n : ℕ} (r : L.RudimentaryTerm n) (t : L.Term' n) :
  L.DeltaZeroBoundedFormula n :=
  ∃₀∈ t (r.castSucc.eq &-1)
  termination_by (r.depth, 2, 0)
  decreasing_by simp [castSucc, castAdd, castLE, Prod.lex_def]

noncomputable def memSelf {n : ℕ} (r : L.RudimentaryTerm n) :
  L.DeltaZeroBoundedFormula n :=
  r.exMem (r.castSucc.eq &-1)
  termination_by (r.depth, 3, 0)
  decreasing_by all_goals simp [castSucc, castAdd, castLE, Prod.lex_def]

noncomputable def allMem {n : ℕ} (r : L.RudimentaryTerm n)
   (φ : L.DeltaZeroBoundedFormula (n + 1)) :
  L.DeltaZeroBoundedFormula n :=
  match r with
  | .var i => ∀₀∈ &i φ
  | .const c => ∀₀∈ c.term φ
  | .unorderedPair r₁ r₂ =>
    r₁.substLowerAt (k := last _) φ ⊓ r₂.substLowerAt (k := last _) φ
  | .sdiff r₁ r₂ => r₁.allMem (r₂.castSucc.hasMem &-1 ⊔ φ)
  | .iUnion ri rf => ri.allMem (rf.allMem (φ.substBoundBound (snoc (Fin.castAdd 2) (last _))))
  | .char _ _ => ⊥
  termination_by (r.depth, 1, 0)
  decreasing_by all_goals simp [castSucc, castAdd, castLE, depth, Prod.lex_def]

noncomputable def exMem {n : ℕ} (r : L.RudimentaryTerm n)
   (φ : L.DeltaZeroBoundedFormula (n + 1)) :
L.DeltaZeroBoundedFormula n :=
  ∼(r.allMem (∼φ))
  termination_by (r.depth, 2, 0)
  decreasing_by all_goals simp [Prod.lex_def]

noncomputable def substLowerAt {n : ℕ} {k : Fin (n + 1)}
  (r : L.RudimentaryTerm k.val)
  (φ : L.DeltaZeroBoundedFormula (n + 1)) :
  L.DeltaZeroBoundedFormula n :=
  match φ with
  | .falsum => .falsum
  | .equal t₁ t₂ =>
    if h₁₂ : t₁ = t₂ then ⊤
    else if h₁ : t₁ = &k then (r.castLE (is_le k)).eq (t₂.lowerAt (Ne.symm (h₁ ▸ h₁₂)))
    else if h₂ : t₂ = &k then (r.castLE (is_le k)).eq (t₁.lowerAt (h₂ ▸ h₁₂))
    else t₁.lowerAt h₁ =₀ t₂.lowerAt h₂
  | .mem t₁ t₂ =>
    if h₁ : t₁ = &k then
      if h₁₂ : t₂ = t₁ then (r.castLE (is_le k)).memSelf
      else (r.castLE (is_le k)).mem (t₂.lowerAt (h₁ ▸ h₁₂))
    else
      if h₂ : t₂ = &k then (r.castLE (is_le k)).hasMem (t₁.lowerAt h₁)
      else (t₁.lowerAt h₁) ∈₀ (t₂.lowerAt h₂)
  | .imp φ₁ φ₂ => r.substLowerAt φ₁ ⟹ r.substLowerAt φ₂
  | .allMem t ψ =>
    if h : t ≠ &k then .allMem (t.lowerAt h) (r.substLowerAt (k := k.castSucc) ψ)
    else (r.castLE (is_le k)).allMem (r.substLowerAt (k := k.castSucc) ψ)
  | .rel _ _ => ⊥
  termination_by (r.depth, 4, sizeOf φ)
  decreasing_by all_goals simp [castLE, Prod.lex_def, Nat.lt_add_right]
end

mutual
theorem relFree_hasMem {n : ℕ} (r : L.RudimentaryTerm n) [hr : r.CharFree] (t : L.Term' n) :
    (r.hasMem t).RelFree :=
  match r, hr with
  | .var i, _ => by simp only [hasMem]; infer_instance
  | .const c, _ => by simp only [hasMem]; infer_instance
  | .unorderedPair r₁ r₂, hr => by
    have := CharFree.of_unorderedPair_left r₁ r₂
    have := CharFree.of_unorderedPair_right r₁ r₂
    have := relFree_eq r₁ t
    have := relFree_eq r₂ t
    simp only [hasMem]; infer_instance
  | .sdiff r₁ r₂, hr => by
    have := CharFree.of_sdiff_left r₁ r₂
    have := CharFree.of_sdiff_right r₁ r₂
    have := relFree_hasMem r₁ t
    have := relFree_hasMem r₂ t
    simp only [hasMem]; infer_instance
  | .iUnion ri rf, hr => by
    have := CharFree.of_iUnion_index ri rf
    have := CharFree.of_iUnion_function ri rf
    have := relFree_hasMem rf t.castSucc
    have := relFree_exMem ri (rf.hasMem t.castSucc)
    simp only [hasMem]; infer_instance
  | .char _ _, hr => by simp at hr
  termination_by (r.depth, 1, 0)
  decreasing_by all_goals simp [depth, Prod.lex_def]

theorem relFree_eq {n : ℕ} (r : L.RudimentaryTerm n) [hr : r.CharFree] (t : L.Term' n) :
    (r.eq t).RelFree :=
  match r, hr with
  | .var i, _ => by simp only [eq]; infer_instance
  | .const c, _ => by simp only [eq]; infer_instance
  | .unorderedPair r₁ r₂, hr => by
    have := CharFree.of_unorderedPair_left r₁ r₂
    have := CharFree.of_unorderedPair_right r₁ r₂
    have := relFree_mem r₁ t
    have := relFree_mem r₂ t
    have := relFree_eq r₁.castSucc &-1
    have := relFree_eq r₂.castSucc &-1
    simp only [eq]; infer_instance
  | .sdiff r₁ r₂, hr => by
    have := CharFree.of_sdiff_left r₁ r₂
    have := CharFree.of_sdiff_right r₁ r₂
    have := relFree_hasMem r₁.castSucc &-1
    have := relFree_hasMem r₂.castSucc &-1
    have := relFree_allMem r₁ (r₂.castSucc.hasMem &-1 ⊔ &-1 ∈₀ t.castSucc)
    simp only [eq]; infer_instance
  | .iUnion ri rf, hr => by
    have := CharFree.of_iUnion_index ri rf
    have := CharFree.of_iUnion_function ri rf
    have := relFree_hasMem (rf.substBoundBound (snoc (Fin.castAdd 2) (last _))) &-2
    have := relFree_exMem ri.castSucc
      ((rf.substBoundBound (snoc (Fin.castAdd 2) (last _))).hasMem &-2)
    have := relFree_allMem rf (&-1 ∈₀ (t.castAdd 2))
    have := relFree_allMem ri (rf.allMem (&-1 ∈₀ (t.castAdd 2)))
    simp only [eq]; infer_instance
  | .char _ _, hr => by simp at hr
  termination_by (r.depth, 1, 0)
  decreasing_by all_goals simp [depth, castSucc, castAdd, castLE, Prod.lex_def]

theorem relFree_mem {n : ℕ} (r : L.RudimentaryTerm n) [r.CharFree] (t : L.Term' n) :
    (r.mem t).RelFree := by
  have := relFree_eq r.castSucc &-1
  simp only [mem]; infer_instance
  termination_by (r.depth, 2, 0)
  decreasing_by simp [castSucc, castAdd, castLE, Prod.lex_def]

theorem relFree_memSelf {n : ℕ} (r : L.RudimentaryTerm n) [r.CharFree] :
    r.memSelf.RelFree := by
  have := relFree_eq r.castSucc &-1
  have := relFree_exMem r (r.castSucc.eq &-1)
  simp only [memSelf]; infer_instance
  termination_by (r.depth, 3, 0)
  decreasing_by all_goals simp [castSucc, castAdd, castLE, Prod.lex_def]

theorem relFree_allMem {n : ℕ} (r : L.RudimentaryTerm n) [hr : r.CharFree]
    (φ : L.DeltaZeroBoundedFormula (n + 1)) [φ.RelFree] :
    (r.allMem φ).RelFree :=
  match r, hr with
  | .var i, _ => by simp only [allMem]; infer_instance
  | .const c, _ => by simp only [allMem]; infer_instance
  | .unorderedPair r₁ r₂, hr => by
    have := CharFree.of_unorderedPair_left r₁ r₂
    have := CharFree.of_unorderedPair_right r₁ r₂
    have := relFree_substLowerAt (k := last _) r₁ φ
    have := relFree_substLowerAt (k := last _) r₂ φ
    simp only [allMem]; infer_instance
  | .sdiff r₁ r₂, hr => by
    have := CharFree.of_sdiff_left r₁ r₂
    have := CharFree.of_sdiff_right r₁ r₂
    have := relFree_hasMem r₂.castSucc &-1
    have := relFree_allMem r₁ (r₂.castSucc.hasMem &-1 ⊔ φ)
    simp only [allMem]; infer_instance
  | .iUnion ri rf, hr => by
    have := CharFree.of_iUnion_index ri rf
    have := CharFree.of_iUnion_function ri rf
    have := relFree_allMem rf (φ.substBoundBound (snoc (Fin.castAdd 2) (last _)))
    have := relFree_allMem ri (rf.allMem (φ.substBoundBound (snoc (Fin.castAdd 2) (last _))))
    simp only [allMem]; infer_instance
  | .char _ _, hr => by simp at hr
  termination_by (r.depth, 1, 0)
  decreasing_by all_goals simp [castSucc, castAdd, castLE, depth, Prod.lex_def]

theorem relFree_exMem {n : ℕ} (r : L.RudimentaryTerm n) [r.CharFree]
    (φ : L.DeltaZeroBoundedFormula (n + 1)) [φ.RelFree] :
    (r.exMem φ).RelFree := by
  have := relFree_allMem r (∼φ)
  simp only [exMem]; infer_instance
  termination_by (r.depth, 2, 0)
  decreasing_by all_goals simp [Prod.lex_def]

theorem relFree_substLowerAt {n : ℕ} {k : Fin (n + 1)}
    (r : L.RudimentaryTerm k.val) [r.CharFree]
    (φ : L.DeltaZeroBoundedFormula (n + 1)) [hφ : φ.RelFree] :
    (r.substLowerAt φ).RelFree :=
  match φ, hφ with
  | .falsum, _ => by simp only [substLowerAt]; infer_instance
  | .equal t₁ t₂, _ => by
    simp only [substLowerAt, Function.comp_apply]
    split_ifs with h₁₂ h₁ h₂
    · infer_instance
    · exact relFree_eq (r.castLE (is_le k)) _
    · exact relFree_eq (r.castLE (is_le k)) _
    · infer_instance
  | .mem t₁ t₂, _ => by
    simp only [substLowerAt, Function.comp_apply]
    split_ifs with h₁ h₁₂ h₂
    · exact relFree_memSelf (r.castLE (is_le k))
    · exact relFree_mem (r.castLE (is_le k)) _
    · exact relFree_hasMem (r.castLE (is_le k)) _
    · infer_instance
  | .imp φ₁ φ₂, hφ => by
    have := DeltaZeroBoundedFormula.RelFree.of_imp_left φ₁ φ₂
    have := DeltaZeroBoundedFormula.RelFree.of_imp_right φ₁ φ₂
    have := relFree_substLowerAt r φ₁
    have := relFree_substLowerAt r φ₂
    simp only [substLowerAt]; infer_instance
  | .allMem t ψ, hφ => by
    have := DeltaZeroBoundedFormula.RelFree.of_allMem t ψ
    have := relFree_substLowerAt (k := k.castSucc) r ψ
    simp only [substLowerAt, Function.comp_apply, ne_eq, dite_not]
    split_ifs with h
    · exact relFree_allMem (r.castLE (is_le k)) _
    · infer_instance
  | .rel _ _, hφ => by simp at hφ
  termination_by (r.depth, 4, sizeOf φ)
  decreasing_by all_goals simp [castLE, Prod.lex_def, Nat.lt_add_right]
end

attribute [instance] relFree_hasMem relFree_eq relFree_mem relFree_memSelf relFree_allMem
  relFree_exMem relFree_substLowerAt

notation "∀ᵣ∈ " x:arg y:50 => FirstOrder.Language.RudimentaryTerm.allMem x y

notation "∃ᵣ∈ " x:arg y:50 => FirstOrder.Language.RudimentaryTerm.exMem x y

end RudimentaryTerm

namespace Term

open RudimentaryTerm
-- open L.DeltaZeroBoundedFormula
variable [L.ExtraConstantsUnaryRelationsOnly]

noncomputable def substBoundRud (t : L.Term' n)
  (rs : Fin n → L.RudimentaryTerm m) :
  L.RudimentaryTerm m :=
  match t with
  | .var (Sum.inr i) => rs i
  | .func F _ (l := 0) => const F
  | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F

instance (t : L.Term' n) (rs : Fin n → L.RudimentaryTerm m)
  [hrs : ∀ i, (rs i).CharFree] :
  (t.substBoundRud rs).CharFree := match t with
  | .var (Sum.inr i) => by simp only [substBoundRud]; infer_instance
  | .func F _ (l := 0) => by simp only [substBoundRud]; infer_instance
  | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F

noncomputable def toRudimentaryTerm {n} (t : L.Term' n) :
  L.RudimentaryTerm n :=
  match t with
  | .var (Sum.inr i) => ᵣi
  | .func F _ (l := 0) => const F
  | .func F _ (l := n + 1) => IsEmpty.elim (by infer_instance) F

instance {n} (t : L.Term' n) :
  t.toRudimentaryTerm.CharFree := match t with
  | .var (Sum.inr i) => by simp only [toRudimentaryTerm]; infer_instance
  | .func F _ (l := 0) => by simp only [toRudimentaryTerm]; infer_instance
  | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F

end Term

namespace DeltaZeroBoundedFormula

open RudimentaryTerm

variable [L.ExtraConstantsUnaryRelationsOnly]

noncomputable def substBoundRud (φ : L.DeltaZeroBoundedFormula n)
  (rs : Fin n → L.RudimentaryTerm m) :
  L.DeltaZeroBoundedFormula m :=
  match φ with
  | .falsum => .falsum
  | .equal t₁ t₂ =>
    (∀ᵣ∈ (t₁.substBoundRud rs) ((t₂.substBoundRud rs).castSucc.hasMem &-1)) ⊓
      ∀ᵣ∈ (t₂.substBoundRud rs) ((t₁.substBoundRud rs).castSucc.hasMem &-1)
  | .mem t₁ t₂ =>
    ∃ᵣ∈ (t₂.substBoundRud rs) ((t₁.substBoundRud rs).castSucc.eq &-1)
  | .imp φ₁ φ₂ => (φ₁.substBoundRud rs) ⟹ (φ₂.substBoundRud rs)
  | .allMem t ψ =>
    ∀ᵣ∈ (t.substBoundRud rs) (ψ.substBoundRud (snoc (castSucc ∘ rs) (ᵣ-1)))
  | .rel _ _ => ⊥

instance (φ : L.DeltaZeroBoundedFormula n)
  [hφ : φ.RelFree]
  (rs : Fin n → L.RudimentaryTerm m)
  [hrs : ∀ i, (rs i).CharFree] :
  (φ.substBoundRud rs).RelFree := by
  induction hφ using relFreeCases generalizing m with
  | falsum => simp only [substBoundRud]; infer_instance
  | equal t₁ t₂ => simp only [substBoundRud]; infer_instance
  | mem t₁ t₂ => simp only [substBoundRud]; infer_instance
  | imp φ₁ φ₂ _ _ _ ih₁ ih₂ =>
    have := ih₁ rs
    have := ih₂ rs
    simp only [substBoundRud]; infer_instance
  | allMem t ψ _ _ ih =>
    have := ih (snoc (castSucc ∘ rs) (ᵣ-1))
    simp only [substBoundRud]; infer_instance

end DeltaZeroBoundedFormula

end Language

end FirstOrder
