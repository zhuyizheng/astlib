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

def charDepth (r : L.RudimentaryTerm n) : ℕ := match r with
  | var _ => 0
  | const _ => 0
  | unorderedPair r₁ r₂ => max r₁.charDepth r₂.charDepth
  | sdiff r₁ r₂ => max r₁.charDepth r₂.charDepth
  | iUnion ri rf => max ri.charDepth rf.charDepth
  | char _ r => r.charDepth + 1

def IsCharFree (r : L.RudimentaryTerm n) : Prop := r.charDepth = 0

@[simp]
theorem isCharFree_var (i : Fin n) : IsCharFree (ᵣi : L.RudimentaryTerm n) := by
  simp [IsCharFree, charDepth]

@[simp]
theorem isCharFree_const (c : L.Constants) : IsCharFree (const c : L.RudimentaryTerm n) := by
  simp [IsCharFree, charDepth]

@[simp]
theorem isCharFree_unorderedPair (r₁ r₂ : L.RudimentaryTerm n) :
    IsCharFree (unorderedPair r₁ r₂) ↔ IsCharFree r₁ ∧ IsCharFree r₂ := by
  simp [IsCharFree, charDepth]

@[simp]
theorem isCharFree_sdiff (r₁ r₂ : L.RudimentaryTerm n) :
    IsCharFree (sdiff r₁ r₂) ↔ IsCharFree r₁ ∧ IsCharFree r₂ := by
  simp [IsCharFree, charDepth]

@[simp]
theorem isCharFree_iUnion (ri : L.RudimentaryTerm n) (rf : L.RudimentaryTerm (n + 1)) :
    IsCharFree (iUnion ri rf) ↔ IsCharFree ri ∧ IsCharFree rf := by
  simp [IsCharFree, charDepth]

@[simp, grind .]
theorem not_isCharFree_char (R : L.Relations 1) (r : L.RudimentaryTerm n) :
    ¬IsCharFree (char R r) := by
  simp [IsCharFree, charDepth]

@[elab_as_elim] def isCharFreeCases
  {motive : ∀ {n}, ∀ {r : L.RudimentaryTerm n}, r.IsCharFree → Sort _}
  (var : ∀ {n}, ∀ i : Fin n, ∀ h : (ᵣi : L.RudimentaryTerm n).IsCharFree, motive h)
  (const : ∀ {n}, ∀ c : L.Constants, ∀ h : (const c : L.RudimentaryTerm n).IsCharFree, motive h)
  (unorderedPair : ∀ {n}, ∀ r₁ r₂ : L.RudimentaryTerm n, ∀ hr₁ : r₁.IsCharFree, ∀ hr₂ : r₂.IsCharFree,
    ∀ hr : (unorderedPair r₁ r₂).IsCharFree,
    motive hr₁ → motive hr₂ → motive hr)
  (sdiff : ∀ {n}, ∀ r₁ r₂ : L.RudimentaryTerm n, ∀ hr₁ : r₁.IsCharFree, ∀ hr₂ : r₂.IsCharFree,
    ∀ hr : (sdiff r₁ r₂).IsCharFree,
    motive hr₁ → motive hr₂ → motive hr)
  (iUnion : ∀ {n}, ∀ ri : L.RudimentaryTerm n, ∀ rf : L.RudimentaryTerm (n + 1),
    ∀ hri : ri.IsCharFree, ∀ hrf : rf.IsCharFree,
    ∀ hr : (iUnion ri rf).IsCharFree,
    motive hri → motive hrf → motive hr)
  {n} {r : L.RudimentaryTerm n} (hr : r.IsCharFree) :
  motive hr := by
  cases r with
  | var i => exact var _ hr
  | const i => exact const _ hr
  | unorderedPair r₁ r₂ =>
    rw [isCharFree_unorderedPair] at hr
    exact unorderedPair _ _ hr.left hr.right _ (isCharFreeCases var const unorderedPair sdiff iUnion hr.left)
      (isCharFreeCases var const unorderedPair sdiff iUnion hr.right)
  | sdiff r₁ r₂ =>
    rw [isCharFree_sdiff] at hr
    exact sdiff _ _ hr.left hr.right _ (isCharFreeCases var const unorderedPair sdiff iUnion hr.left)
      (isCharFreeCases var const unorderedPair sdiff iUnion hr.right)
  | iUnion ri rf =>
    rw [isCharFree_iUnion] at hr
    exact iUnion _ _ hr.left hr.right _ (isCharFreeCases var const unorderedPair sdiff iUnion hr.left)
      (isCharFreeCases var const unorderedPair sdiff iUnion hr.right)
  | char R r =>
    simp [IsCharFree, charDepth] at hr

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
theorem charDepth_substBoundBound {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n)
    (f : Fin n → Fin m) :
    (r.substBoundBound f).charDepth = r.charDepth := by
  induction r generalizing m with
  | var _ => simp [charDepth, substBoundBound]
  | unorderedPair r₁ r₂ ih₁ ih₂ => simp [charDepth, substBoundBound, ih₁, ih₂]
  | sdiff r₁ r₂ ih₁ ih₂ => simp [charDepth, substBoundBound, ih₁, ih₂]
  | iUnion ri rf ihi ihf => simp [charDepth, substBoundBound, ihi, ihf]
  | const c => simp [charDepth, substBoundBound]
  | char R r ih => simp [charDepth, substBoundBound, ih]

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

@[simp]
theorem isCharFree_substBoundBound {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n)
    (f : Fin n → Fin m) :
    (r.substBoundBound f).IsCharFree ↔ r.IsCharFree := by
  simp [IsCharFree]

@[simp]
theorem isCharFree_castLE {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n)
    (h : n ≤ m) :
    (r.castLE h).IsCharFree ↔ r.IsCharFree :=
  isCharFree_substBoundBound _ _

@[simp]
theorem isCharFree_castAdd {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n) :
    (r.castAdd m).IsCharFree ↔ r.IsCharFree :=
  isCharFree_substBoundBound _ _

@[simp]
theorem isCharFree_castSucc {L : Language} [L.HasMem] {n : ℕ} (r : L.RudimentaryTerm n) :
    (r.castSucc).IsCharFree ↔ r.IsCharFree :=
  isCharFree_substBoundBound _ _

@[simp]
theorem isCharFree_substBoundRud {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n)
    (hr : r.IsCharFree)
    (rs : Fin n → L.RudimentaryTerm m) (hrs : ∀ i, (rs i).IsCharFree) :
    (r.substBoundRud rs).IsCharFree := by
  induction r generalizing m with
  | var => simp [substBoundRud, hrs]
  | unorderedPair =>
    simp only [isCharFree_unorderedPair] at hr
    simp [substBoundRud, *]
  | sdiff =>
    simp only [isCharFree_sdiff] at hr
    simp [substBoundRud, *]
  | iUnion ri rf ihi ihf =>
    simp only [isCharFree_iUnion] at hr
    simp only [substBoundRud, isCharFree_iUnion, hr, hrs, implies_true, ihi, true_and]
    apply ihf hr.right
    intro i; cases i using lastCases <;> simp [hrs]
  | const c => simp [substBoundRud]
  | char R r => simp at hr

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
@[simp]
theorem isRelFree_hasMem {n : ℕ} (r : L.RudimentaryTerm n) (hr : r.IsCharFree) (t : L.Term' n) :
    (r.hasMem t).IsRelFree :=
  match r with
  | .var i => by simp [hasMem]
  | .const c => by simp [hasMem]
  | .unorderedPair r₁ r₂ => by
    simp only [isCharFree_unorderedPair] at hr
    simp [hasMem, hr, r₁.isRelFree_eq, r₂.isRelFree_eq]
  | .sdiff r₁ r₂ => by
    simp only [isCharFree_sdiff] at hr
    simp [hasMem, hr, r₁.isRelFree_hasMem, r₂.isRelFree_hasMem]
  | .iUnion ri rf => by
    simp only [isCharFree_iUnion] at hr
    simp [hasMem, hr, ri.isRelFree_exMem, rf.isRelFree_hasMem]
  | .char _ _ => by simp at hr
  termination_by (r.depth, 1, 0)
  decreasing_by all_goals simp [depth, Prod.lex_def]

@[simp]
theorem isRelFree_eq {n : ℕ} (r : L.RudimentaryTerm n) (hr : r.IsCharFree) (t : L.Term' n) :
    (r.eq t).IsRelFree :=
  match r with
  | .var i => by simp [eq]
  | .const c => by simp [eq]
  | .unorderedPair r₁ r₂ => by
    simp only [isCharFree_unorderedPair] at hr
    simp [eq, hr, r₁.isRelFree_mem, r₂.isRelFree_mem, r₁.castSucc.isRelFree_eq, r₂.castSucc.isRelFree_eq]
  | .sdiff r₁ r₂ => by
    simp only [isCharFree_sdiff] at hr
    simp [eq, hr, r₁.castSucc.isRelFree_hasMem, r₂.castSucc.isRelFree_hasMem, r₁.isRelFree_allMem]
  | .iUnion ri rf => by
    simp only [isCharFree_iUnion] at hr
    simp [eq, hr, ri.castSucc.isRelFree_exMem, ri.isRelFree_allMem,
      (rf.substBoundBound (snoc (Fin.castAdd 2) (last _))).isRelFree_hasMem, rf.isRelFree_allMem]
  | .char _ _ => by simp at hr
  termination_by (r.depth, 1, 0)
  decreasing_by all_goals simp [depth, castSucc, castAdd, castLE, Prod.lex_def]

@[simp]
theorem isRelFree_mem {n : ℕ} (r : L.RudimentaryTerm n) (hr : r.IsCharFree) (t : L.Term' n) :
    (r.mem t).IsRelFree := by
  simp [mem, hr, r.castSucc.isRelFree_eq]
  termination_by (r.depth, 2, 0)
  decreasing_by simp [castSucc, castAdd, castLE, Prod.lex_def]

@[simp]
theorem isRelFree_memSelf {n : ℕ} (r : L.RudimentaryTerm n) (hr : r.IsCharFree) :
    r.memSelf.IsRelFree := by
  simp [memSelf, hr, r.isRelFree_exMem, r.castSucc.isRelFree_eq]
  termination_by (r.depth, 3, 0)
  decreasing_by all_goals simp [castSucc, castAdd, castLE, Prod.lex_def]

@[simp]
theorem isRelFree_allMem {n : ℕ} (r : L.RudimentaryTerm n) (hr : r.IsCharFree)
    (φ : L.DeltaZeroBoundedFormula (n + 1)) (hφ : φ.IsRelFree) :
    (r.allMem φ).IsRelFree :=
  match r with
  | .var i => by simp [allMem, hφ]
  | .const c => by simp [allMem, hφ]
  | .unorderedPair r₁ r₂ => by
    simp only [isCharFree_unorderedPair] at hr
    simp [allMem, hφ, hr, r₁.isRelFree_substLowerAt (k := last _), r₂.isRelFree_substLowerAt (k := last _)]
  | .sdiff r₁ r₂ => by
    simp only [isCharFree_sdiff] at hr
    simp [allMem, hφ, hr, r₁.isRelFree_allMem, r₂.castSucc.isRelFree_hasMem]
  | .iUnion ri rf => by
    simp only [isCharFree_iUnion] at hr
    simp [allMem, hφ, hr, ri.isRelFree_allMem, rf.isRelFree_allMem]
  | .char _ _ => by simp at hr
  termination_by (r.depth, 1, 0)
  decreasing_by all_goals simp [castSucc, castAdd, castLE, depth, Prod.lex_def]

@[simp]
theorem isRelFree_exMem {n : ℕ} (r : L.RudimentaryTerm n) (hr : r.IsCharFree)
    (φ : L.DeltaZeroBoundedFormula (n + 1)) (hφ : φ.IsRelFree) :
    (r.exMem φ).IsRelFree := by
  simp [exMem, hr, hφ, r.isRelFree_allMem]
  termination_by (r.depth, 2, 0)
  decreasing_by all_goals simp [Prod.lex_def]

@[simp]
theorem isRelFree_substLowerAt {n : ℕ} {k : Fin (n + 1)}
  (r : L.RudimentaryTerm k.val) (hr : r.IsCharFree)
    (φ : L.DeltaZeroBoundedFormula (n + 1)) (hφ : φ.IsRelFree) :
    (r.substLowerAt φ).IsRelFree :=
  match φ with
  | .falsum => by simp [substLowerAt]
  | .equal t₁ t₂ => by
    simp only [substLowerAt, Function.comp_apply]
    split_ifs with h₁₂ h₁ h₂
    · simp
    · simp [hr, (r.castLE (is_le k)).isRelFree_eq]
    · simp [hr, (r.castLE (is_le k)).isRelFree_eq]
    · simp
  | .mem t₁ t₂ => by
    simp only [substLowerAt, Function.comp_apply]
    split_ifs with h₁ h₁₂ h₂
    · simp [hr, (r.castLE (is_le k)).isRelFree_memSelf]
    · simp [hr, (r.castLE (is_le k)).isRelFree_mem]
    · simp [hr, (r.castLE (is_le k)).isRelFree_hasMem]
    · simp
  | .imp φ₁ φ₂ => by
    simp only [DeltaZeroBoundedFormula.isRelFree_imp] at hφ
    simp [substLowerAt, hφ, r.isRelFree_substLowerAt hr φ₁, r.isRelFree_substLowerAt hr φ₂]
  | .allMem t ψ => by
    simp only [substLowerAt, Function.comp_apply, ne_eq, dite_not]
    simp only [DeltaZeroBoundedFormula.isRelFree_allMem] at hφ
    split_ifs with h
    · simp [hr, hφ, r.isRelFree_substLowerAt (k := k.castSucc) hr ψ,
        (r.castLE (is_le k)).isRelFree_allMem]
    · simp [hφ, r.isRelFree_substLowerAt (k := k.castSucc) hr ψ]
  | .rel _ _ => by simp at hφ
  termination_by (r.depth, 4, sizeOf φ)
  decreasing_by all_goals simp [castLE, Prod.lex_def, Nat.lt_add_right]
end

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

@[simp]
theorem isCharFree_substBoundRud (t : L.Term' n) (rs : Fin n → L.RudimentaryTerm m)
    (hrs : ∀ i, (rs i).IsCharFree) :
    (t.substBoundRud rs).IsCharFree := match t with
  | .var (Sum.inr i) => by simp [substBoundRud, hrs]
  | .func F _ (l := 0) => by simp [substBoundRud]
  | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F

noncomputable def toRudimentaryTerm {n} (t : L.Term' n) :
  L.RudimentaryTerm n :=
  match t with
  | .var (Sum.inr i) => ᵣi
  | .func F _ (l := 0) => const F
  | .func F _ (l := n + 1) => IsEmpty.elim (by infer_instance) F

@[simp]
theorem isCharFree_toRudimentaryTerm {n} (t : L.Term' n) :
    t.toRudimentaryTerm.IsCharFree := match t with
  | .var (Sum.inr i) => by simp [toRudimentaryTerm]
  | .func F _ (l := 0) => by simp [toRudimentaryTerm]
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

@[simp]
theorem isRelFree_substBoundRud {φ : L.DeltaZeroBoundedFormula n}
    (hφ : φ.IsRelFree)
    (rs : Fin n → L.RudimentaryTerm m)
    (hrs : ∀ i, (rs i).IsCharFree) :
    (φ.substBoundRud rs).IsRelFree := by
  induction φ generalizing m with
  | falsum => simp [substBoundRud]
  | equal t₁ t₂ =>
    simp only [substBoundRud, Function.comp_apply, isRelFree_inf]
    constructor <;> apply RudimentaryTerm.isRelFree_allMem <;> simp [hrs]
  | mem t₁ t₂ =>
    simp only [substBoundRud, Function.comp_apply]
    apply RudimentaryTerm.isRelFree_exMem <;> simp [hrs]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [isRelFree_imp] at hφ
    simp [substBoundRud, hφ, hrs, ih₁, ih₂]
  | allMem t ψ ih =>
    simp only [isRelFree_allMem] at hφ
    apply RudimentaryTerm.isRelFree_allMem
    · simp [hrs]
    apply ih hφ
    intro i
    cases i using lastCases <;> simp [hrs]
  | rel _ _ => simp [substBoundRud]

end DeltaZeroBoundedFormula

end Language

end FirstOrder
