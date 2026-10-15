/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Rudimentary.Syntax
import Astlib.Basic.Axiom.KP.SigmaOneBoundedFormula.Syntax
import Astlib.Basic.SetOperation.Function
import Astlib.Basic.Ordinal.Transitive
/-!
file docstring
-/
open FirstOrder Language BoundedFormula Fin Term BoundedFormula


namespace FirstOrder.Language

variable {L : FirstOrder.Language.{u, v}} [L.HasMem]
--  [L.ExtraConstantsUnaryRelationsOnly]
  -- [L.ExtraConstantsOnly]

inductive PrimitiveRecursiveTerm [L.HasMem] : ℕ → Type max u v
  | var : Fin n → PrimitiveRecursiveTerm n
  | const (c : L.Constants) : PrimitiveRecursiveTerm n
  | unorderedPair (r₁ r₂ : PrimitiveRecursiveTerm n) : PrimitiveRecursiveTerm n
  | sdiff (r₁ r₂ : PrimitiveRecursiveTerm n) : PrimitiveRecursiveTerm n
  | iUnion (ri : PrimitiveRecursiveTerm n) (rf : PrimitiveRecursiveTerm (n + 1)) :
    PrimitiveRecursiveTerm n
  | char (R : L.Relations 1) (r : PrimitiveRecursiveTerm n) : PrimitiveRecursiveTerm n
  | recursion (rg : PrimitiveRecursiveTerm (n + 1)) : PrimitiveRecursiveTerm (n + 1)

@[inherit_doc] scoped[FirstOrder] prefix:110 "ₚᵣ" => FirstOrder.Language.PrimitiveRecursiveTerm.var

/-- The largest index of the bounded variables -/
scoped[FirstOrder] notation "ₚᵣ-1" => ₚᵣ(last _)

/-- The second largest index of the bounded variables -/
scoped[FirstOrder] notation "ₚᵣ-2" => ₚᵣ(castAdd 1 (last _))

/-- The third largest index of the bounded variables -/
scoped[FirstOrder] notation "ₚᵣ-3" => ₚᵣ(castAdd 2 (last _))

/-- The fourth largest index of the bounded variables -/
scoped[FirstOrder] notation "ₚᵣ-4" => ₚᵣ(castAdd 3 (last _))

@[inherit_doc] scoped[FirstOrder] notation:max "ₚᵣ{" x ", " y "}" =>
  FirstOrder.Language.PrimitiveRecursiveTerm.unorderedPair x y


  -- reverseInduction last (fun i _ => cast i) i
namespace PrimitiveRecursiveTerm


-- def depth (r : L.RudimentaryTerm n) : ℕ := match r with
--   | var _ => 0
--   | const _ => 0
--   | unorderedPair r₁ r₂ => (max r₁.depth r₂.depth) + 1
--   | sdiff r₁ r₂ => (max r₁.depth r₂.depth) + 1
--   | iUnion ri rf => (max ri.depth rf.depth) + 1
--   | char _ r => r.depth + 1

-- def charDepth (r : L.RudimentaryTerm n) : ℕ := match r with
--   | var _ => 0
--   | const _ => 0
--   | unorderedPair r₁ r₂ => max r₁.charDepth r₂.charDepth
--   | sdiff r₁ r₂ => max r₁.charDepth r₂.charDepth
--   | iUnion ri rf => max ri.charDepth rf.charDepth
--   | char _ r => r.charDepth + 1

-- def IsCharFree (r : L.RudimentaryTerm n) : Prop := r.charDepth = 0

-- @[simp]
-- theorem isCharFree_var (i : Fin n) : IsCharFree (ᵣi : L.RudimentaryTerm n) := by
--   simp [IsCharFree, charDepth]

-- @[simp]
-- theorem isCharFree_const (c : L.Constants) : IsCharFree (const c : L.RudimentaryTerm n) := by
--   simp [IsCharFree, charDepth]

-- @[simp]
-- theorem isCharFree_unorderedPair (r₁ r₂ : L.RudimentaryTerm n) :
--     IsCharFree (unorderedPair r₁ r₂) ↔ IsCharFree r₁ ∧ IsCharFree r₂ := by
--   simp [IsCharFree, charDepth]

-- @[simp]
-- theorem isCharFree_sdiff (r₁ r₂ : L.RudimentaryTerm n) :
--     IsCharFree (sdiff r₁ r₂) ↔ IsCharFree r₁ ∧ IsCharFree r₂ := by
--   simp [IsCharFree, charDepth]

-- @[simp]
-- theorem isCharFree_iUnion (ri : L.RudimentaryTerm n) (rf : L.RudimentaryTerm (n + 1)) :
--     IsCharFree (iUnion ri rf) ↔ IsCharFree ri ∧ IsCharFree rf := by
--   simp [IsCharFree, charDepth]

-- @[simp, grind .]
-- theorem not_isCharFree_char (R : L.Relations 1) (r : L.RudimentaryTerm n) :
--     ¬IsCharFree (char R r) := by
--   simp [IsCharFree, charDepth]

-- @[elab_as_elim] def isCharFreeCases
--   {motive : ∀ {n}, ∀ {r : L.RudimentaryTerm n}, r.IsCharFree → Sort _}
--   (var : ∀ {n}, ∀ i : Fin n, ∀ h : (ᵣi : L.RudimentaryTerm n).IsCharFree, motive h)
--   (const : ∀ {n}, ∀ c : L.Constants, ∀ h : (const c : L.RudimentaryTerm n).IsCharFree, motive h)
--   (unorderedPair : ∀ {n}, ∀ r₁ r₂ : L.RudimentaryTerm n, ∀ hr₁ : r₁.IsCharFree, ∀ hr₂ : r₂.IsCharFree,
--     ∀ hr : (unorderedPair r₁ r₂).IsCharFree,
--     motive hr₁ → motive hr₂ → motive hr)
--   (sdiff : ∀ {n}, ∀ r₁ r₂ : L.RudimentaryTerm n, ∀ hr₁ : r₁.IsCharFree, ∀ hr₂ : r₂.IsCharFree,
--     ∀ hr : (sdiff r₁ r₂).IsCharFree,
--     motive hr₁ → motive hr₂ → motive hr)
--   (iUnion : ∀ {n}, ∀ ri : L.RudimentaryTerm n, ∀ rf : L.RudimentaryTerm (n + 1),
--     ∀ hri : ri.IsCharFree, ∀ hrf : rf.IsCharFree,
--     ∀ hr : (iUnion ri rf).IsCharFree,
--     motive hri → motive hrf → motive hr)
--   {n} {r : L.RudimentaryTerm n} (hr : r.IsCharFree) :
--   motive hr := by
--   cases r with
--   | var i => exact var _ hr
--   | const i => exact const _ hr
--   | unorderedPair r₁ r₂ =>
--     rw [isCharFree_unorderedPair] at hr
--     exact unorderedPair _ _ hr.left hr.right _ (isCharFreeCases var const unorderedPair sdiff iUnion hr.left)
--       (isCharFreeCases var const unorderedPair sdiff iUnion hr.right)
--   | sdiff r₁ r₂ =>
--     rw [isCharFree_sdiff] at hr
--     exact sdiff _ _ hr.left hr.right _ (isCharFreeCases var const unorderedPair sdiff iUnion hr.left)
--       (isCharFreeCases var const unorderedPair sdiff iUnion hr.right)
--   | iUnion ri rf =>
--     rw [isCharFree_iUnion] at hr
--     exact iUnion _ _ hr.left hr.right _ (isCharFreeCases var const unorderedPair sdiff iUnion hr.left)
--       (isCharFreeCases var const unorderedPair sdiff iUnion hr.right)
--   | char R r =>
--     simp [IsCharFree, charDepth] at hr

-- def substBoundBound {L : Language} [L.HasMem] {m n : ℕ} (r : L.PrimitiveRecursiveTerm n)
--     (f : Fin n → Fin m) :
--     L.PrimitiveRecursiveTerm m :=
--   match r with
--   | .var i => var (f i)
--   | .unorderedPair r₁ r₂ => unorderedPair (r₁.substBoundBound f) (r₂.substBoundBound f)
--   | .sdiff r₁ r₂ => sdiff (r₁.substBoundBound f) (r₂.substBoundBound f)
--   | .iUnion ri rf =>
--     iUnion (ri.substBoundBound f) (rf.substBoundBound (snoc (fun i ↦ (f i).castSucc) (last _)))
--   | char R r => char R (r.substBoundBound f)
--   | const c => const c
--   | recursion rg => recursion (rg.substBoundBound (f ∘ castSucc))

-- @[simp]
-- theorem depth_substBoundBound {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n)
--     (f : Fin n → Fin m) :
--     (r.substBoundBound f).depth = r.depth := by
--   induction r generalizing m with
--   | var _ => simp [depth, substBoundBound]
--   | unorderedPair r₁ r₂ ih₁ ih₂ => simp [depth, substBoundBound, ih₁, ih₂]
--   | sdiff r₁ r₂ ih₁ ih₂ => simp [depth, substBoundBound, ih₁, ih₂]
--   | iUnion ri rf ihi ihf => simp [depth, substBoundBound, ihi, ihf]
--   | const c => simp [depth, substBoundBound]
--   | char R r ih => simp [depth, substBoundBound, ih]

-- @[simp]
-- theorem charDepth_substBoundBound {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n)
--     (f : Fin n → Fin m) :
--     (r.substBoundBound f).charDepth = r.charDepth := by
--   induction r generalizing m with
--   | var _ => simp [charDepth, substBoundBound]
--   | unorderedPair r₁ r₂ ih₁ ih₂ => simp [charDepth, substBoundBound, ih₁, ih₂]
--   | sdiff r₁ r₂ ih₁ ih₂ => simp [charDepth, substBoundBound, ih₁, ih₂]
--   | iUnion ri rf ihi ihf => simp [charDepth, substBoundBound, ihi, ihf]
--   | const c => simp [charDepth, substBoundBound]
--   | char R r ih => simp [charDepth, substBoundBound, ih]

-- def substBoundPR {L : Language} [L.HasMem] {n : ℕ} (r : L.PrimitiveRecursiveTerm n)
--     (rs : Fin n → L.PrimitiveRecursiveTerm m) :
--     L.PrimitiveRecursiveTerm m :=
--   match r with
--   | .var i => rs i
--   | .unorderedPair r₁ r₂ => unorderedPair (r₁.substBoundPR rs) (r₂.substBoundRud rs)
--   | .sdiff r₁ r₂ => sdiff (r₁.substBoundRud rs) (r₂.substBoundRud rs)
--   | .iUnion ri rf =>
--     iUnion (ri.substBoundRud rs)
--       (rf.substBoundRud (snoc (fun i ↦ (rs i).substBoundBound castSucc) (var (last _))))
--   | .const c => const c
--   | .char R r => char R (r.substBoundRud rs)

-- def castLE {L : Language} [L.HasMem] {n m : ℕ} (r : L.RudimentaryTerm n) (h : n ≤ m) :
--     L.RudimentaryTerm m := r.substBoundBound (Fin.castLE h)

-- def castAdd {L : Language} [L.HasMem] {n : ℕ} (r : L.RudimentaryTerm n) (m : ℕ) :
--     L.RudimentaryTerm (n + m) := r.castLE (n.le_add_right m)

-- def castSucc {L : Language} [L.HasMem] {n : ℕ} (r : L.RudimentaryTerm n) :
--     L.RudimentaryTerm (n + 1) := r.castAdd 1

-- @[simp]
-- theorem isCharFree_substBoundBound {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n)
--     (f : Fin n → Fin m) :
--     (r.substBoundBound f).IsCharFree ↔ r.IsCharFree := by
--   simp [IsCharFree]

-- @[simp]
-- theorem isCharFree_castLE {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n)
--     (h : n ≤ m) :
--     (r.castLE h).IsCharFree ↔ r.IsCharFree :=
--   isCharFree_substBoundBound _ _

-- @[simp]
-- theorem isCharFree_castAdd {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n) :
--     (r.castAdd m).IsCharFree ↔ r.IsCharFree :=
--   isCharFree_substBoundBound _ _

-- @[simp]
-- theorem isCharFree_castSucc {L : Language} [L.HasMem] {n : ℕ} (r : L.RudimentaryTerm n) :
--     (r.castSucc).IsCharFree ↔ r.IsCharFree :=
--   isCharFree_substBoundBound _ _

-- @[simp]
-- theorem isCharFree_substBoundRud {L : Language} [L.HasMem] {m n : ℕ} (r : L.RudimentaryTerm n)
--     (hr : r.IsCharFree)
--     (rs : Fin n → L.RudimentaryTerm m) (hrs : ∀ i, (rs i).IsCharFree) :
--     (r.substBoundRud rs).IsCharFree := by
--   induction r generalizing m with
--   | var => simp [substBoundRud, hrs]
--   | unorderedPair =>
--     simp only [isCharFree_unorderedPair] at hr
--     simp [substBoundRud, *]
--   | sdiff =>
--     simp only [isCharFree_sdiff] at hr
--     simp [substBoundRud, *]
--   | iUnion ri rf ihi ihf =>
--     simp only [isCharFree_iUnion] at hr
--     simp only [substBoundRud, isCharFree_iUnion, hr, hrs, implies_true, ihi, true_and]
--     apply ihf hr.right
--     intro i; cases i using lastCases <;> simp [hrs]
--   | const c => simp [substBoundRud]
--   | char R r => simp at hr

-- def _root_.Fin.lowerAt (i : Fin (n + 1)) {k : Fin (n + 1)} (h : i ≠ k) : Fin n :=
--   if hi : i.val < k.val then i.castPred (ne_last_of_lt hi)
--   else i.pred (val_ne_zero_iff.mp (by omega))

-- variable [L.ExtraConstantsUnaryRelationsOnly]

end PrimitiveRecursiveTerm


namespace Term

open RudimentaryTerm
-- -- open L.DeltaZeroBoundedFormula
variable [L.ExtraConstantsUnaryRelationsOnly]

-- noncomputable def substBoundRud (t : L.Term' n)
--   (rs : Fin n → L.RudimentaryTerm m) :
--   L.RudimentaryTerm m :=
--   match t with
--   | .var (Sum.inr i) => rs i
--   | .func F _ (l := 0) => const F
--   | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F

-- @[simp]
-- theorem isCharFree_substBoundRud (t : L.Term' n) (rs : Fin n → L.RudimentaryTerm m)
--     (hrs : ∀ i, (rs i).IsCharFree) :
--     (t.substBoundRud rs).IsCharFree := match t with
--   | .var (Sum.inr i) => by simp [substBoundRud, hrs]
--   | .func F _ (l := 0) => by simp [substBoundRud]
--   | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F

noncomputable def toPrimitiveRecursiveTerm {n} (t : L.Term' n) :
  L.PrimitiveRecursiveTerm n :=
  match t with
  | .var (Sum.inr i) => ₚᵣi
  | .func F _ (l := 0) => .const F
  | .func F _ (l := n + 1) => IsEmpty.elim (by infer_instance) F

-- @[simp]
-- theorem isCharFree_toRudimentaryTerm {n} (t : L.Term' n) :
--     t.toRudimentaryTerm.IsCharFree := match t with
--   | .var (Sum.inr i) => by simp [toRudimentaryTerm]
--   | .func F _ (l := 0) => by simp [toRudimentaryTerm]
--   | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F

end Term

-- namespace DeltaZeroBoundedFormula

-- open RudimentaryTerm

-- variable [L.ExtraConstantsUnaryRelationsOnly]

-- noncomputable def substBoundRud (φ : L.DeltaZeroBoundedFormula n)
--   (rs : Fin n → L.RudimentaryTerm m) :
--   L.DeltaZeroBoundedFormula m :=
--   match φ with
--   | .falsum => .falsum
--   | .equal t₁ t₂ =>
--     (∀ᵣ∈ (t₁.substBoundRud rs) ((t₂.substBoundRud rs).castSucc.hasMem &-1)) ⊓
--       ∀ᵣ∈ (t₂.substBoundRud rs) ((t₁.substBoundRud rs).castSucc.hasMem &-1)
--   | .mem t₁ t₂ =>
--     ∃ᵣ∈ (t₂.substBoundRud rs) ((t₁.substBoundRud rs).castSucc.eq &-1)
--   | .imp φ₁ φ₂ => (φ₁.substBoundRud rs) ⟹ (φ₂.substBoundRud rs)
--   | .allMem t ψ =>
--     ∀ᵣ∈ (t.substBoundRud rs) (ψ.substBoundRud (snoc (castSucc ∘ rs) (ᵣ-1)))
--   | .rel _ _ => ⊥

-- @[simp]
-- theorem isRelFree_substBoundRud {φ : L.DeltaZeroBoundedFormula n}
--     (hφ : φ.IsRelFree)
--     (rs : Fin n → L.RudimentaryTerm m)
--     (hrs : ∀ i, (rs i).IsCharFree) :
--     (φ.substBoundRud rs).IsRelFree := by
--   induction φ generalizing m with
--   | falsum => simp [substBoundRud]
--   | equal t₁ t₂ =>
--     simp only [substBoundRud, Function.comp_apply, isRelFree_inf]
--     constructor <;> apply RudimentaryTerm.isRelFree_allMem <;> simp [hrs]
--   | mem t₁ t₂ =>
--     simp only [substBoundRud, Function.comp_apply]
--     apply RudimentaryTerm.isRelFree_exMem <;> simp [hrs]
--   | imp φ₁ φ₂ ih₁ ih₂ =>
--     simp only [isRelFree_imp] at hφ
--     simp [substBoundRud, hφ, hrs, ih₁, ih₂]
--   | allMem t ψ ih =>
--     simp only [isRelFree_allMem] at hφ
--     apply RudimentaryTerm.isRelFree_allMem
--     · simp [hrs]
--     apply ih hφ
--     intro i
--     cases i using lastCases <;> simp [hrs]
--   | rel _ _ => simp [substBoundRud]

namespace PrimitiveRecursiveTerm

variable [L.ExtraConstantsUnaryRelationsOnly]

/-- The `Σ₁` formula `t = p(ts)`, where `p` is a primitive recursive term in `n` variables,
and `t` and `ts` are terms in `m` variables.

* `iUnion ri rf`: there are `a` and a function `f` such that `a = ri(ts)`, `dom f = a`,
  `f ﹫ y = rf(ts, y)` for all `y ∈ a`, and `t = ⋃₀ ran f`.
* `recursion rg`: there is a function `f` whose domain `d` is transitive and contains the last
  entry `x` of `ts`, such that `f ﹫ y = rg(ts', f ↾ y)` for all `y ∈ d` (where `ts'` is `ts`
  without its last entry), and `t = f ﹫ x`. -/
noncomputable def eqRealize {n : ℕ} (p : L.PrimitiveRecursiveTerm n) {m : ℕ} (t : L.Term' m)
  (ts : Fin n → L.Term' m) : L.SigmaOneBoundedFormula m :=
  match p with
  | var i => (t =₀ ts i).toSigmaOneBoundedFormula
  | const c => (t =₀ c.term).toSigmaOneBoundedFormula
  | unorderedPair r₁ r₂ =>
    -- `∃ y₁ y₂, y₁ = r₁(ts) ∧ y₂ = r₂(ts) ∧ t = {y₁, y₂}`
    ∃₁ ∃₁ (
      r₁.eqRealize &-2 (fun i ↦ (ts i).castAdd 2) ⊓
      r₂.eqRealize &-1 (fun i ↦ (ts i).castAdd 2) ⊓
      ((&0 =₀ &1).substBoundRud
        ![(t.castAdd 2).toRudimentaryTerm, ᵣ{ᵣ-2, ᵣ-1}]).toSigmaOneBoundedFormula)
  | sdiff r₁ r₂ =>
    -- `∃ y₁ y₂, y₁ = r₁(ts) ∧ y₂ = r₂(ts) ∧ t = y₁ \ y₂`
    ∃₁ ∃₁ (
      r₁.eqRealize &-2 (fun i ↦ (ts i).castAdd 2) ⊓
      r₂.eqRealize &-1 (fun i ↦ (ts i).castAdd 2) ⊓
      ((&0 =₀ &1).substBoundRud
        ![(t.castAdd 2).toRudimentaryTerm, ᵣ-2 \ ᵣ-1]).toSigmaOneBoundedFormula)
  | iUnion ri rf =>
    -- `∃ a f, a = ri(ts) ∧ IsFunction f ∧ dom f = a ∧`
    -- `(∀ y ∈ a, ∃ z, z = rf(ts, y) ∧ z = f ﹫ y) ∧ t = ⋃₀ ran f`
    ∃₁ ∃₁ (
      ri.eqRealize &-2 (fun i ↦ (ts i).castAdd 2) ⊓
      ((ᵣ-1).isFunction ⊓
        (&0 =₀ &1).substBoundRud ![(ᵣ-1).dom, ᵣ-2]).toSigmaOneBoundedFormula ⊓
      (∀₁∈ &-2 ∃₁ (
        rf.eqRealize &-1 (snoc (fun i ↦ (ts i).castAdd 4) &-2) ⊓
        ((&0 =₀ &1).substBoundRud ![ᵣ-1, ᵣ-3 ﹫ ᵣ-2]).toSigmaOneBoundedFormula)) ⊓
      ((&0 =₀ &1).substBoundRud
        ![(t.castAdd 2).toRudimentaryTerm, ᵣ⋃₀ (ᵣ-1).ran]).toSigmaOneBoundedFormula)
  | char R r =>
    -- `∃ y, y = r(ts) ∧ ((R y ∧ t = {∅, ∅}) ∨ (¬R y ∧ t = ∅))`
    ∃₁ (
      r.eqRealize &-1 (fun i ↦ (ts i).castSucc) ⊓
      ((.rel R &-1 ⊓
          (&0 =₀ &1).substBoundRud ![t.castSucc.toRudimentaryTerm, ᵣ{∅, ∅}]) ⊔
        (∼(.rel R &-1) ⊓
          (&0 =₀ &1).substBoundRud ![t.castSucc.toRudimentaryTerm, ∅])).toSigmaOneBoundedFormula)
  | recursion rg =>
    -- `∃ f d, IsFunction f ∧ d = dom f ∧ Transitive d ∧ x ∈ d ∧`
    -- `(∀ y ∈ d, ∃ z w, z = rg(ts', w) ∧ z = f ﹫ y ∧ w = f ↾ y) ∧ t = f ﹫ x`
    ∃₁ ∃₁ (
      ((ᵣ-2).isFunction ⊓
        (&0 =₀ &1).substBoundRud ![ᵣ-1, (ᵣ-2).dom] ⊓
        (ᵣ-1).isTransitive ⊓
        (&0 ∈₀ &1).substBoundRud
          ![((ts (last _)).castAdd 2).toRudimentaryTerm, ᵣ-1]).toSigmaOneBoundedFormula ⊓
      (∀₁∈ &-1 ∃₁ ∃₁ (
        rg.eqRealize &-2 (snoc (fun i ↦ (ts i.castSucc).castAdd 5) &-1) ⊓
        ((&0 =₀ &1).substBoundRud ![ᵣ-2, (.var (castAdd 4 (last _))) ﹫ ᵣ-3] ⊓
          (&0 =₀ &1).substBoundRud
            ![ᵣ-1, (.var (castAdd 4 (last _))) ↾ ᵣ-3]).toSigmaOneBoundedFormula)) ⊓
      ((&0 =₀ &1).substBoundRud
        ![(t.castAdd 2).toRudimentaryTerm,
          ᵣ-2 ﹫ ((ts (last _)).castAdd 2).toRudimentaryTerm]).toSigmaOneBoundedFormula)

end PrimitiveRecursiveTerm

end Language

end FirstOrder
