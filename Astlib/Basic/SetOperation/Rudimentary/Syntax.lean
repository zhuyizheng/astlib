import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Astlib.Basic.SetOperation.MemStructure.Levy

open FirstOrder Language BoundedFormula Fin Term BoundedFormula


namespace FirstOrder.Language

variable {L L' : FirstOrder.Language.{u, v}} [L.HasMem] [L'.HasMem]
  [L'.ExtraConstantsOnly]

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


def RudimentaryTerm.depth (r : L.RudimentaryTerm n) : ℕ := match r with
  | var _ => 0
  | unorderedPair r₁ r₂ => (max r₁.depth r₂.depth) + 1
  | sdiff r₁ r₂ => (max r₁.depth r₂.depth) + 1
  | iUnion ri rf => (max ri.depth rf.depth) + 1
  | const _ => 0
  | char _ r => r.depth + 1


namespace RudimentaryTerm

-- open L'.DeltaZeroBoundedFormula

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

def _root_.Fin.lowerAt (i : Fin (n + 1)) {k : Fin (n + 1)} (h : i ≠ k) : Fin n :=
  if hi : i.val < k.val then i.castPred (ne_last_of_lt hi)
  else i.pred (val_ne_zero_iff.mp (by omega))

def _root_.FirstOrder.Language.Term.lowerAt [L'.ExtraConstantsUnaryRelationsOnly]
  (t : L'.Term' (n + 1)) {k : Fin (n + 1)} (h : t ≠ &k) : L'.Term' n :=
  match t with
  | .var (Sum.inr i) => .var (Sum.inr (Fin.lowerAt i
      (Ne.intro fun a ↦ h (congrArg _ (congrArg _ a)))))
  | .func F _ (l := 0) => .func F elim0
  | .func F _ (l := n + 1) => IsEmpty.elim (by infer_instance) F

noncomputable instance : DecidableEq (L.Functions n) := Classical.typeDecidableEq _

mutual
noncomputable def hasMem {n : ℕ} (r : L'.RudimentaryTerm n) (t : L'.Term' n) :
  L'.DeltaZeroBoundedFormula n :=
  match r with
  | .var i => t ∈₀ &i
  | .const c => t ∈₀ c.term
  | .unorderedPair r₁ r₂ => r₁.eq t ⊔ r₂.eq t
  | .sdiff r₁ r₂ => r₁.hasMem t ⊓ ∼(r₂.hasMem t)
  | .iUnion ri rf => ri.exMem (rf.hasMem t.castSucc)
  | .char R _ => IsEmpty.elim (by infer_instance) R
  termination_by (r.depth, 1, 0)
  decreasing_by all_goals simp [depth, Prod.lex_def]

noncomputable def eq {n : ℕ} (r : L'.RudimentaryTerm n) (t : L'.Term' n) :
  L'.DeltaZeroBoundedFormula n :=
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
  | .char R _ => IsEmpty.elim (by infer_instance) R
  termination_by (r.depth, 1, 0)
  decreasing_by all_goals simp [depth, castSucc, castAdd, castLE, Prod.lex_def]

noncomputable def mem {n : ℕ} (r : L'.RudimentaryTerm n) (t : L'.Term' n) :
  L'.DeltaZeroBoundedFormula n :=
  ∃₀∈ t (r.castSucc.eq &-1)
  termination_by (r.depth, 2, 0)
  decreasing_by simp [castSucc, castAdd, castLE, Prod.lex_def]

noncomputable def memSelf {n : ℕ} (r : L'.RudimentaryTerm n) :
  L'.DeltaZeroBoundedFormula n :=
  r.exMem (r.castSucc.eq &-1)
  termination_by (r.depth, 3, 0)
  decreasing_by all_goals simp [castSucc, castAdd, castLE, Prod.lex_def]

noncomputable def allMem {n : ℕ} (r : L'.RudimentaryTerm n)
  (φ : L'.DeltaZeroBoundedFormula (n + 1)) :
  L'.DeltaZeroBoundedFormula n :=
  match r with
  | .var i => ∀₀∈ &i φ
  | .const c => ∀₀∈ c.term φ
  | .unorderedPair r₁ r₂ =>
    r₁.substLowerAt (k := last _) φ ⊓ r₂.substLowerAt (k := last _) φ
  | .sdiff r₁ r₂ => r₁.allMem (r₂.castSucc.hasMem &-1 ⊔ φ)
  | .iUnion ri rf => ri.allMem (rf.allMem (φ.substBoundBound (snoc (Fin.castAdd 2) (last _))))
  | .char R _ => IsEmpty.elim (by infer_instance) R
  termination_by (r.depth, 1, 0)
  decreasing_by all_goals simp [castSucc, castAdd, castLE, depth, Prod.lex_def]

noncomputable def exMem {n : ℕ} (r : L'.RudimentaryTerm n)
  (φ : L'.DeltaZeroBoundedFormula (n + 1)) :
L'.DeltaZeroBoundedFormula n :=
  ∼(r.allMem (∼φ))
  termination_by (r.depth, 2, 0)
  decreasing_by all_goals simp [Prod.lex_def]

noncomputable def substLowerAt {n : ℕ} {k : Fin (n + 1)}
  (r : L'.RudimentaryTerm k.val)
  (φ : L'.DeltaZeroBoundedFormula (n + 1)) :
  L'.DeltaZeroBoundedFormula n :=
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
  | .rel R  _ => IsEmpty.elim (by infer_instance) R
  termination_by (r.depth, 4, sizeOf φ)
  decreasing_by all_goals simp [castLE, Prod.lex_def, Nat.lt_add_right]
end

notation "∀ᵣ∈ " x:arg y:50 => FirstOrder.Language.RudimentaryTerm.allMem x y

notation "∃ᵣ∈ " x:arg y:50 => FirstOrder.Language.RudimentaryTerm.exMem x y

end RudimentaryTerm

namespace LHom

open RudimentaryTerm

variable {L L' : Language} [L.HasMem] [L'.HasMem]
  (φ : L →ᴸ L') {n : ℕ}

instance : SDiff (L.RudimentaryTerm n) := ⟨sdiff⟩

-- theorem sdiff_eq_sdiff (r₁ r₂ : L.RudimentaryTerm n) : r₁.sdiff r₂ = r₁ \ r₂ := rfl

@[simp]
def onRudimentaryTerm {n : ℕ} (I : L →ᴸ L') :
  L.RudimentaryTerm n → L'.RudimentaryTerm n
  | .var i => .var i
  | .const c => .const (I.onFunction c)
  | .unorderedPair r₁ r₂ => .unorderedPair (I.onRudimentaryTerm r₁) (I.onRudimentaryTerm r₂)
  | .sdiff r₁ r₂ => (I.onRudimentaryTerm r₁) \ (I.onRudimentaryTerm r₂)
  | .iUnion ri rf => .iUnion (I.onRudimentaryTerm ri) (I.onRudimentaryTerm rf)
  | .char R r => .char (I.onRelation R) (I.onRudimentaryTerm r)

@[simp]
theorem onRudimentaryTerm_substBoundBound {n : ℕ} (I : L →ᴸ L') (r : L.RudimentaryTerm n)
    (f : Fin n → Fin m) :
    I.onRudimentaryTerm (r.substBoundBound f) = (I.onRudimentaryTerm r).substBoundBound f := by
  induction r generalizing m with
  | var i => rfl
  | const c => rfl
  | unorderedPair r₁ r₂ ih₁ ih₂ => simp [RudimentaryTerm.substBoundBound, ih₁, ih₂]
  | sdiff r₁ r₂ ih₁ ih₂ => simp [RudimentaryTerm.substBoundBound, ih₁, ih₂]; rfl
  | iUnion ri rf ihi ihf => simp [RudimentaryTerm.substBoundBound, ihi, ihf]
  | char R r ih => simp [RudimentaryTerm.substBoundBound, ih]

@[simp]
theorem onRudimentaryTerm_castLE {n : ℕ} (I : L →ᴸ L') (r : L.RudimentaryTerm n)
    (h : n ≤ n') :
    I.onRudimentaryTerm (r.castLE h) = (I.onRudimentaryTerm r).castLE h :=
  onRudimentaryTerm_substBoundBound _ _ _

@[simp]
theorem onRudimentaryTerm_castAdd {n : ℕ} (I : L →ᴸ L') (r : L.RudimentaryTerm n) (m : ℕ) :
    I.onRudimentaryTerm (r.castAdd m) = (I.onRudimentaryTerm r).castAdd m :=
  onRudimentaryTerm_substBoundBound _ _ _

@[simp]
theorem onRudimentaryTerm_castSucc {n : ℕ} (I : L →ᴸ L') (r : L.RudimentaryTerm n) :
    I.onRudimentaryTerm (r.castSucc) = (I.onRudimentaryTerm r).castSucc :=
  onRudimentaryTerm_substBoundBound _ _ _

@[simp]
theorem onRudimentaryTerm_substBoundRud {n : ℕ} (I : L →ᴸ L') (r : L.RudimentaryTerm n)
    (rs : Fin n → L.RudimentaryTerm m) :
    I.onRudimentaryTerm (r.substBoundRud rs) =
      (I.onRudimentaryTerm r).substBoundRud (I.onRudimentaryTerm ∘ rs) := by
  induction r generalizing m with
  | var i => rfl
  | const c => rfl
  | unorderedPair r₁ r₂ ih₁ ih₂ => simp [RudimentaryTerm.substBoundRud, ih₁, ih₂]
  | sdiff r₁ r₂ ih₁ ih₂ => simp [RudimentaryTerm.substBoundRud, ih₁, ih₂]; rfl
  | iUnion ri rf ihi ihf =>
    simp only [substBoundRud, onRudimentaryTerm, ihi, ihf, Function.comp_apply, iUnion.injEq,
      true_and]
    congr
    ext i; cases i using Fin.lastCases <;> simp
  | char R r ih =>
    simp [RudimentaryTerm.substBoundRud, ih]

-- def _root_.FirstOrder.Language.ofPureSTRudimentaryTerm {L : Language} [L.HasMem] {n : ℕ}
--   (r : L.toExtraConstantsOnly.RudimentaryTerm n) : L.RudimentaryTerm n :=
--   L.extraConstantsOnlyLHom.onRudimentaryTerm r

-- instance : Coe (L'.RudimentaryTerm n) (L.RudimentaryTerm n) :=
  -- ⟨L.extraConstantsOnlyLHom.onRudimentaryTerm⟩

end LHom

namespace Term

open RudimentaryTerm
-- open L'.DeltaZeroBoundedFormula

noncomputable def substBoundRud (t : L'.Term' n)
  (rs : Fin n → L'.RudimentaryTerm m) :
  L'.RudimentaryTerm m :=
  match t with
  | .var (Sum.inr i) => rs i
  | .func F _ (l := 0) => const F
  | .func F _ (l := n + 1) => IsEmpty.elim (by infer_instance) F

noncomputable def toRudimentaryTerm {n} [L.ExtraConstantsUnaryRelationsOnly] (t : L.Term' n) :
  L.RudimentaryTerm n :=
  match t with
  | .var (Sum.inr i) => ᵣi
  | .func F _ (l := 0) => const F
  | .func F _ (l := n + 1) => IsEmpty.elim (by infer_instance) F

end Term

namespace DeltaZeroBoundedFormula

open RudimentaryTerm

noncomputable def substBoundRud (φ : L'.DeltaZeroBoundedFormula n)
  (rs : Fin n → L'.RudimentaryTerm m) :
  L'.DeltaZeroBoundedFormula m :=
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
  | .rel R t => IsEmpty.elim (by infer_instance) R

end DeltaZeroBoundedFormula

end Language

end FirstOrder
