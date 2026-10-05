/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Rudimentary.Semantics
import Astlib.Basic.SetOperation.SProd
/-!
file docstring
-/
open FirstOrder Language Structure BoundedFormula DeltaZeroBoundedFormula RudimentaryTerm Fin MemStructure

variable {L : Language.{u, v}} [L.HasMem]

namespace FirstOrder.Language

inductive RudimentaryBasisTerm [L.HasMem] : ℕ → Type max u v
  | var : Fin n → RudimentaryBasisTerm n
  | const (c : L.Constants) : RudimentaryBasisTerm n
  | unorderedPair (r₁ r₂ : RudimentaryBasisTerm n) : RudimentaryBasisTerm n
  | sdiff (r₁ r₂ : RudimentaryBasisTerm n) : RudimentaryBasisTerm n
  | sprod (r₁ r₂ : RudimentaryBasisTerm n) : RudimentaryBasisTerm n
  | switch (r₁ r₂ : RudimentaryBasisTerm n) : RudimentaryBasisTerm n
  | rotate (r₁ r₂ : RudimentaryBasisTerm n) : RudimentaryBasisTerm n
  | sUnion (r : RudimentaryBasisTerm n) : RudimentaryBasisTerm n
  | dom (r : RudimentaryBasisTerm n) : RudimentaryBasisTerm n
  | invMemGraph (r : RudimentaryBasisTerm n) : RudimentaryBasisTerm n
  | sliceSet (r₁ r₂ : RudimentaryBasisTerm n) : RudimentaryBasisTerm n
  | interRel (r : RudimentaryBasisTerm n) (R : L.Relations 1) : RudimentaryBasisTerm n

namespace RudimentaryBasisTerm

instance : SDiff (L.RudimentaryBasisTerm n) :=
  ⟨RudimentaryBasisTerm.sdiff⟩

def substBoundRudBasis (r : L.RudimentaryBasisTerm n) (rs : Fin n → L.RudimentaryBasisTerm m) : L.RudimentaryBasisTerm m :=
  match r with
  | var i => rs i
  | const c => const c
  | unorderedPair r₁ r₂ => unorderedPair (r₁.substBoundRudBasis rs) (r₂.substBoundRudBasis rs)
  | sdiff r₁ r₂ => sdiff (r₁.substBoundRudBasis rs) (r₂.substBoundRudBasis rs)
  | sprod r₁ r₂ => sprod (r₁.substBoundRudBasis rs) (r₂.substBoundRudBasis rs)
  | switch r₁ r₂ => switch (r₁.substBoundRudBasis rs) (r₂.substBoundRudBasis rs)
  | rotate r₁ r₂ => rotate (r₁.substBoundRudBasis rs) (r₂.substBoundRudBasis rs)
  | sUnion r => sUnion (r.substBoundRudBasis rs)
  | dom r => dom (r.substBoundRudBasis rs)
  | invMemGraph r => invMemGraph (r.substBoundRudBasis rs)
  | sliceSet r₁ r₂ => sliceSet (r₁.substBoundRudBasis rs) (r₂.substBoundRudBasis rs)
  | interRel r R => interRel (r.substBoundRudBasis rs) R

@[simp]
theorem substBoundRudBasis_substBoundRudBasis (r : L.RudimentaryBasisTerm n)
    (rs : Fin n → L.RudimentaryBasisTerm m)
    (ts : Fin m → L.RudimentaryBasisTerm l) :
    (r.substBoundRudBasis rs).substBoundRudBasis ts =
      r.substBoundRudBasis (fun i ↦ (rs i).substBoundRudBasis ts) := by
  induction r with
  | var => simp [substBoundRudBasis]
  | const => simp [substBoundRudBasis]
  | unorderedPair => simp [substBoundRudBasis, *]
  | sdiff => simp [substBoundRudBasis, *]
  | sprod => simp [substBoundRudBasis, *]
  | switch => simp [substBoundRudBasis, *]
  | rotate => simp [substBoundRudBasis, *]
  | sUnion => simp [substBoundRudBasis, *]
  | dom => simp [substBoundRudBasis, *]
  | invMemGraph => simp [substBoundRudBasis, *]
  | sliceSet => simp [substBoundRudBasis, *]
  | interRel => simp [substBoundRudBasis, *]

@[inherit_doc] prefix:110 "⋃₀ " => sUnion

instance : Union (L.RudimentaryBasisTerm n) := ⟨fun r₁ r₂ ↦ ⋃₀ (r₁.unorderedPair r₂)⟩

instance : Inter (L.RudimentaryBasisTerm n) := ⟨fun r₁ r₂ ↦ r₁ \ (r₁ \ r₂)⟩

def unionSUnion (r : L.RudimentaryBasisTerm n) := r ∪ (⋃₀ r)

instance : Singleton (L.RudimentaryBasisTerm n) (L.RudimentaryBasisTerm n) :=
  ⟨fun r ↦ r.unorderedPair r⟩

def left₀ := ⋃₀ ({var 0} : L.RudimentaryBasisTerm 1).dom

def left (r : L.RudimentaryBasisTerm n) := left₀.substBoundRudBasis ![r]

def ran₀ := ⋃₀ (var 0 : L.RudimentaryBasisTerm 1).sliceSet (var 0 : L.RudimentaryBasisTerm 1).dom

def ran (r : L.RudimentaryBasisTerm n) := ran₀.substBoundRudBasis ![r]

def right₀ := ⋃₀ ⋃₀ ({var 0} : L.RudimentaryBasisTerm 1).sliceSet ({var 0} : L.RudimentaryBasisTerm 1).dom
--
def right (r : L.RudimentaryBasisTerm n) := ⋃₀ ({r} : L.RudimentaryBasisTerm n).ran

def orderedPair (r₁ r₂ : L.RudimentaryBasisTerm n) :=
  (r₁.unorderedPair r₁).unorderedPair (r₁.unorderedPair r₂)

def tuple {n l} (rs : Fin (l + 1) → L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  match l with
  | 0 => rs 0
  | _ + 1 => (tuple (rs ∘ castSucc)).orderedPair (rs (last _))

@[simp]
theorem tuple_one (rs : Fin 1 → L.RudimentaryBasisTerm n) : tuple rs = rs 0 := by simp [tuple]

theorem tuple_succ {l n} (rs : Fin (l + 2) → L.RudimentaryBasisTerm n) :
  tuple rs = (tuple (rs ∘ castSucc)).orderedPair (rs (last _)) := by simp [tuple]

def sProd {l : ℕ} (rs : Fin (l + 1) → L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  match l with
  -- | 0 => empty
  | 0 => rs 0
  | _ + 1 => (sProd (rs ∘ castSucc)).sprod (rs (last _))


def tupleVal (r : L.RudimentaryBasisTerm n) {l : ℕ} : Fin l → L.RudimentaryBasisTerm n :=
  match l with
  | 0 => elim0
  | 1 => fun _ ↦ r
  | _ + 1 => snoc r.left.tupleVal r.right

theorem tupleVal_eq_substBoundRudBasis (r : L.RudimentaryBasisTerm n) {l : ℕ} (i : Fin l) :
    r.tupleVal i = (((var 0) : L.RudimentaryBasisTerm 1).tupleVal i).substBoundRudBasis ![r] := by
  induction l generalizing n with
  | zero => exact elim0 i
  | succ l ih =>
    rcases l with rfl | l
    · simp [tupleVal, substBoundRudBasis]
    · cases i using lastCases with
      | last =>
        simp only [tupleVal, right, ran, ran₀, isValue, snoc_last]
        rfl
      | cast i =>
        simp only [tupleVal, snoc_castSucc, isValue]
        rw [ih r.left, ih (var 0).left]
        simp only [substBoundRudBasis_substBoundRudBasis]
        congr
        ext i; fin_cases i
        simp only [left, Nat.succ_eq_add_one, Nat.reduceAdd, zero_eta, isValue,
          Matrix.cons_val_fin_one, substBoundRudBasis_substBoundRudBasis, substBoundRudBasis]
        rfl

def rotateSProd (r : L.RudimentaryBasisTerm n) {l : ℕ} (rs : Fin l → L.RudimentaryBasisTerm n) :=
  match l with
  | 0 => r
  | _ + 1 => r.rotate (sProd rs)

def iterSwitch (r : L.RudimentaryBasisTerm n) {l : ℕ} (rs : Fin l → L.RudimentaryBasisTerm n) := match l with
  | 0 => r
  | _ + 1 => (r.iterSwitch (rs ∘ castSucc)).switch (rs (last _))

/-- The set of `l + 1`-tuples where after unraveling, the first `l` elements are in `rs`
pointwise, and the `l`th element is a member of the `i`th element. -/
def lastMemFin {n} (i : Fin l) (rs : Fin l → L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  (rotateSProd (rs i).invMemGraph (rs ∘ Fin.castLE (n := i) (i.prop.le))).iterSwitch
    fun j : Fin (l - (i.val + 1)) ↦ rs (⟨i.val + 1 + j.val, by omega⟩)

/-- The set of elements `l + 1`-tuples where after unraveling, the first `l` elements are in `rs`
pointwise, and the `l`th element is a member of `c`. -/
def lastMemConst {n} (c : L.Constants) {l : ℕ} (rs : Fin l → L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  sProd (snoc rs (const c))

def symDiff (r₁ r₂ : L.RudimentaryBasisTerm n) := (r₁ \ r₂) ∪ (r₂ \ r₁)

variable [L.ExtraConstantsUnaryRelationsOnly]

mutual
/-- The set of `l + 1`-tuples where after unraveling, the first `l` elements are in `rs`
pointwise, and the `l`th element is a member of `t`. -/
def lastMemRud {n} (t : L.RudimentaryTerm l) (rs : Fin l → L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  match t with
  | .var i  => lastMemFin i rs
  | .const c => lastMemConst c rs
  | .unorderedPair t₁ t₂ => lastEqRud t₁ rs ∪ lastEqRud t₂ rs
  | .sdiff t₁ t₂ => lastMemRud t₁ rs \ lastMemRud t₂ rs
  | .iUnion ri rf =>
    match l with
    | 0 =>
      let ri_memRange := lastMemRud ri rs
      let rf_memRange := (lastMemRud rf (snoc rs ri_memRange)).ran
      let rs' : Fin 1 → L.RudimentaryBasisTerm n := (snoc rs rf_memRange)
      let rs'' : Fin 2 → L.RudimentaryBasisTerm n := snoc rs' ri_memRange
      lastMemRud (ri.castSucc) rs' ∩ memGraph ᵣ-2 (rf.substBoundBound (snoc (castAdd 2) (last _))) rs'' |>.dom
    | l + 1 =>
      let ri_memRange := (lastMemRud ri rs).ran
      let rf_memRange := (lastMemRud rf (snoc rs ri_memRange)).ran
      let rs' : Fin (l + 2) → L.RudimentaryBasisTerm n := (snoc rs rf_memRange)
      let rs'' : Fin (l + 3) → L.RudimentaryBasisTerm n := snoc rs' ri_memRange
      lastMemRud (ri.castSucc) rs' ∩ memGraph ᵣ-2 (rf.substBoundBound (snoc (castAdd 2) (last _))) rs'' |>.dom
  | .char R r =>
      match l with
      | 0 => ({lastMemRud r rs \ lastMemRud r rs} : L.RudimentaryBasisTerm n).sprod ((interRel (image r rs) R) ∩ lastEqRud r rs)
        |>.dom
      | l + 1 => sProd (snoc rs (interRel (image r rs) R)) ∩ lastEqRud r rs |>.dom.sprod
        {lastMemRud r rs \ lastMemRud r rs}
termination_by (t.depth, 0)
decreasing_by all_goals simp [RudimentaryTerm.depth, Prod.lex_def, RudimentaryTerm.castAdd, RudimentaryTerm.castLE, RudimentaryTerm.castSucc]

/-- The set of `l + 1`-tuples in `sProd rs` where after unraveling, `t₁` is equal to `t₂`. -/
def eqGraph {l} {n} (t₁ t₂ : L.RudimentaryTerm (l + 1)) (rs : Fin (l + 1) → L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  sProd rs \ ((lastMemRud t₁ rs).symDiff (lastMemRud t₂ rs)).dom
termination_by (max t₁.depth t₂.depth, 1)
decreasing_by all_goals (simp only [Prod.lex_def]; grind)

def image (t : L.RudimentaryTerm l) (rs : Fin l → L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  match l with
  | 0 => {lastMemRud t rs}
  | _ + 1 => (lastMemRud t rs).sliceSet (sProd rs)
termination_by (t.depth, 2)

def lastEqRud {n} (t : L.RudimentaryTerm l) (rs : Fin l → L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  eqGraph ᵣ-1 t.castSucc (snoc rs (image t rs))
termination_by (t.depth, 3)
decreasing_by all_goals simp [RudimentaryTerm.depth, Prod.lex_def, RudimentaryTerm.castSucc,
  RudimentaryTerm.castAdd, RudimentaryTerm.castLE]

def memGraph {n} (t₁ t₂ : L.RudimentaryTerm l) (rs : Fin l → L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  match l with
  | 0 => ({lastMemRud t₂ rs \ lastMemRud t₂ rs} : L.RudimentaryBasisTerm n).sprod (lastMemRud t₂ rs ∩ lastEqRud t₁ rs) |>.dom
  | _ + 1 => (lastMemRud t₂ rs ∩ lastEqRud t₁ rs).dom
termination_by (max t₁.depth t₂.depth, 4)
decreasing_by all_goals (simp only [Prod.lex_def]; grind)
end

end RudimentaryBasisTerm




end FirstOrder.Language
