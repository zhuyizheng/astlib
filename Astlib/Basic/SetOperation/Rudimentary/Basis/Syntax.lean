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
  | memGraph (r : RudimentaryBasisTerm n) : RudimentaryBasisTerm n
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
  | memGraph r => memGraph (r.substBoundRudBasis rs)
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
  | memGraph => simp [substBoundRudBasis, *]
  | sliceSet => simp [substBoundRudBasis, *]
  | interRel => simp [substBoundRudBasis, *]

@[inherit_doc] prefix:110 "⋃₀ " => sUnion

instance : Union (L.RudimentaryBasisTerm n) := ⟨fun r₁ r₂ ↦ ⋃₀ (r₁.unorderedPair r₂)⟩

instance : Inter (L.RudimentaryBasisTerm n) := ⟨fun r₁ r₂ ↦ r₁ \ (r₁ \ r₂)⟩

def iterSUnion₀ (k : ℕ) (r : L.RudimentaryBasisTerm n) := match k with
  | 0 => r
  | k + 1 => ((var 0).iterSUnion₀ k).substBoundRudBasis ![r ∪ (⋃₀ r)]

@[simp]
theorem iterSUnion₀_zero {n} (r : L.RudimentaryBasisTerm n) :
  r.iterSUnion₀ 0 = r := by simp [iterSUnion₀]

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

instance : Singleton (L.RudimentaryBasisTerm n) (L.RudimentaryBasisTerm n) :=
  ⟨fun r ↦ r.unorderedPair r⟩

def left₀ := ⋃₀ ({var 0} : L.RudimentaryBasisTerm 1).dom

def left (r : L.RudimentaryBasisTerm n) := left₀.substBoundRudBasis ![r]

def right₀ := ⋃₀ ⋃₀ ({var 0} : L.RudimentaryBasisTerm 1).sliceSet ({var 0} : L.RudimentaryBasisTerm 1).dom

def right (r : L.RudimentaryBasisTerm n) := right₀.substBoundRudBasis ![r]

def sPower (r : L.RudimentaryBasisTerm n) (l : ℕ) := match l with
  | 0 => r -- junk value
  | 1 => r
  | l + 1 => (r.sPower l).sprod r

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
        simp only [tupleVal, right, snoc_last, isValue, substBoundRudBasis_substBoundRudBasis,
          Matrix.cons_val_fin_one]
        congr
        ext i; fin_cases i; simp [substBoundRudBasis]
      | cast i =>
        simp only [tupleVal, snoc_castSucc, isValue]
        rw [ih r.left, ih (var 0).left]
        simp only [substBoundRudBasis_substBoundRudBasis]
        congr
        ext i; fin_cases i
        simp only [left, Nat.succ_eq_add_one, Nat.reduceAdd, zero_eta, isValue,
          Matrix.cons_val_fin_one, substBoundRudBasis_substBoundRudBasis, substBoundRudBasis]
        rfl

def rotateSPower (r : L.RudimentaryBasisTerm n) (l : ℕ) (s : L.RudimentaryBasisTerm n) := match l with
  | 0 => r
  | l + 1 => r.rotate (s.sPower (l + 1))

def iterSwitch (r : L.RudimentaryBasisTerm n) (l : ℕ) (s : L.RudimentaryBasisTerm n) := match l with
  | 0 => r
  | l + 1 => (r.iterSwitch l s).switch s

/-- The set of elements in `sPower r (l + 1)` where after unraveling, the `l`th element is a
member of the `i`th element. -/
def lastMemFin {n} (i : Fin l) (r : L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  (r.memGraph.rotateSPower i.val r).iterSwitch (l - 1 - i.val) r

/-- The set of elements in `sPower (r ∪ (iterSUnion₀ 1 c)) (l + 1)` where after unraveling, the `l`th element is a
member of `c`. -/
def lastMemConst {n} (c : L.Constants) (l : ℕ) (r : L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  match l with
  | 0 => const c ∩ r
  | l + 1 => (r.sPower (l + 1)).sprod (const c ∩ r)

variable [L.ExtraConstantsUnaryRelationsOnly]

def unionConst (r : L.RudimentaryBasisTerm n) (t : L.Term' l) : L.RudimentaryBasisTerm n :=
  match t with
  | .var (Sum.inr i) => r
  | .func F _ (l := 0) => r ∪ {const F}
  | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F

/-- The set of elements in `sPower (r.unionConst t) (l + 1)` where after unraveling, the `l`th element is a
member of `t`. -/
def lastMemTerm' {n} (t : L.Term' l) (r : L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  match t with
  | .var (Sum.inr i) => r.lastMemFin i
  | .func F _ (l := 0) => r.lastMemConst F l
  | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F

def symDiff (r₁ r₂ : L.RudimentaryBasisTerm n) := (r₁ \ r₂) ∪ (r₂ \ r₁)

/-- The set of elements in `sPower ((r.unionIterSUnion₀Const t₁).unionIterSUnion₀Const t₂) l` where after unraveling, `t₁` is equal to `t₂`. -/
def eq {n} (t₁ t₂ : L.Term' l) (r : L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  ((var 0 : L.RudimentaryBasisTerm 2).sPower l) \
    (((var 1 : L.RudimentaryBasisTerm 2).lastMemTerm' t₁).symDiff ((var 1 : L.RudimentaryBasisTerm 2).lastMemTerm' t₂)).dom |>.substBoundRudBasis ![r, ((r.unionConst t₁).unionConst t₂).iterSUnion₀ 1]

/-- The set of elements in `sPower r l` where after unraveling, `t₁` is a member of `t₂`. -/
def mem {n} (t₁ t₂ : L.Term' l) (r : L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  (var 0 : L.RudimentaryBasisTerm 2).sPower l ∩
    (((var 1 : L.RudimentaryBasisTerm 2).eq (&-1) t₁.castSucc) ∩ ((var 1 : L.RudimentaryBasisTerm 2).lastMemTerm' t₂)).dom
    |>.substBoundRudBasis ![r, r.unionConst t₁]

/-- The set of elements in `sPower r l` where after unraveling, the `l`-tuple is true of `φ` -/
def truth (r : L.RudimentaryBasisTerm n) (φ : L.DeltaZeroBoundedFormula l) : L.RudimentaryBasisTerm n :=
  match φ with
  | .falsum => r \ r
  | .equal t₁ t₂ => r.eq t₁ t₂
  | .mem t₁ t₂ => r.mem t₁ t₂
  | .imp φ₁ φ₂ => r.sPower l \ (r.truth φ₁ \ r.truth φ₂)
  | .allMem t ψ => r.sPower l \ (((r.unionConst t).iterSUnion₀ 1).lastMemTerm' t \ ((r.unionConst t).iterSUnion₀ 1).truth ψ).dom
  | .rel _ _ => r -- junk value

end RudimentaryBasisTerm




end FirstOrder.Language
