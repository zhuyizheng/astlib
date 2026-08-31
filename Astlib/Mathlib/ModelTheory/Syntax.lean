/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.ModelTheory.Syntax
import Mathlib.Tactic.FinCases
import Astlib.Mathlib.Fin.Basic
/-!
file docstring
-/

open FirstOrder Language

open Structure Fin Nat

universe u v

variable {L : FirstOrder.Language} {α : Type*} {m n n' n'' l k : ℕ}


@[inherit_doc] scoped[FirstOrder] prefix:110 "∀'' " => FirstOrder.Language.BoundedFormula.alls

@[inherit_doc] scoped[FirstOrder] prefix:110 "∃'' " => FirstOrder.Language.BoundedFormula.exs

namespace FirstOrder

namespace Language

abbrev Term' (L : Language) (n) := L.Term (Empty ⊕ Fin n)

namespace Term

variable {L : Language} {n m k : ℕ} (ts : Fin n → L.Term (α ⊕ Fin m)) {i : Fin n} {x : α}
  (f : Fin n → Fin m) (g : Fin m → Fin k) (u : L.Term (α ⊕ Fin n))

/-- `u.substBound ts : L.Term (α ⊕ Fin m)` is obtained by replacing every occurrence of the
bound variable `&i` by `ts i` -/
def substBound {L : Language} {n m : ℕ} (u : L.Term (α ⊕ Fin n))
    (ts : Fin n → L.Term (α ⊕ Fin m)) : L.Term (α ⊕ (Fin m)) :=
  u.subst (Sum.elim (var ∘ Sum.inl) ts)

@[simp]
theorem substBound_var_inl : (var (Sum.inl x)).substBound ts = var (Sum.inl x) := by
  simp [substBound]

@[simp]
theorem substBound_var_comp_inr : (&i).substBound ts = ts i := by
  simp [substBound]

@[simp]
theorem substBound_var_inr : (var (Sum.inr i)).substBound ts = ts i := by
  simp [substBound]

@[simp]
theorem substBound_var_func (f : L.Functions l) (us : Fin l → L.Term (α ⊕ Fin n)) :
    (func f us).substBound ts = func f (fun i ↦ (us i).substBound ts) := by
  simp [substBound]

@[simp]
theorem substBound_substBound (us : Fin m → L.Term (α ⊕ Fin k)) :
    (u.substBound ts).substBound us = u.substBound (fun i ↦ (ts i).substBound us) := by
  induction u with
  | var i => cases i <;> simp
  | func f vs ih => simp [ih]

/-- `u.substBound ts : L.Term (α ⊕ Fin m)` is obtained by replacing every occurrence of the
bound variable `&i` by `ts i` -/
def substBoundBound {L : Language} {n m : ℕ} (u : L.Term (α ⊕ Fin n))
    (f : Fin n → Fin m) : L.Term (α ⊕ (Fin m)) :=
  u.substBound (fun i ↦ &(f i))

@[simp]
theorem substBoundBound_var_inl :
    (var (Sum.inl x) : L.Term (α ⊕ Fin n)).substBoundBound f = var (Sum.inl x) := by
  simp [substBoundBound]

@[simp]
theorem substBoundBound_var_comp_inr : (&i : L.Term (α ⊕ Fin n)).substBoundBound f = &(f i) := by
  simp [substBoundBound, substBound]

@[simp]
theorem substBoundBound_var_inr :
    (var (Sum.inr i) : L.Term (α ⊕ Fin n)).substBoundBound f = &(f i) := by
  simp [substBoundBound, substBound]

@[simp]
theorem substBoundBound_var_func (F : L.Functions l) (us : Fin l → L.Term (α ⊕ Fin n)) :
    (func F us).substBoundBound f = func F (fun i ↦ (us i).substBoundBound f) := by
  simp [substBoundBound]

@[simp]
theorem substBoundBound_substBoundBound :
    (u.substBoundBound f).substBoundBound g = u.substBoundBound (g ∘ f) := by
  simp [substBoundBound]

@[simp]
theorem substBoundBound_id :
    u.substBoundBound id = u := by
  induction u with
  | var i => cases i <;> simp [substBoundBound, substBound]
  | func f us ih => simp [ih]

/-- Cast a `L.Term (α ⊕ (Fin m))` to `L.Term (α ⊕ Fin n)` given a proof of `m ≤ n` -/
@[simp]
def castLE (h : m ≤ n) (t : L.Term (α ⊕ Fin m)) :
  L.Term (α ⊕ Fin n) := t.substBoundBound (Fin.castLE h)

/-- Cast a `L.Term (α ⊕ (Fin m))` to `L.Term (α ⊕ Fin n)` given a proof of `m = n` -/
@[simp]
def cast (h : m = n) (t : L.Term (α ⊕ Fin m)) : L.Term (α ⊕ Fin n) := t.castLE h.le

/-- Cast a `L.Term (α ⊕ Fin n)` to `L.Term (α ⊕ (Fin (n + 1)))` -/
@[simp]
def castAdd (t : L.Term (α ⊕ Fin n)) (m : ℕ) : L.Term (α ⊕ Fin (n + m)) :=
  t.castLE (n.le_add_right m)

/-- Cast a `L.Term (α ⊕ Fin n)` to `L.Term (α ⊕ (Fin (n + 1)))` -/
@[simp]
def castSucc (t : L.Term (α ⊕ Fin n)) := t.castAdd 1

@[simp]
theorem substBound_castSucc_snoc_castSucc
    (u : L.Term (α ⊕ Fin n)) (ts : Fin n → L.Term (α ⊕ Fin m)) (t : L.Term (α ⊕ Fin (m + 1))) :
    (u.castSucc).substBound (snoc (fun i ↦ (ts i).castSucc) t) = (u.substBound ts).castSucc := by
  simp only [castSucc, castAdd, castLE, substBoundBound, castLE_succ_castSucc, Function.comp_apply,
    substBound_substBound, substBound_var_inr, snoc_castSucc]

-- @[simp]
-- theorem castLE_castLE (h : n ≤ n') (h' : n' ≤ n'') (t : L.Term (α ⊕ Fin n)) :
--     (t.castLE h).castLE h' = t.castLE (h.trans h') := by
--   simp [castLE]


end Term

abbrev BoundedFormula' (n) := L.BoundedFormula Empty n

-- instance : Inhabited (L.BoundedFormula' n) :=
--   ⟨(⊥ : L.BoundedFormula Empty n)⟩

-- instance : Bot (L.BoundedFormula' n) :=
--   ⟨(⊥ : L.BoundedFormula Empty n)⟩

-- instance : Top (L.BoundedFormula' n) :=
--   ⟨BoundedFormula.not ⊥⟩

-- instance : Min (L.BoundedFormula' n) :=
--   ⟨fun f g => (f.imp g.not).not⟩

-- instance : Max (L.BoundedFormula' n) :=
--   ⟨fun f g => f.not.imp g⟩

namespace BoundedFormula

/-- `φ.substBound ts : L.BoundedFormula α m` is obtained by replacing every occurrence of the
bound variable `&i` by `ts i` if `i < n`, by `&(i + m - n)` otherwise -/
def substBound
    {L : Language} {n m : ℕ} (φ : L.BoundedFormula α n)
    (ts : Fin n → L.Term (α ⊕ Fin m)) : L.BoundedFormula α m :=
  match φ with
  | falsum => falsum
  | equal t₁ t₂ => equal (t₁.substBound ts) (t₂.substBound ts)
  | rel R vs => rel R (fun k ↦ (vs k).substBound ts)
  | imp φ₁ φ₂ => φ₁.substBound ts ⟹ φ₂.substBound ts
  | all φ => ∀' (φ.substBound (snoc (fun i ↦ (ts i).castSucc) &(last m)))

variable (ts : Fin n → L.Term (α ⊕ Fin m)) (f : Fin n → Fin m) (g : Fin m → Fin k)

@[simp]
theorem substBound_falsum :
    (falsum : L.BoundedFormula α n).substBound ts = falsum := by simp [substBound]

@[simp]
theorem substBound_bot :
    (⊥ : L.BoundedFormula α n).substBound ts = ⊥ := by simp [Bot.bot]

@[simp]
theorem substBound_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂).substBound ts = equal (t₁.substBound ts) (t₂.substBound ts) := by
  simp [substBound]

@[simp]
theorem substBound_equal' (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (t₁ =' t₂).substBound ts = t₁.substBound ts =' t₂.substBound ts := by
  simp [Term.bdEqual]

@[simp]
theorem substBound_rel (R : L.Relations l)
    (us : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R us).substBound ts = rel R (fun i ↦ (us i).substBound ts)  := by
  simp [substBound]

@[simp]
theorem substBound_rel_boundedFormula₁ (R : L.Relations 1)
    (t : L.Term (α ⊕ Fin n)) :
    (R.boundedFormula₁ t).substBound ts = R.boundedFormula₁ (t.substBound ts) := by
  simp [Relations.boundedFormula₁, Relations.boundedFormula, Matrix.const_fin1_eq]

@[simp]
theorem substBound_rel_boundedFormula₂ (R : L.Relations 2) (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (R.boundedFormula₂ t₁ t₂).substBound ts =
      R.boundedFormula₂ (t₁.substBound ts) (t₂.substBound ts) := by
  simp only [Relations.boundedFormula₂, Relations.boundedFormula, substBound_rel, rel.injEq,
    heq_eq_eq, true_and]
  exact List.ofFn_inj.mp rfl

@[simp]
theorem substBound_imp (φ ψ : L.BoundedFormula α n) :
    (φ ⟹ ψ).substBound ts = φ.substBound ts ⟹ ψ.substBound ts := by
  simp [substBound]

@[simp]
theorem substBound_all (ψ : L.BoundedFormula α (n + 1)) :
    (∀' ψ).substBound ts = ∀' (ψ.substBound (snoc (fun i ↦ (ts i).castSucc) &(last m))) := by
  simp [substBound]

@[simp]
theorem substBound_ex (ψ : L.BoundedFormula α (n + 1)) :
    (∃' ψ).substBound ts = ∃' (ψ.substBound (snoc (fun i ↦ (ts i).castSucc) &(last m))) := by
  simp [substBound]
  rfl

@[simp]
theorem substBound_substBound (φ : L.BoundedFormula α n) (ts : Fin n → L.Term (α ⊕ Fin m))
    (us : Fin m → L.Term (α ⊕ Fin k)) :
    (φ.substBound ts).substBound us = φ.substBound (fun i ↦ (ts i).substBound us) := by
  induction φ generalizing m k with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R vs => simp
  | imp φ₁ φ₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | all ψ ih =>
    simp only [substBound_all, Function.comp_apply, ih, all.injEq]
    congr
    ext i
    induction i using lastCases with
    | last => simp
    | cast i' =>
      simp only [Term.castSucc, Term.castAdd, Term.castLE, Term.substBoundBound,
        Function.comp_apply, snoc_castSucc, Term.substBound_substBound, Term.substBound_var_inr]
      congr
      ext j
      have : Fin.castSucc j = Fin.castLE (by omega) j := rfl
      rw [← this, snoc_castSucc]

/-- `φ.substBoundBound f : L.BoundedFormula α m` is obtained by replacing every occurrence of the
bound variable `&i` by `&(f i)` if `i < n`, by `&(i + m - n)` otherwise -/
def substBoundBound
    {L : Language} {n m : ℕ} (φ : L.BoundedFormula α n)
    (f : Fin n → Fin m) : L.BoundedFormula α m :=
  φ.substBound (fun i ↦ &(f i))

@[simp]
theorem substBoundBound_falsum :
    (falsum : L.BoundedFormula α n).substBoundBound f = falsum := by simp [substBoundBound]

@[simp]
theorem substBoundBound_bot :
    (⊥ : L.BoundedFormula α n).substBoundBound f = ⊥ := by simp [Bot.bot]

@[simp]
theorem substBoundBound_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂).substBoundBound f = equal (t₁.substBoundBound f) (t₂.substBoundBound f) := by
  simp [substBoundBound, Term.substBoundBound]

@[simp]
theorem substBoundBound_rel (R : L.Relations l)
    (us : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R us).substBoundBound f = rel R (fun i ↦ (us i).substBoundBound f)  := by
  simp [substBoundBound, Term.substBoundBound]

@[simp]
theorem substBoundBound_rel_boundedFormula₁ (R : L.Relations 1)
    (t : L.Term (α ⊕ Fin n)) :
    (R.boundedFormula₁ t).substBoundBound f = R.boundedFormula₁ (t.substBoundBound f) := by
  simp [substBoundBound, Term.substBoundBound]

@[simp]
theorem substBoundBound_rel_boundedFormula₂ (R : L.Relations 2) (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (R.boundedFormula₂ t₁ t₂).substBoundBound f =
      R.boundedFormula₂ (t₁.substBoundBound f) (t₂.substBoundBound f) := by
  simp [substBoundBound, Term.substBoundBound]

@[simp]
theorem substBoundBound_imp (φ ψ : L.BoundedFormula α n) :
    (φ ⟹ ψ).substBoundBound f = φ.substBoundBound f ⟹ ψ.substBoundBound f := by
  simp [substBoundBound]

@[simp]
theorem substBoundBound_all (ψ : L.BoundedFormula α (n + 1)) :
    (∀' ψ).substBoundBound f =
      ∀' (ψ.substBoundBound (snoc (fun i ↦ (f i).castSucc) (last m))) := by
  simp only [substBoundBound, Function.comp_apply, substBound_all, Term.castSucc, Term.castAdd,
    Term.castLE, Term.substBoundBound_var_inr, all.injEq]
  congr
  ext i
  induction i using lastCases with
  | last => simp
  | cast i' => grind [snoc_castSucc, Sum.inr.injEq]

@[simp]
theorem substBoundBound_ex (ψ : L.BoundedFormula α (n + 1)) :
    (∃' ψ).substBoundBound f =
      ∃' (ψ.substBoundBound (snoc (fun i ↦ (f i).castSucc) (last m))) := by
  simp [BoundedFormula.ex, BoundedFormula.not]

@[simp]
theorem substBoundBound_substBoundBound (φ : L.BoundedFormula α n) :
    (φ.substBoundBound f).substBoundBound g = φ.substBoundBound (g ∘ f) := by
  simp [substBoundBound]

@[simp]
theorem substBoundBound_id {φ : L.BoundedFormula α n} : φ.substBoundBound id = φ := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ₁ φ₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | all ψ ih => simp [ih]

@[simp]
def cast {m n : ℕ} (h : m = n) (φ : L.BoundedFormula α m) : L.BoundedFormula α n :=
  φ.substBoundBound (Fin.cast h)

/-- Places `m` universal quantifiers in front of a bounded formula. -/
def all' : ∀ m, L.BoundedFormula α (n + m) → L.BoundedFormula α n
  | 0, φ => φ
  | m + 1, φ => φ.all.all' m

@[simp]
theorem all'_zero (φ : L.BoundedFormula α n) : φ.all' 0 = φ := by rfl

@[simp]
theorem all'_one (φ : L.BoundedFormula α (n + 1)) : φ.all' 1 = ∀' φ := by rfl

theorem all'_succ (φ : L.BoundedFormula α (n + m + 1)) : φ.all' (m + 1) = φ.all.all' m := by rfl

@[simp]
theorem substBound_all'_eq_all'_substBound (φ : L.BoundedFormula α (n + m))
    (ts : Fin n → L.Term (α ⊕ Fin k)) :
    (φ.all' m).substBound ts =
      (φ.substBound (append (fun i ↦ (ts i).castAdd m) (fun i ↦ &(i.natAdd k)))).all' m  := by
  induction m with
  | zero => simp [append_right_nil]
  | succ m ih =>
    rw [all'_succ, all'_succ, ih, substBound_all]
    congr
    ext i
    cases i using lastCases with
    | last => simp
    | cast j =>
      simp only [Term.castSucc, Term.castAdd, Term.castLE, Function.comp_apply, append_nat,
        natAdd_mk, castLE_succ_castSucc, snoc_castSucc, val_castSucc]
      split_ifs
      · simp only [Term.substBoundBound_substBoundBound]
        rfl
      · simp

-- @[simp]
-- theorem cast_all'_eq_all'_cast (h : n = n') (φ : L.BoundedFormula α (n + m)) :
--     (φ.all' m).cast h = (φ.cast (Nat.add_left_inj.mpr h)).all' m  := by
--   induction m with
--   | zero => simp
--   | succ m ih =>
--     rw [all'_succ, all'_succ, ih]
--     congr
--     simp only [cast, substBoundBound_all]
--     congr
--     simp only [castSucc, Fin.cast, castAdd_mk]
--     rw [snoc_val_last_eq_cast (by omega)]

-- @[simp]
-- theorem cast_all_eq_all_cast (h : n = n') (φ : L.BoundedFormula α (n + 1)) :
--     (φ.all).cast h = (φ.cast (Nat.add_left_inj.mpr h)).all := φ.cast_all'_eq_all'_cast h

theorem all'_all'_eq_all'_cast (φ : L.BoundedFormula α (n + m + k)) :
    (φ.all' k).all' m = (φ.cast (n.add_assoc m k)).all' (m + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [all', add_eq, ih, cast, substBoundBound_all]
    congr
    simp only [castSucc, Fin.cast, castAdd_mk]
    rw [snoc_val_last_eq_cast (by omega)]

/-- Places `m` existential quantifiers in front of a bounded formula. -/
def ex' : ∀ m, L.BoundedFormula α (n + m) → L.BoundedFormula α n
  | 0, φ => φ
  | m + 1, φ => φ.ex.ex' m

@[simp]
theorem ex'_zero (φ : L.BoundedFormula α n) : φ.ex' 0 = φ := by rfl

@[simp]
theorem ex'_one (φ : L.BoundedFormula α (n + 1)) : φ.ex' 1 = ∃' φ := by rfl

theorem ex'_succ (φ : L.BoundedFormula α (n + m + 1)) : φ.ex' (m + 1) = φ.ex.ex' m := by rfl

@[simp]
theorem substBound_ex'_eq_ex'_substBound (φ : L.BoundedFormula α (n + m))
    (ts : Fin n → L.Term (α ⊕ Fin k)) :
    (φ.ex' m).substBound ts =
      (φ.substBound (append (fun i ↦ (ts i).castAdd m) (fun i ↦ &(i.natAdd k)))).ex' m  := by
  induction m with
  | zero => simp [append_right_nil]
  | succ m ih =>
    rw [ex'_succ, ex'_succ, ih, substBound_ex]
    congr
    ext i
    induction i using lastCases with
    | last => simp
    | cast j =>
      simp only [Term.castSucc, Term.castAdd, Term.castLE, Function.comp_apply, append_nat,
        natAdd_mk, castLE_succ_castSucc, snoc_castSucc, val_castSucc]
      split_ifs
      · simp only [Term.substBoundBound_substBoundBound]
        rfl
      · simp


-- @[simp]
-- theorem cast_ex'_eq_ex'_cast (h : n = n') (φ : L.BoundedFormula α (n + m)) :
--     (φ.ex' m).cast h = (φ.cast (Nat.add_left_inj.mpr h)).ex' m  := by
--   induction m with
--   | zero => simp
--   | succ m ih =>
--     rw [ex'_succ, ex'_succ, ih]
--     congr
--     simp only [cast, substBoundBound_ex]
--     congr
--     simp only [castSucc, Fin.cast, castAdd_mk]
--     rw [snoc_val_last_eq_cast (by omega)]


-- @[simp]
-- theorem cast_ex_eq_ex_cast (h : n = n') (φ : L.BoundedFormula α (n + 1)) :
--     (φ.ex).cast h = (φ.cast (Nat.add_left_inj.mpr h)).ex := φ.cast_ex'_eq_ex'_cast h

theorem ex'_ex'_eq_ex'_cast (φ : L.BoundedFormula α (n + m + k)) :
    (φ.ex' k).ex' m = (φ.cast (n.add_assoc m k)).ex' (m + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [ex', add_eq, ih, cast, substBoundBound_ex]
    congr
    simp only [castSucc, Fin.cast, castAdd_mk]
    rw [snoc_val_last_eq_cast (by omega)]

/-- The largest index of the bounded variables -/
scoped[FirstOrder] notation "&-1" => &(last _)

/-- The second largest index of the bounded variables -/
scoped[FirstOrder] notation "&-2" => &(castAdd 1 (last _))

/-- The third largest index of the bounded variables -/
scoped[FirstOrder] notation "&-3" => &(castAdd 2 (last _))

/-- The fourth largest index of the bounded variables -/
scoped[FirstOrder] notation "&-4" => &(castAdd 3 (last _))

-- /-- The fifth largest index of the bounded variables -/
-- scoped[FirstOrder] notation "&-5" => &(Fin.last _ - 4)

-- /-- The sixth largest index of the bounded variables -/
-- scoped[FirstOrder] notation "&-6" => &(Fin.last _ - 5)

-- /-- The seventh largest index of the bounded variables -/
-- scoped[FirstOrder] notation "&-7" => &(Fin.last _ - 6)

-- /-- The eighth largest index of the bounded variables -/
-- scoped[FirstOrder] notation "&-8" => &(Fin.last _ - 7)

-- /-- The ninth largest index of the bounded variables -/
-- scoped[FirstOrder] notation "&-9" => &(Fin.last _ - 8)

/-- Puts a `∃!` quantifier on a bounded formula. -/
protected def exUnique (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  ∃' (φ ⊓ ∀' (φ.substBoundBound (snoc (castAdd 2) (last _)) ⟹ &-1 =' &-2))

@[inherit_doc] scoped[FirstOrder] prefix:110 "∃!' " => FirstOrder.Language.BoundedFormula.exUnique


end BoundedFormula

end Language

end FirstOrder
