import Mathlib.ModelTheory.Syntax
import Mathlib.Tactic.FinCases

open FirstOrder Language

open Structure Fin Nat

universe u v

variable {L : FirstOrder.Language}


@[inherit_doc] scoped[FirstOrder] prefix:110 "∀'' " => FirstOrder.Language.BoundedFormula.alls

@[inherit_doc] scoped[FirstOrder] prefix:110 "∃'' " => FirstOrder.Language.BoundedFormula.exs

namespace FirstOrder

namespace Language

namespace Term

/-- Cast a `L.Term (α ⊕ (Fin m))` to `L.Term (α ⊕ (Fin n))` given a proof of `m ≤ n` -/
def castLE (_h : m ≤ n) (t : L.Term (α ⊕ (Fin m))) :
  L.Term (α ⊕ (Fin n)):= t.relabel (Sum.map id (Fin.castLE _h))

/-- Cast a `L.Term (α ⊕ (Fin m))` to `L.Term (α ⊕ (Fin n))` given a proof of `m = n` -/
@[simp]
def cast (_h : m = n) (t : L.Term (α ⊕ (Fin m))) := t.castLE _h.le

/-- Cast a `L.Term (α ⊕ (Fin n))` to `L.Term (α ⊕ (Fin (n + 1)))` -/
@[simp]
def castSucc (t : L.Term (α ⊕ (Fin n))) := t.castLE (n.le_succ)

@[simp]
theorem castLE_castLE (h : n ≤ n') (h' : n' ≤ n'') (t : L.Term (α ⊕ (Fin n))) :
    (t.castLE h).castLE h' = t.castLE (h.trans h') := by
  simp [castLE]

@[simp 1100]
theorem castLE_var_inl (h : n ≤ n') (x : α) :
    (var (Sum.inl x) : L.Term (α ⊕ Fin n)).castLE h = var (Sum.inl x) := by
  simp [castLE]

@[simp 1100]
theorem castLE_var_inr (h : n ≤ n') (i : Fin n) :
    (var (Sum.inr i) : L.Term (α ⊕ Fin n)).castLE h = var (Sum.inr (Fin.castLE h i)) := by
  simp [castLE]

@[simp 1100]
theorem castLE_func (h : n ≤ n') (l : ℕ) (f : L.Functions l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (func f ts).castLE h = func f (fun i ↦ (ts i).castLE h) := by
  simp [castLE]

@[simp 1100]
theorem liftAt_var_inl (x : α) :
    (Term.var (Sum.inl x) : L.Term (α ⊕ Fin n)).liftAt n' m = Term.var (Sum.inl x) := by
  simp [liftAt]

@[simp 1100]
theorem liftAt_var_inr (i : Fin n) :
    (Term.var (Sum.inr i) : L.Term (α ⊕ Fin n)).liftAt n' m =
      Term.var (Sum.inr (if i < m then castAdd n' i else addNat i n')) := by
  simp [liftAt]

@[simp 1100]
theorem liftAt_func (l : ℕ) (f : L.Functions l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (Term.func f ts).liftAt n' m = Term.func f (fun i ↦ (ts i).liftAt n' m) := by
  simp [liftAt]

-- theorem liftAt_castLE_of_le (t : L.Term (α ⊕ Fin m)) (hmn : m ≤ n) (hmm' : m ≤ m') :
--     (t.castLE hmn).liftAt n' m' = (t.liftAt (n' + (n - m)) m').cast (by omega) := by
--   simp only [liftAt, castLE, relabel_relabel, Sum.map_comp_map, Function.comp_id, cast]
--   congr 1
--   simp only [Sum.map, Function.comp_id]
--   congr 2
--   grind

end Term

namespace BoundedFormula

@[simp]
def cast : ∀ {m n : ℕ} (_h : m = n), L.BoundedFormula α m → L.BoundedFormula α n :=
  fun _h ↦ castLE _h.le

@[simp 1100]
theorem castLE_falsum (h : n ≤ n') :
    (falsum : L.BoundedFormula α n).castLE h = falsum := by simp

@[simp 1100]
theorem castLE_equal (h : n ≤ n') (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂).castLE h = equal (t₁.castLE h) (t₂.castLE h) := by simp [Term.castLE]

@[simp 1100]
theorem castLE_rel (h : n ≤ n') (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts).castLE h = rel R (fun i ↦ (ts i).castLE h)  := by
  simp only [castLE, Term.castLE, rel.injEq, heq_eq_eq, true_and]
  ext i; simp

@[simp 1100]
theorem castLE_rel_boundedFormula₁ (h : n ≤ n') (R : L.Relations 1)
    (t : L.Term (α ⊕ (Fin n))) :
    (R.boundedFormula₁ t).castLE h = R.boundedFormula₁ (t.castLE h) := by
  simp only [Relations.boundedFormula₁, Relations.boundedFormula, BoundedFormula.castLE_rel,
    Matrix.cons_val_fin_one, BoundedFormula.rel.injEq, heq_eq_eq, true_and]
  ext; simp

@[simp 1100]
theorem castLE_rel_boundedFormula₂ (h : n ≤ n') (R : L.Relations 2)
    (t₁ t₂ : L.Term (α ⊕ (Fin n))) :
    (R.boundedFormula₂ t₁ t₂).castLE h = R.boundedFormula₂ (t₁.castLE h) (t₂.castLE h) := by
  simp only [Relations.boundedFormula₂, Relations.boundedFormula, BoundedFormula.castLE_rel,
    BoundedFormula.rel.injEq, heq_eq_eq, true_and]
  ext i; fin_cases i <;> simp

@[simp 1100]
theorem castLE_imp (h : n ≤ n') (φ ψ : L.BoundedFormula α n) :
    (φ ⟹ ψ).castLE h = φ.castLE h ⟹ ψ.castLE h := by
  simp

@[simp 1100]
theorem castLE_all (h : n ≤ n') (φ : L.BoundedFormula α (n + 1)) :
    (∀' φ).castLE h = ∀' (φ.castLE (add_le_add_left h 1)) := by simp

@[simp 1100]
theorem liftAt_falsum :
    (falsum : L.BoundedFormula α n).liftAt n' m = falsum := by
  simp [liftAt, mapTermRel]

@[simp 1100]
theorem liftAt_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂).liftAt n' m = equal (t₁.liftAt n' m) (t₂.liftAt n' m) := by
  simp [liftAt, mapTermRel]

@[simp 1100]
theorem liftAt_rel (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts).liftAt n' m = rel R (fun i ↦ (ts i).liftAt n' m)  := by
  simp [liftAt, mapTermRel]

@[simp 1100]
theorem liftAt_rel_boundedFormula₁ (R : L.Relations 1)
    (t : L.Term (α ⊕ (Fin n))) :
    (R.boundedFormula₁ t).liftAt n' m = R.boundedFormula₁ (t.liftAt n' m) := by
  simp only [Relations.boundedFormula₁, Relations.boundedFormula, liftAt_rel,
    Matrix.cons_val_fin_one, rel.injEq, heq_eq_eq, true_and]
  ext; simp

@[simp 1100]
theorem liftAt_rel_boundedFormula₂ (R : L.Relations 2)
    (t₁ t₂ : L.Term (α ⊕ (Fin n))) :
    (R.boundedFormula₂ t₁ t₂).liftAt n' m =
      R.boundedFormula₂ (t₁.liftAt n' m) (t₂.liftAt n' m) := by
  simp only [Relations.boundedFormula₂, Relations.boundedFormula, liftAt_rel, rel.injEq, heq_eq_eq,
    true_and]
  ext i; fin_cases i <;> simp

@[simp 1100]
theorem liftAt_imp (φ ψ : L.BoundedFormula α n) :
    (φ ⟹ ψ).liftAt n' m = φ.liftAt n' m ⟹ ψ.liftAt n' m := by
  simp [liftAt, mapTermRel]

@[simp 1100]
theorem liftAt_all (φ : L.BoundedFormula α (n + 1)) :
    (∀' φ).liftAt n' m = ∀' (φ.liftAt n' m).cast (Nat.add_right_comm _ _ _) := by
  simp [liftAt, mapTermRel]


-- @[simp]
-- theorem castLE_rfl {n} (φ : L.BoundedFormula α n) : φ.cast rfl = φ := castLE_rfl _ _

-- @[simp]
-- theorem castLE_all_castLE_eq_all {m n : ℕ} (h : m = n) (φ : L.BoundedFormula α (m + 1)) :
--     (φ.cast (h ▸ rfl)).all.cast h.symm = φ.all := by
--   simp [cast]

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
theorem castLE_all'_eq_all'_cast (h : n ≤ n') (φ : L.BoundedFormula α (n + m)) :
    (φ.all' m).castLE h = (φ.castLE (add_le_add_left h m)).all' m  := by
  induction m with
  | zero => simp
  | succ m ih => rw [all'_succ, all'_succ, ih]; congr

@[simp]
theorem castLE_all_eq_all_cast (h : n ≤ n') (φ : L.BoundedFormula α (n + 1)) :
    (φ.all).castLE h = (φ.castLE (add_le_add_left h 1)).all := φ.castLE_all'_eq_all'_cast h

-- @[simp]
-- theorem all'_all_castLE_eq_all' (φ : L.BoundedFormula α (n + (m + 1))) :
--     ((φ.castLE (n.add_assoc m 1).symm).all).all' m = φ.all' (m + 1) := by
--   induction m with
--   | zero => simp
--   | succ m ih => rw [all', all', ← ih]; congr

theorem all'_all'_eq_all'_cast (φ : L.BoundedFormula α (n + m + k)) :
    (φ.all' k).all' m = (φ.cast (n.add_assoc m k)).all' (m + k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [all']; convert ih _ using 1

-- @[simp]
-- theorem all'_castLE_eq_alls (φ : L.BoundedFormula α n) :
--     (φ.cast (Nat.zero_add n).symm).all' n = φ.alls := by
--   induction n with
--   | zero => simp [alls]
--   | succ n ih => rw [all', alls]; convert ih _; simp

@[simp]
theorem liftAt_all'_eq_all'_cast_liftAt (φ : L.BoundedFormula α (n + m)) :
    (φ.all' m).liftAt n' k = ((φ.liftAt n' k).cast (add_right_comm _ _ _)).all' m := by
  induction m with
  | zero => simp
  | succ m ih => simp [all'_succ, all'_succ, ih]

@[simp]
theorem liftAt_all_eq_all_cast_liftAt (φ : L.BoundedFormula α (n + 1)) :
    φ.all.liftAt n' k = ((φ.liftAt n' k).cast (add_right_comm _ _ _)).all :=
  φ.liftAt_all'_eq_all'_cast_liftAt

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
theorem castLE_ex'_eq_ex'_cast (h : n ≤ n') (φ : L.BoundedFormula α (n + m)) :
    (φ.ex' m).castLE h = (φ.castLE (add_le_add_left h m)).ex' m  := by
  induction m with
  | zero => simp
  | succ m ih => rw [ex'_succ, ex'_succ, ih]; congr

@[simp]
theorem castLE_ex_eq_ex_cast (h : n ≤ n') (φ : L.BoundedFormula α (n + 1)) :
    (φ.ex).castLE h = (φ.castLE (add_le_add_left h 1)).ex := φ.castLE_ex'_eq_ex'_cast h

-- @[simp]
-- theorem ex'_ex_castLE_eq_ex' (φ : L.BoundedFormula α (n + (m + 1))) :
--     ((φ.castLE (n.add_assoc m 1).symm).ex).ex' m = φ.ex' (m + 1) := by
--   induction m with
--   | zero => simp
--   | succ m ih => rw [ex', ex', ← ih]; congr

theorem ex'_ex'_eq_ex'_cast (φ : L.BoundedFormula α (n + m + k)) :
    (φ.ex' k).ex' m = (φ.cast (n.add_assoc m k)).ex' (m + k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [ex']; convert ih _ using 1

-- @[simp]
-- theorem ex'_cast_eq_exs (φ : L.BoundedFormula α n) :
--     (φ.cast (Nat.zero_add n).symm).ex' n = φ.exs := by
--   induction n with
--   | zero => simp [exs]
--   | succ n ih => rw [ex', exs]; convert ih _; simp; rfl

@[simp]
theorem liftAt_ex'_eq_ex'_cast_liftAt (φ : L.BoundedFormula α (n + m)) :
    (φ.ex' m).liftAt n' k = ((φ.liftAt n' k).cast (add_right_comm _ _ _)).ex' m := by
  induction m with
  | zero => simp
  | succ m ih => simp [ex'_succ, BoundedFormula.ex, BoundedFormula.not, Bot.bot, ih]

@[simp]
theorem liftAt_ex_eq_ex_cast_liftAt (φ : L.BoundedFormula α (n + 1)) :
    φ.ex.liftAt n' k = ((φ.liftAt n' k).cast (add_right_comm _ _ _)).ex :=
  φ.liftAt_ex'_eq_ex'_cast_liftAt

/-- The largest index of the bounded variables -/
scoped[FirstOrder] notation "&-1" => &(Fin.last _)

/-- The second largest index of the bounded variables -/
scoped[FirstOrder] notation "&-2" => &(Fin.last _ - 1)

/-- The third largest index of the bounded variables -/
scoped[FirstOrder] notation "&-3" => &(Fin.last _ - 2)

/-- The fourth largest index of the bounded variables -/
scoped[FirstOrder] notation "&-4" => &(Fin.last _ - 3)

/-- The fifth largest index of the bounded variables -/
scoped[FirstOrder] notation "&-5" => &(Fin.last _ - 4)

/-- The sixth largest index of the bounded variables -/
scoped[FirstOrder] notation "&-6" => &(Fin.last _ - 5)

/-- The seventh largest index of the bounded variables -/
scoped[FirstOrder] notation "&-7" => &(Fin.last _ - 6)

/-- The eighth largest index of the bounded variables -/
scoped[FirstOrder] notation "&-8" => &(Fin.last _ - 7)

/-- The ninth largest index of the bounded variables -/
scoped[FirstOrder] notation "&-9" => &(Fin.last _ - 8)

/-- Puts a `∃!` quantifier on a bounded formula. -/
protected def exUnique (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  ∃' (φ ⊓ ∀' (φ.liftAt 1 n ⟹ &-1 =' &-2))

@[inherit_doc] scoped[FirstOrder] prefix:110 "∃!' " => FirstOrder.Language.BoundedFormula.exUnique

end BoundedFormula

end Language

end FirstOrder
