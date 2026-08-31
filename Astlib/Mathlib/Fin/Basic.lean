/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
/-!
file docstring
-/

variable {α : Type*} {m n p : ℕ} (a : Fin m → α) (b : Fin n → α) (c : Fin p → α) (x : α)

open Fin Nat


@[simp, grind =]
theorem Fin.cast_comp_cast {n m k : ℕ} (h : n = m) (h' : m = k) :
    Fin.cast h' ∘ Fin.cast h  = Fin.cast (Eq.trans h h') := by
  ext i; simp

@[simp]
theorem Fin.snoc_castSucc_last : snoc (fun i ↦ i.castSucc) (last n) = id := by
  convert Fin.snoc_init_self _
  · grind [init]
  · simp

@[simp]
theorem Fin.snoc_val_last_eq_cast {n' : ℕ} (h : n = n') :
    snoc (fun i ↦ (⟨i.val, i.prop.trans (h ▸ n'.lt_add_one)⟩)) (last n') =
      Fin.cast (Nat.succ_inj.mpr h) := by
  ext i
  cases i using Fin.lastCases with
  | last => simp
  | cast i' => simp

@[simp]
theorem Fin.append_comp_castAdd : append a b ∘ (castAdd n) = a := by ext i; simp

@[simp]
theorem Fin.append_comp_natAdd : append a b ∘ (natAdd m) = b := by ext i; simp

@[simp]
theorem Fin.snoc_comp_snoc (f : Fin n → Fin m) :
    (snoc a x) ∘ (snoc (castSucc ∘ f) (last m)) = snoc (a ∘ f) x := by
  ext i
  cases i using Fin.lastCases with
  | last => simp
  | cast i' => simp

@[simp]
theorem Fin.snoc_comp_snoc' (f : Fin n → Fin m) :
    (snoc a x) ∘ (snoc (fun y ↦ castSucc (f y)) (last m)) = snoc (a ∘ f) x := by
  convert Fin.snoc_comp_snoc _ _ _
  simp

@[simp]
theorem Fin.castLE_succ_castSucc (n : ℕ) : Fin.castLE n.le_succ = Fin.castSucc := by rfl

theorem Fin.castLE_add_two_castSucc (n : ℕ) : Fin.castLE (n := n) (m := n + 2) (by omega) =
    Fin.castSucc ∘ Fin.castSucc := by rfl

theorem Fin.castLE_add_three_castSucc (n : ℕ) : Fin.castLE (n := n) (m := n + 3) (by omega) =
    Fin.castSucc ∘ Fin.castSucc ∘ Fin.castSucc := by rfl

theorem Fin.castLE_add_four_castSucc (n : ℕ) : Fin.castLE (n := n) (m := n + 4) (by omega) =
    Fin.castSucc ∘ Fin.castSucc ∘ Fin.castSucc ∘ Fin.castSucc := by rfl

@[simp]
theorem snoc_snoc_comp_castSucc_castSucc {α : Sort*} {a b : α} {f : Fin n → α} :
    (snoc (snoc f a : Fin (n + 1) → α) b) ∘ castSucc ∘ castSucc = f := by
  simp [← Function.comp_assoc]

theorem castAdd_two_eq_castSucc_castSucc :
    castLE (n := n) (m := n + 2) (by omega) =  castSucc ∘ castSucc := by
  ext; simp

@[simp]
theorem snoc_snoc_comp_castLE {α : Sort*} {a b : α} {f : Fin n → α} :
    (snoc (snoc f a : Fin (n + 1) → α) b) ∘ (castLE (by omega)) = f := by
  simp [castAdd_two_eq_castSucc_castSucc]

@[simp]
theorem Fin.val_last_plus_one_minus_one : (last (n + 1) - 1).val = n := by
  simp only [last, sub_def, coe_ofNat_eq_mod, one_mod, Nat.add_one_sub_one]
  rw [Nat.mod_eq_sub_mod (by omega)]
  convert Nat.mod_eq_of_lt ?_ <;> grind

@[simp]
theorem Fin.val_last_plus_two_minus_two : (last (n + 2) - 2).val = n := by
  simp only [last, sub_def, coe_ofNat_eq_mod]
  rw [Nat.mod_eq_of_lt (a := 2) (by omega), Nat.mod_eq_sub_mod (by omega)]
  convert Nat.mod_eq_of_lt ?_ <;> grind

@[simp]
theorem Fin.val_last_plus_two_minus_three : (last (n + 3) - 3).val = n := by
  simp only [last, sub_def, coe_ofNat_eq_mod]
  rw [Nat.mod_eq_of_lt (a := 3) (by omega), Nat.mod_eq_sub_mod (by omega)]
  convert Nat.mod_eq_of_lt ?_ <;> grind

-- @[simp]
-- theorem Fin.val_last_plus_minus :
--     (last (n + p) - OfNat.ofNat (α := Fin (n + p + 1)) p).val = n := by
--   simp only [OfNat.ofNat, last, ofNat_eq_cast, sub_def, val_natCast]
--   rw [Nat.mod_eq_of_lt (a := p) (by lia), Nat.mod_eq_sub_mod (by omega)]
--   convert Nat.mod_eq_of_lt ?_ <;> grind

theorem Fin.cons_nat (i : Fin (m + 1)) :
    (cons x a : Fin (m + 1) → α) i = if hi : i ≠ 0 then a (i.pred hi) else x := by
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp

theorem Fin.snoc_nat (i : Fin (m + 1)) :
    (snoc a x : Fin (m + 1) → α) i = if hi : i < m then a ⟨i, hi⟩ else x := by
  cases i using Fin.lastCases with
  | last => simp
  | cast i => simp

theorem Fin.append_nat (i : Fin (m + n)) :
    append a b i = if hi : i < m then a ⟨i, hi⟩ else b ⟨i.val - m, by omega⟩ := by
  cases i using Fin.addCases with
  | left i => simp
  | right i => simp

@[simp]
theorem snoc_comp_castLE {n m : ℕ} {α : Sort*} (f : Fin n → α) (a : α) (h : m ≤ n) :
    (snoc f a : Fin _ → α) ∘ (castLE (le_succ_of_le h))  = f ∘ (castLE h) := by
  have : castLE (le_succ_of_le h) = castLE (le_succ _) ∘ castLE h := by
    rw [Fin.castLE_comp_castLE]
  simp [this, ← Function.comp_assoc]

@[simp]
theorem Fin.exists_fin_add {P : Fin (n + m) → Prop} :
    (∃ i, P i) ↔ (∃ i : Fin n, P (i.castAdd m)) ∨ (∃ i : Fin m, P (i.natAdd n)) := by
  constructor
  · intro ⟨i, hi⟩
    cases i using Fin.addCases with
    | left i => exact Or.inl ⟨i, hi⟩
    | right i => exact Or.inr ⟨i, hi⟩
  · grind

  -- ⟨fun ⟨i, h⟩ => Fin.lastCases Or.inr (fun i hi => Or.inl ⟨i, hi⟩) i h,
  --  fun h => h.elim (fun ⟨i, hi⟩ => ⟨i.castSucc, hi⟩) (fun h => ⟨.last _, h⟩)⟩

@[simp]
lemma Fin.range_append {α : Type*} (f : Fin n → α) (g : Fin m → α) :
    Set.range (append f g) = Set.range f ∪ Set.range g := by
  ext
  simp

@[simp]
theorem Fin.append_last (a : Fin m → α) (b : Fin (n + 1) → α) :
    append a b (last (m + n)) = b (last n) := by
  simp only [append, addCases, val_last, eq_rec_constant]
  split_ifs
  · omega
  · congr
    grind

@[simp]
theorem Fin.append_comp_append_castAdd (f : Fin p → Fin (m + n)) :
    append a b ∘ append (castAdd n) f = append a (append a b ∘ f) := by
  grind [append_nat]

@[simp]
theorem Fin.append_comp_snoc_castAdd (x : Fin (m + n)) :
    append a b ∘ snoc (castAdd n) x = snoc a (append a b x) := by
  simp only [snoc_eq_append, Nat.reduceAdd, append_comp_append_castAdd]
  congr 1
  ext i; fin_cases i; rfl

@[simp]
theorem Fin.append_comp_append_natAdd (f : Fin p → Fin (m + n)) :
    append a b ∘ append f (natAdd m) = append (append a b ∘ f) b := by
  grind [append_nat]

-- @[simp]
-- theorem Fin.append_comp_natAdd' {l : ℕ} (f : Fin l → Fin n) :
--     append a b ∘ (fun i ↦ natAdd m (f i)) = b ∘ f := by
--   grind [append_nat]

@[simp]
theorem Fin.append_comp_natAdd_comp {l : ℕ} (f : Fin l → Fin n) :
    append a b ∘ (natAdd m ∘ f) = b ∘ f := by
  grind [append_nat]

@[simp]
theorem Fin.append_append_comp_append_castAdd_castAdd_natAdd :
    append (append a b) c ∘ append (castAdd p ∘ castAdd n) (fun i ↦ natAdd (m + n) i) =
      append a c := by
  ext i
  simp only [Function.comp_apply, append_nat, castAdd_mk, natAdd_mk]
  by_cases hi : i.val < m
  · grind
  · have : ¬(m + n + (↑i - m) < m + n) := by omega
    simp [hi, this]
-- @[simp]
-- theorem Fin.append_append_comp_append_castAdd_append_natAdd_natAdd_natAdd_castAdd
-- append xs (append zs ys) ∘
--       append (castAdd (q + p)) (append (fun i ↦ natAdd n (natAdd q i)) fun i ↦ natAdd n (castAdd p i))

@[simp]
theorem Fin.append_comp_append_natAdd_castAdd :
    append b a ∘ append (natAdd n) (castAdd m) = append a b := by
  ext i
  simp only [Function.comp_apply, append_nat, natAdd_mk, castAdd_mk]
  grind

-- /-- `Fin.gap n n' m : Fin n → Fin (n + n')` is the function that is the identity on numbers `< m`,
-- and adds `n'` to numbers `≥ m` -/
-- def Fin.gap (n n' m : ℕ) (i : Fin n) : Fin (n + n') := if ↑i < m then castAdd n' i else addNat i n'

@[simp]
theorem Fin.insertNth_castSucc_snoc (k : Fin (n + 1)) (a y : α) (xs : Fin n → α) :
    (k.castSucc.insertNth y (snoc xs a) : Fin (n + 2) → α) = snoc (k.insertNth y xs) a := by
  ext i
  cases i using Fin.succAboveCases k.castSucc with
  | x => simp
  | p j =>
    simp only [insertNth_apply_succAbove]
    cases j using Fin.lastCases <;> simp

variable {n n' m : ℕ}

-- @[simp]
-- theorem Fin.append_append_gap (xs : Fin m → α) (ys : Fin n' → α) (zs : Fin n → α) :
--     (append xs (append ys zs) ∘ Fin.cast (by rw [Nat.add_assoc, Nat.add_comm n]))
--       ∘ (gap (m + n) n' m) = append xs zs := by
--   grind [gap, castAdd, append_nat]

-- @[simp]
-- theorem Fin.append_append_gap' (xs : Fin m → α) (ys : Fin n' → α) (zs : Fin n → α) :
--     (append (append xs ys) zs ∘ Fin.cast (by rw [Nat.add_assoc, Nat.add_comm n, Nat.add_assoc]))
--       ∘ (gap (m + n) n' m) = append xs zs := by
--   grind [gap, castAdd, append_nat]

-- @[simp]
-- theorem Fin.append_append_gap_zero (xs : Fin m → α) (ys : Fin n' → α) (zs : Fin n → α) :
--     (append (append ys xs) zs ∘ Fin.cast (add_rotate n' m n |>.symm))
--       ∘ (gap (m + n) n' 0) = append xs zs := by
--   grind [gap, castAdd, append_nat]

-- @[simp]
-- theorem Fin.gap_same (xs : Fin (n + n') → α) :
--     xs ∘ (gap n n' n) = xs ∘ (castLE (Nat.le_add_right n n')):= by
--   ext
--   simp [gap, castAdd]

-- @[simp]
-- theorem Fin.append_gap_same (xs : Fin n → α) (ys : Fin n' → α) :
--     (append xs ys) ∘ (gap n n' n) = xs := by
--   simp only [gap_same]
--   ext i
--   simp

-- @[simp]
-- theorem Fin.snoc_gap_same (xs : Fin n → α) (a : α) :
--     (snoc xs a) ∘ (gap n 1 n) = xs := by
--   simp

-- @[simp]
-- theorem Fin.gap_add_one (xs : Fin (n + 1 + n') → α) :
--     xs ∘ (gap (n + 1) n' n) = snoc (xs ∘ (castLE (le_add_right_of_le (le_succ _))))
--       (xs (⟨n + n', Nat.add_lt_add_right (Nat.lt_add_one n) n'⟩)) := by
--   ext i
--   simp only [Function.comp_apply, gap, castAdd, castLE, addNat, snoc_nat]
--   grind

@[simp]
theorem Fin.snoc_snoc_castAdd_one_last {n : ℕ} (xs : Fin n → α) (a : α) :
    ((snoc (snoc xs x) a) : Fin (n + 2) → α) ((last n).castAdd 1) = x := by
  grind [snoc_nat]

@[simp]
theorem Fin.snoc_snoc_comp_snoc_castAdd_two_last (xs : Fin n → α) (x a : α) :
    (snoc (snoc xs x) a) ∘ snoc (castAdd 2) (last _) = snoc xs a := by
  grind [snoc_nat]

@[simp]
theorem Fin.snoc_snoc_comp_cons_last_castAdd_two (xs : Fin n → α) (x a : α) :
    snoc (snoc xs x) a ∘ cons (last _) (castAdd 2) = cons a xs := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [Function.comp_apply, cons_succ, snoc_castAdd]
    convert snoc_castSucc (α := fun _ ↦ α) _ _ _
    simp [castSucc]


-- @[simp]
-- theorem Fin.snoc_append_snoc_gap_add_one (vs : Fin m → α) (xs₀ : Fin n → α) (x a : α) :
--     (snoc (append vs (snoc xs₀ x)) a ∘ gap (m + (n + 1)) 1 (m + n)) = append vs (snoc xs₀ a) := by
--   ext i
--   simp only [Function.comp_apply, gap, addNat_one, snoc_nat, append_nat]
--   split_ifs <;> grind

-- @[simp]
-- theorem Fin.snoc_append_gap_add_one (vs : Fin m → α) (xs : Fin (n + 1) → α) (a : α) :
--     (snoc (append vs xs) a) ∘ (gap (m + (n + 1)) 1 (m + n)) = append vs (snoc (init xs) a) := by
--   nth_rw 1 [← snoc_init_self xs]
--   rw [snoc_append_snoc_gap_add_one]

-- @[simp]
-- theorem Fin.snoc_snoc_gap_add_one (xs : Fin n → α) (x a : α) :
--     (snoc (snoc xs x) a) ∘ (gap (n + 1) 1 n) = snoc xs a := by
--   grind [gap, snoc_nat]

-- @[simp]
-- theorem snoc_comp_castSucc : snoc a x ∘ Fin.castSucc = a := by
--   simp
--   -- simp only [snoc, val_castSucc, is_lt, dite_true]
--   -- convert cast_eq rfl (p i)
