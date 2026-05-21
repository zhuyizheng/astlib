import Mathlib.Data.Fin.Tuple.Basic

variable {α : Type*} {m n p : ℕ} (a : Fin m → α) (b : Fin n → α) (c : Fin p → α) (x : α)

open Fin

@[simp]
theorem Fin.castLE_succ_castSucc (n : ℕ) : Fin.castLE n.le_succ = Fin.castSucc := by rfl

theorem Fin.castLE_add_two_castSucc (n : ℕ) : Fin.castLE (n := n) (m := n + 2) (by omega) =
    Fin.castSucc ∘ Fin.castSucc := by rfl

theorem Fin.castLE_add_three_castSucc (n : ℕ) : Fin.castLE (n := n) (m := n + 3) (by omega) =
    Fin.castSucc ∘ Fin.castSucc ∘ Fin.castSucc := by rfl

theorem Fin.castLE_add_four_castSucc (n : ℕ) : Fin.castLE (n := n) (m := n + 4) (by omega) =
    Fin.castSucc ∘ Fin.castSucc ∘ Fin.castSucc ∘ Fin.castSucc := by rfl

@[simp]
theorem Fin.val_last_plus_one_minus_one : (last (n + 1) - 1).val = n := by
    simp only [last, sub_def, coe_ofNat_eq_mod, Nat.one_mod, Nat.add_one_sub_one]
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


theorem Fin.snoc_nat (i : Fin (m + 1)) :
    (snoc a x : Fin (m + 1) → α) i = if hi : i < m then a ⟨i, hi⟩ else x := by
  split_ifs with hi
  · nth_rw 1 [show i = Fin.castSucc ⟨i.val, hi⟩ by simp]
    rw [snoc_castSucc]
  · convert snoc_last (α := fun _ ↦ α) x a
    grind

theorem Fin.append_nat (i : Fin (m + n)) :
    append a b i = if hi : i < m then a ⟨i, hi⟩ else b ⟨i.val - m, by omega⟩ := by
  split_ifs with hi
  · nth_rw 1 [show i = Fin.castAdd n ⟨i.val, hi⟩ by simp]
    rw [append_left]
  · nth_rw 1 [show i = Fin.natAdd (m := n) m ⟨(i.val - m), by omega⟩ by grind]
    rw [append_right]



-- @[simp]
-- theorem snoc_comp_castSucc : snoc a x ∘ Fin.castSucc = a := by
--   simp
--   -- simp only [snoc, val_castSucc, is_lt, dite_true]
--   -- convert cast_eq rfl (p i)
