import Mathlib.Data.Fin.Tuple.Basic

variable {α : Type*} {m n p : ℕ} (a : Fin m → α) (b : Fin n → α) (c : Fin p → α)

open Fin

@[simp]
theorem Fin.val_last_plus_one_minus_one : (last (n + 1) - 1).val = n := by
    simp only [last, sub_def, coe_ofNat_eq_mod, Nat.one_mod, Nat.add_one_sub_one]
    rw [Nat.mod_eq_sub_mod (by omega)]
    convert Nat.mod_eq_of_lt ?_ <;> grind


theorem Fin.append_nat (i : Fin (m + n)) :
    append a b i = if hi : i < m then a ⟨i, hi⟩ else b ⟨i.val - m, by omega⟩ := by
  split_ifs with hi
  · nth_rw 1 [show i = Fin.castAdd n ⟨i.val, hi⟩ by simp]
    rw [append_left]
  · nth_rw 1 [show i = Fin.natAdd (m := n) m ⟨(i.val - m), by omega⟩ by grind]
    rw [append_right]
