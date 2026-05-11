import Mathlib.Data.Fin.Tuple.Basic

variable {α : Type*} {m n p : ℕ} (a : Fin m → α) (b : Fin n → α) (c : Fin p → α)

open Fin

theorem Fin.append_nat (i : Fin (m + n)) :
    append a b i = if hi : i < m then a ⟨i, hi⟩ else b ⟨i.val - m, by omega⟩ := by
  split_ifs with hi
  · nth_rw 1 [show i = Fin.castAdd n ⟨i.val, hi⟩ by simp]
    rw [append_left]
  · nth_rw 1 [show i = Fin.natAdd (m := n) m ⟨(i.val - m), by omega⟩ by grind]
    rw [append_right]
