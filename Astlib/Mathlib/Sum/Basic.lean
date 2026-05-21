import Init.Data.Sum.Basic

import Astlib.Mathlib.Fin.Basic

-- variable (α β : Type* )

@[simp]
theorem Sum.elim_comp_map_castSucc (v : α → β) (xs : Fin n → β) (a : β) :
    Sum.elim v (Fin.snoc xs a) ∘ Sum.map id (Fin.castSucc) = Sum.elim v xs := by
  grind [Fin.snoc_castSucc]

@[simp]
theorem Sum.elim_comp_map_castSucc_comp (v : α → β) (xs : Fin n → β) (a : β) :
    Sum.elim v (Fin.snoc xs a) ∘ Sum.map id (Fin.castSucc ∘ f) = Sum.elim v (xs ∘ f) := by
  grind [Fin.snoc_castSucc]
