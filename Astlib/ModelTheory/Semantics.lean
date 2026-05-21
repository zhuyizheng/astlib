import Astlib.Mathlib.ModelTheory.Semantics
import Astlib.ModelTheory.Defs
import Astlib.Mathlib.Fin.Basic
import Astlib.Mathlib.Sum.Basic

open Fin

namespace FirstOrder

namespace Language

variable {m n} {M : MemStructure} {α : Type u'}
  (t : M.L.Term (α ⊕ Fin n)) (φ : M.L.BoundedFormula α (n + 1))
  {v : α → M} {xs : Fin n → M}

namespace BoundedFormula

@[simp]
theorem realize_allMem :
    (∀'∈ t φ).Realize v xs ↔ ∀ a ∈ t.realize' v xs, φ.Realize v (snoc xs a) := by
  simp

@[simp]
theorem realize_exMem :
    (∃'∈ t φ).Realize v xs ↔ ∃ a ∈ t.realize' v xs, φ.Realize v (snoc xs a) := by
  simp

-- @[simp]
-- theorem realize_ex' :
--     (θ.ex' m).Realize v xs ↔ ∃ ys : Fin m → M, θ.Realize v (append xs ys) := by
--   induction m with
--   | zero => simp [append_right_nil]
--   | succ m ih =>
--     simp only [ex'_succ, ih, realize_ex]
--     refine ⟨fun ⟨ys, a, h⟩ ↦ ⟨snoc ys a, ?_⟩, fun ⟨zs, h⟩ ↦ ⟨init zs, zs (last _), ?_⟩⟩
--     · simpa [append_snoc]
--     · simpa [← append_snoc]



end BoundedFormula

end Language

end FirstOrder
