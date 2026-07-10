/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Mathlib.ModelTheory.Semantics
import Astlib.ModelTheory.Defs
import Astlib.Mathlib.Fin.Basic
import Astlib.Mathlib.Sum.Basic
/-!
file docstring
-/

open Fin

namespace FirstOrder

namespace Language

variable {m n : ℕ} {M : MemStructure} {α : Type u'}
  (t : M.L.Term (α ⊕ Fin n)) (φ : M.L.BoundedFormula α (n + 1))
  {v : α → M} {xs : Fin n → M}

namespace BoundedFormula

@[simp]
theorem realize_allMem :
    (∀'∈ t φ)〘v, xs〙 ↔ ∀ a ∈ t〘v, xs〙, φ〘v, snoc xs a〙 := by
  simp [allMem, Term.realize']

@[simp]
theorem realize_exMem :
    (∃'∈ t φ)〘v, xs〙 ↔ ∃ a ∈ t〘v, xs〙, φ〘v, snoc xs a〙 := by
  simp [exMem, Term.realize']

-- @[simp]
-- theorem realize_ex' :
--     (θ.ex' m)〘v, xs〙 ↔ ∃ ys : Fin m → M, θ.Realize v (append xs ys) := by
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
