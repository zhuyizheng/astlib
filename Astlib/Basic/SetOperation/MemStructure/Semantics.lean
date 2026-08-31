/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Mathlib.ModelTheory.Semantics
import Astlib.Basic.SetOperation.MemStructure.Defs
import Astlib.Mathlib.Fin.Basic
import Astlib.Mathlib.Sum.Basic
/-!
file docstring
-/

open Fin

namespace FirstOrder

namespace Language

variable {m n : ℕ} {M : MemStructure}
  (t : M.L.Term' n) (φ : M.L.BoundedFormula' (n + 1))
  {xs : Fin n → M}

namespace BoundedFormula

@[simp]
theorem realize_allMem :
    (∀'∈ t φ)〘xs〙 ↔ ∀ a ∈ t〘xs〙, φ〘snoc xs a〙 := by
  simp [allMem]

@[simp]
theorem realize_exMem :
    (∃'∈ t φ)〘xs〙 ↔ ∃ a ∈ t〘xs〙, φ〘snoc xs a〙 := by
  simp [exMem]

end BoundedFormula

end Language

end FirstOrder
