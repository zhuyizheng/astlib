/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.Data.Fin.Tuple.Basic
/-!
# Quantifying over tuples by their last entry

Versions of `Fin.forall_fin_succ_pi` and `Fin.exists_fin_succ_pi` with `Fin.snoc` in place of
`Fin.cons`.
-/

namespace Fin

variable {n : ℕ} {α : Fin (n + 1) → Sort*}

theorem forall_fin_succ_pi' {P : (∀ i, α i) → Prop} :
    (∀ x, P x) ↔ ∀ v a, P (Fin.snoc v a) :=
  ⟨fun h v a ↦ h (Fin.snoc v a), snocCases⟩

theorem exists_fin_succ_pi' {P : (∀ i, α i) → Prop} :
    (∃ x, P x) ↔ ∃ v a, P (Fin.snoc v a) :=
  ⟨fun ⟨x, h⟩ ↦ ⟨init x, x (last n), (snoc_init_self x).symm ▸ h⟩, fun ⟨_, _, h⟩ ↦ ⟨_, h⟩⟩

end Fin
