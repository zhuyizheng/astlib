/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Order.Basic
import Astlib.Basic.SetOperation.Function.Restrict
/-!
# The Brouwer–Kleene order

`BKLt R s t`: the Brouwer–Kleene order on finite sequences with coordinates ordered by `R`, the
lexicographic order in which a proper extension is smaller.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M]

/-- The Brouwer–Kleene order on finite sequences with coordinates ordered by `R`: `s` is below
`t` if `s` properly extends `t`, or `s` and `t` first differ at some `k` with `s(k) R t(k)` -/
def BKLt (R s t : M) : Prop :=
  (t ⊆ s ∧ t ≠ s) ∨ ∃ k ∈ dom s, k ∈ dom t ∧ s ↾ k = t ↾ k ∧ (s ﹫ k) [R] (t ﹫ k)

end FirstOrder.Language.MemStructure
