/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.PrimitiveRecursive.Semantics
import Astlib.Basic.Ordinal.Basic
/-!
# Recursion on ordinals

* `ordRecursion rg`: `F(xs, α) = rg(xs, F(xs, ·) ↾ α)` for ordinals `α`, and `F(xs, x) = ∅` for
  non-ordinals `x`.
* `ordRecursion' r₀ rs rl`: recursion on ordinals given by the value `r₀(xs)` at `0`, the value
  `rs(xs, β, F(xs, β))` at `succ β`, and the value `rl(xs, F(xs, ·) ↾ α)` at a limit `α`.
-/
open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula PrimitiveRecursiveTerm Fin
  MemStructure

namespace FirstOrder.Language

namespace PrimitiveRecursiveTerm

section Syntax

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] {n : ℕ}

/-- Recursion on ordinals: `F(xs, α) = rg(xs, F(xs, ·) ↾ α)` for ordinals `α`, and `F(xs, x) = ∅`
for non-ordinals `x` -/
noncomputable def ordRecursion (rg : L.PrimitiveRecursiveTerm (n + 1)) :
    L.PrimitiveRecursiveTerm (n + 1) :=
  recursion (rg.ifTrue (ᵣ-1).dom.isOrdinal)

/-- The step of `ordRecursion' r₀ rs rl` on `f = F(xs, ·) ↾ α`: `r₀(xs)` if `α = 0`,
`rs(xs, β, f ﹫ β)` if `α = succ β`, and `rl(xs, f)` if `α` is a nonzero limit -/
noncomputable def ordRecursionStep' (r₀ : L.PrimitiveRecursiveTerm n)
    (rs : L.PrimitiveRecursiveTerm (n + 2)) (rl : L.PrimitiveRecursiveTerm (n + 1)) :
    L.PrimitiveRecursiveTerm (n + 1) :=
  r₀.castSucc.ifTrue (ᵣ-1).dom.isZero ∪
    (rs.substBoundPR (snoc (snoc (fun i ↦ ₚᵣ(i.castSucc)) (ᵣ⋃₀ (ᵣ-1).dom).toPrimitiveRecursiveTerm)
      ((ᵣ-1) ﹫ ᵣ⋃₀ (ᵣ-1).dom).toPrimitiveRecursiveTerm)).ifTrue (ᵣ-1).dom.isSuccOrdinal ∪
    rl.ifTrue (ᵣ-1).dom.isNonZeroLimOrdinal

/-- Recursion on ordinals with value `r₀(xs)` at `0`, `rs(xs, β, F(xs, β))` at `succ β`, and
`rl(xs, F(xs, ·) ↾ α)` at a nonzero limit `α` -/
noncomputable def ordRecursion' (r₀ : L.PrimitiveRecursiveTerm n)
    (rs : L.PrimitiveRecursiveTerm (n + 2)) (rl : L.PrimitiveRecursiveTerm (n + 1)) : L.PrimitiveRecursiveTerm (n + 1) :=
  ordRecursion (ordRecursionStep' r₀ rs rl)

end Syntax

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] {n : ℕ}

theorem realize_ordRecursion (rg : L.PrimitiveRecursiveTerm (n + 1)) (xs : Fin n → M) (x : M) :
    (ordRecursion rg)〘snoc xs x〙 = if Ordinal x then
      rg〘snoc xs ((fun y ↦ (ordRecursion rg)〘snoc xs y〙) ↾₀ x)〙 else ∅ := by
  rw [ordRecursion, realize_recursion]
  simp [isSetRestrictedTo]

@[simp]
theorem realize_ordRecursion_of_not_ordinal (rg : L.PrimitiveRecursiveTerm (n + 1))
    (xs : Fin n → M) {x : M} (hx : ¬Ordinal x) : (ordRecursion rg)〘snoc xs x〙 = ∅ := by
  rw [realize_ordRecursion, if_neg hx]

@[simp]
theorem realize_ordRecursion_of_ordinal (rg : L.PrimitiveRecursiveTerm (n + 1))
    (xs : Fin n → M) {x : M} (hx : Ordinal x) :
    (ordRecursion rg)〘snoc xs x〙 = rg〘snoc xs ((fun y ↦ (ordRecursion rg)〘snoc xs y〙) ↾₀ x)〙 := by
  rw [realize_ordRecursion, if_pos hx]

variable (r₀ : L.PrimitiveRecursiveTerm n) (rs : L.PrimitiveRecursiveTerm (n + 2))
  (rl : L.PrimitiveRecursiveTerm (n + 1)) (xs : Fin n → M)

@[simp]
theorem realize_ordRecursion'_zero : (ordRecursion' r₀ rs rl)〘snoc xs ∅〙 = r₀〘xs〙 := by
  simp only [ordRecursion', realize_ordRecursion_of_ordinal, ordinal_empty, ordRecursionStep']
  simp [isSetRestrictedTo]

@[simp]
theorem realize_ordRecursion'_succ {β : M} (hβ : Ordinal β) :
    (ordRecursion' r₀ rs rl)〘snoc xs (succ β)〙 =
      rs〘snoc (snoc xs β) (ordRecursion' r₀ rs rl)〘snoc xs β〙〙 := by
  simp only [ordRecursion', realize_ordRecursion_of_ordinal, ordinal_succ, hβ, ordRecursionStep']
  simp [isSetRestrictedTo, hβ]

@[simp]
theorem realize_ordRecursion'_limit {α : M} (hα : NonZeroLimOrdinal α) :
    (ordRecursion' r₀ rs rl)〘snoc xs α〙 =
      rl〘snoc xs ((fun y ↦ (ordRecursion' r₀ rs rl)〘snoc xs y〙) ↾₀ α)〙 := by
  simp only [ordRecursion', realize_ordRecursion_of_ordinal, hα.ordinal, ordRecursionStep']
  simp [isSetRestrictedTo, hα, hα.ne_empty, hα.not_succOrdinal]

@[simp]
theorem realize_ordRecursion'_of_not_ordinal {x : M} (hx : ¬Ordinal x) :
    (ordRecursion' r₀ rs rl)〘snoc xs x〙 = ∅ :=
  realize_ordRecursion_of_not_ordinal _ _ hx

end PrimitiveRecursiveTerm

end FirstOrder.Language
