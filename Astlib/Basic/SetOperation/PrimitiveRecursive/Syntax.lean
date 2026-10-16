/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Rudimentary.Syntax
import Astlib.Basic.Axiom.KP.SigmaOneBoundedFormula.Syntax
import Astlib.Basic.SetOperation.Function
import Astlib.Basic.Ordinal.Transitive
/-!
file docstring
-/
open FirstOrder Language BoundedFormula Fin Term BoundedFormula


namespace FirstOrder.Language

variable {L : FirstOrder.Language.{u, v}} [L.HasMem]
--  [L.ExtraConstantsUnaryRelationsOnly]
  -- [L.ExtraConstantsOnly]

inductive PrimitiveRecursiveTerm [L.HasMem] : ℕ → Type max u v
  | var : Fin n → PrimitiveRecursiveTerm n
  | const (c : L.Constants) : PrimitiveRecursiveTerm n
  | unorderedPair (r₁ r₂ : PrimitiveRecursiveTerm n) : PrimitiveRecursiveTerm n
  | sdiff (r₁ r₂ : PrimitiveRecursiveTerm n) : PrimitiveRecursiveTerm n
  | iUnion (ri : PrimitiveRecursiveTerm n) (rf : PrimitiveRecursiveTerm (n + 1)) :
    PrimitiveRecursiveTerm n
  | char (R : L.Relations 1) (r : PrimitiveRecursiveTerm n) : PrimitiveRecursiveTerm n
  | recursion (rg : PrimitiveRecursiveTerm (n + 1)) : PrimitiveRecursiveTerm (n + 1)

@[inherit_doc] scoped[FirstOrder] prefix:110 "ₚᵣ" => FirstOrder.Language.PrimitiveRecursiveTerm.var

/-- The largest index of the bounded variables -/
scoped[FirstOrder] notation "ₚᵣ-1" => ₚᵣ(last _)

/-- The second largest index of the bounded variables -/
scoped[FirstOrder] notation "ₚᵣ-2" => ₚᵣ(castAdd 1 (last _))

/-- The third largest index of the bounded variables -/
scoped[FirstOrder] notation "ₚᵣ-3" => ₚᵣ(castAdd 2 (last _))

/-- The fourth largest index of the bounded variables -/
scoped[FirstOrder] notation "ₚᵣ-4" => ₚᵣ(castAdd 3 (last _))

@[inherit_doc] scoped[FirstOrder] notation:max "ₚᵣ{" x ", " y "}" =>
  FirstOrder.Language.PrimitiveRecursiveTerm.unorderedPair x y

instance : SDiff (L.PrimitiveRecursiveTerm n) := ⟨PrimitiveRecursiveTerm.sdiff⟩

instance : Singleton (L.PrimitiveRecursiveTerm n) (L.PrimitiveRecursiveTerm n) :=
  ⟨fun r ↦ ₚᵣ{r, r}⟩


/-- Every rudimentary term is a primitive recursive term -/
def RudimentaryTerm.toPrimitiveRecursiveTerm {n} : L.RudimentaryTerm n → L.PrimitiveRecursiveTerm n
  | .var i => .var i
  | .const c => .const c
  | .unorderedPair r₁ r₂ => .unorderedPair r₁.toPrimitiveRecursiveTerm r₂.toPrimitiveRecursiveTerm
  | .sdiff r₁ r₂ => .sdiff r₁.toPrimitiveRecursiveTerm r₂.toPrimitiveRecursiveTerm
  | .iUnion ri rf => .iUnion ri.toPrimitiveRecursiveTerm rf.toPrimitiveRecursiveTerm
  | .char R r => .char R r.toPrimitiveRecursiveTerm

namespace Term

open RudimentaryTerm
-- -- open L.DeltaZeroBoundedFormula
variable [L.ExtraConstantsUnaryRelationsOnly]

/-- A term is turned into a primitive recursive term via a rudimentary term -/
noncomputable def toPrimitiveRecursiveTerm {n} (t : L.Term' n) : L.PrimitiveRecursiveTerm n :=
  t.toRudimentaryTerm.toPrimitiveRecursiveTerm

end Term

namespace PrimitiveRecursiveTerm

variable [L.ExtraConstantsUnaryRelationsOnly]

/-- The `Σ₁` formula `t = p(ts)`, where `p` is a primitive recursive term in `n` variables,
and `t` and `ts` are terms in `m` variables.

* `iUnion ri rf`: there are `a` and a function `f` such that `a = ri(ts)`, `dom f = a`,
  `f ﹫ y = rf(ts, y)` for all `y ∈ a`, and `t = ⋃₀ ran f`.
* `recursion rg`: there is a function `f` whose domain `d` is transitive and contains the last
  entry `x` of `ts`, such that `f ﹫ y = rg(ts', f ↾ y)` for all `y ∈ d` (where `ts'` is `ts`
  without its last entry), and `t = f ﹫ x`. -/
noncomputable def eqRealize {n : ℕ} (p : L.PrimitiveRecursiveTerm n) {m : ℕ} (t : L.Term' m)
  (ts : Fin n → L.Term' m) : L.SigmaOneBoundedFormula m :=
  match p with
  | var i => (t =₀ ts i).toSigmaOneBoundedFormula
  | const c => (t =₀ c.term).toSigmaOneBoundedFormula
  | unorderedPair r₁ r₂ =>
    -- `∃ y₁ y₂, y₁ = r₁(ts) ∧ y₂ = r₂(ts) ∧ t = {y₁, y₂}`
    ∃₁ ∃₁ (
      r₁.eqRealize &-2 (fun i ↦ (ts i).castAdd 2) ⊓
      r₂.eqRealize &-1 (fun i ↦ (ts i).castAdd 2) ⊓
      ((&0 =₀ &1).substBoundRud
        ![(t.castAdd 2).toRudimentaryTerm, ᵣ{ᵣ-2, ᵣ-1}]).toSigmaOneBoundedFormula)
  | sdiff r₁ r₂ =>
    -- `∃ y₁ y₂, y₁ = r₁(ts) ∧ y₂ = r₂(ts) ∧ t = y₁ \ y₂`
    ∃₁ ∃₁ (
      r₁.eqRealize &-2 (fun i ↦ (ts i).castAdd 2) ⊓
      r₂.eqRealize &-1 (fun i ↦ (ts i).castAdd 2) ⊓
      ((&0 =₀ &1).substBoundRud
        ![(t.castAdd 2).toRudimentaryTerm, ᵣ-2 \ ᵣ-1]).toSigmaOneBoundedFormula)
  | iUnion ri rf =>
    -- `∃ a f, a = ri(ts) ∧ IsFunction f ∧ dom f = a ∧`
    -- `(∀ y ∈ a, ∃ z, z = rf(ts, y) ∧ z = f ﹫ y) ∧ t = ⋃₀ ran f`
    ∃₁ ∃₁ (
      ri.eqRealize &-2 (fun i ↦ (ts i).castAdd 2) ⊓
      ((ᵣ-1).isFunction ⊓
        (&0 =₀ &1).substBoundRud ![(ᵣ-1).dom, ᵣ-2]).toSigmaOneBoundedFormula ⊓
      (∀₁∈ &-2 ∃₁ (
        rf.eqRealize &-1 (snoc (fun i ↦ (ts i).castAdd 4) &-2) ⊓
        ((&0 =₀ &1).substBoundRud ![ᵣ-1, ᵣ-3 ﹫ ᵣ-2]).toSigmaOneBoundedFormula)) ⊓
      ((&0 =₀ &1).substBoundRud
        ![(t.castAdd 2).toRudimentaryTerm, ᵣ⋃₀ (ᵣ-1).ran]).toSigmaOneBoundedFormula)
  | char R r =>
    -- `∃ y, y = r(ts) ∧ ((R y ∧ t = {∅, ∅}) ∨ (¬R y ∧ t = ∅))`
    ∃₁ (
      r.eqRealize &-1 (fun i ↦ (ts i).castSucc) ⊓
      ((.rel R &-1 ⊓
          (&0 =₀ &1).substBoundRud ![t.castSucc.toRudimentaryTerm, ᵣ{∅, ∅}]) ⊔
        (∼(.rel R &-1) ⊓
          (&0 =₀ &1).substBoundRud ![t.castSucc.toRudimentaryTerm, ∅])).toSigmaOneBoundedFormula)
  | recursion rg =>
    -- `∃ f d, IsFunction f ∧ d = dom f ∧ Transitive d ∧ x ∈ d ∧`
    -- `(∀ y ∈ d, ∃ z w, z = rg(ts', w) ∧ z = f ﹫ y ∧ w = f ↾ y) ∧ t = f ﹫ x`
    ∃₁ ∃₁ (
      ((ᵣ-2).isFunction ⊓
        (&0 =₀ &1).substBoundRud ![ᵣ-1, (ᵣ-2).dom] ⊓
        (ᵣ-1).isTransitive ⊓
        (&0 ∈₀ &1).substBoundRud
          ![((ts (last _)).castAdd 2).toRudimentaryTerm, ᵣ-1]).toSigmaOneBoundedFormula ⊓
      (∀₁∈ &-1 ∃₁ ∃₁ (
        rg.eqRealize &-2 (snoc (fun i ↦ (ts i.castSucc).castAdd 5) &-1) ⊓
        ((&0 =₀ &1).substBoundRud ![ᵣ-2, (.var (castAdd 4 (last _))) ﹫ ᵣ-3] ⊓
          (&0 =₀ &1).substBoundRud
            ![ᵣ-1, (.var (castAdd 4 (last _))) ↾ ᵣ-3]).toSigmaOneBoundedFormula)) ⊓
      ((&0 =₀ &1).substBoundRud
        ![(t.castAdd 2).toRudimentaryTerm,
          ᵣ-2 ﹫ ((ts (last _)).castAdd 2).toRudimentaryTerm]).toSigmaOneBoundedFormula)

end PrimitiveRecursiveTerm

end Language

end FirstOrder
