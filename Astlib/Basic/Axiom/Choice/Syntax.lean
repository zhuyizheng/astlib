/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Axiom.ZF.Syntax
import Astlib.Basic.Ordinal.Omega
/-!
# The axiom of choice

* `choiceAxiom` says that every function `F` has a choice function, picking an element of each
  nonempty `F ﹫ x`, and `ZFC` is `ZF` with the axiom of choice.
* `countableChoiceAxiom` says that every function `F` with `dom F = ω` has a choice function,
  and `ZFCC` is `ZF` with countable choice.
* `dependentChoiceAxiom` says that if every element of a nonempty set `a` has an `R`-successor in
  `a`, then there is a sequence `f !: ω → a` with `f ﹫ n [R] f ﹫ succ n`, and `ZFDC` is `ZF` with
  dependent choice.
-/

namespace FirstOrder.Language

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin RudimentaryTerm

variable {L : FirstOrder.Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]

/-- The `Δ₀` formula saying that if `F` is a function, then `f` is a function on `dom F` with
`f ﹫ x ∈ F ﹫ x` whenever `F ﹫ x` is nonempty -/
noncomputable def isChoiceFunctionOfIsFunction : L.DeltaZeroBoundedFormula 2 :=
  -- `[F, f]`
  (ᵣ0).isFunction ⟹
    ((ᵣ1).isFunction ⊓ (&0 =₀ &1).substBoundRud ![(ᵣ1).dom, (ᵣ0).dom] ⊓
      -- `[d, F, f]` with `d = dom F`; for `x ∈ d`, `F ﹫ x ≠ ∅ → f ﹫ x ∈ F ﹫ x`
      (∀₀∈ &0 ((∃₀∈ &0 ⊤ : L.DeltaZeroBoundedFormula 1).substBoundRud ![(ᵣ1) ﹫ (ᵣ3)] ⟹
        (&0 ∈₀ &1).substBoundRud ![(ᵣ2) ﹫ (ᵣ3), (ᵣ1) ﹫ (ᵣ3)]) :
        L.DeltaZeroBoundedFormula 3).substBoundRud ![(ᵣ0).dom, ᵣ0, ᵣ1])

/-- The axiom of choice: every function `F` has a choice function, picking an element of each
nonempty `F ﹫ x` -/
noncomputable def choiceAxiom : L.Sentence :=
  ∀' ∃' (isChoiceFunctionOfIsFunction : L.DeltaZeroBoundedFormula 2).toBoundedFormula

/-- The theory `ZFC` -/
noncomputable def ZFC : L.Theory := ZF ∪ {choiceAxiom}

theorem ZF_subset_ZFC : (ZF : L.Theory) ⊆ ZFC := Set.subset_union_left

/-- The axiom of countable choice: every function `F` with `dom F = ω` has a choice function -/
noncomputable def countableChoiceAxiom : L.Sentence :=
  -- `[F, w]` with `w = ω = dom F`, and `[F, f]`
  ∀' ((∃' ((ᵣ1).isOmega ⊓ (&0 =₀ &1).substBoundRud ![(ᵣ0).dom, ᵣ1] :
    L.DeltaZeroBoundedFormula 2).toBoundedFormula) ⟹
      ∃' (isChoiceFunctionOfIsFunction : L.DeltaZeroBoundedFormula 2).toBoundedFormula)

/-- The theory `ZF` with countable choice -/
noncomputable def ZFCC : L.Theory := ZF ∪ {countableChoiceAxiom}

theorem ZF_subset_ZFCC : (ZF : L.Theory) ⊆ ZFCC := Set.subset_union_left

/-- The axiom of dependent choice: if every element of a nonempty set `a` has an `R`-successor in
`a`, then there is a sequence `f !: ω → a` with `f ﹫ n [R] f ﹫ succ n` -/
noncomputable def dependentChoiceAxiom : L.Sentence :=
  -- `[a, R]`: `a ≠ ∅` and every `x ∈ a` has some `y ∈ a` with `x [R] y`
  ∀' ∀' (((∃₀∈ &0 ⊤) ⊓ ∀₀∈ &0 ∃₀∈ &0 (&0 ∈₀ &1).substBoundRud ![ᵣ(ᵣ2, ᵣ3), ᵣ1] :
    L.DeltaZeroBoundedFormula 2).toBoundedFormula ⟹
      -- `[a, R, f, w]`: if `w = ω`, then `f !: w → a` and `f ﹫ n [R] f ﹫ succ n` for `n ∈ w`
      ∃' ∀' ((ᵣ3).isOmega ⟹ ((ᵣ2).isFunctionFromTo (ᵣ3) (ᵣ0) ⊓
        ∀₀∈ &3 (&0 ∈₀ &1).substBoundRud ![ᵣ((ᵣ2) ﹫ (ᵣ4), (ᵣ2) ﹫ (ᵣ4).succ), ᵣ1]) :
          L.DeltaZeroBoundedFormula 4).toBoundedFormula)

/-- The theory `ZF` with dependent choice -/
noncomputable def ZFDC : L.Theory := ZF ∪ {dependentChoiceAxiom}

theorem ZF_subset_ZFDC : (ZF : L.Theory) ⊆ ZFDC := Set.subset_union_left

end FirstOrder.Language
