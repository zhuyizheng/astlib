/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.MemStructure.Levy
import Astlib.Basic.SetOperation.Rudimentary.Syntax
import Astlib.Basic.SetOperation.Pair.Syntax
import Astlib.Basic.SetOperation.Rudimentary.Basis.Semantics
/-!
file docstring
-/

open FirstOrder Language BoundedFormula Theory Fin

variable {L : FirstOrder.Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]

namespace FirstOrder

namespace Language

/-- `Σ₁` bounded formulas in `L` -/
structure SigmaOneBoundedFormula [L.HasMem] (n : ℕ) where
  deltaZeroBody : L.DeltaZeroBoundedFormula (n + 1)

/-- Merging the last two variables `y₁, y₂` of `φ` into one variable `p`:
`∃ y₁ y₂ ∈ ⋃₀ p, p = (y₁, y₂) ∧ φ (..., y₁, y₂)` -/
def DeltaZeroBoundedFormula.mergeLastTwo (φ : L.DeltaZeroBoundedFormula (n + 2)) :
    L.DeltaZeroBoundedFormula (n + 1) :=
  ∃₀∈⋃₀ &-1 ∃₀∈⋃₀ &-2 ((&-3).eqOrderedPair &-2 &-1 ⊓
    φ.substBoundBound (snoc (snoc (castAdd 3) (last _).castSucc) (last _)))

/-- Merging the last `m + 1` variables `y₀, …, yₘ` of `φ` into one variable, the tuple
`p = ((y₀, y₁), …, yₘ)` -/
def DeltaZeroBoundedFormula.mergeLast :
    ∀ {n : ℕ} (m : ℕ), L.DeltaZeroBoundedFormula (n + m + 1) → L.DeltaZeroBoundedFormula (n + 1)
  | _, 0, φ => φ
  | n, m + 1, φ =>
    -- move `yₘ₊₁` in front of `y₀`, merge `y₀, …, yₘ` into `p'`, and merge `p'` with `yₘ₊₁`
    ((mergeLast m (φ.substBoundBound
      (snoc (append (fun i ↦ castAdd (m + 1) i.castSucc) (natAdd (n + 1)))
        (castAdd (m + 1) (last n))))).substBoundBound
      (snoc (snoc (castAdd 2) (last (n + 1))) (last n).castSucc)).mergeLastTwo

def DeltaZeroBoundedFormula.toSigmaOneBoundedFormula (φ : L.DeltaZeroBoundedFormula n) :
  L.SigmaOneBoundedFormula n :=
  ⟨φ.substBoundBound castSucc⟩

namespace SigmaOneBoundedFormula

def toBoundedFormula (φ : L.SigmaOneBoundedFormula n) : L.BoundedFormula' n :=
  ∃' φ.deltaZeroBody.toBoundedFormula

instance : Coe (L.SigmaOneBoundedFormula n) (L.BoundedFormula' n) := ⟨toBoundedFormula⟩

def sup (φ ψ : L.SigmaOneBoundedFormula n) : L.SigmaOneBoundedFormula n :=
  ⟨φ.deltaZeroBody ⊔ ψ.deltaZeroBody⟩

/-- `φ ∧ ψ`: the witness is the pair of the witnesses of `φ` and `ψ` -/
def inf (φ ψ : L.SigmaOneBoundedFormula n) : L.SigmaOneBoundedFormula n :=
  ⟨(φ.deltaZeroBody.substBoundBound castSucc ⊓
    ψ.deltaZeroBody.substBoundBound (snoc (castAdd 2) (last _))).mergeLastTwo⟩

instance : Max (L.SigmaOneBoundedFormula n) := ⟨sup⟩

instance : Min (L.SigmaOneBoundedFormula n) := ⟨inf⟩

instance : Bot (L.SigmaOneBoundedFormula n) := ⟨⟨⊥⟩⟩

instance : Top (L.SigmaOneBoundedFormula n) := ⟨⟨⊤⟩⟩

/-- `∃ x, φ (..., x)`: the witness is the pair of `x` and the witness of `φ` -/
def ex (φ : L.SigmaOneBoundedFormula (n + 1)) : L.SigmaOneBoundedFormula n :=
  ⟨φ.deltaZeroBody.mergeLastTwo⟩

/-- `∀ x ∈ t, φ (..., x)`: the witness is a set containing a witness of `φ` for each `x` -/
def allMem (φ : L.SigmaOneBoundedFormula (n + 1)) (t : L.Term' n) :
  L.SigmaOneBoundedFormula n :=
  ⟨∀₀∈ t.castSucc ∃₀∈ &-2
    (φ.deltaZeroBody.substBoundBound (snoc (snoc (castAdd 3) (last _).castSucc) (last _)))⟩

@[inherit_doc] scoped[FirstOrder] prefix:110 "∃₁ " => FirstOrder.Language.SigmaOneBoundedFormula.ex

@[inherit_doc] scoped[FirstOrder]
notation "∀₁∈ " x:arg y:50 => FirstOrder.Language.SigmaOneBoundedFormula.allMem y x

/-- `∃ ys, φ (..., ys)` -/
def ex' : ∀ m, L.SigmaOneBoundedFormula (n + m) → L.SigmaOneBoundedFormula n
  | 0, φ => φ
  | m + 1, φ => ex' m (∃₁ φ)

/-- Renaming the variables of a `Σ₁` formula -/
def substBoundBound (φ : L.SigmaOneBoundedFormula n) (f : Fin n → Fin m) :
  L.SigmaOneBoundedFormula m :=
  ⟨φ.deltaZeroBody.substBoundBound (snoc (castSucc ∘ f) (last _))⟩

end SigmaOneBoundedFormula

end FirstOrder.Language
