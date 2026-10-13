/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.MemStructure.Levy
import Astlib.Basic.SetOperation.Rudimentary.Syntax
import Astlib.Basic.SetOperation.Pair.Syntax
/-!
file docstring
-/

open FirstOrder Language BoundedFormula Theory Fin

variable {L : FirstOrder.Language.{u, v}} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]

namespace FirstOrder

namespace Language

/-- `Σ₁` bounded formulas in `L` -/
structure SigmaOneBoundedFormula [L.HasMem] (n : ℕ) where
  deltaZeroBody : L.DeltaZeroBoundedFormula (n + 1)

def DeltaZeroBoundedFormula.toSigmaOneBoundedFormula (φ : L.DeltaZeroBoundedFormula n) :
  L.SigmaOneBoundedFormula n :=
  ⟨φ.substBoundBound castSucc⟩

namespace SigmaOneBoundedFormula

def toBoundedFormula (φ : L.SigmaOneBoundedFormula n) : L.BoundedFormula' n :=
  ∃' φ.deltaZeroBody.toBoundedFormula

instance : Coe (L.SigmaOneBoundedFormula n) (L.BoundedFormula' n) := ⟨toBoundedFormula⟩

def sup (φ ψ : L.SigmaOneBoundedFormula n) : L.SigmaOneBoundedFormula n :=
  ⟨φ.deltaZeroBody ⊔ ψ.deltaZeroBody⟩

noncomputable def inf (φ ψ : L.SigmaOneBoundedFormula n) : L.SigmaOneBoundedFormula n :=
  ⟨(ᵣ-1).isOrderedPair ⊓
    φ.deltaZeroBody.substBoundRud (snoc (fun i ↦ ᵣi.castSucc) (ᵣ-1).left) ⊓
    ψ.deltaZeroBody.substBoundRud (snoc (fun i ↦ ᵣi.castSucc) (ᵣ-1).right)⟩

instance : Max (L.SigmaOneBoundedFormula n) := ⟨sup⟩

noncomputable instance : Min (L.SigmaOneBoundedFormula n) := ⟨inf⟩

instance : Bot (L.SigmaOneBoundedFormula n) := ⟨⟨⊥⟩⟩

instance : Top (L.SigmaOneBoundedFormula n) := ⟨⟨⊤⟩⟩

noncomputable def ex (φ : L.SigmaOneBoundedFormula (n + 1)) : L.SigmaOneBoundedFormula n :=
  ⟨(ᵣ-1).isOrderedPair ⊓
    φ.deltaZeroBody.substBoundRud (snoc (snoc (fun i ↦ ᵣi.castSucc) (ᵣ-1).left) (ᵣ-1).right)⟩

noncomputable def allMem (φ : L.SigmaOneBoundedFormula (n + 1)) (t : L.Term' n) :
  L.SigmaOneBoundedFormula n :=
  ⟨∀₀∈ t.castSucc ∃₀∈ &-2 (φ.deltaZeroBody.substBoundRud (snoc (snoc (fun i ↦ .var (i.castAdd 3)) ᵣ-2) ᵣ-1))⟩



end SigmaOneBoundedFormula

end FirstOrder.Language
