/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Foundational
import Astlib.Basic.SetOperation.Choice
import Astlib.Mathlib.Fin.Basic
/-!
file docstring
-/

namespace FirstOrder

namespace Language

open FirstOrder Language BoundedFormula Fin

variable {L : FirstOrder.Language} [L.HasMem]

/-- The extensionalityAxiom axiom -/
def extensionalityAxiom {L : FirstOrder.Language} [L.HasMem] : L.Sentence :=
  ∀' ∀' (∀' (&2 ∈' &0 ⇔ &2 ∈' &1) ⟹ &0 =' &1)

/-- The comprehension axiom -/
def BoundedFormula.comprehension (φ : L.BoundedFormula' (n + 1)) : L.Sentence :=
  ∀'' ∃' ∀' (&-1 ∈' &-2 ⇔ (&-1 ∈' &-3 ⊓ φ.substBoundBound (snoc (castAdd 3) (last _))))

/-- DeltaZero comprehension schema -/
def deltaZeroComprehensionSchema : Set (L.Sentence) :=
  {ψ | ∃ n, ∃ φ : L.BoundedFormula' (n + 1), ∃ _ : φ.DeltaZero, ψ = φ.comprehension}

/-- The union axiom -/
def sUnionAxiom : L.Sentence := ∀' ∃' ∀' ∀' ((&3 ∈' &2 ⊓ &2 ∈' &0) ⟹ &3 ∈' &1)

/-- The pairing axiom -/
def pairAxiom : L.Sentence := ∀' ∀' ∃' (&0 ∈' &2 ⊓ &1 ∈' &2)

/-- The collection axiom -/
def BoundedFormula.collection (φ : L.BoundedFormula' (n + 2)) : L.Sentence :=
  ∀'' ((∀'∈ &-1 ∃' (φ.substBoundBound (snoc (snoc (castAdd 3) (last _).castSucc) (last _)))) ⟹
    ∃' ∀'∈ &-2 ∃'∈ &-2 (φ.substBoundBound (snoc (snoc (castAdd 4) (last _).castSucc) (last _))))

/-- DeltaZero collection schema -/
def deltaZeroCollectionSchema : Set (L.Sentence) :=
  {ψ | ∃ n, ∃ φ : L.BoundedFormula' (n + 2), ∃ _ : φ.DeltaZero, ψ = φ.collection}

/-- The infinity axiom -/
def infinityAxiom : L.Sentence := ∃' ((∃'∈ &0 ∀'∈ &1 ⊥) ⊓ ∀'∈ &0 (∃'∈ &0 ∀' (&3 ∈' &2 ⇔ &3 =' &1 ⊔ &3 ∈' &1)))

/-- The recursion axiom -/
def BoundedFormula.recursion (φ : L.BoundedFormula' (n + 1)) : L.Sentence :=
  ∀'' ((∀' ((∀'∈ &-1 φ.substBoundBound (snoc (castAdd 2) (last _))) ⟹ φ)) ⟹ ∀' φ)

/-- The recursion schema -/
def recursionSchema : Set (L.Sentence) :=
  {ψ | ∃ n, ∃ φ : L.BoundedFormula' (n + 1), ψ = φ.recursion}

def KP : L.Theory :=
  {extensionalityAxiom, pairAxiom, sUnionAxiom} ∪
    deltaZeroComprehensionSchema ∪ deltaZeroCollectionSchema ∪ recursionSchema

def KPInf : L.Theory :=
  KP ∪ {infinityAxiom}


end Language

end FirstOrder
