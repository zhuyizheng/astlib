/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Axiom.KP.Syntax
/-!
file docstring
-/

namespace FirstOrder

namespace Language

open FirstOrder Language BoundedFormula Fin

variable {L : FirstOrder.Language} [L.HasMem]

/-- Full comprehension schema -/
def comprehensionSchema : Set (L.Sentence) :=
  {ψ | ∃ n, ∃ φ : L.BoundedFormula' (n + 1), ψ = φ.comprehension}

/-- Full collection schema -/
def collectionSchema : Set (L.Sentence) :=
  {ψ | ∃ n, ∃ φ : L.BoundedFormula' (n + 2), ψ = φ.collection}

/-- The power set axiom -/
def powersetAxiom : L.Sentence := ∀' ∃' ∀' (&2 ⊆' &0 ⟹ &2 ∈' &1)

/-- The foundation axiom -/
def foundationAxiom : L.Sentence := ∀'((∃'(&1 ∈' &0)) ⟹ ∃'∈ &0 ∀'∈ &1 ∼(&2 ∈' &0))


def ZFC : Set (L.Sentence) :=
  {extensionalityAxiom, pairAxiom, sUnionAxiom}


end Language

end FirstOrder
