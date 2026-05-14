import Astlib.Syntax

namespace FirstOrder

namespace Language

open FirstOrder Language BoundedFormula

variable {L : FirstOrder.Language} [HasMem L]

/-- The extensionality axiom -/
def extensionality : L.Sentence := ∀' ∀' (∀' (&2 ∈' &0 ⇔ &2 ∈' &1) ⟹ &0 =' &1)

/-- The comprehension axiom -/
def comprehension (φ : L.BoundedFormula α (n + 2)) : L.Formula α :=
  ∀'' ∃' ∀' (&-1 ∈' &-2 ⇔ (&-1 ∈' &0 ⊓ φ.liftAt 1 (n + 1)))

/-- The pairing axiom -/
def pair : L.Sentence := ∀' ∀' ∃' (&2 ∈' &0 ⊔ &2 ∈' &1)

/-- The union axiom -/
def union : L.Sentence := ∀' ∃' ∀' ∀' ((&3 ∈' &2 ⊓ &2 ∈' &0) ⟹ &3 ∈' &1)

/-- The replacement axiom -/
def replacement (φ : L.BoundedFormula α (n + 3)) : L.Formula α :=
  ∀'' ((∀'∈ &0 ∃!' φ) ⟹ ∃' (∀'∈ &0 ∃'∈ &-3 (φ.liftAt 1 (n + 1))))

/-- The infinity axiom -/
def infinity : L.Sentence := ∃' ((∃'∈ &0 (&1).isEmptyset) ⊓ ∀'∈ &0 (∃'∈ &0 ((&2).eqSucc &1)))

/-- The regularity axiom -/
def regularity : L.Sentence := ∀' ((&0).isEmptyset ⊔ ∃'∈ &0 ∼(∃'∈ &1 (&2 ∈' &0)))

/-- The power set axiom -/
def power : L.Sentence := ∀' ∃' ∀' (&2 ⊆' &0 ⟹ &2 ∈' &1)

/-- The axiom of choice -/
def choice : L.Sentence :=
  ∀' (∼(&-1).isEmptyset ⟹ ∃' ((&-2).isFun ⊓ (&-1).eqDom (&-2) ⊓
    ∀' ∃' ((&-3).memDom (&-2) ⟹ ∼(&-3).isEmptyset ⟹ ((&-4).eqVal &-2 &-3 ⊓ &-4 ∈' &-3))))

/-- There exists an empty set -/
def exEmptyset : L.Sentence := ∃' ((&0).isEmptyset)

/-- Every set has a union -/
def exUnion : L.Sentence := ∀' ∃' ∀' (&2 ∈' &1 ⇔ ∃' ((&3 ∈' &0 ⊓ &2 ∈' &3)))

/-- Closed under unordered pairing -/
def exUnorderedPair : L.Sentence := ∀' ∀' ∃' ∀' (&3 ∈' &2 ⇔ (&3 =' &0 ⊔ &3 =' &1))

end Language

end FirstOrder
