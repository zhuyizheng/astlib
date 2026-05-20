import Astlib.ModelTheory.Syntax
import Astlib.ModelTheory.Levy

namespace FirstOrder

namespace Language

open FirstOrder Language BoundedFormula

variable {L : FirstOrder.Language} [HasMem L]

-- /-- The extensionality axiom -/
-- def extensionality : L.Sentence := ∀' ∀' (∀' (&2 ∈' &0 ⇔ &2 ∈' &1) ⟹ &0 =' &1)

-- def comprehension' (φ : L.BoundedFormula α (n + 2)) : L.BoundedFormula α (n + 2) :=
--   ∀' (&-1 ∈' &-2 ⇔ (&-1 ∈' &0 ⊓ φ.liftAt 1 (n + 1)))


-- /-- The pairing axiom -/
-- def pair : L.Sentence := ∀' ∀' ∃' (&2 ∈' &0 ⊔ &2 ∈' &1)

-- /-- The union axiom -/
-- def sUnion : L.Sentence := ∀' ∃' ∀' ∀' ((&3 ∈' &2 ⊓ &2 ∈' &0) ⟹ &3 ∈' &1)

-- /-- The replacement axiom -/
-- def replacement (φ : L.BoundedFormula α (n + 3)) : L.Formula α :=
--   ∀'' ((∀'∈ &0 ∃!' φ) ⟹ ∃' (∀'∈ &0 ∃'∈ &-3 (φ.liftAt 1 (n + 1))))

-- /-- The infinity axiom -/
-- def infinity : L.Sentence := ∃' ((∃'∈ &0 (&1).isEmpty) ⊓ ∀'∈ &0 (∃'∈ &0 ((&2).eqSucc &1)))

-- /-- The foundation axiom -/
-- def foundation : L.Sentence := ∀' ((&0).isEmpty ⊔ ∃'∈ &0 ∼(∃'∈ &0 (&2 ∈' &1)))

-- /-- The power set axiom -/
-- def power : L.Sentence := ∀' ∃' ∀' (&2 ⊆' &0 ⟹ &2 ∈' &1)

-- /-- The axiom of choice -/
-- def choice : L.Sentence :=
--   ∀' (∼(&-1).isEmpty ⟹ ∃' ((&-2).isFun ⊓ (&-1).eqDom (&-2) ⊓
--     ∀' ∃' ((&-3).memDom (&-2) ⟹ ∼(&-3).isEmpty ⟹ ((&-4).eqVal &-2 &-3 ⊓ &-4 ∈' &-3))))

-- /-- There exists an empty set -/
-- def exEmptyset : L.Sentence := ∃' ((&0).isEmpty)

-- /-- Every set has a union -/
-- def allExSUnion : L.Sentence := ∀' ∃' ∀' (&2 ∈' &1 ⇔ ∃' ((&3 ∈' &0 ⊓ &2 ∈' &3)))

-- /-- Closed under unordered pairing -/
-- def allAllExPair : L.Sentence := ∀' ∀' ∃' ∀' (&3 ∈' &2 ⇔ (&3 =' &0 ⊔ &3 =' &1))

-- /-- Closed under power set -/
-- def allExPowerset : L.Sentence := ∀' ∃' ∀' (&2 ∈' &1 ⇔ &2 ⊆' &0)


end Language

end FirstOrder
