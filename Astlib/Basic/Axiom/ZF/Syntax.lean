/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Axiom.KP.Syntax
import Astlib.Basic.SetOperation.Subset
/-!
# The axioms of `ZF`

`ZF` consists of extensionality, pairing, union, power set, infinity, foundation and the full
comprehension and collection schemas. It contains `KP₀` (`KP₀_subset_ZF`).
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

/-- The theory `ZF` -/
def ZF : L.Theory :=
  {extensionalityAxiom, pairAxiom, sUnionAxiom, powersetAxiom, infinityAxiom, foundationAxiom} ∪
    comprehensionSchema ∪ collectionSchema

theorem deltaZeroComprehensionSchema_subset :
    (deltaZeroComprehensionSchema : Set L.Sentence) ⊆ comprehensionSchema := by
  grind [deltaZeroComprehensionSchema, comprehensionSchema]

theorem deltaZeroCollectionSchema_subset :
    (deltaZeroCollectionSchema : Set L.Sentence) ⊆ collectionSchema := by
  grind [deltaZeroCollectionSchema, collectionSchema]

/-- `KP₀` is a subtheory of `ZF` -/
theorem KP₀_subset_ZF : (KP₀ : L.Theory) ⊆ ZF := by
  have h₁ : deltaZeroComprehensionSchema ⊆ comprehensionSchema :=
    deltaZeroComprehensionSchema_subset (L := L)
  have h₂ : deltaZeroCollectionSchema ⊆ collectionSchema :=
    deltaZeroCollectionSchema_subset (L := L)
  intro φ hφ
  simp only [KP₀, ZF, Set.mem_union, Set.mem_insert_iff] at hφ ⊢
  grind


end Language

end FirstOrder
