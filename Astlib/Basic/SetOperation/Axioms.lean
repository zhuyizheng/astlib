import Astlib.Basic.SetOperation.Foundational
import Astlib.Basic.SetOperation.Choice

namespace FirstOrder

namespace Language

open FirstOrder Language BoundedFormula Fin

variable {L : FirstOrder.Language} [HasMem L] {M : MemStructure}

/-- The extensionality axiom -/
def extensionality {L : FirstOrder.Language} [HasMem L] : L.Sentence :=
  ∀' ∀' (∀' (&2 ∈' &0 ⇔ &2 ∈' &1) ⟹ &0 =' &1)

instance (hM : M ⊨ M.L.extensionality) : M.Extensional :=
  ⟨by simpa [Sentence.Realize, Formula.Realize, extensionality] using hM⟩

/-- The comprehension axiom -/
def BoundedFormula.comprehension (φ : L.BoundedFormula α (n + 2)) : L.Formula α :=
  ∀'' ∃' ∀' (&-1 ∈' &-2 ⇔ (&-1 ∈' &-3 ⊓ φ.liftAt 1 (n + 1)))

/-- DeltaZero comprehension schema -/
def deltaZeroComprehensionSchema : Set (L.Sentence) :=
  {ψ | ∃ n, ∃ φ : L.BoundedFormula Empty (n + 2), ∃ _ : φ.DeltaZero, ψ = φ.comprehension}
  -- {ψ | ∃ n, ∃ φ : L.BoundedFormula Empty (n + 2), DeltaZero φ ∧ ψ = φ.comprehension}

/-- Full comprehension schema -/
def comprehensionSchema : Set (L.Sentence) :=
  {ψ | ∃ n, ∃ φ : L.BoundedFormula Empty (n + 2), ψ = φ.comprehension}

theorem exists_deltaZeroComprehension (hM : M ⊨ M.L.deltaZeroComprehensionSchema) (x : M)
    (φ : M.L.BoundedFormula Empty (n + 2)) [φ.DeltaZero] (xs : Fin n → M) :
    ∃ a : M, ∀ z, z ∈ a ↔ z ∈ x ∧ φ.Realize default (snoc (snoc xs x) z) := by
  simp only [deltaZeroComprehensionSchema, exists_prop, Theory.model_iff, Set.mem_setOf_eq,
    forall_exists_index, and_imp] at hM
  specialize hM φ.comprehension n φ (by infer_instance) rfl
  simp [BoundedFormula.comprehension, Sentence.Realize, snoc] at hM
  -- rw [realize_alls] at hM
  sorry


-- instance (hM : M ⊨ M.L.deltaZeroComprehensionSchema) :
--   M.ClosedUnderDeltaZeroComprehension where
--   closedUnderDeltaZeroComprehension := by

-- instance (hM : M ⊨ M.L.comprehensionSchema) :
--   M.ClosedUnderComprehension where
--   closedUnderComprehension := by


/-- Every set has a union -/
def allExSUnion : L.Sentence := ∀' ∃' (&1).eqSUnion &0

theorem exists_sUnion (hM : M ⊨ M.L.allExSUnion) (x : M) :
    ∃ a : M, ∀ y, y ∈ a ↔ (∃ z ∈ x, y ∈ z) := by
  have : ∀ (a : M), ∃ a_1 : M, (∀ a_2 ∈ a_1, ∃ y ∈ a, a_2 ∈ y) ∧ ∀ a_2 ∈ a, ∀ a ∈ a_2, a ∈ a_1 := by
    simpa [allExSUnion, Sentence.Realize, Formula.Realize, Fin.snoc] using hM
  exact exists_congr (by grind) |>.mpr (this x)

-- noncomputable instance (hM : M ⊨ M.L.allExSUnion) :
--   M.ClosedUnderSUnion := M.instClosedUnderSUnion (fun x ↦ exists_sUnion hM x)

/-- Closed under unordered pairing -/
def allAllExPair : L.Sentence := ∀' ∀' ∃' (&2).eqUnorderedPair &0 &1

theorem exists_unorderedPair (hM : M ⊨ M.L.allAllExPair) (x y : M) :
    ∃ a : M, ∀ z, z ∈ a ↔ z = x ∨ z = y := by
  have : ∀ (a a_1 : M), ∃ a_2 : M, (∀ a_3 ∈ a_2, a_3 = a ∨ a_3 = a_1) ∧ a ∈ a_2 ∧ a_1 ∈ a_2 := by
    simpa [allAllExPair, Sentence.Realize, Formula.Realize, Fin.snoc] using hM
  exact exists_congr (by grind) |>.mpr (this x y)

-- noncomputable instance {M : MemStructure}
--     (hM : M ⊨ M.L.allAllExPair) :
--     M.ClosedUnderPair := M.instClosedUnderPair (fun x y ↦ exists_unorderedPair hM x y)

/-- Closed under power set -/
def allExPowerset : L.Sentence := ∀' ∃' ∀' (&2 ∈' &1 ⇔ &2 ⊆' &0)

theorem exists_powerset {M : MemStructure} (hM : M ⊨ M.L.allExPowerset) (x : M) :
    ∃ a : M, ∀ z, z ∈ a ↔ z ⊆ x := by
  have :  ∀ (a : M), ∃ a_1 : M, ∀ (a_2 : M), a_2 ∈ a_1 ↔ a_2 ⊆ a := by
    simpa [allExPowerset, Sentence.Realize, Formula.Realize, Fin.snoc] using hM
  exact this x

-- instance (hM : M ⊨ M.L.allExPowerset) : M.ClosedUnderPowerset :=
--   M.instClosedUnderPowerset (fun x ↦ exists_powerset hM x)

/-- The foundation axiom -/
def foundation : L.Sentence := ∀' ((&0).isEmpty ⊔ ∃'∈ &0 ∼(∃'∈ &0 (&2 ∈' &1)))

theorem exists_memMin [M.Extensional] [M.HasEmpty] (hM : M ⊨ M.L.foundation) (x : M)
    (hx : x ≠ ∅) :
    ∃ y : M, (y ∈ x ∧ ∀ z ∈ y, z ∉ x) := by
  have : ∀ (a : ↑M), a = ∅ ∨ ∃ x ∈ a, ∀ x_1 ∈ a, x_1 ∉ x := by
    simpa [foundation, Sentence.Realize, Formula.Realize, Fin.snoc] using hM
  specialize this x
  grind

-- noncomputable instance [M.Extensional] [M.HasEmpty]
--     (hM : M ⊨ M.L.foundation) : M.Foundational :=
--   M.instFoundational (fun x ↦ exists_memMin hM x)

-- noncomputable instance (hM : M ⊨ M.L.allExSUnion) : M.ClosedUnderSUnion where

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
