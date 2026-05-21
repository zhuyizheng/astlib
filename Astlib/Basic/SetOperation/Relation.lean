import Astlib.Basic.SetOperation.SProd

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} [M.ClosedUnderPair] (x y z x₁ x₂ y₁ y₂ u v : M)

def isRelation (R : M) :=
  ∀ ⦃z : M⦄, z ∈ R → ∃ x y, z = !(x, y)

-- export ClosedUnderPair (isRelation)

theorem mem_of_isRelation {R : M} (hR : isRelation R) (hz : z ∈ R) :
    ∃ x y, z = !(x, y) := hR hz

theorem empty_isRelation [M.HasEmpty] : isRelation (∅ : M) := by
  simp [isRelation]

theorem sprod_isRelation [M.ClosedUnderSProd] : isRelation (x ×ˢ y) := by
  simp only [isRelation, mem_sprod_iff, forall_exists_index, and_imp]
  intro z u hu v hv hz
  use u, v
  sorry
  -- exact hz

theorem isRelation.subset {R S : M} (hR : isRelation R) (hSR : S ⊆ R) :
    isRelation S := by
  grind [isRelation]

theorem isRelation.inter [M.ClosedUnderDeltaZeroComprehension] {R S : M} (hR : isRelation R) :
    isRelation (R ∩ S) := by
  grind [isRelation]

theorem isRelation.sdiff [M.ClosedUnderDeltaZeroComprehension] {R S : M} (hR : isRelation R) :
    isRelation (R \ S) := by
  grind [isRelation]

theorem isRelation.union [M.ClosedUnderSUnion] {R S : M} (hR : isRelation R) (hS : isRelation S) :
    isRelation (R ∪ S) := by
  grind [isRelation]

theorem isRelation.sUnion [M.ClosedUnderSUnion] {X : M} (hX : ∀ R ∈ X, isRelation R) :
    isRelation (⋃₀ X) := by
  grind [isRelation]

variable [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSUnion]

noncomputable def dom (R : M) :=
  {∈ ⋃₀ (⋃₀ R) | ∃'∈ &0 (&2).eqLeft (&3) 〘R〙}

theorem mem_dom_iff [M.Extensional] (R x : M) : x ∈ dom R ↔ ∃ y, !(x, y) ∈ R := by
  suffices ∀ y, !(x, y) ∈ R → ∃ z, (∃ w ∈ R, z ∈ w) ∧ x ∈ z by simpa [dom]
  exact fun y _ ↦ ⟨unorderedPair x y, ⟨!(x, y), by grind [orderedPair]⟩, by grind⟩

noncomputable def ran (R : M) :=
  {∈ ⋃₀ (⋃₀ R) | ∃'∈ &0 (&2).eqRight (&3) 〘R〙}

theorem mem_ran_iff [M.Extensional] (R y : M) : y ∈ ran R ↔ ∃ x, !(x, y) ∈ R := by
  suffices ∀ x, !(x, y) ∈ R → ∃ z, (∃ w ∈ R, z ∈ w) ∧ y ∈ z by simpa [ran]
  exact fun x _ ↦ ⟨unorderedPair x y, ⟨!(x, y), by grind [orderedPair]⟩, by grind⟩

end FirstOrder.Language.MemStructure
