import Astlib.Basic.SetOperation.SProd

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} [M.ClosedUnderPair] (x y z x₁ x₂ y₁ y₂ u v : M)

def ClosedUnderPair.isRelation (R : M) :=
  ∀ ⦃z : M⦄, z ∈ R → ∃ x y, z = !(x, y)

export ClosedUnderPair (isRelation)

theorem mem_of_isRelation {R : M} (hR : isRelation R) (hz : z ∈ R) :
    ∃ x y, z = !(x, y) := hR hz

theorem empty_isRelation [M.HasEmpty] : isRelation (∅ : M) := by
  simp [isRelation]

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

noncomputable def ClosedUnderPair.dom (R : M) :=
  {∈ ⋃₀ (⋃₀ R) | (&0).isEmpty }

export ClosedUnderPair (isRelation)

end FirstOrder.Language.MemStructure
