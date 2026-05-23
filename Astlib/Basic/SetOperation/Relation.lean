import Astlib.Basic.SetOperation.SProd

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

def IsRelation [M.ClosedUnderPair] (R : M) :=
  ∀ ⦃z : M⦄, z ∈ R → ∃ x y, z = !(x, y)

-- export ClosedUnderPair (isRelation)

theorem IsRelation.exists_exists [M.ClosedUnderPair] {R : M} (hR : IsRelation R)
    {z : M} (hz : z ∈ R) : ∃ x y, z = !(x, y) := hR hz

theorem empty_isRelation [M.HasEmpty] [M.ClosedUnderPair] : IsRelation (∅ : M) := by
  simp [IsRelation]

theorem sprod_isRelation [M.ClosedUnderSProd] : IsRelation (x ×ˢ y) := by
  grind [IsRelation]

theorem IsRelation.subset [M.ClosedUnderPair] {R S : M} (hR : IsRelation R) (hSR : S ⊆ R) :
    IsRelation S := by
  grind [IsRelation]

theorem IsRelation.inter [M.ClosedUnderPair] [M.ClosedUnderDeltaZeroComprehension]
    {R S : M} (hR : IsRelation R) : IsRelation (R ∩ S) := by
  grind [IsRelation]

theorem IsRelation.sdiff [M.ClosedUnderPair] [M.ClosedUnderDeltaZeroComprehension]
    {R S : M} (hR : IsRelation R) : IsRelation (R \ S) := by
  grind [IsRelation]

theorem IsRelation.union [M.ClosedUnderPair] [M.ClosedUnderSUnion] {R S : M}
    (hR : IsRelation R) (hS : IsRelation S) : IsRelation (R ∪ S) := by
  grind [IsRelation]

theorem IsRelation.sUnion [M.ClosedUnderSUnion] [M.ClosedUnderPair] {X : M}
    (hX : ∀ R ∈ X, IsRelation R) : IsRelation (⋃₀ X) := by
  grind [IsRelation]

variable [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSUnion]

noncomputable def dom (R : M) :=
  {∈ ⋃₀ (⋃₀ R) | ∃'∈ &0 (&2).eqLeft (&3) 〘R〙₀}

@[grind =]
theorem mem_dom_iff [M.Extensional] [M.ClosedUnderPair] (R x : M) :
    x ∈ dom R ↔ ∃ y, !(x, y) ∈ R := by
  suffices ∀ y, !(x, y) ∈ R → ∃ z, (∃ w ∈ R, z ∈ w) ∧ x ∈ z by simpa [dom]
  exact fun y _ ↦ ⟨unorderedPair x y, ⟨!(x, y), by grind [orderedPair]⟩, by grind⟩

noncomputable def ran (R : M) :=
  {∈ ⋃₀ (⋃₀ R) | ∃'∈ &0 (&2).eqRight (&3) 〘R〙₀}

@[grind =]
theorem mem_ran_iff [M.Extensional] [M.ClosedUnderPair] (R y : M) :
    y ∈ ran R ↔ ∃ x, !(x, y) ∈ R := by
  suffices ∀ x, !(x, y) ∈ R → ∃ z, (∃ w ∈ R, z ∈ w) ∧ y ∈ z by simpa [ran]
  exact fun x _ ↦ ⟨unorderedPair x y, ⟨!(x, y), by grind [orderedPair]⟩, by grind⟩

theorem IsRelation.subset_dom_sprod_ran [M.Extensional] [M.ClosedUnderSProd] {R : M}
    (hR : IsRelation R) : R ⊆ dom R ×ˢ ran R := by
  intro z hz
  obtain ⟨x, y, hxy⟩ := hR.exists_exists hz
  simp only [mem_sprod_iff]
  exact ⟨x, by grind, y, by grind, hxy⟩

/-- `R ∘ S` in set theory, denoted by `R !∘ S` in lean -/
noncomputable def comp [M.ClosedUnderSProd] [M.ClosedUnderDeltaZeroComprehension] (R S : M) : M :=
  {∈ dom R ×ˢ ran S |
    ∃'∈ &0 ∃'∈ &1 ((&4).sameLeft &3 ⊓ (&5).sameRight &3 ⊓ (&4).rightEqLeft (&5)) 〘![R, S]〙}

@[inherit_doc] infixr:90 " !∘ "  => FirstOrder.Language.MemStructure.comp

@[grind =]
theorem IsRelation.comp_mem [M.Extensional] [M.ClosedUnderSProd]
    (R S z : M) :
    z ∈ R !∘ S ↔ ∃ a b c : M, z = !(a, c) ∧ !(a, b) ∈ R ∧ !(b, c) ∈ S := by
  suffices ((∃ u ∈ dom R, ∃ v ∈ ran S, z = !(u, v)) ∧
    ∃ x x_1, !(x, x_1) ∈ R ∧ ∃ x_2 x_3, !(x_1, x_3) ∈ S ∧ (∃ x_4, z = !(x, x_4)) ∧ z = !(x_2, x_3))
    ↔ ∃ a b c, z = !(a, c) ∧ !(a, b) ∈ R ∧ !(b, c) ∈ S by
    simpa [MemStructure.comp, mem_subsetComprehension_iff]
  refine ⟨by grind, fun ⟨a, b, c, hz, hab, hbc⟩ ↦ ?_⟩
  exact ⟨⟨a, by grind, c, by grind, hz⟩, ⟨a, b, hab, a, c, hbc, ⟨⟨c, hz⟩, hz⟩⟩⟩

theorem IsRelation.comp_assoc [M.Extensional] [M.ClosedUnderSProd] (R S T : M) :
    (R !∘ S) !∘ T = R !∘ (S !∘ T) := by
  ext
  grind


end FirstOrder.Language.MemStructure
