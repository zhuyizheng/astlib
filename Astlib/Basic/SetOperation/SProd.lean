import Astlib.Basic.SetOperation.SDiff
import Astlib.Basic.SetOperation.Powerset

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

variable (M) in
/- Every nonempty member of `M` has a `∈`-mimimal element -/
class ClosedUnderSProd extends M.ClosedUnderPair, SProd M M M where
  protected sprod_prop (x y z : M) : z ∈ x ×ˢ y ↔ ∃ u ∈ x, ∃ v ∈ y, z = !(u, v)

-- export ClosedUnderProduct (sprod_prop)

theorem exists_sprod [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
    [M.ClosedUnderDeltaZeroComprehension]
    [M.HasPowerset (x ∪ y)] [M.HasPowerset (𝒫 (x ∪ y))] :
    ∃ a : M, ∀ z, z ∈ a ↔ ∃ u ∈ x, ∃ v ∈ y, z = !(u, v) := by
  -- sorry
  use {∈ 𝒫 (𝒫 (x ∪ y)) | ∃'∈ &0 ∃'∈ &1 (&3).eqOrderedPair &4 &5 〘![x, y]〙}
  suffices ∀ (z x_1 : ↑M), x_1 ∈ x → ∀ x_2 ∈ y, z = !(x_1, x_2) → z ⊆ 𝒫 (x ∪ y) by
    simpa
  intro z u hu v hv hz
  rw [hz, orderedPair]
  intro p
  simp only [mem_unorderedPair_iff, mem_powerset_iff]
  grind

noncomputable instance [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
  [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderPowerset] :
  M.ClosedUnderSProd where
  sprod x y := Classical.choose (exists_sprod x y)
  sprod_prop x y z := by simpa using Classical.choose_spec (exists_sprod x y) z

@[simp, grind =]
theorem mem_sprod_iff [ClosedUnderSProd M] : z ∈ x ×ˢ y ↔ ∃ u ∈ x, ∃ v ∈ y, z = !(u, v) :=
  ClosedUnderSProd.sprod_prop x y z

theorem mem_sprod [ClosedUnderSProd M] (hu : u ∈ x) (hv : v ∈ y) : !(u, v) ∈ x ×ˢ y := by
  grind

variable [M.ClosedUnderSProd]

theorem sprod_empty [M.Extensional] [M.HasEmpty] :
    x ×ˢ (∅ : M) = ∅ := by
  ext; grind

theorem empty_sprod [M.Extensional] [M.HasEmpty] :
    (∅ : M) ×ˢ x = ∅ := by
  ext; grind

theorem sprod_mono_left {x₁ x₂ : M} (h : x₁ ⊆ x₂) : x₁ ×ˢ y ⊆ x₂ ×ˢ y := by
  grind

theorem sprod_mono_right {y₁ y₂ : M} (h : y₁ ⊆ y₂) : x ×ˢ y₁ ⊆ x ×ˢ y₂ := by
  grind

theorem union_sprod [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    (x₁ ∪ x₂) ×ˢ y = x₁ ×ˢ y ∪ x₂ ×ˢ y := by
  ext; grind

theorem sprod_union [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    x ×ˢ (y₁ ∪ y₂) = x ×ˢ y₁ ∪ x ×ˢ y₂ := by
  ext; grind

theorem inter_sprod [M.Extensional] [M.ClosedUnderDeltaZeroComprehension] :
    (x₁ ∩ x₂) ×ˢ y = x₁ ×ˢ y ∩ x₂ ×ˢ y := by
  ext; grind

theorem sprod_inter [M.Extensional] [M.ClosedUnderDeltaZeroComprehension] :
    x ×ˢ (y₁ ∩ y₂) = x ×ˢ y₁ ∩ x ×ˢ y₂ := by
  ext; grind

theorem sdiff_sprod [M.Extensional] [M.ClosedUnderDeltaZeroComprehension] :
    (x₁ \ x₂) ×ˢ y = x₁ ×ˢ y \ x₂ ×ˢ y := by
  ext; grind

theorem sprod_sdiff [M.Extensional] [M.ClosedUnderDeltaZeroComprehension] :
    x ×ˢ (y₁ \ y₂) = x ×ˢ y₁ \ x ×ˢ y₂ := by
  ext; grind

theorem sprod_inter_sprod [M.Extensional] [M.ClosedUnderDeltaZeroComprehension] :
    x₁ ×ˢ y₁ ∩ x₂ ×ˢ y₂ = (x₁ ∩ x₂) ×ˢ (y₁ ∩ y₂) := by
  ext z; simp only [mem_inter, mem_sprod_iff]
  exact ⟨fun ⟨⟨u₁, hu₁, v₁, hv₁, hz₁⟩, ⟨u₂, hu₂, v₂, hv₂, hz₂⟩⟩ ↦ ⟨u₁, (by grind), v₁, (by grind)⟩,
    fun ⟨u, hu, v, hv, hz⟩ ↦ ⟨⟨u, by grind, v, by grind, hz⟩, ⟨u, by grind, v, by grind, hz⟩⟩⟩

end FirstOrder.Language.MemStructure
