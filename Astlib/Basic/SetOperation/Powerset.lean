import Astlib.Basic.SetOperation.Empty

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y : M)

abbrev IsPowerset (a x : M) := ∀ z, z ∈ a ↔ z ⊆ x

noncomputable instance : Decidable (∃ a : M, IsPowerset a x) :=
  Classical.propDecidable _

/-- The power set of `x` -/
noncomputable def powerset (x : M) := dite (∃ a : M, IsPowerset a x) Classical.choose default

@[inherit_doc] prefix:100 "𝒫 " => powerset

class HasPowerset (x : M) : Prop where
  protected hasPowerset : ∃ a, IsPowerset a x

variable (M) in
class ClosedUnderPowerset : Prop where
  protected closedUnderPowerset : ∀ x : M, ∃ a, IsPowerset a x

instance [hM : M.ClosedUnderPowerset] (x : M) : HasPowerset x := ⟨hM.closedUnderPowerset x⟩

@[simp, grind =, push]
theorem mem_powerset_iff {x : M} [hx : HasPowerset x] (z : M) : z ∈ 𝒫 x ↔ z ⊆ x := by
  simp only [HasPowerset.hasPowerset, powerset]
  grind

@[grind! .]
theorem mem_powerset_self [HasPowerset x] : x ∈ 𝒫 x := by simp

@[grind! .]
theorem empty_mem_powerset [M.HasEmpty] [HasPowerset x] : ∅ ∈ 𝒫 x := by grind

theorem powerset_mono {x y : M} (h : x ⊆ y) [HasPowerset x] [HasPowerset y] : 𝒫 x ⊆ 𝒫 y := by grind

theorem eq_of_powerset_eq [M.Extensional] {x y : M} [HasPowerset x] [HasPowerset y]
    (h : 𝒫 x = 𝒫 y) : x = y := by
  ext; grind

end FirstOrder.Language.MemStructure
