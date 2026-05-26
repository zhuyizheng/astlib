import Astlib.Basic.SetOperation.Empty

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y : M)

noncomputable instance : Decidable (∃ a : M, ∀ z, z ∈ a ↔ z ⊆ x) :=
  Classical.propDecidable _

/-- The power set of `x` -/
noncomputable def powerset (x : M) := dite (∃ a : M, ∀ z, z ∈ a ↔ z ⊆ x) Classical.choose default

@[inherit_doc] prefix:100 "𝒫 " => powerset
--
class HasPowerset (x : M) : Prop where
  protected powerset_prop : ∀ z, z ∈ 𝒫 x ↔ z ⊆ x

export HasPowerset (powerset_prop)

variable (M) in
class ClosedUnderPowerset : Prop where
  protected closedUnderPowerset : ∀ x z : M, z ∈ 𝒫 x ↔ z ⊆ x

instance [hM : M.ClosedUnderPowerset] (x : M) : HasPowerset x := ⟨hM.closedUnderPowerset x⟩

-- export HasPowerset (hasPowerset)

-- export ClosedUnderPowerset (closedUnderPowerset)

noncomputable instance instHasPowerset (h : ∃ a : M, ∀ z, z ∈ a ↔ z ⊆ x) :
    M.HasPowerset x :=
  ⟨by convert Classical.choose_spec (h); simp [powerset, h]⟩

noncomputable instance instClosedUnderPowerset (h : ∀ x : M, ∃ a : M, ∀ z, z ∈ a ↔ z ⊆ x) :
    M.ClosedUnderPowerset :=
  ⟨fun x ↦ by convert Classical.choose_spec (h x); simp [powerset, h]⟩

@[simp, grind =, push]
theorem mem_powerset_iff {x : M} [hx : HasPowerset x] (z : M) : z ∈ 𝒫 x ↔ z ⊆ x :=
  HasPowerset.powerset_prop z

@[grind! .]
theorem mem_powerset_self [HasPowerset x] : x ∈ 𝒫 x := by simp

@[grind! .]
theorem empty_mem_powerset [M.HasEmpty] [HasPowerset x] : ∅ ∈ 𝒫 x := by grind

theorem powerset_mono {x y : M} (h : x ⊆ y) [HasPowerset x] [HasPowerset y] : 𝒫 x ⊆ 𝒫 y := by grind

theorem eq_of_powerset_eq [M.Extensional] {x y : M} [HasPowerset x] [HasPowerset y]
    (h : 𝒫 x = 𝒫 y) : x = y := by
  ext; grind

end MemStructure

variable {L : FirstOrder.Language} [HasMem L]

/-- Closed under power set -/
def allExPowerset : L.Sentence := ∀' ∃' ∀' (&2 ∈' &1 ⇔ &2 ⊆' &0)

variable {M : MemStructure}

-- instance (hM : M ⊨ M.L.allExPowerset) : M.ClosedUnderPowerset :=
--   ⟨by simpa [Term.subset] using realize_all.mp hM⟩

end FirstOrder.Language
