import Astlib.Basic.SetOperation.Empty

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y : M)

class HasPowerset (x : M) : Prop where
  protected hasPowerset : ∃ y : M, ∀ z, z ∈ y ↔ z ⊆ x

class ClosedUnderPowerset : Prop where
  protected closedUnderPowerset : ∀ x, ∃ y : M, ∀ z, z ∈ y ↔ z ⊆ x

instance [hM : M.ClosedUnderPowerset] (x : M) : HasPowerset x where
  hasPowerset := hM.closedUnderPowerset x

export HasPowerset (hasPowerset)

export ClosedUnderPowerset (closedUnderPowerset)

/-- The power set of `x` -/
noncomputable def powerset (x : M) [hx : HasPowerset x] := Classical.choose hx.hasPowerset

@[inherit_doc] prefix:100 "𝒫 " => powerset

@[simp, grind =, push]
theorem mem_powerset_iff {x : M} [hx : HasPowerset x] (z : M) : z ∈ 𝒫 x ↔ z ⊆ x :=
  Classical.choose_spec hx.hasPowerset z

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

instance (hM : M ⊨ M.L.allExPowerset) : M.ClosedUnderPowerset :=
  ⟨by simpa [Term.subset] using realize_all.mp hM⟩

end FirstOrder.Language
