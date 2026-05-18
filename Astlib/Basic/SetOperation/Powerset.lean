import Astlib.Basic.SetOperation.Empty

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y : M)

class HasPowerset (x : M) where
  hasPowerset : ∃ y : M, ∀ z, z ∈ y ↔ z ⊆ x

export HasPowerset (hasPowerset)

/-- The power set of `x` -/
noncomputable def powerset (x : M) [hx : HasPowerset x] := Classical.choose hx.hasPowerset

@[inherit_doc] prefix:100 "𝒫 " => powerset

@[simp, grind =, push]
theorem mem_powerset_iff {x : M} [hx : HasPowerset x] (z : M) : z ∈ 𝒫 x ↔ z ⊆ x :=
  Classical.choose_spec hx.hasPowerset z

instance instHasPowerSet (hM : M ⊨ M.L.allExPowerset) (x : M) : HasPowerset x where
  hasPowerset := by simpa [Term.subset] using realize_all.mp hM x

@[grind! .]
theorem mem_powerset_self [HasPowerset x] : x ∈ 𝒫 x := by simp

@[grind! .]
theorem empty_mem_powerset [HasEmpty M] [HasPowerset x] : ∅ ∈ 𝒫 x := by grind

theorem powerset_mono {x y : M} (h : x ⊆ y) [HasPowerset x] [HasPowerset y] : 𝒫 x ⊆ 𝒫 y := by grind

theorem eq_of_powerset_eq [Extensional M] {x y : M} [HasPowerset x] [HasPowerset y]
    (h : 𝒫 x = 𝒫 y) : x = y := by
  ext; grind

end FirstOrder.Language.MemStructure
