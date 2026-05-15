import Astlib.Basic.SetOperation.HasEmpty

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable (M : MemStructure)

/- `M` is closed under `⋃` -/
class HasPowerset where
  /-- The power set operator -/
  powerset : M → M
  powerset_prop : ∀ x y : M, y ∈ powerset x ↔ y ⊆ x

export HasPowerset (powerset powerset_prop)

@[inherit_doc] prefix:100 "𝒫 " => powerset

noncomputable instance (hM : M ⊨ M.L.exPowerSet) : HasPowerset M where
  powerset x := Classical.choose (exists_of_ex (realize_all.mp hM x))
  powerset_prop := fun x ↦ by
    simpa [Term.subset] using Classical.choose_spec (exists_of_ex (realize_all.mp hM x))

variable {M}

@[simp, grind =, push]
theorem mem_powerset_iff [HasPowerset M] (x a : M) : x ∈ 𝒫 a ↔ x ⊆ a :=
  powerset_prop _ _

@[grind! .]
theorem mem_powerset_self [HasPowerset M] (x : M) : x ∈ 𝒫 x := by simp

@[grind! .]
theorem empty_mem_powerset [HasEmpty M] [HasPowerset M] (x : M) : ∅ ∈ 𝒫 x := by grind

theorem powerset_mono [HasPowerset M] (x y : M) (h : x ⊆ y) : 𝒫 x ⊆ 𝒫 y := by
  intro z hz
  simp only [mem_powerset_iff] at hz ⊢
  exact hz.trans h

theorem powerset_injective [Extensional M] [HasPowerset M] : Function.Injective M.powerset := by
  intro _ _ _
  grind [eq_of_subset_of_subset]

end FirstOrder.Language.MemStructure
