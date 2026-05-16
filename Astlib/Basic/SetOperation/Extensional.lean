import Astlib.ModelTheory.Defs

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure}

variable (M) in
/- `M` is extensional -/
class Extensional where
  extensional : ∀ x y : M, ((∀ z : M, (z ∈ x ↔ z ∈ y)) → x = y)

export Extensional (extensional)

instance instExtensional (hM : M ⊨ M.L.extensionality) : Extensional M where
  extensional := by simpa [Sentence.Realize, Formula.Realize, extensionality] using hM

@[ext]
theorem ext [Extensional M] {x y : M} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y :=
  extensional x y h

theorem eq_of_subset_of_subset [Extensional M] {x y : M} (h : x ⊆ y) (h' : y ⊆ x) :
    x = y := by
  ext; grind

instance instAntisymmSubset [Extensional M] : Std.Antisymm (α := M) Subset where
  antisymm := fun _ _ h h' ↦ eq_of_subset_of_subset h h'

end FirstOrder.Language.MemStructure
