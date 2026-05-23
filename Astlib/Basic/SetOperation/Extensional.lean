import Astlib.ModelTheory.Defs
import Astlib.Basic.SetOperation.Subset

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure}

variable (M) in
/- `M` is extensional -/
class Extensional : Prop where
  protected extensional : ∀ x y : M, ((∀ z : M, (z ∈ x ↔ z ∈ y)) → x = y)

@[ext]
theorem ext [M.Extensional] {x y : M} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y :=
  Extensional.extensional x y h

theorem eq_iff [M.Extensional] {x y : M} : x = y ↔ (∀ z, z ∈ x ↔ z ∈ y) :=
  ⟨by grind, fun h ↦ by ext; exact h _⟩

theorem eq_of_subset_of_subset [M.Extensional] {x y : M} (h : x ⊆ y) (h' : y ⊆ x) :
    x = y := by
  ext; grind

instance instAntisymmSubset [M.Extensional] : Std.Antisymm (α := M) Subset where
  antisymm := fun _ _ h h' ↦ eq_of_subset_of_subset h h'

/-- The extensionality axiom -/
def _root_.FirstOrder.Language.extensionality {L : FirstOrder.Language} [HasMem L] : L.Sentence :=
  ∀' ∀' (∀' (&2 ∈' &0 ⇔ &2 ∈' &1) ⟹ &0 =' &1)

instance (hM : M ⊨ M.L.extensionality) : M.Extensional :=
  ⟨by simpa [Sentence.Realize, Formula.Realize, extensionality] using hM⟩

end FirstOrder.Language.MemStructure
