import Astlib.Basic.SetOperation.Function

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y : M)

abbrev IsChoiceFunction (f F : M) :=
  IsFunction f ∧ dom f = dom F ∧ ∀ x ∈ dom F, F ﹫ x ≠ ∅ → f ﹫ x ∈ F ﹫ x

noncomputable instance : Decidable
  (∃ f, IsChoiceFunction f F) :=
  Classical.propDecidable _

noncomputable def choiceFunction (F : M) :=
  dite (∃ f, IsChoiceFunction f F) Classical.choose default

variable (M) in
/- `M` is closed under `⋃` -/
class ClosedUnderChoice : Prop where
  protected closedUnderChoice : ∀ (F : M), IsFunction F →
    ∃ f, IsChoiceFunction f F

@[simp, grind .]
theorem isChoiceFunction_choiceFunction [ClosedUnderChoice M] {F : M} (hF : IsFunction F) :
    IsChoiceFunction (choiceFunction F) F := by
  simp only [choiceFunction, ClosedUnderChoice.closedUnderChoice F hF, ↓reduceDIte]
  grind

@[simp, grind .]
theorem isFunction_choiceFunction [ClosedUnderChoice M] {F : M} (hF : IsFunction F) :
    IsFunction (choiceFunction F) := by
  grind

@[simp, grind .]
theorem dom_choiceFunction [ClosedUnderChoice M] {F : M} (hF : IsFunction F) :
    dom (choiceFunction F) = dom F :=
  isChoiceFunction_choiceFunction hF |>.right.left

@[simp, grind .]
theorem choiceFunction_mem [ClosedUnderChoice M] {F x : M} (hF : IsFunction F)
    (hx : x ∈ dom F) (hFx : F ﹫ x ≠ ∅) :
    (choiceFunction F) ﹫ x ∈ F ﹫ x :=
  isChoiceFunction_choiceFunction hF |>.right.right x hx hFx

end FirstOrder.Language.MemStructure
