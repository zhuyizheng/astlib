import Astlib.Basic.SetOperation.Function

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y : M)

noncomputable instance : Decidable
  (∃ f, IsFunction f ∧ dom f = dom F ∧ ∀ x ∈ dom F, F ﹫ x ≠ ∅ → f ﹫ x ∈ F ﹫ x) :=
  Classical.propDecidable _

noncomputable def choice (F : M) := dite
  (∃ f, IsFunction f ∧ dom f = dom F ∧ ∀ x ∈ dom F, F ﹫ x ≠ ∅ → f ﹫ x ∈ F ﹫ x)
  Classical.choose default

variable (M) in
/- `M` is closed under `⋃` -/
class ClosedUnderChoice : Prop where
  protected choice_prop : ∀ (F : M), IsFunction F →
    IsFunction (choice F) ∧ dom (choice F) = dom F ∧ ∀ x ∈ dom F, F ﹫ x ≠ ∅ → (choice F) ﹫ x ∈ F ﹫ x

noncomputable instance instClosedUnderChoice
    (h : ∀ F : M, IsFunction F →
      ∃ f, IsFunction f ∧ dom f = dom F ∧ ∀ x ∈ dom F, F ﹫ x ≠ ∅ → f ﹫ x ∈ F ﹫ x) :
    M.ClosedUnderChoice :=
  ⟨fun F hF ↦ by
    specialize h F hF
    suffices choice F = Classical.choose h by convert Classical.choose_spec h
    simp only [choice]; split_ifs; simp⟩

@[simp, grind .]
theorem isFunction_choice [ClosedUnderChoice M] {F : M} (hF : IsFunction F) :
    IsFunction (choice F) :=
  ClosedUnderChoice.choice_prop F hF |>.left

@[simp, grind .]
theorem dom_choice [ClosedUnderChoice M] {F : M} (hF : IsFunction F) :
    dom (choice F) = dom F :=
  ClosedUnderChoice.choice_prop F hF |>.right.left

@[simp, grind .]
theorem choice_mem [ClosedUnderChoice M] {F x : M} (hF : IsFunction F)
    (hx : x ∈ dom F) (hFx : F ﹫ x ≠ ∅) :
    (choice F) ﹫ x ∈ F ﹫ x :=
  ClosedUnderChoice.choice_prop F hF |>.right.right x hx hFx

end FirstOrder.Language.MemStructure
