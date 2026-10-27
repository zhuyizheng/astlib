/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Function
/-!
file docstring
-/

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] (x y : M)

def IsChoiceFunction (f F : M) :=
  IsFunction f ∧ dom f = dom F ∧ ∀ x ∈ dom F, F ﹫ x ≠ ∅ → f ﹫ x ∈ F ﹫ x

noncomputable instance (F : M) : Decidable
  (∃ f, IsChoiceFunction f F) :=
  Classical.propDecidable _

noncomputable def choiceFunction : ClassFunction M := fun F ↦
  dite (∃ f, IsChoiceFunction f F) Classical.choose default

/-- `F` has a choice function if it is a function: a function picking an element of each
nonempty `F ﹫ x` -/
def HasChoice (F : M) : Prop := IsFunction F → ∃ f, IsChoiceFunction f F

@[simp, grind .]
theorem isChoiceFunction_choiceFunction {F : M} (hc : HasChoice F) (hF : IsFunction F) :
    IsChoiceFunction (choiceFunction F) F := by
  simp only [choiceFunction, hc hF, ↓reduceDIte]
  grind

@[simp, grind .]
theorem isFunction_choiceFunction {F : M} (hc : HasChoice F) (hF : IsFunction F) :
    IsFunction (choiceFunction F) := by
  grind [IsChoiceFunction, isChoiceFunction_choiceFunction]

@[simp, grind .]
theorem dom_choiceFunction {F : M} (hc : HasChoice F) (hF : IsFunction F) :
    dom (choiceFunction F) = dom F :=
  isChoiceFunction_choiceFunction hc hF |>.right.left

@[simp, grind .]
theorem choiceFunction_mem {F x : M} (hc : HasChoice F) (hF : IsFunction F)
    (hx : x ∈ dom F) (hFx : F ﹫ x ≠ ∅) :
    (choiceFunction F) ﹫ x ∈ F ﹫ x :=
  isChoiceFunction_choiceFunction hc hF |>.right.right x hx hFx

/-- Every set of nonempty sets has a choice function -/
theorem exists_val_mem_of_ne_empty [Extensional M] [RudClosed M] {x : M} (hc : HasChoice (id x))
    (hx : ∀ y ∈ x, y ≠ ∅) : ∃ c, ∀ y ∈ x, c ﹫ y ∈ y := by
  refine ⟨choiceFunction (id x), fun y hy ↦ ?_⟩
  have h := choiceFunction_mem hc (isFunction_id x) (by rwa [dom_id])
    (by simpa [id_val x hy] using hx y hy)
  rwa [id_val x hy] at h

end FirstOrder.Language.MemStructure
