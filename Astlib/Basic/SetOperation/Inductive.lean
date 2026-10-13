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

variable {L : Language.{u, v}} {M : Type max u v}
  [L.MemStructure M]
  -- [L.ExtraConstantsUnaryRelationsOnly]
  [Inhabited M] (x y : M)

def IsInductive (a : M) :=
   ∅ ∈ a ∧ ∀ x ∈ a, succ x ∈ a

noncomputable instance : Decidable
  (∃ a : M, IsInductive a ∧ ∀ x, IsInductive x → a ⊆ x) :=
  Classical.propDecidable _

noncomputable def minInductive :=
  dite (∃ a : M, IsInductive a ∧ ∀ x, IsInductive x → a ⊆ x) Classical.choose default

notation:max "ω" => minInductive

variable (M) in
/- `M` is closed under `⋃` -/
class HasInductive : Prop where
  protected hasInductive :
    ∃ a : M, IsInductive a

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.isInductive
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r : L.RudimentaryTerm n) :
  L.DeltaZeroBoundedFormula n :=
  (∃₀∈ &0 (&0 =₀ &1).substBoundRud ![ᵣ1, ∅]) ⊓ ∀₀∈ &0 (&1 ∈₀ &0).substBoundRud ![ᵣ0, (ᵣ1).succ] |>.substBoundRud ![r]


-- @[simp, grind .]
-- theorem minInductive_of_hasInductive [HasInductive M] :
--      (IsInductive (ω : M)) ∧  ∀ x : M, IsInductive x → ω ⊆ x := by
--   simp only [minInductive, HasInductive.hasInductive, ↓reduceDIte]
--   grind
theorem minInductive_of_hasInductive_aux [h : HasInductive M] :
    ∃ a : M, IsInductive a ∧ ∀ x, IsInductive x → a ⊆ x := by
  obtain ⟨b, hb⟩ := h.hasInductive
  sorry


theorem minInductive_of_hasInductive [h : HasInductive M] :
     (IsInductive (ω : M)) ∧ ∀ x : M, IsInductive x → ω ⊆ x := by
  convert Classical.choose_spec minInductive_of_hasInductive_aux
  · simp [minInductive, minInductive_of_hasInductive_aux]
  · simp [minInductive, minInductive_of_hasInductive_aux]
  · exact h

  -- simp only [minInductive, HasInductive.hasInductive, ↓reduceDIte]
  -- grind

-- @[simp, grind .]
-- theorem isFunction_choiceFunction [ClosedUnderChoice M] {F : M} (hF : IsFunction F) :
--     IsFunction (choiceFunction F) := by
--   grind [IsChoiceFunction, isChoiceFunction_choiceFunction]

-- @[simp, grind .]
-- theorem dom_choiceFunction [ClosedUnderChoice M] {F : M} (hF : IsFunction F) :
--     dom (choiceFunction F) = dom F :=
--   isChoiceFunction_choiceFunction hF |>.right.left

-- @[simp, grind .]
-- theorem choiceFunction_mem [ClosedUnderChoice M] {F x : M} (hF : IsFunction F)
--     (hx : x ∈ dom F) (hFx : F ﹫ x ≠ ∅) :
--     (choiceFunction F) ﹫ x ∈ F ﹫ x :=
--   isChoiceFunction_choiceFunction hF |>.right.right x hx hFx

end FirstOrder.Language.MemStructure
