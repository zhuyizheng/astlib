/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Axiom.Choice.Syntax
import Astlib.Basic.Axiom.ZF.Semantics
import Astlib.Basic.SetOperation.Choice
/-!
# Models of the axiom of choice

`HasChoice F` says that if `F` is a function, then it has a choice function, picking an element
of each nonempty `F ﹫ x`, and `HasDependentChoice a R` says that if every element of a nonempty
set `a` has an `R`-successor in `a`, then there is a sequence `f !: ω → a` with
`f ﹫ n [R] f ﹫ succ n`.

* The axiom of choice is `∀ F, HasChoice F` (`forall_hasChoice_iff_realize_choiceAxiom`), and
  holds in models of `ZFC` (`hasChoice`).
* Countable choice is `∀ F, dom F = ω → HasChoice F`
  (`forall_hasChoice_iff_realize_countableChoiceAxiom`), and holds in models of `ZFCC`
  (`hasChoice_of_dom_eq_omega`).
* Dependent choice is `∀ a R, HasDependentChoice a R`
  (`forall_hasDependentChoice_iff_realize_dependentChoiceAxiom`), and holds in models of `ZFDC`
  (`hasDependentChoice`).

Models of `ZFC` are models of `ZFCC` and of `ZFDC`.

Uniformization: in models of `ZF`, if every function on a set `a` has a choice function, then
every definable `P` is uniformized on `a` by a function `f` with `P ![x, f ﹫ x]` for every
`x ∈ a` having a `P`-witness (`exists_uniformization_of_hasChoice`). This holds for all `a` in
models of `ZFC` (`exists_uniformization`) and for `a = ω` in models of `ZFCC`
(`exists_uniformization_omega`).
-/

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin RudimentaryTerm MemStructure

namespace FirstOrder.Language

/-- `M` is a model of `ZFC` -/
class ModelsZFC {L : FirstOrder.Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (M : Type*) [h : L.MemStructure M] where
  modelsZFC : @Theory.Model L M h.toStructure ZFC

/-- `M` is a model of `ZF` with countable choice -/
class ModelsZFCC {L : FirstOrder.Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (M : Type*) [h : L.MemStructure M] where
  modelsZFCC : @Theory.Model L M h.toStructure ZFCC

/-- `M` is a model of `ZF` with dependent choice -/
class ModelsZFDC {L : FirstOrder.Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (M : Type*) [h : L.MemStructure M] where
  modelsZFDC : @Theory.Model L M h.toStructure ZFDC

namespace MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M]

instance [hM : ModelsZFC M] : ModelsZF M := ⟨hM.modelsZFC.mono ZF_subset_ZFC⟩

instance [hM : ModelsZFCC M] : ModelsZF M := ⟨hM.modelsZFCC.mono ZF_subset_ZFCC⟩

instance [hM : ModelsZFDC M] : ModelsZF M := ⟨hM.modelsZFDC.mono ZF_subset_ZFDC⟩

/-- `HasChoice F` in the form of the formula `isChoiceFunctionOfIsFunction` -/
theorem hasChoice_iff_realize [ModelsKP₀ M] (F : M) : HasChoice F ↔ ∃ f, IsFunction F →
    (IsFunction f ∧ dom f = dom F) ∧ ∀ x ∈ dom F, ∀ z ∈ F ﹫ x, f ﹫ x ∈ F ﹫ x := by
  refine ⟨fun h ↦ ?_, fun ⟨f, hf⟩ hF ↦ ?_⟩
  · by_cases hF : IsFunction F
    · obtain ⟨f, hf₁, hf₂, hf₃⟩ := h hF
      refine ⟨f, fun _ ↦ ⟨⟨hf₁, hf₂⟩, fun x hx z hz ↦ hf₃ x hx ?_⟩⟩
      simp only [ne_empty_iff]
      exact ⟨z, hz⟩
    · exact ⟨default, fun h' ↦ by contradiction⟩
  · obtain ⟨⟨hf₁, hf₂⟩, hf₃⟩ := hf hF
    refine ⟨f, hf₁, hf₂, fun x hx hne ↦ ?_⟩
    simp only [ne_empty_iff] at hne
    obtain ⟨z, hz⟩ := hne
    exact hf₃ x hx z hz

theorem forall_hasChoice_iff_realize_choiceAxiom [ModelsKP₀ M] :
    (∀ F : M, HasChoice F) ↔ M ⊨ (choiceAxiom : L.Sentence) := by
  rw [realize_iff_realize']
  simpa [choiceAxiom, isChoiceFunctionOfIsFunction, snoc_nat] using
    forall_congr' fun F : M ↦ hasChoice_iff_realize F

/-- In models of `ZFC`, every function has a choice function -/
theorem hasChoice [ModelsZFC M] (F : M) : HasChoice F := by
  suffices ∀ F : M, HasChoice F from this F
  rw [forall_hasChoice_iff_realize_choiceAxiom]
  exact ModelsZFC.modelsZFC.realize_of_mem _ (by simp [ZFC])

section Uniformization

variable [ModelsZF M]

/-- Uniformization from choice on `a`: if every function on `a` has a choice function, then a
definable `P` is uniformized on `a` by a function `f` with `P ![x, f ﹫ x]` for every `x ∈ a`
having a `P`-witness -/
theorem exists_uniformization_of_hasChoice (P : Multiclass M 2) [P.Definable Set.univ] {a : M}
    (hc : ∀ F : M, dom F = a → HasChoice F) :
    ∃ f, IsFunction f ∧ dom f = a ∧ ∀ x ∈ a, (∃ y, P ![x, y]) → P ![x, f ﹫ x] := by
  -- `F ![u, w]`: `w` is a `P`-witness for `u` if there is one
  let F : Multiclass M 2 := fun ys ↦ (∃ y, P ![ys 0, y]) → P ![ys 0, ys 1]
  -- by collection, the witnesses can be taken from a set `b`
  obtain ⟨b, hbF⟩ := exists_collection_of_modelsZF F a fun u _ ↦ by
    by_cases h : ∃ y, P ![u, y]
    · exact h.imp fun _ hy _ ↦ hy
    · exact ⟨u, by simp only [F]; tauto⟩
  -- a choice function for the nonempty sets `G u` of witnesses in `b`
  let G : ClassFunction M := fun u ↦ b ∩₀ fun w ↦ F ![u, w]
  have hmemG (u w : M) : w ∈ G u ↔ w ∈ b ∧ F ![u, w] := mem_comprehension_iff _ _ _
  have hGr : IsSetRestrictedTo G a :=
    isSetRestrictedTo_of_definable (G := fun u ↦ b ∩₀ fun w ↦ F ![u, w]) a
  have hGfun : IsFunction (G ↾₀ a) := isFunction_toSetRestrictedTo hGr
  specialize hc (G ↾₀ a) (dom_toSetRestrictedTo hGr)
  refine ⟨choiceFunction (G ↾₀ a), isFunction_choiceFunction hc hGfun,
    by rw [dom_choiceFunction hc hGfun, dom_toSetRestrictedTo hGr], fun x hx hP ↦ ?_⟩
  have hxdom : x ∈ dom (G ↾₀ a) := by rwa [dom_toSetRestrictedTo hGr]
  have hGne : (G ↾₀ a) ﹫ x ≠ ∅ := by
    rw [val_toSetRestrictedTo hGr hx, ne_empty_iff]
    obtain ⟨w, hw, hFw⟩ := hbF x hx
    grind
  have hchosen := choiceFunction_mem hc hGfun hxdom hGne
  rw [val_toSetRestrictedTo hGr hx, hmemG] at hchosen
  exact hchosen.right hP

/-- Uniformization in models of `ZFC`: a definable `P` is uniformized on every set `a` -/
theorem exists_uniformization [ModelsZFC M] (P : Multiclass M 2) [P.Definable Set.univ] (a : M) :
    ∃ f, IsFunction f ∧ dom f = a ∧ ∀ x ∈ a, (∃ y, P ![x, y]) → P ![x, f ﹫ x] :=
  exists_uniformization_of_hasChoice P fun F _ ↦ hasChoice F

end Uniformization

section Omega

variable [ModelsKP M] [HasOmega M]

theorem forall_hasChoice_iff_realize_countableChoiceAxiom :
    (∀ F : M, dom F = ω → HasChoice F) ↔ M ⊨ (countableChoiceAxiom : L.Sentence) := by
  suffices (∀ F : M, dom F = ω → HasChoice F) ↔ ∀ F : M, dom F = ω → ∃ f, IsFunction F →
      (IsFunction f ∧ dom f = dom F) ∧ ∀ x ∈ dom F, ∀ z ∈ F ﹫ x, f ﹫ x ∈ F ﹫ x by
    rw [realize_iff_realize']
    simpa [countableChoiceAxiom, isChoiceFunctionOfIsFunction, snoc_nat] using this
  exact forall_congr' fun F ↦ imp_congr_right fun _ ↦ hasChoice_iff_realize F

/-- In models of `ZF` with countable choice, every function on `ω` has a choice function -/
theorem hasChoice_of_dom_eq_omega [ModelsZFCC M] {F : M} (hF : dom F = ω) : HasChoice F := by
  suffices ∀ F : M, dom F = ω → HasChoice F from this F hF
  rw [forall_hasChoice_iff_realize_countableChoiceAxiom]
  exact ModelsZFCC.modelsZFCC.realize_of_mem _ (by simp [ZFCC])

/-- Uniformization in models of `ZF` with countable choice: a definable `P` is uniformized on
`ω` -/
theorem exists_uniformization_omega [ModelsZFCC M] (P : Multiclass M 2) [P.Definable Set.univ] :
    ∃ f, IsFunction f ∧ dom f = ω ∧ ∀ x ∈ (ω : M), (∃ y, P ![x, y]) → P ![x, f ﹫ x] :=
  exists_uniformization_of_hasChoice P fun _ hF ↦ hasChoice_of_dom_eq_omega hF

instance [ModelsZFC M] : ModelsZFCC M where
  modelsZFCC := by
    rw [ZFCC, Theory.model_union_iff, Theory.model_singleton_iff,
      ← forall_hasChoice_iff_realize_countableChoiceAxiom]
    exact ⟨ModelsZF.modelsZF, fun F _ ↦ hasChoice F⟩

/-- Dependent choice for `a` and `R`: if every element of a nonempty set `a` has an `R`-successor
in `a`, then there is a sequence `f !: ω → a` with `f ﹫ n [R] f ﹫ succ n` -/
def HasDependentChoice (a R : M) : Prop :=
  a ≠ ∅ → (∀ x ∈ a, ∃ y ∈ a, x [R] y) →
    ∃ f, f !: ω → a ∧ ∀ n ∈ (ω : M), (f ﹫ n) [R] (f ﹫ succ n)

theorem forall_hasDependentChoice_iff_realize_dependentChoiceAxiom :
    (∀ a R : M, HasDependentChoice a R) ↔ M ⊨ (dependentChoiceAxiom : L.Sentence) := by
  rw [realize_iff_realize']
  simp [dependentChoiceAxiom, HasDependentChoice, snoc_nat, ne_empty_iff]

/-- In models of `ZF` with dependent choice, dependent choice holds for all `a` and `R` -/
theorem hasDependentChoice [ModelsZFDC M] (a R : M) : HasDependentChoice a R := by
  suffices ∀ a R : M, HasDependentChoice a R from this a R
  rw [forall_hasDependentChoice_iff_realize_dependentChoiceAxiom]
  exact ModelsZFDC.modelsZFDC.realize_of_mem _ (by simp [ZFDC])

/-- The axiom of choice implies dependent choice -/
theorem hasDependentChoice_of_forall_hasChoice [ModelsZF M] (hc : ∀ F : M, HasChoice F)
    (a R : M) :
    HasDependentChoice a R := by
  intro ha hR
  -- `c ﹫ x` is an `R`-successor of `x` in `a`
  obtain ⟨c, -, -, hcR⟩ := exists_uniformization_of_hasChoice
    (fun ys ↦ ys 1 ∈ a ∧ (ys 0) [R] (ys 1)) (a := a) fun F _ ↦ hc F
  have hsucc {x : M} (hx : x ∈ a) : c ﹫ x ∈ a ∧ x [R] (c ﹫ x) := by
    obtain ⟨y, hy, hxy⟩ := hR x hx
    simpa using hcR x hx ⟨y, by simpa using ⟨hy, hxy⟩⟩
  -- iterate `x ↦ c ﹫ x` from some `x₀ ∈ a`
  let G : ClassFunction M := fun x ↦ c ﹫ x
  simp only [ne_empty_iff] at ha
  obtain ⟨x₀, hx₀⟩ := ha
  have hr : IsSetRestrictedTo (natRec x₀ G) ω := isSetRestrictedTo_of_sigma (G := natRec x₀ G) ω
  have hmem {n : M} (hn : n ∈ (ω : M)) : natRec x₀ G n ∈ a :=
    natRec_induction (A := fun x ↦ x ∈ a) hx₀ (fun n _ ih ↦ (hsucc ih).left) hn
  refine ⟨natRec x₀ G ↾₀ ω, isFunctionFromTo_toSetRestrictedTo hr (by grind),
    fun n hn ↦ ?_⟩
  rw [val_toSetRestrictedTo hr hn, val_toSetRestrictedTo hr (succ_mem_omega hn),
    natRec_succ _ _ (by grind)]
  exact (hsucc (hmem hn)).right

instance [ModelsZFC M] : ModelsZFDC M where
  modelsZFDC := by
    rw [ZFDC, Theory.model_union_iff, Theory.model_singleton_iff,
      ← forall_hasDependentChoice_iff_realize_dependentChoiceAxiom]
    exact ⟨ModelsZF.modelsZF, hasDependentChoice_of_forall_hasChoice hasChoice⟩

end Omega

end MemStructure

end FirstOrder.Language
