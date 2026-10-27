/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Comprehension
/-!
file docstring
-/

open Fin FirstOrder Language MemStructure

namespace FirstOrder.Language

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M]

namespace MemStructure

def IsReplacement (b : M) (F : Multiclass M 2) (a : M) := ∀ z, z ∈ b ↔ ∃ u ∈ a, F ![u, z]

noncomputable instance (F : Multiclass M 2) (a : M) :
  Decidable (∃ b : M, IsReplacement b F a) :=
  Classical.propDecidable _

/-- The pointwise image `{F u | u ∈ a}` of `a` under `F` -/
noncomputable def replacement (a : M) (F : Multiclass M 2) :=
  dite (∃ b : M, IsReplacement b F a)
    Classical.choose default

@[inherit_doc] scoped[FirstOrder.Language]
notation:88 F:89 " ''₀ " a:89 => FirstOrder.Language.MemStructure.replacement a F

/-- If `F` relates every `u ∈ a` to exactly one `w`, then the image `{F u | u ∈ a}` is a set -/
class HasReplacement (a : M) (F : Multiclass M 2) : Prop where
  protected hasReplacement : (∀ u ∈ a, ∃! w, F ![u, w]) → ∃ b : M, IsReplacement b F a

theorem mem_replacement_iff {a : M} {F : Multiclass M 2} [hF : HasReplacement a F]
    (hFa : ∀ u ∈ a, ∃! w, F ![u, w]) (z : M) :
    z ∈ F ''₀ a ↔ ∃ u ∈ a, F ![u, z] := by
  convert Classical.choose_spec (hF.hasReplacement hFa) z
  simp [MemStructure.replacement, hF.hasReplacement hFa]

theorem mem_replacement_of_mem {a : M} {F : Multiclass M 2} [HasReplacement a F]
    (hFa : ∀ u ∈ a, ∃! w, F ![u, w]) {u w : M} (hu : u ∈ a) (hw : F ![u, w]) :
    w ∈ F ''₀ a := by
  simp only [mem_replacement_iff hFa]
  exact ⟨u, hu, hw⟩

end MemStructure

namespace MemStructure

section KP

open BoundedFormula

variable [L.ExtraConstantsUnaryRelationsOnly]

/-- `Δ₀`-replacement -/
instance [ModelsKP₀ M] (x : M) (F : Multiclass M 2) [hF : F.DeltaZero Set.univ] :
  HasReplacement x F where
  hasReplacement hFx := by
    obtain ⟨m, φ, hφ, vs, -, rfl⟩ := hF.isDeltaZero
    obtain ⟨b, hb⟩ := exists_collection_of_modelsKP (φ.multiclass.slice vs) x
      (fun u hu ↦ (hFx u hu).exists)
    -- `χ(z, vs, x)` says `∃ u ∈ x, φ(u, z, vs)`
    let χ : L.BoundedFormula' (1 + (m + 1)) := ∃'∈ &-1
      φ.castAssoc.switchBound.substBoundBound (snoc (castAdd 2) (last (1 + m + 1)))
    refine ⟨b ∩₀ χ.multiclass.slice (snoc vs x), fun z ↦ ?_⟩
    simp only [mem_comprehension_iff, Multiclass.toClass_iff]
    simp only [Multiclass.slice, BoundedFormula.multiclass, χ, append_snoc,
      BoundedFormula.realize_exMem, realize'_substBoundBound, Term.realize'_var', snoc_last,
      snoc_snoc_comp_snoc_castAdd_two_last, Function.comp_apply, Nat.add_eq]
    simp only [snoc_eq_append, realize'_switchBound, realize'_castAssoc]
    simp only [append_left_eq_cons, Fin.cast_refl, Function.comp_id]
    simp only [Multiclass.slice, BoundedFormula.multiclass] at hb hFx
    refine ⟨fun ⟨_, u, hu, hz⟩ ↦ ⟨u, hu, hz⟩, fun ⟨u, hu, hz⟩ ↦ ⟨?_, u, hu, hz⟩⟩
    obtain ⟨w, hwb, hw⟩ := hb u hu
    rwa [(hFx u hu).unique hz hw]

end KP

end MemStructure

end FirstOrder.Language
