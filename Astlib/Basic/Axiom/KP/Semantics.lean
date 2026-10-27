/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Axiom.KP.Syntax
import Astlib.Basic.SetOperation.Multiclass.Lambda
import Astlib.Basic.SetOperation.MemStructure.Semantics
/-!
file docstring
-/

namespace FirstOrder

namespace Language

open FirstOrder Language BoundedFormula Fin MemStructure

variable {L : FirstOrder.Language} {M : Type*}
  [L.MemStructure M] [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M]

class ModelsKP {L : FirstOrder.Language} (M : Type*) [h : L.MemStructure M] where
  modelsKP : @Theory.Model L M h.toStructure KP

/-- `M` is a model of `KP₀`, i.e. of `KP` without the `∈`-induction schema -/
class ModelsKP₀ {L : FirstOrder.Language} (M : Type*) [h : L.MemStructure M] where
  modelsKP₀ : @Theory.Model L M h.toStructure KP₀

instance [hM : ModelsKP M] : ModelsKP₀ M := ⟨hM.modelsKP.mono KP₀_subset_KP⟩

/-- `M` is a model of `KP` with the axiom of infinity -/
class ModelsKPInf {L : FirstOrder.Language} (M : Type*) [h : L.MemStructure M] where
  modelsKPInf : @Theory.Model L M h.toStructure KPInf

instance [hM : ModelsKPInf M] : ModelsKP M := ⟨hM.modelsKPInf.mono KP_subset_KPInf⟩

/-- Δ₀-collection -/
theorem MemStructure.exists_collection_of_modelsKP [hM : ModelsKP₀ M] (F : Multiclass M 2)
    [hF : F.DeltaZero Set.univ] (a : M) (h : ∀ u ∈ a, ∃ w, F ![u, w]) :
    ∃ b : M, ∀ u ∈ a, ∃ w ∈ b, F ![u, w] := by
  obtain ⟨n, φ, hφ, vs, -, rfl⟩ := hF.isDeltaZero
  have hφ' (u w : M) : (φ.multiclass.slice vs : Multiclass M 2) ![u, w] ↔
      φ.switchBound〘snoc (snoc vs u) w〙 := by
    simp [snoc_snoc_eq_append]
  simp only [hφ'] at h ⊢
  replace hM := hM.modelsKP₀
  simp only [KP₀, Theory.model_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    realize_iff_realize'] at hM
  have : φ.switchBound.collection ∈ deltaZeroCollectionSchema :=
    ⟨n, φ.switchBound, by infer_instance, rfl⟩
  specialize hM φ.switchBound.collection (by simp [this])
  simp only [BoundedFormula.collection, realize'_alls, realize'_ex, realize'_imp,
    BoundedFormula.realize_allMem, BoundedFormula.realize_exMem, realize'_substBoundBound] at hM
  simpa using hM (snoc vs a) (by simpa using h)

end Language

end FirstOrder
