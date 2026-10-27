/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.PrimitiveRecursive.Semantics
/-!
# Transitive closure

The transitive closure `tc x = x ∪ ⋃_{y ∈ x} tc y`, defined by a primitive recursive term, is the
smallest transitive set containing `x` as a subset.
-/
open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula PrimitiveRecursiveTerm Fin
  MemStructure

namespace FirstOrder.Language

/-- The transitive closure, defined by recursion with step `f ↦ dom f ∪ ⋃₀ ran f` -/
noncomputable def PrimitiveRecursiveTerm.tc₀ {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.PrimitiveRecursiveTerm 1 :=
  recursion ((ᵣ0).dom ∪ ᵣ⋃₀ (ᵣ0).ran).toPrimitiveRecursiveTerm

namespace MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M]

/-- The transitive closure `tc x = x ∪ ⋃_{y ∈ x} tc y` -/
noncomputable def tc : ClassFunction M := fun x ↦ tc₀〘x〙₁

omit [ModelsKP M] in
theorem tc_eq_realize : (tc : ClassFunction M) = fun y ↦ (tc₀〘snoc ![] y〙 : M) := by
  funext
  simp [tc]

instance : ClassFunction.Sigma (tc : ClassFunction M) 1 Set.univ := by
  unfold tc
  infer_instance

theorem tc_eq (x : M) : tc x = x ∪ ⋃₀ ran (tc ↾₀ x) := by
  have := realize_recursion (xs := ![x])
    (rg := ((ᵣ0).dom ∪ ᵣ⋃₀ (ᵣ0).ran).toPrimitiveRecursiveTerm)
  rw [Subsingleton.elim (![x] ∘ Fin.castSucc) ![], ← tc₀, ← tc_eq_realize] at this
  refine this.trans ?_
  simp [isSetRestrictedTo_of_modelsKP]

theorem mem_tc_iff {x z : M} : z ∈ tc x ↔ z ∈ x ∨ ∃ y ∈ x, z ∈ tc y := by
  rw [tc_eq]
  simp [isSetRestrictedTo_of_modelsKP]

@[grind .]
theorem subset_tc (x : M) : x ⊆ tc x := by grind [mem_tc_iff]

@[simp, grind .]
theorem transitive_tc (x : M) : Transitive (tc x) := by
  refine induction_of_modelsKP (A := fun x ↦ Transitive (tc x)) (fun x ih z hz w hw ↦ ?_) x
  rw [mem_tc_iff] at hz ⊢
  rcases hz with hz | ⟨y, hy, hzy⟩
  · exact .inr ⟨z, hz, subset_tc z hw⟩
  · exact .inr ⟨y, hy, ih y hy z hzy hw⟩

/-- `tc x` is the smallest transitive set containing `x` as a subset -/
theorem tc_subset {x t : M} (ht : Transitive t) (hxt : x ⊆ t) : tc x ⊆ t := by
  revert hxt
  refine induction_of_modelsKP (A := fun x ↦ x ⊆ t → tc x ⊆ t) (fun x ih ↦ ?_) x
  grind [mem_tc_iff]

@[simp, grind =]
theorem tc_eq_self {x : M} (hx : Transitive x) : tc x = x :=
  eq_of_subset_of_subset (tc_subset hx (subset_refl _)) (subset_tc _)

end MemStructure

end FirstOrder.Language
