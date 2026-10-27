/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Ordinal.Omega
/-!
# Clubs and stationary sets

For a set `S` and an ordinal `α`, in models of `KP`:

* `UnboundedInOrd S α`: every `γ <ₒ α` is below some element of `S`;
* `IsLimitPoint S γ`: `γ` is a nonzero limit ordinal and `S ∩ γ` is unbounded in `γ`;
  `limitPoints S` is the set of limit points of a set `S` of ordinals (`mem_limitPoints_iff`);
* `ClosedInOrd S α`: `S ⊆ α` and `S` contains its limit points below `α`. The intersection of two
  closed sets is closed (`ClosedInOrd.inter`);
* `ClubInOrd S α`: `S` is closed and unbounded in `α`;
* `StationaryInOrd S α`: `S ⊆ α` and `S` meets every club in `α`;
* `next S x`: the least element of `S` above `x`, a `Σ₁` class function.
-/

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin RudimentaryTerm MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] {S T α γ δ x : M}

section UnboundedInOrd

/-- `S` is unbounded in `α`: every `γ <ₒ α` is below some element of `S` -/
def UnboundedInOrd (S α : M) : Prop := ∀ γ ∈ α, ∃ ξ ∈ S, γ ≤ₒ ξ

instance : Multiclass.DeltaZero (fun ys : Fin 2 → M ↦ UnboundedInOrd (ys 0) (ys 1)) Set.univ := by
  unfold UnboundedInOrd
  infer_instance

theorem unboundedInOrd_iff (hα : Ordinal α) : UnboundedInOrd S α ↔ ∀ γ <ₒ α, ∃ ξ ∈ S, γ ≤ₒ ξ := by
  unfold UnboundedInOrd
  grind

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] in
theorem UnboundedInOrd.exists_ole (hS : UnboundedInOrd S α) (hγ : γ <ₒ α) : ∃ ξ ∈ S, γ ≤ₒ ξ :=
  hS γ hγ.mem

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] in
/-- A superset of an unbounded set is unbounded -/
theorem UnboundedInOrd.mono (hS : UnboundedInOrd S α) (h : S ⊆ T) : UnboundedInOrd T α := by
  intro γ hγ
  obtain ⟨ξ, hξ, hγξ⟩ := hS γ hγ
  exact ⟨ξ, h hξ, hγξ⟩

end UnboundedInOrd

section LimitPoint

/-- `γ` is a limit point of `S`: a nonzero limit ordinal with `S ∩ γ` unbounded in `γ` -/
def IsLimitPoint (S γ : M) : Prop := NonZeroLimOrdinal γ ∧ UnboundedInOrd (S ∩ γ) γ

instance : Multiclass.DeltaZero (fun ys : Fin 2 → M ↦ IsLimitPoint (ys 0) (ys 1)) Set.univ := by
  unfold IsLimitPoint UnboundedInOrd
  infer_instance

/-- A limit point of a subset is a limit point -/
theorem IsLimitPoint.mono (hγ : IsLimitPoint S γ) (h : S ⊆ T) : IsLimitPoint T γ := by
  refine ⟨hγ.left, hγ.right.mono fun ξ hξ ↦ ?_⟩
  simp only [mem_inter_iff] at hξ ⊢
  exact ⟨h hξ.left, hξ.right⟩

/-- The set of limit points of a set `S` of ordinals -/
noncomputable def limitPoints (S : M) : M := succ (osup S) ∩₀ IsLimitPoint S

/-- A limit point of a set of ordinals is at most its supremum -/
theorem IsLimitPoint.ole_osup (hS : ∀ x ∈ S, Ordinal x) (hγ : IsLimitPoint S γ) :
    γ ≤ₒ osup S := by
  have hγo := hγ.left.ordinal
  simp only [← not_olt_iff (ordinal_osup hS) hγo]
  intro hlt
  obtain ⟨ξ, hξ, hle⟩ := hγ.right.exists_ole (hγ.left.succ_olt hlt)
  have hξS : ξ ∈ S := (mem_inter_iff _ _ _).mp hξ |>.left
  have := MemStructure.ole_osup hS hξS
  grind

theorem mem_limitPoints_iff (hS : ∀ x ∈ S, Ordinal x) : γ ∈ limitPoints S ↔ IsLimitPoint S γ := by
  simp only [limitPoints, mem_comprehension_iff, and_iff_right_iff_imp]
  intro hγ
  rcases mem_or_eq_of_ole (hγ.ole_osup hS) with h | h <;> grind

end LimitPoint

section ClosedInOrd

/-- `S` is closed in `α`: `S ⊆ α` and `S` contains its limit points below `α` -/
def ClosedInOrd (S α : M) : Prop := S ⊆ α ∧ limitPoints S ∩ α ⊆ S

theorem closedInOrd_iff (hα : Ordinal α) :
    ClosedInOrd S α ↔ S ⊆ α ∧ ∀ γ <ₒ α, IsLimitPoint S γ → γ ∈ S := by
  refine and_congr_right fun hSα ↦ ?_
  have hS : ∀ x ∈ S, Ordinal x := fun x hx ↦ ordinal_of_mem hα (hSα hx)
  refine ⟨fun h γ hγ hlim ↦ h ?_, fun h γ hγ ↦ ?_⟩
  · simp only [mem_inter_iff, mem_limitPoints_iff hS]
    exact ⟨hlim, hγ.mem⟩
  · simp only [mem_inter_iff, mem_limitPoints_iff hS] at hγ
    exact h γ (olt_of_mem hα hγ.right) hγ.left

/-- A closed set contains its limit points below `α` -/
@[grind .]
theorem ClosedInOrd.mem_of_isLimitPoint (hα : Ordinal α) (hS : ClosedInOrd S α) (hγ : γ <ₒ α)
    (hlim : IsLimitPoint S γ) : γ ∈ S :=
  ((closedInOrd_iff hα).mp hS).right γ hγ hlim

/-- The intersection of two closed sets is closed -/
@[grind .]
theorem ClosedInOrd.inter (hα : Ordinal α) (hS : ClosedInOrd S α) (hT : ClosedInOrd T α) :
    ClosedInOrd (S ∩ T) α := by
  simp only [closedInOrd_iff hα] at hS hT ⊢
  refine ⟨fun x hx ↦ by grind, fun γ hγ hlim ↦ ?_⟩
  simp only [mem_inter_iff]
  exact ⟨hS.right γ hγ (hlim.mono (by grind)), hT.right γ hγ (hlim.mono (by grind))⟩

end ClosedInOrd

/-- `S` is a club in `α`: closed and unbounded in `α` -/
def ClubInOrd (S α : M) : Prop := ClosedInOrd S α ∧ UnboundedInOrd S α

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
@[grind .]
theorem ClubInOrd.closedInOrd (hS : ClubInOrd S α) : ClosedInOrd S α := hS.left

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
@[grind .]
theorem ClubInOrd.unboundedInOrd (hS : ClubInOrd S α) : UnboundedInOrd S α := hS.right

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
@[grind .]
theorem ClubInOrd.subset (hS : ClubInOrd S α) : S ⊆ α := hS.left.left

/-- `S` is stationary in `α`: `S ⊆ α` and `S` meets every club in `α` -/
def StationaryInOrd (S α : M) : Prop := S ⊆ α ∧ ∀ C, ClubInOrd C α → S ∩ C ≠ ∅

section Next

/-- The least element of `S` above `x` -/
noncomputable def next (S x : M) : M := Class.omin fun ξ ↦ ξ ∈ S ∧ x <ₒ ξ

/-- `next S x` is an element of `S` above `x` if there is one -/
theorem next_spec (h : ∃ ξ ∈ S, x <ₒ ξ) : next S x ∈ S ∧ x <ₒ next S x := by
  obtain ⟨ξ, hξ, hxξ⟩ := h
  exact Class.omin_mem (A := fun ξ ↦ ξ ∈ S ∧ x <ₒ ξ) hxξ.ordinal_right ⟨hξ, hxξ⟩

@[grind .]
theorem next_mem (h : ∃ ξ ∈ S, x <ₒ ξ) : next S x ∈ S := (next_spec h).left

@[grind .]
theorem olt_next (h : ∃ ξ ∈ S, x <ₒ ξ) : x <ₒ next S x := (next_spec h).right

/-- `next S x` is the least element of `S` above `x` -/
theorem next_ole (hξ : δ ∈ S) (hxξ : x <ₒ δ) : next S x ≤ₒ δ :=
  Class.omin_ole (A := fun ξ ↦ ξ ∈ S ∧ x <ₒ ξ) hxξ.ordinal_right ⟨hξ, hxξ⟩

/-- `next S` is `Σ₁` -/
instance (S : M) : ClassFunction.Sigma (next S) 1 Set.univ := by
  unfold next
  infer_instance

end Next

end FirstOrder.Language.MemStructure
