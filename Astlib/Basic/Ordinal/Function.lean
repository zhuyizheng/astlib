/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Ordinal.Order
/-!
# Functions on ordinals

In models of `KP`, a surjection `f` from an ordinal `β` onto `b` gives the injection
`leastInv f β b` from `b` into `β`, sending `y` to its least preimage `leastPreimage f β y`
(`IsSurjectionFromTo.leastInv`).
-/

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin RudimentaryTerm MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] {β f : M}

/-- The least `x ∈ β` with `f ﹫ x = y`, or `∅` if there is none -/
noncomputable def leastPreimage (f β : M) : ClassFunction M :=
  fun y ↦ Class.omin fun x ↦ x ∈ β ∧ f ﹫ x = y

theorem definable_preimageIn (f β y : M) :
    Class.Definable (fun x ↦ x ∈ β ∧ f ﹫ x = y : Class M) Set.univ :=
  inferInstance

/-- If `y` has a preimage in `β`, then `leastPreimage f β y` is its least preimage in `β` -/
theorem leastPreimage_spec {x y : M} (hβ : Ordinal β) (hx : x ∈ β) (hxy : f ﹫ x = y) :
    leastPreimage f β y ∈ β ∧ f ﹫ leastPreimage f β y = y ∧
      ∀ z ∈ leastPreimage f β y, f ﹫ z ≠ y := by
  have := definable_preimageIn f β y
  obtain ⟨-, ⟨hβ', hy⟩, hmin⟩ :=
    Class.omin_spec (A := fun x ↦ x ∈ β ∧ f ﹫ x = y) (ordinal_of_mem hβ hx) ⟨hx, hxy⟩
  exact ⟨hβ', hy, fun z hz hzy ↦ hmin z hz ⟨hβ.transitive _ hβ' hz, hzy⟩⟩

/-- A least preimage `w ∈ β` of `y` is `leastPreimage f β y` -/
theorem leastPreimage_eq {y w : M} (hβ : Ordinal β) (hw : w ∈ β) (hwy : f ﹫ w = y)
    (hmin : ∀ x ∈ w, f ﹫ x ≠ y) : leastPreimage f β y = w :=
  have := definable_preimageIn f β y
  Class.omin_eq (ordinal_of_mem hβ hw) ⟨hw, hwy⟩ fun x hx hPx ↦ hmin x hx hPx.right

omit [ModelsKP M] in
theorem leastPreimage_eq_empty {y : M} (h : ∀ x ∈ β, f ﹫ x ≠ y) : leastPreimage f β y = ∅ :=
  Class.omin_eq_empty fun x _ hPx ↦ h x hPx.left hPx.right

theorem sigma_leastPreimage (hβ : Ordinal β) : (leastPreimage f β).Sigma 1 Set.univ := by
  -- `[y, w, β, f]`: `w` is the least `x ∈ β` with `f ﹫ x = y` if there is one, else `∅`
  let χ : L.DeltaZeroBoundedFormula 4 := ∃₀∈ &2 ((&0 =₀ &1).substBoundRud ![(ᵣ3) ﹫ (ᵣ4), ᵣ0])
  let φ : L.DeltaZeroBoundedFormula 4 :=
    (&1 ∈₀ &2 ⊓ (&0 =₀ &1).substBoundRud ![(ᵣ3) ﹫ (ᵣ1), ᵣ0] ⊓
      ∀₀∈ &1 ∼((&0 =₀ &1).substBoundRud ![(ᵣ3) ﹫ (ᵣ4), ᵣ0])) ⊔
    (∼χ ⊓ (&0 =₀ &1).substBoundRud ![ᵣ1, ∅])
  refine ClassFunction.Sigma.of_iff (F := φ.toBoundedFormula.multiclass.slice ![β, f])
    fun y w ↦ ?_
  suffices leastPreimage f β y = w ↔
      (w ∈ β ∧ f ﹫ w = y ∧ ∀ x ∈ w, f ﹫ x ≠ y) ∨ ((∀ x ∈ β, f ﹫ x ≠ y) ∧ w = ∅) by
    simp [this, φ, χ, Multiclass.slice, and_assoc]
  grind [leastPreimage_spec, leastPreimage_eq, leastPreimage_eq_empty]

/-- The inverse on `b` of `f` sending `y` to its least preimage in `β` -/
noncomputable def leastInv (f β b : M) : M := leastPreimage f β ↾₀ b

/-- A surjection from an ordinal `β` onto `b` gives an injection `leastInv f β b` from `b` into
`β` -/
theorem IsSurjectionFromTo.leastInv {b : M} (hβ : Ordinal β) (hf : f !: β ↠ b) :
    MemStructure.leastInv f β b !: b ↪ β := by
  have := sigma_leastPreimage (f := f) hβ
  have hGb {y : M} (hy : y ∈ b) : leastPreimage f β y ∈ β ∧ f ﹫ leastPreimage f β y = y := by
    obtain ⟨x, hx, hxy⟩ := hf.exists_mem_val hy
    obtain ⟨h₁, h₂, -⟩ := leastPreimage_spec hβ hx hxy
    exact ⟨h₁, h₂⟩
  refine isInjectionFromTo_toSetRestrictedTo (isSetRestrictedTo_of_sigma b)
    (fun y hy ↦ (hGb hy).left) fun y hy y' hy' h ↦ ?_
  rw [← (hGb hy).right, ← (hGb hy').right, h]

end FirstOrder.Language.MemStructure
