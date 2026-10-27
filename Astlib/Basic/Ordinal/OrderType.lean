/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Order.StrictWellOrder
import Astlib.Basic.Ordinal.Order
import Astlib.Basic.SetOperation.PrimitiveRecursive.Semantics
/-!
# Order types of sets of ordinals

For a set `S` of ordinals, `memRelOn S` is the relation `∈` on `S`, a strict well-order on `S`
that is well-founded for definable classes. Its collapse `otMap S` is the isomorphism from `S`
onto the ordinal `ot S`, the order type of `S`.

* `IsOrderHomOn.ot_ran`: if `f` is an order homomorphism from the ordinal `a`, then the order
  type of its range is `a`; `IsOrderHom.ot_ran` is the version for order homomorphisms of the
  ordinals.
* `ot_ole`: the order type of a subset of an ordinal `α` is at most `α`.
* `otMap_val_eq_ot`: `otMap S ﹫ x` is the order type of the image of the predecessors of
  `x`.
-/

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin MemStructure

namespace FirstOrder.Language

/-- `memRelOn₀〘S〙` is `{z ∈ S ×ˢ S | left z ∈ right z}` -/
noncomputable def RudimentaryTerm.memRelOn₀ {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 1 :=
  ((&0 ∈₀ &1).substBoundRud ![(ᵣ0).left, (ᵣ0).right] :
    L.DeltaZeroBoundedFormula 1).comprehensionRudimentaryTerm.substBoundRud
    ![(ᵣ0 : L.RudimentaryTerm 1) ×ˢ (ᵣ0 : L.RudimentaryTerm 1)]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (RudimentaryTerm.memRelOn₀ : L.RudimentaryTerm 1).CharFree := by
  unfold RudimentaryTerm.memRelOn₀
  infer_instance

namespace MemStructure

open RudimentaryTerm

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] {S a b x y z : M}

/-- The relation `∈` on a set `S` -/
noncomputable def memRelOn : ClassFunction M := fun S ↦ memRelOn₀〘S〙₁

instance : (memRelOn : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq memRelOn₀ fun _ ↦ rfl

theorem mem_memRelOn_iff : z ∈ memRelOn S ↔ z ∈ S ×ˢ S ∧ left z ∈ right z := by
  simp [memRelOn, memRelOn₀]

@[simp]
theorem rel_memRelOn_iff : y [memRelOn S] x ↔ (y ∈ S ∧ x ∈ S) ∧ y ∈ x := by
  simp [mem_memRelOn_iff]

theorem isRelationOn_memRelOn (S : M) : IsRelationOn (memRelOn S) S := by
  refine (isRelationOn_sprod S).subset fun _ hz ↦ ?_
  simp only [mem_memRelOn_iff] at hz
  exact hz.left

/-- `∈` on a set is well-founded, also for definable classes -/
theorem isStrictWellFounded₀_memRelOn (S : M) : IsStrictWellFounded₀ (memRelOn S) S := by
  refine Multiclass.IsStrictWellFounded₀.isStrictWellFounded₀ ?_ (isRelationOn_memRelOn S)
  intro A _ hA
  obtain ⟨x, hx, hmin⟩ := isStrictWellFounded₀_memRel A hA
  refine ⟨x, hx, fun y hy ↦ hmin y ?_⟩
  simp only [Multiclass.ofRel_iff, rel_memRelOn_iff] at hy
  simp only [memRel_iff x y]
  exact hy.right

/-- A set relation `R` on `a` is well-founded, also for definable classes, if a `Σ₁` class
function `F` maps it into `∈` -/
theorem isStrictWellFounded₀_of_mem {R a : M} {F : ClassFunction M} [F.Sigma 1 Set.univ]
    (hRa : IsRelationOn R a) (hF : ∀ x ∈ a, ∀ y ∈ a, y [R] x → F y ∈ F x) :
    IsStrictWellFounded₀ R a := by
  refine Multiclass.IsStrictWellFounded₀.isStrictWellFounded₀ ?_ hRa
  intro A _ ⟨x, hx⟩
  by_cases hxa : x ∈ a
  swap
  · exact ⟨x, hx, fun y hy ↦ absurd (hRa.mem_right hy) hxa⟩
  -- `B w`: `w = F y` for some `y ∈ a` with `A y`
  let B : Class M := fun w ↦ ∃ y, (y ∈ a ∧ A y) ∧ F y = w
  have hB (w : M) : B w ↔ ∃ y, (y ∈ a ∧ A y) ∧ F y = w := .rfl
  have hBx : B (F x) := by
    rw [hB]
    exact ⟨x, ⟨hxa, hx⟩, rfl⟩
  obtain ⟨w, hw, hmin⟩ := isStrictWellFounded₀_memRel B ⟨F x, hBx⟩
  rw [hB w] at hw
  obtain ⟨y, ⟨hya, hAy⟩, rfl⟩ := hw
  refine ⟨y, hAy, fun z hzy hAz ↦ ?_⟩
  have hza : ![z, y] 0 ∈ a := hRa.mem_left hzy
  apply hmin (F z)
  · simp only [memRel_iff]
    exact hF y hya z hza hzy
  · rw [hB]
    exact ⟨z, ⟨hza, hAz⟩, rfl⟩

section

variable (hS : ∀ x ∈ S, Ordinal x)
include hS

/-- `∈` is a strict well-order on a set of ordinals -/
theorem isStrictWellOrder_memRelOn : IsStrictWellOrder (memRelOn S) S := by
  have hR : IsRelationOn (memRelOn S) S := isRelationOn_memRelOn S
  refine ⟨⟨hR, fun x _ hx ↦ ?_, fun x hx y hy z hz hxy hyz ↦ ?_, fun x hx y hy ↦ ?_⟩,
    (isStrictWellFounded₀_memRelOn S).isStrictWellFounded⟩
  · simp only [rel_memRelOn_iff] at hx
    grind
  · simp only [rel_memRelOn_iff] at hxy hyz ⊢
    grind
  · rcases ordinal_compatible (hS x hx) (hS y hy) with h | h | h <;> simp [hx, hy, h]

end

theorem predSet_memRelOn (hx : x ∈ S) : predSet (memRelOn S) x = S ∩ x := by
  ext y
  simp [hx]

/-- The order isomorphism from a set `S` of ordinals onto its order type -/
noncomputable def otMap : ClassFunction M := fun S ↦ collapseOn (memRelOn S) S

/-- The order type of a set `S` of ordinals -/
noncomputable def ot : ClassFunction M := fun S ↦ ran (otMap S)

theorem isFunction_otMap (S : M) : IsFunction (otMap S) :=
  (isStrictWellFounded₀_memRelOn S).isFunction_collapseOn

@[simp]
theorem dom_otMap (S : M) : dom (otMap S) = S :=
  (isStrictWellFounded₀_memRelOn S).dom_collapseOn

theorem mem_ot_iff : z ∈ ot S ↔ ∃ x ∈ S, otMap S ﹫ x = z := by
  simp only [ot, (isFunction_otMap S).mem_ran_iff, dom_otMap]

/-- The recursive description of `otMap S`: `otMap S ﹫ x = {otMap S ﹫ y | y ∈ S ∩ x}` -/
theorem otMap_val_eq (hx : x ∈ S) : otMap S ﹫ x = ran (otMap S ↾ (S ∩ x)) := by
  rw [otMap, (isStrictWellFounded₀_memRelOn S).collapseOn_val_eq hx, predSet_memRelOn hx]

theorem mem_otMap_val_iff (hx : x ∈ S) :
    z ∈ otMap S ﹫ x ↔ ∃ y ∈ S, y ∈ x ∧ otMap S ﹫ y = z := by
  have hf : IsFunction (otMap S) := isFunction_otMap S
  rw [otMap_val_eq hx, (hf.restrict _).mem_ran_iff, dom_restrict hf, dom_otMap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_inter_iff] at hy
    obtain ⟨hyS, hySx⟩ := hy
    refine ⟨y, hyS, by grind, ?_⟩
    exact (val_restrict _ hf hySx (by simpa using hyS)).symm
  · rintro ⟨y, hyS, hyx, rfl⟩
    have hy : y ∈ S ∩ x := by
      simp only [mem_inter_iff]
      exact ⟨hyS, hyx⟩
    refine ⟨y, ?_, val_restrict _ hf hy (by simpa using hyS)⟩
    rw [mem_inter_iff]
    exact ⟨hyS, hy⟩

section

variable (hS : ∀ x ∈ S, Ordinal x)
include hS

/-- `∈` on a set of ordinals is a strict well-order, also well-founded for definable classes -/
theorem isStrictWellOrder₀_memRelOn : IsStrictWellOrder₀ (memRelOn S) S :=
  ⟨isStrictWellOrder_memRelOn hS, (isStrictWellFounded₀_memRelOn S).isStrictWellFounded₀_ofRel⟩

/-- The order type of a set of ordinals is an ordinal -/
@[simp, grind .]
theorem ordinal_ot : Ordinal (ot S) :=
  (isStrictWellOrder₀_memRelOn hS).ordinal_ran_collapseOn

theorem ordinal_otMap_val (hx : x ∈ S) : Ordinal (otMap S ﹫ x) :=
  (isStrictWellOrder₀_memRelOn hS).ordinal_collapseOn_val hx

/-- `otMap S` is an isomorphism from `S` onto `ot S` -/
theorem otMap_mem_otMap_iff (hx : x ∈ S) (hy : y ∈ S) :
    otMap S ﹫ y ∈ otMap S ﹫ x ↔ y ∈ x := by
  unfold otMap
  rw [← (isStrictWellOrder₀_memRelOn hS).rel_iff_collapseOn_mem_collapseOn hx hy]
  simp [hx, hy]

@[simp]
theorem otMap_injOn (hx : x ∈ S) (hy : y ∈ S) :
    otMap S ﹫ x = otMap S ﹫ y ↔ x = y :=
  (isStrictWellFounded₀_memRelOn S).collapseOn_injOn
    (isStrictWellOrder_memRelOn hS).isExtensionalOn hx hy

/-- `otMap S` is a bijection from `S` onto `ot S` -/
theorem isBijectionFromTo_otMap : otMap S !: S ↔ ot S := by
  simp only [isBijectionFromTo_iff]
  exact ⟨⟨isFunction_otMap S, dom_otMap S, subset_refl _⟩, fun x hx x' hx' h ↦ by simp_all, rfl⟩

end

/-- If `f` is an order homomorphism from the ordinal `a` to the ordinal `b`, then `otMap` of
its range is the inverse of `f` -/
theorem IsOrderHomOn.otMap_ran {f : M} (hf : IsOrderHomOn f a b) : otMap (ran f) = f⁻¹ := by
  have hbij : f !: a ↔ ran f := isBijectionFromTo_ran_of_isInjectionFromTo hf.isInjectionFromTo
  set S := ran f
  -- `x ∈ a → otMap S ﹫ (f ﹫ x) = x` as a definable class
  let Fs : Fin 2 → MulticlassFunction M 1 :=
    ![ClassFunction.toMulticlassFunction _root_.id, ClassFunction.toMulticlassFunction
      (ClassFunction.comp (fun y ↦ otMap S ﹫ y) fun y ↦ f ﹫ y)]
  have hA (x : M) : (Class.Mem a ⟹ ((Multiclass.Eq (0 : Fin 2) 1).subst Fs : Class M)) x ↔
      (x ∈ a → otMap S ﹫ (f ﹫ x) = x) := by
    simp [Fs, Multiclass.subst, ClassFunction.comp, ← ClassFunction.eq_toMulticlassFunction,
      eq_comm]
  -- `otMap S ﹫ (f ﹫ x) = x` for `x ∈ a`
  have hval (x : M) (hx : Ordinal x) :
      (Class.Mem a ⟹ ((Multiclass.Eq (0 : Fin 2) 1).subst Fs : Class M)) x := by
    refine ordinal_induction (fun x hxo ih ↦ ?_) hx
    simp only [hA] at ih ⊢
    intro hxa
    ext z
    simp only [mem_otMap_val_iff, hbij.isFunctionFromTo.val_mem, hxa]
    constructor
    · rintro ⟨w, hwS, hwx, rfl⟩
      rw [hf.isFunctionFromTo.isFunction.mem_ran_iff, hf.isFunctionFromTo.dom_eq] at hwS
      obtain ⟨y, hya, rfl⟩ := hwS
      grind [hf.olt_iff (olt_of_mem hf.ordinal_left hxa) (olt_of_mem hf.ordinal_left hya)]
    · intro hz
      have hza : z ∈ a := hf.ordinal_left.transitive _ hxa hz
      exact ⟨f ﹫ z, hbij.isFunctionFromTo.val_mem hza,
        (hf.olt (olt_of_mem hf.ordinal_left hxa) (olt_of_mem hxo hz)).mem,
        ih z (olt_of_mem hxo hz) hza⟩
  refine (isFunction_otMap S).ext hbij.inv.isFunction (by rw [dom_otMap, dom_inv]) fun w hw ↦ ?_
  rw [dom_otMap, hf.isFunctionFromTo.isFunction.mem_ran_iff, hf.isFunctionFromTo.dom_eq] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  have h := hval x (ordinal_of_mem (by grind) hx)
  rw [hA] at h
  rw [h hx, hbij.inv_val_val hx]

/-- If `f` is an order homomorphism from the ordinal `a` to the ordinal `b`, then `a` is the order
type of the range of `f` -/
theorem IsOrderHomOn.ot_ran {f : M} (hf : IsOrderHomOn f a b) : ot (ran f) = a := by
  simp [ot, hf.otMap_ran, ran_inv, hf.isFunctionFromTo.dom_eq]

/-- The order type of the image of an ordinal `a` under a `Σ₁` order homomorphism of the
ordinals is `a` -/
theorem IsOrderHom.ot_ran {F : ClassFunction M} [F.Sigma 1 Set.univ] (hF : IsOrderHom F)
    (ha : Ordinal a) : ot (ran (F ↾₀ a)) = a :=
  -- `F` maps `a` into `F a`
  (hF.isOrderHomOn ha (hF.ordinal ha) fun _ hx ↦ hF.olt hx).ot_ran

/-- The collapse of `∈` on an ordinal `α` is the identity on `α` -/
theorem collapseOn_memRelOn_eq_id {α : M} (hα : Ordinal α) :
    collapseOn (memRelOn α) α = id α := by
  simpa [otMap] using (isOrderHomOn_id hα).otMap_ran

/-- The image of the collapse of `∈` on an ordinal `α` is `α` -/
theorem ran_collapseOn_memRelOn {α : M} (hα : Ordinal α) : ran (collapseOn (memRelOn α) α) = α := by
  rw [collapseOn_memRelOn_eq_id hα, ran_id]

/-- The order type of an ordinal is itself -/
@[simp]
theorem ot_eq_self {α : M} (hα : Ordinal α) : ot α = α :=
  ran_collapseOn_memRelOn hα

/-- Order isomorphic ordinals are equal -/
theorem eq_of_isBijectionFromTo_of_olt {α α' g : M} (hα : Ordinal α) (hα' : Ordinal α')
    (hg : g !: α ↔ α') (hmono : ∀ x <ₒ α, ∀ y <ₒ x, g ﹫ y <ₒ g ﹫ x) : α = α' := by
  rw [← IsOrderHomOn.ot_ran ⟨hα, hα', hg.isFunctionFromTo, hmono⟩, hg.ran_eq, ot_eq_self hα']

/-- `otMap S ﹫ x` is the order type of the image of the predecessors of `x` under
`otMap S` -/
theorem otMap_val_eq_ot (hS : ∀ x ∈ S, Ordinal x) (hx : x ∈ S) :
    otMap S ﹫ x = ot (ran (otMap S ↾ (S ∩ x))) := by
  rw [← otMap_val_eq hx, ot_eq_self (ordinal_otMap_val hS hx)]

/-- The order type of a subset of an ordinal `α` is at most `α` -/
theorem ot_ole {α : M} (hα : Ordinal α) (hSα : S ⊆ α) : ot S ≤ₒ α := by
  have hS (x : M) (hx : x ∈ S) : Ordinal x := ordinal_of_mem hα (hSα hx)
  -- `x ∈ S → otMap S ﹫ x ⊆ x` as a definable class
  let Fs : Fin 2 → MulticlassFunction M 1 :=
    ![ClassFunction.toMulticlassFunction (fun y ↦ otMap S ﹫ y),
      ClassFunction.toMulticlassFunction _root_.id]
  have hA (x : M) : (Class.Mem S ⟹ ((Multiclass.Subset (0 : Fin 2) 1).subst Fs : Class M)) x ↔
      (x ∈ S → otMap S ﹫ x ⊆ x) := by
    tauto
  -- `otMap S ﹫ x ⊆ x` for `x ∈ S`
  have hle (x : M) (hx : Ordinal x) :
      (Class.Mem S ⟹ ((Multiclass.Subset (0 : Fin 2) 1).subst Fs : Class M)) x := by
    refine ordinal_induction (fun x hxo ih ↦ ?_) hx
    simp only [hA] at ih ⊢
    intro hxS z hz
    simp only [mem_otMap_val_iff, hxS] at hz
    obtain ⟨y, hyS, hyx, rfl⟩ := hz
    have hy : otMap S ﹫ y ⊆ y := (ih y (olt_of_mem hxo hyx) hyS)
    rw [← ole_iff_subset (ordinal_otMap_val hS hyS) (hS y hyS)] at hy
    grind
  rw [ole_iff_subset (ordinal_ot hS) hα]
  intro z hz
  simp only [mem_ot_iff] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have h := hle x (hS x hx)
  rw [hA] at h
  grind [ole_iff_subset (ordinal_otMap_val hS hx) (hS x hx)]

end MemStructure

end FirstOrder.Language
