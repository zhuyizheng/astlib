/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Order.StrictLinearOrder
import Astlib.Basic.Order.StrictWellFounded
import Astlib.Basic.Ordinal.Basic
/-!
# Strict well-orders

`IsStrictWellOrder R a` says that `R` is a strict linear order on `a` that is strict well-founded,
i.e. every nonempty subset of `a` has an `R`-least element (`IsStrictWellOrder.exists_least`).
-/

namespace FirstOrder.Language.MemStructure

open FirstOrder Language

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] {R a b c x y : M}

/-- `R` is a strict well-order on `a` -/
def IsStrictWellOrder (R a : M) : Prop := IsStrictLinearOrder R a ∧ IsStrictWellFounded R a

theorem isStrictWellOrder_iff :
    IsStrictWellOrder R a ↔ IsStrictLinearOrder R a ∧ IsStrictWellFounded R a :=
  .rfl

/-- A transitive and trichotomous strict well-founded relation is a strict well-order -/
theorem IsStrictWellFounded.isStrictWellOrder [RudClosed M] [Extensional M]
    (h : IsStrictWellFounded R a) (htr : IsTransOn R a) (htri : IsTrichotomousOn R a) :
    IsStrictWellOrder R a :=
  ⟨⟨h.isRelationOn, h.isIrreflOn, htr, htri⟩, h⟩

namespace IsStrictWellOrder

@[grind .]
theorem isStrictLinearOrder (h : IsStrictWellOrder R a) : IsStrictLinearOrder R a := h.left

@[grind .]
theorem isStrictWellFounded (h : IsStrictWellOrder R a) : IsStrictWellFounded R a := h.right

theorem isRelationOn (h : IsStrictWellOrder R a) : IsRelationOn R a :=
  h.isStrictLinearOrder.isRelationOn

/-- Every nonempty subset has a least element -/
theorem exists_least [RudClosed M] (h : IsStrictWellOrder R a) (hba : b ⊆ a) (hx : x ∈ b) :
    ∃ x ∈ b, ∀ y ∈ b, y ≠ x → x [R] y := by
  obtain ⟨z, hz, hmin⟩ := h.isStrictWellFounded.exists_minimal hba hx
  exact ⟨z, hz, fun y hy hyz ↦ by grind [h.isStrictLinearOrder.trichotomous (hba hz) (hba hy)]⟩

variable [RudClosed M] [Extensional M]

/-- The least element is unique -/
theorem eq_of_least (h : IsStrictWellOrder R a) (hx : ∀ z ∈ b, z ≠ x → x [R] z)
    (hy : ∀ z ∈ b, z ≠ y → y [R] z) (hxb : x ∈ b) (hyb : y ∈ b) : x = y := by
  grind [h.isStrictLinearOrder.asymm]

/-- Well-founded induction -/
theorem induction_subset (h : IsStrictWellOrder R a)
    (hc : ∀ x ∈ a, (∀ y, y [R] x → y ∈ c) → x ∈ c) : a ⊆ c :=
  h.isStrictWellFounded.induction_subset hc

/-- The restriction of a strict well-order to a subset is a strict well-order -/
theorem restrict₂ (h : IsStrictWellOrder R a) (hba : b ⊆ a) : IsStrictWellOrder (R ↾↾ b) b :=
  ⟨h.isStrictLinearOrder.restrict₂ hba, h.isStrictWellFounded.restrict₂ hba⟩

end IsStrictWellOrder

variable [RudClosed M] [Extensional M]

@[simp, grind .]
theorem isStrictWellOrder_empty : IsStrictWellOrder (∅ : M) ∅ :=
  ⟨isStrictLinearOrder_empty, isStrictWellFounded_empty _⟩

@[simp, grind .]
theorem isStrictWellOrder_empty_singleton (x : M) : IsStrictWellOrder (∅ : M) {x} :=
  ⟨isStrictLinearOrder_empty_singleton x, isStrictWellFounded_empty _⟩

section Constructions

/-- The concatenation of strict well-orders on disjoint sets is a strict well-order -/
theorem IsStrictWellOrder.concat (hR : IsStrictWellOrder R a) (hS : IsStrictWellOrder S b)
    (hab : a ∩ b = ∅) : IsStrictWellOrder (concat R a S b) (a ∪ b) :=
  ⟨hR.isStrictLinearOrder.concat hS.isStrictLinearOrder hab,
    hR.isStrictWellFounded.concat hS.isStrictWellFounded hab⟩

/-- Adding a maximum `x ∉ a` to a strict well-order on `a` yields a strict well-order -/
theorem IsStrictWellOrder.insertMax (hR : IsStrictWellOrder R a) (hx : x ∉ a) :
    IsStrictWellOrder (insertMax R a x) (insert x a) :=
  ⟨hR.isStrictLinearOrder.insertMax hx, hR.isStrictWellFounded.insertMax hx⟩

/-- Adding a minimum `x ∉ a` to a strict well-order on `a` yields a strict well-order -/
theorem IsStrictWellOrder.insertMin (hR : IsStrictWellOrder R a) (hx : x ∉ a) :
    IsStrictWellOrder (insertMin R a x) (insert x a) :=
  ⟨hR.isStrictLinearOrder.insertMin hx, hR.isStrictWellFounded.insertMin hx⟩

/-- The lexicographic product of strict well-orders is a strict well-order -/
theorem IsStrictWellOrder.lexProd (hR : IsStrictWellOrder R a) (hS : IsStrictWellOrder S b) :
    IsStrictWellOrder (lexProd R a S b) (a ×ˢ b) :=
  ⟨hR.isStrictLinearOrder.lexProd hS.isStrictLinearOrder,
    hR.isStrictWellFounded.lexProd hS.isStrictWellFounded⟩

end Constructions

end FirstOrder.Language.MemStructure

namespace FirstOrder.Language

open FirstOrder Language

namespace RudimentaryTerm

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] {n : ℕ}

/-- The `Π₁` formula saying that `r` is a strict well-order on `s` -/
noncomputable def isStrictWellOrder (r s : L.RudimentaryTerm n) : L.BoundedFormula' n :=
  ∀' (r.castSucc.isStrictLinearOrder s.castSucc ⊓ r.hasMinimal s).toBoundedFormula

instance (r s : L.RudimentaryTerm n) : (r.isStrictWellOrder s).Pi 1 := by
  unfold isStrictWellOrder; infer_instance

end RudimentaryTerm

namespace MemStructure

open RudimentaryTerm

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] {n : ℕ}

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isStrictWellOrder
    (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] (xs : Fin n → M) :
    (r.isStrictWellOrder s)〘xs〙 ↔ IsStrictWellOrder (r〘xs〙 : M) s〘xs〙 := by
  simp [isStrictWellOrder, isStrictWellOrder_iff, isStrictWellFounded_iff, forall_and]
  grind

end MemStructure

end FirstOrder.Language

namespace FirstOrder.Language.MemStructure

open FirstOrder Language

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] {R : Multiclass M 2} {x y : M}

section ClassWellOrder

/-- A class relation `R` is a strict well-order: it is well-founded for definable classes,
transitive and trichotomous -/
def Multiclass.IsStrictWellOrder (R : Multiclass M 2) : Prop :=
  R.IsStrictWellFounded₀ ∧ (∀ x y z, R ![x, y] → R ![y, z] → R ![x, z]) ∧
    ∀ x y, R ![x, y] ∨ x = y ∨ R ![y, x]

omit [Inhabited M] [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
theorem Multiclass.IsStrictWellOrder.isStrictWellFounded₀ (hR : R.IsStrictWellOrder) :
    R.IsStrictWellFounded₀ :=
  hR.left

omit [Inhabited M] [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
theorem Multiclass.IsStrictWellOrder.trans (hR : R.IsStrictWellOrder) {z : M} (hxy : R ![x, y])
    (hyz : R ![y, z]) : R ![x, z] :=
  hR.right.left x y z hxy hyz

omit [Inhabited M] [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
theorem Multiclass.IsStrictWellOrder.trichotomous (hR : R.IsStrictWellOrder) (x y : M) :
    R ![x, y] ∨ x = y ∨ R ![y, x] :=
  hR.right.right x y

omit [Inhabited M] [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
theorem Multiclass.IsStrictWellOrder.rel_or_rel_of_ne (hR : R.IsStrictWellOrder) (hxy : x ≠ y) :
    R ![x, y] ∨ R ![y, x] := by
  grind [hR.trichotomous x y]

omit [Inhabited M] [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
/-- A relation that is well-founded for definable classes is irreflexive -/
theorem Multiclass.IsStrictWellFounded₀.irrefl (hR : R.IsStrictWellFounded₀) (x : M) :
    ¬R ![x, x] := by
  intro hx
  obtain ⟨z, hz, hmin⟩ := hR (Class.Eq x) ⟨x, by rw [Class.eq_iff]⟩
  simp only [Class.eq_iff] at hz
  subst hz
  exact hmin z hx (by rw [Class.eq_iff])

omit [Inhabited M] [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
/-- A strict well-order is extensional -/
theorem Multiclass.IsStrictWellOrder.isExtensional (hR : R.IsStrictWellOrder) :
    R.IsExtensional := by
  intro x y _ _ h
  by_contra! hne
  rcases hR.rel_or_rel_of_ne hne with hxy | hxy
  · rw [← h x] at hxy
    exact hR.isStrictWellFounded₀.irrefl x hxy
  · rw [h y] at hxy
    exact hR.isStrictWellFounded₀.irrefl y hxy

variable (hR : R.IsStrictWellOrder) (hS : R.IsSetLike) [R.predSet.Sigma 1 Set.univ]
include hR hS

/-- The collapse of a strict well-order consists of ordinals -/
theorem ordinal_collapse (x : M) : Ordinal (collapse R x) := by
  have hR' : R.IsStrictWellFounded₀ := hR.isStrictWellFounded₀
  refine ⟨fun z hz w hw ↦ ?_, fun z hz w hw ↦ ?_⟩
  · simp only [mem_collapse_iff, hR', hS] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    simp only [mem_collapse_iff, hR', hS] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    exact collapse_mem_collapse hR' hS (hR.trans hu hy)
  · simp only [mem_collapse_iff, hR', hS] at hz
    obtain ⟨y, -, rfl⟩ := hz
    simp only [mem_collapse_iff, hR', hS] at hw
    obtain ⟨u, -, rfl⟩ := hw
    rcases hR.trichotomous y u with h | rfl | h
    · exact .inl (collapse_mem_collapse hR' hS h)
    · tauto
    · exact .inr (.inr (collapse_mem_collapse hR' hS h))

/-- The collapse of a strict well-order is an isomorphism onto its image: it is injective, maps
into the ordinals and turns `R` into `∈` -/
theorem collapse_isIso_ordinals :
    Function.Injective (collapse R) ∧ (∀ x, Ordinal (collapse R x)) ∧
      ∀ x y, (R ![y, x] ↔ collapse R y ∈ collapse R x) :=
  ⟨collapse_injective hR.isStrictWellFounded₀ hS hR.isExtensional, ordinal_collapse hR hS,
    fun _ _ ↦ rel_iff_collapse_mem_collapse hR.isStrictWellFounded₀ hS hR.isExtensional⟩

end ClassWellOrder

section SetWellOrder

variable {R a : M}

/-- `R` is a strict well-order on `a` that is moreover well-founded for definable classes -/
def IsStrictWellOrder₀ (R a : M) : Prop :=
  IsStrictWellOrder R a ∧ (Multiclass.ofRel R).IsStrictWellFounded₀

omit [ModelsKP M] in
theorem IsStrictWellOrder.isExtensionalOn (h : IsStrictWellOrder R a) : IsExtensionalOn R a :=
  h.isStrictLinearOrder.isExtensionalOn

namespace IsStrictWellOrder₀

variable (h : IsStrictWellOrder₀ R a)
include h

omit [ModelsKP M] in
theorem isStrictWellOrder : IsStrictWellOrder R a := h.left

omit [ModelsKP M] in
theorem isStrictWellFounded₀ : IsStrictWellFounded₀ R a :=
  ⟨h.isStrictWellOrder.isStrictWellFounded, h.right⟩

omit [ModelsKP M] in
theorem isRelationOn : IsRelationOn R a := h.isStrictWellOrder.isRelationOn

omit [ModelsKP M] in
theorem isExtensionalOn : IsExtensionalOn R a := h.isStrictWellOrder.isExtensionalOn

/-- The range of the collapse of a strict well-order on a set is an ordinal: the order type -/
theorem ordinal_ran_collapseOn : Ordinal (ran (collapseOn R a)) := by
  have hf : IsFunction (collapseOn R a) := h.isStrictWellFounded₀.isFunction_collapseOn
  refine ⟨h.isStrictWellFounded₀.transitive_ran_collapseOn, fun z hz w hw ↦ ?_⟩
  simp only [hf.mem_ran_iff, h.isStrictWellFounded₀.dom_collapseOn] at hz hw
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, rfl⟩ := hw
  have hiso {x y : M} (hx : x ∈ a) (hy : y ∈ a) :=
    h.isStrictWellFounded₀.rel_iff_collapseOn_mem_collapseOn h.isExtensionalOn hx hy
  rcases h.isStrictWellOrder.isStrictLinearOrder.trichotomous hx hy with h' | rfl | h'
  · rw [hiso hy hx] at h'
    tauto
  · tauto
  · rw [hiso hx hy] at h'
    tauto

/-- The collapse of a strict well-order on a set maps it into ordinals -/
theorem ordinal_collapseOn_val {x : M} (hx : x ∈ a) : Ordinal (collapseOn R a ﹫ x) := by
  refine ordinal_of_mem h.ordinal_ran_collapseOn ?_
  simp only [h.isStrictWellFounded₀.isFunction_collapseOn.mem_ran_iff,
    h.isStrictWellFounded₀.dom_collapseOn]
  grind

/-- The collapse of a strict well-order on `a` is an isomorphism from `R` onto `∈` on the ordinal
`ran (collapseOn R a)` -/
theorem rel_iff_collapseOn_mem_collapseOn {x y : M} (hx : x ∈ a) (hy : y ∈ a) :
    y [R] x ↔ collapseOn R a ﹫ y ∈ collapseOn R a ﹫ x :=
  h.isStrictWellFounded₀.rel_iff_collapseOn_mem_collapseOn h.isExtensionalOn hx hy

end IsStrictWellOrder₀

end SetWellOrder

end FirstOrder.Language.MemStructure
