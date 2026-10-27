/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Order.Basic
/-!
# Strict linear orders

`IsStrictLinearOrder R a` says that `R` is a relation on `a` that is irreflexive, transitive and
trichotomous on `a`.
-/

namespace FirstOrder.Language.MemStructure

open FirstOrder Language

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] {R S a b x y z : M}

/-- `R` is a strict linear order on `a` -/
def IsStrictLinearOrder (R a : M) : Prop :=
  IsRelationOn R a ∧ IsIrreflOn R a ∧ IsTransOn R a ∧ IsTrichotomousOn R a

@[grind =]
theorem isStrictLinearOrder_iff :
    IsStrictLinearOrder R a ↔
      IsRelationOn R a ∧ IsIrreflOn R a ∧ IsTransOn R a ∧ IsTrichotomousOn R a :=
  .rfl

namespace IsStrictLinearOrder

@[grind .]
theorem isRelationOn (h : IsStrictLinearOrder R a) : IsRelationOn R a := h.left

@[grind .]
theorem isIrreflOn (h : IsStrictLinearOrder R a) : IsIrreflOn R a := h.right.left

@[grind .]
theorem isTransOn (h : IsStrictLinearOrder R a) : IsTransOn R a := h.right.right.left

@[grind .]
theorem isTrichotomousOn (h : IsStrictLinearOrder R a) : IsTrichotomousOn R a :=
  h.right.right.right

@[grind .]
theorem isAsymmOn (h : IsStrictLinearOrder R a) : IsAsymmOn R a :=
  h.isIrreflOn.isAsymmOn h.isTransOn

theorem isAntisymmOn (h : IsStrictLinearOrder R a) : IsAntisymmOn R a :=
  h.isAsymmOn.isAntisymmOn

theorem trichotomous (h : IsStrictLinearOrder R a) (hx : x ∈ a) (hy : y ∈ a) :
    x [R] y ∨ x = y ∨ y [R] x :=
  h.isTrichotomousOn.trichotomous hx hy

theorem rel_or_rel_of_ne (h : IsStrictLinearOrder R a) (hx : x ∈ a) (hy : y ∈ a)
    (hxy : x ≠ y) : x [R] y ∨ y [R] x := by
  grind [IsTrichotomousOn]

/-- A strict linear order is extensional -/
theorem isExtensionalOn (h : IsStrictLinearOrder R a) : IsExtensionalOn R a := by
  grind [IsExtensionalOn, IsIrreflOn, IsTrichotomousOn]

variable [RudClosed M] [Extensional M]

theorem mem_left (h : IsStrictLinearOrder R a) (hxy : x [R] y) : x ∈ a :=
  h.isRelationOn.mem_left hxy

theorem mem_right (h : IsStrictLinearOrder R a) (hxy : x [R] y) : y ∈ a :=
  h.isRelationOn.mem_right hxy

theorem irrefl (h : IsStrictLinearOrder R a) (x : M) : ¬x [R] x := by
  grind [IsIrreflOn]

theorem asymm (h : IsStrictLinearOrder R a) (hxy : x [R] y) : ¬y [R] x := by
  grind [IsAsymmOn]

theorem trans (h : IsStrictLinearOrder R a) (hxy : x [R] y) (hyz : y [R] z) : x [R] z := by
  grind [IsTransOn]

theorem ne (h : IsStrictLinearOrder R a) (hxy : x [R] y) : x ≠ y :=
  fun e ↦ h.irrefl y (e ▸ hxy)

theorem not_rel_iff (h : IsStrictLinearOrder R a) (hx : x ∈ a) (hy : y ∈ a) :
    ¬x [R] y ↔ y [R] x ∨ x = y := by
  grind [IsAsymmOn, IsTrichotomousOn]

theorem rel_iff_not_rel_and_ne (h : IsStrictLinearOrder R a) (hx : x ∈ a) (hy : y ∈ a) :
    x [R] y ↔ ¬y [R] x ∧ x ≠ y := by
  grind [IsAsymmOn, IsTrichotomousOn]

theorem inv (h : IsStrictLinearOrder R a) : IsStrictLinearOrder R⁻¹ a :=
  ⟨h.isRelationOn.inv, by simpa using h.right⟩

/-- The restriction of a strict linear order to a subset is a strict linear order -/
theorem restrict₂ (h : IsStrictLinearOrder R a) (hba : b ⊆ a) :
    IsStrictLinearOrder (R ↾↾ b) b :=
  ⟨by grind, by simp [hba, h.isIrreflOn.mono, h.isTransOn.mono, h.isTrichotomousOn.mono]⟩

/-- A strict linear order is maximal among asymmetric relations on `a` -/
theorem eq_of_subset (hR : IsStrictLinearOrder R a) (hS : IsRelationOn S a) (hS' : IsAsymmOn S a)
    (hRS : R ⊆ S) : R = S :=
  hR.isRelationOn.ext hS fun x hx y hy ↦ by grind [IsAsymmOn, IsTrichotomousOn]

end IsStrictLinearOrder

variable [RudClosed M] [Extensional M]

@[simp, grind =]
theorem isStrictLinearOrder_inv_iff (hR : IsRelation R) :
    IsStrictLinearOrder R⁻¹ a ↔ IsStrictLinearOrder R a :=
  ⟨fun h ↦ inv_inv hR ▸ h.inv, .inv⟩

@[simp, grind .]
theorem isStrictLinearOrder_empty : IsStrictLinearOrder (∅ : M) ∅ := by
  grind

@[simp, grind .]
theorem isStrictLinearOrder_empty_singleton (x : M) : IsStrictLinearOrder (∅ : M) {x} := by
  grind [IsTrichotomousOn]

@[simp, grind =]
theorem isStrictLinearOrder_inter_sprod_iff :
    IsStrictLinearOrder (R ∩ a ×ˢ a) a ↔
      IsIrreflOn R a ∧ IsTransOn R a ∧ IsTrichotomousOn R a := by
  grind

section Constructions

/-- The concatenation of strict linear orders on disjoint sets is a strict linear order -/
theorem IsStrictLinearOrder.concat (hR : IsStrictLinearOrder R a) (hS : IsStrictLinearOrder S b)
    (hab : a ∩ b = ∅) : IsStrictLinearOrder (concat R a S b) (a ∪ b) := by
  refine ⟨isRelationOn_concat hR.isRelationOn hS.isRelationOn, fun x hx ↦ ?_,
    fun x hx y hy z hz hxy hyz ↦ ?_, fun x hx y hy ↦ ?_⟩
  · grind [hR.irrefl x, hS.irrefl x]
  · simp only [rel_concat_iff] at hxy hyz ⊢
    grind [hR.trans, hS.trans, hR.mem_left, hR.mem_right, hS.mem_left, hS.mem_right]
  · simp only [rel_concat_iff] at hx hy ⊢
    grind [hR.trichotomous, hS.trichotomous]

/-- Adding a maximum `x ∉ a` to a strict linear order on `a` yields a strict linear order -/
theorem IsStrictLinearOrder.insertMax (hR : IsStrictLinearOrder R a) (hx : x ∉ a) :
    IsStrictLinearOrder (insertMax R a x) (insert x a) := by
  have := hR.concat (isStrictLinearOrder_empty_singleton x) (by ext; grind)
  rwa [union_comm, ← insert_eq] at this

/-- Adding a minimum `x ∉ a` to a strict linear order on `a` yields a strict linear order -/
theorem IsStrictLinearOrder.insertMin (hR : IsStrictLinearOrder R a) (hx : x ∉ a) :
    IsStrictLinearOrder (insertMin R a x) (insert x a) := by
  have := (isStrictLinearOrder_empty_singleton x).concat hR (by ext; grind)
  rwa [← insert_eq] at this

/-- The lexicographic product of strict linear orders is a strict linear order -/
theorem IsStrictLinearOrder.lexProd (hR : IsStrictLinearOrder R a)
    (hS : IsStrictLinearOrder S b) : IsStrictLinearOrder (lexProd R a S b) (a ×ˢ b) := by
  refine ⟨isRelationOn_lexProd, fun x hx ↦ ?_,
    fun x hx y hy z hz ↦ ?_, fun x hx y hy ↦ ?_⟩
  · simp only [mem_sprod_iff] at hx
    obtain ⟨u, -, v, -, rfl⟩ := hx
    simp [hR.irrefl u, hS.irrefl v]
  · simp only [mem_sprod_iff] at hx
    obtain ⟨u₁, -, v₁, -, rfl⟩ := hx
    simp only [mem_sprod_iff] at hy hz
    obtain ⟨u₂, -, v₂, -, rfl⟩ := hy
    obtain ⟨u₃, -, v₃, -, rfl⟩ := hz
    simp only [rel_lexProd_iff]
    grind [hR.trans, hS.trans]
  · simp only [mem_sprod_iff] at hx
    obtain ⟨u₁, hu₁, v₁, hv₁, rfl⟩ := hx
    simp only [mem_sprod_iff] at hy
    obtain ⟨u₂, hu₂, v₂, hv₂, rfl⟩ := hy
    simp only [orderedPair_eq_orderedPair_iff]
    grind [hR.trichotomous hu₁ hu₂, hS.trichotomous hv₁ hv₂]

end Constructions

end FirstOrder.Language.MemStructure

namespace FirstOrder.Language

open FirstOrder Language DeltaZeroBoundedFormula

namespace RudimentaryTerm

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] {n : ℕ}

noncomputable def isStrictLinearOrder (r s : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  r.isRelationOn s ⊓ r.isIrreflOn s ⊓ r.isTransOn s ⊓ r.isTrichotomousOn s

instance (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] :
    (r.isStrictLinearOrder s).RelFree := by
  unfold isStrictLinearOrder; infer_instance

end RudimentaryTerm

namespace MemStructure

open RudimentaryTerm

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] {n : ℕ}

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isStrictLinearOrder
    (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] (xs : Fin n → M) :
    (r.isStrictLinearOrder s).toBoundedFormula 〘xs〙 ↔
      IsStrictLinearOrder (r〘xs〙 : M) s〘xs〙 := by
  simp [isStrictLinearOrder, isStrictLinearOrder_iff, and_assoc]

end MemStructure

end FirstOrder.Language
