/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Order.Basic
import Astlib.Basic.SetOperation.Function.Update
/-!
# Strict linear orders

`IsStrictLinearOrder R a` says that `R` is a relation on `a` that is irreflexive, transitive and
trichotomous on `a`.

Strictly linearly ordered sets are pairs `B = !(A, R)` with `IsStrictLinearOrder R A`
(`IsStrictLinearOrderedSet B`, a `Δ₀` class), with components `losSet B = A` and `losOdr B = R`.
`losIrm B b` adds `b` to `B` as a maximum (`IsStrictLinearOrderedSet.losIrm`), and
`losIlf B d e` inserts `e` immediately before `d` (`IsStrictLinearOrderedSet.losIlf`, via
`insertBefore` on orders). For a function `f`, `mvalIrm`, `mvalMvalIrm`, `mvalIlf` and `mvalMvalIlf`
apply these operations to the (nested) value of `f` at `a`. All are `Δ₀`.
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

/-- `R` on `a` with `e` inserted immediately before `d`: below `e` are the `R`-predecessors of
`d`, and above `e` are `d` and its `R`-successors -/
noncomputable def insertBefore (R a d e : M) : M :=
  R ∪ dom (R ∩ a ×ˢ ({d} : M)) ×ˢ ({e} : M) ∪ ({e} : M) ×ˢ insert d (ran (R ∩ ({d} : M) ×ˢ a))

@[simp, grind =]
theorem rel_insertBefore_iff {d e : M} : x [insertBefore R a d e] y ↔
    x [R] y ∨ ((x ∈ a ∧ x [R] d) ∧ y = e) ∨ (x = e ∧ (y = d ∨ (y ∈ a ∧ d [R] y))) := by
  simp only [MemStructure.insertBefore, mem_union_iff, mem_sprod_iff, mem_singleton_iff,
    orderedPair_eq_orderedPair_iff, exists_eq_left, ↓existsAndEq, true_and, mem_insert_iff,
    exists_eq_or_imp, and_true, mem_dom_iff, mem_ran_iff, mem_inter_iff]
  grind

/-- Inserting `e ∉ a` immediately before `d ∈ a` into a strict linear order on `a` yields a
strict linear order -/
theorem IsStrictLinearOrder.insertBefore {d e : M} (hR : IsStrictLinearOrder R a) (hd : d ∈ a)
    (he : e ∉ a) : IsStrictLinearOrder (insertBefore R a d e) (insert e a) := by
  refine ⟨(isRelationOn_sprod _).subset fun z hz ↦ ?_, fun x hx ↦ ?_,
    fun x hx y hy z hz hxy hyz ↦ ?_, fun x hx y hy ↦ ?_⟩
  · simp only [MemStructure.insertBefore, mem_union_iff] at hz
    rcases hz with (hz | hz) | hz
    · obtain ⟨x, hx, y, hy, rfl⟩ := hR.isRelationOn.exists_exists hz
      grind
    · rw [mem_sprod_iff] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      rw [mem_dom_iff] at hx
      obtain ⟨w, hw⟩ := hx
      rw [mem_inter_iff, pair_mem_sprod_iff] at hw
      rw [mem_singleton_iff] at hy
      rw [pair_mem_sprod_iff, mem_insert_iff, mem_insert_iff]
      exact ⟨Or.inr hw.right.left, Or.inl hy⟩
    · rw [mem_sprod_iff] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      rw [mem_singleton_iff] at hx
      rw [mem_insert_iff, mem_ran_iff] at hy
      rw [pair_mem_sprod_iff, mem_insert_iff, mem_insert_iff]
      refine ⟨Or.inl hx, Or.inr ?_⟩
      rcases hy with rfl | ⟨w, hw⟩
      · exact hd
      rw [mem_inter_iff, pair_mem_sprod_iff] at hw
      exact hw.right.right
  · grind [hR.irrefl x]
  · rw [rel_insertBefore_iff] at hxy hyz ⊢
    grind [hR.trans, hR.mem_left, hR.mem_right, hR.irrefl]
  · rw [rel_insertBefore_iff, rel_insertBefore_iff]
    grind [hR.trichotomous]

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

namespace FirstOrder.Language

open FirstOrder Language DeltaZeroBoundedFormula

namespace RudimentaryTerm

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] {n : ℕ}

/-- `r` is a strictly linearly ordered set `!(A, R)`: `R` is a strict linear order on `A` -/
noncomputable def isStrictLinearOrderedSet (r : L.RudimentaryTerm n) :
    L.DeltaZeroBoundedFormula n :=
  r.isOrderedPair ⊓ r.right.isStrictLinearOrder r.left

instance (r : L.RudimentaryTerm n) [r.CharFree] : r.isStrictLinearOrderedSet.RelFree := by
  unfold isStrictLinearOrderedSet; infer_instance

/-- `losIrm₀〘B, b〙₂` is `!(insert b (left B), right B ∪ ∅ ∪ left B ×ˢ {b})` -/
noncomputable def losIrm₀ : L.RudimentaryTerm 2 :=
  let B : L.RudimentaryTerm 2 := ᵣ0
  let b : L.RudimentaryTerm 2 := ᵣ1
  ᵣ(insert b B.left, B.right ∪ ∅ ∪ B.left ×ˢ ({b} : L.RudimentaryTerm 2))

instance : (losIrm₀ : L.RudimentaryTerm 2).CharFree := by
  unfold losIrm₀; infer_instance

/-- The rudimentary term for `losIrm r s` -/
noncomputable def losIrm (r s : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  losIrm₀.substBoundRud ![r, s]

instance (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] : (losIrm r s).CharFree := by
  unfold losIrm; infer_instance

/-- `losIlf₀〘B, d, e〙₃` is `!(insert e A, R ∪ dom (R ∩ A ×ˢ {d}) ×ˢ {e} ∪
{e} ×ˢ insert d (ran (R ∩ {d} ×ˢ A)))` for `A = left B` and `R = right B` -/
noncomputable def losIlf₀ : L.RudimentaryTerm 3 :=
  let B : L.RudimentaryTerm 3 := ᵣ0
  let d : L.RudimentaryTerm 3 := ᵣ1
  let e : L.RudimentaryTerm 3 := ᵣ2
  let A := B.left
  let R := B.right
  ᵣ(insert e A, R ∪ (R ∩ A ×ˢ ({d} : L.RudimentaryTerm 3)).dom ×ˢ ({e} : L.RudimentaryTerm 3) ∪
    ({e} : L.RudimentaryTerm 3) ×ˢ insert d (R ∩ ({d} : L.RudimentaryTerm 3) ×ˢ A).ran)

instance : (losIlf₀ : L.RudimentaryTerm 3).CharFree := by
  unfold losIlf₀; infer_instance

/-- The rudimentary term for `losIlf r s t` -/
noncomputable def losIlf (r s t : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  losIlf₀.substBoundRud ![r, s, t]

instance (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] :
    (losIlf r s t).CharFree := by
  unfold losIlf; infer_instance

/-- `mvalIrm₀〘f, a, e〙₃` is `update f a (losIrm (f ﹫ a) e)` -/
noncomputable def mvalIrm₀ : L.RudimentaryTerm 3 :=
  (ᵣ0).update (ᵣ1) (((ᵣ0) ﹫ (ᵣ1)).losIrm (ᵣ2))

instance : (mvalIrm₀ : L.RudimentaryTerm 3).CharFree := by
  unfold mvalIrm₀; infer_instance

/-- The rudimentary term for `mvalIrm r s t` -/
noncomputable def mvalIrm (r s t : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  mvalIrm₀.substBoundRud ![r, s, t]

instance (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] :
    (mvalIrm r s t).CharFree := by
  unfold mvalIrm; infer_instance

/-- `mvalMvalIrm₀〘f, a, c, e〙` is `update f a (mvalIrm (f ﹫ a) c e)` -/
noncomputable def mvalMvalIrm₀ : L.RudimentaryTerm 4 :=
  (ᵣ0).update (ᵣ1) (((ᵣ0) ﹫ (ᵣ1)).mvalIrm (ᵣ2) (ᵣ3))

instance : (mvalMvalIrm₀ : L.RudimentaryTerm 4).CharFree := by
  unfold mvalMvalIrm₀; infer_instance

/-- `mvalIlf₀〘f, a, d, e〙` is `update f a (losIlf (f ﹫ a) d e)` -/
noncomputable def mvalIlf₀ : L.RudimentaryTerm 4 :=
  (ᵣ0).update (ᵣ1) (((ᵣ0) ﹫ (ᵣ1)).losIlf (ᵣ2) (ᵣ3))

instance : (mvalIlf₀ : L.RudimentaryTerm 4).CharFree := by
  unfold mvalIlf₀; infer_instance

/-- The rudimentary term for `mvalIlf r s t u` -/
noncomputable def mvalIlf (r s t u : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  mvalIlf₀.substBoundRud ![r, s, t, u]

instance (r s t u : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] [u.CharFree] :
    (mvalIlf r s t u).CharFree := by
  unfold mvalIlf; infer_instance

/-- `mvalMvalIlf₀〘f, a, c, d, e〙` is `update f a (mvalIlf (f ﹫ a) c d e)` -/
noncomputable def mvalMvalIlf₀ : L.RudimentaryTerm 5 :=
  (ᵣ0).update (ᵣ1) (((ᵣ0) ﹫ (ᵣ1)).mvalIlf (ᵣ2) (ᵣ3) (ᵣ4))

instance : (mvalMvalIlf₀ : L.RudimentaryTerm 5).CharFree := by
  unfold mvalMvalIlf₀; infer_instance

/-- The rudimentary term for `mvalMvalIrm r s t u` -/
noncomputable def mvalMvalIrm (r s t u : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  mvalMvalIrm₀.substBoundRud ![r, s, t, u]

instance (r s t u : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] [u.CharFree] :
    (mvalMvalIrm r s t u).CharFree := by
  unfold mvalMvalIrm; infer_instance

/-- The rudimentary term for `mvalMvalIlf r s t u v` -/
noncomputable def mvalMvalIlf (r s t u v : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  mvalMvalIlf₀.substBoundRud ![r, s, t, u, v]

instance (r s t u v : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] [u.CharFree]
    [v.CharFree] : (mvalMvalIlf r s t u v).CharFree := by
  unfold mvalMvalIlf; infer_instance

end RudimentaryTerm

namespace MemStructure

open RudimentaryTerm

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] {n : ℕ} {A R B b : M}

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isStrictLinearOrderedSet
    (r : L.RudimentaryTerm n) [r.CharFree] (xs : Fin n → M) :
    r.isStrictLinearOrderedSet.toBoundedFormula 〘xs〙 ↔
      IsOrderedPair (r〘xs〙 : M) ∧
        IsStrictLinearOrder (right (r〘xs〙 : M)) (left r〘xs〙) := by
  simp [isStrictLinearOrderedSet]

/-- The underlying set `B_set` of a strictly linearly ordered set `B = !(A, R)` -/
noncomputable def losSet : ClassFunction M := left

/-- The order `B_odr` of a strictly linearly ordered set `B = !(A, R)` -/
noncomputable def losOdr : ClassFunction M := right

omit [L.ExtraConstantsUnaryRelationsOnly] in
@[simp]
theorem losSet_orderedPair : losSet !(A, R) = A := by
  simp [losSet]

omit [L.ExtraConstantsUnaryRelationsOnly] in
@[simp]
theorem losOdr_orderedPair : losOdr !(A, R) = R := by
  simp [losOdr]

instance : (losSet : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq left₀ fun _ ↦ by simp [losSet]

instance : (losOdr : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq right₀ fun _ ↦ by simp [losOdr]

/-- `π[B]`: the image `!(π '' A, π ∘ R ∘ π⁻¹)` of the strictly linearly ordered set `B = !(A, R)`
under `π` -/
noncomputable def losImg (π B : M) : M := !(π '' losSet B, π !∘ losOdr B !∘ π⁻¹)

/-- `B_irm(b)`: `B = !(A, R)` with `b` added as a maximum, `!(A ∪ {b}, R ∪ A ×ˢ {b})` -/
noncomputable def losIrm (B b : M) : M := losIrm₀〘B, b〙₂

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ losIrm (ys 0) (ys 1)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ losIrm₀ fun _ _ ↦ rfl

theorem losIrm_eq (B b : M) :
    losIrm B b = !(insert b (losSet B), insertMax (losOdr B) (losSet B) b) := by
  simp [losIrm, losIrm₀, insertMax, concat, losSet, losOdr]

/-- `B = !(A, R)` is a strictly linearly ordered set: `R` is a strict linear order on `A` -/
def IsStrictLinearOrderedSet : Class M := fun B ↦
  IsOrderedPair B ∧ IsStrictLinearOrder (losOdr B) (losSet B)

omit [RudClosed M] [Extensional M] in
theorem IsStrictLinearOrderedSet.isOrderedPair (hB : IsStrictLinearOrderedSet B) :
    IsOrderedPair B :=
  hB.left

omit [RudClosed M] [Extensional M] in
theorem IsStrictLinearOrderedSet.isStrictLinearOrder (hB : IsStrictLinearOrderedSet B) :
    IsStrictLinearOrder (losOdr B) (losSet B) :=
  hB.right

theorem isStrictLinearOrderedSet_orderedPair_iff :
    IsStrictLinearOrderedSet !(A, R) ↔ IsStrictLinearOrder R A := by
  simp [IsStrictLinearOrderedSet, IsOrderedPair]

instance : (IsStrictLinearOrderedSet : Class M).DeltaZero Set.univ := by
  have h : (IsStrictLinearOrderedSet : Class M) =
      Multiclass.toClass
        (ᵣ0 : L.RudimentaryTerm 1).isStrictLinearOrderedSet.toBoundedFormula.multiclass := by
    funext B
    rw [Multiclass.toClass_iff, BoundedFormula.multiclass, realize_isStrictLinearOrderedSet]
    simp [IsStrictLinearOrderedSet, losSet, losOdr]
  rw [h]
  infer_instance

/-- Adding a maximum `b ∉ B_set` to a strictly linearly ordered set gives a strictly linearly
ordered set -/
theorem IsStrictLinearOrderedSet.losIrm (hB : IsStrictLinearOrderedSet B) (hb : b ∉ losSet B) :
    IsStrictLinearOrderedSet (losIrm B b) := by
  rw [losIrm_eq, isStrictLinearOrderedSet_orderedPair_iff]
  exact hB.isStrictLinearOrder.insertMax hb

omit [RudClosed M] [Extensional M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_losIrm₀ (xs : Fin 2 → M) :
    losIrm₀〘xs〙 = losIrm (xs 0) (xs 1) := by
  rw [losIrm, Matrix.vec_fin_two_eq xs]

/-- `B_ilf(d, e)`: `B = !(A, R)` with `e` inserted immediately before `d` -/
noncomputable def losIlf (B d e : M) : M := losIlf₀〘B, d, e〙₃

instance : MulticlassFunction.DeltaZero (fun ys : Fin 3 → M ↦ losIlf (ys 0) (ys 1) (ys 2))
    Set.univ :=
  MulticlassFunction.deltaZero_of_eq losIlf₀ fun ys ↦ by
    rw [losIlf, show ![ys 0, ys 1, ys 2] = ys by ext i; fin_cases i <;> rfl]

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_losIlf₀ (xs : Fin 3 → M) :
    losIlf₀〘xs〙 = losIlf (xs 0) (xs 1) (xs 2) := by
  rw [losIlf, show ![xs 0, xs 1, xs 2] = xs by ext i; fin_cases i <;> rfl]

theorem losIlf_eq (B d e : M) :
    losIlf B d e = !(insert e (losSet B), insertBefore (losOdr B) (losSet B) d e) := by
  simp [losIlf, losIlf₀, insertBefore, losSet, losOdr]

/-- Inserting `e ∉ B_set` immediately before `d ∈ B_set` into a strictly linearly ordered set
gives a strictly linearly ordered set -/
theorem IsStrictLinearOrderedSet.losIlf {d e : M} (hB : IsStrictLinearOrderedSet B)
    (hd : d ∈ losSet B) (he : e ∉ losSet B) : IsStrictLinearOrderedSet (losIlf B d e) := by
  rw [losIlf_eq, isStrictLinearOrderedSet_orderedPair_iff]
  exact hB.isStrictLinearOrder.insertBefore hd he

/-- `f_{mVal.irm}(a, e)`: `f` with the value at `a` replaced by `(f ﹫ a)_{irm}(e)` -/
noncomputable def mvalIrm (f a e : M) : M := mvalIrm₀〘f, a, e〙₃

instance : MulticlassFunction.DeltaZero (fun ys : Fin 3 → M ↦ mvalIrm (ys 0) (ys 1) (ys 2))
    Set.univ :=
  MulticlassFunction.deltaZero_of_eq mvalIrm₀ fun ys ↦ by
    rw [mvalIrm, show ![ys 0, ys 1, ys 2] = ys by ext i; fin_cases i <;> rfl]

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_mvalIrm₀ (xs : Fin 3 → M) :
    mvalIrm₀〘xs〙 = mvalIrm (xs 0) (xs 1) (xs 2) := by
  rw [mvalIrm, show ![xs 0, xs 1, xs 2] = xs by ext i; fin_cases i <;> rfl]

omit [RudClosed M] in
theorem mvalIrm_eq (f a e : M) : mvalIrm f a e = update f a (losIrm (f ﹫ a) e) := by
  simp [mvalIrm, mvalIrm₀, RudimentaryTerm.losIrm]

/-- `f_{mVal.mVal.irm}(a, c, e)`: `f` with the value at `a` replaced by
`(f ﹫ a)_{mVal.irm}(c, e)` -/
noncomputable def mvalMvalIrm (f a c e : M) : M := mvalMvalIrm₀〘![f, a, c, e]〙

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 4 → M ↦ mvalMvalIrm (ys 0) (ys 1) (ys 2) (ys 3)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq mvalMvalIrm₀ fun ys ↦ by
    rw [mvalMvalIrm, show ![ys 0, ys 1, ys 2, ys 3] = ys by ext i; fin_cases i <;> rfl]

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_mvalMvalIrm₀ (xs : Fin 4 → M) :
    mvalMvalIrm₀〘xs〙 = mvalMvalIrm (xs 0) (xs 1) (xs 2) (xs 3) := by
  rw [mvalMvalIrm, show ![xs 0, xs 1, xs 2, xs 3] = xs by ext i; fin_cases i <;> rfl]

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_mvalMvalIrm
    (r s t u : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] [u.CharFree]
    (xs : Fin n → M) :
    (RudimentaryTerm.mvalMvalIrm r s t u)〘xs〙 =
      MemStructure.mvalMvalIrm r〘xs〙 s〘xs〙 t〘xs〙 u〘xs〙 := by
  simp [RudimentaryTerm.mvalMvalIrm]

omit [RudClosed M] in
theorem mvalMvalIrm_eq (f a c e : M) :
    mvalMvalIrm f a c e = update f a (mvalIrm (f ﹫ a) c e) := by
  simp [mvalMvalIrm, mvalMvalIrm₀, RudimentaryTerm.mvalIrm]

/-- `f_{mVal.ilf}(a, d, e)`: `f` with the value at `a` replaced by `(f ﹫ a)_{ilf}(d, e)` -/
noncomputable def mvalIlf (f a d e : M) : M := mvalIlf₀〘![f, a, d, e]〙

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 4 → M ↦ mvalIlf (ys 0) (ys 1) (ys 2) (ys 3)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq mvalIlf₀ fun ys ↦ by
    rw [mvalIlf, show ![ys 0, ys 1, ys 2, ys 3] = ys by ext i; fin_cases i <;> rfl]

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_mvalIlf₀ (xs : Fin 4 → M) :
    mvalIlf₀〘xs〙 = mvalIlf (xs 0) (xs 1) (xs 2) (xs 3) := by
  rw [mvalIlf, show ![xs 0, xs 1, xs 2, xs 3] = xs by ext i; fin_cases i <;> rfl]

omit [RudClosed M] in
theorem mvalIlf_eq (f a d e : M) : mvalIlf f a d e = update f a (losIlf (f ﹫ a) d e) := by
  simp [mvalIlf, mvalIlf₀, RudimentaryTerm.losIlf]

/-- `f_{mVal.mVal.ilf}(a, c, d, e)`: `f` with the value at `a` replaced by
`(f ﹫ a)_{mVal.ilf}(c, d, e)` -/
noncomputable def mvalMvalIlf (f a c d e : M) : M := mvalMvalIlf₀〘![f, a, c, d, e]〙

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 5 → M ↦ mvalMvalIlf (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq mvalMvalIlf₀ fun ys ↦ by
    rw [mvalMvalIlf, show ![ys 0, ys 1, ys 2, ys 3, ys 4] = ys by ext i; fin_cases i <;> rfl]

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_mvalMvalIlf₀ (xs : Fin 5 → M) :
    mvalMvalIlf₀〘xs〙 = mvalMvalIlf (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) := by
  rw [mvalMvalIlf, show ![xs 0, xs 1, xs 2, xs 3, xs 4] = xs by ext i; fin_cases i <;> rfl]

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_mvalMvalIlf
    (r s t u v : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] [u.CharFree]
    [v.CharFree] (xs : Fin n → M) :
    (RudimentaryTerm.mvalMvalIlf r s t u v)〘xs〙 =
      MemStructure.mvalMvalIlf r〘xs〙 s〘xs〙 t〘xs〙 u〘xs〙 v〘xs〙 := by
  simp [RudimentaryTerm.mvalMvalIlf]

omit [RudClosed M] in
theorem mvalMvalIlf_eq (f a c d e : M) :
    mvalMvalIlf f a c d e = update f a (mvalIlf (f ﹫ a) c d e) := by
  simp [mvalMvalIlf, mvalMvalIlf₀, RudimentaryTerm.mvalIlf]

/-- `r` is the smallest element of the strictly linearly ordered set `B` -/
def IsLeastLos (B r : M) : Prop := r ∈ losSet B ∧ ∀ y ∈ losSet B, ¬y [losOdr B] r

instance : Multiclass.DeltaZero (fun ys : Fin 2 → M ↦ IsLeastLos (ys 0) (ys 1)) Set.univ := by
  let φ : L.DeltaZeroBoundedFormula 2 := (ᵣ1 : L.RudimentaryTerm 2).isMem (ᵣ0).left ⊓
    (ᵣ0 : L.RudimentaryTerm 2).left.allMem
      ∼((ᵣ0 : L.RudimentaryTerm 3).right.hasMemOrderedPair (ᵣ2) (ᵣ1))
  have h : (fun ys : Fin 2 → M ↦ IsLeastLos (ys 0) (ys 1)) = φ.toBoundedFormula.multiclass := by
    funext ys
    simp [φ, IsLeastLos, losSet, losOdr, BoundedFormula.multiclass, Fin.snoc_nat]
  rw [h]
  infer_instance

omit [L.ExtraConstantsUnaryRelationsOnly] in
/-- The only element of `({b}, ∅)` is its least element -/
theorem isLeastLos_singleton (b : M) : IsLeastLos !(({b} : M), ∅) b := by
  simp [IsLeastLos, losSet_orderedPair, losOdr_orderedPair]

end MemStructure

end FirstOrder.Language
