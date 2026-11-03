/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Order.StrictLinearOrder
import Astlib.Combinatorics.TreeStructure
/-!
# Semi-linearly ordered tree structures

In models of `KP`:

* `SLOTreeStructure M` bundles the data `(T, F)` of a semi-linearly ordered tree structure: a
  tree structure `S.ts` and a function `S.losfn` on its sibling partition;
* `S.IsSLOTreeStructure`: `T` is a tree structure whose nodes `a` are pairs with `left a` a
  function with domain in `ω \ {∅}`, and `F` assigns to each `X` in the sibling partition a
  function `F ﹫ X` sending each `D = left a ﹫ ∅` (`a ∈ X`) to a strictly linearly ordered set
  on `{a ∈ X | left a ﹫ ∅ = D}`;
* the components `S.nd`, `S.dep`, `S.chd`, `S.rt`, `S.prt`, `S.sbl`, `S.sblptn` of `S.ts`, and
  `S.rtlos = F ﹫ S.rt`, `S.chdlos = F !∘ S.chd` (on the nodes with children) and
  `S.sbllos = F !∘ S.sbl` (on `S.nd`);
* the empty semi-linearly ordered tree structure `∅ = (∅, ∅)`.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M]

/-- `G` assigns to each `D = left a ﹫ ∅` with `a ∈ X` a strictly linearly ordered set on
`{a ∈ X | left a ﹫ ∅ = D}` (Clause 4 of a semi-linearly ordered tree structure) -/
structure IsSblLos (X G : M) : Prop where
  isFunction : IsFunction G
  mem_dom_iff (D : M) : D ∈ dom G ↔ ∃ a ∈ X, left a ﹫ ∅ = D
  isStrictLinearOrderedSet {D : M} (hD : D ∈ dom G) : IsStrictLinearOrderedSet (G ﹫ D)
  mem_losSet_iff {D : M} (hD : D ∈ dom G) (a : M) :
    a ∈ losSet (G ﹫ D) ↔ a ∈ X ∧ left a ﹫ ∅ = D

theorem isSblLos_empty : IsSblLos (∅ : M) ∅ where
  isFunction := isFunction_empty
  mem_dom_iff := by simp
  isStrictLinearOrderedSet := by simp
  mem_losSet_iff := by simp

/-- Adding `b` to `X` and replacing the value at `D = left b ﹫ ∅` by a strictly linearly ordered
set on `{a ∈ insert b X | left a ﹫ ∅ = D}` -/
theorem IsSblLos.update {X G b L : M} (hG : IsSblLos X G) (hL : IsStrictLinearOrderedSet L)
    (hLset : ∀ a, a ∈ losSet L ↔ a ∈ insert b X ∧ left a ﹫ ∅ = left b ﹫ ∅) :
    IsSblLos (insert b X) (MemStructure.update G (left b ﹫ ∅) L) := by
  have hmem {D : M} (hD : D ∈ dom (MemStructure.update G (left b ﹫ ∅) L)) (hDb : D ≠ left b ﹫ ∅) :
      D ∈ dom G := by
    rw [dom_update, mem_insert_iff] at hD
    tauto
  refine ⟨hG.isFunction.update _ L, fun D ↦ ?_, fun {D} hD ↦ ?_, fun {D} hD a ↦ ?_⟩
  · rw [dom_update, mem_insert_iff, hG.mem_dom_iff]
    constructor
    · rintro (rfl | ⟨a, ha, rfl⟩)
      · exact ⟨b, mem_insert b X, rfl⟩
      · exact ⟨a, subset_insert b X ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      rw [mem_insert_iff] at ha
      rcases ha with rfl | ha
      · left
        rfl
      · right
        exact ⟨a, ha, rfl⟩
  · by_cases hDb : D = left b ﹫ ∅
    · rwa [hDb, val_update_self hG.isFunction]
    rw [val_update_of_ne hG.isFunction L (hmem hD hDb) hDb]
    exact hG.isStrictLinearOrderedSet (hmem hD hDb)
  · by_cases hDb : D = left b ﹫ ∅
    · rw [hDb, val_update_self hG.isFunction, hLset]
    rw [val_update_of_ne hG.isFunction L (hmem hD hDb) hDb, hG.mem_losSet_iff (hmem hD hDb),
      mem_insert_iff]
    grind

/-- `{b}` with its only linearly ordered set `({b}, ∅)` -/
theorem isSblLos_singleton (b : M) :
    IsSblLos {b} (singletonFun (left b ﹫ ∅) !(({b} : M), ∅)) := by
  have hLb : IsStrictLinearOrderedSet (!(({b} : M), ∅) : M) := by
    rw [isStrictLinearOrderedSet_orderedPair_iff]
    exact isStrictLinearOrder_empty_singleton b
  rw [singletonFun, ← insert_empty_eq_singleton b]
  refine isSblLos_empty.update ?_ fun a ↦ ?_
  · rwa [insert_empty_eq_singleton]
  rw [losSet_orderedPair, insert_empty_eq_singleton, mem_singleton_iff]
  grind

/-- Adding `b` to `X` when no element of `X` has first value `D = left b ﹫ ∅`: the new linearly
ordered set at `D` is `({b}, ∅)` -/
theorem IsSblLos.insert_of_not_mem {X G b : M} (hG : IsSblLos X G) (hD : left b ﹫ ∅ ∉ dom G) :
    IsSblLos (insert b X) (MemStructure.update G (left b ﹫ ∅) !(({b} : M), ∅)) := by
  have hLb : IsStrictLinearOrderedSet (!(({b} : M), ∅) : M) := by
    rw [isStrictLinearOrderedSet_orderedPair_iff]
    exact isStrictLinearOrder_empty_singleton b
  refine hG.update hLb fun a ↦ ?_
  rw [losSet_orderedPair, mem_singleton_iff, mem_insert_iff]
  have hnot : ¬∃ a ∈ X, left a ﹫ ∅ = left b ﹫ ∅ := by
    rwa [← hG.mem_dom_iff]
  grind

/-- Adding `b ∉ X` to `X` when some element of `X` has first value `D = left b ﹫ ∅`: `b` is
added as a maximum to the linearly ordered set at `D` -/
theorem IsSblLos.insert_of_mem {X G b : M} (hG : IsSblLos X G) (hbX : b ∉ X)
    (hD : left b ﹫ ∅ ∈ dom G) : IsSblLos (insert b X) (mvalIrm G (left b ﹫ ∅) b) := by
  rw [mvalIrm_eq]
  refine hG.update ?_ fun a ↦ ?_
  · refine (hG.isStrictLinearOrderedSet hD).losIrm fun hbL ↦ hbX ?_
    exact ((hG.mem_losSet_iff hD b).mp hbL).left
  · rw [losIrm_eq, losSet_orderedPair, mem_insert_iff, hG.mem_losSet_iff hD, mem_insert_iff]
    grind

/-- Adding `b ∉ X` to `X` immediately before `a ∈ X` with `left a ﹫ ∅ = left b ﹫ ∅` in the
linearly ordered set at `left b ﹫ ∅` -/
theorem IsSblLos.insert_before {X G a b : M} (hG : IsSblLos X G) (hbX : b ∉ X) (haX : a ∈ X)
    (hab : left a ﹫ ∅ = left b ﹫ ∅) : IsSblLos (insert b X) (mvalIlf G (left b ﹫ ∅) a b) := by
  have hD : left b ﹫ ∅ ∈ dom G := by
    rw [hG.mem_dom_iff]
    exact ⟨a, haX, hab⟩
  rw [mvalIlf_eq]
  refine hG.update ?_ fun c ↦ ?_
  · refine (hG.isStrictLinearOrderedSet hD).losIlf ?_ fun hbL ↦ hbX ?_
    · rw [hG.mem_losSet_iff hD]
      exact ⟨haX, hab⟩
    · exact ((hG.mem_losSet_iff hD b).mp hbL).left
  · rw [losIlf_eq, losSet_orderedPair, mem_insert_iff, hG.mem_losSet_iff hD, mem_insert_iff]
    grind

/-- `sngLosFn₀〘C〙₁` is `⋃_{x ∈ C} {!(left x ﹫ ∅, !({x}, ∅))}` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.sngLosFn₀ : L.RudimentaryTerm 1 :=
  (ᵣ0).iUnion
    ({ᵣ((ᵣ1).left ﹫ ∅, ᵣ(({ᵣ1} : L.RudimentaryTerm 2), ∅))} : L.RudimentaryTerm 2)

instance : (RudimentaryTerm.sngLosFn₀ : L.RudimentaryTerm 1).CharFree := by
  unfold RudimentaryTerm.sngLosFn₀; infer_instance

/-- The function `{(left x ﹫ ∅, ({x}, ∅)) | x ∈ C}`, giving each `x ∈ C` its own singleton
linearly ordered set -/
noncomputable def sngLosFn : ClassFunction M := fun C ↦ RudimentaryTerm.sngLosFn₀〘C〙₁

instance : (sngLosFn : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq RudimentaryTerm.sngLosFn₀ fun _ ↦ rfl

theorem mem_sngLosFn_iff {C z : M} :
    z ∈ sngLosFn C ↔ ∃ x ∈ C, z = !(left x ﹫ ∅, !(({x} : M), ∅)) := by
  simp [sngLosFn, RudimentaryTerm.sngLosFn₀]

theorem rel_sngLosFn_iff {C D L : M} :
    D [sngLosFn C] L ↔ ∃ x ∈ C, D = left x ﹫ ∅ ∧ L = !(({x} : M), ∅) := by
  simp [sngLosFn, RudimentaryTerm.sngLosFn₀]

/-- If the first values `left x ﹫ ∅` of the elements `x ∈ C` are distinct, then `sngLosFn C`
assigns the right linearly ordered sets to `C` -/
theorem isSblLos_sngLosFn {C : M} (hinj : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → left x ﹫ ∅ ≠ left y ﹫ ∅) :
    IsSblLos C (sngLosFn C) := by
  have hinj' {x y : M} (hx : x ∈ C) (hy : y ∈ C) (hxy : left x ﹫ ∅ = left y ﹫ ∅) : x = y := by
    by_contra hne
    exact hinj x hx y hy hne hxy
  have hF : IsFunction (sngLosFn C) := by
    refine ⟨fun z hz ↦ ?_, fun D L₁ L₂ h₁ h₂ ↦ ?_⟩
    · rw [mem_sngLosFn_iff] at hz
      obtain ⟨x, -, rfl⟩ := hz
      exact ⟨left x ﹫ ∅, !(({x} : M), ∅), rfl⟩
    rw [rel_sngLosFn_iff] at h₁ h₂
    obtain ⟨x₁, hx₁, rfl, rfl⟩ := h₁
    obtain ⟨x₂, hx₂, hD, rfl⟩ := h₂
    rw [hinj' hx₁ hx₂ hD]
  have hval {x : M} (hx : x ∈ C) : sngLosFn C ﹫ (left x ﹫ ∅) = !(({x} : M), ∅) :=
    hF.val_eq_of_rel (rel_sngLosFn_iff.mpr ⟨x, hx, rfl, rfl⟩)
  have hdom (D : M) : D ∈ dom (sngLosFn C) ↔ ∃ x ∈ C, left x ﹫ ∅ = D := by
    rw [mem_dom_iff]
    constructor
    · rintro ⟨L, hL⟩
      rw [rel_sngLosFn_iff] at hL
      obtain ⟨x, hx, rfl, -⟩ := hL
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨!(({x} : M), ∅), rel_sngLosFn_iff.mpr ⟨x, hx, rfl, rfl⟩⟩
  refine ⟨hF, hdom, fun {D} hD ↦ ?_, fun {D} hD a ↦ ?_⟩
  · obtain ⟨x, hx, rfl⟩ := (hdom D).mp hD
    rw [hval hx, isStrictLinearOrderedSet_orderedPair_iff]
    exact isStrictLinearOrder_empty_singleton x
  · obtain ⟨x, hx, rfl⟩ := (hdom D).mp hD
    rw [hval hx, losSet_orderedPair, mem_singleton_iff]
    constructor
    · rintro rfl
      exact ⟨hx, rfl⟩
    · rintro ⟨ha, hax⟩
      exact hinj' ha hx hax

/-- The data `(T, F)` of a semi-linearly ordered tree structure: a tree structure `T` and a
function `F` on its sibling partition -/
@[ext]
structure SLOTreeStructure (M : Type*) where
  /-- The tree structure -/
  ts : TreeStructure M
  /-- The function assigning linear orders to the sets in the sibling partition -/
  losfn : M

namespace SLOTreeStructure

variable (S : SLOTreeStructure M)

/-- The nodes -/
noncomputable abbrev nd : M := S.ts.nd

/-- The depth function -/
noncomputable abbrev dep : M := S.ts.dep

/-- The children function -/
noncomputable abbrev chd : M := S.ts.chd

/-- The roots -/
noncomputable abbrev rt : M := S.ts.rt

/-- The parent function -/
noncomputable abbrev prt : M := S.ts.prt

/-- The sibling function -/
noncomputable abbrev sbl : M := S.ts.sbl

/-- The sibling partition -/
noncomputable abbrev sblptn : M := S.ts.sblptn

/-- `S = (T, F)` is a semi-linearly ordered tree structure -/
structure IsSLOTreeStructure : Prop where
  isTreeStructure : S.ts.IsTreeStructure
  isOrderedPair {a : M} (ha : a ∈ S.nd) : IsOrderedPair a
  isFunction_left {a : M} (ha : a ∈ S.nd) : IsFunction (left a)
  dom_left_mem {a : M} (ha : a ∈ S.nd) : dom (left a) ∈ (ω : M) \ {∅}
  isFunction_losfn : IsFunction S.losfn
  dom_losfn : dom S.losfn = S.sblptn
  isFunction_losfn_val {X : M} (hX : X ∈ S.sblptn) : IsFunction (S.losfn ﹫ X)
  mem_dom_losfn_val_iff {X : M} (hX : X ∈ S.sblptn) (D : M) :
    D ∈ dom (S.losfn ﹫ X) ↔ ∃ a ∈ X, left a ﹫ ∅ = D
  isStrictLinearOrderedSet {X : M} (hX : X ∈ S.sblptn) {D : M} (hD : D ∈ dom (S.losfn ﹫ X)) :
    IsStrictLinearOrderedSet ((S.losfn ﹫ X) ﹫ D)
  mem_losSet_iff {X : M} (hX : X ∈ S.sblptn) {D : M} (hD : D ∈ dom (S.losfn ﹫ X)) (a : M) :
    a ∈ losSet ((S.losfn ﹫ X) ﹫ D) ↔ a ∈ X ∧ left a ﹫ ∅ = D

/-- The linearly ordered sets of the roots -/
noncomputable def rtlos : M := S.losfn ﹫ S.rt

/-- The linearly ordered sets of the children, on the nodes with children -/
noncomputable def chdlos : M := S.losfn !∘ S.chd

/-- The linearly ordered sets of the siblings, on the nodes -/
noncomputable def sbllos : M := S.losfn !∘ S.sbl

noncomputable instance : Decidable (S.rt = ∅) := Classical.propDecidable _

noncomputable instance (D : M) : Decidable (D ∈ dom S.rtlos) := Classical.propDecidable _

/-- `S_irmrt(b)`: `S` with a new root `b`, added as a maximum to the linearly ordered set of the
roots `a` with `left a ﹫ ∅ = D`, where `D = left b ﹫ ∅` -/
noncomputable def irmrt (b : M) : SLOTreeStructure M :=
  if S.rt = ∅ then ⟨S.ts.irt b, singletonFun {b} (singletonFun (left b ﹫ ∅) !({b}, ∅))⟩
  else if left b ﹫ ∅ ∉ dom S.rtlos then
    ⟨S.ts.irt b, mkeyIns (mvalIns S.losfn S.rt (left b ﹫ ∅) !({b}, ∅)) S.rt b⟩
  else ⟨S.ts.irt b, mkeyIns (mvalMvalIrm S.losfn S.rt (left b ﹫ ∅) b) S.rt b⟩

noncomputable instance (a : M) : Decidable (S.chd ﹫ a = ∅) := Classical.propDecidable _

noncomputable instance (a D : M) : Decidable (D ∈ dom (S.chdlos ﹫ a)) := Classical.propDecidable _

/-- `S_irmchd(a, b)`: `S` with a new child `b` of `a`, added as a maximum to the linearly ordered
set of the children `c` of `a` with `left c ﹫ ∅ = D`, where `D = left b ﹫ ∅` -/
noncomputable def irmchd (a b : M) : SLOTreeStructure M :=
  if S.chd ﹫ a = ∅ then
    ⟨S.ts.ionechd a b, update S.losfn {b} (singletonFun (left b ﹫ ∅) !({b}, ∅))⟩
  else if left b ﹫ ∅ ∉ dom (S.chdlos ﹫ a) then
    ⟨S.ts.ionechd a b, mkeyIns (mvalIns S.losfn (S.chd ﹫ a) (left b ﹫ ∅) !({b}, ∅)) (S.chd ﹫ a) b⟩
  else ⟨S.ts.ionechd a b, mkeyIns (mvalMvalIrm S.losfn (S.chd ﹫ a) (left b ﹫ ∅) b) (S.chd ﹫ a) b⟩

/-- `S_ilfsbl(a, b)`: `S` with a new sibling `b` of `a`, inserted immediately before `a` in the
linearly ordered set of the siblings `c` of `a` with `left c ﹫ ∅ = D`, where
`D = left a ﹫ ∅ = left b ﹫ ∅` -/
noncomputable def ilfsbl (a b : M) : SLOTreeStructure M :=
  ⟨S.ts.isbl a b, mkeyIns (mvalMvalIlf S.losfn (S.sbl ﹫ a) (left b ﹫ ∅) a b) (S.sbl ﹫ a) b⟩

noncomputable instance (C : M) : Decidable (C = ∅) := Classical.propDecidable _

/-- `S_asnchd(a, C)`: `S` with the set `C` of new children of the childless node `a`, each with
its own singleton linearly ordered set -/
noncomputable def asnchd (a C : M) : SLOTreeStructure M :=
  if C = ∅ then S else ⟨S.ts.ichd a C, update S.losfn C (sngLosFn C)⟩

/-- The empty semi-linearly ordered tree structure `(∅, ∅)` -/
noncomputable instance : EmptyCollection (SLOTreeStructure M) := ⟨⟨∅, ∅⟩⟩

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
@[simp]
theorem ts_empty : (∅ : SLOTreeStructure M).ts = ∅ := rfl

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
@[simp]
theorem losfn_empty : (∅ : SLOTreeStructure M).losfn = ∅ := rfl

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
@[simp]
theorem nd_empty : (∅ : SLOTreeStructure M).nd = ∅ := rfl

@[simp]
theorem sblptn_empty : (∅ : SLOTreeStructure M).sblptn = ∅ := TreeStructure.sblptn_empty

/-- The empty semi-linearly ordered tree structure is a semi-linearly ordered tree structure -/
theorem isSLOTreeStructure_empty : (∅ : SLOTreeStructure M).IsSLOTreeStructure where
  isTreeStructure := TreeStructure.isTreeStructure_empty
  isOrderedPair := by simp
  isFunction_left := by simp
  dom_left_mem := by simp
  isFunction_losfn := isFunction_empty
  dom_losfn := by simp
  isFunction_losfn_val := by simp
  mem_dom_losfn_val_iff := by simp
  isStrictLinearOrderedSet := by simp
  mem_losSet_iff := by simp

variable {S} {a X : M}

namespace IsSLOTreeStructure

variable (hS : S.IsSLOTreeStructure)
include hS

/-- A semi-linearly ordered tree structure with empty tree structure is empty -/
theorem eq_empty_of_ts_eq_empty (hT : S.ts = ∅) : S = ∅ := by
  have hF : S.losfn !: ∅ → ran S.losfn := by
    have h := isFunctionFromTo_dom_ran hS.isFunction_losfn
    rwa [hS.dom_losfn, sblptn, hT, TreeStructure.sblptn_empty] at h
  exact SLOTreeStructure.ext hT hF.eq_empty_of_dom_empty

/-- A nonempty semi-linearly ordered tree structure has a nonempty tree structure -/
theorem ts_ne_empty (hne : S ≠ ∅) : S.ts ≠ ∅ :=
  fun hT ↦ hne (hS.eq_empty_of_ts_eq_empty hT)

/-- `S.chdlos` is defined on the nodes with children -/
theorem mem_dom_chdlos_iff : a ∈ dom S.chdlos ↔ a ∈ S.nd ∧ S.chd ﹫ a ≠ ∅ := by
  have hT := hS.isTreeStructure
  rw [chdlos, mem_dom_comp_iff hS.isFunction_losfn hT.isFunction_chd, hT.dom_chd, hS.dom_losfn,
    sblptn, TreeStructure.mem_sblptn_iff]
  refine and_congr_right fun ha ↦ ?_
  suffices S.chd ﹫ a ∈ ran S.chd by tauto
  rw [hT.isFunction_chd.mem_ran_iff, hT.dom_chd]
  exact ⟨a, ha, rfl⟩

theorem chdlos_val (ha : a ∈ dom S.chdlos) : S.chdlos ﹫ a = S.losfn ﹫ (S.chd ﹫ a) :=
  comp_val hS.isFunction_losfn hS.isTreeStructure.isFunction_chd ha

omit [ModelsKP M] in
theorem isSblLos (hX : X ∈ S.sblptn) : IsSblLos X (S.losfn ﹫ X) :=
  ⟨hS.isFunction_losfn_val hX, hS.mem_dom_losfn_val_iff hX,
    fun hD ↦ hS.isStrictLinearOrderedSet hX hD, fun hD ↦ hS.mem_losSet_iff hX hD⟩

variable [HasOmega M]

/-- `S.sbllos` is defined on the nodes -/
theorem dom_sbllos : dom S.sbllos = S.nd := by
  have hT := hS.isTreeStructure
  rw [sbllos, dom_comp hS.isFunction_losfn ?_, hT.dom_sbl]
  intro X hX
  rw [hT.isFunction_sbl.mem_ran_iff, hT.dom_sbl] at hX
  obtain ⟨a, ha, rfl⟩ := hX
  rw [hS.dom_losfn]
  exact hT.sbl_val_mem_sblptn ha

theorem sbllos_val (ha : a ∈ S.nd) : S.sbllos ﹫ a = S.losfn ﹫ (S.sbl ﹫ a) := by
  rw [← hS.dom_sbllos] at ha
  exact comp_val hS.isFunction_losfn hS.isTreeStructure.isFunction_sbl ha

section Insert

omit [HasOmega M] in
theorem insert_not_mem_sblptn {b : M} (hbA : b ∉ S.nd) (X : M) : insert b X ∉ S.sblptn :=
  fun h ↦ hbA (hS.isTreeStructure.subset_nd_of_mem_sblptn h (mem_insert b X))

omit [ModelsKP M] [HasOmega M] in
/-- Let `T'` be a tree structure obtained from `S.ts` by adding nodes that are pairs `c` with
`left c` a function on a nonzero natural number, in whose sibling partition the set `X₀` is
replaced by `X₁`. Then `(T', F)` is a semi-linearly ordered tree structure if `F` is a function on
the sibling partition of `T'` that agrees with `S.losfn` on the old sets of siblings other than
`X₀`, and whose value on `X₁` is as required -/
theorem mk_of_sblptn {T' : TreeStructure M} {X₀ X₁ F : M} (hT' : T'.IsTreeStructure)
    (hnd : ∀ {c}, c ∈ T'.nd → c ∈ S.nd ∨
      (IsOrderedPair c ∧ IsFunction (left c) ∧ dom (left c) ∈ (ω : M) \ {∅}))
    (hsbl : ∀ {X}, X ∈ T'.sblptn ↔ X = X₁ ∨ (X ∈ S.sblptn ∧ X ≠ X₀))
    (hF : IsFunction F) (hdom : dom F = T'.sblptn)
    (hold : ∀ X ∈ S.sblptn, X ≠ X₀ → F ﹫ X = S.losfn ﹫ X)
    (hnew : IsSblLos X₁ (F ﹫ X₁)) :
    (⟨T', F⟩ : SLOTreeStructure M).IsSLOTreeStructure := by
  have hX {X : M} (hX : X ∈ T'.sblptn) : IsSblLos X (F ﹫ X) := by
    rw [hsbl] at hX
    rcases hX with rfl | ⟨hX, hX₀⟩
    · exact hnew
    rw [hold X hX hX₀]
    exact hS.isSblLos hX
  refine
    { isTreeStructure := hT'
      isOrderedPair := fun ha ↦ ?_
      isFunction_left := fun ha ↦ ?_
      dom_left_mem := fun ha ↦ ?_
      isFunction_losfn := hF
      dom_losfn := hdom
      isFunction_losfn_val := fun {_} hX' ↦ (hX hX').isFunction
      mem_dom_losfn_val_iff := fun {_} hX' ↦ (hX hX').mem_dom_iff
      isStrictLinearOrderedSet := fun {_} hX' {_} hD ↦ (hX hX').isStrictLinearOrderedSet hD
      mem_losSet_iff := fun {_} hX' {_} hD ↦ (hX hX').mem_losSet_iff hD }
  · rcases hnd ha with ha | hc
    · exact hS.isOrderedPair ha
    exact hc.left
  · rcases hnd ha with ha | hc
    · exact hS.isFunction_left ha
    exact hc.right.left
  · rcases hnd ha with ha | hc
    · exact hS.dom_left_mem ha
    exact hc.right.right

omit [HasOmega M] in
/-- The case `X₀ ∈ S.sblptn`: the value of `S.losfn` at `X₀`, modified to `H`, is moved to `X₁` -/
theorem mk_moveKey {T' : TreeStructure M} {X₀ X₁ H : M} (hT' : T'.IsTreeStructure)
    (hnd : ∀ {c}, c ∈ T'.nd → c ∈ S.nd ∨
      (IsOrderedPair c ∧ IsFunction (left c) ∧ dom (left c) ∈ (ω : M) \ {∅}))
    (hsbl : ∀ {X}, X ∈ T'.sblptn ↔ X = X₁ ∨ (X ∈ S.sblptn ∧ X ≠ X₀))
    (hX₀ : X₀ ∈ S.sblptn) (hX₁ : X₁ ∉ S.sblptn) (hH : IsSblLos X₁ H) :
    (⟨T', moveKey (update S.losfn X₀ H) X₀ X₁⟩ : SLOTreeStructure M).IsSLOTreeStructure := by
  have hX₀F : X₀ ∈ dom S.losfn := by rwa [hS.dom_losfn]
  have hG := hS.isFunction_losfn.update X₀ H
  have hdomG : dom (update S.losfn X₀ H) = S.sblptn := by
    rw [dom_update, insert_eq_self hX₀F, hS.dom_losfn]
  have hy : X₁ ∉ dom (update S.losfn X₀ H) := by rwa [hdomG]
  refine hS.mk_of_sblptn hT' hnd hsbl (hG.moveKey X₀ hy) ?_ (fun X hX hXX₀ ↦ ?_) ?_
  · ext X
    rw [dom_moveKey, hdomG, mem_insert_iff, mem_sdiff_iff, mem_singleton_iff, hsbl]
  · rw [val_moveKey_of_ne hG hy (by rwa [hdomG]) hXX₀,
      val_update_of_ne hS.isFunction_losfn H (by rwa [hS.dom_losfn]) hXX₀]
  · rwa [val_moveKey_self hG X₀ hy, val_update_self hS.isFunction_losfn]

/-- The case `X₀ ∉ S.sblptn` (i.e. `X₀ = ∅`): `S.losfn` is extended by the value `H` at `X₁` -/
theorem mk_update {T' : TreeStructure M} {X₀ X₁ H : M} (hT' : T'.IsTreeStructure)
    (hnd : ∀ {c}, c ∈ T'.nd → c ∈ S.nd ∨
      (IsOrderedPair c ∧ IsFunction (left c) ∧ dom (left c) ∈ (ω : M) \ {∅}))
    (hsbl : ∀ {X}, X ∈ T'.sblptn ↔ X = X₁ ∨ (X ∈ S.sblptn ∧ X ≠ X₀))
    (hX₀ : X₀ ∉ S.sblptn) (hX₁ : X₁ ∉ S.sblptn) (hH : IsSblLos X₁ H) :
    (⟨T', update S.losfn X₁ H⟩ : SLOTreeStructure M).IsSLOTreeStructure := by
  refine hS.mk_of_sblptn hT' hnd hsbl (hS.isFunction_losfn.update X₁ H) ?_
    (fun X hX hXX₀ ↦ ?_) ?_
  · ext X
    rw [dom_update, hS.dom_losfn, mem_insert_iff, hsbl]
    grind
  · exact val_update_of_ne hS.isFunction_losfn H (by rwa [hS.dom_losfn]) (by grind)
  · rwa [val_update_self hS.isFunction_losfn]

variable {b : M} (hb : IsOrderedPair b) (hbA : b ∉ S.nd) (hbf : IsFunction (left b))
  (hbd : dom (left b) ∈ (ω : M) \ {∅})
include hb hbA hbf hbd

omit hS [ModelsKP M] [HasOmega M] in
theorem hnd_of_insert {T' : TreeStructure M} (h : ∀ {c}, c ∈ T'.nd → c = b ∨ c ∈ S.nd) {c : M}
    (hc : c ∈ T'.nd) : c ∈ S.nd ∨
      (IsOrderedPair c ∧ IsFunction (left c) ∧ dom (left c) ∈ (ω : M) \ {∅}) := by
  rcases h hc with rfl | hc
  · exact Or.inr ⟨hb, hbf, hbd⟩
  exact Or.inl hc

/-- Inserting a new root `b` into a semi-linearly ordered tree structure gives a semi-linearly
ordered tree structure -/
theorem irmrt : (S.irmrt b).IsSLOTreeStructure := by
  have hT := hS.isTreeStructure
  have hT' := hT.irt hbA
  have hnd {c : M} (hc : c ∈ (S.ts.irt b).nd) : c = b ∨ c ∈ S.nd := by
    rwa [TreeStructure.nd_irt, mem_insert_iff] at hc
  have hnd' {c : M} := hnd_of_insert hb hbA hbf hbd hnd (c := c)
  have hsbl {X : M} := hT.mem_sblptn_irt_iff hbA (X := X)
  by_cases hrt : S.rt = ∅
  · -- no roots: `S` is empty
    have hrt' : S.ts.rt = ∅ := hrt
    have hA := hT.nd_eq_empty_of_rt_eq_empty hrt
    have hsblptn {X : M} (hX : X ∈ S.sblptn) : False := by
      have hXA := hT.subset_nd_of_mem_sblptn hX
      have hXne := TreeStructure.ne_empty_of_mem_sblptn hX
      rw [ne_empty_iff] at hXne
      obtain ⟨a, ha⟩ := hXne
      have haA : a ∈ S.ts.nd := hXA ha
      rw [hA] at haA
      simp at haA
    rw [SLOTreeStructure.irmrt, if_pos hrt]
    refine hS.mk_of_sblptn (X₀ := ∅) (X₁ := {b}) hT' hnd' (fun {X} ↦ ?_)
      (isFunction_singletonFun _ _) ?_ (fun X hX ↦ (hsblptn hX).elim) ?_
    · rw [hsbl, hrt', insert_empty_eq_singleton]
    · ext X
      rw [dom_singletonFun, mem_singleton_iff, hsbl, hrt', insert_empty_eq_singleton]
      grind
    · rw [singletonFun_val]
      exact isSblLos_singleton b
  have hrtX := TreeStructure.rt_mem_sblptn hrt
  have hG := hS.isSblLos hrtX
  have hbrt : b ∉ S.rt := fun h ↦ hbA (hT.subset_nd_of_mem_sblptn hrtX h)
  have hX₁ := hS.insert_not_mem_sblptn hbA S.rt
  rw [SLOTreeStructure.irmrt, if_neg hrt]
  by_cases hD : left b ﹫ ∅ ∈ dom S.rtlos
  · rw [if_neg (not_not.mpr hD), mkeyIns_eq, mvalMvalIrm_eq]
    rw [rtlos] at hD
    exact hS.mk_moveKey hT' hnd' hsbl hrtX hX₁ (hG.insert_of_mem hbrt hD)
  · rw [if_pos hD, mkeyIns_eq, mvalIns_eq]
    rw [rtlos] at hD
    exact hS.mk_moveKey hT' hnd' hsbl hrtX hX₁ (hG.insert_of_not_mem hD)

/-- Inserting a new child `b` of a node `a` into a semi-linearly ordered tree structure gives a
semi-linearly ordered tree structure -/
theorem irmchd (ha : a ∈ S.nd) : (S.irmchd a b).IsSLOTreeStructure := by
  have hT := hS.isTreeStructure
  have hT' := hT.ionechd ha hbA
  have hnd {c : M} (hc : c ∈ (S.ts.ionechd a b).nd) : c = b ∨ c ∈ S.nd := by
    rw [TreeStructure.ionechd, TreeStructure.nd_ichd, mem_union_iff, mem_singleton_iff] at hc
    tauto
  have hnd' {c : M} := hnd_of_insert hb hbA hbf hbd hnd (c := c)
  have hsbl {X : M} := hT.mem_sblptn_ionechd_iff ha hbA (X := X)
  by_cases hC : S.chd ﹫ a = ∅
  · have hC' : S.ts.chd ﹫ a = ∅ := hC
    rw [SLOTreeStructure.irmchd, if_pos hC]
    refine hS.mk_update (X₀ := ∅) hT' hnd' (fun {X} ↦ ?_) ?_ ?_ (isSblLos_singleton b)
    · rw [hsbl, hC', insert_empty_eq_singleton]
    · exact fun h ↦ TreeStructure.ne_empty_of_mem_sblptn h rfl
    · rw [← insert_empty_eq_singleton]
      exact hS.insert_not_mem_sblptn hbA ∅
  have hCX : S.chd ﹫ a ∈ S.sblptn := by
    rw [sblptn, TreeStructure.mem_sblptn_iff, hT.isFunction_chd.mem_ran_iff, hT.dom_chd]
    exact ⟨Or.inr ⟨a, ha, rfl⟩, hC⟩
  have hG := hS.isSblLos hCX
  have hbC : b ∉ S.chd ﹫ a := fun h ↦ hbA (hT.chd_subset a ha h)
  have hX₁ := hS.insert_not_mem_sblptn hbA (S.chd ﹫ a)
  have hchdlos : S.chdlos ﹫ a = S.losfn ﹫ (S.chd ﹫ a) :=
    hS.chdlos_val ((hS.mem_dom_chdlos_iff).mpr ⟨ha, hC⟩)
  rw [SLOTreeStructure.irmchd, if_neg hC]
  by_cases hD : left b ﹫ ∅ ∈ dom (S.chdlos ﹫ a)
  · rw [if_neg (not_not.mpr hD), mkeyIns_eq, mvalMvalIrm_eq]
    rw [hchdlos] at hD
    exact hS.mk_moveKey hT' hnd' hsbl hCX hX₁ (hG.insert_of_mem hbC hD)
  · rw [if_pos hD, mkeyIns_eq, mvalIns_eq]
    rw [hchdlos] at hD
    exact hS.mk_moveKey hT' hnd' hsbl hCX hX₁ (hG.insert_of_not_mem hD)

/-- Inserting a new sibling `b` of a node `a` with `left a ﹫ ∅ = left b ﹫ ∅`, immediately before
`a`, into a semi-linearly ordered tree structure gives a semi-linearly ordered tree structure -/
theorem ilfsbl (ha : a ∈ S.nd) (hab : left a ﹫ ∅ = left b ﹫ ∅) :
    (S.ilfsbl a b).IsSLOTreeStructure := by
  have hT := hS.isTreeStructure
  have hT' := hT.isbl_of_mem_nd ha hbA
  have hnd {c : M} (hc : c ∈ (S.ts.isbl a b).nd) : c = b ∨ c ∈ S.nd :=
    (hT.mem_nd_isbl_iff ha hbA).mp hc
  have hnd' {c : M} := hnd_of_insert hb hbA hbf hbd hnd (c := c)
  have hsbl {X : M} := hT.mem_sblptn_isbl_iff ha hbA (X := X)
  have hX₀ : S.sbl ﹫ a ∈ S.sblptn := hT.sbl_val_mem_sblptn ha
  have hbX : b ∉ S.sbl ﹫ a := fun h ↦ hbA (hT.subset_nd_of_mem_sblptn hX₀ h)
  rw [SLOTreeStructure.ilfsbl, mkeyIns_eq, mvalMvalIlf_eq]
  exact hS.mk_moveKey hT' hnd' hsbl hX₀ (hS.insert_not_mem_sblptn hbA (S.sbl ﹫ a))
    ((hS.isSblLos hX₀).insert_before hbX (hT.mem_sbl_val_self ha) hab)

omit hb hbA hbf hbd

/-- Assigning a set `C` of new children with distinct first values to a childless node `a` of a
semi-linearly ordered tree structure gives a semi-linearly ordered tree structure -/
theorem asnchd {C : M} (ha : a ∈ S.nd) (hCa : S.chd ﹫ a = ∅)
    (hC : ∀ x ∈ C, IsOrderedPair x ∧ IsFunction (left x) ∧ dom (left x) ∈ (ω : M) \ {∅})
    (hCA : C ∩ S.nd = ∅) (hinj : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → left x ﹫ ∅ ≠ left y ﹫ ∅) :
    (S.asnchd a C).IsSLOTreeStructure := by
  by_cases hCe : C = ∅
  · rw [SLOTreeStructure.asnchd, if_pos hCe]
    exact hS
  have hT := hS.isTreeStructure
  have hCa' : S.ts.chd ﹫ a = ∅ := hCa
  rw [SLOTreeStructure.asnchd, if_neg hCe]
  refine hS.mk_update (X₀ := ∅) (hT.ichd ha hCA) (fun hc ↦ ?_) (fun {X} ↦ ?_)
    (fun h ↦ TreeStructure.ne_empty_of_mem_sblptn h rfl) (fun h ↦ ?_) (isSblLos_sngLosFn hinj)
  · rw [TreeStructure.nd_ichd, mem_union_iff] at hc
    rcases hc with hc | hc
    · exact Or.inl hc
    exact Or.inr (hC _ hc)
  · rw [hT.mem_sblptn_ichd_iff ha hCA hCe, hCa', empty_union]
  · change C ≠ ∅ at hCe
    rw [ne_empty_iff] at hCe
    obtain ⟨c, hc⟩ := hCe
    exact TreeStructure.IsTreeStructure.not_mem_nd_of_mem_new hCA hc
      (hT.subset_nd_of_mem_sblptn h hc)

end Insert

end IsSLOTreeStructure

end SLOTreeStructure

end FirstOrder.Language.MemStructure
