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

* `SLOTreeStructure M` is `M`, viewed as semi-linearly ordered tree structures `(T, F)` coded by
  the sets `!(T, F)` (`SLOTreeStructure.mk T F`): a tree structure `S.ts` and a function
  `S.losfn` on its sibling partition;
* `S.IsSLOTreeStructure`: `T` is a tree structure whose nodes `a` are pairs with `left a` a
  function with domain in `ω \ {∅}`, and `F` assigns to each `X` in the sibling partition a
  function `F ﹫ X` sending each `D = left a ﹫ ∅` (`a ∈ X`) to a strictly linearly ordered set
  on `{a ∈ X | left a ﹫ ∅ = D}`;
* the components `S.nd`, `S.dep`, `S.chd`, `S.rt`, `S.prt`, `S.sbl`, `S.sblptn` of `S.ts`, and
  `S.rtlos = F ﹫ S.rt`, `S.chdlos = F !∘ S.chd` (on the nodes with children) and
  `S.sbllos = F !∘ S.sbl` (on `S.nd`), and `S.ndlos a`, the linearly ordered set containing the
  node `a`;
* the empty semi-linearly ordered tree structure `∅ = (∅, ∅)`;
* `S.IsEmbedding S' π`: `π` is an embedding of the tree structures that preserves the split of the
  siblings into linearly ordered sets and their orders, and `S.IsIsomorphism S' π`: `π` is a
  surjective embedding;
* `S.sngIso S'`: the unique isomorphism of structures with a single node.
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
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.sngLosFn₀ {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 1 :=
  (ᵣ0).iUnion
    ({ᵣ((ᵣ1).left ﹫ ∅, ᵣ(({ᵣ1} : L.RudimentaryTerm 2), ∅))} : L.RudimentaryTerm 2)

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (RudimentaryTerm.sngLosFn₀ : L.RudimentaryTerm 1).CharFree := by
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
def SLOTreeStructure (M : Type*) := M

namespace SLOTreeStructure

/-- The semi-linearly ordered tree structure `(T, F)`, coded as `!(T, F)` -/
noncomputable def mk (T : TreeStructure M) (F : M) : SLOTreeStructure M := (!(T.toM, F) : M)

variable (S : SLOTreeStructure M)

/-- The set coding a semi-linearly ordered tree structure -/
def toM : M := S

/-- The semi-linearly ordered tree structure coded by a set -/
def ofM (x : M) : SLOTreeStructure M := x

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] in
@[simp]
theorem toM_ofM (x : M) : (ofM x).toM = x := rfl

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] in
@[simp]
theorem ofM_toM : ofM S.toM = S := rfl

/-- The tree structure -/
noncomputable def ts : TreeStructure M := TreeStructure.ofM (left S.toM)

/-- The function assigning linear orders to the sets in the sibling partition -/
noncomputable def losfn : M := right S.toM

section Mk

variable (T : TreeStructure M) (F : M)

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
@[simp]
theorem toM_mk : (mk T F).toM = !(T.toM, F) := rfl

@[simp]
theorem ts_mk : (mk T F).ts = T := by
  simp [ts]

@[simp]
theorem losfn_mk : (mk T F).losfn = F := by
  simp [losfn]

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
theorem isOrderedPair_mk : IsOrderedPair (mk T F).toM := ⟨T.toM, F, rfl⟩

end Mk

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
  isOrderedPair_toM : IsOrderedPair S.toM
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

/-- The linearly ordered set containing the node `a`: the one of the siblings `c` of `a` with
`left c ﹫ ∅ = left a ﹫ ∅` -/
noncomputable def ndlos (a : M) : M := (S.sbllos ﹫ a) ﹫ (left a ﹫ ∅)

noncomputable instance : Decidable (S.rt = ∅) := Classical.propDecidable _

noncomputable instance (D : M) : Decidable (D ∈ dom S.rtlos) := Classical.propDecidable _

/-- `S_irmrt(b)`: `S` with a new root `b`, added as a maximum to the linearly ordered set of the
roots `a` with `left a ﹫ ∅ = D`, where `D = left b ﹫ ∅` -/
noncomputable def irmrt (b : M) : SLOTreeStructure M :=
  if S.rt = ∅ then mk (S.ts.irt b) (singletonFun {b} (singletonFun (left b ﹫ ∅) !({b}, ∅)))
  else if left b ﹫ ∅ ∉ dom S.rtlos then
    mk (S.ts.irt b) (mkeyIns (mvalIns S.losfn S.rt (left b ﹫ ∅) !({b}, ∅)) S.rt b)
  else mk (S.ts.irt b) (mkeyIns (mvalMvalIrm S.losfn S.rt (left b ﹫ ∅) b) S.rt b)

noncomputable instance (a : M) : Decidable (S.chd ﹫ a = ∅) := Classical.propDecidable _

noncomputable instance (a D : M) : Decidable (D ∈ dom (S.chdlos ﹫ a)) := Classical.propDecidable _

/-- `S_irmchd(a, b)`: `S` with a new child `b` of `a`, added as a maximum to the linearly ordered
set of the children `c` of `a` with `left c ﹫ ∅ = D`, where `D = left b ﹫ ∅` -/
noncomputable def irmchd (a b : M) : SLOTreeStructure M :=
  if S.chd ﹫ a = ∅ then
    mk (S.ts.ionechd a b) (update S.losfn {b} (singletonFun (left b ﹫ ∅) !({b}, ∅)))
  else if left b ﹫ ∅ ∉ dom (S.chdlos ﹫ a) then
    mk (S.ts.ionechd a b)
      (mkeyIns (mvalIns S.losfn (S.chd ﹫ a) (left b ﹫ ∅) !({b}, ∅)) (S.chd ﹫ a) b)
  else mk (S.ts.ionechd a b)
    (mkeyIns (mvalMvalIrm S.losfn (S.chd ﹫ a) (left b ﹫ ∅) b) (S.chd ﹫ a) b)

/-- `S_ilfsbl(a, b)`: `S` with a new sibling `b` of `a`, inserted immediately before `a` in the
linearly ordered set of the siblings `c` of `a` with `left c ﹫ ∅ = D`, where
`D = left a ﹫ ∅ = left b ﹫ ∅` -/
noncomputable def ilfsbl (a b : M) : SLOTreeStructure M :=
  mk (S.ts.isbl a b) (mkeyIns (mvalMvalIlf S.losfn (S.sbl ﹫ a) (left b ﹫ ∅) a b) (S.sbl ﹫ a) b)

noncomputable instance (C : M) : Decidable (C = ∅) := Classical.propDecidable _

/-- `S_asnchd(a, C)`: `S` with the set `C` of new children of the childless node `a`, each with
its own singleton linearly ordered set -/
noncomputable def asnchd (a C : M) : SLOTreeStructure M :=
  if C = ∅ then S else mk (S.ts.ichd a C) (update S.losfn C (sngLosFn C))

/-- The empty semi-linearly ordered tree structure `(∅, ∅)` -/
noncomputable instance : EmptyCollection (SLOTreeStructure M) := ⟨mk ∅ ∅⟩

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
theorem empty_eq_mk : (∅ : SLOTreeStructure M) = mk ∅ ∅ := rfl

@[simp]
theorem ts_empty : (∅ : SLOTreeStructure M).ts = ∅ := ts_mk ∅ ∅

@[simp]
theorem losfn_empty : (∅ : SLOTreeStructure M).losfn = ∅ := losfn_mk ∅ ∅

@[simp]
theorem nd_empty : (∅ : SLOTreeStructure M).nd = ∅ := by
  rw [nd, ts_empty, TreeStructure.nd_empty]

@[simp]
theorem sblptn_empty : (∅ : SLOTreeStructure M).sblptn = ∅ := by
  rw [sblptn, ts_empty, TreeStructure.sblptn_empty]

/-- The empty semi-linearly ordered tree structure is a semi-linearly ordered tree structure -/
theorem isSLOTreeStructure_empty : (∅ : SLOTreeStructure M).IsSLOTreeStructure where
  isOrderedPair_toM := isOrderedPair_mk ∅ ∅
  isTreeStructure := by
    rw [ts_empty]
    exact TreeStructure.isTreeStructure_empty
  isOrderedPair := by simp
  isFunction_left := by simp
  dom_left_mem := by simp
  isFunction_losfn := by
    rw [losfn_empty]
    exact isFunction_empty
  dom_losfn := by simp
  isFunction_losfn_val := by simp
  mem_dom_losfn_val_iff := by simp
  isStrictLinearOrderedSet := by simp
  mem_losSet_iff := by simp

theorem ts_irmrt (S : SLOTreeStructure M) (b : M) : (S.irmrt b).ts = S.ts.irt b := by
  unfold irmrt
  split_ifs <;> simp

theorem nd_irmrt (S : SLOTreeStructure M) (b : M) : (S.irmrt b).nd = insert b S.nd := by
  rw [nd, ts_irmrt, TreeStructure.nd_irt]

theorem nd_subset_nd_asnchd (S : SLOTreeStructure M) (a C : M) : S.nd ⊆ (S.asnchd a C).nd := by
  unfold asnchd
  split_ifs
  · exact subset_refl _
  · change S.ts.nd ⊆ (mk (S.ts.ichd a C) _).ts.nd
    rw [ts_mk, TreeStructure.nd_ichd]
    exact left_subset_union (x := S.ts.nd) (y := C)

theorem rt_empty : (∅ : SLOTreeStructure M).rt = ∅ := by
  rw [rt, ts_empty, TreeStructure.rt_empty]

theorem empty_irmrt (b : M) : (∅ : SLOTreeStructure M).irmrt b =
    mk ((∅ : TreeStructure M).irt b) (singletonFun {b} (singletonFun (left b ﹫ ∅) !({b}, ∅))) := by
  rw [irmrt, if_pos rt_empty, ts_empty]

theorem nd_empty_irmrt (b : M) : ((∅ : SLOTreeStructure M).irmrt b).nd = {b} := by
  rw [nd_irmrt, nd_empty, insert_empty_eq_singleton]

theorem rt_empty_irmrt (b : M) : ((∅ : SLOTreeStructure M).irmrt b).rt = {b} := by
  have hb : b ∉ (∅ : TreeStructure M).nd := by simp [TreeStructure.nd_empty]
  rw [rt, ts_irmrt, ts_empty, TreeStructure.isTreeStructure_empty.rt_irt hb,
    TreeStructure.rt_empty, insert_empty_eq_singleton]

theorem chd_empty_irmrt_val (b a : M) : ((∅ : SLOTreeStructure M).irmrt b).chd ﹫ a = ∅ := by
  rw [chd, ts_irmrt, ts_empty, TreeStructure.chd_irt, TreeStructure.chd_empty]
  by_cases hab : a = b
  · rw [hab, val_update_self isFunction_empty]
  · refine val_eq_empty_of_not_mem_dom ?_
    rw [dom_update, dom_empty, mem_insert_iff]
    simp [hab]

theorem rtlos_empty_irmrt (b : M) :
    ((∅ : SLOTreeStructure M).irmrt b).rtlos = singletonFun (left b ﹫ ∅) !({b}, ∅) := by
  rw [rtlos, rt_empty_irmrt, empty_irmrt, losfn_mk, singletonFun_val]


variable {S} {a X : M}

/-- `IsSLOTreeStructure` with all quantifiers bounded -/
theorem isSLOTreeStructure_iff [HasOmega M] :
    S.IsSLOTreeStructure ↔ IsOrderedPair S.toM ∧ S.ts.IsTreeStructure ∧
      (∀ a ∈ S.nd, IsOrderedPair a ∧ IsFunction (left a) ∧ IsNat (dom (left a)) ∧
        dom (left a) ≠ ∅) ∧
      IsFunction S.losfn ∧ dom S.losfn = S.sblptn ∧
      ∀ X ∈ S.sblptn, IsFunction (S.losfn ﹫ X) ∧
        (∀ D ∈ dom (S.losfn ﹫ X), ∃ a ∈ X, left a ﹫ ∅ = D) ∧
        (∀ a ∈ X, left a ﹫ ∅ ∈ dom (S.losfn ﹫ X)) ∧
        ∀ D ∈ dom (S.losfn ﹫ X), IsStrictLinearOrderedSet ((S.losfn ﹫ X) ﹫ D) ∧
          (∀ a ∈ losSet ((S.losfn ﹫ X) ﹫ D), a ∈ X ∧ left a ﹫ ∅ = D) ∧
          ∀ a ∈ X, left a ﹫ ∅ = D → a ∈ losSet ((S.losfn ﹫ X) ﹫ D) := by
  have hdom (x : M) : x ∈ (ω : M) \ {∅} ↔ IsNat x ∧ x ≠ ∅ := by
    rw [mem_sdiff_iff, mem_omega_iff, mem_singleton_iff]
  constructor
  · intro hS
    refine ⟨hS.isOrderedPair_toM, hS.isTreeStructure, fun a ha ↦ ?_, hS.isFunction_losfn,
      hS.dom_losfn, fun X hX ↦ ⟨hS.isFunction_losfn_val hX, fun D hD ↦ ?_, fun a ha ↦ ?_,
      fun D hD ↦ ⟨hS.isStrictLinearOrderedSet hX hD, fun a ha ↦ ?_, fun a ha haD ↦ ?_⟩⟩⟩
    · rw [← hdom]
      exact ⟨hS.isOrderedPair ha, hS.isFunction_left ha, hS.dom_left_mem ha⟩
    · rwa [← hS.mem_dom_losfn_val_iff hX]
    · rw [hS.mem_dom_losfn_val_iff hX]
      exact ⟨a, ha, rfl⟩
    · rwa [← hS.mem_losSet_iff hX hD]
    · rw [hS.mem_losSet_iff hX hD]
      exact ⟨ha, haD⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine
      { isOrderedPair_toM := h1
        isTreeStructure := h2
        isOrderedPair := fun ha ↦ (h3 _ ha).left
        isFunction_left := fun ha ↦ (h3 _ ha).right.left
        dom_left_mem := fun ha ↦ (hdom _).mpr (h3 _ ha).right.right
        isFunction_losfn := h4
        dom_losfn := h5
        isFunction_losfn_val := fun hX ↦ (h6 _ hX).left
        mem_dom_losfn_val_iff := fun hX D ↦ ?_
        isStrictLinearOrderedSet := fun {_} hX {_} hD ↦ ((h6 _ hX).right.right.right _ hD).left
        mem_losSet_iff := fun {_} hX {_} hD a ↦ ?_ }
    · constructor
      · exact (h6 _ hX).right.left D
      · rintro ⟨a, ha, rfl⟩
        exact (h6 _ hX).right.right.left a ha
    · have h := (h6 _ hX).right.right.right _ hD
      constructor
      · exact h.right.left a
      · rintro ⟨ha, haD⟩
        exact h.right.right a ha haD

namespace IsSLOTreeStructure

variable (hS : S.IsSLOTreeStructure)
include hS

/-- A semi-linearly ordered tree structure is the pair of its components -/
theorem eq_mk : S = SLOTreeStructure.mk S.ts S.losfn := by
  obtain ⟨T, F, hTF⟩ := hS.isOrderedPair_toM
  change S.toM = (SLOTreeStructure.mk S.ts S.losfn).toM
  simp [ts, losfn, hTF]

/-- A semi-linearly ordered tree structure with empty tree structure is empty -/
theorem eq_empty_of_ts_eq_empty (hT : S.ts = ∅) : S = ∅ := by
  have hF : S.losfn !: ∅ → ran S.losfn := by
    have h := isFunctionFromTo_dom_ran hS.isFunction_losfn
    rwa [hS.dom_losfn, sblptn, hT, TreeStructure.sblptn_empty] at h
  rw [hS.eq_mk, hT, hF.eq_empty_of_dom_empty]
  rfl

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

/-- A node lies in its linearly ordered set -/
theorem mem_losSet_ndlos (ha : a ∈ S.nd) : a ∈ losSet (S.ndlos a) := by
  have hT := hS.isTreeStructure
  have hX := hT.sbl_val_mem_sblptn ha
  have hD : left a ﹫ ∅ ∈ dom (S.losfn ﹫ (S.sbl ﹫ a)) := by
    rw [hS.mem_dom_losfn_val_iff hX]
    exact ⟨a, hT.mem_sbl_val_self ha, rfl⟩
  rw [ndlos, hS.sbllos_val ha, hS.mem_losSet_iff hX hD]
  exact ⟨hT.mem_sbl_val_self ha, rfl⟩

/-- Two nodes lie in the same linearly ordered set if and only if they are siblings with the same
first value `left a ﹫ ∅` -/
theorem ndlos_eq_iff (ha : a ∈ S.nd) {b : M} (hb : b ∈ S.nd) :
    S.ndlos a = S.ndlos b ↔ S.sbl ﹫ a = S.sbl ﹫ b ∧ left a ﹫ ∅ = left b ﹫ ∅ := by
  have hT := hS.isTreeStructure
  refine ⟨fun h ↦ ?_, fun ⟨hsbl, hkey⟩ ↦ ?_⟩
  swap
  · rw [ndlos, ndlos, hS.sbllos_val ha, hS.sbllos_val hb, hsbl, hkey]
  have hXb := hT.sbl_val_mem_sblptn hb
  have hDb : left b ﹫ ∅ ∈ dom (S.losfn ﹫ (S.sbl ﹫ b)) := by
    rw [hS.mem_dom_losfn_val_iff hXb]
    exact ⟨b, hT.mem_sbl_val_self hb, rfl⟩
  have hmem := hS.mem_losSet_ndlos ha
  rw [h, ndlos, hS.sbllos_val hb, hS.mem_losSet_iff hXb hDb] at hmem
  exact ⟨hT.sbl_val_of_mem_sblptn hXb hmem.left, hmem.right⟩

/-- The linearly ordered set of a node is strictly linearly ordered -/
theorem isStrictLinearOrderedSet_ndlos (ha : a ∈ S.nd) :
    IsStrictLinearOrderedSet (S.ndlos a) := by
  have hT := hS.isTreeStructure
  have hX := hT.sbl_val_mem_sblptn ha
  have hD : left a ﹫ ∅ ∈ dom (S.losfn ﹫ (S.sbl ﹫ a)) := by
    rw [hS.mem_dom_losfn_val_iff hX]
    exact ⟨a, hT.mem_sbl_val_self ha, rfl⟩
  rw [ndlos, hS.sbllos_val ha]
  exact hS.isStrictLinearOrderedSet hX hD

/-- A semi-linearly ordered tree structure with a single node `b` is `∅_irmrt(b)` -/
theorem eq_empty_irmrt {b : M} (hnd : S.nd = {b}) : S = (∅ : SLOTreeStructure M).irmrt b := by
  have hT := hS.isTreeStructure
  have hbnd : b ∈ S.nd := by
    rw [hnd]
    exact mem_singleton b
  have hTne : S.ts ≠ ∅ := fun h ↦ by
    have hnd' : S.nd = ∅ := by rw [nd, h, TreeStructure.nd_empty]
    rw [hnd'] at hbnd
    simp at hbnd
  have hbrt : b ∈ S.rt := by
    obtain ⟨r, hr⟩ := (ne_empty_iff _).mp (hT.rt_ne_empty hTne)
    have hr' := hr
    rw [TreeStructure.mem_rt_iff] at hr'
    have hrb : r = b := by
      have h := hr'.left
      rwa [← nd, hnd, mem_singleton_iff] at h
    rwa [← hrb]
  have hdepb : S.dep ﹫ b = ∅ := by
    rw [rt, TreeStructure.mem_rt_iff] at hbrt
    exact hbrt.right
  have hchdb : S.chd ﹫ b = ∅ := by
    ext c
    refine ⟨fun hc ↦ ?_, by simp⟩
    have hcb : c = b := by
      have h := hT.chd_subset b hbnd hc
      rwa [← nd, hnd, mem_singleton_iff] at h
    subst hcb
    have h := hT.dep_of_mem_chd c hbnd c hc
    rw [hdepb] at h
    exact (succ_ne_empty _ h.symm).elim
  have hdom : dom (MemStructure.update (∅ : M) b ∅) = {b} := by
    rw [dom_update, dom_empty, insert_empty_eq_singleton]
  have hdep : S.dep = MemStructure.update ∅ b ∅ := by
    refine hT.dep_fromTo.isFunction.ext (isFunction_empty.update b ∅) ?_ fun x hx ↦ ?_
    · rw [hdom, hT.dep_fromTo.dom_eq, ← nd, hnd]
    · rw [hT.dep_fromTo.dom_eq, ← nd, hnd, mem_singleton_iff] at hx
      rw [hx, hdepb, val_update_self isFunction_empty]
  have hchd : S.chd = MemStructure.update ∅ b ∅ := by
    refine hT.isFunction_chd.ext (isFunction_empty.update b ∅) ?_ fun x hx ↦ ?_
    · rw [hdom, hT.dom_chd, ← nd, hnd]
    · rw [hT.dom_chd, ← nd, hnd, mem_singleton_iff] at hx
      rw [hx, hchdb, val_update_self isFunction_empty]
  have hts : S.ts = (∅ : TreeStructure M).irt b := by
    rw [hT.eq_mk, TreeStructure.irt, TreeStructure.nd_empty, TreeStructure.dep_empty,
      TreeStructure.chd_empty, insert_empty_eq_singleton]
    change TreeStructure.mk S.nd S.dep S.chd = _
    rw [hnd, hdep, hchd]
  have hsblptn : S.sblptn = {{b}} := by
    ext X
    rw [sblptn, TreeStructure.mem_sblptn_iff, mem_singleton_iff, ← rt, ← chd]
    constructor
    · rintro ⟨hX | hX, hXne⟩
      · rw [hX]
        ext c
        rw [mem_singleton_iff]
        constructor
        · intro hc
          rw [rt, TreeStructure.mem_rt_iff, ← nd, hnd, mem_singleton_iff] at hc
          exact hc.left
        · rintro rfl
          exact hbrt
      · rw [mem_ran_iff] at hX
        obtain ⟨a, ha⟩ := hX
        have haX := hT.isFunction_chd.val_eq_of_rel ha
        have hab : a ∈ dom S.chd := by
          rw [mem_dom_iff]
          exact ⟨X, ha⟩
        rw [hT.dom_chd, ← nd, hnd, mem_singleton_iff] at hab
        rw [← haX, hab, hchdb] at hXne
        exact (hXne rfl).elim
    · rintro rfl
      refine ⟨Or.inl ?_, singleton_ne_empty b⟩
      ext c
      rw [mem_singleton_iff]
      constructor
      · rintro rfl
        exact hbrt
      · intro hc
        rw [rt, TreeStructure.mem_rt_iff, ← nd, hnd, mem_singleton_iff] at hc
        exact hc.left
  have hlosfn : S.losfn = singletonFun {b} (singletonFun (left b ﹫ ∅) !({b}, ∅)) := by
    refine hS.isFunction_losfn.ext (isFunction_singletonFun _ _) ?_ fun X hX ↦ ?_
    · rw [hS.dom_losfn, hsblptn, dom_singletonFun]
    have hXs : X ∈ S.sblptn := by rwa [← hS.dom_losfn]
    have hXb : X = {b} := by
      rwa [hsblptn, mem_singleton_iff] at hXs
    rw [hXb, singletonFun_val]
    rw [hXb] at hXs
    refine (hS.isFunction_losfn_val hXs).ext (isFunction_singletonFun _ _) ?_ fun D hD ↦ ?_
    · ext D
      rw [hS.mem_dom_losfn_val_iff hXs, dom_singletonFun, mem_singleton_iff]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [mem_singleton_iff] at ha
        rw [ha]
      · rintro rfl
        exact ⟨b, mem_singleton b, rfl⟩
    have hDb : D = left b ﹫ ∅ := by
      obtain ⟨a, ha, rfl⟩ := (hS.mem_dom_losfn_val_iff hXs D).mp hD
      rw [mem_singleton_iff] at ha
      rw [ha]
    rw [hDb, singletonFun_val]
    rw [hDb] at hD
    have hL := hS.isStrictLinearOrderedSet hXs hD
    have hset (a : M) : a ∈ losSet ((S.losfn ﹫ {b}) ﹫ (left b ﹫ ∅)) ↔ a = b := by
      rw [hS.mem_losSet_iff hXs hD, mem_singleton_iff]
      constructor
      · exact fun h ↦ h.left
      · rintro rfl
        exact ⟨rfl, rfl⟩
    obtain ⟨A, R, hAR⟩ := hL.isOrderedPair
    rw [hAR] at hL hset ⊢
    rw [isStrictLinearOrderedSet_orderedPair_iff] at hL
    simp only [losSet_orderedPair] at hset
    have hA : A = {b} := by
      ext a
      rw [hset, mem_singleton_iff]
    have hR : R = ∅ := by
      ext z
      refine ⟨fun hz ↦ ?_, by simp⟩
      obtain ⟨x, y, rfl⟩ := hL.isRelationOn.left hz
      have hx := (hset x).mp (hL.mem_left hz)
      have hy := (hset y).mp (hL.mem_right hz)
      rw [hx, hy] at hz
      exact (hL.irrefl b hz).elim
    rw [hA, hR]
  rw [hS.eq_mk, hts, hlosfn, empty_irmrt]

section Insert

omit [HasOmega M] in
theorem insert_not_mem_sblptn {b : M} (hbA : b ∉ S.nd) (X : M) : insert b X ∉ S.sblptn :=
  fun h ↦ hbA (hS.isTreeStructure.subset_nd_of_mem_sblptn h (mem_insert b X))

omit [HasOmega M] in
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
    (SLOTreeStructure.mk T' F).IsSLOTreeStructure := by
  suffices key : ∀ S' : SLOTreeStructure M, IsOrderedPair S'.toM → S'.ts = T' → S'.losfn = F →
      S'.IsSLOTreeStructure from
    key _ (SLOTreeStructure.isOrderedPair_mk T' F) (ts_mk T' F) (losfn_mk T' F)
  rintro S' hS' rfl rfl
  have hX {X : M} (hX : X ∈ S'.ts.sblptn) : IsSblLos X (S'.losfn ﹫ X) := by
    rw [hsbl] at hX
    rcases hX with rfl | ⟨hX, hX₀⟩
    · exact hnew
    rw [hold X hX hX₀]
    exact hS.isSblLos hX
  refine
    { isOrderedPair_toM := hS'
      isTreeStructure := hT'
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
    (SLOTreeStructure.mk T' (moveKey (update S.losfn X₀ H) X₀ X₁)).IsSLOTreeStructure := by
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
    (SLOTreeStructure.mk T' (update S.losfn X₁ H)).IsSLOTreeStructure := by
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

/-- `π` is an embedding of the semi-linearly ordered tree structure `S` into `S'`: an embedding of
the tree structures such that two nodes lie in the same linearly ordered set if and only if their
images do, and the order of each linearly ordered set is preserved -/
structure IsEmbedding (S S' : SLOTreeStructure M) (π : M) : Prop where
  isEmbedding_ts : S.ts.IsEmbedding S'.ts π
  ndlos_eq_iff {a b : M} (ha : a ∈ S.nd) (hb : b ∈ S.nd) :
    S'.ndlos (π ﹫ a) = S'.ndlos (π ﹫ b) ↔ S.ndlos a = S.ndlos b
  rel_losOdr {a b : M} (ha : a ∈ S.nd) (hb : b ∈ S.nd) (hab : S.ndlos a = S.ndlos b)
    (hrel : a [losOdr (S.ndlos a)] b) : (π ﹫ a) [losOdr (S'.ndlos (π ﹫ a))] (π ﹫ b)

/-- `π` is an isomorphism of the semi-linearly ordered tree structure `S` onto `S'`: a surjective
embedding -/
structure IsIsomorphism (S S' : SLOTreeStructure M) (π : M) : Prop where
  isEmbedding : S.IsEmbedding S' π
  ran_eq : ran π = S'.nd

omit [ModelsKP M] in
/-- An isomorphism of semi-linearly ordered tree structures is one of the tree structures -/
theorem IsIsomorphism.isIsomorphism_ts {S S' : SLOTreeStructure M} {π : M}
    (h : S.IsIsomorphism S' π) : S.ts.IsIsomorphism S'.ts π :=
  ⟨h.isEmbedding.isEmbedding_ts, h.ran_eq⟩

/-- `S.sngIso S' = {(b, c)}` for semi-linearly ordered tree structures `S` and `S'` with single
nodes `b` and `c`: the unique isomorphism of `S` onto `S'` -/
noncomputable def sngIso (S S' : SLOTreeStructure M) : M := S.ts.sngIso S'.ts

section SngIso

variable {S S' : SLOTreeStructure M} {b c π : M} (hnd : S.nd = {b}) (hnd' : S'.nd = {c})
include hnd hnd'

/-- `S.sngIso S'` is an isomorphism of `S` onto `S'` -/
theorem isIsomorphism_sngIso [HasOmega M] (hS : S.IsSLOTreeStructure)
    (hS' : S'.IsSLOTreeStructure) : S.IsIsomorphism S' (S.sngIso S') := by
  have hiso := TreeStructure.isIsomorphism_sngIso hnd hnd' hS.isTreeStructure hS'.isTreeStructure
  have hb : b ∈ S.nd := by
    rw [hnd]
    exact mem_singleton b
  refine ⟨⟨hiso.isEmbedding, ?_, ?_⟩, hiso.ran_eq⟩
  · intro a a' ha ha'
    rw [hnd, mem_singleton_iff] at ha ha'
    rw [ha, ha']
    exact iff_of_true rfl rfl
  · intro a a' ha ha' _ hrel
    rw [hnd, mem_singleton_iff] at ha ha'
    rw [ha, ha'] at hrel
    exact ((hS.isStrictLinearOrderedSet_ndlos hb).isStrictLinearOrder.irrefl b hrel).elim

/-- `S.sngIso S'` is the unique embedding of `S` into `S'` -/
theorem IsEmbedding.eq_sngIso (he : S.IsEmbedding S' π) : π = S.sngIso S' :=
  he.isEmbedding_ts.eq_sngIso hnd hnd'

end SngIso

end SLOTreeStructure

end FirstOrder.Language.MemStructure

/-! ### `Δ₀` definitions -/

namespace FirstOrder.Language

open FirstOrder Language DeltaZeroBoundedFormula

namespace RudimentaryTerm

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] {n : ℕ}

/-- The tree structure of the semi-linearly ordered tree structure coded by `r` -/
noncomputable def slTs (r : L.RudimentaryTerm n) : L.RudimentaryTerm n := r.left

/-- The function `losfn` of the semi-linearly ordered tree structure coded by `r` -/
noncomputable def slLosfn (r : L.RudimentaryTerm n) : L.RudimentaryTerm n := r.right

/-- The semi-linearly ordered tree structure `(r, s)` -/
noncomputable def slMk (r s : L.RudimentaryTerm n) : L.RudimentaryTerm n := ᵣ(r, s)

instance (r : L.RudimentaryTerm n) [r.CharFree] : r.slTs.CharFree := by
  unfold slTs; infer_instance

instance (r : L.RudimentaryTerm n) [r.CharFree] : r.slLosfn.CharFree := by
  unfold slLosfn; infer_instance

instance (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] : (slMk r s).CharFree := by
  unfold slMk; infer_instance

/-- `slRtlos₀〘S〙₁` is `S.rtlos` -/
noncomputable def slRtlos₀ : L.RudimentaryTerm 1 :=
  (ᵣ0 : L.RudimentaryTerm 1).slLosfn ﹫ (ᵣ0 : L.RudimentaryTerm 1).slTs.tsRt

/-- `slChdlos₀〘S〙₁` is `S.chdlos` -/
noncomputable def slChdlos₀ : L.RudimentaryTerm 1 :=
  (ᵣ0 : L.RudimentaryTerm 1).slLosfn.comp (ᵣ0 : L.RudimentaryTerm 1).slTs.tsChd

/-- `slSbllos₀〘S〙₁` is `S.sbllos` -/
noncomputable def slSbllos₀ : L.RudimentaryTerm 1 :=
  (ᵣ0 : L.RudimentaryTerm 1).slLosfn.comp (ᵣ0 : L.RudimentaryTerm 1).slTs.tsSbl

instance : (slRtlos₀ : L.RudimentaryTerm 1).CharFree := by
  unfold slRtlos₀; infer_instance

instance : (slChdlos₀ : L.RudimentaryTerm 1).CharFree := by
  unfold slChdlos₀; infer_instance

instance : (slSbllos₀ : L.RudimentaryTerm 1).CharFree := by
  unfold slSbllos₀; infer_instance

/-- `slNdOk₀〘S, a〙`: `a` is a pair with `left a` a function on a nonzero natural number -/
noncomputable def slNdOk₀ : L.DeltaZeroBoundedFormula 2 :=
  (ᵣ1 : L.RudimentaryTerm 2).isOrderedPair ⊓ (ᵣ1 : L.RudimentaryTerm 2).left.isFunction ⊓
    (ᵣ1 : L.RudimentaryTerm 2).left.dom.isNat ⊓ ∼((ᵣ1 : L.RudimentaryTerm 2).left.dom.isEq ∅)

instance : (slNdOk₀ : L.DeltaZeroBoundedFormula 2).RelFree := by
  unfold slNdOk₀; infer_instance

/-- `slLosOk₀〘S, X, D〙`: `S.losfn ﹫ X ﹫ D` is a strictly linearly ordered set on
`{a ∈ X | left a ﹫ ∅ = D}` -/
noncomputable def slLosOk₀ : L.DeltaZeroBoundedFormula 3 :=
  (((ᵣ0 : L.RudimentaryTerm 3).slLosfn ﹫ ᵣ1) ﹫ ᵣ2).isStrictLinearOrderedSet ⊓
    (((ᵣ0 : L.RudimentaryTerm 3).slLosfn ﹫ ᵣ1) ﹫ ᵣ2).left.allMem
      ((ᵣ3 : L.RudimentaryTerm 4).isMem (ᵣ1) ⊓ ((ᵣ3 : L.RudimentaryTerm 4).left ﹫ ∅).isEq (ᵣ2)) ⊓
    (ᵣ1 : L.RudimentaryTerm 3).allMem
      (((ᵣ3 : L.RudimentaryTerm 4).left ﹫ ∅).isEq (ᵣ2) ⟹
        (ᵣ3 : L.RudimentaryTerm 4).isMem (((ᵣ0).slLosfn ﹫ ᵣ1) ﹫ ᵣ2).left)

instance : (slLosOk₀ : L.DeltaZeroBoundedFormula 3).RelFree := by
  unfold slLosOk₀; infer_instance

/-- `slSblOk₀〘S, X〙`: Clause 4 of a semi-linearly ordered tree structure at `X` -/
noncomputable def slSblOk₀ : L.DeltaZeroBoundedFormula 2 :=
  ((ᵣ0 : L.RudimentaryTerm 2).slLosfn ﹫ ᵣ1).isFunction ⊓
    ((ᵣ0 : L.RudimentaryTerm 2).slLosfn ﹫ ᵣ1).dom.allMem
      ((ᵣ1 : L.RudimentaryTerm 3).exMem (((ᵣ3 : L.RudimentaryTerm 4).left ﹫ ∅).isEq (ᵣ2))) ⊓
    (ᵣ1 : L.RudimentaryTerm 2).allMem
      (((ᵣ2 : L.RudimentaryTerm 3).left ﹫ ∅).isMem ((ᵣ0).slLosfn ﹫ ᵣ1).dom) ⊓
    ((ᵣ0 : L.RudimentaryTerm 2).slLosfn ﹫ ᵣ1).dom.allMem slLosOk₀

instance : (slSblOk₀ : L.DeltaZeroBoundedFormula 2).RelFree := by
  unfold slSblOk₀; infer_instance

/-- `isSLOTreeStructure₀〘S〙` says that `S` is a semi-linearly ordered tree structure, as in
`isSLOTreeStructure_iff` -/
noncomputable def isSLOTreeStructure₀ : L.DeltaZeroBoundedFormula 1 :=
  (ᵣ0 : L.RudimentaryTerm 1).isOrderedPair ⊓ (ᵣ0 : L.RudimentaryTerm 1).slTs.isTreeStructure ⊓
    (ᵣ0 : L.RudimentaryTerm 1).slTs.tsNd.allMem slNdOk₀ ⊓
    (ᵣ0 : L.RudimentaryTerm 1).slLosfn.isFunction ⊓
    (ᵣ0 : L.RudimentaryTerm 1).slLosfn.dom.isEq (ᵣ0).slTs.tsSblptn ⊓
    (ᵣ0 : L.RudimentaryTerm 1).slTs.tsSblptn.allMem slSblOk₀

instance : (isSLOTreeStructure₀ : L.DeltaZeroBoundedFormula 1).RelFree := by
  unfold isSLOTreeStructure₀; infer_instance


section Operations

variable (R : L.RudimentaryTerm 2)

/-- The new tree structure `T.irt b` of `irmrt`, for `[S, b]` -/
noncomputable def slIrmrtTs₀ : L.RudimentaryTerm 2 :=
  tsIrt₀.substBoundRud ![(ᵣ0 : L.RudimentaryTerm 2).slTs, ᵣ1]

instance : (slIrmrtTs₀ : L.RudimentaryTerm 2).CharFree := by
  unfold slIrmrtTs₀; infer_instance

/-- `slIrmrt₀〘S, b〙₂` is `S.irmrt b` -/
noncomputable def slIrmrt₀ : L.RudimentaryTerm 2 :=
  (slMk slIrmrtTs₀ ((∅ : L.RudimentaryTerm 2).update {ᵣ1}
      ((∅ : L.RudimentaryTerm 2).update ((ᵣ1 : L.RudimentaryTerm 2).left ﹫ ∅) ᵣ({ᵣ1}, ∅)))).ifTrue
      ((ᵣ0 : L.RudimentaryTerm 2).slTs.tsRt.isEq ∅) ∪
    (slMk slIrmrtTs₀ ((((ᵣ0 : L.RudimentaryTerm 2).slLosfn.mvalIns (ᵣ0).slTs.tsRt
        ((ᵣ1).left ﹫ ∅) ᵣ({ᵣ1}, ∅))).mkeyIns (ᵣ0).slTs.tsRt (ᵣ1))).ifTrue
      (∼((ᵣ0 : L.RudimentaryTerm 2).slTs.tsRt.isEq ∅) ⊓
        ∼(((ᵣ1 : L.RudimentaryTerm 2).left ﹫ ∅).isMem ((ᵣ0).slLosfn ﹫ (ᵣ0).slTs.tsRt).dom)) ∪
    (slMk slIrmrtTs₀ ((RudimentaryTerm.mvalMvalIrm (ᵣ0 : L.RudimentaryTerm 2).slLosfn (ᵣ0).slTs.tsRt
        ((ᵣ1).left ﹫ ∅) (ᵣ1)).mkeyIns (ᵣ0).slTs.tsRt (ᵣ1))).ifTrue
      (∼((ᵣ0 : L.RudimentaryTerm 2).slTs.tsRt.isEq ∅) ⊓
        ((ᵣ1 : L.RudimentaryTerm 2).left ﹫ ∅).isMem ((ᵣ0).slLosfn ﹫ (ᵣ0).slTs.tsRt).dom)

instance : (slIrmrt₀ : L.RudimentaryTerm 2).CharFree := by
  unfold slIrmrt₀; infer_instance

/-- The new tree structure `T.ionechd a b` of `irmchd`, for `[S, a, b]` -/
noncomputable def slIrmchdTs₀ : L.RudimentaryTerm 3 :=
  tsIchd₀.substBoundRud ![(ᵣ0 : L.RudimentaryTerm 3).slTs, ᵣ1, {ᵣ2}]

instance : (slIrmchdTs₀ : L.RudimentaryTerm 3).CharFree := by
  unfold slIrmchdTs₀; infer_instance

/-- `slIrmchd₀〘S, a, b〙₃` is `S.irmchd a b` -/
noncomputable def slIrmchd₀ : L.RudimentaryTerm 3 :=
  (slMk slIrmchdTs₀ ((ᵣ0 : L.RudimentaryTerm 3).slLosfn.update {ᵣ2}
      ((∅ : L.RudimentaryTerm 3).update ((ᵣ2 : L.RudimentaryTerm 3).left ﹫ ∅) ᵣ({ᵣ2}, ∅)))).ifTrue
      (((ᵣ0 : L.RudimentaryTerm 3).slTs.tsChd ﹫ ᵣ1).isEq ∅) ∪
    (slMk slIrmchdTs₀ (((ᵣ0 : L.RudimentaryTerm 3).slLosfn.mvalIns ((ᵣ0).slTs.tsChd ﹫ ᵣ1)
        ((ᵣ2).left ﹫ ∅) ᵣ({ᵣ2}, ∅)).mkeyIns ((ᵣ0).slTs.tsChd ﹫ ᵣ1) (ᵣ2))).ifTrue
      (∼(((ᵣ0 : L.RudimentaryTerm 3).slTs.tsChd ﹫ ᵣ1).isEq ∅) ⊓
        ∼(((ᵣ2 : L.RudimentaryTerm 3).left ﹫ ∅).isMem
          ((slChdlos₀.substBoundRud ![ᵣ0]) ﹫ ᵣ1).dom)) ∪
    (slMk slIrmchdTs₀ ((RudimentaryTerm.mvalMvalIrm (ᵣ0 : L.RudimentaryTerm 3).slLosfn
        ((ᵣ0).slTs.tsChd ﹫ ᵣ1) ((ᵣ2).left ﹫ ∅) (ᵣ2)).mkeyIns ((ᵣ0).slTs.tsChd ﹫ ᵣ1) (ᵣ2))).ifTrue
      (∼(((ᵣ0 : L.RudimentaryTerm 3).slTs.tsChd ﹫ ᵣ1).isEq ∅) ⊓
        ((ᵣ2 : L.RudimentaryTerm 3).left ﹫ ∅).isMem ((slChdlos₀.substBoundRud ![ᵣ0]) ﹫ ᵣ1).dom)

instance : (slIrmchd₀ : L.RudimentaryTerm 3).CharFree := by
  unfold slIrmchd₀; infer_instance

/-- `slIlfsbl₀〘S, a, b〙₃` is `S.ilfsbl a b` -/
noncomputable def slIlfsbl₀ : L.RudimentaryTerm 3 :=
  slMk (tsIsbl₀.substBoundRud ![(ᵣ0 : L.RudimentaryTerm 3).slTs, ᵣ1, ᵣ2])
    ((RudimentaryTerm.mvalMvalIlf (ᵣ0 : L.RudimentaryTerm 3).slLosfn ((ᵣ0).slTs.tsSbl ﹫ ᵣ1)
        ((ᵣ2).left ﹫ ∅) (ᵣ1) (ᵣ2)).mkeyIns ((ᵣ0).slTs.tsSbl ﹫ ᵣ1) (ᵣ2))

instance : (slIlfsbl₀ : L.RudimentaryTerm 3).CharFree := by
  unfold slIlfsbl₀; infer_instance

/-- `slAsnchd₀〘S, a, C〙₃` is `S.asnchd a C` -/
noncomputable def slAsnchd₀ : L.RudimentaryTerm 3 :=
  (ᵣ0 : L.RudimentaryTerm 3).ifTrue ((ᵣ2 : L.RudimentaryTerm 3).isEq ∅) ∪
    (slMk (tsIchd₀.substBoundRud ![(ᵣ0 : L.RudimentaryTerm 3).slTs, ᵣ1, ᵣ2])
      ((ᵣ0 : L.RudimentaryTerm 3).slLosfn.update (ᵣ2) (sngLosFn₀.substBoundRud ![ᵣ2]))).ifTrue
      ∼((ᵣ2 : L.RudimentaryTerm 3).isEq ∅)

instance : (slAsnchd₀ : L.RudimentaryTerm 3).CharFree := by
  unfold slAsnchd₀; infer_instance

end Operations

end RudimentaryTerm

namespace MemStructure

open RudimentaryTerm SLOTreeStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] {n : ℕ}

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_slTs (r : L.RudimentaryTerm n)
    (xs : Fin n → M) : r.slTs〘xs〙 = (SLOTreeStructure.ofM r〘xs〙).ts.toM := by
  simp [slTs, SLOTreeStructure.ts]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_slLosfn (r : L.RudimentaryTerm n)
    (xs : Fin n → M) : r.slLosfn〘xs〙 = (SLOTreeStructure.ofM r〘xs〙).losfn := by
  simp [slLosfn, SLOTreeStructure.losfn]

theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_slNdOk₀ (xs : Fin 2 → M) :
    (slNdOk₀ : L.DeltaZeroBoundedFormula 2).toBoundedFormula 〘xs〙 ↔
      IsOrderedPair (xs 1) ∧ IsFunction (left (xs 1)) ∧ IsNat (dom (left (xs 1))) ∧
        dom (left (xs 1)) ≠ ∅ := by
  simp [slNdOk₀, and_assoc]

theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_slLosOk₀ (xs : Fin 3 → M) :
    (slLosOk₀ : L.DeltaZeroBoundedFormula 3).toBoundedFormula 〘xs〙 ↔
      IsStrictLinearOrderedSet (((ofM (xs 0)).losfn ﹫ xs 1) ﹫ xs 2) ∧
        (∀ a ∈ losSet (((ofM (xs 0)).losfn ﹫ xs 1) ﹫ xs 2), a ∈ xs 1 ∧ left a ﹫ ∅ = xs 2) ∧
        ∀ a ∈ xs 1, left a ﹫ ∅ = xs 2 → a ∈ losSet (((ofM (xs 0)).losfn ﹫ xs 1) ﹫ xs 2) := by
  simp [slLosOk₀, IsStrictLinearOrderedSet, losSet, losOdr, Fin.snoc_nat, and_assoc]

theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_slSblOk₀ (xs : Fin 2 → M) :
    (slSblOk₀ : L.DeltaZeroBoundedFormula 2).toBoundedFormula 〘xs〙 ↔
      IsFunction ((ofM (xs 0)).losfn ﹫ xs 1) ∧
        (∀ D ∈ dom ((ofM (xs 0)).losfn ﹫ xs 1), ∃ a ∈ xs 1, left a ﹫ ∅ = D) ∧
        (∀ a ∈ xs 1, left a ﹫ ∅ ∈ dom ((ofM (xs 0)).losfn ﹫ xs 1)) ∧
        ∀ D ∈ dom ((ofM (xs 0)).losfn ﹫ xs 1),
          IsStrictLinearOrderedSet (((ofM (xs 0)).losfn ﹫ xs 1) ﹫ D) ∧
          (∀ a ∈ losSet (((ofM (xs 0)).losfn ﹫ xs 1) ﹫ D), a ∈ xs 1 ∧ left a ﹫ ∅ = D) ∧
          ∀ a ∈ xs 1, left a ﹫ ∅ = D → a ∈ losSet (((ofM (xs 0)).losfn ﹫ xs 1) ﹫ D) := by
  simp [slSblOk₀, realize_slLosOk₀, Fin.snoc_nat, and_assoc]

theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isSLOTreeStructure₀ [HasOmega M]
    (xs : Fin 1 → M) :
    (isSLOTreeStructure₀ : L.DeltaZeroBoundedFormula 1).toBoundedFormula 〘xs〙 ↔
      (ofM (xs 0)).IsSLOTreeStructure := by
  rw [isSLOTreeStructure_iff]
  simp [isSLOTreeStructure₀, realize_slNdOk₀, realize_slSblOk₀, Fin.snoc_nat, and_assoc]

/-- Being a semi-linearly ordered tree structure is `Δ₀` -/
instance [HasOmega M] : Class.DeltaZero (fun x : M ↦ (ofM x).IsSLOTreeStructure) Set.univ := by
  have h : (fun x : M ↦ (ofM x).IsSLOTreeStructure) =
      Multiclass.toClass
        (isSLOTreeStructure₀ : L.DeltaZeroBoundedFormula 1).toBoundedFormula.multiclass := by
    funext x
    rw [Multiclass.toClass_iff, BoundedFormula.multiclass, realize_isSLOTreeStructure₀]
    rfl
  rw [h]
  infer_instance

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_slMk (r s : L.RudimentaryTerm n)
    (xs : Fin n → M) :
    (slMk r s)〘xs〙 = (SLOTreeStructure.mk (TreeStructure.ofM r〘xs〙) s〘xs〙).toM := by
  simp [slMk]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_slRtlos₀ (xs : Fin 1 → M) :
    slRtlos₀〘xs〙 = (ofM (xs 0)).rtlos := by
  simp [slRtlos₀, rtlos]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_slChdlos₀ (xs : Fin 1 → M) :
    slChdlos₀〘xs〙 = (ofM (xs 0)).chdlos := by
  simp [slChdlos₀, chdlos]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_slSbllos₀ (xs : Fin 1 → M) :
    slSbllos₀〘xs〙 = (ofM (xs 0)).sbllos := by
  simp [slSbllos₀, sbllos]

instance : ClassFunction.DeltaZero (fun x : M ↦ (ofM x).ts.toM) Set.univ :=
  ClassFunction.deltaZero_of_eq (ᵣ0 : L.RudimentaryTerm 1).slTs fun _ ↦ by simp

instance : ClassFunction.DeltaZero (fun x : M ↦ (ofM x).losfn) Set.univ :=
  ClassFunction.deltaZero_of_eq (ᵣ0 : L.RudimentaryTerm 1).slLosfn fun _ ↦ by simp

instance : ClassFunction.DeltaZero (fun x : M ↦ (ofM x).rtlos) Set.univ :=
  ClassFunction.deltaZero_of_eq slRtlos₀ fun _ ↦ by simp

instance : ClassFunction.DeltaZero (fun x : M ↦ (ofM x).chdlos) Set.univ :=
  ClassFunction.deltaZero_of_eq slChdlos₀ fun _ ↦ by simp

instance : ClassFunction.DeltaZero (fun x : M ↦ (ofM x).sbllos) Set.univ :=
  ClassFunction.deltaZero_of_eq slSbllos₀ fun _ ↦ by simp

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_slIrmrt₀ (xs : Fin 2 → M) :
    slIrmrt₀〘xs〙 = ((ofM (xs 0)).irmrt (xs 1)).toM := by
  by_cases h₁ : (ofM (xs 0)).ts.rt = ∅
  · ext z
    simp [slIrmrt₀, slIrmrtTs₀, SLOTreeStructure.irmrt, h₁, singletonFun,
      DeltaZeroBoundedFormula.toBoundedFormula_not]
  by_cases h₂ : left (xs 1) ﹫ ∅ ∈ dom ((ofM (xs 0)).losfn ﹫ (ofM (xs 0)).ts.rt)
  · have h₂' : left (xs 1) ﹫ ∅ ∈ dom (ofM (xs 0)).rtlos := h₂
    ext z
    simp [slIrmrt₀, slIrmrtTs₀, SLOTreeStructure.irmrt, h₁, h₂, h₂',
      DeltaZeroBoundedFormula.toBoundedFormula_not]
  · have h₂' : left (xs 1) ﹫ ∅ ∉ dom (ofM (xs 0)).rtlos := h₂
    ext z
    simp [slIrmrt₀, slIrmrtTs₀, SLOTreeStructure.irmrt, h₁, h₂, h₂',
      DeltaZeroBoundedFormula.toBoundedFormula_not]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_slIrmchd₀ (xs : Fin 3 → M) :
    slIrmchd₀〘xs〙 = ((ofM (xs 0)).irmchd (xs 1) (xs 2)).toM := by
  by_cases h₁ : (ofM (xs 0)).ts.chd ﹫ xs 1 = ∅
  · have h₁' : (ofM (xs 0)).chd ﹫ xs 1 = ∅ := h₁
    ext z
    simp [slIrmchd₀, slIrmchdTs₀, SLOTreeStructure.irmchd, TreeStructure.ionechd, h₁, 
      singletonFun, DeltaZeroBoundedFormula.toBoundedFormula_not]
  by_cases h₂ : left (xs 2) ﹫ ∅ ∈ dom ((ofM (xs 0)).chdlos ﹫ xs 1)
  · ext z
    simp [slIrmchd₀, slIrmchdTs₀, SLOTreeStructure.irmchd, TreeStructure.ionechd, h₁, h₂,
      DeltaZeroBoundedFormula.toBoundedFormula_not]
  · ext z
    simp [slIrmchd₀, slIrmchdTs₀, SLOTreeStructure.irmchd, TreeStructure.ionechd, h₁, h₂,
      DeltaZeroBoundedFormula.toBoundedFormula_not]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_slIlfsbl₀ (xs : Fin 3 → M) :
    slIlfsbl₀〘xs〙 = ((ofM (xs 0)).ilfsbl (xs 1) (xs 2)).toM := by
  simp [slIlfsbl₀, SLOTreeStructure.ilfsbl]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_slAsnchd₀ (xs : Fin 3 → M) :
    slAsnchd₀〘xs〙 = ((ofM (xs 0)).asnchd (xs 1) (xs 2)).toM := by
  by_cases h : xs 2 = ∅
  · ext z
    simp [slAsnchd₀, SLOTreeStructure.asnchd, h]
  · ext z
    simp [slAsnchd₀, SLOTreeStructure.asnchd, h, sngLosFn, Matrix.fun_fin_one_eq,
      DeltaZeroBoundedFormula.toBoundedFormula_not]

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ ((ofM (ys 0)).irmrt (ys 1)).toM)
    Set.univ :=
  MulticlassFunction.deltaZero_of_eq slIrmrt₀ fun _ ↦ by simp

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 3 → M ↦ ((ofM (ys 0)).irmchd (ys 1) (ys 2)).toM) Set.univ :=
  MulticlassFunction.deltaZero_of_eq slIrmchd₀ fun _ ↦ by simp

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 3 → M ↦ ((ofM (ys 0)).ilfsbl (ys 1) (ys 2)).toM) Set.univ :=
  MulticlassFunction.deltaZero_of_eq slIlfsbl₀ fun _ ↦ by simp

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 3 → M ↦ ((ofM (ys 0)).asnchd (ys 1) (ys 2)).toM) Set.univ :=
  MulticlassFunction.deltaZero_of_eq slAsnchd₀ fun _ ↦ by simp

section Wrappers

/-! ### Semi-linearly ordered tree structures as sets

Named functions on codes of semi-linearly ordered tree structures, so that conditions built from
them are recognized as definable. -/

open SLOTreeStructure in
/-- `x` codes a semi-linearly ordered tree structure -/
def IsSLOT : Class M := fun x ↦ (ofM x).IsSLOTreeStructure

open SLOTreeStructure in
/-- The nodes `P_nd` -/
noncomputable def ndOf : ClassFunction M := fun P ↦ (ofM P).nd

open SLOTreeStructure in
/-- The roots `P_rt` -/
noncomputable def rtOf : ClassFunction M := fun P ↦ (ofM P).rt

open SLOTreeStructure in
/-- `P_rtlos` -/
noncomputable def rtlosOf : ClassFunction M := fun P ↦ (ofM P).rtlos

open SLOTreeStructure in
/-- `P_chd(p)` -/
noncomputable def chdOf (P p : M) : M := (ofM P).chd ﹫ p

open SLOTreeStructure in
/-- `P_prt(p)` -/
noncomputable def prtOf (P p : M) : M := (ofM P).prt ﹫ p

open SLOTreeStructure in
/-- `P_chdlos(p)` -/
noncomputable def chdlosOf (P p : M) : M := (ofM P).chdlos ﹫ p

open SLOTreeStructure in
/-- `P_irmrt(b)` -/
noncomputable def irmrtOf (P b : M) : M := ((ofM P).irmrt b).toM

open SLOTreeStructure in
/-- `P_irmchd(a, b)` -/
noncomputable def irmchdOf (P a b : M) : M := ((ofM P).irmchd a b).toM

open SLOTreeStructure in
/-- `P_ilfsbl(a, b)` -/
noncomputable def ilfsblOf (P a b : M) : M := ((ofM P).ilfsbl a b).toM

open SLOTreeStructure in
/-- `P_asnchd(a, C)` -/
noncomputable def asnchdOf (P a C : M) : M := ((ofM P).asnchd a C).toM

instance [HasOmega M] : (IsSLOT : Class M).DeltaZero Set.univ := by
  unfold IsSLOT; infer_instance

instance : (ndOf : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq (ᵣ0 : L.RudimentaryTerm 1).slTs.tsNd fun _ ↦ by simp [ndOf]

instance : (rtOf : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq (ᵣ0 : L.RudimentaryTerm 1).slTs.tsRt fun _ ↦ by simp [rtOf]

instance : (rtlosOf : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq slRtlos₀ fun _ ↦ by simp [rtlosOf]

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ chdOf (ys 0) (ys 1)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ ((ᵣ0 : L.RudimentaryTerm 2).slTs.tsChd ﹫ ᵣ1) fun _ _ ↦ by
    simp [chdOf]

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ prtOf (ys 0) (ys 1)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ ((ᵣ0 : L.RudimentaryTerm 2).slTs.tsPrt ﹫ ᵣ1) fun _ _ ↦ by
    simp [prtOf]

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ chdlosOf (ys 0) (ys 1)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ (slChdlos₀.substBoundRud ![ᵣ0] ﹫ ᵣ1) fun _ _ ↦ by
    simp [chdlosOf]

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ irmrtOf (ys 0) (ys 1)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ slIrmrt₀ fun _ _ ↦ by simp [irmrtOf]

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 3 → M ↦ irmchdOf (ys 0) (ys 1) (ys 2)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq slIrmchd₀ fun _ ↦ by simp [irmchdOf]

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 3 → M ↦ ilfsblOf (ys 0) (ys 1) (ys 2)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq slIlfsbl₀ fun _ ↦ by simp [ilfsblOf]

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 3 → M ↦ asnchdOf (ys 0) (ys 1) (ys 2)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq slAsnchd₀ fun _ ↦ by simp [asnchdOf]

end Wrappers

section Union

/-- The nodes `⋃_{X ∈ U} X_nd` of the elements of `U` -/
noncomputable def ndUnion : ClassFunction M := fun U ↦
  ((ᵣ0 : L.RudimentaryTerm 1).iUnion (ᵣ1 : L.RudimentaryTerm 2).slTs.tsNd)〘U〙₁

instance : (ndUnion : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq _ fun _ ↦ rfl

theorem mem_ndUnion_iff (U z : M) : z ∈ ndUnion U ↔ ∃ X ∈ U, z ∈ ndOf X := by
  simp [ndUnion, ndOf]

end Union

end MemStructure

end FirstOrder.Language
