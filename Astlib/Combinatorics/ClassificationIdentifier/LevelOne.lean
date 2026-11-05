/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Order.Pullback
import Astlib.Combinatorics.ClassificationIdentifier.TrivialExistence
/-!
# Classification identifiers of level one

* The nodes of the trees in `otci_1` have no children (`chdOf_eq_empty_of_mem_otci_one`), since
  their children would come from `ext_0 = ∅` (`ciExt_empty`); hence every node is a root
  (`ndOf_eq_rtOf_of_mem_otci_one`).
* `Z = trvAZero` is the unique trivial array in `aotci_0` occurring in `stduoci_0`
  (`aoc_eq_trvAZero_of_mem_stduoci_empty`); `dctUZero` is the standard
  `uoci_0` with array `Z` and `ctp = dct`. The nodes of a tree in `otci_1` all have the key `Z`
  (`aoc_uc_eq_trvAZero_of_mem_otci_one`).
* `tensorProdAZeroAZero P Q` for `P, Q ∈ aotci_0`: the array in `aotci_0` with label `(p, ∅)`,
  where `p` is the label of `P`.
* `tensorProdOneAZero P Q` for `P ∈ otci_1` and `Q ∈ aotci_0`: the copy of `P` in which every
  node `(U, l)` is relabeled to `(U, (l, U_aoc ⊗ Q))`, built as a single linearly ordered set of
  roots (`rtLosSLOT`) with the order pulled back from `P`.
* `trvuoci_0 = {dctUZero}` (`trvuoci_empty`); the nodes of the trees in `otci_1` are the pairs
  `(dctUZero, l)` (`exists_eq_of_mem_otci_one`), and conversely a linearly ordered set of such pairs
  is a tree in `otci_1` (`rtLosSLOT_mem_otci_one`); `P ⊗ Q ∈ otci_1` and `P ⊗ Q ∈ aotci_1`
  (`tensorProdOneAZero_mem_otci`, `tensorProdAOneAZero_mem_aotci`).
* `tensorProdAOneAZero P Q` for `P ∈ aotci_1` and `Q ∈ aotci_0`: the array in `aotci_1` with
  entries `(P ↾ 1 ⊗ Q)(0)` and `P(1) ⊗ Q`.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M] {p P : M}

/-- The nodes of the trees in `otci_1` have no children -/
theorem chdOf_eq_empty_of_mem_otci_one (hP : P ∈ otci ((1 : ℕ) : M)) (hp : p ∈ ndOf P) :
    chdOf P p = ∅ := by
  rw [mem_otci_iff_of_ne_empty natCast_one_ne_empty] at hP
  obtain ⟨-, -, -, -, hnd⟩ := hP
  have hchd := (hnd p hp).left
  rw [sUnion_natCast_one, extL_ciRec_restrict empty_mem_natCast_one, ciExt_empty] at hchd
  rw [empty_iff]
  intro q hq
  obtain ⟨q', hq', -⟩ := (hchd (aoc (uc q))).mp ⟨q, hq, rfl⟩
  simp at hq'

/-- Every node of a tree in `otci_1` is a root -/
theorem ndOf_eq_rtOf_of_mem_otci_one (hP : P ∈ otci ((1 : ℕ) : M)) : ndOf P = rtOf P := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := isSLOT_of_mem_otci hP
  have hT := hS.isTreeStructure
  ext a
  refine ⟨fun ha ↦ ?_, mem_ndOf_of_mem_rtOf⟩
  by_contra hart
  have ha' : a ∈ (SLOTreeStructure.ofM P).ts.nd \ (SLOTreeStructure.ofM P).ts.rt := by
    rw [mem_sdiff_iff]
    exact ⟨ha, hart⟩
  have hempty : chdOf P (prtOf P a) = ∅ :=
    chdOf_eq_empty_of_mem_otci_one hP (hT.prt_val_mem_nd ha')
  have hchd : a ∈ chdOf P (prtOf P a) := hT.mem_chd_prt_val ha'
  rw [hempty] at hchd
  simp at hchd

/-- `Z = {(0, ∅_slots_irmrt((otci0Uc, ∅)))}`: the unique trivial array in `aotci_0` occurring in
`stduoci_0` (`aoc_eq_trvAZero_of_mem_stduoci_empty`) -/
noncomputable def trvAZero : M := singletonFun ∅ (trvTree otci0Uc)

/-- The standard `uoci_0` with array `Z` and `ctp = dct`:
`{(0, Z), (1, ∅), (2, dct), (3, (0, r)), (4, lf)}`, where `r = (otci0Uc, ∅)` is the root of
`Z(0)` -/
noncomputable def dctUZero : M := cc (cc (ciTriple trvAZero ∅ dct) !(∅, !(otci0Uc, ∅))) lf

/-- The array of every element of `stduoci_0` is `Z` -/
theorem aoc_eq_trvAZero_of_mem_stduoci_empty {U : M} (hU : U ∈ stduoci (∅ : M)) :
    aoc U = trvAZero := by
  rw [mem_stduoci_iff, mem_uoci_iff_of_mem_omega empty_mem_omega] at hU
  obtain ⟨⟨-, -, haoc, -⟩, hstd⟩ := hU
  have hA := (mem_finaotci_iff.mp haoc).left
  have h0 : (∅ : M) ∈ succ ∅ := mem_succ_self ∅
  have hT := val_mem_otci_of_mem_aotci hA h0
  rw [mem_otci_empty_iff] at hT
  obtain ⟨l, -, hl⟩ := hT
  obtain ⟨hf, hdom, -, -⟩ := mem_aotci_iff.mp hA
  have hr : !(otci0Uc, l) ∈ ndOf (aoc U ﹫ ∅) := by
    rw [hl, ndOf_irmrtOf_emptySLOT]
    exact mem_singleton _
  have hrt : !(otci0Uc, l) ∈ rtOf (aoc U ﹫ ∅) := by
    rw [hl, rtOf_irmrtOf_emptySLOT]
    exact mem_singleton _
  have hlbl := (hstd ∅ h0 _ hr).left ⟨isEven_empty, hrt⟩
  rw [lbl_orderedPair] at hlbl
  rw [hlbl] at hl
  refine hf.ext (isFunction_singletonFun _ _) ?_ fun i hi ↦ ?_
  · rw [hdom, trvAZero, dom_singletonFun, succ, insert_empty_eq_singleton]
  rw [hdom] at hi
  rcases mem_or_eq_of_mem_succ hi with hi | rfl
  · simp at hi
  rw [hl, trvAZero, singletonFun_val, trvTree]

/-- The nodes of the trees in `otci_1` have the key `Z` -/
theorem aoc_uc_eq_trvAZero_of_mem_otci_one (hP : P ∈ otci ((1 : ℕ) : M)) (hp : p ∈ ndOf P) :
    aoc (uc p) = trvAZero := by
  rw [mem_otci_iff_of_ne_empty natCast_one_ne_empty] at hP
  obtain ⟨-, hnd, -⟩ := hP
  have huc := (hnd p hp).left
  rw [sUnion_natCast_one, stduociL_ciRec_restrict empty_mem_natCast_one] at huc
  exact aoc_eq_trvAZero_of_mem_stduoci_empty huc

/-- The label of the single node of the tree of an array in `aotci_0` -/
noncomputable def aotci0Lbl (P : M) : M := lbl (⋃₀ ndOf (P ﹫ ∅))

/-- `P ⊗ Q` for `P, Q ∈ aotci_0`: the array in `aotci_0` with label `(p, ∅)`, where `p` is the
label of `P` -/
noncomputable def tensorProdAZeroAZero (P _Q : M) : M :=
  singletonFun ∅ (irmrtOf emptySLOT !(otci0Uc, !(aotci0Lbl P, ∅)))

instance : MulticlassFunction.Definable (fun ys : Fin 2 → M ↦ tensorProdAZeroAZero (ys 0) (ys 1))
    Set.univ := by
  unfold tensorProdAZeroAZero aotci0Lbl singletonFun; infer_instance

/-- The relabeling `(U, l) ↦ (U, (l, U_aoc ⊗ Q))` of the nodes of `P` -/
noncomputable def tensorProdOneAZeroRelabel (P Q : M) : M :=
  (fun p ↦ !(uc p, !(lbl p, tensorProdAZeroAZero (aoc (uc p)) Q))) ↾₀ ndOf P

/-- The inverse `(U, (l, X)) ↦ (U, l)` of the relabeling, on the relabeled nodes -/
noncomputable def tensorProdOneAZeroUnlabel (P Q : M) : M :=
  (fun p ↦ !(uc p, left (lbl p))) ↾₀ ran (tensorProdOneAZeroRelabel P Q)

/-- `P ⊗ Q` for `P ∈ otci_1` and `Q ∈ aotci_0`: the copy of `P` in which every node `p` is
relabeled to `(p_uc, (p_lbl, W ⊗ Q))`, where `W = (p_uc)_aoc ∈ aotci_0`; its nodes are all roots,
ordered as their originals in `P` -/
noncomputable def tensorProdOneAZero (P Q : M) : M :=
  rtLosSLOT trvAZero !(ran (tensorProdOneAZeroRelabel P Q),
    pullback (tensorProdOneAZeroUnlabel P Q) (losOdr (rtlosOf P ﹫ trvAZero))
      (ran (tensorProdOneAZeroRelabel P Q)))

/-- `P ⊗ Q` for `P ∈ aotci_1` and `Q ∈ aotci_0`: the array in `aotci_1` with `aotci_0` part
`P ↾ 1 ⊗ Q` and `otci_1` part `P(1) ⊗ Q` -/
noncomputable def tensorProdAOneAZero (P Q : M) : M :=
  cc (tensorProdAZeroAZero (P ↾ ((1 : ℕ) : M)) Q) (tensorProdOneAZero (P ﹫ ((1 : ℕ) : M)) Q)

section Membership

/-! ### The trivial `uoci_0` and the tensor products of level one -/

variable {B Q U : M}

omit [ModelsZF M] in
/-- `dctUZero` is the trivial `uoci` of level `0` built from `Z` -/
theorem dctUZero_eq_lfTrvUoci : (dctUZero : M) = lfTrvUoci trvAZero := rfl

theorem trvAotci_empty : trvAotci (∅ : M) = trvAZero := by
  obtain ⟨U, hU⟩ := exists_mem_trvuoci (M := M) empty_mem_omega
  rw [← aoc_eq_trvAotci empty_mem_omega hU]
  exact aoc_eq_trvAZero_of_mem_stduoci_empty (mem_trvuoci_iff.mp hU).left

theorem dctUZero_mem_trvuoci : dctUZero ∈ trvuoci (∅ : M) := by
  have h := lfTrvUoci_mem_trvuoci (M := M) empty_mem_omega isEven_empty
  rwa [trvAotci_empty] at h

/-- `dctUZero` is the only trivial `uoci` of level `0` -/
theorem eq_dctUZero_of_mem_trvuoci_empty (hU : U ∈ trvuoci (∅ : M)) : U = dctUZero := by
  have haoc : aoc U = trvAZero :=
    aoc_eq_trvAZero_of_mem_stduoci_empty (mem_trvuoci_iff.mp hU).left
  have hsig := sig_eq_empty_of_mem_trvuoci empty_mem_omega hU
  have hct := (mem_trvuoci_iff.mp hU).right.right
  have hUu := (mem_stduoci_iff.mp (mem_trvuoci_iff.mp hU).left).left
  rw [mem_uoci_iff_of_mem_omega empty_mem_omega] at hUu
  obtain ⟨hf, hdom, -, -, -, -, hdom3, hucf⟩ := hUu
  have hne3 : dom U ≠ ((3 : ℕ) : M) := fun h ↦ by
    rcases hdom3.mp h with ⟨-, ho⟩ | h'
    · exact not_isOdd_empty ho
    · exact ct_ne_dct (h'.symm.trans hct)
  have h3 : ((3 : ℕ) : M) ∈ dom U := by
    rcases hdom with h | h | h
    · exact (hne3 h).elim
    · rw [h]
      exact natCast_mem_natCast_of_lt (by omega)
    · rw [h]
      exact natCast_mem_natCast_of_lt (by omega)
  obtain ⟨⟨l, d, hld⟩, hl, hd, -, -, hdr5, h6⟩ := hucf h3
  have hl0 : ucflvl U = ∅ := by
    rcases mem_or_eq_of_mem_succ hl with h | h
    · simp at h
    · exact h
  have hdom5 : dom U = ((5 : ℕ) : M) := by
    rcases hdom with h | h | h
    · exact (hne3 h).elim
    · exact h
    · have h' := (h6 h).left
      rw [hl0] at h'
      simp at h'
  rw [ucfdcn, hld, dcn_orderedPair, ucflvl, hld, lvl_orderedPair] at hd
  rw [ucflvl, hld, lvl_orderedPair] at hl0
  subst hl0
  rw [haoc, trvAZero, singletonFun_val, ndOf_trvTree, mem_singleton_iff] at hd
  change U = lfTrvUoci trvAZero
  refine hf.ext (isFunction_lfTrvUoci _) (by rw [hdom5, dom_lfTrvUoci]) fun x hx ↦ ?_
  rw [hdom5] at hx
  obtain ⟨k, hk, rfl⟩ := exists_eq_natCast_of_mem_natCast hx
  rcases k with _ | _ | _ | _ | _ | k
  · exact haoc.trans (aoc_lfTrvUoci _).symm
  · exact hsig.trans (sig_lfTrvUoci _).symm
  · exact hct.trans (ctp_lfTrvUoci _).symm
  · change ucflvldcn U = ucflvldcn (lfTrvUoci trvAZero)
    rw [hld, hd, ucflvldcn_lfTrvUoci]
  · change ucfdr U = ucfdr (lfTrvUoci trvAZero)
    rw [hdr5.mp hdom5, ucfdr_lfTrvUoci]
  · omega

/-- `trvuoci_0 = {dctUZero}` -/
theorem trvuoci_empty : trvuoci (∅ : M) = {dctUZero} := by
  ext U
  rw [mem_singleton_iff]
  exact ⟨eq_dctUZero_of_mem_trvuoci_empty, fun h ↦ h ▸ dctUZero_mem_trvuoci⟩

theorem isOdd_one : IsOdd ((1 : ℕ) : M) := (isOdd_succ_iff empty_mem_omega).mpr isEven_empty

/-- The nodes of the trees in `otci_1` have the identifier `dctUZero` -/
theorem uc_eq_dctUZero_of_mem_otci_one (hP : P ∈ otci ((1 : ℕ) : M)) (hp : p ∈ ndOf P) :
    uc p = dctUZero := by
  have hr : p ∈ rtOf P := by
    rw [← ndOf_eq_rtOf_of_mem_otci_one hP]
    exact hp
  rw [mem_otci_iff_of_ne_empty natCast_one_ne_empty] at hP
  have h := hP.right.right.left p hr
  rw [sUnion_natCast_one, trvuociL_ciRec_restrict empty_mem_natCast_one] at h
  exact eq_dctUZero_of_mem_trvuoci_empty h

theorem lbl_mem_of_mem_otci_one (hP : P ∈ otci ((1 : ℕ) : M)) (hp : p ∈ ndOf P) :
    lbl p ∈ (𝕍 ω : M) :=
  (((mem_otci_iff_of_ne_empty natCast_one_ne_empty).mp hP).right.left p hp).right

/-- The nodes of the trees in `otci_1` are the pairs `(dctUZero, l)` with `l ∈ V_ω` -/
theorem exists_eq_of_mem_otci_one (hP : P ∈ otci ((1 : ℕ) : M)) (hp : p ∈ ndOf P) :
    ∃ l ∈ (𝕍 ω : M), p = !(dctUZero, l) := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := isSLOT_of_mem_otci hP
  obtain ⟨u, l, rfl⟩ := hS.isOrderedPair hp
  have huc := uc_eq_dctUZero_of_mem_otci_one hP hp
  have hl := lbl_mem_of_mem_otci_one hP hp
  rw [uc_orderedPair] at huc
  rw [lbl_orderedPair] at hl
  exact ⟨l, hl, by rw [huc]⟩

/-- A single linearly ordered set of nodes `(dctUZero, l)`, `l ∈ V_ω`, is a tree in `otci_1` -/
theorem rtLosSLOT_mem_otci_one (hB : losSet B ≠ ∅ → IsStrictLinearOrderedSet B)
    (hA : ∀ a ∈ losSet B, ∃ l ∈ (𝕍 ω : M), a = !(dctUZero, l)) :
    rtLosSLOT trvAZero B ∈ otci ((1 : ℕ) : M) := by
  have hdU := dctUZero_mem_trvuoci (M := M)
  have hdUs := (mem_trvuoci_iff.mp hdU).left
  have hS : IsSLOT (rtLosSLOT trvAZero B) := isSLOT_rtLosSLOT hB fun a ha ↦ by
    obtain ⟨l, -, rfl⟩ := hA a ha
    rw [left_orderedPair]
    exact ⟨⟨_, _, rfl⟩, isFunction_lfTrvUoci _,
      dom_mem_of_mem_uoci empty_mem_omega (mem_stduoci_iff.mp hdUs).left, aoc_lfTrvUoci _⟩
  rw [mem_otci_iff_of_ne_empty natCast_one_ne_empty]
  refine ⟨hS, fun p hp ↦ ?_, fun r hr ↦ ?_, fun he ↦ (isOdd_one.not_isEven he).elim,
    fun p hp ↦ ?_⟩
  · rw [sUnion_natCast_one, stduociL_ciRec_restrict empty_mem_natCast_one]
    rw [ndOf_rtLosSLOT] at hp
    obtain ⟨l, hl, rfl⟩ := hA p hp
    rw [uc_orderedPair, lbl_orderedPair]
    exact ⟨hdUs, hl⟩
  · rw [sUnion_natCast_one, trvuociL_ciRec_restrict empty_mem_natCast_one]
    rw [rtOf_rtLosSLOT] at hr
    obtain ⟨l, -, rfl⟩ := hA r hr
    rw [uc_orderedPair]
    exact hdU
  · rw [sUnion_natCast_one, extL_ciRec_restrict empty_mem_natCast_one, ciExt_empty]
    refine ⟨fun D ↦ iff_of_false ?_ ?_, fun q hq ↦ by simp at hq⟩
    · rintro ⟨c, hc, -⟩
      rw [chdOf_rtLosSLOT] at hc
      simp at hc
    · rintro ⟨q, hq, -⟩
      simp at hq

theorem losSet_empty : losSet (∅ : M) = ∅ :=
  left_of_not_isOrderedPair fun ⟨x, y, h⟩ ↦ orderedPair_ne_empty x y h.symm

theorem losOdr_empty : losOdr (∅ : M) = ∅ :=
  right_of_not_isOrderedPair fun ⟨x, y, h⟩ ↦ orderedPair_ne_empty x y h.symm

/-- The roots of a tree in `otci_1` form the linearly ordered set with key `Z` -/
theorem rtlosOf_of_mem_otci_one (hP : P ∈ otci ((1 : ℕ) : M)) :
    IsStrictLinearOrder (losOdr (rtlosOf P ﹫ trvAZero)) (ndOf P) ∧
      losSet (rtlosOf P ﹫ trvAZero) = ndOf P ∧
      (ndOf P ≠ ∅ → IsStrictLinearOrderedSet (rtlosOf P ﹫ trvAZero)) := by
  have hPs := isSLOT_of_mem_otci hP
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hPs
  have hrt := ndOf_eq_rtOf_of_mem_otci_one hP
  have hv (x : M) : (∅ : M) ﹫ x = ∅ := val_eq_empty_of_not_mem_dom (by simp)
  by_cases hne : ndOf P = ∅
  · have h0 : rtlosOf P ﹫ trvAZero = ∅ := by
      rw [eq_emptySLOT_of_ndOf_eq_empty hPs hne]
      change ((∅ : SLOTreeStructure M).losfn ﹫ (∅ : SLOTreeStructure M).rt) ﹫ trvAZero = ∅
      rw [SLOTreeStructure.losfn_empty, hv, hv]
    rw [h0, hne, losSet_empty, losOdr_empty]
    exact ⟨isStrictLinearOrder_empty, rfl, fun h ↦ (h rfl).elim⟩
  have hrtne : (SLOTreeStructure.ofM P).ts.rt ≠ ∅ := by
    change rtOf P ≠ ∅
    rwa [← hrt]
  have hX := TreeStructure.rt_mem_sblptn hrtne
  obtain ⟨a, ha⟩ : ∃ a, a ∈ ndOf P := by
    have h : ndOf P ≠ ∅ := hne
    rwa [ne_empty_iff] at h
  have hD : trvAZero ∈ dom ((SLOTreeStructure.ofM P).losfn ﹫ (SLOTreeStructure.ofM P).ts.rt) :=
    (hS.mem_dom_losfn_val_iff hX _).mpr ⟨a, by change a ∈ rtOf P; rw [← hrt]; exact ha,
      aoc_uc_eq_trvAZero_of_mem_otci_one hP ha⟩
  have hB := hS.isStrictLinearOrderedSet hX hD
  have hset : losSet (rtlosOf P ﹫ trvAZero) = ndOf P := by
    ext x
    change x ∈ losSet (((SLOTreeStructure.ofM P).losfn ﹫ (SLOTreeStructure.ofM P).ts.rt) ﹫
      trvAZero) ↔ _
    rw [hS.mem_losSet_iff hX hD]
    constructor
    · intro h
      have h1 : x ∈ rtOf P := h.left
      rw [← hrt] at h1
      exact h1
    · intro h
      refine ⟨?_, aoc_uc_eq_trvAZero_of_mem_otci_one hP h⟩
      change x ∈ rtOf P
      rwa [← hrt]
  refine ⟨?_, hset, fun _ ↦ hB⟩
  rw [← hset]
  exact hB.isStrictLinearOrder

/-- `P ⊗ Q ∈ aotci_0`, and it is hereditarily finite -/
theorem tensorProdAZeroAZero_mem (hP : P ﹫ ∅ ∈ otci (∅ : M)) (Q : M) :
    tensorProdAZeroAZero P Q ∈ aotci (∅ : M) ∧ tensorProdAZeroAZero P Q ∈ (𝕍 ω : M) := by
  have hP' := hP
  rw [mem_otci_empty_iff] at hP'
  obtain ⟨l, hl, hPl⟩ := hP'
  have hlbl : aotci0Lbl P = l := by
    rw [aotci0Lbl, hPl, ndOf_irmrtOf_emptySLOT, sUnion_singleton, lbl_orderedPair]
  have hb : !(otci0Uc, !(aotci0Lbl P, ∅)) ∈ (𝕍 ω : M) := by
    rw [hlbl]
    exact orderedPair_mem_vonNeumann_omega otci0Uc_mem_vonNeumann_omega
      (orderedPair_mem_vonNeumann_omega hl empty_mem_vonNeumann_omega)
  have hT : irmrtOf emptySLOT !(otci0Uc, !(aotci0Lbl P, ∅)) ∈ otci (∅ : M) := by
    rw [mem_otci_empty_iff, hlbl]
    exact ⟨_, orderedPair_mem_vonNeumann_omega hl empty_mem_vonNeumann_omega, rfl⟩
  have hTV : irmrtOf emptySLOT !(otci0Uc, !(aotci0Lbl P, ∅)) ∈ (𝕍 ω : M) := by
    refine mem_vonNeumann_omega_of_isSLOT (isSLOT_of_mem_otci hT) ?_ ?_ <;>
      rw [ndOf_irmrtOf_emptySLOT]
    · exact finite_singleton _
    · intro x hx
      rw [mem_singleton_iff] at hx
      rw [hx]
      exact hb
  have hdom : dom (tensorProdAZeroAZero P Q) = succ ∅ := by
    rw [tensorProdAZeroAZero, dom_singletonFun, succ, insert_empty_eq_singleton]
  refine ⟨mem_aotci_iff.mpr ⟨isFunction_singletonFun _ _, hdom, by simp, ?_⟩, ?_⟩
  · rw [tensorProdAZeroAZero, singletonFun_val]
    exact hT
  · refine (isFunction_singletonFun _ _).mem_vonNeumann_omega ?_ fun x hx ↦ ?_
    · change dom (tensorProdAZeroAZero P Q) ∈ _
      rw [hdom]
      exact mem_vonNeumann_omega_of_mem_omega (succ_mem_omega empty_mem_omega)
    · change x ∈ dom (tensorProdAZeroAZero P Q) at hx
      rw [hdom, succ, insert_empty_eq_singleton, mem_singleton_iff] at hx
      rw [hx, singletonFun_val]
      exact hTV

/-- The relabeled nodes of `P ⊗ Q` for `P ∈ otci_1` -/
theorem mem_ran_tensorProdOneAZeroRelabel_iff (hP : P ∈ otci ((1 : ℕ) : M)) (Q y : M) :
    y ∈ ran (tensorProdOneAZeroRelabel P Q) ↔
      ∃ p ∈ ndOf P, !(uc p, !(lbl p, tensorProdAZeroAZero (aoc (uc p)) Q)) = y := by
  have hres : IsSetRestrictedTo
      (fun p ↦ !(uc p, !(lbl p, tensorProdAZeroAZero (aoc (uc p)) Q))) (ndOf P) := by
    -- on the nodes of `P`, the relabeling agrees with one with the constant array `Z ⊗ Q`
    have h : IsSetRestrictedTo (fun p ↦ !(uc p, !(lbl p, tensorProdAZeroAZero trvAZero Q)))
        (ndOf P) := isSetRestrictedTo_of_definable _
    refine ⟨_, isFunction_toSetRestrictedTo h, dom_toSetRestrictedTo h, fun y hy ↦ ?_⟩
    rw [val_toSetRestrictedTo h hy]
    change _ = !(uc y, !(lbl y, tensorProdAZeroAZero (aoc (uc y)) Q))
    rw [aoc_uc_eq_trvAZero_of_mem_otci_one hP hy]
  exact mem_ran_toSetRestrictedTo_iff hres

/-- `P ⊗ Q ∈ otci_1` for `P ∈ otci_1` -/
theorem tensorProdOneAZero_mem_otci (hP : P ∈ otci ((1 : ℕ) : M)) (Q : M) :
    tensorProdOneAZero P Q ∈ otci ((1 : ℕ) : M) := by
  have hZ : trvAZero ﹫ ∅ ∈ otci (∅ : M) := by
    rw [trvAZero, singletonFun_val, mem_otci_empty_iff]
    exact ⟨∅, empty_mem_vonNeumann_omega, rfl⟩
  have hX := tensorProdAZeroAZero_mem hZ Q
  have hran (y : M) : y ∈ ran (tensorProdOneAZeroRelabel P Q) ↔
      ∃ p ∈ ndOf P, !(uc p, !(lbl p, tensorProdAZeroAZero (aoc (uc p)) Q)) = y :=
    mem_ran_tensorProdOneAZeroRelabel_iff hP Q y
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := isSLOT_of_mem_otci hP
  -- the inverse of the relabeling
  have hres' : IsSetRestrictedTo (fun y ↦ !(uc y, left (lbl y)))
      (ran (tensorProdOneAZeroRelabel P Q)) :=
    isSetRestrictedTo_of_definable _
  have hHG {p : M} (hp : p ∈ ndOf P) :
      !(uc !(uc p, !(lbl p, tensorProdAZeroAZero (aoc (uc p)) Q)),
        left (lbl !(uc p, !(lbl p, tensorProdAZeroAZero (aoc (uc p)) Q)))) = p := by
    obtain ⟨u, l, rfl⟩ := hS.isOrderedPair hp
    simp only [uc_orderedPair, lbl_orderedPair, left_orderedPair]
  refine rtLosSLOT_mem_otci_one (fun hne ↦ ?_) fun a ha ↦ ?_
  · rw [losSet_orderedPair] at hne
    rw [isStrictLinearOrderedSet_orderedPair_iff]
    refine (rtlosOf_of_mem_otci_one hP).left.pullback
      (isInjectionFromTo_toSetRestrictedTo hres' (fun y hy ↦ ?_) fun y hy y' hy' h ↦ ?_)
    · obtain ⟨p, hp, rfl⟩ := (hran y).mp hy
      rw [hHG hp]
      exact hp
    · obtain ⟨p, hp, rfl⟩ := (hran y).mp hy
      obtain ⟨p', hp', rfl⟩ := (hran y').mp hy'
      rw [hHG hp, hHG hp'] at h
      rw [h]
  · rw [losSet_orderedPair] at ha
    obtain ⟨p, hp, rfl⟩ := (hran a).mp ha
    refine ⟨_, orderedPair_mem_vonNeumann_omega (lbl_mem_of_mem_otci_one hP hp) hX.right, ?_⟩
    rw [aoc_uc_eq_trvAZero_of_mem_otci_one hP hp, uc_eq_dctUZero_of_mem_otci_one hP hp]

/-- `P ⊗ Q ∈ aotci_1` for an array `P` with `(P ↾ 1)(0) ∈ otci_0` and `P(1) ∈ otci_1` -/
theorem tensorProdAOneAZero_mem_aotci (hP0 : (P ↾ ((1 : ℕ) : M)) ﹫ ∅ ∈ otci (∅ : M))
    (hP1 : P ﹫ ((1 : ℕ) : M) ∈ otci ((1 : ℕ) : M)) (Q : M) :
    tensorProdAOneAZero P Q ∈ aotci ((1 : ℕ) : M) := by
  have hA := (tensorProdAZeroAZero_mem hP0 Q).left
  obtain ⟨hAf, hAdom, -⟩ := mem_aotci_iff.mp hA
  have hlast : tensorProdAOneAZero P Q ﹫ ((1 : ℕ) : M) =
      tensorProdOneAZero (P ﹫ ((1 : ℕ) : M)) Q := by
    have h := cc_val_self hAf (tensorProdOneAZero (P ﹫ ((1 : ℕ) : M)) Q)
    rwa [hAdom] at h
  rw [mem_aotci_iff]
  refine ⟨hAf.cc _, by rw [tensorProdAOneAZero, dom_cc, hAdom]; rfl, fun i hi ↦ ?_, ?_⟩
  · rw [otciL_ciRec_restrict hi, tensorProdAOneAZero, cc_val_of_mem hAf _ (by rw [hAdom]; exact hi)]
    have hi0 : i = ∅ := by
      rcases mem_or_eq_of_mem_succ hi with h | h
      · change i ∈ (∅ : M) at h
        simp at h
      · exact h
    subst hi0
    exact val_mem_otci_of_mem_aotci hA (mem_succ_self ∅)
  · rw [hlast]
    exact tensorProdOneAZero_mem_otci hP1 Q

end Membership

end FirstOrder.Language.MemStructure
