/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.Basic
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
  node `(U, l)` is relabeled to `(U, (l, U_aoc ⊗ Q))`.
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

/-- The relabeling `(U, l) ↦ (U, (l, U_aoc ⊗ Q))` of the nodes of `P` -/
noncomputable def tensorProdOneAZeroRelabel (P Q : M) : M :=
  (fun p ↦ !(uc p, !(lbl p, tensorProdAZeroAZero (aoc (uc p)) Q))) ↾₀ ndOf P

/-- `P ⊗ Q` for `P ∈ otci_1` and `Q ∈ aotci_0`: the copy of `P` in which every node `p` is
relabeled to `(p_uc, (p_lbl, W ⊗ Q))`, where `W = (p_uc)_aoc ∈ aotci_0` -/
noncomputable def tensorProdOneAZero (P Q : M) : M := mapOf P (tensorProdOneAZeroRelabel P Q)

/-- `P ⊗ Q` for `P ∈ aotci_1` and `Q ∈ aotci_0`: the array in `aotci_1` with `aotci_0` part
`P ↾ 1 ⊗ Q` and `otci_1` part `P(1) ⊗ Q` -/
noncomputable def tensorProdAOneAZero (P Q : M) : M :=
  cc (tensorProdAZeroAZero (P ↾ ((1 : ℕ) : M)) Q) (tensorProdOneAZero (P ﹫ ((1 : ℕ) : M)) Q)

end FirstOrder.Language.MemStructure
