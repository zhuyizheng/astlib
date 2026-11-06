/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Order.BrouwerKleene
import Astlib.Combinatorics.ClassificationIdentifier.Embedding
import Astlib.Combinatorics.ClassificationIdentifier.LevelOne
/-!
# Classification identifiers of level two

`tensorProdTwoAOne P Q` for `P ∈ otci_2` and `Q ∈ aotci_1` is the tree in `otci_1` whose nodes
`(dctUZero, (p, f))` are all roots, where `p` is a non-root node of `P` and `f` is an embedding of
`W = (p_uc)_aoc` into `Q ⊗ Z`. The node `(p, f)` has the sequence
`((f(w_0), p_1), …, (f(w_{d-1}), p_d))`, where `d` is the depth of `p`, `w_i` is the node of the
`i`-th entry of the signature of `p_uc` and `p_k` is the ancestor of `p` of depth `k`. The nodes are
ordered by the Brouwer–Kleene order of their sequences, the coordinates being compared
lexicographically by the order of the roots of `(Q ⊗ Z)(1)` and the sibling order of `P`; this is
the Brouwer–Kleene order of `(f(w_0), p_1, f(w_1), p_2, …)`.

`tensorProdATwoAOne P Q` for `P ∈ aotci_2` and `Q ∈ aotci_1` is the array in `aotci_1` obtained
from `B = (P ↾ 2) ⊗ (Q ↾ 1) ∈ aotci_1` by attaching the roots of `P(2) ⊗ Q` to the right of the
roots of `B(1)` (`losConcat`), in a single linearly ordered set with key `Z`.

Main results: `tensorProdTwoAOne_mem_otci` (`P ⊗ Q ∈ otci_1` for `P ∈ otci_2`, `Q ∈ aotci_1`) and
`tensorProdATwoAOne_mem_aotci` (`P ⊗ Q ∈ aotci_1` for `P ∈ aotci_2`, `Q ∈ aotci_1`). The proof
uses:

* an extension `(U, q) ∈ ext_n` adds one entry to the signature (`exists_sig_eq_cc_of_mem_ciExt`),
  and at level `1` the array of `q` is determined by `U` (`aoc_eq_of_mem_ciExt_one`); hence in a
  tree of `otci_2` the signature of a node has the length of its depth (`dom_sig_uc_eq_depOf`) and
  the children of a node have the same key (`aoc_uc_eq_of_mem_chdOf`);
* the nodes of the level-`1` tree of `U ∈ stduoci_1` are the nodes of its signature
  (`exists_sigdcn_eq`), so an embedding is determined by its values there
  (`eq_of_mem_aotciEmbSet_one`), and the sequences determine the labels
  (`eq_of_tensorProdTwoAOneSeq_eq`);
* the first differing coordinates of two sequences are comparable (`tensorProdTwoAOneSeq_cmp`), so
  the Brouwer–Kleene order of the sequences is a strict linear order.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M]

/-- The array `Q ⊗ Z` in `aotci_1`, the target of the embeddings labeling `P ⊗ Q` -/
noncomputable def tensorProdTwoAOneTgt (Q : M) : M := tensorProdAOneAZero Q trvAZero

/-- The labels `(p, f)` of the nodes of `P ⊗ Q`: `p` a non-root node of `P` and `f` an embedding
of `(p_uc)_aoc` into `Q ⊗ Z`. The root is excluded: its label would have the empty sequence, the
maximum of the Brouwer–Kleene order, so that `A ⊗ W ≇ W` for the trivial `A ∈ aotci_2` -/
noncomputable def tensorProdTwoAOneLbls (P Q : M) : M :=
  ⋃₀ ran ((fun p ↦ ({p} : M) ×ˢ
    aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) (tensorProdTwoAOneTgt Q)) ↾₀ (ndOf P \ rtOf P))

/-- The sequence `((f(w_0), p_1), …, (f(w_{d-1}), p_d))` of the label `x = (p, f)` -/
noncomputable def tensorProdTwoAOneSeq (P x : M) : M :=
  (fun i ↦ !((right x ﹫ siglvl (uc (left x)) i) ﹫ sigdcn (uc (left x)) i,
    ancOf P (left x) (succ i))) ↾₀ depOf P (left x)

/-- The order of the coordinates `(f(w_i), p_{i+1})` of the sequences: lexicographic, by the order
of the roots of `(Q ⊗ Z)(1)` and then by the sibling order of `P` -/
noncomputable def tensorProdTwoAOneCoordOdr (P Q : M) : M :=
  lexProd (losOdr (rtlosOf (tensorProdTwoAOneTgt Q ﹫ ((1 : ℕ) : M)) ﹫ trvAZero))
    (ndOf (tensorProdTwoAOneTgt Q ﹫ ((1 : ℕ) : M))) (sblOdrOf P) (ndOf P)

/-- The labels `x` and `y` of `P ⊗ Q` are in the Brouwer–Kleene order of their sequences -/
def TensorProdTwoAOneLt (P Q x y : M) : Prop :=
  BKLt (tensorProdTwoAOneCoordOdr P Q) (tensorProdTwoAOneSeq P x) (tensorProdTwoAOneSeq P y)

/-- The nodes `(dctUZero, x)` of `P ⊗ Q`, for the labels `x` -/
noncomputable def tensorProdTwoAOneNds (P Q : M) : M :=
  ran ((fun x ↦ !(dctUZero, x)) ↾₀ tensorProdTwoAOneLbls P Q)

/-- The order of the nodes of `P ⊗ Q`: the Brouwer–Kleene order of the sequences of their
labels -/
noncomputable def tensorProdTwoAOneOdr (P Q : M) : M :=
  (tensorProdTwoAOneNds P Q ×ˢ tensorProdTwoAOneNds P Q) ∩₀
    fun z ↦ TensorProdTwoAOneLt P Q (lbl (left z)) (lbl (right z))

/-- `P ⊗ Q` for `P ∈ otci_2` and `Q ∈ aotci_1`: the tree in `otci_1` whose nodes
`(dctUZero, (p, f))` are all roots, forming a single linearly ordered set with key `Z` -/
noncomputable def tensorProdTwoAOne (P Q : M) : M :=
  rtLosSLOT trvAZero !(tensorProdTwoAOneNds P Q, tensorProdTwoAOneOdr P Q)

/-- The array `(P ↾ 2) ⊗ (Q ↾ 1) ∈ aotci_1` from the `aotci_1` part of `P` and the `aotci_0`
part of `Q` -/
noncomputable def tensorProdATwoAOneBase (P Q : M) : M :=
  tensorProdAOneAZero (P ↾ 2) (Q ↾ ((1 : ℕ) : M))

/-- `P ⊗ Q` for `P ∈ aotci_2` and `Q ∈ aotci_1`: the array in `aotci_1` obtained from
`B = (P ↾ 2) ⊗ (Q ↾ 1)` by attaching the roots of `P(2) ⊗ Q ∈ otci_1` to the right of the roots
of `B(1)`, in a single linearly ordered set with key `Z` -/
noncomputable def tensorProdATwoAOne (P Q : M) : M :=
  cc (tensorProdATwoAOneBase P Q ↾ ((1 : ℕ) : M))
    (rtLosSLOT trvAZero (losConcat
      (rtlosOf (tensorProdATwoAOneBase P Q ﹫ ((1 : ℕ) : M)) ﹫ trvAZero)
      (rtlosOf (tensorProdTwoAOne (P ﹫ 2) Q) ﹫ trvAZero)))

section Ext

/-! ### Extensions of level one -/

variable {A b n q q' U Y : M}

/-- An extension adds one entry to the signature -/
theorem exists_sig_eq_cc_of_mem_ciExt (hn : n ∈ (ω : M)) (h : !(U, q) ∈ ciExt n) :
    ∃ e, sig q = cc (sig U) e := by
  obtain ⟨hUs, -, hUd, -⟩ := mem_ciExt_props h
  obtain ⟨P', -, Q', -, hPQ, hext⟩ := mem_ciExt_iff.mp h
  rw [orderedPair_eq_orderedPair_iff] at hPQ
  obtain ⟨rfl, rfl⟩ := hPQ
  obtain ⟨-, -, hrt, hlfrt, hlfsbl, hdn⟩ := hext
  by_cases hs : sig U = ∅ ∧ IsOdd n
  · obtain ⟨-, R, -, A, -, -, hsig⟩ := hrt hs
    exact ⟨_, by rw [hsig, hs.left]⟩
  have hUu := (mem_stduoci_iff.mp hUs).left
  rw [mem_uoci_iff_of_mem_omega hn] at hUu
  obtain ⟨-, hdom, -, -, -, -, hdom3, hucf⟩ := hUu
  have hne3 : dom U ≠ ((3 : ℕ) : M) := fun h3 ↦
    (hdom3.mp h3).elim hs fun hct ↦ ct_ne_dct (hct.symm.trans hUd)
  have hmem (k : ℕ) (hk : k < 5) : ((k : ℕ) : M) ∈ dom U := by
    rcases hdom with h | h | h
    · exact (hne3 h).elim
    · rw [h]
      exact natCast_mem_natCast_of_lt hk
    · rw [h]
      exact natCast_mem_natCast_of_lt (by omega)
  obtain ⟨-, -, -, -, hdr, -⟩ := hucf (hmem 3 (by omega))
  rcases hdr with hlf | hdn'
  · by_cases hr : IsEven (ucflvl U) ∧ ucfdcn U ∈ rtOf (aoc U ﹫ ucflvl U)
    · obtain ⟨-, -, R, -, A, -, -, hsig⟩ := hlfrt ⟨hmem 4 (by omega), hlf, hr⟩
      exact ⟨_, hsig⟩
    · obtain ⟨-, -, A, -, hsig⟩ := hlfsbl ⟨hmem 4 (by omega), hlf, hr⟩
      exact ⟨_, hsig⟩
  · obtain ⟨-, -, R, -, R', A, -, -, -, -, hsig⟩ := hdn hdn'
    exact ⟨_, hsig⟩

/-- Assigning children to a childless node `b` of a tree in `otci_1` assigns no children -/
theorem asnchdOf_eq_of_mem_otci_one (hX : asnchdOf Y b A ∈ otci ((1 : ℕ) : M))
    (hb : b ∈ ndOf Y) (hbY : chdOf Y b = ∅) : asnchdOf Y b A = Y := by
  have hXs : (SLOTreeStructure.ofM (asnchdOf Y b A)).IsSLOTreeStructure := isSLOT_of_mem_otci hX
  have hA : chdOf (asnchdOf Y b A) b = A :=
    SLOTreeStructure.chd_asnchd_val_self hXs.isTreeStructure.isFunction_chd hbY
  have hA0 := chdOf_eq_empty_of_mem_otci_one hX
    (SLOTreeStructure.nd_subset_nd_asnchd _ _ _ hb)
  rw [hA] at hA0
  change ((SLOTreeStructure.ofM Y).asnchd b A).toM = Y
  rw [SLOTreeStructure.asnchd, if_pos hA0]
  rfl

/-- The level-`1` tree of an extension `q` of `U ∈ stduoci_1` is determined by `U`: a new root
`(dctUZero, ∅)` if `U_sig = ∅`, and otherwise a new left sibling of `U_ucfdcn` -/
theorem aoc_val_of_mem_ciExt_one (h : !(U, q) ∈ ciExt ((1 : ℕ) : M)) :
    aoc q ﹫ ∅ = aoc U ﹫ ∅ ∧ aoc q ﹫ ((1 : ℕ) : M) =
      if sig U = ∅ then irmrtOf (aoc U ﹫ ((1 : ℕ) : M)) !(dctUZero, ∅)
      else ilfsblOf (aoc U ﹫ ((1 : ℕ) : M)) (ucfdcn U) !(uc (ucfdcn U), dom (sig U)) := by
  have h1ω : ((1 : ℕ) : M) ∈ (ω : M) := natCast_mem_omega 1
  obtain ⟨hUs, hqs, hUd, -⟩ := mem_ciExt_props h
  obtain ⟨P', -, Q', -, hPQ, hext⟩ := mem_ciExt_iff.mp h
  rw [orderedPair_eq_orderedPair_iff] at hPQ
  obtain ⟨rfl, rfl⟩ := hPQ
  obtain ⟨-, -, hrt, hlfrt, hlfsbl, hdn⟩ := hext
  -- the arrays
  have harr (V : M) (hV : V ∈ stduoci ((1 : ℕ) : M)) : aoc V ∈ aotci ((1 : ℕ) : M) := by
    have hVu := (mem_stduoci_iff.mp hV).left
    rw [mem_uoci_iff_of_mem_omega h1ω] at hVu
    exact (mem_finaotci_iff.mp hVu.right.right.left).left
  have hUA := harr U hUs
  have hqA := harr q hqs
  have hU1 := val_mem_otci_of_mem_aotci hUA (mem_succ_self _)
  have hq1 := val_mem_otci_of_mem_aotci hqA (mem_succ_self _)
  have hUS : (SLOTreeStructure.ofM (aoc U ﹫ ((1 : ℕ) : M))).IsSLOTreeStructure :=
    isSLOT_of_mem_otci hU1
  have h01 : (∅ : M) ∈ ((1 : ℕ) : M) := empty_mem_natCast_one
  have hU0dom : (∅ : M) ∈ dom (aoc U) := by
    rw [(mem_aotci_iff.mp hUA).right.left]
    exact mem_succ_of_mem h01
  have hq0dom : (∅ : M) ∈ dom (aoc q) := by
    rw [(mem_aotci_iff.mp hqA).right.left]
    exact mem_succ_of_mem h01
  have hl1 (l : M) (hl : l ∈ succ ((1 : ℕ) : M)) (h0 : ∅ ∈ l) : l = ((1 : ℕ) : M) := by
    rcases mem_or_eq_of_mem_succ hl with h | h
    · rw [natCast_succ, natCast_zero, mem_succ_iff] at h
      rcases h with h | h
      · rw [h] at h0
        simp at h0
      · simp at h
    · exact h
  by_cases hs : sig U = ∅
  · rw [if_pos hs]
    obtain ⟨hres, R, -, A, -, hq, -⟩ := hrt ⟨hs, isOdd_one⟩
    refine ⟨?_, ?_⟩
    · rw [← val_restrict _ (mem_aotci_iff.mp hqA).left h01 hq0dom, ← hres,
        val_restrict _ (mem_aotci_iff.mp hUA).left h01 hU0dom]
    have hbn : !(R, ∅) ∈ ndOf (irmrtOf (aoc U ﹫ ((1 : ℕ) : M)) !(R, ∅)) := by
      change !(R, ∅) ∈ ((SLOTreeStructure.ofM _).irmrt _).nd
      rw [SLOTreeStructure.nd_irmrt]
      exact mem_insert _ _
    have hbc : chdOf (irmrtOf (aoc U ﹫ ((1 : ℕ) : M)) !(R, ∅)) !(R, ∅) = ∅ := by
      change ((SLOTreeStructure.ofM _).irmrt _).ts.chd ﹫ _ = ∅
      rw [SLOTreeStructure.ts_irmrt]
      exact hUS.isTreeStructure.chd_irt_val_self
    rw [hq] at hq1 ⊢
    have heq := asnchdOf_eq_of_mem_otci_one hq1 hbn hbc
    rw [heq] at hq1 ⊢
    have hR := uc_eq_dctUZero_of_mem_otci_one hq1 hbn
    rw [uc_orderedPair] at hR
    rw [hR]
  rw [if_neg hs]
  have hs' : ¬(sig U = ∅ ∧ IsOdd ((1 : ℕ) : M)) := fun h ↦ hs h.left
  have hUu := (mem_stduoci_iff.mp hUs).left
  rw [mem_uoci_iff_of_mem_omega h1ω] at hUu
  obtain ⟨-, hdom, -, -, -, -, hdom3, hucf⟩ := hUu
  have hne3 : dom U ≠ ((3 : ℕ) : M) := fun h3 ↦
    (hdom3.mp h3).elim hs' fun hct ↦ ct_ne_dct (hct.symm.trans hUd)
  have hmem (k : ℕ) (hk : k < 5) : ((k : ℕ) : M) ∈ dom U := by
    rcases hdom with h | h | h
    · exact (hne3 h).elim
    · rw [h]
      exact natCast_mem_natCast_of_lt hk
    · rw [h]
      exact natCast_mem_natCast_of_lt (by omega)
  obtain ⟨-, hlvl, hd, -, hdr, hdr5, h6⟩ := hucf (hmem 3 (by omega))
  rcases hdr with hlf | hdn'
  swap
  · -- `ucfdr = dn` is impossible at level `1`
    exfalso
    have hdom6 : dom U = ((6 : ℕ) : M) := by
      rcases hdom with h | h | h
      · exact (hne3 h).elim
      · have := (hdr5.mp h).symm.trans hdn'
        rw [lf, dn, natCast_inj] at this
        omega
      · exact h
    obtain ⟨h0, hex⟩ := h6 hdom6
    rw [hl1 _ hlvl h0, sUnion_natCast_one, extL_ciRec_restrict empty_mem_natCast_one,
      ciExt_empty] at hex
    simp at hex
  by_cases hr : IsEven (ucflvl U) ∧ ucfdcn U ∈ rtOf (aoc U ﹫ ucflvl U)
  · exfalso
    have h1 := (hlfrt ⟨hmem 4 (by omega), hlf, hr⟩).left
    rcases mem_or_eq_of_mem_succ hlvl with h | h
    · rw [natCast_succ, natCast_zero, mem_succ_iff] at h
      rcases h with h | h
      · rw [h] at h1
        simp at h1
      · simp at h
    · rw [h] at h1
      exact notMem_self _ h1
  obtain ⟨h0, hothers, A, hq, -⟩ := hlfsbl ⟨hmem 4 (by omega), hlf, hr⟩
  have hl := hl1 _ hlvl h0
  rw [hl] at hothers hq hd
  refine ⟨(hothers ∅ (mem_succ_of_mem h01) (by rw [ne_comm]; exact natCast_one_ne_empty)).symm, ?_⟩
  -- the new left sibling of the root `ucfdcn U` has no children
  have hdr : ucfdcn U ∈ rtOf (aoc U ﹫ ((1 : ℕ) : M)) := by
    rw [← ndOf_eq_rtOf_of_mem_otci_one hU1]
    exact hd
  set b' := !(uc (ucfdcn U), dom (sig U))
  have hbn : b' ∈ ndOf (ilfsblOf (aoc U ﹫ ((1 : ℕ) : M)) (ucfdcn U) b') := by
    change b' ∈ ((SLOTreeStructure.ofM _).ilfsbl _ _).ts.nd
    rw [SLOTreeStructure.ilfsbl, SLOTreeStructure.ts_mk, TreeStructure.isbl_of_mem_rt hdr,
      TreeStructure.nd_irt]
    exact mem_insert _ _
  have hbc : chdOf (ilfsblOf (aoc U ﹫ ((1 : ℕ) : M)) (ucfdcn U) b') b' = ∅ := by
    change ((SLOTreeStructure.ofM _).ilfsbl _ _).ts.chd ﹫ _ = ∅
    rw [SLOTreeStructure.ilfsbl, SLOTreeStructure.ts_mk, TreeStructure.isbl_of_mem_rt hdr]
    exact hUS.isTreeStructure.chd_irt_val_self
  rw [hq] at hq1 ⊢
  exact asnchdOf_eq_of_mem_otci_one hq1 hbn hbc

/-- The extensions of an element of `stduoci_1` have the same array -/
theorem aoc_eq_of_mem_ciExt_one (h : !(U, q) ∈ ciExt ((1 : ℕ) : M))
    (h' : !(U, q') ∈ ciExt ((1 : ℕ) : M)) : aoc q = aoc q' := by
  have h1ω : ((1 : ℕ) : M) ∈ (ω : M) := natCast_mem_omega 1
  have harr (V : M) (hV : V ∈ stduoci ((1 : ℕ) : M)) : aoc V ∈ aotci ((1 : ℕ) : M) := by
    have hVu := (mem_stduoci_iff.mp hV).left
    rw [mem_uoci_iff_of_mem_omega h1ω] at hVu
    exact (mem_finaotci_iff.mp hVu.right.right.left).left
  obtain ⟨hf, hdom, -⟩ := mem_aotci_iff.mp (harr q (mem_ciExt_props h).right.left)
  obtain ⟨hf', hdom', -⟩ := mem_aotci_iff.mp (harr q' (mem_ciExt_props h').right.left)
  obtain ⟨h0, h1⟩ := aoc_val_of_mem_ciExt_one h
  obtain ⟨h0', h1'⟩ := aoc_val_of_mem_ciExt_one h'
  refine hf.ext hf' (hdom.trans hdom'.symm) fun i hi ↦ ?_
  rw [hdom] at hi
  rcases mem_or_eq_of_mem_succ hi with hi | rfl
  · rw [natCast_succ, natCast_zero, mem_succ_iff] at hi
    rcases hi with rfl | hi
    · rw [h0, h0']
    · simp at hi
  · rw [h1, h1']

end Ext

section OtciTwo

/-! ### The trees in `otci_2` and the arrays of `stduoci_1` -/

variable {b c c' f f' i p w P T U : M}

theorem sUnion_natCast_two : ⋃₀ ((2 : ℕ) : M) = ((1 : ℕ) : M) := by
  rw [natCast_succ, sUnion_succ (isNat_natCast 1).ordinal.transitive]

theorem natCast_one_mem_two : ((1 : ℕ) : M) ∈ ((2 : ℕ) : M) := natCast_mem_natCast_of_lt (by omega)

theorem natCast_two_ne_empty : ((2 : ℕ) : M) ≠ ∅ := by
  rw [← natCast_zero, Ne, natCast_inj]
  omega

theorem isEven_two : IsEven ((2 : ℕ) : M) :=
  (isEven_succ_iff (natCast_mem_omega 1)).mpr isOdd_one

/-- The nodes of a semi-linearly ordered tree structure are not `∅` -/
theorem empty_not_mem_ndOf (hT : IsSLOT T) : (∅ : M) ∉ ndOf T := fun h ↦ by
  obtain ⟨x, y, hxy⟩ := (show (SLOTreeStructure.ofM T).IsSLOTreeStructure from hT).isOrderedPair h
  exact orderedPair_ne_empty x y hxy.symm

/-- The conditions of `otci_2` with the levels below `2` looked up -/
theorem otciCond_two (hP : P ∈ otci ((2 : ℕ) : M)) :
    IsSLOT P ∧ (∀ p ∈ ndOf P, uc p ∈ stduoci ((1 : ℕ) : M) ∧ lbl p ∈ 𝕍 (ω : M)) ∧
    (∀ r ∈ rtOf P, uc r ∈ trvuoci ((1 : ℕ) : M)) ∧ (∃ r, rtOf P = {r}) ∧
    ∀ p ∈ ndOf P,
      (∀ D, (∃ q ∈ chdOf P p, aoc (uc q) = D) ↔
        ∃ q, !(uc p, q) ∈ ciExt ((1 : ℕ) : M) ∧ aoc q = D) ∧
      (∀ q, !(uc p, q) ∈ ciExt ((1 : ℕ) : M) → ∀ r ∈ losSet (chdlosOf P p ﹫ aoc q),
        sig (uc r) = sig q ∧ (IsLeastLos (chdlosOf P p ﹫ aoc q) r ↔ ctp (uc r) = ct)) ∧
      ∀ q, !(uc p, q) ∈ ciExt ((1 : ℕ) : M) →
        ∃ r ∈ losSet (chdlosOf P p ﹫ aoc q), IsLeastLos (chdlosOf P p ﹫ aoc q) r := by
  rw [mem_otci_iff_of_ne_empty natCast_two_ne_empty] at hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  rw [sUnion_natCast_two, stduociL_ciRec_restrict natCast_one_mem_two] at h2
  rw [sUnion_natCast_two, trvuociL_ciRec_restrict natCast_one_mem_two] at h3
  rw [sUnion_natCast_two, extL_ciRec_restrict natCast_one_mem_two] at h5
  exact ⟨h1, h2, h3, h4 isEven_two, h5⟩

/-- In a tree of `otci_2`, the signature of a node has the length of its depth -/
theorem dom_sig_uc_eq_depOf (hP : P ∈ otci ((2 : ℕ) : M)) (hp : p ∈ ndOf P) :
    dom (sig (uc p)) = depOf P p := by
  obtain ⟨hPs, -, hroot, -, hchd⟩ := otciCond_two hP
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hPs
  have hT := hS.isTreeStructure
  refine omega_induction (A := fun k ↦ ∀ p ∈ ndOf P, depOf P p = k → dom (sig (uc p)) = k)
    (fun p hp hd ↦ ?_) (fun k hk ih p hp hd ↦ ?_) (hT.dep_mem_omega hp) p hp rfl
  · have hr : p ∈ rtOf P := TreeStructure.mem_rt_iff.mpr ⟨hp, hd⟩
    rw [sig_eq_empty_of_mem_trvuoci (natCast_mem_omega 1) (hroot p hr), dom_empty]
  have hpr : p ∈ (SLOTreeStructure.ofM P).ts.nd \ (SLOTreeStructure.ofM P).ts.rt := by
    rw [mem_sdiff_iff, TreeStructure.mem_rt_iff]
    exact ⟨hp, fun h ↦ succ_ne_empty _ (hd.symm.trans h.right)⟩
  have hb : prtOf P p ∈ ndOf P := hT.prt_val_mem_nd hpr
  have hpc : p ∈ chdOf P (prtOf P p) := hT.mem_chd_prt_val hpr
  have hdb : depOf P (prtOf P p) = k := by
    have h : depOf P p = succ (depOf P (prtOf P p)) := hT.dep_of_mem_chd _ hb _ hpc
    rw [hd] at h
    exact (TreeStructure.eq_of_succ_eq_succ (ordinal_of_mem ordinal_omega hk) h).symm
  obtain ⟨q, hq, hqk⟩ := ((hchd _ hb).left (aoc (uc p))).mp ⟨p, hpc, rfl⟩
  have hmem : p ∈ losSet (chdlosOf P (prtOf P p) ﹫ aoc q) := by
    rw [hqk]
    exact (mem_losSet_chdlosOf_iff hPs hb hpc p).mpr ⟨hpc, rfl⟩
  have hsig := ((hchd _ hb).right.left q hq p hmem).left
  obtain ⟨e, he⟩ := exists_sig_eq_cc_of_mem_ciExt (natCast_mem_omega 1) hq
  rw [hsig, he, dom_cc, ih _ hb hdb]

/-- In a tree of `otci_2`, the children of a node have the same key -/
theorem aoc_uc_eq_of_mem_chdOf (hP : P ∈ otci ((2 : ℕ) : M)) (hb : b ∈ ndOf P)
    (hc : c ∈ chdOf P b) (hc' : c' ∈ chdOf P b) : aoc (uc c) = aoc (uc c') := by
  obtain ⟨-, -, -, -, hchd⟩ := otciCond_two hP
  obtain ⟨q, hq, hqc⟩ := ((hchd _ hb).left (aoc (uc c))).mp ⟨c, hc, rfl⟩
  obtain ⟨q', hq', hqc'⟩ := ((hchd _ hb).left (aoc (uc c'))).mp ⟨c', hc', rfl⟩
  rw [← hqc, ← hqc', aoc_eq_of_mem_ciExt_one hq hq']

/-- The trees in `otci_0` have a single node -/
theorem exists_ndOf_eq_singleton_of_mem_otci_empty (hT : T ∈ otci (∅ : M)) :
    ∃ b, ndOf T = {b} := by
  rw [mem_otci_empty_iff] at hT
  obtain ⟨l, -, rfl⟩ := hT
  exact ⟨_, ndOf_irmrtOf_emptySLOT _⟩

theorem aoc_mem_aotci_of_mem_stduoci_one (hU : U ∈ stduoci ((1 : ℕ) : M)) :
    aoc U ∈ aotci ((1 : ℕ) : M) := by
  have hUu := (mem_stduoci_iff.mp hU).left
  rw [mem_uoci_iff_of_mem_omega (natCast_mem_omega 1)] at hUu
  exact (mem_finaotci_iff.mp hUu.right.right.left).left

/-- The signature of an element of `stduoci_1` lies at level `1` -/
theorem siglvl_eq_one (hU : U ∈ stduoci ((1 : ℕ) : M)) (hi : i ∈ dom (sig U)) :
    siglvl U i = ((1 : ℕ) : M) ∧ sigdcn U i ∈ ndOf (aoc U ﹫ ((1 : ℕ) : M)) := by
  have hA := aoc_mem_aotci_of_mem_stduoci_one hU
  have hUu := (mem_stduoci_iff.mp hU).left
  rw [mem_uoci_iff_of_mem_omega (natCast_mem_omega 1)] at hUu
  have hsc := hUu.right.right.right.left.right.right.right i hi
  have hnd := mem_ndOf_of_sigCond (natCast_mem_omega 1) hA hsc
  obtain ⟨-, hlvl, hev, -, -⟩ := hsc
  rcases mem_or_eq_of_mem_succ hlvl with h | h
  · exfalso
    have h0 : siglvl U i = ∅ := by
      rw [natCast_succ, natCast_zero, mem_succ_iff] at h
      rcases h with h | h
      · exact h
      · simp at h
    have hW := val_mem_otci_of_mem_aotci hA (mem_succ_of_mem empty_mem_natCast_one)
    rw [mem_otci_empty_iff] at hW
    obtain ⟨l, -, hl⟩ := hW
    have hW' : aoc U ﹫ siglvl U i = irmrtOf emptySLOT !(otci0Uc, l) := by
      rw [h0]
      exact hl
    have hrt : !(otci0Uc, l) ∈ rtOf (aoc U ﹫ siglvl U i) := by
      rw [hW', rtOf_irmrtOf_emptySLOT]
      exact mem_singleton _
    rcases hev (by rw [h0]; exact isEven_empty) _ hrt with h' | ⟨j, -, -, h'⟩ <;>
      rw [hW', chdOf_irmrtOf_emptySLOT] at h' <;> simp at h'
  · exact ⟨h, h ▸ hnd⟩

/-- The nodes of the level-`1` tree of an element of `stduoci_1` are in its signature -/
theorem exists_sigdcn_eq (hU : U ∈ stduoci ((1 : ℕ) : M)) (hw : w ∈ ndOf (aoc U ﹫ ((1 : ℕ) : M))) :
    ∃ i ∈ dom (sig U), siglvl U i = ((1 : ℕ) : M) ∧ sigdcn U i = w := by
  have hA := aoc_mem_aotci_of_mem_stduoci_one hU
  have hW1 := val_mem_otci_of_mem_aotci hA (mem_succ_self _)
  have hct : ctp (uc w) = dct := by
    rw [uc_eq_dctUZero_of_mem_otci_one hW1 hw, dctUZero_eq_lfTrvUoci, ctp_lfTrvUoci]
  have h2 := ((mem_stduoci_iff.mp hU).right _ (mem_succ_self _) w hw).right.left
    ⟨hct, fun h ↦ isOdd_one.not_isEven h.left⟩
  by_cases hl : lbl w ∈ dom (sig U)
  · exact ⟨lbl w, hl, by rw [siglvl, ← h2, lvl_orderedPair],
      by rw [sigdcn, ← h2, dcn_orderedPair]⟩
  · rw [val_eq_empty_of_not_mem_dom hl] at h2
    exact (orderedPair_ne_empty _ _ h2).elim

end OtciTwo

section Labels

/-! ### The labels and their sequences -/

variable {f f' n p x y P Q T U W : M}

theorem mem_aotciEmbSet_iff : f ∈ aotciEmbSet n W T ↔
    f ∈ 𝒫 (succ n ×ˢ 𝒫 (ndUnion (ran W) ×ˢ ndUnion (ran T))) ∧ IsAotciEmbedding n W T f := by
  rw [aotciEmbSet, mem_comprehension_iff]

omit [ModelsZF M] in
theorem mem_powerset_sprod_powerset_iff [ModelsZF M] {A B : M} :
    f ∈ 𝒫 (A ×ˢ 𝒫 B) ↔ ∀ y ∈ f, IsOrderedPair y ∧ left y ∈ A ∧ right y ⊆ B := by
  rw [mem_powerset_iff]
  constructor
  · intro h y hy
    have hy' := h hy
    rw [mem_sprod_iff] at hy'
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    rw [left_orderedPair, right_orderedPair]
    rw [mem_powerset_iff] at hb
    exact ⟨⟨a, b, rfl⟩, ha, hb⟩
  · intro h y hy
    obtain ⟨⟨a, b, rfl⟩, ha, hb⟩ := h y hy
    rw [left_orderedPair] at ha
    rw [right_orderedPair] at hb
    rw [mem_sprod_iff]
    exact ⟨a, ha, b, (mem_powerset_iff b).mpr hb, rfl⟩

instance : Multiclass.Definable
    (fun xs : Fin 4 → M ↦ xs 0 ⊆ xs 1 ×ˢ 𝒫 (xs 2 ×ˢ xs 3)) Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ xs 0 ⊆ xs 1 ×ˢ 𝒫 (xs 2 ×ˢ xs 3)) = fun xs ↦
      ∀ y ∈ xs 0, IsOrderedPair y ∧ left y ∈ xs 1 ∧ right y ⊆ xs 2 ×ˢ xs 3 := by
    funext xs
    rw [← mem_powerset_sprod_powerset_iff, mem_powerset_iff]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ xs i ⊆ xs j ×ˢ 𝒫 (xs k ×ˢ xs l)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ xs i ⊆ xs j ×ˢ 𝒫 (xs k ×ˢ xs l)) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ ys 0 ⊆ ys 1 ×ˢ 𝒫 (ys 2 ×ˢ ys 3)) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable
    (fun xs : Fin 4 → M ↦ xs 3 ∈ aotciEmbSet (xs 0) (xs 1) (xs 2)) Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ xs 3 ∈ aotciEmbSet (xs 0) (xs 1) (xs 2)) = fun xs ↦
      (∃ n A B, n = succ (xs 0) ∧ A = ndUnion (ran (xs 1)) ∧ B = ndUnion (ran (xs 2)) ∧
        xs 3 ⊆ n ×ˢ 𝒫 (A ×ˢ B)) ∧
      IsAotciEmbedding (xs 0) (xs 1) (xs 2) (xs 3) := by
    funext xs
    rw [mem_aotciEmbSet_iff, mem_powerset_iff]
    apply propext
    constructor
    · rintro ⟨hb, he⟩
      exact ⟨⟨_, _, _, rfl, rfl, rfl, hb⟩, he⟩
    · rintro ⟨⟨n, A, B, rfl, rfl, rfl, hb⟩, he⟩
      exact ⟨hb, he⟩
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ xs l ∈ aotciEmbSet (xs i) (xs j) (xs k)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ xs l ∈ aotciEmbSet (xs i) (xs j) (xs k)) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ ys 3 ∈ aotciEmbSet (ys 0) (ys 1) (ys 2)) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance (T : M) : ClassFunction.Definable
    (fun p ↦ ({p} : M) ×ˢ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) T) Set.univ :=
  .of_mem_iff (R := fun p z ↦ ∃ n W T', n = ((1 : ℕ) : M) ∧ W = aoc (uc p) ∧ T' = T ∧
    ∃ f, z = !(p, f) ∧ f ∈ aotciEmbSet n W T') fun p z ↦ by
    simp only [mem_sprod_iff, mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl, f, hf, rfl⟩
      exact ⟨_, _, _, rfl, rfl, rfl, f, rfl, hf⟩
    · rintro ⟨n, W, T', rfl, rfl, rfl, f, rfl, hf⟩
      exact ⟨p, rfl, f, hf, rfl⟩

theorem mem_ancOf_iff (P p k z : M) :
    z ∈ ancOf P p k ↔ ∃ b ∈ ndOf P, (depOf P b = k ∧ IsAncOf P p b) ∧ z ∈ b := by
  rw [ancOf, TreeStructure.anc, mem_sUnion_iff]
  simp only [mem_comprehension_iff]
  constructor
  · rintro ⟨b, ⟨hb, h⟩, hz⟩
    exact ⟨b, hb, h, hz⟩
  · rintro ⟨b, hb, h, hz⟩
    exact ⟨b, ⟨hb, h⟩, hz⟩

instance : MulticlassFunction.Definable (fun ys : Fin 3 → M ↦ ancOf (ys 0) (ys 1) (ys 2))
    Set.univ := by
  have h : MulticlassFunction.toMulticlass (M := M) (n := 3)
      (fun ys ↦ ancOf (ys 0) (ys 1) (ys 2)) = fun xs : Fin 4 → M ↦
        ∀ z, z ∈ xs 3 ↔ ∃ b ∈ ndOf (xs 0),
          (depOf (xs 0) b = xs 2 ∧ IsAncOf (xs 0) (xs 1) b) ∧ z ∈ b := by
    funext xs
    change (ancOf (xs 0) (xs 1) (xs 2) = xs 3) = _
    apply propext
    constructor
    · intro h z
      rw [← h, mem_ancOf_iff]
    · intro h
      ext z
      rw [mem_ancOf_iff, h z]
  have : Multiclass.Definable (MulticlassFunction.toMulticlass (M := M) (n := 3)
      (fun ys ↦ ancOf (ys 0) (ys 1) (ys 2))) Set.univ := by
    rw [h]
    infer_instance
  infer_instance

instance {n : ℕ} (i j k l : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ ancOf (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ ancOf (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (MulticlassFunction.toMulticlass (M := M) (n := 3) fun ys ↦ ancOf (ys 0) (ys 1) (ys 2))
      ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap, MulticlassFunction.toMulticlass]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance (P p : M) : ClassFunction.Definable (fun i ↦ ancOf P p (succ i)) Set.univ :=
  .of_mem_iff (R := fun i z ↦ ∃ b ∈ ndOf P, (depOf P b = succ i ∧ IsAncOf P p b) ∧ z ∈ b)
    fun i z ↦ mem_ancOf_iff P p (succ i) z

/-- The labels of `P ⊗ Q` -/
theorem mem_tensorProdTwoAOneLbls_iff : x ∈ tensorProdTwoAOneLbls P Q ↔
    ∃ p ∈ ndOf P, p ∉ rtOf P ∧
      ∃ f ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) (tensorProdTwoAOneTgt Q), x = !(p, f) := by
  have hres : IsSetRestrictedTo
      (fun p ↦ ({p} : M) ×ˢ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) (tensorProdTwoAOneTgt Q))
      (ndOf P \ rtOf P) := isSetRestrictedTo_of_definable _
  rw [tensorProdTwoAOneLbls, mem_sUnion_iff]
  simp only [mem_ran_toSetRestrictedTo_iff hres]
  constructor
  · rintro ⟨y, ⟨p, hp, rfl⟩, hx⟩
    rw [mem_sdiff_iff] at hp
    rw [mem_sprod_iff] at hx
    obtain ⟨p', hp', f, hf, rfl⟩ := hx
    rw [mem_singleton_iff] at hp'
    subst hp'
    exact ⟨p', hp.left, hp.right, f, hf, rfl⟩
  · rintro ⟨p, hp, hpr, f, hf, rfl⟩
    refine ⟨_, ⟨p, by rw [mem_sdiff_iff]; exact ⟨hp, hpr⟩, rfl⟩, ?_⟩
    rw [mem_sprod_iff]
    exact ⟨p, mem_singleton p, f, hf, rfl⟩

/-- The coordinates of the sequences -/
instance (f U P p : M) : ClassFunction.Definable
    (fun i ↦ !((f ﹫ siglvl U i) ﹫ sigdcn U i, ancOf P p (succ i))) Set.univ := by
  infer_instance

instance (P : M) : Multiclass.Definable (fun xs : Fin 5 → M ↦
    !((xs 0 ﹫ siglvl (xs 1) (xs 3)) ﹫ sigdcn (xs 1) (xs 3), ancOf P (xs 2) (succ (xs 3))) = xs 4)
    Set.univ := by
  have h : (fun xs : Fin 5 → M ↦
      !((xs 0 ﹫ siglvl (xs 1) (xs 3)) ﹫ sigdcn (xs 1) (xs 3), ancOf P (xs 2) (succ (xs 3))) =
        xs 4) = fun xs ↦ ∃ Q k b, Q = P ∧ k = succ (xs 3) ∧ ancOf Q (xs 2) k = b ∧
        !((xs 0 ﹫ siglvl (xs 1) (xs 3)) ﹫ sigdcn (xs 1) (xs 3), b) = xs 4 := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, _, rfl, rfl, rfl, h⟩
    · rintro ⟨Q, k, b, rfl, rfl, rfl, h⟩
      exact h
  rw [h]
  infer_instance

instance {n : ℕ} (P : M) (i j k l m : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    !((xs i ﹫ siglvl (xs j) (xs l)) ﹫ sigdcn (xs j) (xs l), ancOf P (xs k) (succ (xs l))) = xs m)
    Set.univ := by
  have h : (fun xs : Fin n → M ↦
      !((xs i ﹫ siglvl (xs j) (xs l)) ﹫ sigdcn (xs j) (xs l), ancOf P (xs k) (succ (xs l))) =
        xs m) = Multiclass.remap (fun ys : Fin 5 → M ↦
      !((ys 0 ﹫ siglvl (ys 1) (ys 3)) ﹫ sigdcn (ys 1) (ys 3), ancOf P (ys 2) (succ (ys 3))) =
        ys 4) ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The sequence of a label is a function on the depth of its node -/
theorem tensorProdTwoAOneSeq_spec (x : M) :
    IsFunction (tensorProdTwoAOneSeq P x) ∧ dom (tensorProdTwoAOneSeq P x) = depOf P (left x) ∧
      ∀ i ∈ depOf P (left x), tensorProdTwoAOneSeq P x ﹫ i =
        !((right x ﹫ siglvl (uc (left x)) i) ﹫ sigdcn (uc (left x)) i,
          ancOf P (left x) (succ i)) := by
  have hres : IsSetRestrictedTo (fun i ↦ !((right x ﹫ siglvl (uc (left x)) i) ﹫
      sigdcn (uc (left x)) i, ancOf P (left x) (succ i))) (depOf P (left x)) :=
    isSetRestrictedTo_of_definable _
  exact ⟨isFunction_toSetRestrictedTo hres, dom_toSetRestrictedTo hres,
    fun i hi ↦ val_toSetRestrictedTo hres hi⟩

instance (P : M) : ClassFunction.Definable (fun x ↦ tensorProdTwoAOneSeq P x) Set.univ := by
  have hG : Multiclass.Definable (fun xs : Fin 3 → M ↦
      (fun x i ↦ !((right x ﹫ siglvl (uc (left x)) i) ﹫ sigdcn (uc (left x)) i,
        ancOf P (left x) (succ i))) (xs 0) (xs 1) = xs 2) Set.univ := by
    have h : (fun xs : Fin 3 → M ↦
        (fun x i ↦ !((right x ﹫ siglvl (uc (left x)) i) ﹫ sigdcn (uc (left x)) i,
          ancOf P (left x) (succ i))) (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
        ∃ f U p, f = right (xs 0) ∧ U = uc (left (xs 0)) ∧ p = left (xs 0) ∧
          !((f ﹫ siglvl U (xs 1)) ﹫ sigdcn U (xs 1), ancOf P p (succ (xs 1))) = xs 2 := by
      funext xs
      apply propext
      constructor
      · intro h
        exact ⟨_, _, _, rfl, rfl, rfl, h⟩
      · rintro ⟨f, U, p, rfl, rfl, rfl, h⟩
        exact h
    rw [h]
    infer_instance
  exact ClassFunction.Definable.toSetRestrictedTo
    (G := fun x i ↦ !((right x ﹫ siglvl (uc (left x)) i) ﹫ sigdcn (uc (left x)) i,
      ancOf P (left x) (succ i))) (D := fun x ↦ depOf P (left x))

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦
    xs 3 ∈ dom (xs 2) ∧ xs 1 ↾ xs 3 = xs 2 ↾ xs 3 ∧ (xs 1 ﹫ xs 3) [xs 0] (xs 2 ﹫ xs 3))
    Set.univ := by
  infer_instance

/-- The first difference of `xs j` and `xs k` is at `xs l`, where `xs j` is below in `xs i` -/
instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    xs l ∈ dom (xs k) ∧ xs j ↾ xs l = xs k ↾ xs l ∧ (xs j ﹫ xs l) [xs i] (xs k ﹫ xs l))
    Set.univ := by
  have h : (fun xs : Fin n → M ↦
      xs l ∈ dom (xs k) ∧ xs j ↾ xs l = xs k ↾ xs l ∧ (xs j ﹫ xs l) [xs i] (xs k ﹫ xs l)) =
      Multiclass.remap (fun ys : Fin 4 → M ↦ ys 3 ∈ dom (ys 2) ∧ ys 1 ↾ ys 3 = ys 2 ↾ ys 3 ∧
        (ys 1 ﹫ ys 3) [ys 0] (ys 2 ﹫ ys 3)) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ BKLt (xs 0) (xs 1) (xs 2)) Set.univ := by
  unfold BKLt; infer_instance

instance (P Q : M) : Class.Definable
    (fun z ↦ TensorProdTwoAOneLt P Q (lbl (left z)) (lbl (right z))) Set.univ := by
  have h : (fun z ↦ TensorProdTwoAOneLt P Q (lbl (left z)) (lbl (right z))) = fun z ↦
      ∃ x y s t, lbl (left z) = x ∧ lbl (right z) = y ∧ tensorProdTwoAOneSeq P x = s ∧
        tensorProdTwoAOneSeq P y = t ∧ BKLt (tensorProdTwoAOneCoordOdr P Q) s t := by
    funext z
    simp [TensorProdTwoAOneLt]
  rw [h]
  infer_instance

end Labels

section Orders

/-! ### Embeddings, the sibling order and the order of the coordinates -/

variable {a b f f' A R₁ P Q T U : M}

/-- The array `Q ⊗ Z ∈ aotci_1` -/
theorem tensorProdTwoAOneTgt_mem (hQ : Q ∈ aotci ((1 : ℕ) : M)) :
    tensorProdTwoAOneTgt Q ∈ aotci ((1 : ℕ) : M) := by
  obtain ⟨hf, hdom, -⟩ := mem_aotci_iff.mp hQ
  have h0 : (Q ↾ ((1 : ℕ) : M)) ﹫ ∅ = Q ﹫ ∅ :=
    val_restrict Q hf empty_mem_natCast_one
      (by rw [hdom]; exact mem_succ_of_mem empty_mem_natCast_one)
  refine tensorProdAOneAZero_mem_aotci ?_ (val_mem_otci_of_mem_aotci hQ (mem_succ_self _)) _
  rw [h0]
  exact val_mem_otci_of_mem_aotci hQ (mem_succ_of_mem empty_mem_natCast_one)

/-- An embedding of the array of `U ∈ stduoci_1` is determined by its values at the nodes of the
signature -/
theorem eq_of_mem_aotciEmbSet_one (hU : U ∈ stduoci ((1 : ℕ) : M)) (hT : T ∈ aotci ((1 : ℕ) : M))
    (hf : f ∈ aotciEmbSet ((1 : ℕ) : M) (aoc U) T) (hf' : f' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc U) T)
    (h : ∀ i ∈ dom (sig U), (f ﹫ siglvl U i) ﹫ sigdcn U i = (f' ﹫ siglvl U i) ﹫ sigdcn U i) :
    f = f' := by
  have he := (mem_aotciEmbSet_iff.mp hf).right
  have he' := (mem_aotciEmbSet_iff.mp hf').right
  have hA := aoc_mem_aotci_of_mem_stduoci_one hU
  refine he.isFunction.ext he'.isFunction (he.dom_eq.trans he'.dom_eq.symm) fun i hi ↦ ?_
  rw [he.dom_eq] at hi
  have hi' := hi
  rcases mem_or_eq_of_mem_succ hi' with hi' | rfl
  · have hi0 : i = ∅ := by
      rw [natCast_succ, natCast_zero, mem_succ_iff] at hi'
      rcases hi' with h' | h'
      · exact h'
      · simp at h'
    subst hi0
    obtain ⟨b, hb⟩ := exists_ndOf_eq_singleton_of_mem_otci_empty (val_mem_otci_of_mem_aotci hA hi)
    obtain ⟨c, hc⟩ := exists_ndOf_eq_singleton_of_mem_otci_empty (val_mem_otci_of_mem_aotci hT hi)
    rw [(he.isOtciEmbedding hi).eq_otciSngIso hb hc, (he'.isOtciEmbedding hi).eq_otciSngIso hb hc]
  · have hE := (he.isOtciEmbedding hi).isEmbedding.isEmbedding_ts.isInjectionFromTo
    have hE' := (he'.isOtciEmbedding hi).isEmbedding.isEmbedding_ts.isInjectionFromTo
    refine hE.isFunction.ext hE'.isFunction
      (hE.isFunctionFromTo.dom_eq.trans hE'.isFunctionFromTo.dom_eq.symm) fun w hw ↦ ?_
    rw [hE.isFunctionFromTo.dom_eq] at hw
    obtain ⟨j, hj, hl, hd⟩ := exists_sigdcn_eq hU hw
    have h' := h j hj
    rwa [hl, hd] at h'

/-- The sibling order: two nodes in the same linearly ordered set, in its order -/
theorem rel_sblOdrOf_iff (hP : IsSLOT P) : a [sblOdrOf P] b ↔
    a ∈ ndOf P ∧ b ∈ ndOf P ∧ ndlosOf P a = ndlosOf P b ∧ a [losOdr (ndlosOf P a)] b := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hP
  have hT := hS.isTreeStructure
  have hres : IsSetRestrictedTo (fun c ↦ losOdr (ndlosOf P c)) (ndOf P) :=
    isSetRestrictedTo_of_definable _
  change !(a, b) ∈ ⋃₀ ran ((fun c ↦ losOdr (ndlosOf P c)) ↾₀ ndOf P) ↔ _
  rw [mem_sUnion_iff]
  simp only [mem_ran_toSetRestrictedTo_iff hres]
  constructor
  · rintro ⟨y, ⟨c, hc, rfl⟩, hab⟩
    have hB := (hS.isStrictLinearOrderedSet_ndlos hc).isStrictLinearOrder
    have ha := hB.mem_left hab
    have hb := hB.mem_right hab
    have hlos {x : M} (hx : x ∈ losSet (ndlosOf P c)) : x ∈ ndOf P ∧ ndlosOf P x = ndlosOf P c := by
      rw [ndlosOf, hS.mem_losSet_ndlos_iff hc] at hx
      have hxn : x ∈ ndOf P := hT.subset_nd_of_mem_sblptn (hT.sbl_val_mem_sblptn hc) hx.left
      refine ⟨hxn, (hS.ndlos_eq_iff hxn hc).mpr ⟨?_, hx.right⟩⟩
      exact hT.sbl_val_of_mem_sblptn (hT.sbl_val_mem_sblptn hc) hx.left
    obtain ⟨han, hac⟩ := hlos ha
    obtain ⟨hbn, hbc⟩ := hlos hb
    exact ⟨han, hbn, hac.trans hbc.symm, by rw [hac]; exact hab⟩
  · rintro ⟨ha, -, -, hab⟩
    exact ⟨_, ⟨a, ha, rfl⟩, hab⟩

/-- The order of the coordinates is irreflexive and transitive -/
theorem coordOdr_props (hP : IsSLOT P) (hR1 : IsStrictLinearOrder R₁ A) :
    IsIrreflOn (lexProd R₁ A (sblOdrOf P) (ndOf P)) (A ×ˢ ndOf P) ∧
      IsTransOn (lexProd R₁ A (sblOdrOf P) (ndOf P)) (A ×ˢ ndOf P) := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hP
  refine ⟨fun x hx ↦ ?_, fun x hx y hy z hz hxy hyz ↦ ?_⟩
  · rw [mem_sprod_iff] at hx
    obtain ⟨u, -, v, -, rfl⟩ := hx
    rw [rel_lexProd_iff, rel_sblOdrOf_iff hP]
    rintro ⟨-, -, h | ⟨-, hv, -, -, h⟩⟩
    · exact hR1.irrefl u h
    · exact (hS.isStrictLinearOrderedSet_ndlos hv).isStrictLinearOrder.irrefl v h
  · rw [mem_sprod_iff] at hx hy hz
    obtain ⟨u₁, -, v₁, -, rfl⟩ := hx
    obtain ⟨u₂, -, v₂, -, rfl⟩ := hy
    obtain ⟨u₃, -, v₃, -, rfl⟩ := hz
    rw [rel_lexProd_iff] at hxy hyz ⊢
    obtain ⟨h1, h2, h12⟩ := hxy
    obtain ⟨-, h3, h23⟩ := hyz
    refine ⟨h1, h3, ?_⟩
    rcases h12 with h12 | ⟨rfl, h12⟩ <;> rcases h23 with h23 | ⟨rfl, h23⟩
    · exact .inl (hR1.trans h12 h23)
    · exact .inl h12
    · exact .inl h23
    · right
      refine ⟨rfl, ?_⟩
      rw [rel_sblOdrOf_iff hP] at h12 h23 ⊢
      obtain ⟨ha, hb, hab, h12⟩ := h12
      obtain ⟨-, hc, hbc, h23⟩ := h23
      refine ⟨ha, hc, hab.trans hbc, ?_⟩
      rw [← hab] at h23
      exact (hS.isStrictLinearOrderedSet_ndlos ha).isStrictLinearOrder.trans h12 h23

end Orders

section Mem

/-! ### `P ⊗ Q ∈ otci_1` -/

variable {f f' i k p p' x y P Q : M}

theorem succ_mem_succ_of_mem {n : M} (hn : n ∈ (ω : M)) (hi : i ∈ n) : succ i ∈ succ n := by
  have hiω : i ∈ (ω : M) := ordinal_omega.transitive _ hn hi
  rcases olt_trichotomy (ordinal_of_mem ordinal_omega (succ_mem_omega hiω))
    (ordinal_of_mem ordinal_omega hn) with h | h | h
  · exact mem_succ_of_mem h.right.right
  · rw [h]
    exact mem_succ_self _
  · exfalso
    rcases mem_or_eq_of_mem_succ h.right.right with h' | h'
    · exact notMem_self _ ((ordinal_of_mem ordinal_omega hiω).transitive _ h' hi)
    · exact notMem_self _ (h' ▸ hi)

variable (hP : P ∈ otci ((2 : ℕ) : M))
include hP

omit hP in
theorem tensorProdTwoAOneSeq_dom (p f : M) :
    dom (tensorProdTwoAOneSeq P !(p, f)) = depOf P p := by
  rw [(tensorProdTwoAOneSeq_spec _).right.left, left_orderedPair]

theorem tensorProdTwoAOneSeq_val (hp : p ∈ ndOf P) (hi : i ∈ depOf P p) :
    tensorProdTwoAOneSeq P !(p, f) ﹫ i =
      !((f ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc p) i, ancOf P p (succ i)) := by
  have huc := ((otciCond_two hP).right.left p hp).left
  rw [(tensorProdTwoAOneSeq_spec _).right.right i (by rwa [left_orderedPair]), left_orderedPair,
    right_orderedPair, (siglvl_eq_one huc (by rwa [dom_sig_uc_eq_depOf hP hp])).left]

/-- The coordinates of the sequences lie in `(Q ⊗ Z)(1)_nd × P_nd` -/
theorem tensorProdTwoAOneSeq_val_mem (hp : p ∈ ndOf P)
    (hf : f ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) (tensorProdTwoAOneTgt Q))
    (hi : i ∈ depOf P p) :
    tensorProdTwoAOneSeq P !(p, f) ﹫ i ∈
      ndOf (tensorProdTwoAOneTgt Q ﹫ ((1 : ℕ) : M)) ×ˢ ndOf P := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have huc := ((otciCond_two hP).right.left p hp).left
  have hw := (siglvl_eq_one huc (by rwa [dom_sig_uc_eq_depOf hP hp])).right
  have he := (mem_aotciEmbSet_iff.mp hf).right
  have hE := (he.isOtciEmbedding (mem_succ_self ((1 : ℕ) : M))).isEmbedding.isEmbedding_ts
  rw [tensorProdTwoAOneSeq_val hP hp hi, pair_mem_sprod_iff]
  exact ⟨hE.isInjectionFromTo.isFunctionFromTo.val_mem hw,
    (hS.isTreeStructure.anc_mem_nd hp
      (succ_mem_succ_of_mem (hS.isTreeStructure.dep_mem_omega hp) hi)).left⟩

/-- The sequences determine the labels -/
theorem eq_of_tensorProdTwoAOneSeq_eq (hQ : Q ∈ aotci ((1 : ℕ) : M)) (hp : p ∈ ndOf P)
    (hp' : p' ∈ ndOf P)
    (hf : f ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) (tensorProdTwoAOneTgt Q))
    (hf' : f' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p')) (tensorProdTwoAOneTgt Q))
    (h : tensorProdTwoAOneSeq P !(p, f) = tensorProdTwoAOneSeq P !(p', f')) :
    !(p, f) = !(p', f') := by
  obtain ⟨hPs, hnodes, -, ⟨r, hr⟩, -⟩ := otciCond_two hP
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hPs
  have hTS := hS.isTreeStructure
  have hd : depOf P p = depOf P p' := by
    rw [← tensorProdTwoAOneSeq_dom p f, h, tensorProdTwoAOneSeq_dom]
  have hdω := hTS.dep_mem_omega hp
  have hpp : p = p' := by
    by_cases h0 : depOf P p = ∅
    · have hpr : p ∈ rtOf P := TreeStructure.mem_rt_iff.mpr ⟨hp, h0⟩
      have hpr' : p' ∈ rtOf P := TreeStructure.mem_rt_iff.mpr ⟨hp', hd.symm.trans h0⟩
      rw [hr, mem_singleton_iff] at hpr hpr'
      rw [hpr, hpr']
    obtain ⟨-, hdm, hdeq⟩ := sUnion_mem_of_ne_empty hdω h0
    have hdm : ⋃₀ depOf P p ∈ depOf P p := hdm
    have hdeq : depOf P p = succ (⋃₀ depOf P p) := hdeq
    have h2 : tensorProdTwoAOneSeq P !(p, f) ﹫ ⋃₀ depOf P p =
        tensorProdTwoAOneSeq P !(p', f') ﹫ ⋃₀ depOf P p := by rw [h]
    rw [tensorProdTwoAOneSeq_val hP hp hdm, tensorProdTwoAOneSeq_val hP hp' (hd ▸ hdm),
      orderedPair_eq_orderedPair_iff] at h2
    have h3 := h2.right
    rw [← hdeq] at h3
    have ha : ancOf P p (depOf P p) = p := hTS.anc_dep hp
    have ha' : ancOf P p' (depOf P p') = p' := hTS.anc_dep hp'
    rw [ha, hd, ha'] at h3
    exact h3
  subst hpp
  have huc := (hnodes p hp).left
  rw [eq_of_mem_aotciEmbSet_one huc (tensorProdTwoAOneTgt_mem hQ) hf hf' fun i hi ↦ ?_]
  rw [dom_sig_uc_eq_depOf hP hp] at hi
  have h2 : tensorProdTwoAOneSeq P !(p, f) ﹫ i = tensorProdTwoAOneSeq P !(p, f') ﹫ i := by
    rw [h]
  rw [tensorProdTwoAOneSeq_val hP hp hi, tensorProdTwoAOneSeq_val hP hp hi,
    orderedPair_eq_orderedPair_iff] at h2
  rw [(siglvl_eq_one huc (by rwa [dom_sig_uc_eq_depOf hP hp])).left]
  exact h2.left

/-- The first differing coordinates of two sequences are comparable -/
theorem tensorProdTwoAOneSeq_cmp (hQ : Q ∈ aotci ((1 : ℕ) : M)) (hp : p ∈ ndOf P)
    (hp' : p' ∈ ndOf P)
    (hf : f ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) (tensorProdTwoAOneTgt Q))
    (hf' : f' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p')) (tensorProdTwoAOneTgt Q))
    (hk : k ∈ depOf P p) (hk' : k ∈ depOf P p')
    (hres : tensorProdTwoAOneSeq P !(p, f) ↾ k = tensorProdTwoAOneSeq P !(p', f') ↾ k)
    (hne : tensorProdTwoAOneSeq P !(p, f) ﹫ k ≠ tensorProdTwoAOneSeq P !(p', f') ﹫ k) :
    (tensorProdTwoAOneSeq P !(p, f) ﹫ k) [tensorProdTwoAOneCoordOdr P Q]
        (tensorProdTwoAOneSeq P !(p', f') ﹫ k) ∨
      (tensorProdTwoAOneSeq P !(p', f') ﹫ k) [tensorProdTwoAOneCoordOdr P Q]
        (tensorProdTwoAOneSeq P !(p, f) ﹫ k) := by
  obtain ⟨hPs, -, -, ⟨r, hr⟩, -⟩ := otciCond_two hP
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hPs
  have hTS := hS.isTreeStructure
  have hT1 := val_mem_otci_of_mem_aotci (tensorProdTwoAOneTgt_mem hQ) (mem_succ_self _)
  have hR1 := (rtlosOf_of_mem_otci_one hT1).left
  have hm := tensorProdTwoAOneSeq_val_mem hP hp hf hk
  have hm' := tensorProdTwoAOneSeq_val_mem hP hp' hf' hk'
  rw [tensorProdTwoAOneSeq_val hP hp hk] at hne hm ⊢
  rw [tensorProdTwoAOneSeq_val hP hp' hk'] at hne hm' ⊢
  rw [pair_mem_sprod_iff] at hm hm'
  change _ [lexProd _ _ _ _] _ ∨ _ [lexProd _ _ _ _] _
  rw [rel_lexProd_iff, rel_lexProd_iff]
  by_cases huu : (f ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc p) k = (f' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc p') k
  swap
  · rcases hR1.trichotomous hm.left hm'.left with h | h | h
    · exact .inl ⟨hm, hm', .inl h⟩
    · exact (huu h).elim
    · exact .inr ⟨hm', hm, .inl h⟩
  have haa : ancOf P p (succ k) ≠ ancOf P p' (succ k) := fun h ↦ hne (by rw [huu, h])
  -- the two ancestors of depth `k + 1` are siblings
  have hdω := hTS.dep_mem_omega hp
  have hdω' := hTS.dep_mem_omega hp'
  have hb : ancOf P p k = ancOf P p' k := by
    by_cases hk0 : k = ∅
    · subst hk0
      have h1 : ancOf P p ∅ ∈ rtOf P := hTS.anc_empty_mem_rt hp
      have h2 : ancOf P p' ∅ ∈ rtOf P := hTS.anc_empty_mem_rt hp'
      rw [hr, mem_singleton_iff] at h1 h2
      rw [h1, h2]
    obtain ⟨-, hkm, hkeq⟩ := sUnion_mem_of_ne_empty (ordinal_omega.transitive _ hdω hk) hk0
    have hseq := (tensorProdTwoAOneSeq_spec (P := P) !(p, f)).left
    have hseq' := (tensorProdTwoAOneSeq_spec (P := P) !(p', f')).left
    have hkd : ⋃₀ k ∈ depOf P p := (ordinal_of_mem ordinal_omega hdω).transitive _ hk hkm
    have hkd' : ⋃₀ k ∈ depOf P p' := (ordinal_of_mem ordinal_omega hdω').transitive _ hk' hkm
    have h2 := val_eq_of_restrict_eq hseq hseq' hres hkm
      (by rw [tensorProdTwoAOneSeq_dom]; exact hkd) (by rw [tensorProdTwoAOneSeq_dom]; exact hkd')
    rw [tensorProdTwoAOneSeq_val hP hp hkd, tensorProdTwoAOneSeq_val hP hp' hkd',
      orderedPair_eq_orderedPair_iff, ← hkeq] at h2
    exact h2.right
  have hac : ancOf P p (succ k) ∈ chdOf P (ancOf P p k) := hTS.anc_succ_mem_chd hp hk
  have hac' : ancOf P p' (succ k) ∈ chdOf P (ancOf P p k) := by
    rw [hb]
    exact hTS.anc_succ_mem_chd hp' hk'
  have hbn : ancOf P p k ∈ ndOf P := (hTS.anc_mem_nd hp (mem_succ_of_mem hk)).left
  have hkey := aoc_uc_eq_of_mem_chdOf hP hbn hac hac'
  have hsbl (c : M) (hc : c ∈ chdOf P (ancOf P p k)) :
      (SLOTreeStructure.ofM P).ts.sbl ﹫ c = chdOf P (ancOf P p k) := by
    have hcr : c ∈ (SLOTreeStructure.ofM P).ts.nd \ (SLOTreeStructure.ofM P).ts.rt := by
      rw [mem_sdiff_iff]
      exact ⟨mem_ndOf_of_mem_chdOf hPs hc, not_mem_rtOf_of_mem_chdOf hPs hc⟩
    rw [hTS.sbl_val_of_not_mem_rt hcr]
    change chdOf P (prtOf P c) = _
    rw [prtOf_eq_of_mem_chdOf hPs hc]
  have hn := mem_ndOf_of_mem_chdOf hPs hac
  have hn' := mem_ndOf_of_mem_chdOf hPs hac'
  have hlos : ndlosOf P (ancOf P p (succ k)) = ndlosOf P (ancOf P p' (succ k)) :=
    (hS.ndlos_eq_iff hn hn').mpr ⟨by rw [hsbl _ hac, hsbl _ hac'], hkey⟩
  have hB := (hS.isStrictLinearOrderedSet_ndlos hn).isStrictLinearOrder
  have hmem := hS.mem_losSet_ndlos hn
  have hmem' := hS.mem_losSet_ndlos hn'
  change _ ∈ losSet (ndlosOf P _) at hmem hmem'
  rw [← hlos] at hmem'
  rcases hB.trichotomous hmem hmem' with h | h | h
  · exact .inl ⟨hm, hm', .inr ⟨huu, (rel_sblOdrOf_iff hPs).mpr ⟨hn, hn', hlos, h⟩⟩⟩
  · exact (haa h).elim
  · refine .inr ⟨hm', hm, .inr ⟨huu.symm, (rel_sblOdrOf_iff hPs).mpr ⟨hn', hn, hlos.symm, ?_⟩⟩⟩
    rw [← hlos]
    exact h

omit hP in
/-- The embeddings of the array of `U ∈ stduoci_1` into an array in `aotci_1` are hereditarily
finite -/
theorem mem_vonNeumann_omega_of_mem_aotciEmbSet {U T : M} (hU : U ∈ stduoci ((1 : ℕ) : M))
    (hT : T ∈ aotci ((1 : ℕ) : M)) (hf : f ∈ aotciEmbSet ((1 : ℕ) : M) (aoc U) T) :
    f ∈ (𝕍 ω : M) := by
  have he := (mem_aotciEmbSet_iff.mp hf).right
  have hUu := (mem_stduoci_iff.mp hU).left
  rw [mem_uoci_iff_of_mem_omega (natCast_mem_omega 1)] at hUu
  have hfin := mem_finaotci_iff.mp hUu.right.right.left
  refine he.isFunction.mem_vonNeumann_omega ?_ fun i hi ↦ ?_
  · rw [he.dom_eq]
    exact mem_vonNeumann_omega_of_mem_omega (succ_mem_omega (natCast_mem_omega 1))
  rw [he.dom_eq] at hi
  have hiω := mem_omega_of_mem_succ (natCast_mem_omega 1) hi
  have hE := (he.isOtciEmbedding hi).isEmbedding.isEmbedding_ts.isInjectionFromTo
  have hWi := mem_finotci_iff.mp (hfin.right i hi)
  refine hE.isFunction.mem_vonNeumann_omega ?_ fun a ha ↦ ?_
  · rw [hE.isFunctionFromTo.dom_eq]
    exact hWi.right.mem_vonNeumann_omega (ndOf_subset_of_mem_otci hiω hWi.left)
  · rw [hE.isFunctionFromTo.dom_eq] at ha
    exact ndOf_subset_of_mem_otci hiω (val_mem_otci_of_mem_aotci hT hi)
      (hE.isFunctionFromTo.val_mem ha)

/-- `P ⊗ Q ∈ otci_1` for `P ∈ otci_2` and `Q ∈ aotci_1` -/
theorem tensorProdTwoAOne_mem_otci (hQ : Q ∈ aotci ((1 : ℕ) : M)) :
    tensorProdTwoAOne P Q ∈ otci ((1 : ℕ) : M) := by
  obtain ⟨hPs, hnodes, -, -, -⟩ := otciCond_two hP
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hPs
  have hTS := hS.isTreeStructure
  have hT := tensorProdTwoAOneTgt_mem hQ
  have hT1 := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hR1 := (rtlosOf_of_mem_otci_one hT1).left
  obtain ⟨hirr, htr⟩ := coordOdr_props hPs hR1
  have hLb (x : M) := mem_tensorProdTwoAOneLbls_iff (x := x) (P := P) (Q := Q)
  have hresN : IsSetRestrictedTo (fun x ↦ !(dctUZero, x)) (tensorProdTwoAOneLbls P Q) :=
    isSetRestrictedTo_of_definable _
  have hNds (a : M) : a ∈ tensorProdTwoAOneNds P Q ↔
      ∃ x ∈ tensorProdTwoAOneLbls P Q, !(dctUZero, x) = a :=
    mem_ran_toSetRestrictedTo_iff hresN
  -- the sequences of the labels
  have hseq (x : M) (hx : x ∈ tensorProdTwoAOneLbls P Q) :
      IsFunction (tensorProdTwoAOneSeq P x) ∧ Ordinal (dom (tensorProdTwoAOneSeq P x)) ∧
        ∀ k ∈ dom (tensorProdTwoAOneSeq P x), tensorProdTwoAOneSeq P x ﹫ k ∈
          ndOf (tensorProdTwoAOneTgt Q ﹫ ((1 : ℕ) : M)) ×ˢ ndOf P := by
    obtain ⟨p, hp, -, f, hf, rfl⟩ := (hLb x).mp hx
    refine ⟨(tensorProdTwoAOneSeq_spec _).left, ?_, fun k hk ↦ ?_⟩
    · rw [tensorProdTwoAOneSeq_dom]
      exact ordinal_of_mem ordinal_omega (hTS.dep_mem_omega hp)
    · rw [tensorProdTwoAOneSeq_dom] at hk
      exact tensorProdTwoAOneSeq_val_mem hP hp hf hk
  -- the order of the labels
  have hirr' (x : M) (hx : x ∈ tensorProdTwoAOneLbls P Q) : ¬TensorProdTwoAOneLt P Q x x :=
    not_bkLt_self hirr (hseq x hx).right.right
  have htr' (x y z : M) (hx : x ∈ tensorProdTwoAOneLbls P Q) (hy : y ∈ tensorProdTwoAOneLbls P Q)
      (hz : z ∈ tensorProdTwoAOneLbls P Q) (hxy : TensorProdTwoAOneLt P Q x y)
      (hyz : TensorProdTwoAOneLt P Q y z) : TensorProdTwoAOneLt P Q x z :=
    BKLt.trans (hseq x hx).left (hseq y hy).left (hseq z hz).left (hseq x hx).right.left
      (hseq y hy).right.left (hseq z hz).right.left htr (hseq x hx).right.right
      (hseq y hy).right.right (hseq z hz).right.right hxy hyz
  have htri' (x y : M) (hx : x ∈ tensorProdTwoAOneLbls P Q) (hy : y ∈ tensorProdTwoAOneLbls P Q) :
      TensorProdTwoAOneLt P Q x y ∨ x = y ∨ TensorProdTwoAOneLt P Q y x := by
    obtain ⟨p, hp, -, f, hf, rfl⟩ := (hLb x).mp hx
    obtain ⟨p', hp', -, f', hf', rfl⟩ := (hLb y).mp hy
    rcases bkLt_trichotomous (hseq _ hx).left (hseq _ hy).left (hseq _ hx).right.left
      (hseq _ hy).right.left (fun k hk hk' hres hne ↦ by
        rw [tensorProdTwoAOneSeq_dom] at hk hk'
        exact tensorProdTwoAOneSeq_cmp hP hQ hp hp' hf hf' hk hk' hres hne) with h | h | h
    · exact .inl h
    · exact .inr (.inl (eq_of_tensorProdTwoAOneSeq_eq hP hQ hp hp' hf hf' h))
    · exact .inr (.inr h)
  -- the order of the nodes
  have hOdr (a b : M) : a [tensorProdTwoAOneOdr P Q] b ↔
      (a ∈ tensorProdTwoAOneNds P Q ∧ b ∈ tensorProdTwoAOneNds P Q) ∧
        TensorProdTwoAOneLt P Q (lbl a) (lbl b) := by
    change !(a, b) ∈ (tensorProdTwoAOneNds P Q ×ˢ tensorProdTwoAOneNds P Q) ∩₀ _ ↔ _
    rw [mem_comprehension_iff, pair_mem_sprod_iff, left_orderedPair, right_orderedPair]
  have hlbl {a : M} (ha : a ∈ tensorProdTwoAOneNds P Q) :
      lbl a ∈ tensorProdTwoAOneLbls P Q ∧ a = !(dctUZero, lbl a) := by
    obtain ⟨x, hx, rfl⟩ := (hNds a).mp ha
    rw [lbl_orderedPair]
    exact ⟨hx, rfl⟩
  have hSLO : IsStrictLinearOrder (tensorProdTwoAOneOdr P Q) (tensorProdTwoAOneNds P Q) := by
    refine ⟨(isRelationOn_sprod _).subset (comprehension_subset _ _), fun a ha h ↦ ?_,
      fun a ha b hb c hc hab hbc ↦ ?_, fun a ha b hb ↦ ?_⟩
    · exact hirr' _ (hlbl ha).left ((hOdr a a).mp h).right
    · exact (hOdr a c).mpr ⟨⟨ha, hc⟩, htr' _ _ _ (hlbl ha).left (hlbl hb).left (hlbl hc).left
        ((hOdr a b).mp hab).right ((hOdr b c).mp hbc).right⟩
    · rcases htri' _ _ (hlbl ha).left (hlbl hb).left with h | h | h
      · exact .inl ((hOdr a b).mpr ⟨⟨ha, hb⟩, h⟩)
      · exact .inr (.inl (by rw [(hlbl ha).right, (hlbl hb).right, h]))
      · exact .inr (.inr ((hOdr b a).mpr ⟨⟨hb, ha⟩, h⟩))
  refine rtLosSLOT_mem_otci_one (fun _ ↦ ?_) fun a ha ↦ ?_
  · rw [isStrictLinearOrderedSet_orderedPair_iff]
    exact hSLO
  · rw [losSet_orderedPair] at ha
    obtain ⟨x, hx, rfl⟩ := (hNds a).mp ha
    refine ⟨x, ?_, rfl⟩
    obtain ⟨p, hp, -, f, hf, rfl⟩ := (hLb x).mp hx
    exact orderedPair_mem_vonNeumann_omega (ndOf_subset_of_mem_otci (natCast_mem_omega 2) hP hp)
      (mem_vonNeumann_omega_of_mem_aotciEmbSet (hnodes p hp).left hT hf)

end Mem

section Array

/-! ### `P ⊗ Q ∈ aotci_1` for `P ∈ aotci_2` -/

variable {P Q : M}

theorem dom_tensorProdAZeroAZero (P Q : M) : dom (tensorProdAZeroAZero P Q) = succ ∅ := by
  rw [tensorProdAZeroAZero, dom_singletonFun, succ, insert_empty_eq_singleton]

/-- `P ⊗ Q ∈ aotci_1` for `P ∈ aotci_2` and `Q ∈ aotci_1` -/
theorem tensorProdATwoAOne_mem_aotci (hP : P ∈ aotci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((1 : ℕ) : M)) : tensorProdATwoAOne P Q ∈ aotci ((1 : ℕ) : M) := by
  obtain ⟨hPf, hPdom, -⟩ := mem_aotci_iff.mp hP
  have h12 : ((1 : ℕ) : M) ∈ (2 : M) := natCast_one_mem_two
  have h02 : (∅ : M) ∈ (2 : M) := natCast_mem_natCast_of_lt (j := 0) (k := 2) (by omega)
  have hP2 : P ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hP (mem_succ_self _)
  -- the array `B = (P ↾ 2) ⊗ (Q ↾ 1)`
  have hPX : (P ↾ (2 : M)) ﹫ ((1 : ℕ) : M) ∈ otci ((1 : ℕ) : M) := by
    rw [val_restrict P hPf h12 (by rw [hPdom]; exact mem_succ_of_mem h12)]
    exact val_mem_otci_of_mem_aotci hP (mem_succ_of_mem h12)
  have hB : tensorProdATwoAOneBase P Q ∈ aotci ((1 : ℕ) : M) := by
    refine tensorProdAOneAZero_mem_aotci ?_ hPX _
    rw [restrict_restrict,
      val_restrict P hPf (by rw [mem_inter_iff]; exact ⟨h02, empty_mem_natCast_one⟩)
      (by rw [hPdom]; exact mem_succ_of_mem h02)]
    exact val_mem_otci_of_mem_aotci hP (mem_succ_of_mem h02)
  obtain ⟨hBf, hBdom, -⟩ := mem_aotci_iff.mp hB
  have hB1 := val_mem_otci_of_mem_aotci hB (mem_succ_self _)
  have hB1eq : tensorProdATwoAOneBase P Q ﹫ ((1 : ℕ) : M) =
      tensorProdOneAZero ((P ↾ (2 : M)) ﹫ ((1 : ℕ) : M)) (Q ↾ ((1 : ℕ) : M)) := by
    have hA0 : IsFunction (tensorProdAZeroAZero ((P ↾ (2 : M)) ↾ ((1 : ℕ) : M))
        (Q ↾ ((1 : ℕ) : M))) := isFunction_singletonFun _ _
    have h := cc_val_self hA0
      (tensorProdOneAZero ((P ↾ (2 : M)) ﹫ ((1 : ℕ) : M)) (Q ↾ ((1 : ℕ) : M)))
    rw [dom_tensorProdAZeroAZero] at h
    exact h
  have hT2 := tensorProdTwoAOne_mem_otci hP2 hQ
  obtain ⟨hR1, hs1, -⟩ := rtlosOf_of_mem_otci_one hB1
  obtain ⟨hR2, hs2, -⟩ := rtlosOf_of_mem_otci_one hT2
  -- the nodes of `B(1)` and of `P(2) ⊗ Q` are disjoint: their labels have arrays on `1` and
  -- embeddings on `2`
  have hdisj : ndOf (tensorProdATwoAOneBase P Q ﹫ ((1 : ℕ) : M)) ∩
      ndOf (tensorProdTwoAOne (P ﹫ (2 : M)) Q) = ∅ := by
    rw [empty_iff]
    intro a ha
    rw [mem_inter_iff] at ha
    obtain ⟨ha1, ha2⟩ := ha
    have hresN : IsSetRestrictedTo (fun x ↦ !(dctUZero, x))
        (tensorProdTwoAOneLbls (P ﹫ (2 : M)) Q) := isSetRestrictedTo_of_definable _
    rw [tensorProdTwoAOne, ndOf_rtLosSLOT, losSet_orderedPair] at ha2
    obtain ⟨x, hx, rfl⟩ := (mem_ran_toSetRestrictedTo_iff hresN).mp ha2
    obtain ⟨p, -, -, f, hf, rfl⟩ := mem_tensorProdTwoAOneLbls_iff.mp hx
    rw [hB1eq, tensorProdOneAZero, ndOf_rtLosSLOT, losSet_orderedPair,
      mem_ran_tensorProdOneAZeroRelabel_iff hPX] at ha1
    obtain ⟨q, -, hq⟩ := ha1
    rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hq
    have hdom := congrArg dom hq.right.right
    rw [dom_tensorProdAZeroAZero, (mem_aotciEmbSet_iff.mp hf).right.dom_eq] at hdom
    have h1 : (∅ : M) = succ ∅ := TreeStructure.eq_of_succ_eq_succ ordinal_empty hdom
    exact succ_ne_empty _ h1.symm
  -- the concatenated linearly ordered set
  have hL : IsStrictLinearOrderedSet (losConcat
      (rtlosOf (tensorProdATwoAOneBase P Q ﹫ ((1 : ℕ) : M)) ﹫ trvAZero)
      (rtlosOf (tensorProdTwoAOne (P ﹫ (2 : M)) Q) ﹫ trvAZero)) := by
    rw [losConcat, isStrictLinearOrderedSet_orderedPair_iff, hs1, hs2]
    exact hR1.concat hR2 hdisj
  have hX := rtLosSLOT_mem_otci_one (fun _ ↦ hL) fun a ha ↦ by
    rw [losConcat, losSet_orderedPair, hs1, hs2, mem_union_iff] at ha
    rcases ha with ha | ha
    · exact exists_eq_of_mem_otci_one hB1 ha
    · exact exists_eq_of_mem_otci_one hT2 ha
  -- the array
  have hBr : IsFunction (tensorProdATwoAOneBase P Q ↾ ((1 : ℕ) : M)) := hBf.restrict _
  have hBrdom : dom (tensorProdATwoAOneBase P Q ↾ ((1 : ℕ) : M)) = ((1 : ℕ) : M) :=
    dom_restrict_of_subset hBf fun x hx ↦ by
      rw [hBdom]
      exact mem_succ_of_mem hx
  rw [mem_aotci_iff]
  refine ⟨hBr.cc _, by rw [tensorProdATwoAOne, dom_cc, hBrdom], fun i hi ↦ ?_, ?_⟩
  · rw [otciL_ciRec_restrict hi, tensorProdATwoAOne, cc_val_of_mem hBr _ (by rw [hBrdom]; exact hi),
      val_restrict _ hBf hi (by rw [hBdom]; exact mem_succ_of_mem hi)]
    exact val_mem_otci_of_mem_aotci hB (mem_succ_of_mem hi)
  · have h := cc_val_self hBr (rtLosSLOT trvAZero (losConcat
      (rtlosOf (tensorProdATwoAOneBase P Q ﹫ ((1 : ℕ) : M)) ﹫ trvAZero)
      (rtlosOf (tensorProdTwoAOne (P ﹫ (2 : M)) Q) ﹫ trvAZero)))
    rw [hBrdom] at h
    rw [tensorProdATwoAOne, h]
    exact hX

end Array

end FirstOrder.Language.MemStructure
