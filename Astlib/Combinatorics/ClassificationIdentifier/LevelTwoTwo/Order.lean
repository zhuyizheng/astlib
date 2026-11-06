/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.Parent
/-!
# The parent is a node; the order of `P ⊗ Q`

The parent of a node of `P ⊗ Q` is a node, the order is a semi-linear tree order, the trees of
the extensions of level one, the least new node with a given nearest old node above it, and the
keys and linearly ordered sets of the children.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M]

section TensorProd

variable {P Q T W : M}

section Slot

variable {U k x y : M}

section PrtMem

variable {V X X' t σ : M}

/-- A root of `P` with an embedding into `(Q, V)` for `V` with empty signature is a node -/
theorem root_mem_tensorProdTwoTwoNds (hP : P ∈ otci ((2 : ℕ) : M)) (ht : t ∈ rtOf P)
    (hV : V ∈ stduoci ((1 : ℕ) : M)) (hs : sig V = ∅)
    (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q (aoc V))) :
    !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q := by
  obtain ⟨-, -, hroot, -, -⟩ := otciCond_two hP
  have h1 : ((1 : ℕ) : M) ∈ (ω : M) := natCast_mem_omega 1
  have htu := hroot t ht
  have htsig := sig_eq_empty_of_mem_trvuoci h1 htu
  have hc := uociCond_of_mem_stduoci_one hV
  have hctV : ctp V = dct := hc.right.right.right.right.right.left ⟨hs, isOdd_one⟩
  have hdom3 : dom V = ((3 : ℕ) : M) :=
    hc.right.right.right.right.right.right.left.mpr (.inl ⟨hs, isOdd_one⟩)
  have hctt := (mem_trvuoci_iff.mp htu).right.right
  have hemb : embTpSigs Q (aoc V) (uc t) σ = ∅ := by
    have hres : IsSetRestrictedTo (fun i ↦ embTpSigEntry Q (aoc V) (uc t) σ i)
        (dom (sig (uc t))) := isSetRestrictedTo_of_definable _
    refine (isFunction_toSetRestrictedTo hres).isRelation.eq_empty_of_dom_eq_empty ?_
    rw [dom_toSetRestrictedTo hres, htsig, dom_empty]
  rw [mem_tensorProdTwoTwoNds_iff]
  refine ⟨t, mem_ndOf_of_mem_rtOf ht, V, hV, σ, hσ,
    ⟨⟨hσ, ?_, ?_, fun h ↦ ?_⟩, fun _ ↦ htsig⟩, rfl⟩
  · rw [hemb, contraction_empty, hs]
  · exact ⟨fun h ↦ (ct_ne_dct (h.symm.trans hctV)).elim,
      fun h ↦ (ct_ne_dct (h.left.symm.trans hctt)).elim⟩
  · rw [hdom3] at h
    exact (notMem_self _ h).elim

/-- The restriction of an embedding of `t_uc` to the array of a root `t₀` of `P`, into a target
with the same level-`0` tree -/
theorem embRestrict_mem_aotciEmbSet_of_mem_rtOf (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) (ht : t ∈ ndOf P) {t₀ : M} (ht₀ : t₀ ∈ rtOf P)
    (hX : X ∈ aotci ((1 : ℕ) : M)) (hX' : X' ∈ aotci ((1 : ℕ) : M)) (h0 : X ﹫ ∅ = X' ﹫ ∅)
    (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q X)) :
    embRestrict (uc t₀) σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t₀)) (tensorProdATwoAOne Q X') := by
  obtain ⟨-, -, hroot, -, -⟩ := otciCond_two hP
  have h1 : ((1 : ℕ) : M) ∈ (ω : M) := natCast_mem_omega 1
  have hA : aoc (uc t₀) = trvAotci ((1 : ℕ) : M) := aoc_eq_trvAotci h1 (hroot t₀ ht₀)
  have hAa := (mem_trvaotci_iff.mp (trvAotci_mem_trvaotci (M := M) h1)).left
  obtain ⟨hAf, hAdom, -⟩ := mem_aotci_iff.mp hAa
  have hT' := tensorProdATwoAOne_mem_aotci hQ hX'
  obtain ⟨hTf, hTdom, -⟩ := mem_aotci_iff.mp hT'
  have he := (mem_aotciEmbSet_iff.mp hσ).right
  have hres : IsSetRestrictedTo (fun i ↦ (σ ﹫ i) ↾ ndOf (aoc (uc t₀) ﹫ i)) ((2 : ℕ) : M) :=
    isSetRestrictedTo_of_definable _
  have h2 : ((2 : ℕ) : M) = succ ((1 : ℕ) : M) := natCast_succ 1
  have hAt : aoc (uc t₀) = trvAotci ((1 : ℕ) : M) := hA
  rw [hAt]
  refine mem_aotciEmbSet_of_isAotciEmbedding hAf hAdom hTf hTdom
    ⟨isFunction_toSetRestrictedTo hres, by rw [embRestrict, dom_toSetRestrictedTo hres, h2],
      fun {i} hi ↦ ?_⟩
  rw [embRestrict, val_toSetRestrictedTo hres (by rw [h2]; exact hi), hA]
  rcases mem_or_eq_of_mem_succ hi with hi' | rfl
  · have hi0 : i = ∅ := by
      rw [natCast_succ, natCast_zero, mem_succ_iff] at hi'
      rcases hi' with h' | h'
      · exact h'
      · simp at h'
    subst hi0
    have hE := he.isOtciEmbedding hi
    have hdom : dom (σ ﹫ ∅) = ndOf (trvAotci ((1 : ℕ) : M) ﹫ ∅) := by
      rw [hE.isEmbedding.isEmbedding_ts.isInjectionFromTo.isFunctionFromTo.dom_eq,
        aoc_uc_val_zero_of_mem_otci_two hP ht]
      rfl
    rw [← hdom, restrict_dom hE.isEmbedding.isEmbedding_ts.isInjectionFromTo.isFunction,
      ← tensorProdATwoAOne_val_zero_eq hQ hX hX' h0, ← aoc_uc_val_zero_of_mem_otci_two hP ht]
    exact hE
  · rw [ndOf_trvAotci_one_val_one, restrict_empty]
    exact isOtciEmbedding_empty_of_ndOf_eq_empty ndOf_trvAotci_one_val_one

/-- The parent of a node of depth `1` is the root -/
theorem tensorProdTwoTwoPrt_mem_of_sUnion_eq_empty (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hx : x ∈ tensorProdTwoTwoNds P Q)
    (hd : dom (sig (uc x)) ≠ ∅) (hm : ⋃₀ dom (sig (uc x)) = ∅) :
    tensorProdTwoTwoPrt P Q x ∈ tensorProdTwoTwoNds P Q := by
  have hTS := (show (SLOTreeStructure.ofM P).IsSLOTreeStructure from
    (otciCond_two hP).left).isTreeStructure
  rw [tensorProdTwoTwoPrt, if_pos hm, prtOne, prtUc, hm, prtRootAnc, cutRes]
  rw [mem_tensorProdTwoTwoNds_iff] at hx
  obtain ⟨t, ht, V, hV, σ, hσ, -, rfl⟩ := hx
  rw [uc_orderedPair] at hd
  have hq : nodeQ !(V, !(t, σ)) = t := by simp [nodeQ, lbl_orderedPair, left_orderedPair]
  have hH : nodeH !(V, !(t, σ)) = σ := by simp [nodeH, lbl_orderedPair, right_orderedPair]
  rw [uc_orderedPair, hq, hH]
  have ht₀ : ancOf P t ∅ ∈ rtOf P := hTS.anc_empty_mem_rt ht
  have h0 : (∅ : M) ∈ dom (sig V) := empty_mem_of_ordinal_of_ne_empty
    (ordinal_of_mem ordinal_omega (dom_sig_mem_omega_of_mem_stduoci_one hV)) hd
  have hV' := iniSeg_mem_stduoci hV h0
  have hs' : sig (iniSeg V ∅) = ∅ := by rw [sig_iniSeg, restrict_empty]
  refine root_mem_tensorProdTwoTwoNds hP ht₀ hV' hs'
    (embRestrict_mem_aotciEmbSet_of_mem_rtOf hP hQ ht ht₀ (aoc_mem_aotci_of_mem_stduoci_one hV)
      (aoc_mem_aotci_of_mem_stduoci_one hV') ?_ hσ)
  rw [aoc_iniSeg, iniSegAoc_val_zero hV]

/-- The parent of a node of depth `m > 1` is a node -/
theorem tensorProdTwoTwoPrt_mem_of_sUnion_ne_empty (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hx : x ∈ tensorProdTwoTwoNds P Q)
    (hm0 : ⋃₀ dom (sig (uc x)) ≠ ∅) :
    tensorProdTwoTwoPrt P Q x ∈ tensorProdTwoTwoNds P Q := by
  rw [tensorProdTwoTwoPrt, if_neg hm0]
  rw [mem_tensorProdTwoTwoNds_iff] at hx
  obtain ⟨t, ht, V, hV, σ, hσ, hemb, rfl⟩ := hx
  rw [uc_orderedPair] at hm0
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hB := tensorProdATwoAOne_mem_aotci hQ hX
  have hmω := dom_sig_mem_omega_of_mem_stduoci_one hV
  have hd0 : dom (sig V) ≠ ∅ := fun h' ↦ hm0 (by rw [h', sUnion_empty])
  have hm : ⋃₀ dom (sig V) ∈ dom (sig V) := (sUnion_mem_of_ne_empty hmω hd0).right.left
  have hU := hemb.left
  set s := embTpSigs Q (aoc V) (uc t) σ with hsdef
  have hs : IsFinSeqSeq s :=
    isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUt) (aoc V) σ
  have hcon : contraction s = sig V := hU.right.left
  have he' : sig V ﹫ ⋃₀ dom (sig V) ∈ ctrSet s := by
    obtain ⟨-, -, -, hran, -⟩ := isContraction_contraction hs
    rw [← hran, hcon, (uociCond_of_mem_stduoci_one hV).right.right.right.left.left.mem_ran_iff]
    exact ⟨_, hm, rfl⟩
  obtain ⟨l, hl, k, hk, hv, hmin⟩ := exists_firstOcc hs he'
  have hfo : IsFirstOcc s (sig V ﹫ ⋃₀ dom (sig V)) l k := ⟨hl, hk, hv, hmin⟩
  -- the parent's components
  have hnQ : nodeQ !(V, !(t, σ)) = t := nodeQ_orderedPair _ _ _
  have hnU : nodeU !(V, !(t, σ)) = uc t := nodeU_orderedPair _ _ _
  have hnH : nodeH !(V, !(t, σ)) = σ := nodeH_orderedPair _ _ _
  have hpos : prtPos Q !(V, !(t, σ)) = !(l, k) := by
    rw [prtPos, prtSeqs, prtEntry, uc_orderedPair, hnU, hnH]
    exact firstOccPos_eq hs hfo
  have hrow : prtRow Q !(V, !(t, σ)) = l := by rw [prtRow, hpos, left_orderedPair]
  have hancL : prtAncL P Q !(V, !(t, σ)) = ancOf P t l := by rw [prtAncL, hnQ, hrow]
  have hancS : prtAncS P Q !(V, !(t, σ)) = ancOf P t (succ l) := by
    rw [prtAncS, ancSucc, hnQ, hrow]
  have hnode : prtNode Q !(V, !(t, σ)) = sigdcn (uc t) l := by rw [prtNode, hnU, hrow]
  have hsucc : prtSucc Q !(V, !(t, σ)) =
      ⋃₀ (aboveIn (odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
        (ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
        ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l) ∩₀ fun z ↦ IsLeastIn
          (odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
          (aboveIn (odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
            (ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
            ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l)) z) := by
    rw [prtSucc, prtAbove, prtOdr, prtSmall, prtImg, prtUc, uc_orderedPair, uociEmbTgt,
      uociEmbTgt, aoc_iniSeg, hnH, hnode]
    rfl
  have hucfI : prtUcfImg P Q !(V, !(t, σ)) = ucfImg σ (uc (ancOf P t l)) := by
    rw [prtUcfImg, hnH, hancL]
  rw [prtTwo, prtUc, uc_orderedPair, prtLbl]
  -- the image `y` of the `l`-th node
  have hlsig : l ∈ dom (sig (uc t)) := by rw [← dom_embTpSigs Q (aoc V) (uc t) σ]; exact hl
  have hlrow : s ﹫ l = tpSig Q (aoc V) ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l) :=
    embTpSigs_val hUt hlsig
  have hkr := hk
  rw [hlrow] at hkr
  have hyC : (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) := by
    by_contra hnot
    rw [tpSig_eq_empty_of_not_isTpTwo hnot, dom_empty] at hkr
    exact notin_empty _ hkr
  obtain ⟨q, hq, -, h, hh, hyeq⟩ := mem_tensorProdTwoAOneNds_iff'.mp hyC
  rw [hyeq] at hyC hkr
  have hk' : k ∈ depOf (Q ﹫ 2) q := by
    rw [← dom_sig_uc_eq_depOf hQ2 hq, ← dom_tpSig_eq hyC]
    exact hkr
  have hksig : k ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hk'
  have hval (i : M) (hi : i ∈ dom (sig (uc q))) : (s ﹫ l) ﹫ i =
      !(((1 : ℕ) : M), sigImg (aoc V) q h i) := by
    rw [hlrow, hyeq, tpSig_val_eq hQ hyC hi]
    rfl
  have hje : sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V)) := by
    have h' := hv
    rw [hval k hksig, sig_val_eq_pair hV hm, orderedPair_eq_orderedPair_iff] at h'
    exact h'.right
  have hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V)) := by
    intro i hi he
    have hik : i ∈ dom (sig (uc q)) := (ordinal_of_mem ordinal_omega
      (dom_sig_mem_omega_of_mem_stduoci_one (uc_mem_stduoci_of_mem_otci_two hQ2 hq))).transitive
        _ hksig hi
    have hi' : i ∈ dom (s ﹫ l) := by rw [hlrow, hyeq, dom_tpSig_eq hyC]; exact hik
    rcases hmin l hl i hi' (by rw [hval i hik, he, sig_val_eq_pair hV hm]) with
      ⟨-, rfl⟩ | h' | ⟨-, h'⟩
    · exact notMem_self _ hi
    · exact notMem_self _ h'
    · exact notMem_self _ ((ordinal_of_mem_dom_val hs hl hk).transitive _ hi h')
  have hspec := succ_spec hQ hV hm hq hyC hh hk' hfirst hje
  rw [← hyeq] at hspec
  have hl' : l ∈ depOf P t := by rw [← dom_sig_uc_eq_depOf hP ht]; exact hlsig
  have hDne {D : M} (h' : D ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V)))) :
      D ≠ ∅ := by
    obtain ⟨-, -, -, -, -, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp h'
    exact orderedPair_ne_empty _ _
  by_cases hcase : PrtCase P Q !(V, !(t, σ))
  · rw [if_pos hcase, prtLblOne, hancL, cutRes, hnH]
    rw [PrtCase, hsucc, hucfI] at hcase
    rcases hspec with ⟨hD0, hk0, -, hnone⟩ | ⟨D, hDe, hDC, -, -, hDsig, -, -, hDucf⟩
    · rw [hD0] at hcase
      exact prt_mem_case_one hP hQ hV hm ht hσ hfo hU hm0 (.inl ⟨rfl, hk0⟩) (fun _ ↦ hnone)
        hcase
    · rw [hDe] at hcase
      exact prt_mem_case_one hP hQ hV hm ht hσ hfo hU hm0 (.inr ⟨hDC, hDsig, hDucf⟩)
        (fun h0 ↦ (hDne hDC h0).elim) hcase
  · rw [if_neg hcase, prtLblTwo, prtCt, prtEmbTwo, hancL, hancS, hnH, hnode, hsucc]
    rw [PrtCase, hsucc, hucfI] at hcase
    rcases hspec with ⟨hD0, -, -, hnone⟩ | ⟨D, hDe, hDC, hlt, hmin', hDsig, hDdom, hDct, hDucf⟩
    · exfalso
      rw [hD0] at hcase
      by_cases hl0 : l = ∅
      · subst hl0
        rw [ucfImg_ancOf_empty hP ht] at hcase
        exact hcase rfl
      · obtain ⟨-, ⟨i0, hi0, hr⟩, hyr⟩ := ucf_anc_rel hP ht hl' hl0 hB hσ
        refine hnone _ ?_ hyr
        rw [hr]
        exact img_mem_lastSeg hP hQ hV hm ht hσ hfo hi0
    · rw [hDe]
      rw [hDe] at hcase
      exact prt_mem_case_two hP hQ hV hm ht hσ hfo hU hm0 hDC hlt hmin' hDsig hDdom hDct hDucf
        hcase


end PrtMem

/-- The parent of a node of positive depth is a node -/
theorem tensorProdTwoTwoPrt_mem (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hx : x ∈ tensorProdTwoTwoNds P Q) (hd : dom (sig (uc x)) ≠ ∅) :
    tensorProdTwoTwoPrt P Q x ∈ tensorProdTwoTwoNds P Q := by
  by_cases hm : ⋃₀ dom (sig (uc x)) = ∅
  · exact tensorProdTwoTwoPrt_mem_of_sUnion_eq_empty hP hQ hx hd hm
  · exact tensorProdTwoTwoPrt_mem_of_sUnion_ne_empty hP hQ hx hm

theorem isTreeStructure_tensorProdTwoTwoTs (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) : (tensorProdTwoTwoTs P Q).IsTreeStructure := by
  have hresD : IsSetRestrictedTo (fun x ↦ dom (sig (uc x))) (tensorProdTwoTwoNds P Q) :=
    isSetRestrictedTo_of_definable _
  have hresC : IsSetRestrictedTo (fun x ↦ tensorProdTwoTwoNds P Q ∩₀ fun y ↦ IsPrtChd P Q x y)
      (tensorProdTwoTwoNds P Q) := isSetRestrictedTo_of_definable _
  have hchdEq : (tensorProdTwoTwoTs P Q).chd =
      (fun x ↦ tensorProdTwoTwoNds P Q ∩₀ fun y ↦ IsPrtChd P Q x y) ↾₀ tensorProdTwoTwoNds P Q := by
    rw [tensorProdTwoTwoTs, TreeStructure.chd_mk]
    rfl
  have hchd {x y : M} (hx : x ∈ tensorProdTwoTwoNds P Q) :
      y ∈ (tensorProdTwoTwoTs P Q).chd ﹫ x ↔
        y ∈ tensorProdTwoTwoNds P Q ∧ IsPrtChd P Q x y := by
    rw [hchdEq, val_toSetRestrictedTo hresC hx, mem_comprehension_iff]
  have hdep {x : M} (hx : x ∈ tensorProdTwoTwoNds P Q) :
      (tensorProdTwoTwoTs P Q).dep ﹫ x = dom (sig (uc x)) := by
    rw [tensorProdTwoTwoTs, TreeStructure.dep_mk, val_toSetRestrictedTo hresD hx]
  have hnd : (tensorProdTwoTwoTs P Q).nd = tensorProdTwoTwoNds P Q := by
    rw [tensorProdTwoTwoTs, TreeStructure.nd_mk]
  refine
    { isOrderedPair := TreeStructure.isOrderedPair_mk _ _ _
      isOrderedPair_right := TreeStructure.isOrderedPair_right_mk _ _ _
      dep_fromTo := ?_
      isFunction_chd := ?_
      dom_chd := ?_
      chd_subset := fun a ha y hy ↦ ?_
      dep_of_mem_chd := fun a ha b hb ↦ ?_
      existsUnique_prt := fun b hb hpos ↦ ?_ }
  · rw [tensorProdTwoTwoTs, TreeStructure.dep_mk, TreeStructure.nd_mk]
    exact isFunctionFromTo_toSetRestrictedTo hresD fun x hx ↦
      dom_sig_mem_omega_of_mem_stduoci_one (uc_mem_stduoci_of_mem_tensorProdTwoTwoNds hx)
  · rw [hchdEq]
    exact isFunction_toSetRestrictedTo hresC
  · rw [hchdEq, hnd]
    exact dom_toSetRestrictedTo hresC
  · rw [hnd] at ha ⊢
    exact ((hchd ha).mp hy).left
  · rw [hnd] at ha
    obtain ⟨hbn, hbd, rfl⟩ := (hchd ha).mp hb
    rw [hdep hbn, hdep ha, succ_dom_sig_uc_tensorProdTwoTwoPrt hbn hbd]
  · rw [hnd] at hb
    rw [hdep hb] at hpos
    have hd : dom (sig (uc b)) ≠ ∅ := fun h ↦ by
      rw [h] at hpos
      simpa using hpos.right.right
    have ha := tensorProdTwoTwoPrt_mem hP hQ hb hd
    refine ⟨tensorProdTwoTwoPrt P Q b, (hchd ha).mpr ⟨hb, hd, rfl⟩, fun a' ha' ↦ ?_⟩
    have ha'n : a' ∈ tensorProdTwoTwoNds P Q := by
      by_contra hn
      have h0 : (tensorProdTwoTwoTs P Q).chd ﹫ a' = ∅ := by
        refine val_eq_empty_of_not_mem_dom ?_
        rw [hchdEq, dom_toSetRestrictedTo hresC]
        exact hn
      change b ∈ (tensorProdTwoTwoTs P Q).chd ﹫ a' at ha'
      rw [h0] at ha'
      simp at ha'
    exact ((hchd ha'n).mp ha').right.right.symm

section OdrDef

instance : ClassFunction.Definable (fun z : M ↦
    tensorProdTwoTwoCoordOdr (left z) (left (right z)) (right (right z))) Set.univ := by
  unfold tensorProdTwoTwoCoordOdr
  have : ClassFunction.Definable (fun z : M ↦
      tensorProdATwoAOne (left (right z)) (right (right z))) Set.univ :=
    ClassFunction.Definable.comp₁ (H := fun w : M ↦ tensorProdATwoAOne (left w) (right w))
      (F := fun z : M ↦ right z)
  have : ClassFunction.Definable (fun z : M ↦ losOdr (rtlosOf
      (tensorProdATwoAOne (left (right z)) (right (right z)) ﹫ ((1 : ℕ) : M)) ﹫ trvAZero))
      Set.univ :=
    ClassFunction.Definable.comp₁
      (H := fun T : M ↦ losOdr (rtlosOf (T ﹫ ((1 : ℕ) : M)) ﹫ trvAZero))
      (F := fun z : M ↦ tensorProdATwoAOne (left (right z)) (right (right z)))
  have : ClassFunction.Definable (fun z : M ↦
      ndOf (tensorProdATwoAOne (left (right z)) (right (right z)) ﹫ ((1 : ℕ) : M))) Set.univ :=
    ClassFunction.Definable.comp₁ (H := fun T : M ↦ ndOf (T ﹫ ((1 : ℕ) : M)))
      (F := fun z : M ↦ tensorProdATwoAOne (left (right z)) (right (right z)))
  have : ClassFunction.Definable (fun z : M ↦ sblOdrOf (left z)) Set.univ :=
    ClassFunction.Definable.comp₁ (H := fun P : M ↦ sblOdrOf P)
  have : Multiclass.Definable
      (fun ys : Fin 5 → M ↦ lexProd (ys 0) (ys 1) (ys 2) (ys 3) = ys 4) Set.univ :=
    (inferInstance : MulticlassFunction.Definable
      (fun ys : Fin 4 → M ↦ lexProd (ys 0) (ys 1) (ys 2) (ys 3)) Set.univ).1
  exact ClassFunction.Definable.comp₄ (H := lexProd) (E := fun z : M ↦ ndOf (left z))

/-- `R` is the coordinate order of the node `x` of `P ⊗ Q` -/
def IsCoordOdrOf (P Q x R : M) : Prop := tensorProdTwoTwoCoordOdr P Q (aoc (uc x)) = R

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ IsCoordOdrOf (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  obtain ⟨C, hC⟩ : ∃ C : ClassFunction M,
      C = fun z ↦ tensorProdTwoTwoCoordOdr (left z) (left (right z)) (right (right z)) :=
    ⟨_, rfl⟩
  have : C.Definable Set.univ := by
    rw [hC]
    infer_instance
  have h : (fun xs : Fin 4 → M ↦ IsCoordOdrOf (xs 0) (xs 1) (xs 2) (xs 3)) = fun xs : Fin 4 → M ↦
      ∃ X y z : M, X = aoc (uc (xs 2)) ∧ y = !(xs 1, X) ∧ z = !(xs 0, y) ∧ C z = xs 3 := by
    funext xs
    rw [hC]
    simp [IsCoordOdrOf, left_orderedPair, right_orderedPair]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ IsCoordOdrOf (xs i) (xs j) (xs k) (xs l)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsCoordOdrOf (xs i) (xs j) (xs k) (xs l)) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ IsCoordOdrOf (ys 0) (ys 1) (ys 2) (ys 3)) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The sequences of the labels of `x` and `y` are in the Brouwer–Kleene order for `R` -/
def SeqBKLt (P R x y : M) : Prop :=
  BKLt R (tensorProdTwoAOneSeq P (lbl x)) (tensorProdTwoAOneSeq P (lbl y))

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ SeqBKLt (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  obtain ⟨S, hS⟩ : ∃ S : ClassFunction M,
      S = fun w ↦ tensorProdTwoAOneSeq (left w) (right w) := ⟨_, rfl⟩
  have : S.Definable Set.univ := by
    rw [hS]
    infer_instance
  have h : (fun xs : Fin 4 → M ↦ SeqBKLt (xs 0) (xs 1) (xs 2) (xs 3)) = fun xs : Fin 4 → M ↦
      ∃ w w' : M, w = !(xs 0, lbl (xs 2)) ∧ w' = !(xs 0, lbl (xs 3)) ∧
        ∃ s t : M, S w = s ∧ S w' = t ∧ BKLt (xs 1) s t := by
    funext xs
    rw [hS]
    simp [SeqBKLt, left_orderedPair, right_orderedPair]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ SeqBKLt (xs i) (xs j) (xs k) (xs l)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ SeqBKLt (xs i) (xs j) (xs k) (xs l)) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ SeqBKLt (ys 0) (ys 1) (ys 2) (ys 3)) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable
    (fun xs : Fin 4 → M ↦ TensorProdTwoTwoLt (xs 0) (xs 1) (xs 2) (xs 3)) Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ TensorProdTwoTwoLt (xs 0) (xs 1) (xs 2) (xs 3)) =
      fun xs : Fin 4 → M ↦ aoc (uc (xs 2)) = aoc (uc (xs 3)) ∧
        ∃ R : M, IsCoordOdrOf (xs 0) (xs 1) (xs 2) R ∧ SeqBKLt (xs 0) R (xs 2) (xs 3) := by
    funext xs
    simp [TensorProdTwoTwoLt, IsCoordOdrOf, SeqBKLt]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ TensorProdTwoTwoLt (xs i) (xs j) (xs k) (xs l)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ TensorProdTwoTwoLt (xs i) (xs j) (xs k) (xs l)) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ TensorProdTwoTwoLt (ys 0) (ys 1) (ys 2) (ys 3)) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance (P Q : M) :
    Class.Definable (fun z : M ↦ TensorProdTwoTwoLt P Q (left z) (right z)) Set.univ := by
  have h : (fun z : M ↦ TensorProdTwoTwoLt P Q (left z) (right z)) = fun z : M ↦
      ∃ P' Q' a b : M, (P' = P ∧ Q' = Q) ∧ (a = left z ∧ b = right z) ∧
        TensorProdTwoTwoLt P' Q' a b := by
    funext z
    simp
  rw [h]
  infer_instance

theorem rel_tensorProdTwoTwoOdr_iff {a b : M} : a [tensorProdTwoTwoOdr P Q] b ↔
    (a ∈ tensorProdTwoTwoNds P Q ∧ b ∈ tensorProdTwoTwoNds P Q) ∧ TensorProdTwoTwoLt P Q a b := by
  change !(a, b) ∈ (tensorProdTwoTwoNds P Q ×ˢ tensorProdTwoTwoNds P Q) ∩₀
    (fun z ↦ TensorProdTwoTwoLt P Q (left z) (right z)) ↔ _
  rw [mem_comprehension_iff, pair_mem_sprod_iff, left_orderedPair, right_orderedPair]

end OdrDef

section Order

variable {V V' σ D : M}

theorem eq_ciQuint (hP : IsFunction P) (hdom : dom P = ((5 : ℕ) : M)) :
    P = ciQuint (aoc P) (sig P) (ctp P) (ucflvldcn P) (ucfdr P) := by
  refine hP.ext (isFunction_ciQuint _ _ _ _ _) (by rw [hdom, dom_ciQuint]) fun x hx ↦ ?_
  rw [hdom] at hx
  simp only [natCast_succ, natCast_zero, mem_succ_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | hx
  · exact (ucfdr_ciQuint _ _ _ _ _).symm
  · exact (ucflvldcn_ciQuint _ _ _ _ _).symm
  · exact (ctp_ciQuint _ _ _ _ _).symm
  · exact (sig_ciQuint _ _ _ _ _).symm
  · exact (aoc_ciQuint _ _ _ _ _).symm
  · simp at hx

/-- The target `V` of an embedding is determined by its array and the embedding -/
theorem eq_of_isUociEmb (hV : V ∈ stduoci ((1 : ℕ) : M)) (hV' : V' ∈ stduoci ((1 : ℕ) : M))
    (haoc : aoc V = aoc V') (h : IsUociEmb Q U V σ) (h' : IsUociEmb Q U V' σ) : V = V' := by
  have hc := uociCond_of_mem_stduoci_one hV
  have hc' := uociCond_of_mem_stduoci_one hV'
  have hsig : sig V = sig V' := by
    rw [← h.right.left, ← h'.right.left, haoc]
  have hct : ctp V = ct ↔ ctp V' = ct := by
    rw [h.right.right.left, h'.right.right.left, haoc]
  have hctp : ctp V = ctp V' := by
    rcases hc.right.right.right.right.left with h1 | h1 <;>
      rcases hc'.right.right.right.right.left with h2 | h2
    · rw [h1, h2]
    · exact absurd (hct.mp h1) (by rw [h2]; exact ct_ne_dct.symm)
    · exact absurd (hct.mpr h2) (by rw [h1]; exact ct_ne_dct.symm)
    · rw [h1, h2]
  have h3 : dom V = ((3 : ℕ) : M) ↔ dom V' = ((3 : ℕ) : M) := by
    rw [hc.right.right.right.right.right.right.left, hc'.right.right.right.right.right.right.left,
      hsig, hctp]
  rcases hc.right.left with hd | hd | hd
  · rw [eq_ciTriple hc.left hd, eq_ciTriple hc'.left (h3.mp hd), haoc, hsig, hctp]
  · have hd' : dom V' = ((5 : ℕ) : M) := by
      rcases hc'.right.left with hd' | hd' | hd'
      · rw [← h3] at hd'
        rw [hd'] at hd
        exact absurd (natCast_injective hd) (by omega)
      · exact hd'
      · exact absurd hd' (dom_ne_six_of_mem_stduoci_one hV')
    have h35 : ((3 : ℕ) : M) ∈ ((5 : ℕ) : M) := natCast_mem_natCast_iff.mpr (by omega)
    obtain ⟨hu, hr⟩ := h.right.right.right (by rw [hd]; exact h35)
    obtain ⟨hu', hr'⟩ := h'.right.right.right (by rw [hd']; exact h35)
    rw [eq_ciQuint hc.left hd, eq_ciQuint hc'.left hd', haoc, hsig, hctp, hu, hu', hr, hr', haoc]
  · exact absurd hd (dom_ne_six_of_mem_stduoci_one hV)

/-- The order of `P ⊗ Q` strictly linearly orders every set of nodes with the same key -/
theorem isStrictLinearOrder_tensorProdTwoTwoOdr (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) {S : M}
    (hS : ∀ x ∈ S, x ∈ tensorProdTwoTwoNds P Q ∧ aoc (uc x) = D) :
    IsStrictLinearOrder (tensorProdTwoTwoOdr P Q ∩ (S ×ˢ S)) S := by
  obtain ⟨hPs, -, -, -, -⟩ := otciCond_two hP
  have hTS := (show (SLOTreeStructure.ofM P).IsSLOTreeStructure from hPs).isTreeStructure
  -- the data of a node
  have hdata {x : M} (hx : x ∈ S) : ∃ t ∈ ndOf P, ∃ V ∈ stduoci ((1 : ℕ) : M), ∃ σ,
      σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q D) ∧
        IsTensorProdTwoTwoEmb Q t V σ ∧ x = !(V, !(t, σ)) ∧ aoc V = D := by
    obtain ⟨hxn, hxD⟩ := hS x hx
    rw [mem_tensorProdTwoTwoNds_iff] at hxn
    obtain ⟨t, ht, V, hV, σ, hσ, h, rfl⟩ := hxn
    rw [uc_orderedPair] at hxD
    rw [hxD] at hσ
    exact ⟨t, ht, V, hV, σ, hσ, h, rfl, hxD⟩
  have hTD {x : M} (hx : x ∈ S) : tensorProdATwoAOne Q D ∈ aotci ((1 : ℕ) : M) := by
    obtain ⟨t, -, V, hV, σ, -, -, -, hVD⟩ := hdata hx
    rw [← hVD]
    exact tensorProdATwoAOne_mem_aotci hQ (aoc_mem_aotci_of_mem_stduoci_one hV)
  have hco {x : M} (hx : x ∈ S) :=
    coordOdr_props hPs (rtlosOf_of_mem_otci_one
      (val_mem_otci_of_mem_aotci (hTD hx) (mem_succ_self _))).left
  have hseq {t σ : M} (ht : t ∈ ndOf P)
      (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q D)) :
      IsFunction (tensorProdTwoAOneSeq P !(t, σ)) ∧
        Ordinal (dom (tensorProdTwoAOneSeq P !(t, σ))) ∧
        ∀ k ∈ dom (tensorProdTwoAOneSeq P !(t, σ)), tensorProdTwoAOneSeq P !(t, σ) ﹫ k ∈
          ndOf (tensorProdATwoAOne Q D ﹫ ((1 : ℕ) : M)) ×ˢ ndOf P := by
    refine ⟨(tensorProdTwoAOneSeq_spec _).left, ?_, fun k hk ↦ ?_⟩
    · rw [tensorProdTwoAOneSeq_dom]
      exact ordinal_of_mem ordinal_omega (hTS.dep_mem_omega ht)
    · rw [tensorProdTwoAOneSeq_dom] at hk
      exact tensorProdTwoAOneSeq_val_mem hP ht hσ hk
  have hlt {x y : M} (hx : x ∈ S) (hy : y ∈ S) : x [tensorProdTwoTwoOdr P Q] y ↔
      BKLt (tensorProdTwoTwoCoordOdr P Q D) (tensorProdTwoAOneSeq P (lbl x))
        (tensorProdTwoAOneSeq P (lbl y)) := by
    rw [rel_tensorProdTwoTwoOdr_iff, TensorProdTwoTwoLt, (hS x hx).right, (hS y hy).right]
    exact ⟨fun h ↦ h.right.right, fun h ↦ ⟨⟨(hS x hx).left, (hS y hy).left⟩, rfl, h⟩⟩
  rw [isStrictLinearOrder_inter_sprod_iff]
  refine ⟨fun x hx h ↦ ?_, fun x hx y hy z hz hxy hyz ↦ ?_, fun x hx y hy ↦ ?_⟩
  · obtain ⟨t, ht, V, -, σ, hσ, -, rfl, -⟩ := hdata hx
    rw [hlt hx hx, lbl_orderedPair] at h
    exact not_bkLt_self (hco hx).left (hseq ht hσ).right.right h
  · rw [hlt hx hy] at hxy
    rw [hlt hy hz] at hyz
    rw [hlt hx hz]
    obtain ⟨t, ht, V, -, σ, hσ, -, hxe, -⟩ := hdata hx
    obtain ⟨t', ht', V', -, σ', hσ', -, hye, -⟩ := hdata hy
    obtain ⟨t'', ht'', V'', -, σ'', hσ'', -, hze, -⟩ := hdata hz
    rw [hxe, lbl_orderedPair] at hxy ⊢
    rw [hye, lbl_orderedPair] at hxy hyz
    rw [hze, lbl_orderedPair] at hyz ⊢
    exact BKLt.trans (hseq ht hσ).left (hseq ht' hσ').left (hseq ht'' hσ'').left
      (hseq ht hσ).right.left (hseq ht' hσ').right.left (hseq ht'' hσ'').right.left (hco hx).right
      (hseq ht hσ).right.right (hseq ht' hσ').right.right (hseq ht'' hσ'').right.right hxy hyz
  · rw [hlt hx hy, hlt hy hx]
    obtain ⟨t, ht, V, hV, σ, hσ, hemb, rfl, hVD⟩ := hdata hx
    obtain ⟨t', ht', V', hV', σ', hσ', hemb', rfl, hVD'⟩ := hdata hy
    rw [lbl_orderedPair, lbl_orderedPair]
    rcases bkLt_trichotomous (hseq ht hσ).left (hseq ht' hσ').left (hseq ht hσ).right.left
      (hseq ht' hσ').right.left (fun k hk hk' hres hne ↦ by
        rw [tensorProdTwoAOneSeq_dom] at hk hk'
        exact tensorProdTwoAOneSeq_cmp hP (hTD hx) ht ht' hσ hσ' hk hk' hres hne) with h | h | h
    · exact .inl h
    · right
      left
      have hl := eq_of_tensorProdTwoAOneSeq_eq hP (hTD hx) ht ht' hσ hσ' h
      rw [orderedPair_eq_orderedPair_iff] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rw [eq_of_isUociEmb hV hV' (hVD.trans hVD'.symm) hemb.left hemb'.left]
    · exact .inr (.inr h)

end Order

end Slot

/-- `P ⊗ Q` is a semi-linearly ordered tree structure: the parent of a node is a node, of depth one
less, and the siblings with the same key are strictly linearly ordered -/
theorem isSLOT_tensorProdTwoTwo (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M)) :
    IsSLOT (tensorProdTwoTwo P Q) := by
  have hT := isTreeStructure_tensorProdTwoTwoTs hP hQ
  have hnd : (tensorProdTwoTwoTs P Q).nd = tensorProdTwoTwoNds P Q := by
    rw [tensorProdTwoTwoTs, TreeStructure.nd_mk]
  refine SLOTreeStructure.isSLOTreeStructure_ofTsOdr hT (fun a ha ↦ ?_) fun X hX D ↦ ?_
  · rw [hnd, mem_tensorProdTwoTwoNds_iff] at ha
    obtain ⟨t, -, V, hV, σ, -, -, rfl⟩ := ha
    rw [left_orderedPair]
    exact ⟨⟨_, _, rfl⟩, (uociCond_of_mem_stduoci_one hV).left,
      dom_mem_of_mem_uoci (natCast_mem_omega 1) (mem_stduoci_iff.mp hV).left⟩
  · refine isStrictLinearOrder_tensorProdTwoTwoOdr (D := D) hP hQ fun x hx ↦ ?_
    rw [mem_keyBlock_iff] at hx
    refine ⟨hnd ▸ hT.subset_nd_of_mem_sblptn hX hx.left, ?_⟩
    rw [← hx.right]
    simp [aoc, uc]

/-- `P ⊗ Q` has a single root, with the trivial `uoci_1` -/
theorem rtOf_tensorProdTwoTwo (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M)) :
    ∃ r, rtOf (tensorProdTwoTwo P Q) = {r} ∧ uc r ∈ trvuoci ((1 : ℕ) : M) := by
  obtain ⟨-, hPnd, hroot, ⟨t₀, ht₀⟩, -⟩ := otciCond_two hP
  have h1 : ((1 : ℕ) : M) ∈ (ω : M) := natCast_mem_omega 1
  have ht₀r : t₀ ∈ rtOf P := by
    rw [ht₀]
    exact mem_singleton t₀
  have ht₀nd := mem_ndOf_of_mem_rtOf ht₀r
  have ht₀u := hroot t₀ ht₀r
  have ht₀s := (hPnd t₀ ht₀nd).left
  have ht₀sig := sig_eq_empty_of_mem_trvuoci h1 ht₀u
  have hV₀ : trvUoci ((1 : ℕ) : M) ∈ trvuoci ((1 : ℕ) : M) := trvUoci_mem_trvuoci h1 isOdd_one
  have hV₀s := (mem_trvuoci_iff.mp hV₀).left
  have hV₀sig := sig_eq_empty_of_mem_trvuoci h1 hV₀
  have hTA := tensorProdATwoAOne_mem_aotci hQ (aoc_mem_aotci_of_mem_stduoci_one hV₀s)
  obtain ⟨σ₀, hσ₀⟩ := exists_mem_aotciEmbSet_trvAotci_one hTA
  rw [← aoc_eq_trvAotci h1 ht₀u] at hσ₀
  have hres : IsSetRestrictedTo (fun x ↦ dom (sig (uc x))) (tensorProdTwoTwoNds P Q) :=
    isSetRestrictedTo_of_definable _
  have hrt : rtOf (tensorProdTwoTwo P Q) = (tensorProdTwoTwoTs P Q).rt := by
    change (SLOTreeStructure.mk (tensorProdTwoTwoTs P Q) _).ts.rt = _
    rw [SLOTreeStructure.ts_mk]
  refine ⟨!(trvUoci ((1 : ℕ) : M), !(t₀, σ₀)), ?_, by rw [uc_orderedPair]; exact hV₀⟩
  rw [hrt]
  ext x
  rw [TreeStructure.mem_rt_iff, tensorProdTwoTwoTs, TreeStructure.nd_mk, TreeStructure.dep_mk,
    mem_singleton_iff]
  constructor
  · rintro ⟨hx, hd⟩
    rw [val_toSetRestrictedTo hres hx] at hd
    rw [mem_tensorProdTwoTwoNds_iff] at hx
    obtain ⟨t, ht, V, hV, σ, hσ, hemb, rfl⟩ := hx
    rw [uc_orderedPair] at hd
    have hsf := (uociCond_of_mem_stduoci_one hV).right.right.right.left.left
    have hs : sig V = ∅ := hsf.isRelation.eq_empty_of_dom_eq_empty hd
    have hVe : V = trvUoci ((1 : ℕ) : M) :=
      eq_of_mem_trvuoci_of_isOdd h1 isOdd_one (mem_trvuoci_one_of_sig_eq_empty hV hs) hV₀
    have htu := (hPnd t ht).left
    have hts : sig (uc t) = ∅ := hemb.right hs
    have htr : t ∈ rtOf P := by
      have hdep := dom_sig_uc_eq_depOf hP ht
      rw [hts, dom_empty] at hdep
      exact TreeStructure.mem_rt_iff.mpr ⟨ht, hdep.symm⟩
    rw [ht₀, mem_singleton_iff] at htr
    subst htr hVe
    rw [eq_of_mem_aotciEmbSet_one htu hTA hσ hσ₀ fun i hi ↦ by simp [hts] at hi]
  · rintro rfl
    have hemb : embTpSigs Q (aoc (trvUoci ((1 : ℕ) : M))) (uc t₀) σ₀ = ∅ := by
      have hres' : IsSetRestrictedTo
          (fun i ↦ embTpSigEntry Q (aoc (trvUoci ((1 : ℕ) : M))) (uc t₀) σ₀ i)
          (dom (sig (uc t₀))) := isSetRestrictedTo_of_definable _
      refine (isFunction_toSetRestrictedTo hres').isRelation.eq_empty_of_dom_eq_empty ?_
      rw [dom_toSetRestrictedTo hres', ht₀sig, dom_empty]
    have hctV := (mem_trvuoci_iff.mp hV₀).right.right
    have hctt := (mem_trvuoci_iff.mp ht₀u).right.right
    have hx : !(trvUoci ((1 : ℕ) : M), !(t₀, σ₀)) ∈ tensorProdTwoTwoNds P Q := by
      rw [mem_tensorProdTwoTwoNds_iff]
      refine ⟨t₀, ht₀nd, _, hV₀s, σ₀, hσ₀, ⟨⟨hσ₀, ?_, ?_, fun h ↦ ?_⟩, fun _ ↦ ht₀sig⟩, rfl⟩
      · rw [hemb, contraction_empty, hV₀sig]
      · exact ⟨fun h ↦ (ct_ne_dct (h.symm.trans hctV)).elim,
          fun h ↦ (ct_ne_dct (h.left.symm.trans hctt)).elim⟩
      · rw [trvUoci_eq h1 isOdd_one, dom_ciTriple] at h
        exact (notMem_self _ h).elim
    refine ⟨hx, ?_⟩
    rw [val_toSetRestrictedTo hres hx, uc_orderedPair, hV₀sig, dom_empty]

section RtLosEq

/-! ### Trees in `otci_1` determined by their order; arrays of the extensions of initial
segments -/

variable {D Y : M}

/-- A semi-linearly ordered tree structure whose nodes are all roots with the key `D` is
`ofRtLos D` of its linearly ordered set of roots -/
theorem SLOTreeStructure.IsSLOTreeStructure.eq_ofRtLos {S : SLOTreeStructure M}
    (hS : S.IsSLOTreeStructure) (hrt : S.rt = S.nd) (hne : S.nd ≠ ∅)
    (hkey : ∀ a ∈ S.nd, left a ﹫ ∅ = D) : S = SLOTreeStructure.ofRtLos D (S.rtlos ﹫ D) := by
  have hT := hS.isTreeStructure
  have hrt' : S.ts.rt = S.ts.nd := hrt
  have hdep (a : M) (ha : a ∈ S.ts.nd) : S.ts.dep ﹫ a = ∅ := by
    rw [← hrt', TreeStructure.mem_rt_iff] at ha
    exact ha.right
  have hchd (a : M) (ha : a ∈ S.ts.nd) : S.ts.chd ﹫ a = ∅ := by
    rw [empty_iff]
    intro b hb
    have h := hT.dep_of_mem_chd a ha b hb
    rw [hdep b (hT.chd_subset a ha hb)] at h
    exact succ_ne_empty _ h.symm
  have hrtne : S.ts.rt ≠ ∅ := by rw [hrt']; exact hne
  have hsbl (X : M) : X ∈ S.sblptn ↔ X = S.rt := by
    rw [sblptn, TreeStructure.mem_sblptn_iff]
    constructor
    · rintro ⟨h | h, hX⟩
      · exact h
      · rw [hT.isFunction_chd.mem_ran_iff] at h
        obtain ⟨a, ha, rfl⟩ := h
        rw [hT.dom_chd] at ha
        exact (hX (hchd a ha)).elim
    · rintro rfl
      exact ⟨.inl rfl, hrtne⟩
  have hrtX : S.rt ∈ S.sblptn := (hsbl _).mpr rfl
  have hD : D ∈ dom (S.losfn ﹫ S.rt) := by
    rw [hS.mem_dom_losfn_val_iff hrtX]
    rw [ne_empty_iff] at hne
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, by rw [hrt]; exact ha, hkey a ha⟩
  have hset : losSet (S.rtlos ﹫ D) = S.nd := by
    ext a
    rw [rtlos, hS.mem_losSet_iff hrtX hD, hrt]
    exact ⟨fun h ↦ h.left, fun h ↦ ⟨h, hkey a h⟩⟩
  have hsetne : losSet (S.rtlos ﹫ D) ≠ ∅ := by rw [hset]; exact hne
  unfold SLOTreeStructure.ofRtLos
  rw [if_neg hsetne, hset]
  refine hS.eq_mk.trans ?_
  congr 1
  · rw [hT.eq_mk]
    change TreeStructure.mk _ _ _ = TreeStructure.mk _ _ _
    rw [TreeStructure.mk_eq_mk_iff]
    refine ⟨rfl, ?_, ?_⟩
    · exact hT.dep_fromTo.isFunction.ext (isFunction_constFun _ _)
        (by rw [hT.dep_fromTo.dom_eq, dom_constFun]) fun a ha ↦ by
          rw [hT.dep_fromTo.dom_eq] at ha
          rw [hdep a ha, val_constFun ha]
    · exact hT.isFunction_chd.ext (isFunction_constFun _ _)
        (by rw [hT.dom_chd, dom_constFun]) fun a ha ↦ by
          rw [hT.dom_chd] at ha
          rw [hchd a ha, val_constFun ha]
  · refine hS.isFunction_losfn.ext (isFunction_singletonFun _ _) ?_ fun X hX ↦ ?_
    · ext X
      rw [hS.dom_losfn, hsbl, dom_singletonFun, mem_singleton_iff, hrt]
    rw [hS.dom_losfn, hsbl] at hX
    rw [hX, ← hrt, singletonFun_val]
    refine (hS.isFunction_losfn_val hrtX).ext (isFunction_singletonFun _ _) ?_ fun D' hD' ↦ ?_
    · ext D'
      rw [hS.mem_dom_losfn_val_iff hrtX, dom_singletonFun, mem_singleton_iff, hrt]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact hkey a ha
      · rintro rfl
        rw [ne_empty_iff] at hne
        obtain ⟨a, ha⟩ := hne
        exact ⟨a, ha, hkey a ha⟩
    have hD'D : D' = D := by
      rw [hS.mem_dom_losfn_val_iff hrtX] at hD'
      obtain ⟨a, ha, rfl⟩ := hD'
      rw [hrt] at ha
      exact hkey a ha
    rw [hD'D, singletonFun_val]
    rfl

/-- A tree in `otci_1` is the tree of its linearly ordered set of roots -/
theorem eq_rtLosSLOT_of_mem_otci_one (hY : Y ∈ otci ((1 : ℕ) : M)) :
    Y = rtLosSLOT trvAZero (rtlosOf Y ﹫ trvAZero) := by
  have hYS := isSLOT_of_mem_otci hY
  by_cases hne : ndOf Y = ∅
  · obtain ⟨-, hset, -⟩ := rtlosOf_of_mem_otci_one hY
    rw [hne] at hset
    have h := eq_emptySLOT_of_ndOf_eq_empty hYS hne
    rw [rtLosSLOT, SLOTreeStructure.ofRtLos, if_pos hset, h]
    rfl
  have hS : (SLOTreeStructure.ofM Y).IsSLOTreeStructure := hYS
  have h := hS.eq_ofRtLos (D := trvAZero) (ndOf_eq_rtOf_of_mem_otci_one hY).symm hne
    fun a ha ↦ by
      obtain ⟨l, -, rfl⟩ := exists_eq_of_mem_otci_one hY ha
      rw [left_orderedPair, ← natCast_zero, dctUZero_eq_lfTrvUoci]
      exact aoc_lfTrvUoci _
  exact congrArg SLOTreeStructure.toM h

/-- A relation on `a` relates only elements of `a` -/
theorem mem_of_rel_of_isRelationOn {R a x y : M} (hR : IsRelationOn R a) (h : x [R] y) :
    x ∈ a ∧ y ∈ a := by
  rw [← hR.right, rel_restrict₂_iff] at h
  exact h.right

/-- Two trees in `otci_1` with the same nodes and the same order are equal -/
theorem eq_of_mem_otci_one_of_rel_iff {Y' : M} (hY : Y ∈ otci ((1 : ℕ) : M))
    (hY' : Y' ∈ otci ((1 : ℕ) : M)) (hnd : ndOf Y = ndOf Y')
    (hodr : ∀ a ∈ ndOf Y, ∀ b ∈ ndOf Y, (a [odrOne Y] b ↔ a [odrOne Y'] b)) : Y = Y' := by
  rw [eq_rtLosSLOT_of_mem_otci_one hY, eq_rtLosSLOT_of_mem_otci_one hY']
  obtain ⟨hR, hs, hne⟩ := rtlosOf_of_mem_otci_one hY
  obtain ⟨hR', hs', hne'⟩ := rtlosOf_of_mem_otci_one hY'
  by_cases h0 : ndOf Y = ∅
  · rw [rtLosSLOT, rtLosSLOT, SLOTreeStructure.ofRtLos, SLOTreeStructure.ofRtLos,
      if_pos (hs.trans h0), if_pos (hs'.trans (hnd ▸ h0))]
  obtain ⟨A, R, hB⟩ := (hne h0).isOrderedPair
  obtain ⟨A', R', hB'⟩ := (hne' (hnd ▸ h0)).isOrderedPair
  have hRR : R = R' := by
    have hR1 : IsStrictLinearOrder R (ndOf Y) := by
      have h := hR
      rwa [hB, losOdr_orderedPair] at h
    have hR1' : IsStrictLinearOrder R' (ndOf Y) := by
      have h := hR'
      rwa [hB', losOdr_orderedPair, ← hnd] at h
    refine hR1.left.left.ext hR1'.left.left fun x y ↦ ?_
    have hiff (hx : x ∈ ndOf Y) (hy : y ∈ ndOf Y) : x [R] y ↔ x [R'] y := by
      have h := hodr x hx y hy
      rwa [odrOne, odrOne, hB, hB', losOdr_orderedPair, losOdr_orderedPair] at h
    constructor
    · intro h
      obtain ⟨hx, hy⟩ := mem_of_rel_of_isRelationOn hR1.left h
      exact (hiff hx hy).mp h
    · intro h
      obtain ⟨hx, hy⟩ := mem_of_rel_of_isRelationOn hR1'.left h
      exact (hiff hx hy).mpr h
  have hAA : A = A' := by
    rw [← losSet_orderedPair (A := A) (R := R), ← hB, hs, hnd, ← hs', hB', losSet_orderedPair]
  rw [hB, hB', hAA, hRR]

open SLOTreeStructure in
/-- The extension of the initial segment `V | (m - 1)` of `V ∈ stduoci_1` with `|V_sig| = m > 0`
has the array of `V` -/
theorem aoc_eq_of_mem_ciExt_iniSeg {V q : M} (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
    (hq : !(iniSeg V (⋃₀ dom (sig V)), q) ∈ ciExt ((1 : ℕ) : M)) : aoc q = aoc V := by
  set k := ⋃₀ dom (sig V) with hkdef
  set U := iniSeg V k with hUdef
  obtain ⟨-, hqs, -, -⟩ := mem_ciExt_props hq
  have hqA := aoc_mem_aotci_of_mem_stduoci_one hqs
  have hVA := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hqf, hqdom, -⟩ := mem_aotci_iff.mp hqA
  obtain ⟨hVf, hVdom, -⟩ := mem_aotci_iff.mp hVA
  obtain ⟨h0, h1⟩ := aoc_val_of_mem_ciExt_one hq
  refine hqf.ext hVf (hqdom.trans hVdom.symm) fun i hi ↦ ?_
  rw [hqdom] at hi
  rcases mem_succ_one_cases hi with rfl | rfl
  · rw [h0, hUdef, aoc_iniSeg, iniSegAoc_val_zero hV]
  -- level `1`
  have hq1 := val_mem_otci_of_mem_aotci hqA (mem_succ_self _)
  have hV1 := val_mem_otci_of_mem_aotci hVA (mem_succ_self _)
  have hRV := isStrictLinearOrder_iniSegOdr hV
  set N := iniSegNds V k with hNdef
  set Y0 := aoc U ﹫ ((1 : ℕ) : M) with hY0def
  have hU1 : U ∈ stduoci ((1 : ℕ) : M) := iniSeg_mem_stduoci hV hm
  have hY0 := val_mem_otci_of_mem_aotci (aoc_mem_aotci_of_mem_stduoci_one hU1) (mem_succ_self _)
  have hY0eq : Y0 = rtLosSLOT trvAZero !(N, iniSegOdr V ↾↾ N) := by
    rw [hY0def, hUdef, aoc_iniSeg, iniSegAoc_val_one hV]
  have hY0nd : ndOf Y0 = N := by rw [hY0eq, ndOf_rtLosSLOT, losSet_orderedPair]
  have hsub := isSubOne_iniSegAoc hV hm
  rw [← aoc_iniSeg, ← hUdef, ← hY0def] at hsub
  set b := sigdcn V k with hbdef
  have hbV : b ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) := (siglvl_eq_one hV hm).right
  have hbN : b ∉ N := fun h ↦ ((mem_iniSegNds_last_iff hV hm).mp h).right rfl
  have hNV : ndOf (aoc V ﹫ ((1 : ℕ) : M)) = insert b N := by
    ext w
    rw [mem_insert_iff, mem_iniSegNds_last_iff hV hm]
    constructor
    · intro hw
      by_cases h : w = b
      · exact .inl h
      · exact .inr ⟨hw, h⟩
    · rintro (rfl | ⟨hw, -⟩)
      · exact hbV
      · exact hw
  have hbeq : b = !(dctUZero, k) := by
    obtain ⟨l, -, hl⟩ := exists_eq_of_mem_otci_one hV1 hbV
    have h := lbl_sigdcn hV hm
    rw [← hbdef, hl, lbl_orderedPair] at h
    rw [hl, h]
  have hsU : dom (sig U) = k := dom_sig_iniSeg hV hm
  by_cases hk0 : k = ∅
  · -- a new root
    have hs : sig U = ∅ := by
      have hsf := (uociCond_of_mem_stduoci_one hU1).right.right.right.left.left
      exact hsf.isRelation.eq_empty_of_dom_eq_empty (hsU.trans hk0)
    rw [if_pos hs] at h1
    have hN0 : N = ∅ := by
      rw [empty_iff]
      intro w hw
      rw [hNdef, mem_iniSegNds_iff, hk0] at hw
      obtain ⟨i, hi, -⟩ := hw
      simp at hi
    have hb0 : b = !(dctUZero, ∅) := by rw [hbeq, hk0]
    have hnd : ndOf (aoc q ﹫ ((1 : ℕ) : M)) = ndOf (aoc V ﹫ ((1 : ℕ) : M)) := by
      rw [h1, hNV, hN0, ← hb0]
      change ((ofM Y0).irmrt b).nd = _
      rw [nd_irmrt]
      change insert b (ndOf Y0) = _
      rw [hY0nd, hN0]
    refine eq_of_mem_otci_one_of_rel_iff hq1 hV1 hnd fun a ha c hc ↦ ?_
    rw [hnd, hNV, hN0, mem_insert_iff] at ha hc
    have ha' : a = b := ha.resolve_right (by simp)
    have hc' : c = b := hc.resolve_right (by simp)
    subst ha' hc'
    exact iff_of_false ((rtlosOf_of_mem_otci_one hq1).left.isIrreflOn.irrefl (hnd ▸ hbV))
      (hRV.isIrreflOn.irrefl hbV)
  -- a new left sibling of the nearest node to the right
  have hs : sig U ≠ ∅ := fun h ↦ hk0 (by rw [← hsU, h, dom_empty])
  rw [if_neg hs] at h1
  obtain ⟨hl1, -, -⟩ := ucf_of_mem_ciExt_one hq hs
  obtain ⟨hucf, -⟩ := ucflvldcn_iniSeg (U := V) hk0
  rw [← hUdef] at hucf
  have hR : iniSegRight V k ≠ ∅ := by
    intro hR
    rw [iniSegUcf, if_pos hR, tpUcfZero] at hucf
    rw [ucflvl, hucf, lvl_orderedPair] at hl1
    exact natCast_one_ne_empty hl1.symm
  obtain ⟨f, hfR, hfmin, hfeq⟩ := iniSegUcf_of_ne_empty hV hm hR
  have hf : ucfdcn U = f := by
    rw [hfeq] at hucf
    rw [ucfdcn, hucf, dcn_orderedPair]
  rw [hf, hsU] at h1
  obtain ⟨hfN, hbf⟩ := mem_iniSegRight_iff.mp hfR
  have hNsub (a : M) (ha : a ∈ N) : a ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) := by
    rw [hNV, mem_insert_iff]
    exact .inr ha
  have hfV := hNsub f hfN
  have hbeq' : !(uc f, k) = b := by rw [uc_eq_dctUZero_of_mem_otci_one hV1 hfV, hbeq]
  rw [hbeq'] at h1
  have hfrt : f ∈ rtOf Y0 := by
    rw [← ndOf_eq_rtOf_of_mem_otci_one hY0, hY0nd]
    exact hfN
  have hbY0 : b ∉ ndOf Y0 := by
    rw [hY0nd]
    exact hbN
  have hkey : left b ﹫ ∅ = trvAZero := by
    rw [hbeq, left_orderedPair, ← natCast_zero, dctUZero_eq_lfTrvUoci]
    exact aoc_lfTrvUoci _
  have hlos := rtlosOf_ilfsblOf_val (isSLOT_of_mem_otci hY0) hfrt hbY0
  rw [hkey, ← h1] at hlos
  obtain ⟨hR0, hA0, -⟩ := rtlosOf_of_mem_otci_one hY0
  obtain ⟨-, hAq, -⟩ := rtlosOf_of_mem_otci_one hq1
  have hodr : odrOne (aoc q ﹫ ((1 : ℕ) : M)) = insertBefore (odrOne Y0) (ndOf Y0) f b := by
    rw [odrOne, hlos, losIlf_eq, losOdr_orderedPair, hA0]
    rfl
  have hnd : ndOf (aoc q ﹫ ((1 : ℕ) : M)) = ndOf (aoc V ﹫ ((1 : ℕ) : M)) := by
    rw [← hAq, hlos, losIlf_eq, losSet_orderedPair, hA0, hY0nd, hNV]
  have hsubr (a c : M) (ha : a ∈ N) (hc : c ∈ N) :
      a [odrOne Y0] c ↔ a [iniSegOdr V] c :=
    hsub.right a (hY0nd ▸ ha) c (hY0nd ▸ hc)
  have hY0rel (a c : M) (h : a [odrOne Y0] c) : a ∈ N ∧ c ∈ N :=
    hY0nd ▸ mem_of_rel_of_isRelationOn hR0.isRelationOn h
  refine eq_of_mem_otci_one_of_rel_iff hq1 hV1 hnd fun x hx y hy ↦ ?_
  rw [hnd, hNV, mem_insert_iff] at hx hy
  rw [hodr, rel_insertBefore_iff, hY0nd]
  change _ ↔ x [iniSegOdr V] y
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · refine iff_of_false ?_ (hRV.isIrreflOn.irrefl hbV)
    rintro (h | ⟨⟨h, -⟩, -⟩ | ⟨-, h | ⟨h, -⟩⟩)
    · exact hbN (hY0rel _ _ h).left
    · exact hbN h
    · exact hbN (h ▸ hfN)
    · exact hbN h
  · constructor
    · rintro (h | ⟨⟨h, -⟩, -⟩ | ⟨-, rfl | ⟨-, h⟩⟩)
      · exact (hbN (hY0rel _ _ h).left).elim
      · exact (hbN h).elim
      · exact hbf
      · exact hRV.isTransOn.trans hbV hfV (hNsub y hy) hbf ((hsubr f y hfN hy).mp h)
    · intro h
      rcases hfmin y (mem_iniSegRight_iff.mpr ⟨hy, h⟩) with rfl | h'
      · exact .inr (.inr ⟨rfl, .inl rfl⟩)
      · exact .inr (.inr ⟨rfl, .inr ⟨hy, (hsubr f y hfN hy).mpr h'⟩⟩)
  · constructor
    · rintro (h | ⟨⟨-, h⟩, -⟩ | ⟨rfl, -⟩)
      · exact (hbN (hY0rel _ _ h).right).elim
      · have hxf := (hsubr x f hx hfN).mp h
        rcases hRV.trichotomous (hNsub x hx) hbV with h' | rfl | h'
        · exact h'
        · exact (hbN hx).elim
        · rcases hfmin x (mem_iniSegRight_iff.mpr ⟨hx, h'⟩) with rfl | h''
          · exact (hRV.isIrreflOn.irrefl hfV hxf).elim
          · exact (hRV.isAsymmOn.asymm hfV (hNsub x hx) h'' hxf).elim
      · exact (hbN hx).elim
    · intro h
      exact .inr (.inl ⟨⟨hx, (hsubr x f hx hfN).mpr
        (hRV.isTransOn.trans (hNsub x hx) hbV hfV h hbf)⟩, rfl⟩)
  · constructor
    · rintro (h | ⟨-, rfl⟩ | ⟨rfl, -⟩)
      · exact (hsubr x y hx hy).mp h
      · exact (hbN hy).elim
      · exact (hbN hx).elim
    · exact fun h ↦ .inl ((hsubr x y hx hy).mpr h)

end RtLosEq

section ExtTree

/-! ### The trees of the extensions of level one; extending embeddings -/

variable {U q : M}

/-- The level-`1` tree of an extension `q` of `U ∈ stduoci_1`: the new node
`b = q_sigdcn(|U_sig|)` is added to that of `U`, which is a subtree, and for nonempty `U_sig` the
node `b` lies immediately before `U_ucfdcn` -/
theorem ext_one_tree (hq : !(U, q) ∈ ciExt ((1 : ℕ) : M)) :
    sigdcn q (dom (sig U)) ∈ ndOf (aoc q ﹫ ((1 : ℕ) : M)) ∧
    ndOf (aoc q ﹫ ((1 : ℕ) : M)) =
      insert (sigdcn q (dom (sig U))) (ndOf (aoc U ﹫ ((1 : ℕ) : M))) ∧
    sigdcn q (dom (sig U)) ∉ ndOf (aoc U ﹫ ((1 : ℕ) : M)) ∧
    IsSubOne (aoc U ﹫ ((1 : ℕ) : M)) (aoc q ﹫ ((1 : ℕ) : M)) ∧
    (sig U ≠ ∅ → (sigdcn q (dom (sig U))) [odrOne (aoc q ﹫ ((1 : ℕ) : M))] (ucfdcn U) ∧
      ∀ z ∈ ndOf (aoc U ﹫ ((1 : ℕ) : M)),
        (sigdcn q (dom (sig U))) [odrOne (aoc q ﹫ ((1 : ℕ) : M))] z →
          z = ucfdcn U ∨ (ucfdcn U) [odrOne (aoc q ﹫ ((1 : ℕ) : M))] z) := by
  obtain ⟨hUs, hqs, -, -⟩ := mem_ciExt_props hq
  have hUA := aoc_mem_aotci_of_mem_stduoci_one hUs
  have hU1 := val_mem_otci_of_mem_aotci hUA (mem_succ_self _)
  have hqA := aoc_mem_aotci_of_mem_stduoci_one hqs
  have hq1 := val_mem_otci_of_mem_aotci hqA (mem_succ_self _)
  have h1 := (aoc_val_of_mem_ciExt_one hq).right
  by_cases hs : sig U = ∅
  · rw [if_pos hs] at h1
    have hU0 : ndOf (aoc U ﹫ ((1 : ℕ) : M)) = ∅ := by
      rw [empty_iff]
      intro w hw
      obtain ⟨hl, -⟩ := sig_val_lbl_of_mem hUs hw
      rw [hs, dom_empty] at hl
      simp at hl
    set b := !((dctUZero : M), (∅ : M)) with hbdef
    have hnd : ndOf (aoc q ﹫ ((1 : ℕ) : M)) = insert b (ndOf (aoc U ﹫ ((1 : ℕ) : M))) := by
      rw [h1]
      change ((SLOTreeStructure.ofM _).irmrt b).nd = _
      rw [SLOTreeStructure.nd_irmrt]
      rfl
    have hbq : b ∈ ndOf (aoc q ﹫ ((1 : ℕ) : M)) := by rw [hnd]; exact mem_insert _ _
    have hsb : sigdcn q (dom (sig U)) = b := by
      have h := sigdcn_lbl_of_mem hqs hbq
      rw [hbdef, lbl_orderedPair, ← dom_empty, ← hs] at h
      rw [h, hs, dom_empty]
    rw [hsb]
    refine ⟨hbq, hnd, by rw [hU0]; simp, ⟨fun z hz ↦ by rw [hU0] at hz; simp at hz,
      fun a ha ↦ by rw [hU0] at ha; simp at ha⟩, fun h ↦ (h hs).elim⟩
  rw [if_neg hs] at h1
  obtain ⟨-, hd, -⟩ := ucf_of_mem_ciExt_one hq hs
  set n := !(uc (ucfdcn U), dom (sig U)) with hn
  have hdrt : ucfdcn U ∈ rtOf (aoc U ﹫ ((1 : ℕ) : M)) := by
    rw [← ndOf_eq_rtOf_of_mem_otci_one hU1]
    exact hd
  have hnN : n ∉ ndOf (aoc U ﹫ ((1 : ℕ) : M)) := by
    intro h
    have hl := (sig_val_lbl_of_mem hUs h).left
    rw [hn, lbl_orderedPair] at hl
    exact notMem_self _ hl
  have hkey : left n ﹫ ∅ = trvAZero := by
    rw [hn, left_orderedPair]
    exact aoc_uc_eq_trvAZero_of_mem_otci_one hU1 hd
  have hlos := rtlosOf_ilfsblOf_val (isSLOT_of_mem_otci hU1) hdrt hnN
  rw [hkey, ← h1] at hlos
  obtain ⟨hR, hA, -⟩ := rtlosOf_of_mem_otci_one hU1
  obtain ⟨-, hA', -⟩ := rtlosOf_of_mem_otci_one hq1
  have hodr : odrOne (aoc q ﹫ ((1 : ℕ) : M)) =
      insertBefore (odrOne (aoc U ﹫ ((1 : ℕ) : M)))
        (ndOf (aoc U ﹫ ((1 : ℕ) : M))) (ucfdcn U) n := by
    rw [odrOne, hlos, losIlf_eq, losOdr_orderedPair, hA]
    rfl
  have hnd' : ndOf (aoc q ﹫ ((1 : ℕ) : M)) = insert n (ndOf (aoc U ﹫ ((1 : ℕ) : M))) := by
    rw [← hA', hlos, losIlf_eq, losSet_orderedPair, hA]
  have hnC : n ∈ ndOf (aoc q ﹫ ((1 : ℕ) : M)) := by
    rw [hnd']
    exact mem_insert _ _
  have hsn : sigdcn q (dom (sig U)) = n := by
    have h := sigdcn_lbl_of_mem hqs hnC
    rwa [hn, lbl_orderedPair] at h
  have hRo : IsStrictLinearOrder (odrOne (aoc U ﹫ ((1 : ℕ) : M)))
      (ndOf (aoc U ﹫ ((1 : ℕ) : M))) := hR
  rw [hsn]
  refine ⟨hnC, hnd', hnN, ⟨fun z hz ↦ by rw [hnd', mem_insert_iff]; exact .inr hz,
    fun a ha b hb ↦ ?_⟩, fun _ ↦ ⟨?_, fun z hz hnz ↦ ?_⟩⟩
  · rw [hodr, rel_insertBefore_iff]
    constructor
    · exact fun h ↦ .inl h
    · rintro (h | ⟨-, rfl⟩ | ⟨rfl, -⟩)
      · exact h
      · exact (hnN hb).elim
      · exact (hnN ha).elim
  · rw [hodr, rel_insertBefore_iff]
    exact Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)
  · rw [hodr, rel_insertBefore_iff] at hnz
    rw [hodr, rel_insertBefore_iff]
    rcases hnz with h | ⟨⟨h, -⟩, -⟩ | ⟨-, h | ⟨-, h⟩⟩
    · exact (hnN (hRo.mem_left h)).elim
    · exact (hnN h).elim
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- The signature of an extension `q` of `U ∈ stduoci_1` has length `|U_sig| + 1` -/
theorem dom_sig_of_mem_ciExt_one (hq : !(U, q) ∈ ciExt ((1 : ℕ) : M)) :
    dom (sig q) = succ (dom (sig U)) ∧ ⋃₀ dom (sig q) = dom (sig U) ∧
      dom (sig U) ∈ dom (sig q) ∧ sig q ↾ dom (sig U) = sig U := by
  obtain ⟨hUs, -, -, -⟩ := mem_ciExt_props hq
  obtain ⟨e, he⟩ := exists_sig_eq_cc_of_mem_ciExt (natCast_mem_omega 1) hq
  have hsU := (uociCond_of_mem_stduoci_one hUs).right.right.right.left.left
  have hdω := dom_sig_mem_omega_of_mem_stduoci_one hUs
  have hd : dom (sig q) = succ (dom (sig U)) := by rw [he, dom_cc]
  refine ⟨hd, by rw [hd, sUnion_succ (ordinal_of_mem ordinal_omega hdω).transitive],
    by rw [hd]; exact mem_succ_self _, ?_⟩
  rw [he]
  refine ((hsU.cc e).restrict _).ext hsU (dom_restrict_of_subset (hsU.cc e)
    (by rw [dom_cc]; exact fun _ h ↦ mem_succ_of_mem h)) fun i hi ↦ ?_
  rw [dom_restrict_of_subset (hsU.cc e) (by rw [dom_cc]; exact fun _ h ↦ mem_succ_of_mem h)] at hi
  rw [val_restrict _ (hsU.cc e) hi (by rw [dom_cc]; exact mem_succ_of_mem hi),
    cc_val_of_mem hsU e hi]

/-- The initial segment of an extension `q` of `U` cut at `|U_sig|` has the array of `U` -/
theorem iniSegAoc_eq_of_mem_ciExt_one (hq : !(U, q) ∈ ciExt ((1 : ℕ) : M)) :
    iniSegAoc q (dom (sig U)) = aoc U := by
  obtain ⟨hUs, hqs, -, -⟩ := mem_ciExt_props hq
  obtain ⟨-, hsU, hn, -⟩ := dom_sig_of_mem_ciExt_one hq
  obtain ⟨hb, hnd, hbU, hsub, -⟩ := ext_one_tree hq
  have hm : ⋃₀ dom (sig q) ∈ dom (sig q) := by rw [hsU]; exact hn
  have hIA := (mem_finaotci_iff.mp (iniSegAoc_mem_finaotci hqs hn)).left
  have hUA := aoc_mem_aotci_of_mem_stduoci_one hUs
  obtain ⟨hIf, hIdom, -⟩ := mem_aotci_iff.mp hIA
  obtain ⟨hUf, hUdom, -⟩ := mem_aotci_iff.mp hUA
  refine hIf.ext hUf (hIdom.trans hUdom.symm) fun i hi ↦ ?_
  rw [hIdom] at hi
  rcases mem_succ_one_cases hi with rfl | rfl
  · rw [iniSegAoc_val_zero hqs, (aoc_val_of_mem_ciExt_one hq).left]
  have hT := iniSegTree_mem_otci hqs hn
  have hU1 := val_mem_otci_of_mem_aotci hUA (mem_succ_self _)
  have hNiff (w : M) : w ∈ iniSegNds q (dom (sig U)) ↔ w ∈ ndOf (aoc U ﹫ ((1 : ℕ) : M)) := by
    have h := mem_iniSegNds_last_iff (w := w) hqs hm
    rw [hsU] at h
    rw [h, hnd, mem_insert_iff]
    constructor
    · rintro ⟨h' | h', hne⟩
      · exact (hne h').elim
      · exact h'
    · intro h'
      exact ⟨.inr h', fun he ↦ hbU (he ▸ h')⟩
  have hsubI := isSubOne_iniSegAoc hqs hm
  rw [hsU, iniSegAoc_val_one hqs] at hsubI
  rw [iniSegAoc_val_one hqs]
  have hndT : ndOf (rtLosSLOT trvAZero !(iniSegNds q (dom (sig U)),
      iniSegOdr q ↾↾ iniSegNds q (dom (sig U)))) = ndOf (aoc U ﹫ ((1 : ℕ) : M)) := by
    ext w
    rw [ndOf_rtLosSLOT, losSet_orderedPair, hNiff]
  refine eq_of_mem_otci_one_of_rel_iff hT hU1 hndT fun a ha c hc ↦ ?_
  rw [hsubI.right a ha c hc]
  rw [hndT] at ha hc
  exact (hsub.right a ha c hc).symm

/-- The initial segment of an extension `q` of `U` cut at `|U_sig|` is `U` -/
theorem iniSeg_eq_of_mem_ciExt_one (hq : !(U, q) ∈ ciExt ((1 : ℕ) : M)) :
    iniSeg q (dom (sig U)) = U := by
  obtain ⟨hUs, hqs, hUd, -⟩ := mem_ciExt_props hq
  obtain ⟨-, hsU, hn, hres⟩ := dom_sig_of_mem_ciExt_one hq
  have hA := iniSegAoc_eq_of_mem_ciExt_one hq
  have hUf := (uociCond_of_mem_stduoci_one hUs).left
  by_cases hs : sig U = ∅
  · have hn0 : dom (sig U) = ∅ := by rw [hs, dom_empty]
    have h3 : dom U = ((3 : ℕ) : M) :=
      (uociCond_of_mem_stduoci_one hUs).right.right.right.right.right.right.left.mpr
        (.inl ⟨hs, isOdd_one⟩)
    rw [iniSeg, if_pos hn0, hA, hres]
    conv_rhs => rw [eq_ciTriple hUf h3]
    rw [hUd]
  obtain ⟨h5, hlf, -, -⟩ := ucf_props_of_mem_stduoci_one hUs hUd hs
  obtain ⟨hl1, hfd, hpair⟩ := ucf_of_mem_ciExt_one hq hs
  have hn0 : dom (sig U) ≠ ∅ := fun h ↦ hs
    (((uociCond_of_mem_stduoci_one hUs).right.right.right.left.left.isRelation
      ).eq_empty_of_dom_eq_empty h)
  obtain ⟨hb, hnd, hbU, hsub, hnear⟩ := ext_one_tree hq
  obtain ⟨hblt, hbmin⟩ := hnear hs
  have hm : ⋃₀ dom (sig q) ∈ dom (sig q) := by rw [hsU]; exact hn
  have hq1 := val_mem_otci_of_mem_aotci (aoc_mem_aotci_of_mem_stduoci_one hqs) (mem_succ_self _)
  have hRq := (rtlosOf_of_mem_otci_one hq1).left
  have hfN : ucfdcn U ∈ iniSegNds q (dom (sig U)) := by
    have h := mem_iniSegNds_last_iff (w := ucfdcn U) hqs hm
    rw [hsU] at h
    rw [h, hnd, mem_insert_iff]
    exact ⟨.inr hfd, fun he ↦ hbU (he ▸ hfd)⟩
  have hfR : ucfdcn U ∈ iniSegRight q (dom (sig U)) := mem_iniSegRight_iff.mpr ⟨hfN, hblt⟩
  have hR : iniSegRight q (dom (sig U)) ≠ ∅ := fun h ↦ by rw [h] at hfR; simp at hfR
  obtain ⟨w, hwR, hwmin, hw⟩ := iniSegUcf_of_ne_empty hqs hn hR
  have hwf : w = ucfdcn U := by
    obtain ⟨hwN, hbw⟩ := mem_iniSegRight_iff.mp hwR
    have hwU : w ∈ ndOf (aoc U ﹫ ((1 : ℕ) : M)) := by
      have h := mem_iniSegNds_last_iff (w := w) hqs hm
      rw [hsU, hnd, mem_insert_iff] at h
      rcases (h.mp hwN) with ⟨h' | h', hne⟩
      · exact (hne h').elim
      · exact h'
    rcases hwmin _ hfR with h | h
    · exact h.symm
    · rcases hbmin w hwU hbw with h' | h'
      · exact h'
      · exact (hRq.isAsymmOn.asymm (hRq.mem_left h) (hRq.mem_left h') h h').elim
  rw [iniSeg, if_neg hn0, hA, hres, hw, hwf]
  conv_rhs => rw [eq_ciQuint hUf h5]
  rw [hUd, hlf, hpair]

/-- Extending an embedding of `A` to `A'`, which has the one new level-`1` node `s`, by `s ↦ D` -/
theorem embExt_mem_aotciEmbSet {A A' B h s D : M} (hA : A ∈ aotci ((1 : ℕ) : M))
    (hA' : A' ∈ aotci ((1 : ℕ) : M)) (hB : B ∈ aotci ((1 : ℕ) : M)) (h0 : A' ﹫ ∅ = A ﹫ ∅)
    (hsub : IsSubOne (A ﹫ ((1 : ℕ) : M)) (A' ﹫ ((1 : ℕ) : M)))
    (hnd : ndOf (A' ﹫ ((1 : ℕ) : M)) = insert s (ndOf (A ﹫ ((1 : ℕ) : M))))
    (hs : s ∉ ndOf (A ﹫ ((1 : ℕ) : M))) (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) A B)
    (hD : D ∈ ndOf (B ﹫ ((1 : ℕ) : M)))
    (hlt : ∀ z ∈ ndOf (A ﹫ ((1 : ℕ) : M)), z [odrOne (A' ﹫ ((1 : ℕ) : M))] s →
      ((h ﹫ ((1 : ℕ) : M)) ﹫ z) [odrOne (B ﹫ ((1 : ℕ) : M))] D)
    (hgt : ∀ z ∈ ndOf (A ﹫ ((1 : ℕ) : M)), s [odrOne (A' ﹫ ((1 : ℕ) : M))] z →
      D [odrOne (B ﹫ ((1 : ℕ) : M))] ((h ﹫ ((1 : ℕ) : M)) ﹫ z)) :
    cc (h ↾ ((1 : ℕ) : M)) (update (h ﹫ ((1 : ℕ) : M)) s D) ∈
      aotciEmbSet ((1 : ℕ) : M) A' B := by
  obtain ⟨hA'f, hA'dom, -⟩ := mem_aotci_iff.mp hA'
  obtain ⟨hBf, hBdom, -⟩ := mem_aotci_iff.mp hB
  have he := (mem_aotciEmbSet_iff.mp hh).right
  have h1s : ((1 : ℕ) : M) ∈ succ ((1 : ℕ) : M) := mem_succ_self _
  have h12 : ((1 : ℕ) : M) ⊆ dom h := by
    rw [he.dom_eq]
    exact fun _ hz ↦ mem_succ_of_mem hz
  have hhr : IsFunction (h ↾ ((1 : ℕ) : M)) := he.isFunction.restrict _
  have hhrdom : dom (h ↾ ((1 : ℕ) : M)) = ((1 : ℕ) : M) := dom_restrict_of_subset he.isFunction h12
  have hv0 : cc (h ↾ ((1 : ℕ) : M)) (update (h ﹫ ((1 : ℕ) : M)) s D) ﹫ ∅ = h ﹫ ∅ := by
    rw [cc_val_of_mem hhr _ (by rw [hhrdom]; exact empty_mem_natCast_one),
      val_restrict _ he.isFunction empty_mem_natCast_one (h12 empty_mem_natCast_one)]
  have hv1 : cc (h ↾ ((1 : ℕ) : M)) (update (h ﹫ ((1 : ℕ) : M)) s D) ﹫ ((1 : ℕ) : M) =
      update (h ﹫ ((1 : ℕ) : M)) s D := by
    have h' := cc_val_self hhr (update (h ﹫ ((1 : ℕ) : M)) s D)
    rwa [hhrdom] at h'
  refine mem_aotciEmbSet_of_isAotciEmbedding hA'f hA'dom hBf hBdom
    ⟨hhr.cc _, by rw [dom_cc, hhrdom], fun {i} hi ↦ ?_⟩
  rcases mem_succ_one_cases hi with rfl | rfl
  · rw [hv0, h0]
    exact he.isOtciEmbedding hi
  rw [hv1]
  have hA1 := val_mem_otci_of_mem_aotci hA h1s
  have hA'1 := val_mem_otci_of_mem_aotci hA' h1s
  have hB1 := val_mem_otci_of_mem_aotci hB h1s
  obtain ⟨hinj, hodr⟩ := (isOtciEmbedding_iff_of_mem_otci_one hA1 hB1).mp (he.isOtciEmbedding h1s)
  have hRA' := (rtlosOf_of_mem_otci_one hA'1).left
  have hRB := (rtlosOf_of_mem_otci_one hB1).left
  have hf := hinj.isFunction
  have hfdom := hinj.isFunctionFromTo.dom_eq
  have hval {a : M} (ha : a ∈ ndOf (A ﹫ ((1 : ℕ) : M))) :
      update (h ﹫ ((1 : ℕ) : M)) s D ﹫ a = (h ﹫ ((1 : ℕ) : M)) ﹫ a :=
    val_update_of_ne hf _ (by rw [hfdom]; exact ha) fun he' ↦ hs (he' ▸ ha)
  have hvals : update (h ﹫ ((1 : ℕ) : M)) s D ﹫ s = D := val_update_self hf _ _
  have hsA' : s ∈ ndOf (A' ﹫ ((1 : ℕ) : M)) := by rw [hnd]; exact mem_insert _ _
  have hneD {a : M} (ha : a ∈ ndOf (A ﹫ ((1 : ℕ) : M))) : D ≠ (h ﹫ ((1 : ℕ) : M)) ﹫ a := by
    intro hDa
    rcases hRA'.trichotomous (hsub.left ha) hsA' with h' | h' | h'
    · have := hlt a ha h'
      rw [← hDa] at this
      exact hRB.isIrreflOn.irrefl hD this
    · exact hs (h' ▸ ha)
    · have := hgt a ha h'
      rw [← hDa] at this
      exact hRB.isIrreflOn.irrefl hD this
  have hcases {a : M} (ha : a ∈ ndOf (A' ﹫ ((1 : ℕ) : M))) :
      a = s ∨ a ∈ ndOf (A ﹫ ((1 : ℕ) : M)) := by
    rw [hnd, mem_insert_iff] at ha
    exact ha
  rw [isOtciEmbedding_iff_of_mem_otci_one hA'1 hB1]
  refine ⟨isInjectionFromTo_of_val (hf.update _ _) ?_ (fun a ha ↦ ?_) fun a ha b hb hab ↦ ?_,
    fun a ha b hb hab ↦ ?_⟩
  · rw [dom_update, hfdom, hnd]
  · rcases hcases ha with rfl | ha
    · rw [hvals]
      exact hD
    · rw [hval ha]
      exact hinj.isFunctionFromTo.val_mem ha
  · rcases hcases ha with rfl | ha <;> rcases hcases hb with rfl | hb
    · rfl
    · rw [hvals, hval hb] at hab
      exact (hneD hb hab).elim
    · rw [hvals, hval ha] at hab
      exact (hneD ha hab.symm).elim
    · rw [hval ha, hval hb] at hab
      exact hinj.right ha hb hab
  · rcases hcases ha with rfl | ha <;> rcases hcases hb with rfl | hb
    · exact (hRA'.isIrreflOn.irrefl hsA' hab).elim
    · rw [hvals, hval hb]
      exact hgt b hb hab
    · rw [hvals, hval ha]
      exact hlt a ha hab
    · rw [hval ha, hval hb]
      exact hodr a ha b hb ((hsub.right a ha b hb).mpr hab)

end ExtTree

section SuccCases

/-! ### The least new node with a given nearest old node above it -/

variable {Q V q h k a : M}

/-- If `a` is the least node of `(Q ⊗ X')(1)` above the new node `y = (q, h)`, it is the prefix
candidate `succOne` or the replacement candidate `succTwo` -/
theorem eq_succ_of_isLeastAbove (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hq : q ∈ ndOf (Q ﹫ 2))
    (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)))
    (hk : k ∈ depOf (Q ﹫ 2) q)
    (hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V)))
    (hje : sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V)))
    (ha : a ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
    (hya : !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] a)
    (hamin : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
      !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
        z = a ∨ a [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) :
    ∃ w ∈ iniSegRight V (⋃₀ dom (sig V)),
      (∀ r ∈ iniSegRight V (⋃₀ dom (sig V)), r = w ∨ w [iniSegOdr V] r) ∧
      ((k ≠ ∅ ∧ (h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) q k)) =
          relabelOne trvAZero w ∧ a = succOne (Q ﹫ 2) q h k) ∨
        ((k ≠ ∅ → relabelOne trvAZero w ≠
            (h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) q k))) ∧
          a = succTwo (Q ﹫ 2) q h k (relabelOne trvAZero w))) := by
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  obtain ⟨hX', h0, hsub, -⟩ := lastSeg_facts hV hm
  have hB1 := val_mem_otci_of_mem_aotci (tensorProdATwoAOne_mem_aotci hQ hX) (mem_succ_self _)
  have hO := (rtlosOf_of_mem_otci_one hB1).left
  have hksig : k ∈ dom (sig (uc q)) := by
    rw [dom_sig_uc_eq_depOf (val_mem_otci_of_mem_aotci hQ (mem_succ_self _)) hq]; exact hk
  have hR1 : IsStrictLinearOrder (odrOne (aoc V ﹫ ((1 : ℕ) : M))) (ndOf (aoc V ﹫ ((1 : ℕ) : M))) :=
    (rtlosOf_of_mem_otci_one hX1).left
  have hN (z : M) (hz : z ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V)))) :
      z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) :=
    (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX').mpr (.inr hz)
  have hCX (z : M) (hz : z ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V)))) :
      z ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) :=
    ((mem_tensorProdTwoAOneNds_iff_of_isSubOne hQ hX hX' h0 hsub).mp hz).left
  have heq {E : M} (hE : E ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫
      ((1 : ℕ) : M)))
      (hmin : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
        !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
          z = E ∨ E [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z)
      (hlt : !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] E) :
      a = E := by
    rcases hmin a ha hya with h' | h'
    · exact h'
    rcases hamin E hE hlt with h'' | h''
    · exact h''.symm
    exact (hO.isAsymmOn.asymm (hO.mem_left h') (hO.mem_right h') h' h'').elim
  have hR : iniSegRight V (⋃₀ dom (sig V)) ≠ ∅ := by
    intro hR
    have hk0 : k = ∅ := by
      by_contra hk0
      obtain ⟨-, -, w, hw, -⟩ := ucf_ancOf_facts hQ hV hm hq hh hk hk0 hje
      rw [hR] at hw
      exact notin_empty _ hw
    subst hk0
    exact not_rel_of_succ_none hQ hV hm hq hy hh hk hje hR ha hya
  obtain ⟨w, hwR, hwl, -⟩ := iniSegUcf_of_ne_empty hV hm hR
  have hwX : w ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) :=
    ((mem_iniSegNds_last_iff hV hm).mp (mem_iniSegRight_iff.mp hwR).left).left
  refine ⟨w, hwR, hwl, ?_⟩
  by_cases hc : k ≠ ∅ ∧ (h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) q k)) =
      relabelOne trvAZero w
  · obtain ⟨hk0, hrw⟩ := hc
    have hE := succOne_mem hQ hV hm hq hh hksig hk0 hfirst
    have hlt := rel_succOne hQ hV hm hq hy hh hk hk0 hfirst
    have hnone : ∀ w' ∈ iniSegRight V (⋃₀ dom (sig V)),
        ¬ (relabelOne trvAZero w') [odrOne (tensorProdTwoAOneTgt (aoc V) ﹫ ((1 : ℕ) : M))]
          ((h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) q k))) := fun w' hw' hlt' ↦ by
      have hw'X := ((mem_iniSegNds_last_iff hV hm).mp (mem_iniSegRight_iff.mp hw').left).left
      rw [hrw, tensorProdTwoAOneTgt_val_one, rel_odrOne_tensorProdOneAZero_iff hX1 hw'X hwX] at hlt'
      rcases hwl w' hw' with h' | h'
      · rw [h'] at hlt'
        exact hR1.irrefl _ hlt'
      · exact hR1.asymm h' hlt'
    exact .inl ⟨hk0, hrw, heq (hN _ hE) (fun z hz hyz ↦
      succOne_min hQ hV hm hq hy hh hk hk0 hje hnone (hCX _ hE) hz hyz) hlt⟩
  · have hne : k ≠ ∅ → relabelOne trvAZero w ≠
        (h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) q k)) := fun hk0 h' ↦ hc ⟨hk0, h'.symm⟩
    have hE := succTwo_mem hQ hV hm hq hh hk hwR hwl hne hfirst hje
    obtain ⟨hlt, -⟩ := rel_succTwo hQ hV hm hq hy hh hk hwR hwl hne hfirst hje
    exact .inr ⟨hne, heq (hN _ hE) (fun z hz hyz ↦
      succTwo_min hQ hV hm hq hy hh hk hje hwR hwl (hCX _ hE) hz hyz) hlt⟩

/-- Comparing two nodes `y = (q, h)`, `y' = (q', h')` of `Q(2) ⊗ X` whose sequences agree before
`k`, with the same image at `k`, where `q` has depth `k + 1`, is childless, and is at most the
ancestor of `q'` of depth `k + 1` in the sibling order: `y ≤ y'` -/
theorem eq_or_rel_of_seq_prefix {X q h q' h' k : M} (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hX : X ∈ aotci ((1 : ℕ) : M))
    (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) X)
    (hy' : !(dctUZero, !(q', h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) X)
    (hq : q ∈ ndOf (Q ﹫ 2)) (hq' : q' ∈ ndOf (Q ﹫ 2))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt X))
    (hh' : h' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q')) (tensorProdTwoAOneTgt X))
    (hdq : depOf (Q ﹫ 2) q = succ k) (hk' : k ∈ depOf (Q ﹫ 2) q')
    (hpre : ∀ i ∈ k, tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h) ﹫ i =
      tensorProdTwoAOneSeq (Q ﹫ 2) !(q', h') ﹫ i)
    (himg : (h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) k = (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q') k)
    (hchd : chdOf (Q ﹫ 2) q = ∅)
    (hsbl : q = ancOf (Q ﹫ 2) q' (succ k) ∨ q [sblOdrOf (Q ﹫ 2)] ancOf (Q ﹫ 2) q' (succ k)) :
    !(dctUZero, !(q, h)) = !(dctUZero, !(q', h')) ∨
      !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M))]
        !(dctUZero, !(q', h')) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  have hT := tensorProdTwoAOneTgt_mem hX
  have hdq' := hTS.dep_mem_omega hq'
  have hkq : k ∈ depOf (Q ﹫ 2) q := by rw [hdq]; exact mem_succ_self k
  have hsf := isFunction_tensorProdTwoAOneSeq (Q ﹫ (2 : M)) !(q, h)
  have hsf' := isFunction_tensorProdTwoAOneSeq (Q ﹫ (2 : M)) !(q', h')
  have hres : tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h) ↾ k =
      tensorProdTwoAOneSeq (Q ﹫ 2) !(q', h') ↾ k := by
    have hks : k ⊆ dom (tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h)) := by
      rw [tensorProdTwoAOneSeq_dom, hdq]
      exact fun _ h' ↦ mem_succ_of_mem h'
    have hks' : k ⊆ dom (tensorProdTwoAOneSeq (Q ﹫ 2) !(q', h')) := by
      rw [tensorProdTwoAOneSeq_dom]
      exact (ordinal_of_mem ordinal_omega hdq').transitive _ hk'
    refine (hsf.restrict _).ext (hsf'.restrict _)
      (by rw [dom_restrict_of_subset hsf hks, dom_restrict_of_subset hsf' hks']) fun i hi ↦ ?_
    rw [dom_restrict_of_subset hsf hks] at hi
    rw [val_restrict _ hsf hi (hks hi), val_restrict _ hsf' hi (hks' hi), hpre i hi]
  rcases hsbl with heq | hlt
  · -- `q'` lies below the childless `q`, so it is `q`
    have hqq : q' = q := by
      by_contra hne
      have hlt' : succ k ∈ depOf (Q ﹫ 2) q' := by
        rcases mem_or_eq_of_mem_succ (succ_mem_succ_of_mem hdq' hk') with h' | h'
        · exact h'
        · exfalso
          apply hne
          rw [heq, h']
          exact (hTS.anc_dep hq').symm
      have hc := hTS.anc_succ_mem_chd hq' hlt'
      change ancOf (Q ﹫ 2) q' (succ (succ k)) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q' (succ k)) at hc
      rw [← heq, hchd] at hc
      simp at hc
    subst hqq
    left
    have hkq' : k ∈ depOf (Q ﹫ 2) q' := hk'
    have hseq : tensorProdTwoAOneSeq (Q ﹫ 2) !(q', h) = tensorProdTwoAOneSeq (Q ﹫ 2) !(q', h') := by
      refine hsf.ext hsf' (by rw [tensorProdTwoAOneSeq_dom, tensorProdTwoAOneSeq_dom]) fun i hi ↦ ?_
      rw [tensorProdTwoAOneSeq_dom, hdq] at hi
      rcases mem_or_eq_of_mem_succ hi with hi | rfl
      · exact hpre i hi
      · rw [tensorProdTwoAOneSeq_val hQ2 hq hkq', tensorProdTwoAOneSeq_val hQ2 hq hkq', himg]
    rw [eq_of_tensorProdTwoAOneSeq_eq hQ2 hT hq hq hh hh' hseq]
  · right
    rw [rel_odrOne_tensorProdATwoAOne_iff_of_mem hQ hX hy, lbl_orderedPair, lbl_orderedPair]
    refine ⟨hy', .inr ⟨k, by rw [tensorProdTwoAOneSeq_dom]; exact hkq,
      by rw [tensorProdTwoAOneSeq_dom]; exact hk', hres, ?_⟩⟩
    have hm1 := tensorProdTwoAOneSeq_val_mem hQ2 hq hh hkq
    have hm2 := tensorProdTwoAOneSeq_val_mem hQ2 hq' hh' hk'
    rw [tensorProdTwoAOneSeq_val hQ2 hq hkq] at hm1 ⊢
    rw [tensorProdTwoAOneSeq_val hQ2 hq' hk'] at hm2 ⊢
    rw [pair_mem_sprod_iff] at hm1 hm2
    rw [tensorProdTwoAOneCoordOdr, rel_lexProd_iff]
    have hqa : ancOf (Q ﹫ 2) q (succ k) = q := by rw [← hdq]; exact hTS.anc_dep hq
    rw [hqa] at hm1 ⊢
    exact ⟨hm1, hm2, .inr ⟨himg, hlt⟩⟩

end SuccCases

section YStarHelp

variable {V w : M}

/-- The relabelled order of the level-`1` nodes in `X ⊗ Z` -/
theorem rel_tgt_relabel_iff {X z z' : M} (hX : X ∈ aotci ((1 : ℕ) : M))
    (hz : z ∈ ndOf (X ﹫ ((1 : ℕ) : M))) (hz' : z' ∈ ndOf (X ﹫ ((1 : ℕ) : M))) :
    (relabelOne trvAZero z) [odrOne (tensorProdTwoAOneTgt X ﹫ ((1 : ℕ) : M))]
      (relabelOne trvAZero z') ↔ z [odrOne (X ﹫ ((1 : ℕ) : M))] z' := by
  rw [tensorProdTwoAOneTgt_val_one,
    rel_odrOne_tensorProdOneAZero_iff (val_mem_otci_of_mem_aotci hX (mem_succ_self _)) hz hz']

/-- The new node `e` lies before its nearest right neighbour `w`, and an old node before `w` is
before `e` -/
theorem new_lt_nearest (hV : V ∈ stduoci ((1 : ℕ) : M)) (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
    (hwR : w ∈ iniSegRight V (⋃₀ dom (sig V)))
    (hwl : ∀ r ∈ iniSegRight V (⋃₀ dom (sig V)), r = w ∨ w [iniSegOdr V] r) :
    (sigdcn V (⋃₀ dom (sig V))) [odrOne (aoc V ﹫ ((1 : ℕ) : M))] w ∧
      w ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)) ∧
      ∀ z ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)),
        z [odrOne (aoc V ﹫ ((1 : ℕ) : M))] w →
          z [odrOne (aoc V ﹫ ((1 : ℕ) : M))] (sigdcn V (⋃₀ dom (sig V))) := by
  obtain ⟨-, -, -, hnd'⟩ := lastSeg_facts hV hm
  have hX1 := val_mem_otci_of_mem_aotci (aoc_mem_aotci_of_mem_stduoci_one hV) (mem_succ_self _)
  have hR := (rtlosOf_of_mem_otci_one hX1).left
  obtain ⟨hwN, hew⟩ := mem_iniSegRight_iff.mp hwR
  have heX := (siglvl_eq_one hV hm).right
  refine ⟨hew, by rw [hnd']; exact (mem_iniSegNds_last_iff hV hm).mp hwN, fun z hz hzw ↦ ?_⟩
  obtain ⟨hzX, hze⟩ := (hnd' z).mp hz
  rcases hR.trichotomous hzX heX with h | h | h
  · exact h
  · exact (hze h).elim
  · have hzR : z ∈ iniSegRight V (⋃₀ dom (sig V)) :=
      mem_iniSegRight_iff.mpr ⟨(mem_iniSegNds_last_iff hV hm).mpr ⟨hzX, hze⟩, h⟩
    rcases hwl z hzR with h' | h'
    · rw [h'] at hzw
      exact (hR.isIrreflOn.irrefl (hR.mem_left hzw) hzw).elim
    · exact (hR.isAsymmOn.asymm (hR.mem_left h') (hR.mem_right h') h' hzw).elim

end YStarHelp

theorem ancOf_eq_of_mem_chdOf {P p c : M} (hP : IsSLOT P) (hc : c ∈ chdOf P p) :
    depOf P c = succ (depOf P p) ∧ ancOf P c (depOf P p) = p := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hP
  have hTS := hS.isTreeStructure
  have hp := hTS.mem_nd_of_mem_chd_val hc
  have hcn := mem_ndOf_of_mem_chdOf hP hc
  have hdc : depOf P c = succ (depOf P p) := hTS.dep_of_mem_chd p hp c hc
  refine ⟨hdc, ?_⟩
  have hk : depOf P p ∈ depOf P c := by rw [hdc]; exact mem_succ_self _
  have h' := hTS.anc_succ_mem_chd hcn hk
  change ancOf P c (succ (depOf P p)) ∈ chdOf P (ancOf P c (depOf P p)) at h'
  rw [← hdc] at h'
  have hcc : ancOf P c (depOf P c) = c := hTS.anc_dep hcn
  rw [hcc] at h'
  rw [← prtOf_eq_of_mem_chdOf hP h', prtOf_eq_of_mem_chdOf hP hc]

/-- A continuous child is the continuous child with its key -/
theorem eq_ctChd_of_ctp_eq_ct {n T p c : M} (hn : n ∈ (ω : M)) (hn0 : n ≠ ∅) (hT : T ∈ otci n)
    (hp : p ∈ ndOf T) (hc : c ∈ chdOf T p) (hct : ctp (uc c) = ct) :
    ctChd T p (aoc (uc c)) = c := by
  have hTs : IsSLOT T := isSLOT_of_mem_otci hT
  obtain ⟨hc', hk', -, -, -, hmin⟩ := ctChd_spec hn hn0 hT hp hc
  rcases hmin c hc rfl with h | h
  · exact h.symm
  exfalso
  obtain ⟨hmω, hmn, -⟩ := sUnion_mem_of_ne_empty hn hn0
  have hT' := hT
  rw [mem_otci_iff_of_ne_empty hn0] at hT'
  obtain ⟨-, -, -, -, hchd⟩ := hT'
  obtain ⟨q, hq, hqk⟩ := ((hchd p hp).left (aoc (uc c))).mp ⟨c, hc, rfl⟩
  have hkey : aoc q = left c ﹫ ∅ := hqk
  have hmemB (x : M) : x ∈ losSet (chdlosOf T p ﹫ aoc q) ↔
      x ∈ chdOf T p ∧ aoc (uc x) = aoc (uc c) := by
    rw [hkey]
    exact mem_losSet_chdlosOf_iff hTs hp hc x
  have hcB : c ∈ losSet (chdlosOf T p ﹫ aoc q) := (hmemB c).mpr ⟨hc, rfl⟩
  have hc'B : ctChd T p (aoc (uc c)) ∈ losSet (chdlosOf T p ﹫ aoc q) := (hmemB _).mpr ⟨hc', hk'⟩
  have hl := ((hchd p hp).right.left q hq c hcB).right.mpr hct
  rw [rel_sblOdrOf_iff hTs] at h
  obtain ⟨-, -, -, hrel⟩ := h
  have hl1 : ndlosOf T (ctChd T p (aoc (uc c))) = chdlosOf T p ﹫ aoc q := by
    rw [ndlosOf_eq_chdlosOf hTs hp hc', hkey]
    change chdlosOf T p ﹫ aoc (uc (ctChd T p (aoc (uc c)))) = chdlosOf T p ﹫ aoc (uc c)
    rw [hk']
  rw [hl1] at hrel
  exact hl.right _ hc'B hrel

/-- Replacing the value of an embedding at the level-`1` node `u` by `D`, in the same place of the
order -/
theorem embRep_mem_aotciEmbSet {A B h u D : M} (hA : A ∈ aotci ((1 : ℕ) : M))
    (hB : B ∈ aotci ((1 : ℕ) : M)) (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) A B)
    (hu : u ∈ ndOf (A ﹫ ((1 : ℕ) : M))) (hD : D ∈ ndOf (B ﹫ ((1 : ℕ) : M)))
    (hlt : ∀ z ∈ ndOf (A ﹫ ((1 : ℕ) : M)), z [odrOne (A ﹫ ((1 : ℕ) : M))] u →
      ((h ﹫ ((1 : ℕ) : M)) ﹫ z) [odrOne (B ﹫ ((1 : ℕ) : M))] D)
    (hgt : ∀ z ∈ ndOf (A ﹫ ((1 : ℕ) : M)), u [odrOne (A ﹫ ((1 : ℕ) : M))] z →
      D [odrOne (B ﹫ ((1 : ℕ) : M))] ((h ﹫ ((1 : ℕ) : M)) ﹫ z)) :
    cc (h ↾ ((1 : ℕ) : M)) (update (h ﹫ ((1 : ℕ) : M)) u D) ∈
      aotciEmbSet ((1 : ℕ) : M) A B := by
  obtain ⟨hAf, hAdom, -⟩ := mem_aotci_iff.mp hA
  obtain ⟨hBf, hBdom, -⟩ := mem_aotci_iff.mp hB
  have he := (mem_aotciEmbSet_iff.mp hh).right
  have h1s : ((1 : ℕ) : M) ∈ succ ((1 : ℕ) : M) := mem_succ_self _
  have h12 : ((1 : ℕ) : M) ⊆ dom h := by
    rw [he.dom_eq]
    exact fun _ hz ↦ mem_succ_of_mem hz
  have hhr : IsFunction (h ↾ ((1 : ℕ) : M)) := he.isFunction.restrict _
  have hhrdom : dom (h ↾ ((1 : ℕ) : M)) = ((1 : ℕ) : M) := dom_restrict_of_subset he.isFunction h12
  have hv0 : cc (h ↾ ((1 : ℕ) : M)) (update (h ﹫ ((1 : ℕ) : M)) u D) ﹫ ∅ = h ﹫ ∅ := by
    rw [cc_val_of_mem hhr _ (by rw [hhrdom]; exact empty_mem_natCast_one),
      val_restrict _ he.isFunction empty_mem_natCast_one (h12 empty_mem_natCast_one)]
  have hv1 : cc (h ↾ ((1 : ℕ) : M)) (update (h ﹫ ((1 : ℕ) : M)) u D) ﹫ ((1 : ℕ) : M) =
      update (h ﹫ ((1 : ℕ) : M)) u D := by
    have h' := cc_val_self hhr (update (h ﹫ ((1 : ℕ) : M)) u D)
    rwa [hhrdom] at h'
  refine mem_aotciEmbSet_of_isAotciEmbedding hAf hAdom hBf hBdom
    ⟨hhr.cc _, by rw [dom_cc, hhrdom], fun {i} hi ↦ ?_⟩
  rcases mem_succ_one_cases hi with rfl | rfl
  · rw [hv0]
    exact he.isOtciEmbedding hi
  rw [hv1]
  have hA1 := val_mem_otci_of_mem_aotci hA h1s
  have hB1 := val_mem_otci_of_mem_aotci hB h1s
  obtain ⟨hinj, hodr⟩ := (isOtciEmbedding_iff_of_mem_otci_one hA1 hB1).mp (he.isOtciEmbedding h1s)
  have hRA := (rtlosOf_of_mem_otci_one hA1).left
  have hRB := (rtlosOf_of_mem_otci_one hB1).left
  have hf := hinj.isFunction
  have hfdom := hinj.isFunctionFromTo.dom_eq
  have hval {a : M} (ha : a ∈ ndOf (A ﹫ ((1 : ℕ) : M))) (hne : a ≠ u) :
      update (h ﹫ ((1 : ℕ) : M)) u D ﹫ a = (h ﹫ ((1 : ℕ) : M)) ﹫ a :=
    val_update_of_ne hf _ (by rw [hfdom]; exact ha) hne
  have hvalu : update (h ﹫ ((1 : ℕ) : M)) u D ﹫ u = D := val_update_self hf _ _
  have hneD {a : M} (ha : a ∈ ndOf (A ﹫ ((1 : ℕ) : M))) (hne : a ≠ u) :
      D ≠ (h ﹫ ((1 : ℕ) : M)) ﹫ a := by
    intro hDa
    rcases hRA.trichotomous ha hu with h' | h' | h'
    · have := hlt a ha h'
      rw [← hDa] at this
      exact hRB.isIrreflOn.irrefl hD this
    · exact hne h'
    · have := hgt a ha h'
      rw [← hDa] at this
      exact hRB.isIrreflOn.irrefl hD this
  rw [isOtciEmbedding_iff_of_mem_otci_one hA1 hB1]
  refine ⟨isInjectionFromTo_of_val (hf.update _ _) ?_ (fun a ha ↦ ?_) fun a ha b hb hab ↦ ?_,
    fun a ha b hb hab ↦ ?_⟩
  · rw [dom_update, hfdom]
    ext z
    rw [mem_insert_iff]
    exact ⟨fun h' ↦ h'.elim (fun h'' ↦ h'' ▸ hu) (fun h'' ↦ h''), .inr⟩
  · by_cases hau : a = u
    · rw [hau, hvalu]
      exact hD
    · rw [hval ha hau]
      exact hinj.isFunctionFromTo.val_mem ha
  · by_cases hau : a = u <;> by_cases hbu : b = u
    · rw [hau, hbu]
    · rw [hau, hvalu, hval hb hbu] at hab
      exact (hneD hb hbu hab).elim
    · rw [hbu, hvalu, hval ha hau] at hab
      exact (hneD ha hau hab.symm).elim
    · rw [hval ha hau, hval hb hbu] at hab
      exact hinj.right ha hb hab
  · by_cases hau : a = u <;> by_cases hbu : b = u
    · rw [hau, hbu] at hab
      exact (hRA.isIrreflOn.irrefl hu hab).elim
    · rw [hau, hvalu, hval hb hbu]
      rw [hau] at hab
      exact hgt b hb hab
    · rw [hbu, hvalu, hval ha hau]
      rw [hbu] at hab
      exact hlt a ha hab
    · rw [hval ha hau, hval hb hbu]
      exact hodr a ha b hb hab

/-- The values of `embUpd σ A w D` at level `1` away from `w` -/
theorem embUpd_val_one_of_ne {σ A w D x : M} (hσ : IsFunction σ) (h0 : (∅ : M) ∈ dom σ)
    (hf1 : IsFunction (σ ﹫ ((1 : ℕ) : M))) (hx : x ∈ dom (σ ﹫ ((1 : ℕ) : M)))
    (hxA : x ∈ ndOf (aoc (uc A) ﹫ ((1 : ℕ) : M))) (hxw : x ≠ w) :
    (embUpd σ A w D ﹫ ((1 : ℕ) : M)) ﹫ x = (σ ﹫ ((1 : ℕ) : M)) ﹫ x := by
  have h12 : ((1 : ℕ) : M) ⊆ dom σ := by
    intro z hz
    rw [natCast_succ, natCast_zero, mem_succ_iff] at hz
    rcases hz with rfl | hz
    · exact h0
    · simp at hz
  have hhr : IsFunction (σ ↾ ((1 : ℕ) : M)) := hσ.restrict _
  have hhrdom : dom (σ ↾ ((1 : ℕ) : M)) = ((1 : ℕ) : M) := dom_restrict_of_subset hσ h12
  have hv1 : embUpd σ A w D ﹫ ((1 : ℕ) : M) = update (lvlOneRes σ A) w D := by
    have h' := cc_val_self hhr (update (lvlOneRes σ A) w D)
    rwa [hhrdom] at h'
  have hlf : IsFunction (lvlOneRes σ A) := hf1.restrict _
  have hxd : x ∈ dom (lvlOneRes σ A) := by
    rw [lvlOneRes, dom_restrict hf1, mem_inter_iff]
    exact ⟨hx, hxA⟩
  rw [hv1, val_update_of_ne hlf _ hxd hxw, lvlOneRes, val_restrict _ hf1 hxA hx]

section YStar

variable {Q V w qa ha : M}

/-- The `ucf` data of an old node `a = (q_a, h_a)` of `Q(2) ⊗ X'` whose `ucf` as a tensor product
is `(1, w)`, for discontinuous `q_a`: `q_a` has a level-`1` `ucf` sent to `w` -/
theorem ucf_facts_of_tpUcf_dct (hQ : Q ∈ aotci ((2 : ℕ) : M)) {X : M}
    (hX : X ∈ aotci ((1 : ℕ) : M)) (hqa : qa ∈ ndOf (Q ﹫ 2)) (hqart : qa ∉ rtOf (Q ﹫ 2))
    (hha : ha ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa)) (tensorProdTwoAOneTgt X))
    (hdct : ctp (uc qa) = dct)
    (hucf : tpUcf Q X !(dctUZero, !(qa, ha)) = !(((1 : ℕ) : M), w)) :
    ucflvl (uc qa) = ((1 : ℕ) : M) ∧ ucfdcn (uc qa) ∈ ndOf (aoc (uc qa) ﹫ ((1 : ℕ) : M)) ∧
      (ha ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc qa) = relabelOne trvAZero w ∧
      w ∈ ndOf (X ﹫ ((1 : ℕ) : M)) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hUa := uc_mem_stduoci_of_mem_otci_two hQ2 hqa
  have hy : !(dctUZero, !(qa, ha)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) X :=
    mem_tensorProdTwoAOneNds_iff'.mpr ⟨qa, hqa, hqart, ha, hha, rfl⟩
  have hs : sig (uc qa) ≠ ∅ := by
    intro h'
    apply hqart
    have hd := dom_sig_uc_eq_depOf hQ2 hqa
    rw [h', dom_empty] at hd
    exact TreeStructure.mem_rt_iff.mpr ⟨hqa, hd.symm⟩
  obtain ⟨h5, -, -, -⟩ := ucf_props_of_mem_stduoci_one hUa hdct hs
  have h3 : ((3 : ℕ) : M) ∈ dom (uc qa) := by
    rw [h5]
    exact natCast_mem_natCast_of_lt (by omega)
  rw [tpUcf, if_pos (isTpTwo_orderedPair hy), tpUcfTwo, nodeU_orderedPair, nodeH_orderedPair,
    ucfOrLast, if_pos h3, tpUcfAux, orderedPair_eq_orderedPair_iff] at hucf
  obtain ⟨hl, ho⟩ := hucf
  have hl' : ucflvl (uc qa) = ((1 : ℕ) : M) := hl
  have hnd := (ucf_props_of_mem_stduoci_one hUa hdct hs).right.right.right
  rw [hl'] at hnd
  obtain ⟨i, hi, -, hie⟩ := exists_sigdcn_eq hUa hnd
  obtain ⟨hmem, hval⟩ := sigImg_spec hQ2 hqa hX hha hi
  have hsi : sigImg X qa ha i = w := by
    rw [← ho]
    change tpOrig X ((1 : ℕ) : M) ((ha ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) i) = _
    rw [hie, hl]
    rfl
  refine ⟨hl', hnd, ?_, hsi ▸ hmem⟩
  rw [← hie, hval, hsi]

/-- The least new node above which the old node `a = (q_a, h_a)` is the nearest, for
discontinuous `q_a`: the continuous child `c` of `q_a`, with the new node of `c` sent to the new
entry `e` of `V` -/
theorem exists_yStar_dct (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hwR : w ∈ iniSegRight V (⋃₀ dom (sig V)))
    (hwl : ∀ r ∈ iniSegRight V (⋃₀ dom (sig V)), r = w ∨ w [iniSegOdr V] r)
    (hqa : qa ∈ ndOf (Q ﹫ 2)) (hqart : qa ∉ rtOf (Q ﹫ 2))
    (hha : ha ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa))
      (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V)))))
    (hdct : ctp (uc qa) = dct)
    (hucf : tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) !(dctUZero, !(qa, ha)) =
      !(((1 : ℕ) : M), w)) :
    ∃ c h', c ∈ chdOf (Q ﹫ 2) qa ∧ ctp (uc c) = ct ∧ chdOf (Q ﹫ 2) c = ∅ ∧
      (∀ c' ∈ chdOf (Q ﹫ 2) qa, c' = c ∨ c [sblOdrOf (Q ﹫ 2)] c') ∧
      h' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc c)) (tensorProdTwoAOneTgt (aoc V)) ∧
      !(dctUZero, !(c, h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) ∧
      (∀ i ∈ depOf (Q ﹫ 2) qa, (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) i =
        (ha ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) i) ∧
      (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) (depOf (Q ﹫ 2) qa) =
        relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))) ∧
      embRestrict (uc qa) h' = ha := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  obtain ⟨hX', h0, hsub, hnd'⟩ := lastSeg_facts hV hm
  obtain ⟨ht0, htsub, -⟩ := lastSeg_tgt_facts hV hm
  have hT := tensorProdTwoAOneTgt_mem hX
  have hT' := tensorProdTwoAOneTgt_mem hX'
  have hRX := (rtlosOf_of_mem_otci_one hX1).left
  have hUa := uc_mem_stduoci_of_mem_otci_two hQ2 hqa
  have hAa := aoc_mem_aotci_of_mem_stduoci_one hUa
  obtain ⟨hl1, hund, hhu, hwX'⟩ := ucf_facts_of_tpUcf_dct hQ hX' hqa hqart hha hdct hucf
  obtain ⟨hew, -, hold⟩ := new_lt_nearest hV hm hwR hwl
  have hwX : w ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) := hsub.left hwX'
  have heX := (siglvl_eq_one hV hm).right
  -- the extension of `q_a`'s identifier and the continuous child
  obtain ⟨r, hr⟩ := (exists_mem_ciExt_one_iff hUa hdct).mpr (.inr hl1)
  obtain ⟨-, -, -, -, hchd⟩ := otciCond_two hQ2
  obtain ⟨c0, hc0, hc0k⟩ := ((hchd qa hqa).left (aoc r)).mpr ⟨r, hr, rfl⟩
  obtain ⟨hc, hck, -, hcct, hcchd, hcmin⟩ :=
    ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hqa hc0
  set c := ctChd (Q ﹫ 2) qa (aoc (uc c0)) with hcdef
  have hcn : c ∈ ndOf (Q ﹫ 2) := mem_ndOf_of_mem_chdOf (otciCond_two hQ2).left hc
  have hUc := uc_mem_stduoci_of_mem_otci_two hQ2 hcn
  obtain ⟨-, hrs, -, hrct⟩ := mem_ciExt_props hr
  have hucr : uc c = r :=
    eq_of_aoc_eq_of_ctp_eq_ct (natCast_mem_omega 1) hUc hrs hcct hrct (hck.trans hc0k)
  have hext : !(uc qa, uc c) ∈ ciExt ((1 : ℕ) : M) := by rw [hucr]; exact hr
  obtain ⟨hsb, hndc, hsU, hsubc, hnear⟩ := ext_one_tree hext
  have hs : sig (uc qa) ≠ ∅ := by
    intro h'
    apply hqart
    have hd := dom_sig_uc_eq_depOf hQ2 hqa
    rw [h', dom_empty] at hd
    exact TreeStructure.mem_rt_iff.mpr ⟨hqa, hd.symm⟩
  obtain ⟨hsu, hsmin⟩ := hnear hs
  have hda : dom (sig (uc qa)) = depOf (Q ﹫ 2) qa := dom_sig_uc_eq_depOf hQ2 hqa
  rw [hda] at hsb hndc hsU hsu hsmin
  set sn := sigdcn (uc c) (depOf (Q ﹫ 2) qa) with hsndef
  -- `h_a` into the full target
  have hhaT : ha ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa)) (tensorProdTwoAOneTgt (aoc V)) :=
    ((mem_aotciEmbSet_tgt_iff hAa hX hX' h0 hsub).mp hha).left
  have hAc := aoc_mem_aotci_of_mem_stduoci_one hUc
  obtain ⟨hinj, hodr⟩ := (isOtciEmbedding_iff_of_mem_otci_one
    (val_mem_otci_of_mem_aotci hAa (mem_succ_self _))
    (val_mem_otci_of_mem_aotci hT' (mem_succ_self _))).mp
      ((mem_aotciEmbSet_iff.mp hha).right.isOtciEmbedding (mem_succ_self _))
  have hrelX' (z : M) (hz : z ∈ ndOf (aoc (uc qa) ﹫ ((1 : ℕ) : M))) :
      ∃ z' ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)),
        (ha ﹫ ((1 : ℕ) : M)) ﹫ z = relabelOne trvAZero z' :=
    exists_relabelOne_eq hX' hha hz
  have hRc := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci hAc (mem_succ_self _))).left
  set h' := cc (ha ↾ ((1 : ℕ) : M)) (update (ha ﹫ ((1 : ℕ) : M)) sn
    (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))))) with hh'def
  have hh' : h' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc c)) (tensorProdTwoAOneTgt (aoc V)) := by
    refine embExt_mem_aotciEmbSet hAa hAc hT (aoc_val_of_mem_ciExt_one hext).left hsubc hndc hsU
      hhaT ?_ (fun z hz hzs ↦ ?_) (fun z hz hsz ↦ ?_)
    · rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hX1]
      exact ⟨_, heX, rfl⟩
    · obtain ⟨z', hz', hzz⟩ := hrelX' z hz
      have hzu : z [odrOne (aoc (uc qa) ﹫ ((1 : ℕ) : M))] (ucfdcn (uc qa)) :=
        (hsubc.right z hz _ hund).mpr (hRc.isTransOn.trans (hsubc.left hz) hsb (hsubc.left hund)
          hzs hsu)
      have h1 := hodr z hz _ hund hzu
      rw [hzz, hhu, rel_tgt_relabel_iff hX' hz' hwX'] at h1
      rw [hzz, rel_tgt_relabel_iff hX (hsub.left hz') heX]
      exact hold z' hz' ((hsub.right z' hz' w hwX').mp h1)
    · obtain ⟨z', hz', hzz⟩ := hrelX' z hz
      rw [hzz, rel_tgt_relabel_iff hX heX (hsub.left hz')]
      have hX'1 := val_mem_otci_of_mem_aotci hX' (mem_succ_self _)
      rcases hsmin z hz hsz with rfl | h''
      · rw [hhu] at hzz
        rw [← relabelOne_injective hX'1 hwX' hz' hzz]
        exact hew
      · have h1 := hodr _ hund z hz ((hsubc.right _ hund z hz).mpr h'')
        rw [hzz, hhu, rel_tgt_relabel_iff hX' hwX' hz'] at h1
        exact hRX.isTransOn.trans heX hwX (hsub.left hz') hew ((hsub.right w hwX' z' hz').mp h1)
  have he := (mem_aotciEmbSet_iff.mp hha).right
  have h12 : ((1 : ℕ) : M) ⊆ dom ha := by
    rw [he.dom_eq]
    exact fun _ hz ↦ mem_succ_of_mem hz
  have hhr : IsFunction (ha ↾ ((1 : ℕ) : M)) := he.isFunction.restrict _
  have hhrdom : dom (ha ↾ ((1 : ℕ) : M)) = ((1 : ℕ) : M) := dom_restrict_of_subset he.isFunction h12
  have hv1 : h' ﹫ ((1 : ℕ) : M) = update (ha ﹫ ((1 : ℕ) : M)) sn
      (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V)))) := by
    have h'' := cc_val_self hhr (update (ha ﹫ ((1 : ℕ) : M)) sn
      (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V)))))
    rwa [hhrdom] at h''
  have hv0 : h' ﹫ ∅ = ha ﹫ ∅ := by
    rw [hh'def, cc_val_of_mem hhr _ (by rw [hhrdom]; exact empty_mem_natCast_one),
      val_restrict _ he.isFunction empty_mem_natCast_one (h12 empty_mem_natCast_one)]
  have hinj1 := hinj.isFunction
  have hdom1 := hinj.isFunctionFromTo.dom_eq
  have hsigc := (uc_rel_of_mem_chdOf hQ2 hqa hc).left
  have hsfc := (uociCond_of_mem_stduoci_one hUc).right.right.right.left.left
  have hsd (i : M) (hi : i ∈ depOf (Q ﹫ 2) qa) : sigdcn (uc c) i = sigdcn (uc qa) i := by
    have hi' : i ∈ dom (sig (uc qa)) := by rw [hda]; exact hi
    have hic : i ∈ dom (sig (uc c)) := by
      rw [(uc_rel_of_mem_chdOf hQ2 hqa hc).right.left, hda]
      exact mem_succ_of_mem hi
    rw [sigdcn, sigdcn, hsigc, val_restrict _ hsfc hi' hic]
  have hold' (i : M) (hi : i ∈ depOf (Q ﹫ 2) qa) :
      sigdcn (uc qa) i ∈ ndOf (aoc (uc qa) ﹫ ((1 : ℕ) : M)) :=
    (siglvl_eq_one hUa (by rw [hda]; exact hi)).right
  refine ⟨c, h', hc, hcct, hcchd,
    fun c' hc' ↦ hcmin c' hc' (aoc_uc_eq_of_mem_chdOf hQ2 hqa hc' hc0),
    hh', mem_tensorProdTwoAOneNds_iff'.mpr ⟨c, hcn,
      not_mem_rtOf_of_mem_chdOf (otciCond_two hQ2).left hc, h', hh', rfl⟩,
    fun i hi ↦ ?_, by rw [hv1]; exact val_update_self hinj1 _ _, ?_⟩
  · rw [hv1, hsd i hi]
    exact val_update_of_ne hinj1 _ (by rw [hdom1]; exact hold' i hi)
      fun h'' ↦ hsU (h'' ▸ hold' i hi)
  -- the restriction to `q_a` gives back `h_a`
  have hres : IsSetRestrictedTo (fun i ↦ (h' ﹫ i) ↾ ndOf (aoc (uc qa) ﹫ i)) ((2 : ℕ) : M) :=
    isSetRestrictedTo_of_definable _
  refine (isFunction_toSetRestrictedTo hres).ext he.isFunction
    (by rw [dom_toSetRestrictedTo hres, he.dom_eq]; rfl) fun i hi ↦ ?_
  rw [dom_toSetRestrictedTo hres] at hi
  rw [val_toSetRestrictedTo hres hi]
  rcases mem_succ_one_cases hi with rfl | rfl
  · rw [hv0]
    have he0 := ((he.isOtciEmbedding (mem_succ_of_mem empty_mem_natCast_one)).isEmbedding
      ).isEmbedding_ts.isInjectionFromTo
    have hd0 : ndOf (aoc (uc qa) ﹫ ∅) = dom (ha ﹫ ∅) := he0.isFunctionFromTo.dom_eq.symm
    rw [hd0]
    exact restrict_dom he0.isFunction
  · rw [hv1]
    have hsub' : ndOf (aoc (uc qa) ﹫ ((1 : ℕ) : M)) ⊆
        dom (update (ha ﹫ ((1 : ℕ) : M)) sn (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))))) := by
      rw [dom_update, hdom1]
      exact fun _ h'' ↦ by rw [mem_insert_iff]; exact .inr h''
    refine ((hinj1.update _ _).restrict _).ext hinj1
      (by rw [dom_restrict_of_subset (hinj1.update _ _) hsub', hdom1]) fun x hx ↦ ?_
    rw [dom_restrict_of_subset (hinj1.update _ _) hsub'] at hx
    rw [val_restrict _ (hinj1.update _ _) hx (hsub' hx)]
    exact val_update_of_ne hinj1 _ (by rw [hdom1]; exact hx) fun h'' ↦ hsU (h'' ▸ hx)

/-- `a` is the nearest old node above the node `y*` of `exists_yStar_dct` -/
theorem yStar_dct_order (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (_hwR : w ∈ iniSegRight V (⋃₀ dom (sig V)))
    (hwl : ∀ r ∈ iniSegRight V (⋃₀ dom (sig V)), r = w ∨ w [iniSegOdr V] r)
    (hqa : qa ∈ ndOf (Q ﹫ 2)) (hqart : qa ∉ rtOf (Q ﹫ 2))
    (hha : ha ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa))
      (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V)))))
    (hdct : ctp (uc qa) = dct)
    (hucf : tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) !(dctUZero, !(qa, ha)) =
      !(((1 : ℕ) : M), w))
    {c h' : M} (hc : c ∈ chdOf (Q ﹫ 2) qa)
    (hh' : h' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc c)) (tensorProdTwoAOneTgt (aoc V)))
    (hy : !(dctUZero, !(c, h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hval : ∀ i ∈ depOf (Q ﹫ 2) qa, (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) i =
        (ha ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) i)
    (hnew : (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) (depOf (Q ﹫ 2) qa) =
        relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))))
    (hres : embRestrict (uc qa) h' = ha) :
    !(dctUZero, !(c, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
        !(dctUZero, !(qa, ha)) ∧
      ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
        !(dctUZero, !(c, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
          z = !(dctUZero, !(qa, ha)) ∨
            !(dctUZero, !(qa, ha)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hPs := (otciCond_two hQ2).left
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  obtain ⟨hX', h0, hsub, hnd'⟩ := lastSeg_facts hV hm
  have hR1 := (rtlosOf_of_mem_otci_one hX1).left
  have hUa := uc_mem_stduoci_of_mem_otci_two hQ2 hqa
  have hUc := uc_mem_stduoci_of_mem_otci_two hQ2 (mem_ndOf_of_mem_chdOf hPs hc)
  have hcn := mem_ndOf_of_mem_chdOf hPs hc
  obtain ⟨hdc, hanc⟩ := ancOf_eq_of_mem_chdOf hPs hc
  have hk : depOf (Q ﹫ 2) qa ∈ depOf (Q ﹫ 2) c := by rw [hdc]; exact mem_succ_self _
  have hk0 : depOf (Q ﹫ 2) qa ≠ ∅ := fun h'' ↦ hqart (TreeStructure.mem_rt_iff.mpr ⟨hqa, h''⟩)
  have hda : dom (sig (uc qa)) = depOf (Q ﹫ 2) qa := dom_sig_uc_eq_depOf hQ2 hqa
  obtain ⟨-, hund, hhu, hwX'⟩ := ucf_facts_of_tpUcf_dct hQ hX' hqa hqart hha hdct hucf
  have hsigc := (uc_rel_of_mem_chdOf hQ2 hqa hc).left
  have hsfc := (uociCond_of_mem_stduoci_one hUc).right.right.right.left.left
  have hsd (i : M) (hi : i ∈ depOf (Q ﹫ 2) qa) : sigdcn (uc c) i = sigdcn (uc qa) i := by
    have hi' : i ∈ dom (sig (uc qa)) := by rw [hda]; exact hi
    have hic : i ∈ dom (sig (uc c)) := by
      rw [(uc_rel_of_mem_chdOf hQ2 hqa hc).right.left, hda]
      exact mem_succ_of_mem hi
    rw [sigdcn, sigdcn, hsigc, val_restrict _ hsfc hi' hic]
  have hheX := (siglvl_eq_one hV hm).right
  have hfirst : ∀ i ∈ depOf (Q ﹫ 2) qa,
      sigImg (aoc V) c h' i ≠ sigdcn V (⋃₀ dom (sig V)) := by
    intro i hi
    obtain ⟨z', hz', hzz⟩ := exists_relabelOne_eq hX' hha
      (siglvl_eq_one hUa (by rw [hda]; exact hi)).right
    change tpOrig (aoc V) ((1 : ℕ) : M) ((h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) i) ≠ _
    rw [hval i hi, hzz, tpOrig_one_relabelOne hX (hsub.left hz')]
    exact ((hnd' z').mp hz').right
  have hje : sigImg (aoc V) c h' (depOf (Q ﹫ 2) qa) = sigdcn V (⋃₀ dom (sig V)) := by
    change tpOrig (aoc V) ((1 : ℕ) : M) ((h' ﹫ ((1 : ℕ) : M)) ﹫ _) = _
    rw [hnew, tpOrig_one_relabelOne hX hheX]
  have hwX : w ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) := hsub.left hwX'
  have hhu' : (h' ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) c (depOf (Q ﹫ 2) qa))) =
      relabelOne trvAZero w := by
    rw [hanc]
    obtain ⟨i, hi, -, hie⟩ := exists_sigdcn_eq hUa hund
    rw [hda] at hi
    rw [← hie, ← hsd i hi, hval i hi, hie, hhu]
  have hnone : ∀ w' ∈ iniSegRight V (⋃₀ dom (sig V)),
      ¬ (relabelOne trvAZero w') [odrOne (tensorProdTwoAOneTgt (aoc V) ﹫ ((1 : ℕ) : M))]
        ((h' ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) c (depOf (Q ﹫ 2) qa)))) := by
    intro w' hw' hlt'
    have hw'X := ((mem_iniSegNds_last_iff hV hm).mp (mem_iniSegRight_iff.mp hw').left).left
    rw [hhu', rel_tgt_relabel_iff hX hw'X hwX] at hlt'
    rcases hwl w' hw' with h'' | h''
    · rw [h''] at hlt'
      exact hR1.isIrreflOn.irrefl hwX hlt'
    · exact hR1.isAsymmOn.asymm hwX hw'X h'' hlt'
  have hsucc : succOne (Q ﹫ 2) c h' (depOf (Q ﹫ 2) qa) = !(dctUZero, !(qa, ha)) := by
    rw [succOne, hanc, hres]
  have haX' : !(dctUZero, !(qa, ha)) ∈ tensorProdTwoAOneNds (Q ﹫ 2)
      (iniSegAoc V (⋃₀ dom (sig V))) :=
    mem_tensorProdTwoAOneNds_iff'.mpr ⟨qa, hqa, hqart, ha, hha, rfl⟩
  have hE : succOne (Q ﹫ 2) c h' (depOf (Q ﹫ 2) qa) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) := by
    rw [hsucc]
    exact ((mem_tensorProdTwoAOneNds_iff_of_isSubOne hQ hX hX' h0 hsub).mp haX').left
  have hlt := rel_succOne hQ hV hm hcn hy hh' hk hk0 hfirst
  rw [hsucc] at hlt
  refine ⟨hlt, fun z hz hyz ↦ ?_⟩
  have h'' := succOne_min hQ hV hm hcn hy hh' hk hk0 hje hnone hE hz hyz
  rwa [hsucc] at h''

/-- For a continuous `q_a`, the last node `u` of `q_a`'s signature is sent to `w` by `h_a` -/
theorem ucf_facts_of_tpUcf_ct (hQ : Q ∈ aotci ((2 : ℕ) : M)) {X : M}
    (hX : X ∈ aotci ((1 : ℕ) : M)) (hqa : qa ∈ ndOf (Q ﹫ 2)) (hqart : qa ∉ rtOf (Q ﹫ 2))
    (hha : ha ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa)) (tensorProdTwoAOneTgt X))
    (hct : ctp (uc qa) = ct)
    (hucf : tpUcf Q X !(dctUZero, !(qa, ha)) = !(((1 : ℕ) : M), w)) :
    depOf (Q ﹫ 2) qa = succ (⋃₀ depOf (Q ﹫ 2) qa) ∧
      (ha ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) (⋃₀ depOf (Q ﹫ 2) qa) = relabelOne trvAZero w ∧
      w ∈ ndOf (X ﹫ ((1 : ℕ) : M)) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hUa := uc_mem_stduoci_of_mem_otci_two hQ2 hqa
  have hy : !(dctUZero, !(qa, ha)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) X :=
    mem_tensorProdTwoAOneNds_iff'.mpr ⟨qa, hqa, hqart, ha, hha, rfl⟩
  have hda : dom (sig (uc qa)) = depOf (Q ﹫ 2) qa := dom_sig_uc_eq_depOf hQ2 hqa
  have hd0 : depOf (Q ﹫ 2) qa ≠ ∅ := fun h'' ↦ hqart (TreeStructure.mem_rt_iff.mpr ⟨hqa, h''⟩)
  obtain ⟨-, hkd, hdeq⟩ := sUnion_mem_of_ne_empty (hS.isTreeStructure.dep_mem_omega hqa) hd0
  have h3 : ((3 : ℕ) : M) ∉ dom (uc qa) := by
    rw [dom_eq_three_of_ctp_eq_ct (natCast_mem_omega 1) (mem_stduoci_iff.mp hUa).left hct]
    exact notMem_self _
  have hk : ⋃₀ depOf (Q ﹫ 2) qa ∈ dom (sig (uc qa)) := by rw [hda]; exact hkd
  rw [tpUcf, if_pos (isTpTwo_orderedPair hy), tpUcfTwo, nodeU_orderedPair, nodeH_orderedPair,
    ucfOrLast, if_neg h3, hda, sig_val_eq_pair hUa hk, tpUcfAux, lvl_orderedPair, dcn_orderedPair,
    orderedPair_eq_orderedPair_iff] at hucf
  obtain ⟨hmem, hval⟩ := sigImg_spec hQ2 hqa hX hha hk
  have hsi : sigImg X qa ha (⋃₀ depOf (Q ﹫ 2) qa) = w := hucf.right
  refine ⟨hdeq, ?_, hsi ▸ hmem⟩
  rw [hval, hsi]

/-- The least new node above which the old node `a = (q_a, h_a)` is the nearest, for continuous
`q_a`: `q_a` itself, with the image `w` of its last node replaced by the new entry `e` -/
theorem exists_yStar_ct (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hwR : w ∈ iniSegRight V (⋃₀ dom (sig V)))
    (hwl : ∀ r ∈ iniSegRight V (⋃₀ dom (sig V)), r = w ∨ w [iniSegOdr V] r)
    (hqa : qa ∈ ndOf (Q ﹫ 2)) (hqart : qa ∉ rtOf (Q ﹫ 2))
    (hha : ha ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa))
      (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V)))))
    (hct : ctp (uc qa) = ct)
    (hucf : tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) !(dctUZero, !(qa, ha)) =
      !(((1 : ℕ) : M), w)) :
    ∃ h', h' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa)) (tensorProdTwoAOneTgt (aoc V)) ∧
      !(dctUZero, !(qa, h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) ∧
      (∀ i ∈ ⋃₀ depOf (Q ﹫ 2) qa, (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) i =
        (ha ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) i) ∧
      (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) (⋃₀ depOf (Q ﹫ 2) qa) =
        relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))) ∧
      embUpd h' qa (sigdcn (uc qa) (⋃₀ depOf (Q ﹫ 2) qa)) (relabelOne trvAZero w) = ha := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  obtain ⟨hX', h0, hsub, hnd'⟩ := lastSeg_facts hV hm
  have hT := tensorProdTwoAOneTgt_mem hX
  have hRX := (rtlosOf_of_mem_otci_one hX1).left
  have hUa := uc_mem_stduoci_of_mem_otci_two hQ2 hqa
  have hAa := aoc_mem_aotci_of_mem_stduoci_one hUa
  obtain ⟨hdeq, hhu, hwX'⟩ := ucf_facts_of_tpUcf_ct hQ hX' hqa hqart hha hct hucf
  obtain ⟨hew, -, hold⟩ := new_lt_nearest hV hm hwR hwl
  have hwX : w ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) := hsub.left hwX'
  have heX := (siglvl_eq_one hV hm).right
  have hda : dom (sig (uc qa)) = depOf (Q ﹫ 2) qa := dom_sig_uc_eq_depOf hQ2 hqa
  set ka := ⋃₀ depOf (Q ﹫ 2) qa with hkadef
  have hka : ka ∈ dom (sig (uc qa)) := by rw [hda, hdeq]; exact mem_succ_self _
  set u := sigdcn (uc qa) ka with hudef
  have hu : u ∈ ndOf (aoc (uc qa) ﹫ ((1 : ℕ) : M)) := (siglvl_eq_one hUa hka).right
  have hhaT : ha ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa)) (tensorProdTwoAOneTgt (aoc V)) :=
    ((mem_aotciEmbSet_tgt_iff hAa hX hX' h0 hsub).mp hha).left
  obtain ⟨hinjT, hodrT⟩ := (isOtciEmbedding_iff_of_mem_otci_one
    (val_mem_otci_of_mem_aotci hAa (mem_succ_self _))
    (val_mem_otci_of_mem_aotci hT (mem_succ_self _))).mp
      ((mem_aotciEmbSet_iff.mp hhaT).right.isOtciEmbedding (mem_succ_self _))
  set h' := cc (ha ↾ ((1 : ℕ) : M)) (update (ha ﹫ ((1 : ℕ) : M)) u
    (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))))) with hh'def
  have hh' : h' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa)) (tensorProdTwoAOneTgt (aoc V)) := by
    refine embRep_mem_aotciEmbSet hAa hT hhaT hu ?_ (fun z hz hzu ↦ ?_) (fun z hz huz ↦ ?_)
    · rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hX1]
      exact ⟨_, heX, rfl⟩
    · obtain ⟨z', hz', hzz⟩ := exists_relabelOne_eq hX' hha hz
      have h1 := hodrT z hz u hu hzu
      rw [hzz, hhu, rel_tgt_relabel_iff hX (hsub.left hz') hwX] at h1
      rw [hzz, rel_tgt_relabel_iff hX (hsub.left hz') heX]
      exact hold z' hz' h1
    · obtain ⟨z', hz', hzz⟩ := exists_relabelOne_eq hX' hha hz
      have h1 := hodrT u hu z hz huz
      rw [hzz, hhu, rel_tgt_relabel_iff hX hwX (hsub.left hz')] at h1
      rw [hzz, rel_tgt_relabel_iff hX heX (hsub.left hz')]
      exact hRX.isTransOn.trans heX hwX (hsub.left hz') hew h1
  have he := (mem_aotciEmbSet_iff.mp hha).right
  have h12 : ((1 : ℕ) : M) ⊆ dom ha := by
    rw [he.dom_eq]
    exact fun _ hz ↦ mem_succ_of_mem hz
  have hhr : IsFunction (ha ↾ ((1 : ℕ) : M)) := he.isFunction.restrict _
  have hhrdom : dom (ha ↾ ((1 : ℕ) : M)) = ((1 : ℕ) : M) := dom_restrict_of_subset he.isFunction h12
  have hv1 : h' ﹫ ((1 : ℕ) : M) = update (ha ﹫ ((1 : ℕ) : M)) u
      (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V)))) := by
    have h'' := cc_val_self hhr (update (ha ﹫ ((1 : ℕ) : M)) u
      (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V)))))
    rwa [hhrdom] at h''
  have hinj1 := hinjT.isFunction
  have hdom1 := hinjT.isFunctionFromTo.dom_eq
  have hsfa := (uociCond_of_mem_stduoci_one hUa).right.right.right.left
  have hne (i : M) (hi : i ∈ ka) : sigdcn (uc qa) i ≠ u := by
    intro h''
    have hi' : i ∈ dom (sig (uc qa)) := (ordinal_of_mem ordinal_omega
      (dom_sig_mem_omega_of_mem_stduoci_one hUa)).transitive _ hka hi
    have := congrArg lbl h''
    rw [lbl_sigdcn hUa hi', lbl_sigdcn hUa hka] at this
    rw [this] at hi
    exact notMem_self _ hi
  refine ⟨h', hh', mem_tensorProdTwoAOneNds_iff'.mpr ⟨qa, hqa, hqart, h', hh', rfl⟩,
    fun i hi ↦ ?_, by rw [hv1]; exact val_update_self hinj1 _ _, ?_⟩
  · have hi' : i ∈ dom (sig (uc qa)) := (ordinal_of_mem ordinal_omega
      (dom_sig_mem_omega_of_mem_stduoci_one hUa)).transitive _ hka hi
    rw [hv1]
    exact val_update_of_ne hinj1 _ (by rw [hdom1]; exact (siglvl_eq_one hUa hi').right) (hne i hi)
  -- `embUpd` gives back `h_a`
  have hres1 : (h' ↾ ((1 : ℕ) : M)) = ha ↾ ((1 : ℕ) : M) := by
    have h'' := cc_restrict_dom hhr (update (ha ﹫ ((1 : ℕ) : M)) u
      (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V)))))
    rwa [hhrdom] at h''
  have hlvl : lvlOneRes h' qa = update (ha ﹫ ((1 : ℕ) : M)) u
      (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V)))) := by
    rw [lvlOneRes, hv1, ← hdom1]
    have hdu : dom (update (ha ﹫ ((1 : ℕ) : M)) u
        (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))))) = dom (ha ﹫ ((1 : ℕ) : M)) := by
      rw [dom_update, hdom1]
      ext z
      rw [mem_insert_iff]
      exact ⟨fun h'' ↦ h''.elim (fun h3 ↦ h3 ▸ hu) (fun h3 ↦ h3), .inr⟩
    rw [← hdu]
    exact restrict_dom (hinj1.update _ _)
  rw [embUpd, hres1, hlvl]
  refine (hhr.cc _).ext he.isFunction (by rw [dom_cc, hhrdom, he.dom_eq]) fun i hi ↦ ?_
  rw [dom_cc, hhrdom] at hi
  rcases mem_succ_one_cases hi with rfl | rfl
  · rw [cc_val_of_mem hhr _ (by rw [hhrdom]; exact empty_mem_natCast_one),
      val_restrict _ he.isFunction empty_mem_natCast_one (h12 empty_mem_natCast_one)]
  · have h'' := cc_val_self hhr (update (update (ha ﹫ ((1 : ℕ) : M)) u
      (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))))) u (relabelOne trvAZero w))
    rw [hhrdom] at h''
    rw [h'']
    have hdu : dom (update (update (ha ﹫ ((1 : ℕ) : M)) u
        (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))))) u (relabelOne trvAZero w)) =
          dom (ha ﹫ ((1 : ℕ) : M)) := by
      rw [dom_update, dom_update, hdom1]
      ext z
      rw [mem_insert_iff, mem_insert_iff]
      exact ⟨fun h3 ↦ h3.elim (fun h4 ↦ h4 ▸ hu) (fun h4 ↦ h4.elim (fun h5 ↦ h5 ▸ hu)
        (fun h5 ↦ h5)), fun h3 ↦ .inr (.inr h3)⟩
    refine ((hinj1.update _ _).update _ _).ext hinj1 hdu fun x hx ↦ ?_
    rw [hdu, hdom1] at hx
    by_cases hxu : x = u
    · rw [hxu, val_update_self (hinj1.update _ _), hhu]
    · have hx' : x ∈ dom (update (ha ﹫ ((1 : ℕ) : M)) u
          (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))))) := by
        rw [dom_update, hdom1, mem_insert_iff]
        exact .inr hx
      rw [val_update_of_ne (hinj1.update _ _) _ hx' hxu,
        val_update_of_ne hinj1 _ (by rw [hdom1]; exact hx) hxu]

/-- `a` is the nearest old node above the node `y*` of `exists_yStar_ct` -/
theorem yStar_ct_order (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hwR : w ∈ iniSegRight V (⋃₀ dom (sig V)))
    (hwl : ∀ r ∈ iniSegRight V (⋃₀ dom (sig V)), r = w ∨ w [iniSegOdr V] r)
    (hqa : qa ∈ ndOf (Q ﹫ 2)) (hqart : qa ∉ rtOf (Q ﹫ 2))
    (hha : ha ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa))
      (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V)))))
    (hct : ctp (uc qa) = ct)
    (hucf : tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) !(dctUZero, !(qa, ha)) =
      !(((1 : ℕ) : M), w)) {h' : M}
    (hh' : h' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa)) (tensorProdTwoAOneTgt (aoc V)))
    (hy : !(dctUZero, !(qa, h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hval : ∀ i ∈ ⋃₀ depOf (Q ﹫ 2) qa, (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) i =
        (ha ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) i)
    (hnew : (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) (⋃₀ depOf (Q ﹫ 2) qa) =
        relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))))
    (hupd : embUpd h' qa (sigdcn (uc qa) (⋃₀ depOf (Q ﹫ 2) qa)) (relabelOne trvAZero w) = ha) :
    !(dctUZero, !(qa, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
        !(dctUZero, !(qa, ha)) ∧
      ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
        !(dctUZero, !(qa, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
          z = !(dctUZero, !(qa, ha)) ∨
            !(dctUZero, !(qa, ha)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hPs := (otciCond_two hQ2).left
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := hPs
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, hnd'⟩ := lastSeg_facts hV hm
  have hUa := uc_mem_stduoci_of_mem_otci_two hQ2 hqa
  have hAa := aoc_mem_aotci_of_mem_stduoci_one hUa
  obtain ⟨hdeq, hhu, hwX'⟩ := ucf_facts_of_tpUcf_ct hQ hX' hqa hqart hha hct hucf
  have hda : dom (sig (uc qa)) = depOf (Q ﹫ 2) qa := dom_sig_uc_eq_depOf hQ2 hqa
  set ka := ⋃₀ depOf (Q ﹫ 2) qa with hkadef
  have hk : ka ∈ depOf (Q ﹫ 2) qa := by rw [hdeq]; exact mem_succ_self _
  have hka : ka ∈ dom (sig (uc qa)) := by rw [hda]; exact hk
  have hheX := (siglvl_eq_one hV hm).right
  have hfirst : ∀ i ∈ ka, sigImg (aoc V) qa h' i ≠ sigdcn V (⋃₀ dom (sig V)) := by
    intro i hi
    have hi' : i ∈ dom (sig (uc qa)) := (ordinal_of_mem ordinal_omega
      (dom_sig_mem_omega_of_mem_stduoci_one hUa)).transitive _ hka hi
    obtain ⟨z', hz', hzz⟩ := exists_relabelOne_eq hX' hha (siglvl_eq_one hUa hi').right
    change tpOrig (aoc V) ((1 : ℕ) : M) ((h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) i) ≠ _
    rw [hval i hi, hzz, tpOrig_one_relabelOne hX (hsub.left hz')]
    exact ((hnd' z').mp hz').right
  have hje : sigImg (aoc V) qa h' ka = sigdcn V (⋃₀ dom (sig V)) := by
    change tpOrig (aoc V) ((1 : ℕ) : M) ((h' ﹫ ((1 : ℕ) : M)) ﹫ _) = _
    rw [hnew, tpOrig_one_relabelOne hX hheX]
  have hanc1 : ancOf (Q ﹫ 2) qa (succ ka) = qa := by rw [← hdeq]; exact hTS.anc_dep hqa
  have hchd : qa ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) qa ka) := by
    have h'' := hTS.anc_succ_mem_chd hqa hk
    change ancOf (Q ﹫ 2) qa (succ ka) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) qa ka) at h''
    rwa [hanc1] at h''
  have hp0 : ancOf (Q ﹫ 2) qa ka ∈ ndOf (Q ﹫ 2) := hTS.mem_nd_of_mem_chd_val hchd
  have hu : sigdcn (uc qa) ka ∈ ndOf (aoc (uc qa) ﹫ ((1 : ℕ) : M)) := (siglvl_eq_one hUa hka).right
  have hne : ka ≠ ∅ → relabelOne trvAZero w ≠
      (h' ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) qa ka)) := by
    intro hk0 heq
    have hdp : depOf (Q ﹫ 2) (ancOf (Q ﹫ 2) qa ka) = ka :=
      (hTS.anc_mem_nd hqa (mem_succ_of_mem hk)).right
    have hs0 : sig (uc (ancOf (Q ﹫ 2) qa ka)) ≠ ∅ := by
      intro h''
      have hd := dom_sig_uc_eq_depOf hQ2 hp0
      rw [h'', dom_empty, hdp] at hd
      exact hk0 hd.symm
    obtain ⟨-, -, hsub0, hrel⟩ := uc_rel_of_mem_chdOf hQ2 hp0 hchd
    obtain ⟨-, hvnd, hlt, -⟩ := hrel hs0
    rw [dom_sig_uc_eq_depOf hQ2 hp0, hdp] at hlt
    have hvq := hsub0.left hvnd
    have hRa := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci hAa (mem_succ_self _))).left
    have hvu : ucfdcn (uc (ancOf (Q ﹫ 2) qa ka)) ≠ sigdcn (uc qa) ka := fun h'' ↦ by
      rw [h''] at hlt
      exact hRa.isIrreflOn.irrefl hu hlt
    have hhaT : ha ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa)) (tensorProdTwoAOneTgt (aoc V)) :=
      ((mem_aotciEmbSet_tgt_iff hAa hX hX' h0 hsub).mp hha).left
    obtain ⟨-, hodrT⟩ := (isOtciEmbedding_iff_of_mem_otci_one
      (val_mem_otci_of_mem_aotci hAa (mem_succ_self _))
      (val_mem_otci_of_mem_aotci (tensorProdTwoAOneTgt_mem hX) (mem_succ_self _))).mp
        ((mem_aotciEmbSet_iff.mp hhaT).right.isOtciEmbedding (mem_succ_self _))
    have h1 := hodrT _ hu _ hvq hlt
    -- the value of `h'` at the `ucf` of the parent is that of `h_a`
    obtain ⟨i, hi, -, hie⟩ := exists_sigdcn_eq hUa hvq
    have hik : i ∈ ka := by
      rw [hda, hdeq] at hi
      rcases mem_or_eq_of_mem_succ hi with h'' | h''
      · exact h''
      · exact (hvu (by rw [← hie, h''])).elim
    have hv' : (h' ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) qa ka)) =
        (ha ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) qa ka)) := by
      rw [← hie, hval i hik]
    rw [hv', ← hhu] at heq
    rw [← heq] at h1
    have hRT := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci (tensorProdTwoAOneTgt_mem hX)
      (mem_succ_self _))).left
    exact hRT.isIrreflOn.irrefl (hRT.mem_left h1) h1
  have hsucc : succTwo (Q ﹫ 2) qa h' ka (relabelOne trvAZero w) = !(dctUZero, !(qa, ha)) := by
    rw [succTwo, hanc1, eq_ctChd_of_ctp_eq_ct (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hp0
      hchd hct, hupd]
  have haX' : !(dctUZero, !(qa, ha)) ∈ tensorProdTwoAOneNds (Q ﹫ 2)
      (iniSegAoc V (⋃₀ dom (sig V))) :=
    mem_tensorProdTwoAOneNds_iff'.mpr ⟨qa, hqa, hqart, ha, hha, rfl⟩
  have haX : !(dctUZero, !(qa, ha)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) :=
    ((mem_tensorProdTwoAOneNds_iff_of_isSubOne hQ hX hX' h0 hsub).mp haX').left
  obtain ⟨hlt, -⟩ := rel_succTwo hQ hV hm hqa hy hh' hk hwR hwl hne hfirst hje
  rw [hsucc] at hlt
  refine ⟨hlt, fun z hz hyz ↦ ?_⟩
  have hE : !(dctUZero, !(ctChd (Q ﹫ 2) (ancOf (Q ﹫ 2) qa ka)
      (aoc (uc (ancOf (Q ﹫ 2) qa (succ ka)))), embUpd h' (ancOf (Q ﹫ 2) qa (succ ka))
        (sigdcn (uc qa) ka) (relabelOne trvAZero w))) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) := by
    have h'' := hsucc
    rw [succTwo] at h''
    rw [h'']
    exact haX
  have h'' := succTwo_min hQ hV hm hqa hy hh' hk hje hwR hwl hE hz hyz
  rw [← succTwo, hsucc] at h''
  exact h''

/-- The node `y*` of `exists_yStar_dct` is the least new node `y` with nearest old node `a` above
it -/
theorem yStar_dct_le (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
    (_hqa : qa ∈ ndOf (Q ﹫ 2)) (hdct : ctp (uc qa) = dct)
    {c h' : M} (hc : c ∈ chdOf (Q ﹫ 2) qa) (hcchd : chdOf (Q ﹫ 2) c = ∅)
    (hcmin : ∀ c' ∈ chdOf (Q ﹫ 2) qa, c' = c ∨ c [sblOdrOf (Q ﹫ 2)] c')
    (hh' : h' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc c)) (tensorProdTwoAOneTgt (aoc V)))
    (hy' : !(dctUZero, !(c, h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hnew : (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) (depOf (Q ﹫ 2) qa) =
        relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))))
    (hres : embRestrict (uc qa) h' = ha)
    {q h k : M} (hq : q ∈ ndOf (Q ﹫ 2))
    (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)))
    (hk : k ∈ depOf (Q ﹫ 2) q)
    (hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V)))
    (hje : sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V)))
    (haN : !(dctUZero, !(qa, ha)) ∈
      ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
    (hya : !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
      !(dctUZero, !(qa, ha)))
    (hamin : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
      !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
        z = !(dctUZero, !(qa, ha)) ∨
          !(dctUZero, !(qa, ha)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) :
    !(dctUZero, !(c, h')) = !(dctUZero, !(q, h)) ∨
      !(dctUZero, !(c, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
        !(dctUZero, !(q, h)) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hPs := (otciCond_two hQ2).left
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := hPs
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hcn := mem_ndOf_of_mem_chdOf hPs hc
  obtain ⟨hdc, hanc⟩ := ancOf_eq_of_mem_chdOf hPs hc
  have hdq := hTS.dep_mem_omega hq
  obtain ⟨w', -, -, hcase⟩ := eq_succ_of_isLeastAbove hQ hV hm hq hy hh hk hfirst hje haN hya hamin
  have hk1 : succ k ∈ succ (depOf (Q ﹫ 2) q) := succ_mem_succ_of_mem hdq hk
  have hck : ancOf (Q ﹫ 2) q (succ k) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) :=
    hTS.anc_succ_mem_chd hq hk
  rcases hcase with ⟨-, -, hE⟩ | ⟨-, hE⟩
  · rw [succOne, orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hE
    obtain ⟨-, hqeq, hheq⟩ := hE
    have hkd : depOf (Q ﹫ 2) qa = k := by
      rw [hqeq]
      exact (hTS.anc_mem_nd hq (mem_succ_of_mem hk)).right
    rw [← hqeq] at hck
    have hseqa :
        tensorProdTwoAOneSeq (Q ﹫ 2) !(qa, ha) = tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h) ↾ k := by
      have h'' := tensorProdTwoAOneSeq_embRestrict hQ2 hq (mem_succ_of_mem hk) hh
      rwa [← hheq, ← hqeq] at h''
    have hseqc : tensorProdTwoAOneSeq (Q ﹫ 2) !(qa, ha) =
        tensorProdTwoAOneSeq (Q ﹫ 2) !(c, h') ↾ depOf (Q ﹫ 2) qa := by
      have h'' := tensorProdTwoAOneSeq_embRestrict hQ2 hcn
        (by rw [hdc]; exact mem_succ_of_mem (mem_succ_self _)) hh'
      rwa [hanc, hres] at h''
    have hdsc : depOf (Q ﹫ 2) qa ⊆ dom (tensorProdTwoAOneSeq (Q ﹫ 2) !(c, h')) := by
      rw [tensorProdTwoAOneSeq_dom, hdc]
      exact fun _ h'' ↦ mem_succ_of_mem h''
    have hdsq : k ⊆ dom (tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h)) := by
      rw [tensorProdTwoAOneSeq_dom]
      exact (ordinal_of_mem ordinal_omega hdq).transitive _ hk
    have hsfc := isFunction_tensorProdTwoAOneSeq (Q ﹫ (2 : M)) !(c, h')
    have hsfq := isFunction_tensorProdTwoAOneSeq (Q ﹫ (2 : M)) !(q, h)
    have himg : (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) (depOf (Q ﹫ 2) qa) =
        (h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) k := by
      rw [hnew, (sigImg_spec hQ2 hq hX hh
        (by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hk)).right, hje]
    rw [hkd] at himg hdc
    refine eq_or_rel_of_seq_prefix hQ hX hy' hy hcn hq hh' hh hdc hk (fun i hi ↦ ?_) himg hcchd ?_
    · have h1 : tensorProdTwoAOneSeq (Q ﹫ 2) !(qa, ha) ﹫ i =
          (tensorProdTwoAOneSeq (Q ﹫ 2) !(c, h') ↾ depOf (Q ﹫ 2) qa) ﹫ i := by rw [hseqc]
      have h2 : tensorProdTwoAOneSeq (Q ﹫ 2) !(qa, ha) ﹫ i =
          (tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h) ↾ k) ﹫ i := by rw [hseqa]
      rw [hkd] at hdsc h1
      rw [val_restrict _ hsfc hi (hdsc hi)] at h1
      rw [val_restrict _ hsfq hi (hdsq hi)] at h2
      rw [← h1, h2]
    · rcases hcmin _ hck with h'' | h''
      · exact .inl h''.symm
      · exact .inr h''
  · exfalso
    rw [succTwo, orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hE
    obtain ⟨-, hqeq, -⟩ := hE
    have hka := (hTS.anc_mem_nd hq (mem_succ_of_mem hk)).left
    obtain ⟨-, -, -, hct, -⟩ :=
      ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hka hck
    change ctp (uc (ctChd (Q ﹫ 2) (ancOf (Q ﹫ 2) q k)
      (aoc (uc (ancOf (Q ﹫ 2) q (succ k)))))) = ct at hct
    rw [← hqeq, hdct] at hct
    exact ct_ne_dct hct.symm

/-- The node `y*` of `exists_yStar_ct` is the least new node `y` with nearest old node `a` above
it -/
theorem yStar_ct_le (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
    (hqa : qa ∈ ndOf (Q ﹫ 2)) (hct : ctp (uc qa) = ct) {h' : M}
    (hh' : h' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa)) (tensorProdTwoAOneTgt (aoc V)))
    (hy' : !(dctUZero, !(qa, h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hval : ∀ i ∈ ⋃₀ depOf (Q ﹫ 2) qa, (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) i =
        (ha ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) i)
    (hnew : (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) (⋃₀ depOf (Q ﹫ 2) qa) =
        relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))))
    {q h k : M} (hq : q ∈ ndOf (Q ﹫ 2))
    (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)))
    (hk : k ∈ depOf (Q ﹫ 2) q)
    (hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V)))
    (hje : sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V)))
    (haN : !(dctUZero, !(qa, ha)) ∈
      ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
    (hya : !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
      !(dctUZero, !(qa, ha)))
    (hamin : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
      !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
        z = !(dctUZero, !(qa, ha)) ∨
          !(dctUZero, !(qa, ha)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) :
    !(dctUZero, !(qa, h')) = !(dctUZero, !(q, h)) ∨
      !(dctUZero, !(qa, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
        !(dctUZero, !(q, h)) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hPs := (otciCond_two hQ2).left
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := hPs
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hdq := hTS.dep_mem_omega hq
  have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
  obtain ⟨w', -, -, hcase⟩ := eq_succ_of_isLeastAbove hQ hV hm hq hy hh hk hfirst hje haN hya hamin
  have hk1 : succ k ∈ succ (depOf (Q ﹫ 2) q) := succ_mem_succ_of_mem hdq hk
  have hck : ancOf (Q ﹫ 2) q (succ k) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) :=
    hTS.anc_succ_mem_chd hq hk
  have hka : ancOf (Q ﹫ 2) q k ∈ ndOf (Q ﹫ 2) := (hTS.anc_mem_nd hq (mem_succ_of_mem hk)).left
  have hkdep : depOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) = k :=
    (hTS.anc_mem_nd hq (mem_succ_of_mem hk)).right
  rcases hcase with ⟨-, -, hE⟩ | ⟨-, hE⟩
  · exfalso
    rw [succOne, orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hE
    obtain ⟨-, hqeq, -⟩ := hE
    rw [← hqeq, chdOf_eq_empty_of_ctp_eq_ct (natCast_mem_omega 2) hQ2 hqa hct] at hck
    simp at hck
  rw [succTwo, orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hE
  obtain ⟨-, hqeq, hheq⟩ := hE
  obtain ⟨hcc, hcck, hccs, -, -, hccmin⟩ :=
    ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hka hck
  rw [← hqeq] at hcc hcck hccs hccmin
  obtain ⟨hdqa, hanc⟩ := ancOf_eq_of_mem_chdOf hPs hcc
  rw [hkdep] at hdqa hanc
  have hka' : ⋃₀ depOf (Q ﹫ 2) qa = k := by
    rw [hdqa, sUnion_succ (ordinal_of_mem ordinal_omega
      (ordinal_omega.transitive _ hdq hk)).transitive]
  rw [hka'] at hval hnew
  have hUa := uc_mem_stduoci_of_mem_otci_two hQ2 hqa
  have hsfa := (uociCond_of_mem_stduoci_one hUa).right.right.right.left.left
  have hsfq := (uociCond_of_mem_stduoci_one hUq).right.right.right.left.left
  obtain ⟨hsig1, -⟩ := uc_ancOf_rel hQ2 hq hk1
  have hdqk : dom (sig (uc q)) = depOf (Q ﹫ 2) q := dom_sig_uc_eq_depOf hQ2 hq
  have hsd (i : M) (hi : i ∈ succ k) : sigdcn (uc qa) i = sigdcn (uc q) i := by
    have hiq : i ∈ dom (sig (uc q)) := by
      rw [hdqk]
      rcases mem_or_eq_of_mem_succ hi with h'' | h''
      · exact (ordinal_of_mem ordinal_omega hdq).transitive _ hk h''
      · rw [h'']; exact hk
    rw [sigdcn, sigdcn, hccs, hsig1, val_restrict _ hsfq hi hiq]
  have hkq : k ∈ dom (sig (uc q)) := by rw [hdqk]; exact hk
  have hhe := (mem_aotciEmbSet_iff.mp hh).right
  have hf1 := ((hhe.isOtciEmbedding (mem_succ_self _)).isEmbedding).isEmbedding_ts.isInjectionFromTo
  have himg : (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) k = (h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) k := by
    rw [hnew, (sigImg_spec hQ2 hq hX hh hkq).right, hje]
  refine eq_or_rel_of_seq_prefix hQ hX hy' hy hqa hq hh' hh hdqa hk (fun i hi ↦ ?_) himg
    (chdOf_eq_empty_of_ctp_eq_ct (natCast_mem_omega 2) hQ2 hqa hct) ?_
  · have hik : i ∈ depOf (Q ﹫ 2) qa := by rw [hdqa]; exact mem_succ_of_mem hi
    have hiq : i ∈ depOf (Q ﹫ 2) q := (ordinal_of_mem ordinal_omega hdq).transitive _ hk hi
    rw [tensorProdTwoAOneSeq_val hQ2 hqa hik, tensorProdTwoAOneSeq_val hQ2 hq hiq,
      hval i hi, hheq]
    have hiq' : i ∈ dom (sig (uc q)) := by rw [hdqk]; exact hiq
    have hnd : sigdcn (uc q) i ∈ ndOf (aoc (uc q) ﹫ ((1 : ℕ) : M)) := (siglvl_eq_one hUq hiq').right
    have hne : sigdcn (uc q) i ≠ sigdcn (uc q) k := by
      intro h''
      have := congrArg lbl h''
      rw [lbl_sigdcn hUq hiq', lbl_sigdcn hUq hkq] at this
      rw [this] at hi
      exact notMem_self _ hi
    have hsubk := (uc_ancOf_rel hQ2 hq hk1).right
    have hk1n : ancOf (Q ﹫ 2) q (succ k) ∈ ndOf (Q ﹫ 2) := (hTS.anc_mem_nd hq hk1).left
    have hk1d : depOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q (succ k)) = succ k := (hTS.anc_mem_nd hq hk1).right
    have hnd' : sigdcn (uc q) i ∈ ndOf (aoc (uc (ancOf (Q ﹫ 2) q (succ k))) ﹫ ((1 : ℕ) : M)) := by
      have hi1 : i ∈ dom (sig (uc (ancOf (Q ﹫ 2) q (succ k)))) := by
        rw [dom_sig_uc_eq_depOf hQ2 hk1n, hk1d]
        exact mem_succ_of_mem hi
      have h'' := (siglvl_eq_one (uc_mem_stduoci_of_mem_otci_two hQ2 hk1n) hi1).right
      have hsd' : sigdcn (uc (ancOf (Q ﹫ 2) q (succ k))) i = sigdcn (uc q) i := by
        rw [sigdcn, sigdcn, hsig1, val_restrict _ hsfq (mem_succ_of_mem hi) hiq']
      rwa [hsd'] at h''
    rw [hsd i (mem_succ_of_mem hi), embUpd_val_one_of_ne hhe.isFunction
      (by rw [hhe.dom_eq]; exact mem_succ_of_mem empty_mem_natCast_one) hf1.isFunction
      (by rw [hf1.isFunctionFromTo.dom_eq]; exact hnd) hnd' hne]
    have hanc2 : ancOf (Q ﹫ 2) qa (succ i) = ancOf (Q ﹫ 2) q (succ i) := by
      rw [← ancOf_ancOf hPs hqa (by rw [hdqa]; exact mem_succ_of_mem (mem_succ_self k))
        (succ_mem_succ_of_mem (ordinal_omega.transitive _ hdq hk) hi), hanc,
        ancOf_ancOf hPs hq (mem_succ_of_mem hk)
          (succ_mem_succ_of_mem (ordinal_omega.transitive _ hdq hk) hi)]
    rw [hanc2]
  · rcases hccmin _ hck rfl with h'' | h''
    · exact .inl h''.symm
    · exact .inr h''

end YStar

section ChdKeys

/-! ### The keys of the children of `P ⊗ Q` -/

/-- For a node `(V, (t, σ))` of `P ⊗ Q` with `|V_sig| ≥ 2`, the newest entry of `V_sig` has an
older right neighbour -/
theorem iniSegRight_ne_empty_of_mem (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) {x : M} (hx : x ∈ tensorProdTwoTwoNds P Q)
    (hm0 : ⋃₀ dom (sig (uc x)) ≠ ∅) :
    iniSegRight (uc x) (⋃₀ dom (sig (uc x))) ≠ ∅ := by
  rw [mem_tensorProdTwoTwoNds_iff] at hx
  obtain ⟨t, ht, V, hV, σ, hσ, hemb, rfl⟩ := hx
  rw [uc_orderedPair] at hm0
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hB := tensorProdATwoAOne_mem_aotci hQ hX
  have hmω := dom_sig_mem_omega_of_mem_stduoci_one hV
  have hd0 : dom (sig V) ≠ ∅ := fun h' ↦ hm0 (by rw [h', sUnion_empty])
  have hm : ⋃₀ dom (sig V) ∈ dom (sig V) := (sUnion_mem_of_ne_empty hmω hd0).right.left
  have hU := hemb.left
  set s := embTpSigs Q (aoc V) (uc t) σ with hsdef
  have hs : IsFinSeqSeq s :=
    isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUt) (aoc V) σ
  have hcon : contraction s = sig V := hU.right.left
  have he' : sig V ﹫ ⋃₀ dom (sig V) ∈ ctrSet s := by
    obtain ⟨-, -, -, hran, -⟩ := isContraction_contraction hs
    rw [← hran, hcon, (uociCond_of_mem_stduoci_one hV).right.right.right.left.left.mem_ran_iff]
    exact ⟨_, hm, rfl⟩
  obtain ⟨l, hl, k, hk, hv, hmin⟩ := exists_firstOcc hs he'
  have hfo : IsFirstOcc s (sig V ﹫ ⋃₀ dom (sig V)) l k := ⟨hl, hk, hv, hmin⟩
  -- the image `y` of the `l`-th node
  have hlsig : l ∈ dom (sig (uc t)) := by rw [← dom_embTpSigs Q (aoc V) (uc t) σ]; exact hl
  have hlrow : s ﹫ l = tpSig Q (aoc V) ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l) :=
    embTpSigs_val hUt hlsig
  have hkr := hk
  rw [hlrow] at hkr
  have hyC : (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) := by
    by_contra hnot
    rw [tpSig_eq_empty_of_not_isTpTwo hnot, dom_empty] at hkr
    exact notin_empty _ hkr
  obtain ⟨q, hq, -, h, hh, hyeq⟩ := mem_tensorProdTwoAOneNds_iff'.mp hyC
  rw [hyeq] at hyC hkr
  have hk' : k ∈ depOf (Q ﹫ 2) q := by
    rw [← dom_sig_uc_eq_depOf hQ2 hq, ← dom_tpSig_eq hyC]
    exact hkr
  have hksig : k ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hk'
  have hval (i : M) (hi : i ∈ dom (sig (uc q))) : (s ﹫ l) ﹫ i =
      !(((1 : ℕ) : M), sigImg (aoc V) q h i) := by
    rw [hlrow, hyeq, tpSig_val_eq hQ hyC hi]
    rfl
  have hje : sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V)) := by
    have h' := hv
    rw [hval k hksig, sig_val_eq_pair hV hm, orderedPair_eq_orderedPair_iff] at h'
    exact h'.right
  have hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V)) := by
    intro i hi he
    have hik : i ∈ dom (sig (uc q)) := (ordinal_of_mem ordinal_omega
      (dom_sig_mem_omega_of_mem_stduoci_one (uc_mem_stduoci_of_mem_otci_two hQ2 hq))).transitive
        _ hksig hi
    have hi' : i ∈ dom (s ﹫ l) := by rw [hlrow, hyeq, dom_tpSig_eq hyC]; exact hik
    rcases hmin l hl i hi' (by rw [hval i hik, he, sig_val_eq_pair hV hm]) with
      ⟨-, rfl⟩ | h' | ⟨-, h'⟩
    · exact notMem_self _ hi
    · exact notMem_self _ h'
    · exact notMem_self _ ((ordinal_of_mem_dom_val hs hl hk).transitive _ hi h')
  have hl' : l ∈ depOf P t := by rw [← dom_sig_uc_eq_depOf hP ht]; exact hlsig
  rw [uc_orderedPair]
  intro hR
  by_cases hk0 : k = ∅
  · subst hk0
    by_cases hl0 : l = ∅
    · -- the new entry would be the first entry of the contraction
      subst hl0
      have hk'm : ⋃₀ dom (sig V) ≠ ∅ := hm0
      have hn : dom (contraction s) = succ (⋃₀ dom (sig V)) := by
        rw [hcon]
        exact (sUnion_mem_of_ne_empty hmω hd0).right.right
      have hfo' : IsFirstOcc s (contraction s ﹫ ⋃₀ dom (sig V)) ∅ ∅ := by rw [hcon]; exact hfo
      obtain ⟨-, -, -, hran, -⟩ := isContraction_contraction hs
      have h0 : (∅ : M) ∈ dom (sig V) := by
        rw [(sUnion_mem_of_ne_empty hmω hd0).right.right]
        exact empty_mem_succ_of_mem_omega (sUnion_mem_of_ne_empty hmω hd0).left
      have hsf := (uociCond_of_mem_stduoci_one hV).right.right.right.left
      have hx0 : sig V ﹫ ∅ ∈ ctrSet s := by
        rw [← hran, hcon, hsf.left.mem_ran_iff]
        exact ⟨∅, h0, rfl⟩
      have hne : sig V ﹫ ∅ ≠ contraction s ﹫ ⋃₀ dom (sig V) := by
        rw [hcon]
        exact fun h' ↦ hk'm (hsf.right.left ∅ h0 _ hm h').symm
      obtain ⟨i, -, j, -, -, hij⟩ := occ_before hs hn hfo' _ hx0 hne
      rcases hij with h' | ⟨-, h'⟩ <;> simp at h'
    · obtain ⟨-, ⟨i0, hi0, hr⟩, hyr⟩ := ucf_anc_rel hP ht hl' hl0 hB hσ
      rw [hyeq, hr] at hyr
      exact not_rel_of_succ_none hQ hV hm hq hyC hh hk' hje hR
        (img_mem_lastSeg hP hQ hV hm ht hσ hfo hi0) hyr
  · obtain ⟨-, -, w, hw, -⟩ := ucf_ancOf_facts hQ hV hm hq hh hk' hk0 hje
    rw [hR] at hw
    simp at hw

/-- The children of a node of `P ⊗ Q`: the nodes of positive depth with that parent -/
theorem mem_chdOf_tensorProdTwoTwo_iff {p x : M} (hp : p ∈ tensorProdTwoTwoNds P Q) :
    x ∈ chdOf (tensorProdTwoTwo P Q) p ↔ x ∈ tensorProdTwoTwoNds P Q ∧
      dom (sig (uc x)) ≠ ∅ ∧ tensorProdTwoTwoPrt P Q x = p := by
  have hresC : IsSetRestrictedTo (fun x ↦ tensorProdTwoTwoNds P Q ∩₀ fun y ↦ IsPrtChd P Q x y)
      (tensorProdTwoTwoNds P Q) := isSetRestrictedTo_of_definable _
  change x ∈ (SLOTreeStructure.mk (tensorProdTwoTwoTs P Q) _).ts.chd ﹫ p ↔ _
  rw [SLOTreeStructure.ts_mk, tensorProdTwoTwoTs, TreeStructure.chd_mk]
  change x ∈ ((fun x ↦ tensorProdTwoTwoNds P Q ∩₀ fun y ↦ IsPrtChd P Q x y) ↾₀
    tensorProdTwoTwoNds P Q) ﹫ p ↔ _
  rw [val_toSetRestrictedTo hresC hp, mem_comprehension_iff]
  rfl

/-- The `uoci` of a child of a node `p` of `P ⊗ Q` has the array of an extension of `p_uc` -/
theorem exists_mem_ciExt_of_mem_chdOf_tensorProdTwoTwo (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) {p x : M} (hp : p ∈ ndOf (tensorProdTwoTwo P Q))
    (hx : x ∈ chdOf (tensorProdTwoTwo P Q) p) :
    ∃ q, !(uc p, q) ∈ ciExt ((1 : ℕ) : M) ∧ aoc q = aoc (uc x) := by
  rw [ndOf_tensorProdTwoTwo] at hp
  obtain ⟨hxn, hd, rfl⟩ := (mem_chdOf_tensorProdTwoTwo_iff hp).mp hx
  have hV := uc_mem_stduoci_of_mem_tensorProdTwoTwoNds hxn
  have hmω := dom_sig_mem_omega_of_mem_stduoci_one hV
  have hm : ⋃₀ dom (sig (uc x)) ∈ dom (sig (uc x)) := (sUnion_mem_of_ne_empty hmω hd).right.left
  rw [uc_tensorProdTwoTwoPrt]
  have hU := iniSeg_mem_stduoci hV hm
  have hcase : sig (iniSeg (uc x) (⋃₀ dom (sig (uc x)))) = ∅ ∨
      ucflvl (iniSeg (uc x) (⋃₀ dom (sig (uc x)))) = ((1 : ℕ) : M) := by
    by_cases hk0 : ⋃₀ dom (sig (uc x)) = ∅
    · left
      rw [sig_iniSeg, hk0, restrict_empty]
    · right
      obtain ⟨w, -, -, hw⟩ :=
        iniSegUcf_of_ne_empty hV hm (iniSegRight_ne_empty_of_mem hP hQ hxn hk0)
      rw [ucflvl, (ucflvldcn_iniSeg hk0).left, hw, lvl_orderedPair]
  obtain ⟨q, hq⟩ := (exists_mem_ciExt_one_iff hU ctp_iniSeg).mpr hcase
  exact ⟨q, hq, aoc_eq_of_mem_ciExt_iniSeg hV hm hq⟩

/-- The elements of a linearly ordered set of children of `p` are children of `p` with its key -/
theorem mem_chdOf_of_mem_losSet_chdlosOf {T p r D : M} (hT : IsSLOT T) (hp : p ∈ ndOf T)
    (hr : r ∈ losSet (chdlosOf T p ﹫ D)) : r ∈ chdOf T p ∧ left r ﹫ ∅ = D := by
  have hS : (SLOTreeStructure.ofM T).IsSLOTreeStructure := hT
  have hTs := hS.isTreeStructure
  by_cases hne : (SLOTreeStructure.ofM T).chd ﹫ p = ∅
  · exfalso
    have h : p ∉ dom (SLOTreeStructure.ofM T).chdlos := fun h ↦
      (hS.mem_dom_chdlos_iff.mp h).right hne
    rw [chdlosOf, val_eq_empty_of_not_mem_dom h, val_eq_empty_of_not_mem_dom (by simp),
      losSet_empty] at hr
    simp at hr
  have hX : (SLOTreeStructure.ofM T).chd ﹫ p ∈ (SLOTreeStructure.ofM T).sblptn := by
    rw [TreeStructure.mem_sblptn_iff, hTs.isFunction_chd.mem_ran_iff, hTs.dom_chd]
    exact ⟨.inr ⟨p, hp, rfl⟩, hne⟩
  rw [chdlosOf, hS.chdlos_val (hS.mem_dom_chdlos_iff.mpr ⟨hp, hne⟩)] at hr
  by_cases hD : D ∈ dom ((SLOTreeStructure.ofM T).losfn ﹫ ((SLOTreeStructure.ofM T).chd ﹫ p))
  · exact (hS.mem_losSet_iff hX hD r).mp hr
  · rw [val_eq_empty_of_not_mem_dom hD, losSet_empty] at hr
    simp at hr

/-- The children of a node `p` of `P ⊗ Q` with the key of an extension `q` of `p_uc` have the
signature of `q` -/
theorem sig_uc_eq_of_mem_losSet_chdlosOf_tensorProdTwoTwo (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) {p q r : M} (hp : p ∈ ndOf (tensorProdTwoTwo P Q))
    (hq : !(uc p, q) ∈ ciExt ((1 : ℕ) : M))
    (hr : r ∈ losSet (chdlosOf (tensorProdTwoTwo P Q) p ﹫ aoc q)) : sig (uc r) = sig q := by
  obtain ⟨hrc, hkey⟩ := mem_chdOf_of_mem_losSet_chdlosOf (isSLOT_tensorProdTwoTwo hP hQ) hp hr
  obtain ⟨q', hq', hq'a⟩ := exists_mem_ciExt_of_mem_chdOf_tensorProdTwoTwo hP hQ hp hrc
  rw [eq_of_mem_ciExt_one hq' hq] at hq'a
  have hrn : r ∈ tensorProdTwoTwoNds P Q := by
    rw [← ndOf_tensorProdTwoTwo]
    exact mem_ndOf_of_mem_chdOf (isSLOT_tensorProdTwoTwo hP hQ) hrc
  exact sig_eq_of_aoc_eq (natCast_mem_omega 1) (uc_mem_stduoci_of_mem_tensorProdTwoTwoNds hrn)
    (mem_ciExt_props hq).right.left hq'a.symm

end ChdKeys

section Extend

/-! ### Extending a sequence of sequences at the end -/

variable {s s' c x : M}

/-- `s'` extends `s` at the end: the positions of `s` are positions of `s'` with the same entries,
and the other positions of `s'` come after all positions of `s` -/
def IsSeqSeqExt (s s' : M) : Prop :=
  (∀ i ∈ dom s, ∀ j ∈ dom (s ﹫ i), i ∈ dom s' ∧ j ∈ dom (s' ﹫ i) ∧
    (s' ﹫ i) ﹫ j = (s ﹫ i) ﹫ j) ∧
  ∀ i' ∈ dom s', ∀ j' ∈ dom (s' ﹫ i'), (i' ∈ dom s ∧ j' ∈ dom (s ﹫ i')) ∨
    ∀ i ∈ dom s, ∀ j ∈ dom (s ﹫ i), i ∈ i' ∨ (i = i' ∧ j ∈ j')

theorem ctrSet_subset_of_isSeqSeqExt (hs : IsFinSeqSeq s) (hs' : IsFinSeqSeq s')
    (hE : IsSeqSeqExt s s') : ctrSet s ⊆ ctrSet s' := by
  intro z hz
  rw [mem_ctrSet_iff hs] at hz
  obtain ⟨i, hi, j, hj, rfl⟩ := hz
  obtain ⟨hi', hj', he⟩ := hE.left i hi j hj
  rw [mem_ctrSet_iff hs']
  exact ⟨i, hi', j, hj', he⟩

omit [ModelsZF M] in
theorem occursBefore_of_isSeqSeqExt (hE : IsSeqSeqExt s s') {y z : M}
    (h : OccursBefore s y z) : OccursBefore s' y z := by
  obtain ⟨i, hi, j, hj, hy, hpre⟩ := h
  obtain ⟨hi', hj', he⟩ := hE.left i hi j hj
  refine ⟨i, hi', j, hj', he.trans hy, fun i' hi'' j' hj'' hz ↦ ?_⟩
  rcases hE.right i' hi'' j' hj'' with ⟨hi₁, hj₁⟩ | hlt
  · obtain ⟨-, -, he'⟩ := hE.left i' hi₁ j' hj₁
    exact hpre i' hi₁ j' hj₁ (he'.symm.trans hz)
  · exact hlt i hi j hj

/-- Extending `s` at the end by old entries keeps the contraction -/
theorem isContraction_of_isSeqSeqExt_old (hs : IsFinSeqSeq s) (hs' : IsFinSeqSeq s')
    (hc : IsContraction s c) (hE : IsSeqSeqExt s s')
    (hold : ∀ i' ∈ dom s', ∀ j' ∈ dom (s' ﹫ i'), (s' ﹫ i') ﹫ j' ∈ ctrSet s) :
    IsContraction s' c := by
  obtain ⟨hcf, hcd, hci, hcr, hco⟩ := hc
  refine ⟨hcf, hcd, hci, ?_, fun k hk l hl hkl ↦ occursBefore_of_isSeqSeqExt hE (hco k hk l hl hkl)⟩
  rw [hcr]
  ext z
  refine ⟨fun hz ↦ ctrSet_subset_of_isSeqSeqExt hs hs' hE hz, fun hz ↦ ?_⟩
  rw [mem_ctrSet_iff hs'] at hz
  obtain ⟨i, hi, j, hj, rfl⟩ := hz
  exact hold i hi j hj

/-- Extending `s` at the end by old entries and a new entry `x` appends `x` to the contraction -/
theorem isContraction_of_isSeqSeqExt (hs : IsFinSeqSeq s) (hs' : IsFinSeqSeq s')
    (hc : IsContraction s c) (hE : IsSeqSeqExt s s')
    (hnew : ∀ i' ∈ dom s', ∀ j' ∈ dom (s' ﹫ i'),
      (s' ﹫ i') ﹫ j' ∈ ctrSet s ∨ (s' ﹫ i') ﹫ j' = x)
    (hx : x ∈ ctrSet s') (hxs : x ∉ ctrSet s) {c' : M} (hc'f : IsFunction c')
    (hc'd : dom c' = succ (dom c)) (hc'r : ∀ k ∈ dom c, c' ﹫ k = c ﹫ k)
    (hc'x : c' ﹫ dom c = x) : IsContraction s' c' := by
  obtain ⟨hcf, hcd, hci, hcr, hco⟩ := hc
  have hco' := ordinal_of_mem ordinal_omega hcd
  have hcmem {k : M} (hk : k ∈ dom c) : c ﹫ k ∈ ctrSet s := by
    rw [← hcr, hcf.mem_ran_iff]; exact ⟨k, hk, rfl⟩
  refine ⟨hc'f, by rw [hc'd]; exact succ_mem_omega hcd, fun k hk l hl hkl ↦ ?_, ?_,
    fun k hk l hl hkl ↦ ?_⟩
  · rw [hc'd] at hk hl
    rcases mem_or_eq_of_mem_succ hk with hk | rfl <;> rcases mem_or_eq_of_mem_succ hl with hl | rfl
    · rw [hc'r k hk, hc'r l hl] at hkl
      exact hci k hk l hl hkl
    · rw [hc'r k hk, hc'x] at hkl
      exact (hxs (hkl ▸ hcmem hk)).elim
    · rw [hc'r l hl, hc'x] at hkl
      exact (hxs (hkl ▸ hcmem hl)).elim
    · rfl
  · ext z
    rw [hc'f.mem_ran_iff, hc'd]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases mem_or_eq_of_mem_succ hk with hk | rfl
      · rw [hc'r k hk]
        exact ctrSet_subset_of_isSeqSeqExt hs hs' hE (hcmem hk)
      · rw [hc'x]; exact hx
    · intro hz
      have hz' := hz
      rw [mem_ctrSet_iff hs'] at hz'
      obtain ⟨i, hi, j, hj, rfl⟩ := hz'
      rcases hnew i hi j hj with h | h
      · rw [← hcr, hcf.mem_ran_iff] at h
        obtain ⟨k, hk, hke⟩ := h
        exact ⟨k, mem_succ_of_mem hk, (hc'r k hk).trans hke⟩
      · exact ⟨dom c, mem_succ_self _, hc'x.trans h.symm⟩
  · rw [hc'd] at hk hl
    rcases mem_or_eq_of_mem_succ hl with hl | rfl
    · have hk' : k ∈ dom c := hco'.transitive _ hl hkl
      rw [hc'r k hk', hc'r l hl]
      exact occursBefore_of_isSeqSeqExt hE (hco k hk' l hl hkl)
    · rw [hc'r k hkl, hc'x]
      have h := hcmem hkl
      rw [mem_ctrSet_iff hs] at h
      obtain ⟨i, hi, j, hj, hij⟩ := h
      obtain ⟨hi', hj', he⟩ := hE.left i hi j hj
      refine ⟨i, hi', j, hj', he.trans hij, fun i' hi'' j' hj'' hz ↦ ?_⟩
      rcases hE.right i' hi'' j' hj'' with ⟨hi₁, hj₁⟩ | hlt
      · obtain ⟨-, -, he'⟩ := hE.left i' hi₁ j' hj₁
        exfalso
        apply hxs
        rw [mem_ctrSet_iff hs]
        exact ⟨i', hi₁, j', hj₁, he'.symm.trans hz⟩
      · exact hlt i hi j hj

end Extend


section ChdLos

/-! ### The linearly ordered sets of the children of a node of `P ⊗ Q` -/

variable {P Q : M}

omit [ModelsZF M] in
theorem aoc_uc_eq_left_val (c : M) : aoc (uc c) = left c ﹫ ∅ := by simp [aoc, uc]

/-- The children of `p` in `P ⊗ Q` with key `D`, ordered by the order of `P ⊗ Q` -/
theorem chdlosOf_tensorProdTwoTwo_val (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {p c : M} (hp : p ∈ ndOf (tensorProdTwoTwo P Q)) (hc : c ∈ chdOf (tensorProdTwoTwo P Q) p) :
    chdlosOf (tensorProdTwoTwo P Q) p ﹫ aoc (uc c) =
      keyLos (tensorProdTwoTwoOdr P Q) (chdOf (tensorProdTwoTwo P Q) p) (aoc (uc c)) := by
  have hT := isSLOT_tensorProdTwoTwo hP hQ
  have hS : (SLOTreeStructure.ofM (tensorProdTwoTwo P Q)).IsSLOTreeStructure := hT
  have hTs := hS.isTreeStructure
  have hne : (SLOTreeStructure.ofM (tensorProdTwoTwo P Q)).chd ﹫ p ≠ ∅ := by
    rw [ne_empty_iff]
    exact ⟨c, hc⟩
  have hX : (SLOTreeStructure.ofM (tensorProdTwoTwo P Q)).chd ﹫ p ∈
      (SLOTreeStructure.ofM (tensorProdTwoTwo P Q)).sblptn := by
    rw [TreeStructure.mem_sblptn_iff, hTs.isFunction_chd.mem_ran_iff, hTs.dom_chd]
    exact ⟨.inr ⟨p, hp, rfl⟩, hne⟩
  rw [chdlosOf, hS.chdlos_val (hS.mem_dom_chdlos_iff.mpr ⟨hp, hne⟩)]
  have hres : IsSetRestrictedTo (fun X ↦ keyLosFn (tensorProdTwoTwoOdr P Q) X)
      (tensorProdTwoTwoTs P Q).sblptn := isSetRestrictedTo_of_definable _
  have hlf : (SLOTreeStructure.ofM (tensorProdTwoTwo P Q)).losfn =
      (fun X ↦ keyLosFn (tensorProdTwoTwoOdr P Q) X) ↾₀ (tensorProdTwoTwoTs P Q).sblptn := by
    change (SLOTreeStructure.mk (tensorProdTwoTwoTs P Q) _).losfn = _
    rw [SLOTreeStructure.losfn_mk]
  have hX' : (SLOTreeStructure.ofM (tensorProdTwoTwo P Q)).chd ﹫ p ∈
      (tensorProdTwoTwoTs P Q).sblptn := by
    change _ ∈ (SLOTreeStructure.mk (tensorProdTwoTwoTs P Q) _).ts.sblptn at hX
    rw [SLOTreeStructure.ts_mk] at hX
    exact hX
  rw [hlf, val_toSetRestrictedTo hres hX']
  have hk : IsSetRestrictedTo (fun a ↦ left a ﹫ ∅)
      ((SLOTreeStructure.ofM (tensorProdTwoTwo P Q)).chd ﹫ p) := isSetRestrictedTo_of_definable _
  have : ClassFunction.Definable (fun D ↦ keyLos (tensorProdTwoTwoOdr P Q)
      ((SLOTreeStructure.ofM (tensorProdTwoTwo P Q)).chd ﹫ p) D) Set.univ :=
    ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ R' X',
      R' = tensorProdTwoTwoOdr P Q ∧
      X' = (SLOTreeStructure.ofM (tensorProdTwoTwo P Q)).chd ﹫ p ∧
      keyLos R' X' (xs 0) = xs 1) fun u w ↦ by simp
  have hv : IsSetRestrictedTo (fun D ↦ keyLos (tensorProdTwoTwoOdr P Q)
      ((SLOTreeStructure.ofM (tensorProdTwoTwo P Q)).chd ﹫ p) D)
      (keysOf ((SLOTreeStructure.ofM (tensorProdTwoTwo P Q)).chd ﹫ p)) :=
    isSetRestrictedTo_of_definable _
  have hD : aoc (uc c) ∈ keysOf ((SLOTreeStructure.ofM (tensorProdTwoTwo P Q)).chd ﹫ p) := by
    rw [keysOf, mem_ran_toSetRestrictedTo_iff hk, aoc_uc_eq_left_val]
    exact ⟨c, hc, rfl⟩
  rw [keyLosFn, val_toSetRestrictedTo hv hD]
  rfl

/-- A child `x` of `p` that is below all other children with its key is least in their linearly
ordered set -/
theorem isLeastLos_of_forall_tensorProdTwoTwo (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) {p x : M} (hp : p ∈ ndOf (tensorProdTwoTwo P Q))
    (hx : x ∈ chdOf (tensorProdTwoTwo P Q) p)
    (hmin : ∀ r ∈ chdOf (tensorProdTwoTwo P Q) p, aoc (uc r) = aoc (uc x) →
      r = x ∨ x [tensorProdTwoTwoOdr P Q] r) :
    IsLeastLos (chdlosOf (tensorProdTwoTwo P Q) p ﹫ aoc (uc x)) x := by
  have hT := isSLOT_tensorProdTwoTwo hP hQ
  have hB := isStrictLinearOrderedSet_chdlosOf hT hp hx
  rw [← aoc_uc_eq_left_val] at hB
  rw [chdlosOf_tensorProdTwoTwo_val hP hQ hp hx] at hB ⊢
  rw [keyLos, isStrictLinearOrderedSet_orderedPair_iff] at hB
  have hxB : x ∈ keyBlock (chdOf (tensorProdTwoTwo P Q) p) (aoc (uc x)) := by
    rw [mem_keyBlock_iff, ← aoc_uc_eq_left_val]
    exact ⟨hx, rfl⟩
  rw [keyLos]
  refine ⟨by rw [losSet_orderedPair]; exact hxB, fun y hy hyx ↦ ?_⟩
  rw [losSet_orderedPair] at hy
  rw [losOdr_orderedPair] at hyx
  have hy' := hy
  rw [mem_keyBlock_iff, ← aoc_uc_eq_left_val] at hy'
  rcases hmin y hy'.left hy'.right with rfl | hxy
  · exact hB.irrefl _ hyx
  · refine hB.asymm hyx ?_
    rw [mem_inter_iff]
    exact ⟨hxy, by rw [pair_mem_sprod_iff]; exact ⟨hxB, hy⟩⟩

/-- The elements of the linearly ordered set of the children of `p` with key `D` -/
theorem mem_losSet_chdlosOf_tensorProdTwoTwo_iff (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) {p r : M} (hp : p ∈ ndOf (tensorProdTwoTwo P Q)) (D : M) :
    r ∈ losSet (chdlosOf (tensorProdTwoTwo P Q) p ﹫ D) ↔
      r ∈ chdOf (tensorProdTwoTwo P Q) p ∧ aoc (uc r) = D := by
  constructor
  · intro hr
    rw [aoc_uc_eq_left_val]
    exact mem_chdOf_of_mem_losSet_chdlosOf (isSLOT_tensorProdTwoTwo hP hQ) hp hr
  · rintro ⟨hr, rfl⟩
    rw [chdlosOf_tensorProdTwoTwo_val hP hQ hp hr, keyLos, losSet_orderedPair, mem_keyBlock_iff,
      ← aoc_uc_eq_left_val]
    exact ⟨hr, rfl⟩

/-- A least element is the given least element -/
theorem eq_of_isLeastLos_tensorProdTwoTwo (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) {p x r : M} (hp : p ∈ ndOf (tensorProdTwoTwo P Q))
    (hx : x ∈ chdOf (tensorProdTwoTwo P Q) p)
    (hmin : ∀ r ∈ chdOf (tensorProdTwoTwo P Q) p, aoc (uc r) = aoc (uc x) →
      r = x ∨ x [tensorProdTwoTwoOdr P Q] r)
    (hr : IsLeastLos (chdlosOf (tensorProdTwoTwo P Q) p ﹫ aoc (uc x)) r) : r = x := by
  have hrm := hr.left
  rw [mem_losSet_chdlosOf_tensorProdTwoTwo_iff hP hQ hp] at hrm
  rcases hmin r hrm.left hrm.right with h | hxr
  · exact h
  · exfalso
    refine hr.right x ((mem_losSet_chdlosOf_tensorProdTwoTwo_iff hP hQ hp _).mpr ⟨hx, rfl⟩) ?_
    rw [chdlosOf_tensorProdTwoTwo_val hP hQ hp hx, keyLos, losOdr_orderedPair, mem_inter_iff,
      pair_mem_sprod_iff, mem_keyBlock_iff, mem_keyBlock_iff, ← aoc_uc_eq_left_val,
      ← aoc_uc_eq_left_val]
    exact ⟨hxr, ⟨hx, rfl⟩, hrm.left, hrm.right⟩

end ChdLos

section SeqCmp

/-! ### Comparing sequences with a common prefix -/

variable {P T t σ t' σ' k : M}

/-- Comparing the sequences of two labels `(t, σ)`, `(t', σ')` that agree before `k`, where `t`
has depth `k + 1`: if the images at `k` are in order, or are equal while `t` is childless and at
most the ancestor of `t'` of depth `k + 1` in the sibling order, then `(t, σ) ≤ (t', σ')` -/
theorem eq_or_bkLt_of_seq_prefix (hP : P ∈ otci ((2 : ℕ) : M)) (hT : T ∈ aotci ((1 : ℕ) : M))
    (ht : t ∈ ndOf P) (ht' : t' ∈ ndOf P)
    (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) T)
    (hσ' : σ' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t')) T)
    (hdt : depOf P t = succ k) (hk' : k ∈ depOf P t')
    (hpre : ∀ i ∈ k, tensorProdTwoAOneSeq P !(t, σ) ﹫ i = tensorProdTwoAOneSeq P !(t', σ') ﹫ i)
    (hcase : ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) k) [odrOne (T ﹫ ((1 : ℕ) : M))]
        ((σ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t') k) ∨
      ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) k = (σ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t') k ∧
        chdOf P t = ∅ ∧ (t = ancOf P t' (succ k) ∨ t [sblOdrOf P] ancOf P t' (succ k)))) :
    !(t, σ) = !(t', σ') ∨
      BKLt (lexProd (odrOne (T ﹫ ((1 : ℕ) : M))) (ndOf (T ﹫ ((1 : ℕ) : M))) (sblOdrOf P)
        (ndOf P)) (tensorProdTwoAOneSeq P !(t, σ)) (tensorProdTwoAOneSeq P !(t', σ')) := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  have hdt' := hTS.dep_mem_omega ht'
  have hkt : k ∈ depOf P t := by rw [hdt]; exact mem_succ_self k
  have hsf := isFunction_tensorProdTwoAOneSeq P !(t, σ)
  have hsf' := isFunction_tensorProdTwoAOneSeq P !(t', σ')
  have hres : tensorProdTwoAOneSeq P !(t, σ) ↾ k = tensorProdTwoAOneSeq P !(t', σ') ↾ k := by
    have hks : k ⊆ dom (tensorProdTwoAOneSeq P !(t, σ)) := by
      rw [tensorProdTwoAOneSeq_dom, hdt]
      exact fun _ h' ↦ mem_succ_of_mem h'
    have hks' : k ⊆ dom (tensorProdTwoAOneSeq P !(t', σ')) := by
      rw [tensorProdTwoAOneSeq_dom]
      exact (ordinal_of_mem ordinal_omega hdt').transitive _ hk'
    refine (hsf.restrict _).ext (hsf'.restrict _)
      (by rw [dom_restrict_of_subset hsf hks, dom_restrict_of_subset hsf' hks']) fun i hi ↦ ?_
    rw [dom_restrict_of_subset hsf hks] at hi
    rw [val_restrict _ hsf hi (hks hi), val_restrict _ hsf' hi (hks' hi), hpre i hi]
  have hm1 := tensorProdTwoAOneSeq_val_mem hP ht hσ hkt
  have hm2 := tensorProdTwoAOneSeq_val_mem hP ht' hσ' hk'
  rw [tensorProdTwoAOneSeq_val hP ht hkt] at hm1
  rw [tensorProdTwoAOneSeq_val hP ht' hk'] at hm2
  rw [pair_mem_sprod_iff] at hm1 hm2
  have hta : ancOf P t (succ k) = t := by rw [← hdt]; exact hTS.anc_dep ht
  have hbk : (∃ k' ∈ dom (tensorProdTwoAOneSeq P !(t, σ)),
      k' ∈ dom (tensorProdTwoAOneSeq P !(t', σ')) ∧
      tensorProdTwoAOneSeq P !(t, σ) ↾ k' = tensorProdTwoAOneSeq P !(t', σ') ↾ k' ∧
      (tensorProdTwoAOneSeq P !(t, σ) ﹫ k') [lexProd (odrOne (T ﹫ ((1 : ℕ) : M)))
        (ndOf (T ﹫ ((1 : ℕ) : M))) (sblOdrOf P) (ndOf P)] (tensorProdTwoAOneSeq P !(t', σ') ﹫ k')) →
      BKLt (lexProd (odrOne (T ﹫ ((1 : ℕ) : M))) (ndOf (T ﹫ ((1 : ℕ) : M))) (sblOdrOf P)
        (ndOf P)) (tensorProdTwoAOneSeq P !(t, σ)) (tensorProdTwoAOneSeq P !(t', σ')) :=
    fun h ↦ .inr h
  rcases hcase with hlt | ⟨himg, hchd, hsbl⟩
  · right
    refine hbk ⟨k, by rw [tensorProdTwoAOneSeq_dom]; exact hkt,
      by rw [tensorProdTwoAOneSeq_dom]; exact hk', hres, ?_⟩
    rw [tensorProdTwoAOneSeq_val hP ht hkt, tensorProdTwoAOneSeq_val hP ht' hk', rel_lexProd_iff]
    exact ⟨hm1, hm2, .inl hlt⟩
  rcases hsbl with heq | hlt
  · -- `t'` lies below the childless `t`, so it is `t`
    have htt : t' = t := by
      by_contra hne
      have hlt' : succ k ∈ depOf P t' := by
        rcases mem_or_eq_of_mem_succ (succ_mem_succ_of_mem hdt' hk') with h' | h'
        · exact h'
        · exfalso
          apply hne
          rw [heq, h']
          exact (hTS.anc_dep ht').symm
      have hc := hTS.anc_succ_mem_chd ht' hlt'
      change ancOf P t' (succ (succ k)) ∈ chdOf P (ancOf P t' (succ k)) at hc
      rw [← heq, hchd] at hc
      simp at hc
    subst htt
    left
    have hseq : tensorProdTwoAOneSeq P !(t', σ) = tensorProdTwoAOneSeq P !(t', σ') := by
      refine hsf.ext hsf' (by rw [tensorProdTwoAOneSeq_dom, tensorProdTwoAOneSeq_dom]) fun i hi ↦ ?_
      rw [tensorProdTwoAOneSeq_dom, hdt] at hi
      rcases mem_or_eq_of_mem_succ hi with hi | rfl
      · exact hpre i hi
      · rw [tensorProdTwoAOneSeq_val hP ht hkt, tensorProdTwoAOneSeq_val hP ht hkt, himg]
    exact eq_of_tensorProdTwoAOneSeq_eq hP hT ht ht hσ hσ' hseq
  · right
    refine hbk ⟨k, by rw [tensorProdTwoAOneSeq_dom]; exact hkt,
      by rw [tensorProdTwoAOneSeq_dom]; exact hk', hres, ?_⟩
    rw [tensorProdTwoAOneSeq_val hP ht hkt, tensorProdTwoAOneSeq_val hP ht' hk', rel_lexProd_iff]
    rw [hta] at hm1 ⊢
    exact ⟨hm1, hm2, .inr ⟨himg, hlt⟩⟩

end SeqCmp

section NdsPair

variable {P Q V t σ : M}

/-- The node conditions for `(V, (t, σ))` -/
theorem pair_mem_tensorProdTwoTwoNds_iff : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q ↔
    t ∈ ndOf P ∧ V ∈ stduoci ((1 : ℕ) : M) ∧
      σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q (aoc V)) ∧
      IsTensorProdTwoTwoEmb Q t V σ := by
  rw [mem_tensorProdTwoTwoNds_iff]
  constructor
  · rintro ⟨t', ht', V', hV', σ', hσ', hemb, he⟩
    rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨ht', hV', hσ', hemb⟩
  · rintro ⟨ht, hV, hσ, hemb⟩
    exact ⟨t, ht, V, hV, σ, hσ, hemb, rfl⟩

variable {V' t' σ' k : M}

/-- Comparing two nodes of `P ⊗ Q` with the same key whose sequences agree before `k` -/
theorem eq_or_rel_tensorProdTwoTwoOdr_of_seq_prefix (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hx : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q) (hr : !(V', !(t', σ')) ∈ tensorProdTwoTwoNds P Q)
    (haoc : aoc V = aoc V')
    (hdt : depOf P t = succ k) (hk' : k ∈ depOf P t')
    (hpre : ∀ i ∈ k, tensorProdTwoAOneSeq P !(t, σ) ﹫ i = tensorProdTwoAOneSeq P !(t', σ') ﹫ i)
    (hcase : ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) k)
        [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
        ((σ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t') k) ∨
      ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) k = (σ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t') k ∧
        chdOf P t = ∅ ∧ (t = ancOf P t' (succ k) ∨ t [sblOdrOf P] ancOf P t' (succ k)))) :
    !(V, !(t, σ)) = !(V', !(t', σ')) ∨
      !(V, !(t, σ)) [tensorProdTwoTwoOdr P Q] !(V', !(t', σ')) := by
  have hx' := hx
  have hr' := hr
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hx' hr'
  obtain ⟨ht, hV, hσ, hemb⟩ := hx'
  obtain ⟨ht', hV', hσ', hemb'⟩ := hr'
  rw [← haoc] at hσ'
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hB := tensorProdATwoAOne_mem_aotci hQ hX
  rcases eq_or_bkLt_of_seq_prefix hP hB ht ht' hσ hσ' hdt hk' hpre hcase with he | hlt
  · rw [orderedPair_eq_orderedPair_iff] at he
    obtain ⟨rfl, rfl⟩ := he
    left
    rw [eq_of_isUociEmb hV hV' haoc hemb.left hemb'.left]
  · right
    rw [rel_tensorProdTwoTwoOdr_iff]
    refine ⟨⟨hx, hr⟩, ?_, ?_⟩
    · rw [uc_orderedPair, uc_orderedPair, haoc]
    · rw [lbl_orderedPair, lbl_orderedPair, uc_orderedPair]
      exact hlt

end NdsPair

end TensorProd

end FirstOrder.Language.MemStructure
