/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.Tree
/-!
# The parent of a node of `P ⊗ Q`

The pieces of the parent of a node of `P ⊗ Q` of depth `m > 1`: the nearest old node `D` above
the image of the newest entry, and the two cases of the parent.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M]

section TensorProd

variable {P Q T W : M}

section Slot

variable {U k x y : M}

section IniSegSub

variable {Q V X w k a b : M}

/-- The nodes of the first `|V_sig| - 1` entries are the level-`1` nodes other than the last one -/
theorem mem_iniSegNds_last_iff (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) :
    w ∈ iniSegNds V (⋃₀ dom (sig V)) ↔
      w ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) ∧ w ≠ sigdcn V (⋃₀ dom (sig V)) := by
  have hdω := dom_sig_mem_omega_of_mem_stduoci_one hV
  have hne : dom (sig V) ≠ ∅ := fun h ↦ by rw [h] at hm; simp at hm
  obtain ⟨-, -, hdeq⟩ := sUnion_mem_of_ne_empty hdω hne
  rw [mem_iniSegNds_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hid : i ∈ dom (sig V) := subset_dom_sig_of_mem hV hm hi
    refine ⟨(siglvl_eq_one hV hid).right, fun h ↦ ?_⟩
    have := congrArg lbl h
    rw [lbl_sigdcn hV hid, lbl_sigdcn hV hm] at this
    rw [this] at hi
    exact notMem_self _ hi
  · rintro ⟨hw, hne'⟩
    obtain ⟨hl, -⟩ := sig_val_lbl_of_mem hV hw
    rw [hdeq] at hl
    rcases mem_or_eq_of_mem_succ hl with h | h
    · exact ⟨lbl w, h, sigdcn_lbl_of_mem hV hw⟩
    · exact (hne' (by rw [← h, sigdcn_lbl_of_mem hV hw])).elim

/-- The level-`1` tree of an initial segment is a subtree -/
theorem isSubOne_iniSegAoc (hV : V ∈ stduoci ((1 : ℕ) : M)) (hk : k ∈ dom (sig V)) :
    IsSubOne (iniSegAoc V k ﹫ ((1 : ℕ) : M)) (aoc V ﹫ ((1 : ℕ) : M)) := by
  rw [IsSubOne, iniSegAoc_val_one hV, ndOf_rtLosSLOT, losSet_orderedPair]
  refine ⟨iniSegNds_subset hV hk, fun a ha b hb ↦ ?_⟩
  have hne : losSet !(iniSegNds V k, iniSegOdr V ↾↾ iniSegNds V k) ≠ ∅ := by
    rw [losSet_orderedPair]
    intro h
    rw [h] at ha
    simp at ha
  rw [odrOne_rtLosSLOT hne, losOdr_orderedPair, rel_restrict₂_iff]
  exact ⟨fun h ↦ h.left, fun h ↦ ⟨h, ha, hb⟩⟩

/-- On the nodes from `Q(2)`, the order of `(Q ⊗ X)(1)` is that of `Q(2) ⊗ X` -/
theorem rel_odrOne_tensorProdATwoAOne_iff_of_mem (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hX : X ∈ aotci ((1 : ℕ) : M)) (ha : a ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) :
    a [odrOne (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M))] b ↔
      b ∈ tensorProdTwoAOneNds (Q ﹫ 2) X ∧
        TensorProdTwoAOneLt (Q ﹫ 2) X (lbl a) (lbl b) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hB1 := val_mem_otci_of_mem_aotci (tensorProdATwoAOneBase_mem_aotci hQ X) (mem_succ_self _)
  have hC := tensorProdTwoAOne_mem_otci hQ2 hX
  obtain ⟨hRB, hsB, -⟩ := rtlosOf_of_mem_otci_one hB1
  obtain ⟨-, hsC, -⟩ := rtlosOf_of_mem_otci_one hC
  have hdisj := ndOf_base_inter_ndOf_tensorProdTwoAOne hQ X
  have haC : a ∈ ndOf (tensorProdTwoAOne (Q ﹫ 2) X) := by
    rw [ndOf_tensorProdTwoAOne]
    exact ha
  have haB : a ∉ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) := fun h ↦ by
    have h' : a ∈ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ∩
        ndOf (tensorProdTwoAOne (Q ﹫ 2) X) := by
      rw [mem_inter_iff]
      exact ⟨h, haC⟩
    rw [hdisj] at h'
    simp at h'
  have hne : losSet (losConcat (rtlosOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ﹫ trvAZero)
      (rtlosOf (tensorProdTwoAOne (Q ﹫ 2) X) ﹫ trvAZero)) ≠ ∅ := by
    rw [losConcat, losSet_orderedPair, hsC]
    intro h
    have h' : a ∈ losSet (rtlosOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ﹫ trvAZero) ∪
        ndOf (tensorProdTwoAOne (Q ﹫ 2) X) := by
      rw [mem_union_iff]
      exact .inr haC
    rw [h] at h'
    simp at h'
  have hRBo : IsStrictLinearOrder (odrOne (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)))
      (ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M))) := hRB
  rw [tensorProdATwoAOne_val_one_eq hQ, odrOne_rtLosSLOT hne, losConcat, losOdr_orderedPair,
    rel_concat_iff, hsB]
  change a [odrOne (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M))] b ∨
    a [odrOne (tensorProdTwoAOne (Q ﹫ 2) X)] b ∨ _ ↔ _
  rw [rel_odrOne_tensorProdTwoAOne_iff ha]
  constructor
  · rintro (h | h | h)
    · exact (haB (hRBo.mem_left h)).elim
    · exact ⟨h.left.right, h.right⟩
    · exact (haB h.left).elim
  · intro h
    exact .inr (.inl ⟨⟨ha, h.left⟩, h.right⟩)

section EmbSub

variable {A B B' f P q h : M}

/-- The embeddings into an array whose level-`1` tree is a subtree -/
theorem mem_aotciEmbSet_iff_of_isSubOne (hA : A ∈ aotci ((1 : ℕ) : M))
    (hB : B ∈ aotci ((1 : ℕ) : M)) (hB' : B' ∈ aotci ((1 : ℕ) : M)) (h0 : B' ﹫ ∅ = B ﹫ ∅)
    (hsub : IsSubOne (B' ﹫ ((1 : ℕ) : M)) (B ﹫ ((1 : ℕ) : M))) :
    f ∈ aotciEmbSet ((1 : ℕ) : M) A B' ↔
      f ∈ aotciEmbSet ((1 : ℕ) : M) A B ∧ ran (f ﹫ ((1 : ℕ) : M)) ⊆ ndOf (B' ﹫ ((1 : ℕ) : M)) := by
  obtain ⟨hAf, hAdom, -⟩ := mem_aotci_iff.mp hA
  obtain ⟨hTf, hTdom, -⟩ := mem_aotci_iff.mp hB
  obtain ⟨hT'f, hT'dom, -⟩ := mem_aotci_iff.mp hB'
  have h1s : ((1 : ℕ) : M) ∈ succ ((1 : ℕ) : M) := mem_succ_self _
  have hA1 := val_mem_otci_of_mem_aotci hA h1s
  have hZ := val_mem_otci_of_mem_aotci hB h1s
  have hZ' := val_mem_otci_of_mem_aotci hB' h1s
  constructor
  · intro hf
    have he := (mem_aotciEmbSet_iff.mp hf).right
    have he1 := (isOtciEmbedding_iff_of_isSubOne hA1 hZ' hZ hsub).mp (he.isOtciEmbedding h1s)
    refine ⟨mem_aotciEmbSet_of_isAotciEmbedding hAf hAdom hTf hTdom
      ⟨he.isFunction, he.dom_eq, fun {i} hi ↦ ?_⟩, he1.right⟩
    rcases mem_succ_one_cases hi with rfl | rfl
    · rw [← h0]
      exact he.isOtciEmbedding hi
    · exact he1.left
  · rintro ⟨hf, hran⟩
    have he := (mem_aotciEmbSet_iff.mp hf).right
    refine mem_aotciEmbSet_of_isAotciEmbedding hAf hAdom hT'f hT'dom
      ⟨he.isFunction, he.dom_eq, fun {i} hi ↦ ?_⟩
    rcases mem_succ_one_cases hi with rfl | rfl
    · rw [h0]
      exact he.isOtciEmbedding hi
    · exact (isOtciEmbedding_iff_of_isSubOne hA1 hZ' hZ hsub).mpr
        ⟨he.isOtciEmbedding h1s, hran⟩

theorem embRestrict_val (U σ : M) {i : M} (hi : i ∈ ((2 : ℕ) : M)) :
    embRestrict U σ ﹫ i = (σ ﹫ i) ↾ ndOf (aoc U ﹫ i) := by
  have hres : IsSetRestrictedTo (fun i ↦ (σ ﹫ i) ↾ ndOf (aoc U ﹫ i)) ((2 : ℕ) : M) :=
    isSetRestrictedTo_of_definable _
  rw [embRestrict, val_toSetRestrictedTo hres hi]

/-- The restriction of an embedding of `q_uc` to the array of an ancestor of `q` is an embedding -/
theorem embRestrict_mem_aotciEmbSet (hP : P ∈ otci ((2 : ℕ) : M)) (hq : q ∈ ndOf P) {k : M}
    (hk : k ∈ succ (depOf P q)) (hB : B ∈ aotci ((1 : ℕ) : M))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) B) :
    embRestrict (uc (ancOf P q k)) h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc (ancOf P q k))) B := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hT := hS.isTreeStructure
  obtain ⟨hak, -⟩ := hT.anc_mem_nd hq hk
  change ancOf P q k ∈ ndOf P at hak
  obtain ⟨-, hsub⟩ := uc_ancOf_rel hP hq hk
  have hUq := uc_mem_stduoci_of_mem_otci_two hP hq
  have hUa := uc_mem_stduoci_of_mem_otci_two hP hak
  have hA := aoc_mem_aotci_of_mem_stduoci_one hUa
  obtain ⟨hAf, hAdom, -⟩ := mem_aotci_iff.mp hA
  obtain ⟨hBf, hBdom, -⟩ := mem_aotci_iff.mp hB
  have he := (mem_aotciEmbSet_iff.mp hh).right
  have h2 : ((2 : ℕ) : M) = succ ((1 : ℕ) : M) := natCast_succ 1
  have hres : IsSetRestrictedTo (fun i ↦ (h ﹫ i) ↾ ndOf (aoc (uc (ancOf P q k)) ﹫ i))
      ((2 : ℕ) : M) := isSetRestrictedTo_of_definable _
  refine mem_aotciEmbSet_of_isAotciEmbedding hAf hAdom hBf hBdom
    ⟨isFunction_toSetRestrictedTo hres, by rw [embRestrict, dom_toSetRestrictedTo hres, h2],
      fun {i} hi ↦ ?_⟩
  rw [embRestrict_val _ _ (by rw [h2]; exact hi)]
  rcases mem_succ_one_cases hi with rfl | rfl
  · have hE := he.isOtciEmbedding hi
    have h0 : aoc (uc (ancOf P q k)) ﹫ ∅ = aoc (uc q) ﹫ ∅ := by
      rw [aoc_uc_val_zero_of_mem_otci_two hP hak, aoc_uc_val_zero_of_mem_otci_two hP hq]
    have hdom : dom (h ﹫ ∅) = ndOf (aoc (uc q) ﹫ ∅) :=
      hE.isEmbedding.isEmbedding_ts.isInjectionFromTo.isFunctionFromTo.dom_eq
    rw [h0, ← hdom, restrict_dom hE.isEmbedding.isEmbedding_ts.isInjectionFromTo.isFunction]
    exact hE
  · have h1s : ((1 : ℕ) : M) ∈ succ ((1 : ℕ) : M) := mem_succ_self _
    have hY := val_mem_otci_of_mem_aotci hA h1s
    have hU1 := val_mem_otci_of_mem_aotci (aoc_mem_aotci_of_mem_stduoci_one hUq) h1s
    have hZ := val_mem_otci_of_mem_aotci hB h1s
    obtain ⟨hinj, hodr⟩ := (isOtciEmbedding_iff_of_mem_otci_one hU1 hZ).mp (he.isOtciEmbedding h1s)
    rw [isOtciEmbedding_iff_of_mem_otci_one hY hZ]
    refine ⟨hinj.restrict hsub.left (fun _ h ↦ h), fun a ha b hb hab ↦ ?_⟩
    rw [val_restrict _ hinj.isFunction ha (by rw [hinj.dom_eq]; exact hsub.left ha),
      val_restrict _ hinj.isFunction hb (by rw [hinj.dom_eq]; exact hsub.left hb)]
    exact hodr a (hsub.left ha) b (hsub.left hb) ((hsub.right a ha b hb).mp hab)

end EmbSub

end IniSegSub

section SuccPieces

variable {P Q V X q h i i' j : M}

/-- The image in `X(1)` of the `i`-th signature node of `q_uc` under `h` -/
noncomputable def sigImg (X q h i : M) : M :=
  tpOrig X ((1 : ℕ) : M) ((h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) i)

theorem sigImg_spec (hP : P ∈ otci ((2 : ℕ) : M)) (hq : q ∈ ndOf P)
    (hX : X ∈ aotci ((1 : ℕ) : M))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt X))
    (hi : i ∈ dom (sig (uc q))) :
    sigImg X q h i ∈ ndOf (X ﹫ ((1 : ℕ) : M)) ∧
      (h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) i = relabelOne trvAZero (sigImg X q h i) := by
  have hUq := uc_mem_stduoci_of_mem_otci_two hP hq
  obtain ⟨w, hw, hwe⟩ := exists_relabelOne_eq hX hh (siglvl_eq_one hUq hi).right
  rw [sigImg, hwe, tpOrig_one_relabelOne hX hw]
  exact ⟨hw, rfl⟩

theorem sigImg_injective (hP : P ∈ otci ((2 : ℕ) : M)) (hq : q ∈ ndOf P)
    (hX : X ∈ aotci ((1 : ℕ) : M))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt X))
    (hi : i ∈ dom (sig (uc q))) (hi' : i' ∈ dom (sig (uc q)))
    (h' : sigImg X q h i = sigImg X q h i') : i = i' := by
  have hUq := uc_mem_stduoci_of_mem_otci_two hP hq
  have he := (mem_aotciEmbSet_iff.mp hh).right.isOtciEmbedding (mem_succ_self _)
  have hinj := he.isEmbedding.isEmbedding_ts.isInjectionFromTo
  have h1 := (sigImg_spec hP hq hX hh hi).right
  have h2 := (sigImg_spec hP hq hX hh hi').right
  rw [h', ← h2] at h1
  have hu := hinj.eq (siglvl_eq_one hUq hi).right (siglvl_eq_one hUq hi').right h1
  rw [← lbl_sigdcn hUq hi, ← lbl_sigdcn hUq hi', hu]

section LastSeg

variable (hV : V ∈ stduoci ((1 : ℕ) : M)) (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
include hV hm

/-- The array of `V | (|V_sig| - 1)` -/
theorem lastSeg_facts :
    iniSegAoc V (⋃₀ dom (sig V)) ∈ aotci ((1 : ℕ) : M) ∧
      aoc V ﹫ ∅ = iniSegAoc V (⋃₀ dom (sig V)) ﹫ ∅ ∧
      IsSubOne (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)) (aoc V ﹫ ((1 : ℕ) : M)) ∧
      ∀ w, w ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)) ↔
        w ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) ∧ w ≠ sigdcn V (⋃₀ dom (sig V)) := by
  refine ⟨(mem_finaotci_iff.mp (iniSegAoc_mem_finaotci hV hm)).left,
    (iniSegAoc_val_zero hV).symm, isSubOne_iniSegAoc hV hm, fun w ↦ ?_⟩
  rw [iniSegAoc_val_one hV, ndOf_rtLosSLOT, losSet_orderedPair]
  exact mem_iniSegNds_last_iff hV hm

/-- The targets `X ⊗ Z` and `X' ⊗ Z` -/
theorem lastSeg_tgt_facts :
    tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ∅ = tensorProdTwoAOneTgt (aoc V) ﹫ ∅ ∧
      IsSubOne (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M))
        (tensorProdTwoAOneTgt (aoc V) ﹫ ((1 : ℕ) : M)) ∧
      ∀ w ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)),
        relabelOne trvAZero w ∈
          ndOf (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) := by
  obtain ⟨hX', h0, hsub, -⟩ := lastSeg_facts hV hm
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  refine ⟨?_, isSubOne_tensorProdTwoAOneTgt_val_one hX hX' hsub, fun w hw ↦ ?_⟩
  · rw [tensorProdTwoAOneTgt_val_zero, tensorProdTwoAOneTgt_val_zero,
      restrict_one_eq_of_val_zero_eq hX hX' h0]
  · rw [tensorProdTwoAOneTgt_val_one,
      mem_ndOf_tensorProdOneAZero_iff (val_mem_otci_of_mem_aotci hX' (mem_succ_self _))]
    exact ⟨w, hw, rfl⟩

end LastSeg

section SuccOne

/-- The prefix candidate `E1 = (q_j, h ↾ q_j)` -/
noncomputable def succOne (P q h j : M) : M :=
  !(dctUZero, !(ancOf P q j, embRestrict (uc (ancOf P q j)) h))

variable (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
  (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hq : q ∈ ndOf (Q ﹫ 2))
  (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)))
  (hj : j ∈ dom (sig (uc q)))
include hQ hV hm hq hh hj

theorem succOne_mem (hj0 : j ≠ ∅)
    (hjv : ∀ i ∈ j, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V))) :
    succOne (Q ﹫ 2) q h j ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V))) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', -, -, hnd'⟩ := lastSeg_facts hV hm
  obtain ⟨ht0, htsub, htnd⟩ := lastSeg_tgt_facts hV hm
  have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
  have hdq : dom (sig (uc q)) = depOf (Q ﹫ 2) q := dom_sig_uc_eq_depOf hQ2 hq
  have hjs : j ∈ succ (depOf (Q ﹫ 2) q) := by rw [← hdq]; exact mem_succ_of_mem hj
  obtain ⟨hqj, hdqj⟩ := hTS.anc_mem_nd hq hjs
  change ancOf (Q ﹫ 2) q j ∈ ndOf (Q ﹫ 2) at hqj
  change depOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q j) = j at hdqj
  obtain ⟨hsigj, -⟩ := uc_ancOf_rel hQ2 hq hjs
  have hUj := uc_mem_stduoci_of_mem_otci_two hQ2 hqj
  rw [succOne, mem_tensorProdTwoAOneNds_iff']
  refine ⟨ancOf (Q ﹫ 2) q j, hqj, fun hr ↦ hj0 ?_, _, ?_, rfl⟩
  · rw [← hdqj]
    exact (TreeStructure.mem_rt_iff.mp hr).right
  refine (mem_aotciEmbSet_iff_of_isSubOne (aoc_mem_aotci_of_mem_stduoci_one hUj)
    (tensorProdTwoAOneTgt_mem hX) (tensorProdTwoAOneTgt_mem hX') ht0 htsub).mpr
    ⟨embRestrict_mem_aotciEmbSet hQ2 hq hjs (tensorProdTwoAOneTgt_mem hX) hh, fun z hz ↦ ?_⟩
  have hhf := ((mem_aotciEmbSet_iff.mp hh).right.isOtciEmbedding
    (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  rw [embRestrict_val _ _ natCast_one_mem_two,
    (hhf.isFunction.restrict _).mem_ran_iff] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  rw [dom_restrict_of_subset hhf.isFunction (by
    rw [hhf.dom_eq]; exact (uc_ancOf_rel hQ2 hq hjs).right.left)] at ha
  have hsjdom : dom (sig (uc (ancOf (Q ﹫ 2) q j))) = j := by
    rw [dom_sig_uc_eq_depOf hQ2 hqj, hdqj]
  have ha' := ha
  rw [ndOf_aoc_val_one_eq hUj, mem_iniSegNds_iff, hsjdom] at ha'
  obtain ⟨i, hi, rfl⟩ := ha'
  have hij : i ∈ dom (sig (uc q)) := (ordinal_of_mem ordinal_omega
    (dom_sig_mem_omega_of_mem_stduoci_one hUq)).transitive _ hj hi
  have hsd : sigdcn (uc (ancOf (Q ﹫ 2) q j)) i = sigdcn (uc q) i := by
    rw [sigdcn, sigdcn, hsigj,
      val_restrict _ (uociCond_of_mem_stduoci_one hUq).right.right.right.left.left hi hij]
  rw [val_restrict _ hhf.isFunction ha
      (by rw [hhf.dom_eq]; exact (uc_ancOf_rel hQ2 hq hjs).right.left ha),
    hsd, (sigImg_spec hQ2 hq hX hh hij).right]
  exact htnd _ ((hnd' _).mpr ⟨(sigImg_spec hQ2 hq hX hh hij).left, hjv i hi⟩)

end SuccOne

section SeqLemmas

variable {f : M}

theorem isFunction_tensorProdTwoAOneSeq (P x : M) : IsFunction (tensorProdTwoAOneSeq P x) :=
  (tensorProdTwoAOneSeq_spec _).left

/-- The sequence of the label `(q_k, h ↾ q_k)` of an ancestor is the restriction of that of
`(q, h)` -/
theorem tensorProdTwoAOneSeq_embRestrict (hP : P ∈ otci ((2 : ℕ) : M)) (hq : q ∈ ndOf P)
    {k : M} (hk : k ∈ succ (depOf P q)) {B : M}
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) B) :
    tensorProdTwoAOneSeq P !(ancOf P q k, embRestrict (uc (ancOf P q k)) h) =
      tensorProdTwoAOneSeq P !(q, h) ↾ k := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  obtain ⟨hqk, hdqk⟩ := hTS.anc_mem_nd hq hk
  change ancOf P q k ∈ ndOf P at hqk
  change depOf P (ancOf P q k) = k at hdqk
  obtain ⟨hsigk, hsubk⟩ := uc_ancOf_rel hP hq hk
  have hUq := uc_mem_stduoci_of_mem_otci_two hP hq
  have hUk := uc_mem_stduoci_of_mem_otci_two hP hqk
  have hdq := hTS.dep_mem_omega hq
  have hkd : k ⊆ depOf P q := fun z hz ↦ by
    rcases mem_or_eq_of_mem_succ hk with h' | h'
    · exact (ordinal_of_mem ordinal_omega hdq).transitive _ h' hz
    · rw [← h']
      exact hz
  have hsf := (uociCond_of_mem_stduoci_one hUq).right.right.right.left.left
  refine (isFunction_tensorProdTwoAOneSeq _ _).ext
    ((isFunction_tensorProdTwoAOneSeq _ _).restrict _) ?_ fun i hi ↦ ?_
  · rw [tensorProdTwoAOneSeq_dom, hdqk, dom_restrict_of_subset
      (isFunction_tensorProdTwoAOneSeq _ _) (by rw [tensorProdTwoAOneSeq_dom]; exact hkd)]
  rw [tensorProdTwoAOneSeq_dom, hdqk] at hi
  have hiq : i ∈ depOf P q := hkd hi
  have hik : i ∈ dom (sig (uc (ancOf P q k))) := by
    rw [dom_sig_uc_eq_depOf hP hqk, hdqk]
    exact hi
  have hiu : i ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hP hq]; exact hiq
  rw [tensorProdTwoAOneSeq_val hP hqk (by rw [hdqk]; exact hi),
    val_restrict _ (isFunction_tensorProdTwoAOneSeq _ _) hi
      (by rw [tensorProdTwoAOneSeq_dom]; exact hiq), tensorProdTwoAOneSeq_val hP hq hiq,
    embRestrict_val _ _ natCast_one_mem_two]
  have hsd : sigdcn (uc (ancOf P q k)) i = sigdcn (uc q) i := by
    rw [sigdcn, sigdcn, hsigk, val_restrict _ hsf hi hiu]
  have hnd : sigdcn (uc q) i ∈ ndOf (aoc (uc (ancOf P q k)) ﹫ ((1 : ℕ) : M)) := by
    rw [← hsd]
    exact (siglvl_eq_one hUk hik).right
  have hhf := ((mem_aotciEmbSet_iff.mp hh).right.isOtciEmbedding
    (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  have hkω : k ∈ (ω : M) := ordinal_omega.transitive _ (succ_mem_omega hdq) hk
  rw [hsd, val_restrict _ hhf.isFunction hnd
      (by rw [hhf.dom_eq]; exact (siglvl_eq_one hUq hiu).right),
    ancOf_ancOf (otciCond_two hP).left hq hk (succ_mem_succ_of_mem hkω hi)]

end SeqLemmas

end SuccPieces

section EmbUpd

variable {P q h j B B' D : M}

/-- An embedding of trees in `otci_1` reflects the order -/
theorem rel_of_rel_val {Y Z π a b : M} (hY : Y ∈ otci ((1 : ℕ) : M)) (hZ : Z ∈ otci ((1 : ℕ) : M))
    (he : IsOtciEmbedding Y Z π) (ha : a ∈ ndOf Y) (hb : b ∈ ndOf Y)
    (h : (π ﹫ a) [odrOne Z] (π ﹫ b)) : a [odrOne Y] b := by
  obtain ⟨hinj, hodr⟩ := (isOtciEmbedding_iff_of_mem_otci_one hY hZ).mp he
  have hRY : IsStrictLinearOrder (odrOne Y) (ndOf Y) := (rtlosOf_of_mem_otci_one hY).left
  have hRZ : IsStrictLinearOrder (odrOne Z) (ndOf Z) := (rtlosOf_of_mem_otci_one hZ).left
  rcases hRY.trichotomous ha hb with h' | rfl | h'
  · exact h'
  · exact (hRZ.irrefl _ h).elim
  · exact (hRZ.asymm h (hodr b hb a ha h')).elim

/-- The embedding of the continuous child `q_j⁺`: `h` on the first `j` nodes of the signature and
`D` at the `j`-th node, for `D` the successor of `h(u_j)` in a subtree, not the image of the `ucf`
of `q_j` -/
theorem embUpd_mem_aotciEmbSet (hP : P ∈ otci ((2 : ℕ) : M)) (hq : q ∈ ndOf P)
    (hj : j ∈ depOf P q) (hB : B ∈ aotci ((1 : ℕ) : M)) (hB' : B' ∈ aotci ((1 : ℕ) : M))
    (h0 : B' ﹫ ∅ = B ﹫ ∅) (hsub : IsSubOne (B' ﹫ ((1 : ℕ) : M)) (B ﹫ ((1 : ℕ) : M)))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) B) (hD : D ∈ ndOf (B' ﹫ ((1 : ℕ) : M)))
    (himg : ∀ i ∈ j, (h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) i ∈ ndOf (B' ﹫ ((1 : ℕ) : M)))
    (hlt : ((h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) j) [odrOne (B ﹫ ((1 : ℕ) : M))] D)
    (hsucc : ∀ z ∈ ndOf (B' ﹫ ((1 : ℕ) : M)),
      ((h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) j) [odrOne (B ﹫ ((1 : ℕ) : M))] z →
        z = D ∨ D [odrOne (B ﹫ ((1 : ℕ) : M))] z)
    (hne : j ≠ ∅ → D ≠ (h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf P q j))) :
    embUpd h (ancOf P q (succ j)) (sigdcn (uc q) j) D ∈ aotciEmbSet ((1 : ℕ) : M)
      (aoc (uc (ctChd P (ancOf P q j) (aoc (uc (ancOf P q (succ j))))))) B' := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  have hdq := hTS.dep_mem_omega hq
  have hjω : j ∈ (ω : M) := ordinal_omega.transitive _ hdq hj
  have hjs : j ∈ succ (depOf P q) := mem_succ_of_mem hj
  have hj1s : succ j ∈ succ (depOf P q) := succ_mem_succ_of_mem hdq hj
  obtain ⟨hqj, hdqj⟩ := hTS.anc_mem_nd hq hjs
  change ancOf P q j ∈ ndOf P at hqj
  change depOf P (ancOf P q j) = j at hdqj
  obtain ⟨hqj1, hdqj1⟩ := hTS.anc_mem_nd hq hj1s
  change ancOf P q (succ j) ∈ ndOf P at hqj1
  change depOf P (ancOf P q (succ j)) = succ j at hdqj1
  have hc : ancOf P q (succ j) ∈ chdOf P (ancOf P q j) := hTS.anc_succ_mem_chd hq hj
  obtain ⟨-, hKk, -, -, -, -⟩ := ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hP hqj hc
  rw [hKk]
  set K := aoc (uc (ancOf P q (succ j))) with hK
  have hUq := uc_mem_stduoci_of_mem_otci_two hP hq
  have hUj := uc_mem_stduoci_of_mem_otci_two hP hqj
  have hUj1 := uc_mem_stduoci_of_mem_otci_two hP hqj1
  have hKA := aoc_mem_aotci_of_mem_stduoci_one hUj1
  obtain ⟨hKf, hKdom, -⟩ := mem_aotci_iff.mp hKA
  obtain ⟨hB'f, hB'dom, -⟩ := mem_aotci_iff.mp hB'
  have he := (mem_aotciEmbSet_iff.mp hh).right
  have h1s : ((1 : ℕ) : M) ∈ succ ((1 : ℕ) : M) := mem_succ_self _
  have h12 : ((1 : ℕ) : M) ⊆ dom h := by
    rw [he.dom_eq]
    exact fun _ hz ↦ mem_succ_of_mem hz
  have hhr : IsFunction (h ↾ ((1 : ℕ) : M)) := he.isFunction.restrict _
  have hhrdom : dom (h ↾ ((1 : ℕ) : M)) = ((1 : ℕ) : M) := dom_restrict_of_subset he.isFunction h12
  have hv0 : embUpd h (ancOf P q (succ j)) (sigdcn (uc q) j) D ﹫ ∅ = h ﹫ ∅ := by
    rw [embUpd, cc_val_of_mem hhr _ (by rw [hhrdom]; exact empty_mem_natCast_one),
      val_restrict _ he.isFunction empty_mem_natCast_one (h12 empty_mem_natCast_one)]
  have hv1 : embUpd h (ancOf P q (succ j)) (sigdcn (uc q) j) D ﹫ ((1 : ℕ) : M) =
      update (lvlOneRes h (ancOf P q (succ j))) (sigdcn (uc q) j) D := by
    have h' := cc_val_self hhr (update (lvlOneRes h (ancOf P q (succ j))) (sigdcn (uc q) j) D)
    rwa [hhrdom] at h'
  refine mem_aotciEmbSet_of_isAotciEmbedding hKf hKdom hB'f hB'dom
    ⟨hhr.cc _, by rw [embUpd, dom_cc, hhrdom], fun {i} hi ↦ ?_⟩
  rcases mem_succ_one_cases hi with rfl | rfl
  · rw [hv0, h0, hK, aoc_uc_val_zero_of_mem_otci_two hP hqj1,
      ← aoc_uc_val_zero_of_mem_otci_two hP hq]
    exact he.isOtciEmbedding hi
  rw [hv1]
  -- the level-`1` trees
  have hK1 := val_mem_otci_of_mem_aotci hKA h1s
  have hU1 := val_mem_otci_of_mem_aotci (aoc_mem_aotci_of_mem_stduoci_one hUq) h1s
  have hZ := val_mem_otci_of_mem_aotci hB h1s
  have hZ' := val_mem_otci_of_mem_aotci hB' h1s
  have he1 := he.isOtciEmbedding h1s
  obtain ⟨hinj, hodr⟩ := (isOtciEmbedding_iff_of_mem_otci_one hU1 hZ).mp he1
  obtain ⟨hsig1, hsub1⟩ := uc_ancOf_rel hP hq hj1s
  obtain ⟨hsigj, -⟩ := uc_ancOf_rel hP hq hjs
  have hsf := (uociCond_of_mem_stduoci_one hUq).right.right.right.left.left
  have hdomq : dom (sig (uc q)) = depOf P q := dom_sig_uc_eq_depOf hP hq
  have hsd1 {i : M} (hi : i ∈ succ j) : sigdcn (uc (ancOf P q (succ j))) i = sigdcn (uc q) i := by
    have hiq : i ∈ dom (sig (uc q)) := by
      rw [hdomq]
      rcases mem_or_eq_of_mem_succ hi with h' | h'
      · exact (ordinal_of_mem ordinal_omega hdq).transitive _ hj h'
      · rw [h']; exact hj
    rw [sigdcn, sigdcn, hsig1, val_restrict _ hsf hi hiq]
  have hdom1 : dom (sig (uc (ancOf P q (succ j)))) = succ j := by
    rw [dom_sig_uc_eq_depOf hP hqj1, hdqj1]
  have hdomj : dom (sig (uc (ancOf P q j))) = j := by
    rw [dom_sig_uc_eq_depOf hP hqj, hdqj]
  have hnodes (a : M) : a ∈ ndOf (K ﹫ ((1 : ℕ) : M)) ↔ ∃ i ∈ succ j, sigdcn (uc q) i = a := by
    rw [ndOf_aoc_val_one_eq hUj1, mem_iniSegNds_iff, hdom1]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, (hsd1 hi).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, hsd1 hi⟩
  have huj : sigdcn (uc q) j ∈ ndOf (K ﹫ ((1 : ℕ) : M)) :=
    (hnodes _).mpr ⟨j, mem_succ_self j, rfl⟩
  -- the values of the new embedding
  have hfK : IsFunction (lvlOneRes h (ancOf P q (succ j))) := hinj.isFunction.restrict _
  have hdomK : dom (lvlOneRes h (ancOf P q (succ j))) = ndOf (K ﹫ ((1 : ℕ) : M)) :=
    dom_restrict_of_subset hinj.isFunction (by rw [hinj.dom_eq]; exact hsub1.left)
  have hval {a : M} (ha : a ∈ ndOf (K ﹫ ((1 : ℕ) : M))) (hne' : a ≠ sigdcn (uc q) j) :
      update (lvlOneRes h (ancOf P q (succ j))) (sigdcn (uc q) j) D ﹫ a =
        (h ﹫ ((1 : ℕ) : M)) ﹫ a := by
    rw [val_update_of_ne hfK _ (by rw [hdomK]; exact ha) hne', lvlOneRes,
      val_restrict _ hinj.isFunction ha (by rw [hinj.dom_eq]; exact hsub1.left ha)]
  have hvalj :
      update (lvlOneRes h (ancOf P q (succ j))) (sigdcn (uc q) j) D ﹫ sigdcn (uc q) j = D :=
    val_update_self hfK _ _
  have hold {a : M} (ha : a ∈ ndOf (K ﹫ ((1 : ℕ) : M))) (hne' : a ≠ sigdcn (uc q) j) :
      ∃ i ∈ j, sigdcn (uc q) i = a := by
    obtain ⟨i, hi, rfl⟩ := (hnodes a).mp ha
    rcases mem_or_eq_of_mem_succ hi with h' | h'
    · exact ⟨i, h', rfl⟩
    · exact (hne' (by rw [h'])).elim
  have himg' {a : M} (ha : a ∈ ndOf (K ﹫ ((1 : ℕ) : M))) (hne' : a ≠ sigdcn (uc q) j) :
      (h ﹫ ((1 : ℕ) : M)) ﹫ a ∈ ndOf (B' ﹫ ((1 : ℕ) : M)) := by
    obtain ⟨i, hi, rfl⟩ := hold ha hne'
    exact himg i hi
  have hRB : IsStrictLinearOrder (odrOne (B ﹫ ((1 : ℕ) : M))) (ndOf (B ﹫ ((1 : ℕ) : M))) :=
    (rtlosOf_of_mem_otci_one hZ).left
  -- the nodes after `u_j`
  have hafter {b : M} (hb : b ∈ ndOf (K ﹫ ((1 : ℕ) : M))) (hne' : b ≠ sigdcn (uc q) j)
      (hjb : (sigdcn (uc q) j) [odrOne (K ﹫ ((1 : ℕ) : M))] b) :
      D [odrOne (B ﹫ ((1 : ℕ) : M))] ((h ﹫ ((1 : ℕ) : M)) ﹫ b) := by
    have hj0 : j ≠ ∅ := by
      rintro rfl
      obtain ⟨i, hi, -⟩ := hold hb hne'
      simp at hi
    have hsj : sig (uc (ancOf P q j)) ≠ ∅ := fun h' ↦ hj0 (by rw [← hdomj, h', dom_empty])
    obtain ⟨-, -, hsubjj1, hrel⟩ := uc_rel_of_mem_chdOf hP hqj hc
    obtain ⟨-, hrq, hnr, hafter'⟩ := hrel hsj
    have hRK : IsStrictLinearOrder (odrOne (K ﹫ ((1 : ℕ) : M))) (ndOf (K ﹫ ((1 : ℕ) : M))) :=
      (rtlosOf_of_mem_otci_one hK1).left
    rw [hdomj, hsd1 (mem_succ_self j)] at hnr hafter'
    obtain ⟨i, hi, rfl⟩ := hold hb hne'
    have hbj : sigdcn (uc q) i ∈ ndOf (aoc (uc (ancOf P q j)) ﹫ ((1 : ℕ) : M)) := by
      rw [ndOf_aoc_val_one_eq hUj, mem_iniSegNds_iff, hdomj]
      refine ⟨i, hi, ?_⟩
      rw [sigdcn, sigdcn, hsigj, val_restrict _ hsf hi (by
        rw [hdomq]; exact (ordinal_of_mem ordinal_omega hdq).transitive _ hj hi)]
    have hhub : ((h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) j) [odrOne (B ﹫ ((1 : ℕ) : M))]
        ((h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) i) :=
      hodr _ (hsub1.left huj) _ (hsub1.left hb) ((hsub1.right _ huj _ hb).mp hjb)
    rcases hsucc _ (himg i hi) hhub with h' | h'
    · exfalso
      rcases hafter' _ hbj hjb with h'' | h''
      · exact hne hj0 (by rw [← h'', h'])
      · -- `r_q` lies strictly between `u_j` and `u_i`, so its image too
        have hrqK := hsubjj1.left hrq
        have h1 : ((h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf P q j))) [odrOne (B ﹫ ((1 : ℕ) : M))]
            ((h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) i) :=
          hodr _ (hsub1.left hrqK) _ (hsub1.left hb) ((hsub1.right _ hrqK _ hb).mp h'')
        have h2 : ((h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) j) [odrOne (B ﹫ ((1 : ℕ) : M))]
            ((h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf P q j))) :=
          hodr _ (hsub1.left huj) _ (hsub1.left hrqK) ((hsub1.right _ huj _ hrqK).mp hnr)
        have hrqB' : (h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf P q j)) ∈ ndOf (B' ﹫ ((1 : ℕ) : M)) :=
          himg' hrqK (fun h3 ↦ by rw [h3] at hnr; exact hRK.irrefl _ hnr)
        rcases hsucc _ hrqB' h2 with h3 | h3
        · exact hne hj0 h3.symm
        · rw [h'] at h1
          exact hRB.asymm h1 h3
    · exact h'
  have hRK : IsStrictLinearOrder (odrOne (K ﹫ ((1 : ℕ) : M))) (ndOf (K ﹫ ((1 : ℕ) : M))) :=
    (rtlosOf_of_mem_otci_one hK1).left
  have hmaps {a : M} (ha : a ∈ ndOf (K ﹫ ((1 : ℕ) : M))) :
      update (lvlOneRes h (ancOf P q (succ j))) (sigdcn (uc q) j) D ﹫ a ∈
        ndOf (B' ﹫ ((1 : ℕ) : M)) := by
    by_cases hne' : a = sigdcn (uc q) j
    · rw [hne', hvalj]
      exact hD
    · rw [hval ha hne']
      exact himg' ha hne'
  have hbefore {b : M} (hb : b ∈ ndOf (K ﹫ ((1 : ℕ) : M))) (hne' : b ≠ sigdcn (uc q) j)
      (hbj : b [odrOne (K ﹫ ((1 : ℕ) : M))] (sigdcn (uc q) j)) :
      ((h ﹫ ((1 : ℕ) : M)) ﹫ b) [odrOne (B ﹫ ((1 : ℕ) : M))] D :=
    hRB.trans (hodr _ (hsub1.left hb) _ (hsub1.left huj) ((hsub1.right _ hb _ huj).mp hbj)) hlt
  have hneD {b : M} (hb : b ∈ ndOf (K ﹫ ((1 : ℕ) : M))) (hne' : b ≠ sigdcn (uc q) j) :
      D ≠ (h ﹫ ((1 : ℕ) : M)) ﹫ b := by
    intro hDb
    rcases hRK.trichotomous huj hb with h' | h' | h'
    · have := hafter hb hne' h'
      rw [← hDb] at this
      exact hRB.irrefl _ this
    · exact hne' h'.symm
    · have := hbefore hb hne' h'
      rw [← hDb] at this
      exact hRB.irrefl _ this
  rw [isOtciEmbedding_iff_of_mem_otci_one hK1 hZ']
  refine ⟨isInjectionFromTo_of_val (hfK.update _ _) ?_ (fun a ha ↦ hmaps ha) fun a ha b hb hab ↦ ?_,
    fun a ha b hb hab ↦ ?_⟩
  · rw [dom_update, hdomK]
    ext z
    rw [mem_insert_iff]
    constructor
    · rintro (h' | h')
      · rw [h']
        exact huj
      · exact h'
    · exact fun h' ↦ .inr h'
  · by_cases ha' : a = sigdcn (uc q) j <;> by_cases hb' : b = sigdcn (uc q) j
    · rw [ha', hb']
    · rw [ha', hvalj, hval hb hb'] at hab
      exact (hneD hb hb' hab).elim
    · rw [hb', hvalj, hval ha ha'] at hab
      exact (hneD ha ha' hab.symm).elim
    · rw [hval ha ha', hval hb hb'] at hab
      exact hinj.eq (hsub1.left ha) (hsub1.left hb) hab
  · refine (hsub.right _ (hmaps ha) _ (hmaps hb)).mpr ?_
    by_cases ha' : a = sigdcn (uc q) j <;> by_cases hb' : b = sigdcn (uc q) j
    · rw [ha', hb'] at hab
      exact (hRK.irrefl _ hab).elim
    · rw [ha', hvalj, hval hb hb']
      rw [ha'] at hab
      exact hafter hb hb' hab
    · rw [hb', hvalj, hval ha ha']
      rw [hb'] at hab
      exact hbefore ha ha' hab
    · rw [hval ha ha', hval hb hb']
      exact hodr _ (hsub1.left ha) _ (hsub1.left hb) ((hsub1.right _ ha _ hb).mp hab)

end EmbUpd

section EmbUpdSeq

variable {P q h j B D : M}

theorem embUpd_val_one (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) B) (A u : M) :
    embUpd h A u D ﹫ ((1 : ℕ) : M) = update (lvlOneRes h A) u D := by
  have he := (mem_aotciEmbSet_iff.mp hh).right
  have h12 : ((1 : ℕ) : M) ⊆ dom h := by
    rw [he.dom_eq]
    exact fun _ hz ↦ mem_succ_of_mem hz
  have hhr : IsFunction (h ↾ ((1 : ℕ) : M)) := he.isFunction.restrict _
  have hhrdom : dom (h ↾ ((1 : ℕ) : M)) = ((1 : ℕ) : M) := dom_restrict_of_subset he.isFunction h12
  have h' := cc_val_self hhr (update (lvlOneRes h A) u D)
  rwa [hhrdom] at h'

/-- The sequence of the label `(q_j⁺, σ')` -/
theorem tensorProdTwoAOneSeq_embUpd (hP : P ∈ otci ((2 : ℕ) : M)) (hq : q ∈ ndOf P)
    (hj : j ∈ depOf P q) (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) B) :
    dom (tensorProdTwoAOneSeq P !(ctChd P (ancOf P q j) (aoc (uc (ancOf P q (succ j)))),
        embUpd h (ancOf P q (succ j)) (sigdcn (uc q) j) D)) = succ j ∧
      tensorProdTwoAOneSeq P !(ctChd P (ancOf P q j) (aoc (uc (ancOf P q (succ j)))),
        embUpd h (ancOf P q (succ j)) (sigdcn (uc q) j) D) ↾ j =
          tensorProdTwoAOneSeq P !(q, h) ↾ j ∧
      tensorProdTwoAOneSeq P !(ctChd P (ancOf P q j) (aoc (uc (ancOf P q (succ j)))),
        embUpd h (ancOf P q (succ j)) (sigdcn (uc q) j) D) ﹫ j =
          !(D, ctChd P (ancOf P q j) (aoc (uc (ancOf P q (succ j))))) := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  have hdq := hTS.dep_mem_omega hq
  have hjω : j ∈ (ω : M) := ordinal_omega.transitive _ hdq hj
  have hjs : j ∈ succ (depOf P q) := mem_succ_of_mem hj
  have hj1s : succ j ∈ succ (depOf P q) := succ_mem_succ_of_mem hdq hj
  obtain ⟨hqj, hdqj⟩ := hTS.anc_mem_nd hq hjs
  change ancOf P q j ∈ ndOf P at hqj
  change depOf P (ancOf P q j) = j at hdqj
  obtain ⟨hqj1, -⟩ := hTS.anc_mem_nd hq hj1s
  change ancOf P q (succ j) ∈ ndOf P at hqj1
  have hc : ancOf P q (succ j) ∈ chdOf P (ancOf P q j) := hTS.anc_succ_mem_chd hq hj
  obtain ⟨hpc, hpk, hps, -, -, -⟩ :=
    ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hP hqj hc
  set qp := ctChd P (ancOf P q j) (aoc (uc (ancOf P q (succ j)))) with hqp
  have hqpn : qp ∈ ndOf P := mem_ndOf_of_mem_chdOf (otciCond_two hP).left hpc
  have hdqp : depOf P qp = succ j := by
    have h' : depOf P qp = succ (depOf P (ancOf P q j)) := hTS.dep_of_mem_chd _ hqj _ hpc
    rw [h', hdqj]
  have hqprt : qp ∈ (SLOTreeStructure.ofM P).ts.nd \ (SLOTreeStructure.ofM P).ts.rt := by
    rw [mem_sdiff_iff, TreeStructure.mem_rt_iff]
    exact ⟨hqpn, fun h' ↦ succ_ne_empty _ (hdqp.symm.trans h'.right)⟩
  have hprt : prtOf P qp = ancOf P q j := prtOf_eq_of_mem_chdOf (otciCond_two hP).left hpc
  have hUq := uc_mem_stduoci_of_mem_otci_two hP hq
  have hUj1 := uc_mem_stduoci_of_mem_otci_two hP hqj1
  obtain ⟨hsig1, hsub1⟩ := uc_ancOf_rel hP hq hj1s
  have hsf := (uociCond_of_mem_stduoci_one hUq).right.right.right.left.left
  have hdomq : dom (sig (uc q)) = depOf P q := dom_sig_uc_eq_depOf hP hq
  have hiq {i : M} (hi : i ∈ succ j) : i ∈ depOf P q := by
    rcases mem_or_eq_of_mem_succ hi with h' | h'
    · exact (ordinal_of_mem ordinal_omega hdq).transitive _ hj h'
    · rw [h']; exact hj
  have hsd {i : M} (hi : i ∈ succ j) : sigdcn (uc qp) i = sigdcn (uc q) i := by
    rw [sigdcn, sigdcn, hps, hsig1, val_restrict _ hsf hi (by rw [hdomq]; exact hiq hi)]
  have he := (mem_aotciEmbSet_iff.mp hh).right
  have hinj := (he.isOtciEmbedding (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  have hfK : IsFunction (lvlOneRes h (ancOf P q (succ j))) := hinj.isFunction.restrict _
  have hdomK : dom (lvlOneRes h (ancOf P q (succ j))) =
      ndOf (aoc (uc (ancOf P q (succ j))) ﹫ ((1 : ℕ) : M)) :=
    dom_restrict_of_subset hinj.isFunction (by rw [hinj.dom_eq]; exact hsub1.left)
  have hval {i : M} (hi : i ∈ succ j) :
      tensorProdTwoAOneSeq P !(qp, embUpd h (ancOf P q (succ j)) (sigdcn (uc q) j) D) ﹫ i =
        !(update (lvlOneRes h (ancOf P q (succ j))) (sigdcn (uc q) j) D ﹫ sigdcn (uc q) i,
          ancOf P qp (succ i)) := by
    rw [tensorProdTwoAOneSeq_val hP hqpn (by rw [hdqp]; exact hi), embUpd_val_one hh, hsd hi]
  refine ⟨by rw [tensorProdTwoAOneSeq_dom, hdqp], ?_, ?_⟩
  · have hjsub : j ⊆ succ j := fun _ hz ↦ mem_succ_of_mem hz
    have hjq : j ⊆ depOf P q := fun z hz ↦ (ordinal_of_mem ordinal_omega hdq).transitive _ hj hz
    refine ((isFunction_tensorProdTwoAOneSeq _ _).restrict _).ext
      ((isFunction_tensorProdTwoAOneSeq _ _).restrict _) ?_ fun i hi ↦ ?_
    · rw [dom_restrict_of_subset (isFunction_tensorProdTwoAOneSeq _ _)
        (by rw [tensorProdTwoAOneSeq_dom, hdqp]; exact hjsub),
        dom_restrict_of_subset (isFunction_tensorProdTwoAOneSeq _ _)
        (by rw [tensorProdTwoAOneSeq_dom]; exact hjq)]
    rw [dom_restrict_of_subset (isFunction_tensorProdTwoAOneSeq _ _)
      (by rw [tensorProdTwoAOneSeq_dom, hdqp]; exact hjsub)] at hi
    have his : i ∈ succ j := mem_succ_of_mem hi
    rw [val_restrict _ (isFunction_tensorProdTwoAOneSeq _ _) hi
      (by rw [tensorProdTwoAOneSeq_dom, hdqp]; exact his),
      val_restrict _ (isFunction_tensorProdTwoAOneSeq _ _) hi
      (by rw [tensorProdTwoAOneSeq_dom]; exact hjq hi), hval his,
      tensorProdTwoAOneSeq_val hP hq (hjq hi)]
    have hne : sigdcn (uc q) i ≠ sigdcn (uc q) j := by
      intro h'
      have := congrArg lbl h'
      rw [lbl_sigdcn hUq (by rw [hdomq]; exact hjq hi), lbl_sigdcn hUq (by rw [hdomq]; exact hj)]
        at this
      rw [this] at hi
      exact notMem_self _ hi
    have hnd : sigdcn (uc q) i ∈ ndOf (aoc (uc (ancOf P q (succ j))) ﹫ ((1 : ℕ) : M)) := by
      rw [← hsd his, ← hpk]
      exact (siglvl_eq_one (uc_mem_stduoci_of_mem_otci_two hP hqpn)
        (by rw [dom_sig_uc_eq_depOf hP hqpn, hdqp]; exact his)).right
    have hA : ancOf P qp (succ i) = ancOf P (prtOf P qp) (succ i) :=
      hTS.anc_prt_val hqprt (by
        change succ i ∈ succ (depOf P (prtOf P qp))
        rw [hprt, hdqj]
        exact succ_mem_succ_of_mem hjω hi)
    rw [val_update_of_ne hfK _ (by rw [hdomK]; exact hnd) hne, lvlOneRes,
      val_restrict _ hinj.isFunction hnd (by rw [hinj.dom_eq]; exact hsub1.left hnd),
      hA, hprt, ancOf_ancOf (otciCond_two hP).left hq hjs (succ_mem_succ_of_mem hjω hi)]
  · rw [hval (mem_succ_self j), val_update_self hfK]
    have h' := hTS.anc_dep hqpn
    change ancOf P qp (depOf P qp) = qp at h'
    rw [hdqp] at h'
    rw [h']

end EmbUpdSeq

section SuccMin

variable {Q V X q h j z : M}

theorem mem_ndOf_tensorProdATwoAOne_val_one_iff (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hX : X ∈ aotci ((1 : ℕ) : M)) :
    z ∈ ndOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M)) ↔
      z ∈ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ∨
        z ∈ tensorProdTwoAOneNds (Q ﹫ 2) X := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hB1 := val_mem_otci_of_mem_aotci (tensorProdATwoAOneBase_mem_aotci hQ X) (mem_succ_self _)
  have hC := tensorProdTwoAOne_mem_otci hQ2 hX
  obtain ⟨-, hsB, -⟩ := rtlosOf_of_mem_otci_one hB1
  obtain ⟨-, hsC, -⟩ := rtlosOf_of_mem_otci_one hC
  rw [tensorProdATwoAOne_val_one_eq hQ, ndOf_rtLosSLOT, losConcat, losSet_orderedPair, hsB, hsC,
    mem_union_iff, ndOf_tensorProdTwoAOne]

/-- A node of `(Q ⊗ X')(1)` above a node from `Q(2)` -/
theorem exists_of_rel_of_mem_lastSeg (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hV : V ∈ stduoci ((1 : ℕ) : M)) (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) {y : M}
    (hy : y ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hz : z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
    (hyz : y [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) :
    ∃ qz hz', z = !(dctUZero, !(qz, hz')) ∧ qz ∈ ndOf (Q ﹫ 2) ∧ qz ∉ rtOf (Q ﹫ 2) ∧
      hz' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qz))
        (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V)))) ∧
      hz' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qz)) (tensorProdTwoAOneTgt (aoc V)) ∧
      TensorProdTwoAOneLt (Q ﹫ 2) (aoc V) (lbl y) !(qz, hz') := by
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, -⟩ := lastSeg_facts hV hm
  rw [rel_odrOne_tensorProdATwoAOne_iff_of_mem hQ hX hy] at hyz
  obtain ⟨hzN, hlt⟩ := hyz
  have hbase : tensorProdATwoAOneBase Q (iniSegAoc V (⋃₀ dom (sig V))) =
      tensorProdATwoAOneBase Q (aoc V) := by
    rw [tensorProdATwoAOneBase, tensorProdATwoAOneBase, restrict_one_eq_of_val_zero_eq hX hX' h0]
  rw [mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX', hbase] at hz
  have hzN' : z ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V))) := by
    rcases hz with hz | hz
    · exfalso
      have h' : z ∈ ndOf (tensorProdATwoAOneBase Q (aoc V) ﹫ ((1 : ℕ) : M)) ∩
          ndOf (tensorProdTwoAOne (Q ﹫ 2) (aoc V)) := by
        rw [mem_inter_iff, ndOf_tensorProdTwoAOne]
        exact ⟨hz, hzN⟩
      rw [ndOf_base_inter_ndOf_tensorProdTwoAOne hQ] at h'
      simp at h'
    · exact hz
  obtain ⟨qz, hqz, hqzr, hz', hhz', rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp hzN'
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  obtain ⟨ht0, htsub, -⟩ := lastSeg_tgt_facts hV hm
  have hhzX := ((mem_aotciEmbSet_iff_of_isSubOne
    (aoc_mem_aotci_of_mem_stduoci_one (uc_mem_stduoci_of_mem_otci_two hQ2 hqz))
    (tensorProdTwoAOneTgt_mem hX) (tensorProdTwoAOneTgt_mem hX') ht0 htsub).mp hhz').left
  rw [lbl_orderedPair] at hlt
  exact ⟨qz, hz', rfl, hqz, hqzr, hhz', hhzX, hlt⟩

theorem subset_of_not_mem_of_ordinal {a b : M} (ha : Ordinal a) (hb : Ordinal b) (h : b ∉ a) :
    a ⊆ b := by
  rcases olt_trichotomy ha hb with h' | rfl | h'
  · exact fun z hz ↦ hb.transitive _ h'.right.right hz
  · exact fun _ hz ↦ hz
  · exact (h h'.right.right).elim

theorem val_eq_of_subset_of_mem {f g i : M} (hf : IsFunction f) (hg : IsFunction g) (hfg : f ⊆ g)
    (hi : i ∈ dom f) : g ﹫ i = f ﹫ i := by
  have h1 : !(i, f ﹫ i) ∈ f := (hf.mem_dom_iff i).mp hi
  exact hg.val_eq_of_rel (hfg h1)

/-- The node `E2` is the successor of `y` in `(Q ⊗ X')(1)` -/
theorem succTwo_min (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hq : q ∈ ndOf (Q ﹫ 2))
    (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)))
    (hj : j ∈ depOf (Q ﹫ 2) q) (hje : sigImg (aoc V) q h j = sigdcn V (⋃₀ dom (sig V)))
    {w : M} (hw : w ∈ iniSegRight V (⋃₀ dom (sig V)))
    (hwl : ∀ r ∈ iniSegRight V (⋃₀ dom (sig V)), r = w ∨ w [iniSegOdr V] r)
    (hE : !(dctUZero, !(ctChd (Q ﹫ 2) (ancOf (Q ﹫ 2) q j)
      (aoc (uc (ancOf (Q ﹫ 2) q (succ j)))), embUpd h (ancOf (Q ﹫ 2) q (succ j))
        (sigdcn (uc q) j) (relabelOne trvAZero w))) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hz : z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
    (hyz : !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) :
    z = !(dctUZero, !(ctChd (Q ﹫ 2) (ancOf (Q ﹫ 2) q j)
      (aoc (uc (ancOf (Q ﹫ 2) q (succ j)))), embUpd h (ancOf (Q ﹫ 2) q (succ j))
        (sigdcn (uc q) j) (relabelOne trvAZero w))) ∨
      !(dctUZero, !(ctChd (Q ﹫ 2) (ancOf (Q ﹫ 2) q j)
        (aoc (uc (ancOf (Q ﹫ 2) q (succ j)))), embUpd h (ancOf (Q ﹫ 2) q (succ j))
          (sigdcn (uc q) j) (relabelOne trvAZero w)))
        [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, hnd'⟩ := lastSeg_facts hV hm
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  have hX'1 := val_mem_otci_of_mem_aotci hX' (mem_succ_self _)
  have hT := tensorProdTwoAOneTgt_mem hX
  have he1 : sigdcn V (⋃₀ dom (sig V)) ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) :=
    (siglvl_eq_one hV hm).right
  set e := sigdcn V (⋃₀ dom (sig V)) with he
  obtain ⟨qz, hz', rfl, hqz, hqzr, hhz'X', hhzX, hlt⟩ :=
    exists_of_rel_of_mem_lastSeg hQ hV hm hy hz hyz
  set qp := ctChd (Q ﹫ 2) (ancOf (Q ﹫ 2) q j) (aoc (uc (ancOf (Q ﹫ 2) q (succ j)))) with hqp
  set f2 := embUpd h (ancOf (Q ﹫ 2) q (succ j)) (sigdcn (uc q) j) (relabelOne trvAZero w)
    with hf2
  obtain ⟨qp', hqp', -, f2', hf2', he2⟩ := mem_tensorProdTwoAOneNds_iff'.mp hE
  rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at he2
  obtain ⟨-, hqpeq, hf2eq⟩ := he2
  subst hqpeq hf2eq
  rw [rel_odrOne_tensorProdATwoAOne_iff_of_mem hQ hX hE, lbl_orderedPair, lbl_orderedPair]
  rw [lbl_orderedPair] at hlt
  -- the sequences
  set Sy := tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h) with hSy
  set Sz := tensorProdTwoAOneSeq (Q ﹫ 2) !(qz, hz') with hSz
  set S2 := tensorProdTwoAOneSeq (Q ﹫ 2) !(qp, f2) with hS2
  have hfy := isFunction_tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h)
  have hfz := isFunction_tensorProdTwoAOneSeq (Q ﹫ 2) !(qz, hz')
  have hf2s := isFunction_tensorProdTwoAOneSeq (Q ﹫ 2) !(qp, f2)
  obtain ⟨hdS2, hrS2, hvS2⟩ := tensorProdTwoAOneSeq_embUpd (D := relabelOne trvAZero w) hQ2 hq hj hh
  change S2 ↾ j = Sy ↾ j at hrS2
  have hdy : dom Sy = depOf (Q ﹫ 2) q := tensorProdTwoAOneSeq_dom _ _
  have hdz : dom Sz = depOf (Q ﹫ 2) qz := tensorProdTwoAOneSeq_dom _ _
  have hdqz := hTS.dep_mem_omega hqz
  have hdq := hTS.dep_mem_omega hq
  have hjω : j ∈ (ω : M) := ordinal_omega.transitive _ hdq hj
  have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
  have hjsig : j ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hj
  have hvy : Sy ﹫ j = !(relabelOne trvAZero e, ancOf (Q ﹫ 2) q (succ j)) := by
    rw [hSy, tensorProdTwoAOneSeq_val hQ2 hq hj, (sigImg_spec hQ2 hq hX hh hjsig).right, hje]
  have heN : relabelOne trvAZero e ∉ ndOf (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V))) ﹫
      ((1 : ℕ) : M)) := by
    rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hX'1]
    rintro ⟨w', hw', hwe⟩
    have := relabelOne_injective hX1 (hsub.left hw') he1 hwe
    exact ((hnd' w').mp hw').right this
  have hzmem {i : M} (hi : i ∈ dom Sz) : Sz ﹫ i ∈ ndOf (tensorProdTwoAOneTgt
      (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) ×ˢ ndOf (Q ﹫ 2) := by
    rw [hdz] at hi
    exact tensorProdTwoAOneSeq_val_mem hQ2 hqz hhz'X' hi
  have hnotj (hjz : j ∈ dom Sz) : Sz ﹫ j ≠ Sy ﹫ j := by
    intro h'
    have := hzmem hjz
    rw [h', hvy, pair_mem_sprod_iff] at this
    exact heN this.left
  have hzN : !(dctUZero, !(qz, hz')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) :=
    mem_tensorProdTwoAOneNds_iff'.mpr ⟨qz, hqz, hqzr, hz', hhzX, rfl⟩
  have hright (h' : BKLt (tensorProdTwoAOneCoordOdr (Q ﹫ 2) (aoc V)) S2 Sz) :
      !(dctUZero, !(qz, hz')) = !(dctUZero, !(qp, f2)) ∨
        !(dctUZero, !(qz, hz')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) ∧
          TensorProdTwoAOneLt (Q ﹫ 2) (aoc V) !(qp, f2) !(qz, hz') := .inr ⟨hzN, h'⟩
  have hoj : Ordinal j := ordinal_of_mem ordinal_omega hjω
  have hodz : Ordinal (dom Sz) := by rw [hdz]; exact ordinal_of_mem ordinal_omega hdqz
  have hjsub : j ⊆ dom Sy := fun z hz ↦ by
    rw [hdy]; exact (ordinal_of_mem ordinal_omega hdq).transitive _ hj hz
  have hagree (i : M) (hi : i ∈ j) : S2 ﹫ i = Sy ﹫ i :=
    val_eq_of_restrict_eq hf2s hfy hrS2 hi (by rw [hdS2]; exact mem_succ_of_mem hi) (hjsub hi)
  have hX1nd {w' : M} (hw' : w' ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M))) :
      relabelOne trvAZero w' ∈ ndOf (tensorProdTwoAOneTgt (aoc V) ﹫ ((1 : ℕ) : M)) := by
    rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hX1]
    exact ⟨w', hw', rfl⟩
  have hwX1 : w ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) :=
    hsub.left ((hnd' w).mpr ((mem_iniSegNds_last_iff hV hm).mp (mem_iniSegRight_iff.mp hw).left))
  unfold TensorProdTwoAOneLt at hlt ⊢
  rcases hlt with ⟨hzy, hne⟩ | ⟨k, hky, hkz, hres, hrel⟩
  · -- the sequence of `z` is a proper initial segment of that of `y`
    have hjz : j ∉ dom Sz := fun hjz ↦ hnotj hjz (val_eq_of_subset_of_mem hfz hfy hzy hjz).symm
    have hzj : dom Sz ⊆ j := subset_of_not_mem_of_ordinal hodz hoj hjz
    refine hright (.inl ⟨fun p hp ↦ ?_, fun h' ↦ hjz ?_⟩)
    · obtain ⟨i, rfl⟩ := hfz.exists_val hp
      have hi : i ∈ dom Sz := by
        rw [hfz.mem_dom_iff]
        exact hp
      have hiy : Sy ﹫ i = Sz ﹫ i := val_eq_of_subset_of_mem hfz hfy hzy hi
      rw [← hiy, ← hagree i (hzj hi)]
      exact (hf2s.mem_dom_iff i).mp (by rw [hdS2]; exact mem_succ_of_mem (hzj hi))
    · rw [h', hdS2]
      exact mem_succ_self j
  have hok : Ordinal k := hodz.transitive _ hkz |> fun _ ↦ ordinal_of_mem hodz hkz
  rcases olt_trichotomy hok hoj with hkj | hkeq | hjk
  · -- the first difference is before `j`
    have hkj' : k ∈ j := hkj.right.right
    have hkjs : k ⊆ j := hoj.transitive _ hkj'
    refine hright (.inr ⟨k, by rw [hdS2]; exact mem_succ_of_mem hkj', hkz, ?_, ?_⟩)
    · rw [← hres]
      exact hf2s.restrict_eq_restrict hfy (fun z hz ↦ by rw [hdS2]; exact mem_succ_of_mem (hkjs hz))
        (fun z hz ↦ hjsub (hkjs hz)) fun i hi ↦ hagree i (hkjs hi)
    · rw [hagree k hkj']
      exact hrel
  swap
  · -- the first difference is after `j`: impossible
    exfalso
    have hjz : j ∈ dom Sz := hodz.transitive _ hkz hjk.right.right
    exact hnotj hjz (val_eq_of_restrict_eq hfz hfy hres.symm hjk.right.right hjz
      (by rw [hdy]; exact hj))
  -- the first difference is at `j`
  rw [hkeq] at hkz hres hrel
  have hjz := hkz
  have hjdz : j ∈ depOf (Q ﹫ 2) qz := by rw [← hdz]; exact hjz
  have hvz : Sz ﹫ j = !((hz' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qz) j, ancOf (Q ﹫ 2) qz (succ j)) :=
    tensorProdTwoAOneSeq_val hQ2 hqz hjdz
  have haN' : (hz' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qz) j ∈
      ndOf (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) := by
    have h' := hzmem hjz
    rw [hvz, pair_mem_sprod_iff] at h'
    exact h'.left
  unfold tensorProdTwoAOneCoordOdr at hrel ⊢
  rw [hvy, hvz, rel_lexProd_iff] at hrel
  obtain ⟨-, ⟨haA, hq'B⟩, hcmp⟩ := hrel
  have hea : (relabelOne trvAZero e) [odrOne (tensorProdTwoAOneTgt (aoc V) ﹫ ((1 : ℕ) : M))]
      ((hz' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qz) j) := by
    rcases hcmp with h' | h'
    · exact h'
    · rw [← h'.left] at haN'
      exact (heN haN').elim
  have haN'' := haN'
  rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hX'1] at haN''
  obtain ⟨w', hw'1, hw'eq⟩ := haN''
  rw [← hw'eq, tensorProdTwoAOneTgt_val_one,
    rel_odrOne_tensorProdOneAZero_iff hX1 he1 (hsub.left hw'1)] at hea
  have hw'R : w' ∈ iniSegRight V (⋃₀ dom (sig V)) :=
    mem_iniSegRight_iff.mpr ⟨(mem_iniSegNds_last_iff hV hm).mpr ((hnd' w').mp hw'1), hea⟩
  have hres' : S2 ↾ j = Sz ↾ j := hrS2.trans hres
  have hqj : ancOf (Q ﹫ 2) q j ∈ ndOf (Q ﹫ 2) := (hTS.anc_mem_nd hq (mem_succ_of_mem hj)).left
  have hc : ancOf (Q ﹫ 2) q (succ j) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q j) :=
    hTS.anc_succ_mem_chd hq hj
  obtain ⟨hqpc, -, -, -, hqp0, hmin⟩ :=
    ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hqj hc
  rcases hwl w' hw'R with hww | hww
  · -- the same image: compare the nodes of `Q(2)`
    rw [hww] at hw'eq
    -- the ancestors of depth `j` agree
    have hanc : ancOf (Q ﹫ 2) qz j = ancOf (Q ﹫ 2) q j := by
      by_cases hj0 : j = ∅
      · obtain ⟨r, hr⟩ := (otciCond_two hQ2).right.right.right.left
        have h1 : ancOf (Q ﹫ 2) qz j ∈ rtOf (Q ﹫ 2) := by rw [hj0]; exact hTS.anc_empty_mem_rt hqz
        have h2 : ancOf (Q ﹫ 2) q j ∈ rtOf (Q ﹫ 2) := by rw [hj0]; exact hTS.anc_empty_mem_rt hq
        rw [hr, mem_singleton_iff] at h1 h2
        rw [h1, h2]
      obtain ⟨-, hj0m, hj0eq⟩ := sUnion_mem_of_ne_empty hjω hj0
      have hv := val_eq_of_restrict_eq hfy hfz hres hj0m (hjsub hj0m) (hodz.transitive _ hjz hj0m)
      rw [tensorProdTwoAOneSeq_val hQ2 hq (by rw [← hdy]; exact hjsub hj0m),
        tensorProdTwoAOneSeq_val hQ2 hqz (by rw [← hdz]; exact hodz.transitive _ hjz hj0m),
        orderedPair_eq_orderedPair_iff, ← hj0eq] at hv
      exact hv.right.symm
    have hc' : ancOf (Q ﹫ 2) qz (succ j) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q j) := by
      rw [← hanc]
      exact hTS.anc_succ_mem_chd hqz hjdz
    have hkey := aoc_uc_eq_of_mem_chdOf hQ2 hqj hc' hc
    rcases hmin _ hc' hkey with hq'eq | hlt'
    · -- `z = E2`
      left
      have hdzeq : depOf (Q ﹫ 2) qz = succ j := by
        rcases olt_trichotomy (ordinal_of_mem ordinal_omega (succ_mem_omega hjω))
          (ordinal_of_mem ordinal_omega hdqz) with h' | h' | h'
        · exfalso
          have h'' := hTS.anc_succ_mem_chd hqz h'.right.right
          change ancOf (Q ﹫ 2) qz (succ (succ j)) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) qz (succ j)) at h''
          rw [hq'eq, hqp0] at h''
          simp at h''
        · exact h'.symm
        · exfalso
          rcases mem_or_eq_of_mem_succ h'.right.right with h'' | h''
          · exact notMem_self _ (hoj.transitive _ h'' hjdz)
          · have h3 : j ∈ (SLOTreeStructure.ofM (Q ﹫ 2)).ts.dep ﹫ qz := hjdz
            rw [h''] at h3
            exact notMem_self _ h3
      have hqzeq : qz = qp := by
        have h' := hTS.anc_dep hqz
        change ancOf (Q ﹫ 2) qz (depOf (Q ﹫ 2) qz) = qz at h'
        rw [hdzeq, hq'eq] at h'
        exact h'.symm
      have hSeq : Sz = S2 := by
        refine hfz.ext hf2s (by rw [hdz, hdzeq, hdS2]) fun i hi ↦ ?_
        rw [hdz, hdzeq] at hi
        rcases mem_or_eq_of_mem_succ hi with hi' | hi'
        · rw [hagree i hi', val_eq_of_restrict_eq hfz hfy hres.symm hi'
            (hodz.transitive _ hjz hi') (hjsub hi')]
        · rw [hi', hvz, hvS2, ← hw'eq, hq'eq]
      have := eq_of_tensorProdTwoAOneSeq_eq hQ2 hT hqz hqp' hhzX hf2' hSeq
      rw [this]
    · refine hright (.inr ⟨j, by rw [hdS2]; exact mem_succ_self j, hjz, hres', ?_⟩)
      unfold tensorProdTwoAOneCoordOdr
      rw [hvS2, hvz, rel_lexProd_iff]
      exact ⟨⟨hX1nd hwX1, mem_ndOf_of_mem_chdOf hS hqpc⟩, ⟨haA, hq'B⟩,
        .inr ⟨by rw [← hw'eq], hlt'⟩⟩
  · -- a larger image
    refine hright (.inr ⟨j, by rw [hdS2]; exact mem_succ_self j, hjz, hres', ?_⟩)
    unfold tensorProdTwoAOneCoordOdr
    rw [hvS2, hvz, rel_lexProd_iff]
    refine ⟨⟨hX1nd hwX1, mem_ndOf_of_mem_chdOf hS hqpc⟩, ⟨haA, hq'B⟩, .inl ?_⟩
    rw [← hw'eq, tensorProdTwoAOneTgt_val_one]
    exact (rel_odrOne_tensorProdOneAZero_iff hX1 hwX1 (hsub.left hw'1) trvAZero).mpr hww

end SuccMin

section SuccMinOne

variable {Q V X q h j z : M}

/-- Children of a node of a tree in `otci_2` with the same key have the same signature -/
theorem sig_uc_eq_of_mem_chdOf {P p c c' : M} (hP : P ∈ otci ((2 : ℕ) : M)) (hp : p ∈ ndOf P)
    (hc : c ∈ chdOf P p) (hc' : c' ∈ chdOf P p) (hk : aoc (uc c') = aoc (uc c)) :
    sig (uc c') = sig (uc c) := by
  obtain ⟨hPs, -, -, -, hchd⟩ := otciCond_two hP
  obtain ⟨q, hq, hqk⟩ := ((hchd p hp).left (aoc (uc c))).mp ⟨c, hc, rfl⟩
  have hmem (x : M) (hx : x ∈ chdOf P p) (hxk : aoc (uc x) = aoc (uc c)) :
      x ∈ losSet (chdlosOf P p ﹫ aoc q) := by
    rw [hqk]
    exact (mem_losSet_chdlosOf_iff hPs hp hc x).mpr ⟨hx, hxk⟩
  rw [((hchd p hp).right.left q hq c' (hmem c' hc' hk)).left,
    ((hchd p hp).right.left q hq c (hmem c hc rfl)).left]

/-- The node `E1` is the successor of `y` in `(Q ⊗ X')(1)` when the right neighbour `w` of the new
entry is the image of the `ucf` of `q_j` -/
theorem succOne_min (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hq : q ∈ ndOf (Q ﹫ 2))
    (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)))
    (hj : j ∈ depOf (Q ﹫ 2) q) (hj0 : j ≠ ∅)
    (hje : sigImg (aoc V) q h j = sigdcn V (⋃₀ dom (sig V)))
    (hnone : ∀ w ∈ iniSegRight V (⋃₀ dom (sig V)),
      ¬ (relabelOne trvAZero w) [odrOne (tensorProdTwoAOneTgt (aoc V) ﹫ ((1 : ℕ) : M))]
        ((h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) q j))))
    (hE : succOne (Q ﹫ 2) q h j ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hz : z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
    (hyz : !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) :
    z = succOne (Q ﹫ 2) q h j ∨
      (succOne (Q ﹫ 2) q h j) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, hnd'⟩ := lastSeg_facts hV hm
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  have hX'1 := val_mem_otci_of_mem_aotci hX' (mem_succ_self _)
  have hT := tensorProdTwoAOneTgt_mem hX
  have he1 : sigdcn V (⋃₀ dom (sig V)) ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) :=
    (siglvl_eq_one hV hm).right
  set e := sigdcn V (⋃₀ dom (sig V)) with he
  obtain ⟨qz, hz', rfl, hqz, hqzr, hhz'X', hhzX, hlt⟩ :=
    exists_of_rel_of_mem_lastSeg hQ hV hm hy hz hyz
  have hdq := hTS.dep_mem_omega hq
  have hjω : j ∈ (ω : M) := ordinal_omega.transitive _ hdq hj
  have hjs : j ∈ succ (depOf (Q ﹫ 2) q) := mem_succ_of_mem hj
  obtain ⟨hqj, hdqj⟩ := hTS.anc_mem_nd hq hjs
  change ancOf (Q ﹫ 2) q j ∈ ndOf (Q ﹫ 2) at hqj
  change depOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q j) = j at hdqj
  have hE' := hE
  rw [succOne] at hE'
  obtain ⟨qj', hqj', -, f1, hf1, he2⟩ := mem_tensorProdTwoAOneNds_iff'.mp hE'
  rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at he2
  obtain ⟨-, hqjeq, hf1eq⟩ := he2
  subst hqjeq hf1eq
  rw [rel_odrOne_tensorProdATwoAOne_iff_of_mem hQ hX hE, succOne, lbl_orderedPair, lbl_orderedPair]
  rw [lbl_orderedPair] at hlt
  set Sy := tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h) with hSy
  set Sz := tensorProdTwoAOneSeq (Q ﹫ 2) !(qz, hz') with hSz
  set S1 := tensorProdTwoAOneSeq (Q ﹫ 2)
    !(ancOf (Q ﹫ 2) q j, embRestrict (uc (ancOf (Q ﹫ 2) q j)) h) with hS1
  have hfy := isFunction_tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h)
  have hfz := isFunction_tensorProdTwoAOneSeq (Q ﹫ 2) !(qz, hz')
  have hS1eq : S1 = Sy ↾ j := tensorProdTwoAOneSeq_embRestrict hQ2 hq hjs hh
  have hdy : dom Sy = depOf (Q ﹫ 2) q := tensorProdTwoAOneSeq_dom _ _
  have hdz : dom Sz = depOf (Q ﹫ 2) qz := tensorProdTwoAOneSeq_dom _ _
  have hdqz := hTS.dep_mem_omega hqz
  have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
  have hjsig : j ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hj
  have hvy : Sy ﹫ j = !(relabelOne trvAZero e, ancOf (Q ﹫ 2) q (succ j)) := by
    rw [hSy, tensorProdTwoAOneSeq_val hQ2 hq hj, (sigImg_spec hQ2 hq hX hh hjsig).right, hje]
  have heN : relabelOne trvAZero e ∉ ndOf (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V))) ﹫
      ((1 : ℕ) : M)) := by
    rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hX'1]
    rintro ⟨w', hw', hwe⟩
    have := relabelOne_injective hX1 (hsub.left hw') he1 hwe
    exact ((hnd' w').mp hw').right this
  have hzmem {i : M} (hi : i ∈ dom Sz) : Sz ﹫ i ∈ ndOf (tensorProdTwoAOneTgt
      (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) ×ˢ ndOf (Q ﹫ 2) := by
    rw [hdz] at hi
    exact tensorProdTwoAOneSeq_val_mem hQ2 hqz hhz'X' hi
  have hnotj (hjz : j ∈ dom Sz) : Sz ﹫ j ≠ Sy ﹫ j := by
    intro h'
    have := hzmem hjz
    rw [h', hvy, pair_mem_sprod_iff] at this
    exact heN this.left
  have hzN : !(dctUZero, !(qz, hz')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) :=
    mem_tensorProdTwoAOneNds_iff'.mpr ⟨qz, hqz, hqzr, hz', hhzX, rfl⟩
  have hoj : Ordinal j := ordinal_of_mem ordinal_omega hjω
  have hodz : Ordinal (dom Sz) := by rw [hdz]; exact ordinal_of_mem ordinal_omega hdqz
  have hjsub : j ⊆ dom Sy := fun z hz ↦ by
    rw [hdy]; exact (ordinal_of_mem ordinal_omega hdq).transitive _ hj hz
  have hfS1 : IsFunction S1 := by rw [hS1eq]; exact hfy.restrict _
  have hdS1 : dom S1 = j := by rw [hS1eq]; exact dom_restrict_of_subset hfy hjsub
  have hagree (i : M) (hi : i ∈ j) : S1 ﹫ i = Sy ﹫ i := by
    rw [hS1eq, val_restrict _ hfy hi (hjsub hi)]
  unfold TensorProdTwoAOneLt at hlt ⊢
  rcases hlt with ⟨hzy, hne⟩ | ⟨k, hky, hkz, hres, hrel⟩
  · have hjz : j ∉ dom Sz := fun hjz ↦ hnotj hjz (val_eq_of_subset_of_mem hfz hfy hzy hjz).symm
    have hzj : dom Sz ⊆ j := subset_of_not_mem_of_ordinal hodz hoj hjz
    have hzS1 : Sz ⊆ S1 := fun p hp ↦ by
      obtain ⟨i, rfl⟩ := hfz.exists_val hp
      have hi : i ∈ dom Sz := by
        rw [hfz.mem_dom_iff]
        exact hp
      rw [← val_eq_of_subset_of_mem hfz hfy hzy hi, ← hagree i (hzj hi)]
      exact (hfS1.mem_dom_iff i).mp (by rw [hdS1]; exact hzj hi)
    by_cases hdeq : dom Sz = j
    · left
      have hSeq : Sz = S1 := hfz.ext hfS1 (by rw [hdeq, hdS1]) fun i hi ↦
        (val_eq_of_subset_of_mem hfz hfS1 hzS1 hi).symm
      rw [eq_of_tensorProdTwoAOneSeq_eq hQ2 hT hqz hqj' hhzX hf1 hSeq]
    · exact .inr ⟨hzN, .inl ⟨hzS1, fun h' ↦ hdeq ((congrArg dom h').trans hdS1)⟩⟩
  have hok : Ordinal k := ordinal_of_mem hodz hkz
  rcases olt_trichotomy hok hoj with hkj | hkeq | hjk
  · have hkj' : k ∈ j := hkj.right.right
    have hkjs : k ⊆ j := hoj.transitive _ hkj'
    refine .inr ⟨hzN, .inr ⟨k, by rw [hdS1]; exact hkj', hkz, ?_, ?_⟩⟩
    · rw [← hres]
      exact hfS1.restrict_eq_restrict hfy (fun z hz ↦ by rw [hdS1]; exact hkjs hz)
        (fun z hz ↦ hjsub (hkjs hz)) fun i hi ↦ hagree i (hkjs hi)
    · rw [hagree k hkj']
      exact hrel
  swap
  · exfalso
    have hjz : j ∈ dom Sz := hodz.transitive _ hkz hjk.right.right
    exact hnotj hjz (val_eq_of_restrict_eq hfz hfy hres.symm hjk.right.right hjz
      (by rw [hdy]; exact hj))
  -- the first difference is at `j`: impossible
  exfalso
  rw [hkeq] at hkz hres hrel
  have hjz := hkz
  have hjdz : j ∈ depOf (Q ﹫ 2) qz := by rw [← hdz]; exact hjz
  have hvz : Sz ﹫ j = !((hz' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qz) j, ancOf (Q ﹫ 2) qz (succ j)) :=
    tensorProdTwoAOneSeq_val hQ2 hqz hjdz
  have haN' : (hz' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qz) j ∈
      ndOf (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) := by
    have h' := hzmem hjz
    rw [hvz, pair_mem_sprod_iff] at h'
    exact h'.left
  unfold tensorProdTwoAOneCoordOdr at hrel
  rw [hvy, hvz, rel_lexProd_iff] at hrel
  obtain ⟨-, -, hcmp⟩ := hrel
  have hea : (relabelOne trvAZero e) [odrOne (tensorProdTwoAOneTgt (aoc V) ﹫ ((1 : ℕ) : M))]
      ((hz' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qz) j) := by
    rcases hcmp with h' | h'
    · exact h'
    · rw [← h'.left] at haN'
      exact (heN haN').elim
  have haN'' := haN'
  rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hX'1] at haN''
  obtain ⟨w', hw'1, hw'eq⟩ := haN''
  rw [← hw'eq, tensorProdTwoAOneTgt_val_one,
    rel_odrOne_tensorProdOneAZero_iff hX1 he1 (hsub.left hw'1)] at hea
  have hw'R : w' ∈ iniSegRight V (⋃₀ dom (sig V)) :=
    mem_iniSegRight_iff.mpr ⟨(mem_iniSegNds_last_iff hV hm).mpr ((hnd' w').mp hw'1), hea⟩
  -- the ancestors of depth `j` agree
  obtain ⟨-, hj0m, hj0eq⟩ := sUnion_mem_of_ne_empty hjω hj0
  have hanc : ancOf (Q ﹫ 2) qz j = ancOf (Q ﹫ 2) q j := by
    have hv := val_eq_of_restrict_eq hfy hfz hres hj0m (hjsub hj0m) (hodz.transitive _ hjz hj0m)
    rw [tensorProdTwoAOneSeq_val hQ2 hq (by rw [← hdy]; exact hjsub hj0m),
      tensorProdTwoAOneSeq_val hQ2 hqz (by rw [← hdz]; exact hodz.transitive _ hjz hj0m),
      orderedPair_eq_orderedPair_iff, ← hj0eq] at hv
    exact hv.right.symm
  have hc : ancOf (Q ﹫ 2) q (succ j) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q j) :=
    hTS.anc_succ_mem_chd hq hj
  have hc' : ancOf (Q ﹫ 2) qz (succ j) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q j) := by
    rw [← hanc]
    exact hTS.anc_succ_mem_chd hqz hjdz
  have hkey := aoc_uc_eq_of_mem_chdOf hQ2 hqj hc' hc
  have hsigeq := sig_uc_eq_of_mem_chdOf hQ2 hqj hc hc' hkey
  have hj1s : succ j ∈ succ (depOf (Q ﹫ 2) q) := succ_mem_succ_of_mem hdq hj
  have hj1sz : succ j ∈ succ (depOf (Q ﹫ 2) qz) := succ_mem_succ_of_mem hdqz hjdz
  obtain ⟨hsig1, hsub1⟩ := uc_ancOf_rel hQ2 hq hj1s
  obtain ⟨hsig1z, hsub1z⟩ := uc_ancOf_rel hQ2 hqz hj1sz
  have hUqz := uc_mem_stduoci_of_mem_otci_two hQ2 hqz
  have hsfq := (uociCond_of_mem_stduoci_one hUq).right.right.right.left.left
  have hsfz := (uociCond_of_mem_stduoci_one hUqz).right.right.right.left.left
  have hdomq : dom (sig (uc q)) = depOf (Q ﹫ 2) q := dom_sig_uc_eq_depOf hQ2 hq
  have hdomz : dom (sig (uc qz)) = depOf (Q ﹫ 2) qz := dom_sig_uc_eq_depOf hQ2 hqz
  have hsd {i : M} (hi : i ∈ succ j) : sigdcn (uc qz) i = sigdcn (uc q) i := by
    have hiq : i ∈ dom (sig (uc q)) := by
      rw [hdomq]
      rcases mem_or_eq_of_mem_succ hi with h' | h'
      · exact (ordinal_of_mem ordinal_omega hdq).transitive _ hj h'
      · rw [h']; exact hj
    have hiz : i ∈ dom (sig (uc qz)) := by
      rw [hdomz]
      rcases mem_or_eq_of_mem_succ hi with h' | h'
      · exact (ordinal_of_mem ordinal_omega hdqz).transitive _ hjdz h'
      · rw [h']; exact hjdz
    rw [sigdcn, sigdcn, ← val_restrict _ hsfz hi hiz, ← hsig1z, hsigeq, hsig1,
      val_restrict _ hsfq hi hiq]
  -- the `ucf` of `q_j` lies between the new node and its image
  have hUj := uc_mem_stduoci_of_mem_otci_two hQ2 hqj
  have hsj : sig (uc (ancOf (Q ﹫ 2) q j)) ≠ ∅ := fun h' ↦ hj0 (by
    rw [← hdqj, ← dom_sig_uc_eq_depOf hQ2 hqj, h', dom_empty])
  obtain ⟨-, -, hsubjj1, hrel⟩ := uc_rel_of_mem_chdOf hQ2 hqj hc
  obtain ⟨-, hrq, hnr, -⟩ := hrel hsj
  have hdomj : dom (sig (uc (ancOf (Q ﹫ 2) q j))) = j := by
    rw [dom_sig_uc_eq_depOf hQ2 hqj, hdqj]
  rw [hdomj] at hnr
  have hrq' := hrq
  rw [ndOf_aoc_val_one_eq hUj, mem_iniSegNds_iff, hdomj] at hrq'
  obtain ⟨i0, hi0, hi0eq⟩ := hrq'
  have hsdj : sigdcn (uc (ancOf (Q ﹫ 2) q j)) i0 = sigdcn (uc q) i0 := by
    obtain ⟨hsigj, -⟩ := uc_ancOf_rel hQ2 hq hjs
    rw [sigdcn, sigdcn, hsigj, val_restrict _ hsfq hi0 (by
      rw [hdomq]; exact (ordinal_of_mem ordinal_omega hdq).transitive _ hj hi0)]
  have hnew : sigdcn (uc (ancOf (Q ﹫ 2) q (succ j))) j = sigdcn (uc q) j := by
    rw [sigdcn, sigdcn, hsig1, val_restrict _ hsfq (mem_succ_self j) hjsig]
  rw [hnew, ← hi0eq, hsdj] at hnr
  -- transport the order to `qz`
  have hk1 : aoc (uc (ancOf (Q ﹫ 2) q (succ j))) = aoc (uc (ancOf (Q ﹫ 2) qz (succ j))) :=
    hkey.symm
  have hujK : sigdcn (uc q) j ∈ ndOf (aoc (uc (ancOf (Q ﹫ 2) qz (succ j))) ﹫ ((1 : ℕ) : M)) := by
    rw [← hk1, ← hnew]
    obtain ⟨hqj1, hdqj1⟩ := hTS.anc_mem_nd hq hj1s
    change ancOf (Q ﹫ 2) q (succ j) ∈ ndOf (Q ﹫ 2) at hqj1
    change depOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q (succ j)) = succ j at hdqj1
    exact (siglvl_eq_one (uc_mem_stduoci_of_mem_otci_two hQ2 hqj1)
      (by rw [dom_sig_uc_eq_depOf hQ2 hqj1, hdqj1]; exact mem_succ_self j)).right
  have hi0K : sigdcn (uc q) i0 ∈ ndOf (aoc (uc (ancOf (Q ﹫ 2) qz (succ j))) ﹫ ((1 : ℕ) : M)) := by
    rw [← hk1, ← hsdj, hi0eq]
    exact hsubjj1.left hrq
  rw [hk1] at hnr
  have hez := (mem_aotciEmbSet_iff.mp hhzX).right.isOtciEmbedding (mem_succ_self _)
  have hTX1 := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hUz1 := val_mem_otci_of_mem_aotci (aoc_mem_aotci_of_mem_stduoci_one hUqz) (mem_succ_self _)
  obtain ⟨-, hodrz⟩ := (isOtciEmbedding_iff_of_mem_otci_one hUz1 hTX1).mp hez
  have hlt1 := hodrz _ (hsub1z.left hujK) _ (hsub1z.left hi0K)
    ((hsub1z.right _ hujK _ hi0K).mp hnr)
  -- the image of `u_{i0}` under `hz'` is that under `h`
  have hi0j : i0 ∈ j := hi0
  have hvi0 := val_eq_of_restrict_eq hfy hfz hres hi0j (hjsub hi0j) (hodz.transitive _ hjz hi0j)
  rw [tensorProdTwoAOneSeq_val hQ2 hq (by rw [← hdy]; exact hjsub hi0j),
    tensorProdTwoAOneSeq_val hQ2 hqz (by rw [← hdz]; exact hodz.transitive _ hjz hi0j),
    orderedPair_eq_orderedPair_iff, hsd (mem_succ_of_mem hi0j)] at hvi0
  rw [hsd (mem_succ_self j)] at hw'eq
  rw [← hw'eq, ← hvi0.left, ← hsdj, hi0eq] at hlt1
  exact hnone w' hw'R hlt1

/-- There is no node of `(Q ⊗ X')(1)` above `y` if the new entry is the first one and has no right
neighbour -/
theorem not_rel_of_succ_none (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hq : q ∈ ndOf (Q ﹫ 2))
    (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)))
    (hj : (∅ : M) ∈ depOf (Q ﹫ 2) q)
    (hje : sigImg (aoc V) q h ∅ = sigdcn V (⋃₀ dom (sig V)))
    (hR : iniSegRight V (⋃₀ dom (sig V)) = ∅)
    (hz : z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M))) :
    ¬ !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z := by
  intro hyz
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, hnd'⟩ := lastSeg_facts hV hm
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  have hX'1 := val_mem_otci_of_mem_aotci hX' (mem_succ_self _)
  have he1 : sigdcn V (⋃₀ dom (sig V)) ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) :=
    (siglvl_eq_one hV hm).right
  obtain ⟨qz, hz', rfl, hqz, hqzr, hhz'X', -, hlt⟩ :=
    exists_of_rel_of_mem_lastSeg hQ hV hm hy hz hyz
  rw [lbl_orderedPair] at hlt
  have hfy := isFunction_tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h)
  have hfz := isFunction_tensorProdTwoAOneSeq (Q ﹫ 2) !(qz, hz')
  have hdz : dom (tensorProdTwoAOneSeq (Q ﹫ 2) !(qz, hz')) = depOf (Q ﹫ 2) qz :=
    tensorProdTwoAOneSeq_dom _ _
  have hdqz := hTS.dep_mem_omega hqz
  have hodz : Ordinal (dom (tensorProdTwoAOneSeq (Q ﹫ 2) !(qz, hz'))) := by
    rw [hdz]; exact ordinal_of_mem ordinal_omega hdqz
  have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
  have hjsig : (∅ : M) ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hj
  -- the depth of `qz` is positive
  have hdz0 : (∅ : M) ∈ dom (tensorProdTwoAOneSeq (Q ﹫ 2) !(qz, hz')) := by
    rw [hdz]
    refine empty_mem_of_ordinal_of_ne_empty (ordinal_of_mem ordinal_omega hdqz) fun h' ↦ hqzr ?_
    exact TreeStructure.mem_rt_iff.mpr ⟨hqz, h'⟩
  -- the first coordinates
  have hvz : tensorProdTwoAOneSeq (Q ﹫ 2) !(qz, hz') ﹫ ∅ =
      !((hz' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qz) ∅, ancOf (Q ﹫ 2) qz (succ ∅)) :=
    tensorProdTwoAOneSeq_val hQ2 hqz (by rw [← hdz]; exact hdz0)
  have hvy : tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h) ﹫ ∅ =
      !(relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))), ancOf (Q ﹫ 2) q (succ ∅)) := by
    rw [tensorProdTwoAOneSeq_val hQ2 hq hj, (sigImg_spec hQ2 hq hX hh hjsig).right, hje]
  have haN' : (hz' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qz) ∅ ∈
      ndOf (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) := by
    have h' := tensorProdTwoAOneSeq_val_mem hQ2 hqz hhz'X' (by rw [← hdz]; exact hdz0)
    rw [hvz, pair_mem_sprod_iff] at h'
    exact h'.left
  have heN : relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))) ∉
      ndOf (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) := by
    rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hX'1]
    rintro ⟨w', hw', hwe⟩
    have := relabelOne_injective hX1 (hsub.left hw') he1 hwe
    exact ((hnd' w').mp hw').right this
  -- the first coordinate of `z` is larger
  have hfirst : (relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V))))
      [odrOne (tensorProdTwoAOneTgt (aoc V) ﹫ ((1 : ℕ) : M))]
        ((hz' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qz) ∅) := by
    unfold TensorProdTwoAOneLt at hlt
    rcases hlt with ⟨hzy, -⟩ | ⟨k, -, hkz, hres, hrel⟩
    · exfalso
      have h' := val_eq_of_subset_of_mem hfz hfy hzy hdz0
      rw [hvz, hvy, orderedPair_eq_orderedPair_iff] at h'
      rw [← h'.left] at haN'
      exact heN haN'
    by_cases hk0 : k = ∅
    · rw [hk0, hvy, hvz] at hrel
      unfold tensorProdTwoAOneCoordOdr at hrel
      rw [rel_lexProd_iff] at hrel
      obtain ⟨-, -, hcmp⟩ := hrel
      rcases hcmp with h' | h'
      · exact h'
      · rw [← h'.left] at haN'
        exact (heN haN').elim
    · exfalso
      have h0k := empty_mem_of_ordinal_of_ne_empty (ordinal_of_mem hodz hkz) hk0
      have h' := val_eq_of_restrict_eq hfy hfz hres h0k
        (by rw [tensorProdTwoAOneSeq_dom]; exact hj) hdz0
      rw [hvy, hvz, orderedPair_eq_orderedPair_iff] at h'
      rw [← h'.left] at haN'
      exact heN haN'
  have haN'' := haN'
  rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hX'1] at haN''
  obtain ⟨w', hw'1, hw'eq⟩ := haN''
  rw [← hw'eq, tensorProdTwoAOneTgt_val_one,
    rel_odrOne_tensorProdOneAZero_iff hX1 he1 (hsub.left hw'1)] at hfirst
  have hw'R : w' ∈ iniSegRight V (⋃₀ dom (sig V)) :=
    mem_iniSegRight_iff.mpr ⟨(mem_iniSegNds_last_iff hV hm).mpr ((hnd' w').mp hw'1), hfirst⟩
  rw [hR] at hw'R
  simp at hw'R

end SuccMinOne

section PrtPieces

/-! ### Pieces of the parent of a node of depth `m > 1` -/

theorem sUnion_least_aboveIn_eq {O S N y E : M} (hO : IsAsymmOn O S) (hN : N ⊆ S)
    (hE : E ∈ N) (hyE : y [O] E) (hmin : ∀ z ∈ N, y [O] z → z = E ∨ E [O] z) :
    ⋃₀ (aboveIn O N y ∩₀ fun z ↦ IsLeastIn O (aboveIn O N y) z) = E := by
  have h : (aboveIn O N y ∩₀ fun z ↦ IsLeastIn O (aboveIn O N y) z) = {E} := by
    ext z
    rw [mem_comprehension_iff, mem_singleton_iff, mem_aboveIn_iff]
    constructor
    · rintro ⟨⟨hz, hyz⟩, hl⟩
      rcases hmin z hz hyz with h | h
      · exact h
      rcases hl E (mem_aboveIn_iff.mpr ⟨hE, hyE⟩) with h' | h'
      · exact h'.symm
      · exact absurd h' (hO E (hN hE) z (hN hz) h)
    · rintro rfl
      refine ⟨⟨hE, hyE⟩, fun r hr ↦ ?_⟩
      rw [mem_aboveIn_iff] at hr
      exact hmin r hr.left hr.right
  rw [h, sUnion_singleton]

theorem sUnion_least_aboveIn_eq_empty {O N y : M} (h : ∀ z ∈ N, ¬ y [O] z) :
    ⋃₀ (aboveIn O N y ∩₀ fun z ↦ IsLeastIn O (aboveIn O N y) z) = ∅ := by
  have h' : (aboveIn O N y ∩₀ fun z ↦ IsLeastIn O (aboveIn O N y) z) = ∅ := by
    ext z
    rw [mem_comprehension_iff, mem_aboveIn_iff]
    simp only [notin_empty, iff_false]
    exact fun hz ↦ h z hz.left.left hz.left.right
  rw [h', sUnion_empty]


theorem posLe_antisymm {i j i' j' : M} (hi : Ordinal i) (hj : Ordinal j)
    (h₁ : (i = i' ∧ j = j') ∨ i ∈ i' ∨ (i = i' ∧ j ∈ j'))
    (h₂ : (i' = i ∧ j' = j) ∨ i' ∈ i ∨ (i' = i ∧ j' ∈ j)) : i = i' ∧ j = j' := by
  rcases h₁ with h₁ | h₁ | ⟨rfl, h₁⟩
  · exact h₁
  · rcases h₂ with ⟨rfl, -⟩ | h₂ | ⟨rfl, -⟩
    · exact (notMem_self _ h₁).elim
    · exact (notMem_self _ (hi.transitive _ h₂ h₁)).elim
    · exact (notMem_self _ h₁).elim
  · rcases h₂ with ⟨-, rfl⟩ | h₂ | ⟨-, h₂⟩
    · exact (notMem_self _ h₁).elim
    · exact (notMem_self _ h₂).elim
    · exact (notMem_self _ (hj.transitive _ h₂ h₁)).elim

theorem firstOccPos_eq {s e i j : M} (hs : IsFinSeqSeq s) (h : IsFirstOcc s e i j) :
    firstOccPos s e = !(i, j) := by
  have hset : (((ω : M) ×ˢ (ω : M)) ∩₀ fun p ↦ IsFirstOcc s e (left p) (right p)) = {!(i, j)} := by
    ext p
    rw [mem_comprehension_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hp, h'⟩
      rw [mem_sprod_iff] at hp
      obtain ⟨a, -, b, -, rfl⟩ := hp
      rw [left_orderedPair, right_orderedPair] at h'
      obtain ⟨ha, hb, hab, h'min⟩ := h'
      obtain ⟨hi, hj, hij, hmin⟩ := h
      obtain ⟨rfl, rfl⟩ := posLe_antisymm (ordinal_of_mem_dom hs hi)
        (ordinal_of_mem_dom_val hs hi hj) (hmin a ha b hb hab) (h'min i hi j hj hij)
      rfl
    · rintro rfl
      refine ⟨?_, by rw [left_orderedPair, right_orderedPair]; exact h⟩
      rw [pair_mem_sprod_iff]
      exact ⟨ordinal_omega.transitive _ hs.right.left h.left,
        ordinal_omega.transitive _ (hs.right.right i h.left).right h.right.left⟩
  rw [firstOccPos, hset, sUnion_singleton]


/-- A position before `(a, b)` is before every position not before `(a, b)` -/
theorem posLt_of_posLt_of_not {a b i j i' j' : M} (ha : Ordinal a) (hb : Ordinal b)
    (hi' : Ordinal i') (hj' : Ordinal j') (h₁ : i ∈ a ∨ (i = a ∧ j ∈ b))
    (h₂ : ¬(i' ∈ a ∨ (i' = a ∧ j' ∈ b))) : i ∈ i' ∨ (i = i' ∧ j ∈ j') := by
  rcases olt_trichotomy ha hi' with h | rfl | h
  · rcases h₁ with h₁ | ⟨rfl, -⟩
    · exact .inl (hi'.transitive _ h.right.right h₁)
    · exact .inl h.right.right
  · rcases olt_trichotomy hb hj' with h' | rfl | h'
    · rcases h₁ with h₁ | ⟨rfl, h₁⟩
      · exact .inl h₁
      · exact .inr ⟨rfl, hj'.transitive _ h'.right.right h₁⟩
    · rcases h₁ with h₁ | ⟨rfl, h₁⟩
      · exact .inl h₁
      · exact .inr ⟨rfl, h₁⟩
    · exact (h₂ (.inr ⟨rfl, h'.right.right⟩)).elim
  · exact (h₂ (.inl h.right.right)).elim

/-- Cutting `s` before the first occurrence of the last entry of its contraction: if `s'` agrees
with `s` before the position `(a, b)`, every entry of `s'` is an entry of `s` other than the last
entry `c_n` of the contraction `c` of `s`, and every other entry occurs in `s` before `(a, b)`,
then the contraction of `s'` is `c ↾ n` -/
theorem contraction_eq_restrict_of_cut {s s' a b n : M} (hs : IsFinSeqSeq s)
    (hs' : IsFinSeqSeq s') (ha : Ordinal a) (hb : Ordinal b)
    (hn : dom (contraction s) = succ n)
    (hagree : ∀ i ∈ dom s, ∀ j ∈ dom (s ﹫ i), (i ∈ a ∨ (i = a ∧ j ∈ b)) →
      i ∈ dom s' ∧ j ∈ dom (s' ﹫ i) ∧ (s' ﹫ i) ﹫ j = (s ﹫ i) ﹫ j)
    (hagree' : ∀ i ∈ dom s', ∀ j ∈ dom (s' ﹫ i), (i ∈ a ∨ (i = a ∧ j ∈ b)) →
      i ∈ dom s ∧ j ∈ dom (s ﹫ i) ∧ (s' ﹫ i) ﹫ j = (s ﹫ i) ﹫ j)
    (hent : ∀ i ∈ dom s', ∀ j ∈ dom (s' ﹫ i),
      (s' ﹫ i) ﹫ j ∈ ctrSet s ∧ (s' ﹫ i) ﹫ j ≠ contraction s ﹫ n)
    (hocc : ∀ x ∈ ctrSet s, x ≠ contraction s ﹫ n →
      ∃ i ∈ dom s, ∃ j ∈ dom (s ﹫ i), (s ﹫ i) ﹫ j = x ∧ (i ∈ a ∨ (i = a ∧ j ∈ b))) :
    contraction s' = contraction s ↾ n := by
  obtain ⟨hcf, hdom, hinj, hran, hord⟩ := isContraction_contraction hs
  set c := contraction s with hc
  have hnsub : n ⊆ dom c := fun k hk ↦ by rw [hn]; exact mem_succ_of_mem hk
  have hdn : dom (c ↾ n) = n := dom_restrict_of_subset hcf hnsub
  have hnω : n ∈ (ω : M) := ordinal_omega.transitive _ hdom (by rw [hn]; exact mem_succ_self n)
  have hcn : ∀ k ∈ n, c ﹫ k ≠ c ﹫ n := fun k hk h ↦
    notMem_self _ (by rwa [hinj k (hnsub hk) n (by rw [hn]; exact mem_succ_self n) h] at hk)
  have hf' : IsFunction (c ↾ n) := hcf.restrict _
  refine (eq_contraction_of_isContraction hs' ⟨hf', by rw [hdn]; exact hnω,
    fun k hk l hl h ↦ ?_, ?_, fun k hk l hl hkl ↦ ?_⟩).symm
  · rw [hdn] at hk hl
    rw [val_restrict _ hcf hk (hnsub hk), val_restrict _ hcf hl (hnsub hl)] at h
    exact hinj k (hnsub hk) l (hnsub hl) h
  · ext x
    rw [hf'.mem_ran_iff, mem_ctrSet_iff hs', hdn]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [val_restrict _ hcf hk (hnsub hk)]
      have hx : c ﹫ k ∈ ctrSet s := by rw [← hran, hcf.mem_ran_iff]; exact ⟨k, hnsub hk, rfl⟩
      obtain ⟨i, hi, j, hj, hv, hlt⟩ := hocc _ hx (hcn k hk)
      obtain ⟨hi', hj', hv'⟩ := hagree i hi j hj hlt
      exact ⟨i, hi', j, hj', hv'.trans hv⟩
    · rintro ⟨i, hi, j, hj, rfl⟩
      obtain ⟨hx, hne⟩ := hent i hi j hj
      rw [← hran, hcf.mem_ran_iff] at hx
      obtain ⟨k, hk, hkv⟩ := hx
      rw [hn] at hk
      rcases mem_or_eq_of_mem_succ hk with hk | rfl
      · exact ⟨k, hk, by rw [val_restrict _ hcf hk (hnsub hk), hkv]⟩
      · exact (hne hkv.symm).elim
  · rw [hdn] at hk hl
    rw [val_restrict _ hcf hk (hnsub hk), val_restrict _ hcf hl (hnsub hl)]
    have hx : c ﹫ k ∈ ctrSet s := by rw [← hran, hcf.mem_ran_iff]; exact ⟨k, hnsub hk, rfl⟩
    obtain ⟨i, hi, j, hj, hv, hpre⟩ := hord k (hnsub hk) l (hnsub hl) hkl
    obtain ⟨i₀, hi₀, j₀, hj₀, hv₀, hlt₀⟩ := hocc _ hx (hcn k hk)
    obtain ⟨i₁, hi₁, j₁, hj₁, hv₁, hmin⟩ := exists_firstOcc hs hx
    -- the first occurrence is before `(a, b)` and before every occurrence of `c_l` in `s`
    have hlt₁ : i₁ ∈ a ∨ (i₁ = a ∧ j₁ ∈ b) := by
      rcases hmin i₀ hi₀ j₀ hj₀ hv₀ with ⟨rfl, rfl⟩ | h | ⟨rfl, h⟩
      · exact hlt₀
      · rcases hlt₀ with h' | ⟨rfl, -⟩
        · exact .inl (ha.transitive _ h' h)
        · exact .inl h
      · rcases hlt₀ with h' | ⟨rfl, h'⟩
        · exact .inl h'
        · exact .inr ⟨rfl, hb.transitive _ h' h⟩
    have hpre₁ : PrecedesAll s (c ﹫ l) i₁ j₁ := fun i' hi' j' hj' hv' ↦ by
      have h₁ := hpre i' hi' j' hj' hv'
      rcases hmin i hi j hj hv with ⟨rfl, rfl⟩ | h | ⟨rfl, h⟩
      · exact h₁
      · rcases h₁ with h₁ | ⟨rfl, -⟩
        · exact .inl ((ordinal_of_mem_dom hs hi').transitive _ h₁ h)
        · exact .inl h
      · rcases h₁ with h₁ | ⟨rfl, h₁⟩
        · exact .inl h₁
        · exact .inr ⟨rfl, (ordinal_of_mem_dom_val hs hi' hj').transitive _ h₁ h⟩
    obtain ⟨hi₁', hj₁', hv₁'⟩ := hagree i₁ hi₁ j₁ hj₁ hlt₁
    refine ⟨i₁, hi₁', j₁, hj₁', hv₁'.trans hv₁, fun i' hi' j' hj' hv' ↦ ?_⟩
    by_cases hlt : i' ∈ a ∨ (i' = a ∧ j' ∈ b)
    · obtain ⟨hi'', hj'', hv''⟩ := hagree' i' hi' j' hj' hlt
      exact hpre₁ i' hi'' j' hj'' (hv''.symm.trans hv')
    · exact posLt_of_posLt_of_not ha hb (ordinal_of_mem_dom hs' hi')
        (ordinal_of_mem_dom_val hs' hi' hj') hlt₁ hlt


section Avoid

variable {Q V q h : M} (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
  (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
include hQ hV hm

/-- A node from `Q(2)` whose signature avoids the new entry is a node over `X'` -/
theorem mem_tensorProdTwoAOneNds_lastSeg_of_avoid
    (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hav : ∀ i ∈ dom (sig (uc q)), sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V))) :
    !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V))) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', -, -, hnd'⟩ := lastSeg_facts hV hm
  obtain ⟨ht0, htsub, htnd⟩ := lastSeg_tgt_facts hV hm
  obtain ⟨q', hq', hqr, h', hh', he⟩ := mem_tensorProdTwoAOneNds_iff'.mp hy
  rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at he
  obtain ⟨-, rfl, rfl⟩ := he
  have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq'
  rw [mem_tensorProdTwoAOneNds_iff']
  refine ⟨q, hq', hqr, h, ?_, rfl⟩
  refine (mem_aotciEmbSet_iff_of_isSubOne (aoc_mem_aotci_of_mem_stduoci_one hUq)
    (tensorProdTwoAOneTgt_mem hX) (tensorProdTwoAOneTgt_mem hX') ht0 htsub).mpr
    ⟨hh', fun z hz ↦ ?_⟩
  have hhf := ((mem_aotciEmbSet_iff.mp hh').right.isOtciEmbedding
    (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  rw [hhf.isFunction.mem_ran_iff, hhf.dom_eq] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  change a ∈ ndOf (aoc (uc q) ﹫ ((1 : ℕ) : M)) at ha
  rw [ndOf_aoc_val_one_eq hUq, mem_iniSegNds_iff] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  rw [(sigImg_spec hQ2 hq' hX hh' hi).right]
  exact htnd _ ((hnd' _).mpr ⟨(sigImg_spec hQ2 hq' hX hh' hi).left, hav i hi⟩)

omit hQ hV hm in
theorem tpSig_eq_empty_of_not_isTpTwo {X z : M} (h : ¬ IsTpTwo Q X z) : tpSig Q X z = ∅ := by
  have hres : IsSetRestrictedTo (fun j ↦ tpSigEntry X z j) (tpSigDom Q X z) :=
    isSetRestrictedTo_of_definable _
  refine (isFunction_toSetRestrictedTo hres).isRelation.eq_empty_of_dom_eq_empty ?_
  rw [dom_toSetRestrictedTo hres, tpSigDom, if_neg h]

omit hV hm in
theorem not_isTpTwo_of_mem_base {X z : M}
    (hz : z ∈ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M))) : ¬ IsTpTwo Q X z := by
  intro h'
  have h'' : z ∈ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ∩
      ndOf (tensorProdTwoAOne (Q ﹫ (2 : M)) X) := by
    rw [mem_inter_iff, ndOf_tensorProdTwoAOne]
    exact ⟨hz, h'⟩
  rw [ndOf_base_inter_ndOf_tensorProdTwoAOne hQ] at h''
  exact notin_empty _ h''

omit hQ in
theorem base_lastSeg_eq :
    tensorProdATwoAOneBase Q (iniSegAoc V (⋃₀ dom (sig V))) = tensorProdATwoAOneBase Q (aoc V) := by
  obtain ⟨hX', h0, -, -⟩ := lastSeg_facts hV hm
  rw [tensorProdATwoAOneBase, tensorProdATwoAOneBase,
    restrict_one_eq_of_val_zero_eq (aoc_mem_aotci_of_mem_stduoci_one hV) hX' h0]

/-- A node of `(Q ⊗ X)(1)` whose signature avoids the new entry is a node of `(Q ⊗ X')(1)` -/
theorem mem_ndOf_lastSeg_of_avoid {z : M}
    (hz : z ∈ ndOf (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
    (hav : ∀ i ∈ dom (tpSig Q (aoc V) z),
      tpSig Q (aoc V) z ﹫ i ≠ !(((1 : ℕ) : M), sigdcn V (⋃₀ dom (sig V)))) :
    z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) := by
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', -, -, -⟩ := lastSeg_facts hV hm
  rw [mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX] at hz
  rw [mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX', base_lastSeg_eq hV hm]
  rcases hz with hz | hz
  · exact .inl hz
  right
  obtain ⟨q, hq, -, h, -, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp hz
  refine mem_tensorProdTwoAOneNds_lastSeg_of_avoid hQ hV hm hz fun i hi he ↦ ?_
  refine hav i (by rw [dom_tpSig_eq hz]; exact hi) ?_
  rw [tpSig_val_eq hQ hz hi, ← he]
  rfl

/-- The signature of a node of `(Q ⊗ X')(1)` is the same in `X` -/
theorem tpSig_lastSeg_eq {z : M}
    (hz : z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M))) :
    tpSig Q (iniSegAoc V (⋃₀ dom (sig V))) z = tpSig Q (aoc V) z := by
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, -⟩ := lastSeg_facts hV hm
  rw [mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX'] at hz
  rcases hz with hz | hz
  · have hz' := hz
    rw [base_lastSeg_eq hV hm] at hz'
    rw [tpSig_eq_empty_of_not_isTpTwo (not_isTpTwo_of_mem_base hQ hz),
      tpSig_eq_empty_of_not_isTpTwo (not_isTpTwo_of_mem_base hQ hz')]
  · obtain ⟨q, -, -, h, -, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp hz
    exact tpSig_eq_of_isSubOne hQ hX hX' h0 hsub hz

end Avoid


/-- The candidate `E2 = (q_k⁺, h')`: the continuous child of `q_k` with the key of `q_{k+1}`,
and `h` with `u_k ↦ D` -/
noncomputable def succTwo (P q h k D : M) : M :=
  !(dctUZero, !(ctChd P (ancOf P q k) (aoc (uc (ancOf P q (succ k)))),
    embUpd h (ancOf P q (succ k)) (sigdcn (uc q) k) D))

theorem sig_val_eq_pair {V i : M} (hV : V ∈ stduoci ((1 : ℕ) : M)) (hi : i ∈ dom (sig V)) :
    sig V ﹫ i = !(((1 : ℕ) : M), sigdcn V i) := by
  have h := (sig_val_lbl_of_mem hV (siglvl_eq_one hV hi).right).right
  rwa [lbl_sigdcn hV hi] at h

/-- The signature of a node from `Q(2)` read off its sequence -/
theorem tpSig_val_eq_seq {Q X p f i : M} (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hz : !(dctUZero, !(p, f)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) (hi : i ∈ dom (sig (uc p))) :
    tpSig Q X !(dctUZero, !(p, f)) ﹫ i = !(((1 : ℕ) : M),
      tpOrig X ((1 : ℕ) : M) (left (tensorProdTwoAOneSeq (Q ﹫ 2) !(p, f) ﹫ i))) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  obtain ⟨p', hp', -, f', -, he⟩ := mem_tensorProdTwoAOneNds_iff'.mp hz
  rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at he
  obtain ⟨-, rfl, rfl⟩ := he
  rw [tpSig_val_eq hQ hz hi, tensorProdTwoAOneSeq_val hQ2 hp' (by
    rw [← dom_sig_uc_eq_depOf hQ2 hp']; exact hi), left_orderedPair]

section SuccSpec

variable {Q V q h k : M} (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
  (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hq : q ∈ ndOf (Q ﹫ 2))
  (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
  (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)))
  (hk : k ∈ depOf (Q ﹫ 2) q)
include hQ hV hm hq hy hh hk

/-- `y` is below the prefix candidate `E1` -/
theorem rel_succOne (hk0 : k ≠ ∅)
    (hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V))) :
    !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
      succOne (Q ﹫ 2) q h k := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, -⟩ := lastSeg_facts hV hm
  have hksig : k ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hk
  have hE := succOne_mem hQ hV hm hq hh hksig hk0 hfirst
  have hEX := ((mem_tensorProdTwoAOneNds_iff_of_isSubOne hQ hX hX' h0 hsub).mp hE).left
  rw [rel_odrOne_tensorProdATwoAOne_iff_of_mem hQ hX hy, succOne, lbl_orderedPair, lbl_orderedPair]
  refine ⟨hEX, .inl ⟨?_, fun h' ↦ ?_⟩⟩
  · rw [tensorProdTwoAOneSeq_embRestrict hQ2 hq (mem_succ_of_mem hk) hh]
    exact restrict_subset _ _
  · have hd := congrArg dom h'
    rw [tensorProdTwoAOneSeq_embRestrict hQ2 hq (mem_succ_of_mem hk) hh,
      dom_restrict_of_subset (isFunction_tensorProdTwoAOneSeq _ _) (by
        rw [tensorProdTwoAOneSeq_dom]
        exact (ordinal_of_mem ordinal_omega (hS.isTreeStructure.dep_mem_omega hq)).transitive _ hk),
      tensorProdTwoAOneSeq_dom] at hd
    rw [hd] at hk
    exact notMem_self _ hk

/-- The signature of `E1` is that of `y` cut at `k` -/
theorem tpSig_succOne (hk0 : k ≠ ∅)
    (hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V))) :
    dom (tpSig Q (aoc V) (succOne (Q ﹫ 2) q h k)) = k ∧
      ∀ i ∈ k, tpSig Q (aoc V) (succOne (Q ﹫ 2) q h k) ﹫ i =
        tpSig Q (aoc V) !(dctUZero, !(q, h)) ﹫ i := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, -⟩ := lastSeg_facts hV hm
  have hksig : k ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hk
  have hE := succOne_mem hQ hV hm hq hh hksig hk0 hfirst
  have hEX := ((mem_tensorProdTwoAOneNds_iff_of_isSubOne hQ hX hX' h0 hsub).mp hE).left
  have hks : k ∈ succ (depOf (Q ﹫ 2) q) := mem_succ_of_mem hk
  obtain ⟨hqk, hdqk⟩ := hTS.anc_mem_nd hq hks
  change ancOf (Q ﹫ 2) q k ∈ ndOf (Q ﹫ 2) at hqk
  change depOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) = k at hdqk
  obtain ⟨hsigk, hsubk⟩ := uc_ancOf_rel hQ2 hq hks
  have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
  have hUk := uc_mem_stduoci_of_mem_otci_two hQ2 hqk
  have hdk : dom (sig (uc (ancOf (Q ﹫ 2) q k))) = k := by
    rw [dom_sig_uc_eq_depOf hQ2 hqk, hdqk]
  rw [succOne] at hEX ⊢
  refine ⟨by rw [dom_tpSig_eq hEX, hdk], fun i hi ↦ ?_⟩
  have hiq : i ∈ dom (sig (uc q)) := (ordinal_of_mem ordinal_omega
    (dom_sig_mem_omega_of_mem_stduoci_one hUq)).transitive _ hksig hi
  have hsd : sigdcn (uc (ancOf (Q ﹫ 2) q k)) i = sigdcn (uc q) i := by
    rw [sigdcn, sigdcn, hsigk,
      val_restrict _ (uociCond_of_mem_stduoci_one hUq).right.right.right.left.left hi hiq]
  have hhf := ((mem_aotciEmbSet_iff.mp hh).right.isOtciEmbedding
    (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  have hun : sigdcn (uc (ancOf (Q ﹫ 2) q k)) i ∈ ndOf (aoc (uc (ancOf (Q ﹫ 2) q k)) ﹫
      ((1 : ℕ) : M)) := (siglvl_eq_one hUk (by rw [hdk]; exact hi)).right
  rw [tpSig_val_eq hQ hEX (by rw [hdk]; exact hi), tpSig_val_eq hQ hy hiq,
    embRestrict_val _ _ natCast_one_mem_two, val_restrict _ hhf.isFunction hun
      (by rw [hhf.dom_eq]; exact hsubk.left hun), hsd]

omit hy in
/-- The `ucf` of `q_k` (for `k > 0`) is at level `1`, and its image is right of the new entry -/
theorem ucf_ancOf_facts (hk0 : k ≠ ∅)
    (hje : sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V))) :
    ucflvldcn (uc (ancOf (Q ﹫ 2) q k)) = !(((1 : ℕ) : M), ucfdcn (uc (ancOf (Q ﹫ 2) q k))) ∧
      ucfdcn (uc (ancOf (Q ﹫ 2) q k)) ∈ ndOf (aoc (uc (ancOf (Q ﹫ 2) q k)) ﹫ ((1 : ℕ) : M)) ∧
      ∃ w ∈ iniSegRight V (⋃₀ dom (sig V)),
        (h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) q k)) = relabelOne trvAZero w := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  have hT := tensorProdTwoAOneTgt_mem hX
  have hTX1 := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have he1 : sigdcn V (⋃₀ dom (sig V)) ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) :=
    (siglvl_eq_one hV hm).right
  have hdq := hTS.dep_mem_omega hq
  have hks : k ∈ succ (depOf (Q ﹫ 2) q) := mem_succ_of_mem hk
  have hk1s : succ k ∈ succ (depOf (Q ﹫ 2) q) := succ_mem_succ_of_mem hdq hk
  obtain ⟨hqk, hdqk⟩ := hTS.anc_mem_nd hq hks
  change ancOf (Q ﹫ 2) q k ∈ ndOf (Q ﹫ 2) at hqk
  change depOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) = k at hdqk
  obtain ⟨hqk1, hdqk1⟩ := hTS.anc_mem_nd hq hk1s
  change ancOf (Q ﹫ 2) q (succ k) ∈ ndOf (Q ﹫ 2) at hqk1
  change depOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q (succ k)) = succ k at hdqk1
  have hc : ancOf (Q ﹫ 2) q (succ k) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) :=
    hTS.anc_succ_mem_chd hq hk
  have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
  have hUk1 := uc_mem_stduoci_of_mem_otci_two hQ2 hqk1
  have hksig : k ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hk
  have hdk : dom (sig (uc (ancOf (Q ﹫ 2) q k))) = k := by
    rw [dom_sig_uc_eq_depOf hQ2 hqk, hdqk]
  have hsk : sig (uc (ancOf (Q ﹫ 2) q k)) ≠ ∅ := fun h' ↦ hk0 (by rw [← hdk, h', dom_empty])
  obtain ⟨-, -, hsubkk1, hrel⟩ := uc_rel_of_mem_chdOf hQ2 hqk hc
  obtain ⟨hlv, hrq, hnr, -⟩ := hrel hsk
  rw [hdk] at hnr
  obtain ⟨hsig1, hsub1⟩ := uc_ancOf_rel hQ2 hq hk1s
  have hsfq := (uociCond_of_mem_stduoci_one hUq).right.right.right.left.left
  have hnew : sigdcn (uc (ancOf (Q ﹫ 2) q (succ k))) k = sigdcn (uc q) k := by
    rw [sigdcn, sigdcn, hsig1, val_restrict _ hsfq (mem_succ_self k) hksig]
  rw [hnew] at hnr
  have hukK : sigdcn (uc q) k ∈ ndOf (aoc (uc (ancOf (Q ﹫ 2) q (succ k))) ﹫ ((1 : ℕ) : M)) := by
    rw [← hnew]
    have hkd : k ∈ dom (sig (uc (ancOf (Q ﹫ 2) q (succ k)))) := by
      rw [dom_sig_uc_eq_depOf hQ2 hqk1, hdqk1]
      exact mem_succ_self k
    exact (siglvl_eq_one hUk1 hkd).right
  have hrK := hsubkk1.left hrq
  have hlt := (hsub1.right _ hukK _ hrK).mp hnr
  have hez := (mem_aotciEmbSet_iff.mp hh).right.isOtciEmbedding (mem_succ_self _)
  have hUq1 := val_mem_otci_of_mem_aotci (aoc_mem_aotci_of_mem_stduoci_one hUq) (mem_succ_self _)
  obtain ⟨-, hodr⟩ := (isOtciEmbedding_iff_of_mem_otci_one hUq1 hTX1).mp hez
  have hlt1 := hodr _ (hsub1.left hukK) _ (hsub1.left hrK) hlt
  obtain ⟨w, hw, hwe⟩ := exists_relabelOne_eq hX hh (hsub1.left hrK)
  refine ⟨hlv, hrq, w, ?_, hwe⟩
  rw [(sigImg_spec hQ2 hq hX hh hksig).right, hje, hwe, tensorProdTwoAOneTgt_val_one,
    rel_odrOne_tensorProdOneAZero_iff hX1 he1 hw] at hlt1
  have hR1 : IsStrictLinearOrder (odrOne (aoc V ﹫ ((1 : ℕ) : M))) (ndOf (aoc V ﹫ ((1 : ℕ) : M))) :=
    (rtlosOf_of_mem_otci_one hX1).left
  refine mem_iniSegRight_iff.mpr ⟨(mem_iniSegNds_last_iff hV hm).mpr ⟨hw, fun h' ↦ ?_⟩, hlt1⟩
  rw [h'] at hlt1
  exact hR1.irrefl _ hlt1

omit hy in
/-- The `ucf` and the type of `E1` -/
theorem tpUcf_succOne (hk0 : k ≠ ∅)
    (hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V)))
    (hje : sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V))) :
    ¬ TpCt Q (iniSegAoc V (⋃₀ dom (sig V))) (succOne (Q ﹫ 2) q h k) ∧
      ∃ w ∈ iniSegRight V (⋃₀ dom (sig V)),
        (h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) q k)) = relabelOne trvAZero w ∧
        tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) (succOne (Q ﹫ 2) q h k) =
          !(((1 : ℕ) : M), w) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  obtain ⟨hX', -, -, hnd'⟩ := lastSeg_facts hV hm
  have hksig : k ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hk
  have hE := succOne_mem hQ hV hm hq hh hksig hk0 hfirst
  have hks : k ∈ succ (depOf (Q ﹫ 2) q) := mem_succ_of_mem hk
  obtain ⟨hqk, -⟩ := hTS.anc_mem_nd hq hks
  change ancOf (Q ﹫ 2) q k ∈ ndOf (Q ﹫ 2) at hqk
  have hc : ancOf (Q ﹫ 2) q (succ k) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) :=
    hTS.anc_succ_mem_chd hq hk
  obtain ⟨hlv, hrq, w, hwR, hwe⟩ := ucf_ancOf_facts hQ hV hm hq hh hk hk0 hje
  have hnct : ctp (uc (ancOf (Q ﹫ 2) q k)) ≠ ct := fun hct ↦ by
    have h' := chdOf_eq_empty_of_ctp_eq_ct (natCast_mem_omega 2) hQ2 hqk hct
    rw [h'] at hc
    exact notin_empty _ hc
  have h3 : ((3 : ℕ) : M) ∈ dom (uc (ancOf (Q ﹫ 2) q k)) := by
    by_contra h3
    have h' : ucflvldcn (uc (ancOf (Q ﹫ 2) q k)) = ∅ := val_eq_empty_of_not_mem_dom h3
    rw [hlv] at h'
    exact orderedPair_ne_empty _ _ h'
  have hwX' : w ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)) :=
    (hnd' w).mpr ((mem_iniSegNds_last_iff hV hm).mp (mem_iniSegRight_iff.mp hwR).left)
  refine ⟨fun h' ↦ hnct (by rw [TpCt, succOne, nodeU_orderedPair] at h'; exact h'.right),
    w, hwR, hwe, ?_⟩
  have hUk := uc_mem_stduoci_of_mem_otci_two hQ2 hqk
  have hhf := ((mem_aotciEmbSet_iff.mp hh).right.isOtciEmbedding
    (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  obtain ⟨-, hsubk⟩ := uc_ancOf_rel hQ2 hq hks
  rw [tpUcf, if_pos (show IsTpTwo Q _ _ from hE), tpUcfTwo, succOne, nodeU_orderedPair,
    nodeH_orderedPair, ucfOrLast,
    if_pos h3, hlv, tpUcfAux, lvl_orderedPair, dcn_orderedPair,
    embRestrict_val _ _ natCast_one_mem_two, val_restrict _ hhf.isFunction hrq
      (by rw [hhf.dom_eq]; exact hsubk.left hrq), hwe, tpOrig_one_relabelOne hX' hwX']

omit hy in
/-- `E2` is a node of `Q(2) ⊗ X'` -/
theorem succTwo_mem {w : M} (hwR : w ∈ iniSegRight V (⋃₀ dom (sig V)))
    (hwl : ∀ r ∈ iniSegRight V (⋃₀ dom (sig V)), r = w ∨ w [iniSegOdr V] r)
    (hne : k ≠ ∅ → relabelOne trvAZero w ≠
      (h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) q k)))
    (hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V)))
    (hje : sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V))) :
    succTwo (Q ﹫ 2) q h k (relabelOne trvAZero w) ∈
      tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V))) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  obtain ⟨hX', -, hsub, hnd'⟩ := lastSeg_facts hV hm
  have hX'1 := val_mem_otci_of_mem_aotci hX' (mem_succ_self _)
  obtain ⟨ht0, htsub, htnd⟩ := lastSeg_tgt_facts hV hm
  have he1 : sigdcn V (⋃₀ dom (sig V)) ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) :=
    (siglvl_eq_one hV hm).right
  have hksig : k ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hk
  have hdq := hTS.dep_mem_omega hq
  have hks : k ∈ succ (depOf (Q ﹫ 2) q) := mem_succ_of_mem hk
  obtain ⟨hqk, hdqk⟩ := hTS.anc_mem_nd hq hks
  change ancOf (Q ﹫ 2) q k ∈ ndOf (Q ﹫ 2) at hqk
  have hc : ancOf (Q ﹫ 2) q (succ k) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) :=
    hTS.anc_succ_mem_chd hq hk
  obtain ⟨hcc, -⟩ := ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hqk hc
  have hwX' : w ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)) :=
    (hnd' w).mpr ((mem_iniSegNds_last_iff hV hm).mp (mem_iniSegRight_iff.mp hwR).left)
  have hwX := hsub.left hwX'
  have hemb := embUpd_mem_aotciEmbSet hQ2 hq hk (tensorProdTwoAOneTgt_mem hX)
    (tensorProdTwoAOneTgt_mem hX') ht0 htsub hh (htnd w hwX') (fun i hi ↦ by
      have hiq : i ∈ dom (sig (uc q)) := (ordinal_of_mem ordinal_omega
        (dom_sig_mem_omega_of_mem_stduoci_one (uc_mem_stduoci_of_mem_otci_two hQ2 hq))).transitive
          _ hksig hi
      rw [(sigImg_spec hQ2 hq hX hh hiq).right]
      exact htnd _ ((hnd' _).mpr ⟨(sigImg_spec hQ2 hq hX hh hiq).left, hfirst i hi⟩))
    (by
      rw [(sigImg_spec hQ2 hq hX hh hksig).right, hje, tensorProdTwoAOneTgt_val_one,
        rel_odrOne_tensorProdOneAZero_iff hX1 he1 hwX]
      exact (mem_iniSegRight_iff.mp hwR).right)
    (fun z hz hlt ↦ by
      rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hX'1] at hz
      obtain ⟨w', hw', rfl⟩ := hz
      rw [(sigImg_spec hQ2 hq hX hh hksig).right, hje, tensorProdTwoAOneTgt_val_one,
        rel_odrOne_tensorProdOneAZero_iff hX1 he1 (hsub.left hw')] at hlt
      have hw'R : w' ∈ iniSegRight V (⋃₀ dom (sig V)) :=
        mem_iniSegRight_iff.mpr ⟨(mem_iniSegNds_last_iff hV hm).mpr ((hnd' w').mp hw'), hlt⟩
      rw [tensorProdTwoAOneTgt_val_one,
        rel_odrOne_tensorProdOneAZero_iff hX1 hwX (hsub.left hw')]
      rcases hwl w' hw'R with h' | h'
      · exact .inl (by rw [h'])
      · exact .inr h')
    hne
  rw [succTwo, mem_tensorProdTwoAOneNds_iff']
  refine ⟨_, mem_ndOf_of_mem_chdOf hS hcc, fun hr ↦ ?_, _, hemb, rfl⟩
  have h0 := (TreeStructure.mem_rt_iff.mp hr).right
  rw [hTS.dep_of_mem_chd _ hqk _ hcc] at h0
  exact succ_ne_empty _ h0

/-- `y` is below `E2`, and the signature of `E2` is that of `y` cut at `k`, followed by `w` -/
theorem rel_succTwo {w : M} (hwR : w ∈ iniSegRight V (⋃₀ dom (sig V)))
    (hwl : ∀ r ∈ iniSegRight V (⋃₀ dom (sig V)), r = w ∨ w [iniSegOdr V] r)
    (hne : k ≠ ∅ → relabelOne trvAZero w ≠
      (h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) q k)))
    (hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V)))
    (hje : sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V))) :
    !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
      succTwo (Q ﹫ 2) q h k (relabelOne trvAZero w) ∧
    dom (tpSig Q (aoc V) (succTwo (Q ﹫ 2) q h k (relabelOne trvAZero w))) = succ k ∧
    (∀ i ∈ k, tpSig Q (aoc V) (succTwo (Q ﹫ 2) q h k (relabelOne trvAZero w)) ﹫ i =
      tpSig Q (aoc V) !(dctUZero, !(q, h)) ﹫ i) ∧
    tpSig Q (aoc V) (succTwo (Q ﹫ 2) q h k (relabelOne trvAZero w)) ﹫ k =
      !(((1 : ℕ) : M), w) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  obtain ⟨hX', h0, hsub, hnd'⟩ := lastSeg_facts hV hm
  obtain ⟨-, htsub, htnd⟩ := lastSeg_tgt_facts hV hm
  have he1 : sigdcn V (⋃₀ dom (sig V)) ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) :=
    (siglvl_eq_one hV hm).right
  have hksig : k ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hk
  have hdq := hTS.dep_mem_omega hq
  have hks : k ∈ succ (depOf (Q ﹫ 2) q) := mem_succ_of_mem hk
  have hk1s : succ k ∈ succ (depOf (Q ﹫ 2) q) := succ_mem_succ_of_mem hdq hk
  obtain ⟨hqk, -⟩ := hTS.anc_mem_nd hq hks
  change ancOf (Q ﹫ 2) q k ∈ ndOf (Q ﹫ 2) at hqk
  obtain ⟨hqk1, hdqk1⟩ := hTS.anc_mem_nd hq hk1s
  change ancOf (Q ﹫ 2) q (succ k) ∈ ndOf (Q ﹫ 2) at hqk1
  change depOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q (succ k)) = succ k at hdqk1
  have hc : ancOf (Q ﹫ 2) q (succ k) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) :=
    hTS.anc_succ_mem_chd hq hk
  obtain ⟨hcc, -, hcsig, -⟩ := ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hqk hc
  have hwX' : w ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)) :=
    (hnd' w).mpr ((mem_iniSegNds_last_iff hV hm).mp (mem_iniSegRight_iff.mp hwR).left)
  have hwX := hsub.left hwX'
  have hE := succTwo_mem hQ hV hm hq hh hk hwR hwl hne hfirst hje
  have hEX := ((mem_tensorProdTwoAOneNds_iff_of_isSubOne hQ hX hX' h0 hsub).mp hE).left
  obtain ⟨hdE, hresE, hvE⟩ := tensorProdTwoAOneSeq_embUpd (D := relabelOne trvAZero w) hQ2 hq hk hh
  have hdc : dom (sig (uc (ctChd (Q ﹫ 2) (ancOf (Q ﹫ 2) q k)
      (aoc (uc (ancOf (Q ﹫ 2) q (succ k))))))) = succ k := by
    rw [hcsig, dom_sig_uc_eq_depOf hQ2 hqk1, hdqk1]
  set Sy := tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h) with hSy
  have hfy := isFunction_tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h)
  have hfE := isFunction_tensorProdTwoAOneSeq (Q ﹫ 2) !(ctChd (Q ﹫ 2) (ancOf (Q ﹫ 2) q k)
    (aoc (uc (ancOf (Q ﹫ 2) q (succ k)))), embUpd h (ancOf (Q ﹫ 2) q (succ k))
      (sigdcn (uc q) k) (relabelOne trvAZero w))
  have hdy : dom Sy = depOf (Q ﹫ 2) q := tensorProdTwoAOneSeq_dom _ _
  have hksub : k ⊆ dom Sy := fun z hz ↦ by
    rw [hdy]; exact (ordinal_of_mem ordinal_omega hdq).transitive _ hk hz
  have hagree (i : M) (hi : i ∈ k) :
      tensorProdTwoAOneSeq (Q ﹫ 2) !(ctChd (Q ﹫ 2) (ancOf (Q ﹫ 2) q k)
        (aoc (uc (ancOf (Q ﹫ 2) q (succ k)))), embUpd h (ancOf (Q ﹫ 2) q (succ k))
          (sigdcn (uc q) k) (relabelOne trvAZero w)) ﹫ i = Sy ﹫ i := by
    have h1 := val_restrict _ hfE hi (by rw [hdE]; exact mem_succ_of_mem hi)
    rw [hresE, val_restrict _ hfy hi (hksub hi)] at h1
    exact h1.symm
  refine ⟨?_, ?_, fun i hi ↦ ?_, ?_⟩
  · rw [rel_odrOne_tensorProdATwoAOne_iff_of_mem hQ hX hy, succTwo, lbl_orderedPair,
      lbl_orderedPair]
    refine ⟨hEX, .inr ⟨k, by rw [hdy]; exact hk, by rw [hdE]; exact mem_succ_self k,
      hresE.symm, ?_⟩⟩
    rw [hvE, tensorProdTwoAOneSeq_val hQ2 hq hk, tensorProdTwoAOneCoordOdr, rel_lexProd_iff]
    refine ⟨⟨(tensorProdTwoAOneSeq_val_mem hQ2 hq hh hk |> fun h' ↦ by
        rw [tensorProdTwoAOneSeq_val hQ2 hq hk, pair_mem_sprod_iff] at h'; exact h'.left),
      hTS.anc_mem_nd hq hk1s |>.left⟩,
      ⟨htsub.left (htnd w hwX'), mem_ndOf_of_mem_chdOf hS hcc⟩, .inl ?_⟩
    rw [(sigImg_spec hQ2 hq hX hh hksig).right, hje]
    change (relabelOne trvAZero _) [odrOne (tensorProdTwoAOneTgt (aoc V) ﹫ ((1 : ℕ) : M))] _
    rw [tensorProdTwoAOneTgt_val_one, rel_odrOne_tensorProdOneAZero_iff hX1 he1 hwX]
    exact (mem_iniSegRight_iff.mp hwR).right
  · rw [succTwo, dom_tpSig_eq hEX, hdc]
  · rw [succTwo, tpSig_val_eq_seq hQ hEX (by rw [hdc]; exact mem_succ_of_mem hi), hagree i hi,
      tpSig_val_eq_seq hQ hy (by
        have := hksub hi
        rw [hdy, ← dom_sig_uc_eq_depOf hQ2 hq] at this
        exact this)]
  · rw [succTwo, tpSig_val_eq_seq hQ hEX (by rw [hdc]; exact mem_succ_self k), hvE,
      left_orderedPair, tpOrig_one_relabelOne hX hwX]

omit hy in
/-- `E2` is of type `ct`, with `ucf` the image `w` of its newest entry -/
theorem tpUcf_succTwo {w : M} (hwR : w ∈ iniSegRight V (⋃₀ dom (sig V)))
    (hwl : ∀ r ∈ iniSegRight V (⋃₀ dom (sig V)), r = w ∨ w [iniSegOdr V] r)
    (hne : k ≠ ∅ → relabelOne trvAZero w ≠
      (h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) q k)))
    (hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V)))
    (hje : sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V))) :
    tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) (succTwo (Q ﹫ 2) q h k (relabelOne trvAZero w)) =
      !(((1 : ℕ) : M), w) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  obtain ⟨hX', -, -, hnd'⟩ := lastSeg_facts hV hm
  have hksig : k ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hk
  have hdq := hTS.dep_mem_omega hq
  have hks : k ∈ succ (depOf (Q ﹫ 2) q) := mem_succ_of_mem hk
  have hk1s : succ k ∈ succ (depOf (Q ﹫ 2) q) := succ_mem_succ_of_mem hdq hk
  obtain ⟨hqk, -⟩ := hTS.anc_mem_nd hq hks
  change ancOf (Q ﹫ 2) q k ∈ ndOf (Q ﹫ 2) at hqk
  obtain ⟨hqk1, hdqk1⟩ := hTS.anc_mem_nd hq hk1s
  change ancOf (Q ﹫ 2) q (succ k) ∈ ndOf (Q ﹫ 2) at hqk1
  change depOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q (succ k)) = succ k at hdqk1
  have hc : ancOf (Q ﹫ 2) q (succ k) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) :=
    hTS.anc_succ_mem_chd hq hk
  obtain ⟨hcc, -, hcsig, hcct, -⟩ :=
    ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hqk hc
  set c := ctChd (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) (aoc (uc (ancOf (Q ﹫ 2) q (succ k)))) with hcdef
  have hcn := mem_ndOf_of_mem_chdOf hS hcc
  have hUc := uc_mem_stduoci_of_mem_otci_two hQ2 hcn
  have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
  have hdom3 : dom (uc c) = ((3 : ℕ) : M) :=
    dom_eq_three_of_ctp_eq_ct (natCast_mem_omega 1) (mem_stduoci_iff.mp hUc).left hcct
  have h3 : ((3 : ℕ) : M) ∉ dom (uc c) := by rw [hdom3]; exact notMem_self _
  have hdc : dom (sig (uc c)) = succ k := by
    rw [hcsig, dom_sig_uc_eq_depOf hQ2 hqk1, hdqk1]
  have hkω : k ∈ (ω : M) := ordinal_omega.transitive _ hdq hk
  have hlast : ⋃₀ dom (sig (uc c)) = k := by
    rw [hdc, sUnion_succ (ordinal_of_mem ordinal_omega hkω).transitive]
  obtain ⟨hsig1, hsub1⟩ := uc_ancOf_rel hQ2 hq hk1s
  have hsfq := (uociCond_of_mem_stduoci_one hUq).right.right.right.left.left
  have hsdc : sigdcn (uc c) k = sigdcn (uc q) k := by
    rw [sigdcn, sigdcn, hcsig, hsig1, val_restrict _ hsfq (mem_succ_self k) hksig]
  have hE := succTwo_mem hQ hV hm hq hh hk hwR hwl hne hfirst hje
  have hwX' : w ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)) :=
    (hnd' w).mpr ((mem_iniSegNds_last_iff hV hm).mp (mem_iniSegRight_iff.mp hwR).left)
  have he := (mem_aotciEmbSet_iff.mp hh).right
  have hinj := (he.isOtciEmbedding (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  have hfK : IsFunction (lvlOneRes h (ancOf (Q ﹫ 2) q (succ k))) := hinj.isFunction.restrict _
  have hkc : k ∈ dom (sig (uc c)) := by rw [hdc]; exact mem_succ_self k
  rw [tpUcf, if_pos (show IsTpTwo Q _ _ from hE), tpUcfTwo, succTwo, nodeU_orderedPair,
    nodeH_orderedPair, ucfOrLast, if_neg h3, hlast, sig_val_eq_pair hUc hkc, tpUcfAux,
    lvl_orderedPair, dcn_orderedPair, embUpd_val_one hh,
    hsdc, val_update_self hfK, tpOrig_one_relabelOne hX' hwX']

/-- The successor `D` of `y` in `(Q ⊗ X')(1)`: either there is none (and then `k = 0` and the new
entry has no right neighbour), or `D` is a node from `Q(2)` whose signature is that of `y` cut at
`k`, possibly followed by an old entry if `D` is of type `ct`, and whose `ucf` is that of
`V | m'` -/
theorem succ_spec (hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V)))
    (hje : sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V))) :
    (⋃₀ (aboveIn (odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
        (ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
        !(dctUZero, !(q, h)) ∩₀ fun z ↦ IsLeastIn
          (odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
          (aboveIn (odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
            (ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
            !(dctUZero, !(q, h))) z) = ∅ ∧
      k = ∅ ∧ iniSegRight V (⋃₀ dom (sig V)) = ∅ ∧
      ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
        ¬ !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) ∨
    ∃ D, ⋃₀ (aboveIn (odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
        (ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
        !(dctUZero, !(q, h)) ∩₀ fun z ↦ IsLeastIn
          (odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
          (aboveIn (odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
            (ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
            !(dctUZero, !(q, h))) z) = D ∧
      D ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V))) ∧
      !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] D ∧
      (∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
        !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
          z = D ∨ D [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) ∧
      (∀ i ∈ k, i ∈ dom (tpSig Q (aoc V) D) ∧
        tpSig Q (aoc V) D ﹫ i = tpSig Q (aoc V) !(dctUZero, !(q, h)) ﹫ i) ∧
      dom (tpSig Q (aoc V) D) ⊆ succ k ∧
      (TpCt Q (iniSegAoc V (⋃₀ dom (sig V))) D → k ∈ dom (tpSig Q (aoc V) D)) ∧
      tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) D = iniSegUcf V (⋃₀ dom (sig V)) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  obtain ⟨hX', h0, hsub, hnd'⟩ := lastSeg_facts hV hm
  have hB1 := val_mem_otci_of_mem_aotci (tensorProdATwoAOne_mem_aotci hQ hX) (mem_succ_self _)
  have hO := (rtlosOf_of_mem_otci_one hB1).left
  have hBsub := isSubOne_tensorProdATwoAOne hQ hX hX' h0 hsub
  have hksig : k ∈ dom (sig (uc q)) := by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hk
  have hR1 : IsStrictLinearOrder (odrOne (aoc V ﹫ ((1 : ℕ) : M))) (ndOf (aoc V ﹫ ((1 : ℕ) : M))) :=
    (rtlosOf_of_mem_otci_one hX1).left
  have hN (z : M) (hz : z ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V)))) :
      z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) :=
    (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX').mpr (.inr hz)
  have hCX (z : M) (hz : z ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V)))) :
      z ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) :=
    ((mem_tensorProdTwoAOneNds_iff_of_isSubOne hQ hX hX' h0 hsub).mp hz).left
  by_cases hR : iniSegRight V (⋃₀ dom (sig V)) = ∅
  · have hk0 : k = ∅ := by
      by_contra hk0
      obtain ⟨-, -, w, hw, -⟩ := ucf_ancOf_facts hQ hV hm hq hh hk hk0 hje
      rw [hR] at hw
      exact notin_empty _ hw
    subst hk0
    have hnone : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫
        ((1 : ℕ) : M)), ¬ !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫
          ((1 : ℕ) : M))] z := fun z hz ↦ not_rel_of_succ_none hQ hV hm hq hy hh hk hje hR hz
    exact .inl ⟨sUnion_least_aboveIn_eq_empty hnone, rfl, hR, hnone⟩
  right
  obtain ⟨w, hwR, hwl, hucf⟩ := iniSegUcf_of_ne_empty hV hm hR
  have hwX : w ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) :=
    ((mem_iniSegNds_last_iff hV hm).mp (mem_iniSegRight_iff.mp hwR).left).left
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
    have hmin : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫
        ((1 : ℕ) : M)), !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫
          ((1 : ℕ) : M))] z → z = succOne (Q ﹫ 2) q h k ∨ (succOne (Q ﹫ 2) q h k)
            [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z := fun z hz hyz ↦
      succOne_min hQ hV hm hq hy hh hk hk0 hje hnone (hCX _ hE) hz hyz
    obtain ⟨hdom, hval⟩ := tpSig_succOne hQ hV hm hq hy hh hk hk0 hfirst
    obtain ⟨hnct, w', hw'R, hw'e, hucf'⟩ := tpUcf_succOne hQ hV hm hq hh hk hk0 hfirst hje
    have hw'X := ((mem_iniSegNds_last_iff hV hm).mp (mem_iniSegRight_iff.mp hw'R).left).left
    have hww : w' = w := relabelOne_injective hX1 hw'X hwX (hw'e.symm.trans hrw)
    refine ⟨_, sUnion_least_aboveIn_eq hO.isAsymmOn hBsub.left (hN _ hE) hlt hmin, hE, hlt, hmin,
      fun i hi ↦ ⟨by rw [hdom]; exact hi, hval i hi⟩, ?_, fun h' ↦ (hnct h').elim,
      by rw [hucf', hww, hucf]⟩
    rw [hdom]
    exact fun _ h' ↦ mem_succ_of_mem h'
  · have hne : k ≠ ∅ → relabelOne trvAZero w ≠
        (h ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf (Q ﹫ 2) q k)) := fun hk0 h' ↦ hc ⟨hk0, h'.symm⟩
    have hE := succTwo_mem hQ hV hm hq hh hk hwR hwl hne hfirst hje
    obtain ⟨hlt, hdom, hval, -⟩ := rel_succTwo hQ hV hm hq hy hh hk hwR hwl hne hfirst hje
    have hmin : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫
        ((1 : ℕ) : M)), !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫
          ((1 : ℕ) : M))] z → z = succTwo (Q ﹫ 2) q h k (relabelOne trvAZero w) ∨
            (succTwo (Q ﹫ 2) q h k (relabelOne trvAZero w))
              [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z := fun z hz hyz ↦
      succTwo_min hQ hV hm hq hy hh hk hje hwR hwl (hCX _ hE) hz hyz
    refine ⟨_, sUnion_least_aboveIn_eq hO.isAsymmOn hBsub.left (hN _ hE) hlt hmin, hE, hlt, hmin,
      fun i hi ↦ ⟨by rw [hdom]; exact mem_succ_of_mem hi, hval i hi⟩,
      by rw [hdom]; exact fun _ h' ↦ h',
      fun _ ↦ by rw [hdom]; exact mem_succ_self k,
      by rw [tpUcf_succTwo hQ hV hm hq hh hk hwR hwl hne hfirst hje, hucf]⟩

end SuccSpec


section TLevel

theorem embTpSigs_val {Q X U σ i : M} (hU : U ∈ stduoci ((1 : ℕ) : M))
    (hi : i ∈ dom (sig U)) :
    embTpSigs Q X U σ ﹫ i = tpSig Q X ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn U i) := by
  have hres : IsSetRestrictedTo (fun i ↦ embTpSigEntry Q X U σ i) (dom (sig U)) :=
    isSetRestrictedTo_of_definable _
  rw [embTpSigs, val_toSetRestrictedTo hres hi, embTpSigEntry, (siglvl_eq_one hU hi).left]

theorem dom_embTpSigs (Q X U σ : M) : dom (embTpSigs Q X U σ) = dom (sig U) := by
  have hres : IsSetRestrictedTo (fun i ↦ embTpSigEntry Q X U σ i) (dom (sig U)) :=
    isSetRestrictedTo_of_definable _
  rw [embTpSigs, dom_toSetRestrictedTo hres]

/-- The rows before the row of the first occurrence of `e` avoid `e` -/
theorem row_avoid {s e l k i : M} (hs : IsFinSeqSeq s) (hfo : IsFirstOcc s e l k) (hi : i ∈ l) :
    ∀ j ∈ dom (s ﹫ i), (s ﹫ i) ﹫ j ≠ e := by
  intro j hj he
  have hl := ordinal_of_mem_dom hs hfo.left
  have hid : i ∈ dom s := (ordinal_of_mem ordinal_omega hs.right.left).transitive _ hfo.left hi
  rcases hfo.right.right.right i hid j hj he with ⟨rfl, -⟩ | h | ⟨rfl, -⟩
  · exact notMem_self _ hi
  · exact notMem_self _ (hl.transitive _ hi h)
  · exact notMem_self _ hi

/-- Every entry other than the last entry of the contraction occurs before the first occurrence of
the last entry -/
theorem occ_before {s n l k : M} (hs : IsFinSeqSeq s) (hn : dom (contraction s) = succ n)
    (hfo : IsFirstOcc s (contraction s ﹫ n) l k) :
    ∀ x ∈ ctrSet s, x ≠ contraction s ﹫ n →
      ∃ i ∈ dom s, ∃ j ∈ dom (s ﹫ i), (s ﹫ i) ﹫ j = x ∧ (i ∈ l ∨ (i = l ∧ j ∈ k)) := by
  intro x hx hne
  obtain ⟨hcf, -, -, hran, hord⟩ := isContraction_contraction hs
  rw [← hran, hcf.mem_ran_iff, hn] at hx
  obtain ⟨i₀, hi₀, rfl⟩ := hx
  rcases mem_or_eq_of_mem_succ hi₀ with hi₀ | rfl
  · obtain ⟨i, hi, j, hj, hv, hpre⟩ := hord i₀ (by rw [hn]; exact mem_succ_of_mem hi₀) n
      (by rw [hn]; exact mem_succ_self n) hi₀
    obtain ⟨hl, hk, hv', -⟩ := hfo
    exact ⟨i, hi, j, hj, hv, hpre l hl k hk hv'⟩
  · exact (hne rfl).elim

/-- For `0 < l < |t|`, the `ucf` of `t_l` is at level `1`, it is the `i`-th node of the signature
of `t` for some `i < l`, and its image is above that of the `l`-th node -/
theorem ucf_anc_rel {P t l σ B : M} (hP : P ∈ otci ((2 : ℕ) : M)) (ht : t ∈ ndOf P)
    (hl : l ∈ depOf P t) (hl0 : l ≠ ∅) (hB : B ∈ aotci ((1 : ℕ) : M))
    (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) B) :
    ucflvldcn (uc (ancOf P t l)) = !(((1 : ℕ) : M), ucfdcn (uc (ancOf P t l))) ∧
      (∃ i ∈ l, ucfdcn (uc (ancOf P t l)) = sigdcn (uc t) i) ∧
      ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l) [odrOne (B ﹫ ((1 : ℕ) : M))]
        ((σ ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf P t l))) := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  have hB1 := val_mem_otci_of_mem_aotci hB (mem_succ_self _)
  have hdt := hTS.dep_mem_omega ht
  have hls : l ∈ succ (depOf P t) := mem_succ_of_mem hl
  have hl1s : succ l ∈ succ (depOf P t) := succ_mem_succ_of_mem hdt hl
  obtain ⟨htl, hdtl⟩ := hTS.anc_mem_nd ht hls
  change ancOf P t l ∈ ndOf P at htl
  change depOf P (ancOf P t l) = l at hdtl
  obtain ⟨htl1, hdtl1⟩ := hTS.anc_mem_nd ht hl1s
  change ancOf P t (succ l) ∈ ndOf P at htl1
  change depOf P (ancOf P t (succ l)) = succ l at hdtl1
  have hc : ancOf P t (succ l) ∈ chdOf P (ancOf P t l) := hTS.anc_succ_mem_chd ht hl
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hUl := uc_mem_stduoci_of_mem_otci_two hP htl
  have hUl1 := uc_mem_stduoci_of_mem_otci_two hP htl1
  have hlsig : l ∈ dom (sig (uc t)) := by rw [dom_sig_uc_eq_depOf hP ht]; exact hl
  have hdl : dom (sig (uc (ancOf P t l))) = l := by rw [dom_sig_uc_eq_depOf hP htl, hdtl]
  have hsl : sig (uc (ancOf P t l)) ≠ ∅ := fun h' ↦ hl0 (by rw [← hdl, h', dom_empty])
  obtain ⟨-, -, hsubll1, hrel⟩ := uc_rel_of_mem_chdOf hP htl hc
  obtain ⟨hlv, hrq, hnr, -⟩ := hrel hsl
  rw [hdl] at hnr
  obtain ⟨hsig1, hsub1⟩ := uc_ancOf_rel hP ht hl1s
  obtain ⟨hsigl, -⟩ := uc_ancOf_rel hP ht hls
  have hsft := (uociCond_of_mem_stduoci_one hUt).right.right.right.left.left
  have hnew : sigdcn (uc (ancOf P t (succ l))) l = sigdcn (uc t) l := by
    rw [sigdcn, sigdcn, hsig1, val_restrict _ hsft (mem_succ_self l) hlsig]
  rw [hnew] at hnr
  have hulK : sigdcn (uc t) l ∈ ndOf (aoc (uc (ancOf P t (succ l))) ﹫ ((1 : ℕ) : M)) := by
    rw [← hnew]
    have hld : l ∈ dom (sig (uc (ancOf P t (succ l)))) := by
      rw [dom_sig_uc_eq_depOf hP htl1, hdtl1]
      exact mem_succ_self l
    exact (siglvl_eq_one hUl1 hld).right
  have hrK := hsubll1.left hrq
  have hlt := (hsub1.right _ hulK _ hrK).mp hnr
  have hez := (mem_aotciEmbSet_iff.mp hσ).right.isOtciEmbedding (mem_succ_self _)
  have hUt1 := val_mem_otci_of_mem_aotci (aoc_mem_aotci_of_mem_stduoci_one hUt) (mem_succ_self _)
  obtain ⟨-, hodr⟩ := (isOtciEmbedding_iff_of_mem_otci_one hUt1 hB1).mp hez
  refine ⟨hlv, ?_, hodr _ (hsub1.left hulK) _ (hsub1.left hrK) hlt⟩
  have hrq' := hrq
  rw [ndOf_aoc_val_one_eq hUl, mem_iniSegNds_iff, hdl] at hrq'
  obtain ⟨i, hi, hie⟩ := hrq'
  have hit : i ∈ dom (sig (uc t)) := (ordinal_of_mem ordinal_omega
    (dom_sig_mem_omega_of_mem_stduoci_one hUt)).transitive _ hlsig hi
  refine ⟨i, hi, ?_⟩
  rw [← hie, sigdcn, sigdcn, hsigl, val_restrict _ hsft hi hit]

theorem left_empty_eq_empty : left (∅ : M) = ∅ :=
  left_of_not_isOrderedPair fun ⟨x, y, h⟩ ↦ orderedPair_ne_empty x y h.symm

theorem ucflvl_eq_empty_of_not_mem {U : M} (h : ((3 : ℕ) : M) ∉ dom U) : ucflvl U = ∅ := by
  rw [ucflvl, ucflvldcn, val_eq_empty_of_not_mem_dom h]
  exact left_empty_eq_empty

/-- The `ucf` of `U | k` for `k > 0` -/
theorem ucflvldcn_iniSeg {U k : M} (hk0 : k ≠ ∅) :
    ucflvldcn (iniSeg U k) = iniSegUcf U k ∧ ucfdr (iniSeg U k) = lf := by
  rw [iniSeg, if_neg hk0, ucflvldcn_ciQuint, ucfdr_ciQuint]
  exact ⟨rfl, rfl⟩

/-- A root of `P ∈ otci_2` has no `ucf` -/
theorem not_mem_dom_uc_of_mem_rtOf {P r : M} (hP : P ∈ otci ((2 : ℕ) : M)) (hr : r ∈ rtOf P) :
    ((3 : ℕ) : M) ∉ dom (uc r) := by
  obtain ⟨-, -, hroot, -, -⟩ := otciCond_two hP
  have h1 : ((1 : ℕ) : M) ∈ (ω : M) := natCast_mem_omega 1
  have hru := hroot r hr
  have hs := sig_eq_empty_of_mem_trvuoci h1 hru
  have hc := uociCond_of_mem_stduoci_one (mem_trvuoci_iff.mp hru).left
  have h3 : dom (uc r) = ((3 : ℕ) : M) :=
    hc.right.right.right.right.right.right.left.mpr (.inl ⟨hs, isOdd_one⟩)
  rw [h3]
  exact notMem_self _

/-- The image of the `ucf` of the root ancestor is empty -/
theorem ucfImg_ancOf_empty {P t σ : M} (hP : P ∈ otci ((2 : ℕ) : M)) (ht : t ∈ ndOf P) :
    ucfImg σ (uc (ancOf P t ∅)) = ∅ := by
  have hTS := (show (SLOTreeStructure.ofM P).IsSLOTreeStructure from
    (otciCond_two hP).left).isTreeStructure
  have hr : ancOf P t ∅ ∈ rtOf P := hTS.anc_empty_mem_rt ht
  rw [ucfImg, if_pos (ucflvl_eq_empty_of_not_mem (not_mem_dom_uc_of_mem_rtOf hP hr))]

section Rows

variable {P Q V t σ l : M} (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
  (hV : V ∈ stduoci ((1 : ℕ) : M)) (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (ht : t ∈ ndOf P)
  (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q (aoc V)))
include hP hQ hV hm ht hσ

omit hQ hV hm hσ in
theorem sigdcn_anc {i : M} (hl : l ∈ succ (depOf P t)) (hi : i ∈ l) :
    sigdcn (uc (ancOf P t l)) i = sigdcn (uc t) i := by
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hsft := (uociCond_of_mem_stduoci_one hUt).right.right.right.left.left
  obtain ⟨hsigl, -⟩ := uc_ancOf_rel hP ht hl
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hdt := hS.isTreeStructure.dep_mem_omega ht
  have hit : i ∈ dom (sig (uc t)) := by
    rw [dom_sig_uc_eq_depOf hP ht]
    rcases mem_or_eq_of_mem_succ hl with h' | rfl
    · exact (ordinal_of_mem ordinal_omega hdt).transitive _ h' hi
    · exact hi
  rw [sigdcn, sigdcn, hsigl, val_restrict _ hsft hi hit]

/-- The rows of the parent `(t_l, σ ↾ t_l)` are the first `l` rows -/
theorem embTpSigs_embRestrict (hl : l ∈ succ (depOf P t))
    (hN : ∀ i ∈ l, (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i ∈
      ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M))) :
    dom (embTpSigs Q (iniSegAoc V (⋃₀ dom (sig V))) (uc (ancOf P t l))
      (embRestrict (uc (ancOf P t l)) σ)) = l ∧
    ∀ i ∈ l, embTpSigs Q (iniSegAoc V (⋃₀ dom (sig V))) (uc (ancOf P t l))
      (embRestrict (uc (ancOf P t l)) σ) ﹫ i = embTpSigs Q (aoc V) (uc t) σ ﹫ i := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  obtain ⟨htl, hdtl⟩ := hTS.anc_mem_nd ht hl
  change ancOf P t l ∈ ndOf P at htl
  change depOf P (ancOf P t l) = l at hdtl
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hUl := uc_mem_stduoci_of_mem_otci_two hP htl
  have hdl : dom (sig (uc (ancOf P t l))) = l := by rw [dom_sig_uc_eq_depOf hP htl, hdtl]
  obtain ⟨-, hsubl⟩ := uc_ancOf_rel hP ht hl
  have hhf := ((mem_aotciEmbSet_iff.mp hσ).right.isOtciEmbedding
    (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  refine ⟨by rw [dom_embTpSigs, hdl], fun i hi ↦ ?_⟩
  have hil : i ∈ dom (sig (uc (ancOf P t l))) := by rw [hdl]; exact hi
  have hit : i ∈ dom (sig (uc t)) := by
    have hdt := hTS.dep_mem_omega ht
    rw [dom_sig_uc_eq_depOf hP ht]
    rcases mem_or_eq_of_mem_succ hl with h' | rfl
    · exact (ordinal_of_mem ordinal_omega hdt).transitive _ h' hi
    · exact hi
  have hun := (siglvl_eq_one hUl hil).right
  rw [embTpSigs_val hUl hil, embTpSigs_val hUt hit, embRestrict_val _ _ natCast_one_mem_two,
    val_restrict _ hhf.isFunction hun (by rw [hhf.dom_eq]; exact hsubl.left hun),
    sigdcn_anc hP ht hl hi]
  exact tpSig_lastSeg_eq hQ hV hm (hN i hi)

/-- The rows of the parent `(t_l⁺, σ')`: the first `l` rows, then the signature of `D` -/
theorem embTpSigs_embUpd {D : M} (hl : l ∈ depOf P t)
    (hN : ∀ i ∈ l, (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i ∈
      ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
    (hD : D ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M))) :
    dom (embTpSigs Q (iniSegAoc V (⋃₀ dom (sig V)))
      (uc (ctChd P (ancOf P t l) (aoc (uc (ancOf P t (succ l))))))
      (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D)) = succ l ∧
    (∀ i ∈ l, embTpSigs Q (iniSegAoc V (⋃₀ dom (sig V)))
      (uc (ctChd P (ancOf P t l) (aoc (uc (ancOf P t (succ l))))))
      (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D) ﹫ i =
        embTpSigs Q (aoc V) (uc t) σ ﹫ i) ∧
    embTpSigs Q (iniSegAoc V (⋃₀ dom (sig V)))
      (uc (ctChd P (ancOf P t l) (aoc (uc (ancOf P t (succ l))))))
      (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D) ﹫ l = tpSig Q (aoc V) D := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  have hdt := hTS.dep_mem_omega ht
  have hls : l ∈ succ (depOf P t) := mem_succ_of_mem hl
  have hl1s : succ l ∈ succ (depOf P t) := succ_mem_succ_of_mem hdt hl
  obtain ⟨htl, -⟩ := hTS.anc_mem_nd ht hls
  change ancOf P t l ∈ ndOf P at htl
  obtain ⟨htl1, hdtl1⟩ := hTS.anc_mem_nd ht hl1s
  change ancOf P t (succ l) ∈ ndOf P at htl1
  change depOf P (ancOf P t (succ l)) = succ l at hdtl1
  have hc : ancOf P t (succ l) ∈ chdOf P (ancOf P t l) := hTS.anc_succ_mem_chd ht hl
  obtain ⟨hcc, -, hcsig, -⟩ := ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hP htl hc
  set c := ctChd P (ancOf P t l) (aoc (uc (ancOf P t (succ l)))) with hcdef
  have hcn := mem_ndOf_of_mem_chdOf hS hcc
  have hUc := uc_mem_stduoci_of_mem_otci_two hP hcn
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hUl1 := uc_mem_stduoci_of_mem_otci_two hP htl1
  have hdc : dom (sig (uc c)) = succ l := by rw [hcsig, dom_sig_uc_eq_depOf hP htl1, hdtl1]
  have hsdc {i : M} (hi : i ∈ succ l) : sigdcn (uc c) i = sigdcn (uc t) i := by
    rw [← sigdcn_anc hP ht hl1s hi, sigdcn, sigdcn, hcsig]
  obtain ⟨-, hsub1⟩ := uc_ancOf_rel hP ht hl1s
  have he := (mem_aotciEmbSet_iff.mp hσ).right
  have hinj := (he.isOtciEmbedding (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  have hfK : IsFunction (lvlOneRes σ (ancOf P t (succ l))) := hinj.isFunction.restrict _
  have hdomK : dom (lvlOneRes σ (ancOf P t (succ l))) =
      ndOf (aoc (uc (ancOf P t (succ l))) ﹫ ((1 : ℕ) : M)) :=
    dom_restrict_of_subset hinj.isFunction (by rw [hinj.dom_eq]; exact hsub1.left)
  have hlt : l ∈ dom (sig (uc t)) := by rw [dom_sig_uc_eq_depOf hP ht]; exact hl
  refine ⟨by rw [dom_embTpSigs, hdc], fun i hi ↦ ?_, ?_⟩
  · have hic : i ∈ dom (sig (uc c)) := by rw [hdc]; exact mem_succ_of_mem hi
    have hit : i ∈ dom (sig (uc t)) := (ordinal_of_mem ordinal_omega
      (dom_sig_mem_omega_of_mem_stduoci_one hUt)).transitive _ hlt hi
    have hil1 : i ∈ dom (sig (uc (ancOf P t (succ l)))) := by
      rw [dom_sig_uc_eq_depOf hP htl1, hdtl1]; exact mem_succ_of_mem hi
    have hun : sigdcn (uc t) i ∈ ndOf (aoc (uc (ancOf P t (succ l))) ﹫ ((1 : ℕ) : M)) := by
      rw [← sigdcn_anc hP ht hl1s (mem_succ_of_mem hi)]
      exact (siglvl_eq_one hUl1 hil1).right
    have hne : sigdcn (uc t) i ≠ sigdcn (uc t) l := fun h' ↦ by
      have h'' := congrArg lbl h'
      rw [lbl_sigdcn hUt hit, lbl_sigdcn hUt hlt] at h''
      rw [h''] at hi
      exact notMem_self _ hi
    rw [embTpSigs_val hUc hic, embTpSigs_val hUt hit, embUpd_val_one hσ, hsdc (mem_succ_of_mem hi),
      val_update_of_ne hfK _ (by rw [hdomK]; exact hun) hne, lvlOneRes,
      val_restrict _ hinj.isFunction hun (by rw [hinj.dom_eq]; exact hsub1.left hun)]
    exact tpSig_lastSeg_eq hQ hV hm (hN i hi)
  · have hlc : l ∈ dom (sig (uc c)) := by rw [hdc]; exact mem_succ_self l
    rw [embTpSigs_val hUc hlc, embUpd_val_one hσ, hsdc (mem_succ_self l), val_update_self hfK]
    exact tpSig_lastSeg_eq hQ hV hm hD

end Rows

/-- The entries of the signature of a node of `Q(2) ⊗ X'` are nodes of `X'` -/
theorem tpSig_entry_lastSeg {Q V D j : M} (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hV : V ∈ stduoci ((1 : ℕ) : M)) (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
    (hD : D ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V))))
    (hj : j ∈ dom (tpSig Q (aoc V) D)) :
    ∃ w ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)),
      tpSig Q (aoc V) D ﹫ j = !(((1 : ℕ) : M), w) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  obtain ⟨hX', -, -, -⟩ := lastSeg_facts hV hm
  have hDN : D ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) :=
    (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX').mpr (.inr hD)
  rw [← tpSig_lastSeg_eq hQ hV hm hDN] at hj ⊢
  obtain ⟨q, hq, -, h, hh, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp hD
  rw [dom_tpSig_eq hD] at hj
  refine ⟨_, (sigImg_spec hQ2 hq hX' hh hj).left, ?_⟩
  rw [tpSig_val_eq hQ hD hj]
  rfl

section Cases

variable {P Q V t σ l k : M} (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
  (hV : V ∈ stduoci ((1 : ℕ) : M)) (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (ht : t ∈ ndOf P)
  (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q (aoc V)))
  (hfo : IsFirstOcc (embTpSigs Q (aoc V) (uc t) σ) (sig V ﹫ ⋃₀ dom (sig V)) l k)
include hP hQ hV hm ht hσ hfo

/-- The images of the nodes of the rows before `l` are nodes of `(Q ⊗ X')(1)` -/
theorem img_mem_lastSeg {i : M} (hi : i ∈ l) :
    (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i ∈
      ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) := by
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hs := isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUt) (aoc V) σ
  have hid : i ∈ dom (sig (uc t)) := by
    rw [← dom_embTpSigs Q (aoc V) (uc t) σ]
    exact (ordinal_of_mem ordinal_omega hs.right.left).transitive _ hfo.left hi
  have he := ((mem_aotciEmbSet_iff.mp hσ).right.isOtciEmbedding (mem_succ_self _)).isEmbedding
  have hz := he.isEmbedding_ts.isInjectionFromTo.isFunctionFromTo.val_mem
    (siglvl_eq_one hUt hid).right
  refine mem_ndOf_lastSeg_of_avoid hQ hV hm hz fun j hj he' ↦ ?_
  have hrow := embTpSigs_val (Q := Q) (X := aoc V) (σ := σ) hUt hid
  refine row_avoid hs hfo hi j (by rw [hrow]; exact hj) ?_
  rw [hrow, he', sig_val_eq_pair hV hm]

/-- Case 1 of the parent: `D` is the image of the `ucf` of `t_l`, and the parent is
`(V | m', (t_l, σ ↾ t_l))` -/
theorem prt_mem_case_one (hU : IsUociEmb Q (uc t) V σ) (hm0 : ⋃₀ dom (sig V) ≠ ∅) {D : M}
    (hD : (D = ∅ ∧ k = ∅) ∨
      (D ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V))) ∧
        (∀ i ∈ k, i ∈ dom (tpSig Q (aoc V) D) ∧ tpSig Q (aoc V) D ﹫ i =
          tpSig Q (aoc V) ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l) ﹫ i) ∧
        tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) D = iniSegUcf V (⋃₀ dom (sig V))))
    (hnone : D = ∅ →
      ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
        ¬ ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l)
          [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z)
    (hcase : D = ucfImg σ (uc (ancOf P t l))) :
    !(iniSeg V (⋃₀ dom (sig V)), !(ancOf P t l, embRestrict (uc (ancOf P t l)) σ)) ∈
      tensorProdTwoTwoNds P Q := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, hnd'⟩ := lastSeg_facts hV hm
  have hB := tensorProdATwoAOne_mem_aotci hQ hX
  have hB' := tensorProdATwoAOne_mem_aotci hQ hX'
  set s := embTpSigs Q (aoc V) (uc t) σ with hsdef
  have hs : IsFinSeqSeq s :=
    isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUt) (aoc V) σ
  have hcon : contraction s = sig V := hU.right.left
  have hdm : dom (sig V) = succ (⋃₀ dom (sig V)) :=
    (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV)
      (fun h' ↦ by rw [h'] at hm; exact notin_empty _ hm)).right.right
  have hn : dom (contraction s) = succ (⋃₀ dom (sig V)) := by rw [hcon]; exact hdm
  have hfo' : IsFirstOcc s (contraction s ﹫ ⋃₀ dom (sig V)) l k := by rw [hcon]; exact hfo
  have hocc := occ_before hs hn hfo'
  have hlsig : l ∈ dom (sig (uc t)) := by rw [← dom_embTpSigs Q (aoc V) (uc t) σ]; exact hfo.left
  have hl : l ∈ depOf P t := by rw [← dom_sig_uc_eq_depOf hP ht]; exact hlsig
  have hls : l ∈ succ (depOf P t) := mem_succ_of_mem hl
  have hlrow : s ﹫ l = tpSig Q (aoc V) ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l) :=
    embTpSigs_val hUt hlsig
  have hmω := dom_sig_mem_omega_of_mem_stduoci_one hV
  have hm'o : Ordinal (⋃₀ dom (sig V)) := ordinal_of_mem ordinal_omega
    (ordinal_omega.transitive _ hmω hm)
  have hDne (h' : D ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V)))) : D ≠ ∅ := by
    obtain ⟨-, -, -, -, -, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp h'
    exact orderedPair_ne_empty _ _
  -- the row `l` is not the first row
  have hl0 : l ≠ ∅ := by
    intro hl0
    subst hl0
    rw [ucfImg_ancOf_empty hP ht] at hcase
    have hk0 : k = ∅ := by
      rcases hD with h' | h'
      · exact h'.right
      · exact (hDne h'.left hcase).elim
    subst hk0
    have h0m : (∅ : M) ∈ ⋃₀ dom (sig V) := empty_mem_of_ordinal_of_ne_empty hm'o hm0
    obtain ⟨hcf, -, hinj, hran, -⟩ := isContraction_contraction hs
    have hx : contraction s ﹫ ∅ ∈ ctrSet s := by
      rw [← hran, hcf.mem_ran_iff]
      exact ⟨∅, by rw [hn]; exact mem_succ_of_mem h0m, rfl⟩
    have hne : contraction s ﹫ ∅ ≠ contraction s ﹫ ⋃₀ dom (sig V) := fun h' ↦ by
      have := hinj _ (by rw [hn]; exact mem_succ_of_mem h0m) _
        (by rw [hn]; exact mem_succ_self _) h'
      rw [← this] at h0m
      exact notin_empty _ h0m
    obtain ⟨i, -, j, -, -, h' | ⟨-, h'⟩⟩ := hocc _ hx hne
    · exact notin_empty _ h'
    · exact notin_empty _ h'
  obtain ⟨hlv, ⟨i0, hi0, hr⟩, hyr⟩ := ucf_anc_rel hP ht hl hl0 hB hσ
  have hi0t : i0 ∈ dom (sig (uc t)) := (ordinal_of_mem ordinal_omega
    (dom_sig_mem_omega_of_mem_stduoci_one hUt)).transitive _ hlsig hi0
  have hlv1 : ucflvl (uc (ancOf P t l)) ≠ ∅ := by
    rw [ucflvl, hlv, lvl_orderedPair]
    exact natCast_one_ne_empty
  have hDr : D = (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i0 := by
    rw [hcase, ucfImg, if_neg hlv1, hr]
  have hDN : D ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) := by
    rw [hDr]
    exact img_mem_lastSeg hP hQ hV hm ht hσ hfo hi0
  obtain ⟨-, hDsig, hDucf⟩ : D ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V))) ∧
      (∀ i ∈ k, i ∈ dom (tpSig Q (aoc V) D) ∧ tpSig Q (aoc V) D ﹫ i =
        tpSig Q (aoc V) ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l) ﹫ i) ∧
      tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) D = iniSegUcf V (⋃₀ dom (sig V)) := by
    rcases hD with h' | h'
    · refine (hnone h'.left D hDN ?_).elim
      rw [hDr, ← hr]
      exact hyr
    · exact h'
  have hrowi0 : s ﹫ i0 = tpSig Q (aoc V) D := by rw [hDr]; exact embTpSigs_val hUt hi0t
  -- every old entry occurs before the row `l`
  have hocc1 : ∀ x ∈ ctrSet s, x ≠ contraction s ﹫ ⋃₀ dom (sig V) →
      ∃ i ∈ dom s, ∃ j ∈ dom (s ﹫ i), (s ﹫ i) ﹫ j = x ∧ (i ∈ l ∨ (i = l ∧ j ∈ (∅ : M))) := by
    intro x hx hne
    obtain ⟨i, hi, j, hj, hv, h' | ⟨rfl, hjk⟩⟩ := hocc x hx hne
    · exact ⟨i, hi, j, hj, hv, .inl h'⟩
    · obtain ⟨hjD, hjv⟩ := hDsig j hjk
      refine ⟨i0, by rw [dom_embTpSigs]; exact hi0t, j, by rw [hrowi0]; exact hjD, ?_, .inl hi0⟩
      rw [hrowi0, hjv, ← hlrow, hv]
  have hN : ∀ i ∈ l, (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i ∈
      ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) :=
    fun i hi ↦ img_mem_lastSeg hP hQ hV hm ht hσ hfo hi
  obtain ⟨hdom', hrows⟩ := embTpSigs_embRestrict hP hQ hV hm ht hσ hls hN
  obtain ⟨htl, hdtl⟩ := hTS.anc_mem_nd ht hls
  change ancOf P t l ∈ ndOf P at htl
  change depOf P (ancOf P t l) = l at hdtl
  have hUl := uc_mem_stduoci_of_mem_otci_two hP htl
  have hA := aoc_mem_aotci_of_mem_stduoci_one hUl
  have hdl : dom (sig (uc (ancOf P t l))) = l := by rw [dom_sig_uc_eq_depOf hP htl, hdtl]
  have h0B : tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ∅ =
      tensorProdATwoAOne Q (aoc V) ﹫ ∅ := (tensorProdATwoAOne_val_zero_eq hQ hX hX' h0).symm
  have hsubB := isSubOne_tensorProdATwoAOne hQ hX hX' h0 hsub
  have hhf := ((mem_aotciEmbSet_iff.mp hσ).right.isOtciEmbedding
    (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  obtain ⟨-, hsubl⟩ := uc_ancOf_rel hP ht hls
  have hσ'' : embRestrict (uc (ancOf P t l)) σ ∈ aotciEmbSet ((1 : ℕ) : M)
      (aoc (uc (ancOf P t l))) (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V)))) := by
    refine (mem_aotciEmbSet_iff_of_isSubOne hA hB hB' h0B hsubB).mpr
      ⟨embRestrict_mem_aotciEmbSet hP ht hls hB hσ, fun z hz ↦ ?_⟩
    rw [embRestrict_val _ _ natCast_one_mem_two, (hhf.isFunction.restrict _).mem_ran_iff] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [dom_restrict_of_subset hhf.isFunction (by rw [hhf.dom_eq]; exact hsubl.left)] at ha
    have ha' := ha
    rw [ndOf_aoc_val_one_eq hUl, mem_iniSegNds_iff, hdl] at ha'
    obtain ⟨i, hi, rfl⟩ := ha'
    rw [val_restrict _ hhf.isFunction ha (by rw [hhf.dom_eq]; exact hsubl.left ha),
      sigdcn_anc hP ht hls hi]
    exact hN i hi
  have hs' := isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUl)
    (iniSegAoc V (⋃₀ dom (sig V))) (embRestrict (uc (ancOf P t l)) σ)
  have hlo : Ordinal l := ordinal_of_mem_dom hs hfo.left
  set s' := embTpSigs Q (iniSegAoc V (⋃₀ dom (sig V))) (uc (ancOf P t l))
    (embRestrict (uc (ancOf P t l)) σ) with hs'def
  have hcontr : contraction s' = sig V ↾ ⋃₀ dom (sig V) := by
    have hc' := contraction_eq_restrict_of_cut hs hs' hlo ordinal_empty hn ?_ ?_ ?_ hocc1
    · rw [hc', hcon]
    · intro i _ j hj hlt
      have hil : i ∈ l := hlt.elim (fun h' ↦ h') fun h' ↦ (notin_empty _ h'.right).elim
      exact ⟨by rw [hdom']; exact hil, by rw [hrows i hil]; exact hj, by rw [hrows i hil]⟩
    · intro i _ j hj hlt
      have hil : i ∈ l := hlt.elim (fun h' ↦ h') fun h' ↦ (notin_empty _ h'.right).elim
      exact ⟨(ordinal_of_mem ordinal_omega hs.right.left).transitive _ hfo.left hil,
        by rw [← hrows i hil]; exact hj, by rw [hrows i hil]⟩
    · intro i hi j hj
      rw [hdom'] at hi
      rw [hrows i hi] at hj ⊢
      refine ⟨(mem_ctrSet_iff hs).mpr ⟨i, (ordinal_of_mem ordinal_omega hs.right.left).transitive
        _ hfo.left hi, j, hj, rfl⟩, ?_⟩
      rw [hcon]
      exact row_avoid hs hfo hi j hj
  have hc : ancOf P t (succ l) ∈ chdOf P (ancOf P t l) := hTS.anc_succ_mem_chd ht hl
  have hnct : ctp (uc (ancOf P t l)) ≠ ct := fun hct ↦ by
    have h' := chdOf_eq_empty_of_ctp_eq_ct (natCast_mem_omega 2) hP htl hct
    rw [h'] at hc
    exact notin_empty _ hc
  have h3 : ((3 : ℕ) : M) ∈ dom (uc (ancOf P t l)) := by
    by_contra h3
    have h' : ucflvldcn (uc (ancOf P t l)) = ∅ := val_eq_empty_of_not_mem_dom h3
    rw [hlv] at h'
    exact orderedPair_ne_empty _ _ h'
  have hrq : ucfdcn (uc (ancOf P t l)) ∈ ndOf (aoc (uc (ancOf P t l)) ﹫ ((1 : ℕ) : M)) := by
    rw [hr, ← sigdcn_anc hP ht hls hi0]
    exact (siglvl_eq_one hUl (by rw [hdl]; exact hi0)).right
  rw [mem_tensorProdTwoTwoNds_iff]
  refine ⟨_, htl, _, iniSeg_mem_stduoci hV hm, _, by rw [aoc_iniSeg]; exact hσ'',
    ⟨⟨by rw [aoc_iniSeg]; exact hσ'', by rw [aoc_iniSeg, sig_iniSeg]; exact hcontr, ?_,
      fun _ ↦ ?_⟩, fun h' ↦ ?_⟩, rfl⟩
  · rw [ctp_iniSeg]
    exact iff_of_false (fun h' ↦ ct_ne_dct h'.symm) fun h' ↦ hnct h'.left
  · obtain ⟨hu1, hu2⟩ := ucflvldcn_iniSeg (U := V) hm0
    refine ⟨?_, hu2⟩
    rw [hu1, ← hDucf, aoc_iniSeg, embUcf, ucfOrLast, if_pos h3, hlv, embUcfAux, lvl_orderedPair,
      if_neg natCast_one_ne_empty, dcn_orderedPair, embRestrict_val _ _ natCast_one_mem_two,
      val_restrict _ hhf.isFunction hrq (by rw [hhf.dom_eq]; exact hsubl.left hrq), hr, ← hDr]
  · have hd := dom_sig_iniSeg hV hm
    rw [h', dom_empty] at hd
    exact (hm0 hd.symm).elim

/-- Case 2 of the parent: `D` is not the image of the `ucf` of `t_l`, and the parent is
`(V | m', (t_l⁺, σ'))` with `σ'` sending `w_l` to `D` -/
theorem prt_mem_case_two (hU : IsUociEmb Q (uc t) V σ) (hm0 : ⋃₀ dom (sig V) ≠ ∅) {D : M}
    (hDC : D ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V))))
    (hlt : ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l)
      [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] D)
    (hmin : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
      ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l)
        [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
          z = D ∨ D [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z)
    (hDsig : ∀ i ∈ k, i ∈ dom (tpSig Q (aoc V) D) ∧ tpSig Q (aoc V) D ﹫ i =
      tpSig Q (aoc V) ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l) ﹫ i)
    (hDdom : dom (tpSig Q (aoc V) D) ⊆ succ k)
    (hDct : TpCt Q (iniSegAoc V (⋃₀ dom (sig V))) D → k ∈ dom (tpSig Q (aoc V) D))
    (hDucf : tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) D = iniSegUcf V (⋃₀ dom (sig V)))
    (hcase : D ≠ ucfImg σ (uc (ancOf P t l))) :
    !(iniSeg V (⋃₀ dom (sig V)), !(ctChd P (ancOf P t l) (aoc (uc (ancOf P t (succ l)))),
      embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D)) ∈ tensorProdTwoTwoNds P Q := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, hnd'⟩ := lastSeg_facts hV hm
  have hB := tensorProdATwoAOne_mem_aotci hQ hX
  have hB' := tensorProdATwoAOne_mem_aotci hQ hX'
  set s := embTpSigs Q (aoc V) (uc t) σ with hsdef
  have hs : IsFinSeqSeq s :=
    isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUt) (aoc V) σ
  have hcon : contraction s = sig V := hU.right.left
  have hdm : dom (sig V) = succ (⋃₀ dom (sig V)) :=
    (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV)
      (fun h' ↦ by rw [h'] at hm; exact notin_empty _ hm)).right.right
  have hn : dom (contraction s) = succ (⋃₀ dom (sig V)) := by rw [hcon]; exact hdm
  have hfo' : IsFirstOcc s (contraction s ﹫ ⋃₀ dom (sig V)) l k := by rw [hcon]; exact hfo
  have hocc := occ_before hs hn hfo'
  have hlsig : l ∈ dom (sig (uc t)) := by rw [← dom_embTpSigs Q (aoc V) (uc t) σ]; exact hfo.left
  have hl : l ∈ depOf P t := by rw [← dom_sig_uc_eq_depOf hP ht]; exact hlsig
  have hls : l ∈ succ (depOf P t) := mem_succ_of_mem hl
  have hdt := hTS.dep_mem_omega ht
  have hl1s : succ l ∈ succ (depOf P t) := succ_mem_succ_of_mem hdt hl
  have hlrow : s ﹫ l = tpSig Q (aoc V) ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l) :=
    embTpSigs_val hUt hlsig
  have hN : ∀ i ∈ l, (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i ∈
      ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) :=
    fun i hi ↦ img_mem_lastSeg hP hQ hV hm ht hσ hfo hi
  have hDN : D ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) :=
    (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX').mpr (.inr hDC)
  obtain ⟨hdom', hrows, hrowl⟩ := embTpSigs_embUpd hP hQ hV hm ht hσ hl hN hDN
  obtain ⟨htl, -⟩ := hTS.anc_mem_nd ht hls
  change ancOf P t l ∈ ndOf P at htl
  obtain ⟨htl1, hdtl1⟩ := hTS.anc_mem_nd ht hl1s
  change ancOf P t (succ l) ∈ ndOf P at htl1
  change depOf P (ancOf P t (succ l)) = succ l at hdtl1
  have hc : ancOf P t (succ l) ∈ chdOf P (ancOf P t l) := hTS.anc_succ_mem_chd ht hl
  obtain ⟨hcc, -, hcsig, hcct, -⟩ :=
    ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hP htl hc
  set c := ctChd P (ancOf P t l) (aoc (uc (ancOf P t (succ l)))) with hcdef
  have hcn := mem_ndOf_of_mem_chdOf hS hcc
  have hUc := uc_mem_stduoci_of_mem_otci_two hP hcn
  have hdc : dom (sig (uc c)) = succ l := by rw [hcsig, dom_sig_uc_eq_depOf hP htl1, hdtl1]
  have h0B : tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ∅ =
      tensorProdATwoAOne Q (aoc V) ﹫ ∅ := (tensorProdATwoAOne_val_zero_eq hQ hX hX' h0).symm
  have hsubB := isSubOne_tensorProdATwoAOne hQ hX hX' h0 hsub
  have hne : l ≠ ∅ → D ≠ (σ ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf P t l)) := fun hl0 h' ↦ by
    obtain ⟨hlv, -, -⟩ := ucf_anc_rel hP ht hl hl0 hB hσ
    have hlv1 : ucflvl (uc (ancOf P t l)) ≠ ∅ := by
      rw [ucflvl, hlv, lvl_orderedPair]
      exact natCast_one_ne_empty
    exact hcase (by rw [ucfImg, if_neg hlv1, h'])
  have hσ'' := embUpd_mem_aotciEmbSet hP ht hl hB hB' h0B hsubB hσ hDN hN hlt hmin hne
  set s' := embTpSigs Q (iniSegAoc V (⋃₀ dom (sig V))) (uc c)
    (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D) with hs'def
  have hs' : IsFinSeqSeq s' := isFinSeqSeq_embTpSigs hQ
    (dom_sig_mem_omega_of_mem_stduoci_one hUc) _ _
  have hlo : Ordinal l := ordinal_of_mem_dom hs hfo.left
  have hko : Ordinal k := ordinal_of_mem_dom_val hs hfo.left hfo.right.left
  have hldom : l ∈ dom s := hfo.left
  have hdoms : ∀ i ∈ l, i ∈ dom s := fun i hi ↦
    (ordinal_of_mem ordinal_omega hs.right.left).transitive _ hldom hi
  -- the entries of `s'`
  have hent : ∀ i ∈ dom s', ∀ j ∈ dom (s' ﹫ i),
      (s' ﹫ i) ﹫ j ∈ ctrSet s ∧ (s' ﹫ i) ﹫ j ≠ contraction s ﹫ ⋃₀ dom (sig V) := by
    intro i hi j hj
    rw [hdom'] at hi
    rcases mem_or_eq_of_mem_succ hi with hi | rfl
    · rw [hrows i hi] at hj ⊢
      refine ⟨(mem_ctrSet_iff hs).mpr ⟨i, hdoms i hi, j, hj, rfl⟩, ?_⟩
      rw [hcon]
      exact row_avoid hs hfo hi j hj
    · rw [hrowl] at hj ⊢
      obtain ⟨w, hw, hwe⟩ := tpSig_entry_lastSeg hQ hV hm hDC hj
      obtain ⟨hwX, hwne⟩ := (hnd' w).mp hw
      obtain ⟨hcf, -, -, hran, -⟩ := isContraction_contraction hs
      rw [hwe]
      refine ⟨?_, ?_⟩
      · rw [← hran, hcon, (uociCond_of_mem_stduoci_one hV).right.right.right.left.left.mem_ran_iff]
        exact ⟨_, (sig_val_lbl_of_mem hV hwX).left, (sig_val_lbl_of_mem hV hwX).right⟩
      · rw [hcon, sig_val_eq_pair hV hm]
        intro h'
        rw [orderedPair_eq_orderedPair_iff] at h'
        exact hwne h'.right
  have hagree : ∀ i ∈ dom s, ∀ j ∈ dom (s ﹫ i), (i ∈ l ∨ (i = l ∧ j ∈ k)) →
      i ∈ dom s' ∧ j ∈ dom (s' ﹫ i) ∧ (s' ﹫ i) ﹫ j = (s ﹫ i) ﹫ j := by
    rintro i - j hj (hi | ⟨rfl, hjk⟩)
    · exact ⟨by rw [hdom']; exact mem_succ_of_mem hi, by rw [hrows i hi]; exact hj,
        by rw [hrows i hi]⟩
    · obtain ⟨hjD, hjv⟩ := hDsig j hjk
      exact ⟨by rw [hdom']; exact mem_succ_self _, by rw [hrowl]; exact hjD,
        by rw [hrowl, hjv, hlrow]⟩
  have hcontr : contraction s' = sig V ↾ ⋃₀ dom (sig V) := by
    have hc' := contraction_eq_restrict_of_cut hs hs' hlo hko hn hagree ?_ hent hocc
    · rw [hc', hcon]
    · rintro i - j hj (hi | ⟨rfl, hjk⟩)
      · exact ⟨hdoms i hi, by rw [← hrows i hi]; exact hj, by rw [hrows i hi]⟩
      · obtain ⟨-, hjv⟩ := hDsig j hjk
        refine ⟨hldom, (ordinal_of_mem ordinal_omega (hs.right.right _ hldom).right).transitive _
          hfo.right.left hjk, by rw [hrowl, hjv, hlrow]⟩
  have hinj := ((mem_aotciEmbSet_iff.mp hσ).right.isOtciEmbedding
    (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  have hfK : IsFunction (lvlOneRes σ (ancOf P t (succ l))) := hinj.isFunction.restrict _
  have hlc : l ∈ dom (sig (uc c)) := by rw [hdc]; exact mem_succ_self l
  have hlast : ⋃₀ dom (sig (uc c)) = l := by rw [hdc, sUnion_succ hlo.transitive]
  have hsdcl : sigdcn (uc c) l = sigdcn (uc t) l := by
    rw [← sigdcn_anc hP ht hl1s (mem_succ_self l), sigdcn, sigdcn, hcsig]
  have himgD : (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D ﹫ ((1 : ℕ) : M)) ﹫
      sigdcn (uc c) l = D := by
    rw [embUpd_val_one hσ, hsdcl, val_update_self hfK]
  have hls'd : l ∈ dom s' := by rw [hdom']; exact mem_succ_self l
  have hDo : Ordinal (dom (tpSig Q (aoc V) D)) := by
    rw [← hrowl]
    exact ordinal_of_mem ordinal_omega (hs'.right.right l hls'd).right
  -- the parent is discontinuous: the last entry of `s'` is old
  have hct : ¬(ctp (uc c) = ct ∧ TpCt Q (iniSegAoc V (⋃₀ dom (sig V)))
      ((embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D ﹫ siglvl (uc c) (⋃₀ dom (sig (uc c))))
        ﹫ sigdcn (uc c) (⋃₀ dom (sig (uc c)))) ∧ EndsWithNew s') := by
    rintro ⟨-, hTp, hEnd⟩
    rw [hlast, (siglvl_eq_one hUc hlc).left, himgD] at hTp
    have hk' := hDct hTp
    have hDdom' : dom (tpSig Q (aoc V) D) = succ k := by
      ext z
      constructor
      · exact fun hz ↦ hDdom hz
      · intro hz
        rcases mem_or_eq_of_mem_succ hz with h' | rfl
        · exact hDo.transitive _ hk' h'
        · exact hk'
    obtain ⟨-, -, hEnd⟩ := hEnd
    have hli : lastIdx s' = l := by
      change ⋃₀ dom s' = l
      rw [hdom', sUnion_succ hlo.transitive]
    have hlq : lastSeq s' = tpSig Q (aoc V) D := by
      change s' ﹫ lastIdx s' = _
      rw [hli, hrowl]
    have hlk : lastIdx (lastSeq s') = k := by
      rw [hlq]
      change ⋃₀ dom (tpSig Q (aoc V) D) = k
      rw [hDdom', sUnion_succ hko.transitive]
    have hle : lastEntry s' = tpSig Q (aoc V) D ﹫ k := by
      change lastSeq s' ﹫ lastIdx (lastSeq s') = _
      rw [hlk, hlq]
    obtain ⟨hx1, hx2⟩ := hent l hls'd k (by rw [hrowl]; exact hk')
    rw [hrowl] at hx1 hx2
    obtain ⟨i, hi, j, hj, hv, hpos⟩ := hocc _ hx1 hx2
    obtain ⟨hi', hj', hv'⟩ := hagree i hi j hj hpos
    have h' := hEnd i hi' j hj' (by rw [hv', hv, hle])
    rw [hli, hlk] at h'
    rcases hpos with h'' | ⟨-, h''⟩
    · rw [h'.left] at h''
      exact notMem_self _ h''
    · rw [h'.right] at h''
      exact notMem_self _ h''
  have h3c : ((3 : ℕ) : M) ∉ dom (uc c) := by
    rw [dom_eq_three_of_ctp_eq_ct (natCast_mem_omega 1) (mem_stduoci_iff.mp hUc).left hcct]
    exact notMem_self _
  rw [mem_tensorProdTwoTwoNds_iff]
  refine ⟨c, hcn, _, iniSeg_mem_stduoci hV hm, _, by rw [aoc_iniSeg]; exact hσ'',
    ⟨⟨by rw [aoc_iniSeg]; exact hσ'', by rw [aoc_iniSeg, sig_iniSeg]; exact hcontr, ?_,
      fun _ ↦ ?_⟩, fun h' ↦ ?_⟩, rfl⟩
  · rw [ctp_iniSeg, aoc_iniSeg]
    exact iff_of_false (fun h' ↦ ct_ne_dct h'.symm) hct
  · obtain ⟨hu1, hu2⟩ := ucflvldcn_iniSeg (U := V) hm0
    refine ⟨?_, hu2⟩
    rw [hu1, ← hDucf, aoc_iniSeg, embUcf, ucfOrLast, if_neg h3c, hlast, sig_val_eq_pair hUc hlc,
      embUcfAux, lvl_orderedPair, if_neg natCast_one_ne_empty, dcn_orderedPair, himgD]
  · have hd := dom_sig_iniSeg hV hm
    rw [h', dom_empty] at hd
    exact (hm0 hd.symm).elim

end Cases

end TLevel

end PrtPieces

end Slot

end TensorProd

end FirstOrder.Language.MemStructure
