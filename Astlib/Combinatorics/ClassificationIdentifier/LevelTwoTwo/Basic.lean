/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwo
/-!
# Initial segments, signatures and contractions

Preliminaries for the tensor product `T ⊗ Q` of two arrays in `aotci_2`: the initial segments
`iniSeg U k` of an element of `stduoci_1`, the signatures `tpSig Q X x` of the nodes of
`(Q ⊗ X)(1)`, the contraction of a finite sequence of finite sequences, the embeddings
`IsUociEmb Q U V σ` of an element of `stduoci_1` into a pair `(Q, V)`, and their definability.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M]

section General

/-! ### Auxiliary results -/

variable {R a b B X : M}

/-- A nonempty finite subset of a strict linear order has a least element -/
theorem IsStrictLinearOrder.exists_least_of_finite (h : IsStrictLinearOrder R a)
    (hb : MemStructure.Finite b) (hba : b ⊆ a) (hne : b ≠ ∅) :
    ∃ x ∈ b, ∀ y ∈ b, y ≠ x → x [R] y := by
  refine Finite.induction (A := fun b ↦ b ⊆ a → b ≠ ∅ → ∃ x ∈ b, ∀ y ∈ b, y ≠ x → x [R] y)
    (fun _ h ↦ (h rfl).elim) (fun x c ih hxa _ ↦ ?_) hb hba hne
  have hc : c ∈ a := hxa (by simp)
  have hx : x ⊆ a := fun y hy ↦ hxa (by simp [hy])
  by_cases hx0 : x = ∅
  · subst hx0
    refine ⟨c, (by simp), fun y hy hyc ↦ ?_⟩
    rw [mem_insert_iff] at hy
    rcases hy with h' | h'
    · exact (hyc h').elim
    · simp at h'
  obtain ⟨m, hm, hmin⟩ := ih hx hx0
  by_cases hcm : c [R] m
  · refine ⟨c, (by simp), fun y hy hyc ↦ ?_⟩
    rw [mem_insert_iff] at hy
    rcases hy with h' | h'
    · exact (hyc h').elim
    · by_cases hym : y = m
      · rw [hym]
        exact hcm
      · exact h.trans hcm (hmin y h' hym)
  · refine ⟨m, (by simp [hm]), fun y hy hym ↦ ?_⟩
    rw [mem_insert_iff] at hy
    rcases hy with h' | h'
    · subst h'
      rcases h.trichotomous (hx hm) hc with h1 | h1 | h1
      · exact h1
      · exact (hym h1.symm).elim
      · exact (hcm h1).elim
    · exact hmin y h' hym

/-- An array on `2` with an `aotci_0` part from `aotci_1` and a level-`1` tree in `otci_1` -/
theorem cc_restrict_mem_aotci_one (hB : B ∈ aotci ((1 : ℕ) : M)) (hX : X ∈ otci ((1 : ℕ) : M)) :
    cc (B ↾ ((1 : ℕ) : M)) X ∈ aotci ((1 : ℕ) : M) := by
  obtain ⟨hBf, hBdom, -⟩ := mem_aotci_iff.mp hB
  have hBr : IsFunction (B ↾ ((1 : ℕ) : M)) := hBf.restrict _
  have hBrdom : dom (B ↾ ((1 : ℕ) : M)) = ((1 : ℕ) : M) :=
    dom_restrict_of_subset hBf fun x hx ↦ by
      rw [hBdom]
      exact mem_succ_of_mem hx
  rw [mem_aotci_iff]
  refine ⟨hBr.cc _, by rw [dom_cc, hBrdom], fun i hi ↦ ?_, ?_⟩
  · rw [otciL_ciRec_restrict hi, cc_val_of_mem hBr _ (by rw [hBrdom]; exact hi),
      val_restrict _ hBf hi (by rw [hBdom]; exact mem_succ_of_mem hi)]
    exact val_mem_otci_of_mem_aotci hB (mem_succ_of_mem hi)
  · have h := cc_val_self hBr X
    rw [hBrdom] at h
    rw [h]
    exact hX

theorem cc_restrict_val_zero (hB : B ∈ aotci ((1 : ℕ) : M)) (X : M) :
    cc (B ↾ ((1 : ℕ) : M)) X ﹫ ∅ = B ﹫ ∅ := by
  obtain ⟨hBf, hBdom, -⟩ := mem_aotci_iff.mp hB
  have hBrdom : dom (B ↾ ((1 : ℕ) : M)) = ((1 : ℕ) : M) :=
    dom_restrict_of_subset hBf fun x hx ↦ by
      rw [hBdom]
      exact mem_succ_of_mem hx
  rw [cc_val_of_mem (hBf.restrict _) _ (by rw [hBrdom]; exact empty_mem_natCast_one),
    val_restrict _ hBf empty_mem_natCast_one
      (by rw [hBdom]; exact mem_succ_of_mem empty_mem_natCast_one)]

theorem cc_restrict_val_one (hB : B ∈ aotci ((1 : ℕ) : M)) (X : M) :
    cc (B ↾ ((1 : ℕ) : M)) X ﹫ ((1 : ℕ) : M) = X := by
  obtain ⟨hBf, hBdom, -⟩ := mem_aotci_iff.mp hB
  have hBrdom : dom (B ↾ ((1 : ℕ) : M)) = ((1 : ℕ) : M) :=
    dom_restrict_of_subset hBf fun x hx ↦ by
      rw [hBdom]
      exact mem_succ_of_mem hx
  have h := cc_val_self (hBf.restrict ((1 : ℕ) : M)) X
  rwa [hBrdom] at h

/-- The trees in `otci_0` have a single node, a root with identifier `otci0Uc` -/
theorem exists_ndOf_eq_of_mem_otci_empty (hT : X ∈ otci (∅ : M)) :
    ∃ l, ndOf X = {!(otci0Uc, l)} ∧ rtOf X = {!(otci0Uc, l)} := by
  rw [mem_otci_empty_iff] at hT
  obtain ⟨l, -, rfl⟩ := hT
  exact ⟨l, ndOf_irmrtOf_emptySLOT _, rtOf_irmrtOf_emptySLOT _⟩

end General

section Trivial

/-! ### Embeddings of the trivial array and trivial `uoci`'s -/

variable {f n P Q T V W : M}

/-- An embedding of arrays of trees is in the set of embeddings -/
theorem mem_aotciEmbSet_of_isAotciEmbedding (hW : IsFunction W) (hWdom : dom W = succ n)
    (hT : IsFunction T) (hTdom : dom T = succ n) (h : IsAotciEmbedding n W T f) :
    f ∈ aotciEmbSet n W T := by
  rw [mem_aotciEmbSet_iff, mem_powerset_sprod_powerset_iff]
  refine ⟨fun y hy ↦ ?_, h⟩
  obtain ⟨i, rfl⟩ := h.isFunction.exists_val hy
  have hi : i ∈ dom f := by
    rw [mem_dom_iff]
    exact ⟨_, hy⟩
  rw [h.dom_eq] at hi
  rw [left_orderedPair, right_orderedPair]
  refine ⟨⟨_, _, rfl⟩, hi, ?_⟩
  have hE := (h.isOtciEmbedding hi).isEmbedding.isEmbedding_ts.isInjectionFromTo
  intro z hz
  have hz := hE.isFunctionFromTo.subset_sprod hz
  rw [mem_sprod_iff] at hz ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  refine ⟨a, ?_, b, ?_, rfl⟩
  · rw [mem_ndUnion_iff]
    exact ⟨W ﹫ i, by rw [hW.mem_ran_iff]; exact ⟨i, hWdom ▸ hi, rfl⟩, ha⟩
  · rw [mem_ndUnion_iff]
    exact ⟨T ﹫ i, by rw [hT.mem_ran_iff]; exact ⟨i, hTdom ▸ hi, rfl⟩, hb⟩

/-- The empty function is an embedding of an empty tree -/
theorem isOtciEmbedding_empty_of_ndOf_eq_empty (hP : ndOf P = ∅) : IsOtciEmbedding P Q ∅ := by
  rw [isOtciEmbedding_iff, hP]
  refine ⟨isInjectionFromTo_empty _, ?_⟩
  simp

/-- The level-`1` tree of the trivial array of `aotci_1` is empty -/
theorem ndOf_trvAotci_one_val_one : ndOf (trvAotci ((1 : ℕ) : M) ﹫ ((1 : ℕ) : M)) = ∅ := by
  rw [trvAotci_val (natCast_mem_omega 1) (mem_succ_self _)]
  exact (mem_trvotci_iff.mp (trvOtci_mem_trvotci (natCast_mem_omega 1))).right.right isOdd_one

/-- The trivial array of `aotci_1` embeds into every array of `aotci_1` -/
theorem exists_mem_aotciEmbSet_trvAotci_one (hT : T ∈ aotci ((1 : ℕ) : M)) :
    ∃ σ, σ ∈ aotciEmbSet ((1 : ℕ) : M) (trvAotci ((1 : ℕ) : M)) T := by
  have hA := (mem_trvaotci_iff.mp (trvAotci_mem_trvaotci (M := M) (natCast_mem_omega 1))).left
  obtain ⟨hAf, hAdom, -⟩ := mem_aotci_iff.mp hA
  obtain ⟨hTf, hTdom, -⟩ := mem_aotci_iff.mp hT
  have h0 : (∅ : M) ∈ succ ((1 : ℕ) : M) := mem_succ_of_mem empty_mem_natCast_one
  let σ₀ : M := cc ∅ (otciSngIso (trvAotci ((1 : ℕ) : M) ﹫ ∅) (T ﹫ ∅))
  have hσ₀ : IsFunction σ₀ := isFunction_empty.cc _
  have hσ₀dom : dom σ₀ = ((1 : ℕ) : M) := by
    rw [dom_cc, dom_empty, natCast_succ, natCast_zero]
  refine ⟨cc σ₀ ∅, mem_aotciEmbSet_of_isAotciEmbedding hAf hAdom hTf hTdom
    ⟨hσ₀.cc _, by rw [dom_cc, hσ₀dom], fun {i} hi ↦ ?_⟩⟩
  rcases mem_or_eq_of_mem_succ hi with hi' | rfl
  · have hi0 : i = ∅ := by
      rw [natCast_succ, natCast_zero, mem_succ_iff] at hi'
      rcases hi' with h' | h'
      · exact h'
      · simp at h'
    subst hi0
    have hv : cc σ₀ ∅ ﹫ ∅ = otciSngIso (trvAotci ((1 : ℕ) : M) ﹫ ∅) (T ﹫ ∅) := by
      rw [cc_val_of_mem hσ₀ _ (by rw [hσ₀dom]; exact empty_mem_natCast_one)]
      have h := cc_val_self (isFunction_empty (M := M))
        (otciSngIso (trvAotci ((1 : ℕ) : M) ﹫ ∅) (T ﹫ ∅))
      rwa [dom_empty] at h
    rw [hv]
    exact (isOtciIsomorphism_otciSngIso_of_mem_otci_empty (val_mem_otci_of_mem_aotci hA h0)
      (val_mem_otci_of_mem_aotci hT h0)).isOtciEmbedding
  · have hv : cc σ₀ ∅ ﹫ ((1 : ℕ) : M) = ∅ := by
      have h := cc_val_self hσ₀ ∅
      rwa [hσ₀dom] at h
    rw [hv]
    exact isOtciEmbedding_empty_of_ndOf_eq_empty ndOf_trvAotci_one_val_one

end Trivial

/-- The function `{(0, a), (1, b), (2, c), (3, d), (4, e)}` -/
noncomputable def ciQuint (a b c d e : M) : M := cc (cc (ciTriple a b c) d) e

section CiQuint

variable (a b c d e : M)

private theorem isFunction_ciQuint₀ : IsFunction (cc (ciTriple a b c) d) :=
  (isFunction_ciTriple _ _ _).cc _

private theorem dom_ciQuint₀ : dom (cc (ciTriple a b c) d) = ((4 : ℕ) : M) := by
  rw [dom_cc, dom_ciTriple]
  rfl

private theorem val_ciQuint {k : ℕ} (hk : k < 3) :
    ciQuint a b c d e ﹫ (k : M) = ciTriple a b c ﹫ (k : M) := by
  rw [ciQuint, cc_val_of_mem (isFunction_ciQuint₀ a b c d) _
      (by rw [dom_ciQuint₀]; exact natCast_mem_natCast_of_lt (by omega)),
    cc_val_of_mem (isFunction_ciTriple _ _ _) _
      (by rw [dom_ciTriple]; exact natCast_mem_natCast_of_lt hk)]

theorem isFunction_ciQuint : IsFunction (ciQuint a b c d e) := (isFunction_ciQuint₀ a b c d).cc _

theorem dom_ciQuint : dom (ciQuint a b c d e) = ((5 : ℕ) : M) := by
  rw [ciQuint, dom_cc, dom_ciQuint₀]
  rfl

theorem aoc_ciQuint : aoc (ciQuint a b c d e) = a :=
  (val_ciQuint a b c d e (k := 0) (by omega)).trans (aoc_ciTriple a b c)

theorem sig_ciQuint : sig (ciQuint a b c d e) = b :=
  (val_ciQuint a b c d e (k := 1) (by omega)).trans (sig_ciTriple a b c)

theorem ctp_ciQuint : ctp (ciQuint a b c d e) = c :=
  (val_ciQuint a b c d e (k := 2) (by omega)).trans (ctp_ciTriple a b c)

theorem ucflvldcn_ciQuint : ucflvldcn (ciQuint a b c d e) = d := by
  have h : ((3 : ℕ) : M) = dom (ciTriple a b c) := (dom_ciTriple _ _ _).symm
  rw [ucflvldcn, ciQuint, cc_val_of_mem (isFunction_ciQuint₀ a b c d) _
      (by rw [dom_ciQuint₀]; exact natCast_mem_natCast_of_lt (by omega)), h,
    cc_val_self (isFunction_ciTriple _ _ _)]

theorem ucfdr_ciQuint : ucfdr (ciQuint a b c d e) = e := by
  have h : ((4 : ℕ) : M) = dom (cc (ciTriple a b c) d) := (dom_ciQuint₀ a b c d).symm
  rw [ucfdr, ciQuint, h, cc_val_self (isFunction_ciQuint₀ a b c d)]

end CiQuint

section IniSeg

/-! ### Initial segments of an element of `stduoci_1` -/

/-- The nodes `U_sigdcn(i)`, `i < k`, of the first `k` entries of the signature of `U` -/
noncomputable def iniSegNds (U k : M) : M := ran ((fun i ↦ sigdcn U i) ↾₀ k)

/-- The order of the level-`1` nodes of `U ∈ stduoci_1`: the roots of `U_aoc(1)`, a single linearly
ordered set with key `Z` -/
noncomputable def iniSegOdr (U : M) : M := losOdr (rtlosOf (aoc U ﹫ ((1 : ℕ) : M)) ﹫ trvAZero)

/-- The array of the initial segment `U | k`: the tree `U_aoc(0)` and the level-`1` tree of `U` cut
down to the nodes of the first `k` entries of the signature -/
noncomputable def iniSegAoc (U k : M) : M :=
  cc (aoc U ↾ ((1 : ℕ) : M)) (rtLosSLOT trvAZero !(iniSegNds U k, iniSegOdr U ↾↾ iniSegNds U k))

/-- The nodes of the first `k` entries to the right of the `k`-th node of the signature of `U` -/
noncomputable def iniSegRight (U k : M) : M :=
  iniSegNds U k ∩₀ fun r ↦ (sigdcn U k) [iniSegOdr U] r

/-- The level-`0` `ucflvldcn` `(0, r)` of the array `X`, for the node `r` of `X(0)` -/
noncomputable def tpUcfZero (X : M) : M := !(∅, ⋃₀ ndOf (X ﹫ ∅))

/-- The `ucflvldcn` of `U | k`: `(1, r)` for the nearest node `r` of the first `k` entries to the
right of the `k`-th node of the signature of `U`, or the level-`0` one if there is no such node -/
noncomputable def iniSegUcf (U k : M) : M :=
  if iniSegRight U k = ∅ then tpUcfZero (aoc U)
  else !(((1 : ℕ) : M), ⋃₀ (iniSegRight U k ∩₀
    fun r ↦ ∀ r' ∈ iniSegRight U k, r' = r ∨ r [iniSegOdr U] r'))

/-- `U | k` for `U ∈ stduoci_1` and `k < |U_sig|`: the array `iniSegAoc U k`, the signature
`U_sig ↾ k`, `ctp = dct`, and for `k > 0` the `ucflvldcn` `iniSegUcf U k` with `ucfdr = lf` -/
noncomputable def iniSeg (U k : M) : M :=
  if k = ∅ then ciTriple (iniSegAoc U k) (sig U ↾ k) dct
  else ciQuint (iniSegAoc U k) (sig U ↾ k) dct (iniSegUcf U k) lf

variable {U k i r : M}

theorem mem_iniSegNds_iff : r ∈ iniSegNds U k ↔ ∃ i ∈ k, sigdcn U i = r := by
  have hres : IsSetRestrictedTo (fun i ↦ sigdcn U i) k := isSetRestrictedTo_of_definable _
  rw [iniSegNds, mem_ran_toSetRestrictedTo_iff hres]

theorem mem_iniSegRight_iff :
    r ∈ iniSegRight U k ↔ r ∈ iniSegNds U k ∧ (sigdcn U k) [iniSegOdr U] r := by
  rw [iniSegRight, mem_comprehension_iff]

/-- The conditions of `uoci_1` for `U ∈ stduoci_1` -/
theorem uociCond_of_mem_stduoci_one (hU : U ∈ stduoci ((1 : ℕ) : M)) :
    UociCond (ciRec ↾₀ ((1 : ℕ) : M)) ((1 : ℕ) : M) (finaotci ((1 : ℕ) : M)) U := by
  have hUu := (mem_stduoci_iff.mp hU).left
  rwa [mem_uoci_iff_of_mem_omega (natCast_mem_omega 1)] at hUu

theorem aoc_mem_finaotci_of_mem_stduoci_one (hU : U ∈ stduoci ((1 : ℕ) : M)) :
    aoc U ∈ finaotci ((1 : ℕ) : M) :=
  (uociCond_of_mem_stduoci_one hU).right.right.left

theorem dom_sig_mem_omega_of_mem_stduoci_one (hU : U ∈ stduoci ((1 : ℕ) : M)) :
    dom (sig U) ∈ (ω : M) :=
  (uociCond_of_mem_stduoci_one hU).right.right.right.left.right.right.left

theorem subset_dom_sig_of_mem (hU : U ∈ stduoci ((1 : ℕ) : M)) (hk : k ∈ dom (sig U)) :
    k ⊆ dom (sig U) :=
  (ordinal_of_mem ordinal_omega (dom_sig_mem_omega_of_mem_stduoci_one hU)).transitive _ hk

theorem iniSegNds_subset (hU : U ∈ stduoci ((1 : ℕ) : M)) (hk : k ∈ dom (sig U)) :
    iniSegNds U k ⊆ ndOf (aoc U ﹫ ((1 : ℕ) : M)) := by
  intro r hr
  rw [mem_iniSegNds_iff] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  exact (siglvl_eq_one hU (subset_dom_sig_of_mem hU hk hi)).right

theorem finite_iniSegNds (hU : U ∈ stduoci ((1 : ℕ) : M)) (hk : k ∈ dom (sig U)) :
    MemStructure.Finite (iniSegNds U k) := by
  have h := (mem_finaotci_iff.mp (aoc_mem_finaotci_of_mem_stduoci_one hU)).right _
    (mem_succ_self ((1 : ℕ) : M))
  rw [mem_finotci_iff] at h
  exact h.right.of_subset (iniSegNds_subset hU hk)

theorem isStrictLinearOrder_iniSegOdr (hU : U ∈ stduoci ((1 : ℕ) : M)) :
    IsStrictLinearOrder (iniSegOdr U) (ndOf (aoc U ﹫ ((1 : ℕ) : M))) :=
  (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci (aoc_mem_aotci_of_mem_stduoci_one hU)
    (mem_succ_self _))).left

/-- The level-`1` tree of `U | k` is in `otci_1` -/
theorem iniSegTree_mem_otci (hU : U ∈ stduoci ((1 : ℕ) : M)) (hk : k ∈ dom (sig U)) :
    rtLosSLOT trvAZero !(iniSegNds U k, iniSegOdr U ↾↾ iniSegNds U k) ∈ otci ((1 : ℕ) : M) := by
  have hW1 := val_mem_otci_of_mem_aotci (aoc_mem_aotci_of_mem_stduoci_one hU) (mem_succ_self _)
  refine rtLosSLOT_mem_otci_one (fun _ ↦ ?_) fun a ha ↦ ?_
  · rw [isStrictLinearOrderedSet_orderedPair_iff]
    exact (isStrictLinearOrder_iniSegOdr hU).restrict₂ (iniSegNds_subset hU hk)
  · rw [losSet_orderedPair] at ha
    exact exists_eq_of_mem_otci_one hW1 (iniSegNds_subset hU hk ha)

theorem iniSegAoc_val_zero (hU : U ∈ stduoci ((1 : ℕ) : M)) :
    iniSegAoc U k ﹫ ∅ = aoc U ﹫ ∅ :=
  cc_restrict_val_zero (aoc_mem_aotci_of_mem_stduoci_one hU) _

theorem iniSegAoc_val_one (hU : U ∈ stduoci ((1 : ℕ) : M)) :
    iniSegAoc U k ﹫ ((1 : ℕ) : M) =
      rtLosSLOT trvAZero !(iniSegNds U k, iniSegOdr U ↾↾ iniSegNds U k) :=
  cc_restrict_val_one (aoc_mem_aotci_of_mem_stduoci_one hU) _

/-- The array of `U | k` is in `finaotci_1` -/
theorem iniSegAoc_mem_finaotci (hU : U ∈ stduoci ((1 : ℕ) : M)) (hk : k ∈ dom (sig U)) :
    iniSegAoc U k ∈ finaotci ((1 : ℕ) : M) := by
  have hA := aoc_mem_aotci_of_mem_stduoci_one hU
  have hAf := (mem_finaotci_iff.mp (aoc_mem_finaotci_of_mem_stduoci_one hU)).right
  have hX := iniSegTree_mem_otci hU hk
  rw [mem_finaotci_iff]
  refine ⟨cc_restrict_mem_aotci_one hA hX, fun i hi ↦ ?_⟩
  rcases mem_or_eq_of_mem_succ hi with h | h
  · have h0 : i = ∅ := by
      rw [natCast_succ, natCast_zero, mem_succ_iff] at h
      rcases h with h | h
      · exact h
      · simp at h
    subst h0
    rw [iniSegAoc_val_zero hU]
    exact hAf ∅ hi
  · subst h
    rw [iniSegAoc_val_one hU, mem_finotci_iff, ndOf_rtLosSLOT, losSet_orderedPair]
    exact ⟨hX, finite_iniSegNds hU hk⟩

theorem isFunction_iniSeg : IsFunction (iniSeg U k) := by
  by_cases hk0 : k = ∅
  · rw [iniSeg, if_pos hk0]
    exact isFunction_ciTriple _ _ _
  · rw [iniSeg, if_neg hk0]
    exact isFunction_ciQuint _ _ _ _ _

theorem aoc_iniSeg : aoc (iniSeg U k) = iniSegAoc U k := by
  by_cases hk0 : k = ∅
  · rw [iniSeg, if_pos hk0, aoc_ciTriple]
  · rw [iniSeg, if_neg hk0, aoc_ciQuint]

theorem sig_iniSeg : sig (iniSeg U k) = sig U ↾ k := by
  by_cases hk0 : k = ∅
  · rw [iniSeg, if_pos hk0, sig_ciTriple]
  · rw [iniSeg, if_neg hk0, sig_ciQuint]

theorem ctp_iniSeg : ctp (iniSeg U k) = dct := by
  by_cases hk0 : k = ∅
  · rw [iniSeg, if_pos hk0, ctp_ciTriple]
  · rw [iniSeg, if_neg hk0, ctp_ciQuint]

/-- The nearest node to the right of the `k`-th node of the signature, if any -/
theorem iniSegUcf_of_ne_empty (hU : U ∈ stduoci ((1 : ℕ) : M)) (hk : k ∈ dom (sig U))
    (hY : iniSegRight U k ≠ ∅) : ∃ m ∈ iniSegRight U k,
      (∀ r ∈ iniSegRight U k, r = m ∨ m [iniSegOdr U] r) ∧
        iniSegUcf U k = !(((1 : ℕ) : M), m) := by
  have hR := isStrictLinearOrder_iniSegOdr hU
  have hYS : iniSegRight U k ⊆ iniSegNds U k := fun r hr ↦ (mem_iniSegRight_iff.mp hr).left
  have hYf := (finite_iniSegNds hU hk).of_subset hYS
  obtain ⟨m, hm, hmin⟩ :=
    hR.exists_least_of_finite hYf (fun r hr ↦ iniSegNds_subset hU hk (hYS hr)) hY
  refine ⟨m, hm, fun r hr ↦ ?_, ?_⟩
  · by_cases h : r = m
    · exact .inl h
    · exact .inr (hmin r hr h)
  have hset : (iniSegRight U k ∩₀ fun r ↦ ∀ r' ∈ iniSegRight U k, r' = r ∨ r [iniSegOdr U] r') =
      {m} := by
    ext r
    rw [mem_comprehension_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hr, hrmin⟩
      by_contra hrm
      rcases hrmin m hm with h | h
      · exact hrm h.symm
      · exact hR.asymm h (hmin r hr hrm)
    · rintro rfl
      refine ⟨hm, fun r' hr' ↦ ?_⟩
      by_cases h : r' = r
      · exact .inl h
      · exact .inr (hmin r' hr' h)
  rw [iniSegUcf, if_neg hY, hset, sUnion_singleton]

/-- The proper initial segments of an element of `stduoci_1` are in `uoci_1` -/
theorem iniSeg_mem_uoci (hU : U ∈ stduoci ((1 : ℕ) : M)) (hk : k ∈ dom (sig U)) :
    iniSeg U k ∈ uoci ((1 : ℕ) : M) := by
  obtain ⟨-, -, -, ⟨hsf, hinj, hdom, hsc⟩, -⟩ := uociCond_of_mem_stduoci_one hU
  have hsub := subset_dom_sig_of_mem hU hk
  have hkω : k ∈ (ω : M) := ordinal_omega.transitive _ hdom hk
  have hA := aoc_mem_aotci_of_mem_stduoci_one hU
  have hW1 := val_mem_otci_of_mem_aotci hA (mem_succ_self _)
  have hval : ∀ i ∈ k, sig (iniSeg U k) ﹫ i = sig U ﹫ i := fun i hi ↦ by
    rw [sig_iniSeg, val_restrict _ hsf hi (hsub hi)]
  have hsdom : dom (sig (iniSeg U k)) = k := by rw [sig_iniSeg, dom_restrict_of_subset hsf hsub]
  have hsig : IsFunction (sig (iniSeg U k)) ∧
      (∀ i ∈ dom (sig (iniSeg U k)), ∀ j ∈ dom (sig (iniSeg U k)),
        sig (iniSeg U k) ﹫ i = sig (iniSeg U k) ﹫ j → i = j) ∧
      dom (sig (iniSeg U k)) ∈ (ω : M) ∧
      ∀ i ∈ dom (sig (iniSeg U k)), SigCond ((1 : ℕ) : M) (iniSeg U k) i := by
    rw [hsdom]
    refine ⟨by rw [sig_iniSeg]; exact hsf.restrict _, fun i hi j hj h ↦ ?_, hkω, fun i hi ↦ ?_⟩
    · rw [hval i hi, hval j hj] at h
      exact hinj i (hsub hi) j (hsub hj) h
    obtain ⟨hp, hl, -, -, hct⟩ := hsc i (hsub hi)
    have hl1 := (siglvl_eq_one hU (hsub hi)).left
    have hsl : siglvl (iniSeg U k) i = siglvl U i := by rw [siglvl, siglvl, hval i hi]
    have hsd : sigdcn (iniSeg U k) i = sigdcn U i := by rw [sigdcn, sigdcn, hval i hi]
    refine ⟨by rw [hval i hi]; exact hp, by rw [hsl]; exact hl, fun he ↦ ?_, fun _ ↦ .inl ?_,
      by rw [hsd]; exact hct⟩
    · rw [hsl, hl1] at he
      exact (isOdd_one.not_isEven he).elim
    · rw [hsl, hl1, hsd, aoc_iniSeg, iniSegAoc_val_one hU, rtOf_rtLosSLOT, losSet_orderedPair,
        mem_iniSegNds_iff]
      exact ⟨i, hi, rfl⟩
  have haoc : aoc (iniSeg U k) ∈ finaotci ((1 : ℕ) : M) := by
    rw [aoc_iniSeg]
    exact iniSegAoc_mem_finaotci hU hk
  rw [mem_uoci_iff_of_mem_omega (natCast_mem_omega 1)]
  by_cases hk0 : k = ∅
  · have h3 : dom (iniSeg U k) = ((3 : ℕ) : M) := by rw [iniSeg, if_pos hk0, dom_ciTriple]
    have hs0 : sig (iniSeg U k) = ∅ := by rw [sig_iniSeg, hk0, restrict_empty]
    refine ⟨isFunction_iniSeg, .inl h3, haoc, hsig, .inr ctp_iniSeg, fun _ ↦ ctp_iniSeg,
      iff_of_true h3 (.inl ⟨hs0, isOdd_one⟩), fun h ↦ ?_⟩
    rw [h3] at h
    exact (notMem_self _ h).elim
  have he : iniSeg U k = ciQuint (iniSegAoc U k) (sig U ↾ k) dct (iniSegUcf U k) lf := by
    rw [iniSeg, if_neg hk0]
  have h5 : dom (iniSeg U k) = ((5 : ℕ) : M) := by rw [he, dom_ciQuint]
  have hne (j l : ℕ) (hjl : j ≠ l) : ((j : ℕ) : M) ≠ ((l : ℕ) : M) := by
    rw [Ne, natCast_inj]
    exact hjl
  refine ⟨isFunction_iniSeg, .inr (.inl h5), haoc, hsig, .inr ctp_iniSeg, fun h ↦ ?_, ?_,
    fun _ ↦ ?_⟩
  · rw [← hsdom, h.left, dom_empty] at hk0
    exact (hk0 rfl).elim
  · rw [h5, ctp_iniSeg]
    refine iff_of_false (hne 5 3 (by omega)) ?_
    rintro (⟨h, -⟩ | h)
    · rw [← hsdom, h, dom_empty] at hk0
      exact hk0 rfl
    · exact ct_ne_dct h.symm
  have hucf : ucflvldcn (iniSeg U k) = iniSegUcf U k := by rw [he, ucflvldcn_ciQuint]
  have hdr : ucfdr (iniSeg U k) = lf := by rw [he, ucfdr_ciQuint]
  have hpost : IsOrderedPair (ucflvldcn (iniSeg U k)) ∧ ucflvl (iniSeg U k) ∈ succ ((1 : ℕ) : M) ∧
      ucfdcn (iniSeg U k) ∈ ndOf (aoc (iniSeg U k) ﹫ ucflvl (iniSeg U k)) ∧
      ctp (uc (ucfdcn (iniSeg U k))) = dct := by
    rw [ucfdcn, ucflvl, hucf, aoc_iniSeg]
    by_cases hY : iniSegRight U k = ∅
    · rw [iniSegUcf, if_pos hY, tpUcfZero, lvl_orderedPair, dcn_orderedPair, iniSegAoc_val_zero hU]
      obtain ⟨l, hnd, -⟩ := exists_ndOf_eq_of_mem_otci_empty
        (val_mem_otci_of_mem_aotci hA (mem_succ_of_mem empty_mem_natCast_one))
      rw [hnd, sUnion_singleton, uc_orderedPair, otci0Uc, ctp_ciTriple]
      exact ⟨⟨_, _, rfl⟩, mem_succ_of_mem empty_mem_natCast_one, mem_singleton _, rfl⟩
    · obtain ⟨m, hm, -, hm'⟩ := iniSegUcf_of_ne_empty hU hk hY
      have hmS := (mem_iniSegRight_iff.mp hm).left
      rw [hm', lvl_orderedPair, dcn_orderedPair, iniSegAoc_val_one hU, ndOf_rtLosSLOT,
        losSet_orderedPair, uc_eq_dctUZero_of_mem_otci_one hW1 (iniSegNds_subset hU hk hmS),
        dctUZero_eq_lfTrvUoci, ctp_lfTrvUoci]
      exact ⟨⟨_, _, rfl⟩, mem_succ_self _, hmS, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := hpost
  exact ⟨h1, h2, h3, h4, .inl hdr, iff_of_true h5 hdr,
    fun h ↦ (hne 5 6 (by omega) (h5.symm.trans h)).elim⟩

/-- The proper initial segments of an element of `stduoci_1` are in `stduoci_1` -/
theorem iniSeg_mem_stduoci (hU : U ∈ stduoci ((1 : ℕ) : M)) (hk : k ∈ dom (sig U)) :
    iniSeg U k ∈ stduoci ((1 : ℕ) : M) := by
  obtain ⟨-, -, -, ⟨hsf, hinj, -, hsc⟩, -⟩ := uociCond_of_mem_stduoci_one hU
  have hsub := subset_dom_sig_of_mem hU hk
  have hA := aoc_mem_aotci_of_mem_stduoci_one hU
  have hW1 := val_mem_otci_of_mem_aotci hA (mem_succ_self _)
  have hstd := (mem_stduoci_iff.mp hU).right
  rw [mem_stduoci_iff]
  refine ⟨iniSeg_mem_uoci hU hk, fun i hi p hp ↦ ?_⟩
  rw [aoc_iniSeg] at hp ⊢
  rcases mem_or_eq_of_mem_succ hi with h | h
  · have h0 : i = ∅ := by
      rw [natCast_succ, natCast_zero, mem_succ_iff] at h
      rcases h with h | h
      · exact h
      · simp at h
    subst h0
    rw [iniSegAoc_val_zero hU] at hp ⊢
    obtain ⟨hA', -, hC'⟩ := hstd ∅ hi p hp
    obtain ⟨l, hnd, hrt⟩ := exists_ndOf_eq_of_mem_otci_empty
      (val_mem_otci_of_mem_aotci hA (mem_succ_of_mem empty_mem_natCast_one))
    have hpr : p ∈ rtOf (aoc U ﹫ ∅) := by
      rw [hrt]
      rwa [hnd] at hp
    exact ⟨hA', fun h ↦ (h.right ⟨isEven_empty, hpr⟩).elim, hC'⟩
  subst h
  rw [iniSegAoc_val_one hU, ndOf_rtLosSLOT, losSet_orderedPair] at hp
  have hpU := iniSegNds_subset hU hk hp
  have hct : ctp (uc p) = dct := by
    rw [uc_eq_dctUZero_of_mem_otci_one hW1 hpU, dctUZero_eq_lfTrvUoci, ctp_lfTrvUoci]
  refine ⟨fun h ↦ (isOdd_one.not_isEven h.left).elim, fun _ ↦ ?_,
    fun h ↦ (ct_ne_dct (h.symm.trans hct)).elim⟩
  have hB := (hstd _ hi p hpU).right.left ⟨hct, fun h ↦ isOdd_one.not_isEven h.left⟩
  rw [mem_iniSegNds_iff] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  obtain ⟨⟨x, y, hxy⟩, -, -, -, -⟩ := hsc j (hsub hj)
  have hx : x = ((1 : ℕ) : M) := by
    have h := (siglvl_eq_one hU (hsub hj)).left
    rwa [siglvl, hxy, lvl_orderedPair] at h
  have hy : y = sigdcn U j := by rw [sigdcn, hxy, dcn_orderedPair]
  have hl : lbl (sigdcn U j) ∈ dom (sig U) := by
    by_contra hn
    rw [val_eq_empty_of_not_mem_dom hn] at hB
    exact orderedPair_ne_empty _ _ hB
  have hlj : lbl (sigdcn U j) = j := hinj _ hl _ (hsub hj) (by rw [← hB, hxy, hx, hy])
  rw [hlj] at hB
  rw [sig_iniSeg, hlj, val_restrict _ hsf hj (hsub hj)]
  exact hB

/-- A standard `uoci_1` with empty signature is trivial -/
theorem mem_trvuoci_one_of_sig_eq_empty (hV : V ∈ stduoci ((1 : ℕ) : M)) (hs : sig V = ∅) :
    V ∈ trvuoci ((1 : ℕ) : M) := by
  have hc := uociCond_of_mem_stduoci_one hV
  have hA := aoc_mem_finaotci_of_mem_stduoci_one hV
  rw [mem_trvuoci_iff]
  refine ⟨hV, ?_, hc.right.right.right.right.right.left ⟨hs, isOdd_one⟩⟩
  rw [mem_trvaotci_iff]
  refine ⟨(mem_finaotci_iff.mp hA).left, fun i hi ↦ ?_⟩
  have hfin := (mem_finaotci_iff.mp hA).right i hi
  rw [mem_trvotci_iff]
  refine ⟨hfin, ?_⟩
  rcases mem_or_eq_of_mem_succ hi with hi' | rfl
  · have hi0 : i = ∅ := by
      rw [natCast_succ, natCast_zero, mem_succ_iff] at hi'
      rcases hi' with h' | h'
      · exact h'
      · simp at h'
    subst hi0
    obtain ⟨l, hnd, hrt⟩ := exists_ndOf_eq_of_mem_otci_empty (mem_finotci_iff.mp hfin).left
    refine ⟨fun _ p hp ↦ ?_, fun ho ↦ (not_isOdd_empty ho).elim⟩
    rw [hnd, mem_singleton_iff] at hp
    rw [hrt, hp, uc_orderedPair, otci0Uc, ctp_ciTriple]
    simp
  · refine ⟨fun he ↦ (isOdd_one.not_isEven he).elim, fun _ ↦ ?_⟩
    ext w
    refine ⟨fun hw ↦ ?_, by simp⟩
    obtain ⟨j, hj, -⟩ := exists_sigdcn_eq hV hw
    rw [hs, dom_empty] at hj
    simp at hj

end IniSeg

section TpSig

/-! ### The signature, type and `ucf` of a node of `Q ⊗ X` -/

/-- The node `q` of the label `(q, h)` of a node `x` of `Q(2) ⊗ X` -/
noncomputable def nodeQ : ClassFunction M := fun x ↦ left (lbl x)

/-- The identifier `q_uc` of the node `q` of the label `(q, h)` of `x` -/
noncomputable def nodeU : ClassFunction M := fun x ↦ uc (left (lbl x))

/-- The embedding `h` of the label `(q, h)` of `x` -/
noncomputable def nodeH : ClassFunction M := fun x ↦ right (lbl x)

instance : (nodeQ : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq (ᵣ0 : L.RudimentaryTerm 1).right.left fun _ ↦ by
    simp [nodeQ, lbl]

instance : (nodeU : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq (ᵣ0 : L.RudimentaryTerm 1).right.left.left fun _ ↦ by
    simp [nodeU, uc, lbl]

instance : (nodeH : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq (ᵣ0 : L.RudimentaryTerm 1).right.right fun _ ↦ by
    simp [nodeH, lbl]

/-- The node `w` of `X(l)` whose copy in `(X ⊗ Z)(l)` is `y` -/
noncomputable def tpOrig (X l y : M) : M :=
  ⋃₀ (ndOf (X ﹫ l) ∩₀ fun w ↦ l = ∅ ∨ tensorProdOneAZeroRelabel (X ﹫ l) trvAZero ﹫ w = y)

/-- The node `x` of `(Q ⊗ X)(1)` comes from `Q(2) ⊗ X`, with label `(q, h)` for `q ∈ Q(2)_nd` -/
def IsTpTwo (Q X x : M) : Prop := x ∈ tensorProdTwoAOneNds (Q ﹫ 2) X

noncomputable instance (Q X x : M) : Decidable (IsTpTwo Q X x) := Classical.propDecidable _

/-- The domain of the signature of `x`: that of `q_uc` if `x = (_, (q, h))` comes from `Q(2)`,
and `∅` otherwise -/
noncomputable def tpSigDom (Q X x : M) : M :=
  if IsTpTwo Q X x then dom (sig (nodeU x)) else ∅

/-- The `i`-th entry `(l_i, H(w_i))` of the signature of `U` under `H`, read in `X` -/
noncomputable def tpSigEntryAux (X U H i : M) : M :=
  !(siglvl U i, tpOrig X (siglvl U i) ((H ﹫ siglvl U i) ﹫ sigdcn U i))

/-- The `i`-th entry `(l_i, h(w_i))` of the signature of `x = (_, (q, h))`, read in `X`, for the
`i`-th entry `(l_i, w_i)` of the signature of `q_uc` -/
noncomputable def tpSigEntry (X x i : M) : M := tpSigEntryAux X (nodeU x) (nodeH x) i

/-- The signature of the node `x = (_, (q, h))` of `(Q ⊗ X)(1)` in the nodes of `X`: the images
`(l_i, h(w_i))` of the entries `(l_i, w_i)` of `q_uc`'s signature, read in `X` -/
noncomputable def tpSig (Q X x : M) : M := (fun i ↦ tpSigEntry X x i) ↾₀ tpSigDom Q X x

/-- The node `x` of `(Q ⊗ X)(1)` is of type `ct`: it comes from `Q(2)` and its node is of type
`ct` -/
def TpCt (Q X x : M) : Prop := IsTpTwo Q X x ∧ ctp (nodeU x) = ct

noncomputable instance (U : M) : Decidable (((3 : ℕ) : M) ∈ dom U) := Classical.propDecidable _

/-- The `ucflvldcn` of `U` as an element of a tensor product: that of `U` if `U` has a `ucf`, and
otherwise (e.g. for `U` of type `ct`) the last entry of its signature -/
noncomputable def ucfOrLast (U : M) : M :=
  if ((3 : ℕ) : M) ∈ dom U then ucflvldcn U else sig U ﹫ ⋃₀ dom (sig U)

/-- The image `(l, H(w))` of `e = (l, w)` under `H`, read in `X` -/
noncomputable def tpUcfAux (X e H : M) : M := !(lvl e, tpOrig X (lvl e) ((H ﹫ lvl e) ﹫ dcn e))

/-- The `ucflvldcn` `(l, h(w))` of the node `x = (_, (q, h))` from `Q(2)`, read in `X`, for
`ucfOrLast q_uc = (l, w)` -/
noncomputable def tpUcfTwo (X x : M) : M := tpUcfAux X (ucfOrLast (nodeU x)) (nodeH x)

/-- The `ucflvldcn` of the node `x` of `(Q ⊗ X)(1)` in `X`: `tpUcfTwo X x` for `x` from `Q(2)`,
and the level-`0` `ucflvldcn` for `x` from `Q(1)` -/
noncomputable def tpUcf (Q X x : M) : M := if IsTpTwo Q X x then tpUcfTwo X x else tpUcfZero X

end TpSig

section Contraction

/-! ### The contraction of a finite sequence of finite sequences -/

/-- The position `(i, j)` in the sequence of sequences `s` is before every occurrence of `y` -/
def PrecedesAll (s y i j : M) : Prop :=
  ∀ i' ∈ dom s, ∀ j' ∈ dom (s ﹫ i'), (s ﹫ i') ﹫ j' = y → i ∈ i' ∨ (i = i' ∧ j ∈ j')

/-- `x` occurs in the sequence of sequences `s` before the first occurrence of `y` -/
def OccursBefore (s x y : M) : Prop :=
  ∃ i ∈ dom s, ∃ j ∈ dom (s ﹫ i), (s ﹫ i) ﹫ j = x ∧ PrecedesAll s y i j

/-- The entries of the sequences of `s` -/
noncomputable def ctrSet (s : M) : M := ⋃₀ ran ((fun f ↦ ran f) ↾₀ ran s)

/-- `c` is the contraction of `s`: the injective finite sequence of the entries of the sequences of
`s`, in the order of their first occurrences -/
def IsContraction (s c : M) : Prop :=
  IsFunction c ∧ dom c ∈ (ω : M) ∧ (∀ k ∈ dom c, ∀ l ∈ dom c, c ﹫ k = c ﹫ l → k = l) ∧
    ran c = ctrSet s ∧ ∀ k ∈ dom c, ∀ l ∈ dom c, k ∈ l → OccursBefore s (c ﹫ k) (c ﹫ l)

/-- The contraction of the finite sequence `s` of finite sequences: their concatenation with the
repetitions removed from left to right -/
noncomputable def contraction (s : M) : M :=
  ⋃₀ (𝒫 ((ω : M) ×ˢ ctrSet s) ∩₀ fun c ↦ IsContraction s c)

/-- `s` is a finite sequence of finite sequences -/
def IsFinSeqSeq (s : M) : Prop :=
  IsFunction s ∧ dom s ∈ (ω : M) ∧ ∀ i ∈ dom s, IsFunction (s ﹫ i) ∧ dom (s ﹫ i) ∈ (ω : M)

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ PrecedesAll (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  unfold PrecedesAll; infer_instance

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ OccursBefore (xs 0) (xs 1) (xs 2))
    Set.univ := by
  unfold OccursBefore; infer_instance

/-- The order of the first occurrences on the entries of `s` -/
noncomputable def ctrRel (s : M) : M :=
  (ctrSet s ×ˢ ctrSet s) ∩₀ fun z ↦ OccursBefore s (left z) (right z)

variable {s c x y z : M}

theorem mem_ctrSet_iff (hs : IsFinSeqSeq s) :
    x ∈ ctrSet s ↔ ∃ i ∈ dom s, ∃ j ∈ dom (s ﹫ i), (s ﹫ i) ﹫ j = x := by
  have hres : IsSetRestrictedTo (fun f ↦ ran f) (ran s) := isSetRestrictedTo_of_definable _
  rw [ctrSet, mem_sUnion_iff]
  simp only [mem_ran_toSetRestrictedTo_iff hres]
  constructor
  · rintro ⟨y, ⟨f, hf, rfl⟩, hx⟩
    rw [hs.left.mem_ran_iff] at hf
    obtain ⟨i, hi, rfl⟩ := hf
    rw [(hs.right.right i hi).left.mem_ran_iff] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact ⟨i, hi, j, hj, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    refine ⟨_, ⟨s ﹫ i, by rw [hs.left.mem_ran_iff]; exact ⟨i, hi, rfl⟩, rfl⟩, ?_⟩
    rw [(hs.right.right i hi).left.mem_ran_iff]
    exact ⟨j, hj, rfl⟩

theorem ordinal_of_mem_dom (hs : IsFinSeqSeq s) {i : M} (hi : i ∈ dom s) : Ordinal i :=
  ordinal_of_mem ordinal_omega (ordinal_omega.transitive _ hs.right.left hi)

theorem ordinal_of_mem_dom_val (hs : IsFinSeqSeq s) {i j : M} (hi : i ∈ dom s)
    (hj : j ∈ dom (s ﹫ i)) : Ordinal j :=
  ordinal_of_mem ordinal_omega (ordinal_omega.transitive _ (hs.right.right i hi).right hj)

omit [Inhabited M] [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M] in
/-- The lexicographic order of positions is transitive -/
private theorem lex_trans {i j i' j' i'' j'' : M} (hi'' : Ordinal i'') (hj'' : Ordinal j'')
    (h₁ : i ∈ i' ∨ (i = i' ∧ j ∈ j'))
    (h₂ : (i' = i'' ∧ j' = j'') ∨ i' ∈ i'' ∨ (i' = i'' ∧ j' ∈ j'')) :
    i ∈ i'' ∨ (i = i'' ∧ j ∈ j'') := by
  rcases h₂ with ⟨rfl, rfl⟩ | h₂ | ⟨rfl, h₂⟩
  · exact h₁
  · rcases h₁ with h₁ | ⟨rfl, -⟩
    · exact .inl (hi''.transitive _ h₂ h₁)
    · exact .inl h₂
  · rcases h₁ with h₁ | ⟨rfl, h₁⟩
    · exact .inl h₁
    · exact .inr ⟨rfl, hj''.transitive _ h₂ h₁⟩

/-- The first occurrence of an entry -/
theorem exists_firstOcc (hs : IsFinSeqSeq s) (hx : x ∈ ctrSet s) :
    ∃ i ∈ dom s, ∃ j ∈ dom (s ﹫ i), (s ﹫ i) ﹫ j = x ∧
      ∀ i' ∈ dom s, ∀ j' ∈ dom (s ﹫ i'), (s ﹫ i') ﹫ j' = x →
        (i = i' ∧ j = j') ∨ i ∈ i' ∨ (i = i' ∧ j ∈ j') := by
  rw [mem_ctrSet_iff hs] at hx
  obtain ⟨i₀, hi₀, j₀, hj₀, hx₀⟩ := hx
  obtain ⟨i, hio, ⟨hi, j₁, hj₁, hx₁⟩, himin⟩ :=
    exists_min_ordinal (A := fun i ↦ i ∈ dom s ∧ ∃ j ∈ dom (s ﹫ i), (s ﹫ i) ﹫ j = x)
      (ordinal_of_mem_dom hs hi₀) ⟨hi₀, j₀, hj₀, hx₀⟩
  obtain ⟨j, hjo, ⟨hj, hxj⟩, hjmin⟩ :=
    exists_min_ordinal (A := fun j ↦ j ∈ dom (s ﹫ i) ∧ (s ﹫ i) ﹫ j = x)
      (ordinal_of_mem_dom_val hs hi hj₁) ⟨hj₁, hx₁⟩
  refine ⟨i, hi, j, hj, hxj, fun i' hi' j' hj' hx' ↦ ?_⟩
  rcases olt_trichotomy hio (ordinal_of_mem_dom hs hi') with h | rfl | h
  · exact .inr (.inl h.right.right)
  · rcases olt_trichotomy hjo (ordinal_of_mem_dom_val hs hi' hj') with h' | rfl | h'
    · exact .inr (.inr ⟨rfl, h'.right.right⟩)
    · exact .inl ⟨rfl, rfl⟩
    · exact (hjmin j' h'.right.right ⟨hj', hx'⟩).elim
  · exact (himin i' h.right.right ⟨hi', j', hj', hx'⟩).elim

theorem not_occursBefore_self : ¬OccursBefore s x x := by
  rintro ⟨i, hi, j, hj, hx, h⟩
  rcases h i hi j hj hx with h | ⟨-, h⟩ <;> exact notMem_self _ h

theorem OccursBefore.trans (hs : IsFinSeqSeq s) (hxy : OccursBefore s x y)
    (hyz : OccursBefore s y z) : OccursBefore s x z := by
  obtain ⟨i, hi, j, hj, hx, h₁⟩ := hxy
  obtain ⟨i', hi', j', hj', hy, h₂⟩ := hyz
  refine ⟨i, hi, j, hj, hx, fun i'' hi'' j'' hj'' hz ↦ ?_⟩
  exact lex_trans (ordinal_of_mem_dom hs hi'') (ordinal_of_mem_dom_val hs hi'' hj'')
    (h₁ i' hi' j' hj' hy) (.inr (h₂ i'' hi'' j'' hj'' hz))

theorem occursBefore_trichotomous (hs : IsFinSeqSeq s) (hx : x ∈ ctrSet s) (hy : y ∈ ctrSet s) :
    OccursBefore s x y ∨ x = y ∨ OccursBefore s y x := by
  obtain ⟨i, hi, j, hj, hxv, hxmin⟩ := exists_firstOcc hs hx
  obtain ⟨i', hi', j', hj', hyv, hymin⟩ := exists_firstOcc hs hy
  rcases olt_trichotomy (ordinal_of_mem_dom hs hi) (ordinal_of_mem_dom hs hi') with h | rfl | h
  · exact .inl ⟨i, hi, j, hj, hxv, fun i'' hi'' j'' hj'' hz ↦
      lex_trans (ordinal_of_mem_dom hs hi'') (ordinal_of_mem_dom_val hs hi'' hj'')
        (.inl h.right.right) (hymin i'' hi'' j'' hj'' hz)⟩
  · rcases olt_trichotomy (ordinal_of_mem_dom_val hs hi hj) (ordinal_of_mem_dom_val hs hi hj') with
      h | rfl | h
    · exact .inl ⟨i, hi, j, hj, hxv, fun i'' hi'' j'' hj'' hz ↦
        lex_trans (ordinal_of_mem_dom hs hi'') (ordinal_of_mem_dom_val hs hi'' hj'')
          (.inr ⟨rfl, h.right.right⟩) (hymin i'' hi'' j'' hj'' hz)⟩
    · exact .inr (.inl (hxv.symm.trans hyv))
    · exact .inr (.inr ⟨i, hi', j', hj', hyv, fun i'' hi'' j'' hj'' hz ↦
        lex_trans (ordinal_of_mem_dom hs hi'') (ordinal_of_mem_dom_val hs hi'' hj'')
          (.inr ⟨rfl, h.right.right⟩) (hxmin i'' hi'' j'' hj'' hz)⟩)
  · exact .inr (.inr ⟨i', hi', j', hj', hyv, fun i'' hi'' j'' hj'' hz ↦
      lex_trans (ordinal_of_mem_dom hs hi'') (ordinal_of_mem_dom_val hs hi'' hj'')
        (.inl h.right.right) (hxmin i'' hi'' j'' hj'' hz)⟩)

theorem rel_ctrRel_iff : x [ctrRel s] y ↔ (x ∈ ctrSet s ∧ y ∈ ctrSet s) ∧ OccursBefore s x y := by
  change !(x, y) ∈ (ctrSet s ×ˢ ctrSet s) ∩₀ _ ↔ _
  rw [mem_comprehension_iff, pair_mem_sprod_iff, left_orderedPair, right_orderedPair]

theorem finite_ctrSet (hs : IsFinSeqSeq s) : MemStructure.Finite (ctrSet s) := by
  have hres : IsSetRestrictedTo (fun f ↦ ran f) (ran s) := isSetRestrictedTo_of_definable _
  have hran : MemStructure.Finite (ran s) :=
    (finite_of_mem_omega hs.right.left).of_isSurjectionFromTo (isSurjectionFromTo_dom_ran hs.left)
  refine Finite.sUnion ?_ fun y hy ↦ ?_
  · have h := isSurjectionFromTo_dom_ran (isFunction_toSetRestrictedTo hres)
    rw [dom_toSetRestrictedTo hres] at h
    exact hran.of_isSurjectionFromTo h
  · rw [mem_ran_toSetRestrictedTo_iff hres] at hy
    obtain ⟨f, hf, rfl⟩ := hy
    rw [hs.left.mem_ran_iff] at hf
    obtain ⟨i, hi, rfl⟩ := hf
    exact (finite_of_mem_omega (hs.right.right i hi).right).of_isSurjectionFromTo
      (isSurjectionFromTo_dom_ran (hs.right.right i hi).left)

/-- The order of the first occurrences is a strict well-order on the entries -/
theorem isStrictWellOrder_ctrRel (hs : IsFinSeqSeq s) :
    IsStrictWellOrder (ctrRel s) (ctrSet s) := by
  have hL : IsStrictLinearOrder (ctrRel s) (ctrSet s) := by
    refine ⟨(isRelationOn_sprod _).subset (comprehension_subset _ _), fun x _ h ↦ ?_,
      fun x _ y _ z _ hxy hyz ↦ ?_, fun x hx y hy ↦ ?_⟩
    · exact not_occursBefore_self (rel_ctrRel_iff.mp h).right
    · rw [rel_ctrRel_iff] at hxy hyz ⊢
      exact ⟨⟨hxy.left.left, hyz.left.right⟩, hxy.right.trans hs hyz.right⟩
    · rcases occursBefore_trichotomous hs hx hy with h | h | h
      · exact .inl (rel_ctrRel_iff.mpr ⟨⟨hx, hy⟩, h⟩)
      · exact .inr (.inl h)
      · exact .inr (.inr (rel_ctrRel_iff.mpr ⟨⟨hy, hx⟩, h⟩))
  refine ⟨hL, hL.isRelationOn, fun b hb hne ↦ ?_⟩
  obtain ⟨m, hm, hmin⟩ := hL.exists_least_of_finite ((finite_ctrSet hs).of_subset hb) hb hne
  refine ⟨m, hm, fun y hy h ↦ ?_⟩
  by_cases hym : y = m
  · rw [hym] at h
    exact hL.irrefl _ h
  · exact hL.asymm h (hmin y hy hym)

/-- The inverse of the collapse of the order of the first occurrences is a contraction -/
theorem isContraction_inv_collapseOn (hs : IsFinSeqSeq s) :
    IsContraction s (collapseOn (ctrRel s) (ctrSet s))⁻¹ := by
  have hW := isStrictWellOrder_ctrRel hs
  have hWF := hW.isStrictWellFounded
  have hb :
      collapseOn (ctrRel s) (ctrSet s) !: ctrSet s ↔ ran (collapseOn (ctrRel s) (ctrSet s)) := by
    rw [isBijectionFromTo_iff]
    refine ⟨⟨hWF.isFunction_collapseOn, hWF.dom_collapseOn, fun _ h ↦ h⟩, fun x hx x' hx' h ↦ ?_,
      rfl⟩
    exact (hWF.collapseOn_injOn hW.isExtensionalOn hx hx').mp h
  have hbi := hb.inv
  have hfin : MemStructure.Finite (ran (collapseOn (ctrRel s) (ctrSet s))) :=
    (finite_ctrSet hs).of_isBijectionFromTo hb
  refine ⟨hbi.isFunction, ?_, fun k hk l hl h ↦ ?_, hbi.ran_eq, fun k hk l hl hkl ↦ ?_⟩
  · rw [hbi.dom_eq]
    exact hfin.mem_omega hW.ordinal_ran_collapseOn
  · rw [hbi.dom_eq] at hk hl
    exact hbi.isInjectionFromTo.eq hk hl h
  · rw [hbi.dom_eq] at hk hl
    have hxk := hbi.isFunctionFromTo.val_mem hk
    have hxl := hbi.isFunctionFromTo.val_mem hl
    have h := (hW.rel_iff_collapseOn_mem_collapseOn hxl hxk).mpr
      (by rw [hb.val_inv_val hk, hb.val_inv_val hl]; exact hkl)
    exact (rel_ctrRel_iff.mp h).right

/-- A contraction is the inverse of the collapse of the order of the first occurrences -/
theorem eq_inv_collapseOn_of_isContraction (hs : IsFinSeqSeq s) (h : IsContraction s c) :
    c = (collapseOn (ctrRel s) (ctrSet s))⁻¹ := by
  obtain ⟨hcf, hdom, hinj, hran, hord⟩ := h
  have hW := isStrictWellOrder_ctrRel hs
  have hb : c !: dom c ↔ ctrSet s := by
    rw [isBijectionFromTo_iff]
    exact ⟨⟨hcf, rfl, fun _ h ↦ hran ▸ h⟩, hinj, hran⟩
  have hbi := hb.inv
  have hdo : Ordinal (dom c) := ordinal_of_mem ordinal_omega hdom
  -- `c` is increasing, so its inverse is increasing
  have hrel (k l : M) (hk : k ∈ dom c) (hl : l ∈ dom c) :
      (c ﹫ k) [ctrRel s] (c ﹫ l) ↔ k ∈ l := by
    have hck := hb.isFunctionFromTo.val_mem hk
    have hcl := hb.isFunctionFromTo.val_mem hl
    constructor
    · intro h
      rcases olt_trichotomy (ordinal_of_mem hdo hk) (ordinal_of_mem hdo hl) with h' | rfl | h'
      · exact h'.right.right
      · exact (hW.isStrictLinearOrder.irrefl _ h).elim
      · exact (hW.isStrictLinearOrder.asymm h
          (rel_ctrRel_iff.mpr ⟨⟨hcl, hck⟩, hord l hl k hk h'.right.right⟩)).elim
    · intro h
      exact rel_ctrRel_iff.mpr ⟨⟨hck, hcl⟩, hord k hk l hl h⟩
  have hrec : IsCollapseOn (ctrRel s) (ctrSet s) c⁻¹ := by
    refine ⟨hbi.isFunction, hbi.dom_eq, fun x hx ↦ ?_⟩
    have hpred : predSet (ctrRel s) x ⊆ dom c⁻¹ := fun y hy ↦ by
      rw [hbi.dom_eq]
      exact (rel_ctrRel_iff.mp (mem_predSet_iff.mp hy)).left.left
    have hk := hbi.isFunctionFromTo.val_mem hx
    ext z
    rw [(hbi.isFunction.restrict _).mem_ran_iff, dom_restrict_of_subset hbi.isFunction hpred]
    constructor
    · intro hz
      have hzd : z ∈ dom c := hdo.transitive _ hk hz
      refine ⟨c ﹫ z, mem_predSet_iff.mpr ?_, ?_⟩
      · have h := (hrel z _ hzd hk).mpr hz
        rwa [hb.val_inv_val hx] at h
      · rw [val_restrict _ hbi.isFunction (mem_predSet_iff.mpr ?_)
          (by rw [hbi.dom_eq]; exact hb.isFunctionFromTo.val_mem hzd), hb.inv_val_val hzd]
        have h := (hrel z _ hzd hk).mpr hz
        rwa [hb.val_inv_val hx] at h
    · rintro ⟨y, hy, rfl⟩
      have hyX := (rel_ctrRel_iff.mp (mem_predSet_iff.mp hy)).left.left
      rw [val_restrict _ hbi.isFunction hy (by rw [hbi.dom_eq]; exact hyX)]
      have hl := hbi.isFunctionFromTo.val_mem hyX
      have h := mem_predSet_iff.mp hy
      rw [← hb.val_inv_val hyX, ← hb.val_inv_val hx] at h
      exact (hrel _ _ hl hk).mp h
  have heq := hW.isStrictWellFounded.eq_of_isWFRecursionOn hrec
    hW.isStrictWellFounded.isCollapseOn_collapseOn
  rw [← heq, inv_inv hcf.isRelation]

instance (s : M) : Class.Definable (fun c ↦ IsContraction s c) Set.univ := by
  unfold IsContraction
  have : Class.Definable (fun c : M ↦ ∀ k ∈ dom c, ∀ l ∈ dom c, c ﹫ k = c ﹫ l → k = l)
      Set.univ := by
    infer_instance
  have : Class.Definable (fun c : M ↦ ran c = ctrSet s) Set.univ := by
    infer_instance
  have : Class.Definable
      (fun c : M ↦ ∀ k ∈ dom c, ∀ l ∈ dom c, k ∈ l → OccursBefore s (c ﹫ k) (c ﹫ l)) Set.univ := by
    infer_instance
  infer_instance

/-- The contraction is the inverse of the collapse of the order of the first occurrences -/
theorem contraction_eq (hs : IsFinSeqSeq s) :
    contraction s = (collapseOn (ctrRel s) (ctrSet s))⁻¹ := by
  have hc := isContraction_inv_collapseOn hs
  have hset : (𝒫 ((ω : M) ×ˢ ctrSet s) ∩₀ fun c ↦ IsContraction s c) =
      {(collapseOn (ctrRel s) (ctrSet s))⁻¹} := by
    ext d
    rw [mem_comprehension_iff, mem_singleton_iff]
    constructor
    · rintro ⟨-, hd⟩
      exact eq_inv_collapseOn_of_isContraction hs hd
    · rintro rfl
      refine ⟨?_, hc⟩
      rw [mem_powerset_iff]
      intro w hw
      obtain ⟨hcf, hdom, -, hran, -⟩ := hc
      obtain ⟨k, v, rfl⟩ := hcf.isRelation hw
      rw [pair_mem_sprod_iff]
      refine ⟨ordinal_omega.transitive _ hdom ((mem_dom_iff _ k).mpr ⟨v, hw⟩), ?_⟩
      rw [← hran]
      exact (mem_ran_iff _ v).mpr ⟨k, hw⟩
  rw [contraction, hset, sUnion_singleton]

/-- A finite sequence of finite sequences has a contraction -/
theorem isContraction_contraction (hs : IsFinSeqSeq s) : IsContraction s (contraction s) := by
  rw [contraction_eq hs]
  exact isContraction_inv_collapseOn hs

/-- The contraction is unique -/
theorem eq_contraction_of_isContraction (hs : IsFinSeqSeq s) (h : IsContraction s c) :
    c = contraction s := by
  rw [contraction_eq hs]
  exact eq_inv_collapseOn_of_isContraction hs h

theorem isFinSeqSeq_empty : IsFinSeqSeq (∅ : M) :=
  ⟨isFunction_empty, by rw [dom_empty]; exact empty_mem_omega, by simp⟩

/-- The contraction of the empty sequence is empty -/
theorem contraction_empty : contraction (∅ : M) = ∅ := by
  refine (eq_contraction_of_isContraction isFinSeqSeq_empty
    ⟨isFunction_empty, by rw [dom_empty]; exact empty_mem_omega, by simp, ?_, by simp⟩).symm
  ext x
  rw [mem_ctrSet_iff isFinSeqSeq_empty]
  simp

/-- The last index `⋃₀ dom s` of a sequence `s` on a positive natural number -/
noncomputable def lastIdx : ClassFunction M := fun s ↦ ⋃₀ dom s

/-- The last sequence of the sequence of sequences `s` -/
noncomputable def lastSeq : ClassFunction M := fun s ↦ s ﹫ lastIdx s

/-- The last entry of the last sequence of the sequence of sequences `s` -/
noncomputable def lastEntry : ClassFunction M := fun s ↦ lastSeq s ﹫ lastIdx (lastSeq s)

instance : (lastIdx : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq (ᵣ⋃₀ (ᵣ0 : L.RudimentaryTerm 1).dom) fun _ ↦ by
    simp [lastIdx]

instance : (lastSeq : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq ((ᵣ0 : L.RudimentaryTerm 1) ﹫ ᵣ⋃₀ (ᵣ0 : L.RudimentaryTerm 1).dom)
    fun _ ↦ by simp [lastSeq, lastIdx]

instance : (lastEntry : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq (((ᵣ0 : L.RudimentaryTerm 1) ﹫ ᵣ⋃₀ (ᵣ0 : L.RudimentaryTerm 1).dom) ﹫
    ᵣ⋃₀ ((ᵣ0 : L.RudimentaryTerm 1) ﹫ ᵣ⋃₀ (ᵣ0 : L.RudimentaryTerm 1).dom).dom)
    fun _ ↦ by simp [lastEntry, lastSeq, lastIdx]

/-- The sequence of sequences `s` ends with a new entry: its last sequence is nonempty and its last
entry occurs nowhere else -/
def EndsWithNew (s : M) : Prop :=
  lastIdx s ∈ dom s ∧ lastIdx (lastSeq s) ∈ dom (lastSeq s) ∧
    ∀ i ∈ dom s, ∀ j ∈ dom (s ﹫ i), (s ﹫ i) ﹫ j = lastEntry s →
      i = lastIdx s ∧ j = lastIdx (lastSeq s)

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ ∀ i ∈ dom (xs 0), ∀ j ∈ dom (xs 0 ﹫ i),
    (xs 0 ﹫ i) ﹫ j = xs 1 → i = xs 2 ∧ j = xs 3) Set.univ := by
  infer_instance

instance {n : ℕ} (a b c d : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    ∀ i ∈ dom (xs a), ∀ j ∈ dom (xs a ﹫ i), (xs a ﹫ i) ﹫ j = xs b → i = xs c ∧ j = xs d)
    Set.univ := by
  have h : (fun xs : Fin n → M ↦
      ∀ i ∈ dom (xs a), ∀ j ∈ dom (xs a ﹫ i), (xs a ﹫ i) ﹫ j = xs b → i = xs c ∧ j = xs d) =
      Multiclass.remap (fun ys : Fin 4 → M ↦ ∀ i ∈ dom (ys 0), ∀ j ∈ dom (ys 0 ﹫ i),
        (ys 0 ﹫ i) ﹫ j = ys 1 → i = ys 2 ∧ j = ys 3) ![a, b, c, d] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Class.Definable (fun s : M ↦ EndsWithNew s) Set.univ := by
  unfold EndsWithNew
  have : Class.Definable (fun s : M ↦ lastIdx s ∈ dom s) Set.univ := by
    infer_instance
  have : Class.Definable (fun s : M ↦ lastIdx (lastSeq s) ∈ dom (lastSeq s)) Set.univ := by
    infer_instance
  have : Class.Definable (fun s : M ↦ ∀ i ∈ dom s, ∀ j ∈ dom (s ﹫ i), (s ﹫ i) ﹫ j = lastEntry s →
      i = lastIdx s ∧ j = lastIdx (lastSeq s)) Set.univ := by
    have h : (fun s : M ↦ ∀ i ∈ dom s, ∀ j ∈ dom (s ﹫ i), (s ﹫ i) ﹫ j = lastEntry s →
        i = lastIdx s ∧ j = lastIdx (lastSeq s)) = fun s : M ↦ ∃ e L L', e = lastEntry s ∧
          L = lastIdx s ∧ L' = lastIdx (lastSeq s) ∧
            ∀ i ∈ dom s, ∀ j ∈ dom (s ﹫ i), (s ﹫ i) ﹫ j = e → i = L ∧ j = L' := by
      funext s
      apply propext
      constructor
      · intro h
        exact ⟨_, _, _, rfl, rfl, rfl, h⟩
      · rintro ⟨e, L, L', rfl, rfl, rfl, h⟩
        exact h
    rw [h]
    infer_instance
  infer_instance

/-- The contraction is preserved by an injective map of the entries -/
theorem isContraction_map {s s' c c' : M} (μ : M → M) (hs : IsFinSeqSeq s)
    (hs' : IsFinSeqSeq s') (hd : dom s' = dom s)
    (hdi : ∀ i ∈ dom s, dom (s' ﹫ i) = dom (s ﹫ i))
    (hv : ∀ i ∈ dom s, ∀ j ∈ dom (s ﹫ i), (s' ﹫ i) ﹫ j = μ ((s ﹫ i) ﹫ j))
    (hinj : ∀ x ∈ ctrSet s, ∀ y ∈ ctrSet s, μ x = μ y → x = y)
    (hc : IsContraction s c) (hc'f : IsFunction c') (hc'd : dom c' = dom c)
    (hc'v : ∀ k ∈ dom c, c' ﹫ k = μ (c ﹫ k)) : IsContraction s' c' := by
  obtain ⟨hcf, hcd, hcinj, hcran, hcob⟩ := hc
  have hcmem (k : M) (hk : k ∈ dom c) : c ﹫ k ∈ ctrSet s := by
    rw [← hcran]; exact (hcf.mem_ran_iff _).mpr ⟨k, hk, rfl⟩
  have hsmem (i : M) (hi : i ∈ dom s) (j : M) (hj : j ∈ dom (s ﹫ i)) : (s ﹫ i) ﹫ j ∈ ctrSet s :=
    (mem_ctrSet_iff hs).mpr ⟨i, hi, j, hj, rfl⟩
  refine ⟨hc'f, by rw [hc'd]; exact hcd, fun k hk l hl h ↦ ?_, ?_, fun k hk l hl hkl ↦ ?_⟩
  · rw [hc'd] at hk hl
    rw [hc'v k hk, hc'v l hl] at h
    exact hcinj k hk l hl (hinj _ (hcmem k hk) _ (hcmem l hl) h)
  · ext y
    rw [hc'f.mem_ran_iff, mem_ctrSet_iff hs']
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [hc'd] at hk
      have h := hcmem k hk
      rw [mem_ctrSet_iff hs] at h
      obtain ⟨i, hi, j, hj, hij⟩ := h
      refine ⟨i, by rw [hd]; exact hi, j, by rw [hdi i hi]; exact hj, ?_⟩
      rw [hv i hi j hj, hij, hc'v k hk]
    · rintro ⟨i, hi, j, hj, rfl⟩
      rw [hd] at hi
      rw [hdi i hi] at hj
      have h := hsmem i hi j hj
      rw [← hcran, hcf.mem_ran_iff] at h
      obtain ⟨k, hk, hkv⟩ := h
      exact ⟨k, by rw [hc'd]; exact hk, by rw [hc'v k hk, hkv, hv i hi j hj]⟩
  · rw [hc'd] at hk hl
    obtain ⟨i, hi, j, hj, hij, hpre⟩ := hcob k hk l hl hkl
    refine ⟨i, by rw [hd]; exact hi, j, by rw [hdi i hi]; exact hj,
      by rw [hv i hi j hj, hij, hc'v k hk], fun i' hi' j' hj' h ↦ ?_⟩
    rw [hd] at hi'
    rw [hdi i' hi'] at hj'
    rw [hv i' hi' j' hj', hc'v l hl] at h
    exact hpre i' hi' j' hj' (hinj _ (hsmem i' hi' j' hj') _ (hcmem l hl) h)

end Contraction

section UociEmb

/-! ### Embeddings of an element of `stduoci_1` into a pair `(Q, V)` -/

/-- The signature in `X` of the image under `σ` of the `i`-th node of the signature of `U` -/
noncomputable def embTpSigEntry (Q X U σ i : M) : M := tpSig Q X ((σ ﹫ siglvl U i) ﹫ sigdcn U i)

/-- The signatures in `X` of the images under `σ` of the nodes of the signature of `U` -/
noncomputable def embTpSigs (Q X U σ : M) : M := (fun i ↦ embTpSigEntry Q X U σ i) ↾₀ dom (sig U)

/-- The `ucflvldcn` in `X` of the image under `σ` of the entry `e = (l, w)`: the level-`0` one if
`l = 0`, and otherwise that of the image node `σ(l)(w)` in `(Q ⊗ X)(1)` -/
noncomputable def embUcfAux (Q X σ e : M) : M :=
  if lvl e = ∅ then tpUcfZero X else tpUcf Q X ((σ ﹫ lvl e) ﹫ dcn e)

/-- The `ucflvldcn` in `X` of the image under `σ` of the `ucf` of `U`: the level-`0` one if
`ucfOrLast U` is at level `0`, and otherwise that of the image node in `(Q ⊗ X)(1)` -/
noncomputable def embUcf (Q X U σ : M) : M := embUcfAux Q X σ (ucfOrLast U)

/-- `σ` is an embedding of `U ∈ stduoci_1` into the pair `(Q, V)`, `Q ∈ aotci_2`,
`V ∈ stduoci_1`: an embedding of `U_aoc` into `Q ⊗ V_aoc` such that
(a) the contraction of the signatures of the images of the nodes of `U_sig` is `V_sig`;
(b) `V` is of type `ct` if and only if `U` is, the image of the last node of `U_sig` is of type
`ct`, and the last entry of the sequence of signatures is its only occurrence (the newest entry of
`V_sig` first appears there);
(c) the `ucf` of `V` is the image `embUcf` of that of `U`, with `ucfdr = lf`. -/
def IsUociEmb (Q U V σ : M) : Prop :=
  σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc U) (tensorProdATwoAOne Q (aoc V)) ∧
  contraction (embTpSigs Q (aoc V) U σ) = sig V ∧
  (ctp V = ct ↔ ctp U = ct ∧
    TpCt Q (aoc V) ((σ ﹫ siglvl U (⋃₀ dom (sig U))) ﹫ sigdcn U (⋃₀ dom (sig U))) ∧
      EndsWithNew (embTpSigs Q (aoc V) U σ)) ∧
  (((3 : ℕ) : M) ∈ dom V → ucflvldcn V = embUcf Q (aoc V) U σ ∧ ucfdr V = lf)

end UociEmb

section Definability

/-! ### Definability of the signatures, types and `ucf`'s of the nodes, and of the contraction

Functions of several arguments are shown definable as functions of the tuple of their arguments,
coded by nested pairs. -/

theorem mem_tpOrig_iff {X l y z : M} : z ∈ tpOrig X l y ↔ ∃ w ∈ ndOf (X ﹫ l),
    (l = ∅ ∨ !(uc w, !(lbl w, tensorProdAZeroAZero (aoc (uc w)) trvAZero)) = y) ∧ z ∈ w := by
  have hres : IsSetRestrictedTo
      (fun p ↦ !(uc p, !(lbl p, tensorProdAZeroAZero (aoc (uc p)) trvAZero))) (ndOf (X ﹫ l)) :=
    isSetRestrictedTo_of_definable _
  rw [tpOrig, mem_sUnion_iff]
  constructor
  · rintro ⟨w, hw, hz⟩
    rw [mem_comprehension_iff] at hw
    obtain ⟨hw, h⟩ := hw
    refine ⟨w, hw, ?_, hz⟩
    rwa [tensorProdOneAZeroRelabel, val_toSetRestrictedTo hres hw] at h
  · rintro ⟨w, hw, h, hz⟩
    refine ⟨w, ?_, hz⟩
    rw [mem_comprehension_iff, tensorProdOneAZeroRelabel, val_toSetRestrictedTo hres hw]
    exact ⟨hw, h⟩

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ ∃ w ∈ ndOf (xs 0 ﹫ xs 1),
    (xs 1 = ∅ ∨ !(uc w, !(lbl w, tensorProdAZeroAZero (aoc (uc w)) trvAZero)) = xs 2) ∧
      xs 3 ∈ w) Set.univ := by
  obtain ⟨G, hG⟩ : ∃ G : ClassFunction M,
      G = fun w ↦ !(uc w, !(lbl w, tensorProdAZeroAZero (aoc (uc w)) trvAZero)) := ⟨_, rfl⟩
  have : G.Sigma 1 Set.univ := by
    rw [hG]
    infer_instance
  have h : (fun xs : Fin 4 → M ↦ ∃ w ∈ ndOf (xs 0 ﹫ xs 1),
      (xs 1 = ∅ ∨ !(uc w, !(lbl w, tensorProdAZeroAZero (aoc (uc w)) trvAZero)) = xs 2) ∧
        xs 3 ∈ w) = fun xs : Fin 4 → M ↦
          ∃ w ∈ ndOf (xs 0 ﹫ xs 1), (xs 1 = ∅ ∨ G w = xs 2) ∧ xs 3 ∈ w := by
    rw [hG]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    ∃ w ∈ ndOf (xs i ﹫ xs j),
      (xs j = ∅ ∨ !(uc w, !(lbl w, tensorProdAZeroAZero (aoc (uc w)) trvAZero)) = xs k) ∧
        xs l ∈ w) Set.univ := by
  have h : (fun xs : Fin n → M ↦ ∃ w ∈ ndOf (xs i ﹫ xs j),
      (xs j = ∅ ∨ !(uc w, !(lbl w, tensorProdAZeroAZero (aoc (uc w)) trvAZero)) = xs k) ∧
        xs l ∈ w) = Multiclass.remap (fun ys : Fin 4 → M ↦ ∃ w ∈ ndOf (ys 0 ﹫ ys 1),
      (ys 1 = ∅ ∨ !(uc w, !(lbl w, tensorProdAZeroAZero (aoc (uc w)) trvAZero)) = ys 2) ∧
        ys 3 ∈ w) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : ClassFunction.Definable
    (fun a : M ↦ tpOrig (left a) (left (right a)) (right (right a))) Set.univ :=
  .of_mem_iff (R := fun a z ↦ ∃ X l y, X = left a ∧ l = left (right a) ∧ y = right (right a) ∧
    ∃ w ∈ ndOf (X ﹫ l),
      (l = ∅ ∨ !(uc w, !(lbl w, tensorProdAZeroAZero (aoc (uc w)) trvAZero)) = y) ∧ z ∈ w)
    fun a z ↦ by
      rw [mem_tpOrig_iff]
      constructor
      · intro h
        exact ⟨_, _, _, rfl, rfl, rfl, h⟩
      · rintro ⟨X, l, y, rfl, rfl, rfl, h⟩
        exact h

instance : Class.Definable
    (fun a : M ↦ IsTpTwo (left a) (left (right a)) (right (right a))) Set.univ := by
  unfold IsTpTwo
  have : ClassFunction.Definable
      (fun a : M ↦ tensorProdTwoAOneNds (left a ﹫ 2) (left (right a))) Set.univ := by
    have h := ClassFunction.Definable.comp₁
      (H := fun z : M ↦ tensorProdTwoAOneNds (left z) (right z))
      (F := fun a : M ↦ !(left a ﹫ 2, left (right a)))
    simp only [left_orderedPair, right_orderedPair] at h
    exact h
  infer_instance

instance : ClassFunction.Definable
    (fun a : M ↦ tpSigDom (left a) (left (right a)) (right (right a))) Set.univ := by
  unfold tpSigDom
  exact ClassFunction.definable_ite
    (P := fun a ↦ IsTpTwo (left a) (left (right a)) (right (right a)))
    (F := fun a ↦ dom (sig (nodeU (right (right a)))))
    (G := fun _ ↦ ∅)

instance : Class.Definable
    (fun a : M ↦ TpCt (left a) (left (right a)) (right (right a))) Set.univ := by
  unfold TpCt
  infer_instance

instance : ClassFunction.Definable (fun U : M ↦ ucfOrLast U) Set.univ := by
  unfold ucfOrLast
  exact ClassFunction.definable_ite (P := fun U ↦ ((3 : ℕ) : M) ∈ dom U) (F := fun U ↦ ucflvldcn U)
    (G := fun U ↦ sig U ﹫ ⋃₀ dom (sig U))

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ tpOrig (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ tpOrig (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∀ z, z ∈ xs 3 ↔ ∃ w ∈ ndOf (xs 0 ﹫ xs 1),
        (xs 1 = ∅ ∨ !(uc w, !(lbl w, tensorProdAZeroAZero (aoc (uc w)) trvAZero)) = xs 2) ∧
          z ∈ w := by
    funext xs
    apply propext
    constructor
    · intro h z
      rw [← h, mem_tpOrig_iff]
    · intro h
      ext z
      rw [mem_tpOrig_iff, h z]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ tpOrig (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tpOrig (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ tpOrig (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ tpSigEntryAux (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) Set.univ := by
  have h : (fun xs : Fin 5 → M ↦ tpSigEntryAux (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) =
      fun xs : Fin 5 → M ↦ ∃ l y o, l = siglvl (xs 1) (xs 3) ∧
        y = (xs 2 ﹫ l) ﹫ sigdcn (xs 1) (xs 3) ∧ tpOrig (xs 0) l y = o ∧ !(l, o) = xs 4 := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, _, rfl, rfl, rfl, h⟩
    · rintro ⟨l, y, o, rfl, rfl, rfl, h⟩
      exact h
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ tpSigEntryAux (xs i) (xs j) (xs k) (xs l) = xs m) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tpSigEntryAux (xs i) (xs j) (xs k) (xs l) = xs m) =
      Multiclass.remap (fun ys : Fin 5 → M ↦ tpSigEntryAux (ys 0) (ys 1) (ys 2) (ys 3) = ys 4)
        ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ tpSigEntry (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ tpSigEntry (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∃ U H, U = nodeU (xs 1) ∧ H = nodeH (xs 1) ∧ tpSigEntryAux (xs 0) U H (xs 2) = xs 3 := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, rfl, rfl, h⟩
    · rintro ⟨U, H, rfl, rfl, h⟩
      exact h
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ tpSigEntry (xs i) (xs j) (xs k) = xs l)
      Set.univ := by
  have h : (fun xs : Fin n → M ↦ tpSigEntry (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ tpSigEntry (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : ClassFunction.Definable
    (fun a : M ↦ tpSig (left a) (left (right a)) (right (right a))) Set.univ := by
  unfold tpSig
  have hG : Multiclass.Definable (fun xs : Fin 3 → M ↦
      (fun a i ↦ tpSigEntry (left (right a)) (right (right a)) i) (xs 0) (xs 1) = xs 2)
      Set.univ := by
    have h : (fun xs : Fin 3 → M ↦
        (fun a i ↦ tpSigEntry (left (right a)) (right (right a)) i) (xs 0) (xs 1) = xs 2) =
        fun xs : Fin 3 → M ↦ ∃ X x, X = left (right (xs 0)) ∧ x = right (right (xs 0)) ∧
          tpSigEntry X x (xs 1) = xs 2 := by
      funext xs
      apply propext
      constructor
      · intro h
        exact ⟨_, _, rfl, rfl, h⟩
      · rintro ⟨X, x, rfl, rfl, h⟩
        exact h
    rw [h]
    infer_instance
  exact ClassFunction.Definable.toSetRestrictedTo
    (D := fun a ↦ tpSigDom (left a) (left (right a)) (right (right a)))

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ tpUcfAux (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ tpUcfAux (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∃ l y o, l = lvl (xs 1) ∧ y = (xs 2 ﹫ l) ﹫ dcn (xs 1) ∧ tpOrig (xs 0) l y = o ∧
        !(l, o) = xs 3 := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, _, rfl, rfl, rfl, h⟩
    · rintro ⟨l, y, o, rfl, rfl, rfl, h⟩
      exact h
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ tpUcfAux (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tpUcfAux (xs i) (xs j) (xs k) = xs l) =
      Multiclass.remap (fun ys : Fin 4 → M ↦ tpUcfAux (ys 0) (ys 1) (ys 2) = ys 3)
        ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ tpUcfTwo (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ tpUcfTwo (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ U e H, U = nodeU (xs 1) ∧ ucfOrLast U = e ∧ H = nodeH (xs 1) ∧
        tpUcfAux (xs 0) e H = xs 2 := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, _, rfl, rfl, rfl, h⟩
    · rintro ⟨U, e, H, rfl, rfl, rfl, h⟩
      exact h
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ tpUcfTwo (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tpUcfTwo (xs i) (xs j) = xs k) =
      Multiclass.remap (fun ys : Fin 3 → M ↦ tpUcfTwo (ys 0) (ys 1) = ys 2)
        ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : ClassFunction.Sigma (fun X : M ↦ tpUcfZero X) 1 Set.univ := by
  unfold tpUcfZero
  infer_instance

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ IsTpTwo (xs 0) (xs 1) (xs 2)) Set.univ := by
  obtain ⟨T, hT⟩ : ∃ T : Class M, T = fun a ↦ IsTpTwo (left a) (left (right a)) (right (right a)) :=
    ⟨_, rfl⟩
  have : T.Definable Set.univ := by
    rw [hT]
    infer_instance
  have h : (fun xs : Fin 3 → M ↦ IsTpTwo (xs 0) (xs 1) (xs 2)) = fun xs : Fin 3 → M ↦
      ∃ a, a = !(xs 0, !(xs 1, xs 2)) ∧ T a := by
    funext xs
    simp [hT, left_orderedPair, right_orderedPair]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ IsTpTwo (xs i) (xs j) (xs k)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsTpTwo (xs i) (xs j) (xs k)) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ IsTpTwo (ys 0) (ys 1) (ys 2)) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ tpUcf (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ tpUcf (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      (IsTpTwo (xs 0) (xs 1) (xs 2) ∧ tpUcfTwo (xs 1) (xs 2) = xs 3) ∨
        (¬IsTpTwo (xs 0) (xs 1) (xs 2) ∧ tpUcfZero (xs 1) = xs 3) := by
    funext xs
    by_cases hp : IsTpTwo (xs 0) (xs 1) (xs 2) <;> simp [tpUcf, hp]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ tpUcf (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tpUcf (xs i) (xs j) (xs k) = xs l) =
      Multiclass.remap (fun ys : Fin 4 → M ↦ tpUcf (ys 0) (ys 1) (ys 2) = ys 3)
        ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ embUcfAux (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) Set.univ := by
  have h : (fun xs : Fin 5 → M ↦ embUcfAux (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) =
      fun xs : Fin 5 → M ↦ (lvl (xs 3) = ∅ ∧ tpUcfZero (xs 1) = xs 4) ∨
        (lvl (xs 3) ≠ ∅ ∧ ∃ y, y = (xs 2 ﹫ lvl (xs 3)) ﹫ dcn (xs 3) ∧
          tpUcf (xs 0) (xs 1) y = xs 4) := by
    funext xs
    by_cases hp : lvl (xs 3) = ∅ <;> simp [embUcfAux, hp]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ embUcfAux (xs i) (xs j) (xs k) (xs l) = xs m) Set.univ := by
  have h : (fun xs : Fin n → M ↦ embUcfAux (xs i) (xs j) (xs k) (xs l) = xs m) =
      Multiclass.remap (fun ys : Fin 5 → M ↦ embUcfAux (ys 0) (ys 1) (ys 2) (ys 3) = ys 4)
        ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ embUcf (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) Set.univ := by
  have h : (fun xs : Fin 5 → M ↦ embUcf (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) =
      fun xs : Fin 5 → M ↦ ∃ e, ucfOrLast (xs 2) = e ∧ embUcfAux (xs 0) (xs 1) (xs 3) e = xs 4 := by
    funext xs
    simp [embUcf]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ embUcf (xs i) (xs j) (xs k) (xs l) = xs m) Set.univ := by
  have h : (fun xs : Fin n → M ↦ embUcf (xs i) (xs j) (xs k) (xs l) = xs m) =
      Multiclass.remap (fun ys : Fin 5 → M ↦ embUcf (ys 0) (ys 1) (ys 2) (ys 3) = ys 4)
        ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ tpSig (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  obtain ⟨T, hT⟩ : ∃ T : ClassFunction M,
      T = fun a ↦ tpSig (left a) (left (right a)) (right (right a)) := ⟨_, rfl⟩
  have : T.Definable Set.univ := by
    rw [hT]
    infer_instance
  have h : (fun xs : Fin 4 → M ↦ tpSig (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∃ a, a = !(xs 0, !(xs 1, xs 2)) ∧ T a = xs 3 := by
    funext xs
    simp [hT, left_orderedPair, right_orderedPair]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ tpSig (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tpSig (xs i) (xs j) (xs k) = xs l) =
      Multiclass.remap (fun ys : Fin 4 → M ↦ tpSig (ys 0) (ys 1) (ys 2) = ys 3)
        ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable
    (fun xs : Fin 6 → M ↦ embTpSigEntry (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) = xs 5) Set.univ := by
  have h : (fun xs : Fin 6 → M ↦ embTpSigEntry (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) = xs 5) =
      fun xs : Fin 6 → M ↦ ∃ y, y = (xs 3 ﹫ siglvl (xs 2) (xs 4)) ﹫ sigdcn (xs 2) (xs 4) ∧
        tpSig (xs 0) (xs 1) y = xs 5 := by
    funext xs
    simp [embTpSigEntry]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m q : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ embTpSigEntry (xs i) (xs j) (xs k) (xs l) (xs m) = xs q) Set.univ := by
  have h : (fun xs : Fin n → M ↦ embTpSigEntry (xs i) (xs j) (xs k) (xs l) (xs m) = xs q) =
      Multiclass.remap
        (fun ys : Fin 6 → M ↦ embTpSigEntry (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) = ys 5)
        ![i, j, k, l, m, q] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `embTpSigEntry` with the pair `d = (U, σ)` -/
private noncomputable def embTpSigEntryR (Q X d i : M) : M :=
  embTpSigEntry Q X (left d) (right d) i

/-- `embTpSigEntry` with the pairs `c = (Q, X)` and `d = (U, σ)` -/
private noncomputable def embTpSigEntryP (c d i : M) : M := embTpSigEntryR (left c) (right c) d i

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ embTpSigEntryR (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) Set.univ := by
  have h : (fun xs : Fin 5 → M ↦ embTpSigEntryR (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) =
      fun xs : Fin 5 → M ↦ ∃ U σ, U = left (xs 2) ∧ σ = right (xs 2) ∧
        embTpSigEntry (xs 0) (xs 1) U σ (xs 3) = xs 4 := by
    funext xs
    simp [embTpSigEntryR]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ embTpSigEntryR (xs i) (xs j) (xs k) (xs l) = xs m) Set.univ := by
  have h : (fun xs : Fin n → M ↦ embTpSigEntryR (xs i) (xs j) (xs k) (xs l) = xs m) =
      Multiclass.remap (fun ys : Fin 5 → M ↦ embTpSigEntryR (ys 0) (ys 1) (ys 2) (ys 3) = ys 4)
        ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable
    (fun xs : Fin 4 → M ↦ embTpSigEntryP (xs 0) (xs 1) (xs 2) = xs 3) Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ embTpSigEntryP (xs 0) (xs 1) (xs 2) = xs 3) =
      fun xs : Fin 4 → M ↦ ∃ Q X, Q = left (xs 0) ∧ X = right (xs 0) ∧
        embTpSigEntryR Q X (xs 1) (xs 2) = xs 3 := by
    funext xs
    simp [embTpSigEntryP]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ embTpSigEntryP (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ embTpSigEntryP (xs i) (xs j) (xs k) = xs l) =
      Multiclass.remap (fun ys : Fin 4 → M ↦ embTpSigEntryP (ys 0) (ys 1) (ys 2) = ys 3)
        ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : ClassFunction.Definable (fun b : M ↦
    embTpSigs (left (left b)) (right (left b)) (left (right b)) (right (right b))) Set.univ := by
  have hG : Multiclass.Definable (fun xs : Fin 3 → M ↦
      (fun b i ↦ embTpSigEntryP (left b) (right b) i) (xs 0) (xs 1) = xs 2) Set.univ := by
    have h : (fun xs : Fin 3 → M ↦
        (fun b i ↦ embTpSigEntryP (left b) (right b) i) (xs 0) (xs 1) = xs 2) =
        fun xs : Fin 3 → M ↦ ∃ c d, c = left (xs 0) ∧ d = right (xs 0) ∧
          embTpSigEntryP c d (xs 1) = xs 2 := by
      funext xs
      apply propext
      constructor
      · intro h
        exact ⟨_, _, rfl, rfl, h⟩
      · rintro ⟨c, d, rfl, rfl, h⟩
        exact h
    rw [h]
    infer_instance
  exact ClassFunction.Definable.toSetRestrictedTo
    (G := fun b i ↦ embTpSigEntryP (left b) (right b) i)
    (D := fun b ↦ dom (sig (left (right b))))

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ embTpSigs (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) Set.univ := by
  obtain ⟨T, hT⟩ : ∃ T : ClassFunction M, T = fun b ↦
      embTpSigs (left (left b)) (right (left b)) (left (right b)) (right (right b)) := ⟨_, rfl⟩
  have : T.Definable Set.univ := by
    rw [hT]
    infer_instance
  have h : (fun xs : Fin 5 → M ↦ embTpSigs (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) =
      fun xs : Fin 5 → M ↦ ∃ b, b = !(!(xs 0, xs 1), !(xs 2, xs 3)) ∧ T b = xs 4 := by
    funext xs
    simp [hT, left_orderedPair, right_orderedPair]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ embTpSigs (xs i) (xs j) (xs k) (xs l) = xs m) Set.univ := by
  have h : (fun xs : Fin n → M ↦ embTpSigs (xs i) (xs j) (xs k) (xs l) = xs m) =
      Multiclass.remap (fun ys : Fin 5 → M ↦ embTpSigs (ys 0) (ys 1) (ys 2) (ys 3) = ys 4)
        ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : ClassFunction.Definable (fun s : M ↦ ctrSet s) Set.univ := by
  unfold ctrSet
  have : ClassFunction.Definable (fun s : M ↦ (fun f ↦ ran f) ↾₀ ran s) Set.univ :=
    ClassFunction.Definable.toSetRestrictedTo (G := fun _ f ↦ ran f) (D := ran)
  have : ClassFunction.Definable (fun s : M ↦ ran ((fun f ↦ ran f) ↾₀ ran s)) Set.univ :=
    ClassFunction.Definable.comp₁ (H := ran)
  exact ClassFunction.Definable.comp₁ (H := fun x : M ↦ ⋃₀ x)
    (F := fun s : M ↦ ran ((fun f ↦ ran f) ↾₀ ran s))

instance : Multiclass.Definable (fun xs : Fin 2 → M ↦ IsContraction (xs 0) (xs 1)) Set.univ := by
  unfold IsContraction
  have : Multiclass.Definable (fun xs : Fin 2 → M ↦
      ∀ k ∈ dom (xs 1), ∀ l ∈ dom (xs 1), xs 1 ﹫ k = xs 1 ﹫ l → k = l) Set.univ := by
    infer_instance
  have : Multiclass.Definable (fun xs : Fin 2 → M ↦ ran (xs 1) = ctrSet (xs 0)) Set.univ := by
    infer_instance
  have : Multiclass.Definable (fun xs : Fin 2 → M ↦ ∀ k ∈ dom (xs 1), ∀ l ∈ dom (xs 1), k ∈ l →
      OccursBefore (xs 0) (xs 1 ﹫ k) (xs 1 ﹫ l)) Set.univ := by
    infer_instance
  infer_instance

theorem mem_contraction_iff {s z : M} : z ∈ contraction s ↔
    ∃ c, c ⊆ (ω : M) ×ˢ ctrSet s ∧ IsContraction s c ∧ z ∈ c := by
  rw [contraction, mem_sUnion_iff]
  simp only [mem_comprehension_iff, mem_powerset_iff]
  constructor
  · rintro ⟨c, ⟨hc, h⟩, hz⟩
    exact ⟨c, hc, h, hz⟩
  · rintro ⟨c, hc, h, hz⟩
    exact ⟨c, ⟨hc, h⟩, hz⟩

instance : ClassFunction.Definable (fun s : M ↦ contraction s) Set.univ :=
  .of_mem_iff (R := fun s z ↦ ∃ c Y, Y = ctrSet s ∧ c ⊆ (ω : M) ×ˢ Y ∧ IsContraction s c ∧
    z ∈ c) fun s z ↦ by
    rw [mem_contraction_iff]
    constructor
    · rintro ⟨c, hc, h, hz⟩
      exact ⟨c, _, rfl, hc, h, hz⟩
    · rintro ⟨c, Y, rfl, hc, h, hz⟩
      exact ⟨c, hc, h, hz⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ TpCt (xs 0) (xs 1) (xs 2)) Set.univ := by
  unfold TpCt
  infer_instance

instance {n : ℕ} (i j k : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ TpCt (xs i) (xs j) (xs k)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ TpCt (xs i) (xs j) (xs k)) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ TpCt (ys 0) (ys 1) (ys 2)) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The target array `Q ⊗ V_aoc` of the embeddings into `(Q, V)` -/
noncomputable def uociEmbTgt (Q V : M) : M := tensorProdATwoAOne Q (aoc V)

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ uociEmbTgt (xs 0) (xs 1) = xs 2)
    Set.univ := by
  obtain ⟨T, hT⟩ : ∃ T : ClassFunction M,
      T = fun z ↦ tensorProdATwoAOne (left z) (right z) := ⟨_, rfl⟩
  have : T.Definable Set.univ := by
    rw [hT]
    infer_instance
  have h : (fun xs : Fin 3 → M ↦ uociEmbTgt (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ z, z = !(xs 0, aoc (xs 1)) ∧ T z = xs 2 := by
    funext xs
    simp [hT, uociEmbTgt, left_orderedPair, right_orderedPair]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ uociEmbTgt (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ uociEmbTgt (xs i) (xs j) = xs k) =
      Multiclass.remap (fun ys : Fin 3 → M ↦ uociEmbTgt (ys 0) (ys 1) = ys 2)
        ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 6 → M ↦
    (ctp (xs 2) = ct ↔ ctp (xs 1) = ct ∧ TpCt (xs 0) (xs 3) (xs 4) ∧ EndsWithNew (xs 5)))
    Set.univ := by
  infer_instance

instance {n : ℕ} (i j k l m q : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    (ctp (xs k) = ct ↔ ctp (xs j) = ct ∧ TpCt (xs i) (xs l) (xs m) ∧ EndsWithNew (xs q)))
    Set.univ := by
  have h : (fun xs : Fin n → M ↦
      (ctp (xs k) = ct ↔ ctp (xs j) = ct ∧ TpCt (xs i) (xs l) (xs m) ∧ EndsWithNew (xs q))) =
      Multiclass.remap (fun ys : Fin 6 → M ↦ (ctp (ys 2) = ct ↔ ctp (ys 1) = ct ∧
        TpCt (ys 0) (ys 3) (ys 4) ∧ EndsWithNew (ys 5))) ![i, j, k, l, m, q] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The image under `σ` of the last node of the signature of `U` -/
private noncomputable def lastImg (U σ : M) : M :=
  (σ ﹫ siglvl U (⋃₀ dom (sig U))) ﹫ sigdcn U (⋃₀ dom (sig U))

instance : MulticlassFunction.Sigma (fun ys : Fin 2 → M ↦ lastImg (ys 0) (ys 1)) 1 Set.univ := by
  unfold lastImg
  have : MulticlassFunction.Sigma
      (fun ys : Fin 2 → M ↦ siglvl (ys 0) (⋃₀ dom (sig (ys 0)))) 1 Set.univ := by
    infer_instance
  have : MulticlassFunction.Sigma
      (fun ys : Fin 2 → M ↦ sigdcn (ys 0) (⋃₀ dom (sig (ys 0)))) 1 Set.univ := by
    infer_instance
  have : MulticlassFunction.Sigma
      (fun ys : Fin 2 → M ↦ ys 1 ﹫ siglvl (ys 0) (⋃₀ dom (sig (ys 0)))) 1 Set.univ := by
    infer_instance
  infer_instance

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ IsUociEmb (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  unfold IsUociEmb
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦ xs 3 ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (xs 1))
      (tensorProdATwoAOne (xs 0) (aoc (xs 2)))) Set.univ := by
    have h : (fun xs : Fin 4 → M ↦ xs 3 ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (xs 1))
        (tensorProdATwoAOne (xs 0) (aoc (xs 2)))) = fun xs : Fin 4 → M ↦ ∃ n W T,
          n = ((1 : ℕ) : M) ∧ W = aoc (xs 1) ∧ uociEmbTgt (xs 0) (xs 2) = T ∧
            xs 3 ∈ aotciEmbSet n W T := by
      funext xs
      apply propext
      constructor
      · intro h
        exact ⟨_, _, _, rfl, rfl, rfl, h⟩
      · rintro ⟨n, W, T, rfl, rfl, rfl, h⟩
        exact h
    rw [h]
    infer_instance
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦
      contraction (embTpSigs (xs 0) (aoc (xs 2)) (xs 1) (xs 3)) = sig (xs 2)) Set.univ := by
    have h : (fun xs : Fin 4 → M ↦
        contraction (embTpSigs (xs 0) (aoc (xs 2)) (xs 1) (xs 3)) = sig (xs 2)) =
        fun xs : Fin 4 → M ↦ ∃ X t, X = aoc (xs 2) ∧ embTpSigs (xs 0) X (xs 1) (xs 3) = t ∧
          contraction t = sig (xs 2) := by
      funext xs
      apply propext
      constructor
      · intro h
        exact ⟨_, _, rfl, rfl, h⟩
      · rintro ⟨X, t, rfl, rfl, h⟩
        exact h
    rw [h]
    infer_instance
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦ (ctp (xs 2) = ct ↔ ctp (xs 1) = ct ∧
      TpCt (xs 0) (aoc (xs 2)) ((xs 3 ﹫ siglvl (xs 1) (⋃₀ dom (sig (xs 1)))) ﹫
        sigdcn (xs 1) (⋃₀ dom (sig (xs 1)))) ∧
      EndsWithNew (embTpSigs (xs 0) (aoc (xs 2)) (xs 1) (xs 3)))) Set.univ := by
    have h : (fun xs : Fin 4 → M ↦ (ctp (xs 2) = ct ↔ ctp (xs 1) = ct ∧
        TpCt (xs 0) (aoc (xs 2)) ((xs 3 ﹫ siglvl (xs 1) (⋃₀ dom (sig (xs 1)))) ﹫
          sigdcn (xs 1) (⋃₀ dom (sig (xs 1)))) ∧
        EndsWithNew (embTpSigs (xs 0) (aoc (xs 2)) (xs 1) (xs 3)))) = fun xs : Fin 4 → M ↦
          ∃ X y s, (X = aoc (xs 2) ∧ y = lastImg (xs 1) (xs 3) ∧
            embTpSigs (xs 0) X (xs 1) (xs 3) = s) ∧
            (ctp (xs 2) = ct ↔ ctp (xs 1) = ct ∧ TpCt (xs 0) X y ∧ EndsWithNew s) := by
      funext xs
      apply propext
      constructor
      · intro h
        exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, h⟩
      · rintro ⟨X, y, s, ⟨rfl, rfl, rfl⟩, h⟩
        exact h
    rw [h]
    infer_instance
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦ (((3 : ℕ) : M) ∈ dom (xs 2) →
      ucflvldcn (xs 2) = embUcf (xs 0) (aoc (xs 2)) (xs 1) (xs 3) ∧ ucfdr (xs 2) = lf))
      Set.univ := by
    have h : (fun xs : Fin 4 → M ↦ (((3 : ℕ) : M) ∈ dom (xs 2) →
        ucflvldcn (xs 2) = embUcf (xs 0) (aoc (xs 2)) (xs 1) (xs 3) ∧ ucfdr (xs 2) = lf)) =
        fun xs : Fin 4 → M ↦ ∃ X e, X = aoc (xs 2) ∧ embUcf (xs 0) X (xs 1) (xs 3) = e ∧
          (((3 : ℕ) : M) ∈ dom (xs 2) → ucflvldcn (xs 2) = e ∧ ucfdr (xs 2) = lf) := by
      funext xs
      apply propext
      constructor
      · intro h
        exact ⟨_, _, rfl, rfl, h⟩
      · rintro ⟨X, e, rfl, rfl, h⟩
        exact h
    rw [h]
    infer_instance
  infer_instance
/-! #### Definability of the initial segments -/

instance : MulticlassFunction.Sigma (fun ys : Fin 3 → M ↦ ciTriple (ys 0) (ys 1) (ys 2)) 1
    Set.univ := by
  unfold ciTriple; infer_instance

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ ys 0 ↾↾ ys 1) Set.univ :=
  MulticlassFunction.deltaZero_of_eq RudimentaryTerm.restrict₂₀ fun ys ↦ by
    rw [RudimentaryTerm.realize_restrict₂₀]

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ rtLosSLOT (xs 0) (xs 1) = xs 2)
    Set.univ :=
  (inferInstance : MulticlassFunction.Definable (fun ys : Fin 2 → M ↦ rtLosSLOT (ys 0) (ys 1))
    Set.univ).1

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ rtLosSLOT (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ rtLosSLOT (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ rtLosSLOT (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ iniSegNds (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ iniSegNds (xs 0) (xs 1) = xs 2) = fun xs ↦
      (∀ r ∈ xs 2, ∃ i ∈ xs 1, sigdcn (xs 0) i = r) ∧ ∀ i ∈ xs 1, sigdcn (xs 0) i ∈ xs 2 := by
    funext xs
    apply propext
    constructor
    · intro h
      rw [← h]
      exact ⟨fun r hr ↦ mem_iniSegNds_iff.mp hr, fun i hi ↦ mem_iniSegNds_iff.mpr ⟨i, hi, rfl⟩⟩
    · rintro ⟨h₁, h₂⟩
      ext r
      rw [mem_iniSegNds_iff]
      refine ⟨?_, fun h ↦ h₁ r h⟩
      rintro ⟨i, hi, rfl⟩
      exact h₂ i hi
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ iniSegNds (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ iniSegNds (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ iniSegNds (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : MulticlassFunction.Sigma (fun ys : Fin 1 → M ↦ iniSegOdr (ys 0)) 1 Set.univ := by
  unfold iniSegOdr; infer_instance

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ rtLosSLOT trvAZero
    !(iniSegNds (xs 0) (xs 1), iniSegOdr (xs 0) ↾↾ iniSegNds (xs 0) (xs 1)) = xs 2) Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ rtLosSLOT trvAZero
      !(iniSegNds (xs 0) (xs 1), iniSegOdr (xs 0) ↾↾ iniSegNds (xs 0) (xs 1)) = xs 2) = fun xs ↦
      ∃ B : M, (∃ N O : M, iniSegNds (xs 0) (xs 1) = N ∧ iniSegOdr (xs 0) = O ∧ B = !(N, O ↾↾ N)) ∧
        ∃ D : M, D = trvAZero ∧ rtLosSLOT D B = xs 2 := by
    funext xs
    simp
  rw [h]
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦ ∃ N O : M, iniSegNds (xs 1) (xs 2) = N ∧
      iniSegOdr (xs 1) = O ∧ xs 0 = !(N, O ↾↾ N)) Set.univ := by
    infer_instance
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦ rtLosSLOT trvAZero
    !(iniSegNds (xs i) (xs j), iniSegOdr (xs i) ↾↾ iniSegNds (xs i) (xs j)) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ rtLosSLOT trvAZero
      !(iniSegNds (xs i) (xs j), iniSegOdr (xs i) ↾↾ iniSegNds (xs i) (xs j)) = xs k) =
      Multiclass.remap (fun ys : Fin 3 → M ↦ rtLosSLOT trvAZero
        !(iniSegNds (ys 0) (ys 1), iniSegOdr (ys 0) ↾↾ iniSegNds (ys 0) (ys 1)) = ys 2)
        ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ iniSegAoc (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ iniSegAoc (xs 0) (xs 1) = xs 2) = fun xs ↦
      ∃ S, rtLosSLOT trvAZero
        !(iniSegNds (xs 0) (xs 1), iniSegOdr (xs 0) ↾↾ iniSegNds (xs 0) (xs 1)) = S ∧
        cc (aoc (xs 0) ↾ ((1 : ℕ) : M)) S = xs 2 := by
    funext xs
    simp [iniSegAoc]
  rw [h]
  infer_instance
instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ iniSegAoc (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ iniSegAoc (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ iniSegAoc (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ iniSegRight (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ iniSegRight (xs 0) (xs 1) = xs 2) = fun xs ↦
      ∃ N O : M, iniSegNds (xs 0) (xs 1) = N ∧ iniSegOdr (xs 0) = O ∧ ∃ d : M,
        d = sigdcn (xs 0) (xs 1) ∧ (∀ r ∈ xs 2, r ∈ N ∧ d [O] r) ∧ ∀ r ∈ N, d [O] r → r ∈ xs 2 := by
    funext xs
    apply propext
    constructor
    · intro h
      refine ⟨_, _, rfl, rfl, _, rfl, fun r hr ↦ ?_, fun r hr hd ↦ ?_⟩
      · rw [← h] at hr
        exact mem_iniSegRight_iff.mp hr
      · rw [← h]
        exact mem_iniSegRight_iff.mpr ⟨hr, hd⟩
    · rintro ⟨N, O, rfl, rfl, d, rfl, h₁, h₂⟩
      ext r
      rw [mem_iniSegRight_iff]
      exact ⟨fun h ↦ h₂ r h.left h.right, fun h ↦ h₁ r h⟩
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ iniSegRight (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ iniSegRight (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ iniSegRight (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `r` is the least element of `R` in the order `O` -/
def IsLeastIn (O R r : M) : Prop := ∀ r' ∈ R, r' = r ∨ r [O] r'

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ IsLeastIn (xs 0) (xs 1) (xs 2)) Set.univ := by
  unfold IsLeastIn; infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ IsLeastIn (xs i) (xs j) (xs k)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsLeastIn (xs i) (xs j) (xs k)) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ IsLeastIn (ys 0) (ys 1) (ys 2)) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦
    ⋃₀ (xs 1 ∩₀ fun r ↦ IsLeastIn (xs 0) (xs 1) r) = xs 2) Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ ⋃₀ (xs 1 ∩₀ fun r ↦ IsLeastIn (xs 0) (xs 1) r) = xs 2) =
      fun xs ↦ (∀ z ∈ xs 2, ∃ r ∈ xs 1, IsLeastIn (xs 0) (xs 1) r ∧ z ∈ r) ∧
        ∀ r ∈ xs 1, IsLeastIn (xs 0) (xs 1) r → ∀ z ∈ r, z ∈ xs 2 := by
    funext xs
    apply propext
    constructor
    · intro h
      rw [← h]
      refine ⟨fun z hz ↦ ?_, fun r hr hl z hz ↦ ?_⟩
      · rw [mem_sUnion_iff] at hz
        obtain ⟨r, hr, hz⟩ := hz
        rw [mem_comprehension_iff] at hr
        exact ⟨r, hr.left, hr.right, hz⟩
      · rw [mem_sUnion_iff]
        exact ⟨r, (mem_comprehension_iff ..).mpr ⟨hr, hl⟩, hz⟩
    · rintro ⟨h₁, h₂⟩
      ext z
      rw [mem_sUnion_iff]
      constructor
      · rintro ⟨r, hr, hz⟩
        rw [mem_comprehension_iff] at hr
        exact h₂ r hr.left hr.right z hz
      · intro hz
        obtain ⟨r, hr, hl, hz⟩ := h₁ z hz
        exact ⟨r, (mem_comprehension_iff ..).mpr ⟨hr, hl⟩, hz⟩
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    ⋃₀ (xs j ∩₀ fun r ↦ IsLeastIn (xs i) (xs j) r) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ ⋃₀ (xs j ∩₀ fun r ↦ IsLeastIn (xs i) (xs j) r) = xs k) =
      Multiclass.remap (fun ys : Fin 3 → M ↦
        ⋃₀ (ys 1 ∩₀ fun r ↦ IsLeastIn (ys 0) (ys 1) r) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ iniSegUcf (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ iniSegUcf (xs 0) (xs 1) = xs 2) = fun xs ↦
      ∃ R : M, iniSegRight (xs 0) (xs 1) = R ∧ ((R = ∅ ∧ tpUcfZero (aoc (xs 0)) = xs 2) ∨
        (R ≠ ∅ ∧ ∃ O m : M, iniSegOdr (xs 0) = O ∧
          ⋃₀ (R ∩₀ fun r ↦ IsLeastIn O R r) = m ∧ !(((1 : ℕ) : M), m) = xs 2)) := by
    funext xs
    by_cases hR : iniSegRight (xs 0) (xs 1) = ∅ <;> simp [iniSegUcf, hR, IsLeastIn]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ iniSegUcf (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ iniSegUcf (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ iniSegUcf (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The `uoci` part `(U | k)_{aoc, sig, ctp}` of the initial segment -/
noncomputable def iniSegBase (U k : M) : M := ciTriple (iniSegAoc U k) (sig U ↾ k) dct

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ iniSegBase (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ iniSegBase (xs 0) (xs 1) = xs 2) = fun xs ↦
      ∃ A s : M, iniSegAoc (xs 0) (xs 1) = A ∧ s = sig (xs 0) ↾ xs 1 ∧ ciTriple A s dct = xs 2 := by
    funext xs
    simp [iniSegBase]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ iniSegBase (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ iniSegBase (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ iniSegBase (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ iniSeg (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ iniSeg (xs 0) (xs 1) = xs 2) = fun xs ↦
      ∃ B : M, iniSegBase (xs 0) (xs 1) = B ∧ ((xs 1 = ∅ ∧ B = xs 2) ∨
        (xs 1 ≠ ∅ ∧ ∃ F : M, iniSegUcf (xs 0) (xs 1) = F ∧ cc (cc B F) lf = xs 2)) := by
    funext xs
    by_cases hk : xs 1 = ∅ <;> simp [iniSeg, iniSegBase, hk, ciQuint]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ iniSeg (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ iniSeg (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ iniSeg (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

end Definability

end FirstOrder.Language.MemStructure
