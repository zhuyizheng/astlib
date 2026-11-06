/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.Order
/-!
# The least child; `P ⊗ Q ∈ otci_2`

The least child `leastChdOf P Q p q` of a node `p` of `P ⊗ Q` with the key of an extension `q`
of `p_uc`, `tensorProdTwoTwo P Q ∈ otci_2`, `tensorProdATwoATwo T Q ∈ aotci_2` and the
definability of `(T, Q) ↦ T ⊗ Q`.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M]

section TensorProd

variable {P Q T W : M}

section YStarSpec

/-! ### The least new node with a given nearest old node above it, packaged -/

variable {Q V w qa ha : M}

/-- The children of a node of an `otci_2` tree share their key -/
theorem aoc_uc_eq_of_mem_chdOf_otci_two {P p c c' : M} (hP : P ∈ otci ((2 : ℕ) : M))
    (hp : p ∈ ndOf P) (hc : c ∈ chdOf P p) (hc' : c' ∈ chdOf P p) :
    aoc (uc c) = aoc (uc c') := by
  obtain ⟨-, -, -, -, hchd⟩ := otciCond_two hP
  obtain ⟨q, hq, hqk⟩ := ((hchd p hp).left (aoc (uc c))).mp ⟨c, hc, rfl⟩
  obtain ⟨q', hq', hqk'⟩ := ((hchd p hp).left (aoc (uc c'))).mp ⟨c', hc', rfl⟩
  rw [← hqk, ← hqk', eq_of_mem_ciExt_one hq hq']

/-- `y* = (c, h')` is below every new node `y = (q, h)` with first new entry at `k` and nearest
old node `a = (q_a, h_a)` above it, and equal to it if `y` is of type `ct` with depth `k + 1` -/
def IsYStarLe (Q V qa ha c h' : M) : Prop :=
  ∀ q h k, q ∈ ndOf (Q ﹫ 2) →
    !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) →
    h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)) →
    k ∈ depOf (Q ﹫ 2) q →
    (∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V))) →
    sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V)) →
    !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
      !(dctUZero, !(qa, ha)) →
    (∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
      !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
        z = !(dctUZero, !(qa, ha)) ∨
          !(dctUZero, !(qa, ha)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) →
    (!(dctUZero, !(c, h')) = !(dctUZero, !(q, h)) ∨
      !(dctUZero, !(c, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
        !(dctUZero, !(q, h))) ∧
    (ctp (uc q) = ct → depOf (Q ﹫ 2) q = succ k → !(q, h) = !(c, h'))

/-- The least new node `y*` with nearest old node `a = (q_a, h_a)` above it: it is of type `ct`
and childless, its signature has the new entry exactly at the end, `a` is the least old node
above it, it is below every new node `y` with nearest old node `a` above, and it is the only
such `y` of type `ct` with the new entry only at the end -/
theorem exists_yStar (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hwR : w ∈ iniSegRight V (⋃₀ dom (sig V)))
    (hwl : ∀ r ∈ iniSegRight V (⋃₀ dom (sig V)), r = w ∨ w [iniSegOdr V] r)
    (hqa : qa ∈ ndOf (Q ﹫ 2)) (hqart : qa ∉ rtOf (Q ﹫ 2))
    (hha : ha ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa))
      (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V)))))
    (hucf : tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) !(dctUZero, !(qa, ha)) =
      !(((1 : ℕ) : M), w))
    (haN : !(dctUZero, !(qa, ha)) ∈
      ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M))) :
    ∃ c h', c ∈ ndOf (Q ﹫ 2) ∧
      h' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc c)) (tensorProdTwoAOneTgt (aoc V)) ∧
      !(dctUZero, !(c, h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) ∧
      ctp (uc c) = ct ∧ chdOf (Q ﹫ 2) c = ∅ ∧
      (∃ j, depOf (Q ﹫ 2) c = succ j ∧ sigImg (aoc V) c h' j = sigdcn V (⋃₀ dom (sig V)) ∧
        (∀ i ∈ j, sigImg (aoc V) c h' i = sigImg (iniSegAoc V (⋃₀ dom (sig V))) qa ha i) ∧
        (depOf (Q ﹫ 2) qa = j ∨ (depOf (Q ﹫ 2) qa = succ j ∧ ctp (uc qa) = ct))) ∧
      !(dctUZero, !(c, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
        !(dctUZero, !(qa, ha)) ∧
      (∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
        !(dctUZero, !(c, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
          z = !(dctUZero, !(qa, ha)) ∨
            !(dctUZero, !(qa, ha)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) ∧
      IsYStarLe Q V qa ha c h' := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hPs := (otciCond_two hQ2).left
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := hPs
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', -, hsub, -⟩ := lastSeg_facts hV hm
  have hT := tensorProdTwoAOneTgt_mem hX
  have heX := (siglvl_eq_one hV hm).right
  have hUa := uc_mem_stduoci_of_mem_otci_two hQ2 hqa
  have himgold {c h' i : M} (hi : i ∈ dom (sig (uc qa)))
      (hv : (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) i = (ha ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc qa) i) :
      sigImg (aoc V) c h' i = sigImg (iniSegAoc V (⋃₀ dom (sig V))) qa ha i := by
    obtain ⟨hz, hze⟩ := sigImg_spec hQ2 hqa hX' hha hi
    rw [show sigImg (aoc V) c h' i = tpOrig (aoc V) ((1 : ℕ) : M)
      ((h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) i) from rfl, hv, hze,
      tpOrig_one_relabelOne hX (hsub.left hz)]
  have himgnew {c h' j : M} (hv : (h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) j =
      relabelOne trvAZero (sigdcn V (⋃₀ dom (sig V)))) :
      sigImg (aoc V) c h' j = sigdcn V (⋃₀ dom (sig V)) := by
    rw [sigImg, hv, tpOrig_one_relabelOne hX heX]
  have hda : dom (sig (uc qa)) = depOf (Q ﹫ 2) qa := dom_sig_uc_eq_depOf hQ2 hqa
  rcases ctp_eq_ct_or_dct (natCast_mem_omega 1) (mem_stduoci_iff.mp hUa).left with hct | hdct
  · -- `q_a` is continuous: `y* = (q_a, h_a[last ↦ e])`
    obtain ⟨h', hh', hy', hval, hnew, hupd⟩ :=
      exists_yStar_ct hQ hV hm hwR hwl hqa hqart hha hct hucf
    obtain ⟨hlt, hmin⟩ :=
      yStar_ct_order hQ hV hm hwR hwl hqa hqart hha hct hucf hh' hy' hval hnew hupd
    have hcchd := chdOf_eq_empty_of_ctp_eq_ct (natCast_mem_omega 2) hQ2 hqa hct
    obtain ⟨hdqa, -, -⟩ := ucf_facts_of_tpUcf_ct hQ hX' hqa hqart hha hct hucf
    refine ⟨qa, h', hqa, hh', hy', hct, hcchd, ⟨⋃₀ depOf (Q ﹫ 2) qa, hdqa, himgnew hnew,
      fun i hi ↦ himgold (by rw [hda, hdqa]; exact mem_succ_of_mem hi) (hval i hi),
      .inr ⟨hdqa, hct⟩⟩, hlt, hmin,
      fun q h k hq hy hh hk hfirst hje hya hamin ↦
        ⟨yStar_ct_le hQ hV hm hqa hct hh' hy' hval hnew hq hy hh hk hfirst hje haN hya hamin,
          fun hctq hdq ↦ ?_⟩⟩
    have hdqω := hTS.dep_mem_omega hq
    have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
    obtain ⟨w', -, -, hcase⟩ :=
      eq_succ_of_isLeastAbove hQ hV hm hq hy hh hk hfirst hje haN hya hamin
    have hck : ancOf (Q ﹫ 2) q (succ k) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) :=
      hTS.anc_succ_mem_chd hq hk
    have hka : ancOf (Q ﹫ 2) q k ∈ ndOf (Q ﹫ 2) := (hTS.anc_mem_nd hq (mem_succ_of_mem hk)).left
    have hqq : ancOf (Q ﹫ 2) q (succ k) = q := by rw [← hdq]; exact hTS.anc_dep hq
    rcases hcase with ⟨-, -, hE⟩ | ⟨-, hE⟩
    · exfalso
      rw [succOne, orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hE
      obtain ⟨-, hqeq, -⟩ := hE
      rw [← hqeq, hcchd] at hck
      simp at hck
    rw [succTwo, orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hE
    obtain ⟨-, hqeq, hheq⟩ := hE
    rw [hqq] at hqeq hheq hck
    rw [eq_ctChd_of_ctp_eq_ct (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hka hck hctq] at hqeq
    subst hqeq
    have hka' : ⋃₀ depOf (Q ﹫ 2) qa = k := by
      rw [hdq, sUnion_succ (ordinal_of_mem ordinal_omega
        (ordinal_omega.transitive _ hdqω hk)).transitive]
    rw [hka'] at hval hnew
    have hdqk : dom (sig (uc qa)) = depOf (Q ﹫ 2) qa := hda
    have hkq : k ∈ dom (sig (uc qa)) := by rw [hdqk]; exact hk
    have hhe := (mem_aotciEmbSet_iff.mp hh).right
    have hf1 :=
      ((hhe.isOtciEmbedding (mem_succ_self _)).isEmbedding).isEmbedding_ts.isInjectionFromTo
    rw [orderedPair_eq_orderedPair_iff]
    refine ⟨rfl, eq_of_mem_aotciEmbSet_one hUq hT hh hh' fun i hi ↦ ?_⟩
    rw [(siglvl_eq_one hUq hi).left]
    have hi' : i ∈ succ k := by rw [← hdq, ← hdqk]; exact hi
    rcases mem_or_eq_of_mem_succ hi' with hik | rfl
    · have hnd : sigdcn (uc qa) i ∈ ndOf (aoc (uc qa) ﹫ ((1 : ℕ) : M)) :=
        (siglvl_eq_one hUq hi).right
      have hne : sigdcn (uc qa) i ≠ sigdcn (uc qa) k := by
        intro h''
        have := congrArg lbl h''
        rw [lbl_sigdcn hUq hi, lbl_sigdcn hUq hkq] at this
        rw [this] at hik
        exact notMem_self _ hik
      rw [hval i hik, hheq, embUpd_val_one_of_ne hhe.isFunction
        (by rw [hhe.dom_eq]; exact mem_succ_of_mem empty_mem_natCast_one) hf1.isFunction
        (by rw [hf1.isFunctionFromTo.dom_eq]; exact hnd) hnd hne]
    · rw [hnew, (sigImg_spec hQ2 hq hX hh hkq).right, hje]
  · -- `q_a` is discontinuous: `y* = (q_a⁺, h_a ∪ {new ↦ e})`
    obtain ⟨c, h', hc, hcct, hcchd, hcmin, hh', hy', hval, hnew, hres⟩ :=
      exists_yStar_dct hQ hV hm hwR hwl hqa hqart hha hdct hucf
    obtain ⟨hlt, hmin⟩ :=
      yStar_dct_order hQ hV hm hwR hwl hqa hqart hha hdct hucf hc hh' hy' hval hnew hres
    have hcn := mem_ndOf_of_mem_chdOf hPs hc
    obtain ⟨hdc, hanc⟩ := ancOf_eq_of_mem_chdOf hPs hc
    refine ⟨c, h', hcn, hh', hy', hcct, hcchd, ⟨depOf (Q ﹫ 2) qa, hdc, himgnew hnew,
      fun i hi ↦ himgold (by rw [hda]; exact hi) (hval i hi), .inl rfl⟩, hlt, hmin,
      fun q h k hq hy hh hk hfirst hje hya hamin ↦
        ⟨yStar_dct_le hQ hV hm hqa hdct hc hcchd hcmin hh' hy' hnew hres hq hy hh hk hfirst hje
          haN hya hamin, fun hctq hdq ↦ ?_⟩⟩
    have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
    obtain ⟨w', -, -, hcase⟩ :=
      eq_succ_of_isLeastAbove hQ hV hm hq hy hh hk hfirst hje haN hya hamin
    have hck : ancOf (Q ﹫ 2) q (succ k) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) :=
      hTS.anc_succ_mem_chd hq hk
    have hka : ancOf (Q ﹫ 2) q k ∈ ndOf (Q ﹫ 2) := (hTS.anc_mem_nd hq (mem_succ_of_mem hk)).left
    have hqq : ancOf (Q ﹫ 2) q (succ k) = q := by rw [← hdq]; exact hTS.anc_dep hq
    rw [hqq] at hck
    rcases hcase with ⟨-, -, hE⟩ | ⟨-, hE⟩
    · rw [succOne, orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hE
      obtain ⟨-, hqeq, hheq⟩ := hE
      have hkd : depOf (Q ﹫ 2) qa = k := by
        rw [hqeq]
        exact (hTS.anc_mem_nd hq (mem_succ_of_mem hk)).right
      rw [← hqeq] at hck hheq
      have hqc : q = c := by
        rw [← eq_ctChd_of_ctp_eq_ct (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hqa hck hctq,
          ← eq_ctChd_of_ctp_eq_ct (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hqa hc hcct,
          aoc_uc_eq_of_mem_chdOf_otci_two hQ2 hqa hck hc]
      rw [hqc] at hh hje hdq ⊢
      have hUc := uc_mem_stduoci_of_mem_otci_two hQ2 hcn
      have hhe := (mem_aotciEmbSet_iff.mp hh).right
      have hf1 :=
        ((hhe.isOtciEmbedding (mem_succ_self _)).isEmbedding).isEmbedding_ts.isInjectionFromTo
      obtain ⟨-, -, hsubc, -⟩ := uc_rel_of_mem_chdOf hQ2 hqa hc
      rw [orderedPair_eq_orderedPair_iff]
      refine ⟨rfl, eq_of_mem_aotciEmbSet_one hUc hT hh hh' fun i hi ↦ ?_⟩
      rw [(siglvl_eq_one hUc hi).left]
      have hi' : i ∈ succ k := by rw [← hdq, ← dom_sig_uc_eq_depOf hQ2 hcn]; exact hi
      rcases mem_or_eq_of_mem_succ hi' with hik | rfl
      · have hik' : i ∈ depOf (Q ﹫ 2) qa := by rw [hkd]; exact hik
        have hsd : sigdcn (uc qa) i = sigdcn (uc c) i := by
          have h'' := sigdcn_anc hQ2 hcn (l := depOf (Q ﹫ 2) qa)
            (by rw [hdc]; exact mem_succ_of_mem (mem_succ_self _)) hik'
          rwa [hanc] at h''
        have hnda : sigdcn (uc qa) i ∈ ndOf (aoc (uc qa) ﹫ ((1 : ℕ) : M)) :=
          (siglvl_eq_one hUa (by rw [hda]; exact hik')).right
        rw [hval i hik', hheq, embRestrict_val _ _ natCast_one_mem_two,
          val_restrict _ hf1.isFunction hnda
            (by rw [hf1.isFunctionFromTo.dom_eq]; exact hsubc.left hnda), hsd]
      · rw [(sigImg_spec hQ2 hcn hX hh hi).right, hje, ← hkd, hnew]
    · exfalso
      rw [succTwo, orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hE
      obtain ⟨-, hqeq, -⟩ := hE
      obtain ⟨-, -, -, hct, -⟩ :=
        ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hka hck
      rw [hqq] at hqeq
      rw [← hqeq, hdct] at hct
      exact ct_ne_dct hct.symm

end YStarSpec

section EmbHelpers

/-! ### Values of embeddings changed at one level-`1` node -/

variable {A B σ : M}

theorem embChg_vals (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) A B) (s D : M) :
    cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M)) s D) ﹫ ((1 : ℕ) : M) =
        update (σ ﹫ ((1 : ℕ) : M)) s D ∧
      cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M)) s D) ﹫ ∅ = σ ﹫ ∅ ∧
      cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M)) s D) ↾ ((1 : ℕ) : M) =
        σ ↾ ((1 : ℕ) : M) := by
  have he := (mem_aotciEmbSet_iff.mp hσ).right
  have h12 : ((1 : ℕ) : M) ⊆ dom σ := by
    rw [he.dom_eq]
    exact fun _ hz ↦ mem_succ_of_mem hz
  have hhr : IsFunction (σ ↾ ((1 : ℕ) : M)) := he.isFunction.restrict _
  have hhrdom : dom (σ ↾ ((1 : ℕ) : M)) = ((1 : ℕ) : M) := dom_restrict_of_subset he.isFunction h12
  refine ⟨?_, ?_, ?_⟩
  · have h'' := cc_val_self hhr (update (σ ﹫ ((1 : ℕ) : M)) s D)
    rwa [hhrdom] at h''
  · rw [cc_val_of_mem hhr _ (by rw [hhrdom]; exact empty_mem_natCast_one),
      val_restrict _ he.isFunction empty_mem_natCast_one (h12 empty_mem_natCast_one)]
  · have h'' := cc_restrict_dom hhr (update (σ ﹫ ((1 : ℕ) : M)) s D)
    rwa [hhrdom] at h''

theorem embChg_val_one_isFunction (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) A B) :
    IsFunction (σ ﹫ ((1 : ℕ) : M)) ∧ dom (σ ﹫ ((1 : ℕ) : M)) = ndOf (A ﹫ ((1 : ℕ) : M)) := by
  have he := (mem_aotciEmbSet_iff.mp hσ).right
  have hf1 := ((he.isOtciEmbedding (mem_succ_self _)).isEmbedding).isEmbedding_ts.isInjectionFromTo
  exact ⟨hf1.isFunction, hf1.isFunctionFromTo.dom_eq⟩

/-- An embedding is its level-`0` part followed by its level-`1` part -/
theorem cc_restrict_val_one_eq (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) A B) :
    cc (σ ↾ ((1 : ℕ) : M)) (σ ﹫ ((1 : ℕ) : M)) = σ := by
  have he := (mem_aotciEmbSet_iff.mp hσ).right
  have h12 : ((1 : ℕ) : M) ⊆ dom σ := by
    rw [he.dom_eq]
    exact fun _ hz ↦ mem_succ_of_mem hz
  have hhr : IsFunction (σ ↾ ((1 : ℕ) : M)) := he.isFunction.restrict _
  have hhrdom : dom (σ ↾ ((1 : ℕ) : M)) = ((1 : ℕ) : M) := dom_restrict_of_subset he.isFunction h12
  have hdσ : dom σ = succ ((1 : ℕ) : M) := by rw [he.dom_eq]
  refine (hhr.cc _).ext he.isFunction (by rw [dom_cc, hhrdom, hdσ]) fun i hi ↦ ?_
  rw [dom_cc, hhrdom] at hi
  rcases mem_succ_one_cases hi with rfl | rfl
  · rw [cc_val_of_mem hhr _ (by rw [hhrdom]; exact empty_mem_natCast_one),
      val_restrict _ he.isFunction empty_mem_natCast_one (h12 empty_mem_natCast_one)]
  · have h'' := cc_val_self hhr (σ ﹫ ((1 : ℕ) : M))
    rwa [hhrdom] at h''

/-- Restricting an embedding extended by a new node `s` gives back the embedding -/
theorem embRestrict_embExt {U s D : M} (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc U) B)
    (hs : s ∉ ndOf (aoc U ﹫ ((1 : ℕ) : M))) :
    embRestrict U (cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M)) s D)) = σ := by
  have he := (mem_aotciEmbSet_iff.mp hσ).right
  obtain ⟨hv1, hv0, -⟩ := embChg_vals hσ s D
  obtain ⟨hinj1, hdom1⟩ := embChg_val_one_isFunction hσ
  have hres : IsSetRestrictedTo (fun i ↦ (cc (σ ↾ ((1 : ℕ) : M))
      (update (σ ﹫ ((1 : ℕ) : M)) s D) ﹫ i) ↾ ndOf (aoc U ﹫ i)) ((2 : ℕ) : M) :=
    isSetRestrictedTo_of_definable _
  refine (isFunction_toSetRestrictedTo hres).ext he.isFunction
    (by rw [dom_toSetRestrictedTo hres, he.dom_eq]; rfl) fun i hi ↦ ?_
  rw [dom_toSetRestrictedTo hres] at hi
  rw [val_toSetRestrictedTo hres hi]
  rcases mem_succ_one_cases hi with rfl | rfl
  · rw [hv0]
    have he0 := ((he.isOtciEmbedding (mem_succ_of_mem empty_mem_natCast_one)).isEmbedding
      ).isEmbedding_ts.isInjectionFromTo
    have hd0 : ndOf (aoc U ﹫ ∅) = dom (σ ﹫ ∅) := he0.isFunctionFromTo.dom_eq.symm
    rw [hd0]
    exact restrict_dom he0.isFunction
  · rw [hv1]
    have hsub' : ndOf (aoc U ﹫ ((1 : ℕ) : M)) ⊆ dom (update (σ ﹫ ((1 : ℕ) : M)) s D) := by
      rw [dom_update, hdom1]
      exact fun _ h'' ↦ by rw [mem_insert_iff]; exact .inr h''
    refine ((hinj1.update _ _).restrict _).ext hinj1
      (by rw [dom_restrict_of_subset (hinj1.update _ _) hsub', hdom1]) fun x hx ↦ ?_
    rw [dom_restrict_of_subset (hinj1.update _ _) hsub'] at hx
    rw [val_restrict _ (hinj1.update _ _) hx (hsub' hx)]
    exact val_update_of_ne hinj1 _ (by rw [hdom1]; exact hx) fun h'' ↦ hs (h'' ▸ hx)

/-- Changing back the value at `u` to the original value gives back the embedding -/
theorem embUpd_embRep {t u D : M} (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) B)
    (hu : u ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) :
    embUpd (cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M)) u D)) t u
      ((σ ﹫ ((1 : ℕ) : M)) ﹫ u) = σ := by
  obtain ⟨hv1, -, hr1⟩ := embChg_vals hσ u D
  obtain ⟨hinj1, hdom1⟩ := embChg_val_one_isFunction hσ
  have hdu : dom (update (σ ﹫ ((1 : ℕ) : M)) u D) = ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)) := by
    rw [dom_update, hdom1]
    ext z
    rw [mem_insert_iff]
    exact ⟨fun h ↦ h.elim (fun h' ↦ h' ▸ hu) (fun h' ↦ h'), .inr⟩
  rw [embUpd, hr1, lvlOneRes, hv1, ← hdu, restrict_dom (hinj1.update _ _)]
  have hupd : update (update (σ ﹫ ((1 : ℕ) : M)) u D) u ((σ ﹫ ((1 : ℕ) : M)) ﹫ u) =
      σ ﹫ ((1 : ℕ) : M) := by
    refine ((hinj1.update _ _).update _ _).ext hinj1 ?_ fun z hz ↦ ?_
    · rw [dom_update, hdu, hdom1]
      ext z
      rw [mem_insert_iff]
      exact ⟨fun h ↦ h.elim (fun h' ↦ h' ▸ hu) (fun h' ↦ h'), .inr⟩
    · rw [dom_update, hdu] at hz
      by_cases hzu : z = u
      · rw [hzu, val_update_self (hinj1.update _ _)]
      · rw [mem_insert_iff] at hz
        have hz' : z ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)) := hz.resolve_left hzu
        rw [val_update_of_ne (hinj1.update _ _) _ (by rw [hdu]; exact hz') hzu,
          val_update_of_ne hinj1 _ (by rw [hdom1]; exact hz') hzu]
  rw [hupd]
  exact cc_restrict_val_one_eq hσ

end EmbHelpers

section XStarNode

/-! ### The least child `x*` is a node -/

theorem endsWithNew_of {s L J e : M} (hL : Ordinal L) (hJ : Ordinal J) (hd : dom s = succ L)
    (hdL : dom (s ﹫ L) = succ J) (he : (s ﹫ L) ﹫ J = e)
    (hne : ∀ i ∈ dom s, ∀ j ∈ dom (s ﹫ i), ¬(i = L ∧ j = J) → (s ﹫ i) ﹫ j ≠ e) :
    EndsWithNew s := by
  have hli : lastIdx s = L := by
    change ⋃₀ dom s = L
    rw [hd, sUnion_succ hL.transitive]
  have hls : lastSeq s = s ﹫ L := by
    change s ﹫ lastIdx s = _
    rw [hli]
  have hlj : lastIdx (lastSeq s) = J := by
    rw [hls]
    change ⋃₀ dom (s ﹫ L) = J
    rw [hdL, sUnion_succ hJ.transitive]
  have hle : lastEntry s = e := by
    change lastSeq s ﹫ lastIdx (lastSeq s) = e
    rw [hlj, hls, he]
  refine ⟨by rw [hli, hd]; exact mem_succ_self _, by rw [hlj, hls, hdL]; exact mem_succ_self _,
    fun i hi j hj hv ↦ ?_⟩
  rw [hle] at hv
  rw [hli, hlj]
  by_contra hij
  exact hne i hi j hj hij hv


variable {P Q V t σ tc : M}

theorem pair_mem_ran_sig_restrict (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) {w : M}
    (hw : w ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M))) :
    !(((1 : ℕ) : M), w) ∈ ran (sig V ↾ ⋃₀ dom (sig V)) := by
  obtain ⟨-, -, -, hnd'⟩ := lastSeg_facts hV hm
  have hsf := (uociCond_of_mem_stduoci_one hV).right.right.right.left.left
  obtain ⟨hwX, hwe⟩ := (hnd' w).mp hw
  rw [ndOf_aoc_val_one_eq hV, mem_iniSegNds_iff] at hwX
  obtain ⟨i, hi, rfl⟩ := hwX
  have hdm := (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV)
    (fun h' ↦ by rw [h'] at hm; exact notin_empty _ hm)).right.right
  have him : i ∈ ⋃₀ dom (sig V) := by
    have hi' := hi
    rw [hdm] at hi'
    rcases mem_or_eq_of_mem_succ hi' with h' | h'
    · exact h'
    · exact (hwe (by rw [h'])).elim
  have hsub : ⋃₀ dom (sig V) ⊆ dom (sig V) := fun _ h' ↦ by
    rw [hdm]; exact mem_succ_of_mem h'
  rw [(hsf.restrict _).mem_ran_iff, dom_restrict_of_subset hsf hsub]
  exact ⟨i, him, by rw [val_restrict _ hsf him hi, sig_val_eq_pair hV hi]⟩

theorem pair_not_mem_ran_sig_restrict (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) :
    !(((1 : ℕ) : M), sigdcn V (⋃₀ dom (sig V))) ∉ ran (sig V ↾ ⋃₀ dom (sig V)) := by
  have hsfc := (uociCond_of_mem_stduoci_one hV).right.right.right.left
  have hsf := hsfc.left
  have hdm := (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV)
    (fun h' ↦ by rw [h'] at hm; exact notin_empty _ hm)).right.right
  have hsub : ⋃₀ dom (sig V) ⊆ dom (sig V) := fun _ h' ↦ by
    rw [hdm]; exact mem_succ_of_mem h'
  intro h
  rw [(hsf.restrict _).mem_ran_iff, dom_restrict_of_subset hsf hsub] at h
  obtain ⟨i, hi, he⟩ := h
  rw [val_restrict _ hsf hi (hsub hi), ← sig_val_eq_pair hV hm] at he
  have := hsfc.right.left i (hsub hi) _ hm he
  rw [this] at hi
  exact notMem_self _ hi

/-- `x* = (V, (t*, σ ∪ {s ↦ y*}))` for a continuous child `t*` of `t` with new node `s` and a node
`y*` of `Q(2) ⊗ V_aoc` of type `ct` whose signature is old entries followed by the new entry -/
theorem xStar_one_mem (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hV : V ∈ stduoci ((1 : ℕ) : M)) (hVct : ctp V = ct) (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
    (hp : !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)) ∈ tensorProdTwoTwoNds P Q)
    (htc : tc ∈ chdOf P t) (hext : !(uc t, uc tc) ∈ ciExt ((1 : ℕ) : M))
    {c h' j : M} (hy : !(dctUZero, !(c, h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hcct : ctp (uc c) = ct) (hdc : depOf (Q ﹫ 2) c = succ j)
    (hje : sigImg (aoc V) c h' j = sigdcn V (⋃₀ dom (sig V)))
    (hold : ∀ i ∈ j, sigImg (aoc V) c h' i ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)))
    (hlt : ∀ z ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)),
      z [odrOne (aoc (uc tc) ﹫ ((1 : ℕ) : M))] (sigdcn (uc tc) (dom (sig (uc t)))) →
        ((σ ﹫ ((1 : ℕ) : M)) ﹫ z) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
          !(dctUZero, !(c, h')))
    (hgt : ∀ z ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)),
      (sigdcn (uc tc) (dom (sig (uc t)))) [odrOne (aoc (uc tc) ﹫ ((1 : ℕ) : M))] z →
        !(dctUZero, !(c, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
          ((σ ﹫ ((1 : ℕ) : M)) ﹫ z)) :
    !(V, !(tc, cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M))
      (sigdcn (uc tc) (dom (sig (uc t)))) !(dctUZero, !(c, h'))))) ∈ tensorProdTwoTwoNds P Q ∧
      IsFirstOcc (embTpSigs Q (aoc V) (uc tc) (cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M))
        (sigdcn (uc tc) (dom (sig (uc t)))) !(dctUZero, !(c, h')))))
        (sig V ﹫ ⋃₀ dom (sig V)) (dom (sig (uc t))) j := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  rw [pair_mem_tensorProdTwoTwoNds_iff, aoc_iniSeg] at hp
  obtain ⟨ht, -, hσ, hemb⟩ := hp
  have hU := hemb.left
  have htcn := mem_ndOf_of_mem_chdOf hS htc
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hUtc := uc_mem_stduoci_of_mem_otci_two hP htcn
  have hA := aoc_mem_aotci_of_mem_stduoci_one hUt
  have hAc := aoc_mem_aotci_of_mem_stduoci_one hUtc
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, hnd'⟩ := lastSeg_facts hV hm
  have hB := tensorProdATwoAOne_mem_aotci hQ hX
  have hB' := tensorProdATwoAOne_mem_aotci hQ hX'
  have h0B : tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ∅ =
      tensorProdATwoAOne Q (aoc V) ﹫ ∅ := (tensorProdATwoAOne_val_zero_eq hQ hX hX' h0).symm
  have hsubB := isSubOne_tensorProdATwoAOne hQ hX hX' h0 hsub
  have hσB := ((mem_aotciEmbSet_iff_of_isSubOne hA hB hB' h0B hsubB).mp hσ).left
  obtain ⟨hsn, hndc, hsU, hsubc, -⟩ := ext_one_tree hext
  set sn := sigdcn (uc tc) (dom (sig (uc t))) with hsndef
  set y := !(dctUZero, !(c, h')) with hydef
  have hyB : y ∈ ndOf (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)) :=
    (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX).mpr (.inr hy)
  have hσc := embExt_mem_aotciEmbSet hA hAc hB (aoc_val_of_mem_ciExt_one hext).left hsubc hndc hsU
    hσB hyB hlt hgt
  obtain ⟨hv1, -, -⟩ := embChg_vals hσB sn y
  set σc := cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M)) sn y) with hσcdef
  obtain ⟨hinj1, hdom1⟩ := embChg_val_one_isFunction hσB
  obtain ⟨hsig, hdtc, -, -⟩ := uc_rel_of_mem_chdOf hP ht htc
  have hnω := dom_sig_mem_omega_of_mem_stduoci_one hUt
  have hno := ordinal_of_mem ordinal_omega hnω
  set n := dom (sig (uc t)) with hndef
  have hsft := (uociCond_of_mem_stduoci_one hUtc).right.right.right.left.left
  have hsd (i : M) (hi : i ∈ n) : sigdcn (uc tc) i = sigdcn (uc t) i := by
    rw [sigdcn, sigdcn, hsig, val_restrict _ hsft hi (by rw [hdtc]; exact mem_succ_of_mem hi)]
  have hold' (i : M) (hi : i ∈ n) : sigdcn (uc t) i ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)) :=
    (siglvl_eq_one hUt hi).right
  have hval_old (i : M) (hi : i ∈ n) :
      (σc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) i = (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i := by
    rw [hv1, hsd i hi]
    exact val_update_of_ne hinj1 _ (by rw [hdom1]; exact hold' i hi)
      fun h'' ↦ hsU (h'' ▸ hold' i hi)
  have hval_new : (σc ﹫ ((1 : ℕ) : M)) ﹫ sn = y := by rw [hv1]; exact val_update_self hinj1 _ _
  -- the rows
  set s := embTpSigs Q (iniSegAoc V (⋃₀ dom (sig V))) (uc t) σ with hsdef
  set s' := embTpSigs Q (aoc V) (uc tc) σc with hs'def
  have hs : IsFinSeqSeq s := isFinSeqSeq_embTpSigs hQ hnω _ σ
  have hs' : IsFinSeqSeq s' :=
    isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUtc) _ σc
  have hds : dom s = n := dom_embTpSigs _ _ _ _
  have hds' : dom s' = succ n := by rw [dom_embTpSigs, hdtc]
  have hhf := ((mem_aotciEmbSet_iff.mp hσ).right.isOtciEmbedding
    (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  have hrow (i : M) (hi : i ∈ n) : s' ﹫ i = s ﹫ i := by
    rw [hs'def, embTpSigs_val hUtc (by rw [hdtc]; exact mem_succ_of_mem hi), hval_old i hi,
      hsdef, embTpSigs_val hUt hi]
    exact (tpSig_lastSeg_eq hQ hV hm (hhf.isFunctionFromTo.val_mem (hold' i hi))).symm
  have hrown : s' ﹫ n = tpSig Q (aoc V) y := by
    rw [hs'def, embTpSigs_val hUtc (by rw [hdtc]; exact mem_succ_self _), ← hsndef, hval_new]
  have hcn : c ∈ ndOf (Q ﹫ 2) := by
    obtain ⟨c', hc', -, h'', -, hce⟩ := mem_tensorProdTwoAOneNds_iff'.mp hy
    rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hce
    rw [hce.right.left]
    exact hc'
  have hUc := uc_mem_stduoci_of_mem_otci_two hQ2 hcn
  have hdy : dom (tpSig Q (aoc V) y) = succ j := by
    rw [hydef, dom_tpSig_eq hy, dom_sig_uc_eq_depOf hQ2 hcn, hdc]
  have hyval (i : M) (hi : i ∈ succ j) :
      tpSig Q (aoc V) y ﹫ i = !(((1 : ℕ) : M), sigImg (aoc V) c h' i) :=
    tpSig_val_eq hQ hy (by rw [dom_sig_uc_eq_depOf hQ2 hcn, hdc]; exact hi)
  -- the contraction
  have hcon : contraction s = sig V ↾ ⋃₀ dom (sig V) := by
    have h := hU.right.left
    rwa [sig_iniSeg, aoc_iniSeg] at h
  have hc0 : IsContraction s (sig V ↾ ⋃₀ dom (sig V)) := hcon ▸ isContraction_contraction hs
  have hctr : ctrSet s = ran (sig V ↾ ⋃₀ dom (sig V)) := hc0.right.right.right.left.symm
  set e := !(((1 : ℕ) : M), sigdcn V (⋃₀ dom (sig V))) with hedef
  have hentry (i : M) (hi : i ∈ succ j) :
      tpSig Q (aoc V) y ﹫ i ∈ ctrSet s ∨ tpSig Q (aoc V) y ﹫ i = e := by
    rcases mem_or_eq_of_mem_succ hi with hi | rfl
    · left
      rw [hyval i (mem_succ_of_mem hi), hctr]
      exact pair_mem_ran_sig_restrict hV hm (hold i hi)
    · right
      rw [hyval _ (mem_succ_self _), hje]
  have hext' : IsSeqSeqExt s s' := by
    refine ⟨fun i hi j' hj' ↦ ?_, fun i' hi' j' hj' ↦ ?_⟩
    · rw [hds] at hi
      exact ⟨by rw [hds']; exact mem_succ_of_mem hi, by rw [hrow i hi]; exact hj',
        by rw [hrow i hi]⟩
    · rw [hds'] at hi'
      rcases mem_or_eq_of_mem_succ hi' with hi' | rfl
      · left
        exact ⟨by rw [hds]; exact hi', by rw [← hrow i' hi']; exact hj'⟩
      · right
        intro i hi _ _
        rw [hds] at hi
        exact .inl hi
  have hnew : ∀ i' ∈ dom s', ∀ j' ∈ dom (s' ﹫ i'),
      (s' ﹫ i') ﹫ j' ∈ ctrSet s ∨ (s' ﹫ i') ﹫ j' = e := by
    intro i' hi' j' hj'
    rw [hds'] at hi'
    rcases mem_or_eq_of_mem_succ hi' with hi' | rfl
    · left
      rw [hrow i' hi'] at hj' ⊢
      exact (mem_ctrSet_iff hs).mpr ⟨i', by rw [hds]; exact hi', j', hj', rfl⟩
    · rw [hrown] at hj' ⊢
      rw [hdy] at hj'
      exact hentry j' hj'
  have hes : e ∈ ctrSet s' := (mem_ctrSet_iff hs').mpr ⟨n, by rw [hds']; exact mem_succ_self _, j,
    by rw [hrown, hdy]; exact mem_succ_self _, by rw [hrown, hyval _ (mem_succ_self _), hje]⟩
  have hens : e ∉ ctrSet s := by rw [hctr]; exact pair_not_mem_ran_sig_restrict hV hm
  have hsf := (uociCond_of_mem_stduoci_one hV).right.right.right.left.left
  have hdm := (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV)
    (fun h' ↦ by rw [h'] at hm; exact notin_empty _ hm)).right.right
  have hsubm : ⋃₀ dom (sig V) ⊆ dom (sig V) := fun _ h' ↦ by rw [hdm]; exact mem_succ_of_mem h'
  have hdc0 : dom (sig V ↾ ⋃₀ dom (sig V)) = ⋃₀ dom (sig V) := dom_restrict_of_subset hsf hsubm
  have hcon' : IsContraction s' (sig V) :=
    isContraction_of_isSeqSeqExt hs hs' hc0 hext' hnew hes hens hsf (by rw [hdc0]; exact hdm)
      (fun k hk ↦ by rw [hdc0] at hk; rw [val_restrict _ hsf hk (hsubm hk)])
      (by rw [hdc0, sig_val_eq_pair hV hm])
  have hcon's : contraction s' = sig V := (eq_contraction_of_isContraction hs' hcon').symm
  have hjo : Ordinal j := by
    have hdω : depOf (Q ﹫ 2) c ∈ (ω : M) :=
      (otciCond_two hQ2).left.isTreeStructure.dep_mem_omega hcn
    have hdo := ordinal_of_mem ordinal_omega hdω
    rw [hdc] at hdo
    exact ordinal_of_mem hdo (mem_succ_self j)
  have huniq : ∀ i' ∈ dom s', ∀ j' ∈ dom (s' ﹫ i'), ¬(i' = n ∧ j' = j) →
      (s' ﹫ i') ﹫ j' ≠ e := by
    intro i' hi' j' hj' hij hv
    rw [hds'] at hi'
    rcases mem_or_eq_of_mem_succ hi' with hi' | hin
    · apply hens
      rw [← hv, hrow i' hi']
      rw [hrow i' hi'] at hj'
      exact (mem_ctrSet_iff hs).mpr ⟨i', by rw [hds]; exact hi', j', hj', rfl⟩
    · rw [hin] at hj' hv hij
      rw [hrown, hdy] at hj'
      rw [hrown] at hv
      have hj'j : j' ∈ j := by
        rcases mem_or_eq_of_mem_succ hj' with h'' | h''
        · exact h''
        · exact (hij ⟨rfl, h''⟩).elim
      rw [hyval j' (mem_succ_of_mem hj'j), hedef, orderedPair_eq_orderedPair_iff] at hv
      exact ((hnd' _).mp (hold j' hj'j)).right hv.right
  have hpos : (s' ﹫ n) ﹫ j = e := by rw [hrown, hyval _ (mem_succ_self _), hje]
  have hfo : IsFirstOcc s' (sig V ﹫ ⋃₀ dom (sig V)) n j := by
    rw [sig_val_eq_pair hV hm]
    refine ⟨by rw [hds']; exact mem_succ_self _, by rw [hrown, hdy]; exact mem_succ_self _, hpos,
      fun i' hi' j' hj' hv ↦ ?_⟩
    by_contra hno'
    exact huniq i' hi' j' hj' (fun h ↦ hno' (.inl ⟨h.left.symm, h.right.symm⟩)) hv
  refine ⟨?_, hfo⟩
  rw [pair_mem_tensorProdTwoTwoNds_iff]
  refine ⟨htcn, hV, hσc, ⟨hσc, hcon's, ?_, fun h3 ↦ ?_⟩, fun h' ↦ ?_⟩
  · have hlast : ⋃₀ dom (sig (uc tc)) = n := by rw [hdtc, sUnion_succ hno.transitive]
    rw [hlast]
    refine iff_of_true hVct ⟨(mem_ciExt_props hext).right.right.right, ?_, ?_⟩
    · rw [(siglvl_eq_one hUtc (by rw [hdtc]; exact mem_succ_self _)).left, ← hsndef, hval_new]
      have hnu : nodeU y = uc c := by simp only [nodeU, hydef, lbl_orderedPair, left_orderedPair]
      exact ⟨hy, by rw [hnu]; exact hcct⟩
    · exact endsWithNew_of (e := e) hno hjo hds' (by rw [hrown, hdy]) hpos huniq
  · exfalso
    have hd3 : dom V = ((3 : ℕ) : M) :=
      (uociCond_of_mem_stduoci_one hV).right.right.right.right.right.right.left.mpr (.inr hVct)
    rw [hd3] at h3
    exact notMem_self _ h3
  · rw [h', dom_empty] at hm
    exact (notin_empty _ hm).elim

end XStarNode

section Replace

/-! ### Replacing the last entry of a sequence of sequences -/

variable {s s' c x L J : M}

/-- Replacing the entry at the last position `(L, J)` of `s`, which also occurs elsewhere in
`s`, by a new entry `x` appends `x` to the contraction -/
theorem isContraction_of_replace_last (hs : IsFinSeqSeq s) (hs' : IsFinSeqSeq s')
    (hc : IsContraction s c) (hL : L ∈ dom s) (hJ : J ∈ dom (s ﹫ L))
    (hlast : ∀ i ∈ dom s, ∀ j ∈ dom (s ﹫ i), (i = L ∧ j = J) ∨ i ∈ L ∨ (i = L ∧ j ∈ J))
    (hdom : dom s' = dom s) (hdomi : ∀ i ∈ dom s, dom (s' ﹫ i) = dom (s ﹫ i))
    (hval : ∀ i ∈ dom s, ∀ j ∈ dom (s ﹫ i), ¬(i = L ∧ j = J) → (s' ﹫ i) ﹫ j = (s ﹫ i) ﹫ j)
    (hx : (s' ﹫ L) ﹫ J = x) (hxs : x ∉ ctrSet s)
    (hocc : ∃ i ∈ dom s, ∃ j ∈ dom (s ﹫ i), ¬(i = L ∧ j = J) ∧ (s ﹫ i) ﹫ j = (s ﹫ L) ﹫ J)
    {c' : M} (hc'f : IsFunction c') (hc'd : dom c' = succ (dom c))
    (hc'r : ∀ k ∈ dom c, c' ﹫ k = c ﹫ k) (hc'x : c' ﹫ dom c = x) : IsContraction s' c' := by
  obtain ⟨hcf, hcd, hci, hcr, hco⟩ := hc
  have hco' := ordinal_of_mem ordinal_omega hcd
  have hLo := ordinal_of_mem_dom hs hL
  have hJo := ordinal_of_mem_dom_val hs hL hJ
  have hcmem {k : M} (hk : k ∈ dom c) : c ﹫ k ∈ ctrSet s := by
    rw [← hcr, hcf.mem_ran_iff]; exact ⟨k, hk, rfl⟩
  -- every entry of `s` occurs at a position other than `(L, J)`
  have hother {z : M} (hz : z ∈ ctrSet s) :
      ∃ i ∈ dom s, ∃ j ∈ dom (s ﹫ i), ¬(i = L ∧ j = J) ∧ (s ﹫ i) ﹫ j = z := by
    rw [mem_ctrSet_iff hs] at hz
    obtain ⟨i, hi, j, hj, rfl⟩ := hz
    by_cases hij : i = L ∧ j = J
    · obtain ⟨rfl, rfl⟩ := hij
      exact hocc
    · exact ⟨i, hi, j, hj, hij, rfl⟩
  -- the entries of `s'` are those of `s` and `x`
  have hents : ∀ i ∈ dom s', ∀ j ∈ dom (s' ﹫ i), (i = L ∧ j = J) ∨ (s' ﹫ i) ﹫ j ∈ ctrSet s := by
    intro i hi j hj
    rw [hdom] at hi
    rw [hdomi i hi] at hj
    by_cases hij : i = L ∧ j = J
    · exact .inl hij
    · right
      rw [hval i hi j hj hij, mem_ctrSet_iff hs]
      exact ⟨i, hi, j, hj, rfl⟩
  have hsub : ctrSet s ⊆ ctrSet s' := by
    intro z hz
    obtain ⟨i, hi, j, hj, hij, rfl⟩ := hother hz
    rw [mem_ctrSet_iff hs']
    exact ⟨i, by rw [hdom]; exact hi, j, by rw [hdomi i hi]; exact hj, hval i hi j hj hij⟩
  have hxs' : x ∈ ctrSet s' := by
    rw [mem_ctrSet_iff hs']
    exact ⟨L, by rw [hdom]; exact hL, J, by rw [hdomi L hL]; exact hJ, hx⟩
  -- a position of `s` with a later occurrence is not `(L, J)`
  have hne_last {i j i' j' : M} (hi' : i' ∈ dom s) (hj' : j' ∈ dom (s ﹫ i'))
      (hlt : i ∈ i' ∨ (i = i' ∧ j ∈ j')) : ¬(i = L ∧ j = J) := by
    rintro ⟨rfl, rfl⟩
    obtain ⟨h1, h2⟩ := posLe_antisymm hLo hJo
      (hlt.elim (fun h ↦ .inr (.inl h)) fun h ↦ .inr (.inr h)) (hlast i' hi' j' hj')
    rcases hlt with h | ⟨-, h⟩
    · rw [← h1] at h; exact notMem_self _ h
    · rw [← h2] at h; exact notMem_self _ h
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
        exact hsub (hcmem hk)
      · rw [hc'x]; exact hxs'
    · intro hz
      have hz' := hz
      rw [mem_ctrSet_iff hs'] at hz'
      obtain ⟨i, hi, j, hj, rfl⟩ := hz'
      rcases hents i hi j hj with ⟨rfl, rfl⟩ | h
      · exact ⟨dom c, mem_succ_self _, hc'x.trans hx.symm⟩
      · rw [← hcr, hcf.mem_ran_iff] at h
        obtain ⟨k, hk, hke⟩ := h
        exact ⟨k, mem_succ_of_mem hk, (hc'r k hk).trans hke⟩
  · rw [hc'd] at hk hl
    -- the witness position of `c k`
    have hwit : ∀ z, ∀ i ∈ dom s, ∀ j ∈ dom (s ﹫ i), ¬(i = L ∧ j = J) → (s ﹫ i) ﹫ j = c ﹫ k →
        (∀ i' ∈ dom s', ∀ j' ∈ dom (s' ﹫ i'), (s' ﹫ i') ﹫ j' = z →
          i ∈ i' ∨ (i = i' ∧ j ∈ j')) → OccursBefore s' (c ﹫ k) z := by
      intro z i hi j hj hij he hpre
      exact ⟨i, by rw [hdom]; exact hi, j, by rw [hdomi i hi]; exact hj,
        (hval i hi j hj hij).trans he, hpre⟩
    rcases mem_or_eq_of_mem_succ hl with hl | rfl
    · have hk' : k ∈ dom c := hco'.transitive _ hl hkl
      rw [hc'r k hk', hc'r l hl]
      obtain ⟨i, hi, j, hj, he, hpre⟩ := hco k hk' l hl hkl
      obtain ⟨i₁, hi₁, j₁, hj₁, -, he₁⟩ := hother (hcmem hl)
      have hij : ¬(i = L ∧ j = J) := hne_last hi₁ hj₁ (hpre i₁ hi₁ j₁ hj₁ he₁)
      refine hwit _ i hi j hj hij he fun i' hi' j' hj' hz ↦ ?_
      rcases hents i' hi' j' hj' with ⟨rfl, rfl⟩ | h
      · rw [hx] at hz
        exact (hxs (hz ▸ hcmem hl)).elim
      · rw [hdom] at hi'
        rw [hdomi i' hi'] at hj'
        by_cases hij' : i' = L ∧ j' = J
        · obtain ⟨rfl, rfl⟩ := hij'
          rw [hx] at hz
          exact (hxs (hz ▸ hcmem hl)).elim
        · rw [hval i' hi' j' hj' hij'] at hz
          exact hpre i' hi' j' hj' hz
    · rw [hc'r k hkl, hc'x]
      obtain ⟨i, hi, j, hj, hij, he⟩ := hother (hcmem hkl)
      refine hwit _ i hi j hj hij he fun i' hi' j' hj' hz ↦ ?_
      rcases hents i' hi' j' hj' with ⟨rfl, rfl⟩ | h
      · rcases hlast i hi j hj with h' | h' | h'
        · exact (hij h').elim
        · exact .inl h'
        · exact .inr h'
      · exact (hxs (hz ▸ h)).elim

end Replace

section XStarNodeTwo

variable {P Q V t σ l : M}

/-- `x* = (V, (t, σ[u ↦ y*]))` for `t` of type `ct` with last signature node `u`, `σ(u) = a`, and
`y*` with the signature of `a` with the new entry appended or replacing the last entry -/
theorem xStar_two_mem (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hV : V ∈ stduoci ((1 : ℕ) : M)) (hVct : ctp V = ct) (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
    (hp : !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)) ∈ tensorProdTwoTwoNds P Q)
    (htct : ctp (uc t) = ct) (hdl : dom (sig (uc t)) = succ l)
    {qa ha : M} (haσ : (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l = !(dctUZero, !(qa, ha)))
    (haN : !(dctUZero, !(qa, ha)) ∈
      tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V))))
    {c h' j : M} (hy : !(dctUZero, !(c, h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hcct : ctp (uc c) = ct) (hdc : depOf (Q ﹫ 2) c = succ j)
    (hje : sigImg (aoc V) c h' j = sigdcn V (⋃₀ dom (sig V)))
    (hsame : ∀ i ∈ j, sigImg (aoc V) c h' i = sigImg (iniSegAoc V (⋃₀ dom (sig V))) qa ha i)
    (hcase : depOf (Q ﹫ 2) qa = j ∨ (depOf (Q ﹫ 2) qa = succ j ∧ ctp (uc qa) = ct))
    (hlt : ∀ z ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)),
      z [odrOne (aoc (uc t) ﹫ ((1 : ℕ) : M))] (sigdcn (uc t) l) →
        ((σ ﹫ ((1 : ℕ) : M)) ﹫ z) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
          !(dctUZero, !(c, h')))
    (hgt : ∀ z ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)),
      (sigdcn (uc t) l) [odrOne (aoc (uc t) ﹫ ((1 : ℕ) : M))] z →
        !(dctUZero, !(c, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
          ((σ ﹫ ((1 : ℕ) : M)) ﹫ z)) :
    !(V, !(t, cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M))
      (sigdcn (uc t) l) !(dctUZero, !(c, h'))))) ∈ tensorProdTwoTwoNds P Q ∧
      IsFirstOcc (embTpSigs Q (aoc V) (uc t) (cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M))
        (sigdcn (uc t) l) !(dctUZero, !(c, h'))))) (sig V ﹫ ⋃₀ dom (sig V)) l j := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  rw [pair_mem_tensorProdTwoTwoNds_iff, aoc_iniSeg] at hp
  obtain ⟨ht, -, hσ, hemb⟩ := hp
  have hU := hemb.left
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hA := aoc_mem_aotci_of_mem_stduoci_one hUt
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, hnd'⟩ := lastSeg_facts hV hm
  have hB := tensorProdATwoAOne_mem_aotci hQ hX
  have hB' := tensorProdATwoAOne_mem_aotci hQ hX'
  have h0B : tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ∅ =
      tensorProdATwoAOne Q (aoc V) ﹫ ∅ := (tensorProdATwoAOne_val_zero_eq hQ hX hX' h0).symm
  have hsubB := isSubOne_tensorProdATwoAOne hQ hX hX' h0 hsub
  have hσB := ((mem_aotciEmbSet_iff_of_isSubOne hA hB hB' h0B hsubB).mp hσ).left
  have hlsig : l ∈ dom (sig (uc t)) := by rw [hdl]; exact mem_succ_self l
  have hu := (siglvl_eq_one hUt hlsig).right
  set u := sigdcn (uc t) l with hudef
  set y := !(dctUZero, !(c, h')) with hydef
  have hyB : y ∈ ndOf (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)) :=
    (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX).mpr (.inr hy)
  have hσc := embRep_mem_aotciEmbSet hA hB hσB hu hyB hlt hgt
  obtain ⟨hv1, -, -⟩ := embChg_vals hσB u y
  set σc := cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M)) u y) with hσcdef
  obtain ⟨hinj1, hdom1⟩ := embChg_val_one_isFunction hσB
  have hnω := dom_sig_mem_omega_of_mem_stduoci_one hUt
  have hlo : Ordinal l := ordinal_of_mem (ordinal_of_mem ordinal_omega hnω) hlsig
  have hil (i : M) (hi : i ∈ l) : i ∈ dom (sig (uc t)) := by rw [hdl]; exact mem_succ_of_mem hi
  have hval_old (i : M) (hi : i ∈ l) :
      (σc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i = (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i := by
    have hnd := (siglvl_eq_one hUt (hil i hi)).right
    rw [hv1]
    refine val_update_of_ne hinj1 _ (by rw [hdom1]; exact hnd) fun h'' ↦ ?_
    have := congrArg lbl h''
    rw [lbl_sigdcn hUt (hil i hi), lbl_sigdcn hUt hlsig] at this
    rw [this] at hi
    exact notMem_self _ hi
  have hval_new : (σc ﹫ ((1 : ℕ) : M)) ﹫ u = y := by rw [hv1]; exact val_update_self hinj1 _ _
  -- the node `a` and `y*`
  obtain ⟨qa', hqa, -, ha', hha, hae⟩ := mem_tensorProdTwoAOneNds_iff'.mp haN
  rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hae
  obtain ⟨-, rfl, rfl⟩ := hae
  have hcn : c ∈ ndOf (Q ﹫ 2) := by
    obtain ⟨c', hc', -, h'', -, hce⟩ := mem_tensorProdTwoAOneNds_iff'.mp hy
    rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hce
    rw [hce.right.left]
    exact hc'
  have hjqa : j ⊆ depOf (Q ﹫ 2) qa := by
    rcases hcase with h'' | ⟨h'', -⟩
    · rw [h'']; exact fun _ h3 ↦ h3
    · rw [h'']; exact fun _ h3 ↦ mem_succ_of_mem h3
  have hdqa : dom (sig (uc qa)) = depOf (Q ﹫ 2) qa := dom_sig_uc_eq_depOf hQ2 hqa
  have hold (i : M) (hi : i ∈ j) :
      sigImg (aoc V) c h' i ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)) := by
    rw [hsame i hi]
    exact (sigImg_spec hQ2 hqa hX' hha (by rw [hdqa]; exact hjqa hi)).left
  -- the rows
  set s := embTpSigs Q (iniSegAoc V (⋃₀ dom (sig V))) (uc t) σ with hsdef
  set s' := embTpSigs Q (aoc V) (uc t) σc with hs'def
  have hs : IsFinSeqSeq s := isFinSeqSeq_embTpSigs hQ hnω _ σ
  have hs' : IsFinSeqSeq s' := isFinSeqSeq_embTpSigs hQ hnω _ σc
  have hds : dom s = succ l := by rw [dom_embTpSigs, hdl]
  have hds' : dom s' = succ l := by rw [dom_embTpSigs, hdl]
  have hhf := ((mem_aotciEmbSet_iff.mp hσ).right.isOtciEmbedding
    (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  have hrow (i : M) (hi : i ∈ l) : s' ﹫ i = s ﹫ i := by
    rw [hs'def, embTpSigs_val hUt (hil i hi), hval_old i hi, hsdef, embTpSigs_val hUt (hil i hi)]
    exact (tpSig_lastSeg_eq hQ hV hm (hhf.isFunctionFromTo.val_mem
      (siglvl_eq_one hUt (hil i hi)).right)).symm
  have hrowl' : s' ﹫ l = tpSig Q (aoc V) y := by
    rw [hs'def, embTpSigs_val hUt hlsig, ← hudef, hval_new]
  have hrowl : s ﹫ l = tpSig Q (iniSegAoc V (⋃₀ dom (sig V))) !(dctUZero, !(qa, ha)) := by
    rw [hsdef, embTpSigs_val hUt hlsig, haσ]
  have hdy : dom (tpSig Q (aoc V) y) = succ j := by
    rw [hydef, dom_tpSig_eq hy, dom_sig_uc_eq_depOf hQ2 hcn, hdc]
  have hda : dom (tpSig Q (iniSegAoc V (⋃₀ dom (sig V))) !(dctUZero, !(qa, ha))) =
      depOf (Q ﹫ 2) qa := by rw [dom_tpSig_eq haN, hdqa]
  have hyval (i : M) (hi : i ∈ succ j) :
      tpSig Q (aoc V) y ﹫ i = !(((1 : ℕ) : M), sigImg (aoc V) c h' i) :=
    tpSig_val_eq hQ hy (by rw [dom_sig_uc_eq_depOf hQ2 hcn, hdc]; exact hi)
  have haval (i : M) (hi : i ∈ depOf (Q ﹫ 2) qa) :
      tpSig Q (iniSegAoc V (⋃₀ dom (sig V))) !(dctUZero, !(qa, ha)) ﹫ i =
        !(((1 : ℕ) : M), sigImg (iniSegAoc V (⋃₀ dom (sig V))) qa ha i) :=
    tpSig_val_eq hQ haN (by rw [hdqa]; exact hi)
  have hcon : contraction s = sig V ↾ ⋃₀ dom (sig V) := by
    have h := hU.right.left
    rwa [sig_iniSeg, aoc_iniSeg] at h
  have hc0 : IsContraction s (sig V ↾ ⋃₀ dom (sig V)) := hcon ▸ isContraction_contraction hs
  have hctr : ctrSet s = ran (sig V ↾ ⋃₀ dom (sig V)) := hc0.right.right.right.left.symm
  set e := !(((1 : ℕ) : M), sigdcn V (⋃₀ dom (sig V))) with hedef
  have hens : e ∉ ctrSet s := by rw [hctr]; exact pair_not_mem_ran_sig_restrict hV hm
  have hsf := (uociCond_of_mem_stduoci_one hV).right.right.right.left.left
  have hdm := (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV)
    (fun h' ↦ by rw [h'] at hm; exact notin_empty _ hm)).right.right
  have hsubm : ⋃₀ dom (sig V) ⊆ dom (sig V) := fun _ h' ↦ by rw [hdm]; exact mem_succ_of_mem h'
  have hdc0 : dom (sig V ↾ ⋃₀ dom (sig V)) = ⋃₀ dom (sig V) := dom_restrict_of_subset hsf hsubm
  have hes : e ∈ ctrSet s' := (mem_ctrSet_iff hs').mpr ⟨l, by rw [hds']; exact mem_succ_self _, j,
    by rw [hrowl', hdy]; exact mem_succ_self _, by rw [hrowl', hyval _ (mem_succ_self _), hje]⟩
  have hsrow (i : M) (hi : i ∈ l) (j' : M) (hj' : j' ∈ dom (s ﹫ i)) : (s ﹫ i) ﹫ j' ∈ ctrSet s :=
    (mem_ctrSet_iff hs).mpr ⟨i, by rw [hds]; exact mem_succ_of_mem hi, j', hj', rfl⟩
  have hcon' : IsContraction s' (sig V) := by
    rcases hcase with hdj | ⟨hdj, hqct⟩
    · -- `y*` appends the new entry to the signature of `a`
      refine isContraction_of_isSeqSeqExt hs hs' hc0 ⟨fun i hi j' hj' ↦ ?_, fun i' hi' j' hj' ↦ ?_⟩
        (fun i' hi' j' hj' ↦ ?_) hes hens hsf (by rw [hdc0]; exact hdm)
        (fun k hk ↦ by rw [hdc0] at hk; rw [val_restrict _ hsf hk (hsubm hk)])
        (by rw [hdc0, sig_val_eq_pair hV hm])
      · rw [hds] at hi
        rcases mem_or_eq_of_mem_succ hi with hi | rfl
        · exact ⟨by rw [hds']; exact mem_succ_of_mem hi, by rw [hrow i hi]; exact hj',
            by rw [hrow i hi]⟩
        · rw [hrowl, hda, hdj] at hj'
          refine ⟨by rw [hds']; exact mem_succ_self _,
            by rw [hrowl', hdy]; exact mem_succ_of_mem hj', ?_⟩
          rw [hrowl', hrowl, hyval j' (mem_succ_of_mem hj'), haval j' (by rw [hdj]; exact hj'),
            hsame j' hj']
      · rw [hds'] at hi'
        rcases mem_or_eq_of_mem_succ hi' with hi' | rfl
        · left
          exact ⟨by rw [hds]; exact mem_succ_of_mem hi', by rw [← hrow i' hi']; exact hj'⟩
        · rw [hrowl', hdy] at hj'
          rcases mem_or_eq_of_mem_succ hj' with hj' | rfl
          · left
            exact ⟨by rw [hds]; exact mem_succ_self _, by rw [hrowl, hda, hdj]; exact hj'⟩
          · right
            intro i hi j'' hj''
            rw [hds] at hi
            rcases mem_or_eq_of_mem_succ hi with hi | rfl
            · exact .inl hi
            · rw [hrowl, hda, hdj] at hj''
              exact .inr ⟨rfl, hj''⟩
      · rw [hds'] at hi'
        rcases mem_or_eq_of_mem_succ hi' with hi' | rfl
        · left
          rw [hrow i' hi'] at hj' ⊢
          exact hsrow i' hi' j' hj'
        · rw [hrowl'] at hj' ⊢
          rw [hdy] at hj'
          rcases mem_or_eq_of_mem_succ hj' with hj' | rfl
          · left
            rw [hyval j' (mem_succ_of_mem hj'), hsame j' hj', ← haval j' (by rw [hdj]; exact hj'),
              ← hrowl]
            exact (mem_ctrSet_iff hs).mpr ⟨_, by rw [hds]; exact mem_succ_self _, j',
              by rw [hrowl, hda, hdj]; exact hj', rfl⟩
          · right
            rw [hyval _ (mem_succ_self _), hje]
    · -- `y*` replaces the last entry of the signature of `a` by the new entry
      have hjo : Ordinal j := by
        have hdω : depOf (Q ﹫ 2) qa ∈ (ω : M) :=
          (otciCond_two hQ2).left.isTreeStructure.dep_mem_omega hqa
        have hdo := ordinal_of_mem ordinal_omega hdω
        rw [hdj] at hdo
        exact ordinal_of_mem hdo (mem_succ_self j)
      have hlastpos : ∀ i ∈ dom s, ∀ j' ∈ dom (s ﹫ i), (i = l ∧ j' = j) ∨ i ∈ l ∨
          (i = l ∧ j' ∈ j) := by
        intro i hi j' hj'
        rw [hds] at hi
        rcases mem_or_eq_of_mem_succ hi with hi | rfl
        · exact .inr (.inl hi)
        · rw [hrowl, hda, hdj] at hj'
          rcases mem_or_eq_of_mem_succ hj' with hj' | rfl
          · exact .inr (.inr ⟨rfl, hj'⟩)
          · exact .inl ⟨rfl, rfl⟩
      have hnew' : ¬ EndsWithNew s := by
        intro hew
        have hb := hU.right.right.left
        rw [ctp_iniSeg, aoc_iniSeg] at hb
        have hlast' : ⋃₀ dom (sig (uc t)) = l := by rw [hdl, sUnion_succ hlo.transitive]
        rw [hlast', (siglvl_eq_one hUt hlsig).left, ← hudef, haσ] at hb
        have hnu : nodeU !(dctUZero, !(qa, ha)) = uc qa := by
          simp only [nodeU, lbl_orderedPair, left_orderedPair]
        exact ct_ne_dct (hb.mpr ⟨htct, ⟨haN, by rw [hnu]; exact hqct⟩, hew⟩).symm
      have hocc : ∃ i ∈ dom s, ∃ j' ∈ dom (s ﹫ i), ¬(i = l ∧ j' = j) ∧
          (s ﹫ i) ﹫ j' = (s ﹫ l) ﹫ j := by
        by_contra hno
        exact hnew' (endsWithNew_of hlo hjo hds (by rw [hrowl, hda, hdj]) rfl
          fun i hi j' hj' hij hv ↦ hno ⟨i, hi, j', hj', hij, hv⟩)
      refine isContraction_of_replace_last hs hs' hc0 (by rw [hds]; exact mem_succ_self _)
        (by rw [hrowl, hda, hdj]; exact mem_succ_self _) hlastpos (hds'.trans hds.symm)
        (fun i hi ↦ ?_) (fun i hi j' hj' hij ↦ ?_)
        (by rw [hrowl', hyval _ (mem_succ_self _), hje]) hens hocc hsf (by rw [hdc0]; exact hdm)
        (fun k hk ↦ by rw [hdc0] at hk; rw [val_restrict _ hsf hk (hsubm hk)])
        (by rw [hdc0, sig_val_eq_pair hV hm])
      · rw [hds] at hi
        rcases mem_or_eq_of_mem_succ hi with hi | rfl
        · rw [hrow i hi]
        · rw [hrowl', hrowl, hdy, hda, hdj]
      · rw [hds] at hi
        rcases mem_or_eq_of_mem_succ hi with hi | rfl
        · rw [hrow i hi]
        · rw [hrowl, hda, hdj] at hj'
          have hj'j : j' ∈ j := by
            rcases mem_or_eq_of_mem_succ hj' with h'' | h''
            · exact h''
            · exact (hij ⟨rfl, h''⟩).elim
          rw [hrowl', hrowl, hyval j' hj', haval j' (by rw [hdj]; exact hj'), hsame j' hj'j]
  have hcon's : contraction s' = sig V := (eq_contraction_of_isContraction hs' hcon').symm
  have hjo : Ordinal j := by
    have hdω : depOf (Q ﹫ 2) c ∈ (ω : M) :=
      (otciCond_two hQ2).left.isTreeStructure.dep_mem_omega hcn
    have hdo := ordinal_of_mem ordinal_omega hdω
    rw [hdc] at hdo
    exact ordinal_of_mem hdo (mem_succ_self j)
  have hpos : (s' ﹫ l) ﹫ j = e := by rw [hrowl', hyval _ (mem_succ_self _), hje]
  have huniq : ∀ i ∈ dom s', ∀ j' ∈ dom (s' ﹫ i), ¬(i = l ∧ j' = j) → (s' ﹫ i) ﹫ j' ≠ e := by
      intro i hi j' hj' hij hv
      rw [hds'] at hi
      rcases mem_or_eq_of_mem_succ hi with hi | hil
      · rw [hrow i hi] at hj' hv
        exact hens (by rw [← hv]; exact hsrow i hi j' hj')
      · rw [hil] at hj' hv hij
        rw [hrowl', hdy] at hj'
        rw [hrowl'] at hv
        have hj'j : j' ∈ j := by
          rcases mem_or_eq_of_mem_succ hj' with h'' | h''
          · exact h''
          · exact (hij ⟨rfl, h''⟩).elim
        rw [hyval j' hj', hedef, orderedPair_eq_orderedPair_iff] at hv
        exact ((hnd' _).mp (hold j' hj'j)).right hv.right
  have hfo : IsFirstOcc s' (sig V ﹫ ⋃₀ dom (sig V)) l j := by
    rw [sig_val_eq_pair hV hm]
    refine ⟨by rw [hds']; exact mem_succ_self _, by rw [hrowl', hdy]; exact mem_succ_self _, hpos,
      fun i' hi' j' hj' hv ↦ ?_⟩
    by_contra hno'
    exact huniq i' hi' j' hj' (fun h ↦ hno' (.inl ⟨h.left.symm, h.right.symm⟩)) hv
  refine ⟨?_, hfo⟩
  rw [pair_mem_tensorProdTwoTwoNds_iff]
  refine ⟨ht, hV, hσc, ⟨hσc, hcon's, ?_, fun h3 ↦ ?_⟩, fun h' ↦ ?_⟩
  · have hlast' : ⋃₀ dom (sig (uc t)) = l := by rw [hdl, sUnion_succ hlo.transitive]
    rw [hlast']
    refine iff_of_true hVct ⟨htct, ?_, ?_⟩
    · rw [(siglvl_eq_one hUt hlsig).left, ← hudef, hval_new]
      have hnu : nodeU y = uc c := by simp only [nodeU, hydef, lbl_orderedPair, left_orderedPair]
      exact ⟨hy, by rw [hnu]; exact hcct⟩
    · exact endsWithNew_of (e := e) hlo hjo hds' (by rw [hrowl', hdy]) hpos huniq
  · exfalso
    have hd3 : dom V = ((3 : ℕ) : M) :=
      (uociCond_of_mem_stduoci_one hV).right.right.right.right.right.right.left.mpr (.inr hVct)
    rw [hd3] at h3
    exact notMem_self _ h3
  · rw [h', dom_empty] at hm
    exact (notin_empty _ hm).elim

end XStarNodeTwo

section XStarPrt

/-! ### The parent of `x*` -/

variable {P Q V t σ tc : M}

/-- The successor of the image `y` of a node `x` with `uc x = V` is the least old node `a`
above `y` -/
theorem prtSucc_eq_of_least (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) {x y a : M} (hxV : uc x = V) (himg : prtImg Q x = y)
    (haN : a ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
    (hya : y [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] a)
    (hamin : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
      y [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
        z = a ∨ a [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) :
    prtSucc Q x = a := by
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, -⟩ := lastSeg_facts hV hm
  have hB1 := val_mem_otci_of_mem_aotci (tensorProdATwoAOne_mem_aotci hQ hX) (mem_succ_self _)
  have hO := (rtlosOf_of_mem_otci_one hB1).left
  have hBsub := isSubOne_tensorProdATwoAOne hQ hX hX' h0 hsub
  rw [prtSucc, prtAbove, prtOdr, prtSmall, prtUc, hxV, uociEmbTgt, uociEmbTgt, aoc_iniSeg, himg]
  exact sUnion_least_aboveIn_eq hO.isAsymmOn hBsub.left haN hya hamin

/-- The parent of the case-`1` node `x* = (V, (t*, σ ∪ {s ↦ y*}))` is `(V | m, (t, σ))` -/
theorem prt_xStar_one (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hV : V ∈ stduoci ((1 : ℕ) : M)) (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
    (hm0 : ⋃₀ dom (sig V) ≠ ∅) (ht : t ∈ ndOf P) (htc : tc ∈ chdOf P t)
    (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t))
      (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V)))))
    (hsU : sigdcn (uc tc) (dom (sig (uc t))) ∉ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) {y a j : M}
    (hfo : IsFirstOcc (embTpSigs Q (aoc V) (uc tc) (cc (σ ↾ ((1 : ℕ) : M))
      (update (σ ﹫ ((1 : ℕ) : M)) (sigdcn (uc tc) (dom (sig (uc t)))) y)))
      (sig V ﹫ ⋃₀ dom (sig V)) (dom (sig (uc t))) j)
    (haN : a ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
    (hya : y [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] a)
    (hamin : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
      y [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
        z = a ∨ a [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z)
    (hlv : ucflvl (uc t) ≠ ∅) (hucfn : ucfdcn (uc t) ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)))
    (ha : (σ ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc t) = a) :
    tensorProdTwoTwoPrt P Q !(V, !(tc, cc (σ ↾ ((1 : ℕ) : M))
      (update (σ ﹫ ((1 : ℕ) : M)) (sigdcn (uc tc) (dom (sig (uc t)))) y))) =
      !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)) := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have htcn := mem_ndOf_of_mem_chdOf hS htc
  have hUtc := uc_mem_stduoci_of_mem_otci_two hP htcn
  obtain ⟨-, hanc⟩ := ancOf_eq_of_mem_chdOf hS htc
  have hn : dom (sig (uc t)) = depOf P t := dom_sig_uc_eq_depOf hP ht
  set sn := sigdcn (uc tc) (dom (sig (uc t))) with hsndef
  obtain ⟨hv1, -, -⟩ := embChg_vals hσ sn y
  obtain ⟨hinj1, hdom1⟩ := embChg_val_one_isFunction hσ
  set σc := cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M)) sn y) with hσcdef
  have hs' := isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUtc) (aoc V) σc
  rw [tensorProdTwoTwoPrt, if_neg (by rw [uc_orderedPair]; exact hm0), prtTwo, prtUc,
    uc_orderedPair, prtLbl]
  have hnQ := nodeQ_orderedPair V tc σc
  have hnU := nodeU_orderedPair V tc σc
  have hnH := nodeH_orderedPair V tc σc
  have hpos : prtPos Q !(V, !(tc, σc)) = !(dom (sig (uc t)), j) := by
    rw [prtPos, prtSeqs, prtEntry, uc_orderedPair, hnU, hnH]
    exact firstOccPos_eq hs' hfo
  have hrow : prtRow Q !(V, !(tc, σc)) = dom (sig (uc t)) := by
    rw [prtRow, hpos, left_orderedPair]
  have hancL : prtAncL P Q !(V, !(tc, σc)) = t := by rw [prtAncL, hnQ, hrow, hn, hanc]
  have hnode : prtNode Q !(V, !(tc, σc)) = sn := by rw [prtNode, hnU, hrow]
  have himg : prtImg Q !(V, !(tc, σc)) = y := by
    rw [prtImg, hnH, hnode, hv1, val_update_self hinj1]
  have hsucc := prtSucc_eq_of_least hQ hV hm uc_orderedPair himg haN hya hamin
  have hucfI : prtUcfImg P Q !(V, !(tc, σc)) = a := by
    rw [prtUcfImg, hnH, hancL, ucfImg, if_neg hlv, hv1,
      val_update_of_ne hinj1 _ (by rw [hdom1]; exact hucfn)
        (fun h ↦ hsU (by rw [← h]; exact hucfn)), ha]
  rw [if_pos (show PrtCase P Q !(V, !(tc, σc)) from hsucc.trans hucfI.symm), prtLblOne, hancL,
    cutRes, hnH, embRestrict_embExt hσ hsU]

/-- The parent of the root-case node `x* = (V, (t*, σ ∪ {s ↦ y*}))` with `|V_sig| = 1` is
`(V | 0, (t, σ))` -/
theorem prt_xStar_root (hP : P ∈ otci ((2 : ℕ) : M)) {B : M} (hm0 : ⋃₀ dom (sig V) = ∅)
    (ht : t ∈ rtOf P) (htc : tc ∈ chdOf P t)
    (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) B)
    (hsU : sigdcn (uc tc) (dom (sig (uc t))) ∉ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) {y : M} :
    tensorProdTwoTwoPrt P Q !(V, !(tc, cc (σ ↾ ((1 : ℕ) : M))
      (update (σ ﹫ ((1 : ℕ) : M)) (sigdcn (uc tc) (dom (sig (uc t)))) y))) =
      !(iniSeg V ∅, !(t, σ)) := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  obtain ⟨-, hanc⟩ := ancOf_eq_of_mem_chdOf hS htc
  have hd0 : depOf P t = ∅ := (TreeStructure.mem_rt_iff.mp ht).right
  rw [hd0] at hanc
  rw [tensorProdTwoTwoPrt, if_pos (by rw [uc_orderedPair]; exact hm0), prtOne, prtUc,
    uc_orderedPair, hm0, prtRootAnc, cutRes, nodeQ_orderedPair, nodeH_orderedPair, hanc,
    embRestrict_embExt hσ hsU]

/-- The parent of the case-`2` node `x* = (V, (t, σ[u ↦ y*]))` is `(V | m, (t, σ))` -/
theorem prt_xStar_two (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hV : V ∈ stduoci ((1 : ℕ) : M)) (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
    (hm0 : ⋃₀ dom (sig V) ≠ ∅) (ht : t ∈ ndOf P) (htct : ctp (uc t) = ct) {l : M}
    (hdl : dom (sig (uc t)) = succ l)
    (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t))
      (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))))) {y a j : M}
    (hfo : IsFirstOcc (embTpSigs Q (aoc V) (uc t) (cc (σ ↾ ((1 : ℕ) : M))
      (update (σ ﹫ ((1 : ℕ) : M)) (sigdcn (uc t) l) y))) (sig V ﹫ ⋃₀ dom (sig V)) l j)
    (haN : a ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
    (hane : a ≠ ∅)
    (hya : y [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] a)
    (hamin : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
      y [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
        z = a ∨ a [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z)
    (ha : (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l = a) :
    tensorProdTwoTwoPrt P Q !(V, !(t, cc (σ ↾ ((1 : ℕ) : M))
      (update (σ ﹫ ((1 : ℕ) : M)) (sigdcn (uc t) l) y))) =
      !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)) := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', -, -, -⟩ := lastSeg_facts hV hm
  have hB' := tensorProdATwoAOne_mem_aotci hQ hX'
  have hlsig : l ∈ dom (sig (uc t)) := by rw [hdl]; exact mem_succ_self l
  have hdt : depOf P t = succ l := by rw [← dom_sig_uc_eq_depOf hP ht, hdl]
  have hl : l ∈ depOf P t := by rw [hdt]; exact mem_succ_self l
  have hu := (siglvl_eq_one hUt hlsig).right
  set u := sigdcn (uc t) l with hudef
  obtain ⟨hv1, -, -⟩ := embChg_vals hσ u y
  obtain ⟨hinj1, hdom1⟩ := embChg_val_one_isFunction hσ
  set σc := cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M)) u y) with hσcdef
  have hs' := isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUt) (aoc V) σc
  rw [tensorProdTwoTwoPrt, if_neg (by rw [uc_orderedPair]; exact hm0), prtTwo, prtUc,
    uc_orderedPair, prtLbl]
  have hnQ := nodeQ_orderedPair V t σc
  have hnU := nodeU_orderedPair V t σc
  have hnH := nodeH_orderedPair V t σc
  have hpos : prtPos Q !(V, !(t, σc)) = !(l, j) := by
    rw [prtPos, prtSeqs, prtEntry, uc_orderedPair, hnU, hnH]
    exact firstOccPos_eq hs' hfo
  have hrow : prtRow Q !(V, !(t, σc)) = l := by rw [prtRow, hpos, left_orderedPair]
  have hancL : prtAncL P Q !(V, !(t, σc)) = ancOf P t l := by rw [prtAncL, hnQ, hrow]
  have htt : ancOf P t (succ l) = t := by rw [← hdt]; exact hTS.anc_dep ht
  have hancS : prtAncS P Q !(V, !(t, σc)) = t := by rw [prtAncS, ancSucc, hnQ, hrow, htt]
  have hnode : prtNode Q !(V, !(t, σc)) = u := by rw [prtNode, hnU, hrow]
  have himg : prtImg Q !(V, !(t, σc)) = y := by
    rw [prtImg, hnH, hnode, hv1, val_update_self hinj1]
  have hsucc := prtSucc_eq_of_least hQ hV hm uc_orderedPair himg haN hya hamin
  have hhf := ((mem_aotciEmbSet_iff.mp hσ).right.isOtciEmbedding
    (mem_succ_self _)).isEmbedding.isEmbedding_ts.isInjectionFromTo
  have hncase : ¬ PrtCase P Q !(V, !(t, σc)) := by
    rw [PrtCase, hsucc, prtUcfImg, hnH, hancL]
    by_cases hl0 : l = ∅
    · rw [hl0, ucfImg_ancOf_empty hP ht]
      exact hane
    · obtain ⟨hlv, ⟨i0, hi0, hr⟩, -⟩ := ucf_anc_rel hP ht hl hl0 hB' hσ
      have hlv1 : ucflvl (uc (ancOf P t l)) ≠ ∅ := by
        rw [ucflvl, hlv, lvl_orderedPair]
        exact natCast_one_ne_empty
      have hi0t : i0 ∈ dom (sig (uc t)) := by rw [hdl]; exact mem_succ_of_mem hi0
      have hnd0 := (siglvl_eq_one hUt hi0t).right
      have hne : sigdcn (uc t) i0 ≠ u := by
        intro h''
        have := congrArg lbl h''
        rw [lbl_sigdcn hUt hi0t, hudef, lbl_sigdcn hUt hlsig] at this
        rw [this] at hi0
        exact notMem_self _ hi0
      rw [ucfImg, if_neg hlv1, hr, hv1, val_update_of_ne hinj1 _ (by rw [hdom1]; exact hnd0) hne,
        ← ha]
      intro h''
      exact hne (hhf.right hu hnd0 h'').symm
  have hct : ctChd P (ancOf P t l) (aoc (uc t)) = t := by
    have hc := hTS.anc_succ_mem_chd ht hl
    change ancOf P t (succ l) ∈ chdOf P (ancOf P t l) at hc
    rw [htt] at hc
    exact eq_ctChd_of_ctp_eq_ct (natCast_mem_omega 2) natCast_two_ne_empty hP
      (hTS.anc_mem_nd ht (mem_succ_of_mem hl)).left hc htct
  rw [if_neg hncase, prtLblTwo, prtCt, prtEmbTwo, hancL, hancS, hnH, hnode, hsucc, hct, ← ha,
    embUpd_embRep hσ hu]

end XStarPrt

section ChdGeneric

/-! ### Generic facts for the analysis of the children -/

variable {Q V : M}

/-- If the union of the least elements of `A` is a nonempty `E`, then `E` is the least element -/
theorem mem_of_sUnion_least_eq {O S A E : M} (hO : IsAsymmOn O S) (hA : A ⊆ S)
    (h : ⋃₀ (A ∩₀ fun z ↦ IsLeastIn O A z) = E) (hE : E ≠ ∅) : E ∈ A ∧ IsLeastIn O A E := by
  by_cases hC : (A ∩₀ fun z ↦ IsLeastIn O A z) = ∅
  · rw [hC, sUnion_empty] at h
    exact (hE h.symm).elim
  have hC' : (A ∩₀ fun z ↦ IsLeastIn O A z) ≠ ∅ := hC
  rw [ne_empty_iff] at hC'
  obtain ⟨z, hz⟩ := hC'
  have hz' := (mem_comprehension_iff ..).mp hz
  have hCz : (A ∩₀ fun z ↦ IsLeastIn O A z) = {z} := by
    ext z'
    rw [mem_singleton_iff]
    constructor
    · intro hz''
      obtain ⟨hz'A, hz'l⟩ := (mem_comprehension_iff ..).mp hz''
      rcases hz'.right z' hz'A with h1 | h1
      · exact h1
      rcases hz'l z hz'.left with h2 | h2
      · exact h2.symm
      · exact (hO.asymm (hA hz'.left) (hA hz'A) h1 h2).elim
    · rintro rfl
      exact hz
  rw [hCz, sUnion_singleton] at h
  subst h
  exact hz'

/-- The successor of the image of a node `x` with `uc x = V`, if nonempty, is the least old node
above the image -/
theorem least_of_prtSucc_eq (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) {x a : M} (hxV : uc x = V) (h : prtSucc Q x = a)
    (ha : a ≠ ∅) :
    a ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) ∧
      (prtImg Q x) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] a ∧
      ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
        (prtImg Q x) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
          z = a ∨ a [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z := by
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, -⟩ := lastSeg_facts hV hm
  have hB1 := val_mem_otci_of_mem_aotci (tensorProdATwoAOne_mem_aotci hQ hX) (mem_succ_self _)
  have hO := (rtlosOf_of_mem_otci_one hB1).left
  have hBsub := isSubOne_tensorProdATwoAOne hQ hX hX' h0 hsub
  rw [prtSucc, prtAbove, prtOdr, prtSmall, prtUc, hxV, uociEmbTgt, uociEmbTgt, aoc_iniSeg] at h
  have hAS : aboveIn (odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
      (ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M))) (prtImg Q x) ⊆
      ndOf (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)) :=
    fun z hz ↦ hBsub.left (mem_aboveIn_iff.mp hz).left
  obtain ⟨hmem, hl⟩ := mem_of_sUnion_least_eq hO.isAsymmOn hAS h ha
  rw [mem_aboveIn_iff] at hmem
  refine ⟨hmem.left, hmem.right, fun z hz hyz ↦ hl z (mem_aboveIn_iff.mpr ⟨hz, hyz⟩)⟩

/-- If the rows end with a new entry, the first occurrence of the newest entry of the
contraction is the last position -/
theorem firstOcc_last_of_endsWithNew {s n l k : M} (hs : IsFinSeqSeq s)
    (hn : dom (contraction s) = succ n) (hfo : IsFirstOcc s (contraction s ﹫ n) l k)
    (hew : EndsWithNew s) : l = lastIdx s ∧ k = lastIdx (lastSeq s) := by
  obtain ⟨hL, hJ, huniq⟩ := hew
  by_cases hz : lastEntry s = contraction s ﹫ n
  · exact (huniq l hfo.left k hfo.right.left (hfo.right.right.left.trans hz.symm))
  · have hzs : lastEntry s ∈ ctrSet s := (mem_ctrSet_iff hs).mpr ⟨_, hL, _, hJ, rfl⟩
    obtain ⟨i, hi, j, hj, hv, hlt⟩ := occ_before hs hn hfo _ hzs hz
    obtain ⟨rfl, rfl⟩ := huniq i hi j hj hv
    have hdω := hs.right.left
    have hds : dom s = succ (lastIdx s) := (sUnion_mem_of_ne_empty hdω
      (fun h ↦ by rw [h] at hL; exact notin_empty _ hL)).right.right
    have hLo := ordinal_of_mem_dom hs hL
    have hl := hfo.left
    rw [hds] at hl
    rcases hlt with h' | ⟨h1, h2⟩
    · rcases mem_or_eq_of_mem_succ hl with hl | hl
      · exact (notMem_self _ (hLo.transitive _ hl h')).elim
      · rw [hl] at h'; exact (notMem_self _ h').elim
    · have hdl := (hs.right.right _ hfo.left).right
      have hds' : dom (s ﹫ l) = succ (lastIdx (lastSeq s)) := by
        rw [← h1]
        exact (sUnion_mem_of_ne_empty (hs.right.right _ hL).right
          (fun h ↦ by rw [h] at hj; exact notin_empty _ hj)).right.right
      have hk := hfo.right.left
      rw [hds'] at hk
      have hJo := ordinal_of_mem_dom_val hs hL hJ
      rcases mem_or_eq_of_mem_succ hk with hk | hk
      · exact (notMem_self _ (hJo.transitive _ hk h2)).elim
      · rw [hk] at h2; exact (notMem_self _ h2).elim

/-- A node of `Q(2) ⊗ X` with the new entry in its signature is not old -/
theorem not_mem_lastSeg_of_sigImg_eq (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hV : V ∈ stduoci ((1 : ℕ) : M)) (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) {c h' j : M}
    (hy : !(dctUZero, !(c, h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hj : j ∈ dom (sig (uc c))) (he : sigImg (aoc V) c h' j = sigdcn V (⋃₀ dom (sig V))) :
    !(dctUZero, !(c, h')) ∉
      ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  obtain ⟨hX', -, hsub, hnd'⟩ := lastSeg_facts hV hm
  intro hmem
  rw [mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX'] at hmem
  rcases hmem with hz | hz
  · rw [base_lastSeg_eq hV hm] at hz
    exact not_isTpTwo_of_mem_base hQ hz hy
  · obtain ⟨c', hc', -, h'', hh'', hce⟩ := mem_tensorProdTwoAOneNds_iff'.mp hz
    rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hce
    obtain ⟨-, rfl, rfl⟩ := hce
    obtain ⟨hz1, hz2⟩ := sigImg_spec hQ2 hc' hX' hh'' hj
    obtain ⟨c3, -, -, h3, hh3, hce3⟩ := mem_tensorProdTwoAOneNds_iff'.mp hy
    rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hce3
    obtain ⟨-, rfl, rfl⟩ := hce3
    have hz3 := (sigImg_spec hQ2 hc' hX hh3 hj).right
    rw [he, hz2] at hz3
    have heX := (siglvl_eq_one hV hm).right
    exact ((hnd' _).mp hz1).right (relabelOne_injective hX1 (hsub.left hz1) heX hz3)

end ChdGeneric

section ChdOrder

variable {Q V : M}

/-- An old node below `a` is below `y*` -/
theorem lt_yStar_of_lt (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) {y a z : M}
    (hyB : y ∈ ndOf (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
    (hyold : y ∉ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
    (hamin : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
      y [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
        z = a ∨ a [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z)
    (hz : z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
    (hza : z [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] a) :
    z [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] y := by
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, -⟩ := lastSeg_facts hV hm
  have hB1 := val_mem_otci_of_mem_aotci (tensorProdATwoAOne_mem_aotci hQ hX) (mem_succ_self _)
  have hO := (rtlosOf_of_mem_otci_one hB1).left
  have hBsub := isSubOne_tensorProdATwoAOne hQ hX hX' h0 hsub
  rcases hO.isTrichotomousOn z (hBsub.left hz) y hyB with h | rfl | h
  · exact h
  · exact (hyold hz).elim
  · rcases hamin z hz h with rfl | h'
    · exact (hO.irrefl _ hza).elim
    · exact (hO.asymm h' hza).elim

/-- A node at least `a` is above `y*` -/
theorem yStar_lt_of_le (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    {y a z : M} (hya : y [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] a)
    (haz : z = a ∨ a [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) :
    y [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z := by
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hB1 := val_mem_otci_of_mem_aotci (tensorProdATwoAOne_mem_aotci hQ hX) (mem_succ_self _)
  have hO := (rtlosOf_of_mem_otci_one hB1).left
  rcases haz with rfl | h
  · exact hya
  · exact hO.trans hya h

end ChdOrder

section FirstOccData

variable {P Q V t σ : M}

/-- The first occurrence `(l, k)` of the newest entry in the rows of a node `(V, (t, σ))`, the
image `σ(w_l) = (q, h)` from `Q(2)` and the first occurrence `k` in its signature -/
theorem firstOcc_data (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hx : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q) (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) :
    ∃ l k q h, IsFirstOcc (embTpSigs Q (aoc V) (uc t) σ) (sig V ﹫ ⋃₀ dom (sig V)) l k ∧
      l ∈ depOf P t ∧ (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l = !(dctUZero, !(q, h)) ∧
      q ∈ ndOf (Q ﹫ 2) ∧ !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) ∧
      h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)) ∧
      k ∈ depOf (Q ﹫ 2) q ∧ (∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V))) ∧
      sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V)) ∧
      prtRow Q !(V, !(t, σ)) = l ∧
      prtImg Q !(V, !(t, σ)) = !(dctUZero, !(q, h)) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hx
  obtain ⟨ht, hV, hσ, hemb⟩ := hx
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
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
  have hnU : nodeU !(V, !(t, σ)) = uc t := nodeU_orderedPair _ _ _
  have hnH : nodeH !(V, !(t, σ)) = σ := nodeH_orderedPair _ _ _
  have hpos : prtPos Q !(V, !(t, σ)) = !(l, k) := by
    rw [prtPos, prtSeqs, prtEntry, uc_orderedPair, hnU, hnH]
    exact firstOccPos_eq hs hfo
  have hrow : prtRow Q !(V, !(t, σ)) = l := by rw [prtRow, hpos, left_orderedPair]
  have hnode : prtNode Q !(V, !(t, σ)) = sigdcn (uc t) l := by rw [prtNode, hnU, hrow]
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
  exact ⟨l, k, q, h, hfo, hl', hyeq, hq, hyC, hh, hk', hfirst, hje, hrow,
    by rw [prtImg, hnH, hnode, hyeq]⟩

end FirstOccData

section LeastOne

/-! ### `x*` is the least child with its key, case `t` discontinuous -/

variable {P Q V t σ tc c h' qa ha : M}

/-- A child `r` of `p = (V | m, (t, σ))` with the key and signature of `V`, for `t`
discontinuous and `m > 0`, is at least `x* = (V, (t*, σ ∪ {s ↦ y*}))`, and equal to it if `r` is
continuous -/
theorem chd_cmp_xStar_one (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hV : V ∈ stduoci ((1 : ℕ) : M)) (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
    (hm0 : ⋃₀ dom (sig V) ≠ ∅)
    (hp : !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)) ∈ tensorProdTwoTwoNds P Q)
    (htdct : ctp (uc t) = dct) (htc : tc ∈ chdOf P t) (htcchd : chdOf P tc = ∅)
    (htcmin : ∀ c' ∈ chdOf P t, c' = tc ∨ tc [sblOdrOf P] c')
    (htcct : ctp (uc tc) = ct)
    (hsU : sigdcn (uc tc) (dom (sig (uc t))) ∉ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)))
    (hx : !(V, !(tc, cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M))
      (sigdcn (uc tc) (dom (sig (uc t)))) !(dctUZero, !(c, h'))))) ∈ tensorProdTwoTwoNds P Q)
    (hlv : ucflvl (uc t) ≠ ∅) (hucfn : ucfdcn (uc t) ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)))
    (hσa : (σ ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc t) = !(dctUZero, !(qa, ha)))
    (hY : IsYStarLe Q V qa ha c h')
    {V' t' σ' : M} (hr : !(V', !(t', σ')) ∈ tensorProdTwoTwoNds P Q)
    (hprt : tensorProdTwoTwoPrt P Q !(V', !(t', σ')) = !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)))
    (haoc : aoc V' = aoc V) (hsig : sig V' = sig V) :
    (!(V', !(t', σ')) = !(V, !(tc, cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M))
      (sigdcn (uc tc) (dom (sig (uc t)))) !(dctUZero, !(c, h'))))) ∨
      !(V, !(tc, cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M))
        (sigdcn (uc tc) (dom (sig (uc t)))) !(dctUZero, !(c, h')))))
        [tensorProdTwoTwoOdr P Q] !(V', !(t', σ'))) ∧
    (ctp V' = ct → !(V', !(t', σ')) = !(V, !(tc, cc (σ ↾ ((1 : ℕ) : M))
      (update (σ ﹫ ((1 : ℕ) : M)) (sigdcn (uc tc) (dom (sig (uc t))))
        !(dctUZero, !(c, h')))))) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  set sn := sigdcn (uc tc) (dom (sig (uc t))) with hsndef
  set y := !(dctUZero, !(c, h')) with hydef
  set σc := cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M)) sn y) with hσcdef
  have hp' := hp
  rw [pair_mem_tensorProdTwoTwoNds_iff, aoc_iniSeg] at hp'
  obtain ⟨ht, -, hσ, -⟩ := hp'
  have hr' := hr
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hr'
  obtain ⟨ht', hV', hσ', hemb'⟩ := hr'
  have hx' := hx
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hx'
  obtain ⟨htcn, -, hσc, hembx⟩ := hx'
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hUt' := uc_mem_stduoci_of_mem_otci_two hP ht'
  have hUtc := uc_mem_stduoci_of_mem_otci_two hP htcn
  have hm' : ⋃₀ dom (sig V') ∈ dom (sig V') := by rw [hsig]; exact hm
  have hmeq : ⋃₀ dom (sig V') = ⋃₀ dom (sig V) := by rw [hsig]
  have hsdV (i : M) : sigdcn V' i = sigdcn V i := by rw [sigdcn, sigdcn, hsig]
  -- the parent of `r`
  have hm0' : ⋃₀ dom (sig (uc !(V', !(t', σ')))) ≠ ∅ := by rw [uc_orderedPair, hmeq]; exact hm0
  rw [tensorProdTwoTwoPrt, if_neg hm0', prtTwo, orderedPair_eq_orderedPair_iff] at hprt
  obtain ⟨huc, hlbl⟩ := hprt
  rw [prtUc, uc_orderedPair, hmeq] at huc
  have hX'eq : iniSegAoc V' (⋃₀ dom (sig V')) = iniSegAoc V (⋃₀ dom (sig V)) := by
    rw [← aoc_iniSeg, hmeq, huc, aoc_iniSeg]
  -- the first occurrence of the newest entry in the rows of `r`
  obtain ⟨l, k, q₁, h₁, hfo, hl, hy₁, hq₁, hy₁N, hh₁, hk, hfirst, hje, hrow, himg⟩ :=
    firstOcc_data hP hQ hr hm'
  rw [haoc, hsdV, hmeq] at hfirst hje
  rw [haoc] at hy₁N hh₁
  have hnQ := nodeQ_orderedPair V' t' σ'
  have hnH := nodeH_orderedPair V' t' σ'
  have hancL : prtAncL P Q !(V', !(t', σ')) = ancOf P t' l := by rw [prtAncL, hnQ, hrow]
  have hancS : prtAncS P Q !(V', !(t', σ')) = ancOf P t' (succ l) := by
    rw [prtAncS, ancSucc, hnQ, hrow]
  have hdt' := hTS.dep_mem_omega ht'
  have hls : l ∈ succ (depOf P t') := mem_succ_of_mem hl
  obtain ⟨htl, hdtl⟩ := hTS.anc_mem_nd ht' hls
  change ancOf P t' l ∈ ndOf P at htl
  change depOf P (ancOf P t' l) = l at hdtl
  have hc1 : ancOf P t' (succ l) ∈ chdOf P (ancOf P t' l) := hTS.anc_succ_mem_chd ht' hl
  -- the case of the parent
  have hcase : PrtCase P Q !(V', !(t', σ')) := by
    by_contra hcase
    rw [prtLbl, if_neg hcase, prtLblTwo, orderedPair_eq_orderedPair_iff, prtCt, hancL,
      hancS] at hlbl
    obtain ⟨-, -, -, hct, -⟩ := ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hP htl hc1
    rw [hlbl.left, htdct] at hct
    exact ct_ne_dct hct.symm
  rw [prtLbl, if_pos hcase, prtLblOne, orderedPair_eq_orderedPair_iff, hancL, cutRes,
    hnH] at hlbl
  obtain ⟨htl', hσeq⟩ := hlbl
  -- `t = t'_l`, `σ = σ' ↾ t`
  have hdtl' : depOf P t = l := by rw [← htl', hdtl]
  have hn : dom (sig (uc t)) = l := by rw [dom_sig_uc_eq_depOf hP ht, hdtl']
  have hanct : ancOf P t' l = t := htl'
  -- the successor of `σ'(w'_l)` is `a`
  have hσ'1 := embChg_val_one_isFunction hσ'
  have hsubt := (uc_ancOf_rel hP ht' hls).right
  rw [hanct] at hsubt hσeq
  have hσval (z : M) (hz : z ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) :
      (σ ﹫ ((1 : ℕ) : M)) ﹫ z = (σ' ﹫ ((1 : ℕ) : M)) ﹫ z := by
    rw [← hσeq, embRestrict_val _ _ natCast_one_mem_two,
      val_restrict _ hσ'1.left hz (by rw [hσ'1.right]; exact hsubt.left hz)]
  have hsucc : prtSucc Q !(V', !(t', σ')) = !(dctUZero, !(qa, ha)) := by
    rw [hcase, prtUcfImg, hnH, hancL, hanct, ucfImg, if_neg hlv, ← hσval _ hucfn, hσa]
  obtain ⟨haN, hya₁, hamin₁⟩ := least_of_prtSucc_eq hQ hV' hm' uc_orderedPair hsucc
    (orderedPair_ne_empty _ _)
  rw [hX'eq] at haN
  rw [haoc, himg] at hya₁
  rw [hX'eq, haoc, himg] at hamin₁
  obtain ⟨hle, hcteq⟩ := hY q₁ h₁ k hq₁ hy₁N hh₁ hk hfirst hje hya₁ hamin₁
  -- the coordinates of `x*` and of `r`
  obtain ⟨hsigtc, hdtc, -, -⟩ := uc_rel_of_mem_chdOf hP ht htc
  obtain ⟨hdtcd, hanctc⟩ := ancOf_eq_of_mem_chdOf hS htc
  obtain ⟨hv1, -, -⟩ := embChg_vals hσ sn y
  obtain ⟨hinj1, hdom1⟩ := embChg_val_one_isFunction hσ
  have hsftc := (uociCond_of_mem_stduoci_one hUtc).right.right.right.left.left
  have hsdtc (i : M) (hi : i ∈ l) : sigdcn (uc tc) i = sigdcn (uc t) i := by
    rw [← hn] at hi
    rw [sigdcn, sigdcn, hsigtc, val_restrict _ hsftc hi (by rw [hdtc]; exact mem_succ_of_mem hi)]
  have hsdt' (i : M) (hi : i ∈ l) : sigdcn (uc t') i = sigdcn (uc t) i := by
    rw [← sigdcn_anc hP ht' hls hi, hanct]
  have hold (i : M) (hi : i ∈ l) : sigdcn (uc t) i ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)) :=
    (siglvl_eq_one hUt (by rw [hn]; exact hi)).right
  have hσcold (i : M) (hi : i ∈ l) :
      (σc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) i = (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i := by
    rw [hv1, hsdtc i hi]
    exact val_update_of_ne hinj1 _ (by rw [hdom1]; exact hold i hi)
      fun h'' ↦ hsU (h'' ▸ hold i hi)
  have hσ'old (i : M) (hi : i ∈ l) :
      (σ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t') i = (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i := by
    rw [hsdt' i hi, hσval _ (hold i hi)]
  have hσcnew : (σc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) l = y := by
    rw [← hn, hv1]
    exact val_update_self hinj1 _ _
  have hdtcl : depOf P tc = succ l := by rw [hdtcd, hdtl']
  have hlo : Ordinal l := ordinal_of_mem (ordinal_of_mem ordinal_omega hdt') hl
  have hpre : ∀ i ∈ l, tensorProdTwoAOneSeq P !(tc, σc) ﹫ i =
      tensorProdTwoAOneSeq P !(t', σ') ﹫ i := by
    intro i hi
    have hitc : i ∈ depOf P tc := by rw [hdtcl]; exact mem_succ_of_mem hi
    have hit' : i ∈ depOf P t' := (ordinal_of_mem ordinal_omega hdt').transitive _ hl hi
    rw [tensorProdTwoAOneSeq_val hP htcn hitc, tensorProdTwoAOneSeq_val hP ht' hit',
      hσcold i hi, hσ'old i hi]
    have hsi : succ i ∈ succ l := succ_mem_succ_of_mem (ordinal_omega.transitive _ hdt' hl) hi
    have hltc : l ∈ succ (depOf P tc) := by
      rw [hdtcl]
      exact mem_succ_of_mem (mem_succ_self l)
    rw [← ancOf_ancOf (isSLOT_of_mem_otci hP) htcn hltc hsi,
      ← ancOf_ancOf (isSLOT_of_mem_otci hP) ht' hls hsi, hanct, ← hdtl', hanctc]
  have hcmp : (σc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) l = (σ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t') l ∨
      ((σc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) l)
        [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
        ((σ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t') l) := by
    rw [hσcnew, hy₁]
    exact hle
  have hc1' : ancOf P t' (succ l) ∈ chdOf P t := by rw [← hanct]; exact hc1
  refine ⟨?_, fun hct ↦ ?_⟩
  · rcases eq_or_rel_tensorProdTwoTwoOdr_of_seq_prefix hP hQ hx hr haoc.symm hdtcl hl hpre
      (hcmp.elim (fun he ↦ .inr ⟨he, htcchd, (htcmin _ hc1').imp_left Eq.symm⟩) .inl) with
      h'' | h''
    · exact .inl h''.symm
    · exact .inr h''
  -- `r` is continuous: it is `x*`
  have hb := hemb'.left.right.right.left
  obtain ⟨hct', hTpCt, hew⟩ := hb.mp hct
  set s := embTpSigs Q (aoc V') (uc t') σ' with hsdef
  have hs : IsFinSeqSeq s :=
    isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUt') (aoc V') σ'
  have hcon : contraction s = sig V' := hemb'.left.right.left
  have hdm' := (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV')
    (fun h'' ↦ by rw [h''] at hm'; exact notin_empty _ hm')).right.right
  have hfo' : IsFirstOcc s (contraction s ﹫ ⋃₀ dom (sig V')) l k := by rw [hcon]; exact hfo
  obtain ⟨hll, hkl⟩ := firstOcc_last_of_endsWithNew hs (by rw [hcon]; exact hdm') hfo' hew
  have hds : dom s = depOf P t' := by rw [dom_embTpSigs, dom_sig_uc_eq_depOf hP ht']
  have hdt'l : depOf P t' = succ l := by
    have hl' : l ∈ dom s := hfo.left
    have h1 := (sUnion_mem_of_ne_empty hs.right.left
      (fun h'' ↦ by rw [h''] at hl'; exact notin_empty _ hl')).right.right
    rw [← hds, h1]
    exact congrArg succ hll.symm
  have ht't : ancOf P t' (succ l) = t' := by rw [← hdt'l]; exact hTS.anc_dep ht'
  rw [ht't] at hc1'
  have httc : t' = tc := by
    rw [← eq_ctChd_of_ctp_eq_ct (natCast_mem_omega 2) natCast_two_ne_empty hP ht hc1' hct',
      ← eq_ctChd_of_ctp_eq_ct (natCast_mem_omega 2) natCast_two_ne_empty hP ht htc htcct,
      aoc_uc_eq_of_mem_chdOf_otci_two hP ht hc1' htc]
  -- `y₁` is continuous with the new entry at the end, so it is `y*`
  have hlrow : s ﹫ l = tpSig Q (aoc V') !(dctUZero, !(q₁, h₁)) := by
    rw [hsdef, embTpSigs_val hUt' (by rw [dom_sig_uc_eq_depOf hP ht']; exact hl), hy₁]
  have hy₁N' : !(dctUZero, !(q₁, h₁)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V') := by
    rw [haoc]; exact hy₁N
  have hdq₁ : depOf (Q ﹫ 2) q₁ = succ k := by
    have hk' : k ∈ dom (s ﹫ l) := hfo.right.left
    have h1 := (sUnion_mem_of_ne_empty (hs.right.right l hfo.left).right
      (fun h'' ↦ by rw [h''] at hk'; exact notin_empty _ hk')).right.right
    rw [hlrow, dom_tpSig_eq hy₁N', dom_sig_uc_eq_depOf hQ2 hq₁] at h1
    rw [h1, hkl]
    change succ (⋃₀ depOf (Q ﹫ 2) q₁) = succ (⋃₀ dom (s ﹫ lastIdx s))
    rw [← hll, hlrow, dom_tpSig_eq hy₁N', dom_sig_uc_eq_depOf hQ2 hq₁]
  have hlast' : ⋃₀ dom (sig (uc t')) = l := by
    rw [dom_sig_uc_eq_depOf hP ht', hdt'l, sUnion_succ hlo.transitive]
  rw [hlast', (siglvl_eq_one hUt' (by rw [dom_sig_uc_eq_depOf hP ht']; exact hl)).left,
    hy₁] at hTpCt
  have hctq₁ : ctp (uc q₁) = ct := by
    have h1 := hTpCt.right
    rwa [nodeU_orderedPair] at h1
  have hyy := hcteq hctq₁ hdq₁
  -- the embeddings agree
  subst httc
  have hσσ : σ' = σc := by
    refine eq_of_mem_aotciEmbSet_one hUt' (tensorProdATwoAOne_mem_aotci hQ
      (aoc_mem_aotci_of_mem_stduoci_one hV)) (by rw [← haoc]; exact hσ') hσc fun i hi ↦ ?_
    rw [(siglvl_eq_one hUt' hi).left]
    have hi' : i ∈ succ l := by rw [← hdt'l, ← dom_sig_uc_eq_depOf hP ht']; exact hi
    rcases mem_or_eq_of_mem_succ hi' with hi | rfl
    · rw [hσ'old i hi, hσcold i hi]
    · rw [hσcnew, hy₁, hyy]
  subst hσσ
  rw [eq_of_isUociEmb hV' hV haoc hemb'.left hembx.left]

end LeastOne

section LeastTwo

/-! ### `x*` is the least child with its key, case `t` continuous -/

variable {P Q V t σ c h' qa ha l : M}

/-- A child `r` of `p = (V | m, (t, σ))` with the key and signature of `V`, for `t` continuous
with last signature node `u`, is at least `x* = (V, (t, σ[u ↦ y*]))`, and equal to it if `r` is
continuous -/
theorem chd_cmp_xStar_two (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hV : V ∈ stduoci ((1 : ℕ) : M)) (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
    (hm0 : ⋃₀ dom (sig V) ≠ ∅)
    (hp : !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)) ∈ tensorProdTwoTwoNds P Q)
    (htct : ctp (uc t) = ct) (hdl : dom (sig (uc t)) = succ l)
    (hx : !(V, !(t, cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M))
      (sigdcn (uc t) l) !(dctUZero, !(c, h'))))) ∈ tensorProdTwoTwoNds P Q)
    (hσa : (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l = !(dctUZero, !(qa, ha)))
    (hY : IsYStarLe Q V qa ha c h')
    {V' t' σ' : M} (hr : !(V', !(t', σ')) ∈ tensorProdTwoTwoNds P Q)
    (hprt : tensorProdTwoTwoPrt P Q !(V', !(t', σ')) = !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)))
    (haoc : aoc V' = aoc V) (hsig : sig V' = sig V) :
    (!(V', !(t', σ')) = !(V, !(t, cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M))
      (sigdcn (uc t) l) !(dctUZero, !(c, h'))))) ∨
      !(V, !(t, cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M))
        (sigdcn (uc t) l) !(dctUZero, !(c, h')))))
        [tensorProdTwoTwoOdr P Q] !(V', !(t', σ'))) ∧
    (ctp V' = ct → !(V', !(t', σ')) = !(V, !(t, cc (σ ↾ ((1 : ℕ) : M))
      (update (σ ﹫ ((1 : ℕ) : M)) (sigdcn (uc t) l) !(dctUZero, !(c, h')))))) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  set y := !(dctUZero, !(c, h')) with hydef
  have hp' := hp
  rw [pair_mem_tensorProdTwoTwoNds_iff, aoc_iniSeg] at hp'
  obtain ⟨ht, -, hσ, -⟩ := hp'
  have hr' := hr
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hr'
  obtain ⟨ht', hV', hσ', hemb'⟩ := hr'
  have hx' := hx
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hx'
  obtain ⟨-, -, hσc, hembx⟩ := hx'
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hUt' := uc_mem_stduoci_of_mem_otci_two hP ht'
  have hm' : ⋃₀ dom (sig V') ∈ dom (sig V') := by rw [hsig]; exact hm
  have hmeq : ⋃₀ dom (sig V') = ⋃₀ dom (sig V) := by rw [hsig]
  have hsdV (i : M) : sigdcn V' i = sigdcn V i := by rw [sigdcn, sigdcn, hsig]
  -- the parent of `r`
  have hm0' : ⋃₀ dom (sig (uc !(V', !(t', σ')))) ≠ ∅ := by rw [uc_orderedPair, hmeq]; exact hm0
  rw [tensorProdTwoTwoPrt, if_neg hm0', prtTwo, orderedPair_eq_orderedPair_iff] at hprt
  obtain ⟨huc, hlbl⟩ := hprt
  rw [prtUc, uc_orderedPair, hmeq] at huc
  have hX'eq : iniSegAoc V' (⋃₀ dom (sig V')) = iniSegAoc V (⋃₀ dom (sig V)) := by
    rw [← aoc_iniSeg, hmeq, huc, aoc_iniSeg]
  obtain ⟨lr, k, q₁, h₁, hfo, hl, hy₁, hq₁, hy₁N, hh₁, hk, hfirst, hje, hrow, himg⟩ :=
    firstOcc_data hP hQ hr hm'
  rw [haoc, hsdV, hmeq] at hfirst hje
  rw [haoc] at hy₁N hh₁
  have hnQ := nodeQ_orderedPair V' t' σ'
  have hnH := nodeH_orderedPair V' t' σ'
  have hancL : prtAncL P Q !(V', !(t', σ')) = ancOf P t' lr := by rw [prtAncL, hnQ, hrow]
  have hancS : prtAncS P Q !(V', !(t', σ')) = ancOf P t' (succ lr) := by
    rw [prtAncS, ancSucc, hnQ, hrow]
  have hnode : prtNode Q !(V', !(t', σ')) = sigdcn (uc t') lr := by
    rw [prtNode, nodeU_orderedPair, hrow]
  have hdt' := hTS.dep_mem_omega ht'
  have hls : lr ∈ succ (depOf P t') := mem_succ_of_mem hl
  have hl1s : succ lr ∈ succ (depOf P t') := succ_mem_succ_of_mem hdt' hl
  obtain ⟨htl, hdtl⟩ := hTS.anc_mem_nd ht' hls
  change ancOf P t' lr ∈ ndOf P at htl
  change depOf P (ancOf P t' lr) = lr at hdtl
  obtain ⟨htl1, hdtl1⟩ := hTS.anc_mem_nd ht' hl1s
  change ancOf P t' (succ lr) ∈ ndOf P at htl1
  change depOf P (ancOf P t' (succ lr)) = succ lr at hdtl1
  have hc1 : ancOf P t' (succ lr) ∈ chdOf P (ancOf P t' lr) := hTS.anc_succ_mem_chd ht' hl
  -- the case of the parent
  have hcase : ¬ PrtCase P Q !(V', !(t', σ')) := by
    intro hcase
    rw [prtLbl, if_pos hcase, prtLblOne, orderedPair_eq_orderedPair_iff, hancL] at hlbl
    rw [hlbl.left, chdOf_eq_empty_of_ctp_eq_ct (natCast_mem_omega 2) hP ht htct] at hc1
    exact notin_empty _ hc1
  rw [prtLbl, if_neg hcase, prtLblTwo, orderedPair_eq_orderedPair_iff, prtCt, prtEmbTwo, hancL,
    hancS, hnH, hnode] at hlbl
  obtain ⟨htct', hσeq⟩ := hlbl
  obtain ⟨hcc, hcck, hccs, -, -, hccmin⟩ :=
    ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hP htl hc1
  rw [htct'] at hcc hcck hccs hccmin
  obtain ⟨hdtd, hanct⟩ := ancOf_eq_of_mem_chdOf hS hcc
  rw [hdtl] at hdtd hanct
  -- `l = l_r`
  have hlo : Ordinal lr := ordinal_of_mem (ordinal_of_mem ordinal_omega hdt') hl
  have hlr : lr = l := by
    have h1 : succ lr = succ l := by rw [← hdl, dom_sig_uc_eq_depOf hP ht, hdtd]
    have h2 : Ordinal l := by
      have h3 := ordinal_of_mem ordinal_omega (dom_sig_mem_omega_of_mem_stduoci_one hUt)
      rw [hdl] at h3
      exact ordinal_of_mem h3 (mem_succ_self l)
    rw [← sUnion_succ hlo.transitive, h1, sUnion_succ h2.transitive]
  subst hlr
  -- the signature nodes of `t` and `t'` agree up to `l`
  have hUl1 := uc_mem_stduoci_of_mem_otci_two hP htl1
  have hsfl1 := (uociCond_of_mem_stduoci_one hUl1).right.right.right.left.left
  have hdsl1 : dom (sig (uc (ancOf P t' (succ lr)))) = succ lr := by
    rw [dom_sig_uc_eq_depOf hP htl1, hdtl1]
  have hsd (i : M) (hi : i ∈ succ lr) : sigdcn (uc t) i = sigdcn (uc t') i := by
    rw [← sigdcn_anc hP ht' hl1s hi, sigdcn, sigdcn, hccs]
  have hilr (i : M) (hi : i ∈ lr) : i ∈ dom (sig (uc t)) := by rw [hdl]; exact mem_succ_of_mem hi
  have hnel (i : M) (hi : i ∈ lr) : sigdcn (uc t) i ≠ sigdcn (uc t) lr := by
    intro h''
    have := congrArg lbl h''
    rw [lbl_sigdcn hUt (hilr i hi), lbl_sigdcn hUt (by rw [hdl]; exact mem_succ_self _)] at this
    rw [this] at hi
    exact notMem_self _ hi
  -- the successor of `σ'(w'_l)` is `a`
  have hσ'e := (mem_aotciEmbSet_iff.mp hσ').right
  have hσ'1 := embChg_val_one_isFunction hσ'
  have hσ'0 : (∅ : M) ∈ dom σ' := by
    rw [hσ'e.dom_eq]; exact mem_succ_of_mem empty_mem_natCast_one
  have hsucc : prtSucc Q !(V', !(t', σ')) = !(dctUZero, !(qa, ha)) := by
    rw [← hσa, ← hσeq, embUpd_val_one hσ', hsd lr (mem_succ_self _)]
    exact (val_update_self (hσ'1.left.restrict _) _ _).symm
  obtain ⟨haN, hya₁, hamin₁⟩ := least_of_prtSucc_eq hQ hV' hm' uc_orderedPair hsucc
    (orderedPair_ne_empty _ _)
  rw [hX'eq] at haN
  rw [haoc, himg] at hya₁
  rw [hX'eq, haoc, himg] at hamin₁
  obtain ⟨hle, hcteq⟩ := hY q₁ h₁ k hq₁ hy₁N hh₁ hk hfirst hje hya₁ hamin₁
  -- the coordinates of `x*` and of `r`
  set σc := cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M)) (sigdcn (uc t) lr) y)
    with hσcdef
  obtain ⟨hv1, -, -⟩ := embChg_vals hσ (sigdcn (uc t) lr) y
  obtain ⟨hinj1, hdom1⟩ := embChg_val_one_isFunction hσ
  have hσold (i : M) (hi : i ∈ lr) :
      (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i = (σ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t') i := by
    have hi1 : i ∈ succ lr := mem_succ_of_mem hi
    have hnd' : sigdcn (uc t') i ∈ ndOf (aoc (uc (ancOf P t' (succ lr))) ﹫ ((1 : ℕ) : M)) := by
      have h'' := (siglvl_eq_one hUl1 (by rw [hdsl1]; exact hi1)).right
      rwa [sigdcn_anc hP ht' hl1s hi1] at h''
    have hit' : i ∈ dom (sig (uc t')) := by
      rw [dom_sig_uc_eq_depOf hP ht']
      exact (ordinal_of_mem ordinal_omega hdt').transitive _ hl hi
    have hnd : sigdcn (uc t') i ∈ ndOf (aoc (uc t') ﹫ ((1 : ℕ) : M)) :=
      (siglvl_eq_one hUt' hit').right
    have hne : sigdcn (uc t') i ≠ sigdcn (uc t') lr := by
      rw [← hsd i hi1, ← hsd lr (mem_succ_self _)]
      exact hnel i hi
    rw [← hσeq, hsd i hi1, embUpd_val_one_of_ne hσ'e.isFunction hσ'0 hσ'1.left
      (by rw [hσ'1.right]; exact hnd) hnd' hne]
  have hσcold (i : M) (hi : i ∈ lr) :
      (σc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i = (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i := by
    rw [hv1]
    exact val_update_of_ne hinj1 _ (by rw [hdom1]; exact (siglvl_eq_one hUt (hilr i hi)).right)
      (hnel i hi)
  have hσcnew : (σc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) lr = y := by
    rw [hv1]
    exact val_update_self hinj1 _ _
  have hdt : depOf P t = succ lr := hdtd
  have hpre : ∀ i ∈ lr, tensorProdTwoAOneSeq P !(t, σc) ﹫ i =
      tensorProdTwoAOneSeq P !(t', σ') ﹫ i := by
    intro i hi
    have hit : i ∈ depOf P t := by rw [hdt]; exact mem_succ_of_mem hi
    have hit' : i ∈ depOf P t' := (ordinal_of_mem ordinal_omega hdt').transitive _ hl hi
    rw [tensorProdTwoAOneSeq_val hP ht hit, tensorProdTwoAOneSeq_val hP ht' hit',
      hσcold i hi, hσold i hi]
    have hsi : succ i ∈ succ lr := succ_mem_succ_of_mem (ordinal_omega.transitive _ hdt' hl) hi
    have hltc : lr ∈ succ (depOf P t) := by
      rw [hdt]
      exact mem_succ_of_mem (mem_succ_self lr)
    rw [← ancOf_ancOf (isSLOT_of_mem_otci hP) ht hltc hsi,
      ← ancOf_ancOf (isSLOT_of_mem_otci hP) ht' hls hsi, hanct]
  have hcmp : (σc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) lr =
        (σ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t') lr ∨
      ((σc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) lr)
        [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
        ((σ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t') lr) := by
    rw [hσcnew, hy₁]
    exact hle
  have htchd := chdOf_eq_empty_of_ctp_eq_ct (natCast_mem_omega 2) hP ht htct
  refine ⟨?_, fun hct ↦ ?_⟩
  · rcases eq_or_rel_tensorProdTwoTwoOdr_of_seq_prefix hP hQ hx hr haoc.symm hdt hl hpre
      (hcmp.elim (fun he ↦ .inr ⟨he, htchd, (hccmin _ hc1 rfl).imp_left Eq.symm⟩) .inl) with
      h'' | h''
    · exact .inl h''.symm
    · exact .inr h''
  -- `r` is continuous: it is `x*`
  have hb := hemb'.left.right.right.left
  obtain ⟨hct', hTpCt, hew⟩ := hb.mp hct
  set s := embTpSigs Q (aoc V') (uc t') σ' with hsdef
  have hs : IsFinSeqSeq s :=
    isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUt') (aoc V') σ'
  have hcon : contraction s = sig V' := hemb'.left.right.left
  have hdm' := (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV')
    (fun h'' ↦ by rw [h''] at hm'; exact notin_empty _ hm')).right.right
  have hfo' : IsFirstOcc s (contraction s ﹫ ⋃₀ dom (sig V')) lr k := by rw [hcon]; exact hfo
  obtain ⟨hll, hkl⟩ := firstOcc_last_of_endsWithNew hs (by rw [hcon]; exact hdm') hfo' hew
  have hds : dom s = depOf P t' := by rw [dom_embTpSigs, dom_sig_uc_eq_depOf hP ht']
  have hdt'l : depOf P t' = succ lr := by
    have hl' : lr ∈ dom s := hfo.left
    have h1 := (sUnion_mem_of_ne_empty hs.right.left
      (fun h'' ↦ by rw [h''] at hl'; exact notin_empty _ hl')).right.right
    rw [← hds, h1]
    exact congrArg succ hll.symm
  have ht't : ancOf P t' (succ lr) = t' := by rw [← hdt'l]; exact hTS.anc_dep ht'
  rw [ht't] at hc1
  have htt' : t = t' := by
    rw [← htct', ht't]
    exact eq_ctChd_of_ctp_eq_ct (natCast_mem_omega 2) natCast_two_ne_empty hP htl hc1 hct'
  have hlrow : s ﹫ lr = tpSig Q (aoc V') !(dctUZero, !(q₁, h₁)) := by
    rw [hsdef, embTpSigs_val hUt' (by rw [dom_sig_uc_eq_depOf hP ht']; exact hl), hy₁]
  have hy₁N' : !(dctUZero, !(q₁, h₁)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V') := by
    rw [haoc]; exact hy₁N
  have hdq₁ : depOf (Q ﹫ 2) q₁ = succ k := by
    have hk' : k ∈ dom (s ﹫ lr) := hfo.right.left
    have h1 := (sUnion_mem_of_ne_empty (hs.right.right lr hfo.left).right
      (fun h'' ↦ by rw [h''] at hk'; exact notin_empty _ hk')).right.right
    rw [hlrow, dom_tpSig_eq hy₁N', dom_sig_uc_eq_depOf hQ2 hq₁] at h1
    rw [h1, hkl]
    change succ (⋃₀ depOf (Q ﹫ 2) q₁) = succ (⋃₀ dom (s ﹫ lastIdx s))
    rw [← hll, hlrow, dom_tpSig_eq hy₁N', dom_sig_uc_eq_depOf hQ2 hq₁]
  have hlast' : ⋃₀ dom (sig (uc t')) = lr := by
    rw [dom_sig_uc_eq_depOf hP ht', hdt'l, sUnion_succ hlo.transitive]
  rw [hlast', (siglvl_eq_one hUt' (by rw [dom_sig_uc_eq_depOf hP ht']; exact hl)).left,
    hy₁] at hTpCt
  have hctq₁ : ctp (uc q₁) = ct := by
    have h1 := hTpCt.right
    rwa [nodeU_orderedPair] at h1
  have hyy := hcteq hctq₁ hdq₁
  -- the embeddings agree
  subst htt'
  have hσσ : σ' = σc := by
    refine eq_of_mem_aotciEmbSet_one hUt (tensorProdATwoAOne_mem_aotci hQ
      (aoc_mem_aotci_of_mem_stduoci_one hV)) (by rw [← haoc]; exact hσ') hσc fun i hi ↦ ?_
    rw [(siglvl_eq_one hUt hi).left]
    have hi' : i ∈ succ lr := by rw [← hdl]; exact hi
    rcases mem_or_eq_of_mem_succ hi' with hi | rfl
    · rw [hσcold i hi, hσold i hi]
    · rw [hσcnew, hy₁, hyy]
  subst hσσ
  rw [eq_of_isUociEmb hV' hV haoc hemb'.left hembx.left]

end LeastTwo

section YStarRoot

/-! ### The least new node for the root -/

variable {Q V : M}

/-- For `|V_sig| = 1`, the level-`1` nodes of `V` are just the new node -/
theorem mem_ndOf_aoc_val_one_iff_of_sUnion_eq_empty (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hm0 : ⋃₀ dom (sig V) = ∅) (w : M) :
    w ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) ↔ w = sigdcn V (⋃₀ dom (sig V)) := by
  have hdm := (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV)
    (fun h' ↦ by rw [h'] at hm; exact notin_empty _ hm)).right.right
  rw [ndOf_aoc_val_one_eq hV, mem_iniSegNds_iff, hm0]
  rw [hm0] at hdm
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [hdm] at hi
    rcases mem_or_eq_of_mem_succ hi with hi | rfl
    · exact (notin_empty _ hi).elim
    · rfl
  · rintro rfl
    exact ⟨∅, by rw [hdm]; exact mem_succ_self _, rfl⟩

/-- The level-`1` nodes of an element of `stduoci_1` with empty signature: none -/
theorem ndOf_aoc_val_one_eq_empty_of_sig_eq_empty {U : M} (hU : U ∈ stduoci ((1 : ℕ) : M))
    (hs : sig U = ∅) : ndOf (aoc U ﹫ ((1 : ℕ) : M)) = ∅ := by
  ext w
  refine ⟨fun hw ↦ ?_, fun hw ↦ (notin_empty _ hw).elim⟩
  obtain ⟨i, hi, -⟩ := exists_sigdcn_eq hU hw
  rw [hs, dom_empty] at hi
  exact (notin_empty _ hi).elim

/-- The least new node `y*₀ = (r₀⁺, {s₀ ↦ e})` for the root: the continuous child of the root
of `Q(2)` with its new node sent to the new entry -/
theorem exists_yStar_root (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hm0 : ⋃₀ dom (sig V) = ∅) :
    ∃ c h', c ∈ ndOf (Q ﹫ 2) ∧
      h' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc c)) (tensorProdTwoAOneTgt (aoc V)) ∧
      !(dctUZero, !(c, h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) ∧
      ctp (uc c) = ct ∧ chdOf (Q ﹫ 2) c = ∅ ∧ depOf (Q ﹫ 2) c = succ ∅ ∧
      sigImg (aoc V) c h' ∅ = sigdcn V (⋃₀ dom (sig V)) ∧
      ∀ q h, q ∈ ndOf (Q ﹫ 2) → !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) →
        h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)) →
        (!(dctUZero, !(c, h')) = !(dctUZero, !(q, h)) ∨
          !(dctUZero, !(c, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
            !(dctUZero, !(q, h))) ∧
        (ctp (uc q) = ct → depOf (Q ﹫ 2) q = succ ∅ → !(q, h) = !(c, h')) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  obtain ⟨hPs, -, hrt, ⟨r₀, hr₀⟩, hchd⟩ := otciCond_two hQ2
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := hPs
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  have hT := tensorProdTwoAOneTgt_mem hX
  have heX := (siglvl_eq_one hV hm).right
  have hr₀m : r₀ ∈ rtOf (Q ﹫ 2) := by rw [hr₀]; exact mem_singleton _
  have hr₀n : r₀ ∈ ndOf (Q ﹫ 2) := (TreeStructure.mem_rt_iff.mp hr₀m).left
  have hr₀d : depOf (Q ﹫ 2) r₀ = ∅ := (TreeStructure.mem_rt_iff.mp hr₀m).right
  have hUr := hrt r₀ hr₀m
  have hUr' := hUr
  rw [mem_trvuoci_iff] at hUr'
  obtain ⟨hUrs, -, hUrd⟩ := hUr'
  have hsr : sig (uc r₀) = ∅ := sig_eq_empty_of_mem_trvuoci (natCast_mem_omega 1) hUr
  have hndr := ndOf_aoc_val_one_eq_empty_of_sig_eq_empty hUrs hsr
  -- the continuous child of the root
  obtain ⟨q₀, hq₀⟩ := (exists_mem_ciExt_one_iff hUrs hUrd).mpr (.inl hsr)
  obtain ⟨c0, hc0, hc0k⟩ := ((hchd r₀ hr₀n).left (aoc q₀)).mpr ⟨q₀, hq₀, rfl⟩
  obtain ⟨hc, hck, -, hcct, hcchd, hcmin⟩ :=
    ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hr₀n hc0
  set c := ctChd (Q ﹫ 2) r₀ (aoc (uc c0)) with hcdef
  have hcn : c ∈ ndOf (Q ﹫ 2) := mem_ndOf_of_mem_chdOf hPs hc
  have hUc := uc_mem_stduoci_of_mem_otci_two hQ2 hcn
  obtain ⟨-, hq₀s, -, hq₀ct⟩ := mem_ciExt_props hq₀
  have hucr : uc c = q₀ :=
    eq_of_aoc_eq_of_ctp_eq_ct (natCast_mem_omega 1) hUc hq₀s hcct hq₀ct (hck.trans hc0k)
  have hext : !(uc r₀, uc c) ∈ ciExt ((1 : ℕ) : M) := by rw [hucr]; exact hq₀
  obtain ⟨hsb, hndc, hsU, hsubc, -⟩ := ext_one_tree hext
  have hAr := aoc_mem_aotci_of_mem_stduoci_one hUrs
  have hAc := aoc_mem_aotci_of_mem_stduoci_one hUc
  -- the embedding
  obtain ⟨hr, hhr⟩ := exists_mem_aotciEmbSet_trvAotci_one hT
  rw [← aoc_eq_trvAotci (natCast_mem_omega 1) hUr] at hhr
  set s₀ := sigdcn (uc c) (dom (sig (uc r₀))) with hs₀def
  set e := sigdcn V (⋃₀ dom (sig V)) with hedef
  have hD : relabelOne trvAZero e ∈ ndOf (tensorProdTwoAOneTgt (aoc V) ﹫ ((1 : ℕ) : M)) := by
    rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hX1]
    exact ⟨_, heX, rfl⟩
  have hh' := embExt_mem_aotciEmbSet hAr hAc hT (aoc_val_of_mem_ciExt_one hext).left hsubc hndc hsU
    hhr hD (fun z hz ↦ by rw [hndr] at hz; exact (notin_empty _ hz).elim)
    (fun z hz ↦ by rw [hndr] at hz; exact (notin_empty _ hz).elim)
  obtain ⟨hv1, -, -⟩ := embChg_vals hhr s₀ (relabelOne trvAZero e)
  obtain ⟨hinj1, -⟩ := embChg_val_one_isFunction hhr
  set h' := cc (hr ↾ ((1 : ℕ) : M)) (update (hr ﹫ ((1 : ℕ) : M)) s₀ (relabelOne trvAZero e))
    with hh'def
  have hval : (h' ﹫ ((1 : ℕ) : M)) ﹫ s₀ = relabelOne trvAZero e := by
    rw [hv1]; exact val_update_self hinj1 _ _
  have hy : !(dctUZero, !(c, h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) :=
    mem_tensorProdTwoAOneNds_iff'.mpr ⟨c, hcn, not_mem_rtOf_of_mem_chdOf hPs hc, h', hh', rfl⟩
  obtain ⟨hdc, hancc⟩ := ancOf_eq_of_mem_chdOf hPs hc
  rw [hr₀d] at hdc hancc
  have hds0 : dom (sig (uc r₀)) = ∅ := by rw [hsr, dom_empty]
  have hs₀e : sigdcn (uc c) ∅ = s₀ := by rw [hs₀def, hds0]
  have himg0 : sigImg (aoc V) c h' ∅ = e := by
    rw [show sigImg (aoc V) c h' ∅ = tpOrig (aoc V) ((1 : ℕ) : M)
      ((h' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) ∅) from rfl, hs₀e, hval,
      tpOrig_one_relabelOne hX heX]
  -- the images of the first signature nodes are all the new node
  have himgq {q h : M} (hq : q ∈ ndOf (Q ﹫ 2))
      (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V))) {i : M}
      (hi : i ∈ dom (sig (uc q))) :
      (h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) i = relabelOne trvAZero e := by
    obtain ⟨hz, hze⟩ := sigImg_spec hQ2 hq hX hh hi
    rw [hze, (mem_ndOf_aoc_val_one_iff_of_sUnion_eq_empty hV hm hm0 _).mp hz]
  refine ⟨c, h', hcn, hh', hy, hcct, hcchd, hdc, himg0, fun q h hq hyq hh ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨q', -, hqr, h'', -, hqe⟩ := mem_tensorProdTwoAOneNds_iff'.mp hyq
    rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hqe
    obtain ⟨-, rfl, rfl⟩ := hqe
    have hdq := hTS.dep_mem_omega hq
    have hd0 : depOf (Q ﹫ 2) q ≠ ∅ := fun h0 ↦ hqr (TreeStructure.mem_rt_iff.mpr ⟨hq, h0⟩)
    have h0q : (∅ : M) ∈ depOf (Q ﹫ 2) q :=
      empty_mem_of_ordinal_of_ne_empty (ordinal_of_mem ordinal_omega hdq) hd0
    have hq1 : ancOf (Q ﹫ 2) q (succ ∅) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q ∅) :=
      hTS.anc_succ_mem_chd hq h0q
    have hq0 : ancOf (Q ﹫ 2) q ∅ = r₀ := by
      have h1 : ancOf (Q ﹫ 2) q ∅ ∈ rtOf (Q ﹫ 2) := hTS.anc_empty_mem_rt hq
      rw [hr₀, mem_singleton_iff] at h1
      exact h1
    rw [hq0] at hq1
    refine eq_or_rel_of_seq_prefix hQ hX hy hyq hcn hq hh' hh hdc h0q
      (fun i hi ↦ (notin_empty _ hi).elim) ?_ hcchd ?_
    · rw [hs₀e, hval, himgq hq hh (by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact h0q)]
    · rcases hcmin _ hq1 (aoc_uc_eq_of_mem_chdOf_otci_two hQ2 hr₀n hq1 hc0) with h1 | h1
      · exact .inl h1.symm
      · exact .inr h1
  · intro hctq hdq
    have hqq : ancOf (Q ﹫ 2) q (succ ∅) = q := by rw [← hdq]; exact hTS.anc_dep hq
    have h0q : (∅ : M) ∈ depOf (Q ﹫ 2) q := by rw [hdq]; exact mem_succ_self _
    have hq1 : ancOf (Q ﹫ 2) q (succ ∅) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q ∅) :=
      hTS.anc_succ_mem_chd hq h0q
    have hq0 : ancOf (Q ﹫ 2) q ∅ = r₀ := by
      have h1 : ancOf (Q ﹫ 2) q ∅ ∈ rtOf (Q ﹫ 2) := hTS.anc_empty_mem_rt hq
      rw [hr₀, mem_singleton_iff] at h1
      exact h1
    rw [hq0, hqq] at hq1
    have hqc : q = c := by
      rw [← eq_ctChd_of_ctp_eq_ct (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hr₀n hq1 hctq,
        aoc_uc_eq_of_mem_chdOf_otci_two hQ2 hr₀n hq1 hc0]
    subst hqc
    rw [orderedPair_eq_orderedPair_iff]
    refine ⟨rfl, eq_of_mem_aotciEmbSet_one hUc hT hh hh' fun i hi ↦ ?_⟩
    rw [(siglvl_eq_one hUc hi).left, himgq hcn hh hi, himgq hcn hh' hi]

end YStarRoot

section LeastRoot

/-! ### `x*` is the least child with its key, case `p` the root -/

variable {P Q V t σ tc c h' : M}

/-- A child `r` of the root `p = (V | 0, (t, σ))` with the key and signature of `V` is at least
`x* = (V, (t*, σ ∪ {s ↦ y*₀}))`, and equal to it if `r` is continuous -/
theorem chd_cmp_xStar_root (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hV : V ∈ stduoci ((1 : ℕ) : M)) (hm : ⋃₀ dom (sig V) ∈ dom (sig V))
    (hm0 : ⋃₀ dom (sig V) = ∅)
    (hp : !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)) ∈ tensorProdTwoTwoNds P Q)
    (ht : t ∈ rtOf P) (htc : tc ∈ chdOf P t)
    (htcchd : chdOf P tc = ∅) (htcmin : ∀ c' ∈ chdOf P t, c' = tc ∨ tc [sblOdrOf P] c')
    (htcct : ctp (uc tc) = ct)
    (hx : !(V, !(tc, cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M))
      (sigdcn (uc tc) (dom (sig (uc t)))) !(dctUZero, !(c, h'))))) ∈ tensorProdTwoTwoNds P Q)
    (hle : ∀ q h, q ∈ ndOf (Q ﹫ 2) → !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) →
        h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)) →
        (!(dctUZero, !(c, h')) = !(dctUZero, !(q, h)) ∨
          !(dctUZero, !(c, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
            !(dctUZero, !(q, h))) ∧
        (ctp (uc q) = ct → depOf (Q ﹫ 2) q = succ ∅ → !(q, h) = !(c, h')))
    {V' t' σ' : M} (hr : !(V', !(t', σ')) ∈ tensorProdTwoTwoNds P Q)
    (hprt : tensorProdTwoTwoPrt P Q !(V', !(t', σ')) = !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)))
    (haoc : aoc V' = aoc V) (hsig : sig V' = sig V) :
    (!(V', !(t', σ')) = !(V, !(tc, cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M))
      (sigdcn (uc tc) (dom (sig (uc t)))) !(dctUZero, !(c, h'))))) ∨
      !(V, !(tc, cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M))
        (sigdcn (uc tc) (dom (sig (uc t)))) !(dctUZero, !(c, h')))))
        [tensorProdTwoTwoOdr P Q] !(V', !(t', σ'))) ∧
    (ctp V' = ct → !(V', !(t', σ')) = !(V, !(tc, cc (σ ↾ ((1 : ℕ) : M))
      (update (σ ﹫ ((1 : ℕ) : M)) (sigdcn (uc tc) (dom (sig (uc t))))
        !(dctUZero, !(c, h')))))) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  set sn := sigdcn (uc tc) (dom (sig (uc t))) with hsndef
  set y := !(dctUZero, !(c, h')) with hydef
  set σc := cc (σ ↾ ((1 : ℕ) : M)) (update (σ ﹫ ((1 : ℕ) : M)) sn y) with hσcdef
  have htn := (TreeStructure.mem_rt_iff.mp ht).left
  have hdt0 : depOf P t = ∅ := (TreeStructure.mem_rt_iff.mp ht).right
  have hr' := hr
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hr'
  obtain ⟨ht', hV', hσ', hemb'⟩ := hr'
  have hx' := hx
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hx'
  obtain ⟨htcn, -, hσc, hembx⟩ := hx'
  have hUt' := uc_mem_stduoci_of_mem_otci_two hP ht'
  have hUtc := uc_mem_stduoci_of_mem_otci_two hP htcn
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hB := tensorProdATwoAOne_mem_aotci hQ hX
  rw [haoc] at hσ'
  have hm' : ⋃₀ dom (sig V') ∈ dom (sig V') := by rw [hsig]; exact hm
  have hmeq : ⋃₀ dom (sig V') = ⋃₀ dom (sig V) := by rw [hsig]
  have hsdV (i : M) : sigdcn V' i = sigdcn V i := by rw [sigdcn, sigdcn, hsig]
  -- the parent of `r`
  rw [tensorProdTwoTwoPrt, if_pos (by rw [uc_orderedPair, hmeq]; exact hm0), prtOne,
    orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff, prtRootAnc,
    nodeQ_orderedPair] at hprt
  obtain ⟨-, hanc0, -⟩ := hprt
  obtain ⟨lr, k, q₁, h₁, hfo, hl, hy₁, hq₁, hy₁N, hh₁, hk, hfirst, hje, -, -⟩ :=
    firstOcc_data hP hQ hr hm'
  rw [haoc, hsdV, hmeq] at hfirst hje
  rw [haoc] at hy₁N hh₁ hfo
  have hX1 (w : M) := mem_ndOf_aoc_val_one_iff_of_sUnion_eq_empty hV hm hm0 w
  -- the new entry first occurs in the first row
  set s := embTpSigs Q (aoc V) (uc t') σ' with hsdef
  have hs : IsFinSeqSeq s :=
    isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUt') (aoc V) σ'
  have hdt' := hTS.dep_mem_omega ht'
  have hlr0 : lr = ∅ := by
    by_contra hl0
    obtain ⟨-, ⟨i0, hi0, hr0⟩, hyr⟩ := ucf_anc_rel hP ht' hl hl0 hB hσ'
    rw [hr0, hy₁] at hyr
    obtain ⟨hb, -⟩ := (rel_odrOne_tensorProdATwoAOne_iff_of_mem hQ hX hy₁N).mp hyr
    obtain ⟨q₂, hq₂, hq₂r, h₂, hh₂, hb'⟩ := mem_tensorProdTwoAOneNds_iff'.mp hb
    have hdq₂ := ((show (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure from
      (otciCond_two hQ2).left).isTreeStructure).dep_mem_omega hq₂
    have hd0 : depOf (Q ﹫ 2) q₂ ≠ ∅ := fun h0 ↦ hq₂r (TreeStructure.mem_rt_iff.mpr ⟨hq₂, h0⟩)
    have h0q : (∅ : M) ∈ dom (sig (uc q₂)) := by
      rw [dom_sig_uc_eq_depOf hQ2 hq₂]
      exact empty_mem_of_ordinal_of_ne_empty (ordinal_of_mem ordinal_omega hdq₂) hd0
    have hi0t : i0 ∈ dom (sig (uc t')) := by
      rw [dom_sig_uc_eq_depOf hP ht']
      exact (ordinal_of_mem ordinal_omega hdt').transitive _ hl hi0
    have hrow : s ﹫ i0 = tpSig Q (aoc V) !(dctUZero, !(q₂, h₂)) := by
      rw [hsdef, embTpSigs_val hUt' hi0t, hb']
    rw [hb'] at hb
    have hent : (s ﹫ i0) ﹫ ∅ = sig V' ﹫ ⋃₀ dom (sig V') := by
      rw [hrow, tpSig_val_eq hQ hb h0q, sig_val_eq_pair hV' hm', hsdV, hmeq]
      have h1 := (sigImg_spec hQ2 hq₂ hX hh₂ h0q).left
      rw [hX1] at h1
      exact congrArg _ h1
    have hj0 : (∅ : M) ∈ dom (s ﹫ i0) := by rw [hrow, dom_tpSig_eq hb]; exact h0q
    rcases hfo.right.right.right i0 (by rw [hsdef, dom_embTpSigs]; exact hi0t) ∅ hj0
        hent with ⟨h1, -⟩ | h1 | ⟨h1, -⟩
    · rw [h1] at hi0; exact notMem_self _ hi0
    · exact notMem_self _ ((ordinal_of_mem (ordinal_of_mem ordinal_omega hdt') hl).transitive _
        hi0 h1)
    · rw [h1] at hi0; exact notMem_self _ hi0
  subst hlr0
  obtain ⟨hcmp, hcteq⟩ := hle q₁ h₁ hq₁ hy₁N hh₁
  -- the coordinates
  obtain ⟨hdtcd, hanctc⟩ := ancOf_eq_of_mem_chdOf hS htc
  rw [hdt0] at hdtcd hanctc
  have hdst : dom (sig (uc t)) = ∅ := by rw [dom_sig_uc_eq_depOf hP htn, hdt0]
  have hp' := hp
  rw [pair_mem_tensorProdTwoTwoNds_iff, aoc_iniSeg] at hp'
  obtain ⟨-, -, hσ, -⟩ := hp'
  obtain ⟨hv1, -, -⟩ := embChg_vals hσ sn y
  obtain ⟨hinj1, -⟩ := embChg_val_one_isFunction hσ
  have hσcnew : (σc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) ∅ = y := by
    rw [hv1, ← hdst]
    exact val_update_self hinj1 _ _
  have hc1 : ancOf P t' (succ ∅) ∈ chdOf P t := by
    rw [← hanc0]
    exact hTS.anc_succ_mem_chd ht' hl
  refine ⟨?_, fun hct ↦ ?_⟩
  · have hcmp' : (σc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) ∅ =
          (σ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t') ∅ ∨
        ((σc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) ∅)
          [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
          ((σ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t') ∅) := by
      rw [hσcnew, hy₁]
      exact hcmp
    rcases eq_or_rel_tensorProdTwoTwoOdr_of_seq_prefix hP hQ hx hr haoc.symm hdtcd hl
      (fun i hi ↦ (notin_empty _ hi).elim)
      (hcmp'.elim (fun he ↦ .inr ⟨he, htcchd, (htcmin _ hc1).imp_left Eq.symm⟩) .inl) with
      h'' | h''
    · exact .inl h''.symm
    · exact .inr h''
  -- `r` is continuous: it is `x*`
  have hb := hemb'.left.right.right.left
  rw [haoc] at hb
  obtain ⟨hct', hTpCt, hew⟩ := hb.mp hct
  have hcon : contraction s = sig V' := by rw [hsdef, ← haoc]; exact hemb'.left.right.left
  have hdm' := (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV')
    (fun h'' ↦ by rw [h''] at hm'; exact notin_empty _ hm')).right.right
  have hfo' : IsFirstOcc s (contraction s ﹫ ⋃₀ dom (sig V')) ∅ k := by rw [hcon]; exact hfo
  obtain ⟨hll, hkl⟩ := firstOcc_last_of_endsWithNew hs (by rw [hcon]; exact hdm') hfo' hew
  have hds : dom s = depOf P t' := by rw [dom_embTpSigs, dom_sig_uc_eq_depOf hP ht']
  have hdt'l : depOf P t' = succ ∅ := by
    have hl' : (∅ : M) ∈ dom s := hfo.left
    have h1 := (sUnion_mem_of_ne_empty hs.right.left
      (fun h'' ↦ by rw [h''] at hl'; exact notin_empty _ hl')).right.right
    rw [← hds, h1]
    exact congrArg succ hll.symm
  have ht't : ancOf P t' (succ ∅) = t' := by rw [← hdt'l]; exact hTS.anc_dep ht'
  rw [ht't] at hc1
  have httc : t' = tc := by
    rw [← eq_ctChd_of_ctp_eq_ct (natCast_mem_omega 2) natCast_two_ne_empty hP htn hc1 hct',
      ← eq_ctChd_of_ctp_eq_ct (natCast_mem_omega 2) natCast_two_ne_empty hP htn htc htcct,
      aoc_uc_eq_of_mem_chdOf_otci_two hP htn hc1 htc]
  -- `y₁` has depth `1`
  have hk0 : k = ∅ := by
    by_contra hk0
    have h0k : (∅ : M) ∈ k := empty_mem_of_ordinal_of_ne_empty
      (ordinal_of_mem (ordinal_of_mem ordinal_omega ((show (SLOTreeStructure.ofM
        (Q ﹫ (2 : M))).IsSLOTreeStructure from (otciCond_two hQ2).left).isTreeStructure
          |>.dep_mem_omega hq₁)) hk) hk0
    have hdq := ((show (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure from
      (otciCond_two hQ2).left).isTreeStructure).dep_mem_omega hq₁
    have h0q : (∅ : M) ∈ dom (sig (uc q₁)) := by
      rw [dom_sig_uc_eq_depOf hQ2 hq₁]
      exact (ordinal_of_mem ordinal_omega hdq).transitive _ hk h0k
    exact hfirst ∅ h0k ((hX1 _).mp (sigImg_spec hQ2 hq₁ hX hh₁ h0q).left)
  subst hk0
  have hlrow : s ﹫ ∅ = tpSig Q (aoc V) !(dctUZero, !(q₁, h₁)) := by
    rw [hsdef, embTpSigs_val hUt' (by rw [dom_sig_uc_eq_depOf hP ht']; exact hl), hy₁]
  have hdq₁ : depOf (Q ﹫ 2) q₁ = succ ∅ := by
    have hk' : (∅ : M) ∈ dom (s ﹫ ∅) := hfo.right.left
    have h1 := (sUnion_mem_of_ne_empty (hs.right.right ∅ hfo.left).right
      (fun h'' ↦ by rw [h''] at hk'; exact notin_empty _ hk')).right.right
    rw [hlrow, dom_tpSig_eq hy₁N, dom_sig_uc_eq_depOf hQ2 hq₁] at h1
    rw [h1, hkl]
    change succ (⋃₀ depOf (Q ﹫ 2) q₁) = succ (⋃₀ dom (s ﹫ lastIdx s))
    rw [← hll, hlrow, dom_tpSig_eq hy₁N, dom_sig_uc_eq_depOf hQ2 hq₁]
  have hlast' : ⋃₀ dom (sig (uc t')) = ∅ := by
    rw [dom_sig_uc_eq_depOf hP ht', hdt'l, sUnion_succ ordinal_empty.transitive]
  rw [hlast', (siglvl_eq_one hUt' (by rw [dom_sig_uc_eq_depOf hP ht']; exact hl)).left,
    hy₁] at hTpCt
  have hctq₁ : ctp (uc q₁) = ct := by
    have h1 := hTpCt.right
    rwa [nodeU_orderedPair] at h1
  have hyy := hcteq hctq₁ hdq₁
  subst httc
  have hσσ : σ' = σc := by
    refine eq_of_mem_aotciEmbSet_one hUt' hB hσ' hσc fun i hi ↦ ?_
    rw [(siglvl_eq_one hUt' hi).left]
    have hi' : i ∈ succ (∅ : M) := by rw [← hdt'l, ← dom_sig_uc_eq_depOf hP ht']; exact hi
    rcases mem_or_eq_of_mem_succ hi' with hi | rfl
    · exact (notin_empty _ hi).elim
    · rw [hσcnew, hy₁, hyy]
  subst hσσ
  rw [eq_of_isUociEmb hV' hV haoc hemb'.left hembx.left]

end LeastRoot

section LeastChd

/-! ### The least child with the key of an extension -/

variable {P Q : M}

/-- `x` is a child of `p` with `uc x = q`, below all other children with the key of `q`, and the
only continuous one -/
def IsLeastChd (P Q p q x : M) : Prop :=
  x ∈ tensorProdTwoTwoNds P Q ∧ dom (sig (uc x)) ≠ ∅ ∧ tensorProdTwoTwoPrt P Q x = p ∧ uc x = q ∧
    ∀ V' t' σ', !(V', !(t', σ')) ∈ tensorProdTwoTwoNds P Q →
      tensorProdTwoTwoPrt P Q !(V', !(t', σ')) = p → aoc V' = aoc q → sig V' = sig q →
        (!(V', !(t', σ')) = x ∨ x [tensorProdTwoTwoOdr P Q] !(V', !(t', σ'))) ∧
          (ctp V' = ct → !(V', !(t', σ')) = x)

/-- The least continuous child of a node of an `otci_2` tree with an extension -/
theorem exists_ct_chd {t : M} (hP : P ∈ otci ((2 : ℕ) : M)) (ht : t ∈ ndOf P)
    (hd : ctp (uc t) = dct) (hext : sig (uc t) = ∅ ∨ ucflvl (uc t) = ((1 : ℕ) : M)) :
    ∃ tc ∈ chdOf P t, !(uc t, uc tc) ∈ ciExt ((1 : ℕ) : M) ∧ ctp (uc tc) = ct ∧
      chdOf P tc = ∅ ∧ ∀ c' ∈ chdOf P t, c' = tc ∨ tc [sblOdrOf P] c' := by
  obtain ⟨hPs, -, -, -, hchd⟩ := otciCond_two hP
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  obtain ⟨q₀, hq₀⟩ := (exists_mem_ciExt_one_iff hUt hd).mpr hext
  obtain ⟨c0, hc0, hc0k⟩ := ((hchd t ht).left (aoc q₀)).mpr ⟨q₀, hq₀, rfl⟩
  obtain ⟨hc, hck, -, hcct, hcchd, hcmin⟩ :=
    ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hP ht hc0
  have hcn := mem_ndOf_of_mem_chdOf hPs hc
  have hUc := uc_mem_stduoci_of_mem_otci_two hP hcn
  obtain ⟨-, hq₀s, -, hq₀ct⟩ := mem_ciExt_props hq₀
  have hucr : uc (ctChd P t (aoc (uc c0))) = q₀ :=
    eq_of_aoc_eq_of_ctp_eq_ct (natCast_mem_omega 1) hUc hq₀s hcct hq₀ct (hck.trans hc0k)
  exact ⟨_, hc, by rw [hucr]; exact hq₀, hcct, hcchd,
    fun c' hc' ↦ hcmin c' hc' (aoc_uc_eq_of_mem_chdOf_otci_two hP ht hc' hc0)⟩

/-- The root case -/
theorem isLeastChd_root (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {V t σ : M} (hV : V ∈ stduoci ((1 : ℕ) : M)) (hVct : ctp V = ct)
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hm0 : ⋃₀ dom (sig V) = ∅)
    (hp : !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)) ∈ tensorProdTwoTwoNds P Q) :
    ∃ x, IsLeastChd P Q !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)) V x := by
  have hp' := hp
  rw [pair_mem_tensorProdTwoTwoNds_iff, aoc_iniSeg] at hp'
  obtain ⟨ht, -, hσ, hemb⟩ := hp'
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  -- `t` is the root
  have hsU : sig (iniSeg V (⋃₀ dom (sig V))) = ∅ := by rw [sig_iniSeg, hm0, restrict_empty]
  have hst := hemb.right hsU
  have htr : t ∈ rtOf P := by
    refine TreeStructure.mem_rt_iff.mpr ⟨ht, ?_⟩
    change depOf P t = ∅
    rw [← dom_sig_uc_eq_depOf hP ht, hst, dom_empty]
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hUtr := (otciCond_two hP).right.right.left t htr
  rw [mem_trvuoci_iff] at hUtr
  obtain ⟨tc, htc, hext, htcct, htcchd, htcmin⟩ := exists_ct_chd hP ht hUtr.right.right (.inl hst)
  obtain ⟨-, -, hsn, -, -⟩ := ext_one_tree hext
  have hndt := ndOf_aoc_val_one_eq_empty_of_sig_eq_empty hUt hst
  obtain ⟨c, h', hcn, hh', hy, hcct, hcchd, hdc, himg0, hle⟩ := exists_yStar_root hQ hV hm hm0
  obtain ⟨hxN, -⟩ := xStar_one_mem hP hQ hV hVct hm hp htc hext hy hcct hdc himg0
    (fun i hi ↦ (notin_empty _ hi).elim)
    (fun z hz ↦ by rw [hndt] at hz; exact (notin_empty _ hz).elim)
    (fun z hz ↦ by rw [hndt] at hz; exact (notin_empty _ hz).elim)
  have hprt := prt_xStar_root (Q := Q) (V := V) (y := !(dctUZero, !(c, h'))) hP hm0 htr htc hσ hsn
  rw [← hm0] at hprt
  refine ⟨_, hxN, by rw [uc_orderedPair]; exact fun h'' ↦ by rw [h''] at hm; exact notin_empty _ hm,
    hprt, uc_orderedPair, fun V' t' σ' hr hprt' haoc hsig ↦ ?_⟩
  exact chd_cmp_xStar_root hP hQ hV hm hm0 hp htr htc htcchd htcmin htcct hxN hle hr hprt' haoc
    hsig

end LeastChd

section LeastChdNe

variable {P Q : M}

/-- The non-root case -/
theorem isLeastChd_of_ne (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {V t σ : M} (hV : V ∈ stduoci ((1 : ℕ) : M)) (hVct : ctp V = ct)
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hm0 : ⋃₀ dom (sig V) ≠ ∅)
    (hR : iniSegRight V (⋃₀ dom (sig V)) ≠ ∅)
    (hp : !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)) ∈ tensorProdTwoTwoNds P Q) :
    ∃ x, IsLeastChd P Q !(iniSeg V (⋃₀ dom (sig V)), !(t, σ)) V x := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hp' := hp
  rw [pair_mem_tensorProdTwoTwoNds_iff, aoc_iniSeg] at hp'
  obtain ⟨ht, -, hσ, hemb⟩ := hp'
  have hU := hemb.left
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hA := aoc_mem_aotci_of_mem_stduoci_one hUt
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, -⟩ := lastSeg_facts hV hm
  have hB := tensorProdATwoAOne_mem_aotci hQ hX
  have hB' := tensorProdATwoAOne_mem_aotci hQ hX'
  have hsubB := isSubOne_tensorProdATwoAOne hQ hX hX' h0 hsub
  obtain ⟨w, hwR, hwl, hwU⟩ := iniSegUcf_of_ne_empty hV hm hR
  have hdV : dom (sig V) ≠ ∅ := fun h'' ↦ by rw [h''] at hm; exact notin_empty _ hm
  -- condition (c) of `p`
  have h3 : ((3 : ℕ) : M) ∈ dom (iniSeg V (⋃₀ dom (sig V))) := by
    rw [iniSeg, if_neg hm0, dom_ciQuint]
    exact natCast_mem_natCast_iff.mpr (by omega)
  have hucfU : embUcf Q (iniSegAoc V (⋃₀ dom (sig V))) (uc t) σ = !(((1 : ℕ) : M), w) := by
    have h1 := (hU.right.right.right h3).left
    rw [(ucflvldcn_iniSeg hm0).left, hwU, aoc_iniSeg] at h1
    exact h1.symm
  -- `t` is not a root
  have hsf := (uociCond_of_mem_stduoci_one hV).right.right.right.left.left
  have hdm := (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV) hdV).right.right
  have hsubm : ⋃₀ dom (sig V) ⊆ dom (sig V) := fun _ h' ↦ by rw [hdm]; exact mem_succ_of_mem h'
  have hst0 : sig (uc t) ≠ ∅ := by
    intro h
    have hcon := hU.right.left
    rw [sig_iniSeg, aoc_iniSeg] at hcon
    have hs0 : embTpSigs Q (iniSegAoc V (⋃₀ dom (sig V))) (uc t) σ = ∅ :=
      (isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUt) _
        σ).left.isRelation.eq_empty_of_dom_eq_empty (by rw [dom_embTpSigs, h, dom_empty])
    rw [hs0, contraction_empty] at hcon
    have hd := congrArg dom hcon
    rw [dom_empty, dom_restrict_of_subset hsf hsubm] at hd
    exact hm0 hd.symm
  -- the order facts of `σ`
  have he := (mem_aotciEmbSet_iff.mp hσ).right
  have hA1 := val_mem_otci_of_mem_aotci hA (mem_succ_self _)
  have hB'1 := val_mem_otci_of_mem_aotci hB' (mem_succ_self _)
  obtain ⟨hinj, hodr⟩ := (isOtciEmbedding_iff_of_mem_otci_one hA1 hB'1).mp
    (he.isOtciEmbedding (mem_succ_self _))
  have hodrB {z z' : M} (hz : z ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)))
      (hz' : z' ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)))
      (h : z [odrOne (aoc (uc t) ﹫ ((1 : ℕ) : M))] z') :
      ((σ ﹫ ((1 : ℕ) : M)) ﹫ z) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
        ((σ ﹫ ((1 : ℕ) : M)) ﹫ z') :=
    (hsubB.right _ (hinj.isFunctionFromTo.val_mem hz) _ (hinj.isFunctionFromTo.val_mem hz')).mp
      (hodr z hz z' hz' h)
  -- the image `a` of the `ucf`
  have ha_of {z₀ : M} (hz₀ : z₀ ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)))
      (hz : tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) ((σ ﹫ ((1 : ℕ) : M)) ﹫ z₀) =
        !(((1 : ℕ) : M), w)) :
      ∃ qa ha, (σ ﹫ ((1 : ℕ) : M)) ﹫ z₀ = !(dctUZero, !(qa, ha)) ∧ qa ∈ ndOf (Q ﹫ 2) ∧
        qa ∉ rtOf (Q ﹫ 2) ∧ ha ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc qa))
          (tensorProdTwoAOneTgt (iniSegAoc V (⋃₀ dom (sig V)))) ∧
        !(dctUZero, !(qa, ha)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V))) ∧
        !(dctUZero, !(qa, ha)) ∈
          ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) := by
    have haN := hinj.isFunctionFromTo.val_mem hz₀
    by_cases hT2 : IsTpTwo Q (iniSegAoc V (⋃₀ dom (sig V))) ((σ ﹫ ((1 : ℕ) : M)) ﹫ z₀)
    · obtain ⟨qa, hqa, hqart, ha, hha, hae⟩ := mem_tensorProdTwoAOneNds_iff'.mp hT2
      exact ⟨qa, ha, hae, hqa, hqart, hha, hae ▸ hT2, hae ▸ haN⟩
    · exfalso
      rw [tpUcf, if_neg hT2, tpUcfZero, orderedPair_eq_orderedPair_iff] at hz
      exact natCast_one_ne_empty hz.left.symm
  have hdV0 : dom (sig (uc !(V, !(t, σ)))) ≠ ∅ := by rw [uc_orderedPair]; exact hdV
  rcases ctp_eq_ct_or_dct (natCast_mem_omega 1) (mem_stduoci_iff.mp hUt).left with hct | hdct
  · -- `t` continuous: `x* = (V, (t, σ[u ↦ y*]))`
    have hdt0 : dom (sig (uc t)) ≠ ∅ := fun h'' ↦ hst0
      (((uociCond_of_mem_stduoci_one hUt).right.right.right.left.left.isRelation
        ).eq_empty_of_dom_eq_empty h'')
    obtain ⟨-, hlsig, hdl⟩ :=
      sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hUt) hdt0
    set l := ⋃₀ dom (sig (uc t)) with hldef
    have hz₀ := (siglvl_eq_one hUt hlsig).right
    have h3t : ((3 : ℕ) : M) ∉ dom (uc t) := by
      rw [(uociCond_of_mem_stduoci_one hUt).right.right.right.right.right.right.left.mpr
        (.inr hct)]
      exact notMem_self _
    have hucf : tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l) =
        !(((1 : ℕ) : M), w) := by
      rw [embUcf, ucfOrLast, if_neg h3t, sig_val_eq_pair hUt hlsig, embUcfAux, lvl_orderedPair,
        if_neg natCast_one_ne_empty, dcn_orderedPair] at hucfU
      exact hucfU
    obtain ⟨qa, ha, hσa, hqa, hqart, hha, haT, haN⟩ := ha_of hz₀ hucf
    rw [hσa] at hucf
    obtain ⟨c, h', hcn, hh', hy, hcct, hcchd, ⟨j, hdc, hje, hsame, hcase⟩, hlt_a, hmin_a, hY⟩ :=
      exists_yStar hQ hV hm hwR hwl hqa hqart hha hucf haN
    have hj : j ∈ dom (sig (uc c)) := by
      rw [dom_sig_uc_eq_depOf hQ2 hcn, hdc]
      exact mem_succ_self j
    have hyold := not_mem_lastSeg_of_sigImg_eq hQ hV hm hy hj hje
    have hyB : !(dctUZero, !(c, h')) ∈ ndOf (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)) :=
      (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX).mpr (.inr hy)
    have hlt (z : M) (hz : z ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)))
        (hzu : z [odrOne (aoc (uc t) ﹫ ((1 : ℕ) : M))] (sigdcn (uc t) l)) :
        ((σ ﹫ ((1 : ℕ) : M)) ﹫ z) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
          !(dctUZero, !(c, h')) :=
      lt_yStar_of_lt hQ hV hm hyB hyold hmin_a (hinj.isFunctionFromTo.val_mem hz)
        (by rw [← hσa]; exact hodrB hz hz₀ hzu)
    have hgt (z : M) (hz : z ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)))
        (huz : (sigdcn (uc t) l) [odrOne (aoc (uc t) ﹫ ((1 : ℕ) : M))] z) :
        !(dctUZero, !(c, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
          ((σ ﹫ ((1 : ℕ) : M)) ﹫ z) :=
      yStar_lt_of_le hQ hV hlt_a (.inr (by rw [← hσa]; exact hodrB hz₀ hz huz))
    obtain ⟨hxN, hfo⟩ := xStar_two_mem hP hQ hV hVct hm hp hct hdl hσa haT hy hcct hdc hje
      hsame hcase hlt hgt
    have hprt := prt_xStar_two hP hQ hV hm hm0 ht hct hdl hσ hfo haN (orderedPair_ne_empty _ _)
      hlt_a hmin_a hσa
    refine ⟨_, hxN, by rw [uc_orderedPair]; exact hdV, hprt, uc_orderedPair,
      fun V' t' σ' hr hprt' haoc hsig ↦ ?_⟩
    exact chd_cmp_xStar_two hP hQ hV hm hm0 hp hct hdl hxN hσa hY hr hprt' haoc hsig
  · -- `t` discontinuous: `x* = (V, (t*, σ ∪ {s ↦ y*}))`
    obtain ⟨hd5, -, hlv01, hucfn⟩ := ucf_props_of_mem_stduoci_one hUt hdct hst0
    have h3t : ((3 : ℕ) : M) ∈ dom (uc t) := by
      rw [hd5]
      exact natCast_mem_natCast_iff.mpr (by omega)
    have hlv : ucflvl (uc t) = ((1 : ℕ) : M) := by
      rcases hlv01 with h | h
      · exfalso
        have h' : lvl (ucflvldcn (uc t)) = ∅ := h
        rw [embUcf, ucfOrLast, if_pos h3t, embUcfAux, if_pos h', tpUcfZero,
          orderedPair_eq_orderedPair_iff] at hucfU
        exact natCast_one_ne_empty hucfU.left.symm
      · exact h
    rw [hlv] at hucfn
    have hucf : tpUcf Q (iniSegAoc V (⋃₀ dom (sig V))) ((σ ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc t)) =
        !(((1 : ℕ) : M), w) := by
      have hlv' : lvl (ucflvldcn (uc t)) = ((1 : ℕ) : M) := hlv
      rw [embUcf, ucfOrLast, if_pos h3t, embUcfAux, hlv', if_neg natCast_one_ne_empty] at hucfU
      exact hucfU
    obtain ⟨qa, ha, hσa, hqa, hqart, hha, haT, haN⟩ := ha_of hucfn hucf
    rw [hσa] at hucf
    obtain ⟨c, h', hcn, hh', hy, hcct, hcchd, ⟨j, hdc, hje, hsame, hcase⟩, hlt_a, hmin_a, hY⟩ :=
      exists_yStar hQ hV hm hwR hwl hqa hqart hha hucf haN
    have hj : j ∈ dom (sig (uc c)) := by
      rw [dom_sig_uc_eq_depOf hQ2 hcn, hdc]
      exact mem_succ_self j
    have hyold := not_mem_lastSeg_of_sigImg_eq hQ hV hm hy hj hje
    have hyB : !(dctUZero, !(c, h')) ∈ ndOf (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)) :=
      (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX).mpr (.inr hy)
    obtain ⟨tc, htc, hext, htcct, htcchd, htcmin⟩ := exists_ct_chd hP ht hdct (.inr hlv)
    obtain ⟨-, -, hsU, hsubc, hnear⟩ := ext_one_tree hext
    obtain ⟨hsu, hsmin⟩ := hnear hst0
    have hUtc :=
      uc_mem_stduoci_of_mem_otci_two hP (mem_ndOf_of_mem_chdOf (otciCond_two hP).left htc)
    have hRc := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci
      (aoc_mem_aotci_of_mem_stduoci_one hUtc) (mem_succ_self _))).left
    have hlt (z : M) (hz : z ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)))
        (hzs : z [odrOne (aoc (uc tc) ﹫ ((1 : ℕ) : M))] (sigdcn (uc tc) (dom (sig (uc t))))) :
        ((σ ﹫ ((1 : ℕ) : M)) ﹫ z) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
          !(dctUZero, !(c, h')) := by
      have hzu : z [odrOne (aoc (uc t) ﹫ ((1 : ℕ) : M))] (ucfdcn (uc t)) :=
        (hsubc.right z hz _ hucfn).mpr (hRc.trans hzs hsu)
      exact lt_yStar_of_lt hQ hV hm hyB hyold hmin_a (hinj.isFunctionFromTo.val_mem hz)
        (by rw [← hσa]; exact hodrB hz hucfn hzu)
    have hgt (z : M) (hz : z ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)))
        (hsz : (sigdcn (uc tc) (dom (sig (uc t)))) [odrOne (aoc (uc tc) ﹫ ((1 : ℕ) : M))] z) :
        !(dctUZero, !(c, h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))]
          ((σ ﹫ ((1 : ℕ) : M)) ﹫ z) := by
      refine yStar_lt_of_le hQ hV hlt_a ?_
      rcases hsmin z hz hsz with rfl | h''
      · exact .inl hσa
      · exact .inr (by rw [← hσa]; exact hodrB hucfn hz ((hsubc.right _ hucfn z hz).mpr h''))
    have hdqa : dom (sig (uc qa)) = depOf (Q ﹫ 2) qa := dom_sig_uc_eq_depOf hQ2 hqa
    have hold (i : M) (hi : i ∈ j) :
        sigImg (aoc V) c h' i ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)) := by
      rw [hsame i hi]
      refine (sigImg_spec hQ2 hqa hX' hha ?_).left
      rw [hdqa]
      rcases hcase with h'' | ⟨h'', -⟩
      · rw [h'']; exact hi
      · rw [h'']; exact mem_succ_of_mem hi
    obtain ⟨hxN, hfo⟩ := xStar_one_mem hP hQ hV hVct hm hp htc hext hy hcct hdc hje hold hlt hgt
    have hlv0 : ucflvl (uc t) ≠ ∅ := by rw [hlv]; exact natCast_one_ne_empty
    have hprt := prt_xStar_one hP hQ hV hm hm0 ht htc hσ hsU hfo haN hlt_a hmin_a hlv0 hucfn hσa
    refine ⟨_, hxN, by rw [uc_orderedPair]; exact hdV, hprt, uc_orderedPair,
      fun V' t' σ' hr hprt' haoc hsig ↦ ?_⟩
    exact chd_cmp_xStar_one hP hQ hV hm hm0 hp hdct htc htcchd htcmin htcct hsU hxN hlv0 hucfn hσa
      hY hr hprt' haoc hsig

end LeastChdNe

section LeastChdFinal

variable {P Q : M}

/-- Every extension `q` of the `uoci` of a node `p` of `P ⊗ Q` has a least child `x` with
`x_uc = q` -/
theorem exists_isLeastChd (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {p q : M} (hp : p ∈ tensorProdTwoTwoNds P Q) (hq : !(uc p, q) ∈ ciExt ((1 : ℕ) : M)) :
    ∃ x, IsLeastChd P Q p q x := by
  have hp' := hp
  rw [mem_tensorProdTwoTwoNds_iff] at hp'
  obtain ⟨t, -, U, -, σ, -, -, rfl⟩ := hp'
  rw [uc_orderedPair] at hq
  obtain ⟨hUs, hqs, hUd, hqct⟩ := mem_ciExt_props hq
  obtain ⟨-, hsU, hm', -⟩ := dom_sig_of_mem_ciExt_one hq
  have hm : ⋃₀ dom (sig q) ∈ dom (sig q) := by rw [hsU]; exact hm'
  have hUeq : iniSeg q (⋃₀ dom (sig q)) = U := by rw [hsU]; exact iniSeg_eq_of_mem_ciExt_one hq
  rw [← hUeq] at hp ⊢
  by_cases hm0 : ⋃₀ dom (sig q) = ∅
  · exact isLeastChd_root hP hQ hqs hqct hm hm0 hp
  · have hR : iniSegRight q (⋃₀ dom (sig q)) ≠ ∅ := by
      intro hR
      rcases (exists_mem_ciExt_one_iff hUs hUd).mp ⟨q, hq⟩ with hs | hl
      · apply hm0
        rw [hsU, hs, dom_empty]
      · rw [← hUeq, ucflvl, (ucflvldcn_iniSeg hm0).left, iniSegUcf, if_pos hR, tpUcfZero,
          lvl_orderedPair] at hl
        exact natCast_one_ne_empty hl.symm
    exact isLeastChd_of_ne hP hQ hqs hqct hm hm0 hR hp

/-- The least child of the extension `q`: a child with key `q_aoc`, least in its linearly ordered
set, and the only continuous one -/
theorem exists_least_chd_tensorProdTwoTwo (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) {p q : M} (hp : p ∈ ndOf (tensorProdTwoTwo P Q))
    (hq : !(uc p, q) ∈ ciExt ((1 : ℕ) : M)) :
    ∃ x ∈ chdOf (tensorProdTwoTwo P Q) p, uc x = q ∧
      (∀ r ∈ chdOf (tensorProdTwoTwo P Q) p, aoc (uc r) = aoc (uc x) →
        r = x ∨ x [tensorProdTwoTwoOdr P Q] r) ∧
      ∀ r ∈ chdOf (tensorProdTwoTwo P Q) p, aoc (uc r) = aoc (uc x) → ctp (uc r) = ct → r = x := by
  have hpN : p ∈ tensorProdTwoTwoNds P Q := by rw [← ndOf_tensorProdTwoTwo]; exact hp
  obtain ⟨x, hxN, hxd, hxp, hxq, hmin⟩ := exists_isLeastChd hP hQ hpN hq
  have hxc : x ∈ chdOf (tensorProdTwoTwo P Q) p :=
    (mem_chdOf_tensorProdTwoTwo_iff hpN).mpr ⟨hxN, hxd, hxp⟩
  have hqs := (mem_ciExt_props hq).right.left
  have hr_data {r : M} (hr : r ∈ chdOf (tensorProdTwoTwo P Q) p) (hk : aoc (uc r) = aoc (uc x)) :
      (r = x ∨ x [tensorProdTwoTwoOdr P Q] r) ∧ (ctp (uc r) = ct → r = x) := by
    obtain ⟨hrN, -, hrp⟩ := (mem_chdOf_tensorProdTwoTwo_iff hpN).mp hr
    have hrN' := hrN
    rw [mem_tensorProdTwoTwoNds_iff] at hrN'
    obtain ⟨t', -, V', hV', σ', -, -, rfl⟩ := hrN'
    rw [uc_orderedPair, hxq] at hk
    rw [uc_orderedPair]
    exact hmin V' t' σ' hrN hrp hk (sig_eq_of_aoc_eq (natCast_mem_omega 1) hV' hqs hk)
  exact ⟨x, hxc, hxq, fun r hr hk ↦ (hr_data hr hk).left, fun r hr hk ↦ (hr_data hr hk).right⟩

end LeastChdFinal


/-- The keys of the children of a node of `P ⊗ Q` are the arrays of the extensions of its
`uoci` -/
theorem keys_chdOf_tensorProdTwoTwo (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {p : M} (hp : p ∈ ndOf (tensorProdTwoTwo P Q)) (D : M) :
    (∃ q ∈ chdOf (tensorProdTwoTwo P Q) p, aoc (uc q) = D) ↔
      ∃ q, !(uc p, q) ∈ ciExt ((1 : ℕ) : M) ∧ aoc q = D := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact exists_mem_ciExt_of_mem_chdOf_tensorProdTwoTwo hP hQ hp hx
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨x, hx, hxq, -, -⟩ := exists_least_chd_tensorProdTwoTwo hP hQ hp hq
    exact ⟨x, hx, by rw [hxq]⟩

/-- The children of a node of `P ⊗ Q` with the key of an extension `q` of its `uoci` have the
signature of `q`, and the least one is the one of type `ct` -/
theorem chdlosOf_tensorProdTwoTwo (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {p : M} (hp : p ∈ ndOf (tensorProdTwoTwo P Q)) {q : M} (hq : !(uc p, q) ∈ ciExt ((1 : ℕ) : M))
    {r : M} (hr : r ∈ losSet (chdlosOf (tensorProdTwoTwo P Q) p ﹫ aoc q)) :
    sig (uc r) = sig q ∧ (IsLeastLos (chdlosOf (tensorProdTwoTwo P Q) p ﹫ aoc q) r ↔
      ctp (uc r) = ct) := by
  refine ⟨sig_uc_eq_of_mem_losSet_chdlosOf_tensorProdTwoTwo hP hQ hp hq hr, ?_⟩
  obtain ⟨x, hxc, hxq, hmin, hct⟩ := exists_least_chd_tensorProdTwoTwo hP hQ hp hq
  have hrmem := (mem_losSet_chdlosOf_tensorProdTwoTwo_iff hP hQ hp _).mp hr
  have hkey : aoc q = aoc (uc x) := by rw [hxq]
  have hk : aoc (uc r) = aoc (uc x) := hrmem.right.trans hkey
  constructor
  · intro hl
    rw [hkey] at hl
    rw [eq_of_isLeastLos_tensorProdTwoTwo hP hQ hp hxc hmin hl, hxq]
    exact (mem_ciExt_props hq).right.right.right
  · intro hc
    rw [hct r hrmem.left hk hc, hkey]
    exact isLeastLos_of_forall_tensorProdTwoTwo hP hQ hp hxc hmin

/-- The children of a node of `P ⊗ Q` with the key of an extension of its `uoci` have a least
element -/
theorem exists_isLeastLos_chdlosOf_tensorProdTwoTwo (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) {p : M} (hp : p ∈ ndOf (tensorProdTwoTwo P Q)) {q : M}
    (hq : !(uc p, q) ∈ ciExt ((1 : ℕ) : M)) :
    ∃ r ∈ losSet (chdlosOf (tensorProdTwoTwo P Q) p ﹫ aoc q),
      IsLeastLos (chdlosOf (tensorProdTwoTwo P Q) p ﹫ aoc q) r := by
  obtain ⟨x, hxc, hxq, hmin, -⟩ := exists_least_chd_tensorProdTwoTwo hP hQ hp hq
  refine ⟨x, (mem_losSet_chdlosOf_tensorProdTwoTwo_iff hP hQ hp _).mpr ⟨hxc, by rw [hxq]⟩, ?_⟩
  have h := isLeastLos_of_forall_tensorProdTwoTwo hP hQ hp hxc hmin
  rwa [hxq] at h

/-- The least element of a strictly linearly ordered set (`∅` if there is none) -/
noncomputable def leastLos (B : M) : M := ⋃₀ (losSet B ∩₀ fun r ↦ IsLeastLos B r)

/-- The least element of a strictly linearly ordered set is unique -/
theorem leastLos_eq {B r : M} (hB : IsStrictLinearOrderedSet B) (hr : IsLeastLos B r) :
    leastLos B = r := by
  have hR := hB.isStrictLinearOrder
  have hset : (losSet B ∩₀ fun r ↦ IsLeastLos B r) = {r} := by
    ext x
    rw [mem_comprehension_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxl⟩
      rcases hR.isTrichotomousOn x hx r hr.left with h | h | h
      · exact (hr.right x hx h).elim
      · exact h
      · exact (hxl.right r hr.left h).elim
    · rintro rfl
      exact ⟨hr.left, hr⟩
  rw [leastLos, hset, sUnion_singleton]

/-- The least child of the node `p` of `P ⊗ Q` with the key of the extension `q` of `p_uc` -/
noncomputable def leastChdOf (P Q p q : M) : M :=
  leastLos (chdlosOf (tensorProdTwoTwo P Q) p ﹫ aoc q)

/-- The least child `leastChdOf P Q p q` is a child with identifier `q`, the least element of its
linearly ordered set -/
theorem leastChdOf_spec (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {p q : M} (hp : p ∈ ndOf (tensorProdTwoTwo P Q)) (hq : !(uc p, q) ∈ ciExt ((1 : ℕ) : M)) :
    leastChdOf P Q p q ∈ chdOf (tensorProdTwoTwo P Q) p ∧ uc (leastChdOf P Q p q) = q ∧
      IsLeastLos (chdlosOf (tensorProdTwoTwo P Q) p ﹫ aoc q) (leastChdOf P Q p q) := by
  obtain ⟨x, hxc, hxq, hmin, -⟩ := exists_least_chd_tensorProdTwoTwo hP hQ hp hq
  have hl := isLeastLos_of_forall_tensorProdTwoTwo hP hQ hp hxc hmin
  rw [hxq] at hl
  have hB := isStrictLinearOrderedSet_chdlosOf (isSLOT_tensorProdTwoTwo hP hQ) hp hxc
  change IsStrictLinearOrderedSet (chdlosOf (tensorProdTwoTwo P Q) p ﹫ aoc (uc x)) at hB
  rw [hxq] at hB
  rw [leastChdOf, leastLos_eq hB hl]
  exact ⟨hxc, hxq, hl⟩

/-- `P ⊗ Q ∈ otci_2` for `P ∈ otci_2` and `Q ∈ aotci_2` -/
theorem tensorProdTwoTwo_mem_otci (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M)) :
    tensorProdTwoTwo P Q ∈ otci ((2 : ℕ) : M) := by
  rw [mem_otci_iff_of_ne_empty natCast_two_ne_empty, OtciCond, sUnion_natCast_two,
    stduociL_ciRec_restrict natCast_one_mem_two, trvuociL_ciRec_restrict natCast_one_mem_two,
    extL_ciRec_restrict natCast_one_mem_two]
  obtain ⟨r, hr, hru⟩ := rtOf_tensorProdTwoTwo hP hQ
  refine ⟨isSLOT_tensorProdTwoTwo hP hQ,
    fun p hp ↦ uc_mem_and_lbl_mem_of_mem_tensorProdTwoTwo hP hQ hp, fun r' hr' ↦ ?_,
    fun _ ↦ ⟨r, hr⟩, fun p hp ↦ ⟨keys_chdOf_tensorProdTwoTwo hP hQ hp,
      fun q hq r hr ↦ chdlosOf_tensorProdTwoTwo hP hQ hp hq hr,
      fun q hq ↦ exists_isLeastLos_chdlosOf_tensorProdTwoTwo hP hQ hp hq⟩⟩
  rw [hr, mem_singleton_iff] at hr'
  rw [hr']
  exact hru

/-- The `aotci_1` part of an array in `aotci_2` -/
theorem restrict_two_mem_aotci_one (hQ : Q ∈ aotci ((2 : ℕ) : M)) :
    Q ↾ (2 : M) ∈ aotci ((1 : ℕ) : M) := by
  obtain ⟨hQf, hQdom, -⟩ := mem_aotci_iff.mp hQ
  have hsub : (2 : M) ⊆ dom Q := fun x hx ↦ by
    rw [hQdom]
    exact mem_succ_of_mem hx
  have hdom : dom (Q ↾ (2 : M)) = (2 : M) := dom_restrict_of_subset hQf hsub
  rw [mem_aotci_iff]
  refine ⟨hQf.restrict _, hdom, fun i hi ↦ ?_, ?_⟩
  · have hi2 : i ∈ (2 : M) := mem_succ_of_mem hi
    rw [otciL_ciRec_restrict hi, val_restrict _ hQf hi2 (hsub hi2)]
    exact val_mem_otci_of_mem_aotci hQ (mem_succ_of_mem hi2)
  · have h12 : ((1 : ℕ) : M) ∈ (2 : M) := natCast_one_mem_two
    rw [val_restrict _ hQf h12 (hsub h12)]
    exact val_mem_otci_of_mem_aotci hQ (mem_succ_of_mem h12)

/-- `T ⊗ Q ∈ aotci_2` for `T, Q ∈ aotci_2` -/
theorem tensorProdATwoATwo_mem_aotci (hT : T ∈ aotci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) : tensorProdATwoATwo T Q ∈ aotci ((2 : ℕ) : M) := by
  have hB := tensorProdATwoAOne_mem_aotci hT (restrict_two_mem_aotci_one hQ)
  have hX := tensorProdTwoTwo_mem_otci (val_mem_otci_of_mem_aotci hT (mem_succ_self _)) hQ
  obtain ⟨hBf, hBdom, -⟩ := mem_aotci_iff.mp hB
  rw [mem_aotci_iff]
  refine ⟨hBf.cc _, by rw [tensorProdATwoATwo, dom_cc, hBdom]; rfl, fun i hi ↦ ?_, ?_⟩
  · rw [otciL_ciRec_restrict hi, tensorProdATwoATwo, cc_val_of_mem hBf _ (by rw [hBdom]; exact hi)]
    exact val_mem_otci_of_mem_aotci hB hi
  · have h := cc_val_self hBf (tensorProdTwoTwo (T ﹫ 2) Q)
    rw [hBdom] at h
    rw [tensorProdATwoATwo]
    change cc (tensorProdATwoAOne T (Q ↾ 2)) (tensorProdTwoTwo (T ﹫ 2) Q) ﹫
      succ ((1 : ℕ) : M) ∈ _
    rw [h]
    exact hX

section DefinableTwoTwo

/-! ### Definability of `T ⊗ Q` -/

instance : ClassFunction.Definable (fun w : M ↦
    tensorProdTwoTwoCoordOdr (left w) (left (right w)) (right (right w))) Set.univ := by
  unfold tensorProdTwoTwoCoordOdr
  have : ClassFunction.Definable (fun w : M ↦
      tensorProdATwoAOne (left (right w)) (right (right w))) Set.univ :=
    ClassFunction.Definable.comp₁ (H := fun z : M ↦ tensorProdATwoAOne (left z) (right z))
      (F := fun w : M ↦ right w)
  have : ClassFunction.Definable (fun w : M ↦ losOdr (rtlosOf (tensorProdATwoAOne (left (right w))
      (right (right w)) ﹫ ((1 : ℕ) : M)) ﹫ trvAZero)) Set.univ :=
    ClassFunction.Definable.comp₁
      (H := fun T : M ↦ losOdr (rtlosOf (T ﹫ ((1 : ℕ) : M)) ﹫ trvAZero))
      (F := fun w : M ↦ tensorProdATwoAOne (left (right w)) (right (right w)))
  have : ClassFunction.Definable (fun w : M ↦
      ndOf (tensorProdATwoAOne (left (right w)) (right (right w)) ﹫ ((1 : ℕ) : M))) Set.univ :=
    ClassFunction.Definable.comp₁ (H := fun T : M ↦ ndOf (T ﹫ ((1 : ℕ) : M)))
      (F := fun w : M ↦ tensorProdATwoAOne (left (right w)) (right (right w)))
  have : ClassFunction.Definable (fun w : M ↦ sblOdrOf (left w)) Set.univ :=
    ClassFunction.Definable.comp₁ (H := fun P : M ↦ sblOdrOf P)
  have : Multiclass.Definable
      (fun ys : Fin 5 → M ↦ lexProd (ys 0) (ys 1) (ys 2) (ys 3) = ys 4) Set.univ :=
    (inferInstance : MulticlassFunction.Definable
      (fun ys : Fin 4 → M ↦ lexProd (ys 0) (ys 1) (ys 2) (ys 3)) Set.univ).1
  exact ClassFunction.Definable.comp₄ (H := lexProd) (E := fun w : M ↦ ndOf (left w))

/-- The Brouwer–Kleene comparison of the sequences of `a` and `b` for the key `K`, with
`z = (P, Q)` -/
def TwoTwoBKLt (z K a b : M) : Prop :=
  BKLt (tensorProdTwoTwoCoordOdr (left z) (right z) K) (tensorProdTwoAOneSeq (left z) a)
    (tensorProdTwoAOneSeq (left z) b)

instance : Multiclass.Definable
    (fun xs : Fin 4 → M ↦ TwoTwoBKLt (xs 0) (xs 1) (xs 2) (xs 3)) Set.univ := by
  obtain ⟨C, hC⟩ : ∃ C : ClassFunction M,
      C = fun w ↦ tensorProdTwoTwoCoordOdr (left (left w)) (right (left w)) (right w) :=
    ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ClassFunction M,
      S = fun w ↦ tensorProdTwoAOneSeq (left (left w)) (right w) := ⟨_, rfl⟩
  have : C.Definable Set.univ := by
    rw [hC]
    exact ClassFunction.Definable.comp₁ (H := fun w : M ↦
      tensorProdTwoTwoCoordOdr (left w) (left (right w)) (right (right w)))
      (F := fun w : M ↦ !(left (left w), !(right (left w), right w)))
      |> fun h ↦ by simpa only [left_orderedPair, right_orderedPair] using h
  have : S.Definable Set.univ := by
    rw [hS]
    exact ClassFunction.Definable.comp₁ (H := fun w : M ↦ tensorProdTwoAOneSeq (left w) (right w))
      (F := fun w : M ↦ !(left (left w), right w))
      |> fun h ↦ by simpa only [left_orderedPair, right_orderedPair] using h
  have h : (fun xs : Fin 4 → M ↦ TwoTwoBKLt (xs 0) (xs 1) (xs 2) (xs 3)) = fun xs ↦
      ∃ u v v', u = !(xs 0, xs 1) ∧ v = !(xs 0, xs 2) ∧ v' = !(xs 0, xs 3) ∧
        ∃ R s t, C u = R ∧ S v = s ∧ S v' = t ∧ BKLt R s t := by
    funext xs
    rw [hC, hS]
    apply propext
    constructor
    · intro h
      exact ⟨_, _, _, rfl, rfl, rfl, _, _, _, rfl, rfl, rfl, by
        simpa [left_orderedPair, right_orderedPair, TwoTwoBKLt] using h⟩
    · rintro ⟨z, w, w', rfl, rfl, rfl, R, s, t, rfl, rfl, rfl, h⟩
      simpa [left_orderedPair, right_orderedPair, TwoTwoBKLt] using h
  rw [h]
  infer_instance

instance : Multiclass.Definable
    (fun xs : Fin 4 → M ↦ TensorProdTwoTwoLt (xs 0) (xs 1) (xs 2) (xs 3)) Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ TensorProdTwoTwoLt (xs 0) (xs 1) (xs 2) (xs 3)) = fun xs ↦
      aoc (uc (xs 2)) = aoc (uc (xs 3)) ∧
        TwoTwoBKLt !(xs 0, xs 1) (aoc (uc (xs 2))) (lbl (xs 2)) (lbl (xs 3)) := by
    funext xs
    simp [TensorProdTwoTwoLt, TwoTwoBKLt, left_orderedPair, right_orderedPair]
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦
      TwoTwoBKLt !(xs 0, xs 1) (aoc (uc (xs 2))) (lbl (xs 2)) (lbl (xs 3))) Set.univ := by
    infer_instance
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦ aoc (uc (xs 2)) = aoc (uc (xs 3)))
      Set.univ := by
    infer_instance
  rw [h]
  infer_instance

theorem mem_tensorProdTwoTwoOdr_iff {P Q e : M} : e ∈ tensorProdTwoTwoOdr P Q ↔
    e ∈ tensorProdTwoTwoNds P Q ×ˢ tensorProdTwoTwoNds P Q ∧
      TensorProdTwoTwoLt P Q (left e) (right e) := by
  rw [tensorProdTwoTwoOdr, mem_comprehension_iff]

instance : ClassFunction.Definable (fun z : M ↦ tensorProdTwoTwoOdr (left z) (right z))
    Set.univ := by
  obtain ⟨N, hN⟩ : ∃ N : ClassFunction M,
      N = fun z ↦ tensorProdTwoTwoNds (left z) (right z) := ⟨_, rfl⟩
  have : N.Definable Set.univ := by
    rw [hN]
    infer_instance
  refine .of_mem_iff (R := fun z e ↦ ∃ X, N z = X ∧ e ∈ X ×ˢ X ∧
    TensorProdTwoTwoLt (left z) (right z) (left e) (right e)) fun z e ↦ ?_
  rw [mem_tensorProdTwoTwoOdr_iff]
  constructor
  · rintro ⟨he, hlt⟩
    exact ⟨_, by rw [hN], he, hlt⟩
  · rintro ⟨X, hX, he, hlt⟩
    rw [hN] at hX
    subst hX
    exact ⟨he, hlt⟩

instance : ClassFunction.Definable (fun z : M ↦ (tensorProdTwoTwoTs (left z) (right z)).toM)
    Set.univ := by
  obtain ⟨N, hN⟩ : ∃ N : ClassFunction M,
      N = fun z ↦ tensorProdTwoTwoNds (left z) (right z) := ⟨_, rfl⟩
  have : N.Definable Set.univ := by
    rw [hN]
    infer_instance
  have hD : ClassFunction.Definable (fun z ↦ (fun x ↦ dom (sig (uc x))) ↾₀ N z) Set.univ :=
    ClassFunction.Definable.toSetRestrictedTo (G := fun _ x ↦ dom (sig (uc x))) (D := N)
  have hG : Multiclass.Definable (fun xs : Fin 3 → M ↦
      (fun z x ↦ N z ∩₀ fun y ↦ IsPrtChd (left z) (right z) x y) (xs 0) (xs 1) = xs 2)
      Set.univ := by
    have h : (fun xs : Fin 3 → M ↦
        (fun z x ↦ N z ∩₀ fun y ↦ IsPrtChd (left z) (right z) x y) (xs 0) (xs 1) = xs 2) =
        fun xs ↦ ∃ A P Q, N (xs 0) = A ∧ P = left (xs 0) ∧ Q = right (xs 0) ∧
          (∀ y ∈ xs 2, y ∈ A ∧ IsPrtChd P Q (xs 1) y) ∧
            ∀ y ∈ A, IsPrtChd P Q (xs 1) y → y ∈ xs 2 := by
      funext xs
      apply propext
      constructor
      · intro h
        rw [← h]
        refine ⟨_, _, _, rfl, rfl, rfl, fun y hy ↦ (mem_comprehension_iff ..).mp hy,
          fun y hy hc ↦ (mem_comprehension_iff ..).mpr ⟨hy, hc⟩⟩
      · rintro ⟨A, P, Q, hA, rfl, rfl, h₁, h₂⟩
        ext y
        rw [mem_comprehension_iff, hA]
        exact ⟨fun h ↦ h₂ y h.left h.right, fun h ↦ h₁ y h⟩
    rw [h]
    infer_instance
  have hC : ClassFunction.Definable (fun z ↦
      (fun x ↦ N z ∩₀ fun y ↦ IsPrtChd (left z) (right z) x y) ↾₀ N z) Set.univ :=
    ClassFunction.Definable.toSetRestrictedTo
      (G := fun z x ↦ N z ∩₀ fun y ↦ IsPrtChd (left z) (right z) x y) (D := N)
  have hDC : ClassFunction.Definable (fun z ↦ !((fun x ↦ dom (sig (uc x))) ↾₀ N z,
      (fun x ↦ N z ∩₀ fun y ↦ IsPrtChd (left z) (right z) x y) ↾₀ N z)) Set.univ :=
    ClassFunction.Definable.comp₂ (H := fun a b ↦ !(a, b))
  have h : (fun z : M ↦ (tensorProdTwoTwoTs (left z) (right z)).toM) = fun z ↦
      !(N z, !((fun x ↦ dom (sig (uc x))) ↾₀ N z,
        (fun x ↦ N z ∩₀ fun y ↦ IsPrtChd (left z) (right z) x y) ↾₀ N z)) := by
    funext z
    rw [hN]
    rfl
  rw [h]
  exact ClassFunction.Definable.comp₂ (H := fun a b ↦ !(a, b))

instance : ClassFunction.Definable (fun w : M ↦ keyLosFn (left w) (right w)) Set.univ := by
  unfold keyLosFn
  have : Multiclass.Definable (fun xs : Fin 3 → M ↦
      (fun w D ↦ keyLos (left w) (right w) D) (xs 0) (xs 1) = xs 2) Set.univ := by
    have h : (fun xs : Fin 3 → M ↦ (fun w D ↦ keyLos (left w) (right w) D) (xs 0) (xs 1) = xs 2) =
        fun xs ↦ ∃ R X, R = left (xs 0) ∧ X = right (xs 0) ∧ keyLos R X (xs 1) = xs 2 := by
      funext xs
      simp
    rw [h]
    infer_instance
  have : ClassFunction.Definable (fun w : M ↦ keysOf (right w)) Set.univ :=
    ClassFunction.Definable.comp₁ (H := fun X : M ↦ keysOf X)
  exact ClassFunction.Definable.toSetRestrictedTo (G := fun w D ↦ keyLos (left w) (right w) D)
    (D := fun w ↦ keysOf (right w))

instance : ClassFunction.Definable (fun z : M ↦ tensorProdTwoTwo (left z) (right z))
    Set.univ := by
  obtain ⟨T, hT⟩ : ∃ T : ClassFunction M,
      T = fun z ↦ (tensorProdTwoTwoTs (left z) (right z)).toM := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ClassFunction M,
      R = fun z ↦ tensorProdTwoTwoOdr (left z) (right z) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ClassFunction M, K = fun w ↦ keyLosFn (left w) (right w) := ⟨_, rfl⟩
  have : T.Definable Set.univ := by
    rw [hT]
    infer_instance
  have : R.Definable Set.univ := by
    rw [hR]
    infer_instance
  have : K.Definable Set.univ := by
    rw [hK]
    infer_instance
  have hS : ClassFunction.Definable (fun z ↦ (TreeStructure.ofM (T z)).sblptn) Set.univ :=
    ClassFunction.Definable.comp₁ (H := fun x : M ↦ (TreeStructure.ofM x).sblptn)
  have hG : Multiclass.Definable (fun xs : Fin 3 → M ↦
      (fun z X ↦ K !(R z, X)) (xs 0) (xs 1) = xs 2) Set.univ := by
    have h : (fun xs : Fin 3 → M ↦ (fun z X ↦ K !(R z, X)) (xs 0) (xs 1) = xs 2) =
        fun xs ↦ ∃ r w, R (xs 0) = r ∧ w = !(r, xs 1) ∧ K w = xs 2 := by
      funext xs
      apply propext
      constructor
      · intro h
        exact ⟨_, _, rfl, rfl, h⟩
      · rintro ⟨r, w, rfl, rfl, h⟩
        exact h
    rw [h]
    infer_instance
  have hF : ClassFunction.Definable (fun z ↦ (fun X ↦ K !(R z, X)) ↾₀
      (TreeStructure.ofM (T z)).sblptn) Set.univ :=
    ClassFunction.Definable.toSetRestrictedTo (G := fun z X ↦ K !(R z, X))
      (D := fun z ↦ (TreeStructure.ofM (T z)).sblptn)
  have h : (fun z : M ↦ tensorProdTwoTwo (left z) (right z)) = fun z ↦
      !(T z, (fun X ↦ K !(R z, X)) ↾₀ (TreeStructure.ofM (T z)).sblptn) := by
    funext z
    rw [hT, hR, hK]
    simp only [left_orderedPair, right_orderedPair]
    rfl
  rw [h]
  exact ClassFunction.Definable.comp₂ (H := fun a b ↦ !(a, b))

end DefinableTwoTwo

/-- `(T, Q) ↦ T ⊗ Q` is definable -/
theorem definable_tensorProdATwoATwo :
    ClassFunction.Definable (fun z : M ↦ tensorProdATwoATwo (left z) (right z)) Set.univ := by
  unfold tensorProdATwoATwo
  have : ClassFunction.Definable (fun z : M ↦ tensorProdATwoAOne (left z) (right z ↾ 2))
      Set.univ := by
    have h := ClassFunction.Definable.comp₁
      (H := fun z : M ↦ tensorProdATwoAOne (left z) (right z))
      (F := fun z : M ↦ !(left z, right z ↾ 2))
    simp only [left_orderedPair, right_orderedPair] at h
    exact h
  have : ClassFunction.Definable (fun z : M ↦ tensorProdTwoTwo (left z ﹫ 2) (right z))
      Set.univ := by
    have h := ClassFunction.Definable.comp₁
      (H := fun z : M ↦ tensorProdTwoTwo (left z) (right z))
      (F := fun z : M ↦ !(left z ﹫ 2, right z))
    simp only [left_orderedPair, right_orderedPair] at h
    exact h
  have : Multiclass.Definable (fun ys : Fin 3 → M ↦ cc (ys 0) (ys 1) = ys 2) Set.univ :=
    inferInstance
  exact ClassFunction.Definable.comp₂ (H := cc)

end TensorProd

end FirstOrder.Language.MemStructure
