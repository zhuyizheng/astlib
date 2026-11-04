/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.Defs
/-!
# Classification identifiers: basic properties

The lemmas `mem_otci_empty_iff`, `mem_otci_iff_of_ne_empty`, `mem_finotci_iff`, `mem_trvotci_iff`,
`mem_aotci_iff`, `mem_finaotci_iff`, `mem_trvaotci_iff`, `mem_uoci_iff_of_mem_omega`,
`mem_stduoci_iff`, `mem_trvuoci_iff` and `mem_ciExt_iff` characterize the sets of
`ClassificationIdentifier.Defs` by their conditions, where the levels below `n` are read off
`ciRec ↾₀ n` (`levComp_ciRec_restrict`).

`ext_0 = ∅` (`ciExt_empty`).
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language

namespace MemStructure

open RudimentaryTerm

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] {a b f P i : M}

section Pair

omit [L.ExtraConstantsUnaryRelationsOnly] in
@[simp]
theorem uc_orderedPair : uc !(a, b) = a := by
  simp [uc]

omit [L.ExtraConstantsUnaryRelationsOnly] in
@[simp]
theorem lbl_orderedPair : lbl !(a, b) = b := by
  simp [lbl]

omit [L.ExtraConstantsUnaryRelationsOnly] in
@[simp]
theorem lvl_orderedPair : lvl !(a, b) = a := by
  simp [lvl]

omit [L.ExtraConstantsUnaryRelationsOnly] in
@[simp]
theorem dcn_orderedPair : dcn !(a, b) = b := by
  simp [dcn]

end Pair

section Levels

variable [ModelsKP M]

omit [ModelsKP M] in
theorem mem_levUnion_iff (j : ℕ) (s n z : M) :
    z ∈ levUnion j s n ↔ ∃ i ∈ n, z ∈ levComp j s i := by
  simp [levUnion, levComp]

end Levels

section Bounds

variable [ModelsZF M]

theorem mem_dvals_iff (N z : M) : z ∈ dvals N ↔ ∃ a ∈ N, z = left a ﹫ ∅ := by
  simp [dvals]


open SLOTreeStructure in
/-- A semi-linearly ordered tree structure with nodes in `N` lies in `slotBound N` -/
theorem mem_slotBound {N P : M} (hP : IsSLOT P) (hN : ndOf P ⊆ N) : P ∈ slotBound N := by
  have hS : (ofM P).IsSLOTreeStructure := hP
  have hT := hS.isTreeStructure
  have hNd : (ofM P).ts.nd ⊆ N := hN
  have e₂ : (ofM P).ts.toM = !((ofM P).ts.nd, !((ofM P).ts.dep, (ofM P).ts.chd)) := by
    have h := congrArg TreeStructure.toM hT.eq_mk
    rwa [TreeStructure.toM_mk] at h
  have hP' : P = !(!((ofM P).ts.nd, !((ofM P).ts.dep, (ofM P).ts.chd)), (ofM P).losfn) :=
    calc P = (SLOTreeStructure.mk (ofM P).ts (ofM P).losfn).toM := congrArg toM hS.eq_mk
      _ = !((ofM P).ts.toM, (ofM P).losfn) := rfl
      _ = _ := by rw [e₂]
  rw [hP', slotBound, pair_mem_sprod_iff, pair_mem_sprod_iff, pair_mem_sprod_iff,
    mem_powerset_iff, mem_powerset_iff, mem_powerset_iff, mem_powerset_iff]
  refine ⟨⟨hNd, fun z hz ↦ ?_, fun z hz ↦ ?_⟩, fun z hz ↦ ?_⟩
  · -- the depth function
    have hz' := hT.dep_fromTo.subset_sprod hz
    rw [mem_sprod_iff] at hz' ⊢
    obtain ⟨a, ha, m, hm, rfl⟩ := hz'
    exact ⟨a, hNd ha, m, hm, rfl⟩
  · -- the children function
    obtain ⟨a, c, rfl⟩ := hT.isFunction_chd.isRelation hz
    have ha : a ∈ (ofM P).ts.nd := by
      rw [← hT.dom_chd, mem_dom_iff]
      exact ⟨c, hz⟩
    have hc : (ofM P).ts.chd ﹫ a = c := hT.isFunction_chd.val_eq_of_rel hz
    rw [pair_mem_sprod_iff, mem_powerset_iff, ← hc]
    exact ⟨hNd ha, fun b hb ↦ hNd (hT.chd_subset a ha hb)⟩
  · -- the linearly ordered sets
    obtain ⟨X, G, rfl⟩ := hS.isFunction_losfn.isRelation hz
    have hX : X ∈ (ofM P).sblptn := by
      rw [← hS.dom_losfn, mem_dom_iff]
      exact ⟨G, hz⟩
    have hG : (ofM P).losfn ﹫ X = G := hS.isFunction_losfn.val_eq_of_rel hz
    have hXN : X ⊆ N := fun a ha ↦ hNd (hT.subset_nd_of_mem_sblptn hX ha)
    rw [pair_mem_sprod_iff, mem_powerset_iff, mem_powerset_iff]
    refine ⟨hXN, fun w hw ↦ ?_⟩
    have hGf := hS.isFunction_losfn_val hX
    rw [hG] at hGf
    obtain ⟨D, B, rfl⟩ := hGf.isRelation hw
    have hD : D ∈ dom ((ofM P).losfn ﹫ X) := by
      rw [hG, mem_dom_iff]
      exact ⟨B, hw⟩
    have hB : ((ofM P).losfn ﹫ X) ﹫ D = B := by
      rw [hG]
      exact hGf.val_eq_of_rel hw
    have hlos := hS.isStrictLinearOrderedSet hX hD
    rw [hB] at hlos
    have hset {a : M} (ha : a ∈ losSet B) : a ∈ N := by
      rw [← hB, hS.mem_losSet_iff hX hD] at ha
      exact hXN ha.left
    obtain ⟨A, R, rfl⟩ := hlos.isOrderedPair
    rw [isStrictLinearOrderedSet_orderedPair_iff] at hlos
    rw [pair_mem_sprod_iff, pair_mem_sprod_iff, mem_powerset_iff, mem_powerset_iff, mem_dvals_iff]
    refine ⟨?_, fun a ha ↦ ?_, fun r hr ↦ ?_⟩
    · rw [hS.mem_dom_losfn_val_iff hX] at hD
      obtain ⟨a, ha, rfl⟩ := hD
      exact ⟨a, hXN ha, rfl⟩
    · exact hset (by rwa [losSet_orderedPair])
    · have hr' := hlos.isRelationOn.isSubset hr
      rw [mem_sprod_iff] at hr'
      obtain ⟨u, hu, v, hv, rfl⟩ := hr'
      rw [pair_mem_sprod_iff]
      exact ⟨hset (by rwa [losSet_orderedPair]), hset (by rwa [losSet_orderedPair])⟩

end Bounds

section Recursion

variable [ModelsZF M]

/-- The recursion equation: the level tuple of `n` is computed from those below `n` -/
theorem ciRec_eq (n : M) : ciRec n = ciStep (ciRec ↾₀ n) := ordRecursion_eq n

theorem ciRec_val {j : ℕ} (hj : j < 7) (n : M) :
    ciRec n ﹫ (j : M) = compS j (ciRec ↾₀ n) := by
  rw [ciRec_eq, ciStep, seqOf_val _ hj]

/-- The sequence of level tuples below `n` -/
theorem dom_ciRec_restrict (n : M) : dom (ciRec ↾₀ n) = n :=
  dom_toSetRestrictedTo (isSetRestrictedTo_of_definable n)

theorem levComp_ciRec_restrict (j : ℕ) {k n : M} (hk : k ∈ n) :
    levComp j (ciRec ↾₀ n) k = ciRec k ﹫ (j : M) := by
  rw [levComp, val_toSetRestrictedTo (isSetRestrictedTo_of_definable n) hk]

variable {n P z : M}

section Lookup

variable {k : M} (hk : k ∈ n)
include hk

theorem otciL_ciRec_restrict : otciL (ciRec ↾₀ n) k = otci k := levComp_ciRec_restrict 0 hk

theorem trvaotciL_ciRec_restrict : trvaotciL (ciRec ↾₀ n) k = trvaotci k :=
  levComp_ciRec_restrict 2 hk

theorem stduociL_ciRec_restrict : stduociL (ciRec ↾₀ n) k = stduoci k :=
  levComp_ciRec_restrict 4 hk

theorem trvuociL_ciRec_restrict : trvuociL (ciRec ↾₀ n) k = trvuoci k :=
  levComp_ciRec_restrict 5 hk

theorem extL_ciRec_restrict : extL (ciRec ↾₀ n) k = ciExt k := levComp_ciRec_restrict 6 hk

end Lookup

theorem mem_otci_iff : P ∈ otci n ↔ P ∈ otciBound (ciRec ↾₀ n) ∧
    ((n = ∅ ∧ Otci0Cond P) ∨ (n ≠ ∅ ∧ OtciCond (ciRec ↾₀ n) n P)) := by
  rw [otci, ciRec_val (j := 0) (by omega), compS, otciS, mem_comprehension_iff,
    dom_ciRec_restrict]

theorem otciS_ciRec_restrict : otciS (ciRec ↾₀ n) = otci n := by
  rw [otci, ciRec_val (j := 0) (by omega), compS]

theorem aotciS_ciRec_restrict : aotciS (ciRec ↾₀ n) = aotci n := by
  rw [aotci, ciRec_val (j := 1) (by omega), compS]

theorem trvaotciS_ciRec_restrict : trvaotciS (ciRec ↾₀ n) = trvaotci n := by
  rw [trvaotci, ciRec_val (j := 2) (by omega), compS]

theorem uociS_ciRec_restrict : uociS (ciRec ↾₀ n) = uoci n := by
  rw [uoci, ciRec_val (j := 3) (by omega), compS]

theorem stduociS_ciRec_restrict : stduociS (ciRec ↾₀ n) = stduoci n := by
  rw [stduoci, ciRec_val (j := 4) (by omega), compS]

theorem trvuociS_ciRec_restrict : trvuociS (ciRec ↾₀ n) = trvuoci n := by
  rw [trvuoci, ciRec_val (j := 5) (by omega), compS]

theorem extS_ciRec_restrict : extS (ciRec ↾₀ n) = ciExt n := by
  rw [ciExt, ciRec_val (j := 6) (by omega), compS]

theorem finaotciS_ciRec_restrict : finaotciS (ciRec ↾₀ n) = finaotci n := by
  rw [finaotciS, aotciS_ciRec_restrict, dom_ciRec_restrict]
  rfl

theorem mem_otci0_iff : P ∈ (otci0 : M) ↔ Otci0Cond P := by
  have hF : ∀ u ∈ 𝕍 (ω : M), ∃! w, otci0Rel ![u, w] := fun u _ ↦
    ⟨irmrtOf emptySLOT !(otci0Uc, u), by simp [otci0Rel],
      fun w hw ↦ by simpa [otci0Rel] using hw⟩
  rw [otci0, mem_replacement_iff hF, Otci0Cond]
  simp [otci0Rel]

/-- `otci_0 = {∅_slots_irmrt((otci0Uc, p)) | p ∈ V_ω}` -/
theorem mem_otci_empty_iff : P ∈ otci (∅ : M) ↔ Otci0Cond P := by
  rw [mem_otci_iff]
  constructor
  · rintro ⟨-, ⟨-, h⟩ | ⟨hne, -⟩⟩
    · exact h
    · exact (hne rfl).elim
  · intro h
    refine ⟨?_, Or.inl ⟨rfl, h⟩⟩
    rw [otciBound, mem_union_iff, mem_otci0_iff]
    exact Or.inl h

/-- For `n > 0`, `otci_n` consists of the semi-linearly ordered tree structures satisfying
`OtciCond` -/
theorem mem_otci_iff_of_ne_empty (hn : n ≠ ∅) :
    P ∈ otci n ↔ OtciCond (ciRec ↾₀ n) n P := by
  rw [mem_otci_iff]
  constructor
  · rintro ⟨-, ⟨rfl, -⟩ | ⟨-, h⟩⟩
    · exact (hn rfl).elim
    · exact h
  · intro h
    refine ⟨?_, Or.inr ⟨hn, h⟩⟩
    rw [otciBound, mem_union_iff, dom_ciRec_restrict]
    refine Or.inr (mem_slotBound h.left fun p hp ↦ ?_)
    have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := h.left
    obtain ⟨u, l, rfl⟩ := hS.isOrderedPair hp
    have huc := (h.right.left !(u, l) hp).left
    have hlbl := (h.right.left !(u, l) hp).right
    rw [uc_orderedPair] at huc
    rw [lbl_orderedPair] at hlbl
    rw [pair_mem_sprod_iff]
    exact ⟨huc, hlbl⟩

omit [ModelsZF M] in
theorem isFunction_ciTriple (a b c : M) : IsFunction (ciTriple a b c) :=
  ((isFunction_empty.cc a).cc b).cc c

omit [ModelsZF M] in
theorem dom_ciTriple (a b c : M) : dom (ciTriple a b c) = ((3 : ℕ) : M) := by
  rw [ciTriple, dom_cc, dom_cc, dom_cc, dom_empty]
  rfl

theorem aoc_ciTriple (a b c : M) : aoc (ciTriple a b c) = a := by
  have h1 : IsFunction (cc (∅ : M) a) := isFunction_empty.cc a
  have h0 : ((0 : ℕ) : M) = dom (∅ : M) := by rw [dom_empty, natCast_zero]
  rw [aoc, ciTriple, cc_val_of_mem (h1.cc b) c (by simp [natCast_zero]),
    cc_val_of_mem h1 b (by simp [natCast_zero]), h0, cc_val_self isFunction_empty]

theorem sig_ciTriple (a b c : M) : sig (ciTriple a b c) = b := by
  have h1 : IsFunction (cc (∅ : M) a) := isFunction_empty.cc a
  have h0 : ((1 : ℕ) : M) = dom (cc (∅ : M) a) := by
    rw [dom_cc, dom_empty]
    rfl
  rw [sig, ciTriple, cc_val_of_mem (h1.cc b) c (by rw [h0]; simp), h0, cc_val_self h1]

omit [ModelsZF M] in
theorem ctp_ciTriple (a b c : M) : ctp (ciTriple a b c) = c := by
  have h2 : IsFunction (cc (cc (∅ : M) a) b) := (isFunction_empty.cc a).cc b
  have h0 : ((2 : ℕ) : M) = dom (cc (cc (∅ : M) a) b) := by
    rw [dom_cc, dom_cc, dom_empty]
    rfl
  rw [ctp, ciTriple, h0, cc_val_self h2]

theorem natCast_three_mem : ((3 : ℕ) : M) ∈ (ω : M) \ {∅} := by
  rw [mem_sdiff_iff, mem_singleton_iff, ← natCast_zero, natCast_inj]
  exact ⟨natCast_mem_omega 3, by omega⟩

omit [Extensional M] in
theorem ct_ne_dct : (ct : M) ≠ dct := by
  rw [ct, dct, Ne, natCast_inj]
  omega

/-- A function on `3` is determined by its components -/
theorem eq_ciTriple (hP : IsFunction P) (hdom : dom P = ((3 : ℕ) : M)) :
    P = ciTriple (aoc P) (sig P) (ctp P) := by
  refine hP.ext (isFunction_ciTriple _ _ _) (by rw [hdom, dom_ciTriple]) fun x hx ↦ ?_
  rw [hdom] at hx
  simp only [natCast_succ, natCast_zero, mem_succ_iff] at hx
  rcases hx with rfl | rfl | rfl | hx
  · exact (ctp_ciTriple _ _ _).symm
  · exact (sig_ciTriple _ _ _).symm
  · exact (aoc_ciTriple _ _ _).symm
  · simp at hx

/-- The node `(otci0Uc, p)` of the trees in `otci_0` -/
theorem otci0_node_conditions (p : M) :
    IsOrderedPair !(otci0Uc, p) ∧
      IsFunction (left !(otci0Uc, p)) ∧
      dom (left !(otci0Uc, p)) ∈ (ω : M) \ {∅} := by
  refine ⟨⟨_, _, rfl⟩, ?_, ?_⟩
  · rw [left_orderedPair]
    exact isFunction_ciTriple _ _ _
  · rw [left_orderedPair, otci0Uc, dom_ciTriple]
    exact natCast_three_mem

/-- The trees in `otci_n` are semi-linearly ordered tree structures -/
theorem isSLOT_of_mem_otci (hP : P ∈ otci n) : IsSLOT P := by
  by_cases hn : n = ∅
  · subst hn
    rw [mem_otci_empty_iff] at hP
    obtain ⟨p, -, rfl⟩ := hP
    obtain ⟨hb, hbf, hbd⟩ := otci0_node_conditions p
    exact SLOTreeStructure.IsSLOTreeStructure.irmrt SLOTreeStructure.isSLOTreeStructure_empty hb
      (by simp) hbf hbd
  rw [mem_otci_iff_of_ne_empty hn] at hP
  exact hP.left

/-- The trees in `otci_n` for even `n` have a root -/
theorem exists_mem_rtOf_of_mem_otci (hP : P ∈ otci n) (hn : IsEven n) : ∃ r, r ∈ rtOf P := by
  by_cases hn' : n = ∅
  · subst hn'
    rw [mem_otci_empty_iff] at hP
    obtain ⟨p, -, rfl⟩ := hP
    refine ⟨!(otci0Uc, p), ?_⟩
    change _ ∈ ((SLOTreeStructure.ofM emptySLOT).irmrt _).ts.rt
    rw [SLOTreeStructure.ts_irmrt,
      show (SLOTreeStructure.ofM (emptySLOT : M)).ts = ∅ from SLOTreeStructure.ts_empty,
      TreeStructure.isTreeStructure_empty.rt_irt (by simp)]
    exact mem_insert _ _
  rw [mem_otci_iff_of_ne_empty hn'] at hP
  obtain ⟨r, hr⟩ := (hP.right.right.left hn).left
  refine ⟨r, ?_⟩
  rw [hr]
  exact mem_singleton _

omit [RudClosed M] [Extensional M] in
open SLOTreeStructure in
/-- A child is a node -/
theorem mem_ndOf_of_mem_chdOf {X q d : M} (hX : IsSLOT X) (hd : d ∈ chdOf X q) :
    d ∈ ndOf X := by
  have hT := (show (ofM X).IsSLOTreeStructure from hX).isTreeStructure
  exact hT.chd_subset q (hT.mem_nd_of_mem_chd_val hd) hd

omit [RudClosed M] [Extensional M] in
open SLOTreeStructure in
/-- A root is a node -/
theorem mem_ndOf_of_mem_rtOf {X r : M} (hr : r ∈ rtOf X) : r ∈ ndOf X := by
  have hr' : r ∈ (ofM X).ts.rt := hr
  rw [TreeStructure.mem_rt_iff] at hr'
  exact hr'.left

omit [RudClosed M] [Extensional M] in
/-- `finotci_n = {P ∈ otci_n | P_nd is finite}` -/
theorem mem_finotci_iff : P ∈ finotci n ↔ P ∈ otci n ∧ MemStructure.Finite (ndOf P) := by
  rw [finotci, mem_comprehension_iff]

/-- `trvotci_n` -/
theorem mem_trvotci_iff : P ∈ trvotci n ↔ P ∈ finotci n ∧ TrvotciCond n P := by
  rw [trvotci, mem_comprehension_iff]

/-- `aotci_n`: functions `P` on `n + 1` with `P(i) ∈ otci_i` -/
theorem mem_aotci_iff : P ∈ aotci n ↔ ArrayCond (ciRec ↾₀ n) n (otci n) P := by
  rw [← aotciS_ciRec_restrict, aotciS, mem_comprehension_iff, otciS_ciRec_restrict,
    dom_ciRec_restrict, and_iff_right_iff_imp]
  rintro ⟨hf, hdom, hval, hn⟩
  rw [aotciBound, mem_powerset_iff, dom_ciRec_restrict, otciS_ciRec_restrict]
  intro z hz
  obtain ⟨i, v, rfl⟩ := hf.isRelation hz
  have hi : i ∈ succ n := by
    rw [← hdom, mem_dom_iff]
    exact ⟨v, hz⟩
  have hv : P ﹫ i = v := hf.val_eq_of_rel hz
  rw [pair_mem_sprod_iff, mem_union_iff, mem_levUnion_iff]
  refine ⟨hi, ?_⟩
  rcases mem_or_eq_of_mem_succ hi with hi | rfl
  · exact Or.inl ⟨i, hi, hv ▸ hval i hi⟩
  · exact Or.inr (hv ▸ hn)

/-- The entries of an array in `aotci_n` -/
theorem val_mem_otci_of_mem_aotci {i : M} (hP : P ∈ aotci n) (hi : i ∈ succ n) :
    P ﹫ i ∈ otci i := by
  obtain ⟨-, -, hval, hn⟩ := mem_aotci_iff.mp hP
  rcases mem_or_eq_of_mem_succ hi with hi | rfl
  · have h := hval i hi
    rwa [otciL_ciRec_restrict hi] at h
  · exact hn

/-- `finaotci_n`: the arrays in `aotci_n` with `P(i) ∈ finotci_i` -/
theorem mem_finaotci_iff : P ∈ finaotci n ↔ P ∈ aotci n ∧ ∀ i ∈ succ n, P ﹫ i ∈ finotci i := by
  rw [finaotci, mem_comprehension_iff]
  refine and_congr_right fun hP ↦ forall₂_congr fun i hi ↦ ?_
  rw [mem_finotci_iff]
  exact (and_iff_right (val_mem_otci_of_mem_aotci hP hi)).symm

/-- `trvaotci_n`: the arrays in `aotci_n` with `P(i) ∈ trvotci_i` -/
theorem mem_trvaotci_iff : P ∈ trvaotci n ↔ P ∈ aotci n ∧ ∀ i ∈ succ n, P ﹫ i ∈ trvotci i := by
  rw [← trvaotciS_ciRec_restrict, trvaotciS, mem_comprehension_iff, aotciS_ciRec_restrict,
    dom_ciRec_restrict]
  refine and_congr_right fun hP ↦ forall₂_congr fun i hi ↦ ?_
  rw [mem_trvotci_iff, mem_finotci_iff, and_iff_right (val_mem_otci_of_mem_aotci hP hi)]

theorem mem_uoci_iff : P ∈ uoci n ↔
    P ∈ uociBound (ciRec ↾₀ n) ∧ UociCond (ciRec ↾₀ n) n (finaotci n) P := by
  rw [← uociS_ciRec_restrict, uociS, mem_comprehension_iff, finaotciS_ciRec_restrict,
    dom_ciRec_restrict]

/-- A nonzero level `ℓ ≤ n` has a predecessor `⋃₀ ℓ < n` -/
theorem sUnion_mem_of_mem_succ {ℓ : M} (hn : n ∈ (ω : M)) (hℓ : ℓ ∈ succ n) (h0 : ∅ ∈ ℓ) :
    ⋃₀ ℓ ∈ n := by
  have hℓω : ℓ ∈ (ω : M) := ordinal_omega.transitive _ (succ_mem_omega hn) hℓ
  rcases mem_omega_cases hℓω with rfl | ⟨m, hm, rfl⟩
  · simp at h0
  have hmo : Ordinal m := ordinal_of_mem ordinal_omega hm
  rw [sUnion_succ hmo.transitive]
  rcases mem_or_eq_of_mem_succ hℓ with hℓ | hℓ
  · exact (ordinal_of_mem ordinal_omega hn).transitive _ hℓ (mem_succ_self m)
  · rw [← hℓ]
    exact mem_succ_self m

theorem mem_natCast_six_of_mem_dom {P i : M}
    (hdom : dom P = ((3 : ℕ) : M) ∨ dom P = ((5 : ℕ) : M) ∨ dom P = ((6 : ℕ) : M))
    (hi : i ∈ dom P) : i ∈ ((6 : ℕ) : M) := by
  have h6 : Ordinal ((6 : ℕ) : M) := (isNat_natCast 6).ordinal
  rcases hdom with h | h | h <;> rw [h] at hi
  · exact h6.transitive _ (natCast_mem_natCast_iff.mpr (by omega)) hi
  · exact h6.transitive _ (natCast_mem_natCast_iff.mpr (by omega)) hi
  · exact hi

/-- For `n ∈ ω`, `uoci_n` consists of the functions satisfying `UociCond` -/
theorem mem_uoci_iff_of_mem_omega (hn : n ∈ (ω : M)) :
    P ∈ uoci n ↔ UociCond (ciRec ↾₀ n) n (finaotci n) P := by
  rw [mem_uoci_iff, and_iff_right_iff_imp]
  intro h
  obtain ⟨hf, hdom, haoc, ⟨hsigf, -, hsigdom, hsig⟩, hctp, -, -, hucf⟩ := h
  -- the trees of the array `P_aoc`
  have harr (k : M) (hk : k ∈ succ n) :
      aoc P ﹫ k ∈ otci k ∧ aoc P ﹫ k ∈ levUnion 0 (ciRec ↾₀ n) n ∪ otci n := by
    have hA := (mem_finaotci_iff.mp haoc).left
    rw [mem_aotci_iff] at hA
    obtain ⟨-, -, hval, hlast⟩ := hA
    rcases mem_or_eq_of_mem_succ hk with hk | rfl
    swap
    · exact ⟨hlast, by rw [mem_union_iff]; exact Or.inr hlast⟩
    refine ⟨?_, ?_⟩
    · have h := hval k hk
      rwa [otciL_ciRec_restrict hk] at h
    · rw [mem_union_iff, mem_levUnion_iff]
      exact Or.inl ⟨k, hk, hval k hk⟩
  have hnodes (k : M) (hk : k ∈ succ n) (d : M) (hd : d ∈ ndOf (aoc P ﹫ k)) :
      d ∈ levNodes (ciRec ↾₀ n) := by
    rw [levNodes, mem_ndUnion_iff, dom_ciRec_restrict, otciS_ciRec_restrict]
    exact ⟨aoc P ﹫ k, (harr k hk).right, hd⟩
  have h3 : ((3 : ℕ) : M) ∈ dom P ∨ dom P = ((3 : ℕ) : M) := by
    rcases hdom with h | h | h
    · exact Or.inr h
    · rw [h, natCast_mem_natCast_iff]
      exact Or.inl (by omega)
    · rw [h, natCast_mem_natCast_iff]
      exact Or.inl (by omega)
  rw [uociBound, mem_powerset_iff]
  intro z hz
  obtain ⟨i, v, rfl⟩ := hf.isRelation hz
  have hi : i ∈ dom P := by
    rw [mem_dom_iff]
    exact ⟨v, hz⟩
  have hv : P ﹫ i = v := hf.val_eq_of_rel hz
  rw [pair_mem_sprod_iff]
  refine ⟨mem_natCast_six_of_mem_dom hdom hi, ?_⟩
  have hi6 := mem_natCast_six_of_mem_dom hdom hi
  simp only [natCast_succ, natCast_zero, mem_succ_iff] at hi6
  simp only [uociVals, mem_union_iff, dom_ciRec_restrict]
  rcases hi6 with rfl | rfl | rfl | rfl | rfl | rfl | hi6
  · -- `P_ucfex`
    have hi' : ((5 : ℕ) : M) ∈ dom P := hi
    have hdom6 : dom P = ((6 : ℕ) : M) := by
      rcases hdom with h | h | h
      · rw [h, natCast_mem_natCast_iff] at hi'
        omega
      · rw [h, natCast_mem_natCast_iff] at hi'
        omega
      · exact h
    have hU := hucf (by rw [hdom6, natCast_mem_natCast_iff]; omega)
    obtain ⟨-, hlvl, -, -, -, -, hex⟩ := hU
    obtain ⟨h0, hext⟩ := hex hdom6
    have hm := sUnion_mem_of_mem_succ hn hlvl h0
    right
    rw [mem_sUnion_iff]
    refine ⟨unorderedPair (uc (ucfdcn P)) v, ?_, by rw [mem_unorderedPair_iff]; exact Or.inr rfl⟩
    rw [mem_sUnion_iff]
    refine ⟨!(uc (ucfdcn P), v), ?_, by rw [mem_orderedPair_iff]; exact Or.inr rfl⟩
    rw [mem_levUnion_iff]
    exact ⟨⋃₀ ucflvl P, hm, hv ▸ hext⟩
  · -- `P_ucfdr`
    have hi' : ((4 : ℕ) : M) ∈ dom P := hi
    have hU := hucf (h3.resolve_right fun h ↦ by
      rw [h, natCast_mem_natCast_iff] at hi'
      omega)
    obtain ⟨-, -, -, -, hdr, -, -⟩ := hU
    left; left; right
    have hv' : ucfdr P = v := hv
    rw [← hv']
    rcases hdr with h | h <;> rw [h]
    · exact natCast_mem_natCast_iff.mpr (by omega)
    · exact natCast_mem_natCast_iff.mpr (by omega)
  · -- `P_ucflvldcn`
    have hi' : ((3 : ℕ) : M) ∈ dom P := hi
    have hU := hucf hi'
    obtain ⟨hpair, hlvl, hdcn, -⟩ := hU
    left; right
    have hv' : ucflvldcn P = v := hv
    obtain ⟨l, d, hld⟩ := hpair
    rw [← hv', hld, pair_mem_sprod_iff]
    have hl : ucflvl P = l := by simp [ucflvl, hld]
    have hd : ucfdcn P = d := by simp [ucfdcn, hld]
    rw [hl] at hlvl
    rw [hl, hd] at hdcn
    exact ⟨hlvl, hnodes l hlvl d hdcn⟩
  · -- `P_ctp`
    left; left; right
    have hv' : ctp P = v := hv
    rw [← hv']
    rcases hctp with h | h <;> rw [h]
    · exact natCast_mem_natCast_iff.mpr (by omega)
    · exact natCast_mem_natCast_iff.mpr (by omega)
  · -- `P_sig`
    left; left; left; right
    have hv' : sig P = v := hv
    rw [← hv', mem_powerset_iff]
    intro w hw
    obtain ⟨j, u, rfl⟩ := hsigf.isRelation hw
    have hj : j ∈ dom (sig P) := by
      rw [mem_dom_iff]
      exact ⟨u, hw⟩
    have hu : sig P ﹫ j = u := hsigf.val_eq_of_rel hw
    obtain ⟨hpair, hlvl, heven, hodd, -⟩ := hsig j hj
    rw [hu] at hpair
    obtain ⟨l, d, rfl⟩ := hpair
    have hl : siglvl P j = l := by simp [siglvl, hu]
    have hd : sigdcn P j = d := by simp [sigdcn, hu]
    rw [hl] at hlvl heven hodd
    rw [hd] at heven hodd
    have hX := isSLOT_of_mem_otci (harr l hlvl).left
    rw [pair_mem_sprod_iff, pair_mem_sprod_iff]
    refine ⟨ordinal_omega.transitive _ hsigdom hj, hlvl, hnodes l hlvl d ?_⟩
    by_cases hle : IsEven l
    · obtain ⟨r, hr⟩ := exists_mem_rtOf_of_mem_otci (harr l hlvl).left hle
      rcases heven hle r hr with h | ⟨j', -, -, h⟩
      · exact mem_ndOf_of_mem_chdOf hX h
      · exact mem_ndOf_of_mem_chdOf hX h
    · have hlω : l ∈ (ω : M) := ordinal_omega.transitive _ (succ_mem_omega hn) hlvl
      rcases hodd ((isOdd_iff_not_isEven hlω).mpr hle) with h | ⟨j', -, -, h⟩
      · exact mem_ndOf_of_mem_rtOf h
      · exact mem_ndOf_of_mem_chdOf hX h
  · -- `P_aoc`
    left; left; left; left
    have hv' : aoc P = v := hv
    rw [← hv', finaotciS_ciRec_restrict]
    exact haoc
  · simp at hi6

/-- `stduoci_n` -/
theorem mem_stduoci_iff : P ∈ stduoci n ↔ P ∈ uoci n ∧ StduociCond n P := by
  rw [← stduociS_ciRec_restrict, stduociS, mem_comprehension_iff, uociS_ciRec_restrict,
    dom_ciRec_restrict]

/-- `trvuoci_n` -/
theorem mem_trvuoci_iff : P ∈ trvuoci n ↔ P ∈ stduoci n ∧ TrvuociCond n (trvaotci n) P := by
  rw [← trvuociS_ciRec_restrict, trvuociS, mem_comprehension_iff, stduociS_ciRec_restrict,
    trvaotciS_ciRec_restrict, dom_ciRec_restrict]

/-- `ext_n`: the pairs `(P, Q)` of elements of `stduoci_n` satisfying `ExtCond` -/
theorem mem_ciExt_iff : z ∈ ciExt n ↔ ∃ P ∈ stduoci n, ∃ Q ∈ stduoci n,
    z = !(P, Q) ∧ ExtCond (ciRec ↾₀ n) n P Q := by
  rw [← extS_ciRec_restrict, extS, mem_comprehension_iff, stduociS_ciRec_restrict,
    dom_ciRec_restrict, mem_sprod_iff]
  constructor
  · rintro ⟨⟨P, hP, Q, hQ, rfl⟩, h⟩
    rw [left_orderedPair, right_orderedPair] at h
    exact ⟨P, hP, Q, hQ, rfl, h⟩
  · rintro ⟨P, hP, Q, hQ, rfl, h⟩
    rw [left_orderedPair, right_orderedPair]
    exact ⟨⟨P, hP, Q, hQ, rfl⟩, h⟩

/-- `ext_0 = ∅` -/
theorem ciExt_empty : ciExt (∅ : M) = ∅ := by
  rw [empty_iff]
  intro z hz
  rw [mem_ciExt_iff] at hz
  obtain ⟨P, hP, Q, -, -, hctp, -, -, hlfrt, hlfsbl, hdn⟩ := hz
  rw [mem_stduoci_iff, mem_uoci_iff_of_mem_omega empty_mem_omega] at hP
  obtain ⟨⟨-, hdom, -, -, -, -, hdom3, hucf⟩, -⟩ := hP
  have hne3 : dom P ≠ ((3 : ℕ) : M) := by
    intro h
    rcases hdom3.mp h with ⟨-, hodd⟩ | hct
    · exact not_isOdd_empty hodd
    · exact ct_ne_dct (hct ▸ hctp)
  have hmem (k : ℕ) (hk : k < 5) : (k : M) ∈ dom P := by
    rcases hdom with h | h | h
    · exact (hne3 h).elim
    · rw [h]
      exact natCast_mem_natCast_of_lt hk
    · rw [h]
      exact natCast_mem_natCast_of_lt (by omega)
  obtain ⟨-, hlvl, -, -, hdr, -, -⟩ := hucf (hmem 3 (by omega))
  have hnot (x : M) : x ∉ ucflvl P := by
    rcases mem_or_eq_of_mem_succ hlvl with h | h
    · simp at h
    rw [h]
    simp
  rcases hdr with hlf | hdn'
  · by_cases hrt : IsEven (ucflvl P) ∧ ucfdcn P ∈ rtOf (aoc P ﹫ ucflvl P)
    · exact hnot _ (hlfrt ⟨hmem 4 (by omega), hlf, hrt⟩).left
    · exact hnot _ (hlfsbl ⟨hmem 4 (by omega), hlf, hrt⟩).left
  · exact hnot _ (hdn hdn').left

omit [Extensional M] in
theorem natCast_one_ne_empty : ((1 : ℕ) : M) ≠ ∅ := by
  rw [← natCast_zero, Ne, natCast_inj]
  omega

omit [ModelsZF M] in
theorem sUnion_natCast_one : ⋃₀ ((1 : ℕ) : M) = ∅ := by
  rw [natCast_succ, natCast_zero, sUnion_succ isTransitive_empty]

omit [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [ModelsZF M] in
theorem empty_mem_natCast_one : (∅ : M) ∈ ((1 : ℕ) : M) :=
  natCast_mem_natCast_of_lt (j := 0) (by omega)

end Recursion

section SingleNode

/-! ### Trees with a single node -/

variable [ModelsZF M] {A B c j m n p q r P Q R T U : M}

omit [RudClosed M] [Extensional M] [ModelsZF M] in
theorem ndOf_irmrtOf_emptySLOT [ModelsKP M] (b : M) : ndOf (irmrtOf emptySLOT b) = {b} :=
  SLOTreeStructure.nd_empty_irmrt b

omit [RudClosed M] [Extensional M] [ModelsZF M] in
theorem rtOf_irmrtOf_emptySLOT [ModelsKP M] (b : M) : rtOf (irmrtOf emptySLOT b) = {b} :=
  SLOTreeStructure.rt_empty_irmrt b

omit [RudClosed M] [Extensional M] [ModelsZF M] in
theorem chdOf_irmrtOf_emptySLOT [ModelsKP M] (b p : M) : chdOf (irmrtOf emptySLOT b) p = ∅ :=
  SLOTreeStructure.chd_empty_irmrt_val b p

theorem isSLOT_trvTree (hr : IsFunction r) (hdom : dom r = ((3 : ℕ) : M)) : IsSLOT (trvTree r) :=
  SLOTreeStructure.IsSLOTreeStructure.irmrt SLOTreeStructure.isSLOTreeStructure_empty
    ⟨_, _, rfl⟩ (by simp [SLOTreeStructure.nd_empty]) (by rwa [left_orderedPair])
    (by rw [left_orderedPair, hdom]; exact natCast_three_mem)

omit [RudClosed M] [Extensional M] in
/-- A semi-linearly ordered tree structure with the single node `b` -/
theorem eq_irmrtOf_emptySLOT {b : M} (hT : IsSLOT T) (hnd : ndOf T = {b}) :
    T = irmrtOf emptySLOT b :=
  congrArg SLOTreeStructure.toM
    (SLOTreeStructure.IsSLOTreeStructure.eq_empty_irmrt (S := SLOTreeStructure.ofM T) hT hnd)

omit [RudClosed M] [Extensional M] in
theorem rtOf_trvTree (r : M) : rtOf (trvTree r) = {!(r, ∅)} := rtOf_irmrtOf_emptySLOT _

omit [RudClosed M] [Extensional M] in
theorem ndOf_trvTree (r : M) : ndOf (trvTree r) = {!(r, ∅)} := ndOf_irmrtOf_emptySLOT _

omit [RudClosed M] [Extensional M] in
theorem chdOf_trvTree (r p : M) : chdOf (trvTree r) p = ∅ := chdOf_irmrtOf_emptySLOT _ _

end SingleNode

end MemStructure

end FirstOrder.Language
