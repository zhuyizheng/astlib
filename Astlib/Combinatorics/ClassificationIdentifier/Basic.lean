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

For every `n ∈ ω`, `trvuoci_n` has a unique element (`existsUnique_mem_trvuoci`).
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

end Recursion

section Trivial

/-! ### Trivial `uoci`'s

For every `n ∈ ω`, `trvuoci_n` has a unique element (`existsUnique_mem_trvuoci`): the function
`{(0, A), (1, ∅), (2, c)}`, where `A(j)` is the tree with the single node `(U_{j-1}, ∅)` (with
`U_{-1} = otci0Uc`) and `c` is `ct` or `dct` as `n` is even or odd. -/

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

section Step

variable (hj : j ∈ (ω : M)) (ih : ∀ m ∈ j, TrvGood m)
include hj ih

omit [RudClosed M] [Extensional M] in
theorem IsTrvRoot.eq (hr : IsTrvRoot j r) {r' : M} (hr' : IsTrvRoot j r') : r = r' := by
  rcases hr with ⟨rfl, rfl⟩ | ⟨hj0, hr⟩
  · rcases hr' with ⟨-, rfl⟩ | ⟨hj0, -⟩
    · rfl
    · exact (hj0 rfl).elim
  rcases hr' with ⟨rfl, -⟩ | ⟨-, hr'⟩
  · exact (hj0 rfl).elim
  obtain ⟨-, hmj, -⟩ := sUnion_mem_of_ne_empty hj hj0
  obtain ⟨U, hU, -⟩ := ih _ hmj
  rw [(hU r).mp hr, (hU r').mp hr']

theorem IsTrvRoot.props (hr : IsTrvRoot j r) :
    IsFunction r ∧ dom r = ((3 : ℕ) : M) ∧ (IsEven j → ctp r = dct) ∧ (IsOdd j → ctp r = ct) := by
  rcases hr with ⟨rfl, rfl⟩ | ⟨hj0, hr⟩
  · refine ⟨isFunction_ciTriple _ _ _, dom_ciTriple _ _ _, fun _ ↦ ctp_ciTriple _ _ _,
      fun h ↦ (not_isOdd_empty h).elim⟩
  obtain ⟨hmω, hmj, hjm⟩ := sUnion_mem_of_ne_empty hj hj0
  obtain ⟨U, hU, hUf, hUdom, -, -, hUev, hUodd, -⟩ := ih _ hmj
  rw [(hU r).mp hr]
  refine ⟨hUf, hUdom, fun hje ↦ hUodd ?_, fun hjo ↦ hUev ?_⟩
  · rwa [hjm, isEven_succ_iff hmω] at hje
  · rwa [hjm, isOdd_succ_iff hmω] at hjo

end Step

theorem IsTrvArray.eq (hn : n ∈ (ω : M)) (ih : ∀ m ∈ n, TrvGood m) (hA : IsTrvArray n A)
    (hB : IsTrvArray n B) : A = B := by
  obtain ⟨hAf, hAdom, hAval⟩ := hA
  obtain ⟨hBf, hBdom, hBval⟩ := hB
  refine hAf.ext hBf (hAdom.trans hBdom.symm) fun j hj ↦ ?_
  rw [hAdom] at hj
  obtain ⟨r, hr, hAr⟩ := hAval j hj
  obtain ⟨r', hr', hBr⟩ := hBval j hj
  rw [hAr, hBr, hr.eq (mem_omega_of_mem_succ hn hj) (forall_mem_of_mem_succ hn ih hj) hr']

omit [RudClosed M] [Extensional M] in
theorem rtOf_trvTree (r : M) : rtOf (trvTree r) = {!(r, ∅)} := rtOf_irmrtOf_emptySLOT _

omit [RudClosed M] [Extensional M] in
theorem ndOf_trvTree (r : M) : ndOf (trvTree r) = {!(r, ∅)} := ndOf_irmrtOf_emptySLOT _

omit [RudClosed M] [Extensional M] in
theorem chdOf_trvTree (r p : M) : chdOf (trvTree r) p = ∅ := chdOf_irmrtOf_emptySLOT _ _

section Tree

variable (hj : j ∈ (ω : M)) (ih : ∀ m ∈ j, TrvGood m)
include hj ih

/-- The trees in `trvotci_j` whose roots have label `∅` are the trees `trvTree r` -/
theorem exists_eq_trvTree (hT : T ∈ trvotci j) (hlbl : ∀ p ∈ rtOf T, lbl p = ∅) :
    ∃ r, IsTrvRoot j r ∧ T = trvTree r := by
  rw [mem_trvotci_iff, mem_finotci_iff] at hT
  obtain ⟨⟨hTo, -⟩, hev, hodd⟩ := hT
  by_cases hj0 : j = ∅
  · subst hj0
    rw [mem_otci_empty_iff] at hTo
    obtain ⟨p, -, rfl⟩ := hTo
    have hp := hlbl !(otci0Uc, p) (by rw [rtOf_irmrtOf_emptySLOT]; exact mem_singleton _)
    rw [lbl_orderedPair] at hp
    subst hp
    exact ⟨otci0Uc, Or.inl ⟨rfl, rfl⟩, rfl⟩
  obtain ⟨hmω, hmj, hjm⟩ := sUnion_mem_of_ne_empty hj hj0
  obtain ⟨U, hU, hUf, hUdom, hUsig, hUarr, hUev, -, hUext, hUstd⟩ := ih _ hmj
  have ihm : ∀ m ∈ ⋃₀ j, TrvGood m := fun m hm ↦
    ih m ((ordinal_of_mem ordinal_omega hj).transitive _ hmj hm)
  rw [mem_otci_iff_of_ne_empty hj0] at hTo
  obtain ⟨hTslot, hnodes, hevc, hoddc, hchdc⟩ := hTo
  have hstd : stduociL (ciRec ↾₀ j) (⋃₀ j) = stduoci (⋃₀ j) := stduociL_ciRec_restrict hmj
  have htrvu : trvuociL (ciRec ↾₀ j) (⋃₀ j) = trvuoci (⋃₀ j) := trvuociL_ciRec_restrict hmj
  have htrva : trvaotciL (ciRec ↾₀ j) (⋃₀ j) = trvaotci (⋃₀ j) := trvaotciL_ciRec_restrict hmj
  have hext : extL (ciRec ↾₀ j) (⋃₀ j) = ciExt (⋃₀ j) := extL_ciRec_restrict hmj
  rw [hstd] at hnodes
  rw [htrvu] at hevc hoddc
  rw [htrva] at hoddc
  rw [hext] at hchdc
  -- the roots have `uc = U`
  have hrtU : ∀ p ∈ rtOf T, uc p = U := by
    intro p hp
    rcases isEven_or_isOdd hj with hje | hjo
    · exact (hU _).mp ((hevc hje).right p hp)
    have hmev : IsEven (⋃₀ j) := by rwa [hjm, isOdd_succ_iff hmω] at hjo
    have hpstd := (hnodes p (mem_ndOf_of_mem_rtOf hp)).left
    obtain ⟨hparr, hpsig⟩ := hUstd _ hpstd ((hoddc hjo).right p hp).left
    have hpct := hodd hjo p (mem_ndOf_of_mem_rtOf hp)
    have hpuoci := (mem_stduoci_iff.mp hpstd).left
    rw [mem_uoci_iff_of_mem_omega hmω] at hpuoci
    obtain ⟨hpf, -, -, -, -, -, hdom3, -⟩ := hpuoci
    rw [eq_ciTriple hpf (hdom3.mpr (.inr hpct)), eq_ciTriple hUf hUdom,
      hparr.eq hmω ihm hUarr, hpsig, hUsig, hpct, hUev hmev]
  -- no node has children
  have hchd : ∀ p ∈ ndOf T, chdOf T p = ∅ := by
    intro p hp
    by_contra hne
    obtain ⟨q, hq⟩ := (ne_empty_iff _).mp hne
    obtain ⟨q', hq', -⟩ := ((hchdc p hp).left (aoc (uc q))).mp ⟨q, hq, rfl⟩
    obtain ⟨P', -, Q', -, hPQ, hPQext⟩ := mem_ciExt_iff.mp hq'
    rw [orderedPair_eq_orderedPair_iff] at hPQ
    have hdct : ctp (uc p) = dct := by
      rw [hPQ.left]
      exact hPQext.left
    rcases isEven_or_isOdd hj with hje | hjo
    · rw [hrtU p ((hev hje p hp).mp hdct)] at hq'
      exact hUext q' hq'
    · exact ct_ne_dct ((hodd hjo p hp).symm.trans hdct)
  have hS : (SLOTreeStructure.ofM T).IsSLOTreeStructure := hTslot
  -- every node is a root
  have hndrt : ∀ p ∈ ndOf T, p ∈ rtOf T := by
    intro p hp
    by_contra hpr
    have hpd : p ∈ (SLOTreeStructure.ofM T).ts.nd \ (SLOTreeStructure.ofM T).ts.rt := by
      rw [mem_sdiff_iff]
      exact ⟨hp, hpr⟩
    have hmem := hS.isTreeStructure.mem_chd_prt_val hpd
    have h0 : chdOf T ((SLOTreeStructure.ofM T).ts.prt ﹫ p) = ∅ :=
      hchd _ (hS.isTreeStructure.prt_val_mem_nd hpd)
    rw [chdOf] at h0
    rw [SLOTreeStructure.chd] at h0
    rw [h0] at hmem
    simp at hmem
  -- the nodes are `(U, ∅)`
  have hpair : ∀ p ∈ ndOf T, p = !(U, ∅) := by
    intro p hp
    have hpr := hndrt p hp
    obtain ⟨u, l, rfl⟩ := hS.isOrderedPair hp
    have hu := hrtU _ hpr
    have hl := hlbl _ hpr
    rw [uc_orderedPair] at hu
    rw [lbl_orderedPair] at hl
    rw [hu, hl]
  obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ ∈ rtOf T := by
    rcases isEven_or_isOdd hj with hje | hjo
    · obtain ⟨r₀, hr₀⟩ := (hevc hje).left
      exact ⟨r₀, by rw [hr₀]; exact mem_singleton _⟩
    · obtain ⟨q, hq, -⟩ := (hoddc hjo).left
      exact ⟨q, hq⟩
  have hnd : ndOf T = {!(U, ∅)} := by
    ext p
    rw [mem_singleton_iff]
    refine ⟨hpair p, ?_⟩
    rintro rfl
    rw [← hpair r₀ (mem_ndOf_of_mem_rtOf hr₀)]
    exact mem_ndOf_of_mem_rtOf hr₀
  exact ⟨U, Or.inr ⟨hj0, (hU U).mpr rfl⟩, eq_irmrtOf_emptySLOT hTslot hnd⟩

/-- The trees `trvTree r` are in `trvotci_j` -/
theorem trvTree_mem_trvotci (hr : IsTrvRoot j r) : trvTree r ∈ trvotci j := by
  obtain ⟨hrf, hrdom, hrev, hrodd⟩ := hr.props hj ih
  have hslot : IsSLOT (trvTree r) := isSLOT_trvTree hrf hrdom
  have hV : (∅ : M) ∈ 𝕍 (ω : M) := by
    have h := vonNeumann_mem_vonNeumann (M := M) ⟨ordinal_empty, ordinal_omega, empty_mem_omega⟩
    rwa [vonNeumann_empty] at h
  rw [mem_trvotci_iff, mem_finotci_iff, ndOf_trvTree]
  refine ⟨⟨?_, finite_singleton _⟩, fun hje p hp ↦ ?_, fun hjo p hp ↦ ?_⟩
  rotate_left
  · rw [ndOf_trvTree, mem_singleton_iff] at hp
    rw [hp, rtOf_trvTree, uc_orderedPair, hrev hje]
    simp
  · rw [ndOf_trvTree, mem_singleton_iff] at hp
    rw [hp, uc_orderedPair, hrodd hjo]
  by_cases hj0 : j = ∅
  · subst hj0
    rcases hr with ⟨-, rfl⟩ | ⟨hj0, -⟩
    · rw [mem_otci_empty_iff]
      exact ⟨∅, hV, rfl⟩
    · exact (hj0 rfl).elim
  obtain ⟨hmω, hmj, hjm⟩ := sUnion_mem_of_ne_empty hj hj0
  have hrt : r ∈ trvuoci (⋃₀ j) := by
    rcases hr with ⟨h, -⟩ | ⟨-, h⟩
    · exact (hj0 h).elim
    · exact h
  obtain ⟨U, hU, -, -, -, -, -, -, hUext, -⟩ := ih _ hmj
  have hrU := (hU r).mp hrt
  rw [mem_trvuoci_iff] at hrt
  obtain ⟨hrstd, hraoc, -⟩ := hrt
  rw [mem_otci_iff_of_ne_empty hj0]
  have hstd : stduociL (ciRec ↾₀ j) (⋃₀ j) = stduoci (⋃₀ j) := stduociL_ciRec_restrict hmj
  have htrvu : trvuociL (ciRec ↾₀ j) (⋃₀ j) = trvuoci (⋃₀ j) := trvuociL_ciRec_restrict hmj
  have htrva : trvaotciL (ciRec ↾₀ j) (⋃₀ j) = trvaotci (⋃₀ j) := trvaotciL_ciRec_restrict hmj
  have hext : extL (ciRec ↾₀ j) (⋃₀ j) = ciExt (⋃₀ j) := extL_ciRec_restrict hmj
  unfold OtciCond
  rw [hstd, htrvu, htrva, hext, ndOf_trvTree, rtOf_trvTree]
  have hnoext : ∀ q, !(r, q) ∉ ciExt (⋃₀ j) := by
    rw [hrU]
    exact hUext
  have hrtrv : r ∈ trvuoci (⋃₀ j) := by
    rw [hU]
    exact hrU
  refine ⟨hslot, fun p hp ↦ ?_, fun _ ↦ ⟨⟨_, rfl⟩, fun p hp ↦ ?_⟩,
    fun hjo ↦ ⟨⟨_, mem_singleton _, ?_⟩, fun p hp ↦ ?_⟩, fun p hp ↦ ?_⟩
  · rw [mem_singleton_iff] at hp
    rw [hp, uc_orderedPair, lbl_orderedPair]
    exact ⟨hrstd, hV⟩
  · rw [mem_singleton_iff] at hp
    rwa [hp, uc_orderedPair]
  · rwa [uc_orderedPair]
  · rw [mem_singleton_iff] at hp
    have hrtlos : rtlosOf (trvTree r) = singletonFun (left !(r, ∅) ﹫ ∅) !({!(r, ∅)}, ∅) :=
      SLOTreeStructure.rtlos_empty_irmrt _
    have haoc : aoc r = left !(r, ∅) ﹫ ∅ := by
      rw [left_orderedPair, aoc, natCast_zero]
    rw [hp, uc_orderedPair, hrtlos, haoc, singletonFun_val, hrodd hjo]
    rw [← haoc]
    exact ⟨hraoc, iff_of_true (isLeastLos_singleton _) rfl⟩
  · rw [mem_singleton_iff] at hp
    rw [hp, uc_orderedPair, chdOf_trvTree]
    refine ⟨fun D ↦ ?_, fun q hq ↦ (hnoext q hq).elim⟩
    constructor
    · rintro ⟨q, hq, -⟩
      simp at hq
    · rintro ⟨q, hq, -⟩
      exact (hnoext q hq).elim

end Tree

/-- The step of the induction: `trvuoci_n` has a unique element if every level below does -/
theorem trvGood_of_forall (hn : n ∈ (ω : M)) (ih : ∀ m ∈ n, TrvGood m) : TrvGood n := by
  -- the array of trivial trees
  obtain ⟨A, hA⟩ : ∃ A, IsTrvArray n A := by
    by_cases hn0 : n = ∅
    · subst hn0
      refine ⟨cc ∅ (trvTree otci0Uc), isFunction_empty.cc _, by rw [dom_cc, dom_empty],
        fun j hj ↦ ⟨otci0Uc, ?_, ?_⟩⟩ <;> rw [mem_succ_iff] at hj <;>
        rcases hj with rfl | hj
      · exact .inl ⟨rfl, rfl⟩
      · simp at hj
      · have h := cc_val_self isFunction_empty (trvTree (otci0Uc : M))
        rwa [dom_empty] at h
      · simp at hj
    obtain ⟨-, hmn, hnm⟩ := sUnion_mem_of_ne_empty hn hn0
    obtain ⟨U, hU, -, -, -, ⟨hAf, hAdom, hAval⟩, -⟩ := ih _ hmn
    have hAdom' : dom (aoc U) = n := by rw [hAdom, ← hnm]
    refine ⟨cc (aoc U) (trvTree U), hAf.cc _, by rw [dom_cc, hAdom'], fun j hj ↦ ?_⟩
    rcases mem_or_eq_of_mem_succ hj with hj | hjn
    · obtain ⟨r, hr, hval⟩ := hAval j (by rwa [← hnm])
      exact ⟨r, hr, by rw [cc_val_of_mem hAf _ (by rwa [hAdom']), hval]⟩
    · refine ⟨U, .inr ⟨hjn ▸ hn0, ?_⟩, ?_⟩
      · rw [hjn, hU]
      · rw [hjn, ← hAdom', cc_val_self hAf]
  obtain ⟨hAf, hAdom, hAval⟩ := hA
  have hAtrv : ∀ j ∈ succ n, A ﹫ j ∈ trvotci j := by
    intro j hj
    obtain ⟨r, hr, hval⟩ := hAval j hj
    rw [hval]
    exact trvTree_mem_trvotci (mem_omega_of_mem_succ hn hj) (forall_mem_of_mem_succ hn ih hj) hr
  have hAotci : ∀ j ∈ succ n, A ﹫ j ∈ otci j := fun j hj ↦
    (mem_finotci_iff.mp (mem_trvotci_iff.mp (hAtrv j hj)).left).left
  have hAfin : ∀ j ∈ succ n, A ﹫ j ∈ finotci j := fun j hj ↦
    (mem_trvotci_iff.mp (hAtrv j hj)).left
  have hAaotci : A ∈ aotci n := by
    rw [mem_aotci_iff]
    refine ⟨hAf, hAdom, fun i hi ↦ ?_, hAotci n (mem_succ_self n)⟩
    rw [otciL_ciRec_restrict hi]
    exact hAotci i (mem_succ_of_mem hi)
  have hAfinaotci : A ∈ finaotci n := mem_finaotci_iff.mpr ⟨hAaotci, hAfin⟩
  have hAtrvaotci : A ∈ trvaotci n := mem_trvaotci_iff.mpr ⟨hAaotci, hAtrv⟩
  -- the arrays of the standard `uoci`'s with trivial arrays
  have hstd : ∀ R ∈ stduoci n, aoc R ∈ trvaotci n → IsTrvArray n (aoc R) ∧ sig R = ∅ := by
    intro R hR hRarr
    rw [mem_trvaotci_iff] at hRarr
    obtain ⟨hRaotci, hRtrv⟩ := hRarr
    obtain ⟨hRf, hRdom, -⟩ := mem_aotci_iff.mp hRaotci
    rw [mem_stduoci_iff] at hR
    obtain ⟨hRuoci, hRstd⟩ := hR
    have hRtree : ∀ j ∈ succ n, ∃ r, IsTrvRoot j r ∧ aoc R ﹫ j = trvTree r := by
      intro j hj
      have hjω := mem_omega_of_mem_succ hn hj
      refine exists_eq_trvTree hjω (forall_mem_of_mem_succ hn ih hj) (hRtrv j hj) fun p hp ↦ ?_
      have hpn := mem_ndOf_of_mem_rtOf hp
      obtain ⟨ha, -, hc⟩ := hRstd j hj p hpn
      rcases isEven_or_isOdd hjω with hje | hjo
      · exact ha ⟨hje, hp⟩
      · exact (hc ((mem_trvotci_iff.mp (hRtrv j hj)).right.right hjo p hpn)).left hp
    refine ⟨⟨hRf, hRdom, hRtree⟩, ?_⟩
    rw [mem_uoci_iff_of_mem_omega hn] at hRuoci
    obtain ⟨-, -, -, ⟨hsigf, -, -, hsig⟩, -⟩ := hRuoci
    refine hsigf.isRelation.eq_empty_of_dom_eq_empty ?_
    ext i
    refine ⟨fun hi ↦ ?_, by simp⟩
    exfalso
    obtain ⟨-, hlvl, heven, hodd, hctp⟩ := hsig i hi
    have hlω := mem_omega_of_mem_succ hn hlvl
    obtain ⟨r, hr, htree⟩ := hRtree _ hlvl
    obtain ⟨-, -, -, hrodd⟩ := hr.props hlω (forall_mem_of_mem_succ hn ih hlvl)
    rw [htree] at heven hodd
    rcases isEven_or_isOdd hlω with hle | hlo
    · rcases heven hle !(r, ∅) (by rw [rtOf_trvTree]; exact mem_singleton _) with h | ⟨j, -, -, h⟩
      all_goals
        rw [chdOf_trvTree] at h
        simp at h
    · rcases hodd hlo with h | ⟨j, -, -, h⟩
      · rw [rtOf_trvTree, mem_singleton_iff] at h
        rw [h, uc_orderedPair, hrodd hlo] at hctp
        exact ct_ne_dct hctp
      · rw [chdOf_trvTree] at h
        simp at h
  -- the trivial `uoci`
  obtain ⟨c, hcev, hcodd⟩ : ∃ c : M, (IsEven n → c = ct) ∧ (IsOdd n → c = dct) := by
    rcases isEven_or_isOdd hn with h | h
    · exact ⟨ct, fun _ ↦ rfl, fun h' ↦ (h.not_isOdd h').elim⟩
    · exact ⟨dct, fun h' ↦ (h.not_isEven h').elim, fun _ ↦ rfl⟩
  have hUuoci : ciTriple A ∅ c ∈ uoci n := by
    rw [mem_uoci_iff_of_mem_omega hn]
    unfold UociCond
    refine ⟨isFunction_ciTriple _ _ _, .inl (dom_ciTriple _ _ _), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [aoc_ciTriple]
      exact hAfinaotci
    · rw [sig_ciTriple, dom_empty]
      exact ⟨isFunction_empty, by simp, empty_mem_omega, by simp⟩
    · rw [ctp_ciTriple]
      rcases isEven_or_isOdd hn with h | h
      · exact .inl (hcev h)
      · exact .inr (hcodd h)
    · rw [ctp_ciTriple]
      exact fun h ↦ hcodd h.right
    · rw [sig_ciTriple, ctp_ciTriple]
      refine iff_of_true (dom_ciTriple _ _ _) ?_
      rcases isEven_or_isOdd hn with h | h
      · exact .inr (hcev h)
      · exact .inl ⟨rfl, h⟩
    · rw [dom_ciTriple, natCast_mem_natCast_iff]
      omega
  have hUstd : StduociCond n (ciTriple A ∅ c) := by
    intro i hi p hp
    obtain ⟨r, hr, htree⟩ := hAval i hi
    obtain ⟨-, -, -, hrodd⟩ := hr.props (mem_omega_of_mem_succ hn hi)
      (forall_mem_of_mem_succ hn ih hi)
    rw [aoc_ciTriple, htree, ndOf_trvTree, mem_singleton_iff] at hp
    rw [aoc_ciTriple, htree, rtOf_trvTree, hp, uc_orderedPair, lbl_orderedPair]
    refine ⟨fun _ ↦ rfl, fun ⟨hdct, hne⟩ ↦ ?_,
      fun _ ↦ ⟨fun _ ↦ rfl, fun h ↦ (h (mem_singleton _)).elim⟩⟩
    exfalso
    rcases isEven_or_isOdd (mem_omega_of_mem_succ hn hi) with h | h
    · exact hne ⟨h, mem_singleton _⟩
    · exact ct_ne_dct ((hrodd h).symm.trans hdct)
  have hUtrv : ciTriple A ∅ c ∈ trvuoci n := by
    rw [mem_trvuoci_iff, mem_stduoci_iff]
    refine ⟨⟨hUuoci, hUstd⟩, by rwa [aoc_ciTriple], fun h ↦ ?_, fun h ↦ ?_⟩ <;> rw [ctp_ciTriple]
    · exact hcev h
    · exact hcodd h
  refine ⟨ciTriple A ∅ c, fun P ↦ ⟨fun hP ↦ ?_, ?_⟩, isFunction_ciTriple _ _ _, dom_ciTriple _ _ _,
    sig_ciTriple _ _ _, by rw [aoc_ciTriple]; exact ⟨hAf, hAdom, hAval⟩,
    fun h ↦ by rw [ctp_ciTriple]; exact hcev h, fun h ↦ by rw [ctp_ciTriple]; exact hcodd h,
    fun Q hQ ↦ ?_, hstd⟩
  rotate_left
  · rintro rfl
    exact hUtrv
  · -- no extension of the trivial `uoci`
    obtain ⟨P', -, Q', hQ', hPQ, hext⟩ := mem_ciExt_iff.mp hQ
    rw [orderedPair_eq_orderedPair_iff] at hPQ
    obtain ⟨rfl, rfl⟩ := hPQ
    obtain ⟨hdct, -, hrt, -⟩ := hext
    rw [ctp_ciTriple] at hdct
    have hno : IsOdd n := by
      rcases isEven_or_isOdd hn with h | h
      · exact (ct_ne_dct ((hcev h).symm.trans hdct)).elim
      · exact h
    obtain ⟨hres, R, -, B, -, haocQ, hsigQ⟩ := hrt ⟨sig_ciTriple _ _ _, hno⟩
    have hn0 : n ≠ ∅ := fun h ↦ not_isOdd_empty (h ▸ hno)
    have h0n : ∅ ∈ n := empty_mem_of_ordinal_of_ne_empty (ordinal_of_mem ordinal_omega hn) hn0
    have hQuoci := (mem_stduoci_iff.mp hQ').left
    rw [mem_uoci_iff_of_mem_omega hn] at hQuoci
    obtain ⟨hQf, hQdom, -, ⟨-, -, -, hsig⟩, -⟩ := hQuoci
    have h0Q : (∅ : M) ∈ dom Q := by
      rcases hQdom with h | h | h <;> rw [h, ← natCast_zero, natCast_mem_natCast_iff] <;> omega
    have haoc : aoc Q = A := by
      have h : (ciTriple A ∅ c ↾ n) ﹫ ∅ = (Q ↾ n) ﹫ ∅ := by rw [hres]
      have h0U : (∅ : M) ∈ dom (ciTriple A ∅ c) := by
        rw [dom_ciTriple, ← natCast_zero, natCast_mem_natCast_iff]
        omega
      rw [val_restrict _ (isFunction_ciTriple _ _ _) h0n h0U, val_restrict _ hQf h0n h0Q] at h
      rw [aoc, natCast_zero, ← h]
      exact aoc_ciTriple _ _ _
    rw [haoc, aoc_ciTriple] at haocQ
    obtain ⟨r, hr, htree⟩ := hAval n (mem_succ_self n)
    obtain ⟨-, -, -, hrodd⟩ := hr.props hn ih
    have hmem : !(R, ∅) ∈ ndOf (A ﹫ n) := by
      rw [haocQ]
      refine SLOTreeStructure.nd_subset_nd_asnchd _ _ _ ?_
      change _ ∈ ((SLOTreeStructure.ofM (A ﹫ n)).irmrt !(R, ∅)).nd
      rw [SLOTreeStructure.nd_irmrt]
      exact mem_insert _ _
    rw [htree, ndOf_trvTree, mem_singleton_iff, orderedPair_eq_orderedPair_iff] at hmem
    have h0sig : (∅ : M) ∈ dom (sig Q) := by
      rw [hsigQ, dom_cc, dom_empty]
      exact mem_succ_self _
    have hctp := (hsig ∅ h0sig).right.right.right.right
    have hdcn : sigdcn Q ∅ = !(R, ∅) := by
      have h := cc_val_self isFunction_empty !(n, !(R, ∅))
      rw [dom_empty] at h
      rw [sigdcn, hsigQ, h, dcn_orderedPair]
    rw [hdcn, uc_orderedPair, hmem.left, hrodd hno] at hctp
    exact ct_ne_dct hctp
  -- uniqueness
  rw [mem_trvuoci_iff] at hP
  obtain ⟨hPstd, hParr, hPev, hPodd⟩ := hP
  obtain ⟨hParr', hPsig⟩ := hstd P hPstd hParr
  have hPuoci := (mem_stduoci_iff.mp hPstd).left
  rw [mem_uoci_iff_of_mem_omega hn] at hPuoci
  obtain ⟨hPf, -, -, -, -, -, hdom3, -⟩ := hPuoci
  have hPdom : dom P = ((3 : ℕ) : M) := by
    refine hdom3.mpr ?_
    rcases isEven_or_isOdd hn with h | h
    · exact .inr (hPev h)
    · exact .inl ⟨hPsig, h⟩
  have hPctp : ctp P = c := by
    rcases isEven_or_isOdd hn with h | h
    · rw [hPev h, hcev h]
    · rw [hPodd h, hcodd h]
  rw [eq_ciTriple hPf hPdom, hParr'.eq hn ih ⟨hAf, hAdom, hAval⟩, hPsig, hPctp]

theorem trvGood (hn : n ∈ (ω : M)) : TrvGood n :=
  induction_of_modelsZF (A := fun x ↦ x ∈ (ω : M) → TrvGood x)
    (fun _ ih hx ↦ trvGood_of_forall hx fun m hm ↦ ih m hm (ordinal_omega.transitive _ hx hm))
    n hn

/-- For every `n ∈ ω`, there is a unique trivial level-`n` `uoci` -/
theorem existsUnique_mem_trvuoci (hn : n ∈ (ω : M)) : ∃! P, P ∈ trvuoci n := by
  obtain ⟨U, hU, -⟩ := trvGood hn
  exact ⟨U, (hU U).mpr rfl, fun P hP ↦ (hU P).mp hP⟩

/-- `trvuoci_n = {trvU n}` -/
theorem trvuoci_eq_singleton (hn : n ∈ (ω : M)) : trvuoci n = {trvU n} := by
  obtain ⟨U, hU, -⟩ := trvGood hn
  have htrv : trvuoci n = {U} := by
    ext P
    rw [mem_singleton_iff, hU]
  rw [trvU, htrv, sUnion_singleton]

theorem mem_trvuoci_iff_eq_trvU (hn : n ∈ (ω : M)) : P ∈ trvuoci n ↔ P = trvU n := by
  rw [trvuoci_eq_singleton hn, mem_singleton_iff]

theorem trvU_mem_trvuoci (hn : n ∈ (ω : M)) : trvU n ∈ trvuoci n :=
  (mem_trvuoci_iff_eq_trvU hn).mpr rfl

theorem isTrvUoci_trvU (hn : n ∈ (ω : M)) : IsTrvUoci n (trvU n) := by
  obtain ⟨U, hU, hUtrv⟩ := trvGood hn
  rwa [← (mem_trvuoci_iff_eq_trvU hn).mp ((hU U).mpr rfl)]

theorem isFunction_trvU (hn : n ∈ (ω : M)) : IsFunction (trvU n) :=
  (isTrvUoci_trvU hn).left

theorem dom_trvU (hn : n ∈ (ω : M)) : dom (trvU n) = ((3 : ℕ) : M) :=
  (isTrvUoci_trvU hn).right.left

theorem sig_trvU (hn : n ∈ (ω : M)) : sig (trvU n) = ∅ :=
  (isTrvUoci_trvU hn).right.right.left

theorem isTrvArray_aoc_trvU (hn : n ∈ (ω : M)) : IsTrvArray n (aoc (trvU n)) :=
  (isTrvUoci_trvU hn).right.right.right.left

theorem ctp_trvU_of_isEven (hn : n ∈ (ω : M)) (he : IsEven n) : ctp (trvU n) = ct :=
  (isTrvUoci_trvU hn).right.right.right.right.left he

theorem ctp_trvU_of_isOdd (hn : n ∈ (ω : M)) (ho : IsOdd n) : ctp (trvU n) = dct :=
  (isTrvUoci_trvU hn).right.right.right.right.right.left ho

/-- `trvU n = {(0, A), (1, ∅), (2, c)}` -/
theorem trvU_eq_ciTriple (hn : n ∈ (ω : M)) :
    trvU n = ciTriple (aoc (trvU n)) ∅ (ctp (trvU n)) := by
  rw [← sig_trvU hn]
  exact eq_ciTriple (isFunction_trvU hn) (dom_trvU hn)

end Trivial

end MemStructure

end FirstOrder.Language
