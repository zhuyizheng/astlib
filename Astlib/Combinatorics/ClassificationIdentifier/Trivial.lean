/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.Basic
/-!
# Trivial `uoci`'s

For `n ∈ ω`:

* all elements of `trvuoci_n` have the same array (`aoc_eq_of_mem_trvuoci`): its odd-level trees are
  empty, its level-`0` tree is the single node `(otci0Uc, ∅)`, and for even `i > 0` its level-`i`
  tree is the root `(U, ∅)` with `U ∈ trvuoci_{i-1}` and the continuous children `(q, (U, ∅))`
  for the extensions `(U, q) ∈ ext_{i-1}`;
* the elements of `trvuoci_n` have empty signatures (`sig_eq_empty_of_mem_trvuoci`), so for odd `n`
  they are the triples `{(0, A), (1, ∅), (2, dct)}`, and `trvuoci_n` has at most one element
  (`eq_of_mem_trvuoci_of_isOdd`);
* the roots of a tree in `otci_n` for `n > 0` have the same key, so they form a single linearly
  ordered set (`losSet_ndlos_of_mem_rtOf`).

The array and the uniqueness at odd levels are proved together by induction on `n`, since the
level-`i` tree of the array is determined by the trivial `uoci_{i-1}` of the odd level `i - 1`.
Trivial `uoci`'s of even levels `n > 0` are not unique: they differ in their unique continuity
failure.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M] {b k n p r R T T' U U' : M}

section Trees

/-! ### The trees of the trivial arrays -/

/-- A semi-linearly ordered tree structure without nodes is empty -/
theorem eq_emptySLOT_of_ndOf_eq_empty (hT : IsSLOT T) (hnd : ndOf T = ∅) : T = emptySLOT := by
  have hS : (SLOTreeStructure.ofM T).IsSLOTreeStructure := hT
  have hts := hS.isTreeStructure.eq_empty_of_nd_eq_empty hnd
  exact congrArg SLOTreeStructure.toM (hS.eq_empty_of_ts_eq_empty hts)

/-- The labels of the trees of a standard `uoci` at the roots of even levels and at the
continuous non-root nodes -/
def StdLbls (T : M) : Prop :=
  ∀ p ∈ ndOf T, (p ∈ rtOf T → lbl p = ∅) ∧ ((ctp (uc p) = ct ∧ p ∉ rtOf T) → lbl p = prtOf T p)

omit [ModelsZF M] in
/-- The trees of the array of a standard `uoci` of even levels have the standard labels -/
theorem stdLbls_of_stduociCond {i : M} (h : StduociCond n U) (hi : i ∈ succ n) (he : IsEven i) :
    StdLbls (aoc U ﹫ i) := fun p hp ↦
  ⟨fun hr ↦ (h i hi p hp).left ⟨he, hr⟩,
    fun hc ↦ ((h i hi p hp).right.right hc.left).right hc.right⟩

/-- A tree in `trvotci_0` with root label `∅` is the single node `(otci0Uc, ∅)` -/
theorem eq_trvTree_of_mem_otci_empty (hT : T ∈ otci (∅ : M)) (hlbl : StdLbls T) :
    T = trvTree otci0Uc := by
  rw [mem_otci_empty_iff] at hT
  obtain ⟨l, -, rfl⟩ := hT
  have hrt : !(otci0Uc, l) ∈ rtOf (irmrtOf emptySLOT !(otci0Uc, l)) := by
    rw [rtOf_irmrtOf_emptySLOT]
    exact mem_singleton _
  have hl := (hlbl _ (mem_ndOf_of_mem_rtOf hrt)).left hrt
  rw [lbl_orderedPair] at hl
  rw [hl]
  rfl

/-- The children of a node `(R, ∅)` whose children are continuous with label `(R, ∅)`: one child
`(q, (R, ∅))` for each extension `(R, q) ∈ ext_{k-1}` -/
theorem mem_chdOf_iff_of_ext (hk : k ∈ (ω : M)) (hk0 : k ≠ ∅) (hT : T ∈ otci k)
    (hb : !(R, ∅) ∈ ndOf T) (hct : ∀ c ∈ chdOf T !(R, ∅), ctp (uc c) = ct)
    (hlbl : ∀ c ∈ chdOf T !(R, ∅), lbl c = !(R, ∅)) (x : M) :
    x ∈ chdOf T !(R, ∅) ↔ ∃ q, x = !(q, !(R, ∅)) ∧ !(R, q) ∈ ciExt (⋃₀ k) := by
  obtain ⟨hmω, hmk, -⟩ := sUnion_mem_of_ne_empty hk hk0
  have hX := isSLOT_of_mem_otci hT
  have hS : (SLOTreeStructure.ofM T).IsSLOTreeStructure := hX
  rw [mem_otci_iff_of_ne_empty hk0] at hT
  obtain ⟨-, hnodes, -, -, hchd⟩ := hT
  have hD := (hchd _ hb).left
  rw [extL_ciRec_restrict hmk, uc_orderedPair] at hD
  -- a child `c` is `(q, (R, ∅))` for an extension `q` with the key of `c`
  have hchild {c : M} (hc : c ∈ chdOf T !(R, ∅)) {q : M} (hq : !(R, q) ∈ ciExt (⋃₀ k))
      (hcq : aoc q = aoc (uc c)) : c = !(q, !(R, ∅)) := by
    have hcnd := mem_ndOf_of_mem_chdOf hX hc
    have hcs := (hnodes c hcnd).left
    rw [stduociL_ciRec_restrict hmk] at hcs
    obtain ⟨-, hqs, -, hqct⟩ := mem_ciExt_props hq
    have hucq := eq_of_aoc_eq_of_ctp_eq_ct hmω hcs hqs (hct c hc) hqct hcq.symm
    have hl := hlbl c hc
    obtain ⟨u, l, rfl⟩ := hS.isOrderedPair hcnd
    rw [uc_orderedPair] at hucq
    rw [lbl_orderedPair] at hl
    rw [hucq, hl]
  constructor
  · intro hx
    obtain ⟨q, hq, hqD⟩ := (hD (aoc (uc x))).mp ⟨x, hx, rfl⟩
    exact ⟨q, hchild hx hq hqD, hq⟩
  · rintro ⟨q, rfl, hq⟩
    obtain ⟨c, hc, hcD⟩ := (hD (aoc q)).mpr ⟨q, hq, rfl⟩
    rwa [← hchild hc hq hcD.symm]

/-- A tree in `trvotci_k` for even `k > 0` with the standard labels is the root `(R, ∅)` together
with its children, where `R` is the identifier of the root -/
theorem eq_asnchd_of_mem_trvotci (hk : k ∈ (ω : M)) (hk0 : k ≠ ∅) (he : IsEven k)
    (hT : T ∈ trvotci k) (hlbl : StdLbls T) (hr : r ∈ rtOf T) :
    T = asnchdOf (trvTree (uc r)) !(uc r, ∅) (chdOf T !(uc r, ∅)) ∧
      ∀ x, x ∈ chdOf T !(uc r, ∅) ↔
        ∃ q, x = !(q, !(uc r, ∅)) ∧ !(uc r, q) ∈ ciExt (⋃₀ k) := by
  rw [mem_trvotci_iff, mem_finotci_iff] at hT
  obtain ⟨⟨hTo, -⟩, hev, -⟩ := hT
  obtain ⟨hmω, -, -⟩ := sUnion_mem_of_ne_empty hk hk0
  have hTslot := isSLOT_of_mem_otci hTo
  have hS : (SLOTreeStructure.ofM T).IsSLOTreeStructure := hTslot
  have hTo' := hTo
  rw [mem_otci_iff_of_ne_empty hk0] at hTo'
  obtain ⟨-, hnodes, -, hevc, -⟩ := hTo'
  rw [stduociL_ciRec_restrict (sUnion_mem_of_ne_empty hk hk0).right.left] at hnodes
  -- the root is `(uc r, ∅)`
  obtain ⟨r₀, hr₀⟩ := hevc he
  have hrr : r = r₀ := by
    rw [hr₀, mem_singleton_iff] at hr
    exact hr
  subst hrr
  have hrb : r = !(uc r, ∅) := by
    have hl := (hlbl r (mem_ndOf_of_mem_rtOf hr)).left hr
    obtain ⟨u, l, rfl⟩ := hS.isOrderedPair (mem_ndOf_of_mem_rtOf hr)
    rw [lbl_orderedPair] at hl
    rw [uc_orderedPair, hl]
  have hb := mem_ndOf_of_mem_rtOf hr
  have hrt : rtOf T = {!(uc r, ∅)} := by rw [hr₀, ← hrb]
  rw [hrb] at hb
  -- the non-root nodes are continuous children of the root
  have hnonrt : ∀ p ∈ ndOf T, p ∉ rtOf T → ctp (uc p) = ct := by
    intro p hp hpr
    rcases ctp_eq_ct_or_dct hmω (mem_stduoci_iff.mp (hnodes p hp).left).left with h | h
    · exact h
    · exact (hpr ((hev he p hp).mp h)).elim
  have hndrt : ∀ p ∈ ndOf T, p ∉ rtOf T → p ∈ chdOf T !(uc r, ∅) := by
    intro p hp hpr
    have hpd : p ∈ (SLOTreeStructure.ofM T).ts.nd \ (SLOTreeStructure.ofM T).ts.rt := by
      rw [mem_sdiff_iff]
      exact ⟨hp, hpr⟩
    have hq := hS.isTreeStructure.prt_val_mem_nd hpd
    have hmem := hS.isTreeStructure.mem_chd_prt_val hpd
    by_cases hqr : (SLOTreeStructure.ofM T).ts.prt ﹫ p ∈ rtOf T
    · rw [hrt, mem_singleton_iff] at hqr
      rw [hqr] at hmem
      exact hmem
    · have h0 := chdOf_eq_empty_of_ctp_eq_ct hk hTo hq (hnonrt _ hq hqr)
      rw [chdOf, SLOTreeStructure.chd] at h0
      rw [h0] at hmem
      simp at hmem
  have hchdct : ∀ c ∈ chdOf T !(uc r, ∅), ctp (uc c) = ct := fun c hc ↦
    hnonrt c (mem_ndOf_of_mem_chdOf hTslot hc) (not_mem_rtOf_of_mem_chdOf hTslot hc)
  have hchdlbl : ∀ c ∈ chdOf T !(uc r, ∅), lbl c = !(uc r, ∅) := by
    intro c hc
    have hcn := mem_ndOf_of_mem_chdOf hTslot hc
    rw [(hlbl c hcn).right ⟨hchdct c hc, not_mem_rtOf_of_mem_chdOf hTslot hc⟩,
      prtOf_eq_of_mem_chdOf hTslot hc]
  have hmem := mem_chdOf_iff_of_ext hk hk0 hTo hb hchdct hchdlbl
  refine ⟨?_, hmem⟩
  have hnd : ndOf T = insert !(uc r, ∅) (chdOf T !(uc r, ∅)) := by
    ext p
    rw [mem_insert_iff]
    constructor
    · intro hp
      by_cases hpr : p ∈ rtOf T
      · rw [hrt, mem_singleton_iff] at hpr
        exact .inl hpr
      · exact .inr (hndrt p hp hpr)
    · rintro (rfl | hp)
      · exact hb
      · exact mem_ndOf_of_mem_chdOf hTslot hp
  -- the children have distinct keys
  have hinj : ∀ x ∈ chdOf T !(uc r, ∅), ∀ y ∈ chdOf T !(uc r, ∅), x ≠ y →
      left x ﹫ ∅ ≠ left y ﹫ ∅ := by
    intro x hx y hy hxy h
    obtain ⟨q, rfl, hq⟩ := (hmem x).mp hx
    obtain ⟨q', rfl, hq'⟩ := (hmem y).mp hy
    rw [left_orderedPair, left_orderedPair] at h
    obtain ⟨-, hqs, -, hqct⟩ := mem_ciExt_props hq
    obtain ⟨-, hqs', -, hqct'⟩ := mem_ciExt_props hq'
    exact hxy (by rw [eq_of_aoc_eq_of_ctp_eq_ct hmω hqs hqs' hqct hqct' h])
  have heq := hS.eq_asnchd_empty_irmrt (b := !(uc r, ∅)) hrt hnd rfl hinj
  exact congrArg SLOTreeStructure.toM heq

/-- Two trees in `trvotci_k` for even `k > 0` with the standard labels and the same root
identifier are equal -/
theorem eq_of_mem_trvotci (hk : k ∈ (ω : M)) (hk0 : k ≠ ∅) (he : IsEven k)
    (hT : T ∈ trvotci k) (hT' : T' ∈ trvotci k) (hlbl : StdLbls T) (hlbl' : StdLbls T')
    {r' : M} (hr : r ∈ rtOf T) (hr' : r' ∈ rtOf T') (huc : uc r = uc r') : T = T' := by
  obtain ⟨hTeq, hTchd⟩ := eq_asnchd_of_mem_trvotci hk hk0 he hT hlbl hr
  obtain ⟨hT'eq, hT'chd⟩ := eq_asnchd_of_mem_trvotci hk hk0 he hT' hlbl' hr'
  have hC : chdOf T !(uc r, ∅) = chdOf T' !(uc r', ∅) := by
    ext x
    rw [hTchd, hT'chd, huc]
  rw [hTeq, hT'eq, hC, huc]

end Trees

section Signature

/-- The elements of `trvuoci_n` have empty signatures: the only discontinuous nodes of a trivial
array are the roots of the even levels -/
theorem sig_eq_empty_of_mem_trvuoci (hn : n ∈ (ω : M)) (hU : U ∈ trvuoci n) : sig U = ∅ := by
  obtain ⟨hUstd, hUarr, -⟩ := mem_trvuoci_iff.mp hU
  obtain ⟨hA, hAt⟩ := mem_trvaotci_iff.mp hUarr
  have hUu := (mem_stduoci_iff.mp hUstd).left
  rw [mem_uoci_iff_of_mem_omega hn] at hUu
  obtain ⟨-, -, -, ⟨hsigf, -, -, hsig⟩, -⟩ := hUu
  refine hsigf.isRelation.eq_empty_of_dom_eq_empty ?_
  ext i
  refine ⟨fun hi ↦ ?_, by simp⟩
  exfalso
  have hnot := not_isEven_and_mem_rtOf_of_sigCond hA (hsig i hi)
  have hnd := mem_ndOf_of_sigCond hn hA (hsig i hi)
  obtain ⟨-, hlvl, -, -, hctp⟩ := hsig i hi
  obtain ⟨-, hev, hodd⟩ := mem_trvotci_iff.mp (hAt _ hlvl)
  rcases isEven_or_isOdd (mem_omega_of_mem_succ hn hlvl) with he | ho
  · exact hnot ⟨he, (hev he _ hnd).mp hctp⟩
  · rw [hodd ho] at hnd
    simp at hnd

end Signature

section Induction

/-! ### Uniqueness of the trivial arrays and of the trivial `uoci`'s of odd levels -/

/-- All elements of `trvuoci_n` have the same array, and for odd `n`, `trvuoci_n` has at most one
element -/
def TrvUniq (n : M) : Prop :=
  (∀ U ∈ trvuoci n, ∀ U' ∈ trvuoci n, aoc U = aoc U') ∧
    (IsOdd n → ∀ U ∈ trvuoci n, ∀ U' ∈ trvuoci n, U = U')

instance : Multiclass.Definable (fun xs : Fin 1 → M ↦ TrvUniq (xs 0)) Set.univ := by
  have h : (fun xs : Fin 1 → M ↦ TrvUniq (xs 0)) = fun xs : Fin 1 → M ↦
      (∀ U ∈ trvuoci (xs 0), ∀ U' ∈ trvuoci (xs 0), ∃ A, A = aoc U ∧ A = aoc U') ∧
        (IsOdd (xs 0) → ∀ U ∈ trvuoci (xs 0), ∀ U' ∈ trvuoci (xs 0), U = U') := by
    funext xs
    simp [TrvUniq]
  rw [h]
  infer_instance

/-- The step of the induction -/
theorem trvUniq_of_forall (hn : n ∈ (ω : M)) (ih : ∀ m ∈ n, TrvUniq m) : TrvUniq n := by
  -- the arrays
  have harr : ∀ U ∈ trvuoci n, ∀ U' ∈ trvuoci n, aoc U = aoc U' := by
    intro U hU U' hU'
    obtain ⟨hUstd, hUarr, -⟩ := mem_trvuoci_iff.mp hU
    obtain ⟨hU'std, hU'arr, -⟩ := mem_trvuoci_iff.mp hU'
    obtain ⟨hA, hAt⟩ := mem_trvaotci_iff.mp hUarr
    obtain ⟨hA', hA't⟩ := mem_trvaotci_iff.mp hU'arr
    obtain ⟨hAf, hAdom, -⟩ := mem_aotci_iff.mp hA
    obtain ⟨hA'f, hA'dom, -⟩ := mem_aotci_iff.mp hA'
    have hstd := (mem_stduoci_iff.mp hUstd).right
    have hstd' := (mem_stduoci_iff.mp hU'std).right
    refine hAf.ext hA'f (hAdom.trans hA'dom.symm) fun i hi ↦ ?_
    rw [hAdom] at hi
    have hiω := mem_omega_of_mem_succ hn hi
    have hT := hAt i hi
    have hT' := hA't i hi
    have hTo := (mem_finotci_iff.mp (mem_trvotci_iff.mp hT).left).left
    have hT'o := (mem_finotci_iff.mp (mem_trvotci_iff.mp hT').left).left
    rcases isEven_or_isOdd hiω with he | ho
    swap
    · -- odd levels: empty trees
      rw [eq_emptySLOT_of_ndOf_eq_empty (isSLOT_of_mem_otci hTo)
          ((mem_trvotci_iff.mp hT).right.right ho),
        eq_emptySLOT_of_ndOf_eq_empty (isSLOT_of_mem_otci hT'o)
          ((mem_trvotci_iff.mp hT').right.right ho)]
    have hlbl := stdLbls_of_stduociCond hstd hi he
    have hlbl' := stdLbls_of_stduociCond hstd' hi he
    by_cases hi0 : i = ∅
    · -- level `0`
      subst hi0
      rw [eq_trvTree_of_mem_otci_empty hTo hlbl, eq_trvTree_of_mem_otci_empty hT'o hlbl']
    -- even levels `i > 0`: the roots are trivial `uoci`'s of the odd level `i - 1 < n`
    obtain ⟨hmω, hmi, him⟩ := sUnion_mem_of_ne_empty hiω hi0
    have hmn : ⋃₀ i ∈ n := sUnion_mem_of_mem_succ hn hi
      (empty_mem_of_ordinal_of_ne_empty (ordinal_of_mem ordinal_omega hiω) hi0)
    have hmo : IsOdd (⋃₀ i) := by
      have h := he
      rwa [him, isEven_succ_iff hmω] at h
    have hTo2 := hTo
    have hT'o2 := hT'o
    rw [mem_otci_iff_of_ne_empty hi0] at hTo2 hT'o2
    obtain ⟨-, -, hroot, hone, -⟩ := hTo2
    obtain ⟨-, -, hroot', hone', -⟩ := hT'o2
    obtain ⟨r, hr⟩ := hone he
    obtain ⟨r', hr'⟩ := hone' he
    have hrmem : r ∈ rtOf (aoc U ﹫ i) := by
      rw [hr]
      exact mem_singleton r
    have hr'mem : r' ∈ rtOf (aoc U' ﹫ i) := by
      rw [hr']
      exact mem_singleton r'
    have huc := hroot r hrmem
    have huc' := hroot' r' hr'mem
    rw [trvuociL_ciRec_restrict hmi] at huc huc'
    exact eq_of_mem_trvotci hiω hi0 he hT hT' hlbl hlbl' hrmem hr'mem
      ((ih _ hmn).right hmo _ huc _ huc')
  refine ⟨harr, fun hno U hU U' hU' ↦ ?_⟩
  -- odd levels: the trivial `uoci`'s are triples
  have htriple (V : M) (hV : V ∈ trvuoci n) : V = ciTriple (aoc V) ∅ dct := by
    have hsig := sig_eq_empty_of_mem_trvuoci hn hV
    obtain ⟨hVstd, -, hVct⟩ := mem_trvuoci_iff.mp hV
    have hVu := (mem_stduoci_iff.mp hVstd).left
    rw [mem_uoci_iff_of_mem_omega hn] at hVu
    obtain ⟨hVf, -, -, -, -, -, hdom3, -⟩ := hVu
    rw [← hsig, ← hVct]
    exact eq_ciTriple hVf (hdom3.mpr (.inl ⟨hsig, hno⟩))
  rw [htriple U hU, htriple U' hU', harr U hU U' hU']

theorem trvUniq (hn : n ∈ (ω : M)) : TrvUniq n :=
  induction_of_modelsZF (A := fun x ↦ x ∈ (ω : M) → TrvUniq x)
    (fun _ ih hx ↦ trvUniq_of_forall hx fun m hm ↦ ih m hm (ordinal_omega.transitive _ hx hm))
    n hn

/-- All elements of `trvuoci_n` have the same array -/
theorem aoc_eq_of_mem_trvuoci (hn : n ∈ (ω : M)) (hU : U ∈ trvuoci n) (hU' : U' ∈ trvuoci n) :
    aoc U = aoc U' :=
  (trvUniq hn).left U hU U' hU'

/-- For odd `n`, `trvuoci_n` has at most one element -/
theorem eq_of_mem_trvuoci_of_isOdd (hn : n ∈ (ω : M)) (hno : IsOdd n) (hU : U ∈ trvuoci n)
    (hU' : U' ∈ trvuoci n) : U = U' :=
  (trvUniq hn).right hno U hU U' hU'

end Induction

section Roots

/-! ### The roots of the trees in `otci_n` -/

/-- The roots of a tree in `otci_n` for `n > 0` have the same key -/
theorem aoc_uc_eq_of_mem_rtOf (hn : n ∈ (ω : M)) (hn0 : n ≠ ∅) (hP : T ∈ otci n)
    (hr : r ∈ rtOf T) {r' : M} (hr' : r' ∈ rtOf T) : aoc (uc r) = aoc (uc r') := by
  obtain ⟨hmω, hmn, -⟩ := sUnion_mem_of_ne_empty hn hn0
  rw [mem_otci_iff_of_ne_empty hn0] at hP
  obtain ⟨-, -, hroot, -⟩ := hP
  have huc := hroot r hr
  have huc' := hroot r' hr'
  rw [trvuociL_ciRec_restrict hmn] at huc huc'
  exact aoc_eq_of_mem_trvuoci hmω huc huc'

/-- The roots of a tree in `otci_n` for `n > 0` form a single linearly ordered set -/
theorem losSet_ndlos_of_mem_rtOf (hn : n ∈ (ω : M)) (hn0 : n ≠ ∅) (hP : T ∈ otci n)
    (hr : r ∈ rtOf T) : losSet ((SLOTreeStructure.ofM T).ndlos r) = rtOf T := by
  have hS : (SLOTreeStructure.ofM T).IsSLOTreeStructure := isSLOT_of_mem_otci hP
  have hrnd := mem_ndOf_of_mem_rtOf hr
  ext b
  rw [hS.mem_losSet_ndlos_iff hrnd, hS.isTreeStructure.sbl_val_of_mem_rt hr]
  refine ⟨fun hb ↦ hb.left, fun hb ↦ ⟨hb, aoc_uc_eq_of_mem_rtOf hn hn0 hP hb hr⟩⟩

end Roots

end FirstOrder.Language.MemStructure
