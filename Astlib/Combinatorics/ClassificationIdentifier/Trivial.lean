/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.HereditarilyFinite
/-!
# Trivial `uoci`'s

For every `n ∈ ω`, `trvuoci_n` has a unique element `trvU n` (`existsUnique_mem_trvuoci`): the
function `{(0, A), (1, ∅), (2, c)}`, where `c` is `ct` or `dct` as `n` is even or odd, and
`A(j) = trvTreeAt j U_{j-1}` (with `U_{-1} = otci0Uc`) is

* the tree with the single node `(U_{j-1}, ∅)` if `j = 0` or `j` is odd;
* for even `j > 0`, the root `(U_{j-1}, ∅)` together with one child `(q, (U_{j-1}, ∅))` for each
  extension `(U_{j-1}, q) ∈ ext_{j-1}` (`trvChd`).

The proof is by induction on `n`. The key facts are:

* a standard `uoci` is determined by its array and its continuity type when it is continuous
  (`eq_of_aoc_eq_of_ctp_eq_ct`), since its signature lists its discontinuous nodes by their labels
  (`sig_eq_of_aoc_eq`), and continuous `uoci`'s have no extensions;
* for odd `n`, an extension `Q` of `U_n` adds a new root `(R, ∅)` at level `n` with
  `R ∈ stduoci_{n-1}` having the trivial array, and the children of `(R, ∅)` are then forced to be
  `trvChd (n - 1) R`; so `Q` is determined by `R`, and there are only finitely many such `R`
  (`finite_trvChd`).
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M] {A B b c d j k m n p q r x y P Q R T U X : M}

section General

/-! ### Extensions and standard `uoci`'s -/

/-- The pairs in `ext_n` consist of standard `uoci`'s, the first discontinuous and the second
continuous -/
theorem mem_ciExt_props (h : !(P, Q) ∈ ciExt n) :
    P ∈ stduoci n ∧ Q ∈ stduoci n ∧ ctp P = dct ∧ ctp Q = ct := by
  obtain ⟨P', hP', Q', hQ', hPQ, hext⟩ := mem_ciExt_iff.mp h
  rw [orderedPair_eq_orderedPair_iff] at hPQ
  obtain ⟨rfl, rfl⟩ := hPQ
  exact ⟨hP', hQ', hext.left, hext.right.left⟩

/-- A continuous `uoci` has no extensions -/
theorem not_mem_ciExt_of_ctp_eq_ct (hct : ctp P = ct) (Q : M) : !(P, Q) ∉ ciExt n :=
  fun h ↦ ct_ne_dct (hct.symm.trans (mem_ciExt_props h).right.right.left)

/-- The continuity type of a `uoci` is `ct` or `dct` -/
theorem ctp_eq_ct_or_dct (hn : n ∈ (ω : M)) (hP : P ∈ uoci n) : ctp P = ct ∨ ctp P = dct := by
  rw [mem_uoci_iff_of_mem_omega hn] at hP
  exact hP.right.right.right.right.left

/-- Continuous `uoci`'s are triples -/
theorem dom_eq_three_of_ctp_eq_ct (hn : n ∈ (ω : M)) (hP : P ∈ uoci n) (hct : ctp P = ct) :
    dom P = ((3 : ℕ) : M) := by
  rw [mem_uoci_iff_of_mem_omega hn] at hP
  obtain ⟨-, -, -, -, -, -, hdom3, -⟩ := hP
  exact hdom3.mpr (.inr hct)

/-- Children are not roots -/
theorem not_mem_rtOf_of_mem_chdOf (hX : IsSLOT X) (hd : d ∈ chdOf X q) : d ∉ rtOf X := by
  have hT := (show (SLOTreeStructure.ofM X).IsSLOTreeStructure from hX).isTreeStructure
  have hq := hT.mem_nd_of_mem_chd_val hd
  intro hrt
  have h := hT.dep_of_mem_chd q hq d hd
  rw [(TreeStructure.mem_rt_iff.mp hrt).right] at h
  exact succ_ne_empty _ h.symm

/-- The parent of a child -/
theorem prtOf_eq_of_mem_chdOf (hX : IsSLOT X) (hd : d ∈ chdOf X q) : prtOf X d = q := by
  have hT := (show (SLOTreeStructure.ofM X).IsSLOTreeStructure from hX).isTreeStructure
  exact hT.isFunction_prt.val_eq_of_rel
    ((hT.rel_prt_iff_mem_chd (hT.mem_nd_of_mem_chd_val hd)).mpr hd)

/-- The nodes of the trees in an array of `aotci_n` -/
theorem mem_ndOf_of_sigCond (hn : n ∈ (ω : M)) (hA : aoc P ∈ aotci n) {i : M}
    (hi : SigCond n P i) : sigdcn P i ∈ ndOf (aoc P ﹫ siglvl P i) := by
  obtain ⟨-, hlvl, heven, hodd, -⟩ := hi
  have hT := val_mem_otci_of_mem_aotci hA hlvl
  have hX := isSLOT_of_mem_otci hT
  rcases isEven_or_isOdd (mem_omega_of_mem_succ hn hlvl) with he | ho
  · obtain ⟨r, hr⟩ := exists_mem_rtOf_of_mem_otci hT he
    rcases heven he r hr with h | ⟨_, -, -, h⟩
    · exact mem_ndOf_of_mem_chdOf hX h
    · exact mem_ndOf_of_mem_chdOf hX h
  · rcases hodd ho with h | ⟨_, -, -, h⟩
    · exact mem_ndOf_of_mem_rtOf h
    · exact mem_ndOf_of_mem_chdOf hX h

/-- The signature entries of a `uoci` are not roots at even levels -/
theorem not_isEven_and_mem_rtOf_of_sigCond (hA : aoc P ∈ aotci n) {i : M}
    (hi : SigCond n P i) :
    ¬(IsEven (siglvl P i) ∧ sigdcn P i ∈ rtOf (aoc P ﹫ siglvl P i)) := by
  rintro ⟨he, hrt⟩
  obtain ⟨-, hlvl, heven, -, -⟩ := hi
  have hX := isSLOT_of_mem_otci (val_mem_otci_of_mem_aotci hA hlvl)
  rcases heven he _ hrt with h | ⟨_, -, -, h⟩
  · exact not_mem_rtOf_of_mem_chdOf hX h hrt
  · exact not_mem_rtOf_of_mem_chdOf hX h hrt

/-- The signature of a standard `uoci` lists its discontinuous nodes other than the roots of even
levels, indexed by their labels: the `i`-th entry of the signature of `P` is the `i`-th entry of
the signature of any standard `Q` with the same array -/
theorem sig_val_of_aoc_eq (hn : n ∈ (ω : M)) (hP : P ∈ stduoci n) (hQ : Q ∈ stduoci n)
    (h : aoc P = aoc Q) {i : M} (hi : i ∈ dom (sig P)) :
    i ∈ dom (sig Q) ∧ sig Q ﹫ i = sig P ﹫ i := by
  rw [mem_stduoci_iff] at hP hQ
  obtain ⟨hPu, hPstd⟩ := hP
  obtain ⟨-, hQstd⟩ := hQ
  rw [mem_uoci_iff_of_mem_omega hn] at hPu
  obtain ⟨-, -, haoc, ⟨hsigf, hinj, -, hsig⟩, -⟩ := hPu
  have hA := (mem_finaotci_iff.mp haoc).left
  have hnd := mem_ndOf_of_sigCond hn hA (hsig i hi)
  have hnot := not_isEven_and_mem_rtOf_of_sigCond hA (hsig i hi)
  obtain ⟨⟨l, d, hld⟩, hlvl, -, -, hctp⟩ := hsig i hi
  have hl : siglvl P i = l := by rw [siglvl, hld, lvl_orderedPair]
  have hd : sigdcn P i = d := by rw [sigdcn, hld, dcn_orderedPair]
  rw [hl] at hlvl hnd hnot
  rw [hd] at hnd hnot hctp
  have hPi := (hPstd l hlvl d hnd).right.left ⟨hctp, hnot⟩
  rw [h] at hnd hnot
  have hQi := (hQstd l hlvl d hnd).right.left ⟨hctp, hnot⟩
  have hpair : !(l, d) ≠ ∅ := orderedPair_ne_empty l d
  have hlbl : lbl d = i := by
    have hmem : lbl d ∈ dom (sig P) := by
      by_contra hne
      rw [val_eq_empty_of_not_mem_dom hne] at hPi
      exact hpair hPi
    exact hinj _ hmem _ hi (hPi.symm.trans hld.symm)
  rw [hlbl] at hQi
  refine ⟨?_, by rw [← hQi, hld]⟩
  by_contra hne
  rw [val_eq_empty_of_not_mem_dom hne] at hQi
  exact hpair hQi

/-- The signature of a standard `uoci` is determined by its array -/
theorem sig_eq_of_aoc_eq (hn : n ∈ (ω : M)) (hP : P ∈ stduoci n) (hQ : Q ∈ stduoci n)
    (h : aoc P = aoc Q) : sig P = sig Q := by
  have hsigf (R : M) (hR : R ∈ stduoci n) : IsFunction (sig R) := by
    have hRu := (mem_stduoci_iff.mp hR).left
    rw [mem_uoci_iff_of_mem_omega hn] at hRu
    exact hRu.right.right.right.left.left
  refine (hsigf P hP).ext (hsigf Q hQ) ?_ fun i hi ↦ (sig_val_of_aoc_eq hn hP hQ h hi).right.symm
  ext i
  exact ⟨fun hi ↦ (sig_val_of_aoc_eq hn hP hQ h hi).left,
    fun hi ↦ (sig_val_of_aoc_eq hn hQ hP h.symm hi).left⟩

/-- A continuous standard `uoci` is determined by its array -/
theorem eq_of_aoc_eq_of_ctp_eq_ct (hn : n ∈ (ω : M)) (hP : P ∈ stduoci n) (hQ : Q ∈ stduoci n)
    (hPct : ctp P = ct) (hQct : ctp Q = ct) (h : aoc P = aoc Q) : P = Q := by
  have hPu := (mem_stduoci_iff.mp hP).left
  have hQu := (mem_stduoci_iff.mp hQ).left
  have hPf : IsFunction P := ((mem_uoci_iff_of_mem_omega hn).mp hPu).left
  have hQf : IsFunction Q := ((mem_uoci_iff_of_mem_omega hn).mp hQu).left
  calc P = ciTriple (aoc P) (sig P) (ctp P) :=
        eq_ciTriple hPf (dom_eq_three_of_ctp_eq_ct hn hPu hPct)
    _ = ciTriple (aoc Q) (sig Q) (ctp Q) := by rw [h, sig_eq_of_aoc_eq hn hP hQ h, hPct, hQct]
    _ = Q := (eq_ciTriple hQf (dom_eq_three_of_ctp_eq_ct hn hQu hQct)).symm

/-- Continuous nodes have no children -/
theorem chdOf_eq_empty_of_ctp_eq_ct (hn : n ∈ (ω : M)) (hT : T ∈ otci n) (hp : p ∈ ndOf T)
    (hct : ctp (uc p) = ct) : chdOf T p = ∅ := by
  by_cases hn0 : n = ∅
  · subst hn0
    rw [mem_otci_empty_iff] at hT
    obtain ⟨l, -, rfl⟩ := hT
    exact chdOf_irmrtOf_emptySLOT _ _
  obtain ⟨-, hmn, -⟩ := sUnion_mem_of_ne_empty hn hn0
  rw [mem_otci_iff_of_ne_empty hn0] at hT
  obtain ⟨-, -, -, -, hchd⟩ := hT
  rw [empty_iff]
  intro q hq
  obtain ⟨q', hq', -⟩ := ((hchd p hp).left (aoc (uc q))).mp ⟨q, hq, rfl⟩
  rw [extL_ciRec_restrict hmn] at hq'
  exact not_mem_ciExt_of_ctp_eq_ct hct q' hq'

end General

section TrvChd

/-! ### The children of the roots of the trivial trees -/

theorem mem_trvChd_iff : x ∈ trvChd m U ↔ ∃ q, x = !(q, !(U, ∅)) ∧ !(U, q) ∈ ciExt m := by
  rw [trvChd, mem_comprehension_iff]
  constructor
  · exact fun h ↦ h.right
  · rintro ⟨q, rfl, hq⟩
    refine ⟨?_, q, rfl, hq⟩
    rw [pair_mem_sprod_iff, mem_singleton_iff]
    exact ⟨(mem_ciExt_props hq).right.left, rfl⟩

/-- A continuous `uoci` has no children in a trivial tree -/
theorem trvChd_eq_empty_of_ctp_eq_ct (hct : ctp U = ct) : trvChd m U = ∅ := by
  rw [empty_iff]
  intro x hx
  rw [mem_trvChd_iff] at hx
  obtain ⟨q, -, hq⟩ := hx
  exact not_mem_ciExt_of_ctp_eq_ct hct q hq

/-- The children have distinct keys -/
theorem eq_of_mem_trvChd (hm : m ∈ (ω : M)) (hx : x ∈ trvChd m U) (hy : y ∈ trvChd m U)
    (h : aoc (uc x) = aoc (uc y)) : x = y := by
  rw [mem_trvChd_iff] at hx hy
  obtain ⟨q, rfl, hq⟩ := hx
  obtain ⟨q', rfl, hq'⟩ := hy
  rw [uc_orderedPair, uc_orderedPair] at h
  obtain ⟨-, hqs, -, hqct⟩ := mem_ciExt_props hq
  obtain ⟨-, hqs', -, hqct'⟩ := mem_ciExt_props hq'
  rw [eq_of_aoc_eq_of_ctp_eq_ct hm hqs hqs' hqct hqct' h]

theorem not_mem_trvChd : !(U, ∅) ∉ trvChd m U := by
  intro h
  rw [mem_trvChd_iff] at h
  obtain ⟨q, hq, -⟩ := h
  rw [orderedPair_eq_orderedPair_iff] at hq
  exact orderedPair_ne_empty U ∅ hq.right.symm

end TrvChd

section TreeAt

/-! ### The trivial trees -/

theorem trvTreeAt_of_isEven (hj : IsEven j ∧ j ≠ ∅) :
    trvTreeAt j r = asnchdOf (trvTree r) !(r, ∅) (trvChd (⋃₀ j) r) := by
  simp only [trvTreeAt, if_pos hj, trvEvenTree, left_orderedPair, right_orderedPair]

theorem trvTreeAt_of_not_isEven (hj : ¬(IsEven j ∧ j ≠ ∅)) : trvTreeAt j r = trvTree r := by
  rw [trvTreeAt, if_neg hj]

theorem trvChd_inter_ndOf_trvTree : trvChd m r ∩ ndOf (trvTree r) = ∅ := by
  rw [ndOf_trvTree]
  ext x
  rw [mem_inter_iff, mem_singleton_iff]
  refine ⟨fun ⟨hx, hxr⟩ ↦ ?_, by simp⟩
  rw [hxr] at hx
  exact (not_mem_trvChd hx).elim

theorem ndOf_trvTreeAt_of_isEven (hj : IsEven j ∧ j ≠ ∅) :
    ndOf (trvTreeAt j r) = insert !(r, ∅) (trvChd (⋃₀ j) r) := by
  rw [trvTreeAt_of_isEven hj]
  change (((∅ : SLOTreeStructure M).irmrt !(r, ∅)).asnchd !(r, ∅) (trvChd (⋃₀ j) r)).nd = _
  rw [SLOTreeStructure.nd_asnchd, SLOTreeStructure.nd_empty_irmrt, insert_eq]

/-- The nodes of `trvTreeAt j r` are the root `(r, ∅)` and the children `trvChd (j - 1) r` -/
theorem ndOf_trvTreeAt_subset : ndOf (trvTreeAt j r) ⊆ insert !(r, ∅) (trvChd (⋃₀ j) r) := by
  by_cases hj : IsEven j ∧ j ≠ ∅
  · rw [ndOf_trvTreeAt_of_isEven hj]
    exact subset_refl _
  · rw [trvTreeAt_of_not_isEven hj, ndOf_trvTree]
    intro z hz
    rw [mem_singleton_iff] at hz
    rw [hz]
    exact mem_insert _ _

section Even

variable (hj : IsEven j ∧ j ≠ ∅) (hm : ⋃₀ j ∈ (ω : M)) (hr : IsFunction r)
  (hdom : dom r = ((3 : ℕ) : M))
include hj hm hr hdom

theorem isSLOT_trvTreeAt_of_isEven : IsSLOT (trvTreeAt j r) := by
  rw [trvTreeAt_of_isEven hj]
  have hS₀ : (SLOTreeStructure.ofM (trvTree r)).IsSLOTreeStructure := isSLOT_trvTree hr hdom
  refine hS₀.asnchd ?_ (chdOf_trvTree r _) (fun x hx ↦ ?_) trvChd_inter_ndOf_trvTree
    (fun x hx y hy hxy h ↦ hxy (eq_of_mem_trvChd hm hx hy h))
  · change _ ∈ ndOf (trvTree r)
    rw [ndOf_trvTree]
    exact mem_singleton _
  rw [mem_trvChd_iff] at hx
  obtain ⟨q, rfl, hq⟩ := hx
  obtain ⟨-, hqs, -, hqct⟩ := mem_ciExt_props hq
  have hqu := (mem_stduoci_iff.mp hqs).left
  refine ⟨⟨_, _, rfl⟩, ?_, ?_⟩ <;> rw [left_orderedPair]
  · exact ((mem_uoci_iff_of_mem_omega hm).mp hqu).left
  · rw [dom_eq_three_of_ctp_eq_ct hm hqu hqct]
    exact natCast_three_mem

omit hm in
theorem rtOf_trvTreeAt_of_isEven : rtOf (trvTreeAt j r) = {!(r, ∅)} := by
  have hS₀ : (SLOTreeStructure.ofM (trvTree r)).IsSLOTreeStructure := isSLOT_trvTree hr hdom
  rw [trvTreeAt_of_isEven hj, ← rtOf_trvTree r]
  exact hS₀.rt_asnchd trvChd_inter_ndOf_trvTree

theorem chdOf_trvTreeAt_root : chdOf (trvTreeAt j r) !(r, ∅) = trvChd (⋃₀ j) r := by
  have hS : (SLOTreeStructure.ofM (trvTreeAt j r)).IsSLOTreeStructure :=
    isSLOT_trvTreeAt_of_isEven hj hm hr hdom
  have hf := hS.isTreeStructure.isFunction_chd
  rw [trvTreeAt_of_isEven hj] at hf ⊢
  exact SLOTreeStructure.chd_asnchd_val_self hf (chdOf_trvTree r _)

omit hm in
theorem chdOf_trvTreeAt_of_mem_trvChd (hx : x ∈ trvChd (⋃₀ j) r) :
    chdOf (trvTreeAt j r) x = ∅ := by
  have hS₀ : (SLOTreeStructure.ofM (trvTree r)).IsSLOTreeStructure := isSLOT_trvTree hr hdom
  have hb : !(r, ∅) ∈ ndOf (trvTree r) := by
    rw [ndOf_trvTree]
    exact mem_singleton _
  rw [trvTreeAt_of_isEven hj]
  exact hS₀.chd_asnchd_val_of_mem_new hb trvChd_inter_ndOf_trvTree hx

end Even

/-- In a tree of level `k > 0`, the continuous children with label `(R, ∅)` of a node `(R, ∅)` are
exactly `trvChd (k - 1) R`, one for each extension of `R` -/
theorem chdOf_eq_trvChd (hk : k ∈ (ω : M)) (hk0 : k ≠ ∅) (hT : T ∈ otci k)
    (hb : !(R, ∅) ∈ ndOf T) (hct : ∀ c ∈ chdOf T !(R, ∅), ctp (uc c) = ct)
    (hlbl : ∀ c ∈ chdOf T !(R, ∅), lbl c = !(R, ∅)) : chdOf T !(R, ∅) = trvChd (⋃₀ k) R := by
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
  ext x
  rw [mem_trvChd_iff]
  constructor
  · intro hx
    obtain ⟨q, hq, hqD⟩ := (hD (aoc (uc x))).mp ⟨x, hx, rfl⟩
    exact ⟨q, hchild hx hq hqD, hq⟩
  · rintro ⟨q, rfl, hq⟩
    obtain ⟨c, hc, hcD⟩ := (hD (aoc q)).mpr ⟨q, hq, rfl⟩
    rwa [← hchild hc hq hcD.symm]

end TreeAt

section Step

/-! ### The trivial trees from the trivial `uoci`'s of lower levels -/

variable (hj : j ∈ (ω : M)) (ih : ∀ m ∈ j, TrvGood m)
include hj ih

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

section Tree

variable (hj : j ∈ (ω : M)) (ih : ∀ m ∈ j, TrvGood m)
include hj ih

/-- The trivial trees are in `trvotci_j` -/
theorem trvTreeAt_mem_trvotci (hr : IsTrvRoot j r) : trvTreeAt j r ∈ trvotci j := by
  obtain ⟨hrf, hrdom, hrev, hrodd⟩ := hr.props hj ih
  by_cases hje : IsEven j ∧ j ≠ ∅
  swap
  · -- a single node
    rw [trvTreeAt_of_not_isEven hje]
    have hslot : IsSLOT (trvTree r) := isSLOT_trvTree hrf hrdom
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
        exact ⟨∅, empty_mem_vonNeumann_omega, rfl⟩
      · exact (hj0 rfl).elim
    have hjo : IsOdd j := by
      rcases isEven_or_isOdd hj with h | h
      · exact (hje ⟨h, hj0⟩).elim
      · exact h
    obtain ⟨hmω, hmj, -⟩ := sUnion_mem_of_ne_empty hj hj0
    have hrt : r ∈ trvuoci (⋃₀ j) := by
      rcases hr with ⟨h, -⟩ | ⟨-, h⟩
      · exact (hj0 h).elim
      · exact h
    obtain ⟨hrstd, hraoc, -⟩ := mem_trvuoci_iff.mp hrt
    rw [mem_otci_iff_of_ne_empty hj0]
    unfold OtciCond
    rw [stduociL_ciRec_restrict hmj, trvuociL_ciRec_restrict hmj, trvaotciL_ciRec_restrict hmj,
      extL_ciRec_restrict hmj, ndOf_trvTree, rtOf_trvTree]
    have hnoext : ∀ q, !(r, q) ∉ ciExt (⋃₀ j) := not_mem_ciExt_of_ctp_eq_ct (hrodd hjo)
    refine ⟨hslot, fun p hp ↦ ?_, fun _ ↦ ⟨⟨_, rfl⟩, fun p hp ↦ ?_⟩,
      fun _ ↦ ⟨⟨_, mem_singleton _, ?_⟩, fun p hp ↦ ?_⟩, fun p hp ↦ ?_⟩
    · rw [mem_singleton_iff] at hp
      rw [hp, uc_orderedPair, lbl_orderedPair]
      exact ⟨hrstd, empty_mem_vonNeumann_omega⟩
    · rw [mem_singleton_iff] at hp
      rw [hp, uc_orderedPair]
      exact hrt
    · rw [uc_orderedPair]
      exact hrt
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
  -- an even level: the root and its children
  obtain ⟨hmω, hmj, hjm⟩ := sUnion_mem_of_ne_empty hj hje.right
  have hrt : r ∈ trvuoci (⋃₀ j) := by
    rcases hr with ⟨h, -⟩ | ⟨-, h⟩
    · exact (hje.right h).elim
    · exact h
  obtain ⟨U, hU, -, -, -, -, -, -, -, hUfin⟩ := ih _ hmj
  have hmodd : IsOdd (⋃₀ j) := by
    have h := hje.left
    rwa [hjm, isEven_succ_iff hmω] at h
  have hfin : MemStructure.Finite (trvChd (⋃₀ j) r) := by
    rw [(hU r).mp hrt]
    exact hUfin hmodd
  have hrstd := (mem_trvuoci_iff.mp hrt).left
  have hrV := mem_vonNeumann_omega_of_mem_stduoci hmω hrstd
  have hdct := hrev hje.left
  have hnd := ndOf_trvTreeAt_of_isEven (r := r) hje
  have hrtT := rtOf_trvTreeAt_of_isEven hje hrf hrdom
  have hslot := isSLOT_trvTreeAt_of_isEven hje hmω hrf hrdom
  have hchdb := chdOf_trvTreeAt_root hje hmω hrf hrdom
  rw [mem_trvotci_iff, mem_finotci_iff, hnd]
  refine ⟨⟨?_, hfin.insert _⟩, fun _ p hp ↦ ?_, fun hjo ↦ (hje.left.not_isOdd hjo).elim⟩
  swap
  · -- the root is the only discontinuous node
    rw [hnd, mem_insert_iff] at hp
    rw [hrtT, mem_singleton_iff]
    rcases hp with rfl | hp
    · rw [uc_orderedPair]
      exact iff_of_true hdct rfl
    · obtain ⟨q, rfl, hq⟩ := mem_trvChd_iff.mp hp
      rw [uc_orderedPair, (mem_ciExt_props hq).right.right.right]
      exact iff_of_false (fun h ↦ ct_ne_dct h) fun h ↦ not_mem_trvChd (h ▸ hp)
  rw [mem_otci_iff_of_ne_empty hje.right]
  unfold OtciCond
  rw [stduociL_ciRec_restrict hmj, trvuociL_ciRec_restrict hmj, extL_ciRec_restrict hmj, hnd,
    hrtT]
  refine ⟨hslot, fun p hp ↦ ?_, fun _ ↦ ⟨⟨_, rfl⟩, fun p hp ↦ ?_⟩,
    fun hjo ↦ (hje.left.not_isOdd hjo).elim, fun p hp ↦ ?_⟩
  · -- the identifiers and the labels
    rw [mem_insert_iff] at hp
    rcases hp with rfl | hp
    · rw [uc_orderedPair, lbl_orderedPair]
      exact ⟨hrstd, empty_mem_vonNeumann_omega⟩
    · obtain ⟨q, rfl, hq⟩ := mem_trvChd_iff.mp hp
      rw [uc_orderedPair, lbl_orderedPair]
      exact ⟨(mem_ciExt_props hq).right.left,
        orderedPair_mem_vonNeumann_omega hrV empty_mem_vonNeumann_omega⟩
  · rw [mem_singleton_iff] at hp
    rw [hp, uc_orderedPair]
    exact hrt
  -- the children
  rw [mem_insert_iff] at hp
  rcases hp with rfl | hp
  swap
  · obtain ⟨q, rfl, hq⟩ := mem_trvChd_iff.mp hp
    have hqct := (mem_ciExt_props hq).right.right.right
    rw [chdOf_trvTreeAt_of_mem_trvChd hje hrf hrdom hp, uc_orderedPair]
    refine ⟨fun D ↦ iff_of_false ?_ ?_, fun q' hq' ↦ (not_mem_ciExt_of_ctp_eq_ct hqct q' hq').elim⟩
    · rintro ⟨c, hc, -⟩
      simp at hc
    · rintro ⟨q', hq', -⟩
      exact not_mem_ciExt_of_ctp_eq_ct hqct q' hq'
  rw [hchdb, uc_orderedPair]
  refine ⟨fun D ↦ ⟨?_, ?_⟩, fun q hq c hc ↦ ?_⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨q, rfl, hq⟩ := mem_trvChd_iff.mp hx
    exact ⟨q, hq, by rw [uc_orderedPair]⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨!(q, !(r, ∅)), mem_trvChd_iff.mpr ⟨q, rfl, hq⟩, by rw [uc_orderedPair]⟩
  -- the linearly ordered set of the children with key `aoc q` is `{(q, (r, ∅))}`
  have hS : (SLOTreeStructure.ofM (trvTreeAt j r)).IsSLOTreeStructure := hslot
  have hT := hS.isTreeStructure
  have hbnd : !(r, ∅) ∈ (SLOTreeStructure.ofM (trvTreeAt j r)).nd := by
    change _ ∈ ndOf _
    rw [hnd]
    exact mem_insert _ _
  have hx₀ : !(q, !(r, ∅)) ∈ trvChd (⋃₀ j) r := mem_trvChd_iff.mpr ⟨q, rfl, hq⟩
  have hchdb' : (SLOTreeStructure.ofM (trvTreeAt j r)).ts.chd ﹫ !(r, ∅) = trvChd (⋃₀ j) r :=
    hchdb
  have hCne : trvChd (⋃₀ j) r ≠ ∅ := by
    rw [ne_empty_iff]
    exact ⟨_, hx₀⟩
  have hlos : chdlosOf (trvTreeAt j r) !(r, ∅) =
      (SLOTreeStructure.ofM (trvTreeAt j r)).losfn ﹫ trvChd (⋃₀ j) r := by
    change (SLOTreeStructure.ofM (trvTreeAt j r)).chdlos ﹫ _ = _
    rw [hS.chdlos_val ((hS.mem_dom_chdlos_iff).mpr ⟨hbnd, by rwa [SLOTreeStructure.chd, hchdb']⟩)]
    rw [SLOTreeStructure.chd, hchdb']
  have hX : trvChd (⋃₀ j) r ∈ (SLOTreeStructure.ofM (trvTreeAt j r)).sblptn := by
    rw [SLOTreeStructure.sblptn, TreeStructure.mem_sblptn_iff, hT.isFunction_chd.mem_ran_iff,
      hT.dom_chd]
    exact ⟨.inr ⟨_, hbnd, hchdb'⟩, hCne⟩
  have hD : aoc q ∈ dom ((SLOTreeStructure.ofM (trvTreeAt j r)).losfn ﹫ trvChd (⋃₀ j) r) := by
    rw [hS.mem_dom_losfn_val_iff hX]
    exact ⟨_, hx₀, by rw [left_orderedPair]; rfl⟩
  have hmemset (y : M) : y ∈ losSet (((SLOTreeStructure.ofM (trvTreeAt j r)).losfn ﹫
      trvChd (⋃₀ j) r) ﹫ aoc q) ↔ y = !(q, !(r, ∅)) := by
    rw [hS.mem_losSet_iff hX hD]
    constructor
    · rintro ⟨hy, hyD⟩
      refine eq_of_mem_trvChd hmω hy hx₀ ?_
      rw [uc_orderedPair]
      exact hyD
    · rintro rfl
      exact ⟨hx₀, by rw [left_orderedPair]; rfl⟩
  rw [hlos] at hc ⊢
  rw [(hmemset c).mp hc, uc_orderedPair]
  refine ⟨rfl, iff_of_true ⟨(hmemset _).mpr rfl, fun y hy hyc ↦ ?_⟩
    (mem_ciExt_props hq).right.right.right⟩
  rw [(hmemset y).mp hy] at hyc
  exact (hS.isStrictLinearOrderedSet hX hD).isStrictLinearOrder.irrefl _ hyc

/-- A tree in `trvotci_j` with the labels required in a standard `uoci` is a trivial tree -/
theorem exists_eq_trvTreeAt (hT : T ∈ trvotci j)
    (hstd : ∀ p ∈ ndOf T, ((IsEven j ∧ p ∈ rtOf T) → lbl p = ∅) ∧
      (ctp (uc p) = ct → (p ∈ rtOf T → lbl p = ∅) ∧ (p ∉ rtOf T → lbl p = prtOf T p))) :
    ∃ r, IsTrvRoot j r ∧ T = trvTreeAt j r := by
  rw [mem_trvotci_iff, mem_finotci_iff] at hT
  obtain ⟨⟨hTo, -⟩, hev, hodd⟩ := hT
  have hTslot := isSLOT_of_mem_otci hTo
  have hS : (SLOTreeStructure.ofM T).IsSLOTreeStructure := hTslot
  by_cases hj0 : j = ∅
  · subst hj0
    rw [mem_otci_empty_iff] at hTo
    obtain ⟨p, -, rfl⟩ := hTo
    have hpn : !(otci0Uc, p) ∈ ndOf (irmrtOf emptySLOT !(otci0Uc, p)) := by
      rw [ndOf_irmrtOf_emptySLOT]
      exact mem_singleton _
    have hpr : !(otci0Uc, p) ∈ rtOf (irmrtOf emptySLOT !(otci0Uc, p)) := by
      rw [rtOf_irmrtOf_emptySLOT]
      exact mem_singleton _
    have hp := (hstd _ hpn).left ⟨isEven_empty, hpr⟩
    rw [lbl_orderedPair] at hp
    subst hp
    refine ⟨otci0Uc, .inl ⟨rfl, rfl⟩, ?_⟩
    rw [trvTreeAt_of_not_isEven fun h ↦ h.right rfl]
    rfl
  obtain ⟨hmω, hmj, hjm⟩ := sUnion_mem_of_ne_empty hj hj0
  obtain ⟨U, hU, hUf, hUdom, hUsig, hUarr, hUev, -, hUstd, -⟩ := ih _ hmj
  have ihm : ∀ m ∈ ⋃₀ j, TrvGood m := fun m hm ↦
    ih m ((ordinal_of_mem ordinal_omega hj).transitive _ hmj hm)
  have hTo' := hTo
  rw [mem_otci_iff_of_ne_empty hj0] at hTo'
  obtain ⟨-, hnodes, hevc, hoddc, -⟩ := hTo'
  rw [stduociL_ciRec_restrict hmj] at hnodes
  rw [trvuociL_ciRec_restrict hmj] at hevc hoddc
  rw [trvaotciL_ciRec_restrict hmj] at hoddc
  -- the roots are `(U, ∅)`
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
  have hrtlbl : ∀ p ∈ rtOf T, lbl p = ∅ := by
    intro p hp
    have hpn := mem_ndOf_of_mem_rtOf hp
    obtain ⟨ha, hc⟩ := hstd p hpn
    rcases isEven_or_isOdd hj with hje | hjo
    · exact ha ⟨hje, hp⟩
    · exact (hc (hodd hjo p hpn)).left hp
  have hrtpair : ∀ p ∈ rtOf T, p = !(U, ∅) := by
    intro p hp
    have hu := hrtU p hp
    have hl := hrtlbl p hp
    obtain ⟨u, l, rfl⟩ := hS.isOrderedPair (mem_ndOf_of_mem_rtOf hp)
    rw [uc_orderedPair] at hu
    rw [lbl_orderedPair] at hl
    rw [hu, hl]
  have hbrt : !(U, ∅) ∈ rtOf T := by
    obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ ∈ rtOf T := by
      rcases isEven_or_isOdd hj with hje | hjo
      · obtain ⟨r₀, hr₀⟩ := (hevc hje).left
        exact ⟨r₀, by rw [hr₀]; exact mem_singleton _⟩
      · obtain ⟨q, hq, -⟩ := (hoddc hjo).left
        exact ⟨q, hq⟩
    rw [← hrtpair r₀ hr₀]
    exact hr₀
  have hrt : rtOf T = {!(U, ∅)} := by
    ext p
    rw [mem_singleton_iff]
    refine ⟨hrtpair p, ?_⟩
    rintro rfl
    exact hbrt
  have hb := mem_ndOf_of_mem_rtOf hbrt
  rcases isEven_or_isOdd hj with hje | hjo
  swap
  · -- an odd level: every node is continuous and hence childless, so every node is a root
    have hndrt : ∀ p ∈ ndOf T, p ∈ rtOf T := by
      intro p hp
      by_contra hpr
      have hpd : p ∈ (SLOTreeStructure.ofM T).ts.nd \ (SLOTreeStructure.ofM T).ts.rt := by
        rw [mem_sdiff_iff]
        exact ⟨hp, hpr⟩
      have hq := hS.isTreeStructure.prt_val_mem_nd hpd
      have hmem := hS.isTreeStructure.mem_chd_prt_val hpd
      have h0 := chdOf_eq_empty_of_ctp_eq_ct hj hTo hq (hodd hjo _ hq)
      rw [chdOf, SLOTreeStructure.chd] at h0
      rw [h0] at hmem
      simp at hmem
    have hnd : ndOf T = {!(U, ∅)} := by
      ext p
      rw [mem_singleton_iff]
      refine ⟨fun hp ↦ hrtpair p (hndrt p hp), ?_⟩
      rintro rfl
      exact hb
    refine ⟨U, .inr ⟨hj0, (hU U).mpr rfl⟩, ?_⟩
    rw [trvTreeAt_of_not_isEven fun h ↦ hjo.not_isEven h.left]
    exact eq_irmrtOf_emptySLOT hTslot hnd
  -- an even level: the non-root nodes are continuous children of the root
  have hnonrt : ∀ p ∈ ndOf T, p ∉ rtOf T → ctp (uc p) = ct := by
    intro p hp hpr
    rcases ctp_eq_ct_or_dct hmω (mem_stduoci_iff.mp (hnodes p hp).left).left with h | h
    · exact h
    · exact (hpr ((hev hje p hp).mp h)).elim
  have hndrt : ∀ p ∈ ndOf T, p ∉ rtOf T → p ∈ chdOf T !(U, ∅) := by
    intro p hp hpr
    have hpd : p ∈ (SLOTreeStructure.ofM T).ts.nd \ (SLOTreeStructure.ofM T).ts.rt := by
      rw [mem_sdiff_iff]
      exact ⟨hp, hpr⟩
    have hq := hS.isTreeStructure.prt_val_mem_nd hpd
    have hmem := hS.isTreeStructure.mem_chd_prt_val hpd
    by_cases hqr : (SLOTreeStructure.ofM T).ts.prt ﹫ p ∈ rtOf T
    · rw [hrtpair _ hqr] at hmem
      exact hmem
    · have h0 := chdOf_eq_empty_of_ctp_eq_ct hj hTo hq (hnonrt _ hq hqr)
      rw [chdOf, SLOTreeStructure.chd] at h0
      rw [h0] at hmem
      simp at hmem
  have hchdct : ∀ c ∈ chdOf T !(U, ∅), ctp (uc c) = ct := fun c hc ↦
    hnonrt c (mem_ndOf_of_mem_chdOf hTslot hc) (not_mem_rtOf_of_mem_chdOf hTslot hc)
  have hchdlbl : ∀ c ∈ chdOf T !(U, ∅), lbl c = !(U, ∅) := by
    intro c hc
    have hcn := mem_ndOf_of_mem_chdOf hTslot hc
    rw [((hstd c hcn).right (hchdct c hc)).right (not_mem_rtOf_of_mem_chdOf hTslot hc),
      prtOf_eq_of_mem_chdOf hTslot hc]
  have hchdb := chdOf_eq_trvChd hj hj0 hTo hb hchdct hchdlbl
  have hnd : ndOf T = insert !(U, ∅) (trvChd (⋃₀ j) U) := by
    rw [← hchdb]
    ext p
    rw [mem_insert_iff]
    constructor
    · intro hp
      by_cases hpr : p ∈ rtOf T
      · exact .inl (hrtpair p hpr)
      · exact .inr (hndrt p hp hpr)
    · rintro (rfl | hp)
      · exact hb
      · exact mem_ndOf_of_mem_chdOf hTslot hp
  refine ⟨U, .inr ⟨hj0, (hU U).mpr rfl⟩, ?_⟩
  rw [trvTreeAt_of_isEven ⟨hje, hj0⟩]
  have heq := hS.eq_asnchd_empty_irmrt (b := !(U, ∅)) hrt hnd hchdb
    fun x hx y hy hxy h ↦ hxy (eq_of_mem_trvChd hmω hx hy h)
  exact congrArg SLOTreeStructure.toM heq

end Tree

section Extensions

/-! ### The extensions of the trivial `uoci`'s of odd levels -/

theorem trvU_eq_of_forall (hU : ∀ P, P ∈ trvuoci n ↔ P = U) : trvU n = U := by
  have h : trvuoci n = {U} := by
    ext P
    rw [mem_singleton_iff, hU]
  change ⋃₀ trvuoci n = U
  rw [h, sUnion_singleton]

/-- The nodes of the trees of an array in `trvaotci_n` form a finite set -/
theorem finite_ndUnion_ran_of_mem_trvaotci (hn : n ∈ (ω : M)) (hA : A ∈ trvaotci n) :
    MemStructure.Finite (ndUnion (ran A)) := by
  rw [mem_trvaotci_iff] at hA
  obtain ⟨hAa, hAt⟩ := hA
  obtain ⟨hAf, hAdom, -⟩ := mem_aotci_iff.mp hAa
  have hran : MemStructure.Finite (ran A) :=
    (finite_of_mem_omega (succ_mem_omega hn)).of_isSurjectionFromTo
      ⟨⟨hAf, hAdom, subset_refl _⟩, rfl⟩
  have hres : IsSetRestrictedTo ndOf (ran A) := isSetRestrictedTo_of_definable _
  have heq : ndUnion (ran A) = ⋃₀ ran (ndOf ↾₀ ran A) := by
    ext z
    rw [mem_ndUnion_iff, mem_sUnion_iff]
    constructor
    · rintro ⟨T, hT, hz⟩
      exact ⟨ndOf T, (mem_ran_toSetRestrictedTo_iff hres).mpr ⟨T, hT, rfl⟩, hz⟩
    · rintro ⟨Y, hY, hz⟩
      obtain ⟨T, hT, rfl⟩ := (mem_ran_toSetRestrictedTo_iff hres).mp hY
      exact ⟨T, hT, hz⟩
  rw [heq]
  refine hran.image.sUnion fun Y hY ↦ ?_
  obtain ⟨T, hT, rfl⟩ := (mem_ran_toSetRestrictedTo_iff hres).mp hY
  rw [IsFunction.mem_ran_iff T hAf, hAdom] at hT
  obtain ⟨i, hi, rfl⟩ := hT
  exact (mem_finotci_iff.mp (mem_trvotci_iff.mp (hAt i hi)).left).right

/-- For odd `n`, in the level-`n` tree of an extension `Q` of a `uoci` `U` with empty signature, the
new root `(R, ∅)` has the children `trvChd (n - 1) R` -/
theorem aoc_val_eq_of_ext (hn : n ∈ (ω : M)) (hno : IsOdd n) (hY : IsSLOT Y)
    (hQ : Q ∈ stduoci n) (hsig : sig Q = cc ∅ !(n, !(R, ∅)))
    (haoc : aoc Q ﹫ n = asnchdOf (irmrtOf Y !(R, ∅)) !(R, ∅) B) :
    aoc Q ﹫ n = asnchdOf (irmrtOf Y !(R, ∅)) !(R, ∅) (trvChd (⋃₀ n) R) := by
  have hn0 : n ≠ ∅ := fun h ↦ not_isOdd_empty (h ▸ hno)
  obtain ⟨hmω, hmn, -⟩ := sUnion_mem_of_ne_empty hn hn0
  obtain ⟨hQu, hQstd⟩ := mem_stduoci_iff.mp hQ
  have hA := (mem_finaotci_iff.mp ((mem_uoci_iff_of_mem_omega hn).mp hQu).right.right.left).left
  have hT := val_mem_otci_of_mem_aotci hA (mem_succ_self n)
  have hX := isSLOT_of_mem_otci hT
  have hS : (SLOTreeStructure.ofM (aoc Q ﹫ n)).IsSLOTreeStructure := hX
  have hTr := hS.isTreeStructure
  have hb : !(R, ∅) ∈ ndOf (aoc Q ﹫ n) := by
    rw [haoc]
    change _ ∈ (((SLOTreeStructure.ofM Y).irmrt !(R, ∅)).asnchd !(R, ∅) B).nd
    rw [SLOTreeStructure.nd_asnchd, mem_union_iff, SLOTreeStructure.nd_irmrt]
    exact .inl (mem_insert _ _)
  have hchdB : chdOf (aoc Q ﹫ n) !(R, ∅) = B := by
    have hf := hTr.isFunction_chd
    rw [haoc] at hf ⊢
    refine SLOTreeStructure.chd_asnchd_val_self hf ?_
    change ((SLOTreeStructure.ofM Y).irmrt !(R, ∅)).ts.chd ﹫ _ = ∅
    rw [SLOTreeStructure.ts_irmrt,
      (show (SLOTreeStructure.ofM Y).IsSLOTreeStructure from hY).isTreeStructure.chd_irt_val_self]
  have hT' := hT
  rw [mem_otci_iff_of_ne_empty hn0] at hT'
  obtain ⟨-, hnodes, -⟩ := hT'
  have hcprops (c : M) (hc : c ∈ chdOf (aoc Q ﹫ n) !(R, ∅)) :
      ctp (uc c) = ct ∧ lbl c = !(R, ∅) := by
    have hcn := mem_ndOf_of_mem_chdOf hX hc
    have hnrt := not_mem_rtOf_of_mem_chdOf hX hc
    have hcs := (hnodes c hcn).left
    rw [stduociL_ciRec_restrict hmn] at hcs
    have hct : ctp (uc c) = ct := by
      rcases ctp_eq_ct_or_dct hmω (mem_stduoci_iff.mp hcs).left with h | h
      · exact h
      exfalso
      have hsc := (hQstd n (mem_succ_self n) c hcn).right.left ⟨h, fun h' ↦ hnrt h'.right⟩
      rw [hsig] at hsc
      by_cases hl : lbl c = ∅
      · have h0 := cc_val_self isFunction_empty !(n, !(R, ∅))
        rw [dom_empty] at h0
        rw [hl, h0, orderedPair_eq_orderedPair_iff] at hsc
        rw [hsc.right] at hc
        have hbn := hTr.mem_nd_of_mem_chd_val hc
        have hdep := hTr.dep_of_mem_chd _ hbn _ hc
        have hmem := mem_succ_self ((SLOTreeStructure.ofM (aoc Q ﹫ n)).ts.dep ﹫ !(R, ∅))
        rw [← hdep] at hmem
        exact notMem_self _ hmem
      · have hnd : lbl c ∉ dom (cc (∅ : M) !(n, !(R, ∅))) := by
          intro h'
          rw [dom_cc, dom_empty] at h'
          rcases mem_or_eq_of_mem_succ h' with h' | h'
          · simp at h'
          · exact hl h'
        rw [val_eq_empty_of_not_mem_dom hnd] at hsc
        exact orderedPair_ne_empty _ _ hsc
    refine ⟨hct, ?_⟩
    rw [((hQstd n (mem_succ_self n) c hcn).right.right hct).right hnrt,
      prtOf_eq_of_mem_chdOf hX hc]
  have h := chdOf_eq_trvChd hn hn0 hT hb (fun c hc ↦ (hcprops c hc).left)
    fun c hc ↦ (hcprops c hc).right
  rw [hchdB] at h
  rw [haoc, h]

/-- For odd `n`, the trivial `uoci` `{(0, A), (1, ∅), (2, dct)}` has finitely many extensions: an
extension is determined by the identifier `R` of its new root, and `R` is a function on `6` with
values in a finite set -/
theorem finite_trvChd (hn : n ∈ (ω : M)) (ih : ∀ m ∈ n, TrvGood m) (hno : IsOdd n)
    (hAt : A ∈ trvaotci n) :
    MemStructure.Finite (trvChd n (ciTriple A ∅ dct)) := by
  have hn0 : n ≠ ∅ := fun h ↦ not_isOdd_empty (h ▸ hno)
  obtain ⟨hmω, hmn, -⟩ := sUnion_mem_of_ne_empty hn hn0
  have ihm : ∀ k ∈ ⋃₀ n, TrvGood k := fun k hk ↦
    ih k ((ordinal_of_mem ordinal_omega hn).transitive _ hmn hk)
  obtain ⟨Um, hUm, -, -, -, hUmarr, -, -, hUmstd, -⟩ := ih _ hmn
  have hAm : aoc Um ∈ trvaotci (⋃₀ n) := (mem_trvuoci_iff.mp ((hUm Um).mpr rfl)).right.left
  obtain ⟨hAmf, hAmdom, hAmval⟩ := hUmarr
  have hAa := (mem_trvaotci_iff.mp hAt).left
  have hAf : IsFunction A := (mem_aotci_iff.mp hAa).left
  have hAdom : dom A = succ n := (mem_aotci_iff.mp hAa).right.left
  -- the extensions of `trvU k` for `k < n - 1`
  have hresX : IsSetRestrictedTo (fun k ↦ dom (trvChdP !(k, trvU k))) (⋃₀ n) :=
    isSetRestrictedTo_of_definable _
  have htrvChdP (k : M) : trvChdP !(k, trvU k) = trvChd k (trvU k) := by
    simp only [trvChdP, left_orderedPair, right_orderedPair]
  have hXfin : MemStructure.Finite (⋃₀ ran ((fun k ↦ dom (trvChdP !(k, trvU k))) ↾₀ ⋃₀ n)) := by
    refine (finite_of_mem_omega hmω).image.sUnion fun Y hY ↦ ?_
    obtain ⟨k, hk, rfl⟩ := (mem_ran_toSetRestrictedTo_iff hresX).mp hY
    have hkω := ordinal_omega.transitive _ hmω hk
    obtain ⟨Uk, hUk, -, -, -, -, hUkev, -, -, hUkfin⟩ := ihm k hk
    rw [htrvChdP, trvU_eq_of_forall hUk]
    refine MemStructure.Finite.dom ?_
      (IsRelation.subset (isRelation_sprod _ _) (comprehension_subset _ _))
    rcases isEven_or_isOdd hkω with he | ho
    · rw [trvChd_eq_empty_of_ctp_eq_ct (hUkev he)]
      exact finite_empty
    · exact hUkfin ho
  -- the finite set `W` of the values of the identifiers `R` of the new roots
  obtain ⟨W, hW⟩ : ∃ W : M, W = insert (aoc Um) (insert ∅ (insert ct (insert dct
      ((succ (⋃₀ n) ×ˢ ndUnion (ran (aoc Um))) ∪
        ⋃₀ ran ((fun k ↦ dom (trvChdP !(k, trvU k))) ↾₀ ⋃₀ n))))) := ⟨_, rfl⟩
  have hWfin : MemStructure.Finite W := by
    rw [hW]
    exact ((((finite_of_mem_omega (succ_mem_omega hmω)).sprod
      (finite_ndUnion_ran_of_mem_trvaotci hmω hAm)).union hXfin).insert _ |>.insert _
        |>.insert _ |>.insert _)
  -- the extensions of `U = {(0, A), (1, ∅), (2, dct)}`
  have hext {Q : M} (hQ : !(ciTriple A ∅ dct, Q) ∈ ciExt n) : ∃ R,
      R ∈ 𝒫 (((6 : ℕ) : M) ×ˢ W) ∧
      (∃ B, aoc Q ﹫ n = asnchdOf (irmrtOf (A ﹫ n) !(R, ∅)) !(R, ∅) B) ∧
      sig Q = cc ∅ !(n, !(R, ∅)) ∧ A ↾ n = aoc Q ↾ n := by
    obtain ⟨P', -, Q', -, hPQ, hPQext⟩ := mem_ciExt_iff.mp hQ
    rw [orderedPair_eq_orderedPair_iff] at hPQ
    obtain ⟨hP', hQ'⟩ := hPQ
    rw [← hP', ← hQ'] at hPQext
    obtain ⟨-, -, hrt, -⟩ := hPQext
    obtain ⟨hres, R, hR, B, hRtrv, haocQ, hsigQ⟩ := hrt ⟨sig_ciTriple _ _ _, hno⟩
    rw [stduociL_ciRec_restrict hmn] at hR
    rw [trvaotciL_ciRec_restrict hmn] at hRtrv
    rw [aoc_ciTriple] at hres haocQ
    refine ⟨R, ?_, ⟨B, haocQ⟩, hsigQ, hres⟩
    obtain ⟨hRarr, hRsig⟩ := hUmstd R hR hRtrv
    have hRaoc : aoc R = aoc Um := hRarr.eq hmω ihm ⟨hAmf, hAmdom, hAmval⟩
    have hRu := (mem_stduoci_iff.mp hR).left
    rw [mem_uoci_iff_of_mem_omega hmω] at hRu
    obtain ⟨hRf, hRdom, -, -, hRctp, -, -, hRucf⟩ := hRu
    have h3 {k : ℕ} (hk : 3 < k) (hkd : (k : M) ∈ dom R) : ((3 : ℕ) : M) ∈ dom R := by
      rcases hRdom with h | h | h <;> rw [h] at hkd ⊢ <;>
        rw [natCast_mem_natCast_iff] at hkd ⊢ <;> omega
    rw [mem_powerset_iff]
    intro z hz
    obtain ⟨i, rfl⟩ := hRf.exists_val hz
    have hi : i ∈ dom R := (MemStructure.mem_dom_iff R i).mpr ⟨_, hz⟩
    rw [pair_mem_sprod_iff]
    refine ⟨mem_natCast_six_of_mem_dom hRdom hi, ?_⟩
    rw [hW]
    simp only [mem_insert_iff, mem_union_iff]
    obtain ⟨k, hk, rfl⟩ := exists_eq_natCast_of_mem_natCast (mem_natCast_six_of_mem_dom hRdom hi)
    rcases k with _ | _ | _ | _ | _ | _ | k
    · -- the array
      exact .inl hRaoc
    · -- the signature
      exact .inr (.inl hRsig)
    · -- the continuity type
      rcases hRctp with h | h
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl h)))
    · -- the level and the node of the unique continuity failure
      obtain ⟨⟨l, d, hld⟩, hlvl, hdcn, -⟩ := hRucf hi
      have hl : ucflvl R = l := by rw [ucflvl, hld, lvl_orderedPair]
      have hd : ucfdcn R = d := by rw [ucfdcn, hld, dcn_orderedPair]
      rw [hl] at hlvl hdcn
      rw [hd, hRaoc] at hdcn
      refine .inr (.inr (.inr (.inr (.inl ?_))))
      change ucflvldcn R ∈ _
      rw [hld]
      rw [pair_mem_sprod_iff]
      refine ⟨hlvl, ?_⟩
      rw [mem_ndUnion_iff]
      exact ⟨_, (IsFunction.mem_ran_iff _ hAmf).mpr ⟨l, by rwa [hAmdom], rfl⟩, hdcn⟩
    · -- the direction
      obtain ⟨-, -, -, -, hdr, -⟩ := hRucf (h3 (by omega) hi)
      rcases hdr with h | h
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl h)))
    · -- the extension of the node of the unique continuity failure
      have h6 : dom R = ((6 : ℕ) : M) := by
        rcases hRdom with h | h | h <;> rw [h] at hi
        · rw [natCast_mem_natCast_iff] at hi
          omega
        · rw [natCast_mem_natCast_iff] at hi
          omega
        · exact h
      obtain ⟨⟨l, d, hld⟩, hlvl, hdcn, -, -, -, hex⟩ := hRucf (h3 (by omega) hi)
      have hl : ucflvl R = l := by rw [ucflvl, hld, lvl_orderedPair]
      have hd : ucfdcn R = d := by rw [ucfdcn, hld, dcn_orderedPair]
      obtain ⟨h0, hexR⟩ := hex h6
      rw [hl] at hlvl hdcn h0 hexR
      rw [hd, hRaoc] at hdcn
      rw [hd] at hexR
      have hk := sUnion_mem_of_mem_succ hmω hlvl h0
      rw [extL_ciRec_restrict hk] at hexR
      have hddct := (mem_ciExt_props hexR).right.right.left
      -- the node is the root `(r, ∅)` of the trivial tree, with `r = trvU (l - 1)`
      obtain ⟨r, hr, hrtree⟩ := hAmval l hlvl
      rw [hrtree] at hdcn
      have hdr : d = !(r, ∅) := by
        have hd' := ndOf_trvTreeAt_subset hdcn
        rw [mem_insert_iff] at hd'
        rcases hd' with h | h
        · exact h
        · obtain ⟨q, rfl, hq⟩ := mem_trvChd_iff.mp h
          rw [uc_orderedPair, (mem_ciExt_props hq).right.right.right] at hddct
          exact (ct_ne_dct hddct).elim
      have hl0 : l ≠ ∅ := fun h ↦ by simp [h] at h0
      have hrU : r = trvU (⋃₀ l) := by
        rcases hr with ⟨h, -⟩ | ⟨-, h⟩
        · exact (hl0 h).elim
        obtain ⟨Uk, hUk, -⟩ := ihm _ hk
        rw [trvU_eq_of_forall hUk]
        exact (hUk r).mp h
      rw [hdr, uc_orderedPair, hrU] at hexR
      refine .inr (.inr (.inr (.inr (.inr ?_))))
      rw [mem_sUnion_iff]
      refine ⟨_, (mem_ran_toSetRestrictedTo_iff hresX).mpr ⟨_, hk, rfl⟩, ?_⟩
      rw [htrvChdP, MemStructure.mem_dom_iff]
      exact ⟨_, mem_trvChd_iff.mpr ⟨_, rfl, hexR⟩⟩
    · omega
  -- an extension is determined by its signature
  have hY : IsSLOT (A ﹫ n) := isSLOT_of_mem_otci (val_mem_otci_of_mem_aotci hAa (mem_succ_self n))
  have h0 (a : M) : cc (∅ : M) a ﹫ ∅ = a := by
    have h := cc_val_self isFunction_empty a
    rwa [dom_empty] at h
  have hdet {Q Q' : M} (hQ : !(ciTriple A ∅ dct, Q) ∈ ciExt n)
      (hQ' : !(ciTriple A ∅ dct, Q') ∈ ciExt n) (hsig : sig Q = sig Q') : Q = Q' := by
    obtain ⟨R, -, ⟨B, haocQ⟩, hsigQ, hres⟩ := hext hQ
    obtain ⟨R', -, ⟨B', haocQ'⟩, hsigQ', hres'⟩ := hext hQ'
    have hRR : R = R' := by
      have h := congrArg (· ﹫ (∅ : M)) (hsigQ.symm.trans (hsig.trans hsigQ'))
      simp only [h0, orderedPair_eq_orderedPair_iff] at h
      exact h.right.left
    subst hRR
    obtain ⟨-, hQs, -, hQct⟩ := mem_ciExt_props hQ
    obtain ⟨-, hQs', -, hQct'⟩ := mem_ciExt_props hQ'
    have hQn := aoc_val_eq_of_ext hn hno hY hQs hsigQ haocQ
    have hQn' := aoc_val_eq_of_ext hn hno hY hQs' hsigQ' haocQ'
    have harr {P : M} (hP : P ∈ stduoci n) : IsFunction (aoc P) ∧ dom (aoc P) = succ n := by
      have hPu := (mem_stduoci_iff.mp hP).left
      rw [mem_uoci_iff_of_mem_omega hn] at hPu
      obtain ⟨hf, hdom, -⟩ := mem_aotci_iff.mp (mem_finaotci_iff.mp hPu.right.right.left).left
      exact ⟨hf, hdom⟩
    refine eq_of_aoc_eq_of_ctp_eq_ct hn hQs hQs' hQct hQct' ?_
    refine (harr hQs).left.ext (harr hQs').left (by rw [(harr hQs).right, (harr hQs').right])
      fun i hi ↦ ?_
    rw [(harr hQs).right] at hi
    rcases mem_or_eq_of_mem_succ hi with hi | rfl
    · have hdA : i ∈ dom A := by
        rw [hAdom]
        exact mem_succ_of_mem hi
      have hdQ : i ∈ dom (aoc Q) := by
        rw [(harr hQs).right]
        exact mem_succ_of_mem hi
      have hdQ' : i ∈ dom (aoc Q') := by
        rw [(harr hQs').right]
        exact mem_succ_of_mem hi
      have h₁ := congrArg (· ﹫ i) hres
      have h₂ := congrArg (· ﹫ i) hres'
      rw [val_restrict _ hAf hi hdA, val_restrict _ (harr hQs).left hi hdQ] at h₁
      rw [val_restrict _ hAf hi hdA, val_restrict _ (harr hQs').left hi hdQ'] at h₂
      rw [← h₁, ← h₂]
    · rw [hQn, hQn']
  -- an injection into the finite set of the signatures
  have hresf : IsSetRestrictedTo (fun x ↦ sig (left x)) (trvChd n (ciTriple A ∅ dct)) :=
    isSetRestrictedTo_of_definable _
  have hresS : IsSetRestrictedTo (fun R ↦ cc ∅ !(n, !(R, ∅))) (𝒫 (((6 : ℕ) : M) ×ˢ W)) :=
    isSetRestrictedTo_of_definable _
  have hSfin := (((finite_of_mem_omega (natCast_mem_omega 6)).sprod hWfin).powerset).image
    (G := fun R ↦ cc ∅ !(n, !(R, ∅)))
  refine hSfin.of_isInjectionFromTo
    (isInjectionFromTo_toSetRestrictedTo hresf (fun x hx ↦ ?_) fun x hx y hy hxy ↦ ?_)
  · obtain ⟨Q, rfl, hQ⟩ := mem_trvChd_iff.mp hx
    obtain ⟨R, hR6, -, hsigQ, -⟩ := hext hQ
    rw [left_orderedPair, hsigQ]
    exact (mem_ran_toSetRestrictedTo_iff hresS).mpr ⟨R, hR6, rfl⟩
  · obtain ⟨Q, rfl, hQ⟩ := mem_trvChd_iff.mp hx
    obtain ⟨Q', rfl, hQ'⟩ := mem_trvChd_iff.mp hy
    rw [left_orderedPair, left_orderedPair] at hxy
    rw [hdet hQ hQ' hxy]

end Extensions

section Induction

/-- The step of the induction: `trvuoci_n` has a unique element if every level below does -/
theorem trvGood_of_forall (hn : n ∈ (ω : M)) (ih : ∀ m ∈ n, TrvGood m) : TrvGood n := by
  -- the array of trivial trees
  obtain ⟨A, hA⟩ : ∃ A, IsTrvArray n A := by
    by_cases hn0 : n = ∅
    · subst hn0
      refine ⟨cc ∅ (trvTreeAt ∅ otci0Uc), isFunction_empty.cc _, by rw [dom_cc, dom_empty],
        fun j hj ↦ ⟨otci0Uc, ?_, ?_⟩⟩ <;> rw [mem_succ_iff] at hj <;>
        rcases hj with rfl | hj
      · exact .inl ⟨rfl, rfl⟩
      · simp at hj
      · have h := cc_val_self isFunction_empty (trvTreeAt ∅ (otci0Uc : M))
        rwa [dom_empty] at h
      · simp at hj
    obtain ⟨-, hmn, hnm⟩ := sUnion_mem_of_ne_empty hn hn0
    obtain ⟨U, hU, -, -, -, ⟨hAf, hAdom, hAval⟩, -⟩ := ih _ hmn
    have hAdom' : dom (aoc U) = n := by rw [hAdom, ← hnm]
    refine ⟨cc (aoc U) (trvTreeAt n U), hAf.cc _, by rw [dom_cc, hAdom'], fun j hj ↦ ?_⟩
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
    exact trvTreeAt_mem_trvotci (mem_omega_of_mem_succ hn hj) (forall_mem_of_mem_succ hn ih hj) hr
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
    refine ⟨⟨hRf, hRdom, fun j hj ↦ ?_⟩, ?_⟩
    · exact exists_eq_trvTreeAt (mem_omega_of_mem_succ hn hj) (forall_mem_of_mem_succ hn ih hj)
        (hRtrv j hj) fun p hp ↦ ⟨(hRstd j hj p hp).left, (hRstd j hj p hp).right.right⟩
    -- the signature is empty: in a trivial array, only the roots of even levels are discontinuous
    rw [mem_uoci_iff_of_mem_omega hn] at hRuoci
    obtain ⟨-, -, -, ⟨hsigf, -, -, hsig⟩, -⟩ := hRuoci
    refine hsigf.isRelation.eq_empty_of_dom_eq_empty ?_
    ext i
    refine ⟨fun hi ↦ ?_, by simp⟩
    exfalso
    have hnot := not_isEven_and_mem_rtOf_of_sigCond hRaotci (hsig i hi)
    have hnd := mem_ndOf_of_sigCond hn hRaotci (hsig i hi)
    obtain ⟨-, hlvl, -, -, hctp⟩ := hsig i hi
    obtain ⟨-, hev, hodd⟩ := mem_trvotci_iff.mp (hRtrv _ hlvl)
    rcases isEven_or_isOdd (mem_omega_of_mem_succ hn hlvl) with he | ho
    · exact hnot ⟨he, (hev he _ hnd).mp hctp⟩
    · exact ct_ne_dct ((hodd ho _ hnd).symm.trans hctp)
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
    have hiω := mem_omega_of_mem_succ hn hi
    obtain ⟨hrf, hrdom, -, hrodd⟩ := hr.props hiω (forall_mem_of_mem_succ hn ih hi)
    rw [aoc_ciTriple, htree] at hp ⊢
    have hp' := ndOf_trvTreeAt_subset hp
    rw [mem_insert_iff] at hp'
    rcases hp' with rfl | hp'
    · -- the root
      have hrt : !(r, ∅) ∈ rtOf (trvTreeAt i r) := by
        by_cases hie : IsEven i ∧ i ≠ ∅
        · rw [rtOf_trvTreeAt_of_isEven hie hrf hrdom]
          exact mem_singleton _
        · rw [trvTreeAt_of_not_isEven hie, rtOf_trvTree]
          exact mem_singleton _
      rw [lbl_orderedPair, uc_orderedPair]
      refine ⟨fun _ ↦ rfl, fun ⟨hdct, hne⟩ ↦ ?_, fun _ ↦ ⟨fun _ ↦ rfl, fun h ↦ (h hrt).elim⟩⟩
      exfalso
      rcases isEven_or_isOdd hiω with h | h
      · exact hne ⟨h, hrt⟩
      · exact ct_ne_dct ((hrodd h).symm.trans hdct)
    -- a child of the root
    obtain ⟨q, rfl, hq⟩ := mem_trvChd_iff.mp hp'
    have hqct := (mem_ciExt_props hq).right.right.right
    have hie : IsEven i ∧ i ≠ ∅ := by
      by_contra hie
      rw [trvTreeAt_of_not_isEven hie, ndOf_trvTree, mem_singleton_iff] at hp
      exact not_mem_trvChd (hp ▸ hp')
    obtain ⟨hmω, -, -⟩ := sUnion_mem_of_ne_empty hiω hie.right
    have hX := isSLOT_trvTreeAt_of_isEven hie hmω hrf hrdom
    have hc : !(q, !(r, ∅)) ∈ chdOf (trvTreeAt i r) !(r, ∅) := by
      rw [chdOf_trvTreeAt_root hie hmω hrf hrdom]
      exact hp'
    have hnrt := not_mem_rtOf_of_mem_chdOf hX hc
    rw [uc_orderedPair, lbl_orderedPair, hqct, prtOf_eq_of_mem_chdOf hX hc]
    exact ⟨fun h ↦ (hnrt h.right).elim, fun h ↦ (ct_ne_dct h.left).elim,
      fun _ ↦ ⟨fun h ↦ (hnrt h).elim, fun _ ↦ rfl⟩⟩
  have hUtrv : ciTriple A ∅ c ∈ trvuoci n := by
    rw [mem_trvuoci_iff, mem_stduoci_iff]
    refine ⟨⟨hUuoci, hUstd⟩, by rwa [aoc_ciTriple], fun h ↦ ?_, fun h ↦ ?_⟩ <;> rw [ctp_ciTriple]
    · exact hcev h
    · exact hcodd h
  refine ⟨ciTriple A ∅ c, fun P ↦ ⟨fun hP ↦ ?_, ?_⟩, isFunction_ciTriple _ _ _, dom_ciTriple _ _ _,
    sig_ciTriple _ _ _, by rw [aoc_ciTriple]; exact ⟨hAf, hAdom, hAval⟩,
    fun h ↦ by rw [ctp_ciTriple]; exact hcev h, fun h ↦ by rw [ctp_ciTriple]; exact hcodd h,
    hstd, fun hno ↦ ?_⟩
  rotate_left
  · rintro rfl
    exact hUtrv
  · rw [hcodd hno]
    exact finite_trvChd hn ih hno hAtrvaotci
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
  ext P
  rw [mem_singleton_iff, hU, trvU_eq_of_forall hU]

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

end Induction

end FirstOrder.Language.MemStructure
