/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.HereditarilyFinite
import Astlib.Combinatorics.ClassificationIdentifier.Trivial
/-!
# Existence of the trivial classification identifiers

For `n ∈ ω`, by induction on `n`:

* `trvuoci_n` is nonempty (`exists_mem_trvuoci`) and finite (`finite_trvuoci`);
* the trivial `otci_n` with the standard labels is the empty tree for odd `n`, the single node
  `(otci0Uc, ∅)` for `n = 0`, and for even `n > 0` the root `(V, ∅)`, `V` the trivial `uoci` of the
  odd level `n - 1`, with the childless children `(q, (V, ∅))` for the extensions
  `(V, q) ∈ ext_{n-1}` (`asnchdOf_trvTree_mem_trvotci`); the trivial arrays with the standard labels
  give the trivial `uoci`'s `{(0, A), (1, ∅), (2, dct)}` for odd `n` and `lfTrvUoci A` for even `n`
  (`mem_trvuoci_of_mem_trvaotci`).

The trivial `otci_n` is finite since the extensions of the trivial `uoci` of the odd level `n - 1`
are determined by the root identifiers in `trvuoci_{n-2}` of their new level-`(n-1)` trees
(`finite_trvExtFib_of_isOdd`), and for even `n` the elements of `trvuoci_n` take finitely many
values (`finite_trvuoci_of_isEven`).

The unique objects get names:

* `trvAotci n`, the common array of the elements of `trvuoci_n`, a trivial array
  (`trvAotci_mem_trvaotci`);
* `trvOtci n = trvAotci n ﹫ n`, the unique trivial `otci_n` with the standard labels at even
  levels (`trvOtci_mem_trvotci`, `eq_trvOtci`), with `trvAotci n ﹫ i = trvOtci i`
  (`trvAotci_val`);
* `trvUoci n` for odd `n`, with `trvuoci_n = {trvUoci n}` (`trvuoci_eq_singleton`) and
  `trvUoci n = {(0, trvAotci n), (1, ∅), (2, dct)}` (`trvUoci_eq`).

For even `n`, `trvuoci_n` is not a singleton in general; `lfTrvUoci (trvAotci n)` is an element
(`lfTrvUoci_mem_trvuoci`).
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M] {A B b c m n p q r C R T U V W : M}

section Star

/-! ### A root with childless children -/

/-- The nodes of `C` are new childless nodes with distinct keys -/
def IsNewChd (b C : M) : Prop :=
  (∀ x ∈ C, IsOrderedPair x ∧ IsFunction (left x) ∧ dom (left x) ∈ (ω : M) \ {∅}) ∧ b ∉ C ∧
    ∀ x ∈ C, ∀ y ∈ C, x ≠ y → left x ﹫ ∅ ≠ left y ﹫ ∅

theorem ndOf_asnchdOf_trvTree : ndOf (asnchdOf (trvTree V) !(V, ∅) C) = insert !(V, ∅) C := by
  change (((SLOTreeStructure.ofM (trvTree V))).asnchd !(V, ∅) C).nd = _
  rw [SLOTreeStructure.nd_asnchd, insert_eq]
  change ndOf (trvTree V) ∪ C = _
  rw [ndOf_trvTree]

theorem disjoint_ndOf_trvTree (hbC : !(V, ∅) ∉ C) :
    C ∩ (SLOTreeStructure.ofM (trvTree V)).nd = ∅ := by
  change C ∩ ndOf (trvTree V) = ∅
  rw [ndOf_trvTree, empty_iff]
  intro x hx
  rw [mem_inter_iff, mem_singleton_iff] at hx
  exact hbC (hx.right ▸ hx.left)

theorem mem_nd_ofM_trvTree : !(V, ∅) ∈ (SLOTreeStructure.ofM (trvTree V)).nd := by
  change !(V, ∅) ∈ ndOf (trvTree V)
  rw [ndOf_trvTree]
  exact mem_singleton _

variable (hV : IsFunction V) (hVd : dom V ∈ (ω : M) \ {∅})
include hV hVd

theorem isSLOT_trvTree' : IsSLOT (trvTree V) :=
  SLOTreeStructure.IsSLOTreeStructure.irmrt SLOTreeStructure.isSLOTreeStructure_empty
    ⟨_, _, rfl⟩ (by simp [SLOTreeStructure.nd_empty]) (by rwa [left_orderedPair])
    (by rwa [left_orderedPair])

theorem rtOf_asnchdOf_trvTree (hbC : !(V, ∅) ∉ C) :
    rtOf (asnchdOf (trvTree V) !(V, ∅) C) = {!(V, ∅)} := by
  have hS₀ : (SLOTreeStructure.ofM (trvTree V)).IsSLOTreeStructure := isSLOT_trvTree' hV hVd
  change (((SLOTreeStructure.ofM (trvTree V))).asnchd !(V, ∅) C).rt = _
  rw [hS₀.rt_asnchd (disjoint_ndOf_trvTree hbC)]
  exact rtOf_trvTree V

theorem chdOf_asnchdOf_trvTree_of_mem (hbC : !(V, ∅) ∉ C) (hc : c ∈ C) :
    chdOf (asnchdOf (trvTree V) !(V, ∅) C) c = ∅ :=
  (show (SLOTreeStructure.ofM (trvTree V)).IsSLOTreeStructure from
    isSLOT_trvTree' hV hVd).chd_asnchd_val_of_mem_new mem_nd_ofM_trvTree
    (disjoint_ndOf_trvTree hbC) hc

theorem isSLOT_asnchdOf_trvTree (hC : IsNewChd !(V, ∅) C) :
    IsSLOT (asnchdOf (trvTree V) !(V, ∅) C) :=
  (show (SLOTreeStructure.ofM (trvTree V)).IsSLOTreeStructure from
    isSLOT_trvTree' hV hVd).asnchd mem_nd_ofM_trvTree (chdOf_trvTree V _) hC.left
    (disjoint_ndOf_trvTree hC.right.left) hC.right.right

theorem chdOf_asnchdOf_trvTree_self (hC : IsNewChd !(V, ∅) C) :
    chdOf (asnchdOf (trvTree V) !(V, ∅) C) !(V, ∅) = C :=
  SLOTreeStructure.chd_asnchd_val_self
    (show (SLOTreeStructure.ofM (asnchdOf (trvTree V) !(V, ∅) C)).IsSLOTreeStructure from
      isSLOT_asnchdOf_trvTree hV hVd hC).isTreeStructure.isFunction_chd
    (chdOf_trvTree V _)

end Star

section Los

/-- The linearly ordered set of the children of `p` with the key of the child `c` -/
theorem mem_losSet_chdlosOf_iff (hT : IsSLOT T) (hp : p ∈ ndOf T) (hc : c ∈ chdOf T p) (x : M) :
    x ∈ losSet (chdlosOf T p ﹫ (left c ﹫ ∅)) ↔ x ∈ chdOf T p ∧ left x ﹫ ∅ = left c ﹫ ∅ := by
  have hS : (SLOTreeStructure.ofM T).IsSLOTreeStructure := hT
  have hTs := hS.isTreeStructure
  have hne : (SLOTreeStructure.ofM T).chd ﹫ p ≠ ∅ := by
    rw [ne_empty_iff]
    exact ⟨c, hc⟩
  have hX : (SLOTreeStructure.ofM T).chd ﹫ p ∈ (SLOTreeStructure.ofM T).sblptn := by
    rw [TreeStructure.mem_sblptn_iff, hTs.isFunction_chd.mem_ran_iff, hTs.dom_chd]
    exact ⟨.inr ⟨p, hp, rfl⟩, hne⟩
  have hD : left c ﹫ ∅ ∈ dom ((SLOTreeStructure.ofM T).losfn ﹫
      ((SLOTreeStructure.ofM T).chd ﹫ p)) :=
    (hS.mem_dom_losfn_val_iff hX _).mpr ⟨c, hc, rfl⟩
  rw [chdlosOf, hS.chdlos_val (hS.mem_dom_chdlos_iff.mpr ⟨hp, hne⟩)]
  exact hS.mem_losSet_iff hX hD x

/-- The linearly ordered set of the children of `p` with the key of the child `c` is a linearly
ordered set -/
theorem isStrictLinearOrderedSet_chdlosOf (hT : IsSLOT T) (hp : p ∈ ndOf T)
    (hc : c ∈ chdOf T p) : IsStrictLinearOrderedSet (chdlosOf T p ﹫ (left c ﹫ ∅)) := by
  have hS : (SLOTreeStructure.ofM T).IsSLOTreeStructure := hT
  have hTs := hS.isTreeStructure
  have hne : (SLOTreeStructure.ofM T).chd ﹫ p ≠ ∅ := by
    rw [ne_empty_iff]
    exact ⟨c, hc⟩
  have hX : (SLOTreeStructure.ofM T).chd ﹫ p ∈ (SLOTreeStructure.ofM T).sblptn := by
    rw [TreeStructure.mem_sblptn_iff, hTs.isFunction_chd.mem_ran_iff, hTs.dom_chd]
    exact ⟨.inr ⟨p, hp, rfl⟩, hne⟩
  have hD : left c ﹫ ∅ ∈ dom ((SLOTreeStructure.ofM T).losfn ﹫
      ((SLOTreeStructure.ofM T).chd ﹫ p)) :=
    (hS.mem_dom_losfn_val_iff hX _).mpr ⟨c, hc, rfl⟩
  rw [chdlosOf, hS.chdlos_val (hS.mem_dom_chdlos_iff.mpr ⟨hp, hne⟩)]
  exact hS.isStrictLinearOrderedSet hX hD

/-- The only element of a linearly ordered set is its least element -/
theorem isLeastLos_of_losSet_eq_singleton (hB : IsStrictLinearOrderedSet B)
    (h : ∀ x, x ∈ losSet B ↔ x = r) : IsLeastLos B r :=
  ⟨(h r).mpr rfl, fun y hy ↦ by
    rw [(h y).mp hy]
    exact hB.isStrictLinearOrder.irrefl r⟩

end Los

section Fiber

/-! ### The extensions of the trivial `uoci` of an odd level -/

/-- The extensions `q`, `(U, q) ∈ ext_j`, of the trivial `uoci`'s `U ∈ trvuoci_j` of odd levels
`j`; empty for even `j` -/
noncomputable def trvExtFib : ClassFunction M := fun j ↦
  stduoci j ∩₀ fun q ↦ IsOdd j ∧ ∃ U ∈ trvuoci j, !(U, q) ∈ ciExt j

instance : (trvExtFib : ClassFunction M).Definable Set.univ :=
  .of_mem_iff (R := fun j q ↦ ∃ S X E, S = stduoci j ∧ X = trvuoci j ∧ E = ciExt j ∧
    q ∈ S ∧ IsOdd j ∧ ∃ U ∈ X, !(U, q) ∈ E) fun j q ↦ by simp [trvExtFib, mem_comprehension_iff]

theorem mem_trvExtFib_iff {j : M} :
    q ∈ trvExtFib j ↔ q ∈ stduoci j ∧ IsOdd j ∧ ∃ U ∈ trvuoci j, !(U, q) ∈ ciExt j := by
  rw [trvExtFib, mem_comprehension_iff]

/-- For odd `j ∈ ω` and `V ∈ trvuoci_j`, the fiber consists of the extensions of `V` -/
theorem mem_trvExtFib_iff_of_mem_trvuoci {j : M} (hj : j ∈ (ω : M)) (hjo : IsOdd j)
    (hV : V ∈ trvuoci j) : q ∈ trvExtFib j ↔ !(V, q) ∈ ciExt j := by
  rw [mem_trvExtFib_iff]
  constructor
  · rintro ⟨-, -, U, hU, hq⟩
    rwa [eq_of_mem_trvuoci_of_isOdd hj hjo hV hU]
  · intro hq
    exact ⟨(mem_ciExt_props hq).right.left, hjo, V, hV, hq⟩

end Fiber

section OddExt

/-! ### The extensions of the trivial `uoci` of an odd level -/

/-- The domain of a `uoci` is a nonzero natural number -/
theorem dom_mem_of_mem_uoci (hn : n ∈ (ω : M)) (hU : U ∈ uoci n) : dom U ∈ (ω : M) \ {∅} := by
  rw [mem_uoci_iff_of_mem_omega hn] at hU
  have h (k : ℕ) (hk : k ≠ 0) : ((k : ℕ) : M) ∈ (ω : M) \ {∅} := by
    rw [mem_sdiff_iff, mem_singleton_iff, ← natCast_zero, natCast_inj]
    exact ⟨natCast_mem_omega k, hk⟩
  rcases hU.right.left with h' | h' | h' <;> rw [h'] <;> exact h _ (by omega)

/-- A child of a node is not the node itself -/
theorem not_mem_chdOf_self (hT : IsSLOT T) (hp : p ∈ ndOf T) : p ∉ chdOf T p := by
  have hTs := (show (SLOTreeStructure.ofM T).IsSLOTreeStructure from hT).isTreeStructure
  intro h
  have h' := hTs.dep_of_mem_chd p hp p h
  have hmem := mem_succ_self ((SLOTreeStructure.ofM T).ts.dep ﹫ p)
  rw [← h'] at hmem
  exact notMem_self _ hmem

/-- An extension `q` of the trivial `uoci` `U` of an odd level `m`: its level-`m` tree is the new
root `(R, ∅)` for some `R ∈ trvuoci_{m-1}`, together with the children `(q', (R, ∅))` for the
extensions `(R, q') ∈ ext_{m-1}`, and its signature is `{(0, (m, (R, ∅)))}` -/
theorem exists_of_mem_ciExt_of_mem_trvuoci (hm : m ∈ (ω : M)) (hmo : IsOdd m)
    (hU : U ∈ trvuoci m) (hq : !(U, q) ∈ ciExt m) : ∃ R, R ∈ trvuoci (⋃₀ m) ∧
      q = ciTriple (aoc q) (cc ∅ !(m, !(R, ∅))) ct ∧
      IsFunction (aoc q) ∧ dom (aoc q) = succ m ∧ (∀ i ∈ m, aoc q ﹫ i = aoc U ﹫ i) ∧
      rtOf (aoc q ﹫ m) = {!(R, ∅)} ∧
      aoc q ﹫ m = asnchdOf (trvTree R) !(R, ∅) (chdOf (aoc q ﹫ m) !(R, ∅)) ∧
      ∀ x, x ∈ chdOf (aoc q ﹫ m) !(R, ∅) ↔
        ∃ q', x = !(q', !(R, ∅)) ∧ !(R, q') ∈ ciExt (⋃₀ m) := by
  have hm0 : m ≠ ∅ := fun h ↦ not_isOdd_empty (h ▸ hmo)
  obtain ⟨hkω, hkm, -⟩ := sUnion_mem_of_ne_empty hm hm0
  obtain ⟨-, hqs, -, hqc⟩ := mem_ciExt_props hq
  obtain ⟨P', -, Q', -, hPQ, hext⟩ := mem_ciExt_iff.mp hq
  rw [orderedPair_eq_orderedPair_iff] at hPQ
  obtain ⟨rfl, rfl⟩ := hPQ
  obtain ⟨hres, R, hRs, A, -, hqm, hsigq⟩ := hext.right.right.left
    ⟨sig_eq_empty_of_mem_trvuoci hm hU, hmo⟩
  rw [stduociL_ciRec_restrict hkm] at hRs
  -- the level-`m` tree of `U` is empty
  have hUm := (mem_trvaotci_iff.mp (mem_trvuoci_iff.mp hU).right.left).right m (mem_succ_self m)
  rw [eq_emptySLOT_of_ndOf_eq_empty
    (isSLOT_of_mem_otci (mem_finotci_iff.mp (mem_trvotci_iff.mp hUm).left).left)
    ((mem_trvotci_iff.mp hUm).right.right hmo)] at hqm
  change aoc q ﹫ m = asnchdOf (trvTree R) !(R, ∅) A at hqm
  -- the array of `q`
  have hqu := mem_stduoci_iff.mp hqs
  have hqu' := hqu.left
  rw [mem_uoci_iff_of_mem_omega hm] at hqu'
  obtain ⟨hqf, -, hqfa, -⟩ := hqu'
  have hqA := (mem_finaotci_iff.mp hqfa).left
  obtain ⟨hAf, hAdom, -⟩ := mem_aotci_iff.mp hqA
  have hTo : aoc q ﹫ m ∈ otci m := val_mem_otci_of_mem_aotci hqA (mem_succ_self m)
  have hTs := isSLOT_of_mem_otci hTo
  have hRu := (mem_stduoci_iff.mp hRs).left
  have hRf : IsFunction R := (by
    rw [mem_uoci_iff_of_mem_omega hkω] at hRu
    exact hRu.left)
  have hRd := dom_mem_of_mem_uoci hkω hRu
  have hb : !(R, ∅) ∈ ndOf (aoc q ﹫ m) := by
    rw [hqm]
    exact SLOTreeStructure.nd_subset_nd_asnchd _ _ _ mem_nd_ofM_trvTree
  have hchdA : chdOf (aoc q ﹫ m) !(R, ∅) = A := by
    have hf := (show (SLOTreeStructure.ofM (aoc q ﹫ m)).IsSLOTreeStructure from
      hTs).isTreeStructure.isFunction_chd
    rw [hqm] at hf ⊢
    exact SLOTreeStructure.chd_asnchd_val_self hf (chdOf_trvTree R _)
  have hbA : !(R, ∅) ∉ A := hchdA ▸ not_mem_chdOf_self hTs hb
  have hrt : rtOf (aoc q ﹫ m) = {!(R, ∅)} := by
    rw [hqm]
    exact rtOf_asnchdOf_trvTree hRf hRd hbA
  -- `R` is trivial
  have hTo' := hTo
  rw [mem_otci_iff_of_ne_empty hm0] at hTo'
  obtain ⟨-, hnodes, hroot, -⟩ := hTo'
  have hRt := hroot !(R, ∅) (by rw [hrt]; exact mem_singleton _)
  rw [trvuociL_ciRec_restrict hkm, uc_orderedPair] at hRt
  -- the children are continuous, with label `(R, ∅)`
  have hct : ∀ c ∈ chdOf (aoc q ﹫ m) !(R, ∅), ctp (uc c) = ct := by
    intro c hc
    have hcn := mem_ndOf_of_mem_chdOf hTs hc
    have hcs := (hnodes c hcn).left
    rw [stduociL_ciRec_restrict hkm] at hcs
    rcases ctp_eq_ct_or_dct hkω (mem_stduoci_iff.mp hcs).left with h | h
    · exact h
    exfalso
    have hsig := (hqu.right m (mem_succ_self m) c hcn).right.left
      ⟨h, fun h' ↦ (isOdd_iff_not_isEven hm).mp hmo h'.left⟩
    rw [hsigq] at hsig
    by_cases hl : lbl c = dom (∅ : M)
    · rw [hl, cc_val_self isFunction_empty, orderedPair_eq_orderedPair_iff] at hsig
      rw [hchdA] at hc
      exact hbA (hsig.right ▸ hc)
    · rw [val_eq_empty_of_not_mem_dom (by
        rw [dom_cc, mem_succ_iff, dom_empty]
        rw [dom_empty] at hl
        simpa using hl)] at hsig
      exact orderedPair_ne_empty _ _ hsig
  have hlbl : ∀ c ∈ chdOf (aoc q ﹫ m) !(R, ∅), lbl c = !(R, ∅) := by
    intro c hc
    rw [((hqu.right m (mem_succ_self m) c (mem_ndOf_of_mem_chdOf hTs hc)).right.right
      (hct c hc)).right (not_mem_rtOf_of_mem_chdOf hTs hc), prtOf_eq_of_mem_chdOf hTs hc]
  refine ⟨R, hRt, ?_, hAf, hAdom, fun i hi ↦ ?_, hrt, by rw [hchdA]; exact hqm,
    mem_chdOf_iff_of_ext hm hm0 hTo hb hct hlbl⟩
  · have h := eq_ciTriple hqf (dom_eq_three_of_ctp_eq_ct hm hqu.left hqc)
    rwa [hsigq, hqc] at h
  · have hiU : i ∈ dom (aoc U) := by
      rw [(mem_aotci_iff.mp (mem_trvaotci_iff.mp
        (mem_trvuoci_iff.mp hU).right.left).left).right.left]
      exact mem_succ_of_mem hi
    rw [← val_restrict _ hAf hi (by rw [hAdom]; exact mem_succ_of_mem hi), ← hres,
      val_restrict _ (mem_aotci_iff.mp (mem_trvaotci_iff.mp
        (mem_trvuoci_iff.mp hU).right.left).left).left hi hiU]

/-- For odd `m`, the extensions of the trivial `uoci` of level `m` are determined by the root
identifiers `R ∈ trvuoci_{m-1}` of their level-`m` trees, so they are finitely many if
`trvuoci_{m-1}` is finite -/
theorem finite_trvExtFib_of_isOdd (hm : m ∈ (ω : M)) (hmo : IsOdd m)
    (hfin : MemStructure.Finite (trvuoci (⋃₀ m))) : MemStructure.Finite (trvExtFib m) := by
  have hG (q : M) (hq : q ∈ trvExtFib m) : ∃ U ∈ trvuoci m, !(U, q) ∈ ciExt m :=
    (mem_trvExtFib_iff.mp hq).right.right
  have hval {q U : M} (hU : U ∈ trvuoci m) (hq : !(U, q) ∈ ciExt m) :
      ∃ R, uc (⋃₀ rtOf (aoc q ﹫ m)) = R ∧ R ∈ trvuoci (⋃₀ m) ∧
        q = ciTriple (aoc q) (cc ∅ !(m, !(R, ∅))) ct ∧
        IsFunction (aoc q) ∧ dom (aoc q) = succ m ∧ (∀ i ∈ m, aoc q ﹫ i = aoc U ﹫ i) ∧
        aoc q ﹫ m = asnchdOf (trvTree R) !(R, ∅) (chdOf (aoc q ﹫ m) !(R, ∅)) ∧
        ∀ x, x ∈ chdOf (aoc q ﹫ m) !(R, ∅) ↔
          ∃ q', x = !(q', !(R, ∅)) ∧ !(R, q') ∈ ciExt (⋃₀ m) := by
    obtain ⟨R, hR, htr, hf, hdom, hlow, hrt, htree, hchd⟩ :=
      exists_of_mem_ciExt_of_mem_trvuoci hm hmo hU hq
    refine ⟨R, ?_, hR, htr, hf, hdom, hlow, htree, hchd⟩
    rw [hrt, sUnion_singleton, uc_orderedPair]
  refine hfin.of_isInjectionFromTo (f := (fun q ↦ uc (⋃₀ rtOf (aoc q ﹫ m))) ↾₀ trvExtFib m)
    (isInjectionFromTo_toSetRestrictedTo (isSetRestrictedTo_of_definable _) (fun q hq ↦ ?_)
      fun q hq q' hq' hqq' ↦ ?_)
  · obtain ⟨U, hU, hqU⟩ := hG q hq
    obtain ⟨R, hRq, hR, -⟩ := hval hU hqU
    rwa [hRq]
  obtain ⟨U, hU, hqU⟩ := hG q hq
  obtain ⟨U', hU', hqU'⟩ := hG q' hq'
  obtain ⟨R, hRq, -, htr, hf, hdom, hlow, htree, hchd⟩ := hval hU hqU
  obtain ⟨R', hRq', -, htr', hf', hdom', hlow', htree', hchd'⟩ := hval hU' hqU'
  have hRR : R = R' := by rw [← hRq, ← hRq', hqq']
  subst hRR
  have hUU := eq_of_mem_trvuoci_of_isOdd hm hmo hU hU'
  subst hUU
  have haoc : aoc q = aoc q' := by
    refine hf.ext hf' (hdom.trans hdom'.symm) fun i hi ↦ ?_
    rw [hdom] at hi
    rcases mem_or_eq_of_mem_succ hi with hi | rfl
    · rw [hlow i hi, hlow' i hi]
    · have hC : chdOf (aoc q ﹫ i) !(R, ∅) = chdOf (aoc q' ﹫ i) !(R, ∅) := by
        ext x
        rw [hchd, hchd']
      rw [htree, htree', hC]
  rw [htr, htr', haoc]

end OddExt

section Witness

theorem empty_mem_succ_of_mem_omega (hn : n ∈ (ω : M)) : (∅ : M) ∈ succ n := by
  by_cases h : n = ∅
  · rw [h]
    exact mem_succ_self ∅
  · exact mem_succ_of_mem (empty_mem_of_ordinal_of_ne_empty (ordinal_of_mem ordinal_omega hn) h)

/-! ### Trivial `uoci`'s from trivial arrays -/

/-- The discontinuous `uoci` with array `A`, empty signature and its continuity failure at the
root `(otci0Uc, ∅)` of level `0`, to the left -/
noncomputable def lfTrvUoci (A : M) : M := cc (cc (ciTriple A ∅ dct) !(∅, !(otci0Uc, ∅))) lf

section Values

variable (A : M)

private theorem isFunction_lfTrvUoci₀ : IsFunction (cc (ciTriple A ∅ dct) !(∅, !(otci0Uc, ∅))) :=
  (isFunction_ciTriple _ _ _).cc _

private theorem dom_lfTrvUoci₀ :
    dom (cc (ciTriple A ∅ dct) !(∅, !(otci0Uc, ∅))) = ((4 : ℕ) : M) := by
  rw [dom_cc, dom_ciTriple]
  rfl

private theorem val_lfTrvUoci {k : ℕ} (hk : k < 3) :
    lfTrvUoci A ﹫ (k : M) = ciTriple A ∅ dct ﹫ (k : M) := by
  rw [lfTrvUoci, cc_val_of_mem (isFunction_lfTrvUoci₀ A) _
      (by rw [dom_lfTrvUoci₀]; exact natCast_mem_natCast_of_lt (by omega)),
    cc_val_of_mem (isFunction_ciTriple _ _ _) _
      (by rw [dom_ciTriple]; exact natCast_mem_natCast_of_lt hk)]

theorem isFunction_lfTrvUoci : IsFunction (lfTrvUoci A) := (isFunction_lfTrvUoci₀ A).cc _

theorem dom_lfTrvUoci : dom (lfTrvUoci A) = ((5 : ℕ) : M) := by
  rw [lfTrvUoci, dom_cc, dom_lfTrvUoci₀]
  rfl

theorem aoc_lfTrvUoci : aoc (lfTrvUoci A) = A := by
  exact (val_lfTrvUoci A (k := 0) (by omega)).trans (aoc_ciTriple A ∅ dct)

theorem sig_lfTrvUoci : sig (lfTrvUoci A) = ∅ := by
  exact (val_lfTrvUoci A (k := 1) (by omega)).trans (sig_ciTriple A ∅ dct)

theorem ctp_lfTrvUoci : ctp (lfTrvUoci A) = dct := by
  exact (val_lfTrvUoci A (k := 2) (by omega)).trans (ctp_ciTriple A ∅ dct)

theorem ucflvldcn_lfTrvUoci : ucflvldcn (lfTrvUoci A) = !(∅, !(otci0Uc, ∅)) := by
  have h : ((3 : ℕ) : M) = dom (ciTriple A ∅ dct) := (dom_ciTriple _ _ _).symm
  rw [ucflvldcn, lfTrvUoci, cc_val_of_mem (isFunction_lfTrvUoci₀ A) _
      (by rw [dom_lfTrvUoci₀]; exact natCast_mem_natCast_of_lt (by omega)), h,
    cc_val_self (isFunction_ciTriple _ _ _)]

theorem ucfdr_lfTrvUoci : ucfdr (lfTrvUoci A) = lf := by
  have h : ((4 : ℕ) : M) = dom (cc (ciTriple A ∅ dct) !(∅, !(otci0Uc, ∅))) :=
    (dom_lfTrvUoci₀ A).symm
  rw [ucfdr, lfTrvUoci, h, cc_val_self (isFunction_lfTrvUoci₀ A)]

end Values

/-- The standard labels of the trees of even levels of a trivial array give a standard `uoci` -/
theorem stduociCond_of_mem_trvaotci (hn : n ∈ (ω : M)) (hA : aoc W ∈ trvaotci n)
    (hlbl : ∀ i ∈ succ n, IsEven i → StdLbls (aoc W ﹫ i)) : StduociCond n W := by
  intro i hi p hp
  obtain ⟨-, hev, hodd⟩ := mem_trvotci_iff.mp ((mem_trvaotci_iff.mp hA).right i hi)
  rcases isEven_or_isOdd (mem_omega_of_mem_succ hn hi) with he | ho
  swap
  · rw [hodd ho] at hp
    simp at hp
  have hl := hlbl i hi he p hp
  exact ⟨fun h ↦ hl.left h.right, fun h ↦ (h.right ⟨he, (hev he p hp).mp h.left⟩).elim,
    fun hct ↦ ⟨hl.left, fun hnr ↦ hl.right ⟨hct, hnr⟩⟩⟩

/-- A trivial array with the standard labels at the even levels is the array of a trivial `uoci`:
`{(0, A), (1, ∅), (2, dct)}` for odd `n` and `lfTrvUoci A` for even `n` -/
theorem mem_trvuoci_of_mem_trvaotci (hn : n ∈ (ω : M)) (hA : A ∈ trvaotci n)
    (hlbl : ∀ i ∈ succ n, IsEven i → StdLbls (A ﹫ i)) :
    (IsOdd n → ciTriple A ∅ dct ∈ trvuoci n) ∧ (IsEven n → lfTrvUoci A ∈ trvuoci n) := by
  have hfin : A ∈ finaotci n := mem_finaotci_iff.mpr ⟨(mem_trvaotci_iff.mp hA).left,
    fun i hi ↦ (mem_trvotci_iff.mp ((mem_trvaotci_iff.mp hA).right i hi)).left⟩
  have hsig (W : M) (hW : sig W = ∅) : IsFunction (sig W) ∧
      (∀ i ∈ dom (sig W), ∀ j ∈ dom (sig W), sig W ﹫ i = sig W ﹫ j → i = j) ∧
      dom (sig W) ∈ (ω : M) ∧ ∀ i ∈ dom (sig W), SigCond n W i := by
    rw [hW, dom_empty]
    exact ⟨isFunction_empty, by simp, empty_mem_omega, by simp⟩
  have hmem (W : M) (hW : UociCond (ciRec ↾₀ n) n (finaotci n) W) (haoc : aoc W = A)
      (hct : ctp W = dct) : W ∈ trvuoci n := by
    rw [mem_trvuoci_iff, mem_stduoci_iff, mem_uoci_iff_of_mem_omega hn]
    refine ⟨⟨hW, stduociCond_of_mem_trvaotci hn (haoc ▸ hA) (haoc ▸ hlbl)⟩, haoc ▸ hA, hct⟩
  refine ⟨fun ho ↦ hmem _ ?_ (aoc_ciTriple _ _ _) (ctp_ciTriple _ _ _),
    fun he ↦ hmem _ ?_ (aoc_lfTrvUoci A) (ctp_lfTrvUoci A)⟩
  · have h3 := dom_ciTriple A ∅ dct
    refine ⟨isFunction_ciTriple _ _ _, .inl h3, by rwa [aoc_ciTriple], hsig _ (sig_ciTriple _ _ _),
      .inr (ctp_ciTriple _ _ _), fun _ ↦ ctp_ciTriple _ _ _,
      iff_of_true h3 (.inl ⟨sig_ciTriple _ _ _, ho⟩), fun h ↦ ?_⟩
    rw [h3] at h
    exact (notMem_self _ h).elim
  · have h5 := dom_lfTrvUoci A
    have hno : ¬IsOdd n := fun ho ↦ he.not_isOdd ho
    have hne (j k : ℕ) (hjk : j ≠ k) : ((j : ℕ) : M) ≠ ((k : ℕ) : M) := by
      rw [Ne, natCast_inj]
      exact hjk
    have h0 : A ﹫ ∅ = trvTree otci0Uc :=
      eq_trvTree_of_mem_otci_empty (val_mem_otci_of_mem_aotci (mem_trvaotci_iff.mp hA).left
        (empty_mem_succ_of_mem_omega hn)) (hlbl ∅ (empty_mem_succ_of_mem_omega hn) isEven_empty)
    refine ⟨isFunction_lfTrvUoci A, .inr (.inl h5), by rwa [aoc_lfTrvUoci],
      hsig _ (sig_lfTrvUoci A), .inr (ctp_lfTrvUoci A), fun h ↦ (hno h.right).elim, ?_, fun _ ↦ ?_⟩
    · rw [h5, sig_lfTrvUoci, ctp_lfTrvUoci]
      refine iff_of_false (hne 5 3 (by omega)) ?_
      rintro (⟨-, ho⟩ | h)
      · exact hno ho
      · exact ct_ne_dct h.symm
    refine ⟨?_, ?_, ?_, ?_, .inl (ucfdr_lfTrvUoci A), ?_,
      fun h ↦ (hne 5 6 (by omega) (h5.symm.trans h)).elim⟩
    · rw [ucflvldcn_lfTrvUoci]
      exact ⟨_, _, rfl⟩
    · rw [ucflvl, ucflvldcn_lfTrvUoci, lvl_orderedPair]
      exact empty_mem_succ_of_mem_omega hn
    · rw [ucfdcn, ucflvl, ucflvldcn_lfTrvUoci, lvl_orderedPair, dcn_orderedPair, aoc_lfTrvUoci, h0,
        ndOf_trvTree]
      exact mem_singleton _
    · rw [ucfdcn, ucflvldcn_lfTrvUoci, dcn_orderedPair, uc_orderedPair, otci0Uc, ctp_ciTriple]
    · exact iff_of_true h5 (ucfdr_lfTrvUoci A)

end Witness

section Trees

/-! ### The trivial trees -/

/-- The tree `(otci0Uc, ∅)` is a trivial `otci_0` with the standard labels -/
theorem trvTree_mem_trvotci_empty :
    trvTree otci0Uc ∈ trvotci (∅ : M) ∧ StdLbls (trvTree (otci0Uc : M)) := by
  have hrt : !(otci0Uc, ∅) ∈ rtOf (trvTree (otci0Uc : M)) := by
    rw [rtOf_trvTree]
    exact mem_singleton _
  refine ⟨mem_trvotci_iff.mpr ⟨mem_finotci_iff.mpr ⟨mem_otci_empty_iff.mpr
      ⟨∅, empty_mem_vonNeumann_omega, rfl⟩, by rw [ndOf_trvTree]; exact finite_singleton _⟩,
    fun _ p hp ↦ ?_, fun h ↦ (not_isOdd_empty h).elim⟩, fun p hp ↦ ?_⟩
  · rw [ndOf_trvTree, mem_singleton_iff] at hp
    subst hp
    exact iff_of_true (by rw [uc_orderedPair, otci0Uc, ctp_ciTriple]) hrt
  · rw [ndOf_trvTree, mem_singleton_iff] at hp
    subst hp
    exact ⟨fun _ ↦ lbl_orderedPair, fun h ↦ (h.right hrt).elim⟩

/-- The empty tree is the trivial `otci_n` of odd levels -/
theorem emptySLOT_mem_trvotci (hn0 : n ≠ ∅) (ho : IsOdd n) : emptySLOT ∈ trvotci n := by
  have hS : IsSLOT (emptySLOT : M) := SLOTreeStructure.isSLOTreeStructure_empty
  have hnd : ndOf (emptySLOT : M) = ∅ := SLOTreeStructure.nd_empty
  have hrt : rtOf (emptySLOT : M) = ∅ := SLOTreeStructure.rt_empty
  have hne : ¬IsEven n := fun he ↦ he.not_isOdd ho
  refine mem_trvotci_iff.mpr ⟨mem_finotci_iff.mpr ⟨(mem_otci_iff_of_ne_empty hn0).mpr
    ⟨hS, by simp [hnd], by simp [hrt], fun he ↦ (hne he).elim, by simp [hnd]⟩,
    by rw [hnd]; exact finite_empty⟩, fun he ↦ (hne he).elim, fun _ ↦ hnd⟩

/-- For even `n > 0` and `V ∈ trvuoci_{n-1}` with finitely many extensions, the root `(V, ∅)`
with the children `(q, (V, ∅))` for the extensions `(V, q) ∈ ext_{n-1}` is a trivial `otci_n`
with the standard labels -/
theorem asnchdOf_trvTree_mem_trvotci (hn : n ∈ (ω : M)) (hn0 : n ≠ ∅) (he : IsEven n)
    (hV : V ∈ trvuoci (⋃₀ n)) (hfin : MemStructure.Finite (trvExtFib (⋃₀ n))) :
    asnchdOf (trvTree V) !(V, ∅) (ran ((fun q ↦ !(q, !(V, ∅))) ↾₀ trvExtFib (⋃₀ n))) ∈
        trvotci n ∧
      StdLbls (asnchdOf (trvTree V) !(V, ∅)
        (ran ((fun q ↦ !(q, !(V, ∅))) ↾₀ trvExtFib (⋃₀ n)))) := by
  obtain ⟨hmω, hmn, hnm⟩ := sUnion_mem_of_ne_empty hn hn0
  have hmo : IsOdd (⋃₀ n) := by
    have h := he
    rwa [hnm, isEven_succ_iff hmω] at h
  set m := ⋃₀ n
  set C := ran ((fun q ↦ !(q, !(V, ∅))) ↾₀ trvExtFib m) with hCdef
  set T := asnchdOf (trvTree V) !(V, ∅) C with hTdef
  have hres : IsSetRestrictedTo (fun q ↦ !(q, !(V, ∅))) (trvExtFib m) :=
    isSetRestrictedTo_of_definable _
  have hCmem (x : M) : x ∈ C ↔ ∃ q, x = !(q, !(V, ∅)) ∧ !(V, q) ∈ ciExt m := by
    rw [hCdef, mem_ran_toSetRestrictedTo_iff hres]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, rfl, (mem_trvExtFib_iff_of_mem_trvuoci hmω hmo hV).mp hq⟩
    · rintro ⟨q, rfl, hq⟩
      exact ⟨q, (mem_trvExtFib_iff_of_mem_trvuoci hmω hmo hV).mpr hq, rfl⟩
  have hcn {q : M} (hq : !(V, q) ∈ ciExt m) : !(q, !(V, ∅)) ∈ C := (hCmem _).mpr ⟨q, rfl, hq⟩
  have hVs := (mem_trvuoci_iff.mp hV).left
  have hVu := (mem_stduoci_iff.mp hVs).left
  have hVf : IsFunction V := by
    have h := hVu
    rw [mem_uoci_iff_of_mem_omega hmω] at h
    exact h.left
  have hVd := dom_mem_of_mem_uoci hmω hVu
  have hC : IsNewChd !(V, ∅) C := by
    refine ⟨fun x hx ↦ ?_, fun hb ↦ ?_, fun x hx y hy hxy hk ↦ ?_⟩
    · obtain ⟨q, rfl, hq⟩ := (hCmem x).mp hx
      have hqu := (mem_stduoci_iff.mp (mem_ciExt_props hq).right.left).left
      have hqf : IsFunction q := by
        have h := hqu
        rw [mem_uoci_iff_of_mem_omega hmω] at h
        exact h.left
      rw [left_orderedPair]
      exact ⟨⟨_, _, rfl⟩, hqf, dom_mem_of_mem_uoci hmω hqu⟩
    · obtain ⟨q, hqb, -⟩ := (hCmem _).mp hb
      rw [orderedPair_eq_orderedPair_iff] at hqb
      exact orderedPair_ne_empty _ _ hqb.right.symm
    · obtain ⟨q, rfl, hq⟩ := (hCmem x).mp hx
      obtain ⟨q', rfl, hq'⟩ := (hCmem y).mp hy
      rw [left_orderedPair, left_orderedPair] at hk
      obtain ⟨-, hqs, -, hqc⟩ := mem_ciExt_props hq
      obtain ⟨-, hqs', -, hqc'⟩ := mem_ciExt_props hq'
      exact hxy (by rw [eq_of_aoc_eq_of_ctp_eq_ct hmω hqs hqs' hqc hqc' hk])
  have hTs : IsSLOT T := isSLOT_asnchdOf_trvTree hVf hVd hC
  have hnd : ndOf T = insert !(V, ∅) C := ndOf_asnchdOf_trvTree
  have hrt : rtOf T = {!(V, ∅)} := rtOf_asnchdOf_trvTree hVf hVd hC.right.left
  have hchdb : chdOf T !(V, ∅) = C := chdOf_asnchdOf_trvTree_self hVf hVd hC
  have hchdc {c : M} (hc : c ∈ C) : chdOf T c = ∅ :=
    chdOf_asnchdOf_trvTree_of_mem hVf hVd hC.right.left hc
  have hbn : !(V, ∅) ∈ ndOf T := by
    rw [hnd]
    exact mem_insert _ _
  have hbr : !(V, ∅) ∈ rtOf T := by
    rw [hrt]
    exact mem_singleton _
  have hnode {p : M} (hp : p ∈ ndOf T) :
      p = !(V, ∅) ∨ ∃ q, p = !(q, !(V, ∅)) ∧ !(V, q) ∈ ciExt m := by
    rw [hnd, mem_insert_iff] at hp
    rcases hp with rfl | hp
    · exact .inl rfl
    · exact .inr ((hCmem p).mp hp)
  have hchild {q : M} (hq : !(V, q) ∈ ciExt m) : !(q, !(V, ∅)) ∈ chdOf T !(V, ∅) := by
    rw [hchdb]
    exact hcn hq
  -- `T ∈ otci_n`
  have hTo : T ∈ otci n := by
    rw [mem_otci_iff_of_ne_empty hn0]
    refine ⟨hTs, fun p hp ↦ ?_, fun r hr ↦ ?_, fun _ ↦ ⟨_, hrt⟩, fun p hp ↦ ?_⟩
    · rw [stduociL_ciRec_restrict hmn]
      rcases hnode hp with rfl | ⟨q, rfl, hq⟩
      · rw [uc_orderedPair, lbl_orderedPair]
        exact ⟨hVs, empty_mem_vonNeumann_omega⟩
      · rw [uc_orderedPair, lbl_orderedPair]
        exact ⟨(mem_ciExt_props hq).right.left, orderedPair_mem_vonNeumann_omega
          (mem_vonNeumann_omega_of_mem_stduoci hmω hVs) empty_mem_vonNeumann_omega⟩
    · rw [hrt, mem_singleton_iff] at hr
      rw [hr, trvuociL_ciRec_restrict hmn, uc_orderedPair]
      exact hV
    rw [extL_ciRec_restrict hmn]
    rcases hnode hp with rfl | ⟨q, rfl, hq⟩
    · rw [uc_orderedPair]
      refine ⟨fun D ↦ ⟨?_, ?_⟩, fun q hq r hr ↦ ?_⟩
      · rintro ⟨c, hc, rfl⟩
        rw [hchdb] at hc
        obtain ⟨q, rfl, hq⟩ := (hCmem c).mp hc
        exact ⟨q, hq, by rw [uc_orderedPair]⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨_, hchild hq, by rw [uc_orderedPair]⟩
      have hkey : aoc q = left !(q, !(V, ∅)) ﹫ ∅ := by
        rw [left_orderedPair]
        rfl
      obtain ⟨-, hqs, -, hqc⟩ := mem_ciExt_props hq
      have hset (x : M) : x ∈ losSet (chdlosOf T !(V, ∅) ﹫ aoc q) ↔ x = !(q, !(V, ∅)) := by
        rw [hkey, mem_losSet_chdlosOf_iff hTs hbn (hchild hq)]
        constructor
        · rintro ⟨hx, hk⟩
          rw [hchdb] at hx
          obtain ⟨q', rfl, hq'⟩ := (hCmem x).mp hx
          rw [left_orderedPair, left_orderedPair] at hk
          obtain ⟨-, hqs', -, hqc'⟩ := mem_ciExt_props hq'
          rw [eq_of_aoc_eq_of_ctp_eq_ct hmω hqs' hqs hqc' hqc hk]
        · rintro rfl
          exact ⟨hchild hq, rfl⟩
      rw [(hset r).mp hr, uc_orderedPair]
      refine ⟨rfl, iff_of_true (isLeastLos_of_losSet_eq_singleton ?_ hset) hqc⟩
      rw [hkey]
      exact isStrictLinearOrderedSet_chdlosOf hTs hbn (hchild hq)
    · have hqct := (mem_ciExt_props hq).right.right.right
      rw [uc_orderedPair]
      refine ⟨fun D ↦ iff_of_false ?_ ?_,
        fun q' hq' ↦ (not_mem_ciExt_of_ctp_eq_ct hqct q' hq').elim⟩
      · rintro ⟨c, hc, -⟩
        rw [hchdc (hcn hq)] at hc
        simp at hc
      · rintro ⟨q', hq', -⟩
        exact not_mem_ciExt_of_ctp_eq_ct hqct q' hq'
  refine ⟨mem_trvotci_iff.mpr ⟨mem_finotci_iff.mpr ⟨hTo, ?_⟩, fun _ p hp ↦ ?_,
    fun ho ↦ (he.not_isOdd ho).elim⟩, fun p hp ↦ ⟨fun hr ↦ ?_, fun h ↦ ?_⟩⟩
  · rw [hnd]
    exact (Finite.image hfin).insert _
  · rcases hnode hp with rfl | ⟨q, rfl, hq⟩
    · rw [uc_orderedPair]
      exact iff_of_true (mem_trvuoci_iff.mp hV).right.right hbr
    · rw [uc_orderedPair, (mem_ciExt_props hq).right.right.right]
      exact iff_of_false ct_ne_dct (not_mem_rtOf_of_mem_chdOf hTs (hchild hq))
  · rw [hrt, mem_singleton_iff] at hr
    rw [hr, lbl_orderedPair]
  · rcases hnode hp with rfl | ⟨q, rfl, hq⟩
    · exact (h.right hbr).elim
    · rw [lbl_orderedPair, prtOf_eq_of_mem_chdOf hTs (hchild hq)]

end Trees

section Arrays

/-! ### The trivial arrays -/

/-- Appending a trivial `otci_n` to a trivial array of level `n - 1` -/
theorem cc_mem_trvaotci (hB : IsFunction B) (hdom : dom B = n) (hBi : ∀ i ∈ n, B ﹫ i ∈ trvotci i)
    (hT : T ∈ trvotci n) : cc B T ∈ trvaotci n := by
  have hval (i : M) (hi : i ∈ n) : cc B T ﹫ i = B ﹫ i := cc_val_of_mem hB T (hdom ▸ hi)
  have hlast : cc B T ﹫ n = T := by
    have h := cc_val_self hB T
    rwa [hdom] at h
  have hTo {i X : M} (h : X ∈ trvotci i) : X ∈ otci i :=
    (mem_finotci_iff.mp (mem_trvotci_iff.mp h).left).left
  rw [mem_trvaotci_iff, mem_aotci_iff]
  refine ⟨⟨hB.cc T, by rw [dom_cc, hdom], fun i hi ↦ ?_, by rw [hlast]; exact hTo hT⟩,
    fun i hi ↦ ?_⟩
  · rw [otciL_ciRec_restrict hi, hval i hi]
    exact hTo (hBi i hi)
  · rcases mem_or_eq_of_mem_succ hi with hi | rfl
    · rw [hval i hi]
      exact hBi i hi
    · rw [hlast]
      exact hT

/-- If the trivial `uoci`'s of the levels below `n` exist and the trivial `uoci`'s of the odd
levels below `n` have finitely many extensions, then there is a trivial array of level `n` with the
standard labels -/
theorem exists_mem_trvaotci (hn : n ∈ (ω : M)) (hU : ∀ m ∈ n, ∃ U, U ∈ trvuoci m)
    (hfin : ∀ m ∈ n, MemStructure.Finite (trvExtFib m)) :
    ∃ A ∈ trvaotci n, ∀ i ∈ succ n, IsEven i → StdLbls (A ﹫ i) := by
  have hlvl (B : M) (hB : IsFunction B) (hdom : dom B = n) (hBi : ∀ i ∈ n, B ﹫ i ∈ trvotci i)
      (hBl : ∀ i ∈ n, IsEven i → StdLbls (B ﹫ i)) (T : M) (hT : T ∈ trvotci n)
      (hTl : IsEven n → StdLbls T) :
      ∃ A ∈ trvaotci n, ∀ i ∈ succ n, IsEven i → StdLbls (A ﹫ i) := by
    refine ⟨cc B T, cc_mem_trvaotci hB hdom hBi hT, fun i hi he ↦ ?_⟩
    rcases mem_or_eq_of_mem_succ hi with hi | rfl
    · rw [cc_val_of_mem hB T (hdom ▸ hi)]
      exact hBl i hi he
    · have h := cc_val_self hB T
      rw [hdom] at h
      rw [h]
      exact hTl he
  by_cases hn0 : n = ∅
  · subst hn0
    exact hlvl ∅ isFunction_empty dom_empty (by simp) (by simp) _ trvTree_mem_trvotci_empty.left
      fun _ ↦ trvTree_mem_trvotci_empty.right
  obtain ⟨hmω, hmn, hnm⟩ := sUnion_mem_of_ne_empty hn hn0
  obtain ⟨U', hU'⟩ := hU _ hmn
  obtain ⟨hAa, hAt⟩ := mem_trvaotci_iff.mp (mem_trvuoci_iff.mp hU').right.left
  obtain ⟨hAf, hAdom, -⟩ := mem_aotci_iff.mp hAa
  have hmem {i : M} (hi : i ∈ n) : i ∈ succ (⋃₀ n) := by
    rw [hnm] at hi
    exact hi
  have hBi (i : M) (hi : i ∈ n) : aoc U' ﹫ i ∈ trvotci i := hAt i (hmem hi)
  have hBl (i : M) (hi : i ∈ n) (he : IsEven i) : StdLbls (aoc U' ﹫ i) :=
    stdLbls_of_stduociCond (mem_stduoci_iff.mp (mem_trvuoci_iff.mp hU').left).right (hmem hi) he
  rcases isEven_or_isOdd hn with he | ho
  · obtain ⟨hT, hTl⟩ := asnchdOf_trvTree_mem_trvotci hn hn0 he hU' (hfin _ hmn)
    exact hlvl _ hAf (hAdom.trans hnm.symm) hBi hBl _ hT fun _ ↦ hTl
  · exact hlvl _ hAf (hAdom.trans hnm.symm) hBi hBl _ (emptySLOT_mem_trvotci hn0 ho)
      fun he ↦ (he.not_isOdd ho).elim

end Arrays

section Finite

/-! ### Finiteness of the trivial `uoci`'s of even levels -/

/-- For even `n`, the elements of `trvuoci_n` are functions on at most `6` whose values are the
common array `A`, `∅`, `dct`, a node of `A`, `lf` or `dn`, or an extension of a trivial `uoci`
of an odd level below `n`; so `trvuoci_n` is finite if these extensions are finitely many -/
theorem finite_trvuoci_of_isEven (hn : n ∈ (ω : M))
    (hfin : ∀ j ∈ n, MemStructure.Finite (trvExtFib j)) (hU₀ : U ∈ trvuoci n) :
    MemStructure.Finite (trvuoci n) := by
  obtain ⟨hAa, hAt⟩ := mem_trvaotci_iff.mp (mem_trvuoci_iff.mp hU₀).right.left
  have hresN : IsSetRestrictedTo (fun i ↦ ndOf (aoc U ﹫ i)) (succ n) :=
    isSetRestrictedTo_of_definable _
  have hresF : IsSetRestrictedTo trvExtFib n := isSetRestrictedTo_of_definable _
  set N := ⋃₀ ran ((fun i ↦ ndOf (aoc U ﹫ i)) ↾₀ succ n) with hN
  set F := ⋃₀ ran (trvExtFib ↾₀ n) with hF
  set Y := insert (aoc U) (((2 : ℕ) : M) ∪ (succ n ×ˢ N) ∪ F) with hY
  have hNf : MemStructure.Finite N := Finite.sUnion
    (Finite.image (finite_of_mem_omega (succ_mem_omega hn))) fun y hy ↦ by
      rw [mem_ran_toSetRestrictedTo_iff hresN] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      exact (mem_finotci_iff.mp (mem_trvotci_iff.mp (hAt i hi)).left).right
  have hFf : MemStructure.Finite F := Finite.sUnion (Finite.image (finite_of_mem_omega hn))
    fun y hy ↦ by
      rw [mem_ran_toSetRestrictedTo_iff hresF] at hy
      obtain ⟨j, hj, rfl⟩ := hy
      exact hfin j hj
  have hYf : MemStructure.Finite Y :=
    (((finite_of_mem_omega (natCast_mem_omega 2)).union
      ((finite_of_mem_omega (succ_mem_omega hn)).sprod hNf)).union hFf).insert _
  have h2 {x : M} (hx : x ∈ ((2 : ℕ) : M)) : x ∈ Y := by
    rw [hY, mem_insert_iff, mem_union_iff, mem_union_iff]
    exact .inr (.inl (.inl hx))
  refine (((finite_of_mem_omega (natCast_mem_omega 6)).sprod hYf).powerset).of_subset fun V hV ↦ ?_
  have hVu := (mem_stduoci_iff.mp (mem_trvuoci_iff.mp hV).left).left
  have hdomω : dom V ∈ (ω : M) := by
    have h := dom_mem_of_mem_uoci hn hVu
    rw [mem_sdiff_iff] at h
    exact h.left
  rw [mem_uoci_iff_of_mem_omega hn] at hVu
  obtain ⟨hVf, hdom, -, -, -, -, -, hucf⟩ := hVu
  have haoc : aoc V = aoc U := aoc_eq_of_mem_trvuoci hn hV hU₀
  have hord : Ordinal (dom V) := ordinal_of_mem ordinal_omega hdomω
  have h3 {k : ℕ} (hk : 3 ≤ k) (h : ((k : ℕ) : M) ∈ dom V) : ((3 : ℕ) : M) ∈ dom V := by
    rcases Nat.eq_or_lt_of_le hk with rfl | hk
    · exact h
    · exact hord.transitive _ h (natCast_mem_natCast_of_lt hk)
  rw [mem_powerset_iff]
  intro z hz
  obtain ⟨k, v, rfl⟩ := hVf.isRelation hz
  have hk : k ∈ dom V := (mem_dom_iff V k).mpr ⟨v, hz⟩
  have hk6 := mem_natCast_six_of_mem_dom hdom hk
  rw [pair_mem_sprod_iff, ← hVf.val_eq_of_rel hz]
  refine ⟨hk6, ?_⟩
  obtain ⟨j, hj, rfl⟩ := exists_eq_natCast_of_mem_natCast hk6
  rcases j with _ | _ | _ | _ | _ | _ | j
  · change aoc V ∈ Y
    rw [haoc, hY]
    exact mem_insert _ _
  · change sig V ∈ Y
    rw [sig_eq_empty_of_mem_trvuoci hn hV, ← natCast_zero]
    exact h2 (natCast_mem_natCast_of_lt (by omega))
  · change ctp V ∈ Y
    rw [(mem_trvuoci_iff.mp hV).right.right, dct]
    exact h2 (natCast_mem_natCast_of_lt (by omega))
  · change ucflvldcn V ∈ Y
    obtain ⟨⟨l, d, hld⟩, hl, hd, -⟩ := hucf hk
    rw [ucflvl, hld, lvl_orderedPair] at hl
    rw [ucfdcn, hld, dcn_orderedPair, ucflvl, hld, lvl_orderedPair, haoc] at hd
    rw [hld, hY, mem_insert_iff, mem_union_iff, mem_union_iff, pair_mem_sprod_iff, hN,
      mem_sUnion_iff]
    exact .inr (.inl (.inr ⟨hl, _, (mem_ran_toSetRestrictedTo_iff hresN).mpr ⟨l, hl, rfl⟩, hd⟩))
  · change ucfdr V ∈ Y
    rcases (hucf (h3 (by omega) hk)).right.right.right.right.left with h | h <;> rw [h]
    · rw [lf]
      exact h2 (natCast_mem_natCast_of_lt (by omega))
    · rw [dn]
      exact h2 (natCast_mem_natCast_of_lt (by omega))
  · change ucfex V ∈ Y
    obtain ⟨-, hl, hd, hdct, -, -, h6⟩ := hucf (h3 (by omega) hk)
    have hdom6 : dom V = ((6 : ℕ) : M) := by
      rcases hdom with h | h | h
      · rw [h] at hk
        exact (notMem_self _ (by
          have := (isNat_natCast (M := M) 3).ordinal.transitive _ hk
            (natCast_mem_natCast_of_lt (show 3 < 5 by omega))
          exact this)).elim
      · rw [h] at hk
        exact (notMem_self _ hk).elim
      · exact h
    obtain ⟨h0, hext⟩ := h6 hdom6
    have hl0 : ucflvl V ≠ ∅ := by
      rw [ne_empty_iff]
      exact ⟨∅, h0⟩
    have hjn := sUnion_mem_of_mem_succ hn hl h0
    have hlω := mem_omega_of_mem_succ hn hl
    obtain ⟨hjω, hjl, hlj⟩ := sUnion_mem_of_ne_empty hlω hl0
    rw [extL_ciRec_restrict hjn] at hext
    rw [haoc] at hd
    obtain ⟨hTo, hev, hodd⟩ := mem_trvotci_iff.mp (hAt _ hl)
    have hTo := (mem_finotci_iff.mp hTo).left
    rcases isEven_or_isOdd hlω with he | ho
    swap
    · rw [hodd ho] at hd
      simp at hd
    have hdr := (hev he _ hd).mp hdct
    have hTo' := hTo
    rw [mem_otci_iff_of_ne_empty hl0] at hTo'
    have hduc := hTo'.right.right.left _ hdr
    rw [trvuociL_ciRec_restrict hjl] at hduc
    have hjo : IsOdd (⋃₀ ucflvl V) := by
      have h := he
      rwa [hlj, isEven_succ_iff hjω] at h
    have hmem : ucfex V ∈ trvExtFib (⋃₀ ucflvl V) :=
      mem_trvExtFib_iff.mpr ⟨(mem_ciExt_props hext).right.left, hjo, _, hduc, hext⟩
    rw [hY, mem_insert_iff, mem_union_iff, hF, mem_sUnion_iff]
    exact .inr (.inr ⟨_, (mem_ran_toSetRestrictedTo_iff hresF).mpr ⟨_, hjn, rfl⟩, hmem⟩)
  · omega

end Finite

section Induction

/-! ### Existence of the trivial `uoci`'s -/

/-- `trvuoci_n` is nonempty, the trivial `uoci` of level `n` has finitely many extensions if `n` is
odd, and `trvuoci_n` is finite if `n` is even -/
def TrvExists (n : M) : Prop :=
  (∃ U, U ∈ trvuoci n) ∧ MemStructure.Finite (trvExtFib n) ∧
    (IsEven n → MemStructure.Finite (trvuoci n))

instance : Multiclass.Definable (fun xs : Fin 1 → M ↦ TrvExists (xs 0)) Set.univ := by
  have h : (fun xs : Fin 1 → M ↦ TrvExists (xs 0)) = fun xs : Fin 1 → M ↦
      ∃ X F, X = trvuoci (xs 0) ∧ F = trvExtFib (xs 0) ∧ (∃ U, U ∈ X) ∧
        MemStructure.Finite F ∧ (IsEven (xs 0) → MemStructure.Finite X) := by
    funext xs
    simp [TrvExists]
  rw [h]
  infer_instance

/-- The step of the induction -/
theorem trvExists_of_forall (hn : n ∈ (ω : M)) (ih : ∀ m ∈ n, TrvExists m) : TrvExists n := by
  obtain ⟨A, hA, hlbl⟩ := exists_mem_trvaotci hn (fun m hm ↦ (ih m hm).left)
    (fun m hm ↦ (ih m hm).right.left)
  have hW := mem_trvuoci_of_mem_trvaotci hn hA hlbl
  obtain ⟨U, hU⟩ : ∃ U, U ∈ trvuoci n := by
    rcases isEven_or_isOdd hn with he | ho
    · exact ⟨_, hW.right he⟩
    · exact ⟨_, hW.left ho⟩
  refine ⟨⟨U, hU⟩, ?_, fun _ ↦ finite_trvuoci_of_isEven hn (fun j hj ↦ (ih j hj).right.left) hU⟩
  rcases isEven_or_isOdd hn with he | ho
  · exact finite_empty.of_subset fun q hq ↦
      (he.not_isOdd (mem_trvExtFib_iff.mp hq).right.left).elim
  · have hn0 : n ≠ ∅ := fun h ↦ not_isOdd_empty (h ▸ ho)
    obtain ⟨hmω, hmn, hnm⟩ := sUnion_mem_of_ne_empty hn hn0
    have hme : IsEven (⋃₀ n) := by
      have h := ho
      rwa [hnm, isOdd_succ_iff hmω] at h
    exact finite_trvExtFib_of_isOdd hn ho ((ih _ hmn).right.right hme)

theorem trvExists (hn : n ∈ (ω : M)) : TrvExists n :=
  induction_of_modelsZF (A := fun x ↦ x ∈ (ω : M) → TrvExists x)
    (fun _ ih hx ↦ trvExists_of_forall hx fun m hm ↦ ih m hm (ordinal_omega.transitive _ hx hm))
    n hn

/-- Trivial `uoci`'s exist at every level -/
theorem exists_mem_trvuoci (hn : n ∈ (ω : M)) : ∃ U, U ∈ trvuoci n := (trvExists hn).left

/-- `trvuoci_n` is finite -/
theorem finite_trvuoci (hn : n ∈ (ω : M)) : MemStructure.Finite (trvuoci n) := by
  rcases isEven_or_isOdd hn with he | ho
  · exact (trvExists hn).right.right he
  · obtain ⟨U, hU⟩ := exists_mem_trvuoci hn
    refine (finite_singleton U).of_subset fun V hV ↦ ?_
    rw [mem_singleton_iff]
    exact eq_of_mem_trvuoci_of_isOdd hn ho hV hU

end Induction

section Names

/-! ### The trivial array, the trivial `otci` and the trivial `uoci` of odd levels -/

/-- The trivial array of level `n`: the common array of the elements of `trvuoci_n` -/
noncomputable def trvAotci : ClassFunction M := fun n ↦ ⋃₀ ran (aoc ↾₀ trvuoci n)

/-- The trivial `otci_n` with the standard labels: the level-`n` tree of the trivial array -/
noncomputable def trvOtci : ClassFunction M := fun n ↦ trvAotci n ﹫ n

/-- The trivial `uoci` of an odd level `n`: the unique element of `trvuoci_n` -/
noncomputable def trvUoci : ClassFunction M := fun n ↦ ⋃₀ trvuoci n

variable {i : M}

/-- The elements of `trvuoci_n` have the array `trvAotci n` -/
theorem aoc_eq_trvAotci (hn : n ∈ (ω : M)) (hU : U ∈ trvuoci n) : aoc U = trvAotci n := by
  have hran : ran (aoc ↾₀ trvuoci n) = {aoc U} := by
    ext y
    rw [mem_ran_toSetRestrictedTo_iff (isSetRestrictedTo_of_definable _), mem_singleton_iff]
    constructor
    · rintro ⟨V, hV, rfl⟩
      exact aoc_eq_of_mem_trvuoci hn hV hU
    · rintro rfl
      exact ⟨U, hU, rfl⟩
  change aoc U = ⋃₀ ran (aoc ↾₀ trvuoci n)
  rw [hran, sUnion_singleton]

/-- The trivial array is a trivial array -/
theorem trvAotci_mem_trvaotci (hn : n ∈ (ω : M)) : trvAotci n ∈ trvaotci n := by
  obtain ⟨U, hU⟩ := exists_mem_trvuoci hn
  rw [← aoc_eq_trvAotci hn hU]
  exact (mem_trvuoci_iff.mp hU).right.left

/-- The trivial `otci` is a trivial `otci` -/
theorem trvOtci_mem_trvotci (hn : n ∈ (ω : M)) : trvOtci n ∈ trvotci n :=
  (mem_trvaotci_iff.mp (trvAotci_mem_trvaotci hn)).right n (mem_succ_self n)

/-- The trivial `otci` of an even level has the standard labels -/
theorem stdLbls_trvOtci (hn : n ∈ (ω : M)) (he : IsEven n) : StdLbls (trvOtci n) := by
  obtain ⟨U, hU⟩ := exists_mem_trvuoci hn
  change StdLbls (trvAotci n ﹫ n)
  rw [← aoc_eq_trvAotci hn hU]
  exact stdLbls_of_stduociCond (mem_stduoci_iff.mp (mem_trvuoci_iff.mp hU).left).right
    (mem_succ_self n) he

/-- The trivial `otci` is the unique trivial `otci` with the standard labels at even levels -/
theorem eq_trvOtci (hn : n ∈ (ω : M)) (hT : T ∈ trvotci n) (hlbl : IsEven n → StdLbls T) :
    T = trvOtci n := by
  have hT' := trvOtci_mem_trvotci hn
  have hTo := (mem_finotci_iff.mp (mem_trvotci_iff.mp hT).left).left
  have hT'o := (mem_finotci_iff.mp (mem_trvotci_iff.mp hT').left).left
  rcases isEven_or_isOdd hn with he | ho
  swap
  · rw [eq_emptySLOT_of_ndOf_eq_empty (isSLOT_of_mem_otci hTo)
        ((mem_trvotci_iff.mp hT).right.right ho),
      eq_emptySLOT_of_ndOf_eq_empty (isSLOT_of_mem_otci hT'o)
        ((mem_trvotci_iff.mp hT').right.right ho)]
  by_cases hn0 : n = ∅
  · subst hn0
    rw [eq_trvTree_of_mem_otci_empty hTo (hlbl he),
      eq_trvTree_of_mem_otci_empty hT'o (stdLbls_trvOtci hn he)]
  obtain ⟨hmω, hmn, hnm⟩ := sUnion_mem_of_ne_empty hn hn0
  have hmo : IsOdd (⋃₀ n) := by
    have h := he
    rwa [hnm, isEven_succ_iff hmω] at h
  obtain ⟨r, hr⟩ := exists_mem_rtOf_of_mem_otci hTo he
  obtain ⟨r', hr'⟩ := exists_mem_rtOf_of_mem_otci hT'o he
  have huc := ((mem_otci_iff_of_ne_empty hn0).mp hTo).right.right.left r hr
  have huc' := ((mem_otci_iff_of_ne_empty hn0).mp hT'o).right.right.left r' hr'
  rw [trvuociL_ciRec_restrict hmn] at huc huc'
  exact eq_of_mem_trvotci hn hn0 he hT hT' (hlbl he) (stdLbls_trvOtci hn he) hr hr'
    (eq_of_mem_trvuoci_of_isOdd hmω hmo huc huc')

/-- The trees of the trivial array are the trivial `otci`'s -/
theorem trvAotci_val (hn : n ∈ (ω : M)) (hi : i ∈ succ n) : trvAotci n ﹫ i = trvOtci i := by
  obtain ⟨U, hU⟩ := exists_mem_trvuoci hn
  rw [← aoc_eq_trvAotci hn hU]
  exact eq_trvOtci (mem_omega_of_mem_succ hn hi)
    ((mem_trvaotci_iff.mp (mem_trvuoci_iff.mp hU).right.left).right i hi)
    (stdLbls_of_stduociCond (mem_stduoci_iff.mp (mem_trvuoci_iff.mp hU).left).right hi)

/-- For even `n`, `lfTrvUoci (trvAotci n)` is a trivial `uoci` -/
theorem lfTrvUoci_mem_trvuoci (hn : n ∈ (ω : M)) (he : IsEven n) :
    lfTrvUoci (trvAotci n) ∈ trvuoci n :=
  (mem_trvuoci_of_mem_trvaotci hn (trvAotci_mem_trvaotci hn) fun i hi he' ↦ by
    rw [trvAotci_val hn hi]
    exact stdLbls_trvOtci (mem_omega_of_mem_succ hn hi) he').right he

/-- For odd `n`, `trvuoci_n = {trvUoci n}` -/
theorem trvuoci_eq_singleton (hn : n ∈ (ω : M)) (ho : IsOdd n) : trvuoci n = {trvUoci n} := by
  obtain ⟨U, hU⟩ := exists_mem_trvuoci hn
  have h : trvuoci n = {U} := by
    ext V
    rw [mem_singleton_iff]
    exact ⟨fun hV ↦ eq_of_mem_trvuoci_of_isOdd hn ho hV hU, fun h ↦ h ▸ hU⟩
  change trvuoci n = {⋃₀ trvuoci n}
  rw [h, sUnion_singleton]

theorem trvUoci_mem_trvuoci (hn : n ∈ (ω : M)) (ho : IsOdd n) : trvUoci n ∈ trvuoci n := by
  rw [trvuoci_eq_singleton hn ho]
  exact mem_singleton _

/-- For odd `n`, the trivial `uoci` is `{(0, trvAotci n), (1, ∅), (2, dct)}` -/
theorem trvUoci_eq (hn : n ∈ (ω : M)) (ho : IsOdd n) :
    trvUoci n = ciTriple (trvAotci n) ∅ dct := by
  have h := (mem_trvuoci_of_mem_trvaotci hn (trvAotci_mem_trvaotci hn) fun i hi he ↦ by
    rw [trvAotci_val hn hi]
    exact stdLbls_trvOtci (mem_omega_of_mem_succ hn hi) he).left ho
  rw [trvuoci_eq_singleton hn ho, mem_singleton_iff] at h
  exact h.symm

end Names

end FirstOrder.Language.MemStructure
