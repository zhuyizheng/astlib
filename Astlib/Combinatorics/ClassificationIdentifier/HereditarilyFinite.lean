/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.HereditarilyFinite
import Astlib.Combinatorics.ClassificationIdentifier.Basic
/-!
# Classification identifiers are hereditarily finite

A semi-linearly ordered tree structure with finitely many nodes, all in `𝕍 ω`, is in `𝕍 ω`
(`mem_vonNeumann_omega_of_isSLOT`). Hence, for `n ∈ ω`, the nodes of the trees in `otci_n`, the
trees in `finotci_n` and the elements of `uoci_n` are in `𝕍 ω` (`ndOf_subset_of_mem_otci`,
`mem_vonNeumann_omega_of_mem_finotci`, `mem_vonNeumann_omega_of_mem_uoci`).
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M] {n P T U : M}

theorem natCast_mem_vonNeumann_omega' (k : ℕ) : ((k : ℕ) : M) ∈ (𝕍 ω : M) :=
  natCast_mem_vonNeumann_omega k

theorem ciTriple_mem_vonNeumann_omega {a b c : M} (ha : a ∈ (𝕍 ω : M)) (hb : b ∈ (𝕍 ω : M))
    (hc : c ∈ (𝕍 ω : M)) : ciTriple a b c ∈ (𝕍 ω : M) := by
  have h0 := isFunction_empty.cc_mem_vonNeumann_omega (M := M) empty_mem_vonNeumann_omega ha
  have h1 := (isFunction_empty.cc a).cc_mem_vonNeumann_omega h0 hb
  exact ((isFunction_empty.cc a).cc b).cc_mem_vonNeumann_omega h1 hc

theorem otci0Uc_mem_vonNeumann_omega : (otci0Uc : M) ∈ (𝕍 ω : M) :=
  ciTriple_mem_vonNeumann_omega empty_mem_vonNeumann_omega empty_mem_vonNeumann_omega
    (natCast_mem_vonNeumann_omega 1)

/-- The keys `dvals N` of a finite set `N ⊆ 𝕍 ω` of nodes are in `𝕍 ω` -/
theorem dvals_mem_vonNeumann_omega {N : M} (hfin : Finite N) (hN : N ⊆ (𝕍 ω : M))
    (hnd : ∀ a ∈ N, IsOrderedPair a ∧ IsFunction (left a)) : dvals N ∈ (𝕍 ω : M) := by
  have hres : IsSetRestrictedTo (fun a ↦ left a ﹫ ∅) N := isSetRestrictedTo_of_definable N
  have hfinD : Finite (dvals N) := by
    have heq : dvals N = ran ((fun a ↦ left a ﹫ ∅) ↾₀ N) := by
      ext z
      rw [mem_dvals_iff, mem_ran_toSetRestrictedTo_iff hres]
      grind
    rw [heq]
    exact hfin.image
  refine hfinD.mem_vonNeumann_omega fun z hz ↦ ?_
  rw [mem_dvals_iff] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  obtain ⟨⟨u, l, rfl⟩, hf⟩ := hnd _ ha
  rw [left_orderedPair] at hf ⊢
  exact hf.val_mem_vonNeumann_omega (mem_vonNeumann_omega_of_orderedPair_mem (hN ha)).left ∅

/-- A semi-linearly ordered tree structure with finitely many nodes, all in `𝕍 ω`, is in
`𝕍 ω` -/
theorem mem_vonNeumann_omega_of_isSLOT (hP : IsSLOT P) (hfin : Finite (ndOf P))
    (hnd : ndOf P ⊆ (𝕍 ω : M)) : P ∈ (𝕍 ω : M) := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hP
  have hT := hS.isTreeStructure
  have hNV : ndOf P ∈ (𝕍 ω : M) := hfin.mem_vonNeumann_omega hnd
  have hD : dvals (ndOf P) ∈ (𝕍 ω : M) := dvals_mem_vonNeumann_omega hfin hnd
    fun a ha ↦ ⟨hS.isOrderedPair ha, hS.isFunction_left ha⟩
  have hdepV : (SLOTreeStructure.ofM P).ts.dep ∈ (𝕍 ω : M) := by
    have hdep := hT.dep_fromTo
    refine hdep.isFunction.mem_vonNeumann_omega ?_ fun a ha ↦ ?_
    · rw [hdep.dom_eq]
      exact hNV
    · rw [hdep.dom_eq] at ha
      exact mem_vonNeumann_omega_of_mem_omega (hdep.val_mem ha)
  have hB := mem_slotBound hP (subset_refl (ndOf P))
  unfold slotBound at hB
  rw [mem_sprod_iff] at hB
  obtain ⟨u, hu, v, hv, hPuv⟩ := hB
  have hvV : v ∈ (𝕍 ω : M) := by
    rw [mem_powerset_iff] at hv
    refine mem_vonNeumann_omega_of_subset ?_ hv
    exact sprod_mem_vonNeumann_omega (powerset_mem_vonNeumann_omega hNV)
      (powerset_mem_vonNeumann_omega (sprod_mem_vonNeumann_omega hD
        (sprod_mem_vonNeumann_omega (powerset_mem_vonNeumann_omega hNV)
          (powerset_mem_vonNeumann_omega (sprod_mem_vonNeumann_omega hNV hNV)))))
  rw [mem_sprod_iff] at hu
  obtain ⟨A, hA, w, hw, rfl⟩ := hu
  rw [mem_sprod_iff] at hw
  obtain ⟨d, -, C, hC, rfl⟩ := hw
  have hdep : (SLOTreeStructure.ofM P).ts.dep = d := by
    simp [SLOTreeStructure.ts, TreeStructure.dep, hPuv]
  rw [hdep] at hdepV
  rw [mem_powerset_iff] at hA hC
  rw [hPuv]
  refine orderedPair_mem_vonNeumann_omega (orderedPair_mem_vonNeumann_omega
    (mem_vonNeumann_omega_of_subset hNV hA) (orderedPair_mem_vonNeumann_omega hdepV ?_)) hvV
  exact mem_vonNeumann_omega_of_subset
    (sprod_mem_vonNeumann_omega hNV (powerset_mem_vonNeumann_omega hNV)) hC

/-- The nodes of the trees in `otci_n` are in `𝕍 ω`, and so are the elements of `uoci_n` -/
def HerFinLevel (n : M) : Prop :=
  (∀ T ∈ otci n, ∀ p ∈ ndOf T, p ∈ (𝕍 ω : M)) ∧ ∀ U ∈ uoci n, U ∈ (𝕍 ω : M)

instance : Multiclass.Definable (fun xs : Fin 1 → M ↦ xs 0 ∈ (𝕍 ω : M)) Set.univ := by
  infer_instance

instance : Multiclass.Definable (fun xs : Fin 1 → M ↦ ∀ p ∈ ndOf (xs 0), p ∈ (𝕍 ω : M))
    Set.univ := by
  infer_instance

instance : Multiclass.Definable
    (fun xs : Fin 1 → M ↦ ∀ T ∈ otci (xs 0), ∀ p ∈ ndOf T, p ∈ (𝕍 ω : M)) Set.univ := by
  infer_instance

instance : Multiclass.Definable (fun xs : Fin 1 → M ↦ ∀ U ∈ uoci (xs 0), U ∈ (𝕍 ω : M))
    Set.univ := by
  infer_instance

instance : Multiclass.Definable (fun xs : Fin 1 → M ↦ HerFinLevel (xs 0)) Set.univ := by
  unfold HerFinLevel; infer_instance

/-- The step of the induction: `HerFinLevel n` holds if it holds below `n` -/
theorem herFinLevel_of_forall (hn : n ∈ (ω : M)) (ih : ∀ m ∈ n, HerFinLevel m) :
    HerFinLevel n := by
  -- the nodes of the trees in `otci_n`
  have hnd : ∀ T ∈ otci n, ∀ p ∈ ndOf T, p ∈ (𝕍 ω : M) := by
    intro T hT p hp
    by_cases hn0 : n = ∅
    · subst hn0
      rw [mem_otci_empty_iff] at hT
      obtain ⟨l, hl, rfl⟩ := hT
      rw [ndOf_irmrtOf_emptySLOT, mem_singleton_iff] at hp
      rw [hp]
      exact orderedPair_mem_vonNeumann_omega otci0Uc_mem_vonNeumann_omega hl
    obtain ⟨-, hmn, -⟩ := sUnion_mem_of_ne_empty hn hn0
    have hS : (SLOTreeStructure.ofM T).IsSLOTreeStructure := isSLOT_of_mem_otci hT
    rw [mem_otci_iff_of_ne_empty hn0] at hT
    obtain ⟨-, hnodes, -⟩ := hT
    obtain ⟨huc, hlbl⟩ := hnodes p hp
    rw [stduociL_ciRec_restrict hmn] at huc
    have hucV := (ih _ hmn).right _ (mem_stduoci_iff.mp huc).left
    obtain ⟨u, l, rfl⟩ := hS.isOrderedPair hp
    rw [uc_orderedPair] at hucV
    rw [lbl_orderedPair] at hlbl
    exact orderedPair_mem_vonNeumann_omega hucV hlbl
  refine ⟨hnd, fun U hU ↦ ?_⟩
  -- the trees in `finotci_i` for `i ≤ n` and their nodes
  have hlev (i : M) (hi : i ∈ succ n) (T : M) (hT : T ∈ otci i) : ndOf T ⊆ (𝕍 ω : M) := by
    intro p hp
    rcases mem_or_eq_of_mem_succ hi with hi | rfl
    · exact (ih i hi).left T hT p hp
    · exact hnd T hT p hp
  rw [mem_uoci_iff_of_mem_omega hn] at hU
  obtain ⟨hUf, hdom, haoc, ⟨hsigf, -, hsigdom, hsig⟩, hctp, -, -, hucf⟩ := hU
  have hA := (mem_finaotci_iff.mp haoc).left
  have htree (i : M) (hi : i ∈ succ n) : aoc U ﹫ i ∈ otci i := val_mem_otci_of_mem_aotci hA hi
  have hnodeV (i : M) (hi : i ∈ succ n) {d : M} (hd : d ∈ ndOf (aoc U ﹫ i)) : d ∈ (𝕍 ω : M) :=
    hlev i hi _ (htree i hi) hd
  have hsuccV : succ n ∈ (𝕍 ω : M) := insert_mem_vonNeumann_omega
    (mem_vonNeumann_omega_of_mem_omega hn) (mem_vonNeumann_omega_of_mem_omega hn)
  have hlvlV {i : M} (hi : i ∈ succ n) : i ∈ (𝕍 ω : M) := mem_vonNeumann_omega_of_mem hsuccV hi
  refine hUf.mem_vonNeumann_omega ?_ fun i hi ↦ ?_
  · rcases hdom with h | h | h <;> rw [h] <;> exact natCast_mem_vonNeumann_omega _
  have h3 {k : ℕ} (hk : 3 < k) (hkd : (k : M) ∈ dom U) : ((3 : ℕ) : M) ∈ dom U := by
    rcases hdom with h | h | h <;> rw [h] at hkd ⊢ <;> rw [natCast_mem_natCast_iff] at hkd ⊢ <;>
      omega
  obtain ⟨k, hk, rfl⟩ := exists_eq_natCast_of_mem_natCast (mem_natCast_six_of_mem_dom hdom hi)
  rcases k with _ | _ | _ | _ | _ | _ | k
  · -- the array
    change aoc U ∈ (𝕍 ω : M)
    obtain ⟨hAf, hAdom, -, -⟩ := mem_aotci_iff.mp hA
    refine hAf.mem_vonNeumann_omega (by rwa [hAdom]) fun i hi ↦ ?_
    rw [hAdom] at hi
    have hT := htree i hi
    have hfin := (mem_finaotci_iff.mp haoc).right i hi
    exact mem_vonNeumann_omega_of_isSLOT (isSLOT_of_mem_otci hT)
      (mem_finotci_iff.mp hfin).right (hlev i hi _ hT)
  · -- the signature
    change sig U ∈ (𝕍 ω : M)
    refine hsigf.mem_vonNeumann_omega (mem_vonNeumann_omega_of_mem_omega hsigdom) fun j hj ↦ ?_
    obtain ⟨⟨l, d, hld⟩, hlvl, heven, hodd, -⟩ := hsig j hj
    have hl : siglvl U j = l := by rw [siglvl, hld, lvl_orderedPair]
    have hd : sigdcn U j = d := by rw [sigdcn, hld, dcn_orderedPair]
    rw [hl] at hlvl heven hodd
    rw [hd] at heven hodd
    rw [hld]
    refine orderedPair_mem_vonNeumann_omega (hlvlV hlvl) (hnodeV l hlvl ?_)
    have hX := isSLOT_of_mem_otci (htree l hlvl)
    rcases isEven_or_isOdd (mem_omega_of_mem_succ hn hlvl) with he | ho
    · obtain ⟨r, hr⟩ := exists_mem_rtOf_of_mem_otci (htree l hlvl) he
      rcases heven he r hr with h | ⟨_, -, -, h⟩
      · exact mem_ndOf_of_mem_chdOf hX h
      · exact mem_ndOf_of_mem_chdOf hX h
    · rcases hodd ho with h | ⟨_, -, -, h⟩
      · exact mem_ndOf_of_mem_rtOf h
      · exact mem_ndOf_of_mem_chdOf hX h
  · -- the continuity type
    change ctp U ∈ (𝕍 ω : M)
    rcases hctp with h | h <;> rw [h] <;> exact natCast_mem_vonNeumann_omega _
  · -- the level and the node of the unique continuity failure
    change ucflvldcn U ∈ (𝕍 ω : M)
    obtain ⟨⟨l, d, hld⟩, hlvl, hdcn, -⟩ := hucf hi
    have hl : ucflvl U = l := by rw [ucflvl, hld, lvl_orderedPair]
    have hd : ucfdcn U = d := by rw [ucfdcn, hld, dcn_orderedPair]
    rw [hl] at hlvl hdcn
    rw [hd] at hdcn
    rw [hld]
    exact orderedPair_mem_vonNeumann_omega (hlvlV hlvl) (hnodeV l hlvl hdcn)
  · -- the direction
    change ucfdr U ∈ (𝕍 ω : M)
    obtain ⟨-, -, -, -, hdr, -⟩ := hucf (h3 (by omega) hi)
    rcases hdr with h | h <;> rw [h] <;> exact natCast_mem_vonNeumann_omega _
  · -- the extension
    change ucfex U ∈ (𝕍 ω : M)
    have h6 : dom U = ((6 : ℕ) : M) := by
      rcases hdom with h | h | h <;> rw [h] at hi
      · rw [natCast_mem_natCast_iff] at hi
        omega
      · rw [natCast_mem_natCast_iff] at hi
        omega
      · exact h
    obtain ⟨-, hlvl, -, -, -, -, hex⟩ := hucf (h3 (by omega) hi)
    obtain ⟨h0, hext⟩ := hex h6
    have hm := sUnion_mem_of_mem_succ hn hlvl h0
    rw [extL_ciRec_restrict hm, mem_ciExt_iff] at hext
    obtain ⟨P', -, Q, hQ, hPQ, -⟩ := hext
    rw [orderedPair_eq_orderedPair_iff] at hPQ
    rw [hPQ.right]
    exact (ih _ hm).right Q (mem_stduoci_iff.mp hQ).left
  · omega

theorem herFinLevel (hn : n ∈ (ω : M)) : HerFinLevel n :=
  induction_of_modelsZF (A := fun x ↦ x ∈ (ω : M) → HerFinLevel x)
    (fun _ ih hx ↦ herFinLevel_of_forall hx fun m hm ↦ ih m hm (ordinal_omega.transitive _ hx hm))
    n hn

/-- The nodes of the trees in `otci_n` are in `𝕍 ω` -/
theorem ndOf_subset_of_mem_otci (hn : n ∈ (ω : M)) (hT : T ∈ otci n) :
    ndOf T ⊆ (𝕍 ω : M) :=
  fun p hp ↦ (herFinLevel hn).left T hT p hp

/-- The elements of `uoci_n` are in `𝕍 ω` -/
theorem mem_vonNeumann_omega_of_mem_uoci (hn : n ∈ (ω : M)) (hU : U ∈ uoci n) :
    U ∈ (𝕍 ω : M) :=
  (herFinLevel hn).right U hU

/-- The elements of `stduoci_n` are in `𝕍 ω` -/
theorem mem_vonNeumann_omega_of_mem_stduoci (hn : n ∈ (ω : M)) (hU : U ∈ stduoci n) :
    U ∈ (𝕍 ω : M) :=
  mem_vonNeumann_omega_of_mem_uoci hn (mem_stduoci_iff.mp hU).left

/-- The trees in `finotci_n` are in `𝕍 ω` -/
theorem mem_vonNeumann_omega_of_mem_finotci (hn : n ∈ (ω : M)) (hT : T ∈ finotci n) :
    T ∈ (𝕍 ω : M) := by
  rw [mem_finotci_iff] at hT
  exact mem_vonNeumann_omega_of_isSLOT (isSLOT_of_mem_otci hT.left) hT.right
    (ndOf_subset_of_mem_otci hn hT.left)

end FirstOrder.Language.MemStructure
