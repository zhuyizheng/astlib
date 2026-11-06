/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.IsoOrder
/-!
# The canonical isomorphism `(T ⊗ Q) ⊗ W ≅ T ⊗ (Q ⊗ W)`

Every node of `T ⊗ (Q ⊗ W)` is an image: the preimage `isoPre Q W t τ` of an upper node is
rebuilt from the contraction of its entries in `W`. Hence the canonical map
`tensorProdAssocIso T Q W` is an isomorphism (`isAotciIsomorphism_tensorProdAssocIso`).
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M]

section SurjTree

/-! ### The level-`1` tree of the rebuilt target `V`: the entries `(1, e_k)` of the contraction,
as nodes `(dctUZero, k)` ordered as the `e_k` in `W(1)` -/

/-- The nodes `(dctUZero, k)`, `k < m` -/
noncomputable def surjNds (m : M) : M := ({dctUZero} : M) ×ˢ m

/-- `(dctUZero, k) ↦ e_k` for the entries `c(k) = (1, e_k)` -/
noncomputable def surjTau (c : M) : M := (fun p ↦ dcn (c ﹫ right p)) ↾₀ surjNds (dom c)

theorem isSetRestrictedTo_surjTau (c : M) :
    IsSetRestrictedTo (fun p ↦ dcn (c ﹫ right p)) (surjNds (dom c)) := by
  have : ClassFunction.Definable (fun p ↦ dcn (c ﹫ right p)) Set.univ :=
    ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ c' : M, c' = c ∧
      dcn (c' ﹫ right (xs 0)) = xs 1) fun u w ↦ by
        constructor
        · rintro ⟨c', rfl, h⟩
          exact h
        · intro h
          exact ⟨_, rfl, h⟩
  exact isSetRestrictedTo_of_definable _

theorem mem_surjNds_iff {m p : M} : p ∈ surjNds m ↔ ∃ k ∈ m, p = !(dctUZero, k) := by
  rw [surjNds, mem_sprod_iff]
  constructor
  · rintro ⟨u, hu, k, hk, rfl⟩
    rw [mem_singleton_iff] at hu
    exact ⟨k, hk, by rw [hu]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, mem_singleton _, k, hk, rfl⟩

theorem surjTau_val {c k : M} (hk : k ∈ dom c) :
    surjTau c ﹫ !(dctUZero, k) = dcn (c ﹫ k) := by
  rw [surjTau, val_toSetRestrictedTo (isSetRestrictedTo_surjTau c)
    (mem_surjNds_iff.mpr ⟨k, hk, rfl⟩), right_orderedPair]

/-- The entries of `c` are `(1, e)` for distinct nodes `e` of `W(1)` -/
def IsEntrySeq (W c : M) : Prop :=
  IsFunction c ∧ dom c ∈ (ω : M) ∧ (∀ k ∈ dom c, ∀ l ∈ dom c, c ﹫ k = c ﹫ l → k = l) ∧
    ∀ k ∈ dom c, ∃ e ∈ ndOf (W ﹫ ((1 : ℕ) : M)), c ﹫ k = !(((1 : ℕ) : M), e)

theorem IsEntrySeq.dcn_mem {W c : M} (hc : IsEntrySeq W c) {k : M} (hk : k ∈ dom c) :
    dcn (c ﹫ k) ∈ ndOf (W ﹫ ((1 : ℕ) : M)) ∧ c ﹫ k = !(((1 : ℕ) : M), dcn (c ﹫ k)) := by
  obtain ⟨e, he, hce⟩ := hc.right.right.right k hk
  rw [hce, dcn_orderedPair]
  exact ⟨he, rfl⟩

theorem IsEntrySeq.surjTau_inj {W c : M} (hc : IsEntrySeq W c) :
    surjTau c !: surjNds (dom c) ↪ ndOf (W ﹫ ((1 : ℕ) : M)) := by
  have hres := isSetRestrictedTo_surjTau c
  refine ⟨⟨isFunction_toSetRestrictedTo hres, dom_toSetRestrictedTo hres, fun y hy ↦ ?_⟩,
    fun p q hp hq h ↦ ?_⟩
  · rw [surjTau, mem_ran_toSetRestrictedTo_iff hres] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    obtain ⟨k, hk, rfl⟩ := mem_surjNds_iff.mp hp
    rw [right_orderedPair]
    exact (hc.dcn_mem hk).left
  · obtain ⟨k, hk, rfl⟩ := mem_surjNds_iff.mp hp
    obtain ⟨l, hl, rfl⟩ := mem_surjNds_iff.mp hq
    rw [surjTau_val hk, surjTau_val hl] at h
    have h' : c ﹫ k = c ﹫ l := by rw [(hc.dcn_mem hk).right, (hc.dcn_mem hl).right, h]
    rw [hc.right.right.left k hk l hl h']

/-- The linearly ordered set of the nodes -/
noncomputable def surjLos (W c : M) : M :=
  !(surjNds (dom c), pullback (surjTau c) (odrOne (W ﹫ ((1 : ℕ) : M))) (surjNds (dom c)))

/-- The array of the rebuilt target: the level-`0` tree of `B` and the level-`1` tree on the
entries -/
noncomputable def surjX (B W c : M) : M :=
  cc (B ↾ ((1 : ℕ) : M)) (rtLosSLOT trvAZero (surjLos W c))

variable {B W c : M}

theorem IsEntrySeq.isStrictLinearOrderedSet (hW : W ∈ aotci ((1 : ℕ) : M))
    (hc : IsEntrySeq W c) : IsStrictLinearOrderedSet (surjLos W c) := by
  have hW1 := val_mem_otci_of_mem_aotci hW (mem_succ_self _)
  refine ⟨⟨_, _, rfl⟩, ?_⟩
  rw [surjLos, losOdr_orderedPair, losSet_orderedPair]
  exact (rtlosOf_of_mem_otci_one hW1).left.pullback hc.surjTau_inj

theorem IsEntrySeq.tree_mem (hW : W ∈ aotci ((1 : ℕ) : M)) (hc : IsEntrySeq W c) :
    rtLosSLOT trvAZero (surjLos W c) ∈ otci ((1 : ℕ) : M) := by
  refine rtLosSLOT_mem_otci_one (fun _ ↦ hc.isStrictLinearOrderedSet hW) fun a ha ↦ ?_
  rw [surjLos, losSet_orderedPair] at ha
  obtain ⟨k, hk, rfl⟩ := mem_surjNds_iff.mp ha
  exact ⟨k, mem_vonNeumann_omega_of_mem_omega (ordinal_omega.transitive _ hc.right.left hk), rfl⟩

theorem IsEntrySeq.surjX_mem (hB : B ∈ aotci ((1 : ℕ) : M)) (hW : W ∈ aotci ((1 : ℕ) : M))
    (hc : IsEntrySeq W c) : surjX B W c ∈ aotci ((1 : ℕ) : M) :=
  cc_restrict_mem_aotci_one hB (hc.tree_mem hW)

theorem surjX_val_zero (hB : B ∈ aotci ((1 : ℕ) : M)) : surjX B W c ﹫ ∅ = B ﹫ ∅ :=
  cc_restrict_val_zero hB _

theorem surjX_val_one (hB : B ∈ aotci ((1 : ℕ) : M)) :
    surjX B W c ﹫ ((1 : ℕ) : M) = rtLosSLOT trvAZero (surjLos W c) :=
  cc_restrict_val_one hB _

theorem ndOf_surjX_val_one (hB : B ∈ aotci ((1 : ℕ) : M)) :
    ndOf (surjX B W c ﹫ ((1 : ℕ) : M)) = surjNds (dom c) := by
  rw [surjX_val_one hB, ndOf_rtLosSLOT, surjLos, losSet_orderedPair]

theorem rel_surjX_iff (hB : B ∈ aotci ((1 : ℕ) : M)) {k l : M}
    (hk : k ∈ dom c) (hl : l ∈ dom c) :
    (!(dctUZero, k)) [odrOne (surjX B W c ﹫ ((1 : ℕ) : M))] (!(dctUZero, l)) ↔
      (dcn (c ﹫ k)) [odrOne (W ﹫ ((1 : ℕ) : M))] (dcn (c ﹫ l)) := by
  have hne : losSet (surjLos W c) ≠ ∅ := by
    rw [surjLos, losSet_orderedPair]
    intro h0
    have h' : !(dctUZero, k) ∈ surjNds (dom c) := mem_surjNds_iff.mpr ⟨k, hk, rfl⟩
    rw [h0] at h'
    exact notin_empty _ h'
  rw [surjX_val_one hB, odrOne_rtLosSLOT hne, surjLos, losOdr_orderedPair, rel_pullback_iff,
    surjTau_val hk, surjTau_val hl]
  exact ⟨fun h ↦ h.right, fun h ↦ ⟨⟨mem_surjNds_iff.mpr ⟨k, hk, rfl⟩,
    mem_surjNds_iff.mpr ⟨l, hl, rfl⟩⟩, h⟩⟩

end SurjTree

section SurjPull

/-! ### Pulling the embeddings back to the rebuilt target -/

/-- `g` pulled back: `u ↦ ρ(dctUZero, k)` for the index `k = ci(1, e)` of the entry of `g(u)` -/
noncomputable def pullOne (ci W g : M) : M :=
  (fun u ↦ relabelOne trvAZero
    !(dctUZero, ci ﹫ !(((1 : ℕ) : M), tpOrig W ((1 : ℕ) : M) ((g ﹫ ((1 : ℕ) : M)) ﹫ u)))) ↾₀
    dom (g ﹫ ((1 : ℕ) : M))

/-- The family behind `pullOne`, with packed parameters `p = (ci, (W, g))` -/
noncomputable def pullG (p u : M) : M :=
  relabelOne trvAZero !(dctUZero, left p ﹫ !(((1 : ℕ) : M), tpOrig (left (right p)) ((1 : ℕ) : M)
    ((right (right p) ﹫ ((1 : ℕ) : M)) ﹫ u)))

/-- The graph of `pullG` with unpacked parameters -/
def PullGAux (ci W g u r : M) : Prop :=
  ∃ one y o e k p : M, one = ((1 : ℕ) : M) ∧ y = (g ﹫ one) ﹫ u ∧ tpOrig W one y = o ∧
    e = !(one, o) ∧ k = ci ﹫ e ∧ p = !(dctUZero, k) ∧ relabelOne trvAZero p = r

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ PullGAux (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)) Set.univ := by
  unfold PullGAux
  infer_instance

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ PullGAux (xs i) (xs j) (xs k) (xs l) (xs m)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ PullGAux (xs i) (xs j) (xs k) (xs l) (xs m)) = Multiclass.remap
      (fun ys : Fin 5 → M ↦ PullGAux (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)) ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ pullG (xs 0) (xs 1) = xs 2) Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ pullG (xs 0) (xs 1) = xs 2) = fun xs ↦
      ∃ ci W' g : M, ci = left (xs 0) ∧ W' = left (right (xs 0)) ∧ g = right (right (xs 0)) ∧
        PullGAux ci W' g (xs 1) (xs 2) := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, _, rfl, rfl, rfl, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, h⟩
    · rintro ⟨ci, W', g, rfl, rfl, rfl, one, y, o, e, k, p, rfl, rfl, rfl, rfl, rfl, rfl, h⟩
      exact h
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ pullG (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ pullG (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ pullG (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : ClassFunction.Definable (fun p : M ↦ pullOne (left p) (left (right p))
    (right (right p))) Set.univ := by
  have : ClassFunction.Definable (fun p : M ↦ dom (right (right p) ﹫ ((1 : ℕ) : M))) Set.univ := by
    infer_instance
  exact ClassFunction.Definable.toSetRestrictedTo (G := pullG)
    (D := fun p ↦ dom (right (right p) ﹫ ((1 : ℕ) : M)))

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ pullOne (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  obtain ⟨G, hG⟩ : ∃ G : ClassFunction M, G = fun p : M ↦ pullOne (left p) (left (right p))
      (right (right p)) := ⟨_, rfl⟩
  have : G.Definable Set.univ := by
    rw [hG]
    infer_instance
  have h : (fun xs : Fin 4 → M ↦ pullOne (xs 0) (xs 1) (xs 2) = xs 3) =
      fun xs : Fin 4 → M ↦ ∃ p : M, p = !(xs 0, !(xs 1, xs 2)) ∧ G p = xs 3 := by
    funext xs
    apply propext
    rw [hG]
    simp only [left_orderedPair, right_orderedPair, exists_eq_left]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ pullOne (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ pullOne (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ pullOne (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

theorem pullOne_spec (ci W g : M) : IsFunction (pullOne ci W g) ∧
    dom (pullOne ci W g) = dom (g ﹫ ((1 : ℕ) : M)) ∧ ∀ u ∈ dom (g ﹫ ((1 : ℕ) : M)),
      pullOne ci W g ﹫ u = relabelOne trvAZero
        !(dctUZero, ci ﹫ !(((1 : ℕ) : M), tpOrig W ((1 : ℕ) : M) ((g ﹫ ((1 : ℕ) : M)) ﹫ u))) := by
  have hres : IsSetRestrictedTo (fun u ↦ pullG !(ci, !(W, g)) u) (dom (g ﹫ ((1 : ℕ) : M))) := by
    generalize !(ci, !(W, g)) = P₀
    have : ClassFunction.Definable (fun u ↦ pullG P₀ u) Set.univ :=
      ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ p : M,
        p = P₀ ∧ pullG p (xs 0) = xs 1) fun u w ↦ by
          constructor
          · rintro ⟨p, rfl, h⟩
            exact h
          · intro h
            exact ⟨_, rfl, h⟩
    exact isSetRestrictedTo_of_definable _
  have hf : (fun u ↦ relabelOne trvAZero
      !(dctUZero, ci ﹫ !(((1 : ℕ) : M), tpOrig W ((1 : ℕ) : M) ((g ﹫ ((1 : ℕ) : M)) ﹫ u)))) =
      fun u ↦ pullG !(ci, !(W, g)) u := by
    funext u
    simp only [pullG, left_orderedPair, right_orderedPair]
  unfold pullOne
  rw [hf]
  exact ⟨isFunction_toSetRestrictedTo hres, dom_toSetRestrictedTo hres,
    fun u hu ↦ (val_toSetRestrictedTo hres hu).trans
      (by simp only [pullG, left_orderedPair, right_orderedPair])⟩

/-- A node of `(Q ⊗ W)(1)` pulled back to `(Q ⊗ X)(1)` -/
noncomputable def pullNd (Q W ci X z : M) : M :=
  if IsTpTwo Q W z then !(dctUZero, !(nodeQ z, embMk (aoc (uc (nodeQ z)))
    (tensorProdTwoAOneTgt X) (pullOne ci W (nodeH z)))) else z

end SurjPull

section SurjPullFacts

variable {Q B W c : M}

/-- The embedding `(dctUZero, k) ↦ ρ(e_k)` of the rebuilt target into `W ⊗ Z` -/
noncomputable def surjPsi (B W c : M) : M :=
  embMk (surjX B W c) (tensorProdTwoAOneTgt W)
    ((fun p ↦ relabelOne trvAZero (dcn (c ﹫ right p))) ↾₀ surjNds (dom c))

theorem isSetRestrictedTo_surjPsi (c : M) :
    IsSetRestrictedTo (fun p ↦ relabelOne trvAZero (dcn (c ﹫ right p))) (surjNds (dom c)) := by
  have : ClassFunction.Definable (fun p ↦ relabelOne trvAZero (dcn (c ﹫ right p))) Set.univ :=
    ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ c' y : M, c' = c ∧
      y = dcn (c' ﹫ right (xs 0)) ∧ relabelOne trvAZero y = xs 1) fun u w ↦ by
        constructor
        · rintro ⟨c', y, rfl, rfl, h⟩
          exact h
        · intro h
          exact ⟨_, _, rfl, rfl, h⟩
  exact isSetRestrictedTo_of_definable _

theorem surjPsi_val {k : M} (hk : k ∈ dom c) :
    (surjPsi B W c ﹫ ((1 : ℕ) : M)) ﹫ !(dctUZero, k) = relabelOne trvAZero (dcn (c ﹫ k)) := by
  rw [surjPsi, embMk_val_one, val_toSetRestrictedTo (isSetRestrictedTo_surjPsi c)
    (mem_surjNds_iff.mpr ⟨k, hk, rfl⟩), right_orderedPair]

theorem surjPsi_mem (hB : B ∈ aotci ((1 : ℕ) : M)) (hW : W ∈ aotci ((1 : ℕ) : M))
    (hc : IsEntrySeq W c) :
    surjPsi B W c ∈ aotciEmbSet ((1 : ℕ) : M) (surjX B W c) (tensorProdTwoAOneTgt W) := by
  have hX := hc.surjX_mem hB hW
  have hTW := tensorProdTwoAOneTgt_mem hW
  have hW1 := val_mem_otci_of_mem_aotci hW (mem_succ_self _)
  have hres := isSetRestrictedTo_surjPsi c
  refine embMk_mem_aotciEmbSet' hX hTW (isFunction_toSetRestrictedTo hres)
    (by rw [dom_toSetRestrictedTo hres, ndOf_surjX_val_one hB]) (fun p hp ↦ ?_)
    (fun p hp p' hp' hpp' ↦ ?_)
  · rw [ndOf_surjX_val_one hB] at hp
    obtain ⟨k, hk, rfl⟩ := mem_surjNds_iff.mp hp
    rw [val_toSetRestrictedTo hres (mem_surjNds_iff.mpr ⟨k, hk, rfl⟩), right_orderedPair,
      tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hW1]
    exact ⟨_, (hc.dcn_mem hk).left, rfl⟩
  · rw [ndOf_surjX_val_one hB] at hp hp'
    obtain ⟨k, hk, rfl⟩ := mem_surjNds_iff.mp hp
    obtain ⟨l, hl, rfl⟩ := mem_surjNds_iff.mp hp'
    rw [val_toSetRestrictedTo hres (mem_surjNds_iff.mpr ⟨k, hk, rfl⟩),
      val_toSetRestrictedTo hres (mem_surjNds_iff.mpr ⟨l, hl, rfl⟩), right_orderedPair,
      right_orderedPair, rel_tgt_relabel_iff hW (hc.dcn_mem hk).left (hc.dcn_mem hl).left]
    exact (rel_surjX_iff hB hk hl).mp hpp'

omit [ModelsZF M] in
/-- The entry function `c` is a bijection onto its range -/
theorem IsEntrySeq.isBijection (hc : IsEntrySeq W c) : c !: dom c ↔ ran c :=
  ⟨⟨⟨hc.left, rfl, fun _ h ↦ h⟩, fun x y hx hy h ↦ hc.right.right.left x hx y hy h⟩,
    ⟨⟨hc.left, rfl, fun _ h ↦ h⟩, rfl⟩⟩

theorem IsEntrySeq.inv_val (hc : IsEntrySeq W c) {x : M} (hx : x ∈ ran c) :
    c⁻¹ ﹫ x ∈ dom c ∧ c ﹫ (c⁻¹ ﹫ x) = x :=
  ⟨hc.isBijection.inv.isInjectionFromTo.isFunctionFromTo.val_mem hx,
    hc.isBijection.val_inv_val hx⟩

/-- The entries of `g` are entries of `c` -/
def EntriesIn (W c g u : M) : Prop :=
  !(((1 : ℕ) : M), tpOrig W ((1 : ℕ) : M) ((g ﹫ ((1 : ℕ) : M)) ﹫ u)) ∈ ran c

/-- The pullback of an embedding `g` with entries in `c` is an embedding into the rebuilt
target -/
theorem pullEmb_mem (hB : B ∈ aotci ((1 : ℕ) : M)) (hW : W ∈ aotci ((1 : ℕ) : M))
    (hc : IsEntrySeq W c) {A g : M} (hA : A ∈ aotci ((1 : ℕ) : M))
    (hg : g ∈ aotciEmbSet ((1 : ℕ) : M) A (tensorProdTwoAOneTgt W))
    (hent : ∀ u ∈ ndOf (A ﹫ ((1 : ℕ) : M)), EntriesIn W c g u) :
    embMk A (tensorProdTwoAOneTgt (surjX B W c)) (pullOne c⁻¹ W g) ∈
      aotciEmbSet ((1 : ℕ) : M) A (tensorProdTwoAOneTgt (surjX B W c)) := by
  have hX := hc.surjX_mem hB hW
  have hTX := tensorProdTwoAOneTgt_mem hX
  have hTW := tensorProdTwoAOneTgt_mem hW
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  obtain ⟨hpf, hpd, hpv⟩ := pullOne_spec c⁻¹ W g
  obtain ⟨-, hgd⟩ := embChg_val_one_isFunction hg
  have hnode (u : M) (hu : u ∈ ndOf (A ﹫ ((1 : ℕ) : M))) :
      ∃ e ∈ ndOf (W ﹫ ((1 : ℕ) : M)), (g ﹫ ((1 : ℕ) : M)) ﹫ u = relabelOne trvAZero e ∧
        c⁻¹ ﹫ !(((1 : ℕ) : M), tpOrig W ((1 : ℕ) : M) ((g ﹫ ((1 : ℕ) : M)) ﹫ u)) ∈ dom c ∧
        dcn (c ﹫ (c⁻¹ ﹫ !(((1 : ℕ) : M), tpOrig W ((1 : ℕ) : M) ((g ﹫ ((1 : ℕ) : M)) ﹫ u)))) =
          e := by
    obtain ⟨e, he, hge⟩ := exists_relabelOne_eq hW hg hu
    obtain ⟨hk, hck⟩ := hc.inv_val (hent u hu)
    refine ⟨e, he, hge, hk, ?_⟩
    rw [hck, dcn_orderedPair, hge, tpOrig_one_relabelOne hW he]
  refine embMk_mem_aotciEmbSet' hA hTX hpf (by rw [hpd, hgd]) (fun u hu ↦ ?_)
    (fun u hu u' hu' huu' ↦ ?_)
  · obtain ⟨e, -, -, hk, -⟩ := hnode u hu
    rw [hpv u (by rw [hgd]; exact hu), tensorProdTwoAOneTgt_val_one,
      mem_ndOf_tensorProdOneAZero_iff hX1]
    exact ⟨_, by rw [ndOf_surjX_val_one hB]; exact mem_surjNds_iff.mpr ⟨_, hk, rfl⟩, rfl⟩
  · obtain ⟨e, he, hge, hk, hke⟩ := hnode u hu
    obtain ⟨e', he', hge', hk', hke'⟩ := hnode u' hu'
    rw [hpv u (by rw [hgd]; exact hu), hpv u' (by rw [hgd]; exact hu'),
      rel_tgt_relabel_iff hX (by rw [ndOf_surjX_val_one hB]; exact mem_surjNds_iff.mpr ⟨_, hk, rfl⟩)
        (by rw [ndOf_surjX_val_one hB]; exact mem_surjNds_iff.mpr ⟨_, hk', rfl⟩),
      rel_surjX_iff hB hk hk', hke, hke']
    have h := emb_odr hA hTW hg hu hu' huu'
    rwa [hge, hge', rel_tgt_relabel_iff hW he he'] at h

end SurjPullFacts

section SurjPullNd

variable {Q B W c : M}

/-- Pulling a node back and pushing it forward again gives the node -/
theorem pullNd_spec (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hB : B ∈ aotci ((1 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) (hc : IsEntrySeq W c) {z : M}
    (hz : z ∈ ndOf (tensorProdATwoAOne Q W ﹫ ((1 : ℕ) : M)))
    (hent : IsTpTwo Q W z →
      ∀ u ∈ ndOf (aoc (uc (nodeQ z)) ﹫ ((1 : ℕ) : M)), EntriesIn W c (nodeH z) u) :
    pullNd Q W c⁻¹ (surjX B W c) z ∈ ndOf (tensorProdATwoAOne Q (surjX B W c) ﹫ ((1 : ℕ) : M)) ∧
      pushNd Q (surjX B W c) W (surjPsi B W c) (pullNd Q W c⁻¹ (surjX B W c) z) = z := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hX := hc.surjX_mem hB hW
  have hTW := tensorProdTwoAOneTgt_mem hW
  have hψ := surjPsi_mem hB hW hc
  by_cases hT : IsTpTwo Q W z
  · have hent' := hent hT
    obtain ⟨q, hq, hqr, g, hg, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp hT
    rw [nodeQ_orderedPair, nodeH_orderedPair] at hent'
    have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
    have hA := aoc_mem_aotci_of_mem_stduoci_one hUq
    have hh := pullEmb_mem hB hW hc hA hg hent'
    have hyN : !(dctUZero, !(q, embMk (aoc (uc q)) (tensorProdTwoAOneTgt (surjX B W c))
        (pullOne c⁻¹ W g))) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (surjX B W c) :=
      mem_tensorProdTwoAOneNds_iff'.mpr ⟨q, hq, hqr, _, hh, rfl⟩
    rw [pullNd, if_pos hT, nodeQ_orderedPair, nodeH_orderedPair]
    refine ⟨(mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX).mpr (.inr hyN), ?_⟩
    rw [pushNd_of_mem hyN]
    congr 2
    refine eq_of_mem_aotciEmbSet_one hUq hTW (embMk_pushOne_mem hX hW hA hh hψ) hg fun i hi ↦ ?_
    have hu := (siglvl_eq_one hUq hi).right
    rw [(siglvl_eq_one hUq hi).left, pushEmb, embMk_val_one]
    obtain ⟨e, he, hge⟩ := exists_relabelOne_eq hW hg hu
    obtain ⟨hk, hck⟩ := hc.inv_val (hent' _ hu)
    obtain ⟨-, hgd⟩ := embChg_val_one_isFunction hg
    have hhu : (embMk (aoc (uc q)) (tensorProdTwoAOneTgt (surjX B W c)) (pullOne c⁻¹ W g) ﹫
        ((1 : ℕ) : M)) ﹫ sigdcn (uc q) i = relabelOne trvAZero !(dctUZero, c⁻¹ ﹫
          !(((1 : ℕ) : M), tpOrig W ((1 : ℕ) : M) ((g ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) i))) := by
      rw [embMk_val_one, (pullOne_spec c⁻¹ W g).right.right _ (by rw [hgd]; exact hu)]
    have hkn : !(dctUZero, c⁻¹ ﹫ !(((1 : ℕ) : M), tpOrig W ((1 : ℕ) : M)
        ((g ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) i))) ∈ ndOf (surjX B W c ﹫ ((1 : ℕ) : M)) := by
      rw [ndOf_surjX_val_one hB]
      exact mem_surjNds_iff.mpr ⟨_, hk, rfl⟩
    rw [pushOne_val_of_eq hX hh hu hkn hhu, surjPsi_val hk, hck, dcn_orderedPair, hge,
      tpOrig_one_relabelOne hW he]
  · have hb : z ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M)) := by
      rcases (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hW).mp hz with h | h
      · exact h
      · exact (hT h).elim
    have hb' : z ∈ ndOf (tensorProdATwoAOneBase Q (surjX B W c) ﹫ ((1 : ℕ) : M)) := by
      rw [base_val_one_congr Q _ W]; exact hb
    rw [pullNd, if_neg hT]
    exact ⟨(mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX).mpr (.inl hb'),
      pushNd_of_not (not_mem_upper_of_mem_base hQ hb')⟩

end SurjPullNd

section SurjSigma

/-- The `Q(2)`-branch of the pullback -/
def PullNdTwo (W ci X z r : M) : Prop :=
  ∃ q h A T o e : M, q = nodeQ z ∧ h = nodeH z ∧ A = aoc (uc q) ∧ tensorProdTwoAOneTgt X = T ∧
    pullOne ci W h = o ∧ embMk A T o = e ∧ r = !(dctUZero, !(q, e))

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ PullNdTwo (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)) Set.univ := by
  have : ClassFunction.Definable (fun Q : M ↦ tensorProdTwoAOneTgt Q) Set.univ := inferInstance
  unfold PullNdTwo
  infer_instance

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ PullNdTwo (xs i) (xs j) (xs k) (xs l) (xs m)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ PullNdTwo (xs i) (xs j) (xs k) (xs l) (xs m)) = Multiclass.remap
      (fun ys : Fin 5 → M ↦ PullNdTwo (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)) ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable
    (fun xs : Fin 6 → M ↦ pullNd (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) = xs 5) Set.univ := by
  have h : (fun xs : Fin 6 → M ↦ pullNd (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) = xs 5) =
      fun xs : Fin 6 → M ↦ (IsTpTwo (xs 0) (xs 1) (xs 4) ∧
        PullNdTwo (xs 1) (xs 2) (xs 3) (xs 4) (xs 5)) ∨
        (¬ IsTpTwo (xs 0) (xs 1) (xs 4) ∧ xs 4 = xs 5) := by
    funext xs
    apply propext
    by_cases hp : IsTpTwo (xs 0) (xs 1) (xs 4)
    · rw [pullNd, if_pos hp]
      simp only [PullNdTwo, hp, true_and, not_true_eq_false, false_and, or_false]
      constructor
      · intro h
        exact ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, h.symm⟩
      · rintro ⟨q, h, A, T, o, e, rfl, rfl, rfl, rfl, rfl, rfl, h'⟩
        exact h'.symm
    · rw [pullNd, if_neg hp]
      simp only [hp, false_and, false_or, not_false_eq_true, true_and]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m o : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ pullNd (xs i) (xs j) (xs k) (xs l) (xs m) = xs o) Set.univ := by
  have h : (fun xs : Fin n → M ↦ pullNd (xs i) (xs j) (xs k) (xs l) (xs m) = xs o) =
      Multiclass.remap (fun ys : Fin 6 → M ↦
        pullNd (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) = ys 5) ![i, j, k, l, m, o] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The level-`1` part of the pulled-back embedding -/
noncomputable def surjSigOne (Q W ci X σW A : M) : M :=
  (fun w ↦ pullNd Q W ci X ((σW ﹫ ((1 : ℕ) : M)) ﹫ w)) ↾₀ ndOf (A ﹫ ((1 : ℕ) : M))

theorem isSetRestrictedTo_surjSigOne (Q W ci X σW A : M) :
    IsSetRestrictedTo (fun w ↦ pullNd Q W ci X ((σW ﹫ ((1 : ℕ) : M)) ﹫ w))
      (ndOf (A ﹫ ((1 : ℕ) : M))) := by
  have : ClassFunction.Definable (fun w ↦ pullNd Q W ci X ((σW ﹫ ((1 : ℕ) : M)) ﹫ w))
      Set.univ :=
    ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ Q' W' ci' X' s z : M, Q' = Q ∧
      W' = W ∧ ci' = ci ∧ X' = X ∧ s = σW ∧ z = (s ﹫ ((1 : ℕ) : M)) ﹫ xs 0 ∧
        pullNd Q' W' ci' X' z = xs 1) fun u w ↦ by
      constructor
      · rintro ⟨Q', W', ci', X', s, z, rfl, rfl, rfl, rfl, rfl, rfl, h⟩
        exact h
      · intro h
        exact ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, h⟩
  exact isSetRestrictedTo_of_definable _

theorem surjSigOne_val (Q W ci X σW : M) {A w : M} (hw : w ∈ ndOf (A ﹫ ((1 : ℕ) : M))) :
    surjSigOne Q W ci X σW A ﹫ w = pullNd Q W ci X ((σW ﹫ ((1 : ℕ) : M)) ﹫ w) :=
  val_toSetRestrictedTo (isSetRestrictedTo_surjSigOne Q W ci X σW A) hw

variable {Q B W c : M}

/-- The pulled-back embedding `σ` of `A` into `Q ⊗ X`, for an embedding `σ_W` into `Q ⊗ W` with
all entries in `c` -/
theorem surjSig_mem (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hB : B ∈ aotci ((1 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) (hc : IsEntrySeq W c) {A σW : M}
    (hA : A ∈ aotci ((1 : ℕ) : M))
    (hσW : σW ∈ aotciEmbSet ((1 : ℕ) : M) A (tensorProdATwoAOne Q W))
    (hent : ∀ w ∈ ndOf (A ﹫ ((1 : ℕ) : M)), IsTpTwo Q W ((σW ﹫ ((1 : ℕ) : M)) ﹫ w) →
      ∀ u ∈ ndOf (aoc (uc (nodeQ ((σW ﹫ ((1 : ℕ) : M)) ﹫ w))) ﹫ ((1 : ℕ) : M)),
        EntriesIn W c (nodeH ((σW ﹫ ((1 : ℕ) : M)) ﹫ w)) u) :
    embMk A (tensorProdATwoAOne Q (surjX B W c)) (surjSigOne Q W c⁻¹ (surjX B W c) σW A) ∈
      aotciEmbSet ((1 : ℕ) : M) A (tensorProdATwoAOne Q (surjX B W c)) := by
  have hX := hc.surjX_mem hB hW
  have hBX := tensorProdATwoAOne_mem_aotci hQ hX
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hψ := surjPsi_mem hB hW hc
  have hres := isSetRestrictedTo_surjSigOne Q W c⁻¹ (surjX B W c) σW A
  have hz (w : M) (hw : w ∈ ndOf (A ﹫ ((1 : ℕ) : M))) :=
    pullNd_spec hQ hB hW hc (emb_val_mem hA hBW hσW hw) (hent w hw)
  refine embMk_mem_aotciEmbSet' hA hBX (isFunction_toSetRestrictedTo hres)
    (dom_toSetRestrictedTo hres) (fun w hw ↦ ?_) (fun w hw w' hw' hww' ↦ ?_)
  · rw [surjSigOne_val _ _ _ _ _ hw]
    exact (hz w hw).left
  · rw [surjSigOne_val _ _ _ _ _ hw, surjSigOne_val _ _ _ _ _ hw',
      pushNd_odr_iff hQ hX hW hψ (hz w hw).left (hz w' hw').left, (hz w hw).right,
      (hz w' hw').right]
    exact emb_odr hA hBW hσW hw hw' hww'

end SurjSigma

section SurjStd

/-- The signature `k ↦ (1, (dctUZero, k))` of the rebuilt target -/
noncomputable def surjSig (c : M) : M :=
  (fun k ↦ !(((1 : ℕ) : M), !(dctUZero, k))) ↾₀ dom c

theorem isSetRestrictedTo_surjSig (c : M) :
    IsSetRestrictedTo (fun k ↦ !(((1 : ℕ) : M), !(dctUZero, k))) (dom c) :=
  isSetRestrictedTo_of_definable _

theorem surjSig_spec (c : M) : IsFunction (surjSig c) ∧ dom (surjSig c) = dom c ∧
    ∀ k ∈ dom c, surjSig c ﹫ k = !(((1 : ℕ) : M), !(dctUZero, k)) :=
  ⟨isFunction_toSetRestrictedTo (isSetRestrictedTo_surjSig c),
    dom_toSetRestrictedTo (isSetRestrictedTo_surjSig c),
    fun _ hk ↦ val_toSetRestrictedTo (isSetRestrictedTo_surjSig c) hk⟩

variable {U W c : M}

/-- A valid `ucflvldcn` for the array `X` -/
def IsUcfOf (X u : M) : Prop :=
  IsOrderedPair u ∧ lvl u ∈ succ ((1 : ℕ) : M) ∧ dcn u ∈ ndOf (X ﹫ lvl u) ∧
    ctp (uc (dcn u)) = dct

/-- The rebuilt targets are in `stduoci_1` -/
theorem surjV_mem_stduoci (hU : U ∈ stduoci ((1 : ℕ) : M)) (hW : W ∈ aotci ((1 : ℕ) : M))
    (hc : IsEntrySeq W c) (hm : dom c ≠ ∅) {V : M}
    (hV : V = ciTriple (surjX (aoc U) W c) (surjSig c) ct ∨
      ∃ u, IsUcfOf (surjX (aoc U) W c) u ∧
        V = ciQuint (surjX (aoc U) W c) (surjSig c) dct u lf) :
    V ∈ stduoci ((1 : ℕ) : M) := by
  have hA := aoc_mem_aotci_of_mem_stduoci_one hU
  have hX := hc.surjX_mem hA hW
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  obtain ⟨hsf, hsd, hsv⟩ := surjSig_spec c
  have hAf := (mem_finaotci_iff.mp (aoc_mem_finaotci_of_mem_stduoci_one hU)).right
  have hdω := hc.right.left
  have hfin : surjX (aoc U) W c ∈ finaotci ((1 : ℕ) : M) := by
    rw [mem_finaotci_iff]
    refine ⟨hX, fun i hi ↦ ?_⟩
    rcases mem_succ_one_cases hi with rfl | rfl
    · rw [surjX_val_zero hA]
      exact hAf ∅ hi
    · rw [mem_finotci_iff, ndOf_surjX_val_one hA, surjNds]
      exact ⟨hX1, (finite_singleton _).sprod (finite_of_mem_omega hdω)⟩
  have hdct : ctp (dctUZero : M) = dct := by
    rw [dctUZero_eq_lfTrvUoci, ctp_lfTrvUoci]
  have hsig : ∀ {V : M}, aoc V = surjX (aoc U) W c → sig V = surjSig c →
      IsFunction (sig V) ∧
      (∀ i ∈ dom (sig V), ∀ j ∈ dom (sig V), sig V ﹫ i = sig V ﹫ j → i = j) ∧
      dom (sig V) ∈ (ω : M) ∧ ∀ i ∈ dom (sig V), SigCond ((1 : ℕ) : M) V i := by
    intro V haV hsV
    rw [hsV, hsd]
    refine ⟨hsf, fun i hi j hj h ↦ ?_, hdω, fun i hi ↦ ?_⟩
    · rw [hsv i hi, hsv j hj, orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at h
      exact h.right.right
    have hl : siglvl V i = ((1 : ℕ) : M) := by rw [siglvl, hsV, hsv i hi, lvl_orderedPair]
    have hd : sigdcn V i = !(dctUZero, i) := by rw [sigdcn, hsV, hsv i hi, dcn_orderedPair]
    refine ⟨by rw [hsV, hsv i hi]; exact ⟨_, _, rfl⟩, by rw [hl]; exact mem_succ_self _,
      fun he ↦ ?_, fun _ ↦ .inl ?_, by rw [hd, uc_orderedPair]; exact hdct⟩
    · rw [hl] at he
      exact (isOdd_one.not_isEven he).elim
    · rw [hl, hd, haV, surjX_val_one hA, rtOf_rtLosSLOT, surjLos, losSet_orderedPair]
      exact mem_surjNds_iff.mpr ⟨i, hi, rfl⟩
  have hstd : ∀ {V : M}, aoc V = surjX (aoc U) W c → sig V = surjSig c →
      StduociCond ((1 : ℕ) : M) V := by
    intro V haV hsV i hi p hp
    rw [haV] at hp ⊢
    have hstdU := (mem_stduoci_iff.mp hU).right
    rcases mem_succ_one_cases hi with rfl | rfl
    · rw [surjX_val_zero hA] at hp ⊢
      obtain ⟨hA', -, hC'⟩ := hstdU ∅ hi p hp
      obtain ⟨l, hnd, hrt⟩ := exists_ndOf_eq_of_mem_otci_empty
        (val_mem_otci_of_mem_aotci hA (mem_succ_of_mem empty_mem_natCast_one))
      have hpr : p ∈ rtOf (aoc U ﹫ ∅) := by
        rw [hrt]
        rwa [hnd] at hp
      exact ⟨hA', fun h ↦ (h.right ⟨isEven_empty, hpr⟩).elim, hC'⟩
    · rw [ndOf_surjX_val_one hA] at hp
      obtain ⟨k, hk, rfl⟩ := mem_surjNds_iff.mp hp
      rw [uc_orderedPair]
      refine ⟨fun h ↦ (isOdd_one.not_isEven h.left).elim, fun _ ↦ ?_,
        fun h ↦ (ct_ne_dct (h.symm.trans hdct)).elim⟩
      rw [lbl_orderedPair, hsV, hsv k hk]
  rw [mem_stduoci_iff, mem_uoci_iff_of_mem_omega (natCast_mem_omega 1)]
  have hne (j l : ℕ) (hjl : j ≠ l) : ((j : ℕ) : M) ≠ ((l : ℕ) : M) := by
    rw [Ne, natCast_inj]
    exact hjl
  have hs0 : surjSig c ≠ ∅ := fun h0 ↦ hm (by rw [← hsd, h0, dom_empty])
  rcases hV with rfl | ⟨u, hu, rfl⟩
  · have h3 : dom (ciTriple (surjX (aoc U) W c) (surjSig c) ct) = ((3 : ℕ) : M) := dom_ciTriple _ _
      _
    refine ⟨⟨isFunction_ciTriple _ _ _, .inl h3, by rw [aoc_ciTriple]; exact hfin,
      hsig (aoc_ciTriple _ _ _) (sig_ciTriple _ _ _), by rw [ctp_ciTriple]; exact .inl rfl,
      fun h ↦ (hs0 (by rw [← sig_ciTriple (surjX (aoc U) W c) (surjSig c) ct]; exact h.left)).elim,
      iff_of_true h3 (.inr (ctp_ciTriple _ _ _)), fun h ↦ ?_⟩,
      hstd (aoc_ciTriple _ _ _) (sig_ciTriple _ _ _)⟩
    rw [h3] at h
    exact (notMem_self _ h).elim
  · have h5 : dom (ciQuint (surjX (aoc U) W c) (surjSig c) dct u lf) = ((5 : ℕ) : M) :=
      dom_ciQuint _ _ _ _ _
    obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
    refine ⟨⟨isFunction_ciQuint _ _ _ _ _, .inr (.inl h5),
        by rw [aoc_ciQuint _ _ _ _ _]; exact hfin,
      hsig (aoc_ciQuint _ _ _ _ _) (sig_ciQuint _ _ _ _ _),
          by rw [ctp_ciQuint _ _ _ _ _]; exact .inr rfl,
      fun _ ↦ ctp_ciQuint _ _ _ _ _, ?_, fun _ ↦ ?_⟩,
          hstd (aoc_ciQuint _ _ _ _ _) (sig_ciQuint _ _ _ _ _)⟩
    · rw [h5, ctp_ciQuint _ _ _ _ _]
      refine iff_of_false (hne 5 3 (by omega)) ?_
      rintro (⟨h, -⟩ | h)
      · rw [sig_ciQuint _ _ _ _ _] at h
        exact hs0 h
      · exact ct_ne_dct h.symm
    · have hucf : ucflvldcn (ciQuint (surjX (aoc U) W c) (surjSig c) dct u lf) = u :=
        ucflvldcn_ciQuint _ _ _ _ _
      have hdr : ucfdr (ciQuint (surjX (aoc U) W c) (surjSig c) dct u lf) = lf := ucfdr_ciQuint _ _
          _ _ _
      refine ⟨by rw [hucf]; exact hu1, by rw [ucflvl, hucf]; exact hu2,
        by rw [ucfdcn, ucflvl, hucf, aoc_ciQuint _ _ _ _ _]; exact hu3,
        by rw [ucfdcn, hucf]; exact hu4,
        .inl hdr, iff_of_true h5 hdr, fun h ↦ (hne 5 6 (by omega) (h5.symm.trans h)).elim⟩

end SurjStd

section SurjUcf

variable {Q X U σ : M}

/-- `ucfOrLast` of an element of `stduoci_1` with nonempty signature is a node -/
theorem ucfOrLast_facts (hU : U ∈ stduoci ((1 : ℕ) : M)) (hs : sig U ≠ ∅) :
    IsOrderedPair (ucfOrLast U) ∧ lvl (ucfOrLast U) ∈ succ ((1 : ℕ) : M) ∧
      dcn (ucfOrLast U) ∈ ndOf (aoc U ﹫ lvl (ucfOrLast U)) := by
  have hUu := uociCond_of_mem_stduoci_one hU
  obtain ⟨-, -, -, ⟨hsf, -, hdom, hsc⟩, -, -, -, hucf⟩ := hUu
  by_cases h3 : ((3 : ℕ) : M) ∈ dom U
  · rw [ucfOrLast, if_pos h3]
    obtain ⟨h1, h2, h3', -⟩ := hucf h3
    exact ⟨h1, h2, h3'⟩
  · rw [ucfOrLast, if_neg h3]
    have hdV : dom (sig U) ≠ ∅ := fun h0 ↦ hs (hsf.isRelation.eq_empty_of_dom_eq_empty h0)
    have hm := (sUnion_mem_of_ne_empty hdom hdV).right.left
    obtain ⟨hp, -, -, -, -⟩ := hsc _ hm
    have hl := siglvl_eq_one hU hm
    refine ⟨hp, ?_, ?_⟩
    · have : lvl (sig U ﹫ ⋃₀ dom (sig U)) = ((1 : ℕ) : M) := hl.left
      rw [this]; exact mem_succ_self _
    · have h1 : lvl (sig U ﹫ ⋃₀ dom (sig U)) = ((1 : ℕ) : M) := hl.left
      rw [h1]
      exact hl.right

theorem tpOrig_zero_eq (hX : X ∈ aotci ((1 : ℕ) : M)) (y : M) :
    tpOrig X ∅ y = ⋃₀ ndOf (X ﹫ ∅) := by
  obtain ⟨l, hnd, -⟩ := exists_ndOf_eq_of_mem_otci_empty
    (val_mem_otci_of_mem_aotci hX (mem_succ_of_mem empty_mem_natCast_one))
  rw [hnd, sUnion_singleton]
  ext z
  rw [mem_tpOrig_iff]
  constructor
  · rintro ⟨w, hw, -, hz⟩
    rw [hnd, mem_singleton_iff] at hw
    rwa [hw] at hz
  · intro hz
    exact ⟨_, by rw [hnd]; exact mem_singleton _, .inl rfl, hz⟩

theorem isUcfOf_tpUcfZero (hX : X ∈ aotci ((1 : ℕ) : M)) : IsUcfOf X (tpUcfZero X) := by
  obtain ⟨l, hnd, -⟩ := exists_ndOf_eq_of_mem_otci_empty
    (val_mem_otci_of_mem_aotci hX (mem_succ_of_mem empty_mem_natCast_one))
  rw [tpUcfZero]
  refine ⟨⟨_, _, rfl⟩, by rw [lvl_orderedPair]; exact mem_succ_of_mem empty_mem_natCast_one, ?_, ?_⟩
  · rw [lvl_orderedPair, dcn_orderedPair, hnd, sUnion_singleton]
    exact mem_singleton _
  · rw [dcn_orderedPair, hnd, sUnion_singleton, uc_orderedPair, otci0Uc, ctp_ciTriple]

/-- The `ucf` given by condition (c) is valid -/
theorem isUcfOf_embUcf (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hX : X ∈ aotci ((1 : ℕ) : M))
    (hU : U ∈ stduoci ((1 : ℕ) : M)) (hs : sig U ≠ ∅)
    (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc U) (tensorProdATwoAOne Q X)) :
    IsUcfOf X (embUcf Q X U σ) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hA := aoc_mem_aotci_of_mem_stduoci_one hU
  have hBX := tensorProdATwoAOne_mem_aotci hQ hX
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  obtain ⟨-, hl, hd⟩ := ucfOrLast_facts hU hs
  rw [embUcf, embUcfAux]
  by_cases h0 : lvl (ucfOrLast U) = ∅
  · rw [if_pos h0]
    exact isUcfOf_tpUcfZero hX
  rw [if_neg h0]
  have h1 : lvl (ucfOrLast U) = ((1 : ℕ) : M) := (mem_succ_one_cases hl).resolve_left h0
  rw [h1] at hd ⊢
  have hy := emb_val_mem hA hBX hσ hd
  rw [tpUcf]
  by_cases hT : IsTpTwo Q X ((σ ﹫ ((1 : ℕ) : M)) ﹫ dcn (ucfOrLast U))
  · rw [if_pos hT]
    obtain ⟨q, hq, hqr, h, hh, hye⟩ := mem_tensorProdTwoAOneNds_iff'.mp hT
    rw [hye, tpUcfTwo, nodeU_orderedPair, nodeH_orderedPair, tpUcfAux]
    have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
    have hsq : sig (uc q) ≠ ∅ := fun h0 ↦ by
      have h' := empty_mem_depOf_of_not_mem_rtOf (otciCond_two hQ2).left hq hqr
      rw [← dom_sig_uc_eq_depOf hQ2 hq, h0, dom_empty] at h'
      exact notin_empty _ h'
    obtain ⟨-, hl', hd'⟩ := ucfOrLast_facts hUq hsq
    refine ⟨⟨_, _, rfl⟩, by rw [lvl_orderedPair]; exact hl', ?_⟩
    rw [lvl_orderedPair, dcn_orderedPair]
    rcases mem_succ_one_cases hl' with h0' | h1'
    · rw [h0', tpOrig_zero_eq hX]
      obtain ⟨l, hnd, -⟩ := exists_ndOf_eq_of_mem_otci_empty
        (val_mem_otci_of_mem_aotci hX (mem_succ_of_mem empty_mem_natCast_one))
      rw [hnd, sUnion_singleton]
      exact ⟨mem_singleton _, by rw [uc_orderedPair, otci0Uc, ctp_ciTriple]⟩
    · rw [h1'] at hd' ⊢
      obtain ⟨v, hv, hhv⟩ := exists_relabelOne_eq hX hh hd'
      rw [hhv, tpOrig_one_relabelOne hX hv, uc_eq_dctUZero_of_mem_otci_one hX1 hv,
        dctUZero_eq_lfTrvUoci, ctp_lfTrvUoci]
      exact ⟨hv, rfl⟩
  · rw [if_neg hT]
    exact isUcfOf_tpUcfZero hX

end SurjUcf

section SurjCtr

variable {Q B W c U σW : M}

/-- The entries of the signatures of the images under `σ_W` -/
theorem entries_of_embTpSigs (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hW : W ∈ aotci ((1 : ℕ) : M))
    (hU : U ∈ stduoci ((1 : ℕ) : M)) {x : M}
    (hx : x ∈ ctrSet (embTpSigs Q W U σW)) :
    ∃ e ∈ ndOf (W ﹫ ((1 : ℕ) : M)), x = !(((1 : ℕ) : M), e) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hss := isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hU) W σW
  obtain ⟨i, hi, j, hj, rfl⟩ := (mem_ctrSet_iff hss).mp hx
  rw [dom_embTpSigs] at hi
  rw [embTpSigs_val hU hi] at hj ⊢
  by_cases hT : IsTpTwo Q W ((σW ﹫ ((1 : ℕ) : M)) ﹫ sigdcn U i)
  · obtain ⟨q, hq, -, g, hg, hye⟩ := mem_tensorProdTwoAOneNds_iff'.mp hT
    rw [hye] at hT hj ⊢
    rw [dom_tpSig_eq hT] at hj
    have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
    obtain ⟨e, he, hge⟩ := exists_relabelOne_eq hW hg (siglvl_eq_one hUq hj).right
    rw [tpSig_val_eq hQ hT hj, hge, tpOrig_one_relabelOne hW he]
    exact ⟨e, he, rfl⟩
  · rw [tpSig_eq_empty_of_not_isTpTwo hT, dom_empty] at hj
    exact (notin_empty _ hj).elim

/-- The entries of the images under `σ_W` are entries of the contraction -/
theorem entriesIn_of_contraction (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hU : U ∈ stduoci ((1 : ℕ) : M))
    (hc : IsContraction (embTpSigs Q W U σW) c) {w : M}
    (hw : w ∈ ndOf (aoc U ﹫ ((1 : ℕ) : M))) (hT : IsTpTwo Q W ((σW ﹫ ((1 : ℕ) : M)) ﹫ w)) :
    ∀ u ∈ ndOf (aoc (uc (nodeQ ((σW ﹫ ((1 : ℕ) : M)) ﹫ w))) ﹫ ((1 : ℕ) : M)),
      EntriesIn W c (nodeH ((σW ﹫ ((1 : ℕ) : M)) ﹫ w)) u := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hss := isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hU) W σW
  obtain ⟨i, hi, -, rfl⟩ := exists_sigdcn_eq hU hw
  obtain ⟨q, hq, -, g, hg, hye⟩ := mem_tensorProdTwoAOneNds_iff'.mp hT
  rw [hye] at hT ⊢
  rw [nodeQ_orderedPair, nodeH_orderedPair]
  intro u hu
  have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
  obtain ⟨j, hj, -, rfl⟩ := exists_sigdcn_eq hUq hu
  unfold EntriesIn
  rw [hc.right.right.right.left, mem_ctrSet_iff hss]
  refine ⟨i, by rw [dom_embTpSigs]; exact hi, j, ?_, ?_⟩
  · rw [embTpSigs_val hU hi, hye, dom_tpSig_eq hT]; exact hj
  · rw [embTpSigs_val hU hi, hye, tpSig_val_eq hQ hT hj]

/-- The signatures of the pulled-back images are the entries mapped by
`x ↦ (1, (dctUZero, c⁻¹(x)))` -/
theorem embTpSigs_surj_val (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hB : B ∈ aotci ((1 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) (hU : U ∈ stduoci ((1 : ℕ) : M))
    (hσW : σW ∈ aotciEmbSet ((1 : ℕ) : M) (aoc U) (tensorProdATwoAOne Q W))
    (hcon : IsContraction (embTpSigs Q W U σW) c) (hc : IsEntrySeq W c) {i : M}
    (hi : i ∈ dom (sig U)) :
    dom (embTpSigs Q (surjX B W c) U (embMk (aoc U) (tensorProdATwoAOne Q (surjX B W c))
        (surjSigOne Q W c⁻¹ (surjX B W c) σW (aoc U))) ﹫ i) =
      dom (embTpSigs Q W U σW ﹫ i) ∧
    ∀ j ∈ dom (embTpSigs Q W U σW ﹫ i),
      (embTpSigs Q (surjX B W c) U (embMk (aoc U) (tensorProdATwoAOne Q (surjX B W c))
        (surjSigOne Q W c⁻¹ (surjX B W c) σW (aoc U))) ﹫ i) ﹫ j =
      !(((1 : ℕ) : M), !(dctUZero, c⁻¹ ﹫ ((embTpSigs Q W U σW ﹫ i) ﹫ j))) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hX := hc.surjX_mem hB hW
  have hw := (siglvl_eq_one hU hi).right
  have hA := aoc_mem_aotci_of_mem_stduoci_one hU
  rw [embTpSigs_val hU hi, embTpSigs_val hU hi, embMk_val_one, surjSigOne_val _ _ _ _ _ hw]
  by_cases hT : IsTpTwo Q W ((σW ﹫ ((1 : ℕ) : M)) ﹫ sigdcn U i)
  · have hent := entriesIn_of_contraction hQ hU hcon hw hT
    obtain ⟨q, hq, hqr, g, hg, hye⟩ := mem_tensorProdTwoAOneNds_iff'.mp hT
    rw [hye] at hT hent ⊢
    rw [nodeQ_orderedPair, nodeH_orderedPair] at hent
    have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
    have hAq := aoc_mem_aotci_of_mem_stduoci_one hUq
    have hh := pullEmb_mem hB hW hc hAq hg hent
    have hyN : !(dctUZero, !(q, embMk (aoc (uc q)) (tensorProdTwoAOneTgt (surjX B W c))
        (pullOne c⁻¹ W g))) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (surjX B W c) :=
      mem_tensorProdTwoAOneNds_iff'.mpr ⟨q, hq, hqr, _, hh, rfl⟩
    rw [pullNd, if_pos hT, nodeQ_orderedPair, nodeH_orderedPair, dom_tpSig_eq hyN,
      dom_tpSig_eq hT]
    refine ⟨rfl, fun j hj ↦ ?_⟩
    obtain ⟨-, hgd⟩ := embChg_val_one_isFunction hg
    have hu := (siglvl_eq_one hUq hj).right
    obtain ⟨k, hk⟩ := (⟨_, rfl⟩ : ∃ k, k = c⁻¹ ﹫ !(((1 : ℕ) : M), tpOrig W ((1 : ℕ) : M)
      ((g ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) j)))
    have hkd : k ∈ dom c := by rw [hk]; exact (hc.inv_val (hent _ hu)).left
    rw [tpSig_val_eq hQ hyN hj, tpSig_val_eq hQ hT hj, embMk_val_one,
      (pullOne_spec c⁻¹ W g).right.right _ (by rw [hgd]; exact hu), ← hk,
      tpOrig_one_relabelOne hX (by rw [ndOf_surjX_val_one hB]; exact mem_surjNds_iff.mpr ⟨k, hkd,
          rfl⟩)]
  · have hb : (σW ﹫ ((1 : ℕ) : M)) ﹫ sigdcn U i ∈
        ndOf (tensorProdATwoAOneBase Q (surjX B W c) ﹫ ((1 : ℕ) : M)) := by
      rw [base_val_one_congr Q _ W]
      rcases (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hW).mp
        (emb_val_mem hA (tensorProdATwoAOne_mem_aotci hQ hW) hσW hw) with h | h
      · exact h
      · exact (hT h).elim
    rw [pullNd, if_neg hT, tpSig_eq_empty_of_not_isTpTwo hT,
      tpSig_eq_empty_of_not_isTpTwo (not_mem_upper_of_mem_base hQ hb)]
    exact ⟨rfl, fun j hj ↦ by rw [dom_empty] at hj; exact (notin_empty _ hj).elim⟩

/-- The contraction of the signatures of the pulled-back images is the rebuilt signature -/
theorem contraction_surj (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hB : B ∈ aotci ((1 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) (hU : U ∈ stduoci ((1 : ℕ) : M))
    (hσW : σW ∈ aotciEmbSet ((1 : ℕ) : M) (aoc U) (tensorProdATwoAOne Q W))
    (hcon : IsContraction (embTpSigs Q W U σW) c) (hc : IsEntrySeq W c) :
    contraction (embTpSigs Q (surjX B W c) U (embMk (aoc U) (tensorProdATwoAOne Q (surjX B W c))
      (surjSigOne Q W c⁻¹ (surjX B W c) σW (aoc U)))) = surjSig c := by
  have hdω := dom_sig_mem_omega_of_mem_stduoci_one hU
  have hs := isFinSeqSeq_embTpSigs hQ hdω W σW
  have hs' := isFinSeqSeq_embTpSigs hQ hdω (surjX B W c) (embMk (aoc U)
    (tensorProdATwoAOne Q (surjX B W c)) (surjSigOne Q W c⁻¹ (surjX B W c) σW (aoc U)))
  obtain ⟨hsf, hsd, hsv⟩ := surjSig_spec c
  have hran := hcon.right.right.right.left
  refine (eq_contraction_of_isContraction hs' (isContraction_map
    (fun x ↦ !(((1 : ℕ) : M), !(dctUZero, c⁻¹ ﹫ x))) hs hs'
    (by rw [dom_embTpSigs, dom_embTpSigs])
    (fun i hi ↦ (embTpSigs_surj_val hQ hB hW hU hσW hcon hc (by rwa [dom_embTpSigs] at hi)).left)
    (fun i hi ↦ (embTpSigs_surj_val hQ hB hW hU hσW hcon hc (by rwa [dom_embTpSigs] at hi)).right)
    (fun x hx y hy h ↦ ?_) hcon hsf hsd fun k hk ↦ ?_)).symm
  · rw [← hran] at hx hy
    simp only [orderedPair_eq_orderedPair_iff, true_and] at h
    rw [← (hc.inv_val hx).right, ← (hc.inv_val hy).right, h]
  · rw [hsv k hk, hc.isBijection.inv_val_val hk]

end SurjCtr

section SurjHelpers

theorem isSetRestrictedTo_unrel_val (τ D : M) :
    IsSetRestrictedTo (fun w ↦ unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w)) D := by
  have : ClassFunction.Definable (fun w ↦ unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w)) Set.univ :=
    ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ p z : M, p = τ ∧
      z = (p ﹫ ((1 : ℕ) : M)) ﹫ xs 0 ∧ unrel z = xs 1) fun u w ↦ by
        constructor
        · rintro ⟨p, z, rfl, rfl, h⟩
          exact h
        · intro h
          exact ⟨_, _, rfl, rfl, h⟩
  exact isSetRestrictedTo_of_definable _

/-- The nodes of `(X ⊗ Z)(1)` are relabeled nodes of `X(1)` -/
theorem relabelOne_unrel_of_mem_tgt {X y : M} (hX : X ∈ aotci ((1 : ℕ) : M))
    (hy : y ∈ ndOf (tensorProdTwoAOneTgt X ﹫ ((1 : ℕ) : M))) :
    unrel y ∈ ndOf (X ﹫ ((1 : ℕ) : M)) ∧ relabelOne trvAZero (unrel y) = y := by
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hX1] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  rw [unrel_relabelOne ((isSLOT_of_mem_otci hX1).isOrderedPair hw)]
  exact ⟨hw, rfl⟩

end SurjHelpers

section SurjMain

/-- The embedding `w ↦ ρ⁻¹(τ(w))` of `A` into `B`, for `τ` into `B ⊗ Z` -/
noncomputable def unrelEmb (A B τ : M) : M :=
  embMk A B ((fun w ↦ unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w)) ↾₀ ndOf (A ﹫ ((1 : ℕ) : M)))

/-- The embedding `σ_W` pulled back to the rebuilt target of the entries `c` -/
noncomputable def surjSigma (Q W U σW c : M) : M :=
  embMk (aoc U) (tensorProdATwoAOne Q (surjX (aoc U) W c))
    (surjSigOne Q W c⁻¹ (surjX (aoc U) W c) σW (aoc U))

/-- Condition (b) for the rebuilt target to be continuous -/
def SurjCt (Q X U σ : M) : Prop :=
  ctp U = ct ∧ TpCt Q X ((σ ﹫ siglvl U (⋃₀ dom (sig U))) ﹫ sigdcn U (⋃₀ dom (sig U))) ∧
    EndsWithNew (embTpSigs Q X U σ)

noncomputable instance (Q X U σ : M) : Decidable (SurjCt Q X U σ) := Classical.propDecidable _

/-- The rebuilt target `V`: continuous iff condition (b) holds, otherwise with the `ucf` from
condition (c) -/
noncomputable def surjV (Q W U σ c : M) : M :=
  if SurjCt Q (surjX (aoc U) W c) U σ then ciTriple (surjX (aoc U) W c) (surjSig c) ct
  else ciQuint (surjX (aoc U) W c) (surjSig c) dct (embUcf Q (surjX (aoc U) W c) U σ) lf

/-- The upper node of `(T ⊗ Q) ⊗ W` rebuilt from `t`, `σ_W` and the entries `c` -/
noncomputable def isoPreOf (Q W t σW c : M) : M :=
  !(dctUZero, !(!(surjV Q W (uc t) (surjSigma Q W (uc t) σW c) c,
    !(t, surjSigma Q W (uc t) σW c)), surjPsi (aoc (uc t)) W c))

/-- The preimage of the upper node `(t, τ)` of `T ⊗ (Q ⊗ W)` -/
noncomputable def isoPre (Q W t τ : M) : M :=
  isoPreOf Q W t (unrelEmb (aoc (uc t)) (tensorProdATwoAOne Q W) τ)
    (contraction (embTpSigs Q W (uc t) (unrelEmb (aoc (uc t)) (tensorProdATwoAOne Q W) τ)))

variable {T Q W : M}

theorem surjV_spec (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hW : W ∈ aotci ((1 : ℕ) : M)) {U σ c : M}
    (hU : U ∈ stduoci ((1 : ℕ) : M)) (hsU : sig U ≠ ∅) (hc : IsEntrySeq W c) (hm : dom c ≠ ∅)
    (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc U) (tensorProdATwoAOne Q (surjX (aoc U) W c))) :
    surjV Q W U σ c ∈ stduoci ((1 : ℕ) : M) ∧ aoc (surjV Q W U σ c) = surjX (aoc U) W c ∧
      sig (surjV Q W U σ c) = surjSig c ∧
      (ctp (surjV Q W U σ c) = ct ↔ ctp U = ct ∧ TpCt Q (surjX (aoc U) W c)
        ((σ ﹫ siglvl U (⋃₀ dom (sig U))) ﹫ sigdcn U (⋃₀ dom (sig U))) ∧
        EndsWithNew (embTpSigs Q (surjX (aoc U) W c) U σ)) ∧
      (((3 : ℕ) : M) ∈ dom (surjV Q W U σ c) →
        ucflvldcn (surjV Q W U σ c) = embUcf Q (surjX (aoc U) W c) U σ ∧
          ucfdr (surjV Q W U σ c) = lf) := by
  have hX := hc.surjX_mem (aoc_mem_aotci_of_mem_stduoci_one hU) hW
  unfold surjV
  by_cases hct : SurjCt Q (surjX (aoc U) W c) U σ
  · rw [if_pos hct]
    refine ⟨surjV_mem_stduoci hU hW hc hm (.inl rfl), aoc_ciTriple _ _ _,
      sig_ciTriple _ _ _, iff_of_true (ctp_ciTriple _ _ _) hct, fun h ↦ ?_⟩
    rw [dom_ciTriple] at h
    exact (notMem_self _ h).elim
  · rw [if_neg hct]
    exact ⟨surjV_mem_stduoci hU hW hc hm (.inr ⟨_, isUcfOf_embUcf hQ hX hU hsU hσ, rfl⟩),
      aoc_ciQuint _ _ _ _ _, sig_ciQuint _ _ _ _ _,
      iff_of_false (by rw [ctp_ciQuint]; exact fun h ↦ ct_ne_dct h.symm) hct,
      fun _ ↦ ⟨ucflvldcn_ciQuint _ _ _ _ _, ucfdr_ciQuint _ _ _ _ _⟩⟩

/-- The rebuilt node from an embedding `σ_W` into `Q ⊗ W` and the contraction `c` of its
entries is an upper node with image `(t, τ)` -/
theorem isoPreOf_spec (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {t τ : M} (ht : t ∈ ndOf (T ﹫ 2)) (htr : t ∉ rtOf (T ﹫ 2))
    (hτ : τ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t))
      (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W)))
    {σW c : M} (hσW : σW ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q W))
    (hσWv : ∀ w ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)),
      (σW ﹫ ((1 : ℕ) : M)) ﹫ w = unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w))
    (hcon : IsContraction (embTpSigs Q W (uc t) σW) c)
    (hup : ∃ w ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)),
      unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w) ∈ tensorProdTwoAOneNds (Q ﹫ 2) W) :
    isoPreOf Q W t σW c ∈ tensorProdTwoAOneNds (tensorProdTwoTwo (T ﹫ 2) Q) W ∧
      isoOne T Q W (isoPreOf Q W t σW c) = !(dctUZero, !(t, τ)) := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hA := aoc_mem_aotci_of_mem_stduoci_one hUt
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hTB := tensorProdTwoAOneTgt_mem hBW
  have hz (w : M) (hw : w ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) :=
    relabelOne_unrel_of_mem_tgt hBW (emb_val_mem hA hTB hτ hw)
  have hc : IsEntrySeq W c := ⟨hcon.left, hcon.right.left, hcon.right.right.left, fun k hk ↦
    entries_of_embTpSigs hQ hW hUt (by
      rw [← hcon.right.right.right.left]; exact (hcon.left.mem_ran_iff _).mpr ⟨k, hk, rfl⟩)⟩
  have hent (w : M) (hw : w ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) :=
    entriesIn_of_contraction hQ hUt hcon hw
  have hm : dom c ≠ ∅ := by
    obtain ⟨w, hw, hwu⟩ := hup
    rw [← hσWv w hw] at hwu
    have he := hent w hw hwu
    obtain ⟨q, hq, hqr, g, -, hye⟩ := mem_tensorProdTwoAOneNds_iff'.mp hwu
    rw [hye, nodeQ_orderedPair, nodeH_orderedPair] at he
    have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
    have h0 := empty_mem_depOf_of_not_mem_rtOf (otciCond_two hQ2).left hq hqr
    rw [← dom_sig_uc_eq_depOf hQ2 hq] at h0
    have h' := he _ (siglvl_eq_one hUq h0).right
    unfold EntriesIn at h'
    rw [hcon.left.mem_ran_iff] at h'
    obtain ⟨k, hk, -⟩ := h'
    intro h0'
    rw [h0'] at hk
    exact notin_empty _ hk
  -- the rebuilt target, embeddings and node
  have hX := hc.surjX_mem hA hW
  have hσ : surjSigma Q W (uc t) σW c ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t))
      (tensorProdATwoAOne Q (surjX (aoc (uc t)) W c)) := surjSig_mem hQ hA hW hc hA hσW hent
  have hψ := surjPsi_mem hA hW hc
  have hcontr : contraction (embTpSigs Q (surjX (aoc (uc t)) W c) (uc t)
      (surjSigma Q W (uc t) σW c)) = surjSig c := contraction_surj hQ hA hW hUt hσW hcon hc
  have hσ1 : surjSigma Q W (uc t) σW c ﹫ ((1 : ℕ) : M) =
      surjSigOne Q W c⁻¹ (surjX (aoc (uc t)) W c) σW (aoc (uc t)) := embMk_val_one _ _ _
  rw [isoPreOf]
  generalize surjSigma Q W (uc t) σW c = σ at hσ hcontr hσ1 ⊢
  have hsU : sig (uc t) ≠ ∅ := fun h0 ↦ by
    have h' := empty_mem_depOf_of_not_mem_rtOf (otciCond_two hP).left ht htr
    rw [← dom_sig_uc_eq_depOf hP ht, h0, dom_empty] at h'
    exact notin_empty _ h'
  obtain ⟨hsf, hsd, -⟩ := surjSig_spec c
  -- the rebuilt target `V`: continuous iff condition (b) holds, otherwise with `ucf` from (c)
  obtain ⟨hV, haV, hsV, hctp, hucf⟩ := surjV_spec hQ hW hUt hsU hc hm hσ
  generalize surjV Q W (uc t) σ c = V at hV haV hsV hctp hucf ⊢
  have hxN : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds (T ﹫ 2) Q := by
    rw [pair_mem_tensorProdTwoTwoNds_iff]
    refine ⟨ht, hV, by rw [haV]; exact hσ, ⟨⟨by rw [haV]; exact hσ, by rw [haV, hcontr, hsV],
      by rw [haV]; exact hctp, by rw [haV]; exact hucf⟩, fun h0 ↦ ?_⟩⟩
    rw [hsV] at h0
    exact (hm (by rw [← hsd, h0, dom_empty])).elim
  have hxr : !(V, !(t, σ)) ∉ rtOf (tensorProdTwoTwo (T ﹫ 2) Q) := by
    rw [mem_rtOf_tensorProdTwoTwo_iff hxN, uc_orderedPair, hsV, hsd]
    exact hm
  have ha : !(dctUZero, !(!(V, !(t, σ)), surjPsi (aoc (uc t)) W c)) ∈
      tensorProdTwoAOneNds (tensorProdTwoTwo (T ﹫ 2) Q) W :=
    mem_tensorProdTwoAOneNds_iff'.mpr ⟨_, by rw [ndOf_tensorProdTwoTwo]; exact hxN, hxr, _,
      by rw [uc_orderedPair, haV]; exact hψ, rfl⟩
  refine ⟨ha, ?_⟩
  rw [isoOne_up ha, lbl_orderedPair, left_orderedPair, right_orderedPair, isoUp_orderedPair,
    isoUpOf, haV]
  have heq : tauEmb Q (surjX (aoc (uc t)) W c) W (aoc (uc t)) (surjPsi (aoc (uc t)) W c) σ = τ := by
    refine eq_of_mem_aotciEmbSet_one hUt hTB (tauEmb_mem hQ hX hW hA hσ hψ) hτ fun i hi ↦ ?_
    have hw := (siglvl_eq_one hUt hi).right
    rw [(siglvl_eq_one hUt hi).left, tauEmb_val_one hσ hw, hσ1, surjSigOne_val _ _ _ _ _ hw,
      (pullNd_spec hQ hA hW hc (emb_val_mem hA hBW hσW hw) (hent _ hw)).right, hσWv _ hw,
      (hz _ hw).right]
  rw [heq]

/-- (Surjectivity, upper part) An upper node `(t, τ)` of `T ⊗ (Q ⊗ W)` with a value from
`Q(2)` is the image of the upper node `isoPre Q W t τ` of `(T ⊗ Q) ⊗ W` -/
theorem isoPre_spec (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {t τ : M} (ht : t ∈ ndOf (T ﹫ 2)) (htr : t ∉ rtOf (T ﹫ 2))
    (hτ : τ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t))
      (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W)))
    (hup : ∃ w ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)),
      unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w) ∈ tensorProdTwoAOneNds (Q ﹫ 2) W) :
    isoPre Q W t τ ∈ tensorProdTwoAOneNds (tensorProdTwoTwo (T ﹫ 2) Q) W ∧
      isoOne T Q W (isoPre Q W t τ) = !(dctUZero, !(t, τ)) := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hA := aoc_mem_aotci_of_mem_stduoci_one hUt
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hTB := tensorProdTwoAOneTgt_mem hBW
  have hz (w : M) (hw : w ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) :=
    relabelOne_unrel_of_mem_tgt hBW (emb_val_mem hA hTB hτ hw)
  have hres := isSetRestrictedTo_unrel_val τ (ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)))
  have hfv (w : M) (hw : w ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) :
      ((fun w ↦ unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w)) ↾₀ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) ﹫ w =
        unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w) := val_toSetRestrictedTo hres hw
  have hσW : unrelEmb (aoc (uc t)) (tensorProdATwoAOne Q W) τ ∈ aotciEmbSet ((1 : ℕ) : M)
      (aoc (uc t)) (tensorProdATwoAOne Q W) :=
    embMk_mem_aotciEmbSet' hA hBW (isFunction_toSetRestrictedTo hres)
    (dom_toSetRestrictedTo hres) (fun w hw ↦ by rw [hfv w hw]; exact (hz w hw).left)
    (fun w hw w' hw' hww' ↦ by
      rw [hfv w hw, hfv w' hw']
      have h := emb_odr hA hTB hτ hw hw' hww'
      rwa [← (hz w hw).right, ← (hz w' hw').right,
        rel_tgt_relabel_iff hBW (hz w hw).left (hz w' hw').left] at h)
  have hσWv (w : M) (hw : w ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) :
      (unrelEmb (aoc (uc t)) (tensorProdATwoAOne Q W) τ ﹫ ((1 : ℕ) : M)) ﹫ w =
        unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w) := by rw [unrelEmb, embMk_val_one, hfv w hw]
  exact isoPreOf_spec hT hQ hW ht htr hτ hσW hσWv (isContraction_contraction
    (isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUt) W _)) hup

end SurjMain

section Assembly

variable {T Q W : M}

/-- (Surjectivity) Every node of `(T ⊗ (Q ⊗ W))(1)` is an image -/
theorem isoOne_surj (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {r : M}
    (hr : r ∈ ndOf (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))) :
    ∃ a ∈ ndOf (tensorProdATwoAOne (tensorProdATwoATwo T Q) W ﹫ ((1 : ℕ) : M)),
      isoOne T Q W a = r := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hF := tensorProdATwoATwo_mem_aotci hT hQ
  have hQ2 := restrict_two_mem_aotci_one hQ
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hF1 : tensorProdATwoATwo T Q ﹫ ((1 : ℕ) : M) =
      tensorProdATwoAOne T (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M) := tensorProdATwoATwo_val_one hT hQ
  have hlow {a₀ : M} (ha₀ : a₀ ∈ ndOf (tensorProdATwoAOne T (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M))) :
      relabelOne trvAZero a₀ ∈
        ndOf (tensorProdATwoAOne (tensorProdATwoATwo T Q) W ﹫ ((1 : ℕ) : M)) := by
    rw [← hF1] at ha₀
    exact (mem_ndOf_tensorProdATwoAOne_val_one_iff hF hW).mpr (.inl (relabelOne_mem_base hF W ha₀))
  rcases (mem_ndOf_tensorProdATwoAOne_iff' hT hBW).mp hr with ⟨w, hw, rfl⟩ | hr
  · refine ⟨_, hlow ((mem_ndOf_tensorProdATwoAOne_val_one_iff hT hQ2).mpr
      (.inl (relabelOne_mem_base hT _ hw))), isoOne_low hT hQ hw⟩
  obtain ⟨t, ht, htr, τ, hτ, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp hr
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hA := aoc_mem_aotci_of_mem_stduoci_one hUt
  have hTB := tensorProdTwoAOneTgt_mem hBW
  have hB0 := tensorProdATwoAOneBase_mem_aotci hQ W
  have hz (w : M) (hw : w ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) :=
    relabelOne_unrel_of_mem_tgt hBW (emb_val_mem hA hTB hτ hw)
  by_cases hup : ∃ w ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)),
      unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w) ∈ tensorProdTwoAOneNds (Q ﹫ 2) W
  · obtain ⟨ha, hae⟩ := isoPre_spec hT hQ hW ht htr hτ hup
    refine ⟨_, ?_, hae⟩
    rw [← tensorProdATwoATwo_val_two hT hQ] at ha
    exact (mem_ndOf_tensorProdATwoAOne_val_one_iff hF hW).mpr (.inr ha)
  -- all values from `Q(1)`
  have hbase (w : M) (hw : w ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) :
      unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w) ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M)) := by
    rcases (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hW).mp (hz w hw).left with h | h
    · exact h
    · exact (hup ⟨w, hw, h⟩).elim
  have hres := isSetRestrictedTo_unrel_val τ (ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)))
  have hfv (w : M) (hw : w ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) :
      ((fun w ↦ unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w)) ↾₀ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) ﹫ w =
        unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w) := val_toSetRestrictedTo hres hw
  have hf := embMk_mem_aotciEmbSet' hA hB0 (isFunction_toSetRestrictedTo hres)
    (dom_toSetRestrictedTo hres) (fun w hw ↦ by rw [hfv w hw]; exact hbase w hw)
    (fun w hw w' hw' hww' ↦ by
      rw [hfv w hw, hfv w' hw']
      have h := emb_odr hA hTB hτ hw hw' hww'
      rw [← (hz w hw).right, ← (hz w' hw').right, rel_tgt_relabel_iff hBW (hz w hw).left
        (hz w' hw').left, rel_base_iff hQ hW (hbase w hw) (hbase w' hw')] at h
      exact h)
  have hf1 : (embMk (aoc (uc t)) (tensorProdATwoAOneBase Q W)
      ((fun w ↦ unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w)) ↾₀ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) ﹫
        ((1 : ℕ) : M)) = (fun w ↦ unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w)) ↾₀
          ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)) := embMk_val_one _ _ _
  generalize embMk (aoc (uc t)) (tensorProdATwoAOneBase Q W)
    ((fun w ↦ unrel ((τ ﹫ ((1 : ℕ) : M)) ﹫ w)) ↾₀ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) = f at hf hf1
  rw [← tgt_restrict_eq_base Q W] at hf
  have hy : !(dctUZero, !(t, f)) ∈ tensorProdTwoAOneNds (T ﹫ 2) (Q ↾ (2 : M)) :=
    mem_tensorProdTwoAOneNds_iff'.mpr ⟨t, ht, htr, f, hf, rfl⟩
  refine ⟨_, hlow ((mem_ndOf_tensorProdATwoAOne_val_one_iff hT hQ2).mpr (.inr hy)), ?_⟩
  have heq : tauEmb Q W W (aoc (uc t)) ∅ f = τ := by
    refine eq_of_mem_aotciEmbSet_one hUt hTB (tauEmb_base_mem hQ hW hA hf) hτ fun i hi ↦ ?_
    have hw := (siglvl_eq_one hUt hi).right
    rw [(siglvl_eq_one hUt hi).left, (tauEmb_base_val (W := W) hQ hA hf hw).left, hf1,
      hfv _ hw, (hz _ hw).right]
  rw [isoOne_mid hT hQ hy, isoMid, heq]

/-- The level-`1` part `ρρw ↦ ρw`, `ρ(t, f) ↦ (t, ρ ∘ f)`, `((V, (t, σ)), ψ) ↦ (t, ρ ∘ Φ_ψ ∘ σ)`
of the canonical isomorphism `(T ⊗ Q) ⊗ W → T ⊗ (Q ⊗ W)` -/
noncomputable def tensorProdAssocOne (T Q W : M) : M :=
  (fun a ↦ isoOne T Q W a) ↾₀ ndOf (tensorProdATwoAOne (tensorProdATwoATwo T Q) W ﹫ ((1 : ℕ) : M))

/-- The canonical isomorphism `(T ⊗ Q) ⊗ W → T ⊗ (Q ⊗ W)` -/
noncomputable def tensorProdAssocIso (T Q W : M) : M :=
  embMk (tensorProdATwoAOne (tensorProdATwoATwo T Q) W)
    (tensorProdATwoAOne T (tensorProdATwoAOne Q W)) (tensorProdAssocOne T Q W)

/-- The canonical map is an isomorphism `(T ⊗ Q) ⊗ W ≅ T ⊗ (Q ⊗ W)` -/
theorem isAotciIsomorphism_tensorProdAssocIso (hT : T ∈ aotci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hW : W ∈ aotci ((1 : ℕ) : M)) :
    IsAotciIsomorphism ((1 : ℕ) : M) (tensorProdATwoAOne (tensorProdATwoATwo T Q) W)
      (tensorProdATwoAOne T (tensorProdATwoAOne Q W)) (tensorProdAssocIso T Q W) := by
  have hF := tensorProdATwoATwo_mem_aotci hT hQ
  have hL := tensorProdATwoAOne_mem_aotci hF hW
  have hR := tensorProdATwoAOne_mem_aotci hT (tensorProdATwoAOne_mem_aotci hQ hW)
  have hres : IsSetRestrictedTo (fun a ↦ isoOne T Q W a)
      (ndOf (tensorProdATwoAOne (tensorProdATwoATwo T Q) W ﹫ ((1 : ℕ) : M))) :=
    isSetRestrictedTo_of_definable _
  have hemb := embMk_mem_aotciEmbSet' hL hR (isFunction_toSetRestrictedTo hres)
    (dom_toSetRestrictedTo hres) (fun a ha ↦ by
      rw [val_toSetRestrictedTo hres ha]; exact isoOne_mem hT hQ hW ha)
    (fun a ha b hb hab ↦ by
      rw [val_toSetRestrictedTo hres ha, val_toSetRestrictedTo hres hb]
      exact isoOne_lt hT hQ hW ha hb hab)
  obtain ⟨-, he⟩ := mem_aotciEmbSet_iff.mp hemb
  refine ⟨he.isFunction, he.dom_eq, fun {i} hi ↦ ⟨he.isOtciEmbedding hi, ?_⟩⟩
  rcases mem_succ_one_cases hi with rfl | rfl
  · rw [tensorProdAssocIso, embMk_val_zero]
    exact (isOtciIsomorphism_otciSngIso_of_mem_otci_empty
      (val_mem_otci_of_mem_aotci hL (mem_succ_of_mem empty_mem_natCast_one))
      (val_mem_otci_of_mem_aotci hR (mem_succ_of_mem empty_mem_natCast_one))).ran_eq
  · rw [tensorProdAssocIso, embMk_val_one, tensorProdAssocOne]
    ext r
    rw [mem_ran_toSetRestrictedTo_iff hres]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact isoOne_mem hT hQ hW ha
    · exact isoOne_surj hT hQ hW

end Assembly

section IsoFinal

variable {T Q W : M}

/-- `(T ⊗ Q) ⊗ W ≅ T ⊗ (Q ⊗ W)` for `T, Q ∈ aotci_2` and `W ∈ aotci_1` -/
theorem exists_isAotciIsomorphism_tensorProdATwoATwo (hT : T ∈ aotci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hW : W ∈ aotci ((1 : ℕ) : M)) :
    ∃ π, IsAotciIsomorphism ((1 : ℕ) : M) (tensorProdATwoAOne (tensorProdATwoATwo T Q) W)
      (tensorProdATwoAOne T (tensorProdATwoAOne Q W)) π :=
  ⟨_, isAotciIsomorphism_tensorProdAssocIso hT hQ hW⟩

end IsoFinal

end FirstOrder.Language.MemStructure
