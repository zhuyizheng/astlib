/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.IsoUpper
/-!
# The canonical map preserves the order

The images of the upper nodes are in the Brouwer–Kleene order of the nodes (`rel_isoUp_of_bkLt`),
the images `isoMid` of the base nodes, and the level-`1` map `isoOne` preserving the order.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M]

section AncLtDef

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ embRestrict (xs 0) (xs 1) = xs 2)
    Set.univ := by
  obtain ⟨G, hG⟩ : ∃ G : ClassFunction M,
      G = fun z : M ↦ embRestrict (left z) (right z) := ⟨_, rfl⟩
  have : G.Definable Set.univ := by
    rw [hG]
    infer_instance
  have h : (fun xs : Fin 3 → M ↦ embRestrict (xs 0) (xs 1) = xs 2) = fun xs ↦
      ∃ z : M, z = !(xs 0, xs 1) ∧ G z = xs 2 := by
    funext xs
    apply propext
    rw [hG]
    simp only [left_orderedPair, right_orderedPair, exists_eq_left]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ embRestrict (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ embRestrict (xs i) (xs j) = xs k) =
      Multiclass.remap (fun ys : Fin 3 → M ↦ embRestrict (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The image of `(x, ψ)` is below that of the ancestor of `x` at depth `k`, with `ψ` restricted -/
def AncLtAt (Q W R F x ψ k : M) : Prop :=
  ∃ A U φ a b : M, ancOf F x k = A ∧ U = uc A ∧ embRestrict U ψ = φ ∧ isoUp Q W x ψ = a ∧
    isoUp Q W A φ = b ∧ !(a, b) ∈ R

instance : Multiclass.Definable
    (fun xs : Fin 7 → M ↦ AncLtAt (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6)) Set.univ := by
  unfold AncLtAt
  infer_instance

instance {n : ℕ} (i j k l m o u : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ AncLtAt (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ AncLtAt (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u)) =
      Multiclass.remap (fun ys : Fin 7 → M ↦
        AncLtAt (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6)) ![i, j, k, l, m, o, u] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `AncLtAt` for all nonzero `k < n` -/
def AncLtK (Q W R F x ψ n : M) : Prop := ∀ k ∈ n, k ≠ ∅ → AncLtAt Q W R F x ψ k

instance : Multiclass.Definable
    (fun xs : Fin 7 → M ↦ AncLtK (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6)) Set.univ := by
  unfold AncLtK
  infer_instance

instance {n : ℕ} (i j k l m o u : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ AncLtK (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ AncLtK (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u)) =
      Multiclass.remap (fun ys : Fin 7 → M ↦
        AncLtK (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6)) ![i, j, k, l, m, o, u] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `AncLtK` for all embeddings of the node `x` -/
def AncLtNd (Q W R F TW x n : M) : Prop :=
  ∀ ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc x)) TW, AncLtK Q W R F x ψ n

instance : Multiclass.Definable
    (fun xs : Fin 7 → M ↦ AncLtNd (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6)) Set.univ := by
  have h : (fun xs : Fin 7 → M ↦ AncLtNd (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6)) =
      fun xs ↦ ∃ o A : M, o = ((1 : ℕ) : M) ∧ A = aoc (uc (xs 5)) ∧
        ∀ ψ, ψ ∈ aotciEmbSet o A (xs 4) → AncLtK (xs 0) (xs 1) (xs 2) (xs 3) (xs 5) ψ (xs 6) := by
    funext xs
    simp [AncLtNd]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m o u : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ AncLtNd (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ AncLtNd (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u)) =
      Multiclass.remap (fun ys : Fin 7 → M ↦
        AncLtNd (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6)) ![i, j, k, l, m, o, u] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `AncLtNd` for all nodes of depth `n` -/
def AncLtCond (Q W R F TW n : M) : Prop :=
  ∀ x ∈ ndOf F, depOf F x = n → AncLtNd Q W R F TW x n

instance (Q W R F TW : M) : Class.Definable (fun n : M ↦ AncLtCond Q W R F TW n) Set.univ := by
  have h : (fun n : M ↦ AncLtCond Q W R F TW n) = fun n : M ↦ ∃ Q' W' R' F' T' N : M,
      Q' = Q ∧ W' = W ∧ R' = R ∧ F' = F ∧ T' = TW ∧ N = ndOf F ∧
      ∀ x ∈ N, depOf F' x = n → AncLtNd Q' W' R' F' T' x n := by
    funext n
    simp [AncLtCond]
  rw [h]
  infer_instance

end AncLtDef

section UpOrder

variable {T Q W : M}

/-- `ρ ∘ Φ_ψ ∘ σ` only depends on the values of `ψ` on `X(1)` -/
theorem tauEmb_congr (hQ : Q ∈ aotci ((2 : ℕ) : M)) {X A σ ψ ψ' : M}
    (hX : X ∈ aotci ((1 : ℕ) : M)) (hA : A ∈ aotci ((1 : ℕ) : M))
    (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) A (tensorProdATwoAOne Q X))
    (hagr : ∀ v ∈ ndOf (X ﹫ ((1 : ℕ) : M)),
      (ψ' ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ ﹫ ((1 : ℕ) : M)) ﹫ v) :
    tauEmb Q X W A ψ' σ = tauEmb Q X W A ψ σ := by
  unfold tauEmb
  congr 1
  obtain ⟨hf, hd, hv⟩ := tauOne_spec Q X W ψ' σ
  obtain ⟨hf', hd', hv'⟩ := tauOne_spec Q X W ψ σ
  refine hf.ext hf' (by rw [hd, hd']) fun w hw ↦ ?_
  rw [hd] at hw
  have hσd := (embChg_val_one_isFunction hσ).right
  rw [hv w hw, hv' w hw, pushNd_old hQ hX hX rfl (isSubOne_refl _) hagr
    (emb_val_mem hA (tensorProdATwoAOne_mem_aotci hQ hX) hσ (by rw [← hσd]; exact hw))]

theorem isoUp_orderedPair (Q W V t σ ψ : M) :
    isoUp Q W !(V, !(t, σ)) ψ = isoUpOf Q W V t σ ψ := by
  rw [isoUp, uc_orderedPair, nodeQ_orderedPair, nodeH_orderedPair]

/-- The image of `(x, ψ)` only depends on the values of `ψ` on `x_uc` -/
theorem isoUp_congr {P : M} (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {x ψ ψ' : M} (hx : x ∈ tensorProdTwoTwoNds P Q)
    (hagr : ∀ v ∈ ndOf (aoc (uc x) ﹫ ((1 : ℕ) : M)),
      (ψ' ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ ﹫ ((1 : ℕ) : M)) ﹫ v) :
    isoUp Q W x ψ' = isoUp Q W x ψ := by
  obtain ⟨t, ht, V, hV, σ, hσ, -, rfl⟩ := mem_tensorProdTwoTwoNds_iff.mp hx
  rw [uc_orderedPair] at hagr
  rw [isoUp_orderedPair, isoUp_orderedPair, isoUpOf, isoUpOf,
    tauEmb_congr hQ (aoc_mem_aotci_of_mem_stduoci_one hV)
      (aoc_mem_aotci_of_mem_stduoci_one (uc_mem_stduoci_of_mem_otci_two hP ht)) hσ hagr]

/-- The order of the images of upper nodes from the Brouwer–Kleene order of their sequences -/
theorem rel_isoUpOf_of_bkLt (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {V t σ ψ V' t' σ' ψ' : M}
    (hx : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds (T ﹫ 2) Q) (hs : sig V ≠ ∅)
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W))
    (hx' : !(V', !(t', σ')) ∈ tensorProdTwoTwoNds (T ﹫ 2) Q) (hs' : sig V' ≠ ∅)
    (hψ' : ψ' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V') (tensorProdTwoAOneTgt W))
    (h : BKLt (tensorProdTwoAOneCoordOdr (T ﹫ 2) (tensorProdATwoAOne Q W))
      (tensorProdTwoAOneSeq (T ﹫ 2) !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ))
      (tensorProdTwoAOneSeq (T ﹫ 2) !(t', tauEmb Q (aoc V') W (aoc (uc t')) ψ' σ'))) :
    (isoUpOf Q W V t σ ψ) [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
      (isoUpOf Q W V' t' σ' ψ') := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  rw [rel_odrOne_tensorProdATwoAOne_iff_of_mem hT (tensorProdATwoAOne_mem_aotci hQ hW)
    (isoUpOf_mem hP hQ hW hx hs hψ)]
  refine ⟨isoUpOf_mem hP hQ hW hx' hs' hψ', ?_⟩
  unfold TensorProdTwoAOneLt
  rw [isoUpOf, isoUpOf, lbl_orderedPair, lbl_orderedPair]
  exact h

/-- The image of an upper node is a node of the level-`1` tree -/
theorem isoUpOf_mem_ndOf (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {V t σ ψ : M}
    (hx : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds (T ﹫ 2) Q) (hs : sig V ≠ ∅)
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W)) :
    isoUpOf Q W V t σ ψ ∈ ndOf (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)) := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  exact (mem_ndOf_tensorProdATwoAOne_val_one_iff hT (tensorProdATwoAOne_mem_aotci hQ hW)).mpr
    (.inr (isoUpOf_mem hP hQ hW hx hs hψ))

/-- (I1) The image of `(x, ψ)` is below that of every proper non-root ancestor of `x`, with `ψ`
restricted -/
theorem ancLtAt_of_mem (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {x ψ k : M}
    (hx : x ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc x)) (tensorProdTwoAOneTgt W))
    (hk : k ∈ depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) (hk0 : k ≠ ∅) :
    AncLtAt Q W (odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)))
      (tensorProdTwoTwo (T ﹫ 2) Q) x ψ k := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hF := tensorProdTwoTwo_mem_otci hP hQ
  have hFs : IsSLOT (tensorProdTwoTwo (T ﹫ 2) Q) := (otciCond_two hF).left
  have hS : (SLOTreeStructure.ofM (tensorProdTwoTwo (T ﹫ 2) Q)).IsSLOTreeStructure := hFs
  have hTS := hS.isTreeStructure
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hTW := tensorProdTwoAOneTgt_mem hW
  have hR := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci
    (tensorProdATwoAOne_mem_aotci hT hBW) (mem_succ_self _))).left
  change IsStrictLinearOrder (odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫
    ((1 : ℕ) : M))) _ at hR
  suffices h : AncLtCond Q W
      (odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)))
      (tensorProdTwoTwo (T ﹫ 2) Q) (tensorProdTwoAOneTgt W)
      (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) from h x hx rfl ψ hψ k hk hk0
  refine omega_induction (A := fun n ↦ AncLtCond Q W
      (odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)))
      (tensorProdTwoTwo (T ﹫ 2) Q) (tensorProdTwoAOneTgt W) n)
    (fun x _ _ ψ _ k hk ↦ (notin_empty _ hk).elim) (fun n hn ih x hx hd ψ hψ k hk hk0 ↦ ?_)
    (hTS.dep_mem_omega hx)
  have hno : Ordinal n := ordinal_of_mem ordinal_omega hn
  have hn0 : n ≠ ∅ := by
    intro h0
    rw [h0, mem_succ_iff] at hk
    rcases hk with h | h
    · exact hk0 h
    · exact notin_empty _ h
  have hns : n ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) := by
    rw [hd]; exact mem_succ_of_mem (mem_succ_self n)
  obtain ⟨hC, hdC⟩ := hTS.anc_mem_nd hx hns
  change ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q) at hC
  change depOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n) = n at hdC
  have hxC : x ∈ chdOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n) := by
    have h' : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ n) ∈
        chdOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n) :=
      hTS.anc_succ_mem_chd hx (by
        change n ∈ depOf (tensorProdTwoTwo (T ﹫ 2) Q) x
        rw [hd]; exact mem_succ_self n)
    have hxd : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) = x :=
      hTS.anc_dep hx
    rwa [← hd, hxd] at h'
  have hCN := hC
  rw [ndOf_tensorProdTwoTwo] at hCN
  rw [mem_chdOf_tensorProdTwoTwo_iff hCN] at hxC
  obtain ⟨hxN, -, hprt⟩ := hxC
  have hsub := (uc_ancOf_rel hF hx hns).right
  have hψC := embRestrict_mem_aotciEmbSet hF hx hns hTW hψ
  have hdx := dom_sig_uc_eq_depOf hF hx
  have hdCs := dom_sig_uc_eq_depOf hF hC
  rw [hd] at hdx
  rw [hdC] at hdCs
  have hψ1 := embChg_val_one_isFunction hψ
  have hagr : ∀ v ∈ ndOf (aoc (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)) ﹫ ((1 : ℕ) : M)),
      (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)) ψ ﹫ ((1 : ℕ) : M)) ﹫ v =
        (ψ ﹫ ((1 : ℕ) : M)) ﹫ v := fun v hv ↦ by
    rw [embRestrict_val _ _ natCast_one_mem_two, val_restrict _ hψ1.left hv
      (by rw [hψ1.right]; exact hsub.left hv)]
  -- the step from `x` to its parent
  have hstep : (isoUp Q W x ψ)
      [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
      (isoUp Q W (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)
        (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)) ψ)) := by
    obtain ⟨tC, -, VC, -, σC, -, -, hCe⟩ := mem_tensorProdTwoTwoNds_iff.mp hCN
    obtain ⟨t, -, V, -, σ, -, -, rfl⟩ := mem_tensorProdTwoTwoNds_iff.mp hxN
    rw [hCe] at hprt hagr hψC hdCs ⊢
    rw [uc_orderedPair] at hψ hagr hψC hdx hdCs ⊢
    rw [isoUp_orderedPair, isoUp_orderedPair]
    have hm0 : ⋃₀ dom (sig V) ≠ ∅ := by rw [hdx, sUnion_succ hno.transitive]; exact hn0
    have hsC : sig VC ≠ ∅ := fun h0 ↦ hn0 (by rw [← hdCs, h0, dom_empty])
    have hs : sig V ≠ ∅ := fun h0 ↦ by
      have h' := hdx
      rw [h0, dom_empty] at h'
      exact notin_empty n (by rw [h']; exact mem_succ_self n)
    exact rel_isoUpOf_of_bkLt hT hQ hW hxN hs hψ (by rw [← hCe]; exact hCN) hsC hψC (bkLt_isoUp_chd
        hP hQ hW hxN hm0 hprt hψ hagr)
  rw [mem_succ_iff] at hk
  rcases hk with hkn | hkn
  · subst hkn
    exact ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, hstep⟩
  · -- `k < n`: the induction hypothesis at the parent
    obtain ⟨A, U, φ, a, b, hA, hU, hφ, ha, hb, hab⟩ :=
      ih _ hC hdC _ hψC k hkn hk0
    have hks : k ∈ succ n := mem_succ_of_mem hkn
    rw [ancOf_ancOf hFs hx hns hks] at hA
    subst hA hU hφ ha hb
    have hkx : k ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) := by
      rw [hd]; exact mem_succ_of_mem hks
    obtain ⟨hAn, -⟩ := hTS.anc_mem_nd hx hkx
    change ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q) at hAn
    have hAN := hAn
    rw [ndOf_tensorProdTwoTwo] at hAN
    obtain ⟨-, hsubA⟩ := uc_ancOf_rel hF hx hkx
    have hψC1 := embChg_val_one_isFunction hψC
    have hcong : isoUp Q W (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)
        (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k))
          (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)) ψ)) =
        isoUp Q W (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)
          (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)) ψ) := by
      refine isoUp_congr hP hQ hAN fun v hv ↦ ?_
      have hvx := hsubA.left hv
      have hvC : v ∈ ndOf (aoc (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)) ﹫ ((1 : ℕ) : M)) := by
        refine (uc_ancOf_rel hF hC (by rw [hdC]; exact hks)).right.left ?_
        rw [ancOf_ancOf hFs hx hns hks]
        exact hv
      rw [embRestrict_val (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)) _ natCast_one_mem_two,
        val_restrict _ hψC1.left hv (by rw [hψC1.right]; exact hvC), hagr v hvC,
        embRestrict_val (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)) ψ natCast_one_mem_two,
        val_restrict _ hψ1.left hv (by rw [hψ1.right]; exact hvx)]
    refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [← hcong]
    exact hR.right.right.left.trans (hR.mem_left hstep) (hR.mem_right hstep) (hR.mem_right hab)
      hstep hab

end UpOrder


section DescLtDef

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ tensorProdATwoAOne (xs 0) (xs 1) = xs 2)
    Set.univ := by
  obtain ⟨G, hG⟩ : ∃ G : ClassFunction M,
      G = fun z : M ↦ tensorProdATwoAOne (left z) (right z) := ⟨_, rfl⟩
  have : G.Definable Set.univ := by
    rw [hG]
    infer_instance
  have h : (fun xs : Fin 3 → M ↦ tensorProdATwoAOne (xs 0) (xs 1) = xs 2) = fun xs ↦
      ∃ z : M, z = !(xs 0, xs 1) ∧ G z = xs 2 := by
    funext xs
    apply propext
    rw [hG]
    simp only [left_orderedPair, right_orderedPair, exists_eq_left]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ tensorProdATwoAOne (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tensorProdATwoAOne (xs i) (xs j) = xs k) =
      Multiclass.remap (fun ys : Fin 3 → M ↦ tensorProdATwoAOne (ys 0) (ys 1) = ys 2)
        ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `z` is the image `ρ(Φ_ψ(b))` of an old node `b` of `(Q ⊗ X)(1)` -/
def IsOldImg (Q X W ψ z : M) : Prop :=
  ∃ b ∈ ndOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M)), z = relabelOne trvAZero (pushNd Q X W ψ b)

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ IsOldImg (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)) Set.univ := by
  have h : (fun xs : Fin 5 → M ↦ IsOldImg (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)) = fun xs ↦
      ∃ C o N : M, tensorProdATwoAOne (xs 0) (xs 1) = C ∧ o = ((1 : ℕ) : M) ∧ N = ndOf (C ﹫ o) ∧
        ∃ b ∈ N, ∃ p : M, pushNd (xs 0) (xs 1) (xs 2) (xs 3) b = p ∧
          relabelOne trvAZero p = xs 4 := by
    funext xs
    apply propext
    constructor
    · rintro ⟨b, hb, hz⟩
      exact ⟨_, _, _, rfl, rfl, rfl, b, hb, _, rfl, hz.symm⟩
    · rintro ⟨C, o, N, rfl, rfl, rfl, b, hb, p, rfl, hz⟩
      exact ⟨b, hb, hz.symm⟩
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ IsOldImg (xs i) (xs j) (xs k) (xs l) (xs m)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsOldImg (xs i) (xs j) (xs k) (xs l) (xs m)) =
      Multiclass.remap (fun ys : Fin 5 → M ↦
        IsOldImg (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)) ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The coordinate `i` of the level-`1` map `τ₁` on the signature of `U` is an old image -/
def OldAt (Q X W ψ τ₁ U i : M) : Prop := IsOldImg Q X W ψ (τ₁ ﹫ sigdcn U i)

instance : Multiclass.Definable
    (fun xs : Fin 7 → M ↦ OldAt (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6)) Set.univ := by
  have h : (fun xs : Fin 7 → M ↦ OldAt (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6)) =
      fun xs ↦ ∃ w z : M, w = sigdcn (xs 5) (xs 6) ∧ z = xs 4 ﹫ w ∧
        IsOldImg (xs 0) (xs 1) (xs 2) (xs 3) z := by
    funext xs
    simp [OldAt]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m o u : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ OldAt (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ OldAt (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u)) =
      Multiclass.remap (fun ys : Fin 7 → M ↦
        OldAt (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6)) ![i, j, k, l, m, o, u] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- All coordinates of the label `y = (t, τ)` are images of old nodes -/
def OldSeq (Pt Q X W ψ y : M) : Prop :=
  ∀ i ∈ depOf Pt (left y), OldAt Q X W ψ (right y ﹫ ((1 : ℕ) : M)) (uc (left y)) i

instance : Multiclass.Definable
    (fun xs : Fin 6 → M ↦ OldSeq (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5)) Set.univ := by
  have h : (fun xs : Fin 6 → M ↦ OldSeq (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5)) = fun xs ↦
      ∃ t τ₁ U D : M, t = left (xs 5) ∧ τ₁ = right (xs 5) ﹫ ((1 : ℕ) : M) ∧ U = uc t ∧
        D = depOf (xs 0) t ∧ ∀ i ∈ D, OldAt (xs 1) (xs 2) (xs 3) (xs 4) τ₁ U i := by
    funext xs
    simp [OldSeq]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m o : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ OldSeq (xs i) (xs j) (xs k) (xs l) (xs m) (xs o)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ OldSeq (xs i) (xs j) (xs k) (xs l) (xs m) (xs o)) =
      Multiclass.remap (fun ys : Fin 6 → M ↦
        OldSeq (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)) ![i, j, k, l, m, o] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- An upper node `b₀` with old coordinates below `a` is below `c` -/
def DescLtAll (Pt Q W R X φ a c NU : M) : Prop :=
  ∀ b₀ ∈ NU, OldSeq Pt Q X W φ (lbl b₀) → !(b₀, a) ∈ R → !(b₀, c) ∈ R

instance : Multiclass.Definable (fun xs : Fin 9 → M ↦
    DescLtAll (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6) (xs 7) (xs 8)) Set.univ := by
  have h : (fun xs : Fin 9 → M ↦
      DescLtAll (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6) (xs 7) (xs 8)) = fun xs ↦
      ∀ b₀ ∈ xs 8, ∃ y : M, y = lbl b₀ ∧ (OldSeq (xs 0) (xs 1) (xs 4) (xs 2) (xs 5) y →
        !(b₀, xs 6) ∈ xs 3 → !(b₀, xs 7) ∈ xs 3) := by
    funext xs
    simp [DescLtAll]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m o u v w : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    DescLtAll (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u) (xs v) (xs w)) Set.univ := by
  have h : (fun xs : Fin n → M ↦
      DescLtAll (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u) (xs v) (xs w)) =
      Multiclass.remap (fun ys : Fin 9 → M ↦
        DescLtAll (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8))
        ![i, j, k, l, m, o, u, v, w] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `DescLtAll` for the images of `(A, φ)` and `(x, ψ)` -/
def DescLt₂ (Pt Q W R NU A U φ x ψ : M) : Prop :=
  ∃ X a c : M, X = aoc U ∧ isoUp Q W A φ = a ∧ isoUp Q W x ψ = c ∧ DescLtAll Pt Q W R X φ a c NU

instance : Multiclass.Definable (fun xs : Fin 10 → M ↦
    DescLt₂ (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6) (xs 7) (xs 8) (xs 9)) Set.univ := by
  unfold DescLt₂
  infer_instance

instance {n : ℕ} (i j k l m o u v w a : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    DescLt₂ (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u) (xs v) (xs w) (xs a)) Set.univ := by
  have h : (fun xs : Fin n → M ↦
      DescLt₂ (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u) (xs v) (xs w) (xs a)) =
      Multiclass.remap (fun ys : Fin 10 → M ↦
        DescLt₂ (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9))
        ![i, j, k, l, m, o, u, v, w, a] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `DescLt₂` for the ancestor `A` of `x` at depth `k` and `φ = ψ` restricted -/
def DescLtAt (Pt Q W R F NU x ψ k : M) : Prop :=
  ∃ A U φ : M, ancOf F x k = A ∧ U = uc A ∧ embRestrict U ψ = φ ∧ DescLt₂ Pt Q W R NU A U φ x ψ

instance : Multiclass.Definable (fun xs : Fin 9 → M ↦
    DescLtAt (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6) (xs 7) (xs 8)) Set.univ := by
  unfold DescLtAt
  infer_instance

instance {n : ℕ} (i j k l m o u v w : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    DescLtAt (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u) (xs v) (xs w)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ DescLtAt (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u) (xs v)
      (xs w)) =
      Multiclass.remap (fun ys : Fin 9 → M ↦ DescLtAt (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys
          6) (ys 7) (ys 8))
        ![i, j, k, l, m, o, u, v, w] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

end DescLtDef

section DescLt

variable {T Q W : M}

/-- `DescLtAt` for all nonzero `k < n` -/
def DescLtK (Pt Q W R F NU x ψ n : M) : Prop := ∀ k ∈ n, k ≠ ∅ → DescLtAt Pt Q W R F NU x ψ k

instance : Multiclass.Definable (fun xs : Fin 9 → M ↦
    DescLtK (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6) (xs 7) (xs 8)) Set.univ := by
  unfold DescLtK
  infer_instance

instance {n : ℕ} (i j k l m o u v w : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    DescLtK (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u) (xs v) (xs w)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ DescLtK (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u) (xs v)
      (xs w)) =
      Multiclass.remap (fun ys : Fin 9 → M ↦ DescLtK (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys
          6) (ys 7) (ys 8))
        ![i, j, k, l, m, o, u, v, w] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `DescLtK` for all embeddings of `x` -/
def DescLtNd (Pt Q W R F NU TW x n : M) : Prop :=
  ∀ ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc x)) TW, DescLtK Pt Q W R F NU x ψ n

instance : Multiclass.Definable (fun xs : Fin 9 → M ↦
    DescLtNd (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6) (xs 7) (xs 8)) Set.univ := by
  have h : (fun xs : Fin 9 → M ↦
      DescLtNd (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6) (xs 7) (xs 8)) = fun xs ↦
      ∃ o A : M, o = ((1 : ℕ) : M) ∧ A = aoc (uc (xs 7)) ∧
        ∀ ψ, ψ ∈ aotciEmbSet o A (xs 6) →
          DescLtK (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 7) ψ (xs 8) := by
    funext xs
    simp [DescLtNd]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m o u v w : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    DescLtNd (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u) (xs v) (xs w)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ DescLtNd (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u) (xs v)
      (xs w)) =
      Multiclass.remap (fun ys : Fin 9 → M ↦ DescLtNd (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys
          6) (ys 7) (ys 8))
        ![i, j, k, l, m, o, u, v, w] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `DescLtNd` for all nodes of depth `n` -/
def DescLtCond (Pt Q W R F NU TW n : M) : Prop :=
  ∀ x ∈ ndOf F, depOf F x = n → DescLtNd Pt Q W R F NU TW x n

instance (Pt Q W R F NU TW : M) :
    Class.Definable (fun n : M ↦ DescLtCond Pt Q W R F NU TW n) Set.univ := by
  have h : (fun n : M ↦ DescLtCond Pt Q W R F NU TW n) = fun n : M ↦ ∃ Pt' Q' W' R' F' NU' TW' N :
      M,
      Pt' = Pt ∧ Q' = Q ∧ W' = W ∧ R' = R ∧ F' = F ∧ NU' = NU ∧ TW' = TW ∧ N = ndOf F ∧
      ∀ x ∈ N, depOf F' x = n → DescLtNd Pt' Q' W' R' F' NU' TW' x n := by
    funext n
    simp [DescLtCond]
  rw [h]
  infer_instance

end DescLt

section DescLtProof

variable {T Q W : M}

theorem rel_isoUpOf_iff_bkLt (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {b₀ : M}
    (hb : b₀ ∈ tensorProdTwoAOneNds (T ﹫ 2) (tensorProdATwoAOne Q W)) {V t σ ψ : M}
    (hx : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds (T ﹫ 2) Q) (hs : sig V ≠ ∅)
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W)) :
    b₀ [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
        (isoUpOf Q W V t σ ψ) ↔
      BKLt (tensorProdTwoAOneCoordOdr (T ﹫ 2) (tensorProdATwoAOne Q W))
        (tensorProdTwoAOneSeq (T ﹫ 2) (lbl b₀))
        (tensorProdTwoAOneSeq (T ﹫ 2) !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ)) := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  rw [rel_odrOne_tensorProdATwoAOne_iff_of_mem hT (tensorProdATwoAOne_mem_aotci hQ hW) hb]
  unfold TensorProdTwoAOneLt
  have hl : lbl (isoUpOf Q W V t σ ψ) = !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ) := by
    rw [isoUpOf, lbl_orderedPair]
  rw [hl]
  exact ⟨fun h ↦ h.right, fun h ↦ ⟨isoUpOf_mem hP hQ hW hx hs hψ, h⟩⟩

/-- Old images for `(X', ψ')` are old images for an extension `(X, ψ)` -/
theorem isOldImg_of_isSubOne (hQ : Q ∈ aotci ((2 : ℕ) : M)) {X X' ψ ψ' z : M}
    (hX : X ∈ aotci ((1 : ℕ) : M)) (hX' : X' ∈ aotci ((1 : ℕ) : M)) (h0 : X ﹫ ∅ = X' ﹫ ∅)
    (hsub : IsSubOne (X' ﹫ ((1 : ℕ) : M)) (X ﹫ ((1 : ℕ) : M)))
    (hagr : ∀ v ∈ ndOf (X' ﹫ ((1 : ℕ) : M)),
      (ψ' ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ ﹫ ((1 : ℕ) : M)) ﹫ v)
    (h : IsOldImg Q X' W ψ' z) : IsOldImg Q X W ψ z := by
  obtain ⟨b, hb, rfl⟩ := h
  exact ⟨b, (isSubOne_tensorProdATwoAOne hQ hX hX' h0 hsub).left hb,
    by rw [pushNd_old hQ hX hX' h0 hsub hagr hb]⟩

/-- (G*) An upper node with coordinates old for an ancestor `A` of `x` that is below the image of
`A` is below the image of `x` -/
theorem descLtAt_of_mem (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {x ψ k : M}
    (hx : x ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc x)) (tensorProdTwoAOneTgt W))
    (hk : k ∈ depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) (hk0 : k ≠ ∅) :
    DescLtAt (T ﹫ 2) Q W
      (odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)))
      (tensorProdTwoTwo (T ﹫ 2) Q) (tensorProdTwoAOneNds (T ﹫ 2) (tensorProdATwoAOne Q W))
      x ψ k := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hF := tensorProdTwoTwo_mem_otci hP hQ
  have hFs : IsSLOT (tensorProdTwoTwo (T ﹫ 2) Q) := (otciCond_two hF).left
  have hS : (SLOTreeStructure.ofM (tensorProdTwoTwo (T ﹫ 2) Q)).IsSLOTreeStructure := hFs
  have hTS := hS.isTreeStructure
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hTW := tensorProdTwoAOneTgt_mem hW
  suffices h : DescLtCond (T ﹫ 2) Q W
      (odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)))
      (tensorProdTwoTwo (T ﹫ 2) Q) (tensorProdTwoAOneNds (T ﹫ 2) (tensorProdATwoAOne Q W))
      (tensorProdTwoAOneTgt W) (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) from
    h x hx rfl ψ hψ k hk hk0
  refine omega_induction (A := fun n ↦ DescLtCond (T ﹫ 2) Q W
      (odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)))
      (tensorProdTwoTwo (T ﹫ 2) Q) (tensorProdTwoAOneNds (T ﹫ 2) (tensorProdATwoAOne Q W))
      (tensorProdTwoAOneTgt W) n)
    (fun x _ _ ψ _ k hk ↦ (notin_empty _ hk).elim) (fun n hn ih x hx hd ψ hψ k hk hk0 ↦ ?_)
    (hTS.dep_mem_omega hx)
  have hno : Ordinal n := ordinal_of_mem ordinal_omega hn
  have hn0 : n ≠ ∅ := by
    intro h0
    rw [h0, mem_succ_iff] at hk
    rcases hk with h | h
    · exact hk0 h
    · exact notin_empty _ h
  have hns : n ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) := by
    rw [hd]; exact mem_succ_of_mem (mem_succ_self n)
  obtain ⟨hC, hdC⟩ := hTS.anc_mem_nd hx hns
  change ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q) at hC
  change depOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n) = n at hdC
  have hxC : x ∈ chdOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n) := by
    have h' : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ n) ∈
        chdOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n) :=
      hTS.anc_succ_mem_chd hx (by
        change n ∈ depOf (tensorProdTwoTwo (T ﹫ 2) Q) x
        rw [hd]; exact mem_succ_self n)
    have hxd : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) = x :=
      hTS.anc_dep hx
    rwa [← hd, hxd] at h'
  have hCN := hC
  rw [ndOf_tensorProdTwoTwo] at hCN
  rw [mem_chdOf_tensorProdTwoTwo_iff hCN] at hxC
  obtain ⟨hxN, -, hprt⟩ := hxC
  have hsub := (uc_ancOf_rel hF hx hns).right
  have hψC := embRestrict_mem_aotciEmbSet hF hx hns hTW hψ
  have hdx := dom_sig_uc_eq_depOf hF hx
  have hdCs := dom_sig_uc_eq_depOf hF hC
  rw [hd] at hdx
  rw [hdC] at hdCs
  have hψ1 := embChg_val_one_isFunction hψ
  have hagr : ∀ v ∈ ndOf (aoc (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)) ﹫ ((1 : ℕ) : M)),
      (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)) ψ ﹫ ((1 : ℕ) : M)) ﹫ v =
        (ψ ﹫ ((1 : ℕ) : M)) ﹫ v := fun v hv ↦ by
    rw [embRestrict_val _ _ natCast_one_mem_two, val_restrict _ hψ1.left hv
      (by rw [hψ1.right]; exact hsub.left hv)]
  have hks : k ∈ succ n := by rwa [mem_succ_iff] at hk ⊢
  have hkx : k ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) := by
    rw [hd]; exact mem_succ_of_mem hks
  obtain ⟨hAn, -⟩ := hTS.anc_mem_nd hx hkx
  change ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q) at hAn
  have hkC : k ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n))
      :=
    by rw [hdC]; exact hks
  have hAC := ancOf_ancOf hFs hx hns hks
  obtain ⟨-, hsubAC⟩ := uc_ancOf_rel hF hC hkC
  rw [hAC] at hsubAC
  have hUA := uc_mem_stduoci_of_mem_otci_two hF hAn
  have hUC := uc_mem_stduoci_of_mem_otci_two hF hC
  have hXA := aoc_mem_aotci_of_mem_stduoci_one hUA
  have hXC := aoc_mem_aotci_of_mem_stduoci_one hUC
  have h0AC : aoc (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)) ﹫ ∅ =
      aoc (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)) ﹫ ∅ := by
    rw [aoc_uc_val_zero_of_mem_otci_two hF hC, aoc_uc_val_zero_of_mem_otci_two hF hAn]
  have hψC1 := embChg_val_one_isFunction hψC
  -- the restrictions of `ψ` and of `ψ_C` to `A` agree with `ψ_C`
  have hagrA : ∀ v ∈ ndOf (aoc (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)) ﹫ ((1 : ℕ) : M)),
      (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)) ψ ﹫ ((1 : ℕ) : M)) ﹫ v =
        (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)) ψ ﹫ ((1 : ℕ) : M)) ﹫ v :=
    fun v hv ↦ by
      rw [embRestrict_val (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)) ψ natCast_one_mem_two,
        val_restrict _ hψ1.left hv (by rw [hψ1.right]; exact hsub.left (hsubAC.left hv)),
        hagr v (hsubAC.left hv)]
  refine ⟨_, _, _, rfl, rfl, rfl, _, _, _, rfl, rfl, rfl, fun b₀ hb₀ hold hlt ↦ ?_⟩
  -- first `b₀` is below the image of the parent
  have hltC : b₀ [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
      (isoUp Q W (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)
        (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)) ψ)) := by
    rw [mem_succ_iff] at hks
    rcases hks with hkn | hkn
    · subst hkn
      exact hlt
    · obtain ⟨A, U, φ, hA, hU, hφ, X, a, c, hX, ha, hc, hall⟩ := ih _ hC hdC _ hψC k hkn hk0
      rw [hAC] at hA
      subst hA hU hφ hX ha hc
      refine hall b₀ hb₀ (fun i hi ↦ ?_) ?_
      · obtain ⟨b, hb, hz⟩ := hold i hi
        refine ⟨b, hb, ?_⟩
        rw [hz, pushNd_old hQ hXA hXA rfl (isSubOne_refl _) ?_ hb]
        intro v hv
        rw [hagrA v hv, embRestrict_val (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k))
          (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)) ψ) natCast_one_mem_two,
          val_restrict _ hψC1.left hv (by rw [hψC1.right]; exact hsubAC.left hv)]
      · rw [isoUp_congr (W := W)
          (ψ := embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)) ψ) hP hQ
          (by rw [← ndOf_tensorProdTwoTwo]; exact hAn) fun v hv ↦ ?_]
        · exact hlt
        · rw [embRestrict_val (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k))
            (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)) ψ) natCast_one_mem_two,
            val_restrict _ hψC1.left hv (by rw [hψC1.right]; exact hsubAC.left hv)]
          exact (hagrA v hv).symm
  -- then the gap step
  obtain ⟨tB, htB, -, τB, hτB, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp hb₀
  have hold' : ∀ i ∈ depOf (T ﹫ 2) tB, ∃ b ∈ ndOf (tensorProdATwoAOne Q
      (aoc (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n))) ﹫ ((1 : ℕ) : M)),
      (τB ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tB) i = relabelOne trvAZero (pushNd Q
        (aoc (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n))) W
        (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x n)) ψ) b) := fun i hi ↦ by
    have h' := hold i (by simp only [lbl_orderedPair, left_orderedPair]; exact hi)
    simp only [OldAt, lbl_orderedPair, left_orderedPair, right_orderedPair] at h'
    exact isOldImg_of_isSubOne hQ hXC hXA h0AC hsubAC hagrA h'
  obtain ⟨tC, -, VC, -, σC, -, -, hCe⟩ := mem_tensorProdTwoTwoNds_iff.mp hCN
  rw [hCe] at hprt hagr hψC hdCs hold' hltC
  rw [uc_orderedPair] at hagr hψC hdCs hold' hltC
  rw [isoUp_orderedPair] at hltC
  obtain ⟨t, -, V, -, σ, -, -, rfl⟩ := mem_tensorProdTwoTwoNds_iff.mp hxN
  rw [uc_orderedPair] at hψ hdx
  rw [isoUp_orderedPair]
  have hm0 : ⋃₀ dom (sig V) ≠ ∅ := by rw [hdx, sUnion_succ hno.transitive]; exact hn0
  have hsC : sig VC ≠ ∅ := fun h0 ↦ hn0 (by rw [← hdCs, h0, dom_empty])
  have hs : sig V ≠ ∅ := fun h0 ↦ by
    have h' := hdx
    rw [h0, dom_empty] at h'
    exact notin_empty n (by rw [h']; exact mem_succ_self n)
  have hCN' : !(VC, !(tC, σC)) ∈ tensorProdTwoTwoNds (T ﹫ 2) Q := by rw [← hCe]; exact hCN
  have hltC' := (rel_isoUpOf_iff_bkLt hT hQ hW hb₀ hCN' hsC hψC).mp hltC
  rw [lbl_orderedPair] at hltC'
  refine (rel_isoUpOf_iff_bkLt hT hQ hW hb₀ hxN hs hψ).mpr ?_
  rw [lbl_orderedPair]
  exact bkLt_isoUp_chd_of_old hP hQ hW hxN hm0 hprt hψ hagr htB hτB hold' hltC'

end DescLtProof

section SigMax

/-- `v` is the first node of the signature of `U` or below it -/
def IsBelowFirst (U v : M) : Prop :=
  v = sigdcn U ∅ ∨ v [odrOne (aoc U ﹫ ((1 : ℕ) : M))] (sigdcn U ∅)

instance : Multiclass.Definable (fun xs : Fin 2 → M ↦ IsBelowFirst (xs 0) (xs 1)) Set.univ := by
  have h : (fun xs : Fin 2 → M ↦ IsBelowFirst (xs 0) (xs 1)) = fun xs ↦
      ∃ w Y : M, w = sigdcn (xs 0) ∅ ∧ Y = aoc (xs 0) ﹫ ((1 : ℕ) : M) ∧
        (xs 1 = w ∨ !(xs 1, w) ∈ odrOne Y) := by
    funext xs
    simp [IsBelowFirst]
  rw [h]
  infer_instance

instance {n : ℕ} (i j : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ IsBelowFirst (xs i) (xs j)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsBelowFirst (xs i) (xs j)) =
      Multiclass.remap (fun ys : Fin 2 → M ↦ IsBelowFirst (ys 0) (ys 1)) ![i, j] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `IsBelowFirst` for all level-`1` nodes of `U` -/
def BelowFirstNd (U : M) : Prop := ∀ v ∈ ndOf (aoc U ﹫ ((1 : ℕ) : M)), IsBelowFirst U v

instance : Multiclass.Definable (fun xs : Fin 1 → M ↦ BelowFirstNd (xs 0)) Set.univ := by
  have h : (fun xs : Fin 1 → M ↦ BelowFirstNd (xs 0)) = fun xs ↦
      ∃ Y : M, Y = ndOf (aoc (xs 0) ﹫ ((1 : ℕ) : M)) ∧ ∀ v ∈ Y, IsBelowFirst (xs 0) v := by
    funext xs
    simp [BelowFirstNd]
  rw [h]
  infer_instance

instance {n : ℕ} (i : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ BelowFirstNd (xs i)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ BelowFirstNd (xs i)) =
      Multiclass.remap (fun ys : Fin 1 → M ↦ BelowFirstNd (ys 0)) ![i] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `IsBelowFirst` for all nodes of depth `n` -/
def BelowFirstCond (P n : M) : Prop :=
  ∀ t ∈ ndOf P, depOf P t = n → BelowFirstNd (uc t)

instance (P : M) : Class.Definable (fun n : M ↦ BelowFirstCond P n) Set.univ := by
  have h : (fun n : M ↦ BelowFirstCond P n) = fun n : M ↦ ∃ P' N : M, P' = P ∧ N = ndOf P ∧
      ∀ t ∈ N, depOf P' t = n → ∃ U : M, U = uc t ∧ BelowFirstNd U := by
    funext n
    simp [BelowFirstCond]
  rw [h]
  infer_instance

/-- The first node of the signature of a node of a tree of `otci_2` is the greatest level-`1` node:
every new node is placed immediately before the `ucf` -/
theorem isBelowFirst_of_mem {P t v : M} (hP : P ∈ otci ((2 : ℕ) : M)) (ht : t ∈ ndOf P)
    (hv : v ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M))) : IsBelowFirst (uc t) v := by
  have hPs : IsSLOT P := (otciCond_two hP).left
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hPs
  have hTS := hS.isTreeStructure
  suffices h : BelowFirstCond P (depOf P t) from h t ht rfl v hv
  refine omega_induction (A := fun n ↦ BelowFirstCond P n) (fun t ht hd v hv ↦ ?_)
    (fun n hn ih t ht hd v hv ↦ ?_) (hTS.dep_mem_omega ht)
  · have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
    rw [ndOf_aoc_val_one_eq hUt, mem_iniSegNds_iff, dom_sig_uc_eq_depOf hP ht, hd] at hv
    obtain ⟨i, hi, -⟩ := hv
    exact (notin_empty _ hi).elim
  have hno : Ordinal n := ordinal_of_mem ordinal_omega hn
  have hns : n ∈ succ (depOf P t) := by rw [hd]; exact mem_succ_of_mem (mem_succ_self n)
  obtain ⟨hp, hdp⟩ := hTS.anc_mem_nd ht hns
  change ancOf P t n ∈ ndOf P at hp
  change depOf P (ancOf P t n) = n at hdp
  have htp : t ∈ chdOf P (ancOf P t n) := by
    have h' : ancOf P t (succ n) ∈ chdOf P (ancOf P t n) :=
      hTS.anc_succ_mem_chd ht (by change n ∈ depOf P t; rw [hd]; exact mem_succ_self n)
    have htd : ancOf P t (depOf P t) = t := hTS.anc_dep ht
    rwa [← hd, htd] at h'
  obtain ⟨-, -, hsub, hucf⟩ := uc_rel_of_mem_chdOf hP hp htp
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hUp := uc_mem_stduoci_of_mem_otci_two hP hp
  have hdp' : dom (sig (uc (ancOf P t n))) = n := by rw [dom_sig_uc_eq_depOf hP hp, hdp]
  have hY := val_mem_otci_of_mem_aotci (aoc_mem_aotci_of_mem_stduoci_one hUt) (mem_succ_self _)
  have hR := (rtlosOf_of_mem_otci_one hY).left
  change IsStrictLinearOrder (odrOne (aoc (uc t) ﹫ ((1 : ℕ) : M))) _ at hR
  have hv' := hv
  rw [ndOf_aoc_val_one_eq hUt, mem_iniSegNds_iff, dom_sig_uc_eq_depOf hP ht, hd] at hv'
  obtain ⟨i, hi, rfl⟩ := hv'
  by_cases hn0 : n = ∅
  · subst hn0
    rw [mem_succ_iff] at hi
    rcases hi with rfl | hi
    · exact .inl rfl
    · exact (notin_empty _ hi).elim
  have h0n : (∅ : M) ∈ n := empty_mem_of_ordinal_of_ne_empty hno hn0
  have hw0 : sigdcn (uc (ancOf P t n)) ∅ = sigdcn (uc t) ∅ := sigdcn_anc hP ht hns h0n
  -- the old nodes
  have hold (j : M) (hj : j ∈ n) : IsBelowFirst (uc t) (sigdcn (uc t) j) := by
    have hjp : sigdcn (uc t) j ∈ ndOf (aoc (uc (ancOf P t n)) ﹫ ((1 : ℕ) : M)) := by
      rw [← sigdcn_anc hP ht hns hj, ndOf_aoc_val_one_eq hUp, mem_iniSegNds_iff, hdp']
      exact ⟨j, hj, rfl⟩
    rcases ih _ hp hdp _ hjp with h | h
    · rw [hw0] at h
      exact .inl h
    · rw [hw0] at h
      have hw0p : sigdcn (uc t) ∅ ∈ ndOf (aoc (uc (ancOf P t n)) ﹫ ((1 : ℕ) : M)) := by
        rw [← hw0, ndOf_aoc_val_one_eq hUp, mem_iniSegNds_iff, hdp']
        exact ⟨∅, h0n, rfl⟩
      exact .inr ((hsub.right _ hjp _ hw0p).mp h)
  rw [mem_succ_iff] at hi
  rcases hi with rfl | hi
  · -- the new node is immediately before the `ucf` of the parent
    have hsp : sig (uc (ancOf P t i)) ≠ ∅ := fun h0 ↦ hn0 (by rw [← hdp', h0, dom_empty])
    obtain ⟨-, hucfn, hlt, -⟩ := hucf hsp
    rw [hdp'] at hlt
    have hucfp := hucfn
    rw [ndOf_aoc_val_one_eq hUp, mem_iniSegNds_iff, hdp'] at hucfp
    obtain ⟨j, hj, hje⟩ := hucfp
    rw [sigdcn_anc hP ht hns hj] at hje
    have hmem (j : M) (hj : j ∈ succ i) : sigdcn (uc t) j ∈ ndOf (aoc (uc t) ﹫ ((1 : ℕ) : M)) := by
      rw [ndOf_aoc_val_one_eq hUt, mem_iniSegNds_iff, dom_sig_uc_eq_depOf hP ht, hd]
      exact ⟨j, hj, rfl⟩
    rw [← hje] at hlt
    rcases hold j hj with h | h
    · rw [h] at hlt
      exact .inr hlt
    · exact .inr (hR.right.right.left.trans (hmem _ (mem_succ_self i)) (hmem _ (mem_succ_of_mem hj))
        (hmem _ (mem_succ_of_mem h0n)) hlt h)
  · exact hold i hi

end SigMax

section RtChd

variable {P Q W : M}

/-- The image of the first signature node of `t` under `σ` comes from `Q(2)`, for a node
`(V, (t, σ))` with `V_sig ≠ ∅` -/
theorem row_zero_isTpTwo (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {V t σ : M} (hc : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q) (hs : sig V ≠ ∅) :
    ∅ ∈ depOf P t ∧ (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) ∅ ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V)
        := by
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hc
  obtain ⟨ht, hV, hσ, ⟨-, hcon, -⟩, -⟩ := hc
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hA := aoc_mem_aotci_of_mem_stduoci_one hUt
  have hBX := tensorProdATwoAOne_mem_aotci hQ hX
  have hss := isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUt) (aoc V) σ
  have hsf := (uociCond_of_mem_stduoci_one hV).right.right.right.left.left
  have hdV : dom (sig V) ≠ ∅ := fun h0 ↦ hs (hsf.isRelation.eq_empty_of_dom_eq_empty h0)
  obtain ⟨i0, hi0⟩ : ∃ i0, i0 ∈ dom (sig V) := by
    by_contra h'
    exact hdV (by
      ext z
      exact ⟨fun hz ↦ (h' ⟨z, hz⟩).elim, fun hz ↦ (notin_empty _ hz).elim⟩)
  have hran : sig V ﹫ i0 ∈ ctrSet (embTpSigs Q (aoc V) (uc t) σ) := by
    rw [← (isContraction_contraction hss).right.right.right.left, hcon]
    exact (hsf.mem_ran_iff _).mpr ⟨i0, hi0, rfl⟩
  obtain ⟨i, hi, j, hj, -⟩ := (mem_ctrSet_iff hss).mp hran
  rw [dom_embTpSigs] at hi
  rw [embTpSigs_val hUt hi] at hj
  have hwi := (siglvl_eq_one hUt hi).right
  have hTp : IsTpTwo Q (aoc V) ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i) := by
    by_contra h'
    rw [tpSig_eq_empty_of_not_isTpTwo h', dom_empty] at hj
    exact notin_empty _ hj
  have hdt : depOf P t ≠ ∅ := fun h0 ↦ by
    rw [dom_sig_uc_eq_depOf hP ht, h0] at hi
    exact notin_empty _ hi
  have h0t : ∅ ∈ depOf P t := empty_mem_of_ordinal_of_ne_empty
    (ordinal_of_mem ordinal_omega ((otciCond_two hP).left.isTreeStructure.dep_mem_omega ht)) hdt
  refine ⟨h0t, ?_⟩
  have hw0 := (siglvl_eq_one hUt (by rw [dom_sig_uc_eq_depOf hP ht]; exact h0t)).right
  rcases isBelowFirst_of_mem hP ht hwi with h | h
  · rw [← h]
    exact hTp
  · have hlt := emb_odr hA hBX hσ hwi hw0 h
    exact ((rel_odrOne_tensorProdATwoAOne_iff_of_mem hQ hX hTp).mp hlt).left

end RtChd

section RtChdCmp

theorem empty_mem_depOf_of_not_mem_rtOf {P q : M} (hP : IsSLOT P) (hq : q ∈ ndOf P)
    (hqr : q ∉ rtOf P) : ∅ ∈ depOf P q := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hP
  have hTS := hS.isTreeStructure
  refine empty_mem_of_ordinal_of_ne_empty (ordinal_of_mem ordinal_omega (hTS.dep_mem_omega hq))
    fun h0 ↦ hqr ?_
  exact TreeStructure.mem_rt_iff.mpr ⟨hq, h0⟩

variable {P Q W : M}

/-- The level-`1` value at the first signature node of `q` of the push of `h` along `ψ`, when
`X(1)` has the single node `v` -/
theorem pushEmb_val_first {X ψ q h v : M}
    (hX : X ∈ aotci ((1 : ℕ) : M)) (hv : ∀ w ∈ ndOf (X ﹫ ((1 : ℕ) : M)), w = v)
    (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) {u : M}
    (hu : u ∈ ndOf (aoc (uc q) ﹫ ((1 : ℕ) : M))) :
    (pushEmb W (aoc (uc q)) ψ h ﹫ ((1 : ℕ) : M)) ﹫ u = (ψ ﹫ ((1 : ℕ) : M)) ﹫ v := by
  obtain ⟨q', -, -, h', hh, he⟩ := mem_tensorProdTwoAOneNds_iff'.mp hy
  rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at he
  obtain ⟨-, rfl, rfl⟩ := he
  obtain ⟨w, hw, hgw⟩ := exists_relabelOne_eq hX hh hu
  rw [pushEmb, embMk_val_one, pushOne_val_of_eq hX hh hu hw hgw, hv w hw]

/-- Two children `(V, (t, σ))` and `(V', (t', σ'))` of the root (same array and signature of length
`1`), pushed along embeddings sending the new node to `e < e'`, have images in order: compare at the
first coordinate -/
theorem bkLt_isoUp_rtChd (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {V t σ V' t' σ' ψ ψ' : M}
    (hc : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q)
    (hc' : !(V', !(t', σ')) ∈ tensorProdTwoTwoNds P Q)
    (haoc : aoc V' = aoc V) (hsig : sig V' = sig V) (hd : dom (sig V) = ((1 : ℕ) : M))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W))
    (hψ' : ψ' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W))
    (hnew : ((ψ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn V ∅)
      [odrOne (tensorProdTwoAOneTgt W ﹫ ((1 : ℕ) : M))]
      ((ψ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn V ∅)) :
    BKLt (tensorProdTwoAOneCoordOdr P (tensorProdATwoAOne Q W))
      (tensorProdTwoAOneSeq P !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ))
      (tensorProdTwoAOneSeq P !(t', tauEmb Q (aoc V') W (aoc (uc t')) ψ' σ')) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hTS := (otciCond_two hP).left.isTreeStructure
  have hTQ := (otciCond_two hQ2).left.isTreeStructure
  have hs : sig V ≠ ∅ := fun h0 ↦ by
    rw [h0, dom_empty] at hd
    have h1 : (∅ : M) ∈ ((1 : ℕ) : M) := empty_mem_natCast_one
    rw [← hd] at h1
    exact notin_empty _ h1
  have hs' : sig V' ≠ ∅ := by rw [hsig]; exact hs
  obtain ⟨h0t, hy⟩ := row_zero_isTpTwo hP hQ hc hs
  obtain ⟨h0t', hy'⟩ := row_zero_isTpTwo hP hQ hc' hs'
  rw [haoc] at hy' ⊢
  have hc1 := hc
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hc1
  obtain ⟨ht, hV, hσ, -⟩ := hc1
  have hc2 := hc'
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hc2
  obtain ⟨ht', -, hσ', -⟩ := hc2
  rw [haoc] at hσ'
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hTW := tensorProdTwoAOneTgt_mem hW
  have hv : ∀ w ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)), w = sigdcn V ∅ := fun w hw ↦ by
    rw [ndOf_aoc_val_one_eq hV, mem_iniSegNds_iff, hd] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    rw [(mem_succ_one_cases (mem_succ_of_mem hi)).resolve_right fun h1 ↦ by
      rw [h1] at hi; exact notMem_self _ hi]
  -- the first coordinates
  obtain ⟨q, hq, hqr, h, hh, hye⟩ := mem_tensorProdTwoAOneNds_iff'.mp hy
  obtain ⟨q', hq', hqr', h', hh', hye'⟩ := mem_tensorProdTwoAOneNds_iff'.mp hy'
  have hdq : ∅ ∈ depOf (Q ﹫ 2) q := empty_mem_depOf_of_not_mem_rtOf (otciCond_two hQ2).left hq hqr
  have hdq' : ∅ ∈ depOf (Q ﹫ 2) q' :=
    empty_mem_depOf_of_not_mem_rtOf (otciCond_two hQ2).left hq' hqr'
  have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
  have hUq' := uc_mem_stduoci_of_mem_otci_two hQ2 hq'
  have hu0 := (siglvl_eq_one hUq (by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hdq)).right
  have hu0' := (siglvl_eq_one hUq' (by rw [dom_sig_uc_eq_depOf hQ2 hq']; exact hdq')).right
  have hyN : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) := by rw [← hye]; exact hy
  have hyN' : !(dctUZero, !(q', h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) := by
    rw [← hye']; exact hy'
  have hg0 := pushEmb_val_first (W := W) (ψ := ψ) hX hv hyN hu0
  have hg0' := pushEmb_val_first (W := W) (ψ := ψ') hX hv hyN' hu0'
  have hz : pushNd Q (aoc V) W ψ ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) ∅) =
      !(dctUZero, !(q, pushEmb W (aoc (uc q)) ψ h)) := by
    rw [hye, pushNd_of_mem hyN]
  have hz' : pushNd Q (aoc V) W ψ' ((σ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t') ∅) =
      !(dctUZero, !(q', pushEmb W (aoc (uc q')) ψ' h')) := by
    rw [hye', pushNd_of_mem hyN']
  have hzW : !(dctUZero, !(q, pushEmb W (aoc (uc q)) ψ h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) W := by
    rw [← hz]; exact pushNd_mem_of_mem hQ hX hW hψ hy
  have hzW' : !(dctUZero, !(q', pushEmb W (aoc (uc q')) ψ' h')) ∈
      tensorProdTwoAOneNds (Q ﹫ 2) W := by
    rw [← hz']; exact pushNd_mem_of_mem hQ hX hW hψ' hy'
  have hv0 : sigdcn V ∅ ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)) :=
    (siglvl_eq_one hV (by rw [hd]; exact empty_mem_natCast_one)).right
  have hs0 : ∀ {f g : M}, IsFunction f → IsFunction g → f ↾ (∅ : M) = g ↾ ∅ := fun hf hg ↦
    hf.restrict_eq_restrict hg (fun _ h ↦ (notin_empty _ h).elim)
      (fun _ h ↦ (notin_empty _ h).elim) fun _ h ↦ (notin_empty _ h).elim
  -- the order of the pushed nodes in `(Q ⊗ W)(1)`
  have hlt : (!(dctUZero, !(q, pushEmb W (aoc (uc q)) ψ h)))
      [odrOne (tensorProdATwoAOne Q W ﹫ ((1 : ℕ) : M))]
      (!(dctUZero, !(q', pushEmb W (aoc (uc q')) ψ' h'))) := by
    rw [rel_odrOne_tensorProdATwoAOne_iff_of_mem hQ hW hzW]
    refine ⟨hzW', ?_⟩
    unfold TensorProdTwoAOneLt
    rw [lbl_orderedPair, lbl_orderedPair]
    unfold BKLt
    right
    refine ⟨∅, by rw [tensorProdTwoAOneSeq_dom]; exact hdq,
      by rw [tensorProdTwoAOneSeq_dom]; exact hdq',
      hs0 (isFunction_tensorProdTwoAOneSeq _ _) (isFunction_tensorProdTwoAOneSeq _ _), ?_⟩
    rw [tensorProdTwoAOneSeq_val hQ2 hq hdq, tensorProdTwoAOneSeq_val hQ2 hq' hdq', hg0, hg0',
      tensorProdTwoAOneCoordOdr, rel_lexProd_iff]
    exact ⟨⟨emb_val_mem hX hTW hψ hv0,
      (hTQ.anc_mem_nd hq (succ_mem_succ_of_mem (hTQ.dep_mem_omega hq) hdq)).left⟩,
      ⟨emb_val_mem hX hTW hψ' hv0,
      (hTQ.anc_mem_nd hq' (succ_mem_succ_of_mem (hTQ.dep_mem_omega hq') hdq')).left⟩, .inl hnew⟩
  have hzB := (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hW).mpr (.inr hzW)
  have hzB' := (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hW).mpr (.inr hzW')
  have hBW1 := val_mem_otci_of_mem_aotci hBW (mem_succ_self _)
  unfold BKLt
  right
  refine ⟨∅, by rw [tensorProdTwoAOneSeq_dom]; exact h0t,
      by rw [tensorProdTwoAOneSeq_dom]; exact h0t',
    hs0 (isFunction_tensorProdTwoAOneSeq _ _) (isFunction_tensorProdTwoAOneSeq _ _), ?_⟩
  rw [seq_tauEmb_val hP ht hσ h0t, seq_tauEmb_val hP ht' hσ' h0t', hz, hz',
    tensorProdTwoAOneCoordOdr, rel_lexProd_iff]
  refine ⟨⟨?_, (hTS.anc_mem_nd ht (succ_mem_succ_of_mem (hTS.dep_mem_omega ht) h0t)).left⟩,
    ⟨?_, (hTS.anc_mem_nd ht' (succ_mem_succ_of_mem (hTS.dep_mem_omega ht') h0t')).left⟩,
    .inl ((rel_tgt_relabel_iff hBW hzB hzB').mpr hlt)⟩
  · rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hBW1]
    exact ⟨_, hzB, rfl⟩
  · rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hBW1]
    exact ⟨_, hzB', rfl⟩

end RtChdCmp

section UpLemmas

variable {T Q W : M}

/-- `ψ` restricted to the node itself agrees with `ψ` -/
theorem isoUp_embRestrict_self {P : M} (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) {x ψ B : M} (hx : x ∈ tensorProdTwoTwoNds P Q)
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc x)) B) :
    isoUp Q W x (embRestrict (uc x) ψ) = isoUp Q W x ψ := by
  have hψ1 := embChg_val_one_isFunction hψ
  refine isoUp_congr hP hQ hx fun v hv ↦ ?_
  rw [embRestrict_val _ _ natCast_one_mem_two,
      val_restrict _ hψ1.left hv (by rw [hψ1.right]; exact hv)]

/-- (I1 with equality) The image of `(x, ψ)` is at most that of its ancestor at a nonzero depth -/
theorem isoUp_le_anc (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {x ψ k : M}
    (hx : x ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc x)) (tensorProdTwoAOneTgt W))
    (hk : k ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x)) (hk0 : k ≠ ∅) :
    isoUp Q W x ψ = isoUp Q W (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)
        (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)) ψ) ∨
      (isoUp Q W x ψ)
        [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
        (isoUp Q W (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)
          (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)) ψ)) := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hF := tensorProdTwoTwo_mem_otci hP hQ
  have hTS := (otciCond_two hF).left.isTreeStructure
  rw [mem_succ_iff] at hk
  rcases hk with rfl | hk
  · left
    have hxd : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) = x :=
      hTS.anc_dep hx
    rw [hxd, isoUp_embRestrict_self hP hQ (by rw [← ndOf_tensorProdTwoTwo]; exact hx) hψ]
  · right
    obtain ⟨A, U, φ, a, b, hA, hU, hφ, ha, hb, hab⟩ := ancLtAt_of_mem hT hQ hW hx hψ hk hk0
    subst hA hU hφ ha hb
    exact hab

/-- (G* with equality) An upper node with coordinates old for the ancestor `A` of `x` at a nonzero
depth that is below the image of `A` is below the image of `x` -/
theorem rel_isoUp_desc (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {x ψ k b₀ : M}
    (hx : x ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc x)) (tensorProdTwoAOneTgt W))
    (hk : k ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x)) (hk0 : k ≠ ∅)
    (hb₀ : b₀ ∈ tensorProdTwoAOneNds (T ﹫ 2) (tensorProdATwoAOne Q W))
    (hold : OldSeq (T ﹫ 2) Q (aoc (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k))) W
      (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)) ψ) (lbl b₀))
    (hlt : b₀ [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
      (isoUp Q W (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)
        (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k)) ψ))) :
    b₀ [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
      (isoUp Q W x ψ) := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hF := tensorProdTwoTwo_mem_otci hP hQ
  have hTS := (otciCond_two hF).left.isTreeStructure
  rw [mem_succ_iff] at hk
  rcases hk with rfl | hk
  · have hxd : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) = x :=
      hTS.anc_dep hx
    rw [hxd, isoUp_embRestrict_self hP hQ (by rw [← ndOf_tensorProdTwoTwo]; exact hx) hψ] at hlt
    exact hlt
  · obtain ⟨A, U, φ, hA, hU, hφ, X, a, c, hX, ha, hc, hall⟩ := descLtAt_of_mem hT hQ hW hx hψ hk hk0
    subst hA hU hφ hX ha hc
    exact hall b₀ hb₀ hold hlt

/-- Children of the same node of `P ⊗ Q` have the same array and signature -/
theorem aoc_sig_eq_of_mem_chdOf {P : M} (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) {p c c' : M} (hp : p ∈ ndOf (tensorProdTwoTwo P Q))
    (hc : c ∈ chdOf (tensorProdTwoTwo P Q) p) (hc' : c' ∈ chdOf (tensorProdTwoTwo P Q) p) :
    aoc (uc c') = aoc (uc c) ∧ sig (uc c') = sig (uc c) := by
  obtain ⟨q, hq, hqa⟩ := exists_mem_ciExt_of_mem_chdOf_tensorProdTwoTwo hP hQ hp hc
  obtain ⟨q', hq', hqa'⟩ := exists_mem_ciExt_of_mem_chdOf_tensorProdTwoTwo hP hQ hp hc'
  rw [eq_of_mem_ciExt_one hq' hq] at hqa'
  have hs := sig_uc_eq_of_mem_losSet_chdlosOf_tensorProdTwoTwo hP hQ hp hq
    ((mem_losSet_chdlosOf_tensorProdTwoTwo_iff hP hQ hp _).mpr ⟨hc, hqa.symm⟩)
  have hs' := sig_uc_eq_of_mem_losSet_chdlosOf_tensorProdTwoTwo hP hQ hp hq
    ((mem_losSet_chdlosOf_tensorProdTwoTwo_iff hP hQ hp _).mpr ⟨hc', hqa'.symm⟩)
  exact ⟨hqa'.symm.trans hqa, hs'.trans hs.symm⟩

/-- The sibling order of `P ⊗ Q` is its order -/
theorem rel_tensorProdTwoTwoOdr_of_sblOdrOf {P : M} (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) {p c c' : M} (hp : p ∈ ndOf (tensorProdTwoTwo P Q))
    (hc : c ∈ chdOf (tensorProdTwoTwo P Q) p)
    (h : c [sblOdrOf (tensorProdTwoTwo P Q)] c') : c [tensorProdTwoTwoOdr P Q] c' := by
  have hT := isSLOT_tensorProdTwoTwo hP hQ
  obtain ⟨-, -, -, hlt⟩ := (rel_sblOdrOf_iff hT).mp h
  rw [ndlosOf_eq_chdlosOf hT hp hc] at hlt
  change c [losOdr (chdlosOf (tensorProdTwoTwo P Q) p ﹫ aoc (uc c))] c' at hlt
  rw [chdlosOf_tensorProdTwoTwo_val hP hQ hp hc, keyLos, losOdr_orderedPair, mem_inter_iff] at hlt
  exact hlt.left

end UpLemmas

section UpCases

variable {T Q W : M}

/-- The image of an upper node has old coordinates for `(X, ψ')` if `ψ'` agrees with its
embedding `ψ` on `X(1)` -/
theorem oldSeq_isoUpOf {P : M} (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {V t σ ψ ψ' : M} (hc : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q)
    (hagr : ∀ v ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)),
      (ψ ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ' ﹫ ((1 : ℕ) : M)) ﹫ v) :
    OldSeq P Q (aoc V) W ψ' (lbl (isoUpOf Q W V t σ ψ)) := by
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hc
  obtain ⟨ht, hV, hσ, -⟩ := hc
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  intro i hi
  simp only [isoUpOf, lbl_orderedPair, left_orderedPair, right_orderedPair] at hi ⊢
  have hw := (siglvl_eq_one hUt (by rw [dom_sig_uc_eq_depOf hP ht]; exact hi)).right
  have hz := emb_val_mem (aoc_mem_aotci_of_mem_stduoci_one hUt) (tensorProdATwoAOne_mem_aotci hQ hX)
    hσ hw
  refine ⟨_, hz, ?_⟩
  rw [tauEmb_val_one hσ hw, pushNd_old hQ hX hX rfl (isSubOne_refl _) (fun v hv ↦ (hagr v hv)) hz]

/-- (B1) If `c < c'` are siblings and `ψ` and `ψ'` agree on `c_uc`, the image of `(c, ψ)` is below
those of the descendants `(x', ψ')` of `c'` -/
theorem rel_isoUp_of_sbl (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {C c c' x' ψc ψ' : M}
    (hC : C ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q))
    (hc : c ∈ chdOf (tensorProdTwoTwo (T ﹫ 2) Q) C)
    (hc' : c' ∈ chdOf (tensorProdTwoTwo (T ﹫ 2) Q) C)
    (hx' : x' ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q))
    (hk' : depOf (tensorProdTwoTwo (T ﹫ 2) Q) c' ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x'))
    (hcx' : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x' (depOf (tensorProdTwoTwo (T ﹫ 2) Q) c') = c')
    (hψc : ψc ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc c)) (tensorProdTwoAOneTgt W))
    (hψ' : ψ' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc x')) (tensorProdTwoAOneTgt W))
    (hagr : ∀ v ∈ ndOf (aoc (uc c) ﹫ ((1 : ℕ) : M)),
      (ψc ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ' ﹫ ((1 : ℕ) : M)) ﹫ v)
    (hsbl : c [sblOdrOf (tensorProdTwoTwo (T ﹫ 2) Q)] c') :
    (isoUp Q W c ψc) [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
      (isoUp Q W x' ψ') := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hF := tensorProdTwoTwo_mem_otci hP hQ
  have hTS := (otciCond_two hF).left.isTreeStructure
  have hTW := tensorProdTwoAOneTgt_mem hW
  have hCN := hC
  rw [ndOf_tensorProdTwoTwo] at hCN
  obtain ⟨haoc, hsig⟩ := aoc_sig_eq_of_mem_chdOf hP hQ hC hc hc'
  have hodr := rel_tensorProdTwoTwoOdr_of_sblOdrOf hP hQ hC hc hsbl
  obtain ⟨⟨hcN, hc'N⟩, -, hbk⟩ := rel_tensorProdTwoTwoOdr_iff.mp hodr
  have hψ'c := embRestrict_mem_aotciEmbSet hF hx' hk' hTW hψ'
  rw [hcx'] at hψ'c
  have hFs := (otciCond_two hF).left
  have hk0 : depOf (tensorProdTwoTwo (T ﹫ 2) Q) c' ≠ ∅ := by
    obtain ⟨-, hd, -⟩ := (mem_chdOf_tensorProdTwoTwo_iff hCN).mp hc'
    rwa [dom_sig_uc_eq_depOf hF (mem_ndOf_of_mem_chdOf hFs hc')] at hd
  have hsd : dom (sig (uc c)) ≠ ∅ := ((mem_chdOf_tensorProdTwoTwo_iff hCN).mp hc).right.left
  have hsub' := (uc_ancOf_rel hF hx' hk').right
  rw [hcx'] at hsub'
  have hψ'1 := embChg_val_one_isFunction hψ'
  obtain ⟨t, ht, V, hV, σ, hσ, -, rfl⟩ := mem_tensorProdTwoTwoNds_iff.mp hcN
  obtain ⟨t', ht', V', hV', σ', hσ', -, rfl⟩ := mem_tensorProdTwoTwoNds_iff.mp hc'N
  simp only [uc_orderedPair, lbl_orderedPair] at haoc hsig hψc hψ'c hagr hbk hsd hsub' ⊢
  rw [isoUp_orderedPair]
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  rw [haoc] at hσ' hψ'c hsub'
  have hs : sig V ≠ ∅ := fun h0 ↦ hsd (by rw [h0, dom_empty])
  have hs' : sig V' ≠ ∅ := by rw [hsig]; exact hs
  have hagr' : ∀ v ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M)),
      (ψc ﹫ ((1 : ℕ) : M)) ﹫ v = (embRestrict V' ψ' ﹫ ((1 : ℕ) : M)) ﹫ v := fun v hv ↦ by
    rw [hagr v hv, embRestrict_val _ _ natCast_one_mem_two, val_restrict _ hψ'1.left
      (by rw [haoc]; exact hv) (by rw [hψ'1.right]; exact hsub'.left hv)]
  have h1 := rel_isoUpOf_of_bkLt hT hQ hW hcN hs hψc hc'N hs' (by rw [haoc]; exact hψc)
    (by rw [haoc]; exact (bkLt_iff_isoUpOf hP hQ hX hW hψc ht ht' hσ hσ').mp hbk)
  have h2 : isoUpOf Q W V' t' σ' ψc = isoUpOf Q W V' t' σ' (embRestrict V' ψ') := by
    rw [← isoUp_orderedPair, ← isoUp_orderedPair]
    refine isoUp_congr hP hQ hc'N fun v hv ↦ ?_
    rw [uc_orderedPair, haoc] at hv
    exact hagr' v hv
  rw [h2] at h1
  refine rel_isoUp_desc hT hQ hW hx' hψ' hk' hk0 (isoUpOf_mem hP hQ hW hcN hs hψc) ?_ ?_
  · rw [hcx', uc_orderedPair, haoc]
    exact oldSeq_isoUpOf hP hQ hcN hagr'
  · rw [hcx', isoUp_orderedPair, uc_orderedPair]
    exact h1

end UpCases

section UpCases2

variable {T Q W : M}

/-- (B2) If `c` and `c'` are children of `C`, `ψ` and `ψ'` agree on `C_uc` and send the new node
of `c` to `e < e'`, the image of `(c, ψ)` is below those of the descendants `(x', ψ')` of `c'`:
compare with the least child `x*` of `C` along `ψ'` -/
theorem rel_isoUp_of_lt_new (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {C c c' x' ψc ψ' : M}
    (hC : C ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q))
    (hc : c ∈ chdOf (tensorProdTwoTwo (T ﹫ 2) Q) C)
    (hc' : c' ∈ chdOf (tensorProdTwoTwo (T ﹫ 2) Q) C)
    (hx' : x' ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q))
    (hk' : depOf (tensorProdTwoTwo (T ﹫ 2) Q) c' ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x'))
    (hcx' : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x' (depOf (tensorProdTwoTwo (T ﹫ 2) Q) c') = c')
    (hψc : ψc ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc c)) (tensorProdTwoAOneTgt W))
    (hψ' : ψ' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc x')) (tensorProdTwoAOneTgt W))
    (hagr : ∀ v ∈ ndOf (aoc (uc C) ﹫ ((1 : ℕ) : M)),
      (ψc ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ' ﹫ ((1 : ℕ) : M)) ﹫ v)
    (hnew : ((ψc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) (depOf (tensorProdTwoTwo (T ﹫ 2) Q) C))
      [odrOne (tensorProdTwoAOneTgt W ﹫ ((1 : ℕ) : M))]
      ((ψ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) (depOf (tensorProdTwoTwo (T ﹫ 2) Q) C))) :
    (isoUp Q W c ψc) [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
      (isoUp Q W x' ψ') := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hF := tensorProdTwoTwo_mem_otci hP hQ
  have hFs := (otciCond_two hF).left
  have hS : (SLOTreeStructure.ofM (tensorProdTwoTwo (T ﹫ 2) Q)).IsSLOTreeStructure := hFs
  have hTS := hS.isTreeStructure
  have hTW := tensorProdTwoAOneTgt_mem hW
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hR := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci
    (tensorProdATwoAOne_mem_aotci hT hBW) (mem_succ_self _))).left
  change IsStrictLinearOrder (odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫
    ((1 : ℕ) : M))) _ at hR
  have hCN := hC
  rw [ndOf_tensorProdTwoTwo] at hCN
  set k := depOf (tensorProdTwoTwo (T ﹫ 2) Q) C with hkdef
  -- the least child
  obtain ⟨q, hq, hqa⟩ := exists_mem_ciExt_of_mem_chdOf_tensorProdTwoTwo hP hQ hC hc
  obtain ⟨xs, hxs, hxsq, hmin, -⟩ := exists_least_chd_tensorProdTwoTwo hP hQ hC hq
  have hqct := (mem_ciExt_props hq).right.right.right
  have hxsn := mem_ndOf_of_mem_chdOf hFs hxs
  have hxs0 : chdOf (tensorProdTwoTwo (T ﹫ 2) Q) xs = ∅ :=
    chdOf_eq_empty_of_ctp_eq_ct (natCast_mem_omega 2) hF hxsn (by rw [hxsq]; exact hqct)
  obtain ⟨haoc', hsig'⟩ := aoc_sig_eq_of_mem_chdOf hP hQ hC hc hc'
  obtain ⟨haocs, hsigs⟩ := aoc_sig_eq_of_mem_chdOf hP hQ hC hc hxs
  have hψ'c := embRestrict_mem_aotciEmbSet hF hx' hk' hTW hψ'
  rw [hcx'] at hψ'c
  have hψ'1 := embChg_val_one_isFunction hψ'
  have hsub' := (uc_ancOf_rel hF hx' hk').right
  rw [hcx'] at hsub'
  have hcn := mem_ndOf_of_mem_chdOf hFs hc
  have hc'n := mem_ndOf_of_mem_chdOf hFs hc'
  have hdc : depOf (tensorProdTwoTwo (T ﹫ 2) Q) c = succ k := hTS.dep_of_mem_chd _ hC _ hc
  have hdc' : depOf (tensorProdTwoTwo (T ﹫ 2) Q) c' = succ k := hTS.dep_of_mem_chd _ hC _ hc'
  have hsubC' := (uc_rel_of_mem_chdOf hF hC hc').right.right.left
  -- `ψ` and `ψ'` restricted
  have hval' (v : M) (hv : v ∈ ndOf (aoc (uc c') ﹫ ((1 : ℕ) : M))) :
      (embRestrict (uc c') ψ' ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ' ﹫ ((1 : ℕ) : M)) ﹫ v := by
    rw [embRestrict_val _ _ natCast_one_mem_two, val_restrict _ hψ'1.left hv
      (by rw [hψ'1.right]; exact hsub'.left hv)]
  have hagrC : ∀ v ∈ ndOf (aoc (uc C) ﹫ ((1 : ℕ) : M)),
      (ψc ﹫ ((1 : ℕ) : M)) ﹫ v = (embRestrict (uc c') ψ' ﹫ ((1 : ℕ) : M)) ﹫ v := fun v hv ↦ by
    rw [hagr v hv, hval' v (hsubC'.left hv)]
  have hkc' : sigdcn (uc c) k ∈ ndOf (aoc (uc c') ﹫ ((1 : ℕ) : M)) := by
    have hUc' := uc_mem_stduoci_of_mem_otci_two hF hc'n
    have hkd : k ∈ dom (sig (uc c')) := by
      rw [dom_sig_uc_eq_depOf hF hc'n, hdc']; exact mem_succ_self k
    have h' := (siglvl_eq_one hUc' hkd).right
    rwa [sigdcn, hsig'] at h'
  have hnew' : ((ψc ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) k)
      [odrOne (tensorProdTwoAOneTgt W ﹫ ((1 : ℕ) : M))]
      ((embRestrict (uc c') ψ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc c) k) := by
    rw [hval' _ hkc']; exact hnew
  have hko : Ordinal k := ordinal_of_mem ordinal_omega (hTS.dep_mem_omega hC)
  have hcN : c ∈ tensorProdTwoTwoNds (T ﹫ 2) Q := by rw [← ndOf_tensorProdTwoTwo]; exact hcn
  have hxsN : xs ∈ tensorProdTwoTwoNds (T ﹫ 2) Q := by rw [← ndOf_tensorProdTwoTwo]; exact hxsn
  have hc'N : c' ∈ tensorProdTwoTwoNds (T ﹫ 2) Q := by rw [← ndOf_tensorProdTwoTwo]; exact hc'n
  -- `(c, ψ)` is below `(x*, ψ')`
  have hstep1 : (isoUp Q W c ψc)
      [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
      (isoUp Q W xs (embRestrict (uc c') ψ')) := by
    obtain ⟨-, -, hprtc⟩ := (mem_chdOf_tensorProdTwoTwo_iff hCN).mp hc
    obtain ⟨-, -, hprts⟩ := (mem_chdOf_tensorProdTwoTwo_iff hCN).mp hxs
    have hdsc : dom (sig (uc c)) = succ k := by rw [dom_sig_uc_eq_depOf hF hcn, hdc]
    have hψ'cV : embRestrict (uc c') ψ' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc c))
        (tensorProdTwoAOneTgt W) := by rw [← haoc']; exact hψ'c
    obtain ⟨tC, -, VC, -, σC, -, -, hCe⟩ := mem_tensorProdTwoTwoNds_iff.mp hCN
    obtain ⟨t, -, V, -, σ, -, -, hce⟩ := mem_tensorProdTwoTwoNds_iff.mp hcN
    obtain ⟨ts, -, Vs, -, σs, -, -, hxse⟩ := mem_tensorProdTwoTwoNds_iff.mp hxsN
    rw [hce, uc_orderedPair] at hψc hnew' hdsc hψ'cV
    rw [hce, hxse, uc_orderedPair, uc_orderedPair] at haocs hsigs
    rw [hce] at hprtc hcN
    rw [hxse] at hprts hxsN
    rw [hCe] at hprtc hprts
    rw [hxse, isoUp_orderedPair, hce, isoUp_orderedPair]
    have hs : sig V ≠ ∅ := fun h0 ↦ by
      rw [h0, dom_empty] at hdsc
      exact notin_empty k (by rw [hdsc]; exact mem_succ_self k)
    have hss : sig Vs ≠ ∅ := by rw [hsigs]; exact hs
    have hbk : BKLt (tensorProdTwoAOneCoordOdr (T ﹫ 2) (tensorProdATwoAOne Q W))
        (tensorProdTwoAOneSeq (T ﹫ 2) !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψc σ))
        (tensorProdTwoAOneSeq (T ﹫ 2) !(ts, tauEmb Q (aoc Vs) W (aoc (uc ts))
          (embRestrict (uc c') ψ') σs)) := by
      by_cases hk0 : k = ∅
      · have hd : dom (sig V) = ((1 : ℕ) : M) := by
          rw [hdsc, hk0, natCast_succ, natCast_zero]
        rw [hk0] at hnew'
        exact bkLt_isoUp_rtChd hP hQ hW hcN hxsN haocs hsigs hd hψc hψ'cV hnew'
      · have hm : ⋃₀ dom (sig V) = k := by rw [hdsc, sUnion_succ hko.transitive]
        have hm0 : ⋃₀ dom (sig V) ≠ ∅ := by rw [hm]; exact hk0
        have hVC := (chd_rows (W := W) (ψ := ψc) (ψC := ψc) hP hQ hcN hm0 hprtc
          fun _ _ ↦ rfl).left
        refine bkLt_isoUp_sbl hP hQ hW hcN hxsN haocs hsigs hm0 hprtc hprts hψc hψ'cV
          (fun v hv ↦ ?_) (by rw [hm]; exact hnew')
        have hv' : v ∈ ndOf (aoc (uc C) ﹫ ((1 : ℕ) : M)) := by
          rw [hCe, uc_orderedPair, hVC, aoc_iniSeg]; exact hv
        exact hagrC v hv'
    exact rel_isoUpOf_of_bkLt hT hQ hW hcN hs hψc hxsN hss (by rw [haocs]; exact hψ'cV) hbk
  -- `(x*, ψ')` is at most `(x', ψ')`
  have hk0' : depOf (tensorProdTwoTwo (T ﹫ 2) Q) c' ≠ ∅ := by
    rw [hdc']; exact succ_ne_empty k
  have hstep2 : isoUp Q W xs (embRestrict (uc c') ψ') = isoUp Q W x' ψ' ∨
      (isoUp Q W xs (embRestrict (uc c') ψ'))
        [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
        (isoUp Q W x' ψ') := by
    rcases hmin c' hc' (by rw [haoc', haocs]) with hce' | hlt
    · left
      have hx'c : x' = c' := by
        rw [mem_succ_iff] at hk'
        rcases hk' with hk' | hk'
        · rw [← hcx', hk']; exact (hTS.anc_dep hx').symm
        · exfalso
          have h' : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x' (succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q)
              c'))
              ∈ chdOf (tensorProdTwoTwo (T ﹫ 2) Q)
                (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x' (depOf (tensorProdTwoTwo (T ﹫ 2) Q) c')) :=
            hTS.anc_succ_mem_chd hx' hk'
          rw [hcx', hce', hxs0] at h'
          exact notin_empty _ h'
      rw [hx'c] at hψ' ⊢
      rw [← hce', isoUp_embRestrict_self hP hQ hc'N hψ']
    · right
      obtain ⟨-, -, hbk⟩ := rel_tensorProdTwoTwoOdr_iff.mp hlt
      obtain ⟨ts, hts, Vs, hVs, σs, hσs, -, hxse⟩ := mem_tensorProdTwoTwoNds_iff.mp hxsN
      obtain ⟨t', ht', V', hV', σ', hσ', -, hc'e⟩ := mem_tensorProdTwoTwoNds_iff.mp hc'N
      have hψ'cs : embRestrict (uc c') ψ' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc xs))
          (tensorProdTwoAOneTgt W) := by rw [haocs, ← haoc']; exact hψ'c
      have hsxs : sig (uc xs) ≠ ∅ := fun h0 ↦
        ((mem_chdOf_tensorProdTwoTwo_iff hCN).mp hxs).right.left (by rw [h0, dom_empty])
      have hsc' : sig (uc c') ≠ ∅ := fun h0 ↦
        ((mem_chdOf_tensorProdTwoTwo_iff hCN).mp hc').right.left (by rw [h0, dom_empty])
      have haoc's : aoc (uc c') = aoc (uc xs) := by rw [haoc', haocs]
      have hold := oldSeq_isoUpOf (P := T ﹫ 2) (W := W) (ψ' := embRestrict (uc c') ψ') hP hQ
        (by rw [← hxse]; exact hxsN) (fun _ _ ↦ rfl) (t := ts) (σ := σs)
      rw [hxse, hc'e] at hbk
      rw [hxse] at hψ'cs hsxs hxsN haoc's
      rw [hc'e] at hsc' hc'N haoc's
      simp only [uc_orderedPair, lbl_orderedPair] at hbk hψ'cs hsxs hsc' haoc's
      rw [haoc's] at hσ'
      have hXs := aoc_mem_aotci_of_mem_stduoci_one hVs
      have hψ'cs' : embRestrict (uc c') ψ' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V')
          (tensorProdTwoAOneTgt W) := by rw [haoc's]; exact hψ'cs
      have h1 := rel_isoUpOf_of_bkLt (ψ := embRestrict (uc c') ψ') (ψ' := embRestrict (uc c') ψ')
        hT hQ hW hxsN hsxs hψ'cs hc'N hsc' hψ'cs'
        (by rw [haoc's]; exact (bkLt_iff_isoUpOf hP hQ hXs hW hψ'cs hts ht' hσs hσ').mp hbk)
      rw [hxse, isoUp_orderedPair]
      refine rel_isoUp_desc hT hQ hW hx' hψ' hk' hk0' (isoUpOf_mem hP hQ hW hxsN hsxs hψ'cs) ?_ ?_
      · rw [hcx', hc'e, uc_orderedPair, haoc's]
        rw [hc'e, uc_orderedPair] at hold
        exact hold
      · rw [hcx', hc'e, isoUp_orderedPair, uc_orderedPair]
        rw [hc'e, uc_orderedPair] at h1
        exact h1
  rcases hstep2 with h2 | h2
  · rw [← h2]; exact hstep1
  · exact hR.right.right.left.trans (hR.mem_left hstep1) (hR.mem_right hstep1) (hR.mem_right h2)
      hstep1 h2

end UpCases2

section UpMain

variable {T Q W : M}

/-- The coordinates of the sequence of `(x, ψ)` give `ψ` on the signature nodes of the ancestor
of `x` at depth `k`, which are those of `x` -/
theorem ancOf_eq_and_val_of_restrict_eq (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) :
    M))
    {x ψ x' ψ' k : M} (hx : x ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q))
    (hx' : x' ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q))
    (hk : k ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x))
    (hk' : k ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x'))
    (hres : tensorProdTwoAOneSeq (tensorProdTwoTwo (T ﹫ 2) Q) !(x, ψ) ↾ k =
      tensorProdTwoAOneSeq (tensorProdTwoTwo (T ﹫ 2) Q) !(x', ψ') ↾ k) :
    ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x' k = ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k ∧
      ∀ i ∈ k, sigdcn (uc x') i = sigdcn (uc x) i ∧
        (ψ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc x) i = (ψ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc x) i := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hF := tensorProdTwoTwo_mem_otci hP hQ
  have hFs := (otciCond_two hF).left
  have hS : (SLOTreeStructure.ofM (tensorProdTwoTwo (T ﹫ 2) Q)).IsSLOTreeStructure := hFs
  have hTS := hS.isTreeStructure
  have hdo := ordinal_of_mem ordinal_omega (hTS.dep_mem_omega hx)
  have hdo' := ordinal_of_mem ordinal_omega (hTS.dep_mem_omega hx')
  have hsub (i : M) (hi : i ∈ k) : i ∈ depOf (tensorProdTwoTwo (T ﹫ 2) Q) x := by
    rw [mem_succ_iff] at hk
    rcases hk with rfl | hk
    · exact hi
    · exact hdo.transitive _ hk hi
  have hsub' (i : M) (hi : i ∈ k) : i ∈ depOf (tensorProdTwoTwo (T ﹫ 2) Q) x' := by
    rw [mem_succ_iff] at hk'
    rcases hk' with rfl | hk'
    · exact hi
    · exact hdo'.transitive _ hk' hi
  have hval (i : M) (hi : i ∈ k) :
      !((ψ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc x) i, ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ i)) =
        !((ψ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc x') i,
          ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x' (succ i)) := by
    rw [← tensorProdTwoAOneSeq_val hF hx (hsub i hi),
        ← tensorProdTwoAOneSeq_val hF hx' (hsub' i hi)]
    exact val_eq_of_restrict_eq (isFunction_tensorProdTwoAOneSeq _ _)
      (isFunction_tensorProdTwoAOneSeq _ _) hres hi
      (by rw [tensorProdTwoAOneSeq_dom]; exact hsub i hi)
      (by rw [tensorProdTwoAOneSeq_dom]; exact hsub' i hi)
  have hko : Ordinal k := ordinal_of_mem (ordinal_succ hdo) hk
  have hanc : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x' k = ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k := by
    rcases mem_omega_cases (ordinal_omega.transitive _ (succ_mem_omega (hTS.dep_mem_omega hx)) hk)
      with rfl | ⟨j, -, rfl⟩
    · -- both are the root
      obtain ⟨r, hr, -⟩ := rtOf_tensorProdTwoTwo hP hQ
      have hroot {y : M} (hy : y ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q)) :
          ancOf (tensorProdTwoTwo (T ﹫ 2) Q) y ∅ = r := by
        have h0 : (∅ : M) ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) y) := by
          by_cases h : depOf (tensorProdTwoTwo (T ﹫ 2) Q) y = ∅
          · rw [h]; exact mem_succ_self _
          · exact mem_succ_of_mem (empty_mem_of_ordinal_of_ne_empty
              (ordinal_of_mem ordinal_omega (hTS.dep_mem_omega hy)) h)
        obtain ⟨hyn, hyd⟩ := hTS.anc_mem_nd hy h0
        have hrt : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) y ∅ ∈ rtOf (tensorProdTwoTwo (T ﹫ 2) Q) :=
          TreeStructure.mem_rt_iff.mpr ⟨hyn, hyd⟩
        rw [hr, mem_singleton_iff] at hrt
        exact hrt
      rw [hroot hx, hroot hx']
    · have h' := hval j (mem_succ_self j)
      rw [orderedPair_eq_orderedPair_iff] at h'
      exact h'.right.symm
  refine ⟨hanc, fun i hi ↦ ?_⟩
  have hsd : sigdcn (uc x') i = sigdcn (uc x) i := by
    rw [← sigdcn_anc hF hx' hk' hi, hanc, sigdcn_anc hF hx hk hi]
  refine ⟨hsd, ?_⟩
  have h' := hval i hi
  rw [orderedPair_eq_orderedPair_iff, hsd] at h'
  exact h'.left.symm

/-- The values of `embRestrict` on the nodes of an ancestor -/
theorem embRestrict_anc_val {P x ψ k v B : M} (hP : P ∈ otci ((2 : ℕ) : M)) (hx : x ∈ ndOf P)
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc x)) B) (hk : k ∈ succ (depOf P x))
    (hv : v ∈ ndOf (aoc (uc (ancOf P x k)) ﹫ ((1 : ℕ) : M))) :
    (embRestrict (uc (ancOf P x k)) ψ ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ ﹫ ((1 : ℕ) : M)) ﹫ v := by
  have hψ1 := embChg_val_one_isFunction hψ
  have hsub := (uc_ancOf_rel hP hx hk).right
  rw [embRestrict_val _ _ natCast_one_mem_two, val_restrict _ hψ1.left hv
    (by rw [hψ1.right]; exact hsub.left hv)]

/-- (Upper part) The map preserves the Brouwer–Kleene order of the upper nodes -/
theorem rel_isoUp_of_bkLt (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {x ψ x' ψ' : M}
    (hx : x ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc x)) (tensorProdTwoAOneTgt W))
    (hx' : x' ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q))
    (hx'r : x' ∉ rtOf (tensorProdTwoTwo (T ﹫ 2) Q))
    (hψ' : ψ' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc x')) (tensorProdTwoAOneTgt W))
    (h : BKLt (tensorProdTwoAOneCoordOdr (tensorProdTwoTwo (T ﹫ 2) Q) W)
      (tensorProdTwoAOneSeq (tensorProdTwoTwo (T ﹫ 2) Q) !(x, ψ))
      (tensorProdTwoAOneSeq (tensorProdTwoTwo (T ﹫ 2) Q) !(x', ψ'))) :
    (isoUp Q W x ψ) [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
      (isoUp Q W x' ψ') := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hF := tensorProdTwoTwo_mem_otci hP hQ
  have hFs := (otciCond_two hF).left
  have hS : (SLOTreeStructure.ofM (tensorProdTwoTwo (T ﹫ 2) Q)).IsSLOTreeStructure := hFs
  have hTS := hS.isTreeStructure
  have hTW := tensorProdTwoAOneTgt_mem hW
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hR := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci
    (tensorProdATwoAOne_mem_aotci hT hBW) (mem_succ_self _))).left
  change IsStrictLinearOrder (odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫
    ((1 : ℕ) : M))) _ at hR
  have hdo := ordinal_of_mem ordinal_omega (hTS.dep_mem_omega hx)
  have hdo' := ordinal_of_mem ordinal_omega (hTS.dep_mem_omega hx')
  have hsf := isFunction_tensorProdTwoAOneSeq (tensorProdTwoTwo (T ﹫ 2) Q) !(x, ψ)
  have hsf' := isFunction_tensorProdTwoAOneSeq (tensorProdTwoTwo (T ﹫ 2) Q) !(x', ψ')
  have hψ1 := embChg_val_one_isFunction hψ
  have hψ'1 := embChg_val_one_isFunction hψ'
  have hUx' := uc_mem_stduoci_of_mem_otci_two hF hx'
  unfold BKLt at h
  rcases h with ⟨hts, hne⟩ | ⟨k, hks, hks', hres, hrel⟩
  · -- `x'` is a proper ancestor of `x` and `ψ'` is `ψ` restricted
    have hdd := dom_mono hts
    rw [tensorProdTwoAOneSeq_dom, tensorProdTwoAOneSeq_dom] at hdd
    have hdne : depOf (tensorProdTwoTwo (T ﹫ 2) Q) x' ≠ depOf (tensorProdTwoTwo (T ﹫ 2) Q) x := by
      intro hde
      refine hne (eq_of_subset_of_subset hts (subset_of_val_eq hsf hsf' ?_ fun i hi ↦ ?_))
      · rw [tensorProdTwoAOneSeq_dom, tensorProdTwoAOneSeq_dom, hde]; exact fun _ h ↦ h
      · exact val_eq_of_subset hsf hsf' hts (by
          rw [tensorProdTwoAOneSeq_dom, hde]; rwa [tensorProdTwoAOneSeq_dom] at hi)
    have hdin := mem_of_subset_of_ne_ordinal hdo' hdo hdd hdne
    have hk : depOf (tensorProdTwoTwo (T ﹫ 2) Q) x' ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) :=
      mem_succ_of_mem hdin
    have hk' : depOf (tensorProdTwoTwo (T ﹫ 2) Q) x' ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x')
        :=
      mem_succ_self _
    have hres : tensorProdTwoAOneSeq (tensorProdTwoTwo (T ﹫ 2) Q) !(x, ψ) ↾
        depOf (tensorProdTwoTwo (T ﹫ 2) Q) x' =
        tensorProdTwoAOneSeq (tensorProdTwoTwo (T ﹫ 2) Q) !(x', ψ') ↾
          depOf (tensorProdTwoTwo (T ﹫ 2) Q) x' := by
      exact restrict_eq_of_subset hsf hsf' hts (k := depOf (tensorProdTwoTwo (T ﹫ 2) Q) x')
        (by rw [tensorProdTwoAOneSeq_dom]; exact fun _ h ↦ h)
    obtain ⟨hanc, hvals⟩ := ancOf_eq_and_val_of_restrict_eq hT hQ hx hx' hk hk' hres
    have hxa : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x' (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x') = x' :=
      hTS.anc_dep hx'
    rw [hxa] at hanc
    have h0 : depOf (tensorProdTwoTwo (T ﹫ 2) Q) x' ≠ ∅ := fun h0 ↦ by
      have := empty_mem_depOf_of_not_mem_rtOf hFs hx' hx'r
      rw [h0] at this
      exact notin_empty _ this
    obtain ⟨A, U, φ, a, b, hA, hU, hφ, ha, hb, hab⟩ := ancLtAt_of_mem hT hQ hW hx hψ hdin h0
    change ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x') = A at hA
    rw [← hanc] at hA
    subst hA hU hφ ha hb
    rw [isoUp_congr (x := x') (ψ' := embRestrict (uc x') ψ) (ψ := ψ') hP hQ
      (by rw [← ndOf_tensorProdTwoTwo]; exact hx') fun v hv ↦ ?_] at hab
    · exact hab
    · have hv' := hv
      rw [ndOf_aoc_val_one_eq hUx', mem_iniSegNds_iff, dom_sig_uc_eq_depOf hF hx'] at hv'
      obtain ⟨i, hi, rfl⟩ := hv'
      rw [embRestrict_val _ _ natCast_one_mem_two, val_restrict _ hψ1.left hv
        (by
          have hs1 := (uc_ancOf_rel hF hx hk).right.left
          rw [← hanc] at hs1
          rw [hψ1.right]; exact hs1 hv),
        (hvals i hi).left, (hvals i hi).right]
  · -- the first difference is at row `k`, below the common ancestor `C` at depth `k`
    rw [tensorProdTwoAOneSeq_dom] at hks hks'
    have hk := mem_succ_of_mem hks
    have hk' := mem_succ_of_mem hks'
    obtain ⟨hanc, hvals⟩ := ancOf_eq_and_val_of_restrict_eq hT hQ hx hx' hk hk' hres
    obtain ⟨hC, hdC⟩ := hTS.anc_mem_nd hx hk
    change ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q) at hC
    change depOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k) = k at hdC
    have hk1 : succ k ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x) := succ_mem_succ_of_mem
        (hTS.dep_mem_omega hx) hks
    have hk1' : succ k ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x') :=
      succ_mem_succ_of_mem (hTS.dep_mem_omega hx') hks'
    obtain ⟨hcn, hdc⟩ := hTS.anc_mem_nd hx hk1
    change ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ k) ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q) at hcn
    change depOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ k)) =
        succ k at hdc
    have hc : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ k) ∈
        chdOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k) :=
      hTS.anc_succ_mem_chd hx hks
    have hc' : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x' (succ k) ∈
        chdOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x k) := by
      rw [← hanc]; exact hTS.anc_succ_mem_chd hx' hks'
    obtain ⟨-, hdc'⟩ := hTS.anc_mem_nd hx' hk1'
    change depOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x' (succ k)) =
      succ k at hdc'
    have hψc := embRestrict_mem_aotciEmbSet hF hx hk1 hTW hψ
    have hle := isoUp_le_anc hT hQ hW hx hψ hk1 (succ_ne_empty k)
    rw [tensorProdTwoAOneSeq_val hF hx hks, tensorProdTwoAOneSeq_val hF hx' hks',
      tensorProdTwoAOneCoordOdr, rel_lexProd_iff] at hrel
    obtain ⟨-, -, hrel⟩ := hrel
    obtain ⟨-, hsig'⟩ := aoc_sig_eq_of_mem_chdOf hP hQ hC hc hc'
    have hsdc := sigdcn_anc hF hx hk1 (mem_succ_self k)
    have hsdc' := sigdcn_anc hF hx' hk1' (mem_succ_self k)
    have hsdk : sigdcn (uc x') k = sigdcn (uc x) k := by
      rw [← hsdc, ← hsdc', sigdcn, sigdcn, hsig']
    have hUc := uc_mem_stduoci_of_mem_otci_two hF hcn
    have hdcs : dom (sig (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ k)))) = succ k := by
      rw [dom_sig_uc_eq_depOf hF hcn, hdc]
    -- `ψ` restricted to `c` agrees with `ψ'` on the signature nodes of `c` before `k`
    have hagrc (i : M) (hi : i ∈ k) :
        (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ k))) ψ ﹫ ((1 : ℕ) : M)) ﹫
          sigdcn (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ k))) i =
        (ψ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ k))) i := by
      have hin := (siglvl_eq_one hUc (by rw [hdcs]; exact mem_succ_of_mem hi)).right
      rw [embRestrict_anc_val hF hx hψ hk1 hin, sigdcn_anc hF hx hk1 (mem_succ_of_mem hi),
        (hvals i hi).right]
    have hnode (v : M) (hv : v ∈ ndOf (aoc (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ k))) ﹫
        ((1 : ℕ) : M))) : ∃ i ∈ succ k,
        sigdcn (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ k))) i = v := by
      rw [ndOf_aoc_val_one_eq hUc, mem_iniSegNds_iff, hdcs] at hv
      exact hv
    have hkin := (siglvl_eq_one hUc (by rw [hdcs]; exact mem_succ_self k)).right
    have hcx' : ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x'
        (depOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x' (succ k))) =
        ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x' (succ k) := by rw [hdc']
    have hk1'' : depOf (tensorProdTwoTwo (T ﹫ 2) Q) (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x' (succ k))
        ∈ succ (depOf (tensorProdTwoTwo (T ﹫ 2) Q) x') := by rw [hdc']; exact hk1'
    have h2 : (isoUp Q W (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ k))
        (embRestrict (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ k))) ψ))
        [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
        (isoUp Q W x' ψ') := by
      rcases hrel with hlt | ⟨heq, hsbl⟩
      · refine rel_isoUp_of_lt_new hT hQ hW hC hc hc' hx' hk1'' hcx' hψc hψ' (fun v hv ↦ ?_) ?_
        · have hvc := (uc_rel_of_mem_chdOf hF hC hc).right.right.left.left hv
          obtain ⟨i, hi, rfl⟩ := hnode v hvc
          rw [mem_succ_iff] at hi
          rcases hi with hik | hi
          · exfalso
            rw [hik] at hv
            have hUC := uc_mem_stduoci_of_mem_otci_two hF hC
            rw [ndOf_aoc_val_one_eq hUC, mem_iniSegNds_iff, dom_sig_uc_eq_depOf hF hC, hdC] at hv
            obtain ⟨j, hj, hje⟩ := hv
            rw [sigdcn_anc hF hx hk hj] at hje
            have hjd : j ∈ dom (sig (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ k)))) := by
              rw [hdcs]; exact mem_succ_of_mem hj
            have hkd : k ∈ dom (sig (uc (ancOf (tensorProdTwoTwo (T ﹫ 2) Q) x (succ k)))) := by
              rw [hdcs]; exact mem_succ_self _
            rw [← sigdcn_anc hF hx hk1 (mem_succ_of_mem hj)] at hje
            have := congrArg lbl hje
            rw [lbl_sigdcn hUc hjd, lbl_sigdcn hUc hkd] at this
            rw [this] at hj
            exact notMem_self _ hj
          · exact hagrc i hi
        · rw [hdC, hsdc]
          rw [embRestrict_anc_val hF hx hψ hk1 (by rw [hsdc] at hkin; exact hkin)]
          rw [hsdk] at hlt
          exact hlt
      · refine rel_isoUp_of_sbl hT hQ hW hC hc hc' hx' hk1'' hcx' hψc hψ' (fun v hv ↦ ?_) hsbl
        obtain ⟨i, hi, rfl⟩ := hnode v hv
        rw [mem_succ_iff] at hi
        rcases hi with hik | hi
        · rw [hik, hsdc, embRestrict_anc_val hF hx hψ hk1 (by rw [hsdc] at hkin; exact hkin), heq,
            hsdk]
        · exact hagrc i hi
    rcases hle with h1 | h1
    · rw [h1]; exact h2
    · exact hR.right.right.left.trans (hR.mem_left h1) (hR.mem_right h1) (hR.mem_right h2) h1 h2

end UpMain


section LhsNds

variable {T Q W : M}

theorem tensorProdATwoATwo_val_one (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M)) :
    tensorProdATwoATwo T Q ﹫ ((1 : ℕ) : M) = tensorProdATwoAOne T (Q ↾ 2) ﹫ ((1 : ℕ) : M) := by
  have hB := tensorProdATwoAOne_mem_aotci hT (restrict_two_mem_aotci_one hQ)
  obtain ⟨hBf, hBdom, -⟩ := mem_aotci_iff.mp hB
  rw [tensorProdATwoATwo, cc_val_of_mem hBf _ (by rw [hBdom]; exact mem_succ_self _)]

theorem tensorProdATwoATwo_val_two (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M)) :
    tensorProdATwoATwo T Q ﹫ (2 : M) = tensorProdTwoTwo (T ﹫ 2) Q := by
  have hB := tensorProdATwoAOne_mem_aotci hT (restrict_two_mem_aotci_one hQ)
  obtain ⟨hBf, hBdom, -⟩ := mem_aotci_iff.mp hB
  have h := cc_val_self hBf (tensorProdTwoTwo (T ﹫ 2) Q)
  rw [hBdom] at h
  exact h

/-- The nodes of the level-`1` tree of `T ⊗ X` for `T ∈ aotci_2`: the relabeled nodes of `T(1)` and
the nodes of `T(2) ⊗ X` -/
theorem mem_ndOf_tensorProdATwoAOne_iff' (hT : T ∈ aotci ((2 : ℕ) : M)) {X : M}
    (hX : X ∈ aotci ((1 : ℕ) : M)) {a : M} :
    a ∈ ndOf (tensorProdATwoAOne T X ﹫ ((1 : ℕ) : M)) ↔
      (∃ w ∈ ndOf (T ﹫ ((1 : ℕ) : M)), a = relabelOne trvAZero w) ∨
        a ∈ tensorProdTwoAOneNds (T ﹫ 2) X := by
  obtain ⟨hTf, hTdom, -⟩ := mem_aotci_iff.mp hT
  have h12 : ((1 : ℕ) : M) ∈ (2 : M) := natCast_one_mem_two
  have hT1 : (T ↾ (2 : M)) ﹫ ((1 : ℕ) : M) = T ﹫ ((1 : ℕ) : M) :=
    val_restrict T hTf h12 (by rw [hTdom]; exact mem_succ_of_mem h12)
  have hT1o : T ﹫ ((1 : ℕ) : M) ∈ otci ((1 : ℕ) : M) :=
    val_mem_otci_of_mem_aotci hT (mem_succ_of_mem natCast_one_mem_two)
  rw [mem_ndOf_tensorProdATwoAOne_val_one_iff hT hX, tensorProdATwoAOneBase_val_one, hT1,
    mem_ndOf_tensorProdOneAZero_iff hT1o]
  constructor
  · rintro (⟨w, hw, rfl⟩ | h)
    · exact .inl ⟨w, hw, rfl⟩
    · exact .inr h
  · rintro (⟨w, hw, rfl⟩ | h)
    · exact .inl ⟨w, hw, rfl⟩
    · exact .inr h

end LhsNds

section IsoMid

variable {T Q W : M}

omit [ModelsZF M] in
theorem tgt_restrict_eq_base (Q X : M) :
    tensorProdTwoAOneTgt (Q ↾ (2 : M)) = tensorProdATwoAOneBase Q X := rfl

/-- The image `(t, ρ ∘ f)` of the node `ρ(t, f)` of the base of `(T ⊗ Q) ⊗ W` -/
noncomputable def isoMid (Q W t f : M) : M :=
  !(dctUZero, !(t, tauEmb Q W W (aoc (uc t)) ∅ f))

theorem tauEmb_base_val (hQ : Q ∈ aotci ((2 : ℕ) : M)) {A f w : M} (hA : A ∈ aotci ((1 : ℕ) : M))
    (hf : f ∈ aotciEmbSet ((1 : ℕ) : M) A (tensorProdTwoAOneTgt (Q ↾ (2 : M))))
    (hw : w ∈ ndOf (A ﹫ ((1 : ℕ) : M))) :
    (tauEmb Q W W A ∅ f ﹫ ((1 : ℕ) : M)) ﹫ w = relabelOne trvAZero ((f ﹫ ((1 : ℕ) : M)) ﹫ w) ∧
      (f ﹫ ((1 : ℕ) : M)) ﹫ w ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M)) := by
  have hB0 := tensorProdATwoAOneBase_mem_aotci hQ W
  have hfw := emb_val_mem hA hB0 hf hw
  refine ⟨?_, hfw⟩
  obtain ⟨-, hfd⟩ := embChg_val_one_isFunction hf
  rw [tauEmb, embMk_val_one, (tauOne_spec Q W W ∅ f).right.right w (by rw [hfd]; exact hw)]
  congr 1
  refine pushNd_of_not fun h ↦ ?_
  have h' : (f ﹫ ((1 : ℕ) : M)) ﹫ w ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M)) ∩
      ndOf (tensorProdTwoAOne (Q ﹫ (2 : M)) W) := by
    rw [mem_inter_iff, ndOf_tensorProdTwoAOne]
    exact ⟨hfw, h⟩
  rw [ndOf_base_inter_ndOf_tensorProdTwoAOne hQ W] at h'
  exact notin_empty _ h'

/-- `ρ ∘ f` is an embedding into `(Q ⊗ W) ⊗ Z` -/
theorem tauEmb_base_mem (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hW : W ∈ aotci ((1 : ℕ) : M)) {A f : M}
    (hA : A ∈ aotci ((1 : ℕ) : M))
    (hf : f ∈ aotciEmbSet ((1 : ℕ) : M) A (tensorProdTwoAOneTgt (Q ↾ (2 : M)))) :
    tauEmb Q W W A ∅ f ∈
      aotciEmbSet ((1 : ℕ) : M) A (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W)) := by
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hBW1 := val_mem_otci_of_mem_aotci hBW (mem_succ_self _)
  have hT := tensorProdTwoAOneTgt_mem hBW
  have hB0 := tensorProdATwoAOneBase_mem_aotci hQ W
  obtain ⟨-, hfd⟩ := embChg_val_one_isFunction hf
  have hbase (z : M) (hz : z ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M))) :
      z ∈ ndOf (tensorProdATwoAOne Q W ﹫ ((1 : ℕ) : M)) :=
    (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hW).mpr (.inl hz)
  refine embMk_mem_aotciEmbSet' hA hT (tauOne_spec Q W W ∅ f).left
    (by rw [(tauOne_spec Q W W ∅ f).right.left, hfd]) (fun a ha ↦ ?_) (fun a ha b hb hab ↦ ?_)
  · have h := (tauEmb_base_val (W := W) hQ hA hf ha)
    rw [tauEmb, embMk_val_one] at h
    rw [h.left, tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hBW1]
    exact ⟨_, hbase _ h.right, rfl⟩
  · have h := (tauEmb_base_val (W := W) hQ hA hf ha)
    have h' := (tauEmb_base_val (W := W) hQ hA hf hb)
    rw [tauEmb, embMk_val_one] at h h'
    rw [h.left, h'.left, rel_tgt_relabel_iff hBW (hbase _ h.right) (hbase _ h'.right),
      rel_odrOne_tensorProdATwoAOne_iff hQ hW]
    exact .inl (emb_odr hA hB0 hf ha hb hab)

/-- The image of a node of `T(2) ⊗ (Q ↾ 2)` is an upper node of `T ⊗ (Q ⊗ W)` -/
theorem isoMid_mem (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {t f : M}
    (hy : !(dctUZero, !(t, f)) ∈ tensorProdTwoAOneNds (T ﹫ 2) (Q ↾ (2 : M))) :
    isoMid Q W t f ∈ tensorProdTwoAOneNds (T ﹫ 2) (tensorProdATwoAOne Q W) := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  obtain ⟨t', ht, htr, f', hf, he⟩ := mem_tensorProdTwoAOneNds_iff'.mp hy
  rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at he
  obtain ⟨-, rfl, rfl⟩ := he
  exact mem_tensorProdTwoAOneNds_iff'.mpr ⟨t, ht, htr, _, tauEmb_base_mem hQ hW
    (aoc_mem_aotci_of_mem_stduoci_one (uc_mem_stduoci_of_mem_otci_two hP ht)) hf, rfl⟩

/-- The coordinates of the image of a node of `T(2) ⊗ (Q ↾ 2)` -/
theorem seq_tauEmb_base_val (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {t f i : M} (ht : t ∈ ndOf (T ﹫ 2))
    (hf : f ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdTwoAOneTgt (Q ↾ (2 : M))))
    (hi : i ∈ depOf (T ﹫ 2) t) :
    tensorProdTwoAOneSeq (T ﹫ 2) !(t, tauEmb Q W W (aoc (uc t)) ∅ f) ﹫ i =
      !(relabelOne trvAZero ((f ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i), ancOf (T ﹫ 2) t (succ i)) ∧
      (f ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M))
          := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hw := (siglvl_eq_one hUt (by rw [dom_sig_uc_eq_depOf hP ht]; exact hi)).right
  have h := tauEmb_base_val (W := W) hQ (aoc_mem_aotci_of_mem_stduoci_one hUt) hf hw
  rw [tensorProdTwoAOneSeq_val hP ht hi, h.left]
  exact ⟨rfl, h.right⟩

/-- The relabeling is an isomorphism of the coordinate orders on the base coordinates -/
theorem coordOdr_relabel_iff (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {a₁ a₂ b₁ b₂ : M}
    (ha₁ : a₁ ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M)))
    (hb₁ : b₁ ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M))) :
    !(a₁, a₂) [tensorProdTwoAOneCoordOdr (T ﹫ 2) (Q ↾ (2 : M))] !(b₁, b₂) ↔
      !(relabelOne trvAZero a₁, a₂)
        [tensorProdTwoAOneCoordOdr (T ﹫ 2) (tensorProdATwoAOne Q W)]
        !(relabelOne trvAZero b₁, b₂) := by
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hBW1 := val_mem_otci_of_mem_aotci hBW (mem_succ_self _)
  have hB01 := val_mem_otci_of_mem_aotci (tensorProdATwoAOneBase_mem_aotci hQ W) (mem_succ_self _)
  have hbase (z : M) (hz : z ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M))) :
      z ∈ ndOf (tensorProdATwoAOne Q W ﹫ ((1 : ℕ) : M)) :=
    (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hW).mpr (.inl hz)
  have hmem (z : M) (hz : z ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M))) :
      relabelOne trvAZero z ∈ ndOf (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))
          := by
    rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hBW1]
    exact ⟨_, hbase z hz, rfl⟩
  have hupper (z : M) (hz : z ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M)))
      (hz' : z ∈ tensorProdTwoAOneNds (Q ﹫ 2) W) : False := by
    have h' : z ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M)) ∩
        ndOf (tensorProdTwoAOne (Q ﹫ (2 : M)) W) := by
      rw [mem_inter_iff, ndOf_tensorProdTwoAOne]; exact ⟨hz, hz'⟩
    rw [ndOf_base_inter_ndOf_tensorProdTwoAOne hQ W] at h'
    exact notin_empty _ h'
  have hRB := (rtlosOf_of_mem_otci_one hB01).left
  have hord : a₁ [odrOne (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M))] b₁ ↔
      (relabelOne trvAZero a₁) [odrOne (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W) ﹫
        ((1 : ℕ) : M))] (relabelOne trvAZero b₁) := by
    rw [rel_tgt_relabel_iff hBW (hbase _ ha₁) (hbase _ hb₁),
        rel_odrOne_tensorProdATwoAOne_iff hQ hW]
    constructor
    · exact fun h ↦ .inl h
    · rintro (h | ⟨h, -⟩ | ⟨-, h⟩)
      · exact h
      · exact (hupper _ ha₁ h).elim
      · exact (hupper _ hb₁ h).elim
  have heq : a₁ = b₁ ↔ relabelOne trvAZero a₁ = relabelOne trvAZero b₁ :=
    ⟨fun h ↦ by rw [h], fun h ↦ relabelOne_injective hB01 ha₁ hb₁ h⟩
  unfold tensorProdTwoAOneCoordOdr
  rw [rel_lexProd_iff, rel_lexProd_iff, tgt_restrict_eq_base Q W]
  change _ ∧ _ ∧ (a₁ [odrOne (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M))] b₁ ∨ _) ↔
    _ ∧ _ ∧ ((relabelOne trvAZero a₁) [odrOne (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W) ﹫
      ((1 : ℕ) : M))] (relabelOne trvAZero b₁) ∨ _)
  rw [hord, heq]
  constructor
  · rintro ⟨⟨-, ha₂⟩, ⟨-, hb₂⟩, h⟩
    exact ⟨⟨hmem _ ha₁, ha₂⟩, ⟨hmem _ hb₁, hb₂⟩, h⟩
  · rintro ⟨⟨-, ha₂⟩, ⟨-, hb₂⟩, h⟩
    exact ⟨⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩, h⟩

/-- The order of the images of the nodes of `T(2) ⊗ (Q ↾ 2)` -/
theorem rel_isoMid_iff (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {t f t' f' : M}
    (hy : !(dctUZero, !(t, f)) ∈ tensorProdTwoAOneNds (T ﹫ 2) (Q ↾ (2 : M)))
    (hy' : !(dctUZero, !(t', f')) ∈ tensorProdTwoAOneNds (T ﹫ 2) (Q ↾ (2 : M))) :
    TensorProdTwoAOneLt (T ﹫ 2) (Q ↾ (2 : M)) !(t, f) !(t', f') ↔
      (isoMid Q W t f) [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
        (isoMid Q W t' f') := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hTS := (otciCond_two hP).left.isTreeStructure
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  rw [rel_odrOne_tensorProdATwoAOne_iff_of_mem hT hBW (isoMid_mem hT hQ hW hy)]
  obtain ⟨t₁, ht, -, f₁, hf, he⟩ := mem_tensorProdTwoAOneNds_iff'.mp hy
  rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at he
  obtain ⟨-, rfl, rfl⟩ := he
  obtain ⟨t₂, ht', -, f₂, hf', he'⟩ := mem_tensorProdTwoAOneNds_iff'.mp hy'
  rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at he'
  obtain ⟨-, rfl, rfl⟩ := he'
  unfold TensorProdTwoAOneLt
  rw [isoMid, isoMid, lbl_orderedPair, lbl_orderedPair]
  let κ : M → M := fun c ↦ !(relabelOne trvAZero (left c), right c)
  have hcoord {p g : M} (hp : p ∈ ndOf (T ﹫ 2))
      (hg : g ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) (tensorProdTwoAOneTgt (Q ↾ (2 : M)))) :
      ∀ i ∈ dom (tensorProdTwoAOneSeq (T ﹫ 2) !(p, g)),
        tensorProdTwoAOneSeq (T ﹫ 2) !(p, tauEmb Q W W (aoc (uc p)) ∅ g) ﹫ i =
          κ (tensorProdTwoAOneSeq (T ﹫ 2) !(p, g) ﹫ i) ∧
        tensorProdTwoAOneSeq (T ﹫ 2) !(p, g) ﹫ i ∈
          ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M)) ×ˢ ndOf (T ﹫ 2) := by
    intro i hi
    rw [tensorProdTwoAOneSeq_dom] at hi
    obtain ⟨hv, hb⟩ := seq_tauEmb_base_val (W := W) hT hQ hp hg hi
    rw [hv, tensorProdTwoAOneSeq_val hP hp hi]
    refine ⟨by simp only [κ, left_orderedPair, right_orderedPair], ?_⟩
    rw [pair_mem_sprod_iff]
    exact ⟨hb, (hTS.anc_mem_nd hp (succ_mem_succ_of_mem (hTS.dep_mem_omega hp) hi)).left⟩
  have hB01 := val_mem_otci_of_mem_aotci (tensorProdATwoAOneBase_mem_aotci hQ W) (mem_succ_self _)
  have hiff := bkLt_iff_of_map (R := tensorProdTwoAOneCoordOdr (T ﹫ 2) (Q ↾ (2 : M)))
    (R' := tensorProdTwoAOneCoordOdr (T ﹫ 2) (tensorProdATwoAOne Q W)) κ
    (isFunction_tensorProdTwoAOneSeq _ _) (isFunction_tensorProdTwoAOneSeq _ _)
    (isFunction_tensorProdTwoAOneSeq _ _) (isFunction_tensorProdTwoAOneSeq _ _)
    (by rw [tensorProdTwoAOneSeq_dom, tensorProdTwoAOneSeq_dom])
    (by rw [tensorProdTwoAOneSeq_dom, tensorProdTwoAOneSeq_dom])
    (fun i hi ↦ (hcoord ht hf i hi).left) (fun i hi ↦ (hcoord ht' hf' i hi).left)
    (fun i hi ↦ (hcoord ht hf i hi).right) (fun i hi ↦ (hcoord ht' hf' i hi).right)
    (fun a ha b hb hab ↦ ?_) (fun a ha b hb ↦ ?_)
    (by rw [tensorProdTwoAOneSeq_dom]
        exact ordinal_of_mem ordinal_omega (hTS.dep_mem_omega ht))
    (by rw [tensorProdTwoAOneSeq_dom]
        exact ordinal_of_mem ordinal_omega (hTS.dep_mem_omega ht'))
  · rw [hiff]
    exact ⟨fun h ↦ ⟨isoMid_mem hT hQ hW hy', h⟩, fun h ↦ h.right⟩
  · rw [mem_sprod_iff] at ha hb
    obtain ⟨a₁, ha₁, a₂, -, rfl⟩ := ha
    obtain ⟨b₁, hb₁, b₂, -, rfl⟩ := hb
    simp only [κ, left_orderedPair, right_orderedPair, orderedPair_eq_orderedPair_iff] at hab
    rw [relabelOne_injective hB01 ha₁ hb₁ hab.left, hab.right]
  · rw [mem_sprod_iff] at ha hb
    obtain ⟨a₁, ha₁, a₂, -, rfl⟩ := ha
    obtain ⟨b₁, hb₁, b₂, -, rfl⟩ := hb
    simp only [κ, left_orderedPair, right_orderedPair]
    exact coordOdr_relabel_iff hQ hW ha₁ hb₁

/-- The images of the base nodes `ρ(t, f)` are below the images of the upper nodes: compare at the
first coordinate, from `Q(1)` and from `Q(2)` -/
theorem rel_isoMid_isoUpOf (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {t f V t' σ ψ : M}
    (hy : !(dctUZero, !(t, f)) ∈ tensorProdTwoAOneNds (T ﹫ 2) (Q ↾ (2 : M)))
    (hx : !(V, !(t', σ)) ∈ tensorProdTwoTwoNds (T ﹫ 2) Q) (hs : sig V ≠ ∅)
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W)) :
    (isoMid Q W t f) [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
      (isoUpOf Q W V t' σ ψ) := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hPs := (otciCond_two hP).left
  have hTS := hPs.isTreeStructure
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hBW1 := val_mem_otci_of_mem_aotci hBW (mem_succ_self _)
  rw [rel_odrOne_tensorProdATwoAOne_iff_of_mem hT hBW (isoMid_mem hT hQ hW hy)]
  refine ⟨isoUpOf_mem hP hQ hW hx hs hψ, ?_⟩
  obtain ⟨t₁, ht, htr, f₁, hf, he⟩ := mem_tensorProdTwoAOneNds_iff'.mp hy
  rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at he
  obtain ⟨-, rfl, rfl⟩ := he
  obtain ⟨h0t', hz⟩ := row_zero_isTpTwo hP hQ hx hs
  have hx' := hx
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hx'
  obtain ⟨ht', hV, hσ, -⟩ := hx'
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have h0t : ∅ ∈ depOf (T ﹫ 2) t := empty_mem_depOf_of_not_mem_rtOf hPs ht htr
  unfold TensorProdTwoAOneLt
  rw [isoMid, isoUpOf, lbl_orderedPair, lbl_orderedPair]
  unfold BKLt
  right
  refine ⟨∅, by rw [tensorProdTwoAOneSeq_dom]; exact h0t,
      by rw [tensorProdTwoAOneSeq_dom]; exact h0t',
    (isFunction_tensorProdTwoAOneSeq _ _).restrict_eq_restrict (isFunction_tensorProdTwoAOneSeq _ _)
      (fun _ h ↦ (notin_empty _ h).elim) (fun _ h ↦ (notin_empty _ h).elim)
      fun _ h ↦ (notin_empty _ h).elim, ?_⟩
  obtain ⟨hv, hb⟩ := seq_tauEmb_base_val (W := W) hT hQ ht hf h0t
  rw [hv, seq_tauEmb_val hP ht' hσ h0t', tensorProdTwoAOneCoordOdr, rel_lexProd_iff]
  have hzW := pushNd_mem_of_mem hQ hX hW hψ hz
  have hbB := (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hW).mpr (.inl hb)
  have huB := (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hW).mpr (.inr hzW)
  refine ⟨⟨?_, (hTS.anc_mem_nd ht (succ_mem_succ_of_mem (hTS.dep_mem_omega ht) h0t)).left⟩,
    ⟨?_, (hTS.anc_mem_nd ht' (succ_mem_succ_of_mem (hTS.dep_mem_omega ht') h0t')).left⟩,
    .inl ((rel_tgt_relabel_iff hBW hbB huB).mpr
      ((rel_odrOne_tensorProdATwoAOne_iff hQ hW).mpr (.inr (.inr ⟨hb, hzW⟩))))⟩
  · rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hBW1]
    exact ⟨_, hbB, rfl⟩
  · rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hBW1]
    exact ⟨_, huB, rfl⟩

end IsoMid

section IsoOne

variable {T Q W : M}

/-- `a` is an upper node of `(T ⊗ Q) ⊗ W` -/
def IsUpNd (T Q W a : M) : Prop := a ∈ tensorProdTwoAOneNds (tensorProdTwoTwo (T ﹫ 2) Q) W

/-- `a` comes from a node of `T(2) ⊗ (Q ↾ 2)` -/
def IsMidNd (T Q a : M) : Prop := unrel a ∈ tensorProdTwoAOneNds (T ﹫ 2) (Q ↾ (2 : M))

noncomputable instance (T Q W a : M) : Decidable (IsUpNd T Q W a) := Classical.propDecidable _
noncomputable instance (T Q a : M) : Decidable (IsMidNd T Q a) := Classical.propDecidable _

/-- The level-`1` map `(T ⊗ Q) ⊗ W → T ⊗ (Q ⊗ W)` -/
noncomputable def isoOne (T Q W a : M) : M :=
  if IsUpNd T Q W a then isoUp Q W (left (lbl a)) (right (lbl a))
  else if IsMidNd T Q a then isoMid Q W (left (lbl (unrel a))) (right (lbl (unrel a)))
  else unrel a

/-- The nodes of the level-`1` tree of `(T ⊗ Q) ⊗ W`: from `T(1)`, from `T(2) ⊗ (Q ↾ 2)` and the
upper nodes -/
theorem lhs_cases (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {a : M}
    (ha : a ∈ ndOf (tensorProdATwoAOne (tensorProdATwoATwo T Q) W ﹫ ((1 : ℕ) : M))) :
    (∃ w ∈ ndOf (T ﹫ ((1 : ℕ) : M)), a = relabelOne trvAZero (relabelOne trvAZero w)) ∨
      (∃ t f, !(dctUZero, !(t, f)) ∈ tensorProdTwoAOneNds (T ﹫ 2) (Q ↾ (2 : M)) ∧
        a = relabelOne trvAZero !(dctUZero, !(t, f))) ∨
      a ∈ tensorProdTwoAOneNds (tensorProdTwoTwo (T ﹫ 2) Q) W := by
  have hF := tensorProdATwoATwo_mem_aotci hT hQ
  have hQ2 := restrict_two_mem_aotci_one hQ
  obtain ⟨hFf, hFdom, -⟩ := mem_aotci_iff.mp hF
  have h12 : ((1 : ℕ) : M) ∈ (2 : M) := natCast_one_mem_two
  have hF1 : (tensorProdATwoATwo T Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M) =
      tensorProdATwoAOne T (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M) := by
    rw [val_restrict _ hFf h12 (by rw [hFdom]; exact mem_succ_of_mem h12),
      tensorProdATwoATwo_val_one hT hQ]
  have hF1o : tensorProdATwoAOne T (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M) ∈ otci ((1 : ℕ) : M) :=
    val_mem_otci_of_mem_aotci (tensorProdATwoAOne_mem_aotci hT hQ2) (mem_succ_self _)
  rw [mem_ndOf_tensorProdATwoAOne_val_one_iff hF hW, tensorProdATwoAOneBase_val_one, hF1,
    mem_ndOf_tensorProdOneAZero_iff hF1o, tensorProdATwoATwo_val_two hT hQ] at ha
  rcases ha with ⟨a₀, ha₀, rfl⟩ | ha
  · rcases (mem_ndOf_tensorProdATwoAOne_iff' hT hQ2).mp ha₀ with ⟨w, hw, rfl⟩ | ha₀
    · exact .inl ⟨w, hw, rfl⟩
    · obtain ⟨t, -, -, f, -, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp ha₀
      exact .inr (.inl ⟨t, f, ha₀, rfl⟩)
  · exact .inr (.inr ha)

/-- The relabeled nodes of `T(1)` are base nodes of `T ⊗ X` -/
theorem relabelOne_mem_base (hT : T ∈ aotci ((2 : ℕ) : M)) (X : M) {w : M}
    (hw : w ∈ ndOf (T ﹫ ((1 : ℕ) : M))) :
    relabelOne trvAZero w ∈ ndOf (tensorProdATwoAOneBase T X ﹫ ((1 : ℕ) : M)) := by
  obtain ⟨hTf, hTdom, -⟩ := mem_aotci_iff.mp hT
  have h12 : ((1 : ℕ) : M) ∈ (2 : M) := natCast_one_mem_two
  have hT1 : (T ↾ (2 : M)) ﹫ ((1 : ℕ) : M) = T ﹫ ((1 : ℕ) : M) :=
    val_restrict T hTf h12 (by rw [hTdom]; exact mem_succ_of_mem h12)
  have hT1o : T ﹫ ((1 : ℕ) : M) ∈ otci ((1 : ℕ) : M) :=
    val_mem_otci_of_mem_aotci hT (mem_succ_of_mem natCast_one_mem_two)
  rw [tensorProdATwoAOneBase_val_one, hT1, mem_ndOf_tensorProdOneAZero_iff hT1o]
  exact ⟨w, hw, rfl⟩

/-- Base nodes of `T ⊗ X` are not upper nodes -/
theorem not_mem_upper_of_mem_base (hT : T ∈ aotci ((2 : ℕ) : M)) {X a : M}
    (ha : a ∈ ndOf (tensorProdATwoAOneBase T X ﹫ ((1 : ℕ) : M))) :
    a ∉ tensorProdTwoAOneNds (T ﹫ 2) X := fun h ↦ by
  have h' : a ∈ ndOf (tensorProdATwoAOneBase T X ﹫ ((1 : ℕ) : M)) ∩
      ndOf (tensorProdTwoAOne (T ﹫ (2 : M)) X) := by
    rw [mem_inter_iff, ndOf_tensorProdTwoAOne]; exact ⟨ha, h⟩
  rw [ndOf_base_inter_ndOf_tensorProdTwoAOne hT X] at h'
  exact notin_empty _ h'

/-- The relabeled nodes of `(T ⊗ (Q ↾ 2))(1)` are not upper nodes of `(T ⊗ Q) ⊗ W` -/
theorem not_isUpNd_relabelOne (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {a₀ : M} (ha₀ : a₀ ∈ ndOf (tensorProdATwoAOne T (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M))) :
    ¬ IsUpNd T Q W (relabelOne trvAZero a₀) := fun h ↦ by
  have hF := tensorProdATwoATwo_mem_aotci hT hQ
  have hQ2 := restrict_two_mem_aotci_one hQ
  obtain ⟨hFf, hFdom, -⟩ := mem_aotci_iff.mp hF
  have h12 : ((1 : ℕ) : M) ∈ (2 : M) := natCast_one_mem_two
  have hF1 : (tensorProdATwoATwo T Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M) =
      tensorProdATwoAOne T (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M) := by
    rw [val_restrict _ hFf h12 (by rw [hFdom]; exact mem_succ_of_mem h12),
      tensorProdATwoATwo_val_one hT hQ]
  have hF1o : tensorProdATwoAOne T (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M) ∈ otci ((1 : ℕ) : M) :=
    val_mem_otci_of_mem_aotci (tensorProdATwoAOne_mem_aotci hT hQ2) (mem_succ_self _)
  have hb : relabelOne trvAZero a₀ ∈
      ndOf (tensorProdATwoAOneBase (tensorProdATwoATwo T Q) W ﹫ ((1 : ℕ) : M)) := by
    rw [tensorProdATwoAOneBase_val_one, hF1, mem_ndOf_tensorProdOneAZero_iff hF1o]
    exact ⟨a₀, ha₀, rfl⟩
  refine not_mem_upper_of_mem_base hF hb ?_
  rw [tensorProdATwoATwo_val_two hT hQ]
  exact h

theorem isoOne_up {a : M} (ha : a ∈ tensorProdTwoAOneNds (tensorProdTwoTwo (T ﹫ 2) Q) W) :
    isoOne T Q W a = isoUp Q W (left (lbl a)) (right (lbl a)) := by
  rw [isoOne, if_pos (show IsUpNd T Q W a from ha)]

theorem isoOne_mid (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M)) {t f : M}
    (hy : !(dctUZero, !(t, f)) ∈ tensorProdTwoAOneNds (T ﹫ 2) (Q ↾ (2 : M))) :
    isoOne T Q W (relabelOne trvAZero !(dctUZero, !(t, f))) = isoMid Q W t f := by
  have hQ2 := restrict_two_mem_aotci_one hQ
  have hy' := (mem_ndOf_tensorProdATwoAOne_val_one_iff hT hQ2).mpr (.inr hy)
  have hu := unrel_relabelOne (w := !(dctUZero, !(t, f))) ⟨_, _, rfl⟩ trvAZero
  have hmid : IsMidNd T Q (relabelOne trvAZero !(dctUZero, !(t, f))) := by
    unfold IsMidNd; rw [hu]; exact hy
  rw [isoOne, if_neg (not_isUpNd_relabelOne hT hQ hy'), if_pos hmid, hu, lbl_orderedPair,
    left_orderedPair, right_orderedPair]

theorem isoOne_low (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M)) {w : M}
    (hw : w ∈ ndOf (T ﹫ ((1 : ℕ) : M))) :
    isoOne T Q W (relabelOne trvAZero (relabelOne trvAZero w)) = relabelOne trvAZero w := by
  have hQ2 := restrict_two_mem_aotci_one hQ
  have hb := relabelOne_mem_base hT (Q ↾ (2 : M)) hw
  have hw' := (mem_ndOf_tensorProdATwoAOne_val_one_iff hT hQ2).mpr (.inl hb)
  have hT1o : T ﹫ ((1 : ℕ) : M) ∈ otci ((1 : ℕ) : M) :=
    val_mem_otci_of_mem_aotci hT (mem_succ_of_mem natCast_one_mem_two)
  have hu := unrel_relabelOne (w := relabelOne trvAZero w)
    ⟨_, _, rfl⟩ trvAZero
  have hmid : ¬ IsMidNd T Q (relabelOne trvAZero (relabelOne trvAZero w)) := by
    unfold IsMidNd; rw [hu]; exact not_mem_upper_of_mem_base hT hb
  rw [isoOne, if_neg (not_isUpNd_relabelOne hT hQ hw'), if_neg hmid, hu]

end IsoOne

section IsoOneOrder

variable {T Q W : M}

theorem upper_data (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M)) {a : M}
    (ha : a ∈ tensorProdTwoAOneNds (tensorProdTwoTwo (T ﹫ 2) Q) W) :
    ∃ V t σ ψ, a = !(dctUZero, !(!(V, !(t, σ)), ψ)) ∧
      !(V, !(t, σ)) ∈ tensorProdTwoTwoNds (T ﹫ 2) Q ∧ sig V ≠ ∅ ∧
      ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W) ∧
      !(V, !(t, σ)) ∉ rtOf (tensorProdTwoTwo (T ﹫ 2) Q) := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hF := tensorProdTwoTwo_mem_otci hP hQ
  obtain ⟨x, hx, hxr, ψ, hψ, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp ha
  have hxN := hx
  rw [ndOf_tensorProdTwoTwo] at hxN
  obtain ⟨t, -, V, -, σ, -, -, rfl⟩ := mem_tensorProdTwoTwoNds_iff.mp hxN
  rw [uc_orderedPair] at hψ
  have hs : sig V ≠ ∅ := fun h0 ↦ by
    have h' := empty_mem_depOf_of_not_mem_rtOf (otciCond_two hF).left hx hxr
    rw [← dom_sig_uc_eq_depOf hF hx, uc_orderedPair, h0, dom_empty] at h'
    exact notin_empty _ h'
  exact ⟨V, t, σ, ψ, rfl, hxN, hs, hψ, hxr⟩

/-- The values of the level-`1` map are nodes of `T ⊗ (Q ⊗ W)` -/
theorem isoOne_mem (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {a : M}
    (ha : a ∈ ndOf (tensorProdATwoAOne (tensorProdATwoATwo T Q) W ﹫ ((1 : ℕ) : M))) :
    isoOne T Q W a ∈ ndOf (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)) := by
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  rcases lhs_cases hT hQ hW ha with ⟨w, hw, rfl⟩ | ⟨t, f, hy, rfl⟩ | ha
  · rw [isoOne_low hT hQ hw]
    exact (mem_ndOf_tensorProdATwoAOne_iff' hT hBW).mpr (.inl ⟨w, hw, rfl⟩)
  · rw [isoOne_mid hT hQ hy]
    exact (mem_ndOf_tensorProdATwoAOne_iff' hT hBW).mpr (.inr (isoMid_mem hT hQ hW hy))
  · rw [isoOne_up ha]
    obtain ⟨V, t, σ, ψ, rfl, hx, hs, hψ, -⟩ := upper_data hT hQ ha
    simp only [lbl_orderedPair, left_orderedPair, right_orderedPair]
    rw [isoUp_orderedPair]
    exact isoUpOf_mem_ndOf hT hQ hW hx hs hψ

/-- The order of `(P ⊗ X)(1)` on base nodes is the base order -/
theorem rel_base_iff {P X a b : M} (hP : P ∈ aotci ((2 : ℕ) : M)) (hX : X ∈ aotci ((1 : ℕ) : M))
    (ha : a ∈ ndOf (tensorProdATwoAOneBase P X ﹫ ((1 : ℕ) : M)))
    (hb : b ∈ ndOf (tensorProdATwoAOneBase P X ﹫ ((1 : ℕ) : M))) :
    a [odrOne (tensorProdATwoAOne P X ﹫ ((1 : ℕ) : M))] b ↔
      a [odrOne (tensorProdATwoAOneBase P X ﹫ ((1 : ℕ) : M))] b := by
  rw [rel_odrOne_tensorProdATwoAOne_iff hP hX]
  constructor
  · rintro (h | ⟨h, -⟩ | ⟨-, h⟩)
    · exact h
    · exact (not_mem_upper_of_mem_base hP ha h).elim
    · exact (not_mem_upper_of_mem_base hP hb h).elim
  · exact fun h ↦ .inl h

/-- The base order of `P ⊗ X` on relabeled nodes is the order of `P(1)` -/
theorem rel_relabel_base_iff {P X u u' : M} (hP : P ∈ aotci ((2 : ℕ) : M))
    (hu : u ∈ ndOf (P ﹫ ((1 : ℕ) : M))) (hu' : u' ∈ ndOf (P ﹫ ((1 : ℕ) : M))) :
    (relabelOne trvAZero u) [odrOne (tensorProdATwoAOneBase P X ﹫ ((1 : ℕ) : M))]
        (relabelOne trvAZero u') ↔ u [odrOne (P ﹫ ((1 : ℕ) : M))] u' := by
  obtain ⟨hPf, hPdom, -⟩ := mem_aotci_iff.mp hP
  have h12 : ((1 : ℕ) : M) ∈ (2 : M) := natCast_one_mem_two
  have hP1 : (P ↾ (2 : M)) ﹫ ((1 : ℕ) : M) = P ﹫ ((1 : ℕ) : M) :=
    val_restrict P hPf h12 (by rw [hPdom]; exact mem_succ_of_mem h12)
  have hP1o : P ﹫ ((1 : ℕ) : M) ∈ otci ((1 : ℕ) : M) :=
    val_mem_otci_of_mem_aotci hP (mem_succ_of_mem natCast_one_mem_two)
  rw [tensorProdATwoAOneBase_val_one, hP1]
  exact rel_odrOne_tensorProdOneAZero_iff hP1o hu hu' _

/-- The order of the base of `(T ⊗ Q) ⊗ W` is that of `(T ⊗ (Q ↾ 2))(1)` -/
theorem lhs_base_rel_iff (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {a₀ b₀ : M}
    (ha₀ : a₀ ∈ ndOf (tensorProdATwoAOne T (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M)))
    (hb₀ : b₀ ∈ ndOf (tensorProdATwoAOne T (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M))) :
    (relabelOne trvAZero a₀)
        [odrOne (tensorProdATwoAOne (tensorProdATwoATwo T Q) W ﹫ ((1 : ℕ) : M))]
        (relabelOne trvAZero b₀) ↔
      a₀ [odrOne (tensorProdATwoAOne T (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M))] b₀ := by
  have hF := tensorProdATwoATwo_mem_aotci hT hQ
  have hF1 : tensorProdATwoATwo T Q ﹫ ((1 : ℕ) : M) =
      tensorProdATwoAOne T (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M) := tensorProdATwoATwo_val_one hT hQ
  have ha := ha₀
  have hb := hb₀
  rw [← hF1] at ha hb
  rw [rel_base_iff hF hW (relabelOne_mem_base hF W ha) (relabelOne_mem_base hF W hb),
    rel_relabel_base_iff hF ha hb, hF1]

/-- (Order) The level-`1` map preserves the order -/
theorem isoOne_lt (hT : T ∈ aotci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {a b : M}
    (ha : a ∈ ndOf (tensorProdATwoAOne (tensorProdATwoATwo T Q) W ﹫ ((1 : ℕ) : M)))
    (hb : b ∈ ndOf (tensorProdATwoAOne (tensorProdATwoATwo T Q) W ﹫ ((1 : ℕ) : M)))
    (hab : a [odrOne (tensorProdATwoAOne (tensorProdATwoATwo T Q) W ﹫ ((1 : ℕ) : M))] b) :
    (isoOne T Q W a) [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
      (isoOne T Q W b) := by
  have hP : T ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hT (mem_succ_self _)
  have hF := tensorProdATwoATwo_mem_aotci hT hQ
  have hQ2 := restrict_two_mem_aotci_one hQ
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hNM {y : M} (hy : y ∈ tensorProdTwoAOneNds (T ﹫ 2) (Q ↾ (2 : M))) :
      y ∈ ndOf (tensorProdATwoAOne T (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M)) :=
    (mem_ndOf_tensorProdATwoAOne_val_one_iff hT hQ2).mpr (.inr hy)
  have hLow {w : M} (hw : w ∈ ndOf (T ﹫ ((1 : ℕ) : M))) :
      relabelOne trvAZero w ∈ ndOf (tensorProdATwoAOne T (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M)) :=
    (mem_ndOf_tensorProdATwoAOne_val_one_iff hT hQ2).mpr (.inl (relabelOne_mem_base hT _ hw))
  have hupLt {a b : M} (ha : a ∈ tensorProdTwoAOneNds (tensorProdTwoTwo (T ﹫ 2) Q) W)
      (hab : a [odrOne (tensorProdATwoAOne (tensorProdATwoATwo T Q) W ﹫ ((1 : ℕ) : M))] b) :
      b ∈ tensorProdTwoAOneNds (tensorProdTwoTwo (T ﹫ 2) Q) W ∧
        TensorProdTwoAOneLt (tensorProdTwoTwo (T ﹫ 2) Q) W (lbl a) (lbl b) := by
    rw [← tensorProdATwoATwo_val_two hT hQ] at ha ⊢
    exact (rel_odrOne_tensorProdATwoAOne_iff_of_mem hF hW ha).mp hab
  have hRup {V t σ ψ : M} (hx : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds (T ﹫ 2) Q) (hs : sig V ≠ ∅)
      (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W)) :
      isoUpOf Q W V t σ ψ ∈ tensorProdTwoAOneNds (T ﹫ 2) (tensorProdATwoAOne Q W) :=
    isoUpOf_mem hP hQ hW hx hs hψ
  have hlow_up {w y : M} (hw : w ∈ ndOf (T ﹫ ((1 : ℕ) : M)))
      (hy : y ∈ tensorProdTwoAOneNds (T ﹫ 2) (tensorProdATwoAOne Q W)) :
      (relabelOne trvAZero w)
        [odrOne (tensorProdATwoAOne T (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))] y :=
    (rel_odrOne_tensorProdATwoAOne_iff hT hBW).mpr (.inr (.inr ⟨relabelOne_mem_base hT _ hw, hy⟩))
  rcases lhs_cases hT hQ hW ha with ⟨w, hw, rfl⟩ | ⟨t, f, hy, rfl⟩ | hau <;>
    rcases lhs_cases hT hQ hW hb with ⟨w', hw', rfl⟩ | ⟨t', f', hy', rfl⟩ | hbu
  · rw [isoOne_low hT hQ hw, isoOne_low hT hQ hw']
    rw [lhs_base_rel_iff hT hQ hW (hLow hw) (hLow hw'), rel_base_iff hT hQ2
      (relabelOne_mem_base hT _ hw) (relabelOne_mem_base hT _ hw'),
      rel_relabel_base_iff hT hw hw'] at hab
    rw [rel_base_iff hT hBW (relabelOne_mem_base hT _ hw) (relabelOne_mem_base hT _ hw'),
      rel_relabel_base_iff hT hw hw']
    exact hab
  · rw [isoOne_low hT hQ hw, isoOne_mid hT hQ hy']
    exact hlow_up hw (isoMid_mem hT hQ hW hy')
  · rw [isoOne_low hT hQ hw, isoOne_up hbu]
    obtain ⟨V, t, σ, ψ, rfl, hx, hs, hψ, -⟩ := upper_data hT hQ hbu
    simp only [lbl_orderedPair, left_orderedPair, right_orderedPair]
    rw [isoUp_orderedPair]
    exact hlow_up hw (hRup hx hs hψ)
  · exfalso
    rw [lhs_base_rel_iff hT hQ hW (hNM hy) (hLow hw'),
      rel_odrOne_tensorProdATwoAOne_iff_of_mem hT hQ2 hy] at hab
    exact not_mem_upper_of_mem_base hT (relabelOne_mem_base hT _ hw') hab.left
  · rw [isoOne_mid hT hQ hy, isoOne_mid hT hQ hy']
    rw [lhs_base_rel_iff hT hQ hW (hNM hy) (hNM hy'),
      rel_odrOne_tensorProdATwoAOne_iff_of_mem hT hQ2 hy, lbl_orderedPair, lbl_orderedPair] at hab
    exact (rel_isoMid_iff hT hQ hW hy hy').mp hab.right
  · rw [isoOne_mid hT hQ hy, isoOne_up hbu]
    obtain ⟨V, t', σ, ψ, rfl, hx, hs, hψ, -⟩ := upper_data hT hQ hbu
    simp only [lbl_orderedPair, left_orderedPair, right_orderedPair]
    rw [isoUp_orderedPair]
    exact rel_isoMid_isoUpOf hT hQ hW hy hx hs hψ
  · exact (not_isUpNd_relabelOne hT hQ (hLow hw') (hupLt hau hab).left).elim
  · exact (not_isUpNd_relabelOne hT hQ (hNM hy') (hupLt hau hab).left).elim
  · obtain ⟨-, hlt⟩ := hupLt hau hab
    rw [isoOne_up hau, isoOne_up hbu]
    obtain ⟨V, t, σ, ψ, rfl, hx, hs, hψ, hxr⟩ := upper_data hT hQ hau
    obtain ⟨V', t', σ', ψ', rfl, hx', hs', hψ', hxr'⟩ := upper_data hT hQ hbu
    simp only [lbl_orderedPair, left_orderedPair, right_orderedPair] at hlt ⊢
    have hxn : !(V, !(t, σ)) ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q) := by
      rw [ndOf_tensorProdTwoTwo]; exact hx
    have hxn' : !(V', !(t', σ')) ∈ ndOf (tensorProdTwoTwo (T ﹫ 2) Q) := by
      rw [ndOf_tensorProdTwoTwo]; exact hx'
    exact rel_isoUp_of_bkLt hT hQ hW hxn (by rw [uc_orderedPair]; exact hψ) hxn' hxr'
      (by rw [uc_orderedPair]; exact hψ') hlt

end IsoOneOrder

section IsoOneDefinable

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ tensorProdTwoTwo (xs 0) (xs 1) = xs 2)
    Set.univ := by
  obtain ⟨G, hG⟩ : ∃ G : ClassFunction M,
      G = fun z : M ↦ tensorProdTwoTwo (left z) (right z) := ⟨_, rfl⟩
  have : G.Definable Set.univ := by
    rw [hG]
    infer_instance
  have h : (fun xs : Fin 3 → M ↦ tensorProdTwoTwo (xs 0) (xs 1) = xs 2) = fun xs ↦
      ∃ z : M, z = !(xs 0, xs 1) ∧ G z = xs 2 := by
    funext xs
    apply propext
    rw [hG]
    simp only [left_orderedPair, right_orderedPair, exists_eq_left]
  rw [h]
  infer_instance

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ tensorProdTwoAOneNds (xs 0) (xs 1) = xs 2)
    Set.univ := by
  obtain ⟨G, hG⟩ : ∃ G : ClassFunction M,
      G = fun z : M ↦ tensorProdTwoAOneNds (left z) (right z) := ⟨_, rfl⟩
  have : G.Definable Set.univ := by
    rw [hG]
    infer_instance
  have h : (fun xs : Fin 3 → M ↦ tensorProdTwoAOneNds (xs 0) (xs 1) = xs 2) = fun xs ↦
      ∃ z : M, z = !(xs 0, xs 1) ∧ G z = xs 2 := by
    funext xs
    apply propext
    rw [hG]
    simp only [left_orderedPair, right_orderedPair, exists_eq_left]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    tensorProdTwoTwo (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tensorProdTwoTwo (xs i) (xs j) = xs k) =
      Multiclass.remap (fun ys : Fin 3 → M ↦ tensorProdTwoTwo (ys 0) (ys 1) = ys 2)
        ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    tensorProdTwoAOneNds (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tensorProdTwoAOneNds (xs i) (xs j) = xs k) =
      Multiclass.remap (fun ys : Fin 3 → M ↦ tensorProdTwoAOneNds (ys 0) (ys 1) = ys 2)
        ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ IsUpNd (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ IsUpNd (xs 0) (xs 1) (xs 2) (xs 3)) = fun xs ↦
      ∃ two P F N : M, two = ((2 : ℕ) : M) ∧ P = xs 0 ﹫ two ∧ tensorProdTwoTwo P (xs 1) = F ∧
        tensorProdTwoAOneNds F (xs 2) = N ∧ xs 3 ∈ N := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, h⟩
    · rintro ⟨two, P, F, N, rfl, rfl, rfl, rfl, h⟩
      exact h
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    IsUpNd (xs i) (xs j) (xs k) (xs l)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsUpNd (xs i) (xs j) (xs k) (xs l)) =
      Multiclass.remap (fun ys : Fin 4 → M ↦ IsUpNd (ys 0) (ys 1) (ys 2) (ys 3))
        ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩


instance : Multiclass.Definable (fun xs : Fin 2 → M ↦ unrel (xs 0) = xs 1) Set.univ := by
  unfold unrel
  infer_instance

instance {n : ℕ} (i j : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ unrel (xs i) = xs j) Set.univ := by
  have h : (fun xs : Fin n → M ↦ unrel (xs i) = xs j) =
      Multiclass.remap (fun ys : Fin 2 → M ↦ unrel (ys 0) = ys 1) ![i, j] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ IsMidNd (xs 0) (xs 1) (xs 2)) Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ IsMidNd (xs 0) (xs 1) (xs 2)) = fun xs ↦
      ∃ two u P R N : M, two = ((2 : ℕ) : M) ∧ unrel (xs 2) = u ∧
        P = xs 0 ﹫ two ∧ R = xs 1 ↾ two ∧ tensorProdTwoAOneNds P R = N ∧ u ∈ N := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, h⟩
    · rintro ⟨two, u, P, R, N, rfl, rfl, rfl, rfl, rfl, h⟩
      exact h
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    IsMidNd (xs i) (xs j) (xs k)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsMidNd (xs i) (xs j) (xs k)) =
      Multiclass.remap (fun ys : Fin 3 → M ↦ IsMidNd (ys 0) (ys 1) (ys 2))
        ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩


instance : Multiclass.Definable (fun xs : Fin 5 → M ↦ isoMid (xs 0) (xs 1) (xs 2) (xs 3) = xs 4)
    Set.univ := by
  have h : (fun xs : Fin 5 → M ↦ isoMid (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) = fun xs ↦
      ∃ A z e : M, A = aoc (uc (xs 2)) ∧ z = ∅ ∧ tauEmb (xs 0) (xs 1) (xs 1) A z (xs 3) = e ∧
        xs 4 = !(dctUZero, !(xs 2, e)) := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, _, rfl, rfl, rfl, h.symm⟩
    · rintro ⟨A, z, e, rfl, rfl, rfl, h⟩
      exact h.symm
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    isoMid (xs i) (xs j) (xs k) (xs l) = xs m) Set.univ := by
  have h : (fun xs : Fin n → M ↦ isoMid (xs i) (xs j) (xs k) (xs l) = xs m) =
      Multiclass.remap (fun ys : Fin 5 → M ↦ isoMid (ys 0) (ys 1) (ys 2) (ys 3) = ys 4)
        ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

def IsoOneA (T Q W a r : M) : Prop :=
  IsUpNd T Q W a ∧ ∃ x ψ : M, x = left (lbl a) ∧ ψ = right (lbl a) ∧ isoUp Q W x ψ = r

def IsoOneB (T Q W a r : M) : Prop :=
  ¬ IsUpNd T Q W a ∧ IsMidNd T Q a ∧ ∃ u t f : M, unrel a = u ∧ t = left (lbl u) ∧
    f = right (lbl u) ∧ isoMid Q W t f = r

def IsoOneC (T Q W a r : M) : Prop := ¬ IsUpNd T Q W a ∧ ¬ IsMidNd T Q a ∧ unrel a = r

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ IsoOneA (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)) Set.univ := by
  unfold IsoOneA
  infer_instance

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ IsoOneB (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)) Set.univ := by
  unfold IsoOneB
  infer_instance

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ IsoOneC (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)) Set.univ := by
  unfold IsoOneC
  infer_instance

/-- The graph of `isoOne` -/
def IsoOneRel (T Q W a r : M) : Prop := IsoOneA T Q W a r ∨ IsoOneB T Q W a r ∨ IsoOneC T Q W a r

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ IsoOneRel (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)) Set.univ := by
  unfold IsoOneRel
  infer_instance

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    IsoOneRel (xs i) (xs j) (xs k) (xs l) (xs m)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsoOneRel (xs i) (xs j) (xs k) (xs l) (xs m)) =
      Multiclass.remap (fun ys : Fin 5 → M ↦ IsoOneRel (ys 0) (ys 1) (ys 2) (ys 3) (ys 4))
        ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

theorem isoOne_eq_iff (T Q W a r : M) : isoOne T Q W a = r ↔ IsoOneRel T Q W a r := by
  unfold IsoOneRel IsoOneA IsoOneB IsoOneC isoOne
  by_cases h1 : IsUpNd T Q W a
  · rw [if_pos h1]
    constructor
    · intro h
      exact .inl ⟨h1, _, _, rfl, rfl, h⟩
    · rintro (⟨-, x, ψ, rfl, rfl, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · exact h
      · exact (h h1).elim
      · exact (h h1).elim
  · by_cases h2 : IsMidNd T Q a
    · rw [if_neg h1, if_pos h2]
      constructor
      · intro h
        exact .inr (.inl ⟨h1, h2, _, _, _, rfl, rfl, rfl, h⟩)
      · rintro (⟨h, -⟩ | ⟨-, -, u, t, f, rfl, rfl, rfl, h⟩ | ⟨-, h, -⟩)
        · exact (h1 h).elim
        · exact h
        · exact (h h2).elim
    · rw [if_neg h1, if_neg h2]
      constructor
      · intro h
        exact .inr (.inr ⟨h1, h2, h⟩)
      · rintro (⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩)
        · exact (h1 h).elim
        · exact (h2 h).elim
        · exact h

instance (T Q W : M) : ClassFunction.Definable (fun a ↦ isoOne T Q W a) Set.univ :=
  ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ T' Q' W' : M, T' = T ∧ Q' = Q ∧
    W' = W ∧ IsoOneRel T' Q' W' (xs 0) (xs 1)) fun a r ↦ by
      rw [isoOne_eq_iff]
      constructor
      · rintro ⟨T', Q', W', rfl, rfl, rfl, h⟩
        exact h
      · intro h
        exact ⟨_, _, _, rfl, rfl, rfl, h⟩

end IsoOneDefinable

end FirstOrder.Language.MemStructure
