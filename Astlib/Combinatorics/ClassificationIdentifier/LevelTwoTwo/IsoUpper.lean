/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.LeastChild
/-!
# The canonical map on upper nodes

The image `isoUpOf Q W V t σ ψ = (t, ρ ∘ Φ_ψ ∘ σ)` of an upper node `((V, (t, σ)), ψ)` of
`(T ⊗ Q) ⊗ W`, pushing nodes of `(Q ⊗ X)(1)` along `ψ`, and the comparison of the images of a
child and its parent and of siblings.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M]

section IsoBasic

/-! ### Basic facts for the isomorphism -/

variable {Q X A B : M}

omit [ModelsZF M] in
/-- The relabeling of the nodes of a tree in `otci_1` does not depend on the `aotci_0` factor -/
theorem relabelOne_congr (Q Q' w : M) : relabelOne Q w = relabelOne Q' w := rfl

/-- The inverse `(U, (l, Y)) ↦ (U, l)` of the relabeling -/
noncomputable def unrel (y : M) : M := !(uc y, left (lbl y))

theorem unrel_relabelOne {w : M} (hw : IsOrderedPair w) (Q : M) :
    unrel (relabelOne Q w) = w := by
  obtain ⟨u, l, rfl⟩ := hw
  simp only [unrel, relabelOne, uc_orderedPair, lbl_orderedPair, left_orderedPair]

/-- The order of `(Q ⊗ X)(1)`: the base, then `Q(2) ⊗ X` -/
theorem rel_odrOne_tensorProdATwoAOne_iff (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hX : X ∈ aotci ((1 : ℕ) : M)) {a b : M} :
    a [odrOne (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M))] b ↔
      a [odrOne (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M))] b ∨
      (a ∈ tensorProdTwoAOneNds (Q ﹫ 2) X ∧ b ∈ tensorProdTwoAOneNds (Q ﹫ 2) X ∧
        TensorProdTwoAOneLt (Q ﹫ 2) X (lbl a) (lbl b)) ∨
      (a ∈ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ∧
        b ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hB1 := val_mem_otci_of_mem_aotci (tensorProdATwoAOneBase_mem_aotci hQ X) (mem_succ_self _)
  have hC := tensorProdTwoAOne_mem_otci hQ2 hX
  obtain ⟨-, hsB, -⟩ := rtlosOf_of_mem_otci_one hB1
  obtain ⟨hRC, hsC, -⟩ := rtlosOf_of_mem_otci_one hC
  have hY1 := val_mem_otci_of_mem_aotci (tensorProdATwoAOne_mem_aotci hQ hX) (mem_succ_self _)
  have hRY := (rtlosOf_of_mem_otci_one hY1).left
  have hRBo : IsStrictLinearOrder (odrOne (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)))
      (ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M))) := (rtlosOf_of_mem_otci_one hB1).left
  have hRCo : IsStrictLinearOrder (odrOne (tensorProdTwoAOne (Q ﹫ 2) X))
      (ndOf (tensorProdTwoAOne (Q ﹫ 2) X)) := hRC
  by_cases hne : losSet (losConcat (rtlosOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ﹫ trvAZero)
      (rtlosOf (tensorProdTwoAOne (Q ﹫ 2) X) ﹫ trvAZero)) = ∅
  · rw [losConcat, losSet_orderedPair, hsB, hsC] at hne
    have hBe (z : M) (hz : z ∈ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M))) : False := by
      have h' : z ∈ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ∪
          ndOf (tensorProdTwoAOne (Q ﹫ 2) X) := by rw [mem_union_iff]; exact .inl hz
      rw [hne] at h'
      exact notin_empty _ h'
    have hCe (z : M) (hz : z ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) : False := by
      have h' : z ∈ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ∪
          ndOf (tensorProdTwoAOne (Q ﹫ 2) X) := by
        rw [ndOf_tensorProdTwoAOne, mem_union_iff]
        exact .inr hz
      rw [hne] at h'
      exact notin_empty _ h'
    constructor
    · intro h
      rcases (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX).mp (hRY.mem_left h) with h' | h'
      · exact (hBe _ h').elim
      · exact (hCe _ h').elim
    · rintro (h | h | h)
      · exact (hBe _ (hRBo.mem_left h)).elim
      · exact (hCe _ h.left).elim
      · exact (hBe _ h.left).elim
  rw [tensorProdATwoAOne_val_one_eq hQ, odrOne_rtLosSLOT hne, losConcat, losOdr_orderedPair,
    rel_concat_iff, hsB, hsC, ndOf_tensorProdTwoAOne]
  change a [odrOne (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M))] b ∨
    a [odrOne (tensorProdTwoAOne (Q ﹫ 2) X)] b ∨ _ ↔ _
  constructor
  · rintro (h | h | h)
    · exact .inl h
    · have ha : a ∈ tensorProdTwoAOneNds (Q ﹫ 2) X := by
        rw [← ndOf_tensorProdTwoAOne]; exact hRCo.mem_left h
      rw [rel_odrOne_tensorProdTwoAOne_iff ha] at h
      exact .inr (.inl ⟨h.left.left, h.left.right, h.right⟩)
    · exact .inr (.inr h)
  · rintro (h | ⟨ha, hb, h⟩ | h)
    · exact .inl h
    · exact .inr (.inl ((rel_odrOne_tensorProdTwoAOne_iff ha).mpr ⟨⟨ha, hb⟩, h⟩))
    · exact .inr (.inr h)

end IsoBasic

section EmbMk

/-! ### Building level-`1` embeddings -/

variable {A B φ : M}

/-- The level-`1` embedding with level-`0` part the unique isomorphism and level-`1` part `φ` -/
noncomputable def embMk (A B φ : M) : M := cc (cc ∅ (otciSngIso (A ﹫ ∅) (B ﹫ ∅))) φ

theorem embMk_val_one (A B φ : M) : embMk A B φ ﹫ ((1 : ℕ) : M) = φ := by
  have hσ₀ : IsFunction (cc ∅ (otciSngIso (A ﹫ ∅) (B ﹫ ∅)) : M) := isFunction_empty.cc _
  have hσ₀dom : dom (cc ∅ (otciSngIso (A ﹫ ∅) (B ﹫ ∅)) : M) = ((1 : ℕ) : M) := by
    rw [dom_cc, dom_empty, natCast_succ, natCast_zero]
  have h := cc_val_self hσ₀ φ
  rwa [hσ₀dom] at h

theorem embMk_val_zero (A B φ : M) : embMk A B φ ﹫ ∅ = otciSngIso (A ﹫ ∅) (B ﹫ ∅) := by
  have hσ₀ : IsFunction (cc ∅ (otciSngIso (A ﹫ ∅) (B ﹫ ∅)) : M) := isFunction_empty.cc _
  have hσ₀dom : dom (cc ∅ (otciSngIso (A ﹫ ∅) (B ﹫ ∅)) : M) = ((1 : ℕ) : M) := by
    rw [dom_cc, dom_empty, natCast_succ, natCast_zero]
  rw [embMk, cc_val_of_mem hσ₀ _ (by rw [hσ₀dom]; exact empty_mem_natCast_one)]
  have h := cc_val_self (isFunction_empty (M := M)) (otciSngIso (A ﹫ ∅) (B ﹫ ∅))
  rwa [dom_empty] at h

/-- An order embedding of the level-`1` trees gives an embedding of the arrays -/
theorem embMk_mem_aotciEmbSet (hA : A ∈ aotci ((1 : ℕ) : M)) (hB : B ∈ aotci ((1 : ℕ) : M))
    (hφ : φ !: ndOf (A ﹫ ((1 : ℕ) : M)) ↪ ndOf (B ﹫ ((1 : ℕ) : M)))
    (hodr : ∀ a ∈ ndOf (A ﹫ ((1 : ℕ) : M)), ∀ b ∈ ndOf (A ﹫ ((1 : ℕ) : M)),
      a [odrOne (A ﹫ ((1 : ℕ) : M))] b →
        (φ ﹫ a) [odrOne (B ﹫ ((1 : ℕ) : M))] (φ ﹫ b)) :
    embMk A B φ ∈ aotciEmbSet ((1 : ℕ) : M) A B := by
  obtain ⟨hAf, hAdom, -⟩ := mem_aotci_iff.mp hA
  obtain ⟨hBf, hBdom, -⟩ := mem_aotci_iff.mp hB
  have h0 : (∅ : M) ∈ succ ((1 : ℕ) : M) := mem_succ_of_mem empty_mem_natCast_one
  have h1 : ((1 : ℕ) : M) ∈ succ ((1 : ℕ) : M) := mem_succ_self _
  have hσ₀ : IsFunction (cc ∅ (otciSngIso (A ﹫ ∅) (B ﹫ ∅)) : M) := isFunction_empty.cc _
  have hσ₀dom : dom (cc ∅ (otciSngIso (A ﹫ ∅) (B ﹫ ∅)) : M) = ((1 : ℕ) : M) := by
    rw [dom_cc, dom_empty, natCast_succ, natCast_zero]
  refine mem_aotciEmbSet_of_isAotciEmbedding hAf hAdom hBf hBdom
    ⟨hσ₀.cc _, by rw [embMk, dom_cc, hσ₀dom], fun {i} hi ↦ ?_⟩
  rcases mem_succ_one_cases hi with rfl | rfl
  · rw [embMk_val_zero]
    exact (isOtciIsomorphism_otciSngIso_of_mem_otci_empty (val_mem_otci_of_mem_aotci hA h0)
      (val_mem_otci_of_mem_aotci hB h0)).isOtciEmbedding
  · rw [embMk_val_one]
    exact (isOtciEmbedding_iff_of_mem_otci_one (val_mem_otci_of_mem_aotci hA h1)
      (val_mem_otci_of_mem_aotci hB h1)).mpr ⟨hφ, hodr⟩

end EmbMk

section Push

/-! ### Pushing an embedding along `ψ` -/

theorem isSetRestrictedTo_pushOne (ψ g : M) :
    IsSetRestrictedTo (fun u ↦ (ψ ﹫ ((1 : ℕ) : M)) ﹫ unrel ((g ﹫ ((1 : ℕ) : M)) ﹫ u))
      (dom (g ﹫ ((1 : ℕ) : M))) := by
  have : ClassFunction.Definable
      (fun u ↦ (ψ ﹫ ((1 : ℕ) : M)) ﹫ unrel ((g ﹫ ((1 : ℕ) : M)) ﹫ u)) Set.univ :=
    ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ ψ' g' : M,
      ψ' = ψ ﹫ ((1 : ℕ) : M) ∧ g' = g ﹫ ((1 : ℕ) : M) ∧
        ∃ a, a = g' ﹫ xs 0 ∧ ψ' ﹫ !(uc a, left (lbl a)) = xs 1) fun u w ↦ by
      simp only [unrel]
      constructor
      · rintro ⟨ψ', g', rfl, rfl, a, rfl, h⟩
        exact h
      · intro h
        exact ⟨_, _, rfl, rfl, _, rfl, h⟩
  exact isSetRestrictedTo_of_definable _

end Push

section EmbMk2

variable {A B φ : M}

/-- An order-preserving function on the level-`1` nodes gives an embedding of the arrays -/
theorem embMk_mem_aotciEmbSet' (hA : A ∈ aotci ((1 : ℕ) : M)) (hB : B ∈ aotci ((1 : ℕ) : M))
    (hφ : IsFunction φ) (hdom : dom φ = ndOf (A ﹫ ((1 : ℕ) : M)))
    (hval : ∀ a ∈ ndOf (A ﹫ ((1 : ℕ) : M)), φ ﹫ a ∈ ndOf (B ﹫ ((1 : ℕ) : M)))
    (hodr : ∀ a ∈ ndOf (A ﹫ ((1 : ℕ) : M)), ∀ b ∈ ndOf (A ﹫ ((1 : ℕ) : M)),
      a [odrOne (A ﹫ ((1 : ℕ) : M))] b →
        (φ ﹫ a) [odrOne (B ﹫ ((1 : ℕ) : M))] (φ ﹫ b)) :
    embMk A B φ ∈ aotciEmbSet ((1 : ℕ) : M) A B := by
  have h1 : ((1 : ℕ) : M) ∈ succ ((1 : ℕ) : M) := mem_succ_self _
  have hRA := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci hA h1)).left
  have hRB := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci hB h1)).left
  refine embMk_mem_aotciEmbSet hA hB ⟨isFunctionFromTo_of_val hφ hdom hval, fun a b ha hb h ↦ ?_⟩
    hodr
  rcases hRA.isTrichotomousOn a ha b hb with h' | h' | h'
  · exact (hRB.ne (hodr a ha b hb h') h).elim
  · exact h'
  · exact (hRB.ne (hodr b hb a ha h') h.symm).elim

end EmbMk2

section EmbFacts

variable {A B f : M}

/-- The level-`1` part of an embedding maps nodes to nodes -/
theorem emb_val_mem (hA : A ∈ aotci ((1 : ℕ) : M)) (hB : B ∈ aotci ((1 : ℕ) : M))
    (hf : f ∈ aotciEmbSet ((1 : ℕ) : M) A B) {a : M} (ha : a ∈ ndOf (A ﹫ ((1 : ℕ) : M))) :
    (f ﹫ ((1 : ℕ) : M)) ﹫ a ∈ ndOf (B ﹫ ((1 : ℕ) : M)) := by
  have h1 : ((1 : ℕ) : M) ∈ succ ((1 : ℕ) : M) := mem_succ_self _
  obtain ⟨hinj, -⟩ := (isOtciEmbedding_iff_of_mem_otci_one (val_mem_otci_of_mem_aotci hA h1)
    (val_mem_otci_of_mem_aotci hB h1)).mp ((mem_aotciEmbSet_iff.mp hf).right.isOtciEmbedding h1)
  exact hinj.isFunctionFromTo.val_mem ha

/-- The level-`1` part of an embedding preserves the order -/
theorem emb_odr (hA : A ∈ aotci ((1 : ℕ) : M)) (hB : B ∈ aotci ((1 : ℕ) : M))
    (hf : f ∈ aotciEmbSet ((1 : ℕ) : M) A B) {a b : M} (ha : a ∈ ndOf (A ﹫ ((1 : ℕ) : M)))
    (hb : b ∈ ndOf (A ﹫ ((1 : ℕ) : M))) (hab : a [odrOne (A ﹫ ((1 : ℕ) : M))] b) :
    ((f ﹫ ((1 : ℕ) : M)) ﹫ a) [odrOne (B ﹫ ((1 : ℕ) : M))] ((f ﹫ ((1 : ℕ) : M)) ﹫ b) := by
  have h1 : ((1 : ℕ) : M) ∈ succ ((1 : ℕ) : M) := mem_succ_self _
  obtain ⟨-, hodr⟩ := (isOtciEmbedding_iff_of_mem_otci_one (val_mem_otci_of_mem_aotci hA h1)
    (val_mem_otci_of_mem_aotci hB h1)).mp ((mem_aotciEmbSet_iff.mp hf).right.isOtciEmbedding h1)
  exact hodr a ha b hb hab

end EmbFacts

section PushOne

variable {X W A g ψ : M}

/-- The level-`1` part `u ↦ ψ(g(u))` of the push of `g : A → X ⊗ Z` along `ψ : X → W ⊗ Z`,
reading the values of `g` in `X` -/
noncomputable def pushOne (ψ g : M) : M :=
  (fun u ↦ (ψ ﹫ ((1 : ℕ) : M)) ﹫ unrel ((g ﹫ ((1 : ℕ) : M)) ﹫ u)) ↾₀ dom (g ﹫ ((1 : ℕ) : M))

theorem pushOne_spec (ψ g : M) : IsFunction (pushOne ψ g) ∧
    dom (pushOne ψ g) = dom (g ﹫ ((1 : ℕ) : M)) ∧ ∀ u ∈ dom (g ﹫ ((1 : ℕ) : M)),
      pushOne ψ g ﹫ u = (ψ ﹫ ((1 : ℕ) : M)) ﹫ unrel ((g ﹫ ((1 : ℕ) : M)) ﹫ u) :=
  ⟨isFunction_toSetRestrictedTo (isSetRestrictedTo_pushOne ψ g),
    dom_toSetRestrictedTo (isSetRestrictedTo_pushOne ψ g),
    fun _ hu ↦ val_toSetRestrictedTo (isSetRestrictedTo_pushOne ψ g) hu⟩

/-- The value of the push at a node `u` with `g(u) = w ⊗ Z` -/
theorem pushOne_val_of_eq (hX : X ∈ aotci ((1 : ℕ) : M))
    (hg : g ∈ aotciEmbSet ((1 : ℕ) : M) A (tensorProdTwoAOneTgt X)) {u w : M}
    (hu : u ∈ ndOf (A ﹫ ((1 : ℕ) : M))) (hw : w ∈ ndOf (X ﹫ ((1 : ℕ) : M)))
    (hgu : (g ﹫ ((1 : ℕ) : M)) ﹫ u = relabelOne trvAZero w) :
    pushOne ψ g ﹫ u = (ψ ﹫ ((1 : ℕ) : M)) ﹫ w := by
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  obtain ⟨hgi, hgd⟩ := embChg_val_one_isFunction hg
  rw [(pushOne_spec ψ g).right.right u (by rw [hgd]; exact hu), hgu,
    unrel_relabelOne ((isSLOT_of_mem_otci hX1).isOrderedPair hw)]

/-- The push of an embedding is an embedding -/
theorem embMk_pushOne_mem (hX : X ∈ aotci ((1 : ℕ) : M)) (hW : W ∈ aotci ((1 : ℕ) : M))
    (hA : A ∈ aotci ((1 : ℕ) : M))
    (hg : g ∈ aotciEmbSet ((1 : ℕ) : M) A (tensorProdTwoAOneTgt X))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) X (tensorProdTwoAOneTgt W)) :
    embMk A (tensorProdTwoAOneTgt W) (pushOne ψ g) ∈
      aotciEmbSet ((1 : ℕ) : M) A (tensorProdTwoAOneTgt W) := by
  have hT := tensorProdTwoAOneTgt_mem hW
  have hTX := tensorProdTwoAOneTgt_mem hX
  obtain ⟨-, hgd⟩ := embChg_val_one_isFunction hg
  refine embMk_mem_aotciEmbSet' hA hT (pushOne_spec ψ g).left
    (by rw [(pushOne_spec ψ g).right.left, hgd]) (fun a ha ↦ ?_) (fun a ha b hb hab ↦ ?_)
  · obtain ⟨w, hw, hgw⟩ := exists_relabelOne_eq hX hg ha
    rw [pushOne_val_of_eq hX hg ha hw hgw]
    exact emb_val_mem hX hT hψ hw
  · obtain ⟨w, hw, hgw⟩ := exists_relabelOne_eq hX hg ha
    obtain ⟨w', hw', hgw'⟩ := exists_relabelOne_eq hX hg hb
    rw [pushOne_val_of_eq hX hg ha hw hgw, pushOne_val_of_eq hX hg hb hw' hgw']
    have h := emb_odr hA hTX hg ha hb hab
    rw [hgw, hgw', rel_tgt_relabel_iff hX hw hw'] at h
    exact emb_odr hX hT hψ hw hw' h

end PushOne

section PushNd

/-! ### Pushing a node of `(Q ⊗ X)(1)` along `ψ : X → W ⊗ Z` -/

variable {Q X W ψ : M}

/-- The level-`1` embedding `ψ ∘ g` for `g : A → X ⊗ Z` and `ψ : X → W ⊗ Z` -/
noncomputable def pushEmb (W A ψ g : M) : M := embMk A (tensorProdTwoAOneTgt W) (pushOne ψ g)

/-- The image of a node `z` of `(Q ⊗ X)(1)` in `(Q ⊗ W)(1)`: `(q, ψ ∘ g)` for `z = (q, g)` from
`Q(2)`, and `z` itself for `z` from the base -/
noncomputable def pushNd (Q X W ψ z : M) : M :=
  if IsTpTwo Q X z then !(dctUZero, !(nodeQ z, pushEmb W (aoc (uc (nodeQ z))) ψ (nodeH z)))
  else z

theorem pushNd_of_mem {q g : M} (hz : !(dctUZero, !(q, g)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) :
    pushNd Q X W ψ !(dctUZero, !(q, g)) =
      !(dctUZero, !(q, pushEmb W (aoc (uc q)) ψ g)) := by
  rw [pushNd, if_pos (show IsTpTwo Q X _ from hz), nodeQ_orderedPair, nodeH_orderedPair]

omit [ModelsZF M] in
theorem pushNd_of_not {z : M} (hz : ¬ IsTpTwo Q X z) : pushNd Q X W ψ z = z := by
  rw [pushNd, if_neg hz]

omit [ModelsZF M] in
/-- The base of `(Q ⊗ X)(1)` does not depend on `X` -/
theorem tensorProdOneAZero_congr (P Y Y' : M) : tensorProdOneAZero P Y = tensorProdOneAZero P Y' :=
  rfl

theorem base_val_one_congr (Q X X' : M) :
    tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M) = tensorProdATwoAOneBase Q X' ﹫ ((1 : ℕ) : M) := by
  rw [tensorProdATwoAOneBase_val_one, tensorProdATwoAOneBase_val_one, tensorProdOneAZero_congr]

end PushNd

section EmbFacts2

variable {A B f : M}

/-- The level-`1` part of an embedding is injective -/
theorem emb_inj (hA : A ∈ aotci ((1 : ℕ) : M)) (hB : B ∈ aotci ((1 : ℕ) : M))
    (hf : f ∈ aotciEmbSet ((1 : ℕ) : M) A B) {a b : M} (ha : a ∈ ndOf (A ﹫ ((1 : ℕ) : M)))
    (hb : b ∈ ndOf (A ﹫ ((1 : ℕ) : M)))
    (h : (f ﹫ ((1 : ℕ) : M)) ﹫ a = (f ﹫ ((1 : ℕ) : M)) ﹫ b) : a = b := by
  have h1 : ((1 : ℕ) : M) ∈ succ ((1 : ℕ) : M) := mem_succ_self _
  obtain ⟨hinj, -⟩ := (isOtciEmbedding_iff_of_mem_otci_one (val_mem_otci_of_mem_aotci hA h1)
    (val_mem_otci_of_mem_aotci hB h1)).mp ((mem_aotciEmbSet_iff.mp hf).right.isOtciEmbedding h1)
  exact hinj.right ha hb h

/-- The level-`1` part of an embedding preserves and reflects the order -/
theorem emb_odr_iff (hA : A ∈ aotci ((1 : ℕ) : M)) (hB : B ∈ aotci ((1 : ℕ) : M))
    (hf : f ∈ aotciEmbSet ((1 : ℕ) : M) A B) {a b : M} (ha : a ∈ ndOf (A ﹫ ((1 : ℕ) : M)))
    (hb : b ∈ ndOf (A ﹫ ((1 : ℕ) : M))) :
    a [odrOne (A ﹫ ((1 : ℕ) : M))] b ↔
      ((f ﹫ ((1 : ℕ) : M)) ﹫ a) [odrOne (B ﹫ ((1 : ℕ) : M))] ((f ﹫ ((1 : ℕ) : M)) ﹫ b) := by
  have h1 : ((1 : ℕ) : M) ∈ succ ((1 : ℕ) : M) := mem_succ_self _
  have hRA := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci hA h1)).left
  have hRB := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci hB h1)).left
  refine ⟨emb_odr hA hB hf ha hb, fun h ↦ ?_⟩
  rcases hRA.isTrichotomousOn a ha b hb with h' | rfl | h'
  · exact h'
  · exact (hRB.irrefl _ h).elim
  · exact (hRB.asymm h (emb_odr hA hB hf hb ha h')).elim

end EmbFacts2

section PushNdSpec

variable {Q X W ψ : M}

/-- The push of a node from `Q(2)` is a node from `Q(2)` -/
theorem pushNd_mem_of_mem (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hX : X ∈ aotci ((1 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) X (tensorProdTwoAOneTgt W))
    {z : M} (hz : z ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) :
    pushNd Q X W ψ z ∈ tensorProdTwoAOneNds (Q ﹫ 2) W := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  obtain ⟨q, hq, hqr, g, hg, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp hz
  rw [pushNd_of_mem hz]
  exact mem_tensorProdTwoAOneNds_iff'.mpr ⟨q, hq, hqr, _, embMk_pushOne_mem hX hW
    (aoc_mem_aotci_of_mem_stduoci_one (uc_mem_stduoci_of_mem_otci_two hQ2 hq)) hg hψ, rfl⟩

/-- The push preserves the order of nodes from `Q(2)` -/
theorem tensorProdTwoAOneLt_pushNd_iff (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hX : X ∈ aotci ((1 : ℕ) : M)) (hW : W ∈ aotci ((1 : ℕ) : M))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) X (tensorProdTwoAOneTgt W)) {z z' : M}
    (hz : z ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) (hz' : z' ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) :
    TensorProdTwoAOneLt (Q ﹫ 2) X (lbl z) (lbl z') ↔
      TensorProdTwoAOneLt (Q ﹫ 2) W (lbl (pushNd Q X W ψ z)) (lbl (pushNd Q X W ψ z')) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hTX := tensorProdTwoAOneTgt_mem hX
  have hTW := tensorProdTwoAOneTgt_mem hW
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  have hTX1 := val_mem_otci_of_mem_aotci hTX (mem_succ_self _)
  obtain ⟨q, hq, -, g, hg, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp hz
  obtain ⟨q', hq', -, g', hg', rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp hz'
  rw [pushNd_of_mem hz, pushNd_of_mem hz', lbl_orderedPair, lbl_orderedPair, lbl_orderedPair,
    lbl_orderedPair]
  -- the map of the coordinates
  let κ : M → M := fun c ↦ !((ψ ﹫ ((1 : ℕ) : M)) ﹫ unrel (left c), right c)
  have hdep (p : M) (hp : p ∈ ndOf (Q ﹫ 2)) : Ordinal (depOf (Q ﹫ 2) p) :=
    ordinal_of_mem ordinal_omega ((otciCond_two hQ2).left.isTreeStructure.dep_mem_omega hp)
  have hsv {p h : M} (hp : p ∈ ndOf (Q ﹫ 2))
      (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) (tensorProdTwoAOneTgt X)) :
      ∀ i ∈ dom (tensorProdTwoAOneSeq (Q ﹫ 2) !(p, h)),
        tensorProdTwoAOneSeq (Q ﹫ 2) !(p, pushEmb W (aoc (uc p)) ψ h) ﹫ i =
          κ (tensorProdTwoAOneSeq (Q ﹫ 2) !(p, h) ﹫ i) := by
    intro i hi
    rw [tensorProdTwoAOneSeq_dom] at hi
    have hUp := uc_mem_stduoci_of_mem_otci_two hQ2 hp
    have hip : i ∈ dom (sig (uc p)) := by rw [dom_sig_uc_eq_depOf hQ2 hp]; exact hi
    have hu := (siglvl_eq_one hUp hip).right
    obtain ⟨-, hhd⟩ := embChg_val_one_isFunction hh
    rw [tensorProdTwoAOneSeq_val hQ2 hp hi, tensorProdTwoAOneSeq_val hQ2 hp hi, pushEmb,
      embMk_val_one, (pushOne_spec ψ h).right.right _ (by rw [hhd]; exact hu)]
    simp only [κ, left_orderedPair, right_orderedPair]
  have hsC {p h : M} (hp : p ∈ ndOf (Q ﹫ 2))
      (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) (tensorProdTwoAOneTgt X)) :
      ∀ i ∈ dom (tensorProdTwoAOneSeq (Q ﹫ 2) !(p, h)), tensorProdTwoAOneSeq (Q ﹫ 2) !(p, h) ﹫ i ∈
        ndOf (tensorProdTwoAOneTgt X ﹫ ((1 : ℕ) : M)) ×ˢ ndOf (Q ﹫ 2) := by
    intro i hi
    rw [tensorProdTwoAOneSeq_dom] at hi
    exact tensorProdTwoAOneSeq_val_mem hQ2 hp hh hi
  have hrel (c : M) (hc : c ∈ ndOf (tensorProdTwoAOneTgt X ﹫ ((1 : ℕ) : M)) ×ˢ ndOf (Q ﹫ 2)) :
      ∃ w ∈ ndOf (X ﹫ ((1 : ℕ) : M)), ∃ n ∈ ndOf (Q ﹫ 2), c = !(relabelOne trvAZero w, n) ∧
        κ c = !((ψ ﹫ ((1 : ℕ) : M)) ﹫ w, n) := by
    rw [mem_sprod_iff] at hc
    obtain ⟨z, hz, n, hn, rfl⟩ := hc
    rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hX1] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨w, hw, n, hn, rfl, ?_⟩
    simp only [κ, left_orderedPair, right_orderedPair,
      unrel_relabelOne ((isSLOT_of_mem_otci hX1).isOrderedPair hw)]
  unfold TensorProdTwoAOneLt tensorProdTwoAOneCoordOdr
  refine bkLt_iff_of_map κ (isFunction_tensorProdTwoAOneSeq _ _)
    (isFunction_tensorProdTwoAOneSeq _ _) (isFunction_tensorProdTwoAOneSeq _ _)
    (isFunction_tensorProdTwoAOneSeq _ _) (by rw [tensorProdTwoAOneSeq_dom,
      tensorProdTwoAOneSeq_dom]) (by rw [tensorProdTwoAOneSeq_dom, tensorProdTwoAOneSeq_dom])
    (hsv hq hg) (hsv hq' hg') (hsC hq hg) (hsC hq' hg') (fun c hc c' hc' h ↦ ?_)
    (fun c hc c' hc' ↦ ?_) (by rw [tensorProdTwoAOneSeq_dom]; exact hdep q hq)
    (by rw [tensorProdTwoAOneSeq_dom]; exact hdep q' hq')
  · obtain ⟨w, hw, n, hn, rfl, hκ⟩ := hrel c hc
    obtain ⟨w', hw', n', hn', rfl, hκ'⟩ := hrel c' hc'
    rw [hκ, hκ', orderedPair_eq_orderedPair_iff] at h
    rw [emb_inj hX hTW hψ hw hw' h.left, h.right]
  · obtain ⟨w, hw, n, hn, rfl, hκ⟩ := hrel c hc
    obtain ⟨w', hw', n', hn', rfl, hκ'⟩ := hrel c' hc'
    have e1 : (relabelOne trvAZero w)
        [losOdr (rtlosOf (tensorProdTwoAOneTgt X ﹫ ((1 : ℕ) : M)) ﹫ trvAZero)]
        (relabelOne trvAZero w') ↔ ((ψ ﹫ ((1 : ℕ) : M)) ﹫ w)
          [losOdr (rtlosOf (tensorProdTwoAOneTgt W ﹫ ((1 : ℕ) : M)) ﹫ trvAZero)]
          ((ψ ﹫ ((1 : ℕ) : M)) ﹫ w') :=
      (rel_tgt_relabel_iff hX hw hw').trans (emb_odr_iff hX hTW hψ hw hw')
    have e2 : relabelOne trvAZero w = relabelOne trvAZero w' ↔
        (ψ ﹫ ((1 : ℕ) : M)) ﹫ w = (ψ ﹫ ((1 : ℕ) : M)) ﹫ w' :=
      ⟨fun h ↦ by rw [relabelOne_injective hX1 hw hw' h],
        fun h ↦ by rw [emb_inj hX hTW hψ hw hw' h]⟩
    have m1 := emb_val_mem hX hTW hψ hw
    have m2 := emb_val_mem hX hTW hψ hw'
    rw [pair_mem_sprod_iff] at hc hc'
    rw [hκ, hκ', rel_lexProd_iff, rel_lexProd_iff, e1, e2]
    exact ⟨fun h ↦ ⟨⟨m1, h.left.right⟩, ⟨m2, h.right.left.right⟩, h.right.right⟩,
      fun h ↦ ⟨⟨hc.left, h.left.right⟩, ⟨hc'.left, h.right.left.right⟩, h.right.right⟩⟩

end PushNdSpec

section PushNdFull

variable {Q X W ψ : M}

/-- The push maps the nodes of `(Q ⊗ X)(1)` to those of `(Q ⊗ W)(1)` -/
theorem pushNd_mem (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hX : X ∈ aotci ((1 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) X (tensorProdTwoAOneTgt W))
    {z : M} (hz : z ∈ ndOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M))) :
    pushNd Q X W ψ z ∈ ndOf (tensorProdATwoAOne Q W ﹫ ((1 : ℕ) : M)) := by
  rw [mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX] at hz
  rw [mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hW]
  rcases hz with hz | hz
  · rw [pushNd_of_not (not_isTpTwo_of_mem_base hQ hz), ← base_val_one_congr]
    exact .inl hz
  · exact .inr (pushNd_mem_of_mem hQ hX hW hψ hz)

/-- The push preserves and reflects the order of `(Q ⊗ X)(1)` -/
theorem pushNd_odr_iff (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hX : X ∈ aotci ((1 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) X (tensorProdTwoAOneTgt W))
    {z z' : M} (hz : z ∈ ndOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M)))
    (hz' : z' ∈ ndOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M))) :
    z [odrOne (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M))] z' ↔
      (pushNd Q X W ψ z) [odrOne (tensorProdATwoAOne Q W ﹫ ((1 : ℕ) : M))] (pushNd Q X W ψ z') := by
  have hBX := base_val_one_congr Q X W
  rw [mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX] at hz hz'
  have hdisj (a : M) (ha : a ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M)))
      (ha' : a ∈ tensorProdTwoAOneNds (Q ﹫ 2) W) : False := by
    have h' : a ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M)) ∩
        ndOf (tensorProdTwoAOne (Q ﹫ (2 : M)) W) := by
      rw [mem_inter_iff, ndOf_tensorProdTwoAOne]
      exact ⟨ha, ha'⟩
    rw [ndOf_base_inter_ndOf_tensorProdTwoAOne hQ W] at h'
    exact notin_empty _ h'
  have hdisjX (a : M) (ha : a ∈ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)))
      (ha' : a ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) : False := by
    have h' : a ∈ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ∩
        ndOf (tensorProdTwoAOne (Q ﹫ (2 : M)) X) := by
      rw [mem_inter_iff, ndOf_tensorProdTwoAOne]
      exact ⟨ha, ha'⟩
    rw [ndOf_base_inter_ndOf_tensorProdTwoAOne hQ X] at h'
    exact notin_empty _ h'
  have hB1 := val_mem_otci_of_mem_aotci (tensorProdATwoAOneBase_mem_aotci hQ W) (mem_succ_self _)
  have hRB := (rtlosOf_of_mem_otci_one hB1).left
  rw [rel_odrOne_tensorProdATwoAOne_iff hQ hX, rel_odrOne_tensorProdATwoAOne_iff hQ hW, hBX]
  have hnot {a : M} (ha : a ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M))) :
      ¬ IsTpTwo Q X a := not_isTpTwo_of_mem_base hQ (by rw [hBX]; exact ha)
  rw [hBX] at hz hz' hdisjX
  have hBm {a b : M} (h : a [odrOne (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M))] b) :
      a ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M)) ∧
        b ∈ ndOf (tensorProdATwoAOneBase Q W ﹫ ((1 : ℕ) : M)) :=
    ⟨hRB.mem_left h, hRB.mem_right h⟩
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  · rw [pushNd_of_not (hnot hz), pushNd_of_not (hnot hz')]
    constructor
    · rintro (h | h | h)
      · exact .inl h
      · exact (hdisjX _ hz h.left).elim
      · exact (hdisjX _ hz' h.right).elim
    · rintro (h | h | h)
      · exact .inl h
      · exact (hdisj _ hz h.left).elim
      · exact (hdisj _ hz' h.right).elim
  · rw [pushNd_of_not (hnot hz)]
    exact iff_of_true (.inr (.inr ⟨hz, hz'⟩))
      (.inr (.inr ⟨hz, pushNd_mem_of_mem hQ hX hW hψ hz'⟩))
  · rw [pushNd_of_not (hnot hz')]
    have hpz := pushNd_mem_of_mem hQ hX hW hψ (W := W) (ψ := ψ) hz
    refine iff_of_false ?_ ?_
    · rintro (h | h | h)
      · exact hdisjX _ (hBm h).left hz
      · exact hdisjX _ hz' h.right.left
      · exact hdisjX _ h.left hz
    · rintro (h | h | h)
      · exact hdisj _ (hBm h).left hpz
      · exact hdisj _ hz' h.right.left
      · exact hdisj _ h.left hpz
  · have hpz := pushNd_mem_of_mem hQ hX hW hψ (W := W) (ψ := ψ) hz
    have hpz' := pushNd_mem_of_mem hQ hX hW hψ (W := W) (ψ := ψ) hz'
    rw [tensorProdTwoAOneLt_pushNd_iff hQ hX hW hψ hz hz']
    constructor
    · rintro (h | ⟨-, -, h⟩ | h)
      · exact (hdisjX _ (hBm h).left hz).elim
      · exact .inr (.inl ⟨hpz, hpz', h⟩)
      · exact (hdisjX _ h.left hz).elim
    · rintro (h | ⟨-, -, h⟩ | h)
      · exact (hdisj _ (hBm h).left hpz).elim
      · exact .inr (.inl ⟨hz, hz', h⟩)
      · exact (hdisj _ h.left hpz).elim

end PushNdFull

section IsoDefinable

/-! ### Definability of the pieces of the isomorphism -/

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ otciSngIso (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ otciSngIso (xs 0) (xs 1) = xs 2) =
      fun xs ↦ update ∅ (⋃₀ ndOf (xs 0)) (⋃₀ ndOf (xs 1)) = xs 2 := rfl
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ otciSngIso (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ otciSngIso (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ otciSngIso (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ embMk (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ embMk (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∃ a b c : M, a = xs 0 ﹫ (∅ : M) ∧ b = xs 1 ﹫ (∅ : M) ∧ otciSngIso a b = c ∧
        cc (cc (∅ : M) c) (xs 2) = xs 3 := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, _, rfl, rfl, rfl, h⟩
    · rintro ⟨a, b, c, rfl, rfl, rfl, h⟩
      exact h
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ embMk (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ embMk (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ embMk (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : MulticlassFunction.Sigma (fun ys : Fin 1 → M ↦ unrel (ys 0)) 1 Set.univ := by
  unfold unrel; infer_instance

instance : ClassFunction.Definable (fun z : M ↦ pushOne (left z) (right z)) Set.univ := by
  unfold pushOne
  have : MulticlassFunction.Sigma (fun ys : Fin 2 → M ↦
      (left (ys 0) ﹫ ((1 : ℕ) : M)) ﹫ unrel ((right (ys 0) ﹫ ((1 : ℕ) : M)) ﹫ ys 1)) 1
      Set.univ := by infer_instance
  have : Multiclass.Definable (fun xs : Fin 3 → M ↦
      (fun z u ↦ (left z ﹫ ((1 : ℕ) : M)) ﹫ unrel ((right z ﹫ ((1 : ℕ) : M)) ﹫ u)) (xs 0) (xs 1) =
        xs 2) Set.univ :=
    (inferInstance : MulticlassFunction.Definable (fun ys : Fin 2 → M ↦
      (left (ys 0) ﹫ ((1 : ℕ) : M)) ﹫ unrel ((right (ys 0) ﹫ ((1 : ℕ) : M)) ﹫ ys 1))
        Set.univ).1
  exact ClassFunction.Definable.toSetRestrictedTo (D := fun z ↦ dom (right z ﹫ ((1 : ℕ) : M)))

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ pushOne (xs 0) (xs 1) = xs 2) Set.univ :=
  Multiclass.definable_graph₂ inferInstance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ pushOne (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ pushOne (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ pushOne (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 5 → M ↦ pushEmb (xs 0) (xs 1) (xs 2) (xs 3) = xs 4)
    Set.univ := by
  have : ClassFunction.Definable (fun Q : M ↦ tensorProdTwoAOneTgt Q) Set.univ := inferInstance
  have h : (fun xs : Fin 5 → M ↦ pushEmb (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) =
      fun xs : Fin 5 → M ↦ ∃ T φ : M, tensorProdTwoAOneTgt (xs 0) = T ∧
        pushOne (xs 2) (xs 3) = φ ∧ embMk (xs 1) T φ = xs 4 := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, rfl, rfl, h⟩
    · rintro ⟨T, φ, rfl, rfl, h⟩
      exact h
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ pushEmb (xs i) (xs j) (xs k) (xs l) = xs m) Set.univ := by
  have h : (fun xs : Fin n → M ↦ pushEmb (xs i) (xs j) (xs k) (xs l) = xs m) = Multiclass.remap
      (fun ys : Fin 5 → M ↦ pushEmb (ys 0) (ys 1) (ys 2) (ys 3) = ys 4) ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The `Q(2)`-branch of the push -/
def PushNdTwo (W ψ z r : M) : Prop :=
  ∃ q h A e : M, q = nodeQ z ∧ h = nodeH z ∧ A = aoc (uc q) ∧ pushEmb W A ψ h = e ∧
    r = !(dctUZero, !(q, e))

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ PushNdTwo (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  unfold PushNdTwo; infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ PushNdTwo (xs i) (xs j) (xs k) (xs l)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ PushNdTwo (xs i) (xs j) (xs k) (xs l)) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ PushNdTwo (ys 0) (ys 1) (ys 2) (ys 3)) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable
    (fun xs : Fin 6 → M ↦ pushNd (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) = xs 5) Set.univ := by
  have h : (fun xs : Fin 6 → M ↦ pushNd (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) = xs 5) =
      fun xs : Fin 6 → M ↦ (IsTpTwo (xs 0) (xs 1) (xs 4) ∧ PushNdTwo (xs 2) (xs 3) (xs 4) (xs 5)) ∨
        (¬ IsTpTwo (xs 0) (xs 1) (xs 4) ∧ xs 4 = xs 5) := by
    funext xs
    apply propext
    by_cases hp : IsTpTwo (xs 0) (xs 1) (xs 4)
    · rw [pushNd, if_pos hp]
      simp only [PushNdTwo, hp, true_and, not_true_eq_false, false_and, or_false]
      constructor
      · intro h
        exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, h.symm⟩
      · rintro ⟨q, h, A, e, rfl, rfl, rfl, rfl, h'⟩
        exact h'.symm
    · rw [pushNd, if_neg hp]
      simp only [hp, false_and, false_or, not_false_eq_true, true_and]
  rw [h]
  infer_instance

end IsoDefinable

section IsoDefinable2

instance : ClassFunction.Definable (fun y : M ↦ relabelOne trvAZero y) Set.univ := by
  have h : (fun y : M ↦ relabelOne trvAZero y) =
      fun y ↦ !(uc y, !(lbl y, tensorProdAZeroAZero (aoc (uc y)) ∅)) := rfl
  rw [h]
  infer_instance

/-- The value `ρ(Φ_ψ(σ(w)))` for the packed parameters `p = ((Q, X), (W, (ψ, σ)))` -/
noncomputable def tauG (p w : M) : M :=
  relabelOne trvAZero (pushNd (left (left p)) (right (left p)) (left (right p))
    (left (right (right p))) ((right (right (right p)) ﹫ ((1 : ℕ) : M)) ﹫ w))

instance {n : ℕ} (i j k l m o : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ pushNd (xs i) (xs j) (xs k) (xs l) (xs m) = xs o) Set.univ := by
  have h : (fun xs : Fin n → M ↦ pushNd (xs i) (xs j) (xs k) (xs l) (xs m) = xs o) =
      Multiclass.remap (fun ys : Fin 6 → M ↦
        pushNd (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) = ys 5) ![i, j, k, l, m, o] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 2 → M ↦ relabelOne trvAZero (xs 0) = xs 1)
    Set.univ := by
  have h : (fun xs : Fin 2 → M ↦ relabelOne trvAZero (xs 0) = xs 1) = fun xs : Fin 2 → M ↦
      !(uc (xs 0), !(lbl (xs 0), tensorProdAZeroAZero (aoc (uc (xs 0))) ∅)) = xs 1 := rfl
  rw [h]
  infer_instance

instance {n : ℕ} (i j : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ relabelOne trvAZero (xs i) = xs j) Set.univ := by
  have h : (fun xs : Fin n → M ↦ relabelOne trvAZero (xs i) = xs j) =
      Multiclass.remap (fun ys : Fin 2 → M ↦ relabelOne trvAZero (ys 0) = ys 1) ![i, j] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The graph of `w ↦ ρ(Φ_ψ(σ(w)))` with explicit parameters -/
def TauGRel (Q X W ψ σ w r : M) : Prop :=
  ∃ z z' : M, z = (σ ﹫ ((1 : ℕ) : M)) ﹫ w ∧ pushNd Q X W ψ z = z' ∧ relabelOne trvAZero z' = r

instance : Multiclass.Definable
    (fun xs : Fin 7 → M ↦ TauGRel (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6)) Set.univ := by
  unfold TauGRel; infer_instance

instance {n : ℕ} (i j k l m o u : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ TauGRel (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ TauGRel (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) (xs u)) =
      Multiclass.remap (fun ys : Fin 7 → M ↦
        TauGRel (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6)) ![i, j, k, l, m, o, u] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- Unpacking `c = (ψ, σ)` -/
def TauGRel₄ (Q X W c w r : M) : Prop := ∃ ψ σ : M, ψ = left c ∧ σ = right c ∧ TauGRel Q X W ψ σ w r

instance : Multiclass.Definable
    (fun xs : Fin 6 → M ↦ TauGRel₄ (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5)) Set.univ := by
  unfold TauGRel₄; infer_instance

instance {n : ℕ} (i j k l m o : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ TauGRel₄ (xs i) (xs j) (xs k) (xs l) (xs m) (xs o)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ TauGRel₄ (xs i) (xs j) (xs k) (xs l) (xs m) (xs o)) =
      Multiclass.remap (fun ys : Fin 6 → M ↦
        TauGRel₄ (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)) ![i, j, k, l, m, o] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- Unpacking `b = (W, c)` -/
def TauGRel₃ (Q X b w r : M) : Prop := ∃ W c : M, W = left b ∧ c = right b ∧ TauGRel₄ Q X W c w r

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ TauGRel₃ (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)) Set.univ := by
  unfold TauGRel₃; infer_instance

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ TauGRel₃ (xs i) (xs j) (xs k) (xs l) (xs m)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ TauGRel₃ (xs i) (xs j) (xs k) (xs l) (xs m)) =
      Multiclass.remap (fun ys : Fin 5 → M ↦
        TauGRel₃ (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)) ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- Unpacking `a = (Q, X)` -/
def TauGRel₂ (a b w r : M) : Prop := ∃ Q X : M, Q = left a ∧ X = right a ∧ TauGRel₃ Q X b w r

instance : Multiclass.Definable
    (fun xs : Fin 4 → M ↦ TauGRel₂ (xs 0) (xs 1) (xs 2) (xs 3)) Set.univ := by
  unfold TauGRel₂; infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ TauGRel₂ (xs i) (xs j) (xs k) (xs l)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ TauGRel₂ (xs i) (xs j) (xs k) (xs l)) =
      Multiclass.remap (fun ys : Fin 4 → M ↦ TauGRel₂ (ys 0) (ys 1) (ys 2) (ys 3)) ![i, j, k,
          l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ tauG (xs 0) (xs 1) = xs 2) Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ tauG (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ a b : M, a = left (xs 0) ∧ b = right (xs 0) ∧ TauGRel₂ a b (xs 1) (xs 2) := by
    funext xs
    apply propext
    simp only [tauG, TauGRel₂, TauGRel₃, TauGRel₄, TauGRel]
    constructor
    · intro h
      exact ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, h⟩
    · rintro ⟨a, b, rfl, rfl, Q, X, rfl, rfl, W, c, rfl, rfl, ψ, σ, rfl, rfl, z, z', rfl, rfl, h⟩
      exact h
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ tauG (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tauG (xs i) (xs j) = xs k) =
      Multiclass.remap (fun ys : Fin 3 → M ↦ tauG (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

end IsoDefinable2

section Tau

/-! ### The image `(t, ρ ∘ Φ_ψ ∘ σ)` of a node `((V, (t, σ)), ψ)` -/

variable {Q X W A ψ σ : M}

theorem isSetRestrictedTo_tauOne (Q X W ψ σ : M) : IsSetRestrictedTo
    (fun w ↦ relabelOne trvAZero (pushNd Q X W ψ ((σ ﹫ ((1 : ℕ) : M)) ﹫ w)))
    (dom (σ ﹫ ((1 : ℕ) : M))) := by
  have hf : (fun w ↦ relabelOne trvAZero (pushNd Q X W ψ ((σ ﹫ ((1 : ℕ) : M)) ﹫ w))) =
      fun w ↦ tauG !(!(Q, X), !(W, !(ψ, σ))) w := by
    funext w
    simp only [tauG, left_orderedPair, right_orderedPair]
  rw [hf]
  generalize !(!(Q, X), !(W, !(ψ, σ))) = P₀
  have : ClassFunction.Definable (fun w ↦ tauG P₀ w) Set.univ :=
    ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ p : M,
      p = P₀ ∧ tauG p (xs 0) = xs 1) fun u w ↦ by
        constructor
        · rintro ⟨p, rfl, h⟩
          exact h
        · intro h
          exact ⟨_, rfl, h⟩
  exact isSetRestrictedTo_of_definable _

/-- The level-`1` part `w ↦ ρ(Φ_ψ(σ(w)))` -/
noncomputable def tauOne (Q X W ψ σ : M) : M :=
  (fun w ↦ relabelOne trvAZero (pushNd Q X W ψ ((σ ﹫ ((1 : ℕ) : M)) ﹫ w))) ↾₀
    dom (σ ﹫ ((1 : ℕ) : M))

theorem tauOne_spec (Q X W ψ σ : M) : IsFunction (tauOne Q X W ψ σ) ∧
    dom (tauOne Q X W ψ σ) = dom (σ ﹫ ((1 : ℕ) : M)) ∧ ∀ w ∈ dom (σ ﹫ ((1 : ℕ) : M)),
      tauOne Q X W ψ σ ﹫ w = relabelOne trvAZero (pushNd Q X W ψ ((σ ﹫ ((1 : ℕ) : M)) ﹫ w)) :=
  ⟨isFunction_toSetRestrictedTo (isSetRestrictedTo_tauOne Q X W ψ σ),
    dom_toSetRestrictedTo (isSetRestrictedTo_tauOne Q X W ψ σ),
    fun _ hw ↦ val_toSetRestrictedTo (isSetRestrictedTo_tauOne Q X W ψ σ) hw⟩

/-- The embedding `ρ ∘ Φ_ψ ∘ σ` of `A` into `(Q ⊗ W) ⊗ Z` -/
noncomputable def tauEmb (Q X W A ψ σ : M) : M :=
  embMk A (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W)) (tauOne Q X W ψ σ)

theorem tauEmb_val_one (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) A (tensorProdATwoAOne Q X))
    {w : M} (hw : w ∈ ndOf (A ﹫ ((1 : ℕ) : M))) :
    (tauEmb Q X W A ψ σ ﹫ ((1 : ℕ) : M)) ﹫ w =
      relabelOne trvAZero (pushNd Q X W ψ ((σ ﹫ ((1 : ℕ) : M)) ﹫ w)) := by
  obtain ⟨-, hσd⟩ := embChg_val_one_isFunction hσ
  rw [tauEmb, embMk_val_one, (tauOne_spec Q X W ψ σ).right.right w (by rw [hσd]; exact hw)]

/-- `ρ ∘ Φ_ψ ∘ σ` is an embedding -/
theorem tauEmb_mem (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hX : X ∈ aotci ((1 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) (hA : A ∈ aotci ((1 : ℕ) : M))
    (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) A (tensorProdATwoAOne Q X))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) X (tensorProdTwoAOneTgt W)) :
    tauEmb Q X W A ψ σ ∈
      aotciEmbSet ((1 : ℕ) : M) A (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W)) := by
  have hBX := tensorProdATwoAOne_mem_aotci hQ hX
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hBW1 := val_mem_otci_of_mem_aotci hBW (mem_succ_self _)
  have hT := tensorProdTwoAOneTgt_mem hBW
  obtain ⟨-, hσd⟩ := embChg_val_one_isFunction hσ
  refine embMk_mem_aotciEmbSet' hA hT (tauOne_spec Q X W ψ σ).left
    (by rw [(tauOne_spec Q X W ψ σ).right.left, hσd]) (fun a ha ↦ ?_) (fun a ha b hb hab ↦ ?_)
  · rw [(tauOne_spec Q X W ψ σ).right.right a (by rw [hσd]; exact ha), tensorProdTwoAOneTgt_val_one,
      mem_ndOf_tensorProdOneAZero_iff hBW1]
    exact ⟨_, pushNd_mem hQ hX hW hψ (emb_val_mem hA hBX hσ ha), rfl⟩
  · rw [(tauOne_spec Q X W ψ σ).right.right a (by rw [hσd]; exact ha),
      (tauOne_spec Q X W ψ σ).right.right b (by rw [hσd]; exact hb),
      rel_tgt_relabel_iff hBW (pushNd_mem hQ hX hW hψ (emb_val_mem hA hBX hσ ha))
        (pushNd_mem hQ hX hW hψ (emb_val_mem hA hBX hσ hb))]
    exact (pushNd_odr_iff hQ hX hW hψ (emb_val_mem hA hBX hσ ha) (emb_val_mem hA hBX hσ hb)).mp
      (emb_odr hA hBX hσ ha hb hab)

end Tau

section IsoUp

/-! ### The image of an upper node -/

variable {P Q W V t σ ψ : M}

/-- The roots of `P ⊗ Q` are the nodes with empty signature -/
theorem mem_rtOf_tensorProdTwoTwo_iff {x : M} (hx : x ∈ tensorProdTwoTwoNds P Q) :
    x ∈ rtOf (tensorProdTwoTwo P Q) ↔ dom (sig (uc x)) = ∅ := by
  have hres : IsSetRestrictedTo (fun x ↦ dom (sig (uc x))) (tensorProdTwoTwoNds P Q) :=
    isSetRestrictedTo_of_definable _
  have hrt : rtOf (tensorProdTwoTwo P Q) = (tensorProdTwoTwoTs P Q).rt := by
    change (SLOTreeStructure.mk (tensorProdTwoTwoTs P Q) _).ts.rt = _
    rw [SLOTreeStructure.ts_mk]
  rw [hrt, TreeStructure.mem_rt_iff, tensorProdTwoTwoTs, TreeStructure.nd_mk,
    TreeStructure.dep_mk, val_toSetRestrictedTo hres hx]
  exact ⟨fun h ↦ h.right, fun h ↦ ⟨hx, h⟩⟩

/-- The node `t` of a non-root node `(V, (t, σ))` is not a root -/
theorem not_mem_rtOf_of_sig_ne_empty (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hx : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q) (hs : sig V ≠ ∅) : t ∉ rtOf P := by
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hx
  obtain ⟨ht, -, -, hemb⟩ := hx
  intro htr
  have hd : dom (sig (uc t)) = ∅ := by
    rw [dom_sig_uc_eq_depOf hP ht]
    exact (TreeStructure.mem_rt_iff.mp htr).right
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have h0 : embTpSigs Q (aoc V) (uc t) σ = ∅ :=
    (isFinSeqSeq_embTpSigs hQ (dom_sig_mem_omega_of_mem_stduoci_one hUt) _
      σ).left.isRelation.eq_empty_of_dom_eq_empty (by rw [dom_embTpSigs, hd])
  have hcon := hemb.left.right.left
  rw [h0, contraction_empty] at hcon
  exact hs hcon.symm

/-- The image `(t, ρ ∘ Φ_ψ ∘ σ)` of the node `((V, (t, σ)), ψ)` of `(P ⊗ Q) ⊗ W` -/
noncomputable def isoUpOf (Q W V t σ ψ : M) : M :=
  !(dctUZero, !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ))

/-- The image of an upper node is an upper node of `P ⊗ (Q ⊗ W)` -/
theorem isoUpOf_mem (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) (hx : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q)
    (hs : sig V ≠ ∅) (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W)) :
    isoUpOf Q W V t σ ψ ∈ tensorProdTwoAOneNds P (tensorProdATwoAOne Q W) := by
  have htr := not_mem_rtOf_of_sig_ne_empty hP hQ hx hs
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hx
  obtain ⟨ht, hV, hσ, -⟩ := hx
  exact mem_tensorProdTwoAOneNds_iff'.mpr ⟨t, ht, htr, _, tauEmb_mem hQ
    (aoc_mem_aotci_of_mem_stduoci_one hV) hW
    (aoc_mem_aotci_of_mem_stduoci_one (uc_mem_stduoci_of_mem_otci_two hP ht)) hσ hψ, rfl⟩

end IsoUp

section SameKey

variable {P Q X W ψ : M}

/-- The push is injective -/
theorem pushNd_inj (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hX : X ∈ aotci ((1 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) X (tensorProdTwoAOneTgt W))
    {z z' : M} (hz : z ∈ ndOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M)))
    (hz' : z' ∈ ndOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M)))
    (h : pushNd Q X W ψ z = pushNd Q X W ψ z') : z = z' := by
  have hR := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci
    (tensorProdATwoAOne_mem_aotci hQ hX) (mem_succ_self _))).left
  have hR' := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci
    (tensorProdATwoAOne_mem_aotci hQ hW) (mem_succ_self _))).left
  rcases hR.isTrichotomousOn z hz z' hz' with h' | h' | h'
  · have := (pushNd_odr_iff hQ hX hW hψ hz hz').mp h'
    rw [h] at this
    exact (hR'.irrefl _ this).elim
  · exact h'
  · have := (pushNd_odr_iff hQ hX hW hψ hz' hz).mp h'
    rw [h] at this
    exact (hR'.irrefl _ this).elim

/-- For nodes with the same key and the same `ψ`, the order of `P ⊗ Q` is that of the images -/
theorem bkLt_iff_isoUpOf (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hX : X ∈ aotci ((1 : ℕ) : M)) (hW : W ∈ aotci ((1 : ℕ) : M))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) X (tensorProdTwoAOneTgt W)) {t σ t' σ' : M}
    (ht : t ∈ ndOf P) (ht' : t' ∈ ndOf P)
    (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q X))
    (hσ' : σ' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t')) (tensorProdATwoAOne Q X)) :
    BKLt (tensorProdTwoTwoCoordOdr P Q X) (tensorProdTwoAOneSeq P !(t, σ))
        (tensorProdTwoAOneSeq P !(t', σ')) ↔
      BKLt (tensorProdTwoAOneCoordOdr P (tensorProdATwoAOne Q W))
        (tensorProdTwoAOneSeq P !(t, tauEmb Q X W (aoc (uc t)) ψ σ))
        (tensorProdTwoAOneSeq P !(t', tauEmb Q X W (aoc (uc t')) ψ σ')) := by
  have hBX := tensorProdATwoAOne_mem_aotci hQ hX
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hBW1 := val_mem_otci_of_mem_aotci hBW (mem_succ_self _)
  let κ : M → M := fun c ↦ !(relabelOne trvAZero (pushNd Q X W ψ (left c)), right c)
  have hdep (p : M) (hp : p ∈ ndOf P) : Ordinal (depOf P p) :=
    ordinal_of_mem ordinal_omega ((otciCond_two hP).left.isTreeStructure.dep_mem_omega hp)
  have hsv {p h : M} (hp : p ∈ ndOf P)
      (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) (tensorProdATwoAOne Q X)) :
      ∀ i ∈ dom (tensorProdTwoAOneSeq P !(p, h)),
        tensorProdTwoAOneSeq P !(p, tauEmb Q X W (aoc (uc p)) ψ h) ﹫ i =
          κ (tensorProdTwoAOneSeq P !(p, h) ﹫ i) := by
    intro i hi
    rw [tensorProdTwoAOneSeq_dom] at hi
    have hUp := uc_mem_stduoci_of_mem_otci_two hP hp
    have hip : i ∈ dom (sig (uc p)) := by rw [dom_sig_uc_eq_depOf hP hp]; exact hi
    rw [tensorProdTwoAOneSeq_val hP hp hi, tensorProdTwoAOneSeq_val hP hp hi,
      tauEmb_val_one hh (siglvl_eq_one hUp hip).right]
    simp only [κ, left_orderedPair, right_orderedPair]
  have hsC {p h : M} (hp : p ∈ ndOf P)
      (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) (tensorProdATwoAOne Q X)) :
      ∀ i ∈ dom (tensorProdTwoAOneSeq P !(p, h)), tensorProdTwoAOneSeq P !(p, h) ﹫ i ∈
        ndOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M)) ×ˢ ndOf P := by
    intro i hi
    rw [tensorProdTwoAOneSeq_dom] at hi
    exact tensorProdTwoAOneSeq_val_mem hP hp hh hi
  unfold tensorProdTwoTwoCoordOdr tensorProdTwoAOneCoordOdr
  refine bkLt_iff_of_map κ (isFunction_tensorProdTwoAOneSeq _ _)
    (isFunction_tensorProdTwoAOneSeq _ _) (isFunction_tensorProdTwoAOneSeq _ _)
    (isFunction_tensorProdTwoAOneSeq _ _) (by rw [tensorProdTwoAOneSeq_dom,
      tensorProdTwoAOneSeq_dom]) (by rw [tensorProdTwoAOneSeq_dom, tensorProdTwoAOneSeq_dom])
    (hsv ht hσ) (hsv ht' hσ') (hsC ht hσ) (hsC ht' hσ') (fun c hc c' hc' h ↦ ?_)
    (fun c hc c' hc' ↦ ?_) (by rw [tensorProdTwoAOneSeq_dom]; exact hdep t ht)
    (by rw [tensorProdTwoAOneSeq_dom]; exact hdep t' ht')
  · rw [mem_sprod_iff] at hc hc'
    obtain ⟨z, hz, n, -, rfl⟩ := hc
    obtain ⟨z', hz', n', -, rfl⟩ := hc'
    simp only [κ, left_orderedPair, right_orderedPair, orderedPair_eq_orderedPair_iff] at h
    rw [pushNd_inj hQ hX hW hψ hz hz' (relabelOne_injective hBW1 (pushNd_mem hQ hX hW hψ hz)
      (pushNd_mem hQ hX hW hψ hz') h.left), h.right]
  · rw [mem_sprod_iff] at hc hc'
    obtain ⟨z, hz, n, hn, rfl⟩ := hc
    obtain ⟨z', hz', n', hn', rfl⟩ := hc'
    have hpz := pushNd_mem hQ hX hW hψ hz
    have hpz' := pushNd_mem hQ hX hW hψ hz'
    have e1 : z [losOdr (rtlosOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M)) ﹫ trvAZero)] z' ↔
        (relabelOne trvAZero (pushNd Q X W ψ z))
          [losOdr (rtlosOf (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)) ﹫
            trvAZero)] (relabelOne trvAZero (pushNd Q X W ψ z')) :=
      (pushNd_odr_iff hQ hX hW hψ hz hz').trans (rel_tgt_relabel_iff hBW hpz hpz').symm
    have e2 : z = z' ↔ relabelOne trvAZero (pushNd Q X W ψ z) =
        relabelOne trvAZero (pushNd Q X W ψ z') :=
      ⟨fun h ↦ by rw [h], fun h ↦ pushNd_inj hQ hX hW hψ hz hz'
        (relabelOne_injective hBW1 hpz hpz' h)⟩
    have m1 : relabelOne trvAZero (pushNd Q X W ψ z) ∈
        ndOf (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)) := by
      rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hBW1]
      exact ⟨_, hpz, rfl⟩
    have m2 : relabelOne trvAZero (pushNd Q X W ψ z') ∈
        ndOf (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)) := by
      rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hBW1]
      exact ⟨_, hpz', rfl⟩
    simp only [κ, left_orderedPair, right_orderedPair]
    rw [rel_lexProd_iff, rel_lexProd_iff, e1, e2]
    exact ⟨fun h ↦ ⟨⟨m1, hn⟩, ⟨m2, hn'⟩, h.right.right⟩,
      fun h ↦ ⟨⟨hz, hn⟩, ⟨hz', hn'⟩, h.right.right⟩⟩

end SameKey



section PushOld

variable {Q X X' W ψ ψ' : M}

/-- On the old nodes, pushing along `ψ'` and along an extension `ψ` agree -/
theorem pushNd_old (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hX : X ∈ aotci ((1 : ℕ) : M))
    (hX' : X' ∈ aotci ((1 : ℕ) : M)) (h0 : X ﹫ ∅ = X' ﹫ ∅)
    (hsub : IsSubOne (X' ﹫ ((1 : ℕ) : M)) (X ﹫ ((1 : ℕ) : M)))
    (hagr : ∀ v ∈ ndOf (X' ﹫ ((1 : ℕ) : M)),
      (ψ' ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ ﹫ ((1 : ℕ) : M)) ﹫ v)
    {z : M} (hz : z ∈ ndOf (tensorProdATwoAOne Q X' ﹫ ((1 : ℕ) : M))) :
    pushNd Q X' W ψ' z = pushNd Q X W ψ z := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  rw [mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX'] at hz
  rcases hz with hz | hz
  · rw [pushNd_of_not (not_isTpTwo_of_mem_base hQ hz), pushNd_of_not
      (not_isTpTwo_of_mem_base hQ (by rw [base_val_one_congr Q X X']; exact hz))]
  · have hzX := ((mem_tensorProdTwoAOneNds_iff_of_isSubOne hQ hX hX' h0 hsub).mp hz).left
    obtain ⟨q, hq, -, g, hg, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp hz
    rw [pushNd_of_mem hz, pushNd_of_mem hzX, pushEmb, pushEmb]
    congr 3
    obtain ⟨hf, hd, hv⟩ := pushOne_spec ψ' g
    obtain ⟨hf', hd', hv'⟩ := pushOne_spec ψ g
    obtain ⟨-, hgd⟩ := embChg_val_one_isFunction hg
    refine hf.ext hf' (by rw [hd, hd']) fun u hu ↦ ?_
    rw [hd, hgd] at hu
    obtain ⟨w, hw, hgw⟩ := exists_relabelOne_eq hX' hg hu
    rw [pushOne_val_of_eq hX' hg hu hw hgw, hagr w hw]
    rw [hv' u (by rw [hgd]; exact hu), hgw, unrel_relabelOne
      ((isSLOT_of_mem_otci (val_mem_otci_of_mem_aotci hX' (mem_succ_self _))).isOrderedPair hw)]

end PushOld

section RhsSeq

variable {P Q X W A t ψ σ : M}

/-- The coordinates of the sequence of the image `(t, ρ ∘ Φ_ψ ∘ σ)` -/
theorem seq_tauEmb_val (hP : P ∈ otci ((2 : ℕ) : M)) (ht : t ∈ ndOf P)
    (hσ : σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q X)) {i : M}
    (hi : i ∈ depOf P t) :
    tensorProdTwoAOneSeq P !(t, tauEmb Q X W (aoc (uc t)) ψ σ) ﹫ i =
      !(relabelOne trvAZero (pushNd Q X W ψ ((σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i)),
        ancOf P t (succ i)) := by
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  rw [tensorProdTwoAOneSeq_val hP ht hi, tauEmb_val_one hσ
    (siglvl_eq_one hUt (by rw [dom_sig_uc_eq_depOf hP ht]; exact hi)).right]

end RhsSeq

section ChdStruct

variable {P Q : M}

/-- The structure of the parent of a node `c = (V, (t, σ))` of `P ⊗ Q` with `|V_sig| ≥ 2`: with
the first occurrence `(l, k)` of the newest entry, `y = σ(w_l)` and its successor `D`, the parent
is `(V | m, (t_l, σ ↾ t_l))` with `D = σ(ucf t_l)`, or `(V | m, (t_l⁺, σ[w_l ↦ D]))` -/
theorem chd_struct (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {V t σ C : M} (hc : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q)
    (hm0 : ⋃₀ dom (sig V) ≠ ∅) (hprt : tensorProdTwoTwoPrt P Q !(V, !(t, σ)) = C) :
    ∃ l k q h D, IsFirstOcc (embTpSigs Q (aoc V) (uc t) σ) (sig V ﹫ ⋃₀ dom (sig V)) l k ∧
      l ∈ depOf P t ∧ (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l = !(dctUZero, !(q, h)) ∧
      q ∈ ndOf (Q ﹫ 2) ∧ !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) ∧
      h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)) ∧
      k ∈ depOf (Q ﹫ 2) q ∧ (∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V))) ∧
      sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V)) ∧
      D ∈ tensorProdTwoAOneNds (Q ﹫ 2) (iniSegAoc V (⋃₀ dom (sig V))) ∧
      !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] D ∧
      (∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
        !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
          z = D ∨ D [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) ∧
      ((C = !(iniSeg V (⋃₀ dom (sig V)), !(ancOf P t l, embRestrict (uc (ancOf P t l)) σ)) ∧
          ucflvl (uc (ancOf P t l)) ≠ ∅ ∧ D = (σ ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc (ancOf P t l))) ∨
        C = !(iniSeg V (⋃₀ dom (sig V)), !(ctChd P (ancOf P t l) (aoc (uc (ancOf P t (succ l)))),
          embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D))) := by
  have hV := uc_mem_stduoci_of_mem_tensorProdTwoTwoNds hc
  rw [uc_orderedPair] at hV
  have hdV : dom (sig V) ≠ ∅ := fun h' ↦ hm0 (by rw [h', sUnion_empty])
  have hm : ⋃₀ dom (sig V) ∈ dom (sig V) :=
    (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV) hdV).right.left
  have hR := iniSegRight_ne_empty_of_mem hP hQ hc (by rw [uc_orderedPair]; exact hm0)
  rw [uc_orderedPair] at hR
  obtain ⟨l, k, q, h, hfo, hl, hy, hq, hyN, hh, hk, hfirst, hje, hrow, himg⟩ :=
    firstOcc_data hP hQ hc hm
  have hnQ := nodeQ_orderedPair V t σ
  have hnH := nodeH_orderedPair V t σ
  have hsucc : prtSucc Q !(V, !(t, σ)) =
      ⋃₀ (aboveIn (odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
        (ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
        !(dctUZero, !(q, h)) ∩₀ fun z ↦ IsLeastIn
          (odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
          (aboveIn (odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)))
            (ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
            !(dctUZero, !(q, h))) z) := by
    rw [prtSucc, prtAbove, prtOdr, prtSmall, prtUc, uc_orderedPair, uociEmbTgt,
      uociEmbTgt, aoc_iniSeg, himg]
    rfl
  rcases succ_spec hQ hV hm hq hyN hh hk hfirst hje with ⟨-, -, hR0, -⟩ |
    ⟨D, hDe, hDN, hlt, hmin, -⟩
  · exact (hR hR0).elim
  rw [← hsucc] at hDe
  have hancL : prtAncL P Q !(V, !(t, σ)) = ancOf P t l := by rw [prtAncL, hnQ, hrow]
  have hancS : prtAncS P Q !(V, !(t, σ)) = ancOf P t (succ l) := by
    rw [prtAncS, ancSucc, hnQ, hrow]
  have hnode : prtNode Q !(V, !(t, σ)) = sigdcn (uc t) l := by
    rw [prtNode, nodeU_orderedPair, hrow]
  refine ⟨l, k, q, h, D, hfo, hl, hy, hq, hyN, hh, hk, hfirst, hje, hDN, hlt, hmin, ?_⟩
  rw [tensorProdTwoTwoPrt, if_neg (by rw [uc_orderedPair]; exact hm0), prtTwo, prtUc,
    uc_orderedPair, prtLbl] at hprt
  have hDne : D ≠ ∅ := by
    obtain ⟨-, -, -, -, -, rfl⟩ := mem_tensorProdTwoAOneNds_iff'.mp hDN
    exact orderedPair_ne_empty _ _
  by_cases hcase : PrtCase P Q !(V, !(t, σ))
  · left
    rw [if_pos hcase, prtLblOne, hancL, cutRes, hnH] at hprt
    rw [PrtCase, hDe, prtUcfImg, hnH, hancL] at hcase
    have hlv : ucflvl (uc (ancOf P t l)) ≠ ∅ := by
      intro h0
      rw [ucfImg, if_pos h0] at hcase
      exact hDne hcase
    rw [ucfImg, if_neg hlv] at hcase
    exact ⟨hprt.symm, hlv, hcase⟩
  · right
    rw [if_neg hcase, prtLblTwo, prtCt, prtEmbTwo, hancL, hancS, hnH, hnode, hDe] at hprt
    exact hprt.symm

end ChdStruct

section ChdPrtOrder

variable {P Q W : M}

/-- The image of a child is below the image of its parent -/
theorem bkLt_isoUp_chd (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {V t σ VC tC σC ψ ψC : M}
    (hc : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q) (hm0 : ⋃₀ dom (sig V) ≠ ∅)
    (hprt : tensorProdTwoTwoPrt P Q !(V, !(t, σ)) = !(VC, !(tC, σC)))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W))
    (hagr : ∀ v ∈ ndOf (aoc VC ﹫ ((1 : ℕ) : M)),
      (ψC ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ ﹫ ((1 : ℕ) : M)) ﹫ v) :
    BKLt (tensorProdTwoAOneCoordOdr P (tensorProdATwoAOne Q W))
      (tensorProdTwoAOneSeq P !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ))
      (tensorProdTwoAOneSeq P !(tC, tauEmb Q (aoc VC) W (aoc (uc tC)) ψC σC)) := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  have hPs : IsSLOT P := (otciCond_two hP).left
  have hCN := tensorProdTwoTwoPrt_mem hP hQ hc (by
    rw [uc_orderedPair]; exact fun h' ↦ hm0 (by rw [h', sUnion_empty]))
  rw [hprt, pair_mem_tensorProdTwoTwoNds_iff] at hCN
  obtain ⟨htC, -, hσC, -⟩ := hCN
  have hc' := hc
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hc'
  obtain ⟨ht, hV, hσ, -⟩ := hc'
  have hdV : dom (sig V) ≠ ∅ := fun h' ↦ hm0 (by rw [h', sUnion_empty])
  have hm : ⋃₀ dom (sig V) ∈ dom (sig V) :=
    (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV) hdV).right.left
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, -⟩ := lastSeg_facts hV hm
  have hBX := tensorProdATwoAOne_mem_aotci hQ hX
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  obtain ⟨l, k, q, h, D, hfo, hl, hy, hq, hyN, hh, hk, hfirst, hje, hDN, hlt, hmin, hcase⟩ :=
    chd_struct hP hQ hc hm0 hprt
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hdt := hTS.dep_mem_omega ht
  have hls : l ∈ succ (depOf P t) := mem_succ_of_mem hl
  obtain ⟨htl, hdtl⟩ := hTS.anc_mem_nd ht hls
  change ancOf P t l ∈ ndOf P at htl
  change depOf P (ancOf P t l) = l at hdtl
  have hsf := isFunction_tensorProdTwoAOneSeq P !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ)
  have hsfC := isFunction_tensorProdTwoAOneSeq P !(tC, tauEmb Q (aoc VC) W (aoc (uc tC)) ψC σC)
  have hlo : Ordinal l := ordinal_of_mem (ordinal_of_mem ordinal_omega hdt) hl
  have hil (i : M) (hi : i ∈ l) : i ∈ depOf P t := (ordinal_of_mem ordinal_omega hdt).transitive _
      hl hi
  rcases hcase with ⟨hCe, -, -⟩ | hCe
  · rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hCe
    obtain ⟨rfl, rfl, rfl⟩ := hCe
    rw [aoc_iniSeg] at hσC hagr hsfC ⊢
    have hσ1 := embChg_val_one_isFunction hσ
    obtain ⟨-, hsubl⟩ := uc_ancOf_rel hP ht hls
    have hUl := uc_mem_stduoci_of_mem_otci_two hP htl
    have hdl : dom (sig (uc (ancOf P t l))) = l := by rw [dom_sig_uc_eq_depOf hP htl, hdtl]
    have hval (i : M) (hi : i ∈ l) :
        tensorProdTwoAOneSeq P !(ancOf P t l, tauEmb Q (iniSegAoc V (⋃₀ dom (sig V))) W
          (aoc (uc (ancOf P t l))) ψC (embRestrict (uc (ancOf P t l)) σ)) ﹫ i =
        tensorProdTwoAOneSeq P !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ) ﹫ i := by
      have hnd := (siglvl_eq_one hUl (by rw [hdl]; exact hi)).right
      have hσl : (embRestrict (uc (ancOf P t l)) σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc (ancOf P t l)) i =
          (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i := by
        rw [embRestrict_val _ _ natCast_one_mem_two, val_restrict _ hσ1.left hnd
          (by rw [hσ1.right]; exact hsubl.left hnd), sigdcn_anc hP ht hls hi]
      have hz := emb_val_mem (aoc_mem_aotci_of_mem_stduoci_one hUl)
        (tensorProdATwoAOne_mem_aotci hQ hX') hσC hnd
      rw [hσl] at hz
      rw [seq_tauEmb_val hP htl hσC (by rw [hdtl]; exact hi), seq_tauEmb_val hP ht hσ (hil i hi),
        hσl, pushNd_old hQ hX hX' h0 hsub hagr hz,
        ancOf_ancOf hPs ht hls (succ_mem_succ_of_mem (ordinal_omega.transitive _ hdt hl) hi)]
    unfold BKLt
    refine .inl ⟨subset_of_val_eq hsfC hsf ?_ ?_, fun he ↦ ?_⟩
    · rw [tensorProdTwoAOneSeq_dom, tensorProdTwoAOneSeq_dom, hdtl]
      exact fun i hi ↦ hil i hi
    · intro i hi
      rw [tensorProdTwoAOneSeq_dom, hdtl] at hi
      exact hval i hi
    · have hd := congrArg dom he
      rw [tensorProdTwoAOneSeq_dom, tensorProdTwoAOneSeq_dom, hdtl] at hd
      rw [hd] at hl
      exact notMem_self _ hl
  · rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hCe
    obtain ⟨rfl, rfl, rfl⟩ := hCe
    rw [aoc_iniSeg] at hσC hagr hsfC ⊢
    have hl1s : succ l ∈ succ (depOf P t) := succ_mem_succ_of_mem hdt hl
    obtain ⟨htl1, hdtl1⟩ := hTS.anc_mem_nd ht hl1s
    change ancOf P t (succ l) ∈ ndOf P at htl1
    change depOf P (ancOf P t (succ l)) = succ l at hdtl1
    have hc1 : ancOf P t (succ l) ∈ chdOf P (ancOf P t l) := hTS.anc_succ_mem_chd ht hl
    obtain ⟨hcc, -, hccs, -, -, -⟩ :=
      ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hP htl hc1
    set tc := ctChd P (ancOf P t l) (aoc (uc (ancOf P t (succ l)))) with htcdef
    obtain ⟨hdtc, hanctc⟩ := ancOf_eq_of_mem_chdOf hPs hcc
    rw [hdtl] at hdtc hanctc
    have hUl1 := uc_mem_stduoci_of_mem_otci_two hP htl1
    have hUtc := uc_mem_stduoci_of_mem_otci_two hP htC
    have hsfl1 := (uociCond_of_mem_stduoci_one hUl1).right.right.right.left.left
    have hsd (i : M) (hi : i ∈ succ l) : sigdcn (uc tc) i = sigdcn (uc t) i := by
      rw [← sigdcn_anc hP ht hl1s hi, sigdcn, sigdcn, hccs]
    have hσe := (mem_aotciEmbSet_iff.mp hσ).right
    have hσ1 := embChg_val_one_isFunction hσ
    have hσ0 : (∅ : M) ∈ dom σ := by
      rw [hσe.dom_eq]; exact mem_succ_of_mem empty_mem_natCast_one
    have hlsig : l ∈ dom (sig (uc t)) := by rw [dom_sig_uc_eq_depOf hP ht]; exact hl
    have hσCv (i : M) (hi : i ∈ l) :
        (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) i =
          (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i := by
      have hi1 : i ∈ succ l := mem_succ_of_mem hi
      have hit : i ∈ dom (sig (uc t)) := by rw [dom_sig_uc_eq_depOf hP ht]; exact hil i hi
      have hnd' : sigdcn (uc t) i ∈ ndOf (aoc (uc (ancOf P t (succ l))) ﹫ ((1 : ℕ) : M)) := by
        have hi1' : i ∈ dom (sig (uc (ancOf P t (succ l)))) := by
          rw [dom_sig_uc_eq_depOf hP htl1, hdtl1]; exact hi1
        have h'' := (siglvl_eq_one hUl1 hi1').right
        rwa [sigdcn_anc hP ht hl1s hi1] at h''
      have hne : sigdcn (uc t) i ≠ sigdcn (uc t) l := by
        intro h''
        have := congrArg lbl h''
        rw [lbl_sigdcn hUt hit, lbl_sigdcn hUt hlsig] at this
        rw [this] at hi
        exact notMem_self _ hi
      rw [hsd i hi1, embUpd_val_one_of_ne hσe.isFunction hσ0 hσ1.left
        (by rw [hσ1.right]; exact (siglvl_eq_one hUt hit).right) hnd' hne]
    have hσCl : (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D ﹫ ((1 : ℕ) : M)) ﹫
        sigdcn (uc tc) l = D := by
      rw [hsd l (mem_succ_self l), embUpd_val_one hσ]
      exact val_update_self (hσ1.left.restrict _) _ _
    have hBX'1 := tensorProdATwoAOne_mem_aotci hQ hX'
    have hAtc := aoc_mem_aotci_of_mem_stduoci_one hUtc
    have hzold (i : M) (hi : i ∈ succ l) :
        (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) i ∈
          ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) :=
      emb_val_mem hAtc hBX'1 hσC (siglvl_eq_one hUtc
        (by rw [dom_sig_uc_eq_depOf hP htC, hdtc]; exact hi)).right
    have hval (i : M) (hi : i ∈ l) :
        tensorProdTwoAOneSeq P !(tc, tauEmb Q (iniSegAoc V (⋃₀ dom (sig V))) W (aoc (uc tc)) ψC
          (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D)) ﹫ i =
        tensorProdTwoAOneSeq P !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ) ﹫ i := by
      have hz := hzold i (mem_succ_of_mem hi)
      rw [hσCv i hi] at hz
      have hsi : succ i ∈ succ l := succ_mem_succ_of_mem (ordinal_omega.transitive _ hdt hl) hi
      rw [seq_tauEmb_val hP htC hσC (by rw [hdtc]; exact mem_succ_of_mem hi),
        seq_tauEmb_val hP ht hσ (hil i hi), hσCv i hi, pushNd_old hQ hX hX' h0 hsub hagr hz,
        ← ancOf_ancOf hPs htC (by rw [hdtc]; exact mem_succ_of_mem (mem_succ_self l)) hsi,
        hanctc, ancOf_ancOf hPs ht hls hsi]
    unfold BKLt
    right
    refine ⟨l, by rw [tensorProdTwoAOneSeq_dom]; exact hl,
      by rw [tensorProdTwoAOneSeq_dom, hdtc]; exact mem_succ_self l, ?_, ?_⟩
    · have hks : l ⊆ dom (tensorProdTwoAOneSeq P !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ)) := by
        rw [tensorProdTwoAOneSeq_dom]; exact fun i hi ↦ hil i hi
      have hks' : l ⊆ dom (tensorProdTwoAOneSeq P !(tc, tauEmb Q (iniSegAoc V (⋃₀ dom (sig V))) W
          (aoc (uc tc)) ψC (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D))) := by
        rw [tensorProdTwoAOneSeq_dom, hdtc]; exact fun i hi ↦ mem_succ_of_mem hi
      exact hsf.restrict_eq_restrict hsfC hks hks' fun i hi ↦ (hval i hi).symm
    · have hDold := hzold l (mem_succ_self l)
      rw [hσCl] at hDold
      rw [seq_tauEmb_val hP ht hσ hl,
          seq_tauEmb_val hP htC hσC (by rw [hdtc]; exact mem_succ_self l),
        hσCl, pushNd_old hQ hX hX' h0 hsub hagr hDold, hy, tensorProdTwoAOneCoordOdr,
        rel_lexProd_iff]
      have hyB : !(dctUZero, !(q, h)) ∈ ndOf (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)) :=
        (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX).mpr (.inr hyN)
      have hDB : D ∈ ndOf (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)) :=
        (isSubOne_tensorProdATwoAOne hQ hX hX' h0 hsub).left hDold
      have hBW1 := val_mem_otci_of_mem_aotci hBW (mem_succ_self _)
      have hm1 : relabelOne trvAZero (pushNd Q (aoc V) W ψ !(dctUZero, !(q, h))) ∈
          ndOf (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)) := by
        rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hBW1]
        exact ⟨_, pushNd_mem hQ hX hW hψ hyB, rfl⟩
      have hm2 : relabelOne trvAZero (pushNd Q (aoc V) W ψ D) ∈
          ndOf (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)) := by
        rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hBW1]
        exact ⟨_, pushNd_mem hQ hX hW hψ hDB, rfl⟩
      have htct : ancOf P tc (succ l) = tc := by rw [← hdtc]; exact hTS.anc_dep htC
      rw [htct]
      refine ⟨⟨hm1, (hTS.anc_mem_nd ht hl1s).left⟩, ⟨hm2, htC⟩, .inl ?_⟩
      exact (rel_tgt_relabel_iff hBW (pushNd_mem hQ hX hW hψ hyB)
        (pushNd_mem hQ hX hW hψ hDB)).mpr ((pushNd_odr_iff hQ hX hW hψ hyB hDB).mp hlt)

end ChdPrtOrder

section SblCt

/-- Nothing is below a continuous node in the sibling order -/
theorem not_sbl_lt_of_ctp_eq_ct {P p c x : M} (hP : P ∈ otci ((2 : ℕ) : M)) (hp : p ∈ ndOf P)
    (hc : c ∈ chdOf P p) (hct : ctp (uc c) = ct) : ¬ x [sblOdrOf P] c := by
  have hTs : IsSLOT P := (otciCond_two hP).left
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hTs
  obtain ⟨-, -, -, -, hchd⟩ := otciCond_two hP
  obtain ⟨q, hq, hqk⟩ := ((hchd p hp).left (aoc (uc c))).mp ⟨c, hc, rfl⟩
  have hkey : aoc q = left c ﹫ ∅ := hqk
  have hcB : c ∈ losSet (chdlosOf P p ﹫ aoc q) := by
    rw [hkey]; exact (mem_losSet_chdlosOf_iff hTs hp hc c).mpr ⟨hc, rfl⟩
  have hl := ((hchd p hp).right.left q hq c hcB).right.mpr hct
  intro h
  rw [rel_sblOdrOf_iff hTs] at h
  obtain ⟨hx, -, heq, hrel⟩ := h
  have hlc : ndlosOf P c = chdlosOf P p ﹫ aoc q := by
    rw [ndlosOf_eq_chdlosOf hTs hp hc, hkey]
  have hxB : x ∈ losSet (chdlosOf P p ﹫ aoc q) := by
    rw [← hlc, ← heq]
    exact hS.mem_losSet_ndlos hx
  rw [heq, hlc] at hrel
  exact hl.right x hxB hrel

end SblCt

section Gap

theorem mem_of_subset_of_ne_ordinal {a b : M} (ha : Ordinal a) (hb : Ordinal b) (h : a ⊆ b)
    (hne : a ≠ b) : a ∈ b := by
  rcases olt_trichotomy ha hb with h' | h' | h'
  · exact h'.right.right
  · exact (hne h').elim
  · exact (notMem_self _ (h h'.right.right)).elim

variable {P Q W : M}

/-- The gap property: an image node `B` built from the old entries of the parent `C` of `c` that
is below the image of `C` is below the image of `c` -/
theorem bkLt_isoUp_chd_of_old (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {V t σ VC tC σC ψ ψC : M}
    (hc : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q) (hm0 : ⋃₀ dom (sig V) ≠ ∅)
    (hprt : tensorProdTwoTwoPrt P Q !(V, !(t, σ)) = !(VC, !(tC, σC)))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W))
    (hagr : ∀ v ∈ ndOf (aoc VC ﹫ ((1 : ℕ) : M)),
      (ψC ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ ﹫ ((1 : ℕ) : M)) ﹫ v)
    {tB τB : M} (htB : tB ∈ ndOf P)
    (hτB : τB ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc tB))
      (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W)))
    (hold : ∀ i ∈ depOf P tB, ∃ b ∈ ndOf (tensorProdATwoAOne Q (aoc VC) ﹫ ((1 : ℕ) : M)),
      (τB ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tB) i = relabelOne trvAZero (pushNd Q (aoc VC) W ψC b))
    (hlt : BKLt (tensorProdTwoAOneCoordOdr P (tensorProdATwoAOne Q W))
      (tensorProdTwoAOneSeq P !(tB, τB))
      (tensorProdTwoAOneSeq P !(tC, tauEmb Q (aoc VC) W (aoc (uc tC)) ψC σC))) :
    BKLt (tensorProdTwoAOneCoordOdr P (tensorProdATwoAOne Q W))
      (tensorProdTwoAOneSeq P !(tB, τB))
      (tensorProdTwoAOneSeq P !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ)) := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  have hPs : IsSLOT P := (otciCond_two hP).left
  have hCN := tensorProdTwoTwoPrt_mem hP hQ hc (by
    rw [uc_orderedPair]; exact fun h' ↦ hm0 (by rw [h', sUnion_empty]))
  rw [hprt] at hCN
  have hCN' := hCN
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hCN'
  obtain ⟨htC, -, hσC, -⟩ := hCN'
  have hc' := hc
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hc'
  obtain ⟨ht, hV, hσ, -⟩ := hc'
  have hdV : dom (sig V) ≠ ∅ := fun h' ↦ hm0 (by rw [h', sUnion_empty])
  have hm : ⋃₀ dom (sig V) ∈ dom (sig V) :=
    (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV) hdV).right.left
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, -⟩ := lastSeg_facts hV hm
  have hBX := tensorProdATwoAOne_mem_aotci hQ hX
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  have hT := tensorProdTwoAOneTgt_mem hBW
  have hBX'1 := tensorProdATwoAOne_mem_aotci hQ hX'
  have hsubB := isSubOne_tensorProdATwoAOne hQ hX hX' h0 hsub
  have hRX := (rtlosOf_of_mem_otci_one (val_mem_otci_of_mem_aotci hBX (mem_succ_self _))).left
  obtain ⟨l, k, q, h, D, hfo, hl, hy, hq, hyN, hh, hk, hfirst, hje, hDN, hylt, hmin, hcase⟩ :=
    chd_struct hP hQ hc hm0 hprt
  have hVC : VC = iniSeg V (⋃₀ dom (sig V)) := by
    rcases hcase with ⟨h', -⟩ | h' <;>
      (rw [orderedPair_eq_orderedPair_iff] at h'; exact h'.left)
  subst hVC
  rw [aoc_iniSeg] at hagr hold hlt hσC
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hyB : !(dctUZero, !(q, h)) ∈ ndOf (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)) :=
    (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX).mpr (.inr hyN)
  have hyold := not_mem_lastSeg_of_sigImg_eq hQ hV hm hyN
    (by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hk) hje
  have hDB' : D ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) :=
    (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX').mpr (.inr hDN)
  have hDB := hsubB.left hDB'
  -- an old node below `D` is below `y`
  have hkey {b : M} (hb : b ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫
      ((1 : ℕ) : M)))
      (hbD : (relabelOne trvAZero (pushNd Q (iniSegAoc V (⋃₀ dom (sig V))) W ψC b))
        [odrOne (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
        (relabelOne trvAZero (pushNd Q (iniSegAoc V (⋃₀ dom (sig V))) W ψC D))) :
      (relabelOne trvAZero (pushNd Q (iniSegAoc V (⋃₀ dom (sig V))) W ψC b))
        [odrOne (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
        (relabelOne trvAZero (pushNd Q (aoc V) W ψ !(dctUZero, !(q, h)))) := by
    have hbB := hsubB.left hb
    rw [pushNd_old hQ hX hX' h0 hsub hagr hb, pushNd_old hQ hX hX' h0 hsub hagr hDB',
      rel_tgt_relabel_iff hBW (pushNd_mem hQ hX hW hψ hbB) (pushNd_mem hQ hX hW hψ hDB),
      ← pushNd_odr_iff hQ hX hW hψ hbB hDB] at hbD
    rw [pushNd_old hQ hX hX' h0 hsub hagr hb,
      rel_tgt_relabel_iff hBW (pushNd_mem hQ hX hW hψ hbB) (pushNd_mem hQ hX hW hψ hyB),
      ← pushNd_odr_iff hQ hX hW hψ hbB hyB]
    rcases hRX.isTrichotomousOn _ hbB _ hyB with h' | h' | h'
    · exact h'
    · exact (hyold (h' ▸ hb)).elim
    · rcases hmin _ hb h' with h'' | h''
      · rw [h''] at hbD; exact (hRX.irrefl _ hbD).elim
      · exact (hRX.asymm hbD h'').elim
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hAt := aoc_mem_aotci_of_mem_stduoci_one hUt
  have hdt := hTS.dep_mem_omega ht
  have hls : l ∈ succ (depOf P t) := mem_succ_of_mem hl
  obtain ⟨htl, hdtl⟩ := hTS.anc_mem_nd ht hls
  change ancOf P t l ∈ ndOf P at htl
  change depOf P (ancOf P t l) = l at hdtl
  have hlo : Ordinal l := ordinal_of_mem (ordinal_of_mem ordinal_omega hdt) hl
  have hil (i : M) (hi : i ∈ l) : i ∈ depOf P t :=
    (ordinal_of_mem ordinal_omega hdt).transitive _ hl hi
  have hdtB := hTS.dep_mem_omega htB
  set sB := tensorProdTwoAOneSeq P !(tB, τB) with hsBdef
  set sc := tensorProdTwoAOneSeq P !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ) with hscdef
  set sC := tensorProdTwoAOneSeq P
    !(tC, tauEmb Q (iniSegAoc V (⋃₀ dom (sig V))) W (aoc (uc tC)) ψC σC) with hsCdef
  have hsBf : IsFunction sB := isFunction_tensorProdTwoAOneSeq _ _
  have hscf : IsFunction sc := isFunction_tensorProdTwoAOneSeq _ _
  have hsCf : IsFunction sC := isFunction_tensorProdTwoAOneSeq _ _
  have hdsB : dom sB = depOf P tB := tensorProdTwoAOneSeq_dom _ _
  have hdsc : dom sc = depOf P t := tensorProdTwoAOneSeq_dom _ _
  have hdsC : dom sC = depOf P tC := tensorProdTwoAOneSeq_dom _ _
  have hsBv (i : M) (hi : i ∈ depOf P tB) :
      sB ﹫ i = !((τB ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tB) i, ancOf P tB (succ i)) :=
    tensorProdTwoAOneSeq_val hP htB hi
  have hmemB (i : M) (hi : i ∈ depOf P tB) := tensorProdTwoAOneSeq_val_mem hP htB hτB hi
  have hmemc (i : M) (hi : i ∈ depOf P t) :=
    tensorProdTwoAOneSeq_val_mem hP ht (tauEmb_mem hQ hX hW hAt hσ hψ (W := W)) hi
  have hbk (d : M) (hdB : d ∈ depOf P tB) (hdc : d ∈ depOf P t)
      (hres : ∀ i ∈ d, sB ﹫ i = sc ﹫ i)
      (hrel : (sB ﹫ d) [tensorProdTwoAOneCoordOdr P (tensorProdATwoAOne Q W)] (sc ﹫ d)) :
      BKLt (tensorProdTwoAOneCoordOdr P (tensorProdATwoAOne Q W)) sB sc := by
    have hdo := ordinal_of_mem (ordinal_of_mem ordinal_omega hdtB) hdB
    refine .inr ⟨d, by rw [hdsB]; exact hdB, by rw [hdsc]; exact hdc,
      hsBf.restrict_eq_restrict hscf (fun i hi ↦ by rw [hdsB]; exact
        (ordinal_of_mem ordinal_omega hdtB).transitive _ hdB hi)
        (fun i hi ↦ by rw [hdsc]; exact (ordinal_of_mem ordinal_omega hdt).transitive _ hdc hi)
        hres, hrel⟩
  -- the coordinate `l`, given an old image below `D`
  have hcoord {b : M} (hlB : l ∈ depOf P tB)
      (hb : b ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
      (hbe : (τB ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tB) l =
        relabelOne trvAZero (pushNd Q (iniSegAoc V (⋃₀ dom (sig V))) W ψC b))
      (hbD : (relabelOne trvAZero (pushNd Q (iniSegAoc V (⋃₀ dom (sig V))) W ψC b))
        [odrOne (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M))]
        (relabelOne trvAZero (pushNd Q (iniSegAoc V (⋃₀ dom (sig V))) W ψC D))) :
      (sB ﹫ l) [tensorProdTwoAOneCoordOdr P (tensorProdATwoAOne Q W)] (sc ﹫ l) := by
    have hmB := hmemB l hlB
    have hmc := hmemc l hl
    rw [hsBv l hlB, hbe] at hmB ⊢
    rw [seq_tauEmb_val hP ht hσ hl, hy] at hmc
    rw [hscdef, seq_tauEmb_val hP ht hσ hl, hy]
    rw [pair_mem_sprod_iff] at hmB hmc
    rw [tensorProdTwoAOneCoordOdr, rel_lexProd_iff]
    exact ⟨hmB, hmc, .inl (hkey hb hbD)⟩
  rcases hcase with ⟨hCe, hlv, hD⟩ | hCe
  · -- case 1: the parent is `(V | m, (t_l, σ ↾ t_l))`
    rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hCe
    obtain ⟨-, rfl, rfl⟩ := hCe
    have hσ1 := embChg_val_one_isFunction hσ
    obtain ⟨-, hsubl⟩ := uc_ancOf_rel hP ht hls
    have hUl := uc_mem_stduoci_of_mem_otci_two hP htl
    have hdl : dom (sig (uc (ancOf P t l))) = l := by rw [dom_sig_uc_eq_depOf hP htl, hdtl]
    have hagree (i : M) (hi : i ∈ l) : sC ﹫ i = sc ﹫ i := by
      have hnd := (siglvl_eq_one hUl (by rw [hdl]; exact hi)).right
      have hσl : (embRestrict (uc (ancOf P t l)) σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc (ancOf P t l)) i =
          (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i := by
        rw [embRestrict_val _ _ natCast_one_mem_two, val_restrict _ hσ1.left hnd
          (by rw [hσ1.right]; exact hsubl.left hnd), sigdcn_anc hP ht hls hi]
      have hz := emb_val_mem (aoc_mem_aotci_of_mem_stduoci_one hUl) hBX'1 hσC hnd
      rw [hσl] at hz
      rw [hsCdef, hscdef, seq_tauEmb_val hP htl hσC (by rw [hdtl]; exact hi),
        seq_tauEmb_val hP ht hσ (hil i hi), hσl, pushNd_old hQ hX hX' h0 hsub hagr hz,
        ancOf_ancOf hPs ht hls (succ_mem_succ_of_mem (ordinal_omega.transitive _ hdt hl) hi)]
    have hdsC' : dom sC = l := by rw [hdsC, hdtl]
    unfold BKLt at hlt
    rcases hlt with ⟨hsub', hne'⟩ | ⟨d, hdB, hdC, hres, hrel⟩
    · have hlsB : l ⊆ depOf P tB := by rw [← hdsC', ← hdsB]; exact dom_mono hsub'
      have hlne : l ≠ depOf P tB := by
        intro he
        apply hne'
        refine hsCf.ext hsBf (by rw [hdsC', hdsB, he]) fun i hi ↦ ?_
        exact (val_eq_of_subset hsBf hsCf hsub' hi).symm
      have hlB : l ∈ depOf P tB :=
        mem_of_subset_of_ne_ordinal hlo (ordinal_of_mem ordinal_omega hdtB) hlsB hlne
      have hl0 : l ≠ ∅ := by
        intro hl0
        have hs : sig (iniSeg V (⋃₀ dom (sig V))) ≠ ∅ := by
          intro h''
          have hd := dom_sig_iniSeg hV hm
          rw [h'', dom_empty] at hd
          exact hm0 hd.symm
        refine not_mem_rtOf_of_sig_ne_empty hP hQ hCN hs (TreeStructure.mem_rt_iff.mpr ⟨htl, ?_⟩)
        change depOf P (ancOf P t l) = ∅
        rw [hdtl, hl0]
      obtain ⟨-, hlm, hlsucc⟩ := sUnion_mem_of_ne_empty (ordinal_omega.transitive _ hdt hl) hl0
      have hu : sB ﹫ ⋃₀ l = sC ﹫ ⋃₀ l :=
        val_eq_of_subset hsBf hsCf hsub' (by rw [hdsC']; exact hlm)
      rw [hsBv _ (hlsB hlm), hsCdef, seq_tauEmb_val hP htl hσC (by rw [hdtl]; exact hlm),
        orderedPair_eq_orderedPair_iff, ← hlsucc] at hu
      have hancB : ancOf P tB l = ancOf P t l := by
        rw [hu.right]
        have h'' := hTS.anc_dep htl
        change ancOf P (ancOf P t l) (depOf P (ancOf P t l)) = ancOf P t l at h''
        rwa [hdtl] at h''
      obtain ⟨-, ⟨i0, hi0, hr⟩, hyr⟩ := ucf_anc_rel hP htB hlB hl0 hT hτB
      have hr' : ucfdcn (uc (ancOf P t l)) = sigdcn (uc tB) i0 := by rw [← hancB]; exact hr
      rw [hancB, hr'] at hyr
      have hu0 : sB ﹫ i0 = sC ﹫ i0 :=
        val_eq_of_subset hsBf hsCf hsub' (by rw [hdsC']; exact hi0)
      rw [hsBv _ (hlsB hi0), hsCdef, seq_tauEmb_val hP htl hσC (by rw [hdtl]; exact hi0),
        orderedPair_eq_orderedPair_iff] at hu0
      rw [hu0.left] at hyr
      have hsd0 : sigdcn (uc (ancOf P t l)) i0 = sigdcn (uc tB) i0 := by
        rw [← hancB]; exact sigdcn_anc hP htB (mem_succ_of_mem hlB) hi0
      have hσD : (embRestrict (uc (ancOf P t l)) σ ﹫ ((1 : ℕ) : M)) ﹫
          sigdcn (uc (ancOf P t l)) i0 = D := by
        have hnd := (siglvl_eq_one hUl (by rw [hdl]; exact hi0)).right
        rw [embRestrict_val _ _ natCast_one_mem_two, val_restrict _ hσ1.left hnd
          (by rw [hσ1.right]; exact hsubl.left hnd), hD, hsd0, hr']
      rw [hσD] at hyr
      obtain ⟨b, hb, hbe⟩ := hold l hlB
      rw [hbe] at hyr
      refine hbk l hlB hl (fun i hi ↦ ?_) (hcoord hlB hb hbe hyr)
      rw [val_eq_of_subset hsBf hsCf hsub' (by rw [hdsC']; exact hi), hagree i hi]
    · rw [hdsC'] at hdC
      refine hbk d (by rw [← hdsB]; exact hdB) (hil d hdC) (fun i hi ↦ ?_) ?_
      · rw [val_eq_of_restrict_eq hsBf hsCf hres hi
          ((ordinal_of_mem ordinal_omega (by rw [hdsB]; exact hdtB)).transitive _ hdB hi)
          (by rw [hdsC']; exact hlo.transitive _ hdC hi), hagree i (hlo.transitive _ hdC hi)]
      · rw [← hagree d hdC]; exact hrel
  · -- case 2: the parent is `(V | m, (t_l⁺, σ[w_l ↦ D]))`
    rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hCe
    obtain ⟨-, rfl, rfl⟩ := hCe
    have hl1s : succ l ∈ succ (depOf P t) := succ_mem_succ_of_mem hdt hl
    obtain ⟨htl1, hdtl1⟩ := hTS.anc_mem_nd ht hl1s
    change ancOf P t (succ l) ∈ ndOf P at htl1
    change depOf P (ancOf P t (succ l)) = succ l at hdtl1
    have hc1 : ancOf P t (succ l) ∈ chdOf P (ancOf P t l) := hTS.anc_succ_mem_chd ht hl
    obtain ⟨hcc, -, hccs, hcct, -, -⟩ :=
      ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hP htl hc1
    set tc := ctChd P (ancOf P t l) (aoc (uc (ancOf P t (succ l)))) with htcdef
    obtain ⟨hdtc, hanctc⟩ := ancOf_eq_of_mem_chdOf hPs hcc
    rw [hdtl] at hdtc hanctc
    have hUl1 := uc_mem_stduoci_of_mem_otci_two hP htl1
    have hUtc := uc_mem_stduoci_of_mem_otci_two hP htC
    have hsd (i : M) (hi : i ∈ succ l) : sigdcn (uc tc) i = sigdcn (uc t) i := by
      rw [← sigdcn_anc hP ht hl1s hi, sigdcn, sigdcn, hccs]
    have hσe := (mem_aotciEmbSet_iff.mp hσ).right
    have hσ1 := embChg_val_one_isFunction hσ
    have hσ0 : (∅ : M) ∈ dom σ := by
      rw [hσe.dom_eq]; exact mem_succ_of_mem empty_mem_natCast_one
    have hlsig : l ∈ dom (sig (uc t)) := by rw [dom_sig_uc_eq_depOf hP ht]; exact hl
    have hσCv (i : M) (hi : i ∈ l) :
        (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) i =
          (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i := by
      have hi1 : i ∈ succ l := mem_succ_of_mem hi
      have hit : i ∈ dom (sig (uc t)) := by rw [dom_sig_uc_eq_depOf hP ht]; exact hil i hi
      have hnd' : sigdcn (uc t) i ∈ ndOf (aoc (uc (ancOf P t (succ l))) ﹫ ((1 : ℕ) : M)) := by
        have h'' := (siglvl_eq_one hUl1
          (by rw [dom_sig_uc_eq_depOf hP htl1, hdtl1]; exact hi1)).right
        rwa [sigdcn_anc hP ht hl1s hi1] at h''
      have hne : sigdcn (uc t) i ≠ sigdcn (uc t) l := by
        intro h''
        have := congrArg lbl h''
        rw [lbl_sigdcn hUt hit, lbl_sigdcn hUt hlsig] at this
        rw [this] at hi
        exact notMem_self _ hi
      rw [hsd i hi1, embUpd_val_one_of_ne hσe.isFunction hσ0 hσ1.left
        (by rw [hσ1.right]; exact (siglvl_eq_one hUt hit).right) hnd' hne]
    have hσCl : (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D ﹫ ((1 : ℕ) : M)) ﹫
        sigdcn (uc tc) l = D := by
      rw [hsd l (mem_succ_self l), embUpd_val_one hσ]
      exact val_update_self (hσ1.left.restrict _) _ _
    have hAtc := aoc_mem_aotci_of_mem_stduoci_one hUtc
    have hzold (i : M) (hi : i ∈ succ l) :
        (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) i ∈
          ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) :=
      emb_val_mem hAtc hBX'1 hσC (siglvl_eq_one hUtc
        (by rw [dom_sig_uc_eq_depOf hP htC, hdtc]; exact hi)).right
    have hagree (i : M) (hi : i ∈ l) : sC ﹫ i = sc ﹫ i := by
      have hz := hzold i (mem_succ_of_mem hi)
      rw [hσCv i hi] at hz
      have hsi : succ i ∈ succ l := succ_mem_succ_of_mem (ordinal_omega.transitive _ hdt hl) hi
      rw [hsCdef, hscdef, seq_tauEmb_val hP htC hσC (by rw [hdtc]; exact mem_succ_of_mem hi),
        seq_tauEmb_val hP ht hσ (hil i hi), hσCv i hi, pushNd_old hQ hX hX' h0 hsub hagr hz,
        ← ancOf_ancOf hPs htC (by rw [hdtc]; exact mem_succ_of_mem (mem_succ_self l)) hsi,
        hanctc, ancOf_ancOf hPs ht hls hsi]
    have hdsC' : dom sC = succ l := by rw [hdsC, hdtc]
    have htct : ancOf P tc (succ l) = tc := by rw [← hdtc]; exact hTS.anc_dep htC
    have hsCl : sC ﹫ l = !(relabelOne trvAZero (pushNd Q (iniSegAoc V (⋃₀ dom (sig V))) W ψC D),
        tc) := by
      rw [hsCdef, seq_tauEmb_val hP htC hσC (by rw [hdtc]; exact mem_succ_self l), hσCl, htct]
    unfold BKLt at hlt
    rcases hlt with ⟨hsub', hne'⟩ | ⟨d, hdB, hdC, hres, hrel⟩
    · exfalso
      have hlsB : succ l ⊆ depOf P tB := by rw [← hdsC', ← hdsB]; exact dom_mono hsub'
      have hlne : succ l ≠ depOf P tB := by
        intro he
        apply hne'
        refine hsCf.ext hsBf (by rw [hdsC', hdsB, he]) fun i hi ↦ ?_
        exact (val_eq_of_subset hsBf hsCf hsub' hi).symm
      have hlB : succ l ∈ depOf P tB :=
        mem_of_subset_of_ne_ordinal (ordinal_of_mem ordinal_omega (succ_mem_omega
          (ordinal_omega.transitive _ hdt hl))) (ordinal_of_mem ordinal_omega hdtB) hlsB hlne
      have hu : sB ﹫ l = sC ﹫ l :=
        val_eq_of_subset hsBf hsCf hsub' (by rw [hdsC']; exact mem_succ_self l)
      rw [hsBv _ (hlsB (mem_succ_self l)), hsCl, orderedPair_eq_orderedPair_iff] at hu
      have hchd := hTS.anc_succ_mem_chd htB hlB
      change ancOf P tB (succ (succ l)) ∈ chdOf P (ancOf P tB (succ l)) at hchd
      rw [hu.right, chdOf_eq_empty_of_ctp_eq_ct (natCast_mem_omega 2) hP htC hcct] at hchd
      exact notin_empty _ hchd
    · rw [hdsC'] at hdC
      have hdB' : d ∈ depOf P tB := by rw [← hdsB]; exact hdB
      rcases mem_or_eq_of_mem_succ hdC with hdl | hdl
      · refine hbk d hdB' (hil d hdl) (fun i hi ↦ ?_) ?_
        · rw [val_eq_of_restrict_eq hsBf hsCf hres hi
            ((ordinal_of_mem ordinal_omega (by rw [hdsB]; exact hdtB)).transitive _ hdB hi)
            (by rw [hdsC']; exact mem_succ_of_mem (hlo.transitive _ hdl hi)),
            hagree i (hlo.transitive _ hdl hi)]
        · rw [← hagree d hdl]; exact hrel
      · rw [hdl] at hdB' hres hrel
        have hrel' := hrel
        rw [hsBv l hdB', hsCl, tensorProdTwoAOneCoordOdr, rel_lexProd_iff] at hrel'
        obtain ⟨-, -, hr | ⟨-, hsb⟩⟩ := hrel'
        · obtain ⟨b, hb, hbe⟩ := hold l hdB'
          rw [hbe] at hr
          refine hbk l hdB' hl (fun i hi ↦ ?_) (hcoord hdB' hb hbe hr)
          rw [val_eq_of_restrict_eq hsBf hsCf hres hi
            (by rw [hdsB]; exact (ordinal_of_mem ordinal_omega hdtB).transitive _ hdB' hi)
            (by rw [hdsC']; exact mem_succ_of_mem hi), hagree i hi]
        · exact (not_sbl_lt_of_ctp_eq_ct hP htl hcc hcct hsb).elim

end Gap

section QPrefix

variable {Q V : M}

/-- Two new nodes with the same nearest old node above them first contain the new entry at the
same position, and agree before it -/
theorem seq_prefix_of_succ_eq (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) {q h k q' h' k' D : M}
    (hq : q ∈ ndOf (Q ﹫ 2)) (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)))
    (hk : k ∈ depOf (Q ﹫ 2) q)
    (hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V)))
    (hje : sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V)))
    (hq' : q' ∈ ndOf (Q ﹫ 2))
    (hy' : !(dctUZero, !(q', h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hh' : h' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q')) (tensorProdTwoAOneTgt (aoc V)))
    (hk' : k' ∈ depOf (Q ﹫ 2) q')
    (hfirst' : ∀ i ∈ k', sigImg (aoc V) q' h' i ≠ sigdcn V (⋃₀ dom (sig V)))
    (hje' : sigImg (aoc V) q' h' k' = sigdcn V (⋃₀ dom (sig V)))
    (hD : D ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)))
    (hyD : !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] D)
    (hmin : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
      !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
        z = D ∨ D [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z)
    (hyD' : !(dctUZero, !(q', h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] D)
    (hmin' : ∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
      !(dctUZero, !(q', h')) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
        z = D ∨ D [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) :
    k = k' ∧ tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h) ↾ k = tensorProdTwoAOneSeq (Q ﹫ 2) !(q',
        h') ↾ k := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  obtain ⟨w, -, -, hc⟩ := eq_succ_of_isLeastAbove hQ hV hm hq hy hh hk hfirst hje hD hyD hmin
  obtain ⟨w', -, -, hc'⟩ := eq_succ_of_isLeastAbove hQ hV hm hq' hy' hh' hk' hfirst' hje' hD hyD'
    hmin'
  have hdq := hTS.dep_mem_omega hq
  have hdq' := hTS.dep_mem_omega hq'
  have hks : k ∈ succ (depOf (Q ﹫ 2) q) := mem_succ_of_mem hk
  have hks' : k' ∈ succ (depOf (Q ﹫ 2) q') := mem_succ_of_mem hk'
  -- the node of `E1` has a child, that of `E2` is continuous
  have hdct {r j : M} (hr : r ∈ ndOf (Q ﹫ 2)) (hj : j ∈ depOf (Q ﹫ 2) r) :
      ctp (uc (ancOf (Q ﹫ 2) r j)) ≠ ct := by
    intro hct
    have hc1 := hTS.anc_succ_mem_chd hr hj
    change ancOf (Q ﹫ 2) r (succ j) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) r j) at hc1
    have hrj : ancOf (Q ﹫ 2) r j ∈ ndOf (Q ﹫ 2) := (hTS.anc_mem_nd hr (mem_succ_of_mem hj)).left
    rw [chdOf_eq_empty_of_ctp_eq_ct (natCast_mem_omega 2) hQ2 hrj hct] at hc1
    exact notin_empty _ hc1
  have hct {r j : M} (hr : r ∈ ndOf (Q ﹫ 2)) (hj : j ∈ depOf (Q ﹫ 2) r) :
      ctp (uc (ctChd (Q ﹫ 2) (ancOf (Q ﹫ 2) r j) (aoc (uc (ancOf (Q ﹫ 2) r (succ j)))))) = ct :=
    (ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hQ2
      (hTS.anc_mem_nd hr (mem_succ_of_mem hj)).left (hTS.anc_succ_mem_chd hr
          hj)).right.right.right.left
  rcases hc with ⟨-, -, hE⟩ | ⟨-, hE⟩ <;> rcases hc' with ⟨-, -, hE'⟩ | ⟨-, hE'⟩
  · rw [hE, succOne, succOne, orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff]
      at hE'
    have hkk : k = k' := by
      rw [← (hTS.anc_mem_nd hq hks).right, ← (hTS.anc_mem_nd hq' hks').right]
      exact congrArg _ hE'.right.left
    subst hkk
    refine ⟨rfl, ?_⟩
    rw [← tensorProdTwoAOneSeq_embRestrict hQ2 hq hks hh,
      ← tensorProdTwoAOneSeq_embRestrict hQ2 hq' hks' hh', hE'.right.right, hE'.right.left]
  · exfalso
    rw [hE, succOne, succTwo, orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff]
      at hE'
    exact hdct hq hk (by rw [hE'.right.left]; exact hct hq' hk')
  · exfalso
    rw [hE, succOne, succTwo, orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff]
      at hE'
    exact hdct hq' hk' (by rw [← hE'.right.left]; exact hct hq hk)
  · rw [hE, succTwo, succTwo, orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff]
      at hE'
    have hqk : ancOf (Q ﹫ 2) q k ∈ ndOf (Q ﹫ 2) := (hTS.anc_mem_nd hq hks).left
    have hdqk : depOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) = k := (hTS.anc_mem_nd hq hks).right
    have hc1 : ancOf (Q ﹫ 2) q (succ k) ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q k) :=
      hTS.anc_succ_mem_chd hq hk
    have hqk' : ancOf (Q ﹫ 2) q' k' ∈ ndOf (Q ﹫ 2) := (hTS.anc_mem_nd hq' hks').left
    have hdqk' : depOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q' k') = k' := (hTS.anc_mem_nd hq' hks').right
    have hc1' : ancOf (Q ﹫ 2) q' (succ k') ∈ chdOf (Q ﹫ 2) (ancOf (Q ﹫ 2) q' k') :=
      hTS.anc_succ_mem_chd hq' hk'
    have hcc := (ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hqk hc1).left
    have hcc' := (ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hQ2 hqk' hc1').left
    have hd1 := (ancOf_eq_of_mem_chdOf (otciCond_two hQ2).left hcc).left
    have hd1' := (ancOf_eq_of_mem_chdOf (otciCond_two hQ2).left hcc').left
    rw [hdqk] at hd1
    rw [hdqk'] at hd1'
    have hkk : k = k' := by
      have h1 := hd1
      rw [hE'.right.left, hd1'] at h1
      exact (TreeStructure.eq_of_succ_eq_succ (ordinal_of_mem (ordinal_of_mem ordinal_omega hdq')
        hk') h1).symm
    subst hkk
    refine ⟨rfl, ?_⟩
    obtain ⟨-, hs1, -⟩ := tensorProdTwoAOneSeq_embUpd hQ2 hq hk hh (D := relabelOne trvAZero w)
    obtain ⟨-, hs1', -⟩ := tensorProdTwoAOneSeq_embUpd hQ2 hq' hk' hh' (D := relabelOne trvAZero w')
    rw [← hs1, ← hs1', hE'.right.right, hE'.right.left]

end QPrefix

section QCmp

variable {Q V W ψ ψ' : M}

/-- Pushing two new nodes that agree before their first new entry along embeddings that agree on
the old nodes and send the new node to `e < e'` gives nodes in order -/
theorem pushNd_lt_of_prefix (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hm : ⋃₀ dom (sig V) ∈ dom (sig V)) (hW : W ∈ aotci ((1 : ℕ) : M))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W))
    (hψ' : ψ' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W))
    (hagr : ∀ v ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)),
      (ψ ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ' ﹫ ((1 : ℕ) : M)) ﹫ v)
    (hnew : ((ψ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn V (⋃₀ dom (sig V)))
      [odrOne (tensorProdTwoAOneTgt W ﹫ ((1 : ℕ) : M))]
      ((ψ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn V (⋃₀ dom (sig V))))
    {q h k q' h' : M} (hq : q ∈ ndOf (Q ﹫ 2))
    (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)))
    (hk : k ∈ depOf (Q ﹫ 2) q)
    (hfirst : ∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V)))
    (hje : sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V)))
    (hq' : q' ∈ ndOf (Q ﹫ 2))
    (hy' : !(dctUZero, !(q', h')) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V))
    (hh' : h' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q')) (tensorProdTwoAOneTgt (aoc V)))
    (hk' : k ∈ depOf (Q ﹫ 2) q')
    (hje' : sigImg (aoc V) q' h' k = sigdcn V (⋃₀ dom (sig V)))
    (hpre : tensorProdTwoAOneSeq (Q ﹫ 2) !(q, h) ↾ k = tensorProdTwoAOneSeq (Q ﹫ 2) !(q', h') ↾ k) :
    (pushNd Q (aoc V) W ψ !(dctUZero, !(q, h)))
      [odrOne (tensorProdATwoAOne Q W ﹫ ((1 : ℕ) : M))]
      (pushNd Q (aoc V) W ψ' !(dctUZero, !(q', h'))) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hS : (SLOTreeStructure.ofM (Q ﹫ (2 : M))).IsSLOTreeStructure := (otciCond_two hQ2).left
  have hTS := hS.isTreeStructure
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  obtain ⟨-, -, -, hnd'⟩ := lastSeg_facts hV hm
  have hTW := tensorProdTwoAOneTgt_mem hW
  have hpz := pushNd_mem_of_mem hQ hX hW hψ hy
  have hpz' := pushNd_mem_of_mem hQ hX hW hψ' hy'
  rw [rel_odrOne_tensorProdATwoAOne_iff hQ hW]
  refine .inr (.inl ⟨hpz, hpz', ?_⟩)
  rw [pushNd_of_mem hy, pushNd_of_mem hy', lbl_orderedPair, lbl_orderedPair]
  have hdq := hTS.dep_mem_omega hq
  have hdq' := hTS.dep_mem_omega hq'
  have hko : Ordinal k := ordinal_of_mem (ordinal_of_mem ordinal_omega hdq) hk
  have hUq := uc_mem_stduoci_of_mem_otci_two hQ2 hq
  have hUq' := uc_mem_stduoci_of_mem_otci_two hQ2 hq'
  -- the coordinates of the pushed sequences
  have hval {p g φ : M} (hp : p ∈ ndOf (Q ﹫ 2))
      (hg : g ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) (tensorProdTwoAOneTgt (aoc V)))
      {i : M} (hi : i ∈ depOf (Q ﹫ 2) p) :
      tensorProdTwoAOneSeq (Q ﹫ 2) !(p, pushEmb W (aoc (uc p)) φ g) ﹫ i =
        !((φ ﹫ ((1 : ℕ) : M)) ﹫ sigImg (aoc V) p g i, ancOf (Q ﹫ 2) p (succ i)) := by
    have hUp := uc_mem_stduoci_of_mem_otci_two hQ2 hp
    have hip : i ∈ dom (sig (uc p)) := by rw [dom_sig_uc_eq_depOf hQ2 hp]; exact hi
    obtain ⟨hz, hze⟩ := sigImg_spec hQ2 hp hX hg hip
    rw [tensorProdTwoAOneSeq_val hQ2 hp hi, pushEmb, embMk_val_one,
      pushOne_val_of_eq hX hg (siglvl_eq_one hUp hip).right hz hze]
  have hold (i : M) (hi : i ∈ k) :
      tensorProdTwoAOneSeq (Q ﹫ 2) !(q, pushEmb W (aoc (uc q)) ψ h) ﹫ i =
        tensorProdTwoAOneSeq (Q ﹫ 2) !(q', pushEmb W (aoc (uc q')) ψ' h') ﹫ i := by
    have hiq : i ∈ depOf (Q ﹫ 2) q := (ordinal_of_mem ordinal_omega hdq).transitive _ hk hi
    have hiq' : i ∈ depOf (Q ﹫ 2) q' := (ordinal_of_mem ordinal_omega hdq').transitive _ hk' hi
    have h1 := val_eq_of_restrict_eq (isFunction_tensorProdTwoAOneSeq _ _)
      (isFunction_tensorProdTwoAOneSeq _ _) hpre hi (by rw [tensorProdTwoAOneSeq_dom]; exact hiq)
      (by rw [tensorProdTwoAOneSeq_dom]; exact hiq')
    rw [tensorProdTwoAOneSeq_val hQ2 hq hiq, tensorProdTwoAOneSeq_val hQ2 hq' hiq',
      orderedPair_eq_orderedPair_iff] at h1
    have hs1 : sigImg (aoc V) q h i = sigImg (aoc V) q' h' i := by
      unfold sigImg; rw [h1.left]
    have hz := (sigImg_spec hQ2 hq hX hh (by rw [dom_sig_uc_eq_depOf hQ2 hq]; exact hiq)).left
    rw [hval hq hh hiq, hval hq' hh' hiq', ← hs1, h1.right,
      hagr _ ((hnd' _).mpr ⟨hz, hfirst i hi⟩)]
  unfold TensorProdTwoAOneLt BKLt
  refine .inr ⟨k, by rw [tensorProdTwoAOneSeq_dom]; exact hk,
    by rw [tensorProdTwoAOneSeq_dom]; exact hk', ?_, ?_⟩
  · refine (isFunction_tensorProdTwoAOneSeq _ _).restrict_eq_restrict
      (isFunction_tensorProdTwoAOneSeq _ _) (fun i hi ↦ ?_) (fun i hi ↦ ?_) hold
    · rw [tensorProdTwoAOneSeq_dom]; exact (ordinal_of_mem ordinal_omega hdq).transitive _ hk hi
    · rw [tensorProdTwoAOneSeq_dom]; exact (ordinal_of_mem ordinal_omega hdq').transitive _ hk' hi
  · have hm1 := tensorProdTwoAOneSeq_val_mem hQ2 hq
      (embMk_pushOne_mem hX hW (aoc_mem_aotci_of_mem_stduoci_one hUq) hh hψ) hk
    have hm2 := tensorProdTwoAOneSeq_val_mem hQ2 hq'
      (embMk_pushOne_mem hX hW (aoc_mem_aotci_of_mem_stduoci_one hUq') hh' hψ') hk'
    rw [← pushEmb] at hm1 hm2
    rw [hval hq hh hk, hje, pair_mem_sprod_iff] at hm1
    rw [hval hq' hh' hk', hje', pair_mem_sprod_iff] at hm2
    rw [hval hq hh hk, hval hq' hh' hk', hje, hje', tensorProdTwoAOneCoordOdr, rel_lexProd_iff]
    exact ⟨hm1, hm2, .inl hnew⟩

end QCmp


section ChdRows

theorem ucf_one_of_ucflvl_ne_empty {U : M} (hU : U ∈ stduoci ((1 : ℕ) : M))
    (hlv : ucflvl U ≠ ∅) :
    ucflvl U = ((1 : ℕ) : M) ∧ ucfdcn U ∈ ndOf (aoc U ﹫ ((1 : ℕ) : M)) := by
  have hUu := (mem_stduoci_iff.mp hU).left
  rw [mem_uoci_iff_of_mem_omega (natCast_mem_omega 1)] at hUu
  obtain ⟨-, -, -, -, -, -, -, hucf⟩ := hUu
  have h3 : ((3 : ℕ) : M) ∈ dom U := by
    by_contra h3
    have h' : ucflvldcn U = ∅ := val_eq_empty_of_not_mem_dom h3
    apply hlv
    change left (ucflvldcn U) = ∅
    rw [h']
    exact left_empty_eq_empty
  obtain ⟨-, hlvl, hnd, -⟩ := hucf h3
  have hl : ucflvl U = ((1 : ℕ) : M) := by
    rcases mem_or_eq_of_mem_succ hlvl with h | h
    · rw [natCast_succ, natCast_zero, mem_succ_iff] at h
      rcases h with h | h
      · exact (hlv h).elim
      · simp at h
    · exact h
  rw [hl] at hnd
  exact ⟨hl, hnd⟩

variable {P Q W : M}

/-- The rows of a child `c = (V, (t, σ))` and of its parent `(V | m, (t_C, σ_C))` agree before the
cut row `l`; the parent's row `l` (if any) is the successor `D` of `y = σ(w_l)`, either at the
`ucf` of `t_C = t_l` (case 1) or at the last node of the continuous `t_C` (case 2) -/
theorem chd_rows (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    {V t σ VC tC σC ψ ψC : M}
    (hc : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q) (hm0 : ⋃₀ dom (sig V) ≠ ∅)
    (hprt : tensorProdTwoTwoPrt P Q !(V, !(t, σ)) = !(VC, !(tC, σC)))
    (hagr : ∀ v ∈ ndOf (aoc VC ﹫ ((1 : ℕ) : M)),
      (ψC ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ ﹫ ((1 : ℕ) : M)) ﹫ v) :
    VC = iniSeg V (⋃₀ dom (sig V)) ∧
    ∃ l k q h D, l ∈ depOf P t ∧ (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) l = !(dctUZero, !(q, h)) ∧
      q ∈ ndOf (Q ﹫ 2) ∧ !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) (aoc V) ∧
      h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt (aoc V)) ∧
      k ∈ depOf (Q ﹫ 2) q ∧ (∀ i ∈ k, sigImg (aoc V) q h i ≠ sigdcn V (⋃₀ dom (sig V))) ∧
      sigImg (aoc V) q h k = sigdcn V (⋃₀ dom (sig V)) ∧
      D ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) ∧
      !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] D ∧
      (∀ z ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)),
        !(dctUZero, !(q, h)) [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z →
          z = D ∨ D [odrOne (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M))] z) ∧
      (∀ i ∈ l, tensorProdTwoAOneSeq P !(tC, tauEmb Q (aoc VC) W (aoc (uc tC)) ψC σC) ﹫ i =
        tensorProdTwoAOneSeq P !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ) ﹫ i) ∧
      ((depOf P tC = l ∧ chdOf P tC ≠ ∅ ∧ D = (σC ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (uc tC)) ∨
        (depOf P tC = succ l ∧ ctp (uc tC) = ct ∧
          (σC ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tC) l = D)) := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := (otciCond_two hP).left
  have hTS := hS.isTreeStructure
  have hPs : IsSLOT P := (otciCond_two hP).left
  have hCN := tensorProdTwoTwoPrt_mem hP hQ hc (by
    rw [uc_orderedPair]; exact fun h' ↦ hm0 (by rw [h', sUnion_empty]))
  rw [hprt, pair_mem_tensorProdTwoTwoNds_iff] at hCN
  obtain ⟨htC, -, hσC, -⟩ := hCN
  have hc' := hc
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hc'
  obtain ⟨ht, hV, hσ, -⟩ := hc'
  have hdV : dom (sig V) ≠ ∅ := fun h' ↦ hm0 (by rw [h', sUnion_empty])
  have hm : ⋃₀ dom (sig V) ∈ dom (sig V) :=
    (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV) hdV).right.left
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  obtain ⟨hX', h0, hsub, -⟩ := lastSeg_facts hV hm
  obtain ⟨l, k, q, h, D, -, hl, hy, hq, hyN, hh, hk, hfirst, hje, hDN, hlt, hmin, hcase⟩ :=
    chd_struct hP hQ hc hm0 hprt
  have hDN' : D ∈ ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) :=
    (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX').mpr (.inr hDN)
  have hUt := uc_mem_stduoci_of_mem_otci_two hP ht
  have hdt := hTS.dep_mem_omega ht
  have hls : l ∈ succ (depOf P t) := mem_succ_of_mem hl
  obtain ⟨htl, hdtl⟩ := hTS.anc_mem_nd ht hls
  change ancOf P t l ∈ ndOf P at htl
  change depOf P (ancOf P t l) = l at hdtl
  have hil (i : M) (hi : i ∈ l) : i ∈ depOf P t :=
    (ordinal_of_mem ordinal_omega hdt).transitive _ hl hi
  rcases hcase with ⟨hCe, hlv, hDe⟩ | hCe
  · rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hCe
    obtain ⟨rfl, rfl, rfl⟩ := hCe
    rw [aoc_iniSeg] at hσC hagr ⊢
    refine ⟨rfl, l, k, q, h, D, hl, hy, hq, hyN, hh, hk, hfirst, hje, hDN', hlt, hmin,
      fun i hi ↦ ?_, .inl ⟨hdtl, ?_, ?_⟩⟩
    · have hσ1 := embChg_val_one_isFunction hσ
      obtain ⟨-, hsubl⟩ := uc_ancOf_rel hP ht hls
      have hUl := uc_mem_stduoci_of_mem_otci_two hP htl
      have hdl : dom (sig (uc (ancOf P t l))) = l := by rw [dom_sig_uc_eq_depOf hP htl, hdtl]
      have hnd := (siglvl_eq_one hUl (by rw [hdl]; exact hi)).right
      have hσl : (embRestrict (uc (ancOf P t l)) σ ﹫ ((1 : ℕ) : M)) ﹫
          sigdcn (uc (ancOf P t l)) i = (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i := by
        rw [embRestrict_val _ _ natCast_one_mem_two, val_restrict _ hσ1.left hnd
          (by rw [hσ1.right]; exact hsubl.left hnd), sigdcn_anc hP ht hls hi]
      have hz := emb_val_mem (aoc_mem_aotci_of_mem_stduoci_one hUl)
        (tensorProdATwoAOne_mem_aotci hQ hX') hσC hnd
      rw [hσl] at hz
      rw [seq_tauEmb_val hP htl hσC (by rw [hdtl]; exact hi), seq_tauEmb_val hP ht hσ (hil i hi),
        hσl, pushNd_old hQ hX hX' h0 hsub hagr hz,
        ancOf_ancOf hPs ht hls (succ_mem_succ_of_mem (ordinal_omega.transitive _ hdt hl) hi)]
    · intro h0
      have h1 : ancOf P t (succ l) ∈ chdOf P (ancOf P t l) := hTS.anc_succ_mem_chd ht hl
      rw [h0] at h1
      exact notin_empty _ h1
    · have hUl := uc_mem_stduoci_of_mem_otci_two hP htl
      have hσ1 := embChg_val_one_isFunction hσ
      obtain ⟨-, hsubl⟩ := uc_ancOf_rel hP ht hls
      have hnd := (ucf_one_of_ucflvl_ne_empty hUl hlv).right
      rw [hDe, embRestrict_val _ _ natCast_one_mem_two, val_restrict _ hσ1.left hnd
        (by rw [hσ1.right]; exact hsubl.left hnd)]
  · rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hCe
    obtain ⟨rfl, rfl, rfl⟩ := hCe
    rw [aoc_iniSeg] at hσC hagr ⊢
    have hl1s : succ l ∈ succ (depOf P t) := succ_mem_succ_of_mem hdt hl
    obtain ⟨htl1, hdtl1⟩ := hTS.anc_mem_nd ht hl1s
    change ancOf P t (succ l) ∈ ndOf P at htl1
    change depOf P (ancOf P t (succ l)) = succ l at hdtl1
    have hc1 : ancOf P t (succ l) ∈ chdOf P (ancOf P t l) := hTS.anc_succ_mem_chd ht hl
    obtain ⟨hcc, -, hccs, hcct, -, -⟩ :=
      ctChd_spec (natCast_mem_omega 2) natCast_two_ne_empty hP htl hc1
    set tc := ctChd P (ancOf P t l) (aoc (uc (ancOf P t (succ l)))) with htcdef
    obtain ⟨hdtc, hanctc⟩ := ancOf_eq_of_mem_chdOf hPs hcc
    rw [hdtl] at hdtc hanctc
    have hUl1 := uc_mem_stduoci_of_mem_otci_two hP htl1
    have hUtc := uc_mem_stduoci_of_mem_otci_two hP htC
    have hsfl1 := (uociCond_of_mem_stduoci_one hUl1).right.right.right.left.left
    have hsd (i : M) (hi : i ∈ succ l) : sigdcn (uc tc) i = sigdcn (uc t) i := by
      rw [← sigdcn_anc hP ht hl1s hi, sigdcn, sigdcn, hccs]
    have hσe := (mem_aotciEmbSet_iff.mp hσ).right
    have hσ1 := embChg_val_one_isFunction hσ
    have hσ0 : (∅ : M) ∈ dom σ := by
      rw [hσe.dom_eq]; exact mem_succ_of_mem empty_mem_natCast_one
    have hlsig : l ∈ dom (sig (uc t)) := by rw [dom_sig_uc_eq_depOf hP ht]; exact hl
    have hσCv (i : M) (hi : i ∈ l) :
        (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) i =
          (σ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc t) i := by
      have hi1 : i ∈ succ l := mem_succ_of_mem hi
      have hit : i ∈ dom (sig (uc t)) := by rw [dom_sig_uc_eq_depOf hP ht]; exact hil i hi
      have hnd' : sigdcn (uc t) i ∈ ndOf (aoc (uc (ancOf P t (succ l))) ﹫ ((1 : ℕ) : M)) := by
        have hi1' : i ∈ dom (sig (uc (ancOf P t (succ l)))) := by
          rw [dom_sig_uc_eq_depOf hP htl1, hdtl1]; exact hi1
        have h'' := (siglvl_eq_one hUl1 hi1').right
        rwa [sigdcn_anc hP ht hl1s hi1] at h''
      have hne : sigdcn (uc t) i ≠ sigdcn (uc t) l := by
        intro h''
        have := congrArg lbl h''
        rw [lbl_sigdcn hUt hit, lbl_sigdcn hUt hlsig] at this
        rw [this] at hi
        exact notMem_self _ hi
      rw [hsd i hi1, embUpd_val_one_of_ne hσe.isFunction hσ0 hσ1.left
        (by rw [hσ1.right]; exact (siglvl_eq_one hUt hit).right) hnd' hne]
    have hσCl : (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D ﹫ ((1 : ℕ) : M)) ﹫
        sigdcn (uc tc) l = D := by
      rw [hsd l (mem_succ_self l), embUpd_val_one hσ]
      exact val_update_self (hσ1.left.restrict _) _ _
    have hBX'1 := tensorProdATwoAOne_mem_aotci hQ hX'
    have hAtc := aoc_mem_aotci_of_mem_stduoci_one hUtc
    have hzold (i : M) (hi : i ∈ succ l) :
        (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc tc) i ∈
          ndOf (tensorProdATwoAOne Q (iniSegAoc V (⋃₀ dom (sig V))) ﹫ ((1 : ℕ) : M)) :=
      emb_val_mem hAtc hBX'1 hσC (siglvl_eq_one hUtc
        (by rw [dom_sig_uc_eq_depOf hP htC, hdtc]; exact hi)).right
    have hval (i : M) (hi : i ∈ l) :
        tensorProdTwoAOneSeq P !(tc, tauEmb Q (iniSegAoc V (⋃₀ dom (sig V))) W (aoc (uc tc)) ψC
          (embUpd σ (ancOf P t (succ l)) (sigdcn (uc t) l) D)) ﹫ i =
        tensorProdTwoAOneSeq P !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ) ﹫ i := by
      have hz := hzold i (mem_succ_of_mem hi)
      rw [hσCv i hi] at hz
      have hsi : succ i ∈ succ l := succ_mem_succ_of_mem (ordinal_omega.transitive _ hdt hl) hi
      rw [seq_tauEmb_val hP htC hσC (by rw [hdtc]; exact mem_succ_of_mem hi),
        seq_tauEmb_val hP ht hσ (hil i hi), hσCv i hi, pushNd_old hQ hX hX' h0 hsub hagr hz,
        ← ancOf_ancOf hPs htC (by rw [hdtc]; exact mem_succ_of_mem (mem_succ_self l)) hsi,
        hanctc, ancOf_ancOf hPs ht hls hsi]
    refine ⟨rfl, l, k, q, h, D, hl, hy, hq, hyN, hh, hk, hfirst, hje, hDN', hlt, hmin,
      fun i hi ↦ hval i hi, .inr ⟨hdtc, hcct, hσCl⟩⟩

end ChdRows

section SblCmp

variable {P Q W : M}

/-- Two children of the same parent (with the same key `V`), pushed along embeddings that agree on
the old nodes and send the new node to `e < e'`, have images in order -/
theorem bkLt_isoUp_sbl (hP : P ∈ otci ((2 : ℕ) : M)) (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hW : W ∈ aotci ((1 : ℕ) : M)) {V t σ V' t' σ' VC tC σC ψ ψ' : M}
    (hc : !(V, !(t, σ)) ∈ tensorProdTwoTwoNds P Q)
    (hc' : !(V', !(t', σ')) ∈ tensorProdTwoTwoNds P Q)
    (haoc : aoc V' = aoc V) (hsig : sig V' = sig V)
    (hm0 : ⋃₀ dom (sig V) ≠ ∅)
    (hprt : tensorProdTwoTwoPrt P Q !(V, !(t, σ)) = !(VC, !(tC, σC)))
    (hprt' : tensorProdTwoTwoPrt P Q !(V', !(t', σ')) = !(VC, !(tC, σC)))
    (hψ : ψ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W))
    (hψ' : ψ' ∈ aotciEmbSet ((1 : ℕ) : M) (aoc V) (tensorProdTwoAOneTgt W))
    (hagr : ∀ v ∈ ndOf (iniSegAoc V (⋃₀ dom (sig V)) ﹫ ((1 : ℕ) : M)),
      (ψ ﹫ ((1 : ℕ) : M)) ﹫ v = (ψ' ﹫ ((1 : ℕ) : M)) ﹫ v)
    (hnew : ((ψ ﹫ ((1 : ℕ) : M)) ﹫ sigdcn V (⋃₀ dom (sig V)))
      [odrOne (tensorProdTwoAOneTgt W ﹫ ((1 : ℕ) : M))]
      ((ψ' ﹫ ((1 : ℕ) : M)) ﹫ sigdcn V (⋃₀ dom (sig V)))) :
    BKLt (tensorProdTwoAOneCoordOdr P (tensorProdATwoAOne Q W))
      (tensorProdTwoAOneSeq P !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ))
      (tensorProdTwoAOneSeq P !(t', tauEmb Q (aoc V') W (aoc (uc t')) ψ' σ')) := by
  rw [haoc]
  have hsd : sigdcn V' = sigdcn V := by
    funext i
    simp only [sigdcn, hsig]
  have hia : iniSegAoc V' = iniSegAoc V := by
    funext i
    simp only [iniSegAoc, iniSegNds, iniSegOdr, hsd, haoc]
  have hm0' : ⋃₀ dom (sig V') ≠ ∅ := by rw [hsig]; exact hm0
  have hTS := (otciCond_two hP).left.isTreeStructure
  have hCN := tensorProdTwoTwoPrt_mem hP hQ hc (by
    rw [uc_orderedPair]; exact fun h' ↦ hm0 (by rw [h', sUnion_empty]))
  rw [hprt, pair_mem_tensorProdTwoTwoNds_iff] at hCN
  obtain ⟨htC, -, -, -⟩ := hCN
  have hc1 := hc
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hc1
  obtain ⟨ht, hV, hσ, -⟩ := hc1
  have hc2 := hc'
  rw [pair_mem_tensorProdTwoTwoNds_iff] at hc2
  obtain ⟨ht', -, hσ', -⟩ := hc2
  rw [haoc] at hσ'
  have hdV : dom (sig V) ≠ ∅ := fun h' ↦ hm0 (by rw [h', sUnion_empty])
  have hm : ⋃₀ dom (sig V) ∈ dom (sig V) :=
    (sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV) hdV).right.left
  have hX := aoc_mem_aotci_of_mem_stduoci_one hV
  have hBW := tensorProdATwoAOne_mem_aotci hQ hW
  obtain ⟨hVC, l, k, q, h, D, hl, hy, hq, hyN, hh, hk, hfirst, hje, hDN, hlt, hmin, hrows,
    hcase⟩ := chd_rows (W := W) (ψ := ψ) (ψC := ψ) hP hQ hc hm0 hprt fun _ _ ↦ rfl
  obtain ⟨-, l', k', q', h', D', hl', hy', hq', hyN', hh', hk', hfirst', hje', hDN', hlt', hmin',
    hrows', hcase'⟩ := chd_rows (W := W) (ψ := ψ') (ψC := ψ) hP hQ hc' hm0' hprt' (by
      rw [hVC, aoc_iniSeg]; exact hagr)
  simp only [haoc, hsig, hsd, hia] at hyN' hh' hfirst' hje' hDN' hlt' hmin' hrows'
  have hctE : ctp (uc tC) = ct → chdOf P tC = ∅ :=
    chdOf_eq_empty_of_ctp_eq_ct (natCast_mem_omega 2) hP htC
  obtain ⟨rfl, rfl⟩ : l = l' ∧ D = D' := by
    rcases hcase with ⟨hd, hch, hD⟩ | ⟨hd, hct, hD⟩ <;>
      rcases hcase' with ⟨hd', hch', hD'⟩ | ⟨hd', hct', hD'⟩
    · rw [hd] at hd'
      subst hd'
      exact ⟨rfl, hD.trans hD'.symm⟩
    · exact (hch (hctE hct')).elim
    · exact (hch' (hctE hct)).elim
    · rw [hd] at hd'
      have hl0 := TreeStructure.eq_of_succ_eq_succ
        (ordinal_of_mem (ordinal_of_mem ordinal_omega (hTS.dep_mem_omega ht)) hl) hd'
      subst hl0
      exact ⟨rfl, hD.symm.trans hD'⟩
  obtain ⟨rfl, hpre⟩ := seq_prefix_of_succ_eq hQ hV hm hq hyN hh hk hfirst hje hq' hyN' hh' hk'
    hfirst' hje' hDN hlt hmin hlt' hmin'
  have hlt0 := pushNd_lt_of_prefix hQ hV hm hW hψ hψ' hagr hnew hq hyN hh hk hfirst hje hq' hyN'
    hh' hk' hje' hpre
  have hsf := isFunction_tensorProdTwoAOneSeq P !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ)
  have hsf' := isFunction_tensorProdTwoAOneSeq P !(t', tauEmb Q (aoc V) W (aoc (uc t')) ψ' σ')
  have hdt := hTS.dep_mem_omega ht
  have hdt' := hTS.dep_mem_omega ht'
  unfold BKLt
  right
  refine ⟨l, by rw [tensorProdTwoAOneSeq_dom]; exact hl,
      by rw [tensorProdTwoAOneSeq_dom]; exact hl',
    ?_, ?_⟩
  · have hks : l ⊆ dom (tensorProdTwoAOneSeq P !(t, tauEmb Q (aoc V) W (aoc (uc t)) ψ σ)) := by
      rw [tensorProdTwoAOneSeq_dom]
      exact fun i hi ↦ (ordinal_of_mem ordinal_omega hdt).transitive _ hl hi
    have hks' : l ⊆ dom (tensorProdTwoAOneSeq P !(t', tauEmb Q (aoc V) W (aoc (uc t')) ψ' σ')) := by
      rw [tensorProdTwoAOneSeq_dom]
      exact fun i hi ↦ (ordinal_of_mem ordinal_omega hdt').transitive _ hl' hi
    exact hsf.restrict_eq_restrict hsf' hks hks' fun i hi ↦ (hrows i hi).symm.trans (hrows' i hi)
  · rw [seq_tauEmb_val hP ht hσ hl, seq_tauEmb_val hP ht' hσ' hl', hy, hy',
      tensorProdTwoAOneCoordOdr, rel_lexProd_iff]
    have hyB : !(dctUZero, !(q, h)) ∈ ndOf (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)) :=
      (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX).mpr (.inr hyN)
    have hyB' : !(dctUZero, !(q', h')) ∈ ndOf (tensorProdATwoAOne Q (aoc V) ﹫ ((1 : ℕ) : M)) :=
      (mem_ndOf_tensorProdATwoAOne_val_one_iff hQ hX).mpr (.inr hyN')
    have hBW1 := val_mem_otci_of_mem_aotci hBW (mem_succ_self _)
    have hm1 : relabelOne trvAZero (pushNd Q (aoc V) W ψ !(dctUZero, !(q, h))) ∈
        ndOf (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)) := by
      rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hBW1]
      exact ⟨_, pushNd_mem hQ hX hW hψ hyB, rfl⟩
    have hm2 : relabelOne trvAZero (pushNd Q (aoc V) W ψ' !(dctUZero, !(q', h'))) ∈
        ndOf (tensorProdTwoAOneTgt (tensorProdATwoAOne Q W) ﹫ ((1 : ℕ) : M)) := by
      rw [tensorProdTwoAOneTgt_val_one, mem_ndOf_tensorProdOneAZero_iff hBW1]
      exact ⟨_, pushNd_mem hQ hX hW hψ' hyB', rfl⟩
    refine ⟨⟨hm1, (hTS.anc_mem_nd ht (succ_mem_succ_of_mem hdt hl)).left⟩,
      ⟨hm2, (hTS.anc_mem_nd ht' (succ_mem_succ_of_mem hdt' hl')).left⟩, .inl ?_⟩
    exact (rel_tgt_relabel_iff hBW (pushNd_mem hQ hX hW hψ hyB)
      (pushNd_mem hQ hX hW hψ' hyB')).mpr hlt0

end SblCmp

section IsoDefinable3

instance : ClassFunction.Definable (fun p : M ↦ tauOne (left (left p)) (right (left p))
    (left (right p)) (left (right (right p))) (right (right (right p)))) Set.univ := by
  have : ClassFunction.Definable (fun p : M ↦ dom (right (right (right p)) ﹫ ((1 : ℕ) : M)))
      Set.univ := by
    infer_instance
  exact ClassFunction.Definable.toSetRestrictedTo (G := tauG)
    (D := fun p ↦ dom (right (right (right p)) ﹫ ((1 : ℕ) : M)))

instance : Multiclass.Definable
    (fun xs : Fin 6 → M ↦ tauOne (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) = xs 5) Set.univ := by
  obtain ⟨G, hG⟩ : ∃ G : ClassFunction M, G = fun p : M ↦ tauOne (left (left p)) (right (left p))
      (left (right p)) (left (right (right p))) (right (right (right p))) := ⟨_, rfl⟩
  have : G.Definable Set.univ := by
    rw [hG]
    infer_instance
  have h : (fun xs : Fin 6 → M ↦ tauOne (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) = xs 5) =
      fun xs : Fin 6 → M ↦ ∃ p : M, p = !(!(xs 0, xs 1), !(xs 2, !(xs 3, xs 4))) ∧ G p = xs 5 := by
    funext xs
    apply propext
    rw [hG]
    simp only [left_orderedPair, right_orderedPair, exists_eq_left]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m o : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ tauOne (xs i) (xs j) (xs k) (xs l) (xs m) = xs o) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tauOne (xs i) (xs j) (xs k) (xs l) (xs m) = xs o) =
      Multiclass.remap (fun ys : Fin 6 → M ↦
        tauOne (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) = ys 5) ![i, j, k, l, m, o] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The target `(Q ⊗ W) ⊗ Z` of the embeddings `ρ ∘ Φ_ψ ∘ σ` -/
def TauTgt (Q W B : M) : Prop :=
  ∃ z C : M, z = !(Q, W) ∧ tensorProdATwoAOne (left z) (right z) = C ∧
    tensorProdTwoAOneTgt C = B

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ TauTgt (xs 0) (xs 1) (xs 2)) Set.univ := by
  have : ClassFunction.Definable (fun Q : M ↦ tensorProdTwoAOneTgt Q) Set.univ := inferInstance
  obtain ⟨G, hG⟩ : ∃ G : ClassFunction M,
      G = fun z : M ↦ tensorProdATwoAOne (left z) (right z) := ⟨_, rfl⟩
  have : G.Definable Set.univ := by
    rw [hG]
    infer_instance
  have h : (fun xs : Fin 3 → M ↦ TauTgt (xs 0) (xs 1) (xs 2)) = fun xs ↦
      ∃ z C : M, z = !(xs 0, xs 1) ∧ G z = C ∧ tensorProdTwoAOneTgt C = xs 2 := by
    rw [hG]
    rfl
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ TauTgt (xs i) (xs j) (xs k)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ TauTgt (xs i) (xs j) (xs k)) =
      Multiclass.remap (fun ys : Fin 3 → M ↦ TauTgt (ys 0) (ys 1) (ys 2)) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The graph of `tauEmb` -/
def TauEmbRel (Q X W A ψ σ r : M) : Prop :=
  ∃ B o : M, TauTgt Q W B ∧ tauOne Q X W ψ σ = o ∧ embMk A B o = r

instance : Multiclass.Definable
    (fun xs : Fin 7 → M ↦ TauEmbRel (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6)) Set.univ := by
  unfold TauEmbRel
  infer_instance

instance : Multiclass.Definable
    (fun xs : Fin 7 → M ↦ tauEmb (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) = xs 6) Set.univ := by
  have h : (fun xs : Fin 7 → M ↦ tauEmb (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) = xs 6) =
      fun xs ↦ TauEmbRel (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6) := by
    funext xs
    apply propext
    constructor
    · intro h
      refine ⟨tensorProdTwoAOneTgt (tensorProdATwoAOne (xs 0) (xs 2)), _,
        ⟨!(xs 0, xs 2), tensorProdATwoAOne (xs 0) (xs 2), rfl, ?_, rfl⟩, rfl, h⟩
      rw [left_orderedPair, right_orderedPair]
    · rintro ⟨B, o, ⟨z, C, hz, hC, hB⟩, ho, h⟩
      rw [hz, left_orderedPair, right_orderedPair] at hC
      rw [← h, ← ho, ← hB, ← hC]
      rfl
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m o u : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ tauEmb (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) = xs u) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tauEmb (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) = xs u) =
      Multiclass.remap (fun ys : Fin 7 → M ↦
        tauEmb (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) = ys 6) ![i, j, k, l, m, o, u] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The graph of `isoUpOf` -/
def IsoUpRel (Q W V t σ ψ r : M) : Prop :=
  ∃ X A e : M, X = aoc V ∧ A = aoc (uc t) ∧ tauEmb Q X W A ψ σ = e ∧ r = !(dctUZero, !(t, e))

instance : Multiclass.Definable
    (fun xs : Fin 7 → M ↦ IsoUpRel (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6)) Set.univ := by
  unfold IsoUpRel
  infer_instance

instance : Multiclass.Definable
    (fun xs : Fin 7 → M ↦ isoUpOf (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) = xs 6) Set.univ := by
  have h : (fun xs : Fin 7 → M ↦ isoUpOf (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) = xs 6) =
      fun xs ↦ IsoUpRel (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) (xs 5) (xs 6) := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, _, rfl, rfl, rfl, h.symm⟩
    · rintro ⟨X, A, e, rfl, rfl, rfl, h⟩
      exact h.symm
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m o u : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ isoUpOf (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) = xs u) Set.univ := by
  have h : (fun xs : Fin n → M ↦ isoUpOf (xs i) (xs j) (xs k) (xs l) (xs m) (xs o) = xs u) =
      Multiclass.remap (fun ys : Fin 7 → M ↦
        isoUpOf (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) = ys 6) ![i, j, k, l, m, o, u] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The image of the node `(x, ψ)`, `x = (V, (t, σ))` -/
noncomputable def isoUp (Q W x ψ : M) : M := isoUpOf Q W (uc x) (nodeQ x) (nodeH x) ψ

/-- The graph of `isoUp` -/
def IsoUpRel₂ (Q W x ψ r : M) : Prop :=
  ∃ V t σ : M, V = uc x ∧ t = nodeQ x ∧ σ = nodeH x ∧ isoUpOf Q W V t σ ψ = r

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ IsoUpRel₂ (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)) Set.univ := by
  unfold IsoUpRel₂
  infer_instance

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ isoUp (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) Set.univ := by
  have h : (fun xs : Fin 5 → M ↦ isoUp (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) =
      fun xs ↦ IsoUpRel₂ (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, _, rfl, rfl, rfl, h⟩
    · rintro ⟨V, t, σ, rfl, rfl, rfl, h⟩
      exact h
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ isoUp (xs i) (xs j) (xs k) (xs l) = xs m) Set.univ := by
  have h : (fun xs : Fin n → M ↦ isoUp (xs i) (xs j) (xs k) (xs l) = xs m) =
      Multiclass.remap (fun ys : Fin 5 → M ↦
        isoUp (ys 0) (ys 1) (ys 2) (ys 3) = ys 4) ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

end IsoDefinable3

end FirstOrder.Language.MemStructure
