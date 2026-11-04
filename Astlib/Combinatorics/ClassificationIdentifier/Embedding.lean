/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.Basic
/-!
# Embeddings of classification identifiers

* `IsOtciEmbedding P Q π`: `π` is an embedding of the semi-linearly ordered tree structure `P` into
  `Q` that preserves the identifier `uc` of every node (and ignores the labels);
  `IsOtciIsomorphism P Q π`: moreover `π` is onto the nodes of `Q`.
* `IsAotciEmbedding n P Q π`: `π` is a function on `n + 1` whose value at `i` is an embedding of the
  tree `P(i)` into `Q(i)`; `IsAotciIsomorphism n P Q π`: each `π(i)` is an isomorphism;
  `aotciEmbSet n P Q`: the set of these embeddings.

For semi-linearly ordered tree structures preserving `uc`, the split of the siblings into linearly
ordered sets is preserved automatically, since it is given by `left a ﹫ ∅ = aoc (uc a)`
(`IsOtciEmbedding.of_isEmbedding_ts`).

`otciSngIso P Q` is the unique isomorphism of trees with a single node; any two trees in `otci_0`
are isomorphic by it (`isOtciIsomorphism_otciSngIso_of_mem_otci_empty`).
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

open SLOTreeStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] {n P Q π : M}

/-- `π` is an embedding of the tree `P` into `Q`: an embedding of semi-linearly ordered tree
structures preserving the identifier `uc` of every node -/
structure IsOtciEmbedding (P Q π : M) : Prop where
  isEmbedding : (ofM P).IsEmbedding (ofM Q) π
  uc_val {a : M} (ha : a ∈ ndOf P) : uc (π ﹫ a) = uc a

/-- `π` is an isomorphism of the tree `P` onto `Q`: a surjective embedding -/
structure IsOtciIsomorphism (P Q π : M) : Prop where
  isOtciEmbedding : IsOtciEmbedding P Q π
  ran_eq : ran π = ndOf Q

/-- `π` is an embedding of the array `P` into `Q` of trees of levels up to `n`: a function on
`n + 1` whose value at `i` is an embedding of `P(i)` into `Q(i)` -/
structure IsAotciEmbedding (n P Q π : M) : Prop where
  isFunction : IsFunction π
  dom_eq : dom π = succ n
  isOtciEmbedding {i : M} (hi : i ∈ succ n) : IsOtciEmbedding (P ﹫ i) (Q ﹫ i) (π ﹫ i)

/-- `π` is an isomorphism of the array `P` onto `Q` of trees of levels up to `n`: a function on
`n + 1` whose value at `i` is an isomorphism of `P(i)` onto `Q(i)` -/
structure IsAotciIsomorphism (n P Q π : M) : Prop where
  isFunction : IsFunction π
  dom_eq : dom π = succ n
  isOtciIsomorphism {i : M} (hi : i ∈ succ n) : IsOtciIsomorphism (P ﹫ i) (Q ﹫ i) (π ﹫ i)

/-- The set of the embeddings of the array `P` into `Q` of trees of levels up to `n` -/
noncomputable def aotciEmbSet (n P Q : M) : M :=
  𝒫 (succ n ×ˢ 𝒫 (ndUnion (ran P) ×ˢ ndUnion (ran Q))) ∩₀ IsAotciEmbedding n P Q

omit [ModelsKP M] in
/-- An isomorphism of trees is one of semi-linearly ordered tree structures -/
theorem IsOtciIsomorphism.isIsomorphism (h : IsOtciIsomorphism P Q π) :
    (ofM P).IsIsomorphism (ofM Q) π :=
  ⟨h.isOtciEmbedding.isEmbedding, h.ran_eq⟩

omit [ModelsKP M] in
/-- An isomorphism of arrays is an embedding -/
theorem IsAotciIsomorphism.isAotciEmbedding (h : IsAotciIsomorphism n P Q π) :
    IsAotciEmbedding n P Q π :=
  ⟨h.isFunction, h.dom_eq, fun hi ↦ (h.isOtciIsomorphism hi).isOtciEmbedding⟩

/-- An embedding of the tree structures of `P` and `Q` preserving `uc` and the orders of the
linearly ordered sets is an embedding of trees: the split into linearly ordered sets is preserved
automatically -/
theorem IsOtciEmbedding.of_isEmbedding_ts [HasOmega M] (hP : IsSLOT P) (hQ : IsSLOT Q)
    (he : (ofM P).ts.IsEmbedding (ofM Q).ts π) (huc : ∀ a ∈ ndOf P, uc (π ﹫ a) = uc a)
    (hodr : ∀ a ∈ ndOf P, ∀ b ∈ ndOf P, (ofM P).ndlos a = (ofM P).ndlos b →
      a [losOdr ((ofM P).ndlos a)] b →
        (π ﹫ a) [losOdr ((ofM Q).ndlos (π ﹫ a))] (π ﹫ b)) :
    IsOtciEmbedding P Q π := by
  have hPS : (ofM P).IsSLOTreeStructure := hP
  have hQS : (ofM Q).IsSLOTreeStructure := hQ
  have hf := he.isInjectionFromTo.left
  refine ⟨⟨he, fun {a b} ha hb ↦ ?_, fun ha hb hab hrel ↦ hodr _ ha _ hb hab hrel⟩, huc _⟩
  have hka : left (π ﹫ a) ﹫ ∅ = left a ﹫ ∅ := by
    have h : left (π ﹫ a) = left a := huc a ha
    rw [h]
  have hkb : left (π ﹫ b) ﹫ ∅ = left b ﹫ ∅ := by
    have h : left (π ﹫ b) = left b := huc b hb
    rw [h]
  rw [hQS.ndlos_eq_iff (hf.val_mem ha) (hf.val_mem hb), hPS.ndlos_eq_iff ha hb,
    he.sbl_val_eq_iff hPS.isTreeStructure hQS.isTreeStructure ha hb, hka, hkb]

/-- `otciSngIso P Q = {(b, c)}` for trees `P` and `Q` with single nodes `b` and `c`: the unique
isomorphism of `P` onto `Q` if `uc b = uc c` -/
noncomputable def otciSngIso (P Q : M) : M := (ofM P).sngIso (ofM Q)

/-- Any two trees in `otci_0` are isomorphic, by `otciSngIso` -/
theorem isOtciIsomorphism_otciSngIso_of_mem_otci_empty [ModelsZF M] (hP : P ∈ otci (∅ : M))
    (hQ : Q ∈ otci (∅ : M)) : IsOtciIsomorphism P Q (otciSngIso P Q) := by
  have hPS : IsSLOT P := isSLOT_of_mem_otci hP
  have hQS : IsSLOT Q := isSLOT_of_mem_otci hQ
  rw [mem_otci_empty_iff] at hP hQ
  obtain ⟨p, -, rfl⟩ := hP
  obtain ⟨q, -, rfl⟩ := hQ
  have hnd := ndOf_irmrtOf_emptySLOT (M := M) !(otci0Uc, p)
  have hnd' := ndOf_irmrtOf_emptySLOT (M := M) !(otci0Uc, q)
  have hiso := SLOTreeStructure.isIsomorphism_sngIso hnd hnd' hPS hQS
  refine ⟨⟨hiso.isEmbedding, ?_⟩, hiso.ran_eq⟩
  intro a ha
  rw [hnd, mem_singleton_iff] at ha
  rw [ha, otciSngIso, SLOTreeStructure.sngIso, TreeStructure.sngIso_eq hnd hnd', singletonFun_val,
    uc_orderedPair, uc_orderedPair]

/-- `otciSngIso P Q` is the unique embedding of trees `P` and `Q` with single nodes -/
theorem IsOtciEmbedding.eq_otciSngIso {b c : M} (hnd : ndOf P = {b}) (hnd' : ndOf Q = {c})
    (he : IsOtciEmbedding P Q π) : π = otciSngIso P Q :=
  he.isEmbedding.eq_sngIso hnd hnd'

end FirstOrder.Language.MemStructure
