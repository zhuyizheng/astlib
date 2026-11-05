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

section Definability

variable [HasOmega M]

omit [HasOmega M] in
/-- `IsOtciEmbedding` with all quantifiers bounded -/
theorem isOtciEmbedding_iff : IsOtciEmbedding P Q π ↔
    π !: ndOf P ↪ ndOf Q ∧
    (∀ a ∈ ndOf P, depOf Q (π ﹫ a) = depOf P a) ∧
    (∀ a ∈ ndOf P, ∀ b ∈ ndOf P, b ∈ chdOf P a → π ﹫ b ∈ chdOf Q (π ﹫ a)) ∧
    (∀ a ∈ ndOf P, ∀ b ∈ ndOf P,
      ndlosOf Q (π ﹫ a) = ndlosOf Q (π ﹫ b) ↔ ndlosOf P a = ndlosOf P b) ∧
    (∀ a ∈ ndOf P, ∀ b ∈ ndOf P, ndlosOf P a = ndlosOf P b → a [losOdr (ndlosOf P a)] b →
      (π ﹫ a) [losOdr (ndlosOf Q (π ﹫ a))] (π ﹫ b)) ∧
    (∀ a ∈ ndOf P, uc (π ﹫ a) = uc a) := by
  constructor
  · rintro ⟨⟨⟨hinj, hdep, hprt⟩, hlos, hodr⟩, huc⟩
    refine ⟨hinj, fun a ha ↦ hdep ha, fun a ha b hb hc ↦ ?_, fun a ha b hb ↦ hlos ha hb,
      fun a ha b hb hab hrel ↦ hodr ha hb hab hrel, fun a ha ↦ huc ha⟩
    have h := hprt ha hb (TreeStructure.rel_prt_iff.mpr ⟨⟨hb, ha⟩, hc⟩)
    exact (TreeStructure.rel_prt_iff.mp h).right
  · rintro ⟨hinj, hdep, hprt, hlos, hodr, huc⟩
    refine ⟨⟨⟨hinj, fun ha ↦ hdep _ ha, fun {a b} ha hb hba ↦ ?_⟩, fun ha hb ↦ hlos _ ha _ hb,
      fun ha hb hab hrel ↦ hodr _ ha _ hb hab hrel⟩, fun ha ↦ huc _ ha⟩
    exact TreeStructure.rel_prt_iff.mpr ⟨⟨hinj.isFunctionFromTo.val_mem hb,
      hinj.isFunctionFromTo.val_mem ha⟩,
      hprt a ha b hb (TreeStructure.rel_prt_iff.mp hba).right⟩

/-- `xs j` is below `xs k` in the linearly ordered set of `xs j` in the tree `xs i` -/
instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    (xs j) [losOdr (ndlosOf (xs i) (xs j))] (xs k)) Set.univ := by
  infer_instance

/-- The images of `xs j` and `xs l` under `xs i` are in the order of the linearly ordered set of the
first in the tree `xs k` -/
instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    (xs i ﹫ xs j) [losOdr (ndlosOf (xs k) (xs i ﹫ xs j))] (xs i ﹫ xs l)) Set.univ := by
  have h : (fun xs : Fin n → M ↦
      (xs i ﹫ xs j) [losOdr (ndlosOf (xs k) (xs i ﹫ xs j))] (xs i ﹫ xs l)) =
      fun xs : Fin n → M ↦
        ∃ c d : M, c = xs i ﹫ xs j ∧ d = xs i ﹫ xs l ∧ c [losOdr (ndlosOf (xs k) c)] d := by
    funext xs
    apply propext
    constructor
    · intro h
      exact ⟨_, _, rfl, rfl, h⟩
    · rintro ⟨c, d, rfl, rfl, h⟩
      exact h
  rw [h]
  infer_instance

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ IsOtciEmbedding (xs 0) (xs 1) (xs 2))
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ IsOtciEmbedding (xs 0) (xs 1) (xs 2)) = fun xs : Fin 3 → M ↦
      xs 2 !: ndOf (xs 0) ↪ ndOf (xs 1) ∧
      (∀ a ∈ ndOf (xs 0), depOf (xs 1) (xs 2 ﹫ a) = depOf (xs 0) a) ∧
      (∀ a ∈ ndOf (xs 0), ∀ b ∈ ndOf (xs 0), b ∈ chdOf (xs 0) a →
        xs 2 ﹫ b ∈ chdOf (xs 1) (xs 2 ﹫ a)) ∧
      (∀ a ∈ ndOf (xs 0), ∀ b ∈ ndOf (xs 0),
        ndlosOf (xs 1) (xs 2 ﹫ a) = ndlosOf (xs 1) (xs 2 ﹫ b) ↔
          ndlosOf (xs 0) a = ndlosOf (xs 0) b) ∧
      (∀ a ∈ ndOf (xs 0), ∀ b ∈ ndOf (xs 0), ndlosOf (xs 0) a = ndlosOf (xs 0) b →
        a [losOdr (ndlosOf (xs 0) a)] b →
          (xs 2 ﹫ a) [losOdr (ndlosOf (xs 1) (xs 2 ﹫ a))] (xs 2 ﹫ b)) ∧
      (∀ a ∈ ndOf (xs 0), uc (xs 2 ﹫ a) = uc a) := by
    funext xs
    exact propext isOtciEmbedding_iff
  have : Multiclass.Definable (fun xs : Fin 3 → M ↦
      ∀ a ∈ ndOf (xs 0), depOf (xs 1) (xs 2 ﹫ a) = depOf (xs 0) a) Set.univ := by infer_instance
  have : Multiclass.Definable (fun xs : Fin 3 → M ↦
      ∀ a ∈ ndOf (xs 0), ∀ b ∈ ndOf (xs 0), b ∈ chdOf (xs 0) a →
        xs 2 ﹫ b ∈ chdOf (xs 1) (xs 2 ﹫ a)) Set.univ := by infer_instance
  have : Multiclass.Definable (fun xs : Fin 3 → M ↦
      ∀ a ∈ ndOf (xs 0), ∀ b ∈ ndOf (xs 0),
        ndlosOf (xs 1) (xs 2 ﹫ a) = ndlosOf (xs 1) (xs 2 ﹫ b) ↔
          ndlosOf (xs 0) a = ndlosOf (xs 0) b) Set.univ := by infer_instance
  have : Multiclass.Definable (fun xs : Fin 3 → M ↦
      ∀ a ∈ ndOf (xs 0), ∀ b ∈ ndOf (xs 0), ndlosOf (xs 0) a = ndlosOf (xs 0) b →
        a [losOdr (ndlosOf (xs 0) a)] b →
          (xs 2 ﹫ a) [losOdr (ndlosOf (xs 1) (xs 2 ﹫ a))] (xs 2 ﹫ b)) Set.univ := by
    infer_instance
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ IsOtciEmbedding (xs i) (xs j) (xs k)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsOtciEmbedding (xs i) (xs j) (xs k)) =
      Multiclass.remap (fun ys : Fin 3 → M ↦ IsOtciEmbedding (ys 0) (ys 1) (ys 2)) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable
    (fun xs : Fin 4 → M ↦ IsAotciEmbedding (xs 0) (xs 1) (xs 2) (xs 3)) Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ IsAotciEmbedding (xs 0) (xs 1) (xs 2) (xs 3)) =
      fun xs : Fin 4 → M ↦
      IsFunction (xs 3) ∧ dom (xs 3) = succ (xs 0) ∧ ∀ i ∈ succ (xs 0), ∃ A B f,
        A = xs 1 ﹫ i ∧ B = xs 2 ﹫ i ∧ f = xs 3 ﹫ i ∧ IsOtciEmbedding A B f := by
    funext xs
    apply propext
    constructor
    · rintro ⟨hf, hdom, he⟩
      exact ⟨hf, hdom, fun i hi ↦ ⟨_, _, _, rfl, rfl, rfl, he hi⟩⟩
    · rintro ⟨hf, hdom, he⟩
      refine ⟨hf, hdom, fun {i} hi ↦ ?_⟩
      obtain ⟨A, B, f, rfl, rfl, rfl, h⟩ := he i hi
      exact h
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦ ∀ i ∈ succ (xs 0), ∃ A B f,
      A = xs 1 ﹫ i ∧ B = xs 2 ﹫ i ∧ f = xs 3 ﹫ i ∧ IsOtciEmbedding A B f) Set.univ := by
    infer_instance
  rw [h]
  infer_instance

end Definability

end FirstOrder.Language.MemStructure
