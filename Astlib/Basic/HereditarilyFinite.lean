/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Cardinal.Finite
import Astlib.Basic.VonNeumannHierarchy
/-!
# Hereditarily finite sets

In models of `ZF`:

* images of finite sets under definable class functions are finite (`Finite.image`), and power
  sets of finite sets are finite (`Finite.powerset`);
* the sets in `𝕍 ω` are the hereditarily finite sets: `x ∈ 𝕍 ω` iff `x` is finite and
  `x ⊆ 𝕍 ω` (`mem_vonNeumann_omega_iff`);
* `𝕍 ω` contains the natural numbers and is closed under elements, subsets, pairs, unions,
  products, power sets and functions with finite domain (`IsFunction.mem_vonNeumann_omega`).
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M] {a b f n x y : M}

/-- Images of finite sets under definable class functions are finite -/
theorem Finite.image {G : ClassFunction M} [(G : Multiclass M 2).Definable Set.univ]
    (hx : Finite x) : Finite (ran (G ↾₀ x)) :=
  hx.of_isSurjectionFromTo (isSurjectionFromTo_toSetRestrictedTo
    (isSetRestrictedTo_of_definable x) fun _ ↦
      mem_ran_toSetRestrictedTo_iff (isSetRestrictedTo_of_definable x))

/-- Power sets of finite sets are finite -/
theorem Finite.powerset (hx : Finite x) : Finite (𝒫 x) := by
  refine hx.induction (A := fun x : M ↦ Finite (𝒫 x)) ?_ (fun x a ih ↦ ?_)
  · have h : (𝒫 ∅ : M) = {∅} := by
      ext y
      rw [mem_powerset_iff, mem_singleton_iff]
      constructor
      · intro hy
        ext z
        simpa using @hy z
      · rintro rfl
        exact fun z hz ↦ hz
    rw [h]
    exact finite_singleton ∅
  have hres : IsSetRestrictedTo (fun y ↦ Insert.insert a y) (𝒫 x) :=
    isSetRestrictedTo_of_definable _
  have h : 𝒫 (Insert.insert a x) = 𝒫 x ∪ ran ((fun y ↦ Insert.insert a y) ↾₀ 𝒫 x) := by
    ext y
    rw [mem_union_iff, mem_ran_toSetRestrictedTo_iff hres, mem_powerset_iff, mem_powerset_iff]
    constructor
    · intro hy
      by_cases ha : a ∈ y
      · refine .inr ⟨y \ {a}, ?_, ?_⟩
        · rw [mem_powerset_iff]
          intro z hz
          grind
        · ext z
          grind
      · refine .inl fun z hz ↦ ?_
        grind
    · rintro (hy | ⟨z, hz, rfl⟩) w hw
      · grind
      · rw [mem_powerset_iff] at hz
        grind
  rw [h]
  exact ih.union ih.image

/-- Products of finite sets are finite -/
theorem Finite.sprod (hx : Finite x) (hy : Finite y) : Finite (x ×ˢ y) := by
  refine hx.induction (A := fun x : M ↦ Finite (x ×ˢ y)) (by rw [empty_sprod]; exact finite_empty)
    (fun x a ih ↦ ?_)
  have hres : IsSetRestrictedTo (fun v ↦ !(a, v)) y := isSetRestrictedTo_of_definable _
  have h : (Insert.insert a x) ×ˢ y = ran ((fun v ↦ !(a, v)) ↾₀ y) ∪ x ×ˢ y := by
    rw [insert_eq, union_sprod]
    congr 1
    ext z
    rw [mem_ran_toSetRestrictedTo_iff hres, mem_sprod_iff]
    grind
  rw [h]
  exact hy.image.union ih

/-- The domain of a finite relation is finite -/
theorem Finite.dom (hf : Finite f) (hrel : IsRelation f) : Finite (MemStructure.dom f) := by
  have hres : IsSetRestrictedTo left f := isSetRestrictedTo_of_definable _
  have h : MemStructure.dom f = ran (left ↾₀ f) := by
    ext x
    rw [mem_ran_toSetRestrictedTo_iff hres, MemStructure.mem_dom_iff]
    constructor
    · rintro ⟨y, hxy⟩
      exact ⟨!(x, y), hxy, left_orderedPair⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨u, v, rfl⟩ := hrel hz
      rw [left_orderedPair]
      exact ⟨v, hz⟩
  rw [h]
  exact hf.image

/-- The levels `𝕍 n` for `n ∈ ω` are finite -/
theorem finite_vonNeumann (hn : n ∈ (ω : M)) : Finite (𝕍 n) := by
  refine omega_induction (A := fun n ↦ Finite (𝕍 n)) ?_ (fun n hn ih ↦ ?_) hn
  · rw [vonNeumann_empty]
    exact finite_empty
  rw [vonNeumann_succ (ordinal_of_mem ordinal_omega hn)]
  exact ih.powerset

theorem empty_mem_vonNeumann_omega : (∅ : M) ∈ (𝕍 ω : M) := by
  have h := vonNeumann_mem_vonNeumann (M := M) ⟨ordinal_empty, ordinal_omega, empty_mem_omega⟩
  rwa [vonNeumann_empty] at h

/-- The elements of `𝕍 ω` are in `𝕍 ω` -/
theorem mem_vonNeumann_omega_of_mem (hx : x ∈ (𝕍 ω : M)) (hy : y ∈ x) : y ∈ (𝕍 ω : M) :=
  transitive_vonNeumann ordinal_omega x hx hy

/-- The subsets of the sets in `𝕍 ω` are in `𝕍 ω` -/
theorem mem_vonNeumann_omega_of_subset (hx : x ∈ (𝕍 ω : M)) (hy : y ⊆ x) : y ∈ (𝕍 ω : M) :=
  mem_vonNeumann_of_subset ordinal_omega hx hy

/-- The sets in `𝕍 ω` are finite -/
theorem Finite.of_mem_vonNeumann_omega (hx : x ∈ (𝕍 ω : M)) : Finite x := by
  rw [nonZeroLimOrdinal_omega.mem_vonNeumann_iff] at hx
  obtain ⟨β, hβ, hxβ⟩ := hx
  exact (finite_vonNeumann hβ).of_subset
    (transitive_vonNeumann (ordinal_of_mem ordinal_omega hβ) x hxβ)

theorem singleton_mem_vonNeumann_omega (ha : a ∈ (𝕍 ω : M)) : ({a} : M) ∈ (𝕍 ω : M) := by
  rw [singleton_eq]
  exact nonZeroLimOrdinal_omega.unorderedPair_mem_vonNeumann ha ha

theorem insert_mem_vonNeumann_omega (ha : a ∈ (𝕍 ω : M)) (hx : x ∈ (𝕍 ω : M)) :
    insert a x ∈ (𝕍 ω : M) := by
  rw [insert_eq]
  exact nonZeroLimOrdinal_omega.union_mem_vonNeumann (singleton_mem_vonNeumann_omega ha) hx

/-- Finite subsets of `𝕍 ω` are in `𝕍 ω` -/
theorem Finite.mem_vonNeumann_omega (hx : Finite x) (h : x ⊆ (𝕍 ω : M)) : x ∈ (𝕍 ω : M) := by
  refine hx.induction (A := fun x ↦ x ⊆ (𝕍 ω : M) → x ∈ (𝕍 ω : M))
    (fun _ ↦ empty_mem_vonNeumann_omega) (fun x a ih h ↦ ?_) h
  have ha : a ∈ (𝕍 ω : M) := h (mem_insert a x)
  have hx : x ⊆ (𝕍 ω : M) := fun z hz ↦ h (subset_insert (x := a) x hz)
  exact insert_mem_vonNeumann_omega ha (ih hx)

/-- `𝕍 ω` consists of the hereditarily finite sets -/
theorem mem_vonNeumann_omega_iff : x ∈ (𝕍 ω : M) ↔ Finite x ∧ x ⊆ (𝕍 ω : M) :=
  ⟨fun hx ↦ ⟨Finite.of_mem_vonNeumann_omega hx, fun _ hy ↦ mem_vonNeumann_omega_of_mem hx hy⟩,
    fun h ↦ h.left.mem_vonNeumann_omega h.right⟩

/-- The natural numbers are in `𝕍 ω` -/
theorem mem_vonNeumann_omega_of_mem_omega (hn : n ∈ (ω : M)) : n ∈ (𝕍 ω : M) :=
  subset_vonNeumann ordinal_omega hn

theorem natCast_mem_vonNeumann_omega (k : ℕ) : (k : M) ∈ (𝕍 ω : M) :=
  mem_vonNeumann_omega_of_mem_omega (natCast_mem_omega k)

theorem orderedPair_mem_vonNeumann_omega (ha : a ∈ (𝕍 ω : M)) (hb : b ∈ (𝕍 ω : M)) :
    !(a, b) ∈ (𝕍 ω : M) :=
  nonZeroLimOrdinal_omega.orderedPair_mem_vonNeumann ha hb

/-- The components of a pair in `𝕍 ω` are in `𝕍 ω` -/
theorem mem_vonNeumann_omega_of_orderedPair_mem (h : !(a, b) ∈ (𝕍 ω : M)) :
    a ∈ (𝕍 ω : M) ∧ b ∈ (𝕍 ω : M) := by
  have hab : unorderedPair a b ∈ (𝕍 ω : M) := by
    refine mem_vonNeumann_omega_of_mem h ?_
    rw [mem_orderedPair_iff]
    exact .inr rfl
  exact ⟨mem_vonNeumann_omega_of_mem hab ((mem_unorderedPair_iff ..).mpr (.inl rfl)),
    mem_vonNeumann_omega_of_mem hab ((mem_unorderedPair_iff ..).mpr (.inr rfl))⟩

theorem sprod_mem_vonNeumann_omega (ha : a ∈ (𝕍 ω : M)) (hb : b ∈ (𝕍 ω : M)) :
    a ×ˢ b ∈ (𝕍 ω : M) :=
  nonZeroLimOrdinal_omega.sprod_mem_vonNeumann ha hb

theorem powerset_mem_vonNeumann_omega (ha : a ∈ (𝕍 ω : M)) : 𝒫 a ∈ (𝕍 ω : M) :=
  nonZeroLimOrdinal_omega.powerset_mem_vonNeumann ha

theorem union_mem_vonNeumann_omega (ha : a ∈ (𝕍 ω : M)) (hb : b ∈ (𝕍 ω : M)) :
    a ∪ b ∈ (𝕍 ω : M) :=
  nonZeroLimOrdinal_omega.union_mem_vonNeumann ha hb

/-- A function with domain in `𝕍 ω` and values in `𝕍 ω` is in `𝕍 ω` -/
theorem IsFunction.mem_vonNeumann_omega (hf : IsFunction f) (hd : dom f ∈ (𝕍 ω : M))
    (hv : ∀ x ∈ dom f, f ﹫ x ∈ (𝕍 ω : M)) : f ∈ (𝕍 ω : M) := by
  have hran : Finite (ran f) :=
    (Finite.of_mem_vonNeumann_omega hd).of_isSurjectionFromTo ⟨⟨hf, rfl, subset_refl _⟩, rfl⟩
  have hranV : ran f ∈ (𝕍 ω : M) := by
    refine hran.mem_vonNeumann_omega fun y hy ↦ ?_
    rw [IsFunction.mem_ran_iff y hf] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hv x hx
  refine mem_vonNeumann_omega_of_subset (sprod_mem_vonNeumann_omega hd hranV) fun z hz ↦ ?_
  obtain ⟨x, y, rfl⟩ := hf.isRelation hz
  rw [pair_mem_sprod_iff]
  exact ⟨(MemStructure.mem_dom_iff f x).mpr ⟨y, hz⟩, (MemStructure.mem_ran_iff f y).mpr ⟨x, hz⟩⟩

/-- The domain of a set in `𝕍 ω` is in `𝕍 ω` -/
theorem dom_mem_vonNeumann_omega (hf : f ∈ (𝕍 ω : M)) : dom f ∈ (𝕍 ω : M) := by
  have hU := sUnion_mem_vonNeumann ordinal_omega (sUnion_mem_vonNeumann ordinal_omega hf)
  refine mem_vonNeumann_omega_of_subset hU fun x hx ↦ ?_
  rw [MemStructure.mem_dom_iff] at hx
  obtain ⟨y, hxy⟩ := hx
  rw [mem_sUnion_iff]
  refine ⟨unorderedPair x x, ?_, (mem_unorderedPair_iff ..).mpr (.inl rfl)⟩
  rw [mem_sUnion_iff]
  exact ⟨!(x, y), hxy, (mem_orderedPair_iff ..).mpr (.inl rfl)⟩

/-- The values of a function in `𝕍 ω` are in `𝕍 ω` -/
theorem IsFunction.val_mem_vonNeumann_omega (hf : IsFunction f) (hfV : f ∈ (𝕍 ω : M)) (x : M) :
    f ﹫ x ∈ (𝕍 ω : M) := by
  by_cases hx : x ∈ dom f
  · exact (mem_vonNeumann_omega_of_orderedPair_mem
      (mem_vonNeumann_omega_of_mem hfV (rel_val hf hx))).right
  · rw [val_eq_empty_of_not_mem_dom hx]
    exact empty_mem_vonNeumann_omega

/-- Appending a value in `𝕍 ω` to a function in `𝕍 ω` gives a function in `𝕍 ω` -/
theorem IsFunction.cc_mem_vonNeumann_omega (hf : IsFunction f) (hfV : f ∈ (𝕍 ω : M))
    (ha : a ∈ (𝕍 ω : M)) : MemStructure.cc f a ∈ (𝕍 ω : M) := by
  have hd := dom_mem_vonNeumann_omega hfV
  refine (hf.cc a).mem_vonNeumann_omega ?_ fun x hx ↦ ?_
  · rw [dom_cc]
    exact insert_mem_vonNeumann_omega hd hd
  rw [dom_cc] at hx
  rcases mem_or_eq_of_mem_succ hx with hx | rfl
  · rw [cc_val_of_mem hf a hx]
    exact hf.val_mem_vonNeumann_omega hfV x
  · rw [cc_val_self hf]
    exact ha

end FirstOrder.Language.MemStructure
