/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Ordinal.Omega
import Astlib.Basic.Axiom.ZF.Semantics
/-!
# The von Neumann hierarchy

* `rank x = ⋃_{y ∈ x} succ (rank y)`, defined by a primitive recursive term, is an ordinal in
  models of `KP`, with `rank y <ₒ rank x` for `y ∈ x`.
* In models of `ZF⁻` with all power sets (i.e. of `ZF`), `𝕍 α` is defined by recursion on `α`:
  `𝕍 ∅ = ∅`, `𝕍 (succ α) = 𝒫 (𝕍 α)`, and `𝕍 α = ⋃_{β ∈ α} 𝕍 β` for limits `α`. The sets in
  `𝕍 α` are those of rank below `α` (`mem_vonNeumann_iff`); in particular `x ∈ 𝕍 (succ (rank x))`
  and `x ∉ 𝕍 (rank x)`. Each `𝕍 α` is transitive, and the hierarchy is increasing.
-/

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula PrimitiveRecursiveTerm Fin
  MemStructure

namespace FirstOrder.Language

/-- The step `f ↦ ⋃_{y ∈ dom f} succ (f ﹫ y)` of `rank₀` -/
noncomputable def PrimitiveRecursiveTerm.rankStep₀ {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.PrimitiveRecursiveTerm 1 :=
  PrimitiveRecursiveTerm.iUnion (ᵣ0 : L.RudimentaryTerm 1).dom.toPrimitiveRecursiveTerm
    ((ᵣ0 : L.RudimentaryTerm 2) ﹫ ᵣ1).succ.toPrimitiveRecursiveTerm

/-- The rank `rank x = ⋃_{y ∈ x} succ (rank y)` as a primitive recursive term -/
noncomputable def PrimitiveRecursiveTerm.rank₀ {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.PrimitiveRecursiveTerm 1 :=
  recursion rankStep₀

namespace MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] {x y z α β : M}

section Rank

variable [ModelsKP M]

/-- The rank `rank x = ⋃_{y ∈ x} succ (rank y)` -/
noncomputable def rank : ClassFunction M := fun x ↦ rank₀〘x〙₁

omit [ModelsKP M] in
theorem rank_eq_realize : (rank : ClassFunction M) = fun y ↦ (rank₀〘snoc ![] y〙 : M) := by
  funext
  simp [rank]

instance : ClassFunction.Sigma (rank : ClassFunction M) 1 Set.univ := by
  unfold rank
  infer_instance

theorem mem_rank_iff : z ∈ rank x ↔ ∃ y ∈ x, z ∈ succ (rank y) := by
  have := realize_recursion (xs := ![x]) (rg := rankStep₀ (L := L))
  rw [Subsingleton.elim (![x] ∘ Fin.castSucc) ![], ← rank₀, ← rank_eq_realize] at this
  have hres : IsSetRestrictedTo rank x := isSetRestrictedTo_of_modelsKP _ x
  change z ∈ rank₀〘x〙₁ ↔ _
  rw [this, rankStep₀, mem_realize_iUnion_iff]
  have key : (∃ y ∈ x, z ∈ succ ((rank ↾₀ x) ﹫ y)) ↔ ∃ y ∈ x, z ∈ succ (rank y) :=
    exists_congr fun y ↦ and_congr_right fun hy ↦ by rw [val_toSetRestrictedTo hres hy]
  simpa [dom_toSetRestrictedTo hres] using key

@[grind .]
theorem ordinal_rank (x : M) : Ordinal (rank x) := by
  refine induction_of_modelsKP (A := fun x ↦ Ordinal (rank x)) (fun x ih ↦ ?_) x
  have hmem {z : M} (hz : z ∈ rank x) : Ordinal z := by
    rw [mem_rank_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    exact ordinal_of_mem (ordinal_succ (ih y hy)) hz
  refine ⟨fun z hz w hw ↦ ?_, fun z hz w hw ↦ ordinal_compatible (hmem hz) (hmem hw)⟩
  simp only [mem_rank_iff] at hz ⊢
  obtain ⟨y, hy, hz⟩ := hz
  exact ⟨y, hy, (ordinal_succ (ih y hy)).transitive z hz hw⟩

/-- The rank of an element is below the rank -/
theorem rank_olt_of_mem (hy : y ∈ x) : rank y <ₒ rank x := by
  refine olt_of_mem (ordinal_rank x) ?_
  rw [mem_rank_iff]
  exact ⟨y, hy, mem_succ_self _⟩

/-- `rank x ≤ₒ β` iff the ranks of the elements of `x` are below `β` -/
theorem rank_ole_iff (hβ : Ordinal β) : rank x ≤ₒ β ↔ ∀ y ∈ x, rank y <ₒ β := by
  refine ⟨fun h y hy ↦ olt_of_olt_of_ole (rank_olt_of_mem hy) h, fun h ↦ ?_⟩
  rw [ole_iff_subset (ordinal_rank x) hβ]
  intro z hz
  rw [mem_rank_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  have hsucc : succ (rank y) ≤ₒ β := by
    simp only [succ_ole_iff (ordinal_rank y) hβ]
    exact h y hy
  rw [ole_iff_subset (ordinal_succ (ordinal_rank y)) hβ] at hsucc
  exact hsucc hz

/-- The rank of an ordinal is itself -/
@[simp]
theorem rank_ordinal (hα : Ordinal α) : rank α = α := by
  refine ordinal_induction (A := fun α ↦ rank α = α) (fun α hα ih ↦ ?_) hα
  ext z
  simp only [mem_rank_iff]
  refine ⟨fun ⟨y, hy, hz⟩ ↦ ?_, fun hz ↦ ⟨z, hz, ?_⟩⟩
  · rw [ih y (olt_of_mem hα hy)] at hz
    rcases mem_or_eq_of_mem_succ hz with hz | rfl
    · exact hα.transitive y hy hz
    · exact hy
  · rw [ih z (olt_of_mem hα hz)]
    exact mem_succ_self z

end Rank

section VonNeumann

variable [ModelsZF M]

/-- The von Neumann hierarchy: `𝕍 ∅ = ∅`, `𝕍 (succ α) = 𝒫 (𝕍 α)`, and `𝕍 α` is the union of
`𝕍 β` for `β ∈ α` at limits `α` -/
noncomputable def vonNeumann : ClassFunction M := ordRecursion' ∅ powerset (sUnion.comp ran)

@[inherit_doc] prefix:max "𝕍" => FirstOrder.Language.MemStructure.vonNeumann

instance : (vonNeumann : ClassFunction M).Definable Set.univ := by
  unfold vonNeumann
  infer_instance

@[simp, grind =]
theorem vonNeumann_empty : 𝕍 (∅ : M) = ∅ := ordRecursion'_empty

theorem vonNeumann_succ (hα : Ordinal α) : 𝕍 (succ α) = 𝒫 (𝕍 α) := ordRecursion'_succ hα

/-- At a limit `α`, `𝕍 α` is the union of `𝕍 β` for `β ∈ α` -/
theorem NonZeroLimOrdinal.vonNeumann_eq (hα : NonZeroLimOrdinal α) :
    𝕍 α = ⋃₀ ran (vonNeumann ↾₀ α) :=
  hα.ordRecursion'_eq

@[simp]
theorem mem_vonNeumann_succ_iff (hα : Ordinal α) : x ∈ 𝕍 (succ α) ↔ x ⊆ 𝕍 α := by
  rw [vonNeumann_succ hα, mem_powerset_iff]

/-- At a limit `α`, `x ∈ 𝕍 α` iff `x ∈ 𝕍 β` for some `β ∈ α` -/
theorem NonZeroLimOrdinal.mem_vonNeumann_iff (hα : NonZeroLimOrdinal α) :
    x ∈ 𝕍 α ↔ ∃ β ∈ α, x ∈ 𝕍 β := by
  simp only [hα.vonNeumann_eq, mem_sUnion_iff, mem_ran_toSetRestrictedTo_iff,
    isSetRestrictedTo_of_definable α]
  grind

/-- The sets in `𝕍 α` are those of rank below `α` -/
theorem mem_vonNeumann_iff (hα : Ordinal α) : x ∈ 𝕍 α ↔ rank x <ₒ α := by
  suffices ∀ x, x ∈ 𝕍 α ↔ rank x <ₒ α from this x
  refine ordinal_induction' (A := fun α ↦ ∀ x, x ∈ 𝕍 α ↔ rank x <ₒ α) (by grind)
    (fun β hβ ih x ↦ ?_) (fun α hα ih x ↦ ?_) hα
  · rw [mem_vonNeumann_succ_iff hβ, olt_succ_iff hβ, rank_ole_iff hβ]
    exact forall₂_congr fun y _ ↦ ih y
  rw [hα.mem_vonNeumann_iff]
  refine ⟨fun ⟨β, hβ, hxβ⟩ ↦ ?_, fun h ↦ ⟨succ (rank x), (hα.succ_olt h).mem, ?_⟩⟩
  · have hβo := olt_of_mem hα.ordinal hβ
    rw [ih β hβo x] at hxβ
    exact olt_trans hxβ hβo
  · rw [ih (succ (rank x)) (hα.succ_olt h) x]
    exact olt_succ (ordinal_rank x)

/-- `x ∈ 𝕍 (succ (rank x))` -/
theorem mem_vonNeumann_succ_rank (x : M) : x ∈ 𝕍 (succ (rank x)) := by
  rw [mem_vonNeumann_iff (ordinal_succ (ordinal_rank x))]
  exact olt_succ (ordinal_rank x)

/-- `x ∉ 𝕍 (rank x)` -/
theorem notMem_vonNeumann_rank (x : M) : x ∉ 𝕍 (rank x) := by
  rw [mem_vonNeumann_iff (ordinal_rank x)]
  exact olt_irrefl _

/-- `𝕍 α` is transitive -/
theorem transitive_vonNeumann (hα : Ordinal α) : Transitive (𝕍 α) := by
  intro x hx y hy
  rw [mem_vonNeumann_iff hα] at hx ⊢
  exact olt_trans (rank_olt_of_mem hy) hx

/-- The von Neumann hierarchy is increasing -/
theorem vonNeumann_mono (hα : Ordinal α) (hαβ : α ≤ₒ β) : 𝕍 α ⊆ 𝕍 β := by
  intro x hx
  rw [mem_vonNeumann_iff hα] at hx
  rw [mem_vonNeumann_iff hαβ.ordinal_right]
  exact olt_of_olt_of_ole hx hαβ

/-- `𝕍 α ∈ 𝕍 (succ α)` -/
theorem vonNeumann_mem_vonNeumann_succ (hα : Ordinal α) : 𝕍 α ∈ 𝕍 (succ α) := by
  simp only [mem_vonNeumann_succ_iff hα]
  exact subset_refl _

/-- `𝕍 α ∈ 𝕍 β` for `α <ₒ β` -/
theorem vonNeumann_mem_vonNeumann (hαβ : α <ₒ β) : 𝕍 α ∈ 𝕍 β := by
  have hα := hαβ.ordinal_left
  exact vonNeumann_mono (ordinal_succ hα) ((succ_ole_iff hα hαβ.ordinal_right).mpr hαβ)
    (vonNeumann_mem_vonNeumann_succ hα)

/-- The von Neumann hierarchy is strictly increasing -/
theorem vonNeumann_ssubset (hαβ : α <ₒ β) : 𝕍 α ⊆ 𝕍 β ∧ 𝕍 α ≠ 𝕍 β := by
  refine subset_ne_of_succ_of_limit (fun α hα ↦ ⟨fun x hx ↦ ?_, fun h ↦ ?_⟩)
    (fun α hα x ↦ hα.mem_vonNeumann_iff) hαβ.ordinal_right hαβ.mem
  · simp only [mem_vonNeumann_succ_iff hα]
    exact transitive_vonNeumann hα x hx
  · -- `𝕍 α ∈ 𝕍 (succ α)` but `𝕍 α ∉ 𝕍 α`
    have hmem := vonNeumann_mem_vonNeumann_succ hα
    rw [← h] at hmem
    exact notMem_self _ hmem

/-- `α ⊆ 𝕍 α` -/
theorem subset_vonNeumann (hα : Ordinal α) : α ⊆ 𝕍 α := by
  intro β hβ
  have hβo := olt_of_mem hα hβ
  rwa [mem_vonNeumann_iff hα, rank_ordinal hβo.ordinal_left]

/-- `𝕍 α` is closed under subsets -/
theorem mem_vonNeumann_of_subset (hα : Ordinal α) {x y : M} (hx : x ∈ 𝕍 α) (hyx : y ⊆ x) :
    y ∈ 𝕍 α := by
  rw [mem_vonNeumann_iff hα] at hx ⊢
  refine olt_of_ole_of_olt ((rank_ole_iff (ordinal_rank x)).mpr fun z hz ↦ ?_) hx
  exact rank_olt_of_mem (hyx hz)

/-- `𝕍 α` is closed under unions -/
theorem sUnion_mem_vonNeumann (hα : Ordinal α) {x : M} (hx : x ∈ 𝕍 α) : ⋃₀ x ∈ 𝕍 α := by
  rw [mem_vonNeumann_iff hα] at hx ⊢
  refine olt_of_ole_of_olt ((rank_ole_iff (ordinal_rank x)).mpr fun z hz ↦ ?_) hx
  rw [mem_sUnion_iff] at hz
  obtain ⟨w, hw, hzw⟩ := hz
  exact olt_trans (rank_olt_of_mem hzw) (rank_olt_of_mem hw)

section Limit

variable {a b : M}

/-- `𝕍 α` is closed under unordered pairs at a limit `α` -/
theorem NonZeroLimOrdinal.unorderedPair_mem_vonNeumann (hα : NonZeroLimOrdinal α)
    (ha : a ∈ 𝕍 α) (hb : b ∈ 𝕍 α) : unorderedPair a b ∈ 𝕍 α := by
  rw [MemStructure.mem_vonNeumann_iff hα.ordinal] at ha hb ⊢
  -- `rank {a, b} ≤ₒ succ (omax₂ (rank a) (rank b)) <ₒ α`
  have hra := ordinal_rank a
  have hrb := ordinal_rank b
  have hmax : omax₂ (rank a) (rank b) <ₒ α := (omax₂_olt_iff hra hrb).mpr ⟨ha, hb⟩
  have hle : rank (unorderedPair a b) ≤ₒ succ (omax₂ (rank a) (rank b)) := by
    rw [rank_ole_iff (ordinal_succ (ordinal_omax₂ hra hrb))]
    intro y hy
    rcases (mem_unorderedPair_iff _ _ _).mp hy with rfl | rfl <;> grind
  exact olt_of_ole_of_olt hle (hα.succ_olt hmax)

/-- `𝕍 α` is closed under ordered pairs at a limit `α` -/
theorem NonZeroLimOrdinal.orderedPair_mem_vonNeumann (hα : NonZeroLimOrdinal α)
    (ha : a ∈ 𝕍 α) (hb : b ∈ 𝕍 α) : !(a, b) ∈ 𝕍 α :=
  hα.unorderedPair_mem_vonNeumann (hα.unorderedPair_mem_vonNeumann ha ha)
    (hα.unorderedPair_mem_vonNeumann ha hb)

/-- `𝕍 α` is closed under power sets at a limit `α` -/
theorem NonZeroLimOrdinal.powerset_mem_vonNeumann (hα : NonZeroLimOrdinal α) {x : M}
    (hx : x ∈ 𝕍 α) : 𝒫 x ∈ 𝕍 α := by
  rw [MemStructure.mem_vonNeumann_iff hα.ordinal] at hx ⊢
  have hr := ordinal_rank x
  refine olt_of_ole_of_olt ((rank_ole_iff (ordinal_succ hr)).mpr fun y hy ↦ ?_) (hα.succ_olt hx)
  rw [olt_succ_iff hr]
  refine (rank_ole_iff hr).mpr fun z hz ↦ ?_
  rw [mem_powerset_iff] at hy
  exact rank_olt_of_mem (hy hz)

/-- `𝕍 α` is closed under binary unions at a limit `α` -/
theorem NonZeroLimOrdinal.union_mem_vonNeumann (hα : NonZeroLimOrdinal α) (ha : a ∈ 𝕍 α)
    (hb : b ∈ 𝕍 α) : a ∪ b ∈ 𝕍 α := by
  have h : a ∪ b = ⋃₀ unorderedPair a b := by
    ext z
    simp [mem_union_iff, mem_sUnion_iff]
  rw [h]
  exact sUnion_mem_vonNeumann hα.ordinal (hα.unorderedPair_mem_vonNeumann ha hb)

/-- `𝕍 α` is closed under products at a limit `α` -/
theorem NonZeroLimOrdinal.sprod_mem_vonNeumann (hα : NonZeroLimOrdinal α) (ha : a ∈ 𝕍 α)
    (hb : b ∈ 𝕍 α) : a ×ˢ b ∈ 𝕍 α := by
  have hp := hα.powerset_mem_vonNeumann (hα.powerset_mem_vonNeumann (hα.union_mem_vonNeumann ha hb))
  refine mem_vonNeumann_of_subset hα.ordinal hp fun z hz ↦ ?_
  rw [mem_sprod_iff] at hz
  obtain ⟨u, hu, v, hv, rfl⟩ := hz
  rw [mem_powerset_iff]
  intro w hw
  rw [mem_orderedPair_iff] at hw
  rw [mem_powerset_iff]
  rcases hw with rfl | rfl <;> intro t ht <;> rw [mem_unorderedPair_iff] at ht <;>
    rcases ht with rfl | rfl <;> simp [mem_union_iff, hu, hv]

end Limit

end VonNeumann

end MemStructure

end FirstOrder.Language
