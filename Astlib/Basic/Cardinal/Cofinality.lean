/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Cardinal.Basic
import Astlib.Basic.Axiom.Choice.Semantics
import Astlib.Basic.Cardinal.Countable
import Astlib.Basic.Ordinal.ClubStationary
/-!
# Cofinality

A cofinal map from an ordinal `β` into `α` is a function `f !: β → α` whose range is unbounded in
`α` (`UnboundedInOrd`). The cofinality `cf α` of an ordinal `α` is the least ordinal with a
cofinal map into `α`, and `α` is regular if `cf α = α`. In models of `KP`:

* `cf_ole`: `cf α ≤ₒ α`; `cf_empty`, `cf_succ`: `cf ∅ = ∅` and `cf (succ α) = succ ∅`;
* `Regular.cardinal`: regular ordinals are cardinals;
* `regular_omega`: `ω` is regular.

If `cf α` is uncountable, the intersection of fewer than `cf α` clubs in `α` is a club
(`ClubInOrd.sInter`), in particular so is the intersection of two clubs (`ClubInOrd.inter`), and
every club in `α` is stationary (`ClubInOrd.stationary`). If `α` is an uncountable regular ordinal,
the diagonal intersection of `α` clubs in `α` is a club (`ClubInOrd.diagInter`).

In models of `ZFC`, the successor cardinal `csucc κ` of an infinite ordinal `κ` is regular
(`regular_csucc`): a cofinal map `f` from `β ∈ csucc κ` together with chosen injections
`f ﹫ ξ ↪ κ` and a choice of `ξ` with `x ∈ f ﹫ ξ` for each `x` would give
`csucc κ ↪ β ×ˢ κ ↪ κ ×ˢ κ ↪ κ`.

In models of `ZF` with countable choice, `ℵ₁` is regular (`regular_aleph_one`): a cofinal map
from a countable ordinal would make `ℵ₁` a countable union of countable ordinals.
-/

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin RudimentaryTerm MemStructure

namespace FirstOrder.Language

namespace MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] {α β f : M}

/-- `f` is a cofinal map from the ordinal `β` into `α`: its range is unbounded in `α` -/
def IsCofinalMap (f β α : M) : Prop := Ordinal β ∧ f !: β → α ∧ UnboundedInOrd (ran f) α

omit [ModelsKP M] in
theorem IsCofinalMap.ordinal (hf : IsCofinalMap f β α) : Ordinal β := hf.left

omit [ModelsKP M] in
theorem IsCofinalMap.isFunctionFromTo (hf : IsCofinalMap f β α) : f !: β → α := hf.right.left

omit [ModelsKP M] in
theorem IsCofinalMap.unboundedInOrd (hf : IsCofinalMap f β α) : UnboundedInOrd (ran f) α :=
  hf.right.right

theorem IsCofinalMap.exists_ole (hf : IsCofinalMap f β α) {γ : M} (hγ : γ <ₒ α) :
    ∃ ξ <ₒ β, γ ≤ₒ f ﹫ ξ := by
  obtain ⟨y, hy, hγy⟩ := hf.unboundedInOrd.exists_ole hγ
  simp only [hf.isFunctionFromTo.isFunction.mem_ran_iff, hf.isFunctionFromTo.dom_eq] at hy
  obtain ⟨ξ, hξ, rfl⟩ := hy
  exact ⟨ξ, olt_of_mem hf.ordinal hξ, hγy⟩

/-- A function from an ordinal `β` whose values are unbounded in the ordinal `α` is a cofinal
map -/
theorem isCofinalMap_of_val (hα : Ordinal α) (hβ : Ordinal β) (hf : f !: β → α)
    (h : ∀ γ <ₒ α, ∃ ξ <ₒ β, γ ≤ₒ f ﹫ ξ) : IsCofinalMap f β α := by
  refine ⟨hβ, hf, ?_⟩
  simp only [unboundedInOrd_iff hα]
  intro γ hγ
  obtain ⟨ξ, hξ, hγξ⟩ := h γ hγ
  refine ⟨f ﹫ ξ, ?_, hγξ⟩
  simp only [hf.isFunction.mem_ran_iff, hf.dom_eq]
  exact ⟨ξ, hξ.mem, rfl⟩

@[grind .]
theorem isCofinalMap_id (hα : Ordinal α) : IsCofinalMap (id α) α α := by
  refine isCofinalMap_of_val hα hα (isFunctionFromTo_id α) fun γ hγ ↦ ⟨γ, hγ, ?_⟩
  rw [id_val α hγ.mem]
  exact ole_refl hγ.ordinal_left

/-- The class of ordinals with a cofinal map into `x` -/
def HasCofinalMap (x : M) : Class M := fun β ↦ ∃ f, IsCofinalMap f β x

/-- `IsCofinalMap` is definable -/
instance : Multiclass.Definable (fun ys : Fin 3 → M ↦ IsCofinalMap (ys 0) (ys 1) (ys 2))
    Set.univ := by
  unfold IsCofinalMap
  infer_instance

/-- `HasCofinalMap x β` is definable in `x` and `β` -/
instance : Multiclass.Definable (fun ys : Fin 2 → M ↦ HasCofinalMap (ys 0) (ys 1)) Set.univ := by
  unfold HasCofinalMap
  infer_instance

/-- The cofinality of `x`: the least ordinal with a cofinal map into `x` -/
noncomputable def cf : ClassFunction M := fun x ↦ (HasCofinalMap x).omin

@[grind .]
theorem ordinal_cf (x : M) : Ordinal (cf x) :=
  Class.ordinal_omin _

theorem exists_isCofinalMap_cf (hα : Ordinal α) : ∃ f, IsCofinalMap f (cf α) α :=
  Class.omin_mem (A := HasCofinalMap α) hα ⟨_, isCofinalMap_id hα⟩

theorem cf_ole_of_isCofinalMap (hβ : Ordinal β) (hf : IsCofinalMap f β α) : cf α ≤ₒ β :=
  Class.omin_ole hβ ⟨f, hf⟩

@[grind .]
theorem cf_ole (hα : Ordinal α) : cf α ≤ₒ α :=
  cf_ole_of_isCofinalMap hα (isCofinalMap_id hα)

/-- The supremum of the values of a function from an ordinal `β <ₒ cf α` into `α` is below `α` -/
theorem osup_ran_olt_of_olt_cf (hα : Ordinal α) (hβ : β <ₒ cf α) (hf : f !: β → α) :
    osup (ran f) <ₒ α := by
  have hran : ∀ y ∈ ran f, Ordinal y := fun y hy ↦ ordinal_of_mem hα (hf.ran_subset hy)
  refine olt_of_ole_of_ne ?_ fun h ↦ ?_
  · rw [osup_ole_iff hran hα]
    exact fun y hy ↦ olt_of_mem hα (hf.ran_subset hy) |>.ole
  -- otherwise `f` is a cofinal map from `β`
  have hcof : IsCofinalMap f β α := by
    refine isCofinalMap_of_val hα hβ.ordinal_left hf fun δ hδ ↦ ?_
    rw [← h, olt_osup_iff hran hδ.ordinal_left] at hδ
    obtain ⟨y, hy, hδy⟩ := hδ
    rw [hf.isFunction.mem_ran_iff, hf.dom_eq] at hy
    obtain ⟨n, hn, rfl⟩ := hy
    exact ⟨n, olt_of_mem hβ.ordinal_left hn, hδy.ole⟩
  grind [cf_ole_of_isCofinalMap hβ.ordinal_left hcof]

@[simp, grind =]
theorem cf_empty : cf (∅ : M) = ∅ := by
  grind [cf_ole (α := (∅ : M)) (by grind)]

/-- A nonzero ordinal has nonzero cofinality -/
theorem cf_ne_empty (hα : Ordinal α) (hα₀ : α ≠ ∅) : cf α ≠ ∅ := by
  intro h
  obtain ⟨f, hf⟩ := exists_isCofinalMap_cf hα
  rw [h] at hf
  grind [hf.exists_ole (γ := ∅) (by grind)]

@[simp, grind =]
theorem cf_succ (hα : Ordinal α) : cf (succ α) = succ ∅ := by
  -- `singletonFun ∅ α` is a cofinal map from `succ ∅` into `succ α`
  have hcf : IsCofinalMap (singletonFun ∅ α) (succ ∅) (succ α) := by
    refine isCofinalMap_of_val (by grind) (by grind) ?_ fun γ hγ ↦ ⟨∅, olt_succ ordinal_empty, ?_⟩
    · convert isFunctionFromTo_singletonFun (mem_succ_self α)
      simp [succ_empty]
    · simp only [singletonFun_val]
      grind
  refine ole_antisymm (cf_ole_of_isCofinalMap (by grind) hcf) ?_
  simp only [succ_ole_iff ordinal_empty (ordinal_cf _)]
  exact olt_of_ole_of_ne (by grind) (by grind [cf_ne_empty])

/-- A nonzero limit ordinal has a nonzero limit cofinality -/
theorem NonZeroLimOrdinal.nonZeroLimOrdinal_cf (hα : NonZeroLimOrdinal α) :
    NonZeroLimOrdinal (cf α) := by
  obtain ⟨f, hf⟩ := exists_isCofinalMap_cf hα.ordinal
  by_contra hl
  obtain ⟨β, hβ, h⟩ := (ordinal_cf α).exists_eq_succ (cf_ne_empty hα.ordinal hα.ne_empty) hl
  rw [h] at hf
  -- some `ξ₀ <ₒ β` has `f ﹫ β <ₒ f ﹫ ξ₀`, so `f ↾ β` is cofinal and `succ β = cf α ≤ₒ β`
  have hfβ : f ﹫ β <ₒ α := olt_of_mem hα.ordinal (hf.isFunctionFromTo.val_mem (by grind))
  obtain ⟨ξ₀, hξ₀, hξ₀f⟩ := hf.exists_ole (γ := succ (f ﹫ β)) (by grind)
  have hlt : f ﹫ β <ₒ f ﹫ ξ₀ := by grind
  have hξ₀β : ξ₀ <ₒ β := by grind
  have hcf : IsCofinalMap (f ↾ β) β α := by
    refine isCofinalMap_of_val hα.ordinal hβ (hf.isFunctionFromTo.restrict (by grind))
      fun γ hγ ↦ ?_
    obtain ⟨ξ, hξ, hγξ⟩ := hf.exists_ole hγ
    have hval {ζ : M} (hζ : ζ <ₒ β) : (f ↾ β) ﹫ ζ = f ﹫ ζ :=
      val_restrict _ hf.isFunctionFromTo.isFunction hζ.mem
        (by rw [hf.isFunctionFromTo.dom_eq]; exact mem_succ_of_mem hζ.mem)
    rcases mem_or_eq_of_ole ((olt_succ_iff hβ).mp hξ) with h | rfl
    · grind [hval (olt_of_mem hβ h)]
    · grind [hval hξ₀β]
  have : cf α ≤ₒ β := cf_ole_of_isCofinalMap hβ hcf
  grind

/-- The cofinality of an ordinal is its own cofinality -/
@[simp, grind =]
theorem cf_cf (hα : Ordinal α) : cf (cf α) = cf α := by
  refine ole_antisymm (cf_ole (ordinal_cf α)) ?_
  rcases hα.cases with rfl | ⟨β, hβ, rfl⟩ | hlim
  · simp
  · simp [hβ]
  -- compose a cofinal map `g` into `cf α` with the suprema of a cofinal map `f` into `α`
  obtain ⟨f, hf⟩ := exists_isCofinalMap_cf hα
  obtain ⟨g, hg⟩ := exists_isCofinalMap_cf (ordinal_cf α)
  have hff := hf.isFunctionFromTo
  have hgf := hg.isFunctionFromTo
  have hres := isSetRestrictedTo_of_sigma
    (G := (supRange f).comp fun η ↦ g ﹫ η) (cf (cf α))
  have hr (y : M) (hy : y ∈ ran f) : Ordinal y := by grind
  have hgη {η : M} (hη : η <ₒ cf (cf α)) : g ﹫ η <ₒ cf α := by grind
  have hdom {η : M} (hη : η <ₒ cf (cf α)) : g ﹫ η ⊆ dom f := by grind
  -- `supRange f (g ﹫ η) <ₒ α` as `g ﹫ η <ₒ cf α`
  have hlt {η : M} (hη : η <ₒ cf (cf α)) : supRange f (g ﹫ η) <ₒ α :=
    osup_ran_olt_of_olt_cf hα (hgη hη) (hff.restrict (by grind))
  -- `(supRange f).comp (g ﹫ ·) ↾₀ cf (cf α)` is a cofinal map into `α`
  have hcof : IsCofinalMap (((supRange f).comp fun η ↦ g ﹫ η) ↾₀ cf (cf α)) (cf (cf α)) α := by
    refine isCofinalMap_of_val hα (ordinal_cf _)
      ⟨isFunction_toSetRestrictedTo hres, dom_toSetRestrictedTo hres, fun y hy ↦ ?_⟩
      fun γ hγ ↦ ?_
    · simp only [mem_ran_toSetRestrictedTo_iff hres] at hy
      simp only [ClassFunction.comp] at hy
      grind
    · -- `γ ≤ₒ f ﹫ ξ` and `succ ξ ≤ₒ g ﹫ η`, using that `cf α` is a limit
      obtain ⟨ξ, hξ, hγξ⟩ := hf.exists_ole hγ
      obtain ⟨η, hη, hξη⟩ := hg.exists_ole (hlim.nonZeroLimOrdinal_cf.succ_olt hξ)
      refine ⟨η, hη, ole_trans hγξ ?_⟩
      rw [val_toSetRestrictedTo hres hη.mem]
      exact val_ole_supRange hr hff.isFunction (hdom hη) (by grind)
  exact cf_ole_of_isCofinalMap (ordinal_cf _) hcof

/-- `α` is regular: its cofinality is `α` -/
def Regular : Class M := fun α ↦ Ordinal α ∧ cf α = α

omit [ModelsKP M] in
@[grind .]
theorem Regular.ordinal (hα : Regular α) : Ordinal α := hα.left

omit [ModelsKP M] in
@[simp, grind =]
theorem Regular.cf_eq (hα : Regular α) : cf α = α := hα.right

/-- The cofinality of an ordinal is regular -/
theorem regular_cf (hα : Ordinal α) : Regular (cf α) := ⟨ordinal_cf α, cf_cf hα⟩

/-- A surjection from an ordinal onto an ordinal is a cofinal map -/
@[grind .]
theorem IsSurjectionFromTo.isCofinalMap (hα : Ordinal α) (hβ : Ordinal β) (hf : f !: β ↠ α) :
    IsCofinalMap f β α := by
  refine ⟨hβ, hf.isFunctionFromTo, fun γ hγ ↦ ⟨γ, ?_, ole_refl (ordinal_of_mem hα hγ)⟩⟩
  rwa [hf.ran_eq]

/-- Regular ordinals are cardinals -/
@[grind .]
theorem Regular.cardinal (hα : Regular α) : Cardinal α := by
  refine ⟨hα.ordinal, fun β hβ f hf ↦ ?_⟩
  have h := cf_ole_of_isCofinalMap (by grind) (hf.isCofinalMap hα.ordinal (by grind))
  rw [hα.cf_eq] at h
  grind

section Omega

variable [HasOmega M] {n : M}

/-- A function from a natural number into `ω` is bounded in `ω` -/
theorem exists_bound_of_mem_omega (hn : n ∈ (ω : M)) (hf : f !: n → ω) :
    ∃ m ∈ (ω : M), ∀ ξ ∈ n, f ﹫ ξ ∈ m := by
  refine omega_induction
    (A := fun n : M ↦ ∀ f : M, f !: n → ω → ∃ m ∈ (ω : M), ∀ ξ ∈ n, f ﹫ ξ ∈ m)
    (fun f _ ↦ ⟨∅, empty_mem_omega, by simp⟩)
    (fun n hn ih f hf ↦ ?_) hn f hf
  -- bound `f ↾ n` by `m`, and take `omax₂ m (succ (f ﹫ n))`
  have hfn : f ↾ n !: n → ω := hf.restrict (by grind)
  obtain ⟨m, hm, hmf⟩ := ih (f ↾ n) hfn
  have hs : succ (f ﹫ n) ∈ (ω : M) := by grind
  refine ⟨omax₂ m (succ (f ﹫ n)), by grind, fun ξ hξ ↦ ?_⟩
  rcases mem_or_eq_of_mem_succ hξ with hξ | rfl
  · have := hmf ξ hξ
    rw [val_restrict f hf.isFunction hξ (by grind)] at this
    simp [this]
  · simp

/-- `ω` is regular -/
@[grind .]
theorem regular_omega : Regular (ω : M) := by
  refine ⟨ordinal_omega, ole_antisymm (cf_ole ordinal_omega) ?_⟩
  by_contra h
  simp only [not_ole_iff ordinal_omega (ordinal_cf _)] at h
  -- a cofinal map from a natural number is bounded by some `m ∈ ω`
  obtain ⟨f, hf⟩ := exists_isCofinalMap_cf (ordinal_omega (M := M))
  obtain ⟨m, hm, hmf⟩ := exists_bound_of_mem_omega h.mem hf.isFunctionFromTo
  obtain ⟨ξ, hξ, hmξ⟩ := hf.exists_ole (olt_of_mem ordinal_omega hm)
  grind

end Omega

section ClubInOrd

variable [HasOmega M] {C D : M}

/-- An ordinal of uncountable cofinality is a nonzero limit ordinal -/
theorem nonZeroLimOrdinal_of_omega_olt_cf (hα : Ordinal α) (hcf : (ω : M) <ₒ cf α) :
    NonZeroLimOrdinal α := by
  rcases hα.cases with rfl | ⟨β, hβ, rfl⟩ | hlim <;> grind

/-- If `cf α` is uncountable and every `x <ₒ α` has some `η` above it below `α` with `R x η`, then
every `γ <ₒ α` is below a limit `lam <ₒ α` such that cofinally many `x <ₒ lam` have such an `η`
below `lam` -/
theorem exists_nonZeroLimOrdinal_iterate {R : M → M → Prop}
    [Multiclass.DeltaZero (fun ys : Fin 2 → M ↦ R (ys 0) (ys 1)) Set.univ]
    (hα : Ordinal α) (hcf : (ω : M) <ₒ cf α) (hR : ∀ x <ₒ α, ∃ η <ₒ α, x <ₒ η ∧ R x η)
    {γ : M} (hγ : γ <ₒ α) :
    ∃ lam <ₒ α, NonZeroLimOrdinal lam ∧ γ ≤ₒ lam ∧
      ∀ δ <ₒ lam, ∃ x <ₒ lam, δ <ₒ x ∧ ∃ η <ₒ lam, x <ₒ η ∧ R x η := by
  -- iterate `x ↦ G x`, the least such `η`, from `γ`
  let G : ClassFunction M := fun x ↦ Class.omin fun η ↦ η ∈ α ∧ (x <ₒ η ∧ R x η)
  have : G.Sigma 1 Set.univ := by unfold G; infer_instance
  have hG {x : M} (hx : x <ₒ α) : G x <ₒ α ∧ x <ₒ G x ∧ R x (G x) := by
    obtain ⟨η, hη, hxη, hRη⟩ := hR x hx
    have : Class.Definable (fun η ↦ η ∈ α ∧ (x <ₒ η ∧ R x η)) Set.univ :=
      definable_mem_and_of_deltaZero (R := fun x η ↦ x <ₒ η ∧ R x η) α x
    have h := Class.omin_mem (A := fun η ↦ η ∈ α ∧ (x <ₒ η ∧ R x η)) hη.ordinal_left
      ⟨hη.mem, hxη, hRη⟩
    exact ⟨olt_of_mem hα h.left, h.right⟩
  let s := natRec γ G
  have hs {n : M} (hn : n ∈ (ω : M)) : s n <ₒ α :=
    natRec_induction (A := fun x ↦ x <ₒ α) hγ (fun _ _ ih ↦ (hG ih).left) hn
  have hsucc {n : M} (hn : n ∈ (ω : M)) : s (succ n) = G (s n) := natRec_succ _ _ (by grind)
  -- `lam = osup (ran (s ↾₀ ω))`
  have hr := isSetRestrictedTo_of_sigma (G := s) ω
  have hmem {y : M} : y ∈ ran (s ↾₀ ω) ↔ ∃ n ∈ (ω : M), s n = y :=
    mem_ran_toSetRestrictedTo_iff hr
  have hran : ∀ y ∈ ran (s ↾₀ ω), Ordinal y := by
    simp only [hmem]
    grind
  set lam := osup (ran (s ↾₀ ω))
  have hlam : Ordinal lam := ordinal_osup hran
  have hle {n : M} (hn : n ∈ (ω : M)) : s n ≤ₒ lam := ole_osup hran (by grind)
  have hex {δ : M} (hδ : δ <ₒ lam) : ∃ n ∈ (ω : M), δ <ₒ s n := by
    rw [olt_osup_iff hran hδ.ordinal_left] at hδ
    obtain ⟨y, hy, hδy⟩ := hδ
    simp only [hmem] at hy
    obtain ⟨n, hn, rfl⟩ := hy
    exact ⟨n, hn, hδy⟩
  -- each `s n <ₒ s (succ n)`, so each `s n` is below `lam`
  have hlt {n : M} (hn : n ∈ (ω : M)) : s n <ₒ s (succ n) := by
    rw [hsucc hn]
    exact (hG (hs hn)).right.left
  have hs_lt {n : M} (hn : n ∈ (ω : M)) : s n <ₒ lam :=
    olt_of_olt_of_ole (hlt hn) (hle (succ_mem_omega hn))
  have hlamlim : NonZeroLimOrdinal lam := by
    refine nonZeroLimOrdinal_of_forall_exists_olt hlam ?_ fun δ hδ ↦ ?_
    · grind [hs_lt empty_mem_omega]
    · obtain ⟨n, hn, hδn⟩ := hex hδ
      exact ⟨s n, hs_lt hn, hδn⟩
  refine ⟨lam, osup_ran_olt_of_olt_cf hα hcf
    (isFunctionFromTo_toSetRestrictedTo hr fun n hn ↦ (hs hn).mem), hlamlim,
    natRec_empty γ G ▸ hle empty_mem_omega, fun δ hδ ↦ ?_⟩
  obtain ⟨n, hn, hδn⟩ := hex hδ
  refine ⟨s n, hs_lt hn, hδn, s (succ n), hs_lt (succ_mem_omega hn), hlt hn, ?_⟩
  rw [hsucc hn]
  exact (hG (hs hn)).right.right

/-- If `cf α` is uncountable, the intersection of fewer than `cf α` clubs in `α` is a club -/
theorem ClubInOrd.sInter {f : M} (hα : Ordinal α) (hcf : (ω : M) <ₒ cf α) (hf : IsFunction f)
    (hdom : dom f <ₒ cf α) (hC : ∀ S ∈ ran f, ClubInOrd S α) :
    ClubInOrd (sInterInOrd (ran f) α) α := by
  have hlim := nonZeroLimOrdinal_of_omega_olt_cf hα hcf
  refine ⟨ClosedInOrd.sInter hα fun S hS ↦ (hC S hS).closedInOrd, ?_⟩
  simp only [unboundedInOrd_iff hα]
  intro γ hγ
  have hval {ξ : M} (hξ : ξ ∈ dom f) : f ﹫ ξ ∈ ran f := (hf.mem_ran_iff _).mpr ⟨ξ, hξ, rfl⟩
  -- the least element `η` of `f ﹫ ξ` above `x`
  have hR (x : M) (hx : x <ₒ α) :
      ∃ η <ₒ α, x <ₒ η ∧ ∀ S ∈ ran f, ∃ ξ ∈ S, x <ₒ ξ ∧ ξ ≤ₒ η := by
    let H : ClassFunction M := fun ξ ↦ Class.omin fun η ↦ η ∈ α ∧ (x <ₒ η ∧ η ∈ f ﹫ ξ)
    have : H.Sigma 1 Set.univ := by unfold H; infer_instance
    have hH {ξ : M} (hξ : ξ ∈ dom f) : H ξ <ₒ α ∧ x <ₒ H ξ ∧ H ξ ∈ f ﹫ ξ := by
      obtain ⟨η, hη, hle⟩ := (hC _ (hval hξ)).unboundedInOrd.exists_ole (hlim.succ_olt hx)
      have hηα : η ∈ α := (hC _ (hval hξ)).subset hη
      have hxη : x <ₒ η := by grind
      have h := Class.omin_mem (A := fun η ↦ η ∈ α ∧ (x <ₒ η ∧ η ∈ f ﹫ ξ))
        (ordinal_of_mem hα hηα) ⟨hηα, hxη, hη⟩
      exact ⟨olt_of_mem hα h.left, h.right⟩
    have hr := isSetRestrictedTo_of_sigma (G := H) (dom f)
    have hF : H ↾₀ dom f !: dom f → α :=
      isFunctionFromTo_toSetRestrictedTo hr fun ξ hξ ↦ (hH hξ).left.mem
    have hsup := osup_ran_olt_of_olt_cf hα hdom hF
    have hran : ∀ y ∈ ran (H ↾₀ dom f), Ordinal y := fun y hy ↦ ordinal_of_mem hα (hF.ran_subset hy)
    have hsx : Ordinal (succ x) := by grind
    refine ⟨omax₂ (succ x) (osup (ran (H ↾₀ dom f))),
      (omax₂_olt_iff hsx (ordinal_osup hran)).mpr ⟨hlim.succ_olt hx, hsup⟩, ?_, fun S hS ↦ ?_⟩
    · exact olt_of_olt_of_ole (by grind) (ole_omax₂_left hsx (ordinal_osup hran))
    · rw [hf.mem_ran_iff] at hS
      obtain ⟨ξ, hξ, rfl⟩ := hS
      have hmem : H ξ ∈ ran (H ↾₀ dom f) := (mem_ran_toSetRestrictedTo_iff hr).mpr ⟨ξ, hξ, rfl⟩
      exact ⟨H ξ, (hH hξ).right.right, (hH hξ).right.left,
        ole_trans (ole_osup hran hmem) (ole_omax₂_right hsx (ordinal_osup hran))⟩
  obtain ⟨lam, hlamα, hlamlim, hγlam, hclosed⟩ := exists_nonZeroLimOrdinal_iterate
    (R := fun x η ↦ ∀ S ∈ ran f, ∃ ξ ∈ S, x <ₒ ξ ∧ ξ ≤ₒ η) hα hcf hR hγ
  refine ⟨lam, mem_sInterInOrd_iff.mpr ⟨hlamα.mem, fun S hS ↦ ?_⟩, hγlam⟩
  refine (hC S hS).closedInOrd.mem_of_isLimitPoint hα hlamα ⟨hlamlim, fun δ hδ ↦ ?_⟩
  obtain ⟨x, -, hδx, η, hη, -, hη'⟩ := hclosed δ (olt_of_mem hlamlim.ordinal hδ)
  obtain ⟨ξ, hξ, hxξ, hξη⟩ := hη' S hS
  have hξlam : ξ <ₒ lam := olt_of_ole_of_olt hξη hη
  simp only [mem_inter_iff]
  exact ⟨ξ, ⟨hξ, hξlam.mem⟩, (olt_trans hδx hxξ).ole⟩

/-- If `cf α` is uncountable, the intersection of two clubs in `α` is a club -/
theorem ClubInOrd.inter (hα : Ordinal α) (hcf : (ω : M) <ₒ cf α) (hC : ClubInOrd C α)
    (hD : ClubInOrd D α) : ClubInOrd (C ∩ D) α := by
  refine ⟨hC.closedInOrd.inter hα hD.closedInOrd, ?_⟩
  -- `C` and `D` are the values of `natRec C (fun _ ↦ D) ↾₀ ω`
  let G : ClassFunction M := fun _ ↦ D
  have hr := isSetRestrictedTo_of_sigma (G := natRec C G) ω
  have hmem {y : M} : y ∈ ran (natRec C G ↾₀ ω) ↔ ∃ n ∈ (ω : M), natRec C G n = y :=
    mem_ran_toSetRestrictedTo_iff hr
  have hclub : ∀ S ∈ ran (natRec C G ↾₀ ω), ClubInOrd S α := by
    simp only [hmem]
    rintro S ⟨n, hn, rfl⟩
    have h : natRec C G n = C ∨ natRec C G n = D :=
      natRec_induction (A := fun y ↦ y = C ∨ y = D) (.inl rfl) (fun _ _ _ ↦ .inr rfl) hn
    rcases h with h | h <;> rwa [h]
  have hs := ClubInOrd.sInter hα hcf (isFunction_toSetRestrictedTo hr)
    (by rwa [dom_toSetRestrictedTo hr]) hclub
  refine hs.unboundedInOrd.mono fun x hx ↦ ?_
  have hx' := (mem_sInterInOrd_iff.mp hx).right
  simp only [mem_inter_iff]
  refine ⟨hx' C (hmem.mpr ⟨∅, empty_mem_omega, natRec_empty C G⟩),
    hx' D (hmem.mpr ⟨succ ∅, succ_mem_omega empty_mem_omega, ?_⟩)⟩
  rw [natRec_succ _ _ ordinal_empty]

/-- If `α` is an uncountable regular ordinal, the diagonal intersection of `α` clubs in `α` is a
club -/
theorem ClubInOrd.diagInter {f : M} (hα : Regular α) (hω : (ω : M) <ₒ α) (hf : IsFunction f)
    (hdom : dom f = α) (hC : ∀ S ∈ ran f, ClubInOrd S α) :
    ClubInOrd (diagInterInOrd f α) α := by
  have hαo := hα.ordinal
  have hcf : (ω : M) <ₒ cf α := by rwa [hα.cf_eq]
  have hval {ξ : M} (hξ : ξ <ₒ α) : ClubInOrd (f ﹫ ξ) α :=
    hC _ ((hf.mem_ran_iff _).mpr ⟨ξ, hdom ▸ hξ.mem, rfl⟩)
  refine ⟨ClosedInOrd.diagInter hαo fun ξ hξ ↦ (hval hξ).closedInOrd, ?_⟩
  simp only [unboundedInOrd_iff hαo]
  intro γ hγ
  -- each `x <ₒ α` has an element above it in the intersection of the `f ﹫ ξ` for `ξ <ₒ x`
  have hR (x : M) (hx : x <ₒ α) : ∃ η <ₒ α, x <ₒ η ∧ ∀ ξ ∈ x, η ∈ f ﹫ ξ := by
    have hsub : x ⊆ dom f := by
      rw [hdom]
      grind
    have hclub := ClubInOrd.sInter hαo hcf (hf.restrict x)
      (by rwa [dom_restrict_of_subset hf hsub, hα.cf_eq])
      (by
        intro S hS
        rw [hf.mem_ran_restrict_iff hsub] at hS
        obtain ⟨ξ, hξ, rfl⟩ := hS
        exact hval (olt_trans (olt_of_mem hx.ordinal_left hξ) hx))
    obtain ⟨η, hη, hle⟩ := hclub.unboundedInOrd.exists_ole
      ((nonZeroLimOrdinal_of_omega_olt_cf hαo hcf).succ_olt hx)
    have hη' := mem_sInterInOrd_iff.mp hη
    refine ⟨η, olt_of_mem hαo hη'.left, by grind, fun ξ hξ ↦ hη'.right _ ?_⟩
    exact (hf.mem_ran_restrict_iff hsub).mpr ⟨ξ, hξ, rfl⟩
  obtain ⟨lam, hlamα, hlamlim, hγlam, hclosed⟩ := exists_nonZeroLimOrdinal_iterate
    (R := fun x η ↦ ∀ ξ ∈ x, η ∈ f ﹫ ξ) hαo hcf hR hγ
  refine ⟨lam, mem_diagInterInOrd_iff.mpr ⟨hlamα.mem, fun ξ hξ ↦ ?_⟩, hγlam⟩
  have hξlam : ξ <ₒ lam := olt_of_mem hlamlim.ordinal hξ
  refine (hval (olt_trans hξlam hlamα)).closedInOrd.mem_of_isLimitPoint hαo hlamα
    ⟨hlamlim, fun δ hδ ↦ ?_⟩
  -- `x` above `δ` and `ξ` has `η <ₒ lam` above it in `f ﹫ ξ`
  have hδlam : δ <ₒ lam := olt_of_mem hlamlim.ordinal hδ
  obtain ⟨x, -, hmaxx, η, hη, hxη, hηf⟩ := hclosed (omax₂ δ ξ)
    ((omax₂_olt_iff hδlam.ordinal_left hξlam.ordinal_left).mpr ⟨hδlam, hξlam⟩)
  have hδx : δ ≤ₒ omax₂ δ ξ := ole_omax₂_left hδlam.ordinal_left hξlam.ordinal_left
  have hξx : ξ ≤ₒ omax₂ δ ξ := ole_omax₂_right hδlam.ordinal_left hξlam.ordinal_left
  simp only [mem_inter_iff]
  exact ⟨η, ⟨hηf ξ (olt_of_ole_of_olt hξx hmaxx).mem, hη.mem⟩,
    (olt_trans (olt_of_ole_of_olt hδx hmaxx) hxη).ole⟩

/-- If `cf α` is uncountable, every club in `α` is stationary -/
theorem ClubInOrd.stationary (hα : Ordinal α) (hcf : (ω : M) <ₒ cf α) (hC : ClubInOrd C α) :
    StationaryInOrd C α := by
  refine ⟨hC.subset, fun D hD ↦ ?_⟩
  have hlim := nonZeroLimOrdinal_of_omega_olt_cf hα hcf
  obtain ⟨ξ, hξ, -⟩ := (hC.inter hα hcf hD).unboundedInOrd.exists_ole (olt_of_mem hα hlim.empty_mem)
  simp only [ne_empty_iff]
  exact ⟨ξ, hξ⟩

end ClubInOrd

section Choice

variable [ModelsZFC M]

/-- The successor cardinal of an infinite ordinal is regular -/
theorem regular_csucc {κ : M} (hκ : Ordinal κ) (hωκ : (ω : M) ≤ₒ κ) : Regular (csucc κ) := by
  refine ⟨by grind, ?_⟩
  -- otherwise `csucc κ ↪ κ`
  have hne := not_isInjectionFromTo_csucc hκ
  contrapose! hne
  -- a cofinal map `f` from `β <ₒ csucc κ`
  set β := cf (csucc κ)
  obtain ⟨f, hf⟩ := exists_isCofinalMap_cf (ordinal_csucc κ)
  obtain ⟨i, hi⟩ := exists_isInjectionFromTo_of_olt_csucc hκ (β := β) (by grind)
  -- injections `g ﹫ ξ !: f ﹫ ξ ↪ κ`
  obtain ⟨g, -, -, hg⟩ := exists_uniformization (fun ys ↦ ys 1 !: f ﹫ ys 0 ↪ κ) β
  have hgI {ξ : M} (hξ : ξ <ₒ β) : g ﹫ ξ !: f ﹫ ξ ↪ κ :=
    hg ξ hξ.mem (exists_isInjectionFromTo_of_olt_csucc (β := f ﹫ ξ) hκ
      (by grind [hf.isFunctionFromTo.val_mem hξ.mem]))
  -- `s ﹫ x = !(ξ, g ﹫ ξ ﹫ x)` for some `ξ <ₒ β` with `x <ₒ f ﹫ ξ`
  obtain ⟨s, hs, hsdom, hsP⟩ := exists_uniformization
    (fun ys ↦ ∃ ξ <ₒ β, ys 0 <ₒ f ﹫ ξ ∧ ys 1 = !(ξ, (g ﹫ ξ) ﹫ ys 0)) (csucc κ)
  have hsx {x : M} (hx : x <ₒ csucc κ) :
      ∃ ξ <ₒ β, x <ₒ f ﹫ ξ ∧ s ﹫ x = !(ξ, (g ﹫ ξ) ﹫ x) := by
    obtain ⟨ξ, hξ, hsub⟩ := hf.exists_ole (γ := succ x) (by grind [NonZeroLimOrdinal.succ_olt])
    have hxξ : x <ₒ f ﹫ ξ := by grind
    exact hsP x hx.mem ⟨!(ξ, (g ﹫ ξ) ﹫ x), ξ, hξ, hxξ, rfl⟩
  -- `csucc κ ↪ β ×ˢ κ ↪ κ ×ˢ κ ↪ κ`
  have hinj : s !: csucc κ ↪ β ×ˢ κ := by
    refine isInjectionFromTo_of_val hs hsdom (fun x hx ↦ ?_) fun x hx y hy hxy ↦ ?_
    · obtain ⟨ξ, hξ, hxξ, hsx⟩ := hsx (x := x) (by grind)
      rw [hsx]
      exact mem_sprod _ _ _ _ hξ.mem ((hgI hξ).isFunctionFromTo.val_mem hxξ.mem)
    · obtain ⟨ξ, -, hxξ, hsx'⟩ := hsx (x := x) (by grind)
      obtain ⟨η, hη, hyη, hsy⟩ := hsx (x := y) (by grind)
      simp only [hsx', hsy, orderedPair_eq_orderedPair_iff] at hxy
      obtain ⟨rfl, hval⟩ := hxy
      exact (hgI hη).eq hxξ.mem hyη.mem hval
  obtain ⟨q, hq⟩ := exists_isInjectionFromTo_sprod_self hωκ
  exact ⟨q !∘ (prodMap i (id κ) β κ !∘ s),
    hq.comp ((hi.prodMap (isInjectionFromTo_id κ)).comp hinj)⟩

end Choice

section CountableChoice

variable [ModelsZFCC M]

/-- Under countable choice, `ℵ₁` is regular: a cofinal map from a countable ordinal would make
`ℵ₁` a countable union of countable ordinals -/
theorem regular_aleph_one : Regular (ℵ (succ (∅ : M))) := by
  rw [aleph_succ ordinal_empty, aleph_empty]
  refine ⟨by grind, ?_⟩
  -- otherwise `csucc ω` is countable
  have hne := not_isInjectionFromTo_csucc (ordinal_omega (M := M))
  contrapose! hne
  obtain ⟨f, hf⟩ := exists_isCofinalMap_cf (ordinal_csucc (ω : M))
  obtain ⟨i, hi⟩ := exists_isInjectionFromTo_of_olt_csucc (β := cf (csucc ω)) (κ := (ω : M))
    (by grind) (by grind)
  -- `csucc ω ⊆ ⋃₀ ran f`
  have hsub : csucc (ω : M) ⊆ ⋃₀ ran f := by
    intro γ hγ
    obtain ⟨ξ, hξ, hle⟩ := hf.exists_ole (γ := succ γ) (by grind)
    have hγξ : γ <ₒ f ﹫ ξ := olt_of_olt_of_ole (by grind) hle
    simp only [mem_sUnion_iff]
    refine ⟨f ﹫ ξ, ?_, hγξ.mem⟩
    simp only [hf.isFunctionFromTo.isFunction.mem_ran_iff, hf.isFunctionFromTo.dom_eq]
    exact ⟨ξ, hξ.mem, rfl⟩
  -- `ran f` is countable and consists of countable ordinals
  have hran : Countable (ran f) := Countable.of_isSurjectionFromTo ⟨i, hi⟩
    (isSurjectionFromTo_ran_of_isFunctionFromTo hf.isFunctionFromTo)
  have hcount (y : M) (hy : y ∈ ran f) : Countable y := by
    exact exists_isInjectionFromTo_of_olt_csucc (by grind)
      (by grind [hf.isFunctionFromTo.ran_subset hy])
  exact (hran.sUnion hcount).of_subset hsub

end CountableChoice

end MemStructure

end FirstOrder.Language
