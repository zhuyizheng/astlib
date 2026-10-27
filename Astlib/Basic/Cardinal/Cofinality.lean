/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Cardinal.Basic
import Astlib.Basic.Axiom.Choice.Semantics
import Astlib.Basic.Cardinal.Countable
/-!
# Cofinality

A cofinal map from `β` into `α` is a function `f !: β → α` such that every `γ <ₒ α` is below a
value `f ﹫ ξ` with `ξ <ₒ β`. The cofinality `cf α` of an ordinal `α` is the least ordinal with a
cofinal map into `α`, and `α` is regular if `cf α = α`. In models of `KP`:

* `cf_ole`: `cf α ≤ₒ α`; `cf_empty`, `cf_succ`: `cf ∅ = ∅` and `cf (succ α) = succ ∅`;
* `Regular.cardinal`: regular ordinals are cardinals;
* `regular_omega`: `ω` is regular.

In models of `ZFC`, the successor cardinal `csucc κ` of an infinite ordinal `κ` is regular
(`regular_csucc`): a cofinal map `f` from `β ∈ csucc κ` together with chosen injections
`f ﹫ ξ ↪ κ` and a choice of `ξ` with `x ∈ f ﹫ ξ` for each `x` would give
`csucc κ ↪ β ×ˢ κ ↪ κ ×ˢ κ ↪ κ`.

In models of `ZF` with countable choice, `ℵ₁` is regular (`regular_aleph_one`): a cofinal map
from a countable ordinal would make `ℵ₁` a countable union of countable ordinals.
-/

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin RudimentaryTerm MemStructure

namespace FirstOrder.Language

namespace RudimentaryTerm

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] {n : ℕ}

/-- The `Δ₀` formula saying that `f` is a cofinal map from `β` into `α` -/
noncomputable def isCofinalMap (f β α : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  -- `[f, β, α]`
  ((ᵣ0).isFunctionFromTo (ᵣ1) (ᵣ2) ⊓
    ∀₀∈ &2 ((ᵣ3).isOrdinal ⊓ (ᵣ2).isOrdinal ⟹ ∃₀∈ &1 ((ᵣ4).isOrdinal ⊓ (ᵣ1).isOrdinal ⊓
      (ᵣ3).isOrdinal ⊓ ((ᵣ0) ﹫ (ᵣ4)).isOrdinal ⊓ ((&0 ∈₀ &1).substBoundRud ![ᵣ3, (ᵣ0) ﹫ (ᵣ4)] ⊔
        (&0 =₀ &1).substBoundRud ![ᵣ3, (ᵣ0) ﹫ (ᵣ4)]))) :
      L.DeltaZeroBoundedFormula 3).substBoundRud ![f, β, α]

instance (f β α : L.RudimentaryTerm n) [f.CharFree] [β.CharFree] [α.CharFree] :
    (isCofinalMap f β α).RelFree := by
  unfold isCofinalMap; infer_instance

end RudimentaryTerm

namespace MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] {α β f : M}

/-- `f` is a cofinal map from `β` into `α` -/
def IsCofinalMap (f β α : M) : Prop := f !: β → α ∧ ∀ γ <ₒ α, ∃ ξ <ₒ β, γ ≤ₒ f ﹫ ξ

omit [ModelsKP M] in
theorem IsCofinalMap.isFunctionFromTo (hf : IsCofinalMap f β α) : f !: β → α := hf.left

omit [ModelsKP M] in
theorem IsCofinalMap.exists_ole (hf : IsCofinalMap f β α) {γ : M} (hγ : γ <ₒ α) :
    ∃ ξ <ₒ β, γ ≤ₒ f ﹫ ξ :=
  hf.right γ hγ

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isCofinalMap {n : ℕ}
    (f β α : L.RudimentaryTerm n) [f.CharFree] [β.CharFree] [α.CharFree] (xs : Fin n → M) :
    (isCofinalMap f β α).toBoundedFormula 〘xs〙 ↔ IsCofinalMap (f〘xs〙 : M) β〘xs〙 α〘xs〙 := by
  rw [isCofinalMap, DeltaZeroBoundedFormula.realize_substBoundRud]
  simp only [isValue, Function.comp_apply, Nat.reduceAdd, RudimentaryTerm.val, Nat.succ_eq_add_one,
    toBoundedFormula_inf, toBoundedFormula, toBoundedFormula_exMem, toBoundedFormula_sup,
    realize'_inf, realize_isFunctionFromTo, realize_basic, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, BoundedFormula.realize_allMem, Term.realize'_var',
    realize'_imp, realize_isOrdinal, snoc_nat, coe_ofNat_eq_mod, Nat.mod_succ, lt_self_iff_false,
    ↓reduceDIte, Nat.reduceMod, Nat.lt_add_one, reduceFinMk, BoundedFormula.realize_exMem,
    Nat.one_mod, Nat.one_lt_ofNat, mk_one, RudimentaryTerm.realize_substBoundRud, realize_val₀,
    Nat.zero_mod, zero_lt_four, zero_eta, zero_lt_three, Matrix.cons_val_fin_one, realize'_sup,
    DeltaZeroBoundedFormula.realize_substBoundRud, realize'_mem, realize'_bdEqual, and_imp,
    IsCofinalMap, olt_iff, ole_iff, and_congr_right_iff]
  refine fun _ ↦ ⟨fun h γ hγ hα hγα ↦ ?_, fun h γ hγα hγ hα ↦ ?_⟩
  · grind [h γ hγα hγ hα]
  · grind [h γ hγ hα hγα]

@[grind .]
theorem isCofinalMap_id (α : M) : IsCofinalMap (id α) α α := by
  refine ⟨isFunctionFromTo_id α, fun γ hγ ↦ ⟨γ, hγ, ?_⟩⟩
  rw [id_val α hγ.mem]
  exact ole_refl hγ.ordinal_left

/-- The class of ordinals with a cofinal map into `x` -/
def HasCofinalMap (x : M) : Class M := fun β ↦ ∃ f, IsCofinalMap f β x

/-- `IsCofinalMap` is `Δ₀` -/
instance : Multiclass.DeltaZero (fun ys : Fin 3 → M ↦ IsCofinalMap (ys 0) (ys 1) (ys 2))
    Set.univ := by
  have h : (fun ys : Fin 3 → M ↦ IsCofinalMap (ys 0) (ys 1) (ys 2)) =
      ((ᵣ0 : L.RudimentaryTerm 3).isCofinalMap (ᵣ1) (ᵣ2)).toBoundedFormula.multiclass := by
    funext ys
    simp
  rw [h]
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
  Class.omin_mem (A := HasCofinalMap α) hα ⟨_, isCofinalMap_id α⟩

theorem cf_ole_of_isCofinalMap (hβ : Ordinal β) (hf : IsCofinalMap f β α) : cf α ≤ₒ β :=
  Class.omin_ole hβ ⟨f, hf⟩

@[grind .]
theorem cf_ole (hα : Ordinal α) : cf α ≤ₒ α :=
  cf_ole_of_isCofinalMap hα (isCofinalMap_id α)

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
    refine ⟨?_, fun γ hγ ↦ ⟨∅, olt_succ ordinal_empty, ?_⟩⟩
    · convert isFunctionFromTo_singletonFun (mem_succ_self α)
      simp [succ_empty]
    · simp only [singletonFun_val]
      grind
  refine ole_antisymm (cf_ole_of_isCofinalMap (by grind) hcf) ?_
  rw [succ_ole_iff ordinal_empty (ordinal_cf _)]
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
    refine ⟨hf.isFunctionFromTo.restrict (by grind), fun γ hγ ↦ ?_⟩
    obtain ⟨ξ, hξ, hγξ⟩ := hf.exists_ole hγ
    have hval {ζ : M} (hζ : ζ <ₒ β) : (f ↾ β) ﹫ ζ = f ﹫ ζ :=
      val_restrict _ hf.isFunctionFromTo.isFunction hζ.mem
        (by rw [hf.isFunctionFromTo.dom_eq]; exact mem_succ_of_mem hζ.mem)
    grind
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
  -- `supRange f (g ﹫ η) <ₒ α`: otherwise `f ↾ (g ﹫ η)` is cofinal and `cf α ≤ₒ g ﹫ η`
  have hlt {η : M} (hη : η <ₒ cf (cf α)) : supRange f (g ﹫ η) <ₒ α := by
    refine olt_of_ole_of_ne ?_ fun h ↦ ?_
    · rw [supRange_ole_iff hr hff.isFunction (hdom hη) hα]
      grind
    have hcof : IsCofinalMap (f ↾ (g ﹫ η)) (g ﹫ η) α := by
      refine ⟨hff.restrict (by grind), fun γ hγ ↦ ?_⟩
      rw [← h, olt_supRange_iff hr hff.isFunction (hdom hη) hγ.ordinal_left] at hγ
      obtain ⟨ξ, hξ', hγξ⟩ := hγ
      exact ⟨ξ, by grind⟩
    grind [cf_ole_of_isCofinalMap]
  -- `(supRange f).comp (g ﹫ ·) ↾₀ cf (cf α)` is a cofinal map into `α`
  have hcof : IsCofinalMap (((supRange f).comp fun η ↦ g ﹫ η) ↾₀ cf (cf α)) (cf (cf α)) α := by
    refine ⟨⟨isFunction_toSetRestrictedTo hres, dom_toSetRestrictedTo hres, fun y hy ↦ ?_⟩,
      fun γ hγ ↦ ?_⟩
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

/-- A surjection from an ordinal is a cofinal map -/
@[grind .]
theorem IsSurjectionFromTo.isCofinalMap (hβ : Ordinal β) (hf : f !: β ↠ α) :
    IsCofinalMap f β α := by
  refine ⟨hf.isFunctionFromTo, fun γ hγ ↦ ?_⟩
  obtain ⟨ξ, hξ, rfl⟩ := hf.exists_mem_val hγ.mem
  exact ⟨ξ, olt_of_mem hβ hξ, ole_refl hγ.ordinal_left⟩

/-- Regular ordinals are cardinals -/
@[grind .]
theorem Regular.cardinal (hα : Regular α) : Cardinal α := by
  refine ⟨hα.ordinal, fun β hβ f hf ↦ ?_⟩
  have h := cf_ole_of_isCofinalMap (by grind) (hf.isCofinalMap (by grind))
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
  rw [not_ole_iff ordinal_omega (ordinal_cf _)] at h
  -- a cofinal map from a natural number is bounded by some `m ∈ ω`
  obtain ⟨f, hf⟩ := exists_isCofinalMap_cf (ordinal_omega (M := M))
  obtain ⟨m, hm, hmf⟩ := exists_bound_of_mem_omega h.mem hf.isFunctionFromTo
  obtain ⟨ξ, hξ, hmξ⟩ := hf.exists_ole (olt_of_mem ordinal_omega hm)
  grind

end Omega

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
    obtain ⟨ξ, hξ, hsub⟩ := hf.exists_ole (γ := succ x) (by grind)
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
      rw [hsx', hsy, orderedPair_eq_orderedPair_iff] at hxy
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
