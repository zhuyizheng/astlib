/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Order.Basic
import Astlib.Basic.Ordinal.Order
import Astlib.Basic.SetOperation.Function.Restrict
/-!
# The Brouwer–Kleene order

`BKLt R s t`: the Brouwer–Kleene order on finite sequences with coordinates ordered by `R`, the
lexicographic order in which a proper extension is smaller.

For functions on ordinals with values in `C`, it is irreflexive if `R` is irreflexive on `C`
(`not_bkLt_self`), transitive if `R` is transitive on `C` (`BKLt.trans`), and trichotomous if
the first differing coordinates of any two sequences are comparable (`bkLt_trichotomous`).
Applying an injective order embedding to the coordinates preserves the order (`bkLt_iff_of_map`).
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M]

/-- The Brouwer–Kleene order on finite sequences with coordinates ordered by `R`: `s` is below
`t` if `s` properly extends `t`, or `s` and `t` first differ at some `k` with `s(k) R t(k)` -/
def BKLt (R s t : M) : Prop :=
  (t ⊆ s ∧ t ≠ s) ∨ ∃ k ∈ dom s, k ∈ dom t ∧ s ↾ k = t ↾ k ∧ (s ﹫ k) [R] (t ﹫ k)

section Properties

variable [ModelsKP M] {C R k s t u x : M}

omit [ModelsKP M] in
/-- A function extending `t` agrees with `t` on `dom t` -/
theorem val_eq_of_subset (hs : IsFunction s) (ht : IsFunction t) (hts : t ⊆ s)
    (hx : x ∈ dom t) : s ﹫ x = t ﹫ x :=
  (hs.val_eq_of_rel (hts (rel_val ht hx))).trans (ht.val_eq_of_rel (rel_val ht hx)).symm

omit [ModelsKP M] in
/-- A function agreeing with `t` on its domain `dom s ⊆ dom t` is contained in `t` -/
theorem subset_of_val_eq (hs : IsFunction s) (ht : IsFunction t) (hd : dom s ⊆ dom t)
    (h : ∀ x ∈ dom s, s ﹫ x = t ﹫ x) : s ⊆ t := by
  intro z hz
  obtain ⟨x, y, rfl⟩ := hs.isRelation hz
  have hx : x ∈ dom s := (mem_dom_iff s x).mpr ⟨y, hz⟩
  rw [← hs.val_eq_of_rel hz, h x hx]
  exact rel_val ht (hd hx)

omit [ModelsKP M] in
/-- Functions with equal restrictions to `k` agree on `k` -/
theorem val_eq_of_restrict_eq (hs : IsFunction s) (ht : IsFunction t) (h : s ↾ k = t ↾ k)
    (hx : x ∈ k) (hxs : x ∈ dom s) (hxt : x ∈ dom t) : s ﹫ x = t ﹫ x := by
  rw [← val_restrict s hs hx hxs, ← val_restrict t ht hx hxt, h]

/-- Equal restrictions to `k` give equal restrictions to `j ⊆ k` -/
theorem restrict_eq_of_restrict_eq {j : M} (h : s ↾ k = t ↾ k) (hj : j ⊆ k) : s ↾ j = t ↾ j := by
  have hkj : k ∩ j = j := by
    ext x
    rw [mem_inter_iff]
    exact ⟨fun h ↦ h.right, fun h ↦ ⟨hj h, h⟩⟩
  rw [← hkj, ← restrict_restrict, ← restrict_restrict, h]

omit [ModelsKP M] in
/-- An extension `s` of `t` has the restrictions of `t` to subsets of `dom t` -/
theorem restrict_eq_of_subset (hs : IsFunction s) (ht : IsFunction t) (hts : t ⊆ s)
    (hk : k ⊆ dom t) : s ↾ k = t ↾ k :=
  hs.restrict_eq_restrict ht (fun _ hx ↦ dom_mono hts (hk hx)) hk fun _ hx ↦
    val_eq_of_subset hs ht hts (hk hx)

theorem subset_of_not_mem {a b : M} (ha : Ordinal a) (hb : Ordinal b) (h : b ∉ a) : a ⊆ b := by
  rcases olt_trichotomy ha hb with h' | rfl | h'
  · exact fun x hx ↦ hb.transitive _ h'.right.right hx
  · exact fun x hx ↦ hx
  · exact (h h'.right.right).elim

omit [RudClosed M] [Extensional M] [ModelsKP M] in
/-- The Brouwer–Kleene order is irreflexive -/
theorem not_bkLt_self (hR : IsIrreflOn R C) (hsC : ∀ k ∈ dom s, s ﹫ k ∈ C) : ¬BKLt R s s := by
  rintro (⟨-, h⟩ | ⟨k, hk, -, -, h⟩)
  · exact h rfl
  · exact hR _ (hsC k hk) h

/-- The Brouwer–Kleene order is transitive -/
theorem BKLt.trans (hs : IsFunction s) (ht : IsFunction t) (hu : IsFunction u)
    (hos : Ordinal (dom s)) (hot : Ordinal (dom t)) (hou : Ordinal (dom u))
    (hR : IsTransOn R C) (hsC : ∀ k ∈ dom s, s ﹫ k ∈ C) (htC : ∀ k ∈ dom t, t ﹫ k ∈ C)
    (huC : ∀ k ∈ dom u, u ﹫ k ∈ C) (h₁ : BKLt R s t) (h₂ : BKLt R t u) : BKLt R s u := by
  rcases h₁ with ⟨hts, hne⟩ | ⟨k, hks, hkt, hres, hrel⟩ <;>
    rcases h₂ with ⟨hut, hne'⟩ | ⟨m, hmt, hmu, hres', hrel'⟩
  · refine .inl ⟨fun z hz ↦ hts (hut hz), fun h ↦ hne' ?_⟩
    subst h
    ext z
    exact ⟨fun hz ↦ hut hz, fun hz ↦ hts hz⟩
  · refine .inr ⟨m, dom_mono hts hmt, hmu, ?_, ?_⟩
    · rw [restrict_eq_of_subset hs ht hts (hot.transitive _ hmt), hres']
    · rwa [val_eq_of_subset hs ht hts hmt]
  · by_cases hku : k ∈ dom u
    · refine .inr ⟨k, hks, hku, ?_, ?_⟩
      · rw [hres, restrict_eq_of_subset ht hu hut (hou.transitive _ hku)]
      · rwa [← val_eq_of_subset ht hu hut hku]
    · have hko : Ordinal k := ordinal_of_mem hos hks
      have hdu : dom u ⊆ k := subset_of_not_mem hou hko hku
      refine .inl ⟨subset_of_val_eq hu hs (fun _ hx ↦ hos.transitive _ hks (hdu hx)) fun x hx ↦ ?_,
        fun h ↦ hku (h ▸ hks)⟩
      rw [← val_eq_of_subset ht hu hut hx]
      exact (val_eq_of_restrict_eq hs ht hres (hdu hx) (hos.transitive _ hks (hdu hx))
        (dom_mono hut hx)).symm
  · have hko : Ordinal k := ordinal_of_mem hot hkt
    have hmo : Ordinal m := ordinal_of_mem hot hmt
    rcases olt_trichotomy hko hmo with hkm | rfl | hmk
    · have hkm := hkm.right.right
      have hku : k ∈ dom u := hou.transitive _ hmu hkm
      refine .inr ⟨k, hks, hku, ?_, ?_⟩
      · rw [hres, restrict_eq_of_restrict_eq hres' (hmo.transitive _ hkm)]
      · rwa [← val_eq_of_restrict_eq ht hu hres' hkm hkt hku]
    · exact .inr ⟨k, hks, hmu, hres.trans hres',
        hR _ (hsC k hks) _ (htC k hkt) _ (huC k hmu) hrel hrel'⟩
    · have hmk := hmk.right.right
      have hms : m ∈ dom s := hos.transitive _ hks hmk
      refine .inr ⟨m, hms, hmu, ?_, ?_⟩
      · rw [restrict_eq_of_restrict_eq hres (hko.transitive _ hmk), hres']
      · rwa [val_eq_of_restrict_eq hs ht hres hmk hms hmt]

/-- The Brouwer–Kleene order is trichotomous if the first differing coordinates of `s` and `t` are
comparable -/
theorem bkLt_trichotomous (hs : IsFunction s) (ht : IsFunction t) (hos : Ordinal (dom s))
    (hot : Ordinal (dom t))
    (hcmp : ∀ k ∈ dom s, k ∈ dom t → s ↾ k = t ↾ k → s ﹫ k ≠ t ﹫ k →
      (s ﹫ k) [R] (t ﹫ k) ∨ (t ﹫ k) [R] (s ﹫ k)) :
    BKLt R s t ∨ s = t ∨ BKLt R t s := by
  by_cases hD : ∃ k, k ∈ dom s ∧ k ∈ dom t ∧ s ﹫ k ≠ t ﹫ k
  · obtain ⟨k₀, hk₀s, hk₀⟩ := hD
    obtain ⟨k, hko, ⟨hks, hkt, hne⟩, hmin⟩ :=
      exists_min_ordinal (A := fun k ↦ k ∈ dom s ∧ k ∈ dom t ∧ s ﹫ k ≠ t ﹫ k)
        (ordinal_of_mem hos hk₀s) ⟨hk₀s, hk₀⟩
    have hres : s ↾ k = t ↾ k :=
      hs.restrict_eq_restrict ht (hos.transitive _ hks) (hot.transitive _ hkt) fun x hx ↦ by
        by_contra h
        exact hmin x hx ⟨hos.transitive _ hks hx, hot.transitive _ hkt hx, h⟩
    rcases hcmp k hks hkt hres hne with h | h
    · exact .inl (.inr ⟨k, hks, hkt, hres, h⟩)
    · exact .inr (.inr (.inr ⟨k, hkt, hks, hres.symm, h⟩))
  push Not at hD
  rcases olt_trichotomy hos hot with h | h | h
  · have hst : s ⊆ t := subset_of_val_eq hs ht (fun x hx ↦ hot.transitive _ h.right.right hx)
      fun x hx ↦ hD x hx (hot.transitive _ h.right.right hx)
    refine .inr (.inr (.inl ⟨hst, fun he ↦ ?_⟩))
    rw [he] at h
    exact notMem_self _ h.right.right
  · exact .inr (.inl (hs.ext ht h fun x hx ↦ hD x hx (h ▸ hx)))
  · have hts : t ⊆ s := subset_of_val_eq ht hs (fun x hx ↦ hos.transitive _ h.right.right hx)
      fun x hx ↦ (hD x (hos.transitive _ h.right.right hx) hx).symm
    refine .inl (.inl ⟨hts, fun he ↦ ?_⟩)
    rw [he] at h
    exact notMem_self _ h.right.right

end Properties

section BKMap

/-! ### The Brouwer–Kleene order under a coordinatewise order embedding -/

variable {R R' s t s' t' C : M}

/-- Applying an injective order embedding `κ` to the coordinates preserves the Brouwer–Kleene
order -/
theorem bkLt_iff_of_map (κ : M → M) (hs : IsFunction s) (ht : IsFunction t)
    (hs' : IsFunction s') (ht' : IsFunction t') (hds : dom s' = dom s) (hdt : dom t' = dom t)
    (hsv : ∀ i ∈ dom s, s' ﹫ i = κ (s ﹫ i)) (htv : ∀ i ∈ dom t, t' ﹫ i = κ (t ﹫ i))
    (hsC : ∀ i ∈ dom s, s ﹫ i ∈ C) (htC : ∀ i ∈ dom t, t ﹫ i ∈ C)
    (hinj : ∀ a ∈ C, ∀ b ∈ C, κ a = κ b → a = b)
    (hR : ∀ a ∈ C, ∀ b ∈ C, (a [R] b ↔ (κ a) [R'] (κ b)))
    (hos : Ordinal (dom s)) (hot : Ordinal (dom t)) :
    BKLt R s t ↔ BKLt R' s' t' := by
  have hsub : t ⊆ s ↔ t' ⊆ s' := by
    constructor
    · intro h
      have hd := dom_mono h
      refine subset_of_val_eq ht' hs' (by rw [hds, hdt]; exact hd) fun i hi ↦ ?_
      rw [hdt] at hi
      rw [htv i hi, hsv i (hd hi), val_eq_of_subset hs ht h hi]
    · intro h
      have hd := dom_mono h
      rw [hds, hdt] at hd
      refine subset_of_val_eq ht hs hd fun i hi ↦ ?_
      have h' := val_eq_of_subset hs' ht' h (by rw [hdt]; exact hi)
      rw [hsv i (hd hi), htv i hi] at h'
      exact (hinj _ (hsC i (hd hi)) _ (htC i hi) h').symm
  have heq : t = s ↔ t' = s' := by
    constructor
    · intro h
      subst h
      refine ht'.ext hs' (by rw [hds, hdt]) fun i hi ↦ ?_
      rw [hdt] at hi
      rw [htv i hi, hsv i hi]
    · intro h
      subst h
      refine ht.ext hs (by rw [← hds, ← hdt]) fun i hi ↦ ?_
      have h1 := htv i hi
      rw [hsv i (by rw [← hds, hdt]; exact hi)] at h1
      exact hinj _ (htC i hi) _ (hsC i (by rw [← hds, hdt]; exact hi)) h1.symm
  have hres {k : M} (hks : k ⊆ dom s) (hkt : k ⊆ dom t) : s ↾ k = t ↾ k ↔ s' ↾ k = t' ↾ k := by
    constructor
    · intro h
      refine hs'.restrict_eq_restrict ht' (by rw [hds]; exact hks) (by rw [hdt]; exact hkt)
        fun i hi ↦ ?_
      rw [hsv i (hks hi), htv i (hkt hi), val_eq_of_restrict_eq hs ht h hi (hks hi) (hkt hi)]
    · intro h
      refine hs.restrict_eq_restrict ht hks hkt fun i hi ↦ ?_
      have h' := val_eq_of_restrict_eq hs' ht' h hi (by rw [hds]; exact hks hi)
        (by rw [hdt]; exact hkt hi)
      rw [hsv i (hks hi), htv i (hkt hi)] at h'
      exact hinj _ (hsC i (hks hi)) _ (htC i (hkt hi)) h'
  unfold BKLt
  rw [hds, hdt]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨k, hks, hkt, hr, h⟩)
    · exact .inl ⟨hsub.mp h1, fun h' ↦ h2 (heq.mpr h')⟩
    · refine .inr ⟨k, hks, hkt, (hres (hos.transitive _ hks) (hot.transitive _ hkt)).mp hr, ?_⟩
      rw [hsv k hks, htv k hkt]
      exact (hR _ (hsC k hks) _ (htC k hkt)).mp h
  · rintro (⟨h1, h2⟩ | ⟨k, hks, hkt, hr, h⟩)
    · exact .inl ⟨hsub.mpr h1, fun h' ↦ h2 (heq.mp h')⟩
    · refine .inr ⟨k, hks, hkt, (hres (hos.transitive _ hks) (hot.transitive _ hkt)).mpr hr, ?_⟩
      rw [hsv k hks, htv k hkt] at h
      exact (hR _ (hsC k hks) _ (htC k hkt)).mpr h

end BKMap

end FirstOrder.Language.MemStructure
