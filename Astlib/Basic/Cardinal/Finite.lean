/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Cardinal.Basic
/-!
# Finite sets

A set is finite if it is in bijection with a natural number. In models of `KP` with `ω`:

* `Finite` is a definable class;
* natural numbers are finite, `ω` is not (`not_finite_omega`);
* subsets, injective preimages and images of finite sets are finite;
* `Finite.induction`: a definable class containing `∅` and closed under adding a point to a
  finite set contains every finite set;
* `insert a x`, `x ∪ y` and `⋃₀ X` are finite for finite `x`, `y`, and finite `X` of finite sets.

In models of `ZF`:

* `finSubsets x` is the set of finite subsets of `x`;
* `finSeqs x` is the set of finite sequences in `x`, i.e. of functions from a natural number to
  `x`;
* composing with an injection (bijection) `f !: x ↪ y` (`f !: x ↔ y`) is an injection
  (bijection) `funSet a x ↪ funSet a y` and `finSeqs x ↪ finSeqs y`;
* an injection `f !: x ↪ y` induces an injection `finSubsets x ↪ finSubsets y`;
* for a set `x` of ordinals, increasing enumeration `enumFinSubsets x` injects `finSubsets x` into
  `finSeqs x`.
-/

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin RudimentaryTerm MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] [HasOmega M]
  {f g a x y n X : M}

/-- `x` is finite: it is in bijection with a natural number -/
def Finite : Class M := fun x ↦ ∃ n ∈ (ω : M), ∃ f, f !: x ↔ n

instance : (Finite : Class M).Definable Set.univ := by
  unfold Finite
  infer_instance

omit [HasOmega M] in
/-- Natural numbers are finite -/
@[grind .]
theorem finite_of_mem_omega (hn : n ∈ (ω : M)) : Finite n :=
  ⟨n, hn, id n, isInjectionFromTo_id n, isSurjectionFromTo_id n⟩

@[simp, grind .]
theorem finite_empty : Finite (∅ : M) := finite_of_mem_omega empty_mem_omega

/-- `ω` is not finite -/
theorem not_finite_omega : ¬Finite (ω : M) := fun ⟨_, hn, _, hf⟩ ↦
  cardinal_omega.not_isSurjectionFromTo (olt_of_mem ordinal_omega hn) _ hf.inv.isSurjectionFromTo

omit [HasOmega M] in
/-- Sets in bijection with finite sets are finite -/
theorem Finite.of_isBijectionFromTo (hx : Finite x) (hf : f !: x ↔ y) : Finite y :=
  have ⟨n, hn, g, hg⟩ := hx
  ⟨n, hn, g !∘ f⁻¹, hg.comp hf.inv⟩

/-- Sets injecting into finite sets are finite -/
theorem Finite.of_isInjectionFromTo (hy : Finite y) (hf : f !: x ↪ y) : Finite x := by
  obtain ⟨n, hn, g, hg⟩ := hy
  have hgf := hg.isInjectionFromTo.comp hf
  have hSo (z : M) (hz : z ∈ ran (g !∘ f)) : Ordinal z := by grind
  refine ⟨ot (ran (g !∘ f)), ?_, _, (isBijectionFromTo_otMap hSo).comp
    (isBijectionFromTo_ran_of_isInjectionFromTo hgf)⟩
  rcases mem_or_eq_of_ole (ot_ole (by grind) hgf.ran_subset) with h | h <;> grind

/-- Subsets of finite sets are finite -/
@[grind .]
theorem Finite.of_subset (hy : Finite y) (h : x ⊆ y) : Finite x :=
  hy.of_isInjectionFromTo ((isInjectionFromTo_id x).of_ran_subset (by rwa [ran_id]))

/-- Finite ordinals are natural numbers -/
theorem Finite.mem_omega {α : M} (hα : Ordinal α) (h : Finite α) : α ∈ (ω : M) := by
  rcases olt_or_ole hα ordinal_omega with h' | h'
  · exact h'.mem
  · exact absurd (h.of_subset ((ole_iff_subset ordinal_omega hα).mp h')) not_finite_omega

@[grind .]
theorem Finite.sdiff (hx : Finite x) (y : M) : Finite (x \ y) :=
  hx.of_subset (sdiff_subset_left x y)

@[grind .]
theorem Finite.inter_left (hx : Finite x) (y : M) : Finite (x ∩ y) :=
  hx.of_subset (inter_subset_left x y)

@[grind .]
theorem Finite.inter_right (hy : Finite y) (x : M) : Finite (x ∩ y) :=
  hy.of_subset (inter_subset_right x y)

/-- Images of finite sets are finite -/
theorem Finite.of_isSurjectionFromTo (hx : Finite x) (hf : f !: x ↠ y) : Finite y := by
  obtain ⟨n, hn, g, hg⟩ := hx
  -- `n ↠ x ↠ y`, so `y ↪ n`
  exact (finite_of_mem_omega hn).of_isInjectionFromTo
    ((hf.comp hg.inv.isSurjectionFromTo).leastInv (by grind))

/-- Images of natural numbers are finite -/
theorem finite_of_isSurjectionFromTo (hn : n ∈ (ω : M)) (hf : f !: n ↠ x) : Finite x :=
  (finite_of_mem_omega hn).of_isSurjectionFromTo hf

/-- Adding a point to a finite set gives a finite set -/
@[grind .]
theorem Finite.insert (hx : Finite x) (a : M) : Finite (insert a x) := by
  by_cases ha : a ∈ x
  ·  simpa [ha]
  obtain ⟨n, hn, f, hf⟩ := hx
  -- send `a` to `n`
  refine ⟨succ n, succ_mem_omega hn, Insert.insert !(a, n) f, ?_⟩
  rw [isBijectionFromTo_iff]
  refine ⟨⟨hf.isFunction.insert (by grind) n, by grind⟩, fun z hz z' hz' h ↦ ?_, ?_⟩
  · simp only [mem_insert_iff] at hz hz'
    rcases hz <;> rcases hz' <;> grind [hf.isFunctionFromTo]
  · simp [hf.ran_eq, succ]

@[simp, grind .]
theorem finite_singleton (a : M) : Finite ({a} : M) := by
  rw [show ({a} : M) = insert a ∅ by ext; simp]
  exact finite_empty.insert a

/-- Induction on finite sets: a definable class containing `∅` and closed under adding a point to
a finite set contains every finite set -/
theorem Finite.induction {A : Class M} [A.Definable Set.univ] (h0 : A ∅)
    (hins : ∀ x a, A x → A (Insert.insert a x)) (hx : Finite x) : A x := by
  obtain ⟨n, hn, f, hf⟩ := hx
  -- induction on the size `n` of `x`
  refine omega_induction (A := fun n ↦ ∀ x f, f !: x ↔ n → A x) (fun x f hf ↦ ?_)
    (fun n hn ih x f hf ↦ ?_) hn x f hf
  · rwa [hf.isFunctionFromTo.eq_empty]
  · -- remove the preimage `z` of `n`
    obtain ⟨z, hz, -⟩ := hf.isSurjectionFromTo.exists_mem_val (mem_succ_self (x := n))
    have hxz : x = Insert.insert z (x \ {z}) := by ext; grind
    rw [hxz] at hf ⊢
    have hg := hf.eraseRedirect (by grind) (by grind)
    exact hins _ z (ih _ _ hg)

/-- Unions of two finite sets are finite -/
@[grind .]
theorem Finite.union (hx : Finite x) (hy : Finite y) : Finite (x ∪ y) := by
  refine hy.induction (A := fun y ↦ Finite (x ∪ y)) (by rwa [union_empty])
    fun y a ih ↦ ?_
  simp only [union_insert]
  exact ih.insert a

/-- Unions of finite sets of finite sets are finite -/
theorem Finite.sUnion (hX : Finite X) (h : ∀ y ∈ X, Finite y) : Finite (⋃₀ X) := by
  refine hX.induction (A := fun X : M ↦ (∀ y ∈ X, Finite y) → Finite (⋃₀ X))
    (fun _ ↦ by grind) (fun X a ih h ↦ ?_) h
  rw [sUnion_insert]
  exact (h a (by grind)).union (ih fun y hy ↦ h y (by grind))

section ZF

/-- The set of finite subsets of `x` -/
noncomputable def finSubsets (x : M) : M := 𝒫 x ∩₀ Finite

/-- The set of finite sequences in `x`: functions from a natural number to `x` -/
noncomputable def finSeqs (x : M) : M := ⋃₀ ran ((fun n ↦ funSet n x) ↾₀ ω)

variable [ModelsZF M] {s : M}

omit [HasOmega M] in
@[simp]
theorem mem_finSubsets_iff : y ∈ finSubsets x ↔ y ⊆ x ∧ Finite y := by
  simp [finSubsets]

omit [ModelsKP M] [HasOmega M] in
theorem mem_finSeqs_iff : s ∈ finSeqs x ↔ ∃ n ∈ (ω : M), s !: n → x := by
  simp only [finSeqs, mem_sUnion_iff,
    mem_ran_toSetRestrictedTo_iff (isSetRestrictedTo_of_definable _)]
  grind [mem_funSet_iff]

omit [ModelsKP M] [HasOmega M] in
theorem dom_isFunctionFromTo_of_mem_funSet (hs : s ∈ funSet a x) : s !: dom s → x := by
  rw [mem_funSet_iff] at hs
  rwa [hs.dom_eq]

omit [ModelsKP M] [HasOmega M] in
theorem dom_isFunctionFromTo_of_mem_finSeqs (hs : s ∈ finSeqs x) : s !: dom s → x := by
  obtain ⟨n, -, hs⟩ := mem_finSeqs_iff.mp hs
  rwa [hs.dom_eq]

omit [ModelsKP M] [HasOmega M] in
/-- Composing with an injection `f !: x ↪ y` injects `funSet a x` into `funSet a y` -/
theorem IsInjectionFromTo.compLeft_funSet (hf : f !: x ↪ y) (a : M) :
    MemStructure.compLeft f (funSet a x) !: funSet a x ↪ funSet a y :=
  hf.compLeft (isSetRestrictedTo_of_definable _) (fun _ ↦ dom_isFunctionFromTo_of_mem_funSet)
    fun _ hs ↦ mem_funSet_iff.mpr ((mem_funSet_iff.mp hs).comp hf.isFunctionFromTo)

omit [ModelsKP M] [HasOmega M] in
/-- Composing with a bijection `f !: x ↔ y` is a bijection `funSet a x ↔ funSet a y` -/
theorem IsBijectionFromTo.compLeft_funSet (hf : f !: x ↔ y) (a : M) :
    MemStructure.compLeft f (funSet a x) !: funSet a x ↔ funSet a y :=
  hf.compLeft (isSetRestrictedTo_of_definable _) (fun _ ↦ dom_isFunctionFromTo_of_mem_funSet)
    (fun _ ↦ dom_isFunctionFromTo_of_mem_funSet)
    (fun _ hs ↦ mem_funSet_iff.mpr ((mem_funSet_iff.mp hs).comp hf.isFunctionFromTo))
    fun _ ht ↦ mem_funSet_iff.mpr ((mem_funSet_iff.mp ht).comp hf.inv.isFunctionFromTo)

omit [ModelsKP M] [HasOmega M] in
/-- Composing with an injection `f !: x ↪ y` injects the finite sequences in `x` into those in
`y` -/
theorem IsInjectionFromTo.finSeqs (hf : f !: x ↪ y) :
    MemStructure.compLeft f (finSeqs x) !: finSeqs x ↪ finSeqs y := by
  refine hf.compLeft (isSetRestrictedTo_of_definable _)
    (fun _ ↦ dom_isFunctionFromTo_of_mem_finSeqs) fun s hs ↦ ?_
  obtain ⟨n, hn, hs⟩ := mem_finSeqs_iff.mp hs
  exact mem_finSeqs_iff.mpr ⟨n, hn, hs.comp hf.isFunctionFromTo⟩

omit [ModelsKP M] [HasOmega M] in
/-- Composing with a bijection `f !: x ↔ y` is a bijection `finSeqs x ↔ finSeqs y` -/
theorem IsBijectionFromTo.finSeqs (hf : f !: x ↔ y) :
    MemStructure.compLeft f (finSeqs x) !: finSeqs x ↔ finSeqs y := by
  refine hf.compLeft (isSetRestrictedTo_of_definable _)
    (fun _ ↦ dom_isFunctionFromTo_of_mem_finSeqs) (fun _ ↦ dom_isFunctionFromTo_of_mem_finSeqs)
    (fun s hs ↦ ?_) fun t ht ↦ ?_
  · obtain ⟨n, hn, hs⟩ := mem_finSeqs_iff.mp hs
    exact mem_finSeqs_iff.mpr ⟨n, hn, hs.comp hf.isFunctionFromTo⟩
  · obtain ⟨n, hn, ht⟩ := mem_finSeqs_iff.mp ht
    exact mem_finSeqs_iff.mpr ⟨n, hn, ht.comp hf.inv.isFunctionFromTo⟩

/-- Taking images under an injection `f !: x ↪ y` injects the finite subsets of `x` into those
of `y` -/
theorem IsInjectionFromTo.finSubsets (hf : f !: x ↪ y) :
    (fun z ↦ (f '' z : M)) ↾₀ finSubsets x !: finSubsets x ↪ finSubsets y := by
  refine isInjectionFromTo_toSetRestrictedTo (isSetRestrictedTo_of_definable _)
    (fun z hz ↦ ?_) fun z hz z' hz' h ↦ ?_
  · obtain ⟨hzx, hz⟩ := mem_finSubsets_iff.mp hz
    have hfz := hf.isFunctionFromTo.restrict hzx
    refine mem_finSubsets_iff.mpr ⟨hfz.ran_subset, ?_⟩
    exact hz.of_isSurjectionFromTo (isSurjectionFromTo_ran_of_isFunctionFromTo hfz)
  · have hzx := (mem_finSubsets_iff.mp hz).left
    have hzx' := (mem_finSubsets_iff.mp hz').left
    ext w
    -- for `w ∈ x`: `w ∈ z ↔ f w ∈ f '' z = f '' z' ↔ w ∈ z'` by injectivity of `f`
    by_cases hw : w ∈ x
    swap
    · grind
    suffices hfw : ∀ {a : M}, a ⊆ x → (w ∈ a ↔ f ﹫ w ∈ (f '' a : M)) by
      rw [hfw hzx, hfw hzx', h]
    intro a ha
    simp only [mem_image_iff]
    refine ⟨fun hwa ↦ ⟨w, hwa, rel_val hf.isFunction (by grind)⟩,
      fun ⟨u, hu, hfu⟩ ↦ ?_⟩
    rwa [← hf.eq (ha hu) hw (by grind)]

/-- The increasing enumerations `z ↦ (otMap z)⁻¹` of the finite subsets of a set `x` of
ordinals -/
noncomputable def enumFinSubsets (x : M) : M := (fun z ↦ (otMap z)⁻¹) ↾₀ finSubsets x

/-- For a set `x` of ordinals, `enumFinSubsets x` injects the finite subsets of `x` into the
finite sequences in `x` -/
theorem isInjectionFromTo_enumFinSubsets (hx : ∀ y ∈ x, Ordinal y) :
    enumFinSubsets x !: finSubsets x ↪ finSeqs x := by
  have hbij {z : M} (hz : z ∈ finSubsets x) : (otMap z)⁻¹ !: ot z ↔ z :=
    (isBijectionFromTo_otMap fun y hy ↦ hx y ((mem_finSubsets_iff.mp hz).left hy)).inv
  refine isInjectionFromTo_toSetRestrictedTo (isSetRestrictedTo_of_definable _)
    (fun z hz ↦ ?_) fun z hz z' hz' h ↦ ?_
  · obtain ⟨hzx, hzf⟩ := mem_finSubsets_iff.mp hz
    refine mem_finSeqs_iff.mpr ⟨ot z, ?_, (hbij hz).isFunctionFromTo.mono hzx⟩
    exact (hzf.of_isBijectionFromTo (hbij hz).inv).mem_omega (ordinal_ot fun y hy ↦ hx y (hzx hy))
  · rw [← (hbij hz).ran_eq, ← (hbij hz').ran_eq, h]

end ZF

end MemStructure

end FirstOrder.Language
