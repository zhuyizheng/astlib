/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Cardinal.Finite
import Astlib.Basic.Ordinal.Pair
import Astlib.Basic.Axiom.Choice.Semantics
/-!
# Countable sets

A set is countable if it injects into `ω`. In models of `KP` with `ω`:

* Gödel's pairing function maps `ω ×ˢ ω` injectively into `ω`, so `ω ×ˢ ω` is countable
  (`countable_omega_sprod_omega`);
* subsets, images and products of countable sets are countable;
* `countable_iff`: a set is countable iff it is empty or the image of `ω`;
* finite sets are countable, and unions of two countable sets and of finite sets of countable
  sets are countable;
* `CountablyInfinite`: sets in bijection with `ω`. A set is countable iff it is finite or
  countably infinite (`countable_iff_finite_or_countablyInfinite`).

In models of `ZF`:

* functions from a natural number to a countable set form a countable set (`Countable.funSet`);
* restricting the code `iteratedGoedelPair` of sequences gives bijections
  `seqCodeOmega n !: funSet n ω ↔ ω` for nonzero `n ∈ ω` (`isBijectionFromTo_seqCodeOmega`),
  and these combine into a bijection `finSeqCode` from the nonempty finite sequences in `ω` onto
  `ω` (`isBijectionFromTo_finSeqCode`);
* the finite sequences in a countable set form a countable set (`Countable.finSeqs`), and so do
  its finite subsets (`Countable.finSubsets`).

With countable choice, definable relations are uniformized on countable sets
(`Countable.exists_uniformization`), and a countable union of countable sets is countable
(`Countable.sUnion`).
-/

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin RudimentaryTerm MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] [HasOmega M]
  {f g x y m n m' n' : M}

/-- `x` is countable: it injects into `ω` -/
def Countable : Class M := fun x ↦ ∃ f, f !: x ↪ ω

instance : (Countable : Class M).Definable Set.univ := by
  unfold Countable
  infer_instance

omit [HasOmega M] in
theorem Countable.of_isInjectionFromTo (hy : Countable y) (hf : f !: x ↪ y) : Countable x :=
  have ⟨g, hg⟩ := hy
  ⟨g !∘ f, hg.comp hf⟩

omit [HasOmega M] in
@[grind .]
theorem Countable.of_subset (hy : Countable y) (h : x ⊆ y) : Countable x :=
  hy.of_isInjectionFromTo ((isInjectionFromTo_id x).of_ran_subset (by rwa [ran_id]))

omit [HasOmega M] in
@[simp, grind .]
theorem countable_omega : Countable (ω : M) := ⟨id ω, isInjectionFromTo_id ω⟩

omit [HasOmega M] in
@[simp, grind .]
theorem countable_empty : Countable (∅ : M) := ⟨∅, isInjectionFromTo_empty ω⟩

/-- Natural numbers are countable -/
@[grind .]
theorem countable_of_mem_omega (hn : n ∈ (ω : M)) : Countable n :=
  countable_omega.of_subset (by grind)

/-- A set is countable iff it is empty or the image of `ω` -/
theorem countable_iff : Countable x ↔ x = ∅ ∨ ∃ f, f !: ω ↠ x := by
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, ?_⟩
  · by_cases hx : x = ∅
    · tauto
    · exact .inr (exists_isSurjectionFromTo_of_isInjectionFromTo hg hx)
  · rintro (rfl | ⟨f, hf⟩)
    · exact countable_empty
    · exact ⟨leastInv f ω x, hf.leastInv ordinal_omega⟩

/-- Images of countable sets are countable -/
theorem Countable.of_isSurjectionFromTo (hx : Countable x) (hf : f !: x ↠ y) : Countable y := by
  simp only [countable_iff] at hx
  rcases hx with rfl | ⟨g, hg⟩
  · rw [eq_empty_of_isSurjectionFromTo_empty hf]
    exact countable_empty
  · simp only [countable_iff]
    exact (.inr ⟨f !∘ g, hf.comp hg⟩)

/-- `ω ×ˢ ω` is countable -/
theorem countable_omega_sprod_omega : Countable ((ω : M) ×ˢ (ω : M)) :=
  ⟨goedelPairOfPair ↾₀ ((ω : M) ×ˢ ω),
    isInjectionFromTo_goedelPairOfPair (by grind) fun _ hm _ hn ↦ goedelPair_mem_omega hm hn⟩

/-- Products of countable sets are countable -/
@[grind .]
theorem Countable.sprod (hx : Countable x) (hy : Countable y) : Countable (x ×ˢ y) :=
  have ⟨_, hf⟩ := hx
  have ⟨_, hg⟩ := hy
  countable_omega_sprod_omega.of_isInjectionFromTo (hf.prodMap hg)

/-- A countable set is in bijection with a natural number or with `ω` -/
theorem Countable.exists_isBijectionFromTo (hx : Countable x) :
    ∃ α, (α ∈ (ω : M) ∨ α = ω) ∧ ∃ g, g !: x ↔ α := by
  obtain ⟨f, hf⟩ := hx
  have hSo (z : M) (hz : z ∈ ran f) : Ordinal z := by grind
  refine ⟨ot (ran f), ?_, _, (isBijectionFromTo_otMap hSo).comp
    (isBijectionFromTo_ran_of_isInjectionFromTo hf)⟩
  exact mem_or_eq_of_ole (ot_ole ordinal_omega (by grind))

/-- Finite sets are countable -/
@[grind .]
theorem Finite.countable (hx : Finite x) : Countable x :=
  have ⟨_, hn, _, hf⟩ := hx
  (countable_of_mem_omega hn).of_isInjectionFromTo hf.isInjectionFromTo

/-- Singletons are countable -/
@[simp, grind .]
theorem countable_singleton (a : M) : Countable ({a} : M) := (finite_singleton a).countable

/-- Unions of two countable sets are countable -/
@[grind .]
theorem Countable.union (hx : Countable x) (hy : Countable y) : Countable (x ∪ y) := by
  rcases countable_iff.mp hx with rfl | ⟨f, hf⟩
  · rwa [empty_union]
  rcases countable_iff.mp hy with rfl | ⟨g, hg⟩
  · rwa [union_empty]
  -- glue `f` and `g` into a surjection from `2 ×ˢ ω = disjUnion ω ω` onto `x ∪ y`
  have hfg : disjUnionMap f g ω ω !: succ (succ (∅ : M)) ×ˢ (ω : M) ↠ x ∪ y := by
    rw [← disjUnion_self]
    exact hf.disjUnionMap hg
  exact ((countable_of_mem_omega (by grind)).sprod countable_omega).of_isSurjectionFromTo hfg

/-- Unions of finite sets of countable sets are countable -/
theorem Finite.countable_sUnion {X : M} (hX : Finite X) (h : ∀ y ∈ X, Countable y) :
    Countable (⋃₀ X) := by
  refine hX.induction (A := fun X : M ↦ (∀ y ∈ X, Countable y) → Countable (⋃₀ X))
    (fun _ ↦ by grind) (fun X a ih h ↦ ?_) h
  rw [sUnion_insert]
  exact (h a (by grind)).union (ih fun y hy ↦ h y (by grind))

section CountablyInfinite

/-- `x` is countably infinite: it is in bijection with `ω` -/
def CountablyInfinite : Class M := fun x ↦ ∃ f, f !: x ↔ ω

instance : (CountablyInfinite : Class M).Definable Set.univ := by
  unfold CountablyInfinite
  infer_instance

omit [HasOmega M] in
@[simp, grind .]
theorem countablyInfinite_omega : CountablyInfinite (ω : M) :=
  ⟨id ω, isInjectionFromTo_id ω, isSurjectionFromTo_id ω⟩

omit [HasOmega M] in
@[grind .]
theorem CountablyInfinite.countable (hx : CountablyInfinite x) : Countable x :=
  have ⟨f, hf⟩ := hx
  ⟨f, hf.isInjectionFromTo⟩

omit [HasOmega M] in
/-- Sets in bijection with countably infinite sets are countably infinite -/
theorem CountablyInfinite.of_isBijectionFromTo (hx : CountablyInfinite x) (hf : f !: x ↔ y) :
    CountablyInfinite y :=
  have ⟨g, hg⟩ := hx
  ⟨g !∘ f⁻¹, hg.comp hf.inv⟩

/-- Finite sets are not countably infinite -/
theorem Finite.not_countablyInfinite (hx : Finite x) : ¬CountablyInfinite x := fun ⟨_, hf⟩ ↦
  not_finite_omega (hx.of_isBijectionFromTo hf)

/-- A set is countable iff it is finite or countably infinite -/
theorem countable_iff_finite_or_countablyInfinite :
    Countable x ↔ Finite x ∨ CountablyInfinite x := by
  refine ⟨fun hx ↦ ?_, fun h ↦ h.elim Finite.countable CountablyInfinite.countable⟩
  obtain ⟨α, hα | rfl, g, hg⟩ := hx.exists_isBijectionFromTo
  · exact .inl ⟨α, hα, g, hg⟩
  · exact .inr ⟨g, hg⟩

/-- A set is countably infinite iff it is countable and not finite -/
theorem countablyInfinite_iff : CountablyInfinite x ↔ Countable x ∧ ¬Finite x := by
  rw [countable_iff_finite_or_countablyInfinite]
  have := Finite.not_countablyInfinite (x := x)
  tauto

end CountablyInfinite


section ZF

variable [ModelsZF M] {k s t : M}

/-- The code `t ↦ iteratedGoedelPair t n` of the sequences on `n` in `ω` -/
noncomputable def seqCodeOmega (n : M) : M := (fun t ↦ iteratedGoedelPair t n) ↾₀ funSet n ω

/-- `seqCodeOmega n` is a bijection from `funSet n ω` onto `ω` for nonzero `n ∈ ω` -/
theorem isBijectionFromTo_seqCodeOmega (hn : n ∈ (ω : M)) (hn₀ : n ≠ ∅) :
    seqCodeOmega n !: funSet n (ω : M) ↔ ω := by
  obtain ⟨k, hk, rfl⟩ := (mem_omega_cases hn).resolve_left hn₀
  have hr := isSetRestrictedTo_of_definable (G := fun t ↦ iteratedGoedelPair t (succ k))
    (funSet (succ k) (ω : M))
  have hinj : seqCodeOmega (succ k) !: funSet (succ k) (ω : M) ↪ ω := by
    refine isInjectionFromTo_toSetRestrictedTo hr (fun t ht ↦ ?_) fun t ht t' ht' h ↦ ?_
    · rw [mem_funSet_iff] at ht
      exact iteratedGoedelPair_mem_omega hn (by grind)
    · rw [mem_funSet_iff] at ht ht'
      exact iteratedGoedelPair_inj hk ht ht' h
  refine ⟨hinj, (isSurjectionFromTo_iff_of_isFunctionFromTo hinj.isFunctionFromTo).mpr
    fun m hm ↦ ?_⟩
  obtain ⟨t, ht, rfl⟩ := exists_iteratedGoedelPair_eq hk hm
  rw [← mem_funSet_iff] at ht
  exact ⟨t, ht, val_toSetRestrictedTo hr ht⟩

/-- Functions from a natural number to `ω` form a countable set -/
theorem countable_funSet_omega (hn : n ∈ (ω : M)) : Countable (funSet n (ω : M)) := by
  rcases eq_or_ne n ∅ with rfl | hn₀
  swap
  · exact ⟨seqCodeOmega n, (isBijectionFromTo_seqCodeOmega hn hn₀).isInjectionFromTo⟩
  -- the only function from `∅` is `∅`
  refine (countable_singleton ∅).of_subset fun f hf ↦ ?_
  simpa using (mem_funSet_iff.mp hf).eq_empty_of_dom_empty

/-- Functions from a natural number to a countable set form a countable set -/
theorem Countable.funSet (hx : Countable x) (hn : n ∈ (ω : M)) :
    Countable (MemStructure.funSet n x) :=
  have ⟨_, hf⟩ := hx
  (countable_funSet_omega hn).of_isInjectionFromTo (hf.compLeft_funSet n)

/-- `s ↦ !(k, iteratedGoedelPair s (succ k))` for a sequence `s` on `succ k` -/
noncomputable def finSeqCodePair : ClassFunction M := fun s ↦
  !(⋃₀ dom s, iteratedGoedelPair s (dom s))

instance : (finSeqCodePair : ClassFunction M).Definable Set.univ := by
  unfold finSeqCodePair
  infer_instance

omit [ModelsKP M] in
theorem mem_finSeqs_omega_sdiff_iff :
    s ∈ finSeqs (ω : M) \ {∅} ↔ ∃ k ∈ (ω : M), s !: succ k → ω := by
  simp only [mem_sdiff_iff, mem_finSeqs_iff, mem_singleton_iff]
  refine ⟨fun ⟨⟨n, hn, hs⟩, hs₀⟩ ↦ ?_, fun ⟨k, hk, hs⟩ ↦ ⟨⟨succ k, by grind⟩, by grind⟩⟩
  rcases mem_omega_cases hn with rfl | ⟨k, hk, rfl⟩
  · grind [hs.eq_empty_of_dom_empty]
  · exact ⟨k, hk, hs⟩

omit [ModelsKP M] in
theorem finSeqCodePair_eq (hk : k ∈ (ω : M)) (hs : s !: succ k → ω) :
    finSeqCodePair s = !(k, iteratedGoedelPair s (succ k)) := by
  rw [finSeqCodePair, hs.dom_eq, sUnion_succ (ordinal_of_mem ordinal_omega hk).transitive]

/-- `finSeqCodePair` is an injection from the nonempty finite sequences in `ω` into `ω ×ˢ ω` -/
theorem isInjectionFromTo_finSeqCodePair :
    finSeqCodePair ↾₀ (finSeqs (ω : M) \ {∅}) !: finSeqs (ω : M) \ {∅} ↪ (ω : M) ×ˢ (ω : M) := by
  refine isInjectionFromTo_toSetRestrictedTo (isSetRestrictedTo_of_definable _)
    (fun s hs ↦ ?_) fun s hs s' hs' h ↦ ?_
  · simp only [mem_finSeqs_omega_sdiff_iff] at hs
    obtain ⟨k, hk, hs⟩ := hs
    simp only [mem_sprod_iff]
    refine ⟨k, hk, iteratedGoedelPair s (succ k), ?_, finSeqCodePair_eq hk hs⟩
    apply iteratedGoedelPair_mem_omega <;> grind
  · simp only [mem_finSeqs_omega_sdiff_iff] at hs hs'
    obtain ⟨k, hk, hs⟩ := hs
    obtain ⟨k', hk', hs'⟩ := hs'
    simp only [finSeqCodePair_eq hk hs, finSeqCodePair_eq hk' hs',
      orderedPair_eq_orderedPair_iff] at h
    obtain ⟨rfl, h⟩ := h
    exact iteratedGoedelPair_inj hk hs hs' h

/-- `finSeqCodePair` is a bijection from the nonempty finite sequences in `ω` onto `ω ×ˢ ω` -/
theorem isBijectionFromTo_finSeqCodePair :
    finSeqCodePair ↾₀ (finSeqs (ω : M) \ {∅}) !: finSeqs (ω : M) \ {∅} ↔ (ω : M) ×ˢ (ω : M) := by
  have hr := isSetRestrictedTo_of_definable (G := finSeqCodePair) (finSeqs (ω : M) \ {∅})
  have hinj := isInjectionFromTo_finSeqCodePair (M := M)
  refine ⟨hinj, ?_⟩
  rw [isSurjectionFromTo_iff_of_isFunctionFromTo hinj.isFunctionFromTo]
  intro w hw
  simp only [mem_sprod_iff] at hw
  obtain ⟨k, hk, m, hm, rfl⟩ := hw
  obtain ⟨s, hs, rfl⟩ := exists_iteratedGoedelPair_eq hk hm
  have hsT : s ∈ finSeqs (ω : M) \ {∅} := by
    simp only [mem_finSeqs_omega_sdiff_iff]
    exact ⟨k, hk, hs⟩
  exact ⟨s, hsT, by rw [val_toSetRestrictedTo hr hsT, finSeqCodePair_eq hk hs]⟩

/-- The bijection from the nonempty finite sequences in `ω` onto `ω`: Gödel's pairing function
applied to the length and the code of a sequence -/
noncomputable def finSeqCode : M :=
  (goedelPairOfPair ↾₀ ((ω : M) ×ˢ (ω : M))) !∘ (finSeqCodePair ↾₀ (finSeqs (ω : M) \ {∅}))

/-- `finSeqCode` is a bijection from the nonempty finite sequences in `ω` onto `ω` -/
theorem isBijectionFromTo_finSeqCode : finSeqCode !: finSeqs (ω : M) \ {∅} ↔ ω :=
  isBijectionFromTo_goedelPairOfPair_omega.comp isBijectionFromTo_finSeqCodePair

/-- The finite sequences in `ω` form a countable set -/
theorem countable_finSeqs_omega : Countable (finSeqs (ω : M)) := by
  have hT : Countable (finSeqs (ω : M) \ {∅}) :=
    ⟨_, isBijectionFromTo_finSeqCode.isInjectionFromTo⟩
  exact (hT.union (countable_singleton ∅)).of_subset fun s hs ↦ by grind

/-- The finite sequences in a countable set form a countable set -/
theorem Countable.finSeqs (hx : Countable x) : Countable (MemStructure.finSeqs x) :=
  have ⟨_, hf⟩ := hx
  countable_finSeqs_omega.of_isInjectionFromTo hf.finSeqs

/-- The finite subsets of a countable set form a countable set: they inject into the finite
subsets of `ω`, which inject into the finite sequences in `ω` by increasing enumeration -/
theorem Countable.finSubsets (hx : Countable x) : Countable (MemStructure.finSubsets x) :=
  have ⟨_, hf⟩ := hx
  countable_finSeqs_omega.of_isInjectionFromTo
    ((isInjectionFromTo_enumFinSubsets fun _ hy ↦ ordinal_of_mem ordinal_omega hy).comp
      hf.finSubsets)

end ZF

section CountableChoice

variable [ModelsZFCC M]

/-- Under countable choice, a definable `P` is uniformized on every countable set `a` -/
theorem Countable.exists_uniformization {a : M} (ha : Countable a) (P : Multiclass M 2)
    [P.Definable Set.univ] :
    ∃ f, IsFunction f ∧ dom f = a ∧ ∀ x ∈ a, (∃ y, P ![x, y]) → P ![x, f ﹫ x] := by
  -- uniformize `P ![i⁻¹ ﹫ n, y]` on `ω` for an injection `i !: a ↪ ω`
  obtain ⟨i, hi⟩ := ha
  have hib := isBijectionFromTo_ran_of_isInjectionFromTo hi
  obtain ⟨g, hg, hdom, hgP⟩ := exists_uniformization_omega (fun ys ↦ P ![i⁻¹ ﹫ ys 0, ys 1])
  have hgi : dom (g !∘ i) = a := by grind
  refine ⟨g !∘ i, hg.comp hi.isFunction, hgi, fun x hx hP ↦ ?_⟩
  specialize hgP (i ﹫ x) (by grind) (by simpa [hib.inv_val_val hx] using hP)
  simpa [comp_val hg hi.isFunction (hgi ▸ hx), hib.inv_val_val hx] using hgP

/-- Under countable choice, a countable union of countable sets is countable -/
theorem Countable.sUnion (hx : Countable x) (h : ∀ y ∈ x, Countable y) : Countable (⋃₀ x) := by
  -- `f ﹫ y !: ω ↠ y` for every nonempty `y ∈ x`
  obtain ⟨f, -, -, hf⟩ := hx.exists_uniformization (fun ys ↦ ys 1 !: ω ↠ ys 0)
  rw [countable_iff] at hx
  rcases hx with rfl | ⟨e, he⟩
  · grind
  -- `z ↦ f ﹫ (e ﹫ left z) ﹫ right z` maps `ω ×ˢ ω` onto a superset of `⋃₀ x`
  have hr := isSetRestrictedTo_of_sigma (G := fun z ↦ (f ﹫ (e ﹫ left z)) ﹫ right z)
    ((ω : M) ×ˢ (ω : M))
  have hH := isSurjectionFromTo_dom_ran (isFunction_toSetRestrictedTo hr)
  rw [dom_toSetRestrictedTo hr] at hH
  refine (countable_omega_sprod_omega.of_isSurjectionFromTo hH).of_subset fun z hz ↦ ?_
  simp only [mem_sUnion_iff] at hz
  obtain ⟨y, hy, hzy⟩ := hz
  obtain ⟨n, hn, rfl⟩ := he.exists_mem_val hy
  specialize h (e ﹫ n) hy
  simp only [countable_iff] at h
  rcases h with h₀ | hex
  · simp [h₀] at hzy
  specialize hf (e ﹫ n) hy (by simpa using hex)
  have hfy : f ﹫ (e ﹫ n) !: ω ↠ e ﹫ n := by simpa using hf
  obtain ⟨k, hk, rfl⟩ := hfy.exists_mem_val hzy
  simp only [mem_ran_toSetRestrictedTo_iff hr]
  exact ⟨!(n, k), by grind, by simp⟩

end CountableChoice

end MemStructure

end FirstOrder.Language
