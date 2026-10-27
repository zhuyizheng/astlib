/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Axiom.ZF.Syntax
import Astlib.Basic.Ordinal.Omega
import Astlib.Basic.SetOperation.Powerset
import Astlib.Basic.Order.StrictWellOrder
/-!
# Models of `ZF`

`ModelsZF M` says that `M` is a model of `ZF`. Models of `ZF`
* are models of `KP₀`, and satisfy collection, comprehension and replacement for all definable
  relations and classes;
* are foundational, closed under power sets, and contain `ω`;
* are models of `KP` (`∈`-induction is `induction_of_modelsZF`) and of `KPInf`.

## `∈`-induction

`ZF` contains `KP₀` and the foundation axiom. To prove the `∈`-induction schema, every set `x` is
shown to lie in a transitive set: the union of the iterated unions `⋃ⁿ x` for `n ∈ ω`. These are
given by approximations `g` on `succ k` with `g ﹫ ∅ = x` and `g ﹫ succ n = ⋃₀ (g ﹫ n)`
(`IsIterUnion`), which exist by induction on `ω`, agree by induction on `ω`, and are collected by
replacement.
-/

namespace FirstOrder

namespace Language

open FirstOrder Language BoundedFormula Fin MemStructure

variable {L : FirstOrder.Language} {M : Type*}
  [L.MemStructure M] [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M]

class ModelsZF {L : FirstOrder.Language} (M : Type*) [h : L.MemStructure M] where
  modelsZF : @Theory.Model L M h.toStructure ZF

instance [hM : ModelsZF M] : ModelsKP₀ M := ⟨hM.modelsZF.mono KP₀_subset_ZF⟩

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] in
/-- Collection for definable relations -/
theorem MemStructure.exists_collection_of_modelsZF [hM : ModelsZF M] (F : Multiclass M 2)
    [hF : F.Definable Set.univ] (a : M) (h : ∀ u ∈ a, ∃ w, F ![u, w]) :
    ∃ b : M, ∀ u ∈ a, ∃ w ∈ b, F ![u, w] := by
  obtain ⟨n, φ, vs, -, rfl⟩ := hF.isDefinable
  have hφ' (u w : M) : (φ.multiclass.slice vs : Multiclass M 2) ![u, w] ↔
      φ.switchBound〘snoc (snoc vs u) w〙 := by
    simp [snoc_snoc_eq_append]
  simp only [hφ'] at h ⊢
  replace hM := hM.modelsZF
  simp only [ZF, Theory.model_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    realize_iff_realize'] at hM
  have : φ.switchBound.collection ∈ collectionSchema := ⟨n, φ.switchBound, rfl⟩
  specialize hM φ.switchBound.collection (by simp [this])
  simp only [BoundedFormula.collection, realize'_alls, realize'_ex, realize'_imp,
    BoundedFormula.realize_allMem, BoundedFormula.realize_exMem, realize'_substBoundBound] at hM
  simpa using hM (snoc vs a) (by simpa using h)

end Language

end FirstOrder

namespace FirstOrder.Language.MemStructure

open FirstOrder Language BoundedFormula Fin

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M]

section Comprehension

/-- Comprehension for definable classes in models of `ZF` -/
instance [hM : ModelsZF M] (x : M) (A : Class M) [hA : A.Definable Set.univ] :
    HasComprehension x A where
  hasComprehension := by
    replace hM := hM.modelsZF
    simp only [ZF, Theory.model_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      realize_iff_realize'] at hM
    obtain ⟨n, φ, vs, _, hA⟩ := hA.isDefinable
    have : φ.switchBound.comprehension ∈ comprehensionSchema := ⟨n, φ.switchBound, rfl⟩
    specialize hM φ.switchBound.comprehension (by simp [this])
    simp only [BoundedFormula.comprehension, Function.comp_apply, realize'_alls, realize'_ex,
      realize'_all, realize'_iff, realize'_mem, Term.realize'_var', snoc_snoc_castAdd_one_last,
      snoc_last, realize'_inf, realize'_substBoundBound] at hM
    obtain ⟨a, ha⟩ := hM (snoc vs x)
    refine ⟨a, fun z ↦ ?_⟩
    rw [ha]
    simp only [snoc_nat, val_castAdd, val_last, Order.lt_add_one_iff, le_add_iff_nonneg_right,
      _root_.zero_le, ↓reduceDIte, lt_add_iff_pos_right, Order.lt_one_iff, lt_self_iff_false,
      snoc_snoc_snoc_comp_snoc_castAdd_three_last, and_congr_right_iff]
    simp only [snoc_eq_append, Nat.reduceAdd, realize'_switchBound, Class.iff_toMulticlass, hA,
      Multiclass.slice, multiclass]
    intro _
    rfl

/-- In models of `ZF`, `u ↦ b ∩₀ {w | R u w}` is definable for a definable relation `R` -/
instance [ModelsZF M] (b : M) {R : M → M → Prop}
    [Multiclass.Definable (fun ys : Fin 2 → M ↦ R (ys 0) (ys 1)) Set.univ] :
    ClassFunction.Definable (fun u ↦ b ∩₀ fun w ↦ R u w) Set.univ :=
  .of_mem_iff (R := fun u z ↦ z ∈ b ∧ R u z) fun _ _ ↦ mem_comprehension_iff _ _ _

end Comprehension

section Replacement

/-- Replacement for definable relations in models of `ZF` -/
instance [ModelsZF M] (x : M) (F : Multiclass M 2) [hF : F.Definable Set.univ] :
  HasReplacement x F where
  hasReplacement hFx := by
    obtain ⟨m, φ, vs, -, rfl⟩ := hF.isDefinable
    obtain ⟨b, hb⟩ := exists_collection_of_modelsZF (φ.multiclass.slice vs) x
      (fun u hu ↦ (hFx u hu).exists)
    -- `χ(z, vs, x)` says `∃ u ∈ x, φ(u, z, vs)`
    let χ : L.BoundedFormula' (1 + (m + 1)) := ∃'∈ &-1
      φ.castAssoc.switchBound.substBoundBound (snoc (castAdd 2) (last (1 + m + 1)))
    refine ⟨b ∩₀ χ.multiclass.slice (snoc vs x), fun z ↦ ?_⟩
    simp only [mem_comprehension_iff, Multiclass.toClass_iff]
    simp only [Multiclass.slice, BoundedFormula.multiclass, χ, append_snoc,
      BoundedFormula.realize_exMem, realize'_substBoundBound, Term.realize'_var', snoc_last,
      snoc_snoc_comp_snoc_castAdd_two_last, Function.comp_apply, Nat.add_eq]
    simp only [snoc_eq_append, realize'_switchBound, realize'_castAssoc]
    simp only [append_left_eq_cons, Fin.cast_refl, Function.comp_id]
    simp only [Multiclass.slice, BoundedFormula.multiclass] at hb hFx
    refine ⟨fun ⟨_, u, hu, hz⟩ ↦ ⟨u, hu, hz⟩, fun ⟨u, hu, hz⟩ ↦ ⟨?_, u, hu, hz⟩⟩
    obtain ⟨w, hwb, hw⟩ := hb u hu
    rwa [(hFx u hu).unique hz hw]

end Replacement

section Foundation

/-- Models of `ZF` are foundational -/
instance [hM : ModelsZF M] : Foundational M where
  hasMemMin x hx := by
    have h : M ⊨ foundationAxiom := hM.modelsZF.realize_of_mem foundationAxiom (by simp [ZF])
    rw [realize_iff_realize'] at h
    replace h : ∀ x : M, (∃ y, y ∈ x) → ∃ y ∈ x, ∀ z ∈ y, z ∉ x := by
      simpa [foundationAxiom, snoc_nat] using h
    simp only [ne_empty_iff] at hx
    exact h x hx

end Foundation

section Powerset

/-- Models of `ZF` are closed under power sets -/
instance [hM : ModelsZF M] (x : M) : HasPowerset x where
  hasPowerset := by
    have hZF := hM.modelsZF
    simp only [ZF, Theory.model_iff, Set.mem_union, Set.mem_insert_iff] at hZF
    specialize hZF powersetAxiom (by simp)
    replace hZF : ∀ x : M, ∃ b : M, ∀ z, z ⊆ x → z ∈ b := by
      simpa [powersetAxiom, snoc_nat] using hZF
    obtain ⟨b, hb⟩ := hZF x
    refine ⟨b ∩₀ Class.Subset x, fun z ↦ ?_⟩
    simp only [mem_comprehension_iff, Class.subset_iff]
    grind

end Powerset

/-- Models of `ZF` contain `ω` -/
instance [hM : ModelsZF M] : HasOmega M :=
  hasOmega_of_infinityAxiom (hM.modelsZF.realize_of_mem _ (by simp [ZF]))

/-- A class function with a definable graph restricts to every set in models of `ZF` -/
theorem isSetRestrictedTo_of_definable [ModelsZF M] {G : ClassFunction M}
    [(G : Multiclass M 2).Definable Set.univ] (x : M) : IsSetRestrictedTo G x :=
  isSetRestrictedTo_of_hasReplacement G.pairGraph_iff x

/-- `p ↦ G p ↾₀ D p` is definable for a family `G` of class functions with a definable graph and
a definable class function `D` -/
theorem ClassFunction.Definable.toSetRestrictedTo [ModelsZF M] {G : M → ClassFunction M}
    [hG : Multiclass.Definable (fun xs : Fin 3 → M ↦ G (xs 0) (xs 1) = xs 2) Set.univ]
    {D : ClassFunction M} [D.Definable Set.univ] :
    ClassFunction.Definable (fun p ↦ G p ↾₀ D p) Set.univ := by
  let R : Multiclass M 3 := fun xs ↦ G (xs 0) (xs 1) = xs 2
  -- `w = G p ↾₀ D p` iff `w` is a function on `D p` agreeing with `G p`
  refine .of_iff (F := fun xs : Fin 2 → M ↦ IsFunction (xs 1) ∧
    (∀ t, t ∈ dom (xs 1) ↔ t ∈ D (xs 0)) ∧ ∀ t, t ∈ dom (xs 1) → R ![xs 0, t, xs 1 ﹫ t])
    fun p w ↦ ?_
  have hres := isSetRestrictedTo_of_definable (G := G p) (D p)
  simp only [R, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  refine ⟨fun ⟨hw, hdom, hval⟩ ↦ toSetRestrictedTo_eq hw (by ext; exact hdom _)
    fun t ht ↦ (hval t ((hdom t).mpr ht)).symm, ?_⟩
  rintro rfl
  exact ⟨isFunction_toSetRestrictedTo hres, fun t ↦ by rw [dom_toSetRestrictedTo hres],
    fun t ht ↦ (val_toSetRestrictedTo hres (by rwa [dom_toSetRestrictedTo hres] at ht)).symm⟩

end FirstOrder.Language.MemStructure

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin RudimentaryTerm MemStructure

namespace FirstOrder.Language

namespace RudimentaryTerm

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] {n : ℕ}

/-- The `Δ₀` formula saying that `g` is a function on `succ k` with `g ﹫ ∅ = x` and
`g ﹫ succ m = ⋃₀ (g ﹫ m)` for `m ∈ k` -/
noncomputable def isIterUnion (x g k : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  -- `[x, g, k]`
  ((ᵣ1).isFunction ⊓ (&0 =₀ &1).substBoundRud ![(ᵣ1).dom, (ᵣ2).succ] ⊓
    (&0 =₀ &1).substBoundRud ![(ᵣ1) ﹫ ∅, ᵣ0] ⊓
    ∀₀∈ &2 ((&0 =₀ &1).substBoundRud ![(ᵣ1) ﹫ (ᵣ3).succ, ᵣ⋃₀ ((ᵣ1) ﹫ (ᵣ3))]) :
      L.DeltaZeroBoundedFormula 3).substBoundRud ![x, g, k]

instance (x g k : L.RudimentaryTerm n) [x.CharFree] [g.CharFree] [k.CharFree] :
    (isIterUnion x g k).RelFree := by
  unfold isIterUnion; infer_instance

end RudimentaryTerm

namespace MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] {x g g' k k' m : M}

/-- `g` is the approximation of length `k` of `n ↦ ⋃ⁿ x`: a function on `succ k` with
`g ﹫ ∅ = x` and `g ﹫ succ m = ⋃₀ (g ﹫ m)` for `m ∈ k` -/
def IsIterUnion (x g k : M) : Prop :=
  IsFunction g ∧ dom g = succ k ∧ g ﹫ ∅ = x ∧ ∀ m ∈ k, g ﹫ succ m = ⋃₀ (g ﹫ m)

theorem isIterUnion_iff : IsIterUnion x g k ↔
    IsFunction g ∧ dom g = succ k ∧ g ﹫ ∅ = x ∧ ∀ m ∈ k, g ﹫ succ m = ⋃₀ (g ﹫ m) :=
  .rfl

theorem IsIterUnion.isFunction (hg : IsIterUnion x g k) : IsFunction g := hg.left

theorem IsIterUnion.dom_eq (hg : IsIterUnion x g k) : dom g = succ k := hg.right.left

theorem IsIterUnion.val_empty (hg : IsIterUnion x g k) : g ﹫ ∅ = x := hg.right.right.left

theorem IsIterUnion.val_succ (hg : IsIterUnion x g k) (hm : m ∈ k) :
    g ﹫ succ m = ⋃₀ (g ﹫ m) :=
  hg.right.right.right m hm

variable [ModelsZF M]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isIterUnion {n : ℕ}
    (x g k : L.RudimentaryTerm n) [x.CharFree] [g.CharFree] [k.CharFree] (xs : Fin n → M) :
    (isIterUnion x g k).toBoundedFormula 〘xs〙 ↔ IsIterUnion (x〘xs〙 : M) g〘xs〙 k〘xs〙 := by
  simp only [isIterUnion, DeltaZeroBoundedFormula.realize_substBoundRud]
  simp only [toBoundedFormula_inf, realize'_inf, DeltaZeroBoundedFormula.toBoundedFormula,
    BoundedFormula.realize_allMem, DeltaZeroBoundedFormula.realize_substBoundRud]
  simp [IsIterUnion, snoc_nat, and_assoc]

/-- Two approximations agree on their common domain -/
theorem IsIterUnion.val_eq_val (hg : IsIterUnion x g k) (hg' : IsIterUnion x g' k')
    (hk : k ∈ (ω : M)) (hk' : k' ∈ (ω : M)) (hm : m ∈ succ k) (hm' : m ∈ succ k') :
    g ﹫ m = g' ﹫ m := by
  -- `[m, g, g', d]`: `m ∈ d → g ﹫ m = g' ﹫ m`
  let φ : L.DeltaZeroBoundedFormula 4 :=
    &0 ∈₀ &3 ⟹ (&0 =₀ &1).substBoundRud ![(ᵣ1) ﹫ (ᵣ0), (ᵣ2) ﹫ (ᵣ0)]
  let A : Class M := φ.toBoundedFormula.multiclass.slice ![g, g', succ k ∩ succ k']
  have hA (m : M) : A m ↔ (m ∈ succ k ∩ succ k' → g ﹫ m = g' ﹫ m) := by
    simp [A, φ, append_left_eq_cons]
  -- induction on `ω`, via the set `ω ∩₀ A`
  have hkω : succ k ⊆ ω := by grind
  suffices hmA : m ∈ ω ∩₀ A by
    simp only [mem_comprehension_iff, hA] at hmA
    exact hmA.right (by simp [hm, hm'])
  have hmω : m ∈ ω := hkω hm
  simp only [mem_omega_iff] at hmω
  refine IsNat.mem_of_inductive hmω ?_ fun n hn _ ↦ ?_
  · simp only [mem_comprehension_iff, hA]
    exact ⟨empty_mem_omega, by simp [hg.val_empty, hg'.val_empty]⟩
  · simp only [mem_comprehension_iff, hA] at hn ⊢
    obtain ⟨hn, ih⟩ := hn
    refine ⟨succ_mem_omega hn, fun hsn ↦ ?_⟩
    simp only [mem_inter_iff] at hsn
    have hnk : n ∈ k := mem_of_succ_mem_succ (ordinal_of_mem ordinal_omega hk).transitive hsn.left
    have hnk' : n ∈ k' :=
      mem_of_succ_mem_succ (ordinal_of_mem ordinal_omega hk').transitive hsn.right
    rw [hg.val_succ hnk, hg'.val_succ hnk', ih (by simp [hnk, hnk'])]

theorem isIterUnion_singleton (x : M) : IsIterUnion x {!(∅, x)} ∅ := by
  have hf : IsFunction ({!(∅, x)} : M) := ⟨by grind, by grind⟩
  refine ⟨hf, ?_, ?_, by simp⟩
  · ext z
    simp [mem_dom_iff]
  · grind

/-- An approximation of length `k` extends to one of length `succ k` -/
theorem IsIterUnion.extend (hg : IsIterUnion x g k) (hk : Ordinal k) :
    IsIterUnion x (g ∪ {!(succ k, ⋃₀ (g ﹫ k))}) (succ k) := by
  set g' := g ∪ {!(succ k, ⋃₀ (g ﹫ k))}
  have hkg (b : M) : !(succ k, b) ∉ g := by
    intro h
    have hdom : succ k ∈ dom g := by
      simp only [mem_dom_iff]
      exact ⟨b, h⟩
    rw [hg.dom_eq] at hdom
    exact notMem_self _ hdom
  have hg' (a b : M) : !(a, b) ∈ g' ↔ !(a, b) ∈ g ∨ (a = succ k ∧ b = ⋃₀ (g ﹫ k)) := by grind
  have hgfun : IsFunction g' := by
    refine ⟨by grind [hg.isFunction], fun a b₁ b₂ h₁ h₂ ↦ ?_⟩
    rw [hg'] at h₁ h₂
    rcases h₁ with h₁ | ⟨rfl, rfl⟩
    · rcases h₂ with h₂ | ⟨rfl, rfl⟩
      · exact hg.isFunction.eq h₁ h₂
      · by_contra
        exact hkg b₁ h₁
    · rcases h₂ with h₂ | ⟨-, rfl⟩
      · by_contra
        exact hkg b₂ h₂
      · rfl
  have hgdom : dom g' = succ (succ k) := by
    ext a
    simp only [mem_dom_iff, hg', ← hg.dom_eq]
    grind
  have hgval (z : M) (hz : z ∈ succ k) : g' ﹫ z = g ﹫ z := by grind [hg.dom_eq]
  refine ⟨hgfun, hgdom, ?_, fun m hm ↦ ?_⟩
  · rw [hgval _ (by grind [hg.dom_eq]), hg.val_empty]
  · rcases mem_or_eq_of_mem_succ hm with hm | rfl
    · rw [hgval _ (succ_mem_succ hk hm), hgval _ (mem_succ_of_mem hm), hg.val_succ hm]
    · rw [hgfun.val_eq_of_rel (by rw [hg']; exact .inr ⟨rfl, rfl⟩), hgval _ (mem_succ_self _)]

variable (x) in
/-- The relation `v = ⋃ⁿ x`, i.e. `v = g ﹫ n` for an approximation `g` of length `n` -/
noncomputable def iterUnionVal : Multiclass M 2 :=
  -- `[n, v, g, x]`
  ((isIterUnion (ᵣ3) (ᵣ2) (ᵣ0) ⊓ (&0 =₀ &1).substBoundRud ![ᵣ1, (ᵣ2) ﹫ (ᵣ0)] :
    L.DeltaZeroBoundedFormula 4).toBoundedFormula.multiclass.slice ![x]).ex

theorem iterUnionVal_iff (n v : M) :
    iterUnionVal x ![n, v] ↔ ∃ g, IsIterUnion x g n ∧ v = g ﹫ n := by
  simp only [iterUnionVal, Multiclass.ex_iff, Multiclass.slice, BoundedFormula.multiclass,
    toBoundedFormula_inf, realize'_inf]
  simp [append_right_eq_snoc]

instance : (iterUnionVal x).Definable Set.univ := by
  unfold iterUnionVal; infer_instance

/-- Approximations of every length in `ω` exist -/
theorem exists_isIterUnion (hk : k ∈ (ω : M)) : ∃ g, IsIterUnion x g k := by
  let A : Class M := (iterUnionVal x).ex
  have hA (k : M) : A k ↔ ∃ g, IsIterUnion x g k := by
    simp [A, iterUnionVal_iff]
  -- induction on `ω`, via the set `ω ∩₀ A`
  suffices hkA : k ∈ ω ∩₀ A by
    simp only [mem_comprehension_iff, hA] at hkA
    exact hkA.right
  simp only [mem_omega_iff] at hk
  refine IsNat.mem_of_inductive hk ?_ fun n hn _ ↦ ?_
  · simp only [mem_comprehension_iff, hA]
    exact ⟨empty_mem_omega, _, isIterUnion_singleton x⟩
  · simp only [mem_comprehension_iff, hA] at hn ⊢
    obtain ⟨hn, g, hg⟩ := hn
    exact ⟨succ_mem_omega hn, _, hg.extend (ordinal_of_mem ordinal_omega hn)⟩

/-- Every set is a subset of a transitive set: `⋃ₙ ⋃ⁿ x` -/
theorem exists_subset_transitive (x : M) : ∃ t : M, x ⊆ t ∧ Transitive t := by
  have hR : ∀ n ∈ (ω : M), ∃! v, iterUnionVal x ![n, v] := by
    intro n hn
    obtain ⟨g, hg⟩ := exists_isIterUnion hn
    refine ⟨g ﹫ n, ?_, fun v hv ↦ ?_⟩
    · simp only [iterUnionVal_iff]
      exact ⟨g, hg, rfl⟩
    · simp only [iterUnionVal_iff] at hv
      obtain ⟨g', hg', rfl⟩ := hv
      exact hg'.val_eq_val hg hn hn (mem_succ_self _) (mem_succ_self _)
  have hmem {n : M} (hn : n ∈ (ω : M)) {g : M} (hg : IsIterUnion x g n) :
      g ﹫ n ∈ iterUnionVal x ''₀ ω := by
    refine mem_replacement_of_mem hR hn ?_
    simp only [iterUnionVal_iff]
    exact ⟨g, hg, rfl⟩
  refine ⟨⋃₀ (iterUnionVal x ''₀ ω), fun z hz ↦ ?_, fun y hy z hz ↦ ?_⟩
  · have h : IsIterUnion x {!(∅, x)} ∅ := isIterUnion_singleton x
    simp only [mem_sUnion_iff]
    exact ⟨_, hmem empty_mem_omega h, by rwa [h.val_empty]⟩
  · simp only [mem_sUnion_iff] at hy
    obtain ⟨v, hv, hyv⟩ := hy
    simp only [mem_replacement_iff hR v] at hv
    obtain ⟨n, hn, hnv⟩ := hv
    simp only [iterUnionVal_iff] at hnv
    obtain ⟨g, hg, rfl⟩ := hnv
    have hg' : IsIterUnion x (g ∪ {!(succ n, ⋃₀ (g ﹫ n))}) (succ n) :=
      hg.extend (ordinal_of_mem ordinal_omega hn)
    have hsn : succ n ∈ ω := succ_mem_omega hn
    simp only [mem_sUnion_iff]
    refine ⟨_, hmem hsn hg', ?_⟩
    rw [hg'.val_succ (mem_succ_self n), hg'.val_eq_val hg hsn hn (by simp) (mem_succ_self n)]
    grind

/-- `∈`-induction in models of `ZF` -/
theorem induction_of_modelsZF {A : Class M} [A.Definable Set.univ]
    (h : ∀ x, (∀ y ∈ x, A y) → A x) (x : M) : A x := by
  by_contra hx
  obtain ⟨t, hxt, ht⟩ := exists_subset_transitive ({x} : M)
  obtain ⟨y, hy, hy'⟩ := exists_min_class_of_mem_transitive (A := ∼A) (by simpa using hx)
    (hxt (mem_singleton x)) ht
  simp only [Class.not_iff, not_not] at hy hy'
  exact hy (h y hy')

/-- Models of `ZF` are models of `KP` -/
instance : ModelsKP M where
  modelsKP := by
    rw [KP, Theory.model_union_iff]
    refine ⟨ModelsKP₀.modelsKP₀, ?_⟩
    simp only [Theory.model_iff]
    rintro _ ⟨n, ψ, rfl⟩
    rw [realize_iff_realize']
    simp only [BoundedFormula.recursion, Function.comp_apply, realize'_alls, realize'_imp,
      realize'_all, BoundedFormula.realize_allMem, Term.realize'_var', snoc_last,
      realize'_substBoundBound, snoc_snoc_comp_snoc_castAdd_two_last]
    intro vs h
    let A : Class M := ψ.switchBound.multiclass.slice vs
    have hA (x : M) : A x ↔ ψ〘snoc vs x〙 := by
      simp [A, snoc_eq_append, Matrix.empty_eq]
    simp only [← hA] at h ⊢
    exact induction_of_modelsZF h

/-- Models of `ZF` are models of `KPInf` -/
instance : ModelsKPInf M where
  modelsKPInf := by
    simp only [KPInf, Theory.model_union_iff]
    refine ⟨ModelsKP.modelsKP, ?_⟩
    simp only [Theory.model_singleton_iff]
    exact ModelsZF.modelsZF.realize_of_mem _ (by simp [ZF])

section Recursion

variable {R : Multiclass M 2} {G : ClassFunction M} [R.predSet.Definable Set.univ]
  [G.Definable Set.univ]

/-- In models of `ZF`, the recursion from a definable `G` along `R` has approximations on every
set if `R.predSet` is definable and `R` is well-founded for definable classes -/
theorem hasWFApprox_of_modelsZF₀ (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike) :
    HasWFApprox G R := by
  let Ap : Class M := fun f ↦ IsWFApprox f G R
  -- `F ![y, f]`: `f` is an approximation defined at `y`
  let F : Multiclass M 2 := fun xs ↦ Ap (xs 1) ∧ xs 0 ∈ dom (xs 1)
  have hF (y f : M) : F ![y, f] ↔ IsWFApprox f G R ∧ y ∈ dom f := .rfl
  -- approximations defined at each point of `s` combine into one defined on `s`
  have hsub {s : M} (h : ∀ y ∈ s, ∃ f, IsWFApprox f G R ∧ y ∈ dom f) :
      ∃ f, IsWFApprox f G R ∧ s ⊆ dom f := by
    obtain ⟨B, hB⟩ := exists_collection_of_modelsZF F s (by simpa [hF] using h)
    simp only [hF] at hB
    refine ⟨⋃₀ (B ∩₀ Ap), isWFApprox_sUnion hR hS fun f hf ↦ ?_, fun y hy ↦ ?_⟩
    · simp only [mem_comprehension_iff] at hf
      exact hf.right
    · obtain ⟨f, hfB, hf, hyf⟩ := hB y hy
      have hfB' : f ∈ B ∩₀ Ap := by
        simp only [mem_comprehension_iff]
        exact ⟨hfB, hf⟩
      simp only [mem_dom_iff] at hyf ⊢
      obtain ⟨z, hz⟩ := hyf
      exact ⟨z, by simp only [mem_sUnion_iff]; exact ⟨f, hfB', hz⟩⟩
  have hFex (x : M) : (F.ex : Class M) x ↔ ∃ f, IsWFApprox f G R ∧ x ∈ dom f := by
    simp [hF]
  -- approximations defined at each point, by induction along `R`
  have hex (x : M) : ∃ f, IsWFApprox f G R ∧ x ∈ dom f := by
    rw [← hFex]
    refine hR.induction (fun x ih ↦ ?_) x
    simp only [hFex] at ih ⊢
    obtain ⟨h, hh, hxh⟩ := hsub fun y hy ↦ ih y (by rwa [hS.mem_predSet_iff] at hy)
    grind [hh.exists_extend hxh]
  exact fun s ↦ hsub fun y _ ↦ hex y

end Recursion

section SetWellFounded

variable {R a x y : M} (h : IsStrictWellFounded R a)
include h

/-- In models of `ZF`, a strict well-founded set relation is also well-founded for definable
classes -/
theorem IsStrictWellFounded.isStrictWellFounded₀ : IsStrictWellFounded₀ R a :=
  h.isStrictWellFounded₀_of_comprehension (hA := fun _ _ ↦ inferInstance)

theorem IsStrictWellFounded.isFunction_collapseOn : IsFunction (collapseOn R a) :=
  h.isStrictWellFounded₀.isFunction_collapseOn

theorem IsStrictWellFounded.dom_collapseOn : dom (collapseOn R a) = a :=
  h.isStrictWellFounded₀.dom_collapseOn

theorem IsStrictWellFounded.val_collapseOn (hx : x ∈ a) :
    collapseOn R a ﹫ x = collapse (Multiclass.ofRel R) x :=
  h.isStrictWellFounded₀.val_collapseOn hx

/-- In models of `ZF`, `collapseOn R a` is the transitive collapse of a strict well-founded set
relation `R` on `a` -/
theorem IsStrictWellFounded.isCollapseOn_collapseOn : IsCollapseOn R a (collapseOn R a) :=
  h.isStrictWellFounded₀.isWFRecursionOn_collapseOn

/-- In models of `ZF`, the collapse of `R` on `a` is the function defined by `R`-recursion on `a`
from `ran` -/
theorem IsStrictWellFounded.collapseOn_eq_wfRecursionOn : collapseOn R a = wfRecursionOn R a ran :=
  h.isStrictWellFounded₀.collapseOn_eq_wfRecursionOn

theorem IsStrictWellFounded.collapseOn_val_eq (hx : x ∈ a) :
    collapseOn R a ﹫ x = ran (collapseOn R a ↾ predSet R x) :=
  h.isStrictWellFounded₀.collapseOn_val_eq hx

/-- In models of `ZF`, the collapse of `R'` on `b ⊆ a` is the restriction of the collapse of `R`
on `a`, if `R'` and `R` have the same predecessors on `b` -/
theorem IsStrictWellFounded.collapseOn_eq_restrict {R' b : M} (h' : IsStrictWellFounded R' b)
    (hba : b ⊆ a) (hpred : ∀ x ∈ b, predSet R' x = predSet R x) :
    collapseOn R' b = collapseOn R a ↾ b :=
  h.isStrictWellFounded₀.collapseOn_eq_restrict h'.isStrictWellFounded₀ hba hpred

/-- In models of `ZF`, the collapse of `R` on `a` is injective if `R` is extensional on `a` -/
theorem IsStrictWellFounded.collapseOn_injOn (hE : IsExtensionalOn R a) (hx : x ∈ a)
    (hy : y ∈ a) : collapseOn R a ﹫ x = collapseOn R a ﹫ y ↔ x = y :=
  h.isStrictWellFounded₀.collapseOn_injOn hE hx hy

/-- In models of `ZF`, the collapse of `R` on `a` is an isomorphism from `R` onto `∈` if `R` is
extensional on `a` -/
theorem IsStrictWellFounded.rel_iff_collapseOn_mem_collapseOn (hE : IsExtensionalOn R a)
    (hx : x ∈ a) (hy : y ∈ a) : y [R] x ↔ collapseOn R a ﹫ y ∈ collapseOn R a ﹫ x :=
  h.isStrictWellFounded₀.rel_iff_collapseOn_mem_collapseOn hE hx hy

/-- In models of `ZF`, the range of the collapse of `R` on `a` is a transitive set -/
theorem IsStrictWellFounded.transitive_ran_collapseOn : Transitive (ran (collapseOn R a)) :=
  h.isStrictWellFounded₀.transitive_ran_collapseOn

end SetWellFounded

section SetWellOrder

variable {R a x y : M} (h : IsStrictWellOrder R a)
include h

/-- In models of `ZF`, a strict well-order on a set is also well-founded for definable classes -/
theorem IsStrictWellOrder.isStrictWellOrder₀ : IsStrictWellOrder₀ R a :=
  ⟨h, h.isStrictWellFounded.isStrictWellFounded₀.isStrictWellFounded₀_ofRel⟩

/-- In models of `ZF`, the range of the collapse of a strict well-order on a set is an ordinal:
the order type -/
theorem IsStrictWellOrder.ordinal_ran_collapseOn : Ordinal (ran (collapseOn R a)) :=
  h.isStrictWellOrder₀.ordinal_ran_collapseOn

/-- In models of `ZF`, the collapse of a strict well-order on a set maps it into ordinals -/
theorem IsStrictWellOrder.ordinal_collapseOn_val (hx : x ∈ a) :
    Ordinal (collapseOn R a ﹫ x) :=
  h.isStrictWellOrder₀.ordinal_collapseOn_val hx

/-- In models of `ZF`, the collapse of a strict well-order on `a` is an isomorphism from `R` onto
`∈` -/
theorem IsStrictWellOrder.rel_iff_collapseOn_mem_collapseOn (hx : x ∈ a) (hy : y ∈ a) :
    y [R] x ↔ collapseOn R a ﹫ y ∈ collapseOn R a ﹫ x :=
  h.isStrictWellOrder₀.rel_iff_collapseOn_mem_collapseOn hx hy

end SetWellOrder

section OrdRecursion

variable {z α : M} {s l : ClassFunction M}

noncomputable instance (a : M) : Decidable (a = ∅) := Classical.propDecidable _

noncomputable instance (a : M) : Decidable (SuccOrdinal a) := Classical.propDecidable _

/-- One step of the recursion on ordinals with value `z` at `∅`, successor step `s` and limit
step `l`, applied to `g = F ↾₀ α`: `z` if `α = ∅`, `s (g ﹫ β)` if `α = succ β`, and `l g`
otherwise -/
noncomputable def ordRecursionStep' (z : M) (s l : ClassFunction M) : ClassFunction M :=
  fun g ↦ if dom g = ∅ then z else if SuccOrdinal (dom g) then s (g ﹫ ⋃₀ dom g) else l g

instance [s.Definable Set.univ] [l.Definable Set.univ] :
    (ordRecursionStep' z s l).Definable Set.univ := by
  -- `[g, v, z, u, w, t]`: `w = g ﹫ ⋃₀ dom g`, `u = s w`, `t = l g`, and `v` is given by the
  -- three cases
  let ψ : Multiclass M 6 := ((&0 =₀ &1).substBoundRud ![ᵣ4, (ᵣ0) ﹫ (ᵣ⋃₀ (ᵣ0).dom)] :
    L.DeltaZeroBoundedFormula 6).toBoundedFormula.multiclass
  have hψ (xs : Fin 6 → M) : ψ xs ↔ xs 4 = xs 0 ﹫ ⋃₀ dom (xs 0) := by
    simp only [ψ, BoundedFormula.multiclass, DeltaZeroBoundedFormula.realize_substBoundRud]
    simp
  let A : Multiclass M 6 := (((&0 =₀ &1).substBoundRud ![(ᵣ0).dom, ∅] ⊓
      (&0 =₀ &1).substBoundRud ![ᵣ1, ᵣ2]) ⊔
    (∼((&0 =₀ &1).substBoundRud ![(ᵣ0).dom, ∅]) ⊓ (ᵣ0).dom.isSuccOrdinal ⊓
      (&0 =₀ &1).substBoundRud ![ᵣ1, ᵣ3]) ⊔
    (∼((&0 =₀ &1).substBoundRud ![(ᵣ0).dom, ∅]) ⊓ ∼(ᵣ0).dom.isSuccOrdinal ⊓
      (&0 =₀ &1).substBoundRud ![ᵣ1, ᵣ5]) :
      L.DeltaZeroBoundedFormula 6).toBoundedFormula.multiclass ⊓ ψ ⊓
    (s : Multiclass M 2).remap ![4, 3] ⊓ (l : Multiclass M 2).remap ![0, 5]
  refine ClassFunction.Definable.of_iff (F := A.ex.ex.ex.slice ![z]) fun g v ↦ ?_
  suffices ((dom g = ∅ ∧ v = z) ∨ (dom g ≠ ∅ ∧ SuccOrdinal (dom g) ∧ v = s (g ﹫ ⋃₀ dom g)) ∨
      (dom g ≠ ∅ ∧ ¬SuccOrdinal (dom g) ∧ v = l g)) ↔ ordRecursionStep' z s l g = v by
    simpa [A, hψ, Multiclass.ex_iff, Multiclass.slice, Multiclass.remap, Matrix.comp_vecCons,
      Matrix.empty_eq, ClassFunction.toMulticlass_vec_iff,
      DeltaZeroBoundedFormula.realize_substBoundRud, realize_isSuccOrdinal, snoc_nat, and_assoc,
      or_assoc] using this
  unfold ordRecursionStep'
  grind

/-- Recursion on ordinals: `F α = G (F ↾₀ α)` -/
noncomputable def ordRecursion (G : ClassFunction M) : ClassFunction M := wfRecursion G MemRel

/-- Recursion on ordinals with value `z` at `∅`, successor step `s` and limit step `l`:
`F ∅ = z`, `F (succ α) = s (F α)` and `F α = l (F ↾₀ α)` for limits `α` -/
noncomputable def ordRecursion' (z : M) (s l : ClassFunction M) : ClassFunction M :=
  ordRecursion (ordRecursionStep' z s l)

section

variable {G : ClassFunction M} [G.Definable Set.univ]

instance : (ordRecursion G).Definable Set.univ :=
  (hasWFApprox_of_modelsZF₀ (G := G) isStrictWellFounded₀_memRel
    isSetLike_memRel).definable_wfRecursion isStrictWellFounded₀_memRel isSetLike_memRel

/-- The recursive definition `ordRecursion G x = G (ordRecursion G ↾₀ x)` -/
theorem ordRecursion_eq (x : M) : ordRecursion G x = G (ordRecursion G ↾₀ x) := by
  have h := (hasWFApprox_of_modelsZF₀ (G := G) isStrictWellFounded₀_memRel
    isSetLike_memRel).wfRecursion_eq isStrictWellFounded₀_memRel isSetLike_memRel x
  rwa [predSet_memRel_apply] at h

/-- Induction along `ordRecursion G`: a definable property holds for every value if it holds for
`G g` whenever it holds for the values of `g` -/
theorem ordRecursion_induction {A : Class M} [A.Definable Set.univ]
    (h : ∀ x, (∀ y ∈ x, A (ordRecursion G y)) → A (G (ordRecursion G ↾₀ x))) (x : M) :
    A (ordRecursion G x) := by
  refine induction_of_modelsZF (A := fun x ↦ A (ordRecursion G x)) (fun x ih ↦ ?_) x
  rw [ordRecursion_eq]
  exact h x ih

end

variable [s.Definable Set.univ] [l.Definable Set.univ]

instance : (ordRecursion' z s l).Definable Set.univ := by
  unfold ordRecursion'
  infer_instance

/-- The recursive definition of `ordRecursion' z s l` -/
theorem ordRecursion'_eq (x : M) :
    ordRecursion' z s l x = ordRecursionStep' z s l (ordRecursion' z s l ↾₀ x) :=
  ordRecursion_eq x

@[simp]
theorem ordRecursion'_empty : ordRecursion' z s l ∅ = z := by
  rw [ordRecursion'_eq]
  unfold ordRecursionStep'
  rw [dom_toSetRestrictedTo (isSetRestrictedTo_of_definable _), if_pos rfl]

theorem ordRecursion'_succ (hα : Ordinal α) :
    ordRecursion' z s l (succ α) = s (ordRecursion' z s l α) := by
  have hres := isSetRestrictedTo_of_definable (G := ordRecursion' z s l) (succ α)
  rw [ordRecursion'_eq]
  unfold ordRecursionStep'
  rw [dom_toSetRestrictedTo hres, if_neg (succ_ne_empty α), if_pos ⟨ordinal_succ hα, α, rfl⟩,
    sUnion_succ hα.transitive, val_toSetRestrictedTo hres (mem_succ_self α)]

theorem NonZeroLimOrdinal.ordRecursion'_eq (hα : NonZeroLimOrdinal α) :
    ordRecursion' z s l α = l (ordRecursion' z s l ↾₀ α) := by
  rw [MemStructure.ordRecursion'_eq]
  unfold ordRecursionStep'
  rw [dom_toSetRestrictedTo (isSetRestrictedTo_of_definable _), if_neg hα.ne_empty,
    if_neg hα.left.right]

/-- Induction along `ordRecursion' z s l`: a definable property holds for every value if it holds
for `z`, is preserved by the successor step `s`, and holds for `l g` whenever it holds for the
values of `g` -/
theorem ordRecursion'_induction {A : Class M} [A.Definable Set.univ] (h0 : A z)
    (hs : ∀ β, Ordinal β → A (ordRecursion' z s l β) → A (s (ordRecursion' z s l β)))
    (hl : ∀ x, (∀ y ∈ x, A (ordRecursion' z s l y)) → A (l (ordRecursion' z s l ↾₀ x)))
    (x : M) : A (ordRecursion' z s l x) := by
  refine induction_of_modelsZF (A := fun x ↦ A (ordRecursion' z s l x)) (fun x ih ↦ ?_) x
  have hres := isSetRestrictedTo_of_definable (G := ordRecursion' z s l) x
  rw [ordRecursion'_eq]
  unfold ordRecursionStep'
  rw [dom_toSetRestrictedTo hres]
  split_ifs with h₀ hsucc
  · exact h0
  · obtain ⟨hxo, β, rfl⟩ := hsucc
    have hβ := ordinal_of_mem hxo (mem_succ_self β)
    rw [sUnion_succ hβ.transitive, val_toSetRestrictedTo hres (mem_succ_self β)]
    exact hs β hβ (ih β (mem_succ_self β))
  · exact hl x ih

end OrdRecursion

section PredClosure

variable {R : Multiclass M 2} [R.predSet.Definable Set.univ] {x y z t : M}

/-- One step of closing a set under `R`-predecessors: `t ↦ t ∪ ⋃₀ {R.predSet y | y ∈ t}` -/
noncomputable def predClosureStep (R : Multiclass M 2) : ClassFunction M :=
  fun t ↦ t ∪ ⋃₀ ran (R.predSet ↾₀ t)

instance : (predClosureStep R).Definable Set.univ := by
  -- `v = t ∪ ⋃₀ w` for the set `w` of the `R.predSet y` with `y ∈ t`
  refine ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ w,
    (∀ q ∈ w, ∃ y ∈ xs 0, R.predSet y = q) ∧ (∀ y ∈ xs 0, ∃ q ∈ w, R.predSet y = q) ∧
      xs 1 = xs 0 ∪ ⋃₀ w) fun t v ↦ ?_
  have hres := isSetRestrictedTo_of_definable (G := R.predSet) t
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, predClosureStep]
  refine ⟨fun ⟨w, hw₁, hw₂, hv⟩ ↦ ?_, fun hv ↦ ⟨_, fun q hq ↦ ?_, fun y hy ↦ ?_, hv.symm⟩⟩
  · rw [hv]
    congr 2
    ext q
    rw [mem_ran_toSetRestrictedTo_iff hres]
    refine ⟨fun ⟨y, hy, hyq⟩ ↦ ?_, hw₁ q⟩
    obtain ⟨q', hq', hyq'⟩ := hw₂ y hy
    rwa [← hyq, hyq']
  · exact (mem_ran_toSetRestrictedTo_iff hres).mp hq
  · exact ⟨_, (mem_ran_toSetRestrictedTo_iff hres).mpr ⟨y, hy, rfl⟩, rfl⟩

theorem mem_predClosureStep_iff (hS : R.IsSetLike) :
    z ∈ predClosureStep R t ↔ z ∈ t ∨ ∃ y ∈ t, R ![z, y] := by
  have hres := isSetRestrictedTo_of_definable (G := R.predSet) t
  simp only [predClosureStep, mem_union_iff, mem_sUnion_iff, mem_ran_toSetRestrictedTo_iff hres]
  grind [hS.mem_predSet_iff]

/-- The closure of `{x}` under `R`-predecessors, built in `ω` steps -/
noncomputable def predClosure (R : Multiclass M 2) (x : M) : M :=
  ordRecursion' {x} (predClosureStep R) (fun g ↦ ⋃₀ ran g) ω

theorem mem_predClosure_iff :
    z ∈ predClosure R x ↔
      ∃ n ∈ (ω : M), z ∈ ordRecursion' {x} (predClosureStep R) (fun g ↦ ⋃₀ ran g) n := by
  have hres := isSetRestrictedTo_of_definable
    (G := ordRecursion' {x} (predClosureStep R) (fun g ↦ ⋃₀ ran g)) ω
  rw [predClosure, nonZeroLimOrdinal_omega.ordRecursion'_eq, mem_sUnion_iff]
  simp only [mem_ran_toSetRestrictedTo_iff hres]
  grind

theorem mem_predClosure_self : x ∈ predClosure R x :=
  mem_predClosure_iff.mpr ⟨∅, empty_mem_omega, by simp⟩

/-- `predClosure R x` is closed under `R`-predecessors -/
theorem mem_predClosure_of_rel (hS : R.IsSetLike) (hy : y ∈ predClosure R x) (hzy : R ![z, y]) :
    z ∈ predClosure R x := by
  obtain ⟨n, hn, hyn⟩ := mem_predClosure_iff.mp hy
  refine mem_predClosure_iff.mpr ⟨succ n, succ_mem_omega hn, ?_⟩
  rw [ordRecursion'_succ (ordinal_of_mem ordinal_omega hn), mem_predClosureStep_iff hS]
  exact .inr ⟨y, hyn, hzy⟩

/-- In models of `ZF`, a set-like class relation that is well-founded for sets is well-founded for
definable classes -/
theorem Multiclass.IsStrictWellFounded.isStrictWellFounded₀ (hR : R.IsStrictWellFounded)
    (hS : R.IsSetLike) : R.IsStrictWellFounded₀ := by
  intro A _ ⟨x, hx⟩
  -- an `R`-minimal element of `predClosure R x ∩₀ A`
  obtain ⟨m, hm, hmin⟩ := hR (predClosure R x ∩₀ A)
    ⟨x, by rw [mem_comprehension_iff]; exact ⟨mem_predClosure_self, hx⟩⟩
  rw [mem_comprehension_iff] at hm
  refine ⟨m, hm.right, fun y hy hAy ↦ hmin y hy ?_⟩
  rw [mem_comprehension_iff]
  exact ⟨mem_predClosure_of_rel hS hm.left hy, hAy⟩

/-- In models of `ZF`, the recursion from a definable `G` along `R` has approximations on every
set if `R.predSet` is definable -/
theorem hasWFApprox_of_modelsZF {G : ClassFunction M} [G.Definable Set.univ]
    (hR : R.IsStrictWellFounded) (hS : R.IsSetLike) : HasWFApprox G R :=
  hasWFApprox_of_modelsZF₀ (hR.isStrictWellFounded₀ hS) hS

end PredClosure

end MemStructure

end FirstOrder.Language
