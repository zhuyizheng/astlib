/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Relation
/-!
# Functions

Functions as sets of ordered pairs, in models of rudimentary set theory:

* `IsFunction f`: `f` is a relation with at most one value at each point, and `f ﹫ x` is the
  value of `f` at `x`;
* `f !∘ g`: composition of functions;
* `id a`: the identity function on `a`.
-/

open Fin FirstOrder Language MemStructure RudimentaryTerm DeltaZeroBoundedFormula

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M]

section Basic

open RudimentaryTerm Fin

variable [Extensional M] [RudClosed M]

def IsFunction : Class M := fun f ↦
  IsRelation f ∧ ∀ ⦃x y₁ y₂ : M⦄, x [f] y₁ → x [f] y₂ → y₁ = y₂

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.isFunction
  {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r : L.RudimentaryTerm n) :
  L.DeltaZeroBoundedFormula n :=
  ((ᵣ0).isRelation ⊓ ∀₀∈ &0 ∀₀∈ &0
    ((ᵣ1).left.isEq (ᵣ2).left ⟹
    (ᵣ1).right.isEq (ᵣ2).right)) |>.substBoundRud ![r]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r : L.RudimentaryTerm n)
  [r.CharFree] : r.isFunction.RelFree := by
  unfold isFunction; infer_instance

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isFunction
    [L.ExtraConstantsUnaryRelationsOnly]
    (r : L.RudimentaryTerm n) [r.CharFree] (xs : Fin n → M) :
    r.isFunction.toBoundedFormula 〘xs〙 ↔ IsFunction (r〘xs〙 : M) := by
  simp only [isFunction, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    IsFunction]
  rw [DeltaZeroBoundedFormula.realize_substBoundRud]
  suffices IsRelation (r〘xs〙 : M) →
      ((∀ a ∈ r〘xs〙, ∀ a_2 ∈ r〘xs〙, left a = left a_2 → right a = right a_2) ↔
      ∀ ⦃x y₁ y₂ : M⦄, !(x, y₁) ∈ r〘xs〙 → !(x, y₂) ∈ r〘xs〙 → y₁ = y₂) by
    simpa [isFunction, IsFunction, snoc_nat]
  intro hr
  constructor
  · intro h x y₁ y₂ hxy₁ hxy₂
    convert h !(x, y₁) hxy₁ !(x, y₂) hxy₂ (by simp) <;> simp
  · intro h z₁ hz₁ z₂ hz₂ hz₁₂
    obtain ⟨x, y₁, rfl⟩ := hr hz₁
    obtain ⟨x', y₂, rfl⟩ := hr hz₂
    simp only [left_orderedPair] at hz₁₂
    subst hz₁₂
    convert h hz₁ hz₂ <;> simp

@[simp, grind .]
theorem IsFunction.isRelation {f : M} (hf : IsFunction f) : IsRelation f := hf.left

@[grind .]
theorem IsFunction.eq
    {f x y₁ y₂: M} (hf : IsFunction f) (h₁ : x [f] y₁) (h₂ : x [f] y₂) : y₁ = y₂ := by
  grind [IsFunction]

-- variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

@[simp, grind .]
theorem isFunction_empty : IsFunction (∅ : M) := by
  simp [IsFunction]

@[simp, grind .]
theorem IsFunction.subset {f g : M} (hf : IsFunction f) (hgf : g ⊆ f) :
    IsFunction g := by
  simp only [IsFunction, hf.isRelation.subset, hgf, true_and]
  exact fun x y₁ y₂ h₁ h₂ ↦ hf.eq (hgf h₁) (hgf h₂)

theorem IsFunction.inter_right
    {f : M} (hf : IsFunction f) (g : M) : IsFunction (f ∩ g) := by
  grind

theorem IsFunction.inter_left
    (f : M) {g : M} (hg : IsFunction g) : IsFunction (f ∩ g) := by
  grind

theorem IsFunction.sdiff
    {f : M} (hf : IsFunction f) (g : M) : IsFunction (f \ g) := by
  grind

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.val₀
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 2 :=
  (ᵣ0).iUnion ((ᵣ2).right.ifTrue
    ((ᵣ2).isOrderedPair ⊓ (ᵣ2).left.isEq (ᵣ1)))

@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.val
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  val₀.substBoundRud ![r, s]

infix:88 " ﹫ " => FirstOrder.Language.RudimentaryTerm.val

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
  (val₀ : L.RudimentaryTerm 2).CharFree := by
  unfold val₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] : (r ﹫ s).CharFree := by
  unfold RudimentaryTerm.val; infer_instance

variable [L.ExtraConstantsUnaryRelationsOnly]

noncomputable def val (f a : M) := RudimentaryTerm.val₀ 〘f, a〙₂

infix:88 " ﹫ " => FirstOrder.Language.MemStructure.val

omit [RudClosed M] in
@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_val₀ (xs : Fin 2 → M) :
    RudimentaryTerm.val₀〘xs〙 = (xs 0 ﹫ xs 1 : M) := by
  simp only [val]
  rw [Matrix.vec_fin_two_eq]

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ ys 0 ﹫ ys 1) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ RudimentaryTerm.val₀ fun _ _ ↦ rfl

-- @[simp]
theorem IsFunction.rel_iff_val_eq
    {f x y : M} (hf : IsFunction f) (hx : x ∈ dom f) : x [f] y ↔ f ﹫ x = y := by
  simp only [mem_dom_iff] at hx
  obtain ⟨y₀, hy₀⟩ := hx
  suffices f ﹫ x = y₀ by grind
  simp only [val, RudimentaryTerm.val₀]
  ext z
  simp only [isValue, mem_realize_iUnion_iff, realize_basic, Matrix.cons_val_zero, Nat.reduceAdd,
    mem_realize_ifTrue_iff, RudimentaryTerm.right, RudimentaryTerm.left,
    RudimentaryTerm.realize_substBoundRud, realize_right₀, realize_left₀,
    Function.comp_apply, snoc_nat, coe_ofNat_eq_mod, Nat.mod_succ,
    lt_self_iff_false, ↓reduceDIte, toBoundedFormula_inf, BoundedFormula.realize'_inf,
    realize_isOrderedPair, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    DeltaZeroBoundedFormula.realize_substBoundRud, toBoundedFormula,
    BoundedFormula.realize'_bdEqual, Term.realize'_var', Nat.one_mod,
    Order.lt_two_iff, Std.le_refl, mk_one, RudimentaryTerm.realize_isEq]
  constructor
  · rintro ⟨w, hw₁, hw₂, ⟨x', y', rfl⟩, hw₃⟩
    simp only [right_orderedPair, left_orderedPair] at hw₂ hw₃
    convert hw₂
    grind
  · intro hz
    exact ⟨!(x, y₀), hy₀, by simp [hz], by simp [IsOrderedPair], by simp⟩

@[simp, grind! .]
theorem IsFunction.val_eq_of_rel
    {f x y : M} (hf : IsFunction f) (hxy : x [f] y) : f ﹫ x = y := by
  rwa [hf.rel_iff_val_eq] at hxy
  simp only [mem_dom_iff]
  use y

theorem IsFunction.exists_val
    {f : M} (hf : IsFunction f)
    {z : M} (hz : z ∈ f) : ∃ x, z = !(x, f ﹫ x) := by
  obtain ⟨x, y, hxy⟩ := hf.isRelation hz
  use x
  convert hxy
  exact val_eq_of_rel hf (by grind)

-- @[simp]
theorem rel_val
    {f x : M} (hf : IsFunction f) (hx : x ∈ dom f) : x [f] (f ﹫ x) := by
  grind

/-- `f ﹫ x` is empty unless `x ∈ dom f` -/
theorem mem_dom_of_mem_val {f x y : M} (h : y ∈ f ﹫ x) : x ∈ dom f := by
  simp only [val, val₀, isValue, Nat.reduceAdd, RudimentaryTerm.right, Nat.succ_eq_add_one,
    Function.comp_apply, RudimentaryTerm.left, mem_realize_iUnion_iff, realize_basic,
    Matrix.cons_val_zero, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty, mem_realize_ifTrue_iff,
    RudimentaryTerm.realize_substBoundRud, Matrix.cons_val_fin_one, Matrix.cons_val,
    realize_right₀, toBoundedFormula_inf, BoundedFormula.realize'_inf, realize_isOrderedPair,
    DeltaZeroBoundedFormula.realize_substBoundRud, toBoundedFormula,
    BoundedFormula.realize'_bdEqual, Term.realize'_var', realize_left₀, Matrix.cons_val_one,
    RudimentaryTerm.realize_isEq] at h
  obtain ⟨w, hw, -, ⟨u, v, rfl⟩, rfl⟩ := h
  rw [mem_dom_iff]
  exact ⟨v, by simpa using hw⟩

lemma IsFunction.subset_iff {f g : M} (hf : IsFunction f) :
    f ⊆ g ↔ ∀ x ∈ dom f, (x [g] (f ﹫ x)) := by
  refine ⟨by grind, fun h z hz ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := hf.exists_val hz
  exact h x (by grind)

@[grind .]
theorem IsFunction.ext {f g : M} (hf : IsFunction f) (hg : IsFunction g)
    (hfg : dom f = dom g)
    (h : ∀ x ∈ dom f, f ﹫ x = g ﹫ x) : f = g := by
  refine eq_of_subset_of_subset ?_ ?_
  · simp only [hf.subset_iff]
    grind
  · simp only [hg.subset_iff]
    grind

@[grind .]
theorem IsFunction.eq_iff {f g : M} (hf : IsFunction f) (hg : IsFunction g) :
    f = g ↔ dom f = dom g ∧ ∀ x ∈ dom f, f ﹫ x = g ﹫ x := by
  grind

/-- Outside the domain, the value is `∅` -/
theorem val_eq_empty_of_not_mem_dom {f x : M} (hx : x ∉ dom f) : f ﹫ x = ∅ := by
  ext z
  simp only [val, RudimentaryTerm.val₀, Fin.isValue, Nat.reduceAdd, RudimentaryTerm.right,
    RudimentaryTerm.left, RudimentaryTerm.mem_realize_iUnion_iff, RudimentaryTerm.realize_basic,
    Matrix.cons_val_zero, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty,
    RudimentaryTerm.mem_realize_ifTrue_iff, RudimentaryTerm.realize_substBoundRud,
    Matrix.cons_val_fin_one, Matrix.cons_val, RudimentaryTerm.realize_right₀,
    DeltaZeroBoundedFormula.toBoundedFormula_inf, BoundedFormula.realize'_inf,
    RudimentaryTerm.realize_isOrderedPair, RudimentaryTerm.realize_isEq,
    RudimentaryTerm.realize_left₀, Matrix.cons_val_one, notin_empty, iff_false, not_exists,
    not_and]
  rintro w hw - ⟨a, b, rfl⟩ rfl
  rw [mem_dom_iff, left_orderedPair] at hx
  exact hx ⟨b, hw⟩

@[grind =]
theorem IsFunction.mem_dom_iff {f : M} (x : M) (hf : IsFunction f) :
    x ∈ dom f ↔ x [f] (f ﹫ x) := by
  grind

@[grind =]
theorem IsFunction.mem_ran_iff {f : M} (y : M) (hf : IsFunction f) :
    y ∈ ran f ↔ ∃ x ∈ dom f, f ﹫ x = y := by
  simp only [MemStructure.mem_ran_iff]
  exact exists_congr (by grind)

theorem IsFunction.subset_dom_sprod_ran {f : M} (hf : IsFunction f) :
    f ⊆ dom f ×ˢ ran f :=
  hf.isRelation.subset_dom_sprod_ran

def FunctionAgree (f g : M) := ∀ ⦃x⦄, x ∈ dom f ∩ dom g → f ﹫ x = g ﹫ x

@[simp, grind .]
theorem IsFunction.union {f g : M}
    (hf : IsFunction f) (hg : IsFunction g)
    (hfg : FunctionAgree f g) : IsFunction (f ∪ g) := by
  refine ⟨hf.isRelation.union hg.isRelation, fun x y₁ y₂ h₁ h₂ ↦ ?_⟩
  simp only [mem_union_iff] at h₁ h₂
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · grind
    · grind [hfg (x := x) (by grind)]
  · rcases h₂ with h₂ | h₂
    · grind [hfg (x := x) (by grind)]
    · grind

/-- The union of two functions with disjoint domains is a function -/
theorem IsFunction.union_of_disjoint {f g : M} (hf : IsFunction f) (hg : IsFunction g)
    (h : ∀ z ∈ dom f, z ∉ dom g) : IsFunction (f ∪ g) :=
  hf.union hg fun z hz ↦ by
    simp only [mem_inter_iff] at hz
    grind

theorem val_union_left {f g z : M} (hf : IsFunction f) (hg : IsFunction g)
    (h : ∀ z ∈ dom f, z ∉ dom g) (hz : z ∈ dom f) : (f ∪ g) ﹫ z = f ﹫ z :=
  (hf.union_of_disjoint hg h).val_eq_of_rel (by simp [mem_union_iff, rel_val hf hz])

theorem val_union_right {f g z : M} (hf : IsFunction f) (hg : IsFunction g)
    (h : ∀ z ∈ dom f, z ∉ dom g) (hz : z ∈ dom g) : (f ∪ g) ﹫ z = g ﹫ z :=
  (hf.union_of_disjoint hg h).val_eq_of_rel (by simp [mem_union_iff, rel_val hg hz])

@[simp, grind .]
theorem IsFunction.sUnion {X : M}
    (hX₁ : ∀ f ∈ X, IsFunction f)
    (hX₂ : ∀ f ∈ X, ∀ g ∈ X, FunctionAgree f g) : IsFunction (⋃₀ X) := by
  refine ⟨IsRelation.sUnion (fun f hf ↦ (hX₁ f hf).isRelation), fun x y₁ y₂ h₁ h₂ ↦ ?_⟩
  simp only [mem_sUnion_iff] at h₁ h₂
  obtain ⟨f, hf₁, hf₂⟩ := h₁
  obtain ⟨g, hg₁, hg₂⟩ := h₂
  grind [(hX₁ f hf₁).union (hX₁ g hg₁) (by grind)]

end Basic

section Comp

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

theorem IsFunction.comp
    {f g : M} (hf : IsFunction f) (hg : IsFunction g) : IsFunction (f !∘ g) := by
  grind [IsFunction]
  -- simp only [IsFunction, isRelation_comp, true_and] at hf hg ⊢
  -- intro x y₁ y₂ hxy₁ hxy₂
  -- rw [rel_comp] at hxy₁ hxy₂

@[simp, grind .]
theorem mem_dom_comp_iff
    {f g x : M} (hf : IsFunction f) (hg : IsFunction g) :
    x ∈ dom (f !∘ g) ↔ x ∈ dom g ∧ g ﹫ x ∈ dom f := by
  simp only [hg.mem_dom_iff, hf.mem_dom_iff, mem_dom_iff]
  grind

@[simp, grind .]
theorem dom_comp
    {f g : M} (hf : IsFunction f)
    (h : ran g ⊆ dom f) :
    dom (f !∘ g) = dom g := by
  ext x
  refine ⟨by grind, ?_⟩
  simp only [mem_dom_iff, rel_comp]
  intro ⟨y, hy⟩
  grind [show y ∈ ran g by grind]

@[simp, grind .]
theorem ran_comp
    {f g : M} (hf : IsFunction f) (hg : IsFunction g)
    (h : dom f ⊆ ran g) :
    ran (f !∘ g) = ran f := by
  ext y
  refine ⟨by grind, ?_⟩
  simp only [mem_ran_iff, rel_comp]
  intro ⟨x, hx⟩
  grind [show x ∈ dom f by grind]

@[simp, grind =]
theorem comp_val
    {f g x : M} (hf : IsFunction f) (hg : IsFunction g)
    (hx : x ∈ dom (f !∘ g)) :
    (f !∘ g) ﹫ x = f ﹫ (g ﹫ x) := by
  apply hf.comp hg |>.val_eq_of_rel
  grind

end Comp

section Id

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

@[simp, grind .]
theorem isFunction_id
    (a : M) : IsFunction (id a) := by
  grind [IsFunction, id]

@[simp, grind =]
theorem id_val (a : M) {x : M} (hx : x ∈ a) : id a ﹫ x = x :=
  (isFunction_id _).val_eq_of_rel (by grind)

@[simp, grind =]
theorem IsFunction.comp_id
    {f a : M} (hf : IsFunction f) (h : dom f ⊆ a) :
    f !∘ (id a) = f := by
  grind [IsFunction]

@[simp, grind =]
theorem IsFunction.id_comp
    {f a : M} (hf : IsFunction f) (h : ran f ⊆ a) :
    (id a) !∘ f = f := by
  grind [IsFunction]

end Id

end FirstOrder.Language.MemStructure
