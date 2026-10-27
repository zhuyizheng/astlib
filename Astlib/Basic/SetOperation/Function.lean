/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Relation
/-!
file docstring
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
    ((&0 =₀ &1).substBoundRud ![(ᵣ1).left, (ᵣ2).left] ⟹
    (&0 =₀ &1).substBoundRud ![(ᵣ1).right, (ᵣ2).right])) |>.substBoundRud ![r]

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
    ((ᵣ2).isOrderedPair ⊓ (&0 =₀ &1).substBoundRud ![(ᵣ2).left, ᵣ1]))

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
    Order.lt_two_iff, Std.le_refl, mk_one]
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

section IsFunctionFromTo

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

def IsFunctionFromTo (f a b : M) := IsFunction f ∧ dom f = a ∧ ran f ⊆ b

notation:50 f " !: " a:50 " → " b:50 => IsFunctionFromTo f a b

/-- The `Δ₀` formula `r !: s → t` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.isFunctionFromTo
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r s t : L.RudimentaryTerm n) :
    L.DeltaZeroBoundedFormula n :=
  r.isFunction ⊓ (&0 =₀ &1).substBoundRud ![r.dom, s] ⊓ (&0 ⊆₀ &1).substBoundRud ![r.ran, t]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] :
    (r.isFunctionFromTo s t).RelFree := by
  unfold RudimentaryTerm.isFunctionFromTo; infer_instance

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isFunctionFromTo
    (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] (xs : Fin n → M) :
    (r.isFunctionFromTo s t).toBoundedFormula 〘xs〙 ↔ (r〘xs〙 : M) !: s〘xs〙 → t〘xs〙 := by
  simp [RudimentaryTerm.isFunctionFromTo, IsFunctionFromTo, and_assoc]


@[simp, grind .]
theorem IsFunctionFromTo.isFunction {f a b : M} (hf : f !: a → b) :
    IsFunction f :=
  hf.left

@[simp, grind .]
theorem IsFunctionFromTo.dom_eq {f a b : M} (hf : f !: a → b) :
    dom f = a :=
  hf.right.left

@[simp, grind .]
theorem IsFunctionFromTo.ran_subset {f a b : M} (hf : f !: a → b) :
    ran f ⊆ b:=
  hf.right.right

@[simp, grind .]
theorem isFunctionFromTo_dom_ran {f : M} (hf : IsFunction f) :
    f !: dom f → ran f:= by
  grind [IsFunctionFromTo]

@[simp, grind .]
theorem IsFunctionFromTo.mono {f b b' : M} (hf : f !: a → b) (hbb' : b ⊆ b') :
    f !: a → b' := by
  grind [IsFunctionFromTo]

@[simp, grind .]
theorem isFunctionFromTo_empty (b : M) :
    (∅ : M) !: ∅ → b := by
  grind [IsFunctionFromTo]

@[simp, grind .]
theorem isFunctionFromTo_id (a : M) :
    id a !: a → a := by
  grind [IsFunctionFromTo]

@[simp, grind .]
theorem IsFunctionFromTo.comp
    {f g a b c : M} (hf : f !: a → b) (hg : g !: b → c) :
    g !∘ f !: a → c := by
  grind [IsFunctionFromTo, ran_comp_subset, IsFunction.comp]

@[grind .]
theorem IsFunctionFromTo.val_mem {f a b x : M} (hf : f !: a → b) (hx : x ∈ a) : f ﹫ x ∈ b := by
  apply hf.ran_subset
  simp only [hf.isFunction.mem_ran_iff]
  exact ⟨x, hf.dom_eq ▸ hx, rfl⟩

/-- A function into `∅` has empty domain -/
@[grind .]
theorem IsFunctionFromTo.eq_empty {f a : M} (hf : f !: a → ∅) : a = ∅ := by
  simpa [empty_iff] using fun _ ↦ hf.val_mem

theorem IsFunctionFromTo.rel_iff {f a b x y : M} (hf : f !: a → b) :
    x [f] y ↔ x ∈ a ∧ f ﹫ x = y := by
  rw [← hf.dom_eq]
  grind [hf.isFunction.rel_iff_val_eq]

/-- A function from `a` to `b` is a subset of `a ×ˢ b` -/
theorem IsFunctionFromTo.subset_sprod {f a b : M} (hf : f !: a → b) : f ⊆ a ×ˢ b := by
  intro z hz
  obtain ⟨x, rfl⟩ := hf.isFunction.exists_val hz
  have hx : x ∈ dom f := by
    simp only [mem_dom_iff]
    exact ⟨_, hz⟩
  have hy : f ﹫ x ∈ ran f := by
    simp only [hf.isFunction.mem_ran_iff]
    exact ⟨x, hx, rfl⟩
  exact mem_sprod _ _ _ _ (hf.dom_eq ▸ hx) (hf.ran_subset hy)

/-- A function from `∅` is `∅` -/
theorem IsFunctionFromTo.eq_empty_of_dom_empty {f b : M} (hf : f !: ∅ → b) : f = ∅ := by
  have := hf.subset_sprod
  rw [empty_sprod] at this
  exact (empty_iff f).mpr fun z hz ↦ by simpa using this hz

/-- A function on `a` with values in `b` is a function from `a` to `b` -/
theorem isFunctionFromTo_of_val {g a b : M} (hg : IsFunction g) (hdom : dom g = a)
    (hval : ∀ z ∈ a, g ﹫ z ∈ b) : g !: a → b := by
  refine ⟨hg, hdom, fun w hw ↦ ?_⟩
  simp only [hg.mem_ran_iff, hdom] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  exact hval z hz

end IsFunctionFromTo

section ConstFun

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

/-- The constant function on `a` with value `c` -/
noncomputable def constFun (a c : M) : M := a ×ˢ ({c} : M)

omit [L.ExtraConstantsUnaryRelationsOnly] in
@[simp, grind =]
theorem rel_constFun_iff {a c z w : M} : z [constFun a c] w ↔ z ∈ a ∧ w = c := by
  simp [constFun]

omit [L.ExtraConstantsUnaryRelationsOnly] in
@[simp, grind .]
theorem isFunction_constFun (a c : M) : IsFunction (constFun a c) :=
  ⟨isRelation_sprod _ _, by grind⟩

@[simp, grind =]
theorem dom_constFun (a c : M) : dom (constFun a c) = a := by
  ext z
  simp [mem_dom_iff]

theorem ran_constFun_subset (a c : M) : ran (constFun a c) ⊆ ({c} : M) := by
  intro w hw
  simp only [mem_ran_iff, rel_constFun_iff] at hw
  grind

@[simp, grind =]
theorem val_constFun {a c z : M} (hz : z ∈ a) : constFun a c ﹫ z = c :=
  (isFunction_constFun a c).val_eq_of_rel (by simp [hz])

end ConstFun

section IsInjectionFromTo

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

def IsInjectionFromTo (f a b : M) :=
    f !: a → b ∧ ∀ ⦃x y⦄, x ∈ a → y ∈ a → f ﹫ x = f ﹫ y → x = y

notation:50 f " !: " a:50 " ↪ " b:50 => IsInjectionFromTo f a b

/-- The `Δ₀` formula `r !: s ↪ t` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.isInjectionFromTo
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r s t : L.RudimentaryTerm n) :
    L.DeltaZeroBoundedFormula n :=
  -- `[f, a, b]`
  ((ᵣ0).isFunctionFromTo (ᵣ1) (ᵣ2) ⊓
    ∀₀∈ &1 ∀₀∈ &1 ((&0 =₀ &1).substBoundRud ![(ᵣ0) ﹫ (ᵣ3), (ᵣ0) ﹫ (ᵣ4)] ⟹ &3 =₀ &4) :
      L.DeltaZeroBoundedFormula 3).substBoundRud ![r, s, t]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] :
    (r.isInjectionFromTo s t).RelFree := by
  unfold RudimentaryTerm.isInjectionFromTo; infer_instance

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isInjectionFromTo
    (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] (xs : Fin n → M) :
    (r.isInjectionFromTo s t).toBoundedFormula 〘xs〙 ↔ (r〘xs〙 : M) !: s〘xs〙 ↪ t〘xs〙 := by
  have h {f a : M} : (∀ x ∈ a, ∀ y ∈ a, f ﹫ x = f ﹫ y → x = y) ↔
      ∀ ⦃x y : M⦄, x ∈ a → y ∈ a → f ﹫ x = f ﹫ y → x = y :=
    ⟨fun h x y hx hy ↦ h x hx y hy, fun h x hx y hy ↦ h hx hy⟩
  simp only [RudimentaryTerm.isInjectionFromTo, DeltaZeroBoundedFormula.realize_substBoundRud]
  simp [IsInjectionFromTo, snoc_nat, h]

@[simp, grind .]
theorem IsInjectionFromTo.isFunctionFromTo {f a b : M} (hf : f !: a ↪ b) :
    f !: a → b := hf.left

@[simp, grind .]
theorem IsInjectionFromTo.isFunction {f a b : M} (hf : f !: a ↪ b) :
    IsFunction f := hf.isFunctionFromTo.isFunction


@[simp, grind .]
theorem IsInjectionFromTo.dom_eq {f a b : M} (hf : f !: a ↪ b) :
    dom f = a :=
  hf.isFunctionFromTo.dom_eq

@[simp, grind .]
theorem IsInjectionFromTo.ran_subset {f a b : M} (hf : f !: a ↪ b) :
    ran f ⊆ b :=
  hf.isFunctionFromTo.ran_subset

@[simp, grind .]
theorem IsInjectionFromTo.of_ran_subset {f a b b' : M} (hf : f !: a ↪ b) (hb' : ran f ⊆ b') :
    f !: a ↪ b' := by
  grind [IsInjectionFromTo, IsFunctionFromTo]

theorem IsInjectionFromTo.eq {f a b x x' : M} (hf : f !: a ↪ b)
    (hx : x ∈ a) (hx' : x' ∈ a)
    (hxx' : f ﹫ x = f ﹫ x') : x = x' := hf.right hx hx' hxx'

@[simp, grind .]
theorem IsInjectionFromTo.eq_iff {f a b x x' : M} (hf : f !: a ↪ b)
    (hx : x ∈ a) (hx' : x' ∈ a) :
    f ﹫ x = f ﹫ x' ↔ x = x' := by
  grind [IsInjectionFromTo.eq]

@[simp, grind .]
theorem isInjectionFromTo_empty (b : M) : (∅ : M) !: ∅ ↪ b := by
  grind [IsInjectionFromTo]

@[simp, grind .]
theorem isInjectionFromTo_id (a : M) : id a !: a ↪ a := by
  grind [IsInjectionFromTo]

@[simp, grind .]
theorem IsInjectionFromTo.comp {f g a b c : M} (hf : f !: b ↪ c)
    (hg : g !: a ↪ b) : f !∘ g !: a ↪ c := by
  grind [IsInjectionFromTo]

@[simp, grind .]
theorem isInjectionFromTo_of_comp {f g a b c : M} (hf : f !: b → c)
    (hg : g !: a → b) (hfg : f !∘ g !: a ↪ c) : g !: a ↪ b := by
  grind [IsInjectionFromTo]

@[simp, grind .]
theorem isInjectionFromTo_of_comp_id
    {f g a b : M} (hf : f !: a → b) (hg : g !: b → a) (hgf : g !∘ f = id a) :
    f !: a ↪ b := by
  grind

/-- A function on `a` with values in `b` that is injective on `a` is an injection `a ↪ b` -/
theorem isInjectionFromTo_of_val {g a b : M} (hg : IsFunction g) (hdom : dom g = a)
    (hval : ∀ z ∈ a, g ﹫ z ∈ b) (hinj : ∀ z ∈ a, ∀ z' ∈ a, g ﹫ z = g ﹫ z' → z = z') :
    g !: a ↪ b :=
  ⟨isFunctionFromTo_of_val hg hdom hval, fun z z' hz hz' h ↦ hinj z hz z' hz' h⟩

end IsInjectionFromTo

section IsSurjectionFromTo

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

def IsSurjectionFromTo (f a b : M) := f !: a → b ∧ ran f = b

notation:50 f " !: " a:50 " ↠ " b:50 => IsSurjectionFromTo f a b

/-- The `Δ₀` formula `r !: s ↠ t` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.isSurjectionFromTo
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r s t : L.RudimentaryTerm n) :
    L.DeltaZeroBoundedFormula n :=
  r.isFunctionFromTo s t ⊓ (&0 =₀ &1).substBoundRud ![r.ran, t]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] :
    (r.isSurjectionFromTo s t).RelFree := by
  unfold RudimentaryTerm.isSurjectionFromTo; infer_instance

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isSurjectionFromTo
    (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] (xs : Fin n → M) :
    (r.isSurjectionFromTo s t).toBoundedFormula 〘xs〙 ↔ (r〘xs〙 : M) !: s〘xs〙 ↠ t〘xs〙 := by
  simp [RudimentaryTerm.isSurjectionFromTo, IsSurjectionFromTo]

@[simp, grind .]
theorem IsSurjectionFromTo.isFunctionFromTo {f a b : M} (hf : f !: a ↠ b) :
    f !: a → b := hf.left

@[simp, grind .]
theorem IsSurjectionFromTo.isFunction {f a b : M} (hf : f !: a ↠ b) :
    IsFunction f := hf.isFunctionFromTo.isFunction

@[simp, grind .]
theorem IsSurjectionFromTo.dom_eq {f a b : M} (hf : f !: a ↠ b) :
    dom f = a :=
  hf.isFunctionFromTo.dom_eq

@[simp, grind .]
theorem IsSurjectionFromTo.ran_eq {f a b : M} (hf : f !: a ↠ b) :
    ran f = b :=
  hf.right

theorem isSurjectionFromTo_ran_of_isFunctionFromTo {f a b : M} (hf : f !: a → b) :
    f !: a ↠ ran f :=
  ⟨by convert isFunctionFromTo_dom_ran hf.isFunction; grind, by grind⟩

theorem isSurjectionFromTo_dom_ran {f : M} (hf : IsFunction f) : f !: dom f ↠ ran f := by
  grind [IsSurjectionFromTo]

@[simp, grind .]
theorem IsSurjectionFromTo.exists_mem_val {f a b y : M} (hf : f !: a ↠ b)
    (hy : y ∈ b) :
    ∃ x ∈ a, f ﹫ x = y := by
  grind [IsSurjectionFromTo]

@[grind .]
theorem eq_empty_of_isSurjectionFromTo_empty {f b : M} (hf : f !: ∅ ↠ b) : b = ∅ := by
  ext y
  refine ⟨fun hy ↦ ?_, by simp⟩
  obtain ⟨x, hx, -⟩ := hf.exists_mem_val hy
  simp at hx

omit [Extensional M] [RudClosed M] in
/-- A function on `a` is a surjection from `a` onto its range -/
theorem IsFunction.isSurjectionFromTo {f a : M} (hf : IsFunction f) (hdom : dom f = a) :
    f !: a ↠ ran f :=
  ⟨⟨hf, hdom, subset_refl _⟩, rfl⟩

theorem isSurjectionFromTo_iff_of_isFunctionFromTo {f a b : M} (hf : f !: a → b) :
    f !: a ↠ b ↔ ∀ y ∈ b, ∃ x ∈ a, f ﹫ x = y := by
  grind [IsSurjectionFromTo, IsFunctionFromTo]

@[simp, grind .]
theorem isSurjectionFromTo_empty : (∅ : M) !: ∅ ↠ ∅ := by
  grind [IsSurjectionFromTo]

@[simp, grind .]
theorem isSurjectionFromTo_id (a : M) : id a !: a ↠ a := by
  grind [IsSurjectionFromTo]

@[simp, grind .]
theorem IsSurjectionFromTo.comp {f g a b c : M} (hf : f !: b ↠ c)
    (hg : g !: a ↠ b) : f !∘ g !: a ↠ c := by
  grind [IsSurjectionFromTo]

@[simp, grind .]
theorem isSurjectionFromTo_of_comp {f g a b c : M} (hf : f !: b → c)
    (hg : g !: a → b) (hfg : f !∘ g !: a ↠ c) : f !: b ↠ c := by
  simp only [IsSurjectionFromTo]
  grind

@[simp, grind .]
theorem isSurjectionFromTo_of_comp_id {f g a b : M} (hf : f !: a → b)
    (hg : g !: b → a) (hfg : f !∘ g = id b) : f !: a ↠ b := by
  grind [IsSurjectionFromTo]

/-- A nonempty subset `a ⊆ b` is the image of `b`: map `a` identically and `b \ a` to some
`c ∈ a` -/
theorem exists_isSurjectionFromTo_of_subset {a b : M} (hab : a ⊆ b) (ha : a ≠ ∅) :
    ∃ r, r !: b ↠ a := by
  simp only [ne_empty_iff] at ha
  obtain ⟨c, hc⟩ := ha
  have hdis : ∀ z ∈ dom (id a), z ∉ dom (constFun (b \ a) c) := by
    simp +contextual [mem_sdiff_iff]
  have hran : ran (id a ∪ constFun (b \ a) c) = a := by
    rw [ran_union, ran_id]
    have := ran_constFun_subset (b \ a) c
    ext w
    simp only [mem_union_iff]
    grind
  refine ⟨id a ∪ constFun (b \ a) c, ⟨(isFunction_id a).union_of_disjoint (isFunction_constFun _ c)
    hdis, ?_, by rw [hran]; exact subset_refl a⟩, hran⟩
  ext z
  simp only [dom_union, dom_id, dom_constFun, mem_union_iff, mem_sdiff_iff]
  grind

-- theorem IsInjective.isSurjective_inv_dom [M.ClosedUnderSProd] {f : M} (hf : IsInjective f) :
    -- IsSurjective f⁻¹ (dom f) := by
  -- grind [IsSurjective, isInjective_iff_isFunction_inv, ran_inv]

end IsSurjectionFromTo

section IsBijectionFromTo

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

def IsBijectionFromTo (f a b : M) := f !: a ↪ b ∧ f !: a ↠ b

notation:50 f " !: " a:50 " ↔ " b:50 => IsBijectionFromTo f a b

theorem isBijectionFromTo_iff {f a b : M} :
    f !: a ↔ b ↔ (f !: a → b ∧ (∀ x ∈ a, ∀ x' ∈ a, f ﹫ x = f ﹫ x' → x = x') ∧ ran f = b) := by
  grind [IsBijectionFromTo, IsInjectionFromTo, IsSurjectionFromTo]

@[simp, grind .]
theorem IsBijectionFromTo.isInjectionFromTo {f a b : M} (hf : f !: a ↔ b) : f !: a ↪ b := hf.left

@[simp, grind .]
theorem IsBijectionFromTo.isSurjectionFromTo {f a b : M} (hf : f !: a ↔ b) : f !: a ↠ b := hf.right

@[simp, grind .]
theorem IsBijectionFromTo.isFunctionFromTo {f a b : M} (hf : f !: a ↔ b) :
    f !: a → b := hf.isInjectionFromTo.isFunctionFromTo

@[simp, grind .]
theorem IsBijectionFromTo.isFunction {f a b : M} (hf : f !: a ↔ b) :
    IsFunction f := hf.isFunctionFromTo.isFunction

@[simp, grind .]
theorem IsBijectionFromTo.dom_eq {f a b : M} (hf : f !: a ↔ b) :
    dom f = a :=
  hf.isFunctionFromTo.dom_eq

@[simp, grind .]
theorem IsBijectionFromTo.ran_eq {f a b : M} (hf : f !: a ↔ b) :
    ran f = b :=
  hf.isSurjectionFromTo.ran_eq

theorem isBijectionFromTo_ran_of_isInjectionFromTo {f : M} (hf : f !: a ↪ b) :
    f !: a ↔ ran f :=
  ⟨by grind, by grind [isSurjectionFromTo_dom_ran (hf.isFunction)]⟩

@[simp, grind .]
theorem IsBijectionFromTo.existsUnique_mem_val {f a b y : M} (hf : f !: a ↔ b) (hy : y ∈ b) :
    ∃! x ∈ a, f ﹫ x = y := by
  obtain ⟨x, hx⟩ := hf.isSurjectionFromTo.exists_mem_val hy
  exact ⟨x, hx, by grind [hf.isInjectionFromTo]⟩

theorem isBijectionFromTo_iff_of_isFunctionFromTo {f a b : M} (hf : f !: a → b) :
    f !: a ↔ b ↔ ∀ y ∈ b, ∃! x ∈ a, f ﹫ x = y := by
  refine ⟨by grind, fun h ↦ ⟨?_, ?_⟩⟩
  · refine ⟨by grind, fun x₁ x₂ h₁ h₂ h₁₂ ↦ ?_⟩
    grind [(h (f ﹫ x₁) (by grind)).unique]
  · rw [isSurjectionFromTo_iff_of_isFunctionFromTo hf]
    exact fun y a ↦ (h y a).exists

theorem IsBijectionFromTo.comp {f g a b c : M} (hf : f !: b ↔ c)
    (hg : g !: a ↔ b) : f !∘ g !: a ↔ c := by
  grind [IsBijectionFromTo]

theorem IsBijectionFromTo.inv
    {f a b : M} (hf : f !: a ↔ b) :
    f⁻¹ !: b ↔ a := by
  simp only [isBijectionFromTo_iff]
  have := hf.dom_eq
  have := hf.ran_eq
  have hf₁ : IsFunction f⁻¹ := by
    refine ⟨by grind, fun y x₁ x₂ h₁ h₂ ↦ ?_⟩
    apply hf.isInjectionFromTo.eq <;> grind
  exact ⟨⟨hf₁, by grind [dom_inv]⟩, by grind [dom_inv], by grind [ran_inv]⟩

@[simp, grind .]
theorem IsBijectionFromTo.inv_val_val {f a b x : M} (hf : f !: a ↔ b)
    (hx : x ∈ a) :
    f⁻¹ ﹫ (f ﹫ x) = x := by
  apply hf.inv.isFunction.val_eq_of_rel
  grind [rel_val]

@[simp]
theorem IsBijectionFromTo.inv_comp {f a b : M} (hf : f !: a ↔ b) :
    f⁻¹ !∘ f = id a := by
  rw [IsFunction.ext (f := f⁻¹ !∘ f)]
  · exact hf.inv.isFunction.comp hf.isFunction
  all_goals grind [hf.inv]

@[simp, grind .]
theorem IsBijectionFromTo.val_inv_val {f a b y : M} (hf : f !: a ↔ b)
    (hx : y ∈ b) :
    f ﹫ (f⁻¹ ﹫ y) = y := by
  grind [hf.inv, rel_val]

@[simp]
theorem IsBijectionFromTo.comp_inv {f : M} (hf : f !: a ↔ b) :
    f !∘ f⁻¹ = id b := by
  have : dom (f !∘ f⁻¹) = ran f := by grind [dom_inv]
  rw [IsFunction.ext (f := f !∘ f⁻¹) (g := id (ran f))]
  · grind
  · exact hf.isFunction.comp hf.inv.isFunction
  all_goals grind [hf.inv]

@[simp, grind .]
theorem isBijectionFromTo_of_comp_id_comp_id
    {f g a b : M} (hf : f !: a → b) (hg : g !: b → a) (hfg : f !∘ g = id b) (hgf : g !∘ f = id a) :
    f !: a ↔ b := by
  grind [IsBijectionFromTo]

/-- An injection from a nonempty set `a` into `b` gives a surjection from `b` onto `a`: the inverse
on `ran g` together with a constant function on the rest of `b` -/
theorem exists_isSurjectionFromTo_of_isInjectionFromTo {g a b : M} (hg : g !: a ↪ b)
    (ha : a ≠ ∅) : ∃ h, h !: b ↠ a := by
  simp only [ne_empty_iff a] at ha
  obtain ⟨c, hc⟩ := ha
  have hbij : g !: a ↔ ran g := isBijectionFromTo_ran_of_isInjectionFromTo hg
  have hdis : ∀ z ∈ dom g⁻¹, z ∉ dom (constFun (b \ ran g) c) := by
    simp +contextual [dom_inv, mem_sdiff_iff]
  refine ⟨g⁻¹ ∪ constFun (b \ ran g) c, ?_⟩
  convert (hbij.inv.isFunction.union_of_disjoint (isFunction_constFun _ c) hdis).isSurjectionFromTo
    ?_
  · rw [ran_union, ran_inv, hg.isFunctionFromTo.dom_eq]
    have := ran_constFun_subset (b \ ran g) c
    ext w
    simp only [mem_union_iff]
    grind
  · have := hg.isFunctionFromTo.ran_subset
    ext z
    simp only [dom_union, dom_inv, dom_constFun, mem_union_iff, mem_sdiff_iff]
    grind

end IsBijectionFromTo

section ProdMap

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

/-- The rudimentary term for `prodMap f g a b`:
`⋃_{z ∈ a ×ˢ b} {!(z, !(f ﹫ left z, g ﹫ right z))}` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.prodMap₀
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 4 :=
  -- `[f, g, a, b]`
  RudimentaryTerm.iUnion ((ᵣ2 : L.RudimentaryTerm 4) ×ˢ (ᵣ3 : L.RudimentaryTerm 4))
    {ᵣ((ᵣ4 : L.RudimentaryTerm 5), ᵣ((ᵣ0) ﹫ (ᵣ4).left, (ᵣ1) ﹫ (ᵣ4).right))}

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (prodMap₀ : L.RudimentaryTerm 4).CharFree := by
  unfold prodMap₀; infer_instance

/-- The function `!(x, y) ↦ !(f ﹫ x, g ﹫ y)` on `a ×ˢ b` -/
noncomputable def prodMap (f g a b : M) : M := prodMap₀〘![f, g, a, b]〙

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 4 → M ↦ prodMap (ys 0) (ys 1) (ys 2) (ys 3)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq prodMap₀ fun ys ↦ by
    rw [prodMap, show ![ys 0, ys 1, ys 2, ys 3] = ys by ext i; fin_cases i <;> rfl]

theorem mem_prodMap_iff {f g a b p : M} :
    p ∈ prodMap f g a b ↔ ∃ z ∈ a ×ˢ b, p = !(z, !(f ﹫ left z, g ﹫ right z)) := by
  simp [prodMap, prodMap₀]

@[simp, grind =]
theorem rel_prodMap_iff {f g a b z w : M} :
    z [prodMap f g a b] w ↔ z ∈ a ×ˢ b ∧ w = !(f ﹫ left z, g ﹫ right z) := by
  simp only [mem_prodMap_iff, orderedPair_eq_orderedPair_iff]
  grind

@[simp, grind .]
theorem isFunction_prodMap (f g a b : M) : IsFunction (prodMap f g a b) := by
  refine ⟨fun p hp ↦ ?_, by grind⟩
  simp only [mem_prodMap_iff] at hp
  obtain ⟨z, -, rfl⟩ := hp
  simp [IsOrderedPair]

@[simp, grind =]
theorem dom_prodMap (f g a b : M) : dom (prodMap f g a b) = a ×ˢ b := by
  ext z
  simp [mem_dom_iff]

@[simp, grind =]
theorem prodMap_val {f g a b x y : M} (hx : x ∈ a) (hy : y ∈ b) :
    prodMap f g a b ﹫ !(x, y) = !(f ﹫ x, g ﹫ y) :=
  (isFunction_prodMap f g a b).val_eq_of_rel (by simp [mem_sprod _ _ _ _ hx hy])

/-- Functions `a → a'` and `b → b'` give a function `a ×ˢ b → a' ×ˢ b'` -/
theorem IsFunctionFromTo.prodMap {f g a a' b b' : M} (hf : f !: a → a') (hg : g !: b → b') :
    MemStructure.prodMap f g a b !: a ×ˢ b → a' ×ˢ b' := by
  refine isFunctionFromTo_of_val (isFunction_prodMap f g a b) (dom_prodMap f g a b) fun z hz ↦ ?_
  simp only [mem_sprod_iff] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  rw [prodMap_val hx hy]
  exact mem_sprod _ _ _ _ (hf.val_mem hx) (hg.val_mem hy)

/-- Injections `a ↪ a'` and `b ↪ b'` give an injection `a ×ˢ b ↪ a' ×ˢ b'` -/
theorem IsInjectionFromTo.prodMap {f g a a' b b' : M} (hf : f !: a ↪ a') (hg : g !: b ↪ b') :
    MemStructure.prodMap f g a b !: a ×ˢ b ↪ a' ×ˢ b' := by
  refine ⟨hf.isFunctionFromTo.prodMap hg.isFunctionFromTo,
    fun z z' hz hz' h ↦ ?_⟩
  simp only [mem_sprod_iff] at hz hz'
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  obtain ⟨x', hx', y', hy', rfl⟩ := hz'
  simp only [prodMap_val, hx, hy, hx', hy', orderedPair_eq_orderedPair_iff] at h
  rw [hf.eq hx hx' h.left, hg.eq hy hy' h.right]

/-- Surjections `a ↠ a'` and `b ↠ b'` give a surjection `a ×ˢ b ↠ a' ×ˢ b'` -/
theorem IsSurjectionFromTo.prodMap {f g a a' b b' : M} (hf : f !: a ↠ a') (hg : g !: b ↠ b') :
    MemStructure.prodMap f g a b !: a ×ˢ b ↠ a' ×ˢ b' := by
  rw [isSurjectionFromTo_iff_of_isFunctionFromTo
    (hf.isFunctionFromTo.prodMap hg.isFunctionFromTo)]
  intro w hw
  simp only [mem_sprod_iff] at hw
  obtain ⟨u, hu, v, hv, rfl⟩ := hw
  obtain ⟨x, hx, rfl⟩ := hf.exists_mem_val hu
  obtain ⟨y, hy, rfl⟩ := hg.exists_mem_val hv
  exact ⟨!(x, y), mem_sprod _ _ _ _ hx hy, prodMap_val hx hy⟩

/-- Bijections `a ↔ a'` and `b ↔ b'` give a bijection `a ×ˢ b ↔ a' ×ˢ b'` -/
theorem IsBijectionFromTo.prodMap {f g a a' b b' : M} (hf : f !: a ↔ a') (hg : g !: b ↔ b') :
    MemStructure.prodMap f g a b !: a ×ˢ b ↔ a' ×ˢ b' :=
  ⟨hf.isInjectionFromTo.prodMap hg.isInjectionFromTo,
    hf.isSurjectionFromTo.prodMap hg.isSurjectionFromTo⟩

end ProdMap

section DisjUnion

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

/-- The disjoint union of `a` and `b`, with `a` tagged by `∅` and `b` tagged by `{∅}` -/
noncomputable def disjUnion (a b : M) : M := ({∅} : M) ×ˢ a ∪ ({{∅}} : M) ×ˢ b

omit [Extensional M] [L.ExtraConstantsUnaryRelationsOnly] in
theorem mem_disjUnion_iff {a b p : M} :
    p ∈ disjUnion a b ↔ (∃ x ∈ a, p = !(∅, x)) ∨ ∃ y ∈ b, p = !({∅}, y) := by
  simp [disjUnion, mem_union_iff, mem_sprod_iff]

@[simp]
theorem empty_pair_mem_disjUnion_iff {a b x : M} : !(∅, x) ∈ disjUnion a b ↔ x ∈ a := by
  simp [mem_disjUnion_iff,
    (singleton_ne_empty (M := M) (x := ∅)).symm]

@[simp]
theorem singleton_pair_mem_disjUnion_iff {a b y : M} : !({∅}, y) ∈ disjUnion a b ↔ y ∈ b := by
  simp [mem_disjUnion_iff, orderedPair_eq_orderedPair_iff, singleton_ne_empty (M := M) (x := ∅)]

/-- `disjUnion a a` is `2 ×ˢ a` -/
theorem disjUnion_self (a : M) : disjUnion a a = succ (succ (∅ : M)) ×ˢ a := by
  ext p
  simp only [mem_disjUnion_iff, mem_sprod_iff, mem_succ_iff, succ_empty, mem_singleton_iff]
  grind

/-- The rudimentary term for `disjUnionSwap a b`:
`{!(!(∅, x), !({∅}, x)) | x ∈ a} ∪ {!(!({∅}, y), !(∅, y)) | y ∈ b}` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.disjUnionSwap₀
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 2 :=
  -- `[a, b]`
  RudimentaryTerm.iUnion (ᵣ0 : L.RudimentaryTerm 2)
      {ᵣ(ᵣ((∅ : L.RudimentaryTerm 3), ᵣ2), ᵣ(({∅} : L.RudimentaryTerm 3), ᵣ2))} ∪
    RudimentaryTerm.iUnion (ᵣ1 : L.RudimentaryTerm 2)
      {ᵣ(ᵣ(({∅} : L.RudimentaryTerm 3), ᵣ2), ᵣ((∅ : L.RudimentaryTerm 3), ᵣ2))}

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (disjUnionSwap₀ : L.RudimentaryTerm 2).CharFree := by
  unfold disjUnionSwap₀; infer_instance

/-- The bijection from `disjUnion a b` onto `disjUnion b a` swapping the tags -/
noncomputable def disjUnionSwap (a b : M) : M := disjUnionSwap₀〘a, b〙₂

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ disjUnionSwap (ys 0) (ys 1))
    Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ disjUnionSwap₀ fun _ _ ↦ rfl

theorem mem_disjUnionSwap_iff {a b p : M} :
    p ∈ disjUnionSwap a b ↔
      (∃ x ∈ a, p = !(!(∅, x), !({∅}, x))) ∨ ∃ y ∈ b, p = !(!({∅}, y), !(∅, y)) := by
  simp [disjUnionSwap, disjUnionSwap₀, mem_union_iff]

theorem rel_disjUnionSwap_iff {a b z w : M} :
    z [disjUnionSwap a b] w ↔
      (∃ x ∈ a, z = !(∅, x) ∧ w = !({∅}, x)) ∨ ∃ y ∈ b, z = !({∅}, y) ∧ w = !(∅, y) := by
  simp only [mem_disjUnionSwap_iff, orderedPair_eq_orderedPair_iff]

theorem isFunction_disjUnionSwap (a b : M) : IsFunction (disjUnionSwap a b) := by
  refine ⟨fun p hp ↦ ?_, fun z w₁ w₂ h₁ h₂ ↦ ?_⟩
  · rw [mem_disjUnionSwap_iff] at hp
    rcases hp with ⟨x, -, rfl⟩ | ⟨y, -, rfl⟩ <;> simp [IsOrderedPair]
  · rw [rel_disjUnionSwap_iff] at h₁ h₂
    grind [singleton_ne_empty (M := M) (x := ∅)]

theorem val_disjUnionSwap_empty {a b x : M} (hx : x ∈ a) :
    disjUnionSwap a b ﹫ !(∅, x) = !({∅}, x) := by
  refine (isFunction_disjUnionSwap a b).val_eq_of_rel ?_
  rw [rel_disjUnionSwap_iff]
  exact .inl ⟨x, hx, rfl, rfl⟩

theorem val_disjUnionSwap_singleton {a b y : M} (hy : y ∈ b) :
    disjUnionSwap a b ﹫ !({∅}, y) = !(∅, y) := by
  refine (isFunction_disjUnionSwap a b).val_eq_of_rel ?_
  rw [rel_disjUnionSwap_iff]
  exact .inr ⟨y, hy, rfl, rfl⟩

/-- Swapping the tags is a bijection from `disjUnion a b` onto `disjUnion b a` -/
theorem isBijectionFromTo_disjUnionSwap (a b : M) :
    disjUnionSwap a b !: disjUnion a b ↔ disjUnion b a := by
  have hdom : dom (disjUnionSwap a b) = disjUnion a b := by
    ext z
    simp only [mem_dom_iff, rel_disjUnionSwap_iff, mem_disjUnion_iff]
    grind
  have hinj : disjUnionSwap a b !: disjUnion a b ↪ disjUnion b a := by
    refine isInjectionFromTo_of_val (isFunction_disjUnionSwap a b) hdom (fun z hz ↦ ?_)
      fun z hz z' hz' h ↦ ?_
    · simp only [mem_disjUnion_iff] at hz
      rcases hz with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩ <;>
        simp [val_disjUnionSwap_empty, val_disjUnionSwap_singleton, *]
    · simp only [mem_disjUnion_iff] at hz hz'
      grind [val_disjUnionSwap_empty, val_disjUnionSwap_singleton]
  refine ⟨hinj, ?_⟩
  rw [isSurjectionFromTo_iff_of_isFunctionFromTo hinj.isFunctionFromTo]
  intro w hw
  simp only [mem_disjUnion_iff] at hw
  rcases hw with ⟨y, hy, rfl⟩ | ⟨x, hx, rfl⟩
  · exact ⟨!({∅}, y), by simp [hy], val_disjUnionSwap_singleton hy⟩
  · exact ⟨!(∅, x), by simp [hx], val_disjUnionSwap_empty hx⟩

/-- The rudimentary term for `disjUnionMap f g a b`:
`{!(!(∅, x), f ﹫ x) | x ∈ a} ∪ {!(!({∅}, y), g ﹫ y) | y ∈ b}` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.disjUnionMap₀
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 4 :=
  -- `[f, g, a, b]`
  RudimentaryTerm.iUnion (ᵣ2 : L.RudimentaryTerm 4)
      {ᵣ(ᵣ((∅ : L.RudimentaryTerm 5), ᵣ4), (ᵣ0) ﹫ (ᵣ4))} ∪
    RudimentaryTerm.iUnion (ᵣ3 : L.RudimentaryTerm 4)
      {ᵣ(ᵣ(({∅} : L.RudimentaryTerm 5), ᵣ4), (ᵣ1) ﹫ (ᵣ4))}

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (disjUnionMap₀ : L.RudimentaryTerm 4).CharFree := by
  unfold disjUnionMap₀; infer_instance

/-- The function on `disjUnion a b` gluing `f` on `a` and `g` on `b`:
`!(∅, x) ↦ f ﹫ x` and `!({∅}, y) ↦ g ﹫ y` -/
noncomputable def disjUnionMap (f g a b : M) : M := disjUnionMap₀〘![f, g, a, b]〙

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 4 → M ↦ disjUnionMap (ys 0) (ys 1) (ys 2) (ys 3)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq disjUnionMap₀ fun ys ↦ by
    rw [disjUnionMap, show ![ys 0, ys 1, ys 2, ys 3] = ys by ext i; fin_cases i <;> rfl]

theorem mem_disjUnionMap_iff {f g a b p : M} :
    p ∈ disjUnionMap f g a b ↔
      (∃ x ∈ a, p = !(!(∅, x), f ﹫ x)) ∨ ∃ y ∈ b, p = !(!({∅}, y), g ﹫ y) := by
  simp [disjUnionMap, disjUnionMap₀]

theorem rel_disjUnionMap_iff {f g a b z w : M} :
    z [disjUnionMap f g a b] w ↔
      (∃ x ∈ a, z = !(∅, x) ∧ w = f ﹫ x) ∨ ∃ y ∈ b, z = !({∅}, y) ∧ w = g ﹫ y := by
  simp [mem_disjUnionMap_iff]

theorem isFunction_disjUnionMap (f g a b : M) : IsFunction (disjUnionMap f g a b) := by
  grind [IsFunction, IsRelation, mem_disjUnionMap_iff, rel_disjUnionMap_iff, IsOrderedPair,
    singleton_ne_empty (M := M) (x := ∅)]

theorem dom_disjUnionMap (f g a b : M) : dom (disjUnionMap f g a b) = disjUnion a b := by
  ext z
  simp only [mem_dom_iff, rel_disjUnionMap_iff, mem_disjUnion_iff]
  grind

theorem val_disjUnionMap_empty {f g a b x : M} (hx : x ∈ a) :
    disjUnionMap f g a b ﹫ !(∅, x) = f ﹫ x :=
  (isFunction_disjUnionMap f g a b).val_eq_of_rel (by simp [rel_disjUnionMap_iff, hx])

theorem val_disjUnionMap_singleton {f g a b y : M} (hy : y ∈ b) :
    disjUnionMap f g a b ﹫ !({∅}, y) = g ﹫ y :=
  (isFunction_disjUnionMap f g a b).val_eq_of_rel (by simp [rel_disjUnionMap_iff, hy])

/-- Gluing functions `a → c` and `b → d` gives a function `disjUnion a b → c ∪ d` -/
theorem IsFunctionFromTo.disjUnionMap {f g a b c d : M} (hf : f !: a → c) (hg : g !: b → d) :
    MemStructure.disjUnionMap f g a b !: disjUnion a b → c ∪ d := by
  refine isFunctionFromTo_of_val (isFunction_disjUnionMap f g a b) (dom_disjUnionMap f g a b)
    fun z hz ↦ ?_
  simp only [mem_disjUnion_iff] at hz
  rcases hz with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
  · simp [val_disjUnionMap_empty hx, hf.val_mem hx]
  · simp [val_disjUnionMap_singleton hy, hg.val_mem hy]

/-- Gluing surjections `a ↠ c` and `b ↠ d` gives a surjection `disjUnion a b ↠ c ∪ d` -/
theorem IsSurjectionFromTo.disjUnionMap {f g a b c d : M} (hf : f !: a ↠ c) (hg : g !: b ↠ d) :
    MemStructure.disjUnionMap f g a b !: disjUnion a b ↠ c ∪ d := by
  simp only [isSurjectionFromTo_iff_of_isFunctionFromTo
    (hf.isFunctionFromTo.disjUnionMap hg.isFunctionFromTo), mem_union_iff]
  rintro w (hw | hw)
  · obtain ⟨x, hx, rfl⟩ := hf.exists_mem_val hw
    exact ⟨!(∅, x), by grind [empty_pair_mem_disjUnion_iff, val_disjUnionMap_empty]⟩
  · obtain ⟨y, hy, rfl⟩ := hg.exists_mem_val hw
    exact ⟨!({∅}, y), by grind [singleton_pair_mem_disjUnion_iff, val_disjUnionMap_singleton]⟩

end DisjUnion


section Restrict

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.restrict₀
  {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 2 :=
  (ᵣ0 : L.RudimentaryTerm 2) ∩ ((ᵣ1 : L.RudimentaryTerm 2) ×ˢ (ᵣ0 : L.RudimentaryTerm 2).ran)

@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.restrict
  {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r s : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  restrict₀.substBoundRud ![r, s]

infix:88 " ↾ " => FirstOrder.Language.RudimentaryTerm.restrict

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
  (restrict₀ : L.RudimentaryTerm 2).CharFree := by
  unfold restrict₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] : (r ↾ s).CharFree := by
  unfold restrict; infer_instance

noncomputable def restrict (f a : M) := restrict₀ 〘f, a〙₂
-- noncomputable def restrict (f a : M) := (∃'∈ &0 (&2).eqLeft &1) 〘a, ∈ f〙₀

infix:88 " ↾ " => FirstOrder.Language.MemStructure.restrict


omit [RudClosed M] in
@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_restrict₀ (xs : Fin 2 → M) :
    restrict₀〘xs〙 = (xs 0 ↾ xs 1 : M) := by
  simp only [restrict]
  rw [Matrix.vec_fin_two_eq]

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ ys 0 ↾ ys 1) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ restrict₀ fun _ _ ↦ rfl

theorem restrict_eq (f a : M) :
    f ↾ a = f ∩ (a ×ˢ ran f) := by
  simp [restrict, restrict₀]
  -- congr 2

theorem mem_restrict_iff (f a z : M) :
    z ∈ f ↾ a ↔ z ∈ f ∧ ∃ x ∈ a, ∃ y, z = !(x, y) := by
  simp only [restrict_eq, mem_inter_iff, mem_sprod_iff, and_congr_right_iff]
  grind

theorem rel_restrict_iff (f x y : M) :
    x [f ↾ a] y ↔ x [f] y ∧ x ∈ a := by
  grind [mem_restrict_iff]

theorem restrict_subset (f a : M) : f ↾ a ⊆ f := by
  grind [mem_restrict_iff]

@[simp, grind =]
theorem empty_restrict (a : M) : (∅ : M) ↾ a = ∅ := by
  grind [restrict_subset]

@[simp, grind .]
theorem IsFunction.restrict {f : M} (hf : IsFunction f) (a : M) :
    IsFunction (f ↾ a) :=
  hf.subset (restrict_subset _ _)

@[simp, grind .]
theorem dom_restrict {f : M} (hf : IsFunction f) (a : M) :
    dom (f ↾ a) = dom f ∩ a := by
  ext; grind [rel_restrict_iff]

@[simp, grind .]
theorem val_restrict (f : M) (hf : IsFunction f)
    {x a : M} (hx : x ∈ a) (hx' : x ∈ dom f) :
    (f ↾ a) ﹫ x = f ﹫ x := by
  grind [show x [f ↾ a] (f ﹫ x) by grind [rel_restrict_iff] ]

theorem restrict_eq_inter_sprod (f a : M) :
    f ↾ a = f ∩ (a ×ˢ ran f) := by
  ext
  simp only [mem_inter_iff]
  grind [mem_restrict_iff]

@[simp, grind =]
theorem restrict_restrict
    (f a b : M) : (f ↾ a) ↾ b = f ↾ (a ∩ b) := by
  ext
  simp only [mem_restrict_iff, mem_inter_iff]
  grind

theorem restrict_inter
    (f a b : M) : f ↾ (a ∩ b) = f ↾ a ∩ f ↾ b := by
  ext
  simp only [mem_restrict_iff, mem_inter_iff]
  grind

theorem restrict_union
    (f a b : M) : f ↾ (a ∪ b) = f ↾ a ∪ f ↾ b := by
  ext; grind [mem_restrict_iff]

theorem restrict_sUnion
    (f X z : M) : z ∈ f ↾ ⋃₀ X ↔ ∃ a ∈ X, z ∈ f ↾ a := by
  grind [mem_restrict_iff]

@[simp, grind =]
theorem restrict_empty (f : M) : (f ↾ ∅) = ∅ := by
  ext; grind [mem_restrict_iff]

@[simp, grind =]
theorem restrict_dom {f : M} (hf : IsFunction f) : (f ↾ dom f) = f := by
  apply hf.restrict (dom f) |>.ext hf <;> grind

theorem dom_restrict_of_subset {f a : M} (hf : IsFunction f) (ha : a ⊆ dom f) :
    dom (f ↾ a) = a := by
  ext; grind

/-- A function `a → b` restricts to a function `a' → b` for `a' ⊆ a` -/
theorem IsFunctionFromTo.restrict {f a b a' : M} (hf : f !: a → b) (ha : a' ⊆ a) :
    f ↾ a' !: a' → b := by
  refine ⟨hf.isFunction.restrict a', dom_restrict_of_subset hf.isFunction (by grind), ?_⟩
  grind [rel_restrict_iff]

/-- An injection `a ↪ b` restricts to an injection `a' ↪ b'` for `a' ⊆ a` and `b ⊆ b'` -/
theorem IsInjectionFromTo.restrict {f a b a' b' : M} (hf : f !: a ↪ b) (ha : a' ⊆ a)
    (hb : b ⊆ b') : f ↾ a' !: a' ↪ b' := by
  refine isInjectionFromTo_of_val (hf.isFunction.restrict a')
    (dom_restrict_of_subset hf.isFunction (by grind)) (fun z hz ↦ ?_)
    fun z hz z' hz' h ↦ ?_ <;> grind

/-- Two functions agreeing on a common subset of their domains have the same restriction to it -/
theorem IsFunction.restrict_eq_restrict {f g a : M} (hf : IsFunction f) (hg : IsFunction g)
    (hfa : a ⊆ dom f) (hga : a ⊆ dom g) (h : ∀ x ∈ a, f ﹫ x = g ﹫ x) : f ↾ a = g ↾ a := by
  apply (hf.restrict a).ext (hg.restrict a)
  · simp [hf, hfa, hg, hga]
  · intro x hx
    simp only [hf, dom_restrict, hfa, inter_of_subset_left] at hx
    simp [val_restrict, hf, hg, h, hx, hfa hx, hga hx]

end Restrict

section Image

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

noncomputable def image (f a : M) := ran (f ↾ a)

infix:88 " '' " => FirstOrder.Language.MemStructure.image

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ ys 0 '' ys 1) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ (restrict₀.substBoundRud ![ᵣ0, ᵣ1]).ran fun _ _ ↦ by
    simp [image]

@[simp, grind =]
theorem image_empty (f : M) : f '' ∅ = ∅ := by
  grind [image]

@[simp, grind =]
theorem image_dom (f : M) : f '' (dom f) = ran f := by
  ext; grind [image, mem_restrict_iff]

theorem image_union (f a b : M) : f '' (a ∪ b) = f '' a ∪ f '' b := by
  grind [image, restrict_union, ran_union]

@[simp]
theorem mem_image_iff (f a y : M) : y ∈ f '' a ↔ ∃ x ∈ a, x [f] y := by
  simp only [image, mem_ran_iff, rel_restrict_iff]
  grind

theorem mem_image_sUnion_iff (f X z : M) :
    z ∈ f '' (⋃₀ X) ↔ ∃ a ∈ X, z ∈ f '' a := by
  grind [image, restrict_sUnion]

end Image

section Update

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

/-- The rudimentary term for `erase f x`: `f ↾ (dom f \ {x})` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.erase₀
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 2 :=
  (ᵣ0 : L.RudimentaryTerm 2) ↾ ((ᵣ0 : L.RudimentaryTerm 2).dom \ {ᵣ1})

/-- The rudimentary term for `erase r s` -/
@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.erase
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  erase₀.substBoundRud ![r, s]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (erase₀ : L.RudimentaryTerm 2).CharFree := by
  unfold erase₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] : (r.erase s).CharFree := by
  unfold RudimentaryTerm.erase; infer_instance

/-- The rudimentary term for `update f x y`: `insert !(x, y) (erase f x)` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.update₀
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 3 :=
  insert ᵣ(ᵣ1, ᵣ2) (erase₀.substBoundRud ![ᵣ0, ᵣ1])

/-- The rudimentary term for `update r s t` -/
@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.update
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s t : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  update₀.substBoundRud ![r, s, t]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (update₀ : L.RudimentaryTerm 3).CharFree := by
  unfold update₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] :
    (r.update s t).CharFree := by
  unfold RudimentaryTerm.update; infer_instance

/-- `f` with the point at `x` removed -/
noncomputable def erase (f x : M) : M := erase₀〘f, x〙₂

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ erase (ys 0) (ys 1)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ erase₀ fun _ _ ↦ rfl

/-- `f` with the value at `x` set to `y` -/
noncomputable def update (f x y : M) : M := update₀〘f, x, y〙₃

instance : MulticlassFunction.DeltaZero (fun ys : Fin 3 → M ↦ update (ys 0) (ys 1) (ys 2))
    Set.univ :=
  MulticlassFunction.deltaZero_of_eq update₀ fun ys ↦ by
    rw [update, show ![ys 0, ys 1, ys 2] = ys by ext i; fin_cases i <;> rfl]

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_erase₀ (xs : Fin 2 → M) :
    erase₀〘xs〙 = erase (xs 0) (xs 1) := by
  simp only [erase]
  rw [Matrix.vec_fin_two_eq]

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_update₀ (xs : Fin 3 → M) :
    update₀〘xs〙 = update (xs 0) (xs 1) (xs 2) := by
  simp only [update]
  congr
  ext i; fin_cases i <;> rfl

omit [RudClosed M] in
theorem erase_eq (f x : M) : erase f x = f ↾ (dom f \ {x}) := by
  simp [erase, erase₀]

omit [RudClosed M] in
theorem update_eq (f x y : M) : update f x y = insert !(x, y) (erase f x) := by
  simp [update, update₀]

@[simp, grind =]
theorem rel_erase_iff {f x z w : M} : z [erase f x] w ↔ z [f] w ∧ z ≠ x := by
  simp only [erase_eq, rel_restrict_iff, mem_sdiff_iff, mem_singleton_iff]
  grind

@[simp, grind .]
theorem IsFunction.erase {f : M} (hf : IsFunction f) (x : M) : IsFunction (erase f x) := by
  rw [erase_eq]
  exact hf.restrict _

@[simp, grind =]
theorem dom_erase (f x : M) : dom (erase f x) = dom f \ {x} := by
  ext z
  simp only [mem_dom_iff, rel_erase_iff, mem_sdiff_iff, mem_singleton_iff]
  grind

@[simp, grind =]
theorem val_erase {f x z : M} (hf : IsFunction f) (hz : z ∈ dom f) (hzx : z ≠ x) :
    erase f x ﹫ z = f ﹫ z :=
  (hf.erase x).val_eq_of_rel (by simp [rel_val hf hz, hzx])

omit [L.ExtraConstantsUnaryRelationsOnly] in
@[simp, grind =]
theorem rel_insert_iff {f x y z w : M} : z [insert !(x, y) f] w ↔ (z = x ∧ w = y) ∨ z [f] w := by
  simp [mem_insert_iff]

/-- Adding a point `!(x, y)` with `x ∉ dom f` to a function `f` gives a function -/
theorem IsFunction.insert {f x : M} (hf : IsFunction f) (hx : x ∉ dom f) (y : M) :
    IsFunction (insert !(x, y) f) := by
  refine ⟨fun p hp ↦ ?_, fun z w₁ w₂ h₁ h₂ ↦ ?_⟩
  · simp only [mem_insert_iff] at hp
    rcases hp with rfl | hp
    · simp [IsOrderedPair]
    · exact hf.isRelation hp
  · grind

@[simp, grind =]
theorem dom_insert (f x y : M) : dom (insert !(x, y) f) = insert x (dom f) := by
  ext z
  simp [mem_dom_iff, mem_insert_iff, exists_or]

@[simp, grind =]
theorem ran_insert (f x y : M) : ran (insert !(x, y) f) = insert y (ran f) := by
  ext w
  simp [mem_ran_iff, mem_insert_iff, exists_or]

@[simp, grind =]
theorem val_insert_self {f x : M} (hf : IsFunction f) (hx : x ∉ dom f) (y : M) :
    insert !(x, y) f ﹫ x = y :=
  (hf.insert hx y).val_eq_of_rel (by simp)

@[simp, grind =]
theorem val_insert_of_mem {f x z : M} (hf : IsFunction f) (hx : x ∉ dom f) (y : M)
    (hz : z ∈ dom f) : insert !(x, y) f ﹫ z = f ﹫ z :=
  (hf.insert hx y).val_eq_of_rel (by simp [rel_val hf hz])

@[simp, grind .]
theorem IsFunction.update {f : M} (hf : IsFunction f) (x y : M) : IsFunction (update f x y) := by
  simp [update_eq, (hf.erase x).insert]

@[simp, grind =]
theorem dom_update (f x y : M) : dom (update f x y) = insert x (dom f) := by
  ext z
  simp [update_eq]
  tauto

@[simp, grind =]
theorem val_update_self {f : M} (hf : IsFunction f) (x y : M) : update f x y ﹫ x = y := by
  simp [update_eq, hf]

@[simp, grind =]
theorem val_update_of_ne {f x z : M} (hf : IsFunction f) (y : M) (hz : z ∈ dom f) (hzx : z ≠ x) :
    update f x y ﹫ z = f ﹫ z := by
  simp [update_eq, hf, hz, hzx]

/-- The function with domain `{x}` mapping `x` to `y` -/
noncomputable def singletonFun (x y : M) : M := update ∅ x y

@[simp, grind .]
theorem isFunction_singletonFun (x y : M) : IsFunction (singletonFun x y) :=
  isFunction_empty.update x y

@[simp, grind =]
theorem dom_singletonFun (x y : M) : dom (singletonFun x y) = {x} := by
  ext z
  simp [singletonFun, mem_insert_iff]

@[simp, grind =]
theorem singletonFun_val (x y : M) : singletonFun x y ﹫ x = y :=
  val_update_self isFunction_empty x y

@[simp, grind =]
theorem ran_singletonFun (x y : M) : ran (singletonFun x y) = {y} := by
  ext z
  simp only [mem_ran_iff, mem_singleton_iff]
  grind [singletonFun, update_eq]

theorem isFunctionFromTo_singletonFun {x y b : M} (hy : y ∈ b) : singletonFun x y !: {x} → b :=
  ⟨isFunction_singletonFun x y, dom_singletonFun x y, by simpa using hy⟩

/-- `erase (f \ (dom f ×ˢ {y})) x` is `f` without the point `x` and the points mapped to `y` -/
theorem rel_erase_sdiff_sprod_iff {f x y z w : M} :
    z [erase (f \ (dom f ×ˢ ({y} : M))) x] w ↔ (z [f] w ∧ w ≠ y) ∧ z ≠ x := by
  simp only [rel_erase_iff, mem_sdiff_iff, pair_mem_sprod_iff, mem_singleton_iff]
  grind

theorem dom_erase_sdiff_sprod_subset (f x y : M) :
    dom (erase (f \ (dom f ×ˢ ({y} : M))) x) ⊆ dom f \ {x} := by
  intro z hz
  simp only [mem_dom_iff, rel_erase_sdiff_sprod_iff, mem_sdiff_iff, mem_singleton_iff] at hz ⊢
  grind

theorem IsFunction.erase_sdiff_sprod {f : M} (hf : IsFunction f) (x y : M) :
    IsFunction (MemStructure.erase (f \ (dom f ×ˢ ({y} : M))) x) :=
  (hf.subset (sdiff_subset_left _ _)).erase x

/-- `h` patched with the constant function `c` on `a \ dom h` -/
theorem rel_union_constFun_iff {h a c z w : M} :
    z [h ∪ constFun (a \ dom h) c] w ↔ z [h] w ∨ ((z ∈ a ∧ z ∉ dom h) ∧ w = c) := by
  simp [mem_union_iff, mem_sdiff_iff]

theorem IsFunction.union_constFun {h : M} (hh : IsFunction h) (a c : M) :
    IsFunction (h ∪ constFun (a \ dom h) c) :=
  hh.union_of_disjoint (isFunction_constFun _ c) (by simp +contextual [mem_sdiff_iff])

theorem ran_union_constFun_subset (h a c : M) :
    ran (h ∪ constFun (a \ dom h) c) ⊆ insert c (ran h) := by
  intro w hw
  simp only [mem_ran_iff, rel_union_constFun_iff, mem_insert_iff] at hw ⊢
  grind

theorem ran_union_constFun {h a c : M} (hz : ∃ z ∈ a, z ∉ dom h) :
    ran (h ∪ constFun (a \ dom h) c) = insert c (ran h) := by
  ext w
  simp only [mem_ran_iff, rel_union_constFun_iff, mem_insert_iff]
  grind

theorem dom_union_constFun {h a : M} (ha : dom h ⊆ a) (c : M) :
    dom (h ∪ constFun (a \ dom h) c) = a := by
  ext z
  simp only [dom_union, dom_constFun, mem_union_iff, mem_sdiff_iff]
  grind

/-- A surjection from `insert x a` onto `insert y b` with `x ∉ a`, `y ∉ b` and `b ≠ ∅` gives one
from `a` onto `b`: drop `x` and the points mapped to `y` from `f`, then send the points of `a`
left out to `f ﹫ x`, or to any point of `b` if `f ﹫ x = y` -/
theorem exists_isSurjectionFromTo_of_insert {f a b x y : M} (hx : x ∉ a) (hy : y ∉ b)
    (hb : b ≠ ∅) (hf : f !: insert x a ↠ insert y b) : ∃ g, g !: a ↠ b := by
  -- `f'` is `f` without `x` and the points mapped to `y`
  set f' := erase (f \ (dom f ×ˢ ({y} : M))) x
  have hdomf' : dom f' ⊆ a := fun z hz ↦ by
    grind [dom_erase_sdiff_sprod_subset f x y hz]
  have hranf' {w : M} : w ∈ ran f' ↔ ∃ z ∈ a, f ﹫ z = w ∧ w ≠ y := by
    simp only [mem_ran_iff, f', rel_erase_sdiff_sprod_iff, hf.isFunctionFromTo.rel_iff,
      mem_insert_iff]
    constructor <;> grind
  have hranb {w : M} (hw : w ∈ ran f') : w ∈ b := by
    rw [hranf'] at hw
    obtain ⟨z, hz, rfl, hzy⟩ := hw
    have := hf.isFunctionFromTo.val_mem (subset_insert _ _ hz)
    grind
  by_cases hxy : f ﹫ x = y
  · -- `ran f' = b`: patch with any `b₀ ∈ b`
    simp only [ne_empty_iff] at hb
    obtain ⟨b₀, hb₀⟩ := hb
    refine ⟨f' ∪ constFun (a \ dom f') b₀, ?_⟩
    convert ((hf.isFunction.erase_sdiff_sprod x y).union_constFun a b₀).isSurjectionFromTo
      (dom_union_constFun hdomf' b₀)
    ext w
    refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
    · obtain ⟨z, hz, rfl⟩ := hf.exists_mem_val (subset_insert _ _ hw)
      simp only [ran_union, mem_union_iff]
      grind
    · have := ran_union_constFun_subset f' a b₀ hw
      simp only [mem_insert_iff] at this
      grind
  · -- `ran f'` and `f ﹫ x` make up `b`, and `dom f'` misses the preimage of `y`: patch with
    -- `f ﹫ x`
    have hmiss : ∃ z ∈ a, z ∉ dom f' := by
      obtain ⟨z, hz, hzy⟩ := hf.exists_mem_val (mem_insert (x := y) (y := b))
      refine ⟨z, by grind, fun hzf ↦ ?_⟩
      simp only [mem_dom_iff, f', rel_erase_sdiff_sprod_iff, hf.isFunctionFromTo.rel_iff] at hzf
      grind
    refine ⟨f' ∪ constFun (a \ dom f') (f ﹫ x), ?_⟩
    convert ((hf.isFunction.erase_sdiff_sprod x y).union_constFun a _).isSurjectionFromTo
      (dom_union_constFun hdomf' _)
    rw [ran_union_constFun hmiss]
    ext w
    simp only [mem_insert_iff]
    refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
    · obtain ⟨z, hz, rfl⟩ := hf.exists_mem_val (subset_insert _ _ hw)
      grind
    · have := hf.isFunctionFromTo.val_mem (mem_insert (x := x) (y := a))
      grind

/-- `f` with `x` removed and the preimage of `y` sent to `f ﹫ x` -/
noncomputable def eraseRedirect (f x y : M) : M :=
  (erase f x \ (dom f ×ˢ ({y} : M))) ∪ constFun (f⁻¹ '' ({y} : M) \ {x}) (f ﹫ x)

theorem rel_eraseRedirect_iff {f x y z w : M} :
    z [eraseRedirect f x y] w ↔ ((z [f] w ∧ w ≠ y) ∨ (z [f] y ∧ w = f ﹫ x)) ∧ z ≠ x := by
  simp only [eraseRedirect, mem_union_iff, mem_sdiff_iff, rel_erase_iff, pair_mem_sprod_iff,
    mem_singleton_iff, rel_constFun_iff, mem_image_iff, rel_inv, exists_eq_left]
  grind

theorem IsFunction.eraseRedirect {f : M} (hf : IsFunction f) (x y : M) :
    IsFunction (MemStructure.eraseRedirect f x y) := by
  refine ⟨((hf.erase x).isRelation.subset (sdiff_subset_left _ _)).union
    (isFunction_constFun _ _).isRelation, fun z w₁ w₂ h₁ h₂ ↦ ?_⟩
  rw [rel_eraseRedirect_iff] at h₁ h₂
  grind [hf.val_eq_of_rel]

theorem val_eraseRedirect_of_ne {f x y z : M} (hf : IsFunction f) (hz : z ∈ dom f) (hzx : z ≠ x)
    (h : f ﹫ z ≠ y) : eraseRedirect f x y ﹫ z = f ﹫ z :=
  (hf.eraseRedirect x y).val_eq_of_rel (by simp [rel_eraseRedirect_iff, rel_val hf hz, h, hzx])

theorem val_eraseRedirect_of_eq {f x y z : M} (hf : IsFunction f) (hz : z ∈ dom f) (hzx : z ≠ x)
    (h : f ﹫ z = y) : eraseRedirect f x y ﹫ z = f ﹫ x :=
  (hf.eraseRedirect x y).val_eq_of_rel (by simp [rel_eraseRedirect_iff, ← h, rel_val hf hz, hzx])

theorem dom_eraseRedirect (f x y : M) : dom (eraseRedirect f x y) = dom f \ {x} := by
  ext z
  simp only [mem_dom_iff, rel_eraseRedirect_iff, mem_sdiff_iff, mem_singleton_iff]
  grind

/-- An injection `f` from `insert x a` into `insert y b` with `x ∉ a` gives the injection
`eraseRedirect f x y` from `a` into `b` -/
theorem IsInjectionFromTo.eraseRedirect {f a b x y : M} (hx : x ∉ a)
    (hf : f !: insert x a ↪ insert y b) : MemStructure.eraseRedirect f x y !: a ↪ b := by
  refine isInjectionFromTo_of_val (hf.isFunction.eraseRedirect x y) ?_ (fun z hz ↦ ?_)
    fun z hz z' hz' h' ↦ ?_
  · rw [dom_eraseRedirect, hf.isFunctionFromTo.dom_eq]
    ext z
    simp only [mem_sdiff_iff, mem_insert_iff, mem_singleton_iff]
    grind
  · have : f ﹫ x ∈ insert y b := hf.isFunctionFromTo.val_mem (mem_insert _ _)
    have : f ﹫ z ∈ insert y b := hf.isFunctionFromTo.val_mem (subset_insert _ _ hz)
    grind [val_eraseRedirect_of_ne, val_eraseRedirect_of_eq]
  · by_cases hzy : f ﹫ z = y <;> grind [val_eraseRedirect_of_ne, val_eraseRedirect_of_eq]

/-- A bijection `f` from `insert x a` onto `insert y b` with `x ∉ a` and `y ∉ b` gives the bijection
`eraseRedirect f x y` from `a` onto `b` -/
theorem IsBijectionFromTo.eraseRedirect {f a b x y : M} (hx : x ∉ a) (hy : y ∉ b)
    (hf : f !: insert x a ↔ insert y b) : MemStructure.eraseRedirect f x y !: a ↔ b := by
  have hg := hf.isInjectionFromTo.eraseRedirect hx
  refine ⟨hg, ?_⟩
  rw [isSurjectionFromTo_iff_of_isFunctionFromTo hg.isFunctionFromTo]
  intro w hw
  obtain ⟨z, hz, rfl⟩ := hf.isSurjectionFromTo.exists_mem_val (subset_insert _ _ hw)
  obtain ⟨z', hz', hz'y⟩ := hf.isSurjectionFromTo.exists_mem_val (mem_insert _ _)
  grind [val_eraseRedirect_of_eq, val_eraseRedirect_of_ne]

/-- Functions on `succ n` agreeing on `n` and at `n` are equal -/
theorem IsFunctionFromTo.eq_of_restrict_eq {s s' n b b' : M} (hs : s !: succ n → b)
    (hs' : s' !: succ n → b') (hres : s ↾ n = s' ↾ n) (hval : s ﹫ n = s' ﹫ n) : s = s' := by
  refine hs.isFunction.ext hs'.isFunction (by rw [hs.dom_eq, hs'.dom_eq]) fun k hk ↦ ?_
  rw [hs.dom_eq, mem_succ_iff] at hk
  rcases hk with rfl | hk
  · exact hval
  · rw [← val_restrict s hs.isFunction hk (by rw [hs.dom_eq]; grind), hres,
      val_restrict s' hs'.isFunction hk (by rw [hs'.dom_eq]; grind)]

/-- Extending a function on `n` by `!(n, y)` gives a function on `succ n` -/
theorem IsFunctionFromTo.insert_succ {s n b y : M} (hs : s !: n → b) (hn : n ∉ n) (hy : y ∈ b) :
    insert !(n, y) s !: succ n → b := by
  have hns : n ∉ dom s := by rwa [hs.dom_eq]
  refine isFunctionFromTo_of_val (hs.isFunction.insert hns y) (by rw [dom_insert, hs.dom_eq]; rfl)
    fun k hk ↦ ?_
  rw [mem_succ_iff] at hk
  rcases hk with rfl | hk
  · rwa [val_insert_self hs.isFunction hns]
  · rw [val_insert_of_mem hs.isFunction hns y (by rwa [hs.dom_eq])]
    exact hs.val_mem hk

theorem IsFunctionFromTo.restrict_insert_succ {s n b y : M} (hs : s !: n → b) (hn : n ∉ n) :
    insert !(n, y) s ↾ n = s := by
  have hns : n ∉ dom s := by rwa [hs.dom_eq]
  have hf := hs.isFunction.insert hns y
  refine (hf.restrict n).ext hs.isFunction (by rw [dom_restrict_of_subset hf (by grind),
    hs.dom_eq]) fun k hk ↦ ?_
  rw [dom_restrict_of_subset hf (by grind)] at hk
  rw [val_restrict _ hf hk (by grind), val_insert_of_mem hs.isFunction hns y (by rwa [hs.dom_eq])]

/-- The restriction of a function on `succ n` to `n` is a function on `n` -/
theorem IsFunctionFromTo.restrict_succ {s n b : M} (hs : s !: succ n → b) : s ↾ n !: n → b :=
  hs.restrict (by grind)

end Update



section ClassFunction

variable [L.ExtraConstantsUnaryRelationsOnly]

def IsSetRestrictedTo (G : ClassFunction M) (x : M) :=
  ∃ f : M, IsFunction f ∧ dom f = x ∧ ∀ y ∈ x, f ﹫ y = G y

noncomputable instance (G : ClassFunction M) : Decidable (IsSetRestrictedTo G x) :=
  Classical.propDecidable _

noncomputable def toSetRestrictedTo (G : ClassFunction M) (x : M) :=
  dite (IsSetRestrictedTo G x) Classical.choose default

infix:88 " ↾₀ " => FirstOrder.Language.MemStructure.toSetRestrictedTo

theorem toSetRestrictedTo_spec {G : ClassFunction M} {x : M}
    (h : IsSetRestrictedTo G x) :
    IsFunction (G ↾₀ x) ∧ dom (G ↾₀ x) = x ∧ ∀ y ∈ x, (G ↾₀ x) ﹫ y = G y := by
  simp only [toSetRestrictedTo] at h ⊢
  convert Classical.choose_spec h <;> simp [h]

@[simp]
theorem isFunction_toSetRestrictedTo {G : ClassFunction M} {x : M}
    (h : IsSetRestrictedTo G x) :
    IsFunction (G ↾₀ x) :=
  toSetRestrictedTo_spec h |>.left

@[simp]
theorem dom_toSetRestrictedTo {G : ClassFunction M} {x : M}
    (h : IsSetRestrictedTo G x) :
    dom (G ↾₀ x) = x :=
  toSetRestrictedTo_spec h |>.right.left

@[simp]
theorem val_toSetRestrictedTo {G : ClassFunction M} {x y : M}
    (h : IsSetRestrictedTo G x) (hy : y ∈ x) :
    (G ↾₀ x) ﹫ y = G y :=
  toSetRestrictedTo_spec h |>.right.right y hy

/-- The restriction of `G` to `x` is the unique function on `x` agreeing with `G` -/
theorem toSetRestrictedTo_eq [Extensional M] [RudClosed M] {G : ClassFunction M} {x f : M}
    (hf : IsFunction f) (hdom : dom f = x) (hval : ∀ y ∈ x, f ﹫ y = G y) : G ↾₀ x = f := by
  have h : IsSetRestrictedTo G x := ⟨f, hf, hdom, hval⟩
  grind [dom_toSetRestrictedTo, val_toSetRestrictedTo, isFunction_toSetRestrictedTo]

@[simp]
theorem mem_ran_toSetRestrictedTo_iff [Extensional M] [RudClosed M] {G : ClassFunction M}
    {x y : M} (h : IsSetRestrictedTo G x) : y ∈ ran (G ↾₀ x) ↔ ∃ z ∈ x, G z = y := by
  rw [(isFunction_toSetRestrictedTo h).mem_ran_iff, dom_toSetRestrictedTo h]
  exact exists_congr fun z ↦ and_congr_right fun hz ↦ by rw [val_toSetRestrictedTo h hz]

theorem mem_ran_restrict_toSetRestrictedTo_iff [Extensional M] [RudClosed M]
    {G : ClassFunction M} {x s y : M} (h : IsSetRestrictedTo G x) (hs : s ⊆ x) :
    y ∈ ran ((G ↾₀ x) ↾ s) ↔ ∃ z ∈ s, G z = y := by
  have hf : IsFunction (G ↾₀ x) := isFunction_toSetRestrictedTo h
  have hsd : s ⊆ dom (G ↾₀ x) := by rwa [dom_toSetRestrictedTo h]
  rw [(hf.restrict s).mem_ran_iff, dom_restrict_of_subset hf hsd]
  refine exists_congr fun z ↦ and_congr_right fun hz ↦ ?_
  rw [val_restrict _ hf hz (hsd hz), val_toSetRestrictedTo h (hs hz)]

theorem isFunctionFromTo_toSetRestrictedTo [Extensional M] [RudClosed M] {G : ClassFunction M}
    {a b : M} (h : IsSetRestrictedTo G a) (hG : ∀ x ∈ a, G x ∈ b) : G ↾₀ a !: a → b := by
  refine ⟨isFunction_toSetRestrictedTo h, dom_toSetRestrictedTo h, fun y hy ↦ ?_⟩
  simp only [mem_ran_toSetRestrictedTo_iff, h] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hG x hx

theorem isInjectionFromTo_toSetRestrictedTo [Extensional M] [RudClosed M] {G : ClassFunction M}
    {a b : M} (h : IsSetRestrictedTo G a) (hG : ∀ x ∈ a, G x ∈ b)
    (hinj : ∀ x ∈ a, ∀ y ∈ a, G x = G y → x = y) : G ↾₀ a !: a ↪ b := by
  refine ⟨isFunctionFromTo_toSetRestrictedTo h hG, fun x y hx hy hxy ↦ hinj x hx y hy ?_⟩
  rwa [val_toSetRestrictedTo h hx, val_toSetRestrictedTo h hy] at hxy

theorem isSurjectionFromTo_toSetRestrictedTo [Extensional M] [RudClosed M] {G : ClassFunction M}
    {a b : M} (h : IsSetRestrictedTo G a) (hG : ∀ y, y ∈ b ↔ ∃ x ∈ a, G x = y) :
    G ↾₀ a !: a ↠ b := by
  refine ⟨isFunctionFromTo_toSetRestrictedTo h fun x hx ↦ ?_, ?_⟩
  · rw [hG]
    exact ⟨x, hx, rfl⟩
  ext y
  simp only [mem_ran_toSetRestrictedTo_iff, h, hG]

end ClassFunction

section CompLeft

variable [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [RudClosed M]

/-- Composing with an injection is left-cancellative -/
theorem IsInjectionFromTo.comp_left_cancel {f a b c s s' : M} (hf : f !: b ↪ c)
    (hs : s !: a → b) (hs' : s' !: a → b) (h : f !∘ s = f !∘ s') : s = s' := by
  refine hs.isFunction.ext hs'.isFunction (by rw [hs.dom_eq, hs'.dom_eq]) fun k hk ↦ ?_
  rw [hs.dom_eq] at hk
  -- by injectivity of `f`, it suffices to show `f (s k) = f (s' k)`
  refine hf.eq (hs.val_mem hk) (hs'.val_mem hk) ?_
  rw [← comp_val hf.isFunction hs.isFunction (by grind),
    ← comp_val hf.isFunction hs'.isFunction (by grind), h]

/-- `s ↦ f !∘ s` on a set `D` of functions -/
noncomputable def compLeft (f D : M) : M := (fun s ↦ f !∘ s) ↾₀ D

/-- Composing with an injection `f !: b ↪ c` injects a set `D` of functions into `b` into any
set `E` containing their composites with `f` -/
theorem IsInjectionFromTo.compLeft {f b c D E : M} (hf : f !: b ↪ c)
    (hr : IsSetRestrictedTo (fun s ↦ f !∘ s) D) (hD : ∀ s ∈ D, s !: dom s → b)
    (hDE : ∀ s ∈ D, f !∘ s ∈ E) : MemStructure.compLeft f D !: D ↪ E := by
  refine isInjectionFromTo_toSetRestrictedTo hr hDE fun s hs s' hs' h ↦ ?_
  have hdom : dom s = dom s' := by
    rw [← ((hD s hs).comp hf.isFunctionFromTo).dom_eq, h,
      ((hD s' hs').comp hf.isFunctionFromTo).dom_eq]
  refine hf.comp_left_cancel (hD s hs) ?_ h
  rw [hdom]
  exact hD s' hs'

/-- Composing with a bijection `f !: b ↔ c` is a bijection `D ↔ E` between sets of functions
into `b` and into `c` that are closed under composing with `f` and `f⁻¹` respectively -/
theorem IsBijectionFromTo.compLeft {f b c D E : M} (hf : f !: b ↔ c)
    (hr : IsSetRestrictedTo (fun s ↦ f !∘ s) D) (hD : ∀ s ∈ D, s !: dom s → b)
    (hE : ∀ t ∈ E, t !: dom t → c) (hDE : ∀ s ∈ D, f !∘ s ∈ E)
    (hED : ∀ t ∈ E, f⁻¹ !∘ t ∈ D) : MemStructure.compLeft f D !: D ↔ E := by
  have hinj := hf.isInjectionFromTo.compLeft hr hD hDE
  refine ⟨hinj, (isSurjectionFromTo_iff_of_isFunctionFromTo hinj.isFunctionFromTo).mpr
    fun t ht ↦ ⟨_, hED t ht, ?_⟩⟩
  rw [MemStructure.compLeft, val_toSetRestrictedTo hr (hED t ht), ← comp_assoc, hf.comp_inv,
    (hE t ht).isFunction.id_comp (hE t ht).ran_subset]

end CompLeft

section Lambda

/-! ### `Δ₀` base cases for lambda notation -/

variable [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [RudClosed M]

/-- `IsFunction` is `Δ₀` -/
instance : Multiclass.DeltaZero (fun ys : Fin 1 → M ↦ IsFunction (ys 0)) Set.univ := by
  have h : (fun ys : Fin 1 → M ↦ IsFunction (ys 0)) =
      ((ᵣ0 : L.RudimentaryTerm 1).isFunction.toBoundedFormula.multiclass : Multiclass M 1) := by
    funext ys
    simp
  rw [h]
  infer_instance

/-- `IsFunctionFromTo` is `Δ₀` -/
instance : Multiclass.DeltaZero
    (fun ys : Fin 3 → M ↦ IsFunctionFromTo (ys 0) (ys 1) (ys 2)) Set.univ := by
  have h : (fun ys : Fin 3 → M ↦ IsFunctionFromTo (ys 0) (ys 1) (ys 2)) =
      ((ᵣ0 : L.RudimentaryTerm 3).isFunctionFromTo (ᵣ1) (ᵣ2)).toBoundedFormula.multiclass := by
    funext ys
    simp
  rw [h]
  infer_instance

/-- `IsInjectionFromTo` is `Δ₀` -/
instance : Multiclass.DeltaZero
    (fun ys : Fin 3 → M ↦ IsInjectionFromTo (ys 0) (ys 1) (ys 2)) Set.univ := by
  have h : (fun ys : Fin 3 → M ↦ IsInjectionFromTo (ys 0) (ys 1) (ys 2)) =
      ((ᵣ0 : L.RudimentaryTerm 3).isInjectionFromTo (ᵣ1) (ᵣ2)).toBoundedFormula.multiclass := by
    funext ys
    simp
  rw [h]
  infer_instance

/-- `IsSurjectionFromTo` is `Δ₀` -/
instance : Multiclass.DeltaZero
    (fun ys : Fin 3 → M ↦ IsSurjectionFromTo (ys 0) (ys 1) (ys 2)) Set.univ := by
  have h : (fun ys : Fin 3 → M ↦ IsSurjectionFromTo (ys 0) (ys 1) (ys 2)) =
      ((ᵣ0 : L.RudimentaryTerm 3).isSurjectionFromTo (ᵣ1) (ᵣ2)).toBoundedFormula.multiclass := by
    funext ys
    simp
  rw [h]
  infer_instance

/-- `IsBijectionFromTo` is `Δ₀` -/
instance : Multiclass.DeltaZero
    (fun ys : Fin 3 → M ↦ IsBijectionFromTo (ys 0) (ys 1) (ys 2)) Set.univ := by
  unfold IsBijectionFromTo
  infer_instance

end Lambda

end FirstOrder.Language.MemStructure
