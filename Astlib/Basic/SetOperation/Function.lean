/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Relation
/-!
file docstring
-/

namespace FirstOrder.Language.MemStructure

variable {L' : Language} [L'.HasMem] [L'.ExtraConstantsOnly]

section Basic

open RudimentaryTerm Fin

variable {M : MemStructure} [M.L.ExtraConstantsUnaryRelationsOnly] [M.Extensional] [M.RudClosed]

def IsFunction (f : M) :=
  IsRelation f ∧ ∀ ⦃x y₁ y₂ : M⦄, x [f] y₁ → x [f] y₂ → y₁ = y₂

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.isFunction (r : L'.RudimentaryTerm n) :
  L'.DeltaZeroBoundedFormula n :=
  ((ᵣ0).isRelation ⊓ ∀₀∈ &0 ∀₀∈ &0
    ((&0 =₀ &1).substBoundRud ![(ᵣ1).left, (ᵣ2).left] ⟹
    (&0 =₀ &1).substBoundRud ![(ᵣ1).right, (ᵣ2).right])) |>.substBoundRud ![r]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isFunction
    (r : M.L'.RudimentaryTerm n) (xs : Fin n → M) :
    r.isFunction.castLHom.toBoundedFormula 〘xs〙 ↔ IsFunction (r.castLHom〘xs〙) := by
  suffices IsRelation r.castLHom〘xs〙 →
      ((∀ a ∈ r.castLHom〘xs〙,
        ∀ a_2 ∈ r.castLHom〘xs〙,
        (ᵣ1).left.castLHom〘snoc (snoc (fun i ↦ r.castLHom〘xs〙) a) a_2〙 =
            (ᵣ2).left.castLHom〘snoc (snoc (fun i ↦ r.castLHom〘xs〙) a) a_2〙 →
          (ᵣ1).right.castLHom〘snoc (snoc (fun i ↦ r.castLHom〘xs〙) a) a_2〙 =
            (ᵣ2).right.castLHom〘snoc (snoc (fun i ↦ r.castLHom〘xs〙) a) a_2〙) ↔
        ∀ ⦃x y₁ y₂ : ↑M⦄, !(x, y₁) ∈ r.castLHom〘xs〙 → !(x, y₂) ∈ r.castLHom〘xs〙 → y₁ = y₂) by
    simpa [isFunction, IsFunction, snoc_nat]
  intro hr
  constructor
  · intro h x y₁ y₂ hxy₁ hxy₂
    convert h !(x, y₁) hxy₁ !(x, y₂) hxy₂ ?_
    · symm
      convert realize_right _ (x := x) (y := y₁)
      simp [snoc_nat]
    · symm
      convert realize_right _ (x := x) (y := y₂)
      simp [snoc_nat]
    · trans x
      · convert realize_left _ (x := x) (y := y₁)
        simp [snoc_nat]
      · symm
        convert realize_left _ (x := x) (y := y₂)
        simp [snoc_nat]
  · intro h z₁ hz₁ z₂ hz₂ hz₁₂
    obtain ⟨x, y₁, rfl⟩ := hr hz₁
    obtain ⟨x', y₂, rfl⟩ := hr hz₂
    have hxx' : x = x' := by
      convert hz₁₂
      · symm
        convert realize_left _ (x := x) (y := y₁)
        simp [snoc_nat]
      · symm
        convert realize_left _ (x := x') (y := y₂)
        simp [snoc_nat]
    subst hxx'
    convert h hz₁ hz₂
    · convert realize_right _ (x := x) (y := y₁)
      simp [snoc_nat]
    · convert realize_right _ (x := x) (y := y₂)
      simp [snoc_nat]

@[simp, grind .]
theorem IsFunction.isRelation {f : M} (hf : IsFunction f) : IsRelation f := hf.left

@[grind .]
theorem IsFunction.eq
    {f x y₁ y₂: M} (hf : IsFunction f) (h₁ : x [f] y₁) (h₂ : x [f] y₂) : y₁ = y₂ := by
  grind [IsFunction]

-- variable [M.Extensional] [M.RudClosed] [M.L.ExtraConstantsUnaryRelationsOnly]

@[simp, grind .]
theorem isFunction_empty : IsFunction (∅ : M) := by
  simp [IsFunction]

@[simp, grind .]
theorem IsFunction.subset {f g : M} (hf : IsFunction f) (hgf : g ⊆ f) :
    IsFunction g := by
  simp only [IsFunction, hf.isRelation.subset hgf, true_and]
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


noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.val
    (r s : L'.RudimentaryTerm n) : L'.RudimentaryTerm n :=
  (ᵣ0).iUnion ((ᵣ2).right.ifTrue
    ((ᵣ2).isOrderedPair ⊓ (&0 =₀ &1).substBoundRud ![(ᵣ2).left, ᵣ1]))
    |>.substBoundRud ![r, s]

noncomputable def val (f a : M) := ((ᵣ0).val (ᵣ1)).castLHom 〘f, a〙₂

infix:88 " ﹫ " => FirstOrder.Language.MemStructure.val

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_val
    (r s : M.L'.RudimentaryTerm n) (xs : Fin n → M) :
    (r.val s).castLHom〘xs〙 = r.castLHom〘xs〙 ﹫ s.castLHom〘xs〙 := by
  simp only [RudimentaryTerm.val, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    castLHom_substBoundRud, castLHom_iUnion, castLHom_var, castLHom_ifTrue,
    DeltaZeroBoundedFormula.castLHom_inf, realize_substBoundRud, val]
  congr
  ext i; fin_cases i <;> simp

-- @[simp]
theorem IsFunction.rel_iff_val_eq
    {f x y : M} (hf : IsFunction f) (hx : x ∈ dom f) : x [f] y ↔ f ﹫ x = y := by
  rw [mem_dom_iff] at hx
  obtain ⟨y₀, hy₀⟩ := hx
  suffices f ﹫ x = y₀ by grind
  simp only [val, Nat.succ_eq_add_one, Nat.reduceAdd, RudimentaryTerm.val, isValue,
    Function.comp_apply, castLHom_substBoundRud, castLHom_iUnion, castLHom_var, castLHom_ifTrue,
    DeltaZeroBoundedFormula.castLHom_inf, realize_substBoundRud]
  ext z
  simp only [isValue, mem_realize_iUnion_iff, realize_basic, Matrix.cons_val_zero, castLHom_var,
    Nat.reduceAdd, mem_realize_ifTrue_iff, DeltaZeroBoundedFormula.toBoundedFormula_inf,
    BoundedFormula.realize'_inf, realize_isOrderedPair,
    DeltaZeroBoundedFormula.realize_substBoundRud, DeltaZeroBoundedFormula.castLHom_bdEqual,
    Term.castLHom_var', Function.comp_apply, DeltaZeroBoundedFormula.toBoundedFormula.eq_2,
    BoundedFormula.realize'_bdEqual, Term.realize'_var', Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  constructor
  · intro ⟨w, hw₁, hw₂, ⟨x', y', hx'y'⟩, hw₃⟩
    convert hw₂
    symm
    convert realize_right _ (x := x) (y := y₀)
    simp only [isValue, snoc_nat, Nat.reduceAdd, coe_ofNat_eq_mod, Nat.mod_succ, lt_self_iff_false,
      ↓reduceDIte, castLHom_var, realize_basic] at hx'y' ⊢
    subst hx'y'
    suffices x' = x by grind
    convert hw₃
    · symm
      convert realize_left _ (x := x') (y := y')
      simp [snoc_nat]
    · simp [snoc_nat]
  · intro hz
    use !(x, y₀), hy₀
    simp only [isValue, IsOrderedPair, snoc_nat, coe_ofNat_eq_mod, Nat.mod_succ, lt_self_iff_false,
      ↓reduceDIte, orderedPair_eq_orderedPair_iff, exists_and_left, ↓existsAndEq, and_true,
      exists_eq', Nat.one_mod, Order.lt_two_iff, Std.le_refl, mk_one, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, castLHom_var, realize_basic, true_and]
    constructor
    · convert hz
      convert realize_right _ (x := x) (y := y₀)
      simp [snoc_nat]
    · convert realize_left _ (x := x) (y := y₀)
      simp [snoc_nat]

@[simp, grind! .]
theorem IsFunction.val_eq_of_rel
    {f x y : M} (hf : IsFunction f) (hxy : x [f] y) : f ﹫ x = y := by
  rwa [hf.rel_iff_val_eq] at hxy
  rw [mem_dom_iff]
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
    (h : ∀ x ∈ dom f, f ﹫ x = g ﹫ x) : f = g :=
  eq_of_subset_of_subset (hf.subset_iff.mpr (by grind)) (hg.subset_iff.mpr (by grind))

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
  rw [M.mem_ran_iff]
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
  rw [mem_union_iff] at h₁ h₂
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · grind
    · grind [hfg (x := x) (by grind)]
  · rcases h₂ with h₂ | h₂
    · grind [hfg (x := x) (by grind)]
    · grind

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

variable {M : MemStructure}

variable [M.Extensional] [M.RudClosed] [M.L.ExtraConstantsUnaryRelationsOnly]

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
  rw [hg.mem_dom_iff, hf.mem_dom_iff, mem_dom_iff]
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

variable {M : MemStructure}

variable [M.Extensional] [M.RudClosed] [M.L.ExtraConstantsUnaryRelationsOnly]

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

variable {M : MemStructure}
  [M.Extensional] [M.RudClosed] [M.L.ExtraConstantsUnaryRelationsOnly]

def IsFunctionFromTo (f a b : M) := IsFunction f ∧ dom f = a ∧ ran f ⊆ b

notation:50 f " !: " a:50 " → " b:50 => IsFunctionFromTo f a b

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

end IsFunctionFromTo

section IsInjectionFromTo

variable {M : MemStructure}
  [M.Extensional] [M.RudClosed] [M.L.ExtraConstantsUnaryRelationsOnly]

def IsInjectionFromTo (f a b : M) :=
    f !: a → b ∧ ∀ ⦃x y⦄, x ∈ a → y ∈ a → f ﹫ x = f ﹫ y → x = y

notation:50 f " !: " a:50 " ↪ " b:50 => IsInjectionFromTo f a b

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

end IsInjectionFromTo

section IsSurjectionFromTo

variable {M : MemStructure}
  [M.Extensional] [M.RudClosed] [M.L.ExtraConstantsUnaryRelationsOnly]

def IsSurjectionFromTo (f a b : M) := f !: a → b ∧ ran f = b

notation:50 f " !: " a:50 " ↠ " b:50 => IsSurjectionFromTo f a b

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
  rw [IsSurjectionFromTo]
  grind

@[simp, grind .]
theorem isSurjectionFromTo_of_comp_id {f g a b : M} (hf : f !: a → b)
    (hg : g !: b → a) (hfg : f !∘ g = id b) : f !: a ↠ b := by
  grind [IsSurjectionFromTo]

-- theorem IsInjective.isSurjective_inv_dom [M.ClosedUnderSProd] {f : M} (hf : IsInjective f) :
    -- IsSurjective f⁻¹ (dom f) := by
  -- grind [IsSurjective, isInjective_iff_isFunction_inv, ran_inv]

end IsSurjectionFromTo

section IsBijectionFromTo

variable {M : MemStructure}
  [M.Extensional] [M.RudClosed] [M.L.ExtraConstantsUnaryRelationsOnly]

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
    grind [(h (f ﹫ x₁) (by grind)).unique (y₁ := x₁) (y₂ := x₂)]
  · rw [isSurjectionFromTo_iff_of_isFunctionFromTo hf]
    exact fun y a ↦ (h y a).exists

theorem IsBijectionFromTo.comp {f g a b c : M} (hf : f !: b ↔ c)
    (hg : g !: a ↔ b) : f !∘ g !: a ↔ c := by
  grind [IsBijectionFromTo]

theorem IsBijectionFromTo.inv
    {f a b : M} (hf : f !: a ↔ b) :
    f⁻¹ !: b ↔ a := by
  rw [isBijectionFromTo_iff]
  have := hf.dom_eq
  have := hf.ran_eq
  have hf₁ : IsFunction f⁻¹ := by
    refine ⟨by grind, fun y x₁ x₂ h₁ h₂ ↦ ?_⟩
    apply hf.isInjectionFromTo.eq (x := x₁) (x' := x₂) <;> grind
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
  rw [IsFunction.ext (f := f⁻¹ !∘ f) (g := id a)]
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

end IsBijectionFromTo


section Restrict

variable {M : MemStructure}
  [M.Extensional] [M.RudClosed] [M.L.ExtraConstantsUnaryRelationsOnly]

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.restrict
    (r s : L'.RudimentaryTerm n) : L'.RudimentaryTerm n :=
  r ∩ (s ×ˢ r.ran)

infix:88 " ↾ " => FirstOrder.Language.RudimentaryTerm.restrict

noncomputable def restrict (f a : M) := ((ᵣ0).restrict (ᵣ1)).castLHom 〘f, a〙₂
-- noncomputable def restrict (f a : M) := (∃'∈ &0 (&2).eqLeft &1) 〘a, ∈ f〙₀

infix:88 " ↾ " => FirstOrder.Language.MemStructure.restrict

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_restrict
    (r s : M.L'.RudimentaryTerm n) (xs : Fin n → M) :
    (r ↾ s).castLHom〘xs〙 = r.castLHom〘xs〙 ↾ s.castLHom〘xs〙:= by
  simp [restrict, RudimentaryTerm.restrict]

theorem restrict_eq (f a : M) :
    f ↾ a = f ∩ (a ×ˢ ran f) := by
  simp [restrict, RudimentaryTerm.restrict]
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
  rw [mem_inter_iff]
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

end Restrict


section Image

variable {M : MemStructure}
  [M.Extensional] [M.RudClosed] [M.L.ExtraConstantsUnaryRelationsOnly]

noncomputable def image (f a : M) := ran (f ↾ a)

infix:88 " '' " => FirstOrder.Language.MemStructure.image

@[simp, grind =]
theorem image_empty (f : M) : f '' ∅ = ∅ := by
  grind [image]

@[simp, grind =]
theorem image_dom (f : M) : f '' (dom f) = ran f := by
  ext; grind [image, mem_restrict_iff]

theorem image_union (f a b : M) : f '' (a ∪ b) = f '' a ∪ f '' b := by
  grind [image, restrict_union, ran_union]

theorem mem_image_sUnion_iff (f X z : M) :
    z ∈ f '' (⋃₀ X) ↔ ∃ a ∈ X, z ∈ f '' a := by
  grind [image, restrict_sUnion]

end Image

end FirstOrder.Language.MemStructure
