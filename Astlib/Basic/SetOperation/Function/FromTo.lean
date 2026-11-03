/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Function.Basic
/-!
# Functions between sets

Functions between sets:

* `f !: a → b`: `f` is a function from `a` into `b`;
* `constFun a c`: the constant function on `a` with value `c`;
* `f !: a ↪ b`, `f !: a ↠ b`, `f !: a ↔ b`: injections, surjections and bijections.
-/

open Fin FirstOrder Language MemStructure RudimentaryTerm DeltaZeroBoundedFormula

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M]

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

end FirstOrder.Language.MemStructure
