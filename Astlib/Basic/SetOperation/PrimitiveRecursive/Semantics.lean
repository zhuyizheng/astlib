/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.PrimitiveRecursive.Syntax
import Astlib.Basic.SetOperation.Rudimentary.Semantics
import Astlib.Basic.SetOperation.Multiclass.Levy
import Astlib.Basic.SetOperation.Function
import Astlib.Basic.SetOperation.Foundational
import Astlib.Basic.Ordinal.Transitive
import Astlib.Basic.Axiom.KP.SigmaOneBoundedFormula.Semantics
/-!
file docstring
-/
open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula PrimitiveRecursiveTerm Fin MemStructure

variable {L : FirstOrder.Language.{u, v}} {M : Type max u v} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M]

namespace FirstOrder.Language

namespace MemStructure

def IsSetRestrictedTo (G : ClassFunction M) (x : M) :=
  ∃ f : M, IsFunction f ∧ dom f = x ∧ ∀ y ∈ x, f ﹫ y = G y

noncomputable instance (G : ClassFunction M) : Decidable (IsSetRestrictedTo G x) :=
  Classical.propDecidable _

noncomputable def toSetRestrictedTo (G : ClassFunction M) (x : M) :=
  dite (IsSetRestrictedTo G x) Classical.choose default

infix:88 " ↾₀ " => FirstOrder.Language.MemStructure.toSetRestrictedTo

theorem toSetRestrictedTo_aux {G : ClassFunction M} {x : M}
    (h : IsSetRestrictedTo G x) :
    IsFunction (G ↾₀ x) ∧ dom (G ↾₀ x) = x ∧ ∀ y ∈ x, (G ↾₀ x) ﹫ y = G y := by
  simp only [toSetRestrictedTo] at h ⊢
  convert Classical.choose_spec h <;> simp [h]

@[simp]
theorem isFunction_toSetRestrictedTo {G : ClassFunction M} {x : M}
    (h : IsSetRestrictedTo G x) :
    IsFunction (G ↾₀ x) :=
  toSetRestrictedTo_aux h |>.left

@[simp]
theorem dom_toSetRestrictedTo {G : ClassFunction M} {x : M}
    (h : IsSetRestrictedTo G x) :
    dom (G ↾₀ x) = x :=
  toSetRestrictedTo_aux h |>.right.left

@[simp]
theorem val_toSetRestrictedTo {G : ClassFunction M} {x y : M}
    (h : IsSetRestrictedTo G x) (hy : y ∈ x) :
    (G ↾₀ x) ﹫ y = G y :=
  toSetRestrictedTo_aux h |>.right.right y hy

/-- The restriction of `G` to `x` is the unique function on `x` agreeing with `G` -/
theorem toSetRestrictedTo_eq [Extensional M] [RudClosed M] {G : ClassFunction M} {x f : M}
    (hf : IsFunction f) (hdom : dom f = x) (hval : ∀ y ∈ x, f ﹫ y = G y) : G ↾₀ x = f := by
  have h : IsSetRestrictedTo G x := ⟨f, hf, hdom, hval⟩
  grind [dom_toSetRestrictedTo, val_toSetRestrictedTo, isFunction_toSetRestrictedTo]

def IsRecursion (F G : ClassFunction M) :=
  (∀ x, IsSetRestrictedTo F x) ∧ ∀ x, F x = G (F ↾₀ x)

noncomputable instance : Decidable (∃ F : ClassFunction M, IsRecursion F G) :=
  Classical.propDecidable _

noncomputable def recursion (G : ClassFunction M) : ClassFunction M :=
  dite (∃ F, IsRecursion F G) Classical.choose fun _ _ ↦ default

theorem exists_min_classFunction_ne_of_mem_transitive [Extensional M] [RudClosed M] [Foundational M]
    {F G : ClassFunction M} {x y : M} (hFGx : F x ≠ G x) (hxy : x ∈ y) (hy : Transitive y)
    (hF : ∀ y, IsSetRestrictedTo F y) (hG : ∀ y, IsSetRestrictedTo G y) :
    ∃ x, (F x ≠ G x ∧ F ↾₀ x = G ↾₀ x) := by
  let A : Class M := fun x ↦ F x ≠ G x
  let B : Class M :=
    ((∼(&0 =₀ &1) : L.DeltaZeroBoundedFormula 2).substBoundRud ![ᵣ1 ﹫ ᵣ0,
    ᵣ2 ﹫ ᵣ0] : L.DeltaZeroBoundedFormula 3).toBoundedFormula.multiclass.slice ![F ↾₀ y, G ↾₀ y]
  have hB : IsComprehension (y ∩₀ B) y A := by
    intro z
    simp only [mem_comprehension_iff, B, A, and_congr_right_iff]
    intro hz
    simp [hF, hG, hz, append_left_eq_cons]
  have : HasComprehension y A := ⟨y ∩₀ B, hB⟩
  obtain ⟨x', hx'₁, hx'₂⟩ := exists_min_class_of_mem_transitive (A := A) hFGx hxy hy
  refine ⟨x', hx'₁, ?_⟩
  exact toSetRestrictedTo_eq (by simp [hG]) (by simp [hG]) (by grind [val_toSetRestrictedTo])

theorem eq_of_isRecursion [Extensional M] [RudClosed M] [Foundational M]
    (hM : ∀ x : M, ∃ y : M, x ∈ y ∧ Transitive y)
    {F₁ F₂ G : ClassFunction M} (h₁ : IsRecursion F₁ G)
    (h₂ : IsRecursion F₂ G) : F₁ = F₂ := by
  funext x
  by_contra!
  obtain ⟨y, hy₁, hy₂⟩ := hM x
  have := exists_min_classFunction_ne_of_mem_transitive this hy₁ hy₂ h₁.left h₂.left
  grind [h₁.right, h₂.right]

/-- A class function defined by recursion from `G` is `recursion G` -/
theorem IsRecursion.eq_recursion [Extensional M] [RudClosed M] [Foundational M]
    (hM : ∀ x : M, ∃ y : M, x ∈ y ∧ Transitive y)
    {F G : ClassFunction M} (hFG : IsRecursion F G) : F = recursion G := by
  have h : ∃ F, IsRecursion F G := ⟨F, hFG⟩
  simp only [recursion, h]
  exact eq_of_isRecursion hM hFG (Classical.choose_spec h)

/-- The recursive definition `recursion G x = G (recursion G ↾₀ x)`, provided that some class
function is defined by recursion from `G` -/
theorem recursion_eq [Extensional M] [RudClosed M] [Foundational M]
    (hM : ∀ x : M, ∃ y : M, x ∈ y ∧ Transitive y)
    {G : ClassFunction M} (h : ∃ F, IsRecursion F G) (x : M) :
    recursion G x = G (recursion G ↾₀ x) := by
  obtain ⟨F, hF⟩ := h
  rw [← hF.eq_recursion hM]
  exact hF.right x

theorem isIUnion_sUnion_ran [ModelsKP M] {f : M} (hf : IsFunction f) {F : ClassFunction M}
    (h : ∀ y ∈ dom f, f ﹫ y = F y) : IsIUnion (⋃₀ ran f) (dom f) F := by
  grind [IsIUnion]

/-- A `Σ₁` class function restricts to a set function on every set. -/
theorem isSetRestrictedTo_of_modelsKP [ModelsKP M] (G : ClassFunction M)
    [hG : G.Sigma 1 Set.univ] (a : M) : IsSetRestrictedTo G a := by
  -- `F ![u, w]` says `w = (u, G u)`
  let F : Multiclass M 2 := ((G : Multiclass M 2).remap ![0, 2] ⊓
    ((&1 : L.Term' 3).eqOrderedPair &0 &2).toBoundedFormula.multiclass).ex
  have hF (u w : M) : F ![u, w] ↔ w = !(u, G u) := by
    simp only [F, Multiclass.ex_iff, Multiclass.inf_iff, Multiclass.remap, Matrix.comp_vecCons,
      Matrix.empty_eq (_ ∘ ![])]
    simp
  have hFa₁ :  ∀ (z : M), z ∈ F ''₀ a ↔ ∃ u ∈ a, F ![u, z] :=
    mem_replacement_iff (F := F) (a := a) fun u _ ↦ ⟨!(u, G u), by grind, by grind⟩
  have hFa₂ : IsFunction (F ''₀ a) := by grind [IsFunction]
  refine ⟨F ''₀ a, hFa₂, ?_, fun y hy ↦ hFa₂.val_eq_of_rel (by grind)⟩
  ext
  simp [mem_dom_iff, hFa₁, hF]

/-- `f` is an approximation of the class function defined by recursion from `G`: a function
with a transitive domain satisfying the recursive definition -/
def IsApprox (f : M) (G : ClassFunction M) : Prop :=
  IsFunction f ∧ Transitive (dom f) ∧ ∀ y ∈ dom f, f ﹫ y = G (f ↾ y)

theorem IsApprox.isFunction {G : ClassFunction M} {f : M} (hf : IsApprox f G) : IsFunction f :=
  hf.left

theorem IsApprox.transitiveDom {G : ClassFunction M} {f : M} (hf : IsApprox f G) :
    Transitive (dom f) :=
  hf.right.left

/-- An approximation satisfies the recursive definition -/
theorem IsApprox.val_eq {G : ClassFunction M} {f y : M} (hf : IsApprox f G) (hy : y ∈ dom f) :
    f ﹫ y = G (f ↾ y) :=
  hf.right.right y hy

/-- The approximations of a `Σ₁` class function form a `Σ₁` class in models of `KP` -/
instance [ModelsKP M] (G : ClassFunction M) [G.Sigma 1 Set.univ] :
    Class.Sigma (fun f ↦ IsApprox f G) 1 Set.univ := by
  -- `[f, d, y, r, v]`: `r = f ↾ y`, `v = f ﹫ y` and `G r = v`
  let B : Multiclass M 5 := ((&0 =₀ &1).substBoundRud ![ᵣ3, ᵣ0 ↾ ᵣ2] ⊓
    (&0 =₀ &1).substBoundRud ![ᵣ4, ᵣ0 ﹫ ᵣ2] : L.DeltaZeroBoundedFormula 5).toBoundedFormula.multiclass ⊓
    (G : Multiclass M 2).remap ![3, 4]
  -- `[f, d]`: `d = dom f`, `f` is a function, `d` is transitive and `∀ y ∈ d, f ﹫ y = G (f ↾ y)`
  let C : Multiclass M 2 := ((&0 =₀ &1).substBoundRud ![ᵣ1, (ᵣ0).dom] ⊓ (ᵣ0).isFunction ⊓
    (ᵣ1).isTransitive : L.DeltaZeroBoundedFormula 2).toBoundedFormula.multiclass ⊓ B.ex.ex.allMem 1
  have hC : (fun f ↦ IsApprox f G : Class M) = (C.ex : Class M) := by
    ext f
    simp [B, C, IsApprox, DeltaZeroBoundedFormula.toBoundedFormula, Matrix.empty_eq (_ ∘ ![]),
      eq_comm, and_assoc]
  rw [hC]
  have : C.Sigma 1 Set.univ := inferInstance
  infer_instance

/-- Two approximations agree on their common domain -/
theorem IsApprox.val_eq_val [ModelsKP M] {G : ClassFunction M} {f f' x : M}
    (hf : IsApprox f G) (hf' : IsApprox f' G) (hx : x ∈ dom f) (hx' : x ∈ dom f') :
    f ﹫ x = f' ﹫ x := by
  let A : Multiclass M 1 := (∼((&0 =₀ &1).substBoundRud ![ᵣ0 ﹫ ᵣ2, ᵣ1 ﹫ ᵣ2]) :
    L.DeltaZeroBoundedFormula 3).toBoundedFormula.switchBound.multiclass.slice ![f, f']
  have hA (z : M) : z ∈ (dom f ∩ dom f') ∩₀ A ↔ (z ∈ dom f ∧ z ∈ dom f') ∧ f ﹫ z ≠ f' ﹫ z := by
    simp [A, append_right_eq_snoc]
  by_contra hne
  -- take a `∈`-minimal point `z` where `f` and `f'` differ
  have hA₀ : (dom f ∩ dom f') ∩₀ A ≠ ∅ := by
    rw [ne_empty_iff]
    exact ⟨x, by simp [hA, hx, hx', hne]⟩
  obtain ⟨z, hz, hzmin⟩ := Foundational.hasMemMin _ hA₀
  rw [hA] at hz
  obtain ⟨⟨hz₁, hz₂⟩, hz₃⟩ := hz
  apply hz₃
  simp only [hf.val_eq, hz₁, hf'.val_eq, hz₂]
  congr 1
  apply hf.isFunction.restrict_eq_restrict hf'.isFunction (hf.transitiveDom z hz₁)
    (hf'.transitiveDom z hz₂)
  convert hzmin with w hw
  simp [hA, hf.transitiveDom z hz₁ hw, hf'.transitiveDom z hz₂ hw]

/-- An approximation can be extended by a point which is a subset of the domain of the
approximation -/
theorem IsApprox.exists_extend [ModelsKP M] {G : ClassFunction M} {h x : M}
    (hh : IsApprox h G) (hx : x ⊆ dom h) :
    ∃ g, IsApprox g G ∧ x ∈ dom g ∧ dom h ⊆ dom g := by
  by_cases hxh : x ∈ dom h
  · grind
  let g := h ∪ {!(x, G (h ↾ x))}
  have hg (a b : M) : !(a, b) ∈ g ↔ !(a, b) ∈ h ∨ (a = x ∧ b = G (h ↾ x)) := by
    simp [g]
  have hgfun : IsFunction g := ⟨by grind [hh.isFunction], by grind [hh.isFunction.eq]⟩
  have hgdom (a : M) : a ∈ dom g ↔ a ∈ dom h ∨ a = x := by
    simp only [mem_dom_iff, hg]
    grind
  have hgval (z : M) (hz : z ∈ dom h) : g ﹫ z = h ﹫ z := by grind [rel_val, IsApprox]
  have hgx : g ﹫ x = G (h ↾ x) := by grind
  have hgres (z : M) (hz : z ⊆ dom h) : g ↾ z = h ↾ z := by
    apply hgfun.restrict_eq_restrict hh.isFunction _ hz <;> grind
  exact ⟨g, ⟨hgfun, by grind [Transitive, IsApprox], by grind [IsApprox]⟩, by grind, by grind⟩

/-- The existence of approximations for a `Σ₁` class function `G` -/
theorem exists_isApprox [ModelsKP M] {G : ClassFunction M} [G.Sigma 1 Set.univ] (x : M) :
    ∃ f, IsApprox f G ∧ x ∈ dom f := by
  -- `F ![y, f]`: `f` is an approximation defined at `y`
  let Ap : Class M := fun f ↦ IsApprox f G
  have : Ap.Sigma 1 Set.univ := by infer_instance
  let F : Multiclass M 2 := (Ap : Multiclass M 1).remap ![1] ⊓
    ((&0 ∈₀ &1).substBoundRud ![ᵣ0, (ᵣ1).dom] :
      L.DeltaZeroBoundedFormula 2).toBoundedFormula.multiclass
  have hF (y f : M) : F ![y, f] ↔ IsApprox f G ∧ y ∈ dom f := by
    simp only [F, Multiclass.inf_iff, Multiclass.remap, Matrix.comp_vecCons,
      Matrix.empty_eq (_ ∘ ![]), Class.toMulticlass_iff]
    simp [Ap, DeltaZeroBoundedFormula.toBoundedFormula]
  have hFex (x : M) : (F.ex : Class M) x ↔ ∃ f, IsApprox f G ∧ x ∈ dom f := by
    simp [Multiclass.toClass_iff, hF]
  have : (F.ex : Multiclass M 1).Definable Set.univ := by infer_instance
  rw [← hFex]
  refine induction_of_modelsKP (fun x ih ↦ ?_) x
  simp only [hFex] at ih ⊢
  -- collect approximations defined at the elements of `x`
  obtain ⟨B, hB₁, hB₂⟩ := exists_strong_collection_of_modelsKP F x (by simpa [hF] using ih)
  simp only [hF] at hB₁ hB₂
  -- any two approximations agree, so `⋃₀ B` is an approximation extending each member of `B`
  have hfun : IsFunction (⋃₀ B) := by
    refine ⟨fun z hz ↦ ?_, fun a b₁ b₂ h₁ h₂ ↦ ?_⟩
    · rw [mem_sUnion_iff] at hz
      obtain ⟨f, hf, hz⟩ := hz
      obtain ⟨_, -, hfB, -⟩ := hB₂ f hf
      exact hfB.isFunction.isRelation hz
    · rw [mem_sUnion_iff] at h₁ h₂
      obtain ⟨f₁, hf₁, h₁⟩ := h₁
      obtain ⟨f₂, hf₂, h₂⟩ := h₂
      obtain ⟨_, -, hfB₁, -⟩ := hB₂ f₁ hf₁
      obtain ⟨_, -, hfB₂, -⟩ := hB₂ f₂ hf₂
      rw [← hfB₁.isFunction.val_eq_of_rel h₁, ← hfB₂.isFunction.val_eq_of_rel h₂]
      exact hfB₁.val_eq_val hfB₂ (by grind) (by grind)
  have hval (f : M) (hf : f ∈ B) (z : M) (hz : z ∈ dom f) : (⋃₀ B) ﹫ z = f ﹫ z := by
    obtain ⟨_, -, hfB, -⟩ := hB₂ f hf
    grind [rel_val, IsApprox.isFunction]
  have hdom (z : M) : z ∈ dom (⋃₀ B) ↔ ∃ f ∈ B, z ∈ dom f := by grind
  have happ : IsApprox (⋃₀ B) G := by
    refine ⟨hfun, fun z hz w hw ↦ ?_, fun z hz ↦ ?_⟩
    · rw [hdom] at hz
      obtain ⟨f, hf, hzf⟩ := hz
      obtain ⟨_, -, hfB, -⟩ := hB₂ f hf
      rw [hdom]
      exact ⟨f, hf, hfB.transitiveDom z hzf hw⟩
    · rw [hdom] at hz
      obtain ⟨f, hf, hzf⟩ := hz
      obtain ⟨_, -, hfB, -⟩ := hB₂ f hf
      rw [hval f hf z hzf, hfB.val_eq hzf]
      congr 1
      apply hfB.isFunction.restrict_eq_restrict hfun (hfB.transitiveDom z hzf) <;>
        grind [IsApprox.transitiveDom, Transitive]
  obtain ⟨g, hg, hxg, -⟩ := happ.exists_extend (x := x) (by grind)
  exact ⟨g, hg, hxg⟩

/-- Choosing an approximation defined at each point gives a class function defined by
recursion from `G`. -/
theorem isRecursion_of_isApprox [ModelsKP M] {G F : ClassFunction M}
    (hF₁ : ∀ x, IsApprox (F x) G) (hF₂ : ∀ x, x ∈ dom (F x)) :
    IsRecursion (fun x ↦ F x ﹫ x) G := by
  -- `F x ↾ x` is the restriction of `fun y ↦ F y ﹫ y` to `x`
  have hsub (x : M) : x ⊆ dom (F x) := by grind [IsApprox, Transitive]
  have hval (x y : M) (hy : y ∈ x) : (F x ↾ x) ﹫ y = F y ﹫ y := by
    grind [IsApprox, IsApprox.val_eq_val]
  have hdom (x : M) : dom (F x ↾ x) = x := by simp [(hF₁ x).isFunction, hsub]
  refine ⟨fun x ↦ ⟨F x ↾ x, by simp [(hF₁ x).isFunction], hdom x, hval x⟩, fun x ↦ ?_⟩
  simp only [(hF₁ x).val_eq (hF₂ x)]
  rw [toSetRestrictedTo_eq (by simp [(hF₁ x).isFunction]) (hdom x) (hval x)]

/-- The `Σ`-recursion theorem: a `Σ₁` class function `G` admits a class function defined by
recursion from it -/
theorem exists_isRecursion [ModelsKP M] {G : ClassFunction M} [G.Sigma 1 Set.univ] :
    ∃ F, IsRecursion F G := by
  choose F hF₁ hF₂ using exists_isApprox (G := G)
  exact ⟨fun x ↦ F x ﹫ x, isRecursion_of_isApprox hF₁ hF₂⟩

/-- `recursion G` agrees with every approximation, assuming that `G` is `Σ₁` -/
theorem IsApprox.recursion_eq [ModelsKP M] {G : ClassFunction M} [G.Sigma 1 Set.univ]
    {f x : M} (hf : IsApprox f G) (hx : x ∈ dom f) : recursion G x = f ﹫ x := by
  choose F hF₁ hF₂ using exists_isApprox (G := G)
  rw [← (isRecursion_of_isApprox hF₁ hF₂).eq_recursion exists_mem_transitive_of_modelsKP]
  grind [IsApprox.val_eq_val]

/-- The recursive definition `recursion G x = G (recursion G ↾₀ x)` for a `Σ₁` class function `G`
in models of `KP` -/
theorem recursion_eq_of_modelsKP [ModelsKP M] {G : ClassFunction M} [G.Sigma 1 Set.univ]
    (x : M) : recursion G x = G (recursion G ↾₀ x) :=
  recursion_eq exists_mem_transitive_of_modelsKP exists_isRecursion x

end MemStructure

namespace PrimitiveRecursiveTerm

-- variable {L : FirstOrder.Language.{u, v}} [L.HasMem]


noncomputable def realize {n : ℕ} (r : L.PrimitiveRecursiveTerm n) : MulticlassFunction M n :=
  match r with
  | var i => fun xs ↦ xs i
  | const c => fun _ ↦ ↑c
  | unorderedPair r₁ r₂ => fun xs ↦ MemStructure.unorderedPair (r₁.realize xs) (r₂.realize xs)
  | sdiff r₁ r₂ => fun xs ↦ MemStructure.sdiff (r₁.realize xs) (r₂.realize xs)
  | iUnion ri rf => fun xs ↦ MemStructure.iUnion (ri.realize xs) (fun y ↦ rf.realize (snoc xs y))
  | char R r => fun xs ↦ if Structure.RelMap R ![r.realize xs] then MemStructure.unorderedPair ∅ ∅ else ∅
  | recursion rg =>
    fun xs ↦ MemStructure.recursion (fun y ↦ rg.realize (snoc (xs ∘ castSucc) y)) (xs (last _))

scoped[FirstOrder.Language] notation:max (name := primitiveRecursiveTermRealize)
  r "〘" xs "〙" => PrimitiveRecursiveTerm.realize r xs

scoped[FirstOrder.Language] notation:max (name := primitiveRecursiveTermRealize₁)
  r "〘" x "〙₁" => PrimitiveRecursiveTerm.realize r ![x]

scoped[FirstOrder.Language] notation:max (name := primitiveRecursiveTermRealize₂)
  r "〘" x ", " y "〙₂" => PrimitiveRecursiveTerm.realize r ![x, y]

scoped[FirstOrder.Language] notation:max (name := primitiveRecursiveTermRealize₃)
  r "〘" x ", " y ", " z "〙₃" => PrimitiveRecursiveTerm.realize r ![x, y, z]


variable {n : ℕ} (r₁ r₂ r ri : L.PrimitiveRecursiveTerm n) (rf rg : L.PrimitiveRecursiveTerm (n + 1))
  (xs : Fin n → M)

@[simp, grind =]
theorem realize_basic (i : Fin n) : (ₚᵣi)〘xs〙 = xs i := by
  simp [realize]

@[simp, grind =]
theorem realize_const (c : L.Functions 0) :
    (const c)〘xs〙 = ↑c := by
  simp [realize]

@[simp, grind =]
theorem realize_unorderedPair : ₚᵣ{r₁, r₂}〘xs〙 = MemStructure.unorderedPair (M := M) r₁〘xs〙 r₂〘xs〙 := by
  simp [realize]

@[simp, grind =]
theorem realize_sdiff' : (r₁.sdiff r₂)〘xs〙 = r₁〘xs〙 \ r₂〘xs〙 := by
  simp [realize, SDiff.sdiff]

@[simp, grind =]
theorem realize_sdiff : (r₁ \ r₂)〘xs〙 = r₁〘xs〙 \ r₂〘xs〙 := realize_sdiff' _ _ _

-- @[simp, grind =]
theorem realize_iUnion :
    (ri.iUnion rf)〘xs〙 = MemStructure.iUnion (M := M) ri〘xs〙 fun y ↦ rf〘snoc xs y〙 := by
  simp [realize]

@[simp, grind =]
theorem realize_char :
    (char R r)〘xs〙 = if Structure.RelMap R ![r.realize xs] then MemStructure.unorderedPair (M := M) ∅ ∅ else ∅ := by
  simp [realize]

/-- A rudimentary term has the same meaning as a primitive recursive term -/
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_toPrimitiveRecursiveTerm {n}
    (r : L.RudimentaryTerm n) (xs : Fin n → M) : r.toPrimitiveRecursiveTerm〘xs〙 = r〘xs〙 := by
  induction r with
  | var i => simp [RudimentaryTerm.toPrimitiveRecursiveTerm]
  | const c => simp [RudimentaryTerm.toPrimitiveRecursiveTerm, RudimentaryTerm.realize]
  | unorderedPair r₁ r₂ ih₁ ih₂ =>
    simp [RudimentaryTerm.toPrimitiveRecursiveTerm, RudimentaryTerm.realize, ih₁, ih₂]
  | sdiff r₁ r₂ ih₁ ih₂ =>
    simp [RudimentaryTerm.toPrimitiveRecursiveTerm, RudimentaryTerm.realize, ih₁, ih₂, SDiff.sdiff]
  | iUnion ri rf ihi ihf =>
    simp [RudimentaryTerm.toPrimitiveRecursiveTerm, RudimentaryTerm.realize, realize_iUnion, ihi, ihf]
  | char R r ih =>
    simp [RudimentaryTerm.toPrimitiveRecursiveTerm, RudimentaryTerm.realize, ih]

@[simp]
theorem _root_.FirstOrder.Language.Term.realize_toPrimitiveRecursiveTerm {n} (t : L.Term' n)
    (xs : Fin n → M) : t.toPrimitiveRecursiveTerm〘xs〙 = t〘xs〙 := by
  simp [Term.toPrimitiveRecursiveTerm]


variable {n : ℕ} (x y z a : M)

-- variable [PairClosed M] [SDiffClosed M]

-- @[simp]
theorem mem_realize_iUnion_iff₀
    {n : ℕ} {ri : L.PrimitiveRecursiveTerm n} {rf : L.PrimitiveRecursiveTerm (n + 1)}
    {xs : Fin n → M} (x : M)
    (h : ∃ a, IsIUnion (M := M) a ri〘xs〙 fun y ↦ rf〘snoc xs y〙) :
    x ∈ (ri.iUnion rf)〘xs〙 ↔
      ∃ z ∈ ri〘xs〙, x ∈ rf〘snoc xs z〙 := by
  simp only [MemStructure.iUnion, h, ↓reduceDIte, realize_iUnion]
  rw [Classical.choose_spec h]

theorem realize_recursion₀_of_isRecursion [Extensional M] [RudClosed M] [Foundational M]
    (hM : ∀ x : M, ∃ y : M, x ∈ y ∧ Transitive y)
    {n : ℕ} {rg : L.PrimitiveRecursiveTerm (n + 1)}
    {xs : Fin (n + 1) → M} {F : ClassFunction M}
    (h : IsRecursion (M := M) F (fun y ↦ rg〘snoc (xs ∘ castSucc) y〙)) :
    rg.recursion〘xs〙 = rg〘snoc (xs ∘ castSucc) (F ↾₀ (xs (last _)))〙 := by
  simp [realize, ← h.eq_recursion hM, h.right]


theorem realize_recursion₀_of_exists_isRecursion [Extensional M] [RudClosed M] [Foundational M]
    (hM : ∀ x : M, ∃ y : M, x ∈ y ∧ Transitive y)
    {n : ℕ} {rg : L.PrimitiveRecursiveTerm (n + 1)}
    {xs : Fin (n + 1) → M}
    (h : ∃ F, IsRecursion (M := M) F (fun y ↦ rg〘snoc (xs ∘ castSucc) y〙)) :
    rg.recursion〘xs〙 = rg〘snoc (xs ∘ castSucc) ((fun y ↦ rg.recursion〘snoc (xs ∘ castSucc) y〙) ↾₀ (xs (last _)))〙 := by
  obtain ⟨F, hF⟩ := h
  convert realize_recursion₀_of_isRecursion hM hF
  simp [realize, hF.eq_recursion hM]

section EqRealize

open SigmaOneBoundedFormula

/-- Given the correctness of `rf.eqRealize`, the class function `y ↦ rf(ps, y)` is `Σ₁` -/
theorem sigma_realize [ModelsKP M] {n : ℕ} (rf : L.PrimitiveRecursiveTerm (n + 1))
    (ih : ∀ {m : ℕ} (t : L.Term' m) (ts : Fin (n + 1) → L.Term' m) (xs : Fin m → M),
      (rf.eqRealize t ts).toBoundedFormula〘xs〙 ↔ t〘xs〙 = rf〘fun i ↦ (ts i)〘xs〙〙)
    (ys : Fin n → M) :
    ClassFunction.Sigma (fun y ↦ rf〘snoc ys y〙) 1 Set.univ := by
  let F := (switchBound (p := 2) (rf.eqRealize &-1
    (fun i ↦ &(i.castSucc))).toBoundedFormula).multiclass.slice ys
  refine .of_iff (F := F) fun u w ↦ ?_
  simp [F, ← snoc_snoc_eq_append, ih, eq_comm]

/-- The formula `p.eqRealize t ts` expresses `t = p〘ts〙` in models of `KP`. -/
theorem realize_eqRealize [ModelsKP M] {n : ℕ} (p : L.PrimitiveRecursiveTerm n) {m : ℕ} (t : L.Term' m) (ts : Fin n → L.Term' m) (xs : Fin m → M) :
    (p.eqRealize t ts).toBoundedFormula〘xs〙 ↔ t〘xs〙 = p〘fun i ↦ (ts i)〘xs〙〙 := by
  induction p generalizing m with
  | var i => simp [eqRealize]
  | const c => simp [eqRealize]
  | unorderedPair r₁ r₂ ih₁ ih₂ =>
    simp [eqRealize, ih₁, ih₂]
  | sdiff r₁ r₂ ih₁ ih₂ =>
    simp [eqRealize, ih₁, ih₂]
  | iUnion ri rf ihi ihf =>
    simp only [eqRealize, SigmaOneBoundedFormula.realize_ex, SigmaOneBoundedFormula.realize_inf,
      and_assoc, SigmaOneBoundedFormula.realize_allMem, ihi, ihf, realize_toSigmaOneBoundedFormula,
      toBoundedFormula_inf, realize'_inf, RudimentaryTerm.realize_isFunction,
      DeltaZeroBoundedFormula.realize_substBoundRud, Term.realize'_snoc,
      DeltaZeroBoundedFormula.toBoundedFormula, realize'_bdEqual, Matrix.cons_val_zero,
      Matrix.cons_val_one, Function.comp_apply, Term.realize'_var', Term.realize_toRudimentaryTerm,
      Term.realize'_castAdd, Fin.castAdd_add_one, Fin.castAdd_zero, Fin.cast_refl, id_eq,
      snoc_castSucc, RudimentaryTerm.realize_basic, RudimentaryTerm.dom, RudimentaryTerm.realize_dom₀,
      RudimentaryTerm.val, RudimentaryTerm.realize_substBoundRud, RudimentaryTerm.realize_val₀,
      snoc_last]
    rw [realize_iUnion]
    constructor
    · rintro ⟨a, f, rfl, hf, hdom, hval, ht⟩
      rw [iUnion_eq_of_isIUnion, ht]
      have hI : IsIUnion (⋃₀ ran f) (dom f) fun y ↦ rf〘snoc (fun i ↦ (ts i)〘xs〙) y〙 :=
        isIUnion_sUnion_ran hf (by grind)
      simp [hdom ▸ hI]
    · intro ht
      rw [ht]
      have := sigma_realize rf ihf fun i ↦ (ts i)〘xs〙
      obtain ⟨f, hf, hdom, hval⟩ :=
        isSetRestrictedTo_of_modelsKP (fun y ↦ rf〘snoc (fun i ↦ (ts i)〘xs〙) y〙) ri〘fun i ↦ (ts i)〘xs〙〙
      refine ⟨_, f, rfl, hf, hdom, fun y hy ↦ ⟨_, rfl, (hval y hy).symm⟩, ?_⟩
      have hI := isIUnion_sUnion_ran hf fun y hy ↦ hval y (by simpa [hdom] using hy)
      simp [iUnion_eq_of_isIUnion (hdom ▸ hI)]
  | char R r ih =>
    simp only [eqRealize, SigmaOneBoundedFormula.realize_ex, SigmaOneBoundedFormula.realize_inf, ih,
      realize_char]
    split_ifs with h <;> simp [h]
  | recursion rg ih =>
    have := sigma_realize rg ih fun i ↦ (ts i.castSucc)〘xs〙
    -- the formula says that there is an approximation defined at the last entry of `ts`
    have hrg : ((recursion rg).eqRealize t ts).toBoundedFormula〘xs〙 ↔
        ∃ f, IsApprox f (fun w ↦ rg〘snoc (fun i ↦ (ts i.castSucc)〘xs〙) w〙) ∧
          (ts (last _))〘xs〙 ∈ dom f ∧ t〘xs〙 = f ﹫ (ts (last _))〘xs〙 := by
      simp only [eqRealize, SigmaOneBoundedFormula.realize_ex, SigmaOneBoundedFormula.realize_inf,
        SigmaOneBoundedFormula.realize_allMem, ih, Term.realize'_snoc, Term.realize'_castAdd,
        Fin.castAdd_add_one]
      simp [IsApprox, and_assoc, and_left_comm]
    rw [hrg]
    change _ ↔ _ = MemStructure.recursion (fun w ↦ rg〘snoc (fun i ↦ (ts i.castSucc)〘xs〙) w〙)
      (ts (last _))〘xs〙
    constructor
    · rintro ⟨f, hf, hx, ht⟩
      simp [ht, hf.recursion_eq hx]
    · intro ht
      obtain ⟨f, hf, hx⟩ := exists_isApprox (G := fun w ↦ rg〘snoc (fun i ↦ (ts i.castSucc)〘xs〙) w〙)
        (ts (last _))〘xs〙
      exact ⟨f, hf, hx, by simp [ht, hf.recursion_eq hx]⟩

theorem exists_isRecursion [ModelsKP M] {n : ℕ} (rg : L.PrimitiveRecursiveTerm (n + 1))
    (ps : Fin n → M) : ∃ F, IsRecursion F (fun y ↦ rg〘snoc ps y〙) := by
  have := sigma_realize rg (realize_eqRealize rg) ps
  exact MemStructure.exists_isRecursion

theorem exists_isIUnion [ModelsKP M] {n : ℕ} (ri : L.PrimitiveRecursiveTerm n)
    (rf : L.PrimitiveRecursiveTerm (n + 1)) (ps : Fin n → M) :
    ∃ a, IsIUnion (M := M) a ri〘ps〙 fun y ↦ rf〘snoc ps y〙 := by
  have := sigma_realize rf (realize_eqRealize rf) ps
  obtain ⟨f, hf, hdom, hval⟩ := isSetRestrictedTo_of_modelsKP (fun y ↦ rf〘snoc ps y〙) ri〘ps〙
  have hI := isIUnion_sUnion_ran hf fun y hy ↦ hval y (by simpa [hdom] using hy)
  exact ⟨_, by simpa [hdom] using hI⟩

@[simp]
theorem mem_realize_iUnion_iff [ModelsKP M] {n : ℕ} {ri : L.PrimitiveRecursiveTerm n}
    {rf : L.PrimitiveRecursiveTerm (n + 1)} {xs : Fin n → M} (x : M) :
    x ∈ (ri.iUnion rf)〘xs〙 ↔ ∃ z ∈ ri〘xs〙, x ∈ rf〘snoc xs z〙 :=
  mem_realize_iUnion_iff₀ x (exists_isIUnion ri rf xs)

theorem realize_recursion [ModelsKP M] {n : ℕ} {rg : L.PrimitiveRecursiveTerm (n + 1)}
    {xs : Fin (n + 1) → M} :
    rg.recursion〘xs〙 = rg〘snoc (xs ∘ castSucc)
      ((fun y ↦ rg.recursion〘snoc (xs ∘ castSucc) y〙) ↾₀ (xs (last _)))〙 :=
  realize_recursion₀_of_exists_isRecursion MemStructure.exists_mem_transitive_of_modelsKP
    (exists_isRecursion rg _)

end EqRealize

end PrimitiveRecursiveTerm

end FirstOrder.Language
