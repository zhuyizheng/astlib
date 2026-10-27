/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.PrimitiveRecursive.Syntax
import Astlib.Basic.SetOperation.Rudimentary.Semantics
import Astlib.Basic.SetOperation.Multiclass.Lambda
import Astlib.Basic.SetOperation.Function
import Astlib.Basic.SetOperation.Foundational
import Astlib.Basic.Transitive.Basic
import Astlib.Basic.Axiom.KP.SigmaOneBoundedFormula.Semantics
import Astlib.Basic.Order.StrictWellFounded
/-!
file docstring
-/
open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula PrimitiveRecursiveTerm Fin MemStructure

variable {L : FirstOrder.Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M]

namespace FirstOrder.Language

namespace MemStructure

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
  let F : Multiclass M 2 := fun xs ↦ xs 1 = !(xs 0, G (xs 0))
  have hF (u w : M) : F ![u, w] ↔ w = !(u, G u) := .rfl
  have hFa₁ :  ∀ (z : M), z ∈ F ''₀ a ↔ ∃ u ∈ a, F ![u, z] :=
    mem_replacement_iff fun u _ ↦ ⟨!(u, G u), by grind, by grind⟩
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

/-! ### `∈`-recursion as well-founded recursion along `∈` -/

theorem isApprox_iff_isWFApprox [Extensional M] [RudClosed M] {G : ClassFunction M} {f : M} :
    IsApprox f G ↔ IsWFApprox f G MemRel := by
  simp only [IsApprox, IsWFApprox, predSet_memRel_apply, Transitive]

theorem isRecursion_iff_isWFRecursion [Extensional M] {F G : ClassFunction M} :
    IsRecursion F G ↔ IsWFRecursion F G MemRel := by
  simp [IsRecursion, IsWFRecursion, isSetLike_memRel]

/-- Two approximations agree on their common domain -/
theorem IsApprox.val_eq_val [ModelsKP M] {G : ClassFunction M} {f f' x : M}
    (hf : IsApprox f G) (hf' : IsApprox f' G) (hx : x ∈ dom f) (hx' : x ∈ dom f') :
    f ﹫ x = f' ﹫ x := by
  rw [isApprox_iff_isWFApprox] at hf hf'
  exact hf.val_eq_val isStrictWellFounded₀_memRel isSetLike_memRel hf' hx hx'

/-- The existence of approximations for a `Σ₁` class function `G` -/
theorem exists_isApprox [ModelsKP M] (G : ClassFunction M) [G.Sigma 1 Set.univ] (x : M) :
    ∃ f, IsApprox f G ∧ x ∈ dom f := by
  simpa only [isApprox_iff_isWFApprox] using
    exists_isWFApprox isStrictWellFounded₀_memRel isSetLike_memRel x

/-- The `Σ`-recursion theorem: a `Σ₁` class function `G` admits a class function defined by
recursion from it -/
theorem exists_isRecursion [ModelsKP M] (G : ClassFunction M) [G.Sigma 1 Set.univ] :
    ∃ F, IsRecursion F G := by
  simpa only [isRecursion_iff_isWFRecursion] using
    exists_isWFRecursion isStrictWellFounded₀_memRel isSetLike_memRel

/-- `recursion G` agrees with every approximation, assuming that `G` is `Σ₁` -/
theorem IsApprox.recursion_eq [ModelsKP M] {G : ClassFunction M} [G.Sigma 1 Set.univ]
    {f x : M} (hf : IsApprox f G) (hx : x ∈ dom f) : recursion G x = f ﹫ x := by
  obtain ⟨F, hF⟩ := exists_isRecursion G
  have hFwf := hF
  rw [isRecursion_iff_isWFRecursion] at hFwf
  rw [isApprox_iff_isWFApprox] at hf
  rw [← hF.eq_recursion exists_mem_transitive_of_modelsKP,
    hFwf.eq_wfRecursion isStrictWellFounded₀_memRel]
  exact hf.wfRecursion_eq isStrictWellFounded₀_memRel isSetLike_memRel hx

/-- The recursive definition `recursion G x = G (recursion G ↾₀ x)` for a `Σ₁` class function `G`
in models of `KP` -/
theorem recursion_eq_of_modelsKP [ModelsKP M] (G : ClassFunction M) [G.Sigma 1 Set.univ]
    (x : M) : recursion G x = G (recursion G ↾₀ x) :=
  recursion_eq exists_mem_transitive_of_modelsKP (exists_isRecursion G) x

/-- `recursion G` is a `Σ₁` class function for a `Σ₁` class function `G` -/
instance [ModelsKP M] (G : ClassFunction M) [G.Sigma 1 Set.univ] :
    (recursion G).Sigma 1 Set.univ := by
  obtain ⟨F, hF⟩ := exists_isRecursion G
  have hFwf := hF
  rw [isRecursion_iff_isWFRecursion] at hFwf
  rw [← hF.eq_recursion exists_mem_transitive_of_modelsKP,
    hFwf.eq_wfRecursion isStrictWellFounded₀_memRel]
  exact sigma_wfRecursion isStrictWellFounded₀_memRel isSetLike_memRel

end MemStructure

namespace PrimitiveRecursiveTerm

-- variable {L : FirstOrder.Language} [L.HasMem]


noncomputable def realize {n : ℕ} (r : L.PrimitiveRecursiveTerm n) : MulticlassFunction M n :=
  match r with
  | var i => fun xs ↦ xs i
  | const c => fun _ ↦ ↑c
  | unorderedPair r₁ r₂ => fun xs ↦ MemStructure.unorderedPair (r₁.realize xs) (r₂.realize xs)
  | sdiff r₁ r₂ => fun xs ↦ MemStructure.sdiff (r₁.realize xs) (r₂.realize xs)
  | iUnion ri rf => fun xs ↦ MemStructure.iUnion (ri.realize xs) (fun y ↦ rf.realize (snoc xs y))
  | char R r => fun xs ↦ if Structure.RelMap R ![r.realize xs] then MemStructure.unorderedPair ∅ ∅ else ∅
  | recursion rg =>
    fun xs ↦ MemStructure.recursion (fun y ↦ rg.realize (snoc (xs ∘ Fin.castSucc) y)) (xs (last _))

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

theorem realize_recursion' (xs : Fin (n + 1) → M) :
    rg.recursion〘xs〙 =
      MemStructure.recursion (fun y ↦ rg〘snoc (xs ∘ Fin.castSucc) y〙) (xs (last _)) := by
  simp [realize]

@[simp, grind =]
theorem realize_char :
    (char R r)〘xs〙 = if Structure.RelMap R ![r.realize xs] then MemStructure.unorderedPair ∅ ∅ else ∅ := by
  simp [realize]

/-- A rudimentary term has the same meaning as a primitive recursive term -/
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_toPrimitiveRecursiveTerm {n}
    (r : L.RudimentaryTerm n) (xs : Fin n → M) : r.toPrimitiveRecursiveTerm〘xs〙 = r〘xs〙 := by
  induction r with
  | var i => simp [RudimentaryTerm.toPrimitiveRecursiveTerm]
  | const c => simp [RudimentaryTerm.toPrimitiveRecursiveTerm]
  | unorderedPair r₁ r₂ ih₁ ih₂ =>
    simp [RudimentaryTerm.toPrimitiveRecursiveTerm, ih₁, ih₂]
  | sdiff r₁ r₂ ih₁ ih₂ =>
    simp [RudimentaryTerm.toPrimitiveRecursiveTerm, ih₁, ih₂]
  | iUnion ri rf ihi ihf =>
    simp [RudimentaryTerm.toPrimitiveRecursiveTerm, RudimentaryTerm.realize, realize_iUnion, ihi, ihf]
  | char R r ih =>
    simp [RudimentaryTerm.toPrimitiveRecursiveTerm, ih]

@[simp]
theorem _root_.FirstOrder.Language.Term.realize_toPrimitiveRecursiveTerm {n} (t : L.Term' n)
    (xs : Fin n → M) : t.toPrimitiveRecursiveTerm〘xs〙 = t〘xs〙 := by
  simp [Term.toPrimitiveRecursiveTerm]

@[simp]
theorem realize_singleton : ({r} : L.PrimitiveRecursiveTerm n)〘xs〙 = !{(r〘xs〙 : M), r〘xs〙} := by
  simp [Singleton.singleton]

@[simp]
theorem realize_snoc {m : ℕ} (ps : Fin n → L.PrimitiveRecursiveTerm m)
    (p : L.PrimitiveRecursiveTerm m) (xs : Fin m → M) (i : Fin (n + 1)) :
    realize (snoc (α := fun _ ↦ L.PrimitiveRecursiveTerm m) ps p i) xs =
      snoc (α := fun _ ↦ M) (fun i ↦ (ps i)〘xs〙) p〘xs〙 i := by
  cases i using lastCases <;> simp

section Subst

variable [Extensional M] [RudClosed M]

omit [L.ExtraConstantsUnaryRelationsOnly] in
@[simp]
theorem _root_.FirstOrder.Language.MemStructure.iUnion_unorderedPair_self (t : M)
    (F : ClassFunction M) : MemStructure.iUnion !{t, t} F = F t :=
  iUnion_eq_of_isIUnion (by simp [IsIUnion])

@[simp]
theorem realize_substBoundBound {m : ℕ} (f : Fin n → Fin m) (xs : Fin m → M) :
    (r.substBoundBound f)〘xs〙 = r〘xs ∘ f〙 := by
  induction r generalizing m <;>
    simp_all [substBoundBound, realize, SDiff.sdiff, comp_snoc, ← Function.comp_assoc]

@[simp]
theorem realize_castSucc (x : M) : r.castSucc〘snoc xs x〙 = r〘xs〙 := by
  simp [castSucc]

@[simp]
theorem realize_substBoundPR {m : ℕ} (ps : Fin n → L.PrimitiveRecursiveTerm m) (xs : Fin m → M) :
    (r.substBoundPR ps)〘xs〙 = r〘fun i ↦ (ps i)〘xs〙〙 := by
  induction r generalizing m <;> simp_all [substBoundPR, realize, SDiff.sdiff]; rfl

@[simp]
theorem realize_union : (r₁ ∪ r₂)〘xs〙 = r₁〘xs〙 ∪ r₂〘xs〙 :=
  iUnion_eq_of_isIUnion (by simp [IsIUnion])

noncomputable instance (φ : L.BoundedFormula' n) (xs : Fin n → M) : Decidable (φ〘xs〙) :=
  Classical.propDecidable _

@[simp]
theorem realize_ifTrue [NeZero n] (φ : L.DeltaZeroBoundedFormula n) :
    (r.ifTrue φ)〘xs〙 = if φ.toBoundedFormula〘xs〙 then (r〘xs〙 : M) else ∅ :=
  iUnion_eq_of_isIUnion (by split_ifs with h <;> simp [IsIUnion,
    realize_charRudimentaryTerm_of_realize, realize_charRudimentaryTerm_of_not_realize, h])

end Subst

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
    (h : IsRecursion F (fun y ↦ rg〘snoc (xs ∘ Fin.castSucc) y〙)) :
    rg.recursion〘xs〙 = rg〘snoc (xs ∘ Fin.castSucc) (F ↾₀ (xs (last _)))〙 := by
  simp [realize, ← h.eq_recursion hM, h.right]


theorem realize_recursion₀_of_exists_isRecursion [Extensional M] [RudClosed M] [Foundational M]
    (hM : ∀ x : M, ∃ y : M, x ∈ y ∧ Transitive y)
    {n : ℕ} {rg : L.PrimitiveRecursiveTerm (n + 1)}
    {xs : Fin (n + 1) → M}
    (h : ∃ F, IsRecursion F (fun y ↦ rg〘snoc (xs ∘ Fin.castSucc) y〙)) :
    rg.recursion〘xs〙 = rg〘snoc (xs ∘ Fin.castSucc) ((fun y ↦ rg.recursion〘snoc (xs ∘ Fin.castSucc) y〙) ↾₀ (xs (last _)))〙 := by
  obtain ⟨F, hF⟩ := h
  convert realize_recursion₀_of_isRecursion hM hF
  simp [realize, hF.eq_recursion hM]

section EqRealize

open SigmaOneBoundedFormula

/-- Given the correctness of `rf.eqRealize`, the class function `y ↦ rf(ys, y)` is `Σ₁` -/
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
    simp only [realize_recursion', Function.comp_def]
    refine ⟨by grind [IsApprox.recursion_eq], fun ht ↦ ?_⟩
    have := exists_isApprox (fun w ↦ rg〘snoc (fun i ↦ (ts i.castSucc)〘xs〙) w〙) (ts (last _))〘xs〙
    grind [IsApprox.recursion_eq]

/-- In models of `KP`, the graph of `p` is defined by the formula `p.eqRealize`. -/
theorem toMulticlass_realize_eq [ModelsKP M] {n : ℕ} (p : L.PrimitiveRecursiveTerm n) :
    ((p.realize : MulticlassFunction M n) : Multiclass M (n + 1)) =
      (p.eqRealize &-1 fun i ↦ &(i.castSucc)).toBoundedFormula.multiclass := by
  funext xs
  rw [← snoc_init_self xs, MulticlassFunction.toMulticlass_snoc_iff]
  simp [realize_eqRealize, init_def, eq_comm]

/-- A primitive recursive term with all but its last argument fixed is a `Σ₁` class function in
models of `KP` -/
instance [ModelsKP M] {n : ℕ} (p : L.PrimitiveRecursiveTerm (n + 1)) (xs : Fin n → M) :
    ClassFunction.Sigma (fun y ↦ p〘snoc xs y〙) 1 Set.univ :=
  sigma_realize p (realize_eqRealize p) xs

/-- A unary primitive recursive term is a `Σ₁` class function in models of `KP` -/
instance [ModelsKP M] (p : L.PrimitiveRecursiveTerm 1) :
    ClassFunction.Sigma (fun y ↦ p〘y〙₁) 1 Set.univ := by
  simpa only [Matrix.Fin.snoc_vecEmpty] using sigma_realize p (realize_eqRealize p) ![]

/-- A binary primitive recursive term is a `Σ₁` class function in the second coordinate
in models of `KP` -/
instance [ModelsKP M] (p : L.PrimitiveRecursiveTerm 2) (x : M) :
    ClassFunction.Sigma (fun y ↦ p〘x, y〙₂) 1 Set.univ := by
  simpa only [Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty] using
    sigma_realize p (realize_eqRealize p) ![x]

/-- A ternary primitive recursive term is a `Σ₁` class function in the third coordinate
in models of `KP` -/
instance [ModelsKP M] (p : L.PrimitiveRecursiveTerm 3) (x y : M) :
    ClassFunction.Sigma (fun z ↦ p〘x, y, z〙₃) 1 Set.univ := by
  simpa only [Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty] using
    sigma_realize p (realize_eqRealize p) ![x, y]

/-- A primitive recursive term is a `Σ₁` multiclass function in models of `KP` -/
instance [ModelsKP M] {n : ℕ} (p : L.PrimitiveRecursiveTerm n) :
    MulticlassFunction.Sigma (p.realize : MulticlassFunction M n) 1 Set.univ := by
  refine { toSigma := ?_ }
  rw [toMulticlass_realize_eq]
  infer_instance

theorem exists_isRecursion [ModelsKP M] {n : ℕ} (rg : L.PrimitiveRecursiveTerm (n + 1))
    (xs : Fin n → M) : ∃ F, IsRecursion F (fun y ↦ rg〘snoc xs y〙) :=
  MemStructure.exists_isRecursion _

theorem isSetRestrictedTo [ModelsKP M] {n : ℕ} (p : L.PrimitiveRecursiveTerm (n + 1))
    (xs : Fin n → M) (x : M) : IsSetRestrictedTo (fun y ↦ p〘snoc xs y〙) x :=
  isSetRestrictedTo_of_modelsKP _ x

theorem exists_isIUnion [ModelsKP M] {n : ℕ} (ri : L.PrimitiveRecursiveTerm n)
    (rf : L.PrimitiveRecursiveTerm (n + 1)) (xs : Fin n → M) :
    ∃ a, IsIUnion (M := M) a ri〘xs〙 fun y ↦ rf〘snoc xs y〙 := by
  obtain ⟨f, hf, hdom, hval⟩ := isSetRestrictedTo_of_modelsKP (fun y ↦ rf〘snoc xs y〙) ri〘xs〙
  have hI := isIUnion_sUnion_ran hf fun y hy ↦ hval y (by simpa [hdom] using hy)
  grind

@[simp]
theorem mem_realize_iUnion_iff [ModelsKP M] {n : ℕ} {ri : L.PrimitiveRecursiveTerm n}
    {rf : L.PrimitiveRecursiveTerm (n + 1)} {xs : Fin n → M} (x : M) :
    x ∈ (ri.iUnion rf)〘xs〙 ↔ ∃ z ∈ ri〘xs〙, x ∈ rf〘snoc xs z〙 :=
  mem_realize_iUnion_iff₀ x (exists_isIUnion ri rf xs)

theorem realize_recursion [ModelsKP M] {n : ℕ} {rg : L.PrimitiveRecursiveTerm (n + 1)}
    {xs : Fin (n + 1) → M} :
    rg.recursion〘xs〙 = rg〘snoc (xs ∘ Fin.castSucc)
      ((fun y ↦ rg.recursion〘snoc (xs ∘ Fin.castSucc) y〙) ↾₀ (xs (last _)))〙 :=
  realize_recursion₀_of_exists_isRecursion MemStructure.exists_mem_transitive_of_modelsKP
    (exists_isRecursion rg _)

end EqRealize

end PrimitiveRecursiveTerm

end FirstOrder.Language
