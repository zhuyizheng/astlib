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
/-!
file docstring
-/
open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula PrimitiveRecursiveTerm Fin MemStructure

variable {L : FirstOrder.Language.{u, v}} {M : Type max u v} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M]

namespace FirstOrder.Language

namespace MemStructure

instance {L : FirstOrder.Language.{u, v}} [L.HasMem] : SDiff (L.PrimitiveRecursiveTerm n) :=
  ⟨PrimitiveRecursiveTerm.sdiff⟩
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
  simp only [IsSetRestrictedTo, toSetRestrictedTo] at h ⊢
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
    (G ↾₀ x) ﹫ y = G y:=
  toSetRestrictedTo_aux h |>.right.right y hy

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
  have : HasComprehension y A := by
    refine ⟨?_⟩
    let B : Class M :=
      ((∼(&0 =₀ &1) : L.DeltaZeroBoundedFormula 2).substBoundRud ![ᵣ1 ﹫ ᵣ0, ᵣ2 ﹫ ᵣ0] : L.DeltaZeroBoundedFormula 3).toBoundedFormula.multiclass.slice ![F ↾₀ y, G ↾₀ y]
    have : B.DeltaZero Set.univ := by infer_instance
    use y ∩₀ B
    intro z
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
      mem_comprehension_iff, Multiclass.toClass_iff, Multiclass.slice, multiclass, isRelFree_not,
      isRelFree_eq, forall_fin_two, Matrix.cons_val_zero, RudimentaryTerm.isCharFree_var,
      RudimentaryTerm.isCharFree_val, Matrix.cons_val_one, Matrix.cons_val_fin_one, and_self,
      realize_substBoundRud, toBoundedFormula_not, toBoundedFormula, realize'_not, realize'_bdEqual,
      Term.realize'_var', RudimentaryTerm.realize_val, RudimentaryTerm.realize_basic, append_nat,
      coe_ofNat_eq_mod, Nat.one_mod, lt_self_iff_false, ↓reduceDIte, tsub_self, zero_eta,
      Nat.zero_mod, Order.lt_one_iff, Nat.mod_succ, Nat.add_one_sub_one,
      mk_one, ne_eq, and_congr_right_iff, B, A]
    intro hz
    have : z ∈ y := by grind
    simp [val_toSetRestrictedTo, hF, hG, this]
  have hAx : A x := by simp [A, hFGx]
  have ⟨x', hx'₁, hx'₂⟩:= exists_min_class_of_mem_transitive hAx hxy hy
  simp only [ne_eq, not_not, A] at hx'₁ hx'₂
  refine ⟨x', hx'₁, ?_⟩
  rw [IsFunction.ext (isFunction_toSetRestrictedTo (hF x')) (isFunction_toSetRestrictedTo (hG x'))]
  · simp [hF, hG]
  · simp only [hF, dom_toSetRestrictedTo]
    intro z hz
    simp [val_toSetRestrictedTo, hF, hG, hx'₂, hz]


theorem eq_of_isRecursion [Extensional M] [RudClosed M] [Foundational M]
    (hM : ∀ x : M, ∃ y : M, x ∈ y ∧ Transitive y)
    {F₁ F₂ G : ClassFunction M} (h₁ : IsRecursion F₁ G)
    (h₂ : IsRecursion F₂ G) : F₁ = F₂ := by
  funext x
  by_contra!
  obtain ⟨y, hy₁, hy₂⟩ := hM x
  have := exists_min_classFunction_ne_of_mem_transitive this hy₁ hy₂ h₁.left h₂.left
  grind [h₁.right, h₂.right]

theorem val_recursion [Extensional M] [RudClosed M] [Foundational M]
  (hM : ∀ x : M, ∃ y : M, x ∈ y ∧ Transitive y)
  {F G : ClassFunction M} (hFG : IsRecursion F G) : F = recursion G := by
  have : ∃ F, IsRecursion F G := ⟨F, hFG⟩
  simp only [recursion, this, ↓reduceDIte]
  apply eq_of_isRecursion hM hFG
  grind

end MemStructure

namespace PrimitiveRecursiveTerm

-- variable {L : FirstOrder.Language.{u, v}} [L.HasMem]

instance {L : FirstOrder.Language} [L.HasMem] : Singleton (L.PrimitiveRecursiveTerm n) (L.PrimitiveRecursiveTerm n) :=
  ⟨fun r ↦ ₚᵣ{r, r}⟩

-- @[simp]
-- theorem isCharFree_singleton {L : Language} [L.HasMem]
--     (r : L.PrimitiveRecursiveTerm n) :
--     ({r} : L.PrimitiveRecursiveTerm n).IsCharFree ↔ r.IsCharFree := by
--   simp [Singleton.singleton]

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

scoped[FirstOrder.Language] notation:max
  r "〘" xs "〙" => PrimitiveRecursiveTerm.realize r xs

scoped[FirstOrder.Language] notation:max
  r "〘" x "〙₁" => PrimitiveRecursiveTerm.realize r ![x]

scoped[FirstOrder.Language] notation:max
  r "〘" x ", " y "〙₂" => PrimitiveRecursiveTerm.realize r ![x, y]

scoped[FirstOrder.Language] notation:max
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

@[simp]
theorem _root_.FirstOrder.Language.Term.realize_toPrimitiveRecursiveTerm {n}
    (t : L.Term' n)
    (xs : Fin n → M) :
    (t.toPrimitiveRecursiveTerm)〘xs〙 = t〘xs〙 :=
  match t with
  | .var (Sum.inr i) => by simp [Term.toPrimitiveRecursiveTerm]
  | .func F _ (l := 0) => by
    simp only [Term.toPrimitiveRecursiveTerm, realize_const, constantMap, Term.realize'_func]
    congr
    ext i; fin_cases i
  | .func F _ (l := n + 1) => IsEmpty.elim (by infer_instance) F


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
  simp [realize, ← val_recursion hM h, h.right]


theorem realize_recursion₀_of_exists_isRecursion [Extensional M] [RudClosed M] [Foundational M]
    (hM : ∀ x : M, ∃ y : M, x ∈ y ∧ Transitive y)
    {n : ℕ} {rg : L.PrimitiveRecursiveTerm (n + 1)}
    {xs : Fin (n + 1) → M}
    (h : ∃ F, IsRecursion (M := M) F (fun y ↦ rg〘snoc (xs ∘ castSucc) y〙)) :
    rg.recursion〘xs〙 = rg〘snoc (xs ∘ castSucc) ((fun y ↦ rg.recursion〘snoc (xs ∘ castSucc) y〙) ↾₀ (xs (last _)))〙 := by
  obtain ⟨F, hF⟩ := h
  convert realize_recursion₀_of_isRecursion hM hF
  simp [realize, val_recursion hM hF]

end PrimitiveRecursiveTerm

end FirstOrder.Language
