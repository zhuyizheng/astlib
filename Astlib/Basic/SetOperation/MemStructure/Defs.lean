/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
-- import Init.Core

import Astlib.Basic.SetOperation.MemStructure.Syntax
import Astlib.Mathlib.ModelTheory.Semantics
import Astlib.Mathlib.Fin.Basic
import Astlib.Mathlib.ModelTheory.LanguageMap

/-!
file docstring
-/

open FirstOrder Language BoundedFormula Fin

variable (L : FirstOrder.Language) [L.HasMem]

namespace FirstOrder.Language

structure MemStructure where
  Carrier : Type*
  L : FirstOrder.Language
  [hasMem : L.HasMem]
  [struc : L.Structure Carrier]
  [nonempty' : Nonempty Carrier]

-- Porting note: In Lean4, other instances precedes `FirstOrder.Language.Theory.ModelType.struc`,
-- it's issues in `ModelTheory.Satisfiability`. So, we increase these priorities. TODO
attribute [instance 2000] MemStructure.hasMem MemStructure.struc
  MemStructure.nonempty'

namespace MemStructure

attribute [coe] MemStructure.Carrier

instance : CoeSort MemStructure (Type _) where
  coe M := M.Carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. TODO -/
def of (M : Type w) [L.Structure M] [Nonempty M] : MemStructure :=
  ⟨M, L⟩

variable (M : MemStructure) (α : Type*) (n : ℕ)

instance : Nonempty M := inferInstance

noncomputable instance : Inhabited M := Classical.inhabited_of_nonempty'

-- instance (M : MemStructure) : M.L.toExtraConstantsOnly.Structure M :=
--   M.L.extraConstantsOnlyLHom.reduct M

def L' (M : MemStructure) := M.L.toExtraConstantsOnly

def LHom (M : MemStructure) := M.L.extraConstantsOnlyLHom

instance (M : MemStructure) : M.L.HasMem := by infer_instance

instance (M : MemStructure) : M.L'.HasMem := by simp only [L']; infer_instance

instance (M : MemStructure) : M.L'.ExtraConstantsOnly :=
  instExtraConstantsOnly M.L

-- instance (M : MemStructure) : M.L'.Structure M := by
--   simp only [L']
--   infer_instance

end MemStructure

namespace Term

open MemStructure

variable {M : MemStructure} {n l : ℕ}

def castLHom {n : ℕ} {M : MemStructure} (t : M.L'.Term' n) :
  M.L.Term' n :=
  M.LHom.onTerm t

@[simp]
theorem castLHom_var (k : Fin n) :
    (&k : M.L'.Term' n).castLHom = &k := by
  simp [castLHom]

@[simp]
theorem castLHom_var' (k : Fin n) :
    (var (Sum.inr k) : M.L'.Term' n).castLHom = &k := by
  simp [castLHom]

@[simp]
theorem castLHom_func (F : M.L'.Functions 0) (ts : Fin 0 → M.L'.Term' n) :
    (func F ts : M.L'.Term' n).castLHom = func (M.LHom.onFunction F) elim0 := by
  simp only [castLHom, LHom.onTerm, func.injEq, heq_eq_eq, true_and]
  ext i; fin_cases i

@[simp]
theorem castLHom_const (c : M.L'.Constants) :
    (c.term : M.L'.Term' n).castLHom = Constants.term (M.LHom.onFunction c) :=
  LHom.onTerm_const _ (I := M.LHom)

@[simp]
theorem castLHom_substBound (t : M.L'.Term' n) (ts : Fin n → M.L'.Term' m) :
    (t.substBound ts).castLHom =
      t.castLHom.substBound (fun i ↦ (ts i).castLHom) :=
  LHom.onTerm_substBound _ _

@[simp]
theorem castLHom_substBoundBound (t : M.L'.Term' n)
    (f : Fin n → Fin m) :
    (t.substBoundBound f).castLHom =
      t.castLHom.substBoundBound f :=
  LHom.onTerm_substBoundBound _ _

-- @[simp]
-- theorem realize'_reduct
--     {M : MemStructure} {n : ℕ} (t : M.L'.Term' n)
--     (xs : Fin n → M) :
--     t〘xs〙 = t.castLHom〘xs〙 := by
--   simp only [Term.realize', castLHom, MemStructure.LHom, LHom.realize_onTerm]
--   rfl

end Term

namespace MemStructure

variable {M : MemStructure}

-- variable {M} in
/-- Membership in a set -/
protected def Mem (x y : M) : Prop :=
  Structure.RelMap (M.hasMem.memSymb) ![y, x]

instance : Membership M M := ⟨M.Mem⟩

@[simp]
theorem realize'_mem {M : MemStructure} {n : ℕ} (t₁ t₂ : M.L.Term' n) (xs : Fin n → M) :
    (t₁ ∈' t₂)〘xs〙 ↔ t₁〘xs〙 ∈ t₂〘xs〙 := by
  simp [mem_boundedFormula, Membership.mem, MemStructure.Mem]

@[simp]
theorem realize_mem {M : MemStructure} {n : ℕ} (t₁ t₂ : M.L.Term' n)
    (v : Empty → M) (xs : Fin n → M) :
    BoundedFormula.Realize (t₁ ∈' t₂) v xs ↔ t₁〘xs〙 ∈ t₂〘xs〙 := by
  convert realize'_mem t₁ t₂ xs
  rw [Realize', Unique.uniq _ v]

end MemStructure

namespace BoundedFormula

open MemStructure

variable {M : MemStructure} {n l : ℕ}

variable (φ ψ : M.L'.BoundedFormula' n)
  (t₁ t₂ : M.L'.Term' n)

def castLHom {n : ℕ} {M : MemStructure} (φ : M.L'.BoundedFormula' n) :
  M.L.BoundedFormula' n :=
  M.LHom.onBoundedFormula φ

-- @[simp]
-- theorem realize'_reduct
--     {M : MemStructure} {n : ℕ} (φ : M.L'.BoundedFormula' n)
--     (xs : Fin n → M) :
--     φ〘xs〙 ↔ φ.castLHom〘xs〙 := by
--   simp only [Realize', castLHom, MemStructure.LHom, LHom.realize_onBoundedFormula]
--   rfl

@[simp]
theorem castLHom_falsum :
    (falsum : M.L'.BoundedFormula' n).castLHom =
      (⊥ : M.L.BoundedFormula' n) := rfl

@[simp]
theorem castLHom_bot :
    (⊥ : M.L'.BoundedFormula' n).castLHom =
      (⊥ : M.L.BoundedFormula' n) := rfl

@[simp]
theorem castLHom_top :
    (⊤ : M.L'.BoundedFormula' n).castLHom =
      (⊤ : M.L.BoundedFormula' n) := rfl

@[simp]
theorem castLHom_bdEqual :
    (t₁ =' t₂ : M.L'.BoundedFormula' n).castLHom =
      t₁.castLHom =' t₂.castLHom := rfl

-- @[simp]
-- theorem castLHom_bdEqual' :
--     L.extraConstantsOnlyLHom.onBoundedFormula (t₁ ∈' t₂) =
--       L.extraConstantsOnlyLHom.onTerm t₁ ∈' L.extraConstantsOnlyLHom.onTerm t₂ := rfl

@[simp]
theorem castLHom_mem :
    (t₁ ∈' t₂).castLHom = t₁.castLHom ∈' t₂.castLHom := by
  simp only [castLHom, mem_boundedFormula, Relations.boundedFormula₂, Relations.boundedFormula,
    LHom.onBoundedFormula, rel.injEq, heq_eq_eq, true_and]
  refine ⟨rfl, ?_⟩
  ext k
  fin_cases k <;> rfl

-- @[simp]
-- theorem castLHom_mem' :
--     L.extraConstantsOnlyLHom.onBoundedFormula (&i ∈' &j) = (&i ∈' &j : L.BoundedFormula' n) := by
--   simp [Function.comp_apply]

@[simp]
theorem castLHom_imp :
    (φ ⟹ ψ : M.L'.BoundedFormula' n).castLHom =
      φ.castLHom ⟹ ψ.castLHom := rfl

@[simp]
theorem castLHom_not :
    (∼φ : M.L'.BoundedFormula' n).castLHom =
      ∼(φ.castLHom) := rfl

@[simp]
theorem castLHom_sup :
    (φ ⊔ ψ : M.L'.BoundedFormula' n).castLHom =
      φ.castLHom ⊔ ψ.castLHom := rfl

@[simp]
theorem castLHom_inf :
    (φ ⊓ ψ : M.L'.BoundedFormula' n).castLHom =
      φ.castLHom ⊓ ψ.castLHom := rfl

@[simp]
theorem castLHom_iff :
    (φ ⇔ ψ : M.L'.BoundedFormula' n).castLHom =
      φ.castLHom ⇔ ψ.castLHom := rfl

variable (φ : M.L'.BoundedFormula' (n + 1))

@[simp]
theorem castLHom_all :
    (∀' φ : M.L'.BoundedFormula' n).castLHom =
      ∀' φ.castLHom := rfl

@[simp]
theorem castLHom_ex :
    (∃' φ : M.L'.BoundedFormula' n).castLHom =
      ∃' φ.castLHom := rfl

@[simp]
theorem castLHom_allMem (φ : M.L'.BoundedFormula' (n + 1))
    (t : M.L'.Term' n) :
    (∀'∈ t φ).castLHom = ∀'∈ t.castLHom φ.castLHom := by
  simp [allMem]

-- @[simp]
-- theorem castLHom_allMem (φ : M.L'.BoundedFormula' (n + 1))
--     (i : Fin n) :
--     M.castLHom
--       (∀'∈ (var (Sum.inr i)) φ : M.L'.BoundedFormula' n) =
--       ∀'∈ (var (Sum.inr i)) (M.castLHom φ) := by
--   simp [BoundedFormula.allMem, castLHom]

@[simp]
theorem castLHom_exMem (φ : M.L'.BoundedFormula' (n + 1))
    (t : M.L'.Term' n) :
    (∃'∈ t φ).castLHom = ∃'∈ t.castLHom φ.castLHom := by
  simp [exMem]


-- @[simp]
-- theorem castLHom_exMem (φ : M.L'.BoundedFormula' (n + 1))
--     (i : Fin n) :
--     M.LHom.onBoundedFormula
--       (∃'∈ (var (Sum.inr i)) φ : M.L'.BoundedFormula' n) =
--       ∃'∈ (var (Sum.inr i)) (M.castLHom φ) := by
--   simp [BoundedFormula.exMem]
variable (φ : M.L'.BoundedFormula' n)

@[simp]
theorem castLHom_substBound (ts : Fin n → M.L'.Term' m) :
    (φ.substBound ts).castLHom =
      φ.castLHom.substBound (fun i ↦ (ts i).castLHom) := by
  convert LHom.onBoundedFormula_substBound φ ts (I := M.LHom) <;> rfl

@[simp]
theorem castLHom_substBoundBound (f : Fin n → Fin m) :
    (φ.substBoundBound f).castLHom =
      φ.castLHom.substBoundBound f :=
  castLHom_substBound _ _

end BoundedFormula

end FirstOrder.Language




section ExUnique

variable {M : MemStructure} {L : Language} [L.Structure M]

-- {T : L.Theory} {M : T.ModelType}

variable {α : Type*} {n : ℕ} {φ : L.BoundedFormula' n}

-- theorem exists_of_ex {φ : L.BoundedFormula' (n + 1)} {v : α → M}
--     {xs : Fin n → M} (h : (∃' φ)〘v, xs〙) :
--     ∃ a, φ〘v, snoc xs a〙 := by
--   simpa using h

theorem existsUnique_of_exUnique {φ : L.BoundedFormula' (n + 1)}
    {xs : Fin n → M} (h : (∃!' φ)〘xs〙) :
    ∃! a, φ〘snoc xs a〙 := by
  simp only [BoundedFormula.exUnique, Function.comp_apply, realize'_ex, realize'_inf, realize'_all,
    realize'_imp, realize'_substBoundBound, snoc_snoc_comp_snoc_castAdd_two_last, realize'_bdEqual,
    Term.realize'_var', snoc_last, snoc_snoc_castAdd_one_last] at h
  exact h

theorem existsUnique_of_exUnique_sentence {φ : L.BoundedFormula Empty 1}
    {xs : Fin 0 → M} (h : (∃!' φ)〘xs〙) :
    ∃! a : M, φ〘![a]〙 := by
  convert existsUnique_of_exUnique h
  ext i
  simp [snoc]


end ExUnique
