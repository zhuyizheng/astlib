/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Mathlib.ModelTheory.Syntax
/-!
file docstring
-/

open FirstOrder Language

open Structure Fin

universe u v

variable {L : FirstOrder.Language.{u, v}}

namespace FirstOrder

/-- A first-order language which contains the relationship symbol `∈` (and possibly
other symbols) -/
class Language.HasMem (L : Language.{u, v}) where
  /-- The relation symbol representing `∈`. -/
  memSymb : L.Relations 2

export HasMem (memSymb)

instance [L.HasMem] : Inhabited (L.Relations 2) := ⟨memSymb⟩

class Language.ExtraConstantsUnaryRelationsOnly (L : Language.{u, v}) [L.HasMem] : Prop where
  extraConstantsOnly : ∀ n, n ≠ 0 → IsEmpty (L.Functions n)
  extraUnaryRelationsOnly : (∀ n, n ≠ 1 → n ≠ 2 → IsEmpty (L.Relations n)) ∧
    Subsingleton (L.Relations 2)

class Language.ExtraConstantsOnly (L : Language.{u, v}) [L.HasMem] : Prop where
  extraConstantsOnly : ∀ n, n ≠ 0 → IsEmpty (L.Functions n)
  noExtraRelation : (∀ n, n ≠ 2 → IsEmpty (L.Relations n)) ∧
    Subsingleton (L.Relations 2)

instance [L.HasMem] [L.ExtraConstantsOnly] : L.ExtraConstantsUnaryRelationsOnly where
  extraConstantsOnly := ExtraConstantsOnly.extraConstantsOnly
  extraUnaryRelationsOnly := by
    have := ExtraConstantsOnly.noExtraRelation (L := L)
    tauto

instance (L' : Language) [L'.HasMem] [L'.ExtraConstantsUnaryRelationsOnly] :
  IsEmpty (L'.Functions (n + 1)) := by
  have := ExtraConstantsUnaryRelationsOnly.extraConstantsOnly (L := L') (n + 1) (by omega)
  infer_instance

instance (L' : Language) [L'.HasMem] [L'.ExtraConstantsUnaryRelationsOnly] :
  Subsingleton (L'.Relations 2) :=
  ExtraConstantsUnaryRelationsOnly.extraUnaryRelationsOnly.right

instance (L' : Language) [L'.HasMem] [L'.ExtraConstantsUnaryRelationsOnly] :
  Unique (L'.Relations 2) :=
  Unique.mk' _

instance [hn₁ : Fact (n ≠ 1)] [hn₂ : Fact (n ≠ 2)] (L' : Language) [L'.HasMem]
  [L'.ExtraConstantsUnaryRelationsOnly] :
  IsEmpty (L'.Relations n) :=
  ExtraConstantsUnaryRelationsOnly.extraUnaryRelationsOnly (L := L') |>.left n hn₁.elim hn₂.elim

instance [hn : Fact (n ≠ 2)] (L' : Language) [L'.HasMem] [L'.ExtraConstantsOnly] :
  IsEmpty (L'.Relations n) :=
  ExtraConstantsOnly.noExtraRelation (L := L') |>.left n hn.elim

instance (L' : Language) [L'.HasMem] [L'.ExtraConstantsOnly] :
  IsEmpty (L'.Relations 1) :=
  ExtraConstantsOnly.noExtraRelation (L := L') |>.left 1 (by decide)

def Language.toExtraConstantsOnly (L : Language.{u, v}) [L.HasMem] : Language.{u, v} where
  Functions n := match n with
    | 0 => L.Functions 0
    | _ => ULift Empty
  Relations n := match n with
    | 2 => ({memSymb} : Set (L.Relations 2))
    | _ => ULift Empty

instance (L : Language) [L.HasMem] : IsEmpty (L.toExtraConstantsOnly.Functions (n + 1)) := by
  simp only [toExtraConstantsOnly, isEmpty_ulift]
  infer_instance

instance {n} [hn : Fact (n ≠ 2)] (L : Language) [L.HasMem] :
  IsEmpty (L.toExtraConstantsOnly.Relations n) := by
  have := hn.elim
  simp only [toExtraConstantsOnly]
  infer_instance

instance (L : Language) [L.HasMem] : Unique (L.toExtraConstantsOnly.Relations 2) :=
  Set.uniqueSingleton memSymb

instance (L : Language) [L.HasMem] : L.toExtraConstantsOnly.HasMem := ⟨default⟩

instance instExtraConstantsOnly (L : Language) [L.HasMem] :
  L.toExtraConstantsOnly.ExtraConstantsOnly where
  extraConstantsOnly n := match n with
    | 0 => by simp
    | n + 1 => by simp only [toExtraConstantsOnly, isEmpty_ulift]; infer_instance
  noExtraRelation :=
    ⟨fun n hn ↦ by have : Fact (n ≠ 2) := { out := hn }; infer_instance,
      Unique.instSubsingleton⟩

namespace Language

def extraConstantsOnlyLHom (L : Language) [L.HasMem] : L.toExtraConstantsOnly →ᴸ L where
  onFunction n := match n with
    | 0 => id
    | n + 1 => isEmptyElim
  onRelation n := if hn : n = 2 then fun R ↦ hn ▸ memSymb else
    have : IsEmpty (L.toExtraConstantsOnly.Relations n) := by
      simp only [toExtraConstantsOnly]
      infer_instance
    isEmptyElim

variable {L : Language} [L.HasMem] {n : ℕ}

/-- Applies the `∈` relation to two terms as a bounded formula. -/
@[match_pattern]
def mem_boundedFormula (t₁ t₂ : L.Term' n) : L.BoundedFormula' n :=
  memSymb.boundedFormula₂ t₁ t₂

infix:88 " ∈' " => FirstOrder.Language.mem_boundedFormula

-- @[coe]
-- def ofExtraConstantsOnly {L : Language} [L.HasMem] {n : ℕ}
--   (φ : L.toExtraConstantsOnly.BoundedFormula' n) :=
--   L.extraConstantsOnlyLHom.onBoundedFormula φ

-- instance {L : Language} [L.HasMem] :
--   Coe (L.toExtraConstantsOnly.BoundedFormula' n) (L.BoundedFormula' n) :=
--   ⟨L.ofExtraConstantsOnly⟩

-- variable (φ ψ : L.toExtraConstantsOnly.BoundedFormula' n) (i j : Fin n)
--   (t₁ t₂ : L.toExtraConstantsOnly.Term' n)

-- @[simp]
-- theorem ofExtraConstantsOnly_bot :
--     L.extraConstantsOnlyLHom.onBoundedFormula (⊥ : L.toExtraConstantsOnly.BoundedFormula' n) =
--       (⊥ : L.BoundedFormula' n) := rfl

-- @[simp]
-- theorem ofExtraConstantsOnly_top :
--     L.extraConstantsOnlyLHom.onBoundedFormula (⊤ : L.toExtraConstantsOnly.BoundedFormula' n) =
--       (⊤ : L.BoundedFormula' n) := rfl

-- @[simp]
-- theorem ofExtraConstantsOnly_bdEqual :
--     L.extraConstantsOnlyLHom.onBoundedFormula (t₁ =' t₂) =
--       L.extraConstantsOnlyLHom.onTerm t₁ =' L.extraConstantsOnlyLHom.onTerm t₂ := rfl

-- -- @[simp]
-- -- theorem ofExtraConstantsOnly_bdEqual' :
-- --     L.extraConstantsOnlyLHom.onBoundedFormula (t₁ ∈' t₂) =
-- --       L.extraConstantsOnlyLHom.onTerm t₁ ∈' L.extraConstantsOnlyLHom.onTerm t₂ := rfl

-- @[simp]
-- theorem ofExtraConstantsOnly_mem :
--     L.extraConstantsOnlyLHom.onBoundedFormula (t₁ ∈' t₂) =
--       L.extraConstantsOnlyLHom.onTerm t₁ ∈' L.extraConstantsOnlyLHom.onTerm t₂ := by
--   simp only [mem_boundedFormula, Relations.boundedFormula₂,
--     Relations.boundedFormula, LHom.onBoundedFormula.eq_3,
--     BoundedFormula.rel.injEq, heq_eq_eq, true_and]
--   refine ⟨rfl, ?_⟩
--   ext k
--   fin_cases k <;> rfl

-- -- @[simp]
-- -- theorem ofExtraConstantsOnly_mem' :
-- --     L.extraConstantsOnlyLHom.onBoundedFormula (&i ∈' &j) = (&i ∈' &j : L.BoundedFormula' n) := by
-- --   simp [Function.comp_apply]

-- @[simp]
-- theorem ofExtraConstantsOnly_imp :
--     L.extraConstantsOnlyLHom.onBoundedFormula (φ ⟹ ψ) = L.extraConstantsOnlyLHom.onBoundedFormula φ ⟹ L.extraConstantsOnlyLHom.onBoundedFormula ψ := rfl

-- @[simp]
-- theorem ofExtraConstantsOnly_not :
--     L.extraConstantsOnlyLHom.onBoundedFormula (∼φ) = ∼(L.extraConstantsOnlyLHom.onBoundedFormula φ) := rfl

-- @[simp]
-- theorem ofExtraConstantsOnly_sup :
--     L.extraConstantsOnlyLHom.onBoundedFormula (φ ⊔ ψ) = L.extraConstantsOnlyLHom.onBoundedFormula φ ⊔ L.extraConstantsOnlyLHom.onBoundedFormula ψ := rfl

-- @[simp]
-- theorem ofExtraConstantsOnly_inf :
--     L.extraConstantsOnlyLHom.onBoundedFormula (φ ⊓ ψ) = L.extraConstantsOnlyLHom.onBoundedFormula φ ⊓ L.extraConstantsOnlyLHom.onBoundedFormula ψ := rfl

-- @[simp]
-- theorem ofExtraConstantsOnly_iff :
--     L.extraConstantsOnlyLHom.onBoundedFormula (φ ⇔ ψ) = L.extraConstantsOnlyLHom.onBoundedFormula φ ⇔ L.extraConstantsOnlyLHom.onBoundedFormula ψ := rfl

-- variable (φ : L.toExtraConstantsOnly.BoundedFormula' (n + 1))

-- @[simp]
-- theorem ofExtraConstantsOnly_all :
--     L.extraConstantsOnlyLHom.onBoundedFormula (∀' φ) = ∀' L.extraConstantsOnlyLHom.onBoundedFormula φ := rfl

-- @[simp]
-- theorem ofExtraConstantsOnly_ex :
--     L.extraConstantsOnlyLHom.onBoundedFormula (∃' φ) = ∃' L.extraConstantsOnlyLHom.onBoundedFormula φ := rfl

@[simp]
theorem BoundedFormula.substBound_mem_boundedFormula (t₁ t₂ : L.Term' n)
    (ts : Fin n → L.Term' m) :
    (t₁ ∈' t₂).substBound ts =
      (t₁.substBound ts) ∈' (t₂.substBound ts) := by
  simp only [mem_boundedFormula, Relations.boundedFormula₂, Relations.boundedFormula, substBound,
    Term.substBound, rel.injEq, heq_eq_eq, true_and]
  ext i
  fin_cases i <;> rfl

variable {L : Language} [L.HasMem] {α : Type*} {n : ℕ}

/-- `∀ x ∈ t, φ (..., x)` -/
def BoundedFormula.allMem
  (t : L.Term' n) (φ : L.BoundedFormula' (n + 1)) : L.BoundedFormula' n :=
  ∀' (&-1 ∈' t.castSucc ⟹ φ)

@[inherit_doc, match_pattern] scoped[FirstOrder]
notation "∀'∈ " x:arg y:50 => FirstOrder.Language.BoundedFormula.allMem x y

/-- `∃ x ∈ t, φ (..., x)` -/
def BoundedFormula.exMem
  (t : L.Term' n) (φ : L.BoundedFormula' (n + 1)) : L.BoundedFormula' n :=
  ∼(∀'∈ t (∼φ))

@[inherit_doc] scoped[FirstOrder]
notation "∃'∈ " x:arg y:50 => FirstOrder.Language.BoundedFormula.exMem x y

end Language

end FirstOrder
