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


variable {L : FirstOrder.Language}

namespace FirstOrder

/-- A first-order language which contains the relationship symbol `∈` (and possibly
other symbols) -/
class Language.HasMem (L : Language) where
  /-- The relation symbol representing `∈`. -/
  memSymb : L.Relations 2

export HasMem (memSymb)

instance [L.HasMem] : Inhabited (L.Relations 2) := ⟨memSymb⟩

/-- `L` has `∈` and possibly constant symbols and unary relation symbols, but not other symbols -/
class Language.ExtraConstantsUnaryRelationsOnly (L : Language) [L.HasMem] : Prop where
  extraConstantsOnly : ∀ n, n ≠ 0 → IsEmpty (L.Functions n)
  extraUnaryRelationsOnly : (∀ n, n ≠ 1 → n ≠ 2 → IsEmpty (L.Relations n)) ∧
    Subsingleton (L.Relations 2)

-- class Language.ExtraConstantsOnly (L : Language) [L.HasMem] : Prop where
--   extraConstantsOnly : ∀ n, n ≠ 0 → IsEmpty (L.Functions n)
--   noExtraRelation : (∀ n, n ≠ 2 → IsEmpty (L.Relations n)) ∧
--     Subsingleton (L.Relations 2)

-- instance [L.HasMem] [L.ExtraConstantsOnly] : L.ExtraConstantsUnaryRelationsOnly where
--   extraConstantsOnly := ExtraConstantsOnly.extraConstantsOnly
--   extraUnaryRelationsOnly := by
--     have := ExtraConstantsOnly.noExtraRelation
--     tauto

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
  ExtraConstantsUnaryRelationsOnly.extraUnaryRelationsOnly |>.left n hn₁.elim hn₂.elim

-- instance [hn : Fact (n ≠ 2)] (L' : Language) [L'.HasMem] [L'.ExtraConstantsOnly] :
--   IsEmpty (L'.Relations n) :=
--   ExtraConstantsOnly.noExtraRelation |>.left n hn.elim

-- instance (L' : Language) [L'.HasMem] [L'.ExtraConstantsOnly] :
--   IsEmpty (L'.Relations 1) :=
--   ExtraConstantsOnly.noExtraRelation |>.left 1 (by decide)

namespace Language

variable {L : Language} [L.HasMem] {n : ℕ}

/-- Applies the `∈` relation to two terms as a bounded formula. -/
@[match_pattern]
def mem_boundedFormula (t₁ t₂ : L.Term' n) : L.BoundedFormula' n :=
  memSymb.boundedFormula₂ t₁ t₂

infix:88 " ∈' " => FirstOrder.Language.mem_boundedFormula

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
