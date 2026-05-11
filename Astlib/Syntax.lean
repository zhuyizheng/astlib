import Mathlib

import Astlib.ModelTheory.Syntax


open FirstOrder Language

open Structure Fin

universe u v

variable {L : FirstOrder.Language}


-- @[inherit_doc] scoped[FirstOrder] prefix:110 "∀'' " => FirstOrder.Language.BoundedFormula.alls

-- @[inherit_doc] scoped[FirstOrder] prefix:110 "∃'' " => FirstOrder.Language.BoundedFormula.exs

namespace FirstOrder


namespace Language
-- @[simp]
-- theorem Language.BoundedFormula.castLE_all (φ : L.BoundedFormula α (n + 1)) (h : n ≤ n') :
--     (∀' φ).castLE h = ∀' (φ.castLE (Nat.add_le_add_right h _)) := by simp

end Language

/-- A first-order language which contains the relationship symbol `∈` (and possibly
other symbols) -/
class Language.HasMem (L : Language.{u, v}) where
  /-- The relation symbol representing `∈`. -/
  memSymb : L.Relations 2

export HasMem (memSymb)

namespace Language

/-- The type of relations for the language of orders, consisting of a single binary relation `le`.
 The `Language` with no symbols other than `∈` -/
inductive pureMemRel : ℕ → Type
  | mem : pureMemRel 2
  deriving DecidableEq

/-- The relational language consisting of a single relation representing `∈`. -/
def pureSTLanguage : Language := ⟨fun _ => Empty, pureMemRel⟩
  deriving IsRelational

instance : HasMem pureSTLanguage := ⟨.mem⟩

-- open STLanguage


variable {L : Language} [HasMem L]

/-- Applies the `∈` relation to two terms as a bounded formula. -/
@[match_pattern]
def mem_boundedFormula [HasMem L] (t₁ t₂ : L.Term (α ⊕ (Fin n))) :
    L.BoundedFormula α n :=
  memSymb.boundedFormula₂ t₁ t₂

-- @[inherit_doc] scoped[STLanguage]
infix:88 " ∈' " => FirstOrder.Language.mem_boundedFormula

@[simp]
theorem BoundedFormula.castLE_mem_boundedFormula (h : n ≤ n') (t₁ t₂ : L.Term (α ⊕ (Fin n))) :
    (t₁ ∈' t₂).castLE h = (t₁.castLE h) ∈' (t₂.castLE h) := by
  simp [mem_boundedFormula]

@[simp]
theorem BoundedFormula.liftAt_mem_boundedFormula (t₁ t₂ : L.Term (α ⊕ (Fin n))) :
    (t₁ ∈' t₂).liftAt n' m = (t₁.liftAt n' m) ∈' (t₂.liftAt n' m) := by
  simp [mem_boundedFormula]

variable {L : Language} [HasMem L]

/-- `t₁ ⊆ t₂`. -/
def Term.subset (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∀' (&-1 ∈' t₁.castSucc ⟹ &-1 ∈' t₂.castSucc)

@[inherit_doc] scoped[STLanguage]
infix:88 " ⊆' " => FirstOrder.Language.Term.subset

/-- `t = ∅` -/
def Term.isEmptyset {α n} (t : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∀' ∼(&-1 ∈' t.castSucc)

/-- `t₁ ∈ t₂ ∪ {t₂}` -/
def Term.memSucc {α n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  t₁ =' t₂ ⊔ t₁ ∈' t₂

/-- `t₁ = t₂ ∪ {t₂}` -/
def Term.eqSucc {α n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∀' (&-1 ∈' t₁.castSucc ⇔ (&-1).memSucc t₂.castSucc)

/-- `∀ x ∈ t, φ (..., x)` -/
@[match_pattern]
def BoundedFormula.allMem {α n}
  (t : L.Term (α ⊕ (Fin n))) (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  ∀' (&-1 ∈' t.castSucc ⟹ φ)

@[inherit_doc, match_pattern] scoped[Language]
notation "∀'∈ " x:arg y:50 => FirstOrder.Language.BoundedFormula.allMem x y

/-- `∃ x ∈ t, φ (..., x)` -/
@[match_pattern]
def BoundedFormula.exMem {α n}
  (t : L.Term (α ⊕ (Fin n))) (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  ∼(∀'∈ t (∼φ))

@[inherit_doc] scoped[Language]
notation "∃'∈ " x:arg y:50 => FirstOrder.Language.BoundedFormula.exMem x y

end Language

end FirstOrder
