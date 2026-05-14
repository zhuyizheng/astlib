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

variable {L : Language} [HasMem L] {α : Type*} {n : ℕ}

/-- `t₁ ⊆ t₂`. -/
def Term.subset (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∀' (&-1 ∈' t₁.castSucc ⟹ &-1 ∈' t₂.castSucc)

@[inherit_doc] scoped[FirstOrder]
infix:88 " ⊆' " => FirstOrder.Language.Term.subset

/-- `t = ∅` -/
def Term.isEmptyset (t : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∀' ∼(&-1 ∈' t.castSucc)


/-- `t₁ = {t₂}` -/
def Term.eqSingleton (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∀' (&-1 ∈' t₁.castSucc ⇔ &-1 =' t₂.castSucc)

/-- `t₁ = {t₂, t₃}` -/
def Term.eqUnoderedPair (t₁ t₂ t₃ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∀' (&-1 ∈' t₁.castSucc ⇔ &-1 =' t₂.castSucc ⊔ &-1 =' t₃.castSucc)

/-- `t₁ ∈ t₂ ∪ {t₃}` -/
def Term.memUnionSingleton (t₁ t₂ t₃ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  t₁ ∈' t₂ ⊔ t₁ =' t₃

/-- `t₁ = t₂ ∪ {t₃}` -/
def Term.eqUnionSingleton (t₁ t₂ t₃ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∀' (&-1 ∈' t₁.castSucc ⇔ (&-1).memUnionSingleton t₂.castSucc t₃.castSucc)

/-- `t₁ ∈ t₂ ∪ {t₂}` -/
def Term.memSucc (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  t₁.memUnionSingleton t₂ t₂

/-- `t₁ = t₂ ∪ {t₂}` -/
def Term.eqSucc (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  t₁.eqUnionSingleton t₂ t₂

/-- `∀ x ∈ t, φ (..., x)` -/
@[match_pattern]
def BoundedFormula.allMem
  (t : L.Term (α ⊕ (Fin n))) (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  ∀' (&-1 ∈' t.castSucc ⟹ φ)

@[inherit_doc, match_pattern] scoped[FirstOrder]
notation "∀'∈ " x:arg y:50 => FirstOrder.Language.BoundedFormula.allMem x y

/-- `∃ x ∈ t, φ (..., x)` -/
@[match_pattern]
def BoundedFormula.exMem
  (t : L.Term (α ⊕ (Fin n))) (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  ∼(∀'∈ t (∼φ))

@[inherit_doc] scoped[FirstOrder]
notation "∃'∈ " x:arg y:50 => FirstOrder.Language.BoundedFormula.exMem x y

/-- `t₁ = (t₂, t₃)` -/
def Term.eqOrderedPair (t₁ t₂ t₃ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∀' (&-1 ∈' t₁.castSucc ⇔
    (&-1).eqSingleton t₂.castSucc ⊔ (&-1).eqUnoderedPair t₂.castSucc t₃.castSucc)

/-- `t` is an ordered pair -/
def Term.isOrderedPair (t : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∃' ∃' (t.castSucc.castSucc.eqOrderedPair &-1 &-2)

/-- `t` is a binary relation -/
def Term.isRel (t : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∀'∈ t (&-1.isOrderedPair)

/-- `t₁` is in the domain of `t₂` -/
def Term.memDom (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∃' (t₂.castSucc.eqOrderedPair t₁.castSucc &-1)

/-- `t₁ = dom t₂` -/
def Term.eqDom (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∀' (&-1 ∈' t₁.castSucc ⇔ &-1.memDom t₂.castSucc)

/-- `t₁` is in the range of `t₂` -/
def Term.memRan (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∃' (t₂.castSucc.eqOrderedPair &-1 t₁.castSucc)

/-- `t₁ = ran t₂` -/
def Term.eqRan (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∀' (&-1 ∈' t₁.castSucc ⇔ &-1.memRan t₂.castSucc)

/-- `t` is a function -/
def Term.isFun (t : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  t.isRel ⊓ ∀'∈ t ∀'∈ t.castSucc ∀' ∀' ∀'
    ( (&-5).eqOrderedPair (&-3) (&-2) ⟹ (&-4).eqOrderedPair (&-3) (&-1) ⟹ &-2 =' &-1)

/-- `t₁ = t₂ t₃` -/
def Term.eqVal (t₁ t₂ t₃ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  ∃'∈ t₁ ((&-1).eqOrderedPair t₂.castSucc t₃.castSucc)

end Language

end FirstOrder
