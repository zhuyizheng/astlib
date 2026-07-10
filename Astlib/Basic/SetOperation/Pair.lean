/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.SUnion
/-!
file docstring
-/

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure}

def IsUnorderedPair (a x y : M) := ∀ z, z ∈ a ↔ z = x ∨ z = y

noncomputable instance : Decidable (∃ a : M, IsUnorderedPair a x y) :=
  Classical.propDecidable _

noncomputable def unorderedPair (x y : M) :=
  dite (∃ a : M, IsUnorderedPair a x y) Classical.choose default

variable (M) in
/- `M` is closed under unordered pairing -/
class ClosedUnderPair : Prop where
  protected closedUnderPair (x y : M) : ∃ a, IsUnorderedPair a x y

@[simp, grind =]
theorem mem_unorderedPair_iff [hM : M.ClosedUnderPair] (x y z : M) :
    z ∈ unorderedPair x y ↔ (z = x ∨ z = y) := by
  convert Classical.choose_spec (hM.closedUnderPair x y) z
  simp [unorderedPair, ClosedUnderPair.closedUnderPair]

theorem eq_unorderedPair_iff [M.Extensional] [M.ClosedUnderPair] (x y z : M) :
    z = unorderedPair x y ↔ (∀ w ∈ z, (w = x ∨ w = y)) ∧ x ∈ z ∧ y ∈ z :=
  ⟨by grind, fun _ ↦ by ext; grind⟩

@[grind! .]
theorem mem_unorderedPair_left [M.ClosedUnderPair] (x y : M) :
    x ∈ unorderedPair x y := by grind

@[grind! .]
theorem mem_unorderedPair_right [M.ClosedUnderPair] (x y : M) :
    y ∈ unorderedPair x y := by grind

@[grind =]
theorem unorderedPair_comm [M.Extensional] [M.ClosedUnderPair] (x y : M) :
    unorderedPair x y = unorderedPair y x := by
  ext; grind

variable (M) in
instance instCommutativeUnodrederPair [M.Extensional] [M.ClosedUnderPair] :
  Std.Commutative (α := M) unorderedPair where
  comm := fun x y ↦ unorderedPair_comm x y

theorem unorderedPair_eq_iff₀ [M.Extensional] [M.ClosedUnderPair] (x y₁ y₂ : M) :
    unorderedPair x y₁ = unorderedPair x y₂ ↔ y₁ = y₂ := by
  grind

theorem unorderedPair_eq_iff [M.Extensional] [M.ClosedUnderPair] (x₁ y₁ x₂ y₂ : M) :
    unorderedPair x₁ y₁ = unorderedPair x₂ y₂ ↔ (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = y₂ ∧ x₂ = y₁) := by
  grind

/-- The ordered pair `(x, y)` -/
noncomputable def orderedPair (x y : M) :=
  unorderedPair (unorderedPair x x) (unorderedPair x y)

@[inherit_doc] scoped[FirstOrder.Language] notation:max "!(" x ", " y ")" =>
  MemStructure.orderedPair x y

@[simp, grind =]
theorem mem_orderedPair_iff [M.ClosedUnderPair] (x y z : M) :
    z ∈ orderedPair x y ↔ (z = unorderedPair x x ∨ z = unorderedPair x y) := by
  simp [orderedPair]

theorem eq_orderedPair_iff [M.Extensional] [M.ClosedUnderPair] (x y z : M) :
    z = orderedPair x y ↔
      (∀ w ∈ z, w = unorderedPair x x ∨ w = unorderedPair x y) ∧
      unorderedPair x x ∈ z ∧ unorderedPair x y ∈ z :=
  ⟨by grind [orderedPair], fun _ ↦ by ext; grind [orderedPair]⟩

@[simp, push, grind =]
theorem orderedPair_eq_orderedPair_iff [M.Extensional] [M.ClosedUnderPair] (x₁ y₁ x₂ y₂ : M) :
    !(x₁, y₁) = !(x₂, y₂) ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  grind [orderedPair]

end MemStructure

section Syntax

variable {L : FirstOrder.Language} [HasMem L] {α : Type*} {n : ℕ}

/-- `t₁ ∈ {t₂, t₃}` -/
def Term.memUnorderedPair (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) :=
  t₁ =' t₂ ⊔ t₁ =' t₃

theorem Term.isDeltaZero_memUnodrederPair (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) :
    (t₁.memUnorderedPair t₂ t₃).IsDeltaZero := by
  simp only [memUnorderedPair]
  exact DeltaZero.isDeltaZero

instance (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) : (t₁.memUnorderedPair t₂ t₃).DeltaZero :=
  ⟨t₁.isDeltaZero_memUnodrederPair t₂ t₃⟩

/-- `t₁ = {t₂, t₃}` -/
def Term.eqUnorderedPair (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) :=
  (∀'∈ t₁ (&-1).memUnorderedPair t₂.castSucc t₃.castSucc) ⊓ (t₂ ∈' t₁ ⊓ t₃ ∈' t₁)

theorem Term.isDeltaZero_eqUnodrederPair (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) :
    (t₁.eqUnorderedPair t₂ t₃).IsDeltaZero := by
  simp only [eqUnorderedPair]
  exact DeltaZero.isDeltaZero

instance (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) : (t₁.eqUnorderedPair t₂ t₃).DeltaZero :=
  ⟨t₁.isDeltaZero_eqUnodrederPair t₂ t₃⟩

/-- `t₁ ∈ (t₂, t₃)` -/
def Term.memOrderedPair (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) :=
  t₁.eqUnorderedPair t₂ t₂ ⊔ t₁.eqUnorderedPair t₂ t₃

theorem Term.isDeltaZero_memOdrederPair (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) :
    (t₁.memOrderedPair t₂ t₃).IsDeltaZero := by
  simp only [memOrderedPair]
  exact DeltaZero.isDeltaZero

instance (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) : (t₁.memOrderedPair t₂ t₃).DeltaZero :=
  ⟨t₁.isDeltaZero_memOdrederPair t₂ t₃⟩

/-- `t₁ = (t₂, t₃)` -/
def Term.eqOrderedPair (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) :=
  (∀'∈ t₁ (&-1).memOrderedPair t₂.castSucc t₃.castSucc) ⊓
    ((∃'∈ t₁ (&-1).eqUnorderedPair t₂.castSucc t₂.castSucc) ⊓
    (∃'∈ t₁ (&-1).eqUnorderedPair t₂.castSucc t₃.castSucc))

theorem Term.isDeltaZero_eqOrderdPair (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) :
    (t₁.eqOrderedPair t₂ t₃).IsDeltaZero := by
  simp only [eqOrderedPair]
  exact DeltaZero.isDeltaZero

instance (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) : (t₁.eqOrderedPair t₂ t₃).DeltaZero :=
  ⟨t₁.isDeltaZero_eqOrderdPair t₂ t₃⟩

-- /-- `t` is an unordered pair -/
-- def Term.isOrderedPair (t : L.Term (α ⊕ Fin n)) :=
--   ∃'∈ t ∃'∈ t.castSucc t.castSucc.castSucc.eqUnorderedPair &-2 &-1

/-- `t₁` is the left component of the ordered pair `t₂` -/
def Term.eqLeft (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  ∃'∈ t₂ ∃'∈ &-1 (t₂.castSucc.castSucc.eqOrderedPair t₁.castSucc.castSucc &-1)

theorem Term.isDeltaZero_eqLeft (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (t₁.eqLeft t₂).IsDeltaZero := by
  simp only [eqLeft]
  exact DeltaZero.isDeltaZero

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁.eqLeft t₂).DeltaZero :=
  ⟨t₁.isDeltaZero_eqLeft t₂⟩

/-- `t₁` is the right component of the ordered pair `t₂` -/
def Term.eqRight (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  ∃'∈ t₂ ∃'∈ &-1 (t₂.castSucc.castSucc.eqOrderedPair &-1 t₁.castSucc.castSucc)

theorem Term.isDeltaZero_eqRight (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (t₁.eqRight t₂).IsDeltaZero := by
  simp only [eqRight]
  exact DeltaZero.isDeltaZero

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁.eqRight t₂).DeltaZero :=
  ⟨t₁.isDeltaZero_eqRight t₂⟩

-- /-- `t` is an ordered pair -/
def Term.isOrderedPair (t : L.Term (α ⊕ Fin n)) :=
  ∃'∈ t ∃'∈ &-1 ((&-1).eqLeft t.castSucc.castSucc)

theorem Term.isDeltaZero_isOrderedPair (t : L.Term (α ⊕ Fin n)) :
    t.isOrderedPair.IsDeltaZero := by
  simp only [isOrderedPair]
  exact DeltaZero.isDeltaZero

instance (t : L.Term (α ⊕ Fin n)) : (t.isOrderedPair).DeltaZero :=
  ⟨t.isDeltaZero_isOrderedPair⟩

/-- `t₁` and `t₂` are ordered pairs with the same left component -/
def Term.sameLeft (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  ∃'∈ t₁ ∃'∈ &-1 ((&-1).eqLeft t₁.castSucc.castSucc ⊓ (&-1).eqLeft t₂.castSucc.castSucc)

theorem Term.isDeltaZero_sameLeft (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (t₁.sameLeft t₂).IsDeltaZero := by
  simp only [sameLeft]
  exact DeltaZero.isDeltaZero

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁.sameLeft t₂).DeltaZero :=
  ⟨t₁.isDeltaZero_sameLeft t₂⟩

/-- `t₁` and `t₂` are ordered pairs with the same right component -/
def Term.sameRight (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  ∃'∈ t₁ ∃'∈ &-1 ((&-1).eqRight t₁.castSucc.castSucc ⊓ (&-1).eqRight t₂.castSucc.castSucc)

theorem Term.isDeltaZero_sameRight (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (t₁.sameRight t₂).IsDeltaZero := by
  simp only [sameRight]
  exact DeltaZero.isDeltaZero

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁.sameRight t₂).DeltaZero :=
  ⟨t₁.isDeltaZero_sameRight t₂⟩

/-- `t₁` and `t₂` are ordered pairs and the right component of `t₁` equals to the left component
of `t₂` -/
def Term.rightEqLeft (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  ∃'∈ t₁ ∃'∈ &-1 ((&-1).eqRight t₁.castSucc.castSucc ⊓ (&-1).eqLeft t₂.castSucc.castSucc)

theorem Term.isDeltaZero_rightEqLeft (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (t₁.rightEqLeft t₂).IsDeltaZero := by
  simp only [rightEqLeft]
  exact DeltaZero.isDeltaZero

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁.rightEqLeft t₂).DeltaZero :=
  ⟨t₁.isDeltaZero_rightEqLeft t₂⟩

/-- `t` is an ordered pair whose left and right components are the same -/
def Term.sameLeftRight (t : L.Term (α ⊕ Fin n)) :=
  t.rightEqLeft t

theorem Term.isDeltaZero_sameLeftRight (t : L.Term (α ⊕ Fin n)) :
    t.sameLeftRight.IsDeltaZero := by
  simp only [sameLeftRight]
  exact DeltaZero.isDeltaZero

instance (t : L.Term (α ⊕ Fin n)) : t.sameLeftRight.DeltaZero :=
  ⟨t.isDeltaZero_sameLeftRight⟩

/-- `t₁` and `t₂` are ordered pairs that switches left and right components -/
def Term.reverseLeftRight (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  t₁.rightEqLeft t₂ ⊓ t₂.rightEqLeft t₁

theorem Term.isDeltaZero_reverseLeftRight (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (t₁.reverseLeftRight t₂).IsDeltaZero := by
  simp only [reverseLeftRight]
  exact DeltaZero.isDeltaZero

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁.reverseLeftRight t₂).DeltaZero :=
  ⟨t₁.isDeltaZero_reverseLeftRight t₂⟩

variable {L : FirstOrder.Language} [HasMem L]

variable {M : MemStructure} (t t₁ t₂ t₃ : M.L.Term (α ⊕ Fin n)) (v : α → M) (xs : Fin n → M)

@[simp]
theorem Term.memUnorderedPair_iff :
    (t₁.memUnorderedPair t₂ t₃)〘v, xs〙 ↔
      t₁〘v, xs〙 = t₂〘v, xs〙 ∨ t₁〘v, xs〙 = t₃〘v, xs〙 := by
  simp [memUnorderedPair]

@[simp]
theorem Term.eqUnorderedPair_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.eqUnorderedPair t₂ t₃)〘v, xs〙 ↔
      t₁〘v, xs〙 = M.unorderedPair (t₂〘v, xs〙) (t₃〘v, xs〙) := by
  simp [M.eq_unorderedPair_iff, eqUnorderedPair]

@[simp]
theorem Term.memOrderedPair_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.memOrderedPair t₂ t₃)〘v, xs〙 ↔
      t₁〘v, xs〙 ∈ !(t₂〘v, xs〙, t₃〘v, xs〙) := by
  simp [memOrderedPair]

@[simp]
theorem Term.eqOrderedPair_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.eqOrderedPair t₂ t₃)〘v, xs〙 ↔
      t₁〘v, xs〙 = !(t₂〘v, xs〙, t₃〘v, xs〙) := by
  simp [M.eq_orderedPair_iff, eqOrderedPair]

@[simp]
theorem Term.eqLeft_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.eqLeft t₂)〘v, xs〙 ↔ ∃ a, t₂〘v, xs〙 = !(t₁〘v, xs〙, a) := by
  simp only [eqLeft, Function.comp_apply, Nat.succ_eq_add_one, castSucc, castLE_castLE,
    realize_exMem, realize'_var', Fin.snoc_last, eqOrderedPair_iff, realize'_castLE,
    Fin.castLE_add_two_castSucc, snoc_snoc_comp_castSucc_castSucc, M.eq_orderedPair_iff]
  grind

@[simp]
theorem Term.eqRight_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.eqRight t₂)〘v, xs〙 ↔ ∃ a, t₂〘v, xs〙 = !(a, t₁〘v, xs〙) := by
  simp only [eqRight, Function.comp_apply, Nat.succ_eq_add_one, castSucc, castLE_castLE,
    realize_exMem, realize'_var', Fin.snoc_last, eqOrderedPair_iff, realize'_castLE,
    Fin.castLE_add_two_castSucc, snoc_snoc_comp_castSucc_castSucc, M.eq_orderedPair_iff]
  exact ⟨by grind, fun ⟨a, _⟩ ↦ ⟨M.unorderedPair a a, by grind⟩⟩

@[simp]
theorem Term.isOrderedPair_iff [M.Extensional] [M.ClosedUnderPair] :
    (t.isOrderedPair)〘v, xs〙 ↔ ∃ a b, t〘v, xs〙 = !(a, b) := by
  simp only [isOrderedPair, Function.comp_apply, castSucc, Nat.succ_eq_add_one, castLE_castLE,
    realize_exMem, realize'_var', Fin.snoc_last, eqLeft_iff, realize'_castLE,
    Fin.castLE_add_two_castSucc, snoc_snoc_comp_castSucc_castSucc, M.eq_orderedPair_iff]
  grind

@[simp]
theorem Term.sameLeft_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.sameLeft t₂)〘v, xs〙 ↔ ∃ a b c, t₁〘v, xs〙 = !(a, b) ∧ t₂〘v, xs〙 = !(a, c) := by
  simp only [sameLeft, Function.comp_apply, castSucc, Nat.succ_eq_add_one, castLE_castLE,
    realize_exMem, realize'_var', Fin.snoc_last, realize_inf, eqLeft_iff, realize'_castLE,
    Fin.castLE_add_two_castSucc, snoc_snoc_comp_castSucc_castSucc, M.eq_orderedPair_iff,
    exists_and_left, exists_and_right]
  grind

@[simp]
theorem Term.sameRight_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.sameRight t₂)〘v, xs〙 ↔ ∃ a b c, t₁〘v, xs〙 = !(a, c) ∧ t₂〘v, xs〙 = !(b, c) := by
  simp only [sameRight, Function.comp_apply, castSucc, Nat.succ_eq_add_one, castLE_castLE,
    realize_exMem, realize'_var', Fin.snoc_last, realize_inf, eqRight_iff, realize'_castLE,
    Fin.castLE_add_two_castSucc, snoc_snoc_comp_castSucc_castSucc, M.eq_orderedPair_iff]
  exact ⟨by grind, fun ⟨a, b, c, _, _⟩ ↦
    ⟨M.unorderedPair a c, by grind, ⟨c, by grind, ⟨a, by assumption⟩, ⟨b, by assumption⟩⟩⟩⟩

@[simp]
theorem Term.rightEqLeft_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.rightEqLeft t₂)〘v, xs〙 ↔ ∃ a b c, t₁〘v, xs〙 = !(a, b) ∧ t₂〘v, xs〙 = !(b, c) := by
  simp only [rightEqLeft, Function.comp_apply, castSucc, Nat.succ_eq_add_one, castLE_castLE,
    realize_exMem, realize'_var', Fin.snoc_last, realize_inf, eqRight_iff, realize'_castLE,
    Fin.castLE_add_two_castSucc, snoc_snoc_comp_castSucc_castSucc, M.eq_orderedPair_iff, eqLeft_iff,
    exists_and_left]
  exact ⟨by grind, fun ⟨a, b, _, ⟨c, _⟩⟩ ↦
    ⟨M.unorderedPair a b, by grind, ⟨b, by grind, ⟨a, by assumption⟩, ⟨c, by assumption⟩⟩⟩⟩

@[simp]
theorem Term.sameLeftRight_iff [M.Extensional] [M.ClosedUnderPair] :
    t.sameLeftRight〘v, xs〙 ↔ ∃ a, t〘v, xs〙 = !(a, a) := by
  simp only [rightEqLeft_iff, sameLeftRight]
  grind

@[simp]
theorem Term.reverseLeftRight_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.reverseLeftRight t₂)〘v, xs〙 ↔ ∃ a b, t₁〘v, xs〙 = !(a, b) ∧ t₂〘v, xs〙 = !(b, a) := by
  simp only [realize_inf, rightEqLeft_iff, reverseLeftRight]
  grind

end Syntax

end FirstOrder.Language
