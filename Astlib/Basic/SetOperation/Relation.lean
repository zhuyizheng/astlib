/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.SProd
/-!
file docstring
-/

open Fin

namespace FirstOrder.Language.MemStructure

section Basic

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

def IsRelation (R : M) :=
  ∀ ⦃z : M⦄, z ∈ R → ∃ x y, z = !(x, y)

notation:50 x " [" R:50 "] " y:50 => !(x, y) ∈ R

theorem IsRelation.exists_exists {R : M} (hR : IsRelation R)
    {z : M} (hz : z ∈ R) : ∃ x y, z = !(x, y) := hR hz

lemma IsRelation.subset_iff [M.Extensional] {R S : M} (hR : IsRelation R) :
    R ⊆ S ↔ ∀ x y : M, x [R] y → x [S] y := by
  refine ⟨by grind, fun h z hz ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := hR.exists_exists hz
  exact hxy ▸ (h x y) (hxy ▸ hz)

@[grind .]
theorem IsRelation.ext [M.Extensional] {R S : M} (hR : IsRelation R) (hS : IsRelation S)
    (h : ∀ x y : M, x [R] y ↔ x [S] y) : R = S :=
  eq_of_subset_of_subset (hR.subset_iff.mpr (by grind)) (hS.subset_iff.mpr (by grind))

@[grind .]
theorem IsRelation.eq_iff [M.Extensional] {R S : M} (hR : IsRelation R) (hS : IsRelation S) :
    R = S ↔ ∀ x y : M, x [R] y ↔ x [S] y := by
  grind

@[simp, grind .]
theorem isRelation_empty [M.HasEmpty] : IsRelation (∅ : M) := by
  simp [IsRelation]

@[simp, grind .]
theorem isRelation_sprod [M.ClosedUnderSProd] : IsRelation (x ×ˢ y) := by
  grind [IsRelation]

@[simp, grind .]
theorem IsRelation.subset {R S : M} (hR : IsRelation R) (hSR : S ⊆ R) :
    IsRelation S := by
  grind [IsRelation]

theorem IsRelation.inter_right [M.ClosedUnderDeltaZeroComprehension]
    {R S : M} (hR : IsRelation R) : IsRelation (R ∩ S) := by
  grind

theorem IsRelation.inter_left [M.ClosedUnderDeltaZeroComprehension]
    {R S : M} (hS : IsRelation S) : IsRelation (R ∩ S) := by
  grind

theorem IsRelation.sdiff [M.ClosedUnderDeltaZeroComprehension]
    {R S : M} (hR : IsRelation R) : IsRelation (R \ S) := by
  grind

@[simp, grind .]
theorem IsRelation.union [M.ClosedUnderSUnion] [M.ClosedUnderPair] {R S : M}
    (hR : IsRelation R) (hS : IsRelation S) : IsRelation (R ∪ S) := by
  grind [IsRelation]

@[simp, grind .]
theorem IsRelation.sUnion [M.ClosedUnderSUnion] [M.ClosedUnderPair] {X : M}
    (hX : ∀ R ∈ X, IsRelation R) : IsRelation (⋃₀ X) := by
  grind [IsRelation]

noncomputable def dom (R : M) :=
  (∃'∈ &0 (&1).eqLeft (&2))〘R, ∈ ⋃₀ (⋃₀ R)〙₀

variable [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSUnion]

@[grind =]
theorem mem_dom_iff [M.Extensional] [M.ClosedUnderPair] (R x : M) :
    x ∈ dom R ↔ ∃ y, x [R] y := by
  suffices ∀ (x_1 : ↑M), !(x, x_1) ∈ R → ∃ y, (∃ y_1 ∈ R, y ∈ y_1) ∧ x ∈ y by
    simpa [dom, mem_sUnion_iff]
  exact fun y hy ↦ ⟨{x, y}, by grind⟩

@[simp, grind .]
theorem dom_mono [M.Extensional] [M.ClosedUnderPair] {R S : M} (h : R ⊆ S) :
    dom R ⊆ dom S := by
  grind

@[simp, grind =]
theorem dom_empty [M.Extensional] [M.ClosedUnderPair] :
    dom (∅ : M) = ∅ := by
  ext; grind

theorem dom_union [M.Extensional] [M.ClosedUnderPair] (R S : M) :
    dom (R ∪ S) = dom R ∪ dom S := by
  ext; grind

theorem mem_dom_sUnion_iff [M.Extensional] [M.ClosedUnderPair] (X z : M) :
    z ∈ dom (⋃₀ X) ↔ ∃ R ∈ X, z ∈ dom R := by
  grind

@[simp, grind =]
theorem dom_sprod [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    (a : M) {b : M} (hb : b ≠ ∅) :
    dom (a ×ˢ b) = a := by
  ext; rw [mem_dom_iff]
  refine ⟨by grind, fun hz ↦ ?_⟩
  obtain ⟨v, hv⟩ := ne_empty_iff _ |>.mp hb
  exact ⟨v, by grind⟩

noncomputable def ran (R : M) :=
  (∃'∈ &0 (&1).eqRight (&2))〘R, ∈ ⋃₀ (⋃₀ R)〙₀

@[grind =]
theorem mem_ran_iff [M.Extensional] [M.ClosedUnderPair] (R y : M) :
    y ∈ ran R ↔ ∃ x, x [R] y := by
  suffices ∀ (x : ↑M), !(x, y) ∈ R → ∃ y_1, (∃ y ∈ R, y_1 ∈ y) ∧ y ∈ y_1 by
    simpa [ran, mem_sUnion_iff]
  exact fun x _ ↦ ⟨{x, y}, by grind⟩

@[simp, grind .]
theorem ran_mono [M.Extensional] [M.ClosedUnderPair] {R S : M} (h : R ⊆ S) :
    ran R ⊆ ran S := by
  grind

@[simp, grind =]
theorem ran_empty [M.Extensional] [M.ClosedUnderPair] :
    ran (∅ : M) = ∅ := by
  ext; grind

theorem ran_union [M.Extensional] [M.ClosedUnderPair] (R S : M) :
    ran (R ∪ S) = ran R ∪ ran S := by
  ext; grind

theorem mem_ran_sUnion_iff [M.Extensional] [M.ClosedUnderPair] (X z : M) :
    z ∈ ran (⋃₀ X) ↔ ∃ R ∈ X, z ∈ ran R := by
  grind

@[simp, grind =]
theorem ran_sprod [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    {a : M} (ha : a ≠ ∅) (b : M) :
    ran (a ×ˢ b) = b := by
  ext; rw [mem_ran_iff]
  refine ⟨by grind, fun hz ↦ ?_⟩
  obtain ⟨v, hv⟩ := ne_empty_iff _ |>.mp ha
  exact ⟨v, by grind⟩

theorem IsRelation.subset_dom_sprod_ran [M.Extensional] [M.ClosedUnderPair]
    [M.ClosedUnderSProd] {R : M} (hR : IsRelation R) : R ⊆ dom R ×ˢ ran R := by
  intro z hz
  obtain ⟨x, y, hxy⟩ := hR.exists_exists hz
  simp only [mem_sprod_iff]
  exact ⟨x, by grind, y, by grind, hxy⟩

end Basic

section Comp

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

variable [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
  [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSUnion]

/-- `R ∘ S` in set theory, denoted by `R !∘ S` in lean -/
noncomputable def comp (R S : M) : M :=
  (∃'∈ &0 ∃'∈ &1 ((&3).sameLeft &2 ⊓ (&4).sameRight &2 ⊓ (&3).rightEqLeft (&4)))
    〘![S, R], ∈ dom S ×ˢ ran R 〙

@[inherit_doc] infixr:90 " !∘ "  => FirstOrder.Language.MemStructure.comp

@[grind =]
theorem mem_comp
    (R S z : M) :
    z ∈ R !∘ S ↔ ∃ a b c : M, z = !(a, c) ∧ (a [S] b) ∧ (b [R] c) := by
  suffices ((∃ u ∈ dom S, ∃ v ∈ ran R, z = !(u, v)) ∧
      ∃ a b c a_1, !(a_1, a) ∈ S ∧ !(a, c) ∈ R ∧ (∃ x, z = !(a_1, x)) ∧ z = !(b, c)) ↔
        ∃ a b c, z = !(a, c) ∧ !(a, b) ∈ S ∧ !(b, c) ∈ R by
    simpa [MemStructure.comp]
  grind

theorem comp_assoc (R S T : M) : (R !∘ S) !∘ T = R !∘ (S !∘ T) := by
  ext
  grind

@[simp, grind! .]
theorem isRelation_comp
    (R S : M) : IsRelation (R !∘ S) := by
  grind [IsRelation]

@[grind =]
theorem rel_comp (R S a c : M) : (a [R !∘ S] c) ↔ ∃ b : M, a [S] b ∧ b [R] c := by
  grind

theorem dom_comp_subset (R S : M) : dom (R !∘ S) ⊆ dom S := by
  grind

theorem ran_comp_subset (R S : M) : ran (R !∘ S) ⊆ ran R := by
  grind

end Comp

section Id

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

variable [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
  [M.ClosedUnderDeltaZeroComprehension]

/-- The set of `!(x, x)` for `x ∈ a` -/
noncomputable def id (a : M) : M :=
  (&0).sameLeftRight〘∈ a ×ˢ a〙

@[grind =]
theorem mem_id (x z : M) : z ∈ id x ↔ ∃ a ∈ x, z = !(a, a) := by
  simp only [id, isValue, Function.comp_apply, mem_comprehension_empty_one_iff, mem_sprod_iff,
    Pi.default_def, Nat.reduceAdd, Term.sameLeftRight_iff, Term.realize'_var', snoc_nat,
    val_eq_zero, lt_self_iff_false, ↓reduceDIte]
  grind

@[grind .]
theorem eq_of_id {x y z : M} (h : y [id x] z) : y = z := by
  grind

-- @[simp, grind .]
-- theorem rel_id_iff
--     {y z a : M} (hy : y ∈ a) : y [id a] z ↔ y = z := by
--   grind

@[simp, grind .]
theorem id_isRelation (a : M) : IsRelation (id a) := by
  grind [IsRelation]

@[simp, grind =]
theorem dom_id [M.ClosedUnderSUnion] (a : M) : dom (id a) = a := by
  ext z
  rw [mem_dom_iff]
  exact ⟨by grind, fun hz ↦ ⟨z, by grind⟩⟩

@[simp, grind =]
theorem ran_id [M.ClosedUnderSUnion] (a : M) : ran (id a) = a := by
  ext z
  rw [mem_ran_iff]
  exact ⟨by grind, fun hz ↦ ⟨z, by grind⟩⟩

@[simp, grind =]
theorem IsRelation.comp_id [M.ClosedUnderSUnion]
    {R a : M} (hR : IsRelation R) (h : dom R ⊆ a) : R !∘ (id a) = R := by
  grind

@[simp, grind =]
theorem IsRelation.id_comp [M.ClosedUnderSUnion]
    {R a : M} (hR : IsRelation R) (h : ran R ⊆ a) : (id a) !∘ R = R := by
  grind

end Id

section Inv

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

variable [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] [M.ClosedUnderSProd]
  [M.ClosedUnderDeltaZeroComprehension]

/-- `y [R⁻¹] x` means `x [R] y` -/
noncomputable instance : Inv M :=
  ⟨fun R ↦ (∃'∈ &0 (&1).reverseLeftRight &2)〘R, ∈ ran R ×ˢ dom R〙₀⟩

@[grind =]
theorem mem_inv (R z : M) : z ∈ R⁻¹ ↔ ∃ a b : M, z = !(a, b) ∧ b [R] a := by
  suffices ((∃ u ∈ ran R, ∃ v ∈ dom R, z = !(u, v)) ∧ ∃ x x_1, !(x_1, x) ∈ R ∧ z = !(x, x_1)) ↔
      ∃ a b, z = !(a, b) ∧ !(b, a) ∈ R by
    simpa [Inv.inv, mem_comprehension_iff]
  exact ⟨by grind, fun ⟨a, b, hz, hba⟩ ↦ ⟨⟨a, by grind, b, by grind, hz⟩, ⟨a, b, hba, hz⟩⟩⟩

@[simp, grind .]
theorem isRelation_inv (R : M) : IsRelation (R⁻¹) := by
  grind [IsRelation]

@[simp, grind =]
theorem rel_inv (R a b : M) : a [R⁻¹] b ↔ b [R] a := by
  grind

@[simp, grind =]
theorem inv_inv {R : M} (hR : IsRelation R) : (R⁻¹)⁻¹ = R := by
  grind [isRelation_inv R⁻¹]

theorem inv_comp {R S : M} : (R !∘ S)⁻¹ = S⁻¹ !∘ R⁻¹ := by
  apply IsRelation.ext (isRelation_inv _) (isRelation_comp _ _)
  intro x y
  simp only [mem_inv, orderedPair_eq_orderedPair_iff, mem_comp, ↓existsAndEq, and_true,
    exists_and_left, exists_eq_left']
  grind

theorem dom_inv {R : M} : dom R⁻¹ = ran R := by
  ext; simp [mem_dom_iff, mem_ran_iff]

theorem ran_inv {R : M} : ran R⁻¹ = dom R := by
  ext; simp [mem_dom_iff, mem_ran_iff]

end Inv

section Restrict

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

variable [M.ClosedUnderDeltaZeroComprehension] [M.Extensional] [M.ClosedUnderPair]

noncomputable def restrict₂ (R a : M) :=
  ((∃'∈ &0 (&2).eqLeft &1) ⊓ (∃'∈ &0 (&2).eqRight &1)) 〘a, ∈ R〙₀

infix:88 " ↾↾ " => FirstOrder.Language.MemStructure.restrict₂

theorem mem_restrict₂_iff (R a z : M) :
    z ∈ R ↾↾ a ↔ z ∈ R ∧ ∃ x ∈ a, ∃ y ∈ a, z = !(x, y) := by
  suffices z ∈ R → (((∃ x ∈ a, ∃ x_1, z = !(x, x_1)) ∧ ∃ x ∈ a, ∃ x_1, z = !(x_1, x)) ↔
    ∃ x ∈ a, ∃ y ∈ a, z = !(x, y)) by simpa [restrict₂]
  grind

theorem rel_restrict₂_iff (R x y : M) :
    x [R ↾↾ a] y ↔ x [R] y ∧ x ∈ a ∧ y ∈ a := by
  grind [mem_restrict₂_iff]

theorem restrict₂_subset (R a : M) : R ↾↾ a ⊆ R := by
  grind [mem_restrict₂_iff]

@[simp, grind =]
theorem empty_restrict₂ (a : M) : (∅ : M) ↾↾ a = ∅ := by
  grind [restrict₂_subset]
--
@[simp, grind .]
theorem IsRelation.restrict₂ {R : M} (hR : IsRelation R) (a : M) :
    IsRelation (R ↾↾ a) :=
  hR.subset (restrict₂_subset _ _)

theorem restrict₂_eq_inter_sprod [M.ClosedUnderSProd] (R a : M) :
    R ↾↾ a = R ∩ (a ×ˢ a) := by
  ext; grind [mem_restrict₂_iff]

theorem dom_restrict₂_subset [M.ClosedUnderSUnion] (R a : M) : dom (R ↾↾ a) ⊆ a := by
  grind [mem_restrict₂_iff]

theorem ran_restrict₂_subset [M.ClosedUnderSUnion] (R a : M) : ran (R ↾↾ a) ⊆ a := by
  grind [mem_restrict₂_iff]

@[simp, grind =]
theorem restrict₂_restrict₂
    (R a b : M) : (R ↾↾ a) ↾↾ b = R ↾↾ (a ∩ b) := by
  ext; grind [mem_restrict₂_iff]

@[simp, grind =]
theorem restrict₂_empty (R : M) : (R ↾↾ ∅) = ∅ := by
  ext; grind [mem_restrict₂_iff]

end Restrict
section IsRelationOn

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

def IsRelationOn (R a : M) := IsRelation R ∧ R ↾↾ a = R

@[simp, grind .]
theorem IsRelationOn.isRelation {R a : M} (h : IsRelationOn R a) : IsRelation R := h.left

@[simp, grind .]
theorem IsRelationOn.restrict_eq {R a : M} (h : IsRelationOn R a) : R ↾↾ a = R := h.right

variable [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderDeltaZeroComprehension]

@[simp, grind .]
theorem IsRelationOn.isSubset [M.ClosedUnderSProd] {R a : M} (h : IsRelationOn R a) :
    R ⊆ a ×ˢ a := by
  grind [restrict₂_eq_inter_sprod, h.restrict_eq]

theorem IsRelationOn.exists_exists {R a : M} (hR : IsRelationOn R a)
    {z : M} (hz : z ∈ R) : ∃ x ∈ a, ∃ y ∈ a, z = !(x, y) := by
  grind [hR.restrict_eq, mem_restrict₂_iff]

theorem IsRelationOn.subset_iff {R a : M} (hR : IsRelationOn R a) (S : M) :
    R ⊆ S ↔ ∀ x ∈ a, ∀ y ∈ a, x [R] y → x [S] y := by
  refine ⟨by grind, fun h z hz ↦ ?_⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hR.exists_exists hz
  exact hxy ▸ (h x hx y hy) (hxy ▸ hz)

@[grind .]
theorem IsRelationOn.ext {R S a : M} (hR : IsRelationOn R a) (hS : IsRelationOn S a)
    (h : ∀ x ∈ a, ∀ y ∈ a, (x [R] y ↔ x [S] y)) : R = S :=
  eq_of_subset_of_subset ((hR.subset_iff _).mpr (by grind)) ((hS.subset_iff _).mpr (by grind))

@[grind .]
theorem IsRelationOn.eq_iff {R S a : M} (hR : IsRelationOn R a) (hS : IsRelationOn S a) :
    R = S ↔ ∀ x ∈ a, ∀ y ∈ a, (x [R] y ↔ x [S] y) := by
  grind

@[simp, grind .]
theorem isRelationOn_empty : IsRelationOn (∅ : M) a := by
  grind [IsRelationOn]

@[simp, grind .]
theorem isRelationOn_restrict₂ {R : M} (hR : IsRelation R) (a : M) :
    IsRelationOn (R ↾↾ a) a := by
  grind [IsRelationOn]

@[simp, grind .]
theorem isRelationOn_sprod [M.ClosedUnderSUnion] (a : M) [M.ClosedUnderSProd] :
    IsRelationOn (a ×ˢ a) a :=
  ⟨by grind, by ext; grind [mem_restrict₂_iff]⟩

@[simp, grind .]
theorem IsRelationOn.subset {R S a : M} (hR : IsRelationOn R a) (hSR : S ⊆ R) :
    IsRelationOn S a :=
  ⟨hR.isRelation.subset hSR, by ext; grind [IsRelationOn, mem_restrict₂_iff]⟩

theorem IsRelationOn.inter_right
    {R S a : M} (hR : IsRelationOn R a) : IsRelationOn (R ∩ S) a := by
  grind

theorem IsRelationOn.inter_left
    {R S a : M} (hS : IsRelationOn S a) : IsRelationOn (R ∩ S) a := by
  grind

theorem IsRelationOn.sdiff
    {R S a : M} (hR : IsRelationOn R a) : IsRelationOn (R \ S) a := by
  grind

theorem IsRelationOn.union [M.ClosedUnderSUnion] {R S a : M}
    (hR : IsRelationOn R a) (hS : IsRelationOn S a) : IsRelationOn (R ∪ S) a :=
  ⟨by grind, by ext; grind [IsRelationOn, mem_restrict₂_iff]⟩

theorem IsRelationOn.sUnion [M.ClosedUnderSUnion] {X a : M}
    (hX : ∀ R ∈ X, IsRelationOn R a) : IsRelationOn (⋃₀ X) a :=
  ⟨by grind, by ext; grind [IsRelationOn, mem_restrict₂_iff]⟩

theorem IsRelationOn.dom_subset [M.ClosedUnderSUnion] {R a : M}
    (hR : IsRelationOn R a) : dom R ⊆ a := by
  grind [mem_restrict₂_iff, hR.restrict_eq]

theorem IsRelationOn.ran_subset [M.ClosedUnderSUnion] {R a : M}
    (hR : IsRelationOn R a) : ran R ⊆ a := by
  grind [mem_restrict₂_iff, hR.restrict_eq]

end IsRelationOn

end MemStructure

section Syntax

variable {L : FirstOrder.Language} [HasMem L] {α : Type*} {n : ℕ} (t t₁ t₂ : L.Term (α ⊕ Fin n))

/-- `t` is a relation -/
def Term.isRelation (t : L.Term (α ⊕ Fin n)) :=
  ∀'∈ t ((&-1).isOrderedPair)


theorem Term.isDeltaZero_isRelation : (t.isRelation).IsDeltaZero := by
  simp only [isRelation]
  exact BoundedFormula.DeltaZero.isDeltaZero

instance : (t.isRelation).DeltaZero := ⟨t.isDeltaZero_isRelation⟩

/-- `t₁ ∈ dom t₂` -/
def Term.memDom (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  ∃'∈ t₂ (t₁.castSucc.eqLeft &-1)

theorem Term.isDeltaZero_memDom : (t₁.memDom t₂).IsDeltaZero := by
  simp only [memDom]
  exact BoundedFormula.DeltaZero.isDeltaZero

instance : (t₁.memDom t₂).DeltaZero := ⟨t₁.isDeltaZero_memDom t₂⟩

/-- `t₁ = dom t₂` -/
def Term.eqDom (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  (∀'∈ t₁ ((&-1).memDom t₂.castSucc)) ⊓
    ∀'∈ t₂ ∀'∈ &-1 ∀'∈ &-1 (&-1.memDom t₂.castSucc.castSucc.castSucc ⟹
    &-1 ∈' t₁.castSucc.castSucc.castSucc)

theorem Term.isDeltaZero_eqDom : (t₁.eqDom t₂).IsDeltaZero := by
  simp only [eqDom]
  exact BoundedFormula.DeltaZero.isDeltaZero

instance : (t₁.eqDom t₂).DeltaZero := ⟨t₁.isDeltaZero_eqDom t₂⟩


variable {M : MemStructure} (v : α → M) (xs : Fin n → M)

variable (t t₁ t₂ : M.L.Term (α ⊕ Fin n))

@[simp]
theorem Term.isRelation_iff [M.Extensional] [M.ClosedUnderPair] :
    t.isRelation〘v, xs〙 ↔ M.IsRelation t〘v, xs〙 := by
  simp [MemStructure.IsRelation, isRelation]

@[simp]
theorem Term.memDom_iff [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSUnion]
    [M.ClosedUnderDeltaZeroComprehension] :
    (t₁.memDom t₂)〘v, xs〙 ↔ t₁〘v, xs〙 ∈ M.dom (t₂〘v, xs〙) := by
  suffices ∀ (x : ↑M),
    !(t₁〘v, xs〙, x) ∈ t₂〘v, xs〙 →
      ∃ y, (∃ y_1 ∈ t₂〘v, xs〙, y ∈ y_1) ∧ t₁〘v, xs〙 ∈ y
    by simpa [MemStructure.dom, memDom, MemStructure.mem_sUnion_iff]
  refine fun w hw ↦ ⟨{t₁〘v, xs〙}, ?_⟩
  simp only [MemStructure.mem_singleton_iff, and_true]
  use !(t₁〘v, xs〙, w)
  simp only [hw, MemStructure.mem_orderedPair_iff, true_and]
  left
  rfl

-- @[simp]
-- theorem Term.eqDom_iff [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSUnion]
--      [M.ClosedUnderSProd] [M.ClosedUnderDeltaZeroComprehension] :
--     (t₁.eqDom t₂)〘v, xs〙 ↔
--     t₁〘v, xs〙 = M.dom (t₂〘v, xs〙) := by
--   -- rw [MemStructure.ext_iff]
--   constructor
--   · intro h
--     simp? [] at h

  -- suffices ∀ (x : ↑M),
  --   !(t₁〘v, xs〙, x) ∈ t₂〘v, xs〙 →
  --     ∃ y, (∃ y_1 ∈ t₂〘v, xs〙, y ∈ y_1) ∧ t₁〘v, xs〙 ∈ y
  --   by simpa [MemStructure.dom]
  -- intro w hw
  -- use {t₁〘v, xs〙}
  -- simp only [MemStructure.mem_singleton_iff, and_true]
  -- use !(t₁〘v, xs〙, w)
  -- simp only [hw, MemStructure.mem_orderedPair_iff, true_and]
  -- left
  -- rfl


end Syntax

end FirstOrder.Language
