/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
-- import Astlib.Basic.SetOperation.Inter
import Astlib.Basic.SetOperation.SProd
import Astlib.Basic.SetOperation.Pair.Syntax
/-!
file docstring
-/

open Fin FirstOrder Language MemStructure RudimentaryTerm DeltaZeroBoundedFormula

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M]
  (x y z x₁ x₂ y₁ y₂ u v : M)


section Basic

@[grind]
def IsRelation : Class M := fun R ↦
  ∀ ⦃z : M⦄, z ∈ R → IsOrderedPair z

notation:50 x " [" R:50 "] " y:50 => !(x, y) ∈ R


noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.isRelation
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r : L.RudimentaryTerm n) :
  L.DeltaZeroBoundedFormula n :=
  ∀₀∈ &0 (ᵣ1).isOrderedPair |>.substBoundRud ![r]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r : L.RudimentaryTerm n)
  [r.CharFree] :
  r.isRelation.RelFree := by
  unfold isRelation; infer_instance

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isRelation
    [RudClosed M] [Extensional M] [L.ExtraConstantsUnaryRelationsOnly]
    (r : L.RudimentaryTerm n) [r.CharFree] (xs : Fin n → M) :
    r.isRelation.toBoundedFormula 〘xs〙 ↔ IsRelation (r〘xs〙 : M) := by
  simp [isRelation, IsRelation, snoc_nat]

-- theorem IsRelation.exists_exists {R : M} (hR : IsRelation R)
--     {z : M} (hz : z ∈ R) : ∃ x y, z = !(x, y) := hR hz

lemma IsRelation.subset_iff {R S : M} (hR : IsRelation R) :
    R ⊆ S ↔ ∀ x y : M, x [R] y → x [S] y := by
  refine ⟨by grind, fun h z hz ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := hR hz
  exact hxy ▸ (h x y) (hxy ▸ hz)

@[grind .]
theorem IsRelation.ext [Extensional M] {R S : M} (hR : IsRelation R) (hS : IsRelation S)
    (h : ∀ x y : M, x [R] y ↔ x [S] y) : R = S := by
  refine eq_of_subset_of_subset ?_ ?_
  · simp only [hR.subset_iff]
    grind
  · simp only [hS.subset_iff]
    grind

@[grind .]
theorem IsRelation.eq_iff [Extensional M] {R S : M} (hR : IsRelation R) (hS : IsRelation S) :
    R = S ↔ ∀ x y : M, x [R] y ↔ x [S] y := by
  grind

variable [RudClosed M]

@[simp, grind .]
theorem isRelation_empty : IsRelation (∅ : M) := by
  simp [IsRelation]

@[simp, grind .]
theorem isRelation_sprod : IsRelation (x ×ˢ y) := by
  grind

omit [RudClosed M] in
@[simp, grind .]
theorem IsRelation.subset {R S : M} (hR : IsRelation R) (hSR : S ⊆ R) :
    IsRelation S := by
  grind

theorem IsRelation.inter_right
    {R S : M} (hR : IsRelation R) : IsRelation (R ∩ S) := by
  grind

theorem IsRelation.inter_left
    {R S : M} (hS : IsRelation S) : IsRelation (R ∩ S) := by
  grind

theorem IsRelation.sdiff
    {R S : M} (hR : IsRelation R) : IsRelation (R \ S) := by
  grind

@[simp, grind .]
theorem IsRelation.union {R S : M}
    (hR : IsRelation R) (hS : IsRelation S) : IsRelation (R ∪ S) := by
  grind

@[simp, grind .]
theorem IsRelation.sUnion {X : M}
    (hX : ∀ R ∈ X, IsRelation R) : IsRelation (⋃₀ X) := by
  grind
  -- {M' : MemStructure} [M'.L.ExtraConstantsOnly] [M'.Extensional] [M'.RudClosed]

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.dom₀
    {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 1 :=
  (ᵣ0).iUnion (({(ᵣ1).left} : L.RudimentaryTerm 2).ifTrue (ᵣ1).isOrderedPair)

@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.dom
    {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly]
    (r : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  dom₀.substBoundRud ![r]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
  (dom₀ : L.RudimentaryTerm 1).CharFree := by
  unfold dom₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r : L.RudimentaryTerm n) [r.CharFree] : (r.dom).CharFree := by
  unfold dom; infer_instance

variable [L.ExtraConstantsUnaryRelationsOnly] [Extensional M]

noncomputable def dom : ClassFunction M := fun R ↦ dom₀ 〘R〙₁

instance : (dom : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq dom₀ fun _ ↦ rfl

omit [RudClosed M] in
@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_dom₀ (xs : Fin 1 → M) :
    dom₀〘xs〙 = dom (xs 0) := by
  simp only [dom]
  congr
  ext i; fin_cases i; rfl

@[grind =]
theorem mem_dom_iff (R x : M) :
    x ∈ dom R ↔ ∃ y, x [R] y := by
  suffices (∃ z ∈ R, x = left z ∧ IsOrderedPair z) ↔
      ∃ y, !(x, y) ∈ R by
    simpa [dom, dom₀, snoc_nat]
  constructor
  · rintro ⟨z, hz₁, hz₂, ⟨x', y', rfl⟩⟩
    simp only [left_orderedPair] at hz₂
    exact ⟨y', by rwa [hz₂]⟩
  · intro ⟨y, hy⟩
    exact ⟨!(x, y), hy, by simp [IsOrderedPair]⟩

@[simp, grind .]
theorem dom_mono {R S : M} (h : R ⊆ S) :
    dom R ⊆ dom S := by
  grind

@[simp, grind =]
theorem dom_empty :
    dom (∅ : M) = ∅ := by
  ext; grind

theorem IsRelation.eq_empty_of_dom_eq_empty {R : M} (hR : IsRelation R) (h : dom R = ∅) :
    R = ∅ := by
  ext z
  refine ⟨fun hz ↦ ?_, by simp⟩
  obtain ⟨x, y, rfl⟩ := hR hz
  have hx : x ∈ dom R := by
    simp only [mem_dom_iff]
    exact ⟨y, hz⟩
  simp [h] at hx

theorem dom_union (R S : M) :
    dom (R ∪ S) = dom R ∪ dom S := by
  ext; grind

theorem mem_dom_sUnion_iff (X z : M) :
    z ∈ dom (⋃₀ X) ↔ ∃ R ∈ X, z ∈ dom R := by
  grind

@[simp, grind =]
theorem dom_sprod
    (a : M) {b : M} (hb : b ≠ ∅) :
    dom (a ×ˢ b) = a := by
  ext; rw [mem_dom_iff]
  refine ⟨by grind, fun hz ↦ ?_⟩
  simp only [ne_empty_iff] at hb
  obtain ⟨v, hv⟩ := hb
  exact ⟨v, by grind⟩

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.ran₀
    {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 1 :=
  (ᵣ0).iUnion (({(ᵣ1).right} : L.RudimentaryTerm 2).ifTrue (ᵣ1).isOrderedPair)

@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.ran
    {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly]
    (r : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  ran₀.substBoundRud ![r]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
  (ran₀ : L.RudimentaryTerm 1).CharFree := by
  unfold ran₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r : L.RudimentaryTerm n) [r.CharFree] : (r.ran).CharFree := by
  unfold ran; infer_instance

noncomputable def ran : ClassFunction M := fun R ↦ ran₀ 〘R〙₁

instance : (ran : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq ran₀ fun _ ↦ rfl

omit [RudClosed M] in
@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_ran₀ (xs : Fin 1 → M) :
    ran₀〘xs〙 = ran (xs 0) := by
  simp only [ran]
  congr
  ext i; fin_cases i; rfl

@[grind =]
theorem mem_ran_iff (R y : M) :
    y ∈ ran R ↔ ∃ x, x [R] y := by
  suffices (∃ z ∈ R, y = right z ∧ IsOrderedPair z) ↔
      ∃ x, !(x, y) ∈ R by
    simpa [ran, ran₀, snoc_nat]
  constructor
  · rintro ⟨z, hz₁, hz₂, ⟨x', y', rfl⟩⟩
    simp only [right_orderedPair] at hz₂
    exact ⟨x', by rwa [hz₂]⟩
  · intro ⟨x, hx⟩
    exact ⟨!(x, y), hx, by simp [IsOrderedPair]⟩

@[simp, grind .]
theorem ran_mono {R S : M} (h : R ⊆ S) :
    ran R ⊆ ran S := by
  grind

@[simp, grind =]
theorem ran_empty :
    ran (∅ : M) = ∅ := by
  ext; grind

theorem ran_union (R S : M) :
    ran (R ∪ S) = ran R ∪ ran S := by
  ext; grind

theorem mem_ran_sUnion_iff (X z : M) :
    z ∈ ran (⋃₀ X) ↔ ∃ R ∈ X, z ∈ ran R := by
  grind

@[simp, grind =]
theorem ran_sprod
    {a : M} (ha : a ≠ ∅) (b : M) :
    ran (a ×ˢ b) = b := by
  ext; rw [mem_ran_iff]
  refine ⟨by grind, fun hz ↦ ?_⟩
  simp only [ne_empty_iff] at ha
  obtain ⟨v, hv⟩ := ha
  exact ⟨v, by grind⟩

theorem IsRelation.subset_dom_sprod_ran {R : M} (hR : IsRelation R) :
    R ⊆ dom R ×ˢ ran R := by
  intro z hz
  obtain ⟨x, y, hxy⟩ := hR hz
  simp only [mem_sprod_iff]
  exact ⟨x, by grind, y, by grind, hxy⟩

end Basic

section Comp

-- variable [Extensional M] [M.ClosedUnderPair] [M.ClosedUnderSProd]
--   [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSUnion]

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.comp₀
    {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 2 :=
  (ᵣ0).iUnion ((ᵣ1).iUnion (({ᵣ((ᵣ3).left, (ᵣ2).right)} : L.RudimentaryTerm 4).ifTrue
    ((ᵣ3).isOrderedPair ⊓ (ᵣ2).isOrderedPair ⊓
      (&0 =₀ &1).substBoundRud (![(ᵣ3).right, (ᵣ2).left]))))

@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.comp
    {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly]
    (r s : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  comp₀.substBoundRud ![r, s]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
  (comp₀ : L.RudimentaryTerm 2).CharFree := by
  unfold comp₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] : (r.comp s).CharFree := by
  unfold comp; infer_instance

variable [L.ExtraConstantsUnaryRelationsOnly] [Extensional M]

/-- `R ∘ S` in set theory, denoted by `R !∘ S` in lean -/
noncomputable def comp (R S : M) : M :=
   comp₀ 〘R, S〙₂

@[inherit_doc] infixr:90 " !∘ "  => FirstOrder.Language.MemStructure.comp

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_comp₀ (xs : Fin 2 → M) :
    comp₀〘xs〙 = (xs 0 !∘ xs 1 : M) := by
  simp only [comp]
  rw [Matrix.vec_fin_two_eq]

variable [RudClosed M]

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ ys 0 !∘ ys 1) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ comp₀ fun _ _ ↦ rfl

@[grind =]
theorem mem_comp_iff
    (R S z : M) :
    z ∈ R !∘ S ↔ ∃ a b c : M, z = !(a, c) ∧ (a [S] b) ∧ (b [R] c) := by
  suffices (∃ z_1 ∈ R, ∃ z_2 ∈ S, z = !(left z_2, right z_1) ∧ (IsOrderedPair z_2 ∧ IsOrderedPair z_1) ∧ right z_2 = left z_1) ↔
      ∃ a b c, z = !(a, c) ∧ !(a, b) ∈ S ∧ !(b, c) ∈ R by
    simpa [comp, comp₀, snoc_nat]
  constructor
  · rintro ⟨x, hx, y, hy, rfl, ⟨⟨a, b, rfl⟩, ⟨b', c, rfl⟩⟩, h₃⟩
    simp only [right_orderedPair, left_orderedPair] at h₃
    subst h₃
    use a, b, c
    simp [hy, hx]
  · rintro ⟨a, b, c, rfl, hab, hbc⟩
    exact ⟨!(b, c), hbc, !(a, b), hab, by simp, ⟨⟨a, b, rfl⟩, ⟨b, c, rfl⟩⟩, by simp⟩

theorem comp_assoc (R S T : M) : (R !∘ S) !∘ T = R !∘ (S !∘ T) := by
  ext
  simp only [mem_comp_iff, orderedPair_eq_orderedPair_iff, ↓existsAndEq, and_true, exists_and_left,
    exists_eq_left']
  grind

@[simp, grind! .]
theorem isRelation_comp
    (R S : M) : IsRelation (R !∘ S) := by
  grind

@[grind =]
theorem rel_comp (R S a c : M) : (a [R !∘ S] c) ↔ ∃ b : M, a [S] b ∧ b [R] c := by
  grind

@[grind .]
theorem dom_comp_subset (R S : M) : dom (R !∘ S) ⊆ dom S := by
  grind

@[grind .]
theorem ran_comp_subset (R S : M) : ran (R !∘ S) ⊆ ran R := by
  grind

end Comp

section Id

-- variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

-- variable [Extensional M] [M.ClosedUnderPair] [M.ClosedUnderSProd]
--   [M.ClosedUnderDeltaZeroComprehension]

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.id₀
    {L : Language} [L.HasMem] : L.RudimentaryTerm 1 :=
  (ᵣ0).iUnion {ᵣ(ᵣ1, ᵣ1)}

@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.id
    {L : Language} [L.HasMem]
    -- [L.ExtraConstantsUnaryRelationsOnly]
    (r : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  id₀.substBoundRud ![r]

instance {L : Language} [L.HasMem] :
  (id₀ : L.RudimentaryTerm 1).CharFree := by
  unfold id₀; infer_instance

instance {L : Language} [L.HasMem]
  (r : L.RudimentaryTerm n) [r.CharFree] : (r.id).CharFree := by
  unfold RudimentaryTerm.id; infer_instance

/-- The identity relation on `a` -/
noncomputable def id : ClassFunction M := fun a ↦
  id₀ 〘a〙₁

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_id₀ (xs : Fin 1 → M) :
    id₀〘xs〙 = (id (xs 0) : M) := by
  simp only [id]
  congr
  ext i; fin_cases i; rfl

variable [RudClosed M]

@[grind =]
theorem mem_id_iff (x z : M) : z ∈ id x ↔ ∃ a ∈ x, z = !(a, a) := by
  simp [id, id₀]

@[grind .]
theorem eq_of_id {x y z : M} (h : y [id x] z) : y = z := by
  grind

-- @[simp, grind .]
-- theorem rel_id_iff
--     {y z a : M} (hy : y ∈ a) : y [id a] z ↔ y = z := by
--   grind

@[simp, grind .]
theorem id_isRelation (a : M) : IsRelation (id a) := by
  grind

variable [L.ExtraConstantsUnaryRelationsOnly] [Extensional M]

@[simp, grind =]
theorem dom_id (a : M) : dom (id a : M) = a := by
  ext z
  simp only [mem_dom_iff]
  exact ⟨by grind, fun hz ↦ ⟨z, by grind⟩⟩

@[simp, grind =]
theorem ran_id (a : M) : ran (id a) = a := by
  ext z
  simp only [mem_ran_iff]
  exact ⟨by grind, fun hz ↦ ⟨z, by grind⟩⟩

@[simp, grind =]
theorem IsRelation.comp_id
    {R a : M} (hR : IsRelation R) (h : dom R ⊆ a) : R !∘ (id a) = R := by
  ext
  grind

@[simp, grind =]
theorem IsRelation.id_comp
    {R a : M} (hR : IsRelation R) (h : ran R ⊆ a) : (id a) !∘ R = R := by
  ext
  grind

end Id

section Inv

-- variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.inv₀
    {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 1 :=
  (ᵣ0).iUnion (({ᵣ((ᵣ1).right, (ᵣ1).left)} : L.RudimentaryTerm 2).ifTrue ((ᵣ1).isOrderedPair))

/-- `y [R⁻¹] x` means `x [R] y` -/
noncomputable instance
  {L : Language} [L.HasMem]
  [L.ExtraConstantsUnaryRelationsOnly] : Inv (L.RudimentaryTerm n) :=
  ⟨fun r ↦ inv₀.substBoundRud ![r]⟩

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.inv_def
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r : L.RudimentaryTerm n) :
    r⁻¹ = inv₀.substBoundRud ![r] := rfl

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
  (inv₀ : L.RudimentaryTerm 1).CharFree := by
  unfold inv₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r : L.RudimentaryTerm n) [r.CharFree] : (r⁻¹).CharFree := by
  rw [inv_def]; infer_instance

-- noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.inv
--     (r : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
--   ((ᵣ0).iUnion {ᵣ((ᵣ1).right, (ᵣ1).left)}).ifTrue ((L.isOrderedPair.substBoundRud ![ᵣ1]))
--     |>.substBoundRud ![r]

variable [L.ExtraConstantsUnaryRelationsOnly]

/-- `y [R⁻¹] x` means `x [R] y` -/
noncomputable instance : Inv M :=
  ⟨fun R ↦ inv₀ 〘R〙₁⟩

instance [Extensional M] [RudClosed M] : ClassFunction.DeltaZero (fun R ↦ (R⁻¹ : M)) Set.univ :=
  ClassFunction.deltaZero_of_eq inv₀ fun _ ↦ rfl

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_inv₀ (xs : Fin 1 → M) :
    inv₀〘xs〙 = (xs 0)⁻¹ := by
  simp only [Inv.inv]
  congr
  ext i; fin_cases i; rfl

variable [RudClosed M] [Extensional M]

@[grind =]
theorem mem_inv (R z : M) : z ∈ R⁻¹ ↔ ∃ a b : M, z = !(a, b) ∧ b [R] a := by
  suffices(∃ z_1 ∈ R, z = !(right z_1, left z_1) ∧ IsOrderedPair z_1) ↔ ∃ a b, z = !(a, b) ∧ !(b, a) ∈ R by
    simpa [Inv.inv, inv₀, snoc_nat]
  constructor
  · rintro ⟨w, hw, rfl, ⟨a, b, rfl⟩⟩
    exact ⟨b, a, by simp, hw⟩
  · rintro ⟨a, b, rfl, hba⟩
    refine ⟨!(b, a), hba, by simp, ⟨b, a, rfl⟩⟩

@[simp, grind .]
theorem isRelation_inv (R : M) : IsRelation (R⁻¹) := by
  grind

@[simp, grind =]
theorem rel_inv (R a b : M) : a [R⁻¹] b ↔ b [R] a := by
  grind

@[simp, grind =]
theorem inv_inv {R : M} (hR : IsRelation R) : (R⁻¹)⁻¹ = R := by
  grind [isRelation_inv R⁻¹]

theorem inv_comp {R S : M} : (R !∘ S)⁻¹ = S⁻¹ !∘ R⁻¹ := by
  apply IsRelation.ext (isRelation_inv _) (isRelation_comp _ _)
  intro x y
  simp only [mem_inv, orderedPair_eq_orderedPair_iff, ↓existsAndEq, and_true, exists_eq_left']
  grind

theorem dom_inv {R : M} : dom R⁻¹ = ran R := by
  ext; simp [mem_dom_iff, mem_ran_iff]

theorem ran_inv {R : M} : ran R⁻¹ = dom R := by
  ext; simp [mem_dom_iff, mem_ran_iff]

@[simp]
theorem inv_id (a : M) : (id a)⁻¹ = id a := by
  apply IsRelation.ext (isRelation_inv _) (id_isRelation a)
  grind

end Inv

section Restrict

-- variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

-- variable [M.ClosedUnderDeltaZeroComprehension] [Extensional M] [M.ClosedUnderPair]

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.restrict₂₀
    {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 2 :=
  ᵣ0 ∩ ((ᵣ1 : L.RudimentaryTerm 2) ×ˢ (ᵣ1 : L.RudimentaryTerm 2))

@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.restrict₂
    {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly]
    (r s : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  restrict₂₀.substBoundRud ![r, s]

infix:88 " ↾↾ " => FirstOrder.Language.RudimentaryTerm.restrict₂

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
  (restrict₂₀ : L.RudimentaryTerm 2).CharFree := by
  unfold restrict₂₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
  (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] : (r ↾↾ s).CharFree := by
  unfold restrict₂; infer_instance

variable [L.ExtraConstantsUnaryRelationsOnly]

noncomputable def restrict₂ (R a : M) :=
  restrict₂₀ 〘R, a〙₂

infix:88 " ↾↾ " => FirstOrder.Language.MemStructure.restrict₂

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_restrict₂₀ (xs : Fin 2 → M) :
    restrict₂₀〘xs〙 = (xs 0 ↾↾ xs 1 : M) := by
  simp only [restrict₂]
  rw [Matrix.vec_fin_two_eq]

@[simp]
theorem restrict₂_eq (R a : M) :
    R ↾↾ a = R ∩ (a ×ˢ a) := by
  simp [restrict₂, restrict₂₀]

variable [RudClosed M]

theorem mem_restrict₂_iff (R a z : M) :
    z ∈ R ↾↾ a ↔ z ∈ R ∧ ∃ x ∈ a, ∃ y ∈ a, z = !(x, y) := by
  simp

variable [Extensional M]

theorem rel_restrict₂_iff (R x y : M) :
    x [R ↾↾ a] y ↔ x [R] y ∧ x ∈ a ∧ y ∈ a := by
  grind [mem_restrict₂_iff]

theorem restrict₂_subset (R a : M) : R ↾↾ a ⊆ R := by
  grind [mem_restrict₂_iff]

@[simp, grind =]
theorem empty_restrict₂ (a : M) : (∅ : M) ↾↾ a = ∅ := by
  grind [restrict₂_subset]
-- --
@[simp, grind .]
theorem IsRelation.restrict₂ {R : M} (hR : IsRelation R) (a : M) :
    IsRelation (R ↾↾ a) :=
  hR.subset (restrict₂_subset _ _)

theorem restrict₂_eq_inter_sprod (R a : M) :
    R ↾↾ a = R ∩ (a ×ˢ a) := by
  ext; grind [mem_restrict₂_iff]

theorem dom_restrict₂_subset (R a : M) : dom (R ↾↾ a) ⊆ a := by
  grind [mem_restrict₂_iff]

theorem ran_restrict₂_subset (R a : M) : ran (R ↾↾ a) ⊆ a := by
  grind [mem_restrict₂_iff]

@[simp, grind =]
theorem restrict₂_restrict₂
    (R a b : M) : (R ↾↾ a) ↾↾ b = R ↾↾ (a ∩ b) := by
  simp [inter_assoc, sprod_inter_sprod]

@[simp, grind =]
theorem restrict₂_empty (R : M) : (R ↾↾ ∅) = ∅ := by
  ext; grind [mem_restrict₂_iff]

end Restrict

section IsRelationOn

-- variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

variable [L.ExtraConstantsUnaryRelationsOnly]

def IsRelationOn (R a : M) := IsRelation R ∧ R ↾↾ a = R

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.isRelationOn
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r s : L.RudimentaryTerm n) :
  L.DeltaZeroBoundedFormula n :=
  (ᵣ0).isRelation ⊓ (&0 =₀ &1).substBoundRud ![ᵣ0 ↾↾ ᵣ1, ᵣ0] |>.substBoundRud ![r, s]

variable [RudClosed M] [Extensional M]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isRelationOn
    (r s : L.RudimentaryTerm n)
    [r.CharFree] [s.CharFree]
    (xs : Fin n → M) :
    (r.isRelationOn s).toBoundedFormula 〘xs〙 ↔
      IsRelationOn (r〘xs〙 : M) s〘xs〙:= by
  simp only [isRelationOn, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, Function.comp_apply,
    IsRelationOn, restrict₂_eq, inter_eq_left_iff_subset]
  simp [DeltaZeroBoundedFormula.realize_substBoundRud]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] (r s : L.RudimentaryTerm n)
  [r.CharFree] [s.CharFree] :
  (r.isRelationOn s).RelFree := by
  unfold isRelationOn; infer_instance

@[simp, grind .]
theorem IsRelationOn.isRelation {R a : M} (h : IsRelationOn R a) : IsRelation R := h.left

@[simp, grind .]
theorem IsRelationOn.restrict_eq {R a : M} (h : IsRelationOn R a) : R ↾↾ a = R := h.right

-- variable [Extensional M] [M.ClosedUnderPair] [M.ClosedUnderDeltaZeroComprehension]

@[simp, grind .]
theorem IsRelationOn.isSubset {R a : M} (h : IsRelationOn R a) :
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
    (h : ∀ x ∈ a, ∀ y ∈ a, (x [R] y ↔ x [S] y)) : R = S := by
  refine eq_of_subset_of_subset ?_ ?_
  · simp only [hR.subset_iff]
    grind
  · simp only [hS.subset_iff]
    grind

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
theorem isRelationOn_sprod (a : M) :
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

theorem IsRelationOn.union {R S a : M}
    (hR : IsRelationOn R a) (hS : IsRelationOn S a) : IsRelationOn (R ∪ S) a :=
  ⟨by grind, by ext; grind [IsRelationOn, mem_restrict₂_iff]⟩

theorem IsRelationOn.sUnion {X a : M}
    (hX : ∀ R ∈ X, IsRelationOn R a) : IsRelationOn (⋃₀ X) a :=
  ⟨by grind, by ext; grind [IsRelationOn, mem_restrict₂_iff]⟩

theorem IsRelationOn.dom_subset {R a : M}
    (hR : IsRelationOn R a) : dom R ⊆ a := by
  intro x
  grind [mem_restrict₂_iff, hR.restrict_eq]

theorem IsRelationOn.ran_subset {R a : M}
    (hR : IsRelationOn R a) : ran R ⊆ a := by
  intro x
  grind [mem_restrict₂_iff, hR.restrict_eq]

@[grind .]
theorem IsRelationOn.mem_left {R a x y : M} (hR : IsRelationOn R a) (h : x [R] y) : x ∈ a := by
  grind [hR.restrict_eq, mem_restrict₂_iff]

@[grind .]
theorem IsRelationOn.mem_right {R a x y : M} (hR : IsRelationOn R a) (h : x [R] y) : y ∈ a := by
  grind [hR.restrict_eq, mem_restrict₂_iff]

@[simp, grind .]
theorem IsRelationOn.inv {R a : M} (hR : IsRelationOn R a) : IsRelationOn R⁻¹ a :=
  ⟨isRelation_inv R, (isRelation_inv R).restrict₂ a |>.ext (isRelation_inv R) <| by
    grind [rel_restrict₂_iff]⟩

end IsRelationOn

section PredSet

variable [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] {R x y : M}

/-- The set of `R`-predecessors of `x` -/
noncomputable def predSet (R x : M) : M := dom (R ∩ dom R ×ˢ ({x} : M))

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ predSet (ys 0) (ys 1)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂
    (ᵣ0 ∩ (ᵣ0 : L.RudimentaryTerm 2).dom ×ˢ ({ᵣ1} : L.RudimentaryTerm 2)).dom fun _ _ ↦ by
      simp [predSet]

@[simp, grind =]
theorem mem_predSet_iff : y ∈ predSet R x ↔ y [R] x := by
  simp only [predSet, mem_dom_iff, mem_inter_iff, pair_mem_sprod_iff]
  grind

theorem IsRelationOn.predSet_subset {a : M} (hRa : IsRelationOn R a) (x : M) :
    predSet R x ⊆ a := by
  intro y hy
  simp only [mem_predSet_iff] at hy
  exact hRa.mem_left hy

end PredSet

section SetLike

/-- `R` is set-like: the `R`-predecessors of each `x` form a set -/
def Multiclass.IsSetLike (R : Multiclass M 2) : Prop := ∀ x, ∃ p : M, ∀ y, y ∈ p ↔ R ![y, x]

noncomputable instance (R : Multiclass M 2) (x : M) :
    Decidable (∃ p : M, ∀ y, y ∈ p ↔ R ![y, x]) :=
  Classical.propDecidable _

/-- The set of `R`-predecessors of `x`, if it exists -/
noncomputable def Multiclass.predSet (R : Multiclass M 2) : ClassFunction M := fun x ↦
  dite (∃ p : M, ∀ y, y ∈ p ↔ R ![y, x]) Classical.choose fun _ ↦ default

theorem Multiclass.IsSetLike.mem_predSet_iff {R : Multiclass M 2} (hS : R.IsSetLike) {x y : M} :
    y ∈ R.predSet x ↔ R ![y, x] := by
  specialize hS x
  simp only [Multiclass.predSet, hS]
  grind

end SetLike

section OfRel

variable {R x y : M}

/-- The class relation `y [R] x` given by a set `R` -/
def Multiclass.ofRel (R : M) : Multiclass M 2 := fun xs ↦ !(xs 0, xs 1) ∈ R

@[simp]
theorem Multiclass.ofRel_iff : Multiclass.ofRel R ![y, x] ↔ y [R] x := .rfl

instance [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] :
    (Multiclass.ofRel R).DeltaZero Set.univ := by
  have : Multiclass.ofRel R = ((&0 ∈₀ &1).substBoundRud ![ᵣ(ᵣ0, ᵣ1), ᵣ2] :
      L.DeltaZeroBoundedFormula 3).toBoundedFormula.multiclass.slice ![R] := by
    funext xs
    simp [Multiclass.ofRel, append_right_eq_snoc, snoc_nat]
  rw [this]
  infer_instance

variable [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M]

theorem Multiclass.isSetLike_ofRel : (Multiclass.ofRel R).IsSetLike :=
  fun x ↦ ⟨MemStructure.predSet R x, by simp⟩

@[simp]
theorem Multiclass.predSet_ofRel_apply (x : M) :
    (Multiclass.ofRel R).predSet x = MemStructure.predSet R x := by
  ext y
  simp only [isSetLike_ofRel.mem_predSet_iff, MemStructure.mem_predSet_iff, ofRel_iff]

instance : (Multiclass.ofRel R).predSet.Sigma 1 Set.univ := by
  have h : (Multiclass.ofRel R).predSet = fun x ↦ MemStructure.predSet R x :=
    funext Multiclass.predSet_ofRel_apply
  rw [h]
  infer_instance

end OfRel

end MemStructure

end FirstOrder.Language
