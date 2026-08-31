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

variable {M : MemStructure} [M.L.ExtraConstantsUnaryRelationsOnly] (x y z x₁ x₂ y₁ y₂ u v : M)
  [M.Extensional] [M.RudClosed]


variable {L L' : Language} [L.HasMem] [L'.HasMem] [L'.ExtraConstantsOnly]

section Basic

@[grind]
def IsRelation (R : M) :=
  ∀ ⦃z : M⦄, z ∈ R → IsOrderedPair z

notation:50 x " [" R:50 "] " y:50 => !(x, y) ∈ R


noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.isRelation (r : L'.RudimentaryTerm n) :
  L'.DeltaZeroBoundedFormula n :=
  ∀₀∈ &0 (ᵣ1).isOrderedPair |>.substBoundRud ![r]


@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isRelation
    (r : M.L'.RudimentaryTerm n) (xs : Fin n → M) :
    r.isRelation.castLHom.toBoundedFormula 〘xs〙 ↔ IsRelation (r.castLHom〘xs〙) := by
  simp [isRelation, IsRelation, snoc_nat]

-- theorem IsRelation.exists_exists {R : M} (hR : IsRelation R)
--     {z : M} (hz : z ∈ R) : ∃ x y, z = !(x, y) := hR hz

lemma IsRelation.subset_iff {R S : M} (hR : IsRelation R) :
    R ⊆ S ↔ ∀ x y : M, x [R] y → x [S] y := by
  refine ⟨by grind, fun h z hz ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := hR hz
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
theorem isRelation_empty : IsRelation (∅ : M) := by
  simp [IsRelation]

@[simp, grind .]
theorem isRelation_sprod : IsRelation (x ×ˢ y) := by
  grind

omit [M.RudClosed] in
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

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.dom
    (r : L'.RudimentaryTerm n) : L'.RudimentaryTerm n :=
  (ᵣ0).iUnion (({(ᵣ1).left} : L'.RudimentaryTerm 2).ifTrue (ᵣ1).isOrderedPair)
    |>.substBoundRud ![r]

noncomputable def dom (R : M) := (ᵣ0).dom.castLHom 〘R〙₁

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_dom (r : M.L'.RudimentaryTerm n) (xs : Fin n → M) :
    r.dom.castLHom〘xs〙 = dom r.castLHom〘xs〙 := by
  simp [dom, RudimentaryTerm.dom]

@[grind =]
theorem mem_dom_iff (R x : M) :
    x ∈ dom R ↔ ∃ y, x [R] y := by
  suffices (∃ z ∈ R, x = (ᵣ1).left.castLHom〘snoc (fun i ↦ R) z〙 ∧ IsOrderedPair z) ↔
      ∃ y, !(x, y) ∈ R by
    simpa [dom, RudimentaryTerm.dom, snoc_nat]
  constructor
  · intro ⟨z, hz₁, hz₂, ⟨x', y', hx'y'⟩⟩
    have := realize_left (r := (ᵣ1 : M.L'.RudimentaryTerm 2))
      (xs := snoc (fun i ↦ R) z) (x := x') (y := y') (by simp [snoc_nat, hx'y'])
    rw [this] at hz₂
    grind
  · intro ⟨y, hy⟩
    exact ⟨!(x, y), hy, realize_left (y := y) (by simp [snoc_nat]) |>.symm, ⟨x, y, rfl⟩⟩

@[simp, grind .]
theorem dom_mono {R S : M} (h : R ⊆ S) :
    dom R ⊆ dom S := by
  grind

@[simp, grind =]
theorem dom_empty :
    dom (∅ : M) = ∅ := by
  ext; grind

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
  obtain ⟨v, hv⟩ := ne_empty_iff _ |>.mp hb
  exact ⟨v, by grind⟩

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.ran
    (r : L'.RudimentaryTerm n) : L'.RudimentaryTerm n :=
  (ᵣ0).iUnion (({(ᵣ1).right} : L'.RudimentaryTerm 2).ifTrue (ᵣ1).isOrderedPair)
    |>.substBoundRud ![r]

noncomputable def ran (R : M) := (ᵣ0).ran.castLHom 〘R〙₁

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_ran (r : M.L'.RudimentaryTerm n) (xs : Fin n → M) :
    r.ran.castLHom〘xs〙 = ran r.castLHom〘xs〙 := by
  simp [ran, RudimentaryTerm.ran]

@[grind =]
theorem mem_ran_iff (R y : M) :
    y ∈ ran R ↔ ∃ x, x [R] y := by
  suffices (∃ z ∈ R, y = (ᵣ1).right.castLHom〘snoc (fun i ↦ R) z〙 ∧ IsOrderedPair z) ↔ ∃ x, !(x, y) ∈ R by
    simpa [ran, RudimentaryTerm.ran, snoc_nat]
  constructor
  · intro ⟨z, hz₁, hz₂, ⟨x', y', hx'y'⟩⟩
    have := realize_right (r := (ᵣ1 : M.L'.RudimentaryTerm 2))
      (xs := snoc (fun i ↦ R) z) (x := x') (y := y') (by simp [snoc_nat, hx'y'])
    rw [this] at hz₂
    grind
  · intro ⟨x, hx⟩
    exact ⟨!(x, y), hx, realize_right (x := x) (by simp [snoc_nat]) |>.symm, ⟨x, y, rfl⟩⟩

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
  obtain ⟨v, hv⟩ := ne_empty_iff _ |>.mp ha
  exact ⟨v, by grind⟩

theorem IsRelation.subset_dom_sprod_ran {R : M} (hR : IsRelation R) :
    R ⊆ dom R ×ˢ ran R := by
  intro z hz
  obtain ⟨x, y, hxy⟩ := hR hz
  simp only [mem_sprod_iff]
  exact ⟨x, by grind, y, by grind, hxy⟩

end Basic

section Comp

-- variable [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
--   [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSUnion]

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.comp
    (r s : L'.RudimentaryTerm n) : L'.RudimentaryTerm n :=
  (ᵣ0).iUnion ((ᵣ1).iUnion (({ᵣ((ᵣ3).left, (ᵣ2).right)} : L'.RudimentaryTerm 4).ifTrue
    ((ᵣ3).isOrderedPair ⊓ (ᵣ2).isOrderedPair ⊓
      (&0 =₀ &1).substBoundRud (![(ᵣ3).right, (ᵣ2).left]))))
    |>.substBoundRud ![r, s]

/-- `R ∘ S` in set theory, denoted by `R !∘ S` in lean -/
noncomputable def comp (R S : M) : M :=
   ((ᵣ0).comp (ᵣ1)).castLHom 〘R, S〙₂

@[inherit_doc] infixr:90 " !∘ "  => FirstOrder.Language.MemStructure.comp

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_comp
    (r s : M.L'.RudimentaryTerm n) (xs : Fin n → M) :
    (r.comp s).castLHom〘xs〙 = r.castLHom〘xs〙 !∘ s.castLHom〘xs〙 := by
  simp only [RudimentaryTerm.comp, isValue, Nat.reduceAdd, Nat.succ_eq_add_one, Function.comp_apply,
    castLHom_substBoundRud, castLHom_iUnion, castLHom_var, castLHom_ifTrue, castLHom_singleton,
    castLHom_orderedPair, castLHom_inf, RudimentaryTerm.realize_substBoundRud, comp]
  congr
  ext i; fin_cases i <;> simp

@[grind =]
theorem mem_comp_iff
    (R S z : M) :
    z ∈ R !∘ S ↔ ∃ a b c : M, z = !(a, c) ∧ (a [S] b) ∧ (b [R] c) := by
  suffices (∃ z_1 ∈ R,
    ∃ z_2 ∈ S,
      z =
          !((ᵣ3).left.castLHom〘snoc (snoc (fun i ↦ (![ᵣ0, ᵣ1] i).castLHom〘R, S〙₂) z_1) z_2〙,
            (ᵣ2).right.castLHom〘snoc (snoc (fun i ↦ (![ᵣ0, ᵣ1] i).castLHom〘R, S〙₂) z_1) z_2〙) ∧
        (IsOrderedPair z_2 ∧ IsOrderedPair z_1) ∧
          (ᵣ3).right.castLHom〘snoc (snoc (fun i ↦ (![ᵣ0, ᵣ1] i).castLHom〘R, S〙₂) z_1) z_2〙 =
            (ᵣ2).left.castLHom〘snoc (snoc (fun i ↦ (![ᵣ0, ᵣ1] i).castLHom〘R, S〙₂) z_1) z_2〙) ↔
  ∃ a b c, z = !(a, c) ∧ !(a, b) ∈ S ∧ !(b, c) ∈ R by
    simpa [comp, RudimentaryTerm.comp, snoc_nat]
  constructor
  · rintro ⟨x, hx, y, hy, rfl, ⟨⟨a, b, hab⟩, ⟨b', c, hb'c⟩⟩, h₃⟩
    use a, b, c
    subst x y
    have hbb' : b = b' := by
      convert h₃
      · symm
        convert realize_right _ (x := a) (y := b)
        simp [snoc_nat]
      · symm
        convert realize_left _ (x := b') (y := c)
        simp [snoc_nat]
    subst hbb'
    simp only [isValue, orderedPair_eq_orderedPair_iff]
    refine ⟨⟨?_, ?_⟩, hy, hx⟩
    · convert realize_left _ (x := a) (y := b)
      simp [snoc_nat]
    · convert realize_right _ (x := b) (y := c)
      simp [snoc_nat]
  · intro ⟨a, b, c, hac, hab, hbc⟩
    subst hac
    refine ⟨!(b, c), hbc, !(a, b), hab, ?_, ⟨⟨a, b, rfl⟩, ⟨b, c, rfl⟩⟩, ?_⟩
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, isValue, orderedPair_eq_orderedPair_iff]
      constructor
      · symm
        convert realize_left _ (x := a) (y := b)
        simp [snoc_nat]
      · symm
        convert realize_right _ (x := b) (y := c)
        simp [snoc_nat]
    · trans b
      · convert realize_right _ (x := a) (y := b)
        simp [snoc_nat]
      · symm
        convert realize_left _ (x := b) (y := c)
        simp [snoc_nat]

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

-- variable [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
--   [M.ClosedUnderDeltaZeroComprehension]

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.id
    (r : L'.RudimentaryTerm n) : L'.RudimentaryTerm n :=
  (ᵣ0).iUnion {ᵣ(ᵣ1, ᵣ1)}
    |>.substBoundRud ![r]

/-- `R ∘ S` in set theory, denoted by `R !∘ S` in lean -/
noncomputable def id (a : M) : M :=
  (ᵣ0).id.castLHom 〘a〙₁

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_id
    (r : M.L'.RudimentaryTerm n) (xs : Fin n → M) :
    r.id.castLHom〘xs〙 = id r.castLHom〘xs〙 := by
  simp [id, RudimentaryTerm.id]

@[grind =]
theorem mem_id_iff (x z : M) : z ∈ id x ↔ ∃ a ∈ x, z = !(a, a) := by
  simp [id, RudimentaryTerm.id, snoc_nat]

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

@[simp, grind =]
theorem dom_id (a : M) : dom (id a) = a := by
  ext z
  rw [mem_dom_iff]
  exact ⟨by grind, fun hz ↦ ⟨z, by grind⟩⟩

@[simp, grind =]
theorem ran_id (a : M) : ran (id a) = a := by
  ext z
  rw [mem_ran_iff]
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

/-- `y [R⁻¹] x` means `x [R] y` -/
noncomputable instance : Inv (L'.RudimentaryTerm n) :=
  ⟨fun r ↦ (ᵣ0).iUnion (({ᵣ((ᵣ1).right, (ᵣ1).left)} : L'.RudimentaryTerm 2).ifTrue ((ᵣ1).isOrderedPair))
    |>.substBoundRud ![r]⟩

-- noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.inv
--     (r : L'.RudimentaryTerm n) : L'.RudimentaryTerm n :=
--   ((ᵣ0).iUnion {ᵣ((ᵣ1).right, (ᵣ1).left)}).ifTrue ((L'.isOrderedPair.substBoundRud ![ᵣ1]))
--     |>.substBoundRud ![r]

/-- `y [R⁻¹] x` means `x [R] y` -/
noncomputable instance : Inv M :=
  ⟨fun R ↦ (ᵣ0)⁻¹.castLHom 〘R〙₁⟩

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_inv
    (r : M.L'.RudimentaryTerm n) (xs : Fin n → M) :
    r⁻¹.castLHom〘xs〙 = (r.castLHom〘xs〙)⁻¹ := by
  simp [Inv.inv]

@[grind =]
theorem mem_inv (R z : M) : z ∈ R⁻¹ ↔ ∃ a b : M, z = !(a, b) ∧ b [R] a := by
  suffices (∃ z_1 ∈ R,
    z = !((ᵣ1).right.castLHom〘snoc (fun i ↦ R) z_1〙, (ᵣ1).left.castLHom〘snoc (fun i ↦ R) z_1〙) ∧ IsOrderedPair z_1) ↔
      ∃ a b, z = !(a, b) ∧ !(b, a) ∈ R by
    simpa [Inv.inv, snoc_nat]
  constructor
  · rintro ⟨w, hw, rfl, ⟨a, b, rfl⟩⟩
    refine ⟨b, a, ?_, hw⟩
    simp only [Nat.reduceAdd, isValue, orderedPair_eq_orderedPair_iff]
    constructor
    · convert realize_right _ (x := a) (y := b)
      simp [snoc_nat]
    · convert realize_left _ (x := a) (y := b)
      simp [snoc_nat]
  · rintro ⟨a, b, rfl, hba⟩
    refine ⟨!(b, a), hba, ?_, ⟨b, a, rfl⟩⟩
    simp only [orderedPair_eq_orderedPair_iff]
    constructor
    · symm
      convert realize_right _ (x := b) (y := a)
      simp [snoc_nat]
    · symm
      convert realize_left _ (x := b) (y := a)
      simp [snoc_nat]

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

end Inv

section Restrict

-- variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

-- variable [M.ClosedUnderDeltaZeroComprehension] [M.Extensional] [M.ClosedUnderPair]

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.restrict₂
    (r s : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  ᵣ0 ∩ ((ᵣ1 : L.RudimentaryTerm 2) ×ˢ (ᵣ1 : L.RudimentaryTerm 2))
    |>.substBoundRud ![r, s]

infix:88 " ↾↾ " => FirstOrder.Language.RudimentaryTerm.restrict₂

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.castLHom_restrict₂
    {M : MemStructure} (r s : M.L'.RudimentaryTerm n) :
    (r ↾↾ s).castLHom = r.castLHom ↾↾ s.castLHom := by
  simp only [restrict₂, isValue, castLHom_substBoundRud, castLHom_inter, castLHom_var,
    castLHom_sprod]
  congr
  ext i; fin_cases i <;> simp

noncomputable def restrict₂ (R a : M) :=
  (ᵣ0 ↾↾ ᵣ1).castLHom 〘R, a〙₂

infix:88 " ↾↾ " => FirstOrder.Language.MemStructure.restrict₂

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_restrict₂
    (r s : M.L.RudimentaryTerm n) (xs : Fin n → M) :
    (r ↾↾ s)〘xs〙 = r〘xs〙 ↾↾ s〘xs〙:= by
  simp [restrict₂, RudimentaryTerm.restrict₂]

@[simp]
theorem restrict₂_eq (R a : M) :
    R ↾↾ a = R ∩ (a ×ˢ a) := by
  simp only [restrict₂, Nat.succ_eq_add_one, Nat.reduceAdd, RudimentaryTerm.restrict₂, Inter.inter,
    isValue, castLHom_substBoundRud, castLHom_sdiff', castLHom_var, castLHom_sprod,
    RudimentaryTerm.realize_substBoundRud, realize_sdiff, realize_basic, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  congr 1

theorem mem_restrict₂_iff (R a z : M) :
    z ∈ R ↾↾ a ↔ z ∈ R ∧ ∃ x ∈ a, ∃ y ∈ a, z = !(x, y) := by
  simp

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

def IsRelationOn (R a : M) := IsRelation R ∧ R ↾↾ a = R

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.isRelationOn (r s : L'.RudimentaryTerm n) :
  L'.DeltaZeroBoundedFormula n :=
  (ᵣ0).isRelation ⊓ (&0 =₀ &1).substBoundRud ![ᵣ0 ↾↾ ᵣ1, ᵣ0] |>.substBoundRud ![r, s]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isRelationOn
    (r s : M.L'.RudimentaryTerm n) (xs : Fin n → M) :
    (r.isRelationOn s).castLHom.toBoundedFormula 〘xs〙 ↔
      IsRelationOn r.castLHom〘xs〙 s.castLHom〘xs〙:= by
  simp [isRelationOn, IsRelationOn]

@[simp, grind .]
theorem IsRelationOn.isRelation {R a : M} (h : IsRelationOn R a) : IsRelation R := h.left

@[simp, grind .]
theorem IsRelationOn.restrict_eq {R a : M} (h : IsRelationOn R a) : R ↾↾ a = R := h.right

-- variable [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderDeltaZeroComprehension]

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

end IsRelationOn

end MemStructure

end FirstOrder.Language
