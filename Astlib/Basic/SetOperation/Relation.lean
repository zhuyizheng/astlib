import Astlib.Basic.SetOperation.SProd

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
  {∈ ⋃₀ (⋃₀ R) | ∃'∈ &0 (&2).eqLeft (&3) 〘R〙₀}

variable [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSUnion]

@[grind =]
theorem mem_dom_iff [M.Extensional] [M.ClosedUnderPair] (R x : M) :
    x ∈ dom R ↔ ∃ y, x [R] y := by
  suffices ∀ y, x [R] y → ∃ z, (∃ w ∈ R, z ∈ w) ∧ x ∈ z by simpa [dom]
  exact fun y _ ↦ ⟨unorderedPair x y, ⟨!(x, y), by grind [orderedPair]⟩, by grind⟩

@[simp, grind .]
theorem dom_mono [M.Extensional] [M.ClosedUnderPair] {R S : M} (h : R ⊆ S) :
    dom R ⊆ dom S := by
  grind

@[simp, grind =]
theorem dom_empty [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair] :
    dom (∅ : M) = ∅ := by
  ext; grind

theorem dom_union [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair] (R S : M) :
    dom (R ∪ S) = dom R ∪ dom S := by
  ext; grind

theorem mem_dom_sUnion_iff [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair] (X z : M) :
    z ∈ dom (⋃₀ X) ↔ ∃ R ∈ X, z ∈ dom R := by
  grind

@[simp, grind =]
theorem dom_sprod [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    (a : M) {b : M} (hb : b ≠ ∅) :
    dom (a ×ˢ b) = a := by
  ext; rw [mem_dom_iff]
  refine ⟨by grind, fun hz ↦ ?_⟩
  obtain ⟨v, hv⟩ := ne_empty_iff _ |>.mp hb
  exact ⟨v, by grind⟩

noncomputable def ran (R : M) :=
  {∈ ⋃₀ (⋃₀ R) | ∃'∈ &0 (&2).eqRight (&3) 〘R〙₀}

@[grind =]
theorem mem_ran_iff [M.Extensional] [M.ClosedUnderPair] (R y : M) :
    y ∈ ran R ↔ ∃ x, x [R] y := by
  suffices ∀ x, x [R] y → ∃ z, (∃ w ∈ R, z ∈ w) ∧ y ∈ z by simpa [ran]
  exact fun x _ ↦ ⟨unorderedPair x y, ⟨!(x, y), by grind [orderedPair]⟩, by grind⟩

@[simp, grind .]
theorem ran_mono [M.Extensional] [M.ClosedUnderPair] {R S : M} (h : R ⊆ S) :
    ran R ⊆ ran S := by
  grind

@[simp, grind =]
theorem ran_empty [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair] :
    ran (∅ : M) = ∅ := by
  ext; grind

theorem ran_union [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair] (R S : M) :
    ran (R ∪ S) = ran R ∪ ran S := by
  ext; grind

theorem mem_ran_sUnion_iff [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair] (X z : M) :
    z ∈ ran (⋃₀ X) ↔ ∃ R ∈ X, z ∈ ran R := by
  grind

@[simp, grind =]
theorem ran_sprod [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair] [M.ClosedUnderSProd]
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
  {∈ dom S ×ˢ ran R |
    ∃'∈ &0 ∃'∈ &1 ((&4).sameLeft &3 ⊓ (&5).sameRight &3 ⊓ (&4).rightEqLeft (&5)) 〘![S, R]〙}

@[inherit_doc] infixr:90 " !∘ "  => FirstOrder.Language.MemStructure.comp

@[grind =]
theorem mem_comp
    (R S z : M) :
    z ∈ R !∘ S ↔ ∃ a b c : M, z = !(a, c) ∧ (a [S] b) ∧ (b [R] c) := by
  suffices ((∃ u ∈ dom S, ∃ v ∈ ran R, z = !(u, v)) ∧
    ∃ x x_1, x [S] x_1 ∧ ∃ x_2 x_3, x_1 [R] x_3 ∧ (∃ x_4, z = !(x, x_4)) ∧ z = !(x_2, x_3))
    ↔ ∃ a b c, z = !(a, c) ∧ a [S] b ∧ b [R] c by
    simpa [MemStructure.comp, mem_comprehension_iff]
  refine ⟨by grind, fun ⟨a, b, c, hz, hab, hbc⟩ ↦ ?_⟩
  exact ⟨⟨a, by grind, c, by grind, hz⟩, ⟨a, b, hab, a, c, hbc, ⟨⟨c, hz⟩, hz⟩⟩⟩

theorem comp_assoc
    (R S T : M) :
    (R !∘ S) !∘ T = R !∘ (S !∘ T) := by
  ext
  grind

@[simp, grind! .]
theorem isRelation_comp
    (R S : M) : IsRelation (R !∘ S) := by
  grind [IsRelation]

@[grind =]
theorem rel_comp
    (R S a c : M) :
    (a [R !∘ S] c) ↔ ∃ b : M, a [S] b ∧ b [R] c := by
  grind

theorem dom_comp_subset (R S : M) :
    dom (R !∘ S) ⊆ dom S := by
  grind

theorem ran_comp_subset (R S : M) :
    ran (R !∘ S) ⊆ ran R := by
  grind

end Comp

section Id

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

variable [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
  [M.ClosedUnderDeltaZeroComprehension]

/-- The set of `!(x, x)` for `x ∈ a` -/
noncomputable def id (a : M) : M :=
  {∈ a ×ˢ a | (&1).sameLeftRight}

@[grind =]
theorem mem_id
    (x z : M) :
    z ∈ id x ↔ ∃ a ∈ x, z = !(a, a) := by
  simp only [id, Fin.isValue, Function.comp_apply, mem_comprehension_iff, mem_sprod_iff,
    Nat.reduceAdd, Pi.default_def, Term.rightEqLeft_iff, Term.realize_var, Sum.elim_inr,
    Fin.snoc_nat, Fin.coe_ofNat_eq_mod, Nat.mod_succ, lt_self_iff_false, ↓reduceDIte,
    exists_and_left]
  grind

@[simp, grind .]
theorem eq_of_id
    {x y z : M} (h : y [id x] z) : y = z := by
  grind

@[simp, grind .]
theorem id_isRelation
    (a : M) : IsRelation (id a) := by
  grind [IsRelation]

@[simp, grind =]
theorem IsRelation.comp_id [M.ClosedUnderSUnion]
    {R a : M} (hR : IsRelation R) (h : dom R ⊆ a) :
    R !∘ (id a) = R := by
  grind

@[simp, grind =]
theorem IsRelation.id_comp [M.ClosedUnderSUnion]
    {R a : M} (hR : IsRelation R) (h : ran R ⊆ a) :
    (id a) !∘ R = R := by
  grind

end Id

section Inv

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

variable [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] [M.ClosedUnderSProd]
  [M.ClosedUnderDeltaZeroComprehension]

/-- `y [R⁻¹] x` means `x [R] y` -/
noncomputable instance : Inv M :=
  ⟨fun R ↦ {∈ ran R ×ˢ dom R | ∃'∈ &0 (&2).reverseLeftRight &3 〘R〙₀}⟩

@[grind =]
theorem mem_inv
    (R z : M) :
    z ∈ R⁻¹ ↔ ∃ a b : M, z = !(a, b) ∧ b [R] a := by
  suffices ((∃ u ∈ ran R, ∃ v ∈ dom R, z = !(u, v)) ∧ ∃ x x_1, !(x_1, x) ∈ R ∧ z = !(x, x_1)) ↔
      ∃ a b, z = !(a, b) ∧ !(b, a) ∈ R by
    simpa [Inv.inv, mem_comprehension_iff]
  exact ⟨by grind, fun ⟨a, b, hz, hba⟩ ↦ ⟨⟨a, by grind, b, by grind, hz⟩, ⟨a, b, hba, hz⟩⟩⟩

@[simp, grind .]
theorem isRelation_inv
    (R : M) : IsRelation (R⁻¹) := by
  grind [IsRelation]

@[simp, grind =]
theorem rel_inv
    (R a b : M) :
    a [R⁻¹] b ↔ b [R] a := by
  grind

@[simp, grind =]
theorem inv_inv
    {R : M} (hR : IsRelation R) : (R⁻¹)⁻¹ = R := by
  grind [isRelation_inv R⁻¹]

theorem inv_comp
    {R S : M} : (R !∘ S)⁻¹ = S⁻¹ !∘ R⁻¹ := by
  apply IsRelation.ext (isRelation_inv _) (isRelation_comp _ _)
  intro x y
  simp only [mem_inv, orderedPair_eq_orderedPair_iff, mem_comp, ↓existsAndEq, and_true,
    exists_and_left, exists_eq_left']
  grind

theorem dom_inv {R : M} :
    dom R⁻¹ = ran R := by
  ext; simp [mem_dom_iff, mem_ran_iff]

theorem ran_inv {R : M} :
    ran R⁻¹ = dom R := by
  ext; simp [mem_dom_iff, mem_ran_iff]

end Inv

section Restrict

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

variable [M.ClosedUnderDeltaZeroComprehension]

noncomputable def restrict₂ (R a : M) := R ∩ (a ×ˢ a)

infix:88 " ↾↾ " => FirstOrder.Language.MemStructure.restrict₂

@[simp, grind .]
theorem isRelation_restrict₂ [M.ClosedUnderSProd] (R a : M) :
    IsRelation (R ↾↾ a) :=
  (isRelation_sprod a a).inter_left

-- theorem dom_restrict₂_subset [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair] [M.ClosedUnderSProd]
--     (R a : M) : dom (R ↾↾ a) ⊆ a := by
--   convert dom_mono (R := R ↾↾ a) (S := a ×ˢ a) (by grind [restrict₂])
--   grind

-- theorem ran_restrict₂_subset [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair] [M.ClosedUnderSProd]
--     (R a : M) : ran (R ↾↾ a) ⊆ a := by
--   convert ran_mono (R := R ↾↾ a) (S := a ×ˢ a) (by grind [restrict₂])
--   grind

@[simp, grind =]
theorem restrict₂_restrict₂ [M.Extensional] [M.ClosedUnderPair]
    [M.ClosedUnderSProd]
    (R a b : M) : (R ↾↾ a) ↾↾ b = R ↾↾ (a ∩ b) := by
  simp only [restrict₂, inter_assoc]
  congr
  exact sprod_inter_sprod a b a b

@[simp, grind =]
theorem restrict₂_empty [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair]
    [M.ClosedUnderSProd]
    (R : M) : (R ↾↾ ∅) = ∅ := by
  grind [restrict₂]

end Restrict
section IsRelationOn

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

def IsRelationOn (R a : M) := IsRelation R ∧ R ⊆ a ×ˢ a

@[simp, grind .]
theorem IsRelationOn.isRelation {R a : M} (h : IsRelationOn R a) : IsRelation R := h.left

@[simp, grind .]
theorem IsRelationOn.isSubset {R a : M} (h : IsRelationOn R a) : R ⊆ a ×ˢ a := h.right

theorem IsRelationOn.exists_exists [M.ClosedUnderSProd] {R : M} (hR : IsRelationOn R a)
    {z : M} (hz : z ∈ R) : ∃ x ∈ a, ∃ y ∈ a, z = !(x, y) := by
  obtain ⟨x, y, hxy⟩ := hR.isRelation.exists_exists hz
  have := hR.isSubset hz
  rw [hxy, mem_sprod_iff] at this
  grind

theorem IsRelationOn.subset_iff [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
    [M.ClosedUnderSProd]
    {R a : M} (hR : IsRelationOn R a) (S : M) :
    R ⊆ S ↔ ∀ x ∈ a, ∀ y ∈ a, x [R] y → x [S] y := by
  refine ⟨by grind, fun h z hz ↦ ?_⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hR.exists_exists hz
  exact hxy ▸ (h x hx y hy) (hxy ▸ hz)

@[grind .]
theorem IsRelationOn.ext [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
    [M.ClosedUnderSProd]
    {R S a : M} (hR : IsRelationOn R a) (hS : IsRelationOn S a)
    (h : ∀ x ∈ a, ∀ y ∈ a, (x [R] y ↔ x [S] y)) :
    R = S :=
  eq_of_subset_of_subset ((hR.subset_iff _).mpr (by grind)) ((hS.subset_iff _).mpr (by grind))

@[grind .]
theorem IsRelationOn.eq_iff [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
    [M.ClosedUnderSProd]
    {R S a : M} (hR : IsRelationOn R a) (hS : IsRelationOn S a) :
    R = S ↔ ∀ x ∈ a, ∀ y ∈ a, (x [R] y ↔ x [S] y) := by
  grind

@[simp, grind .]
theorem isRelationOn_empty [M.HasEmpty] : IsRelationOn (∅ : M) a := by
  grind [IsRelationOn]

@[simp, grind .]
theorem isRelationOn_restrict₂ [M.ClosedUnderDeltaZeroComprehension]
    [M.ClosedUnderSProd] (R a : M) :
    IsRelationOn (R ↾↾ a) a := by
  grind [IsRelationOn, restrict₂]

@[simp, grind .]
theorem isRelationOn_sprod (a : M) [M.ClosedUnderSProd] : IsRelationOn (a ×ˢ a) a := by
  grind [IsRelationOn]

@[simp, grind .]
theorem IsRelationOn.subset {R S a : M} (hR : IsRelationOn R a) (hSR : S ⊆ R) :
    IsRelationOn S a :=
  ⟨hR.isRelation.subset hSR, by grind⟩

theorem IsRelationOn.inter_right [M.ClosedUnderDeltaZeroComprehension]
    {R S a : M} (hR : IsRelationOn R a) : IsRelationOn (R ∩ S) a := by
  grind

theorem IsRelationOn.inter_left [M.ClosedUnderDeltaZeroComprehension]
    {R S a : M} (hS : IsRelationOn S a) : IsRelationOn (R ∩ S) a := by
  grind

theorem IsRelationOn.sdiff [M.ClosedUnderDeltaZeroComprehension]
    {R S a : M} (hR : IsRelationOn R a) : IsRelationOn (R \ S) a := by
  grind

theorem IsRelationOn.union [M.ClosedUnderSUnion] [M.ClosedUnderPair] {R S a : M}
    (hR : IsRelationOn R a) (hS : IsRelationOn S a) : IsRelationOn (R ∪ S) a := by
  grind [IsRelationOn, IsRelation]

theorem IsRelationOn.sUnion [M.ClosedUnderSUnion] [M.ClosedUnderPair] {X a : M}
    (hX : ∀ R ∈ X, IsRelationOn R a) : IsRelationOn (⋃₀ X) a := by
  grind [IsRelationOn, IsRelation]

theorem IsRelationOn.dom_subset [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair]
    [M.ClosedUnderSProd] [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSUnion]
    {R a : M}
    (hR : IsRelationOn R a) : dom R ⊆ a := by
  convert dom_mono (R := R) (S := a ×ˢ a) (by grind)
  grind

theorem IsRelationOn.ran_subset [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair]
    [M.ClosedUnderSProd] [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSUnion]
    {R a : M}
    (hR : IsRelationOn R a) : ran R ⊆ a := by
  convert ran_mono (R := R) (S := a ×ˢ a) (by grind)
  grind

end IsRelationOn

end FirstOrder.Language.MemStructure
