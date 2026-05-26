import Astlib.Basic.SetOperation.SProd

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

def IsRelation (R : M) :=
  ∀ ⦃z : M⦄, z ∈ R → ∃ x y, z = !(x, y)

notation:50 x " [" R:50 "] " y:50 => !(x, y) ∈ R

-- export ClosedUnderPair (isRelation)

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

@[simp]
theorem empty_isRelation [M.HasEmpty] : IsRelation (∅ : M) := by
  simp [IsRelation]

@[simp]
theorem sprod_isRelation [M.ClosedUnderSProd] : IsRelation (x ×ˢ y) := by
  grind [IsRelation]

@[simp]
theorem IsRelation.subset {R S : M} (hR : IsRelation R) (hSR : S ⊆ R) :
    IsRelation S := by
  grind [IsRelation]

theorem IsRelation.inter [M.ClosedUnderDeltaZeroComprehension]
    {R S : M} (hR : IsRelation R) : IsRelation (R ∩ S) := by
  grind [IsRelation]

theorem IsRelation.sdiff [M.ClosedUnderDeltaZeroComprehension]
    {R S : M} (hR : IsRelation R) : IsRelation (R \ S) := by
  grind [IsRelation]

theorem IsRelation.union [M.ClosedUnderSUnion] [M.ClosedUnderPair] {R S : M}
    (hR : IsRelation R) (hS : IsRelation S) : IsRelation (R ∪ S) := by
  grind [IsRelation]

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

noncomputable def ran (R : M) :=
  {∈ ⋃₀ (⋃₀ R) | ∃'∈ &0 (&2).eqRight (&3) 〘R〙₀}

@[grind =]
theorem mem_ran_iff [M.Extensional] [M.ClosedUnderPair] (R y : M) :
    y ∈ ran R ↔ ∃ x, x [R] y := by
  suffices ∀ x, x [R] y → ∃ z, (∃ w ∈ R, z ∈ w) ∧ y ∈ z by simpa [ran]
  exact fun x _ ↦ ⟨unorderedPair x y, ⟨!(x, y), by grind [orderedPair]⟩, by grind⟩

theorem IsRelation.subset_dom_sprod_ran [M.Extensional] [M.ClosedUnderPair]
    [M.ClosedUnderSProd] {R : M} (hR : IsRelation R) : R ⊆ dom R ×ˢ ran R := by
  intro z hz
  obtain ⟨x, y, hxy⟩ := hR.exists_exists hz
  simp only [mem_sprod_iff]
  exact ⟨x, by grind, y, by grind, hxy⟩

/-- `R ∘ S` in set theory, denoted by `R !∘ S` in lean -/
noncomputable def comp (R S : M) : M :=
  {∈ dom S ×ˢ ran R |
    ∃'∈ &0 ∃'∈ &1 ((&4).sameLeft &3 ⊓ (&5).sameRight &3 ⊓ (&4).rightEqLeft (&5)) 〘![S, R]〙}

@[inherit_doc] infixr:90 " !∘ "  => FirstOrder.Language.MemStructure.comp

@[grind =]
theorem mem_comp [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    (R S z : M) :
    z ∈ R !∘ S ↔ ∃ a b c : M, z = !(a, c) ∧ (a [S] b) ∧ (b [R] c) := by
  suffices ((∃ u ∈ dom S, ∃ v ∈ ran R, z = !(u, v)) ∧
    ∃ x x_1, x [S] x_1 ∧ ∃ x_2 x_3, x_1 [R] x_3 ∧ (∃ x_4, z = !(x, x_4)) ∧ z = !(x_2, x_3))
    ↔ ∃ a b c, z = !(a, c) ∧ a [S] b ∧ b [R] c by
    simpa [MemStructure.comp, mem_comprehension_iff]
  refine ⟨by grind, fun ⟨a, b, c, hz, hab, hbc⟩ ↦ ?_⟩
  exact ⟨⟨a, by grind, c, by grind, hz⟩, ⟨a, b, hab, a, c, hbc, ⟨⟨c, hz⟩, hz⟩⟩⟩

theorem comp_assoc [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    (R S T : M) :
    (R !∘ S) !∘ T = R !∘ (S !∘ T) := by
  ext
  grind

@[simp, grind! .]
theorem isRelation_comp [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    (R S : M) : IsRelation (R !∘ S) := by
  grind [IsRelation]

@[grind =]
theorem rel_comp [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    (R S a c : M) :
    (a [R !∘ S] c) ↔ ∃ b : M, a [S] b ∧ b [R] c := by
  grind

theorem dom_comp_subset [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd] (R S : M) :
    dom (R !∘ S) ⊆ dom S := by
  grind

theorem ran_comp_subset [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd] (R S : M) :
    ran (R !∘ S) ⊆ ran R := by
  grind

/-- The set of `!(x, x)` for `x ∈ a` -/
noncomputable def id (a : M) : M :=
  {∈ a ×ˢ a | (&1).sameLeftRight}

omit [M.ClosedUnderSUnion] in
@[grind =]
theorem mem_id [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    (x z : M) :
    z ∈ id x ↔ ∃ a ∈ x, z = !(a, a) := by
  simp only [id, Fin.isValue, Function.comp_apply, mem_comprehension_iff, mem_sprod_iff,
    Nat.reduceAdd, Pi.default_def, Term.rightEqLeft_iff, Term.realize_var, Sum.elim_inr,
    Fin.snoc_nat, Fin.coe_ofNat_eq_mod, Nat.mod_succ, lt_self_iff_false, ↓reduceDIte,
    exists_and_left]
  grind

omit [M.ClosedUnderSUnion] in
@[simp, grind .]
theorem eq_of_id [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    {x y z : M} (h : y [id x] z) : y = z := by
  grind

omit [M.ClosedUnderSUnion] in
@[simp, grind .]
theorem id_isRelation [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    (a : M) : IsRelation (id a) := by
  grind [IsRelation]

@[simp, grind =]
theorem IsRelation.comp_id [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    {R a : M} (hR : IsRelation R) (h : dom R ⊆ a) :
    R !∘ (id a) = R := by
  grind

@[simp, grind =]
theorem IsRelation.id_comp [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    {R a : M} (hR : IsRelation R) (h : ran R ⊆ a) :
    (id a) !∘ R = R := by
  grind

/-- `y [R⁻¹] x` means `x [R] y` -/
noncomputable instance : Inv M :=
  ⟨fun R ↦ {∈ ran R ×ˢ dom R | ∃'∈ &0 (&2).reverseLeftRight &3 〘R〙₀}⟩

@[grind =]
theorem mem_inv [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    (R z : M) :
    z ∈ R⁻¹ ↔ ∃ a b : M, z = !(a, b) ∧ b [R] a := by
  suffices ((∃ u ∈ ran R, ∃ v ∈ dom R, z = !(u, v)) ∧ ∃ x x_1, !(x_1, x) ∈ R ∧ z = !(x, x_1)) ↔
      ∃ a b, z = !(a, b) ∧ !(b, a) ∈ R by
    simpa [Inv.inv, mem_comprehension_iff]
  exact ⟨by grind, fun ⟨a, b, hz, hba⟩ ↦ ⟨⟨a, by grind, b, by grind, hz⟩, ⟨a, b, hba, hz⟩⟩⟩

@[simp, grind! .]
theorem isRelation_inv [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    (R : M) : IsRelation (R⁻¹) := by
  grind [IsRelation]

@[simp, grind =]
theorem rel_inv [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    (R a b : M) :
    a [R⁻¹] b ↔ b [R] a := by
  grind

@[simp, grind =]
theorem inv_inv [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    {R : M} (hR : IsRelation R) : (R⁻¹)⁻¹ = R := by
  grind [isRelation_inv R⁻¹]

theorem inv_comp [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
    {R S : M} : (R !∘ S)⁻¹ = S⁻¹ !∘ R⁻¹ := by
  apply IsRelation.ext (isRelation_inv _) (isRelation_comp _ _)
  intro x y
  simp only [mem_inv, orderedPair_eq_orderedPair_iff, mem_comp, ↓existsAndEq, and_true,
    exists_and_left, exists_eq_left']
  grind

theorem dom_inv [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd] {R : M} :
    dom R⁻¹ = ran R := by
  ext; simp [mem_dom_iff, mem_ran_iff]

theorem ran_inv [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd] {R : M} :
    ran R⁻¹ = dom R := by
  ext; simp [mem_dom_iff, mem_ran_iff]

end FirstOrder.Language.MemStructure
