import Astlib.Basic.SetOperation.Relation

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

def IsFunction (f : M) :=
  IsRelation f ∧ ∀ x y₁ y₂, x [f] y₁ → x [f] y₂ → y₁ = y₂

theorem IsFunction.isRelation {f : M} (hf : IsFunction f) : IsRelation f := hf.left

@[simp, grind! .]
theorem IsFunction.eq
    {f x y₁ y₂: M} (hf : IsFunction f) (h₁ : x [f] y₁) (h₂ : x [f] y₂) : y₁ = y₂ := by
  grind [IsFunction]

@[simp]
theorem empty_isFunction [M.HasEmpty] : IsFunction (∅ : M) := by
  simp [IsFunction]

theorem IsFunction.subset {f g : M} (hf : IsFunction f) (hgf : g ⊆ f) :
    IsFunction g := by
  simp only [IsFunction, hf.isRelation.subset hgf, true_and]
  exact fun x y₁ y₂ h₁ h₂ ↦ hf.eq (hgf h₁) (hgf h₂)

noncomputable instance (f x : M) : Decidable (∃ y, x [f] y) :=
  Classical.propDecidable _

noncomputable def val (f x : M) := dite (∃ y : M, x [f] y) Classical.choose default

infix:88 " @ " => FirstOrder.Language.MemStructure.val

@[simp, grind! .]
theorem IsFunction.val_eq_of_rel
    {f x y : M} (hf : IsFunction f) (hxy : x [f] y) : f @ x = y := by
  have : ∃ y, !(x, y) ∈ f := by use y
  grind [val, IsFunction]

theorem IsFunction.exists_val
    {f : M} (hf : IsFunction f)
    {z : M} (hz : z ∈ f) : ∃ x, z = !(x, f @ x) := by
  obtain ⟨x, y, hxy⟩ := hf.isRelation hz
  use x
  convert hxy
  exact val_eq_of_rel hf (by grind)

variable [M.ClosedUnderDeltaZeroComprehension]
    [M.ClosedUnderSUnion] [M.Extensional] [M.ClosedUnderPair]

@[simp]
theorem rel_val
    {f x : M} (hx : x ∈ dom f) : x [f] (f @ x) := by
  grind [val]

lemma IsFunction.subset_iff {f g : M} (hf : IsFunction f) :
    f ⊆ g ↔ ∀ x ∈ dom f, (x [g] (f @ x)) := by
  refine ⟨by grind, fun h z hz ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := hf.exists_val hz
  exact h x (by grind)

@[grind .]
theorem IsFunction.ext {f g : M} (hf : IsFunction f) (hg : IsFunction g)
    (hfg : dom f = dom g)
    (h : ∀ x ∈ dom f, f @ x = g @ x) : f = g :=
  eq_of_subset_of_subset (hf.subset_iff.mpr (by grind)) (hg.subset_iff.mpr (by grind))

@[grind =]
theorem IsFunction.mem_dom_iff {f : M} (x : M) (hf : IsFunction f) :
    x ∈ dom f ↔ x [f] (f @ x) := by
  grind

theorem IsFunction.mem_ran_iff {f : M} (y : M) (hf : IsFunction f) :
    y ∈ ran f ↔ ∃ x ∈ dom f, f @ x = y := by
  rw [M.mem_ran_iff]
  exact exists_congr (by grind)

theorem IsFunction.subset_dom_sprod_ran [M.ClosedUnderSProd] {f : M} (hf : IsFunction f) :
    f ⊆ dom f ×ˢ ran f :=
  hf.isRelation.subset_dom_sprod_ran

@[grind! .]
theorem IsFunction.isFunction_comp [M.ClosedUnderSProd]
    {f g : M} (hf : IsFunction f) (hg : IsFunction g) : IsFunction (f !∘ g) := by
  grind [IsFunction]

@[grind .]
theorem mem_dom_comp [M.ClosedUnderSProd]
    {f g x : M} (hf : IsFunction f) (hg : IsFunction g)
    (hx : x ∈ dom g) (hx' : g @ x ∈ dom x) :
    x ∈ dom (f !∘ g) := by
  rw [mem_dom_iff]
  sorry

@[grind =]
theorem val_comp [M.ClosedUnderSProd]
    {f g x : M} (hf : IsFunction f) (hg : IsFunction g)
    (hx : x ∈ dom g) (hx' : g @ x ∈ dom x) :
    (f !∘ g) @ x = f @ (g @ x) := by
  sorry
  -- suffices ((∃ u ∈ dom S, ∃ v ∈ ran R, z = !(u, v)) ∧
  --   ∃ x x_1, (x [S] x_1) ∧ ∃ x_2 x_3, (x_1 [R] x_3) ∧ (∃ x_4, z = !(x, x_4)) ∧ z = !(x_2, x_3))
  --   ↔ ∃ a b c, z = !(a, c) ∧ (a [S] b) ∧ (b [R] c) by
  --   simpa [MemStructure.comp, mem_comprehension_iff]
  -- refine ⟨by grind, fun ⟨a, b, c, hz, hab, hbc⟩ ↦ ?_⟩
  -- exact ⟨⟨a, by grind, c, by grind, hz⟩, ⟨a, b, hab, a, c, hbc, ⟨⟨c, hz⟩, hz⟩⟩⟩


-- theorem dom_comp_subset [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd] (R S : M) :
--     dom (R !∘ S) ⊆ dom S := by
--   grind

-- theorem ran_comp_subset [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd] (R S : M) :
--     ran (R !∘ S) ⊆ ran R := by
--   grind


omit [M.ClosedUnderSUnion] in
theorem id_isFunction [M.ClosedUnderSProd]
    (a : M) : IsFunction (id a) := by
  grind [IsFunction, id]


-- @[grind =]
-- theorem mem_inv [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
--     (R z : M) :
--     z ∈ R⁻¹ ↔ ∃ a b : M, z = !(a, b) ∧ (b [R] a) := by
--   suffices ((∃ u ∈ ran R, ∃ v ∈ dom R, z = !(u, v)) ∧ ∃ x x_1, !(x_1, x) ∈ R ∧ z = !(x, x_1)) ↔
--       ∃ a b, z = !(a, b) ∧ !(b, a) ∈ R by
--     simpa [Inv.inv, mem_comprehension_iff]
--   exact ⟨by grind, fun ⟨a, b, hz, hba⟩ ↦ ⟨⟨a, by grind, b, by grind, hz⟩, ⟨a, b, hba, hz⟩⟩⟩

-- @[grind! .]
-- theorem isRelation_inv [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
--     (R : M) : IsRelation (R⁻¹) := by
--   grind [IsRelation]

-- @[simp, grind =]
-- theorem rel_inv [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
--     (R a b : M) :
--     (a [R⁻¹] b) ↔ (b [R] a) := by
--   grind

-- @[simp, grind =]
-- theorem inv_inv [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
--     {R : M} (hR : IsRelation R) : (R⁻¹)⁻¹ = R := by
--   grind [isRelation_inv R⁻¹]

-- theorem inv_comp [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
--     {R S : M} : (R !∘ S)⁻¹ = S⁻¹ !∘ R⁻¹ := by
--   apply IsRelation.ext (isRelation_inv _) (isRelation_comp _ _)
--   intro x y
--   simp only [mem_inv, orderedPair_eq_orderedPair_iff, mem_comp, ↓existsAndEq, and_true,
--     exists_and_left, exists_eq_left']
--   grind

-- theorem dom_inv [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd] {R : M} :
--     dom R⁻¹ = ran R := by
--   ext; simp [mem_dom_iff, mem_ran_iff]

-- theorem ran_inv [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd] {R : M} :
--     ran R⁻¹ = dom R := by
--   ext; simp [mem_dom_iff, mem_ran_iff]

end FirstOrder.Language.MemStructure
