import Astlib.Basic.SetOperation.Relation

namespace FirstOrder.Language.MemStructure

section Basic

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

def IsFunction (f : M) :=
  IsRelation f ∧ ∀ ⦃x y₁ y₂ : M⦄, x [f] y₁ → x [f] y₂ → y₁ = y₂

@[simp, grind .]
theorem IsFunction.isRelation {f : M} (hf : IsFunction f) : IsRelation f := hf.left

@[simp, grind .]
theorem IsFunction.eq
    {f x y₁ y₂: M} (hf : IsFunction f) (h₁ : x [f] y₁) (h₂ : x [f] y₂) : y₁ = y₂ := by
  grind [IsFunction]

@[simp, grind .]
theorem isFunction_empty [M.HasEmpty] : IsFunction (∅ : M) := by
  simp [IsFunction]

@[simp, grind .]
theorem IsFunction.subset {f g : M} (hf : IsFunction f) (hgf : g ⊆ f) :
    IsFunction g := by
  simp only [IsFunction, hf.isRelation.subset hgf, true_and]
  exact fun x y₁ y₂ h₁ h₂ ↦ hf.eq (hgf h₁) (hgf h₂)

theorem IsFunction.inter_right [M.ClosedUnderDeltaZeroComprehension]
    {f g : M} (hf : IsFunction f) : IsFunction (f ∩ g) := by
  grind

theorem IsFunction.inter_left [M.ClosedUnderDeltaZeroComprehension]
    {f g : M} (hg : IsFunction g) : IsFunction (f ∩ g) := by
  grind

theorem IsFunction.sdiff [M.ClosedUnderDeltaZeroComprehension]
    {f g : M} (hf : IsFunction f) : IsFunction (f \ g) := by
  grind

noncomputable instance (f x : M) : Decidable (∃ y, x [f] y) :=
  Classical.propDecidable _

noncomputable def val (f x : M) := dite (∃ y : M, x [f] y) Classical.choose default

infix:88 " ﹫ " => FirstOrder.Language.MemStructure.val

@[simp, grind! .]
theorem IsFunction.val_eq_of_rel
    {f x y : M} (hf : IsFunction f) (hxy : x [f] y) : f ﹫ x = y := by
  have : ∃ y, !(x, y) ∈ f := by use y
  grind [val, IsFunction]

theorem IsFunction.exists_val
    {f : M} (hf : IsFunction f)
    {z : M} (hz : z ∈ f) : ∃ x, z = !(x, f ﹫ x) := by
  obtain ⟨x, y, hxy⟩ := hf.isRelation hz
  use x
  convert hxy
  exact val_eq_of_rel hf (by grind)

variable [M.ClosedUnderDeltaZeroComprehension]
    [M.ClosedUnderSUnion] [M.Extensional] [M.ClosedUnderPair]

-- @[simp]
theorem rel_val
    {f x : M} (hx : x ∈ dom f) : x [f] (f ﹫ x) := by
  grind [val]

lemma IsFunction.subset_iff {f g : M} (hf : IsFunction f) :
    f ⊆ g ↔ ∀ x ∈ dom f, (x [g] (f ﹫ x)) := by
  refine ⟨by grind, fun h z hz ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := hf.exists_val hz
  exact h x (by grind)

@[grind .]
theorem IsFunction.ext {f g : M} (hf : IsFunction f) (hg : IsFunction g)
    (hfg : dom f = dom g)
    (h : ∀ x ∈ dom f, f ﹫ x = g ﹫ x) : f = g :=
  eq_of_subset_of_subset (hf.subset_iff.mpr (by grind)) (hg.subset_iff.mpr (by grind))

@[grind .]
theorem IsFunction.eq_iff {f g : M} (hf : IsFunction f) (hg : IsFunction g) :
    f = g ↔ dom f = dom g ∧ ∀ x ∈ dom f, f ﹫ x = g ﹫ x := by
  grind

@[grind =]
theorem IsFunction.mem_dom_iff {f : M} (x : M) (hf : IsFunction f) :
    x ∈ dom f ↔ x [f] (f ﹫ x) := by
  grind

@[grind =]
theorem IsFunction.mem_ran_iff {f : M} (y : M) (hf : IsFunction f) :
    y ∈ ran f ↔ ∃ x ∈ dom f, f ﹫ x = y := by
  rw [M.mem_ran_iff]
  exact exists_congr (by grind)

theorem IsFunction.subset_dom_sprod_ran [M.ClosedUnderSProd] {f : M} (hf : IsFunction f) :
    f ⊆ dom f ×ˢ ran f :=
  hf.isRelation.subset_dom_sprod_ran

def FunctionAgree (f g : M) := ∀ ⦃x⦄, x ∈ dom f ∩ dom g → f ﹫ x = g ﹫ x

@[simp, grind .]
theorem IsFunction.union {f g : M}
    (hf : IsFunction f) (hg : IsFunction g)
    (hfg : FunctionAgree f g) : IsFunction (f ∪ g) := by
  refine ⟨hf.isRelation.union hg.isRelation, fun x y₁ y₂ h₁ h₂ ↦ ?_⟩
  rw [mem_union] at h₁ h₂
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · grind
    · grind [hfg (x := x) (by grind)]
  · rcases h₂ with h₂ | h₂
    · grind [hfg (x := x) (by grind)]
    · grind

@[simp, grind .]
theorem IsFunction.sUnion {X : M}
    (hX₁ : ∀ f ∈ X, IsFunction f)
    (hX₂ : ∀ f ∈ X, ∀ g ∈ X, FunctionAgree f g) : IsFunction (⋃₀ X) := by
  refine ⟨IsRelation.sUnion (fun f hf ↦ (hX₁ f hf).isRelation), fun x y₁ y₂ h₁ h₂ ↦ ?_⟩
  simp only [mem_sUnion_iff] at h₁ h₂
  obtain ⟨f, hf₁, hf₂⟩ := h₁
  obtain ⟨g, hg₁, hg₂⟩ := h₂
  grind [(hX₁ f hf₁).union (hX₁ g hg₁) (by grind)]

end Basic

section Comp

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

variable [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
  [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSUnion]

@[grind .]
theorem IsFunction.isFunction_comp
    {f g : M} (hf : IsFunction f) (hg : IsFunction g) : IsFunction (f !∘ g) := by
  grind [IsFunction]

@[grind .]
theorem mem_dom_comp
    {f g x : M} (hf : IsFunction f) (hg : IsFunction g)
    (hx : x ∈ dom g) (hx' : g ﹫ x ∈ dom f) :
    x ∈ dom (f !∘ g) := by
  rw [hg.mem_dom_iff] at hx
  rw [hf.mem_dom_iff] at hx'
  grind

@[grind .]
theorem dom_comp
    {f g : M} (hf : IsFunction f)
    (h : ran g ⊆ dom f) :
    dom g = dom (f !∘ g) := by
  ext x
  constructor
  · simp only [mem_dom_iff, rel_comp]
    intro ⟨y, hy⟩
    exact ⟨f ﹫ y, y, hy, by grind [show y ∈ ran g by grind]⟩
  · grind

@[grind =]
theorem val_comp
    {f g x : M} (hf : IsFunction f) (hg : IsFunction g)
    (hx : x ∈ dom g) (hx' : g ﹫ x ∈ dom f) :
    (f !∘ g) ﹫ x = f ﹫ (g ﹫ x) := by
  rw [hg.mem_dom_iff] at hx
  rw [hf.mem_dom_iff] at hx'
  grind

end Comp

section Id

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

variable [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
  [M.ClosedUnderDeltaZeroComprehension]

@[simp, grind .]
theorem isFunction_id
    (a : M) : IsFunction (id a) := by
  grind [IsFunction, id]

@[simp, grind =]
theorem id_val (a : M) {x : M} (hx : x ∈ a) : id a ﹫ x = x :=
  (isFunction_id _).val_eq_of_rel (by grind)

@[simp, grind =]
theorem IsFunction.comp_id [M.ClosedUnderSUnion]
    {f a : M} (hf : IsFunction f) (h : dom f ⊆ a) :
    f !∘ (id a) = f := by
  grind [IsFunction]

@[simp, grind =]
theorem IsFunction.id_comp [M.ClosedUnderSUnion]
    {f a : M} (hf : IsFunction f) (h : ran f ⊆ a) :
    (id a) !∘ f = f := by
  grind [IsFunction]

end Id

section IsFunctionFromTo

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

def IsFunctionFrom (f a : M) := IsFunction f ∧ dom f = a

@[simp, grind .]
theorem isFunctionFrom_dom {f : M} (hf : IsFunction f) : IsFunctionFrom f (dom f) := by
  simp [IsFunctionFrom, hf]

@[simp, grind .]
theorem isFunctionFrom_empty [M.HasEmpty] [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
  [M.ClosedUnderDeltaZeroComprehension] : IsFunctionFrom (∅ : M) ∅ := by
  simp [IsFunctionFrom]

def IsFunctionTo (f b : M) := IsFunction f ∧ ran f ⊆ b

@[simp, grind .]
theorem isFunctionTo_mono {f b b' : M} (hfb : IsFunctionTo f b) (hbb' : b ⊆ b') :
    IsFunctionTo f b' := by
  grind [IsFunctionTo]

@[simp, grind .]
theorem isFunctionTo_ran {f : M} (hf : IsFunction f) :
    IsFunctionTo f (ran f) := by
  grind [IsFunctionTo]

@[simp, grind .]
theorem isFunctionTo_empty [M.HasEmpty] [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
    [M.ClosedUnderDeltaZeroComprehension] (b : M) : IsFunctionTo (∅ : M) b := by
  have : IsFunctionTo (∅ : M) ∅ := by grind [IsFunctionTo]
  grind

def IsFunctionFromTo (f a b : M) := IsFunctionFrom f a ∧ IsFunctionTo f b

notation:50 f " !: " a:50 " → " b:50 => IsFunctionFromTo f a b

theorem isFunctionFromTo_iff (f a b : M) :
    f !: a → b ↔ IsFunction f ∧ dom f = a ∧ ran f ⊆ b := by
  grind [IsFunctionFromTo, IsFunctionFrom, IsFunctionTo]

@[simp, grind .]
theorem isFunctionFromTo_mono {f a b b' : M} (hf : f !: a → b) (hbb' : b ⊆ b') :
    f !: a → b' := by
  grind [IsFunctionFromTo]

@[simp, grind .]
theorem isFunctionFromTo_dom_ran {f : M} (hf : IsFunction f) :
    f !: dom f → ran f := by
  grind [IsFunctionFromTo]

@[simp, grind .]
theorem isFunctionFromTo_empty [M.HasEmpty] [M.Extensional] [M.ClosedUnderSUnion]
    [M.ClosedUnderPair]
    [M.ClosedUnderDeltaZeroComprehension] (b : M) : ∅ !: ∅ → b := by
  grind [IsFunctionFromTo]

@[simp, grind .]
theorem IsFunctionFromTo.comp [M.HasEmpty] [M.Extensional] [M.ClosedUnderSUnion]
    [M.ClosedUnderPair]
    [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSProd]
    {f g a b c : M} (hf : f !: a → b) (hg : g !: b → c) :
    g !∘ f !: a → c := by
  grind [isFunctionFromTo_iff, ran_comp_subset]

end IsFunctionFromTo

section Injective

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

variable [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
  [M.ClosedUnderDeltaZeroComprehension]

def IsInjective (f : M) := ∀ ⦃x y⦄, x ∈ dom f → y ∈ dom f → f ﹫ x = f ﹫ y → x = y

@[simp, grind .]
theorem isInjective_empty [M.HasEmpty] : IsInjective (∅ : M) := by
  grind [IsInjective]

theorem isInjective_iff_isFunction_inv [M.ClosedUnderSProd] {f : M} (hf : IsFunction f) :
    IsInjective f ↔ IsFunction (f⁻¹) := by
  refine ⟨fun h ↦ ⟨by grind, by intros; exact h (by grind) (by grind) (by grind)⟩, ?_⟩
  intro h y₁ y₂ h₁ h₂ h₁₂
  let x := f ﹫ y₁
  grind [show x [f⁻¹] y₁ by grind, show x [f⁻¹] y₂ by grind]

end Injective
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
