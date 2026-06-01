import Astlib.Basic.SetOperation.Relation

namespace FirstOrder.Language.MemStructure

section Basic

variable {M : MemStructure}

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

variable {M : MemStructure}

variable [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSProd]
  [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSUnion]

theorem IsFunction.comp
    {f g : M} (hf : IsFunction f) (hg : IsFunction g) : IsFunction (f !∘ g) := by
  grind [IsFunction]

@[simp, grind .]
theorem mem_dom_comp_iff
    {f g x : M} (hf : IsFunction f) (hg : IsFunction g) :
    x ∈ dom (f !∘ g) ↔ x ∈ dom g ∧ g ﹫ x ∈ dom f := by
  rw [hg.mem_dom_iff, hf.mem_dom_iff]
  grind

@[simp, grind .]
theorem dom_comp
    {f g : M} (hf : IsFunction f)
    (h : ran g ⊆ dom f) :
    dom (f !∘ g) = dom g := by
  ext x
  refine ⟨by grind, ?_⟩
  simp only [mem_dom_iff, rel_comp]
  intro ⟨y, hy⟩
  grind [show y ∈ ran g by grind]

@[simp, grind .]
theorem ran_comp
    {f g : M} (hf : IsFunction f) (hg : IsFunction g)
    (h : dom f ⊆ ran g) :
    ran (f !∘ g) = ran f := by
  ext y
  refine ⟨by grind, ?_⟩
  simp only [mem_ran_iff, rel_comp]
  intro ⟨x, hx⟩
  grind [show x ∈ dom f by grind]

@[simp, grind =]
theorem comp_val
    {f g x : M} (hf : IsFunction f) (hg : IsFunction g)
    (hx : x ∈ dom (f !∘ g)) :
    (f !∘ g) ﹫ x = f ﹫ (g ﹫ x) := by
  grind [rel_val]

end Comp

section Id

variable {M : MemStructure}

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

variable {M : MemStructure}

def IsFunctionFromTo (f a b : M) := IsFunction f ∧ dom f = a ∧ ran f ⊆ b

notation:50 f " !: " a:50 " → " b:50 => IsFunctionFromTo f a b

@[simp, grind .]
theorem IsFunctionFromTo.isFunction {f a b : M} (hf : f !: a → b) :
    IsFunction f :=
  hf.left

@[simp, grind .]
theorem IsFunctionFromTo.dom_eq {f a b : M} (hf : f !: a → b) :
    dom f = a :=
  hf.right.left

@[simp, grind .]
theorem IsFunctionFromTo.ran_subset {f a b : M} (hf : f !: a → b) :
    ran f ⊆ b:=
  hf.right.right

@[simp, grind .]
theorem isFunctionFromTo_dom_ran {f : M} (hf : IsFunction f) :
    f !: dom f → ran f:= by
  simp [IsFunctionFromTo, hf]

@[simp, grind .]
theorem IsFunctionFromTo.mono {f b b' : M} (hf : f !: a → b) (hbb' : b ⊆ b') :
    f !: a → b' := by
  grind [IsFunctionFromTo]

@[simp, grind .]
theorem isFunctionFromTo_empty [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
    [M.ClosedUnderDeltaZeroComprehension] (b : M) :
    (∅ : M) !: ∅ → b := by
  grind [IsFunctionFromTo]

@[simp, grind .]
theorem isFunctionFromTo_id [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
    [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSProd] (a : M) :
    id a !: a → a := by
  grind [IsFunctionFromTo]

@[simp, grind .]
theorem IsFunctionFromTo.comp [M.Extensional] [M.ClosedUnderSUnion]
    [M.ClosedUnderPair]
    [M.ClosedUnderDeltaZeroComprehension] [M.ClosedUnderSProd]
    {f g a b c : M} (hf : f !: a → b) (hg : g !: b → c) :
    g !∘ f !: a → c := by
  grind [IsFunctionFromTo, ran_comp_subset, IsFunction.comp]

end IsFunctionFromTo

section IsInjectionFromTo

variable {M : MemStructure}

def IsInjectionFromTo (f a b : M) :=
    f !: a → b ∧ ∀ ⦃x y⦄, x ∈ a → y ∈ a → f ﹫ x = f ﹫ y → x = y

notation:50 f " !: " a:50 " ↪ " b:50 => IsInjectionFromTo f a b

@[simp, grind .]
theorem IsInjectionFromTo.isFunctionFromTo {f a b : M} (hf : f !: a ↪ b) :
    f !: a → b := hf.left

@[simp, grind .]
theorem IsInjectionFromTo.isFunction {f a b : M} (hf : f !: a ↪ b) :
    IsFunction f := hf.isFunctionFromTo.isFunction


@[simp, grind .]
theorem IsInjectionFromTo.dom_eq {f a b : M} (hf : f !: a ↪ b) :
    dom f = a :=
  hf.isFunctionFromTo.dom_eq

@[simp, grind .]
theorem IsInjectionFromTo.ran_subset {f a b : M} (hf : f !: a ↪ b) :
    ran f ⊆ b :=
  hf.isFunctionFromTo.ran_subset

@[simp, grind .]
theorem IsInjectionFromTo.of_ran_subset {f a b b' : M} (hf : f !: a ↪ b) (hb' : ran f ⊆ b') :
    f !: a ↪ b' := by
  grind [IsInjectionFromTo, IsFunctionFromTo]

theorem IsInjectionFromTo.eq {f a b x x' : M} (hf : f !: a ↪ b)
    (hx : x ∈ a) (hx' : x' ∈ a)
    (hxx' : f ﹫ x = f ﹫ x') : x = x' := hf.right hx hx' hxx'

@[simp, grind .]
theorem IsInjectionFromTo.eq_iff {f a b x x' : M} (hf : f !: a ↪ b)
    (hx : x ∈ a) (hx' : x' ∈ a) :
    f ﹫ x = f ﹫ x' ↔ x = x' := by
  grind [IsInjectionFromTo.eq]

variable [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
  [M.ClosedUnderDeltaZeroComprehension]

@[simp, grind .]
theorem isInjectionFromTo_empty (b : M) : (∅ : M) !: ∅ ↪ b := by
  grind [IsInjectionFromTo]

variable [M.ClosedUnderSProd]
@[simp, grind .]
theorem isInjectionFromTo_id (a : M) : id a !: a ↪ a := by
  grind [IsInjectionFromTo]

@[simp, grind .]
theorem IsInjectionFromTo.comp {f g a b c : M} (hf : f !: b ↪ c)
    (hg : g !: a ↪ b) : f !∘ g !: a ↪ c := by
  grind [IsInjectionFromTo]

@[simp, grind .]
theorem isInjectionFromTo_of_comp {f g a b c : M} (hf : f !: b → c)
    (hg : g !: a → b) (hfg : f !∘ g !: a ↪ c) : g !: a ↪ b := by
  grind [IsInjectionFromTo]

@[simp, grind .]
theorem isInjectionFromTo_of_comp_id
    {f g a b : M} (hf : f !: a → b) (hg : g !: b → a) (hgf : g !∘ f = id a) :
    f !: a ↪ b := by
  grind

end IsInjectionFromTo

section IsSurjectionFromTo

variable {M : MemStructure}

def IsSurjectionFromTo (f a b : M) := f !: a → b ∧ ran f = b

notation:50 f " !: " a:50 " ↠ " b:50 => IsSurjectionFromTo f a b

@[simp, grind .]
theorem IsSurjectionFromTo.isFunctionFromTo {f a b : M} (hf : f !: a ↠ b) :
    f !: a → b := hf.left

@[simp, grind .]
theorem IsSurjectionFromTo.isFunction {f a b : M} (hf : f !: a ↠ b) :
    IsFunction f := hf.isFunctionFromTo.isFunction

@[simp, grind .]
theorem IsSurjectionFromTo.dom_eq {f a b : M} (hf : f !: a ↠ b) :
    dom f = a :=
  hf.isFunctionFromTo.dom_eq

@[simp, grind .]
theorem IsSurjectionFromTo.ran_eq {f a b : M} (hf : f !: a ↠ b) :
    ran f = b :=
  hf.right

theorem isSurjectionFromTo_ran_of_isFunctionFromTo {f a b : M} (hf : f !: a → b) :
    f !: a ↠ ran f :=
  ⟨by convert isFunctionFromTo_dom_ran hf.isFunction; grind, by grind⟩

theorem isSurjectionFromTo_dom_ran {f : M} (hf : IsFunction f) : f !: dom f ↠ ran f := by
  grind [IsSurjectionFromTo]

variable [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
  [M.ClosedUnderDeltaZeroComprehension]

@[simp, grind .]
theorem IsSurjectionFromTo.exists_mem_val {f a b y : M} (hf : f !: a ↠ b)
    (hy : y ∈ b) :
    ∃ x ∈ a, f ﹫ x = y := by
  grind [IsSurjectionFromTo]

theorem isSurjectionFromTo_iff_of_isFunctionFromTo {f a b : M} (hf : f !: a → b) :
    f !: a ↠ b ↔ ∀ y ∈ b, ∃ x ∈ dom f, f ﹫ x = y := by
  grind [IsSurjectionFromTo, IsFunctionFromTo]

@[simp, grind .]
theorem isSurjectionFromTo_empty : (∅ : M) !: ∅ ↠ ∅ := by
  grind [IsSurjectionFromTo]

variable [M.ClosedUnderSProd]

@[simp, grind .]
theorem isSurjectionFromTo_id (a : M) : id a !: a ↠ a := by
  grind [IsSurjectionFromTo]

@[simp, grind .]
theorem IsSurjectionFromTo.comp {f g a b c : M} (hf : f !: b ↠ c)
    (hg : g !: a ↠ b) : f !∘ g !: a ↠ c := by
  grind [IsSurjectionFromTo]

@[simp, grind .]
theorem isSurjectionFromTo_of_comp {f g a b c : M} (hf : f !: b → c)
    (hg : g !: a → b) (hfg : f !∘ g !: a ↠ c) : f !: b ↠ c := by
  rw [IsSurjectionFromTo]
  grind

@[simp, grind .]
theorem isSurjectionFromTo_of_comp_id {f g a b : M} (hf : f !: a → b)
    (hg : g !: b → a) (hfg : f !∘ g = id b) : f !: a ↠ b := by
  grind [IsSurjectionFromTo]

-- theorem IsInjective.isSurjective_inv_dom [M.ClosedUnderSProd] {f : M} (hf : IsInjective f) :
    -- IsSurjective f⁻¹ (dom f) := by
  -- grind [IsSurjective, isInjective_iff_isFunction_inv, ran_inv]

end IsSurjectionFromTo

section IsBijectionFromTo

variable {M : MemStructure}

def IsBijectionFromTo (f a b : M) := f !: a ↪ b ∧ f !: a ↠ b

notation:50 f " !: " a:50 " ↔ " b:50 => IsBijectionFromTo f a b

theorem isBijectionFromTo_iff {f a b : M} :
    f !: a ↔ b ↔ (f !: a → b ∧ (∀ x ∈ a, ∀ x' ∈ a, f ﹫ x = f ﹫ x' → x = x') ∧ ran f = b) := by
  grind [IsBijectionFromTo, IsInjectionFromTo, IsSurjectionFromTo]

@[simp, grind .]
theorem IsBijectionFromTo.isInjectionFromTo {f a b : M} (hf : f !: a ↔ b) : f !: a ↪ b := hf.left

@[simp, grind .]
theorem IsBijectionFromTo.isSurjectionFromTo {f a b : M} (hf : f !: a ↔ b) : f !: a ↠ b := hf.right

@[simp, grind .]
theorem IsBijectionFromTo.isFunctionFromTo {f a b : M} (hf : f !: a ↔ b) :
    f !: a → b := hf.isInjectionFromTo.isFunctionFromTo

@[simp, grind .]
theorem IsBijectionFromTo.isFunction {f a b : M} (hf : f !: a ↔ b) :
    IsFunction f := hf.isFunctionFromTo.isFunction

@[simp, grind .]
theorem IsBijectionFromTo.dom_eq {f a b : M} (hf : f !: a ↔ b) :
    dom f = a :=
  hf.isFunctionFromTo.dom_eq

@[simp, grind .]
theorem IsBijectionFromTo.ran_eq {f a b : M} (hf : f !: a ↔ b) :
    ran f = b :=
  hf.isSurjectionFromTo.ran_eq

theorem isBijectionFromTo_ran_of_isInjectionFromTo {f : M} (hf : f !: a ↪ b) :
    f !: a ↔ ran f :=
  ⟨by grind, by grind [isSurjectionFromTo_dom_ran (hf.isFunction)]⟩

variable [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
  [M.ClosedUnderDeltaZeroComprehension]

@[simp, grind .]
theorem IsBijectionFromTo.existsUnique_mem_val {f a b y : M} (hf : f !: a ↔ b) (hy : y ∈ b) :
    ∃! x ∈ a, f ﹫ x = y := by
  obtain ⟨x, hx⟩ := hf.isSurjectionFromTo.exists_mem_val hy
  exact ⟨x, hx, by grind [hf.isInjectionFromTo]⟩

theorem isBijectionFromTo_iff_of_isFunctionFromTo {f a b : M} (hf : f !: a → b) :
    f !: a ↔ b ↔ ∀ y ∈ b, ∃! x ∈ dom f, f ﹫ x = y := by
  refine ⟨by grind, fun h ↦ ⟨?_, ?_⟩⟩
  · refine ⟨by grind, fun x₁ x₂ h₁ h₂ h₁₂ ↦ ?_⟩
    grind [(h (f ﹫ x₁) (by grind)).unique (y₁ := x₁) (y₂ := x₂)]
  · rw [isSurjectionFromTo_iff_of_isFunctionFromTo hf]
    exact fun y a ↦ (h y a).exists

variable [M.ClosedUnderSProd]

theorem IsBijectionFromTo.comp {f g a b c : M} (hf : f !: b ↔ c)
    (hg : g !: a ↔ b) : f !∘ g !: a ↔ c := by
  grind [IsBijectionFromTo]

theorem IsBijectionFromTo.inv
    {f a b : M} (hf : f !: a ↔ b) :
    f⁻¹ !: b ↔ a := by
  rw [isBijectionFromTo_iff]
  have := hf.dom_eq
  have := hf.ran_eq
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨by grind, fun y x₁ x₂ h₁ h₂ ↦ ?_⟩, by grind [dom_inv]⟩
    apply hf.isInjectionFromTo.eq (x := x₁) (x' := x₂) <;> grind
  · intro y₁ h₁ y₂ h₂ h₁₂
    let x := f⁻¹ ﹫ y₁
    grind [rel_val]
  · grind [ran_inv]

@[simp, grind .]
theorem IsBijectionFromTo.inv_val_val {f a b x : M} (hf : f !: a ↔ b)
    (hx : x ∈ a) :
    f⁻¹ ﹫ (f ﹫ x) = x := by
  grind [hf.inv, rel_val]

@[simp]
theorem IsBijectionFromTo.inv_comp {f a b : M} (hf : f !: a ↔ b) :
    f⁻¹ !∘ f = id a := by
  rw [IsFunction.ext (f := f⁻¹ !∘ f) (g := id a)]
  · exact hf.inv.isFunction.comp hf.isFunction
  all_goals grind [hf.inv]

@[simp, grind .]
theorem IsBijectionFromTo.val_inv_val {f a b y : M} (hf : f !: a ↔ b)
    (hx : y ∈ b) :
    f ﹫ (f⁻¹ ﹫ y) = y := by
  grind [hf.inv, rel_val]

@[simp]
theorem IsBijectionFromTo.comp_inv {f : M} (hf : f !: a ↔ b) :
    f !∘ f⁻¹ = id b := by
  have : dom (f !∘ f⁻¹) = ran f := by grind [dom_inv]
  rw [IsFunction.ext (f := f !∘ f⁻¹) (g := id (ran f))]
  · grind
  · exact hf.isFunction.comp hf.inv.isFunction
  all_goals grind [hf.inv]

@[simp, grind .]
theorem isBijectionFromTo_of_comp_id_comp_id
    {f g a b : M} (hf : f !: a → b) (hg : g !: b → a) (hfg : f !∘ g = id b) (hgf : g !∘ f = id a) :
    f !: a ↔ b := by
  grind [IsBijectionFromTo]

end IsBijectionFromTo

end FirstOrder.Language.MemStructure
