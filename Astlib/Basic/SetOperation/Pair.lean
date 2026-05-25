import Astlib.Basic.SetOperation.SUnion

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure}


variable (M) in
class UnorderedPair where
  unorderedPair : M → M → M

export UnorderedPair (unorderedPair)

noncomputable instance : Decidable (∃ a : M, ∀ z, z ∈ a ↔ z = x ∨ z = y) :=
  Classical.propDecidable _

noncomputable instance : UnorderedPair M :=
  ⟨fun x y ↦ dite (∃ a : M, ∀ z, z ∈ a ↔ z = x ∨ z = y) Classical.choose default⟩

variable (M) in
/- `M` is closed under unordered pairing -/
class ClosedUnderPair : Prop where
  protected closedUnderPair : ∀ x y z : M, z ∈ unorderedPair x y ↔ (z = x ∨ z = y)

noncomputable instance instClosedUnderPair
    (h : ∀ x y : M, ∃ a : M, ∀ z, z ∈ a ↔ z = x ∨ z = y) : M.ClosedUnderPair :=
  ⟨fun x y ↦ by convert Classical.choose_spec (h x y); simp [unorderedPair, h]⟩

@[simp, grind =]
theorem mem_unorderedPair_iff [M.ClosedUnderPair] (x y z : M) :
    z ∈ unorderedPair x y ↔ (z = x ∨ z = y) := ClosedUnderPair.closedUnderPair x y z

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

variable {L : FirstOrder.Language} [HasMem L]

/-- `t₁ ∈ {t₂, t₃}` -/
abbrev Term.memUnorderedPair (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) :=
  t₁ =' t₂ ⊔ t₁ =' t₃

instance (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) : (t₁.memUnorderedPair t₂ t₃).DeltaZero :=
  by infer_instance

/-- `t₁ = {t₂, t₃}` -/
abbrev Term.eqUnorderedPair (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) :=
  (∀'∈ t₁ (&-1).memUnorderedPair t₂.castSucc t₃.castSucc) ⊓ (t₂ ∈' t₁ ⊓ t₃ ∈' t₁)

instance (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) : (t₁.eqUnorderedPair t₂ t₃).DeltaZero :=
  by infer_instance

/-- `t₁ ∈ (t₂, t₃)` -/
abbrev Term.memOrderedPair (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) :=
  t₁.eqUnorderedPair t₂ t₂ ⊔ t₁.eqUnorderedPair t₂ t₃

instance (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) : (t₁.memOrderedPair t₂ t₃).DeltaZero :=
  by infer_instance

/-- `t₁ = (t₂, t₃)` -/
abbrev Term.eqOrderedPair (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) :=
  (∀'∈ t₁ (&-1).memOrderedPair t₂.castSucc t₃.castSucc) ⊓
    ((∃'∈ t₁ (&-1).eqUnorderedPair t₂.castSucc t₂.castSucc) ⊓
    (∃'∈ t₁ (&-1).eqUnorderedPair t₂.castSucc t₃.castSucc))

instance (t₁ t₂ t₃ : L.Term (α ⊕ Fin n)) : (t₁.eqOrderedPair t₂ t₃).DeltaZero :=
  by infer_instance

-- /-- `t` is an unordered pair -/
-- abbrev Term.isOrderedPair (t : L.Term (α ⊕ Fin n)) :=
--   ∃'∈ t ∃'∈ t.castSucc t.castSucc.castSucc.eqUnorderedPair &-2 &-1

/-- `t₁` is the left component of the ordered pair `t₂` -/
abbrev Term.eqLeft (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  ∃'∈ t₂ ∃'∈ &-1 (t₂.castSucc.castSucc.eqOrderedPair t₁.castSucc.castSucc &-1)

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁.eqLeft t₂).DeltaZero :=
  by infer_instance

/-- `t₁` is the right component of the ordered pair `t₂` -/
abbrev Term.eqRight (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  ∃'∈ t₂ ∃'∈ &-1 (t₂.castSucc.castSucc.eqOrderedPair &-1 t₁.castSucc.castSucc)

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁.eqRight t₂).DeltaZero :=
  by infer_instance

-- /-- `t` is an ordered pair -/
abbrev Term.isOrderedPair (t : L.Term (α ⊕ Fin n)) :=
  ∃'∈ t ∃'∈ &-1 ((&-1).eqLeft t.castSucc.castSucc)

instance (t : L.Term (α ⊕ Fin n)) : (t.isOrderedPair).DeltaZero :=
  by infer_instance

/-- `t₁` and `t₂` are ordered pairs with the same left component -/
abbrev Term.sameLeft (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  ∃'∈ t₁ ∃'∈ &-1 ((&-1).eqLeft t₁.castSucc.castSucc ⊓ (&-1).eqLeft t₂.castSucc.castSucc)

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁.sameLeft t₂).DeltaZero :=
  by infer_instance

/-- `t₁` and `t₂` are ordered pairs with the same right component -/
abbrev Term.sameRight (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  ∃'∈ t₁ ∃'∈ &-1 ((&-1).eqRight t₁.castSucc.castSucc ⊓ (&-1).eqRight t₂.castSucc.castSucc)

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁.sameRight t₂).DeltaZero :=
  by infer_instance

/-- `t₁` and `t₂` are ordered pairs and the right component of `t₁` equals to the left component
of `t₂` -/
abbrev Term.rightEqLeft (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  ∃'∈ t₁ ∃'∈ &-1 ((&-1).eqRight t₁.castSucc.castSucc ⊓ (&-1).eqLeft t₂.castSucc.castSucc)

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁.rightEqLeft t₂).DeltaZero :=
  by infer_instance

/-- `t` is an ordered pair whose left and right components are the same -/
abbrev Term.sameLeftRight (t : L.Term (α ⊕ Fin n)) :=
  t.rightEqLeft t

instance (t : L.Term (α ⊕ Fin n)) : t.sameLeftRight.DeltaZero :=
  by infer_instance

/-- `t₁` and `t₂` are ordered pairs that switches left and right components -/
abbrev Term.reverseLeftRight (t₁ t₂ : L.Term (α ⊕ Fin n)) :=
  t₁.rightEqLeft t₂ ⊓ t₂.rightEqLeft t₁

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁.reverseLeftRight t₂).DeltaZero :=
  by infer_instance

variable {L : FirstOrder.Language} [HasMem L]


-- /-- Closed under unordered pairing -/
-- def allAllExPair : L.Sentence :=
--   ∀' ∀' ∃' (&2).eqUnorderedPair &0 &1

-- noncomputable instance {M : MemStructure} (hM : M ⊨ M.L.allAllExPair) : M.ClosedUnderPair where
--   unorderedPair x y := Classical.choose (exists_of_ex (realize_all.mp (realize_all.mp hM x) y))
--   unorderedPair_prop := fun x y ↦ by
--     have := Classical.choose_spec (exists_of_ex (realize_all.mp (realize_all.mp hM x) y))
--     simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_inf,
--       Fin.reduceLast, Term.castSucc, Term.castLE_var_inr, Fin.castLE_zero, Fin.castLE_succ_castSucc,
--       Fin.castSucc_one, realize_all, Fin.reduceCastSucc, realize_imp, MemStructure.realize_mem,
--       Term.realize_var, Sum.elim_inr, Fin.snoc, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.lt_add_one,
--       ↓reduceDIte, Fin.reduceCastLT, Nat.mod_succ, lt_self_iff_false, cast_eq, realize_sup,
--       realize_bdEqual, Nat.zero_mod, zero_lt_three, Fin.castSucc_zero, Order.lt_two_iff, zero_le,
--       Order.lt_one_iff, Nat.one_mod, Nat.one_lt_ofNat, Std.le_refl] at this ⊢
--     grind

variable {M : MemStructure} (t t₁ t₂ t₃ : M.L.Term (α ⊕ Fin n)) (v : α → M) (xs : Fin n → M)

@[simp 1100]
theorem Term.memUnorderedPair_iff :
    (t₁.memUnorderedPair t₂ t₃).Realize v xs ↔
      t₁.realize' v xs = t₂.realize' v xs ∨ t₁.realize' v xs = t₃.realize' v xs := by
  simp

@[simp 1100]
theorem Term.eqUnorderedPair_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.eqUnorderedPair t₂ t₃).Realize v xs ↔
      t₁.realize' v xs = M.unorderedPair (t₂.realize' v xs) (t₃.realize' v xs) := by
  simp [M.eq_unorderedPair_iff]

@[simp 1100]
theorem Term.memOrderedPair_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.memOrderedPair t₂ t₃).Realize v xs ↔
      t₁.realize' v xs ∈ !(t₂.realize' v xs, t₃.realize' v xs) := by
  simp [M.mem_orderedPair_iff]

@[simp 1100]
theorem Term.eqOrderedPair_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.eqOrderedPair t₂ t₃).Realize v xs ↔
      t₁.realize' v xs = !(t₂.realize' v xs, t₃.realize' v xs) := by
  simp [M.eq_orderedPair_iff, M.mem_orderedPair_iff]

@[simp 1100]
theorem Term.eqLeft_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.eqLeft t₂).Realize v xs ↔
      ∃ a : M, t₂.realize' v xs = !(t₁.realize' v xs, a) := by
  simp only [realize_not, Function.comp_apply, Nat.succ_eq_add_one, castSucc,
    castLE_castLE, realize_all, realize_imp, MemStructure.realize_mem, realize_castLE,
    Fin.castLE_succ_castSucc, Sum.elim_comp_map_castSucc, realize_var, Sum.elim_inr, Fin.snoc_last,
    castLE_var_inr, Fin.snoc_castSucc, eqOrderedPair_iff, Fin.castLE_add_two_castSucc,
    Sum.elim_comp_map_castSucc_comp, Fin.snoc_comp_castSucc, M.eq_orderedPair_iff, not_and,
    not_forall, not_not, exists_prop, not_exists]
  grind

@[simp 1100]
theorem Term.eqRight_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.eqRight t₂).Realize v xs ↔
      ∃ a : M, t₂.realize' v xs = !(a, t₁.realize' v xs) := by
  simp only [realize_not, Function.comp_apply, Nat.succ_eq_add_one, castSucc,
    castLE_castLE, realize_all, realize_imp, MemStructure.realize_mem, realize_castLE,
    Fin.castLE_succ_castSucc, Sum.elim_comp_map_castSucc, realize_var, Sum.elim_inr, Fin.snoc_last,
    castLE_var_inr, Fin.snoc_castSucc, eqOrderedPair_iff, Fin.castLE_add_two_castSucc,
    Sum.elim_comp_map_castSucc_comp, Fin.snoc_comp_castSucc, M.eq_orderedPair_iff, not_and,
    not_forall, not_not, exists_prop, not_exists]
  exact ⟨by grind, fun ⟨a, _⟩ ↦ by use M.unorderedPair a a; grind⟩

@[simp 1100]
theorem Term.isOrderedPair_iff [M.Extensional] [M.ClosedUnderPair] :
    (t.isOrderedPair).Realize v xs ↔ ∃ a b : M, t.realize' v xs = !(a, b) := by
  simp only [realize_not, Function.comp_apply, castSucc, Nat.succ_eq_add_one,
    castLE_castLE, realize_all, realize_imp, MemStructure.realize_mem, realize_castLE,
    Fin.castLE_succ_castSucc, Sum.elim_comp_map_castSucc, realize_var, Sum.elim_inr, Fin.snoc_last,
    not_forall, not_not, exists_prop, not_exists, not_and, M.eq_orderedPair_iff]
  simp only [Fin.castLE_add_three_castSucc, Sum.elim_comp_map_castSucc_comp, castLE_var_inr,
    Fin.castLE_add_two_castSucc, Function.comp_apply, eqOrderedPair_iff, realize_castLE,
    Fin.castLE_add_four_castSucc, realize_var, Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last]
  simp only [← Function.comp_assoc, Fin.snoc_comp_castSucc]
  constructor
  · intro ⟨u, hu, a, ha, v, hv, b, hb, hx⟩
    use a, b
    grind [M.eq_orderedPair_iff]
  · intro ⟨a, b, h₁, h₂, h₃⟩
    use M.unorderedPair a a, by grind, a, by grind, M.unorderedPair a b, by grind, b, by grind
    grind [M.eq_orderedPair_iff]

@[simp 1100]
theorem Term.sameLeft_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.sameLeft t₂).Realize v xs ↔
      ∃ a b c : M, t₁.realize' v xs = !(a, b) ∧ t₂.realize' v xs = !(a, c) := by
  simp only [realize_not, Function.comp_apply, castSucc, Nat.succ_eq_add_one,
    castLE_castLE, realize_all, realize_imp, MemStructure.realize_mem, realize_castLE,
    Fin.castLE_succ_castSucc, Sum.elim_comp_map_castSucc, realize_var, Sum.elim_inr, Fin.snoc_last,
    castLE_var_inr, Fin.snoc_castSucc, not_forall, not_not, exists_prop, not_exists, not_and]
  simp only [realize_inf, eqLeft_iff, realize_castLE, Fin.castLE_add_two_castSucc,
    Sum.elim_comp_map_castSucc_comp, Fin.snoc_comp_castSucc, realize_var, Sum.elim_inr,
    Fin.snoc_last, exists_and_left, exists_and_right]
  constructor
  · intro ⟨u, hu, a, ha, ⟨b, hb⟩, ⟨c, hc⟩⟩
    exact ⟨a, ⟨b, hb⟩, ⟨c, hc⟩⟩
  · intro ⟨a, ⟨b, hb⟩, ⟨c, hc⟩⟩
    exact ⟨M.unorderedPair a a, by grind [M.eq_orderedPair_iff],
      ⟨a, by grind, ⟨b, hb⟩, ⟨c, hc⟩⟩⟩

@[simp 1100]
theorem Term.sameRight_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.sameRight t₂).Realize v xs ↔
      ∃ a b c : M, t₁.realize' v xs = !(a, c) ∧ t₂.realize' v xs = !(b, c) := by
  simp only [realize_not, Function.comp_apply, castSucc, Nat.succ_eq_add_one,
    castLE_castLE, realize_all, realize_imp, MemStructure.realize_mem, realize_castLE,
    Fin.castLE_succ_castSucc, Sum.elim_comp_map_castSucc, realize_var, Sum.elim_inr, Fin.snoc_last,
    castLE_var_inr, Fin.snoc_castSucc, not_forall, not_not, exists_prop, not_exists, not_and]
  simp only [realize_inf, eqRight_iff, realize_castLE, Fin.castLE_add_two_castSucc,
    Sum.elim_comp_map_castSucc_comp, Fin.snoc_comp_castSucc, realize_var, Sum.elim_inr,
    Fin.snoc_last]
  constructor
  · intro ⟨u, hu, c, hc, ⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a, b, c, ha, hb⟩
  · intro ⟨a, b, c, ha, hb⟩
    exact ⟨M.unorderedPair a c, by rw [realize', MemStructure.eq_orderedPair_iff] at ha; grind,
      ⟨c, by grind, ⟨a, ha⟩, ⟨b, hb⟩⟩⟩

@[simp 1100]
theorem Term.rightEqLeft_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.rightEqLeft t₂).Realize v xs ↔
      ∃ a b c : M, t₁.realize' v xs = !(a, b) ∧ t₂.realize' v xs = !(b, c) := by
  simp only [realize_not, Function.comp_apply, castSucc, Nat.succ_eq_add_one,
    castLE_castLE, realize_all, realize_imp, MemStructure.realize_mem, realize_castLE,
    Fin.castLE_succ_castSucc, Sum.elim_comp_map_castSucc, realize_var, Sum.elim_inr, Fin.snoc_last,
    castLE_var_inr, Fin.snoc_castSucc, not_forall, not_not, exists_prop, not_exists, not_and]
  simp only [realize_inf, eqLeft_iff, eqRight_iff, realize_castLE, Fin.castLE_add_two_castSucc,
    Sum.elim_comp_map_castSucc_comp, Fin.snoc_comp_castSucc, realize_var, Sum.elim_inr,
    Fin.snoc_last]
  constructor
  · intro ⟨u, hu, b, hb, ⟨a, ha⟩, ⟨c, hc⟩⟩
    exact ⟨a, b, c, ha, hc⟩
  · intro ⟨a, b, c, ha, hc⟩
    exact ⟨M.unorderedPair a b, by rw [realize', MemStructure.eq_orderedPair_iff] at ha; grind,
      ⟨b, by grind, ⟨a, ha⟩, ⟨c, hc⟩⟩⟩

@[simp 1100]
theorem Term.sameLeftRight_iff [M.Extensional] [M.ClosedUnderPair] :
    t.sameLeftRight.Realize v xs ↔
      ∃ a : M, t.realize' v xs = !(a, a) := by
  simp only [rightEqLeft_iff]
  grind

@[simp 1100]
theorem Term.reverseLeftRight_iff [M.Extensional] [M.ClosedUnderPair] :
    (t₁.reverseLeftRight t₂).Realize v xs ↔
      ∃ a b : M, t₁.realize' v xs = !(a, b) ∧ t₂.realize' v xs = !(b, a) := by
  simp only [realize_inf, rightEqLeft_iff]
  grind

end FirstOrder.Language
