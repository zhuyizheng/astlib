import Astlib.Basic.SetOperation.SUnion

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure}

variable (M) in
/- `M` is closed under unordered pairing -/
class HasUnorderedPair where
  unorderedPair : M → M → M
  unorderedPair_prop : ∀ x y z : M, z ∈ unorderedPair x y ↔ (z = x ∨ z = y)

export HasUnorderedPair (unorderedPair unorderedPair_prop)

noncomputable instance (hM : M ⊨ M.L.exUnorderedPair) : HasUnorderedPair M where
  unorderedPair x y := Classical.choose (exists_of_ex (realize_all.mp (realize_all.mp hM x) y))
  unorderedPair_prop := fun x y ↦ by
    simpa using Classical.choose_spec (exists_of_ex (realize_all.mp (realize_all.mp hM x) y))

@[simp, grind =]
theorem mem_unorderedPair_iff {M : MemStructure} [HasUnorderedPair M] (x y z : M) :
    z ∈ unorderedPair x y ↔ (z = x ∨ z = y) := M.unorderedPair_prop x y z

@[grind! .]
theorem mem_unorderedPair_left {M : MemStructure} [HasUnorderedPair M] (x y : M) :
    x ∈ unorderedPair x y := by grind

@[grind! .]
theorem mem_unorderedPair_right {M : MemStructure} [HasUnorderedPair M] (x y : M) :
    y ∈ unorderedPair x y := by grind

@[grind =]
theorem unorderedPair_comm [Extensional M] [HasUnorderedPair M] (x y : M) :
    unorderedPair x y = unorderedPair y x := by
  ext; grind

variable (M) in
instance instCommutativeUnodrederPair [Extensional M] [HasUnorderedPair M] :
  Std.Commutative (α := M) unorderedPair where
  comm := fun x y ↦ unorderedPair_comm x y

theorem unorderedPair_eq_iff₀ [Extensional M] [HasUnorderedPair M] (x y₁ y₂ : M) :
    unorderedPair x y₁ = unorderedPair x y₂ ↔ y₁ = y₂ := by
  grind

theorem unorderedPair_eq_iff [Extensional M] [HasUnorderedPair M] (x₁ y₁ x₂ y₂ : M) :
    unorderedPair x₁ y₁ = unorderedPair x₂ y₂ ↔ (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = y₂ ∧ x₂ = y₁) := by
  grind

/-- The ordered pair `(x, y)` -/
def HasUnorderedPair.orderedPair [HasUnorderedPair M] (x y : M) :=
  M.unorderedPair (M.unorderedPair x x) (M.unorderedPair x y)

export HasUnorderedPair (orderedPair)

@[inherit_doc] scoped[FirstOrder.Language.MemStructure] notation:max "!(" x ", " y ")" =>
  orderedPair x y

@[simp, push, grind =]
theorem HasUnorderedPair.orderedPair_eq_iff [Extensional M] [HasUnorderedPair M] (x₁ y₁ x₂ y₂ : M) :
    !(x₁, y₁) = !(x₂, y₂) ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  grind [orderedPair]

end FirstOrder.Language.MemStructure
