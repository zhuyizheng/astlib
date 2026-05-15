import Astlib.Basic.SetOperation.SUnion

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable (M : MemStructure)

/- `M` is closed under unordered pairing -/
class HasUnorderedPair where
  unorderedPair : M → M → M
  unorderedPair_prop : ∀ x y z : M, z ∈ unorderedPair x y ↔ (z = x ∨ z = y)

export HasUnorderedPair (unorderedPair unorderedPair_prop)

noncomputable instance (hM : M ⊨ M.L.exUnorderedPair) : HasUnorderedPair M where
  unorderedPair x y := Classical.choose (exists_of_ex (realize_all.mp (realize_all.mp hM x) y))
  unorderedPair_prop := fun x y ↦ by
    simpa using Classical.choose_spec (exists_of_ex (realize_all.mp (realize_all.mp hM x) y))

variable {M}
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

variable (M) in
instance [HasUnorderedPair M] : Singleton M M where
  singleton x := unorderedPair x x

@[simp, grind =, push]
theorem mem_singleton_iff [HasUnorderedPair M] (x y : M) :
    y ∈ ({x} : M) ↔ y = x := by
  convert mem_unorderedPair_iff x x y using 1
  tauto

theorem notMem_singleton_iff [HasUnorderedPair M] (x y : M) :
    y ∉ ({x} : M) ↔ y ≠ x := by simp

theorem mem_singleton [HasUnorderedPair M] (x : M) :
    x ∈ ({x} : M) := by simp

@[simp]
theorem singleton_eq_singleton_iff [HasUnorderedPair M] (x y : M) :
    ({x} : M) = {y} ↔ x = y := by grind [mem_singleton]

@[simp]
theorem singleton_ne_empty [HasEmpty M] [HasUnorderedPair M] (x : M) :
    ({x} : M) ≠ ∅ := by grind [mem_singleton]

@[simp, grind =]
theorem singleton_subset_iff [HasUnorderedPair M] (x y : M) :
    ({x} : M) ⊆ y ↔ x ∈ y := by simp [Subset, MemStructure.Subset]

@[gcongr]
theorem singleton_subset_singleton [HasUnorderedPair M] (x y : M) :
    ({x} : M) ⊆ {y} ↔ x = y := by grind [mem_singleton]

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



-- lemma test2 (M : MemStructure) (hM : M ⊨ M.L.exUnion) : True := by
  -- have := realize_all.mp hM

end FirstOrder.Language.MemStructure
