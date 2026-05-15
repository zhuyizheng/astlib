import Astlib.Basic.SetOperation.Pair

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure}

variable (M) in
instance [HasSUnion M] [HasUnorderedPair M] : Union M where
  union x y := ⋃₀ (HasUnorderedPair.unorderedPair x y)

@[simp, grind =]
theorem mem_union [HasSUnion M] [HasUnorderedPair M] (x y z : M) :
    x ∈ y ∪ z ↔ x ∈ y ∨ x ∈ z := by
  simp [Union.union]

@[grind =]
theorem union_comm [Extensional M] [HasSUnion M] [HasUnorderedPair M] (x y : M) :
    x ∪ y = y ∪ x := by
  ext; grind

variable (M) in
instance instCommutativeUnion [Extensional M] [HasSUnion M] [HasUnorderedPair M] :
  Std.Commutative (α := M) Union.union where
  comm := fun x y ↦ union_comm x y

@[grind =]
theorem union_assoc [Extensional M] [HasSUnion M] [HasUnorderedPair M] (x y z : M) :
    (x ∪ y) ∪ z = x ∪ (y ∪ z) := by
  ext; grind

variable (M) in
instance instAssociativeUnion [Extensional M] [HasSUnion M] [HasUnorderedPair M] :
  Std.Associative (α := M) Union.union where
  assoc := fun x y z ↦ union_assoc x y z

@[simp, grind =, push]
theorem empty_union [Extensional M] [HasEmpty M] [HasSUnion M] [HasUnorderedPair M] (x : M) :
    (∅ : M) ∪ x = x := by
  ext; grind

@[simp, grind =, push]
theorem union_empty [Extensional M] [HasEmpty M] [HasSUnion M] [HasUnorderedPair M] (x : M) :
    x ∪ (∅ : M) = x := by
  grind

@[simp, grind =, push]
theorem union_self [Extensional M] [HasEmpty M] [HasSUnion M] [HasUnorderedPair M] (x : M) :
    x ∪ x = x := by
  ext; grind

@[simp, grind =]
theorem union_of_subset_right [Extensional M] [HasEmpty M] [HasSUnion M] [HasUnorderedPair M]
    (x y : M) (h : x ⊆ y) : x ∪ y = y := by
  ext z; simp only [mem_union, or_iff_right_iff_imp]
  exact fun hz ↦ h hz

@[simp, grind =]
theorem union_of_subset_left [Extensional M] [HasEmpty M] [HasSUnion M] [HasUnorderedPair M]
    (x y : M) (h : y ⊆ x) : x ∪ y = x := by
  ext z; simp only [mem_union, or_iff_left_iff_imp]
  exact fun hz ↦ h hz

@[simp, grind ., push]
theorem union_eq_right_iff_subset [Extensional M] [HasEmpty M] [HasSUnion M] [HasUnorderedPair M]
    (x y : M) :
    x ∪ y = y ↔ x ⊆ y :=
  ⟨fun _ _ _ ↦ by grind, by grind⟩

@[simp, grind ., push]
theorem union_eq_left_iff_subset [Extensional M] [HasEmpty M] [HasSUnion M] [HasUnorderedPair M]
    (x y : M) :
    x ∪ y = x ↔ y ⊆ x :=
  ⟨fun _ _ _ ↦ by grind, by grind⟩

instance [HasSUnion M] [HasUnorderedPair M] : Insert M M where
  insert x xs := {x} ∪ xs

@[simp, grind =]
theorem mem_insert [HasSUnion M] [HasUnorderedPair M] (x xs y : M) :
    y ∈ insert x xs ↔ y = x ∨ y ∈ xs := by
  simp [Insert.insert]

-- @[simp, grind! .]
-- theorem mem_two_iff [HasSUnion M] [HasUnorderedPair M] (x₁ x₂ y : M) :
--     y ∈ ({x₁, x₂} : M) ↔ y = x₁ ∨ y = x₂ := by
--   simp

-- @[simp, grind! .]
-- theorem mem_three_iff [HasSUnion M] [HasUnorderedPair M] (x₁ x₂ y : M) :
--     y ∈ ({x₁, x₂} : M) ↔ y = x₁ ∨ y = x₂ := by
--   simp



end FirstOrder.Language.MemStructure
