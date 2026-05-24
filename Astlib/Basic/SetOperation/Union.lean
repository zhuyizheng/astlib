import Astlib.Basic.SetOperation.Pair

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y z : M)

variable (M) in
noncomputable instance [M.ClosedUnderSUnion] [M.ClosedUnderPair] : Union M where
  union x y := ⋃₀ (unorderedPair x y)

@[simp, grind =]
theorem mem_union [M.ClosedUnderSUnion] [M.ClosedUnderPair] : x ∈ y ∪ z ↔ x ∈ y ∨ x ∈ z := by
  simp [Union.union]

@[grind =]
theorem union_comm [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] : x ∪ y = y ∪ x := by
  ext; grind

variable (M) in
instance instCommutativeUnion [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
  Std.Commutative (α := M) Union.union where
  comm := fun x y ↦ union_comm x y

@[grind =]
theorem union_assoc [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    (x ∪ y) ∪ z = x ∪ (y ∪ z) := by
  ext; grind

variable (M) in
instance instAssociativeUnion [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
  Std.Associative (α := M) Union.union where
  assoc := fun x y z ↦ union_assoc x y z

@[simp, grind =, push]
theorem empty_union [M.Extensional] [M.HasEmpty] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    (∅ : M) ∪ x = x := by
  ext; grind

@[simp, grind =, push]
theorem union_empty [M.Extensional] [M.HasEmpty] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    x ∪ (∅ : M) = x := by
  grind

@[simp, grind =, push]
theorem union_self [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    x ∪ x = x := by
  ext; grind

@[grind! .]
theorem left_subset_union [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    x ⊆ x ∪ y := by
  grind

@[grind! .]
theorem right_subset_union [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    y ⊆ x ∪ y := by
  grind

@[simp, grind =]
theorem union_of_subset_right [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
    {x y : M} (h : x ⊆ y) : x ∪ y = y := by
  ext z; simp only [mem_union, or_iff_right_iff_imp]
  exact fun hz ↦ h hz

@[simp, grind =]
theorem union_of_subset_left [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair]
    {x y : M} (h : y ⊆ x) : x ∪ y = x := by
  ext z; simp only [mem_union, or_iff_left_iff_imp]
  exact fun hz ↦ h hz

@[simp, grind ., push]
theorem union_eq_right_iff_subset [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    x ∪ y = y ↔ x ⊆ y := by
  grind

@[simp, grind ., push]
theorem union_eq_left_iff_subset [M.Extensional] [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    x ∪ y = x ↔ y ⊆ x := by
  grind

end FirstOrder.Language.MemStructure
