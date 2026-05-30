import Astlib.Basic.SetOperation.Comprehension
import Astlib.Basic.SetOperation.Union

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y z : M)

variable (M) in
noncomputable instance : Inter M := ⟨fun x y ↦ {∈ x | &2 ∈' &0 〘y〙₀}⟩

variable [M.ClosedUnderDeltaZeroComprehension]

@[simp, grind =]
theorem mem_inter_iff : x ∈ y ∩ z ↔ x ∈ y ∧ x ∈ z := by
  simp [Inter.inter]

@[grind =]
theorem inter_comm [M.Extensional] : x ∩ y = y ∩ x := by
  ext; grind

variable (M) in
instance instCommutativeInter [M.Extensional] :
  Std.Commutative (α := M) Inter.inter where
  comm := fun x y ↦ inter_comm x y

@[grind =]
theorem inter_assoc [M.Extensional] :
    (x ∩ y) ∩ z = x ∩ (y ∩ z) := by
  ext; grind

variable (M) in
instance instAssociativeInter [M.Extensional] :
  Std.Associative (α := M) Inter.inter where
  assoc := fun x y z ↦ inter_assoc x y z

@[simp, grind ., push]
theorem notin_of_inter_empty_mem_left (h : x ∩ y = ∅) (hz : z ∈ x) : z ∉ y := by
  by_contra!
  have : z ∈ x ∩ y := by grind
  grind

@[simp, grind ., push]
theorem notin_of_inter_empty_mem_right (h : x ∩ y = ∅) (hz : z ∈ y) : z ∉ x := by
  grind

@[simp, grind =, push]
theorem empty_inter [M.Extensional] :
    (∅ : M) ∩ x = ∅ := by
  ext; grind

@[simp, grind =, push]
theorem inter_empty [M.Extensional] :
    x ∩ (∅ : M) = ∅ := by
  grind

@[simp, grind =, push]
theorem inter_self [M.Extensional] :
    x ∩ x = x := by
  ext; grind

@[grind! .]
theorem inter_subset_left [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    x ∩ y ⊆ x := by
  grind

@[grind! .]
theorem inter_subset_right [M.ClosedUnderSUnion] [M.ClosedUnderPair] :
    x ∩ y ⊆ y := by
  grind

variable [M.Extensional]

@[simp, grind =]
theorem inter_of_subset_right
    {x y : M} (h : x ⊆ y) : x ∩ y = x := by
  ext z; simp only [mem_inter_iff, and_iff_left_iff_imp]
  exact fun hz ↦ h hz

@[simp, grind =]
theorem inter_of_subset_left
    {x y : M} (h : y ⊆ x) : x ∩ y = y := by
  ext z; simp only [mem_inter_iff, and_iff_right_iff_imp]
  exact fun hz ↦ h hz

@[simp, grind ., push]
theorem inter_eq_right_iff_subset :
    x ∩ y = y ↔ y ⊆ x := by
  grind

@[simp, grind ., push]
theorem inter_eq_left_iff_subset :
    x ∩ y = x ↔ x ⊆ y := by
  grind

variable [M.ClosedUnderSUnion] [M.ClosedUnderPair]

theorem inter_union_distrib_left : x ∩ (y ∪ z) = x ∩ y ∪ x ∩ z := by
  ext; grind

theorem union_inter_distrib_right : (x ∪ y) ∩ z = x ∩ z ∪ y ∩ z := by
  ext; grind

theorem union_inter_distrib_left : x ∪ y ∩ z = (x ∪ y) ∩ (x ∪ z) := by
  ext; grind

theorem inter_union_distrib_right : x ∩ y ∪ z = (x ∪ z) ∩ (y ∪ z) := by
  ext; grind

end FirstOrder.Language.MemStructure
