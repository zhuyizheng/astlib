import Astlib.ModelTheory.Defs
import Astlib.Mathlib.Sum.Basic


open FirstOrder Language BoundedFormula Fin

namespace FirstOrder.Language.MemStructure

variable (L : FirstOrder.Language) [HasMem L] (M : MemStructure)

/-- Subset relation -/
protected def Subset (x y : M) : Prop :=
  ∀ ⦃a⦄, a ∈ x → a ∈ y

instance : HasSubset M := ⟨M.Subset⟩

@[grind =]
theorem subset_iff (x y : M) : x ⊆ y ↔ ∀ z : M, (z ∈ x → z ∈ y) := ⟨id, id⟩

@[grind .]
theorem subset_refl (x : M) : x ⊆ x := fun _ h ↦ h

instance instReflSubset : Std.Refl (α := M) Subset := ⟨subset_refl _⟩

@[grind .]
theorem subset_trans (x y z : M) (hxy : x ⊆ y) (hyz : y ⊆ z) : x ⊆ z :=
  fun _ hw ↦ hyz (hxy hw)

instance : IsTrans M Subset := ⟨subset_trans _⟩

@[grind .]
theorem mem_trans_subset (x y z : M) (hxy : x ∈ y) (hyz : y ⊆ z) : x ∈ z :=
  hyz hxy

instance : Trans (α := M) (β := M) (γ := M)
  (fun x y ↦ Membership.mem y x) Subset (fun x y ↦ Membership.mem y x) :=
  ⟨fun hxy hyz ↦ hyz hxy⟩

end MemStructure

variable {L : FirstOrder.Language} [HasMem L]
  {M : MemStructure} (v : α → M) (xs : Fin n → M)

/-- `t₁ ⊆ t₂`. -/
abbrev Term.subset (t₁ t₂ : L.Term (α ⊕ Fin n)) : L.BoundedFormula α n :=
  ∀'∈ t₁ &-1 ∈' t₂.castSucc

@[inherit_doc] scoped[FirstOrder.Language]
infix:88 " ⊆' " => FirstOrder.Language.Term.subset

variable (t₁ t₂ : M.L.Term (α ⊕ Fin n))

@[simp 1100]
theorem Term.subset_iff : (t₁ ⊆' t₂).Realize v xs ↔
    t₁.realize (Sum.elim v xs) ⊆ t₂.realize (Sum.elim v xs) := by
  simp [M.subset_iff]

end FirstOrder.Language
