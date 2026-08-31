/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.MemStructure.Defs
import Astlib.Mathlib.Sum.Basic
import Astlib.Basic.SetOperation.MemStructure.Levy
/-!
file docstring
-/

open FirstOrder Language BoundedFormula Fin

namespace FirstOrder.Language.MemStructure

variable (L : FirstOrder.Language) [L.HasMem] (M : MemStructure)

/-- Subset relation -/
protected def Subset (x y : M) : Prop :=
  ∀ ⦃a⦄, a ∈ x → a ∈ y

instance : HasSubset M := ⟨M.Subset⟩

@[grind =]
theorem subset_iff (x y : M) : x ⊆ y ↔ ∀ z : M, (z ∈ x → z ∈ y) := ⟨id, id⟩

@[grind .]
theorem subset_refl (x : M) : x ⊆ x := fun _ h ↦ h

instance instReflSubset : Std.Refl (α := M) Subset := ⟨subset_refl _⟩

lemma subset_of_eq {x y : M} (h : x = y) : x ⊆ y := by grind

alias Eq.subset := subset_of_eq

@[grind .]
theorem subset_trans {x y z : M} (hxy : x ⊆ y) (hyz : y ⊆ z) : x ⊆ z :=
  fun _ hw ↦ hyz (hxy hw)

instance : IsTrans M Subset := ⟨@subset_trans _⟩

@[grind .]
theorem mem_trans_subset {x y z : M} (hxy : x ∈ y) (hyz : y ⊆ z) : x ∈ z :=
  hyz hxy

instance : Trans (α := M) (β := M) (γ := M)
  (fun x y ↦ Membership.mem y x) Subset (fun x y ↦ Membership.mem y x) :=
  ⟨fun hxy hyz ↦ hyz hxy⟩

end MemStructure

variable {α : Type*} {n : ℕ} {L : FirstOrder.Language} [L.HasMem]
  {M : MemStructure} (v : α → M) (xs : Fin n → M)

/-- `t₁ ⊆ t₂` as a `Δ₀` formula -/
def Term.subset₀ (t₁ t₂ : L.Term' n) : L.DeltaZeroBoundedFormula n :=
  ∀₀∈ t₁ (&-1 ∈₀ t₂.castSucc)

-- theorem Term.isDeltaZero_subset (t₁ t₂ : L.Term' n) : (t₁.subset t₂).IsDeltaZero := by
--   simp [subset, DeltaZero.isDeltaZero]


@[inherit_doc] scoped[FirstOrder.Language]
infix:88 " ⊆₀ " => FirstOrder.Language.Term.subset₀

/-- `t₁ ⊆ t₂` as a formula -/
def Term.subset (t₁ t₂ : L.Term' n) := (t₁ ⊆₀ t₂).toBoundedFormula

@[inherit_doc] scoped[FirstOrder.Language]
infix:88 " ⊆' " => FirstOrder.Language.Term.subset

instance (t₁ t₂ : L.Term' n) : (t₁ ⊆' t₂).DeltaZero := ⟨t₁ ⊆₀ t₂, rfl⟩

variable (t₁ t₂ : M.L.Term' n)

@[simp]
theorem Term.subset_iff : (t₁ ⊆' t₂) 〘xs〙 ↔ t₁〘xs〙 ⊆ t₂〘xs〙 := by
  simp [M.subset_iff, Term.subset, Term.subset₀, allMem]

end FirstOrder.Language
