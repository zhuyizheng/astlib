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

variable {L : Language} {M : Type*} [L.MemStructure M]

namespace FirstOrder.Language.MemStructure


/-- Subset relation -/
protected def Subset (x y : M) : Prop :=
  ∀ ⦃a⦄, a ∈ x → a ∈ y

instance : HasSubset M := ⟨MemStructure.Subset⟩

@[grind =]
theorem subset_iff (x y : M) : x ⊆ y ↔ ∀ z : M, (z ∈ x → z ∈ y) := ⟨id, id⟩

@[grind .]
theorem subset_refl (x : M) : x ⊆ x := fun _ h ↦ h

instance : Std.Refl (α := M) Subset := ⟨subset_refl⟩

lemma subset_of_eq {x y : M} (h : x = y) : x ⊆ y := by grind

alias Eq.subset := subset_of_eq

@[grind .]
theorem subset_trans {x y z : M} (hxy : x ⊆ y) (hyz : y ⊆ z) : x ⊆ z :=
  fun _ hw ↦ hyz (hxy hw)

instance : IsTrans M Subset := ⟨@subset_trans _ _ _⟩

@[grind .]
theorem mem_trans_subset {x y z : M} (hxy : x ∈ y) (hyz : y ⊆ z) : x ∈ z :=
  hyz hxy

instance : Trans (γ := M)
  (fun x y ↦ Membership.mem y x) Subset (fun x y ↦ Membership.mem y x) :=
  ⟨fun hxy hyz ↦ hyz hxy⟩

end MemStructure

variable {n : ℕ} (xs : Fin n → M)

/-- `t₁ ⊆ t₂` as a `Δ₀` formula -/
def Term.subset₀ {L : Language} [L.HasMem] (t₁ t₂ : L.Term' n) : L.DeltaZeroBoundedFormula n :=
  ∀₀∈ t₁ (&-1 ∈₀ t₂.castSucc)


@[inherit_doc] scoped[FirstOrder.Language]
infix:88 " ⊆₀ " => FirstOrder.Language.Term.subset₀

instance {L : Language} [L.HasMem] (t₁ t₂ : L.Term' n) :
  (t₁ ⊆₀ t₂).RelFree := by
  unfold Term.subset₀; infer_instance

/-- `t₁ ⊆ t₂` as a formula -/
def Term.subset {L : Language} [L.HasMem] (t₁ t₂ : L.Term' n) := (t₁ ⊆₀ t₂).toBoundedFormula

@[inherit_doc] scoped[FirstOrder.Language]
infix:88 " ⊆' " => FirstOrder.Language.Term.subset

instance (t₁ t₂ : L.Term' n) : (t₁ ⊆' t₂).DeltaZero := ⟨t₁ ⊆₀ t₂, rfl⟩

variable (t₁ t₂ : L.Term' n)

@[simp]
theorem Term.subset₀_iff : (t₁ ⊆₀ t₂).toBoundedFormula 〘xs〙 ↔ t₁〘xs〙 ⊆ t₂〘xs〙 := by
  simp [MemStructure.subset_iff, Term.subset₀, allMem]

@[simp]
theorem Term.subset_iff : (t₁ ⊆' t₂) 〘xs〙 ↔ t₁〘xs〙 ⊆ t₂〘xs〙 := by
  simp [Term.subset]

end FirstOrder.Language
