-- import Init.Core

import Astlib.ModelTheory.Syntax
import Astlib.Mathlib.ModelTheory.Semantics
import Astlib.Basic.Axioms
import Astlib.Mathlib.Fin.Basic

open FirstOrder Language BoundedFormula Fin

variable (L : FirstOrder.Language) [HasMem L]

namespace FirstOrder.Language

structure MemStructure where
  Carrier : Type*
  L : FirstOrder.Language
  [hasMem : L.HasMem]
  [struc : L.Structure Carrier]
  [nonempty' : Nonempty Carrier]

-- Porting note: In Lean4, other instances precedes `FirstOrder.Language.Theory.ModelType.struc`,
-- it's issues in `ModelTheory.Satisfiability`. So, we increase these priorities. TODO
attribute [instance 2000] MemStructure.L MemStructure.hasMem MemStructure.struc
  MemStructure.nonempty'

namespace MemStructure

attribute [coe] MemStructure.Carrier

instance : CoeSort MemStructure (Type _) where
  coe M := M.Carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. TODO -/
def of (M : Type w) [L.Structure M] [L.HasMem] [Nonempty M] : MemStructure :=
  ⟨M, L⟩

variable (M : MemStructure)

instance instNonempty : Nonempty M :=
  inferInstance

noncomputable instance instInhabited : Inhabited M :=
  Classical.inhabited_of_nonempty'

/-- Membership in a set -/
protected def Mem (x y : M) : Prop :=
  Structure.RelMap (M.hasMem.memSymb) ![y, x]

instance instMembership : Membership M M where
  mem := M.Mem

@[simp]
theorem realize_mem {M : MemStructure} (t₁ t₂ : M.L.Term (α ⊕ Fin n)) {v : α → M} {xs : Fin n → M} :
    (t₁ ∈' t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) ∈ t₂.realize (Sum.elim v xs) := by
  simp [mem_boundedFormula, Membership.mem, MemStructure.Mem]

/-- Subset relation -/
protected def Subset (x y : M) : Prop :=
  ∀ ⦃a⦄, a ∈ x → a ∈ y

instance instHasSubset : HasSubset M where
  Subset := M.Subset

@[grind =]
theorem subset_iff (x y : M) : x ⊆ y ↔ ∀ z : M, (z ∈ x → z ∈ y) := ⟨id, id⟩

@[grind .]
theorem subset_refl (x : M) : x ⊆ x := fun _ h ↦ h

instance instReflSubset : Std.Refl (α := M) Subset where
  refl := subset_refl _

@[grind .]
theorem subset_trans (x y z : M) (hxy : x ⊆ y) (hyz : y ⊆ z) : x ⊆ z :=
  fun _ hw ↦ hyz (hxy hw)

instance instIsTransSubset : IsTrans M Subset where
  trans := subset_trans _

@[grind .]
theorem subset_trans_mem (x y z : M) (hxy : x ∈ y) (hyz : y ⊆ z) : x ∈ z :=
  hyz hxy

instance instIsTransMemSubsetMem : Trans (α := M) (β := M) (γ := M)
  (fun x y ↦ Membership.mem y x) Subset (fun x y ↦ Membership.mem y x) where
  trans := fun hxy hyz ↦ hyz hxy

end MemStructure

end FirstOrder.Language




section ExUnique
variable {L : Language} [L.Structure M]

-- {T : L.Theory} {M : T.ModelType}

variable {φ : L.BoundedFormula α n}

theorem exists_of_ex {φ : L.BoundedFormula α (n + 1)} {v : α → M}
    {xs : Fin n → M} (h : (∃' φ).Realize v xs) :
    ∃ a : M, φ.Realize v (snoc xs a) := by
  simpa using h

theorem existsUnique_of_exUnique {φ : L.BoundedFormula α (n + 1)} {v : α → M}
    {xs : Fin n → M} (h : (∃!' φ).Realize v xs) :
    ∃! a : M, φ.Realize v (snoc xs a) := by
  simp only [BoundedFormula.exUnique, Function.comp_apply, realize_ex, Nat.succ_eq_add_one,
    realize_inf, realize_all, realize_imp, realize_bdEqual, Term.realize_var, Sum.elim_inr,
    snoc_last] at h
  obtain ⟨a, ha₁, ha₂⟩ := h
  refine ⟨a, ha₁, fun b ↦ ?_⟩
  simp only
  convert ha₂ b using 1
  · rw [realize_liftAt' (by omega)]
    apply Eq.to_iff
    congr
    grind [snoc]
  · grind [snoc, Fin.val_last_plus_one_minus_one]


theorem existsUnique_of_exUnique_sentence {φ : L.BoundedFormula Empty 1}
    (h : (∃!' φ).Realize default (default : _ → M)) :
    ∃! a : M, φ.Realize default ![a] := by
  convert existsUnique_of_exUnique h
  ext i
  simp [snoc]


end ExUnique
