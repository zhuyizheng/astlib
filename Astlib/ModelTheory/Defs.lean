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

instance : Nonempty M := inferInstance

noncomputable instance : Inhabited M := Classical.inhabited_of_nonempty'

/-- Membership in a set -/
protected def Mem (x y : M) : Prop :=
  Structure.RelMap (M.hasMem.memSymb) ![y, x]

instance : Membership M M := ⟨M.Mem⟩

@[simp]
theorem realize_mem {M : MemStructure} (t₁ t₂ : M.L.Term (α ⊕ Fin n)) {v : α → M} {xs : Fin n → M} :
    (t₁ ∈' t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) ∈ t₂.realize (Sum.elim v xs) := by
  simp [mem_boundedFormula, Membership.mem, MemStructure.Mem]

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
