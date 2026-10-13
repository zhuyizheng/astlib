/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
-- import Astlib.Basic.SetOperation.MemStructure.Levy
import Astlib.Basic.Axiom.KP.SigmaOneBoundedFormula.Syntax
import Astlib.Basic.Axiom.KP.Semantics
import Astlib.Basic.SetOperation.Rudimentary.Semantics
import Astlib.Basic.SetOperation.PrimitiveRecursive.Semantics
/-!
file docstring
-/

open FirstOrder Language BoundedFormula Theory Fin MemStructure PrimitiveRecursiveTerm DeltaZeroBoundedFormula

variable {L : FirstOrder.Language.{u, v}} {M : Type max u v}
  [L.MemStructure M] [L.ExtraConstantsUnaryRelationsOnly]
  [Inhabited M] [Extensional M] [RudClosed M] (x : M) (xs : Fin n → M)

namespace FirstOrder

namespace Language

namespace SigmaOneBoundedFormula

variable (φ ψ : L.SigmaOneBoundedFormula n)

theorem realize_top : (⊤ : L.SigmaOneBoundedFormula n).toBoundedFormula 〘xs〙 := by
  simp [toBoundedFormula, Top.top]

theorem realize_bot : ¬(⊥ : L.SigmaOneBoundedFormula n).toBoundedFormula 〘xs〙 := by
  simp [toBoundedFormula]

theorem realize_sup : (φ ⊔ ψ).toBoundedFormula 〘xs〙 ↔ φ.toBoundedFormula 〘xs〙 ∨ ψ.toBoundedFormula 〘xs〙 := by
  simp only [toBoundedFormula, max, sup, toBoundedFormula_sup', realize'_ex, realize'_imp,
    realize'_not]
  grind

theorem realize_ex {φ : L.SigmaOneBoundedFormula (n + 1)} (hφ : φ.deltaZeroBody.IsRelFree) :
    φ.ex.toBoundedFormula 〘xs〙 ↔ ∃ y, φ.toBoundedFormula 〘snoc xs y〙 := by
  simp only [toBoundedFormula, ex, toBoundedFormula_inf, realize'_ex, realize'_inf,
    RudimentaryTerm.isCharFree_var, RudimentaryTerm.realize_isOrderedPair,
    RudimentaryTerm.realize_basic, snoc_nat, val_last, lt_self_iff_false, ↓reduceDIte]
  constructor
  · rintro ⟨y, ⟨y₁, y₂, rfl⟩, hy⟩
    rw [realize_substBoundRud hφ (by simp [Fin.forall_iff_castSucc])] at hy
    use y₁, y₂
    convert hy with i
    revert i
    simp [Fin.forall_iff_castSucc]
  · rintro ⟨y₁, y₂, hy₁y₂⟩
    use !(y₁, y₂), by simp [IsOrderedPair]
    rw [realize_substBoundRud hφ (by simp [Fin.forall_iff_castSucc])]
    convert hy₁y₂ with i
    revert i
    simp [Fin.forall_iff_castSucc]


theorem realize_inf {φ ψ : L.SigmaOneBoundedFormula n}
    (hφ : φ.deltaZeroBody.IsRelFree) (hψ : ψ.deltaZeroBody.IsRelFree) :
    (φ ⊓ ψ).toBoundedFormula 〘xs〙 ↔ φ.toBoundedFormula 〘xs〙 ∧ ψ.toBoundedFormula 〘xs〙 := by
  simp only [toBoundedFormula, min, inf, toBoundedFormula_inf', realize'_ex, realize'_not,
    realize'_imp, RudimentaryTerm.isCharFree_var, RudimentaryTerm.realize_isOrderedPair,
    RudimentaryTerm.realize_basic, snoc_last, Classical.not_imp, not_not, and_imp]
  constructor
  · rintro ⟨_, ⟨y₁, y₂, rfl⟩, hy₂, hy₃⟩
    rw [realize_substBoundRud hφ (by simp [Fin.forall_iff_castSucc])] at hy₂
    rw [realize_substBoundRud hψ (by simp [Fin.forall_iff_castSucc])] at hy₃
    refine ⟨⟨y₁, ?_⟩, ⟨y₂, ?_⟩⟩
    · convert hy₂ with i
      revert i
      simp [Fin.forall_iff_castSucc]
    · convert hy₃ with i
      revert i
      simp [Fin.forall_iff_castSucc]
  · rintro ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩
    refine ⟨!(y₁, y₂), by simp [IsOrderedPair], ?_, ?_⟩
    · rw [realize_substBoundRud hφ (by simp [Fin.forall_iff_castSucc])]
      convert hy₁ with i
      revert i
      simp [Fin.forall_iff_castSucc]
    · rw [realize_substBoundRud hψ (by simp [Fin.forall_iff_castSucc])]
      convert hy₂ with i
      revert i
      simp [Fin.forall_iff_castSucc]

omit [Inhabited M] [Extensional M] [RudClosed M] in
theorem realize_allMem [ModelsKP M]
    {φ : L.SigmaOneBoundedFormula (n + 1)} (hφ : φ.deltaZeroBody.IsRelFree)
    (t : L.Term' n) :
    (φ.allMem t).toBoundedFormula 〘xs〙 ↔ ∃ y ∈ t〘xs〙, φ.toBoundedFormula 〘snoc xs y〙 := by
  sorry



end SigmaOneBoundedFormula

end FirstOrder.Language
