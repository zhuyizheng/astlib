/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.ModelTheory.Satisfiability
import Astlib.Mathlib.ModelTheory.Completeness.Henkin

/-!
# Gödel's completeness theorem

## Main results

- `FirstOrder.Language.BoundedFormula.Provable.of_models`: if `φ` holds whenever `Γ` holds, in
  every nonempty structure, then `Γ ⊢' φ`.
- `FirstOrder.Language.Theory.models_iff_provable`: **Gödel's completeness theorem**
  `T ⊨ᵇ φ ↔ T ⊢' φ`, for `φ : L.BoundedFormula Empty n`.
- `FirstOrder.Language.Theory.modelsBoundedFormula'_iff_provable`: the same, for models in any
  universe `Type (max u v u')`.
- `FirstOrder.Language.Theory.isSatisfiable_iff_consistent`: a theory is satisfiable iff it
  is consistent.
-/

open Fin FirstOrder Language Structure

universe u v w u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α : Type w} {n : ℕ}

namespace BoundedFormula

/-- **Gödel's completeness theorem** for formulas without dangling bound variables. -/
theorem Provable.of_models_formula {Γ : Set (L.Formula α)} {φ : L.Formula α}
    (h : ∀ (M : Type (max u v w u')) [L.Structure M] [Nonempty M] (v : α → M),
      (∀ ψ ∈ Γ, ψ.Realize v) → φ.Realize v) : Γ ⊢' φ := by
  contrapose! h with hφ
  have hcons : Consistent (insert (∼φ) Γ) := fun hbot ↦ hφ (.byContra hbot)
  obtain ⟨β, σ, Δ, hmax, hhenkin, hsub⟩ := hcons.exists_henkin
  have hΔ : IsHenkin Δ := ⟨hmax, hhenkin⟩
  let v₀ : β → hΔ.TermModel := fun b ↦ hΔ.toTermModel (Term.var (Sum.inl b))
  let v : α → hΔ.TermModel := fun a ↦ (σ (Sum.inl a)).realize (Sum.elim v₀ default)
  have hreal (γ : L.Formula α) (hγ : γ ∈ insert (∼φ) Γ) : γ.Realize v := by
    rw [Formula.Realize]
    have hmem : BoundedFormula.substAll γ σ ∈ Δ := hsub γ hγ
    simp only [← hΔ.realize_iff_mem, realize_substAll] at hmem
    convert hmem
  -- Lift the term model to the universe `max u v w u'`.
  let : L.Structure (ULift.{u'} hΔ.TermModel) := Equiv.ulift.symm.inducedStructure
  let liftEquiv : hΔ.TermModel ≃[L] ULift.{u'} hΔ.TermModel :=
    Equiv.ulift.symm.inducedStructureEquiv
  have hΓ (ψ : L.Formula α) (hψ : ψ ∈ Γ) : ψ.Realize (liftEquiv ∘ v) := by
    rw [StrongHomClass.realize_formula]
    exact hreal ψ (by simp [hψ])
  refine ⟨ULift.{u'} hΔ.TermModel, inferInstance, inferInstance, liftEquiv ∘ v, hΓ, ?_⟩
  rw [StrongHomClass.realize_formula, ← Formula.realize_not]
  exact hreal (∼φ) (by simp)

/-- **Gödel's completeness theorem**: if `φ` holds whenever `Γ` holds, in every nonempty
structure, then `φ` is provable from `Γ`. -/
theorem Provable.of_models {Γ : Set (L.Formula α)} {φ : L.BoundedFormula α n}
    (h : ∀ (M : Type (max u v w u')) [L.Structure M] [Nonempty M] (v : α → M)
      (xs : Fin n → M), (∀ ψ ∈ Γ, ψ.Realize v) → φ.Realize v xs) : Γ ⊢' φ := by
  -- Turn the dangling bound variables of `φ` into free variables.
  let ρ' : α ⊕ Fin 0 → L.Term ((α ⊕ Fin n) ⊕ Fin 0) :=
    Sum.elim (fun a ↦ Term.var (Sum.inl (Sum.inl a))) Fin.elim0
  let ρ : α ⊕ Fin n → L.Term ((α ⊕ Fin n) ⊕ Fin 0) := fun x ↦ Term.var (Sum.inl x)
  have h₀ : (fun γ ↦ γ.substAll ρ') '' Γ ⊢' (φ.substAll ρ : L.Formula (α ⊕ Fin n)) := by
    refine of_models_formula.{u, v, w, u'} fun M _ _ v hΓ ↦ ?_
    simp only [Formula.Realize, realize_substAll]
    refine h M (v ∘ Sum.inl) (v ∘ Sum.inr) fun γ hγ ↦ ?_
    have := hΓ _ ⟨γ, hγ, rfl⟩
    simp only [Formula.Realize, realize_substAll] at this
    rw [Formula.Realize]
    convert this using 2
    rfl
  -- Turn them back into bound variables.
  let τ : (α ⊕ Fin n) ⊕ Fin 0 → L.Term (α ⊕ Fin n) :=
    Sum.elim (Sum.elim (Term.var ∘ Sum.inl) (fun i ↦ &i)) Fin.elim0
  have hsubst (δ : L.Formula (α ⊕ Fin n)) (hδ : δ ∈ (fun γ ↦ γ.substAll ρ') '' Γ) :
      Γ ⊢' δ.substAll (Sum.elim (fun b ↦ τ (Sum.inl b)) Fin.elim0) := by
    obtain ⟨γ, hγ, rfl⟩ := hδ
    convert Provable.hyp hγ using 1
    simp only [substAll_substAll, ofFormula_eq_substAll]
    congr 1
    funext x
    rcases x with a | i
    · rfl
    · fin_cases i
  convert h₀.substAll τ hsubst using 1
  rw [substAll_substAll]
  trans φ.substAll Term.var
  · exact (substAll_var φ).symm
  congr 1
  funext x
  rcases x with a | i <;> rfl

/-- The soundness and completeness theorem. -/
theorem provable_iff {Γ : Set (L.Formula α)} {φ : L.BoundedFormula α n} :
    Γ ⊢' φ ↔ ∀ (M : Type (max u v w u')) [L.Structure M] [Nonempty M] (v : α → M)
      (xs : Fin n → M), (∀ ψ ∈ Γ, ψ.Realize v) → φ.Realize v xs :=
  ⟨fun h _ _ _ v xs hΓ ↦ h.sound v hΓ xs, Provable.of_models.{u, v, w, u'}⟩

end BoundedFormula

namespace Theory

open BoundedFormula

/-- `T ⊨' φ`: `φ` holds in every nonempty model of `T` in `Type (max u v w u')`, on all inputs,
where `u'` is an extra universe parameter. This is a variant of `T ⊨ᵇ φ`, which only quantifies
over models in `Type (max u v w)`. -/
def ModelsBoundedFormula' (T : L.Theory) (φ : L.BoundedFormula α n) : Prop :=
  ∀ (M : Type (max u v w u')) [L.Structure M] [M ⊨ T] [Nonempty M] (v : α → M)
    (xs : Fin n → M), φ.Realize v xs

@[inherit_doc] scoped[FirstOrder] infix:51 " ⊨' " =>
  FirstOrder.Language.Theory.ModelsBoundedFormula'

variable {T : L.Theory} {φ : L.BoundedFormula Empty n}

theorem ModelsBoundedFormula.modelsBoundedFormula' {φ : L.BoundedFormula α n} (h : T ⊨ᵇ φ) :
    T ⊨' φ :=
  fun M _ _ _ _ _ ↦ h.realize_boundedFormula M

/-- The soundness theorem, for models in an arbitrary universe. -/
theorem _root_.FirstOrder.Language.BoundedFormula.Provable.modelsBoundedFormula'
    (h : T ⊢' φ) : T ⊨' φ :=
  h.models.modelsBoundedFormula'

/-- **Gödel's completeness theorem**: if `φ` holds in every model of `T` in some universe
`Type (max u v u')`, then `φ` is provable from `T`. -/
theorem ModelsBoundedFormula'.provable (h : ModelsBoundedFormula'.{u, v, 0, u'} T φ) :
    T ⊢' φ := by
  refine Provable.of_models.{u, v, 0, u'} fun M _ _ v xs hΓ ↦ ?_
  have : M ⊨ T := by
    rw [Theory.model_iff]
    intro ψ hψ
    have hψ' := hΓ ψ hψ
    rwa [Subsingleton.elim v default] at hψ'
  exact h M v xs

/-- **Gödel's completeness theorem**: if `φ` holds in every model of `T`, then `φ` is provable
from `T`. -/
theorem ModelsBoundedFormula.provable (h : T ⊨ᵇ φ) : T ⊢' φ :=
  ModelsBoundedFormula'.provable.{u, v, 0} h.modelsBoundedFormula'

/-- **Gödel's completeness theorem**, together with the soundness theorem, for models in any
universe `Type (max u v u')`. -/
theorem modelsBoundedFormula'_iff_provable : T ⊨' φ ↔ T ⊢' φ :=
  ⟨ModelsBoundedFormula'.provable, Provable.modelsBoundedFormula'⟩

/-- **Gödel's completeness theorem**, together with the soundness theorem: `φ` holds in every
model of `T` iff `φ` is provable from `T`. -/
theorem models_iff_provable : T ⊨ᵇ φ ↔ T ⊢' φ :=
  ⟨ModelsBoundedFormula.provable, Provable.models⟩

/-- **Gödel's completeness theorem**, model existence form: a theory is satisfiable iff it is
consistent. -/
theorem isSatisfiable_iff_consistent : T.IsSatisfiable ↔ BoundedFormula.Consistent T :=
  ⟨fun ⟨M⟩ h ↦ h.models M default default,
    fun h ↦ by_contra fun hns ↦ h (ModelsBoundedFormula.provable fun M ↦ (hns ⟨M⟩).elim)⟩

end Theory

end Language

end FirstOrder
