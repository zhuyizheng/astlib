import Mathlib.ModelTheory.Bundled
import Mathlib.ModelTheory.Satisfiability
import Astlib.ModelTheory.Syntax
import Astlib.ModelTheory.Semantics

open FirstOrder Language Theory

variable {α : Type*} {L : FirstOrder.Language} {T : L.Theory} {φ ψ θ : L.BoundedFormula α n}

namespace FirstOrder

namespace Language

namespace Theory

namespace ModelsBoundedFormula

theorem of_imp (h : T ⊨ᵇ φ) (h' : T ⊨ᵇ φ ⟹ ψ) : T ⊨ᵇ ψ := by
  intro M v xs
  grind [h M v xs, h' M v xs, BoundedFormula.realize_imp]

theorem of_imp_imp (h : T ⊨ᵇ φ) (h' : T ⊨ᵇ ψ) (h'' : T ⊨ᵇ φ ⟹ ψ ⟹ θ) : T ⊨ᵇ θ :=
  h'.of_imp (h.of_imp h'')

variable (φ ψ : L.BoundedFormula α n)
@[simp]
theorem and_iff : T ⊨ᵇ φ ⊓ ψ ↔ T ⊨ᵇ φ ∧ T ⊨ᵇ ψ := by
  constructor
  · intro h
    constructor <;> exact h.of_imp (by simp +contextual [ModelsBoundedFormula])
  · intro ⟨h₁, h₂⟩
    exact h₁.of_imp_imp h₂ (by simp +contextual [ModelsBoundedFormula])

@[simp]
theorem iff_iff : T ⊨ᵇ φ ⇔ ψ ↔ T ⊨ᵇ φ ⟹ ψ ∧ T ⊨ᵇ ψ ⟹ φ := and_iff _ _

-- theorem all' (φ : L.BoundedFormula α (n + m)) : T ⊨ᵇ (φ.all' m).not ⇔ φ.not.ex' m := by
--   induction m with
--   | zero => simp +contextual [ModelsBoundedFormula]
--   | succ m ih =>
--     rw [BoundedFormula.all_succ, BoundedFormula.ex_succ]
--     have := ih φ.all


variable {φ ψ : L.BoundedFormula α (n + m)}

theorem all' (h : T ⊨ᵇ φ) : T ⊨ᵇ φ.all' m := by
  grind [ModelsBoundedFormula, BoundedFormula.realize_all']

theorem imp_all'_imp : T ⊨ᵇ (φ.all' m) ⟹ ((φ ⟹ ψ).all' m) ⟹ (ψ.all' m) := by
  simp +contextual [ModelsBoundedFormula]

theorem all'_of_all'_imp (h : T ⊨ᵇ φ.all' m) (h' : T ⊨ᵇ (φ ⟹ ψ).all' m) : T ⊨ᵇ ψ.all' m :=
  h.of_imp_imp h' imp_all'_imp

variable {φ ψ : L.BoundedFormula α (n + 1)}

theorem all (h : T ⊨ᵇ φ) : T ⊨ᵇ ∀' φ := h.all'

theorem imp_all_imp : T ⊨ᵇ ∀' φ ⟹ ∀' (φ ⟹ ψ) ⟹ ∀' ψ := imp_all'_imp (m := 1)

theorem all_of_all_imp (h : T ⊨ᵇ ∀' φ) (h' : T ⊨ᵇ ∀' (φ ⟹ ψ)) : T ⊨ᵇ ∀' ψ :=
  h.all'_of_all'_imp h' (m := 1)


variable {φ ψ : L.BoundedFormula α n}

/- `⊨ᵇ` is monotone in `T` -/
theorem mono (h : T ⊨ᵇ φ) (h' : T ⊆ T') : T' ⊨ᵇ φ :=
  fun M' v xs ↦ h (M'.subtheoryModel h') v xs

theorem mono' (h : T ⊨ᵇ φ) (h' : T ⊆ T') : T' ⊨ᵇ φ := by
  intro M' v xs
  exact h (M'.subtheoryModel h') v xs



end ModelsBoundedFormula


/-- `T ⊨ᵇ U` means that `T ⊨ᵇ φ` for any `φ` in `U` -/
def ModelsTheory.{u, v, w} (T U : L.Theory) : Prop :=
  -- ∀ (M : Type*) (FirstOrder.Language.Structure.{u, v, w} L M → M ⊨ T → ∀ φ ∈ U, M ⊨ φ
  ∀ (M : ModelType.{u, v, max u v w} T), ∀ φ ∈ U, M ⊨ φ

@[inherit_doc FirstOrder.Language.Theory.ModelsTheory]
infixl:51 " ⊨ᵇ " => ModelsTheory -- input using \|= or \vDash, but not using \models

-- theorem models_theory_iff (T U : L.Theory) :
--     T ⊨ᵇ U ↔ ∀ (M : ModelType T) (v : α → M), φ.Realize v :=
--   forall_congr' fun _ => forall_congr' fun _ => Unique.forall_iff

/-- A model of a theory is also a model of any **TODO**. -/
-- @[simps]
def ModelType.modelsTheoryModel.{u, v, w} {T U : L.Theory} (M : ModelType.{u, v, max u v w} T)
  (h : T ⊨ᵇ U) : U.ModelType where
  Carrier := M
  is_model := ⟨fun _φ hφ => h M _φ hφ⟩

-- instance modelsTheoryModel {T U : L.Theory} (M : T.ModelType) (h : T ⊨ᵇ U) :
--     M.modelsTheoryModel h ⊨ T :=
--   M.is_model

namespace ModelsBoundedFormula

/- `⊨ᵇ` is monotone in `T` -/
theorem of_modelsTheory {T U : L.Theory} {n : ℕ} {α : Type w}
    {φ : L.BoundedFormula α n} (h : U ⊨ᵇ φ) (h' : ModelsTheory.{u, v, w} T U) : T ⊨ᵇ φ := by
  intro M' v xs
  exact h (ModelType.modelsTheoryModel M' h') v xs

end ModelsBoundedFormula


end Theory

end Language

end FirstOrder
