import Astlib.Mathlib.ModelTheory.Syntax

open FirstOrder Language Fin Term BoundedFormula

variable {L L' : Language} {I : L →ᴸ L'} {m n n' n'' l k : ℕ}
  (t t₁ t₂ : L.Term' n) (φ ψ : L.BoundedFormula' n)

namespace FirstOrder.Language.LHom

-- @[simp]
theorem onTerm_var (k : Fin n) :
    I.onTerm (&k : L.Term' n) = &k := by
  simp

@[simp]
theorem onTerm_var' (k : Fin n) :
    I.onTerm (var (Sum.inr k) : L.Term' n) = &k := by
  simp

@[simp]
theorem onTerm_const (c : L.Constants) :
    I.onTerm (c.term : L.Term' n) = Constants.term (I.onFunction c) := by
  simp only [Constants.term, onTerm, func.injEq, heq_eq_eq, true_and]
  ext i; fin_cases i

@[simp]
theorem onTerm_substBound (ts : Fin n → L.Term' m) :
    I.onTerm (t.substBound ts) =
      (I.onTerm t).substBound (fun i ↦ (I.onTerm (ts i))) := by
  induction t with
  | var i => cases i <;> simp [Term.substBound]
  | func f _ ih => simp [ih]

@[simp]
theorem onTerm_substBoundBound (f : Fin n → Fin m) :
    I.onTerm (t.substBoundBound f) =
      (I.onTerm t).substBoundBound f :=
  onTerm_substBound _ _

@[simp]
theorem onBoundedFormula_bot :
    I.onBoundedFormula (⊥ : L.BoundedFormula' n) = ⊥ := rfl

@[simp]
theorem onBoundedFormula_top :
    I.onBoundedFormula (⊤ : L.BoundedFormula' n) = ⊤ := rfl

@[simp]
theorem onBoundedFormula_bdEqual :
    I.onBoundedFormula (t₁ =' t₂) = I.onTerm t₁ =' I.onTerm t₂ := rfl

@[simp]
theorem onBoundedFormula_imp :
    I.onBoundedFormula (φ ⟹ ψ) = I.onBoundedFormula φ ⟹ I.onBoundedFormula ψ := rfl

@[simp]
theorem onBoundedFormula_not :
    I.onBoundedFormula (∼φ) = ∼(I.onBoundedFormula φ) := rfl

@[simp]
theorem onBoundedFormula_sup :
    I.onBoundedFormula (φ ⊔ ψ) = I.onBoundedFormula φ ⊔ I.onBoundedFormula ψ := rfl

@[simp]
theorem onBoundedFormula_inf :
    I.onBoundedFormula (φ ⊓ ψ) = I.onBoundedFormula φ ⊓ I.onBoundedFormula ψ := rfl

@[simp]
theorem onBoundedFormula_iff :
    I.onBoundedFormula (φ ⇔ ψ) = I.onBoundedFormula φ ⇔ I.onBoundedFormula ψ := rfl

variable (φ : L.BoundedFormula' (n + 1))

@[simp]
theorem onBoundedFormula_all :
    I.onBoundedFormula (∀' φ) = ∀' I.onBoundedFormula φ := rfl

@[simp]
theorem onBoundedFormula_ex :
    I.onBoundedFormula (∃' φ) = ∃' I.onBoundedFormula φ := rfl

@[simp]
theorem onBoundedFormula_substBound (φ : L.BoundedFormula' n) (ts : Fin n → L.Term' m) :
    I.onBoundedFormula (φ.substBound ts) =
      (I.onBoundedFormula φ).substBound (fun i ↦ (I.onTerm (ts i))) := by
  induction φ generalizing m with
  | falsum => simp [BoundedFormula.substBound]
  | equal u₁ u₂ => simp [BoundedFormula.substBound, Term.bdEqual]
  | rel R us => simp [BoundedFormula.substBound, Relations.boundedFormula, funext_iff]
  | imp φ₁ φ₂ ih₁ ih₂ => simp [BoundedFormula.substBound, ih₁, ih₂]
  | all ψ ih =>
    simp only [BoundedFormula.substBound, Term.castSucc, Term.castAdd, Term.castLE,
      castLE_succ_castSucc, Function.comp_apply, onBoundedFormula.eq_5, ih, onBoundedFormula,
      substBound_all, all.injEq]
    congr
    ext i
    induction i using lastCases <;> simp

@[simp]
theorem onBoundedFormula_substBoundBound (φ : L.BoundedFormula' n) (f : Fin n → Fin m) :
    I.onBoundedFormula (φ.substBoundBound f) =
      (I.onBoundedFormula φ).substBoundBound f :=
  onBoundedFormula_substBound _ _


end FirstOrder.Language.LHom
