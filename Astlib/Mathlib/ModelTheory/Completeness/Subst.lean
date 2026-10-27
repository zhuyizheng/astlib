/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Mathlib.ModelTheory.Semantics

/-!
# Simultaneous substitution of all variables

A bounded formula `φ : L.BoundedFormula α n` has two kinds of variables: the free variables
indexed by `α` and the (de Bruijn) bound variables indexed by `Fin n`.
`φ.substAll σ : L.BoundedFormula β m` replaces all of them simultaneously, according to
`σ : α ⊕ Fin n → L.Term (β ⊕ Fin m)`.

Every syntactic operation needed in the proof of the completeness theorem (weakening of the
bound context, instantiating a quantifier, renaming free variables, turning a free variable
into a bound one, ...) is an instance of `substAll`, so that the general lemmas
`substAll_substAll`, `substAll_var`, `substAll_congr` and `realize_substAll` are all we need.
-/

open Fin FirstOrder Language Structure

namespace FirstOrder

namespace Language

variable {L : Language} {α β γ : Type*} {n m k l : ℕ}

namespace Term

theorem subst_subst (t : L.Term α) (σ : α → L.Term β) (τ : β → L.Term γ) :
    (t.subst σ).subst τ = t.subst (fun x ↦ (σ x).subst τ) := by
  induction t with
  | var x => rfl
  | func f ts ih => simp [subst, ih]

@[simp]
theorem subst_var' (t : L.Term α) : t.subst var = t := by
  induction t with
  | var x => rfl
  | func f ts ih => simp [subst, ih]

theorem substBound_eq_subst (t : L.Term (α ⊕ Fin n)) (ts : Fin n → L.Term (α ⊕ Fin m)) :
    t.substBound ts = t.subst (Sum.elim (var ∘ Sum.inl) ts) := rfl

theorem castSucc_eq_subst (t : L.Term (α ⊕ Fin n)) :
    t.castSucc = t.subst (Sum.elim (var ∘ Sum.inl) (fun i ↦ &(i.castSucc))) := rfl

/-- Lift a simultaneous substitution under a binder: the new bound variable is sent to
itself. -/
def mapCastSucc (σ : α ⊕ Fin n → L.Term (β ⊕ Fin m)) : α ⊕ Fin (n + 1) → L.Term (β ⊕ Fin (m + 1)) :=
  Sum.elim (fun a ↦ (σ (Sum.inl a)).castSucc)
    (snoc (fun i ↦ (σ (Sum.inr i)).castSucc) &(last m))

variable (σ : α ⊕ Fin n → L.Term (β ⊕ Fin m)) (τ : β ⊕ Fin m → L.Term (γ ⊕ Fin k))

@[simp]
theorem mapCastSucc_inl (a : α) : mapCastSucc σ (Sum.inl a) = (σ (Sum.inl a)).castSucc := rfl

@[simp]
theorem mapCastSucc_inr_castSucc (i : Fin n) :
    mapCastSucc σ (Sum.inr i.castSucc) = (σ (Sum.inr i)).castSucc := by
  simp [mapCastSucc]

@[simp]
theorem mapCastSucc_inr_last : mapCastSucc σ (Sum.inr (last n)) = &(last m) := by
  simp [mapCastSucc]

theorem mapCastSucc_map_castSucc (x : α ⊕ Fin n) :
    mapCastSucc σ (Sum.map id Fin.castSucc x) = (σ x).castSucc := by
  cases x <;> simp

theorem castSucc_subst_mapCastSucc (t : L.Term (α ⊕ Fin n)) :
    t.castSucc.subst (mapCastSucc σ) = (t.subst σ).castSucc := by
  simp only [castSucc_eq_subst, subst_subst]
  congr 1
  ext x
  rw [← castSucc_eq_subst, ← mapCastSucc_map_castSucc]
  cases x <;> rfl

theorem mapCastSucc_comp :
    mapCastSucc (fun x ↦ (σ x).subst τ) = fun x ↦ (mapCastSucc σ x).subst (mapCastSucc τ) := by
  ext x
  rcases x with a | i
  · simp only [mapCastSucc_inl, castSucc_subst_mapCastSucc]
  · induction i using lastCases with
    | last => simp [subst]
    | cast i => simp only [mapCastSucc_inr_castSucc, castSucc_subst_mapCastSucc]

@[simp]
theorem mapCastSucc_var : mapCastSucc (var : α ⊕ Fin n → L.Term (α ⊕ Fin n)) = var := by
  ext x
  rcases x with a | i
  · rfl
  · induction i using lastCases <;> simp

theorem mapCastSucc_elim (ts : Fin n → L.Term (α ⊕ Fin m)) :
    mapCastSucc (Sum.elim (var ∘ Sum.inl) ts) =
      Sum.elim (var ∘ Sum.inl) (snoc (fun i ↦ (ts i).castSucc) &(last m)) :=
  rfl

variable {M : Type*} [L.Structure M]

theorem realize_castSucc' (t : L.Term (α ⊕ Fin n)) (v : α → M) (xs : Fin n → M) (a : M) :
    t.castSucc.realize (Sum.elim v (snoc xs a)) = t.realize (Sum.elim v xs) := by
  simp

theorem realize_mapCastSucc (v : β → M) (xs : Fin m → M) (a : M) (x : α ⊕ Fin (n + 1)) :
    (mapCastSucc σ x).realize (Sum.elim v (snoc xs a)) =
      Sum.elim (fun b ↦ (σ (Sum.inl b)).realize (Sum.elim v xs))
        (snoc (fun i ↦ (σ (Sum.inr i)).realize (Sum.elim v xs)) a) x := by
  rcases x with b | i
  · simp
  · induction i using lastCases <;> simp

theorem subst_congr_of_varFinsetLeft [DecidableEq α] {σ τ : α ⊕ Fin n → L.Term β}
    (t : L.Term (α ⊕ Fin n))
    (h : ∀ a ∈ t.varFinsetLeft, σ (Sum.inl a) = τ (Sum.inl a))
    (h' : ∀ i, σ (Sum.inr i) = τ (Sum.inr i)) : t.subst σ = t.subst τ := by
  induction t with
  | var x =>
    rcases x with a | i
    · exact h a (by simp [varFinsetLeft])
    · exact h' i
  | func f ts ih =>
    simp only [subst, func.injEq, heq_eq_eq, true_and]
    ext i
    exact ih i fun a ha ↦ h a (by simpa [varFinsetLeft] using ⟨i, ha⟩)

end Term

namespace BoundedFormula

/-- `φ.substAll σ` simultaneously replaces every variable `x` of `φ`, free or bound, by the
term `σ x`. -/
def substAll : {n m : ℕ} → L.BoundedFormula α n → (α ⊕ Fin n → L.Term (β ⊕ Fin m)) →
    L.BoundedFormula β m
  | _, _, falsum, _ => falsum
  | _, _, equal t₁ t₂, σ => equal (t₁.subst σ) (t₂.subst σ)
  | _, _, rel R ts, σ => rel R (fun i ↦ (ts i).subst σ)
  | _, _, imp φ ψ, σ => imp (φ.substAll σ) (ψ.substAll σ)
  | _, _, all φ, σ => all (φ.substAll (Term.mapCastSucc σ))

variable (σ : α ⊕ Fin n → L.Term (β ⊕ Fin m)) (τ : β ⊕ Fin m → L.Term (γ ⊕ Fin k))

@[simp]
theorem substAll_falsum : (falsum : L.BoundedFormula α n).substAll σ = falsum := rfl

@[simp]
theorem substAll_bot : (⊥ : L.BoundedFormula α n).substAll σ = ⊥ := rfl

@[simp]
theorem substAll_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂).substAll σ = equal (t₁.subst σ) (t₂.subst σ) := rfl

@[simp]
theorem substAll_bdEqual (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (t₁ =' t₂).substAll σ = t₁.subst σ =' t₂.subst σ := rfl

@[simp]
theorem substAll_rel (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts).substAll σ = rel R (fun i ↦ (ts i).subst σ) := rfl

@[simp]
theorem substAll_imp (φ ψ : L.BoundedFormula α n) :
    (φ ⟹ ψ).substAll σ = φ.substAll σ ⟹ ψ.substAll σ := rfl

@[simp]
theorem substAll_not (φ : L.BoundedFormula α n) : (∼φ).substAll σ = ∼(φ.substAll σ) := rfl

@[simp]
theorem substAll_all (φ : L.BoundedFormula α (n + 1)) :
    (∀' φ).substAll σ = ∀' (φ.substAll (Term.mapCastSucc σ)) := rfl

@[simp]
theorem substAll_ex (φ : L.BoundedFormula α (n + 1)) :
    (∃' φ).substAll σ = ∃' (φ.substAll (Term.mapCastSucc σ)) := rfl

theorem substBound_eq_substAll (φ : L.BoundedFormula α n) (ts : Fin n → L.Term (α ⊕ Fin m)) :
    φ.substBound ts = φ.substAll (Sum.elim (Term.var ∘ Sum.inl) ts) := by
  induction φ generalizing m with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R us => rfl
  | imp φ₁ φ₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | all ψ ih => simp [ih, Term.mapCastSucc_elim]

theorem substBoundBound_eq_substAll (φ : L.BoundedFormula α n) (f : Fin n → Fin m) :
    φ.substBoundBound f = φ.substAll (Sum.elim (Term.var ∘ Sum.inl) (fun i ↦ &(f i))) :=
  substBound_eq_substAll _ _

theorem substAll_substAll (φ : L.BoundedFormula α n) :
    (φ.substAll σ).substAll τ = φ.substAll (fun x ↦ (σ x).subst τ) := by
  induction φ generalizing m k β γ with
  | falsum => rfl
  | equal t₁ t₂ => simp [Term.subst_subst]
  | rel R us => simp [Term.subst_subst]
  | imp φ₁ φ₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | all ψ ih => simp [ih, Term.mapCastSucc_comp]

@[simp]
theorem substAll_var (φ : L.BoundedFormula α n) : φ.substAll Term.var = φ := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp
  | rel R us => simp
  | imp φ₁ φ₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | all ψ ih => simp [ih]

/-- `φ.substAll σ` only depends on the values of `σ` at the variables of `φ`. -/
theorem substAll_congr [DecidableEq α] {σ τ : α ⊕ Fin n → L.Term (β ⊕ Fin m)}
    (φ : L.BoundedFormula α n)
    (h : ∀ a ∈ φ.freeVarFinset, σ (Sum.inl a) = τ (Sum.inl a))
    (h' : ∀ i, σ (Sum.inr i) = τ (Sum.inr i)) : φ.substAll σ = φ.substAll τ := by
  induction φ generalizing m with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [freeVarFinset, Finset.mem_union] at h
    exact congrArg₂ equal (Term.subst_congr_of_varFinsetLeft t₁ (fun a ha ↦ h a (.inl ha)) h')
      (Term.subst_congr_of_varFinsetLeft t₂ (fun a ha ↦ h a (.inr ha)) h')
  | rel R us =>
    simp only [freeVarFinset, Finset.mem_biUnion] at h
    exact congrArg (rel R) <| funext fun i ↦
      Term.subst_congr_of_varFinsetLeft _ (fun a ha ↦ h a ⟨i, by simp, ha⟩) h'
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [freeVarFinset, Finset.mem_union] at h
    exact congrArg₂ imp (ih₁ (fun a ha ↦ h a (.inl ha)) h') (ih₂ (fun a ha ↦ h a (.inr ha)) h')
  | all ψ ih =>
    exact congrArg all <| ih (fun a ha ↦ by simp [h a ha]) fun i ↦ by
      induction i using lastCases <;> simp [h']

variable {M : Type*} [L.Structure M]

theorem realize_substAll (φ : L.BoundedFormula α n) (v : β → M) (xs : Fin m → M) :
    (φ.substAll σ).Realize v xs ↔
      φ.Realize (fun a ↦ (σ (Sum.inl a)).realize (Sum.elim v xs))
        (fun i ↦ (σ (Sum.inr i)).realize (Sum.elim v xs)) := by
  induction φ generalizing m with
  | falsum => rfl
  | equal | rel =>
    simp only [substAll_equal, substAll_rel, Realize, Term.realize_subst]
    rw [← Sum.elim_comp_inl_inr fun a ↦ (σ a).realize (Sum.elim v xs)]
    rfl
  | imp φ₁ φ₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | all ψ ih =>
    simp only [substAll_all, realize_all, ih, Term.realize_mapCastSucc, Sum.elim_inl, Sum.elim_inr]

end BoundedFormula

end Language

end FirstOrder
