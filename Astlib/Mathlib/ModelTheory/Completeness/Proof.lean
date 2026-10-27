/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Order.Zorn
import Astlib.Mathlib.ModelTheory.Completeness.Subst

/-!
# A proof system for first-order logic with de Bruijn bound variables

We define a Hilbert-style proof system `Γ ⊢' φ`, where the set of hypotheses
`Γ : Set (L.Formula α)` is a parameter (the hypotheses may have free variables, but no dangling
bound variables), and `φ : L.BoundedFormula α n` is a bounded formula.

The dangling bound variables of `φ` play the role of eigenvariables: they do not occur in the
hypotheses, so if `φ : L.BoundedFormula α (n + 1)` is provable, then so is `∀' φ`.

The rules are modus ponens and generalization. The axioms are the hypotheses, the propositional
axioms `K`, `S` and double negation elimination, the quantifier axioms `∀' φ ⟹ φ.inst t` and
`∀' (ψ.castSucc ⟹ φ) ⟹ ψ ⟹ ∀' φ`, the nonemptiness of the universe, and the equality axioms.

## Main definitions

- `FirstOrder.Language.BoundedFormula.Provable`: the proof system, with notation `Γ ⊢' φ`.
  Since `L.Theory = Set (L.Formula Empty)`, `T ⊢' φ` makes sense for a theory `T` and
  `φ : L.BoundedFormula Empty n`.
- `FirstOrder.Language.BoundedFormula.Consistent`: `Γ` is consistent if `⊥` is not provable
  from `Γ`.

## Main results

- `Provable.deduction`, `Provable.impI`: the deduction theorem.
- `Provable.substAll`: provability is preserved by simultaneous substitution.
- `Provable.sound`, `Provable.models`: the soundness theorem.
- `Consistent.exists_maximal`: Lindenbaum's lemma.
-/

open Fin FirstOrder Language Structure

namespace FirstOrder

namespace Language

variable {L : Language} {α β : Type*} {n m l : ℕ}

namespace BoundedFormula

/-- Weaken a formula with `n` dangling bound variables to a formula with `n + 1` dangling bound
variables. The new variable `&(last n)` does not occur in `φ.castSucc`. -/
def castSucc (φ : L.BoundedFormula α n) : L.BoundedFormula α (n + 1) :=
  φ.substBoundBound Fin.castSucc

/-- `φ.inst t` is obtained from `φ` by substituting `t` for the last bound variable
`&(last n)`. -/
def inst (φ : L.BoundedFormula α (n + 1)) (t : L.Term (α ⊕ Fin n)) : L.BoundedFormula α n :=
  φ.substBound (snoc (fun i ↦ &i) t)

/-- View a formula as a bounded formula with `n` dangling bound variables, which do not occur
in it. -/
def ofFormula (φ : L.Formula α) : L.BoundedFormula α n :=
  φ.substBoundBound (Fin.elim0 : Fin 0 → Fin n)

/-! ### Substitution lemmas for `castSucc` and `inst` -/

theorem castSucc_eq_substAll (φ : L.BoundedFormula α n) :
    φ.castSucc = φ.substAll (Sum.elim (Term.var ∘ Sum.inl) (fun i ↦ &(i.castSucc))) :=
  substBoundBound_eq_substAll _ _

theorem inst_eq_substAll (φ : L.BoundedFormula α (n + 1)) (t : L.Term (α ⊕ Fin n)) :
    φ.inst t = φ.substAll (Sum.elim (Term.var ∘ Sum.inl) (snoc (fun i ↦ &i) t)) :=
  substBound_eq_substAll _ _

theorem _root_.FirstOrder.Language.Term.castSucc_subst_snoc (t u : L.Term (α ⊕ Fin n)) :
    t.castSucc.subst (Sum.elim (Term.var ∘ Sum.inl) (snoc (fun i ↦ &i) u)) = t := by
  simp only [Term.castSucc_eq_subst, Term.subst_subst]
  convert t.subst_var' with x
  rcases x with a | i
  · rfl
  · simp [Term.subst]

theorem castSucc_substAll_mapCastSucc (φ : L.BoundedFormula α n)
    (σ : α ⊕ Fin n → L.Term (β ⊕ Fin m)) :
    φ.castSucc.substAll (Term.mapCastSucc σ) = (φ.substAll σ).castSucc := by
  simp only [castSucc_eq_substAll, substAll_substAll]
  congr 1
  ext x
  rw [← Term.castSucc_eq_subst, ← Term.mapCastSucc_map_castSucc]
  cases x <;> rfl

theorem inst_substAll (φ : L.BoundedFormula α (n + 1)) (t : L.Term (α ⊕ Fin n))
    (σ : α ⊕ Fin n → L.Term (β ⊕ Fin m)) :
    (φ.inst t).substAll σ = (φ.substAll (Term.mapCastSucc σ)).inst (t.subst σ) := by
  simp only [inst_eq_substAll, substAll_substAll]
  congr 1
  ext x
  rcases x with a | i
  · exact (Term.castSucc_subst_snoc _ _).symm
  · induction i using lastCases with
    | last => simp [Term.subst]
    | cast i =>
      simp only [Sum.elim_inr, snoc_castSucc, Function.comp_apply, Term.subst,
        Term.mapCastSucc_inr_castSucc]
      exact (Term.castSucc_subst_snoc _ _).symm

theorem inst_substBound (φ : L.BoundedFormula α (n + 1)) (ts : Fin n → L.Term (α ⊕ Fin m))
    (t : L.Term (α ⊕ Fin m)) :
    (φ.substBound (snoc (fun i ↦ (ts i).castSucc) &(last m))).inst t =
      φ.substBound (snoc ts t) := by
  simp only [inst, substBound_substBound]
  congr 1
  ext i
  induction i using lastCases with
  | last => simp [snoc]
  | cast i =>
    simp only [snoc_castSucc]
    exact Term.castSucc_subst_snoc _ _

variable {M : Type*} [L.Structure M]

@[simp]
theorem realize_castSucc' (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M) (a : M) :
    φ.castSucc.Realize v (snoc xs a) ↔ φ.Realize v xs := by
  simp [castSucc]

@[simp]
theorem realize_inst (φ : L.BoundedFormula α (n + 1)) (t : L.Term (α ⊕ Fin n)) (v : α → M)
    (xs : Fin n → M) :
    (φ.inst t).Realize v xs ↔ φ.Realize v (snoc xs (t.realize (Sum.elim v xs))) := by
  simp only [inst, realize_substBound]
  congr! 1
  ext i
  induction i using lastCases <;> simp

theorem substAll_foldr_imp (l : List (L.BoundedFormula α n)) (φ : L.BoundedFormula α n)
    (σ : α ⊕ Fin n → L.Term (β ⊕ Fin m)) :
    (l.foldr BoundedFormula.imp φ).substAll σ =
      (l.map (fun ψ ↦ ψ.substAll σ)).foldr BoundedFormula.imp (φ.substAll σ) := by
  induction l <;> simp [*]

theorem ofFormula_substAll (φ : L.Formula α) (σ : α ⊕ Fin n → L.Term (β ⊕ Fin m)) :
    (ofFormula φ : L.BoundedFormula α n).substAll σ =
      φ.substAll (Sum.elim (fun a ↦ σ (Sum.inl a)) Fin.elim0) := by
  simp only [ofFormula, substBoundBound_eq_substAll, substAll_substAll]
  congr 1
  funext x
  rcases x with a | i
  · rfl
  · fin_cases i

theorem ofFormula_eq_substAll (φ : L.Formula α) :
    (ofFormula φ : L.BoundedFormula α n) =
      φ.substAll (Sum.elim (Term.var ∘ Sum.inl) Fin.elim0) := by
  rw [← substAll_var (ofFormula φ), ofFormula_substAll]
  rfl

@[simp]
theorem ofFormula_zero (φ : L.Formula α) : (ofFormula φ : L.BoundedFormula α 0) = φ := by
  rw [ofFormula_eq_substAll]
  trans φ.substAll Term.var
  · congr 1
    funext x
    rcases x with a | i
    · rfl
    · fin_cases i
  · exact substAll_var φ

@[simp]
theorem castSucc_ofFormula (φ : L.Formula α) :
    (ofFormula φ : L.BoundedFormula α n).castSucc = ofFormula φ := by
  simp only [ofFormula, castSucc, substBoundBound_substBoundBound]
  congr 1
  funext i
  fin_cases i

@[simp]
theorem realize_ofFormula (φ : L.Formula α) (v : α → M) (xs : Fin n → M) :
    (ofFormula φ : L.BoundedFormula α n).Realize v xs ↔ φ.Realize v := by
  simp only [ofFormula, realize_substBoundBound, Formula.Realize]
  congr!

/-- A Hilbert-style proof system for first-order logic with equality.

The set `Γ` of hypotheses is a parameter: the definition of `Provable Γ` does not refer to
`Provable Γ'` for any other `Γ'`. -/
inductive Provable (Γ : Set (L.Formula α)) : {n : ℕ} → L.BoundedFormula α n → Prop
  /-- The hypotheses are provable. -/
  | hyp {k} {φ : L.Formula α} : φ ∈ Γ → Provable Γ (ofFormula φ : L.BoundedFormula α k)
  /-- Modus ponens. -/
  | mp {k} {φ ψ : L.BoundedFormula α k} : Provable Γ (φ ⟹ ψ) → Provable Γ φ → Provable Γ ψ
  /-- Universal generalization. -/
  | gen {k} {φ : L.BoundedFormula α (k + 1)} : Provable Γ φ → Provable Γ (∀' φ)
  /-- The propositional axiom `K`. -/
  | implyK {k} {φ ψ : L.BoundedFormula α k} : Provable Γ (φ ⟹ ψ ⟹ φ)
  /-- The propositional axiom `S`. -/
  | implyS {k} {φ ψ θ : L.BoundedFormula α k} :
      Provable Γ ((φ ⟹ ψ ⟹ θ) ⟹ (φ ⟹ ψ) ⟹ φ ⟹ θ)
  /-- Double negation elimination. -/
  | dne {k} {φ : L.BoundedFormula α k} : Provable Γ (∼∼φ ⟹ φ)
  /-- Universal instantiation. -/
  | allElim {k} {φ : L.BoundedFormula α (k + 1)} (t : L.Term (α ⊕ Fin k)) :
      Provable Γ (∀' φ ⟹ φ.inst t)
  /-- A universal quantifier can be moved past a formula in which the quantified variable does
  not occur. -/
  | allImp {k} {ψ : L.BoundedFormula α k} {φ : L.BoundedFormula α (k + 1)} :
      Provable Γ (∀' (ψ.castSucc ⟹ φ) ⟹ ψ ⟹ ∀' φ)
  /-- The universe is nonempty. -/
  | nonempty {k} : Provable Γ (∼(∀' (⊥ : L.BoundedFormula α (k + 1))))
  /-- Equality is reflexive. -/
  | eqRefl {k} (t : L.Term (α ⊕ Fin k)) : Provable Γ (t =' t)
  /-- Equality is Euclidean; together with reflexivity, this gives symmetry and transitivity. -/
  | eqEuclidAx {k} {t₁ t₂ t₃ : L.Term (α ⊕ Fin k)} :
      Provable Γ (t₁ =' t₂ ⟹ t₁ =' t₃ ⟹ t₂ =' t₃)
  /-- Function symbols respect equality:
  `ts 0 =' us 0 ⟹ ... ⟹ ts (l - 1) =' us (l - 1) ⟹ f ts =' f us`. -/
  | funCongrAx {k l} (f : L.Functions l) (ts us : Fin l → L.Term (α ⊕ Fin k)) :
      Provable Γ ((List.ofFn fun i ↦ ts i =' us i).foldr BoundedFormula.imp
        (Term.func f ts =' Term.func f us))
  /-- Relation symbols respect equality:
  `ts 0 =' us 0 ⟹ ... ⟹ ts (l - 1) =' us (l - 1) ⟹ R ts ⟹ R us`. -/
  | relCongrAx {k l} (R : L.Relations l) (ts us : Fin l → L.Term (α ⊕ Fin k)) :
      Provable Γ ((List.ofFn fun i ↦ ts i =' us i).foldr BoundedFormula.imp
        (rel R ts ⟹ rel R us))

@[inherit_doc] scoped[FirstOrder] infix:51 " ⊢' " => FirstOrder.Language.BoundedFormula.Provable

namespace Provable

variable {Γ Γ' : Set (L.Formula α)} {φ ψ : L.BoundedFormula α n}

/-! ### Structural properties -/

/-- Strengthening. -/
theorem mono (h : Γ ⊢' φ) (hΓ : Γ ⊆ Γ') : Γ' ⊢' φ := by
  induction h with
  | hyp h => exact hyp (hΓ h)
  | mp _ _ ih₁ ih₂ => exact mp ih₁ ih₂
  | gen _ ih => exact gen ih
  | implyK => exact implyK
  | implyS => exact implyS
  | dne => exact dne
  | allElim t => exact allElim t
  | allImp => exact allImp
  | nonempty => exact nonempty
  | eqRefl t => exact eqRefl t
  | eqEuclidAx => exact eqEuclidAx
  | funCongrAx f ts us => exact funCongrAx f ts us
  | relCongrAx R ts us => exact relCongrAx R ts us

/-- A proof only uses finitely many hypotheses. -/
theorem finite (h : Γ ⊢' φ) : ∃ Γ₀ ⊆ Γ, Γ₀.Finite ∧ Γ₀ ⊢' φ := by
  induction h with
  | @hyp _ φ h => exact ⟨{φ}, by simpa using h, Set.finite_singleton _, hyp rfl⟩
  | mp _ _ ih₁ ih₂ =>
    obtain ⟨Γ₁, h₁, hfin₁, h₁'⟩ := ih₁
    obtain ⟨Γ₂, h₂, hfin₂, h₂'⟩ := ih₂
    exact ⟨Γ₁ ∪ Γ₂, Set.union_subset h₁ h₂, hfin₁.union hfin₂,
      mp (h₁'.mono Set.subset_union_left) (h₂'.mono Set.subset_union_right)⟩
  | gen _ ih =>
    obtain ⟨Γ₀, h₀, hfin, h'⟩ := ih
    exact ⟨Γ₀, h₀, hfin, gen h'⟩
  | implyK => exact ⟨∅, by simp, Set.finite_empty, implyK⟩
  | implyS => exact ⟨∅, by simp, Set.finite_empty, implyS⟩
  | dne => exact ⟨∅, by simp, Set.finite_empty, dne⟩
  | allElim t => exact ⟨∅, by simp, Set.finite_empty, allElim t⟩
  | allImp => exact ⟨∅, by simp, Set.finite_empty, allImp⟩
  | nonempty => exact ⟨∅, by simp, Set.finite_empty, nonempty⟩
  | eqRefl t => exact ⟨∅, by simp, Set.finite_empty, eqRefl t⟩
  | eqEuclidAx => exact ⟨∅, by simp, Set.finite_empty, eqEuclidAx⟩
  | funCongrAx f ts us => exact ⟨∅, by simp, Set.finite_empty, funCongrAx f ts us⟩
  | relCongrAx R ts us => exact ⟨∅, by simp, Set.finite_empty, relCongrAx R ts us⟩

theorem mp_foldr {l : List (L.BoundedFormula α n)} (h : Γ ⊢' l.foldr BoundedFormula.imp φ)
    (hl : ∀ ψ ∈ l, Γ ⊢' ψ) : Γ ⊢' φ := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    exact ih (mp h (hl a List.mem_cons_self)) fun ψ hψ ↦ hl ψ (List.mem_cons_of_mem _ hψ)

theorem imp_self : Γ ⊢' φ ⟹ φ :=
  mp (mp (implyS (ψ := φ ⟹ φ)) implyK) implyK

/-- The deduction theorem. -/
theorem deduction {χ : L.Formula α} (h : insert χ Γ ⊢' φ) : Γ ⊢' ofFormula χ ⟹ φ := by
  induction h with
  | hyp h =>
    rcases h with rfl | h
    · exact imp_self
    · exact mp implyK (hyp h)
  | mp _ _ ih₁ ih₂ => exact mp (mp implyS ih₁) ih₂
  | gen _ ih =>
    rw [← castSucc_ofFormula] at ih
    exact mp allImp (gen ih)
  | implyK => exact mp implyK implyK
  | implyS => exact mp implyK implyS
  | dne => exact mp implyK dne
  | allElim t => exact mp implyK (allElim t)
  | allImp => exact mp implyK allImp
  | nonempty => exact mp implyK nonempty
  | eqRefl t => exact mp implyK (eqRefl t)
  | eqEuclidAx => exact mp implyK eqEuclidAx
  | funCongrAx f ts us => exact mp implyK (funCongrAx f ts us)
  | relCongrAx R ts us => exact mp implyK (relCongrAx R ts us)

/-! ### Substitution -/

/-- Provability is preserved by simultaneous substitution of all the variables, provided that
the substituted hypotheses remain provable after any further substitution fixing the free
variables. This form of the hypothesis is stable under `Term.mapCastSucc`. -/
theorem substAll_of_stable {Γ' : Set (L.Formula β)} (h : Γ ⊢' φ) {m : ℕ}
    (σ : α ⊕ Fin n → L.Term (β ⊕ Fin m))
    (hΓ : ∀ γ ∈ Γ, ∀ {k} (τ : β ⊕ Fin m → L.Term (β ⊕ Fin k)),
      (∀ b, τ (Sum.inl b) = Term.var (Sum.inl b)) →
      Γ' ⊢' γ.substAll (Sum.elim (fun a ↦ (σ (Sum.inl a)).subst τ) Fin.elim0)) :
    Γ' ⊢' φ.substAll σ := by
  induction h generalizing m with
  | hyp h =>
    rw [ofFormula_substAll]
    simpa using hΓ _ h Term.var fun _ ↦ rfl
  | mp _ _ ih₁ ih₂ => exact mp (ih₁ σ hΓ) (ih₂ σ hΓ)
  | gen _ ih =>
    apply gen
    refine ih (Term.mapCastSucc σ) fun γ hγ k τ hτ ↦ ?_
    convert hΓ γ hγ (fun x ↦ (Sum.elim (Term.var ∘ Sum.inl) (fun i ↦ &i.castSucc) x).subst τ)
      hτ using 3
    exact funext fun _ ↦ Term.subst_subst _ _ _
  | implyK => exact implyK
  | implyS => exact implyS
  | dne => exact dne
  | allElim t =>
    simp only [substAll_imp, substAll_all, inst_substAll]
    exact allElim _
  | allImp =>
    simp only [substAll_imp, substAll_all, castSucc_substAll_mapCastSucc]
    exact allImp
  | nonempty => exact nonempty
  | eqRefl t => exact eqRefl _
  | eqEuclidAx => exact eqEuclidAx
  | funCongrAx f ts us =>
    simp only [substAll_foldr_imp, List.map_ofFn]
    exact funCongrAx f (fun i ↦ (ts i).subst σ) (fun i ↦ (us i).subst σ)
  | relCongrAx R ts us =>
    simp only [substAll_foldr_imp, List.map_ofFn]
    exact relCongrAx R (fun i ↦ (ts i).subst σ) (fun i ↦ (us i).subst σ)

/-- Provability is preserved by substitutions which fix the free variables. -/
theorem substAll_of_inl (h : Γ ⊢' φ) {m : ℕ} (σ : α ⊕ Fin n → L.Term (α ⊕ Fin m))
    (hσ : ∀ a, σ (Sum.inl a) = Term.var (Sum.inl a)) : Γ ⊢' φ.substAll σ := by
  apply h.substAll_of_stable σ
  intro γ hγ k τ hτ
  convert hyp hγ using 1
  rw [ofFormula_eq_substAll]
  congr 1
  funext x
  rcases x with a | i
  · simp [hσ, hτ, Term.subst]
  · fin_cases i

/-- A provable formula remains provable when a new dangling bound variable is added. -/
theorem castSucc (h : Γ ⊢' φ) : Γ ⊢' φ.castSucc := by
  rw [castSucc_eq_substAll]
  exact h.substAll_of_inl _ fun _ ↦ rfl

/-- Provability is preserved by simultaneous substitution of all the variables, provided that
the substituted hypotheses are provable. -/
theorem substAll {Γ' : Set (L.Formula β)} (h : Γ ⊢' φ) {m : ℕ}
    (σ : α ⊕ Fin n → L.Term (β ⊕ Fin m))
    (hΓ : ∀ γ ∈ Γ, Γ' ⊢' γ.substAll (Sum.elim (fun a ↦ σ (Sum.inl a)) Fin.elim0)) :
    Γ' ⊢' φ.substAll σ := by
  apply h.substAll_of_stable σ
  intro γ hγ _ τ hτ
  convert (hΓ γ hγ).substAll_of_inl τ hτ using 1
  rw [substAll_substAll]
  congr 1
  funext x
  rcases x with a | i
  · rfl
  · fin_cases i

/-! ### Derived rules -/

/-- A hypothesis is provable. -/
theorem ax {φ : L.Formula α} (h : φ ∈ Γ) : Γ ⊢' φ := by
  simpa using hyp (k := 0) h

/-- Implication introduction (the deduction theorem). -/
theorem impI {φ ψ : L.Formula α} (h : insert φ Γ ⊢' ψ) : Γ ⊢' φ ⟹ ψ := by
  simpa using h.deduction

/-- Implication elimination (modus ponens). -/
theorem impE (h₁ : Γ ⊢' φ ⟹ ψ) (h₂ : Γ ⊢' φ) : Γ ⊢' ψ :=
  mp h₁ h₂

theorem exFalso (h : Γ ⊢' (⊥ : L.BoundedFormula α n)) : Γ ⊢' φ :=
  mp dne (mp implyK h)

/-- Proof by contradiction. -/
theorem byContra {φ : L.Formula α} (h : insert (∼φ) Γ ⊢' (⊥ : L.Formula α)) : Γ ⊢' φ :=
  mp dne (impI h)

/-- Universal instantiation. -/
theorem allE {φ : L.BoundedFormula α (n + 1)} (t : L.Term (α ⊕ Fin n)) (h : Γ ⊢' ∀' φ) :
    Γ ⊢' φ.inst t :=
  mp (allElim t) h

/-- Equality is symmetric. -/
theorem eqSymm {t₁ t₂ : L.Term (α ⊕ Fin n)} (h : Γ ⊢' t₁ =' t₂) : Γ ⊢' t₂ =' t₁ :=
  mp (mp eqEuclidAx h) (eqRefl _)

/-- Equality is transitive. -/
theorem eqTrans {t₁ t₂ t₃ : L.Term (α ⊕ Fin n)} (h₁ : Γ ⊢' t₁ =' t₂) (h₂ : Γ ⊢' t₂ =' t₃) :
    Γ ⊢' t₁ =' t₃ :=
  mp (mp eqEuclidAx (eqSymm h₁)) h₂

/-- Function symbols respect equality. -/
theorem funCongr (f : L.Functions l) {ts us : Fin l → L.Term (α ⊕ Fin n)}
    (h : ∀ i, Γ ⊢' ts i =' us i) : Γ ⊢' Term.func f ts =' Term.func f us := by
  apply mp_foldr (funCongrAx f ts us)
  simp only [List.forall_mem_ofFn_iff]
  exact h

/-- Relation symbols respect equality. -/
theorem relCongr (R : L.Relations l) {ts us : Fin l → L.Term (α ⊕ Fin n)}
    (h : ∀ i, Γ ⊢' ts i =' us i) (h' : Γ ⊢' rel R ts) : Γ ⊢' rel R us := by
  refine mp (mp_foldr (relCongrAx R ts us) ?_) h'
  simp only [List.forall_mem_ofFn_iff]
  exact h

/-- If a contradiction is provable with an extra dangling bound variable, then it is already
provable. This uses the fact that the universe is nonempty. -/
theorem bot_of_succ (h : Γ ⊢' (⊥ : L.BoundedFormula α (n + 1))) :
    Γ ⊢' (⊥ : L.BoundedFormula α n) :=
  mp nonempty (gen h)

/-! ### Soundness -/

/-- The soundness theorem: if `φ` is provable from `Γ`, then `φ` holds whenever `Γ` holds, in
every nonempty structure. -/
theorem sound (h : Γ ⊢' φ) [Nonempty M] (v : α → M)
    (hΓ : ∀ γ ∈ Γ, γ.Realize v) : ∀ xs : Fin n → M, φ.Realize v xs := by
  induction h with
  | hyp h =>
    intro xs
    rw [realize_ofFormula]
    exact hΓ _ h
  | mp _ _ ih₁ ih₂ =>
    intro xs
    have himp := ih₁ xs
    rw [realize_imp] at himp
    exact himp (ih₂ xs)
  | gen _ ih =>
    intro xs
    rw [realize_all]
    exact fun a ↦ ih (snoc xs a)
  | implyK => exact fun _ ↦ by simp only [realize_imp]; tauto
  | implyS => exact fun _ ↦ by simp only [realize_imp]; tauto
  | dne => exact fun _ ↦ by simp only [realize_imp, realize_not]; tauto
  | allElim t =>
    intro xs
    simp only [realize_imp, realize_all, realize_inst]
    exact fun h ↦ h _
  | allImp =>
    intro xs
    simp only [realize_imp, realize_all, realize_castSucc']
    exact fun h hψ a ↦ h a hψ
  | nonempty =>
    intro xs
    simp only [realize_not, realize_all]
    exact fun h ↦ h (Classical.arbitrary M)
  | eqRefl t => exact fun _ ↦ by simp
  | eqEuclidAx => exact fun _ ↦ by simp +contextual
  | funCongrAx f ts us =>
    intro xs
    rw [realize_foldr_imp]
    intro h
    simp only [realize_bdEqual, Term.realize]
    simp only [List.forall_mem_ofFn_iff] at h
    exact congrArg _ (funext fun i ↦ by simpa using h i)
  | relCongrAx R ts us =>
    intro xs
    rw [realize_foldr_imp]
    intro h
    simp only [List.forall_mem_ofFn_iff] at h
    have e : (fun i ↦ (ts i).realize (Sum.elim v xs)) = fun i ↦ (us i).realize (Sum.elim v xs) :=
      funext fun i ↦ by simpa using h i
    simp only [Realize, e]
    exact id

/-- The soundness theorem for theories: if `φ` is provable from the sentences of `T`, then
`φ` holds in every model of `T`. -/
theorem models {T : L.Theory} {φ : L.BoundedFormula Empty n} (h : T ⊢' φ) : T ⊨ᵇ φ := by
  intro M v xs
  refine h.sound v (fun ψ hψ ↦ ?_) xs
  rw [Subsingleton.elim v default]
  exact Theory.realize_sentence_of_mem T hψ

end Provable

/-! ### Consistency -/

/-- A set of formulas is consistent if it does not prove `⊥`. -/
def Consistent (Γ : Set (L.Formula α)) : Prop :=
  ¬ Γ ⊢' (⊥ : L.Formula α)

/-- **Lindenbaum's lemma**: every consistent set is contained in a maximal consistent set. -/
theorem Consistent.exists_maximal {Γ : Set (L.Formula α)} (h : Consistent Γ) :
    ∃ Δ, Γ ⊆ Δ ∧ Maximal Consistent Δ := by
  refine zorn_subset_nonempty {Δ | Consistent Δ} (fun c hc hchain hne ↦ ?_) Γ h
  refine ⟨⋃₀ c, fun hbot ↦ ?_, fun s hs ↦ Set.subset_sUnion_of_mem hs⟩
  obtain ⟨Γ₀, h₀, hfin, hΓ₀⟩ := hbot.finite
  obtain ⟨t, ht, h₀t⟩ :=
    hchain.directedOn.exists_mem_subset_of_finite_of_subset_sUnion hne hfin h₀
  exact hc ht (hΓ₀.mono h₀t)

section Maximal

variable {Δ : Set (L.Formula α)} {φ ψ : L.Formula α}

theorem mem_of_provable (hΔ : Maximal Consistent Δ) (h : Δ ⊢' φ) : φ ∈ Δ :=
  hΔ.mem_of_prop_insert fun hbot ↦ hΔ.prop (.impE (.impI hbot) h)

theorem provable_iff_mem (hΔ : Maximal Consistent Δ) : Δ ⊢' φ ↔ φ ∈ Δ :=
  ⟨mem_of_provable hΔ, .ax⟩

theorem bot_notMem (hΔ : Maximal Consistent Δ) : ⊥ ∉ Δ :=
  fun h ↦ hΔ.prop (.ax h)

theorem imp_mem_iff (hΔ : Maximal Consistent Δ) : φ ⟹ ψ ∈ Δ ↔ (φ ∈ Δ → ψ ∈ Δ) := by
  refine ⟨fun h hφ ↦ mem_of_provable hΔ (.impE (.ax h) (.ax hφ)), fun h ↦ ?_⟩
  by_cases hφ : φ ∈ Δ
  · exact mem_of_provable hΔ (.impI (.ax (.inr (h hφ))))
  · have : ¬ Consistent (insert φ Δ) := fun hcon ↦ hφ (hΔ.mem_of_prop_insert hcon)
    simp only [Consistent, not_not] at this
    exact mem_of_provable hΔ (.impI this.exFalso)

end Maximal

end BoundedFormula

end Language

end FirstOrder
