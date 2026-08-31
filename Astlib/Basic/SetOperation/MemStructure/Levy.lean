/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.MemStructure.Defs
import Astlib.Basic.SetOperation.MemStructure.Syntax
import Astlib.Mathlib.ModelTheory.Satisfiability
import Astlib.Mathlib.ModelTheory.Bundled
/-!
file docstring
-/

open FirstOrder Language BoundedFormula Theory Fin

variable {L : FirstOrder.Language.{u, v}} [L.HasMem]

namespace FirstOrder

namespace Language

inductive DeltaZeroBoundedFormula [L.HasMem] : ℕ → Type max u v
  | falsum {n : ℕ} : DeltaZeroBoundedFormula n
  | equal {n : ℕ} (t₁ t₂ : L.Term' n) : DeltaZeroBoundedFormula n
  | mem {n : ℕ} (t₁ t₂ : L.Term' n) : DeltaZeroBoundedFormula n
  | imp {n : ℕ} (f₁ f₂ : DeltaZeroBoundedFormula n) : DeltaZeroBoundedFormula n
  | allMem {n : ℕ} (t : L.Term' n) (f : DeltaZeroBoundedFormula (n + 1)) :
    DeltaZeroBoundedFormula n
  | rel {n : ℕ} (R : L.Relations 1) (t : L.Term' n) :
    DeltaZeroBoundedFormula n

instance : Inhabited (L.DeltaZeroBoundedFormula n) := ⟨DeltaZeroBoundedFormula.falsum⟩

namespace DeltaZeroBoundedFormula

infix:88 " =₀ " => FirstOrder.Language.DeltaZeroBoundedFormula.equal

infix:88 " ∈₀ " => FirstOrder.Language.DeltaZeroBoundedFormula.mem

def not (φ : L.DeltaZeroBoundedFormula n) : L.DeltaZeroBoundedFormula n :=
  φ.imp falsum

def sup (φ ψ : L.DeltaZeroBoundedFormula n) : L.DeltaZeroBoundedFormula n :=
  φ.not.imp ψ

def inf (φ ψ : L.DeltaZeroBoundedFormula n) : L.DeltaZeroBoundedFormula n :=
  (φ.imp ψ.not).not

instance : Max (L.DeltaZeroBoundedFormula n) := ⟨sup⟩

instance : Min (L.DeltaZeroBoundedFormula n) := ⟨inf⟩

def iff (φ ψ : L.DeltaZeroBoundedFormula n) : L.DeltaZeroBoundedFormula n :=
  (φ.imp ψ).inf (ψ.imp φ)

@[inherit_doc] scoped[FirstOrder] infixr:62 " ⟹ " =>
  FirstOrder.Language.DeltaZeroBoundedFormula.imp
-- input \==>

@[inherit_doc] scoped[FirstOrder] prefix:arg "∼" =>
  FirstOrder.Language.DeltaZeroBoundedFormula.not
-- input \~, the ASCII character ~ has too low precedence

@[inherit_doc] scoped[FirstOrder] infixl:61 " ⇔ " =>
  FirstOrder.Language.DeltaZeroBoundedFormula.iff
-- input \<=>

instance : Bot (L.DeltaZeroBoundedFormula n) := ⟨falsum⟩

instance : Top (L.DeltaZeroBoundedFormula n) := ⟨∼falsum⟩

@[inherit_doc, match_pattern] scoped[FirstOrder]
notation "∀₀∈ " x:arg y:50 => FirstOrder.Language.DeltaZeroBoundedFormula.allMem x y

def exMem (t : L.Term' n) (φ : L.DeltaZeroBoundedFormula (n + 1)) :
  L.DeltaZeroBoundedFormula n :=
  ∼(∀₀∈ t ∼φ)

@[inherit_doc, match_pattern] scoped[FirstOrder]
notation "∃₀∈ " x:arg y:50 => FirstOrder.Language.DeltaZeroBoundedFormula.exMem x y

@[coe, simp]
def toBoundedFormula (φ : L.DeltaZeroBoundedFormula n) : L.BoundedFormula' n :=
  match φ with
  | falsum => .falsum
  | equal t₁ t₂ => t₁ =' t₂
  | mem t₁ t₂ => t₁ ∈' t₂
  | imp φ₁ φ₂ => φ₁.toBoundedFormula ⟹ φ₂.toBoundedFormula
  | allMem t φ => ∀'∈ t φ.toBoundedFormula
  | rel R t => R.boundedFormula₁ t

instance : Coe (L.DeltaZeroBoundedFormula n) (L.BoundedFormula' n) := ⟨toBoundedFormula⟩

@[simp]
theorem toBoundedFormula_bot :
    (⊥ : L.DeltaZeroBoundedFormula n).toBoundedFormula = ⊥ := rfl

@[simp]
theorem toBoundedFormula_not (φ : L.DeltaZeroBoundedFormula n) :
    (∼φ).toBoundedFormula = ∼φ.toBoundedFormula := rfl

@[simp]
theorem toBoundedFormula_top :
    (⊤ : L.DeltaZeroBoundedFormula n).toBoundedFormula = ⊤ := rfl

@[simp]
theorem toBoundedFormula_sup (φ ψ : L.DeltaZeroBoundedFormula n) :
    (φ ⊔ ψ).toBoundedFormula = φ.toBoundedFormula ⊔ ψ.toBoundedFormula :=
  rfl

@[simp]
theorem toBoundedFormula_inf (φ ψ : L.DeltaZeroBoundedFormula n) :
    (φ ⊓ ψ).toBoundedFormula = φ.toBoundedFormula ⊓ ψ.toBoundedFormula :=
  rfl

@[simp]
theorem toBoundedFormula_iff (φ ψ : L.DeltaZeroBoundedFormula n) :
    (φ ⇔ ψ).toBoundedFormula = φ.toBoundedFormula ⇔ ψ.toBoundedFormula :=
  rfl

@[simp]
theorem toBoundedFormula_exMem (φ : L.DeltaZeroBoundedFormula (n + 1))
    (t : L.Term' n) :
    (φ.exMem t).toBoundedFormula = ∃'∈ t φ.toBoundedFormula := rfl

def substBound
  {L : Language} [L.HasMem] {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
  (ts : Fin n → L.Term' m) : L.DeltaZeroBoundedFormula m :=
  match φ with
  | .falsum => .falsum
  | .equal t₁ t₂ => .equal (t₁.substBound ts) (t₂.substBound ts)
  | .mem t₁ t₂ => .mem (t₁.substBound ts) (t₂.substBound ts)
  | .imp φ₁ φ₂ => imp (φ₁.substBound ts) (φ₂.substBound ts)
  | .allMem t φ => allMem
      (t.substBound ts)
      (φ.substBound (snoc (fun i ↦ (ts i).castSucc) &(last m)))
  | .rel R t => .rel R (t.substBound ts)

@[simp]
theorem substBound_bot
  {L : Language} [L.HasMem]
  (ts : Fin n → L.Term' m) :
  (⊥ : L.DeltaZeroBoundedFormula n).substBound ts = ⊥ := rfl

@[simp]
theorem substBound_falsum
  {L : Language} [L.HasMem]
  (ts : Fin n → L.Term' m) :
  (falsum : L.DeltaZeroBoundedFormula n).substBound ts = ⊥ := rfl

@[simp, norm_cast]
theorem coe_substBound
    {L : Language} [L.HasMem] {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
    (ts : Fin n → L.Term' m) :
    (φ.substBound ts) = (φ : L.BoundedFormula' n).substBound ts := by
  induction φ generalizing m with
  | falsum => norm_cast
  | equal t₁ t₂ => norm_cast
  | mem t₁ t₂ =>
    simp [substBound, toBoundedFormula]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp [substBound, ih₁, ih₂]
  | allMem t ψ ih =>
    simp [substBound, BoundedFormula.allMem, Term.substBoundBound, ih]
  | rel R ts =>
    simp [substBound, toBoundedFormula]

def substBoundBound
  {L : Language} [L.HasMem] {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
  (f : Fin n → Fin m) : L.DeltaZeroBoundedFormula m :=
  φ.substBound (fun i ↦ &(f i))

@[simp, norm_cast]
theorem coe_substBoundBound
    {L : Language} [L.HasMem] {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
    (f : Fin n → Fin m) :
    (φ.substBoundBound f) = (φ : L.BoundedFormula' n).substBoundBound f :=
  φ.coe_substBound (fun i ↦ &(f i))

def cast
  {L : Language} [L.HasMem] {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
  (h : n = m) : L.DeltaZeroBoundedFormula m :=
  φ.substBoundBound (Fin.cast h)

@[simp, norm_cast]
theorem coe_cast
    {L : Language} [L.HasMem] {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
    (h : n = m) :
    (φ.cast h) = (φ : L.BoundedFormula' n).cast h :=
  φ.coe_substBoundBound (Fin.cast h)


variable {M : MemStructure}

def castLHom : M.L'.DeltaZeroBoundedFormula n → M.L.DeltaZeroBoundedFormula n
  | falsum => falsum
  | equal t₁ t₂  => equal t₁.castLHom t₂.castLHom
  | mem t₁ t₂ => mem t₁.castLHom t₂.castLHom
  | imp f₁ f₂ => imp f₁.castLHom f₂.castLHom
  | allMem t f => allMem t.castLHom f.castLHom
  | rel R t => rel (M.LHom.onRelation R) t.castLHom

@[simp]
theorem castLHom_falsum :
    (falsum : M.L'.DeltaZeroBoundedFormula n).castLHom =
      (⊥ : M.L.DeltaZeroBoundedFormula n) := rfl

@[simp]
theorem castLHom_bot :
    (⊥ : M.L'.DeltaZeroBoundedFormula n).castLHom =
      (⊥ : M.L.DeltaZeroBoundedFormula n) := rfl

@[simp]
theorem castLHom_top :
    (⊤ : M.L'.DeltaZeroBoundedFormula n).castLHom =
      (⊤ : M.L.DeltaZeroBoundedFormula n) := rfl

@[simp]
theorem castLHom_bdEqual :
    (equal t₁ t₂ : M.L'.DeltaZeroBoundedFormula n).castLHom =
      equal t₁.castLHom t₂.castLHom := rfl

-- @[simp]
-- theorem castLHom_bdEqual' :
--     L.extraConstantsOnlyLHom.onBoundedFormula (t₁ ∈' t₂) =
--       L.extraConstantsOnlyLHom.onTerm t₁ ∈' L.extraConstantsOnlyLHom.onTerm t₂ := rfl

@[simp]
theorem castLHom_mem :
    (mem t₁ t₂ : M.L'.DeltaZeroBoundedFormula n).castLHom =
      (mem t₁.castLHom t₂.castLHom : M.L.DeltaZeroBoundedFormula n) := by
  rfl

-- @[simp]
-- theorem castLHom_mem' :
--     L.extraConstantsOnlyLHom.onBoundedFormula (&i ∈' &j) = (&i ∈' &j : L.BoundedFormula' n) := by
--   simp [Function.comp_apply]

@[simp]
theorem castLHom_imp :
    (φ ⟹ ψ : M.L'.DeltaZeroBoundedFormula n).castLHom =
      φ.castLHom ⟹ ψ.castLHom := rfl

@[simp]
theorem castLHom_not :
    (∼φ : M.L'.DeltaZeroBoundedFormula n).castLHom =
      ∼(φ.castLHom) := rfl

@[simp]
theorem castLHom_sup :
    (φ ⊔ ψ : M.L'.DeltaZeroBoundedFormula n).castLHom =
      φ.castLHom ⊔ ψ.castLHom := rfl

@[simp]
theorem castLHom_inf :
    (φ ⊓ ψ : M.L'.DeltaZeroBoundedFormula n).castLHom =
      φ.castLHom ⊓ ψ.castLHom := rfl

@[simp]
theorem castLHom_iff :
    (φ ⇔ ψ : M.L'.DeltaZeroBoundedFormula n).castLHom =
      φ.castLHom ⇔ ψ.castLHom := rfl

@[simp]
theorem castLHom_allMem (φ : M.L'.DeltaZeroBoundedFormula (n + 1))
    (t : M.L'.Term' n) :
    (∀₀∈ t φ).castLHom = ∀₀∈ t.castLHom φ.castLHom := by
  simp [castLHom]

@[simp]
theorem castLHom_exMem (φ : M.L'.DeltaZeroBoundedFormula (n + 1))
    (t : M.L'.Term' n) :
    (∃₀∈ t φ).castLHom = ∃₀∈ t.castLHom φ.castLHom := by
  simp [exMem]

@[simp]
theorem castLHom_toBoundedFormula (φ : M.L'.DeltaZeroBoundedFormula n) :
    φ.toBoundedFormula.castLHom = φ.castLHom.toBoundedFormula := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂  => simp
  | mem t₁ t₂ => simp
  | imp f₁ f₂ => simp [*]
  | allMem t f => simp [*]
  | rel R t =>
    simp only [BoundedFormula.castLHom, toBoundedFormula, Relations.boundedFormula₁,
      Relations.boundedFormula, LHom.onBoundedFormula, castLHom, BoundedFormula.rel.injEq,
      heq_eq_eq, true_and]
    ext i; fin_cases i; rfl

@[simp]
theorem castLHom_substBound (φ : M.L'.DeltaZeroBoundedFormula n)
    (ts : Fin n → M.L'.Term' m) :
    (φ.substBound ts).castLHom = φ.castLHom.substBound (fun i ↦ (ts i).castLHom) := by
  induction φ generalizing m with
  | falsum => simp
  | equal t₁ t₂  => simp [substBound]
  | mem t₁ t₂ => simp [substBound]
  | imp f₁ f₂ => simp [substBound, *]
  | allMem t f ih =>
    simp only [substBound, Term.castSucc, Term.castAdd, Term.castLE, castLE_succ_castSucc,
      Function.comp_apply, castLHom_allMem, Term.castLHom_substBound, ih, allMem.injEq, true_and]
    congr
    ext i; cases i using lastCases <;> simp
  | rel R t =>
    simp [substBound, castLHom]

@[simp]
theorem castLHom_substBoundBound (φ : M.L'.DeltaZeroBoundedFormula n)
    (f : Fin n → Fin m) :
    (φ.substBoundBound f).castLHom = φ.castLHom.substBoundBound f :=
  castLHom_substBound _ _

@[simp]
theorem castLHom_cast (φ : M.L'.DeltaZeroBoundedFormula n)
    (h : n = n') :
    (φ.cast h).castLHom = φ.castLHom.cast h :=
  castLHom_substBound _ _


-- @[simp]
-- theorem toBoundedFormula_realize (φ : M.L.DeltaZeroBoundedFormula n)
--     (xs : Fin n → M) :
--     (φ.exMem t).toBoundedFormula = ∃₀∈ t φ.toBoundedFormula := rfl



-- def substBound {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
--     (ts : Fin n → L.Term' m) : L.DeltaZeroBoundedFormula m :=
--   match φ with
--   | falsum => falsum
--   | equal t₁ t₂ => equal (t₁.substBound ts) (t₂.substBound ts)
--   | mem t₁ t₂ => mem (t₁.substBound ts) (t₂.substBound ts)
--   | imp φ₁ φ₂ => imp (φ₁.substBound ts) (φ₂.substBound ts)
--   | allMem t φ =>
--     ∀₀∈ (t.substBound ts) (φ.substBound (snoc (fun i ↦ (ts i).castSucc) &-1))
--   | rel R t => rel R (t.substBound ts)

-- def substBoundBound {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
--     (f : Fin n → Fin m) : L.DeltaZeroBoundedFormula m := φ.substBound (fun i ↦ &(f i))

end DeltaZeroBoundedFormula

namespace BoundedFormula

variable {n : ℕ}

section SyntacticalLevyHierarchy

def IsDeltaZero (φ : L.BoundedFormula' n) := ∃ ψ : L.DeltaZeroBoundedFormula n, φ = ψ

class DeltaZero (φ : L.BoundedFormula' n) where
  isDeltaZero : IsDeltaZero φ

instance (φ : L.DeltaZeroBoundedFormula n) : φ.toBoundedFormula.DeltaZero := ⟨φ, rfl⟩

mutual
/-- `φ : L.BoundedFormula' n` is said to be a `Π k` formula, denoted by `φ.IsPi k`,
if:
1. if `k = 0`, then `φ.IsDeltaZero`
2. if `k = k' + 1`, then `φ = all' m ψ` where `ψ : L.BoundedFormula' (n + m)` and `ψ.IsSigma k'`
-/
  inductive IsPi : ∀ {n : ℕ}, L.BoundedFormula' n → ℕ → Prop
    | zero {n : ℕ} {φ : L.BoundedFormula' n} (hφ : φ.IsDeltaZero) : φ.IsPi 0
    | succ (m : ℕ) {n k : ℕ} {φ : L.BoundedFormula' (n + m)} (hφ : φ.IsSigma k) :
      (φ.all' m).IsPi (k + 1)

/-- `φ : L.BoundedFormula' n` is said to be a `∑ k` formula, denoted by `φ.IsSigma k`,
if:
1. if `k = 0`, then `φ.IsDeltaZero`
2. if `k = k' + 1`, then `φ = ex' m ψ` where `ψ : L.BoundedFormula' (n + m)` and `ψ.IsPi k'`
-/
  inductive IsSigma : ∀ {n : ℕ}, L.BoundedFormula' n → ℕ → Prop
    | zero {n : ℕ} {φ : L.BoundedFormula' n} (hφ : φ.IsDeltaZero) : φ.IsSigma 0
    | succ (m : ℕ) {n k : ℕ} {φ : L.BoundedFormula' (n + m)} (hφ : φ.IsPi k) :
      (φ.ex' m).IsSigma (k + 1)
end

variable {k n m n' p l : ℕ} {φ ψ : L.BoundedFormula' n}

@[simp]
theorem isDeltaZero_falsum : (falsum : L.BoundedFormula' n).IsDeltaZero :=
  ⟨.falsum, rfl⟩

@[simp]
theorem isDeltaZero_equal (t₁ t₂ : L.Term' n) :
    (t₁ =' t₂).IsDeltaZero :=
  ⟨.equal t₁ t₂, rfl⟩

@[simp]
theorem isDeltaZero_mem (t₁ t₂ : L.Term' n) :
    (t₁ ∈' t₂).IsDeltaZero :=
  ⟨.mem t₁ t₂, rfl⟩

@[simp]
theorem isDeltaZero_rel (R : L.Relations 1) (t : L.Term' n) :
    (rel R ![t]).IsDeltaZero :=
  ⟨.rel R t, rfl⟩

@[simp]
theorem isDeltaZero_bot : (⊥ : L.BoundedFormula' n).IsDeltaZero := by
  simp [Bot.bot]

@[simp]
theorem IsDeltaZero.imp (hφ : φ.IsDeltaZero) (hψ : ψ.IsDeltaZero) :
    (φ ⟹ ψ : L.BoundedFormula' n).IsDeltaZero := by
  obtain ⟨φ', rfl⟩ := hφ
  obtain ⟨ψ', rfl⟩ := hψ
  exact ⟨.imp φ' ψ', by norm_cast⟩

@[simp]
theorem IsDeltaZero.allMem {φ : L.BoundedFormula' (n + 1)} (hφ : φ.IsDeltaZero)
    (t : L.Term' n) :
    (∀'∈ t φ).IsDeltaZero := by
  obtain ⟨φ', rfl⟩ := hφ
  exact ⟨DeltaZeroBoundedFormula.allMem t φ', by norm_cast⟩

@[simp]
theorem IsDeltaZero.not (h : φ.IsDeltaZero) : (∼φ).IsDeltaZero :=
  h.imp isDeltaZero_falsum

@[simp]
theorem isDeltaZero_top : (⊤ : L.BoundedFormula' n).IsDeltaZero := by
  simp [Top.top]

@[simp]
theorem IsDeltaZero.not_iff : (∼φ).IsDeltaZero ↔ φ.IsDeltaZero := by
  refine ⟨?_, IsDeltaZero.not⟩
  rintro ⟨(_ | _ | _ | ⟨φ₁, φ₂⟩ | _), h₁⟩
  · norm_cast at h₁
  · norm_cast at h₁
  · norm_cast at h₁
  · simp [BoundedFormula.not] at h₁
    exact ⟨φ₁, h₁.left⟩
  · norm_cast at h₁
  · norm_cast at h₁

theorem IsDeltaZero.sup (hφ : φ.IsDeltaZero) (hψ : ψ.IsDeltaZero) : (φ ⊔ ψ).IsDeltaZero :=
  hφ.not.imp hψ

theorem IsDeltaZero.foldr_sup {f : List (L.BoundedFormula' n)}
    (hf : ∀ φ ∈ f, φ.IsDeltaZero) :
    (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ f).IsDeltaZero := by
  induction f with
  | nil => simp
  | cons ψ f ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hf
    exact hf.left.sup (ih (hf.right))

theorem isDeltaZero_iSup [Finite β] {f : β → L.BoundedFormula' n} (hf : ∀ i, (f i).IsDeltaZero) :
    (iSup f).IsDeltaZero := by
  simp only [BoundedFormula.iSup]
  grind [IsDeltaZero.foldr_sup]

theorem IsDeltaZero.inf (hφ : φ.IsDeltaZero) (hψ : ψ.IsDeltaZero) : (φ ⊓ ψ).IsDeltaZero :=
  hφ.imp hψ.not |>.not

theorem IsDeltaZero.foldr_inf {f : List (L.BoundedFormula' n)}
    (hf : ∀ φ ∈ f, φ.IsDeltaZero) :
    (List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ f).IsDeltaZero := by
  induction f with
  | nil => simp
  | cons ψ f ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hf
    exact hf.left.inf (ih (hf.right))

theorem isDeltaZero_iInf [Finite β] {f : β → L.BoundedFormula' n} (hf : ∀ i, (f i).IsDeltaZero) :
    (iInf f).IsDeltaZero := by
  simp only [BoundedFormula.iInf]
  grind [IsDeltaZero.foldr_inf]

theorem IsDeltaZero.iff (hφ : φ.IsDeltaZero) (hψ : ψ.IsDeltaZero) : (φ ⇔ ψ).IsDeltaZero :=
  (hφ.imp hψ).inf (hψ.imp hφ)

@[simp]
theorem pi_zero_iff_deltaZero : φ.IsPi 0 ↔ φ.IsDeltaZero := by grind [IsPi]

@[simp]
theorem sigma_zero_iff_deltaZero : φ.IsSigma 0 ↔ φ.IsDeltaZero := by grind [IsSigma]

theorem IsPi.ex' {φ : L.BoundedFormula' (n + m)} (h : φ.IsPi k) :
    (φ.ex' m).IsSigma (k + 1) := IsSigma.succ m h

theorem IsPi.ex {φ : L.BoundedFormula' (n + 1)} (h : φ.IsPi k) :
    (∃' φ).IsSigma (k + 1) := IsSigma.succ 1 h

theorem IsPi.isSigma_succ (h : φ.IsPi k) : φ.IsSigma (k + 1) := IsSigma.succ 0 h

theorem IsSigma.all' {φ : L.BoundedFormula' (n + m)} (h : φ.IsSigma k) :
    (φ.all' m).IsPi (k + 1) := IsPi.succ m h

theorem IsSigma.all {φ : L.BoundedFormula' (n + 1)} (h : φ.IsSigma k) :
    (∀' φ).IsPi (k + 1) := IsPi.succ 1 h

theorem IsSigma.isPi_succ (h : φ.IsSigma k) : φ.IsPi (k + 1) := IsPi.succ 0 h

theorem IsPi.exists_Sigma_all' (h : φ.IsPi (k + 1)) :
    ∃ (m : ℕ), ∃ ψ : L.BoundedFormula' (n + m), ψ.IsSigma k ∧ φ = ψ.all' m := by
  cases h with | succ m hψ
  exact ⟨m, _, hψ, rfl⟩

theorem IsSigma.exists_Pi_ex' (h : φ.IsSigma (k + 1)) :
    ∃ (m : ℕ), ∃ ψ : L.BoundedFormula' (n + m), ψ.IsPi k ∧ φ = ψ.ex' m := by
  cases h with | succ m hψ
  exact ⟨m, _, hψ, rfl⟩

/-- If `φ` is `DeltaZero`, then `φ.substBound ts` is `DeltaZero` -/
theorem IsDeltaZero.substBound (h : φ.IsDeltaZero) (ts : Fin n → L.Term' m) :
    (φ.substBound ts).IsDeltaZero := by
  obtain ⟨φ', rfl⟩ := h
  use φ'.substBound ts
  norm_cast

/-- If `φ` is `DeltaZero`, then `φ.substBoundBound f` is `DeltaZero` -/
theorem IsDeltaZero.substBoundBound (h : φ.IsDeltaZero) (f : Fin n → Fin m) :
    (φ.substBoundBound f).IsDeltaZero :=
  h.substBound _

/-- If `φ` is `DeltaZero`, then `φ.cast h` is `DeltaZero` -/
theorem IsDeltaZero.cast (h : φ.IsDeltaZero) (hnm : n = m) :
    (φ.cast hnm).IsDeltaZero :=
  h.substBoundBound _

mutual
theorem IsPi.substBound {k n l : ℕ} {φ : L.BoundedFormula' n} (h : φ.IsPi k)
    (ts : Fin n → L.Term' l) :
    (φ.substBound ts).IsPi k :=
  match k with
  | 0 => by
    simp only [pi_zero_iff_deltaZero] at h ⊢
    exact h.substBound _
  | k + 1 => by
    obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Sigma_all'
    simp only [hψ₂, substBound_all'_eq_all'_substBound]
    exact hψ₁.substBound _ |>.all'

theorem IsSigma.substBound {k n l : ℕ} {φ : L.BoundedFormula' n} (h : φ.IsSigma k)
    (ts : Fin n → L.Term' l) :
    (φ.substBound ts).IsSigma k :=
  match k with
  | 0 => by
    simp only [sigma_zero_iff_deltaZero] at h ⊢
    exact h.substBound _
  | k + 1 => by
    obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Pi_ex'
    simp only [hψ₂, substBound_ex'_eq_ex'_substBound]
    exact hψ₁.substBound _ |>.ex'
end

theorem IsPi.all' {φ : L.BoundedFormula' (n + m)} (h : φ.IsPi (k + 1)) :
    (φ.all' m).IsPi (k + 1) := by
  obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Sigma_all'
  rw [hψ₂, ψ.all'_all'_eq_all'_cast]
  exact (hψ₁.substBound _).all'

theorem IsPi.all {φ : L.BoundedFormula' (n + 1)} (h : φ.IsPi (k + 1)) :
    φ.all.IsPi (k + 1) := h.all'

theorem IsSigma.ex' {φ : L.BoundedFormula' (n + m)} (h : φ.IsSigma (k + 1)) :
    (φ.ex' m).IsSigma (k + 1) := by
  obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Pi_ex'
  rw [hψ₂, ψ.ex'_ex'_eq_ex'_cast]
  exact (hψ₁.substBound _).ex'

theorem IsSigma.ex {φ : L.BoundedFormula' (n + 1)} (h : φ.IsSigma (k + 1)) :
    φ.ex.IsSigma (k + 1) := h.ex'

mutual
theorem IsPi.isPi_succ {k n : ℕ} {φ : L.BoundedFormula' n} (h : φ.IsPi k) :
    φ.IsPi (k + 1) :=
  match k with
  | 0 => IsSigma.isPi_succ (by simpa using h)
  | k + 1 => by
    obtain ⟨_, _, hψ, _⟩ := h.exists_Sigma_all'
    convert hψ.isSigma_succ.all'

theorem IsSigma.isSigma_succ {k n : ℕ} {φ : L.BoundedFormula' n} (h : φ.IsSigma k) :
    φ.IsSigma (k + 1) :=
  match k with
  | 0 => IsPi.isSigma_succ (by simpa using h)
  | k + 1 => by
    obtain ⟨_, _, hψ, _⟩ := h.exists_Pi_ex'
    convert hψ.isPi_succ.ex'
end

variable {φ : L.BoundedFormula' n} {ts : Fin n → L.Term' m}

theorem IsPi.isPi_of_le (h : φ.IsPi k) (hkm : k ≤ m) : φ.IsPi m := by
  induction m with
  | zero => grind
  | succ m ih =>
    rcases lt_or_eq_of_le hkm with hkm | rfl
    · exact ih (Nat.le_of_lt_succ hkm) |>.isPi_succ
    · exact h

theorem IsSigma.isSigma_of_le (h : φ.IsSigma k) (hkm : k ≤ m) : φ.IsSigma m := by
  induction m with
  | zero => convert h; omega
  | succ m ih =>
    rcases lt_or_eq_of_le hkm with hkm | rfl
    · exact ih (Nat.le_of_lt_succ hkm) |>.isSigma_succ
    · exact h

theorem IsPi.Sigma_of_lt (h : φ.IsPi k) (hkm : k < m) : φ.IsSigma m :=
  h.isSigma_succ.isSigma_of_le (Nat.add_one_le_of_lt hkm)

theorem IsSigma.Pi_of_lt (h : φ.IsSigma k) (hkm : k < m) : φ.IsPi m :=
  h.isPi_succ.isPi_of_le (Nat.add_one_le_of_lt hkm)


instance : (⊥ : L.BoundedFormula' n).DeltaZero := ⟨isDeltaZero_falsum⟩

instance (t₁ t₂ : L.Term' n) : (t₁ =' t₂).DeltaZero := ⟨isDeltaZero_equal _ _⟩

instance (t₁ t₂ : L.Term' n) :
  (t₁ ∈' t₂).DeltaZero := ⟨isDeltaZero_mem _ _⟩

instance [hφ : φ.DeltaZero] [hψ : ψ.DeltaZero] : (φ ⟹ ψ).DeltaZero :=
  ⟨hφ.isDeltaZero.imp hψ.isDeltaZero⟩

instance {φ : L.BoundedFormula' (n + 1)} [hφ : φ.DeltaZero]
  (t : L.Term' n) : (∀'∈ t φ).DeltaZero :=
  ⟨hφ.isDeltaZero.allMem t⟩

instance (R : L.Relations 1)
  (t : L.Term' n) :
  (R.boundedFormula₁ t).DeltaZero := ⟨isDeltaZero_rel _ _⟩

instance [hφ : φ.DeltaZero] : (∼φ).DeltaZero := ⟨hφ.isDeltaZero.not⟩

instance : (⊤ : L.BoundedFormula' n).DeltaZero := ⟨DeltaZero.isDeltaZero.not⟩

instance [hφ : φ.DeltaZero] [hψ : ψ.DeltaZero] : (φ ⊔ ψ).DeltaZero :=
  ⟨hφ.isDeltaZero.not.imp hψ.isDeltaZero⟩

instance [Finite β] {f : β → L.BoundedFormula' n} [hf : ∀ i, (f i).DeltaZero] :
    (iSup f).DeltaZero :=
  ⟨isDeltaZero_iSup (fun i ↦ (hf i).isDeltaZero)⟩

instance [hφ : φ.DeltaZero] [hψ : ψ.DeltaZero] : (φ ⊓ ψ).DeltaZero :=
  ⟨hφ.isDeltaZero.imp hψ.isDeltaZero.not |>.not⟩

instance [Finite β] {f : β → L.BoundedFormula' n} [hf : ∀ i, (f i).DeltaZero] :
    (iInf f).DeltaZero :=
  ⟨isDeltaZero_iInf (fun i ↦ (hf i).isDeltaZero)⟩

instance [hφ : φ.DeltaZero] [hψ : ψ.DeltaZero] : (φ ⇔ ψ).DeltaZero :=
  ⟨(hφ.isDeltaZero.imp hψ.isDeltaZero).inf (hψ.isDeltaZero.imp hφ.isDeltaZero)⟩

instance {φ : L.BoundedFormula' (n + 1)} [hφ : φ.DeltaZero]
  (t : L.Term' n) : (∃'∈ t φ).DeltaZero := ⟨(hφ.isDeltaZero.not.allMem t).not⟩

class Pi (k : ℕ) (φ : L.BoundedFormula' n) : Prop where
  isPi : φ.IsPi k

class Sigma (k : ℕ) (φ : L.BoundedFormula' n) : Prop where
  isSigma : φ.IsSigma k

instance [hφ : φ.DeltaZero] : φ.Pi 0 := ⟨by simpa using hφ.isDeltaZero⟩

instance [hφ : φ.DeltaZero] : φ.Sigma 0 := ⟨by simpa using hφ.isDeltaZero⟩

instance {φ : L.BoundedFormula' (n + m)} [hφ : φ.Pi k] :
  (φ.ex' m).Sigma (k + 1) := ⟨by simpa using hφ.isPi.ex'⟩

instance {φ : L.BoundedFormula' (n + 1)} [hφ : φ.Pi k] :
  φ.ex.Sigma (k + 1) := ⟨by simpa using hφ.isPi.ex⟩

instance {φ : L.BoundedFormula' (n + 1)} [hφ : φ.Pi k] :
  φ.Sigma (k + 1) := ⟨by simpa using hφ.isPi.isSigma_succ⟩

instance {φ : L.BoundedFormula' (n + m)} [hφ : φ.Sigma k] :
  (φ.all' m).Pi (k + 1) := ⟨by simpa using hφ.isSigma.all'⟩

instance {φ : L.BoundedFormula' (n + 1)} [hφ : φ.Sigma k] :
  φ.all.Pi (k + 1) := ⟨by simpa using hφ.isSigma.all⟩

instance {φ : L.BoundedFormula' (n + 1)} [hφ : φ.Sigma k] :
  φ.Pi (k + 1) := ⟨by simpa using hφ.isSigma.isPi_succ⟩

-- instance [h : φ.DeltaZero] (h' : n = n') : (φ.cast h').DeltaZero := ⟨h.isDeltaZero.cast h'⟩

instance {φ : L.BoundedFormula' n} [h : φ.DeltaZero] :
  (φ.substBound ts).DeltaZero := ⟨h.isDeltaZero.substBound ts⟩

instance {φ : L.BoundedFormula' n} [h : φ.DeltaZero] :
  (φ.substBoundBound f).DeltaZero := ⟨h.isDeltaZero.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.DeltaZero] (h' : n = n') :
  (φ.cast h').DeltaZero := ⟨h.isDeltaZero.substBound _⟩

instance {φ : L.BoundedFormula' (n + p)} {ψ : L.BoundedFormula' (n + q)} [hφ : φ.DeltaZero]
  [hψ : ψ.DeltaZero] : (φ.splitImp ψ).DeltaZero := ⟨
  (hφ.isDeltaZero.substBound _).imp (hψ.isDeltaZero.substBound _)⟩

instance {φ : L.BoundedFormula' (n + p)} [hφ : φ.DeltaZero] : (φ.switchBound).DeltaZero :=
  ⟨hφ.isDeltaZero.substBound _⟩

instance {φ : L.BoundedFormula' (n + p + q)} [hφ : φ.DeltaZero] : (φ.castAssoc).DeltaZero :=
  ⟨hφ.isDeltaZero.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.DeltaZero] : (φ.castAssoc').DeltaZero :=
  ⟨hφ.isDeltaZero.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.DeltaZero] :
  (φ.switchBoundRight).DeltaZero :=
  ⟨hφ.isDeltaZero.substBound _⟩

instance {φ : L.BoundedFormula' (p + n)} {ψ : L.BoundedFormula' (q + n)} [hφ : φ.DeltaZero]
  [hψ : ψ.DeltaZero] : (φ.splitImp' ψ).DeltaZero := by rw [splitImp']; infer_instance

instance {φ : L.BoundedFormula' n} [h : φ.Pi k] :
    (φ.substBound ts).Pi k := ⟨h.isPi.substBound ts⟩

instance {φ : L.BoundedFormula' n} [h : φ.Pi k] :
  (φ.substBoundBound f).Pi k := ⟨h.isPi.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.Pi k] (h' : n = n') :
  (φ.cast h').Pi k := ⟨h.isPi.substBound _⟩

-- instance {φ : L.BoundedFormula' (n + p)} {ψ : L.BoundedFormula' (n + q)} [hφ : φ.Sigma k]
--   [hψ : ψ.Pi k] : (φ.splitImp ψ).Pi k := ⟨
--   (hφ.isSigma.substBound _).imp (hψ.isPi.substBound _)⟩

instance {φ : L.BoundedFormula' (n + p)} [hφ : φ.Pi k] : (φ.switchBound).Pi k :=
  ⟨hφ.isPi.substBound _⟩

instance {φ : L.BoundedFormula' (n + p + q)} [hφ : φ.Pi k] : (φ.castAssoc).Pi k :=
  ⟨hφ.isPi.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.Pi k] : (φ.castAssoc').Pi k :=
  ⟨hφ.isPi.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.Pi k] :
  (φ.switchBoundRight).Pi k :=
  ⟨hφ.isPi.substBound _⟩

-- instance {φ : L.BoundedFormula' (p + n)} {ψ : L.BoundedFormula' (q + n)} [hφ : φ.Pi k]
--   [hψ : ψ.Pi k] : (φ.splitImp' ψ).Pi k := by rw [splitImp']; infer_instance

instance {φ : L.BoundedFormula' n} [h : φ.Sigma k] :
    (φ.substBound ts).Sigma k := ⟨h.isSigma.substBound ts⟩

instance {φ : L.BoundedFormula' n} [h : φ.Sigma k] :
  (φ.substBoundBound f).Sigma k := ⟨h.isSigma.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.Sigma k] (h' : n = n') :
  (φ.cast h').Sigma k := ⟨h.isSigma.substBound _⟩

-- instance {φ : L.BoundedFormula' (n + p)} {ψ : L.BoundedFormula' (n + q)} [hφ : φ.Sigma k]
--   [hψ : ψ.Sigma k] : (φ.splitImp ψ).Sigma k := ⟨
--   (hφ.isSigma.substBound _).imp (hψ.isSigma.substBound _)⟩

instance {φ : L.BoundedFormula' (n + p)} [hφ : φ.Sigma k] : (φ.switchBound).Sigma k :=
  ⟨hφ.isSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + p + q)} [hφ : φ.Sigma k] : (φ.castAssoc).Sigma k :=
  ⟨hφ.isSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.Sigma k] : (φ.castAssoc').Sigma k :=
  ⟨hφ.isSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.Sigma k] :
  (φ.switchBoundRight).Sigma k :=
  ⟨hφ.isSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + m)} [h : φ.Pi (k + 1)] :
  (φ.all' m).Pi (k + 1) := ⟨h.isPi.all'⟩

instance {φ : L.BoundedFormula' (n + 1)} [h : φ.Pi (k + 1)] :
  φ.all.Pi (k + 1) := ⟨h.isPi.all⟩

instance {φ : L.BoundedFormula' (n + m)} [h : φ.Sigma (k + 1)] :
  (φ.ex' m).Sigma (k + 1) := ⟨h.isSigma.ex'⟩

instance {φ : L.BoundedFormula' (n + 1)} [h : φ.Sigma (k + 1)] :
  φ.ex.Sigma (k + 1) := ⟨h.isSigma.ex⟩

instance {φ : L.BoundedFormula' n} [h : φ.Pi k] :
  φ.Pi (k + 1) := ⟨h.isPi.isPi_succ⟩

instance {φ : L.BoundedFormula' n} [h : φ.Sigma k] :
  φ.Sigma (k + 1) := ⟨h.isSigma.isSigma_succ⟩

instance [hφ : φ.DeltaZero] : φ.Pi k :=
  ⟨IsPi.isPi_of_le (by simpa using hφ.isDeltaZero) (Nat.zero_le k) ⟩

instance [hφ : φ.DeltaZero] : φ.Sigma k :=
  ⟨IsSigma.isSigma_of_le (by simpa using hφ.isDeltaZero) (Nat.zero_le k) ⟩

end SyntacticalLevyHierarchy


section LogicalLevyHierarchy

variable {k n : ℕ} {φ ψ : L.BoundedFormula' n}

/-- `φ` is `T`-logically `Π n` means that `φ` is `T`-equivalent to a `Π n` formula -/
def IsLogicalPi (k : ℕ) (φ : L.BoundedFormula' n) (T : L.Theory) : Prop :=
  ∃ ψ : L.BoundedFormula' n, (ψ.IsPi k ∧ T ⊨ᵇ φ ⇔ ψ)

/-- `φ` is `T`-logically `Σ n` means that `φ` is `T`-equivalent to a `Σ n` formula -/
def IsLogicalSigma (k : ℕ) (φ : L.BoundedFormula' n) (T : L.Theory) : Prop :=
  ∃ ψ : L.BoundedFormula' n, (ψ.IsSigma k ∧ T ⊨ᵇ φ ⇔ ψ)

-- /-- `φ` is `T`-logically `Δ n` means that `φ` is `T`-logically `Π n` and `T`-logically `Σ n` -/
-- def IsLogicalDelta (k : ℕ) (φ : L.BoundedFormula' n) (T : L.Theory) : Prop :=
--   φ.IsLogicalPi k T ∧ φ.IsLogicalSigma k T

variable {T : L.Theory}

theorem IsPi.isLogicalPi (h : φ.IsPi k) : φ.IsLogicalPi k T :=
  ⟨φ, h, by simp [ModelsBoundedFormula]⟩

theorem IsSigma.isLogicalSigma (h : φ.IsSigma k) : φ.IsLogicalSigma k T :=
  ⟨φ, h, by simp [ModelsBoundedFormula]⟩

theorem IsDeltaZero.isLogicalPi (h : φ.IsDeltaZero) : φ.IsLogicalPi 0 T :=
  IsPi.isLogicalPi (by simpa)

theorem IsDeltaZero.isLogicalSigma (h : φ.IsDeltaZero) : φ.IsLogicalSigma 0 T :=
  IsSigma.isLogicalSigma (by simpa)

theorem isLogicalSigma_zero_iff_isLogicalPi_zero :
    φ.IsLogicalSigma 0 T ↔ φ.IsLogicalPi 0 T :=
  ⟨fun ⟨ψ, hψ⟩ ↦ ⟨ψ, by simpa using hψ⟩, fun ⟨ψ, hψ⟩ ↦ ⟨ψ, by simpa using hψ⟩⟩

-- theorem IsLogicalDelta.isLogicalPi (h : φ.IsLogicalDelta k T) : φ.IsLogicalPi k T := h.left

-- theorem IsLogicalDelta.isLogicalSigma (h : φ.IsLogicalDelta k T) : φ.IsLogicalSigma k T := h.right

/- logical quantifiers -/

variable {m : ℕ} {φ : L.BoundedFormula' (n + m)}

theorem IsLogicalPi.all' (h : φ.IsLogicalPi (k + 1) T) : (φ.all' m).IsLogicalPi (k + 1) T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ.all' m, hψ₁.all'
  simp only [ModelsBoundedFormula.iff_iff]
  constructor <;> exact hψ₂.all'.of_imp (by simp +contextual [ModelsBoundedFormula])

theorem IsLogicalPi.all'₀ (h : φ.IsLogicalPi k T) (hk : k ≠ 0) : (φ.all' m).IsLogicalPi k T := by
  rw [show k = k - 1 + 1 by omega] at h ⊢
  exact h.all'

theorem IsLogicalPi.ex' (h : φ.IsLogicalPi k T) :  (φ.ex' m).IsLogicalSigma (k + 1) T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ.ex' m, hψ₁.ex'
  simp only [ModelsBoundedFormula.iff_iff]
  constructor <;> exact hψ₂.all'.of_imp (by simp +contextual [ModelsBoundedFormula])

theorem IsLogicalSigma.ex' (h : φ.IsLogicalSigma (k + 1) T) :
    (φ.ex' m).IsLogicalSigma (k + 1) T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ.ex' m, hψ₁.ex'
  simp only [ModelsBoundedFormula.iff_iff]
  constructor <;> exact hψ₂.all'.of_imp (by simp +contextual [ModelsBoundedFormula])

theorem IsLogicalSigma.ex'₀ (h : φ.IsLogicalSigma k T) (hk : k ≠ 0) :
    (φ.ex' m).IsLogicalSigma k T := by
  rw [show k = k - 1 + 1 by omega] at h ⊢
  exact h.ex'

theorem IsLogicalSigma.all' (h : φ.IsLogicalSigma k T) :  (φ.all' m).IsLogicalPi (k + 1) T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ.all' m, hψ₁.all'
  simp only [ModelsBoundedFormula.iff_iff]
  constructor <;> exact hψ₂.all'.of_imp (by simp +contextual [ModelsBoundedFormula])

-- theorem IsLogicalDelta.all' (h : φ.IsLogicalDelta (k + 1) T) : (φ.all' m).IsLogicalPi (k + 1) T :=
--   h.left.all'

-- theorem IsLogicalDelta.all'₀ (h : φ.IsLogicalDelta k T) (hk : k ≠ 0) :
--     (φ.all' m).IsLogicalPi k T :=
--   h.left.all'₀ hk

-- theorem IsLogicalDelta.ex' (h : φ.IsLogicalDelta (k + 1) T) : (φ.ex' m).IsLogicalSigma (k + 1) T :=
--   h.right.ex'

-- theorem IsLogicalDelta.ex'₀ (h : φ.IsLogicalDelta k T) (hk : k ≠ 0) :
--     (φ.ex' m).IsLogicalSigma k T :=
--   h.right.ex'₀ hk


/- invariance under `T`-logical equivalence -/

variable {φ ψ : L.BoundedFormula' n}

theorem IsLogicalPi.of_models_iff (h : φ.IsLogicalPi k T) (h' : T ⊨ᵇ φ ⇔ ψ) :
    ψ.IsLogicalPi k T := by
  obtain ⟨θ, hθ₁, hθ₂⟩ := h
  exact ⟨θ, hθ₁, h'.of_imp_imp hθ₂ (by simp +contextual [ModelsBoundedFormula])⟩

theorem IsLogicalSigma.of_models_iff (h : φ.IsLogicalSigma k T) (h' : T ⊨ᵇ φ ⇔ ψ) :
    ψ.IsLogicalSigma k T := by
  obtain ⟨θ, hθ₁, hθ₂⟩ := h
  exact ⟨θ, hθ₁, h'.of_imp_imp hθ₂ (by simp +contextual [ModelsBoundedFormula])⟩

-- theorem IsLogicalDelta.of_models_iff (h : φ.IsLogicalDelta k T) (h' : T ⊨ᵇ φ ⇔ ψ) :
--     ψ.IsLogicalDelta k T :=
--   ⟨h.left.of_models_iff h', h.right.of_models_iff h'⟩

/- logical connectives -/

mutual
theorem IsLogicalPi.not {k n : ℕ} {φ : L.BoundedFormula' n} (h : φ.IsLogicalPi k T) :
    (∼φ).IsLogicalSigma k T :=
  let ⟨ψ, hψ₁, hψ₂⟩ := h
  match k with
  | 0 => ⟨∼ψ, by simpa using hψ₁, hψ₂.of_imp (by simp +contextual [ModelsBoundedFormula])⟩
  | k + 1 => let ⟨m, θ, hθ₁, hθ₂⟩ := hψ₁.exists_Sigma_all'
    hθ₁.isLogicalSigma.not.ex'.of_models_iff <|
      (hθ₂ ▸ hψ₂).of_imp (by simp +contextual [ModelsBoundedFormula])

theorem IsLogicalSigma.not {k n : ℕ} {φ : L.BoundedFormula' n} (h : φ.IsLogicalSigma k T) :
    (∼φ).IsLogicalPi k T :=
  let ⟨ψ, hψ₁, hψ₂⟩ := h
  match k with
  | 0 => ⟨∼ψ, by simpa using hψ₁, hψ₂.of_imp (by simp +contextual [ModelsBoundedFormula])⟩
  | k + 1 => let ⟨m, θ, hθ₁, hθ₂⟩ := hψ₁.exists_Pi_ex'
    hθ₁.isLogicalPi.not.all'.of_models_iff <|
      (hθ₂ ▸ hψ₂).of_imp (by simp +contextual [ModelsBoundedFormula])
end

-- theorem IsLogicalDelta.not (h : φ.IsLogicalDelta k T) : (∼φ).IsLogicalDelta k T :=
--   ⟨h.right.not, h.left.not⟩

@[simp]
theorem LogicalPi_not_iff : (∼φ).IsLogicalPi k T ↔ φ.IsLogicalSigma k T := by
  refine ⟨fun h ↦ h.not.of_models_iff ?_, IsLogicalSigma.not⟩
  simp +contextual [ModelsBoundedFormula]

@[simp]
theorem LogicalSigma_not_iff : (∼φ).IsLogicalSigma k T ↔ φ.IsLogicalPi k T := by
  refine ⟨fun h ↦ h.not.of_models_iff ?_, IsLogicalPi.not⟩
  simp +contextual [ModelsBoundedFormula]

-- @[simp]
-- theorem LogicalDelta_not_iff : (∼φ).IsLogicalDelta k T ↔ φ.IsLogicalDelta k T := by
--   refine ⟨fun h ↦ h.not.of_models_iff ?_, IsLogicalDelta.not⟩
--   simp +contextual [ModelsBoundedFormula]

mutual
theorem IsLogicalPi.imp {k n : ℕ} {φ ψ : L.BoundedFormula' n}
    (hφ : φ.IsLogicalPi k T) (hψ : ψ.IsLogicalSigma k T) : (φ ⟹ ψ).IsLogicalSigma k T :=
  let ⟨φ', hφ₁, hφ₂⟩ := hφ
  let ⟨ψ', hψ₁, hψ₂⟩ := hψ
  match k with
  | 0 => by
    refine ⟨φ' ⟹ ψ', ?_, ?_⟩
    · simp only [pi_zero_iff_deltaZero, sigma_zero_iff_deltaZero] at hφ₁ hψ₁ ⊢
      exact hφ₁.imp hψ₁
    · exact hφ₂.of_imp_imp hψ₂ (by simp +contextual [ModelsBoundedFormula])
  | k + 1 => by
    obtain ⟨p, φ'', hφ''₁, hφ''₂⟩ := hφ₁.exists_Sigma_all'
    obtain ⟨q, ψ'', hψ''₁, hψ''₂⟩ := hψ₁.exists_Pi_ex'
    have : (φ''.splitImp ψ'').ex'.ex'.IsLogicalSigma (k + 1) T :=
      (hφ''₁.substBound _).isLogicalSigma.imp (hψ''₁.substBound _).isLogicalPi |>.ex'.ex'
    refine this.of_models_iff (fun M v xs ↦ ?_)
    specialize hφ₂ M v xs
    specialize hψ₂ M v xs
    simp only [realize_iff] at hφ₂ hψ₂
    simp only [realize_iff, realize_ex', realize_splitImp, realize_imp, hφ₂, hφ''₂, realize_all',
      hψ₂, hψ''₂]
    refine ⟨by grind, fun h₁ ↦ ?_⟩
    by_cases h₂ : ∀ ys, φ''.Realize v (append xs ys)
    · obtain ⟨zs, hzs⟩ := h₁ h₂
      exact ⟨default, zs, by grind⟩
    · simp only [not_forall] at h₂
      obtain ⟨ys, hys⟩ := h₂
      exact ⟨ys, default, by grind⟩

theorem IsLogicalSigma.imp {k n : ℕ} {φ ψ : L.BoundedFormula' n}
    (hφ : φ.IsLogicalSigma k T) (hψ : ψ.IsLogicalPi k T) : (φ ⟹ ψ).IsLogicalPi k T :=
  let ⟨φ', hφ₁, hφ₂⟩ := hφ
  let ⟨ψ', hψ₁, hψ₂⟩ := hψ
  match k with
  | 0 => by
    refine ⟨φ' ⟹ ψ', ?_, ?_⟩
    · simp only [sigma_zero_iff_deltaZero, pi_zero_iff_deltaZero] at hφ₁ hψ₁ ⊢
      exact hφ₁.imp hψ₁
    · exact hφ₂.of_imp_imp hψ₂ (by simp +contextual [ModelsBoundedFormula])
  | k + 1 => by
    obtain ⟨p, φ'', hφ''₁, hφ''₂⟩ := hφ₁.exists_Pi_ex'
    obtain ⟨q, ψ'', hψ''₁, hψ''₂⟩ := hψ₁.exists_Sigma_all'
    have : (φ''.splitImp ψ'').all'.all'.IsLogicalPi (k + 1) T :=
      (hφ''₁.substBound _).isLogicalPi.imp (hψ''₁.substBound _).isLogicalSigma |>.all'.all'
    refine this.of_models_iff (fun M v xs ↦ ?_)
    specialize hφ₂ M v xs
    specialize hψ₂ M v xs
    simp only [realize_iff] at hφ₂ hψ₂
    simp only [realize_iff, realize_all', realize_splitImp, realize_imp, hφ₂, hφ''₂, realize_ex',
      hψ₂, hψ''₂, forall_exists_index]
    tauto
end

-- theorem IsLogicalDelta.imp {φ ψ : L.BoundedFormula' n}
--     (hφ : φ.IsLogicalDelta k T) (hψ : ψ.IsLogicalDelta k T) : (φ ⟹ ψ).IsLogicalDelta k T :=
--   ⟨hφ.right.imp hψ.left, hφ.left.imp hψ.right⟩

theorem IsLogicalPi.sup (hφ : φ.IsLogicalPi k T) (hψ : ψ.IsLogicalPi k T) :
    (φ ⊔ ψ).IsLogicalPi k T := hφ.not.imp hψ

theorem IsLogicalPi.inf (hφ : φ.IsLogicalPi k T) (hψ : ψ.IsLogicalPi k T) :
    (φ ⊓ ψ).IsLogicalPi k T := hφ.imp hψ.not |>.not

theorem IsLogicalSigma.sup (hφ : φ.IsLogicalSigma k T) (hψ : ψ.IsLogicalSigma k T) :
    (φ ⊔ ψ).IsLogicalSigma k T := hφ.not.imp hψ

theorem IsLogicalSigma.inf (hφ : φ.IsLogicalSigma k T) (hψ : ψ.IsLogicalSigma k T) :
    (φ ⊓ ψ).IsLogicalSigma k T := hφ.imp hψ.not |>.not

-- theorem IsLogicalDelta.sup (hφ : φ.IsLogicalDelta k T) (hψ : ψ.IsLogicalDelta k T) :
--     (φ ⊔ ψ).IsLogicalDelta k T := hφ.not.imp hψ

-- theorem IsLogicalDelta.inf (hφ : φ.IsLogicalDelta k T) (hψ : ψ.IsLogicalDelta k T) :
--     (φ ⊓ ψ).IsLogicalDelta k T := hφ.imp hψ.not |>.not

-- theorem IsLogicalDelta.iff (hφ : φ.IsLogicalDelta k T) (hψ : ψ.IsLogicalDelta k T) :
--     (φ ⇔ ψ).IsLogicalDelta k T := (hφ.imp hψ).inf (hψ.imp hφ)

/-- substBound -/
theorem IsLogicalPi.substBound {φ : L.BoundedFormula' n} (ts : Fin n → L.Term' m)
    (hφ : φ.IsLogicalPi k T) : (φ.substBound ts).IsLogicalPi k T := by
  obtain ⟨φ', hφ₁, hφ₂⟩ := hφ
  refine ⟨φ'.substBound ts, hφ₁.substBound _, fun M v xs ↦ ?_⟩
  simpa [realize_iff, realize_substBound] using hφ₂ M v fun i ↦ ((ts i).realize (Sum.elim v xs))

theorem IsLogicalSigma.substBound {φ : L.BoundedFormula' n} (ts : Fin n → L.Term' m)
    (hφ : φ.IsLogicalSigma k T) : (φ.substBound ts).IsLogicalSigma k T := by
  obtain ⟨φ', hφ₁, hφ₂⟩ := hφ
  refine ⟨φ'.substBound ts, hφ₁.substBound _, fun M v xs ↦ ?_⟩
  simpa [realize_iff, realize_substBound] using hφ₂ M v fun i ↦ ((ts i).realize (Sum.elim v xs))

-- theorem IsLogicalDelta.substBound {φ : L.BoundedFormula' n} (ts : Fin n → L.Term' m)
--     (hφ : φ.IsLogicalDelta k T) : (φ.substBound ts).IsLogicalDelta k T :=
--   ⟨hφ.left.substBound _, hφ.right.substBound _⟩

/- lower levels are included in upper levels -/

theorem IsLogicalPi.isLogicalPi_of_le (h : φ.IsLogicalPi k T) (hkm : k ≤ m) :
    φ.IsLogicalPi m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.isPi_of_le hkm

theorem IsLogicalSigma.isLogicalSigma_of_le (h : φ.IsLogicalSigma k T) (hkm : k ≤ m) :
    φ.IsLogicalSigma m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.isSigma_of_le hkm

-- theorem IsLogicalDelta.isLogicalDelta_of_le (h : φ.IsLogicalDelta k T) (hkm : k ≤ m) :
--     φ.IsLogicalDelta m T :=
--   ⟨h.left.isLogicalPi_of_le hkm, h.right.isLogicalSigma_of_le hkm⟩

theorem IsLogicalPi.isLogicalSigma_of_lt (h : φ.IsLogicalPi k T) (hkm : k < m) :
    φ.IsLogicalSigma m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.Sigma_of_lt hkm

theorem IsLogicalSigma.isLogicalPi_of_lt (h : φ.IsLogicalSigma k T) (hkm : k < m) :
    φ.IsLogicalPi m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.Pi_of_lt hkm

-- theorem IsLogicalPi.isLogicalDelta_of_lt (h : φ.IsLogicalPi k T) (hkm : k < m) :
--     φ.IsLogicalDelta m T :=
--   ⟨h.isLogicalPi_of_le hkm.le, h.isLogicalSigma_of_lt hkm⟩

-- theorem IsLogicalSigma.isLogicalDelta_of_lt (h : φ.IsLogicalSigma k T) (hkm : k < m) :
--     φ.IsLogicalDelta m T :=
--   ⟨h.isLogicalPi_of_lt hkm, h.isLogicalSigma_of_le hkm.le⟩

theorem IsLogicalPi.foldr_sup {f : List (L.BoundedFormula' n)}
    (hf : ∀ φ ∈ f, φ.IsLogicalPi k T) :
    (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ f).IsLogicalPi k T := by
  induction f with
  | nil => exact isDeltaZero_bot.isLogicalPi.isLogicalPi_of_le (by omega)
  | cons ψ f ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hf
    exact hf.left.sup (ih (hf.right))

theorem isLogicalPi_iSup [Finite β] {f : β → L.BoundedFormula' n}
    (hf : ∀ i, (f i).IsLogicalPi k T) :
    (iSup f).IsLogicalPi k T := by
  simp only [BoundedFormula.iSup]
  grind [IsLogicalPi.foldr_sup]

theorem IsLogicalPi.foldr_inf {f : List (L.BoundedFormula' n)}
    (hf : ∀ φ ∈ f, φ.IsLogicalPi k T) :
    (List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ f).IsLogicalPi k T := by
  induction f with
  | nil => exact isDeltaZero_top.isLogicalPi.isLogicalPi_of_le (by omega)
  | cons ψ f ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hf
    exact hf.left.inf (ih (hf.right))

theorem isLogicalPi_iInf [Finite β] {f : β → L.BoundedFormula' n}
    (hf : ∀ i, (f i).IsLogicalPi k T) :
    (iInf f).IsLogicalPi k T := by
  simp only [BoundedFormula.iInf]
  grind [IsLogicalPi.foldr_inf]

theorem IsLogicalSigma.foldr_sup {f : List (L.BoundedFormula' n)}
    (hf : ∀ φ ∈ f, φ.IsLogicalSigma k T) :
    (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ f).IsLogicalSigma k T := by
  induction f with
  | nil => exact isDeltaZero_bot.isLogicalSigma.isLogicalSigma_of_le (by omega)
  | cons ψ f ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hf
    exact hf.left.sup (ih (hf.right))

theorem isLogicalSigma_iSup [Finite β] {f : β → L.BoundedFormula' n}
    (hf : ∀ i, (f i).IsLogicalSigma k T) :
    (iSup f).IsLogicalSigma k T := by
  simp only [BoundedFormula.iSup]
  grind [IsLogicalSigma.foldr_sup]

theorem IsLogicalSigma.foldr_inf {f : List (L.BoundedFormula' n)}
    (hf : ∀ φ ∈ f, φ.IsLogicalSigma k T) :
    (List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ f).IsLogicalSigma k T := by
  induction f with
  | nil => exact isDeltaZero_top.isLogicalSigma.isLogicalSigma_of_le (by omega)
  | cons ψ f ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hf
    exact hf.left.inf (ih (hf.right))

theorem isLogicalSigma_iInf [Finite β] {f : β → L.BoundedFormula' n}
    (hf : ∀ i, (f i).IsLogicalSigma k T) :
    (iInf f).IsLogicalSigma k T := by
  simp only [BoundedFormula.iInf]
  grind [IsLogicalSigma.foldr_inf]

/- monotone in the theory -/

variable {T' : L.Theory}

theorem IsLogicalPi.mono (h : φ.IsLogicalPi k T) (h' : T ⊆ T') : φ.IsLogicalPi k T' := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  exact ⟨ψ, hψ₁, hψ₂.mono h'⟩

theorem IsLogicalSigma.mono (h : φ.IsLogicalSigma k T) (h' : T ⊆ T') : φ.IsLogicalSigma k T' := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  exact ⟨ψ, hψ₁, hψ₂.mono h'⟩

-- theorem IsLogicalDelta.mono (h : φ.IsLogicalDelta k T) (h' : T ⊆ T') : φ.IsLogicalDelta k T' := by
--   obtain ⟨hψ₁, hψ₂⟩ := h
--   exact ⟨hψ₁.mono h', hψ₂.mono h'⟩

class LogicalPi (k : ℕ) (φ : L.BoundedFormula' n) (T : L.Theory) : Prop where
  isLogicalPi : φ.IsLogicalPi k T

class LogicalSigma (k : ℕ) (φ : L.BoundedFormula' n) (T : L.Theory) : Prop where
  isLogicalSigma : φ.IsLogicalSigma k T

class abbrev LogicalDelta (k : ℕ) (φ : L.BoundedFormula' n) (T : L.Theory) : Prop :=
  φ.LogicalPi k T, φ.LogicalSigma k T

-- instance [φ.LogicalDelta k T] : φ.LogicalPi k T := by infer_instance
-- instance [φ.LogicalDelta k T] : φ.LogicalSigma k T := by infer_instance

instance [h : φ.Pi k] : φ.LogicalPi k T := ⟨h.isPi.isLogicalPi⟩

instance [h : φ.Sigma k] : φ.LogicalSigma k T := ⟨h.isSigma.isLogicalSigma⟩

instance [h : φ.DeltaZero] : φ.LogicalPi 0 T := ⟨h.isDeltaZero.isLogicalPi⟩

instance [h : φ.DeltaZero] : φ.LogicalSigma 0 T := ⟨h.isDeltaZero.isLogicalSigma⟩

instance [h : φ.LogicalPi 0 T] : φ.LogicalSigma 0 T :=
  ⟨by simpa [isLogicalSigma_zero_iff_isLogicalPi_zero] using h.isLogicalPi⟩

instance [h : φ.LogicalSigma 0 T] : φ.LogicalPi 0 T :=
  ⟨by simpa [isLogicalSigma_zero_iff_isLogicalPi_zero] using h.isLogicalSigma⟩

variable {φ : L.BoundedFormula' (n + m)}

instance [h : φ.LogicalPi (k + 1) T] : (φ.all' m).LogicalPi (k + 1) T := ⟨h.isLogicalPi.all'⟩

instance [h : φ.LogicalPi k T] [hk : NeZero k] :
  (φ.all' m).LogicalPi k T := ⟨h.isLogicalPi.all'₀ hk.out⟩

instance [h : φ.LogicalPi k T] :
  (φ.ex' m).LogicalSigma (k + 1) T := ⟨h.isLogicalPi.ex'⟩

instance [h : φ.LogicalSigma (k + 1) T] :
  (φ.ex' m).LogicalSigma (k + 1) T := ⟨h.isLogicalSigma.ex'⟩

instance [h : φ.LogicalSigma k T] [hk : NeZero k] :
  (φ.ex' m).LogicalSigma k T := ⟨h.isLogicalSigma.ex'₀ hk.out⟩

instance [h : φ.LogicalSigma k T] :
  (φ.all' m).LogicalPi (k + 1) T := ⟨h.isLogicalSigma.all'⟩

variable {φ : L.BoundedFormula' (n + 1)}

instance [h : φ.LogicalPi (k + 1) T] : (φ.all).LogicalPi (k + 1) T := ⟨h.isLogicalPi.all'⟩

instance [h : φ.LogicalPi k T] [hk : NeZero k] :
  (φ.all).LogicalPi k T := ⟨h.isLogicalPi.all'₀ hk.out⟩

instance [h : φ.LogicalPi k T] :
  (φ.ex).LogicalSigma (k + 1) T := ⟨h.isLogicalPi.ex'⟩

instance [h : φ.LogicalSigma (k + 1) T] :
  (φ.ex).LogicalSigma (k + 1) T := ⟨h.isLogicalSigma.ex'⟩

instance [h : φ.LogicalSigma k T] [hk : NeZero k] :
  (φ.ex).LogicalSigma k T := ⟨h.isLogicalSigma.ex'₀ hk.out⟩

instance [h : φ.LogicalSigma k T] :
  (φ.all).LogicalPi (k + 1) T := ⟨h.isLogicalSigma.all'⟩

variable {φ ψ : L.BoundedFormula' n}

instance [h : φ.LogicalPi k T] :
  (∼φ).LogicalSigma k T := ⟨h.isLogicalPi.not⟩

instance [h : φ.LogicalSigma k T] :
  (∼φ).LogicalPi k T := ⟨h.isLogicalSigma.not⟩

-- instance [h : φ.LogicalDelta k T] : (∼φ).LogicalDelta k T where
--   isLogicalPi := h.isLogicalSigma.not
--   isLogicalSigma := h.isLogicalPi.not

instance [hφ : φ.LogicalPi k T] [hψ : ψ.LogicalSigma k T] :
  (φ ⟹ ψ).LogicalSigma k T := ⟨hφ.isLogicalPi.imp hψ.isLogicalSigma⟩

instance [hφ : φ.LogicalSigma k T] [hψ : ψ.LogicalPi k T] :
  (φ ⟹ ψ).LogicalPi k T := ⟨hφ.isLogicalSigma.imp hψ.isLogicalPi⟩

-- instance {k n : ℕ} {φ ψ : L.BoundedFormula' n}
  -- [hφ : φ.LogicalDelta k T] [hψ : ψ.LogicalDelta k T] :
  -- (φ ⟹ ψ).LogicalDelta k T where
  -- isLogicalPi := hφ.isLogicalSigma.imp hψ.isLogicalPi
  -- isLogicalSigma := hφ.isLogicalPi.imp hψ.isLogicalSigma

instance {φ ψ : L.BoundedFormula' n}
  [hφ : φ.LogicalPi k T] [hψ : ψ.LogicalPi k T] :
  (φ ⊔ ψ).LogicalPi k T := ⟨hφ.isLogicalPi.sup hψ.isLogicalPi⟩

instance {φ ψ : L.BoundedFormula' n}
  [hφ : φ.LogicalPi k T] [hψ : ψ.LogicalPi k T] :
  (φ ⊓ ψ).LogicalPi k T := ⟨hφ.isLogicalPi.inf hψ.isLogicalPi⟩

instance {φ ψ : L.BoundedFormula' n}
  [hφ : φ.LogicalSigma k T] [hψ : ψ.LogicalSigma k T] :
  (φ ⊔ ψ).LogicalSigma k T := ⟨hφ.isLogicalSigma.sup hψ.isLogicalSigma⟩

instance {φ ψ : L.BoundedFormula' n}
  [hφ : φ.LogicalSigma k T] [hψ : ψ.LogicalSigma k T] :
  (φ ⊓ ψ).LogicalSigma k T := ⟨hφ.isLogicalSigma.inf hψ.isLogicalSigma⟩

instance [Finite β] {f : β → L.BoundedFormula' n}
    [hf : ∀ i, (f i).LogicalPi k T] :
    (iSup f).LogicalPi k T := ⟨isLogicalPi_iSup (fun i ↦ (hf i).isLogicalPi)⟩

instance [Finite β] {f : β → L.BoundedFormula' n}
    [hf : ∀ i, (f i).LogicalPi k T] :
    (iInf f).LogicalPi k T := ⟨isLogicalPi_iInf (fun i ↦ (hf i).isLogicalPi)⟩

instance [Finite β] {f : β → L.BoundedFormula' n}
    [hf : ∀ i, (f i).LogicalSigma k T] :
    (iSup f).LogicalSigma k T := ⟨isLogicalSigma_iSup (fun i ↦ (hf i).isLogicalSigma)⟩

instance [Finite β] {f : β → L.BoundedFormula' n}
    [hf : ∀ i, (f i).LogicalSigma k T] :
    (iInf f).LogicalSigma k T := ⟨isLogicalSigma_iInf (fun i ↦ (hf i).isLogicalSigma)⟩

-- instance {φ ψ : L.BoundedFormula' n}
--   [hφ : φ.LogicalDelta k T] [hψ : ψ.LogicalDelta k T] :
--   (φ ⊔ ψ).LogicalDelta k T where
--   isLogicalPi := hφ.isLogicalPi.sup hψ.isLogicalPi
--   isLogicalSigma := hφ.isLogicalSigma.sup hψ.isLogicalSigma

-- instance {φ ψ : L.BoundedFormula' n}
--   [hφ : φ.LogicalDelta k T] [hψ : ψ.LogicalDelta k T] :
--   (φ ⊓ ψ).LogicalDelta k T where
--   isLogicalPi := hφ.isLogicalPi.inf hψ.isLogicalPi
--   isLogicalSigma := hφ.isLogicalSigma.inf hψ.isLogicalSigma

instance {φ ψ : L.BoundedFormula' n}
  [hφ : φ.LogicalDelta k T] [hψ : ψ.LogicalDelta k T] :
  (φ ⇔ ψ).LogicalDelta k T where
  isLogicalPi :=
    (hφ.isLogicalSigma.imp hψ.isLogicalPi).inf (hψ.isLogicalSigma.imp hφ.isLogicalPi)
  isLogicalSigma :=
    (hφ.isLogicalPi.imp hψ.isLogicalSigma).inf (hψ.isLogicalPi.imp hφ.isLogicalSigma)

instance {φ : L.BoundedFormula' n}
  [hφ : φ.LogicalPi k T] (ts : Fin n → L.Term' m) :
  (φ.substBound ts).LogicalPi k T :=
  ⟨hφ.isLogicalPi.substBound _⟩

instance {φ : L.BoundedFormula' n}
  [hφ : φ.LogicalSigma k T] (ts : Fin n → L.Term' m) :
  (φ.substBound ts).LogicalSigma k T :=
  ⟨hφ.isLogicalSigma.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.LogicalPi k T] :
  (φ.substBoundBound f).LogicalPi k T := ⟨h.isLogicalPi.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.LogicalSigma k T] :
  (φ.substBoundBound f).LogicalSigma k T := ⟨h.isLogicalSigma.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.LogicalPi k T] (h' : n = n') :
  (φ.cast h').LogicalPi k T := ⟨h.isLogicalPi.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.LogicalSigma k T] (h' : n = n') :
  (φ.cast h').LogicalSigma k T := ⟨h.isLogicalSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + p)} {ψ : L.BoundedFormula' (n + q)} [hφ : φ.LogicalSigma k T]
  [hψ : ψ.LogicalPi k T] : (φ.splitImp ψ).LogicalPi k T :=
  ⟨(hφ.isLogicalSigma.substBound _).imp (hψ.isLogicalPi.substBound _)⟩

instance {φ : L.BoundedFormula' (n + p)} {ψ : L.BoundedFormula' (n + q)} [hφ : φ.LogicalPi k T]
  [hψ : ψ.LogicalSigma k T] : (φ.splitImp ψ).LogicalSigma k T :=
  ⟨(hφ.isLogicalPi.substBound _).imp (hψ.isLogicalSigma.substBound _)⟩

instance {φ : L.BoundedFormula' (n + p)} [hφ : φ.LogicalPi k T] :
  (φ.switchBound).LogicalPi k T :=
  ⟨hφ.isLogicalPi.substBound _⟩

instance {φ : L.BoundedFormula' (n + p)} [hφ : φ.LogicalSigma k T] :
  (φ.switchBound).LogicalSigma k T :=
  ⟨hφ.isLogicalSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + p + q)} [hφ : φ.LogicalPi k T] :
  (φ.castAssoc).LogicalPi k T :=
  ⟨hφ.isLogicalPi.substBound _⟩

instance {φ : L.BoundedFormula' (n + p + q)} [hφ : φ.LogicalSigma k T] :
  (φ.castAssoc).LogicalSigma k T :=
  ⟨hφ.isLogicalSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.LogicalPi k T] :
  (φ.castAssoc').LogicalPi k T :=
  ⟨hφ.isLogicalPi.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.LogicalSigma k T] :
  (φ.castAssoc').LogicalSigma k T :=
  ⟨hφ.isLogicalSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.LogicalPi k T] :
  (φ.switchBoundRight).LogicalPi k T :=
  ⟨hφ.isLogicalPi.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.LogicalSigma k T] :
  (φ.switchBoundRight).LogicalSigma k T :=
  ⟨hφ.isLogicalSigma.substBound _⟩

instance {φ : L.BoundedFormula' (p + n)} {ψ : L.BoundedFormula' (q + n)} [hφ : φ.LogicalSigma k T]
  [hψ : ψ.LogicalPi k T] : (φ.splitImp' ψ).LogicalPi k T := by rw [splitImp']; infer_instance

instance {φ : L.BoundedFormula' (p + n)} {ψ : L.BoundedFormula' (q + n)} [hφ : φ.LogicalPi k T]
  [hψ : ψ.LogicalSigma k T] : (φ.splitImp' ψ).LogicalSigma k T := by rw [splitImp']; infer_instance


end LogicalLevyHierarchy

end BoundedFormula

end Language

end FirstOrder
