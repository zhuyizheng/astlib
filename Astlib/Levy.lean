import Astlib.Syntax
import Astlib.ModelTheory.Satisfiability
import Astlib.ModelTheory.Bundled

open FirstOrder Language BoundedFormula Theory

variable {α : Type*}
-- [DecidableEq α]
  {L : FirstOrder.Language}
  -- [DecidableEq (L.Relations 2)]
  -- [∀ n : ℕ, DecidableEq (L.Functions n)]
  [HasMem L]

namespace FirstOrder

namespace Language

namespace BoundedFormula
variable {n : ℕ}

section SyntacticalLevyHierarchy

inductive DeltaZero : ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | falsum : falsum.DeltaZero
  | equal {n : ℕ} (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁ =' t₂).DeltaZero
  | rel {n : ℕ} {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) :
    (rel R ts).DeltaZero
  | imp {n : ℕ} {φ₁ φ₂ : L.BoundedFormula α n} (hφ₁ : φ₁.DeltaZero) (hφ₂ : φ₂.DeltaZero):
    (imp φ₁ φ₂).DeltaZero
  | bddAll {n : ℕ} {φ : L.BoundedFormula α (n + 1)} (t : L.Term (α ⊕ Fin n)) (hφ : φ.DeltaZero) :
    (∀' (&-1 ∈' t.castSucc ⟹ φ)).DeltaZero

mutual
  inductive Pi : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ → Prop
    | zero {n : ℕ} {φ : L.BoundedFormula α n} (hφ : φ.DeltaZero) : φ.Pi 0
    | succ (m : ℕ) {n k : ℕ} {φ : L.BoundedFormula α (n + m)} (hφ : φ.Sigma k) :
      (φ.all' m).Pi (k + 1)

  inductive Sigma : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ → Prop
    | zero {n : ℕ} {φ : L.BoundedFormula α n} (hφ : φ.DeltaZero) : φ.Sigma 0
    | succ (m : ℕ) {n k : ℕ} {φ : L.BoundedFormula α (n + m)} (hφ : φ.Pi k) :
      (φ.ex' m).Sigma (k + 1)
end

variable {k n : ℕ} {φ ψ : L.BoundedFormula α n}

theorem DeltaZero.not (h : φ.DeltaZero) : (∼φ).DeltaZero := h.imp DeltaZero.falsum

@[simp]
theorem DeltaZero.not_iff : (∼φ).DeltaZero ↔ φ.DeltaZero := by
  refine ⟨?_, DeltaZero.not⟩
  rintro (h | h)
  assumption

theorem DeltaZero.sup (hφ : φ.DeltaZero) (hψ : ψ.DeltaZero) : (φ ⊔ ψ).DeltaZero := hφ.not.imp hψ

theorem DeltaZero.inf (hφ : φ.DeltaZero) (hψ : ψ.DeltaZero) : (φ ⊓ ψ).DeltaZero :=
  hφ.imp hψ.not |>.not

theorem DeltaZero.iff (hφ : φ.DeltaZero) (hψ : ψ.DeltaZero) : (φ ⇔ ψ).DeltaZero :=
  (hφ.imp hψ).inf (hψ.imp hφ)

@[simp]
theorem Pi_zero_iff_DeltaZero : φ.Pi 0 ↔ φ.DeltaZero := by grind [Pi]

@[simp]
theorem Sigma_zero_iff_DeltaZero : φ.Sigma 0 ↔ φ.DeltaZero := by grind [Sigma]

theorem Pi.ex' {φ : L.BoundedFormula α (n + m)} (h : φ.Pi k) :
    (φ.ex' m).Sigma (k + 1) := Sigma.succ m h

theorem Pi.ex {φ : L.BoundedFormula α (n + 1)} (h : φ.Pi k) :
    (∃' φ).Sigma (k + 1) := Sigma.succ 1 h

theorem Pi.Sigma_succ (h : φ.Pi k) : φ.Sigma (k + 1) := Sigma.succ 0 h

theorem Sigma.all' {φ : L.BoundedFormula α (n + m)} (h : φ.Sigma k) :
    (φ.all' m).Pi (k + 1) := Pi.succ m h

theorem Sigma.all {φ : L.BoundedFormula α (n + 1)} (h : φ.Sigma k) :
    (∀' φ).Pi (k + 1) := Pi.succ 1 h

theorem Sigma.Pi_succ (h : φ.Sigma k) : φ.Pi (k + 1) := Pi.succ 0 h

theorem Pi.exists_Sigma_all' (h : φ.Pi (k + 1)) :
    ∃ (m : ℕ), ∃ ψ : L.BoundedFormula α (n + m), ψ.Sigma k ∧ φ = ψ.all' m := by
  cases h with | succ m hψ
  exact ⟨m, _, hψ, rfl⟩

theorem Sigma.exists_Pi_ex' (h : φ.Sigma (k + 1)) :
    ∃ (m : ℕ), ∃ ψ : L.BoundedFormula α (n + m), ψ.Pi k ∧ φ = ψ.ex' m := by
  cases h with | succ m hψ
  exact ⟨m, _, hψ, rfl⟩

theorem DeltaZero.cast (h : φ.DeltaZero) (h' : n = n') : (φ.cast h').DeltaZero := by
  revert n'
  induction h with
  | falsum => exact fun _ ↦ DeltaZero.falsum
  | equal => exact fun _ ↦ DeltaZero.equal _ _
  | rel => exact fun _ ↦ DeltaZero.rel _ _
  | imp h₁ h₂ ih₁ ih₂ =>
    simp only [BoundedFormula.cast, castLE]
    exact fun h' ↦ DeltaZero.imp (ih₁ h') (ih₂ h')
  | bddAll t hψ ih =>
    intro n' h'
    simp only [BoundedFormula.cast, castLE, Function.comp_apply, Term.castSucc, Nat.succ_eq_add_one,
      castLE_mem_boundedFormula, Term.castLE_var_inr, Term.castLE_castLE]
    convert DeltaZero.bddAll (t.cast h') (ih (by rw [h']))
    · grind
    · simp

mutual
theorem Pi.cast {k n n' : ℕ} {φ : L.BoundedFormula α n} (h' : n = n') (h : φ.Pi k) :
    (φ.cast h').Pi k :=
  match k with
  | 0 => by
    simp only [Pi_zero_iff_DeltaZero] at h ⊢
    exact h.cast h'
  | k + 1 => by
    obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Sigma_all'
    simp only [cast, hψ₂, castLE_all'_eq_all'_cast]
    exact hψ₁.cast (h' ▸ rfl) |>.all'

theorem Sigma.cast {k n n' : ℕ} {φ : L.BoundedFormula α n} (h' : n = n') (h : φ.Sigma k) :
    (φ.cast h').Sigma k :=
  match k with
  | 0 => by
    simp only [Sigma_zero_iff_DeltaZero] at h ⊢
    exact h.cast h'
  | k + 1 => by
    obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Pi_ex'
    simp only [cast, hψ₂, castLE_ex'_eq_ex'_cast]
    exact hψ₁.cast (h' ▸ rfl) |>.ex'
end

theorem DeltaZero.liftAt {n n' p : ℕ} {φ : L.BoundedFormula α n} (hmn : p ≤ n)
    (h : φ.DeltaZero) : (φ.liftAt n' p).DeltaZero := by
  revert n'
  induction h with
  | falsum => exact DeltaZero.falsum
  | equal => exact DeltaZero.equal _ _
  | rel => exact DeltaZero.rel _ _
  | imp h₁ h₂ ih₁ ih₂ =>
    simp only [liftAt_imp]
    exact DeltaZero.imp (ih₁ hmn) (ih₂ hmn)
  | @bddAll n ψ t hψ ih =>
    intro n'
    simp only [Function.comp_apply, Term.castSucc, Nat.succ_eq_add_one, liftAt_all,
      BoundedFormula.cast, liftAt_imp, liftAt_mem_boundedFormula, Term.liftAt_var_inr, Fin.val_last,
      Fin.addNat_last, castLE_imp, castLE_mem_boundedFormula, Term.castLE_var_inr]
    convert DeltaZero.bddAll (t.liftAt n' p) ((ih (n' := n') (by omega)).cast (by omega))
    · grind [Term.var.injEq, Sum.inr.injEq]
    · simp only [Term.castLE, Term.liftAt, Term.relabel_relabel, Sum.map_comp_map,
        Term.castSucc]
      congr 1
      simp only [Sum.map]
      congr 2
      grind

mutual
theorem Pi.liftAt {k n n' p : ℕ} {φ : L.BoundedFormula α n} (hpn : p ≤ n) (h : φ.Pi k) :
    (φ.liftAt n' p).Pi k :=
  match k with
  | 0 => by
    simp only [Pi_zero_iff_DeltaZero] at h ⊢
    exact h.liftAt hpn
  | k + 1 => by
    obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Sigma_all'
    simp only [hψ₂, liftAt_all'_eq_all'_cast_liftAt]
    exact hψ₁.liftAt (by omega) |>.cast (by omega) |>.all'

theorem Sigma.liftAt {k n n' p : ℕ} {φ : L.BoundedFormula α n} (hpn : p ≤ n) (h : φ.Sigma k) :
    (φ.liftAt n' p).Sigma k :=
  match k with
  | 0 => by
    simp only [Sigma_zero_iff_DeltaZero] at h ⊢
    exact h.liftAt hpn
  | k + 1 => by
    obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Pi_ex'
    simp only [hψ₂, liftAt_ex'_eq_ex'_cast_liftAt, cast]
    exact hψ₁.liftAt (by omega) |>.cast (by omega) |>.ex'
end

theorem Pi.all' {φ : L.BoundedFormula α (n + m)} (h : φ.Pi (k + 1)) :
    (φ.all' m).Pi (k + 1) := by
  obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Sigma_all'
  rw [hψ₂, ψ.all'_all'_eq_all'_cast]
  exact (hψ₁.cast _).all'

theorem Pi.all {φ : L.BoundedFormula α (n + 1)} (h : φ.Pi (k + 1)) :
    φ.all.Pi (k + 1) := h.all'

theorem Sigma.ex' {φ : L.BoundedFormula α (n + m)} (h : φ.Sigma (k + 1)) :
    (φ.ex' m).Sigma (k + 1) := by
  obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Pi_ex'
  rw [hψ₂, ψ.ex'_ex'_eq_ex'_cast]
  exact (hψ₁.cast _).ex'

theorem Sigma.ex {φ : L.BoundedFormula α (n + 1)} (h : φ.Sigma (k + 1)) :
    φ.ex.Sigma (k + 1) := h.ex'

mutual
theorem Pi.Pi_succ {k n : ℕ} {φ : L.BoundedFormula α n} (h : φ.Pi k) :
    φ.Pi (k + 1) :=
  match k with
  | 0 => Sigma.Pi_succ (by simpa using h)
  | k + 1 => by
    obtain ⟨_, _, hψ, _⟩ := h.exists_Sigma_all'
    convert hψ.Sigma_succ.all'

theorem Sigma.Sigma_succ {k n : ℕ} {φ : L.BoundedFormula α n} (h : φ.Sigma k) :
    φ.Sigma (k + 1) :=
  match k with
  | 0 => Pi.Sigma_succ (by simpa using h)
  | k + 1 => by
    obtain ⟨_, _, hψ, _⟩ := h.exists_Pi_ex'
    convert hψ.Pi_succ.ex'
end

variable {m : ℕ}
variable {φ : L.BoundedFormula α n}

theorem Pi.Pi_of_le (h : φ.Pi k) (hkm : k ≤ m) : φ.Pi m := by
  induction m with
  | zero => grind
  | succ m ih =>
    rcases lt_or_eq_of_le hkm with hkm | rfl
    · exact ih (Nat.le_of_lt_succ hkm) |>.Pi_succ
    · exact h

theorem Sigma.Sigma_of_le (h : φ.Sigma k) (hkm : k ≤ m) : φ.Sigma m := by
  induction m with
  | zero => convert h; omega
  | succ m ih =>
    rcases lt_or_eq_of_le hkm with hkm | rfl
    · exact ih (Nat.le_of_lt_succ hkm) |>.Sigma_succ
    · exact h

theorem Pi.Sigma_of_lt (h : φ.Pi k) (hkm : k < m) : φ.Sigma m :=
  h.Sigma_succ.Sigma_of_le (Nat.add_one_le_of_lt hkm)

theorem Sigma.Pi_of_lt (h : φ.Sigma k) (hkm : k < m) : φ.Pi m :=
  h.Pi_succ.Pi_of_le (Nat.add_one_le_of_lt hkm)

end SyntacticalLevyHierarchy


section LogicalLevyHierarchy

variable {k n : ℕ} {φ ψ : L.BoundedFormula α n}

/-- `φ` is `T`-logically `Π n` means that `φ` is `T`-equivalent to a `Π n` formula -/
def LogicalPi (k : ℕ) {n : ℕ} (φ : L.BoundedFormula α n) (T : L.Theory) : Prop :=
  ∃ ψ : L.BoundedFormula α n, (ψ.Pi k ∧ T ⊨ᵇ φ ⇔ ψ)

/-- `φ` is `T`-logically `Σ n` means that `φ` is `T`-equivalent to a `Σ n` formula -/
def LogicalSigma (k : ℕ) {n : ℕ} (φ : L.BoundedFormula α n) (T : L.Theory) : Prop :=
  ∃ ψ : L.BoundedFormula α n, (ψ.Sigma k ∧ T ⊨ᵇ φ ⇔ ψ)

/-- `φ` is `T`-logically `Δ n` means that `φ` is `T`-logically `Π n` and `T`-logically `Σ n` -/
def LogicalDelta (k : ℕ) {n : ℕ} (φ : L.BoundedFormula α n) (T : L.Theory) : Prop :=
  φ.LogicalPi k T ∧ φ.LogicalSigma k T

variable {T : L.Theory}

theorem Pi.LogicalPi (h : φ.Pi k) : φ.LogicalPi k T :=
  ⟨φ, h, by simp [ModelsBoundedFormula]⟩

theorem Sigma.LogicalSigma (h : φ.Sigma k) : φ.LogicalSigma k T :=
  ⟨φ, h, by simp [ModelsBoundedFormula]⟩

theorem DeltaZero.LogicalDelta (h : φ.DeltaZero) : φ.LogicalDelta 0 T := by
  constructor
  · apply Pi.LogicalPi; simpa
  · apply Sigma.LogicalSigma; simpa

@[simp]
theorem LogicalPi_zero_iff_LogicalDelta_zero : φ.LogicalPi 0 T ↔ φ.LogicalDelta 0 T :=
  ⟨fun ⟨ψ, hψ⟩ ↦ ⟨⟨ψ, hψ⟩, ⟨ψ, by simpa using hψ⟩⟩, fun h ↦ h.left⟩

@[simp]
theorem LogicalSigma_zero_iff_LogicalDelta_zero :
    φ.LogicalSigma 0 T ↔ φ.LogicalDelta 0 T :=
  ⟨fun ⟨ψ, hψ⟩ ↦ ⟨⟨ψ, by simpa using hψ⟩, ⟨ψ, hψ⟩⟩, fun h ↦ h.right⟩

theorem LogicalDelta.LogicalPi (h : φ.LogicalDelta k T) : φ.LogicalPi k T := h.left

theorem LogicalDelta.LogicalSigma (h : φ.LogicalDelta k T) : φ.LogicalSigma k T := h.right

/- logical quantifiers -/

variable {φ : L.BoundedFormula α (n + m)}

theorem LogicalPi.all' (h : φ.LogicalPi (k + 1) T) : (φ.all' m).LogicalPi (k + 1) T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ.all' m, hψ₁.all'
  simp only [ModelsBoundedFormula.iff_iff]
  constructor <;> exact hψ₂.all'.of_imp (by simp +contextual [ModelsBoundedFormula])

theorem LogicalPi.all'₀ (h : φ.LogicalPi k T) (hk : k ≠ 0) : (φ.all' m).LogicalPi k T := by
  rw [show k = k - 1 + 1 by omega] at h ⊢
  exact h.all'

theorem LogicalPi.ex' (h : φ.LogicalPi k T) :  (φ.ex' m).LogicalSigma (k + 1) T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ.ex' m, hψ₁.ex'
  simp only [ModelsBoundedFormula.iff_iff]
  constructor <;> exact hψ₂.all'.of_imp (by simp +contextual [ModelsBoundedFormula])

theorem LogicalSigma.ex' (h : φ.LogicalSigma (k + 1) T) :
    (φ.ex' m).LogicalSigma (k + 1) T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ.ex' m, hψ₁.ex'
  simp only [ModelsBoundedFormula.iff_iff]
  constructor <;> exact hψ₂.all'.of_imp (by simp +contextual [ModelsBoundedFormula])

theorem LogicalSigma.ex'₀ (h : φ.LogicalSigma k T) (hk : k ≠ 0) :
    (φ.ex' m).LogicalSigma k T := by
  rw [show k = k - 1 + 1 by omega] at h ⊢
  exact h.ex'

theorem LogicalSigma.all' (h : φ.LogicalSigma k T) :  (φ.all' m).LogicalPi (k + 1) T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ.all' m, hψ₁.all'
  simp only [ModelsBoundedFormula.iff_iff]
  constructor <;> exact hψ₂.all'.of_imp (by simp +contextual [ModelsBoundedFormula])

theorem LogicalDelta.all' (h : φ.LogicalDelta (k + 1) T) : (φ.all' m).LogicalPi (k + 1) T :=
  h.left.all'

theorem LogicalDelta.all'₀ (h : φ.LogicalDelta k T) (hk : k ≠ 0) :
    (φ.all' m).LogicalPi k T :=
  h.left.all'₀ hk

theorem LogicalDelta.ex' (h : φ.LogicalDelta (k + 1) T) : (φ.ex' m).LogicalSigma (k + 1) T :=
  h.right.ex'

theorem LogicalDelta.ex'₀ (h : φ.LogicalDelta k T) (hk : k ≠ 0) :
    (φ.ex' m).LogicalSigma k T :=
  h.right.ex'₀ hk


/- invariance under `T`-logical equivalence -/

variable {φ ψ : L.BoundedFormula α n}

theorem LogicalPi.of_models_iff (h : φ.LogicalPi k T) (h' : T ⊨ᵇ φ ⇔ ψ) :
    ψ.LogicalPi k T := by
  obtain ⟨θ, hθ₁, hθ₂⟩ := h
  exact ⟨θ, hθ₁, h'.of_imp_imp hθ₂ (by simp +contextual [ModelsBoundedFormula])⟩

theorem LogicalSigma.of_models_iff (h : φ.LogicalSigma k T) (h' : T ⊨ᵇ φ ⇔ ψ) :
    ψ.LogicalSigma k T := by
  obtain ⟨θ, hθ₁, hθ₂⟩ := h
  exact ⟨θ, hθ₁, h'.of_imp_imp hθ₂ (by simp +contextual [ModelsBoundedFormula])⟩

theorem LogicalDelta.of_models_iff (h : φ.LogicalDelta k T) (h' : T ⊨ᵇ φ ⇔ ψ) :
    ψ.LogicalDelta k T :=
  ⟨h.left.of_models_iff h', h.right.of_models_iff h'⟩

/- logical connectives -/

mutual
theorem LogicalPi.not {k n : ℕ} {φ : L.BoundedFormula α n} (h : φ.LogicalPi k T) :
    (∼φ).LogicalSigma k T :=
  let ⟨ψ, hψ₁, hψ₂⟩ := h
  match k with
  | 0 => ⟨∼ψ, by simpa using hψ₁, hψ₂.of_imp (by simp +contextual [ModelsBoundedFormula])⟩
  | k + 1 => let ⟨m, θ, hθ₁, hθ₂⟩ := hψ₁.exists_Sigma_all'
    hθ₁.LogicalSigma.not.ex'.of_models_iff <|
      (hθ₂ ▸ hψ₂).of_imp (by simp +contextual [ModelsBoundedFormula])

theorem LogicalSigma.not {k n : ℕ} {φ : L.BoundedFormula α n} (h : φ.LogicalSigma k T) :
    (∼φ).LogicalPi k T :=
  let ⟨ψ, hψ₁, hψ₂⟩ := h
  match k with
  | 0 => ⟨∼ψ, by simpa using hψ₁, hψ₂.of_imp (by simp +contextual [ModelsBoundedFormula])⟩
  | k + 1 => let ⟨m, θ, hθ₁, hθ₂⟩ := hψ₁.exists_Pi_ex'
    hθ₁.LogicalPi.not.all'.of_models_iff <|
      (hθ₂ ▸ hψ₂).of_imp (by simp +contextual [ModelsBoundedFormula])
end

theorem LogicalDelta.not (h : φ.LogicalDelta k T) : (∼φ).LogicalDelta k T :=
  ⟨h.right.not, h.left.not⟩

@[simp]
theorem LogicalPi_not_iff : (∼φ).LogicalPi k T ↔ φ.LogicalSigma k T := by
  refine ⟨fun h ↦ h.not.of_models_iff ?_, LogicalSigma.not⟩
  simp +contextual [ModelsBoundedFormula]

@[simp]
theorem LogicalSigma_not_iff : (∼φ).LogicalSigma k T ↔ φ.LogicalPi k T := by
  refine ⟨fun h ↦ h.not.of_models_iff ?_, LogicalPi.not⟩
  simp +contextual [ModelsBoundedFormula]

@[simp]
theorem LogicalDelta_not_iff : (∼φ).LogicalDelta k T ↔ φ.LogicalDelta k T := by
  refine ⟨fun h ↦ h.not.of_models_iff ?_, LogicalDelta.not⟩
  simp +contextual [ModelsBoundedFormula]

mutual
theorem LogicalPi.imp {k n : ℕ} {φ ψ : L.BoundedFormula α n}
    (hφ : φ.LogicalPi k T) (hψ : ψ.LogicalSigma k T) : (φ ⟹ ψ).LogicalSigma k T :=
  let ⟨φ', hφ₁, hφ₂⟩ := hφ
  let ⟨ψ', hψ₁, hψ₂⟩ := hψ
  match k with
  | 0 => by
    refine ⟨φ' ⟹ ψ', ?_, ?_⟩
    · simp only [Pi_zero_iff_DeltaZero, Sigma_zero_iff_DeltaZero] at hφ₁ hψ₁ ⊢
      exact hφ₁.imp hψ₁
    · exact hφ₂.of_imp_imp hψ₂ (by simp +contextual [ModelsBoundedFormula])
  | k + 1 => by
    obtain ⟨p, φ'', hφ''₁, hφ''₂⟩ := hφ₁.exists_Sigma_all'
    obtain ⟨q, ψ'', hψ''₁, hψ''₂⟩ := hψ₁.exists_Pi_ex'
    let θ := (φ''.liftAt q (n + p)).cast (Nat.add_assoc _ _ _) ⟹
      (ψ''.liftAt p n).cast (by rw [Nat.add_assoc, add_comm q]) |>.ex' (p + q)
    have : θ.LogicalSigma (k + 1) T :=
      ((hφ''₁.liftAt (by omega)).cast _).LogicalSigma.imp
        ((hψ''₁.liftAt (by omega)).cast _).LogicalPi |>.ex'
    refine this.of_models_iff (fun M v xs ↦ ?_)
    specialize hφ₂ M v xs
    specialize hψ₂ M v xs
    have := realize_imp_all'_ex' (M := M) (θ := φ'') (ψ := ψ'') (xs := xs) (v := v)
    simp_all only [cast, realize_ex', realize_imp, realize_all', realize_iff]
    convert this
    simp [θ]

theorem LogicalSigma.imp {k n : ℕ} {φ ψ : L.BoundedFormula α n}
    (hφ : φ.LogicalSigma k T) (hψ : ψ.LogicalPi k T) : (φ ⟹ ψ).LogicalPi k T :=
  let ⟨φ', hφ₁, hφ₂⟩ := hφ
  let ⟨ψ', hψ₁, hψ₂⟩ := hψ
  match k with
  | 0 => by
    refine ⟨φ' ⟹ ψ', ?_, ?_⟩
    · simp only [Pi_zero_iff_DeltaZero, Sigma_zero_iff_DeltaZero] at hφ₁ hψ₁ ⊢
      exact hφ₁.imp hψ₁
    · exact hφ₂.of_imp_imp hψ₂ (by simp +contextual [ModelsBoundedFormula])
  | k + 1 => by
    obtain ⟨p, φ'', hφ''₁, hφ''₂⟩ := hφ₁.exists_Pi_ex'
    obtain ⟨q, ψ'', hψ''₁, hψ''₂⟩ := hψ₁.exists_Sigma_all'
    let θ := (φ''.liftAt q (n + p)).cast (Nat.add_assoc _ _ _) ⟹
      (ψ''.liftAt p n).cast (by rw [Nat.add_assoc, add_comm q]) |>.all' (p + q)
    have : θ.LogicalPi (k + 1) T :=
      ((hφ''₁.liftAt (by omega)).cast _).LogicalPi.imp
        ((hψ''₁.liftAt (by omega)).cast _).LogicalSigma |>.all'
    refine this.of_models_iff (fun M v xs ↦ ?_)
    specialize hφ₂ M v xs
    specialize hψ₂ M v xs
    have := realize_imp_ex'_all' (M := M) (θ := φ'') (ψ := ψ'') (xs := xs) (v := v)
    simp_all only [cast, realize_ex', realize_imp, realize_all', realize_iff]
    convert this
    simp [θ]
end

theorem LogicalDelta.imp {k n : ℕ} {φ ψ : L.BoundedFormula α n}
    (hφ : φ.LogicalDelta k T) (hψ : ψ.LogicalDelta k T) : (φ ⟹ ψ).LogicalDelta k T :=
  ⟨hφ.right.imp hψ.left, hφ.left.imp hψ.right⟩

theorem LogicalPi.sup (hφ : φ.LogicalPi k T) (hψ : ψ.LogicalPi k T) :
    (φ ⊔ ψ).LogicalPi k T := hφ.not.imp hψ

theorem LogicalPi.inf (hφ : φ.LogicalPi k T) (hψ : ψ.LogicalPi k T) :
    (φ ⊓ ψ).LogicalPi k T := hφ.imp hψ.not |>.not

theorem LogicalSigma.sup (hφ : φ.LogicalSigma k T) (hψ : ψ.LogicalSigma k T) :
    (φ ⊔ ψ).LogicalSigma k T := hφ.not.imp hψ

theorem LogicalSigma.inf (hφ : φ.LogicalSigma k T) (hψ : ψ.LogicalSigma k T) :
    (φ ⊓ ψ).LogicalSigma k T := hφ.imp hψ.not |>.not

theorem LogicalDelta.sup (hφ : φ.LogicalDelta k T) (hψ : ψ.LogicalDelta k T) :
    (φ ⊔ ψ).LogicalDelta k T := hφ.not.imp hψ

theorem LogicalDelta.inf (hφ : φ.LogicalDelta k T) (hψ : ψ.LogicalDelta k T) :
    (φ ⊓ ψ).LogicalDelta k T := hφ.imp hψ.not |>.not

theorem LogicalDelta.iff (hφ : φ.LogicalDelta k T) (hψ : ψ.LogicalDelta k T) :
    (φ ⇔ ψ).LogicalDelta k T := (hφ.imp hψ).inf (hψ.imp hφ)

/- lower levels are included in upper levels -/

theorem LogicalPi.LogicalPi_of_le (h : φ.LogicalPi k T) (hkm : k ≤ m) :
    φ.LogicalPi m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.Pi_of_le hkm

theorem LogicalSigma.LogicalSigma_of_le (h : φ.LogicalSigma k T) (hkm : k ≤ m) :
    φ.LogicalSigma m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.Sigma_of_le hkm

theorem LogicalDelta.LogicalDelta_of_le (h : φ.LogicalDelta k T) (hkm : k ≤ m) :
    φ.LogicalDelta m T :=
  ⟨h.left.LogicalPi_of_le hkm, h.right.LogicalSigma_of_le hkm⟩

theorem LogicalPi.LogicalSigma_of_lt (h : φ.LogicalPi k T) (hkm : k < m) :
    φ.LogicalSigma m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.Sigma_of_lt hkm

theorem LogicalSigma.LogicalPi_of_lt (h : φ.LogicalSigma k T) (hkm : k < m) :
    φ.LogicalPi m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.Pi_of_lt hkm

theorem LogicalPi.LogicalDelta_of_lt (h : φ.LogicalPi k T) (hkm : k < m) :
    φ.LogicalDelta m T :=
  ⟨h.LogicalPi_of_le hkm.le, h.LogicalSigma_of_lt hkm⟩

theorem LogicalSigma.LogicalDelta_of_lt (h : φ.LogicalSigma k T) (hkm : k < m) :
    φ.LogicalDelta m T :=
  ⟨h.LogicalPi_of_lt hkm, h.LogicalSigma_of_le hkm.le⟩


/- monotone in the theory -/

variable {T' : L.Theory}

theorem LogicalPi.mono (h : φ.LogicalPi k T) (h' : T ⊆ T') : φ.LogicalPi k T' := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  exact ⟨ψ, hψ₁, hψ₂.mono h'⟩

theorem LogicalSigma.mono (h : φ.LogicalSigma k T) (h' : T ⊆ T') : φ.LogicalSigma k T' := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  exact ⟨ψ, hψ₁, hψ₂.mono h'⟩

theorem LogicalDelta.mono (h : φ.LogicalDelta k T) (h' : T ⊆ T') : φ.LogicalDelta k T' := by
  obtain ⟨hψ₁, hψ₂⟩ := h
  exact ⟨hψ₁.mono h', hψ₂.mono h'⟩

end LogicalLevyHierarchy

end BoundedFormula

end Language

end FirstOrder
