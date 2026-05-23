import Astlib.ModelTheory.Syntax
import Astlib.Mathlib.ModelTheory.Satisfiability
import Astlib.Mathlib.ModelTheory.Bundled

open FirstOrder Language BoundedFormula Theory

variable {α : Type*} {L : FirstOrder.Language} [HasMem L]

namespace FirstOrder

namespace Language

namespace BoundedFormula
variable {n : ℕ}

section SyntacticalLevyHierarchy

inductive IsDeltaZero : ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | falsum : falsum.IsDeltaZero
  | equal {n : ℕ} (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁ =' t₂).IsDeltaZero
  | rel {n : ℕ} {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts).IsDeltaZero
  | imp {n : ℕ} {φ₁ φ₂ : L.BoundedFormula α n} (hφ₁ : φ₁.IsDeltaZero) (hφ₂ : φ₂.IsDeltaZero):
    (imp φ₁ φ₂).IsDeltaZero
  | bddAll {n : ℕ} {φ : L.BoundedFormula α (n + 1)} (t : L.Term (α ⊕ Fin n)) (hφ : φ.IsDeltaZero) :
    (∀' (&-1 ∈' t.castSucc ⟹ φ)).IsDeltaZero

mutual
  inductive IsPi : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ → Prop
    | zero {n : ℕ} {φ : L.BoundedFormula α n} (hφ : φ.IsDeltaZero) : φ.IsPi 0
    | succ (m : ℕ) {n k : ℕ} {φ : L.BoundedFormula α (n + m)} (hφ : φ.IsSigma k) :
      (φ.all' m).IsPi (k + 1)

  inductive IsSigma : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ → Prop
    | zero {n : ℕ} {φ : L.BoundedFormula α n} (hφ : φ.IsDeltaZero) : φ.IsSigma 0
    | succ (m : ℕ) {n k : ℕ} {φ : L.BoundedFormula α (n + m)} (hφ : φ.IsPi k) :
      (φ.ex' m).IsSigma (k + 1)
end

variable {k n : ℕ} {φ ψ : L.BoundedFormula α n}

theorem IsDeltaZero.not (h : φ.IsDeltaZero) : (∼φ).IsDeltaZero := h.imp IsDeltaZero.falsum

@[simp]
theorem IsDeltaZero.not_iff : (∼φ).IsDeltaZero ↔ φ.IsDeltaZero := by
  refine ⟨?_, IsDeltaZero.not⟩
  rintro (h | h)
  assumption

theorem IsDeltaZero.sup (hφ : φ.IsDeltaZero) (hψ : ψ.IsDeltaZero) : (φ ⊔ ψ).IsDeltaZero :=
  hφ.not.imp hψ

theorem IsDeltaZero.inf (hφ : φ.IsDeltaZero) (hψ : ψ.IsDeltaZero) : (φ ⊓ ψ).IsDeltaZero :=
  hφ.imp hψ.not |>.not

theorem IsDeltaZero.iff (hφ : φ.IsDeltaZero) (hψ : ψ.IsDeltaZero) : (φ ⇔ ψ).IsDeltaZero :=
  (hφ.imp hψ).inf (hψ.imp hφ)

@[simp]
theorem pi_zero_iff_deltaZero : φ.IsPi 0 ↔ φ.IsDeltaZero := by grind [IsPi]

@[simp]
theorem sigma_zero_iff_deltaZero : φ.IsSigma 0 ↔ φ.IsDeltaZero := by grind [IsSigma]

theorem IsPi.ex' {φ : L.BoundedFormula α (n + m)} (h : φ.IsPi k) :
    (φ.ex' m).IsSigma (k + 1) := IsSigma.succ m h

theorem IsPi.ex {φ : L.BoundedFormula α (n + 1)} (h : φ.IsPi k) :
    (∃' φ).IsSigma (k + 1) := IsSigma.succ 1 h

theorem IsPi.isSigma_succ (h : φ.IsPi k) : φ.IsSigma (k + 1) := IsSigma.succ 0 h

theorem IsSigma.all' {φ : L.BoundedFormula α (n + m)} (h : φ.IsSigma k) :
    (φ.all' m).IsPi (k + 1) := IsPi.succ m h

theorem IsSigma.all {φ : L.BoundedFormula α (n + 1)} (h : φ.IsSigma k) :
    (∀' φ).IsPi (k + 1) := IsPi.succ 1 h

theorem IsSigma.isPi_succ (h : φ.IsSigma k) : φ.IsPi (k + 1) := IsPi.succ 0 h

theorem IsPi.exists_Sigma_all' (h : φ.IsPi (k + 1)) :
    ∃ (m : ℕ), ∃ ψ : L.BoundedFormula α (n + m), ψ.IsSigma k ∧ φ = ψ.all' m := by
  cases h with | succ m hψ
  exact ⟨m, _, hψ, rfl⟩

theorem IsSigma.exists_Pi_ex' (h : φ.IsSigma (k + 1)) :
    ∃ (m : ℕ), ∃ ψ : L.BoundedFormula α (n + m), ψ.IsPi k ∧ φ = ψ.ex' m := by
  cases h with | succ m hψ
  exact ⟨m, _, hψ, rfl⟩

theorem IsDeltaZero.cast (h : φ.IsDeltaZero) (h' : n = n') : (φ.cast h').IsDeltaZero := by
  revert n'
  induction h with
  | falsum => exact fun _ ↦ IsDeltaZero.falsum
  | equal => exact fun _ ↦ IsDeltaZero.equal _ _
  | rel => exact fun _ ↦ IsDeltaZero.rel _ _
  | imp h₁ h₂ ih₁ ih₂ =>
    simp only [BoundedFormula.cast, castLE]
    exact fun h' ↦ IsDeltaZero.imp (ih₁ h') (ih₂ h')
  | bddAll t hψ ih =>
    intro n' h'
    simp only [BoundedFormula.cast, castLE, Function.comp_apply, Term.castSucc, Nat.succ_eq_add_one,
      castLE_mem_boundedFormula, Term.castLE_var_inr, Term.castLE_castLE]
    convert IsDeltaZero.bddAll (t.cast h') (ih (by rw [h']))
    · grind
    · simp

mutual
theorem IsPi.cast {k n n' : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsPi k) (h' : n = n') :
    (φ.cast h').IsPi k :=
  match k with
  | 0 => by
    simp only [pi_zero_iff_deltaZero] at h ⊢
    exact h.cast h'
  | k + 1 => by
    obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Sigma_all'
    simp only [cast, hψ₂, castLE_all'_eq_all'_cast]
    exact hψ₁.cast (h' ▸ rfl) |>.all'

theorem IsSigma.cast {k n n' : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsSigma k) (h' : n = n') :
    (φ.cast h').IsSigma k :=
  match k with
  | 0 => by
    simp only [sigma_zero_iff_deltaZero] at h ⊢
    exact h.cast h'
  | k + 1 => by
    obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Pi_ex'
    simp only [cast, hψ₂, castLE_ex'_eq_ex'_cast]
    exact hψ₁.cast (h' ▸ rfl) |>.ex'
end

theorem IsDeltaZero.liftAt {n n' p : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsDeltaZero)
    (hpn : p ≤ n) : (φ.liftAt n' p).IsDeltaZero := by
  revert n'
  induction h with
  | falsum => exact IsDeltaZero.falsum
  | equal => exact IsDeltaZero.equal _ _
  | rel => exact IsDeltaZero.rel _ _
  | imp h₁ h₂ ih₁ ih₂ =>
    simp only [liftAt_imp]
    exact IsDeltaZero.imp (ih₁ hpn) (ih₂ hpn)
  | @bddAll n ψ t hψ ih =>
    intro n'
    simp only [Function.comp_apply, Term.castSucc, Nat.succ_eq_add_one, liftAt_all,
      BoundedFormula.cast, liftAt_imp, liftAt_mem_boundedFormula, Term.liftAt_var_inr, Fin.val_last,
      Fin.addNat_last, castLE_imp, castLE_mem_boundedFormula, Term.castLE_var_inr]
    convert IsDeltaZero.bddAll (t.liftAt n' p) ((ih (n' := n') (by omega)).cast (by omega))
    · grind [Term.var.injEq, Sum.inr.injEq]
    · simp only [Term.castLE, Term.liftAt, Term.relabel_relabel, Sum.map_comp_map,
        Term.castSucc]
      congr 1
      simp only [Sum.map]
      congr 2
      grind

mutual
theorem IsPi.liftAt {k n n' p : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsPi k) (hpn : p ≤ n) :
    (φ.liftAt n' p).IsPi k :=
  match k with
  | 0 => by
    simp only [pi_zero_iff_deltaZero] at h ⊢
    exact h.liftAt hpn
  | k + 1 => by
    obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Sigma_all'
    simp only [hψ₂, liftAt_all'_eq_all'_cast_liftAt]
    exact hψ₁.liftAt (by omega) |>.cast (by omega) |>.all'

theorem IsSigma.liftAt {k n n' p : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsSigma k) (hpn : p ≤ n) :
    (φ.liftAt n' p).IsSigma k :=
  match k with
  | 0 => by
    simp only [sigma_zero_iff_deltaZero] at h ⊢
    exact h.liftAt hpn
  | k + 1 => by
    obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Pi_ex'
    simp only [hψ₂, liftAt_ex'_eq_ex'_cast_liftAt, cast]
    exact hψ₁.liftAt (by omega) |>.cast (by omega) |>.ex'
end

theorem IsPi.all' {φ : L.BoundedFormula α (n + m)} (h : φ.IsPi (k + 1)) :
    (φ.all' m).IsPi (k + 1) := by
  obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Sigma_all'
  rw [hψ₂, ψ.all'_all'_eq_all'_cast]
  exact (hψ₁.cast _).all'

theorem IsPi.all {φ : L.BoundedFormula α (n + 1)} (h : φ.IsPi (k + 1)) :
    φ.all.IsPi (k + 1) := h.all'

theorem IsSigma.ex' {φ : L.BoundedFormula α (n + m)} (h : φ.IsSigma (k + 1)) :
    (φ.ex' m).IsSigma (k + 1) := by
  obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Pi_ex'
  rw [hψ₂, ψ.ex'_ex'_eq_ex'_cast]
  exact (hψ₁.cast _).ex'

theorem IsSigma.ex {φ : L.BoundedFormula α (n + 1)} (h : φ.IsSigma (k + 1)) :
    φ.ex.IsSigma (k + 1) := h.ex'

mutual
theorem IsPi.isPi_succ {k n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsPi k) :
    φ.IsPi (k + 1) :=
  match k with
  | 0 => IsSigma.isPi_succ (by simpa using h)
  | k + 1 => by
    obtain ⟨_, _, hψ, _⟩ := h.exists_Sigma_all'
    convert hψ.isSigma_succ.all'

theorem IsSigma.isSigma_succ {k n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsSigma k) :
    φ.IsSigma (k + 1) :=
  match k with
  | 0 => IsPi.isSigma_succ (by simpa using h)
  | k + 1 => by
    obtain ⟨_, _, hψ, _⟩ := h.exists_Pi_ex'
    convert hψ.isPi_succ.ex'
end

variable {m : ℕ}
variable {φ : L.BoundedFormula α n}

theorem IsPi.Pi_of_le (h : φ.IsPi k) (hkm : k ≤ m) : φ.IsPi m := by
  induction m with
  | zero => grind
  | succ m ih =>
    rcases lt_or_eq_of_le hkm with hkm | rfl
    · exact ih (Nat.le_of_lt_succ hkm) |>.isPi_succ
    · exact h

theorem IsSigma.Sigma_of_le (h : φ.IsSigma k) (hkm : k ≤ m) : φ.IsSigma m := by
  induction m with
  | zero => convert h; omega
  | succ m ih =>
    rcases lt_or_eq_of_le hkm with hkm | rfl
    · exact ih (Nat.le_of_lt_succ hkm) |>.isSigma_succ
    · exact h

theorem IsPi.Sigma_of_lt (h : φ.IsPi k) (hkm : k < m) : φ.IsSigma m :=
  h.isSigma_succ.Sigma_of_le (Nat.add_one_le_of_lt hkm)

theorem IsSigma.Pi_of_lt (h : φ.IsSigma k) (hkm : k < m) : φ.IsPi m :=
  h.isPi_succ.Pi_of_le (Nat.add_one_le_of_lt hkm)


class DeltaZero (φ : L.BoundedFormula α n) : Prop where
  isDeltaZero : φ.IsDeltaZero

instance : (falsum : L.BoundedFormula α n).DeltaZero := ⟨IsDeltaZero.falsum⟩

instance : (⊥ : L.BoundedFormula α n).DeltaZero := ⟨IsDeltaZero.falsum⟩

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁ =' t₂).DeltaZero := ⟨IsDeltaZero.equal _ _⟩

instance {n : ℕ} {l : ℕ} (R : L.Relations l)
  (ts : Fin l → L.Term (α ⊕ Fin n)) :
  (rel R ts).DeltaZero := ⟨IsDeltaZero.rel _ _⟩

instance (t₁ t₂ : L.Term (α ⊕ Fin n)) :
  (t₁ ∈' t₂).DeltaZero := ⟨IsDeltaZero.rel _ _⟩

instance [hφ : φ.DeltaZero] [hψ : ψ.DeltaZero] : (φ ⟹ ψ).DeltaZero :=
  ⟨hφ.isDeltaZero.imp hψ.isDeltaZero⟩

instance {n : ℕ} {φ : L.BoundedFormula α (n + 1)} [hφ : φ.DeltaZero]
  (t : L.Term (α ⊕ Fin n)) : (∀' (&-1 ∈' t.castSucc ⟹ φ)).DeltaZero := ⟨hφ.isDeltaZero.bddAll t⟩

instance {n : ℕ} {φ : L.BoundedFormula α (n + 1)} [hφ : φ.DeltaZero]
  (t : L.Term (α ⊕ Fin n)) : (∀'∈ t φ).DeltaZero := by
  infer_instance

instance [hφ : φ.DeltaZero] : (∼φ).DeltaZero := ⟨hφ.isDeltaZero.not⟩

instance [hφ : φ.DeltaZero] [hψ : ψ.DeltaZero] : (φ ⊔ ψ).DeltaZero :=
  ⟨hφ.isDeltaZero.not.imp hψ.isDeltaZero⟩

instance [hφ : φ.DeltaZero] [hψ : ψ.DeltaZero] : (φ ⊓ ψ).DeltaZero :=
  ⟨hφ.isDeltaZero.imp hψ.isDeltaZero.not |>.not⟩

instance [hφ : φ.DeltaZero] [hψ : ψ.DeltaZero] : (φ ⇔ ψ).DeltaZero :=
  ⟨(hφ.isDeltaZero.imp hψ.isDeltaZero).inf (hψ.isDeltaZero.imp hφ.isDeltaZero)⟩

instance {n : ℕ} {φ : L.BoundedFormula α (n + 1)} [hφ : φ.DeltaZero]
  (t : L.Term (α ⊕ Fin n)) : (∃'∈ t φ).DeltaZero := by
  infer_instance

class Pi (k : ℕ) (φ : L.BoundedFormula α n) : Prop where
  isPi : φ.IsPi k

class Sigma (k : ℕ) (φ : L.BoundedFormula α n) : Prop where
  isSigma : φ.IsSigma k

instance [hφ : φ.DeltaZero] : φ.Pi 0 := ⟨by simpa using hφ.isDeltaZero⟩

instance [hφ : φ.DeltaZero] : φ.Sigma 0 := ⟨by simpa using hφ.isDeltaZero⟩

instance {φ : L.BoundedFormula α (n + m)} [hφ : φ.Pi k] :
  (φ.ex' m).Sigma (k + 1) := ⟨by simpa using hφ.isPi.ex'⟩

instance {φ : L.BoundedFormula α (n + 1)} [hφ : φ.Pi k] :
  φ.ex.Sigma (k + 1) := ⟨by simpa using hφ.isPi.ex⟩

instance {φ : L.BoundedFormula α (n + 1)} [hφ : φ.Pi k] :
  φ.Sigma (k + 1) := ⟨by simpa using hφ.isPi.isSigma_succ⟩

instance {φ : L.BoundedFormula α (n + m)} [hφ : φ.Sigma k] :
  (φ.all' m).Pi (k + 1) := ⟨by simpa using hφ.isSigma.all'⟩

instance {φ : L.BoundedFormula α (n + 1)} [hφ : φ.Sigma k] :
  φ.all.Pi (k + 1) := ⟨by simpa using hφ.isSigma.all⟩

instance {φ : L.BoundedFormula α (n + 1)} [hφ : φ.Sigma k] :
  φ.Pi (k + 1) := ⟨by simpa using hφ.isSigma.isPi_succ⟩

instance [h : φ.DeltaZero] (h' : n = n') : (φ.cast h').DeltaZero := ⟨h.isDeltaZero.cast h'⟩

instance {k n n' : ℕ} {φ : L.BoundedFormula α n} [h : φ.Pi k] (h' : n = n') :
    (φ.cast h').Pi k := ⟨h.isPi.cast h'⟩

instance {k n n' : ℕ} {φ : L.BoundedFormula α n} [h : φ.Sigma k] (h' : n = n') :
    (φ.cast h').Sigma k := ⟨h.isSigma.cast h'⟩

instance {n n' p : ℕ} {φ : L.BoundedFormula α n} [h : φ.DeltaZero]
    (hpn : p ≤ n) : (φ.liftAt n' p).DeltaZero := ⟨h.isDeltaZero.liftAt hpn⟩

instance {k n n' p : ℕ} {φ : L.BoundedFormula α n} [h : φ.Pi k]
    (hpn : p ≤ n) : (φ.liftAt n' p).Pi k := ⟨h.isPi.liftAt hpn⟩

instance {k n n' p : ℕ} {φ : L.BoundedFormula α n} [h : φ.Sigma k]
    (hpn : p ≤ n) : (φ.liftAt n' p).Sigma k := ⟨h.isSigma.liftAt hpn⟩

instance {φ : L.BoundedFormula α (n + m)} [h : φ.Pi (k + 1)] :
    (φ.all' m).Pi (k + 1) := ⟨h.isPi.all'⟩

instance {φ : L.BoundedFormula α (n + 1)} [h : φ.Pi (k + 1)] :
    φ.all.Pi (k + 1) := ⟨h.isPi.all⟩

instance {φ : L.BoundedFormula α (n + m)} [h : φ.Sigma (k + 1)] :
    (φ.ex' m).Sigma (k + 1) := ⟨h.isSigma.ex'⟩

instance {φ : L.BoundedFormula α (n + 1)} [h : φ.Sigma (k + 1)] :
    φ.ex.Sigma (k + 1) := ⟨h.isSigma.ex⟩

instance {k n : ℕ} {φ : L.BoundedFormula α n} [h : φ.Pi k] :
    φ.Pi (k + 1) := ⟨h.isPi.isPi_succ⟩

instance {k n : ℕ} {φ : L.BoundedFormula α n} [h : φ.Sigma k] :
    φ.Sigma (k + 1) := ⟨h.isSigma.isSigma_succ⟩

end SyntacticalLevyHierarchy


section LogicalLevyHierarchy

variable {k n : ℕ} {φ ψ : L.BoundedFormula α n}

/-- `φ` is `T`-logically `Π n` means that `φ` is `T`-equivalent to a `Π n` formula -/
def IsLogicalPi (k : ℕ) {n : ℕ} (φ : L.BoundedFormula α n) (T : L.Theory) : Prop :=
  ∃ ψ : L.BoundedFormula α n, (ψ.IsPi k ∧ T ⊨ᵇ φ ⇔ ψ)

/-- `φ` is `T`-logically `Σ n` means that `φ` is `T`-equivalent to a `Σ n` formula -/
def IsLogicalSigma (k : ℕ) {n : ℕ} (φ : L.BoundedFormula α n) (T : L.Theory) : Prop :=
  ∃ ψ : L.BoundedFormula α n, (ψ.IsSigma k ∧ T ⊨ᵇ φ ⇔ ψ)

/-- `φ` is `T`-logically `Δ n` means that `φ` is `T`-logically `Π n` and `T`-logically `Σ n` -/
def IsLogicalDelta (k : ℕ) {n : ℕ} (φ : L.BoundedFormula α n) (T : L.Theory) : Prop :=
  φ.IsLogicalPi k T ∧ φ.IsLogicalSigma k T

variable {T : L.Theory}

theorem IsPi.isLogicalPi (h : φ.IsPi k) : φ.IsLogicalPi k T :=
  ⟨φ, h, by simp [ModelsBoundedFormula]⟩

theorem IsSigma.isLogicalSigma (h : φ.IsSigma k) : φ.IsLogicalSigma k T :=
  ⟨φ, h, by simp [ModelsBoundedFormula]⟩

theorem IsDeltaZero.isLogicalDelta (h : φ.IsDeltaZero) : φ.IsLogicalDelta 0 T := by
  constructor
  · apply IsPi.isLogicalPi; simpa
  · apply IsSigma.isLogicalSigma; simpa

@[simp]
theorem LogicalPi_zero_iff_isLogicalDelta_zero : φ.IsLogicalPi 0 T ↔ φ.IsLogicalDelta 0 T :=
  ⟨fun ⟨ψ, hψ⟩ ↦ ⟨⟨ψ, hψ⟩, ⟨ψ, by simpa using hψ⟩⟩, fun h ↦ h.left⟩

@[simp]
theorem LogicalSigma_zero_iff_logicalDelta_zero :
    φ.IsLogicalSigma 0 T ↔ φ.IsLogicalDelta 0 T :=
  ⟨fun ⟨ψ, hψ⟩ ↦ ⟨⟨ψ, by simpa using hψ⟩, ⟨ψ, hψ⟩⟩, fun h ↦ h.right⟩

theorem IsLogicalDelta.isLogicalPi (h : φ.IsLogicalDelta k T) : φ.IsLogicalPi k T := h.left

theorem IsLogicalDelta.isLogicalSigma (h : φ.IsLogicalDelta k T) : φ.IsLogicalSigma k T := h.right

/- logical quantifiers -/

variable {φ : L.BoundedFormula α (n + m)}

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

theorem IsLogicalDelta.all' (h : φ.IsLogicalDelta (k + 1) T) : (φ.all' m).IsLogicalPi (k + 1) T :=
  h.left.all'

theorem IsLogicalDelta.all'₀ (h : φ.IsLogicalDelta k T) (hk : k ≠ 0) :
    (φ.all' m).IsLogicalPi k T :=
  h.left.all'₀ hk

theorem IsLogicalDelta.ex' (h : φ.IsLogicalDelta (k + 1) T) : (φ.ex' m).IsLogicalSigma (k + 1) T :=
  h.right.ex'

theorem IsLogicalDelta.ex'₀ (h : φ.IsLogicalDelta k T) (hk : k ≠ 0) :
    (φ.ex' m).IsLogicalSigma k T :=
  h.right.ex'₀ hk


/- invariance under `T`-logical equivalence -/

variable {φ ψ : L.BoundedFormula α n}

theorem IsLogicalPi.of_models_iff (h : φ.IsLogicalPi k T) (h' : T ⊨ᵇ φ ⇔ ψ) :
    ψ.IsLogicalPi k T := by
  obtain ⟨θ, hθ₁, hθ₂⟩ := h
  exact ⟨θ, hθ₁, h'.of_imp_imp hθ₂ (by simp +contextual [ModelsBoundedFormula])⟩

theorem IsLogicalSigma.of_models_iff (h : φ.IsLogicalSigma k T) (h' : T ⊨ᵇ φ ⇔ ψ) :
    ψ.IsLogicalSigma k T := by
  obtain ⟨θ, hθ₁, hθ₂⟩ := h
  exact ⟨θ, hθ₁, h'.of_imp_imp hθ₂ (by simp +contextual [ModelsBoundedFormula])⟩

theorem IsLogicalDelta.of_models_iff (h : φ.IsLogicalDelta k T) (h' : T ⊨ᵇ φ ⇔ ψ) :
    ψ.IsLogicalDelta k T :=
  ⟨h.left.of_models_iff h', h.right.of_models_iff h'⟩

/- logical connectives -/

mutual
theorem IsLogicalPi.not {k n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsLogicalPi k T) :
    (∼φ).IsLogicalSigma k T :=
  let ⟨ψ, hψ₁, hψ₂⟩ := h
  match k with
  | 0 => ⟨∼ψ, by simpa using hψ₁, hψ₂.of_imp (by simp +contextual [ModelsBoundedFormula])⟩
  | k + 1 => let ⟨m, θ, hθ₁, hθ₂⟩ := hψ₁.exists_Sigma_all'
    hθ₁.isLogicalSigma.not.ex'.of_models_iff <|
      (hθ₂ ▸ hψ₂).of_imp (by simp +contextual [ModelsBoundedFormula])

theorem IsLogicalSigma.not {k n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsLogicalSigma k T) :
    (∼φ).IsLogicalPi k T :=
  let ⟨ψ, hψ₁, hψ₂⟩ := h
  match k with
  | 0 => ⟨∼ψ, by simpa using hψ₁, hψ₂.of_imp (by simp +contextual [ModelsBoundedFormula])⟩
  | k + 1 => let ⟨m, θ, hθ₁, hθ₂⟩ := hψ₁.exists_Pi_ex'
    hθ₁.isLogicalPi.not.all'.of_models_iff <|
      (hθ₂ ▸ hψ₂).of_imp (by simp +contextual [ModelsBoundedFormula])
end

theorem IsLogicalDelta.not (h : φ.IsLogicalDelta k T) : (∼φ).IsLogicalDelta k T :=
  ⟨h.right.not, h.left.not⟩

@[simp]
theorem LogicalPi_not_iff : (∼φ).IsLogicalPi k T ↔ φ.IsLogicalSigma k T := by
  refine ⟨fun h ↦ h.not.of_models_iff ?_, IsLogicalSigma.not⟩
  simp +contextual [ModelsBoundedFormula]

@[simp]
theorem LogicalSigma_not_iff : (∼φ).IsLogicalSigma k T ↔ φ.IsLogicalPi k T := by
  refine ⟨fun h ↦ h.not.of_models_iff ?_, IsLogicalPi.not⟩
  simp +contextual [ModelsBoundedFormula]

@[simp]
theorem LogicalDelta_not_iff : (∼φ).IsLogicalDelta k T ↔ φ.IsLogicalDelta k T := by
  refine ⟨fun h ↦ h.not.of_models_iff ?_, IsLogicalDelta.not⟩
  simp +contextual [ModelsBoundedFormula]

mutual
theorem IsLogicalPi.imp {k n : ℕ} {φ ψ : L.BoundedFormula α n}
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
    let θ := (φ''.liftAt q (n + p)).cast (Nat.add_assoc _ _ _) ⟹
      (ψ''.liftAt p n).cast (by rw [Nat.add_assoc, add_comm q]) |>.ex' (p + q)
    have : θ.IsLogicalSigma (k + 1) T :=
      ((hφ''₁.liftAt (by omega)).cast _).isLogicalSigma.imp
        ((hψ''₁.liftAt (by omega)).cast _).isLogicalPi |>.ex'
    refine this.of_models_iff (fun M v xs ↦ ?_)
    specialize hφ₂ M v xs
    specialize hψ₂ M v xs
    have := realize_imp_all'_ex' (M := M) (θ := φ'') (ψ := ψ'') (xs := xs) (v := v)
    simp_all only [cast, realize_ex', realize_imp, realize_all', realize_iff]
    convert this
    simp [θ]

theorem IsLogicalSigma.imp {k n : ℕ} {φ ψ : L.BoundedFormula α n}
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
    let θ := (φ''.liftAt q (n + p)).cast (Nat.add_assoc _ _ _) ⟹
      (ψ''.liftAt p n).cast (by rw [Nat.add_assoc, add_comm q]) |>.all' (p + q)
    have : θ.IsLogicalPi (k + 1) T :=
      ((hφ''₁.liftAt (by omega)).cast _).isLogicalPi.imp
        ((hψ''₁.liftAt (by omega)).cast _).isLogicalSigma |>.all'
    refine this.of_models_iff (fun M v xs ↦ ?_)
    specialize hφ₂ M v xs
    specialize hψ₂ M v xs
    have := realize_imp_ex'_all' (M := M) (θ := φ'') (ψ := ψ'') (xs := xs) (v := v)
    simp_all only [cast, realize_ex', realize_imp, realize_all', realize_iff]
    convert this
    simp [θ]
end

theorem IsLogicalDelta.imp {k n : ℕ} {φ ψ : L.BoundedFormula α n}
    (hφ : φ.IsLogicalDelta k T) (hψ : ψ.IsLogicalDelta k T) : (φ ⟹ ψ).IsLogicalDelta k T :=
  ⟨hφ.right.imp hψ.left, hφ.left.imp hψ.right⟩

theorem IsLogicalPi.sup (hφ : φ.IsLogicalPi k T) (hψ : ψ.IsLogicalPi k T) :
    (φ ⊔ ψ).IsLogicalPi k T := hφ.not.imp hψ

theorem IsLogicalPi.inf (hφ : φ.IsLogicalPi k T) (hψ : ψ.IsLogicalPi k T) :
    (φ ⊓ ψ).IsLogicalPi k T := hφ.imp hψ.not |>.not

theorem IsLogicalSigma.sup (hφ : φ.IsLogicalSigma k T) (hψ : ψ.IsLogicalSigma k T) :
    (φ ⊔ ψ).IsLogicalSigma k T := hφ.not.imp hψ

theorem IsLogicalSigma.inf (hφ : φ.IsLogicalSigma k T) (hψ : ψ.IsLogicalSigma k T) :
    (φ ⊓ ψ).IsLogicalSigma k T := hφ.imp hψ.not |>.not

theorem IsLogicalDelta.sup (hφ : φ.IsLogicalDelta k T) (hψ : ψ.IsLogicalDelta k T) :
    (φ ⊔ ψ).IsLogicalDelta k T := hφ.not.imp hψ

theorem IsLogicalDelta.inf (hφ : φ.IsLogicalDelta k T) (hψ : ψ.IsLogicalDelta k T) :
    (φ ⊓ ψ).IsLogicalDelta k T := hφ.imp hψ.not |>.not

theorem IsLogicalDelta.iff (hφ : φ.IsLogicalDelta k T) (hψ : ψ.IsLogicalDelta k T) :
    (φ ⇔ ψ).IsLogicalDelta k T := (hφ.imp hψ).inf (hψ.imp hφ)

/- lower levels are included in upper levels -/

theorem IsLogicalPi.isLogicalPi_of_le (h : φ.IsLogicalPi k T) (hkm : k ≤ m) :
    φ.IsLogicalPi m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.Pi_of_le hkm

theorem IsLogicalSigma.isLogicalSigma_of_le (h : φ.IsLogicalSigma k T) (hkm : k ≤ m) :
    φ.IsLogicalSigma m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.Sigma_of_le hkm

theorem IsLogicalDelta.isLogicalDelta_of_le (h : φ.IsLogicalDelta k T) (hkm : k ≤ m) :
    φ.IsLogicalDelta m T :=
  ⟨h.left.isLogicalPi_of_le hkm, h.right.isLogicalSigma_of_le hkm⟩

theorem IsLogicalPi.isLogicalSigma_of_lt (h : φ.IsLogicalPi k T) (hkm : k < m) :
    φ.IsLogicalSigma m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.Sigma_of_lt hkm

theorem IsLogicalSigma.isLogicalPi_of_lt (h : φ.IsLogicalSigma k T) (hkm : k < m) :
    φ.IsLogicalPi m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.Pi_of_lt hkm

theorem IsLogicalPi.isLogicalDelta_of_lt (h : φ.IsLogicalPi k T) (hkm : k < m) :
    φ.IsLogicalDelta m T :=
  ⟨h.isLogicalPi_of_le hkm.le, h.isLogicalSigma_of_lt hkm⟩

theorem IsLogicalSigma.isLogicalDelta_of_lt (h : φ.IsLogicalSigma k T) (hkm : k < m) :
    φ.IsLogicalDelta m T :=
  ⟨h.isLogicalPi_of_lt hkm, h.isLogicalSigma_of_le hkm.le⟩


/- monotone in the theory -/

variable {T' : L.Theory}

theorem IsLogicalPi.mono (h : φ.IsLogicalPi k T) (h' : T ⊆ T') : φ.IsLogicalPi k T' := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  exact ⟨ψ, hψ₁, hψ₂.mono h'⟩

theorem IsLogicalSigma.mono (h : φ.IsLogicalSigma k T) (h' : T ⊆ T') : φ.IsLogicalSigma k T' := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  exact ⟨ψ, hψ₁, hψ₂.mono h'⟩

theorem IsLogicalDelta.mono (h : φ.IsLogicalDelta k T) (h' : T ⊆ T') : φ.IsLogicalDelta k T' := by
  obtain ⟨hψ₁, hψ₂⟩ := h
  exact ⟨hψ₁.mono h', hψ₂.mono h'⟩

class LogicalPi (k : ℕ) {n : ℕ} (φ : L.BoundedFormula α n) (T : L.Theory) : Prop where
  isLogicalPi : φ.IsLogicalPi k T

class LogicalSigma (k : ℕ) {n : ℕ} (φ : L.BoundedFormula α n) (T : L.Theory) : Prop where
  isLogicalSigma : φ.IsLogicalSigma k T

class LogicalDelta (k : ℕ) {n : ℕ} (φ : L.BoundedFormula α n) (T : L.Theory) : Prop extends
  φ.LogicalPi k T, φ.LogicalSigma k T

-- instance [φ.LogicalDelta k T] : φ.LogicalPi k T := by infer_instance
-- instance [φ.LogicalDelta k T] : φ.LogicalSigma k T := by infer_instance

instance [h : φ.Pi k] : φ.LogicalPi k T := ⟨h.isPi.isLogicalPi⟩

instance [h : φ.Sigma k] : φ.LogicalSigma k T := ⟨h.isSigma.isLogicalSigma⟩

instance [h : φ.DeltaZero] : φ.LogicalDelta 0 T where
  isLogicalPi := h.isDeltaZero.isLogicalDelta.left
  isLogicalSigma := h.isDeltaZero.isLogicalDelta.right

instance [h : φ.LogicalPi 0 T] : φ.LogicalDelta 0 T where
  isLogicalPi := h.isLogicalPi
  isLogicalSigma := by simpa using h.isLogicalPi

instance [h : φ.LogicalSigma 0 T] : φ.LogicalDelta 0 T where
  isLogicalPi := by simpa using h.isLogicalSigma
  isLogicalSigma := h.isLogicalSigma

variable {φ : L.BoundedFormula α (n + m)}

instance [h : φ.LogicalPi (k + 1) T] : (φ.all' m).LogicalPi (k + 1) T := ⟨h.isLogicalPi.all'⟩

instance [h : φ.LogicalPi k T] (hk : k ≠ 0) :
  (φ.all' m).LogicalPi k T := ⟨h.isLogicalPi.all'₀ hk⟩

instance [h : φ.LogicalPi k T] :
  (φ.ex' m).LogicalSigma (k + 1) T := ⟨h.isLogicalPi.ex'⟩

instance [h : φ.LogicalSigma (k + 1) T] :
  (φ.ex' m).LogicalSigma (k + 1) T := ⟨h.isLogicalSigma.ex'⟩

instance [h : φ.LogicalSigma k T] (hk : k ≠ 0) :
  (φ.ex' m).LogicalSigma k T := ⟨h.isLogicalSigma.ex'₀ hk⟩

instance [h : φ.LogicalSigma k T] :
  (φ.all' m).LogicalPi (k + 1) T := ⟨h.isLogicalSigma.all'⟩

instance {φ : L.BoundedFormula α n} [h : φ.LogicalPi k T] :
  (∼φ).LogicalSigma k T := ⟨h.isLogicalPi.not⟩

instance {φ : L.BoundedFormula α n} [h : φ.LogicalSigma k T] :
  (∼φ).LogicalPi k T := ⟨h.isLogicalSigma.not⟩

instance {φ : L.BoundedFormula α n} [h : φ.LogicalDelta k T] : (∼φ).LogicalDelta k T where
  isLogicalPi := h.isLogicalSigma.not
  isLogicalSigma := h.isLogicalPi.not

instance {φ ψ : L.BoundedFormula α n} [hφ : φ.LogicalPi k T] [hψ : ψ.LogicalSigma k T] :
  (φ ⟹ ψ).LogicalSigma k T := ⟨hφ.isLogicalPi.imp hψ.isLogicalSigma⟩

instance {φ ψ : L.BoundedFormula α n} [hφ : φ.LogicalSigma k T] [hψ : ψ.LogicalPi k T] :
  (φ ⟹ ψ).LogicalPi k T := ⟨hφ.isLogicalSigma.imp hψ.isLogicalPi⟩

instance {k n : ℕ} {φ ψ : L.BoundedFormula α n}
  [hφ : φ.LogicalDelta k T] [hψ : ψ.LogicalDelta k T] :
  (φ ⟹ ψ).LogicalDelta k T where
  isLogicalPi := hφ.isLogicalSigma.imp hψ.isLogicalPi
  isLogicalSigma := hφ.isLogicalPi.imp hψ.isLogicalSigma

instance {φ ψ : L.BoundedFormula α n}
  [hφ : φ.LogicalPi k T] [hψ : ψ.LogicalPi k T] :
  (φ ⊔ ψ).LogicalPi k T := ⟨hφ.isLogicalPi.sup hψ.isLogicalPi⟩

instance {φ ψ : L.BoundedFormula α n}
  [hφ : φ.LogicalPi k T] [hψ : ψ.LogicalPi k T] :
  (φ ⊓ ψ).LogicalPi k T := ⟨hφ.isLogicalPi.inf hψ.isLogicalPi⟩

instance {φ ψ : L.BoundedFormula α n}
  [hφ : φ.LogicalSigma k T] [hψ : ψ.LogicalSigma k T] :
  (φ ⊔ ψ).LogicalSigma k T := ⟨hφ.isLogicalSigma.sup hψ.isLogicalSigma⟩

instance {φ ψ : L.BoundedFormula α n}
  [hφ : φ.LogicalSigma k T] [hψ : ψ.LogicalSigma k T] :
  (φ ⊓ ψ).LogicalSigma k T := ⟨hφ.isLogicalSigma.inf hψ.isLogicalSigma⟩

instance {φ ψ : L.BoundedFormula α n}
  [hφ : φ.LogicalDelta k T] [hψ : ψ.LogicalDelta k T] :
  (φ ⊔ ψ).LogicalDelta k T where
  isLogicalPi := hφ.isLogicalPi.sup hψ.isLogicalPi
  isLogicalSigma := hφ.isLogicalSigma.sup hψ.isLogicalSigma

instance {φ ψ : L.BoundedFormula α n}
  [hφ : φ.LogicalDelta k T] [hψ : ψ.LogicalDelta k T] :
  (φ ⊓ ψ).LogicalDelta k T where
  isLogicalPi := hφ.isLogicalPi.inf hψ.isLogicalPi
  isLogicalSigma := hφ.isLogicalSigma.inf hψ.isLogicalSigma

instance {φ ψ : L.BoundedFormula α n}
  [hφ : φ.LogicalDelta k T] [hψ : ψ.LogicalDelta k T] :
  (φ ⇔ ψ).LogicalDelta k T where
  isLogicalPi :=
    (hφ.isLogicalSigma.imp hψ.isLogicalPi).inf (hψ.isLogicalSigma.imp hφ.isLogicalPi)
  isLogicalSigma :=
    (hφ.isLogicalPi.imp hψ.isLogicalSigma).inf (hψ.isLogicalPi.imp hφ.isLogicalSigma)


end LogicalLevyHierarchy

end BoundedFormula

end Language

end FirstOrder
