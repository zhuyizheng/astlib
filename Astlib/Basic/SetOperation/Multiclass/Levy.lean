/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Multiclass.Defs
/-!
file docstring
-/

open FirstOrder Language BoundedFormula Fin MemStructure

variable {L : Language.{u, v}} {M : Type max u v} [L.MemStructure M] {α : Type*}
  {n k l m : ℕ} {P : Set M}
  {A B : Multiclass M n}

namespace FirstOrder.Language.MemStructure

namespace Multiclass

section DeltaZero

def IsDeltaZero {n} (A : Multiclass M n) (P : Set M) :=
  ∃ m, ∃ φ : L.BoundedFormula' (n + m), ∃ _ : φ.DeltaZero, ∃ vs : Fin m → M,
    Set.range vs ⊆ P ∧ A = φ.multiclass.slice vs

class DeltaZero {n} (A : Multiclass M n) (P : Set M) : Prop where
  isDeltaZero : A.IsDeltaZero P

instance (φ : L.BoundedFormula' n) [φ.DeltaZero] : φ.multiclass.DeltaZero P :=
  ⟨⟨0, φ, by infer_instance, elim0, by simp, by simp⟩⟩

@[simp]
theorem isDeltaZero_top {n} : (⊤ : Multiclass M n).IsDeltaZero P :=
  ⟨0, ⊤, by infer_instance, Fin.elim0, by simp⟩

instance : (⊤ : Multiclass M n).DeltaZero P := ⟨isDeltaZero_top⟩

@[simp]
theorem isDeltaZero_bot {n} : (⊥ : Multiclass M n).IsDeltaZero P :=
  ⟨0, ⊥, by infer_instance, Fin.elim0, by simp⟩

instance : (⊥ : Multiclass M n).DeltaZero P := ⟨isDeltaZero_bot⟩

@[simp]
theorem IsDeltaZero.imp (hA : A.IsDeltaZero P) (hB : B.IsDeltaZero P) :
    (A ⟹ B).IsDeltaZero P := by
  obtain ⟨m, φ, hφ, ys, hys, rfl⟩ := hA
  obtain ⟨l, ψ, hψ, zs, hzs, rfl⟩ := hB
  exact ⟨m + l, (φ.splitImp ψ).castAssoc,
    by infer_instance, append ys zs, by simp [hys, hzs], by funext xs; simp⟩

instance [hA : A.DeltaZero P] [hB : B.DeltaZero P] : (A ⟹ B).DeltaZero P :=
  ⟨hA.isDeltaZero.imp hB.isDeltaZero⟩

@[simp]
theorem IsDeltaZero.not (hA : A.IsDeltaZero P) :
    (∼A).IsDeltaZero P :=
  not_eq (M := M) _ ▸ hA.imp isDeltaZero_bot

instance [hA : A.DeltaZero P] : (∼A).DeltaZero P :=
  ⟨hA.isDeltaZero.not⟩

@[simp]
theorem IsDeltaZero.sup (hA : A.IsDeltaZero P) (hB : B.IsDeltaZero P) :
    (A ⊔ B).IsDeltaZero P :=
  sup_eq (M := M) _ _ ▸ (hA.not).imp hB

instance [hA : A.DeltaZero P] [hB : B.DeltaZero P] : (A ⊔ B).DeltaZero P :=
  ⟨hA.isDeltaZero.sup hB.isDeltaZero⟩

@[simp]
theorem IsDeltaZero.inf (hA : A.IsDeltaZero P) (hB : B.IsDeltaZero P) :
    (A ⊓ B).IsDeltaZero P :=
  inf_eq (M := M) _ _ ▸ (hA.imp (hB.not)).not

variable [Finite β] {As : β → Multiclass M n}

@[simp]
theorem isDeltaZero_foldr_sup {L : List (Multiclass M n)} (hL : ∀ A ∈ L, A.IsDeltaZero P) :
    (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ L).IsDeltaZero P := by
  induction L with
  | nil => simp
  | cons A As ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    simp [hL, ih hL.right]

@[simp]
theorem isDeltaZero_iSup (hAs : ∀ i, (As i).IsDeltaZero P) :
    (iSup As).IsDeltaZero P := by
  grind [Multiclass.iSup, isDeltaZero_foldr_sup]

instance [hAs : ∀ i, (As i).DeltaZero P] : (iSup As).DeltaZero P :=
  ⟨isDeltaZero_iSup fun i ↦ (hAs i).isDeltaZero⟩

@[simp]
theorem isDeltaZero_foldr_inf {L : List (Multiclass M n)} (hL : ∀ A ∈ L, A.IsDeltaZero P) :
    (List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ L).IsDeltaZero P := by
  induction L with
  | nil => simp
  | cons A As ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    simp [hL, ih hL.right]

@[simp]
theorem isDeltaZero_iInf (hAs : ∀ i, (As i).IsDeltaZero P) :
    (iInf As).IsDeltaZero P := by
  grind [Multiclass.iInf, isDeltaZero_foldr_inf]

instance [hAs : ∀ i, (As i).DeltaZero P] : (iInf As).DeltaZero P :=
  ⟨isDeltaZero_iInf fun i ↦ (hAs i).isDeltaZero⟩

instance [hA : A.DeltaZero P] [hB : B.DeltaZero P] : (A ⊓ B).DeltaZero P :=
  ⟨hA.isDeltaZero.inf hB.isDeltaZero⟩

@[simp]
theorem IsDeltaZero.iff (hA : A.IsDeltaZero P) (hB : B.IsDeltaZero P) :
    (A ⇔ B).IsDeltaZero P :=
  iff_eq (M := M) _ _ ▸ (hA.imp hB).inf (hB.imp hA)

instance [hA : A.DeltaZero P] [hB : B.DeltaZero P] : (A ⇔ B).DeltaZero P :=
  ⟨hA.isDeltaZero.iff hB.isDeltaZero⟩

-- variable {A : Multiclass M (n + 1)}

theorem IsDeltaZero.slice {A : Multiclass M (n + l)}
    (hA : A.IsDeltaZero P) {us : Fin l → M} (hus : Set.range us ⊆ P) :
    (A.slice us).IsDeltaZero P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  exact ⟨l + m, φ.castAssoc, by infer_instance, append us vs,
    by simp [hus, hvs], by funext; simp⟩

instance (A : Multiclass M (n + m)) [hA : A.DeltaZero Set.univ] (us : Fin m → M) :
  A.slice us |>.DeltaZero Set.univ := ⟨hA.isDeltaZero.slice (by simp)⟩

instance (A : Multiclass M (n + 1)) [hA : A.DeltaZero Set.univ] (c : M) :
  A.slice₀ c |>.DeltaZero Set.univ := by
  unfold slice₀
  infer_instance

theorem IsDeltaZero.remap {A : Multiclass M n}
    (hA : A.IsDeltaZero P) (f : Fin n → Fin n') :
    (A.remap f).IsDeltaZero P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  refine ⟨m, φ.substBoundBound (append (castAdd m ∘ f) (natAdd n')), by infer_instance, vs,
    by simp [hvs], by funext; simp [← Function.comp_assoc]⟩

instance [hA : A.DeltaZero P] {f : Fin n → Fin n'} : (A.remap f).DeltaZero P :=
  ⟨hA.isDeltaZero.remap f⟩

variable (i j : Fin n)

lemma isDeltaZero_eq : (Eq (M := M) n i j).IsDeltaZero P :=
  ⟨0, &i =' &j, by infer_instance, elim0, by simp, by rw [multiclass_eq]; simp⟩

instance : (Eq (M := M) n i j).DeltaZero P := ⟨isDeltaZero_eq i j⟩

lemma isDeltaZero_mem : (Mem (M := M) n i j).IsDeltaZero P :=
  ⟨0, &i ∈' &j, by infer_instance, elim0, by simp, by rw [multiclass_mem]; simp⟩

instance : (Mem (M := M) n i j).DeltaZero P := ⟨isDeltaZero_mem i j⟩

lemma isDeltaZero_subset : (Subset (M := M) n i j).IsDeltaZero P :=
  ⟨0, &i ⊆' &j, by infer_instance, elim0, by simp, by rw [multiclass_subset]; simp⟩

instance : (Subset (M := M) n i j).DeltaZero P := ⟨isDeltaZero_subset i j⟩

end DeltaZero

section PiSigmaDelta

def IsPi {n} (k) (A : Multiclass M n) (P : Set M) :=
  ∃ m, ∃ φ : L.BoundedFormula' (n + m), ∃ _ : φ.Pi k, ∃ vs : Fin m → M,
    Set.range vs ⊆ P ∧ A = φ.multiclass.slice vs

def IsSigma {n} (k) (A : Multiclass M n) (P : Set M) :=
  ∃ m, ∃ φ : L.BoundedFormula' (n + m), ∃ _ : φ.Sigma k, ∃ vs : Fin m → M,
    Set.range vs ⊆ P ∧ A = φ.multiclass.slice vs

class Pi {n} (k) (A : Multiclass M n) (P : Set M) : Prop where
  isPi : A.IsPi k P

class Sigma {n} (k) (A : Multiclass M n) (P : Set M) : Prop where
  isSigma : A.IsSigma k P

class abbrev Delta {n} (k) (A : Multiclass M n) (P : Set M) : Prop := A.Pi k P, A.Sigma k P

variable {A : Multiclass M (n + l)}

theorem IsPi.all' (hA : A.IsPi (k + 1) P) :
    (A.all' l).IsPi (k + 1) P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  exact ⟨m, φ.castAssoc.switchBoundRight.castAssoc'.all' _, by infer_instance, vs, hvs,
    by funext; simp⟩

instance [hA : A.Pi (k + 1) P] : (A.all' _).Pi (k + 1) P := ⟨hA.isPi.all' ⟩

instance {A : Multiclass M (n + 1)} [hA : A.Pi (k + 1) P] : A.all.Pi (k + 1) P := ⟨hA.isPi.all'⟩

theorem IsSigma.ex' (hA : A.IsSigma (k + 1) P) :
    (A.ex' l).IsSigma (k + 1) P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  refine ⟨m, φ.castAssoc.switchBoundRight.castAssoc'.ex' _, by infer_instance, vs, hvs,
    by funext; simp⟩

instance [hA : A.Sigma (k + 1) P] : (A.ex').Sigma (k + 1) P := ⟨hA.isSigma.ex'⟩

instance {A : Multiclass M (n + 1)} [hA : A.Sigma (k + 1) P] : A.ex.Sigma (k + 1) P :=
  ⟨hA.isSigma.ex'⟩

variable {A : Multiclass M n}

theorem IsPi.isPi_of_le (hA : A.IsPi k P) (hkl : k ≤ l) :
    A.IsPi l P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  exact ⟨m, φ, ⟨hφ.isPi.isPi_of_le hkl⟩, vs, hvs, rfl⟩

theorem IsSigma.isSigma_of_le (hA : A.IsSigma k P) (hkl : k ≤ l) :
    A.IsSigma l P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  exact ⟨m, φ, ⟨hφ.isSigma.isSigma_of_le hkl⟩, vs, hvs, rfl⟩

theorem IsPi.isPi_succ (hA : A.IsPi k P) :
    A.IsPi (k + 1) P := hA.isPi_of_le (Nat.le_succ _)

instance [hA : A.Pi k P] : A.Pi (k + 1) P := ⟨hA.isPi.isPi_succ⟩

theorem IsSigma.isSigma_succ (hA : A.IsSigma k P) :
    A.IsSigma (k + 1) P := hA.isSigma_of_le (Nat.le_succ _)

instance [hA : A.Sigma k P] : A.Sigma (k + 1) P := ⟨hA.isSigma.isSigma_succ⟩

theorem IsPi.isSigma_succ (hA : A.IsPi k P) : A.IsSigma (k + 1) P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  exact ⟨m, φ, ⟨hφ.isPi.isSigma_succ⟩, vs, hvs, rfl⟩

instance [hA : A.Pi k P] : A.Sigma (k + 1) P := ⟨hA.isPi.isSigma_succ⟩

theorem IsSigma.isPi_succ (hA : A.IsSigma k P) : A.IsPi (k + 1) P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  exact ⟨m, φ, ⟨hφ.isSigma.isPi_succ⟩, vs, hvs, rfl⟩

instance [hA : A.Sigma k P] : A.Pi (k + 1) P := ⟨hA.isSigma.isPi_succ⟩

theorem IsPi.Sigma_of_lt (hA : A.IsPi k P) (hkl : k < l) : A.IsSigma l P :=
  hA.isSigma_succ.isSigma_of_le (Nat.add_one_le_of_lt hkl)

theorem IsSigma.Pi_of_lt (hA : A.IsSigma k P) (hkl : k < l) : A.IsPi l P :=
  hA.isPi_succ.isPi_of_le (Nat.add_one_le_of_lt hkl)

theorem DeltaZero.isPi [hA : A.DeltaZero P] : A.IsPi k P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  refine ⟨m, φ, by infer_instance, vs, hvs, rfl⟩

instance [hA : A.DeltaZero P] : A.Pi k P := ⟨hA.isPi⟩

theorem DeltaZero.isSigma [hA : A.DeltaZero P] : A.IsSigma k P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  refine ⟨m, φ, by infer_instance, vs, hvs, rfl⟩

instance [hA : A.DeltaZero P] : A.Sigma k P := ⟨hA.isSigma⟩

variable [Nonempty M]

theorem isPi_iff_isLogicalPi :
    A.IsPi k P ↔
      ∃ m, ∃ φ : L.BoundedFormula' (n + m), ∃ _ : φ.LogicalPi k ∅, ∃ vs : Fin m → M,
    Set.range vs ⊆ P ∧ A = φ.multiclass.slice vs := by
  simp only [IsPi, exists_prop]
  refine ⟨fun ⟨m, φ, _, hφ⟩ ↦ ⟨m, φ, by infer_instance, hφ⟩,
    fun ⟨m, φ, hφ, vs, hvs₁, hvs₂⟩ ↦ ?_⟩
  obtain ⟨ψ, hψ₁, hψ₂⟩ := hφ.isLogicalPi
  refine ⟨m, ψ, ⟨hψ₁⟩, vs, hvs₁, ?_⟩
  funext xs
  specialize hψ₂ ⟨M⟩ default (append xs vs)
  simp only [realize_iff] at hψ₂
  simp only [hvs₂, slice, multiclass, Realize', eq_iff_iff]
  convert hψ₂

theorem isSigma_iff_isLogicalSigma :
    A.IsSigma k P ↔
      ∃ m, ∃ φ : L.BoundedFormula' (n + m), ∃ _ : φ.LogicalSigma k ∅, ∃ vs : Fin m → M,
    Set.range vs ⊆ P ∧ A = φ.multiclass.slice vs := by
  simp only [IsSigma, exists_prop]
  refine ⟨fun ⟨m, φ, _, hφ⟩ ↦ ⟨m, φ, by infer_instance, hφ⟩,
    fun ⟨m, φ, hφ, vs, hvs₁, hvs₂⟩ ↦ ?_⟩
  obtain ⟨ψ, hψ₁, hψ₂⟩ := hφ.isLogicalSigma
  refine ⟨m, ψ, ⟨hψ₁⟩, vs, hvs₁, ?_⟩
  funext xs
  specialize hψ₂ ⟨M⟩ default (append xs vs)
  simp only [realize_iff] at hψ₂
  simp only [hvs₂, slice, multiclass, Realize', eq_iff_iff]
  convert hψ₂

theorem IsPi.not (hA : A.IsPi k P) : (∼A).IsSigma k P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  rw [isSigma_iff_isLogicalSigma]
  exact ⟨m, ∼φ, by infer_instance, vs, hvs, by simp⟩

instance [hA : A.Pi k P] : (∼A).Sigma k P := ⟨hA.isPi.not⟩

theorem IsSigma.not (hA : A.IsSigma k P) : (∼A).IsPi k P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  rw [isPi_iff_isLogicalPi]
  exact ⟨m, ∼φ, by infer_instance, vs, hvs, by simp⟩

instance [hA : A.Sigma k P] : (∼A).Pi k P := ⟨hA.isSigma.not⟩

theorem IsPi.imp (hA : A.IsPi k P) (hB : B.IsSigma k P) : (A ⟹ B).IsSigma k P := by
  obtain ⟨m, φ, hφ, ys, hys, rfl⟩ := hA
  obtain ⟨l, ψ, hψ, zs, hzs, rfl⟩ := hB
  rw [isSigma_iff_isLogicalSigma]
  refine ⟨m + l, (φ.splitImp ψ).castAssoc,
    by infer_instance, append ys zs, by simp [hys, hzs], by funext; simp⟩

instance [hA : A.Pi k P] [hB : B.Sigma k P] : (A ⟹ B).Sigma k P := ⟨hA.isPi.imp hB.isSigma⟩

theorem IsSigma.imp (hA : A.IsSigma k P) (hB : B.IsPi k P) : (A ⟹ B).IsPi k P := by
  obtain ⟨m, φ, hφ, ys, hys, rfl⟩ := hA
  obtain ⟨l, ψ, hψ, zs, hzs, rfl⟩ := hB
  rw [isPi_iff_isLogicalPi]
  refine ⟨m + l, (φ.splitImp ψ).castAssoc,
    by infer_instance, append ys zs, by simp [hys, hzs], by funext; simp⟩

instance [hA : A.Sigma k P] [hB : B.Pi k P] : (A ⟹ B).Pi k P := ⟨hA.isSigma.imp hB.isPi⟩

theorem IsPi.sup (hA : A.IsPi k P) (hB : B.IsPi k P) : (A ⊔ B).IsPi k P :=
  sup_eq (M := M) _ _ ▸ hA.not.imp hB

instance [hA : A.Pi k P] [hB : B.Pi k P] : (A ⊔ B).Pi k P := ⟨hA.isPi.sup hB.isPi⟩

theorem IsPi.inf (hA : A.IsPi k P) (hB : B.IsPi k P) : (A ⊓ B).IsPi k P :=
  inf_eq (M := M) _ _ ▸ (hA.imp hB.not).not

instance [hA : A.Pi k P] [hB : B.Pi k P] : (A ⊓ B).Pi k P := ⟨hA.isPi.inf hB.isPi⟩

theorem IsSigma.sup (hA : A.IsSigma k P) (hB : B.IsSigma k P) : (A ⊔ B).IsSigma k P :=
  sup_eq (M := M) _ _ ▸ hA.not.imp hB

instance [hA : A.Sigma k P] [hB : B.Sigma k P] : (A ⊔ B).Sigma k P := ⟨hA.isSigma.sup hB.isSigma⟩

theorem IsSigma.inf (hA : A.IsSigma k P) (hB : B.IsSigma k P) : (A ⊓ B).IsSigma k P :=
  inf_eq (M := M) _ _ ▸ (hA.imp hB.not).not

instance [hA : A.Sigma k P] [hB : B.Sigma k P] : (A ⊓ B).Sigma k P := ⟨hA.isSigma.inf hB.isSigma⟩

@[simp]
theorem isPi_foldr_sup {L : List (Multiclass M n)} (hL : ∀ A ∈ L, A.IsPi k P) :
    (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ L).IsPi k P := by
  induction L with
  | nil =>
    simp only [List.foldr_nil]
    grind [IsPi.isPi_of_le, DeltaZero.isPi]
  | cons A As ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    simp [hL, ih hL.right, IsPi.sup]

@[simp]
theorem isPi_iSup {As : Fin l → Multiclass M n} (hAs : ∀ i, (As i).IsPi k P) :
    (iSup As).IsPi k P := by
  grind [Multiclass.iSup, isPi_foldr_sup]

instance {As : Fin l → Multiclass M n} [hAs : ∀ i, (As i).Pi k P] :
    (iSup As).Pi k P :=
  ⟨isPi_iSup fun i ↦ (hAs i).isPi⟩

@[simp]
theorem isPi_foldr_inf {L : List (Multiclass M n)} (hL : ∀ A ∈ L, A.IsPi k P) :
    (List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ L).IsPi k P := by
  induction L with
  | nil =>
    simp only [List.foldr_nil]
    grind [IsPi.isPi_of_le, DeltaZero.isPi]
  | cons A As ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    simp [hL, ih hL.right, IsPi.inf]

@[simp]
theorem isPi_iInf {As : Fin l → Multiclass M n} (hAs : ∀ i, (As i).IsPi k P) :
    (iInf As).IsPi k P := by
  grind [Multiclass.iInf, isPi_foldr_inf]

instance {As : Fin l → Multiclass M n} [hAs : ∀ i, (As i).Pi k P] :
    (iInf As).Pi k P :=
  ⟨isPi_iInf fun i ↦ (hAs i).isPi⟩

@[simp]
theorem isSigma_foldr_sup {L : List (Multiclass M n)} (hL : ∀ A ∈ L, A.IsSigma k P) :
    (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ L).IsSigma k P := by
  induction L with
  | nil =>
    simp only [List.foldr_nil]
    grind [IsSigma.isSigma_of_le, DeltaZero.isSigma]
  | cons A As ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    simp [hL, ih hL.right, IsSigma.sup]

@[simp]
theorem isSigma_iSup {As : Fin l → Multiclass M n} (hAs : ∀ i, (As i).IsSigma k P) :
    (iSup As).IsSigma k P := by
  grind [Multiclass.iSup, isSigma_foldr_sup]

instance {As : Fin l → Multiclass M n} [hAs : ∀ i, (As i).Sigma k P] :
    (iSup As).Sigma k P :=
  ⟨isSigma_iSup fun i ↦ (hAs i).isSigma⟩

@[simp]
theorem isSigma_foldr_inf {L : List (Multiclass M n)} (hL : ∀ A ∈ L, A.IsSigma k P) :
    (List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ L).IsSigma k P := by
  induction L with
  | nil =>
    simp only [List.foldr_nil]
    grind [IsSigma.isSigma_of_le, DeltaZero.isSigma]
  | cons A As ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    simp [hL, ih hL.right, IsSigma.inf]

@[simp]
theorem isSigma_iInf {As : Fin l → Multiclass M n} (hAs : ∀ i, (As i).IsSigma k P) :
    (iInf As).IsSigma k P := by
  grind [Multiclass.iInf, isSigma_foldr_inf]

instance {As : Fin l → Multiclass M n} [hAs : ∀ i, (As i).Sigma k P] :
    (iInf As).Sigma k P :=
  ⟨isSigma_iInf fun i ↦ (hAs i).isSigma⟩




instance [hA : A.Delta k P] : (∼A).Delta k P where

instance [hA : A.Delta k P] [hB : B.Delta k P] : (A ⊓ B).Delta k P where

instance [hA : A.Delta k P] [hB : B.Delta k P] : (A ⊔ B).Delta k P where

instance [hA : A.Delta k P] [hB : B.Delta k P] : (A ⟹ B).Delta k P where

instance [hA : A.Delta k P] [hB : B.Delta k P] : (A ⇔ B).Delta k P where
  isPi := by rw [iff_eq]; apply Pi.isPi
  isSigma := by rw [iff_eq]; apply Sigma.isSigma

-- variable {c : M}

theorem IsPi.slice {A : Multiclass M (n + l)}
    (hA : A.IsPi k P) {us : Fin l → M} (hus : Set.range us ⊆ P) :
    (A.slice us).IsPi k P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  refine ⟨l + m, φ.castAssoc, by infer_instance, append us vs,
    by simp [hus, hvs], by funext; simp⟩

theorem IsSigma.slice {A : Multiclass M (n + l)}
    (hA : A.IsSigma k P) {us : Fin l → M} (hus : Set.range us ⊆ P) :
    (A.slice us).IsSigma k P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  refine ⟨l + m, φ.castAssoc, by infer_instance, append us vs,
    by simp [hus, hvs], by funext; simp⟩

instance {A : Multiclass M (n + l)} [hA : A.Pi k Set.univ] {us : Fin l → M} :
  (A.slice us).Pi k Set.univ :=
  ⟨hA.isPi.slice (by simp)⟩

instance {A : Multiclass M (n + l)} [hA : A.Sigma k Set.univ] {us : Fin l → M} :
  (A.slice us).Sigma k Set.univ :=
  ⟨hA.isSigma.slice (by simp)⟩

theorem IsPi.remap {A : Multiclass M n}
    (hA : A.IsPi k P) (f : Fin n → Fin n') :
    (A.remap f).IsPi k P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  refine ⟨m, φ.substBoundBound (append (castAdd m ∘ f) (natAdd n')), by infer_instance, vs,
    by simp [hvs], by funext; simp [← Function.comp_assoc]⟩

theorem IsSigma.remap {A : Multiclass M n}
    (hA : A.IsSigma k P) (f : Fin n → Fin n') :
    (A.remap f).IsSigma k P := by
  obtain ⟨m, φ, hφ, vs, hvs, rfl⟩ := hA
  refine ⟨m, φ.substBoundBound (append (castAdd m ∘ f) (natAdd n')), by infer_instance, vs,
    by simp [hvs], by funext; simp [← Function.comp_assoc]⟩

instance [hA : A.Pi k P] (f : Fin n → Fin n') : (A.remap f).Pi k P :=
  ⟨hA.isPi.remap f⟩

instance [hA : A.Sigma k P] (f : Fin n → Fin n') : (A.remap f).Sigma k P :=
  ⟨hA.isSigma.remap f⟩


end PiSigmaDelta

section Definable

def IsDefinable {n} (A : Multiclass M n) (P : Set M) :=
  ∃ m, ∃ φ : L.BoundedFormula' (n + m), ∃ vs : Fin m → M,
    Set.range vs ⊆ P ∧ A = φ.multiclass.slice vs

class Definable {n} (A : Multiclass M n) (P : Set M) : Prop where
  isDefinable : A.IsDefinable P

instance (φ : L.BoundedFormula' n) : φ.multiclass.Definable P :=
  ⟨⟨0, φ, elim0, by simp, by simp⟩⟩

theorem IsDeltaZero.isDefinable (hA : A.IsDeltaZero P) : A.IsDefinable P := by
  obtain ⟨m, φ, _, vs, hvs⟩ := hA
  exact ⟨m, φ, vs, hvs⟩

instance [hA : A.DeltaZero P] : A.Definable P := ⟨hA.isDeltaZero.isDefinable⟩

instance : (⊤ : Multiclass M n).Definable ∅ := by infer_instance

instance : (⊥ : Multiclass M n).Definable ∅ := by infer_instance

theorem IsDefinable.imp (hA : A.IsDefinable P) (hB : B.IsDefinable P) :
    (A ⟹ B).IsDefinable P := by
  obtain ⟨m, φ, ys, hys, rfl⟩ := hA
  obtain ⟨l, ψ, zs, hzs, rfl⟩ := hB
  refine ⟨m + l, (φ.splitImp ψ).castAssoc,
     append ys zs, by simp [hys, hzs], by funext; simp⟩

instance [hA : A.Definable P] [hB : B.Definable P] : (A ⟹ B).Definable P :=
  ⟨hA.isDefinable.imp hB.isDefinable⟩

theorem IsDefinable.not (hA : A.IsDefinable P) :
    (∼A).IsDefinable P :=
  not_eq (M := M) _ ▸ hA.imp isDeltaZero_bot.isDefinable

instance [hA : A.Definable P] : (∼A).Definable P :=
  ⟨hA.isDefinable.not⟩

theorem IsDefinable.sup (hA : A.IsDefinable P) (hB : B.IsDefinable P) :
    (A ⊔ B).IsDefinable P :=
  sup_eq (M := M) _ _ ▸ (hA.not).imp hB

instance [hA : A.Definable P] [hB : B.Definable P] : (A ⊔ B).Definable P :=
  ⟨hA.isDefinable.sup hB.isDefinable⟩

theorem IsDefinable.inf (hA : A.IsDefinable P) (hB : B.IsDefinable P) :
    (A ⊓ B).IsDefinable P :=
  inf_eq (M := M) _ _ ▸ (hA.imp (hB.not)).not

instance [hA : A.Definable P] [hB : B.Definable P] : (A ⊓ B).Definable P :=
  ⟨hA.isDefinable.inf hB.isDefinable⟩

theorem IsDefinable.iff (hA : A.IsDefinable P) (hB : B.IsDefinable P) :
    (A ⇔ B).IsDefinable P :=
  iff_eq (M := M) _ _ ▸ (hA.imp hB).inf (hB.imp hA)

instance [hA : A.Definable P] [hB : B.Definable P] : (A ⇔ B).Definable P :=
  ⟨hA.isDefinable.iff hB.isDefinable⟩

variable {A : Multiclass M (n + l)}

theorem IsDefinable.all' (hA : A.IsDefinable P) :
    (A.all' l).IsDefinable P := by
  obtain ⟨m, φ, vs, hvs, rfl⟩ := hA
  refine ⟨m, φ.castAssoc.switchBoundRight.castAssoc'.all' _, vs, hvs, by funext; simp⟩

instance [hA : A.Definable P] : (A.all' l).Definable P := ⟨hA.isDefinable.all'⟩

instance {A : Multiclass M (n + 1)} [hA : A.Definable P] : A.all.Definable P :=
  ⟨hA.isDefinable.all'⟩

theorem IsDefinable.ex' (hA : A.IsDefinable P) :
    (A.ex' l).IsDefinable P := by
  obtain ⟨m, φ, vs, hvs, rfl⟩ := hA
  refine ⟨m, φ.castAssoc.switchBoundRight.castAssoc'.ex' _, vs, hvs, by funext; simp⟩

instance [hA : A.Definable P] : (A.ex' l).Definable P := ⟨hA.isDefinable.ex'⟩

instance {A : Multiclass M (n + 1)} [hA : A.Definable P] : A.ex.Definable P :=
  ⟨hA.isDefinable.ex'⟩

theorem IsDefinable.slice {A : Multiclass M (n + l)}
    (hA : A.IsDefinable P) {us : Fin l → M} (hus : Set.range us ⊆ P) :
    (A.slice us).IsDefinable P := by
  obtain ⟨m, φ, vs, hvs, rfl⟩ := hA
  refine ⟨l + m, φ.castAssoc, append us vs, by simp [hus, hvs], by funext; simp⟩

instance {A : Multiclass M (n + l)} [hA : A.Definable Set.univ] {us : Fin l → M} :
  (A.slice us).Definable Set.univ :=
  ⟨hA.isDefinable.slice (by simp)⟩

theorem IsDefinable.remap {n' : ℕ} {A : Multiclass M n}
    (hA : A.IsDefinable P) (f : Fin n → Fin n') :
    (A.remap f).IsDefinable P := by
  obtain ⟨m, φ, vs, hvs, rfl⟩ := hA
  refine ⟨m, φ.substBoundBound (append (castAdd m ∘ f) (natAdd n')), vs,
    by simp [hvs], by funext; simp [← Function.comp_assoc]⟩

instance {A : Multiclass M n} [hA : A.Definable P] (f : Fin n → Fin n') : (A.remap f).Definable P :=
  ⟨hA.isDefinable.remap f⟩

end Definable

end Multiclass

namespace Class

class abbrev DeltaZero (A : Class M) (P : Set M) : Prop := (A : Multiclass M 1).DeltaZero P

instance (A : Multiclass M 1) [A.DeltaZero P] : (A : Class M).DeltaZero P where
  isDeltaZero := by
    norm_cast
    apply Multiclass.DeltaZero.isDeltaZero

instance : (⊤ : Class M).DeltaZero P where
  isDeltaZero := Multiclass.isDeltaZero_top

instance : (⊥ : Class M).DeltaZero P where
  isDeltaZero := Multiclass.isDeltaZero_bot

instance (A : Class M) [hA : A.DeltaZero P] : (∼A).DeltaZero P where
  isDeltaZero := hA.isDeltaZero.not

instance (A B : Class M) [hA : A.DeltaZero P] [hB : B.DeltaZero P] : (A ⟹ B).DeltaZero P where
  isDeltaZero := hA.isDeltaZero.imp hB.isDeltaZero

instance (A B : Class M) [hA : A.DeltaZero P] [hB : B.DeltaZero P] : (A ⊔ B).DeltaZero P where
  isDeltaZero := hA.isDeltaZero.sup hB.isDeltaZero

instance (A B : Class M) [hA : A.DeltaZero P] [hB : B.DeltaZero P] : (A ⊓ B).DeltaZero P where
  isDeltaZero := hA.isDeltaZero.inf hB.isDeltaZero

instance (A B : Class M) [hA : A.DeltaZero P] [hB : B.DeltaZero P] : (A ⇔ B).DeltaZero P where
  isDeltaZero := hA.isDeltaZero.iff hB.isDeltaZero

class abbrev Pi (A : Class M) (k : ℕ) (P : Set M) : Prop := (A : Multiclass M 1).Pi k P

instance (A : Multiclass M 1) (k : ℕ) [A.Pi k P] : (A : Class M).Pi k P where
  isPi := by
    norm_cast
    apply Multiclass.Pi.isPi

class abbrev Sigma (A : Class M) (k : ℕ) (P : Set M) : Prop := (A : Multiclass M 1).Sigma k P

instance (A : Multiclass M 1) (k : ℕ) [A.Sigma k P] : (A : Class M).Sigma k P where
  isSigma := by
    norm_cast
    apply Multiclass.Sigma.isSigma

variable [Nonempty M]

instance (A : Class M) [hA : A.Pi k P] : (∼A).Sigma k P where
  isSigma := hA.isPi.not

instance (A : Class M) [hA : A.Sigma k P] : (∼A).Pi k P where
  isPi := hA.isSigma.not

instance (A B : Class M) [hA : A.Pi k P] [hB : B.Sigma k P] : (A ⟹ B).Sigma k P where
  isSigma := hA.isPi.imp hB.isSigma

instance (A B : Class M) [hA : A.Sigma k P] [hB : B.Pi k P] : (A ⟹ B).Pi k P where
  isPi := hA.isSigma.imp hB.isPi

instance (A B : Class M) [hA : A.Pi k P] [hB : B.Pi k P] : (A ⊔ B).Pi k P where
  isPi := hA.isPi.sup hB.isPi

instance (A B : Class M) [hA : A.Pi k P] [hB : B.Pi k P] : (A ⊓ B).Pi k P where
  isPi := hA.isPi.inf hB.isPi

instance (A B : Class M) [hA : A.Sigma k P] [hB : B.Sigma k P] : (A ⊔ B).Sigma k P where
  isSigma := hA.isSigma.sup hB.isSigma

instance (A B : Class M) [hA : A.Sigma k P] [hB : B.Sigma k P] : (A ⊓ B).Sigma k P where
  isSigma := hA.isSigma.inf hB.isSigma

class abbrev Delta (A : Class M) (k : ℕ) (P : Set M) : Prop := (A : Multiclass M 1).Delta k P

-- instance (A : Class M) [hA : A.Delta k P] : A.Pi k P where

-- instance (A : Class M) [hA : A.Delta k P] : A.Sigma k P where

-- instance (A : Class M) [hA : A.Delta k P] : (∼A).Delta k P where

-- instance (A B : Class M) [hA : A.Delta k P] [hB : B.Delta k P] : (A ⟹ B).Delta k P where

-- instance (A B : Class M) [hA : A.Definable P] [hB : B.Definable P] : (A ⊔ B).Definable P where
--   isDefinable := hA.isDefinable.sup hB.isDefinable

-- instance (A B : Class M) [hA : A.Definable P] [hB : B.Definable P] : (A ⊓ B).Definable P where
--   isDefinable := hA.isDefinable.inf hB.isDefinable

-- instance (A B : Class M) [hA : A.Definable P] [hB : B.Definable P] : (A ⇔ B).Definable P where
--   isDefinable := hA.isDefinable.iff hB.isDefinable

class abbrev Definable (A : Class M) (P : Set M) : Prop := (A : Multiclass M 1).Definable P

instance (A : Multiclass M 1) [A.Definable P] : (A : Class M).Definable P where
  isDefinable := by
    norm_cast
    apply Multiclass.Definable.isDefinable

instance (A : Class M) [hA : A.Definable P] : (∼A).Definable P where
  isDefinable := hA.isDefinable.not

instance (A B : Class M) [hA : A.Definable P] [hB : B.Definable P] : (A ⟹ B).Definable P where
  isDefinable := hA.isDefinable.imp hB.isDefinable

instance (A B : Class M) [hA : A.Definable P] [hB : B.Definable P] : (A ⊔ B).Definable P where
  isDefinable := hA.isDefinable.sup hB.isDefinable

instance (A B : Class M) [hA : A.Definable P] [hB : B.Definable P] : (A ⊓ B).Definable P where
  isDefinable := hA.isDefinable.inf hB.isDefinable

instance (A B : Class M) [hA : A.Definable P] [hB : B.Definable P] : (A ⇔ B).Definable P where
  isDefinable := hA.isDefinable.iff hB.isDefinable

end Class

namespace MulticlassFunction

class abbrev DeltaZero (F : MulticlassFunction M n) (P : Set M) : Prop :=
  (F : Multiclass M (n + 1)).DeltaZero P

theorem isDeltaZero_proj (i : Fin n) :
    (MulticlassFunction.toMulticlass (proj (M := M) i)).IsDeltaZero P :=
  Multiclass.isDeltaZero_eq i.castSucc (last n)

instance DeltaZero_proj (i : Fin n) : DeltaZero (proj (M := M) i) P where
  isDeltaZero := isDeltaZero_proj i

class abbrev Pi (F : MulticlassFunction M n) (k : ℕ) (P : Set M) : Prop :=
  (F : Multiclass M (n + 1)).Pi k P

class abbrev Sigma (F : MulticlassFunction M n) (k : ℕ) (P : Set M) : Prop :=
  (F : Multiclass M (n + 1)).Sigma k P

instance [Nonempty M] {F : MulticlassFunction M n} [F.Sigma (k + 1) P] :
    F.Pi (k + 1) P := by
  refine { toPi:= ?_}
  rw [eq_remap_imp_eq]
  infer_instance

instance [Nonempty M] {F : MulticlassFunction M l}
    [F.Sigma (k + 1) P]
    {Gs : Fin l → MulticlassFunction M n} [∀ i, (Gs i).Sigma (k + 1) P] :
    (F.comp Gs).Sigma (k + 1) P := by
  refine { toSigma := ?_}
  rw [comp_eq_ex']
  infer_instance

instance [Nonempty M] {F : MulticlassFunction M l}
    [F.Pi (k + 1) P]
    {Gs : Fin l → MulticlassFunction M n} [∀ i, (Gs i).Sigma (k + 1) P] :
    (F.comp Gs).Pi (k + 1) P := by
  refine { toPi := ?_}
  rw [comp_eq_all']
  infer_instance

class abbrev Delta (F : MulticlassFunction M n) (k : ℕ) (P : Set M) : Prop :=
  (F : Multiclass M (n + 1)).Pi k P, (F : Multiclass M (n + 1)).Sigma k P

instance [Nonempty M] (F : MulticlassFunction M n) [hF : F.Sigma (k + 1) P] :
  F.Delta (k + 1) P where

class abbrev Definable (F : MulticlassFunction M n) (P : Set M) : Prop :=
  (F : Multiclass M (n + 1)).Definable P


end MulticlassFunction

namespace ClassFunction

class DeltaZero (F : ClassFunction M) (P : Set M) : Prop extends
  DeltaZeroMulticlassFunction : (F : MulticlassFunction M 1).DeltaZero P

theorem isDeltaZero_id :
    (ClassFunction.toMulticlass id).IsDeltaZero P :=
  Multiclass.isDeltaZero_eq 0 1

instance DeltaZero_id : DeltaZero (id : ClassFunction M) P where
  isDeltaZero := isDeltaZero_id

class Pi (F : ClassFunction M) (k : ℕ) (P : Set M) : Prop extends
  PiMulticlassFunction : (F : MulticlassFunction M 1).Pi k P

class Sigma (F : ClassFunction M) (k : ℕ) (P : Set M) : Prop extends
  SigmaMulticlassFunction : (F : MulticlassFunction M 1).Sigma k P

instance (φ : L.BoundedFormula' n) [φ.Pi k] : φ.multiclass.Pi k P :=
  ⟨⟨0, φ, by infer_instance, elim0, by simp, by simp⟩⟩

instance (φ : L.BoundedFormula' n) [φ.Sigma k] : φ.multiclass.Sigma k P :=
  ⟨⟨0, φ, by infer_instance, elim0, by simp, by simp⟩⟩

instance [Nonempty M] {F : ClassFunction M} [hF : F.Sigma (k + 1) P] :
    F.Pi (k + 1) P :=
    { PiMulticlassFunction := by infer_instance }

instance [Nonempty M] {F : ClassFunction M} [hF : F.Sigma (k + 1) P]
    {G : ClassFunction M} [hG : G.Sigma (k + 1) P] :
    (F.comp G).Sigma (k + 1) P := by
  refine { SigmaMulticlassFunction := ?_}
  push_cast
  infer_instance

class Delta (F : ClassFunction M) (k : ℕ) (P : Set M) : Prop extends
  DeltaMulticlassFunction : (F : MulticlassFunction M 1).Delta k P

instance [Nonempty M] (F : ClassFunction M) [hF : F.Sigma (k + 1) P] :
  F.Delta (k + 1) P where

class Definable (F : ClassFunction M) (P : Set M) : Prop extends
  DefinableMulticlassFunction : (F : MulticlassFunction M 1).Definable P

end ClassFunction

namespace Multiclass

instance [Nonempty M] {A : Multiclass M l}
    [A.Sigma (k + 1) P]
    {Gs : Fin l → MulticlassFunction M n} [∀ i, (Gs i).Sigma (k + 1) P] :
    (A.subst Gs).Sigma (k + 1) P := by
  rw [subst_eq_ex']
  infer_instance

instance [Nonempty M] {A : Multiclass M l}
    [A.Pi (k + 1) P]
    {Gs : Fin l → MulticlassFunction M n} [∀ i, (Gs i).Sigma (k + 1) P] :
    (A.subst Gs).Pi (k + 1) P := by
  rw [subst_eq_all']
  infer_instance

end Multiclass

namespace Class

instance {G : MulticlassFunction M n} [G.Sigma k P] : ∀ i, (![G] i).Sigma k P := by
  simp only [Matrix.cons_val_fin_one]
  infer_instance

instance [Nonempty M] {A : Class M}
    [A.Sigma (k + 1) P]
    {G : MulticlassFunction M n} [G.Sigma (k + 1) P] :
    (A.subst G).Sigma (k + 1) P := by
  rw [subst_eq_subst_toMulticlass]
  infer_instance

instance [Nonempty M] {A : Class M}
    [hF : A.Pi (k + 1) P]
    {G : MulticlassFunction M n} [G.Sigma (k + 1) P] :
    (A.subst G).Pi (k + 1) P := by
  rw [subst_eq_subst_toMulticlass]
  infer_instance

instance (a : M) : (Mem a).DeltaZero Set.univ := by
  simp only [Class.Mem, Multiclass.slice₀, isValue]
  infer_instance

instance (a : M) : (Eq a).DeltaZero Set.univ := by
  simp only [Class.Eq, Multiclass.slice₀, isValue]
  infer_instance

instance (a : M) : (Subset a).DeltaZero Set.univ := by
  simp only [Class.Subset, Multiclass.slice₀, isValue]
  infer_instance

instance (R : L.Relations 1) : (Class.Rel R (M := M)).DeltaZero Set.univ where
  isDeltaZero := by
    refine ⟨0, R.boundedFormula₁ &0, by infer_instance, elim0, by simp, ?_⟩
    funext xs
    simp only [Multiclass.slice, multiclass, Nat.add_zero, isValue, Function.comp_apply,
      append_elim0, cast_refl, Function.comp_id, realize'_rel₁, Term.realize'_var', eq_iff_iff]
    simp

end Class

end FirstOrder.Language.MemStructure
