/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Multiclass.Levy
/-!
# Classes and multiclasses in lambda notation

Instances for classes `fun x ↦ ...` and multiclasses `fun xs ↦ ...` built from `∈`, `=`, `⊆`,
definable classes and class functions, logical connectives and quantifiers, so that their
definability and their place in the Lévy hierarchy are found by `infer_instance`.
-/

open FirstOrder Language BoundedFormula Fin MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] {α : Type*}
  {n k l m : ℕ} {P : Set M}

namespace FirstOrder.Language.MemStructure

namespace Multiclass

variable (i j : Fin n)

/-- `xs i ∈ xs j` as a `Δ₀` multiclass -/
instance : Multiclass.DeltaZero (fun xs : Fin n → M ↦ xs i ∈ xs j : Multiclass M n) P :=
  ⟨isDeltaZero_mem i j⟩

/-- `xs i = xs j` as a `Δ₀` multiclass -/
instance : Multiclass.DeltaZero (fun xs : Fin n → M ↦ xs i = xs j : Multiclass M n) P :=
  ⟨isDeltaZero_eq i j⟩

/-- `xs i ⊆ xs j` as a `Δ₀` multiclass -/
instance : Multiclass.DeltaZero (fun xs : Fin n → M ↦ xs i ⊆ xs j : Multiclass M n) P :=
  ⟨isDeltaZero_subset i j⟩

end Multiclass

namespace Class

/-- `{x | x ∈ a}` is `Δ₀` -/
instance (a : M) : Class.DeltaZero (fun x ↦ x ∈ a : Class M) Set.univ :=
  inferInstanceAs ((Mem a).DeltaZero Set.univ)

/-- `{x | x = a}` is `Δ₀` -/
instance (a : M) : Class.DeltaZero (fun x ↦ x = a : Class M) Set.univ := by
  suffices (fun x ↦ x = a : Class M) = Eq a by
    rw [this]
    infer_instance
  funext x
  simp [Class.Eq, Multiclass.Eq]

/-- `{x | x ⊆ a}` is `Δ₀` -/
instance (a : M) : Class.DeltaZero (fun x ↦ x ⊆ a : Class M) Set.univ :=
  inferInstanceAs ((Subset a).DeltaZero Set.univ)

/-- `{x | a ⊆ x}` is `Δ₀` -/
instance (a : M) : Class.DeltaZero (fun x ↦ a ⊆ x : Class M) Set.univ := by
  suffices (fun x ↦ a ⊆ x : Class M) =
      (((Multiclass.Subset 1 0 : Multiclass M (1 + 1)).slice ![a] : Multiclass M 1) : Class M) by
    rw [this]
    infer_instance
  funext x
  simp [Multiclass.Subset, append_right_eq_snoc]

/-- `{x | a ∈ x}` is `Δ₀` -/
instance (a : M) : Class.DeltaZero (fun x ↦ a ∈ x : Class M) Set.univ := by
  suffices (fun x ↦ a ∈ x : Class M) =
      (((Multiclass.Mem 1 0 : Multiclass M (1 + 1)).slice ![a] : Multiclass M 1) : Class M) by
    rw [this]
    infer_instance
  funext x
  simp [Multiclass.Mem, append_right_eq_snoc]

/-- `{x | a = x}` is `Δ₀` -/
instance (a : M) : Class.DeltaZero (fun x ↦ a = x : Class M) Set.univ := by
  suffices (fun x ↦ a = x : Class M) =
      (((Multiclass.Eq 1 0 : Multiclass M (1 + 1)).slice ![a] : Multiclass M 1) : Class M) by
    rw [this]
    infer_instance
  funext x
  simp [Multiclass.Eq, append_right_eq_snoc]

/-- A definable class applied to one coordinate is a definable multiclass -/
instance {A : Class M} [A.Definable Set.univ] (i : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ A (xs i) : Multiclass M n) Set.univ := by
  suffices (fun xs : Fin n → M ↦ A (xs i) : Multiclass M n) = (A : Multiclass M 1).remap ![i] by
    rw [this]
    infer_instance
  funext xs
  simp [Multiclass.remap]

/-- The complement of a definable class is definable -/
instance {A : Class M} [A.Definable Set.univ] :
    Class.Definable (fun x ↦ ¬A x : Class M) Set.univ := by
  suffices (fun x ↦ ¬A x : Class M) = ((∼(A : Multiclass M 1) : Multiclass M 1) : Class M) by
    rw [this]
    infer_instance
  funext x
  simp

/-- The intersection of two `Σₖ` classes is `Σₖ` -/
instance [Nonempty M] {k : ℕ} {A B : Class M} [A.Sigma k Set.univ] [B.Sigma k Set.univ] :
    Class.Sigma (fun x ↦ A x ∧ B x : Class M) k Set.univ := by
  suffices (fun x ↦ A x ∧ B x : Class M) =
      (((A : Multiclass M 1) ⊓ (B : Multiclass M 1) : Multiclass M 1) : Class M) by
    rw [this]
    infer_instance
  funext x
  simp

/-- The union of two `Σₖ` classes is `Σₖ` -/
instance [Nonempty M] {k : ℕ} {A B : Class M} [A.Sigma k Set.univ] [B.Sigma k Set.univ] :
    Class.Sigma (fun x ↦ A x ∨ B x : Class M) k Set.univ := by
  suffices (fun x ↦ A x ∨ B x : Class M) =
      (((A : Multiclass M 1) ⊔ (B : Multiclass M 1) : Multiclass M 1) : Class M) by
    rw [this]
    infer_instance
  funext x
  simp

/-- The intersection of two definable classes is definable -/
instance {A B : Class M} [A.Definable Set.univ] [B.Definable Set.univ] :
    Class.Definable (fun x ↦ A x ∧ B x : Class M) Set.univ := by
  suffices (fun x ↦ A x ∧ B x : Class M) =
      (((A : Multiclass M 1) ⊓ (B : Multiclass M 1) : Multiclass M 1) : Class M) by
    rw [this]
    infer_instance
  funext x
  simp

/-- The union of two definable classes is definable -/
instance {A B : Class M} [A.Definable Set.univ] [B.Definable Set.univ] :
    Class.Definable (fun x ↦ A x ∨ B x : Class M) Set.univ := by
  suffices (fun x ↦ A x ∨ B x : Class M) =
      (((A : Multiclass M 1) ⊔ (B : Multiclass M 1) : Multiclass M 1) : Class M) by
    rw [this]
    infer_instance
  funext x
  simp

/-- `{x | A x → B x}` is definable for definable classes `A` and `B` -/
instance {A B : Class M} [A.Definable Set.univ] [B.Definable Set.univ] :
    Class.Definable (fun x ↦ A x → B x : Class M) Set.univ := by
  suffices (fun x ↦ A x → B x : Class M) =
      (((A : Multiclass M 1) ⟹ (B : Multiclass M 1) : Multiclass M 1) : Class M) by
    rw [this]
    infer_instance
  funext x
  simp

/-- `{x | A x ↔ B x}` is definable for definable classes `A` and `B` -/
instance {A B : Class M} [A.Definable Set.univ] [B.Definable Set.univ] :
    Class.Definable (fun x ↦ (A x ↔ B x) : Class M) Set.univ := by
  suffices (fun x ↦ (A x ↔ B x) : Class M) =
      (((A : Multiclass M 1) ⇔ (B : Multiclass M 1) : Multiclass M 1) : Class M) by
    rw [this]
    infer_instance
  funext x
  simp

/-- `{x | ∀ y ∈ x, A y}` is definable for a definable class `A` -/
instance {A : Class M} [A.Definable Set.univ] :
    Class.Definable (fun x ↦ ∀ y ∈ x, A y : Class M) Set.univ := by
  suffices (fun x ↦ ∀ y ∈ x, A y : Class M) =
      ((((A : Multiclass M 1).remap ![1]).allMem 0 : Multiclass M 1) : Class M) by
    rw [this]
    infer_instance
  funext x
  simp [Multiclass.remap]

/-- `{x | ∃ y ∈ x, A y}` is definable for a definable class `A` -/
instance {A : Class M} [A.Definable Set.univ] :
    Class.Definable (fun x ↦ ∃ y ∈ x, A y : Class M) Set.univ := by
  suffices (fun x ↦ ∃ y ∈ x, A y : Class M) =
      (((Multiclass.Mem 1 0 ⊓ (A : Multiclass M 1).remap ![1]).ex : Multiclass M 1) : Class M) by
    rw [this]
    infer_instance
  funext x
  simp [Multiclass.Mem, Multiclass.remap]

end Class

namespace Multiclass

/-! ### Multiclasses written as `fun xs ↦ ...`

Instances for multiclasses given as functions `(Fin n → M) → Prop`, so that combinations of `∈`,
`=`, definable classes, logical connectives and quantifiers are found by `infer_instance`. -/

section Lambda

variable {n : ℕ} {P : Set M}

/-- A multiclass is `Δ₀` if it is `Δ₀` as a function `fun xs ↦ A xs` -/
instance {A : Multiclass M n} [hA : Multiclass.DeltaZero (fun xs : Fin n → M ↦ A xs) P] :
    A.DeltaZero P :=
  hA

/-- A multiclass is `Σₖ` if it is `Σₖ` as a function `fun xs ↦ A xs` -/
instance {k : ℕ} {A : Multiclass M n} [hA : Multiclass.Sigma k (fun xs : Fin n → M ↦ A xs) P] :
    A.Sigma k P :=
  hA

/-- A multiclass is definable if it is definable as a function `fun xs ↦ A xs` -/
instance {A : Multiclass M n} [hA : Multiclass.Definable (fun xs : Fin n → M ↦ A xs) P] :
    A.Definable P :=
  hA

instance {A : (Fin n → M) → Prop} [hA : Multiclass.DeltaZero A P] : Multiclass.Definable A P :=
  ⟨hA.isDeltaZero.isDefinable⟩

/-- A `Δ₀` class applied to a coordinate is `Δ₀` -/
instance {A : Class M} [A.DeltaZero P] (i : Fin n) :
    Multiclass.DeltaZero (fun xs : Fin n → M ↦ A (xs i)) P := by
  have h : (fun xs : Fin n → M ↦ A (xs i)) = (A : Multiclass M 1).remap ![i] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  infer_instance

/-- `xs i ∈ a` is `Δ₀` -/
instance (a : M) (i : Fin n) : Multiclass.DeltaZero (fun xs : Fin n → M ↦ xs i ∈ a) Set.univ := by
  have h : (fun xs : Fin n → M ↦ xs i ∈ a) =
      (Class.toMulticlass (fun x ↦ x ∈ a)).remap ![i] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  infer_instance

/-- `a ∈ xs i` is `Δ₀` -/
instance (a : M) (i : Fin n) : Multiclass.DeltaZero (fun xs : Fin n → M ↦ a ∈ xs i) Set.univ := by
  have h : (fun xs : Fin n → M ↦ a ∈ xs i) =
      (Class.toMulticlass (fun x ↦ a ∈ x)).remap ![i] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  infer_instance

/-- `xs i = a` is `Δ₀` -/
instance (a : M) (i : Fin n) : Multiclass.DeltaZero (fun xs : Fin n → M ↦ xs i = a) Set.univ := by
  have h : (fun xs : Fin n → M ↦ xs i = a) =
      (Class.toMulticlass (fun x ↦ x = a)).remap ![i] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  infer_instance

/-- `a = xs i` is `Δ₀` -/
instance (a : M) (i : Fin n) : Multiclass.DeltaZero (fun xs : Fin n → M ↦ a = xs i) Set.univ := by
  have h : (fun xs : Fin n → M ↦ a = xs i) =
      (Class.toMulticlass (fun x ↦ a = x)).remap ![i] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  infer_instance

/-- `xs i ⊆ a` is `Δ₀` -/
instance (a : M) (i : Fin n) : Multiclass.DeltaZero (fun xs : Fin n → M ↦ xs i ⊆ a) Set.univ := by
  have h : (fun xs : Fin n → M ↦ xs i ⊆ a) =
      (Class.toMulticlass (fun x ↦ x ⊆ a)).remap ![i] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  infer_instance

/-- `a ⊆ xs i` is `Δ₀` -/
instance (a : M) (i : Fin n) : Multiclass.DeltaZero (fun xs : Fin n → M ↦ a ⊆ xs i) Set.univ := by
  have h : (fun xs : Fin n → M ↦ a ⊆ xs i) =
      (Class.toMulticlass (fun x ↦ a ⊆ x)).remap ![i] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  infer_instance

instance {A : (Fin n → M) → Prop} [hA : Multiclass.DeltaZero A P] :
    Multiclass.DeltaZero (fun xs ↦ ¬A xs) P :=
  ⟨hA.isDeltaZero.not⟩

instance {A B : (Fin n → M) → Prop} [hA : Multiclass.DeltaZero A P]
    [hB : Multiclass.DeltaZero B P] :
    Multiclass.DeltaZero (fun xs ↦ A xs ∧ B xs) P :=
  ⟨hA.isDeltaZero.inf hB.isDeltaZero⟩

instance {A B : (Fin n → M) → Prop} [hA : Multiclass.DeltaZero A P]
    [hB : Multiclass.DeltaZero B P] :
    Multiclass.DeltaZero (fun xs ↦ A xs ∨ B xs) P :=
  ⟨hA.isDeltaZero.sup hB.isDeltaZero⟩

instance {A B : (Fin n → M) → Prop} [hA : Multiclass.DeltaZero A P]
    [hB : Multiclass.DeltaZero B P] :
    Multiclass.DeltaZero (fun xs ↦ A xs → B xs) P :=
  ⟨hA.isDeltaZero.imp hB.isDeltaZero⟩

instance {A B : (Fin n → M) → Prop} [hA : Multiclass.DeltaZero A P]
    [hB : Multiclass.DeltaZero B P] :
    Multiclass.DeltaZero (fun xs ↦ A xs ↔ B xs) P :=
  ⟨hA.isDeltaZero.iff hB.isDeltaZero⟩

/-- Bounded universal quantification `∀ y ∈ xs i` of a `Δ₀` multiclass is `Δ₀` -/
instance {A : (Fin n → M) → M → Prop} (i : Fin n)
    [hA : Multiclass.DeltaZero (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n)))
      P] :
    Multiclass.DeltaZero (fun xs ↦ ∀ y ∈ xs i, A xs y) P := by
  have h : (fun xs ↦ ∀ y ∈ xs i, A xs y) = Multiclass.allMem
      (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n))) i := by
    funext xs
    simp
  rw [h]
  exact ⟨hA.isDeltaZero.allMem i⟩

/-- Bounded existential quantification `∃ y ∈ xs i` of a `Δ₀` multiclass is `Δ₀` -/
instance {A : (Fin n → M) → M → Prop} (i : Fin n)
    [hA : Multiclass.DeltaZero (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n)))
      P] :
    Multiclass.DeltaZero (fun xs ↦ ∃ y ∈ xs i, A xs y) P := by
  have h : (fun xs ↦ ∃ y ∈ xs i, A xs y) = Multiclass.not (Multiclass.allMem
      (fun ys : Fin (n + 1) → M ↦ ¬A (fun j ↦ ys j.castSucc) (ys (last n))) i) := by
    funext xs
    simp
  rw [h]
  exact ⟨(hA.isDeltaZero.not.allMem i).not⟩

/-- A definable class applied to a coordinate is definable -/
instance {A : Class M} [A.Definable P] (i : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ A (xs i)) P := by
  have h : (fun xs : Fin n → M ↦ A (xs i)) = (A : Multiclass M 1).remap ![i] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  infer_instance

instance {A : (Fin n → M) → Prop} [hA : Multiclass.Definable A P] :
    Multiclass.Definable (fun xs ↦ ¬A xs) P :=
  ⟨hA.isDefinable.not⟩

instance {A B : (Fin n → M) → Prop} [hA : Multiclass.Definable A P]
    [hB : Multiclass.Definable B P] :
    Multiclass.Definable (fun xs ↦ A xs ∧ B xs) P :=
  ⟨hA.isDefinable.inf hB.isDefinable⟩

instance {A B : (Fin n → M) → Prop} [hA : Multiclass.Definable A P]
    [hB : Multiclass.Definable B P] :
    Multiclass.Definable (fun xs ↦ A xs ∨ B xs) P :=
  ⟨hA.isDefinable.sup hB.isDefinable⟩

instance {A B : (Fin n → M) → Prop} [hA : Multiclass.Definable A P]
    [hB : Multiclass.Definable B P] :
    Multiclass.Definable (fun xs ↦ A xs → B xs) P :=
  ⟨hA.isDefinable.imp hB.isDefinable⟩

instance {A B : (Fin n → M) → Prop} [hA : Multiclass.Definable A P]
    [hB : Multiclass.Definable B P] :
    Multiclass.Definable (fun xs ↦ A xs ↔ B xs) P :=
  ⟨hA.isDefinable.iff hB.isDefinable⟩

/-- Universal quantification of a definable multiclass is definable -/
instance {A : (Fin n → M) → M → Prop}
    [hA : Multiclass.Definable (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n)))
      P] :
    Multiclass.Definable (fun xs ↦ ∀ y, A xs y) P := by
  have h : (fun xs ↦ ∀ y, A xs y) =
      Multiclass.all (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n))) := by
    funext xs
    have h' :=
      Multiclass.all_iff (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n))) xs
    rw [eq_iff_iff, h']
    simp
  rw [h]
  exact ⟨hA.isDefinable.all'⟩

/-- Existential quantification of a definable multiclass is definable -/
instance {A : (Fin n → M) → M → Prop}
    [hA : Multiclass.Definable (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n)))
      P] :
    Multiclass.Definable (fun xs ↦ ∃ y, A xs y) P := by
  have h : (fun xs ↦ ∃ y, A xs y) =
      Multiclass.ex (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n))) := by
    funext xs
    have h' :=
      Multiclass.ex_iff (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n))) xs
    rw [eq_iff_iff, h']
    simp
  rw [h]
  exact ⟨hA.isDefinable.ex'⟩

/-- A `Δ₀` multiclass is `Σₖ` -/
instance {k : ℕ} {A : (Fin n → M) → Prop} [hA : Multiclass.DeltaZero A P] :
    Multiclass.Sigma k A P :=
  ⟨DeltaZero.isSigma (hA := hA)⟩

instance {A : (Fin n → M) → Prop} [hA : Multiclass.Sigma 1 A P] :
    Multiclass.Definable A P :=
  Sigma.definable hA

/-- A `Σₖ` class applied to a coordinate is `Σₖ` -/
instance [Nonempty M] {k : ℕ} {A : Class M} [A.Sigma k P] (i : Fin n) :
    Multiclass.Sigma k (fun xs : Fin n → M ↦ A (xs i)) P := by
  have h : (fun xs : Fin n → M ↦ A (xs i)) = (A : Multiclass M 1).remap ![i] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  infer_instance

instance [Nonempty M] {k : ℕ} {A B : (Fin n → M) → Prop} [hA : Multiclass.Sigma k A P]
    [hB : Multiclass.Sigma k B P] :
    Multiclass.Sigma k (fun xs ↦ A xs ∧ B xs) P :=
  ⟨hA.isSigma.inf hB.isSigma⟩

instance [Nonempty M] {k : ℕ} {A B : (Fin n → M) → Prop} [hA : Multiclass.Sigma k A P]
    [hB : Multiclass.Sigma k B P] :
    Multiclass.Sigma k (fun xs ↦ A xs ∨ B xs) P :=
  ⟨hA.isSigma.sup hB.isSigma⟩

/-- Existential quantification of a `Σₖ` multiclass is `Σₖ` -/
instance {k : ℕ} [NeZero k] {A : (Fin n → M) → M → Prop}
    [hA : Multiclass.Sigma k (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n)))
      P] :
    Multiclass.Sigma k (fun xs ↦ ∃ y, A xs y) P := by
  have h : (fun xs ↦ ∃ y, A xs y) =
      Multiclass.ex (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n))) := by
    funext xs
    have h' :=
      Multiclass.ex_iff (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n))) xs
    rw [eq_iff_iff, h']
    simp
  rw [h]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne k)
  exact ⟨hA.isSigma.ex'⟩

/-- A `Δ₀` multiclass is `Πₖ` -/
instance {k : ℕ} {A : (Fin n → M) → Prop} [hA : Multiclass.DeltaZero A P] :
    Multiclass.Pi k A P :=
  ⟨DeltaZero.isPi (hA := hA)⟩

instance {A : (Fin n → M) → Prop} [hA : Multiclass.Pi 1 A P] : Multiclass.Definable A P :=
  Pi.definable hA

instance [Nonempty M] {k : ℕ} {A B : (Fin n → M) → Prop} [hA : Multiclass.Pi k A P]
    [hB : Multiclass.Pi k B P] :
    Multiclass.Pi k (fun xs ↦ A xs ∧ B xs) P :=
  ⟨hA.isPi.inf hB.isPi⟩

instance [Nonempty M] {k : ℕ} {A B : (Fin n → M) → Prop} [hA : Multiclass.Pi k A P]
    [hB : Multiclass.Pi k B P] :
    Multiclass.Pi k (fun xs ↦ A xs ∨ B xs) P :=
  ⟨hA.isPi.sup hB.isPi⟩

/-- Universal quantification of a `Πₖ` multiclass is `Πₖ` -/
instance {k : ℕ} [NeZero k] {A : (Fin n → M) → M → Prop}
    [hA : Multiclass.Pi k (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n)))
      P] :
    Multiclass.Pi k (fun xs ↦ ∀ y, A xs y) P := by
  have h : (fun xs ↦ ∀ y, A xs y) =
      Multiclass.all (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n))) := by
    funext xs
    have h' :=
      Multiclass.all_iff (fun ys : Fin (n + 1) → M ↦ A (fun j ↦ ys j.castSucc) (ys (last n))) xs
    rw [eq_iff_iff, h']
    simp
  rw [h]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne k)
  exact ⟨hA.isPi.all'⟩

/-- A `Δ₀` binary relation applied to coordinates is `Δ₀` -/
instance {R : M → M → Prop} [hR : Multiclass.DeltaZero (fun ys : Fin 2 → M ↦ R (ys 0) (ys 1)) P]
    (i j : Fin n) : Multiclass.DeltaZero (fun xs : Fin n → M ↦ R (xs i) (xs j)) P := by
  let R' : Multiclass M 2 := fun ys ↦ R (ys 0) (ys 1)
  have h : (fun xs : Fin n → M ↦ R (xs i) (xs j)) = R'.remap ![i, j] := by
    funext xs
    simp [R', Multiclass.remap]
  rw [h]
  infer_instance

/-- A `Δ₀` ternary relation applied to coordinates is `Δ₀` -/
instance {R : M → M → M → Prop}
    [hR : Multiclass.DeltaZero (fun ys : Fin 3 → M ↦ R (ys 0) (ys 1) (ys 2)) P] (i j l : Fin n) :
    Multiclass.DeltaZero (fun xs : Fin n → M ↦ R (xs i) (xs j) (xs l)) P := by
  let R' : Multiclass M 3 := fun ys ↦ R (ys 0) (ys 1) (ys 2)
  have h : (fun xs : Fin n → M ↦ R (xs i) (xs j) (xs l)) = R'.remap ![i, j, l] := by
    funext xs
    simp [R', Multiclass.remap]
  rw [h]
  infer_instance

end Lambda

end Multiclass

namespace Class

variable {P : Set M}

/-- A class is `Δ₀` if it is `Δ₀` as a multiclass in one variable -/
instance {A : Class M} [hA : Multiclass.DeltaZero (fun xs : Fin 1 → M ↦ A (xs 0)) P] :
    A.DeltaZero P := by
  have h : (A : Multiclass M 1) = fun xs ↦ A (xs 0) := by
    funext xs
    simp
  have : (A : Multiclass M 1).DeltaZero P := h ▸ hA
  infer_instance

/-- A class is `Σₖ` if it is `Σₖ` as a multiclass in one variable -/
instance {k : ℕ} {A : Class M} [hA : Multiclass.Sigma k (fun xs : Fin 1 → M ↦ A (xs 0)) P] :
    A.Sigma k P := by
  have h : (A : Multiclass M 1) = fun xs ↦ A (xs 0) := by
    funext xs
    simp
  have : (A : Multiclass M 1).Sigma k P := h ▸ hA
  infer_instance

/-- A class is `Πₖ` if it is `Πₖ` as a multiclass in one variable -/
instance {k : ℕ} {A : Class M} [hA : Multiclass.Pi k (fun xs : Fin 1 → M ↦ A (xs 0)) P] :
    A.Pi k P := by
  have h : (A : Multiclass M 1) = fun xs ↦ A (xs 0) := by
    funext xs
    simp
  have : (A : Multiclass M 1).Pi k P := h ▸ hA
  infer_instance

/-- A class is definable if it is definable as a multiclass in one variable -/
instance {A : Class M} [hA : Multiclass.Definable (fun xs : Fin 1 → M ↦ A (xs 0)) P] :
    A.Definable P := by
  have h : (A : Multiclass M 1) = fun xs ↦ A (xs 0) := by
    funext xs
    simp
  have : (A : Multiclass M 1).Definable P := h ▸ hA
  infer_instance

end Class

namespace ClassFunction

/-- The identity `fun x ↦ x` is a `Σ₁` class function -/
instance : ClassFunction.Sigma (fun x ↦ x : ClassFunction M) 1 Set.univ :=
  Sigma.of_iff (F := fun xs : Fin 2 → M ↦ xs 0 = xs 1) fun u w ↦ by simp

/-- A constant `fun _ ↦ a` is a `Σ₁` class function -/
instance (a : M) : ClassFunction.Sigma (fun _ ↦ a : ClassFunction M) 1 Set.univ :=
  Sigma.of_iff (F := fun xs : Fin 2 → M ↦ xs 1 = a) fun u w ↦ by simp [eq_comm]

end ClassFunction

namespace Class

/-- `{x | F x ∈ G x}` is `Σ₁` for `Σ₁` class functions `F` and `G` -/
instance [Nonempty M] {F G : ClassFunction M} [F.Sigma 1 Set.univ] [G.Sigma 1 Set.univ] :
    Class.Sigma (fun x ↦ F x ∈ G x : Class M) 1 Set.univ := by
  -- `[x, u, v]` with `u = F x` and `v = G x`
  let B : Multiclass M 3 := (F : Multiclass M 2).remap ![0, 1] ⊓
    (G : Multiclass M 2).remap ![0, 2] ⊓ Multiclass.Mem 1 2
  have hB : (fun x ↦ F x ∈ G x : Class M) = (B.ex.ex : Class M) := by
    funext x
    simp [B, Multiclass.remap, Multiclass.Mem, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff]
  rw [hB]
  infer_instance

/-- `{x | F x ⊆ G x}` is `Σ₁` for `Σ₁` class functions `F` and `G` -/
instance [Nonempty M] {F G : ClassFunction M} [F.Sigma 1 Set.univ] [G.Sigma 1 Set.univ] :
    Class.Sigma (fun x ↦ F x ⊆ G x : Class M) 1 Set.univ := by
  -- `[x, u, v]` with `u = F x` and `v = G x`
  let B : Multiclass M 3 := (F : Multiclass M 2).remap ![0, 1] ⊓
    (G : Multiclass M 2).remap ![0, 2] ⊓ Multiclass.Subset 1 2
  have hB : (fun x ↦ F x ⊆ G x : Class M) = (B.ex.ex : Class M) := by
    funext x
    simp [B, Multiclass.remap, Multiclass.Subset, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff]
  rw [hB]
  infer_instance

/-- `{x | F x ∈ G x}` is definable for definable class functions `F` and `G` -/
instance {F G : ClassFunction M} [F.Definable Set.univ] [G.Definable Set.univ] :
    Class.Definable (fun x ↦ F x ∈ G x : Class M) Set.univ := by
  -- `[x, u, v]` with `u = F x` and `v = G x`
  let B : Multiclass M 3 := (F : Multiclass M 2).remap ![0, 1] ⊓
    (G : Multiclass M 2).remap ![0, 2] ⊓ Multiclass.Mem 1 2
  have hB : (fun x ↦ F x ∈ G x : Class M) = (B.ex.ex : Class M) := by
    funext x
    simp [B, Multiclass.remap, Multiclass.Mem, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff]
  rw [hB]
  infer_instance

/-- `{x | F x ⊆ G x}` is definable for definable class functions `F` and `G` -/
instance {F G : ClassFunction M} [F.Definable Set.univ] [G.Definable Set.univ] :
    Class.Definable (fun x ↦ F x ⊆ G x : Class M) Set.univ := by
  -- `[x, u, v]` with `u = F x` and `v = G x`
  let B : Multiclass M 3 := (F : Multiclass M 2).remap ![0, 1] ⊓
    (G : Multiclass M 2).remap ![0, 2] ⊓ Multiclass.Subset 1 2
  have hB : (fun x ↦ F x ⊆ G x : Class M) = (B.ex.ex : Class M) := by
    funext x
    simp [B, Multiclass.remap, Multiclass.Subset, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff]
  rw [hB]
  infer_instance

/-- `{x | F x = G x}` is definable for definable class functions `F` and `G` -/
instance {F G : ClassFunction M} [F.Definable Set.univ] [G.Definable Set.univ] :
    Class.Definable (fun x ↦ F x = G x : Class M) Set.univ := by
  -- `[x, u, v]` with `u = F x` and `v = G x`
  let B : Multiclass M 3 := (F : Multiclass M 2).remap ![0, 1] ⊓
    (G : Multiclass M 2).remap ![0, 2] ⊓ Multiclass.Eq 1 2
  have hB : (fun x ↦ F x = G x : Class M) = (B.ex.ex : Class M) := by
    funext x
    simp [B, Multiclass.remap, Multiclass.Eq, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff, eq_comm]
  rw [hB]
  infer_instance

/-- `{x | R (F x) (G x)}` is definable for a definable binary relation `R` and definable class
functions `F` and `G` -/
instance {R : M → M → Prop}
    [hR : Multiclass.Definable (fun ys : Fin 2 → M ↦ R (ys 0) (ys 1)) Set.univ]
    {F G : ClassFunction M} [F.Definable Set.univ] [G.Definable Set.univ] :
    Class.Definable (fun x ↦ R (F x) (G x) : Class M) Set.univ := by
  -- `[x, u, v]` with `u = F x` and `v = G x`
  let R' : Multiclass M 2 := fun ys ↦ R (ys 0) (ys 1)
  let B : Multiclass M 3 := (F : Multiclass M 2).remap ![0, 1] ⊓
    (G : Multiclass M 2).remap ![0, 2] ⊓ R'.remap ![1, 2]
  have hB : (fun x ↦ R (F x) (G x) : Class M) = (B.ex.ex : Class M) := by
    funext x
    simp [B, R', Multiclass.remap, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff]
  rw [hB]
  infer_instance

end Class

namespace Multiclass

variable {n : ℕ}

/-- `F (xs i) ∈ G (xs j)` is definable for definable class functions `F` and `G` -/
instance {F G : ClassFunction M} [F.Definable Set.univ] [G.Definable Set.univ] (i j : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ F (xs i) ∈ G (xs j)) Set.univ := by
  -- `[xs, u, v]` with `u = F (xs i)` and `v = G (xs j)`
  let B : Multiclass M (n + 1 + 1) :=
    (F : Multiclass M 2).remap ![i.castSucc.castSucc, (last n).castSucc] ⊓
      (G : Multiclass M 2).remap ![j.castSucc.castSucc, last (n + 1)] ⊓
      Multiclass.Mem (last n).castSucc (last (n + 1))
  have h : (fun xs : Fin n → M ↦ F (xs i) ∈ G (xs j)) = B.ex.ex := by
    funext xs
    simp [B, Multiclass.remap, Multiclass.Mem, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff]
  rw [h]
  infer_instance

/-- `xs i ∈ G (xs j)` is definable for a definable class function `G` -/
instance {G : ClassFunction M} [G.Definable Set.univ] (i j : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ xs i ∈ G (xs j)) Set.univ := by
  -- `[xs, v]` with `v = G (xs j)`
  let B : Multiclass M (n + 1) :=
    (G : Multiclass M 2).remap ![j.castSucc, last n] ⊓ Multiclass.Mem i.castSucc (last n)
  have h : (fun xs : Fin n → M ↦ xs i ∈ G (xs j)) = B.ex := by
    funext xs
    simp [B, Multiclass.remap, Multiclass.Mem, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff]
  rw [h]
  infer_instance

/-- `F (xs i) ∈ xs j` is definable for a definable class function `F` -/
instance {F : ClassFunction M} [F.Definable Set.univ] (i j : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ F (xs i) ∈ xs j) Set.univ := by
  -- `[xs, u]` with `u = F (xs i)`
  let B : Multiclass M (n + 1) :=
    (F : Multiclass M 2).remap ![i.castSucc, last n] ⊓ Multiclass.Mem (last n) j.castSucc
  have h : (fun xs : Fin n → M ↦ F (xs i) ∈ xs j) = B.ex := by
    funext xs
    simp [B, Multiclass.remap, Multiclass.Mem, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff]
  rw [h]
  infer_instance

/-- `F (xs i) ⊆ G (xs j)` is definable for definable class functions `F` and `G` -/
instance {F G : ClassFunction M} [F.Definable Set.univ] [G.Definable Set.univ] (i j : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ F (xs i) ⊆ G (xs j)) Set.univ := by
  -- `[xs, u, v]` with `u = F (xs i)` and `v = G (xs j)`
  let B : Multiclass M (n + 1 + 1) :=
    (F : Multiclass M 2).remap ![i.castSucc.castSucc, (last n).castSucc] ⊓
      (G : Multiclass M 2).remap ![j.castSucc.castSucc, last (n + 1)] ⊓
      Multiclass.Subset (last n).castSucc (last (n + 1))
  have h : (fun xs : Fin n → M ↦ F (xs i) ⊆ G (xs j)) = B.ex.ex := by
    funext xs
    simp [B, Multiclass.remap, Multiclass.Subset, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff]
  rw [h]
  infer_instance

/-- `xs i ⊆ G (xs j)` is definable for a definable class function `G` -/
instance {G : ClassFunction M} [G.Definable Set.univ] (i j : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ xs i ⊆ G (xs j)) Set.univ := by
  -- `[xs, v]` with `v = G (xs j)`
  let B : Multiclass M (n + 1) :=
    (G : Multiclass M 2).remap ![j.castSucc, last n] ⊓ Multiclass.Subset i.castSucc (last n)
  have h : (fun xs : Fin n → M ↦ xs i ⊆ G (xs j)) = B.ex := by
    funext xs
    simp [B, Multiclass.remap, Multiclass.Subset, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff]
  rw [h]
  infer_instance

/-- `F (xs i) ⊆ xs j` is definable for a definable class function `F` -/
instance {F : ClassFunction M} [F.Definable Set.univ] (i j : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ F (xs i) ⊆ xs j) Set.univ := by
  -- `[xs, u]` with `u = F (xs i)`
  let B : Multiclass M (n + 1) :=
    (F : Multiclass M 2).remap ![i.castSucc, last n] ⊓ Multiclass.Subset (last n) j.castSucc
  have h : (fun xs : Fin n → M ↦ F (xs i) ⊆ xs j) = B.ex := by
    funext xs
    simp [B, Multiclass.remap, Multiclass.Subset, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff]
  rw [h]
  infer_instance

/-- `F (xs i) = G (xs j)` is definable for definable class functions `F` and `G` -/
instance {F G : ClassFunction M} [F.Definable Set.univ] [G.Definable Set.univ] (i j : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ F (xs i) = G (xs j)) Set.univ := by
  -- `[xs, u, v]` with `u = F (xs i)` and `v = G (xs j)`
  let B : Multiclass M (n + 1 + 1) :=
    (F : Multiclass M 2).remap ![i.castSucc.castSucc, (last n).castSucc] ⊓
      (G : Multiclass M 2).remap ![j.castSucc.castSucc, last (n + 1)] ⊓
      Multiclass.Eq (last n).castSucc (last (n + 1))
  have h : (fun xs : Fin n → M ↦ F (xs i) = G (xs j)) = B.ex.ex := by
    funext xs
    simp [B, Multiclass.remap, Multiclass.Eq, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff, eq_comm]
  rw [h]
  infer_instance

/-- `xs i = G (xs j)` is definable for a definable class function `G` -/
instance {G : ClassFunction M} [G.Definable Set.univ] (i j : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ xs i = G (xs j)) Set.univ := by
  -- `[xs, v]` with `v = G (xs j)`
  let B : Multiclass M (n + 1) :=
    (G : Multiclass M 2).remap ![j.castSucc, last n] ⊓ Multiclass.Eq i.castSucc (last n)
  have h : (fun xs : Fin n → M ↦ xs i = G (xs j)) = B.ex := by
    funext xs
    simp [B, Multiclass.remap, Multiclass.Eq, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff, eq_comm]
  rw [h]
  infer_instance

/-- `F (xs i) = xs j` is definable for a definable class function `F` -/
instance {F : ClassFunction M} [F.Definable Set.univ] (i j : Fin n) :
    Multiclass.Definable (fun xs : Fin n → M ↦ F (xs i) = xs j) Set.univ := by
  -- `[xs, u]` with `u = F (xs i)`
  let B : Multiclass M (n + 1) :=
    (F : Multiclass M 2).remap ![i.castSucc, last n] ⊓ Multiclass.Eq (last n) j.castSucc
  have h : (fun xs : Fin n → M ↦ F (xs i) = xs j) = B.ex := by
    funext xs
    simp [B, Multiclass.remap, Multiclass.Eq, Matrix.comp_vecCons, Matrix.empty_eq,
      ClassFunction.toMulticlass_vec_iff, eq_comm]
  rw [h]
  infer_instance

end Multiclass

namespace ClassFunction

theorem toMulticlassFunction_eq (F : ClassFunction M) :
    (F : MulticlassFunction M 1) = fun xs ↦ F (xs 0) := by
  funext xs
  simp [toMulticlassFunction]

/-- A class function is `Δ₀` if it is a `Δ₀` term `fun xs ↦ F (xs 0)` -/
instance {F : ClassFunction M}
    [h : MulticlassFunction.DeltaZero (fun xs : Fin 1 → M ↦ F (xs 0)) P] :
    F.DeltaZero P where
  DeltaZeroMulticlassFunction := by
    rw [toMulticlassFunction_eq]
    exact h

/-- A class function is `Πₖ` if it is a `Πₖ` term `fun xs ↦ F (xs 0)` -/
instance {k : ℕ} {F : ClassFunction M}
    [h : MulticlassFunction.Pi (fun xs : Fin 1 → M ↦ F (xs 0)) k P] :
    F.Pi k P where
  piMulticlassFunction := by
    rw [toMulticlassFunction_eq]
    exact h

/-- A class function is `Σₖ` if it is a `Σₖ` term `fun xs ↦ F (xs 0)` -/
instance {k : ℕ} {F : ClassFunction M}
    [h : MulticlassFunction.Sigma (fun xs : Fin 1 → M ↦ F (xs 0)) k P] :
    F.Sigma k P where
  sigmaMulticlassFunction := by
    rw [toMulticlassFunction_eq]
    exact h

end ClassFunction

namespace MulticlassFunction

/-! ### Terms in lambda notation

A term `t : (Fin n → M) → M` is `Σ₁` if its graph is. Atoms `P (t₁ xs) … (tₖ xs)` of a `Σ₁`
predicate `P` applied to `Σ₁` terms are `Σ₁`. -/

variable {n : ℕ}

/-- A projection `fun xs ↦ xs i` is a `Δ₀` term -/
instance (i : Fin n) : MulticlassFunction.DeltaZero (fun xs : Fin n → M ↦ xs i) P :=
  inferInstanceAs (MulticlassFunction.DeltaZero (proj i) P)

/-- A constant `fun _ ↦ a` is a `Δ₀` term -/
instance (a : M) : MulticlassFunction.DeltaZero (fun _ : Fin n → M ↦ a) Set.univ := by
  have h : MulticlassFunction.toMulticlass (fun _ : Fin n → M ↦ a) =
      fun ys ↦ ys (last n) = a := by
    funext ys
    simp [toMulticlass, eq_comm]
  have : (MulticlassFunction.toMulticlass (fun _ : Fin n → M ↦ a)).DeltaZero Set.univ :=
    h ▸ inferInstance
  infer_instance

/-- A `Δ₀` term is a `Σₖ` term -/
instance {k : ℕ} {F : (Fin n → M) → M} [h : MulticlassFunction.DeltaZero F P] :
    MulticlassFunction.Sigma F k P := by
  infer_instance

/-- A projection `fun xs ↦ xs i` is a `Σₖ` term -/
instance {k : ℕ} (i : Fin n) : MulticlassFunction.Sigma (fun xs : Fin n → M ↦ xs i) k P :=
  inferInstanceAs (MulticlassFunction.Sigma (proj i) k P)

/-- A constant `fun _ ↦ a` is a `Σₖ` term -/
instance {k : ℕ} (a : M) : MulticlassFunction.Sigma (fun _ : Fin n → M ↦ a) k Set.univ :=
  inferInstance

/-- A `Σₖ` class function applied to a `Σₖ` term is a `Σₖ` term -/
instance [Nonempty M] {k : ℕ} [NeZero k] {F : ClassFunction M} [F.Sigma k P]
    {t : (Fin n → M) → M} [MulticlassFunction.Sigma t k P] :
    MulticlassFunction.Sigma (fun xs ↦ F (t xs)) k P :=
  inferInstanceAs (MulticlassFunction.Sigma ((F : MulticlassFunction M 1).comp ![t]) k P)

/-- A binary `Σₖ` function applied to `Σₖ` terms is a `Σₖ` term -/
instance [Nonempty M] {k : ℕ} [NeZero k] {G : M → M → M}
    [MulticlassFunction.Sigma (fun ys : Fin 2 → M ↦ G (ys 0) (ys 1)) k P]
    {t₁ t₂ : (Fin n → M) → M} [MulticlassFunction.Sigma t₁ k P]
    [MulticlassFunction.Sigma t₂ k P] :
    MulticlassFunction.Sigma (fun xs ↦ G (t₁ xs) (t₂ xs)) k P :=
  inferInstanceAs (MulticlassFunction.Sigma
    (MulticlassFunction.comp (fun ys : Fin 2 → M ↦ G (ys 0) (ys 1)) ![t₁, t₂]) k P)

end MulticlassFunction

namespace Multiclass

variable {n : ℕ}

/-- A `Σ₁` class applied to a `Σ₁` term is `Σ₁` -/
instance [Nonempty M] {A : Class M} [A.Sigma 1 P] {t : (Fin n → M) → M}
    [MulticlassFunction.Sigma t 1 P] :
    Multiclass.Sigma 1 (fun xs ↦ A (t xs)) P := by
  have h : (fun xs ↦ A (t xs)) = (A : Multiclass M 1).subst ![t] := by
    funext xs
    simp [Multiclass.subst]
  rw [h]
  infer_instance

/-- A binary `Σ₁` relation applied to `Σ₁` terms is `Σ₁` -/
instance [Nonempty M] {R : M → M → Prop}
    [hR : Multiclass.Sigma 1 (fun ys : Fin 2 → M ↦ R (ys 0) (ys 1)) P]
    {t₁ t₂ : (Fin n → M) → M} [MulticlassFunction.Sigma t₁ 1 P]
    [MulticlassFunction.Sigma t₂ 1 P] :
    Multiclass.Sigma 1 (fun xs ↦ R (t₁ xs) (t₂ xs)) P := by
  let R' : Multiclass M 2 := fun ys ↦ R (ys 0) (ys 1)
  have h : (fun xs ↦ R (t₁ xs) (t₂ xs)) = R'.subst ![t₁, t₂] := by
    funext xs
    simp [Multiclass.subst, R']
  rw [h]
  infer_instance

/-- A ternary `Σ₁` relation applied to `Σ₁` terms is `Σ₁` -/
instance [Nonempty M] {R : M → M → M → Prop}
    [hR : Multiclass.Sigma 1 (fun ys : Fin 3 → M ↦ R (ys 0) (ys 1) (ys 2)) P]
    {t₁ t₂ t₃ : (Fin n → M) → M} [h₁ : MulticlassFunction.Sigma t₁ 1 P]
    [h₂ : MulticlassFunction.Sigma t₂ 1 P] [h₃ : MulticlassFunction.Sigma t₃ 1 P] :
    Multiclass.Sigma 1 (fun xs ↦ R (t₁ xs) (t₂ xs) (t₃ xs)) P := by
  let R' : Multiclass M 3 := fun ys ↦ R (ys 0) (ys 1) (ys 2)
  have : ∀ i, MulticlassFunction.Sigma (![t₁, t₂, t₃] i) 1 P := by
    intro i
    fin_cases i <;> simpa
  have h : (fun xs ↦ R (t₁ xs) (t₂ xs) (t₃ xs)) = R'.subst ![t₁, t₂, t₃] := by
    funext xs
    simp [Multiclass.subst, R']
  rw [h]
  infer_instance

/-- A definable binary multiclass applied to `Σ₁` terms is definable -/
instance [Nonempty M] {A : Multiclass M 2} [A.Definable P] {t₁ t₂ : (Fin n → M) → M}
    [MulticlassFunction.Sigma t₁ 1 P] [MulticlassFunction.Sigma t₂ 1 P] :
    Multiclass.Definable (fun xs ↦ A ![t₁ xs, t₂ xs]) P := by
  have h : (fun xs ↦ A ![t₁ xs, t₂ xs]) = A.subst ![t₁, t₂] := by
    funext xs
    simp only [Multiclass.subst]
    congr
    ext i
    fin_cases i <;> rfl
  rw [h, Multiclass.subst_eq_ex']
  infer_instance

/-- A definable ternary multiclass applied to `Σ₁` terms is definable -/
instance [Nonempty M] {A : Multiclass M 3} [A.Definable P] {t₁ t₂ t₃ : (Fin n → M) → M}
    [MulticlassFunction.Sigma t₁ 1 P] [MulticlassFunction.Sigma t₂ 1 P]
    [MulticlassFunction.Sigma t₃ 1 P] :
    Multiclass.Definable (fun xs ↦ A ![t₁ xs, t₂ xs, t₃ xs]) P := by
  have : ∀ i, MulticlassFunction.Sigma (![t₁, t₂, t₃] i) 1 P := by
    intro i
    fin_cases i <;> simpa
  have h : (fun xs ↦ A ![t₁ xs, t₂ xs, t₃ xs]) = A.subst ![t₁, t₂, t₃] := by
    funext xs
    simp only [Multiclass.subst]
    congr
    ext i
    fin_cases i <;> rfl
  rw [h, Multiclass.subst_eq_ex']
  infer_instance

/-- A definable binary relation applied to `Σ₁` terms is definable -/
instance [Nonempty M] {R : M → M → Prop}
    [hR : Multiclass.Definable (fun ys : Fin 2 → M ↦ R (ys 0) (ys 1)) P]
    {t₁ t₂ : (Fin n → M) → M} [MulticlassFunction.Sigma t₁ 1 P]
    [MulticlassFunction.Sigma t₂ 1 P] :
    Multiclass.Definable (fun xs ↦ R (t₁ xs) (t₂ xs)) P := by
  let R' : Multiclass M 2 := fun ys ↦ R (ys 0) (ys 1)
  have h : (fun xs ↦ R (t₁ xs) (t₂ xs)) = R'.subst ![t₁, t₂] := by
    funext xs
    simp [Multiclass.subst, R']
  rw [h, Multiclass.subst_eq_ex']
  infer_instance

/-- A definable ternary relation applied to `Σ₁` terms is definable -/
instance [Nonempty M] {R : M → M → M → Prop}
    [hR : Multiclass.Definable (fun ys : Fin 3 → M ↦ R (ys 0) (ys 1) (ys 2)) P]
    {t₁ t₂ t₃ : (Fin n → M) → M} [MulticlassFunction.Sigma t₁ 1 P]
    [MulticlassFunction.Sigma t₂ 1 P] [MulticlassFunction.Sigma t₃ 1 P] :
    Multiclass.Definable (fun xs ↦ R (t₁ xs) (t₂ xs) (t₃ xs)) P := by
  let R' : Multiclass M 3 := fun ys ↦ R (ys 0) (ys 1) (ys 2)
  have : ∀ i, MulticlassFunction.Sigma (![t₁, t₂, t₃] i) 1 P := by
    intro i
    fin_cases i <;> simpa
  have h : (fun xs ↦ R (t₁ xs) (t₂ xs) (t₃ xs)) = R'.subst ![t₁, t₂, t₃] := by
    funext xs
    simp [Multiclass.subst, R']
  rw [h, Multiclass.subst_eq_ex']
  infer_instance

end Multiclass

namespace ClassFunction

/-- A definable class function composed with a definable class function is definable -/
instance {F G : ClassFunction M} [F.Definable Set.univ] [G.Definable Set.univ] :
    ClassFunction.Definable (fun x ↦ F (G x)) Set.univ :=
  .of_iff (F := fun xs : Fin 2 → M ↦ ∃ y, G (xs 0) = y ∧ F y = xs 1) fun u w ↦ by simp

/-- A definable binary function applied to definable class functions is definable -/
instance [Nonempty M] {H : M → M → M}
    [MulticlassFunction.Definable (fun ys : Fin 2 → M ↦ H (ys 0) (ys 1)) Set.univ]
    {F G : ClassFunction M} [F.Definable Set.univ] [G.Definable Set.univ] :
    ClassFunction.Definable (fun x ↦ H (F x) (G x)) Set.univ :=
  .of_iff (F := fun xs : Fin 2 → M ↦ ∃ a b, F (xs 0) = a ∧ G (xs 0) = b ∧
    MulticlassFunction.toMulticlass (fun ys : Fin 2 → M ↦ H (ys 0) (ys 1)) ![a, b, xs 1])
    fun u w ↦ by simp [MulticlassFunction.toMulticlass]

/-- A member `G p` of a family of class functions with a definable graph has a definable graph -/
instance {G : M → ClassFunction M}
    [Multiclass.Definable (fun xs : Fin 3 → M ↦ G (xs 0) (xs 1) = xs 2) Set.univ] (p : M) :
    (G p : Multiclass M 2).Definable Set.univ := by
  let R : Multiclass M 3 := fun xs ↦ G (xs 0) (xs 1) = xs 2
  have : (G p : Multiclass M 2) = (R.remap ![2, 0, 1]).slice ![p] := by
    funext xs
    rw [← Matrix.vec_fin_two_eq xs, ClassFunction.toMulticlass_vec_iff]
    simp [R, Multiclass.slice, Multiclass.remap, Matrix.comp_vecCons, Matrix.empty_eq]
  rw [this]
  infer_instance

end ClassFunction

end FirstOrder.Language.MemStructure
