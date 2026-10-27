/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Ordinal.Basic
import Astlib.Basic.Ordinal.Order
import Astlib.Basic.SetOperation.PrimitiveRecursive.Semantics
/-!
# The ordinal `ω`

`ω` is the smallest nonzero limit ordinal, if it exists (`HasOmega M`). Its elements are the
natural numbers (`IsNat`): the ordinals `n` such that neither `n` nor any element of `n` is a
nonzero limit ordinal (`mem_omega_iff`).

* In a structure closed under rudimentary functions satisfying foundation, `ω` exists if there is
  a set containing `∅` and closed under `succ` (`hasOmega_of_inductive`), in particular if the axiom
  of infinity holds (`hasOmega_of_infinityAxiom`).
* `omega_induction`: induction on `ω` for definable classes in models of `KP`.
* `natRec a G`: recursion on `ω` in models of `KP`, with `natRec a G ∅ = a` and
  `natRec a G (succ n) = G (natRec a G n)`.
* `(n : M)`: the natural number `n : ℕ` as an element of `M`.
-/

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin RudimentaryTerm MemStructure

namespace FirstOrder.Language

namespace RudimentaryTerm

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] {n : ℕ}

/-- The `Δ₀` formula saying that `t` is a natural number -/
noncomputable def isNat (t : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (ᵣ0).isOrdinal ⊓ ∼(ᵣ0).isNonZeroLimOrdinal ⊓ (∀₀∈ &0 ∼(ᵣ1).isNonZeroLimOrdinal)
    |>.substBoundRud ![t]

instance (t : L.RudimentaryTerm n) [t.CharFree] : t.isNat.RelFree := by
  unfold isNat; infer_instance

/-- The `Δ₀` formula saying that `t` is `ω` -/
noncomputable def isOmega (t : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (ᵣ0).isNonZeroLimOrdinal ⊓ (∀₀∈ &0 ∼(ᵣ1).isNonZeroLimOrdinal) |>.substBoundRud ![t]

instance (t : L.RudimentaryTerm n) [t.CharFree] : t.isOmega.RelFree := by
  unfold isOmega; infer_instance

end RudimentaryTerm

namespace MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [RudClosed M] [Extensional M]
  {a m n w : M}

section Nat

/-- `n` is a natural number: an ordinal such that neither `n` nor any element of `n` is a nonzero
limit ordinal -/
def IsNat : Class M := fun n ↦ Ordinal n ∧ ¬NonZeroLimOrdinal n ∧ ∀ m ∈ n, ¬NonZeroLimOrdinal m

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isNat {k : ℕ}
    (t : L.RudimentaryTerm k) [t.CharFree] (xs : Fin k → M) :
    t.isNat.toBoundedFormula 〘xs〙 ↔ IsNat (t〘xs〙 : M) := by
  simp [isNat, IsNat, snoc_nat, and_assoc]

instance : (IsNat : Class M).DeltaZero Set.univ := by
  unfold IsNat
  infer_instance

omit [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] in
@[simp, grind .]
theorem IsNat.ordinal (hn : IsNat n) : Ordinal n := hn.left

omit [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] in
@[grind .]
theorem IsNat.not_nonZeroLimOrdinal (hn : IsNat n) : ¬NonZeroLimOrdinal n := hn.right.left

omit [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] in
@[grind .]
theorem IsNat.not_nonZeroLimOrdinal_of_mem (hn : IsNat n) (hm : m ∈ n) : ¬NonZeroLimOrdinal m :=
  hn.right.right m hm

@[simp, grind .]
theorem isNat_empty : IsNat (∅ : M) := by
  simp [IsNat]

variable [Foundational M]

@[grind .]
theorem IsNat.of_mem (hn : IsNat n) (hm : m ∈ n) : IsNat m :=
  ⟨ordinal_of_mem hn.ordinal hm, hn.not_nonZeroLimOrdinal_of_mem hm,
    fun _ hk ↦ hn.not_nonZeroLimOrdinal_of_mem (by grind)⟩

omit [Foundational M] in
@[grind .]
theorem isNat_succ (hn : IsNat n) : IsNat (succ n) :=
  ⟨ordinal_succ hn.ordinal, not_nonZeroLimOrdinal_succ n, fun m hm ↦ by grind⟩

/-- Every natural number lies in every set containing `∅` and closed under `succ` on natural
numbers -/
theorem IsNat.mem_of_inductive (hn : IsNat n) (h0 : ∅ ∈ a)
    (hs : ∀ x ∈ a, IsNat x → succ x ∈ a) : n ∈ a := by
  by_contra hna
  -- take an `∈`-minimal element `m` of `succ n` outside `a`
  let S := succ n ∩₀ ∼(toClass a)
  have hS (z : M) : z ∈ S ↔ z ∈ succ n ∧ z ∉ a := by simp [S, toClass]
  have hmS : memMin S ∈ S := memMin_mem (by grind)
  rw [hS] at hmS
  obtain ⟨hmn, hma⟩ := hmS
  have hm : IsNat (memMin S) := by grind
  obtain ⟨k, -, hk⟩ := hm.ordinal.exists_eq_succ (by grind) (by grind)
  have hkm : k ∈ memMin S := by simp [hk]
  have : k ∈ succ n := (ordinal_succ hn.ordinal).transitive _ hmn hkm
  grind

end Nat

section Omega

/-- `w` is `ω`: the smallest nonzero limit ordinal -/
def IsOmega : Class M := fun w ↦ NonZeroLimOrdinal w ∧ ∀ β ∈ w, ¬NonZeroLimOrdinal β

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isOmega {k : ℕ}
    (t : L.RudimentaryTerm k) [t.CharFree] (xs : Fin k → M) :
    t.isOmega.toBoundedFormula 〘xs〙 ↔ IsOmega (t〘xs〙 : M) := by
  simp [isOmega, IsOmega, snoc_nat]

omit [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] in
@[grind .]
theorem IsOmega.nonZeroLimOrdinal (hw : IsOmega w) : NonZeroLimOrdinal w := hw.left

omit [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] in
@[grind .]
theorem IsOmega.not_nonZeroLimOrdinal_of_mem (hw : IsOmega w) (hn : n ∈ w) :
    ¬NonZeroLimOrdinal n :=
  hw.right n hn

noncomputable instance : Decidable (∃ w : M, IsOmega w) := Classical.propDecidable _

/-- `ω`, the smallest nonzero limit ordinal, if it exists -/
noncomputable def omega : M := dite (∃ w : M, IsOmega w) Classical.choose fun _ ↦ default

@[inherit_doc] notation "ω" => omega

variable (M) in
/-- `M` has a smallest nonzero limit ordinal `ω` -/
class HasOmega : Prop where
  protected exists_isOmega : ∃ w : M, IsOmega w

variable [Foundational M]

/-- The elements of `ω` are the natural numbers -/
theorem IsOmega.mem_iff (hw : IsOmega w) : n ∈ w ↔ IsNat n := by
  have hwo : NonZeroLimOrdinal w := hw.nonZeroLimOrdinal
  refine ⟨fun hn ↦ ⟨ordinal_of_mem hwo.ordinal hn, hw.not_nonZeroLimOrdinal_of_mem hn,
    fun _ hm ↦ hw.not_nonZeroLimOrdinal_of_mem (by grind)⟩, fun hn ↦ ?_⟩
  exact IsNat.mem_of_inductive hn hwo.empty_mem fun x hx _ ↦ hwo.succ_mem hx

omit [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] [Foundational M] in
theorem isOmega_omega [h : HasOmega M] : IsOmega (ω : M) := by
  have h' : ∃ w, IsOmega w := h.exists_isOmega
  simp only [omega, h']
  grind

/-- A smallest nonzero limit ordinal is `ω` -/
theorem IsOmega.unique (hw : IsOmega w) : w = ω := by
  have : HasOmega M := ⟨⟨w, hw⟩⟩
  ext n
  simp only [hw.mem_iff, isOmega_omega.mem_iff]

@[simp]
theorem isOmega_iff [HasOmega M] : IsOmega w ↔ w = ω :=
  ⟨IsOmega.unique, by rintro rfl; exact isOmega_omega⟩

@[simp, grind =]
theorem mem_omega_iff [HasOmega M] : n ∈ (ω : M) ↔ IsNat n := isOmega_omega.mem_iff

omit [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] [Foundational M] in
@[grind .]
theorem nonZeroLimOrdinal_omega [HasOmega M] : NonZeroLimOrdinal (ω : M) :=
  isOmega_omega.nonZeroLimOrdinal

omit [Foundational M] in
@[simp, grind .]
theorem ordinal_omega [HasOmega M] : Ordinal (ω : M) := nonZeroLimOrdinal_omega.ordinal

@[simp, grind .]
theorem empty_mem_omega [HasOmega M] : ∅ ∈ (ω : M) := nonZeroLimOrdinal_omega.empty_mem

@[grind .]
theorem succ_mem_omega [HasOmega M] (hn : n ∈ (ω : M)) : succ n ∈ (ω : M) :=
  nonZeroLimOrdinal_omega.succ_mem hn

/-- A member of `ω` is `∅` or the successor of a member of `ω` -/
theorem mem_omega_cases [HasOmega M] (hn : n ∈ (ω : M)) :
    n = ∅ ∨ ∃ m ∈ (ω : M), n = succ m := by
  have : Ordinal n := by grind
  rcases this.cases <;> grind

/-- `ω` exists if some set contains `∅` and is closed under `succ` -/
theorem hasOmega_of_inductive (h0 : ∅ ∈ a) (hs : ∀ x ∈ a, succ x ∈ a) : HasOmega M := by
  -- `ω` consists of the natural numbers in `a`
  let w := a ∩₀ IsNat
  have hw (n : M) : n ∈ w ↔ IsNat n := by
    simp only [w, mem_comprehension_iff, and_iff_right_iff_imp]
    exact fun hn ↦ IsNat.mem_of_inductive hn h0 fun x hx _ ↦ hs x hx
  have hword : Ordinal w := ⟨by grind, by grind [ordinal_compatible]⟩
  exact ⟨w, ⟨⟨hword, fun ⟨_, _, _⟩ ↦ by grind⟩, by grind⟩, by grind⟩

/-- `ω` exists if the axiom of infinity holds -/
theorem hasOmega_of_infinityAxiom (h : M ⊨ (infinityAxiom : L.Sentence)) : HasOmega M := by
  replace h : ∃ a : M, (∃ e ∈ a, ∀ z, z ∉ e) ∧ ∀ x ∈ a, ∃ y ∈ a, ∀ z, z ∈ y ↔ z = x ∨ z ∈ x := by
    simpa [infinityAxiom, snoc_nat] using h
  obtain ⟨a, ⟨e, he, he'⟩, ha⟩ := h
  refine hasOmega_of_inductive (a := a) ?_ fun x hx ↦ ?_
  · convert he
    rw [eq_comm, empty_iff]
    exact he'
  · obtain ⟨y, hy, hy'⟩ := ha x hx
    convert hy
    ext z
    grind

/-- Models of `KPInf` contain `ω` -/
instance [hM : ModelsKPInf M] : HasOmega M :=
  hasOmega_of_infinityAxiom (hM.modelsKPInf.realize_of_mem _ (by simp [KPInf]))

end Omega

section KP

variable [ModelsKP M]

/-- Induction on `ω` for definable classes in models of `KP` -/
theorem omega_induction [HasOmega M] {A : Class M} [A.Definable Set.univ] (h0 : A ∅)
    (hs : ∀ n ∈ (ω : M), A n → A (succ n)) (hn : n ∈ (ω : M)) : A n := by
  -- induct on the definable class `x ∈ ω → A x`
  suffices h : (Class.Mem ω ⟹ A) n by
    tauto
  refine ordinal_induction (fun x hx ih ↦ ?_) (ordinal_of_mem ordinal_omega hn)
  simp only [Class.imp_iff, Class.mem_iff] at ih ⊢
  intro hxω
  rcases mem_omega_cases hxω with rfl | ⟨k, hk, rfl⟩ <;> grind

/-- Two `Σ₁` class functions agree on `ω` if they agree at `∅` and agreement passes to
successors -/
theorem omega_induction_eq [HasOmega M] {F G : ClassFunction M} [F.Sigma 1 Set.univ]
    [G.Sigma 1 Set.univ] (h0 : F ∅ = G ∅)
    (hs : ∀ n ∈ (ω : M), F n = G n → F (succ n) = G (succ n)) (hn : n ∈ (ω : M)) :
    F n = G n :=
  omega_induction (A := fun x ↦ F x = G x) h0 hs hn

noncomputable instance (f : M) : Decidable (f = ∅) := Classical.propDecidable _

/-- The step of recursion on `ω`: `∅ ↦ a` and `f ↦ G (f ﹫ ⋃₀ dom f)` for `f ≠ ∅` -/
noncomputable def natRecStep (a : M) (G : ClassFunction M) : ClassFunction M := fun f ↦
  if f = ∅ then a else G (f ﹫ ⋃₀ dom f)

instance (a : M) (G : ClassFunction M) [G.Sigma 1 Set.univ] :
    (natRecStep a G).Sigma 1 Set.univ := by
  refine ClassFunction.Sigma.of_iff (F := fun xs ↦
    (xs 0 = ∅ ∧ xs 1 = a) ∨ (¬xs 0 = ∅ ∧ G (xs 0 ﹫ ⋃₀ dom (xs 0)) = xs 1))
    (hF := by infer_instance) fun f v ↦ ?_
  by_cases hf : f = ∅ <;> simp [natRecStep, hf, eq_comm]

/-- The class function defined by `∈`-recursion from a `Σ₁` class function restricts to every set -/
theorem isSetRestrictedTo_recursion {H : ClassFunction M} [H.Sigma 1 Set.univ] (x : M) :
    IsSetRestrictedTo (recursion H) x := by
  obtain ⟨F, hF⟩ := exists_isRecursion H
  rw [← hF.eq_recursion exists_mem_transitive_of_modelsKP]
  exact hF.left x

/-- Recursion on `ω`: `natRec a G ∅ = a` and `natRec a G (succ n) = G (natRec a G n)` -/
noncomputable def natRec (a : M) (G : ClassFunction M) : ClassFunction M :=
  recursion (natRecStep a G)

instance (a : M) (G : ClassFunction M) [G.Sigma 1 Set.univ] : (natRec a G).Sigma 1 Set.univ := by
  unfold natRec; infer_instance

variable (a : M) (G : ClassFunction M) [G.Sigma 1 Set.univ]

@[simp]
theorem natRec_empty : natRec a G ∅ = a := by
  simp only [natRec, recursion_eq_of_modelsKP]
  have h : IsSetRestrictedTo (recursion (natRecStep a G)) ∅ :=
    isSetRestrictedTo_recursion (H := natRecStep a G) ∅
  have : recursion (natRecStep a G) ↾₀ ∅ = ∅ :=
    (isFunction_toSetRestrictedTo h).isRelation.eq_empty_of_dom_eq_empty (dom_toSetRestrictedTo h)
  simp [natRecStep, this]

theorem natRec_succ (hn : Ordinal n) : natRec a G (succ n) = G (natRec a G n) := by
  rw [natRec, recursion_eq_of_modelsKP]
  have h : IsSetRestrictedTo (recursion (natRecStep a G)) (succ n) :=
    isSetRestrictedTo_recursion (H := natRecStep a G) (succ n)
  have hne : recursion (natRecStep a G) ↾₀ succ n ≠ ∅ := by
    grind [dom_toSetRestrictedTo h]
  simp [natRecStep, hne, dom_toSetRestrictedTo h, sUnion_succ hn.transitive,
    val_toSetRestrictedTo h (mem_succ_self n)]

variable {a G} in
/-- Induction along `natRec a G`: a definable property holds for `natRec a G n` for `n ∈ ω` if it
holds for `a` and is preserved by `G` -/
theorem natRec_induction [HasOmega M] {A : Class M} [A.Definable Set.univ]
    (h0 : A a) (hs : ∀ n ∈ (ω : M), A (natRec a G n) → A (G (natRec a G n))) (hn : n ∈ (ω : M)) :
    A (natRec a G n) := by
  refine omega_induction (A := fun n ↦ A (natRec a G n)) (by rwa [natRec_empty])
    (fun n hn ih ↦ ?_) hn
  rw [natRec_succ _ _ (ordinal_of_mem ordinal_omega hn)]
  exact hs n hn ih

end KP

section NatCast

/-- The natural number `n` as an element of `M` -/
noncomputable def natCast : ℕ → M
  | 0 => ∅
  | n + 1 => succ (natCast n)

noncomputable instance : NatCast M := ⟨natCast⟩

omit [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] in
@[simp, norm_cast, grind =]
theorem natCast_zero : ((0 : ℕ) : M) = ∅ := rfl

omit [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] in
@[simp, norm_cast, grind =]
theorem natCast_succ (k : ℕ) : ((k + 1 : ℕ) : M) = succ (k : M) := rfl

variable [Foundational M]

omit [Foundational M] in
@[simp, grind .]
theorem isNat_natCast (k : ℕ) : IsNat (k : M) := by
  induction k with
  | zero => exact isNat_empty
  | succ k ih => exact isNat_succ ih

@[simp, grind .]
theorem natCast_mem_omega [HasOmega M] (k : ℕ) : (k : M) ∈ (ω : M) := by
  simp only [mem_omega_iff]
  exact isNat_natCast k

omit [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [Foundational M] in
theorem natCast_mem_natCast_of_lt {j k : ℕ} (h : j < k) : (j : M) ∈ (k : M) := by
  induction k with
  | zero => simp at h
  | succ k ih =>
    simp only [Nat.lt_succ_iff_lt_or_eq] at h
    rcases h with h | rfl <;> grind

omit [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] in
theorem natCast_injective : Function.Injective (Nat.cast : ℕ → M) := by
  intro j k h
  by_contra! hjk
  rcases Nat.lt_or_gt_of_ne hjk with hjk | hjk
  · have hmem := natCast_mem_natCast_of_lt (M := M) hjk
    grind
  · have hmem := natCast_mem_natCast_of_lt (M := M) hjk
    grind

omit [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] in
@[simp, norm_cast]
theorem natCast_inj {j k : ℕ} : (j : M) = (k : M) ↔ j = k := natCast_injective.eq_iff

@[simp, norm_cast]
theorem natCast_mem_natCast_iff {j k : ℕ} : (j : M) ∈ (k : M) ↔ j < k := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, le_iff_eq_or_lt]

end NatCast

end MemStructure

end FirstOrder.Language
