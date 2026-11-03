/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Ordinal.Add
/-!
# Natural numbers

* `IsEven n`: `n = m +ₒ m` for some `m ∈ ω`, and `IsOdd n`: `n = succ (m +ₒ m)` for some
  `m ∈ ω`; both are `Σ₁`.

Every `n ∈ ω` is either even or odd and not both (`isEven_or_isOdd`, `IsEven.not_isOdd`), and
parity alternates (`isEven_succ_iff`, `isOdd_succ_iff`).
-/

open FirstOrder Language

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M]

/-- The natural number `n` is even -/
def IsEven : Class M := fun n ↦ ∃ m ∈ (ω : M), n = m +ₒ m

instance : Multiclass.Sigma 1 (fun ys : Fin 1 → M ↦ IsEven (ys 0)) Set.univ := by
  unfold IsEven; infer_instance

/-- The natural number `n` is odd -/
def IsOdd : Class M := fun n ↦ ∃ m ∈ (ω : M), n = succ (m +ₒ m)

instance : Multiclass.Sigma 1 (fun ys : Fin 1 → M ↦ IsOdd (ys 0)) Set.univ := by
  unfold IsOdd; infer_instance

variable [HasOmega M] {k n : M}

theorem isEven_empty : IsEven (∅ : M) :=
  ⟨∅, empty_mem_omega, (oadd_empty ordinal_empty).symm⟩

/-- `succ k +ₒ succ k = succ (succ (k +ₒ k))` -/
theorem succ_oadd_succ_self (hk : k ∈ (ω : M)) : succ k +ₒ succ k = succ (succ (k +ₒ k)) := by
  have hko : Ordinal k := ordinal_of_mem ordinal_omega hk
  rw [oadd_succ (ordinal_succ hko) hko, oadd_comm_of_mem_omega (succ_mem_omega hk) hk,
    oadd_succ hko hko]

omit [ModelsKP M] [HasOmega M] in
theorem IsEven.isOdd_succ (hn : IsEven n) : IsOdd (succ n) := by
  obtain ⟨k, hk, rfl⟩ := hn
  exact ⟨k, hk, rfl⟩

theorem IsOdd.isEven_succ (hn : IsOdd n) : IsEven (succ n) := by
  obtain ⟨k, hk, rfl⟩ := hn
  exact ⟨succ k, succ_mem_omega hk, (succ_oadd_succ_self hk).symm⟩

theorem isEven_or_isOdd (hn : n ∈ (ω : M)) : IsEven n ∨ IsOdd n := by
  refine omega_induction (A := fun n ↦ IsEven n ∨ IsOdd n) (.inl isEven_empty)
    (fun n _ ih ↦ ?_) hn
  rcases ih with h | h
  · exact .inr h.isOdd_succ
  · exact .inl h.isEven_succ

theorem IsEven.not_isOdd (hn : IsEven n) : ¬IsOdd n := by
  obtain ⟨k, hk, rfl⟩ := hn
  rintro ⟨l, hl, hkl⟩
  have hko : Ordinal k := ordinal_of_mem ordinal_omega hk
  have hlo : Ordinal l := ordinal_of_mem ordinal_omega hl
  have hll : Ordinal (l +ₒ l) := ordinal_oadd hlo hlo
  rcases ole_total hko hlo with h | h
  · -- `k +ₒ k ≤ l +ₒ l < succ (l +ₒ l)`
    have hle : k +ₒ k ≤ₒ l +ₒ l :=
      ole_trans (oadd_ole_oadd_right hko h) ((oadd_ole_oadd_iff_left hlo hko hlo).mpr h)
    rw [hkl] at hle
    exact olt_irrefl _ (olt_of_ole_of_olt hle (olt_succ hll))
  rcases mem_or_eq_of_ole h with h | rfl
  swap
  · have hlt := olt_succ hll
    rw [← hkl] at hlt
    exact olt_irrefl _ hlt
  -- `succ (l +ₒ l) < succ l +ₒ succ l ≤ k +ₒ k`
  have hsl : succ l ≤ₒ k := (succ_ole_iff hlo hko).mpr (olt_of_mem hko h)
  have hle : succ l +ₒ succ l ≤ₒ k +ₒ k :=
    ole_trans (oadd_ole_oadd_right (ordinal_succ hlo) hsl)
      ((oadd_ole_oadd_iff_left hko (ordinal_succ hlo) hko).mpr hsl)
  rw [succ_oadd_succ_self hl, hkl] at hle
  exact olt_irrefl _ (olt_of_ole_of_olt hle (olt_succ (ordinal_succ hll)))

theorem IsOdd.not_isEven (hn : IsOdd n) : ¬IsEven n := fun h ↦ h.not_isOdd hn

theorem not_isOdd_empty : ¬IsOdd (∅ : M) := isEven_empty.not_isOdd

theorem isOdd_iff_not_isEven (hn : n ∈ (ω : M)) : IsOdd n ↔ ¬IsEven n :=
  ⟨IsOdd.not_isEven, (isEven_or_isOdd hn).resolve_left⟩

theorem isEven_iff_not_isOdd (hn : n ∈ (ω : M)) : IsEven n ↔ ¬IsOdd n :=
  ⟨IsEven.not_isOdd, (isEven_or_isOdd hn).resolve_right⟩

theorem isEven_succ_iff (hn : n ∈ (ω : M)) : IsEven (succ n) ↔ IsOdd n := by
  refine ⟨fun h ↦ ?_, IsOdd.isEven_succ⟩
  rw [isOdd_iff_not_isEven hn]
  exact fun hn' ↦ hn'.isOdd_succ.not_isEven h

theorem isOdd_succ_iff (hn : n ∈ (ω : M)) : IsOdd (succ n) ↔ IsEven n := by
  refine ⟨fun h ↦ ?_, IsEven.isOdd_succ⟩
  rw [isEven_iff_not_isOdd hn]
  exact fun hn' ↦ hn'.isEven_succ.not_isOdd h

theorem mem_omega_of_mem_succ (hn : n ∈ (ω : M)) (hj : j ∈ succ n) : j ∈ (ω : M) :=
  ordinal_omega.transitive _ (succ_mem_omega hn) hj

theorem forall_mem_of_mem_succ {C : M → Prop} (hn : n ∈ (ω : M)) (ih : ∀ m ∈ n, C m)
    (hj : j ∈ succ n) : ∀ m ∈ j, C m := by
  intro m hm
  rcases mem_or_eq_of_mem_succ hj with hj | rfl
  · exact ih m ((ordinal_of_mem ordinal_omega hn).transitive _ hj hm)
  · exact ih m hm

theorem sUnion_mem_of_ne_empty (hj : j ∈ (ω : M)) (hj0 : j ≠ ∅) :
    ⋃₀ j ∈ (ω : M) ∧ ⋃₀ j ∈ j ∧ j = succ (⋃₀ j) := by
  rcases mem_omega_cases hj with rfl | ⟨m, hm, rfl⟩
  · exact (hj0 rfl).elim
  rw [sUnion_succ (ordinal_of_mem ordinal_omega hm).transitive]
  exact ⟨hm, mem_succ_self m, rfl⟩

end FirstOrder.Language.MemStructure
