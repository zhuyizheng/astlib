/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.SDiff
import Astlib.Basic.SetOperation.Singleton
import Astlib.Basic.SetOperation.Powerset
/-!
file docstring
-/

open FirstOrder Language RudimentaryTerm BoundedFormula Fin

namespace FirstOrder.Language

instance {n} {L : FirstOrder.Language} [L.HasMem] :
  SProd (L.RudimentaryTerm n) (L.RudimentaryTerm n) (L.RudimentaryTerm n) :=
  ⟨fun r₁ r₂ ↦ ((ᵣ0).iUnion ((ᵣ1).iUnion {ᵣ(ᵣ2, ᵣ3)})).substBoundRud ![r₁, r₂]⟩

@[simp]
theorem castLHom_sprod {M : MemStructure}
    (r₁ r₂ : M.L'.RudimentaryTerm n) :
    (r₁ ×ˢ r₂).castLHom = r₁.castLHom ×ˢ r₂.castLHom := by
  simp only [SProd.sprod, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, castLHom_substBoundRud,
    castLHom_iUnion, castLHom_var, castLHom_singleton, castLHom_orderedPair]
  congr
  ext i; fin_cases i <;> simp

namespace MemStructure

variable {M : MemStructure} (x y z x₁ x₂ y₁ y₂ u v : M)

noncomputable def sprod (x y : M) : M :=
  ((ᵣ0 : M.L.RudimentaryTerm 2) ×ˢ (ᵣ1 : M.L.RudimentaryTerm 2)) 〘x, y〙₂

noncomputable instance : SProd M M M :=
  ⟨fun x y ↦ ((ᵣ0 : M.L.RudimentaryTerm 2) ×ˢ (ᵣ1 : M.L.RudimentaryTerm 2)) 〘x, y〙₂⟩

theorem sprod_eq : x ×ˢ y = iUnion x (fun u ↦ iUnion y fun v ↦ {!(u, v)}) := by
  simp only [SProd.sprod, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, realize_substBoundRud,
    realize_iUnion, realize_basic, Matrix.cons_val_zero, realize_singleton, realize_orderedPair]
  rfl

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_sprod (r₁ r₂ : M.L.RudimentaryTerm n) (xs : Fin n → M) : (r₁ ×ˢ r₂)〘xs〙 = r₁〘xs〙 ×ˢ r₂〘xs〙 := by
  simp only [SProd.sprod, Nat.succ_eq_add_one, Nat.reduceAdd, isValue, realize_substBoundRud]
  congr
  ext i; fin_cases i <;>simp

variable [M.RudClosed]

@[simp, grind =]
theorem mem_sprod_iff : z ∈ x ×ˢ y ↔ ∃ u ∈ x, ∃ v ∈ y, z = !(u, v) := by
  simp [SProd.sprod, snoc_nat]

@[grind .]
theorem isOrderedPair_of_mem_sprod (h : z ∈ x ×ˢ y) : IsOrderedPair z := by
  grind

@[simp, grind =]
theorem pair_mem_sprod_iff [M.Extensional] :
    !(u, v) ∈ x ×ˢ y ↔ u ∈ x ∧ v ∈ y := by
  grind

theorem mem_sprod (hu : u ∈ x) (hv : v ∈ y) : !(u, v) ∈ x ×ˢ y := by
  grind

@[simp, grind =]
theorem sprod_empty [M.Extensional] :
    x ×ˢ (∅ : M) = ∅ := by
  ext; grind

@[simp, grind =]
theorem empty_sprod [M.Extensional] :
    (∅ : M) ×ˢ x = ∅ := by
  ext; grind

@[simp, grind =]
theorem singleton_sprod_singleton [M.Extensional]
    :
    ({x} : M) ×ˢ ({y} : M) = {!(x, y)} := by
  ext; grind

theorem sprod_mono_left {x₁ x₂ : M} (h : x₁ ⊆ x₂) : x₁ ×ˢ y ⊆ x₂ ×ˢ y := by
  grind

theorem sprod_mono_right {y₁ y₂ : M} (h : y₁ ⊆ y₂) : x ×ˢ y₁ ⊆ x ×ˢ y₂ := by
  grind

theorem union_sprod [M.Extensional] :
    (x₁ ∪ x₂) ×ˢ y = x₁ ×ˢ y ∪ x₂ ×ˢ y := by
  ext; grind

theorem sprod_union [M.Extensional] :
    x ×ˢ (y₁ ∪ y₂) = x ×ˢ y₁ ∪ x ×ˢ y₂ := by
  ext
  simp only [mem_sprod_iff]
  grind

theorem inter_sprod [M.Extensional] :
    (x₁ ∩ x₂) ×ˢ y = x₁ ×ˢ y ∩ x₂ ×ˢ y := by
  ext z
  simp only [mem_sprod_iff]
  constructor
  · grind
  · intro h
    simp only [mem_inter_iff, mem_sprod_iff] at h
    obtain ⟨⟨u, hu, v, hv, huv⟩, ⟨u', hu', v', hv', huv'⟩⟩ := h
    grind

theorem sprod_inter [M.Extensional] :
    x ×ˢ (y₁ ∩ y₂) = x ×ˢ y₁ ∩ x ×ˢ y₂ := by
  ext
  simp only [mem_sprod_iff, mem_inter_iff]
  grind


theorem sdiff_sprod [M.Extensional] :
    (x₁ \ x₂) ×ˢ y = x₁ ×ˢ y \ x₂ ×ˢ y := by
  ext
  simp only [mem_sprod_iff, mem_sdiff_iff, not_exists, not_and]
  grind

theorem sprod_sdiff [M.Extensional] :
    x ×ˢ (y₁ \ y₂) = x ×ˢ y₁ \ x ×ˢ y₂ := by
  ext
  simp only [mem_sprod_iff, mem_sdiff_iff, not_exists, not_and]
  grind

theorem sprod_inter_sprod [M.Extensional]
    :
    x₁ ×ˢ y₁ ∩ x₂ ×ˢ y₂ = (x₁ ∩ x₂) ×ˢ (y₁ ∩ y₂) := by
  ext z; simp only [mem_inter_iff, mem_sprod_iff]
  exact ⟨fun ⟨⟨u₁, hu₁, v₁, hv₁, hz₁⟩, ⟨u₂, hu₂, v₂, hv₂, hz₂⟩⟩ ↦ ⟨u₁, (by grind), v₁, (by grind)⟩,
    fun ⟨u, hu, v, hv, hz⟩ ↦ ⟨⟨u, by grind, v, by grind, hz⟩, ⟨u, by grind, v, by grind, hz⟩⟩⟩

end FirstOrder.Language.MemStructure
