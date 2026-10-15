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

def RudimentaryTerm.sprod₀ {L : FirstOrder.Language} [L.HasMem] : L.RudimentaryTerm 2 :=
  (ᵣ0).iUnion ((ᵣ1).iUnion {ᵣ(ᵣ2, ᵣ3)})

instance {n} {L : FirstOrder.Language} [L.HasMem] :
  SProd (L.RudimentaryTerm n) (L.RudimentaryTerm n) (L.RudimentaryTerm n) :=
  ⟨fun r₁ r₂ ↦ sprod₀.substBoundRud ![r₁, r₂]⟩

@[simp]
theorem RudimentaryTerm.sprod_def {L : FirstOrder.Language} [L.HasMem]
    (r₁ r₂ : L.RudimentaryTerm n) :
    r₁ ×ˢ r₂ = sprod₀.substBoundRud ![r₁, r₂] := rfl

instance {L : Language} [L.HasMem] :
  (sprod₀ : L.RudimentaryTerm 2).CharFree := by
  unfold sprod₀; infer_instance

namespace MemStructure

variable {L : Language.{u, v}} {M : Type max u v}
  [L.MemStructure M] [Inhabited M]
  (x y z x₁ x₂ y₁ y₂ u v : M)

noncomputable def sprod (x y : M) : M :=
  sprod₀ 〘x, y〙₂

noncomputable instance : SProd M M M :=
  ⟨fun x y ↦ sprod₀ 〘x, y〙₂⟩

instance {L : Language} [L.HasMem] (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] :
  (r ×ˢ s).CharFree := by
  rw [sprod_def]; infer_instance

theorem sprod_eq : x ×ˢ y = iUnion x (fun u ↦ iUnion y fun v ↦ {!(u, v)}) := by
  simp only [SProd.sprod, sprod₀, Nat.reduceAdd, isValue,
    realize_substBoundRud, realize_iUnion, realize_basic, Matrix.cons_val_zero, singleton_def,
    realize_singleton₀, realize_orderedPair]
  rfl

@[simp, grind =]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_sprod₀ (xs : Fin 2 → M) :
    RudimentaryTerm.sprod₀〘xs〙 = xs 0 ×ˢ xs 1 := by
  simp only [SProd.sprod]
  congr
  ext i; fin_cases i <;> rfl

variable [RudClosed M]

@[simp, grind =]
theorem mem_sprod_iff : z ∈ x ×ˢ y ↔ ∃ u ∈ x, ∃ v ∈ y, z = !(u, v) := by
  simp only [SProd.sprod, sprod₀]
  simp

@[grind .]
theorem isOrderedPair_of_mem_sprod (h : z ∈ x ×ˢ y) : IsOrderedPair z := by
  grind

@[simp, grind =]
theorem pair_mem_sprod_iff [Extensional M] :
    !(u, v) ∈ x ×ˢ y ↔ u ∈ x ∧ v ∈ y := by
  grind

theorem mem_sprod (hu : u ∈ x) (hv : v ∈ y) : !(u, v) ∈ x ×ˢ y := by
  grind

@[simp, grind =]
theorem sprod_empty [Extensional M] :
    x ×ˢ (∅ : M) = ∅ := by
  ext; grind

@[simp, grind =]
theorem empty_sprod [Extensional M] :
    (∅ : M) ×ˢ x = ∅ := by
  ext; grind

@[simp, grind =]
theorem singleton_sprod_singleton [Extensional M]
    :
    ({x} : M) ×ˢ ({y} : M) = {!(x, y)} := by
  ext; grind

theorem sprod_mono_left {x₁ x₂ : M} (h : x₁ ⊆ x₂) : x₁ ×ˢ y ⊆ x₂ ×ˢ y := by
  grind

theorem sprod_mono_right {y₁ y₂ : M} (h : y₁ ⊆ y₂) : x ×ˢ y₁ ⊆ x ×ˢ y₂ := by
  grind

theorem union_sprod [Extensional M] :
    (x₁ ∪ x₂) ×ˢ y = x₁ ×ˢ y ∪ x₂ ×ˢ y := by
  ext; grind

theorem sprod_union [Extensional M] :
    x ×ˢ (y₁ ∪ y₂) = x ×ˢ y₁ ∪ x ×ˢ y₂ := by
  ext
  simp only [mem_sprod_iff]
  grind

theorem inter_sprod [Extensional M] :
    (x₁ ∩ x₂) ×ˢ y = x₁ ×ˢ y ∩ x₂ ×ˢ y := by
  ext z
  simp only [mem_sprod_iff]
  constructor
  · grind
  · intro h
    simp only [mem_inter_iff, mem_sprod_iff] at h
    obtain ⟨⟨u, hu, v, hv, huv⟩, ⟨u', hu', v', hv', huv'⟩⟩ := h
    grind

theorem sprod_inter [Extensional M] :
    x ×ˢ (y₁ ∩ y₂) = x ×ˢ y₁ ∩ x ×ˢ y₂ := by
  ext
  simp only [mem_sprod_iff, mem_inter_iff]
  grind


theorem sdiff_sprod [Extensional M] :
    (x₁ \ x₂) ×ˢ y = x₁ ×ˢ y \ x₂ ×ˢ y := by
  ext
  simp only [mem_sprod_iff, mem_sdiff_iff, not_exists, not_and]
  grind

theorem sprod_sdiff [Extensional M] :
    x ×ˢ (y₁ \ y₂) = x ×ˢ y₁ \ x ×ˢ y₂ := by
  ext
  simp only [mem_sprod_iff, mem_sdiff_iff, not_exists, not_and]
  grind

theorem sprod_inter_sprod [Extensional M]
    :
    x₁ ×ˢ y₁ ∩ x₂ ×ˢ y₂ = (x₁ ∩ x₂) ×ˢ (y₁ ∩ y₂) := by
  ext z; simp only [mem_inter_iff, mem_sprod_iff]
  exact ⟨fun ⟨⟨u₁, hu₁, v₁, hv₁, hz₁⟩, ⟨u₂, hu₂, v₂, hv₂, hz₂⟩⟩ ↦ ⟨u₁, (by grind), v₁, (by grind)⟩,
    fun ⟨u, hu, v, hv, hz⟩ ↦ ⟨⟨u, by grind, v, by grind, hz⟩, ⟨u, by grind, v, by grind, hz⟩⟩⟩

end FirstOrder.Language.MemStructure
