/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
-- import Astlib.Basic.SetOperation.MemStructure.Semantics
import Astlib.Basic.SetOperation.Rudimentary.DeltaZero
import Astlib.Basic.SetOperation.Empty
/-!
file docstring
-/

open FirstOrder Language BoundedFormula RudimentaryTerm Fin MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M] [RudClosed M] (x : M)

namespace FirstOrder.Language

def RudimentaryTerm.sUnion₀ {L : FirstOrder.Language} [L.HasMem] : L.RudimentaryTerm 1 :=
  (ᵣ0).iUnion (ᵣ1)

@[simp]
def RudimentaryTerm.sUnion {n} {L : FirstOrder.Language} [L.HasMem]
  (r : L.RudimentaryTerm n) := sUnion₀.substBoundRud ![r]
  -- (r : L.RudimentaryTerm n) := iUnion r (ᵣ(last _))

@[inherit_doc] prefix:110 "ᵣ⋃₀ " => FirstOrder.Language.RudimentaryTerm.sUnion

instance {L : FirstOrder.Language} [L.HasMem] :
  (sUnion₀ : L.RudimentaryTerm 1).CharFree := by
  unfold sUnion₀; infer_instance

instance {n} {L : FirstOrder.Language} [L.HasMem]
  (r : L.RudimentaryTerm n) [r.CharFree] :
  (ᵣ⋃₀ r).CharFree := by
  unfold sUnion; infer_instance


namespace MemStructure

variable (x y a : M)

/-- `⋃ x` in set theory, denoted by `⋃₀ x` in lean -/
noncomputable def sUnion : ClassFunction M := fun x ↦ sUnion₀〘x〙₁

instance [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] :
    (sUnion : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq sUnion₀ fun _ ↦ rfl

@[inherit_doc] prefix:110 "⋃₀ " => sUnion

omit [RudClosed M] in
@[grind =]
theorem sUnion_eq : ⋃₀ x = iUnion x id := by
  simp [sUnion, sUnion₀, realize_iUnion]
  rfl

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_sUnion₀ (xs : Fin 1 → M) :
    sUnion₀〘xs〙 = (⋃₀ xs 0 : M) := by
  simp [sUnion_eq, sUnion₀, realize_iUnion]
  rfl

@[simp, grind =]
theorem mem_sUnion_iff : x ∈ ⋃₀ a ↔ ∃ y ∈ a, x ∈ y := by
  simp only [sUnion, sUnion₀, mem_realize_iUnion_iff]
  simp

theorem eq_sUnion_iff [Extensional M] : x = ⋃₀ a ↔
    (∀ z ∈ x, ∃ y ∈ a, z ∈ y) ∧ ∀ y ∈ a, ∀ z ∈ y, z ∈ x :=
  ⟨by grind, fun _ ↦ by ext; grind⟩

@[simp, grind! ., push]
theorem sUnion_empty [Extensional M] : ⋃₀ (∅ : M) = ∅ := by
  ext; grind

theorem sUnion_mono {x y : M} (h : x ⊆ y) : ⋃₀ x ⊆ ⋃₀ y := by
  intro z
  simp only [mem_sUnion_iff]
  exact fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, h hw₁, hw₂⟩

end MemStructure

end FirstOrder.Language
