/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.MemStructure.Defs
import Astlib.Basic.SetOperation.Subset
import Astlib.Basic.Axiom.KP.Semantics
/-!
file docstring
-/

namespace FirstOrder.Language.MemStructure

open Fin

variable {L : FirstOrder.Language} {M : Type*} [L.MemStructure M]

variable (M) in
/- `M` is extensional -/
class Extensional : Prop where
  protected extensional : ∀ x y : M, ((∀ z : M, (z ∈ x ↔ z ∈ y)) → x = y)

variable [Extensional M] {x y : M}

@[ext]
theorem ext (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y :=
  Extensional.extensional x y h

theorem eq_iff : x = y ↔ (∀ z, z ∈ x ↔ z ∈ y) :=
  MemStructure.ext_iff

@[grind .]
theorem eq_of_subset_of_subset (h : x ⊆ y) (h' : y ⊆ x) :
    x = y := by
  ext; grind

theorem eq_iff' :
    x = y ↔ x ⊆ y ∧ y ⊆ x:= by
  grind

instance : Std.Antisymm (α := M) Subset where
  antisymm := fun _ _ h h' ↦ eq_of_subset_of_subset h h'

/-- A class function is definable if membership in its values is a definable relation -/
theorem ClassFunction.Definable.of_mem_iff {G : ClassFunction M} {R : M → M → Prop}
    [hR : Multiclass.Definable (fun ys : Fin 2 → M ↦ R (ys 0) (ys 1)) Set.univ]
    (h : ∀ x z, z ∈ G x ↔ R x z) : G.Definable Set.univ := by
  -- `[x, v, z]`: `z ∈ v ↔ R x z`
  let R' : Multiclass M 2 := fun ys ↦ R (ys 0) (ys 1)
  refine .of_iff (F := (Multiclass.Mem 2 1 ⇔ R'.remap ![0, 2] : Multiclass M 3).all) fun u w ↦ ?_
  suffices (∀ z, z ∈ w ↔ R u z) ↔ G u = w by
    simpa [R', Multiclass.remap, Multiclass.Mem, Matrix.comp_vecCons, Matrix.empty_eq] using this
  refine ⟨fun hw ↦ ?_, fun hw z ↦ hw ▸ h u z⟩
  ext z
  rw [h, hw]

section KP

open FirstOrder Language BoundedFormula

/-- Models of `KP` are extensional -/
instance [hM : ModelsKP₀ M] : Extensional M where
  extensional := by
    replace hM := hM.modelsKP₀
    simp only [KP₀, Theory.model_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      realize_iff_realize'] at hM
    specialize hM extensionalityAxiom (by simp)
    simpa [extensionalityAxiom, snoc_nat] using hM

end KP

end FirstOrder.Language.MemStructure
