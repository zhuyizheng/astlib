/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.ModelTheory.Defs
import Astlib.Basic.SetOperation.Subset
/-!
file docstring
-/

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure}

variable (M) in
/- `M` is extensional -/
class Extensional : Prop where
  protected extensional : ∀ x y : M, ((∀ z : M, (z ∈ x ↔ z ∈ y)) → x = y)

variable [M.Extensional] {x y : M}

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

end FirstOrder.Language.MemStructure
