/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Comprehension
/-!
file docstring
-/

open Fin FirstOrder Language MemStructure

namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type max u v}
  [L.MemStructure M] [Inhabited M]

namespace MemStructure

def IsReplacement (b : M) (F : Multiclass M 2) (a : M) := ∀ z, z ∈ b ↔ ∃ u ∈ a, F ![u, z]

noncomputable instance (F : Multiclass M 2) (a : M) :
  Decidable (∃ b : M, IsReplacement b F a) :=
  Classical.propDecidable _

/-- The pointwise image `{F u | u ∈ a}` of `a` under `F` -/
noncomputable def replacement (a : M) (F : Multiclass M 2) :=
  dite (∃ b : M, IsReplacement b F a)
    Classical.choose default

@[inherit_doc] scoped[FirstOrder.Language]
notation:88 F:89 " ''₀ " a:89 => FirstOrder.Language.MemStructure.replacement a F

/-- If `F` relates every `u ∈ a` to exactly one `w`, then the image `{F u | u ∈ a}` is a set -/
class HasReplacement (a : M) (F : Multiclass M 2) : Prop where
  protected hasReplacement : (∀ u ∈ a, ∃! w, F ![u, w]) → ∃ b : M, IsReplacement b F a

theorem mem_replacement_iff {a : M} {F : Multiclass M 2} [hF : HasReplacement a F]
    (hFa : ∀ u ∈ a, ∃! w, F ![u, w]) (z : M) :
    z ∈ F ''₀ a ↔ ∃ u ∈ a, F ![u, z] := by
  convert Classical.choose_spec (hF.hasReplacement hFa) z
  simp [MemStructure.replacement, hF.hasReplacement hFa]

theorem mem_replacement_of_mem {a : M} {F : Multiclass M 2} [HasReplacement a F]
    (hFa : ∀ u ∈ a, ∃! w, F ![u, w]) {u w : M} (hu : u ∈ a) (hw : F ![u, w]) :
    w ∈ F ''₀ a :=
  (mem_replacement_iff hFa w).2 ⟨u, hu, hw⟩

end MemStructure

end FirstOrder.Language
