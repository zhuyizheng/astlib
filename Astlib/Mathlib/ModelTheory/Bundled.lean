/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.ModelTheory.Bundled

/-!
file docstring
-/

open FirstOrder Language BoundedFormula Theory

variable {α : Type*} {L : FirstOrder.Language}

noncomputable instance (T : L.Theory) (M : T.ModelType) : Inhabited M :=
  Classical.inhabited_of_nonempty'
