import Mathlib.ModelTheory.Bundled

open FirstOrder Language BoundedFormula Theory

variable {α : Type*} {L : FirstOrder.Language}

noncomputable instance (T : L.Theory) (M : T.ModelType) : Inhabited M :=
  Classical.inhabited_of_nonempty'
