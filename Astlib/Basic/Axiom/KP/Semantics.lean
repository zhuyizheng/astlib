/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Axiom.KP.Syntax
/-!
file docstring
-/

namespace FirstOrder

namespace Language

open FirstOrder Language BoundedFormula Fin

variable {L : FirstOrder.Language.{u, v}} {M : Type max u v}
  [L.MemStructure M] [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M]

class ModelsKP {L : FirstOrder.Language.{u, v}} (M : Type max u v) [h : L.MemStructure M] where
  modelsKP : @Theory.Model L M h.toStructure KP

end Language

end FirstOrder
