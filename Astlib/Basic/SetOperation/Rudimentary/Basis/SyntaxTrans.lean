import Astlib.Basic.SetOperation.Rudimentary.Basis.Syntax

open FirstOrder Language Structure BoundedFormula DeltaZeroBoundedFormula RudimentaryTerm Fin MemStructure

variable {L : Language.{u, v}} [L.HasMem]

namespace FirstOrder.Language

namespace RudimentaryBasisTerm

def graph (r : L.RudimentaryBasisTerm n) : L.RudimentaryBasisTerm n :=
  r.orderedPair r

end RudimentaryBasisTerm

namespace RudimentaryTerm

def toRudimentaryBasisTerm (r : L.RudimentaryTerm n) : L.RudimentaryBasisTerm n :=
  match r with
  | var i => .var i
  | const c => .const c
  | unorderedPair r₁ r₂ => .unorderedPair r₁.toRudimentaryBasisTerm r₂.toRudimentaryBasisTerm
  | sdiff r₁ r₂ => .sdiff r₁.toRudimentaryBasisTerm r₂.toRudimentaryBasisTerm
  | iUnion ri rf => sorry
  | char R r => sorry

end RudimentaryTerm

end FirstOrder.Language
