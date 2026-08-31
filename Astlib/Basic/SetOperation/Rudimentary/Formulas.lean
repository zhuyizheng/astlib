import Astlib.Basic.SetOperation.Rudimentary.Syntax

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula RudimentaryTerm Fin


-- def BoundedFormula.toRudimentaryTerm (φ : L.BoundedFormula α n)

namespace DeltaZeroBoundedFormula

variable {n : ℕ} (i j k : Fin n)

-- def memSUnion (i j : Fin n) :=
--   (&0 ∈₀ &1).substBoundRud (![ᵣi, ᵣ⋃₀ ᵣj])

-- def eqSUnion (i j : Fin n) :=
--   (&0 =₀ &1).substBoundRud (![ᵣi, ᵣ⋃₀ ᵣj])

-- def memUnorderedPair (i j k : Fin n) :=
--   (&0 ∈₀ &1).substBoundRud (![ᵣi, ᵣ{ᵣj, ᵣk}])

-- def eqUnorderedPair (i j k : Fin n) :=
--   (&0 =₀ &1).substBoundRud (![ᵣi, ᵣ{ᵣj, ᵣk}])

-- def isUnorderedPair (i : Fin n) :=
--   ∃'∈ (ᵣi) ∃'∈ (ᵣi.castSucc) (eqUnorderedPair (i.castAdd 2)
--     (castSucc (last _)) (last _))

-- def memOrderedPair (i j k : Fin n) :=
--   (&0 ∈₀ &1).substBoundRud (![ᵣi, ᵣ(ᵣj, ᵣk)])

-- def eqOrderedPair (i j k : Fin n) :=
--   (&0 =₀ &1).substBoundRud (![ᵣi, ᵣ(ᵣj, ᵣk)])

-- def isOrderedPair (i : Fin n) :=
--   ∃'∈ (ᵣ⋃₀ ᵣi) ∃'∈ (ᵣ⋃₀ ᵣi.castSucc) (eqOrderedPair (i.castAdd 2)
--     (castSucc (last _)) (last _))

-- def eqLeft (i j : Fin n) := ∃'∈ (ᵣ⋃₀ ᵣj) (eqOrderedPair j.castSucc i.castSucc (last _))

-- def eqRight (i j : Fin n) := ∃'∈ (ᵣ⋃₀ ᵣj) (eqOrderedPair j.castSucc (last _) i.castSucc)

-- def sameLeft (i j : Fin n) := ∃'∈ (ᵣ⋃₀ ᵣi)
--   (eqLeft (last _) i.castSucc ⊓ eqLeft (last _) j.castSucc)

-- def rightEqLeft (i j : Fin n) := ∃'∈ (ᵣ⋃₀ ᵣi)
--   (eqRight (last _) i.castSucc ⊓ eqLeft (last _) j.castSucc)

-- def sameLeftRight (i : Fin n) := rightEqLeft i i

-- def reverseLeftRight (i j : Fin n) := rightEqLeft i j ⊓ rightEqLeft j i



-- end DeltaZeroBoundedFormula

-- end FirstOrder.Language
