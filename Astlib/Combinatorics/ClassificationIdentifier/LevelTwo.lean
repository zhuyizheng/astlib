/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Order.BrouwerKleene
import Astlib.Combinatorics.ClassificationIdentifier.Embedding
import Astlib.Combinatorics.ClassificationIdentifier.LevelOne
/-!
# Classification identifiers of level two

`tensorProdTwoAOne P Q` for `P ∈ otci_2` and `Q ∈ aotci_1` is the tree in `otci_1` whose nodes
`(dctUZero, (p, f))` are all roots, where `p ∈ P_nd` and `f` is an embedding of `W = (p_uc)_aoc`
into `Q ⊗ Z`. The node `(p, f)` has the sequence
`((f(w_0), p_1), …, (f(w_{d-1}), p_d))`, where `d` is the depth of `p`, `w_i` is the node of the
`i`-th entry of the signature of `p_uc` and `p_k` is the ancestor of `p` of depth `k`. The nodes are
ordered by the Brouwer–Kleene order of their sequences, the coordinates being compared
lexicographically by the order of the roots of `(Q ⊗ Z)(1)` and the sibling order of `P`; this is
the Brouwer–Kleene order of `(f(w_0), p_1, f(w_1), p_2, …)`.

`tensorProdATwoAOne P Q` for `P ∈ aotci_2` and `Q ∈ aotci_1` is the array in `aotci_1` obtained
from `B = (P ↾ 2) ⊗ (Q ↾ 1) ∈ aotci_1` by attaching the roots of `P(2) ⊗ Q` to the right of the
roots of `B(1)` (`losConcat`), in a single linearly ordered set with key `Z`.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M]

/-- The array `Q ⊗ Z` in `aotci_1`, the target of the embeddings labeling `P ⊗ Q` -/
noncomputable def tensorProdTwoAOneTgt (Q : M) : M := tensorProdAOneAZero Q trvAZero

/-- The labels `(p, f)` of the nodes of `P ⊗ Q`: `p ∈ P_nd` and `f` an embedding of `(p_uc)_aoc`
into `Q ⊗ Z` -/
noncomputable def tensorProdTwoAOneLbls (P Q : M) : M :=
  ⋃₀ ran ((fun p ↦ ({p} : M) ×ˢ
    aotciEmbSet ((1 : ℕ) : M) (aoc (uc p)) (tensorProdTwoAOneTgt Q)) ↾₀ ndOf P)

/-- The sequence `((f(w_0), p_1), …, (f(w_{d-1}), p_d))` of the label `x = (p, f)` -/
noncomputable def tensorProdTwoAOneSeq (P x : M) : M :=
  (fun i ↦ !((right x ﹫ siglvl (uc (left x)) i) ﹫ sigdcn (uc (left x)) i,
    ancOf P (left x) (succ i))) ↾₀ depOf P (left x)

/-- The order of the coordinates `(f(w_i), p_{i+1})` of the sequences: lexicographic, by the order
of the roots of `(Q ⊗ Z)(1)` and then by the sibling order of `P` -/
noncomputable def tensorProdTwoAOneCoordOdr (P Q : M) : M :=
  lexProd (losOdr (rtlosOf (tensorProdTwoAOneTgt Q ﹫ ((1 : ℕ) : M)) ﹫ trvAZero))
    (ndOf (tensorProdTwoAOneTgt Q ﹫ ((1 : ℕ) : M))) (sblOdrOf P) (ndOf P)

/-- The labels `x` and `y` of `P ⊗ Q` are in the Brouwer–Kleene order of their sequences -/
def TensorProdTwoAOneLt (P Q x y : M) : Prop :=
  BKLt (tensorProdTwoAOneCoordOdr P Q) (tensorProdTwoAOneSeq P x) (tensorProdTwoAOneSeq P y)

/-- The nodes `(dctUZero, x)` of `P ⊗ Q`, for the labels `x` -/
noncomputable def tensorProdTwoAOneNds (P Q : M) : M :=
  ran ((fun x ↦ !(dctUZero, x)) ↾₀ tensorProdTwoAOneLbls P Q)

/-- The order of the nodes of `P ⊗ Q`: the Brouwer–Kleene order of the sequences of their
labels -/
noncomputable def tensorProdTwoAOneOdr (P Q : M) : M :=
  (tensorProdTwoAOneNds P Q ×ˢ tensorProdTwoAOneNds P Q) ∩₀
    fun z ↦ TensorProdTwoAOneLt P Q (lbl (left z)) (lbl (right z))

/-- `P ⊗ Q` for `P ∈ otci_2` and `Q ∈ aotci_1`: the tree in `otci_1` whose nodes
`(dctUZero, (p, f))` are all roots, forming a single linearly ordered set with key `Z` -/
noncomputable def tensorProdTwoAOne (P Q : M) : M :=
  rtLosSLOT trvAZero !(tensorProdTwoAOneNds P Q, tensorProdTwoAOneOdr P Q)

/-- The array `(P ↾ 2) ⊗ (Q ↾ 1) ∈ aotci_1` from the `aotci_1` part of `P` and the `aotci_0`
part of `Q` -/
noncomputable def tensorProdATwoAOneBase (P Q : M) : M :=
  tensorProdAOneAZero (P ↾ 2) (Q ↾ ((1 : ℕ) : M))

/-- `P ⊗ Q` for `P ∈ aotci_2` and `Q ∈ aotci_1`: the array in `aotci_1` obtained from
`B = (P ↾ 2) ⊗ (Q ↾ 1)` by attaching the roots of `P(2) ⊗ Q ∈ otci_1` to the right of the roots
of `B(1)`, in a single linearly ordered set with key `Z` -/
noncomputable def tensorProdATwoAOne (P Q : M) : M :=
  cc (tensorProdATwoAOneBase P Q ↾ ((1 : ℕ) : M))
    (rtLosSLOT trvAZero (losConcat
      (rtlosOf (tensorProdATwoAOneBase P Q ﹫ ((1 : ℕ) : M)) ﹫ trvAZero)
      (rtlosOf (tensorProdTwoAOne (P ﹫ 2) Q) ﹫ trvAZero)))

end FirstOrder.Language.MemStructure
