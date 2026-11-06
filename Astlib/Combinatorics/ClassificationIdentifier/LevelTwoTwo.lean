/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.Basic
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.Tree
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.Parent
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.Order
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.LeastChild
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.IsoUpper
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.IsoOrder
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.IsoSurj
/-!
# The tensor product of two arrays in `aotci_2`

`tensorProdATwoATwo T Q` for `T, Q ∈ aotci_2` is the array `F(T, Q) ∈ aotci_2` with
`F(T, Q) ⊗ W ≅ T ⊗ (Q ⊗ W)` for all `W ∈ aotci_1`
(`exists_isAotciIsomorphism_tensorProdATwoATwo`).

1. `iniSeg U k` for `U ∈ stduoci_1` and `k < |U_sig|`: the initial segment of `U` given by the
   first `k` entries of its signature; it has `ctp = dct` and its `ucf` points to the node that the
   `k`-th entry is inserted to the left of (`iniSeg_mem_uoci`).
2. For a node `x` of `(Q ⊗ X)(1)`, `Q ∈ aotci_2`, `X ∈ aotci_1`: `tpSig Q X x`, the signature of
   `x` as a sequence of nodes of `X`; `x` is of type `ct` (`TpCt`) if it comes from `Q(2)` and its
   node is of type `ct`; `tpUcf Q X x`, the image in `X` of the `ucf` of its node (`ucfOrLast`:
   the last entry of the signature for a node without `ucf`), or the level-`0` one for `x` from
   `Q(1)`.
3. `contraction s` for a finite sequence `s` of finite sequences: their concatenation with the
   repetitions removed from left to right (`IsContraction`).
4. `IsUociEmb Q U V σ`: `σ` is an embedding of `U_aoc` into `Q ⊗ V_aoc` such that the contraction of
   the signatures of the images of the nodes of `U_sig` is `V_sig`, the type of `V` is correct and
   the `ucf` of `U` is mapped to that of `V` (`embUcf`).
5. `tensorProdATwoATwo T Q`: the array with `aotci_1` part `T ⊗ (Q ↾ 2)` and level-`2` tree
   `tensorProdTwoTwo (T(2)) Q`, whose nodes are `(V, (t, σ))` for `t ∈ T(2)_nd`, `V ∈ stduoci_1`
   and `IsUociEmb Q t_uc V σ` (with `t` a root if `V_sig = ∅`); the depth is `|V_sig|`, and the
   parent is the restriction to `V | (|V_sig| - 1)` (`prtTwo`): at the first row `l` containing the
   newest entry, `σ(w_l)` is replaced by its successor `D` in the smaller tensor product, giving
   `(t_l, σ ↾ t_l)` if `D` is the image of the `ucf` of `t_l` and `(t_l⁺, σ')` otherwise; siblings
   with the same key are in the Brouwer–Kleene order of the sequences `((σ(w_i), t_{i+1}))_i`, as
   for `tensorProdTwoAOne`.
6. The canonical isomorphism `tensorProdAssocIso T Q W : tensorProdATwoATwo T Q ⊗ W ≅ T ⊗ (Q ⊗ W)`
   (`isAotciIsomorphism_tensorProdAssocIso`), sending `((V, (t, σ)), ψ)` to `(t, ρ ∘ Φ_ψ ∘ σ)`.

The development is split into `LevelTwoTwo/Basic`, `Tree`, `Parent`, `Order`, `LeastChild`
(the tree `P ⊗ Q ∈ otci_2`) and `IsoUpper`, `IsoOrder`, `IsoSurj` (the isomorphism).
-/
