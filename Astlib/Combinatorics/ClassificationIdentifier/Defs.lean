/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.SLOTreeStructure
import Astlib.Basic.VonNeumannHierarchy
import Astlib.Basic.Cardinal.Finite
import Astlib.Basic.Ordinal.Nat
/-!
# Classification identifiers: definitions

Components and basic operations:

* for an ordered pair `a`: `uc a = lvl a = left a` and `lbl a = dcn a = right a`;
* for a function `P`: `aoc P = P ﹫ 0`, `sig P = P ﹫ 1` (with `siglvl P i = lvl (sig P ﹫ i)` and
  `sigdcn P i = dcn (sig P ﹫ i)`), `ctp P = P ﹫ 2`, `ucflvldcn P = P ﹫ 3` (with
  `ucflvl P = lvl (ucflvldcn P)` and `ucfdcn P = dcn (ucflvldcn P)`), `ucfdr P = P ﹫ 4` and
  `ucfex P = P ﹫ 5`;
* the constants `ct = 0`, `dct = 1`, `lf = 0` and `dn = 1`.

In models of `ZF`, the sets `otci n`, `aotci n`, `trvaotci n`, `uoci n`, `stduoci n`,
`trvuoci n` and `ciExt n` (`ext_n`) are defined by recursion on `n`
(`ciRec := ordRecursion ciStep`): the level tuple `ciRec n` is a function on `7`, computed from
the sequence `ciRec ↾₀ n` of the earlier ones. Each set of level `n` is cut out of an explicit
bounding set by its condition (`OtciCond`, `ArrayCond`, `UociCond`, `StduociCond`, `ExtCond`, …),
which is definable, so that the step `ciStep` is definable. The sets `finotci n`, `trvotci n`
and `finaotci n` are then cut out of `otci n` and `aotci n`.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language

namespace MemStructure

open RudimentaryTerm

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] {a b f P i : M}

section Pair

/-- The ultrapowered ordinal classification identifier `a_{uc}` of a node `a = (uc, lbl)` -/
noncomputable def uc : ClassFunction M := left

/-- The label `a_{lbl}` of a node `a = (uc, lbl)` -/
noncomputable def lbl : ClassFunction M := right

/-- The level `a_{lvl}` of a pair `a = (lvl, dcn)` -/
noncomputable def lvl : ClassFunction M := left

/-- The node `a_{dcn}` of a pair `a = (lvl, dcn)` -/
noncomputable def dcn : ClassFunction M := right

instance : (uc : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq left₀ fun _ ↦ by simp [uc]

instance : (lbl : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq right₀ fun _ ↦ by simp [lbl]

instance : (lvl : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq left₀ fun _ ↦ by simp [lvl]

instance : (dcn : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq right₀ fun _ ↦ by simp [dcn]

end Pair

section Components

/-- The array of ordinal tree classification identifiers `P_{aoc} = P(0)` -/
noncomputable def aoc : ClassFunction M := fun P ↦ P ﹫ ((0 : ℕ) : M)

/-- The signature `P_{sig} = P(1)` -/
noncomputable def sig : ClassFunction M := fun P ↦ P ﹫ ((1 : ℕ) : M)

/-- The level `P_{siglvl}(i) = P_{sig}(i)_{lvl}` -/
noncomputable def siglvl (P i : M) : M := lvl (sig P ﹫ i)

/-- The node `P_{sigdcn}(i) = P_{sig}(i)_{dcn}` -/
noncomputable def sigdcn (P i : M) : M := dcn (sig P ﹫ i)

/-- The continuity type `P_{ctp} = P(2)` -/
noncomputable def ctp : ClassFunction M := fun P ↦ P ﹫ ((2 : ℕ) : M)

/-- `P_{ucflvldcn} = P(3)` -/
noncomputable def ucflvldcn : ClassFunction M := fun P ↦ P ﹫ ((3 : ℕ) : M)

/-- `P_{ucflvl} = P_{ucflvldcn\,lvl}` -/
noncomputable def ucflvl : ClassFunction M := fun P ↦ lvl (ucflvldcn P)

/-- `P_{ucfdcn} = P_{ucflvldcn\,dcn}` -/
noncomputable def ucfdcn : ClassFunction M := fun P ↦ dcn (ucflvldcn P)

/-- `P_{ucfdr} = P(4)` -/
noncomputable def ucfdr : ClassFunction M := fun P ↦ P ﹫ ((4 : ℕ) : M)

/-- `P_{ucfex} = P(5)` -/
noncomputable def ucfex : ClassFunction M := fun P ↦ P ﹫ ((5 : ℕ) : M)

instance : (aoc : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq ((ᵣ0 : L.RudimentaryTerm 1) ﹫ RudimentaryTerm.natCast 0)
    fun _ ↦ by simp [aoc]

instance : (sig : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq ((ᵣ0 : L.RudimentaryTerm 1) ﹫ RudimentaryTerm.natCast 1)
    fun _ ↦ by simp [sig]

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ siglvl (ys 0) (ys 1)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂
    (((ᵣ0 : L.RudimentaryTerm 2) ﹫ RudimentaryTerm.natCast 1) ﹫ (ᵣ1)).left
    fun _ _ ↦ by simp [siglvl, sig, lvl]

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ sigdcn (ys 0) (ys 1)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂
    (((ᵣ0 : L.RudimentaryTerm 2) ﹫ RudimentaryTerm.natCast 1) ﹫ (ᵣ1)).right
    fun _ _ ↦ by simp [sigdcn, sig, dcn]

instance : (ctp : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq ((ᵣ0 : L.RudimentaryTerm 1) ﹫ RudimentaryTerm.natCast 2)
    fun _ ↦ by simp [ctp]

instance : (ucflvldcn : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq ((ᵣ0 : L.RudimentaryTerm 1) ﹫ RudimentaryTerm.natCast 3)
    fun _ ↦ by simp [ucflvldcn]

instance : (ucflvl : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq ((ᵣ0 : L.RudimentaryTerm 1) ﹫ RudimentaryTerm.natCast 3).left
    fun _ ↦ by simp [ucflvl, ucflvldcn, lvl]

instance : (ucfdcn : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq ((ᵣ0 : L.RudimentaryTerm 1) ﹫ RudimentaryTerm.natCast 3).right
    fun _ ↦ by simp [ucfdcn, ucflvldcn, dcn]

instance : (ucfdr : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq ((ᵣ0 : L.RudimentaryTerm 1) ﹫ RudimentaryTerm.natCast 4)
    fun _ ↦ by simp [ucfdr]

instance : (ucfex : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq ((ᵣ0 : L.RudimentaryTerm 1) ﹫ RudimentaryTerm.natCast 5)
    fun _ ↦ by simp [ucfex]

end Components

section Constants

/-- The constant `ct = 0` (continuous) -/
noncomputable def ct : M := ((0 : ℕ) : M)

/-- The constant `dct = 1` (discontinuous) -/
noncomputable def dct : M := ((1 : ℕ) : M)

/-- The constant `lf = 0` (left) -/
noncomputable def lf : M := ((0 : ℕ) : M)

/-- The constant `dn = 1` (down) -/
noncomputable def dn : M := ((1 : ℕ) : M)

end Constants

section Levels

variable [ModelsKP M]

/-- The `j`-th component `(s ﹫ k) ﹫ j` of the `k`-th entry of the sequence `s` -/
noncomputable def levComp (j : ℕ) (s k : M) : M := (s ﹫ k) ﹫ (j : M)

instance (j : ℕ) : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ levComp j (ys 0) (ys 1))
    Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂
    (((ᵣ0 : L.RudimentaryTerm 2) ﹫ ᵣ1) ﹫ RudimentaryTerm.natCast j) fun _ _ ↦ by simp [levComp]

/-- The union `⋃_{i ∈ n} levComp j s i` of the `j`-th components of the first `n` entries -/
noncomputable def levUnion (j : ℕ) (s n : M) : M :=
  ((ᵣ1 : L.RudimentaryTerm 2).iUnion
    (((ᵣ0 : L.RudimentaryTerm 3) ﹫ ᵣ2) ﹫ RudimentaryTerm.natCast j))〘s, n〙₂

instance (j : ℕ) : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ levUnion j (ys 0) (ys 1))
    Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ _ fun _ _ ↦ rfl


end Levels

section Conditions

/-! ### The conditions defining each level

A level tuple is the function `{(0, otci), (1, aotci), (2, trvaotci), (3, uoci), (4, stduoci),
(5, trvuoci), (6, ext)}` on `7`, and `s` is a sequence of level tuples (a function on `n`) giving
the levels below `n`. The sets of level `n` are defined from `s`, `n` and the sets of level `n`
defined before them.
The finite and trivial arrays are read off the arrays by `FinArrayCond` and `TrvArrayCond`. -/

variable [ModelsKP M]

/-- `otci_k` in the sequence `s` -/
noncomputable abbrev otciL (s k : M) : M := levComp 0 s k

/-- `aotci_k` in the sequence `s` -/
noncomputable abbrev aotciL (s k : M) : M := levComp 1 s k

/-- `trvaotci_k` in the sequence `s` -/
noncomputable abbrev trvaotciL (s k : M) : M := levComp 2 s k

/-- `uoci_k` in the sequence `s` -/
noncomputable abbrev uociL (s k : M) : M := levComp 3 s k

/-- `stduoci_k` in the sequence `s` -/
noncomputable abbrev stduociL (s k : M) : M := levComp 4 s k

/-- `trvuoci_k` in the sequence `s` -/
noncomputable abbrev trvuociL (s k : M) : M := levComp 5 s k

/-- `ext_k` in the sequence `s` -/
noncomputable abbrev extL (s k : M) : M := levComp 6 s k

/-- The code of the empty semi-linearly ordered tree structure -/
noncomputable def emptySLOT : M := (∅ : SLOTreeStructure M).toM

/-- The function `{(0, a), (1, b), (2, c)}` -/
noncomputable def ciTriple (a b c : M) : M := cc (cc (cc ∅ a) b) c

/-- The identifier `{(0, ∅), (1, ∅), (2, dct)}` of the roots of the trees in `otci_0`: like a
trivial `uoci`, it has empty array and signature and `ctp = dct` -/
noncomputable def otci0Uc : M := ciTriple ∅ ∅ dct

/-- `P ∈ otci_0`: `P = ∅_slots_irmrt((otci0Uc, p))` for some `p ∈ V_ω` -/
def Otci0Cond [ModelsZF M] (P : M) : Prop :=
  ∃ p ∈ 𝕍 (ω : M), P = irmrtOf emptySLOT !(otci0Uc, p)

/-- `P ∈ trvotci_n` given `P ∈ finotci_n`: for even `n`, exactly the roots are discontinuous; for
odd `n`, `P` is empty -/
def TrvotciCond (n P : M) : Prop :=
  (IsEven n → ∀ p ∈ ndOf P, ctp (uc p) = dct ↔ p ∈ rtOf P) ∧ (IsOdd n → ndOf P = ∅)

/-- The array `P` of `otci`'s up to level `n` is finite: `P(i) ∈ finotci_i` for `i ≤ n` -/
def FinArrayCond (n P : M) : Prop := ∀ i ∈ succ n, MemStructure.Finite (ndOf (P ﹫ i))

/-- The array `P` of `otci`'s up to level `n` is trivial: `P(i) ∈ trvotci_i` for `i ≤ n` -/
def TrvArrayCond (n P : M) : Prop :=
  ∀ i ∈ succ n, MemStructure.Finite (ndOf (P ﹫ i)) ∧ TrvotciCond i (P ﹫ i)

/-- `P ∈ otci_n` for `n > 0`, given the levels below `n` in `s`: the children of a node with the key
of an extension `q` have the signature of `q`, and the least one exists and is the one of type
`ct` -/
def OtciCond [ModelsZF M] (s n P : M) : Prop :=
  IsSLOT P ∧
  (∀ p ∈ ndOf P, uc p ∈ stduociL s (⋃₀ n) ∧ lbl p ∈ 𝕍 (ω : M)) ∧
  (∀ r ∈ rtOf P, uc r ∈ trvuociL s (⋃₀ n)) ∧
  (IsEven n → ∃ r, rtOf P = {r}) ∧
  ∀ p ∈ ndOf P,
    (∀ D, (∃ q ∈ chdOf P p, aoc (uc q) = D) ↔ ∃ q, !(uc p, q) ∈ extL s (⋃₀ n) ∧ aoc q = D) ∧
    (∀ q, !(uc p, q) ∈ extL s (⋃₀ n) → ∀ r ∈ losSet (chdlosOf P p ﹫ aoc q),
      sig (uc r) = sig q ∧ (IsLeastLos (chdlosOf P p ﹫ aoc q) r ↔ ctp (uc r) = ct)) ∧
    ∀ q, !(uc p, q) ∈ extL s (⋃₀ n) →
      ∃ r ∈ losSet (chdlosOf P p ﹫ aoc q), IsLeastLos (chdlosOf P p ﹫ aoc q) r


/-- `P` is an array of `otci`'s of levels up to `n`, from `s` and `X = otci_n`: a function on
`n + 1` with `P(i) ∈ otci_i` for `i < n` and `P(n) ∈ X` -/
def ArrayCond (s n X P : M) : Prop :=
  IsFunction P ∧ dom P = succ n ∧ (∀ i ∈ n, P ﹫ i ∈ otciL s i) ∧ P ﹫ n ∈ X

/-- Clause (c) of `uoci_n` at `i`: the signature entry `P_sig(i)` -/
def SigCond (n P i : M) : Prop :=
  IsOrderedPair (sig P ﹫ i) ∧ siglvl P i ∈ succ n ∧
  (IsEven (siglvl P i) → ∀ r ∈ rtOf (aoc P ﹫ siglvl P i),
    sigdcn P i ∈ chdOf (aoc P ﹫ siglvl P i) r ∨
    ∃ j ∈ i, siglvl P j = siglvl P i ∧ sigdcn P i ∈ chdOf (aoc P ﹫ siglvl P i) (sigdcn P j)) ∧
  (IsOdd (siglvl P i) → sigdcn P i ∈ rtOf (aoc P ﹫ siglvl P i) ∨
    ∃ j ∈ i, siglvl P j = siglvl P i ∧ sigdcn P i ∈ chdOf (aoc P ﹫ siglvl P i) (sigdcn P j)) ∧
  ctp (uc (sigdcn P i)) = dct

/-- Clause (h) of `uoci_n`, for `P_dom > 3` -/
def UcfCond (s n P : M) : Prop :=
  IsOrderedPair (ucflvldcn P) ∧ ucflvl P ∈ succ n ∧ ucfdcn P ∈ ndOf (aoc P ﹫ ucflvl P) ∧
  ctp (uc (ucfdcn P)) = dct ∧ (ucfdr P = lf ∨ ucfdr P = dn) ∧
  (dom P = ((5 : ℕ) : M) ↔ ucfdr P = lf) ∧
  (dom P = ((6 : ℕ) : M) → ∅ ∈ ucflvl P ∧ !(uc (ucfdcn P), ucfex P) ∈ extL s (⋃₀ ucflvl P))

/-- `P ∈ uoci_n`, given the levels below `n` in `s` and `X = finaotci_n` -/
def UociCond (s n X P : M) : Prop :=
  IsFunction P ∧
  (dom P = ((3 : ℕ) : M) ∨ dom P = ((5 : ℕ) : M) ∨ dom P = ((6 : ℕ) : M)) ∧
  aoc P ∈ X ∧
  (IsFunction (sig P) ∧ (∀ i ∈ dom (sig P), ∀ j ∈ dom (sig P), sig P ﹫ i = sig P ﹫ j → i = j) ∧
    dom (sig P) ∈ (ω : M) ∧ ∀ i ∈ dom (sig P), SigCond n P i) ∧
  (ctp P = ct ∨ ctp P = dct) ∧
  ((sig P = ∅ ∧ IsOdd n) → ctp P = dct) ∧
  (dom P = ((3 : ℕ) : M) ↔ (sig P = ∅ ∧ IsOdd n) ∨ ctp P = ct) ∧
  (((3 : ℕ) : M) ∈ dom P → UcfCond s n P)

/-- `P ∈ stduoci_n` given `P ∈ uoci_n` -/
def StduociCond (n P : M) : Prop :=
  ∀ i ∈ succ n, ∀ p ∈ ndOf (aoc P ﹫ i),
    ((IsEven i ∧ p ∈ rtOf (aoc P ﹫ i)) → lbl p = ∅) ∧
    ((ctp (uc p) = dct ∧ ¬(IsEven i ∧ p ∈ rtOf (aoc P ﹫ i))) → !(i, p) = sig P ﹫ lbl p) ∧
    (ctp (uc p) = ct →
      (p ∈ rtOf (aoc P ﹫ i) → lbl p = ∅) ∧ (p ∉ rtOf (aoc P ﹫ i) → lbl p = prtOf (aoc P ﹫ i) p))

/-- `P ∈ trvuoci_n` given `P ∈ stduoci_n` and `X = trvaotci_n`: the array is trivial and `P` is
discontinuous -/
def TrvuociCond (X P : M) : Prop := aoc P ∈ X ∧ ctp P = dct

/-- Clause (c) of `ext_n`: a new root at level `n` -/
def ExtRtCond (s n P Q : M) : Prop :=
  (sig P = ∅ ∧ IsOdd n) →
    aoc P ↾ n = aoc Q ↾ n ∧ ∃ R ∈ stduociL s (⋃₀ n), ∃ A, aoc R ∈ trvaotciL s (⋃₀ n) ∧
      aoc Q ﹫ n = asnchdOf (irmrtOf (aoc P ﹫ n) !(R, ∅)) !(R, ∅) A ∧
      sig Q = cc ∅ !(n, !(R, ∅))

/-- Clause (d) of `ext_n`: a new root at level `P_ucflvl - 1` -/
def ExtLfRtCond (s n P Q : M) : Prop :=
  (((4 : ℕ) : M) ∈ dom P ∧ ucfdr P = lf ∧ IsEven (ucflvl P) ∧
      ucfdcn P ∈ rtOf (aoc P ﹫ ucflvl P)) →
    ((1 : ℕ) : M) ∈ ucflvl P ∧
    (∀ i ∈ succ n, i ≠ ⋃₀ ucflvl P → aoc P ﹫ i = aoc Q ﹫ i) ∧
    ∃ R ∈ stduociL s (⋃₀ ⋃₀ ucflvl P), ∃ A, aoc R ∈ trvaotciL s (⋃₀ ⋃₀ ucflvl P) ∧
      aoc Q ﹫ ⋃₀ ucflvl P =
        asnchdOf (irmrtOf (aoc P ﹫ ⋃₀ ucflvl P) !(R, dom (sig P))) !(R, dom (sig P)) A ∧
      sig Q = cc (sig P) !(⋃₀ ucflvl P, !(R, dom (sig P)))

/-- Clause (e) of `ext_n`: a new left sibling of `P_ucfdcn` -/
def ExtLfSblCond (n P Q : M) : Prop :=
  (((4 : ℕ) : M) ∈ dom P ∧ ucfdr P = lf ∧
      ¬(IsEven (ucflvl P) ∧ ucfdcn P ∈ rtOf (aoc P ﹫ ucflvl P))) →
    ∅ ∈ ucflvl P ∧
    (∀ i ∈ succ n, i ≠ ucflvl P → aoc P ﹫ i = aoc Q ﹫ i) ∧
    ∃ A, aoc Q ﹫ ucflvl P = asnchdOf (ilfsblOf (aoc P ﹫ ucflvl P) (ucfdcn P)
        !(uc (ucfdcn P), dom (sig P))) !(uc (ucfdcn P), dom (sig P)) A ∧
      sig Q = cc (sig P) !(ucflvl P, !(uc (ucfdcn P), dom (sig P)))

/-- Clause (f) of `ext_n`: a new discontinuous child of `P_ucfdcn`, after the continuous child
`(R', _)` for an extension `R'` of `(P_ucfdcn)_uc` with the array and signature of `R` -/
def ExtDnCond (s n P Q : M) : Prop :=
  ucfdr P = dn →
    ∅ ∈ ucflvl P ∧
    (∀ i ∈ succ n, i ≠ ucflvl P → aoc P ﹫ i = aoc Q ﹫ i) ∧
    ∃ R ∈ stduociL s (⋃₀ ucflvl P), ∃ R', ∃ A,
      !(uc (ucfdcn P), R') ∈ extL s (⋃₀ ucflvl P) ∧ aoc R = aoc R' ∧ sig R = sig R' ∧
      aoc Q ﹫ ucflvl P =
        asnchdOf (irmchdOf (aoc P ﹫ ucflvl P) (ucfdcn P) !(R, dom (sig P))) !(R, dom (sig P)) A ∧
      sig Q = cc (sig P) !(ucflvl P, !(R, dom (sig P)))

/-- `(P, Q) ∈ ext_n` given `P, Q ∈ stduoci_n`, with the levels below `n` in `s` -/
def ExtCond (s n P Q : M) : Prop :=
  ctp P = dct ∧ ctp Q = ct ∧ ExtRtCond s n P Q ∧ ExtLfRtCond s n P Q ∧ ExtLfSblCond n P Q ∧
    ExtDnCond s n P Q

end Conditions

section Definability

variable [ModelsZF M]

instance : Multiclass.Definable (fun xs : Fin 1 → M ↦ Otci0Cond (xs 0)) Set.univ := by
  unfold Otci0Cond; infer_instance

set_option synthInstance.maxSize 2048 in
instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ OtciCond (xs 0) (xs 1) (xs 2)) Set.univ := by
  unfold OtciCond; infer_instance

set_option synthInstance.maxSize 2048 in
instance : Multiclass.Definable (fun xs : Fin 2 → M ↦ TrvotciCond (xs 0) (xs 1)) Set.univ := by
  unfold TrvotciCond; infer_instance

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ ArrayCond (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  unfold ArrayCond; infer_instance

instance : Multiclass.Definable (fun xs : Fin 2 → M ↦ FinArrayCond (xs 0) (xs 1)) Set.univ := by
  unfold FinArrayCond; infer_instance

set_option synthInstance.maxSize 2048 in
instance : Multiclass.Definable (fun xs : Fin 2 → M ↦ TrvArrayCond (xs 0) (xs 1)) Set.univ := by
  unfold TrvArrayCond; infer_instance

set_option synthInstance.maxSize 2048 in
instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ SigCond (xs 0) (xs 1) (xs 2)) Set.univ := by
  unfold SigCond; infer_instance

set_option synthInstance.maxSize 2048 in
instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ UcfCond (xs 0) (xs 1) (xs 2)) Set.univ := by
  unfold UcfCond; infer_instance

set_option synthInstance.maxSize 2048 in
instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ UociCond (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  unfold UociCond; infer_instance

set_option synthInstance.maxSize 2048 in
instance : Multiclass.Definable (fun xs : Fin 2 → M ↦ StduociCond (xs 0) (xs 1)) Set.univ := by
  unfold StduociCond; infer_instance

instance : Multiclass.Definable (fun xs : Fin 2 → M ↦ TrvuociCond (xs 0) (xs 1)) Set.univ := by
  unfold TrvuociCond; infer_instance

set_option synthInstance.maxSize 2048 in
instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ ExtRtCond (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  unfold ExtRtCond; infer_instance

set_option synthInstance.maxSize 2048 in
instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ ExtLfRtCond (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  unfold ExtLfRtCond; infer_instance

set_option synthInstance.maxSize 2048 in
instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ ExtLfSblCond (xs 0) (xs 1) (xs 2))
    Set.univ := by
  unfold ExtLfSblCond; infer_instance

set_option synthInstance.maxSize 2048 in
instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ ExtDnCond (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  unfold ExtDnCond; infer_instance

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ ExtCond (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  unfold ExtCond; infer_instance

end Definability

section Step

/-! ### The step of the recursion

From a sequence `s` of level tuples on `n = dom s`, the sets of level `n`, each cut out by its
condition from an explicit bounding set. -/

variable [ModelsZF M]

/-- The values `{left a ﹫ ∅ | a ∈ N}` -/
noncomputable def dvals : ClassFunction M := fun N ↦
  ((ᵣ0 : L.RudimentaryTerm 1).iUnion ({(ᵣ1 : L.RudimentaryTerm 2).left ﹫ ∅} :
    L.RudimentaryTerm 2))〘N〙₁

instance : (dvals : ClassFunction M).DeltaZero Set.univ :=
  ClassFunction.deltaZero_of_eq _ fun _ ↦ rfl

/-- A set containing every semi-linearly ordered tree structure with nodes in `N` -/
noncomputable def slotBound : ClassFunction M := fun N ↦
  (𝒫 N ×ˢ (𝒫 (N ×ˢ (ω : M)) ×ˢ 𝒫 (N ×ˢ 𝒫 N))) ×ˢ
    𝒫 (𝒫 N ×ˢ 𝒫 (dvals N ×ˢ (𝒫 N ×ˢ 𝒫 (N ×ˢ N))))

set_option synthInstance.maxSize 2048 in
instance : (slotBound : ClassFunction M).Definable Set.univ := by
  unfold slotBound; infer_instance

/-- `w = ∅_slots_irmrt((otci0Uc, p))` for `[p, w]` -/
def otci0Rel : Multiclass M 2 := fun xs ↦
  xs 1 = irmrtOf emptySLOT !(otci0Uc, xs 0)

instance : (otci0Rel : Multiclass M 2).Definable Set.univ := by
  unfold otci0Rel; infer_instance

/-- `otci_0 = {∅_slots_irmrt((otci0Uc, p)) | p ∈ V_ω}` -/
noncomputable def otci0 : M := otci0Rel ''₀ 𝕍 (ω : M)

/-- The set from which `otci_n` is cut out -/
noncomputable def otciBound : ClassFunction M := fun s ↦
  otci0 ∪ slotBound (stduociL s (⋃₀ dom s) ×ˢ 𝕍 (ω : M))

instance : (otciBound : ClassFunction M).Definable Set.univ := by
  unfold otciBound; infer_instance

/-- `otci_n` from the levels `s` below `n = dom s` -/
noncomputable def otciS : ClassFunction M := fun s ↦
  otciBound s ∩₀ fun P ↦ (dom s = ∅ ∧ Otci0Cond P) ∨ (dom s ≠ ∅ ∧ OtciCond s (dom s) P)

/-- The set from which `aotci_n` is cut out -/
noncomputable def aotciBound : ClassFunction M := fun s ↦
  𝒫 (succ (dom s) ×ˢ (levUnion 0 s (dom s) ∪ otciS s))

/-- `aotci_n` -/
noncomputable def aotciS : ClassFunction M := fun s ↦
  aotciBound s ∩₀ ArrayCond s (dom s) (otciS s)

/-- `finaotci_n` -/
noncomputable def finaotciS : ClassFunction M := fun s ↦
  aotciS s ∩₀ FinArrayCond (dom s)

/-- `trvaotci_n` -/
noncomputable def trvaotciS : ClassFunction M := fun s ↦
  aotciS s ∩₀ TrvArrayCond (dom s)

/-- The nodes of the trees of level at most `n` -/
noncomputable def levNodes : ClassFunction M := fun s ↦
  ndUnion (levUnion 0 s (dom s) ∪ otciS s)

/-- A set containing the values of the elements of `uoci_n` -/
noncomputable def uociVals : ClassFunction M := fun s ↦
  finaotciS s ∪ 𝒫 ((ω : M) ×ˢ (succ (dom s) ×ˢ levNodes s)) ∪ ((2 : ℕ) : M) ∪
    (succ (dom s) ×ˢ levNodes s) ∪ ⋃₀ ⋃₀ levUnion 6 s (dom s)

/-- The set from which `uoci_n` is cut out -/
noncomputable def uociBound : ClassFunction M := fun s ↦ 𝒫 (((6 : ℕ) : M) ×ˢ uociVals s)

/-- `uoci_n` -/
noncomputable def uociS : ClassFunction M := fun s ↦
  uociBound s ∩₀ UociCond s (dom s) (finaotciS s)

/-- `stduoci_n` -/
noncomputable def stduociS : ClassFunction M := fun s ↦ uociS s ∩₀ StduociCond (dom s)

/-- `trvuoci_n` -/
noncomputable def trvuociS : ClassFunction M := fun s ↦
  stduociS s ∩₀ TrvuociCond (trvaotciS s)

/-- `ext_n` -/
noncomputable def extS : ClassFunction M := fun s ↦
  (stduociS s ×ˢ stduociS s) ∩₀ fun z ↦ ExtCond s (dom s) (left z) (right z)

instance : (otciS : ClassFunction M).Definable Set.univ :=
  .of_mem_iff (R := fun s z ↦ ∃ n, n = dom s ∧ z ∈ otciBound s ∧
    ((n = ∅ ∧ Otci0Cond z) ∨ (n ≠ ∅ ∧ OtciCond s n z))) fun s z ↦ by
    simp [otciS, mem_comprehension_iff]

instance : (aotciBound : ClassFunction M).Definable Set.univ := by
  unfold aotciBound; infer_instance

instance : (aotciS : ClassFunction M).Definable Set.univ :=
  .of_mem_iff (R := fun s z ↦ z ∈ aotciBound s ∧ ∃ n X, n = dom s ∧ X = otciS s ∧
    ArrayCond s n X z) fun s z ↦ by
    simp [aotciS, mem_comprehension_iff]

instance : (finaotciS : ClassFunction M).Definable Set.univ :=
  .of_mem_iff (R := fun s z ↦ z ∈ aotciS s ∧ ∃ n, n = dom s ∧ FinArrayCond n z) fun s z ↦ by
    simp [finaotciS, mem_comprehension_iff]

instance : (trvaotciS : ClassFunction M).Definable Set.univ :=
  .of_mem_iff (R := fun s z ↦ z ∈ aotciS s ∧ ∃ n, n = dom s ∧ TrvArrayCond n z) fun s z ↦ by
    simp [trvaotciS, mem_comprehension_iff]

instance : (levNodes : ClassFunction M).Definable Set.univ := by
  unfold levNodes; infer_instance

set_option synthInstance.maxSize 2048 in
instance : (uociVals : ClassFunction M).Definable Set.univ := by
  unfold uociVals; infer_instance

instance : (uociBound : ClassFunction M).Definable Set.univ := by
  unfold uociBound; infer_instance

instance : (uociS : ClassFunction M).Definable Set.univ :=
  .of_mem_iff (R := fun s z ↦ z ∈ uociBound s ∧ ∃ n X, n = dom s ∧ X = finaotciS s ∧
    UociCond s n X z) fun s z ↦ by
    simp [uociS, mem_comprehension_iff]

instance : (stduociS : ClassFunction M).Definable Set.univ :=
  .of_mem_iff (R := fun s z ↦ z ∈ uociS s ∧ ∃ n, n = dom s ∧ StduociCond n z) fun s z ↦ by
    simp [stduociS, mem_comprehension_iff]

instance : (trvuociS : ClassFunction M).Definable Set.univ :=
  .of_mem_iff (R := fun s z ↦ z ∈ stduociS s ∧ ∃ X, X = trvaotciS s ∧ TrvuociCond X z)
    fun s z ↦ by
    simp [trvuociS, mem_comprehension_iff]

instance : (extS : ClassFunction M).Definable Set.univ :=
  .of_mem_iff (R := fun s z ↦ ∃ X, X = stduociS s ∧ z ∈ X ×ˢ X ∧ ∃ n P Q, n = dom s ∧
    P = left z ∧ Q = right z ∧ ExtCond s n P Q) fun s z ↦ by
    simp [extS, mem_comprehension_iff]

end Step

section Recursion

/-! ### The classification identifiers -/

variable [ModelsZF M]

/-- The `j`-th set of level `n = dom s` -/
noncomputable def compS : ℕ → ClassFunction M
  | 0 => otciS
  | 1 => aotciS
  | 2 => trvaotciS
  | 3 => uociS
  | 4 => stduociS
  | 5 => trvuociS
  | 6 => extS
  | _ => fun _ ↦ ∅

/-- The step of the recursion: the level tuple of level `dom s`, a function on `7` -/
noncomputable def ciStep : ClassFunction M := fun s ↦ seqOf (fun j ↦ compS j s) 7

set_option synthInstance.maxSize 2048 in
instance : (ciStep : ClassFunction M).Definable Set.univ := by
  have h : (ciStep : ClassFunction M) = fun s ↦
      cc (cc (cc (cc (cc (cc (cc ∅ (otciS s)) (aotciS s)) (trvaotciS s)) (uociS s)) (stduociS s))
        (trvuociS s)) (extS s) := by
    funext s
    rfl
  rw [h]
  infer_instance

/-- The level tuples, by recursion on `n` -/
noncomputable def ciRec : ClassFunction M := ordRecursion ciStep

instance : (ciRec : ClassFunction M).Definable Set.univ := by
  unfold ciRec; infer_instance

/-- `otci_n`: level-`n` ordinal tree classification identifiers -/
noncomputable def otci : ClassFunction M := fun n ↦ ciRec n ﹫ ((0 : ℕ) : M)

/-- `aotci_n`: arrays of level-up-to-`n` otci's -/
noncomputable def aotci : ClassFunction M := fun n ↦ ciRec n ﹫ ((1 : ℕ) : M)

/-- `trvaotci_n`: trivial arrays of level-up-to-`n` otci's -/
noncomputable def trvaotci : ClassFunction M := fun n ↦ ciRec n ﹫ ((2 : ℕ) : M)

/-- `uoci_n`: level-`n` ultrapowered ordinal classification identifiers -/
noncomputable def uoci : ClassFunction M := fun n ↦ ciRec n ﹫ ((3 : ℕ) : M)

/-- `stduoci_n`: standard level-`n` uoci's -/
noncomputable def stduoci : ClassFunction M := fun n ↦ ciRec n ﹫ ((4 : ℕ) : M)

/-- `trvuoci_n`: trivial level-`n` uoci's -/
noncomputable def trvuoci : ClassFunction M := fun n ↦ ciRec n ﹫ ((5 : ℕ) : M)

/-- `ext_n`: extensions of a standard discontinuous level-`n` uoci into a standard continuous
uoci -/
noncomputable def ciExt : ClassFunction M := fun n ↦ ciRec n ﹫ ((6 : ℕ) : M)

/-! ### The finite `otci`'s and arrays and the trivial `otci`'s -/

/-- `finotci_n`: finite level-`n` otci's -/
noncomputable def finotci : ClassFunction M := fun n ↦
  otci n ∩₀ fun P ↦ MemStructure.Finite (ndOf P)

/-- `trvotci_n`: trivial level-`n` otci's -/
noncomputable def trvotci : ClassFunction M := fun n ↦ finotci n ∩₀ TrvotciCond n

/-- `finaotci_n`: finite arrays of level-up-to-`n` otci's -/
noncomputable def finaotci : ClassFunction M := fun n ↦ aotci n ∩₀ FinArrayCond n

section Trivial

/-! ### Trees with a single node -/

/-- The tree `∅_slots_irmrt((r, ∅))` with the single node `(r, ∅)` -/
noncomputable def trvTree : ClassFunction M := fun r ↦ irmrtOf emptySLOT !(r, ∅)

instance : (otci : ClassFunction M).Definable Set.univ := by
  unfold otci; infer_instance

instance : (aotci : ClassFunction M).Definable Set.univ := by
  unfold aotci; infer_instance

instance : (uoci : ClassFunction M).Definable Set.univ := by
  unfold uoci; infer_instance

instance : (trvuoci : ClassFunction M).Definable Set.univ := by
  unfold trvuoci; infer_instance

instance : (stduoci : ClassFunction M).Definable Set.univ := by
  unfold stduoci; infer_instance

instance : (trvaotci : ClassFunction M).Definable Set.univ := by
  unfold trvaotci; infer_instance

instance : (ciExt : ClassFunction M).Definable Set.univ := by
  unfold ciExt; infer_instance

instance : (trvTree : ClassFunction M).Definable Set.univ := by
  unfold trvTree; infer_instance

end Trivial

end Recursion

end MemStructure

end FirstOrder.Language
