/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Combinatorics.ClassificationIdentifier.LevelTwoTwo.Basic
/-!
# The tree `P ⊗ Q` of level two

The nodes `(V, (t, σ))`, the parent and the order of the tree `tensorProdTwoTwo P Q` for
`P ∈ otci_2` and `Q ∈ aotci_2`, and the structure of the trees in `otci_2` along ancestors and
subtrees.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [ModelsZF M]

section TensorProd

/-! ### The tensor product -/

/-- The elements of `X` with key `D` -/
noncomputable def keyBlock (X D : M) : M := X ∩₀ fun a ↦ left a ﹫ ∅ = D

/-- The elements of `X` with key `D`, ordered by `R` -/
noncomputable def keyLos (R X D : M) : M := !(keyBlock X D, R ∩ (keyBlock X D ×ˢ keyBlock X D))

/-- The keys of the elements of `X` -/
noncomputable def keysOf (X : M) : M := ran ((fun a ↦ left a ﹫ ∅) ↾₀ X)

/-- The function giving each key `D` of the elements of `X` the set `keyLos R X D` -/
noncomputable def keyLosFn (R X : M) : M := (fun D ↦ keyLos R X D) ↾₀ keysOf X

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ keyBlock (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ keyBlock (xs 0) (xs 1) = xs 2) = fun xs ↦
      (∀ z ∈ xs 2, z ∈ xs 0 ∧ left z ﹫ ∅ = xs 1) ∧ ∀ z ∈ xs 0, left z ﹫ ∅ = xs 1 → z ∈ xs 2 := by
    funext xs
    apply propext
    constructor
    · intro h
      rw [← h, keyBlock]
      exact ⟨fun z hz ↦ (mem_comprehension_iff ..).mp hz,
        fun z hz hk ↦ (mem_comprehension_iff ..).mpr ⟨hz, hk⟩⟩
    · rintro ⟨h₁, h₂⟩
      ext z
      rw [keyBlock, mem_comprehension_iff]
      exact ⟨fun h ↦ h₂ z h.left h.right, fun h ↦ h₁ z h⟩
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ keyBlock (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ keyBlock (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ keyBlock (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ keyLos (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ keyLos (xs 0) (xs 1) (xs 2) = xs 3) = fun xs ↦
      ∃ A, keyBlock (xs 1) (xs 2) = A ∧ !(A, xs 0 ∩ (A ×ˢ A)) = xs 3 := by
    funext xs
    simp [keyLos]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ keyLos (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ keyLos (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ keyLos (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : ClassFunction.Definable (fun X : M ↦ keysOf X) Set.univ := by
  unfold keysOf
  have : ClassFunction.Definable (fun X : M ↦ (fun a ↦ left a ﹫ ∅) ↾₀ X) Set.univ :=
    ClassFunction.Definable.toSetRestrictedTo (G := fun _ a ↦ left a ﹫ ∅) (D := fun X ↦ X)
  exact ClassFunction.Definable.comp₁ (H := ran)

instance (R : M) : ClassFunction.Definable (fun X ↦ keyLosFn R X) Set.univ := by
  unfold keyLosFn
  have : Multiclass.Definable (fun xs : Fin 3 → M ↦ keyLos R (xs 0) (xs 1) = xs 2) Set.univ := by
    have h : (fun xs : Fin 3 → M ↦ keyLos R (xs 0) (xs 1) = xs 2) = fun xs ↦
        ∃ R', R' = R ∧ keyLos R' (xs 0) (xs 1) = xs 2 := by
      funext xs
      simp
    rw [h]
    infer_instance
  exact ClassFunction.Definable.toSetRestrictedTo (G := fun X D ↦ keyLos R X D)
    (D := fun X ↦ keysOf X)

/-- The semi-linearly ordered tree structure with tree structure `T` in which the siblings with
the same key are ordered by `R` -/
noncomputable def SLOTreeStructure.ofTsOdr (T : TreeStructure M) (R : M) : SLOTreeStructure M :=
  SLOTreeStructure.mk T ((fun X ↦ keyLosFn R X) ↾₀ T.sblptn)

theorem mem_keyBlock_iff {X D a : M} : a ∈ keyBlock X D ↔ a ∈ X ∧ left a ﹫ ∅ = D :=
  mem_comprehension_iff ..

/-- `keyLosFn R X` is a sibling assignment of `X` if `R` strictly linearly orders each block -/
theorem isSblLos_keyLosFn {R X : M}
    (hR : ∀ D, IsStrictLinearOrder (R ∩ (keyBlock X D ×ˢ keyBlock X D)) (keyBlock X D)) :
    IsSblLos X (keyLosFn R X) := by
  have hk : IsSetRestrictedTo (fun a ↦ left a ﹫ ∅) X := isSetRestrictedTo_of_definable _
  have : ClassFunction.Definable (fun D ↦ keyLos R X D) Set.univ :=
    ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ R' X', R' = R ∧ X' = X ∧
      keyLos R' X' (xs 0) = xs 1) fun u w ↦ by simp
  have hv : IsSetRestrictedTo (fun D ↦ keyLos R X D) (keysOf X) := isSetRestrictedTo_of_definable _
  have hdom (D : M) : D ∈ dom (keyLosFn R X) ↔ ∃ a ∈ X, left a ﹫ ∅ = D := by
    rw [keyLosFn, dom_toSetRestrictedTo hv, keysOf, mem_ran_toSetRestrictedTo_iff hk]
  refine ⟨isFunction_toSetRestrictedTo hv, hdom, fun {D} hD ↦ ?_, fun {D} hD a ↦ ?_⟩
  · rw [keyLosFn, dom_toSetRestrictedTo hv] at hD
    rw [keyLosFn, val_toSetRestrictedTo hv hD, keyLos, isStrictLinearOrderedSet_orderedPair_iff]
    exact hR D
  · rw [keyLosFn, dom_toSetRestrictedTo hv] at hD
    rw [keyLosFn, val_toSetRestrictedTo hv hD, keyLos, losSet_orderedPair, mem_keyBlock_iff]

/-- `ofTsOdr T R` is a semi-linearly ordered tree structure if `T` is a tree structure whose nodes
are pairs `a` with `left a` a function on a nonzero natural number, and `R` strictly linearly
orders the siblings with the same key -/
theorem SLOTreeStructure.isSLOTreeStructure_ofTsOdr {T : TreeStructure M} {R : M}
    (hT : T.IsTreeStructure)
    (hnd : ∀ a ∈ T.nd, IsOrderedPair a ∧ IsFunction (left a) ∧ dom (left a) ∈ (ω : M) \ {∅})
    (hR : ∀ X ∈ T.sblptn, ∀ D,
      IsStrictLinearOrder (R ∩ (keyBlock X D ×ˢ keyBlock X D)) (keyBlock X D)) :
    (ofTsOdr T R).IsSLOTreeStructure := by
  have hres : IsSetRestrictedTo (fun X ↦ keyLosFn R X) T.sblptn := isSetRestrictedTo_of_definable _
  have hX {X : M} (hX : X ∈ T.sblptn) :
      IsSblLos X (((fun X ↦ keyLosFn R X) ↾₀ T.sblptn) ﹫ X) := by
    rw [val_toSetRestrictedTo hres hX]
    exact isSblLos_keyLosFn (hR X hX)
  unfold ofTsOdr
  exact
    { isOrderedPair_toM := isOrderedPair_mk _ _
      isTreeStructure := by rw [ts_mk]; exact hT
      isOrderedPair := fun {a} ha ↦ (hnd a (by rwa [nd, ts_mk] at ha)).left
      isFunction_left := fun {a} ha ↦ (hnd a (by rwa [nd, ts_mk] at ha)).right.left
      dom_left_mem := fun {a} ha ↦ (hnd a (by rwa [nd, ts_mk] at ha)).right.right
      isFunction_losfn := by rw [losfn_mk]; exact isFunction_toSetRestrictedTo hres
      dom_losfn := by rw [losfn_mk, sblptn, ts_mk, dom_toSetRestrictedTo hres]
      isFunction_losfn_val := fun {X} hX' ↦ by
        rw [losfn_mk]; rw [sblptn, ts_mk] at hX'; exact (hX hX').isFunction
      mem_dom_losfn_val_iff := fun {X} hX' ↦ by
        rw [losfn_mk]; rw [sblptn, ts_mk] at hX'; exact (hX hX').mem_dom_iff
      isStrictLinearOrderedSet := fun {X} hX' {D} hD ↦ by
        rw [losfn_mk] at hD ⊢; rw [sblptn, ts_mk] at hX'; exact (hX hX').isStrictLinearOrderedSet hD
      mem_losSet_iff := fun {X} hX' {D} hD ↦ by
        rw [losfn_mk] at hD ⊢; rw [sblptn, ts_mk] at hX'; exact (hX hX').mem_losSet_iff hD }

/-- `(i, j)` is the first occurrence of `e` in the sequence of sequences `s` -/
def IsFirstOcc (s e i j : M) : Prop :=
  i ∈ dom s ∧ j ∈ dom (s ﹫ i) ∧ (s ﹫ i) ﹫ j = e ∧
    ∀ i' ∈ dom s, ∀ j' ∈ dom (s ﹫ i'), (s ﹫ i') ﹫ j' = e →
      (i = i' ∧ j = j') ∨ i ∈ i' ∨ (i = i' ∧ j ∈ j')

/-- The position `(i, j)` of the first occurrence of `e` in `s` -/
noncomputable def firstOccPos (s e : M) : M :=
  ⋃₀ (((ω : M) ×ˢ (ω : M)) ∩₀ fun p ↦ IsFirstOcc s e (left p) (right p))

/-- `σ` is an embedding of `t_uc` into `(Q, V)`, and `t` is a root if `V_sig` is empty -/
def IsTensorProdTwoTwoEmb (Q t V σ : M) : Prop :=
  IsUociEmb Q (uc t) V σ ∧ (sig V = ∅ → sig (uc t) = ∅)

/-- The nodes `(V, (t, σ))` of `P ⊗ Q` over `t ∈ P_nd` and `V ∈ stduoci_1`: `σ` is an embedding of
`t_uc` into `(Q, V)`, and `t` is a root if `V_sig` is empty -/
noncomputable def tensorProdTwoTwoNdsAt (Q t V : M) : M :=
  ({V} : M) ×ˢ (({t} : M) ×ˢ
    (aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q (aoc V)) ∩₀
      fun σ ↦ IsTensorProdTwoTwoEmb Q t V σ))

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ IsUociEmb (xs i) (xs j) (xs k) (xs l)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsUociEmb (xs i) (xs j) (xs k) (xs l)) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ IsUociEmb (ys 0) (ys 1) (ys 2) (ys 3)) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable
    (fun xs : Fin 4 → M ↦ IsTensorProdTwoTwoEmb (xs 0) (xs 1) (xs 2) (xs 3)) Set.univ := by
  unfold IsTensorProdTwoTwoEmb
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦ IsUociEmb (xs 0) (uc (xs 1)) (xs 2) (xs 3))
      Set.univ := by
    have h : (fun xs : Fin 4 → M ↦ IsUociEmb (xs 0) (uc (xs 1)) (xs 2) (xs 3)) =
        fun xs : Fin 4 → M ↦ ∃ U, U = uc (xs 1) ∧ IsUociEmb (xs 0) U (xs 2) (xs 3) := by
      funext xs
      simp
    rw [h]
    infer_instance
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦ sig (xs 2) = ∅ → sig (uc (xs 1)) = ∅)
      Set.univ := by
    infer_instance
  infer_instance

/-- The condition on `σ` for the node `(V, (t, σ))` -/
private def NdsAtCond (Q t V σ : M) : Prop :=
  σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q (aoc V)) ∧
    IsTensorProdTwoTwoEmb Q t V σ

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ NdsAtCond (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  unfold NdsAtCond
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦ xs 3 ∈ aotciEmbSet ((1 : ℕ) : M)
      (aoc (uc (xs 1))) (tensorProdATwoAOne (xs 0) (aoc (xs 2)))) Set.univ := by
    have h : (fun xs : Fin 4 → M ↦ xs 3 ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc (xs 1)))
        (tensorProdATwoAOne (xs 0) (aoc (xs 2)))) = fun xs : Fin 4 → M ↦ ∃ n W T,
          n = ((1 : ℕ) : M) ∧ W = aoc (uc (xs 1)) ∧ uociEmbTgt (xs 0) (xs 2) = T ∧
            xs 3 ∈ aotciEmbSet n W T := by
      funext xs
      apply propext
      constructor
      · intro h
        exact ⟨_, _, _, rfl, rfl, rfl, h⟩
      · rintro ⟨n, W, T, rfl, rfl, rfl, h⟩
        exact h
    rw [h]
    infer_instance
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ NdsAtCond (xs i) (xs j) (xs k) (xs l)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ NdsAtCond (xs i) (xs j) (xs k) (xs l)) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ NdsAtCond (ys 0) (ys 1) (ys 2) (ys 3)) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

theorem mem_tensorProdTwoTwoNdsAt_iff {Q t V w : M} : w ∈ tensorProdTwoTwoNdsAt Q t V ↔
    ∃ σ, w = !(V, !(t, σ)) ∧
      σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q (aoc V)) ∧
        IsTensorProdTwoTwoEmb Q t V σ := by
  rw [tensorProdTwoTwoNdsAt, mem_sprod_iff]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rw [mem_singleton_iff] at hx
    rw [mem_sprod_iff] at hy
    obtain ⟨t', ht', σ, hσ, rfl⟩ := hy
    rw [mem_singleton_iff] at ht'
    rw [mem_comprehension_iff] at hσ
    rw [hx, ht']
    exact ⟨σ, rfl, hσ⟩
  · rintro ⟨σ, rfl, hσ, h⟩
    refine ⟨V, mem_singleton V, !(t, σ), ?_, rfl⟩
    rw [mem_sprod_iff]
    refine ⟨t, mem_singleton t, σ, ?_, rfl⟩
    rw [mem_comprehension_iff]
    exact ⟨hσ, h⟩

instance : Multiclass.Definable
    (fun xs : Fin 4 → M ↦ tensorProdTwoTwoNdsAt (xs 0) (xs 1) (xs 2) = xs 3) Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ tensorProdTwoTwoNdsAt (xs 0) (xs 1) (xs 2) = xs 3) =
      fun xs : Fin 4 → M ↦ ∀ w, w ∈ xs 3 ↔
        ∃ σ, w = !(xs 2, !(xs 1, σ)) ∧ NdsAtCond (xs 0) (xs 1) (xs 2) σ := by
    funext xs
    apply propext
    constructor
    · intro h w
      rw [← h, mem_tensorProdTwoTwoNdsAt_iff]
      rfl
    · intro h
      ext w
      rw [mem_tensorProdTwoTwoNdsAt_iff, h w]
      rfl
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ tensorProdTwoTwoNdsAt (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tensorProdTwoTwoNdsAt (xs i) (xs j) (xs k) = xs l) =
      Multiclass.remap (fun ys : Fin 4 → M ↦ tensorProdTwoTwoNdsAt (ys 0) (ys 1) (ys 2) = ys 3)
        ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The nodes `(V, (t, σ))` of `P ⊗ Q` for `P ∈ otci_2` and `Q ∈ aotci_2`: `t ∈ P_nd`,
`V ∈ stduoci_1` and `σ` an embedding of `t_uc` into `(Q, V)` ending with a new entry -/
noncomputable def tensorProdTwoTwoNds (P Q : M) : M :=
  ⋃₀ ran ((fun z ↦ tensorProdTwoTwoNdsAt Q (left z) (right z)) ↾₀
    (ndOf P ×ˢ stduoci ((1 : ℕ) : M)))

instance : ClassFunction.Definable (fun z : M ↦ tensorProdTwoTwoNds (left z) (right z))
    Set.univ := by
  unfold tensorProdTwoTwoNds
  have hG : Multiclass.Definable (fun xs : Fin 3 → M ↦
      (fun z y ↦ tensorProdTwoTwoNdsAt (right z) (left y) (right y)) (xs 0) (xs 1) = xs 2)
      Set.univ := by
    have h : (fun xs : Fin 3 → M ↦
        (fun z y ↦ tensorProdTwoTwoNdsAt (right z) (left y) (right y)) (xs 0) (xs 1) = xs 2) =
        fun xs : Fin 3 → M ↦ ∃ Q t V, Q = right (xs 0) ∧ t = left (xs 1) ∧ V = right (xs 1) ∧
          tensorProdTwoTwoNdsAt Q t V = xs 2 := by
      funext xs
      apply propext
      constructor
      · intro h
        exact ⟨_, _, _, rfl, rfl, rfl, h⟩
      · rintro ⟨Q, t, V, rfl, rfl, rfl, h⟩
        exact h
    rw [h]
    infer_instance
  have : ClassFunction.Definable (fun z : M ↦
      (fun y ↦ tensorProdTwoTwoNdsAt (right z) (left y) (right y)) ↾₀
        (ndOf (left z) ×ˢ stduoci ((1 : ℕ) : M))) Set.univ :=
    ClassFunction.Definable.toSetRestrictedTo
      (D := fun z ↦ ndOf (left z) ×ˢ stduoci ((1 : ℕ) : M))
  have : ClassFunction.Definable (fun z : M ↦ ran
      ((fun y ↦ tensorProdTwoTwoNdsAt (right z) (left y) (right y)) ↾₀
        (ndOf (left z) ×ˢ stduoci ((1 : ℕ) : M)))) Set.univ :=
    ClassFunction.Definable.comp₁ (H := ran)
  exact ClassFunction.Definable.comp₁ (H := fun x : M ↦ ⋃₀ x)

/-- The restriction of the embedding `σ` to the array of `U` -/
noncomputable def embRestrict (U σ : M) : M :=
  (fun i ↦ (σ ﹫ i) ↾ ndOf (aoc U ﹫ i)) ↾₀ ((2 : ℕ) : M)

/-! #### The parent and its definability -/
instance : ClassFunction.Definable (fun z : M ↦ embRestrict (left z) (right z)) Set.univ := by
  unfold embRestrict
  have : Multiclass.Definable (fun xs : Fin 3 → M ↦
      (fun z i ↦ (right z ﹫ i) ↾ ndOf (aoc (left z) ﹫ i)) (xs 0) (xs 1) = xs 2) Set.univ := by
    simp only
    infer_instance
  have : ClassFunction.Definable (fun _ : M ↦ ((2 : ℕ) : M)) Set.univ := inferInstance
  exact ClassFunction.Definable.toSetRestrictedTo
    (G := fun z i ↦ (right z ﹫ i) ↾ ndOf (aoc (left z) ﹫ i)) (D := fun _ ↦ ((2 : ℕ) : M))

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ embRestrict (xs 0) (xs 1) = xs 2)
    Set.univ :=
  Multiclass.definable_graph₂ inferInstance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ embRestrict (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ embRestrict (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ embRestrict (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The position `(i, j)` is at or before `(i', j')` in the lexicographic order -/
def PosLe (i j i' j' : M) : Prop := i ∈ i' ∨ (i = i' ∧ (j = j' ∨ j ∈ j'))

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ PosLe (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  unfold PosLe; infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ PosLe (xs i) (xs j) (xs k) (xs l)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ PosLe (xs i) (xs j) (xs k) (xs l)) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ PosLe (ys 0) (ys 1) (ys 2) (ys 3)) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- Every occurrence of `e` in `s` is at or after `(i, j)` -/
def OccAfter (s e i j : M) : Prop :=
  ∀ i' ∈ dom s, ∀ j' ∈ dom (s ﹫ i'), (s ﹫ i') ﹫ j' = e → PosLe i j i' j'

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ OccAfter (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  unfold OccAfter; infer_instance

omit [ModelsZF M] in
theorem isFirstOcc_iff {s e i j : M} : IsFirstOcc s e i j ↔
    (i ∈ dom s ∧ j ∈ dom (s ﹫ i) ∧ (s ﹫ i) ﹫ j = e) ∧ OccAfter s e i j := by
  unfold IsFirstOcc OccAfter PosLe
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    refine ⟨⟨h₁, h₂, h₃⟩, fun i' hi' j' hj' he ↦ ?_⟩
    rcases h₄ i' hi' j' hj' he with h | h | h
    · exact .inr ⟨h.left, .inl h.right⟩
    · exact .inl h
    · exact .inr ⟨h.left, .inr h.right⟩
  · rintro ⟨⟨h₁, h₂, h₃⟩, h₄⟩
    refine ⟨h₁, h₂, h₃, fun i' hi' j' hj' he ↦ ?_⟩
    rcases h₄ i' hi' j' hj' he with h | ⟨h, h' | h'⟩
    · exact .inr (.inl h)
    · exact .inl ⟨h, h'⟩
    · exact .inr (.inr ⟨h, h'⟩)

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ IsFirstOcc (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ IsFirstOcc (xs 0) (xs 1) (xs 2) (xs 3)) = fun xs : Fin 4 → M ↦
      (xs 2 ∈ dom (xs 0) ∧ xs 3 ∈ dom (xs 0 ﹫ xs 2) ∧ (xs 0 ﹫ xs 2) ﹫ xs 3 = xs 1) ∧
        OccAfter (xs 0) (xs 1) (xs 2) (xs 3) := by
    funext xs
    exact propext isFirstOcc_iff
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ IsFirstOcc (xs i) (xs j) (xs k) (xs l)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsFirstOcc (xs i) (xs j) (xs k) (xs l)) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ IsFirstOcc (ys 0) (ys 1) (ys 2) (ys 3)) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The pair `p` is the position of the first occurrence of `e` in `s` -/
def IsFirstOccPair (s e p : M) : Prop := IsFirstOcc s e (left p) (right p)

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ IsFirstOccPair (xs 0) (xs 1) (xs 2))
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ IsFirstOccPair (xs 0) (xs 1) (xs 2)) = fun xs : Fin 3 → M ↦
      ∃ i j : M, i = left (xs 2) ∧ j = right (xs 2) ∧ IsFirstOcc (xs 0) (xs 1) i j := by
    funext xs
    simp [IsFirstOccPair]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ IsFirstOccPair (xs i) (xs j) (xs k)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsFirstOccPair (xs i) (xs j) (xs k)) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ IsFirstOccPair (ys 0) (ys 1) (ys 2)) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ firstOccPos (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ firstOccPos (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ W : M, W = (ω : M) ×ˢ (ω : M) ∧
        (∀ z ∈ xs 2, ∃ p ∈ W, IsFirstOccPair (xs 0) (xs 1) p ∧ z ∈ p) ∧
        ∀ p ∈ W, IsFirstOccPair (xs 0) (xs 1) p → ∀ z ∈ p, z ∈ xs 2 := by
    funext xs
    apply propext
    constructor
    · intro h
      rw [← h]
      refine ⟨_, rfl, fun z hz ↦ ?_, fun p hp hl z hz ↦ ?_⟩
      · rw [firstOccPos, mem_sUnion_iff] at hz
        obtain ⟨p, hp, hz⟩ := hz
        rw [mem_comprehension_iff] at hp
        exact ⟨p, hp.left, hp.right, hz⟩
      · rw [firstOccPos, mem_sUnion_iff]
        exact ⟨p, (mem_comprehension_iff ..).mpr ⟨hp, hl⟩, hz⟩
    · rintro ⟨W, rfl, h₁, h₂⟩
      ext z
      rw [firstOccPos, mem_sUnion_iff]
      constructor
      · rintro ⟨p, hp, hz⟩
        rw [mem_comprehension_iff] at hp
        exact h₂ p hp.left hp.right z hz
      · intro hz
        obtain ⟨p, hp, hl, hz⟩ := h₁ z hz
        exact ⟨p, (mem_comprehension_iff ..).mpr ⟨hp, hl⟩, hz⟩
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ firstOccPos (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ firstOccPos (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ firstOccPos (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The ancestor `ancOf P t (i + 1)` of depth `i + 1` -/
noncomputable def ancSucc (P t i : M) : M := ancOf P t (succ i)

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ ancSucc (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ ancSucc (xs 0) (xs 1) (xs 2) = xs 3) = fun xs ↦
      ∃ k : M, k = succ (xs 2) ∧ ancOf (xs 0) (xs 1) k = xs 3 := by
    funext xs
    simp [ancSucc]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ ancSucc (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ ancSucc (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ ancSucc (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The restriction `embRestrict (uc A) h` of the embedding `h` of the node `x = (_, (q, h))` -/
noncomputable def cutRes (x A : M) : M := embRestrict (uc A) (nodeH x)

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ cutRes (xs 0) (xs 1) = xs 2) Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ cutRes (xs 0) (xs 1) = xs 2) = fun xs ↦
      ∃ U H : M, U = uc (xs 1) ∧ H = nodeH (xs 0) ∧ embRestrict U H = xs 2 := by
    funext xs
    simp [cutRes]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ cutRes (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ cutRes (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ cutRes (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `σ(1)` restricted to the nodes of `A_uc(1)` -/
noncomputable def lvlOneRes (σ A : M) : M :=
  (σ ﹫ ((1 : ℕ) : M)) ↾ ndOf (aoc (uc A) ﹫ ((1 : ℕ) : M))

instance : MulticlassFunction.Sigma (fun ys : Fin 2 → M ↦ lvlOneRes (ys 0) (ys 1)) 1 Set.univ := by
  unfold lvlOneRes; infer_instance

/-- The signatures of the images of the signature nodes of `t_uc`, for `x = (V, (t, σ))` -/
noncomputable def prtSeqs (Q x : M) : M := embTpSigs Q (aoc (uc x)) (nodeU x) (nodeH x)

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ prtSeqs (xs 0) (xs 1) = xs 2) Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ prtSeqs (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ X U H : M, X = aoc (uc (xs 1)) ∧ U = nodeU (xs 1) ∧ H = nodeH (xs 1) ∧
        embTpSigs (xs 0) X U H = xs 2 := by
    funext xs
    simp [prtSeqs]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtSeqs (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtSeqs (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ prtSeqs (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The newest entry `V_sig(m - 1)` of `x = (V, (t, σ))`, `m = |V_sig|` -/
noncomputable def prtEntry : ClassFunction M := fun x ↦ sig (uc x) ﹫ ⋃₀ dom (sig (uc x))

instance : (prtEntry : ClassFunction M).Sigma 1 Set.univ := by
  unfold prtEntry; infer_instance

/-- The position of the first occurrence of `V_sig(m - 1)` for `x = (V, (t, σ))` -/
noncomputable def prtPos (Q x : M) : M := firstOccPos (prtSeqs Q x) (prtEntry x)

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ prtPos (xs 0) (xs 1) = xs 2) Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ prtPos (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ s e : M, prtSeqs (xs 0) (xs 1) = s ∧ e = prtEntry (xs 1) ∧ firstOccPos s e = xs 2 := by
    funext xs
    simp [prtPos]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtPos (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtPos (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ prtPos (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The `uoci` `V | (m - 1)` of the parent of `x = (V, (t, σ))`, `m = |V_sig|` -/
noncomputable def prtUc (x : M) : M := iniSeg (uc x) (⋃₀ dom (sig (uc x)))

instance : Multiclass.Definable (fun xs : Fin 2 → M ↦ prtUc (xs 0) = xs 1) Set.univ := by
  have h : (fun xs : Fin 2 → M ↦ prtUc (xs 0) = xs 1) = fun xs : Fin 2 → M ↦
      ∃ U k : M, U = uc (xs 0) ∧ k = ⋃₀ dom (sig (uc (xs 0))) ∧ iniSeg U k = xs 1 := by
    funext xs
    simp [prtUc]
  rw [h]
  infer_instance

instance {n : ℕ} (i j : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtUc (xs i) = xs j) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtUc (xs i) = xs j) = Multiclass.remap
      (fun ys : Fin 2 → M ↦ prtUc (ys 0) = ys 1) ![i, j] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The root `t_0` of `P` below the node `t` of `x = (V, (t, σ))` -/
noncomputable def prtRootAnc (P x : M) : M := ancOf P (nodeQ x) ∅

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ prtRootAnc (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ prtRootAnc (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ q e : M, q = nodeQ (xs 1) ∧ e = ∅ ∧ ancOf (xs 0) q e = xs 2 := by
    funext xs
    simp [prtRootAnc]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtRootAnc (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtRootAnc (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ prtRootAnc (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The parent `(V | 0, (t_0, σ ↾ t_0))` of `x = (V, (t, σ))` with `|V_sig| = 1` -/
noncomputable def prtOne (P x : M) : M := !(prtUc x, !(prtRootAnc P x, cutRes x (prtRootAnc P x)))

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ prtOne (xs 0) (xs 1) = xs 2) Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ prtOne (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ S A E : M, prtUc (xs 1) = S ∧ prtRootAnc (xs 0) (xs 1) = A ∧ cutRes (xs 1) A = E ∧
        !(S, !(A, E)) = xs 2 := by
    funext xs
    simp [prtOne]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtOne (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtOne (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ prtOne (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The row `l` of the first occurrence of the newest entry, for `x = (V, (t, σ))` -/
noncomputable def prtRow (Q x : M) : M := left (prtPos Q x)

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ prtRow (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ prtRow (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ p : M, prtPos (xs 0) (xs 1) = p ∧ left p = xs 2 := by
    funext xs
    simp [prtRow]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtRow (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtRow (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ prtRow (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The ancestor `t_l` of depth `l` of `t` -/
noncomputable def prtAncL (P Q x : M) : M := ancOf P (nodeQ x) (prtRow Q x)

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ prtAncL (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ prtAncL (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∃ q l : M, q = nodeQ (xs 2) ∧ prtRow (xs 1) (xs 2) = l ∧ ancOf (xs 0) q l = xs 3 := by
    funext xs
    simp [prtAncL]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtAncL (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtAncL (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ prtAncL (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The ancestor `t_{l+1}` of depth `l + 1` of `t` -/
noncomputable def prtAncS (P Q x : M) : M := ancSucc P (nodeQ x) (prtRow Q x)

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ prtAncS (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ prtAncS (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∃ q l : M, q = nodeQ (xs 2) ∧ prtRow (xs 1) (xs 2) = l ∧ ancSucc (xs 0) q l = xs 3 := by
    funext xs
    simp [prtAncS]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtAncS (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtAncS (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ prtAncS (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The `l`-th node `w_l` of the signature of `t_uc` -/
noncomputable def prtNode (Q x : M) : M := sigdcn (nodeU x) (prtRow Q x)

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ prtNode (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ prtNode (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ U l : M, U = nodeU (xs 1) ∧ prtRow (xs 0) (xs 1) = l ∧ sigdcn U l = xs 2 := by
    funext xs
    simp [prtNode]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtNode (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtNode (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ prtNode (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The image `y = σ(w_l)` -/
noncomputable def prtImg (Q x : M) : M := (nodeH x ﹫ ((1 : ℕ) : M)) ﹫ prtNode Q x

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ prtImg (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ prtImg (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ H w : M, H = nodeH (xs 1) ∧ prtNode (xs 0) (xs 1) = w ∧
        (H ﹫ ((1 : ℕ) : M)) ﹫ w = xs 2 := by
    funext xs
    simp [prtImg]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtImg (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtImg (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ prtImg (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The order of `(Q ⊗ X)(1)`, `X = V_aoc` -/
noncomputable def prtOdr (Q x : M) : M :=
  losOdr (rtlosOf (uociEmbTgt Q (uc x) ﹫ ((1 : ℕ) : M)) ﹫ trvAZero)

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ prtOdr (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ prtOdr (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ U T : M, U = uc (xs 1) ∧ uociEmbTgt (xs 0) U = T ∧
        losOdr (rtlosOf (T ﹫ ((1 : ℕ) : M)) ﹫ trvAZero) = xs 2 := by
    funext xs
    simp [prtOdr]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtOdr (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtOdr (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ prtOdr (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The nodes of `(Q ⊗ X')(1)`, `X' = (V | (m - 1))_aoc` -/
noncomputable def prtSmall (Q x : M) : M := ndOf (uociEmbTgt Q (prtUc x) ﹫ ((1 : ℕ) : M))

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ prtSmall (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ prtSmall (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ S T : M, prtUc (xs 1) = S ∧ uociEmbTgt (xs 0) S = T ∧
        ndOf (T ﹫ ((1 : ℕ) : M)) = xs 2 := by
    funext xs
    simp [prtSmall]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtSmall (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtSmall (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ prtSmall (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The elements of `N` above `y` in the order `O` -/
noncomputable def aboveIn (O N y : M) : M := N ∩₀ fun z ↦ y [O] z

theorem mem_aboveIn_iff {O N y z : M} : z ∈ aboveIn O N y ↔ z ∈ N ∧ y [O] z :=
  mem_comprehension_iff ..

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ aboveIn (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ aboveIn (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      (∀ z ∈ xs 3, z ∈ xs 1 ∧ (xs 2) [xs 0] z) ∧ ∀ z ∈ xs 1, (xs 2) [xs 0] z → z ∈ xs 3 := by
    funext xs
    apply propext
    constructor
    · intro h
      rw [← h]
      exact ⟨fun z hz ↦ mem_aboveIn_iff.mp hz, fun z hz hl ↦ mem_aboveIn_iff.mpr ⟨hz, hl⟩⟩
    · rintro ⟨h₁, h₂⟩
      ext z
      rw [mem_aboveIn_iff]
      exact ⟨fun h ↦ h₂ z h.left h.right, fun h ↦ h₁ z h⟩
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ aboveIn (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ aboveIn (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ aboveIn (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The nodes of `(Q ⊗ X')(1)` above `y` -/
noncomputable def prtAbove (Q x : M) : M := aboveIn (prtOdr Q x) (prtSmall Q x) (prtImg Q x)

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ prtAbove (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ prtAbove (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ O N y : M, prtOdr (xs 0) (xs 1) = O ∧ prtSmall (xs 0) (xs 1) = N ∧
        prtImg (xs 0) (xs 1) = y ∧ aboveIn O N y = xs 2 := by
    funext xs
    simp [prtAbove]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtAbove (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtAbove (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ prtAbove (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The restriction `D` of `y` to `(Q ⊗ X')(1)`: its successor there, or `∅` if there is none -/
noncomputable def prtSucc (Q x : M) : M :=
  ⋃₀ (prtAbove Q x ∩₀ fun z ↦ IsLeastIn (prtOdr Q x) (prtAbove Q x) z)

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ prtSucc (xs 0) (xs 1) = xs 2)
    Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ prtSucc (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      ∃ O A : M, prtOdr (xs 0) (xs 1) = O ∧ prtAbove (xs 0) (xs 1) = A ∧
        ⋃₀ (A ∩₀ fun z ↦ IsLeastIn O A z) = xs 2 := by
    funext xs
    simp [prtSucc]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtSucc (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtSucc (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ prtSucc (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The image under `σ` of the `ucf` of `U`: `∅` for a `ucf` of level `0` -/
noncomputable def ucfImg (σ U : M) : M :=
  if ucflvl U = ∅ then ∅ else (σ ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn U

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ ucfImg (xs 0) (xs 1) = xs 2) Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ ucfImg (xs 0) (xs 1) = xs 2) = fun xs : Fin 3 → M ↦
      (ucflvl (xs 1) = ∅ ∧ ∅ = xs 2) ∨
        (¬ucflvl (xs 1) = ∅ ∧ (xs 0 ﹫ ((1 : ℕ) : M)) ﹫ ucfdcn (xs 1) = xs 2) := by
    funext xs
    by_cases hc : ucflvl (xs 1) = ∅ <;> simp [ucfImg, hc]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ ucfImg (xs i) (xs j) = xs k) Set.univ := by
  have h : (fun xs : Fin n → M ↦ ucfImg (xs i) (xs j) = xs k) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ ucfImg (ys 0) (ys 1) = ys 2) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The image `σ(r)` of the `ucf` `r` of `t_l` -/
noncomputable def prtUcfImg (P Q x : M) : M := ucfImg (nodeH x) (uc (prtAncL P Q x))

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ prtUcfImg (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ prtUcfImg (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∃ H A U : M, H = nodeH (xs 2) ∧ prtAncL (xs 0) (xs 1) (xs 2) = A ∧ U = uc A ∧
        ucfImg H U = xs 3 := by
    funext xs
    simp [prtUcfImg]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtUcfImg (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtUcfImg (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ prtUcfImg (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The least child of `p` in `P` with key `K`, the one of type `ct` -/
noncomputable def ctChd (P p K : M) : M :=
  ⋃₀ (losSet (chdlosOf P p ﹫ K) ∩₀ fun r ↦ IsLeastLos (chdlosOf P p ﹫ K) r)

instance : Multiclass.Definable (fun xs : Fin 2 → M ↦
    ⋃₀ (losSet (xs 0) ∩₀ fun r ↦ IsLeastLos (xs 0) r) = xs 1) Set.univ := by
  have h : (fun xs : Fin 2 → M ↦ ⋃₀ (losSet (xs 0) ∩₀ fun r ↦ IsLeastLos (xs 0) r) = xs 1) =
      fun xs : Fin 2 → M ↦ ∃ A : M, A = losSet (xs 0) ∧
        (∀ z ∈ xs 1, ∃ r ∈ A, IsLeastLos (xs 0) r ∧ z ∈ r) ∧
          ∀ r ∈ A, IsLeastLos (xs 0) r → ∀ z ∈ r, z ∈ xs 1 := by
    funext xs
    apply propext
    constructor
    · intro h
      rw [← h]
      refine ⟨_, rfl, fun z hz ↦ ?_, fun r hr hl z hz ↦ ?_⟩
      · rw [mem_sUnion_iff] at hz
        obtain ⟨r, hr, hz⟩ := hz
        rw [mem_comprehension_iff] at hr
        exact ⟨r, hr.left, hr.right, hz⟩
      · rw [mem_sUnion_iff]
        exact ⟨r, (mem_comprehension_iff ..).mpr ⟨hr, hl⟩, hz⟩
    · rintro ⟨A, rfl, h₁, h₂⟩
      ext z
      rw [mem_sUnion_iff]
      constructor
      · rintro ⟨r, hr, hz⟩
        rw [mem_comprehension_iff] at hr
        exact h₂ r hr.left hr.right z hz
      · intro hz
        obtain ⟨r, hr, hl, hz⟩ := h₁ z hz
        exact ⟨r, (mem_comprehension_iff ..).mpr ⟨hr, hl⟩, hz⟩
  rw [h]
  infer_instance

instance {n : ℕ} (i j : Fin n) : Multiclass.Definable (fun xs : Fin n → M ↦
    ⋃₀ (losSet (xs i) ∩₀ fun r ↦ IsLeastLos (xs i) r) = xs j) Set.univ := by
  have h : (fun xs : Fin n → M ↦ ⋃₀ (losSet (xs i) ∩₀ fun r ↦ IsLeastLos (xs i) r) = xs j) =
      Multiclass.remap (fun ys : Fin 2 → M ↦
        ⋃₀ (losSet (ys 0) ∩₀ fun r ↦ IsLeastLos (ys 0) r) = ys 1) ![i, j] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ ctChd (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ ctChd (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∃ B : M, chdlosOf (xs 0) (xs 1) ﹫ xs 2 = B ∧
        ⋃₀ (losSet B ∩₀ fun r ↦ IsLeastLos B r) = xs 3 := by
    funext xs
    simp [ctChd]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ ctChd (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ ctChd (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ ctChd (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The continuous child `t_l⁺` of `t_l` with the key of `t_{l+1}` -/
noncomputable def prtCt (P Q x : M) : M := ctChd P (prtAncL P Q x) (aoc (uc (prtAncS P Q x)))

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ prtCt (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ prtCt (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∃ A S K : M, prtAncL (xs 0) (xs 1) (xs 2) = A ∧ prtAncS (xs 0) (xs 1) (xs 2) = S ∧
        K = aoc (uc S) ∧ ctChd (xs 0) A K = xs 3 := by
    funext xs
    simp [prtCt]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtCt (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtCt (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ prtCt (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `σ` with `σ(1)` restricted to the nodes of `A_uc(1)` and the value `D` at `w` -/
noncomputable def embUpd (σ A w D : M) : M :=
  cc (σ ↾ ((1 : ℕ) : M)) (update (lvlOneRes σ A) w D)

instance : MulticlassFunction.Sigma (fun ys : Fin 4 → M ↦ embUpd (ys 0) (ys 1) (ys 2) (ys 3)) 1
    Set.univ := by
  unfold embUpd; infer_instance

instance : Multiclass.Definable
    (fun xs : Fin 5 → M ↦ embUpd (xs 0) (xs 1) (xs 2) (xs 3) = xs 4) Set.univ :=
  (inferInstance : MulticlassFunction.Definable
    (fun ys : Fin 4 → M ↦ embUpd (ys 0) (ys 1) (ys 2) (ys 3)) Set.univ).1

instance {n : ℕ} (i j k l m : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ embUpd (xs i) (xs j) (xs k) (xs l) = xs m) Set.univ := by
  have h : (fun xs : Fin n → M ↦ embUpd (xs i) (xs j) (xs k) (xs l) = xs m) = Multiclass.remap
      (fun ys : Fin 5 → M ↦ embUpd (ys 0) (ys 1) (ys 2) (ys 3) = ys 4) ![i, j, k, l, m] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The embedding `σ'` of the parent `(t_l⁺, σ')`: `σ` on `w_i`, `i < l`, and `σ'(w_l) = D` -/
noncomputable def prtEmbTwo (P Q x : M) : M :=
  embUpd (nodeH x) (prtAncS P Q x) (prtNode Q x) (prtSucc Q x)

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ prtEmbTwo (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ prtEmbTwo (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∃ H A : M, H = nodeH (xs 2) ∧ prtAncS (xs 0) (xs 1) (xs 2) = A ∧ ∃ w D : M,
        prtNode (xs 1) (xs 2) = w ∧ prtSucc (xs 1) (xs 2) = D ∧ embUpd H A w D = xs 3 := by
    funext xs
    simp [prtEmbTwo]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtEmbTwo (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtEmbTwo (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ prtEmbTwo (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The label `(t_l, σ ↾ t_l)` of the parent when `D = σ(r)` -/
noncomputable def prtLblOne (P Q x : M) : M := !(prtAncL P Q x, cutRes x (prtAncL P Q x))

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ prtLblOne (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ prtLblOne (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∃ A E : M, prtAncL (xs 0) (xs 1) (xs 2) = A ∧ cutRes (xs 2) A = E ∧ !(A, E) = xs 3 := by
    funext xs
    simp [prtLblOne]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtLblOne (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtLblOne (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ prtLblOne (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The label `(t_l⁺, σ')` of the parent when `D ≠ σ(r)` -/
noncomputable def prtLblTwo (P Q x : M) : M := !(prtCt P Q x, prtEmbTwo P Q x)

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ prtLblTwo (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ prtLblTwo (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∃ C E : M, prtCt (xs 0) (xs 1) (xs 2) = C ∧ prtEmbTwo (xs 0) (xs 1) (xs 2) = E ∧
        !(C, E) = xs 3 := by
    funext xs
    simp [prtLblTwo]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtLblTwo (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtLblTwo (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ prtLblTwo (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The restriction `D` is the image `σ(r)` of the `ucf` of `t_l` -/
def PrtCase (P Q x : M) : Prop := prtSucc Q x = prtUcfImg P Q x

noncomputable instance (P Q x : M) : Decidable (PrtCase P Q x) := Classical.propDecidable _

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ PrtCase (xs 0) (xs 1) (xs 2)) Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ PrtCase (xs 0) (xs 1) (xs 2)) = fun xs : Fin 3 → M ↦
      ∃ D I : M, prtSucc (xs 1) (xs 2) = D ∧ prtUcfImg (xs 0) (xs 1) (xs 2) = I ∧ D = I := by
    funext xs
    simp [PrtCase]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ PrtCase (xs i) (xs j) (xs k)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ PrtCase (xs i) (xs j) (xs k)) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ PrtCase (ys 0) (ys 1) (ys 2)) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The label of the parent of `x = (V, (t, σ))` with `|V_sig| > 1` -/
noncomputable def prtLbl (P Q x : M) : M :=
  if PrtCase P Q x then prtLblOne P Q x else prtLblTwo P Q x

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ prtLbl (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ prtLbl (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      (PrtCase (xs 0) (xs 1) (xs 2) ∧ prtLblOne (xs 0) (xs 1) (xs 2) = xs 3) ∨
        (¬PrtCase (xs 0) (xs 1) (xs 2) ∧ prtLblTwo (xs 0) (xs 1) (xs 2) = xs 3) := by
    funext xs
    by_cases hc : PrtCase (xs 0) (xs 1) (xs 2) <;> simp [prtLbl, hc]
  rw [h]
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦ PrtCase (xs 0) (xs 1) (xs 2)) Set.univ :=
    inferInstance
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtLbl (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtLbl (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ prtLbl (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The parent `(V | (m - 1), _)` of `x = (V, (t, σ))` with `|V_sig| = m > 1`: with `l` the row of
the first occurrence of `V_sig(m - 1)` and `D` the restriction of `σ(w_l)` to `V | (m - 1)`, the
label is `(t_l, σ ↾ t_l)` if `D` is the image of the `ucf` of `t_l`, and `(t_l⁺, σ')` otherwise -/
noncomputable def prtTwo (P Q x : M) : M := !(prtUc x, prtLbl P Q x)

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ prtTwo (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ prtTwo (xs 0) (xs 1) (xs 2) = xs 3) = fun xs : Fin 4 → M ↦
      ∃ S B : M, prtUc (xs 2) = S ∧ prtLbl (xs 0) (xs 1) (xs 2) = B ∧ !(S, B) = xs 3 := by
    funext xs
    simp [prtTwo]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ prtTwo (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ prtTwo (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ prtTwo (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The parent of the node `x = (V, (t, σ))` with `|V_sig| = m`: for `m = 1`, the root
`(V | 0, (t_0, σ ↾ t_0))`; for `m > 1`, `prtTwo P Q x` -/
noncomputable def tensorProdTwoTwoPrt (P Q x : M) : M :=
  if ⋃₀ dom (sig (uc x)) = ∅ then prtOne P x else prtTwo P Q x

instance : Multiclass.Definable
    (fun xs : Fin 4 → M ↦ tensorProdTwoTwoPrt (xs 0) (xs 1) (xs 2) = xs 3) Set.univ := by
  have h : (fun xs : Fin 4 → M ↦ tensorProdTwoTwoPrt (xs 0) (xs 1) (xs 2) = xs 3) =
      fun xs : Fin 4 → M ↦
      (⋃₀ dom (sig (uc (xs 2))) = ∅ ∧ prtOne (xs 0) (xs 2) = xs 3) ∨
        (¬⋃₀ dom (sig (uc (xs 2))) = ∅ ∧ prtTwo (xs 0) (xs 1) (xs 2) = xs 3) := by
    funext xs
    by_cases hc : ⋃₀ dom (sig (uc (xs 2))) = ∅ <;> simp [tensorProdTwoTwoPrt, hc]
  rw [h]
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦ ⋃₀ dom (sig (uc (xs 2))) = ∅) Set.univ := by
    infer_instance
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦ prtOne (xs 0) (xs 2) = xs 3) Set.univ := by
    infer_instance
  have : Multiclass.Definable (fun xs : Fin 4 → M ↦ prtTwo (xs 0) (xs 1) (xs 2) = xs 3)
    Set.univ := by
    infer_instance
  infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ tensorProdTwoTwoPrt (xs i) (xs j) (xs k) = xs l) Set.univ := by
  have h : (fun xs : Fin n → M ↦ tensorProdTwoTwoPrt (xs i) (xs j) (xs k) = xs l) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ tensorProdTwoTwoPrt (ys 0) (ys 1) (ys 2) = ys 3) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance (P Q : M) : ClassFunction.Definable (fun x ↦ tensorProdTwoTwoPrt P Q x) Set.univ :=
  ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ P' Q' : M, P' = P ∧ Q' = Q ∧
    tensorProdTwoTwoPrt P' Q' (xs 0) = xs 1) fun u w ↦ by simp

/-- The tree structure of `P ⊗ Q`: the depth of `(V, (t, σ))` is `|V_sig|`, the length of the
contraction, and the parent is `tensorProdTwoTwoPrt` -/
noncomputable def tensorProdTwoTwoTs (P Q : M) : TreeStructure M :=
  TreeStructure.mk (tensorProdTwoTwoNds P Q)
    ((fun x ↦ dom (sig (uc x))) ↾₀ tensorProdTwoTwoNds P Q)
    ((fun x ↦ tensorProdTwoTwoNds P Q ∩₀ fun y ↦
      dom (sig (uc y)) ≠ ∅ ∧ tensorProdTwoTwoPrt P Q y = x) ↾₀ tensorProdTwoTwoNds P Q)

/-- The order of the coordinates `(σ(w_i), t_{i+1})` of the sequences of the nodes with key `X`:
lexicographic, by the order of the roots of `(Q ⊗ X)(1)` and then by the sibling order of `P` -/
noncomputable def tensorProdTwoTwoCoordOdr (P Q X : M) : M :=
  lexProd (losOdr (rtlosOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M)) ﹫ trvAZero))
    (ndOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M))) (sblOdrOf P) (ndOf P)

/-- The nodes `x` and `y` of `P ⊗ Q` have the same key and are in the Brouwer–Kleene order of
the sequences `((σ(w_i), t_{i+1}))_i` of their labels -/
def TensorProdTwoTwoLt (P Q x y : M) : Prop :=
  aoc (uc x) = aoc (uc y) ∧ BKLt (tensorProdTwoTwoCoordOdr P Q (aoc (uc x)))
    (tensorProdTwoAOneSeq P (lbl x)) (tensorProdTwoAOneSeq P (lbl y))

/-- The order of the nodes of `P ⊗ Q` -/
noncomputable def tensorProdTwoTwoOdr (P Q : M) : M :=
  (tensorProdTwoTwoNds P Q ×ˢ tensorProdTwoTwoNds P Q) ∩₀
    fun z ↦ TensorProdTwoTwoLt P Q (left z) (right z)

/-- `P ⊗ Q` for `P ∈ otci_2` and `Q ∈ aotci_2`: the tree in `otci_2` with nodes
`tensorProdTwoTwoNds P Q`, parents `tensorProdTwoTwoPrt` and order `tensorProdTwoTwoOdr` -/
noncomputable def tensorProdTwoTwo (P Q : M) : M :=
  (SLOTreeStructure.ofTsOdr (tensorProdTwoTwoTs P Q) (tensorProdTwoTwoOdr P Q)).toM

/-- `T ⊗ Q` for `T, Q ∈ aotci_2`: the array in `aotci_2` with `aotci_1` part `T ⊗ (Q ↾ 2)` and
level-`2` tree `T(2) ⊗ Q` -/
noncomputable def tensorProdATwoATwo (T Q : M) : M :=
  cc (tensorProdATwoAOne T (Q ↾ 2)) (tensorProdTwoTwo (T ﹫ 2) Q)

variable {P Q T W : M}

/-- `P ⊗ Q ∈ otci_2` for `P ∈ otci_2` and `Q ∈ aotci_2` -/
theorem ndOf_tensorProdTwoTwo : ndOf (tensorProdTwoTwo P Q) = tensorProdTwoTwoNds P Q := by
  change (SLOTreeStructure.mk (tensorProdTwoTwoTs P Q) _).ts.nd = _
  rw [SLOTreeStructure.ts_mk, tensorProdTwoTwoTs, TreeStructure.nd_mk]

theorem mem_tensorProdTwoTwoNds_iff {x : M} : x ∈ tensorProdTwoTwoNds P Q ↔
    ∃ t ∈ ndOf P, ∃ V ∈ stduoci ((1 : ℕ) : M), ∃ σ,
      σ ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc t)) (tensorProdATwoAOne Q (aoc V)) ∧
      IsTensorProdTwoTwoEmb Q t V σ ∧ x = !(V, !(t, σ)) := by
  have : ClassFunction.Definable (fun z : M ↦ tensorProdTwoTwoNdsAt Q (left z) (right z))
      Set.univ :=
    ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ Q' t V, Q' = Q ∧
      t = left (xs 0) ∧ V = right (xs 0) ∧ tensorProdTwoTwoNdsAt Q' t V = xs 1) fun u w ↦ by
      simp
  have hres : IsSetRestrictedTo (fun z ↦ tensorProdTwoTwoNdsAt Q (left z) (right z))
      (ndOf P ×ˢ stduoci ((1 : ℕ) : M)) := isSetRestrictedTo_of_definable _
  rw [tensorProdTwoTwoNds, mem_sUnion_iff]
  simp only [mem_ran_toSetRestrictedTo_iff hres]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hx⟩
    rw [mem_sprod_iff] at hz
    obtain ⟨t, ht, V, hV, rfl⟩ := hz
    rw [left_orderedPair, right_orderedPair, mem_tensorProdTwoTwoNdsAt_iff] at hx
    obtain ⟨σ, rfl, hσ, h⟩ := hx
    exact ⟨t, ht, V, hV, σ, hσ, h, rfl⟩
  · rintro ⟨t, ht, V, hV, σ, hσ, h, rfl⟩
    refine ⟨_, ⟨!(t, V), ?_, rfl⟩, ?_⟩
    · rw [mem_sprod_iff]
      exact ⟨t, ht, V, hV, rfl⟩
    · rw [left_orderedPair, right_orderedPair, mem_tensorProdTwoTwoNdsAt_iff]
      exact ⟨σ, rfl, hσ, h⟩

/-- The nodes of `P ⊗ Q` are standard and hereditarily finite -/
theorem uc_mem_and_lbl_mem_of_mem_tensorProdTwoTwo (hP : P ∈ otci ((2 : ℕ) : M))
    (hQ : Q ∈ aotci ((2 : ℕ) : M)) {x : M} (hx : x ∈ ndOf (tensorProdTwoTwo P Q)) :
    uc x ∈ stduoci ((1 : ℕ) : M) ∧ lbl x ∈ 𝕍 (ω : M) := by
  rw [ndOf_tensorProdTwoTwo, mem_tensorProdTwoTwoNds_iff] at hx
  obtain ⟨t, ht, V, hV, σ, hσ, -, rfl⟩ := hx
  rw [uc_orderedPair, lbl_orderedPair]
  refine ⟨hV, orderedPair_mem_vonNeumann_omega
    (ndOf_subset_of_mem_otci (natCast_mem_omega 2) hP ht) ?_⟩
  exact mem_vonNeumann_omega_of_mem_aotciEmbSet ((otciCond_two hP).right.left t ht).left
    (tensorProdATwoAOne_mem_aotci hQ (aoc_mem_aotci_of_mem_stduoci_one hV)) hσ

instance (X x : M) : ClassFunction.Definable (fun j ↦ tpSigEntry X x j) Set.univ :=
  ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ X' x', X' = X ∧ x' = x ∧
    tpSigEntry X' x' (xs 0) = xs 1) fun u w ↦ by simp

instance (Q X U σ : M) : ClassFunction.Definable (fun i ↦ embTpSigEntry Q X U σ i) Set.univ :=
  ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ Q' X', Q' = Q ∧ X' = X ∧
    ∃ U' σ', U' = U ∧ σ' = σ ∧ embTpSigEntry Q' X' U' σ' (xs 0) = xs 1) fun u w ↦ by simp

/-- The domain of the signature of a node of `(Q ⊗ X)(1)` is a natural number -/
theorem tpSigDom_mem_omega (hQ : Q ∈ aotci ((2 : ℕ) : M)) (X x : M) :
    tpSigDom Q X x ∈ (ω : M) := by
  by_cases h : IsTpTwo Q X x
  · rw [tpSigDom, if_pos h]
    have hres : IsSetRestrictedTo (fun y ↦ !(dctUZero, y)) (tensorProdTwoAOneLbls (Q ﹫ 2) X) :=
      isSetRestrictedTo_of_definable _
    rw [IsTpTwo, tensorProdTwoAOneNds, mem_ran_toSetRestrictedTo_iff hres] at h
    obtain ⟨y, hy, rfl⟩ := h
    rw [mem_tensorProdTwoAOneLbls_iff] at hy
    obtain ⟨p, hp, -, f, -, rfl⟩ := hy
    have hQ2 : Q ﹫ 2 ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
    have hpu := ((otciCond_two hQ2).right.left p hp).left
    change dom (sig (uc (left (lbl !(dctUZero, !(p, f)))))) ∈ (ω : M)
    rw [lbl_orderedPair, left_orderedPair]
    exact dom_sig_mem_omega_of_mem_stduoci_one hpu
  · rw [tpSigDom, if_neg h]
    exact empty_mem_omega

/-- The signatures of the images of the nodes of the signature of `U` form a finite sequence of
finite sequences -/
theorem isFinSeqSeq_embTpSigs (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hU : dom (sig U) ∈ (ω : M))
    (X σ : M) : IsFinSeqSeq (embTpSigs Q X U σ) := by
  have hres : IsSetRestrictedTo (fun i ↦ embTpSigEntry Q X U σ i) (dom (sig U)) :=
    isSetRestrictedTo_of_definable _
  refine ⟨isFunction_toSetRestrictedTo hres,
    by rw [embTpSigs, dom_toSetRestrictedTo hres]; exact hU, fun i hi ↦ ?_⟩
  rw [embTpSigs, dom_toSetRestrictedTo hres] at hi
  rw [embTpSigs, val_toSetRestrictedTo hres hi, embTpSigEntry]
  have hres' : IsSetRestrictedTo (fun j ↦ tpSigEntry X ((σ ﹫ siglvl U i) ﹫ sigdcn U i) j)
      (tpSigDom Q X ((σ ﹫ siglvl U i) ﹫ sigdcn U i)) := isSetRestrictedTo_of_definable _
  rw [tpSig]
  exact ⟨isFunction_toSetRestrictedTo hres', by
    rw [dom_toSetRestrictedTo hres']
    exact tpSigDom_mem_omega hQ _ _⟩

/-- A sequence of sequences ending with a new entry has a nonempty contraction -/
theorem contraction_ne_empty_of_endsWithNew {s : M} (hs : IsFinSeqSeq s) (h : EndsWithNew s) :
    contraction s ≠ ∅ := by
  intro h0
  have hran := (isContraction_contraction hs).right.right.right.left
  have hmem : lastEntry s ∈ ctrSet s :=
    (mem_ctrSet_iff hs).mpr ⟨lastIdx s, h.left, lastIdx (lastSeq s), h.right.left, rfl⟩
  rw [← hran, h0] at hmem
  simp at hmem

section Slot

variable {U k x y : M}

/-- `y` is a node of positive depth whose parent is `x` -/
def IsPrtChd (P Q x y : M) : Prop := dom (sig (uc y)) ≠ ∅ ∧ tensorProdTwoTwoPrt P Q y = x

instance : Multiclass.Definable (fun xs : Fin 4 → M ↦ IsPrtChd (xs 0) (xs 1) (xs 2) (xs 3))
    Set.univ := by
  unfold IsPrtChd; infer_instance

instance {n : ℕ} (i j k l : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ IsPrtChd (xs i) (xs j) (xs k) (xs l)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsPrtChd (xs i) (xs j) (xs k) (xs l)) = Multiclass.remap
      (fun ys : Fin 4 → M ↦ IsPrtChd (ys 0) (ys 1) (ys 2) (ys 3)) ![i, j, k, l] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance (P Q : M) : ClassFunction.Definable
    (fun x ↦ tensorProdTwoTwoNds P Q ∩₀ fun y ↦ IsPrtChd P Q x y) Set.univ :=
  ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦ ∃ N P' Q' : M,
    (N = tensorProdTwoTwoNds P Q ∧ P' = P ∧ Q' = Q) ∧
      (∀ y ∈ xs 1, y ∈ N ∧ IsPrtChd P' Q' (xs 0) y) ∧ ∀ y ∈ N, IsPrtChd P' Q' (xs 0) y → y ∈ xs 1)
    fun u w ↦ by
      constructor
      · rintro ⟨N, P', Q', ⟨rfl, rfl, rfl⟩, h₁, h₂⟩
        ext y
        rw [mem_comprehension_iff]
        exact ⟨fun h ↦ h₂ y h.left h.right, fun h ↦ h₁ y h⟩
      · intro h
        refine ⟨_, _, _, ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
        · intro y hy
          rw [← h] at hy
          exact (mem_comprehension_iff ..).mp hy
        · intro y hy hc
          rw [← h]
          exact (mem_comprehension_iff ..).mpr ⟨hy, hc⟩

theorem uc_tensorProdTwoTwoPrt (P Q x : M) :
    uc (tensorProdTwoTwoPrt P Q x) = iniSeg (uc x) (⋃₀ dom (sig (uc x))) := by
  unfold tensorProdTwoTwoPrt
  split_ifs
  · rw [prtOne, uc_orderedPair, prtUc]
  · rw [prtTwo, uc_orderedPair, prtUc]

theorem dom_sig_iniSeg (hU : U ∈ stduoci ((1 : ℕ) : M)) (hk : k ∈ dom (sig U)) :
    dom (sig (iniSeg U k)) = k := by
  rw [sig_iniSeg]
  exact dom_restrict_of_subset (uociCond_of_mem_stduoci_one hU).right.right.right.left.left
    (subset_dom_sig_of_mem hU hk)

theorem uc_mem_stduoci_of_mem_tensorProdTwoTwoNds (hx : x ∈ tensorProdTwoTwoNds P Q) :
    uc x ∈ stduoci ((1 : ℕ) : M) := by
  rw [mem_tensorProdTwoTwoNds_iff] at hx
  obtain ⟨t, -, V, hV, σ, -, -, rfl⟩ := hx
  rw [uc_orderedPair]
  exact hV

/-- The depth of the parent is one less -/
theorem succ_dom_sig_uc_tensorProdTwoTwoPrt (hx : x ∈ tensorProdTwoTwoNds P Q)
    (hd : dom (sig (uc x)) ≠ ∅) :
    succ (dom (sig (uc (tensorProdTwoTwoPrt P Q x)))) = dom (sig (uc x)) := by
  have hV := uc_mem_stduoci_of_mem_tensorProdTwoTwoNds hx
  obtain ⟨-, hkm, hkeq⟩ := sUnion_mem_of_ne_empty (dom_sig_mem_omega_of_mem_stduoci_one hV) hd
  rw [uc_tensorProdTwoTwoPrt, dom_sig_iniSeg hV hkm, ← hkeq]

section Structure

/-! #### The structure of the trees in `otci_2` along ancestors -/

variable {X d e : M}

/-- In a tree of `otci_2`, the level-`0` trees of the arrays of the nodes are all trivial -/
theorem aoc_uc_val_zero_of_mem_otci_two {P : M} (hP : P ∈ otci ((2 : ℕ) : M)) {p : M}
    (hp : p ∈ ndOf P) : aoc (uc p) ﹫ ∅ = trvAotci ((1 : ℕ) : M) ﹫ ∅ := by
  obtain ⟨hPs, -, hroot, -, hchd⟩ := otciCond_two hP
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hPs
  have hT := hS.isTreeStructure
  refine omega_induction (A := fun k ↦ ∀ p ∈ ndOf P, depOf P p = k →
      aoc (uc p) ﹫ ∅ = trvAotci ((1 : ℕ) : M) ﹫ ∅)
    (fun p hp hd ↦ ?_) (fun k hk ih p hp hd ↦ ?_) (hT.dep_mem_omega hp) p hp rfl
  · have hr : p ∈ rtOf P := TreeStructure.mem_rt_iff.mpr ⟨hp, hd⟩
    rw [aoc_eq_trvAotci (natCast_mem_omega 1) (hroot p hr)]
  have hpr : p ∈ (SLOTreeStructure.ofM P).ts.nd \ (SLOTreeStructure.ofM P).ts.rt := by
    rw [mem_sdiff_iff, TreeStructure.mem_rt_iff]
    exact ⟨hp, fun h ↦ succ_ne_empty _ (hd.symm.trans h.right)⟩
  have hb : prtOf P p ∈ ndOf P := hT.prt_val_mem_nd hpr
  have hpc : p ∈ chdOf P (prtOf P p) := hT.mem_chd_prt_val hpr
  have hdb : depOf P (prtOf P p) = k := by
    have h : depOf P p = succ (depOf P (prtOf P p)) := hT.dep_of_mem_chd _ hb _ hpc
    rw [hd] at h
    exact (TreeStructure.eq_of_succ_eq_succ (ordinal_of_mem ordinal_omega hk) h).symm
  obtain ⟨q, hq, hqk⟩ := ((hchd _ hb).left (aoc (uc p))).mp ⟨p, hpc, rfl⟩
  rw [← hqk, (aoc_val_of_mem_ciExt_one hq).left, ih _ hb hdb]


/-- An element of `stduoci_1` does not have domain `6`: there are no extensions of level `0` -/
theorem dom_ne_six_of_mem_stduoci_one {V : M} (hV : V ∈ stduoci ((1 : ℕ) : M)) :
    dom V ≠ ((6 : ℕ) : M) := by
  intro h6
  have hc := uociCond_of_mem_stduoci_one hV
  have h3 : ((3 : ℕ) : M) ∈ dom V := by
    rw [h6]
    exact natCast_mem_natCast_iff.mpr (by omega)
  obtain ⟨-, hlvl, -, -, -, -, hext⟩ := hc.right.right.right.right.right.right.right h3
  obtain ⟨h0, hmem⟩ := hext h6
  have hl1 : ucflvl V = ((1 : ℕ) : M) := by
    rcases mem_or_eq_of_mem_succ hlvl with h | h
    · rw [natCast_succ, natCast_zero, mem_succ_iff] at h
      rcases h with h | h
      · rw [h] at h0
        simp at h0
      · simp at h
    · exact h
  rw [hl1, sUnion_natCast_one, extL_ciRec_restrict empty_mem_natCast_one, ciExt_empty] at hmem
  simp at hmem


open SLOTreeStructure in
/-- Inserting `e` immediately before the root `d`: the linearly ordered set of the roots with the
key of `e` becomes `losIlf` of the old one -/
theorem rtlosOf_ilfsblOf_val (hX : IsSLOT X) (hd : d ∈ rtOf X) (he : e ∉ ndOf X) :
    rtlosOf (ilfsblOf X d e) ﹫ (left e ﹫ ∅) = losIlf (rtlosOf X ﹫ (left e ﹫ ∅)) d e := by
  have hS : (ofM X).IsSLOTreeStructure := hX
  have hT := hS.isTreeStructure
  have hsbl : (ofM X).ts.sbl ﹫ d = (ofM X).ts.rt := hT.sbl_val_of_mem_rt hd
  have hrt : ((ofM X).ilfsbl d e).ts.rt = insert e (ofM X).ts.rt := by
    rw [ilfsbl, ts_mk, TreeStructure.isbl_of_mem_rt hd, hT.rt_irt he]
  have hf : IsFunction (update (ofM X).losfn (ofM X).ts.rt
      (mvalIlf ((ofM X).losfn ﹫ (ofM X).ts.rt) (left e ﹫ ∅) d e)) :=
    hS.isFunction_losfn.update _ _
  have hnot : insert e (ofM X).ts.rt ∉ dom (update (ofM X).losfn (ofM X).ts.rt
      (mvalIlf ((ofM X).losfn ﹫ (ofM X).ts.rt) (left e ﹫ ∅) d e)) := by
    rw [dom_update, mem_insert_iff, hS.dom_losfn]
    rintro (h | h)
    · have : e ∈ (ofM X).ts.rt := by
        rw [← h]
        simp
      exact he (TreeStructure.mem_rt_iff.mp this).left
    · exact he (hT.subset_nd_of_mem_sblptn h (by simp))
  have h1 : rtlosOf (ilfsblOf X d e) = ((ofM X).ilfsbl d e).losfn ﹫ ((ofM X).ilfsbl d e).ts.rt :=
    rfl
  have h2 : rtlosOf X = (ofM X).losfn ﹫ (ofM X).ts.rt := rfl
  rw [h1, h2, hrt]
  rw [ilfsbl, losfn_mk, hsbl, mkeyIns_eq, mvalMvalIlf_eq, val_moveKey_self hf _ hnot,
    val_update_self hS.isFunction_losfn, mvalIlf_eq,
    val_update_self (hS.isFunction_losfn_val (TreeStructure.rt_mem_sblptn ?_))]
  intro h
  have hd' : d ∈ (ofM X).ts.rt := hd
  rw [h] at hd'
  simp at hd'

section Anc

variable {T : TreeStructure M} {a k : M}

/-- The ancestors of `a` of depth at most that of its parent are those of the parent -/
theorem TreeStructure.IsTreeStructure.anc_prt_val (hT : T.IsTreeStructure)
    (ha : a ∈ T.nd \ T.rt) (hk : k ∈ succ (T.dep ﹫ (T.prt ﹫ a))) :
    T.anc a k = T.anc (T.prt ﹫ a) k := by
  have hpa : T.prt ﹫ a ∈ T.nd := hT.prt_val_mem_nd ha
  have hac : a ∈ T.chd ﹫ (T.prt ﹫ a) := hT.mem_chd_prt_val ha
  have hda : T.dep ﹫ a = succ (T.dep ﹫ (T.prt ﹫ a)) := hT.dep_of_mem_chd _ hpa _ hac
  have hdω := hT.dep_mem_omega hpa
  have haN : a ∈ T.nd := by
    rw [mem_sdiff_iff] at ha
    exact ha.left
  have hset : (T.nd ∩₀ fun b ↦ T.dep ﹫ b = k ∧ T.IsAnc a b) =
      (T.nd ∩₀ fun b ↦ T.dep ﹫ b = k ∧ T.IsAnc (T.prt ﹫ a) b) := by
    ext b
    rw [mem_comprehension_iff, mem_comprehension_iff]
    constructor
    · rintro ⟨hb, hd, hanc⟩
      refine ⟨hb, hd, fun X hX hpX hcl ↦ ?_⟩
      have hb' := hanc (insert a X) (fun c hc ↦ by
          rw [mem_insert_iff] at hc
          rcases hc with hc | hc
          · rw [hc]
            exact haN
          · exact hX hc) (mem_insert a X) fun c hc hcr ↦ by
        rw [mem_insert_iff] at hc ⊢
        rcases hc with hc | hc
        · rw [hc]
          exact .inr hpX
        · exact .inr (hcl c hc hcr)
      rw [mem_insert_iff] at hb'
      rcases hb' with hba | hb'
      · exfalso
        rw [hba, hda] at hd
        rw [hd] at hk
        exact notMem_self _ hk
      · exact hb'
    · rintro ⟨hb, hd, hanc⟩
      exact ⟨hb, hd, fun X hX haX hcl ↦ hanc X hX (hcl a haX ha) hcl⟩
  unfold TreeStructure.anc
  rw [hset]

end Anc

section SigNodes

variable {V w i : M}

/-- A node `w` of the level-`1` tree of `V ∈ stduoci_1` is the entry `lbl w` of the signature -/
theorem sig_val_lbl_of_mem (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hw : w ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M))) :
    lbl w ∈ dom (sig V) ∧ sig V ﹫ lbl w = !(((1 : ℕ) : M), w) := by
  have hA := aoc_mem_aotci_of_mem_stduoci_one hV
  have hW1 := val_mem_otci_of_mem_aotci hA (mem_succ_self _)
  have hct : ctp (uc w) = dct := by
    rw [uc_eq_dctUZero_of_mem_otci_one hW1 hw, dctUZero_eq_lfTrvUoci, ctp_lfTrvUoci]
  have h2 := ((mem_stduoci_iff.mp hV).right _ (mem_succ_self _) w hw).right.left
    ⟨hct, fun h ↦ isOdd_one.not_isEven h.left⟩
  by_cases hl : lbl w ∈ dom (sig V)
  · exact ⟨hl, h2.symm⟩
  · rw [val_eq_empty_of_not_mem_dom hl] at h2
    exact (orderedPair_ne_empty _ _ h2).elim

theorem sigdcn_lbl_of_mem (hV : V ∈ stduoci ((1 : ℕ) : M))
    (hw : w ∈ ndOf (aoc V ﹫ ((1 : ℕ) : M))) : sigdcn V (lbl w) = w := by
  rw [sigdcn, (sig_val_lbl_of_mem hV hw).right, dcn_orderedPair]

theorem lbl_sigdcn (hV : V ∈ stduoci ((1 : ℕ) : M)) (hi : i ∈ dom (sig V)) :
    lbl (sigdcn V i) = i := by
  obtain ⟨hl1, hnd⟩ := siglvl_eq_one hV hi
  obtain ⟨hl, hval⟩ := sig_val_lbl_of_mem hV hnd
  have hc := uociCond_of_mem_stduoci_one hV
  have hpair : sig V ﹫ i = !(((1 : ℕ) : M), sigdcn V i) := by
    obtain ⟨a, b, hab⟩ := (hc.right.right.right.left.right.right.right i hi).left
    rw [← hl1, siglvl, sigdcn, hab, lvl_orderedPair, dcn_orderedPair]
  exact hc.right.right.right.left.right.left _ hl _ hi (hval.trans hpair.symm)

/-- The nodes of the level-`1` tree of `V ∈ stduoci_1` are those of its signature -/
theorem ndOf_aoc_val_one_eq (hV : V ∈ stduoci ((1 : ℕ) : M)) :
    ndOf (aoc V ﹫ ((1 : ℕ) : M)) = iniSegNds V (dom (sig V)) := by
  ext w
  rw [mem_iniSegNds_iff]
  constructor
  · intro hw
    exact ⟨lbl w, (sig_val_lbl_of_mem hV hw).left, sigdcn_lbl_of_mem hV hw⟩
  · rintro ⟨i, hi, rfl⟩
    exact (siglvl_eq_one hV hi).right

end SigNodes

section ChdRel

variable {U q c p : M}

/-- An element of `stduoci_1` with nonempty signature that has an extension has its `ucf` at
level `1` -/
theorem ucf_of_mem_ciExt_one (h : !(U, q) ∈ ciExt ((1 : ℕ) : M)) (hs : sig U ≠ ∅) :
    ucflvl U = ((1 : ℕ) : M) ∧ ucfdcn U ∈ ndOf (aoc U ﹫ ((1 : ℕ) : M)) ∧
      ucflvldcn U = !(((1 : ℕ) : M), ucfdcn U) := by
  have h1ω : ((1 : ℕ) : M) ∈ (ω : M) := natCast_mem_omega 1
  obtain ⟨hUs, -, hUd, -⟩ := mem_ciExt_props h
  obtain ⟨P', -, Q', -, hPQ, hext⟩ := mem_ciExt_iff.mp h
  rw [orderedPair_eq_orderedPair_iff] at hPQ
  obtain ⟨rfl, rfl⟩ := hPQ
  obtain ⟨-, -, -, hlfrt, -, -⟩ := hext
  have hs' : ¬(sig U = ∅ ∧ IsOdd ((1 : ℕ) : M)) := fun h ↦ hs h.left
  have hUu := (mem_stduoci_iff.mp hUs).left
  rw [mem_uoci_iff_of_mem_omega h1ω] at hUu
  obtain ⟨-, hdom, -, -, -, -, hdom3, hucf⟩ := hUu
  have hne3 : dom U ≠ ((3 : ℕ) : M) := fun h3 ↦
    (hdom3.mp h3).elim hs' fun hct ↦ ct_ne_dct (hct.symm.trans hUd)
  have hmem (k : ℕ) (hk : k < 5) : ((k : ℕ) : M) ∈ dom U := by
    rcases hdom with h | h | h
    · exact (hne3 h).elim
    · rw [h]
      exact natCast_mem_natCast_of_lt hk
    · rw [h]
      exact natCast_mem_natCast_of_lt (by omega)
  obtain ⟨hpair, hlvl, hd, -, hdr, hdr5, -⟩ := hucf (hmem 3 (by omega))
  have hdom5 : dom U = ((5 : ℕ) : M) := by
    rcases hdom with h | h | h
    · exact (hne3 h).elim
    · exact h
    · exact absurd h (dom_ne_six_of_mem_stduoci_one hUs)
  have hlf := hdr5.mp hdom5
  have hl1 : ucflvl U = ((1 : ℕ) : M) := by
    rcases mem_or_eq_of_mem_succ hlvl with h | h
    · exfalso
      rw [natCast_succ, natCast_zero, mem_succ_iff] at h
      rcases h with h | h
      · have hr : IsEven (ucflvl U) ∧ ucfdcn U ∈ rtOf (aoc U ﹫ ucflvl U) := by
          refine ⟨by rw [h]; exact isEven_empty, ?_⟩
          have hA := aoc_mem_aotci_of_mem_stduoci_one hUs
          obtain ⟨l, hnd, hrt⟩ := exists_ndOf_eq_of_mem_otci_empty
            (val_mem_otci_of_mem_aotci hA (mem_succ_of_mem empty_mem_natCast_one))
          rw [h] at hd ⊢
          rw [hrt, ← hnd]
          exact hd
        have h1 := (hlfrt ⟨hmem 4 (by omega), hlf, hr⟩).left
        rw [h] at h1
        simp at h1
      · simp at h
    · exact h
  refine ⟨hl1, hl1 ▸ hd, ?_⟩
  obtain ⟨a, b, hab⟩ := hpair
  rw [← hl1, ucflvl, ucfdcn, hab, lvl_orderedPair, dcn_orderedPair]

/-- The order of the roots of a tree in `otci_1` -/
noncomputable def odrOne (Y : M) : M := losOdr (rtlosOf Y ﹫ trvAZero)

/-- `Y` is a subtree of `X` in `otci_1`: its nodes are nodes of `X`, with the restricted order -/
def IsSubOne (Y X : M) : Prop :=
  ndOf Y ⊆ ndOf X ∧ ∀ a ∈ ndOf Y, ∀ b ∈ ndOf Y, (a [odrOne Y] b ↔ a [odrOne X] b)

omit [ModelsZF M] in
theorem isSubOne_refl (Y : M) : IsSubOne Y Y := ⟨fun _ h ↦ h, fun _ _ _ _ ↦ Iff.rfl⟩

omit [ModelsZF M] in
theorem IsSubOne.trans {Y Y' X : M} (h : IsSubOne Y Y') (h' : IsSubOne Y' X) : IsSubOne Y X :=
  ⟨fun _ hz ↦ h'.left (h.left hz), fun a ha b hb ↦
    (h.right a ha b hb).trans (h'.right a (h.left ha) b (h.left hb))⟩

/-- A child `c` of a node `p` in a tree of `otci_2`: the signature of `p` is that of `c` without
its last entry, the level-`1` tree of `p` is a subtree of that of `c`, and the new node of `c` lies
immediately before the `ucf` of `p` -/
theorem uc_rel_of_mem_chdOf {P : M} (hP : P ∈ otci ((2 : ℕ) : M)) (hp : p ∈ ndOf P)
    (hc : c ∈ chdOf P p) :
    sig (uc p) = sig (uc c) ↾ dom (sig (uc p)) ∧ dom (sig (uc c)) = succ (dom (sig (uc p))) ∧
      IsSubOne (aoc (uc p) ﹫ ((1 : ℕ) : M)) (aoc (uc c) ﹫ ((1 : ℕ) : M)) ∧
      (sig (uc p) ≠ ∅ → ucflvldcn (uc p) = !(((1 : ℕ) : M), ucfdcn (uc p)) ∧
        ucfdcn (uc p) ∈ ndOf (aoc (uc p) ﹫ ((1 : ℕ) : M)) ∧
        (sigdcn (uc c) (dom (sig (uc p)))) [odrOne (aoc (uc c) ﹫ ((1 : ℕ) : M))]
          (ucfdcn (uc p)) ∧
        ∀ z ∈ ndOf (aoc (uc p) ﹫ ((1 : ℕ) : M)),
          (sigdcn (uc c) (dom (sig (uc p)))) [odrOne (aoc (uc c) ﹫ ((1 : ℕ) : M))] z →
            z = ucfdcn (uc p) ∨ (ucfdcn (uc p)) [odrOne (aoc (uc c) ﹫ ((1 : ℕ) : M))] z) := by
  obtain ⟨hPs, hPnd, -, -, hchd⟩ := otciCond_two hP
  have h1ω : ((1 : ℕ) : M) ∈ (ω : M) := natCast_mem_omega 1
  have hcn : c ∈ ndOf P := mem_ndOf_of_mem_chdOf hPs hc
  have hUs := (hPnd p hp).left
  have hCs := (hPnd c hcn).left
  obtain ⟨q, hq, hqk⟩ := ((hchd p hp).left (aoc (uc c))).mp ⟨c, hc, rfl⟩
  have hmem : c ∈ losSet (chdlosOf P p ﹫ aoc q) := by
    rw [hqk]
    exact (mem_losSet_chdlosOf_iff hPs hp hc c).mpr ⟨hc, rfl⟩
  have hsig : sig (uc c) = sig q := ((hchd p hp).right.left q hq c hmem).left
  obtain ⟨e, he⟩ := exists_sig_eq_cc_of_mem_ciExt h1ω hq
  have hsU := (uociCond_of_mem_stduoci_one hUs).right.right.right.left.left
  have hsc : sig (uc c) = cc (sig (uc p)) e := hsig.trans he
  have hres : sig (uc p) = sig (uc c) ↾ dom (sig (uc p)) := by
    rw [hsc]
    refine hsU.ext ((hsU.cc e).restrict _) (by
      rw [dom_restrict_of_subset (hsU.cc e) (by rw [dom_cc]; exact fun _ h ↦ mem_succ_of_mem h)])
      fun i hi ↦ ?_
    rw [val_restrict _ (hsU.cc e) hi (by rw [dom_cc]; exact mem_succ_of_mem hi),
      cc_val_of_mem hsU e hi]
  refine ⟨hres, by rw [hsc, dom_cc], ?_⟩
  have hUA := aoc_mem_aotci_of_mem_stduoci_one hUs
  have hU1 := val_mem_otci_of_mem_aotci hUA (mem_succ_self _)
  have hCA := aoc_mem_aotci_of_mem_stduoci_one hCs
  have hC1 := val_mem_otci_of_mem_aotci hCA (mem_succ_self _)
  have h1 := (aoc_val_of_mem_ciExt_one hq).right
  rw [hqk] at h1
  by_cases hs : sig (uc p) = ∅
  · refine ⟨⟨fun w hw ↦ ?_, fun a ha ↦ ?_⟩, fun h ↦ (h hs).elim⟩
    · obtain ⟨hl, -⟩ := sig_val_lbl_of_mem hUs hw
      rw [hs, dom_empty] at hl
      simp at hl
    · obtain ⟨hl, -⟩ := sig_val_lbl_of_mem hUs ha
      rw [hs, dom_empty] at hl
      simp at hl
  rw [if_neg hs] at h1
  obtain ⟨hl1, hd, hpair⟩ := ucf_of_mem_ciExt_one hq hs
  set n := !(uc (ucfdcn (uc p)), dom (sig (uc p))) with hn
  have hdrt : ucfdcn (uc p) ∈ rtOf (aoc (uc p) ﹫ ((1 : ℕ) : M)) := by
    rw [← ndOf_eq_rtOf_of_mem_otci_one hU1]
    exact hd
  have hnN : n ∉ ndOf (aoc (uc p) ﹫ ((1 : ℕ) : M)) := by
    intro h
    have hl := (sig_val_lbl_of_mem hUs h).left
    rw [hn, lbl_orderedPair] at hl
    exact notMem_self _ hl
  have hkey : left n ﹫ ∅ = trvAZero := by
    rw [hn, left_orderedPair]
    exact aoc_uc_eq_trvAZero_of_mem_otci_one hU1 hd
  have hlos := rtlosOf_ilfsblOf_val (isSLOT_of_mem_otci hU1) hdrt hnN
  rw [hkey, ← h1] at hlos
  obtain ⟨hR, hA, -⟩ := rtlosOf_of_mem_otci_one hU1
  obtain ⟨-, hA', -⟩ := rtlosOf_of_mem_otci_one hC1
  have hodr : odrOne (aoc (uc c) ﹫ ((1 : ℕ) : M)) =
      insertBefore (odrOne (aoc (uc p) ﹫ ((1 : ℕ) : M)))
        (ndOf (aoc (uc p) ﹫ ((1 : ℕ) : M))) (ucfdcn (uc p)) n := by
    rw [odrOne, hlos, losIlf_eq, losOdr_orderedPair, hA]
    rfl
  have hnd' : ndOf (aoc (uc c) ﹫ ((1 : ℕ) : M)) =
      insert n (ndOf (aoc (uc p) ﹫ ((1 : ℕ) : M))) := by
    rw [← hA', hlos, losIlf_eq, losSet_orderedPair, hA]
  have hnC : n ∈ ndOf (aoc (uc c) ﹫ ((1 : ℕ) : M)) := by
    rw [hnd']
    exact mem_insert _ _
  have hsn : sigdcn (uc c) (dom (sig (uc p))) = n := by
    have h := sigdcn_lbl_of_mem hCs hnC
    rwa [hn, lbl_orderedPair] at h
  have hRo : IsStrictLinearOrder (odrOne (aoc (uc p) ﹫ ((1 : ℕ) : M)))
      (ndOf (aoc (uc p) ﹫ ((1 : ℕ) : M))) := hR
  refine ⟨⟨fun z hz ↦ by rw [hnd', mem_insert_iff]; exact .inr hz, fun a ha b hb ↦ ?_⟩,
    fun _ ↦ ⟨hpair, hd, ?_, fun z hz hnz ↦ ?_⟩⟩
  · rw [hodr, rel_insertBefore_iff]
    constructor
    · exact fun h ↦ .inl h
    · rintro (h | ⟨-, rfl⟩ | ⟨rfl, -⟩)
      · exact h
      · exact (hnN hb).elim
      · exact (hnN ha).elim
  · rw [hsn, hodr, rel_insertBefore_iff]
    exact Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)
  · rw [hsn, hodr, rel_insertBefore_iff] at hnz
    rw [hodr, rel_insertBefore_iff]
    rcases hnz with h | ⟨⟨h, -⟩, -⟩ | ⟨-, h | ⟨-, h⟩⟩
    · exact (hnN (hRo.mem_left h)).elim
    · exact (hnN h).elim
    · exact Or.inl h
    · exact Or.inr (Or.inl h)


instance : MulticlassFunction.Sigma (fun ys : Fin 1 → M ↦ odrOne (ys 0)) 1 Set.univ := by
  unfold odrOne; infer_instance

instance : Multiclass.Definable (fun xs : Fin 2 → M ↦ IsSubOne (xs 0) (xs 1)) Set.univ := by
  unfold IsSubOne
  have : Multiclass.Definable (fun xs : Fin 2 → M ↦ ∀ a ∈ ndOf (xs 0), ∀ b ∈ ndOf (xs 0),
      (a [odrOne (xs 0)] b ↔ a [odrOne (xs 1)] b)) Set.univ := by
    have h : (fun xs : Fin 2 → M ↦ ∀ a ∈ ndOf (xs 0), ∀ b ∈ ndOf (xs 0),
        (a [odrOne (xs 0)] b ↔ a [odrOne (xs 1)] b)) = fun xs : Fin 2 → M ↦
        ∃ N R S : M, N = ndOf (xs 0) ∧ R = odrOne (xs 0) ∧ S = odrOne (xs 1) ∧
          ∀ a ∈ N, ∀ b ∈ N, (a [R] b ↔ a [S] b) := by
      funext xs
      apply propext
      constructor
      · intro h
        exact ⟨_, _, _, rfl, rfl, rfl, h⟩
      · rintro ⟨N, R, S, rfl, rfl, rfl, h⟩
        exact h
    rw [h]
    infer_instance
  infer_instance

instance {n : ℕ} (i j : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ IsSubOne (xs i) (xs j)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ IsSubOne (xs i) (xs j)) = Multiclass.remap
      (fun ys : Fin 2 → M ↦ IsSubOne (ys 0) (ys 1)) ![i, j] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- The relation of the ancestor of depth `k` of `t` to `t` -/
def AncRel (P t k : M) : Prop :=
  sig (uc (ancOf P t k)) = sig (uc t) ↾ k ∧
    IsSubOne (aoc (uc (ancOf P t k)) ﹫ ((1 : ℕ) : M)) (aoc (uc t) ﹫ ((1 : ℕ) : M))

/-- The relation `AncRel` for a given ancestor `A` -/
def AncRelAux (A t k : M) : Prop :=
  sig (uc A) = sig (uc t) ↾ k ∧
    IsSubOne (aoc (uc A) ﹫ ((1 : ℕ) : M)) (aoc (uc t) ﹫ ((1 : ℕ) : M))

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ AncRelAux (xs 0) (xs 1) (xs 2))
    Set.univ := by
  unfold AncRelAux
  have : Multiclass.Definable (fun xs : Fin 3 → M ↦
      IsSubOne (aoc (uc (xs 0)) ﹫ ((1 : ℕ) : M)) (aoc (uc (xs 1)) ﹫ ((1 : ℕ) : M))) Set.univ := by
    have h : (fun xs : Fin 3 → M ↦
        IsSubOne (aoc (uc (xs 0)) ﹫ ((1 : ℕ) : M)) (aoc (uc (xs 1)) ﹫ ((1 : ℕ) : M))) =
        fun xs : Fin 3 → M ↦ ∃ Y X : M, Y = aoc (uc (xs 0)) ﹫ ((1 : ℕ) : M) ∧
          X = aoc (uc (xs 1)) ﹫ ((1 : ℕ) : M) ∧ IsSubOne Y X := by
      funext xs
      simp
    rw [h]
    infer_instance
  have : Multiclass.Definable (fun xs : Fin 3 → M ↦ sig (uc (xs 0)) = sig (uc (xs 1)) ↾ xs 2)
      Set.univ := by
    infer_instance
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ AncRelAux (xs i) (xs j) (xs k)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ AncRelAux (xs i) (xs j) (xs k)) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ AncRelAux (ys 0) (ys 1) (ys 2)) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

instance : Multiclass.Definable (fun xs : Fin 3 → M ↦ AncRel (xs 0) (xs 1) (xs 2)) Set.univ := by
  have h : (fun xs : Fin 3 → M ↦ AncRel (xs 0) (xs 1) (xs 2)) = fun xs : Fin 3 → M ↦
      ∃ A : M, ancOf (xs 0) (xs 1) (xs 2) = A ∧ AncRelAux A (xs 1) (xs 2) := by
    funext xs
    simp [AncRel, AncRelAux]
  rw [h]
  infer_instance

instance {n : ℕ} (i j k : Fin n) : Multiclass.Definable
    (fun xs : Fin n → M ↦ AncRel (xs i) (xs j) (xs k)) Set.univ := by
  have h : (fun xs : Fin n → M ↦ AncRel (xs i) (xs j) (xs k)) = Multiclass.remap
      (fun ys : Fin 3 → M ↦ AncRel (ys 0) (ys 1) (ys 2)) ![i, j, k] := by
    funext xs
    simp [Multiclass.remap]
  rw [h]
  exact ⟨Multiclass.Definable.isDefinable.remap _⟩

/-- `AncRel` for the nodes of depth `n` -/
def AncRelCond (P n : M) : Prop := ∀ t ∈ ndOf P, depOf P t = n → ∀ k ∈ succ n, AncRel P t k

instance (P : M) : Class.Definable (fun n : M ↦ AncRelCond P n) Set.univ := by
  have h : (fun n : M ↦ AncRelCond P n) = fun n : M ↦ ∃ P' N : M, P' = P ∧ N = ndOf P ∧
      ∀ t ∈ N, depOf P' t = n → ∀ k ∈ succ n, AncRel P' t k := by
    funext n
    simp [AncRelCond]
  rw [h]
  infer_instance

/-- The ancestors of a node `t` of a tree of `otci_2`: the signature is an initial segment of that
of `t`, and the level-`1` tree is a subtree -/
theorem uc_ancOf_rel {P t : M} (hP : P ∈ otci ((2 : ℕ) : M)) (ht : t ∈ ndOf P) {k : M}
    (hk : k ∈ succ (depOf P t)) :
    sig (uc (ancOf P t k)) = sig (uc t) ↾ k ∧
      IsSubOne (aoc (uc (ancOf P t k)) ﹫ ((1 : ℕ) : M)) (aoc (uc t) ﹫ ((1 : ℕ) : M)) := by
  obtain ⟨hPs, hPnd, -, -, -⟩ := otciCond_two hP
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hPs
  have hT := hS.isTreeStructure
  have hsf (t : M) (ht : t ∈ ndOf P) :=
    (uociCond_of_mem_stduoci_one (hPnd t ht).left).right.right.right.left.left
  suffices h : AncRelCond P (depOf P t) from h t ht rfl k hk
  refine omega_induction (A := fun n ↦ AncRelCond P n)
    (fun t ht hd k hk ↦ ?_) (fun n hn ih t ht hd k hk ↦ ?_) (hT.dep_mem_omega ht)
  · have hk0 : k = ∅ := by
      rw [mem_succ_iff] at hk
      rcases hk with h | h
      · exact h
      · exact absurd h (by simp)
    subst hk0
    have hanc : ancOf P t ∅ = t := by
      have h := hT.anc_dep ht
      change (SLOTreeStructure.ofM P).ts.anc t (depOf P t) = t at h
      rwa [hd] at h
    have hs : sig (uc t) = ∅ := (hsf t ht).isRelation.eq_empty_of_dom_eq_empty
      ((dom_sig_uc_eq_depOf hP ht).trans hd)
    unfold AncRel
    rw [hanc, hs, restrict_empty]
    exact ⟨rfl, isSubOne_refl _⟩
  have hdom : dom (sig (uc t)) = succ n := (dom_sig_uc_eq_depOf hP ht).trans hd
  rcases mem_or_eq_of_mem_succ hk with hk' | rfl
  swap
  · have hanc : ancOf P t (succ n) = t := by
      have h := hT.anc_dep ht
      change (SLOTreeStructure.ofM P).ts.anc t (depOf P t) = t at h
      rwa [hd] at h
    unfold AncRel
    rw [hanc, ← hdom, restrict_dom (hsf t ht)]
    exact ⟨rfl, isSubOne_refl _⟩
  have htr : t ∈ (SLOTreeStructure.ofM P).ts.nd \ (SLOTreeStructure.ofM P).ts.rt := by
    rw [mem_sdiff_iff, TreeStructure.mem_rt_iff]
    exact ⟨ht, fun h ↦ succ_ne_empty _ (hd.symm.trans h.right)⟩
  have hp : prtOf P t ∈ ndOf P := hT.prt_val_mem_nd htr
  have htc : t ∈ chdOf P (prtOf P t) := hT.mem_chd_prt_val htr
  have hdp : depOf P (prtOf P t) = n := by
    have h : depOf P t = succ (depOf P (prtOf P t)) := hT.dep_of_mem_chd _ hp _ htc
    rw [hd] at h
    exact (TreeStructure.eq_of_succ_eq_succ (ordinal_of_mem ordinal_omega hn) h).symm
  have hanc : ancOf P t k = ancOf P (prtOf P t) k :=
    hT.anc_prt_val htr (by change k ∈ succ (depOf P (prtOf P t)); rw [hdp]; exact hk')
  obtain ⟨ih1, ih2⟩ := ih _ hp hdp k hk'
  unfold AncRel
  obtain ⟨hr1, -, hr2, -⟩ := uc_rel_of_mem_chdOf hP hp htc
  have hkn : k ⊆ n := by
    intro z hz
    rcases mem_or_eq_of_mem_succ hk' with h | h
    · exact (ordinal_of_mem ordinal_omega hn).transitive _ h hz
    · rw [h] at hz
      exact hz
  rw [hanc, ih1, hr1, dom_sig_uc_eq_depOf hP hp, hdp, restrict_restrict]
  refine ⟨?_, ih2.trans hr2⟩
  congr 1
  ext z
  rw [mem_inter_iff]
  exact ⟨fun h ↦ h.right, fun h ↦ ⟨hkn h, h⟩⟩

end ChdRel

end Structure

section SubTree

/-! #### Tensor products with subtrees -/

variable {Y Y' Z Z' π a B : M}

theorem tensorProdATwoAOneBase_mem_aotci {Q : M} (hQ : Q ∈ aotci ((2 : ℕ) : M)) (X : M) :
    tensorProdATwoAOneBase Q X ∈ aotci ((1 : ℕ) : M) := by
  obtain ⟨hQf, hQdom, -⟩ := mem_aotci_iff.mp hQ
  have h12 : ((1 : ℕ) : M) ∈ (2 : M) := natCast_one_mem_two
  have h02 : (∅ : M) ∈ (2 : M) := natCast_mem_natCast_of_lt (j := 0) (k := 2) (by omega)
  have hPX : (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M) ∈ otci ((1 : ℕ) : M) := by
    rw [val_restrict Q hQf h12 (by rw [hQdom]; exact mem_succ_of_mem h12)]
    exact val_mem_otci_of_mem_aotci hQ (mem_succ_of_mem h12)
  refine tensorProdAOneAZero_mem_aotci ?_ hPX _
  rw [restrict_restrict,
    val_restrict Q hQf (by rw [mem_inter_iff]; exact ⟨h02, empty_mem_natCast_one⟩)
    (by rw [hQdom]; exact mem_succ_of_mem h02)]
  exact val_mem_otci_of_mem_aotci hQ (mem_succ_of_mem h02)

/-- The level-`0` tree of `Q ⊗ X` depends only on that of `X` -/
theorem tensorProdATwoAOne_val_zero_eq {Q X X' : M} (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hX : X ∈ aotci ((1 : ℕ) : M)) (hX' : X' ∈ aotci ((1 : ℕ) : M)) (h : X ﹫ ∅ = X' ﹫ ∅) :
    tensorProdATwoAOne Q X ﹫ ∅ = tensorProdATwoAOne Q X' ﹫ ∅ := by
  obtain ⟨hXf, hXdom, -⟩ := mem_aotci_iff.mp hX
  obtain ⟨hX'f, hX'dom, -⟩ := mem_aotci_iff.mp hX'
  have h01 : (∅ : M) ∈ succ ((1 : ℕ) : M) := mem_succ_of_mem empty_mem_natCast_one
  have hr : X ↾ ((1 : ℕ) : M) = X' ↾ ((1 : ℕ) : M) := by
    refine (hXf.restrict _).ext (hX'f.restrict _) ?_ fun i hi ↦ ?_
    · rw [dom_restrict_of_subset hXf (by rw [hXdom]; exact fun _ h ↦ mem_succ_of_mem h),
        dom_restrict_of_subset hX'f (by rw [hX'dom]; exact fun _ h ↦ mem_succ_of_mem h)]
    · rw [dom_restrict_of_subset hXf (by rw [hXdom]; exact fun _ h ↦ mem_succ_of_mem h)] at hi
      have hi0 : i = ∅ := by
        rw [natCast_succ, natCast_zero, mem_succ_iff] at hi
        rcases hi with h' | h'
        · exact h'
        · simp at h'
      subst hi0
      rw [val_restrict X hXf hi (by rw [hXdom]; exact h01),
        val_restrict X' hX'f hi (by rw [hX'dom]; exact h01), h]
  rw [tensorProdATwoAOne, tensorProdATwoAOne,
    cc_restrict_val_zero (tensorProdATwoAOneBase_mem_aotci hQ X),
    cc_restrict_val_zero (tensorProdATwoAOneBase_mem_aotci hQ X'), tensorProdATwoAOneBase,
    tensorProdATwoAOneBase, hr]


/-- In a tree of `otci_1`, every node lies in the linearly ordered set of the roots -/
theorem ndlosOf_of_mem_otci_one (hY : Y ∈ otci ((1 : ℕ) : M)) (ha : a ∈ ndOf Y) :
    ndlosOf Y a = rtlosOf Y ﹫ trvAZero := by
  have hS : (SLOTreeStructure.ofM Y).IsSLOTreeStructure := isSLOT_of_mem_otci hY
  have hT := hS.isTreeStructure
  have har : a ∈ rtOf Y := by
    rw [← ndOf_eq_rtOf_of_mem_otci_one hY]
    exact ha
  change ((SLOTreeStructure.ofM Y).sbllos ﹫ a) ﹫ (left a ﹫ ∅) = _
  rw [hS.sbllos_val ha, hT.sbl_val_of_mem_rt har]
  change ((SLOTreeStructure.ofM Y).rtlos) ﹫ (aoc (uc a)) = _
  rw [aoc_uc_eq_trvAZero_of_mem_otci_one hY ha]
  rfl

/-- The nodes of a tree in `otci_1` are roots of depth `0` -/
theorem depOf_of_mem_otci_one (hY : Y ∈ otci ((1 : ℕ) : M)) (ha : a ∈ ndOf Y) :
    depOf Y a = ∅ := by
  have har : a ∈ rtOf Y := by
    rw [← ndOf_eq_rtOf_of_mem_otci_one hY]
    exact ha
  exact (TreeStructure.mem_rt_iff.mp har).right

/-- An embedding of trees in `otci_1` is an order-preserving injection of the nodes -/
theorem isOtciEmbedding_iff_of_mem_otci_one (hY : Y ∈ otci ((1 : ℕ) : M))
    (hZ : Z ∈ otci ((1 : ℕ) : M)) : IsOtciEmbedding Y Z π ↔
      π !: ndOf Y ↪ ndOf Z ∧
        ∀ a ∈ ndOf Y, ∀ b ∈ ndOf Y, a [odrOne Y] b → (π ﹫ a) [odrOne Z] (π ﹫ b) := by
  rw [isOtciEmbedding_iff]
  constructor
  · rintro ⟨hinj, -, -, -, hodr, -⟩
    refine ⟨hinj, fun a ha b hb h ↦ ?_⟩
    have h' := hodr a ha b hb (by rw [ndlosOf_of_mem_otci_one hY ha,
      ndlosOf_of_mem_otci_one hY hb]) (by rw [ndlosOf_of_mem_otci_one hY ha]; exact h)
    rwa [ndlosOf_of_mem_otci_one hZ (hinj.isFunctionFromTo.val_mem ha)] at h'
  · rintro ⟨hinj, hodr⟩
    refine ⟨hinj, fun a ha ↦ ?_, fun a ha b hb hc ↦ ?_, fun a ha b hb ↦ ?_,
      fun a ha b hb _ h ↦ ?_, fun a ha ↦ ?_⟩
    · rw [depOf_of_mem_otci_one hZ (hinj.isFunctionFromTo.val_mem ha),
        depOf_of_mem_otci_one hY ha]
    · rw [chdOf_eq_empty_of_mem_otci_one hY ha] at hc
      simp at hc
    · rw [ndlosOf_of_mem_otci_one hZ (hinj.isFunctionFromTo.val_mem ha),
        ndlosOf_of_mem_otci_one hZ (hinj.isFunctionFromTo.val_mem hb),
        ndlosOf_of_mem_otci_one hY ha, ndlosOf_of_mem_otci_one hY hb]
      exact iff_of_true rfl rfl
    · rw [ndlosOf_of_mem_otci_one hY ha] at h
      rw [ndlosOf_of_mem_otci_one hZ (hinj.isFunctionFromTo.val_mem ha)]
      exact hodr a ha b hb h
    · rw [uc_eq_dctUZero_of_mem_otci_one hZ (hinj.isFunctionFromTo.val_mem ha),
        uc_eq_dctUZero_of_mem_otci_one hY ha]

/-- An embedding into a subtree is an embedding into the tree with its range in the subtree -/
theorem isOtciEmbedding_iff_of_isSubOne (hY : Y ∈ otci ((1 : ℕ) : M))
    (hZ' : Z' ∈ otci ((1 : ℕ) : M)) (hZ : Z ∈ otci ((1 : ℕ) : M)) (hsub : IsSubOne Z' Z) :
    IsOtciEmbedding Y Z' π ↔ IsOtciEmbedding Y Z π ∧ ran π ⊆ ndOf Z' := by
  rw [isOtciEmbedding_iff_of_mem_otci_one hY hZ', isOtciEmbedding_iff_of_mem_otci_one hY hZ]
  constructor
  · rintro ⟨hinj, hodr⟩
    refine ⟨⟨hinj.of_ran_subset (fun z hz ↦ hsub.left (hinj.ran_subset hz)), fun a ha b hb h ↦ ?_⟩,
      hinj.ran_subset⟩
    exact (hsub.right _ (hinj.isFunctionFromTo.val_mem ha) _
      (hinj.isFunctionFromTo.val_mem hb)).mp (hodr a ha b hb h)
  · rintro ⟨⟨hinj, hodr⟩, hran⟩
    have hinj' : π !: ndOf Y ↪ ndOf Z' := hinj.of_ran_subset hran
    refine ⟨hinj', fun a ha b hb h ↦ ?_⟩
    exact (hsub.right _ (hinj'.isFunctionFromTo.val_mem ha) _
      (hinj'.isFunctionFromTo.val_mem hb)).mpr (hodr a ha b hb h)

theorem odrOne_rtLosSLOT (hB : losSet B ≠ ∅) : odrOne (rtLosSLOT trvAZero B) = losOdr B := by
  rw [odrOne, rtlosOf_rtLosSLOT hB, singletonFun_val]

section Relabel

variable {P w w' : M}

/-- The relabeled copy `(w_uc, (w_lbl, W ⊗ Q))` of a node `w` -/
noncomputable def relabelOne (Q w : M) : M := !(uc w, !(lbl w, tensorProdAZeroAZero (aoc (uc w)) Q))

theorem isSetRestrictedTo_relabel (hP : P ∈ otci ((1 : ℕ) : M)) (Q : M) : IsSetRestrictedTo
    (fun p ↦ !(uc p, !(lbl p, tensorProdAZeroAZero (aoc (uc p)) Q))) (ndOf P) := by
  have h : IsSetRestrictedTo (fun p ↦ !(uc p, !(lbl p, tensorProdAZeroAZero trvAZero Q)))
      (ndOf P) := isSetRestrictedTo_of_definable _
  refine ⟨_, isFunction_toSetRestrictedTo h, dom_toSetRestrictedTo h, fun y hy ↦ ?_⟩
  rw [val_toSetRestrictedTo h hy]
  change _ = !(uc y, !(lbl y, tensorProdAZeroAZero (aoc (uc y)) Q))
  rw [aoc_uc_eq_trvAZero_of_mem_otci_one hP hy]

theorem tensorProdOneAZeroRelabel_val (hP : P ∈ otci ((1 : ℕ) : M)) (hw : w ∈ ndOf P) (Q : M) :
    tensorProdOneAZeroRelabel P Q ﹫ w = relabelOne Q w :=
  val_toSetRestrictedTo (isSetRestrictedTo_relabel hP Q) hw

theorem ndOf_tensorProdOneAZero (P Q : M) :
    ndOf (tensorProdOneAZero P Q) = ran (tensorProdOneAZeroRelabel P Q) := by
  rw [tensorProdOneAZero, ndOf_rtLosSLOT, losSet_orderedPair]

theorem mem_ndOf_tensorProdOneAZero_iff (hP : P ∈ otci ((1 : ℕ) : M)) (Q y : M) :
    y ∈ ndOf (tensorProdOneAZero P Q) ↔ ∃ w ∈ ndOf P, relabelOne Q w = y := by
  rw [ndOf_tensorProdOneAZero, mem_ran_tensorProdOneAZeroRelabel_iff hP]
  rfl

theorem relabelOne_injective (hP : P ∈ otci ((1 : ℕ) : M)) (hw : w ∈ ndOf P) (hw' : w' ∈ ndOf P)
    (h : relabelOne Q w = relabelOne Q w') : w = w' := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := isSLOT_of_mem_otci hP
  obtain ⟨u, l, rfl⟩ := hS.isOrderedPair hw
  obtain ⟨u', l', rfl⟩ := hS.isOrderedPair hw'
  simp only [relabelOne, uc_orderedPair, lbl_orderedPair, orderedPair_eq_orderedPair_iff] at h
  rw [h.left, h.right.left]

/-- The order of `P ⊗ Q` is that of the originals in `P` -/
theorem rel_odrOne_tensorProdOneAZero_iff (hP : P ∈ otci ((1 : ℕ) : M)) (hw : w ∈ ndOf P)
    (hw' : w' ∈ ndOf P) (Q : M) :
    (relabelOne Q w) [odrOne (tensorProdOneAZero P Q)] (relabelOne Q w') ↔ w [odrOne P] w' := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := isSLOT_of_mem_otci hP
  have hres' : IsSetRestrictedTo (fun y ↦ !(uc y, left (lbl y)))
      (ran (tensorProdOneAZeroRelabel P Q)) := isSetRestrictedTo_of_definable _
  have hmem {v : M} (hv : v ∈ ndOf P) : relabelOne Q v ∈ ran (tensorProdOneAZeroRelabel P Q) := by
    rw [mem_ran_tensorProdOneAZeroRelabel_iff hP]
    exact ⟨v, hv, rfl⟩
  have hun {v : M} (hv : v ∈ ndOf P) :
      tensorProdOneAZeroUnlabel P Q ﹫ relabelOne Q v = v := by
    rw [tensorProdOneAZeroUnlabel, val_toSetRestrictedTo hres' (hmem hv)]
    obtain ⟨u, l, rfl⟩ := hS.isOrderedPair hv
    simp only [relabelOne, uc_orderedPair, lbl_orderedPair, left_orderedPair]
  have hne : losSet !(ran (tensorProdOneAZeroRelabel P Q),
      pullback (tensorProdOneAZeroUnlabel P Q) (losOdr (rtlosOf P ﹫ trvAZero))
        (ran (tensorProdOneAZeroRelabel P Q))) ≠ ∅ := by
    rw [losSet_orderedPair]
    intro h
    have h' := hmem hw
    rw [h] at h'
    simp at h'
  rw [tensorProdOneAZero, odrOne_rtLosSLOT hne, losOdr_orderedPair]
  change !(relabelOne Q w, relabelOne Q w') ∈ pullback _ _ _ ↔ _
  rw [mem_pullback_iff, left_orderedPair, right_orderedPair, hun hw, hun hw', pair_mem_sprod_iff]
  exact ⟨fun h ↦ h.right, fun h ↦ ⟨⟨hmem hw, hmem hw'⟩, h⟩⟩

/-- The tensor product of a subtree is a subtree -/
theorem isSubOne_tensorProdOneAZero (hY' : Y' ∈ otci ((1 : ℕ) : M)) (hY : Y ∈ otci ((1 : ℕ) : M))
    (hsub : IsSubOne Y' Y) (Q : M) :
    IsSubOne (tensorProdOneAZero Y' Q) (tensorProdOneAZero Y Q) := by
  refine ⟨fun y hy ↦ ?_, fun a ha b hb ↦ ?_⟩
  · rw [mem_ndOf_tensorProdOneAZero_iff hY'] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    rw [mem_ndOf_tensorProdOneAZero_iff hY]
    exact ⟨w, hsub.left hw, rfl⟩
  · rw [mem_ndOf_tensorProdOneAZero_iff hY'] at ha hb
    obtain ⟨w, hw, rfl⟩ := ha
    obtain ⟨w', hw', rfl⟩ := hb
    rw [rel_odrOne_tensorProdOneAZero_iff hY' hw hw', rel_odrOne_tensorProdOneAZero_iff hY
      (hsub.left hw) (hsub.left hw')]
    exact hsub.right w hw w' hw'

end Relabel

section Tgt

variable {X X' A f : M}

theorem restrict_one_eq_of_val_zero_eq (hX : X ∈ aotci ((1 : ℕ) : M))
    (hX' : X' ∈ aotci ((1 : ℕ) : M)) (h : X ﹫ ∅ = X' ﹫ ∅) :
    X ↾ ((1 : ℕ) : M) = X' ↾ ((1 : ℕ) : M) := by
  obtain ⟨hXf, hXdom, -⟩ := mem_aotci_iff.mp hX
  obtain ⟨hX'f, hX'dom, -⟩ := mem_aotci_iff.mp hX'
  have h01 : (∅ : M) ∈ succ ((1 : ℕ) : M) := mem_succ_of_mem empty_mem_natCast_one
  refine (hXf.restrict _).ext (hX'f.restrict _) ?_ fun i hi ↦ ?_
  · rw [dom_restrict_of_subset hXf (by rw [hXdom]; exact fun _ h ↦ mem_succ_of_mem h),
      dom_restrict_of_subset hX'f (by rw [hX'dom]; exact fun _ h ↦ mem_succ_of_mem h)]
  · rw [dom_restrict_of_subset hXf (by rw [hXdom]; exact fun _ h ↦ mem_succ_of_mem h)] at hi
    have hi0 : i = ∅ := by
      rw [natCast_succ, natCast_zero, mem_succ_iff] at hi
      rcases hi with h' | h'
      · exact h'
      · simp at h'
    subst hi0
    rw [val_restrict X hXf hi (by rw [hXdom]; exact h01),
      val_restrict X' hX'f hi (by rw [hX'dom]; exact h01), h]

theorem tensorProdTwoAOneTgt_val_zero (X : M) :
    tensorProdTwoAOneTgt X ﹫ ∅ = tensorProdAZeroAZero (X ↾ ((1 : ℕ) : M)) trvAZero ﹫ ∅ := by
  have hA0 : IsFunction (tensorProdAZeroAZero (X ↾ ((1 : ℕ) : M)) trvAZero) :=
    isFunction_singletonFun _ _
  rw [tensorProdTwoAOneTgt, tensorProdAOneAZero, cc_val_of_mem hA0 _
    (by rw [dom_tensorProdAZeroAZero]; exact mem_succ_self _)]

theorem tensorProdTwoAOneTgt_val_one (X : M) :
    tensorProdTwoAOneTgt X ﹫ ((1 : ℕ) : M) = tensorProdOneAZero (X ﹫ ((1 : ℕ) : M)) trvAZero := by
  have hA0 : IsFunction (tensorProdAZeroAZero (X ↾ ((1 : ℕ) : M)) trvAZero) :=
    isFunction_singletonFun _ _
  have h := cc_val_self hA0 (tensorProdOneAZero (X ﹫ ((1 : ℕ) : M)) trvAZero)
  rw [dom_tensorProdAZeroAZero] at h
  exact h

/-- The embeddings into the target of a subtree are those into the target of the tree with their
range in the subtree -/
theorem mem_aotciEmbSet_tgt_iff (hA : A ∈ aotci ((1 : ℕ) : M)) (hX : X ∈ aotci ((1 : ℕ) : M))
    (hX' : X' ∈ aotci ((1 : ℕ) : M)) (h0 : X ﹫ ∅ = X' ﹫ ∅)
    (hsub : IsSubOne (X' ﹫ ((1 : ℕ) : M)) (X ﹫ ((1 : ℕ) : M))) :
    f ∈ aotciEmbSet ((1 : ℕ) : M) A (tensorProdTwoAOneTgt X') ↔
      f ∈ aotciEmbSet ((1 : ℕ) : M) A (tensorProdTwoAOneTgt X) ∧
        ran (f ﹫ ((1 : ℕ) : M)) ⊆ ndOf (tensorProdTwoAOneTgt X' ﹫ ((1 : ℕ) : M)) := by
  obtain ⟨hAf, hAdom, -⟩ := mem_aotci_iff.mp hA
  have hT := tensorProdTwoAOneTgt_mem hX
  have hT' := tensorProdTwoAOneTgt_mem hX'
  obtain ⟨hTf, hTdom, -⟩ := mem_aotci_iff.mp hT
  obtain ⟨hT'f, hT'dom, -⟩ := mem_aotci_iff.mp hT'
  have h1s : ((1 : ℕ) : M) ∈ succ ((1 : ℕ) : M) := mem_succ_self _
  have hA1 := val_mem_otci_of_mem_aotci hA h1s
  have hY := val_mem_otci_of_mem_aotci hX h1s
  have hY' := val_mem_otci_of_mem_aotci hX' h1s
  have hTv0 : tensorProdTwoAOneTgt X' ﹫ ∅ = tensorProdTwoAOneTgt X ﹫ ∅ := by
    rw [tensorProdTwoAOneTgt_val_zero, tensorProdTwoAOneTgt_val_zero,
      restrict_one_eq_of_val_zero_eq hX hX' h0]
  have hsub' : IsSubOne (tensorProdTwoAOneTgt X' ﹫ ((1 : ℕ) : M))
      (tensorProdTwoAOneTgt X ﹫ ((1 : ℕ) : M)) := by
    rw [tensorProdTwoAOneTgt_val_one, tensorProdTwoAOneTgt_val_one]
    exact isSubOne_tensorProdOneAZero hY' hY hsub _
  have hZ := val_mem_otci_of_mem_aotci hT h1s
  have hZ' := val_mem_otci_of_mem_aotci hT' h1s
  constructor
  · intro hf
    have he := (mem_aotciEmbSet_iff.mp hf).right
    have he1 := (isOtciEmbedding_iff_of_isSubOne hA1 hZ' hZ hsub').mp (he.isOtciEmbedding h1s)
    refine ⟨mem_aotciEmbSet_of_isAotciEmbedding hAf hAdom hTf hTdom
      ⟨he.isFunction, he.dom_eq, fun {i} hi ↦ ?_⟩, he1.right⟩
    rcases mem_succ_one_cases hi with rfl | rfl
    · rw [← hTv0]
      exact he.isOtciEmbedding hi
    · exact he1.left
  · rintro ⟨hf, hran⟩
    have he := (mem_aotciEmbSet_iff.mp hf).right
    refine mem_aotciEmbSet_of_isAotciEmbedding hAf hAdom hT'f hT'dom
      ⟨he.isFunction, he.dom_eq, fun {i} hi ↦ ?_⟩
    rcases mem_succ_one_cases hi with rfl | rfl
    · rw [hTv0]
      exact he.isOtciEmbedding hi
    · exact (isOtciEmbedding_iff_of_isSubOne hA1 hZ' hZ hsub').mpr
        ⟨he.isOtciEmbedding h1s, hran⟩

end Tgt

section Sub

variable {Q X X' x y n : M}

theorem tensorProdATwoAOneBase_val_one (Q X : M) :
    tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M) =
      tensorProdOneAZero ((Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M)) (X ↾ ((1 : ℕ) : M)) := by
  have hA0 : IsFunction (tensorProdAZeroAZero ((Q ↾ (2 : M)) ↾ ((1 : ℕ) : M))
      (X ↾ ((1 : ℕ) : M))) := isFunction_singletonFun _ _
  have h := cc_val_self hA0
    (tensorProdOneAZero ((Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M)) (X ↾ ((1 : ℕ) : M)))
  rw [dom_tensorProdAZeroAZero] at h
  exact h

/-- The nodes of `B(1)` and of `Q(2) ⊗ X` are disjoint -/
theorem ndOf_base_inter_ndOf_tensorProdTwoAOne (hQ : Q ∈ aotci ((2 : ℕ) : M)) (X : M) :
    ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ∩
      ndOf (tensorProdTwoAOne (Q ﹫ (2 : M)) X) = ∅ := by
  obtain ⟨hQf, hQdom, -⟩ := mem_aotci_iff.mp hQ
  have h12 : ((1 : ℕ) : M) ∈ (2 : M) := natCast_one_mem_two
  have hPX : (Q ↾ (2 : M)) ﹫ ((1 : ℕ) : M) ∈ otci ((1 : ℕ) : M) := by
    rw [val_restrict Q hQf h12 (by rw [hQdom]; exact mem_succ_of_mem h12)]
    exact val_mem_otci_of_mem_aotci hQ (mem_succ_of_mem h12)
  rw [empty_iff]
  intro a ha
  rw [mem_inter_iff] at ha
  obtain ⟨ha1, ha2⟩ := ha
  have hresN : IsSetRestrictedTo (fun x ↦ !(dctUZero, x))
      (tensorProdTwoAOneLbls (Q ﹫ (2 : M)) X) := isSetRestrictedTo_of_definable _
  rw [tensorProdTwoAOne, ndOf_rtLosSLOT, losSet_orderedPair] at ha2
  obtain ⟨x, hx, rfl⟩ := (mem_ran_toSetRestrictedTo_iff hresN).mp ha2
  obtain ⟨p, -, -, f, hf, rfl⟩ := mem_tensorProdTwoAOneLbls_iff.mp hx
  rw [tensorProdATwoAOneBase_val_one, tensorProdOneAZero, ndOf_rtLosSLOT, losSet_orderedPair,
    mem_ran_tensorProdOneAZeroRelabel_iff hPX] at ha1
  obtain ⟨q, -, hq⟩ := ha1
  rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at hq
  have hdom := congrArg dom hq.right.right
  rw [dom_tensorProdAZeroAZero, (mem_aotciEmbSet_iff.mp hf).right.dom_eq] at hdom
  have h1 : (∅ : M) = succ ∅ := TreeStructure.eq_of_succ_eq_succ ordinal_empty hdom
  exact succ_ne_empty _ h1.symm

omit [ModelsZF M] in
theorem bkLt_congr {R R' s t C : M} (hs : ∀ k ∈ dom s, s ﹫ k ∈ C)
    (ht : ∀ k ∈ dom t, t ﹫ k ∈ C) (hRR : ∀ a ∈ C, ∀ b ∈ C, a [R] b ↔ a [R'] b) :
    BKLt R s t ↔ BKLt R' s t := by
  unfold BKLt
  constructor
  · rintro (h | ⟨k, hks, hkt, hres, h⟩)
    · exact .inl h
    · exact .inr ⟨k, hks, hkt, hres, (hRR _ (hs k hks) _ (ht k hkt)).mp h⟩
  · rintro (h | ⟨k, hks, hkt, hres, h⟩)
    · exact .inl h
    · exact .inr ⟨k, hks, hkt, hres, (hRR _ (hs k hks) _ (ht k hkt)).mpr h⟩

theorem lexProd_agree {R R' A A' S B u v : M} (hA : A' ⊆ A)
    (hR : ∀ a ∈ A', ∀ b ∈ A', a [R'] b ↔ a [R] b) (hu : u ∈ A' ×ˢ B) (hv : v ∈ A' ×ˢ B) :
    u [lexProd R' A' S B] v ↔ u [lexProd R A S B] v := by
  rw [mem_sprod_iff] at hu hv
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hu
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := hv
  rw [rel_lexProd_iff, rel_lexProd_iff, hR u₁ hu₁ v₁ hv₁]
  exact ⟨fun h ↦ ⟨⟨hA hu₁, hu₂⟩, ⟨hA hv₁, hv₂⟩, h.right.right⟩,
    fun h ↦ ⟨⟨hu₁, hu₂⟩, ⟨hv₁, hv₂⟩, h.right.right⟩⟩

theorem isSubOne_tensorProdTwoAOneTgt_val_one (hX : X ∈ aotci ((1 : ℕ) : M))
    (hX' : X' ∈ aotci ((1 : ℕ) : M)) (hsub : IsSubOne (X' ﹫ ((1 : ℕ) : M)) (X ﹫ ((1 : ℕ) : M))) :
    IsSubOne (tensorProdTwoAOneTgt X' ﹫ ((1 : ℕ) : M))
      (tensorProdTwoAOneTgt X ﹫ ((1 : ℕ) : M)) := by
  have h1s : ((1 : ℕ) : M) ∈ succ ((1 : ℕ) : M) := mem_succ_self _
  rw [tensorProdTwoAOneTgt_val_one, tensorProdTwoAOneTgt_val_one]
  exact isSubOne_tensorProdOneAZero (val_mem_otci_of_mem_aotci hX' h1s)
    (val_mem_otci_of_mem_aotci hX h1s) hsub _

theorem ndOf_tensorProdTwoAOne (P X : M) :
    ndOf (tensorProdTwoAOne P X) = tensorProdTwoAOneNds P X := by
  rw [tensorProdTwoAOne, ndOf_rtLosSLOT, losSet_orderedPair]

theorem rel_odrOne_tensorProdTwoAOne_iff {P X a b : M} (ha : a ∈ tensorProdTwoAOneNds P X) :
    a [odrOne (tensorProdTwoAOne P X)] b ↔ (a ∈ tensorProdTwoAOneNds P X ∧
      b ∈ tensorProdTwoAOneNds P X) ∧ TensorProdTwoAOneLt P X (lbl a) (lbl b) := by
  have hne : losSet !(tensorProdTwoAOneNds P X, tensorProdTwoAOneOdr P X) ≠ ∅ := by
    rw [losSet_orderedPair]
    intro h
    rw [h] at ha
    simp at ha
  rw [tensorProdTwoAOne, odrOne_rtLosSLOT hne, losOdr_orderedPair]
  change !(a, b) ∈ tensorProdTwoAOneOdr P X ↔ _
  rw [mem_tensorProdTwoAOneOdr_iff, pair_mem_sprod_iff, left_orderedPair, right_orderedPair]

theorem tensorProdATwoAOne_val_one_eq (hQ : Q ∈ aotci ((2 : ℕ) : M)) (X : M) :
    tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M) =
    rtLosSLOT trvAZero (losConcat
      (rtlosOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ﹫ trvAZero)
      (rtlosOf (tensorProdTwoAOne (Q ﹫ 2) X) ﹫ trvAZero)) :=
  cc_restrict_val_one (tensorProdATwoAOneBase_mem_aotci hQ X) _

variable (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hX : X ∈ aotci ((1 : ℕ) : M))
  (hX' : X' ∈ aotci ((1 : ℕ) : M)) (h0 : X ﹫ ∅ = X' ﹫ ∅)
  (hsub : IsSubOne (X' ﹫ ((1 : ℕ) : M)) (X ﹫ ((1 : ℕ) : M)))
include hQ hX hX' h0 hsub

theorem mem_tensorProdTwoAOneLbls_iff_of_isSubOne :
    x ∈ tensorProdTwoAOneLbls (Q ﹫ (2 : M)) X' ↔ x ∈ tensorProdTwoAOneLbls (Q ﹫ (2 : M)) X ∧
      ran (right x ﹫ ((1 : ℕ) : M)) ⊆ ndOf (tensorProdTwoAOneTgt X' ﹫ ((1 : ℕ) : M)) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  rw [mem_tensorProdTwoAOneLbls_iff, mem_tensorProdTwoAOneLbls_iff]
  have hA {p : M} (hp : p ∈ ndOf (Q ﹫ (2 : M))) : aoc (uc p) ∈ aotci ((1 : ℕ) : M) :=
    aoc_mem_aotci_of_mem_stduoci_one ((otciCond_two hQ2).right.left p hp).left
  constructor
  · rintro ⟨p, hp, hpr, f, hf, rfl⟩
    obtain ⟨hf', hran⟩ := (mem_aotciEmbSet_tgt_iff (hA hp) hX hX' h0 hsub).mp hf
    exact ⟨⟨p, hp, hpr, f, hf', rfl⟩, by rw [right_orderedPair]; exact hran⟩
  · rintro ⟨⟨p, hp, hpr, f, hf, rfl⟩, hran⟩
    rw [right_orderedPair] at hran
    exact ⟨p, hp, hpr, f, (mem_aotciEmbSet_tgt_iff (hA hp) hX hX' h0 hsub).mpr ⟨hf, hran⟩, rfl⟩

omit h0 in
theorem tensorProdTwoAOneLt_iff_of_isSubOne (hx : x ∈ tensorProdTwoAOneLbls (Q ﹫ (2 : M)) X')
    (hy : y ∈ tensorProdTwoAOneLbls (Q ﹫ (2 : M)) X') :
    TensorProdTwoAOneLt (Q ﹫ (2 : M)) X' x y ↔ TensorProdTwoAOneLt (Q ﹫ (2 : M)) X x y := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hsub' := isSubOne_tensorProdTwoAOneTgt_val_one hX hX' hsub
  have hco {z : M} (hz : z ∈ tensorProdTwoAOneLbls (Q ﹫ (2 : M)) X') :
      ∀ k ∈ dom (tensorProdTwoAOneSeq (Q ﹫ (2 : M)) z),
        tensorProdTwoAOneSeq (Q ﹫ (2 : M)) z ﹫ k ∈
        ndOf (tensorProdTwoAOneTgt X' ﹫ ((1 : ℕ) : M)) ×ˢ ndOf (Q ﹫ (2 : M)) := by
    obtain ⟨p, hp, -, f, hf, rfl⟩ := mem_tensorProdTwoAOneLbls_iff.mp hz
    intro k hk
    rw [tensorProdTwoAOneSeq_dom] at hk
    exact tensorProdTwoAOneSeq_val_mem hQ2 hp hf hk
  unfold TensorProdTwoAOneLt tensorProdTwoAOneCoordOdr
  exact bkLt_congr (hco hx) (hco hy) fun a ha b hb ↦
    lexProd_agree (R := odrOne (tensorProdTwoAOneTgt X ﹫ ((1 : ℕ) : M)))
      (R' := odrOne (tensorProdTwoAOneTgt X' ﹫ ((1 : ℕ) : M))) hsub'.left hsub'.right ha hb

theorem mem_tensorProdTwoAOneNds_iff_of_isSubOne :
    n ∈ tensorProdTwoAOneNds (Q ﹫ (2 : M)) X' ↔ n ∈ tensorProdTwoAOneNds (Q ﹫ (2 : M)) X ∧
      ran (right (lbl n) ﹫ ((1 : ℕ) : M)) ⊆ ndOf (tensorProdTwoAOneTgt X' ﹫ ((1 : ℕ) : M)) := by
  have hres (X : M) : IsSetRestrictedTo (fun x ↦ !(dctUZero, x))
      (tensorProdTwoAOneLbls (Q ﹫ (2 : M)) X) := isSetRestrictedTo_of_definable _
  rw [tensorProdTwoAOneNds, tensorProdTwoAOneNds, mem_ran_toSetRestrictedTo_iff (hres _),
    mem_ran_toSetRestrictedTo_iff (hres _)]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [lbl_orderedPair]
    obtain ⟨hx', hran⟩ := (mem_tensorProdTwoAOneLbls_iff_of_isSubOne hQ hX hX' h0 hsub).mp hx
    exact ⟨⟨x, hx', rfl⟩, hran⟩
  · rintro ⟨⟨x, hx, rfl⟩, hran⟩
    rw [lbl_orderedPair] at hran
    exact ⟨x, (mem_tensorProdTwoAOneLbls_iff_of_isSubOne hQ hX hX' h0 hsub).mpr ⟨hx, hran⟩, rfl⟩

theorem isSubOne_tensorProdTwoAOne :
    IsSubOne (tensorProdTwoAOne (Q ﹫ (2 : M)) X') (tensorProdTwoAOne (Q ﹫ (2 : M)) X) := by
  have hNds (a : M) (ha : a ∈ tensorProdTwoAOneNds (Q ﹫ (2 : M)) X') :
      a ∈ tensorProdTwoAOneNds (Q ﹫ (2 : M)) X :=
    ((mem_tensorProdTwoAOneNds_iff_of_isSubOne hQ hX hX' h0 hsub).mp ha).left
  have hlbl (a : M) (ha : a ∈ tensorProdTwoAOneNds (Q ﹫ (2 : M)) X') :
      lbl a ∈ tensorProdTwoAOneLbls (Q ﹫ (2 : M)) X' := by
    have hres : IsSetRestrictedTo (fun x ↦ !(dctUZero, x))
        (tensorProdTwoAOneLbls (Q ﹫ (2 : M)) X') := isSetRestrictedTo_of_definable _
    rw [tensorProdTwoAOneNds, mem_ran_toSetRestrictedTo_iff hres] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [lbl_orderedPair]
    exact hx
  rw [IsSubOne, ndOf_tensorProdTwoAOne, ndOf_tensorProdTwoAOne]
  refine ⟨hNds, fun a ha b hb ↦ ?_⟩
  rw [rel_odrOne_tensorProdTwoAOne_iff ha, rel_odrOne_tensorProdTwoAOne_iff (hNds a ha),
    tensorProdTwoAOneLt_iff_of_isSubOne hQ hX hX' hsub (hlbl a ha) (hlbl b hb)]
  exact ⟨fun h ↦ ⟨⟨hNds a ha, hNds b hb⟩, h.right⟩, fun h ↦ ⟨⟨ha, hb⟩, h.right⟩⟩

/-- The tensor product with a subtree is a subtree -/
theorem isSubOne_tensorProdATwoAOne :
    IsSubOne (tensorProdATwoAOne Q X' ﹫ ((1 : ℕ) : M))
      (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M)) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hbase : tensorProdATwoAOneBase Q X' = tensorProdATwoAOneBase Q X := by
    rw [tensorProdATwoAOneBase, tensorProdATwoAOneBase, restrict_one_eq_of_val_zero_eq hX hX' h0]
  have hB1 := val_mem_otci_of_mem_aotci (tensorProdATwoAOneBase_mem_aotci hQ X) (mem_succ_self _)
  have hC := tensorProdTwoAOne_mem_otci hQ2 hX
  have hC' := tensorProdTwoAOne_mem_otci hQ2 hX'
  obtain ⟨hRB, hsB, -⟩ := rtlosOf_of_mem_otci_one hB1
  obtain ⟨hRC, hsC, -⟩ := rtlosOf_of_mem_otci_one hC
  obtain ⟨hRC', hsC', -⟩ := rtlosOf_of_mem_otci_one hC'
  have hsubC := isSubOne_tensorProdTwoAOne hQ hX hX' h0 hsub
  have hdisj := ndOf_base_inter_ndOf_tensorProdTwoAOne hQ X
  have hdisj' (z : M) (hzB : z ∈ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)))
      (hzC : z ∈ ndOf (tensorProdTwoAOne (Q ﹫ 2) X)) : False := by
    have h : z ∈ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ∩
        ndOf (tensorProdTwoAOne (Q ﹫ 2) X) := by
      rw [mem_inter_iff]
      exact ⟨hzB, hzC⟩
    rw [hdisj] at h
    simp at h
  have hnd (X : M) : ndOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M)) =
      losSet (rtlosOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ﹫ trvAZero) ∪
        losSet (rtlosOf (tensorProdTwoAOne (Q ﹫ 2) X) ﹫ trvAZero) := by
    rw [tensorProdATwoAOne_val_one_eq hQ, ndOf_rtLosSLOT, losConcat, losSet_orderedPair]
  have hodr (X : M) (hne : ndOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M)) ≠ ∅) :
      odrOne (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M)) =
        concat (losOdr (rtlosOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ﹫ trvAZero))
          (losSet (rtlosOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ﹫ trvAZero))
          (losOdr (rtlosOf (tensorProdTwoAOne (Q ﹫ 2) X) ﹫ trvAZero))
          (losSet (rtlosOf (tensorProdTwoAOne (Q ﹫ 2) X) ﹫ trvAZero)) := by
    rw [tensorProdATwoAOne_val_one_eq hQ] at hne ⊢
    rw [ndOf_rtLosSLOT] at hne
    rw [odrOne_rtLosSLOT hne, losConcat, losOdr_orderedPair]
  rw [IsSubOne, hnd, hnd, hbase, hsB, hsC, hsC']
  refine ⟨fun z hz ↦ ?_, fun a ha b hb ↦ ?_⟩
  · rw [mem_union_iff] at hz ⊢
    rcases hz with hz | hz
    · exact .inl hz
    · exact .inr (hsubC.left hz)
  have hne' : ndOf (tensorProdATwoAOne Q X' ﹫ ((1 : ℕ) : M)) ≠ ∅ := by
    rw [hnd, hbase, hsB, hsC']
    intro h
    rw [h] at ha
    simp at ha
  have hne : ndOf (tensorProdATwoAOne Q X ﹫ ((1 : ℕ) : M)) ≠ ∅ := by
    rw [hnd, hsB, hsC]
    intro h
    have ha' : a ∈ ndOf (tensorProdATwoAOneBase Q X ﹫ ((1 : ℕ) : M)) ∪
        ndOf (tensorProdTwoAOne (Q ﹫ 2) X) := by
      rw [mem_union_iff] at ha ⊢
      rcases ha with ha | ha
      · exact .inl ha
      · exact .inr (hsubC.left ha)
    rw [h] at ha'
    simp at ha'
  rw [hodr X' hne', hodr X hne, hbase, rel_concat_iff, rel_concat_iff, hsB, hsC, hsC']
  have hRC'o : IsStrictLinearOrder (odrOne (tensorProdTwoAOne (Q ﹫ 2) X'))
      (ndOf (tensorProdTwoAOne (Q ﹫ 2) X')) := hRC'
  have hRCo : IsStrictLinearOrder (odrOne (tensorProdTwoAOne (Q ﹫ 2) X))
      (ndOf (tensorProdTwoAOne (Q ﹫ 2) X)) := hRC
  have hS : a [odrOne (tensorProdTwoAOne (Q ﹫ 2) X')] b ↔
      a [odrOne (tensorProdTwoAOne (Q ﹫ 2) X)] b := by
    rw [mem_union_iff] at ha hb
    rcases ha with ha | ha
    · exact iff_of_false (fun h ↦ hdisj' a ha (hsubC.left (hRC'o.mem_left h)))
        (fun h ↦ hdisj' a ha (hRCo.mem_left h))
    rcases hb with hb | hb
    · exact iff_of_false (fun h ↦ hdisj' b hb (hsubC.left (hRC'o.mem_right h)))
        (fun h ↦ hdisj' b hb (hRCo.mem_right h))
    exact hsubC.right a ha b hb
  have hBb : b ∈ ndOf (tensorProdTwoAOne (Q ﹫ 2) X') ↔
      b ∈ ndOf (tensorProdTwoAOne (Q ﹫ 2) X) := by
    rw [mem_union_iff] at hb
    rcases hb with hb | hb
    · exact iff_of_false (fun h ↦ hdisj' b hb (hsubC.left h)) (fun h ↦ hdisj' b hb h)
    · exact iff_of_true hb (hsubC.left hb)
  change _ ∨ a [odrOne (tensorProdTwoAOne (Q ﹫ 2) X')] b ∨ _ ↔
    _ ∨ a [odrOne (tensorProdTwoAOne (Q ﹫ 2) X)] b ∨ _
  rw [hS, hBb]

end Sub

end SubTree

section AncAnc

variable {P a j k : M}

/-- The ancestors of the ancestors of the nodes of depth `n` -/
def AncAncCond (P n : M) : Prop :=
  ∀ a ∈ ndOf P, depOf P a = n → ∀ j ∈ succ n, ∀ k ∈ succ j,
    ancOf P (ancOf P a j) k = ancOf P a k

instance (P : M) : Class.Definable (fun n : M ↦ AncAncCond P n) Set.univ := by
  have h : (fun n : M ↦ AncAncCond P n) = fun n : M ↦ ∃ P' N : M, P' = P ∧ N = ndOf P ∧
      ∀ a ∈ N, depOf P' a = n → ∀ j ∈ succ n, ∀ k ∈ succ j,
        ∃ b c : M, ancOf P' a j = b ∧ ancOf P' b k = c ∧ ancOf P' a k = c := by
    funext n
    apply propext
    constructor
    · intro h
      exact ⟨P, _, rfl, rfl, fun a ha hd j hj k hk ↦
        ⟨_, _, rfl, rfl, (h a ha hd j hj k hk).symm⟩⟩
    · rintro ⟨P', N, rfl, rfl, h⟩ a ha hd j hj k hk
      obtain ⟨b, c, hb, hc, hc'⟩ := h a ha hd j hj k hk
      rw [hb, hc, hc']
  rw [h]
  infer_instance

/-- The ancestor of depth `k` of the ancestor of depth `j ≥ k` of `a` is the ancestor of depth `k`
of `a` -/
theorem ancOf_ancOf (hP : IsSLOT P) (ha : a ∈ ndOf P) (hj : j ∈ succ (depOf P a))
    (hk : k ∈ succ j) : ancOf P (ancOf P a j) k = ancOf P a k := by
  have hS : (SLOTreeStructure.ofM P).IsSLOTreeStructure := hP
  have hT := hS.isTreeStructure
  suffices h : AncAncCond P (depOf P a) from h a ha rfl j hj k hk
  refine omega_induction (A := fun n ↦ AncAncCond P n)
    (fun a ha hd j hj k hk ↦ ?_) (fun n hn ih a ha hd j hj k hk ↦ ?_) (hT.dep_mem_omega ha)
  · have hanc : ancOf P a ∅ = a := by
      have h := hT.anc_dep ha
      change (SLOTreeStructure.ofM P).ts.anc a (depOf P a) = a at h
      rwa [hd] at h
    have hj0 : j = ∅ := by
      rw [mem_succ_iff] at hj
      rcases hj with h | h
      · exact h
      · exact absurd h (by simp)
    subst hj0
    have hk0 : k = ∅ := by
      rw [mem_succ_iff] at hk
      rcases hk with h | h
      · exact h
      · exact absurd h (by simp)
    subst hk0
    rw [hanc, hanc]
  rcases mem_or_eq_of_mem_succ hj with hj' | rfl
  swap
  · have hanc : ancOf P a (succ n) = a := by
      have h := hT.anc_dep ha
      change (SLOTreeStructure.ofM P).ts.anc a (depOf P a) = a at h
      rwa [hd] at h
    rw [hanc]
  have htr : a ∈ (SLOTreeStructure.ofM P).ts.nd \ (SLOTreeStructure.ofM P).ts.rt := by
    rw [mem_sdiff_iff, TreeStructure.mem_rt_iff]
    exact ⟨ha, fun h ↦ succ_ne_empty _ (hd.symm.trans h.right)⟩
  have hp : prtOf P a ∈ ndOf P := hT.prt_val_mem_nd htr
  have hac : a ∈ chdOf P (prtOf P a) := hT.mem_chd_prt_val htr
  have hdp : depOf P (prtOf P a) = n := by
    have h : depOf P a = succ (depOf P (prtOf P a)) := hT.dep_of_mem_chd _ hp _ hac
    rw [hd] at h
    exact (TreeStructure.eq_of_succ_eq_succ (ordinal_of_mem ordinal_omega hn) h).symm
  have hkn : k ∈ succ n := by
    rcases mem_or_eq_of_mem_succ hk with h | h
    · exact (ordinal_of_mem ordinal_omega (succ_mem_omega hn)).transitive _ hj' h
    · rw [h]
      exact hj'
  have h1 : ancOf P a j = ancOf P (prtOf P a) j :=
    hT.anc_prt_val htr (by change j ∈ succ (depOf P (prtOf P a)); rw [hdp]; exact hj')
  have h2 : ancOf P a k = ancOf P (prtOf P a) k :=
    hT.anc_prt_val htr (by change k ∈ succ (depOf P (prtOf P a)); rw [hdp]; exact hkn)
  rw [h1, h2]
  exact ih _ hp hdp j hj' k hk

section CtChd

variable {T p c c' : M}

theorem ndlosOf_eq_chdlosOf (hT : IsSLOT T) (hp : p ∈ ndOf T) (hc : c ∈ chdOf T p) :
    ndlosOf T c = chdlosOf T p ﹫ (left c ﹫ ∅) := by
  have hS : (SLOTreeStructure.ofM T).IsSLOTreeStructure := hT
  have hTs := hS.isTreeStructure
  have hne : (SLOTreeStructure.ofM T).chd ﹫ p ≠ ∅ := by
    rw [ne_empty_iff]
    exact ⟨c, hc⟩
  have hX : (SLOTreeStructure.ofM T).chd ﹫ p ∈ (SLOTreeStructure.ofM T).sblptn := by
    rw [TreeStructure.mem_sblptn_iff, hTs.isFunction_chd.mem_ran_iff, hTs.dom_chd]
    exact ⟨.inr ⟨p, hp, rfl⟩, hne⟩
  have hcn : c ∈ ndOf T := mem_ndOf_of_mem_chdOf hT hc
  change ((SLOTreeStructure.ofM T).sbllos ﹫ c) ﹫ (left c ﹫ ∅) = _
  rw [hS.sbllos_val hcn, hTs.sbl_val_of_mem_sblptn hX hc, chdlosOf,
    hS.chdlos_val (hS.mem_dom_chdlos_iff.mpr ⟨hp, hne⟩)]

/-- The least child of `p` with the key of the child `c`: a child of type `ct`, with the signature
of `c`, without children, and below the other children with that key -/
theorem ctChd_spec {n : M} (hn : n ∈ (ω : M)) (hn0 : n ≠ ∅) (hT : T ∈ otci n) (hp : p ∈ ndOf T)
    (hc : c ∈ chdOf T p) :
    ctChd T p (aoc (uc c)) ∈ chdOf T p ∧ aoc (uc (ctChd T p (aoc (uc c)))) = aoc (uc c) ∧
      sig (uc (ctChd T p (aoc (uc c)))) = sig (uc c) ∧ ctp (uc (ctChd T p (aoc (uc c)))) = ct ∧
      chdOf T (ctChd T p (aoc (uc c))) = ∅ ∧
      ∀ c' ∈ chdOf T p, aoc (uc c') = aoc (uc c) →
        c' = ctChd T p (aoc (uc c)) ∨ (ctChd T p (aoc (uc c))) [sblOdrOf T] c' := by
  have hTs : IsSLOT T := isSLOT_of_mem_otci hT
  obtain ⟨hmω, hmn, -⟩ := sUnion_mem_of_ne_empty hn hn0
  have hT' := hT
  rw [mem_otci_iff_of_ne_empty hn0] at hT'
  obtain ⟨-, -, -, -, hchd⟩ := hT'
  obtain ⟨q, hq, hqk⟩ := ((hchd p hp).left (aoc (uc c))).mp ⟨c, hc, rfl⟩
  have hkey : aoc q = left c ﹫ ∅ := hqk
  have hB := isStrictLinearOrderedSet_chdlosOf hTs hp hc
  rw [← hkey] at hB
  have hmemB (x : M) : x ∈ losSet (chdlosOf T p ﹫ aoc q) ↔
      x ∈ chdOf T p ∧ aoc (uc x) = aoc (uc c) := by
    rw [hkey]
    exact mem_losSet_chdlosOf_iff hTs hp hc x
  obtain ⟨r, hr, hrl⟩ := (hchd p hp).right.right q hq
  have hRo := hB.isStrictLinearOrder
  have hctr : ctChd T p (aoc (uc c)) = r := by
    rw [ctChd, ← hqk]
    rw [show (losSet (chdlosOf T p ﹫ aoc q) ∩₀ fun r ↦ IsLeastLos (chdlosOf T p ﹫ aoc q) r) =
        {r} from ?_, sUnion_singleton]
    ext x
    rw [mem_comprehension_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxl⟩
      rcases hRo.trichotomous hx hr with h | h | h
      · exact (hrl.right x hx h).elim
      · exact h
      · exact (hxl.right r hr h).elim
    · rintro rfl
      exact ⟨hr, hrl⟩
  rw [hctr]
  obtain ⟨hrc, hrk⟩ := (hmemB r).mp hr
  have hsig := (hchd p hp).right.left q hq r hr
  have hcB : c ∈ losSet (chdlosOf T p ﹫ aoc q) := (hmemB c).mpr ⟨hc, rfl⟩
  have hsigc := ((hchd p hp).right.left q hq c hcB).left
  have hct : ctp (uc r) = ct := hsig.right.mp hrl
  rw [extL_ciRec_restrict hmn] at hq
  refine ⟨hrc, hrk, hsig.left.trans hsigc.symm, hct,
    chdOf_eq_empty_of_ctp_eq_ct hn hT (mem_ndOf_of_mem_chdOf hTs hrc) hct, fun c' hc' hk ↦ ?_⟩
  have hc'B : c' ∈ losSet (chdlosOf T p ﹫ aoc q) := (hmemB c').mpr ⟨hc', hk⟩
  rcases hRo.trichotomous hc'B hr with h | h | h
  · exact (hrl.right c' hc'B h).elim
  · exact .inl h
  · right
    rw [rel_sblOdrOf_iff hTs]
    have hl1 : ndlosOf T r = chdlosOf T p ﹫ aoc q := by
      rw [ndlosOf_eq_chdlosOf hTs hp hrc, hkey]
      change chdlosOf T p ﹫ aoc (uc r) = chdlosOf T p ﹫ aoc (uc c)
      rw [hrk]
    have hl2 : ndlosOf T c' = chdlosOf T p ﹫ aoc q := by
      rw [ndlosOf_eq_chdlosOf hTs hp hc', hkey]
      change chdlosOf T p ﹫ aoc (uc c') = chdlosOf T p ﹫ aoc (uc c)
      rw [hk]
    refine ⟨mem_ndOf_of_mem_chdOf hTs hrc, mem_ndOf_of_mem_chdOf hTs hc', hl1.trans hl2.symm, ?_⟩
    rw [hl1]
    exact h

end CtChd

end AncAnc

section NodesTwo

/-! #### The nodes of `(Q ⊗ X)(1)` from `Q(2)` -/

variable {P Q X X' w y i : M}

theorem tpOrig_one_relabelOne (hX : X ∈ aotci ((1 : ℕ) : M))
    (hw : w ∈ ndOf (X ﹫ ((1 : ℕ) : M))) :
    tpOrig X ((1 : ℕ) : M) (relabelOne trvAZero w) = w := by
  have hX1 := val_mem_otci_of_mem_aotci hX (mem_succ_self _)
  ext z
  rw [mem_tpOrig_iff]
  constructor
  · rintro ⟨w', hw', h | h, hz⟩
    · exact absurd h natCast_one_ne_empty
    · rwa [relabelOne_injective hX1 hw' hw h] at hz
  · intro hz
    exact ⟨w, hw, .inr rfl, hz⟩

/-- The nodes of `P ⊗ X` -/
theorem mem_tensorProdTwoAOneNds_iff' : y ∈ tensorProdTwoAOneNds P X ↔
    ∃ q ∈ ndOf P, q ∉ rtOf P ∧
      ∃ h ∈ aotciEmbSet ((1 : ℕ) : M) (aoc (uc q)) (tensorProdTwoAOneTgt X),
        y = !(dctUZero, !(q, h)) := by
  have hres : IsSetRestrictedTo (fun x ↦ !(dctUZero, x)) (tensorProdTwoAOneLbls P X) :=
    isSetRestrictedTo_of_definable _
  rw [tensorProdTwoAOneNds, mem_ran_toSetRestrictedTo_iff hres]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨q, hq, hqr, h, hh, rfl⟩ := mem_tensorProdTwoAOneLbls_iff.mp hx
    exact ⟨q, hq, hqr, h, hh, rfl⟩
  · rintro ⟨q, hq, hqr, h, hh, rfl⟩
    exact ⟨_, mem_tensorProdTwoAOneLbls_iff.mpr ⟨q, hq, hqr, h, hh, rfl⟩, rfl⟩

theorem nodeQ_orderedPair (a q h : M) : nodeQ !(a, !(q, h)) = q := by
  simp [nodeQ, lbl_orderedPair, left_orderedPair]

theorem nodeU_orderedPair (a q h : M) : nodeU !(a, !(q, h)) = uc q := by
  simp [nodeU, lbl_orderedPair, left_orderedPair]

theorem nodeH_orderedPair (a q h : M) : nodeH !(a, !(q, h)) = h := by
  simp [nodeH, lbl_orderedPair, right_orderedPair]

/-- The images of the level-`1` nodes under an embedding into the target `X ⊗ Z` are relabeled
nodes of `X(1)` -/
theorem exists_relabelOne_eq {A h u : M} (hX : X ∈ aotci ((1 : ℕ) : M))
    (hh : h ∈ aotciEmbSet ((1 : ℕ) : M) A (tensorProdTwoAOneTgt X))
    (hu : u ∈ ndOf (A ﹫ ((1 : ℕ) : M))) :
    ∃ w ∈ ndOf (X ﹫ ((1 : ℕ) : M)), (h ﹫ ((1 : ℕ) : M)) ﹫ u = relabelOne trvAZero w := by
  have he := ((mem_aotciEmbSet_iff.mp hh).right.isOtciEmbedding (mem_succ_self _)).isEmbedding
  have hmem := he.isEmbedding_ts.isInjectionFromTo.isFunctionFromTo.val_mem hu
  change (h ﹫ ((1 : ℕ) : M)) ﹫ u ∈ ndOf (tensorProdTwoAOneTgt X ﹫ ((1 : ℕ) : M)) at hmem
  rw [tensorProdTwoAOneTgt_val_one,
    mem_ndOf_tensorProdOneAZero_iff (val_mem_otci_of_mem_aotci hX (mem_succ_self _))] at hmem
  obtain ⟨w, hw, hwe⟩ := hmem
  exact ⟨w, hw, hwe.symm⟩

section TpSigVal

variable {q h : M}

theorem uc_mem_stduoci_of_mem_otci_two {T q : M} (hT : T ∈ otci ((2 : ℕ) : M))
    (hq : q ∈ ndOf T) : uc q ∈ stduoci ((1 : ℕ) : M) :=
  ((otciCond_two hT).right.left q hq).left

omit [ModelsZF M] in
theorem isTpTwo_orderedPair (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) :
    IsTpTwo Q X !(dctUZero, !(q, h)) := hy

theorem tpSigDom_eq (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) :
    tpSigDom Q X !(dctUZero, !(q, h)) = dom (sig (uc q)) := by
  rw [tpSigDom, if_pos (isTpTwo_orderedPair hy), nodeU_orderedPair]

theorem dom_tpSig_eq (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) :
    dom (tpSig Q X !(dctUZero, !(q, h))) = dom (sig (uc q)) := by
  have hres : IsSetRestrictedTo (fun j ↦ tpSigEntry X !(dctUZero, !(q, h)) j)
      (tpSigDom Q X !(dctUZero, !(q, h))) := isSetRestrictedTo_of_definable _
  rw [tpSig, dom_toSetRestrictedTo hres, tpSigDom_eq hy]

theorem isFunction_tpSig (Q X y : M) : IsFunction (tpSig Q X y) := by
  have hres : IsSetRestrictedTo (fun j ↦ tpSigEntry X y j) (tpSigDom Q X y) :=
    isSetRestrictedTo_of_definable _
  exact isFunction_toSetRestrictedTo hres

/-- The entries of the signature of a node from `Q(2)` -/
theorem tpSig_val_eq (hQ : Q ∈ aotci ((2 : ℕ) : M))
    (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) X) (hi : i ∈ dom (sig (uc q))) :
    tpSig Q X !(dctUZero, !(q, h)) ﹫ i =
      !(((1 : ℕ) : M), tpOrig X ((1 : ℕ) : M) ((h ﹫ ((1 : ℕ) : M)) ﹫ sigdcn (uc q) i)) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  obtain ⟨q', hq', -, h', -, he⟩ := mem_tensorProdTwoAOneNds_iff'.mp hy
  rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at he
  obtain ⟨-, rfl, rfl⟩ := he
  have hres : IsSetRestrictedTo (fun j ↦ tpSigEntry X !(dctUZero, !(q, h)) j)
      (tpSigDom Q X !(dctUZero, !(q, h))) := isSetRestrictedTo_of_definable _
  rw [tpSig, val_toSetRestrictedTo hres (by rw [tpSigDom_eq hy]; exact hi), tpSigEntry,
    nodeU_orderedPair, nodeH_orderedPair, tpSigEntryAux,
    (siglvl_eq_one (uc_mem_stduoci_of_mem_otci_two hQ2 hq') hi).left]

/-- The signature of a node of `(Q ⊗ X')(1)` from `Q(2)` is the same in `X` -/
theorem tpSig_eq_of_isSubOne (hQ : Q ∈ aotci ((2 : ℕ) : M)) (hX : X ∈ aotci ((1 : ℕ) : M))
    (hX' : X' ∈ aotci ((1 : ℕ) : M)) (h0 : X ﹫ ∅ = X' ﹫ ∅)
    (hsub : IsSubOne (X' ﹫ ((1 : ℕ) : M)) (X ﹫ ((1 : ℕ) : M)))
    (hy : !(dctUZero, !(q, h)) ∈ tensorProdTwoAOneNds (Q ﹫ 2) X') :
    tpSig Q X' !(dctUZero, !(q, h)) = tpSig Q X !(dctUZero, !(q, h)) := by
  have hQ2 : Q ﹫ (2 : M) ∈ otci ((2 : ℕ) : M) := val_mem_otci_of_mem_aotci hQ (mem_succ_self _)
  have hyX := ((mem_tensorProdTwoAOneNds_iff_of_isSubOne hQ hX hX' h0 hsub).mp hy).left
  obtain ⟨q', hq', -, h', hh', he⟩ := mem_tensorProdTwoAOneNds_iff'.mp hy
  rw [orderedPair_eq_orderedPair_iff, orderedPair_eq_orderedPair_iff] at he
  obtain ⟨-, rfl, rfl⟩ := he
  have hqs := uc_mem_stduoci_of_mem_otci_two hQ2 hq'
  refine (isFunction_tpSig _ _ _).ext (isFunction_tpSig _ _ _)
    (by rw [dom_tpSig_eq hy, dom_tpSig_eq hyX]) fun i hi ↦ ?_
  rw [dom_tpSig_eq hy] at hi
  rw [tpSig_val_eq hQ hy hi, tpSig_val_eq hQ hyX hi]
  obtain ⟨w, hw, hwe⟩ := exists_relabelOne_eq hX' hh' (siglvl_eq_one hqs hi).right
  rw [hwe, tpOrig_one_relabelOne hX' hw, tpOrig_one_relabelOne hX (hsub.left hw)]

end TpSigVal

end NodesTwo

end Slot

end TensorProd

end FirstOrder.Language.MemStructure
