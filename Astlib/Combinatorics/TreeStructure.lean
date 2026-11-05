/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Axiom.ZF.Semantics
import Astlib.Basic.Ordinal.Add
import Astlib.Basic.Ordinal.Nat
import Astlib.Basic.Ordinal.Omega
/-!
# Tree structures

In models of `KP`:

* `TreeStructure M` is `M`, viewed as tree structures `(A, d, C)` coded by the sets
  `!(A, !(d, C))` (`TreeStructure.mk A d C`): the nodes `T.nd`, the depth function `T.dep` and the
  children function `T.chd`;
* `T.IsTreeStructure`: `d !: A → ω`, `C` is a function on `A` with `C ﹫ a ⊆ A`, children are
  one level deeper, and every node of positive depth is a child of a unique node;
* `T.rt`: the roots, the nodes of depth `∅`;
* `T.prt`: the parent function on `A \ T.rt`, `T.prt ﹫ b = a ↔ b ∈ C ﹫ a`;
* `T.sbl`: the sibling function on `A`, `C ﹫ (T.prt ﹫ a)` for `a ∉ T.rt` and `T.rt` for
  `a ∈ T.rt`;
* `T.sblptn`: the sibling partition `({T.rt} ∪ ran C) \ {∅}`;
* `T.IsEmbedding T' π`: `π` is an embedding of `T` into `T'`, an injection of the nodes
  preserving the depth and the parent relation, and `T.IsIsomorphism T' π`: `π` is a surjective
  embedding;
* `T.map π`: the image of `T` under `π`; `T.iprt a m`, the `m`-th iterated parent of `a`, and
  `T.anc a k`, the ancestor of `a` of depth `k`; `ofRt A`, the tree structure with the roots `A`;
* `T.sngIso T'`: the unique isomorphism of tree structures with a single node.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M]

/-- `d ﹫ a = ∅` is `Δ₀` -/
instance (d : M) : Class.DeltaZero (fun a : M ↦ d ﹫ a = ∅) Set.univ := by
  let φ : L.DeltaZeroBoundedFormula 2 := ((ᵣ1) ﹫ (ᵣ0)).isEq ∅
  have h : (fun ys : Fin 1 → M ↦ d ﹫ ys 0 = ∅) =
      φ.toBoundedFormula.multiclass.slice ![d] := by
    funext ys
    simp only [Fin.isValue, Multiclass.slice, BoundedFormula.multiclass, RudimentaryTerm.val,
      Nat.succ_eq_add_one, Nat.reduceAdd, RudimentaryTerm.realize_isEq,
      RudimentaryTerm.realize_substBoundRud, RudimentaryTerm.realize_val₀, Matrix.cons_val_zero,
      RudimentaryTerm.realize_basic, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      RudimentaryTerm.realize_empty, eq_iff_iff, φ]
    rfl
  have : Multiclass.DeltaZero (fun ys : Fin 1 → M ↦ d ﹫ ys 0 = ∅) Set.univ :=
    h ▸ inferInstance
  infer_instance

/-- `left p ∈ C ﹫ right p` is `Δ₀` -/
instance (C : M) : Class.DeltaZero (fun p : M ↦ left p ∈ C ﹫ right p) Set.univ := by
  let φ : L.DeltaZeroBoundedFormula 2 :=
    (ᵣ0).left.isMem ((ᵣ1) ﹫ (ᵣ0).right)
  have h : (fun ys : Fin 1 → M ↦ left (ys 0) ∈ C ﹫ right (ys 0)) =
      φ.toBoundedFormula.multiclass.slice ![C] := by
    funext ys
    simp only [Fin.isValue, Multiclass.slice, BoundedFormula.multiclass, RudimentaryTerm.left,
      RudimentaryTerm.val, RudimentaryTerm.right, Nat.succ_eq_add_one, Nat.reduceAdd,
      RudimentaryTerm.realize_isMem, RudimentaryTerm.realize_substBoundRud,
      RudimentaryTerm.realize_val₀, Matrix.cons_val_zero, RudimentaryTerm.realize_basic,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, RudimentaryTerm.realize_right₀,
      RudimentaryTerm.realize_left₀, eq_iff_iff, φ]
    rfl
  have : Multiclass.DeltaZero (fun ys : Fin 1 → M ↦ left (ys 0) ∈ C ﹫ right (ys 0))
      Set.univ :=
    h ▸ inferInstance
  infer_instance

/-- A tree structure `(A, d, C)`, coded as the set `!(A, !(d, C))`: the nodes `A`, the depth
function `d` and the children function `C` -/
def TreeStructure (M : Type*) := M

namespace TreeStructure

/-- The tree structure `(A, d, C)` -/
noncomputable def mk (A d C : M) : TreeStructure M := (!(A, !(d, C)) : M)

variable (T : TreeStructure M)

/-- The set coding a tree structure -/
def toM : M := T

/-- The tree structure coded by a set -/
def ofM (x : M) : TreeStructure M := x

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] in
@[simp]
theorem toM_ofM (x : M) : (ofM x).toM = x := rfl

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] in
@[simp]
theorem ofM_toM : ofM T.toM = T := rfl

/-- The set of nodes -/
noncomputable def nd : M := left T.toM

/-- The depth function -/
noncomputable def dep : M := left (right T.toM)

/-- The children function -/
noncomputable def chd : M := right (right T.toM)

section Mk

variable (A d C : M)

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
@[simp]
theorem toM_mk : (mk A d C).toM = !(A, !(d, C)) := rfl

@[simp]
theorem nd_mk : (mk A d C).nd = A := by
  simp [nd]

@[simp]
theorem dep_mk : (mk A d C).dep = d := by
  simp [dep]

@[simp]
theorem chd_mk : (mk A d C).chd = C := by
  simp [chd]

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
theorem isOrderedPair_mk : IsOrderedPair (mk A d C).toM := ⟨A, !(d, C), rfl⟩

theorem isOrderedPair_right_mk : IsOrderedPair (right (mk A d C).toM) := by
  rw [toM_mk, right_orderedPair]
  exact ⟨d, C, rfl⟩

theorem mk_eq_mk_iff {A' d' C' : M} : mk A d C = mk A' d' C' ↔ A = A' ∧ d = d' ∧ C = C' := by
  change (mk A d C).toM = (mk A' d' C').toM ↔ _
  simp

end Mk

/-- `T = (A, d, C)` is a tree structure -/
structure IsTreeStructure : Prop where
  isOrderedPair : IsOrderedPair T.toM
  isOrderedPair_right : IsOrderedPair (right T.toM)
  dep_fromTo : T.dep !: T.nd → (ω : M)
  isFunction_chd : IsFunction T.chd
  dom_chd : dom T.chd = T.nd
  chd_subset : ∀ a ∈ T.nd, T.chd ﹫ a ⊆ T.nd
  dep_of_mem_chd : ∀ a ∈ T.nd, ∀ b ∈ T.chd ﹫ a, T.dep ﹫ b = succ (T.dep ﹫ a)
  existsUnique_prt : ∀ b ∈ T.nd, ∅ <ₒ T.dep ﹫ b → ∃! a, b ∈ T.chd ﹫ a

/-- A tree structure is the triple of its components -/
theorem IsTreeStructure.eq_mk {T : TreeStructure M} (hT : T.IsTreeStructure) :
    T = TreeStructure.mk T.nd T.dep T.chd := by
  obtain ⟨A, X, hAX⟩ := hT.isOrderedPair
  have hX := hT.isOrderedPair_right
  rw [hAX, right_orderedPair] at hX
  obtain ⟨d, C, rfl⟩ := hX
  change T.toM = (TreeStructure.mk T.nd T.dep T.chd).toM
  simp [nd, dep, chd, hAX]

/-- The empty tree structure `(∅, ∅, ∅)` -/
noncomputable instance : EmptyCollection (TreeStructure M) := ⟨mk ∅ ∅ ∅⟩

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
theorem empty_eq_mk : (∅ : TreeStructure M) = mk ∅ ∅ ∅ := rfl

@[simp]
theorem nd_empty : (∅ : TreeStructure M).nd = ∅ := nd_mk ∅ ∅ ∅

@[simp]
theorem dep_empty : (∅ : TreeStructure M).dep = ∅ := dep_mk ∅ ∅ ∅

@[simp]
theorem chd_empty : (∅ : TreeStructure M).chd = ∅ := chd_mk ∅ ∅ ∅

/-- The empty tree structure is a tree structure -/
theorem isTreeStructure_empty : (∅ : TreeStructure M).IsTreeStructure where
  isOrderedPair := isOrderedPair_mk ∅ ∅ ∅
  isOrderedPair_right := isOrderedPair_right_mk ∅ ∅ ∅
  dep_fromTo := by
    rw [dep_empty, nd_empty]
    exact isFunctionFromTo_empty ω
  isFunction_chd := by
    rw [chd_empty]
    exact isFunction_empty
  dom_chd := by simp
  chd_subset := by simp
  dep_of_mem_chd := by simp
  existsUnique_prt := by simp

/-- The roots: the nodes of depth `∅` -/
noncomputable def rt : M := T.nd ∩₀ fun a ↦ T.dep ﹫ a = ∅

/-- The parent function on `T.nd \ T.rt`: `T.prt ﹫ b = a ↔ b ∈ T.chd ﹫ a` -/
noncomputable def prt : M := (T.nd ×ˢ T.nd) ∩₀ fun p ↦ left p ∈ T.chd ﹫ right p

/-- The sibling function on `T.nd`: the children of the parent of a non-root, and the roots for
a root -/
noncomputable def sbl : M := T.chd !∘ T.prt ∪ constFun T.rt T.rt

/-- The sibling partition `({T.rt} ∪ ran T.chd) \ {∅}` -/
noncomputable def sblptn : M := ({T.rt} ∪ ran T.chd) \ {∅}

/-- `T` with a new root `b`: `(A ∪ {b}, d_ins(b, ∅), C_ins(b, ∅))` -/
noncomputable def irt (b : M) : TreeStructure M :=
  mk (insert b T.nd) (update T.dep b ∅) (update T.chd b ∅)

/-- `T` with new children `B` of `a`:
`(A ∪ B, d ∪ (B × {d(a) + 1}), C_mVal(a, C(a) ∪ B) ∪ (B × {∅}))` -/
noncomputable def ichd (a B : M) : TreeStructure M :=
  mk (T.nd ∪ B) (T.dep ∪ constFun B (succ (T.dep ﹫ a)))
    (update T.chd a (T.chd ﹫ a ∪ B) ∪ constFun B ∅)

/-- `T` with a new child `b` of `a`: `T.ichd a {b}` -/
noncomputable def ionechd (a b : M) : TreeStructure M := T.ichd a {b}

noncomputable instance (a : M) : Decidable (a ∈ T.rt) := Classical.propDecidable _

/-- `T` with a new sibling `b` of `a`: `T.irt b` if `a` is a root, and otherwise
`(A ∪ {b}, d_ins(b, d(a)), C_iToVal(T.prt(a), b)_ins(b, ∅))` -/
noncomputable def isbl (a b : M) : TreeStructure M :=
  if a ∈ T.rt then T.irt b
  else mk (insert b T.nd) (update T.dep b (T.dep ﹫ a))
    (update (insertVal T.chd (T.prt ﹫ a) b) b ∅)

variable {T} {a b c e p s B : M}

@[simp]
theorem nd_irt : (T.irt b).nd = insert b T.nd := nd_mk _ _ _

@[simp]
theorem dep_irt : (T.irt b).dep = update T.dep b ∅ := dep_mk _ _ _

@[simp]
theorem chd_irt : (T.irt b).chd = update T.chd b ∅ := chd_mk _ _ _

@[simp]
theorem nd_ichd : (T.ichd a B).nd = T.nd ∪ B := nd_mk _ _ _

@[simp]
theorem dep_ichd : (T.ichd a B).dep = T.dep ∪ constFun B (succ (T.dep ﹫ a)) :=
  dep_mk _ _ _

@[simp]
theorem chd_ichd : (T.ichd a B).chd = update T.chd a (T.chd ﹫ a ∪ B) ∪ constFun B ∅ :=
  chd_mk _ _ _

omit [ModelsKP M] in
theorem isbl_of_mem_rt (ha : a ∈ T.rt) : T.isbl a b = T.irt b := if_pos ha

omit [ModelsKP M] in
theorem isbl_of_not_mem_rt (ha : a ∉ T.rt) :
    T.isbl a b =
      mk (insert b T.nd) (update T.dep b (T.dep ﹫ a))
        (update (insertVal T.chd (T.prt ﹫ a) b) b ∅) :=
  if_neg ha

theorem singleton_inter_eq_empty (hb : b ∉ T.nd) : ({b} : M) ∩ T.nd = ∅ := by
  rw [empty_iff]
  grind

theorem mem_rt_iff : a ∈ T.rt ↔ a ∈ T.nd ∧ T.dep ﹫ a = ∅ := by
  simp [rt]

theorem mem_prt_iff : p ∈ T.prt ↔ p ∈ T.nd ×ˢ T.nd ∧ left p ∈ T.chd ﹫ right p := by
  simp [prt]

theorem rel_prt_iff : b [T.prt] a ↔ (b ∈ T.nd ∧ a ∈ T.nd) ∧ b ∈ T.chd ﹫ a := by
  simp [mem_prt_iff]

theorem mem_sblptn_iff : s ∈ T.sblptn ↔ (s = T.rt ∨ s ∈ ran T.chd) ∧ s ≠ ∅ := by
  simp [sblptn]

/-- The members of the sibling partition are nonempty -/
theorem ne_empty_of_mem_sblptn {X : M} (hX : X ∈ T.sblptn) : X ≠ ∅ :=
  (mem_sblptn_iff.mp hX).right

@[simp]
theorem rt_empty : (∅ : TreeStructure M).rt = ∅ := by
  ext a
  simp [mem_rt_iff]

/-- The empty tree structure has an empty sibling partition -/
@[simp]
theorem sblptn_empty : (∅ : TreeStructure M).sblptn = ∅ := by
  ext s
  simp [mem_sblptn_iff]

theorem rt_mem_sblptn (hrt : T.rt ≠ ∅) : T.rt ∈ T.sblptn := by
  rw [mem_sblptn_iff]
  exact ⟨Or.inl rfl, hrt⟩

theorem ran_prt_subset : ran T.prt ⊆ T.nd := by
  intro a ha
  rw [mem_ran_iff] at ha
  grind [rel_prt_iff]

/-- `IsTreeStructure` with all quantifiers bounded -/
theorem isTreeStructure_iff [HasOmega M] :
    T.IsTreeStructure ↔ IsOrderedPair T.toM ∧ IsOrderedPair (right T.toM) ∧
      IsFunction T.dep ∧ dom T.dep = T.nd ∧ (∀ a ∈ T.nd, IsNat (T.dep ﹫ a)) ∧
      IsFunction T.chd ∧ dom T.chd = T.nd ∧ (∀ a ∈ T.nd, ∀ b ∈ T.chd ﹫ a, b ∈ T.nd) ∧
      (∀ a ∈ T.nd, ∀ b ∈ T.chd ﹫ a, T.dep ﹫ b = succ (T.dep ﹫ a)) ∧
      ∀ b ∈ T.nd, ∅ ∈ T.dep ﹫ b →
        ∃ a ∈ T.nd, b ∈ T.chd ﹫ a ∧ ∀ a' ∈ T.nd, b ∈ T.chd ﹫ a' → a' = a := by
  constructor
  · intro hT
    refine ⟨hT.isOrderedPair, hT.isOrderedPair_right, hT.dep_fromTo.isFunction,
      hT.dep_fromTo.dom_eq, fun a ha ↦ ?_, hT.isFunction_chd, hT.dom_chd,
      fun a ha b hb ↦ hT.chd_subset a ha hb, hT.dep_of_mem_chd, fun b hb h0 ↦ ?_⟩
    · rw [← mem_omega_iff]
      exact hT.dep_fromTo.val_mem ha
    have hnat : IsNat (T.dep ﹫ b) := by
      rw [← mem_omega_iff]
      exact hT.dep_fromTo.val_mem hb
    obtain ⟨a, hab, huniq⟩ := hT.existsUnique_prt b hb ⟨ordinal_empty, hnat.ordinal, h0⟩
    refine ⟨a, ?_, hab, fun a' _ h ↦ huniq a' h⟩
    rw [← hT.dom_chd]
    exact mem_dom_of_mem_val hab
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    refine ⟨h1, h2, isFunctionFromTo_of_val h3 h4 fun a ha ↦ ?_, h6, h7,
      fun a ha b hb ↦ h8 a ha b hb, h9, fun b hb hpos ↦ ?_⟩
    · rw [mem_omega_iff]
      exact h5 a ha
    obtain ⟨a, -, hab, huniq⟩ := h10 b hb hpos.mem
    refine ⟨a, hab, fun a' ha' ↦ huniq a' ?_ ha'⟩
    rw [← h7]
    exact mem_dom_of_mem_val ha'

namespace IsTreeStructure

variable (hT : T.IsTreeStructure)
include hT

theorem dep_mem_omega (ha : a ∈ T.nd) : T.dep ﹫ a ∈ (ω : M) :=
  hT.dep_fromTo.val_mem ha

/-- The parent of a child of `a` is `a` -/
theorem rel_prt_iff_mem_chd (ha : a ∈ T.nd) : b [T.prt] a ↔ b ∈ T.chd ﹫ a := by
  grind [rel_prt_iff, hT.chd_subset]

/-- A node with a child is a node -/
theorem mem_nd_of_mem_chd_val (hb : b ∈ T.chd ﹫ a) : a ∈ T.nd := by
  rw [← hT.dom_chd]
  exact mem_dom_of_mem_val hb

/-- The members of the sibling partition are sets of nodes -/
theorem subset_nd_of_mem_sblptn {X : M} (hX : X ∈ T.sblptn) : X ⊆ T.nd := by
  rw [mem_sblptn_iff] at hX
  rcases hX.left with rfl | hX
  · intro a ha
    rw [mem_rt_iff] at ha
    exact ha.left
  rw [hT.isFunction_chd.mem_ran_iff, hT.dom_chd] at hX
  obtain ⟨p, hp, rfl⟩ := hX
  exact hT.chd_subset p hp

theorem dep_val_mem_ran (ha : a ∈ T.nd) : T.dep ﹫ a ∈ ran T.dep := by
  rw [hT.dep_fromTo.isFunction.mem_ran_iff, hT.dep_fromTo.dom_eq]
  exact ⟨a, ha, rfl⟩

/-- A tree structure without nodes is the empty tree structure -/
theorem eq_empty_of_nd_eq_empty (hA : T.nd = ∅) : T = ∅ := by
  have hdep : T.dep !: ∅ → (ω : M) := hA ▸ hT.dep_fromTo
  have hchd := isFunctionFromTo_dom_ran hT.isFunction_chd
  rw [hT.dom_chd, hA] at hchd
  rw [hT.eq_mk, hA, hdep.eq_empty_of_dom_empty, hchd.eq_empty_of_dom_empty]
  rfl

/-- A nonempty tree structure has a node -/
theorem nd_ne_empty (hne : T ≠ ∅) : T.nd ≠ ∅ :=
  fun hA ↦ hne (hT.eq_empty_of_nd_eq_empty hA)

theorem dep_irt_val_self : (T.irt b).dep ﹫ b = ∅ := by
  rw [dep_irt]
  exact val_update_self hT.dep_fromTo.isFunction b ∅

theorem dep_irt_val_of_mem (hb : b ∉ T.nd) (ha : a ∈ T.nd) :
    (T.irt b).dep ﹫ a = T.dep ﹫ a := by
  rw [dep_irt]
  exact val_update_of_ne hT.dep_fromTo.isFunction ∅ (by rwa [hT.dep_fromTo.dom_eq]) (by grind)

theorem chd_irt_val_self : (T.irt b).chd ﹫ b = ∅ := by
  rw [chd_irt]
  exact val_update_self hT.isFunction_chd b ∅

theorem chd_irt_val_of_mem (hb : b ∉ T.nd) (ha : a ∈ T.nd) :
    (T.irt b).chd ﹫ a = T.chd ﹫ a := by
  rw [chd_irt]
  exact val_update_of_ne hT.isFunction_chd ∅ (by rwa [hT.dom_chd]) (by grind)

theorem dom_chd_irt : dom (T.irt b).chd = insert b T.nd := by
  simp [hT.dom_chd]

omit hT in
theorem not_mem_nd_of_mem_new (hB : B ∩ T.nd = ∅) (hc : c ∈ B) : c ∉ T.nd := by
  intro hcA
  have hmem : c ∈ B ∩ T.nd := by grind
  simp [hB] at hmem

theorem disjoint_dep_ichd (hB : B ∩ T.nd = ∅) (x : M) :
    ∀ z ∈ dom T.dep, z ∉ dom (constFun B x) := by
  rw [hT.dep_fromTo.dom_eq, dom_constFun]
  exact fun z hz hzB ↦ not_mem_nd_of_mem_new hB hzB hz

theorem isFunction_dep_ichd (hB : B ∩ T.nd = ∅) : IsFunction (T.ichd a B).dep := by
  rw [dep_ichd]
  exact hT.dep_fromTo.isFunction.union_of_disjoint (isFunction_constFun B (succ (T.dep ﹫ a)))
    (hT.disjoint_dep_ichd hB (succ (T.dep ﹫ a)))

theorem dom_dep_ichd : dom (T.ichd a B).dep = T.nd ∪ B := by
  simp [dom_union, hT.dep_fromTo.dom_eq]

theorem dep_ichd_val_of_mem_nd (hB : B ∩ T.nd = ∅) (hc : c ∈ T.nd) :
    (T.ichd a B).dep ﹫ c = T.dep ﹫ c := by
  rw [dep_ichd]
  exact val_union_left hT.dep_fromTo.isFunction (isFunction_constFun B (succ (T.dep ﹫ a)))
    (hT.disjoint_dep_ichd hB (succ (T.dep ﹫ a))) (by rwa [hT.dep_fromTo.dom_eq])

theorem dep_ichd_val_of_mem_new (hB : B ∩ T.nd = ∅) (hc : c ∈ B) :
    (T.ichd a B).dep ﹫ c = succ (T.dep ﹫ a) := by
  rw [dep_ichd, val_union_right hT.dep_fromTo.isFunction
    (isFunction_constFun B (succ (T.dep ﹫ a))) (hT.disjoint_dep_ichd hB (succ (T.dep ﹫ a)))
    (by rwa [dom_constFun]), val_constFun hc]

theorem disjoint_chd_ichd (ha : a ∈ T.nd) (hB : B ∩ T.nd = ∅) :
    ∀ z ∈ dom (update T.chd a (T.chd ﹫ a ∪ B)), z ∉ dom (constFun B (∅ : M)) := by
  rw [dom_update, hT.dom_chd, dom_constFun]
  intro z hz hzB
  rw [mem_insert_iff] at hz
  rcases hz with rfl | hz
  · exact not_mem_nd_of_mem_new hB hzB ha
  · exact not_mem_nd_of_mem_new hB hzB hz

theorem isFunction_chd_ichd (ha : a ∈ T.nd) (hB : B ∩ T.nd = ∅) :
    IsFunction (T.ichd a B).chd := by
  rw [chd_ichd]
  exact (hT.isFunction_chd.update a (T.chd ﹫ a ∪ B)).union_of_disjoint (isFunction_constFun B ∅)
    (hT.disjoint_chd_ichd ha hB)

theorem dom_chd_ichd (ha : a ∈ T.nd) : dom (T.ichd a B).chd = T.nd ∪ B := by
  simp [dom_union, hT.dom_chd, insert_eq_self ha]

theorem chd_ichd_val_self (ha : a ∈ T.nd) (hB : B ∩ T.nd = ∅) :
    (T.ichd a B).chd ﹫ a = T.chd ﹫ a ∪ B := by
  rw [chd_ichd, val_union_left (hT.isFunction_chd.update a (T.chd ﹫ a ∪ B))
    (isFunction_constFun B ∅) (hT.disjoint_chd_ichd ha hB) (by simp),
    val_update_self hT.isFunction_chd]

theorem chd_ichd_val_of_ne (ha : a ∈ T.nd) (hB : B ∩ T.nd = ∅) (hc : c ∈ T.nd)
    (hca : c ≠ a) : (T.ichd a B).chd ﹫ c = T.chd ﹫ c := by
  rw [chd_ichd, val_union_left (hT.isFunction_chd.update a (T.chd ﹫ a ∪ B))
    (isFunction_constFun B ∅) (hT.disjoint_chd_ichd ha hB) (by simp [hT.dom_chd, hc]),
    val_update_of_ne hT.isFunction_chd (T.chd ﹫ a ∪ B) (by rwa [hT.dom_chd]) hca]

theorem chd_ichd_val_of_mem_new (ha : a ∈ T.nd) (hB : B ∩ T.nd = ∅) (hc : c ∈ B) :
    (T.ichd a B).chd ﹫ c = ∅ := by
  rw [chd_ichd, val_union_right (hT.isFunction_chd.update a (T.chd ﹫ a ∪ B))
    (isFunction_constFun B ∅) (hT.disjoint_chd_ichd ha hB) (by rwa [dom_constFun]),
    val_constFun hc]

/-- The children in `T.ichd a B`: the old children, and the new children `B` of `a` -/
theorem mem_chd_ichd_val_iff (ha : a ∈ T.nd) (hB : B ∩ T.nd = ∅) :
    e ∈ (T.ichd a B).chd ﹫ c ↔
      (c ∈ T.nd ∧ e ∈ T.chd ﹫ c) ∨ (c = a ∧ e ∈ B) := by
  by_cases hcB : c ∈ B
  · have hcA := not_mem_nd_of_mem_new hB hcB
    rw [hT.chd_ichd_val_of_mem_new ha hB hcB]
    grind
  by_cases hcA : c ∈ T.nd
  swap
  · constructor
    · intro he
      have hdom := mem_dom_of_mem_val he
      rw [hT.dom_chd_ichd ha] at hdom
      grind
    · grind
  by_cases hca : c = a
  · subst hca
    rw [hT.chd_ichd_val_self hcA hB]
    grind
  rw [hT.chd_ichd_val_of_ne ha hB hcA hca]
  grind


variable [HasOmega M]

/-- A node has positive depth iff it is not a root -/
theorem empty_olt_dep_iff (ha : a ∈ T.nd) : ∅ <ₒ T.dep ﹫ a ↔ a ∉ T.rt := by
  rw [mem_rt_iff]
  rcases mem_omega_cases (hT.dep_mem_omega ha) with h | ⟨n, hn, h⟩ <;> grind

/-- A child has positive depth -/
theorem empty_olt_dep_of_mem_chd (ha : a ∈ T.nd) (hb : b ∈ T.chd ﹫ a) :
    ∅ <ₒ T.dep ﹫ b := by
  rw [hT.dep_of_mem_chd a ha b hb]
  grind [hT.dep_mem_omega ha]

/-- A member of a set of children is not a root -/
theorem not_mem_rt_of_mem_ran_chd {X : M} (hX : X ∈ ran T.chd) (ha : a ∈ X) : a ∉ T.rt := by
  rw [hT.isFunction_chd.mem_ran_iff, hT.dom_chd] at hX
  obtain ⟨p, hp, rfl⟩ := hX
  rw [← hT.empty_olt_dep_iff (hT.chd_subset p hp ha)]
  exact hT.empty_olt_dep_of_mem_chd hp ha

theorem isFunction_prt : IsFunction T.prt := by
  refine ⟨(isRelation_sprod T.nd T.nd).subset fun p hp ↦ (mem_prt_iff.mp hp).left, ?_⟩
  intro b a₁ a₂ h₁ h₂
  rw [rel_prt_iff] at h₁ h₂
  have hpos := hT.empty_olt_dep_of_mem_chd h₁.left.right h₁.right
  exact (hT.existsUnique_prt b h₁.left.left hpos).unique h₁.right h₂.right

theorem dom_prt : dom T.prt = T.nd \ T.rt := by
  ext b
  rw [mem_dom_iff, mem_sdiff_iff]
  constructor
  · rintro ⟨a, hab⟩
    rw [rel_prt_iff] at hab
    rw [← hT.empty_olt_dep_iff hab.left.left]
    exact ⟨hab.left.left, hT.empty_olt_dep_of_mem_chd hab.left.right hab.right⟩
  · rintro ⟨hb, hbr⟩
    rw [← hT.empty_olt_dep_iff hb] at hbr
    obtain ⟨a, hba, -⟩ := hT.existsUnique_prt b hb hbr
    exact ⟨a, (hT.rel_prt_iff_mem_chd (hT.mem_nd_of_mem_chd_val hba)).mpr hba⟩

theorem mem_chd_prt_val (hb : b ∈ T.nd \ T.rt) : b ∈ T.chd ﹫ (T.prt ﹫ b) := by
  rw [← hT.dom_prt] at hb
  grind [rel_val hT.isFunction_prt hb, rel_prt_iff]

theorem prt_val_mem_nd (hb : b ∈ T.nd \ T.rt) : T.prt ﹫ b ∈ T.nd :=
  hT.mem_nd_of_mem_chd_val (hT.mem_chd_prt_val hb)

theorem prt_val_eq_iff (hb : b ∈ T.nd \ T.rt) (ha : a ∈ T.nd) :
    T.prt ﹫ b = a ↔ b ∈ T.chd ﹫ a := by
  rw [← hT.rel_prt_iff_mem_chd ha, hT.isFunction_prt.rel_iff_val_eq (by rwa [hT.dom_prt])]

theorem dom_chd_comp_prt : dom (T.chd !∘ T.prt) = T.nd \ T.rt := by
  rw [dom_comp hT.isFunction_chd (by rw [hT.dom_chd]; exact ran_prt_subset), hT.dom_prt]

theorem isFunction_sbl : IsFunction T.sbl := by
  refine (hT.isFunction_chd.comp hT.isFunction_prt).union_of_disjoint
    (isFunction_constFun T.rt T.rt) ?_
  grind [hT.dom_chd_comp_prt]

theorem dom_sbl : dom T.sbl = T.nd := by
  rw [sbl, dom_union, hT.dom_chd_comp_prt, dom_constFun]
  ext a
  grind [mem_rt_iff]

theorem sbl_val_of_mem_rt (ha : a ∈ T.rt) : T.sbl ﹫ a = T.rt := by
  rw [sbl, val_union_right (hT.isFunction_chd.comp hT.isFunction_prt)
    (isFunction_constFun T.rt T.rt) (by grind [hT.dom_chd_comp_prt]) (by rwa [dom_constFun]),
    val_constFun ha]

theorem sbl_val_of_not_mem_rt (ha : a ∈ T.nd \ T.rt) : T.sbl ﹫ a = T.chd ﹫ (T.prt ﹫ a) := by
  rw [sbl, val_union_left (hT.isFunction_chd.comp hT.isFunction_prt)
    (isFunction_constFun T.rt T.rt) (by grind [hT.dom_chd_comp_prt]) (by rwa [hT.dom_chd_comp_prt]),
    comp_val hT.isFunction_chd hT.isFunction_prt (by rwa [hT.dom_chd_comp_prt])]

/-- A node is its own sibling -/
theorem mem_sbl_val_self (ha : a ∈ T.nd) : a ∈ T.sbl ﹫ a := by
  by_cases hrt : a ∈ T.rt
  · rwa [hT.sbl_val_of_mem_rt hrt]
  have hb : a ∈ T.nd \ T.rt := by grind
  rw [hT.sbl_val_of_not_mem_rt hb]
  exact hT.mem_chd_prt_val hb

/-- The siblings of a node form a member of the sibling partition -/
theorem sbl_val_mem_sblptn (ha : a ∈ T.nd) : T.sbl ﹫ a ∈ T.sblptn := by
  rw [mem_sblptn_iff, ne_empty_iff]
  refine ⟨?_, ⟨a, hT.mem_sbl_val_self ha⟩⟩
  by_cases hrt : a ∈ T.rt
  · left
    exact hT.sbl_val_of_mem_rt hrt
  right
  have hb : a ∈ T.nd \ T.rt := by grind
  have hprt := hT.prt_val_mem_nd hb
  rw [hT.sbl_val_of_not_mem_rt hb, hT.isFunction_chd.mem_ran_iff, hT.dom_chd]
  exact ⟨T.prt ﹫ a, hprt, rfl⟩

/-- The siblings of a member of a member `X` of the sibling partition are `X` -/
theorem sbl_val_of_mem_sblptn {X : M} (hX : X ∈ T.sblptn) (ha : a ∈ X) : T.sbl ﹫ a = X := by
  rcases (mem_sblptn_iff.mp hX).left with rfl | hXran
  · exact hT.sbl_val_of_mem_rt ha
  have hart := hT.not_mem_rt_of_mem_ran_chd hXran ha
  rw [hT.isFunction_chd.mem_ran_iff, hT.dom_chd] at hXran
  obtain ⟨p, hp, rfl⟩ := hXran
  have hb : a ∈ T.nd \ T.rt := by grind [hT.chd_subset p hp ha]
  rw [hT.sbl_val_of_not_mem_rt hb]
  congr 1
  rwa [hT.prt_val_eq_iff hb hp]

/-- Two nodes are siblings if and only if one lies in the sibling set of the other -/
theorem sbl_val_eq_iff_mem (ha : a ∈ T.nd) (hb : b ∈ T.nd) :
    T.sbl ﹫ a = T.sbl ﹫ b ↔ b ∈ T.sbl ﹫ a := by
  refine ⟨fun h ↦ ?_, fun h ↦ (hT.sbl_val_of_mem_sblptn (hT.sbl_val_mem_sblptn ha) h).symm⟩
  rw [h]
  exact hT.mem_sbl_val_self hb

/-- Every node lies in a unique member of the sibling partition -/
theorem existsUnique_mem_sblptn (ha : a ∈ T.nd) : ∃! X ∈ T.sblptn, a ∈ X := by
  refine ⟨T.sbl ﹫ a, ⟨hT.sbl_val_mem_sblptn ha, hT.mem_sbl_val_self ha⟩, ?_⟩
  rintro X ⟨hX, haX⟩
  exact (hT.sbl_val_of_mem_sblptn hX haX).symm

/-- A nonempty tree structure has a root: a node of `∈`-minimal depth -/
theorem rt_ne_empty (hne : T ≠ ∅) : T.rt ≠ ∅ := by
  have hnd := hT.nd_ne_empty hne
  rw [ne_empty_iff] at hnd
  obtain ⟨a, ha⟩ := hnd
  have hran : ran T.dep ≠ ∅ := by
    rw [ne_empty_iff]
    exact ⟨T.dep ﹫ a, hT.dep_val_mem_ran ha⟩
  have hmin := memMin_mem hran
  rw [hT.dep_fromTo.isFunction.mem_ran_iff, hT.dep_fromTo.dom_eq] at hmin
  obtain ⟨b, hb, hbmin⟩ := hmin
  rw [ne_empty_iff]
  refine ⟨b, ?_⟩
  by_contra hbrt
  have hb' : b ∈ T.nd \ T.rt := by grind
  have hchd := hT.mem_chd_prt_val hb'
  have hprt := hT.prt_val_mem_nd hb'
  -- the parent of `b` has smaller depth
  have hlt : T.dep ﹫ (T.prt ﹫ b) ∈ memMin (ran T.dep) := by
    rw [← hbmin, hT.dep_of_mem_chd (T.prt ﹫ b) hprt b hchd]
    exact mem_succ_self (T.dep ﹫ (T.prt ﹫ b))
  exact notMem_memMin (hT.dep_val_mem_ran hprt) hlt

/-- Inserting a new root `b ∉ T.nd` into a tree structure gives a tree structure -/
theorem irt (hb : b ∉ T.nd) : (T.irt b).IsTreeStructure where
  isOrderedPair := isOrderedPair_mk _ _ _
  isOrderedPair_right := isOrderedPair_right_mk _ _ _
  dep_fromTo := by
    refine isFunctionFromTo_of_val
      (by rw [dep_irt]; exact hT.dep_fromTo.isFunction.update b ∅) ?_ fun a ha ↦ ?_
    · simp [hT.dep_fromTo.dom_eq]
    rw [nd_irt, mem_insert_iff] at ha
    rcases ha with rfl | ha
    · rw [hT.dep_irt_val_self]
      exact empty_mem_omega
    rw [hT.dep_irt_val_of_mem hb ha]
    exact hT.dep_mem_omega ha
  isFunction_chd := by
    rw [chd_irt]
    exact hT.isFunction_chd.update b ∅
  dom_chd := hT.dom_chd_irt.trans nd_irt.symm
  chd_subset := by
    intro a ha
    rw [nd_irt, mem_insert_iff] at ha
    rcases ha with rfl | ha
    · rw [hT.chd_irt_val_self]
      grind
    rw [hT.chd_irt_val_of_mem hb ha, nd_irt]
    grind [hT.chd_subset a ha]
  dep_of_mem_chd := by
    intro a ha c hc
    rw [nd_irt, mem_insert_iff] at ha
    rcases ha with rfl | ha
    · rw [hT.chd_irt_val_self] at hc
      simp at hc
    rw [hT.chd_irt_val_of_mem hb ha] at hc
    have hcA := hT.chd_subset a ha hc
    rw [hT.dep_irt_val_of_mem hb ha, hT.dep_irt_val_of_mem hb hcA]
    exact hT.dep_of_mem_chd a ha c hc
  existsUnique_prt := by
    intro c hc hpos
    rw [nd_irt, mem_insert_iff] at hc
    rcases hc with rfl | hc
    · rw [hT.dep_irt_val_self] at hpos
      simp at hpos
    rw [hT.dep_irt_val_of_mem hb hc] at hpos
    obtain ⟨a, hca, huniq⟩ := hT.existsUnique_prt c hc hpos
    have ha := hT.mem_nd_of_mem_chd_val hca
    refine ⟨a, ?_, fun a' hca' ↦ ?_⟩
    · dsimp only
      rwa [hT.chd_irt_val_of_mem hb ha]
    dsimp only at hca'
    have ha' : a' ∈ insert b T.nd := by
      rw [← hT.dom_chd_irt]
      exact mem_dom_of_mem_val hca'
    rw [mem_insert_iff] at ha'
    rcases ha' with rfl | ha'
    · rw [hT.chd_irt_val_self] at hca'
      simp at hca'
    rw [hT.chd_irt_val_of_mem hb ha'] at hca'
    exact huniq a' hca'

omit [HasOmega M] in
/-- The roots of `T.irt b` are the old roots and `b` -/
theorem rt_irt (hb : b ∉ T.nd) : (T.irt b).rt = insert b T.rt := by
  ext a
  rw [mem_rt_iff, nd_irt, mem_insert_iff, mem_insert_iff, mem_rt_iff]
  constructor
  · rintro ⟨rfl | ha, hd⟩
    · left
      rfl
    right
    rw [hT.dep_irt_val_of_mem hb ha] at hd
    exact ⟨ha, hd⟩
  · rintro (rfl | ⟨ha, hd⟩)
    · exact ⟨Or.inl rfl, hT.dep_irt_val_self⟩
    rw [hT.dep_irt_val_of_mem hb ha]
    exact ⟨Or.inr ha, hd⟩

/-- The sibling partition of `T.irt b`: the old roots together with `b`, and the old sets of
siblings other than the roots -/
theorem mem_sblptn_irt_iff (hb : b ∉ T.nd) {X : M} :
    X ∈ (T.irt b).sblptn ↔ X = insert b T.rt ∨ (X ∈ T.sblptn ∧ X ≠ T.rt) := by
  have hran : X ∈ ran (T.irt b).chd ↔ X = ∅ ∨ X ∈ ran T.chd := by
    rw [(hT.irt hb).isFunction_chd.mem_ran_iff, hT.dom_chd_irt, hT.isFunction_chd.mem_ran_iff,
      hT.dom_chd]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [mem_insert_iff] at hp
      rcases hp with rfl | hp
      · left
        exact hT.chd_irt_val_self
      right
      exact ⟨p, hp, (hT.chd_irt_val_of_mem hb hp).symm⟩
    · rintro (rfl | ⟨p, hp, rfl⟩)
      · exact ⟨b, mem_insert b T.nd, hT.chd_irt_val_self⟩
      refine ⟨p, ?_, hT.chd_irt_val_of_mem hb hp⟩
      rw [mem_insert_iff]
      exact Or.inr hp
  -- a nonempty set of children is not the set of roots
  have hrt : X ∈ ran T.chd → X ≠ ∅ → X ≠ T.rt := by
    intro hX hne hXrt
    rw [ne_empty_iff] at hne
    obtain ⟨a, ha⟩ := hne
    exact hT.not_mem_rt_of_mem_ran_chd hX ha (hXrt ▸ ha)
  have hins : insert b T.rt ≠ ∅ := insert_ne_empty b T.rt
  rw [mem_sblptn_iff, mem_sblptn_iff, hT.rt_irt hb, hran]
  grind

omit [HasOmega M] in
theorem insert_rt_not_mem_sblptn (hb : b ∉ T.nd) : insert b T.rt ∉ T.sblptn :=
  fun h ↦ hb (hT.subset_nd_of_mem_sblptn h (mem_insert b T.rt))

/-- A tree structure without roots has no nodes -/
theorem nd_eq_empty_of_rt_eq_empty (hrt : T.rt = ∅) : T.nd = ∅ := by
  by_contra hnd
  exact hT.rt_ne_empty (fun hT₀ ↦ hnd (by rw [hT₀, nd_empty])) hrt

/-- Inserting new children `B` of a node `a` into a tree structure gives a tree structure -/
theorem ichd (ha : a ∈ T.nd) (hB : B ∩ T.nd = ∅) : (T.ichd a B).IsTreeStructure where
  isOrderedPair := isOrderedPair_mk _ _ _
  isOrderedPair_right := isOrderedPair_right_mk _ _ _
  dep_fromTo := by
    refine isFunctionFromTo_of_val (hT.isFunction_dep_ichd hB)
      (hT.dom_dep_ichd.trans nd_ichd.symm) fun c hc ↦ ?_
    rw [nd_ichd, mem_union_iff] at hc
    rcases hc with hc | hc
    · rw [hT.dep_ichd_val_of_mem_nd hB hc]
      exact hT.dep_mem_omega hc
    rw [hT.dep_ichd_val_of_mem_new hB hc]
    exact succ_mem_omega (hT.dep_mem_omega ha)
  isFunction_chd := hT.isFunction_chd_ichd ha hB
  dom_chd := (hT.dom_chd_ichd ha).trans nd_ichd.symm
  chd_subset := by
    intro c hc e he
    rw [hT.mem_chd_ichd_val_iff ha hB] at he
    rw [nd_ichd, mem_union_iff]
    rcases he with ⟨hcA, he⟩ | ⟨rfl, he⟩
    · left
      exact hT.chd_subset c hcA he
    · right
      exact he
  dep_of_mem_chd := by
    intro c hc e he
    rw [hT.mem_chd_ichd_val_iff ha hB] at he
    rcases he with ⟨hcA, he⟩ | ⟨rfl, he⟩
    · rw [hT.dep_ichd_val_of_mem_nd hB (hT.chd_subset c hcA he),
        hT.dep_ichd_val_of_mem_nd hB hcA]
      exact hT.dep_of_mem_chd c hcA e he
    · rw [hT.dep_ichd_val_of_mem_new hB he, hT.dep_ichd_val_of_mem_nd hB ha]
  existsUnique_prt := by
    intro e he hpos
    simp only [hT.mem_chd_ichd_val_iff ha hB]
    rw [nd_ichd, mem_union_iff] at he
    rcases he with he | he
    swap
    · have heA := not_mem_nd_of_mem_new hB he
      refine ⟨a, Or.inr ⟨rfl, he⟩, fun p hp ↦ ?_⟩
      grind [hT.chd_subset]
    rw [hT.dep_ichd_val_of_mem_nd hB he] at hpos
    obtain ⟨q, hq, huniq⟩ := hT.existsUnique_prt e he hpos
    have hqA := hT.mem_nd_of_mem_chd_val hq
    refine ⟨q, Or.inl ⟨hqA, hq⟩, fun p hp ↦ ?_⟩
    rcases hp with ⟨-, hp⟩ | ⟨-, hp⟩
    · exact huniq p hp
    · grind [not_mem_nd_of_mem_new hB hp]

/-- Inserting a new child `b ∉ T.nd` of a node `a` gives a tree structure -/
theorem ionechd (ha : a ∈ T.nd) (hb : b ∉ T.nd) : (T.ionechd a b).IsTreeStructure :=
  hT.ichd ha (singleton_inter_eq_empty hb)

omit [HasOmega M] in
/-- Adding children does not change the roots -/
theorem rt_ichd (hB : B ∩ T.nd = ∅) : (T.ichd a B).rt = T.rt := by
  ext c
  rw [mem_rt_iff, mem_rt_iff, nd_ichd, mem_union_iff]
  constructor
  · rintro ⟨hc | hc, hd⟩
    · rw [hT.dep_ichd_val_of_mem_nd hB hc] at hd
      exact ⟨hc, hd⟩
    rw [hT.dep_ichd_val_of_mem_new hB hc] at hd
    exact (succ_ne_empty (T.dep ﹫ a) hd).elim
  · rintro ⟨hc, hd⟩
    rw [hT.dep_ichd_val_of_mem_nd hB hc]
    exact ⟨Or.inl hc, hd⟩

/-- The sibling partition of `T.ichd a B` for `B ≠ ∅`: the children of `a` together with `B`,
and the old sets of siblings other than the children of `a` -/
theorem mem_sblptn_ichd_iff (ha : a ∈ T.nd) (hB : B ∩ T.nd = ∅) (hBne : B ≠ ∅) {X : M} :
    X ∈ (T.ichd a B).sblptn ↔
      X = T.chd ﹫ a ∪ B ∨ (X ∈ T.sblptn ∧ X ≠ T.chd ﹫ a) := by
  have hT' := hT.ichd ha hB
  rw [ne_empty_iff] at hBne
  obtain ⟨c₀, hc₀⟩ := hBne
  have hc₀A := not_mem_nd_of_mem_new hB hc₀
  have hran : X ∈ ran (T.ichd a B).chd ↔
      X = ∅ ∨ X = T.chd ﹫ a ∪ B ∨ ∃ p ∈ T.nd, p ≠ a ∧ T.chd ﹫ p = X := by
    rw [hT'.isFunction_chd.mem_ran_iff, hT'.dom_chd, nd_ichd]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [mem_union_iff] at hp
      rcases hp with hp | hp
      · by_cases hpa : p = a
        · subst hpa
          right
          left
          exact hT.chd_ichd_val_self hp hB
        right
        right
        exact ⟨p, hp, hpa, (hT.chd_ichd_val_of_ne ha hB hp hpa).symm⟩
      left
      exact hT.chd_ichd_val_of_mem_new ha hB hp
    · rintro (rfl | rfl | ⟨p, hp, hpa, rfl⟩)
      · refine ⟨c₀, ?_, hT.chd_ichd_val_of_mem_new ha hB hc₀⟩
        rw [mem_union_iff]
        exact Or.inr hc₀
      · refine ⟨a, ?_, hT.chd_ichd_val_self ha hB⟩
        rw [mem_union_iff]
        exact Or.inl ha
      refine ⟨p, ?_, hT.chd_ichd_val_of_ne ha hB hp hpa⟩
      rw [mem_union_iff]
      exact Or.inl hp
  -- different nonempty sets of children are different
  have hdisj : ∀ p ∈ T.nd, p ≠ a → T.chd ﹫ p ≠ ∅ → T.chd ﹫ p ≠ T.chd ﹫ a := by
    intro p hp hpa hne heq
    rw [ne_empty_iff] at hne
    obtain ⟨e, he⟩ := hne
    have hpos := hT.empty_olt_dep_of_mem_chd hp he
    exact hpa ((hT.existsUnique_prt e (hT.chd_subset p hp he) hpos).unique he (heq ▸ he))
  have hCran : T.chd ﹫ a ∈ ran T.chd := by
    rw [hT.isFunction_chd.mem_ran_iff, hT.dom_chd]
    exact ⟨a, ha, rfl⟩
  have hrtC : T.rt ≠ ∅ → T.rt ≠ T.chd ﹫ a := by
    intro hne heq
    rw [ne_empty_iff] at hne
    obtain ⟨e, he⟩ := hne
    exact hT.not_mem_rt_of_mem_ran_chd hCran (heq ▸ he) he
  have hrtins : T.rt ≠ T.chd ﹫ a ∪ B := by
    intro h
    have hc₀rt : c₀ ∈ T.rt := by
      rw [h, mem_union_iff]
      exact Or.inr hc₀
    rw [mem_rt_iff] at hc₀rt
    exact hc₀A hc₀rt.left
  have hinsne : T.chd ﹫ a ∪ B ≠ ∅ := by
    rw [ne_empty_iff]
    refine ⟨c₀, ?_⟩
    rw [mem_union_iff]
    exact Or.inr hc₀
  rw [mem_sblptn_iff, mem_sblptn_iff, hT.rt_ichd hB, hran, hT.isFunction_chd.mem_ran_iff,
    hT.dom_chd]
  constructor
  · rintro ⟨hX | hX | hX | ⟨p, hp, hpa, rfl⟩, hne⟩
    · subst hX
      exact Or.inr ⟨⟨Or.inl rfl, hne⟩, hrtC hne⟩
    · exact (hne hX).elim
    · exact Or.inl hX
    · exact Or.inr ⟨⟨Or.inr ⟨p, hp, rfl⟩, hne⟩, hdisj p hp hpa hne⟩
  · rintro (rfl | ⟨⟨hX | ⟨p, hp, rfl⟩, hne⟩, hXa⟩)
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hinsne⟩
    · exact ⟨Or.inl hX, hne⟩
    refine ⟨Or.inr (Or.inr (Or.inr ⟨p, hp, ?_, rfl⟩)), hne⟩
    rintro rfl
    exact hXa rfl

/-- The sibling partition of `T.ionechd a b`: the children of `a` together with `b`, and the old
sets of siblings other than the children of `a` -/
theorem mem_sblptn_ionechd_iff (ha : a ∈ T.nd) (hb : b ∉ T.nd) {X : M} :
    X ∈ (T.ionechd a b).sblptn ↔
      X = insert b (T.chd ﹫ a) ∨ (X ∈ T.sblptn ∧ X ≠ T.chd ﹫ a) := by
  have hins : T.chd ﹫ a ∪ {b} = insert b (T.chd ﹫ a) := by
    rw [insert_eq, union_comm]
  rw [TreeStructure.ionechd, hT.mem_sblptn_ichd_iff ha (singleton_inter_eq_empty hb)
    (singleton_ne_empty (x := b)), hins]

/-- A new sibling of a non-root `a` is a new child of the parent of `a` -/
theorem isbl_eq_ionechd (ha : a ∈ T.nd \ T.rt) (hb : b ∉ T.nd) :
    T.isbl a b = T.ionechd (T.prt ﹫ a) b := by
  have hachd := hT.mem_chd_prt_val ha
  have hp := hT.prt_val_mem_nd ha
  have hpdom : T.prt ﹫ a ∈ dom T.chd := by rwa [hT.dom_chd]
  have hB := singleton_inter_eq_empty hb
  rw [mem_sdiff_iff] at ha
  rw [isbl_of_not_mem_rt ha.right, TreeStructure.ionechd, (hT.ichd hp hB).eq_mk, mk_eq_mk_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext z
    simp only [nd_ichd, mem_insert_iff, mem_union_iff, mem_singleton_iff]
    tauto
  · refine (hT.dep_fromTo.isFunction.update b (T.dep ﹫ a)).ext (hT.isFunction_dep_ichd hB) ?_ ?_
    · rw [dom_update, hT.dep_fromTo.dom_eq, hT.dom_dep_ichd]
      ext z
      simp only [mem_insert_iff, mem_union_iff, mem_singleton_iff]
      tauto
    intro z hz
    rw [dom_update, hT.dep_fromTo.dom_eq, mem_insert_iff] at hz
    rcases hz with rfl | hz
    · rw [val_update_self hT.dep_fromTo.isFunction,
        hT.dep_ichd_val_of_mem_new hB (mem_singleton (x := z)),
        hT.dep_of_mem_chd (T.prt ﹫ a) hp a hachd]
    rw [val_update_of_ne hT.dep_fromTo.isFunction (T.dep ﹫ a) (by rwa [hT.dep_fromTo.dom_eq])
      (by grind), hT.dep_ichd_val_of_mem_nd hB hz]
  · have hf := hT.isFunction_chd.insertVal (T.prt ﹫ a) b
    refine (hf.update b ∅).ext (hT.isFunction_chd_ichd hp hB) ?_ ?_
    · rw [dom_update, dom_insertVal hpdom, hT.dom_chd, hT.dom_chd_ichd hp]
      ext z
      simp only [mem_insert_iff, mem_union_iff, mem_singleton_iff]
      tauto
    intro z hz
    rw [dom_update, dom_insertVal hpdom, hT.dom_chd, mem_insert_iff] at hz
    rcases hz with rfl | hz
    · rw [val_update_self hf, hT.chd_ichd_val_of_mem_new hp hB (mem_singleton (x := z))]
    rw [val_update_of_ne hf ∅ (by rwa [dom_insertVal hpdom, hT.dom_chd]) (by grind)]
    by_cases hzp : z = T.prt ﹫ a
    · rw [hzp, val_insertVal_self hT.isFunction_chd, hT.chd_ichd_val_self hp hB]
    rw [val_insertVal_of_ne hT.isFunction_chd b (by rwa [hT.dom_chd]) hzp,
      hT.chd_ichd_val_of_ne hp hB hz hzp]

/-- Inserting a new sibling `b ∉ T.nd` of a non-root `a` gives a tree structure -/
theorem isbl (ha : a ∈ T.nd \ T.rt) (hb : b ∉ T.nd) : (T.isbl a b).IsTreeStructure := by
  rw [hT.isbl_eq_ionechd ha hb]
  exact hT.ionechd (hT.prt_val_mem_nd ha) hb

/-- Inserting a new sibling `b ∉ T.nd` of any node `a` gives a tree structure -/
theorem isbl_of_mem_nd (ha : a ∈ T.nd) (hb : b ∉ T.nd) : (T.isbl a b).IsTreeStructure := by
  by_cases hart : a ∈ T.rt
  · rw [isbl_of_mem_rt hart]
    exact hT.irt hb
  exact hT.isbl (by rw [mem_sdiff_iff]; exact ⟨ha, hart⟩) hb

/-- The nodes of `T.isbl a b` are the old nodes and `b` -/
theorem mem_nd_isbl_iff (ha : a ∈ T.nd) (hb : b ∉ T.nd) {c : M} :
    c ∈ (T.isbl a b).nd ↔ c = b ∨ c ∈ T.nd := by
  by_cases hart : a ∈ T.rt
  · rw [isbl_of_mem_rt hart, nd_irt, mem_insert_iff]
  have ha' : a ∈ T.nd \ T.rt := by
    rw [mem_sdiff_iff]
    exact ⟨ha, hart⟩
  rw [hT.isbl_eq_ionechd ha' hb, TreeStructure.ionechd, nd_ichd, mem_union_iff,
    mem_singleton_iff, or_comm]

/-- The sibling partition of `T.isbl a b`: the siblings of `a` together with `b`, and the old
sets of siblings other than the siblings of `a` -/
theorem mem_sblptn_isbl_iff (ha : a ∈ T.nd) (hb : b ∉ T.nd) {X : M} :
    X ∈ (T.isbl a b).sblptn ↔
      X = insert b (T.sbl ﹫ a) ∨ (X ∈ T.sblptn ∧ X ≠ T.sbl ﹫ a) := by
  by_cases hart : a ∈ T.rt
  · rw [isbl_of_mem_rt hart, hT.sbl_val_of_mem_rt hart, hT.mem_sblptn_irt_iff hb]
  have ha' : a ∈ T.nd \ T.rt := by
    rw [mem_sdiff_iff]
    exact ⟨ha, hart⟩
  rw [hT.isbl_eq_ionechd ha' hb, hT.sbl_val_of_not_mem_rt ha',
    hT.mem_sblptn_ionechd_iff (hT.prt_val_mem_nd ha') hb]

/-- The single node of a tree structure is its root -/
theorem rt_eq_of_nd_eq_singleton (hnd : T.nd = {b}) : T.rt = {b} := by
  have hne : T ≠ ∅ := by
    rintro rfl
    rw [nd_empty] at hnd
    have hb : b ∈ (∅ : M) := by
      rw [hnd]
      exact mem_singleton b
    simp at hb
  have hrt := hT.rt_ne_empty hne
  rw [ne_empty_iff] at hrt
  obtain ⟨r, hr⟩ := hrt
  ext a
  grind [mem_rt_iff]

/-- The single node of a tree structure has depth `∅` -/
theorem dep_val_of_nd_eq_singleton (hnd : T.nd = {b}) : T.dep ﹫ b = ∅ := by
  have hb : b ∈ T.rt := by
    rw [hT.rt_eq_of_nd_eq_singleton hnd]
    exact mem_singleton b
  exact (mem_rt_iff.mp hb).right

/-- A tree structure with a single node has no parent pairs -/
theorem not_rel_prt_of_nd_eq_singleton (hnd : T.nd = {b}) (a a' : M) : ¬a [T.prt] a' := by
  intro hrel
  have ha : a ∈ dom T.prt := by
    rw [mem_dom_iff]
    exact ⟨a', hrel⟩
  rw [hT.dom_prt, mem_sdiff_iff, hT.rt_eq_of_nd_eq_singleton hnd, hnd] at ha
  exact ha.right ha.left

end IsTreeStructure

/-- `T_map(π)`: the image of `T` under `π`, with nodes `π '' A`, depth `d ∘ π⁻¹` and children
`b ↦ π '' C(π⁻¹(b))`; a copy of `T` if `π` is injective on `A` -/
noncomputable def map (T : TreeStructure M) (π : M) : TreeStructure M :=
  mk (π '' T.nd) (T.dep !∘ π⁻¹) ((fun b ↦ π '' (T.chd ﹫ (π⁻¹ ﹫ b))) ↾₀ (π '' T.nd))

/-- `T_iprt(a, m)`: the `m`-th iterated parent of `a` -/
noncomputable def iprt (T : TreeStructure M) (a m : M) : M := natRec a (fun b ↦ T.prt ﹫ b) m

/-- `b` is an ancestor of `a` (or `a` itself): `b` lies in every set of nodes containing `a` and
closed under parents -/
def IsAnc (T : TreeStructure M) (a b : M) : Prop :=
  ∀ X, X ⊆ T.nd → a ∈ X → (∀ c ∈ X, c ∈ T.nd \ T.rt → T.prt ﹫ c ∈ X) → b ∈ X

/-- `T_anc(a, k)`: the ancestor of `a` of depth `k` -/
noncomputable def anc (T : TreeStructure M) (a k : M) : M :=
  ⋃₀ (T.nd ∩₀ fun b ↦ T.dep ﹫ b = k ∧ T.IsAnc a b)

/-- `ofRt(A)`: the tree structure whose nodes `A` are all roots -/
noncomputable def ofRt (A : M) : TreeStructure M := mk A (constFun A ∅) (constFun A ∅)

/-- `π` is an embedding of the tree structure `T` into `T'`: an injection of the nodes that
preserves the depth and the parent relation -/
structure IsEmbedding (T T' : TreeStructure M) (π : M) : Prop where
  isInjectionFromTo : π !: T.nd ↪ T'.nd
  dep_val {a : M} (ha : a ∈ T.nd) : T'.dep ﹫ (π ﹫ a) = T.dep ﹫ a
  rel_prt {a b : M} (ha : a ∈ T.nd) (hb : b ∈ T.nd) (hba : b [T.prt] a) :
    (π ﹫ b) [T'.prt] (π ﹫ a)

/-- `π` is an isomorphism of the tree structure `T` onto `T'`: a surjective embedding -/
structure IsIsomorphism (T T' : TreeStructure M) (π : M) : Prop where
  isEmbedding : T.IsEmbedding T' π
  ran_eq : ran π = T'.nd

namespace IsEmbedding

variable [HasOmega M] {T T' : TreeStructure M} {π : M} (hT : T.IsTreeStructure)
  (hT' : T'.IsTreeStructure) (he : T.IsEmbedding T' π)
include hT hT' he

omit [HasOmega M] hT hT' in
/-- An embedding sends roots exactly to roots -/
theorem mem_rt_iff (ha : a ∈ T.nd) : π ﹫ a ∈ T'.rt ↔ a ∈ T.rt := by
  rw [TreeStructure.mem_rt_iff, TreeStructure.mem_rt_iff, he.dep_val ha]
  exact ⟨fun h ↦ ⟨ha, h.right⟩, fun h ↦ ⟨he.isInjectionFromTo.left.val_mem ha, h.right⟩⟩

/-- An embedding commutes with the parent function -/
theorem prt_val (ha : a ∈ T.nd \ T.rt) : T'.prt ﹫ (π ﹫ a) = π ﹫ (T.prt ﹫ a) := by
  have hp := hT.prt_val_mem_nd ha
  have hrel : a [T.prt] (T.prt ﹫ a) := by
    rw [hT.rel_prt_iff_mem_chd hp]
    exact hT.mem_chd_prt_val ha
  have ha' : a ∈ T.nd := by
    rw [mem_sdiff_iff] at ha
    exact ha.left
  exact hT'.isFunction_prt.val_eq_of_rel (he.rel_prt hp ha' hrel)

/-- An embedding sends siblings exactly to siblings -/
theorem sbl_val_eq_iff (ha : a ∈ T.nd) (hb : b ∈ T.nd) :
    T'.sbl ﹫ (π ﹫ a) = T'.sbl ﹫ (π ﹫ b) ↔ T.sbl ﹫ a = T.sbl ﹫ b := by
  have hf := he.isInjectionFromTo.left
  rw [hT'.sbl_val_eq_iff_mem (hf.val_mem ha) (hf.val_mem hb), hT.sbl_val_eq_iff_mem ha hb]
  by_cases hart : a ∈ T.rt
  · rw [hT.sbl_val_of_mem_rt hart, hT'.sbl_val_of_mem_rt ((he.mem_rt_iff ha).mpr hart),
      he.mem_rt_iff hb]
  have ha' : a ∈ T.nd \ T.rt := by
    rw [mem_sdiff_iff]
    exact ⟨ha, hart⟩
  have hπa : π ﹫ a ∈ T'.nd \ T'.rt := by
    rw [mem_sdiff_iff]
    exact ⟨hf.val_mem ha, fun h ↦ hart ((he.mem_rt_iff ha).mp h)⟩
  have hp := hT.prt_val_mem_nd ha'
  rw [hT.sbl_val_of_not_mem_rt ha', hT'.sbl_val_of_not_mem_rt hπa, prt_val hT hT' he ha',
    ← hT'.rel_prt_iff_mem_chd (hf.val_mem hp), ← hT.rel_prt_iff_mem_chd hp]
  refine ⟨fun h ↦ ?_, he.rel_prt hp hb⟩
  have hb' : b ∈ T.nd \ T.rt := by
    rw [mem_sdiff_iff]
    refine ⟨hb, fun hbr ↦ ?_⟩
    have hdom : π ﹫ b ∈ dom T'.prt := by
      rw [mem_dom_iff]
      exact ⟨_, h⟩
    rw [hT'.dom_prt, mem_sdiff_iff, he.mem_rt_iff hb] at hdom
    exact hdom.right hbr
  have hq := hT.prt_val_mem_nd hb'
  have hrel : b [T.prt] (T.prt ﹫ b) := by
    rw [hT.rel_prt_iff_mem_chd hq]
    exact hT.mem_chd_prt_val hb'
  have heq : π ﹫ (T.prt ﹫ b) = π ﹫ (T.prt ﹫ a) :=
    (hT'.isFunction_prt.val_eq_of_rel (he.rel_prt hq hb hrel)).symm.trans
      (hT'.isFunction_prt.val_eq_of_rel h)
  rwa [← he.isInjectionFromTo.right hq hp heq]

end IsEmbedding

omit [ModelsKP M] in
/-- An isomorphism is a bijection of the nodes -/
theorem IsIsomorphism.isBijectionFromTo {T T' : TreeStructure M} {π : M}
    (h : T.IsIsomorphism T' π) : π !: T.nd ↔ T'.nd :=
  ⟨h.isEmbedding.isInjectionFromTo, h.isEmbedding.isInjectionFromTo.left, h.ran_eq⟩

/-- `T.sngIso T' = {(b, c)}` for tree structures `T` and `T'` with single nodes `b` and `c`: the
unique isomorphism of `T` onto `T'` -/
noncomputable def sngIso (T T' : TreeStructure M) : M := singletonFun (⋃₀ T.nd) (⋃₀ T'.nd)

section SngIso

variable {T T' : TreeStructure M} {b c π : M} (hnd : T.nd = {b}) (hnd' : T'.nd = {c})
include hnd hnd'

theorem sngIso_eq : T.sngIso T' = singletonFun b c := by
  rw [sngIso, hnd, hnd', sUnion_singleton, sUnion_singleton]

/-- `T.sngIso T'` is an isomorphism of `T` onto `T'` -/
theorem isIsomorphism_sngIso [HasOmega M] (hT : T.IsTreeStructure) (hT' : T'.IsTreeStructure) :
    T.IsIsomorphism T' (T.sngIso T') := by
  rw [sngIso_eq hnd hnd']
  refine ⟨⟨⟨?_, ?_⟩, ?_, fun _ _ h ↦ (hT.not_rel_prt_of_nd_eq_singleton hnd _ _ h).elim⟩, ?_⟩
  · rw [hnd, hnd']
    exact isFunctionFromTo_singletonFun (mem_singleton c)
  · intro a a' ha ha' _
    rw [hnd, mem_singleton_iff] at ha ha'
    rw [ha, ha']
  · intro a ha
    rw [hnd, mem_singleton_iff] at ha
    rw [ha, singletonFun_val, hT'.dep_val_of_nd_eq_singleton hnd',
      hT.dep_val_of_nd_eq_singleton hnd]
  · rw [ran_singletonFun, hnd']

/-- `T.sngIso T'` is the unique embedding of `T` into `T'` -/
theorem IsEmbedding.eq_sngIso (he : T.IsEmbedding T' π) : π = T.sngIso T' := by
  have hf := he.isInjectionFromTo.left
  have hb : b ∈ T.nd := by
    rw [hnd]
    exact mem_singleton b
  have hval := hf.val_mem hb
  rw [hnd', mem_singleton_iff] at hval
  rw [sngIso_eq hnd hnd']
  refine hf.isFunction.ext (isFunction_singletonFun b c) ?_ fun a ha ↦ ?_
  · rw [hf.dom_eq, hnd, dom_singletonFun]
  rw [hf.dom_eq, hnd, mem_singleton_iff] at ha
  rw [ha, hval, singletonFun_val]

end SngIso

section OfRt

variable {A a : M}

@[simp]
theorem nd_ofRt : (ofRt A).nd = A := nd_mk _ _ _

@[simp]
theorem dep_ofRt : (ofRt A).dep = constFun A ∅ := dep_mk _ _ _

@[simp]
theorem chd_ofRt : (ofRt A).chd = constFun A ∅ := chd_mk _ _ _

theorem chd_ofRt_val : (ofRt A).chd ﹫ a = ∅ := by
  by_cases ha : a ∈ A
  · rw [chd_ofRt, val_constFun ha]
  · rw [chd_ofRt, val_eq_empty_of_not_mem_dom (by rwa [dom_constFun])]

/-- All nodes of `ofRt(A)` are roots -/
theorem rt_ofRt : (ofRt A).rt = A := by
  ext a
  rw [mem_rt_iff, nd_ofRt, dep_ofRt]
  exact ⟨fun h ↦ h.left, fun h ↦ ⟨h, val_constFun h⟩⟩

/-- `ofRt(A)` is a tree structure -/
theorem isTreeStructure_ofRt [HasOmega M] : (ofRt A).IsTreeStructure where
  isOrderedPair := isOrderedPair_mk _ _ _
  isOrderedPair_right := isOrderedPair_right_mk _ _ _
  dep_fromTo := by
    rw [dep_ofRt, nd_ofRt]
    refine ⟨isFunction_constFun _ _, dom_constFun _ _, fun x hx ↦ ?_⟩
    have h := ran_constFun_subset _ _ hx
    rw [mem_singleton_iff] at h
    rw [h]
    exact empty_mem_omega
  isFunction_chd := by
    rw [chd_ofRt]
    exact isFunction_constFun _ _
  dom_chd := by rw [chd_ofRt, dom_constFun, nd_ofRt]
  chd_subset := fun a _ ↦ by
    rw [chd_ofRt_val]
    exact empty_subset _
  dep_of_mem_chd := fun a _ b hb ↦ by
    rw [chd_ofRt_val] at hb
    simp at hb
  existsUnique_prt := fun b hb h ↦ by
    rw [nd_ofRt] at hb
    rw [dep_ofRt, val_constFun hb] at h
    simp at h

end OfRt

section Anc

/-! ### Iterated parents and ancestors -/

variable [HasOmega M] {T : TreeStructure M} {a k m n : M}

instance (T : TreeStructure M) (a : M) :
    ClassFunction.Sigma (fun m : M ↦ T.iprt a m) 1 Set.univ := by
  unfold iprt; infer_instance

instance [ModelsZF M] (T : TreeStructure M) (a : M) :
    Class.Definable (fun b : M ↦ T.IsAnc a b) Set.univ := by
  unfold IsAnc; infer_instance

omit [HasOmega M] in
theorem iprt_empty : T.iprt a ∅ = a := natRec_empty _ _

omit [HasOmega M] in
theorem iprt_succ (hm : Ordinal m) : T.iprt a (succ m) = T.prt ﹫ T.iprt a m :=
  natRec_succ _ _ hm

omit [HasOmega M] in
/-- `succ` is injective on ordinals -/
theorem eq_of_succ_eq_succ [Foundational M] (hm : Ordinal m) (h : succ m = succ n) : m = n := by
  have hm' : m ∈ succ n := h ▸ mem_succ_self m
  have hn' : n ∈ succ m := h.symm ▸ mem_succ_self n
  rcases mem_or_eq_of_mem_succ hm' with h₁ | h₁
  · rcases mem_or_eq_of_mem_succ hn' with h₂ | h₂
    · exact (notMem_self _ (hm.transitive _ h₂ h₁)).elim
    · exact h₂.symm
  · exact h₁

/-- For `k ≤ n` in `ω`, `k +ₒ m = n` for some `m ∈ ω` -/
theorem exists_oadd_eq (hn : n ∈ (ω : M)) (hk : k ∈ succ n) : ∃ m ∈ (ω : M), k +ₒ m = n := by
  refine omega_induction (A := fun n ↦ ∀ k ∈ succ n, ∃ m ∈ (ω : M), k +ₒ m = n)
    (fun k hk ↦ ?_) (fun n hn ih k hk ↦ ?_) hn k hk
  · rcases mem_or_eq_of_mem_succ hk with h | rfl
    · simp at h
    · exact ⟨∅, empty_mem_omega, oadd_empty ordinal_empty⟩
  · have hnω := succ_mem_omega hn
    rcases mem_or_eq_of_mem_succ hk with h | rfl
    · obtain ⟨m, hm, hkm⟩ := ih k h
      have hko : Ordinal k := ordinal_of_mem (ordinal_of_mem ordinal_omega hnω) h
      refine ⟨succ m, succ_mem_omega hm, ?_⟩
      rw [oadd_succ hko (ordinal_of_mem ordinal_omega hm), hkm]
    · exact ⟨∅, empty_mem_omega, oadd_empty (ordinal_of_mem ordinal_omega hnω)⟩

variable (hT : T.IsTreeStructure)
include hT

namespace IsTreeStructure

/-- The `m`-th iterated parent of a node of depth `e +ₒ m` is a node of depth `e` -/
theorem iprt_mem_nd (ha : a ∈ T.nd) (hm : m ∈ (ω : M)) {e : M} (he : e ∈ (ω : M))
    (hd : T.dep ﹫ a = e +ₒ m) : T.iprt a m ∈ T.nd ∧ T.dep ﹫ T.iprt a m = e := by
  refine omega_induction (A := fun m ↦ ∀ e ∈ (ω : M), T.dep ﹫ a = e +ₒ m →
    T.iprt a m ∈ T.nd ∧ T.dep ﹫ T.iprt a m = e) (fun e he hd ↦ ?_)
    (fun m hm ih e he hd ↦ ?_) hm e he hd
  · rw [oadd_empty (ordinal_of_mem ordinal_omega he)] at hd
    rw [iprt_empty]
    exact ⟨ha, hd⟩
  · have heo := ordinal_of_mem ordinal_omega he
    have hmo := ordinal_of_mem ordinal_omega hm
    have hd' : T.dep ﹫ a = succ e +ₒ m := by
      rw [hd, oadd_succ heo hmo, oadd_comm_of_mem_omega (succ_mem_omega he) hm,
        oadd_succ hmo heo, oadd_comm_of_mem_omega hm he]
    obtain ⟨hb, hdb⟩ := ih (succ e) (succ_mem_omega he) hd'
    have hbr : T.iprt a m ∈ T.nd \ T.rt := by
      rw [mem_sdiff_iff, mem_rt_iff, hdb]
      exact ⟨hb, fun h ↦ succ_ne_empty _ h.right⟩
    have hc := hT.prt_val_mem_nd hbr
    have hdc := hT.dep_of_mem_chd _ hc _ (hT.mem_chd_prt_val hbr)
    rw [hdb] at hdc
    rw [iprt_succ hmo]
    exact ⟨hc, (eq_of_succ_eq_succ heo hdc).symm⟩

/-- Beyond the depth of a node, the iterated parents are `∅` if `∅` is not a node -/
theorem iprt_eq_empty (h0 : ∅ ∉ T.nd) (ha : a ∈ T.nd) (hm : m ∈ (ω : M))
    (hlt : T.dep ﹫ a ∈ m) : T.iprt a m = ∅ := by
  have hdω := hT.dep_mem_omega ha
  have hprt (b : M) (hb : b ∉ T.nd \ T.rt) : T.prt ﹫ b = ∅ :=
    val_eq_empty_of_not_mem_dom (by rwa [hT.dom_prt])
  refine omega_induction (A := fun m ↦ T.dep ﹫ a ∈ m → T.iprt a m = ∅) (fun h ↦ by simp at h)
    (fun m hm ih h ↦ ?_) hm hlt
  rw [iprt_succ (ordinal_of_mem ordinal_omega hm)]
  refine hprt _ fun hb ↦ ?_
  rw [mem_sdiff_iff] at hb
  rcases mem_or_eq_of_mem_succ h with h | h
  · rw [ih h] at hb
    exact h0 hb.left
  · obtain ⟨-, hdb⟩ := hT.iprt_mem_nd ha hm empty_mem_omega
      (by rw [h, empty_oadd (ordinal_of_mem ordinal_omega hm)])
    exact hb.right (mem_rt_iff.mpr ⟨hb.left, hdb⟩)

omit hT in
/-- `m ≤ k +ₒ m` -/
theorem mem_succ_of_oadd_eq (hk : k ∈ (ω : M)) (hm : m ∈ (ω : M)) (h : k +ₒ m = n) :
    m ∈ succ n := by
  obtain ⟨-, -, h'⟩ := ole_oadd_left (ordinal_of_mem ordinal_omega hk)
    (ordinal_of_mem ordinal_omega hm)
  rw [h] at h'
  rcases h' with h' | h'
  · exact mem_succ_of_mem h'
  · rw [h']
    exact mem_succ_self n

/-- The iterated parents of `a` up to its depth -/
theorem exists_iprt_mem_nd (ha : a ∈ T.nd) (hj : m ∈ succ (T.dep ﹫ a)) :
    ∃ e ∈ (ω : M), e +ₒ m = T.dep ﹫ a ∧ T.iprt a m ∈ T.nd ∧ T.dep ﹫ T.iprt a m = e := by
  have hdω := hT.dep_mem_omega ha
  have hmω : m ∈ (ω : M) := ordinal_omega.transitive _ (succ_mem_omega hdω) hj
  obtain ⟨e, he, hme⟩ := exists_oadd_eq hdω hj
  rw [oadd_comm_of_mem_omega hmω he] at hme
  exact ⟨e, he, hme, hT.iprt_mem_nd ha hmω he hme.symm⟩

/-- The ancestor of depth `k` of `a` is the `m`-th iterated parent for `k +ₒ m = T.dep ﹫ a` -/
theorem anc_eq_iprt [ModelsZF M] (ha : a ∈ T.nd) (hk : k ∈ (ω : M)) (hm : m ∈ (ω : M))
    (hkm : k +ₒ m = T.dep ﹫ a) : T.anc a k = T.iprt a m := by
  have hdω := hT.dep_mem_omega ha
  have hko := ordinal_of_mem ordinal_omega hk
  have hmo := ordinal_of_mem ordinal_omega hm
  obtain ⟨hb, hdb⟩ := hT.iprt_mem_nd ha hm hk hkm.symm
  have hsU (X : M) (hX : ∀ b, b ∈ X ↔ b = T.iprt a m) : ⋃₀ X = T.iprt a m := by
    rw [show X = {T.iprt a m} by ext b; rw [hX, mem_singleton_iff], sUnion_singleton]
  have hrt {c : M} (hc : c ∈ T.nd) : c ∈ T.rt ↔ T.dep ﹫ c = ∅ := by
    rw [mem_rt_iff]
    exact ⟨fun h ↦ h.right, fun h ↦ ⟨hc, h⟩⟩
  rw [anc]
  refine hsU _ fun b ↦ ?_
  rw [mem_comprehension_iff]
  constructor
  · rintro ⟨-, hbd, hcl⟩
    -- the iterated parents up to the depth of `a` form a closed set
    have hres : IsSetRestrictedTo (fun j ↦ T.iprt a j) (succ (T.dep ﹫ a)) :=
      isSetRestrictedTo_of_definable _
    have hA (c : M) : c ∈ ran ((fun j ↦ T.iprt a j) ↾₀ succ (T.dep ﹫ a)) ↔
        ∃ j ∈ succ (T.dep ﹫ a), T.iprt a j = c :=
      mem_ran_toSetRestrictedTo_iff hres
    have hbA := hcl _ (fun c hc ↦ by
        obtain ⟨j, hj, rfl⟩ := (hA c).mp hc
        exact (hT.exists_iprt_mem_nd ha hj).choose_spec.right.right.left)
      ((hA a).mpr ⟨∅, by
        by_cases h : T.dep ﹫ a = ∅
        · rw [h]
          exact mem_succ_self ∅
        · exact mem_succ_of_mem (empty_mem_of_ordinal_of_ne_empty
            (ordinal_of_mem ordinal_omega hdω) h), iprt_empty⟩)
      fun c hc hcr ↦ by
        obtain ⟨j, hj, rfl⟩ := (hA c).mp hc
        obtain ⟨e, he, hje, -, hde⟩ := hT.exists_iprt_mem_nd ha hj
        have hjω : j ∈ (ω : M) := ordinal_omega.transitive _ (succ_mem_omega hdω) hj
        have he0 : e ≠ ∅ := fun h ↦ by
          have h' := hcr
          rw [mem_sdiff_iff] at h'
          exact h'.right ((hrt h'.left).mpr (hde.trans h))
        obtain ⟨he'ω, -, hee⟩ := sUnion_mem_of_ne_empty he he0
        have hsj : ⋃₀ e +ₒ succ j = T.dep ﹫ a := by
          refine Eq.trans ?_ hje
          rw [oadd_succ (ordinal_of_mem ordinal_omega he'ω) (ordinal_of_mem ordinal_omega hjω),
            oadd_comm_of_mem_omega he'ω hjω,
            ← oadd_succ (ordinal_of_mem ordinal_omega hjω) (ordinal_of_mem ordinal_omega he'ω),
            ← hee, oadd_comm_of_mem_omega hjω he]
        refine (hA _).mpr ⟨succ j, mem_succ_of_oadd_eq he'ω (succ_mem_omega hjω) hsj, ?_⟩
        rw [iprt_succ (ordinal_of_mem ordinal_omega hjω)]
    obtain ⟨j, hj, rfl⟩ := (hA b).mp hbA
    obtain ⟨e, he, hje, -, hde⟩ := hT.exists_iprt_mem_nd ha hj
    have hjω : j ∈ (ω : M) := ordinal_omega.transitive _ (succ_mem_omega hdω) hj
    rw [hbd] at hde
    subst hde
    rw [(oadd_left_cancel hko hmo (ordinal_of_mem ordinal_omega hjω)).mp (hkm.trans hje.symm)]
  · rintro rfl
    refine ⟨hb, hdb, fun X hX haX hcl ↦ ?_⟩
    have hmd : m ∈ succ (T.dep ﹫ a) := mem_succ_of_oadd_eq hk hm hkm
    refine omega_induction (A := fun j ↦ j ∈ succ m → T.iprt a j ∈ X)
      (fun _ ↦ by rw [iprt_empty]; exact haX) (fun j hjω ih hj ↦ ?_) hm (mem_succ_self m)
    have hjm : j ∈ m := by
      rcases mem_or_eq_of_mem_succ hj with h | h
      · exact hmo.transitive _ h (mem_succ_self j)
      · rw [← h]
        exact mem_succ_self j
    have hjd : j ∈ succ (T.dep ﹫ a) :=
      (ordinal_of_mem ordinal_omega (succ_mem_omega hdω)).transitive _ hmd
        ((ordinal_of_mem ordinal_omega (succ_mem_omega hm)).transitive _ (mem_succ_self m)
          hjm |> fun _ ↦ hmo.transitive _ hjm |> fun _ ↦ hjm)
    obtain ⟨e, he, hje, hcn, hde⟩ := hT.exists_iprt_mem_nd ha hjd
    have he0 : e ≠ ∅ := fun h ↦ by
      rw [h, empty_oadd (ordinal_of_mem ordinal_omega hjω)] at hje
      have h' := ole_oadd_left hko hmo
      rw [hkm, ← hje] at h'
      rcases h'.right.right with h'' | h''
      · exact notMem_self _ ((ordinal_of_mem ordinal_omega hjω).transitive _ h'' hjm)
      · rw [h''] at hjm
        exact notMem_self _ hjm
    have hcr : T.iprt a j ∈ T.nd \ T.rt := by
      rw [mem_sdiff_iff, hrt hcn, hde]
      exact ⟨hcn, he0⟩
    rw [iprt_succ (ordinal_of_mem ordinal_omega hjω)]
    exact hcl _ (ih (mem_succ_of_mem hjm)) hcr

/-- The ancestor of depth `k ≤ T.dep ﹫ a` is a node of depth `k` -/
theorem anc_mem_nd [ModelsZF M] (ha : a ∈ T.nd) (hk : k ∈ succ (T.dep ﹫ a)) :
    T.anc a k ∈ T.nd ∧ T.dep ﹫ T.anc a k = k := by
  have hdω := hT.dep_mem_omega ha
  obtain ⟨m, hm, hkm⟩ := exists_oadd_eq hdω hk
  have hkω : k ∈ (ω : M) := (succ_mem_omega hdω |> fun h ↦ ordinal_omega.transitive _ h hk)
  rw [hT.anc_eq_iprt ha hkω hm hkm]
  exact hT.iprt_mem_nd ha hm hkω hkm.symm

/-- The ancestor of depth `T.dep ﹫ a` of `a` is `a` -/
theorem anc_dep [ModelsZF M] (ha : a ∈ T.nd) : T.anc a (T.dep ﹫ a) = a := by
  have hdω := hT.dep_mem_omega ha
  rw [hT.anc_eq_iprt ha hdω empty_mem_omega (oadd_empty (ordinal_of_mem ordinal_omega hdω)),
    iprt_empty]

/-- The ancestor of depth `succ k` is a child of the ancestor of depth `k` -/
theorem anc_succ_mem_chd [ModelsZF M] (ha : a ∈ T.nd) (hk : k ∈ T.dep ﹫ a) :
    T.anc a (succ k) ∈ T.chd ﹫ T.anc a k := by
  have hdω := hT.dep_mem_omega ha
  have hkω : k ∈ (ω : M) := ordinal_omega.transitive _ hdω hk
  have hko := ordinal_of_mem ordinal_omega hkω
  obtain ⟨m, hm, hkm⟩ := exists_oadd_eq hdω (show succ k ∈ succ (T.dep ﹫ a) from by
    rcases olt_trichotomy (ordinal_of_mem ordinal_omega (succ_mem_omega hkω))
      (ordinal_of_mem ordinal_omega hdω) with h | h | h
    · exact mem_succ_of_mem h.right.right
    · rw [h]
      exact mem_succ_self _
    · exfalso
      rcases mem_or_eq_of_mem_succ h.right.right with h' | h'
      · exact notMem_self _ ((ordinal_of_mem ordinal_omega hkω).transitive _ h' hk)
      · exact notMem_self _ (h' ▸ hk))
  have hmo := ordinal_of_mem ordinal_omega hm
  have hkm' : k +ₒ succ m = T.dep ﹫ a := by
    rw [oadd_succ hko hmo, ← hkm, oadd_comm_of_mem_omega (succ_mem_omega hkω) hm,
      oadd_succ hmo hko, oadd_comm_of_mem_omega hm hkω]
  rw [hT.anc_eq_iprt ha (succ_mem_omega hkω) hm hkm, hT.anc_eq_iprt ha hkω
    (succ_mem_omega hm) hkm', iprt_succ hmo]
  obtain ⟨hb, hdb⟩ := hT.iprt_mem_nd ha hm (succ_mem_omega hkω) hkm.symm
  refine hT.mem_chd_prt_val ?_
  rw [mem_sdiff_iff, mem_rt_iff, hdb]
  exact ⟨hb, fun h ↦ succ_ne_empty _ h.right⟩

/-- The ancestor of depth `∅` is a root -/
theorem anc_empty_mem_rt [ModelsZF M] (ha : a ∈ T.nd) : T.anc a ∅ ∈ T.rt := by
  have hdω := hT.dep_mem_omega ha
  have h := hT.anc_mem_nd ha (show (∅ : M) ∈ succ (T.dep ﹫ a) from by
    by_cases h : T.dep ﹫ a = ∅
    · rw [h]
      exact mem_succ_self ∅
    · exact mem_succ_of_mem (empty_mem_of_ordinal_of_ne_empty
        (ordinal_of_mem ordinal_omega hdω) h))
  exact mem_rt_iff.mpr h

end IsTreeStructure

end Anc

end TreeStructure

end FirstOrder.Language.MemStructure

/-! ### `Δ₀` definitions -/

namespace FirstOrder.Language

open FirstOrder Language DeltaZeroBoundedFormula

namespace RudimentaryTerm

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] {n : ℕ}

/-- The nodes of the tree structure coded by `r` -/
noncomputable def tsNd (r : L.RudimentaryTerm n) : L.RudimentaryTerm n := r.left

/-- The depth function of the tree structure coded by `r` -/
noncomputable def tsDep (r : L.RudimentaryTerm n) : L.RudimentaryTerm n := r.right.left

/-- The children function of the tree structure coded by `r` -/
noncomputable def tsChd (r : L.RudimentaryTerm n) : L.RudimentaryTerm n := r.right.right

instance (r : L.RudimentaryTerm n) [r.CharFree] : r.tsNd.CharFree := by
  unfold tsNd; infer_instance

instance (r : L.RudimentaryTerm n) [r.CharFree] : r.tsDep.CharFree := by
  unfold tsDep; infer_instance

instance (r : L.RudimentaryTerm n) [r.CharFree] : r.tsChd.CharFree := by
  unfold tsChd; infer_instance

/-- `tsRt₀〘T〙₁` is the set of roots `{a ∈ T.nd | T.dep ﹫ a = ∅}` -/
noncomputable def tsRt₀ : L.RudimentaryTerm 1 :=
  (ᵣ0 : L.RudimentaryTerm 1).tsNd.iUnion
    (({ᵣ1} : L.RudimentaryTerm 2).ifTrue (((ᵣ0 : L.RudimentaryTerm 2).tsDep ﹫ ᵣ1).isEq ∅))

instance : (tsRt₀ : L.RudimentaryTerm 1).CharFree := by
  unfold tsRt₀; infer_instance

/-- `tsPrt₀〘T〙₁` is the parent function `{p ∈ T.nd ×ˢ T.nd | left p ∈ T.chd ﹫ right p}` -/
noncomputable def tsPrt₀ : L.RudimentaryTerm 1 :=
  ((ᵣ0 : L.RudimentaryTerm 1).tsNd ×ˢ (ᵣ0 : L.RudimentaryTerm 1).tsNd).iUnion
    (({ᵣ1} : L.RudimentaryTerm 2).ifTrue
      ((ᵣ1 : L.RudimentaryTerm 2).left.isMem ((ᵣ0 : L.RudimentaryTerm 2).tsChd ﹫ (ᵣ1).right)))

instance : (tsPrt₀ : L.RudimentaryTerm 1).CharFree := by
  unfold tsPrt₀; infer_instance

/-- `tsSbl₀〘T〙₁` is the sibling function `T.chd !∘ T.prt ∪ T.rt ×ˢ {T.rt}` -/
noncomputable def tsSbl₀ : L.RudimentaryTerm 1 :=
  (ᵣ0 : L.RudimentaryTerm 1).tsChd.comp (tsPrt₀ : L.RudimentaryTerm 1) ∪
    (tsRt₀ : L.RudimentaryTerm 1) ×ˢ ({tsRt₀} : L.RudimentaryTerm 1)

instance : (tsSbl₀ : L.RudimentaryTerm 1).CharFree := by
  unfold tsSbl₀; infer_instance

/-- `tsSblptn₀〘T〙₁` is the sibling partition `({T.rt} ∪ ran T.chd) \ {∅}` -/
noncomputable def tsSblptn₀ : L.RudimentaryTerm 1 :=
  (({(tsRt₀ : L.RudimentaryTerm 1)} : L.RudimentaryTerm 1) ∪
    (ᵣ0 : L.RudimentaryTerm 1).tsChd.ran) \
    ({∅} : L.RudimentaryTerm 1)

instance : (tsSblptn₀ : L.RudimentaryTerm 1).CharFree := by
  unfold tsSblptn₀; infer_instance

/-- `isTreeStructure₀〘T〙` says that `T` is a tree structure, as in `isTreeStructure_iff` -/
noncomputable def isTreeStructure₀ : L.DeltaZeroBoundedFormula 1 :=
  (ᵣ0 : L.RudimentaryTerm 1).isOrderedPair ⊓ (ᵣ0 : L.RudimentaryTerm 1).right.isOrderedPair ⊓
    (ᵣ0 : L.RudimentaryTerm 1).tsDep.isFunction ⊓
    (ᵣ0 : L.RudimentaryTerm 1).tsDep.dom.isEq (ᵣ0).tsNd ⊓
    (ᵣ0 : L.RudimentaryTerm 1).tsNd.allMem ((ᵣ0 : L.RudimentaryTerm 2).tsDep ﹫ ᵣ1).isNat ⊓
    (ᵣ0 : L.RudimentaryTerm 1).tsChd.isFunction ⊓
    (ᵣ0 : L.RudimentaryTerm 1).tsChd.dom.isEq (ᵣ0).tsNd ⊓
    (ᵣ0 : L.RudimentaryTerm 1).tsNd.allMem
      (((ᵣ0 : L.RudimentaryTerm 2).tsChd ﹫ ᵣ1).allMem
        ((ᵣ2 : L.RudimentaryTerm 3).isMem (ᵣ0).tsNd)) ⊓
    (ᵣ0 : L.RudimentaryTerm 1).tsNd.allMem
      (((ᵣ0 : L.RudimentaryTerm 2).tsChd ﹫ ᵣ1).allMem
        (((ᵣ0 : L.RudimentaryTerm 3).tsDep ﹫ ᵣ2).isEq ((ᵣ0).tsDep ﹫ ᵣ1).succ)) ⊓
    (ᵣ0 : L.RudimentaryTerm 1).tsNd.allMem
      ((∅ : L.RudimentaryTerm 2).isMem ((ᵣ0 : L.RudimentaryTerm 2).tsDep ﹫ ᵣ1) ⟹
        (ᵣ0 : L.RudimentaryTerm 2).tsNd.exMem
          ((ᵣ1 : L.RudimentaryTerm 3).isMem ((ᵣ0).tsChd ﹫ ᵣ2) ⊓
            (ᵣ0 : L.RudimentaryTerm 3).tsNd.allMem
              ((ᵣ1 : L.RudimentaryTerm 4).isMem ((ᵣ0).tsChd ﹫ ᵣ3) ⟹ (ᵣ3).isEq (ᵣ2))))

instance : (isTreeStructure₀ : L.DeltaZeroBoundedFormula 1).RelFree := by
  unfold isTreeStructure₀; infer_instance

/-- The roots of the tree structure coded by `r` -/
noncomputable def tsRt (r : L.RudimentaryTerm n) : L.RudimentaryTerm n := tsRt₀.substBoundRud ![r]

/-- The parent function of the tree structure coded by `r` -/
noncomputable def tsPrt (r : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  tsPrt₀.substBoundRud ![r]

instance (r : L.RudimentaryTerm n) [r.CharFree] : r.tsRt.CharFree := by
  unfold tsRt; infer_instance

instance (r : L.RudimentaryTerm n) [r.CharFree] : r.tsPrt.CharFree := by
  unfold tsPrt; infer_instance

/-- The sibling function of the tree structure coded by `r` -/
noncomputable def tsSbl (r : L.RudimentaryTerm n) : L.RudimentaryTerm n := tsSbl₀.substBoundRud ![r]

/-- The sibling partition of the tree structure coded by `r` -/
noncomputable def tsSblptn (r : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  tsSblptn₀.substBoundRud ![r]

/-- `r` codes a tree structure -/
noncomputable def isTreeStructure (r : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  isTreeStructure₀.substBoundRud ![r]

instance (r : L.RudimentaryTerm n) [r.CharFree] : r.tsSbl.CharFree := by
  unfold tsSbl; infer_instance

instance (r : L.RudimentaryTerm n) [r.CharFree] : r.tsSblptn.CharFree := by
  unfold tsSblptn; infer_instance

instance (r : L.RudimentaryTerm n) [r.CharFree] : r.isTreeStructure.RelFree := by
  unfold isTreeStructure; infer_instance

/-- The tree structure `(r, s, t)` -/
noncomputable def tsMk (r s t : L.RudimentaryTerm n) : L.RudimentaryTerm n := ᵣ(r, ᵣ(s, t))

instance (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] :
    (tsMk r s t).CharFree := by
  unfold tsMk; infer_instance

/-- `tsIrt₀〘T, b〙₂` is `T.irt b` -/
noncomputable def tsIrt₀ : L.RudimentaryTerm 2 :=
  tsMk (insert (ᵣ1) (ᵣ0 : L.RudimentaryTerm 2).tsNd)
    ((ᵣ0 : L.RudimentaryTerm 2).tsDep.update (ᵣ1) ∅)
    ((ᵣ0 : L.RudimentaryTerm 2).tsChd.update (ᵣ1) ∅)

instance : (tsIrt₀ : L.RudimentaryTerm 2).CharFree := by
  unfold tsIrt₀; infer_instance

/-- `tsIchd₀〘T, a, B〙₃` is `T.ichd a B` -/
noncomputable def tsIchd₀ : L.RudimentaryTerm 3 :=
  tsMk ((ᵣ0 : L.RudimentaryTerm 3).tsNd ∪ ᵣ2)
    ((ᵣ0 : L.RudimentaryTerm 3).tsDep ∪
      (ᵣ2 : L.RudimentaryTerm 3) ×ˢ ({((ᵣ0 : L.RudimentaryTerm 3).tsDep ﹫ ᵣ1).succ} :
        L.RudimentaryTerm 3))
    ((ᵣ0 : L.RudimentaryTerm 3).tsChd.update (ᵣ1) (((ᵣ0).tsChd ﹫ ᵣ1) ∪ ᵣ2) ∪
      (ᵣ2 : L.RudimentaryTerm 3) ×ˢ ({∅} : L.RudimentaryTerm 3))

instance : (tsIchd₀ : L.RudimentaryTerm 3).CharFree := by
  unfold tsIchd₀; infer_instance

/-- `tsIsbl₀〘T, a, b〙₃` is `T.isbl a b` -/
noncomputable def tsIsbl₀ : L.RudimentaryTerm 3 :=
  (tsIrt₀.substBoundRud ![ᵣ0, ᵣ2]).ifTrue ((ᵣ1 : L.RudimentaryTerm 3).isMem (ᵣ0).tsRt) ∪
    (tsMk (insert (ᵣ2) (ᵣ0 : L.RudimentaryTerm 3).tsNd)
      ((ᵣ0 : L.RudimentaryTerm 3).tsDep.update (ᵣ2) ((ᵣ0).tsDep ﹫ ᵣ1))
      (((ᵣ0 : L.RudimentaryTerm 3).tsChd.insertVal ((ᵣ0).tsPrt ﹫ ᵣ1) (ᵣ2)).update (ᵣ2) ∅)).ifTrue
      ∼((ᵣ1 : L.RudimentaryTerm 3).isMem (ᵣ0).tsRt)

instance : (tsIsbl₀ : L.RudimentaryTerm 3).CharFree := by
  unfold tsIsbl₀; infer_instance

end RudimentaryTerm

namespace MemStructure

open RudimentaryTerm TreeStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] {n : ℕ}

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsNd (r : L.RudimentaryTerm n)
    (xs : Fin n → M) : r.tsNd〘xs〙 = (ofM r〘xs〙).nd := by
  simp [tsNd, TreeStructure.nd]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsDep (r : L.RudimentaryTerm n)
    (xs : Fin n → M) : r.tsDep〘xs〙 = (ofM r〘xs〙).dep := by
  simp [tsDep, TreeStructure.dep]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsChd (r : L.RudimentaryTerm n)
    (xs : Fin n → M) : r.tsChd〘xs〙 = (ofM r〘xs〙).chd := by
  simp [tsChd, TreeStructure.chd]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsRt₀ (xs : Fin 1 → M) :
    tsRt₀〘xs〙 = (ofM (xs 0)).rt := by
  ext z
  simp [tsRt₀, mem_rt_iff, Fin.snoc_nat]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsPrt₀ (xs : Fin 1 → M) :
    tsPrt₀〘xs〙 = (ofM (xs 0)).prt := by
  ext z
  simp only [tsPrt₀, Fin.isValue, sprod_def, singleton_def, RudimentaryTerm.left,
    RudimentaryTerm.val, RudimentaryTerm.right, mem_realize_iUnion_iff,
    RudimentaryTerm.realize_substBoundRud, realize_sprod₀, Matrix.cons_val_zero, realize_tsNd,
    realize_basic, Matrix.cons_val_one, Matrix.cons_val_fin_one, mem_sprod_iff,
    mem_realize_ifTrue_iff, Fin.snoc_nat, Fin.coe_ofNat_eq_mod, Nat.mod_succ, lt_self_iff_false,
    ↓reduceDIte, realize_singleton₀, mem_singleton_iff, realize_isMem, realize_val₀, realize_tsChd,
    Nat.zero_mod, Order.lt_one_iff, Fin.zero_eta, realize_right₀, realize_left₀, ↓existsAndEq,
    and_true, right_orderedPair, left_orderedPair, mem_prt_iff]
  constructor
  · rintro ⟨u, v, ⟨hu, hv⟩, rfl, h⟩
    exact ⟨⟨u, hu, v, hv, rfl⟩, by simpa using h⟩
  · rintro ⟨⟨u, hu, v, hv, rfl⟩, h⟩
    exact ⟨u, v, ⟨hu, hv⟩, rfl, by simpa using h⟩

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsSbl₀ (xs : Fin 1 → M) :
    tsSbl₀〘xs〙 = (ofM (xs 0)).sbl := by
  simp [tsSbl₀, TreeStructure.sbl, constFun]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsSblptn₀ (xs : Fin 1 → M) :
    tsSblptn₀〘xs〙 = (ofM (xs 0)).sblptn := by
  simp [tsSblptn₀, TreeStructure.sblptn]

theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isTreeStructure₀ [HasOmega M]
    (xs : Fin 1 → M) :
    (isTreeStructure₀ : L.DeltaZeroBoundedFormula 1).toBoundedFormula 〘xs〙 ↔
      (ofM (xs 0)).IsTreeStructure := by
  rw [isTreeStructure_iff]
  simp [isTreeStructure₀, and_assoc, Fin.snoc_nat]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsRt (r : L.RudimentaryTerm n)
    [r.CharFree] (xs : Fin n → M) : r.tsRt〘xs〙 = (ofM r〘xs〙).rt := by
  simp [tsRt]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsPrt (r : L.RudimentaryTerm n)
    [r.CharFree] (xs : Fin n → M) : r.tsPrt〘xs〙 = (ofM r〘xs〙).prt := by
  simp [tsPrt]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsSbl (r : L.RudimentaryTerm n)
    [r.CharFree] (xs : Fin n → M) : r.tsSbl〘xs〙 = (ofM r〘xs〙).sbl := by
  simp [tsSbl]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsSblptn (r : L.RudimentaryTerm n)
    [r.CharFree] (xs : Fin n → M) : r.tsSblptn〘xs〙 = (ofM r〘xs〙).sblptn := by
  simp [tsSblptn]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isTreeStructure [HasOmega M]
    (r : L.RudimentaryTerm n) [r.CharFree] (xs : Fin n → M) :
    r.isTreeStructure.toBoundedFormula 〘xs〙 ↔ (ofM r〘xs〙).IsTreeStructure := by
  rw [isTreeStructure, DeltaZeroBoundedFormula.realize_substBoundRud,
    realize_isTreeStructure₀]
  rfl

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsMk (r s t : L.RudimentaryTerm n)
    (xs : Fin n → M) : (tsMk r s t)〘xs〙 = (TreeStructure.mk r〘xs〙 s〘xs〙 t〘xs〙).toM := by
  simp [tsMk]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsIrt₀ (xs : Fin 2 → M) :
    tsIrt₀〘xs〙 = ((ofM (xs 0)).irt (xs 1)).toM := by
  simp [tsIrt₀, TreeStructure.irt]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsIchd₀ (xs : Fin 3 → M) :
    tsIchd₀〘xs〙 = ((ofM (xs 0)).ichd (xs 1) (xs 2)).toM := by
  simp [tsIchd₀, TreeStructure.ichd, constFun]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_tsIsbl₀ (xs : Fin 3 → M) :
    tsIsbl₀〘xs〙 = ((ofM (xs 0)).isbl (xs 1) (xs 2)).toM := by
  by_cases h : xs 1 ∈ (ofM (xs 0)).rt
  · simp [tsIsbl₀, TreeStructure.isbl_of_mem_rt h, h]
  · ext z
    simp [tsIsbl₀, TreeStructure.isbl_of_not_mem_rt h, h,
      DeltaZeroBoundedFormula.toBoundedFormula_not]

instance : ClassFunction.DeltaZero (fun x : M ↦ (ofM x).nd) Set.univ :=
  ClassFunction.deltaZero_of_eq (ᵣ0 : L.RudimentaryTerm 1).tsNd fun _ ↦ by simp

instance : ClassFunction.DeltaZero (fun x : M ↦ (ofM x).dep) Set.univ :=
  ClassFunction.deltaZero_of_eq (ᵣ0 : L.RudimentaryTerm 1).tsDep fun _ ↦ by simp

instance : ClassFunction.DeltaZero (fun x : M ↦ (ofM x).chd) Set.univ :=
  ClassFunction.deltaZero_of_eq (ᵣ0 : L.RudimentaryTerm 1).tsChd fun _ ↦ by simp

instance : ClassFunction.DeltaZero (fun x : M ↦ (ofM x).rt) Set.univ :=
  ClassFunction.deltaZero_of_eq tsRt₀ fun _ ↦ by simp

instance : ClassFunction.DeltaZero (fun x : M ↦ (ofM x).prt) Set.univ :=
  ClassFunction.deltaZero_of_eq tsPrt₀ fun _ ↦ by simp

instance : ClassFunction.DeltaZero (fun x : M ↦ (ofM x).sbl) Set.univ :=
  ClassFunction.deltaZero_of_eq tsSbl₀ fun _ ↦ by simp

instance : ClassFunction.DeltaZero (fun x : M ↦ (ofM x).sblptn) Set.univ :=
  ClassFunction.deltaZero_of_eq tsSblptn₀ fun _ ↦ by simp

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ ((ofM (ys 0)).irt (ys 1)).toM)
    Set.univ :=
  MulticlassFunction.deltaZero_of_eq tsIrt₀ fun _ ↦ by simp

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 3 → M ↦ ((ofM (ys 0)).ichd (ys 1) (ys 2)).toM) Set.univ :=
  MulticlassFunction.deltaZero_of_eq tsIchd₀ fun _ ↦ by simp

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 3 → M ↦ ((ofM (ys 0)).isbl (ys 1) (ys 2)).toM) Set.univ :=
  MulticlassFunction.deltaZero_of_eq tsIsbl₀ fun _ ↦ by simp

/-- Being a tree structure is `Δ₀` -/
instance [HasOmega M] : Class.DeltaZero (fun x : M ↦ (ofM x).IsTreeStructure) Set.univ := by
  have h : (fun x : M ↦ (ofM x).IsTreeStructure) =
      Multiclass.toClass
        (isTreeStructure₀ : L.DeltaZeroBoundedFormula 1).toBoundedFormula.multiclass := by
    funext x
    rw [Multiclass.toClass_iff, BoundedFormula.multiclass, realize_isTreeStructure₀]
    rfl
  rw [h]
  infer_instance

end MemStructure

end FirstOrder.Language
