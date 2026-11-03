/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Ordinal.Omega
/-!
# Tree structures

In models of `KP`:

* `TreeStructure M` bundles the data `(A, d, C)` of a tree structure: the nodes `T.nd`, the depth
  function `T.dep` and the children function `T.chd`;
* `T.IsTreeStructure`: `d !: A → ω`, `C` is a function on `A` with `C ﹫ a ⊆ A`, children are
  one level deeper, and every node of positive depth is a child of a unique node;
* `T.rt`: the roots, the nodes of depth `∅`;
* `T.prt`: the parent function on `A \ T.rt`, `T.prt ﹫ b = a ↔ b ∈ C ﹫ a`;
* `T.sbl`: the sibling function on `A`, `C ﹫ (T.prt ﹫ a)` for `a ∉ T.rt` and `T.rt` for
  `a ∈ T.rt`;
* `T.sblptn`: the sibling partition `({T.rt} ∪ ran C) \ {∅}`.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M]

/-- `d ﹫ a = ∅` is `Δ₀` -/
instance (d : M) : Class.DeltaZero (fun a : M ↦ d ﹫ a = ∅) Set.univ := by
  let φ : L.DeltaZeroBoundedFormula 2 := (&0 =₀ &1).substBoundRud ![(ᵣ1) ﹫ (ᵣ0), ∅]
  have h : (fun ys : Fin 1 → M ↦ d ﹫ ys 0 = ∅) =
      φ.toBoundedFormula.multiclass.slice ![d] := by
    funext ys
    simp only [Fin.isValue, Multiclass.slice, BoundedFormula.multiclass, Nat.succ_eq_add_one,
      Nat.reduceAdd, Function.comp_apply, RudimentaryTerm.val,
      DeltaZeroBoundedFormula.realize_substBoundRud, DeltaZeroBoundedFormula.toBoundedFormula,
      BoundedFormula.realize'_bdEqual, Term.realize'_var', Matrix.cons_val_zero,
      RudimentaryTerm.realize_substBoundRud, RudimentaryTerm.realize_val₀,
      RudimentaryTerm.realize_basic, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      RudimentaryTerm.realize_empty, eq_iff_iff, φ]
    rfl
  have : Multiclass.DeltaZero (fun ys : Fin 1 → M ↦ d ﹫ ys 0 = ∅) Set.univ :=
    h ▸ inferInstance
  infer_instance

/-- `left p ∈ C ﹫ right p` is `Δ₀` -/
instance (C : M) : Class.DeltaZero (fun p : M ↦ left p ∈ C ﹫ right p) Set.univ := by
  let φ : L.DeltaZeroBoundedFormula 2 :=
    (&0 ∈₀ &1).substBoundRud ![(ᵣ0).left, (ᵣ1) ﹫ (ᵣ0).right]
  have h : (fun ys : Fin 1 → M ↦ left (ys 0) ∈ C ﹫ right (ys 0)) =
      φ.toBoundedFormula.multiclass.slice ![C] := by
    funext ys
    simp only [φ, Multiclass.slice, BoundedFormula.multiclass, eq_iff_iff]
    rw [DeltaZeroBoundedFormula.realize_substBoundRud]
    simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd,
      DeltaZeroBoundedFormula.toBoundedFormula, Function.comp_apply, RudimentaryTerm.left,
      RudimentaryTerm.val, RudimentaryTerm.right, realize'_mem, Term.realize'_var',
      Matrix.cons_val_one, Matrix.cons_val_fin_one, RudimentaryTerm.realize_substBoundRud,
      RudimentaryTerm.realize_val₀, Matrix.cons_val_zero, RudimentaryTerm.realize_basic,
      RudimentaryTerm.realize_right₀, RudimentaryTerm.realize_left₀]
    rfl
  have : Multiclass.DeltaZero (fun ys : Fin 1 → M ↦ left (ys 0) ∈ C ﹫ right (ys 0))
      Set.univ :=
    h ▸ inferInstance
  infer_instance

/-- The data `(A, d, C)` of a tree structure: the nodes `A`, the depth function `d` and the
children function `C` -/
@[ext]
structure TreeStructure (M : Type*) where
  /-- The set of nodes -/
  nd : M
  /-- The depth function -/
  dep : M
  /-- The children function -/
  chd : M

namespace TreeStructure

variable (T : TreeStructure M)

/-- `T = (A, d, C)` is a tree structure -/
structure IsTreeStructure : Prop where
  dep_fromTo : T.dep !: T.nd → (ω : M)
  isFunction_chd : IsFunction T.chd
  dom_chd : dom T.chd = T.nd
  chd_subset : ∀ a ∈ T.nd, T.chd ﹫ a ⊆ T.nd
  dep_of_mem_chd : ∀ a ∈ T.nd, ∀ b ∈ T.chd ﹫ a, T.dep ﹫ b = succ (T.dep ﹫ a)
  existsUnique_prt : ∀ b ∈ T.nd, ∅ <ₒ T.dep ﹫ b → ∃! a, b ∈ T.chd ﹫ a

/-- The empty tree structure `(∅, ∅, ∅)` -/
noncomputable instance : EmptyCollection (TreeStructure M) := ⟨⟨∅, ∅, ∅⟩⟩

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
@[simp]
theorem nd_empty : (∅ : TreeStructure M).nd = ∅ := rfl

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
@[simp]
theorem dep_empty : (∅ : TreeStructure M).dep = ∅ := rfl

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
@[simp]
theorem chd_empty : (∅ : TreeStructure M).chd = ∅ := rfl

/-- The empty tree structure is a tree structure -/
theorem isTreeStructure_empty : (∅ : TreeStructure M).IsTreeStructure where
  dep_fromTo := isFunctionFromTo_empty ω
  isFunction_chd := isFunction_empty
  dom_chd := dom_empty
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
  ⟨insert b T.nd, update T.dep b ∅, update T.chd b ∅⟩

/-- `T` with new children `B` of `a`:
`(A ∪ B, d ∪ (B × {d(a) + 1}), C_mVal(a, C(a) ∪ B) ∪ (B × {∅}))` -/
noncomputable def ichd (a B : M) : TreeStructure M :=
  ⟨T.nd ∪ B, T.dep ∪ constFun B (succ (T.dep ﹫ a)),
    update T.chd a (T.chd ﹫ a ∪ B) ∪ constFun B ∅⟩

/-- `T` with a new child `b` of `a`: `T.ichd a {b}` -/
noncomputable def ionechd (a b : M) : TreeStructure M := T.ichd a {b}

noncomputable instance (a : M) : Decidable (a ∈ T.rt) := Classical.propDecidable _

/-- `T` with a new sibling `b` of `a`: `T.irt b` if `a` is a root, and otherwise
`(A ∪ {b}, d_ins(b, d(a)), C_iToVal(T.prt(a), b)_ins(b, ∅))` -/
noncomputable def isbl (a b : M) : TreeStructure M :=
  if a ∈ T.rt then T.irt b
  else ⟨insert b T.nd, update T.dep b (T.dep ﹫ a),
    update (insertVal T.chd (T.prt ﹫ a) b) b ∅⟩

variable {T} {a b c e p s B : M}

omit [ModelsKP M] in
@[simp]
theorem nd_irt : (T.irt b).nd = insert b T.nd := rfl

omit [ModelsKP M] in
@[simp]
theorem dep_irt : (T.irt b).dep = update T.dep b ∅ := rfl

omit [ModelsKP M] in
@[simp]
theorem chd_irt : (T.irt b).chd = update T.chd b ∅ := rfl

omit [ModelsKP M] in
@[simp]
theorem nd_ichd : (T.ichd a B).nd = T.nd ∪ B := rfl

omit [ModelsKP M] in
@[simp]
theorem dep_ichd : (T.ichd a B).dep = T.dep ∪ constFun B (succ (T.dep ﹫ a)) := rfl

omit [ModelsKP M] in
@[simp]
theorem chd_ichd : (T.ichd a B).chd = update T.chd a (T.chd ﹫ a ∪ B) ∪ constFun B ∅ := rfl

omit [ModelsKP M] in
theorem isbl_of_mem_rt (ha : a ∈ T.rt) : T.isbl a b = T.irt b := if_pos ha

omit [ModelsKP M] in
theorem isbl_of_not_mem_rt (ha : a ∉ T.rt) :
    T.isbl a b =
      ⟨insert b T.nd, update T.dep b (T.dep ﹫ a),
        update (insertVal T.chd (T.prt ﹫ a) b) b ∅⟩ :=
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
  exact TreeStructure.ext hA hdep.eq_empty_of_dom_empty hchd.eq_empty_of_dom_empty

/-- A nonempty tree structure has a node -/
theorem nd_ne_empty (hne : T ≠ ∅) : T.nd ≠ ∅ :=
  fun hA ↦ hne (hT.eq_empty_of_nd_eq_empty hA)

theorem dep_irt_val_self : (T.irt b).dep ﹫ b = ∅ :=
  val_update_self hT.dep_fromTo.isFunction b ∅

theorem dep_irt_val_of_mem (hb : b ∉ T.nd) (ha : a ∈ T.nd) :
    (T.irt b).dep ﹫ a = T.dep ﹫ a :=
  val_update_of_ne hT.dep_fromTo.isFunction ∅ (by rwa [hT.dep_fromTo.dom_eq]) (by grind)

theorem chd_irt_val_self : (T.irt b).chd ﹫ b = ∅ :=
  val_update_self hT.isFunction_chd b ∅

theorem chd_irt_val_of_mem (hb : b ∉ T.nd) (ha : a ∈ T.nd) :
    (T.irt b).chd ﹫ a = T.chd ﹫ a :=
  val_update_of_ne hT.isFunction_chd ∅ (by rwa [hT.dom_chd]) (by grind)

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

theorem isFunction_dep_ichd (hB : B ∩ T.nd = ∅) : IsFunction (T.ichd a B).dep :=
  hT.dep_fromTo.isFunction.union_of_disjoint (isFunction_constFun B (succ (T.dep ﹫ a)))
    (hT.disjoint_dep_ichd hB (succ (T.dep ﹫ a)))

theorem dom_dep_ichd : dom (T.ichd a B).dep = T.nd ∪ B := by
  simp [dom_union, hT.dep_fromTo.dom_eq]

theorem dep_ichd_val_of_mem_nd (hB : B ∩ T.nd = ∅) (hc : c ∈ T.nd) :
    (T.ichd a B).dep ﹫ c = T.dep ﹫ c :=
  val_union_left hT.dep_fromTo.isFunction (isFunction_constFun B (succ (T.dep ﹫ a)))
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
    IsFunction (T.ichd a B).chd :=
  (hT.isFunction_chd.update a (T.chd ﹫ a ∪ B)).union_of_disjoint (isFunction_constFun B ∅)
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
  dep_fromTo := by
    refine isFunctionFromTo_of_val (hT.dep_fromTo.isFunction.update b ∅) ?_ fun a ha ↦ ?_
    · simp [hT.dep_fromTo.dom_eq]
    rw [nd_irt, mem_insert_iff] at ha
    rcases ha with rfl | ha
    · rw [hT.dep_irt_val_self]
      exact empty_mem_omega
    rw [hT.dep_irt_val_of_mem hb ha]
    exact hT.dep_mem_omega ha
  isFunction_chd := hT.isFunction_chd.update b ∅
  dom_chd := hT.dom_chd_irt
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
  dep_fromTo := by
    refine isFunctionFromTo_of_val (hT.isFunction_dep_ichd hB) hT.dom_dep_ichd fun c hc ↦ ?_
    rw [nd_ichd, mem_union_iff] at hc
    rcases hc with hc | hc
    · rw [hT.dep_ichd_val_of_mem_nd hB hc]
      exact hT.dep_mem_omega hc
    rw [hT.dep_ichd_val_of_mem_new hB hc]
    exact succ_mem_omega (hT.dep_mem_omega ha)
  isFunction_chd := hT.isFunction_chd_ichd ha hB
  dom_chd := hT.dom_chd_ichd ha
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
  rw [isbl_of_not_mem_rt ha.right, TreeStructure.ionechd]
  refine TreeStructure.ext ?_ ?_ ?_
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

end IsTreeStructure

end TreeStructure

end FirstOrder.Language.MemStructure
