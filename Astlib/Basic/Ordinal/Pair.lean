/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Ordinal.Mul
import Astlib.Basic.Order.Pullback
/-!
# Gödel's pairing function on ordinals

Gödel's well-order on pairs of ordinals compares the maxima first and then the pairs
lexicographically (`GoedelLT`). On `μ ×ˢ μ` it is the strict well-order `goedelRel μ`.

Gödel's pairing function `goedelPair` is given by the primitive recursive term `goedelPair₀`.
For ordinals, `goedelPair α β` is the position of `!(α, β)` in Gödel's order: the value of the
Mostowski collapse of `goedelRel μ` at `!(α, β)`, for any ordinal `μ` above `α` and `β`
(`goedelPair_eq_collapseOn`). So `goedelPair` is an order isomorphism from Gödel's order onto the
ordinals: it maps pairs of ordinals to ordinals (`ordinal_goedelPair`), turns Gödel's order into
`<ₒ` (`goedelPair_olt_goedelPair_iff`), is injective (`goedelPair_inj`) and every ordinal is a
value (`exists_goedelPair_eq`).

Iterating it gives the primitive recursive code `iteratedGoedelPair t n` of the first `n` values
of a sequence `t` of ordinals. On the sequences in `ω` of a nonzero length `n ∈ ω` it takes values
in `ω` (`iteratedGoedelPair_mem_omega`), is injective (`iteratedGoedelPair_inj`) and every
element of `ω` is a value (`exists_iteratedGoedelPair_eq`).
-/

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin RudimentaryTerm MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] {α β γ δ μ ν x : M}

/-- Gödel's order on pairs of ordinals: `!(γ, δ)` precedes `!(α, β)` if
`omax₂ γ δ <ₒ omax₂ α β`, or the maxima agree and `!(γ, δ)` precedes `!(α, β)`
lexicographically -/
def GoedelLT (γ δ α β : M) : Prop :=
  omax₂ γ δ <ₒ omax₂ α β ∨ (omax₂ γ δ = omax₂ α β ∧ (γ <ₒ α ∨ (γ = α ∧ δ <ₒ β)))

/-- `p ↦ omax₂ (left p) (right p)`, the maximum of a pair of ordinals -/
noncomputable def maxOfPair : ClassFunction M := fun p ↦ omax₂ (left p) (right p)

@[simp]
theorem maxOfPair_orderedPair (α β : M) : maxOfPair !(α, β) = omax₂ α β := by
  simp [maxOfPair]

instance : (maxOfPair : ClassFunction M).Sigma 1 Set.univ := by
  unfold maxOfPair
  infer_instance

/-- `p ↦ !(omax₂ (left p) (right p), p)` -/
noncomputable def maxPair : ClassFunction M := fun p ↦ !(omax₂ (left p) (right p), p)

instance : (maxPair : ClassFunction M).Sigma 1 Set.univ := by
  unfold maxPair
  infer_instance

/-- Gödel's well-order on `μ ×ˢ μ`: the pullback of the lexicographic order on
`μ ×ˢ (μ ×ˢ μ)` along `p ↦ !(omax₂ (left p) (right p), p)` -/
noncomputable def goedelRel (μ : M) : M :=
  pullback (maxPair ↾₀ (μ ×ˢ μ))
    (lexProd (memRelOn μ) μ (lexProd (memRelOn μ) μ (memRelOn μ) μ) (μ ×ˢ μ)) (μ ×ˢ μ)

theorem isRelationOn_goedelRel (μ : M) : IsRelationOn (goedelRel μ) (μ ×ˢ μ) :=
  isRelationOn_pullback

theorem rel_goedelRel_iff (hμ : Ordinal μ) :
    !(γ, δ) [goedelRel μ] !(α, β) ↔
      (γ <ₒ μ ∧ δ <ₒ μ) ∧ (α <ₒ μ ∧ β <ₒ μ) ∧ GoedelLT γ δ α β := by
  have hres : IsSetRestrictedTo maxPair (μ ×ˢ μ) :=
    isSetRestrictedTo_of_sigma (G := maxPair) (μ ×ˢ μ)
  simp only [goedelRel, rel_pullback_iff, pair_mem_sprod_iff, olt_iff_mem', hμ, and_assoc]
  refine and_congr_right fun hγ ↦ and_congr_right fun hδ ↦ and_congr_right fun hα ↦
    and_congr_right fun hβ ↦ ?_
  have hγo : Ordinal γ := by grind
  have hδo : Ordinal δ := by grind
  have hαo : Ordinal α := by grind
  have hβo : Ordinal β := by grind
  rw [val_toSetRestrictedTo hres (mem_sprod _ _ _ _ hγ hδ),
    val_toSetRestrictedTo hres (mem_sprod _ _ _ _ hα hβ)]
  simp only [maxPair, left_orderedPair, right_orderedPair, rel_lexProd_iff, rel_memRelOn_iff,
    GoedelLT, olt_iff_mem, ordinal_omax₂, hγo, hδo, hαo, hβo]
  grind

/-- Gödel's order is a strict well-order on `μ ×ˢ μ` -/
theorem isStrictWellOrder_goedelRel (hμ : Ordinal μ) :
    IsStrictWellOrder (goedelRel μ) (μ ×ˢ μ) := by
  have hwo : IsStrictWellOrder (memRelOn μ) μ :=
    isStrictWellOrder_memRelOn fun x hx ↦ ordinal_of_mem hμ hx
  have hres : IsSetRestrictedTo maxPair (μ ×ˢ μ) :=
    isSetRestrictedTo_of_sigma (G := maxPair) (μ ×ˢ μ)
  refine (hwo.lexProd (hwo.lexProd hwo)).pullback
    (isInjectionFromTo_toSetRestrictedTo hres (fun z hz ↦ ?_) fun z _ z' _ h ↦ ?_)
  · simp only [mem_sprod_iff] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    simpa [maxPair] using mem_sprod _ _ _ _ (union_mem_of_mem hμ ha hb) (mem_sprod _ _ _ _ ha hb)
  · simp only [maxPair, orderedPair_eq_orderedPair_iff] at h
    exact h.right

/-- `p ↦ (μ *ₒ μ) *ₒ omax₂ (left p) (right p) +ₒ (μ *ₒ left p +ₒ right p)`, an embedding of
Gödel's order on `μ ×ˢ μ` into `∈` -/
noncomputable def goedelEmb (μ : M) : ClassFunction M :=
  fun p ↦ (μ *ₒ μ) *ₒ maxOfPair p +ₒ omulPair μ p

instance (μ : M) : (goedelEmb μ).Sigma 1 Set.univ := by
  unfold goedelEmb
  infer_instance

/-- Gödel's order on `μ ×ˢ μ` is well-founded, also for definable classes -/
theorem isStrictWellFounded₀_goedelRel (hμ : Ordinal μ) :
    IsStrictWellFounded₀ (goedelRel μ) (μ ×ˢ μ) := by
  refine isStrictWellFounded₀_of_mem (F := goedelEmb μ) (isRelationOn_goedelRel μ)
    fun p hp q hq hqp ↦ ?_
  simp only [mem_sprod_iff] at hp hq
  obtain ⟨α, hα, β, hβ, rfl⟩ := hp
  obtain ⟨γ, hγ, δ, hδ, rfl⟩ := hq
  simp only [rel_goedelRel_iff, hμ] at hqp
  obtain ⟨⟨hγμ, hδμ⟩, ⟨hαμ, hβμ⟩, hlt⟩ := hqp
  simp only [goedelEmb, maxOfPair_orderedPair, omulPair_orderedPair]
  refine (omul_oadd_olt_omul_oadd (ordinal_omul hμ hμ) (ordinal_omax₂ hαμ.ordinal_left
    hβμ.ordinal_left) (omul_oadd_olt_omul hμ hαμ hβμ) (omul_oadd_olt_omul hμ hγμ hδμ) ?_).mem
  rcases hlt with h | ⟨h, h'⟩
  · exact .inl h
  · grind [omul_oadd_olt_omul_oadd]

/-- Gödel's order on `μ ×ˢ μ` is a strict well-order, also well-founded for definable classes -/
theorem isStrictWellOrder₀_goedelRel (hμ : Ordinal μ) :
    IsStrictWellOrder₀ (goedelRel μ) (μ ×ˢ μ) :=
  ⟨isStrictWellOrder_goedelRel hμ, (isStrictWellFounded₀_goedelRel hμ).isStrictWellFounded₀_ofRel⟩

/-- The predecessors of a pair in `μ ×ˢ μ` are the same for Gödel's order on `ν ×ˢ ν` for
`μ ≤ₒ ν` -/
theorem predSet_goedelRel (hμν : μ ≤ₒ ν) (x : M) (hx : x ∈ μ ×ˢ μ) :
    predSet (goedelRel μ) x = predSet (goedelRel ν) x := by
  have hμ : Ordinal μ := by grind
  have hν : Ordinal ν := by grind
  simp only [mem_sprod_iff] at hx
  obtain ⟨α, hα, β, hβ, rfl⟩ := hx
  ext y
  simp only [mem_predSet_iff]
  constructor
  · intro h
    have hm : y ∈ μ ×ˢ μ := (isRelationOn_goedelRel μ).mem_left h
    simp only [mem_sprod_iff] at hm
    obtain ⟨γ, -, δ, -, rfl⟩ := hm
    simp only [rel_goedelRel_iff, hμ, hν] at h ⊢
    obtain ⟨⟨hγ, hδ⟩, -, hlt⟩ := h
    exact ⟨⟨olt_of_olt_of_ole hγ hμν, olt_of_olt_of_ole hδ hμν⟩, ⟨by grind, by grind⟩, hlt⟩
  · intro h
    have hm : y ∈ ν ×ˢ ν := (isRelationOn_goedelRel ν).mem_left h
    simp only [mem_sprod_iff] at hm
    obtain ⟨γ, -, δ, -, rfl⟩ := hm
    simp only [rel_goedelRel_iff, hμ, hν] at h ⊢
    obtain ⟨⟨hγ, hδ⟩, -, hlt⟩ := h
    have hunion : omax₂ γ δ ≤ₒ omax₂ α β := by
      grind [GoedelLT]
    have hγδ : omax₂ γ δ <ₒ μ := by grind
    simp only [omax₂_olt_iff, hγ.ordinal_left, hδ.ordinal_left] at hγδ
    exact ⟨hγδ, ⟨by grind, by grind⟩, hlt⟩

theorem orderedPair_mem_succ_omax₂_sprod (hα : Ordinal α) (hβ : Ordinal β) :
    !(α, β) ∈ succ (omax₂ α β) ×ˢ succ (omax₂ α β) := by
  grind

/-- The collapse of Gödel's order on `μ ×ˢ μ` turns it into `∈` -/
theorem collapseOn_goedelRel_mem_iff (hα : α <ₒ μ) (hβ : β <ₒ μ) (hγ : γ <ₒ μ) (hδ : δ <ₒ μ) :
    collapseOn (goedelRel μ) (μ ×ˢ μ) ﹫ !(γ, δ) ∈ collapseOn (goedelRel μ) (μ ×ˢ μ) ﹫ !(α, β) ↔
      GoedelLT γ δ α β := by
  have hμ : Ordinal μ := by grind
  rw [← (isStrictWellOrder₀_goedelRel hμ).rel_iff_collapseOn_mem_collapseOn
    (mem_sprod _ _ _ _ hα.mem hβ.mem) (mem_sprod _ _ _ _ hγ.mem hδ.mem), rel_goedelRel_iff hμ]
  simp [hα, hβ, hγ, hδ]

/-- The collapse of Gödel's order on `μ ×ˢ μ` is injective -/
theorem collapseOn_goedelRel_inj (hα : α <ₒ μ) (hβ : β <ₒ μ) (hγ : γ <ₒ μ) (hδ : δ <ₒ μ) :
    collapseOn (goedelRel μ) (μ ×ˢ μ) ﹫ !(γ, δ) = collapseOn (goedelRel μ) (μ ×ˢ μ) ﹫ !(α, β) ↔
      γ = α ∧ δ = β := by
  have hμ : Ordinal μ := by grind
  rw [(isStrictWellFounded₀_goedelRel hμ).collapseOn_injOn
    (isStrictWellOrder_goedelRel hμ).isExtensionalOn (mem_sprod _ _ _ _ hγ.mem hδ.mem)
    (mem_sprod _ _ _ _ hα.mem hβ.mem), orderedPair_eq_orderedPair_iff]

end FirstOrder.Language.MemStructure

namespace FirstOrder.Language

open PrimitiveRecursiveTerm

/-- The step `f ↦ ⋃_{ν ∈ dom f} f ﹫ ν +ₒ (ν +ₒ succ ν)` of `goedelBase₀` -/
noncomputable def PrimitiveRecursiveTerm.goedelBaseStep₀ {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.PrimitiveRecursiveTerm 1 :=
  PrimitiveRecursiveTerm.iUnion (ᵣ0 : L.RudimentaryTerm 1).dom.toPrimitiveRecursiveTerm
    (oadd₀.substBoundPR ![((ᵣ0 : L.RudimentaryTerm 2) ﹫ ᵣ1).toPrimitiveRecursiveTerm,
      oadd₀.substBoundPR ![ₚᵣ1, (ᵣ1 : L.RudimentaryTerm 2).succ.toPrimitiveRecursiveTerm] ])

/-- `g(μ) = ⋃_{ν ∈ μ} g(ν) +ₒ (ν +ₒ succ ν)`, the number of pairs of ordinals whose maximum lies
below `μ` -/
noncomputable def PrimitiveRecursiveTerm.goedelBase₀ {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.PrimitiveRecursiveTerm 1 :=
  ordRecursion goedelBaseStep₀

/-- Gödel's pairing function as a primitive recursive term:
`g(omax₂ α β) +ₒ α` if `α <ₒ β`, and `g(omax₂ α β) +ₒ (α +ₒ β)` otherwise -/
noncomputable def PrimitiveRecursiveTerm.goedelPair₀ {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.PrimitiveRecursiveTerm 2 :=
  oadd₀.substBoundPR
    ![goedelBase₀.substBoundPR ![(ᵣ0 ∪ ᵣ1 : L.RudimentaryTerm 2).toPrimitiveRecursiveTerm],
      (ₚᵣ0).ifTrue (&0 ∈₀ &1) ∪ oadd₀.ifTrue (&0 =₀ &1 ⊔ &1 ∈₀ &0)]

/-- The step of `iteratedGoedelPair₀`: `(t, ν, c) ↦ t ﹫ ν` if `ν = ∅`, and `goedelPair c (t ﹫ ν)`
otherwise -/
noncomputable def PrimitiveRecursiveTerm.iteratedGoedelPairStep₀ {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.PrimitiveRecursiveTerm 3 :=
  (ᵣ0 ﹫ ᵣ1 : L.RudimentaryTerm 3).toPrimitiveRecursiveTerm.ifTrue (ᵣ1).isZero ∪
    (goedelPair₀.substBoundPR
      ![ₚᵣ2, (ᵣ0 ﹫ ᵣ1 : L.RudimentaryTerm 3).toPrimitiveRecursiveTerm]).ifTrue
      ∼(ᵣ1).isZero

/-- The code of the first `ν` values of a sequence `t` of ordinals, by recursion on `ν`:
`t ﹫ ∅` at `1`, and Gödel's pairing of the code at `ν` with `t ﹫ ν` at `succ ν` for `ν ≠ ∅` -/
noncomputable def PrimitiveRecursiveTerm.iteratedGoedelPair₀ {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.PrimitiveRecursiveTerm 2 :=
  ordRecursion' (∅ : L.RudimentaryTerm 1).toPrimitiveRecursiveTerm iteratedGoedelPairStep₀
    (∅ : L.RudimentaryTerm 2).toPrimitiveRecursiveTerm

namespace MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] {α β γ δ μ ν z : M}

theorem mem_goedelBaseStep₀_iff (f : M) :
    z ∈ goedelBaseStep₀〘f〙₁ ↔ ∃ ν ∈ dom f, z ∈ f ﹫ ν +ₒ (ν +ₒ succ ν) := by
  simp [goedelBaseStep₀, PrimitiveRecursiveTerm.mem_realize_iUnion_iff]

/-- `goedelBase μ`: the number of pairs of ordinals whose maximum lies below `μ` -/
noncomputable def goedelBase : ClassFunction M := fun μ ↦ goedelBase₀〘μ〙₁

omit [ModelsKP M] in
@[simp]
theorem _root_.FirstOrder.Language.PrimitiveRecursiveTerm.realize_goedelBase₀ (xs : Fin 1 → M) :
    goedelBase₀〘xs〙 = goedelBase (xs 0) := by
  tauto

instance : (goedelBase : ClassFunction M).Sigma 1 Set.univ := by
  unfold goedelBase
  infer_instance

theorem mem_goedelBase_iff (hμ : Ordinal μ) :
    z ∈ goedelBase μ ↔ ∃ ν <ₒ μ, z ∈ goedelBase ν +ₒ (ν +ₒ succ ν) := by
  have hres : IsSetRestrictedTo goedelBase μ := isSetRestrictedTo_of_modelsKP _ μ
  rw [goedelBase, ← Matrix.Fin.snoc_vecEmpty, goedelBase₀, realize_ordRecursion_of_ordinal _ _ hμ,
    Matrix.Fin.snoc_vecEmpty, mem_goedelBaseStep₀_iff]
  simp only [Matrix.Fin.snoc_vecEmpty, ← goedelBase₀.eq_1, ← goedelBase.eq_1, dom_toSetRestrictedTo,
    hres, olt_iff_mem', hμ]
  exact exists_congr fun ν ↦ and_congr_right fun hν ↦ by rw [val_toSetRestrictedTo hres hν]

/-- Gödel's pairing function given by the primitive recursive term `goedelPair₀` -/
noncomputable def goedelPair (α β : M) : M := goedelPair₀〘α, β〙₂

omit [ModelsKP M] in
@[simp]
theorem _root_.FirstOrder.Language.PrimitiveRecursiveTerm.realize_goedelPair₀ (xs : Fin 2 → M) :
    goedelPair₀〘xs〙 = goedelPair (xs 0) (xs 1) := by
  rw [goedelPair, Matrix.vec_fin_two_eq]

/-- `fun ys ↦ goedelPair (ys 0) (ys 1)` is a `Σ₁` term -/
instance : MulticlassFunction.Sigma (fun ys : Fin 2 → M ↦ goedelPair (ys 0) (ys 1)) 1 Set.univ := by
  rw [← funext realize_goedelPair₀]
  infer_instance

/-- `κ` is closed under Gödel's pairing function -/
def GoedelPairClosed : Class M := fun κ ↦ ∀ β ∈ κ, ∀ γ ∈ κ, goedelPair β γ ∈ κ

instance : (GoedelPairClosed : Class M).Sigma 1 Set.univ := by
  unfold GoedelPairClosed
  infer_instance

theorem goedelPair_eq_of_olt (h : α <ₒ β) :
    goedelPair α β = goedelBase (omax₂ α β) +ₒ α := by
  simp [goedelPair, goedelPair₀, h.mem, notMem_of_mem h.mem, ne_of_mem h.mem]

theorem goedelPair_eq_of_ole (h : β ≤ₒ α) :
    goedelPair α β = goedelBase (omax₂ α β) +ₒ (α +ₒ β) := by
  obtain ⟨-, -, h | rfl⟩ := h
  · simp [goedelPair, goedelPair₀, h, notMem_of_mem h]
  · simp [goedelPair, goedelPair₀, notMem_self]

theorem ordinal_goedelBase (hμ : Ordinal μ) : Ordinal (goedelBase μ) := by
  have hA (μ : M) : ((Ordinal.subst (ClassFunction.toMulticlassFunction goedelBase) :
      Multiclass M 1) : Class M) μ ↔ Ordinal (goedelBase μ) := .rfl
  suffices h : ((Ordinal.subst (ClassFunction.toMulticlassFunction goedelBase) :
      Multiclass M 1) : Class M) μ by
    rwa [hA] at h
  refine ordinal_induction (fun μ hμ ih ↦ ?_) hμ
  simp only [hA] at ih ⊢
  have hord {ν : M} (hν : ν <ₒ μ) : Ordinal (goedelBase ν +ₒ (ν +ₒ succ ν)) :=
    ordinal_oadd (ih ν hν) (ordinal_oadd hν.ordinal_left (ordinal_succ hν.ordinal_left))
  refine ⟨fun z hz w hw ↦ ?_, fun x hx y hy ↦ ?_⟩
  · simp only [mem_goedelBase_iff, hμ] at hz ⊢
    obtain ⟨ν, hν, hz⟩ := hz
    exact ⟨ν, hν, (by grind)⟩
  · simp only [mem_goedelBase_iff, hμ] at hx hy
    obtain ⟨ν, hν, hx⟩ := hx
    obtain ⟨ν', hν', hy⟩ := hy
    grind

/-- The elements of `goedelBase μ` are the values `goedelPair γ δ` for `γ, δ <ₒ μ` -/
theorem mem_goedelBase_iff' (hμ : Ordinal μ) :
    z ∈ goedelBase μ ↔ ∃ γ <ₒ μ, ∃ δ <ₒ μ, z = goedelPair γ δ := by
  -- `p〘μ〙 = ⋃_{γ ∈ μ} ⋃_{δ ∈ μ} {goedelPair γ δ}`
  let p : L.PrimitiveRecursiveTerm 1 := PrimitiveRecursiveTerm.iUnion (ₚᵣ0)
    (PrimitiveRecursiveTerm.iUnion (ₚᵣ0) {goedelPair₀.substBoundBound ![1, 2]})
  have hp {μ z : M} (hμ : Ordinal μ) :
      z ∈ (p〘μ〙₁ : M) ↔ ∃ γ <ₒ μ, ∃ δ <ₒ μ, z = goedelPair γ δ := by
    simp [p, Matrix.Fin.snoc_vecEmpty, Matrix.Fin.snoc_vecCons, olt_iff_mem' hμ]
  rw [ordinal_induction_eq (F := goedelBase) (G := fun μ ↦ (p〘μ〙₁ : M))
    (fun μ hμ ih ↦ ?_) hμ, hp hμ]
  have ih' {ν : M} (hν : ν <ₒ μ) (z : M) :
      z ∈ goedelBase ν ↔ ∃ γ <ₒ ν, ∃ δ <ₒ ν, z = goedelPair γ δ := by
    rw [ih ν hν, hp hν.ordinal_left]
  ext z
  simp only [mem_goedelBase_iff, hμ, hp]
  constructor
  · rintro ⟨ν, hν, hz⟩
    have hνo : Ordinal ν := by grind
    simp only [mem_oadd_iff, ordinal_goedelBase, hνo, ordinal_oadd, ordinal_succ hνo] at hz
    rcases hz with hz | ⟨o, ho | ⟨δ, hδ, rfl⟩, rfl⟩
    · rw [ih' hν] at hz
      obtain ⟨γ, hγ, δ, hδ, rfl⟩ := hz
      exact ⟨γ, olt_trans hγ hν, δ, olt_trans hδ hν, rfl⟩
    · exact ⟨o, by grind, ν, hν, by grind [goedelPair_eq_of_olt]⟩
    · have hδν : δ ≤ₒ ν := by
        grind
      refine ⟨ν, hν, δ, olt_of_ole_of_olt hδν hν, ?_⟩
      rw [goedelPair_eq_of_ole hδν, omax₂_eq_left hδν]
  · rintro ⟨γ, hγ, δ, hδ, rfl⟩
    have hγo : Ordinal γ := by grind
    have hδo : Ordinal δ := by grind
    rcases olt_or_ole hγo hδo with h | hδγ
    · refine ⟨δ, hδ, ?_⟩
      rw [goedelPair_eq_of_olt h, omax₂_eq_right h.ole,
        mem_oadd_iff (ordinal_goedelBase hδo) (ordinal_oadd hδo (ordinal_succ hδo))]
      exact .inr ⟨γ, by simp [mem_oadd_iff hδo (ordinal_succ hδo), h.mem], rfl⟩
    · refine ⟨γ, hγ, ?_⟩
      rw [goedelPair_eq_of_ole hδγ, omax₂_eq_left hδγ,
        mem_oadd_iff (ordinal_goedelBase hγo) (ordinal_oadd hγo (ordinal_succ hγo))]
      refine .inr ⟨γ +ₒ δ, ?_, rfl⟩
      simp only [mem_oadd_iff, hγo, ordinal_succ]
      refine .inr ⟨δ, ?_, rfl⟩
      rw [← olt_iff_mem hδo (ordinal_succ hγo), olt_succ_iff hγo]
      exact hδγ

/-- The elements of `goedelPair α β` are the values `goedelPair γ δ` for the pairs `!(γ, δ)` below
`!(α, β)` in Gödel's order -/
theorem mem_goedelPair_iff (hα : α <ₒ μ) (hβ : β <ₒ μ) :
    z ∈ goedelPair α β ↔ ∃ γ <ₒ μ, ∃ δ <ₒ μ, GoedelLT γ δ α β ∧ z = goedelPair γ δ := by
  have hαo : Ordinal α := by grind
  have hβo : Ordinal β := by grind
  -- `goedelBase (omax₂ α β)` and the pairs below `!(α, β)` with the same maximum
  suffices z ∈ goedelPair α β ↔ z ∈ goedelBase (omax₂ α β) ∨ ∃ γ <ₒ μ, ∃ δ <ₒ μ,
      (omax₂ γ δ = omax₂ α β ∧ (γ <ₒ α ∨ (γ = α ∧ δ <ₒ β))) ∧ z = goedelPair γ δ by
    -- the pairs with a smaller maximum
    rw [this, mem_goedelBase_iff' (by grind)]
    simp only [GoedelLT]
    constructor
    · rintro (⟨γ, hγ, δ, hδ, rfl⟩ | ⟨γ, hγ, δ, hδ, hlt, rfl⟩) <;> grind
    · grind
  rcases olt_or_ole hαo hβo with h | hle
  · rw [goedelPair_eq_of_olt h, mem_oadd_iff (ordinal_goedelBase (by grind)) hαo]
    refine or_congr_right ⟨?_, ?_⟩
    · rintro ⟨o, ho, rfl⟩
      exact ⟨o, by grind, β, hβ, by grind [goedelPair_eq_of_olt]⟩
    · rintro ⟨γ, hγ, δ, hδ, ⟨hu, hγα | ⟨rfl, hδβ⟩⟩, rfl⟩
      · have hγβ : γ <ₒ β := by grind
        exact ⟨γ, hγα.mem, by grind [goedelPair_eq_of_olt]⟩
      · grind
  · rw [goedelPair_eq_of_ole hle,
      mem_oadd_iff (ordinal_goedelBase (by grind)) (ordinal_oadd hαo hβo)]
    refine or_congr_right ⟨?_, ?_⟩
    · rintro ⟨o, ho, rfl⟩
      simp only [mem_oadd_iff, hαo, hβo] at ho
      rcases ho with ho | ⟨δ, hδ, rfl⟩
      · exact ⟨o, by grind, α, hα, by grind [goedelPair_eq_of_olt]⟩
      · have hδα : δ ≤ₒ α := by grind
        exact ⟨α, hα, δ, by grind [goedelPair_eq_of_ole hδα]⟩
    · rintro ⟨γ, hγ, δ, hδ, ⟨hu, hγα | ⟨rfl, hδβ⟩⟩, rfl⟩
      · exact ⟨γ, by simp [mem_oadd_iff hαo hβo, hγα.mem], by grind [goedelPair_eq_of_olt]⟩
      · have hδα : δ ≤ₒ γ := by grind
        exact ⟨γ +ₒ δ, by grind [goedelPair_eq_of_ole hδα]⟩

/-- `p ↦ goedelPair (left p) (right p)` -/
noncomputable def goedelPairOfPair : ClassFunction M := fun p ↦ goedelPair (left p) (right p)

instance : (goedelPairOfPair : ClassFunction M).Sigma 1 Set.univ := by
  unfold goedelPairOfPair
  infer_instance

/-- `goedelPair α β` is the position of `!(α, β)` in Gödel's order: the value of the collapse of
Gödel's order on `succ (omax₂ α β) ×ˢ succ (omax₂ α β)` at `!(α, β)` -/
theorem goedelPair_eq_collapseOn_succ (hα : Ordinal α) (hβ : Ordinal β) :
    goedelPair α β = collapseOn (goedelRel (succ (omax₂ α β)))
      (succ (omax₂ α β) ×ˢ succ (omax₂ α β)) ﹫ !(α, β) := by
  have hsucc : Ordinal (succ (omax₂ α β)) := by grind
  have hpair : !(α, β) ∈ succ (omax₂ α β) ×ˢ succ (omax₂ α β) := by grind
  have hres :=
    isSetRestrictedTo_of_sigma (G := goedelPairOfPair) (succ (omax₂ α β) ×ˢ succ (omax₂ α β))
  suffices hcollapse : collapseOn (goedelRel (succ (omax₂ α β)))
      (succ (omax₂ α β) ×ˢ succ (omax₂ α β)) =
      goedelPairOfPair ↾₀ (succ (omax₂ α β) ×ˢ succ (omax₂ α β)) by
    simp only [hcollapse, val_toSetRestrictedTo, hres, hpair]
    simp [goedelPairOfPair]
  rw [(isStrictWellFounded₀_goedelRel hsucc).collapseOn_eq_wfRecursionOn]
  refine (IsWFRecursionOn.eq_wfRecursionOn (isStrictWellOrder_goedelRel hsucc).isStrictWellFounded
    ⟨isFunction_toSetRestrictedTo hres, dom_toSetRestrictedTo hres, fun p hpair ↦ ?_⟩).symm
  simp only [mem_sprod_iff] at hpair
  obtain ⟨α', hα', β', hβ', rfl⟩ := hpair
  have hα'o : α' <ₒ succ (omax₂ α β) := by grind
  have hβ'o : β' <ₒ succ (omax₂ α β) := by grind
  ext z
  rw [val_toSetRestrictedTo hres (mem_sprod _ _ _ _ hα' hβ'),
    mem_ran_restrict_toSetRestrictedTo_iff hres ((isRelationOn_goedelRel _).predSet_subset _)]
  simp only [goedelPairOfPair, left_orderedPair, right_orderedPair]
  constructor
  · intro hz
    simp only [mem_goedelPair_iff hα'o hβ'o] at hz
    obtain ⟨γ, hγ, δ, hδ, hlt, rfl⟩ := hz
    refine ⟨!(γ, δ), ?_, by simp⟩
    simp only [mem_predSet_iff, rel_goedelRel_iff, hsucc]
    exact ⟨⟨hγ, hδ⟩, ⟨hα'o, hβ'o⟩, hlt⟩
  · rintro ⟨q, hq, rfl⟩
    simp only [mem_predSet_iff] at hq
    have hm : q ∈ succ (omax₂ α β) ×ˢ succ (omax₂ α β) := (isRelationOn_goedelRel _).mem_left hq
    simp only [mem_sprod_iff] at hm
    obtain ⟨γ, -, δ, -, rfl⟩ := hm
    simp only [rel_goedelRel_iff, hsucc] at hq
    obtain ⟨⟨hγ, hδ⟩, -, hlt⟩ := hq
    simp only [left_orderedPair, right_orderedPair, mem_goedelPair_iff hα'o hβ'o]
    exact ⟨γ, hγ, δ, hδ, hlt, rfl⟩

/-- `goedelPair α β` is the value of the collapse of Gödel's order on `μ ×ˢ μ` at `!(α, β)`, for any
ordinal `μ` above `α` and `β` -/
theorem goedelPair_eq_collapseOn (hα : α <ₒ μ) (hβ : β <ₒ μ) :
    goedelPair α β = collapseOn (goedelRel μ) (μ ×ˢ μ) ﹫ !(α, β) := by
  have hμ : Ordinal μ := by grind
  have hle : succ (omax₂ α β) ≤ₒ μ := by grind
  have hsprod : succ (omax₂ α β) ×ˢ succ (omax₂ α β) ⊆ μ ×ˢ μ := by
    refine fun z hz ↦ sprod_mono_left _ ?_ (sprod_mono_right _ ?_ hz) <;>
      rwa [← ole_iff_subset hle.ordinal_left hμ]
  have hwf := isStrictWellFounded₀_goedelRel hμ
  rw [goedelPair_eq_collapseOn_succ (by grind) (by grind),
    hwf.collapseOn_eq_restrict (isStrictWellFounded₀_goedelRel hle.ordinal_left) hsprod
    (predSet_goedelRel hle)]
  refine val_restrict _ hwf.isFunction_collapseOn (by grind) ?_
  rw [hwf.dom_collapseOn]
  exact hsprod (by grind)

/-- Gödel's pairing function maps pairs of ordinals to ordinals -/
theorem ordinal_goedelPair (hα : Ordinal α) (hβ : Ordinal β) : Ordinal (goedelPair α β) := by
  rw [goedelPair_eq_collapseOn_succ hα hβ]
  exact (isStrictWellOrder₀_goedelRel (by grind)).ordinal_collapseOn_val
    (orderedPair_mem_succ_omax₂_sprod hα hβ)

/-- Gödel's pairing function turns Gödel's order into `<ₒ` -/
theorem goedelPair_olt_goedelPair_iff (hα : Ordinal α) (hβ : Ordinal β) (hγ : Ordinal γ)
    (hδ : Ordinal δ) : goedelPair γ δ <ₒ goedelPair α β ↔ GoedelLT γ δ α β := by
  let μ := succ (omax₂ (omax₂ α β) (omax₂ γ δ))
  rw [olt_iff_mem (ordinal_goedelPair hγ hδ) (ordinal_goedelPair hα hβ),
    goedelPair_eq_collapseOn (μ := μ) (by grind) (by grind),
    goedelPair_eq_collapseOn (μ := μ) (by grind) (by grind),
    collapseOn_goedelRel_mem_iff (by grind) (by grind) (by grind) (by grind)]

/-- Gödel's pairing function is injective -/
@[simp]
theorem goedelPair_inj (hα : Ordinal α) (hβ : Ordinal β) (hγ : Ordinal γ) (hδ : Ordinal δ) :
    goedelPair γ δ = goedelPair α β ↔ γ = α ∧ δ = β := by
  let μ := succ (omax₂ (omax₂ α β) (omax₂ γ δ))
  rw [goedelPair_eq_collapseOn (μ := μ) (by grind) (by grind),
    goedelPair_eq_collapseOn (μ := μ) (by grind) (by grind),
    collapseOn_goedelRel_inj (by grind) (by grind) (by grind) (by grind)]

/-- Every ordinal is a value of Gödel's pairing function -/
theorem exists_goedelPair_eq {ξ : M} (hξ : Ordinal ξ) :
    ∃ α β, Ordinal α ∧ Ordinal β ∧ goedelPair α β = ξ := by
  have hsucc : Ordinal (succ ξ) := by
    grind
  have hwf := isStrictWellFounded₀_goedelRel hsucc
  have hwo := isStrictWellOrder₀_goedelRel hsucc
  set C := collapseOn (goedelRel (succ ξ)) (succ ξ ×ˢ succ ξ)
  -- `η ↦ C ﹫ !(η, ∅)` is an order homomorphism from `succ ξ` into `ran C`
  let F : ClassFunction M := fun η ↦ C ﹫ !(η, ∅)
  have hres : IsSetRestrictedTo F (succ ξ) := isSetRestrictedTo_of_sigma (G := F) (succ ξ)
  have hhom : IsOrderHomOn (F ↾₀ succ ξ) (succ ξ) (ran C) := by
    refine ⟨hsucc, hwo.ordinal_ran_collapseOn,
      isFunctionFromTo_toSetRestrictedTo hres fun η hη ↦ ?_, fun η hη η' hη' ↦ ?_⟩
    · rw [hwf.isFunction_collapseOn.mem_ran_iff, hwf.dom_collapseOn]
      exact ⟨!(η, ∅), mem_sprod _ _ _ _ hη (by grind), rfl⟩
    · rw [val_toSetRestrictedTo hres hη.mem, val_toSetRestrictedTo (y := η') hres (by grind)]
      refine olt_of_mem (hwo.ordinal_collapseOn_val (mem_sprod _ _ _ _ hη.mem (by grind))) ?_
      rw [collapseOn_goedelRel_mem_iff (by grind) (by grind) (by grind) (by grind)]
      exact .inl (by grind)
  have hsub := hhom.ole
  rw [ole_iff_subset hsucc hwo.ordinal_ran_collapseOn] at hsub
  have hξran : ξ ∈ ran (collapseOn (goedelRel (succ ξ)) (succ ξ ×ˢ succ ξ)) := by grind
  rw [hwf.isFunction_collapseOn.mem_ran_iff, hwf.dom_collapseOn] at hξran
  obtain ⟨p, hp, hpξ⟩ := hξran
  simp only [mem_sprod_iff] at hp
  obtain ⟨α, hα, β, hβ, rfl⟩ := hp
  exact ⟨α, β, ordinal_of_mem hsucc hα, ordinal_of_mem hsucc hβ,
    (goedelPair_eq_collapseOn (μ := succ ξ) (by grind) (by grind)).trans hpξ⟩

/-- `goedelPair α β` is at least `omax₂ α β` -/
theorem omax₂_ole_goedelPair (hα : Ordinal α) (hβ : Ordinal β) : omax₂ α β ≤ₒ goedelPair α β := by
  -- `η ↦ goedelPair ∅ η` is an order homomorphism of the ordinals
  let F : ClassFunction M := fun η ↦ goedelPair ∅ η
  have hF : IsOrderHom F := by
    refine ⟨fun η hη ↦ ordinal_goedelPair ordinal_empty hη, fun η ξ hξη ↦ ?_⟩
    refine (goedelPair_olt_goedelPair_iff ordinal_empty hξη.ordinal_right ordinal_empty
      hξη.ordinal_left).mpr ?_
    exact .inl (by simpa using hξη)
  have hμ : Ordinal (omax₂ α β) := ordinal_omax₂ hα hβ
  refine ole_trans (hF.ole_apply hμ) ?_
  by_cases hα₀ : α = ∅
  · subst hα₀
    simp only [omax₂, empty_union]
    exact ole_refl (ordinal_goedelPair ordinal_empty hβ)
  · have h' : goedelPair ∅ (omax₂ α β) <ₒ goedelPair α β := by
      rw [goedelPair_olt_goedelPair_iff hα hβ ordinal_empty hμ]
      grind [GoedelLT]
    exact h'.ole

@[simp]
theorem goedelBase_empty : goedelBase (∅ : M) = ∅ := by
  ext z
  simp [mem_goedelBase_iff ordinal_empty]

/-- `goedelBase (succ ν) = goedelBase ν +ₒ (ν +ₒ succ ν)` -/
theorem goedelBase_succ {ν : M} (hν : Ordinal ν) :
    goedelBase (succ ν) = goedelBase ν +ₒ (ν +ₒ succ ν) := by
  ext z
  rw [mem_goedelBase_iff (ordinal_succ hν)]
  refine ⟨fun ⟨ξ, hξ, hz⟩ ↦ ?_, fun hz ↦ ⟨ν, by grind, hz⟩⟩
  rw [olt_succ_iff hν] at hξ
  rcases mem_or_eq_of_ole hξ with hξ | rfl
  · -- `goedelBase ξ +ₒ (ξ +ₒ succ ξ) ⊆ goedelBase ν ⊆ goedelBase ν +ₒ (ν +ₒ succ ν)`
    have hzν : z ∈ goedelBase ν := by
      rw [mem_goedelBase_iff hν]
      exact ⟨ξ, olt_of_mem hν hξ, hz⟩
    have := ole_oadd_right (ordinal_goedelBase hν) (ordinal_oadd hν (ordinal_succ hν))
    rw [ole_iff_subset (ordinal_goedelBase hν) (by grind)] at this
    exact this hzν
  · exact hz

/-- Gödel's pairing function is an injection from `a ×ˢ a` into `b` if `a` consists of ordinals
and it maps `a ×ˢ a` into `b` -/
theorem isInjectionFromTo_goedelPairOfPair {a b : M} (ha : ∀ x ∈ a, Ordinal x)
    (hb : ∀ m ∈ a, ∀ n ∈ a, goedelPair m n ∈ b) : goedelPairOfPair ↾₀ (a ×ˢ a) !: a ×ˢ a ↪ b := by
  have hval {m n : M} (hm : m ∈ a) (hn : n ∈ a) : goedelPairOfPair !(m, n) = goedelPair m n := by
    simp [goedelPairOfPair]
  refine isInjectionFromTo_toSetRestrictedTo (isSetRestrictedTo_of_sigma _)
    (fun z hz ↦ ?_) fun z hz z' hz' h ↦ ?_
  · simp only [mem_sprod_iff] at hz
    obtain ⟨m, hm, n, hn, rfl⟩ := hz
    rw [hval hm hn]
    exact hb m hm n hn
  · simp only [mem_sprod_iff] at hz hz'
    obtain ⟨m, hm, n, hn, rfl⟩ := hz
    obtain ⟨m', hm', n', hn', rfl⟩ := hz'
    rw [hval hm hn, hval hm' hn', goedelPair_inj (ha m' hm') (ha n' hn') (ha m hm) (ha n hn)] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- The code of the first `ν` values of a sequence `t` of ordinals, given by the primitive
recursive term `iteratedGoedelPair₀` -/
noncomputable def iteratedGoedelPair (t ν : M) : M := iteratedGoedelPair₀〘t, ν〙₂

omit [ModelsKP M] in
@[simp]
theorem _root_.FirstOrder.Language.PrimitiveRecursiveTerm.realize_iteratedGoedelPair₀
    (xs : Fin 2 → M) :
    iteratedGoedelPair₀〘xs〙 = iteratedGoedelPair (xs 0) (xs 1) := by
  rw [iteratedGoedelPair, Matrix.vec_fin_two_eq]

instance : MulticlassFunction.Sigma (fun ys : Fin 2 → M ↦ iteratedGoedelPair (ys 0) (ys 1)) 1
    Set.univ := by
  rw [← funext realize_iteratedGoedelPair₀]
  infer_instance

@[simp]
theorem iteratedGoedelPair_empty (t : M) : iteratedGoedelPair t ∅ = ∅ := by
  rw [iteratedGoedelPair, iteratedGoedelPair₀, ← Matrix.Fin.snoc_vecEmpty,
    ← Matrix.Fin.snoc_vecCons, realize_ordRecursion'_zero]
  simp

theorem iteratedGoedelPair_succ (t : M) (hν : Ordinal ν) :
    iteratedGoedelPair t (succ ν) =
      if ν = ∅ then t ﹫ ν else goedelPair (iteratedGoedelPair t ν) (t ﹫ ν) := by
  rw [iteratedGoedelPair, iteratedGoedelPair₀, ← Matrix.Fin.snoc_vecEmpty,
    ← Matrix.Fin.snoc_vecCons, realize_ordRecursion'_succ _ _ _ _ hν, ← iteratedGoedelPair₀]
  split_ifs with h <;> simp [iteratedGoedelPairStep₀, h]

@[simp]
theorem iteratedGoedelPair_one (t : M) : iteratedGoedelPair t (succ ∅) = t ﹫ ∅ := by
  simp [iteratedGoedelPair_succ t ordinal_empty]

theorem iteratedGoedelPair_succ_of_ne (t : M) (hν : Ordinal ν) (hν₀ : ν ≠ ∅) :
    iteratedGoedelPair t (succ ν) = goedelPair (iteratedGoedelPair t ν) (t ﹫ ν) := by
  simp [iteratedGoedelPair_succ t hν, hν₀]

section Omega

variable [HasOmega M]

theorem goedelBase_mem_omega {n : M} (hn : n ∈ (ω : M)) : goedelBase n ∈ (ω : M) := by
  -- the unifier eta-expands `goedelBase` here
  refine omega_induction (A := fun n ↦ Class.Mem ω (goedelBase n)) ?_ (fun n hn ih ↦ ?_) hn
  · simp
  · simp only [Class.mem_iff] at ih ⊢
    rw [goedelBase_succ (by grind)]
    exact oadd_mem_omega ih (oadd_mem_omega hn (succ_mem_omega hn))

/-- Gödel's pairing function maps `ω ×ˢ ω` into `ω` -/
theorem goedelPair_mem_omega {m n : M} (hm : m ∈ (ω : M)) (hn : n ∈ (ω : M)) :
    goedelPair m n ∈ (ω : M) := by
  have hmo : Ordinal m := by grind
  have hno : Ordinal n := by grind
  rcases olt_or_ole hmo hno with h | h
  · rw [goedelPair_eq_of_olt h, omax₂_eq_right h.ole]
    exact oadd_mem_omega (goedelBase_mem_omega hn) hm
  · rw [goedelPair_eq_of_ole h, omax₂_eq_left h]
    exact oadd_mem_omega (goedelBase_mem_omega hm) (oadd_mem_omega hm hn)

/-- Gödel's pairing function is a bijection from `ω ×ˢ ω` onto `ω` -/
theorem isBijectionFromTo_goedelPairOfPair_omega :
    goedelPairOfPair ↾₀ ((ω : M) ×ˢ (ω : M)) !: (ω : M) ×ˢ (ω : M) ↔ (ω : M) := by
  have hinj := isInjectionFromTo_goedelPairOfPair (a := (ω : M)) (by grind)
    fun _ hm _ hn ↦ goedelPair_mem_omega hm hn
  refine ⟨hinj, hinj.isFunctionFromTo, eq_of_subset_of_subset hinj.isFunctionFromTo.ran_subset
    fun ξ hξ ↦ ?_⟩
  -- `ξ = goedelPair β γ` with `omax₂ β γ ≤ₒ ξ`, so `β, γ ∈ ω`
  obtain ⟨β, γ, hβ, hγ, rfl⟩ := exists_goedelPair_eq (ξ := ξ) (by grind)
  have hlt : omax₂ β γ <ₒ ω := by grind [omax₂_ole_goedelPair]
  simp only [mem_ran_toSetRestrictedTo_iff, isSetRestrictedTo_of_sigma]
  exact ⟨!(β, γ), by grind, by simp [goedelPairOfPair]⟩

/-- `iteratedGoedelPair t n` only depends on the values of `t` below `n` -/
theorem iteratedGoedelPair_congr {t t' n : M} (hn : n ∈ (ω : M)) (h : ∀ k ∈ n, t ﹫ k = t' ﹫ k) :
    iteratedGoedelPair t n = iteratedGoedelPair t' n := by
  refine omega_induction
    (A := fun n ↦ (∀ k ∈ n, t ﹫ k = t' ﹫ k) → iteratedGoedelPair t n = iteratedGoedelPair t' n)
    (by simp) (fun n hn ih h ↦ ?_) hn h
  have hno : Ordinal n := by grind
  rw [iteratedGoedelPair_succ t hno, iteratedGoedelPair_succ t' hno, ih fun k hk ↦ h k (by grind),
    h n (by grind)]

/-- Restricting a sequence to `n` does not change the code of its first `n` values -/
theorem iteratedGoedelPair_restrict {s n : M} (hn : n ∈ (ω : M)) (hs : IsFunction s)
    (hns : n ⊆ dom s) : iteratedGoedelPair (s ↾ n) n = iteratedGoedelPair s n :=
  iteratedGoedelPair_congr hn fun _ hk ↦ val_restrict s hs hk (hns hk)

/-- The code of a sequence in `ω` is in `ω` -/
theorem iteratedGoedelPair_mem_omega {t n : M} (hn : n ∈ (ω : M)) (ht : ∀ k ∈ n, t ﹫ k ∈ (ω : M)) :
    iteratedGoedelPair t n ∈ (ω : M) := by
  refine omega_induction
    (A := fun n ↦ (∀ k ∈ n, t ﹫ k ∈ (ω : M)) → iteratedGoedelPair t n ∈ (ω : M)) (by simp)
    (fun n hn ih ht ↦ ?_) hn ht
  have hc := ih fun k hk ↦ ht k (by grind)
  have htn := ht n (by grind)
  rw [iteratedGoedelPair_succ t (by grind)]
  split_ifs
  · exact htn
  exact goedelPair_mem_omega hc htn

/-- Sequences in `ω` of the same nonzero length with the same code are equal -/
theorem iteratedGoedelPair_inj {t t' k : M} (hk : k ∈ (ω : M)) (ht : t !: succ k → ω)
    (ht' : t' !: succ k → ω) (h : iteratedGoedelPair t (succ k) = iteratedGoedelPair t' (succ k)) :
    t = t' := by
  refine omega_induction
    (A := fun k ↦ ∀ t t', (t !: succ k → ω) → (t' !: succ k → ω) →
      iteratedGoedelPair t (succ k) = iteratedGoedelPair t' (succ k) → t = t')
    (fun t t' ht ht' h ↦ ?_) (fun k hk ih t t' ht ht' h ↦ ?_) hk t t' ht ht' h
  · rw [iteratedGoedelPair_one, iteratedGoedelPair_one] at h
    exact ht.eq_of_restrict_eq ht' (by simp) h
  -- the codes of the restrictions to `succ k` and the last values are in `ω`
  have hcode : iteratedGoedelPair t (succ k) ∈ (ω : M) := by
    apply iteratedGoedelPair_mem_omega <;> grind
  have hcode' : iteratedGoedelPair t' (succ k) ∈ (ω : M) := by
    apply iteratedGoedelPair_mem_omega <;> grind
  have hlast : t ﹫ succ k ∈ (ω : M) := by grind
  have hlast' : t' ﹫ succ k ∈ (ω : M) := by grind
  rw [iteratedGoedelPair_succ_of_ne t (by grind) (by grind),
    iteratedGoedelPair_succ_of_ne t' (by grind) (by grind),
    goedelPair_inj (by grind) (by grind) (by grind) (by grind)] at h
  refine ht.eq_of_restrict_eq ht' (ih _ _ ht.restrict_succ ht'.restrict_succ ?_) h.right
  rw [iteratedGoedelPair_restrict (by grind) ht.isFunction (by grind),
    iteratedGoedelPair_restrict (by grind) ht'.isFunction (by grind), h.left]

/-- Every element of `ω` is the code of a sequence in `ω` of any nonzero length -/
theorem exists_iteratedGoedelPair_eq {k m : M} (hk : k ∈ (ω : M)) (hm : m ∈ (ω : M)) :
    ∃ t, t !: succ k → ω ∧ iteratedGoedelPair t (succ k) = m := by
  refine omega_induction
    (A := fun k ↦ ∀ m ∈ (ω : M), ∃ t, t !: succ k → ω ∧ iteratedGoedelPair t (succ k) = m)
    (fun m hm ↦ ?_) (fun k hk ih m hm ↦ ?_) hk m hm
  · refine ⟨insert !(∅, m) ∅, (isFunctionFromTo_empty _).insert_succ (by simp) hm, ?_⟩
    rw [iteratedGoedelPair_one, val_insert_self isFunction_empty (by simp)]
  -- `m = goedelPair β γ` with `β, γ ∈ ω`, `β` the code of some `s`, and `t = insert !(succ k, γ) s`
  obtain ⟨β, γ, hβ, hγ, rfl⟩ := exists_goedelPair_eq (ξ := m) (by grind)
  have hlt : omax₂ β γ <ₒ ω := by grind [omax₂_ole_goedelPair]
  obtain ⟨s, hs, rfl⟩ := ih β (by grind)
  refine ⟨insert !(succ k, γ) s, hs.insert_succ (by grind) (by grind), ?_⟩
  rw [iteratedGoedelPair_succ_of_ne _ (by grind) (by grind),
    iteratedGoedelPair_congr (t' := s) (by grind) fun j hj ↦
      val_insert_of_mem hs.isFunction (by grind) γ (by grind),
    val_insert_self hs.isFunction (by grind)]

end Omega

end MemStructure

end FirstOrder.Language
