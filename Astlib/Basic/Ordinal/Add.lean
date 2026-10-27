/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.PrimitiveRecursive.Ordinal
import Astlib.Basic.Ordinal.OrderType
import Astlib.Basic.Ordinal.Omega
/-!
# Ordinal addition

For an ordinal `α`, `α +ₒ β` is defined by recursion on `β`: `α +ₒ 0 = α`,
`α +ₒ succ β = succ (α +ₒ β)` and `α +ₒ β = ⋃_{γ ∈ β} α +ₒ γ` for nonzero limits `β`. It is `∅`
if `α` or `β` is not an ordinal. For ordinals `α` and `β`, the elements of `α +ₒ β` are those of
`α` and `α +ₒ γ` for `γ ∈ β` (`mem_oadd_iff`), from which the standard facts follow.
-/
open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula PrimitiveRecursiveTerm Fin
  MemStructure

namespace FirstOrder.Language

/-- Ordinal addition `α + β`, by recursion on `β`, which is `∅` if `α` or `β` is not an
ordinal -/
noncomputable def PrimitiveRecursiveTerm.oadd₀ {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.PrimitiveRecursiveTerm 2 :=
  (ordRecursion' (ₚᵣ0) (ᵣ2).succ.toPrimitiveRecursiveTerm
    (ᵣ⋃₀ (ᵣ1).ran).toPrimitiveRecursiveTerm).ifTrue
    (ᵣ0).isOrdinal

namespace MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M]

/-- Ordinal addition, which is `∅` if `α` or `β` is not an ordinal -/
noncomputable def oadd (α β : M) : M := oadd₀〘α, β〙₂

@[inherit_doc] infixl:65 " +ₒ " => oadd

omit [ModelsKP M] in
theorem oadd_def (α β : M) : α +ₒ β = oadd₀〘snoc ![α] β〙 := by
  simp only [oadd]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [ModelsKP M] in
@[simp]
theorem _root_.FirstOrder.Language.PrimitiveRecursiveTerm.realize_oadd₀ (xs : Fin 2 → M) :
    oadd₀〘xs〙 = xs 0 +ₒ xs 1 := by
  rw [oadd, Matrix.vec_fin_two_eq]

omit [ModelsKP M] in
theorem _root_.FirstOrder.Language.PrimitiveRecursiveTerm.realize_oadd₀_eq :
    (oadd₀.realize : (Fin 2 → M) → M) = fun xs ↦ xs 0 +ₒ xs 1 :=
  funext realize_oadd₀

/-- For an ordinal `α`, `α +ₒ β` is given by the recursion on `β` -/
theorem oadd_eq_realize_ordRecursion' {α : M} (hα : Ordinal α) (β : M) :
    α +ₒ β = (ordRecursion' (ₚᵣ0) (ᵣ2).succ.toPrimitiveRecursiveTerm
      (ᵣ⋃₀ (ᵣ1).ran).toPrimitiveRecursiveTerm)〘snoc ![α] β〙 := by
  rw [oadd_def, oadd₀, realize_ifTrue, if_pos (by simpa using hα)]

@[simp, grind =]
theorem oadd_of_not_ordinal_left {α : M} (hα : ¬Ordinal α) (β : M) : α +ₒ β = ∅ := by
  simp [oadd_def, oadd₀, hα]

/-- Ordinal addition is a `Σ₁` multiclass function -/
instance : MulticlassFunction.Sigma (fun xs : Fin 2 → M ↦ xs 0 +ₒ xs 1) 1 Set.univ := by
  rw [← realize_oadd₀_eq]
  infer_instance

@[simp, grind =]
theorem oadd_empty {α : M} (hα : Ordinal α) : α +ₒ ∅ = α := by
  rw [oadd_eq_realize_ordRecursion' hα, realize_ordRecursion'_zero]
  simp

@[simp, grind =]
theorem oadd_succ {α β : M} (hα : Ordinal α) (hβ : Ordinal β) :
    α +ₒ succ β = succ (α +ₒ β) := by
  rw [oadd_eq_realize_ordRecursion' hα, realize_ordRecursion'_succ _ _ _ _ hβ,
    oadd_eq_realize_ordRecursion' hα]
  simp

theorem oadd_of_nonZeroLimOrdinal {α β : M} (hα : Ordinal α) (hβ : NonZeroLimOrdinal β) :
    α +ₒ β = ⋃₀ ran (oadd α ↾₀ β) := by
  rw [oadd_eq_realize_ordRecursion' hα, realize_ordRecursion'_limit _ _ _ _ hβ,
    ← funext (oadd_eq_realize_ordRecursion' hα)]
  simp

@[simp, grind =]
theorem oadd_of_not_ordinal_right (α : M) {β : M} (hβ : ¬Ordinal β) : α +ₒ β = ∅ := by
  by_cases hα : Ordinal α
  · rw [oadd_eq_realize_ordRecursion' hα, realize_ordRecursion'_of_not_ordinal _ _ _ _ hβ]
  · grind

theorem mem_oadd_of_nonZeroLimOrdinal_iff {α β z : M} (hα : Ordinal α)
    (hβ : NonZeroLimOrdinal β) :
    z ∈ α +ₒ β ↔ ∃ γ ∈ β, z ∈ α +ₒ γ := by
  simp [oadd_of_nonZeroLimOrdinal hα hβ, isSetRestrictedTo_of_modelsKP]

/-- The elements of `α +ₒ β` are those of `α` and `α +ₒ γ` for `γ ∈ β` -/
theorem mem_oadd_iff {α β z : M} (hα : Ordinal α) (hβ : Ordinal β) :
    z ∈ α +ₒ β ↔ z ∈ α ∨ ∃ γ ∈ β, z = α +ₒ γ := by
  -- `p〘α, β〙₂ = α ∪ ⋃_{γ ∈ β} {α +ₒ γ}`
  let p : L.PrimitiveRecursiveTerm 2 :=
    ₚᵣ0 ∪ PrimitiveRecursiveTerm.iUnion (ₚᵣ1) {oadd₀.substBoundBound ![0, 2]}
  have hp {β z : M} : z ∈ (p〘α, β〙₂ : M) ↔ z ∈ α ∨ ∃ γ ∈ β, z = α +ₒ γ := by
    simp [p]
  rw [ordinal_induction_eq (F := oadd α) (G := fun β ↦ (p〘α, β〙₂ : M))
    (fun β hβ ih ↦ ?_) hβ, hp]
  have ih' (γ : M) (hγ : γ ∈ β) (z : M) : z ∈ α +ₒ γ ↔ z ∈ α ∨ ∃ ε ∈ γ, z = α +ₒ ε := by
    rw [ih γ (olt_of_mem hβ hγ), hp]
  ext z
  rw [hp]
  rcases hβ.cases with rfl | ⟨δ, hδ, rfl⟩ | hβ
  · simp [hα]
  · simp only [oadd_succ, hα, hδ, mem_succ_iff, ih' δ (by simp), exists_eq_or_imp]
    tauto
  · simp only [mem_oadd_of_nonZeroLimOrdinal_iff, hα, hβ]
    refine ⟨fun ⟨γ, hγ, hz⟩ ↦ ?_, ?_⟩
    · rw [ih' γ hγ z] at hz
      rcases hz with hz | ⟨ε, hε, rfl⟩ <;> grind
    · rintro (hz | ⟨ε, hε, rfl⟩)
      · exact ⟨∅, hβ.empty_mem, by simpa [hα] using hz⟩
      · refine ⟨succ ε, hβ.succ_mem hε, ?_⟩
        rw [ih' _ (hβ.succ_mem hε)]
        exact .inr ⟨ε, by simp, rfl⟩

@[simp, grind .]
theorem ordinal_oadd {α β : M} (hα : Ordinal α) (hβ : Ordinal β) : Ordinal (α +ₒ β) := by
  have hA (β : M) : ((Ordinal.subst (ClassFunction.toMulticlassFunction (oadd α)) :
      Multiclass M 1) : Class M) β ↔ Ordinal (α +ₒ β) := .rfl
  suffices h : ((Ordinal.subst (ClassFunction.toMulticlassFunction (oadd α)) :
      Multiclass M 1) : Class M) β by
    rwa [hA] at h
  refine ordinal_induction' ?_ (fun β hβ ih ↦ ?_) (fun β hβ ih ↦ ?_) hβ
  · simp [hα]
  · grind
  simp only [hA] at ih ⊢
  rw [oadd_of_nonZeroLimOrdinal hα hβ]
  refine ordinal_sUnion fun x hx ↦ ?_
  simp only [mem_ran_toSetRestrictedTo_iff (isSetRestrictedTo_of_modelsKP _ β)] at hx
  obtain ⟨γ, hγ, rfl⟩ := hx
  exact ih γ (olt_of_mem hβ.ordinal hγ)

/-- `β ↦ α +ₒ β` is an order homomorphism of the ordinals -/
theorem isOrderHom_oadd {α : M} (hα : Ordinal α) : IsOrderHom (oadd α) := by
  refine ⟨fun _ hβ ↦ ordinal_oadd hα hβ, fun β γ h ↦
    olt_of_mem (ordinal_oadd hα h.ordinal_right) ?_⟩
  simp only [mem_oadd_iff, hα, h.ordinal_right]
  exact (.inr ⟨γ, h.mem, rfl⟩)

theorem oadd_olt_oadd {α β γ : M} (hα : Ordinal α) (h : β <ₒ γ) : α +ₒ β <ₒ α +ₒ γ :=
  (isOrderHom_oadd hα).olt h

@[simp, grind =]
theorem oadd_olt_oadd_iff_left {α β γ : M} (hα : Ordinal α) (hβ : Ordinal β) (hγ : Ordinal γ) :
    α +ₒ β <ₒ α +ₒ γ ↔ β <ₒ γ :=
  (isOrderHom_oadd hα).olt_iff hβ hγ

@[simp, grind =]
theorem oadd_left_cancel {α β γ : M} (hα : Ordinal α) (hβ : Ordinal β) (hγ : Ordinal γ) :
    α +ₒ β = α +ₒ γ ↔ β = γ :=
  (isOrderHom_oadd hα).eq_iff hβ hγ |>.trans eq_comm

@[simp, grind =]
theorem oadd_ole_oadd_iff_left {α β γ : M} (hα : Ordinal α) (hβ : Ordinal β) (hγ : Ordinal γ) :
    α +ₒ β ≤ₒ α +ₒ γ ↔ β ≤ₒ γ := by
  grind

theorem ole_oadd_right {α β : M} (hα : Ordinal α) (hβ : Ordinal β) : α ≤ₒ α +ₒ β := by
  rw [ole_iff_subset hα (ordinal_oadd hα hβ)]
  intro z hz
  simp only [mem_oadd_iff, hα, hβ]
  exact (.inl hz)

theorem olt_oadd_right {α β : M} (hα : Ordinal α) (hβ : Ordinal β) (h : β ≠ ∅) :
    α <ₒ α +ₒ β := by
  simpa [hα] using oadd_olt_oadd hα ⟨ordinal_empty, hβ, empty_mem_of_ordinal_of_ne_empty hβ h⟩

theorem ole_oadd_left {α β : M} (hα : Ordinal α) (hβ : Ordinal β) : β ≤ₒ α +ₒ β :=
  (isOrderHom_oadd hα).ole_apply hβ

@[simp, grind =]
theorem empty_oadd {β : M} (hβ : Ordinal β) : ∅ +ₒ β = β := by
  refine ordinal_induction_eq (G := _root_.id) (fun β hβ ih ↦ ?_) hβ
  ext z
  simp only [mem_oadd_iff, ordinal_empty, hβ]
  grind

theorem oadd_assoc {α β γ : M} (hα : Ordinal α) (hβ : Ordinal β) (hγ : Ordinal γ) :
    α +ₒ β +ₒ γ = α +ₒ (β +ₒ γ) := by
  refine ordinal_induction_eq (G := ClassFunction.comp (oadd α) (oadd β))
    (fun γ hγ ih ↦ ?_) hγ
  simp only [ClassFunction.comp, Function.comp_apply] at ih ⊢
  ext z
  rw [mem_oadd_iff (ordinal_oadd hα hβ) hγ, mem_oadd_iff hα hβ,
    mem_oadd_iff hα (ordinal_oadd hβ hγ)]
  simp only [mem_oadd_iff, hβ, hγ]
  refine ⟨?_, by rintro (hz | ⟨ε, hε | ⟨δ, hδ, rfl⟩, rfl⟩) <;> grind⟩
  rintro ((hz | ⟨ε, hε, rfl⟩) | ⟨δ, hδ, rfl⟩) <;> grind

/-- For ordinals `α ≤ₒ β`, `α +ₒ ot (β \ α) = β` -/
theorem oadd_ot_sdiff {α β : M} (h : α ≤ₒ β) : α +ₒ ot (β \ α) = β := by
  have hα : Ordinal α := by grind
  have hβ : Ordinal β := by grind
  set S := β \ α
  have hS (x : M) (hx : x ∈ S) : Ordinal x := by
    grind
  -- `α +ₒ δ = ν` when `δ` is the image under `otMap S` of `S ∩ ν`
  have hext {δ ν : M} (hδ : Ordinal δ) (hαν : α ≤ₒ ν) (hνβ : ν ≤ₒ β)
      (hδν : ∀ γ, γ ∈ δ ↔ ∃ η ∈ S ∩ ν, otMap S ﹫ η = γ)
      (ih : ∀ η ∈ S ∩ ν, α +ₒ otMap S ﹫ η = η) : α +ₒ δ = ν := by
    rw [ole_iff_subset hα hαν.ordinal_right] at hαν
    rw [ole_iff_subset hνβ.ordinal_left hβ] at hνβ
    ext z
    simp only [mem_oadd_iff, hα, hδ, hδν, mem_inter_iff] at ih ⊢
    constructor
    · rintro (hz | ⟨γ, ⟨η, ⟨hηS, hην⟩, rfl⟩, rfl⟩) <;> grind
    · grind
  -- `ξ ∈ S → α +ₒ otMap S ﹫ ξ = ξ` as a definable class
  let Fs : Fin 2 → MulticlassFunction M 1 :=
    ![ClassFunction.toMulticlassFunction (ClassFunction.comp (oadd α) (fun y ↦ otMap S ﹫ y)),
      ClassFunction.toMulticlassFunction _root_.id]
  have hA (ξ : M) : (Class.Mem S ⟹ ((Multiclass.Eq (0 : Fin 2) 1).subst Fs : Class M)) ξ ↔
      (ξ ∈ S → α +ₒ otMap S ﹫ ξ = ξ) := by
    tauto
  -- `α +ₒ otMap S ﹫ ξ = ξ` for `ξ ∈ S`
  have hval (ξ : M) (hξ : Ordinal ξ) :
      (Class.Mem S ⟹ ((Multiclass.Eq (0 : Fin 2) 1).subst Fs : Class M)) ξ := by
    refine ordinal_induction (fun ξ hξo ih ↦ ?_) hξ
    simp only [hA] at ih ⊢
    intro hξ
    refine hext (ordinal_otMap_val hS hξ) ?_ ?_ (fun γ ↦ ?_) fun η hη ↦ ?_
    · grind
    · grind
    · simp [mem_otMap_val_iff hξ, and_assoc]
    · grind
  refine hext (ordinal_ot hS) h (ole_refl hβ) (fun γ ↦ ?_) fun η hη ↦ ?_
  · simp only [mem_ot_iff, mem_inter_iff]
    constructor <;> grind
  · grind

theorem oadd_ole_oadd_right {α α' β : M} (hβ : Ordinal β) (h : α ≤ₒ α') :
    α +ₒ β ≤ₒ α' +ₒ β := by
  have hα : Ordinal α := by grind
  have hδ : Ordinal (ot (α' \ α)) := by
    refine ordinal_ot fun x hx ↦ ?_
    simp only [mem_sdiff_iff] at hx
    exact ordinal_of_mem h.ordinal_right hx.left
  -- split `α' = α +ₒ δ`
  rw [← oadd_ot_sdiff h, oadd_assoc hα hδ hβ, oadd_ole_oadd_iff_left hα hβ (ordinal_oadd hδ hβ)]
  exact ole_oadd_left hδ hβ

/-- Addition is continuous in the second argument: `α + sup S = sup {α + γ | γ ∈ S}` for a
nonempty set `S` of ordinals -/
theorem oadd_osup {α S : M} (hα : Ordinal α) (hS : ∀ x ∈ S, Ordinal x) (hS₀ : S ≠ ∅) :
    α +ₒ osup S = osup (ran (oadd α ↾₀ S)) := by
  ext z
  simp only [osup, mem_sUnion_iff,
    mem_ran_toSetRestrictedTo_iff (isSetRestrictedTo_of_modelsKP (oadd α) S)]
  simp only [mem_oadd_iff, hα, ordinal_sUnion hS]
  constructor
  · rintro (hz | ⟨γ, hγ, rfl⟩)
    · simp only [ne_empty_iff S] at hS₀
      obtain ⟨γ, hγ⟩ := hS₀
      refine ⟨α +ₒ γ, ⟨γ, hγ, rfl⟩, ?_⟩
      simp only [mem_oadd_iff, hα, hS γ hγ]
      tauto
    · simp only [mem_sUnion_iff] at hγ
      obtain ⟨δ, hδ, hγδ⟩ := hγ
      refine ⟨α +ₒ δ, ⟨δ, hδ, rfl⟩, ?_⟩
      simp only [mem_oadd_iff, hα, hS δ hδ]
      exact .inr ⟨γ, hγδ, rfl⟩
  · rintro ⟨_, ⟨δ, hδ, rfl⟩, hz⟩
    simp only [mem_oadd_iff, hα, hS δ hδ] at hz
    rcases hz with hz | ⟨γ, hγ, rfl⟩ <;> grind

/-- The bijection from the disjoint union of `α` and `β` onto `α +ₒ β`, sending `!(∅, x)` to `x`
and `!({∅}, γ)` to `α +ₒ γ` -/
noncomputable def oaddMap (α β : M) : M :=
  right ↾₀ (({∅} : M) ×ˢ α) ∪ ClassFunction.comp (oadd α) right ↾₀ (({{∅}} : M) ×ˢ β)

section OaddMap

variable {α β x γ : M}

theorem isSetRestrictedTo_oaddMap_left (α : M) : IsSetRestrictedTo right (({∅} : M) ×ˢ α) :=
  isSetRestrictedTo_of_modelsKP _ _

theorem isSetRestrictedTo_oaddMap_right (α β : M) :
    IsSetRestrictedTo (ClassFunction.comp (oadd α) right) (({{∅}} : M) ×ˢ β) :=
  isSetRestrictedTo_of_modelsKP _ _

/-- The two parts of `oaddMap α β` have disjoint domains -/
theorem dom_oaddMap_disjoint {z : M} (hz : z ∈ dom (right ↾₀ (({∅} : M) ×ˢ α))) :
    z ∉ dom (ClassFunction.comp (oadd α) right ↾₀ (({{∅}} : M) ×ˢ β)) := by
  simp only [dom_toSetRestrictedTo, isSetRestrictedTo_oaddMap_left α,
    isSetRestrictedTo_oaddMap_right α β, mem_sprod_iff, mem_singleton_iff] at hz ⊢
  obtain ⟨_, rfl, _, _, rfl⟩ := hz
  grind [singleton_ne_empty (M := M) (x := ∅)]

theorem isFunction_oaddMap (α β : M) : IsFunction (oaddMap α β) :=
  (isFunction_toSetRestrictedTo (isSetRestrictedTo_oaddMap_left α)).union_of_disjoint
    (isFunction_toSetRestrictedTo (isSetRestrictedTo_oaddMap_right α β))
    (fun _ ↦ dom_oaddMap_disjoint)

@[simp]
theorem dom_oaddMap (α β : M) : dom (oaddMap α β) = disjUnion α β := by
  rw [oaddMap, dom_union, dom_toSetRestrictedTo (isSetRestrictedTo_oaddMap_left α),
    dom_toSetRestrictedTo (isSetRestrictedTo_oaddMap_right α β), disjUnion]

@[simp, grind =]
theorem oaddMap_val_left (hx : x ∈ α) : oaddMap α β ﹫ !(∅, x) = x := by
  have h₁ := isSetRestrictedTo_oaddMap_left α
  have hx' : !(∅, x) ∈ ({∅} : M) ×ˢ α := mem_sprod _ _ _ _ (by simp) hx
  rw [oaddMap, val_union_left (isFunction_toSetRestrictedTo h₁)
    (isFunction_toSetRestrictedTo (isSetRestrictedTo_oaddMap_right α β))
    (fun _ ↦ dom_oaddMap_disjoint) (by rwa [dom_toSetRestrictedTo h₁]),
    val_toSetRestrictedTo h₁ hx', right_orderedPair]

@[simp, grind =]
theorem oaddMap_val_right (hγ : γ ∈ β) : oaddMap α β ﹫ !({∅}, γ) = α +ₒ γ := by
  have h₂ := isSetRestrictedTo_oaddMap_right α β
  have hγ' : !({∅}, γ) ∈ ({{∅}} : M) ×ˢ β := mem_sprod _ _ _ _ (by simp) hγ
  rw [oaddMap, val_union_right (isFunction_toSetRestrictedTo (isSetRestrictedTo_oaddMap_left α))
    (isFunction_toSetRestrictedTo h₂) (fun _ ↦ dom_oaddMap_disjoint)
    (by rwa [dom_toSetRestrictedTo h₂]), val_toSetRestrictedTo h₂ hγ']
  simp [ClassFunction.comp]

/-- `oaddMap α β` is a bijection from the disjoint union of `α` and `β` onto `α +ₒ β` -/
theorem isBijectionFromTo_oaddMap (hα : Ordinal α) (hβ : Ordinal β) :
    oaddMap α β !: disjUnion α β ↔ α +ₒ β := by
  have hne {x γ : M} (hx : x <ₒ α) (hγ : γ <ₒ β) : x ≠ α +ₒ γ := by
    grind [olt_of_olt_of_ole hx (ole_oadd_right hα hγ.left)]
  have hinj : oaddMap α β !: disjUnion α β ↪ α +ₒ β := by
    refine isInjectionFromTo_of_val (isFunction_oaddMap α β) (dom_oaddMap α β)
      (fun z hz ↦ ?_) fun z hz z' hz' h ↦ ?_
    · simp only [mem_disjUnion_iff] at hz
      simp only [mem_oadd_iff, hα, hβ]
      grind
    · simp only [mem_disjUnion_iff] at hz hz'
      rcases hz with ⟨x, hx, rfl⟩ | ⟨γ, hγ, rfl⟩ <;>
        rcases hz' with ⟨x', hx', rfl⟩ | ⟨γ', hγ', rfl⟩ <;> grind
  refine ⟨hinj, ?_⟩
  rw [isSurjectionFromTo_iff_of_isFunctionFromTo hinj.isFunctionFromTo]
  intro z hz
  simp only [mem_oadd_iff, hα, hβ] at hz
  rcases hz with hz | ⟨γ, hγ, rfl⟩
  · exact ⟨!(∅, z), by simp [hz]⟩
  · exact ⟨!({∅}, γ), by simp [hγ]⟩

end OaddMap

section Omega

variable [HasOmega M] {m n : M}

omit [HasOmega M] in
@[simp, grind =]
theorem oadd_one {α : M} (hα : Ordinal α) : α +ₒ succ ∅ = succ α := by
  simp [hα]

@[simp, grind .]
theorem oadd_mem_omega (hm : m ∈ (ω : M)) (hn : n ∈ (ω : M)) : m +ₒ n ∈ (ω : M) := by
  refine omega_induction (A := fun n ↦ Class.Mem ω (m +ₒ n)) ?_ (fun n hn ih ↦ ?_) hn
  · rwa [Class.mem_iff, oadd_empty (ordinal_of_mem ordinal_omega hm)]
  · simp only [Class.mem_iff] at ih ⊢
    rw [oadd_succ (ordinal_of_mem ordinal_omega hm) (ordinal_of_mem ordinal_omega hn)]
    exact succ_mem_omega ih

@[simp, grind =]
theorem one_oadd_of_mem_omega (hn : n ∈ (ω : M)) : succ ∅ +ₒ n = succ n := by
  refine omega_induction_eq ?_ (fun n hn ih ↦ ?_) hn
  · simp
  · grind

/-- `1 +ₒ ω = ω` -/
theorem one_oadd_omega : succ ∅ +ₒ (ω : M) = ω := by
  ext z
  rw [mem_oadd_iff (by simp) ordinal_omega]
  constructor
  · rintro (hz | ⟨n, hn, rfl⟩) <;> grind
  · intro hz
    rcases mem_omega_cases hz with rfl | ⟨m, hm, rfl⟩ <;> grind

/-- `1 +ₒ α = α` for `α ≥ ω` -/
theorem one_oadd_of_omega_ole {α : M} (hωα : (ω : M) ≤ₒ α) : succ ∅ +ₒ α = α := by
  rw [← oadd_ot_sdiff hωα, ← oadd_assoc (by simp) ordinal_omega (ordinal_ot fun x hx ↦ by grind),
    one_oadd_omega]

/-- Addition is commutative on `ω` -/
theorem oadd_comm_of_mem_omega (hm : m ∈ (ω : M)) (hn : n ∈ (ω : M)) : m +ₒ n = n +ₒ m := by
  have hmo : Ordinal m := by grind
  refine omega_induction_eq (G := fun n ↦ n +ₒ m) ?_ (fun n hn ih ↦ ?_) hn
  · simp [hmo]
  · have hno : Ordinal n := by grind
    -- `succ n +ₒ m = n +ₒ (succ ∅ +ₒ m) = n +ₒ succ m`
    rw [oadd_succ hmo hno, ih, ← oadd_one hno, oadd_assoc hno (by simp) hmo,
      one_oadd_of_mem_omega hm, oadd_succ hno hmo]

end Omega

end MemStructure

end FirstOrder.Language
