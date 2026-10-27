/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Ordinal.Add
/-!
# Ordinal multiplication

For an ordinal `α`, `α *ₒ β` is defined by recursion on `β`: `α *ₒ 0 = 0`,
`α *ₒ succ β = α *ₒ β +ₒ α` and `α *ₒ β = ⋃_{γ ∈ β} α *ₒ γ` for nonzero limits `β`. It is `∅` if
`α` or `β` is not an ordinal. For ordinals `α` and `β`, the elements of `α *ₒ β` are the
`α *ₒ γ +ₒ δ` for `γ ∈ β` and `δ ∈ α` (`mem_omul_iff`), from which the standard facts follow.
-/
open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula PrimitiveRecursiveTerm Fin
  MemStructure

namespace FirstOrder.Language

/-- Ordinal multiplication `α * β`, by recursion on `β`, which is `∅` if `α` or `β` is not an
ordinal -/
noncomputable def PrimitiveRecursiveTerm.omul₀ {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.PrimitiveRecursiveTerm 2 :=
  (ordRecursion' (∅ : L.RudimentaryTerm 1).toPrimitiveRecursiveTerm
    (oadd₀.substBoundPR ![ₚᵣ2, ₚᵣ0]) (ᵣ⋃₀ (ᵣ1).ran).toPrimitiveRecursiveTerm).ifTrue
    (ᵣ0).isOrdinal

namespace MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] {α β γ z : M}

/-- Ordinal multiplication, which is `∅` if `α` or `β` is not an ordinal -/
noncomputable def omul (α β : M) : M := omul₀〘α, β〙₂

@[inherit_doc] infixl:70 " *ₒ " => omul

omit [ModelsKP M] in
theorem omul_def (α β : M) : α *ₒ β = omul₀〘snoc ![α] β〙 := by
  simp only [omul]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [ModelsKP M] in
@[simp]
theorem _root_.FirstOrder.Language.PrimitiveRecursiveTerm.realize_omul₀ (xs : Fin 2 → M) :
    omul₀〘xs〙 = xs 0 *ₒ xs 1 := by
  rw [omul, Matrix.vec_fin_two_eq]

omit [ModelsKP M] in
theorem _root_.FirstOrder.Language.PrimitiveRecursiveTerm.realize_omul₀_eq :
    (omul₀.realize : (Fin 2 → M) → M) = fun xs ↦ xs 0 *ₒ xs 1 :=
  funext realize_omul₀

/-- For an ordinal `α`, `α *ₒ β` is given by the recursion on `β` -/
theorem omul_eq_realize_ordRecursion' (hα : Ordinal α) (β : M) :
    α *ₒ β = (ordRecursion' (∅ : L.RudimentaryTerm 1).toPrimitiveRecursiveTerm
      (oadd₀.substBoundPR ![ₚᵣ2, ₚᵣ0]) (ᵣ⋃₀ (ᵣ1).ran).toPrimitiveRecursiveTerm)〘snoc ![α] β〙 := by
  rw [omul_def, omul₀, realize_ifTrue, if_pos (by simpa using hα)]

@[simp, grind =]
theorem omul_of_not_ordinal_left (hα : ¬Ordinal α) (β : M) : α *ₒ β = ∅ := by
  simp [omul_def, omul₀, hα]

/-- Ordinal multiplication is a `Σ₁` multiclass function -/
instance : MulticlassFunction.Sigma (fun xs : Fin 2 → M ↦ xs 0 *ₒ xs 1) 1 Set.univ := by
  rw [← realize_omul₀_eq]
  infer_instance



@[simp, grind =]
theorem omul_empty (hα : Ordinal α) : α *ₒ ∅ = ∅ := by
  rw [omul_eq_realize_ordRecursion' hα, realize_ordRecursion'_zero]
  simp

@[simp, grind =]
theorem omul_succ (hα : Ordinal α) (hβ : Ordinal β) : α *ₒ succ β = α *ₒ β +ₒ α := by
  rw [omul_eq_realize_ordRecursion' hα, realize_ordRecursion'_succ _ _ _ _ hβ,
    omul_eq_realize_ordRecursion' hα]
  simp

theorem omul_of_nonZeroLimOrdinal (hα : Ordinal α) (hβ : NonZeroLimOrdinal β) :
    α *ₒ β = ⋃₀ ran (omul α ↾₀ β) := by
  rw [omul_eq_realize_ordRecursion' hα, realize_ordRecursion'_limit _ _ _ _ hβ,
    ← funext (omul_eq_realize_ordRecursion' hα)]
  simp

@[simp, grind =]
theorem omul_of_not_ordinal_right (α : M) (hβ : ¬Ordinal β) : α *ₒ β = ∅ := by
  by_cases hα : Ordinal α
  · rw [omul_eq_realize_ordRecursion' hα, realize_ordRecursion'_of_not_ordinal _ _ _ _ hβ]
  · grind

theorem mem_omul_of_nonZeroLimOrdinal_iff (hα : Ordinal α) (hβ : NonZeroLimOrdinal β) :
    z ∈ α *ₒ β ↔ ∃ γ ∈ β, z ∈ α *ₒ γ := by
  simp [omul_of_nonZeroLimOrdinal hα hβ, isSetRestrictedTo_of_modelsKP]

@[simp, grind .]
theorem ordinal_omul (hα : Ordinal α) (hβ : Ordinal β) : Ordinal (α *ₒ β) := by
  have hA (β : M) : ((Ordinal.subst (ClassFunction.toMulticlassFunction (omul α)) :
      Multiclass M 1) : Class M) β ↔ Ordinal (α *ₒ β) := .rfl
  suffices h : ((Ordinal.subst (ClassFunction.toMulticlassFunction (omul α)) :
      Multiclass M 1) : Class M) β by
    rwa [hA] at h
  refine ordinal_induction' ?_ (fun β hβ ih ↦ ?_) (fun β hβ ih ↦ ?_) hβ
  · simp [hα]
  · grind
  simp only [hA] at ih ⊢
  rw [omul_of_nonZeroLimOrdinal hα hβ]
  refine ordinal_sUnion fun x hx ↦ ?_
  simp only [mem_ran_toSetRestrictedTo_iff (isSetRestrictedTo_of_modelsKP _ β)] at hx
  obtain ⟨γ, hγ, rfl⟩ := hx
  grind [olt_of_mem hβ.ordinal hγ]

/-- The elements of `α *ₒ β` are the `α *ₒ γ +ₒ δ` for `γ ∈ β` and `δ ∈ α` -/
theorem mem_omul_iff (hα : Ordinal α) (hβ : Ordinal β) :
    z ∈ α *ₒ β ↔ ∃ γ ∈ β, ∃ δ ∈ α, z = α *ₒ γ +ₒ δ := by
  -- `p〘α, β〙₂ = ⋃_{γ ∈ β} ⋃_{δ ∈ α} {α *ₒ γ +ₒ δ}`
  let p : L.PrimitiveRecursiveTerm 2 :=
    PrimitiveRecursiveTerm.iUnion (ₚᵣ1) (PrimitiveRecursiveTerm.iUnion (ₚᵣ0)
      {oadd₀.substBoundPR ![omul₀.substBoundBound ![0, 2], ₚᵣ3]})
  have hp {β z : M} :
      z ∈ (p〘α, β〙₂ : M) ↔ ∃ γ ∈ β, ∃ δ ∈ α, z = α *ₒ γ +ₒ δ := by
    simp [p]
  rw [ordinal_induction_eq (F := omul α) (G := fun β ↦ (p〘α, β〙₂ : M))
    (fun β hβ ih ↦ ?_) hβ, hp]
  have ih' (γ : M) (hγ : γ ∈ β) (z : M) :
      z ∈ α *ₒ γ ↔ ∃ ε ∈ γ, ∃ δ ∈ α, z = α *ₒ ε +ₒ δ := by
    rw [ih γ (olt_of_mem hβ hγ), hp]
  ext z
  rw [hp]
  rcases hβ.cases with rfl | ⟨ε, hε, rfl⟩ | hβ
  · simp [hα]
  · simp only [omul_succ, hα, hε, mem_oadd_iff, ordinal_omul, ih' ε (by simp)]
    simp [mem_succ_iff, or_comm]
  · simp only [mem_omul_of_nonZeroLimOrdinal_iff, hα, hβ]
    constructor
    · rintro ⟨γ, hγ, hz⟩
      rw [ih' γ hγ z] at hz
      obtain ⟨ε, hε, δ, hδ, rfl⟩ := hz
      grind
    · rintro ⟨ε, hε, δ, hδ, rfl⟩
      refine ⟨succ ε, hβ.succ_mem hε, ?_⟩
      rw [ih' _ (hβ.succ_mem hε)]
      exact ⟨ε, by simp, δ, hδ, rfl⟩

/-- `α *ₒ γ +ₒ δ <ₒ α *ₒ β` for `γ <ₒ β` and `δ <ₒ α` -/
theorem omul_oadd_olt_omul (hα : Ordinal α) {δ : M} (hγ : γ <ₒ β) (hδ : δ <ₒ α) :
    α *ₒ γ +ₒ δ <ₒ α *ₒ β := by
  refine ⟨ordinal_oadd (ordinal_omul hα hγ.ordinal_left) hδ.ordinal_left,
    ordinal_omul hα hγ.ordinal_right, ?_⟩
  simp only [mem_omul_iff, hα, hγ.ordinal_right]
  exact ⟨γ, hγ.mem, δ, hδ.mem, rfl⟩

/-- `β ↦ α *ₒ β` is an order homomorphism of the ordinals for `α ≠ ∅` -/
theorem isOrderHom_omul (hα : Ordinal α) (hα₀ : α ≠ ∅) : IsOrderHom (omul α) := by
  refine ⟨fun _ hβ ↦ ordinal_omul hα hβ, fun β γ h ↦ ?_⟩
  simpa [ordinal_omul hα h.ordinal_left] using omul_oadd_olt_omul hα h
    ⟨ordinal_empty, hα, empty_mem_of_ordinal_of_ne_empty hα hα₀⟩

theorem omul_olt_omul (hα : Ordinal α) (hα₀ : α ≠ ∅) (h : β <ₒ γ) : α *ₒ β <ₒ α *ₒ γ :=
  (isOrderHom_omul hα hα₀).olt h

@[simp, grind =]
theorem omul_olt_omul_iff_left (hα : Ordinal α) (hβ : Ordinal β) (hγ : Ordinal γ)
    (hα₀ : α ≠ ∅) : α *ₒ β <ₒ α *ₒ γ ↔ β <ₒ γ :=
  (isOrderHom_omul hα hα₀).olt_iff hβ hγ

@[simp, grind =]
theorem omul_left_cancel (hα : Ordinal α) (hβ : Ordinal β) (hγ : Ordinal γ) (hα₀ : α ≠ ∅) :
    α *ₒ β = α *ₒ γ ↔ β = γ :=
  (isOrderHom_omul hα hα₀).eq_iff hβ hγ |>.trans eq_comm

@[simp, grind =]
theorem omul_ole_omul_iff_left (hα : Ordinal α) (hβ : Ordinal β) (hγ : Ordinal γ)
    (hα₀ : α ≠ ∅) : α *ₒ β ≤ₒ α *ₒ γ ↔ β ≤ₒ γ := by
  grind

/-- `β ↦ α *ₒ β` is strictly increasing for `α ≠ ∅`, hence `β ≤ₒ α *ₒ β` -/
theorem ole_omul_left (hα : Ordinal α) (hβ : Ordinal β) (hα₀ : α ≠ ∅) : β ≤ₒ α *ₒ β :=
  (isOrderHom_omul hα hα₀).ole_apply hβ

@[simp, grind =]
theorem empty_omul (hβ : Ordinal β) : ∅ *ₒ β = ∅ := by
  ext z
  simp [mem_omul_iff ordinal_empty hβ]

@[simp, grind =]
theorem omul_one (hα : Ordinal α) : α *ₒ succ ∅ = α := by
  grind

@[simp, grind =]
theorem one_omul (hβ : Ordinal β) : succ ∅ *ₒ β = β := by
  have h₁ : Ordinal (succ (∅ : M)) := by grind
  refine ordinal_induction_eq (G := _root_.id) (fun β hβ ih ↦ ?_) hβ
  simp only [_root_.id] at ih ⊢
  ext z
  simp only [mem_omul_iff, h₁, hβ]
  refine ⟨by grind, ?_⟩
  intro hz
  exact ⟨z, hz, ∅, mem_succ_self ∅, by simp [ih z (olt_of_mem hβ hz), ordinal_of_mem hβ hz]⟩

/-- Left distributivity `α *ₒ (β +ₒ γ) = α *ₒ β +ₒ α *ₒ γ` -/
theorem omul_oadd (hα : Ordinal α) (hβ : Ordinal β) (hγ : Ordinal γ) :
    α *ₒ (β +ₒ γ) = α *ₒ β +ₒ α *ₒ γ := by
  have hαβ : Ordinal (α *ₒ β) := by grind
  refine ordinal_induction_eq (F := ClassFunction.comp (omul α) (oadd β))
    (G := ClassFunction.comp (oadd (α *ₒ β)) (omul α)) (fun γ hγ ih ↦ ?_) hγ
  simp only [ClassFunction.comp, Function.comp_apply] at ih ⊢
  ext z
  rw [mem_omul_iff hα (ordinal_oadd hβ hγ), mem_oadd_iff hαβ (ordinal_omul hα hγ),
    mem_omul_iff hα hβ]
  simp only [mem_oadd_iff, hβ, hγ, mem_omul_iff, hα]
  constructor
  · rintro ⟨ξ, hξ | ⟨ε, hε, rfl⟩, δ, hδ, rfl⟩
    · grind
    · have hε' : Ordinal ε := by grind
      refine .inr ⟨α *ₒ ε +ₒ δ, ⟨ε, hε, δ, hδ, rfl⟩, ?_⟩
      rw [ih ε (olt_of_mem hγ hε), oadd_assoc hαβ (ordinal_omul hα hε') (ordinal_of_mem hα hδ)]
  · rintro (⟨ξ, hξ, δ, hδ, rfl⟩ | ⟨η, ⟨ε, hε, δ, hδ, rfl⟩, rfl⟩)
    · grind
    · have hε' : Ordinal ε := by grind
      refine ⟨β +ₒ ε, .inr ⟨ε, hε, rfl⟩, δ, hδ, ?_⟩
      rw [ih ε (olt_of_mem hγ hε), oadd_assoc hαβ (ordinal_omul hα hε') (ordinal_of_mem hα hδ)]

/-- Associativity `α *ₒ β *ₒ γ = α *ₒ (β *ₒ γ)` -/
theorem omul_assoc (hα : Ordinal α) (hβ : Ordinal β) (hγ : Ordinal γ) :
    α *ₒ β *ₒ γ = α *ₒ (β *ₒ γ) := by
  have hαβ : Ordinal (α *ₒ β) := by grind
  refine ordinal_induction_eq (G := ClassFunction.comp (omul α) (omul β))
    (fun γ hγ ih ↦ ?_) hγ
  simp only [ClassFunction.comp, Function.comp_apply] at ih ⊢
  ext z
  simp only [mem_omul_iff, hαβ, hγ, hα, ordinal_omul, hβ]
  -- `α *ₒ (β *ₒ ε +ₒ η) +ₒ δ = α *ₒ β *ₒ ε +ₒ (α *ₒ η +ₒ δ)`
  have hassoc {ε η δ : M} (hε : ε ∈ γ) (hη : η ∈ β) (hδ : δ ∈ α) :
      α *ₒ (β *ₒ ε +ₒ η) +ₒ δ = α *ₒ β *ₒ ε +ₒ (α *ₒ η +ₒ δ) := by
    rw [omul_oadd hα (ordinal_omul hβ (by grind)) (by grind), ← ih ε (olt_of_mem hγ hε),
      oadd_assoc (ordinal_omul hαβ (by grind)) (ordinal_omul hα (by grind)) (ordinal_of_mem hα hδ)]
  constructor <;> grind

/-- `α ↦ α *ₒ β` is monotone -/
theorem omul_ole_omul_right {α' : M} (hβ : Ordinal β) (h : α ≤ₒ α') : α *ₒ β ≤ₒ α' *ₒ β := by
  have hα : Ordinal α := by grind
  have hα' : Ordinal α' := by grind
  have hαα' := h
  rw [ole_iff_subset hα hα'] at hαα'
  -- `α *ₒ γ +ₒ δ ≤ₒ α' *ₒ γ +ₒ δ` by induction on `γ`
  let Fs : Fin 2 → MulticlassFunction M 1 :=
    ![ClassFunction.toMulticlassFunction (omul α), ClassFunction.toMulticlassFunction (omul α')]
  have hA (γ : M) : ((Multiclass.Subset (0 : Fin 2) 1).subst Fs : Class M) γ ↔
      α *ₒ γ ⊆ α' *ₒ γ := .rfl
  have hstep (γ : M) (hγ : Ordinal γ) :
      ((Multiclass.Subset (0 : Fin 2) 1).subst Fs : Class M) γ := by
    refine ordinal_induction (fun γ hγ ih ↦ ?_) hγ
    simp only [hA] at ih ⊢
    intro z hz
    simp only [mem_omul_iff, hα, hγ] at hz
    obtain ⟨ε, hε, δ, hδ, rfl⟩ := hz
    have hε' : Ordinal ε := by grind
    have h₁ : α *ₒ ε +ₒ δ ≤ₒ α' *ₒ ε +ₒ δ := oadd_ole_oadd_right (by grind) (by grind)
    exact (olt_of_ole_of_olt h₁ (omul_oadd_olt_omul hα' ⟨hε', hγ, hε⟩ ⟨(by grind), hα', hαα' hδ⟩)).mem
  have h := hstep β hβ
  rw [hA] at h
  rw [ole_iff_subset (ordinal_omul hα hβ) (ordinal_omul hα' hβ)]
  exact h

/-- Multiplication is continuous in the second argument: `α * sup S = sup {α * γ | γ ∈ S}` for a
set `S` of ordinals -/
theorem omul_osup {S : M} (hα : Ordinal α) (hS : ∀ x ∈ S, Ordinal x) :
    α *ₒ osup S = osup (ran (omul α ↾₀ S)) := by
  ext z
  simp only [osup, mem_sUnion_iff,
    mem_ran_toSetRestrictedTo_iff (isSetRestrictedTo_of_modelsKP (omul α) S)]
  simp only [mem_omul_iff, hα, ordinal_sUnion hS]
  constructor
  · rintro ⟨γ, hγ, δ, hδ, rfl⟩
    simp only [mem_sUnion_iff] at hγ
    obtain ⟨ε, hε, hγε⟩ := hγ
    refine ⟨α *ₒ ε, ⟨ε, hε, rfl⟩, ?_⟩
    simp only [mem_omul_iff, hα, hS ε hε]
    exact ⟨γ, hγε, δ, hδ, rfl⟩
  · rintro ⟨_, ⟨ε, hε, rfl⟩, hz⟩
    simp only [mem_omul_iff, hα, hS ε hε] at hz
    obtain ⟨γ, hγ, δ, hδ, rfl⟩ := hz
    refine ⟨γ, ?_, δ, hδ, rfl⟩
    simp only [mem_sUnion_iff]
    exact ⟨ε, hε, hγ⟩

section Lex

/-- `!(γ, δ) ↦ α *ₒ γ +ₒ δ` -/
noncomputable def omulPair (α : M) : ClassFunction M := fun p ↦ α *ₒ left p +ₒ right p

@[simp]
theorem omulPair_orderedPair (α γ δ : M) : omulPair α !(γ, δ) = α *ₒ γ +ₒ δ := by
  simp [omulPair]

instance (α : M) : (omulPair α).Sigma 1 Set.univ := by
  unfold omulPair
  infer_instance

/-- The bijection from `β ×ˢ α` onto `α *ₒ β` sending `!(γ, δ)` to `α *ₒ γ +ₒ δ`: the collapse of
the lexicographic order on `β ×ˢ α` -/
noncomputable def omulMap (α β : M) : M := omulPair α ↾₀ (β ×ˢ α)

theorem isFunction_omulMap (α β : M) : IsFunction (omulMap α β) :=
  isFunction_toSetRestrictedTo (isSetRestrictedTo_of_sigma _)

@[simp]
theorem dom_omulMap (α β : M) : dom (omulMap α β) = β ×ˢ α :=
  dom_toSetRestrictedTo (isSetRestrictedTo_of_sigma _)

@[simp, grind =]
theorem omulMap_val {δ : M} (hγ : γ <ₒ β) (hδ : δ <ₒ α) :
    omulMap α β ﹫ !(γ, δ) = α *ₒ γ +ₒ δ := by
  rw [omulMap,
    val_toSetRestrictedTo (isSetRestrictedTo_of_sigma _) (by grind),
    omulPair_orderedPair]

@[simp]
theorem ran_omulMap (hα : Ordinal α) (hβ : Ordinal β) : ran (omulMap α β) = α *ₒ β := by
  ext z
  rw [omulMap, mem_ran_toSetRestrictedTo_iff (isSetRestrictedTo_of_sigma _), mem_omul_iff hα hβ]
  constructor
  · rintro ⟨p, hp, rfl⟩
    simp only [mem_sprod_iff] at hp
    obtain ⟨γ, hγ, δ, hδ, rfl⟩ := hp
    exact ⟨γ, hγ, δ, hδ, by simp⟩
  · rintro ⟨γ, hγ, δ, hδ, rfl⟩
    exact ⟨!(γ, δ), by grind, omulPair_orderedPair α γ δ⟩

/-- `!(γ, δ) ↦ α *ₒ γ +ₒ δ` is strictly increasing for the lexicographic order -/
theorem omul_oadd_olt_omul_oadd (hα : Ordinal α) (hγ : Ordinal γ) {γ' δ δ' : M} (hδ : δ <ₒ α)
    (hδ' : δ' <ₒ α) (h : γ' <ₒ γ ∨ (γ' = γ ∧ δ' <ₒ δ)) : α *ₒ γ' +ₒ δ' <ₒ α *ₒ γ +ₒ δ := by
  rcases h with h | ⟨rfl, h⟩
  · grind [olt_of_olt_of_ole (omul_oadd_olt_omul hα h hδ'), ole_oadd_right, ordinal_omul]
  · grind [oadd_olt_oadd, ordinal_omul]

/-- The lexicographic order on `β ×ˢ α` is strictly well-founded, also for definable classes -/
theorem isStrictWellFounded₀_lexProd (hα : Ordinal α) (hβ : Ordinal β) :
    IsStrictWellFounded₀ (lexProd (memRelOn β) β (memRelOn α) α) (β ×ˢ α) := by
  -- `omulPair α` maps the lexicographic order into `∈`
  refine isStrictWellFounded₀_of_mem (F := omulPair α) isRelationOn_lexProd
    fun p hp q hq hqp ↦ ?_
  simp only [mem_sprod_iff] at hp hq
  obtain ⟨γ, hγ, δ, hδ, rfl⟩ := hp
  obtain ⟨γ', hγ', δ', hδ', rfl⟩ := hq
  simp only [rel_lexProd_iff, rel_memRelOn_iff, omulPair_orderedPair] at hqp ⊢
  grind [omul_oadd_olt_omul_oadd]

/-- The Mostowski collapse of the lexicographic order on `β ×ˢ α` is
`!(γ, δ) ↦ α *ₒ γ +ₒ δ` -/
theorem collapseOn_lexProd (hα : Ordinal α) (hβ : Ordinal β) :
    collapseOn (lexProd (memRelOn β) β (memRelOn α) α) (β ×ˢ α) = omulMap α β := by
  set R := lexProd (memRelOn β) β (memRelOn α) α
  -- `omulMap α β` is defined by `R`-recursion from `ran`
  suffices hrec : IsWFRecursionOn R (β ×ˢ α) ran (omulMap α β) by
    rw [(isStrictWellFounded₀_lexProd hα hβ).collapseOn_eq_wfRecursionOn, ← hrec.eq_wfRecursionOn
      ((isStrictWellOrder_memRelOn fun x hx ↦ ordinal_of_mem hβ hx).lexProd
        (isStrictWellOrder_memRelOn fun x hx ↦ ordinal_of_mem hα hx)).isStrictWellFounded]
  refine ⟨isFunction_omulMap α β, dom_omulMap α β, fun p hp ↦ ?_⟩
  simp only [mem_sprod_iff] at hp
  obtain ⟨γ, hγ, δ, hδ, rfl⟩ := hp
  have hmem {γ' δ' : M} : !(γ', δ') ∈ predSet R !(γ, δ) ↔
      (γ' ∈ β ∧ δ' ∈ α) ∧ (γ' ∈ γ ∨ (γ' = γ ∧ δ' ∈ δ)) := by
    simp only [R, mem_predSet_iff, rel_lexProd_iff, rel_memRelOn_iff]
    grind
  ext z
  simp only [omulMap_val, olt_of_mem, hβ, hγ, hα, hδ]
  simp only [omulMap, mem_ran_restrict_toSetRestrictedTo_iff, isSetRestrictedTo_of_sigma, R,
    isRelationOn_lexProd.predSet_subset, mem_oadd_iff, mem_omul_iff, ordinal_omul,
    ordinal_of_mem hβ hγ, ordinal_of_mem hα hδ, hα]
  constructor
  · rintro (⟨γ', hγ', δ', hδ', rfl⟩ | ⟨δ', hδ', rfl⟩)
    · refine ⟨!(γ', δ'), ?_, omulPair_orderedPair ..⟩
      rw [hmem]
      exact ⟨⟨(by grind), hδ'⟩, .inl hγ'⟩
    · exact ⟨!(γ, δ'), by grind, by simp⟩
  · rintro ⟨q, hq, rfl⟩
    have hqs : q ∈ β ×ˢ α := isRelationOn_lexProd.predSet_subset _ hq
    simp only [mem_sprod_iff] at hqs
    obtain ⟨γ', -, δ', hδ', rfl⟩ := hqs
    simp only [omulPair_orderedPair]
    grind

/-- `omulMap α β` is a bijection from `β ×ˢ α` onto `α *ₒ β` -/
theorem isBijectionFromTo_omulMap (hα : Ordinal α) (hβ : Ordinal β) :
    omulMap α β !: β ×ˢ α ↔ α *ₒ β := by
  rw [isBijectionFromTo_iff]
  refine ⟨⟨isFunction_omulMap α β, dom_omulMap α β, (ran_omulMap hα hβ).symm ▸ subset_refl _⟩,
    fun p hp q hq h ↦ ?_, ran_omulMap hα hβ⟩
  have hR := (isStrictWellOrder_memRelOn fun x hx ↦ ordinal_of_mem hβ hx).lexProd
    (isStrictWellOrder_memRelOn fun x hx ↦ ordinal_of_mem hα hx)
  rwa [← collapseOn_lexProd hα hβ,
    (isStrictWellFounded₀_lexProd hα hβ).collapseOn_injOn hR.isExtensionalOn hp hq] at h

end Lex

section Omega

variable [HasOmega M] {m n : M}

@[simp, grind .]
theorem omul_mem_omega (hm : m ∈ (ω : M)) (hn : n ∈ (ω : M)) : m *ₒ n ∈ (ω : M) := by
  have hmo : Ordinal m := by grind
  refine omega_induction (A := fun n ↦ Class.Mem ω (m *ₒ n)) ?_ (fun n hn ih ↦ ?_) hn
  · simp [hmo]
  · simp only [Class.mem_iff] at ih ⊢
    rw [omul_succ hmo (ordinal_of_mem ordinal_omega hn)]
    exact oadd_mem_omega ih hm

theorem succ_omul_of_mem_omega (hm : m ∈ (ω : M)) (hn : n ∈ (ω : M)) :
    succ m *ₒ n = m *ₒ n +ₒ n := by
  have hmo : Ordinal m := by grind
  refine omega_induction_eq (G := fun n ↦ m *ₒ n +ₒ n) ?_
    (fun n hn ih ↦ ?_) hn
  · grind
  · have hno : Ordinal n := by grind
    -- both sides are `m *ₒ n +ₒ succ (m +ₒ n)`
    rw [omul_succ (ordinal_succ hmo) hno, ih, oadd_assoc (by grind) hno (ordinal_succ hmo),
      oadd_succ hno hmo, oadd_comm_of_mem_omega hn hm, omul_succ hmo hno,
      oadd_assoc (by grind) hmo (ordinal_succ hno), oadd_succ hmo hno]

/-- Multiplication is commutative on `ω` -/
theorem omul_comm_of_mem_omega (hm : m ∈ (ω : M)) (hn : n ∈ (ω : M)) : m *ₒ n = n *ₒ m := by
  have hmo : Ordinal m := by grind
  refine omega_induction_eq (G := fun n ↦ n *ₒ m) ?_ (fun n hn ih ↦ ?_) hn
  · simp [hmo]
  · rw [omul_succ hmo (ordinal_of_mem ordinal_omega hn), ih, succ_omul_of_mem_omega hn hm]

/-- `n *ₒ ω = ω` for a nonzero natural number `n` -/
theorem omul_omega_of_mem_omega (hn : n ∈ (ω : M)) (hn₀ : n ≠ ∅) : n *ₒ (ω : M) = ω := by
  have hno : Ordinal n := by grind
  ext z
  rw [mem_omul_of_nonZeroLimOrdinal_iff hno nonZeroLimOrdinal_omega]
  refine ⟨by grind, fun hz ↦ ⟨succ z, by grind, ?_⟩⟩
  -- `z ∈ succ z ≤ₒ n *ₒ succ z`
  have hzo : Ordinal z := by grind
  rcases mem_or_eq_of_ole (ole_omul_left hno (ordinal_succ hzo) hn₀) <;> grind

end Omega

end MemStructure

end FirstOrder.Language
