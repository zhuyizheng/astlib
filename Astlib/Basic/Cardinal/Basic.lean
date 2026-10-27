/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Ordinal.Omega
import Astlib.Basic.Ordinal.Add
import Astlib.Basic.Ordinal.Order
import Astlib.Basic.Ordinal.Function
import Astlib.Basic.Ordinal.OrderType
import Astlib.Basic.Ordinal.Pair
import Astlib.Basic.Axiom.ZF.Semantics
/-!
# Cardinals

A cardinal is an ordinal `κ` that is not the image of a smaller ordinal: there is no surjection
`f !: β ↠ κ` with `β ∈ κ`. In models of `KP`:

* `Cardinal` is a definable class;
* `cardinal_of_mem_omega`, `cardinal_omega`: natural numbers and `ω` are cardinals;
* `Cardinal.nonZeroLimOrdinal`: infinite cardinals are limit ordinals;
* `cardinal_sUnion`: a union of a set of cardinals is a cardinal;
* `card α`, the cardinality of an ordinal `α`, is the least ordinal mapped onto `α`.

In models of `ZF`:

* the ordinals that are images of `x` form a set (`exists_surjImage_subset`, Hartogs), and
  `csucc x`, the successor cardinal of `x`, is the union of their successors. For an ordinal
  `κ`, `csucc κ` is a cardinal above `κ` (`cardinal_csucc`, `olt_csucc`) and below every cardinal
  above `κ` (`csucc_ole`);
* `ℵ α` is defined by recursion: `ℵ ∅ = ω` (`aleph_empty`), `ℵ (succ α) = csucc (ℵ α)`
  (`aleph_succ`), and `ℵ α` is the union of `ℵ β` for `β ∈ α` at limits
  (`NonZeroLimOrdinal.aleph_eq`). The alephs are strictly increasing (`aleph_olt_aleph_iff`)
  infinite cardinals (`cardinal_aleph`), and every infinite cardinal is an aleph
  (`Cardinal.exists_aleph_eq`);
* Gödel's pairing function is a bijection from `ℵ α ×ˢ ℵ α` onto `ℵ α`
  (`isBijectionFromTo_goedelPairOfPair_aleph`);
* Hessenberg: every infinite ordinal `α` satisfies `α ×ˢ α ↪ α`
  (`exists_isInjectionFromTo_sprod_self`).
-/

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula Fin RudimentaryTerm MemStructure

namespace FirstOrder.Language

/-- The formula saying that `κ` is a cardinal: an ordinal with `¬(f !: β ↠ κ)` for all `β ∈ κ`
and all `f` -/
noncomputable def BoundedFormula.isCardinal {L : Language} [L.HasMem]
    [L.ExtraConstantsUnaryRelationsOnly] : L.BoundedFormula' 1 :=
  -- `[κ, β, f]`
  (ᵣ0 : L.RudimentaryTerm 1).isOrdinal.toBoundedFormula ⊓
    ∀'∈ &0 ∀' (∼((ᵣ2).isSurjectionFromTo (ᵣ1) (ᵣ0)) :
      L.DeltaZeroBoundedFormula 3).toBoundedFormula

namespace MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsKP M] {α β γ κ f : M}

/-- `κ` is a cardinal: an ordinal that is not the image of a smaller ordinal -/
def Cardinal : Class M := fun κ ↦ Ordinal κ ∧ ∀ β ∈ κ, ∀ f, ¬(f !: β ↠ κ)

omit [ModelsKP M] in
theorem cardinal_iff : Cardinal κ ↔ Ordinal κ ∧ ∀ β ∈ κ, ∀ f, ¬(f !: β ↠ κ) := .rfl

omit [ModelsKP M] in
@[grind .]
theorem Cardinal.ordinal (hκ : Cardinal κ) : Ordinal κ := hκ.left

omit [ModelsKP M] in
theorem Cardinal.not_isSurjectionFromTo (hκ : Cardinal κ) (hβ : β <ₒ κ) (f : M) :
    ¬(f !: β ↠ κ) :=
  hκ.right β hβ.mem f

instance : (Cardinal : Class M).Definable Set.univ := by
  unfold Cardinal
  infer_instance

@[simp, grind .]
theorem cardinal_empty : Cardinal (∅ : M) := ⟨ordinal_empty, by simp⟩

/-- A union of a set of cardinals is a cardinal -/
theorem cardinal_sUnion {X : M} (hX : ∀ κ ∈ X, Cardinal κ) : Cardinal (⋃₀ X) := by
  refine ⟨by grind, fun β hβ g hg ↦ ?_⟩
  simp only [mem_sUnion_iff] at hβ
  obtain ⟨κ, hκX, hβκ⟩ := hβ
  -- `β ↠ ⋃₀ X ↠ κ`
  obtain ⟨r, hr⟩ := exists_isSurjectionFromTo_of_subset (b := ⋃₀ X)
    (fun z hz ↦ by simp only [mem_sUnion_iff]; exact ⟨κ, hκX, hz⟩)
    (by grind)
  exact (hX κ hκX).not_isSurjectionFromTo (by grind) _ (hr.comp hg)

section Card

/-- The class of sets that are mapped onto `x` -/
def SurjectsOnto (x : M) : Class M := fun y ↦ ∃ f, f !: y ↠ x

/-- `SurjectsOnto x y` is definable in `x` and `y` -/
instance : Multiclass.Definable (fun ys : Fin 2 → M ↦ SurjectsOnto (ys 0) (ys 1)) Set.univ := by
  unfold SurjectsOnto
  infer_instance

/-- The cardinality of `x`: the least ordinal mapped onto `x` -/
noncomputable def card : ClassFunction M := fun x ↦ (SurjectsOnto x).omin

@[grind .]
theorem ordinal_card (x : M) : Ordinal (card x) := Class.ordinal_omin _

theorem surjectsOnto_self (x : M) : SurjectsOnto x x := ⟨_, isSurjectionFromTo_id x⟩

@[grind .]
theorem card_ole (hα : Ordinal α) : card α ≤ₒ α := Class.omin_ole hα (surjectsOnto_self α)

theorem exists_isSurjectionFromTo_card (hα : Ordinal α) : ∃ f, f !: card α ↠ α :=
  Class.omin_mem hα (surjectsOnto_self α)

/-- `card α` is a cardinal -/
@[grind .]
theorem cardinal_card (hα : Ordinal α) : Cardinal (card α) := by
  refine ⟨ordinal_card α, fun β hβ g hg ↦ ?_⟩
  -- `β ↠ card α ↠ α`
  obtain ⟨f, hf⟩ := exists_isSurjectionFromTo_card hα
  exact Class.not_of_mem_omin hα (surjectsOnto_self α) hβ ⟨f !∘ g, hf.comp hg⟩

end Card

section Omega

variable [HasOmega M] {n : M}

/-- Natural numbers are cardinals -/
@[grind .]
theorem cardinal_of_mem_omega (hn : n ∈ (ω : M)) : Cardinal n := by
  refine omega_induction cardinal_empty (fun n hn ih ↦ ?_) hn
  refine ⟨ordinal_succ (by grind), fun β hβ f hf ↦ ?_⟩
  have hβω : β ∈ (ω : M) := by grind
  rcases mem_omega_cases hβω with rfl | ⟨k, -, rfl⟩
  · exact succ_ne_empty n (eq_empty_of_isSurjectionFromTo_empty hf)
  · obtain ⟨g, hg⟩ := exists_isSurjectionFromTo_of_insert (notMem_self k) (notMem_self n)
      (by grind) hf
    exact ih.not_isSurjectionFromTo (olt_of_mem (by grind) (by grind)) g hg

/-- `ω` is a cardinal -/
@[grind .]
theorem cardinal_omega : Cardinal (ω : M) := by
  refine ⟨ordinal_omega, fun β hβ f hf ↦ ?_⟩
  -- compose with a surjection from `ω` onto `succ β`
  obtain ⟨r, hr⟩ :=
    exists_isSurjectionFromTo_of_subset (ordinal_omega.transitive _ (by grind)) (succ_ne_empty β)
  exact (cardinal_of_mem_omega (by grind)).not_isSurjectionFromTo
    (olt_succ (ordinal_of_mem ordinal_omega hβ)) _ (hr.comp hf)

/-- An ordinal `α ≥ ω` is in bijection with `succ α`:
`α = 1 +ₒ α ↔ disjUnion 1 α ↔ disjUnion α 1 ↔ α +ₒ 1 = succ α` -/
theorem exists_isBijectionFromTo_succ (hωα : (ω : M) ≤ₒ α) : ∃ g, g !: α ↔ succ α := by
  have hα : Ordinal α := by grind
  have h₁ : Ordinal (succ (∅ : M)) := by grind
  have hg₁ := isBijectionFromTo_oaddMap h₁ hα
  have hg₂ := isBijectionFromTo_oaddMap hα h₁
  simp only [one_oadd_of_omega_ole, hωα] at hg₁
  simp only [oadd_one, hα] at hg₂
  exact ⟨oaddMap α (succ ∅) !∘ disjUnionSwap _ _ !∘ (oaddMap (succ ∅) α)⁻¹,
    hg₂.comp ((isBijectionFromTo_disjUnionSwap _ _).comp hg₁.inv)⟩

/-- The cardinality of an infinite ordinal is infinite -/
@[grind .]
theorem omega_ole_card (hωα : (ω : M) ≤ₒ α) : (ω : M) ≤ₒ card α := by
  have hα : Ordinal α := by grind
  rw [← not_olt_iff (ordinal_card α) ordinal_omega]
  intro h
  -- `card α ↠ α ↠ ω`
  obtain ⟨f, hf⟩ := exists_isSurjectionFromTo_card hα
  obtain ⟨r, hr⟩ := exists_isSurjectionFromTo_of_subset
    (by rwa [← ole_iff_subset ordinal_omega hα])
    (fun h ↦ by simpa [h] using empty_mem_omega (M := M))
  exact cardinal_omega.not_isSurjectionFromTo h _ (hr.comp hf)

/-- Infinite cardinals are nonzero limit ordinals -/
@[grind .]
theorem Cardinal.nonZeroLimOrdinal (hκ : Cardinal κ) (hωκ : (ω : M) ≤ₒ κ) :
    NonZeroLimOrdinal κ := by
  by_contra h
  obtain ⟨α, hα, rfl⟩ := hκ.ordinal.exists_eq_succ (by grind) h
  -- `ω ≤ₒ α` since `ω ≤ₒ succ α` and `ω ≠ succ α`
  have hωα : (ω : M) ≤ₒ α := by grind
  obtain ⟨g, hg⟩ := exists_isBijectionFromTo_succ hωα
  exact hκ.not_isSurjectionFromTo (olt_succ hα) g hg.isSurjectionFromTo

end Omega

end MemStructure

namespace MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M]
  [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [ModelsZF M] {α β γ δ κ μ ν x f : M}

section CSucc

/-- `otMap` is definable: `otMap S` is the transitive collapse of `∈` on `S` -/
instance : (otMap : ClassFunction M).Definable Set.univ :=
  .of_iff (F := fun xs : Fin 2 → M ↦ ∃ R, memRelOn (xs 0) = R ∧ IsCollapseOn R (xs 0) (xs 1))
    fun S f ↦ by
      have hc := (isStrictWellFounded₀_memRelOn S).isStrictWellFounded.isCollapseOn_collapseOn
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine ⟨fun ⟨_, hR, h⟩ ↦ ?_, fun h ↦ ⟨_, rfl, h ▸ hc⟩⟩
      subst hR
      exact (isStrictWellFounded₀_memRelOn S).isStrictWellFounded.eq_of_isCollapseOn hc h

/-- The class of ordinals that are images of `x` -/
def SurjImage (x : M) : Class M := fun α ↦ Ordinal α ∧ ∃ f, f !: x ↠ α

/-- `SurjImage x α` is definable in `x` and `α` -/
instance : Multiclass.Definable (fun ys : Fin 2 → M ↦ SurjImage (ys 0) (ys 1)) Set.univ := by
  unfold SurjImage
  infer_instance

/-- Hartogs: the ordinals that are images of `x` form a set. An image `α` of `x` under `f` is the
range of the transitive collapse `f` of the well-founded relation on `x` induced by `f`, so these
ordinals are the image of the well-founded relations on `x` under replacement -/
theorem exists_surjImage_subset (x : M) : ∃ B : M, ∀ α, SurjImage x α → α ∈ B := by
  -- `F ![R, w]`: `w` is the range of the transitive collapse of `R` on `x`
  let F : Multiclass M 2 := fun xs ↦ ∃ f, IsCollapseOn (xs 0) x f ∧ xs 1 = ran f
  have hF (R w : M) : F ![R, w] ↔ ∃ f, IsCollapseOn R x f ∧ w = ran f := .rfl
  refine ⟨F ''₀ (𝒫 (x ×ˢ x) ∩₀ fun R ↦ IsStrictWellFounded R x), fun α ⟨hα, f, hf⟩ ↦ ?_⟩
  rw [mem_replacement_iff]
  · -- `f` is the transitive collapse of the pullback of `∈` along `f`, a well-founded relation
    refine ⟨memPullback f x, ?_, by rw [hF]; grind [hf.isCollapseOn_memPullback hα.transitive]⟩
    simp only [mem_comprehension_iff, mem_powerset_iff]
    grind [hf.isStrictWellFounded_memPullback]
  · -- `F` is functional on the well-founded relations: the collapse is unique
    intro R hR
    simp only [mem_comprehension_iff, hF] at hR ⊢
    have hc := hR.right.isCollapseOn_collapseOn
    exact ⟨ran (collapseOn R x), ⟨collapseOn R x, hc, rfl⟩,
      fun w ⟨g, hg, hw⟩ ↦ by grind [hR.right.eq_of_isCollapseOn hg hc]⟩

/-- The successor cardinal of `x`: the union of the successors of the ordinals that are images
of `x`, i.e. `⋃₀ S ∪ S` for the set `S` of these ordinals -/
noncomputable def csucc : ClassFunction M := fun x ↦
  ⋃₀ (Classical.choose (exists_surjImage_subset x) ∩₀ SurjImage x) ∪
    Classical.choose (exists_surjImage_subset x) ∩₀ SurjImage x

theorem mem_csucc_iff {y : M} : y ∈ csucc x ↔ ∃ α, SurjImage x α ∧ (y ∈ α ∨ y = α) := by
  have := Classical.choose_spec (exists_surjImage_subset x)
  simp only [csucc, mem_union_iff, mem_sUnion_iff, mem_comprehension_iff]
  grind

@[grind .]
theorem ordinal_csucc (x : M) : Ordinal (csucc x) := by
  have h {y : M} (hy : y ∈ csucc x) : Ordinal y := by
    simp only [mem_csucc_iff] at hy
    obtain ⟨α, ⟨hα, -⟩, hyα | rfl⟩ := hy <;> grind
  refine ⟨fun y hy z hz ↦ ?_, by grind⟩
  simp only [mem_csucc_iff] at hy ⊢
  obtain ⟨α, hα, hyα | rfl⟩ := hy
  · exact ⟨α, hα, .inl (hα.left.transitive _ hyα hz)⟩
  · exact ⟨y, hα, .inl hz⟩

instance : (csucc : ClassFunction M).Definable Set.univ := by
  refine ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦
    ∀ y, y ∈ xs 1 ↔ ∃ α, SurjImage (xs 0) α ∧ (y ∈ α ∨ y = α))
    (hF := by infer_instance) fun x v ↦ ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [eq_comm, MemStructure.ext_iff]
  simp [mem_csucc_iff, SurjImage]

/-- An ordinal image of `κ` is below `csucc κ` -/
theorem IsSurjectionFromTo.olt_csucc (hα : Ordinal α) (hf : f !: κ ↠ α) : α <ₒ csucc κ := by
  refine olt_of_mem (ordinal_csucc κ) ?_
  simp only [mem_csucc_iff]
  exact ⟨α, ⟨hα, f, hf⟩, .inr rfl⟩

/-- `κ <ₒ csucc κ` for an ordinal `κ` -/
@[grind .]
theorem olt_csucc (hκ : Ordinal κ) : κ <ₒ csucc κ :=
  (isSurjectionFromTo_id κ).olt_csucc hκ

/-- `csucc κ` is nonempty for an ordinal `κ` -/
@[grind .]
theorem csucc_ne_empty (hκ : Ordinal κ) : csucc κ ≠ ∅ :=
  fun h ↦ not_olt_empty κ (h ▸ olt_csucc hκ)

/-- `csucc x` is not an image of `x` -/
theorem not_isSurjectionFromTo_csucc (x f : M) : ¬(f !: x ↠ csucc x) :=
  fun hf ↦ olt_irrefl _ (hf.olt_csucc (ordinal_csucc x))

/-- Ordinals below `csucc κ` inject into an ordinal `κ` -/
theorem exists_isInjectionFromTo_of_olt_csucc (hκ : Ordinal κ) (hβ : β <ₒ csucc κ) :
    ∃ f, f !: β ↪ κ := by
  have h := hβ.mem
  simp only [mem_csucc_iff] at h
  obtain ⟨α, ⟨hα, f, hf⟩, hβα⟩ := h
  exact ⟨leastInv f κ α !∘ id β, (hf.leastInv hκ).comp ((isInjectionFromTo_id β).of_ran_subset
    (by grind))⟩

/-- `csucc κ` does not inject into an ordinal `κ` -/
theorem not_isInjectionFromTo_csucc (hκ : Ordinal κ) (f : M) : ¬(f !: csucc κ ↪ κ) := by
  intro hf
  obtain ⟨g, hg⟩ := exists_isSurjectionFromTo_of_isInjectionFromTo hf (csucc_ne_empty hκ)
  exact not_isSurjectionFromTo_csucc κ g hg

/-- `csucc κ` is a cardinal -/
@[grind .]
theorem cardinal_csucc (hκ : Ordinal κ) : Cardinal (csucc κ) := by
  refine ⟨ordinal_csucc κ, fun β hβ g hg ↦ ?_⟩
  -- `κ ↠ β ↠ csucc κ`
  obtain ⟨i, hi⟩ := exists_isInjectionFromTo_of_olt_csucc hκ (olt_of_mem (ordinal_csucc κ) hβ)
  have hne : β ≠ ∅ := by
    rintro rfl
    exact csucc_ne_empty hκ (eq_empty_of_isSurjectionFromTo_empty hg)
  obtain ⟨h, hh⟩ := exists_isSurjectionFromTo_of_isInjectionFromTo hi hne
  exact not_isSurjectionFromTo_csucc κ _ (hg.comp hh)

/-- `csucc κ` is below every cardinal above `κ` -/
@[grind .]
theorem csucc_ole (hμ : Cardinal μ) (hκμ : κ <ₒ μ) : csucc κ ≤ₒ μ := by
  rw [ole_iff_subset (ordinal_csucc κ) hμ.ordinal]
  intro y hy
  simp only [mem_csucc_iff] at hy
  obtain ⟨α, ⟨hα, f, hf⟩, hyα⟩ := hy
  -- `α ∈ μ`, since otherwise `κ ↠ α ↠ μ`
  have hαμ : α ∈ μ := by
    by_contra hαμ
    obtain ⟨r, hr⟩ := exists_isSurjectionFromTo_of_subset (hα.subset_of_notMem hμ.ordinal hαμ)
      (fun h ↦ by simpa [h] using hκμ.mem)
    exact hμ.not_isSurjectionFromTo hκμ _ (hr.comp hf)
  grind

end CSucc

section Aleph

/-- The aleph sequence: `ℵ ∅ = ω`, `ℵ (succ α) = csucc (ℵ α)`, and `ℵ α` is the union of `ℵ β`
for `β ∈ α` at limits `α` -/
noncomputable def aleph : ClassFunction M := ordRecursion' ω csucc (sUnion.comp ran)

@[inherit_doc] prefix:max "ℵ" => FirstOrder.Language.MemStructure.aleph

instance : (aleph : ClassFunction M).Definable Set.univ := by
  unfold aleph
  infer_instance

@[simp, grind =]
theorem aleph_empty : ℵ (∅ : M) = ω := ordRecursion'_empty

@[simp, grind =]
theorem aleph_succ (hα : Ordinal α) : ℵ (succ α) = csucc (ℵ α) := ordRecursion'_succ hα

/-- At a limit `α`, `ℵ α` is the union of `ℵ β` for `β ∈ α` -/
theorem NonZeroLimOrdinal.aleph_eq (hα : NonZeroLimOrdinal α) : ℵ α = ⋃₀ ran (aleph ↾₀ α) :=
  hα.ordRecursion'_eq

@[grind .]
theorem ordinal_aleph (α : M) : Ordinal (ℵ α) := by
  unfold aleph
  refine ordRecursion'_induction (A := Ordinal) ordinal_omega (fun _ _ _ ↦ ordinal_csucc _)
    (fun x ih ↦ ?_) α
  refine ordinal_sUnion fun y hy ↦ ?_
  simp only [mem_ran_toSetRestrictedTo_iff, isSetRestrictedTo_of_definable] at hy
  obtain ⟨β, hβ, rfl⟩ := hy
  exact ih β hβ

/-- At a limit `α`, `x ∈ ℵ α` iff `x ∈ ℵ β` for some `β ∈ α` -/
theorem NonZeroLimOrdinal.mem_aleph_iff (hα : NonZeroLimOrdinal α) :
    x ∈ ℵ α ↔ ∃ β ∈ α, x ∈ ℵ β := by
  simp only [hα.aleph_eq, mem_sUnion_iff, mem_ran_toSetRestrictedTo_iff,
    isSetRestrictedTo_of_definable α]
  grind

/-- At a limit `α`, `x <ₒ ℵ α` iff `x <ₒ ℵ β` for some `β <ₒ α` -/
theorem NonZeroLimOrdinal.olt_aleph_iff (hα : NonZeroLimOrdinal α) :
    x <ₒ ℵ α ↔ ∃ β <ₒ α, x <ₒ ℵ β := by
  constructor
  · intro hx
    have h := hx.mem
    simp only [hα.mem_aleph_iff] at h
    obtain ⟨β, hβ, hxβ⟩ := h
    exact ⟨β, olt_of_mem hα.ordinal hβ, olt_of_mem (ordinal_aleph β) hxβ⟩
  · rintro ⟨β, hβ, hxβ⟩
    refine olt_of_mem (ordinal_aleph α) ?_
    simp only [hα.mem_aleph_iff]
    exact ⟨β, hβ.mem, hxβ.mem⟩

/-- `ℵ α <ₒ ℵ (succ α)` -/
@[grind .]
theorem aleph_olt_aleph_succ (hα : Ordinal α) : ℵ α <ₒ ℵ (succ α) := by
  simp only [aleph_succ, hα]
  exact olt_csucc (ordinal_aleph α)

/-- `ℵ` is an order homomorphism of the ordinals -/
theorem isOrderHom_aleph : IsOrderHom (aleph : ClassFunction M) :=
  isOrderHom_of_succ_of_limit (fun _ hα ↦ aleph_olt_aleph_succ hα) fun _ hα _ ↦ hα.olt_aleph_iff

/-- `ℵ` is strictly increasing -/
@[simp, grind =]
theorem aleph_olt_aleph_iff (hα : Ordinal α) (hβ : Ordinal β) : ℵ β <ₒ ℵ α ↔ β <ₒ α :=
  isOrderHom_aleph.olt_iff hβ hα

@[simp, grind =]
theorem aleph_ole_aleph_iff (hα : Ordinal α) (hβ : Ordinal β) : ℵ β ≤ₒ ℵ α ↔ β ≤ₒ α := by
  grind

@[grind .]
theorem omega_ole_aleph (hα : Ordinal α) : (ω : M) ≤ₒ ℵ α := by
  rw [← aleph_empty, aleph_ole_aleph_iff hα ordinal_empty]
  exact empty_ole hα

/-- `ℵ α` is a cardinal -/
@[grind .]
theorem cardinal_aleph (hα : Ordinal α) : Cardinal (ℵ α) := by
  refine ordinal_induction (A := fun α ↦ Cardinal (ℵ α)) (fun α hα ih ↦ ?_) hα
  rcases hα.cases with rfl | ⟨β, hβ, rfl⟩ | hlim
  · grind
  · grind
  · rw [hlim.aleph_eq]
    refine cardinal_sUnion fun κ hκ ↦ ?_
    simp only [mem_ran_toSetRestrictedTo_iff, isSetRestrictedTo_of_definable] at hκ
    obtain ⟨β, hβ, rfl⟩ := hκ
    exact ih β (olt_of_mem hlim.ordinal hβ)

/-- Every infinite cardinal is an aleph -/
theorem Cardinal.exists_aleph_eq (hκ : Cardinal κ) (hωκ : (ω : M) ≤ₒ κ) :
    ∃ α, Ordinal α ∧ ℵ α = κ := by
  -- the least `α` with `κ ≤ₒ ℵ α` has `ℵ α = κ`; `α = κ` is such an `α`
  obtain ⟨hαo, hCα, hmin⟩ := Class.omin_spec (A := fun α ↦ κ ≤ₒ ℵ α) hκ.ordinal
    (isOrderHom_aleph.ole_apply hκ.ordinal)
  refine ⟨Class.omin (fun α ↦ κ ≤ₒ ℵ α), hαo, ole_antisymm ?_ hCα⟩
  rcases hαo.cases with h₀ | ⟨β, hβ, hsucc⟩ | hlim
  · grind
  · grind
  · by_contra h
    rw [not_ole_iff (ordinal_aleph _) hκ.ordinal, hlim.olt_aleph_iff] at h
    obtain ⟨β, hβ, hκβ⟩ := h
    grind

end Aleph

section Pair

/-- Gödel's pairing function maps `ℵ α ×ˢ ℵ α` into `ℵ α` -/
theorem goedelPairClosed_aleph (hα : Ordinal α) : GoedelPairClosed (ℵ α) := by
  refine ordinal_induction' (A := fun α ↦ GoedelPairClosed (ℵ α)) (fun β hβ γ hγ ↦ ?_)
    (fun δ hδ ih β hβ γ hγ ↦ ?_) (fun α hα ih β hβ γ hγ ↦ ?_) hα
  · simp only [aleph_empty] at hβ hγ ⊢
    exact goedelPair_mem_omega hβ hγ
  swap
  · simp only [hα.mem_aleph_iff] at hβ hγ ⊢
    obtain ⟨δ₁, hδ₁, hβ⟩ := hβ
    obtain ⟨δ₂, hδ₂, hγ⟩ := hγ
    have hlt : omax₂ δ₁ δ₂ <ₒ α := by
      grind [olt_of_mem hα.ordinal hδ₁, olt_of_mem hα.ordinal hδ₂]
    refine ⟨omax₂ δ₁ δ₂, hlt.mem, ih _ hlt β ?_ γ ?_⟩
    · grind [ole_omax₂_left, ole_iff_subset]
    · grind [ole_omax₂_right, ole_iff_subset]
  -- `!(β, γ)` lies in `ν ×ˢ ν` for `ν = succ (β ∪ γ ∪ ω) <ₒ ℵ (succ δ)`
  let ν := succ (β ∪ γ ∪ ω)
  rw [goedelPair_eq_collapseOn (μ := ν) (by grind) (by grind)]
  by_contra h
  -- `ν` injects into `ℵ δ`
  obtain ⟨e, he⟩ : ∃ e, e !: ν ↪ ℵ δ := by
    have hν : ν <ₒ ℵ (succ δ) :=
      ((cardinal_aleph (ordinal_succ hδ)).nonZeroLimOrdinal (by grind)).succ_olt
        (by grind [union_mem_of_mem, (show ℵ ∅ <ₒ ℵ (succ δ) by grind)])
    simp only [aleph_succ, hδ] at hν
    exact exists_isInjectionFromTo_of_olt_csucc (ordinal_aleph δ) hν
  -- `ℵ (succ δ) ⊆ C ﹫ !(β, γ) ⊆ ran C`, and `C⁻¹ : ran C ↪ ν ×ˢ ν` for the collapse `C`
  have hwo := isStrictWellOrder₀_goedelRel (μ := ν) (by grind)
  set C := collapseOn (goedelRel ν) (ν ×ˢ ν)
  have hwf := hwo.isStrictWellFounded₀
  have hC : C !: ν ×ˢ ν ↪ ran C := isInjectionFromTo_of_val hwf.isFunction_collapseOn
    hwf.dom_collapseOn (fun z hz ↦ by grind [hwf.isFunction_collapseOn.mem_ran_iff,
      hwf.dom_collapseOn]) fun z hz z' hz' ↦
      (hwf.collapseOn_injOn hwo.isExtensionalOn hz hz').mp
  have hp : !(β, γ) ∈ ν ×ˢ ν := by grind
  have hCp : C ﹫ !(β, γ) ∈ ran C := by
    rw [hwf.isFunction_collapseOn.mem_ran_iff, hwf.dom_collapseOn]
    exact ⟨_, hp, rfl⟩
  have h₁ := (isBijectionFromTo_ran_of_isInjectionFromTo hC).inv.isInjectionFromTo.restrict
    (subset_trans ((hwo.ordinal_collapseOn_val hp).subset_of_notMem (ordinal_aleph (succ δ)) h)
      (hwo.ordinal_ran_collapseOn.transitive _ hCp)) (subset_refl _)
  -- `ν ×ˢ ν ↪ ℵ δ ×ˢ ℵ δ ↪ ℵ δ`
  have hcl {m n : M} (hm : m ∈ ℵ δ) (hn : n ∈ ℵ δ) : goedelPair m n ∈ ℵ δ := by
    exact ih m hm n hn
  have h₂ := isInjectionFromTo_goedelPairOfPair (by grind) fun _ hm _ hn ↦ hcl hm hn
  obtain ⟨k, hk⟩ :=
    exists_isSurjectionFromTo_of_isInjectionFromTo ((h₂.comp (he.prodMap he)).comp h₁) (by grind)
  exact (cardinal_aleph (by grind)).not_isSurjectionFromTo (by grind) k hk

/-- Gödel's pairing function is a bijection from `ℵ α ×ˢ ℵ α` onto `ℵ α` -/
theorem isBijectionFromTo_goedelPairOfPair_aleph (hα : Ordinal α) :
    goedelPairOfPair ↾₀ (ℵ α ×ˢ ℵ α) !: ℵ α ×ˢ ℵ α ↔ ℵ α := by
  have hcl {m n : M} (hm : m ∈ ℵ α) (hn : n ∈ ℵ α) : goedelPair m n ∈ ℵ α := by
    exact goedelPairClosed_aleph hα m hm n hn
  have hinj := isInjectionFromTo_goedelPairOfPair (by grind) (fun _ hm _ hn ↦ hcl hm hn)
  refine ⟨hinj, hinj.isFunctionFromTo, eq_of_subset_of_subset hinj.isFunctionFromTo.ran_subset
    fun ξ hξ ↦ ?_⟩
  -- `ξ = goedelPair β γ` with `omax₂ β γ ≤ₒ ξ`, so `β, γ ∈ ℵ α`
  obtain ⟨β, γ, hβ, hγ, rfl⟩ := exists_goedelPair_eq (ξ := ξ) (by grind)
  have hlt : omax₂ β γ <ₒ ℵ α := by grind [omax₂_ole_goedelPair]
  simp only [mem_ran_toSetRestrictedTo_iff, isSetRestrictedTo_of_sigma]
  exact ⟨!(β, γ), by grind, by simp [goedelPairOfPair]⟩

end Pair

/-- Hessenberg: every infinite ordinal `α` satisfies `α ×ˢ α ↪ α`, as
`α ×ˢ α ↪ card α ×ˢ card α ↪ card α ⊆ α` with `card α = ℵ δ` -/
theorem exists_isInjectionFromTo_sprod_self (hωα : (ω : M) ≤ₒ α) : ∃ f, f !: α ×ˢ α ↪ α := by
  have hα : Ordinal α := by grind
  obtain ⟨δ, hδ, hcard⟩ := (cardinal_card hα).exists_aleph_eq (omega_ole_card hωα)
  obtain ⟨f, hf⟩ := exists_isSurjectionFromTo_card hα
  have hi := hf.leastInv (ordinal_card α)
  rw [← hcard] at hi
  have hsub : ℵ δ ⊆ α := by grind
  have hq := (isBijectionFromTo_goedelPairOfPair_aleph hδ).isInjectionFromTo.comp (hi.prodMap hi)
  exact ⟨_, ((isInjectionFromTo_id (ℵ δ)).of_ran_subset (by rwa [ran_id])).comp hq⟩

end MemStructure

end FirstOrder.Language
