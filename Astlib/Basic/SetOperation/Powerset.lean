/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Function
import Astlib.Basic.SetOperation.Comprehension
/-!
# Power sets

`𝒫 x` is the power set of `x` when it exists (`HasPowerset x`).
-/

open FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M]
  (x y : M)

def IsPowerset (a x : M) := ∀ z, z ∈ a ↔ z ⊆ x

noncomputable instance : Decidable (∃ a : M, IsPowerset a x) :=
  Classical.propDecidable _

/-- The power set of `x` -/
noncomputable def powerset : ClassFunction M := fun x ↦ dite (∃ a : M, IsPowerset a x) Classical.choose default

@[inherit_doc] prefix:100 "𝒫 " => powerset

class HasPowerset (x : M) : Prop where
  protected hasPowerset : ∃ a, IsPowerset a x

@[simp, grind =, push]
theorem mem_powerset_iff {x : M} [hx : HasPowerset x] (z : M) : z ∈ 𝒫 x ↔ z ⊆ x := by
  convert Classical.choose_spec hx.hasPowerset z
  simp [HasPowerset.hasPowerset, powerset]

/-- The power set is a `Π₁` class function: `w = 𝒫 x` iff `∀ z, z ∈ w ↔ z ⊆ x` -/
instance [∀ x : M, HasPowerset x] [Extensional M] : (powerset : ClassFunction M).Pi 1 Set.univ := by
  have h : MulticlassFunction.toMulticlass (fun xs : Fin 1 → M ↦ 𝒫 (xs 0)) =
      fun ys : Fin 2 → M ↦ ∀ z, z ∈ ys 1 ↔ z ⊆ ys 0 := by
    funext ys
    simp only [MulticlassFunction.toMulticlass, Function.comp_apply, eq_iff_iff]
    rw [eq_comm, MemStructure.ext_iff]
    simp [mem_powerset_iff]
  have : (MulticlassFunction.toMulticlass (fun xs : Fin 1 → M ↦ 𝒫 (xs 0))).Pi 1 Set.univ :=
    h ▸ inferInstance
  infer_instance

@[grind! .]
theorem mem_powerset_self [HasPowerset x] : x ∈ 𝒫 x := by grind

@[grind! .]
theorem empty_mem_powerset [RudClosed M] [HasPowerset x] : ∅ ∈ 𝒫 x := by grind

theorem powerset_mono {x y : M} (h : x ⊆ y) [HasPowerset x] [HasPowerset y] : 𝒫 x ⊆ 𝒫 y := by grind

@[simp]
theorem powerset_inj [Extensional M] {x y : M} [HasPowerset x] [HasPowerset y] :
    𝒫 x = 𝒫 y ↔ x = y := by
  refine ⟨fun h ↦ ?_, by simp +contextual⟩
  ext
  grind

end FirstOrder.Language.MemStructure

namespace FirstOrder.Language

open FirstOrder Language DeltaZeroBoundedFormula Fin

namespace RudimentaryTerm

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] {n : ℕ}

/-- `funSet₀〘a, b, c〙₃` is `{f ∈ c | f !: a → b}` -/
noncomputable def funSet₀ : L.RudimentaryTerm 3 :=
  ((ᵣ0).isFunctionFromTo (ᵣ1) (ᵣ2) : L.DeltaZeroBoundedFormula 3).comprehensionRudimentaryTerm

/-- `injSet₀〘a, b, c〙₃` is `{f ∈ c | f !: a ↪ b}` -/
noncomputable def injSet₀ : L.RudimentaryTerm 3 :=
  ((ᵣ0).isInjectionFromTo (ᵣ1) (ᵣ2) : L.DeltaZeroBoundedFormula 3).comprehensionRudimentaryTerm

/-- `surjSet₀〘a, b, c〙₃` is `{f ∈ c | f !: a ↠ b}` -/
noncomputable def surjSet₀ : L.RudimentaryTerm 3 :=
  ((ᵣ0).isSurjectionFromTo (ᵣ1) (ᵣ2) : L.DeltaZeroBoundedFormula 3).comprehensionRudimentaryTerm

/-- `bijSet₀〘a, b, c〙₃` is `{f ∈ c | f !: a ↔ b}` -/
noncomputable def bijSet₀ : L.RudimentaryTerm 3 :=
  ((ᵣ0).isInjectionFromTo (ᵣ1) (ᵣ2) ⊓ (ᵣ0).isSurjectionFromTo (ᵣ1) (ᵣ2) :
    L.DeltaZeroBoundedFormula 3).comprehensionRudimentaryTerm

/-- The `Π₁` formula `r = 𝒫 s` -/
noncomputable def isPowerset (r s : L.RudimentaryTerm n) : L.BoundedFormula' n :=
  ∀' (((&0 ∈₀ &2 ⟹ &0 ⊆₀ &1) ⊓ (&0 ⊆₀ &1 ⟹ &0 ∈₀ &2) : L.DeltaZeroBoundedFormula 3).substBoundRud
    ![ᵣ-1, s.castSucc, r.castSucc]).toBoundedFormula

instance (r s : L.RudimentaryTerm n) : (r.isPowerset s).Pi 1 := by
  unfold isPowerset; infer_instance

/-- The `Π₁` formula saying that `r` is the set of relations between `s` and `t` -/
noncomputable def isRelSet (r s t : L.RudimentaryTerm n) : L.BoundedFormula' n :=
  r.isPowerset (s ×ˢ t)

instance (r s t : L.RudimentaryTerm n) : (r.isRelSet s t).Pi 1 := by
  unfold isRelSet; infer_instance

/-- The `Π₁` formula saying that `r` is the set of relations on `s` -/
noncomputable def isRelSetOn (r s : L.RudimentaryTerm n) : L.BoundedFormula' n := r.isRelSet s s

instance (r s : L.RudimentaryTerm n) : (r.isRelSetOn s).Pi 1 := by
  unfold isRelSetOn; infer_instance

/-- The `Π₁` formula saying that `r` is the set of functions from `s` to `t` -/
noncomputable def isFunSet (r s t : L.RudimentaryTerm n) : L.BoundedFormula' n :=
  ∀' ((((&0 ∈₀ &3 ⟹ (ᵣ0).isFunctionFromTo (ᵣ1) (ᵣ2)) ⊓
    ((ᵣ0).isFunctionFromTo (ᵣ1) (ᵣ2) ⟹ &0 ∈₀ &3)) : L.DeltaZeroBoundedFormula 4).substBoundRud
      ![ᵣ-1, s.castSucc, t.castSucc, r.castSucc]).toBoundedFormula

instance (r s t : L.RudimentaryTerm n) : (r.isFunSet s t).Pi 1 := by
  unfold isFunSet; infer_instance

end RudimentaryTerm

namespace MemStructure

open RudimentaryTerm

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] {a b x R f p : M}

omit [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] in
theorem isPowerset_iff_eq [HasPowerset x] : IsPowerset p x ↔ p = 𝒫 x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ mem_powerset_iff⟩
  ext z
  simp only [h z, mem_powerset_iff]

/-- The set of relations between `a` and `b`, i.e. of subsets of `a ×ˢ b` -/
noncomputable def relSet (a b : M) : M := 𝒫 (a ×ˢ b)

/-- The set of relations on `a` -/
noncomputable def relSetOn : ClassFunction M := fun a ↦ relSet a a

omit [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] in
@[simp]
theorem mem_relSet_iff [HasPowerset (a ×ˢ b)] : R ∈ relSet a b ↔ R ⊆ a ×ˢ b :=
  mem_powerset_iff R

/-- `relSet` is a `Π₁` function: `𝒫` composed with `×ˢ` -/
instance [∀ x : M, HasPowerset x] :
    MulticlassFunction.Pi (fun ys : Fin 2 → M ↦ relSet (ys 0) (ys 1)) 1 Set.univ :=
  inferInstanceAs (MulticlassFunction.Pi (MulticlassFunction.comp
    (powerset : ClassFunction M) ![fun ys : Fin 2 → M ↦ ys 0 ×ˢ ys 1]) 1 Set.univ)

omit [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] in
@[simp]
theorem mem_relSetOn_iff [HasPowerset (a ×ˢ a)] : R ∈ relSetOn a ↔ R ⊆ a ×ˢ a :=
  mem_relSet_iff

/-- `relSetOn` is a `Π₁` class function -/
instance [∀ x : M, HasPowerset x] : (relSetOn : ClassFunction M).Pi 1 Set.univ where
  piMulticlassFunction := inferInstanceAs (MulticlassFunction.Pi (MulticlassFunction.comp
    (fun ys : Fin 2 → M ↦ relSet (ys 0) (ys 1)) ![fun xs ↦ xs 0, fun xs ↦ xs 0]) 1 Set.univ)

/-- The set of functions from `a` to `b` -/
noncomputable def funSet (a b : M) : M := funSet₀〘a, b, relSet a b〙₃

@[simp]
theorem mem_funSet_iff [HasPowerset (a ×ˢ b)] : f ∈ funSet a b ↔ f !: a → b := by
  rw [funSet, show (![a, b, relSet a b] : Fin 3 → M) = snoc ![a, b] (relSet a b) by simp, funSet₀,
    mem_realize_comprehensionRudimentaryTerm_iff_snoc, realize_isFunctionFromTo]
  suffices f ∈ relSet a b ∧ f !: a → b ↔ f !: a → b by simpa using this
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  simp only [mem_relSet_iff]
  exact h.subset_sprod

/-- `funSet` is a `Π₁` function: `w = funSet a b` iff `∀ f, f ∈ w ↔ f !: a → b` -/
instance [∀ x : M, HasPowerset x] :
    MulticlassFunction.Pi (fun ys : Fin 2 → M ↦ funSet (ys 0) (ys 1)) 1 Set.univ := by
  have h : MulticlassFunction.toMulticlass (fun ys : Fin 2 → M ↦ funSet (ys 0) (ys 1)) =
      fun zs : Fin 3 → M ↦ ∀ f, f ∈ zs 2 ↔ f !: zs 0 → zs 1 := by
    funext zs
    simp only [MulticlassFunction.toMulticlass, Function.comp_apply, eq_iff_iff]
    rw [eq_comm, MemStructure.ext_iff]
    simp [mem_funSet_iff]
  have : (MulticlassFunction.toMulticlass (fun ys : Fin 2 → M ↦ funSet (ys 0) (ys 1))).Pi 1
      Set.univ := h ▸ inferInstance
  infer_instance

/-- `a ↦ funSet a b` is definable -/
instance [∀ x : M, HasPowerset x] (b : M) :
    ClassFunction.Definable (fun a ↦ funSet a b) Set.univ :=
  .of_mem_iff fun _ _ ↦ mem_funSet_iff

/-- The set of injections from `a` to `b` -/
noncomputable def injSet (a b : M) : M := injSet₀〘a, b, relSet a b〙₃

@[simp]
theorem mem_injSet_iff [HasPowerset (a ×ˢ b)] : f ∈ injSet a b ↔ f !: a ↪ b := by
  rw [injSet, show (![a, b, relSet a b] : Fin 3 → M) = snoc ![a, b] (relSet a b) by simp, injSet₀,
    mem_realize_comprehensionRudimentaryTerm_iff_snoc, realize_isInjectionFromTo]
  suffices f ∈ relSet a b ∧ f !: a ↪ b ↔ f !: a ↪ b by simpa using this
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  simp only [mem_relSet_iff]
  exact h.isFunctionFromTo.subset_sprod

/-- `injSet` is a `Π₁` function: `w = injSet a b` iff `∀ f, f ∈ w ↔ f !: a ↪ b` -/
instance [∀ x : M, HasPowerset x] :
    MulticlassFunction.Pi (fun ys : Fin 2 → M ↦ injSet (ys 0) (ys 1)) 1 Set.univ := by
  have h : MulticlassFunction.toMulticlass (fun ys : Fin 2 → M ↦ injSet (ys 0) (ys 1)) =
      fun zs : Fin 3 → M ↦ ∀ f, f ∈ zs 2 ↔ f !: zs 0 ↪ zs 1 := by
    funext zs
    simp only [MulticlassFunction.toMulticlass, Function.comp_apply, eq_iff_iff]
    rw [eq_comm, MemStructure.ext_iff]
    simp [mem_injSet_iff]
  have : (MulticlassFunction.toMulticlass (fun ys : Fin 2 → M ↦ injSet (ys 0) (ys 1))).Pi 1
      Set.univ := h ▸ inferInstance
  infer_instance

/-- The set of surjections from `a` onto `b` -/
noncomputable def surjSet (a b : M) : M := surjSet₀〘a, b, relSet a b〙₃

@[simp]
theorem mem_surjSet_iff [HasPowerset (a ×ˢ b)] : f ∈ surjSet a b ↔ f !: a ↠ b := by
  rw [surjSet, show (![a, b, relSet a b] : Fin 3 → M) = snoc ![a, b] (relSet a b) by simp,
    surjSet₀, mem_realize_comprehensionRudimentaryTerm_iff_snoc, realize_isSurjectionFromTo]
  suffices f ∈ relSet a b ∧ f !: a ↠ b ↔ f !: a ↠ b by simpa using this
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  simp only [mem_relSet_iff]
  exact h.isFunctionFromTo.subset_sprod

/-- `surjSet` is a `Π₁` function: `w = surjSet a b` iff `∀ f, f ∈ w ↔ f !: a ↠ b` -/
instance [∀ x : M, HasPowerset x] :
    MulticlassFunction.Pi (fun ys : Fin 2 → M ↦ surjSet (ys 0) (ys 1)) 1 Set.univ := by
  have h : MulticlassFunction.toMulticlass (fun ys : Fin 2 → M ↦ surjSet (ys 0) (ys 1)) =
      fun zs : Fin 3 → M ↦ ∀ f, f ∈ zs 2 ↔ f !: zs 0 ↠ zs 1 := by
    funext zs
    simp only [MulticlassFunction.toMulticlass, Function.comp_apply, eq_iff_iff]
    rw [eq_comm, MemStructure.ext_iff]
    simp [mem_surjSet_iff]
  have : (MulticlassFunction.toMulticlass (fun ys : Fin 2 → M ↦ surjSet (ys 0) (ys 1))).Pi 1
      Set.univ := h ▸ inferInstance
  infer_instance

/-- The set of bijections from `a` onto `b` -/
noncomputable def bijSet (a b : M) : M := bijSet₀〘a, b, relSet a b〙₃

@[simp]
theorem mem_bijSet_iff [HasPowerset (a ×ˢ b)] : f ∈ bijSet a b ↔ f !: a ↔ b := by
  rw [bijSet, show (![a, b, relSet a b] : Fin 3 → M) = snoc ![a, b] (relSet a b) by simp, bijSet₀,
    mem_realize_comprehensionRudimentaryTerm_iff_snoc]
  suffices f ∈ relSet a b ∧ f !: a ↔ b ↔ f !: a ↔ b by simpa [IsBijectionFromTo] using this
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  simp only [mem_relSet_iff]
  exact h.isFunctionFromTo.subset_sprod

/-- `bijSet` is a `Π₁` function: `w = bijSet a b` iff `∀ f, f ∈ w ↔ f !: a ↔ b` -/
instance [∀ x : M, HasPowerset x] :
    MulticlassFunction.Pi (fun ys : Fin 2 → M ↦ bijSet (ys 0) (ys 1)) 1 Set.univ := by
  have h : MulticlassFunction.toMulticlass (fun ys : Fin 2 → M ↦ bijSet (ys 0) (ys 1)) =
      fun zs : Fin 3 → M ↦ ∀ f, f ∈ zs 2 ↔ f !: zs 0 ↔ zs 1 := by
    funext zs
    simp only [MulticlassFunction.toMulticlass, Function.comp_apply, eq_iff_iff]
    rw [eq_comm, MemStructure.ext_iff]
    simp [mem_bijSet_iff]
  have : (MulticlassFunction.toMulticlass (fun ys : Fin 2 → M ↦ bijSet (ys 0) (ys 1))).Pi 1
      Set.univ := h ▸ inferInstance
  infer_instance

variable {n : ℕ} (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree]
  (xs : Fin n → M)

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isPowerset :
    (r.isPowerset s)〘xs〙 ↔ IsPowerset (r〘xs〙 : M) s〘xs〙 := by
  simp [isPowerset, IsPowerset, snoc_nat, iff_def]

theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isRelSet :
    (r.isRelSet s t)〘xs〙 ↔ IsPowerset (r〘xs〙 : M) ((s〘xs〙 : M) ×ˢ (t〘xs〙 : M)) := by
  simp [isRelSet]

theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isRelSet_iff_eq
    [HasPowerset ((s〘xs〙 : M) ×ˢ t〘xs〙)] :
    (r.isRelSet s t)〘xs〙 ↔ (r〘xs〙 : M) = relSet (s〘xs〙 : M) (t〘xs〙 : M) := by
  simp only [realize_isRelSet, isPowerset_iff_eq, relSet]

theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isRelSetOn_iff_eq
    [HasPowerset ((s〘xs〙 : M) ×ˢ s〘xs〙)] :
    (r.isRelSetOn s)〘xs〙 ↔ (r〘xs〙 : M) = relSetOn (s〘xs〙 : M) :=
  realize_isRelSet_iff_eq r s s xs

theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isFunSet :
    (r.isFunSet s t)〘xs〙 ↔ ∀ f, f ∈ (r〘xs〙 : M) ↔ f !: (s〘xs〙 : M) → (t〘xs〙 : M) := by
  simp [isFunSet, snoc_nat, iff_def]

theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isFunSet_iff_eq
    [HasPowerset ((s〘xs〙 : M) ×ˢ t〘xs〙)] :
    (r.isFunSet s t)〘xs〙 ↔ (r〘xs〙 : M) = funSet (s〘xs〙 : M) (t〘xs〙 : M) := by
  simp [realize_isFunSet, MemStructure.ext_iff]

end MemStructure

end FirstOrder.Language
