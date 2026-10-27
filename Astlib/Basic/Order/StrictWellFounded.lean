/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Order.Basic
import Astlib.Basic.Axiom.KP.SigmaOneBoundedFormula.Semantics
/-!
# Strict well-founded relations

`IsStrictWellFounded R a` says that `R` is a relation on `a` such that every nonempty subset of
`a` has an `R`-minimal element. Such a relation is irreflexive and asymmetric
(`IsStrictWellFounded.isAsymmOn`), and supports induction (`IsStrictWellFounded.induction_subset`,
`IsStrictWellFounded.induction`) and recursion on `a` (`wfRecursionOn`): functions defined by
recursion are unique, and `wfRecursionOn R a G` is the one if it exists.

For class relations `R`, `R.IsStrictWellFounded₀` says that every nonempty definable class has an
`R`-minimal element, which gives induction for definable classes
(`Multiclass.IsStrictWellFounded₀.induction`). In models of `KP`, if moreover `R` is set-like and
the predecessor sets `R.predSet x` are given by a `Σ₁` class function, then a `Σ₁` class function
`G` defines a class function `wfRecursion G R` by
`wfRecursion G R x = G (wfRecursion G R ↾₀ R.predSet x)` (`wfRecursion_eq_of_modelsKP`).
-/

namespace FirstOrder.Language.MemStructure

open FirstOrder Language

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] {R S a b c x y : M}

/-- `R` is a strict well-founded relation on `a`: every nonempty subset of `a` has an
`R`-minimal element -/
def IsStrictWellFounded (R a : M) : Prop :=
  IsRelationOn R a ∧ ∀ b ⊆ a, b ≠ ∅ → ∃ x ∈ b, ∀ y ∈ b, ¬y [R] x

theorem isStrictWellFounded_iff :
    IsStrictWellFounded R a ↔
      IsRelationOn R a ∧ ∀ b ⊆ a, b ≠ ∅ → ∃ x ∈ b, ∀ y ∈ b, ¬y [R] x :=
  .rfl

namespace IsStrictWellFounded

@[grind →]
theorem isRelationOn (h : IsStrictWellFounded R a) : IsRelationOn R a := h.left

/-- Every nonempty subset has a minimal element -/
theorem exists_minimal [RudClosed M] (h : IsStrictWellFounded R a) (hba : b ⊆ a) (hx : x ∈ b) :
    ∃ x ∈ b, ∀ y ∈ b, ¬y [R] x :=
  h.right b hba fun e ↦ by simp [e] at hx

/-- A subrelation of a strict well-founded relation is strict well-founded -/
theorem mono (hS : IsStrictWellFounded S a) (hR : IsRelationOn R a) (hRS : R ⊆ S) :
    IsStrictWellFounded R a :=
  ⟨hR, fun b hba hb ↦ by grind [hS.right b hba hb]⟩

variable [RudClosed M] [Extensional M]

@[grind .]
theorem isAsymmOn (h : IsStrictWellFounded R a) : IsAsymmOn R a := fun x hx y hy hxy hyx ↦ by
  obtain ⟨z, hz, hmin⟩ :=
    h.exists_minimal (fun _ ↦ by grind) (mem_unorderedPair_left x y)
  grind

@[grind →]
theorem isIrreflOn (h : IsStrictWellFounded R a) : IsIrreflOn R a :=
  h.isAsymmOn.isIrreflOn

theorem irrefl (h : IsStrictWellFounded R a) (x : M) : ¬x [R] x := by
  grind [IsIrreflOn]

theorem asymm (h : IsStrictWellFounded R a) (hxy : x [R] y) : ¬y [R] x := by
  grind [IsAsymmOn]

/-- Well-founded induction: if `c` contains every `x ∈ a` whose `R`-predecessors all lie in `c`,
then `a ⊆ c` -/
theorem induction_subset (h : IsStrictWellFounded R a)
    (hc : ∀ x ∈ a, (∀ y, y [R] x → y ∈ c) → x ∈ c) : a ⊆ c := by
  intro x hx
  by_contra hxc
  obtain ⟨z, hz, hmin⟩ :=
    h.exists_minimal (fun _ ↦ by grind) (show x ∈ a \ c by grind)
  simp only [mem_sdiff_iff] at hz
  -- every `R`-predecessor of the minimal `z` lies in `c`, so `z ∈ c`
  refine hz.right (hc z hz.left fun y hyz ↦ ?_)
  grind

/-- The restriction of a strict well-founded relation to a subset is strict well-founded -/
theorem restrict₂ (h : IsStrictWellFounded R a) (hba : b ⊆ a) :
    IsStrictWellFounded (R ↾↾ b) b :=
  ⟨by grind, fun c hcb hc ↦ by grind [h.right c (subset_trans hcb hba) hc, rel_restrict₂_iff]⟩

end IsStrictWellFounded

variable [RudClosed M] [Extensional M]

@[simp, grind .]
theorem isStrictWellFounded_empty (a : M) : IsStrictWellFounded (∅ : M) a := by
  refine ⟨by grind, fun _ _ hb ↦ ?_⟩
  simp only [ne_empty_iff] at hb
  obtain ⟨x, hx⟩ := hb
  grind

section Constructions

/-- The concatenation of strict well-founded relations on disjoint sets is strict
well-founded -/
theorem IsStrictWellFounded.concat (hR : IsStrictWellFounded R a) (hS : IsStrictWellFounded S b)
    (hab : a ∩ b = ∅) : IsStrictWellFounded (concat R a S b) (a ∪ b) := by
  refine ⟨isRelationOn_concat hR.isRelationOn hS.isRelationOn, fun c hc hne ↦ ?_⟩
  by_cases hca : c ∩ a = ∅
  · obtain ⟨m, hm, hmin⟩ := hS.right c (fun z hz ↦ by grind) hne
    grind
  · obtain ⟨m, hm, hmin⟩ := hR.right (c ∩ a) (inter_subset_right _ _) hca
    simp only [mem_inter_iff] at hm
    grind

/-- Adding a maximum `x ∉ a` to a strict well-founded relation on `a` yields a strict
well-founded relation -/
theorem IsStrictWellFounded.insertMax (hR : IsStrictWellFounded R a) (hx : x ∉ a) :
    IsStrictWellFounded (insertMax R a x) (insert x a) := by
  have := hR.concat (isStrictWellFounded_empty {x}) (by ext; grind)
  rwa [union_comm, ← insert_eq] at this

/-- Adding a minimum `x ∉ a` to a strict well-founded relation on `a` yields a strict
well-founded relation -/
theorem IsStrictWellFounded.insertMin (hR : IsStrictWellFounded R a) (hx : x ∉ a) :
    IsStrictWellFounded (insertMin R a x) (insert x a) := by
  have := (isStrictWellFounded_empty {x}).concat hR (by ext; grind)
  rwa [← insert_eq] at this

/-- The lexicographic product of strict well-founded relations is strict well-founded -/
theorem IsStrictWellFounded.lexProd (hR : IsStrictWellFounded R a)
    (hS : IsStrictWellFounded S b) : IsStrictWellFounded (lexProd R a S b) (a ×ˢ b) := by
  refine ⟨isRelationOn_lexProd, fun c hc hne ↦ ?_⟩
  simp only [ne_empty_iff] at hne
  obtain ⟨z, hz⟩ := hne
  have hzc : z ∈ a ×ˢ b := hc hz
  simp only [mem_sprod_iff] at hzc
  obtain ⟨u, -, v, -, rfl⟩ := hzc
  -- `x₀` is a minimal first coordinate of `c`
  obtain ⟨x₀, hx₀, hmin₀⟩ := hR.exists_minimal (b := dom c)
    (fun x hx ↦ by rw [mem_dom_iff] at hx; grind) (x := u) (by grind)
  simp only [mem_dom_iff] at hx₀
  obtain ⟨y, hy⟩ := hx₀
  -- `y₀` is a minimal second coordinate of `c` among those with first coordinate `x₀`
  obtain ⟨y₀, hy₀, hmin₁⟩ := hS.exists_minimal (b := ran (c ∩ ({x₀} : M) ×ˢ b))
    (fun y hy ↦ by rw [mem_ran_iff] at hy; grind) (x := y) (by grind)
  simp only [mem_ran_iff] at hy₀
  obtain ⟨x, hx⟩ := hy₀
  simp only [mem_inter_iff] at hx
  obtain rfl : x = x₀ := by grind
  refine ⟨!(x, y₀), hx.left, fun w hw hwm ↦ ?_⟩
  specialize hc hw
  simp only [mem_sprod_iff] at hc
  obtain ⟨u', -, v', -, rfl⟩ := hc
  simp only [rel_lexProd_iff] at hwm
  rcases hwm.right.right with h | ⟨rfl, h⟩
  · exact hmin₀ u' (by grind) h
  · apply hmin₁ v' _ h
    grind

end Constructions

section Recursion

/-- Well-founded induction for a class admitting comprehension on `a` -/
theorem IsStrictWellFounded.induction (h : IsStrictWellFounded R a) {A : Class M}
    [HasComprehension a A] (hA : ∀ x ∈ a, (∀ y, y [R] x → A y) → A x) (hx : x ∈ a) : A x := by
  suffices x ∈ a ∩₀ A by grind
  refine h.induction_subset (fun x hx ih ↦ ?_) hx
  grind

/-- `f` is defined by `R`-recursion on `a` from `G`: a function on `a` such that
`f ﹫ x = G (f ↾ predSet R x)` for `x ∈ a` -/
def IsWFRecursionOn (R a : M) (G : ClassFunction M) (f : M) : Prop :=
  IsFunction f ∧ dom f = a ∧ ∀ x ∈ a, f ﹫ x = G (f ↾ predSet R x)

/-- Functions defined by well-founded recursion are unique -/
theorem IsStrictWellFounded.eq_of_isWFRecursionOn (h : IsStrictWellFounded R a)
    {G : ClassFunction M} {f g : M} (hf : IsWFRecursionOn R a G f)
    (hg : IsWFRecursionOn R a G g) : f = g := by
  obtain ⟨hf₁, hf₂, hf₃⟩ := hf
  obtain ⟨hg₁, hg₂, hg₃⟩ := hg
  have hpred : ∀ (x : M), predSet R x ⊆ a := h.isRelationOn.predSet_subset
  -- `dom (f ∩ g)` is where `f` and `g` agree
  have hagree {x : M} (hx : x ∈ a) : x ∈ dom (f ∩ g) ↔ f ﹫ x = g ﹫ x := by grind
  have hfg : a ⊆ dom (f ∩ g) := by
    refine h.induction_subset fun x hx ih ↦ ?_
    rw [hagree hx]
    rw [hf₃ x hx, hg₃ x hx]
    congr 1
    exact hf₁.restrict_eq_restrict hg₁ (hf₂ ▸ hpred x) (hg₂ ▸ hpred x) (by grind)
  grind

noncomputable instance (R a : M) (G : ClassFunction M) :
    Decidable (∃ f, IsWFRecursionOn R a G f) :=
  Classical.propDecidable _

/-- The function on `a` defined by `R`-recursion from `G`, if it exists -/
noncomputable def wfRecursionOn (R a : M) (G : ClassFunction M) : M :=
  dite (∃ f, IsWFRecursionOn R a G f) Classical.choose fun _ ↦ default

/-- A function defined by `R`-recursion on `a` from `G` is `wfRecursionOn R a G` -/
theorem IsWFRecursionOn.eq_wfRecursionOn (h : IsStrictWellFounded R a) {G : ClassFunction M}
    {f : M} (hf : IsWFRecursionOn R a G f) : f = wfRecursionOn R a G := by
  have hex : ∃ f, IsWFRecursionOn R a G f := ⟨f, hf⟩
  simp only [wfRecursionOn, hex]
  exact h.eq_of_isWFRecursionOn hf hex.choose_spec

/-- The recursive definition `wfRecursionOn R a G ﹫ x = G (wfRecursionOn R a G ↾ predSet R x)`,
provided that some function is defined by `R`-recursion on `a` from `G` -/
theorem IsStrictWellFounded.wfRecursionOn_val (h : IsStrictWellFounded R a)
    {G : ClassFunction M} (hex : ∃ f, IsWFRecursionOn R a G f) (hx : x ∈ a) :
    wfRecursionOn R a G ﹫ x = G (wfRecursionOn R a G ↾ predSet R x) := by
  obtain ⟨f, hf⟩ := hex
  rw [← hf.eq_wfRecursionOn h]
  exact hf.right.right x hx

end Recursion

end FirstOrder.Language.MemStructure

namespace FirstOrder.Language

open FirstOrder Language Fin DeltaZeroBoundedFormula

namespace RudimentaryTerm

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] {n : ℕ}

/-- The `Δ₀` body of strict well-foundedness: if the last variable `b` is a nonempty subset of
`s`, then `b` has an `r`-minimal element -/
noncomputable def hasMinimal (r s : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula (n + 1) :=
  ((&2 ⊆₀ &1 ⟹ (∃₀∈ &2 ⊤) ⟹ ∃₀∈ &2 ∀₀∈ &2 ∼((ᵣ0).hasMemOrderedPair (ᵣ4) (ᵣ3)) :
    L.DeltaZeroBoundedFormula 3)).substBoundRud ![r.castSucc, s.castSucc, ᵣ-1]

/-- The `Π₁` formula saying that `r` is a strict well-founded relation on `s` -/
noncomputable def isStrictWellFounded (r s : L.RudimentaryTerm n) : L.BoundedFormula' n :=
  ∀' (r.castSucc.isRelationOn s.castSucc ⊓ r.hasMinimal s).toBoundedFormula

instance (r s : L.RudimentaryTerm n) : (r.isStrictWellFounded s).Pi 1 := by
  unfold isStrictWellFounded; infer_instance

end RudimentaryTerm

namespace MemStructure

open RudimentaryTerm

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] {n : ℕ}
  (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] (xs : Fin n → M)

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_hasMinimal (b : M) :
    (r.hasMinimal s).toBoundedFormula 〘snoc xs b〙 ↔
      b ⊆ s〘xs〙 → b ≠ ∅ → ∃ x ∈ b, ∀ y ∈ b, ¬y [(r〘xs〙 : M)] x := by
  simp [hasMinimal, snoc_nat, ne_empty_iff]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isStrictWellFounded :
    (r.isStrictWellFounded s)〘xs〙 ↔ IsStrictWellFounded (r〘xs〙 : M) s〘xs〙 := by
  simp [isStrictWellFounded, isStrictWellFounded_iff, forall_and]

/-- `IsStrictWellFounded` is definable -/
instance : Multiclass.Definable (fun ys : Fin 2 → M ↦ IsStrictWellFounded (ys 0) (ys 1))
    Set.univ := by
  have h : (fun ys : Fin 2 → M ↦ IsStrictWellFounded (ys 0) (ys 1)) =
      ((ᵣ0 : L.RudimentaryTerm 2).isStrictWellFounded (ᵣ1)).multiclass := by
    funext ys
    simp
  rw [h]
  infer_instance

end MemStructure

end FirstOrder.Language

namespace FirstOrder.Language.MemStructure

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula RudimentaryTerm Fin

variable {L : Language} {M : Type*} [L.MemStructure M]

section ClassInduction

/-- A class relation `R`, with `R ![y, x]` read as `y R x`, is well-founded for definable
classes: every nonempty definable class has an `R`-minimal element -/
def Multiclass.IsStrictWellFounded₀ (R : Multiclass M 2) : Prop :=
  ∀ (A : Class M) [A.Definable Set.univ], (∃ x, A x) → ∃ x, A x ∧ ∀ y, R ![y, x] → ¬A y

/-- Well-founded induction along a class relation for definable classes -/
theorem Multiclass.IsStrictWellFounded₀.induction {R : Multiclass M 2} (hR : R.IsStrictWellFounded₀)
    {A : Class M} [A.Definable Set.univ] (h : ∀ x, (∀ y, R ![y, x] → A y) → A x) (x : M) :
    A x := by
  by_contra hx
  obtain ⟨z, hz, hmin⟩ := hR (∼A) ⟨x, by simpa [Class.not_iff] using hx⟩
  simp only [Class.not_iff, not_not] at hz hmin
  grind

/-- A class relation `R`, with `R ![y, x]` read as `y R x`, is well-founded for sets: every
nonempty set has an `R`-minimal element -/
def Multiclass.IsStrictWellFounded (R : Multiclass M 2) : Prop :=
  ∀ b : M, (∃ x, x ∈ b) → ∃ x ∈ b, ∀ y, R ![y, x] → y ∉ b

end ClassInduction

section ClassRecursion

variable [Inhabited M]

variable [L.ExtraConstantsUnaryRelationsOnly]

/-- `F` is defined by recursion from `G` along the set-like class relation `R` -/
def IsWFRecursion (F G : ClassFunction M) (R : Multiclass M 2) :=
  R.IsSetLike ∧ (∀ x, IsSetRestrictedTo F x) ∧ ∀ x, F x = G (F ↾₀ R.predSet x)

noncomputable instance (G : ClassFunction M) (R : Multiclass M 2) :
    Decidable (∃ F : ClassFunction M, IsWFRecursion F G R) :=
  Classical.propDecidable _

/-- The class function defined by recursion from `G` along `R` -/
noncomputable def wfRecursion (G : ClassFunction M) (R : Multiclass M 2) : ClassFunction M :=
  dite (∃ F, IsWFRecursion F G R) Classical.choose fun _ _ ↦ default

variable {R : Multiclass M 2} {G : ClassFunction M}

theorem IsWFRecursion.isSetLike {F : ClassFunction M} (h : IsWFRecursion F G R) :
    R.IsSetLike :=
  h.left

theorem IsWFRecursion.isSetRestrictedTo {F : ClassFunction M} (h : IsWFRecursion F G R)
    (x : M) : IsSetRestrictedTo F x :=
  h.right.left x

theorem IsWFRecursion.eq {F : ClassFunction M} (h : IsWFRecursion F G R) (x : M) :
    F x = G (F ↾₀ R.predSet x) :=
  h.right.right x

/-- `f` is an approximation of the class function defined by recursion from `G` along `R`: a
function whose domain is closed under `R`-predecessors satisfying the recursive definition -/
def IsWFApprox (f : M) (G : ClassFunction M) (R : Multiclass M 2) : Prop :=
  IsFunction f ∧ (∀ x ∈ dom f, R.predSet x ⊆ dom f) ∧ ∀ x ∈ dom f, f ﹫ x = G (f ↾ R.predSet x)

theorem IsWFApprox.isFunction {f : M} (hf : IsWFApprox f G R) : IsFunction f := hf.left

theorem IsWFApprox.closedDom {f x : M} (hf : IsWFApprox f G R) (hx : x ∈ dom f) :
    R.predSet x ⊆ dom f :=
  hf.right.left x hx

/-- An approximation satisfies the recursive definition -/
theorem IsWFApprox.val_eq {f x : M} (hf : IsWFApprox f G R) (hx : x ∈ dom f) :
    f ﹫ x = G (f ↾ R.predSet x) :=
  hf.right.right x hx

variable [ModelsKP M]

/-- The approximations of a `Σ₁` class function form a `Σ₁` class if `R.predSet` is `Σ₁` -/
instance (G : ClassFunction M) (R : Multiclass M 2) [R.predSet.Sigma 1 Set.univ]
    [G.Sigma 1 Set.univ] : Class.Sigma (fun f ↦ IsWFApprox f G R) 1 Set.univ := by
  -- the closure of `dom f` under `R.predSet` and the recursive definition separately
  have : Class.Sigma (fun f : M ↦ ∀ x ∈ dom f, R.predSet x ⊆ dom f) 1 Set.univ := inferInstance
  unfold IsWFApprox
  infer_instance

/-- The approximations of a definable class function form a definable class if `R.predSet` is
definable -/
instance (G : ClassFunction M) (R : Multiclass M 2) [R.predSet.Definable Set.univ]
    [G.Definable Set.univ] : Class.Definable (fun f ↦ IsWFApprox f G R) Set.univ := by
  -- `[f, d, x, p, r, v]` as in the `Σ₁` case
  let B : Multiclass M 6 := ((&3 ⊆₀ &1) ⊓ (&0 =₀ &1).substBoundRud ![ᵣ4, ᵣ0 ↾ ᵣ3] ⊓
      (&0 =₀ &1).substBoundRud ![ᵣ5, ᵣ0 ﹫ ᵣ2] :
      L.DeltaZeroBoundedFormula 6).toBoundedFormula.multiclass ⊓
    (R.predSet : Multiclass M 2).remap ![2, 3] ⊓ (G : Multiclass M 2).remap ![4, 5]
  let C : Multiclass M 1 := (((&0 =₀ &1).substBoundRud ![ᵣ1, (ᵣ0).dom] ⊓ (ᵣ0).isFunction :
    L.DeltaZeroBoundedFormula 2).toBoundedFormula.multiclass ⊓ B.ex.ex.ex.allMem 1).ex
  have hC : (fun f ↦ IsWFApprox f G R : Class M) = (C : Class M) := by
    ext f
    simp [B, C, IsWFApprox, Matrix.empty_eq, eq_comm, forall_and]
  rw [hC]
  infer_instance

/-- Two approximations agree on their common domain -/
theorem IsWFApprox.val_eq_val (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike)
    {f f' x : M} (hf : IsWFApprox f G R) (hf' : IsWFApprox f' G R) (hx : x ∈ dom f)
    (hx' : x ∈ dom f') : f ﹫ x = f' ﹫ x := by
  -- `S` is the set of points of the common domain where `f` and `f'` differ
  let S := (dom f ∩ dom f') \ dom (f ∩ f')
  have hSmem (z : M) : z ∈ S ↔ z ∈ dom f ∧ z ∈ dom f' ∧ f ﹫ z ≠ f' ﹫ z := by
    simp only [S, mem_sdiff_iff]
    grind [IsWFApprox.isFunction]
  by_contra hne
  -- take an `R`-minimal point `z` where `f` and `f'` differ
  obtain ⟨z, hz, hmin⟩ := hR (toClass S) ⟨x, by simp [toClass, hSmem, hx, hx', hne]⟩
  simp only [toClass, Class.mem_iff, hSmem] at hz hmin
  obtain ⟨hz₁, hz₂, hz₃⟩ := hz
  apply hz₃
  rw [hf.val_eq hz₁, hf'.val_eq hz₂]
  congr 1
  refine hf.isFunction.restrict_eq_restrict hf'.isFunction (hf.closedDom hz₁)
    (hf'.closedDom hz₂) fun y hy ↦ ?_
  by_contra hy'
  apply hmin y (by rwa [hS.mem_predSet_iff] at hy)
  exact ⟨hf.closedDom hz₁ hy, hf'.closedDom hz₂ hy, hy'⟩

/-- An approximation can be extended by a point whose predecessors lie in its domain -/
theorem IsWFApprox.exists_extend {h x : M} (hh : IsWFApprox h G R) (hx : R.predSet x ⊆ dom h) :
    ∃ g, IsWFApprox g G R ∧ x ∈ dom g ∧ dom h ⊆ dom g := by
  by_cases hxh : x ∈ dom h
  · exact ⟨h, hh, hxh, subset_refl _⟩
  let g := h ∪ {!(x, G (h ↾ R.predSet x))}
  have hg (a b : M) : !(a, b) ∈ g ↔ !(a, b) ∈ h ∨ (a = x ∧ b = G (h ↾ R.predSet x)) := by grind
  have hgfun : IsFunction g := ⟨by grind [hh.isFunction], by grind [hh.isFunction.eq]⟩
  have hgdom (a : M) : a ∈ dom g ↔ a ∈ dom h ∨ a = x := by
    simp only [mem_dom_iff, hg]
    grind
  have hgval (z : M) (hz : z ∈ dom h) : g ﹫ z = h ﹫ z := by grind
  have hgres (z : M) (hz : z ⊆ dom h) : g ↾ z = h ↾ z := by
    apply hgfun.restrict_eq_restrict hh.isFunction _ hz <;> grind
  refine ⟨g, ?_, by grind, fun z hz ↦ by grind⟩
  refine ⟨hgfun, fun z hz y hy ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hgdom]
    left
    rw [hgdom z] at hz
    rcases hz with hz | rfl
    · exact hh.closedDom hz hy
    · exact hx hy
  · rw [hgdom z] at hz
    rcases hz with hz | rfl
    · rw [hgval z hz, hh.val_eq hz, hgres _ (hh.closedDom hz)]
    · rw [hgres _ hx]
      grind

/-- The union of a set of approximations is an approximation -/
theorem isWFApprox_sUnion (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike) {B : M}
    (hB : ∀ f ∈ B, IsWFApprox f G R) : IsWFApprox (⋃₀ B) G R := by
  have hfun : IsFunction (⋃₀ B) := by
    refine ⟨fun z hz ↦ ?_, fun a b₁ b₂ h₁ h₂ ↦ ?_⟩
    · simp only [mem_sUnion_iff] at hz
      obtain ⟨f, hf, hz⟩ := hz
      exact (hB f hf).isFunction.isRelation hz
    · simp only [mem_sUnion_iff] at h₁ h₂
      obtain ⟨f₁, hf₁, h₁⟩ := h₁
      obtain ⟨f₂, hf₂, h₂⟩ := h₂
      have hB₁ : IsWFApprox f₁ G R := hB f₁ hf₁
      have hB₂ : IsWFApprox f₂ G R := hB f₂ hf₂
      rw [← hB₁.isFunction.val_eq_of_rel h₁, ← hB₂.isFunction.val_eq_of_rel h₂]
      exact hB₁.val_eq_val hR hS hB₂ (by grind) (by grind)
  have hval (f : M) (hf : f ∈ B) (z : M) (hz : z ∈ dom f) : (⋃₀ B) ﹫ z = f ﹫ z := by grind
  have hdom (z : M) : z ∈ dom (⋃₀ B) ↔ ∃ f ∈ B, z ∈ dom f := by grind
  refine ⟨hfun, fun z hz w hw ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hdom] at hz ⊢
    obtain ⟨f, hf, hzf⟩ := hz
    exact ⟨f, hf, (hB f hf).closedDom hzf hw⟩
  · rw [hdom] at hz
    obtain ⟨f, hf, hzf⟩ := hz
    specialize hB f hf
    rw [hval f hf z hzf, hB.val_eq hzf]
    congr 1
    refine hB.isFunction.restrict_eq_restrict hfun (hB.closedDom hzf) ?_ ?_
    · intro w hw
      rw [hdom]
      exact ⟨f, hf, hB.closedDom hzf hw⟩
    · intro w hw
      exact (hval f hf w (hB.closedDom hzf hw)).symm

/-- Being an approximation defined at a point is `Σ₁` -/
theorem exists_multiclass_isWFApprox [R.predSet.Sigma 1 Set.univ] [G.Sigma 1 Set.univ] :
    ∃ F : Multiclass M 2, F.Sigma 1 Set.univ ∧ ∀ y f, F ![y, f] ↔ IsWFApprox f G R ∧ y ∈ dom f := by
  let Ap : Class M := fun f ↦ IsWFApprox f G R
  exact ⟨fun xs ↦ Ap (xs 1) ∧ xs 0 ∈ dom (xs 1), inferInstance, fun y f ↦ .rfl⟩

/-- Approximations defined at each point of a set `s` combine into one defined on `s` -/
theorem exists_isWFApprox_subset_of (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] [G.Sigma 1 Set.univ] {s : M}
    (h : ∀ y ∈ s, ∃ f, IsWFApprox f G R ∧ y ∈ dom f) :
    ∃ f, IsWFApprox f G R ∧ s ⊆ dom f := by
  obtain ⟨F, hF, hF'⟩ := exists_multiclass_isWFApprox (R := R) (G := G)
  -- collect approximations defined at the elements of `s`
  obtain ⟨B, hB₁, hB₂⟩ := exists_strong_collection_of_modelsKP F s (by simpa [hF'] using h)
  simp only [hF'] at hB₁ hB₂
  refine ⟨⋃₀ B, isWFApprox_sUnion hR hS fun f hf ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨-, -, hf', -⟩ := hB₂ f hf
    grind
  · obtain ⟨f, hf, -, hyf⟩ := hB₁ y hy
    grind

/-- The existence of approximations if `R.predSet` and `G` are `Σ₁` -/
theorem exists_isWFApprox (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] [G.Sigma 1 Set.univ] (x : M) :
    ∃ f, IsWFApprox f G R ∧ x ∈ dom f := by
  obtain ⟨F, hF, hF'⟩ := exists_multiclass_isWFApprox (R := R) (G := G)
  have hFex (x : M) : (F.ex : Class M) x ↔ ∃ f, IsWFApprox f G R ∧ x ∈ dom f := by
    simp [hF']
  rw [← hFex]
  refine hR.induction (fun x ih ↦ ?_) x
  simp only [hFex] at ih ⊢
  obtain ⟨h, hh, hxh⟩ := exists_isWFApprox_subset_of hR hS
    fun y hy ↦ ih y (by rwa [hS.mem_predSet_iff] at hy)
  obtain ⟨g, hg, hxg, -⟩ := hh.exists_extend hxh
  grind

/-- There is an approximation defined on any given set -/
theorem exists_isWFApprox_subset (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] [G.Sigma 1 Set.univ] (s : M) :
    ∃ f, IsWFApprox f G R ∧ s ⊆ dom f :=
  exists_isWFApprox_subset_of hR hS fun y _ ↦ exists_isWFApprox hR hS y

/-- Approximations of the recursion from `G` along `R` exist on every set -/
def HasWFApprox (G : ClassFunction M) (R : Multiclass M 2) : Prop :=
  ∀ s, ∃ f, IsWFApprox f G R ∧ s ⊆ dom f

/-- There are approximations on every set if `R.predSet` and `G` are `Σ₁` -/
theorem hasWFApprox (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike) [R.predSet.Sigma 1 Set.univ]
    [G.Sigma 1 Set.univ] : HasWFApprox G R :=
  exists_isWFApprox_subset hR hS

namespace HasWFApprox

variable (hG : HasWFApprox G R)
include hG

theorem exists_isWFApprox (x : M) : ∃ f, IsWFApprox f G R ∧ x ∈ dom f := by
  obtain ⟨f, hf, hx⟩ := hG {x}
  exact ⟨f, hf, hx (by simp)⟩

/-- Class functions defined by recursion from `G` along `R` are unique -/
theorem eq_of_isWFRecursion (hR : R.IsStrictWellFounded₀) {F₁ F₂ : ClassFunction M}
    (h₁ : IsWFRecursion F₁ G R) (h₂ : IsWFRecursion F₂ G R) : F₁ = F₂ := by
  have hS : R.IsSetLike := h₁.isSetLike
  funext x
  by_contra hne
  -- the domain `t` of an approximation defined at `x` is closed under `R`-predecessors
  obtain ⟨f, hf, hx⟩ := hG.exists_isWFApprox x
  set t := dom f
  have hagree {z : M} (hz : z ∈ t) : z ∈ dom (F₁ ↾₀ t ∩ F₂ ↾₀ t) ↔ F₁ z = F₂ z := by
    have h₁t : IsSetRestrictedTo F₁ t := h₁.isSetRestrictedTo t
    have h₂t : IsSetRestrictedTo F₂ t := h₂.isSetRestrictedTo t
    grind [isFunction_toSetRestrictedTo, dom_toSetRestrictedTo, val_toSetRestrictedTo]
  -- take an `R`-minimal point `z ∈ t` where `F₁` and `F₂` differ
  obtain ⟨z, hz, hmin⟩ := hR (toClass (t \ dom (F₁ ↾₀ t ∩ F₂ ↾₀ t)))
    ⟨x, by simp [toClass, hx, hagree hx, hne]⟩
  simp only [toClass, Class.mem_iff, mem_sdiff_iff] at hz hmin
  rw [hagree hz.left] at hz
  apply hz.right
  rw [h₁.eq z, h₂.eq z]
  congr 1
  have h₂z : IsSetRestrictedTo F₂ (R.predSet z) := h₂.isSetRestrictedTo (R.predSet z)
  refine toSetRestrictedTo_eq (isFunction_toSetRestrictedTo h₂z) (dom_toSetRestrictedTo h₂z)
    fun y hy ↦ ?_
  rw [val_toSetRestrictedTo h₂z hy]
  have hyt : y ∈ t := hf.closedDom hz.left hy
  by_contra hy'
  apply hmin y (by rwa [hS.mem_predSet_iff] at hy)
  grind

/-- A class function defined by recursion from `G` along `R` is `wfRecursion G R` -/
theorem eq_wfRecursion (hR : R.IsStrictWellFounded₀) {F : ClassFunction M}
    (hFG : IsWFRecursion F G R) : F = wfRecursion G R := by
  have h : ∃ F, IsWFRecursion F G R := ⟨F, hFG⟩
  simp only [wfRecursion, h]
  exact hG.eq_of_isWFRecursion hR hFG (Classical.choose_spec h)

/-- Choosing an approximation defined at each point gives a class function defined by
recursion from `G` along `R` -/
theorem isWFRecursion_of_isWFApprox (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike)
    {F : ClassFunction M} (hF₁ : ∀ x, IsWFApprox (F x) G R) (hF₂ : ∀ x, x ∈ dom (F x)) :
    IsWFRecursion (fun x ↦ F x ﹫ x) G R := by
  -- an approximation `f` defined on `s` restricts to `fun x ↦ F x ﹫ x` on `s`
  have hres {f s : M} (hf : IsWFApprox f G R) (hs : s ⊆ dom f) :
      IsFunction (f ↾ s) ∧ dom (f ↾ s) = s ∧ ∀ y ∈ s, (f ↾ s) ﹫ y = F y ﹫ y := by
    refine ⟨hf.isFunction.restrict s, dom_restrict_of_subset hf.isFunction hs, fun y hy ↦ ?_⟩
    specialize hs hy
    rw [val_restrict _ hf.isFunction hy hs]
    exact hf.val_eq_val hR hS (hF₁ y) hs (hF₂ y)
  refine ⟨hS, fun s ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨f, hf, hs⟩ := hG s
    exact ⟨f ↾ s, hres hf hs⟩
  · specialize hF₁ x
    specialize hF₂ x
    obtain ⟨h₁, h₂, h₃⟩ := hres hF₁ (hF₁.closedDom hF₂)
    dsimp only
    rw [hF₁.val_eq hF₂, toSetRestrictedTo_eq h₁ h₂ h₃]

/-- The well-founded recursion theorem: some class function is defined by recursion from `G`
along `R` -/
theorem exists_isWFRecursion (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike) :
    ∃ F, IsWFRecursion F G R := by
  choose F hF₁ hF₂ using hG.exists_isWFApprox
  exact ⟨fun x ↦ F x ﹫ x, hG.isWFRecursion_of_isWFApprox hR hS hF₁ hF₂⟩

/-- `wfRecursion G R` agrees with every approximation -/
theorem wfRecursion_eq_val (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike) {f x : M}
    (hf : IsWFApprox f G R) (hx : x ∈ dom f) : wfRecursion G R x = f ﹫ x := by
  choose F hF₁ hF₂ using hG.exists_isWFApprox
  rw [← hG.eq_wfRecursion hR (hG.isWFRecursion_of_isWFApprox hR hS hF₁ hF₂)]
  exact (hF₁ x).val_eq_val hR hS hf (hF₂ x) hx

/-- `wfRecursion G R` is defined by recursion from `G` along `R` -/
theorem isWFRecursion_wfRecursion (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike) :
    IsWFRecursion (wfRecursion G R) G R := by
  obtain ⟨F, hF⟩ := hG.exists_isWFRecursion hR hS
  rw [← hG.eq_wfRecursion hR hF]
  exact hF

/-- The recursive definition `wfRecursion G R x = G (wfRecursion G R ↾₀ R.predSet x)` -/
theorem wfRecursion_eq (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike) (x : M) :
    wfRecursion G R x = G (wfRecursion G R ↾₀ R.predSet x) :=
  (hG.isWFRecursion_wfRecursion hR hS).eq x

/-- `wfRecursion G R` is definable if the approximations form a definable class -/
theorem definable_wfRecursion (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike)
    [Class.Definable (fun f ↦ IsWFApprox f G R) Set.univ] :
    (wfRecursion G R).Definable Set.univ := by
  -- `f` is an approximation defined at `x` with `f ﹫ x = v`
  let Ap : Class M := fun f ↦ IsWFApprox f G R
  refine ClassFunction.Definable.of_iff (F := fun xs ↦ ∃ f, Ap f ∧ xs 0 ∈ dom f ∧ xs 1 = f ﹫ xs 0)
    (hF := by infer_instance) fun x v ↦ ?_
  simp only [Ap, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨f, hf, hx, rfl⟩
    exact hG.wfRecursion_eq_val hR hS hf hx
  · rintro rfl
    obtain ⟨f, hf, hx⟩ := hG.exists_isWFApprox x
    exact ⟨f, hf, hx, hG.wfRecursion_eq_val hR hS hf hx⟩

end HasWFApprox

/-- A class function defined by recursion from `G` along `R` is `wfRecursion G R` -/
theorem IsWFRecursion.eq_wfRecursion (hR : R.IsStrictWellFounded₀) [R.predSet.Sigma 1 Set.univ]
    [G.Sigma 1 Set.univ] {F : ClassFunction M} (hFG : IsWFRecursion F G R) :
    F = wfRecursion G R :=
  (hasWFApprox hR hFG.isSetLike).eq_wfRecursion hR hFG

/-- The well-founded recursion theorem: if `R.predSet` and `G` are `Σ₁`, then some class function is
defined by recursion from `G` along `R` -/
theorem exists_isWFRecursion (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] [G.Sigma 1 Set.univ] : ∃ F, IsWFRecursion F G R :=
  (hasWFApprox hR hS).exists_isWFRecursion hR hS

/-- `wfRecursion G R` agrees with every approximation -/
theorem IsWFApprox.wfRecursion_eq (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] [G.Sigma 1 Set.univ] {f x : M} (hf : IsWFApprox f G R)
    (hx : x ∈ dom f) : wfRecursion G R x = f ﹫ x :=
  (hasWFApprox hR hS).wfRecursion_eq_val hR hS hf hx

/-- The recursive definition `wfRecursion G R x = G (wfRecursion G R ↾₀ R.predSet x)` in models of
`KP`, for a set-like class relation `R` that is well-founded for definable classes, such that
`R.predSet` and `G` are `Σ₁` -/
theorem wfRecursion_eq_of_modelsKP (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] [G.Sigma 1 Set.univ] (x : M) :
    wfRecursion G R x = G (wfRecursion G R ↾₀ R.predSet x) :=
  (hasWFApprox hR hS).wfRecursion_eq hR hS x

/-- `wfRecursion G R` is defined by recursion from `G` along `R` -/
theorem isWFRecursion_wfRecursion (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] [G.Sigma 1 Set.univ] : IsWFRecursion (wfRecursion G R) G R :=
  (hasWFApprox hR hS).isWFRecursion_wfRecursion hR hS

/-- `wfRecursion G R` is a `Σ₁` class function -/
theorem sigma_wfRecursion (hR : R.IsStrictWellFounded₀) (hS : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] [G.Sigma 1 Set.univ] : (wfRecursion G R).Sigma 1 Set.univ := by
  -- `f` is an approximation defined at `x` with `f ﹫ x = v`
  let Ap : Class M := fun f ↦ IsWFApprox f G R
  refine ClassFunction.Sigma.of_iff
    (F := fun xs ↦ ∃ f, (Ap f ∧ xs 0 ∈ dom f) ∧ xs 1 = f ﹫ xs 0)
    (hF := by infer_instance) fun x v ↦ ?_
  simp only [Ap, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨f, ⟨hf, hx⟩, rfl⟩
    exact hf.wfRecursion_eq hR hS hx
  · rintro rfl
    obtain ⟨f, hf, hx⟩ := exists_isWFApprox hR hS (G := G) x
    exact ⟨f, ⟨hf, hx⟩, hf.wfRecursion_eq hR hS hx⟩

end ClassRecursion

section Collapse

variable [Inhabited M] [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] {R : Multiclass M 2}
  {D : Class M} {x y : M}

/-- The Mostowski collapse of `R`: `collapse R x = {collapse R y | y R x}` -/
noncomputable def collapse (R : Multiclass M 2) : ClassFunction M := wfRecursion ran R

theorem sigma_collapse (hRwf : R.IsStrictWellFounded₀) (hRsl : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] : (collapse R).Sigma 1 Set.univ :=
  sigma_wfRecursion hRwf hRsl

theorem collapse_eq (hRwf : R.IsStrictWellFounded₀) (hRsl : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] (x : M) : collapse R x = ran (collapse R ↾₀ R.predSet x) :=
  (isWFRecursion_wfRecursion hRwf hRsl).eq x

theorem mem_collapse_iff (hRwf : R.IsStrictWellFounded₀) (hRsl : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] {z : M} :
    z ∈ collapse R x ↔ ∃ y, R ![y, x] ∧ collapse R y = z := by
  have h : IsWFRecursion (wfRecursion ran R) ran R := isWFRecursion_wfRecursion hRwf hRsl (G := ran)
  simp [collapse, h.eq x, mem_ran_toSetRestrictedTo_iff (h.isSetRestrictedTo _),
    hRsl.mem_predSet_iff]

theorem collapse_mem_collapse (hRwf : R.IsStrictWellFounded₀) (hRsl : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] (hyx : R ![y, x]) : collapse R y ∈ collapse R x := by
  simp only [mem_collapse_iff, hRwf, hRsl]
  exact ⟨y, hyx, rfl⟩

/-- `R` is extensional on the class `D`: elements of `D` with the same `R`-predecessors are
equal -/
def Multiclass.IsExtensionalOn (R : Multiclass M 2) (D : Class M) : Prop :=
  ∀ x y, D x → D y → (∀ z, R ![z, x] ↔ R ![z, y]) → x = y

/-- `R` is extensional: elements with the same `R`-predecessors are equal -/
def Multiclass.IsExtensional (R : Multiclass M 2) : Prop := R.IsExtensionalOn ⊤

/-- The collapse is injective on a definable class `D` closed under `R`-predecessors on which `R`
is extensional -/
theorem collapse_injOn (hRwf : R.IsStrictWellFounded₀) (hRsl : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] [D.Definable Set.univ] (hDR : ∀ x y, D x → R ![y, x] → D y)
    (hR : R.IsExtensionalOn D) (hx : D x) (hy : D y) (hxy : collapse R x = collapse R y) :
    x = y := by
  have := sigma_collapse hRwf hRsl
  -- induction on `x` for `D x → ∀ y, D y → collapse R y = collapse R x → x = y`
  suffices hx' : D x → ∀ y, D y → collapse R y = collapse R x → x = y from
    hx' hx y hy hxy.symm
  refine hRwf.induction
    (A := fun x ↦ D x → ∀ y, D y → collapse R y = collapse R x → x = y) (fun x ih ↦ ?_) x
  intro hx y hy hxy
  refine hR x y hx hy fun z ↦ ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
  · have hzx : collapse R z ∈ collapse R y := hxy ▸ collapse_mem_collapse hRwf hRsl hz
    simp only [mem_collapse_iff, hRwf, hRsl] at hzx
    obtain ⟨w, hw, hwz⟩ := hzx
    grind
  · have hzx : collapse R z ∈ collapse R x := hxy ▸ collapse_mem_collapse hRwf hRsl hz
    simp only [mem_collapse_iff, hRwf, hRsl] at hzx
    obtain ⟨w, hw, hwz⟩ := hzx
    grind

/-- The collapse of an extensional relation is injective -/
theorem collapse_injective (hRwf : R.IsStrictWellFounded₀) (hRsl : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] (hR : R.IsExtensional) : Function.Injective (collapse R) :=
  fun _ _ h ↦ collapse_injOn hRwf hRsl (by simp) hR (by simp) (by simp) h

/-- The image of the collapse -/
def collapseImage (R : Multiclass M 2) : Class M := fun z ↦ ∃ x, collapse R x = z

/-- The image of the collapse is a transitive class -/
theorem collapseImage_of_mem (hRwf : R.IsStrictWellFounded₀) (hRsl : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] {z w : M} (hz : collapseImage R z) (hw : w ∈ z) :
    collapseImage R w := by
  obtain ⟨x, rfl⟩ := hz
  simp only [mem_collapse_iff, hRwf, hRsl] at hw
  obtain ⟨y, -, hy⟩ := hw
  exact ⟨y, hy⟩

/-- The collapse is an isomorphism from `R` onto `∈` on the elements of a class `D` as in
`collapse_injOn` -/
theorem rel_iff_collapse_mem_collapse_of_isExtensionalOn (hRwf : R.IsStrictWellFounded₀)
    (hRsl : R.IsSetLike) [R.predSet.Sigma 1 Set.univ] [D.Definable Set.univ]
    (hDR : ∀ x y, D x → R ![y, x] → D y) (hR : R.IsExtensionalOn D) (hx : D x) (hy : D y) :
    R ![y, x] ↔ collapse R y ∈ collapse R x := by
  refine ⟨collapse_mem_collapse hRwf hRsl, fun h ↦ ?_⟩
  simp only [mem_collapse_iff, hRwf, hRsl] at h
  obtain ⟨z, hz, hzy⟩ := h
  rwa [collapse_injOn hRwf hRsl hDR hR (hDR x z hx hz) hy hzy] at hz

/-- The collapse of an extensional relation `R` is an isomorphism from `R` onto `∈` on the
transitive class `collapseImage R` -/
theorem rel_iff_collapse_mem_collapse (hRwf : R.IsStrictWellFounded₀) (hRsl : R.IsSetLike)
    [R.predSet.Sigma 1 Set.univ] (hR : R.IsExtensional) :
    R ![y, x] ↔ collapse R y ∈ collapse R x :=
  rel_iff_collapse_mem_collapse_of_isExtensionalOn hRwf hRsl (by simp) hR (by simp)
    (by simp)

end Collapse

section MemRel

variable [Inhabited M]

omit [Inhabited M] in
theorem isSetLike_memRel : (MemRel : Multiclass M 2).IsSetLike :=
  fun x ↦ ⟨x, fun y ↦ (memRel_iff x y).symm⟩

@[simp]
theorem predSet_memRel_apply [Extensional M] (x : M) : (MemRel : Multiclass M 2).predSet x = x := by
  ext y
  simp only [isSetLike_memRel.mem_predSet_iff, memRel_iff]

theorem predSet_memRel [Extensional M] : (MemRel : Multiclass M 2).predSet = _root_.id :=
  funext predSet_memRel_apply

instance [Extensional M] : (MemRel : Multiclass M 2).predSet.Sigma 1 Set.univ := by
  rw [predSet_memRel]
  infer_instance

omit [Inhabited M] in
/-- `∈` is well-founded for definable classes in models of `KP` -/
theorem isStrictWellFounded₀_memRel [ModelsKP M] :
    (MemRel : Multiclass M 2).IsStrictWellFounded₀ := by
  intro A _ ⟨x, hx⟩
  by_contra! h
  refine induction_of_modelsKP (A := ∼A) (fun z ih hz ↦ ?_) x hx
  obtain ⟨y, hy, hAy⟩ := h z hz
  simp only [memRel_iff] at hy
  exact ih y hy hAy

variable [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M]

/-- The collapse of `∈` is the identity -/
@[simp]
theorem collapse_memRel (x : M) : collapse (MemRel : Multiclass M 2) x = x := by
  have := sigma_collapse (isStrictWellFounded₀_memRel (M := M)) isSetLike_memRel
  refine induction_of_modelsKP (A := fun x ↦ collapse MemRel x = _root_.id x) (fun x ih ↦ ?_) x
  ext z
  simp only [mem_collapse_iff, isStrictWellFounded₀_memRel, isSetLike_memRel, memRel_iff]
  grind

/-- The image of the collapse of `∈` is the whole universe -/
theorem collapseImage_memRel (x : M) : collapseImage (MemRel : Multiclass M 2) x :=
  ⟨x, collapse_memRel x⟩

end MemRel

section CollapseOn

variable [Inhabited M] [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] {R a x y : M}

/-- A set relation on `a` that is well-founded for definable classes is strict well-founded -/
theorem Multiclass.IsStrictWellFounded₀.isStrictWellFounded_ofRel
    (hR : (Multiclass.ofRel R).IsStrictWellFounded₀) (hRa : IsRelationOn R a) :
    MemStructure.IsStrictWellFounded R a := by
  refine ⟨hRa, fun b hba hb ↦ ?_⟩
  simp only [ne_empty_iff] at hb
  obtain ⟨x, hx⟩ := hb
  obtain ⟨m, hm, hmin⟩ := hR (MemStructure.toClass b) ⟨x, by rwa [toClass_iff_mem]⟩
  exact ⟨m, hm, fun y hy hym ↦ hmin y hym hy⟩

/-- With comprehension for definable classes, a strict well-founded set relation is well-founded
for definable classes -/
theorem IsStrictWellFounded.ofRel
    [hA : ∀ (A : Class M) [A.Definable Set.univ], HasComprehension a A]
    (h : IsStrictWellFounded R a) : (Multiclass.ofRel R).IsStrictWellFounded₀ := by
  intro A _ ⟨x, hx⟩
  by_cases hb : a ∩₀ A = ∅
  · simp only [comprehension_eq_empty_iff] at hb
    exact ⟨x, hx, fun y hy hAy ↦ hb y (h.isRelationOn.mem_left hy) hAy⟩
  · obtain ⟨m, hm, hmin⟩ := h.right (a ∩₀ A) (comprehension_subset _ _) hb
    simp only [mem_comprehension_iff] at hm hmin
    exact ⟨m, hm.right, fun y hy hAy ↦ hmin y ⟨h.isRelationOn.mem_left hy, hAy⟩ hy⟩

omit [Inhabited M] [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
/-- A class relation that is well-founded for definable classes is well-founded for sets -/
theorem Multiclass.IsStrictWellFounded₀.isStrictWellFounded {R : Multiclass M 2}
    (hR : R.IsStrictWellFounded₀) : R.IsStrictWellFounded := by
  intro b ⟨x, hx⟩
  obtain ⟨m, hm, hmin⟩ := hR (MemStructure.toClass b) ⟨x, by rwa [toClass_iff_mem]⟩
  exact ⟨m, hm, fun y hy hyb ↦ hmin y hy hyb⟩

/-- `R` is a strict well-founded relation on `a` that is moreover well-founded for definable
classes -/
def IsStrictWellFounded₀ (R a : M) : Prop :=
  IsStrictWellFounded R a ∧ (Multiclass.ofRel R).IsStrictWellFounded₀

omit [ModelsKP M] in
theorem IsStrictWellFounded₀.isStrictWellFounded (h : IsStrictWellFounded₀ R a) :
    IsStrictWellFounded R a :=
  h.left

omit [ModelsKP M] in
theorem IsStrictWellFounded₀.isStrictWellFounded₀_ofRel (h : IsStrictWellFounded₀ R a) :
    (Multiclass.ofRel R).IsStrictWellFounded₀ :=
  h.right

omit [ModelsKP M] in
theorem IsStrictWellFounded₀.isRelationOn (h : IsStrictWellFounded₀ R a) : IsRelationOn R a :=
  h.isStrictWellFounded.isRelationOn

/-- A set relation on `a` that is well-founded for definable classes is `IsStrictWellFounded₀` -/
theorem Multiclass.IsStrictWellFounded₀.isStrictWellFounded₀
    (hR : (Multiclass.ofRel R).IsStrictWellFounded₀) (hRa : IsRelationOn R a) :
    MemStructure.IsStrictWellFounded₀ R a :=
  ⟨hR.isStrictWellFounded_ofRel hRa, hR⟩

/-- With comprehension for definable classes, a strict well-founded set relation is
`IsStrictWellFounded₀` -/
theorem IsStrictWellFounded.isStrictWellFounded₀_of_comprehension
    [hA : ∀ (A : Class M) [A.Definable Set.univ], HasComprehension a A]
    (h : IsStrictWellFounded R a) : IsStrictWellFounded₀ R a :=
  ⟨h, h.ofRel (hA := hA)⟩

/-- The Mostowski collapse of a set relation `R` on `a`, as a function on `a` -/
noncomputable def collapseOn (R a : M) : M := collapse (Multiclass.ofRel R) ↾₀ a

omit [L.ExtraConstantsUnaryRelationsOnly] [ModelsKP M] in
theorem IsExtensionalOn.isExtensionalOn_ofRel (hE : IsExtensionalOn R a) :
    (Multiclass.ofRel R).IsExtensionalOn (toClass a) := by
  intro x y hx hy h
  exact hE x hx y hy h

theorem isSetRestrictedTo_collapse_ofRel (hR : (Multiclass.ofRel R).IsStrictWellFounded₀) (b : M) :
    IsSetRestrictedTo (collapse (Multiclass.ofRel R)) b :=
  (isWFRecursion_wfRecursion hR Multiclass.isSetLike_ofRel).isSetRestrictedTo b

namespace IsStrictWellFounded₀

variable (h : IsStrictWellFounded₀ R a)
include h

theorem isFunction_collapseOn : IsFunction (collapseOn R a) :=
  isFunction_toSetRestrictedTo (isSetRestrictedTo_collapse_ofRel h.isStrictWellFounded₀_ofRel a)

theorem dom_collapseOn : dom (collapseOn R a) = a :=
  dom_toSetRestrictedTo (isSetRestrictedTo_collapse_ofRel h.isStrictWellFounded₀_ofRel a)

theorem val_collapseOn (hx : x ∈ a) :
    collapseOn R a ﹫ x = collapse (Multiclass.ofRel R) x :=
  val_toSetRestrictedTo (isSetRestrictedTo_collapse_ofRel h.isStrictWellFounded₀_ofRel a) hx

/-- The collapse of `R` on `a` is defined by `R`-recursion on `a` from `ran` -/
theorem isWFRecursionOn_collapseOn : IsWFRecursionOn R a ran (collapseOn R a) := by
  have hf : IsFunction (collapseOn R a) := h.isFunction_collapseOn
  have hpred : ∀ (x : M), predSet R x ⊆ a := h.isRelationOn.predSet_subset
  refine ⟨hf, h.dom_collapseOn, fun x hx ↦ ?_⟩
  rw [h.val_collapseOn hx, collapse_eq h.isStrictWellFounded₀_ofRel Multiclass.isSetLike_ofRel,
    Multiclass.predSet_ofRel_apply]
  congr 1
  refine toSetRestrictedTo_eq (hf.restrict _) ?_ fun y hy ↦ ?_
  · rw [dom_restrict_of_subset hf (by rw [h.dom_collapseOn]; exact hpred x)]
  · rw [val_restrict _ hf hy (by rw [h.dom_collapseOn]; exact hpred x hy),
      h.val_collapseOn (hpred x hy)]

/-- The collapse of `R` on `a` is the function defined by `R`-recursion on `a` from `ran` -/
theorem collapseOn_eq_wfRecursionOn : collapseOn R a = wfRecursionOn R a ran :=
  h.isWFRecursionOn_collapseOn.eq_wfRecursionOn h.isStrictWellFounded

theorem collapseOn_val_eq (hx : x ∈ a) :
    collapseOn R a ﹫ x = ran (collapseOn R a ↾ predSet R x) :=
  h.isWFRecursionOn_collapseOn.right.right x hx

/-- The collapse of `R'` on `b ⊆ a` is the restriction of the collapse of `R` on `a`, if `R'` and
`R` have the same predecessors on `b` -/
theorem collapseOn_eq_restrict {R' b : M} (h' : IsStrictWellFounded₀ R' b) (hba : b ⊆ a)
    (hpred : ∀ x ∈ b, predSet R' x = predSet R x) : collapseOn R' b = collapseOn R a ↾ b := by
  have hf : IsFunction (collapseOn R a) := h.isFunction_collapseOn
  have hdom : b ⊆ dom (collapseOn R a) := by rwa [h.dom_collapseOn]
  rw [h'.collapseOn_eq_wfRecursionOn]
  refine (IsWFRecursionOn.eq_wfRecursionOn h'.isStrictWellFounded
    ⟨hf.restrict b, dom_restrict_of_subset hf hdom, fun x hx ↦ ?_⟩).symm
  have hsub : predSet R x ⊆ b := hpred x hx ▸ h'.isRelationOn.predSet_subset x
  rw [val_restrict _ hf hx (hdom hx), h.collapseOn_val_eq (hba hx), restrict_restrict,
    hpred x hx]
  congr 2
  ext y
  grind

/-- The collapse of `R` on `a` is injective if `R` is extensional on `a` -/
theorem collapseOn_injOn (hE : IsExtensionalOn R a) (hx : x ∈ a) (hy : y ∈ a) :
    collapseOn R a ﹫ x = collapseOn R a ﹫ y ↔ x = y := by
  refine ⟨fun hxy ↦ ?_, by simp +contextual⟩
  rw [h.val_collapseOn hx, h.val_collapseOn hy] at hxy
  refine collapse_injOn h.isStrictWellFounded₀_ofRel Multiclass.isSetLike_ofRel
    (fun x y _ hyx ↦ ?_) hE.isExtensionalOn_ofRel (by simpa [toClass] using hx)
    (by simpa [toClass] using hy) hxy
  simpa [toClass] using h.isRelationOn.mem_left hyx

/-- The collapse of `R` on `a` is an isomorphism from `R` onto `∈` if `R` is extensional on
`a` -/
theorem rel_iff_collapseOn_mem_collapseOn (hE : IsExtensionalOn R a) (hx : x ∈ a) (hy : y ∈ a) :
    y [R] x ↔ collapseOn R a ﹫ y ∈ collapseOn R a ﹫ x := by
  rw [h.val_collapseOn hx, h.val_collapseOn hy]
  refine rel_iff_collapse_mem_collapse_of_isExtensionalOn h.isStrictWellFounded₀_ofRel
    Multiclass.isSetLike_ofRel (fun x y _ hyx ↦ ?_) hE.isExtensionalOn_ofRel
    (by simpa [toClass] using hx) (by simpa [toClass] using hy)
  simpa [toClass] using h.isRelationOn.mem_left hyx

/-- The range of the collapse of `R` on `a` is a transitive set -/
theorem transitive_ran_collapseOn : Transitive (ran (collapseOn R a)) := by
  have hR := h.isStrictWellFounded₀_ofRel
  have hf : IsFunction (collapseOn R a) := h.isFunction_collapseOn
  intro z hz w hw
  simp only [hf.mem_ran_iff, h.dom_collapseOn] at hz ⊢
  obtain ⟨x, hx, rfl⟩ := hz
  simp only [h.val_collapseOn hx, mem_collapse_iff, hR, Multiclass.isSetLike_ofRel] at hw
  obtain ⟨y, hy, rfl⟩ := hw
  have hya : ![y, x] 0 ∈ a := h.isRelationOn.mem_left hy
  exact ⟨y, hya, h.val_collapseOn hya⟩

end IsStrictWellFounded₀

/-- `f` is the transitive collapse of `R` on `a`: `f ﹫ x = {f ﹫ y | y R x}` for `x ∈ a` -/
def IsCollapseOn (R a f : M) : Prop := IsWFRecursionOn R a ran f

instance : Multiclass.Definable (fun xs ↦ IsCollapseOn (xs 0) (xs 1) (xs 2) : Multiclass M 3)
    Set.univ := by
  -- `[R, a, f]`: `f` is a function on `a`
  let φ : L.DeltaZeroBoundedFormula 3 := (ᵣ2).isFunction ⊓ (&0 =₀ &1).substBoundRud ![(ᵣ2).dom, ᵣ1]
  -- `[R, a, f, x]`: `f ﹫ x = ran (f ↾ predSet R x)`
  let ψ : L.DeltaZeroBoundedFormula 4 := (&0 =₀ &1).substBoundRud ![(ᵣ2) ﹫ (ᵣ3),
    ((ᵣ2 : L.RudimentaryTerm 4) ↾ ((ᵣ0 : L.RudimentaryTerm 4) ∩
      ((ᵣ0 : L.RudimentaryTerm 4).dom ×ˢ ({ᵣ3} : L.RudimentaryTerm 4))).dom).ran]
  suffices (fun xs ↦ IsCollapseOn (xs 0) (xs 1) (xs 2) : Multiclass M 3) =
      φ.toBoundedFormula.multiclass ⊓ ψ.toBoundedFormula.multiclass.allMem 1 by
    rw [this]
    infer_instance
  funext xs
  simp only [Multiclass.inf_iff, Multiclass.allMem, BoundedFormula.multiclass, φ, ψ,
    DeltaZeroBoundedFormula.realize_substBoundRud]
  simp [IsCollapseOn, IsWFRecursionOn, predSet, snoc_nat, and_assoc]

/-- The transitive collapse of a strict well-founded set relation is unique -/
theorem IsStrictWellFounded.eq_of_isCollapseOn {f g : M} (h : IsStrictWellFounded R a)
    (hf : IsCollapseOn R a f) (hg : IsCollapseOn R a g) : f = g :=
  h.eq_of_isWFRecursionOn hf hg

/-- The class of pairs `p` with `f ﹫ left p ∈ f ﹫ right p` -/
def MemPullback (f : M) : Class M := fun p ↦ f ﹫ left p ∈ f ﹫ right p

/-- `MemPullback f` is defined by a `Δ₀` formula with parameter `f` -/
theorem MemPullback.eq_multiclass (f : M) :
    MemPullback f = (((&0 ∈₀ &1).substBoundRud ![(ᵣ1) ﹫ (ᵣ0).left, (ᵣ1) ﹫ (ᵣ0).right] :
      L.DeltaZeroBoundedFormula 2).toBoundedFormula.multiclass.slice ![f] : Class M) := by
  funext p
  rw [Multiclass.toClass_iff, Multiclass.slice, Fin.append_vec₁_vec₁, BoundedFormula.multiclass,
    DeltaZeroBoundedFormula.realize_substBoundRud]
  simp [MemPullback]

instance (f : M) : (MemPullback f).DeltaZero Set.univ := by
  rw [MemPullback.eq_multiclass]
  infer_instance

/-- The pullback of `∈` along `f` on `x`: `y` relates to `z` if `f ﹫ y ∈ f ﹫ z` -/
noncomputable def memPullback (f x : M) : M := (x ×ˢ x) ∩₀ MemPullback f

@[simp, grind =]
theorem rel_memPullback_iff {f y z : M} :
    y [memPullback f x] z ↔ y ∈ x ∧ z ∈ x ∧ f ﹫ y ∈ f ﹫ z := by
  rw [memPullback, mem_comprehension_iff]
  simp [MemPullback, and_assoc]

/-- The pullback of `∈` along a surjection is well-founded -/
theorem IsSurjectionFromTo.isStrictWellFounded_memPullback {f : M} (hf : f !: x ↠ a) :
    IsStrictWellFounded (memPullback f x) x := by
  refine ⟨(isRelationOn_sprod x).subset (comprehension_subset _ _), fun b hbx hb ↦ ?_⟩
  -- an element of `b` with `∈`-minimal value
  have hfb : f '' b ≠ ∅ := by
    simp only [ne_empty_iff] at hb ⊢
    obtain ⟨y, hy⟩ := hb
    exact ⟨f ﹫ y, by grind [mem_image_iff, rel_val]⟩
  have hm := memMin_mem hfb
  simp only [mem_image_iff] at hm
  obtain ⟨m, hm, hfm⟩ := hm
  refine ⟨m, hm, fun y hy hym ↦ notMem_of_mem_memMin ?_ (?_ : f ﹫ y ∈ f '' b)⟩
  · grind
  · grind [mem_image_iff, rel_val]

/-- A surjection onto a transitive set is the transitive collapse of the pullback of `∈` -/
theorem IsSurjectionFromTo.isCollapseOn_memPullback {f : M} (ha : Transitive a)
    (hf : f !: x ↠ a) : IsCollapseOn (memPullback f x) x f := by
  refine ⟨hf.isFunction, hf.dom_eq, fun y hy ↦ ?_⟩
  ext z
  rw [(hf.isFunction.restrict _).mem_ran_iff, dom_restrict hf.isFunction, hf.dom_eq]
  refine ⟨fun hz ↦ ?_, fun ⟨y', hy', hz⟩ ↦ by grind⟩
  obtain ⟨y', hy', rfl⟩ := hf.exists_mem_val (ha _ (hf.isFunctionFromTo.val_mem hy) hz)
  exact ⟨y', by grind⟩

end CollapseOn

end FirstOrder.Language.MemStructure
