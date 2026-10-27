/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Relation
/-!
# Basic properties of relations

For `R a : M`, we define what it means for `R` to be reflexive, irreflexive, symmetric,
antisymmetric, asymmetric, transitive, trichotomous and total on `a`. Here `R` is any element of
`M`, viewed as the relation `x [R] y`, and only `x y ∈ a` are considered.
-/

namespace FirstOrder.Language.MemStructure

open FirstOrder Language

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  {R S a b x y z : M}

/-- `R` is reflexive on `a` -/
def IsReflOn (R a : M) : Prop := ∀ x ∈ a, x [R] x

/-- `R` is irreflexive on `a` -/
def IsIrreflOn (R a : M) : Prop := ∀ x ∈ a, ¬x [R] x

/-- `R` is symmetric on `a` -/
def IsSymmOn (R a : M) : Prop := ∀ x ∈ a, ∀ y ∈ a, x [R] y → y [R] x

/-- `R` is antisymmetric on `a` -/
def IsAntisymmOn (R a : M) : Prop := ∀ x ∈ a, ∀ y ∈ a, x [R] y → y [R] x → x = y

/-- `R` is asymmetric on `a` -/
def IsAsymmOn (R a : M) : Prop := ∀ x ∈ a, ∀ y ∈ a, x [R] y → ¬y [R] x

/-- `R` is transitive on `a` -/
def IsTransOn (R a : M) : Prop :=
  ∀ x ∈ a, ∀ y ∈ a, ∀ z ∈ a, x [R] y → y [R] z → x [R] z

/-- `R` is trichotomous on `a` -/
def IsTrichotomousOn (R a : M) : Prop := ∀ x ∈ a, ∀ y ∈ a, x [R] y ∨ x = y ∨ y [R] x

/-- `R` is total on `a` -/
def IsTotalOn (R a : M) : Prop := ∀ x ∈ a, ∀ y ∈ a, x [R] y ∨ y [R] x

/-- `R` is extensional on `a`: elements of `a` with the same `R`-predecessors are equal -/
def IsExtensionalOn (R a : M) : Prop := ∀ x ∈ a, ∀ y ∈ a, (∀ z, z [R] x ↔ z [R] y) → x = y

section Apply

theorem IsReflOn.refl (h : IsReflOn R a) (hx : x ∈ a) : x [R] x := h x hx

theorem IsIrreflOn.irrefl (h : IsIrreflOn R a) (hx : x ∈ a) : ¬x [R] x := h x hx

theorem IsSymmOn.symm (h : IsSymmOn R a) (hx : x ∈ a) (hy : y ∈ a) (hxy : x [R] y) :
    y [R] x :=
  h x hx y hy hxy

theorem IsSymmOn.rel_comm (h : IsSymmOn R a) (hx : x ∈ a) (hy : y ∈ a) :
    x [R] y ↔ y [R] x :=
  ⟨h x hx y hy, h y hy x hx⟩

theorem IsAntisymmOn.antisymm (h : IsAntisymmOn R a) (hx : x ∈ a) (hy : y ∈ a) (hxy : x [R] y)
    (hyx : y [R] x) : x = y :=
  h x hx y hy hxy hyx

theorem IsAsymmOn.asymm (h : IsAsymmOn R a) (hx : x ∈ a) (hy : y ∈ a) (hxy : x [R] y) :
    ¬y [R] x :=
  h x hx y hy hxy

theorem IsTransOn.trans (h : IsTransOn R a) (hx : x ∈ a) (hy : y ∈ a) (hz : z ∈ a)
    (hxy : x [R] y) (hyz : y [R] z) : x [R] z :=
  h x hx y hy z hz hxy hyz

theorem IsTrichotomousOn.trichotomous (h : IsTrichotomousOn R a) (hx : x ∈ a) (hy : y ∈ a) :
    x [R] y ∨ x = y ∨ y [R] x :=
  h x hx y hy

theorem IsTotalOn.total (h : IsTotalOn R a) (hx : x ∈ a) (hy : y ∈ a) : x [R] y ∨ y [R] x :=
  h x hx y hy

end Apply

section Implications

@[grind .]
theorem IsAsymmOn.isIrreflOn (h : IsAsymmOn R a) : IsIrreflOn R a := by
  grind [IsIrreflOn, IsAsymmOn]

@[grind .]
theorem IsAsymmOn.isAntisymmOn (h : IsAsymmOn R a) : IsAntisymmOn R a := by
  grind [IsAntisymmOn, IsAsymmOn]

theorem IsIrreflOn.isAsymmOn (hR : IsIrreflOn R a) (hR' : IsTransOn R a) : IsAsymmOn R a := by
  grind [IsIrreflOn, IsAsymmOn, IsTransOn]

theorem isAsymmOn_iff_isIrreflOn_and_isAntisymmOn :
    IsAsymmOn R a ↔ IsIrreflOn R a ∧ IsAntisymmOn R a := by
  grind [IsIrreflOn, IsAntisymmOn, IsAsymmOn]

@[grind .]
theorem IsTotalOn.isReflOn (h : IsTotalOn R a) : IsReflOn R a := by
  grind [IsReflOn, IsTotalOn]

@[grind .]
theorem IsTotalOn.isTrichotomousOn (h : IsTotalOn R a) : IsTrichotomousOn R a := by
  grind [IsTrichotomousOn, IsTotalOn]

end Implications

section Mono

theorem IsReflOn.mono (h : IsReflOn R a) (hba : b ⊆ a) : IsReflOn R b := by
  grind [IsReflOn]

theorem IsIrreflOn.mono (h : IsIrreflOn R a) (hba : b ⊆ a) : IsIrreflOn R b := by
  grind [IsIrreflOn]

theorem IsSymmOn.mono (h : IsSymmOn R a) (hba : b ⊆ a) : IsSymmOn R b := by
  grind [IsSymmOn]

theorem IsAntisymmOn.mono (h : IsAntisymmOn R a) (hba : b ⊆ a) : IsAntisymmOn R b := by
  grind [IsAntisymmOn]

theorem IsAsymmOn.mono (h : IsAsymmOn R a) (hba : b ⊆ a) : IsAsymmOn R b := by
  grind [IsAsymmOn]

theorem IsTransOn.mono (h : IsTransOn R a) (hba : b ⊆ a) : IsTransOn R b := by
  grind [IsTransOn]

theorem IsTrichotomousOn.mono (h : IsTrichotomousOn R a) (hba : b ⊆ a) :
    IsTrichotomousOn R b := by
  grind [IsTrichotomousOn]

theorem IsTotalOn.mono (h : IsTotalOn R a) (hba : b ⊆ a) : IsTotalOn R b := by
  grind [IsTotalOn]

end Mono

section Empty

variable [RudClosed M]

@[simp, grind .]
theorem isReflOn_empty (R : M) : IsReflOn R ∅ := by
  grind [IsReflOn]

@[simp, grind .]
theorem isIrreflOn_empty (R : M) : IsIrreflOn R ∅ := by
  grind [IsIrreflOn]

@[simp, grind .]
theorem isSymmOn_empty (R : M) : IsSymmOn R ∅ := by
  grind [IsSymmOn]

@[simp, grind .]
theorem isAntisymmOn_empty (R : M) : IsAntisymmOn R ∅ := by
  grind [IsAntisymmOn]

@[simp, grind .]
theorem isAsymmOn_empty (R : M) : IsAsymmOn R ∅ := by
  grind [IsAsymmOn]

@[simp, grind .]
theorem isTransOn_empty (R : M) : IsTransOn R ∅ := by
  grind [IsTransOn]

@[simp, grind .]
theorem isTrichotomousOn_empty (R : M) : IsTrichotomousOn R ∅ := by
  grind [IsTrichotomousOn]

@[simp, grind .]
theorem isTotalOn_empty (R : M) : IsTotalOn R ∅ := by
  grind [IsTotalOn]

@[simp, grind .]
theorem isIrreflOn_empty_left (a : M) : IsIrreflOn ∅ a := by
  grind [IsIrreflOn]

@[simp, grind .]
theorem isSymmOn_empty_left (a : M) : IsSymmOn ∅ a := by
  grind [IsSymmOn]

@[simp, grind .]
theorem isAntisymmOn_empty_left (a : M) : IsAntisymmOn ∅ a := by
  grind [IsAntisymmOn]

@[simp, grind .]
theorem isAsymmOn_empty_left (a : M) : IsAsymmOn ∅ a := by
  grind [IsAsymmOn]

@[simp, grind .]
theorem isTransOn_empty_left (a : M) : IsTransOn ∅ a := by
  grind [IsTransOn]

end Empty

section Inv

variable [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M]

@[simp, grind =]
theorem isReflOn_inv_iff : IsReflOn R⁻¹ a ↔ IsReflOn R a := by
  grind [IsReflOn]

@[simp, grind =]
theorem isIrreflOn_inv_iff : IsIrreflOn R⁻¹ a ↔ IsIrreflOn R a := by
  grind [IsIrreflOn]

@[simp, grind =]
theorem isSymmOn_inv_iff : IsSymmOn R⁻¹ a ↔ IsSymmOn R a := by
  grind [IsSymmOn]

@[simp, grind =]
theorem isAntisymmOn_inv_iff : IsAntisymmOn R⁻¹ a ↔ IsAntisymmOn R a := by
  grind [IsAntisymmOn]

@[simp, grind =]
theorem isAsymmOn_inv_iff : IsAsymmOn R⁻¹ a ↔ IsAsymmOn R a := by
  grind [IsAsymmOn]

@[simp, grind =]
theorem isTransOn_inv_iff : IsTransOn R⁻¹ a ↔ IsTransOn R a := by
  grind [IsTransOn]

@[simp, grind =]
theorem isTrichotomousOn_inv_iff : IsTrichotomousOn R⁻¹ a ↔ IsTrichotomousOn R a := by
  grind [IsTrichotomousOn]

@[simp, grind =]
theorem isTotalOn_inv_iff : IsTotalOn R⁻¹ a ↔ IsTotalOn R a := by
  grind [IsTotalOn]

end Inv

section InterSProd

variable [RudClosed M] [Extensional M]

@[simp, grind =]
theorem isReflOn_inter_sprod_iff : IsReflOn (R ∩ a ×ˢ a) a ↔ IsReflOn R a := by
  simp +contextual [IsReflOn]

@[simp, grind =]
theorem isIrreflOn_inter_sprod_iff : IsIrreflOn (R ∩ a ×ˢ a) a ↔ IsIrreflOn R a := by
  simp +contextual [IsIrreflOn]

@[simp, grind =]
theorem isSymmOn_inter_sprod_iff : IsSymmOn (R ∩ a ×ˢ a) a ↔ IsSymmOn R a := by
  simp +contextual [IsSymmOn]

@[simp, grind =]
theorem isAntisymmOn_inter_sprod_iff : IsAntisymmOn (R ∩ a ×ˢ a) a ↔ IsAntisymmOn R a := by
  simp +contextual [IsAntisymmOn]

@[simp, grind =]
theorem isAsymmOn_inter_sprod_iff : IsAsymmOn (R ∩ a ×ˢ a) a ↔ IsAsymmOn R a := by
  simp +contextual [IsAsymmOn]

@[simp, grind =]
theorem isTransOn_inter_sprod_iff : IsTransOn (R ∩ a ×ˢ a) a ↔ IsTransOn R a := by
  simp +contextual [IsTransOn]

@[simp, grind =]
theorem isTrichotomousOn_inter_sprod_iff :
    IsTrichotomousOn (R ∩ a ×ˢ a) a ↔ IsTrichotomousOn R a := by
  simp +contextual [IsTrichotomousOn]

@[simp, grind =]
theorem isTotalOn_inter_sprod_iff : IsTotalOn (R ∩ a ×ˢ a) a ↔ IsTotalOn R a := by
  simp +contextual [IsTotalOn]

end InterSProd

section Concat

/-- The concatenation of `R` on `a` and `S` on `b`, with every element of `a` below every element
of `b` -/
noncomputable def concat (R a S b : M) : M := R ∪ S ∪ a ×ˢ b

/-- `R` on `a` with `x` added as a maximum -/
noncomputable def insertMax (R a x : M) : M := concat R a ∅ {x}

/-- `R` on `a` with `x` added as a minimum -/
noncomputable def insertMin (R a x : M) : M := concat ∅ {x} R a

variable [RudClosed M]

@[grind =]
theorem mem_concat_iff : z ∈ concat R a S b ↔ z ∈ R ∨ z ∈ S ∨ z ∈ a ×ˢ b := by
  simp [concat, or_assoc]

variable [Extensional M]

@[simp, grind =]
theorem rel_concat_iff : x [concat R a S b] y ↔ x [R] y ∨ x [S] y ∨ (x ∈ a ∧ y ∈ b) := by
  grind

@[simp, grind =]
theorem rel_insertMax_iff : y [insertMax R a x] z ↔ y [R] z ∨ (y ∈ a ∧ z = x) := by
  simp [insertMax]

@[simp, grind =]
theorem rel_insertMin_iff : y [insertMin R a x] z ↔ y [R] z ∨ (y = x ∧ z ∈ a) := by
  simp [insertMin]

theorem isRelationOn_concat [L.ExtraConstantsUnaryRelationsOnly] (hR : IsRelationOn R a)
    (hS : IsRelationOn S b) :
    IsRelationOn (concat R a S b) (a ∪ b) := by
  refine (isRelationOn_sprod _).subset fun z hz ↦ ?_
  simp only [mem_concat_iff] at hz
  rcases hz with hz | hz | hz
  · obtain ⟨x, hx, y, hy, rfl⟩ := hR.exists_exists hz
    grind
  · obtain ⟨x, hx, y, hy, rfl⟩ := hS.exists_exists hz
    grind
  · grind

end Concat

end FirstOrder.Language.MemStructure

namespace FirstOrder.Language

open FirstOrder Language BoundedFormula Fin DeltaZeroBoundedFormula

namespace RudimentaryTerm

variable {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] {n : ℕ}

/-- `hasMemOrderedPair r s t` means `!(s, t) ∈ r`, i.e. `s [r] t` -/
noncomputable def hasMemOrderedPair (r s t : L.RudimentaryTerm n) :
    L.DeltaZeroBoundedFormula n :=
  (&0 ∈₀ &1).substBoundRud ![ᵣ(s, t), r]

noncomputable def isReflOn (r s : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (∀₀∈ &1 (ᵣ0).hasMemOrderedPair (ᵣ2) (ᵣ2)).substBoundRud ![r, s]

noncomputable def isIrreflOn (r s : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (∀₀∈ &1 ∼((ᵣ0).hasMemOrderedPair (ᵣ2) (ᵣ2))).substBoundRud ![r, s]

noncomputable def isSymmOn (r s : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (∀₀∈ &1 ∀₀∈ &1
    ((ᵣ0).hasMemOrderedPair (ᵣ2) (ᵣ3) ⟹ (ᵣ0).hasMemOrderedPair (ᵣ3) (ᵣ2))).substBoundRud ![r, s]

noncomputable def isAntisymmOn (r s : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (∀₀∈ &1 ∀₀∈ &1
    ((ᵣ0).hasMemOrderedPair (ᵣ2) (ᵣ3) ⟹ (ᵣ0).hasMemOrderedPair (ᵣ3) (ᵣ2) ⟹
      &2 =₀ &3)).substBoundRud ![r, s]

noncomputable def isAsymmOn (r s : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (∀₀∈ &1 ∀₀∈ &1
    ((ᵣ0).hasMemOrderedPair (ᵣ2) (ᵣ3) ⟹ ∼((ᵣ0).hasMemOrderedPair (ᵣ3) (ᵣ2)))).substBoundRud ![r, s]

noncomputable def isTransOn (r s : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (∀₀∈ &1 ∀₀∈ &1 ∀₀∈ &1
    ((ᵣ0).hasMemOrderedPair (ᵣ2) (ᵣ3) ⟹ (ᵣ0).hasMemOrderedPair (ᵣ3) (ᵣ4) ⟹
      (ᵣ0).hasMemOrderedPair (ᵣ2) (ᵣ4))).substBoundRud ![r, s]

noncomputable def isTrichotomousOn (r s : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (∀₀∈ &1 ∀₀∈ &1
    ((ᵣ0).hasMemOrderedPair (ᵣ2) (ᵣ3) ⊔ &2 =₀ &3 ⊔
      (ᵣ0).hasMemOrderedPair (ᵣ3) (ᵣ2))).substBoundRud ![r, s]

noncomputable def isTotalOn (r s : L.RudimentaryTerm n) : L.DeltaZeroBoundedFormula n :=
  (∀₀∈ &1 ∀₀∈ &1
    ((ᵣ0).hasMemOrderedPair (ᵣ2) (ᵣ3) ⊔ (ᵣ0).hasMemOrderedPair (ᵣ3) (ᵣ2))).substBoundRud ![r, s]

variable (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree]

instance : (r.hasMemOrderedPair s t).RelFree := by
  unfold hasMemOrderedPair; infer_instance

instance : (r.isReflOn s).RelFree := by
  unfold isReflOn; infer_instance

instance : (r.isIrreflOn s).RelFree := by
  unfold isIrreflOn; infer_instance

instance : (r.isSymmOn s).RelFree := by
  unfold isSymmOn; infer_instance

instance : (r.isAntisymmOn s).RelFree := by
  unfold isAntisymmOn; infer_instance

instance : (r.isAsymmOn s).RelFree := by
  unfold isAsymmOn; infer_instance

instance : (r.isTransOn s).RelFree := by
  unfold isTransOn; infer_instance

instance : (r.isTrichotomousOn s).RelFree := by
  unfold isTrichotomousOn; infer_instance

instance : (r.isTotalOn s).RelFree := by
  unfold isTotalOn; infer_instance

/-- `lexProd₀〘R, S, a, b〙` is
`{z ∈ (a ×ˢ b) ×ˢ (a ×ˢ b) | z.1.1 [R] z.2.1 ∨ (z.1.1 = z.2.1 ∧ z.1.2 [S] z.2.2)}` -/
noncomputable def lexProd₀ : L.RudimentaryTerm 4 :=
  let ab : L.RudimentaryTerm 4 := (ᵣ2 : L.RudimentaryTerm 4) ×ˢ (ᵣ3 : L.RudimentaryTerm 4)
  ((ᵣ1).hasMemOrderedPair (ᵣ0).left.left (ᵣ0).right.left ⊔
      ((&0 =₀ &1).substBoundRud ![(ᵣ0).left.left, (ᵣ0).right.left] ⊓
        (ᵣ2).hasMemOrderedPair (ᵣ0).left.right (ᵣ0).right.right) :
      L.DeltaZeroBoundedFormula 3).comprehensionRudimentaryTerm.substBoundRud
    ![ᵣ0, ᵣ1, ab ×ˢ ab]

instance : (lexProd₀ : L.RudimentaryTerm 4).CharFree := by
  unfold lexProd₀; infer_instance

end RudimentaryTerm

namespace MemStructure

open RudimentaryTerm

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] [RudClosed M] [Extensional M] {n : ℕ}
  (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] (xs : Fin n → M)

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_hasMemOrderedPair :
    (r.hasMemOrderedPair s t).toBoundedFormula 〘xs〙 ↔ (!(s〘xs〙, t〘xs〙) : M) ∈ (r〘xs〙 : M) := by
  simp [hasMemOrderedPair]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isReflOn :
    (r.isReflOn s).toBoundedFormula 〘xs〙 ↔ IsReflOn (r〘xs〙 : M) s〘xs〙 := by
  simp [isReflOn, IsReflOn, snoc_nat]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isIrreflOn :
    (r.isIrreflOn s).toBoundedFormula 〘xs〙 ↔ IsIrreflOn (r〘xs〙 : M) s〘xs〙 := by
  simp [isIrreflOn, IsIrreflOn, snoc_nat]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isSymmOn :
    (r.isSymmOn s).toBoundedFormula 〘xs〙 ↔ IsSymmOn (r〘xs〙 : M) s〘xs〙 := by
  simp [isSymmOn, IsSymmOn, snoc_nat]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isAntisymmOn :
    (r.isAntisymmOn s).toBoundedFormula 〘xs〙 ↔
      IsAntisymmOn (r〘xs〙 : M) s〘xs〙 := by
  simp [isAntisymmOn, IsAntisymmOn, snoc_nat]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isAsymmOn :
    (r.isAsymmOn s).toBoundedFormula 〘xs〙 ↔ IsAsymmOn (r〘xs〙 : M) s〘xs〙 := by
  simp [isAsymmOn, IsAsymmOn, snoc_nat]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isTransOn :
    (r.isTransOn s).toBoundedFormula 〘xs〙 ↔ IsTransOn (r〘xs〙 : M) s〘xs〙 := by
  simp [isTransOn, IsTransOn, snoc_nat]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isTrichotomousOn :
    (r.isTrichotomousOn s).toBoundedFormula 〘xs〙 ↔
      IsTrichotomousOn (r〘xs〙 : M) s〘xs〙 := by
  simp [isTrichotomousOn, IsTrichotomousOn, snoc_nat, or_assoc]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_isTotalOn :
    (r.isTotalOn s).toBoundedFormula 〘xs〙 ↔ IsTotalOn (r〘xs〙 : M) s〘xs〙 := by
  simp [isTotalOn, IsTotalOn, snoc_nat]

end MemStructure

namespace MemStructure

section LexProd

open RudimentaryTerm

variable {L : Language} {M : Type*} [L.MemStructure M] [Inhabited M]
  [L.ExtraConstantsUnaryRelationsOnly] {R S a b x₁ x₂ y₁ y₂ z : M}

/-- The lexicographic order on `a ×ˢ b` given by `R` and `S` -/
noncomputable def lexProd (R a S b : M) : M := lexProd₀〘![R, S, a, b]〙

instance [RudClosed M] [Extensional M] : MulticlassFunction.DeltaZero
    (fun ys : Fin 4 → M ↦ lexProd (ys 0) (ys 2) (ys 1) (ys 3)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq lexProd₀ fun ys ↦ by
    rw [lexProd, show ![ys 0, ys 1, ys 2, ys 3] = ys by ext i; fin_cases i <;> rfl]

variable [RudClosed M] [Extensional M]

theorem mem_lexProd_iff :
    z ∈ lexProd R a S b ↔ ∃ x₁ ∈ a, ∃ y₁ ∈ b, ∃ x₂ ∈ a, ∃ y₂ ∈ b,
      z = !(!(x₁, y₁), !(x₂, y₂)) ∧ (x₁ [R] x₂ ∨ (x₁ = x₂ ∧ y₁ [S] y₂)) := by
  simp +contextual [lexProd, lexProd₀, cons_nat, init_def, iff_def]

@[simp, grind =]
theorem rel_lexProd_iff :
    !(x₁, y₁) [lexProd R a S b] !(x₂, y₂) ↔
      (x₁ ∈ a ∧ y₁ ∈ b) ∧ (x₂ ∈ a ∧ y₂ ∈ b) ∧ (x₁ [R] x₂ ∨ (x₁ = x₂ ∧ y₁ [S] y₂)) := by
  simp only [mem_lexProd_iff]
  grind

theorem lexProd_subset_sprod : lexProd R a S b ⊆ (a ×ˢ b) ×ˢ (a ×ˢ b) := by
  grind [mem_lexProd_iff]

@[simp, grind .]
theorem isRelationOn_lexProd : IsRelationOn (lexProd R a S b) (a ×ˢ b) :=
  (isRelationOn_sprod _).subset lexProd_subset_sprod

end LexProd

end MemStructure

end FirstOrder.Language
