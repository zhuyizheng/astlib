/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.Ordinal.Basic
/-!
# The order on ordinals

`a <ₒ b` says that `a` and `b` are ordinals with `a ∈ b`, and `a ≤ₒ b` says that `a` and `b` are
ordinals with `a ∈ b ∨ a = b`. On ordinals, `≤ₒ` is `⊆` (`ole_iff_subset`) and the order is total
(`olt_trichotomy`).
-/

namespace FirstOrder.Language.MemStructure

open FirstOrder Language

variable {L : Language} {M : Type*} [L.MemStructure M] {a b c : M}

/-- The strict order on ordinals -/
def olt (a b : M) : Prop := Ordinal a ∧ Ordinal b ∧ a ∈ b

/-- The order on ordinals -/
def ole (a b : M) : Prop := Ordinal a ∧ Ordinal b ∧ (a ∈ b ∨ a = b)

@[inherit_doc] infix:50 " <ₒ " => olt

@[inherit_doc] infix:50 " ≤ₒ " => ole

/-- `∃ x <ₒ y, p x` is `∃ x, x <ₒ y ∧ p x`, and `∀ x <ₒ y, p x` is `∀ x, x <ₒ y → p x` -/
binder_predicate x " <ₒ " y:term => `($x <ₒ $y)

/-- `∃ x ≤ₒ y, p x` is `∃ x, x ≤ₒ y ∧ p x`, and `∀ x ≤ₒ y, p x` is `∀ x, x ≤ₒ y → p x` -/
binder_predicate x " ≤ₒ " y:term => `($x ≤ₒ $y)

@[grind =]
theorem olt_iff : a <ₒ b ↔ Ordinal a ∧ Ordinal b ∧ a ∈ b := .rfl

@[grind =]
theorem ole_iff : a ≤ₒ b ↔ Ordinal a ∧ Ordinal b ∧ (a ∈ b ∨ a = b) := .rfl

/-- `<ₒ` is `Δ₀` -/
instance : Multiclass.DeltaZero (fun ys : Fin 2 → M ↦ ys 0 <ₒ ys 1) Set.univ := by
  unfold olt
  infer_instance

/-- `≤ₒ` is `Δ₀` -/
instance : Multiclass.DeltaZero (fun ys : Fin 2 → M ↦ ys 0 ≤ₒ ys 1) Set.univ := by
  unfold ole
  infer_instance

@[simp, grind .]
theorem olt.ordinal_left (h : a <ₒ b) : Ordinal a := h.left

@[simp, grind .]
theorem olt.ordinal_right (h : a <ₒ b) : Ordinal b := h.right.left

@[simp, grind .]
theorem olt.mem (h : a <ₒ b) : a ∈ b := h.right.right

@[simp, grind .]
theorem ole.ordinal_left (h : a ≤ₒ b) : Ordinal a := h.left

@[simp, grind .]
theorem ole.ordinal_right (h : a ≤ₒ b) : Ordinal b := h.right.left

@[simp]
theorem olt_iff_mem (ha : Ordinal a) (hb : Ordinal b) : a <ₒ b ↔ a ∈ b := by grind

theorem ole_iff_mem_or_eq (ha : Ordinal a) (hb : Ordinal b) : a ≤ₒ b ↔ a ∈ b ∨ a = b := by grind

theorem mem_or_eq_of_ole (h : a ≤ₒ b) : a ∈ b ∨ a = b := h.right.right

theorem ole_iff_olt_or_eq : a ≤ₒ b ↔ a <ₒ b ∨ (Ordinal a ∧ a = b) := by grind

@[simp, grind .]
theorem ole_refl (ha : Ordinal a) : a ≤ₒ a := by grind

@[grind .]
theorem olt.ole (h : a <ₒ b) : a ≤ₒ b := by grind

@[grind .]
theorem olt_trans (hab : a <ₒ b) (hbc : b <ₒ c) : a <ₒ c := by grind

@[grind .]
theorem olt_of_olt_of_ole (hab : a <ₒ b) (hbc : b ≤ₒ c) : a <ₒ c := by grind

@[grind .]
theorem olt_of_ole_of_olt (hab : a ≤ₒ b) (hbc : b <ₒ c) : a <ₒ c := by grind

theorem olt_of_ole_of_ne (h : a ≤ₒ b) (hne : a ≠ b) : a <ₒ b := by grind

@[grind .]
theorem ole_trans (hab : a ≤ₒ b) (hbc : b ≤ₒ c) : a ≤ₒ c := by grind

section Foundational

variable [Inhabited M] [RudClosed M]

@[simp, grind .]
theorem not_olt_empty (a : M) : ¬a <ₒ ∅ := by grind

variable [Foundational M]

@[simp, grind .]
theorem olt_irrefl (a : M) : ¬a <ₒ a := by grind
variable [Extensional M]

theorem olt.asymm (h : a <ₒ b) : ¬b <ₒ a := by grind

@[grind .]
theorem ole_antisymm (hab : a ≤ₒ b) (hba : b ≤ₒ a) : a = b := by grind

end Foundational

variable [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [Extensional M] [RudClosed M]
  [Foundational M]

@[grind .]
theorem olt_of_mem (hb : Ordinal b) (h : a ∈ b) : a <ₒ b := ⟨ordinal_of_mem hb h, hb, h⟩

/-- Below an ordinal, `<ₒ` is `∈` -/
theorem olt_iff_mem' (hb : Ordinal b) : a <ₒ b ↔ a ∈ b := ⟨fun h ↦ h.right.right, olt_of_mem hb⟩

/-- On ordinals, `≤ₒ` is `⊆` -/
theorem ole_iff_subset (ha : Ordinal a) (hb : Ordinal b) : a ≤ₒ b ↔ a ⊆ b := by grind

@[grind .]
theorem olt_trichotomy (ha : Ordinal a) (hb : Ordinal b) : a <ₒ b ∨ a = b ∨ b <ₒ a := by
  simpa [ha, hb] using ordinal_compatible ha hb

/-- If `a` is not below `b`, then `a = b` or `b <ₒ a`: used to prove `a <ₒ b` by contradiction -/
theorem eq_or_olt_of_not_olt (ha : Ordinal a) (hb : Ordinal b) (h : ¬a <ₒ b) : a = b ∨ b <ₒ a := by
  grind

/-- Distinct ordinals are comparable by `<ₒ` -/
theorem olt_or_olt_of_ne (ha : Ordinal a) (hb : Ordinal b) (h : a ≠ b) : a <ₒ b ∨ b <ₒ a := by
  grind

theorem ole_total (ha : Ordinal a) (hb : Ordinal b) : a ≤ₒ b ∨ b ≤ₒ a := by
  grind

theorem olt_or_ole (ha : Ordinal a) (hb : Ordinal b) : a <ₒ b ∨ b ≤ₒ a := by
  grind

theorem not_ole_iff (ha : Ordinal a) (hb : Ordinal b) : ¬a ≤ₒ b ↔ b <ₒ a := by
  grind

theorem not_olt_iff (ha : Ordinal a) (hb : Ordinal b) : ¬a <ₒ b ↔ b ≤ₒ a := by
  grind

omit [Foundational M] in
@[simp]
theorem olt_succ_iff (hb : Ordinal b) : a <ₒ succ b ↔ a ≤ₒ b := by grind

@[simp, grind .]
theorem olt_succ (ha : Ordinal a) : a <ₒ succ a := by simp [ha]

@[simp, grind =]
theorem succ_ole_iff (ha : Ordinal a) (hb : Ordinal b) : succ a ≤ₒ b ↔ a <ₒ b := by grind

/-- A nonzero limit ordinal is closed under successors -/
theorem NonZeroLimOrdinal.succ_olt (ha : NonZeroLimOrdinal a) (hb : b <ₒ a) : succ b <ₒ a :=
  olt_of_mem ha.ordinal (ha.succ_mem hb.mem)

/-- A nonzero ordinal in which every element is below another is a nonzero limit -/
theorem nonZeroLimOrdinal_of_forall_exists_olt (ha : Ordinal a) (ha₀ : a ≠ ∅)
    (h : ∀ b <ₒ a, ∃ c <ₒ a, b <ₒ c) : NonZeroLimOrdinal a := by
  rcases ha.cases_of_ne_empty ha₀ with ⟨β, hβ, rfl⟩ | hlim
  · obtain ⟨c, hc, hβc⟩ := h β (olt_succ hβ)
    grind
  · exact hlim

theorem empty_ole (hb : Ordinal b) : ∅ ≤ₒ b := by grind

@[grind .]
theorem empty_olt_succ (hb : Ordinal b) : ∅ <ₒ succ b := by grind

section MaxMin

/-- The maximum of two ordinals -/
noncomputable abbrev omax₂ (a b : M) : M := a ∪ b

/-- The minimum of two ordinals -/
noncomputable abbrev omin₂ (a b : M) : M := a ∩ b

@[simp, grind .]
theorem ordinal_omax₂ (ha : Ordinal a) (hb : Ordinal b) : Ordinal (omax₂ a b) :=
  ordinal_union ha hb

omit [Foundational M] in
@[simp, grind .]
theorem ordinal_omin₂ (ha : Ordinal a) (hb : Ordinal b) : Ordinal (omin₂ a b) :=
  ordinal_inter ha hb

@[simp, grind =]
theorem omax₂_eq_right (h : a ≤ₒ b) : omax₂ a b = b := by
  grind

@[simp, grind =]
theorem omax₂_eq_left (h : b ≤ₒ a) : omax₂ a b = a := by
  grind

@[simp, grind =]
theorem omin₂_eq_left (h : a ≤ₒ b) : omin₂ a b = a := by
  grind

@[simp, grind =]
theorem omin₂_eq_right (h : b ≤ₒ a) : omin₂ a b = b := by
  grind

theorem ole_omax₂_left (ha : Ordinal a) (hb : Ordinal b) : a ≤ₒ omax₂ a b := by
  grind

theorem ole_omax₂_right (ha : Ordinal a) (hb : Ordinal b) : b ≤ₒ omax₂ a b := by
  grind

theorem omin₂_ole_left (ha : Ordinal a) (hb : Ordinal b) : omin₂ a b ≤ₒ a := by
  grind

theorem omin₂_ole_right (ha : Ordinal a) (hb : Ordinal b) : omin₂ a b ≤ₒ b := by
  grind

/-- `omax₂ a b` is the least upper bound of `a` and `b` -/
@[simp, grind =]
theorem omax₂_ole_iff (ha : Ordinal a) (hb : Ordinal b) (hc : Ordinal c) :
    omax₂ a b ≤ₒ c ↔ a ≤ₒ c ∧ b ≤ₒ c := by
  grind

/-- `omin₂ a b` is the greatest lower bound of `a` and `b` -/
@[simp, grind =]
theorem ole_omin₂_iff (ha : Ordinal a) (hb : Ordinal b) (hc : Ordinal c) :
    c ≤ₒ omin₂ a b ↔ c ≤ₒ a ∧ c ≤ₒ b := by
  grind

@[simp, grind =]
theorem omax₂_olt_iff (ha : Ordinal a) (hb : Ordinal b) :
    omax₂ a b <ₒ c ↔ a <ₒ c ∧ b <ₒ c := by
  grind

@[simp, grind =]
theorem olt_omin₂_iff (ha : Ordinal a) (hb : Ordinal b) :
    c <ₒ omin₂ a b ↔ c <ₒ a ∧ c <ₒ b := by
  grind

/-- If `a <ₒ b` and `omax₂ a c = b`, then `c = b` -/
theorem eq_of_omax₂_eq_of_olt (hc : Ordinal c) (ha : a <ₒ b) (h : omax₂ a c = b) : c = b := by
  grind

end MaxMin

/-- `F` is an order homomorphism of the ordinals: it maps ordinals to ordinals and is strictly
increasing -/
def IsOrderHom (F : ClassFunction M) : Prop :=
  (∀ x, Ordinal x → Ordinal (F x)) ∧ ∀ x y, y <ₒ x → F y <ₒ F x

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [Extensional M] [RudClosed M]
  [Foundational M] in
@[grind .]
theorem IsOrderHom.ordinal {F : ClassFunction M} (hF : IsOrderHom F) {x : M} (hx : Ordinal x) :
    Ordinal (F x) :=
  hF.left x hx

omit [L.ExtraConstantsUnaryRelationsOnly] [Inhabited M] [Extensional M] [RudClosed M]
  [Foundational M] in
@[grind .]
theorem IsOrderHom.olt {F : ClassFunction M} (hF : IsOrderHom F) {x y : M} (h : y <ₒ x) :
    F y <ₒ F x :=
  hF.right x y h

/-- `f` is an order homomorphism from the ordinal `a` to the ordinal `b`: a function from `a` to
`b` that is strictly increasing -/
def IsOrderHomOn (f a b : M) : Prop :=
  Ordinal a ∧ Ordinal b ∧ f !: a → b ∧ ∀ x <ₒ a, ∀ y <ₒ x, f ﹫ y <ₒ f ﹫ x

omit [Extensional M] [RudClosed M] [Foundational M] in
@[simp, grind .]
theorem IsOrderHomOn.ordinal_left {f : M} (hf : IsOrderHomOn f a b) : Ordinal a := hf.left

omit [Extensional M] [RudClosed M] [Foundational M] in
@[simp, grind .]
theorem IsOrderHomOn.ordinal_right {f : M} (hf : IsOrderHomOn f a b) : Ordinal b :=
  hf.right.left

omit [Extensional M] [RudClosed M] [Foundational M] in
@[simp, grind .]
theorem IsOrderHomOn.isFunctionFromTo {f : M} (hf : IsOrderHomOn f a b) : f !: a → b :=
  hf.right.right.left

omit [Extensional M] [RudClosed M] [Foundational M] in
@[grind .]
theorem IsOrderHomOn.olt {f x y : M} (hf : IsOrderHomOn f a b) (hx : x <ₒ a) (hy : y <ₒ x) :
    f ﹫ y <ₒ f ﹫ x :=
  hf.right.right.right x hx y hy

/-- An order homomorphism of ordinals reflects `<ₒ` -/
theorem IsOrderHomOn.olt_iff {f x y : M} (hf : IsOrderHomOn f a b) (hx : x <ₒ a) (hy : y <ₒ a) :
    f ﹫ y <ₒ f ﹫ x ↔ y <ₒ x := by
  refine ⟨fun h ↦ ?_, hf.olt hx⟩
  by_contra h'
  have h'' := (eq_or_olt_of_not_olt hy.ordinal_left hx.ordinal_left h').resolve_left (by grind)
  grind [hf.olt hy h'']

/-- An order homomorphism of ordinals is injective -/
theorem IsOrderHomOn.isInjectionFromTo {f : M} (hf : IsOrderHomOn f a b) : f !: a ↪ b := by
  have ha : Ordinal a := by grind
  refine ⟨hf.isFunctionFromTo, fun x y hx hy h ↦ ?_⟩
  by_contra! hne
  rcases olt_or_olt_of_ne (ordinal_of_mem ha hx) (ordinal_of_mem ha hy) hne with h' | h'
  · grind [hf.olt (olt_of_mem ha hy) h']
  · grind [hf.olt (olt_of_mem ha hx) h']

/-- The identity on an ordinal is an order homomorphism -/
theorem isOrderHomOn_id (ha : Ordinal a) : IsOrderHomOn (id a) a a :=
  ⟨ha, ha, isFunctionFromTo_id a, fun x hx y hy ↦ by grind⟩

/-- An order homomorphism of the ordinals reflects `<ₒ` -/
theorem IsOrderHom.olt_iff {F : ClassFunction M} (hF : IsOrderHom F) {x y : M}
    (hx : Ordinal x) (hy : Ordinal y) : F x <ₒ F y ↔ x <ₒ y := by
  grind

/-- An order homomorphism of the ordinals is injective -/
theorem IsOrderHom.eq_iff {F : ClassFunction M} (hF : IsOrderHom F) {x y : M}
    (hx : Ordinal x) (hy : Ordinal y) : F x = F y ↔ y = x := by
  grind

section SupInf

variable {S : M}

/-- The supremum of a set of ordinals -/
noncomputable def osup : ClassFunction M := fun S ↦ ⋃₀ S

theorem ordinal_osup (hS : ∀ x ∈ S, Ordinal x) : Ordinal (osup S) := ordinal_sUnion hS

theorem ole_osup (hS : ∀ x ∈ S, Ordinal x) (hx : a ∈ S) : a ≤ₒ osup S := by
  rw [ole_iff_subset (hS a hx) (ordinal_osup hS)]
  intro z hz
  simp only [osup, mem_sUnion_iff]
  exact ⟨a, hx, hz⟩

/-- `osup S` is the least upper bound of `S` -/
theorem osup_ole_iff (hS : ∀ x ∈ S, Ordinal x) (hb : Ordinal b) :
    osup S ≤ₒ b ↔ ∀ x ∈ S, x ≤ₒ b := by
  refine ⟨fun h x hx ↦ ole_trans (ole_osup hS hx) h, fun h ↦ ?_⟩
  rw [ole_iff_subset (ordinal_osup hS) hb]
  intro z hz
  simp only [osup, mem_sUnion_iff] at hz
  obtain ⟨x, hx, hzx⟩ := hz
  specialize h x hx
  rw [ole_iff_subset (hS x hx) hb] at h
  exact h hzx

theorem olt_osup_iff (hS : ∀ x ∈ S, Ordinal x) (ha : Ordinal a) :
    a <ₒ osup S ↔ ∃ x ∈ S, a <ₒ x := by
  simp only [osup, olt_iff_mem, ha, ordinal_sUnion hS, mem_sUnion_iff]
  grind

/-- The minimum of a nonempty set of ordinals -/
noncomputable def omin : ClassFunction M := fun S ↦ memMin S

variable (hS : ∀ x ∈ S, Ordinal x) (hS₀ : S ≠ ∅)
include hS hS₀

omit hS [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [RudClosed M] in
theorem omin_mem : omin S ∈ S := memMin_mem hS₀

omit [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [RudClosed M] in
theorem ordinal_omin : Ordinal (omin S) := hS _ (omin_mem hS₀)

/-- `omin S` is the least element of `S` -/
theorem omin_ole (hx : a ∈ S) : omin S ≤ₒ a := by
  rw [← not_olt_iff (hS a hx) (ordinal_omin hS hS₀), olt_iff_mem (hS a hx) (ordinal_omin hS hS₀)]
  exact fun h ↦ notMem_of_mem_memMin h hx

theorem ole_omin_iff : b ≤ₒ omin S ↔ ∀ x ∈ S, b ≤ₒ x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ h _ (omin_mem hS₀)⟩
  exact ole_trans h (omin_ole hS hS₀ hx)

end SupInf

/-- `η ↦ osup (ran (f ↾ η))`: the supremum of the values of `f` on `η` -/
noncomputable def supRange (f : M) : ClassFunction M := fun η ↦ osup (ran (f ↾ η))

section SupRange

variable {f η ξ : M}

omit [Foundational M] in
/-- The values of `f ↾ η` are the `f ﹫ ξ` with `ξ ∈ η` -/
theorem IsFunction.mem_ran_restrict_iff (hf : IsFunction f) (hs : η ⊆ dom f) {y : M} :
    y ∈ ran (f ↾ η) ↔ ∃ ξ ∈ η, f ﹫ ξ = y := by
  rw [(hf.restrict η).mem_ran_iff, dom_restrict_of_subset hf hs]
  refine exists_congr fun ξ ↦ and_congr_right fun hξ ↦ ?_
  rw [val_restrict _ hf hξ (hs hξ)]

variable (hr : ∀ y ∈ ran f, Ordinal y)
include hr

omit [Foundational M] in
/-- If the values of `f` are ordinals, so are the values of `f ↾ η` -/
theorem ordinal_of_mem_ran_restrict {y : M} (hy : y ∈ ran (f ↾ η)) : Ordinal y :=
  hr y (ran_mono (restrict_subset f η) hy)

/-- If the values of `f` are ordinals, `supRange f η` is an ordinal -/
theorem ordinal_supRange : Ordinal (supRange f η) :=
  ordinal_osup fun _ ↦ ordinal_of_mem_ran_restrict hr

variable (hf : IsFunction f) (hs : η ⊆ dom f)
include hf hs

/-- `supRange f η` bounds the values of `f` on `η` -/
theorem val_ole_supRange (hξ : ξ ∈ η) : f ﹫ ξ ≤ₒ supRange f η :=
  ole_osup (fun _ ↦ ordinal_of_mem_ran_restrict hr) ((hf.mem_ran_restrict_iff hs).mpr ⟨ξ, hξ, rfl⟩)

/-- `supRange f η` is the least upper bound of the values of `f` on `η` -/
theorem supRange_ole_iff {b : M} (hb : Ordinal b) :
    supRange f η ≤ₒ b ↔ ∀ ξ ∈ η, f ﹫ ξ ≤ₒ b := by
  rw [supRange, osup_ole_iff (fun _ ↦ ordinal_of_mem_ran_restrict hr) hb]
  simp [hf.mem_ran_restrict_iff hs]

/-- An ordinal is below `supRange f η` iff it is below some value of `f` on `η` -/
theorem olt_supRange_iff {a : M} (ha : Ordinal a) :
    a <ₒ supRange f η ↔ ∃ ξ ∈ η, a <ₒ f ﹫ ξ := by
  rw [supRange, olt_osup_iff (fun _ ↦ ordinal_of_mem_ran_restrict hr) ha]
  simp [hf.mem_ran_restrict_iff hs]

end SupRange

section ModelsKP

variable [ModelsKP M]

/-- Transfinite induction on ordinals -/
theorem ordinal_induction {A : Class M} [A.Definable Set.univ]
    (h : ∀ x, Ordinal x → (∀ y <ₒ x, A y) → A x) {x : M} (hx : Ordinal x) : A x :=
  induction_of_modelsKP (A := Ordinal ⟹ A)
    (fun x ih hx ↦ h x hx fun y hy ↦ ih y hy.mem hy.ordinal_left) x hx

/-- Transfinite induction on ordinals by cases: zero, successors and nonzero limits -/
theorem ordinal_induction' {A : Class M} [A.Definable Set.univ] (hzero : A ∅)
    (hsucc : ∀ x, Ordinal x → A x → A (succ x))
    (hlimit : ∀ x, NonZeroLimOrdinal x → (∀ y <ₒ x, A y) → A x) {x : M} (hx : Ordinal x) :
    A x := by
  refine ordinal_induction (fun x hx ih ↦ ?_) hx
  rcases hx.cases with rfl | ⟨y, hy, rfl⟩ | hx
  · exact hzero
  · exact hsucc y hy (ih y (olt_succ hy))
  · exact hlimit x hx ih

/-- Two `Σ₁` class functions agree on the ordinals if they agree at each ordinal whenever they
agree below it -/
theorem ordinal_induction_eq {F G : ClassFunction M} [F.Sigma 1 Set.univ] [G.Sigma 1 Set.univ]
    (h : ∀ x, Ordinal x → (∀ y <ₒ x, F y = G y) → F x = G x) {x : M} (hx : Ordinal x) :
    F x = G x :=
  ordinal_induction h hx

/-- An order homomorphism between ordinals is pointwise `≥ id` -/
theorem IsOrderHomOn.ole_apply {f : M} (hf : IsOrderHomOn f a b) {x : M} (hx' : x <ₒ a) :
    x ≤ₒ f ﹫ x := by
  have hx := hx'.mem
  have ha : Ordinal a := by grind
  have hfx {x : M} (hx : x ∈ a) : Ordinal (f ﹫ x) :=
    ordinal_of_mem hf.ordinal_right (hf.isFunctionFromTo.val_mem hx)
  rw [ole_iff_subset (ordinal_of_mem ha hx) (hfx hx)]
  -- induct on the definable class `x ∈ a → x ⊆ f ﹫ x`, as `Subset` composed with `Σ₁` functions
  let Fs : Fin 2 → MulticlassFunction M 1 :=
    ![ClassFunction.toMulticlassFunction _root_.id,
      ClassFunction.toMulticlassFunction fun y ↦ f ﹫ y]
  have hA (x : M) : (Class.Mem a ⟹ ((Multiclass.Subset (0 : Fin 2) 1).subst Fs : Class M)) x ↔
      (x ∈ a → x ⊆ f ﹫ x) := by
    tauto
  suffices (Class.Mem a ⟹ ((Multiclass.Subset (0 : Fin 2) 1).subst Fs : Class M)) x by grind
  refine ordinal_induction (fun x hx ih ↦ ?_) (ordinal_of_mem ha hx)
  simp only [hA] at ih ⊢
  intro hxa z hz
  have hxo : Ordinal x := ordinal_of_mem ha hxa
  grind [ole_iff_subset, ole_iff_mem_or_eq,
    (hf.olt (olt_of_mem ha hxa) (olt_of_mem hxo hz)).mem]

/-- If there is an order homomorphism from the ordinal `a` to the ordinal `b`, then `a ≤ₒ b` -/
theorem IsOrderHomOn.ole {f : M} (hf : IsOrderHomOn f a b) : a ≤ₒ b := by
  rw [ole_iff_subset hf.ordinal_left hf.ordinal_right]
  intro x hx
  grind [hf.ole_apply (olt_of_mem hf.ordinal_left hx), hf.isFunctionFromTo.val_mem hx]

/-- The restriction of a `Σ₁` order homomorphism of the ordinals to an ordinal `a` mapped into an
ordinal `b` is an order homomorphism from `a` to `b` -/
theorem IsOrderHom.isOrderHomOn {F : ClassFunction M} [F.Sigma 1 Set.univ] (hF : IsOrderHom F)
    (ha : Ordinal a) (hb : Ordinal b) (hab : ∀ x <ₒ a, F x <ₒ b) : IsOrderHomOn (F ↾₀ a) a b := by
  have hFa : IsSetRestrictedTo F a := isSetRestrictedTo_of_sigma (G := F) a
  refine ⟨ha, hb, isFunctionFromTo_toSetRestrictedTo hFa fun x hx ↦ (hab x (olt_of_mem ha hx)).mem,
    fun x hx y hy ↦ ?_⟩
  rw [val_toSetRestrictedTo hFa hx.mem, val_toSetRestrictedTo hFa (by grind)]
  exact hF.olt hy

/-- A `Σ₁` order homomorphism of the ordinals is pointwise `≥ id` -/
theorem IsOrderHom.ole_apply {F : ClassFunction M} [F.Definable Set.univ] (hF : IsOrderHom F)
    {x : M} (hx : Ordinal x) : x ≤ₒ F x := by
  -- `x ⊆ F x` by induction on `x`
  rw [ole_iff_subset hx (hF.ordinal hx)]
  refine ordinal_induction (A := fun x ↦ x ⊆ F x) (fun x hx ih y hy ↦ ?_) hx
  have hyx : y <ₒ x := olt_of_mem hx hy
  have hy' : y ≤ₒ F y := by
    rw [ole_iff_subset hyx.ordinal_left (hF.ordinal hyx.ordinal_left)]
    exact ih y hyx
  exact (olt_of_ole_of_olt hy' (hF.olt hyx)).mem

/-- A definable class function on the ordinals that grows strictly at successors and is the union
of its earlier values at limits is strictly increasing -/
theorem subset_ne_of_succ_of_limit {F : ClassFunction M} [F.Definable Set.univ]
    (hsucc : ∀ α, Ordinal α → F α ⊆ F (succ α) ∧ F α ≠ F (succ α))
    (hlim : ∀ α, NonZeroLimOrdinal α → ∀ x, x ∈ F α ↔ ∃ β ∈ α, x ∈ F β) {α β : M}
    (hα : Ordinal α) (hβ : β ∈ α) : F β ⊆ F α ∧ F β ≠ F α := by
  -- `∀ β ∈ α, F β ⊆ F α ∧ F β ≠ F α` by induction on `α`
  refine ordinal_induction (A := fun α ↦ ∀ β ∈ α, F β ⊆ F α ∧ F β ≠ F α)
    (fun α hα ih β hβ ↦ ?_) hα β hβ
  rcases hα.cases_of_ne_empty (by grind) with ⟨γ, hγ, rfl⟩ | hl
  · simp only [mem_succ_iff] at hβ
    grind
  · -- `F (succ β) ⊆ F α` with `succ β ∈ α`
    have h₃ : F (succ β) ⊆ F α := fun x hx ↦ by grind
    grind

/-- A definable class function on the ordinals that is increasing at successors and continuous at
limits is an order homomorphism -/
theorem isOrderHom_of_succ_of_limit {F : ClassFunction M} [F.Definable Set.univ]
    (hsucc : ∀ α, Ordinal α → F α <ₒ F (succ α))
    (hlim : ∀ α, NonZeroLimOrdinal α → ∀ x, x <ₒ F α ↔ ∃ β <ₒ α, x <ₒ F β) : IsOrderHom F := by
  have hF {α : M} (hα : Ordinal α) : Ordinal (F α) := by grind
  -- continuity at limits in terms of `∈`
  have hlim' (γ : M) (hγ : NonZeroLimOrdinal γ) (x : M) : x ∈ F γ ↔ ∃ β ∈ γ, x ∈ F β := by
    refine ⟨fun hx ↦ ?_, by grind⟩
    have h := olt_of_mem (hF hγ.ordinal) hx
    rw [hlim γ hγ] at h
    obtain ⟨β, hβ, hxβ⟩ := h
    exact ⟨β, hβ.mem, hxβ.mem⟩
  refine ⟨fun α hα ↦ hF hα, fun α β h ↦ ?_⟩
  have := subset_ne_of_succ_of_limit (fun γ hγ ↦ ⟨by grind, by grind⟩) hlim' (by grind) h.mem
  grind

omit [Extensional M] [RudClosed M] [Foundational M] in
/-- A nonempty definable class of ordinals has a least element -/
theorem exists_min_ordinal {A : Class M} [A.Definable Set.univ] (ha : Ordinal a) (hA : A a) :
    ∃ b, Ordinal b ∧ A b ∧ ∀ c ∈ b, ¬A c := by
  by_contra! h
  refine ordinal_induction (A := ∼A) (fun b hb ih ↦ ?_) ha hA
  simp only [Class.not_iff]
  intro hAb
  obtain ⟨c, hc, hAc⟩ := h b hb hAb
  exact ih c (olt_of_mem hb hc) hAc

/-- The least ordinal in `A`, or `∅` if there is none -/
noncomputable def Class.omin (A : Class M) : M :=
  @dite _ (∃ b, Ordinal b ∧ A b ∧ ∀ c ∈ b, ¬A c) (Classical.propDecidable _) Classical.choose
    fun _ ↦ ∅

omit [Extensional M] [RudClosed M] [Foundational M] in
theorem Class.omin_spec {A : Class M} [A.Definable Set.univ] (ha : Ordinal a) (hA : A a) :
    Ordinal (A.omin) ∧ A (A.omin) ∧ ∀ c ∈ A.omin, ¬A c := by
  have h : ∃ b, Ordinal b ∧ A b ∧ ∀ c ∈ b, ¬A c := exists_min_ordinal ha hA
  simp only [Class.omin, h, ↓reduceDIte]
  exact Classical.choose_spec h

omit [Foundational M] [ModelsKP M] in
/-- `A.omin` is an ordinal -/
@[grind .]
theorem Class.ordinal_omin (A : Class M) : Ordinal (A.omin) := by
  unfold Class.omin
  split_ifs with h
  · exact (Classical.choose_spec h).left
  · exact ordinal_empty

omit [Extensional M] [RudClosed M] [Foundational M] in
theorem Class.omin_mem {A : Class M} [A.Definable Set.univ] (ha : Ordinal a) (hA : A a) :
    A (A.omin) :=
  (Class.omin_spec ha hA).right.left

omit [Extensional M] [RudClosed M] [Foundational M] in
theorem Class.not_of_mem_omin {A : Class M} [A.Definable Set.univ] (ha : Ordinal a) (hA : A a)
    (hb : b ∈ A.omin) : ¬A b :=
  (Class.omin_spec ha hA).right.right b hb

/-- The least ordinal in `A` is below every ordinal in `A` -/
theorem Class.omin_ole {A : Class M} [A.Definable Set.univ] (ha : Ordinal a) (hA : A a) :
    A.omin ≤ₒ a := by
  have ho : Ordinal A.omin := Class.ordinal_omin A
  rw [← not_olt_iff ha ho, olt_iff_mem ha ho]
  exact fun h ↦ Class.not_of_mem_omin ha hA h hA

/-- A least ordinal in `A` is `A.omin` -/
theorem Class.omin_eq {A : Class M} [A.Definable Set.univ] (ha : Ordinal a) (hA : A a)
    (hmin : ∀ c ∈ a, ¬A c) : A.omin = a := by
  rcases ordinal_compatible (Class.ordinal_omin A) ha with h | h | h <;> grind [Class.omin_spec]

omit [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [RudClosed M] [Foundational M]
  [ModelsKP M] in
theorem Class.omin_eq_empty {A : Class M} (h : ∀ a, Ordinal a → ¬A a) : A.omin = ∅ := by
  have : ¬∃ b, Ordinal b ∧ A b ∧ ∀ c ∈ b, ¬A c := by grind
  simp [Class.omin, this]

/-- The least ordinal of a class depending definably on a parameter is a definable class function
of the parameter -/
instance (A : Multiclass M 2) [A.Definable Set.univ] :
    ClassFunction.Definable (fun x ↦ Class.omin fun y ↦ A ![x, y]) Set.univ := by
  -- `v` is the least ordinal with `A ![x, v]`, or no ordinal `c` has `A ![x, c]` and `v = ∅`
  refine ClassFunction.Definable.of_iff (F := fun xs ↦
    (Ordinal (xs 1) ∧ A ![xs 0, xs 1] ∧ ∀ c ∈ xs 1, ¬A ![xs 0, c]) ∨
      ((∀ c, Ordinal c → ¬A ![xs 0, c]) ∧ ∀ c, c ∉ xs 1)) fun x v ↦ ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases h : ∃ c, Ordinal c ∧ A ![x, c]
  · grind [Class.omin_eq, Class.omin_spec]
  · grind [Class.omin_eq_empty, empty_iff (x := v)]

/-- The least element of a fixed set `S` in a `Δ₀` relation with `x` is a `Σ₁` class function of
`x` -/
instance (S : M) {R : M → M → Prop}
    [Multiclass.DeltaZero (fun ys : Fin 2 → M ↦ R (ys 0) (ys 1)) Set.univ] :
    ClassFunction.Sigma (fun x ↦ Class.omin fun ξ ↦ ξ ∈ S ∧ R x ξ) 1 Set.univ := by
  -- `w` is the least ordinal of `S` in relation with `x`, or there is none and `w = ∅`
  refine ClassFunction.Sigma.of_iff (F := fun xs ↦
    (Ordinal (xs 1) ∧ xs 1 ∈ S ∧ R (xs 0) (xs 1) ∧ ∀ c ∈ xs 1, ¬(c ∈ S ∧ R (xs 0) c)) ∨
      ((∀ c ∈ S, Ordinal c → ¬R (xs 0) c) ∧ xs 1 = ∅)) (hF := by infer_instance) fun x w ↦ ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases h : ∃ ξ ∈ S, Ordinal ξ ∧ R x ξ
  swap
  · grind [Class.omin_eq_empty]
  obtain ⟨ξ, hξ, hξo, hxξ⟩ := h
  have hspec := Class.omin_spec (A := fun ξ ↦ ξ ∈ S ∧ R x ξ) hξo ⟨hξ, hxξ⟩
  refine ⟨?_, fun hw ↦ .inl ?_⟩
  · rintro (⟨hwo, hwS, hxw, hmin⟩ | ⟨hno, -⟩)
    · exact Class.omin_eq hwo ⟨hwS, hxw⟩ hmin
    · grind
  · subst hw
    exact ⟨hspec.left, hspec.right.left.left, hspec.right.left.right, hspec.right.right⟩

/-- `supRange f` is `Σ₁` -/
instance (f : M) : (supRange f).Sigma 1 Set.univ :=
  ClassFunction.Sigma.of_iff (F := fun xs ↦ ⋃₀ ran (f ↾ xs 0) = xs 1)
    (hF := by infer_instance) fun η w ↦ by simp [supRange, osup]

end ModelsKP

end FirstOrder.Language.MemStructure
