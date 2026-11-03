/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Function.Restrict
/-!
# Modifying functions

Pointwise modifications of functions:

* `erase f x`: `f` with the point at `x` removed;
* `update f x y`: `f` with the value at `x` set to `y`, and `singletonFun x y`;
* `eraseRedirect f x y`: `f` with `x` removed and the preimage of `y` sent to `f ﹫ x`;
* `moveKey f x y`: `f` with the key `x` moved to `y`;
* `insertVal f x y`: `f` with `y` added to the value at `x`.
-/

open Fin FirstOrder Language MemStructure RudimentaryTerm DeltaZeroBoundedFormula

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M]

section Update

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

/-- The rudimentary term for `erase f x`: `f ↾ (dom f \ {x})` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.erase₀
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 2 :=
  (ᵣ0 : L.RudimentaryTerm 2) ↾ ((ᵣ0 : L.RudimentaryTerm 2).dom \ {ᵣ1})

/-- The rudimentary term for `erase r s` -/
@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.erase
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  erase₀.substBoundRud ![r, s]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (erase₀ : L.RudimentaryTerm 2).CharFree := by
  unfold erase₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] : (r.erase s).CharFree := by
  unfold RudimentaryTerm.erase; infer_instance

/-- The rudimentary term for `update f x y`: `insert !(x, y) (erase f x)` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.update₀
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 3 :=
  insert ᵣ(ᵣ1, ᵣ2) (erase₀.substBoundRud ![ᵣ0, ᵣ1])

/-- The rudimentary term for `update r s t` -/
@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.update
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s t : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  update₀.substBoundRud ![r, s, t]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (update₀ : L.RudimentaryTerm 3).CharFree := by
  unfold update₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] :
    (r.update s t).CharFree := by
  unfold RudimentaryTerm.update; infer_instance

/-- `f` with the point at `x` removed -/
noncomputable def erase (f x : M) : M := erase₀〘f, x〙₂

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ erase (ys 0) (ys 1)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ erase₀ fun _ _ ↦ rfl

/-- `f` with the value at `x` set to `y` -/
noncomputable def update (f x y : M) : M := update₀〘f, x, y〙₃

instance : MulticlassFunction.DeltaZero (fun ys : Fin 3 → M ↦ update (ys 0) (ys 1) (ys 2))
    Set.univ :=
  MulticlassFunction.deltaZero_of_eq update₀ fun ys ↦ by
    rw [update, show ![ys 0, ys 1, ys 2] = ys by ext i; fin_cases i <;> rfl]

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_erase₀ (xs : Fin 2 → M) :
    erase₀〘xs〙 = erase (xs 0) (xs 1) := by
  simp only [erase]
  rw [Matrix.vec_fin_two_eq]

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_update₀ (xs : Fin 3 → M) :
    update₀〘xs〙 = update (xs 0) (xs 1) (xs 2) := by
  simp only [update]
  congr
  ext i; fin_cases i <;> rfl

omit [RudClosed M] in
theorem erase_eq (f x : M) : erase f x = f ↾ (dom f \ {x}) := by
  simp [erase, erase₀]

omit [RudClosed M] in
theorem update_eq (f x y : M) : update f x y = insert !(x, y) (erase f x) := by
  simp [update, update₀]

@[simp, grind =]
theorem rel_erase_iff {f x z w : M} : z [erase f x] w ↔ z [f] w ∧ z ≠ x := by
  simp only [erase_eq, rel_restrict_iff, mem_sdiff_iff, mem_singleton_iff]
  grind

@[simp, grind .]
theorem IsFunction.erase {f : M} (hf : IsFunction f) (x : M) : IsFunction (erase f x) := by
  rw [erase_eq]
  exact hf.restrict _

@[simp, grind =]
theorem dom_erase (f x : M) : dom (erase f x) = dom f \ {x} := by
  ext z
  simp only [mem_dom_iff, rel_erase_iff, mem_sdiff_iff, mem_singleton_iff]
  grind

@[simp, grind =]
theorem val_erase {f x z : M} (hf : IsFunction f) (hz : z ∈ dom f) (hzx : z ≠ x) :
    erase f x ﹫ z = f ﹫ z :=
  (hf.erase x).val_eq_of_rel (by simp [rel_val hf hz, hzx])

omit [L.ExtraConstantsUnaryRelationsOnly] in
@[simp, grind =]
theorem rel_insert_iff {f x y z w : M} : z [insert !(x, y) f] w ↔ (z = x ∧ w = y) ∨ z [f] w := by
  simp [mem_insert_iff]

/-- Adding a point `!(x, y)` with `x ∉ dom f` to a function `f` gives a function -/
theorem IsFunction.insert {f x : M} (hf : IsFunction f) (hx : x ∉ dom f) (y : M) :
    IsFunction (insert !(x, y) f) := by
  refine ⟨fun p hp ↦ ?_, fun z w₁ w₂ h₁ h₂ ↦ ?_⟩
  · simp only [mem_insert_iff] at hp
    rcases hp with rfl | hp
    · simp [IsOrderedPair]
    · exact hf.isRelation hp
  · grind

@[simp, grind =]
theorem dom_insert (f x y : M) : dom (insert !(x, y) f) = insert x (dom f) := by
  ext z
  simp [mem_dom_iff, mem_insert_iff, exists_or]

@[simp, grind =]
theorem ran_insert (f x y : M) : ran (insert !(x, y) f) = insert y (ran f) := by
  ext w
  simp [mem_ran_iff, mem_insert_iff, exists_or]

@[simp, grind =]
theorem val_insert_self {f x : M} (hf : IsFunction f) (hx : x ∉ dom f) (y : M) :
    insert !(x, y) f ﹫ x = y :=
  (hf.insert hx y).val_eq_of_rel (by simp)

@[simp, grind =]
theorem val_insert_of_mem {f x z : M} (hf : IsFunction f) (hx : x ∉ dom f) (y : M)
    (hz : z ∈ dom f) : insert !(x, y) f ﹫ z = f ﹫ z :=
  (hf.insert hx y).val_eq_of_rel (by simp [rel_val hf hz])

@[simp, grind .]
theorem IsFunction.update {f : M} (hf : IsFunction f) (x y : M) : IsFunction (update f x y) := by
  simp [update_eq, (hf.erase x).insert]

@[simp, grind =]
theorem dom_update (f x y : M) : dom (update f x y) = insert x (dom f) := by
  ext z
  simp [update_eq]
  tauto

@[simp, grind =]
theorem val_update_self {f : M} (hf : IsFunction f) (x y : M) : update f x y ﹫ x = y := by
  simp [update_eq, hf]

@[simp, grind =]
theorem val_update_of_ne {f x z : M} (hf : IsFunction f) (y : M) (hz : z ∈ dom f) (hzx : z ≠ x) :
    update f x y ﹫ z = f ﹫ z := by
  simp [update_eq, hf, hz, hzx]

/-- The function with domain `{x}` mapping `x` to `y` -/
noncomputable def singletonFun (x y : M) : M := update ∅ x y

@[simp, grind .]
theorem isFunction_singletonFun (x y : M) : IsFunction (singletonFun x y) :=
  isFunction_empty.update x y

@[simp, grind =]
theorem dom_singletonFun (x y : M) : dom (singletonFun x y) = {x} := by
  ext z
  simp [singletonFun, mem_insert_iff]

@[simp, grind =]
theorem singletonFun_val (x y : M) : singletonFun x y ﹫ x = y :=
  val_update_self isFunction_empty x y

@[simp, grind =]
theorem ran_singletonFun (x y : M) : ran (singletonFun x y) = {y} := by
  ext z
  simp only [mem_ran_iff, mem_singleton_iff]
  grind [singletonFun, update_eq]

theorem isFunctionFromTo_singletonFun {x y b : M} (hy : y ∈ b) : singletonFun x y !: {x} → b :=
  ⟨isFunction_singletonFun x y, dom_singletonFun x y, by simpa using hy⟩

/-- `erase (f \ (dom f ×ˢ {y})) x` is `f` without the point `x` and the points mapped to `y` -/
theorem rel_erase_sdiff_sprod_iff {f x y z w : M} :
    z [erase (f \ (dom f ×ˢ ({y} : M))) x] w ↔ (z [f] w ∧ w ≠ y) ∧ z ≠ x := by
  simp only [rel_erase_iff, mem_sdiff_iff, pair_mem_sprod_iff, mem_singleton_iff]
  grind

theorem dom_erase_sdiff_sprod_subset (f x y : M) :
    dom (erase (f \ (dom f ×ˢ ({y} : M))) x) ⊆ dom f \ {x} := by
  intro z hz
  simp only [mem_dom_iff, rel_erase_sdiff_sprod_iff, mem_sdiff_iff, mem_singleton_iff] at hz ⊢
  grind

theorem IsFunction.erase_sdiff_sprod {f : M} (hf : IsFunction f) (x y : M) :
    IsFunction (MemStructure.erase (f \ (dom f ×ˢ ({y} : M))) x) :=
  (hf.subset (sdiff_subset_left _ _)).erase x

/-- `h` patched with the constant function `c` on `a \ dom h` -/
theorem rel_union_constFun_iff {h a c z w : M} :
    z [h ∪ constFun (a \ dom h) c] w ↔ z [h] w ∨ ((z ∈ a ∧ z ∉ dom h) ∧ w = c) := by
  simp [mem_union_iff, mem_sdiff_iff]

theorem IsFunction.union_constFun {h : M} (hh : IsFunction h) (a c : M) :
    IsFunction (h ∪ constFun (a \ dom h) c) :=
  hh.union_of_disjoint (isFunction_constFun _ c) (by simp +contextual [mem_sdiff_iff])

theorem ran_union_constFun_subset (h a c : M) :
    ran (h ∪ constFun (a \ dom h) c) ⊆ insert c (ran h) := by
  intro w hw
  simp only [mem_ran_iff, rel_union_constFun_iff, mem_insert_iff] at hw ⊢
  grind

theorem ran_union_constFun {h a c : M} (hz : ∃ z ∈ a, z ∉ dom h) :
    ran (h ∪ constFun (a \ dom h) c) = insert c (ran h) := by
  ext w
  simp only [mem_ran_iff, rel_union_constFun_iff, mem_insert_iff]
  grind

theorem dom_union_constFun {h a : M} (ha : dom h ⊆ a) (c : M) :
    dom (h ∪ constFun (a \ dom h) c) = a := by
  ext z
  simp only [dom_union, dom_constFun, mem_union_iff, mem_sdiff_iff]
  grind

/-- A surjection from `insert x a` onto `insert y b` with `x ∉ a`, `y ∉ b` and `b ≠ ∅` gives one
from `a` onto `b`: drop `x` and the points mapped to `y` from `f`, then send the points of `a`
left out to `f ﹫ x`, or to any point of `b` if `f ﹫ x = y` -/
theorem exists_isSurjectionFromTo_of_insert {f a b x y : M} (hx : x ∉ a) (hy : y ∉ b)
    (hb : b ≠ ∅) (hf : f !: insert x a ↠ insert y b) : ∃ g, g !: a ↠ b := by
  -- `f'` is `f` without `x` and the points mapped to `y`
  set f' := erase (f \ (dom f ×ˢ ({y} : M))) x
  have hdomf' : dom f' ⊆ a := fun z hz ↦ by
    grind [dom_erase_sdiff_sprod_subset f x y hz]
  have hranf' {w : M} : w ∈ ran f' ↔ ∃ z ∈ a, f ﹫ z = w ∧ w ≠ y := by
    simp only [mem_ran_iff, f', rel_erase_sdiff_sprod_iff, hf.isFunctionFromTo.rel_iff,
      mem_insert_iff]
    constructor <;> grind
  have hranb {w : M} (hw : w ∈ ran f') : w ∈ b := by
    rw [hranf'] at hw
    obtain ⟨z, hz, rfl, hzy⟩ := hw
    have := hf.isFunctionFromTo.val_mem (subset_insert _ _ hz)
    grind
  by_cases hxy : f ﹫ x = y
  · -- `ran f' = b`: patch with any `b₀ ∈ b`
    simp only [ne_empty_iff] at hb
    obtain ⟨b₀, hb₀⟩ := hb
    refine ⟨f' ∪ constFun (a \ dom f') b₀, ?_⟩
    convert ((hf.isFunction.erase_sdiff_sprod x y).union_constFun a b₀).isSurjectionFromTo
      (dom_union_constFun hdomf' b₀)
    ext w
    refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
    · obtain ⟨z, hz, rfl⟩ := hf.exists_mem_val (subset_insert _ _ hw)
      simp only [ran_union, mem_union_iff]
      grind
    · have := ran_union_constFun_subset f' a b₀ hw
      simp only [mem_insert_iff] at this
      grind
  · -- `ran f'` and `f ﹫ x` make up `b`, and `dom f'` misses the preimage of `y`: patch with
    -- `f ﹫ x`
    have hmiss : ∃ z ∈ a, z ∉ dom f' := by
      obtain ⟨z, hz, hzy⟩ := hf.exists_mem_val (mem_insert (x := y) (y := b))
      refine ⟨z, by grind, fun hzf ↦ ?_⟩
      simp only [mem_dom_iff, f', rel_erase_sdiff_sprod_iff, hf.isFunctionFromTo.rel_iff] at hzf
      grind
    refine ⟨f' ∪ constFun (a \ dom f') (f ﹫ x), ?_⟩
    convert ((hf.isFunction.erase_sdiff_sprod x y).union_constFun a _).isSurjectionFromTo
      (dom_union_constFun hdomf' _)
    rw [ran_union_constFun hmiss]
    ext w
    simp only [mem_insert_iff]
    refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
    · obtain ⟨z, hz, rfl⟩ := hf.exists_mem_val (subset_insert _ _ hw)
      grind
    · have := hf.isFunctionFromTo.val_mem (mem_insert (x := x) (y := a))
      grind

/-- `f` with `x` removed and the preimage of `y` sent to `f ﹫ x` -/
noncomputable def eraseRedirect (f x y : M) : M :=
  (erase f x \ (dom f ×ˢ ({y} : M))) ∪ constFun (f⁻¹ '' ({y} : M) \ {x}) (f ﹫ x)

theorem rel_eraseRedirect_iff {f x y z w : M} :
    z [eraseRedirect f x y] w ↔ ((z [f] w ∧ w ≠ y) ∨ (z [f] y ∧ w = f ﹫ x)) ∧ z ≠ x := by
  simp only [eraseRedirect, mem_union_iff, mem_sdiff_iff, rel_erase_iff, pair_mem_sprod_iff,
    mem_singleton_iff, rel_constFun_iff, mem_image_iff, rel_inv, exists_eq_left]
  grind

theorem IsFunction.eraseRedirect {f : M} (hf : IsFunction f) (x y : M) :
    IsFunction (MemStructure.eraseRedirect f x y) := by
  refine ⟨((hf.erase x).isRelation.subset (sdiff_subset_left _ _)).union
    (isFunction_constFun _ _).isRelation, fun z w₁ w₂ h₁ h₂ ↦ ?_⟩
  rw [rel_eraseRedirect_iff] at h₁ h₂
  grind [hf.val_eq_of_rel]

theorem val_eraseRedirect_of_ne {f x y z : M} (hf : IsFunction f) (hz : z ∈ dom f) (hzx : z ≠ x)
    (h : f ﹫ z ≠ y) : eraseRedirect f x y ﹫ z = f ﹫ z :=
  (hf.eraseRedirect x y).val_eq_of_rel (by simp [rel_eraseRedirect_iff, rel_val hf hz, h, hzx])

theorem val_eraseRedirect_of_eq {f x y z : M} (hf : IsFunction f) (hz : z ∈ dom f) (hzx : z ≠ x)
    (h : f ﹫ z = y) : eraseRedirect f x y ﹫ z = f ﹫ x :=
  (hf.eraseRedirect x y).val_eq_of_rel (by simp [rel_eraseRedirect_iff, ← h, rel_val hf hz, hzx])

theorem dom_eraseRedirect (f x y : M) : dom (eraseRedirect f x y) = dom f \ {x} := by
  ext z
  simp only [mem_dom_iff, rel_eraseRedirect_iff, mem_sdiff_iff, mem_singleton_iff]
  grind

/-- An injection `f` from `insert x a` into `insert y b` with `x ∉ a` gives the injection
`eraseRedirect f x y` from `a` into `b` -/
theorem IsInjectionFromTo.eraseRedirect {f a b x y : M} (hx : x ∉ a)
    (hf : f !: insert x a ↪ insert y b) : MemStructure.eraseRedirect f x y !: a ↪ b := by
  refine isInjectionFromTo_of_val (hf.isFunction.eraseRedirect x y) ?_ (fun z hz ↦ ?_)
    fun z hz z' hz' h' ↦ ?_
  · rw [dom_eraseRedirect, hf.isFunctionFromTo.dom_eq]
    ext z
    simp only [mem_sdiff_iff, mem_insert_iff, mem_singleton_iff]
    grind
  · have : f ﹫ x ∈ insert y b := hf.isFunctionFromTo.val_mem (mem_insert _ _)
    have : f ﹫ z ∈ insert y b := hf.isFunctionFromTo.val_mem (subset_insert _ _ hz)
    grind [val_eraseRedirect_of_ne, val_eraseRedirect_of_eq]
  · by_cases hzy : f ﹫ z = y <;> grind [val_eraseRedirect_of_ne, val_eraseRedirect_of_eq]

/-- A bijection `f` from `insert x a` onto `insert y b` with `x ∉ a` and `y ∉ b` gives the bijection
`eraseRedirect f x y` from `a` onto `b` -/
theorem IsBijectionFromTo.eraseRedirect {f a b x y : M} (hx : x ∉ a) (hy : y ∉ b)
    (hf : f !: insert x a ↔ insert y b) : MemStructure.eraseRedirect f x y !: a ↔ b := by
  have hg := hf.isInjectionFromTo.eraseRedirect hx
  refine ⟨hg, ?_⟩
  rw [isSurjectionFromTo_iff_of_isFunctionFromTo hg.isFunctionFromTo]
  intro w hw
  obtain ⟨z, hz, rfl⟩ := hf.isSurjectionFromTo.exists_mem_val (subset_insert _ _ hw)
  obtain ⟨z', hz', hz'y⟩ := hf.isSurjectionFromTo.exists_mem_val (mem_insert _ _)
  grind [val_eraseRedirect_of_eq, val_eraseRedirect_of_ne]

/-- Functions on `succ n` agreeing on `n` and at `n` are equal -/
theorem IsFunctionFromTo.eq_of_restrict_eq {s s' n b b' : M} (hs : s !: succ n → b)
    (hs' : s' !: succ n → b') (hres : s ↾ n = s' ↾ n) (hval : s ﹫ n = s' ﹫ n) : s = s' := by
  refine hs.isFunction.ext hs'.isFunction (by rw [hs.dom_eq, hs'.dom_eq]) fun k hk ↦ ?_
  rw [hs.dom_eq, mem_succ_iff] at hk
  rcases hk with rfl | hk
  · exact hval
  · rw [← val_restrict s hs.isFunction hk (by rw [hs.dom_eq]; grind), hres,
      val_restrict s' hs'.isFunction hk (by rw [hs'.dom_eq]; grind)]

/-- Extending a function on `n` by `!(n, y)` gives a function on `succ n` -/
theorem IsFunctionFromTo.insert_succ {s n b y : M} (hs : s !: n → b) (hn : n ∉ n) (hy : y ∈ b) :
    insert !(n, y) s !: succ n → b := by
  have hns : n ∉ dom s := by rwa [hs.dom_eq]
  refine isFunctionFromTo_of_val (hs.isFunction.insert hns y) (by rw [dom_insert, hs.dom_eq]; rfl)
    fun k hk ↦ ?_
  rw [mem_succ_iff] at hk
  rcases hk with rfl | hk
  · rwa [val_insert_self hs.isFunction hns]
  · rw [val_insert_of_mem hs.isFunction hns y (by rwa [hs.dom_eq])]
    exact hs.val_mem hk

theorem IsFunctionFromTo.restrict_insert_succ {s n b y : M} (hs : s !: n → b) (hn : n ∉ n) :
    insert !(n, y) s ↾ n = s := by
  have hns : n ∉ dom s := by rwa [hs.dom_eq]
  have hf := hs.isFunction.insert hns y
  refine (hf.restrict n).ext hs.isFunction (by rw [dom_restrict_of_subset hf (by grind),
    hs.dom_eq]) fun k hk ↦ ?_
  rw [dom_restrict_of_subset hf (by grind)] at hk
  rw [val_restrict _ hf hk (by grind), val_insert_of_mem hs.isFunction hns y (by rwa [hs.dom_eq])]

/-- The restriction of a function on `succ n` to `n` is a function on `n` -/
theorem IsFunctionFromTo.restrict_succ {s n b : M} (hs : s !: succ n → b) : s ↾ n !: n → b :=
  hs.restrict (by grind)

/-- The rudimentary term for `moveKey f x y`: `insert !(y, f ﹫ x) (erase f x)` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.moveKey₀
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 3 :=
  insert ᵣ(ᵣ2, (ᵣ0) ﹫ (ᵣ1)) (erase₀.substBoundRud ![ᵣ0, ᵣ1])

/-- The rudimentary term for `moveKey r s t` -/
@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.moveKey
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s t : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  moveKey₀.substBoundRud ![r, s, t]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (moveKey₀ : L.RudimentaryTerm 3).CharFree := by
  unfold moveKey₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] :
    (r.moveKey s t).CharFree := by
  unfold RudimentaryTerm.moveKey; infer_instance

/-- The rudimentary term for `insertVal f x y`: `update f x (f ﹫ x ∪ {y})` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.insertVal₀
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 3 :=
  update₀.substBoundRud ![ᵣ0, ᵣ1, (ᵣ0) ﹫ (ᵣ1) ∪ {ᵣ2}]

/-- The rudimentary term for `insertVal r s t` -/
@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.insertVal
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s t : L.RudimentaryTerm n) : L.RudimentaryTerm n :=
  insertVal₀.substBoundRud ![r, s, t]

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (insertVal₀ : L.RudimentaryTerm 3).CharFree := by
  unfold insertVal₀; infer_instance

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly]
    (r s t : L.RudimentaryTerm n) [r.CharFree] [s.CharFree] [t.CharFree] :
    (r.insertVal s t).CharFree := by
  unfold RudimentaryTerm.insertVal; infer_instance

/-- `f` with the key `x` moved to `y`: `x` is removed from the domain and `y` is sent to
`f ﹫ x` -/
noncomputable def moveKey (f x y : M) : M := moveKey₀〘f, x, y〙₃

instance : MulticlassFunction.DeltaZero (fun ys : Fin 3 → M ↦ moveKey (ys 0) (ys 1) (ys 2))
    Set.univ :=
  MulticlassFunction.deltaZero_of_eq moveKey₀ fun ys ↦ by
    rw [moveKey, show ![ys 0, ys 1, ys 2] = ys by ext i; fin_cases i <;> rfl]

/-- `f` with `y` added to the value at `x` -/
noncomputable def insertVal (f x y : M) : M := insertVal₀〘f, x, y〙₃

instance : MulticlassFunction.DeltaZero (fun ys : Fin 3 → M ↦ insertVal (ys 0) (ys 1) (ys 2))
    Set.univ :=
  MulticlassFunction.deltaZero_of_eq insertVal₀ fun ys ↦ by
    rw [insertVal, show ![ys 0, ys 1, ys 2] = ys by ext i; fin_cases i <;> rfl]

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_moveKey₀ (xs : Fin 3 → M) :
    moveKey₀〘xs〙 = moveKey (xs 0) (xs 1) (xs 2) := by
  simp only [moveKey]
  congr
  ext i; fin_cases i <;> rfl

omit [RudClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_insertVal₀ (xs : Fin 3 → M) :
    insertVal₀〘xs〙 = insertVal (xs 0) (xs 1) (xs 2) := by
  simp only [insertVal]
  congr
  ext i; fin_cases i <;> rfl

omit [RudClosed M] in
theorem moveKey_eq (f x y : M) : moveKey f x y = insert !(y, f ﹫ x) (erase f x) := by
  simp [moveKey, moveKey₀]

omit [RudClosed M] in
theorem insertVal_eq (f x y : M) : insertVal f x y = update f x (f ﹫ x ∪ {y}) := by
  simp [insertVal, insertVal₀]

theorem IsFunction.moveKey {f y : M} (hf : IsFunction f) (x : M) (hy : y ∉ dom f) :
    IsFunction (MemStructure.moveKey f x y) := by
  rw [moveKey_eq]
  exact (hf.erase x).insert (by simp [mem_sdiff_iff, hy]) _

@[simp, grind =]
theorem dom_moveKey (f x y : M) : dom (moveKey f x y) = insert y (dom f \ {x}) := by
  simp [moveKey_eq]

@[simp, grind =]
theorem val_moveKey_self {f y : M} (hf : IsFunction f) (x : M) (hy : y ∉ dom f) :
    moveKey f x y ﹫ y = f ﹫ x := by
  rw [moveKey_eq]
  exact val_insert_self (hf.erase x) (by simp [mem_sdiff_iff, hy]) _

@[simp, grind =]
theorem val_moveKey_of_ne {f x y z : M} (hf : IsFunction f) (hy : y ∉ dom f) (hz : z ∈ dom f)
    (hzx : z ≠ x) : moveKey f x y ﹫ z = f ﹫ z := by
  rw [moveKey_eq, val_insert_of_mem (hf.erase x) (by simp [mem_sdiff_iff, hy]) _
    (by simp [mem_sdiff_iff, hz, hzx]), val_erase hf hz hzx]

/-- Moving a key of the domain keeps the range -/
@[simp, grind =]
theorem ran_moveKey {f x : M} (hf : IsFunction f) (hx : x ∈ dom f) (y : M) :
    ran (moveKey f x y) = ran f := by
  ext w
  simp only [moveKey_eq, ran_insert, mem_insert_iff, mem_ran_iff, rel_erase_iff]
  grind [rel_val hf hx, hf.val_eq_of_rel]

@[simp, grind .]
theorem IsFunction.insertVal {f : M} (hf : IsFunction f) (x y : M) :
    IsFunction (MemStructure.insertVal f x y) := by
  rw [insertVal_eq]
  exact hf.update _ _

@[simp, grind =]
theorem dom_insertVal {f x : M} (hx : x ∈ dom f) (y : M) : dom (insertVal f x y) = dom f := by
  simp [insertVal_eq, insert_eq_self hx]

@[simp, grind =]
theorem val_insertVal_self {f : M} (hf : IsFunction f) (x y : M) :
    insertVal f x y ﹫ x = f ﹫ x ∪ {y} := by
  rw [insertVal_eq]
  exact val_update_self hf _ _

@[simp, grind =]
theorem val_insertVal_of_ne {f x z : M} (hf : IsFunction f) (y : M) (hz : z ∈ dom f)
    (hzx : z ≠ x) : insertVal f x y ﹫ z = f ﹫ z := by
  rw [insertVal_eq]
  exact val_update_of_ne hf _ hz hzx

end Update

end FirstOrder.Language.MemStructure
