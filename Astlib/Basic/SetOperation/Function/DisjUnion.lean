/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Function.ProdMap
/-!
# Disjoint unions

Disjoint unions `disjUnion a b`, the swap map `disjUnionSwap a b` and the map
`disjUnionMap f g a b` induced by functions on the summands.
-/

open Fin FirstOrder Language MemStructure RudimentaryTerm DeltaZeroBoundedFormula

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M]

section DisjUnion

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

/-- The disjoint union of `a` and `b`, with `a` tagged by `∅` and `b` tagged by `{∅}` -/
noncomputable def disjUnion (a b : M) : M := ({∅} : M) ×ˢ a ∪ ({{∅}} : M) ×ˢ b

omit [Extensional M] [L.ExtraConstantsUnaryRelationsOnly] in
theorem mem_disjUnion_iff {a b p : M} :
    p ∈ disjUnion a b ↔ (∃ x ∈ a, p = !(∅, x)) ∨ ∃ y ∈ b, p = !({∅}, y) := by
  simp [disjUnion, mem_union_iff, mem_sprod_iff]

@[simp]
theorem empty_pair_mem_disjUnion_iff {a b x : M} : !(∅, x) ∈ disjUnion a b ↔ x ∈ a := by
  simp [mem_disjUnion_iff,
    (singleton_ne_empty (M := M) (x := ∅)).symm]

@[simp]
theorem singleton_pair_mem_disjUnion_iff {a b y : M} : !({∅}, y) ∈ disjUnion a b ↔ y ∈ b := by
  simp [mem_disjUnion_iff, orderedPair_eq_orderedPair_iff, singleton_ne_empty (M := M) (x := ∅)]

/-- `disjUnion a a` is `2 ×ˢ a` -/
theorem disjUnion_self (a : M) : disjUnion a a = succ (succ (∅ : M)) ×ˢ a := by
  ext p
  simp only [mem_disjUnion_iff, mem_sprod_iff, mem_succ_iff, succ_empty, mem_singleton_iff]
  grind

/-- The rudimentary term for `disjUnionSwap a b`:
`{!(!(∅, x), !({∅}, x)) | x ∈ a} ∪ {!(!({∅}, y), !(∅, y)) | y ∈ b}` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.disjUnionSwap₀
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 2 :=
  -- `[a, b]`
  RudimentaryTerm.iUnion (ᵣ0 : L.RudimentaryTerm 2)
      {ᵣ(ᵣ((∅ : L.RudimentaryTerm 3), ᵣ2), ᵣ(({∅} : L.RudimentaryTerm 3), ᵣ2))} ∪
    RudimentaryTerm.iUnion (ᵣ1 : L.RudimentaryTerm 2)
      {ᵣ(ᵣ(({∅} : L.RudimentaryTerm 3), ᵣ2), ᵣ((∅ : L.RudimentaryTerm 3), ᵣ2))}

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (disjUnionSwap₀ : L.RudimentaryTerm 2).CharFree := by
  unfold disjUnionSwap₀; infer_instance

/-- The bijection from `disjUnion a b` onto `disjUnion b a` swapping the tags -/
noncomputable def disjUnionSwap (a b : M) : M := disjUnionSwap₀〘a, b〙₂

instance : MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ disjUnionSwap (ys 0) (ys 1))
    Set.univ :=
  MulticlassFunction.deltaZero_of_eq₂ disjUnionSwap₀ fun _ _ ↦ rfl

theorem mem_disjUnionSwap_iff {a b p : M} :
    p ∈ disjUnionSwap a b ↔
      (∃ x ∈ a, p = !(!(∅, x), !({∅}, x))) ∨ ∃ y ∈ b, p = !(!({∅}, y), !(∅, y)) := by
  simp [disjUnionSwap, disjUnionSwap₀, mem_union_iff]

theorem rel_disjUnionSwap_iff {a b z w : M} :
    z [disjUnionSwap a b] w ↔
      (∃ x ∈ a, z = !(∅, x) ∧ w = !({∅}, x)) ∨ ∃ y ∈ b, z = !({∅}, y) ∧ w = !(∅, y) := by
  simp only [mem_disjUnionSwap_iff, orderedPair_eq_orderedPair_iff]

theorem isFunction_disjUnionSwap (a b : M) : IsFunction (disjUnionSwap a b) := by
  refine ⟨fun p hp ↦ ?_, fun z w₁ w₂ h₁ h₂ ↦ ?_⟩
  · rw [mem_disjUnionSwap_iff] at hp
    rcases hp with ⟨x, -, rfl⟩ | ⟨y, -, rfl⟩ <;> simp [IsOrderedPair]
  · rw [rel_disjUnionSwap_iff] at h₁ h₂
    grind [singleton_ne_empty (M := M) (x := ∅)]

theorem val_disjUnionSwap_empty {a b x : M} (hx : x ∈ a) :
    disjUnionSwap a b ﹫ !(∅, x) = !({∅}, x) := by
  refine (isFunction_disjUnionSwap a b).val_eq_of_rel ?_
  rw [rel_disjUnionSwap_iff]
  exact .inl ⟨x, hx, rfl, rfl⟩

theorem val_disjUnionSwap_singleton {a b y : M} (hy : y ∈ b) :
    disjUnionSwap a b ﹫ !({∅}, y) = !(∅, y) := by
  refine (isFunction_disjUnionSwap a b).val_eq_of_rel ?_
  rw [rel_disjUnionSwap_iff]
  exact .inr ⟨y, hy, rfl, rfl⟩

/-- Swapping the tags is a bijection from `disjUnion a b` onto `disjUnion b a` -/
theorem isBijectionFromTo_disjUnionSwap (a b : M) :
    disjUnionSwap a b !: disjUnion a b ↔ disjUnion b a := by
  have hdom : dom (disjUnionSwap a b) = disjUnion a b := by
    ext z
    simp only [mem_dom_iff, rel_disjUnionSwap_iff, mem_disjUnion_iff]
    grind
  have hinj : disjUnionSwap a b !: disjUnion a b ↪ disjUnion b a := by
    refine isInjectionFromTo_of_val (isFunction_disjUnionSwap a b) hdom (fun z hz ↦ ?_)
      fun z hz z' hz' h ↦ ?_
    · simp only [mem_disjUnion_iff] at hz
      rcases hz with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩ <;>
        simp [val_disjUnionSwap_empty, val_disjUnionSwap_singleton, *]
    · simp only [mem_disjUnion_iff] at hz hz'
      grind [val_disjUnionSwap_empty, val_disjUnionSwap_singleton]
  refine ⟨hinj, ?_⟩
  rw [isSurjectionFromTo_iff_of_isFunctionFromTo hinj.isFunctionFromTo]
  intro w hw
  simp only [mem_disjUnion_iff] at hw
  rcases hw with ⟨y, hy, rfl⟩ | ⟨x, hx, rfl⟩
  · exact ⟨!({∅}, y), by simp [hy], val_disjUnionSwap_singleton hy⟩
  · exact ⟨!(∅, x), by simp [hx], val_disjUnionSwap_empty hx⟩

/-- The rudimentary term for `disjUnionMap f g a b`:
`{!(!(∅, x), f ﹫ x) | x ∈ a} ∪ {!(!({∅}, y), g ﹫ y) | y ∈ b}` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.disjUnionMap₀
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 4 :=
  -- `[f, g, a, b]`
  RudimentaryTerm.iUnion (ᵣ2 : L.RudimentaryTerm 4)
      {ᵣ(ᵣ((∅ : L.RudimentaryTerm 5), ᵣ4), (ᵣ0) ﹫ (ᵣ4))} ∪
    RudimentaryTerm.iUnion (ᵣ3 : L.RudimentaryTerm 4)
      {ᵣ(ᵣ(({∅} : L.RudimentaryTerm 5), ᵣ4), (ᵣ1) ﹫ (ᵣ4))}

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (disjUnionMap₀ : L.RudimentaryTerm 4).CharFree := by
  unfold disjUnionMap₀; infer_instance

/-- The function on `disjUnion a b` gluing `f` on `a` and `g` on `b`:
`!(∅, x) ↦ f ﹫ x` and `!({∅}, y) ↦ g ﹫ y` -/
noncomputable def disjUnionMap (f g a b : M) : M := disjUnionMap₀〘![f, g, a, b]〙

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 4 → M ↦ disjUnionMap (ys 0) (ys 1) (ys 2) (ys 3)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq disjUnionMap₀ fun ys ↦ by
    rw [disjUnionMap, show ![ys 0, ys 1, ys 2, ys 3] = ys by ext i; fin_cases i <;> rfl]

theorem mem_disjUnionMap_iff {f g a b p : M} :
    p ∈ disjUnionMap f g a b ↔
      (∃ x ∈ a, p = !(!(∅, x), f ﹫ x)) ∨ ∃ y ∈ b, p = !(!({∅}, y), g ﹫ y) := by
  simp [disjUnionMap, disjUnionMap₀]

theorem rel_disjUnionMap_iff {f g a b z w : M} :
    z [disjUnionMap f g a b] w ↔
      (∃ x ∈ a, z = !(∅, x) ∧ w = f ﹫ x) ∨ ∃ y ∈ b, z = !({∅}, y) ∧ w = g ﹫ y := by
  simp [mem_disjUnionMap_iff]

theorem isFunction_disjUnionMap (f g a b : M) : IsFunction (disjUnionMap f g a b) := by
  grind [IsFunction, IsRelation, mem_disjUnionMap_iff, rel_disjUnionMap_iff, IsOrderedPair,
    singleton_ne_empty (M := M) (x := ∅)]

theorem dom_disjUnionMap (f g a b : M) : dom (disjUnionMap f g a b) = disjUnion a b := by
  ext z
  simp only [mem_dom_iff, rel_disjUnionMap_iff, mem_disjUnion_iff]
  grind

theorem val_disjUnionMap_empty {f g a b x : M} (hx : x ∈ a) :
    disjUnionMap f g a b ﹫ !(∅, x) = f ﹫ x :=
  (isFunction_disjUnionMap f g a b).val_eq_of_rel (by simp [rel_disjUnionMap_iff, hx])

theorem val_disjUnionMap_singleton {f g a b y : M} (hy : y ∈ b) :
    disjUnionMap f g a b ﹫ !({∅}, y) = g ﹫ y :=
  (isFunction_disjUnionMap f g a b).val_eq_of_rel (by simp [rel_disjUnionMap_iff, hy])

/-- Gluing functions `a → c` and `b → d` gives a function `disjUnion a b → c ∪ d` -/
theorem IsFunctionFromTo.disjUnionMap {f g a b c d : M} (hf : f !: a → c) (hg : g !: b → d) :
    MemStructure.disjUnionMap f g a b !: disjUnion a b → c ∪ d := by
  refine isFunctionFromTo_of_val (isFunction_disjUnionMap f g a b) (dom_disjUnionMap f g a b)
    fun z hz ↦ ?_
  simp only [mem_disjUnion_iff] at hz
  rcases hz with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
  · simp [val_disjUnionMap_empty hx, hf.val_mem hx]
  · simp [val_disjUnionMap_singleton hy, hg.val_mem hy]

/-- Gluing surjections `a ↠ c` and `b ↠ d` gives a surjection `disjUnion a b ↠ c ∪ d` -/
theorem IsSurjectionFromTo.disjUnionMap {f g a b c d : M} (hf : f !: a ↠ c) (hg : g !: b ↠ d) :
    MemStructure.disjUnionMap f g a b !: disjUnion a b ↠ c ∪ d := by
  simp only [isSurjectionFromTo_iff_of_isFunctionFromTo
    (hf.isFunctionFromTo.disjUnionMap hg.isFunctionFromTo), mem_union_iff]
  rintro w (hw | hw)
  · obtain ⟨x, hx, rfl⟩ := hf.exists_mem_val hw
    exact ⟨!(∅, x), by grind [empty_pair_mem_disjUnion_iff, val_disjUnionMap_empty]⟩
  · obtain ⟨y, hy, rfl⟩ := hg.exists_mem_val hw
    exact ⟨!({∅}, y), by grind [singleton_pair_mem_disjUnion_iff, val_disjUnionMap_singleton]⟩

end DisjUnion

end FirstOrder.Language.MemStructure
