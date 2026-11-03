/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Function.FromTo
/-!
# Product maps

`prodMap f g a b`: the function on `a ×ˢ b` sending `!(x, y)` to `!(f ﹫ x, g ﹫ y)`.
-/

open Fin FirstOrder Language MemStructure RudimentaryTerm DeltaZeroBoundedFormula

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*}
  [L.MemStructure M] [Inhabited M]

section ProdMap

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

/-- The rudimentary term for `prodMap f g a b`:
`⋃_{z ∈ a ×ˢ b} {!(z, !(f ﹫ left z, g ﹫ right z))}` -/
noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.prodMap₀
    {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] : L.RudimentaryTerm 4 :=
  -- `[f, g, a, b]`
  RudimentaryTerm.iUnion ((ᵣ2 : L.RudimentaryTerm 4) ×ˢ (ᵣ3 : L.RudimentaryTerm 4))
    {ᵣ((ᵣ4 : L.RudimentaryTerm 5), ᵣ((ᵣ0) ﹫ (ᵣ4).left, (ᵣ1) ﹫ (ᵣ4).right))}

instance {L : Language} [L.HasMem] [L.ExtraConstantsUnaryRelationsOnly] :
    (prodMap₀ : L.RudimentaryTerm 4).CharFree := by
  unfold prodMap₀; infer_instance

/-- The function `!(x, y) ↦ !(f ﹫ x, g ﹫ y)` on `a ×ˢ b` -/
noncomputable def prodMap (f g a b : M) : M := prodMap₀〘![f, g, a, b]〙

instance : MulticlassFunction.DeltaZero
    (fun ys : Fin 4 → M ↦ prodMap (ys 0) (ys 1) (ys 2) (ys 3)) Set.univ :=
  MulticlassFunction.deltaZero_of_eq prodMap₀ fun ys ↦ by
    rw [prodMap, show ![ys 0, ys 1, ys 2, ys 3] = ys by ext i; fin_cases i <;> rfl]

theorem mem_prodMap_iff {f g a b p : M} :
    p ∈ prodMap f g a b ↔ ∃ z ∈ a ×ˢ b, p = !(z, !(f ﹫ left z, g ﹫ right z)) := by
  simp [prodMap, prodMap₀]

@[simp, grind =]
theorem rel_prodMap_iff {f g a b z w : M} :
    z [prodMap f g a b] w ↔ z ∈ a ×ˢ b ∧ w = !(f ﹫ left z, g ﹫ right z) := by
  simp only [mem_prodMap_iff, orderedPair_eq_orderedPair_iff]
  grind

@[simp, grind .]
theorem isFunction_prodMap (f g a b : M) : IsFunction (prodMap f g a b) := by
  refine ⟨fun p hp ↦ ?_, by grind⟩
  simp only [mem_prodMap_iff] at hp
  obtain ⟨z, -, rfl⟩ := hp
  simp [IsOrderedPair]

@[simp, grind =]
theorem dom_prodMap (f g a b : M) : dom (prodMap f g a b) = a ×ˢ b := by
  ext z
  simp [mem_dom_iff]

@[simp, grind =]
theorem prodMap_val {f g a b x y : M} (hx : x ∈ a) (hy : y ∈ b) :
    prodMap f g a b ﹫ !(x, y) = !(f ﹫ x, g ﹫ y) :=
  (isFunction_prodMap f g a b).val_eq_of_rel (by simp [mem_sprod _ _ _ _ hx hy])

/-- Functions `a → a'` and `b → b'` give a function `a ×ˢ b → a' ×ˢ b'` -/
theorem IsFunctionFromTo.prodMap {f g a a' b b' : M} (hf : f !: a → a') (hg : g !: b → b') :
    MemStructure.prodMap f g a b !: a ×ˢ b → a' ×ˢ b' := by
  refine isFunctionFromTo_of_val (isFunction_prodMap f g a b) (dom_prodMap f g a b) fun z hz ↦ ?_
  simp only [mem_sprod_iff] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  rw [prodMap_val hx hy]
  exact mem_sprod _ _ _ _ (hf.val_mem hx) (hg.val_mem hy)

/-- Injections `a ↪ a'` and `b ↪ b'` give an injection `a ×ˢ b ↪ a' ×ˢ b'` -/
theorem IsInjectionFromTo.prodMap {f g a a' b b' : M} (hf : f !: a ↪ a') (hg : g !: b ↪ b') :
    MemStructure.prodMap f g a b !: a ×ˢ b ↪ a' ×ˢ b' := by
  refine ⟨hf.isFunctionFromTo.prodMap hg.isFunctionFromTo,
    fun z z' hz hz' h ↦ ?_⟩
  simp only [mem_sprod_iff] at hz hz'
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  obtain ⟨x', hx', y', hy', rfl⟩ := hz'
  simp only [prodMap_val, hx, hy, hx', hy', orderedPair_eq_orderedPair_iff] at h
  rw [hf.eq hx hx' h.left, hg.eq hy hy' h.right]

/-- Surjections `a ↠ a'` and `b ↠ b'` give a surjection `a ×ˢ b ↠ a' ×ˢ b'` -/
theorem IsSurjectionFromTo.prodMap {f g a a' b b' : M} (hf : f !: a ↠ a') (hg : g !: b ↠ b') :
    MemStructure.prodMap f g a b !: a ×ˢ b ↠ a' ×ˢ b' := by
  rw [isSurjectionFromTo_iff_of_isFunctionFromTo
    (hf.isFunctionFromTo.prodMap hg.isFunctionFromTo)]
  intro w hw
  simp only [mem_sprod_iff] at hw
  obtain ⟨u, hu, v, hv, rfl⟩ := hw
  obtain ⟨x, hx, rfl⟩ := hf.exists_mem_val hu
  obtain ⟨y, hy, rfl⟩ := hg.exists_mem_val hv
  exact ⟨!(x, y), mem_sprod _ _ _ _ hx hy, prodMap_val hx hy⟩

/-- Bijections `a ↔ a'` and `b ↔ b'` give a bijection `a ×ˢ b ↔ a' ×ˢ b'` -/
theorem IsBijectionFromTo.prodMap {f g a a' b b' : M} (hf : f !: a ↔ a') (hg : g !: b ↔ b') :
    MemStructure.prodMap f g a b !: a ×ˢ b ↔ a' ×ˢ b' :=
  ⟨hf.isInjectionFromTo.prodMap hg.isInjectionFromTo,
    hf.isSurjectionFromTo.prodMap hg.isSurjectionFromTo⟩

end ProdMap

end FirstOrder.Language.MemStructure
