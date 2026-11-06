/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Multiclass.Lambda
/-!
# Definable functions: constants, cases and compositions

* `MulticlassFunction.definable_const`: a constant function is definable;
* `MulticlassFunction.definable_ite`, `ClassFunction.definable_ite`: a function defined by cases on
  a definable condition from definable functions is definable;
* `ClassFunction.Definable.comp₁`, …, `comp₄`: a definable function of one to four
  definable class functions is definable. Unlike the `Σ₁` instances, these apply to functions that
  are only definable, so they are not instances; they are applied by hand.
-/

open FirstOrder Language MemStructure

namespace FirstOrder.Language.MemStructure

variable {L : Language} {M : Type*} [L.MemStructure M] {n : ℕ}

/-- A constant function is definable -/
theorem MulticlassFunction.definable_const (a : M) :
    MulticlassFunction.Definable (fun _ : Fin n → M ↦ a) Set.univ := by
  have : Multiclass.DeltaZero
      (MulticlassFunction.toMulticlass (fun _ : Fin n → M ↦ a)) Set.univ := inferInstance
  infer_instance

/-- A function defined by cases on a definable condition from definable functions is definable -/
theorem MulticlassFunction.definable_ite {P : (Fin n → M) → Prop}
    [hP : Multiclass.Definable P Set.univ] [DecidablePred P] {F G : (Fin n → M) → M}
    [hF : MulticlassFunction.Definable F Set.univ] [hG : MulticlassFunction.Definable G Set.univ] :
    MulticlassFunction.Definable (fun xs ↦ if P xs then F xs else G xs) Set.univ := by
  have h : MulticlassFunction.toMulticlass (fun xs ↦ if P xs then F xs else G xs) = fun ys ↦
      (P (ys ∘ Fin.castSucc) ∧ MulticlassFunction.toMulticlass F ys) ∨
        (¬P (ys ∘ Fin.castSucc) ∧ MulticlassFunction.toMulticlass G ys) := by
    funext ys
    by_cases hp : P (ys ∘ Fin.castSucc) <;> simp [MulticlassFunction.toMulticlass, hp]
  have h₁ : Multiclass.Definable (fun ys : Fin (n + 1) → M ↦ P (ys ∘ Fin.castSucc)) Set.univ :=
    ⟨hP.isDefinable.remap _⟩
  have h₂ : Multiclass.Definable (MulticlassFunction.toMulticlass F) Set.univ := inferInstance
  have h₃ : Multiclass.Definable (MulticlassFunction.toMulticlass G) Set.univ := inferInstance
  have : Multiclass.Definable
      (MulticlassFunction.toMulticlass (fun xs ↦ if P xs then F xs else G xs)) Set.univ := by
    rw [h]
    exact ⟨(h₁.isDefinable.inf h₂.isDefinable).sup (h₁.isDefinable.not.inf h₃.isDefinable)⟩
  infer_instance

/-- A class function defined by cases on a definable class from definable class functions is
definable -/
theorem ClassFunction.definable_ite {P : M → Prop} [hP : Class.Definable P Set.univ]
    [DecidablePred P] {F G : ClassFunction M} [hF : F.Definable Set.univ]
    [hG : G.Definable Set.univ] :
    ClassFunction.Definable (fun x ↦ if P x then F x else G x) Set.univ := by
  refine ClassFunction.Definable.of_iff (F := fun xs : Fin 2 → M ↦
    (P (xs 0) ∧ F (xs 0) = xs 1) ∨ (¬P (xs 0) ∧ G (xs 0) = xs 1)) fun u w ↦ ?_
  by_cases hp : P u <;> simp [hp]

/-- The composition of definable class functions is definable -/
theorem ClassFunction.Definable.comp₁ {H F : ClassFunction M} [hH : H.Definable Set.univ]
    [hF : F.Definable Set.univ] : ClassFunction.Definable (fun x ↦ H (F x)) Set.univ := by
  -- `[x, w, u]` with `u = F x` and `w = H u`
  let B : Multiclass M 3 := (F : Multiclass M 2).remap ![0, 2] ⊓ (H : Multiclass M 2).remap ![2, 1]
  refine ClassFunction.Definable.of_iff (F := B.ex) fun u w ↦ ?_
  simp [B, Multiclass.remap, Matrix.comp_vecCons, Matrix.empty_eq,
    ClassFunction.toMulticlass_vec_iff]

/-- A definable binary function of definable class functions is definable -/
theorem ClassFunction.Definable.comp₂ {H : M → M → M}
    [hH : Multiclass.Definable (fun ys : Fin 3 → M ↦ H (ys 0) (ys 1) = ys 2) Set.univ]
    {F G : ClassFunction M} [hF : F.Definable Set.univ] [hG : G.Definable Set.univ] :
    ClassFunction.Definable (fun x ↦ H (F x) (G x)) Set.univ := by
  -- `[x, w, u, v]` with `u = F x`, `v = G x` and `w = H u v`
  let H' : Multiclass M 3 := fun ys ↦ H (ys 0) (ys 1) = ys 2
  have hH' : H'.Definable Set.univ := hH
  let B : Multiclass M 4 := (F : Multiclass M 2).remap ![0, 2] ⊓
    (G : Multiclass M 2).remap ![0, 3] ⊓ H'.remap ![2, 3, 1]
  refine ClassFunction.Definable.of_iff (F := B.ex.ex) fun u w ↦ ?_
  simp [B, H', Multiclass.remap, Matrix.comp_vecCons, Matrix.empty_eq,
    ClassFunction.toMulticlass_vec_iff]

/-- A definable ternary function of definable class functions is definable -/
theorem ClassFunction.Definable.comp₃ {H : M → M → M → M}
    [hH : Multiclass.Definable (fun ys : Fin 4 → M ↦ H (ys 0) (ys 1) (ys 2) = ys 3) Set.univ]
    {F G K : ClassFunction M} [hF : F.Definable Set.univ] [hG : G.Definable Set.univ]
    [hK : K.Definable Set.univ] :
    ClassFunction.Definable (fun x ↦ H (F x) (G x) (K x)) Set.univ := by
  -- `[x, w, u, v, t]` with `u = F x`, `v = G x`, `t = K x` and `w = H u v t`
  let H' : Multiclass M 4 := fun ys ↦ H (ys 0) (ys 1) (ys 2) = ys 3
  have hH' : H'.Definable Set.univ := hH
  let B : Multiclass M 5 := (F : Multiclass M 2).remap ![0, 2] ⊓
    (G : Multiclass M 2).remap ![0, 3] ⊓ (K : Multiclass M 2).remap ![0, 4] ⊓
      H'.remap ![2, 3, 4, 1]
  refine ClassFunction.Definable.of_iff (F := B.ex.ex.ex) fun u w ↦ ?_
  simp [B, H', Multiclass.remap, Matrix.comp_vecCons, Matrix.empty_eq,
    ClassFunction.toMulticlass_vec_iff]

/-- A definable quaternary function of definable class functions is definable -/
theorem ClassFunction.Definable.comp₄ {H : M → M → M → M → M}
    [hH : Multiclass.Definable
      (fun ys : Fin 5 → M ↦ H (ys 0) (ys 1) (ys 2) (ys 3) = ys 4) Set.univ]
    {F G K E : ClassFunction M} [hF : F.Definable Set.univ] [hG : G.Definable Set.univ]
    [hK : K.Definable Set.univ] [hE : E.Definable Set.univ] :
    ClassFunction.Definable (fun x ↦ H (F x) (G x) (K x) (E x)) Set.univ := by
  -- `[x, w, u, v, t, s]` with `u = F x`, `v = G x`, `t = K x`, `s = E x` and `w = H u v t s`
  let H' : Multiclass M 5 := fun ys ↦ H (ys 0) (ys 1) (ys 2) (ys 3) = ys 4
  have hH' : H'.Definable Set.univ := hH
  let B : Multiclass M 6 := (F : Multiclass M 2).remap ![0, 2] ⊓
    (G : Multiclass M 2).remap ![0, 3] ⊓ (K : Multiclass M 2).remap ![0, 4] ⊓
      (E : Multiclass M 2).remap ![0, 5] ⊓ H'.remap ![2, 3, 4, 5, 1]
  refine ClassFunction.Definable.of_iff (F := B.ex.ex.ex.ex) fun u w ↦ ?_
  simp [B, H', Multiclass.remap, Matrix.comp_vecCons, Matrix.empty_eq,
    ClassFunction.toMulticlass_vec_iff]

end FirstOrder.Language.MemStructure
