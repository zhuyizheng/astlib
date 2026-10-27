/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Rudimentary.Realize
/-!
# `Δ₀` formulas under substitution of rudimentary terms

The realization of `r.hasMem t`, `r.eq t`, `r.mem t`, `r.allMem φ`, `r.exMem φ` and
`φ.substBoundRud rs` in structures closed under rudimentary functions.
-/
open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula RudimentaryTerm Fin MemStructure

variable {L : FirstOrder.Language} {M : Type*} [L.MemStructure M] [Inhabited M]

namespace FirstOrder.Language

namespace RudimentaryTerm

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

mutual
  @[simp]
  theorem realize_hasMem {n : ℕ} (r : L.RudimentaryTerm n) [hr : r.CharFree] (t : L.Term' n)
      (xs : Fin n → M) :
      (r.hasMem t).toBoundedFormula 〘xs〙 ↔ t〘xs〙 ∈ r〘xs〙 :=
    match r, hr with
    | .var i, _ => by simp [hasMem]
    | .const c, _ => by simp [hasMem]
    | .unorderedPair r₁ r₂, hr => by
      have := CharFree.of_unorderedPair_left r₁ r₂
      have := CharFree.of_unorderedPair_right r₁ r₂
      simp [hasMem, r₁.realize_eq, r₂.realize_eq]
    | .sdiff r₁ r₂, hr => by
      have := CharFree.of_sdiff_left r₁ r₂
      have := CharFree.of_sdiff_right r₁ r₂
      simp [hasMem, r₁.realize_hasMem, r₂.realize_hasMem]
    | .iUnion ri rf, hr => by
      have := CharFree.of_iUnion_index ri rf
      have := CharFree.of_iUnion_function ri rf
      simp [hasMem, ri.realize_exMem, rf.realize_hasMem]
    | .char R _, hr => by simp at hr
    termination_by (r.depth, 1, 0)
    decreasing_by all_goals simp [depth, Prod.lex_def]

  @[simp]
  theorem realize_eq {n : ℕ} (r : L.RudimentaryTerm n) [hr : r.CharFree] (t : L.Term' n)
      (xs : Fin n → M) :
      (r.eq t).toBoundedFormula 〘xs〙 ↔ t〘xs〙 = r〘xs〙 :=
    match r, hr with
    | .var i, _ => by simp [eq]
    | .const c, _ => by simp [eq]
    | .unorderedPair r₁ r₂, hr => by
      have := CharFree.of_unorderedPair_left r₁ r₂
      have := CharFree.of_unorderedPair_right r₁ r₂
      simp only [eq, Function.comp_apply, toBoundedFormula_inf, toBoundedFormula,
        toBoundedFormula_sup, realize'_inf, r₁.realize_mem, r₂.realize_mem,
        BoundedFormula.realize_allMem, realize'_sup, r₁.castSucc.realize_eq,
        Term.realize'_var', snoc_last, realize_castSucc, r₂.castSucc.realize_eq,
        realize_unorderedPair]
      rw [MemStructure.ext_iff]
      grind
    | .sdiff r₁ r₂, hr => by
      have := CharFree.of_sdiff_left r₁ r₂
      have := CharFree.of_sdiff_right r₁ r₂
      simp only [eq, Function.comp_apply, Term.castSucc, Term.castAdd, Term.castLE,
        castLE_succ_castSucc, toBoundedFormula_inf, toBoundedFormula, toBoundedFormula_not,
        realize'_inf, BoundedFormula.realize_allMem, r₁.castSucc.realize_hasMem, realize_castSucc, Term.realize'_var', snoc_last, realize'_not,
        r₂.castSucc.realize_hasMem, r₁.realize_allMem, toBoundedFormula_sup,
        realize'_sup, realize'_mem, Term.realize'_substBoundBound, snoc_comp_castSucc,
        realize_sdiff']
      rw [MemStructure.ext_iff]
      grind
    | .iUnion ri rf, hr => by
      have := CharFree.of_iUnion_index ri rf
      have := CharFree.of_iUnion_function ri rf
      simp only [eq, Function.comp_apply, Term.castAdd, Term.castLE, toBoundedFormula_inf,
        toBoundedFormula, realize'_inf, BoundedFormula.realize_allMem, ri.castSucc.realize_exMem, realize_castSucc,
        (rf.substBoundBound (snoc (Fin.castAdd 2) (last (n + 1)))).realize_hasMem,
        realize_substBoundBound, snoc_snoc_comp_snoc_castAdd_two_last, Term.realize'_var',
        snoc_snoc_castAdd_one_last, ri.realize_allMem, rf.realize_allMem, realize'_mem, Term.realize'_substBoundBound,
        le_add_iff_nonneg_right, _root_.zero_le, snoc_comp_castLE, castLE_succ_castSucc,
        snoc_comp_castSucc, snoc_last]
      simp only [MemStructure.ext_iff, mem_realize_iUnion_iff]
      grind
    | .char R _, hr => by simp at hr
    termination_by (r.depth, 1, 0)
    decreasing_by all_goals simp [depth, castSucc, castAdd, castLE, Prod.lex_def]

  @[simp]
  theorem realize_mem {n : ℕ} (r : L.RudimentaryTerm n) [hr : r.CharFree] (t : L.Term' n)
      (xs : Fin n → M) :
      (r.mem t).toBoundedFormula 〘xs〙 ↔ r〘xs〙 ∈ t〘xs〙 := by
    simp [mem, r.castSucc.realize_eq]
    termination_by (r.depth, 2, 0)
    decreasing_by simp [castSucc, castAdd, castLE, Prod.lex_def]

  @[simp]
  theorem realize_memSelf {n : ℕ} (r : L.RudimentaryTerm n) [hr : r.CharFree]
      (xs : Fin n → M) :
      (r.memSelf).toBoundedFormula 〘xs〙 ↔ r〘xs〙 ∈ r〘xs〙 := by
    simp [memSelf, r.realize_exMem, r.castSucc.realize_eq]
    termination_by (r.depth, 3, 0)
    decreasing_by all_goals simp [castSucc, castAdd, castLE, Prod.lex_def]

  @[simp]
  theorem realize_allMem {n : ℕ} (r : L.RudimentaryTerm n) [hr : r.CharFree]
      (φ : L.DeltaZeroBoundedFormula (n + 1)) [hφ : φ.RelFree] (xs : Fin n → M) :
      (r.allMem φ).toBoundedFormula 〘xs〙 ↔
        ∀ y ∈ r〘xs〙, φ.toBoundedFormula 〘snoc xs y〙:=
    match r, hr with
    | .var i, _ => by simp [allMem]
    | .const c, _ => by simp [allMem]
    | .unorderedPair r₁ r₂, hr => by
      have := CharFree.of_unorderedPair_left r₁ r₂
      have := CharFree.of_unorderedPair_right r₁ r₂
      simp [allMem, r₁.realize_substLowerAt (k := Fin.last n),
        r₂.realize_substLowerAt (k := Fin.last n)]
    | .sdiff r₁ r₂, hr => by
      have := CharFree.of_sdiff_left r₁ r₂
      have := CharFree.of_sdiff_right r₁ r₂
      simp only [allMem, Function.comp_apply, r₁.realize_allMem, toBoundedFormula_sup, realize'_sup,
        r₂.castSucc.realize_hasMem, realize_castSucc, Term.realize'_var', snoc_last, realize_sdiff',
        mem_sdiff_iff, and_imp]
      grind
    | .iUnion ri rf, hr => by
      have := CharFree.of_iUnion_index ri rf
      have := CharFree.of_iUnion_function ri rf
      simp only [allMem, ri.realize_allMem,
        rf.realize_allMem, coe_substBoundBound, realize'_substBoundBound,
        snoc_snoc_comp_snoc_castAdd_two_last, mem_realize_iUnion_iff, forall_exists_index, and_imp]
      grind
    | .char R _, hr => by simp at hr
    termination_by (r.depth, 1, 0)
    decreasing_by all_goals simp [castSucc, castAdd, castLE, depth, Prod.lex_def]

  @[simp]
  theorem realize_exMem {n : ℕ} (r : L.RudimentaryTerm n) [hr : r.CharFree]
      (φ : L.DeltaZeroBoundedFormula (n + 1)) [hφ : φ.RelFree] (xs : Fin n → M) :
      (r.exMem φ).toBoundedFormula 〘xs〙 ↔
        ∃ y ∈ r〘xs〙, φ.toBoundedFormula 〘snoc xs y〙:= by
    simp [exMem, r.realize_allMem]
    termination_by (r.depth, 2, 0)
    decreasing_by all_goals simp [Prod.lex_def]

  @[simp]
  theorem realize_substLowerAt {n : ℕ} {k : Fin (n + 1)}
      (r : L.RudimentaryTerm k.val) [hr : r.CharFree]
      (φ : L.DeltaZeroBoundedFormula (n + 1)) [hφ : φ.RelFree] (xs : Fin n → M) :
      (r.substLowerAt φ).toBoundedFormula 〘xs〙 ↔
        φ.toBoundedFormula 〘Fin.insertNth k (r 〘xs ∘ (Fin.castLE (is_le k))〙) xs〙 :=
  match φ, hφ with
  | .falsum, _ => by simp [substLowerAt]
  | .equal t₁ t₂, _ => by
    simp only [substLowerAt, Function.comp_apply, toBoundedFormula, realize'_bdEqual]
    split_ifs with h₁₂ h₁ h₂
    · simp [h₁₂]
    · rw [h₁] at h₁₂
      simp [h₁, Ne.symm h₁₂, (r.castLE (is_le k)).realize_eq]
      tauto
    · rw [h₂] at h₁₂
      simp [h₂, h₁₂, (r.castLE (is_le k)).realize_eq]
    · simp [h₁, h₂]
  | .mem t₁ t₂, _ => by
    simp only [substLowerAt, Function.comp_apply, toBoundedFormula, realize'_mem]
    split_ifs with h₁ h₁₂ h₂
    · simp [(r.castLE (is_le k)).realize_memSelf, h₁, h₁₂]
    · rw [h₁] at h₁₂
      simp [h₁, h₁₂, (r.castLE (is_le k)).realize_mem]
    · simp [h₁, h₂, (r.castLE (is_le k)).realize_hasMem]
    · simp [h₁, h₂]
  | .imp φ₁ φ₂, hφ => by
    have := DeltaZeroBoundedFormula.RelFree.of_imp_left φ₁ φ₂
    have := DeltaZeroBoundedFormula.RelFree.of_imp_right φ₁ φ₂
    simp [substLowerAt, r.realize_substLowerAt φ₁, r.realize_substLowerAt φ₂]
  | .allMem t ψ, hφ => by
    simp only [substLowerAt, Function.comp_apply, ne_eq, dite_not, toBoundedFormula,
      BoundedFormula.realize_allMem]
    have := DeltaZeroBoundedFormula.RelFree.of_allMem t ψ
    split_ifs with h
    · simp [(r.castLE (is_le k)).realize_allMem, r.realize_substLowerAt (k := k.castSucc) ψ,
        h, is_le k]
    · simp [r.realize_substLowerAt (k := k.castSucc) ψ, h, is_le k]
  | .rel R _, hφ => by simp at hφ
    termination_by (r.depth, 4, sizeOf φ)
    decreasing_by all_goals simp [castLE, Prod.lex_def, Nat.lt_add_right]
end

end RudimentaryTerm


namespace Term

variable [L.ExtraConstantsUnaryRelationsOnly]

@[simp, grind =]
theorem realize_substBoundRud {m : ℕ} (t : L.Term' n)
    (rs : Fin n → L.RudimentaryTerm m) (xs : Fin m → M) :
    (t.substBoundRud rs)〘xs〙 = t〘fun i ↦ (rs i)〘xs〙〙 :=
  match t with
  | .var (Sum.inr i) => by simp [substBoundRud]
  | .func F _ (l := 0) => by simp [substBoundRud, funMap_eq_coe_constants]
  | .func F _ (l := n + 1) => IsEmpty.elim (by infer_instance) F

end Term

namespace DeltaZeroBoundedFormula

variable {n m : ℕ} [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [RudClosed M]

@[simp]
theorem realize_substBoundRud (φ : L.DeltaZeroBoundedFormula n)
    [hφ : φ.RelFree]
    (rs : Fin n → L.RudimentaryTerm m)
    [hrs : ∀ i, (rs i).CharFree]
    (xs : Fin m → M) :
    (φ.substBoundRud rs).toBoundedFormula 〘xs〙 ↔
      φ.toBoundedFormula 〘fun i ↦ (rs i)〘xs〙〙:= by
  induction hφ using relFreeCases generalizing m with
  | falsum => simp [substBoundRud]
  | equal t₁ t₂ =>
    simp only [substBoundRud, Function.comp_apply, toBoundedFormula_inf, realize'_inf,
      RudimentaryTerm.realize_allMem, Term.realize_substBoundRud, realize_hasMem, realize_castSucc,
      Term.realize'_var', snoc_last, toBoundedFormula, realize'_bdEqual]
    rw [MemStructure.ext_iff]
    grind
  | mem t₁ t₂ =>
    simp [substBoundRud, realize'_mem]
  | imp φ₁ φ₂ _ _ _ ih₁ ih₂ =>
    simp [substBoundRud, ih₁, ih₂]
  | allMem t ψ _ _ ih =>
    simp only [substBoundRud, RudimentaryTerm.realize_allMem, Term.realize_substBoundRud, ih, toBoundedFormula, BoundedFormula.realize_allMem]
    rw [forall_congr]
    intro y
    congr
    funext i; cases i using Fin.lastCases <;> simp

/-- Dropping the third to last variable: `φ` substituted into the context `(xs, b, y, w)` is `φ`
at `(xs, y, w)` -/
theorem realize_substBoundRud_snoc_snoc (φ : L.DeltaZeroBoundedFormula (n + 2))
    [φ.RelFree] (xs : Fin n → M) (b y w : M) :
    (φ.substBoundRud (snoc (snoc (fun i ↦ .var (i.castAdd 3)) ᵣ-2)
      ᵣ-1)).toBoundedFormula〘snoc (snoc (snoc xs b) y) w〙 ↔
    φ.toBoundedFormula〘snoc (snoc xs y) w〙 := by
  rw [realize_substBoundRud]
  apply iff_of_eq
  congr 1
  funext i
  revert i
  simp only [Fin.forall_iff_castSucc]
  simp only [snoc_last, RudimentaryTerm.realize_basic, snoc_castSucc,
    snoc_snoc_castAdd_one_last, snoc_castAdd, true_and]
  exact fun i ↦ snoc_castSucc (α := fun _ ↦ M) b xs i

theorem multiclass_substBoundRud_eq_subst (φ : L.DeltaZeroBoundedFormula n)
    [φ.RelFree]
    (rs : Fin n → L.RudimentaryTerm m)
    [∀ i, (rs i).CharFree] :
    (φ.substBoundRud rs).toBoundedFormula.multiclass =
      φ.toBoundedFormula.multiclass.subst (fun i xs ↦ ((rs i)〘xs〙 : M)) := by
  funext ys
  simp [Multiclass.subst]

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.toDeltaZeroBoundedFormula
  (r : L.RudimentaryTerm n) :
  L.DeltaZeroBoundedFormula (n + 1) :=
  (&0 =₀ &1).substBoundRud ![r.castSucc, ᵣ-1]

theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_eq_toDeltaZeroBoundedFormula
    (r : L.RudimentaryTerm m) [r.CharFree] :
    (r.realize : Multiclass M (m + 1)) = r.toDeltaZeroBoundedFormula.toBoundedFormula.multiclass := by
  simp only [toDeltaZeroBoundedFormula, Nat.succ_eq_add_one, Nat.reduceAdd, isValue,
    Function.comp_apply, multiclass_substBoundRud_eq_subst, toBoundedFormula]
  funext xs
  rw [← Fin.snoc_init_self xs, MulticlassFunction.toMulticlass_snoc_iff]
  simp [Multiclass.subst, RudimentaryTerm.castSucc, RudimentaryTerm.castAdd, init_def]

end DeltaZeroBoundedFormula

namespace MemStructure

/-- The realization of a rudimentary term is a `Δ₀` multiclass function -/
instance [L.ExtraConstantsUnaryRelationsOnly] [Extensional M] [RudClosed M] {m : ℕ}
    (r : L.RudimentaryTerm m) [r.CharFree] :
    MulticlassFunction.DeltaZero (r.realize : MulticlassFunction M m) Set.univ := by
  have : ((r.realize : MulticlassFunction M m) : Multiclass M (m + 1)).DeltaZero Set.univ := by
    rw [r.realize_eq_toDeltaZeroBoundedFormula]
    infer_instance
  infer_instance

/-- A class function given by a rudimentary term is `Δ₀` -/
theorem ClassFunction.deltaZero_of_eq [L.ExtraConstantsUnaryRelationsOnly] [Extensional M]
    [RudClosed M] {F : ClassFunction M} (r : L.RudimentaryTerm 1) [r.CharFree]
    (h : ∀ x, F x = r〘![x]〙) : F.DeltaZero Set.univ := by
  have e : (fun xs : Fin 1 → M ↦ F (xs 0)) = (r.realize : MulticlassFunction M 1) := by
    funext xs
    rw [h, show ![xs 0] = xs by ext i; fin_cases i; rfl]
  have : MulticlassFunction.DeltaZero (fun xs : Fin 1 → M ↦ F (xs 0)) Set.univ :=
    e ▸ inferInstance
  infer_instance

/-- A term given by a rudimentary term is `Δ₀` -/
theorem MulticlassFunction.deltaZero_of_eq [L.ExtraConstantsUnaryRelationsOnly] [Extensional M]
    [RudClosed M] {n : ℕ} {F : (Fin n → M) → M} (r : L.RudimentaryTerm n) [r.CharFree]
    (h : ∀ xs, F xs = r〘xs〙) : MulticlassFunction.DeltaZero F Set.univ := by
  have e : F = (r.realize : MulticlassFunction M n) := funext h
  rw [e]
  infer_instance

/-- A binary operation given by a rudimentary term is a `Δ₀` term -/
theorem MulticlassFunction.deltaZero_of_eq₂ [L.ExtraConstantsUnaryRelationsOnly] [Extensional M]
    [RudClosed M] {G : M → M → M} (r : L.RudimentaryTerm 2) [r.CharFree]
    (h : ∀ x y, G x y = r〘![x, y]〙) :
    MulticlassFunction.DeltaZero (fun ys : Fin 2 → M ↦ G (ys 0) (ys 1)) Set.univ := by
  have e : (fun ys : Fin 2 → M ↦ G (ys 0) (ys 1)) = (r.realize : MulticlassFunction M 2) := by
    funext ys
    rw [h, Matrix.vec_fin_two_eq ys]
  rw [e]
  infer_instance

-- namespace Multiclass

-- variable {n m : ℕ} {M : MemStructure} [M.RudClosed] [M.Extensional]
--   (P : Set M)

-- theorem isDeltaZero_subst_rudimentaryTerm {A : M.Multiclass n} [hA : A.DeltaZero P]
--     (rs : Fin n → L.RudimentaryTerm m) :
--     (A.subst fun i xs ↦ (rs i).castLHom〘xs〙).IsDeltaZero P := by
--   obtain ⟨l, _, ⟨⟨φ, rfl⟩⟩, ys, hys, rfl⟩ := hA
--   refine ⟨l,
--     (φ.substBoundRud (append (fun i ↦ (rs i).castAdd l) (fun i ↦ ᵣ(i.natAdd m)))).toBoundedFormula,
--     by infer_instance, ys, hys, ?_⟩
--   simp only [subst_slice_eq_slice_subst, multiclass_substBoundRud_eq_subst]
--   congr
--   funext i; cases i using Fin.addCases
--   · simp only [append_left, RudimentaryTerm.castAdd, realize_castLE]
--     rfl
--   · simp

-- -- theorem isDeltaZero_rudimentaryTerm
-- --     (r : L.RudimentaryTerm m) :
-- --     (r.realize : M.Multiclass (m + 1)).IsDeltaZero P := by
-- --   convert isDeltaZero_subst_rudimentaryTerm
-- --    
-- --   funext ys
-- --   rw [← Fin.snoc_init_self ys, MulticlassFunction.toMulticlass_snoc_iff]
-- --   simp [subst, RudimentaryTerm.castSucc, RudimentaryTerm.castAdd, init_def]

-- instance {A : M.Multiclass n} [A.DeltaZero P] (rs : Fin n → L.RudimentaryTerm m) :
--   (A.subst fun i xs ↦ (rs i).castLHom〘xs〙).DeltaZero P :=
--   ⟨isDeltaZero_subst_rudimentaryTerm _ _⟩

-- instance (r : L.RudimentaryTerm m) :
--   (r.castLHom.realize : M.Multiclass (m + 1)).DeltaZero P := by
--   rw [RudimentaryTerm.realize_eq_toDeltaZeroBoundedFormula]
--   infer_instance

-- end Multiclass

end MemStructure



end FirstOrder.Language
