/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.MemStructure.Semantics
import Astlib.Basic.SetOperation.Rudimentary.Syntax
import Astlib.Basic.SetOperation.Multiclass.Levy
import Astlib.Basic.SetOperation.Extensional
/-!
file docstring
-/
open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula RudimentaryTerm Fin MemStructure

variable {L : FirstOrder.Language.{u, v}} {M : Type max u v} [L.MemStructure M] [Inhabited M]

namespace FirstOrder.Language

namespace MemStructure

def IsUnorderedPair (a x y : M) := ∀ z : M, z ∈ a ↔ z = x ∨ z = y

noncomputable instance : Decidable (∃ a : M, IsUnorderedPair a x y) :=
  Classical.propDecidable _

noncomputable def unorderedPair (x y : M) :=
  dite (∃ a : M, IsUnorderedPair a x y) Classical.choose default

@[inherit_doc] scoped[FirstOrder] notation:max "!{" x ", " y "}" =>
  FirstOrder.Language.MemStructure.unorderedPair x y

def IsSDiff (a x y : M) := ∀ z, z ∈ a ↔ z ∈ x ∧ z ∉ y

noncomputable instance : Decidable (∃ a : M, IsSDiff a x y) :=
  Classical.propDecidable _

noncomputable def sdiff (x y : M) :=
  dite (∃ a : M, IsSDiff a x y) Classical.choose default

noncomputable instance : SDiff M := ⟨sdiff⟩

instance {L : FirstOrder.Language.{u, v}} [L.HasMem] : SDiff (L.RudimentaryTerm n) :=
  ⟨RudimentaryTerm.sdiff⟩

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryTerm.isCharFree_sdiff' {L : Language} [L.HasMem]
    (r₁ r₂ : L.RudimentaryTerm n) :
    (r₁ \ r₂).IsCharFree ↔ r₁.IsCharFree ∧ r₂.IsCharFree := by
  simp [SDiff.sdiff]

def IsIUnion (a x : M) (A : ClassFunction M) := ∀ z, z ∈ a ↔ ∃ y ∈ x, z ∈ A y

noncomputable instance : Decidable (∃ a : M, IsIUnion a x A) :=
  Classical.propDecidable _

noncomputable def iUnion (x : M) (A : ClassFunction M) :=
  dite (∃ a : M, IsIUnion a x A) Classical.choose default

noncomputable instance (R : L.Relations n) (xs : Fin n → M) :
  Decidable (Structure.RelMap R xs) := Classical.propDecidable _

noncomputable instance : EmptyCollection M := ⟨default \ default⟩

end MemStructure

namespace RudimentaryTerm

open MemStructure

-- variable {L : FirstOrder.Language.{u, v}} [L.HasMem]

instance {L : FirstOrder.Language} [L.HasMem] : Singleton (L.RudimentaryTerm n) (L.RudimentaryTerm n) :=
  ⟨fun r ↦ ᵣ{r, r}⟩

@[simp]
theorem isCharFree_singleton {L : Language} [L.HasMem]
    (r : L.RudimentaryTerm n) :
    ({r} : L.RudimentaryTerm n).IsCharFree ↔ r.IsCharFree := by
  simp [Singleton.singleton]

noncomputable def realize {n : ℕ} (r : L.RudimentaryTerm n) : MulticlassFunction M n :=
  match r with
  | var i => fun xs ↦ xs i
  | const c => fun _ ↦ L.constantMap c
  | unorderedPair r₁ r₂ => fun xs ↦ MemStructure.unorderedPair (r₁.realize xs) (r₂.realize xs)
  | sdiff r₁ r₂ => fun xs ↦ MemStructure.sdiff (r₁.realize xs) (r₂.realize xs)
  | iUnion ri rf => fun xs ↦ MemStructure.iUnion (ri.realize xs) (fun y ↦ rf.realize (snoc xs y))
  | char R r => fun xs ↦ if Structure.RelMap R ![r.realize xs] then MemStructure.unorderedPair ∅ ∅ else ∅

scoped[FirstOrder.Language] notation:max
  r "〘" xs "〙" => RudimentaryTerm.realize r xs

scoped[FirstOrder.Language] notation:max
  r "〘" x "〙₁" => RudimentaryTerm.realize r ![x]

scoped[FirstOrder.Language] notation:max
  r "〘" x ", " y "〙₂" => RudimentaryTerm.realize r ![x, y]

scoped[FirstOrder.Language] notation:max
  r "〘" x ", " y ", " z "〙₃" => RudimentaryTerm.realize r ![x, y, z]

-- @[simp]
-- noncomputable def realize' (r : L.RudimentaryTerm n) : MulticlassFunction M n :=
--   r.castLHom.realize

-- scoped[FirstOrder.Language] notation:max
--   r "〘" xs "〙'" => RudimentaryTerm.realize' r xs

-- scoped[FirstOrder.Language] notation:max
--   r "〘" x "〙'₁" => RudimentaryTerm.realize' r ![x]

-- scoped[FirstOrder.Language] notation:max
--   r "〘" x ", " y "〙'₂" => RudimentaryTerm.realize' r ![x, y]

-- scoped[FirstOrder.Language] notation:max
--   r "〘" x ", " y ", " z "〙'₃" => RudimentaryTerm.realize' r ![x, y, z]

variable {n : ℕ} (r₁ r₂ r ri : L.RudimentaryTerm n) (rf : L.RudimentaryTerm (n + 1))
  (xs : Fin n → M)

@[simp, grind =]
theorem realize_basic (i : Fin n) : (ᵣi)〘xs〙 = xs i := by
  simp [realize]

@[simp, grind =]
theorem realize_const (c : L.Functions 0) :
    (const c)〘xs〙 = L.constantMap c := by
  simp [realize]

@[simp, grind =]
theorem realize_unorderedPair : ᵣ{r₁, r₂}〘xs〙 = MemStructure.unorderedPair (M := M) r₁〘xs〙 r₂〘xs〙 := by
  simp [realize]

@[simp, grind =]
theorem realize_sdiff' : (r₁.sdiff r₂)〘xs〙 = r₁〘xs〙 \ r₂〘xs〙 := by
  simp [realize, SDiff.sdiff]

@[simp, grind =]
theorem realize_sdiff : (r₁ \ r₂)〘xs〙 = r₁〘xs〙 \ r₂〘xs〙 := realize_sdiff' _ _ _

-- @[simp, grind =]
theorem realize_iUnion :
    (ri.iUnion rf)〘xs〙 = MemStructure.iUnion (M := M) ri〘xs〙 fun y ↦ rf〘snoc xs y〙 := by
  simp [realize]

@[simp, grind =]
theorem realize_char :
    (char R r)〘xs〙 = if Structure.RelMap R ![r.realize xs] then MemStructure.unorderedPair (M := M) ∅ ∅ else ∅ := by
  simp [realize]

@[simp, grind =]
theorem realize_substBoundBound {m : ℕ} (f : Fin n → Fin m) (xs : Fin m → M) :
    (r.substBoundBound f)〘xs〙 = r〘xs ∘ f〙 := by
  induction r generalizing m with
  | var i => simp [substBoundBound]
  | const c => simp [substBoundBound]
  | unorderedPair r₁ r₂ ih₁ ih₂ => simp [substBoundBound, ih₁, ih₂]
  | sdiff r₁ r₂ ih₁ ih₂ => simp [substBoundBound, ih₁, ih₂]
  | iUnion ri rf ihi ihf => simp [substBoundBound, ihi, ihf, realize_iUnion]
  | char R r ih => simp [substBoundBound, ih]

@[simp, grind =]
theorem realize_substBoundRud {m : ℕ}
    (rs : Fin n → L.RudimentaryTerm m) (xs : Fin m → M) :
    (r.substBoundRud rs)〘xs〙 = r〘fun i ↦ (rs i)〘xs〙〙 := by
  induction r generalizing m with
  | var i => simp [substBoundRud]
  | const c => simp [substBoundRud]
  | unorderedPair r₁ r₂ ih₁ ih₂ => simp [substBoundRud, ih₁, ih₂]
  | sdiff r₁ r₂ ih₁ ih₂ => simp [substBoundRud, ih₁, ih₂]
  | iUnion ri rf ihi ihf =>
    simp only [substBoundRud, realize_iUnion, ihi, ihf]
    congr
    funext y
    congr
    ext i; cases i using Fin.lastCases <;> simp
  | char R r ih => simp [substBoundRud, ih]

@[simp, grind =]
theorem realize_castLE {n' : ℕ} (h : n ≤ n') (xs : Fin n' → M) :
    (r.castLE h)〘xs〙 = r〘xs ∘ Fin.castLE h〙 := by
  simp [castLE]

@[simp]
theorem realize_castSucc (xs : Fin n → M) :
    (r.castSucc)〘snoc xs x〙 = r〘xs〙 := by
  simp [castSucc, castAdd]

@[simp]
theorem realize_insertNth_eq_lowerAt [L.ExtraConstantsUnaryRelationsOnly] {t : L.Term' (n + 1)} {k : Fin (n + 1)} (h : t ≠ &k)
    (xs : Fin n → M) (y : M) :
    t〘k.insertNth y xs〙 = (t.lowerAt h)〘xs〙 :=
  match t with
  | .var (Sum.inr i) => by
    simp [Term.lowerAt, Fin.lowerAt]
    have hik : i ≠ k := Ne.intro fun a ↦ h (congrArg Language.var (congrArg Sum.inr a))
    by_cases hik₁ : i < k <;> simp [hik, hik₁, Fin.insertNth, Fin.succAboveCases]
  | .func F _ (l := 0) => by
    simp only [Term.realize'_func, Term.lowerAt]
    congr
    ext i; fin_cases i
  | .func F _ (l := n + 1) => IsEmpty.elim' (by infer_instance) F

@[simp]
theorem _root_.FirstOrder.Language.Term.realize_toRudimentaryTerm {n}
    [L.ExtraConstantsUnaryRelationsOnly] (t : L.Term' n)
    (xs : Fin n → M) :
    (t.toRudimentaryTerm)〘xs〙 = t〘xs〙 :=
  match t with
  | .var (Sum.inr i) => by simp [Term.toRudimentaryTerm]
  | .func F _ (l := 0) => by
    simp only [Term.toRudimentaryTerm, realize_const, constantMap, Term.realize'_func]
    congr
    ext i; fin_cases i
  | .func F _ (l := n + 1) => IsEmpty.elim (by infer_instance) F

end RudimentaryTerm

namespace MemStructure

variable (M) in
class PairClosed : Prop where
  pairClosed : ∀ x y, ∃ a : M, IsUnorderedPair a x y

variable (M) in
class SDiffClosed : Prop where
  sdiffClosed : ∀ x y, ∃ a : M, IsSDiff a x y


variable (M) in
class RudClosed : Prop extends PairClosed M, SDiffClosed M where
  iUnionClosed : ∀ {n} (ri : L.RudimentaryTerm n) (rf : L.RudimentaryTerm (n + 1))
    (xs : Fin n → M), ∃ a, IsIUnion (M := M) a ri〘xs〙 fun y ↦ rf〘snoc xs y〙

variable {n : ℕ} (x y z a : M)

variable [PairClosed M] [SDiffClosed M]

@[simp, grind =]
theorem mem_unorderedPair_iff : x ∈ unorderedPair y z ↔ x = y ∨ x = z := by
  simp only [unorderedPair, PairClosed.pairClosed, ↓reduceDIte]
  rw [Classical.choose_spec (PairClosed.pairClosed y z)]

@[simp, grind =]
theorem mem_sdiff_iff : x ∈ y \ z ↔ x ∈ y ∧ x ∉ z := by
  simp only [SDiff.sdiff, sdiff, SDiffClosed.sdiffClosed, ↓reduceDIte]
  rw [Classical.choose_spec (SDiffClosed.sdiffClosed y z)]

-- @[simp]
theorem mem_realize_iUnion_iff₀
    {n : ℕ} (ri : L.RudimentaryTerm n) (rf : L.RudimentaryTerm (n + 1))
    (xs : Fin n → M) (x : M)
    (h : ∃ a, IsIUnion (M := M) a ri〘xs〙 fun y ↦ rf〘snoc xs y〙) :
    x ∈ (ri.iUnion rf)〘xs〙 ↔
      ∃ z ∈ ri〘xs〙, x ∈ rf〘snoc xs z〙 := by
  simp only [iUnion, h, ↓reduceDIte, realize_iUnion]
  rw [Classical.choose_spec h]

@[simp]
theorem mem_realize_iUnion_iff [RudClosed M]
    {n : ℕ} (ri : L.RudimentaryTerm n) (rf : L.RudimentaryTerm (n + 1))
    (xs : Fin n → M) (x : M) :
    x ∈ (ri.iUnion rf)〘xs〙 ↔
      ∃ z ∈ ri〘xs〙, x ∈ rf〘snoc xs z〙 := by
  rw [mem_realize_iUnion_iff₀]
  exact RudClosed.iUnionClosed _ _ _

end MemStructure

namespace RudimentaryTerm

variable [Extensional M] [RudClosed M] [L.ExtraConstantsUnaryRelationsOnly]

mutual
  @[simp]
  theorem realize_hasMem {n : ℕ} (r : L.RudimentaryTerm n) (hr : r.IsCharFree) (t : L.Term' n)
      (xs : Fin n → M) :
      (r.hasMem t).toBoundedFormula 〘xs〙 ↔ t〘xs〙 ∈ r〘xs〙 :=
    match r with
    | .var i => by simp [hasMem]
    | .const c => by simp [hasMem]
    | .unorderedPair r₁ r₂ => by
      simp only [isCharFree_unorderedPair] at hr
      simp [hasMem, hr, r₁.realize_eq, r₂.realize_eq]
    | .sdiff r₁ r₂ => by
      simp only [isCharFree_sdiff] at hr
      simp [hasMem, hr, r₁.realize_hasMem, r₂.realize_hasMem]
    | .iUnion ri rf => by
      simp only [isCharFree_iUnion] at hr
      simp [hasMem, hr, ri.realize_exMem, rf.realize_hasMem]
    | .char R _ => by simp at hr
    termination_by (r.depth, 1, 0)
    decreasing_by all_goals simp [depth, Prod.lex_def]

  @[simp]
  theorem realize_eq {n : ℕ} (r : L.RudimentaryTerm n) (hr : r.IsCharFree) (t : L.Term' n)
      (xs : Fin n → M) :
      (r.eq t).toBoundedFormula 〘xs〙 ↔ t〘xs〙 = r〘xs〙 :=
    match r with
    | .var i => by simp [eq]
    | .const c => by simp [eq]
    | .unorderedPair r₁ r₂ => by
      simp only [isCharFree_unorderedPair] at hr
      simp only [eq, Function.comp_apply, toBoundedFormula_inf, toBoundedFormula,
        toBoundedFormula_sup, realize'_inf, hr, r₁.realize_mem, r₂.realize_mem,
        BoundedFormula.realize_allMem, realize'_sup, isCharFree_castSucc, r₁.castSucc.realize_eq,
        Term.realize'_var', snoc_last, realize_castSucc, r₂.castSucc.realize_eq,
        realize_unorderedPair]
      rw [MemStructure.ext_iff]
      grind
    | .sdiff r₁ r₂ => by
      simp only [isCharFree_sdiff] at hr
      simp only [eq, Function.comp_apply, Term.castSucc, Term.castAdd, Term.castLE,
        castLE_succ_castSucc, toBoundedFormula_inf, toBoundedFormula, toBoundedFormula_not,
        realize'_inf, BoundedFormula.realize_allMem, isCharFree_castSucc, hr,
        r₁.castSucc.realize_hasMem, realize_castSucc, Term.realize'_var', snoc_last, realize'_not,
        r₂.castSucc.realize_hasMem, isRelFree_sup, isRelFree_hasMem,
        DeltaZeroBoundedFormula.isRelFree_mem, and_self, r₁.realize_allMem, toBoundedFormula_sup,
        realize'_sup, realize'_mem, Term.realize'_substBoundBound, snoc_comp_castSucc,
        realize_sdiff']
      rw [MemStructure.ext_iff]
      grind
    | .iUnion ri rf => by
      simp only [isCharFree_iUnion] at hr
      simp only [eq, Function.comp_apply, Term.castAdd, Term.castLE, toBoundedFormula_inf,
        toBoundedFormula, realize'_inf, BoundedFormula.realize_allMem, isCharFree_castSucc, hr,
        isCharFree_substBoundBound, isRelFree_hasMem, ri.castSucc.realize_exMem, realize_castSucc,
        (rf.substBoundBound (snoc (Fin.castAdd 2) (last (n + 1)))).realize_hasMem,
        realize_substBoundBound, snoc_snoc_comp_snoc_castAdd_two_last, Term.realize'_var',
        snoc_snoc_castAdd_one_last, DeltaZeroBoundedFormula.isRelFree_mem, isRelFree_allMem,
        ri.realize_allMem, rf.realize_allMem, realize'_mem, Term.realize'_substBoundBound,
        le_add_iff_nonneg_right, _root_.zero_le, snoc_comp_castLE, castLE_succ_castSucc,
        snoc_comp_castSucc, snoc_last]
      simp only [MemStructure.ext_iff, mem_realize_iUnion_iff]
      grind
    | .char R _ => by simp at hr
    termination_by (r.depth, 1, 0)
    decreasing_by all_goals simp [depth, castSucc, castAdd, castLE, Prod.lex_def]

  @[simp]
  theorem realize_mem {n : ℕ} (r : L.RudimentaryTerm n) (hr : r.IsCharFree) (t : L.Term' n)
      (xs : Fin n → M) :
      (r.mem t).toBoundedFormula 〘xs〙 ↔ r〘xs〙 ∈ t〘xs〙 := by
    simp [mem, hr, r.castSucc.realize_eq]
    termination_by (r.depth, 2, 0)
    decreasing_by simp [castSucc, castAdd, castLE, Prod.lex_def]

  @[simp]
  theorem realize_memSelf {n : ℕ} (r : L.RudimentaryTerm n) (hr : r.IsCharFree)
      (xs : Fin n → M) :
      (r.memSelf).toBoundedFormula 〘xs〙 ↔ r〘xs〙 ∈ r〘xs〙 := by
    simp [memSelf, hr, r.realize_exMem, r.castSucc.realize_eq]
    termination_by (r.depth, 3, 0)
    decreasing_by all_goals simp [castSucc, castAdd, castLE, Prod.lex_def]

  @[simp]
  theorem realize_allMem {n : ℕ} (r : L.RudimentaryTerm n) (hr : r.IsCharFree)
      (φ : L.DeltaZeroBoundedFormula (n + 1)) (hφ : φ.IsRelFree) (xs : Fin n → M) :
      (r.allMem φ).toBoundedFormula 〘xs〙 ↔
        ∀ y ∈ r〘xs〙, φ.toBoundedFormula 〘snoc xs y〙:=
    match r with
    | .var i => by simp [allMem]
    | .const c => by simp [allMem]
    | .unorderedPair r₁ r₂ => by
      simp only [isCharFree_unorderedPair] at hr
      simp [allMem, hr, hφ, r₁.realize_substLowerAt (k := Fin.last n),
        r₂.realize_substLowerAt (k := Fin.last n)]
    | .sdiff r₁ r₂ => by
      simp only [isCharFree_sdiff] at hr
      simp only [allMem, Function.comp_apply, hr, isRelFree_sup, isCharFree_castSucc,
        isRelFree_hasMem, hφ, and_self, r₁.realize_allMem, toBoundedFormula_sup, realize'_sup,
        r₂.castSucc.realize_hasMem, realize_castSucc, Term.realize'_var', snoc_last, realize_sdiff',
        mem_sdiff_iff, and_imp]
      grind
    | .iUnion ri rf => by
      simp only [isCharFree_iUnion] at hr
      simp only [allMem, hr, isRelFree_substBoundBound, hφ, isRelFree_allMem, ri.realize_allMem,
        rf.realize_allMem, coe_substBoundBound, realize'_substBoundBound,
        snoc_snoc_comp_snoc_castAdd_two_last, mem_realize_iUnion_iff, forall_exists_index, and_imp]
      grind
    | .char R _ => by simp at hr
    termination_by (r.depth, 1, 0)
    decreasing_by all_goals simp [castSucc, castAdd, castLE, depth, Prod.lex_def]

  @[simp]
  theorem realize_exMem {n : ℕ} (r : L.RudimentaryTerm n) (hr : r.IsCharFree)
      (φ : L.DeltaZeroBoundedFormula (n + 1)) (hφ : φ.IsRelFree) (xs : Fin n → M) :
      (r.exMem φ).toBoundedFormula 〘xs〙 ↔
        ∃ y ∈ r〘xs〙, φ.toBoundedFormula 〘snoc xs y〙:= by
    simp [exMem, hr, hφ, r.realize_allMem]
    termination_by (r.depth, 2, 0)
    decreasing_by all_goals simp [Prod.lex_def]

  @[simp]
  theorem realize_substLowerAt {n : ℕ} {k : Fin (n + 1)}
      (r : L.RudimentaryTerm k.val) (hr : r.IsCharFree)
      (φ : L.DeltaZeroBoundedFormula (n + 1)) (hφ : φ.IsRelFree) (xs : Fin n → M) :
      (r.substLowerAt φ).toBoundedFormula 〘xs〙 ↔
        φ.toBoundedFormula 〘Fin.insertNth k (r 〘xs ∘ (Fin.castLE (is_le k))〙) xs〙 :=
  match φ with
  | .falsum => by simp [substLowerAt]
  | .equal t₁ t₂ => by
    simp only [substLowerAt, Function.comp_apply, toBoundedFormula, realize'_bdEqual]
    split_ifs with h₁₂ h₁ h₂
    · simp [h₁₂]
    · rw [h₁] at h₁₂
      simp [hr, h₁, Ne.symm h₁₂, (r.castLE (is_le k)).realize_eq]
      tauto
    · rw [h₂] at h₁₂
      simp [hr, h₂, h₁₂, (r.castLE (is_le k)).realize_eq]
    · simp [h₁, h₂]
  | .mem t₁ t₂ => by
    simp only [substLowerAt, Function.comp_apply, toBoundedFormula, realize'_mem]
    split_ifs with h₁ h₁₂ h₂
    · simp [hr, (r.castLE (is_le k)).realize_memSelf, h₁, h₁₂]
    · rw [h₁] at h₁₂
      simp [hr, h₁, h₁₂, (r.castLE (is_le k)).realize_mem]
    · simp [hr, h₁, h₂, (r.castLE (is_le k)).realize_hasMem]
    · simp [h₁, h₂]
  | .imp φ₁ φ₂ => by
    simp only [DeltaZeroBoundedFormula.isRelFree_imp] at hφ
    simp [substLowerAt, hφ, r.realize_substLowerAt hr φ₁, r.realize_substLowerAt hr φ₂]
  | .allMem t ψ => by
    simp only [substLowerAt, Function.comp_apply, ne_eq, dite_not, toBoundedFormula,
      BoundedFormula.realize_allMem]
    simp only [DeltaZeroBoundedFormula.isRelFree_allMem] at hφ
    split_ifs with h
    · simp [hr, hφ, (r.castLE (is_le k)).realize_allMem, r.realize_substLowerAt (k := k.castSucc) hr ψ,
        h, is_le k]
    · simp [hφ, r.realize_substLowerAt (k := k.castSucc) hr ψ, h, is_le k]
  | .rel R _ => by simp at hφ
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
theorem realize_substBoundRud {φ : L.DeltaZeroBoundedFormula n}
    (hφ : φ.IsRelFree)
    (rs : Fin n → L.RudimentaryTerm m)
    (hrs : ∀ i, (rs i).IsCharFree)
    (xs : Fin m → M) :
    (φ.substBoundRud rs).toBoundedFormula 〘xs〙 ↔
      φ.toBoundedFormula 〘fun i ↦ (rs i)〘xs〙〙:= by
  induction φ generalizing m with
  | falsum => simp [substBoundRud]
  | equal t₁ t₂ =>
    have h₁ : ((Term.substBoundRud t₁ rs).castSucc.hasMem (var (Sum.inr (last m)))).IsRelFree := by
      simp [hrs]
    have h₂ : ((Term.substBoundRud t₂ rs).castSucc.hasMem (var (Sum.inr (last m)))).IsRelFree := by
      simp [hrs]
    simp only [substBoundRud, Function.comp_apply, toBoundedFormula_inf, realize'_inf, hrs,
      implies_true, Term.isCharFree_substBoundRud, h₂, RudimentaryTerm.realize_allMem,
      Term.realize_substBoundRud, isCharFree_castSucc, realize_hasMem, realize_castSucc,
      Term.realize'_var', snoc_last, h₁, toBoundedFormula, realize'_bdEqual]
    rw [MemStructure.ext_iff]
    grind
  | mem t₁ t₂ =>
    have h₁ : (Term.substBoundRud t₁ rs).IsCharFree := by simp [hrs]
    have h₂ : (Term.substBoundRud t₂ rs).IsCharFree := by simp [hrs]
    simp [h₁, h₂, substBoundRud, realize'_mem]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [isRelFree_imp] at hφ
    simp [substBoundRud, hφ, hrs, ih₁, ih₂]
  | allMem t ψ ih =>
    have h₁ : (Term.substBoundRud t rs).IsCharFree := by simp [hrs]
    simp only [isRelFree_allMem] at hφ
    have h₃ :  ∀ i : Fin _, (snoc (α := fun _ ↦ L.RudimentaryTerm (m + 1)) (RudimentaryTerm.castSucc ∘ rs) ᵣ-1 i).IsCharFree := by
      intro i
      cases i using lastCases <;> simp [hrs]
    have h₂ : ψ.substBoundRud (snoc (RudimentaryTerm.castSucc ∘ rs) (ᵣlast m)) |>.IsRelFree := by
      apply isRelFree_substBoundRud (hφ := hφ)
      simp [h₃]
    simp only [substBoundRud, h₁, h₂, RudimentaryTerm.realize_allMem, Term.realize_substBoundRud,
      hφ, h₃, implies_true, ih, toBoundedFormula, BoundedFormula.realize_allMem]
    rw [forall_congr]
    intro y
    congr
    funext i; cases i using Fin.lastCases <;> simp
  | rel R t => simp at hφ

theorem multiclass_substBoundRud_eq_subst {φ : L.DeltaZeroBoundedFormula n}
    (hφ : φ.IsRelFree)
    (rs : Fin n → L.RudimentaryTerm m)
    (hrs : ∀ i, (rs i).IsCharFree) :
    (φ.substBoundRud rs).toBoundedFormula.multiclass =
      φ.toBoundedFormula.multiclass.subst (fun i xs ↦ ((rs i)〘xs〙 : M)) := by
  funext ys
  simp [hφ, hrs, Multiclass.subst]

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.toDeltaZeroBoundedFormula
  (r : L.RudimentaryTerm n) :
  L.DeltaZeroBoundedFormula (n + 1) :=
  (&0 =₀ &1).substBoundRud ![r.castSucc, ᵣ-1]

theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_eq_toDeltaZeroBoundedFormula
    (r : L.RudimentaryTerm m) (hr : r.IsCharFree) :
    (r.realize : Multiclass M (m + 1)) = r.toDeltaZeroBoundedFormula.toBoundedFormula.multiclass := by
  simp only [toDeltaZeroBoundedFormula, Nat.succ_eq_add_one, Nat.reduceAdd, isValue,
    Function.comp_apply, isRelFree_eq, forall_fin_two, Matrix.cons_val_zero, isCharFree_castSucc,
    hr, Matrix.cons_val_one, Matrix.cons_val_fin_one, isCharFree_var, and_self,
    multiclass_substBoundRud_eq_subst, toBoundedFormula]
  funext xs
  rw [← Fin.snoc_init_self xs, MulticlassFunction.toMulticlass_snoc_iff]
  simp [Multiclass.subst, RudimentaryTerm.castSucc, RudimentaryTerm.castAdd, init_def]

end DeltaZeroBoundedFormula

namespace MemStructure

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
-- --   convert isDeltaZero_subst_rudimentaryTerm (A := Multiclass.Eq 2 0 1) (P := P)
-- --     (rs := ![r.castSucc, ᵣ-1])
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
