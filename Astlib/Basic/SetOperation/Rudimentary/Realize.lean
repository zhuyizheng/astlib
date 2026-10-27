/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.MemStructure.Semantics
import Astlib.Basic.SetOperation.Rudimentary.Syntax
import Astlib.Basic.SetOperation.Multiclass.Lambda
import Astlib.Basic.SetOperation.Extensional
/-!
# Realization of rudimentary terms

The realization `r〘xs〙` of a rudimentary term in a `MemStructure`, the closure classes
`PairClosed`, `SDiffClosed` and `RudClosed`, and the basic membership lemmas.
-/
open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula RudimentaryTerm Fin MemStructure

variable {L : FirstOrder.Language} {M : Type*} [L.MemStructure M] [Inhabited M]

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

instance {L : FirstOrder.Language} [L.HasMem] : SDiff (L.RudimentaryTerm n) :=
  ⟨RudimentaryTerm.sdiff⟩

instance {L : Language} [L.HasMem] (r₁ r₂ : L.RudimentaryTerm n) [r₁.CharFree] [r₂.CharFree] :
  (r₁ \ r₂).CharFree := by
  change (r₁.sdiff r₂).CharFree
  infer_instance

def IsIUnion (a x : M) (A : ClassFunction M) := ∀ z, z ∈ a ↔ ∃ y ∈ x, z ∈ A y

noncomputable instance : Decidable (∃ a : M, IsIUnion a x A) :=
  Classical.propDecidable _

noncomputable def iUnion (x : M) (A : ClassFunction M) :=
  dite (∃ a : M, IsIUnion a x A) Classical.choose default

theorem iUnion_eq_of_isIUnion [Extensional M] {a x : M} {A : ClassFunction M}
    (h : IsIUnion a x A) : iUnion x A = a := by
  have h' : ∃ a : M, IsIUnion a x A := ⟨a, h⟩
  ext z
  convert Classical.choose_spec h' z
  · simp [iUnion, h']
  · exact h z

noncomputable instance (R : L.Relations n) (xs : Fin n → M) :
  Decidable (Structure.RelMap R xs) := Classical.propDecidable _

noncomputable instance : EmptyCollection M := ⟨default \ default⟩

end MemStructure

namespace RudimentaryTerm

open MemStructure

-- variable {L : FirstOrder.Language} [L.HasMem]

def singleton₀ {L : FirstOrder.Language} [L.HasMem] : L.RudimentaryTerm 1 := ᵣ{ᵣ0, ᵣ0}

instance {L : FirstOrder.Language} [L.HasMem] : Singleton (L.RudimentaryTerm n) (L.RudimentaryTerm n) :=
  ⟨fun r ↦ singleton₀.substBoundRud ![r]⟩

@[simp]
theorem singleton_def {L : FirstOrder.Language} [L.HasMem] (r : L.RudimentaryTerm n) :
    ({r} : L.RudimentaryTerm n) = singleton₀.substBoundRud ![r] := rfl

instance {L : Language} [L.HasMem] :
  (singleton₀ : L.RudimentaryTerm 1).CharFree := by
  unfold singleton₀; infer_instance

instance {L : Language} [L.HasMem] (r : L.RudimentaryTerm n) [r.CharFree] :
  ({r} : L.RudimentaryTerm n).CharFree := by
  rw [singleton_def]; infer_instance

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
    (char R r)〘xs〙 = if Structure.RelMap R ![r.realize xs] then MemStructure.unorderedPair ∅ ∅ else ∅ := by
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
    ext i; cases i using lastCases <;> simp
  | char R r ih => simp [substBoundRud, ih]

/-- Realizing a vector `vecCons r rs` of rudimentary terms componentwise -/
theorem realize_vecCons_apply {m k : ℕ} (r : L.RudimentaryTerm m)
    (rs : Fin k → L.RudimentaryTerm m) (xs : Fin m → M) :
    (fun i ↦ (Matrix.vecCons r rs i)〘xs〙) = Matrix.vecCons r〘xs〙 fun i ↦ (rs i)〘xs〙 := by
  funext i
  cases i using Fin.cases <;> simp

theorem realize_vecEmpty_apply {m : ℕ} (xs : Fin m → M) :
    (fun i ↦ ((![] : Fin 0 → L.RudimentaryTerm m) i)〘xs〙) = ![] :=
  funext fun i ↦ i.elim0

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
  pairClosed (x y : M) : ∃ a, IsUnorderedPair a x y

variable (M) in
class SDiffClosed : Prop where
  sdiffClosed (x y : M) : ∃ a, IsSDiff a x y

variable (M) in
class RudClosed : Prop extends PairClosed M, SDiffClosed M where
  iUnionClosed {n} (ri : L.RudimentaryTerm n) (rf : L.RudimentaryTerm (n + 1))
    (xs : Fin n → M) : ∃ a, IsIUnion (M := M) a ri〘xs〙 fun y ↦ rf〘snoc xs y〙

variable {n : ℕ} (x y z a : M)

variable [PairClosed M] [SDiffClosed M]

@[simp, grind =]
theorem mem_unorderedPair_iff : x ∈ MemStructure.unorderedPair y z ↔ x = y ∨ x = z := by
  simp only [MemStructure.unorderedPair, PairClosed.pairClosed, ↓reduceDIte]
  rw [Classical.choose_spec (PairClosed.pairClosed y z)]

@[simp, grind =]
theorem mem_sdiff_iff : x ∈ y \ z ↔ x ∈ y ∧ x ∉ z := by
  simp only [SDiff.sdiff, MemStructure.sdiff, SDiffClosed.sdiffClosed, ↓reduceDIte]
  rw [Classical.choose_spec (SDiffClosed.sdiffClosed y z)]

end MemStructure


namespace RudimentaryTerm

-- @[simp]
theorem mem_realize_iUnion_iff₀
    {n : ℕ} (ri : L.RudimentaryTerm n) (rf : L.RudimentaryTerm (n + 1))
    (xs : Fin n → M) (x : M)
    (h : ∃ a, IsIUnion (M := M) a ri〘xs〙 fun y ↦ rf〘snoc xs y〙) :
    x ∈ (ri.iUnion rf)〘xs〙 ↔
      ∃ z ∈ ri〘xs〙, x ∈ rf〘snoc xs z〙 := by
  simp only [MemStructure.iUnion, h, ↓reduceDIte, realize_iUnion]
  rw [Classical.choose_spec h]

@[simp]
theorem mem_realize_iUnion_iff [RudClosed M]
    {n : ℕ} (ri : L.RudimentaryTerm n) (rf : L.RudimentaryTerm (n + 1))
    (xs : Fin n → M) (x : M) :
    x ∈ (ri.iUnion rf)〘xs〙 ↔
      ∃ z ∈ ri〘xs〙, x ∈ rf〘snoc xs z〙 := by
  rw [mem_realize_iUnion_iff₀]
  exact RudClosed.iUnionClosed _ _ _

end RudimentaryTerm

end FirstOrder.Language
