/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.ModelTheory.Semantics

import Astlib.Mathlib.ModelTheory.Syntax
import Astlib.Mathlib.Fin.Basic
/-!
file docstring
-/

open Fin FirstOrder Language Structure

namespace FirstOrder

namespace Language

variable {m n} {L : Language} {M : Type w} [L.Structure M] {α : Type u'}
  {l : ℕ} {θ : L.BoundedFormula α (l + m)} {ψ : L.BoundedFormula α (l + n)}
  {v : α → M} {xs : Fin l → M}

namespace Term

def realize' (t : L.Term' n) (xs : Fin n → M) :=
  t.realize (Sum.elim default xs)

scoped[FirstOrder.Language] notation:max
  t "〘" xs "〙" => Term.realize' t xs

@[simp]
theorem realize'_var (xs : Fin n → M) (k : Fin n) :
    (&k : L.Term' n) 〘xs〙 = xs k := by
  simp [realize']

@[simp]
theorem realize'_var' (xs : Fin n → M) (k : Fin n) :
    (var (Sum.inr k) : L.Term' n) 〘xs〙 = xs k := by
  simp [realize']

@[simp]
theorem realize'_func (xs : Fin n → M) (f : L.Functions l)
    (ts : Fin l → L.Term' n) :
    (func f ts)〘xs〙 = Structure.funMap f fun i => (ts i)〘xs〙 := rfl

@[simp]
theorem realize'_const (xs : Fin n → M) (c : L.Constants) :
    (c.term)〘xs〙 = L.constantMap c := by
  simp only [Constants.term, realize'_func, constantMap]
  congr
  ext i
  fin_cases i

@[simp]
theorem realize_substBound {n m : ℕ} {t : L.Term (α ⊕ Fin n)} (ts : Fin n → L.Term (α ⊕ Fin m))
    {v : α → M} {xs : Fin m → M} :
    (t.substBound ts).realize (Sum.elim v xs) =
      t.realize (Sum.elim v fun i ↦ (ts i).realize (Sum.elim v xs)) := by
  induction t with
  | var i => cases i <;> simp [substBound]
  | func f _ ih => simp [ih]

@[simp]
theorem realize'_substBound {n m : ℕ} {t : L.Term' n} (ts : Fin n → L.Term' m)
    {xs : Fin m → M} :
    (t.substBound ts)〘xs〙= t〘fun i ↦ (ts i) 〘xs〙〙 := by
  simp [realize']

@[simp]
theorem realize_substBoundBound {n m : ℕ} {t : L.Term (α ⊕ Fin n)} (f : Fin n → Fin m)
    {v : α → M} {xs : Fin m → M} :
    (t.substBoundBound f).realize (Sum.elim v xs) = t.realize (Sum.elim v (xs ∘ f)) := by
  simp only [substBoundBound, Function.comp_apply, realize_substBound]
  rfl

@[simp]
theorem realize'_substBoundBound {n m : ℕ} {t : L.Term' n} (f : Fin n → Fin m)
    {xs : Fin m → M} :
    (t.substBoundBound f) 〘xs〙 = t〘xs ∘ f〙 := by
  simp [realize']

end Term

namespace BoundedFormula

variable (φ ψ : L.BoundedFormula' n) (xs : Fin n → M)

def Realize' (φ : L.BoundedFormula' n) (xs : Fin n → M) := φ.Realize default xs

scoped[FirstOrder.Language] notation:max
  φ "〘" xs "〙" => BoundedFormula.Realize' φ xs

@[simp]
theorem realize_iff_realize' (φ : L.Sentence) : M ⊨ φ ↔ φ.Realize' default (M := M):= by
  simp [Sentence.Realize, Formula.Realize, Realize']

@[simp]
theorem realize'_falsum : (falsum : L.BoundedFormula' n) 〘xs〙 ↔ False := Iff.rfl

@[simp]
theorem realize'_bot : (⊥ : L.BoundedFormula' n) 〘xs〙 ↔ False := Iff.rfl

@[simp]
theorem realize'_not : (∼φ)〘xs〙 ↔ ¬φ〘xs〙 := by
  simp [Realize']

@[simp]
theorem realize'_bdEqual (xs : Fin n → M) (t₁ t₂ : L.Term' n) :
    (t₁ =' t₂)〘xs〙 ↔ t₁〘xs〙 = t₂〘xs〙 := by
  simp [Realize', Term.realize']

@[simp]
theorem realize'_top : (⊤ : L.BoundedFormula' n) 〘xs〙 := by simp [Realize']

@[simp]
theorem realize'_inf : (φ ⊓ ψ)〘xs〙 ↔ φ〘xs〙 ∧ ψ〘xs〙 := by
  simp [Realize']

@[simp]
theorem realize'_foldr_inf (l : List (L.BoundedFormula' n)) (xs : Fin n → M) :
    (l.foldr (· ⊓ ·) ⊤)〘xs〙 ↔ ∀ φ ∈ l, φ〘xs〙 := by
  simp [Realize']

@[simp]
theorem realize'_imp : (φ.imp ψ)〘xs〙 ↔ φ〘xs〙 → ψ〘xs〙 := by
  simp [Realize']

-- /-- List.foldr on BoundedFormula.imp gives a big "And" of input conditions. -/
-- theorem realize'_foldr_imp {k : ℕ} (l : List (L.BoundedFormula' k))
--     (f : L.BoundedFormula' k) (xs : Fin n → M) :
--       (l.foldr BoundedFormula.imp f).Realize v xs =
--       ((∀ i ∈ l, i.Realize v xs) → f.Realize v xs) := by
--   intro v xs
--   induction l
--   next => simp
--   next f' _ _ => by_cases f'.Realize v xs <;> simp [*]

@[simp]
theorem realize'_iff : (φ.iff ψ)〘xs〙 ↔ (φ〘xs〙 ↔ ψ〘xs〙) := by
  simp [Realize']

@[simp]
theorem realize'_rel {k : ℕ} {R : L.Relations k} {ts : Fin k → L.Term' n} :
    (R.boundedFormula ts)〘xs〙 ↔ RelMap R (fun i ↦ (ts i)〘xs〙) :=
  Iff.rfl

@[simp]
theorem realize'_rel₁ {R : L.Relations 1} {t : L.Term _} :
    (R.boundedFormula₁ t)〘xs〙 ↔ RelMap R ![t〘xs〙] := by
  simp [Realize', Term.realize']

@[simp]
theorem realize'_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.boundedFormula₂ t₁ t₂)〘xs〙 ↔
      RelMap R ![t₁〘xs〙, t₂〘xs〙] := by
  simp [Realize', Term.realize']

@[simp]
theorem realize'_sup : (φ ⊔ ψ)〘xs〙 ↔ φ〘xs〙 ∨ ψ〘xs〙 := by
  simp [Realize']

@[simp]
theorem realize'_foldr_sup (l : List (L.BoundedFormula' n)) (xs : Fin n → M) :
    (l.foldr (· ⊔ ·) ⊥)〘xs〙 ↔ ∃ φ ∈ l, φ〘xs〙 := by
  simp [Realize']

variable (xs : Fin l → M)

@[simp]
theorem realize_all' :
    (θ.all' m).Realize v xs ↔ ∀ ys : Fin m → M, θ.Realize v (append xs ys) := by
  induction m with
  | zero => simp [append_right_nil]
  | succ m ih =>
    simp only [all'_succ, ih]
    refine ⟨fun h zs ↦ ?_, fun h ys a ↦ ?_⟩
    · simpa [← append_snoc] using h (init zs) (zs (last _))
    · simpa [← append_snoc] using h (snoc ys a)

@[simp]
theorem realize_ex' :
    (θ.ex' m).Realize v xs ↔ ∃ ys : Fin m → M, θ.Realize v (append xs ys) := by
  induction m with
  | zero => simp [append_right_nil]
  | succ m ih =>
    simp only [ex'_succ, ih, realize_ex]
    refine ⟨fun ⟨ys, a, h⟩ ↦ ⟨snoc ys a, ?_⟩, fun ⟨zs, h⟩ ↦ ⟨init zs, zs (last _), ?_⟩⟩
    · simpa [append_snoc]
    · simpa [← append_snoc]


@[simp]
theorem realize'_all' (θ : L.BoundedFormula' (l + m)) :
    (θ.all' m) 〘xs〙 ↔ ∀ ys : Fin m → M, θ 〘append xs ys〙 := by
  simp [Realize']

@[simp]
theorem realize'_ex' (θ : L.BoundedFormula' (l + m)) :
    (θ.ex' m) 〘xs〙 ↔ ∃ ys : Fin m → M, θ 〘append xs ys〙 := by
  simp [Realize']

@[simp]
theorem realize'_all (θ : L.BoundedFormula' (l + 1)) :
    θ.all 〘xs〙 ↔ ∀ y : M, θ 〘snoc xs y〙 := by
  simp [Realize']

@[simp]
theorem realize'_ex (θ : L.BoundedFormula' (l + 1)) :
    θ.ex 〘xs〙 ↔ ∃ y : M, θ 〘snoc xs y〙 := by
  simp [Realize']


-- theorem realize_imp_ex'_all' [Inhabited M] :
--     let φ := (θ.liftAt n (l + m)).cast (Nat.add_assoc _ _ _) ⟹
--       (ψ.liftAt m l).cast (by rw [Nat.add_assoc, add_comm n]) |>.all' (m + n)
--     φ〘v, xs〙 ↔ (θ.ex' m ⟹ ψ.all' n)〘v, xs〙 := by
--   intro φ
--   simp only [realize_all', realize_imp, realize_ex', forall_exists_index, φ]
--   refine ⟨fun h ys hys zs ↦ ?_, fun h yzs ↦ ?_⟩
--   · specialize h (append ys zs)
--     repeat rw [cast, realize_castLE_of_eq (by omega), realize_liftAt' (by omega)] at h
--     rw [append_append_gap, ← append_assoc, append_gap_same] at h
--     exact h hys
--   · rw [← Fin.append_castAdd_natAdd (f := yzs),
--       cast, realize_castLE_of_eq (by omega), realize_liftAt' (by omega),
--       cast, realize_castLE_of_eq (by omega), realize_liftAt' (by omega),
--       append_append_gap, ← append_assoc, append_gap_same]
--     tauto

-- theorem realize_imp_all'_ex' [Inhabited M] :
--     let φ := (θ.liftAt n (l + m)).cast (Nat.add_assoc _ _ _) ⟹
--       (ψ.liftAt m l).cast (by rw [Nat.add_assoc, add_comm n]) |>.ex' (m + n)
--     φ〘v, xs〙 ↔ (θ.all' m ⟹ ψ.ex' n)〘v, xs〙 := by
--   intro φ
--   simp only [realize_ex', realize_imp, realize_all', φ]
--   refine ⟨fun ⟨yzs, h⟩ hys ↦ ⟨yzs ∘ natAdd _, ?_⟩, fun h ↦ ?_⟩
--   · rw [← Fin.append_castAdd_natAdd (f := yzs),
--       cast, realize_castLE_of_eq (by omega), realize_liftAt' (by omega),
--       cast, realize_castLE_of_eq (by omega), realize_liftAt' (by omega),
--       append_append_gap, ← append_assoc, append_gap_same] at h
--     tauto
--   · by_cases hys : ∀ (ys : Fin m → M), θ〘v, append xs ys〙
--     · obtain ⟨zs, hzs⟩ := h hys
--       refine ⟨append default zs, fun _ ↦ ?_⟩
--       rwa [cast, realize_castLE_of_eq (by omega), realize_liftAt' (by omega), append_append_gap]
--     · simp only [not_forall] at hys
--       obtain ⟨ys, hys⟩ := hys
--       use (append ys default)
--       contrapose! hys
--       rw [cast, realize_castLE_of_eq (by omega), realize_liftAt' (by omega),
--         ← append_assoc, append_gap_same] at hys
--       exact hys.left

@[simp]
theorem realize_substBound {n m : ℕ} {φ : L.BoundedFormula α n} (ts : Fin n → L.Term (α ⊕ Fin m))
    {v : α → M} {xs : Fin m → M} :
    (φ.substBound ts).Realize v xs ↔
      φ.Realize v fun i ↦ (ts i).realize (Sum.elim v xs) := by
  induction φ generalizing m with
  | falsum => simp [substBound, Realize]
  | equal u₁ u₂ => simp [Realize, substBound, Term.realize_substBound]
  | rel R us => simp [Realize, substBound, Term.realize_substBound]
  | imp φ₁ φ₂ ih₁ ih₂ => simp [substBound, ih₁, ih₂]
  | all ψ ih =>
    simp only [substBound, Term.castSucc, Term.castAdd, Term.castLE, castLE_succ_castSucc,
      Function.comp_apply, realize_all, Nat.succ_eq_add_one, ih]
    rw [forall_congr]
    intro
    congr
    ext i
    induction i using lastCases <;> simp

@[simp]
theorem realize_substBoundBound {n m : ℕ} {φ : L.BoundedFormula α n} (f : Fin n → Fin m)
    {v : α → M} {xs : Fin m → M} :
    (φ.substBoundBound f).Realize v xs ↔
      φ.Realize v (xs ∘ f) := by
  simp [substBoundBound, realize_substBound, Function.comp_def]

@[simp]
theorem realize'_substBound {n m : ℕ} {φ : L.BoundedFormula' n} (ts : Fin n → L.Term' m)
    {xs : Fin m → M} :
    (φ.substBound ts)〘xs〙 ↔ φ〘fun i ↦ (ts i)〘xs〙〙 := by
  simp [Realize', Term.realize']

@[simp]
theorem realize'_substBoundBound {n m : ℕ} {φ : L.BoundedFormula' n} (f : Fin n → Fin m)
    {xs : Fin m → M} :
    (φ.substBoundBound f)〘xs〙 ↔ φ〘xs ∘ f〙 := by
  simp [Realize']

variable {n p q : ℕ} (φ : L.BoundedFormula α (n + p)) (ψ : L.BoundedFormula α (n + q))
  (θ : L.BoundedFormula α (n + p + q))
  (χ : L.BoundedFormula α (n + (p + q)))
  -- (θ' : L.BoundedFormula α (n + (p + q)))
  (v : α → M) (xs : Fin n → M) (ys : Fin p → M) (zs : Fin q → M)
  (φ' : L.BoundedFormula' (n + p)) (ψ' : L.BoundedFormula' (n + q))
  (θ' : L.BoundedFormula' (n + p + q))
  (χ' : L.BoundedFormula' (n + (p + q)))


def splitImp {p q : ℕ} (φ : L.BoundedFormula α (n + p)) (ψ : L.BoundedFormula α (n + q)) :
    L.BoundedFormula α (n + p + q) :=
  φ.substBoundBound (Fin.castAdd q) ⟹
    ψ.substBoundBound (append (castAdd q ∘ castAdd p) (natAdd (n + p)))

@[simp]
theorem realize_splitImp :
    (φ.splitImp ψ).Realize v (append (append xs ys) zs) ↔ (φ.Realize v (append xs ys) → ψ.Realize v (append xs zs)) := by
  simp [splitImp, ← Function.comp_assoc]

@[simp]
theorem realize'_splitImp :
    (φ'.splitImp ψ')〘append (append xs ys) zs〙 ↔ (φ'〘append xs ys〙 → ψ'〘append xs zs〙) := by
  simp [Realize']

def switchBound {p : ℕ} (φ : L.BoundedFormula α (n + p)) : L.BoundedFormula α (p + n) :=
  φ.substBoundBound (append (natAdd p) (castAdd n))

@[simp]
theorem realize_switchBound :
    (φ.switchBound).Realize v (append ys xs) ↔ φ.Realize v (append xs ys) := by
  simp [switchBound]

@[simp]
theorem realize'_switchBound :
    (φ'.switchBound) 〘append ys xs〙 ↔ φ' 〘append xs ys〙 := by
  simp [Realize']

def castAssoc {p q : ℕ} (θ : L.BoundedFormula α (n + p + q)) : L.BoundedFormula α (n + (p + q)) :=
  θ.cast (add_assoc n p q)

@[simp]
theorem realize_castAssoc :
    (θ.castAssoc).Realize v (append xs (append ys zs)) ↔ θ.Realize v (append (append xs ys) zs) := by
  simp [castAssoc, append_assoc]

@[simp]
theorem realize'_castAssoc :
    (θ'.castAssoc) 〘append xs (append ys zs)〙 ↔ θ' 〘append (append xs ys) zs〙:= by
  simp [Realize']

def castAssoc' {p q : ℕ} (χ : L.BoundedFormula α (n + (p + q))) :
  L.BoundedFormula α (n + p + q) :=
  χ.cast (add_assoc n p q).symm

@[simp]
theorem realize_castAssoc' :
    (χ.castAssoc').Realize v (append (append xs ys) zs) ↔ χ.Realize v (append xs (append ys zs)) := by
  simp [castAssoc', append_assoc, Function.comp_assoc]

@[simp]
theorem realize'_castAssoc' :
    (χ'.castAssoc') 〘append (append xs ys) zs〙 ↔ χ'〘append xs (append ys zs)〙 := by
  simp [Realize']

def switchBoundRight {p : ℕ} (χ : L.BoundedFormula α (n + (p + q))) :
  L.BoundedFormula α (n + (q + p)) :=
  χ.substBoundBound (append (castAdd (q + p)) (natAdd n ∘ ((append (natAdd q) (castAdd p)))))

@[simp]
theorem realize_switchBoundRight :
    (χ.switchBoundRight).Realize v (append xs (append zs ys)) ↔ χ.Realize v (append xs (append ys zs)) := by
  simp [switchBoundRight]

@[simp]
theorem realize'_switchBoundRight :
    (χ'.switchBoundRight)〘append xs (append zs ys)〙 ↔ χ'〘append xs (append ys zs)〙 := by
  simp [Realize']

def splitImp' {p q : ℕ} (φ : L.BoundedFormula α (p + n)) (ψ : L.BoundedFormula α (q + n)) :
    L.BoundedFormula α (p + q + n) :=
  φ.switchBound.splitImp ψ.switchBound |>.castAssoc.switchBound

@[simp]
theorem realize_splitImp' (φ : L.BoundedFormula α (p + n)) (ψ : L.BoundedFormula α (q + n)) :
    (φ.splitImp' ψ).Realize v (append (append ys zs) xs) ↔
      (φ.Realize v (append ys xs) → ψ.Realize v (append zs xs)) := by
  simp [splitImp']

@[simp]
theorem realize'_splitImp' (φ : L.BoundedFormula' (p + n)) (ψ : L.BoundedFormula' (q + n)) :
    (φ.splitImp' ψ) 〘append (append ys zs) xs〙 ↔
      (φ 〘append ys xs〙 → ψ 〘append zs xs〙) := by
  simp [Realize']

end BoundedFormula

end Language

end FirstOrder
