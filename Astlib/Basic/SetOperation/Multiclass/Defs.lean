/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
-- import Mathlib.Logic.Equiv.Defs
import Astlib.Basic.SetOperation.Subset
/-!
file docstring
-/

open FirstOrder Language BoundedFormula Fin

variable {L : Language} {M : Type*} [L.MemStructure M] {α : Type*} {n k : ℕ}

namespace FirstOrder.Language

-- variable (M) in
def MemStructure.Multiclass {L : Language} (M : Type*) [L.MemStructure M] (n : ℕ) :=
  (Fin n → M) → Prop


namespace MemStructure.Multiclass

instance : Top (Multiclass M n) := ⟨fun _ ↦ True⟩

instance : Bot (Multiclass M n) := ⟨fun _ ↦ False⟩

instance : Max (Multiclass M n) := ⟨fun A B xs ↦ A xs ∨ B xs⟩

instance : Min (Multiclass M n) := ⟨fun A B xs ↦ A xs ∧ B xs⟩


variable {n : ℕ} (xs : Fin n → M) (A B : Multiclass M n)

@[simp]
theorem top : (⊤ : Multiclass M n) xs  := by simp [Top.top]

@[simp]
theorem not_bot : ¬(⊥ : Multiclass M n) xs := by simp [Bot.bot]

@[simp]
theorem inf_iff : (A ⊓ B) xs ↔ (A xs ∧ B xs) := by simp [Min.min]

@[simp]
theorem sup_iff : (A ⊔ B) xs ↔ (A xs ∨ B xs) := by simp [Max.max]

@[simp]
def not {n} (A : Multiclass M n) : Multiclass M n := fun xs ↦ ¬A xs

@[simp]
def imp {n} (A B : Multiclass M n) : Multiclass M n := fun xs ↦ A xs → B xs

@[simp]
def iff {n} (A B : Multiclass M n) : Multiclass M n := fun xs ↦ A xs ↔ B xs

@[simp]
def all' {n} (m) (A : Multiclass M (n + m)) : Multiclass M n := fun xs ↦ ∀ vs, A (append xs vs)

def all {n} (A : Multiclass M (n + 1)) : Multiclass M n := A.all' 1

@[simp]
theorem all_iff {n} (A : Multiclass M (n + 1)) (xs : Fin n → M) :
    (A.all) xs ↔ ∀ v, A (snoc xs v) := by
  simp only [all, all', snoc_eq_append, Nat.reduceAdd]
  constructor
  · intro h v
    convert h ![v]
    exact List.ofFn_inj.mp rfl
  · intro h vs
    convert h (vs 0)
    exact List.ofFn_inj.mp rfl

@[simp]
def ex' {n} (m) (A : Multiclass M (n + m)) : Multiclass M n := fun xs ↦ ∃ vs, A (append xs vs)

def ex {n} (A : Multiclass M (n + 1)) : Multiclass M n := A.ex' 1

@[simp]
theorem ex_iff {n} (A : Multiclass M (n + 1)) (xs : Fin n → M) :
    (A.ex) xs ↔ ∃ v, A (snoc xs v) := by
  simp only [ex, ex', snoc_eq_append, Nat.reduceAdd]
  constructor
  · intro ⟨vs, hvs⟩
    refine ⟨vs 0, ?_⟩
    convert hvs
    exact List.ofFn_inj.mp rfl
  · intro ⟨v, hv⟩
    refine ⟨![v], ?_⟩
    convert hv
    exact List.ofFn_inj.mp rfl

@[simp]
def slice {n} (A : Multiclass M (n + m)) (vs : Fin m → M) : Multiclass M n :=
  fun xs ↦ A (append xs vs)

@[simp]
def slice₀ {n} (A : Multiclass M (n + 1)) (c : M) : Multiclass M n := A.slice ![c]

@[simp]
theorem slice_elim0 (A : Multiclass M (n + 0)) : A.slice elim0 = A := by
  funext xs
  simp

@[inherit_doc] scoped[FirstOrder] infixr:62 " ⟹ " =>
  FirstOrder.Language.MemStructure.Multiclass.imp
-- input \==>

@[inherit_doc] scoped[FirstOrder] prefix:110 "∀' " =>
  FirstOrder.Language.MemStructure.Multiclass.all

@[inherit_doc] scoped[FirstOrder] prefix:arg "∼" =>
  FirstOrder.Language.MemStructure.Multiclass.not
-- input \~, the ASCII character ~ has too low precedence

@[inherit_doc] scoped[FirstOrder] infixl:61 " ⇔ " =>
  FirstOrder.Language.MemStructure.Multiclass.iff
-- input \<=>

@[inherit_doc] scoped[FirstOrder] prefix:110 "∃' " =>
  FirstOrder.Language.MemStructure.Multiclass.ex
-- input \ex

def iSup {β : Type*} [Finite β] (As : β → Multiclass M n) : Multiclass M n :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map As).foldr (· ⊔ ·) ⊥

def iInf {β : Type*} [Finite β] (As : β → Multiclass M n) : Multiclass M n :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map As).foldr (· ⊓ ·) ⊤

variable {β : Type*} [Finite β] (As : β → Multiclass M n)

@[simp]
theorem foldr_sup_iff (f : List (Multiclass M n)) (xs : Fin n → M) :
    (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ f) xs ↔ ∃ A ∈ f, A xs := by
  induction f with
  | nil => simp
  | cons ψ f ih => simp [ih]

@[simp]
theorem iSup_iff : iSup As xs ↔ (∃ i, As i xs) := by
  simp [iSup]

@[simp]
theorem foldr_inf_iff (f : List (Multiclass M n)) (xs : Fin n → M) :
    (List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ f) xs ↔ ∀ A ∈ f, A xs := by
  induction f with
  | nil => simp
  | cons ψ f ih => simp [ih]

@[simp]
theorem iInf_iff : iInf As xs ↔ (∀ i, As i xs) := by
  simp [iInf]

variable {m n : ℕ} (A B : Multiclass M (n + m)) (vs : Fin m → M)

@[simp]
theorem slice_top : (⊤ : Multiclass M (n + m)).slice vs = ⊤ := by funext; simp

@[simp]
theorem slice_bot : (⊥ : Multiclass M (n + m)).slice vs = ⊥ := by funext; simp

@[simp]
theorem slice_not : (∼A).slice vs = ∼(A.slice vs) := by funext; simp

@[simp]
theorem slice_imp : (A ⟹ B).slice vs = (A.slice vs) ⟹ (B.slice vs) := by funext; simp

@[simp]
theorem slice_sup : (A ⊔ B).slice vs = (A.slice vs) ⊔ (B.slice vs) := by funext; simp

@[simp]
theorem slice_inf : (A ⊓ B).slice vs = (A.slice vs) ⊓ (B.slice vs) := by funext; simp

variable (As : β → Multiclass M (n + m))

@[simp]
theorem slice_foldr_sup (f : List (Multiclass M (n + m))) :
    (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ f).slice vs =
      List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ (List.map (fun A ↦ A.slice vs) f) := by
  induction f with
  | nil => simp
  | cons ψ f ih => simp [ih]

@[simp]
theorem slice_iSup : (iSup As).slice vs = iSup (fun i ↦ (As i).slice vs) := by
  simp only [iSup, slice_foldr_sup, List.map_map]
  rfl

@[simp]
theorem slice_foldr_inf (f : List (Multiclass M (n + m))) :
    (List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ f).slice vs =
      List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ (List.map (fun A ↦ A.slice vs) f) := by
  induction f with
  | nil => simp
  | cons ψ f ih => simp [ih]

@[simp]
theorem slice_iInf : (iInf As).slice vs = iInf (fun i ↦ (As i).slice vs) := by
  simp only [iInf, slice_foldr_inf, List.map_map]
  rfl

@[simp]
theorem slice_iff : (A ⇔ B).slice vs = (A.slice vs) ⇔ (B.slice vs) := by funext; simp

variable {n : ℕ} (A B : Multiclass M n)

lemma not_eq : ∼A = A ⟹ ⊥ := by
  funext xs
  simp [not, imp]

lemma sup_eq : A ⊔ B = (∼A) ⟹ B := by
  funext xs
  simp only [max, imp, not, eq_iff_iff]
  tauto

lemma inf_eq : A ⊓ B = ∼(A ⟹ ∼B) := by
  funext xs
  simp only [min, imp, not, eq_iff_iff]
  tauto

lemma iff_eq : A ⇔ B = (A ⟹ B) ⊓ (B ⟹ A) := by
  funext xs
  simp only [min, imp, iff, eq_iff_iff]
  tauto

@[simp]
def remap {n n'} (A : Multiclass M n) (f : Fin n → Fin n') : Multiclass M n' := fun xs ↦ A (xs ∘ f)

variable (f : Fin n → Fin n')

@[simp]
theorem remap_top : (⊤ : Multiclass M n).remap f = ⊤ := by funext; simp

@[simp]
theorem remap_bot : (⊥ : Multiclass M n).remap f = ⊥ := by funext; simp

@[simp]
theorem remap_not : (∼A).remap f = ∼(A.remap f) := by funext; simp

@[simp]
theorem remap_imp : (A ⟹ B).remap f = (A.remap f) ⟹ (B.remap f) := by funext; simp

@[simp]
theorem remap_sup : (A ⊔ B).remap f = (A.remap f) ⊔ (B.remap f) := by funext; simp

@[simp]
theorem remap_inf : (A ⊓ B).remap f = (A.remap f) ⊓ (B.remap f) := by funext; simp

variable (As : β → Multiclass M n)

@[simp]
theorem remap_foldr_sup (L : List (Multiclass M n)) :
    (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ L).remap f =
      List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ (List.map (fun A ↦ A.remap f) L) := by
  induction L with
  | nil => simp
  | cons ψ f ih => simp [ih]

@[simp]
theorem remap_iSup : (iSup As).remap f = iSup (fun i ↦ (As i).remap f) := by
  simp only [iSup, remap_foldr_sup, List.map_map]
  rfl

@[simp]
theorem remap_foldr_inf (L : List (Multiclass M n)) :
    (List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ L).remap f =
      List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ (List.map (fun A ↦ A.remap f) L) := by
  induction L with
  | nil => simp
  | cons ψ f ih => simp [ih]

@[simp]
theorem remap_iInf : (iInf As).remap f = iInf (fun i ↦ (As i).remap f) := by
  simp only [iInf, remap_foldr_inf, List.map_map]
  rfl

@[simp]
theorem remap_iff : (A ⇔ B).remap f = (A.remap f) ⇔ (B.remap f) := by funext; simp

/-- The multiclass of `xs` with `xs i = xs j` -/
@[simp]
def Eq (n) (i j : Fin n) : Multiclass M n := fun xs ↦ xs i = xs j

/-- The multiclass of `xs` with `xs i ∈ xs j` -/
@[simp]
def Mem (n) (i j : Fin n) : Multiclass M n := fun xs ↦ xs i ∈ xs j

/-- The multiclass of `xs` with `xs i ⊆ xs j` -/
@[simp]
def Subset (n) (i j : Fin n) : Multiclass M n := fun xs ↦ xs i ⊆ xs j

-- /-- For any `xs`, there is `x` with `A (snoc xs x)` -/
-- def AllEx (A : Multiclass M (n + 1)) := ∀ xs : Fin n → M, ∃ x, A (snoc xs x)

-- /-- For any `xs`, there is at most one `x` with `A (snoc xs x)` -/
-- def AllUnique (A : Multiclass M (n + 1)) :=
--   ∀ xs : Fin n → M, ∀ x₁ x₂, A (snoc xs x₁) → A (snoc xs x₂) → x₁ = x₂

-- /-- For any `xs`, there is at most one `x` with `A (snoc xs x)` -/
-- def AllExUnique (A : Multiclass M (n + 1)) := ∀ xs : Fin n → M, ∃! x, A (snoc xs x)

end MemStructure.Multiclass


namespace BoundedFormula

open MemStructure

@[simp]
def multiclass {n : ℕ} (φ : L.BoundedFormula' n) : Multiclass M n :=
  fun xs ↦ φ 〘xs〙

-- def multiclass₀ {n : ℕ} (φ : L.BoundedFormula' n)
--     : Multiclass M n :=
--   fun xs ↦ φ 〘xs〙

-- infix:88 " ﹫ " => FirstOrder.Language.BoundedFormula.multiclass

-- scoped[FirstOrder.Language] notation:max
--   φ "〘" vs "++〙" => BoundedFormula.multiclass φ vs

variable {m n l : ℕ} {φ : L.BoundedFormula' n}
  {vs : Fin m → M}
  {ψ : L.BoundedFormula' n} {us : Fin l → M}

@[simp]
lemma multiclass_top : (⊤ : L.BoundedFormula' n).multiclass = (⊤ : Multiclass M n) := by
  funext
  simp [multiclass]

@[simp]
lemma multiclass_bot : (⊥ : L.BoundedFormula' n).multiclass = (⊥ : Multiclass M n) := by
  funext
  simp [multiclass]

@[simp]
lemma multiclass_not : (∼φ).multiclass = (∼φ.multiclass : Multiclass M n) := by
  funext
  simp [multiclass, MemStructure.Multiclass.not]

@[simp]
lemma multiclass_imp : (φ ⟹ ψ).multiclass = (φ.multiclass ⟹ ψ.multiclass : Multiclass M n) := by
  funext
  simp [multiclass, MemStructure.Multiclass.imp]

@[simp]
lemma multiclass_all' {φ : L.BoundedFormula' (n + m)} :
    (φ.all' m).multiclass = (φ.multiclass : Multiclass M _).all' m := by
  funext
  simp [multiclass, MemStructure.Multiclass.all']

@[simp]
lemma multiclass_all {φ : L.BoundedFormula' (n + 1)} :
    (∀' φ).multiclass = (∀' (φ.multiclass) : Multiclass M n) := φ.multiclass_all'

@[simp]
lemma multiclass_ex' {φ : L.BoundedFormula' (n + m)} :
    (φ.ex' m).multiclass = (φ.multiclass : Multiclass M _).ex' m := by
  funext
  simp [multiclass, MemStructure.Multiclass.ex']

@[simp]
lemma multiclass_ex {φ : L.BoundedFormula' (n + 1)} :
    (∃' φ).multiclass = (∃' (φ.multiclass) : Multiclass M n) := φ.multiclass_ex'

-- lemma multiclass_slice {φ : L.BoundedFormula' (m + (n + 1))}
--     (c : M) :
--     (φ.switchBoundRight).castAssoc' 〘snoc vs c ++〙 = (φ 〘vs ++〙).slice c := by
--   funext
--   simp [multiclass, MemStructure.Multiclass.slice, snoc_eq_append]

@[simp]
lemma multiclass_remap {φ : L.BoundedFormula' n}
    (f : Fin n → Fin n') :
    (φ.substBoundBound f).multiclass = (φ.multiclass : Multiclass M n).remap f := by
  funext
  simp [multiclass, MemStructure.Multiclass.remap]

variable (i j : Fin n)

@[simp]
lemma multiclass_eq :
    (&i =' &j).multiclass = @MemStructure.Multiclass.Eq L M _ n i j := by
  funext
  simp [multiclass, MemStructure.Multiclass.Eq]

@[simp]
lemma multiclass_mem :
    (&i ∈' &j).multiclass = @MemStructure.Multiclass.Mem L M _ n i j := by
  funext
  simp [multiclass, MemStructure.Multiclass.Mem]

@[simp]
lemma multiclass_subset :
    (&i ⊆' &j).multiclass = @MemStructure.Multiclass.Subset L M _ n i j := by
  funext
  simp [multiclass, MemStructure.Multiclass.Subset]

end BoundedFormula


def MemStructure.Class {L : Language} (M : Type*) [L.MemStructure M] := M → Prop


namespace MemStructure

namespace Class

open MemStructure

instance : HasSubset (Class M) := ⟨fun A B ↦ ∀ x, A x → B x⟩

@[coe]
def toMulticlass : Class M → Multiclass M 1 :=
  (Equiv.funUnique (Fin 1) M).symm.arrowCongr (_root_.Equiv.refl _)

@[coe]
def _root_.FirstOrder.Language.MemStructure.Multiclass.toClass : Multiclass M 1 → Class M :=
  (Equiv.funUnique (Fin 1) M).arrowCongr (_root_.Equiv.refl _)

instance : Coe (Class M) (Multiclass M 1) := ⟨toMulticlass⟩

instance : Coe (Multiclass M 1) (Class M) := ⟨Multiclass.toClass⟩

theorem iff_toMulticlass (A : Class M) (x : M) :
    A x ↔ (A : Multiclass M 1) ![x] := by
  norm_cast

@[simp, norm_cast]
lemma toClass_toMulticlass (A : Class M) : ((A : Multiclass M 1) : Class M) = A := by norm_cast

@[simp, norm_cast]
lemma _root_.FirstOrder.Language.MemStructure.Multiclass.toMulticlass_toClass (A : Multiclass M 1) :
    ((A : Class M) : Multiclass M 1) = A := by
  funext u
  unfold Multiclass at A
  simp only [toMulticlass, Equiv.arrowCongr, Equiv.coe_refl, _root_.Equiv.symm_symm,
    Equiv.funUnique_apply, default_eq_zero, isValue, Function.id_comp, Equiv.refl_symm,
    Equiv.funUnique_symm_apply, Multiclass.toClass, Equiv.coe_fn_mk, Function.comp_apply]
  congr
  ext i; fin_cases i; rfl

instance : Top (Class M) := ⟨(⊤ : Multiclass M 1)⟩

instance : Bot (Class M) := ⟨(⊥ : Multiclass M 1)⟩

def inf (A B : Class M) : Class M := (A ⊓ B : Multiclass M 1)

instance : Min (Class M) := ⟨inf⟩

def sup (A B : Class M) : Class M := (A ⊔ B : Multiclass M 1)

instance : Max (Class M) := ⟨sup⟩

def not (A : Class M) : Class M := (∼A : Multiclass M 1)

def imp (A B : Class M) : Class M := (A ⟹ B : Multiclass M 1)

def iff (A B : Class M) : Class M := (A ⇔ B : Multiclass M 1)

@[inherit_doc] scoped[FirstOrder] infixr:62 " ⟹ " =>
  FirstOrder.Language.MemStructure.Class.imp
-- input \==>

@[inherit_doc] scoped[FirstOrder] prefix:arg "∼" =>
  FirstOrder.Language.MemStructure.Class.not
-- input \~, the ASCII character ~ has too low precedence

@[inherit_doc] scoped[FirstOrder] infixl:61 " ⇔ " =>
  FirstOrder.Language.MemStructure.Class.iff
-- input \<=>

variable (A B : Class M) (x : M)

@[simp]
lemma top : (⊤ : Class M) x := by norm_cast

@[simp]
lemma bot_iff : (⊥ : Class M) x ↔ False := by norm_cast

@[simp]
lemma imp_iff : (A ⟹ B) x ↔ (A x → B x) := by rfl

@[simp]
lemma not_iff : (∼A) x ↔ ¬A x := by norm_cast

@[simp]
lemma sup_iff : (A ⊔ B) x ↔ A x ∨ B x := by norm_cast

@[simp]
lemma inf_iff : (A ⊓ B) x ↔ A x ∧ B x := by norm_cast

@[simp]
lemma iff_iff : (A ⇔ B) x ↔ (A x ↔ B x) := by norm_cast

/-- The class of `x` with `x = c` -/
def Eq (c : M) : Class M := Multiclass.Eq 2 0 1 |>.slice₀ c

@[simp]
theorem eq_iff (c x : M) : Eq c x ↔ x = c := by norm_cast

/-- The class of `x` with `x ∈ c` -/
def Mem (c : M) : Class M := Multiclass.Mem 2 0 1 |>.slice₀ c

@[simp]
theorem mem_iff (c x : M) : Mem c x ↔ x ∈ c := by norm_cast

/-- The class of `x` with `x ⊆ c` -/
def Subset (c : M) : Class M := Multiclass.Subset 2 0 1 |>.slice₀ c

@[simp]
theorem subset_iff (c x : M) : Subset c x ↔ x ⊆ c := by norm_cast

end Class

@[implicit_reducible]
def MulticlassFunction {L : Language} (M : Type*) [L.MemStructure M] (n : ℕ) :=
  (Fin n → M) → M

namespace MulticlassFunction

variable {n : ℕ}

@[coe]
def toMulticlass (F : MulticlassFunction M n) : Multiclass M (n + 1) :=
  fun xs ↦ F (xs ∘ Fin.castSucc) = xs (Fin.last _)

instance : Coe (MulticlassFunction M n) (Multiclass M (n + 1)) := ⟨toMulticlass⟩

@[simp]
theorem toMulticlass_snoc_iff (F : MulticlassFunction M n) (xs : Fin n → M) (y : M) :
    (F : Multiclass M (n + 1)) (snoc xs y) ↔ F xs = y := by
  simp [toMulticlass]

variable (F : MulticlassFunction M n)

-- theorem allExUnique : (F : Multiclass M (n + 1)).AllExUnique := by
--   simp [Multiclass.AllExUnique]

def proj {n} (i : Fin n) : MulticlassFunction M n := fun xs ↦ xs i

def comp (F : MulticlassFunction M l) (Gs : Fin l → MulticlassFunction M n) :
  MulticlassFunction M n :=
  fun xs ↦ F (fun i ↦ Gs i xs)

@[simp]
theorem proj_eq {n} (i : Fin n) (xs : Fin n → M) : MulticlassFunction.proj i xs = xs i := by
  simp [proj]

@[norm_cast]
theorem cast_proj {n} (i : Fin n) :
    MulticlassFunction.toMulticlass (M := M) (MulticlassFunction.proj i) =
      Multiclass.Eq (n + 1) (i.castSucc) (Fin.last n) := by
  norm_cast

theorem eq_remap_imp_eq {F : MulticlassFunction M n} :
    F = ((F : Multiclass M (n + 1)).remap (snoc (castAdd 2) (last _)) ⟹
      Multiclass.Eq (n + 2) (last _).castSucc (last _)).all := by
  funext xs
  simp only [toMulticlass, Multiclass.all_iff, Multiclass.imp, Multiclass.remap,
    Function.comp_apply, snoc_last, Multiclass.Eq, snoc_castSucc, eq_iff_iff]
  set us := xs ∘ castSucc
  set u := xs (last n)
  have : xs = snoc us u := by rw [← Fin.snoc_init_self xs]; congr
  simp [this, eq_comm]

theorem comp_eq_ex'
  (F : MulticlassFunction M l) (Gs : Fin l → MulticlassFunction M n) :
  F.comp Gs =
    ((F : Multiclass M (l + 1)).remap (snoc (natAdd (n + 1)) ((Fin.last n).castAdd l)) ⊓
      Multiclass.iInf fun i : Fin l ↦ (Gs i : Multiclass M (n + 1)).remap
        (snoc (castAdd l ∘ castSucc) (i.natAdd (n + 1)))).ex' l := by
  funext xs
  simp only [toMulticlass, comp, Multiclass.ex', Multiclass.inf_iff, Multiclass.remap,
    Function.comp_assoc, snoc_comp_castSucc, append_comp_natAdd, Function.comp_apply, snoc_last,
    append_left, Multiclass.iInf_iff, append_right, eq_iff_iff]
  simp only [← Function.comp_assoc, append_comp_castAdd]
  refine ⟨by grind, fun ⟨vs, hvs₁, hvs₂⟩ ↦ ?_⟩
  rw [← hvs₁]
  congr
  ext
  exact hvs₂ _

theorem comp_eq_all'
  (F : MulticlassFunction M l) (Gs : Fin l → MulticlassFunction M n) :
  F.comp Gs =
    ((Multiclass.iInf fun i : Fin l ↦ (Gs i : Multiclass M (n + 1)).remap
    (snoc (castAdd l ∘ castSucc) (i.natAdd (n + 1)))) ⟹
    (F : Multiclass M (l + 1)).remap (snoc (natAdd (n + 1)) ((Fin.last n).castAdd l))).all' l := by
  funext xs
  simp only [toMulticlass, comp, Multiclass.all', Multiclass.iInf_iff, Multiclass.imp,
    Multiclass.remap, Function.comp_assoc, snoc_comp_castSucc, Function.comp_apply, snoc_last,
    append_right, append_comp_natAdd, append_left, eq_iff_iff]
  simp only [← Function.comp_assoc, append_comp_castAdd]
  refine ⟨fun h vs hvs ↦ ?_, by grind⟩
  rw [← h]
  congr
  ext
  exact (hvs _).symm

end MulticlassFunction

namespace Multiclass

variable {l n : ℕ}

def subst (A : Multiclass M l) (Gs : Fin l → MulticlassFunction M n) :
  Multiclass M n :=
  fun xs ↦ A (fun i ↦ Gs i xs)

theorem subst_eq_remap (A : Multiclass M n) (f : Fin n → Fin n') :
    A.subst (fun i xs ↦ xs (f i)) = A.remap f := rfl

variable (A : Multiclass M l) (Gs : Fin l → MulticlassFunction M n)

theorem subst_eq_ex' :
  A.subst Gs =
    (A.remap (natAdd n) ⊓
    Multiclass.iInf fun i : Fin l ↦ (Gs i : Multiclass M (n + 1)).remap
    (snoc (castAdd l) (i.natAdd n))).ex' l := by
  funext xs
  simp only [subst, ex', inf_iff, remap, append_comp_natAdd, iInf_iff, append_comp_snoc_castAdd,
    append_right, MulticlassFunction.toMulticlass_snoc_iff, eq_iff_iff]
  exact ⟨by grind, fun ⟨vs, hvs₁, hvs₂⟩ ↦ by simp_rw [hvs₂, hvs₁]⟩

theorem subst_eq_all' :
  A.subst Gs =
    ((Multiclass.iInf fun i : Fin l ↦ (Gs i : Multiclass M (n + 1)).remap
    (snoc (castAdd l) (i.natAdd n))) ⟹
    A.remap (natAdd n)).all' l := by
  funext xs
  simp only [subst, all', iInf_iff, imp, remap, append_comp_snoc_castAdd, append_right,
    MulticlassFunction.toMulticlass_snoc_iff, append_comp_natAdd, eq_iff_iff]
  exact ⟨fun h vs hvs ↦ by convert h; rw [hvs], by grind⟩

theorem subst_slice_eq_subst (A : Multiclass M (l + m)) (ys : Fin m → M)
    (Gs : Fin l → MulticlassFunction M n) :
    (A.slice ys).subst Gs = A.subst (append Gs fun i _ ↦ ys i) := by
  funext zs
  simp only [subst, slice]
  congr
  ext i; cases i using Fin.addCases <;> simp

theorem subst_slice_eq_slice_subst (A : Multiclass M (l + m)) (ys : Fin m → M)
    (Gs : Fin l → MulticlassFunction M n) :
    (A.slice ys).subst Gs =
      (A.subst (append (fun i zs ↦ Gs i (fun j ↦ zs (j.castAdd m)))
        (fun i zs ↦ zs (i.natAdd n)))).slice ys := by
  funext ws
  simp only [subst, slice]
  congr
  ext i; cases i using Fin.addCases <;> simp

end Multiclass


namespace Class

def subst (A : Class M) (G : MulticlassFunction M n) :
  Multiclass M n := A ∘ G

theorem subst_eq_subst_toMulticlass (A : Class M) (G : MulticlassFunction M n) :
    A.subst G = (A : Multiclass M 1).subst ![G] := by
  norm_cast

-- theorem subst_eq_remap (A : Class M) (i : Fin n) :
--     A.subst (MulticlassFunction.proj i) = A.remap  := rfl

end Class

@[implicit_reducible]
def ClassFunction {L : Language} (M : Type*) [L.MemStructure M] := M → M

namespace ClassFunction

@[coe]
def toMulticlassFunction : ClassFunction M → MulticlassFunction M 1 :=
  (Equiv.funUnique (Fin 1) M).symm.arrowCongr (_root_.Equiv.refl _)

instance : Coe (ClassFunction M) (MulticlassFunction M 1) := ⟨toMulticlassFunction⟩

theorem eq_toMulticlassFunction (F : ClassFunction M) (x : M) :
    F x = (F : MulticlassFunction M 1) ![x] := by
  simp [toMulticlassFunction]

@[coe]
def toMulticlass : ClassFunction M → Multiclass M 2 :=
  MulticlassFunction.toMulticlass ∘ toMulticlassFunction

instance : Coe (ClassFunction M) (Multiclass M 2) := ⟨toMulticlass⟩

@[simp]
theorem toMulticlass_vec_iff (F : ClassFunction M) (x y : M) :
    (F : Multiclass M 2) ![x, y] ↔ F x = y := by
  norm_cast

@[norm_cast, simp]
theorem cast_cast (F : ClassFunction M) :
    ((F : MulticlassFunction M 1) : Multiclass M 2) = (F : Multiclass M 2) := by
  norm_cast

def comp (F : ClassFunction M) (G : ClassFunction M) :
  ClassFunction M := F ∘ G

@[norm_cast]
theorem cast_comp (F G : ClassFunction M) :
    (F.comp G : MulticlassFunction M 1) =
      (F : MulticlassFunction M 1).comp (fun _ : Fin 1 ↦ G) := by
  norm_cast

end ClassFunction

end FirstOrder.Language.MemStructure
