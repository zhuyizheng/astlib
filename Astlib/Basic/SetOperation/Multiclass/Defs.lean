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

variable {L : FirstOrder.Language} [L.HasMem] {M : MemStructure} {α : Type*} {n k : ℕ}

namespace FirstOrder.Language

def MemStructure.Multiclass (n) := (Fin n → M) → Prop

namespace MemStructure.Multiclass

instance : Top (M.Multiclass n) := ⟨fun _ ↦ True⟩

instance : Bot (M.Multiclass n) := ⟨fun _ ↦ False⟩

instance : Max (M.Multiclass n) := ⟨fun A B xs ↦ A xs ∨ B xs⟩

instance : Min (M.Multiclass n) := ⟨fun A B xs ↦ A xs ∧ B xs⟩


variable {n : ℕ} (xs : Fin n → M) (A B : M.Multiclass n)

@[simp]
theorem top : (⊤ : M.Multiclass n) xs  := by simp [Top.top]

@[simp]
theorem not_bot : ¬(⊥ : M.Multiclass n) xs := by simp [Bot.bot]

@[simp]
theorem inf_iff : (A ⊓ B) xs ↔ (A xs ∧ B xs) := by simp [Min.min]

@[simp]
theorem sup_iff : (A ⊔ B) xs ↔ (A xs ∨ B xs) := by simp [Max.max]

@[simp]
def not {n} (A : M.Multiclass n) : M.Multiclass n := fun xs ↦ ¬A xs

@[simp]
def imp {n} (A B : M.Multiclass n) : M.Multiclass n := fun xs ↦ A xs → B xs

@[simp]
def iff {n} (A B : M.Multiclass n) : M.Multiclass n := fun xs ↦ A xs ↔ B xs

@[simp]
def all' {n} (m) (A : @Multiclass M (n + m)) : M.Multiclass n := fun xs ↦ ∀ vs, A (append xs vs)

def all {n} (A : @Multiclass M (n + 1)) : M.Multiclass n := A.all' 1

@[simp]
theorem all_iff {n} (A : @Multiclass M (n + 1)) (xs : Fin n → M) :
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
def ex' {n} (m) (A : @Multiclass M (n + m)) : M.Multiclass n := fun xs ↦ ∃ vs, A (append xs vs)

def ex {n} (A : @Multiclass M (n + 1)) : M.Multiclass n := A.ex' 1

@[simp]
theorem ex_iff {n} (A : @Multiclass M (n + 1)) (xs : Fin n → M) :
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
def slice {n} (A : M.Multiclass (n + m)) (vs : Fin m → M) : M.Multiclass n :=
  fun xs ↦ A (append xs vs)

@[simp]
def slice₀ {n} (A : M.Multiclass (n + 1)) (c : M) : M.Multiclass n := A.slice ![c]

@[simp]
theorem slice_elim0 (A : M.Multiclass (n + 0)) : A.slice elim0 = A := by
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

def iSup {β : Type*} [Finite β] (As : β → M.Multiclass n) : M.Multiclass n :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map As).foldr (· ⊔ ·) ⊥

def iInf {β : Type*} [Finite β] (As : β → M.Multiclass n) : M.Multiclass n :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map As).foldr (· ⊓ ·) ⊤

variable {β : Type*} [Finite β] (As : β → M.Multiclass n)

@[simp]
theorem foldr_sup_iff (f : List (M.Multiclass n)) (xs : Fin n → M) :
    (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ f) xs ↔ ∃ A ∈ f, A xs := by
  induction f with
  | nil => simp
  | cons ψ f ih => simp [ih]

@[simp]
theorem iSup_iff : iSup As xs ↔ (∃ i, As i xs) := by
  simp [iSup]

@[simp]
theorem foldr_inf_iff (f : List (M.Multiclass n)) (xs : Fin n → M) :
    (List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ f) xs ↔ ∀ A ∈ f, A xs := by
  induction f with
  | nil => simp
  | cons ψ f ih => simp [ih]

@[simp]
theorem iInf_iff : iInf As xs ↔ (∀ i, As i xs) := by
  simp [iInf]

variable {m n : ℕ} (A B : M.Multiclass (n + m)) (vs : Fin m → M)

@[simp]
theorem slice_top : (⊤ : M.Multiclass (n + m)).slice vs = ⊤ := by funext; simp

@[simp]
theorem slice_bot : (⊥ : M.Multiclass (n + m)).slice vs = ⊥ := by funext; simp

@[simp]
theorem slice_not : (∼A).slice vs = ∼(A.slice vs) := by funext; simp

@[simp]
theorem slice_imp : (A ⟹ B).slice vs = (A.slice vs) ⟹ (B.slice vs) := by funext; simp

@[simp]
theorem slice_sup : (A ⊔ B).slice vs = (A.slice vs) ⊔ (B.slice vs) := by funext; simp

@[simp]
theorem slice_inf : (A ⊓ B).slice vs = (A.slice vs) ⊓ (B.slice vs) := by funext; simp

variable (As : β → M.Multiclass (n + m))

@[simp]
theorem slice_foldr_sup (f : List (M.Multiclass (n + m))) :
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
theorem slice_foldr_inf (f : List (M.Multiclass (n + m))) :
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

variable {n : ℕ} (A B : M.Multiclass n)

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
def remap {n n'} (A : M.Multiclass n) (f : Fin n → Fin n') : M.Multiclass n' := fun xs ↦ A (xs ∘ f)

variable (f : Fin n → Fin n')

@[simp]
theorem remap_top : (⊤ : M.Multiclass n).remap f = ⊤ := by funext; simp

@[simp]
theorem remap_bot : (⊥ : M.Multiclass n).remap f = ⊥ := by funext; simp

@[simp]
theorem remap_not : (∼A).remap f = ∼(A.remap f) := by funext; simp

@[simp]
theorem remap_imp : (A ⟹ B).remap f = (A.remap f) ⟹ (B.remap f) := by funext; simp

@[simp]
theorem remap_sup : (A ⊔ B).remap f = (A.remap f) ⊔ (B.remap f) := by funext; simp

@[simp]
theorem remap_inf : (A ⊓ B).remap f = (A.remap f) ⊓ (B.remap f) := by funext; simp

variable (As : β → M.Multiclass n)

@[simp]
theorem remap_foldr_sup (L : List (M.Multiclass n)) :
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
theorem remap_foldr_inf (L : List (M.Multiclass n)) :
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
def Eq (n) (i j : Fin n) : M.Multiclass n := fun xs ↦ xs i = xs j

/-- The multiclass of `xs` with `xs i ∈ xs j` -/
@[simp]
def Mem (n) (i j : Fin n) : M.Multiclass n := fun xs ↦ xs i ∈ xs j

/-- The multiclass of `xs` with `xs i ⊆ xs j` -/
@[simp]
def Subset (n) (i j : Fin n) : M.Multiclass n := fun xs ↦ xs i ⊆ xs j

-- /-- For any `xs`, there is `x` with `A (snoc xs x)` -/
-- def AllEx (A : M.Multiclass (n + 1)) := ∀ xs : Fin n → M, ∃ x, A (snoc xs x)

-- /-- For any `xs`, there is at most one `x` with `A (snoc xs x)` -/
-- def AllUnique (A : M.Multiclass (n + 1)) :=
--   ∀ xs : Fin n → M, ∀ x₁ x₂, A (snoc xs x₁) → A (snoc xs x₂) → x₁ = x₂

-- /-- For any `xs`, there is at most one `x` with `A (snoc xs x)` -/
-- def AllExUnique (A : M.Multiclass (n + 1)) := ∀ xs : Fin n → M, ∃! x, A (snoc xs x)

end MemStructure.Multiclass


namespace BoundedFormula

@[simp]
def multiclass {n : ℕ} (φ : M.L.BoundedFormula Empty n) : M.Multiclass n :=
  fun xs ↦ φ 〘xs〙

-- def multiclass₀ {n : ℕ} (φ : M.L.BoundedFormula Empty n)
--     : M.Multiclass n :=
--   fun xs ↦ φ 〘xs〙

-- infix:88 " ﹫ " => FirstOrder.Language.BoundedFormula.multiclass

-- scoped[FirstOrder.Language] notation:max
--   φ "〘" vs "++〙" => BoundedFormula.multiclass φ vs

variable {m n l : ℕ} {φ : M.L.BoundedFormula Empty n}
  {vs : Fin m → M}
  {ψ : M.L.BoundedFormula Empty n} {us : Fin l → M}

@[simp]
lemma multiclass_top : (⊤ : M.L.BoundedFormula Empty n).multiclass = (⊤ : M.Multiclass n) := by
  funext
  simp [multiclass]

@[simp]
lemma multiclass_bot : (⊥ : M.L.BoundedFormula Empty n).multiclass = (⊥ : M.Multiclass n) := by
  funext
  simp [multiclass]

@[simp]
lemma multiclass_not : (∼φ).multiclass = ∼φ.multiclass := by
  funext
  simp [multiclass, MemStructure.Multiclass.not]

@[simp]
lemma multiclass_imp : (φ ⟹ ψ).multiclass = φ.multiclass ⟹ ψ.multiclass := by
  funext
  simp [multiclass, MemStructure.Multiclass.imp]

@[simp]
lemma multiclass_all' {φ : M.L.BoundedFormula Empty (n + m)} :
    (φ.all' m).multiclass = (φ.multiclass).all' m := by
  funext
  simp [multiclass, MemStructure.Multiclass.all']

@[simp]
lemma multiclass_all {φ : M.L.BoundedFormula Empty (n + 1)} :
    (∀' φ).multiclass = ∀' (φ.multiclass) := φ.multiclass_all'

@[simp]
lemma multiclass_ex' {φ : M.L.BoundedFormula Empty (n + m)} :
    (φ.ex' m).multiclass = (φ.multiclass).ex' m := by
  funext
  simp [multiclass, MemStructure.Multiclass.ex']

@[simp]
lemma multiclass_ex {φ : M.L.BoundedFormula Empty (n + 1)} :
    (∃' φ).multiclass = ∃' (φ.multiclass) := φ.multiclass_ex'

-- lemma multiclass_slice {φ : M.L.BoundedFormula Empty (m + (n + 1))}
--     (c : M) :
--     (φ.switchBoundRight).castAssoc' 〘snoc vs c ++〙 = (φ 〘vs ++〙).slice c := by
--   funext
--   simp [multiclass, MemStructure.Multiclass.slice, snoc_eq_append]

@[simp]
lemma multiclass_remap {φ : M.L.BoundedFormula Empty n}
    (f : Fin n → Fin n') :
    (φ.substBoundBound f).multiclass = (φ.multiclass).remap f := by
  funext
  simp [multiclass, MemStructure.Multiclass.remap]

variable (i j : Fin n)

@[simp]
lemma multiclass_eq :
    (&i =' &j).multiclass = @MemStructure.Multiclass.Eq M n i j := by
  funext
  simp [multiclass, MemStructure.Multiclass.Eq]

@[simp]
lemma multiclass_mem :
    (&i ∈' &j).multiclass = @MemStructure.Multiclass.Mem M n i j := by
  funext
  simp [multiclass, MemStructure.Multiclass.Mem]

@[simp]
lemma multiclass_subset :
    (&i ⊆' &j).multiclass = @MemStructure.Multiclass.Subset M n i j := by
  funext
  simp [multiclass, MemStructure.Multiclass.Subset]

end BoundedFormula


def MemStructure.Class := M → Prop

namespace MemStructure

namespace Class

@[coe]
def toMulticlass : M.Class → M.Multiclass 1 :=
  (Equiv.funUnique (Fin 1) M).symm.arrowCongr (_root_.Equiv.refl _)

@[coe]
def _root_.FirstOrder.Language.MemStructure.Multiclass.toClass : M.Multiclass 1 → M.Class :=
  (Equiv.funUnique (Fin 1) M).arrowCongr (_root_.Equiv.refl _)

instance : Coe M.Class (M.Multiclass 1) := ⟨toMulticlass⟩

instance : Coe (M.Multiclass 1) M.Class := ⟨Multiclass.toClass⟩

theorem iff_toMulticlass (A : M.Class) (x : M) :
    A x ↔ (A : M.Multiclass 1) ![x] := by
  norm_cast

@[simp, norm_cast]
lemma toClass_toMulticlass (A : M.Class) : ((A : M.Multiclass 1) : M.Class) = A := by norm_cast

@[simp, norm_cast]
lemma _root_.FirstOrder.Language.MemStructure.Multiclass.toMulticlass_toClass (A : M.Multiclass 1) :
    ((A : M.Class) : M.Multiclass 1) = A := by
  funext u
  unfold Multiclass at A
  simp only [toMulticlass, Equiv.arrowCongr, Equiv.coe_refl, _root_.Equiv.symm_symm,
    Equiv.funUnique_apply, default_eq_zero, isValue, Function.id_comp, Equiv.refl_symm,
    Equiv.funUnique_symm_apply, Multiclass.toClass, Equiv.coe_fn_mk, Function.comp_apply]
  congr
  ext i; fin_cases i; rfl

instance : Top (M.Class) := ⟨(⊤ : M.Multiclass 1)⟩

instance : Bot (M.Class) := ⟨(⊥ : M.Multiclass 1)⟩

def inf (A B : M.Class) : M.Class := (A ⊓ B : M.Multiclass 1)

instance : Min (M.Class) := ⟨inf⟩

def sup (A B : M.Class) : M.Class := (A ⊔ B : M.Multiclass 1)

instance : Max (M.Class) := ⟨sup⟩

def not (A : M.Class) : M.Class := (∼A : M.Multiclass 1)

def imp (A B : M.Class) : M.Class := (A ⟹ B : M.Multiclass 1)

def iff (A B : M.Class) : M.Class := (A ⇔ B : M.Multiclass 1)

@[inherit_doc] scoped[FirstOrder] infixr:62 " ⟹ " =>
  FirstOrder.Language.MemStructure.Class.imp
-- input \==>

@[inherit_doc] scoped[FirstOrder] prefix:arg "∼" =>
  FirstOrder.Language.MemStructure.Class.not
-- input \~, the ASCII character ~ has too low precedence

@[inherit_doc] scoped[FirstOrder] infixl:61 " ⇔ " =>
  FirstOrder.Language.MemStructure.Class.iff
-- input \<=>

variable (A B : M.Class) (x : M)

@[simp]
lemma top : (⊤ : M.Class) x := by norm_cast

@[simp]
lemma bot_iff : (⊥ : M.Class) x ↔ False := by norm_cast

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
def Eq (c : M) : M.Class := Multiclass.Eq 2 0 1 |>.slice₀ c

@[simp]
theorem eq_iff (c x : M) : Eq c x ↔ x = c := by norm_cast

/-- The class of `x` with `x ∈ c` -/
def Mem (c : M) : M.Class := Multiclass.Mem 2 0 1 |>.slice₀ c

@[simp]
theorem mem_iff (c x : M) : Mem c x ↔ x ∈ c := by norm_cast

/-- The class of `x` with `x ⊆ c` -/
def Subset (c : M) : M.Class := Multiclass.Subset 2 0 1 |>.slice₀ c

@[simp]
theorem subset_iff (c x : M) : Subset c x ↔ x ⊆ c := by norm_cast

end Class

@[implicit_reducible]
def MulticlassFunction (n) := (Fin n → M) → M

namespace MulticlassFunction

variable {n : ℕ}

@[coe]
def toMulticlass (F : M.MulticlassFunction n) : M.Multiclass (n + 1) :=
  fun xs ↦ F (xs ∘ Fin.castSucc) = xs (Fin.last _)

instance : Coe (M.MulticlassFunction n) (M.Multiclass (n + 1)) := ⟨toMulticlass⟩

@[simp]
theorem toMulticlass_snoc_iff (F : M.MulticlassFunction n) (xs : Fin n → M) (y : M) :
    (F : M.Multiclass (n + 1)) (snoc xs y) ↔ F xs = y := by
  simp [toMulticlass]

variable (F : M.MulticlassFunction n)

-- theorem allExUnique : (F : M.Multiclass (n + 1)).AllExUnique := by
--   simp [Multiclass.AllExUnique]

def proj {n} (i : Fin n) : M.MulticlassFunction n := fun xs ↦ xs i

def comp (F : M.MulticlassFunction l) (Gs : Fin l → M.MulticlassFunction n) :
  M.MulticlassFunction n :=
  fun xs ↦ F (fun i ↦ Gs i xs)

@[simp]
theorem proj_eq {n} (i : Fin n) (xs : Fin n → M) : MulticlassFunction.proj i xs = xs i := by
  simp [proj]

@[norm_cast]
theorem cast_proj {n} (i : Fin n) :
    MulticlassFunction.toMulticlass (M := M) (MulticlassFunction.proj i) =
      Multiclass.Eq (n + 1) (i.castSucc) (Fin.last n) := by
  norm_cast

theorem eq_remap_imp_eq {F : M.MulticlassFunction n} :
    F = ((F : M.Multiclass (n + 1)).remap (snoc (castAdd 2) (last _)) ⟹
      Multiclass.Eq (n + 2) (last _).castSucc (last _)).all := by
  funext xs
  simp only [toMulticlass, Multiclass.all_iff, Multiclass.imp, Multiclass.remap,
    Function.comp_apply, snoc_last, Multiclass.Eq, snoc_castSucc, eq_iff_iff]
  set us := xs ∘ castSucc
  set u := xs (last n)
  have : xs = snoc us u := by rw [← Fin.snoc_init_self xs]; congr
  simp [this, eq_comm]

theorem comp_eq_ex'
  (F : M.MulticlassFunction l) (Gs : Fin l → M.MulticlassFunction n) :
  F.comp Gs =
    ((F : M.Multiclass (l + 1)).remap (snoc (natAdd (n + 1)) ((Fin.last n).castAdd l)) ⊓
      Multiclass.iInf fun i : Fin l ↦ (Gs i : M.Multiclass (n + 1)).remap
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
  (F : M.MulticlassFunction l) (Gs : Fin l → M.MulticlassFunction n) :
  F.comp Gs =
    ((Multiclass.iInf fun i : Fin l ↦ (Gs i : M.Multiclass (n + 1)).remap
    (snoc (castAdd l ∘ castSucc) (i.natAdd (n + 1)))) ⟹
    (F : M.Multiclass (l + 1)).remap (snoc (natAdd (n + 1)) ((Fin.last n).castAdd l))).all' l := by
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

def subst (A : M.Multiclass l) (Gs : Fin l → M.MulticlassFunction n) :
  M.Multiclass n :=
  fun xs ↦ A (fun i ↦ Gs i xs)

theorem subst_eq_remap (A : M.Multiclass n) (f : Fin n → Fin n') :
    A.subst (fun i xs ↦ xs (f i)) = A.remap f := rfl

variable (A : M.Multiclass l) (Gs : Fin l → M.MulticlassFunction n)

theorem subst_eq_ex' :
  A.subst Gs =
    (A.remap (natAdd n) ⊓
    Multiclass.iInf fun i : Fin l ↦ (Gs i : M.Multiclass (n + 1)).remap
    (snoc (castAdd l) (i.natAdd n))).ex' l := by
  funext xs
  simp only [subst, ex', inf_iff, remap, append_comp_natAdd, iInf_iff, append_comp_snoc_castAdd,
    append_right, MulticlassFunction.toMulticlass_snoc_iff, eq_iff_iff]
  exact ⟨by grind, fun ⟨vs, hvs₁, hvs₂⟩ ↦ by simp_rw [hvs₂, hvs₁]⟩

theorem subst_eq_all' :
  A.subst Gs =
    ((Multiclass.iInf fun i : Fin l ↦ (Gs i : M.Multiclass (n + 1)).remap
    (snoc (castAdd l) (i.natAdd n))) ⟹
    A.remap (natAdd n)).all' l := by
  funext xs
  simp only [subst, all', iInf_iff, imp, remap, append_comp_snoc_castAdd, append_right,
    MulticlassFunction.toMulticlass_snoc_iff, append_comp_natAdd, eq_iff_iff]
  exact ⟨fun h vs hvs ↦ by convert h; rw [hvs], by grind⟩

theorem subst_slice_eq_subst (A : M.Multiclass (l + m)) (ys : Fin m → M)
    (Gs : Fin l → M.MulticlassFunction n) :
    (A.slice ys).subst Gs = A.subst (append Gs fun i _ ↦ ys i) := by
  funext zs
  simp only [subst, slice]
  congr
  ext i; cases i using Fin.addCases <;> simp

theorem subst_slice_eq_slice_subst (A : M.Multiclass (l + m)) (ys : Fin m → M)
    (Gs : Fin l → M.MulticlassFunction n) :
    (A.slice ys).subst Gs =
      (A.subst (append (fun i zs ↦ Gs i (fun j ↦ zs (j.castAdd m)))
        (fun i zs ↦ zs (i.natAdd n)))).slice ys := by
  funext ws
  simp only [subst, slice]
  congr
  ext i; cases i using Fin.addCases <;> simp

end Multiclass


namespace Class

def subst (A : M.Class) (G : M.MulticlassFunction n) :
  M.Multiclass n := A ∘ G

theorem subst_eq_subst_toMulticlass (A : M.Class) (G : M.MulticlassFunction n) :
    A.subst G = (A : M.Multiclass 1).subst ![G] := by
  norm_cast

-- theorem subst_eq_remap (A : M.Class) (i : Fin n) :
--     A.subst (MulticlassFunction.proj i) = A.remap  := rfl

end Class

@[implicit_reducible]
def ClassFunction := M → M

namespace ClassFunction

@[coe]
def toMulticlassFunction : M.ClassFunction → M.MulticlassFunction 1 :=
  (Equiv.funUnique (Fin 1) M).symm.arrowCongr (_root_.Equiv.refl _)

instance : Coe (M.ClassFunction) (M.MulticlassFunction 1) := ⟨toMulticlassFunction⟩

theorem eq_toMulticlassFunction (F : M.ClassFunction) (x : M) :
    F x = (F : M.MulticlassFunction 1) ![x] := by
  simp [toMulticlassFunction]

@[coe]
def toMulticlass : M.ClassFunction → M.Multiclass 2 :=
  MulticlassFunction.toMulticlass ∘ toMulticlassFunction

instance : Coe (M.ClassFunction) (M.Multiclass 2) := ⟨toMulticlass⟩

@[simp]
theorem toMulticlass_vec_iff (F : M.ClassFunction) (x y : M) :
    (F : M.Multiclass 2) ![x, y] ↔ F x = y := by
  norm_cast

@[norm_cast, simp]
theorem cast_cast (F : M.ClassFunction) :
    ((F : M.MulticlassFunction 1) : M.Multiclass 2) = (F : M.Multiclass 2) := by
  norm_cast

def comp (F : M.ClassFunction) (G : M.ClassFunction) :
  M.ClassFunction := F ∘ G

@[norm_cast]
theorem cast_comp (F G : M.ClassFunction) :
    (F.comp G : M.MulticlassFunction 1) =
      (F : M.MulticlassFunction 1).comp (fun _ : Fin 1 ↦ G) := by
  norm_cast

end ClassFunction

end FirstOrder.Language.MemStructure
