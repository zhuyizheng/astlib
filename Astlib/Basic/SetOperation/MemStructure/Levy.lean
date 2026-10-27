/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.MemStructure.Defs
import Astlib.Basic.SetOperation.MemStructure.Syntax
import Astlib.Mathlib.ModelTheory.Completeness.DerivedRules
/-!
file docstring
-/

open FirstOrder Language BoundedFormula Theory Fin

variable {L : FirstOrder.Language.{u, v}} [L.HasMem]

namespace FirstOrder

namespace Language

/-- `Δ₀` bounded formulas in `L` -/
inductive DeltaZeroBoundedFormula [L.HasMem] : ℕ → Type max u v
  | falsum {n : ℕ} : DeltaZeroBoundedFormula n
  | equal {n : ℕ} (t₁ t₂ : L.Term' n) : DeltaZeroBoundedFormula n
  | mem {n : ℕ} (t₁ t₂ : L.Term' n) : DeltaZeroBoundedFormula n
  | imp {n : ℕ} (f₁ f₂ : DeltaZeroBoundedFormula n) : DeltaZeroBoundedFormula n
  /-- For all `x ∈ t`, `f` holds with the last bound variable evaluated at `x` -/
  | allMem {n : ℕ} (t : L.Term' n) (f : DeltaZeroBoundedFormula (n + 1)) :
    DeltaZeroBoundedFormula n
  | rel {n : ℕ} (R : L.Relations 1) (t : L.Term' n) :
    DeltaZeroBoundedFormula n

instance : Inhabited (L.DeltaZeroBoundedFormula n) := ⟨DeltaZeroBoundedFormula.falsum⟩

namespace DeltaZeroBoundedFormula

infix:88 " =₀ " => FirstOrder.Language.DeltaZeroBoundedFormula.equal

infix:88 " ∈₀ " => FirstOrder.Language.DeltaZeroBoundedFormula.mem

def not (φ : L.DeltaZeroBoundedFormula n) : L.DeltaZeroBoundedFormula n :=
  φ.imp falsum

def sup (φ ψ : L.DeltaZeroBoundedFormula n) : L.DeltaZeroBoundedFormula n :=
  φ.not.imp ψ

def inf (φ ψ : L.DeltaZeroBoundedFormula n) : L.DeltaZeroBoundedFormula n :=
  (φ.imp ψ.not).not

instance : Max (L.DeltaZeroBoundedFormula n) := ⟨sup⟩

instance : Min (L.DeltaZeroBoundedFormula n) := ⟨inf⟩

def iff (φ ψ : L.DeltaZeroBoundedFormula n) : L.DeltaZeroBoundedFormula n :=
  (φ.imp ψ).inf (ψ.imp φ)

@[inherit_doc] scoped[FirstOrder] infixr:62 " ⟹ " =>
  FirstOrder.Language.DeltaZeroBoundedFormula.imp
-- input \==>

@[inherit_doc] scoped[FirstOrder] prefix:arg "∼" =>
  FirstOrder.Language.DeltaZeroBoundedFormula.not
-- input \~, the ASCII character ~ has too low precedence

@[inherit_doc] scoped[FirstOrder] infixl:61 " ⇔ " =>
  FirstOrder.Language.DeltaZeroBoundedFormula.iff
-- input \<=>

instance : Bot (L.DeltaZeroBoundedFormula n) := ⟨falsum⟩

instance : Top (L.DeltaZeroBoundedFormula n) := ⟨∼falsum⟩

@[inherit_doc, match_pattern] scoped[FirstOrder]
notation "∀₀∈ " x:arg y:50 => FirstOrder.Language.DeltaZeroBoundedFormula.allMem x y

def exMem (t : L.Term' n) (φ : L.DeltaZeroBoundedFormula (n + 1)) :
  L.DeltaZeroBoundedFormula n :=
  ∼(∀₀∈ t ∼φ)

@[inherit_doc, match_pattern] scoped[FirstOrder]
notation "∃₀∈ " x:arg y:50 => FirstOrder.Language.DeltaZeroBoundedFormula.exMem x y

@[elab_as_elim] def neZeroCases
  {n} [NeZero n]
  {motive : ∀ {n}, ∀ [NeZero n], L.DeltaZeroBoundedFormula n → Sort _}
  (falsum : ∀ {n}, ∀ [NeZero n], motive (falsum : L.DeltaZeroBoundedFormula n))
  (equal : ∀ {n}, ∀ [NeZero n], ∀ t₁ t₂ : L.Term' n, motive (t₁ =₀ t₂))
  (mem : ∀ {n}, ∀ [NeZero n], ∀ t₁ t₂ : L.Term' n, motive (t₁ ∈₀ t₂))
  (imp : ∀ {n}, ∀ [NeZero n], ∀ φ₁ φ₂ : L.DeltaZeroBoundedFormula n,
    motive φ₁ → motive φ₂ → motive (φ₁ ⟹ φ₂))
  (allMem : ∀ {n}, ∀ [NeZero n], ∀ t : L.Term' n, ∀ φ : L.DeltaZeroBoundedFormula (n + 1),
    motive φ → motive (∀₀∈t φ))
  (rel : ∀ {n}, ∀ [NeZero n], ∀ R : L.Relations 1, ∀ t : L.Term' n,
    motive (rel R t))
  (φ : L.DeltaZeroBoundedFormula n) :
  motive φ := by
  cases φ with
  | falsum => exact falsum
  | equal => exact equal _ _
  | mem => exact mem _ _
  | imp φ₁ φ₂ =>
    exact imp φ₁ φ₂ (neZeroCases falsum equal mem imp allMem rel φ₁)
      (neZeroCases falsum equal mem imp allMem rel φ₂)
  | allMem t φ =>
    exact allMem t φ (neZeroCases falsum equal mem imp allMem rel φ)
  | rel => exact rel _ _

/-- The depth of bounded quantifiers -/
def depth (φ : L.DeltaZeroBoundedFormula n) : ℕ := match φ with
  | falsum => 0
  | equal _ _ => 0
  | mem _ _ => 0
  | imp φ₁ φ₂ => max φ₁.depth φ₂.depth
  | allMem _ ψ => ψ.depth + 1
  | rel _ _ => 0

/-- Whether `φ` does not have any unary relation symbol -/
def isRelFree (φ : L.DeltaZeroBoundedFormula n) : Prop := match φ with
  | falsum => True
  | equal _ _ => True
  | mem _ _ => True
  | imp φ₁ φ₂ => φ₁.isRelFree ∧ φ₂.isRelFree
  | allMem _ ψ => ψ.isRelFree
  | rel _ _ => False

/-- `φ` does not have any unary relation symbol -/
class RelFree (φ : L.DeltaZeroBoundedFormula n) : Prop where
  relFree : φ.isRelFree

/-- Turn a `Δ₀` formula into a bounded formula -/
@[coe, simp]
def toBoundedFormula (φ : L.DeltaZeroBoundedFormula n) : L.BoundedFormula' n :=
  match φ with
  | falsum => .falsum
  | equal t₁ t₂ => t₁ =' t₂
  | mem t₁ t₂ => t₁ ∈' t₂
  | imp φ₁ φ₂ => φ₁.toBoundedFormula ⟹ φ₂.toBoundedFormula
  | allMem t φ => ∀'∈ t φ.toBoundedFormula
  | rel R t => R.boundedFormula₁ t

instance : Coe (L.DeltaZeroBoundedFormula n) (L.BoundedFormula' n) := ⟨toBoundedFormula⟩

@[simp]
theorem toBoundedFormula_bot :
    (⊥ : L.DeltaZeroBoundedFormula n).toBoundedFormula = ⊥ := rfl

@[simp]
theorem toBoundedFormula_not (φ : L.DeltaZeroBoundedFormula n) :
    (∼φ).toBoundedFormula = ∼φ.toBoundedFormula := rfl

@[simp]
theorem toBoundedFormula_top :
    (⊤ : L.DeltaZeroBoundedFormula n).toBoundedFormula = ⊤ := rfl

@[simp]
theorem toBoundedFormula_sup (φ ψ : L.DeltaZeroBoundedFormula n) :
    (φ ⊔ ψ).toBoundedFormula = φ.toBoundedFormula ⊔ ψ.toBoundedFormula :=
  rfl

@[simp]
theorem toBoundedFormula_sup' (φ ψ : L.DeltaZeroBoundedFormula n) :
    (φ.sup ψ).toBoundedFormula = φ.toBoundedFormula ⊔ ψ.toBoundedFormula :=
  rfl

@[simp]
theorem toBoundedFormula_inf (φ ψ : L.DeltaZeroBoundedFormula n) :
    (φ ⊓ ψ).toBoundedFormula = φ.toBoundedFormula ⊓ ψ.toBoundedFormula :=
  rfl

@[simp]
theorem toBoundedFormula_inf' (φ ψ : L.DeltaZeroBoundedFormula n) :
    (φ.inf ψ).toBoundedFormula = φ.toBoundedFormula ⊓ ψ.toBoundedFormula :=
  rfl

@[simp]
theorem toBoundedFormula_iff (φ ψ : L.DeltaZeroBoundedFormula n) :
    (φ ⇔ ψ).toBoundedFormula = φ.toBoundedFormula ⇔ ψ.toBoundedFormula :=
  rfl

@[simp]
theorem toBoundedFormula_exMem (φ : L.DeltaZeroBoundedFormula (n + 1))
    (t : L.Term' n) :
    (φ.exMem t).toBoundedFormula = ∃'∈ t φ.toBoundedFormula := rfl

def substBound
  {L : Language} [L.HasMem] {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
  (ts : Fin n → L.Term' m) : L.DeltaZeroBoundedFormula m :=
  match φ with
  | .falsum => .falsum
  | .equal t₁ t₂ => .equal (t₁.substBound ts) (t₂.substBound ts)
  | .mem t₁ t₂ => .mem (t₁.substBound ts) (t₂.substBound ts)
  | .imp φ₁ φ₂ => imp (φ₁.substBound ts) (φ₂.substBound ts)
  | .allMem t φ => allMem
      (t.substBound ts)
      (φ.substBound (snoc (fun i ↦ (ts i).castSucc) &(last m)))
  | .rel R t => .rel R (t.substBound ts)

@[simp]
theorem substBound_bot
  (ts : Fin n → L.Term' m) :
  (⊥ : L.DeltaZeroBoundedFormula n).substBound ts = ⊥ := rfl

@[simp]
theorem substBound_falsum
  (ts : Fin n → L.Term' m) :
  (falsum : L.DeltaZeroBoundedFormula n).substBound ts = ⊥ := rfl

@[simp, norm_cast]
theorem coe_substBound
    {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
    (ts : Fin n → L.Term' m) :
    (φ.substBound ts) = (φ : L.BoundedFormula' n).substBound ts := by
  induction φ generalizing m with
  | falsum => norm_cast
  | equal t₁ t₂ => norm_cast
  | mem t₁ t₂ =>
    simp [substBound, toBoundedFormula]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp [substBound, ih₁, ih₂]
  | allMem t ψ ih =>
    simp [substBound, BoundedFormula.allMem, Term.substBoundBound, ih]
  | rel R ts =>
    simp [substBound, toBoundedFormula]

def substBoundBound
  {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
  (f : Fin n → Fin m) : L.DeltaZeroBoundedFormula m :=
  φ.substBound (fun i ↦ &(f i))

@[simp, norm_cast]
theorem coe_substBoundBound
    {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
    (f : Fin n → Fin m) :
    (φ.substBoundBound f) = (φ : L.BoundedFormula' n).substBoundBound f :=
  φ.coe_substBound (fun i ↦ &(f i))

def cast
  {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
  (h : n = m) : L.DeltaZeroBoundedFormula m :=
  φ.substBoundBound (Fin.cast h)

@[simp, norm_cast]
theorem coe_cast
    {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
    (h : n = m) :
    (φ.cast h) = (φ : L.BoundedFormula' n).cast h :=
  φ.coe_substBoundBound (Fin.cast h)

/-- Reassociating the variables -/
def castAssoc' {n p q : ℕ} (φ : L.DeltaZeroBoundedFormula (n + (p + q))) :
    L.DeltaZeroBoundedFormula (n + p + q) :=
  φ.cast (add_assoc n p q).symm

@[simp, norm_cast]
theorem coe_castAssoc' {n p q : ℕ} (φ : L.DeltaZeroBoundedFormula (n + (p + q))) :
    (φ.castAssoc' : L.BoundedFormula' (n + p + q)) = (φ : L.BoundedFormula' _).castAssoc' :=
  φ.coe_cast _

/-- Swapping the last two blocks of variables -/
def switchBoundRight {n p q : ℕ} (φ : L.DeltaZeroBoundedFormula (n + (p + q))) :
    L.DeltaZeroBoundedFormula (n + (q + p)) :=
  φ.substBoundBound (append (castAdd (q + p)) (natAdd n ∘ ((append (natAdd q) (castAdd p)))))

@[simp, norm_cast]
theorem coe_switchBoundRight {n p q : ℕ} (φ : L.DeltaZeroBoundedFormula (n + (p + q))) :
    (φ.switchBoundRight : L.BoundedFormula' (n + (q + p))) =
      (φ : L.BoundedFormula' _).switchBoundRight :=
  φ.coe_substBoundBound _

@[simp]
theorem depth_falsum :
    (falsum : L.DeltaZeroBoundedFormula n).depth = 0 := by
  simp [depth]

@[simp]
theorem depth_bot :
    (⊥ : L.DeltaZeroBoundedFormula n).depth = 0 := by
  simp [depth]

@[simp]
theorem depth_eq (t₁ t₂ : L.Term' n) :
    (t₁ =₀ t₂).depth = 0 := by
  simp [depth]

@[simp]
theorem depth_mem (t₁ t₂ : L.Term' n) :
    (t₁ ∈₀ t₂).depth = 0 := by
  simp [depth]

@[simp]
theorem depth_rel (R : L.Relations 1) (t : L.Term' n) :
    (rel R t).depth = 0 := by
  simp [depth]

variable (φ φ₁ φ₂ : L.DeltaZeroBoundedFormula n)

@[simp]
theorem depth_imp :
    (φ₁ ⟹ φ₂).depth = max φ₁.depth φ₂.depth := by
  simp [depth]

@[simp]
theorem depth_not :
    (∼φ).depth = φ.depth := by
  simp [not]

@[simp]
theorem depth_sup :
    (φ₁ ⊔ φ₂).depth = max φ₁.depth φ₂.depth := by
  simp only [depth, max, sup, not]
  grind

@[simp]
theorem depth_inf :
    (φ₁ ⊓ φ₂).depth = max φ₁.depth φ₂.depth := by
  simp [min, inf, not]

@[simp]
theorem depth_iff :
    (φ₁ ⇔ φ₂).depth = max φ₁.depth φ₂.depth := by
  simp only [depth, iff, inf, not]
  grind

@[simp]
theorem depth_top :
    (⊤ : L.DeltaZeroBoundedFormula n).depth = 0 := by
  simp [Top.top]

@[simp]
theorem depth_allMem (t : L.Term' n) (ψ : L.DeltaZeroBoundedFormula (n + 1)) :
    (∀₀∈t ψ).depth = ψ.depth + 1 := by
  simp [depth]

@[simp]
theorem depth_exMem (t : L.Term' n) (ψ : L.DeltaZeroBoundedFormula (n + 1)) :
    (∃₀∈t ψ).depth = ψ.depth + 1 := by
  simp [exMem]

@[simp]
theorem depth_substBound
    {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
    (ts : Fin n → L.Term' m) :
    (φ.substBound ts).depth = φ.depth := by
  induction φ generalizing m with
  | falsum => simp
  | equal t₁ t₂ => simp [substBound]
  | mem t₁ t₂ => simp [substBound]
  | imp φ₁ φ₂ ih₁ ih₂ => simp [substBound, ih₁, ih₂]
  | allMem t ψ ih => simp [substBound, Term.substBoundBound, ih]
  | rel R ts => simp [substBound]

@[simp]
theorem depth_substBoundBound
    {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
    (f : Fin n → Fin m) :
    (φ.substBoundBound f).depth = φ.depth :=
  depth_substBound _ _

@[simp]
theorem depth_cast
    {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
    (h : n = m) :
    (φ.cast h).depth = φ.depth :=
  depth_substBound _ _

theorem relFree_iff_isRelFree (φ : L.DeltaZeroBoundedFormula n) :
    φ.RelFree ↔ φ.isRelFree :=
  ⟨fun h ↦ h.relFree, fun h ↦ ⟨h⟩⟩

instance : (falsum : L.DeltaZeroBoundedFormula n).RelFree := ⟨trivial⟩

instance : (⊥ : L.DeltaZeroBoundedFormula n).RelFree := ⟨trivial⟩

instance (t₁ t₂ : L.Term' n) : (t₁ =₀ t₂).RelFree := ⟨trivial⟩

instance (t₁ t₂ : L.Term' n) : (t₁ ∈₀ t₂).RelFree := ⟨trivial⟩

@[simp]
theorem not_relFree_rel (R : L.Relations 1) (t : L.Term' n) :
    ¬(rel R t).RelFree := by
  simp [relFree_iff_isRelFree, isRelFree]

variable (φ φ₁ φ₂ : L.DeltaZeroBoundedFormula n)

theorem relFree_imp_iff :
    (φ₁ ⟹ φ₂).RelFree ↔ φ₁.RelFree ∧ φ₂.RelFree := by
  simp [relFree_iff_isRelFree, isRelFree]

instance [φ₁.RelFree] [φ₂.RelFree] : (φ₁ ⟹ φ₂).RelFree := by
  simp only [relFree_imp_iff]
  exact ⟨inferInstance, inferInstance⟩

/-- If `φ₁ ⟹ φ₂` is relation-free, then so is `φ₁` -/
theorem RelFree.of_imp_left [h : (φ₁ ⟹ φ₂).RelFree] : φ₁.RelFree := by
  simp only [relFree_imp_iff] at h
  exact h.left

/-- If `φ₁ ⟹ φ₂` is relation-free, then so is `φ₂` -/
theorem RelFree.of_imp_right [h : (φ₁ ⟹ φ₂).RelFree] : φ₂.RelFree := by
  simp only [relFree_imp_iff] at h
  exact h.right

instance [φ.RelFree] : (∼φ).RelFree := by
  unfold not; infer_instance

instance [φ₁.RelFree] [φ₂.RelFree] : (φ₁ ⊔ φ₂).RelFree := by
  show (sup φ₁ φ₂).RelFree
  unfold sup; infer_instance

instance [φ₁.RelFree] [φ₂.RelFree] : (φ₁ ⊓ φ₂).RelFree := by
  show (inf φ₁ φ₂).RelFree
  unfold inf; infer_instance

instance [φ₁.RelFree] [φ₂.RelFree] : (φ₁ ⇔ φ₂).RelFree := by
  unfold iff inf; infer_instance

instance : (⊤ : L.DeltaZeroBoundedFormula n).RelFree := by
  show (∼(falsum : L.DeltaZeroBoundedFormula n)).RelFree
  infer_instance

theorem relFree_allMem_iff (t : L.Term' n) (ψ : L.DeltaZeroBoundedFormula (n + 1)) :
    (∀₀∈t ψ).RelFree ↔ ψ.RelFree := by
  simp [relFree_iff_isRelFree, isRelFree]

instance (t : L.Term' n) (ψ : L.DeltaZeroBoundedFormula (n + 1)) [ψ.RelFree] :
  (∀₀∈t ψ).RelFree := by
  simp only [relFree_allMem_iff]
  exact inferInstance

/-- If `∀₀∈ t ψ` is relation-free, then so is `ψ` -/
theorem RelFree.of_allMem (t : L.Term' n) (ψ : L.DeltaZeroBoundedFormula (n + 1))
    [h : (∀₀∈ t ψ).RelFree] : ψ.RelFree := by
  rwa [relFree_allMem_iff] at h

/-- Induction on a relation-free formula, which has no `rel` case -/
@[elab_as_elim] def relFreeCases
    {motive : ∀ {n}, ∀ {φ : L.DeltaZeroBoundedFormula n}, φ.RelFree → Sort _}
    (falsum : ∀ {n}, ∀ h : (falsum : L.DeltaZeroBoundedFormula n).RelFree, motive h)
    (equal : ∀ {n}, ∀ t₁ t₂ : L.Term' n, ∀ h : (t₁ =₀ t₂).RelFree, motive h)
    (mem : ∀ {n}, ∀ t₁ t₂ : L.Term' n, ∀ h : (t₁ ∈₀ t₂).RelFree, motive h)
    (imp : ∀ {n}, ∀ φ₁ φ₂ : L.DeltaZeroBoundedFormula n, ∀ h₁ : φ₁.RelFree, ∀ h₂ : φ₂.RelFree,
      ∀ h : (φ₁ ⟹ φ₂).RelFree, motive h₁ → motive h₂ → motive h)
    (allMem : ∀ {n}, ∀ t : L.Term' n, ∀ ψ : L.DeltaZeroBoundedFormula (n + 1), ∀ hψ : ψ.RelFree,
      ∀ h : (∀₀∈ t ψ).RelFree, motive hψ → motive h)
    {n} {φ : L.DeltaZeroBoundedFormula n} (h : φ.RelFree) :
    motive h := by
  cases φ with
  | falsum => exact falsum h
  | equal => exact equal _ _ h
  | mem => exact mem _ _ h
  | imp φ₁ φ₂ =>
    have h₁ : φ₁.RelFree := RelFree.of_imp_left φ₁ φ₂
    have h₂ : φ₂.RelFree := RelFree.of_imp_right φ₁ φ₂
    exact imp _ _ h₁ h₂ h (relFreeCases falsum equal mem imp allMem h₁)
      (relFreeCases falsum equal mem imp allMem h₂)
  | allMem t ψ =>
    have hψ : ψ.RelFree := RelFree.of_allMem t ψ
    exact allMem _ _ hψ h (relFreeCases falsum equal mem imp allMem hψ)
  | rel R t => simp at h

instance (t : L.Term' n) (ψ : L.DeltaZeroBoundedFormula (n + 1)) [ψ.RelFree] :
  (∃₀∈t ψ).RelFree := by
  unfold exMem; infer_instance

@[simp]
theorem isRelFree_substBound
    {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
    (ts : Fin n → L.Term' m) :
    (φ.substBound ts).isRelFree ↔ φ.isRelFree := by
  induction φ generalizing m with
  | falsum => simp [substBound, isRelFree]
  | equal t₁ t₂ => simp [substBound, isRelFree]
  | mem t₁ t₂ => simp [substBound, isRelFree]
  | imp φ₁ φ₂ ih₁ ih₂ => simp [substBound, isRelFree, ih₁, ih₂]
  | allMem t ψ ih => simp [substBound, isRelFree, ih]
  | rel R ts => simp [substBound, isRelFree]

theorem relFree_substBound_iff
    {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
    (ts : Fin n → L.Term' m) :
    (φ.substBound ts).RelFree ↔ φ.RelFree := by
  simp [relFree_iff_isRelFree]

instance {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n) [φ.RelFree] (ts : Fin n → L.Term' m) :
  (φ.substBound ts).RelFree := by
  simp only [relFree_substBound_iff]
  exact inferInstance

instance {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n) [φ.RelFree] (f : Fin n → Fin m) :
  (φ.substBoundBound f).RelFree := by
  unfold substBoundBound; infer_instance

instance {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n) [φ.RelFree] (h : n = m) :
  (φ.cast h).RelFree := by
  unfold cast; infer_instance


-- @[simp]
-- theorem toBoundedFormula_realize (φ : M.L.DeltaZeroBoundedFormula n)
--     (xs : Fin n → M) :
--     (φ.exMem t).toBoundedFormula = ∃₀∈ t φ.toBoundedFormula := rfl



-- def substBound {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
--     (ts : Fin n → L.Term' m) : L.DeltaZeroBoundedFormula m :=
--   match φ with
--   | falsum => falsum
--   | equal t₁ t₂ => equal (t₁.substBound ts) (t₂.substBound ts)
--   | mem t₁ t₂ => mem (t₁.substBound ts) (t₂.substBound ts)
--   | imp φ₁ φ₂ => imp (φ₁.substBound ts) (φ₂.substBound ts)
--   | allMem t φ =>
--     ∀₀∈ (t.substBound ts) (φ.substBound (snoc (fun i ↦ (ts i).castSucc) &-1))
--   | rel R t => rel R (t.substBound ts)

-- def substBoundBound {n m : ℕ} (φ : L.DeltaZeroBoundedFormula n)
--     (f : Fin n → Fin m) : L.DeltaZeroBoundedFormula m := φ.substBound (fun i ↦ &(f i))

end DeltaZeroBoundedFormula

namespace BoundedFormula

variable {n : ℕ}

section SyntacticalLevyHierarchy

/-- A bounded formula is `Δ₀` -/
def IsDeltaZero (φ : L.BoundedFormula' n) := ∃ ψ : L.DeltaZeroBoundedFormula n, φ = ψ

/-- A bounded formula is `Δ₀` -/
class DeltaZero (φ : L.BoundedFormula' n) where
  isDeltaZero : IsDeltaZero φ

instance (φ : L.DeltaZeroBoundedFormula n) : φ.toBoundedFormula.DeltaZero := ⟨φ, rfl⟩

mutual
/-- `φ : L.BoundedFormula' n` is said to be a `Π k` formula, denoted by `φ.IsPi k`,
if:
1. if `k = 0`, then `φ.IsDeltaZero`
2. if `k = k' + 1`, then `φ = all' m ψ` where `ψ : L.BoundedFormula' (n + m)` and `ψ.IsSigma k'`
-/
  inductive IsPi : ∀ {n : ℕ}, L.BoundedFormula' n → ℕ → Prop
    | zero {n : ℕ} {φ : L.BoundedFormula' n} (hφ : φ.IsDeltaZero) : φ.IsPi 0
    | succ (m : ℕ) {n k : ℕ} {φ : L.BoundedFormula' (n + m)} (hφ : φ.IsSigma k) :
      (φ.all' m).IsPi (k + 1)

/-- `φ : L.BoundedFormula' n` is said to be a `∑ k` formula, denoted by `φ.IsSigma k`,
if:
1. if `k = 0`, then `φ.IsDeltaZero`
2. if `k = k' + 1`, then `φ = ex' m ψ` where `ψ : L.BoundedFormula' (n + m)` and `ψ.IsPi k'`
-/
  inductive IsSigma : ∀ {n : ℕ}, L.BoundedFormula' n → ℕ → Prop
    | zero {n : ℕ} {φ : L.BoundedFormula' n} (hφ : φ.IsDeltaZero) : φ.IsSigma 0
    | succ (m : ℕ) {n k : ℕ} {φ : L.BoundedFormula' (n + m)} (hφ : φ.IsPi k) :
      (φ.ex' m).IsSigma (k + 1)
end

variable {k n m n' p l : ℕ} {φ ψ : L.BoundedFormula' n}

@[simp]
theorem isDeltaZero_falsum : (falsum : L.BoundedFormula' n).IsDeltaZero :=
  ⟨.falsum, rfl⟩

@[simp]
theorem isDeltaZero_equal (t₁ t₂ : L.Term' n) :
    (t₁ =' t₂).IsDeltaZero :=
  ⟨.equal t₁ t₂, rfl⟩

@[simp]
theorem isDeltaZero_mem (t₁ t₂ : L.Term' n) :
    (t₁ ∈' t₂).IsDeltaZero :=
  ⟨.mem t₁ t₂, rfl⟩

@[simp]
theorem isDeltaZero_rel (R : L.Relations 1) (t : L.Term' n) :
    (rel R ![t]).IsDeltaZero :=
  ⟨.rel R t, rfl⟩

@[simp]
theorem isDeltaZero_bot : (⊥ : L.BoundedFormula' n).IsDeltaZero := by
  simp [Bot.bot]

@[simp]
theorem IsDeltaZero.imp (hφ : φ.IsDeltaZero) (hψ : ψ.IsDeltaZero) :
    (φ ⟹ ψ : L.BoundedFormula' n).IsDeltaZero := by
  obtain ⟨φ', rfl⟩ := hφ
  obtain ⟨ψ', rfl⟩ := hψ
  exact ⟨.imp φ' ψ', by norm_cast⟩

@[simp]
theorem IsDeltaZero.allMem {φ : L.BoundedFormula' (n + 1)} (hφ : φ.IsDeltaZero)
    (t : L.Term' n) :
    (∀'∈ t φ).IsDeltaZero := by
  obtain ⟨φ', rfl⟩ := hφ
  exact ⟨DeltaZeroBoundedFormula.allMem t φ', by norm_cast⟩

@[simp]
theorem IsDeltaZero.not (h : φ.IsDeltaZero) : (∼φ).IsDeltaZero :=
  h.imp isDeltaZero_falsum

@[simp]
theorem isDeltaZero_top : (⊤ : L.BoundedFormula' n).IsDeltaZero := by
  simp [Top.top]

@[simp]
theorem IsDeltaZero.not_iff : (∼φ).IsDeltaZero ↔ φ.IsDeltaZero := by
  refine ⟨?_, IsDeltaZero.not⟩
  rintro ⟨(_ | _ | _ | ⟨φ₁, φ₂⟩ | _), h₁⟩
  · norm_cast at h₁
  · norm_cast at h₁
  · norm_cast at h₁
  · simp [BoundedFormula.not] at h₁
    exact ⟨φ₁, h₁.left⟩
  · norm_cast at h₁
  · norm_cast at h₁

theorem IsDeltaZero.sup (hφ : φ.IsDeltaZero) (hψ : ψ.IsDeltaZero) : (φ ⊔ ψ).IsDeltaZero :=
  hφ.not.imp hψ

theorem IsDeltaZero.foldr_sup {f : List (L.BoundedFormula' n)}
    (hf : ∀ φ ∈ f, φ.IsDeltaZero) :
    (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ f).IsDeltaZero := by
  induction f with
  | nil => simp
  | cons ψ f ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hf
    exact hf.left.sup (ih (hf.right))

theorem isDeltaZero_iSup [Finite β] {f : β → L.BoundedFormula' n} (hf : ∀ i, (f i).IsDeltaZero) :
    (iSup f).IsDeltaZero := by
  simp only [BoundedFormula.iSup]
  grind [IsDeltaZero.foldr_sup]

theorem IsDeltaZero.inf (hφ : φ.IsDeltaZero) (hψ : ψ.IsDeltaZero) : (φ ⊓ ψ).IsDeltaZero :=
  hφ.imp hψ.not |>.not

theorem IsDeltaZero.foldr_inf {f : List (L.BoundedFormula' n)}
    (hf : ∀ φ ∈ f, φ.IsDeltaZero) :
    (List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ f).IsDeltaZero := by
  induction f with
  | nil => simp
  | cons ψ f ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hf
    exact hf.left.inf (ih (hf.right))

theorem isDeltaZero_iInf [Finite β] {f : β → L.BoundedFormula' n} (hf : ∀ i, (f i).IsDeltaZero) :
    (iInf f).IsDeltaZero := by
  simp only [BoundedFormula.iInf]
  grind [IsDeltaZero.foldr_inf]

theorem IsDeltaZero.iff (hφ : φ.IsDeltaZero) (hψ : ψ.IsDeltaZero) : (φ ⇔ ψ).IsDeltaZero :=
  (hφ.imp hψ).inf (hψ.imp hφ)

@[simp]
theorem pi_zero_iff_deltaZero : φ.IsPi 0 ↔ φ.IsDeltaZero := by grind [IsPi]

@[simp]
theorem sigma_zero_iff_deltaZero : φ.IsSigma 0 ↔ φ.IsDeltaZero := by grind [IsSigma]

theorem IsPi.ex' {φ : L.BoundedFormula' (n + m)} (h : φ.IsPi k) :
    (φ.ex' m).IsSigma (k + 1) := IsSigma.succ m h

theorem IsPi.ex {φ : L.BoundedFormula' (n + 1)} (h : φ.IsPi k) :
    (∃' φ).IsSigma (k + 1) := IsSigma.succ 1 h

theorem IsPi.isSigma_succ (h : φ.IsPi k) : φ.IsSigma (k + 1) := IsSigma.succ 0 h

theorem IsSigma.all' {φ : L.BoundedFormula' (n + m)} (h : φ.IsSigma k) :
    (φ.all' m).IsPi (k + 1) := IsPi.succ m h

theorem IsSigma.all {φ : L.BoundedFormula' (n + 1)} (h : φ.IsSigma k) :
    (∀' φ).IsPi (k + 1) := IsPi.succ 1 h

theorem IsSigma.isPi_succ (h : φ.IsSigma k) : φ.IsPi (k + 1) := IsPi.succ 0 h

theorem IsPi.exists_Sigma_all' (h : φ.IsPi (k + 1)) :
    ∃ (m : ℕ), ∃ ψ : L.BoundedFormula' (n + m), ψ.IsSigma k ∧ φ = ψ.all' m := by
  cases h with | succ m hψ
  exact ⟨m, _, hψ, rfl⟩

theorem IsSigma.exists_Pi_ex' (h : φ.IsSigma (k + 1)) :
    ∃ (m : ℕ), ∃ ψ : L.BoundedFormula' (n + m), ψ.IsPi k ∧ φ = ψ.ex' m := by
  cases h with | succ m hψ
  exact ⟨m, _, hψ, rfl⟩

/-- If `φ` is `DeltaZero`, then `φ.substBound ts` is `DeltaZero` -/
theorem IsDeltaZero.substBound (h : φ.IsDeltaZero) (ts : Fin n → L.Term' m) :
    (φ.substBound ts).IsDeltaZero := by
  obtain ⟨φ', rfl⟩ := h
  use φ'.substBound ts
  norm_cast

/-- If `φ` is `DeltaZero`, then `φ.substBoundBound f` is `DeltaZero` -/
theorem IsDeltaZero.substBoundBound (h : φ.IsDeltaZero) (f : Fin n → Fin m) :
    (φ.substBoundBound f).IsDeltaZero :=
  h.substBound _

/-- If `φ` is `DeltaZero`, then `φ.cast h` is `DeltaZero` -/
theorem IsDeltaZero.cast (h : φ.IsDeltaZero) (hnm : n = m) :
    (φ.cast hnm).IsDeltaZero :=
  h.substBoundBound _

mutual
theorem IsPi.substBound {k n l : ℕ} {φ : L.BoundedFormula' n} (h : φ.IsPi k)
    (ts : Fin n → L.Term' l) :
    (φ.substBound ts).IsPi k :=
  match k with
  | 0 => by
    simp only [pi_zero_iff_deltaZero] at h ⊢
    exact h.substBound _
  | k + 1 => by
    obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Sigma_all'
    simp only [hψ₂, substBound_all'_eq_all'_substBound]
    exact hψ₁.substBound _ |>.all'

theorem IsSigma.substBound {k n l : ℕ} {φ : L.BoundedFormula' n} (h : φ.IsSigma k)
    (ts : Fin n → L.Term' l) :
    (φ.substBound ts).IsSigma k :=
  match k with
  | 0 => by
    simp only [sigma_zero_iff_deltaZero] at h ⊢
    exact h.substBound _
  | k + 1 => by
    obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Pi_ex'
    simp only [hψ₂, substBound_ex'_eq_ex'_substBound]
    exact hψ₁.substBound _ |>.ex'
end

theorem IsPi.all' {φ : L.BoundedFormula' (n + m)} (h : φ.IsPi (k + 1)) :
    (φ.all' m).IsPi (k + 1) := by
  obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Sigma_all'
  rw [hψ₂, ψ.all'_all'_eq_all'_cast]
  exact (hψ₁.substBound _).all'

theorem IsPi.all {φ : L.BoundedFormula' (n + 1)} (h : φ.IsPi (k + 1)) :
    φ.all.IsPi (k + 1) := h.all'

theorem IsSigma.ex' {φ : L.BoundedFormula' (n + m)} (h : φ.IsSigma (k + 1)) :
    (φ.ex' m).IsSigma (k + 1) := by
  obtain ⟨m, ψ, hψ₁, hψ₂⟩ := h.exists_Pi_ex'
  rw [hψ₂, ψ.ex'_ex'_eq_ex'_cast]
  exact (hψ₁.substBound _).ex'

theorem IsSigma.ex {φ : L.BoundedFormula' (n + 1)} (h : φ.IsSigma (k + 1)) :
    φ.ex.IsSigma (k + 1) := h.ex'

mutual
theorem IsPi.isPi_succ {k n : ℕ} {φ : L.BoundedFormula' n} (h : φ.IsPi k) :
    φ.IsPi (k + 1) :=
  match k with
  | 0 => IsSigma.isPi_succ (by simpa using h)
  | k + 1 => by
    obtain ⟨_, _, hψ, _⟩ := h.exists_Sigma_all'
    convert hψ.isSigma_succ.all'

theorem IsSigma.isSigma_succ {k n : ℕ} {φ : L.BoundedFormula' n} (h : φ.IsSigma k) :
    φ.IsSigma (k + 1) :=
  match k with
  | 0 => IsPi.isSigma_succ (by simpa using h)
  | k + 1 => by
    obtain ⟨_, _, hψ, _⟩ := h.exists_Pi_ex'
    convert hψ.isPi_succ.ex'
end

variable {φ : L.BoundedFormula' n} {ts : Fin n → L.Term' m}

theorem IsPi.isPi_of_le (h : φ.IsPi k) (hkm : k ≤ m) : φ.IsPi m := by
  induction m with
  | zero => grind
  | succ m ih =>
    rcases lt_or_eq_of_le hkm with hkm | rfl
    · exact ih (Nat.le_of_lt_succ hkm) |>.isPi_succ
    · exact h

theorem IsSigma.isSigma_of_le (h : φ.IsSigma k) (hkm : k ≤ m) : φ.IsSigma m := by
  induction m with
  | zero => convert h; omega
  | succ m ih =>
    rcases lt_or_eq_of_le hkm with hkm | rfl
    · exact ih (Nat.le_of_lt_succ hkm) |>.isSigma_succ
    · exact h

theorem IsPi.Sigma_of_lt (h : φ.IsPi k) (hkm : k < m) : φ.IsSigma m :=
  h.isSigma_succ.isSigma_of_le (Nat.add_one_le_of_lt hkm)

theorem IsSigma.Pi_of_lt (h : φ.IsSigma k) (hkm : k < m) : φ.IsPi m :=
  h.isPi_succ.isPi_of_le (Nat.add_one_le_of_lt hkm)


instance : (⊥ : L.BoundedFormula' n).DeltaZero := ⟨isDeltaZero_falsum⟩

instance (t₁ t₂ : L.Term' n) : (t₁ =' t₂).DeltaZero := ⟨isDeltaZero_equal _ _⟩

instance (t₁ t₂ : L.Term' n) :
  (t₁ ∈' t₂).DeltaZero := ⟨isDeltaZero_mem _ _⟩

instance [hφ : φ.DeltaZero] [hψ : ψ.DeltaZero] : (φ ⟹ ψ).DeltaZero :=
  ⟨hφ.isDeltaZero.imp hψ.isDeltaZero⟩

instance {φ : L.BoundedFormula' (n + 1)} [hφ : φ.DeltaZero]
  (t : L.Term' n) : (∀'∈ t φ).DeltaZero :=
  ⟨hφ.isDeltaZero.allMem t⟩

instance (R : L.Relations 1)
  (t : L.Term' n) :
  (R.boundedFormula₁ t).DeltaZero := ⟨isDeltaZero_rel _ _⟩

instance [hφ : φ.DeltaZero] : (∼φ).DeltaZero := ⟨hφ.isDeltaZero.not⟩

instance : (⊤ : L.BoundedFormula' n).DeltaZero := ⟨DeltaZero.isDeltaZero.not⟩

instance [hφ : φ.DeltaZero] [hψ : ψ.DeltaZero] : (φ ⊔ ψ).DeltaZero :=
  ⟨hφ.isDeltaZero.not.imp hψ.isDeltaZero⟩

instance [Finite β] {f : β → L.BoundedFormula' n} [hf : ∀ i, (f i).DeltaZero] :
  (iSup f).DeltaZero :=
  ⟨isDeltaZero_iSup (fun i ↦ (hf i).isDeltaZero)⟩

instance [hφ : φ.DeltaZero] [hψ : ψ.DeltaZero] : (φ ⊓ ψ).DeltaZero :=
  ⟨hφ.isDeltaZero.imp hψ.isDeltaZero.not |>.not⟩

instance [Finite β] {f : β → L.BoundedFormula' n} [hf : ∀ i, (f i).DeltaZero] :
  (iInf f).DeltaZero :=
  ⟨isDeltaZero_iInf (fun i ↦ (hf i).isDeltaZero)⟩

instance [hφ : φ.DeltaZero] [hψ : ψ.DeltaZero] : (φ ⇔ ψ).DeltaZero :=
  ⟨(hφ.isDeltaZero.imp hψ.isDeltaZero).inf (hψ.isDeltaZero.imp hφ.isDeltaZero)⟩

instance {φ : L.BoundedFormula' (n + 1)} [hφ : φ.DeltaZero]
  (t : L.Term' n) : (∃'∈ t φ).DeltaZero := ⟨(hφ.isDeltaZero.not.allMem t).not⟩

class Pi (k : ℕ) (φ : L.BoundedFormula' n) : Prop where
  isPi : φ.IsPi k

class Sigma (k : ℕ) (φ : L.BoundedFormula' n) : Prop where
  isSigma : φ.IsSigma k

instance [hφ : φ.DeltaZero] : φ.Pi 0 := ⟨by simpa using hφ.isDeltaZero⟩

instance [hφ : φ.DeltaZero] : φ.Sigma 0 := ⟨by simpa using hφ.isDeltaZero⟩

instance {φ : L.BoundedFormula' (n + m)} [hφ : φ.Pi k] :
  (φ.ex' m).Sigma (k + 1) := ⟨by simpa using hφ.isPi.ex'⟩

instance {φ : L.BoundedFormula' (n + 1)} [hφ : φ.Pi k] :
  φ.ex.Sigma (k + 1) := ⟨by simpa using hφ.isPi.ex⟩

instance {φ : L.BoundedFormula' (n + 1)} [hφ : φ.Pi k] :
  φ.Sigma (k + 1) := ⟨by simpa using hφ.isPi.isSigma_succ⟩

instance {φ : L.BoundedFormula' (n + m)} [hφ : φ.Sigma k] :
  (φ.all' m).Pi (k + 1) := ⟨by simpa using hφ.isSigma.all'⟩

instance {φ : L.BoundedFormula' (n + 1)} [hφ : φ.Sigma k] :
  φ.all.Pi (k + 1) := ⟨by simpa using hφ.isSigma.all⟩

instance {φ : L.BoundedFormula' (n + 1)} [hφ : φ.Sigma k] :
  φ.Pi (k + 1) := ⟨by simpa using hφ.isSigma.isPi_succ⟩

-- instance [h : φ.DeltaZero] (h' : n = n') : (φ.cast h').DeltaZero := ⟨h.isDeltaZero.cast h'⟩

instance {φ : L.BoundedFormula' n} [h : φ.DeltaZero] :
  (φ.substBound ts).DeltaZero := ⟨h.isDeltaZero.substBound ts⟩

instance {φ : L.BoundedFormula' n} [h : φ.DeltaZero] :
  (φ.substBoundBound f).DeltaZero := ⟨h.isDeltaZero.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.DeltaZero] (h' : n = n') :
  (φ.cast h').DeltaZero := ⟨h.isDeltaZero.substBound _⟩

instance {φ : L.BoundedFormula' (n + p)} {ψ : L.BoundedFormula' (n + q)} [hφ : φ.DeltaZero]
  [hψ : ψ.DeltaZero] : (φ.splitImp ψ).DeltaZero := ⟨
  (hφ.isDeltaZero.substBound _).imp (hψ.isDeltaZero.substBound _)⟩

instance {φ : L.BoundedFormula' (n + p)} [hφ : φ.DeltaZero] : (φ.switchBound).DeltaZero :=
  ⟨hφ.isDeltaZero.substBound _⟩

instance {φ : L.BoundedFormula' (n + p + q)} [hφ : φ.DeltaZero] : (φ.castAssoc).DeltaZero :=
  ⟨hφ.isDeltaZero.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.DeltaZero] : (φ.castAssoc').DeltaZero :=
  ⟨hφ.isDeltaZero.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.DeltaZero] :
  (φ.switchBoundRight).DeltaZero :=
  ⟨hφ.isDeltaZero.substBound _⟩

instance {φ : L.BoundedFormula' (p + n)} {ψ : L.BoundedFormula' (q + n)} [hφ : φ.DeltaZero]
  [hψ : ψ.DeltaZero] : (φ.splitImp' ψ).DeltaZero := by rw [splitImp']; infer_instance

instance {φ : L.BoundedFormula' n} [h : φ.Pi k] :
  (φ.substBound ts).Pi k := ⟨h.isPi.substBound ts⟩

instance {φ : L.BoundedFormula' n} [h : φ.Pi k] :
  (φ.substBoundBound f).Pi k := ⟨h.isPi.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.Pi k] (h' : n = n') :
  (φ.cast h').Pi k := ⟨h.isPi.substBound _⟩

-- instance {φ : L.BoundedFormula' (n + p)} {ψ : L.BoundedFormula' (n + q)} [hφ : φ.Sigma k]
--   [hψ : ψ.Pi k] : (φ.splitImp ψ).Pi k := ⟨
--   (hφ.isSigma.substBound _).imp (hψ.isPi.substBound _)⟩

instance {φ : L.BoundedFormula' (n + p)} [hφ : φ.Pi k] : (φ.switchBound).Pi k :=
  ⟨hφ.isPi.substBound _⟩

instance {φ : L.BoundedFormula' (n + p + q)} [hφ : φ.Pi k] : (φ.castAssoc).Pi k :=
  ⟨hφ.isPi.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.Pi k] : (φ.castAssoc').Pi k :=
  ⟨hφ.isPi.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.Pi k] :
  (φ.switchBoundRight).Pi k :=
  ⟨hφ.isPi.substBound _⟩

-- instance {φ : L.BoundedFormula' (p + n)} {ψ : L.BoundedFormula' (q + n)} [hφ : φ.Pi k]
--   [hψ : ψ.Pi k] : (φ.splitImp' ψ).Pi k := by rw [splitImp']; infer_instance

instance {φ : L.BoundedFormula' n} [h : φ.Sigma k] :
  (φ.substBound ts).Sigma k := ⟨h.isSigma.substBound ts⟩

instance {φ : L.BoundedFormula' n} [h : φ.Sigma k] :
  (φ.substBoundBound f).Sigma k := ⟨h.isSigma.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.Sigma k] (h' : n = n') :
  (φ.cast h').Sigma k := ⟨h.isSigma.substBound _⟩

-- instance {φ : L.BoundedFormula' (n + p)} {ψ : L.BoundedFormula' (n + q)} [hφ : φ.Sigma k]
--   [hψ : ψ.Sigma k] : (φ.splitImp ψ).Sigma k := ⟨
--   (hφ.isSigma.substBound _).imp (hψ.isSigma.substBound _)⟩

instance {φ : L.BoundedFormula' (n + p)} [hφ : φ.Sigma k] : (φ.switchBound).Sigma k :=
  ⟨hφ.isSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + p + q)} [hφ : φ.Sigma k] : (φ.castAssoc).Sigma k :=
  ⟨hφ.isSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.Sigma k] : (φ.castAssoc').Sigma k :=
  ⟨hφ.isSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.Sigma k] :
  (φ.switchBoundRight).Sigma k :=
  ⟨hφ.isSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + m)} [h : φ.Pi (k + 1)] :
  (φ.all' m).Pi (k + 1) := ⟨h.isPi.all'⟩

instance {φ : L.BoundedFormula' (n + 1)} [h : φ.Pi (k + 1)] :
  φ.all.Pi (k + 1) := ⟨h.isPi.all⟩

instance {φ : L.BoundedFormula' (n + m)} [h : φ.Sigma (k + 1)] :
  (φ.ex' m).Sigma (k + 1) := ⟨h.isSigma.ex'⟩

instance {φ : L.BoundedFormula' (n + 1)} [h : φ.Sigma (k + 1)] :
  φ.ex.Sigma (k + 1) := ⟨h.isSigma.ex⟩

instance {φ : L.BoundedFormula' n} [h : φ.Pi k] :
  φ.Pi (k + 1) := ⟨h.isPi.isPi_succ⟩

instance {φ : L.BoundedFormula' n} [h : φ.Sigma k] :
  φ.Sigma (k + 1) := ⟨h.isSigma.isSigma_succ⟩

instance [hφ : φ.DeltaZero] : φ.Pi k :=
  ⟨IsPi.isPi_of_le (by simpa using hφ.isDeltaZero) (Nat.zero_le k) ⟩

instance [hφ : φ.DeltaZero] : φ.Sigma k :=
  ⟨IsSigma.isSigma_of_le (by simpa using hφ.isDeltaZero) (Nat.zero_le k) ⟩

end SyntacticalLevyHierarchy


section ProvableLevyHierarchy

variable {k n : ℕ} {φ ψ : L.BoundedFormula' n}

/-- `φ` is `T`-provably `Π n` means that `φ` is provably equivalent in `T` to a `Π n` formula -/
def IsProvablePi (k : ℕ) (φ : L.BoundedFormula' n) (T : L.Theory) : Prop :=
  ∃ ψ : L.BoundedFormula' n, (ψ.IsPi k ∧ T ⊢' φ ⇔ ψ)

/-- `φ` is `T`-provably `Σ n` means that `φ` is provably equivalent in `T` to a `Σ n` formula -/
def IsProvableSigma (k : ℕ) (φ : L.BoundedFormula' n) (T : L.Theory) : Prop :=
  ∃ ψ : L.BoundedFormula' n, (ψ.IsSigma k ∧ T ⊢' φ ⇔ ψ)

-- /-- `φ` is `T`-provably `Δ n` means that `φ` is `T`-provably `Π n` and `T`-provably `Σ n` -/
-- def IsProvableDelta (k : ℕ) (φ : L.BoundedFormula' n) (T : L.Theory) : Prop :=
--   φ.IsProvablePi k T ∧ φ.IsProvableSigma k T

variable {T : L.Theory}

theorem IsPi.isProvablePi (h : φ.IsPi k) : φ.IsProvablePi k T :=
  ⟨φ, h, .iff_refl⟩

theorem IsSigma.isProvableSigma (h : φ.IsSigma k) : φ.IsProvableSigma k T :=
  ⟨φ, h, .iff_refl⟩

theorem IsDeltaZero.isProvablePi (h : φ.IsDeltaZero) : φ.IsProvablePi 0 T :=
  IsPi.isProvablePi (by simpa)

theorem IsDeltaZero.isProvableSigma (h : φ.IsDeltaZero) : φ.IsProvableSigma 0 T :=
  IsSigma.isProvableSigma (by simpa)

theorem isProvableSigma_zero_iff_isProvablePi_zero :
    φ.IsProvableSigma 0 T ↔ φ.IsProvablePi 0 T :=
  ⟨fun ⟨ψ, hψ⟩ ↦ ⟨ψ, by simpa using hψ⟩, fun ⟨ψ, hψ⟩ ↦ ⟨ψ, by simpa using hψ⟩⟩

-- theorem IsProvableDelta.isProvablePi (h : φ.IsProvableDelta k T) : φ.IsProvablePi k T := h.left

-- theorem IsProvableDelta.isProvableSigma (h : φ.IsProvableDelta k T) : φ.IsProvableSigma k T :=
--   h.right

/- provable quantifiers -/

variable {m : ℕ} {φ : L.BoundedFormula' (n + m)}

theorem IsProvablePi.all' (h : φ.IsProvablePi (k + 1) T) : (φ.all' m).IsProvablePi (k + 1) T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ.all' m, hψ₁.all'
  simp only [Provable.iff_iff]
  constructor <;> exact .mp (.of_realize fun _ _ _ _ _ ↦ by simp +contextual) hψ₂.all'

theorem IsProvablePi.all'₀ (h : φ.IsProvablePi k T) (hk : k ≠ 0) : (φ.all' m).IsProvablePi k T := by
  rw [show k = k - 1 + 1 by omega] at h ⊢
  exact h.all'

theorem IsProvablePi.ex' (h : φ.IsProvablePi k T) :  (φ.ex' m).IsProvableSigma (k + 1) T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ.ex' m, hψ₁.ex'
  simp only [Provable.iff_iff]
  constructor <;> exact .mp (.of_realize fun _ _ _ _ _ ↦ by simp +contextual) hψ₂.all'

theorem IsProvableSigma.ex' (h : φ.IsProvableSigma (k + 1) T) :
    (φ.ex' m).IsProvableSigma (k + 1) T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ.ex' m, hψ₁.ex'
  simp only [Provable.iff_iff]
  constructor <;> exact .mp (.of_realize fun _ _ _ _ _ ↦ by simp +contextual) hψ₂.all'

theorem IsProvableSigma.ex'₀ (h : φ.IsProvableSigma k T) (hk : k ≠ 0) :
    (φ.ex' m).IsProvableSigma k T := by
  rw [show k = k - 1 + 1 by omega] at h ⊢
  exact h.ex'

theorem IsProvableSigma.all' (h : φ.IsProvableSigma k T) :  (φ.all' m).IsProvablePi (k + 1) T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ.all' m, hψ₁.all'
  simp only [Provable.iff_iff]
  constructor <;> exact .mp (.of_realize fun _ _ _ _ _ ↦ by simp +contextual) hψ₂.all'

-- theorem IsProvableDelta.all' (h : φ.IsProvableDelta (k + 1) T) :
--     (φ.all' m).IsProvablePi (k + 1) T :=
--   h.left.all'

-- theorem IsProvableDelta.all'₀ (h : φ.IsProvableDelta k T) (hk : k ≠ 0) :
--     (φ.all' m).IsProvablePi k T :=
--   h.left.all'₀ hk

-- theorem IsProvableDelta.ex' (h : φ.IsProvableDelta (k + 1) T) :
--     (φ.ex' m).IsProvableSigma (k + 1) T :=
--   h.right.ex'

-- theorem IsProvableDelta.ex'₀ (h : φ.IsProvableDelta k T) (hk : k ≠ 0) :
--     (φ.ex' m).IsProvableSigma k T :=
--   h.right.ex'₀ hk


/- invariance under provable equivalence in `T` -/

variable {φ ψ : L.BoundedFormula' n}

theorem IsProvablePi.of_provable_iff (h : φ.IsProvablePi k T) (h' : T ⊢' φ ⇔ ψ) :
    ψ.IsProvablePi k T := by
  obtain ⟨θ, hθ₁, hθ₂⟩ := h
  exact ⟨θ, hθ₁, .mp₂ (.of_realize fun _ _ _ _ _ ↦ by simp +contextual) h' hθ₂⟩

theorem IsProvableSigma.of_provable_iff (h : φ.IsProvableSigma k T) (h' : T ⊢' φ ⇔ ψ) :
    ψ.IsProvableSigma k T := by
  obtain ⟨θ, hθ₁, hθ₂⟩ := h
  exact ⟨θ, hθ₁, .mp₂ (.of_realize fun _ _ _ _ _ ↦ by simp +contextual) h' hθ₂⟩

-- theorem IsProvableDelta.of_provable_iff (h : φ.IsProvableDelta k T) (h' : T ⊢' φ ⇔ ψ) :
--     ψ.IsProvableDelta k T :=
--   ⟨h.left.of_provable_iff h', h.right.of_provable_iff h'⟩

/- provable connectives -/

mutual
theorem IsProvablePi.not {k n : ℕ} {φ : L.BoundedFormula' n} (h : φ.IsProvablePi k T) :
    (∼φ).IsProvableSigma k T :=
  let ⟨ψ, hψ₁, hψ₂⟩ := h
  match k with
  | 0 => ⟨∼ψ, by simpa using hψ₁, .mp (.of_realize fun _ _ _ _ _ ↦ by simp +contextual) hψ₂⟩
  | k + 1 => let ⟨m, θ, hθ₁, hθ₂⟩ := hψ₁.exists_Sigma_all'
    hθ₁.isProvableSigma.not.ex'.of_provable_iff <|
      .mp (.of_realize fun _ _ _ _ _ ↦ by simp +contextual) (hθ₂ ▸ hψ₂)

theorem IsProvableSigma.not {k n : ℕ} {φ : L.BoundedFormula' n} (h : φ.IsProvableSigma k T) :
    (∼φ).IsProvablePi k T :=
  let ⟨ψ, hψ₁, hψ₂⟩ := h
  match k with
  | 0 => ⟨∼ψ, by simpa using hψ₁, .mp (.of_realize fun _ _ _ _ _ ↦ by simp +contextual) hψ₂⟩
  | k + 1 => let ⟨m, θ, hθ₁, hθ₂⟩ := hψ₁.exists_Pi_ex'
    hθ₁.isProvablePi.not.all'.of_provable_iff <|
      .mp (.of_realize fun _ _ _ _ _ ↦ by simp +contextual) (hθ₂ ▸ hψ₂)
end

-- theorem IsProvableDelta.not (h : φ.IsProvableDelta k T) : (∼φ).IsProvableDelta k T :=
--   ⟨h.right.not, h.left.not⟩

@[simp]
theorem ProvablePi_not_iff : (∼φ).IsProvablePi k T ↔ φ.IsProvableSigma k T := by
  refine ⟨fun h ↦ h.not.of_provable_iff ?_, IsProvableSigma.not⟩
  exact .of_realize fun _ _ _ _ _ ↦ by simp +contextual

@[simp]
theorem ProvableSigma_not_iff : (∼φ).IsProvableSigma k T ↔ φ.IsProvablePi k T := by
  refine ⟨fun h ↦ h.not.of_provable_iff ?_, IsProvablePi.not⟩
  exact .of_realize fun _ _ _ _ _ ↦ by simp +contextual

-- @[simp]
-- theorem ProvableDelta_not_iff : (∼φ).IsProvableDelta k T ↔ φ.IsProvableDelta k T := by
--   refine ⟨fun h ↦ h.not.of_provable_iff ?_, IsProvableDelta.not⟩
--   exact .of_realize fun _ _ _ _ _ ↦ by simp +contextual

mutual
theorem IsProvablePi.imp {k n : ℕ} {φ ψ : L.BoundedFormula' n}
    (hφ : φ.IsProvablePi k T) (hψ : ψ.IsProvableSigma k T) : (φ ⟹ ψ).IsProvableSigma k T :=
  let ⟨φ', hφ₁, hφ₂⟩ := hφ
  let ⟨ψ', hψ₁, hψ₂⟩ := hψ
  match k with
  | 0 => by
    refine ⟨φ' ⟹ ψ', ?_, ?_⟩
    · simp only [pi_zero_iff_deltaZero, sigma_zero_iff_deltaZero] at hφ₁ hψ₁ ⊢
      exact hφ₁.imp hψ₁
    · exact .mp₂ (.of_realize fun _ _ _ _ _ ↦ by simp +contextual) hφ₂ hψ₂
  | k + 1 => by
    obtain ⟨p, φ'', hφ''₁, hφ''₂⟩ := hφ₁.exists_Sigma_all'
    obtain ⟨q, ψ'', hψ''₁, hψ''₂⟩ := hψ₁.exists_Pi_ex'
    have : (φ''.splitImp ψ'').ex'.ex'.IsProvableSigma (k + 1) T :=
      (hφ''₁.substBound _).isProvableSigma.imp (hψ''₁.substBound _).isProvablePi |>.ex'.ex'
    refine this.of_provable_iff (.of_models.{u, v, 0, 0} fun M _ _ v xs hT ↦ ?_)
    have hφ₂ := hφ₂.sound v hT xs
    have hψ₂ := hψ₂.sound v hT xs
    inhabit M
    simp only [realize_iff] at hφ₂ hψ₂
    simp only [realize_iff, realize_ex', realize_splitImp, realize_imp, hφ₂, hφ''₂, realize_all',
      hψ₂, hψ''₂]
    refine ⟨by grind, fun h₁ ↦ ?_⟩
    by_cases h₂ : ∀ ys, φ''.Realize v (append xs ys)
    · obtain ⟨zs, hzs⟩ := h₁ h₂
      exact ⟨default, zs, by grind⟩
    · simp only [not_forall] at h₂
      obtain ⟨ys, hys⟩ := h₂
      exact ⟨ys, default, by grind⟩

theorem IsProvableSigma.imp {k n : ℕ} {φ ψ : L.BoundedFormula' n}
    (hφ : φ.IsProvableSigma k T) (hψ : ψ.IsProvablePi k T) : (φ ⟹ ψ).IsProvablePi k T :=
  let ⟨φ', hφ₁, hφ₂⟩ := hφ
  let ⟨ψ', hψ₁, hψ₂⟩ := hψ
  match k with
  | 0 => by
    refine ⟨φ' ⟹ ψ', ?_, ?_⟩
    · simp only [sigma_zero_iff_deltaZero, pi_zero_iff_deltaZero] at hφ₁ hψ₁ ⊢
      exact hφ₁.imp hψ₁
    · exact .mp₂ (.of_realize fun _ _ _ _ _ ↦ by simp +contextual) hφ₂ hψ₂
  | k + 1 => by
    obtain ⟨p, φ'', hφ''₁, hφ''₂⟩ := hφ₁.exists_Pi_ex'
    obtain ⟨q, ψ'', hψ''₁, hψ''₂⟩ := hψ₁.exists_Sigma_all'
    have : (φ''.splitImp ψ'').all'.all'.IsProvablePi (k + 1) T :=
      (hφ''₁.substBound _).isProvablePi.imp (hψ''₁.substBound _).isProvableSigma |>.all'.all'
    refine this.of_provable_iff (.of_models.{u, v, 0, 0} fun M _ _ v xs hT ↦ ?_)
    have hφ₂ := hφ₂.sound v hT xs
    have hψ₂ := hψ₂.sound v hT xs
    inhabit M
    simp only [realize_iff] at hφ₂ hψ₂
    simp only [realize_iff, realize_all', realize_splitImp, realize_imp, hφ₂, hφ''₂, realize_ex',
      hψ₂, hψ''₂, forall_exists_index]
    tauto
end

-- theorem IsProvableDelta.imp {φ ψ : L.BoundedFormula' n}
--     (hφ : φ.IsProvableDelta k T) (hψ : ψ.IsProvableDelta k T) : (φ ⟹ ψ).IsProvableDelta k T :=
--   ⟨hφ.right.imp hψ.left, hφ.left.imp hψ.right⟩

theorem IsProvablePi.sup (hφ : φ.IsProvablePi k T) (hψ : ψ.IsProvablePi k T) :
    (φ ⊔ ψ).IsProvablePi k T := hφ.not.imp hψ

theorem IsProvablePi.inf (hφ : φ.IsProvablePi k T) (hψ : ψ.IsProvablePi k T) :
    (φ ⊓ ψ).IsProvablePi k T := hφ.imp hψ.not |>.not

theorem IsProvableSigma.sup (hφ : φ.IsProvableSigma k T) (hψ : ψ.IsProvableSigma k T) :
    (φ ⊔ ψ).IsProvableSigma k T := hφ.not.imp hψ

theorem IsProvableSigma.inf (hφ : φ.IsProvableSigma k T) (hψ : ψ.IsProvableSigma k T) :
    (φ ⊓ ψ).IsProvableSigma k T := hφ.imp hψ.not |>.not

-- theorem IsProvableDelta.sup (hφ : φ.IsProvableDelta k T) (hψ : ψ.IsProvableDelta k T) :
--     (φ ⊔ ψ).IsProvableDelta k T := hφ.not.imp hψ

-- theorem IsProvableDelta.inf (hφ : φ.IsProvableDelta k T) (hψ : ψ.IsProvableDelta k T) :
--     (φ ⊓ ψ).IsProvableDelta k T := hφ.imp hψ.not |>.not

-- theorem IsProvableDelta.iff (hφ : φ.IsProvableDelta k T) (hψ : ψ.IsProvableDelta k T) :
--     (φ ⇔ ψ).IsProvableDelta k T := (hφ.imp hψ).inf (hψ.imp hφ)

/-- substBound -/
theorem IsProvablePi.substBound {φ : L.BoundedFormula' n} (ts : Fin n → L.Term' m)
    (hφ : φ.IsProvablePi k T) : (φ.substBound ts).IsProvablePi k T := by
  obtain ⟨φ', hφ₁, hφ₂⟩ := hφ
  refine ⟨φ'.substBound ts, hφ₁.substBound _, .of_models.{u, v, 0, 0} fun M _ _ v xs hT ↦ ?_⟩
  simpa [realize_iff, realize_substBound] using
    hφ₂.sound v hT fun i ↦ ((ts i).realize (Sum.elim v xs))

theorem IsProvableSigma.substBound {φ : L.BoundedFormula' n} (ts : Fin n → L.Term' m)
    (hφ : φ.IsProvableSigma k T) : (φ.substBound ts).IsProvableSigma k T := by
  obtain ⟨φ', hφ₁, hφ₂⟩ := hφ
  refine ⟨φ'.substBound ts, hφ₁.substBound _, .of_models.{u, v, 0, 0} fun M _ _ v xs hT ↦ ?_⟩
  simpa [realize_iff, realize_substBound] using
    hφ₂.sound v hT fun i ↦ ((ts i).realize (Sum.elim v xs))

-- theorem IsProvableDelta.substBound {φ : L.BoundedFormula' n} (ts : Fin n → L.Term' m)
--     (hφ : φ.IsProvableDelta k T) : (φ.substBound ts).IsProvableDelta k T :=
--   ⟨hφ.left.substBound _, hφ.right.substBound _⟩

/- lower levels are included in upper levels -/

theorem IsProvablePi.isProvablePi_of_le (h : φ.IsProvablePi k T) (hkm : k ≤ m) :
    φ.IsProvablePi m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.isPi_of_le hkm

theorem IsProvableSigma.isProvableSigma_of_le (h : φ.IsProvableSigma k T) (hkm : k ≤ m) :
    φ.IsProvableSigma m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.isSigma_of_le hkm

-- theorem IsProvableDelta.isProvableDelta_of_le (h : φ.IsProvableDelta k T) (hkm : k ≤ m) :
--     φ.IsProvableDelta m T :=
--   ⟨h.left.isProvablePi_of_le hkm, h.right.isProvableSigma_of_le hkm⟩

theorem IsProvablePi.isProvableSigma_of_lt (h : φ.IsProvablePi k T) (hkm : k < m) :
    φ.IsProvableSigma m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.Sigma_of_lt hkm

theorem IsProvableSigma.isProvablePi_of_lt (h : φ.IsProvableSigma k T) (hkm : k < m) :
    φ.IsProvablePi m T := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  use ψ, hψ₁.Pi_of_lt hkm

-- theorem IsProvablePi.isProvableDelta_of_lt (h : φ.IsProvablePi k T) (hkm : k < m) :
--     φ.IsProvableDelta m T :=
--   ⟨h.isProvablePi_of_le hkm.le, h.isProvableSigma_of_lt hkm⟩

-- theorem IsProvableSigma.isProvableDelta_of_lt (h : φ.IsProvableSigma k T) (hkm : k < m) :
--     φ.IsProvableDelta m T :=
--   ⟨h.isProvablePi_of_lt hkm, h.isProvableSigma_of_le hkm.le⟩

theorem IsProvablePi.foldr_sup {f : List (L.BoundedFormula' n)}
    (hf : ∀ φ ∈ f, φ.IsProvablePi k T) :
    (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ f).IsProvablePi k T := by
  induction f with
  | nil => exact isDeltaZero_bot.isProvablePi.isProvablePi_of_le (by omega)
  | cons ψ f ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hf
    exact hf.left.sup (ih (hf.right))

theorem isProvablePi_iSup [Finite β] {f : β → L.BoundedFormula' n}
    (hf : ∀ i, (f i).IsProvablePi k T) :
    (iSup f).IsProvablePi k T := by
  simp only [BoundedFormula.iSup]
  grind [IsProvablePi.foldr_sup]

theorem IsProvablePi.foldr_inf {f : List (L.BoundedFormula' n)}
    (hf : ∀ φ ∈ f, φ.IsProvablePi k T) :
    (List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ f).IsProvablePi k T := by
  induction f with
  | nil => exact isDeltaZero_top.isProvablePi.isProvablePi_of_le (by omega)
  | cons ψ f ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hf
    exact hf.left.inf (ih (hf.right))

theorem isProvablePi_iInf [Finite β] {f : β → L.BoundedFormula' n}
    (hf : ∀ i, (f i).IsProvablePi k T) :
    (iInf f).IsProvablePi k T := by
  simp only [BoundedFormula.iInf]
  grind [IsProvablePi.foldr_inf]

theorem IsProvableSigma.foldr_sup {f : List (L.BoundedFormula' n)}
    (hf : ∀ φ ∈ f, φ.IsProvableSigma k T) :
    (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ f).IsProvableSigma k T := by
  induction f with
  | nil => exact isDeltaZero_bot.isProvableSigma.isProvableSigma_of_le (by omega)
  | cons ψ f ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hf
    exact hf.left.sup (ih (hf.right))

theorem isProvableSigma_iSup [Finite β] {f : β → L.BoundedFormula' n}
    (hf : ∀ i, (f i).IsProvableSigma k T) :
    (iSup f).IsProvableSigma k T := by
  simp only [BoundedFormula.iSup]
  grind [IsProvableSigma.foldr_sup]

theorem IsProvableSigma.foldr_inf {f : List (L.BoundedFormula' n)}
    (hf : ∀ φ ∈ f, φ.IsProvableSigma k T) :
    (List.foldr (fun x1 x2 ↦ x1 ⊓ x2) ⊤ f).IsProvableSigma k T := by
  induction f with
  | nil => exact isDeltaZero_top.isProvableSigma.isProvableSigma_of_le (by omega)
  | cons ψ f ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hf
    exact hf.left.inf (ih (hf.right))

theorem isProvableSigma_iInf [Finite β] {f : β → L.BoundedFormula' n}
    (hf : ∀ i, (f i).IsProvableSigma k T) :
    (iInf f).IsProvableSigma k T := by
  simp only [BoundedFormula.iInf]
  grind [IsProvableSigma.foldr_inf]

/- monotone in the theory -/

variable {T' : L.Theory}

theorem IsProvablePi.mono (h : φ.IsProvablePi k T) (h' : T ⊆ T') : φ.IsProvablePi k T' := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  exact ⟨ψ, hψ₁, hψ₂.mono h'⟩

theorem IsProvableSigma.mono (h : φ.IsProvableSigma k T) (h' : T ⊆ T') :
    φ.IsProvableSigma k T' := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := h
  exact ⟨ψ, hψ₁, hψ₂.mono h'⟩

-- theorem IsProvableDelta.mono (h : φ.IsProvableDelta k T) (h' : T ⊆ T') :
--     φ.IsProvableDelta k T' := by
--   obtain ⟨hψ₁, hψ₂⟩ := h
--   exact ⟨hψ₁.mono h', hψ₂.mono h'⟩

class ProvablePi (k : ℕ) (φ : L.BoundedFormula' n) (T : L.Theory) : Prop where
  isProvablePi : φ.IsProvablePi k T

class ProvableSigma (k : ℕ) (φ : L.BoundedFormula' n) (T : L.Theory) : Prop where
  isProvableSigma : φ.IsProvableSigma k T

class abbrev ProvableDelta (k : ℕ) (φ : L.BoundedFormula' n) (T : L.Theory) : Prop :=
  φ.ProvablePi k T, φ.ProvableSigma k T

-- instance [φ.ProvableDelta k T] : φ.ProvablePi k T := by infer_instance
-- instance [φ.ProvableDelta k T] : φ.ProvableSigma k T := by infer_instance

instance [h : φ.Pi k] : φ.ProvablePi k T := ⟨h.isPi.isProvablePi⟩

instance [h : φ.Sigma k] : φ.ProvableSigma k T := ⟨h.isSigma.isProvableSigma⟩

instance [h : φ.DeltaZero] : φ.ProvablePi 0 T := ⟨h.isDeltaZero.isProvablePi⟩

instance [h : φ.DeltaZero] : φ.ProvableSigma 0 T := ⟨h.isDeltaZero.isProvableSigma⟩

instance [h : φ.ProvablePi 0 T] : φ.ProvableSigma 0 T :=
  ⟨by simpa [isProvableSigma_zero_iff_isProvablePi_zero] using h.isProvablePi⟩

instance [h : φ.ProvableSigma 0 T] : φ.ProvablePi 0 T :=
  ⟨by simpa [isProvableSigma_zero_iff_isProvablePi_zero] using h.isProvableSigma⟩

variable {φ : L.BoundedFormula' (n + m)}

instance [h : φ.ProvablePi (k + 1) T] : (φ.all' m).ProvablePi (k + 1) T := ⟨h.isProvablePi.all'⟩

instance [h : φ.ProvablePi k T] [hk : NeZero k] :
  (φ.all' m).ProvablePi k T := ⟨h.isProvablePi.all'₀ hk.out⟩

instance [h : φ.ProvablePi k T] :
  (φ.ex' m).ProvableSigma (k + 1) T := ⟨h.isProvablePi.ex'⟩

instance [h : φ.ProvableSigma (k + 1) T] :
  (φ.ex' m).ProvableSigma (k + 1) T := ⟨h.isProvableSigma.ex'⟩

instance [h : φ.ProvableSigma k T] [hk : NeZero k] :
  (φ.ex' m).ProvableSigma k T := ⟨h.isProvableSigma.ex'₀ hk.out⟩

instance [h : φ.ProvableSigma k T] :
  (φ.all' m).ProvablePi (k + 1) T := ⟨h.isProvableSigma.all'⟩

variable {φ : L.BoundedFormula' (n + 1)}

instance [h : φ.ProvablePi (k + 1) T] : (φ.all).ProvablePi (k + 1) T := ⟨h.isProvablePi.all'⟩

instance [h : φ.ProvablePi k T] [hk : NeZero k] :
  (φ.all).ProvablePi k T := ⟨h.isProvablePi.all'₀ hk.out⟩

instance [h : φ.ProvablePi k T] :
  (φ.ex).ProvableSigma (k + 1) T := ⟨h.isProvablePi.ex'⟩

instance [h : φ.ProvableSigma (k + 1) T] :
  (φ.ex).ProvableSigma (k + 1) T := ⟨h.isProvableSigma.ex'⟩

instance [h : φ.ProvableSigma k T] [hk : NeZero k] :
  (φ.ex).ProvableSigma k T := ⟨h.isProvableSigma.ex'₀ hk.out⟩

instance [h : φ.ProvableSigma k T] :
  (φ.all).ProvablePi (k + 1) T := ⟨h.isProvableSigma.all'⟩

variable {φ ψ : L.BoundedFormula' n}

instance [h : φ.ProvablePi k T] :
  (∼φ).ProvableSigma k T := ⟨h.isProvablePi.not⟩

instance [h : φ.ProvableSigma k T] :
  (∼φ).ProvablePi k T := ⟨h.isProvableSigma.not⟩

-- instance [h : φ.ProvableDelta k T] : (∼φ).ProvableDelta k T where
--   isProvablePi := h.isProvableSigma.not
--   isProvableSigma := h.isProvablePi.not

instance [hφ : φ.ProvablePi k T] [hψ : ψ.ProvableSigma k T] :
  (φ ⟹ ψ).ProvableSigma k T := ⟨hφ.isProvablePi.imp hψ.isProvableSigma⟩

instance [hφ : φ.ProvableSigma k T] [hψ : ψ.ProvablePi k T] :
  (φ ⟹ ψ).ProvablePi k T := ⟨hφ.isProvableSigma.imp hψ.isProvablePi⟩

-- instance {k n : ℕ} {φ ψ : L.BoundedFormula' n}
  -- [hφ : φ.ProvableDelta k T] [hψ : ψ.ProvableDelta k T] :
  -- (φ ⟹ ψ).ProvableDelta k T where
  -- isProvablePi := hφ.isProvableSigma.imp hψ.isProvablePi
  -- isProvableSigma := hφ.isProvablePi.imp hψ.isProvableSigma

instance {φ ψ : L.BoundedFormula' n}
  [hφ : φ.ProvablePi k T] [hψ : ψ.ProvablePi k T] :
  (φ ⊔ ψ).ProvablePi k T := ⟨hφ.isProvablePi.sup hψ.isProvablePi⟩

instance {φ ψ : L.BoundedFormula' n}
  [hφ : φ.ProvablePi k T] [hψ : ψ.ProvablePi k T] :
  (φ ⊓ ψ).ProvablePi k T := ⟨hφ.isProvablePi.inf hψ.isProvablePi⟩

instance {φ ψ : L.BoundedFormula' n}
  [hφ : φ.ProvableSigma k T] [hψ : ψ.ProvableSigma k T] :
  (φ ⊔ ψ).ProvableSigma k T := ⟨hφ.isProvableSigma.sup hψ.isProvableSigma⟩

instance {φ ψ : L.BoundedFormula' n}
  [hφ : φ.ProvableSigma k T] [hψ : ψ.ProvableSigma k T] :
  (φ ⊓ ψ).ProvableSigma k T := ⟨hφ.isProvableSigma.inf hψ.isProvableSigma⟩

instance [Finite β] {f : β → L.BoundedFormula' n}
  [hf : ∀ i, (f i).ProvablePi k T] :
  (iSup f).ProvablePi k T := ⟨isProvablePi_iSup (fun i ↦ (hf i).isProvablePi)⟩

instance [Finite β] {f : β → L.BoundedFormula' n}
  [hf : ∀ i, (f i).ProvablePi k T] :
  (iInf f).ProvablePi k T := ⟨isProvablePi_iInf (fun i ↦ (hf i).isProvablePi)⟩

instance [Finite β] {f : β → L.BoundedFormula' n}
  [hf : ∀ i, (f i).ProvableSigma k T] :
  (iSup f).ProvableSigma k T := ⟨isProvableSigma_iSup (fun i ↦ (hf i).isProvableSigma)⟩

instance [Finite β] {f : β → L.BoundedFormula' n}
  [hf : ∀ i, (f i).ProvableSigma k T] :
  (iInf f).ProvableSigma k T := ⟨isProvableSigma_iInf (fun i ↦ (hf i).isProvableSigma)⟩

-- instance {φ ψ : L.BoundedFormula' n}
--   [hφ : φ.ProvableDelta k T] [hψ : ψ.ProvableDelta k T] :
--   (φ ⊔ ψ).ProvableDelta k T where
--   isProvablePi := hφ.isProvablePi.sup hψ.isProvablePi
--   isProvableSigma := hφ.isProvableSigma.sup hψ.isProvableSigma

-- instance {φ ψ : L.BoundedFormula' n}
--   [hφ : φ.ProvableDelta k T] [hψ : ψ.ProvableDelta k T] :
--   (φ ⊓ ψ).ProvableDelta k T where
--   isProvablePi := hφ.isProvablePi.inf hψ.isProvablePi
--   isProvableSigma := hφ.isProvableSigma.inf hψ.isProvableSigma

instance {φ ψ : L.BoundedFormula' n}
  [hφ : φ.ProvableDelta k T] [hψ : ψ.ProvableDelta k T] :
  (φ ⇔ ψ).ProvableDelta k T where
  isProvablePi :=
    (hφ.isProvableSigma.imp hψ.isProvablePi).inf (hψ.isProvableSigma.imp hφ.isProvablePi)
  isProvableSigma :=
    (hφ.isProvablePi.imp hψ.isProvableSigma).inf (hψ.isProvablePi.imp hφ.isProvableSigma)

instance {φ : L.BoundedFormula' n}
  [hφ : φ.ProvablePi k T] (ts : Fin n → L.Term' m) :
  (φ.substBound ts).ProvablePi k T :=
  ⟨hφ.isProvablePi.substBound _⟩

instance {φ : L.BoundedFormula' n}
  [hφ : φ.ProvableSigma k T] (ts : Fin n → L.Term' m) :
  (φ.substBound ts).ProvableSigma k T :=
  ⟨hφ.isProvableSigma.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.ProvablePi k T] :
  (φ.substBoundBound f).ProvablePi k T := ⟨h.isProvablePi.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.ProvableSigma k T] :
  (φ.substBoundBound f).ProvableSigma k T := ⟨h.isProvableSigma.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.ProvablePi k T] (h' : n = n') :
  (φ.cast h').ProvablePi k T := ⟨h.isProvablePi.substBound _⟩

instance {φ : L.BoundedFormula' n} [h : φ.ProvableSigma k T] (h' : n = n') :
  (φ.cast h').ProvableSigma k T := ⟨h.isProvableSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + p)} {ψ : L.BoundedFormula' (n + q)} [hφ : φ.ProvableSigma k T]
  [hψ : ψ.ProvablePi k T] : (φ.splitImp ψ).ProvablePi k T :=
  ⟨(hφ.isProvableSigma.substBound _).imp (hψ.isProvablePi.substBound _)⟩

instance {φ : L.BoundedFormula' (n + p)} {ψ : L.BoundedFormula' (n + q)} [hφ : φ.ProvablePi k T]
  [hψ : ψ.ProvableSigma k T] : (φ.splitImp ψ).ProvableSigma k T :=
  ⟨(hφ.isProvablePi.substBound _).imp (hψ.isProvableSigma.substBound _)⟩

instance {φ : L.BoundedFormula' (n + p)} [hφ : φ.ProvablePi k T] :
  (φ.switchBound).ProvablePi k T :=
  ⟨hφ.isProvablePi.substBound _⟩

instance {φ : L.BoundedFormula' (n + p)} [hφ : φ.ProvableSigma k T] :
  (φ.switchBound).ProvableSigma k T :=
  ⟨hφ.isProvableSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + p + q)} [hφ : φ.ProvablePi k T] :
  (φ.castAssoc).ProvablePi k T :=
  ⟨hφ.isProvablePi.substBound _⟩

instance {φ : L.BoundedFormula' (n + p + q)} [hφ : φ.ProvableSigma k T] :
  (φ.castAssoc).ProvableSigma k T :=
  ⟨hφ.isProvableSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.ProvablePi k T] :
  (φ.castAssoc').ProvablePi k T :=
  ⟨hφ.isProvablePi.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.ProvableSigma k T] :
  (φ.castAssoc').ProvableSigma k T :=
  ⟨hφ.isProvableSigma.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.ProvablePi k T] :
  (φ.switchBoundRight).ProvablePi k T :=
  ⟨hφ.isProvablePi.substBound _⟩

instance {φ : L.BoundedFormula' (n + (p + q))} [hφ : φ.ProvableSigma k T] :
  (φ.switchBoundRight).ProvableSigma k T :=
  ⟨hφ.isProvableSigma.substBound _⟩

instance {φ : L.BoundedFormula' (p + n)} {ψ : L.BoundedFormula' (q + n)} [hφ : φ.ProvableSigma k T]
  [hψ : ψ.ProvablePi k T] : (φ.splitImp' ψ).ProvablePi k T := by rw [splitImp']; infer_instance

instance {φ : L.BoundedFormula' (p + n)} {ψ : L.BoundedFormula' (q + n)} [hφ : φ.ProvablePi k T]
  [hψ : ψ.ProvableSigma k T] : (φ.splitImp' ψ).ProvableSigma k T := by
  rw [splitImp']; infer_instance


end ProvableLevyHierarchy

end BoundedFormula

end Language

end FirstOrder
