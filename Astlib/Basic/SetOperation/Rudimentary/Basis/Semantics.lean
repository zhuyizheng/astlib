/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Astlib.Basic.SetOperation.Rudimentary.Basis.Syntax
import Astlib.Basic.SetOperation.MemStructure.Substructure

/-!
file dobstring
-/
open FirstOrder Language Structure BoundedFormula Fin MemStructure DeltaZeroBoundedFormula RudimentaryBasisTerm

variable {L : Language.{u, v}} {M : Type max u v}
  [L.MemStructure M] [Inhabited M] (x y : M)

namespace FirstOrder.Language

namespace MemStructure

def IsSProd₀ (a x y : M) := ∀ z, z ∈ a ↔ ∃ u ∈ x, ∃ v ∈ y, z = !(u, v)

noncomputable instance : Decidable (∃ a : M, IsSProd₀ a x y) :=
  Classical.propDecidable _

noncomputable def sprod₀ (x y : M) :=
  dite (∃ a : M, IsSProd₀ a x y) Classical.choose default

def IsSwitch₀ (a x y : M) := ∀ z, z ∈ a ↔ ∃ u v, ∃ w ∈ y, !(u, v) ∈ x ∧ z = !(!(u, w), v)

noncomputable instance : Decidable (∃ a : M, IsSwitch₀ a x y) :=
  Classical.propDecidable _

noncomputable def switch₀ (x y : M) :=
  dite (∃ a : M, IsSwitch₀ a x y) Classical.choose default

def IsRotate₀ (a x y : M) := ∀ z, z ∈ a ↔ ∃ u v, ∃ w ∈ y, !(u, v) ∈ x ∧ z = !(!(w, u), v)

noncomputable instance : Decidable (∃ a : M, IsRotate₀ a x y) :=
  Classical.propDecidable _

noncomputable def rotate₀ (x y : M) :=
  dite (∃ a : M, IsRotate₀ a x y) Classical.choose default

def IsSUnion₀ (a x : M) := ∀ z, z ∈ a ↔ ∃ u ∈ x, z ∈ u

noncomputable instance : Decidable (∃ a : M, IsSUnion₀ a x) :=
  Classical.propDecidable _

noncomputable def sUnion₀ (x : M) :=
  dite (∃ a : M, IsSUnion₀ a x) Classical.choose default

def IsDom₀ (a x : M) := ∀ z, z ∈ a ↔ ∃ y, !(z, y) ∈ x

noncomputable instance : Decidable (∃ a : M, IsDom₀ a x) :=
  Classical.propDecidable _

noncomputable def dom₀ (x : M) :=
  dite (∃ a : M, IsDom₀ a x) Classical.choose default

def IsMemGraph₀ (a x : M) := ∀ z, z ∈ a ↔ ∃ u ∈ x, ∃ v ∈ x, z = !(u, v) ∧ v ∈ u

noncomputable instance : Decidable (∃ a : M, IsMemGraph₀ a x) :=
  Classical.propDecidable _

noncomputable def memGraph₀ (x : M) :=
  dite (∃ a : M, IsMemGraph₀ a x) Classical.choose default

def IsSliceSet₀ (a x y : M) :=
  ∀ z, z ∈ a ↔ ∃ u ∈ y, ∀ v, v ∈ z ↔ !(u, v) ∈ x

noncomputable instance : Decidable (∃ a : M, IsSliceSet₀ a x y) :=
  Classical.propDecidable _

noncomputable def sliceSet₀ (x y : M) :=
  dite (∃ a : M, IsSliceSet₀ a x y) Classical.choose default

def IsInterRel₀ (a x : M) (R : L.Relations 1) :=
  ∀ z, z ∈ a ↔ z ∈ x ∧ RelMap R ![x]

noncomputable instance : Decidable (∃ a : M, IsInterRel₀ a x R) :=
  Classical.propDecidable _

noncomputable def interRel₀ (x : M) (R : L.Relations 1):=
  dite (∃ a : M, IsInterRel₀ a x R) Classical.choose default


@[simp]
noncomputable def _root_.FirstOrder.Language.RudimentaryBasisTerm.realize
    {n : ℕ} (r : L.RudimentaryBasisTerm n) : MulticlassFunction M n :=
  match r with
  | .var i => fun xs ↦ xs i
  | .const c => fun _ ↦ L.constantMap c
  | .unorderedPair r₁ r₂ => fun xs ↦ unorderedPair (r₁.realize xs) (r₂.realize xs)
  | .sdiff r₁ r₂ => fun xs ↦ (r₁.realize xs) \ (r₂.realize xs)
  | .sprod r₁ r₂ => fun xs ↦ sprod₀ (r₁.realize xs) (r₂.realize xs)
  | .switch r₁ r₂ => fun xs ↦ switch₀ (r₁.realize xs) (r₂.realize xs)
  | .rotate r₁ r₂ => fun xs ↦ rotate₀ (r₁.realize xs) (r₂.realize xs)
  | .sUnion r => fun xs ↦ sUnion₀ (r.realize xs)
  | .dom r => fun xs ↦ dom₀ (r.realize xs)
  | .memGraph r => fun xs ↦ memGraph₀ (r.realize xs)
  | .sliceSet r₁ r₂ => fun xs ↦ sliceSet₀ (r₁.realize xs) (r₂.realize xs)
  | .interRel r R => fun xs ↦ interRel₀ (r.realize xs) R

scoped[FirstOrder.Language] notation:max
  r "〘" xs "〙" => RudimentaryBasisTerm.realize r xs


@[simp]
theorem realize_substBoundRudBasis (r : L.RudimentaryBasisTerm n) (rs : Fin n → L.RudimentaryBasisTerm m)
    (xs : Fin m → M) :
    (r.substBoundRudBasis rs)〘xs〙 = r〘fun i ↦ (rs i)〘xs〙〙 := by
  induction r generalizing m with
  | var => simp [substBoundRudBasis]
  | const => simp [substBoundRudBasis]
  | unorderedPair => simp [substBoundRudBasis, *]
  | sdiff => simp [substBoundRudBasis, *]
  | sprod => simp [substBoundRudBasis, *]
  | switch => simp [substBoundRudBasis, *]
  | rotate => simp [substBoundRudBasis, *]
  | sUnion => simp [substBoundRudBasis, *]
  | dom => simp [substBoundRudBasis, *]
  | memGraph => simp [substBoundRudBasis, *]
  | sliceSet => simp [substBoundRudBasis, *]
  | interRel => simp [substBoundRudBasis, *]

section RudBasisClosed

variable (M) in
class RudBasisClosed : Prop extends PairClosed M, SDiffClosed M where
  sprodClosed : ∀ x y, ∃ a : M, IsSProd₀ a x y
  switchClosed : ∀ x y, ∃ a : M, IsSwitch₀ a x y
  rotateClosed : ∀ x y, ∃ a : M, IsRotate₀ a x y
  sUnionClosed : ∀ x, ∃ a : M, IsSUnion₀ a x
  domClosed : ∀ x, ∃ a : M, IsDom₀ a x
  memGraphClosed : ∀ x, ∃ a : M, IsMemGraph₀ a x
  sliceSetClosed : ∀ x y, ∃ a : M, IsSliceSet₀ a x y
  interRelClosed : ∀ x y, ∃ a : M, IsInterRel₀ a x y

variable [RudBasisClosed M] (x y z a : M)

@[simp]
theorem realize_sdiff {n : ℕ} (r₁ r₂ : L.RudimentaryBasisTerm n) (xs : Fin n → M) :
    z ∈ (r₁ \ r₂)〘xs〙 ↔ z ∈ r₁〘xs〙 ∧ z ∉ r₂〘xs〙 := by
  simp only [SDiff.sdiff, RudimentaryBasisTerm.realize]
  rw [← MemStructure.mem_sdiff_iff]
  rfl

@[simp]
theorem mem_sprod₀_iff : z ∈ sprod₀ x y ↔ ∃ u ∈ x, ∃ v ∈ y, z = !(u, v) := by
  simp only [sprod₀, RudBasisClosed.sprodClosed, ↓reduceDIte]
  rw [Classical.choose_spec (RudBasisClosed.sprodClosed _ _)]

@[simp]
theorem mem_switch₀_iff : z ∈ switch₀ x y ↔ ∃ u v, ∃ w ∈ y, !(u, v) ∈ x ∧ z = !(!(u, w), v) := by
  simp only [switch₀, RudBasisClosed.switchClosed, ↓reduceDIte]
  rw [Classical.choose_spec (RudBasisClosed.switchClosed _ _)]

@[simp]
theorem mem_rotate₀_iff : z ∈ rotate₀ x y ↔ ∃ u v, ∃ w ∈ y, !(u, v) ∈ x ∧ z = !(!(w, u), v) := by
  simp only [rotate₀, RudBasisClosed.rotateClosed, ↓reduceDIte]
  rw [Classical.choose_spec (RudBasisClosed.rotateClosed _ _)]

@[simp]
theorem mem_sUnion₀_iff : z ∈ sUnion₀ x ↔ ∃ u ∈ x, z ∈ u := by
  simp only [sUnion₀, RudBasisClosed.sUnionClosed, ↓reduceDIte]
  rw [Classical.choose_spec (RudBasisClosed.sUnionClosed _)]

@[simp]
theorem mem_dom₀_iff : z ∈ dom₀ x ↔ ∃ y, !(z, y) ∈ x := by
  simp only [dom₀, RudBasisClosed.domClosed, ↓reduceDIte]
  rw [Classical.choose_spec (RudBasisClosed.domClosed _)]

@[simp]
theorem mem_memGraph₀_iff : z ∈ memGraph₀ x ↔ ∃ u ∈ x, ∃ v ∈ x, z = !(u, v) ∧ v ∈ u := by
  simp only [memGraph₀, RudBasisClosed.memGraphClosed, ↓reduceDIte]
  rw [Classical.choose_spec (RudBasisClosed.memGraphClosed _)]

@[simp]
theorem mem_sliceSet₀_iff : z ∈ sliceSet₀ x y ↔ ∃ u ∈ y, ∀ v, v ∈ z ↔ !(u, v) ∈ x := by
  simp only [sliceSet₀, RudBasisClosed.sliceSetClosed, ↓reduceDIte]
  rw [Classical.choose_spec (RudBasisClosed.sliceSetClosed _ _)]

@[simp]
theorem mem_interRel₀_iff : z ∈ interRel₀ x R ↔ z ∈ x ∧ RelMap R ![x] := by
  simp only [interRel₀, RudBasisClosed.interRelClosed, ↓reduceDIte]
  rw [Classical.choose_spec (RudBasisClosed.interRelClosed _ _)]

variable (r₁ r₂ : L.RudimentaryBasisTerm n) (xs : Fin n → M)

@[simp]
theorem mem_realize_union_iff :
    z ∈ (r₁ ∪ r₂)〘xs〙 ↔ z ∈ r₁〘xs〙 ∨ z ∈ r₂〘xs〙 := by
  simp [Union.union]

@[simp]
theorem mem_realize_inter_iff :
    z ∈ (r₁ ∩ r₂)〘xs〙 ↔ z ∈ r₁〘xs〙 ∧ z ∈ r₂〘xs〙 := by
  simp only [Inter.inter, realize_sdiff, not_and, not_not, and_congr_right_iff,
    Classical.imp_iff_right_iff]
  tauto

@[simp]
theorem mem_realize_symDiff_iff :
    z ∈ (r₁.symDiff r₂)〘xs〙 ↔ ¬(z ∈ r₁〘xs〙 ↔ z ∈ r₂〘xs〙) := by
  simp only [symDiff, mem_realize_union_iff, realize_sdiff]
  tauto

end RudBasisClosed

section IterSUnion₀

variable [RudBasisClosed M] (x y z a : M)

variable (r : L.RudimentaryBasisTerm n) (xs : Fin n → M)

noncomputable def iterSUnion₀ (k : ℕ) (a : M) := ((RudimentaryBasisTerm.var 0).iterSUnion₀ k)〘![a]〙

@[simp]
theorem iterSUnion₀_zero (a : M) : iterSUnion₀ 0 a = a := by
  simp [iterSUnion₀]

theorem iterSUnion₀_succ (k : ℕ) (a : M) : iterSUnion₀ (k + 1) a = iterSUnion₀ k (iterSUnion₀ 1 a) := by
  simp [iterSUnion₀, RudimentaryBasisTerm.iterSUnion₀, Matrix.const_fin1_eq]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryBasisTerm.realize_iterSUnion₀
    (k : ℕ) :
    (r.iterSUnion₀ k)〘xs〙 = iterSUnion₀ k (r〘xs〙 : M) := by
  induction k generalizing n r xs with
  | zero => simp [iterSUnion₀]
  | succ k ih =>
    rw [iterSUnion₀_succ]
    simp only [RudimentaryBasisTerm.iterSUnion₀, Nat.succ_eq_add_one, Nat.reduceAdd, isValue,
      realize_substBoundRudBasis, Matrix.cons_val_fin_one, ih, realize]
    rfl

theorem mem_iterSUnion₀_one_iff (a x : M) :
    x ∈ iterSUnion₀ 1 a ↔ x ∈ a ∨ ∃ y ∈ a, x ∈ y := by
  simp [iterSUnion₀, RudimentaryBasisTerm.iterSUnion₀, Union.union]

theorem iterSUnion₀_one_mono {a b : M} (hab : a ⊆ b) :
    iterSUnion₀ 1 a ⊆ iterSUnion₀ 1 b := by
  simp only [iterSUnion₀, Nat.succ_eq_add_one, Nat.reduceAdd, RudimentaryBasisTerm.iterSUnion₀,
    isValue, Union.union, realize_substBoundRudBasis, realize, Matrix.cons_val_fin_one, subset_iff,
    mem_sUnion₀_iff, mem_unorderedPair_iff, exists_eq_or_imp, ↓existsAndEq, true_and]
  grind

theorem iterSUnion₀_mono (k : ℕ) {a b : M} (hab : a ⊆ b) :
    iterSUnion₀ k a ⊆ iterSUnion₀ k b := by
  induction k generalizing a b with
  | zero => simp [hab]
  | succ k ih =>
    rw [iterSUnion₀_succ k, iterSUnion₀_succ k]
    apply ih
    apply iterSUnion₀_one_mono
    exact hab

theorem iterSUnion₀_mono' {k l : ℕ} (hkl : k ≤ l) (a : M) : iterSUnion₀ k a ⊆ iterSUnion₀ l a := by
  induction l with
  | zero => grind
  | succ l ih =>
    rcases Nat.le_or_eq_of_le_succ hkl with hkl | rfl
    · trans iterSUnion₀ l a
      · tauto
      · rw [iterSUnion₀_succ]
        apply iterSUnion₀_mono
        simp only [iterSUnion₀, Nat.succ_eq_add_one, Nat.reduceAdd,
          RudimentaryBasisTerm.iterSUnion₀, isValue, Union.union, realize_substBoundRudBasis,
          realize, Matrix.cons_val_fin_one, subset_iff, mem_sUnion₀_iff, mem_unorderedPair_iff,
          exists_eq_or_imp, ↓existsAndEq, true_and]
        grind
    · grind

theorem subset_iterSUnion₀ (a : M) :
    a ⊆ iterSUnion₀ k a := by
  convert iterSUnion₀_mono' (k := 0) (l := k) (a := a)
  simp

variable [L.ExtraConstantsUnaryRelationsOnly]

@[simp]
theorem Term.realize_substructure {n : ℕ} (t : L.Term' n)
    {N : Class M} {xs : Fin n → MemStructure.toSubstructure N} :
    t〘xs〙 = t〘fun i ↦ (xs i).val〙 := match t with
  | var (Sum.inr i) => by simp
  | func F _ (l := 0) => by
    simp only [Term.realize'_func, funMap]
    congr
    ext i
    fin_cases i
  | func F _ (l := l + 1) => IsEmpty.elim' (by infer_instance) F

theorem realize_class_iterSUnion₀_relDepth {n : ℕ} (φ : L.DeltaZeroBoundedFormula n)
    {xs : Fin n → M} {a : M}
    (ha : ∀ c : L.Constants, ↑c ∈ a)
    (hxs : ∀ i, xs i ∈ a)
    {N' : Class M} (hN' : (iterSUnion₀ φ.depth a (M := M) : Class M) ⊆ N')
    {xs' : Fin n → toSubstructure N'} (hxsxs' : ∀ i, xs' i = xs i) :
    φ.toBoundedFormula 〘xs'〙 ↔ φ.toBoundedFormula〘xs〙 := by
  induction φ generalizing a with
  | falsum => simp
  | equal t₁ t₂ => simp [hxsxs']
  | mem t₁ t₂ => simp [hxsxs']
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [depth_imp] at hN'
    have hN'₁ : (iterSUnion₀ φ₁.depth a (M := M) : Class M) ⊆ N' := by
      trans ↑(iterSUnion₀ (max φ₁.depth φ₂.depth) a)
      · apply iterSUnion₀_mono' (k := φ₁.depth) (by simp)
      · exact hN'
    have hN'₂ : (iterSUnion₀ φ₂.depth a (M := M) : Class M) ⊆ N' := by
      trans ↑(iterSUnion₀ (max φ₁.depth φ₂.depth) a)
      · apply iterSUnion₀_mono' (k := φ₂.depth) (by simp)
      · exact hN'
    simp [ih₁ (a := a) ha hxs hN'₁ hxsxs',  ih₂ (a := a) ha hxs hN'₂ hxsxs']
  | allMem t ψ ih =>
    simp only [toBoundedFormula, realize_allMem, toSubstructure_mem_iff, Term.realize_substructure,
      hxsxs', Subtype.forall]
    have ha' : ∀ (c : L.Constants), ↑c ∈ iterSUnion₀ 1 a := fun _ ↦ subset_iterSUnion₀ _ (ha _)
    have hda {d : M} (hd : d ∈ t〘xs〙) : d ∈ sUnion₀ a := match t with
      | var (Sum.inr i) => by
        simp only [Term.realize'_var'] at hd
        simp only [mem_sUnion₀_iff]
        exact ⟨xs i, hxs _, hd⟩
      | func c _ (l := 0) => by
        simp only [Term.realize'_func] at hd
        simp only [mem_sUnion₀_iff]
        refine ⟨↑c, ha _, ?_⟩
        convert hd
        simp [funMap_eq_coe_constants]
      | func F _ (l := l + 1) => IsEmpty.elim' (by infer_instance) F
    have hcN' {d : M} (hd : d ∈ t〘xs〙) : d ∈ toSubstructure N' := by
      apply mem_toSubstructure_of_mem
      apply hN'
      apply iterSUnion₀_mono' (k := 1) (by simp)
      simp only [mem_iterSUnion₀_one_iff]
      right
      simpa using hda hd
    have hxs' {d : M} (hd : d ∈ t〘xs〙) (i) : (snoc xs d : Fin _ → M) i  ∈ iterSUnion₀ 1 a := by
      cases i using lastCases with
      | last =>
        simp only [snoc_last, mem_iterSUnion₀_one_iff]
        right
        simpa using hda hd
      | cast i =>
        simp only [snoc_castSucc]
        apply iterSUnion₀_mono' (k := 0) (by decide)
        simp [hxs]
    have hxsxs' {d : M} (hd : d ∈ t〘xs〙) (i) :
        (snoc xs' ⟨d, hcN' hd⟩ : Fin _ → toSubstructure N') i = (snoc xs d : Fin _ → M) i := by
      cases i using lastCases with
      | last => simp
      | cast i => simp [hxsxs']
    have hN'' : ↑(iterSUnion₀ ψ.depth (iterSUnion₀ 1 a)) ⊆ N' := by
      simp only [depth_allMem] at hN'
      rwa [iterSUnion₀_succ] at hN'
    constructor
    · intro h d hd
      specialize h d (hcN' hd) (by simp [hd])
      rwa [← ih ha' (hxs' hd) hN'' (hxsxs' hd)]
    · intro h d hdN' hd
      specialize h d hd
      rwa [ih ha' (hxs' hd) hN'' (hxsxs' hd)]
  | rel R t => simp [RelMap, hxsxs', Matrix.const_fin1_eq]

theorem realize_mem_iterSUnion₀_relDepth {n : ℕ} (φ : L.DeltaZeroBoundedFormula n)
    {xs : Fin n → M} {a : M}
    (ha : ∀ c : L.Constants, ↑c ∈ a)
    (hxs : ∀ i, xs i ∈ a)
    {b : M} (hb : iterSUnion₀ φ.depth a ⊆ b)
    {xs' : Fin n → toSubstructure (toClass b)} (hxsxs' : ∀ i, xs' i = xs i) :
    φ.toBoundedFormula 〘xs'〙 ↔ φ.toBoundedFormula〘xs〙 := by
  rw [realize_class_iterSUnion₀_relDepth φ ha hxs hb hxsxs' (N' := toClass b)]

end IterSUnion₀

section Tuple

variable (r r₁ r₂ s : L.RudimentaryBasisTerm n) (xs : Fin n → M) {l : ℕ} (ys : Fin (l + 1) → M)

@[simp]
theorem orderedPair_eq : (r.orderedPair s)〘xs〙 = !((r〘xs〙 : M), s〘xs〙) := by
  simp [RudimentaryBasisTerm.orderedPair, orderedPair]

noncomputable def tuple {l} (xs : Fin l → M) : M := match l with
  | 0 => default  -- junk value
  | 1 => xs 0
  | _ + 2 => !(tuple (xs ∘ castSucc), (xs (last _)))

@[simp]
theorem tuple_one (xs : Fin 1 → M) : tuple xs = xs 0 := rfl

theorem tuple_succ (xs : Fin (l + 2) → M) :
    tuple xs = !(tuple (xs ∘ castSucc), (xs (last _))) := rfl

theorem tuple_snoc {l} (hl : l ≠ 0) (xs : Fin l → M) (x : M) :
    tuple (snoc xs x) = !(tuple xs, x) :=
  match l with
  | 0 => by omega
  | 1 => by simp [tuple, snoc]
  | l + 2 => by simp [tuple]

theorem tuple_cast (xs : Fin l → M) (h : m = l) :
    tuple (xs ∘ Fin.cast h) = tuple xs := by
  subst h; simp

variable [Extensional M] [RudBasisClosed M]

theorem tuple_cons_tuple {m} (hm : m ≠ 0) (xs : Fin l → M) (ys : Fin m → M) :
    tuple (cons (tuple ys) xs) = tuple (append ys xs) := by
  induction l with
  | zero => simp [append_right_nil]
  | succ l ih =>
    nth_rw 2 [← snoc_init_self xs]
    simp only [tuple_succ, cons_last]
    set xs₀ := init xs
    set x := xs (last _)
    simp only [append_snoc, Nat.add_eq]
    rw [tuple_snoc (by omega)]
    simp only [← ih, orderedPair_eq_orderedPair_iff, and_true]
    congr 1
    funext i
    nth_rw 1 [← snoc_init_self xs]
    grind [snoc_nat, cons_nat]

theorem tuple_congr (xs : Fin l → M) (ys : Fin l → M) :
    tuple xs = tuple ys ↔ ∀ i, xs i = ys i := by
  induction l with
  | zero => simp [tuple]
  | succ l ih =>
    cases l with
    | zero => simp
    | succ l' =>
      nth_rw 1 [← snoc_init_self xs, ← snoc_init_self ys, tuple_snoc (by omega), tuple_snoc (by omega)]
      rw [forall_iff_castSucc]
      simp only [orderedPair_eq_orderedPair_iff, ih, init]
      tauto

theorem _root_.FirstOrder.Language.RudimentaryBasisTerm.realize_tuple
    (rs : Fin (l + 1) → L.RudimentaryBasisTerm n) :
    (RudimentaryBasisTerm.tuple rs)〘xs〙 = tuple (fun i ↦ ((rs i)〘xs〙 : M)) := by
  induction l with
  | zero => simp [tuple, RudimentaryBasisTerm.tuple]
  | succ l ih =>
    simp only [RudimentaryBasisTerm.tuple, orderedPair_eq, ih, tuple,
      orderedPair_eq_orderedPair_iff, and_true]
    rfl

noncomputable def IsTuple (z : M) (l : ℕ) := ∃ ys : Fin l → M, z = tuple ys

omit [Extensional M] [RudBasisClosed M] in
@[simp]
theorem isTuple_tuple (xs : Fin l → M) : IsTuple (tuple xs) l := ⟨xs, rfl⟩

omit [Extensional M] [RudBasisClosed M] in
@[simp]
theorem isTuple_one (z : M) : IsTuple z 1 := ⟨![z], rfl⟩

omit [Extensional M] [RudBasisClosed M] in
@[simp]
theorem isOrderedPair_of_isTuple {z : M} (hz : IsTuple z (l + 2)) :
    IsOrderedPair z := by
  obtain ⟨ys, rfl⟩ := hz
  use tuple (ys ∘ castSucc), ys (last _)
  rw [tuple]

omit [Extensional M] [RudBasisClosed M] in
@[simp]
theorem isTuple_two_iff_isOrderedPair (z : M) : IsTuple z 2 ↔ IsOrderedPair z := by
  simp only [IsTuple, tuple, Nat.reduceAdd, isValue, Function.comp_apply, castSucc_zero, reduceLast,
    IsOrderedPair]
  constructor
  · rintro ⟨ys, rfl⟩
    use ys 0, ys 1
  · rintro ⟨x, y, rfl⟩
    use ![x, y]
    simp

@[simp]
theorem isTuple_unorderedPair_iff (z w : M) (hl : l ≠ 0) :
    IsTuple !(z, w) (l + 1) ↔ IsTuple z l := by
  simp only [IsTuple]
  constructor
  · rintro ⟨ys, hys⟩
    use ys ∘ castSucc
    rw [← snoc_init_self ys, tuple_snoc hl, orderedPair_eq_orderedPair_iff] at hys
    convert hys.left
    grind [init]
  · rintro ⟨ys, rfl⟩
    use snoc ys w
    simp [tuple_snoc, hl]


omit [Extensional M] [RudBasisClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryBasisTerm.realize_singleton :
    {r}〘xs〙 = {r〘xs〙} := by
  simp [Singleton.singleton]

-- TODO: move to Singleton.lean
@[simp]
theorem all_mem_iff_eq_iff_singleton (u w : M) :
    (∀ (v : M), v ∈ u ↔ v = w) ↔ u = {w} := by
  rw [eq_iff]
  simp

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryBasisTerm.realize_left (h : r〘xs〙 = !(z, w)) :
    (r.left)〘xs〙 = z := by
  simp only [left, left₀, RudimentaryBasisTerm.realize.eq_8, RudimentaryBasisTerm.realize,
    RudimentaryBasisTerm.realize_singleton]
  ext u
  simp [h]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryBasisTerm.realize_right (h : r〘xs〙 = !(z, w)) :
    (r.right)〘xs〙 = w := by
  simp only [right, right₀, RudimentaryBasisTerm.realize, RudimentaryBasisTerm.realize_singleton]
  ext u
  simp [h]

noncomputable def tupleVal (z : M) (i : Fin l) : M :=
  ((.var 0 : L.RudimentaryBasisTerm 1).tupleVal i)〘![z]〙

@[simp]
theorem tupleVal_orderedPair_last (z w : M) (hl : l ≠ 0) :
    tupleVal !(z, w) (last l) = w := by
  simp only [tupleVal, isValue, RudimentaryBasisTerm.tupleVal, snoc_last]
  have : (RudimentaryBasisTerm.var 0)〘![!(z, w)]〙 = !(z, w) := by simp
  rw [realize_right _ _ this]

@[simp]
theorem tupleVal_orderedPair_castSucc (z w : M) (hl : l ≠ 0) (i : Fin l) :
    tupleVal !(z, w) i.castSucc = tupleVal z i := by
  have : (RudimentaryBasisTerm.var 0)〘![!(z, w)]〙 = !(z, w) := by simp
  simp only [tupleVal, isValue, RudimentaryBasisTerm.tupleVal, snoc_castSucc]
  rw [tupleVal_eq_substBoundRudBasis]
  simp only [isValue, realize_substBoundRudBasis, Matrix.cons_val_fin_one]
  rw [realize_left _ _ this]
  congr
  funext i; fin_cases i; simp

-- @[simp]
theorem tupleVal_orderedPair_eq_snoc_tupleval (z w : M) (hl : l ≠ 0) :
    tupleVal (l := l + 1) !(z, w) = snoc (tupleVal z) w := by
  ext i
  cases i using lastCases with
  | last => simp [hl]
  | cast i => simp [hl]

@[simp]
theorem tupleVal_orderedPair_comp_castSucc (z w : M) (hl : l ≠ 0) :
    (tupleVal (l := l + 1) !(z, w)) ∘ castSucc = tupleVal z := by
  ext i
  simp [hl]

@[simp]
theorem tupleVal_orderedPair_zero (z w : M) :
    tupleVal !(z, w) (0 : Fin (l + 2)) = tupleVal z (0 : Fin (l + 1)) := by
  convert tupleVal_orderedPair_castSucc (M := M) _ _ _ _ <;> simp

@[simp]
theorem tupleVal_orderedPair_succ_castSucc (z w : M) (i : Fin l) :
    tupleVal !(z, w) i.castSucc.succ = tupleVal z i.succ := by
  rw [show i.castSucc.succ = i.succ.castSucc by simp,
    tupleVal_orderedPair_castSucc (hl := by omega)]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryBasisTerm.realize_tupleVal (i : Fin l) :
    (r.tupleVal i)〘xs〙 = tupleVal (r〘xs〙 : M) i := by
  rw [tupleVal_eq_substBoundRudBasis]
  simp only [isValue, realize_substBoundRudBasis, Matrix.cons_val_fin_one, tupleVal]
  congr
  ext i; fin_cases i; simp

@[simp]
theorem tupleVal_tuple (xs : Fin l → M) (i : Fin l) :
    tupleVal (tuple xs) i = xs i := by
  induction l with
  | zero => exact elim0 i
  | succ l ih =>
    cases l with
    | zero =>
      simp only [tupleVal, isValue, Nat.reduceAdd, RudimentaryBasisTerm.tupleVal, tuple_one,
        RudimentaryBasisTerm.realize.eq_1, Matrix.cons_val_fin_one]
      congr; omega
    | succ l =>
      simp only [tupleVal, isValue]
      have : (RudimentaryBasisTerm.var 0)〘![tuple xs]〙 =
          !(tuple (xs ∘ castSucc), xs (last _)) := by
        simp [tuple_succ]
      cases i using lastCases with
      | last => simp [RudimentaryBasisTerm.tupleVal, realize_right (h := this)]
      | cast i =>
        simp only [isValue, RudimentaryBasisTerm.tupleVal, snoc_castSucc]
        rw [realize_tupleVal, realize_left (h := this)]
        simp [ih]

@[simp]
theorem tupleVal_one (z : M) :
    tupleVal z (0 : Fin 1) = z := by
  convert tupleVal_tuple ![z] 0 <;> simp

@[simp]
theorem tupleVal_orderedPair_two_zero (z w : M) :
    tupleVal !(z, w) (0 : Fin 2) = z := by
  convert tupleVal_tuple ![z, w] 0 <;> simp [tuple]

@[simp]
theorem tupleVal_orderedPair_two_one (z w : M) :
    tupleVal !(z, w) (1 : Fin 2) = w := by
  convert tupleVal_tuple ![z, w] 1 <;> simp [tuple]

theorem eq_tuple_tupleVal {z : M} (hz : IsTuple z l) :
    z = tuple (fun i : Fin l ↦ tupleVal z i) := by
  obtain ⟨ys, hys⟩ := hz
  simp [hys]

@[simp]
theorem mem_realize_sPower_iff (z : M) (hl : l ≠ 0) :
    z ∈ (r.sPower l)〘xs〙 ↔ IsTuple z l ∧ (∀ i : Fin l, tupleVal z i ∈ r〘xs〙) := by
  induction l generalizing z with
  | zero => omega
  | succ l ih =>
    cases l with
    | zero => simp [sPower]
    | succ l =>
      simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        forall_const] at ih
      simp only [sPower, RudimentaryBasisTerm.realize.eq_5, mem_sprod₀_iff, ih]
      constructor
      · rintro ⟨ys, hys, v, hv, rfl⟩
        simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
          isTuple_unorderedPair_iff, hys, true_and]
        intro i
        cases i using lastCases with
        | last => simp [hv]
        | cast i => simp [hys]
      · rintro ⟨⟨ys, rfl⟩, hz⟩
        simp only [tupleVal_tuple] at hz
        use tuple (ys ∘ castSucc)
        constructor
        · simp [hz]
        · exact ⟨ys (last _), by simp [hz], by simp [tuple]⟩

@[simp]
theorem orderedPair_mem_realize_sPower_iff (hl : l ≠ 0) (x y : M) :
    !(x, y) ∈ (r.sPower (l + 1))〘xs〙 ↔ x ∈ (r.sPower l)〘xs〙 ∧ y ∈ r〘xs〙 := by
  rw [sPower]
  · simp only [RudimentaryBasisTerm.realize, mem_sprod₀_iff, orderedPair_eq_orderedPair_iff,
    exists_eq_right_right']
  · omega


theorem mem_realize_rotateSPower_iff (z : M) (h : ∀ x ∈ r〘xs〙, IsOrderedPair x) :
    z ∈ (r.rotateSPower l s)〘xs〙 ↔ IsTuple z (l + 2) ∧
      (∀ i : Fin l, tupleVal z (i.castAdd 2) ∈ s〘xs〙) ∧
      !(tupleVal z (last l).castSucc, tupleVal z (last (l + 1))) ∈ r〘xs〙 :=
  match l with
  | 0 => by
    simp only [rotateSPower, zero_add, isTuple_two_iff_isOrderedPair, Nat.reduceAdd,
      IsEmpty.forall_iff, last_zero, isValue, castSucc_zero, reduceLast, true_and]
    refine ⟨fun hz ↦ ?_, ?_⟩
    · obtain ⟨x, y, rfl⟩ := h z hz
      simp [IsOrderedPair, hz]
    · rintro ⟨⟨x, y, rfl⟩, hz⟩
      simpa using hz
  | l + 1 => by
    simp only [rotateSPower, RudimentaryBasisTerm.realize.eq_7, mem_rotate₀_iff, ne_eq,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, mem_realize_sPower_iff]
    constructor
    · rintro ⟨u, v, w, hw, huv, rfl⟩
      simp [hw, huv, Fin.castAdd, castLE_add_two_eq_castSucc_castSucc]
    · rintro ⟨hz₁, hz₂, hz₃⟩
      use tupleVal z (last (l + 1)).castSucc, tupleVal z (last (l + 2)),
        tuple (fun i : Fin (l + 1) ↦ tupleVal z (i.castAdd 2))
      simp only [isTuple_tuple, tupleVal_tuple, hz₂, implies_true, and_self, hz₃, true_and]
      rw [eq_tuple_tupleVal hz₁, tuple_succ, tuple_succ]
      simp [castAdd, castLE_add_two_eq_castSucc_castSucc, tuple_congr]

omit [Extensional M] in
theorem isOrderedPair_of_realize_memGraph (hz : z ∈ r.memGraph〘xs〙) : IsOrderedPair z := by
  simp only [RudimentaryBasisTerm.realize, mem_memGraph₀_iff, IsOrderedPair] at hz ⊢
  grind

theorem mem_realize_rotateSPower_memGraph_iff (z w : M) :
    !(z, w) ∈ (r.memGraph.rotateSPower l s)〘xs〙 ↔ IsTuple z (l + 1) ∧
      (∀ i : Fin l, tupleVal z i.castSucc ∈ s〘xs〙) ∧ tupleVal z (last l) ∈ r〘xs〙 ∧ w ∈ r〘xs〙 ∧
      w ∈ tupleVal z (last l) := by
  rw [mem_realize_rotateSPower_iff]
  · simp [castAdd, castLE_add_two_eq_castSucc_castSucc]
  · apply isOrderedPair_of_realize_memGraph

theorem mem_realize_iterSwitch_iff (z : M) (h : ∀ x ∈ r〘xs〙, IsOrderedPair x) :
    z ∈ (r.iterSwitch l s)〘xs〙 ↔ IsTuple z (l + 2) ∧
      (∀ i : Fin l, tupleVal z i.castSucc.succ ∈ s〘xs〙) ∧
      (!(tupleVal z (0 : Fin (l + 2)), tupleVal z (last (l + 1))) ∈ r〘xs〙) := by
  induction l generalizing z with
  | zero =>
    simp only [iterSwitch, zero_add, isTuple_two_iff_isOrderedPair, Nat.reduceAdd,
      IsEmpty.forall_iff, isValue, reduceLast, true_and]
    constructor
    · intro hz
      refine ⟨h z hz, ?_⟩
      convert hz
      obtain ⟨x, y, rfl⟩ := h z hz
      simp
    · rintro ⟨⟨x, y, rfl⟩, hz⟩
      simpa using hz
  | succ l ih =>
    simp only [iterSwitch, realize, mem_switch₀_iff, ih, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, not_false_eq_true, isTuple_unorderedPair_iff, tupleVal_orderedPair_succ_castSucc,
      tupleVal_orderedPair_zero, tupleVal_orderedPair_last]
    constructor
    · rintro ⟨u, v, w, hw₁, ⟨⟨hu₁, hu₂, hu₃⟩, rfl⟩⟩
      refine ⟨?_, ?_, ?_⟩
      · simp [hu₁]
      · intro i
        simp only [tupleVal_orderedPair_succ_castSucc]
        cases i using lastCases with
        | last => simp [hw₁]
        | cast i => simp [hu₂]
      · simp [hu₃]
    · rintro ⟨hz₁, hz₂, hz₃⟩
      use tuple (fun i : Fin (l + 1) ↦ tupleVal z (i.castAdd 2)),
        tupleVal z (last (l + 2)), tupleVal z (last (l + 1)).castSucc
      refine ⟨?_, ⟨by simp, ?_, ?_⟩, ?_⟩
      · convert hz₂ (last _)
        grind
      · intro i
        simp only [tupleVal_tuple]
        convert hz₂ i.castSucc
        grind
      · simp only [tupleVal_tuple]
        convert hz₃
        grind
      · rw [eq_tuple_tupleVal hz₁, tuple_succ, tuple_succ]
        simp [castAdd, castLE_add_two_eq_castSucc_castSucc, tuple_congr]

theorem mem_realize_lastMemFin_iff (i : Fin l) (z : M) :
    z ∈ (r.lastMemFin i)〘xs〙 ↔ IsTuple z (l + 1) ∧
      (∀ i : Fin (l + 1), tupleVal z i ∈ r〘xs〙) ∧ tupleVal z (last l) ∈ tupleVal z i.castSucc := by
  simp only [lastMemFin]
  rw [mem_realize_iterSwitch_iff]
  swap
  · intro x hx
    rw [mem_realize_rotateSPower_iff] at hx
    · exact isOrderedPair_of_isTuple hx.left
    · apply isOrderedPair_of_realize_memGraph
  simp only [mem_realize_rotateSPower_memGraph_iff]
  constructor
  · rintro ⟨⟨bs, rfl⟩, hbs₁, ⟨as, has₁⟩, hbs₂, hbs₃, hbs₄, hbs₅⟩
    rw [has₁] at hbs₂ hbs₃ hbs₅
    simp only [tupleVal_tuple] at *
    have : tuple bs = tuple ((append as (bs ∘ succ)) ∘ Fin.cast (n := l + 1) (by omega)) := by
      nth_rw 1 [← Fin.cons_self_tail bs]
      rw [has₁, tuple_cons_tuple (by omega), tuple_cast, tuple_congr]
      intro _
      rfl
    simp only [this, isTuple_tuple, tupleVal_tuple, Function.comp_apply, cast_castSucc, Nat.add_eq,
      cast_last, append_last, succ_last, Nat.succ_eq_add_one, true_and]
    refine ⟨?_, ?_⟩
    · suffices ∀ j, append as (bs ∘ succ) j ∈ r〘xs〙 from fun _ ↦ this _
      intro j
      cases j using addCases with
      | left j =>
        cases j using lastCases with
        | last => simp [hbs₃]
        | cast j => simp [hbs₂]
      | right j =>
        cases j using lastCases with
        | last => simp [hbs₄]
        | cast j => simp [hbs₁]
    · convert hbs₅
      grind [append_nat]
  · rintro ⟨⟨ys, rfl⟩, hys₁, hys₂⟩
    simp only [tupleVal_tuple] at hys₁ hys₂
    have : tuple ys = tuple (cons (tuple (ys ∘ Fin.castLE (n := i + 1) (by omega)))
        fun j : Fin (l - 1 - ↑i + 1) ↦ ys ⟨i + 1 + j.val, by omega⟩) := by
      rw [tuple_cons_tuple (by omega),
        ← tuple_cast ys (m := (i.val + 1 + (l - 1 - i.val + 1))) (by omega),
        tuple_congr]
      intro j
      cases j using addCases with
      | left j =>
        simp only [Function.comp_apply, append_left]
        congr 1
      | right j =>
        simp only [Function.comp_apply, append_right]
        congr
    simp only [this, isTuple_tuple, tupleVal_tuple, cons_succ, val_castSucc, hys₁, implies_true,
      cons_zero, Function.comp_apply, castLE_castSucc, cons_last, val_last, true_and]
    convert hys₂ <;> grind

theorem mem_realize_lastMemConst_iff (c : L.Constants) (z : M) :
    z ∈ (r.lastMemConst c l)〘xs〙 ↔ IsTuple z (l + 1) ∧
      (∀ i : Fin (l + 1), tupleVal z i ∈ r〘xs〙) ∧ tupleVal z (last l) ∈ (↑c : M) := by
  rcases l with rfl | l
  · simp only [lastMemConst, mem_realize_inter_iff, realize, zero_add, isTuple_one, Nat.reduceAdd,
    forall_fin_one, isValue, tupleVal_one, last_zero, true_and]
    tauto
  simp only [lastMemConst, realize, mem_sprod₀_iff, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, not_false_eq_true, mem_realize_sPower_iff, forall_iff_castSucc,
    mem_realize_inter_iff]
  constructor
  · rintro ⟨w, ⟨⟨ys, rfl⟩, ⟨hys₁, hys₂⟩⟩, u, hu, rfl⟩
    simp only [tupleVal_tuple, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, isTuple_unorderedPair_iff, isTuple_tuple, tupleVal_orderedPair_last,
      tupleVal_orderedPair_castSucc, true_and] at hys₁ hys₂ ⊢
    simp [hys₁, hys₂, hu]
  · rintro ⟨⟨w, rfl⟩, ⟨hw₁, hw₂, hw₃⟩, hw₄⟩
    simp only [tupleVal_tuple] at hw₁ hw₂ hw₃ hw₄ ⊢
    use tuple (w ∘ castSucc)
    simp only [isTuple_tuple, tupleVal_tuple, Function.comp_apply, hw₂, hw₃, implies_true, and_self,
      true_and]
    use w (last _)
    simp [hw₁, hw₄, tuple_succ]

variable [L.ExtraConstantsUnaryRelationsOnly]

theorem mem_realize_lastMem_iff (t : L.Term' l) (z : M) :
    z ∈ (r.lastMemTerm' t)〘xs〙 ↔ IsTuple z (l + 1) ∧
      (∀ i : Fin (l + 1), tupleVal z i ∈ r〘xs〙) ∧ tupleVal z (last l) ∈ t.castSucc〘tupleVal z〙 :=
  match t with
  | .var (Sum.inr i) => by
    simp [lastMemTerm', mem_realize_lastMemFin_iff]
  | .func F _ (l := 0) => by
    simp [lastMemTerm', mem_realize_lastMemConst_iff, funMap_eq_coe_constants]
  | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F

theorem realize_subset_unionConst : r〘xs〙 ⊆ (r.unionConst t)〘xs〙 :=
  match t with
  | .var (Sum.inr i) => by simp [unionConst, subset_iff]
  | .func F _ (l := 0) => by
    simp only [unionConst, subset_iff, mem_realize_union_iff, realize_singleton, realize, mem_singleton_iff]
    tauto
  | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F

theorem mem_realize_eq_iff (hl : l ≠ 0) (t₁ t₂ : L.Term' l) (z : M) :
    z ∈ (r.eq t₁ t₂)〘xs〙 ↔ IsTuple z l ∧
      (∀ k : Fin l, tupleVal z k ∈ r〘xs〙) ∧ t₁〘tupleVal z〙 = t₂〘tupleVal z〙 := by
  simp only [eq, isValue, realize_substBoundRudBasis, realize_sdiff, ne_eq, hl, not_false_eq_true,
    mem_realize_sPower_iff, realize, Matrix.cons_val_zero, mem_dom₀_iff, mem_realize_symDiff_iff,
    mem_realize_lastMem_iff, isTuple_unorderedPair_iff, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, realize_iterSUnion₀, forall_iff_castSucc, tupleVal_orderedPair_last,
    tupleVal_orderedPair_castSucc, Term.castSucc, Term.castAdd, Term.castLE, castLE_succ_castSucc,
    Term.realize'_substBoundBound, tupleVal_orderedPair_comp_castSucc, and_congr_right_iff, and_imp,
    Classical.not_imp, exists_and_left, not_and, not_exists, not_not]
  by_cases hz : IsTuple z l ∧ ∀ (k : Fin l), tupleVal z k ∈ r〘xs〙
  swap
  · grind
  obtain ⟨hz₁, hz₂⟩ := hz
  have hz₃ (k : Fin l) : tupleVal z k ∈ iterSUnion₀ 1 (((r.unionConst t₁).unionConst t₂)〘xs〙 : M) := by
    apply subset_iterSUnion₀
    apply realize_subset_unionConst
    apply realize_subset_unionConst
    apply hz₂
  simp only [hz₁, hz₂, implies_true, and_self, hz₃, forall_const, true_and,
    MemStructure.ext_iff]
  refine ⟨?_, by grind⟩
  intro h w
  by_cases hw : w ∈ (iterSUnion₀ 1 ((r.unionConst t₁).unionConst t₂)〘xs〙 : M)
  · exact h w hw
  have hw₁ : w ∉ t₁〘tupleVal z〙 :=
    match t₁ with
    | .var (Sum.inr i) => by
      contrapose! hw
      simp only [mem_iterSUnion₀_one_iff]
      right
      refine ⟨tupleVal z i, ?_, hw⟩
      apply realize_subset_unionConst
      apply realize_subset_unionConst
      apply hz₂
    | .func F _ (l := 0) => by
      contrapose! hw
      simp only [Term.realize'_func, funMap_eq_coe_constants] at hw
      simp only [mem_iterSUnion₀_one_iff]
      right
      refine ⟨↑F, ?_, hw⟩
      apply realize_subset_unionConst
      simp [unionConst]
    | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F
  have hw₂ : w ∉ t₂〘tupleVal z〙 :=
    match t₂ with
    | .var (Sum.inr i) => by
      contrapose! hw
      simp only [mem_iterSUnion₀_one_iff]
      right
      refine ⟨tupleVal z i, ?_, hw⟩
      apply realize_subset_unionConst
      apply realize_subset_unionConst
      apply hz₂
    | .func F _ (l := 0) => by
      contrapose! hw
      simp only [Term.realize'_func, funMap_eq_coe_constants] at hw
      simp only [mem_iterSUnion₀_one_iff]
      right
      refine ⟨↑F, ?_, hw⟩
      simp [unionConst]
    | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F
  tauto

theorem mem_realize_mem_iff (hl : l ≠ 0) (t₁ t₂ : L.Term' l) (z : M) :
    z ∈ (r.mem t₁ t₂)〘xs〙 ↔ IsTuple z l ∧
      (∀ k : Fin l, tupleVal z k ∈ r〘xs〙) ∧ t₁〘tupleVal z〙 ∈ t₂〘tupleVal z〙 := by
  simp only [RudimentaryBasisTerm.mem, Inter.inter, isValue, Function.comp_apply, Term.castSucc,
    Term.castAdd, Term.castLE, castLE_succ_castSucc, realize_substBoundRudBasis, realize_sdiff,
    ne_eq, hl, not_false_eq_true, mem_realize_sPower_iff, realize, Matrix.cons_val_zero,
    mem_dom₀_iff, Nat.add_eq_zero_iff, one_ne_zero, and_self, mem_realize_eq_iff,
    isTuple_unorderedPair_iff, Matrix.cons_val_one, Matrix.cons_val_fin_one, forall_iff_castSucc,
    tupleVal_orderedPair_last, tupleVal_orderedPair_castSucc, Term.realize'_var',
    Term.realize'_substBoundBound, tupleVal_orderedPair_comp_castSucc, mem_realize_lastMem_iff,
    not_and, and_imp, Classical.not_imp, not_not, ↓existsAndEq, and_true, forall_const]
  by_cases hz : IsTuple z l ∧ ∀ (k : Fin l), tupleVal z k ∈ r〘xs〙
  swap
  · grind
  obtain ⟨hz₁, hz₂⟩ := hz
  have hz₃ (k : Fin l) : tupleVal z k ∈ ((r.unionConst t₁)〘xs〙 : M) := by
    apply realize_subset_unionConst
    apply hz₂
  simp only [hz₁, hz₂, implies_true, and_self, hz₃, true_and, forall_const]
  refine ⟨by grind, fun h ↦ ?_⟩
  suffices t₁〘tupleVal z〙 ∈ ((r.unionConst t₁)〘xs〙 : M) by tauto
  exact match t₁ with
  | .var (Sum.inr i) => by
    apply realize_subset_unionConst
    apply hz₂
  | .func F _ (l := 0) => by
    simp [unionConst, funMap_eq_coe_constants]
  | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F

theorem realize_truth_iff (l : ℕ) (hl : l ≠ 0)
    (r : L.RudimentaryBasisTerm n) {φ : L.DeltaZeroBoundedFormula l}
    (hφ : φ.IsRelFree) (z : M) :
    z ∈ (r.truth φ)〘xs〙 ↔ IsTuple z l ∧
      (∀ k : Fin l, tupleVal z k ∈ r〘xs〙) ∧
      φ.toBoundedFormula〘tupleVal z〙 :=
  match φ with
  | .falsum => by simp [truth]
  | .equal t₁ t₂ => by simp [hl, truth, mem_realize_eq_iff]
  | .mem t₁ t₂ => by simp [hl, truth, mem_realize_mem_iff]
  | .imp φ₁ φ₂ => by
    simp only [isRelFree_imp] at hφ
    simp [hl, truth, realize_truth_iff l hl r hφ.left, realize_truth_iff l hl r hφ.right]
    tauto
  | .allMem t ψ => by
    simp only [isRelFree_allMem] at hφ
    simp only [truth, realize_sdiff, ne_eq, hl, not_false_eq_true, mem_realize_sPower_iff, realize,
      mem_dom₀_iff, mem_realize_lastMem_iff, isTuple_unorderedPair_iff, realize_iterSUnion₀,
      forall_iff_castSucc, tupleVal_orderedPair_last, tupleVal_orderedPair_castSucc, Term.castSucc,
      Term.castAdd, Term.castLE, castLE_succ_castSucc, Term.realize'_substBoundBound,
      tupleVal_orderedPair_comp_castSucc,
      realize_truth_iff (l + 1) (by omega) ((r.unionConst t).iterSUnion₀ 1) hφ, not_and, and_imp,
      not_exists, Classical.not_imp, not_not, toBoundedFormula, realize_allMem]
    by_cases hz : IsTuple z l ∧ ∀ (k : Fin l), tupleVal z k ∈ r〘xs〙
    swap
    · grind
    have h₁ {w : M} (hw : w ∈ (t〘tupleVal z〙 : M) ) : w ∈ iterSUnion₀ 1 ((r.unionConst t)〘xs〙 : M) := match t with
      | .var (Sum.inr i) => by
        simp only [unionConst, mem_iterSUnion₀_one_iff]
        simp only [Term.realize'_var'] at hw
        right
        refine ⟨tupleVal z i, ?_, hw⟩
        apply hz.right
      | .func F _ (l := 0) => by
        simp only [Term.realize'_func, funMap_eq_coe_constants] at hw
        simp [unionConst, mem_iterSUnion₀_one_iff, hw]
      | .func F _ (l := l + 1) => IsEmpty.elim (by infer_instance) F
    have hz₂ (k : Fin l) : tupleVal z k ∈ iterSUnion₀ 1 ((r.unionConst t)〘xs〙 : M) := by
      apply iterSUnion₀_mono (a := (r〘xs〙 : M)) 1 (by apply realize_subset_unionConst)
      apply subset_iterSUnion₀
      tauto
    simp only [hz, implies_true, and_self, hz₂, true_and, forall_const]
    constructor
    · intro h w hw
      specialize h w (h₁ hw) hw
      convert h.right
      simp [tupleVal_orderedPair_eq_snoc_tupleval, hl]
    · intro h w hw hwz
      refine ⟨hw, ?_⟩
      convert h w hwz
      simp [tupleVal_orderedPair_eq_snoc_tupleval, hl]




end Tuple

end MemStructure

end FirstOrder.Language
