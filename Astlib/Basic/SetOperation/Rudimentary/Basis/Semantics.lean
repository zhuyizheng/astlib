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

def IsInvMemGraph₀ (a x : M) := ∀ z, z ∈ a ↔ ∃ u ∈ x, ∃ v ∈ u, z = !(u, v)

noncomputable instance : Decidable (∃ a : M, IsInvMemGraph₀ a x) :=
  Classical.propDecidable _

noncomputable def invMemGraph₀ (x : M) :=
  dite (∃ a : M, IsInvMemGraph₀ a x) Classical.choose default

def IsSliceSet₀ (a x y : M) :=
  ∀ z, z ∈ a ↔ ∃ u ∈ y, ∀ v, v ∈ z ↔ !(u, v) ∈ x

noncomputable instance : Decidable (∃ a : M, IsSliceSet₀ a x y) :=
  Classical.propDecidable _

noncomputable def sliceSet₀ (x y : M) :=
  dite (∃ a : M, IsSliceSet₀ a x y) Classical.choose default

def IsInterRel₀ (a x : M) (R : L.Relations 1) :=
  ∀ z, z ∈ a ↔ z ∈ x ∧ RelMap R ![z]

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
  | .invMemGraph r => fun xs ↦ invMemGraph₀ (r.realize xs)
  | .sliceSet r₁ r₂ => fun xs ↦ sliceSet₀ (r₁.realize xs) (r₂.realize xs)
  | .interRel r R => fun xs ↦ interRel₀ (r.realize xs) R

scoped[FirstOrder.Language] notation:max
  r "〘" xs "〙" => RudimentaryBasisTerm.realize r xs


@[simp]
theorem realize_substBoundRudBasis (r : L.RudimentaryBasisTerm n) (rs : Fin n → L.RudimentaryBasisTerm m)
    (xs : Fin m → M) :
    (r.substBoundRudBasis rs)〘xs〙 = r〘fun i ↦ (rs i)〘xs〙〙 := by
  induction r generalizing m <;> simp [substBoundRudBasis, *]

section RudBasisClosed

variable (M) in
class RudBasisClosed : Prop extends PairClosed M, SDiffClosed M where
  sprodClosed : ∀ x y, ∃ a : M, IsSProd₀ a x y
  switchClosed : ∀ x y, ∃ a : M, IsSwitch₀ a x y
  rotateClosed : ∀ x y, ∃ a : M, IsRotate₀ a x y
  sUnionClosed : ∀ x, ∃ a : M, IsSUnion₀ a x
  domClosed : ∀ x, ∃ a : M, IsDom₀ a x
  invMemGraphClosed : ∀ x, ∃ a : M, IsInvMemGraph₀ a x
  sliceSetClosed : ∀ x y, ∃ a : M, IsSliceSet₀ a x y
  interRelClosed : ∀ x y, ∃ a : M, IsInterRel₀ a x y

variable [RudBasisClosed M] (x y z a : M)

@[simp]
theorem mem_realize_sdiff_iff {n : ℕ} (r₁ r₂ : L.RudimentaryBasisTerm n) (xs : Fin n → M) :
    z ∈ (r₁ \ r₂)〘xs〙 ↔ z ∈ r₁〘xs〙 ∧ z ∉ r₂〘xs〙 := by
  simp only [SDiff.sdiff, RudimentaryBasisTerm.realize]
  rw [← MemStructure.mem_sdiff_iff]
  rfl

@[simp]
theorem realize_sdiff_self [Extensional M] {n : ℕ} (r : L.RudimentaryBasisTerm n) (xs : Fin n → M) :
    (r \ r)〘xs〙 = ∅ := by
  ext
  simp

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
theorem mem_invMemGraph₀_iff : z ∈ invMemGraph₀ x ↔ ∃ u ∈ x, ∃ v ∈ u, z = !(u, v) := by
  simp only [invMemGraph₀, RudBasisClosed.invMemGraphClosed, ↓reduceDIte]
  rw [Classical.choose_spec (RudBasisClosed.invMemGraphClosed _)]

@[simp]
theorem mem_sliceSet₀_iff : z ∈ sliceSet₀ x y ↔ ∃ u ∈ y, ∀ v, v ∈ z ↔ !(u, v) ∈ x := by
  simp only [sliceSet₀, RudBasisClosed.sliceSetClosed, ↓reduceDIte]
  rw [Classical.choose_spec (RudBasisClosed.sliceSetClosed _ _)]

@[simp]
theorem mem_interRel₀_iff : z ∈ interRel₀ x R ↔ z ∈ x ∧ RelMap R ![z] := by
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
  simp only [Inter.inter, mem_realize_sdiff_iff]
  tauto

@[simp]
theorem mem_realize_symDiff_iff :
    z ∈ (r₁.symDiff r₂)〘xs〙 ↔ ¬(z ∈ r₁〘xs〙 ↔ z ∈ r₂〘xs〙) := by
  simp only [symDiff, mem_realize_union_iff, mem_realize_sdiff_iff]
  tauto

end RudBasisClosed

section IterSUnion₀

variable [RudBasisClosed M] (x y z a : M)

variable (r : L.RudimentaryBasisTerm n) (xs : Fin n → M)

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

end IterSUnion₀

section Tuple

variable (r r₁ r₂ s : L.RudimentaryBasisTerm n) (xs : Fin n → M) {l : ℕ} (ys : Fin (l + 1) → M)

@[simp]
theorem orderedPair_eq : (r.orderedPair s)〘xs〙 = !((r〘xs〙 : M), s〘xs〙) := by
  simp [RudimentaryBasisTerm.orderedPair, orderedPair]

noncomputable def tuple {l} (xs : Fin l → M) : M := match l with
  | 0 => ∅
  | 1 => xs 0
  | _ + 2 => !(tuple (xs ∘ castSucc), (xs (last _)))

@[simp]
theorem tuple_zero (xs : Fin 0 → M) : tuple xs = ∅ := rfl

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
theorem isTuple_zero_iff (z : M) : IsTuple z 0 ↔ z = ∅ := by
  simp [IsTuple]

omit [Extensional M] [RudBasisClosed M] in
@[simp]
theorem isTuple_one (z : M) : IsTuple z 1 := ⟨![z], rfl⟩

omit [Extensional M] [RudBasisClosed M] in
@[simp]
theorem isOrderedPair_of_isTuple {z : M} (hz : IsTuple z (l + 2)) :
    IsOrderedPair z := by
  obtain ⟨ys, rfl⟩ := hz
  exact ⟨_, _, tuple_succ ys⟩

omit [Extensional M] [RudBasisClosed M] in
@[simp]
theorem isTuple_two_iff_isOrderedPair (z : M) : IsTuple z 2 ↔ IsOrderedPair z := by
  simp only [IsTuple, tuple, Nat.reduceAdd, isValue, Function.comp_apply, castSucc_zero, reduceLast,
    IsOrderedPair]
  refine ⟨fun ⟨ys, h⟩ ↦ ⟨ys 0, ys 1, h⟩, ?_⟩
  rintro ⟨x, y, rfl⟩
  exact ⟨![x, y], by simp⟩

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
    exact ⟨snoc ys w, by simp [tuple_snoc, hl]⟩


omit [Extensional M] [RudBasisClosed M] in
@[simp]
theorem _root_.FirstOrder.Language.RudimentaryBasisTerm.realize_singleton :
    {r}〘xs〙 = {r〘xs〙} := by
  simp [Singleton.singleton]

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryBasisTerm.realize_left (h : r〘xs〙 = !(z, w)) :
    (r.left)〘xs〙 = z := by
  simp only [left, left₀, isValue, realize_substBoundRudBasis, realize, Matrix.cons_val_fin_one,
    realize_singleton]
  ext u
  simp [h]


@[simp]
theorem _root_.FirstOrder.Language.MemStructure.exists_slice (x y : M) :
    ∃ z : M, ∀ v, v ∈ z ↔ !(y, v) ∈ x := by
  let z' := sUnion₀ (sUnion₀ (x ∩ sprod₀ {y} (sUnion₀ (sUnion₀ x))))
  have : ∀ v, v ≠ y → (v ∈ z' ↔ !(y, v) ∈ x) := by
    simp only [ne_eq, mem_sUnion₀_iff, mem_inter_iff, mem_sprod₀_iff, mem_singleton_iff,
      exists_eq_left, ↓existsAndEq, and_true, mem_orderedPair_iff, z']
    intro v hvy₁
    refine ⟨by grind, fun hvy₂ ↦ ?_⟩
    use unorderedPair y v
    simp only [mem_unorderedPair_iff, or_true, and_true]
    use v
    simp only [hvy₂, true_and, or_true, and_true]
    use unorderedPair y v
    simp only [mem_unorderedPair_iff, or_true, and_true]
    use !(y, v)
    simp [hvy₂]
  by_cases hy : !(y, y) ∈ x
  · use ((RudimentaryBasisTerm.var 0) ∪ (RudimentaryBasisTerm.var 1))〘![z', {y}]〙
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, isValue, mem_realize_union_iff, realize,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mem_singleton_iff]
    grind
  · use z' \ {y}
    grind

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryBasisTerm.mem_realize_ran_iff :
    z ∈ r.ran〘xs〙 ↔ ∃ w, !(w, z) ∈ r〘xs〙 := by
  simp only [ran, ran₀, isValue, realize_substBoundRudBasis, realize, Matrix.cons_val_fin_one,
    mem_sUnion₀_iff, mem_sliceSet₀_iff, mem_dom₀_iff]
  constructor
  · rintro ⟨u, ⟨v, -, hv₂⟩, hu⟩
    exact ⟨v, (hv₂ z).mp hu⟩
  · rintro ⟨w, hwz⟩
    obtain ⟨u, hu⟩ := MemStructure.exists_slice (r〘xs〙 : M) w
    grind

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryBasisTerm.realize_right (h : r〘xs〙 = !(z, w)) :
    (r.right)〘xs〙 = w := by
  ext
  simp [right, h]

noncomputable def tupleVal (z : M) (i : Fin l) : M :=
  ((.var 0 : L.RudimentaryBasisTerm 1).tupleVal i)〘![z]〙


@[simp]
theorem tupleVal_orderedPair_last (z w : M) (hl : l ≠ 0) :
    tupleVal !(z, w) (last l) = w := by
  simp only [tupleVal, isValue, RudimentaryBasisTerm.tupleVal, snoc_last]
  exact realize_right _ _ (z := z) (by simp)

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

theorem tupleVal_orderedPair_eq_snoc_tupleval (z w : M) (hl : l ≠ 0) :
    tupleVal (l := l + 1) !(z, w) = snoc (tupleVal z) w := by
  ext i
  cases i using lastCases <;> simp [hl]

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
theorem tupleVal_orderedPair_comp_snoc_castAdd_two_last (z w : M) :
    tupleVal !(z, w) ∘ snoc (castAdd 2) (last (l + 1)) = snoc (tupleVal z ∘ castSucc) w := by
  funext i
  cases i using lastCases <;> simp [castAdd, castLE_add_two_eq_castSucc_castSucc]

@[simp]
theorem tupleVal_orderedPair_castAdd_one_last (z w : M) :
    tupleVal !(z, w) (castAdd 1 (last (l + 1))) = tupleVal z (last (l + 1)) := by
  rw [show castAdd 1 (last (l + 1)) = (last (l + 1)).castSucc by simp [castSucc] ]
  simp

@[simp]
theorem _root_.FirstOrder.Language.RudimentaryBasisTerm.realize_tupleVal (i : Fin l) :
    (r.tupleVal i)〘xs〙 = tupleVal (r〘xs〙 : M) i := by
  rw [tupleVal_eq_substBoundRudBasis]
  simp only [isValue, realize_substBoundRudBasis, Matrix.cons_val_fin_one, tupleVal]
  congr
  ext i; fin_cases i; simp

@[simp]
theorem tupleVal_tuple (xs : Fin l → M) :
    tupleVal (tuple xs) = xs := by
  ext i
  induction l with
  | zero => exact elim0 i
  | succ l ih =>
    cases l with
    | zero =>
      simp only [tupleVal, isValue, Nat.reduceAdd, RudimentaryBasisTerm.tupleVal, tuple_one,
        realize, Matrix.cons_val_fin_one]
      rw [← eq_iff_iff]
      congr
      omega
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
    tupleVal z = fun _ : Fin 1 ↦ z := by
  simpa [tuple_one] using tupleVal_tuple (fun _ : Fin 1 ↦ z)

@[simp]
theorem tupleVal_orderedPair_two_zero (z w : M) :
    tupleVal !(z, w) (0 : Fin 2) = z := by
  simp

@[simp]
theorem tupleVal_orderedPair_two_one (z w : M) :
    tupleVal !(z, w) (1 : Fin 2) = w := by
  rw [show !(z, w) = tuple ![z, w] by simp [tuple] ]
  simp

@[simp]
theorem tupleVal_orderedPair_comp_one (z w : M) :
    (tupleVal (l := 2) !(z, w)) ∘ (fun _ ↦ (1 : Fin 2)) = fun _ : Fin 1 ↦ w := by
  ext i; fin_cases i
  simp

theorem eq_tuple_tupleVal {z : M} (hz : IsTuple z l) :
    z = tuple (fun i : Fin l ↦ tupleVal z i) := by
  obtain ⟨ys, rfl⟩ := hz
  simp

@[simp]
theorem mem_realize_sProd_iff (z : M) (rs : Fin (l + 1) → L.RudimentaryBasisTerm n) :
    z ∈ (sProd rs)〘xs〙 ↔ IsTuple z (l + 1) ∧ (∀ i, tupleVal z i ∈ (rs i)〘xs〙) := by
  induction l generalizing z with
  | zero =>
    simp [sProd]
  | succ l ih =>
    simp only [sProd, realize, mem_sprod₀_iff, ih, Function.comp_apply]
    constructor
    · rintro ⟨ys, hys, v, hv, rfl⟩
      simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        isTuple_unorderedPair_iff, hys, true_and]
      intro i
      cases i using lastCases <;> simp [hv, hys]
    · rintro ⟨⟨ys, rfl⟩, hz⟩
      simp only [tupleVal_tuple] at hz
      exact ⟨tuple (ys ∘ castSucc), by simp [hz], ys (last _), by simp [hz], by simp [tuple]⟩

@[simp]
theorem orderedPair_mem_realize_sProd_iff (rs : Fin (l + 2) → L.RudimentaryBasisTerm n) (x y : M) :
    !(x, y) ∈ (sProd rs)〘xs〙 ↔ x ∈ (sProd (rs ∘ castSucc))〘xs〙 ∧ y ∈ (rs (last _))〘xs〙 := by
  simp [sProd]

theorem mem_realize_rotateSProd_iff (rs : Fin l → L.RudimentaryBasisTerm n)
    (z : M) (h : ∀ x ∈ r〘xs〙, IsOrderedPair x) :
    z ∈ (r.rotateSProd rs)〘xs〙 ↔ IsTuple z (l + 2) ∧
      (∀ i, tupleVal z (i.castAdd 2) ∈ (rs i)〘xs〙) ∧
      !(tupleVal z (last l).castSucc, tupleVal z (last (l + 1))) ∈ r〘xs〙 :=
  match l with
  | 0 => by
    simp only [rotateSProd, zero_add, isTuple_two_iff_isOrderedPair, Nat.reduceAdd,
      IsEmpty.forall_iff, last_zero, isValue, castSucc_zero, reduceLast, true_and]
    refine ⟨fun hz ↦ ?_, ?_⟩
    · obtain ⟨x, y, rfl⟩ := h z hz
      simp [IsOrderedPair, hz]
    · rintro ⟨⟨x, y, rfl⟩, hz⟩
      simpa using hz
  | l + 1 => by
    simp only [rotateSProd, realize, mem_rotate₀_iff, mem_realize_sProd_iff]
    constructor
    · rintro ⟨u, v, w, hw, huv, rfl⟩
      simp [hw, huv, Fin.castAdd, castLE_add_two_eq_castSucc_castSucc]
    · rintro ⟨hz₁, hz₂, hz₃⟩
      refine ⟨tupleVal z (last (l + 1)).castSucc, tupleVal z (last (l + 2)),
        tuple (fun i : Fin (l + 1) ↦ tupleVal z (i.castAdd 2)), by simp [hz₂], hz₃, ?_⟩
      rw [eq_tuple_tupleVal hz₁, tuple_succ, tuple_succ]
      simp [castAdd, castLE_add_two_eq_castSucc_castSucc, tuple_congr]

omit [Extensional M] in
theorem isOrderedPair_of_realize_memGraph (hz : z ∈ r.invMemGraph〘xs〙) : IsOrderedPair z := by
  simp only [realize, mem_invMemGraph₀_iff, IsOrderedPair] at hz ⊢
  grind

theorem mem_realize_rotateSProd_memGraph_iff (rs : Fin l → L.RudimentaryBasisTerm n) (z w : M) :
    !(z, w) ∈ (r.invMemGraph.rotateSProd rs)〘xs〙 ↔ IsTuple z (l + 1) ∧
      (∀ i, tupleVal z i.castSucc ∈ (rs i)〘xs〙) ∧ tupleVal z (last l) ∈ r〘xs〙 ∧
      w ∈ tupleVal z (last l) := by
  rw [mem_realize_rotateSProd_iff]
  · simp [castAdd, castLE_add_two_eq_castSucc_castSucc]
  · apply isOrderedPair_of_realize_memGraph

theorem mem_realize_iterSwitch_iff (rs : Fin l → L.RudimentaryBasisTerm n)
    (z : M) (h : ∀ x ∈ r〘xs〙, IsOrderedPair x) :
    z ∈ (r.iterSwitch rs)〘xs〙 ↔ IsTuple z (l + 2) ∧
      (∀ i, tupleVal z i.castSucc.succ ∈ (rs i)〘xs〙) ∧
      (!(tupleVal z (0 : Fin (l + 2)), tupleVal z (last (l + 1))) ∈ r〘xs〙) := by
  induction l generalizing z with
  | zero =>
    simp only [iterSwitch, zero_add, isTuple_two_iff_isOrderedPair, Nat.reduceAdd,
      IsEmpty.forall_iff, isValue, reduceLast, true_and]
    refine ⟨fun hz ↦ ?_, ?_⟩
    · obtain ⟨x, y, rfl⟩ := h z hz
      simp [IsOrderedPair, hz]
    · rintro ⟨⟨x, y, rfl⟩, hz⟩
      simpa using hz
  | succ l ih =>
    simp only [iterSwitch, realize, mem_switch₀_iff, ih, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, not_false_eq_true, isTuple_unorderedPair_iff, Function.comp_apply,
      tupleVal_orderedPair_succ_castSucc, tupleVal_orderedPair_zero, tupleVal_orderedPair_last]
    constructor
    · rintro ⟨u, v, w, hw₁, ⟨⟨hu₁, hu₂, hu₃⟩, rfl⟩⟩
      refine ⟨by simp [hu₁], fun i ↦ ?_, by simp [hu₃]⟩
      simp only [tupleVal_orderedPair_succ_castSucc]
      cases i using lastCases <;> simp [hw₁, hu₂]
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

theorem mem_realize_lastMemFin_iff (rs : Fin l → L.RudimentaryBasisTerm n) (i : Fin l) (z : M) :
    z ∈ (lastMemFin i rs)〘xs〙 ↔ IsTuple z (l + 1) ∧
      (∀ j, tupleVal z j.castSucc ∈ (rs j)〘xs〙) ∧ tupleVal z (last l) ∈ tupleVal z i.castSucc := by
  rw [lastMemFin, mem_realize_iterSwitch_iff]
  swap
  · intro x hx
    rw [mem_realize_rotateSProd_iff] at hx
    · exact isOrderedPair_of_isTuple hx.left
    · apply isOrderedPair_of_realize_memGraph
  simp only [mem_realize_rotateSProd_memGraph_iff, Function.comp_apply]
  constructor
  · rintro ⟨⟨bs, rfl⟩, hbs₁, ⟨as, has₁⟩, hbs₂, hbs₃, hbs₄⟩
    rw [has₁] at hbs₂ hbs₃ hbs₄
    simp only [tupleVal_tuple] at *
    have : tuple bs = tuple ((append as (bs ∘ succ)) ∘ Fin.cast (n := l + 1) (by omega)) := by
      nth_rw 1 [← Fin.cons_self_tail bs]
      rw [has₁, tuple_cons_tuple (by omega), tuple_cast, tuple_congr]
      exact fun _ ↦ rfl
    simp only [this, isTuple_tuple, tupleVal_tuple, Function.comp_apply, cast_castSucc, Nat.add_eq,
      cast_last, append_last, succ_last, Nat.succ_eq_add_one, true_and]
    refine ⟨fun j ↦ ?_, ?_⟩
    · by_cases hj : j.val < i.val + 1
      · simp only [append_nat, val_castSucc, val_cast, hj, ↓reduceDIte]
        by_cases hj₁ : j = i
        · simp only [hj₁]
          convert hbs₃ using 3
          simp
        · convert hbs₂ ⟨j.val, by omega⟩ using 3 <;> simp
      · simp only [append_nat, val_castSucc, val_cast, hj, ↓reduceDIte, Function.comp_apply,
        succ_mk]
        convert hbs₁ ⟨j.val - (i.val + 1), by omega⟩
        · grind
        · simp
    · convert hbs₄
      grind [append_nat]
  · rintro ⟨⟨ys, rfl⟩, hys₁, hys₂⟩
    simp only [tupleVal_tuple] at hys₁ hys₂
    have : tuple ys = tuple (cons (tuple (ys ∘ Fin.castLE (n := i + 1) (by omega)))
        fun j : Fin (l - (i.val + 1) + 1) ↦ ys ⟨i + 1 + j.val, by omega⟩) := by
      rw [tuple_cons_tuple (by omega),
        ← tuple_cast ys (m := (i.val + 1 + (l - (i.val + 1) + 1))) (by omega),
        tuple_congr]
      intro j
      cases j using addCases <;> simp only [Function.comp_apply, append_left, append_right] <;>
        congr 1
    simp only [this, isTuple_tuple, tupleVal_tuple, cons_succ, val_castSucc, cons_zero,
      Function.comp_apply, castLE_castSucc, cons_last, val_last, Order.add_one_le_iff, is_lt,
      add_tsub_cancel_of_le, true_and]
    refine ⟨fun _ ↦ hys₁ _, fun _ ↦ hys₁ _, hys₁ _, ?_⟩
    convert hys₂ <;> grind

theorem mem_realize_lastMemConst_iff (rs : Fin l → L.RudimentaryBasisTerm n) (c : L.Constants) (z : M) :
    z ∈ (lastMemConst c rs)〘xs〙 ↔ IsTuple z (l + 1) ∧
      (∀ i, tupleVal z i.castSucc ∈ (rs i)〘xs〙) ∧ tupleVal z (last l) ∈ (↑c : M) := by
  rcases l with rfl | l
  · simp only [lastMemConst, Nat.reduceAdd, mem_realize_sProd_iff, zero_add, isTuple_one,
    forall_fin_one, isValue, tupleVal_one, true_and, IsEmpty.forall_iff, last_zero]
    tauto
  simp only [lastMemConst, mem_realize_sProd_iff, forall_iff_castSucc, snoc_last, realize,
    snoc_castSucc, and_congr_right_iff]
  grind

variable [L.ExtraConstantsUnaryRelationsOnly]

mutual
theorem mem_realize_lastMemRud_iff_aux {l n} (t : L.RudimentaryTerm l) (rs : Fin l → L.RudimentaryBasisTerm n)
    (xs : Fin n → M) (z : M) :
    match t with
    | .iUnion ri rf => z ∈ (lastMemRud t rs)〘xs〙 ↔ IsTuple z (l + 1) ∧
      (∀ i, tupleVal z i.castSucc ∈ (rs i)〘xs〙) ∧
      ∃ w ∈ ri〘tupleVal z ∘ castSucc〙, tupleVal z (last l) ∈ rf〘snoc (tupleVal z ∘ castSucc) w〙
    | _ => z ∈ (lastMemRud t rs)〘xs〙 ↔ IsTuple z (l + 1) ∧
      (∀ i, tupleVal z i.castSucc ∈ (rs i)〘xs〙) ∧ tupleVal z (last l) ∈ t〘tupleVal z ∘ castSucc〙 :=
  match t with
  | .var i => by simp [lastMemRud, mem_realize_lastMemFin_iff]
  | .const c => by simp [lastMemRud, mem_realize_lastMemConst_iff]
  | .unorderedPair t₁ t₂ => by
    simp only [lastMemRud, mem_realize_union_iff, mem_realize_lastEqRud_iff t₁,
      mem_realize_lastEqRud_iff t₂, RudimentaryTerm.realize_unorderedPair,
      mem_unorderedPair_iff]
    grind
  | .sdiff t₁ t₂ => by
    simp only [lastMemRud, mem_realize_sdiff_iff, mem_realize_lastMemRud_iff t₁,
      mem_realize_lastMemRud_iff t₂, not_and, RudimentaryTerm.realize_sdiff', mem_sdiff_iff]
    grind
  | .iUnion ri rf => match l with
    | 0 => by
      simp only [lastMemRud, Nat.reduceAdd, snoc_zero, last_zero, isValue, reduceCastAdd,
        reduceLast, realize, mem_dom₀_iff, mem_realize_inter_iff,
        mem_realize_lastMemRud_iff ri.castSucc, zero_add, isTuple_two_iff_isOrderedPair, ne_eq,
        one_ne_zero, not_false_eq_true, tupleVal_orderedPair_castSucc, tupleVal_one,
        mem_realize_ran_iff, mem_realize_lastMemRud_iff rf, mem_realize_lastMemRud_iff ri,
        isTuple_one, IsEmpty.forall_iff, true_and, forall_const, tupleVal_orderedPair_comp_castSucc,
        tupleVal_orderedPair_two_one,
        mem_realize_memGraph_iff (ᵣ0) (rf.substBoundBound (fun _ ↦ 1)), snoc_nat, Order.lt_one_iff,
        val_eq_zero_iff, dite_eq_ite, forall_iff_castSucc, one_eq_zero_iff, OfNat.ofNat_ne_one,
        ↓reduceIte, castSucc_eq_zero_iff, and_true, RudimentaryTerm.realize_substBoundBound,
        tupleVal_orderedPair_comp_one, RudimentaryTerm.realize_basic, tupleVal_orderedPair_zero]
      simp only [RudimentaryTerm.castSucc, RudimentaryTerm.castAdd, Nat.reduceAdd,
        RudimentaryTerm.realize_castLE, Unique.eq_default]
      grind
    | l + 1 => by
      simp only [lastMemRud, realize, mem_dom₀_iff, mem_realize_inter_iff,
        mem_realize_lastMemRud_iff ri.castSucc, ne_eq, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero,
        and_false, not_false_eq_true, isTuple_unorderedPair_iff, one_ne_zero, and_self,
        tupleVal_orderedPair_castSucc, forall_iff_castSucc (n := l + 1), snoc_last,
        mem_realize_ran_iff, mem_realize_lastMemRud_iff rf, mem_realize_lastMemRud_iff ri,
        tupleVal_orderedPair_comp_castSucc, tupleVal_orderedPair_last, snoc_castSucc,
        mem_realize_memGraph_iff (ᵣcastAdd 1 (last (l + 1)))
            (rf.substBoundBound (snoc (castAdd 2) (last (l + 2)))),
        forall_iff_castSucc (n := l + 2), RudimentaryTerm.realize_substBoundBound,
        tupleVal_orderedPair_comp_snoc_castAdd_two_last, RudimentaryTerm.realize_basic]
      simp only [RudimentaryTerm.castSucc, RudimentaryTerm.castAdd, RudimentaryTerm.realize_castLE,
        castLE_succ_castSucc, tupleVal_orderedPair_castAdd_one_last]
      refine ⟨by grind, ?_⟩
      rintro ⟨hz₁, hz₂, y, hy, hz₃⟩
      have hy₁ : ∃ w, IsTuple w (l + 1) ∧ (∀ i, tupleVal w i ∈ ((rs i)〘xs〙 : M)) ∧
          y ∈ ri〘tupleVal w〙 :=
        ⟨tuple (tupleVal (l := l + 2) z ∘ castSucc), by simp [hz₂, hy]⟩
      refine ⟨y, ⟨hz₁, ⟨?h, hz₂⟩, hy⟩, hz₁, ⟨hy₁, ?h, hz₂⟩, hz₃⟩
      exact ⟨tuple (snoc (tupleVal (l := l + 2) z ∘ castSucc) y), by simp [hy₁, hz₂, hz₃]⟩
  | .char R r => match l with
    | 0 => by
      simp only [lastMemRud, realize, realize_singleton, realize_sdiff_self, mem_dom₀_iff,
        mem_sprod₀_iff, mem_singleton_iff, mem_realize_inter_iff, mem_interRel₀_iff,
        mem_realize_image_iff r, isTuple_zero_iff, IsEmpty.forall_iff, true_and, exists_eq_left,
        mem_realize_lastEqRud_iff r, zero_add, isTuple_one, Nat.reduceAdd, tupleVal_one, last_zero,
        isValue, orderedPair_eq_orderedPair_iff, exists_eq_right_right', exists_and_right,
        ↓existsAndEq, RudimentaryTerm.realize_char, Unique.eq_default]
      grind
    | l + 1 => by
      simp only [lastMemRud, realize, realize_singleton, realize_sdiff_self, mem_sprod₀_iff,
        mem_dom₀_iff, mem_realize_inter_iff, mem_realize_sProd_iff, ne_eq, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, not_false_eq_true, isTuple_unorderedPair_iff,
        forall_iff_castSucc (n := l + 1), snoc_last, tupleVal_orderedPair_last, mem_interRel₀_iff,
        snoc_castSucc, tupleVal_orderedPair_castSucc, mem_singleton_iff, exists_eq_left,
        RudimentaryTerm.realize_char, mem_realize_lastEqRud_iff r,
        tupleVal_orderedPair_comp_castSucc, ↓existsAndEq, and_true]
      constructor
      · rintro ⟨u, ⟨⟨hu, ⟨-, hR⟩, hu₂⟩, -⟩, rfl⟩
        simp [hu, hu₂, hR]
      rintro ⟨⟨ys, rfl⟩, hz₂, hz₃⟩
      split_ifs at hz₃ with hR
      swap
      · simp at hz₃
      simp only [tupleVal_tuple, mem_unorderedPair_iff, or_self] at hz₂ hR hz₃
      refine ⟨tuple (ys ∘ castSucc), ?_, ?_⟩
      · simp only [isTuple_tuple, tupleVal_tuple, mem_realize_image_iff r, hR, and_true,
          Function.comp_apply, hz₂, implies_true, true_and, and_self]
        exact ⟨tuple (ys ∘ castSucc), by simp [hz₂]⟩
      · rw [tuple_succ]
        simp [hz₃]
termination_by (t.depth, 0)
decreasing_by all_goals simp [RudimentaryTerm.depth, Prod.lex_def, RudimentaryTerm.castSucc, RudimentaryTerm.castAdd,
  RudimentaryTerm.castLE]

theorem exists_iUnion {l} (ri : L.RudimentaryTerm l)
    (rf : L.RudimentaryTerm (l + 1)) (xs : Fin l → M) :
    ∃ a, IsIUnion (M := M) a ri〘xs〙 fun y ↦ rf〘snoc xs y〙 :=
  match l with
  | 0 => by
    use (lastMemRud (ri.iUnion rf) (fun i ↦ .var i))〘fun i ↦ {xs i}〙
    simp only [IsIUnion, mem_realize_lastMemRud_iff_aux (ri.iUnion rf), zero_add, isTuple_one,
      Nat.reduceAdd, IsEmpty.forall_iff, last_zero, isValue, tupleVal_one, true_and,
      Unique.eq_default, implies_true]
  | l + 1 => by
    obtain ⟨a, ha⟩ := exists_slice ((lastMemRud (ri.iUnion rf) (fun i ↦ .var i))〘fun i ↦ {xs i}〙 : M) (tuple xs)
    use a
    simp [IsIUnion, ha, mem_realize_lastMemRud_iff_aux (ri.iUnion rf)]
termination_by (max ri.depth rf.depth + 1, 1)
decreasing_by all_goals simp [RudimentaryTerm.depth, Prod.lex_def]

theorem mem_realize_lastMemRud_iff {l n} (t : L.RudimentaryTerm l) (rs : Fin l → L.RudimentaryBasisTerm n)
    (xs : Fin n → M) (z : M) :
    z ∈ (lastMemRud t rs)〘xs〙 ↔ IsTuple z (l + 1) ∧
      (∀ i, tupleVal z i.castSucc ∈ (rs i)〘xs〙) ∧ tupleVal z (last l) ∈ t〘tupleVal z ∘ castSucc〙 :=
  match t with
  | .iUnion ri rf => by
    convert mem_realize_lastMemRud_iff_aux (.iUnion ri rf) rs xs z
    rw [RudimentaryTerm.mem_realize_iUnion_iff₀]
    exact exists_iUnion ri rf _
  | .var i => mem_realize_lastMemRud_iff_aux (.var i) rs xs z
  | .const c => mem_realize_lastMemRud_iff_aux (.const c) rs xs z
  | .unorderedPair t₁ t₂ => mem_realize_lastMemRud_iff_aux (.unorderedPair t₁ t₂) rs xs z
  | .sdiff t₁ t₂ => mem_realize_lastMemRud_iff_aux (.sdiff t₁ t₂) rs xs z
  | .char R r => mem_realize_lastMemRud_iff_aux (.char R r) rs xs z
termination_by (t.depth, 2)
decreasing_by all_goals simp [RudimentaryTerm.depth, Prod.lex_def]

/-- The set of `l + 1`-tuples in `sProd rs` where after unraveling, `t₁` is equal to `t₂`. -/
theorem mem_realize_eqGraph_iff {l n} (t₁ t₂ : L.RudimentaryTerm (l + 1)) (rs : Fin (l + 1) → L.RudimentaryBasisTerm n)
    (xs : Fin n → M) (z : M) :
    z ∈ (eqGraph t₁ t₂ rs)〘xs〙 ↔ IsTuple z (l + 1) ∧ (∀ i, tupleVal z i ∈ (rs i)〘xs〙) ∧
      t₁〘tupleVal z〙 = t₂〘tupleVal z〙 := by
  simp only [eqGraph, mem_realize_sdiff_iff, mem_realize_sProd_iff, realize, mem_dom₀_iff,
    mem_realize_symDiff_iff, mem_realize_lastMemRud_iff t₁, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, not_false_eq_true, isTuple_unorderedPair_iff, tupleVal_orderedPair_castSucc,
    tupleVal_orderedPair_comp_castSucc, tupleVal_orderedPair_last, mem_realize_lastMemRud_iff t₂,
    and_congr_right_iff, Classical.not_imp, exists_and_left, not_and, not_exists, not_not]
  rw [MemStructure.ext_iff]
  grind
termination_by (max t₁.depth t₂.depth, 3)
decreasing_by all_goals (simp [Prod.lex_def, Nat.lt_or_ge])

theorem mem_realize_image_iff {l n} (t : L.RudimentaryTerm l) (rs : Fin l → L.RudimentaryBasisTerm n)
    (xs : Fin n → M) (z : M) :
    z ∈ (image t rs)〘xs〙 ↔ ∃ w : M, IsTuple w l ∧ (∀ i, tupleVal w i ∈ (rs i)〘xs〙) ∧
      z = t〘tupleVal w〙 :=
  match l with
  | 0 => by
    simp only [image, realize_singleton, mem_singleton_iff, IsEmpty.forall_iff, true_and]
    rw [MemStructure.ext_iff]
    simp only [mem_realize_lastMemRud_iff t, zero_add, isTuple_one, Nat.reduceAdd,
      IsEmpty.forall_iff, last_zero, isValue, tupleVal_one, true_and, Unique.eq_default]
    rw [← MemStructure.ext_iff]
    refine ⟨fun hz ↦ ⟨∅, by simp, hz⟩, by grind⟩
  | l + 1 => by
    simp only [image, realize, mem_sliceSet₀_iff, mem_realize_sProd_iff,
      mem_realize_lastMemRud_iff t, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, isTuple_unorderedPair_iff, tupleVal_orderedPair_castSucc,
      tupleVal_orderedPair_comp_castSucc, tupleVal_orderedPair_last]
    simp_rw [MemStructure.ext_iff]
    grind
termination_by (t.depth, 4)

theorem mem_realize_lastEqRud_iff {l n} (t : L.RudimentaryTerm l) (rs : Fin l → L.RudimentaryBasisTerm n)
    (xs : Fin n → M) (z : M) :
    z ∈ (lastEqRud t rs)〘xs〙 ↔ IsTuple z (l + 1) ∧
      (∀ i, tupleVal z i.castSucc ∈ (rs i)〘xs〙) ∧ tupleVal z (last l) = t〘tupleVal z ∘ castSucc〙 := by
  rw [lastEqRud, mem_realize_eqGraph_iff ᵣ-1 (t.castSucc)]
  simp only [forall_iff_castSucc, snoc_last, snoc_castSucc, RudimentaryTerm.realize_basic,
    and_congr_right_iff]
  rw [mem_realize_image_iff t rs]
  simp only [RudimentaryTerm.castSucc, RudimentaryTerm.castAdd, RudimentaryTerm.realize_castLE,
    castLE_succ_castSucc, and_congr_left_iff, and_iff_right_iff_imp]
  exact fun hz₁ hz₂ hz₃ ↦
    ⟨tuple (tupleVal z ∘ castSucc) (l := l), by simp [hz₂, hz₃]⟩
termination_by (t.depth, 5)
decreasing_by all_goals simp [RudimentaryTerm.depth, Prod.lex_def, RudimentaryTerm.castSucc,
  RudimentaryTerm.castAdd, RudimentaryTerm.castLE]

theorem mem_realize_memGraph_iff {l n} (t₁ t₂ : L.RudimentaryTerm l) (rs : Fin l → L.RudimentaryBasisTerm n)
    (xs : Fin n → M) (z : M) :
    z ∈ (memGraph t₁ t₂ rs)〘xs〙 ↔ IsTuple z l ∧
      (∀ i, tupleVal z i ∈ (rs i)〘xs〙) ∧ t₁〘tupleVal z〙 ∈ t₂〘tupleVal z〙 :=
  match l with
  | 0 => by
    simp only [memGraph, realize, realize_singleton, realize_sdiff_self, mem_dom₀_iff,
      mem_sprod₀_iff, mem_singleton_iff, mem_realize_inter_iff, mem_realize_lastMemRud_iff t₂,
      zero_add, isTuple_one, Nat.reduceAdd, IsEmpty.forall_iff, last_zero, isValue, tupleVal_one,
      true_and, mem_realize_lastEqRud_iff t₁, orderedPair_eq_orderedPair_iff,
      exists_eq_right_right', isTuple_zero_iff, Unique.eq_default]
    grind
  | l + 1 => by
    simp only [memGraph, realize, mem_dom₀_iff, mem_realize_inter_iff,
      mem_realize_lastMemRud_iff t₂, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, isTuple_unorderedPair_iff, tupleVal_orderedPair_castSucc,
      forall_iff_castSucc, tupleVal_orderedPair_comp_castSucc, tupleVal_orderedPair_last,
      mem_realize_lastEqRud_iff t₁, ↓existsAndEq, and_true]
    grind
termination_by (max t₁.depth t₂.depth, 6)
decreasing_by all_goals (simp [Prod.lex_def, Nat.lt_or_ge])
end

end Tuple

instance [L.ExtraConstantsUnaryRelationsOnly] [RudBasisClosed M] [Extensional M] : RudClosed M where
  iUnionClosed := exists_iUnion

end MemStructure

end FirstOrder.Language
