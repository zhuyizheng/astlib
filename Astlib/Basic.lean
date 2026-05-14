import Astlib.Syntax
import Astlib.ModelTheory.Semantics
import Astlib.Axioms
import Astlib.Fin.Basic

open FirstOrder Language BoundedFormula Fin

section ExUnique
variable {L : Language} [L.Structure M]

-- {T : L.Theory} {M : T.ModelType}

variable {φ : L.BoundedFormula α n}

theorem exists_of_ex {φ : L.BoundedFormula α (n + 1)} {v : α → M}
    {xs : Fin n → M} (h : (∃' φ).Realize v xs) :
    ∃ a : M, φ.Realize v (snoc xs a) := by
  simpa using h

-- theorem exists_of_ex_empty {φ : L.BoundedFormula Empty (n + 1)}
--     {xs : Fin n → M} (h : (∃' φ).Realize default xs) :
--     ∃ a : M, φ.Realize default (snoc xs a) :=
--   exists_of_ex h

-- -- theorem exists_of_ex_empty_one {φ : L.BoundedFormula Empty 1}
-- --     -- (h : Sentence.Realize M (∃' φ)) :
-- --     ∃ a : M, φ.Realize default ![a] := by
-- --   convert exists_of_ex_empty h
-- --   ext i; simp [snoc]
-- --   -- exists_of_ex h

-- theorem exists_of_ex_empty_one {φ : L.BoundedFormula Empty 1}
--     (h : (∃' φ).Realize default (default : _ → M)) :
--     ∃ a : M, φ.Realize default ![a] := by
--   convert exists_of_ex_empty h
--   ext i; simp [snoc]

-- theorem exists_of_ex_empty_two {φ : L.BoundedFormula Empty 2}
--     (h : (∃' φ).Realize default ![x]) :
--     ∃ a : M, φ.Realize default ![x, a] := by
--   convert exists_of_ex_empty h
--   ext i; fin_cases i <;> simp

-- theorem exists_of_ex_empty_three {φ : L.BoundedFormula Empty 3}
--     (h : (∃' φ).Realize default ![x₁, x₂]) :
--     ∃ a : M, φ.Realize default ![x₁, x₂, a] := by
--   convert exists_of_ex_empty h
--   ext i; fin_cases i <;> simp

-- theorem exists_of_ex_empty_four {φ : L.BoundedFormula Empty 4}
--     (h : (∃' φ).Realize default ![x₁, x₂, x₃]) :
--     ∃ a : M, φ.Realize default ![x₁, x₂, x₃, a] := by
--   convert exists_of_ex_empty h
--   ext i; fin_cases i <;> simp

theorem existsUnique_of_exUnique {φ : L.BoundedFormula α (n + 1)} {v : α → M}
    {xs : Fin n → M} (h : (∃!' φ).Realize v xs) :
    ∃! a : M, φ.Realize v (snoc xs a) := by
  simp only [BoundedFormula.exUnique, Function.comp_apply, realize_ex, Nat.succ_eq_add_one,
    realize_inf, realize_all, realize_imp, realize_bdEqual, Term.realize_var, Sum.elim_inr,
    snoc_last] at h
  obtain ⟨a, ha₁, ha₂⟩ := h
  refine ⟨a, ha₁, fun b ↦ ?_⟩
  simp only
  convert ha₂ b using 1
  · rw [realize_liftAt' (by omega)]
    apply Eq.to_iff
    congr
    grind [snoc]
  · grind [snoc, Fin.val_last_plus_one_minus_one]


theorem existsUnique_of_exUnique_sentence {φ : L.BoundedFormula Empty 1}
    (h : (∃!' φ).Realize default (default : _ → M)) :
    ∃! a : M, φ.Realize default ![a] := by
  convert existsUnique_of_exUnique h
  ext i
  simp [snoc]


end ExUnique



open FirstOrder Language

variable (L : FirstOrder.Language) [HasMem L]

namespace FirstOrder
namespace Language

structure MemStructure where
  Carrier : Type*
  L : FirstOrder.Language
  [hasMem : L.HasMem]
  [struc : L.Structure Carrier]
  [nonempty' : Nonempty Carrier]

-- Porting note: In Lean4, other instances precedes `FirstOrder.Language.Theory.ModelType.struc`,
-- it's issues in `ModelTheory.Satisfiability`. So, we increase these priorities. TODO
attribute [instance 2000] MemStructure.L MemStructure.hasMem MemStructure.struc
  MemStructure.nonempty'

namespace MemStructure

attribute [coe] MemStructure.Carrier

instance : CoeSort MemStructure (Type _) where
  coe M := M.Carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (M : Type w) [L.Structure M] [L.HasMem] [Nonempty M] : MemStructure :=
  ⟨M, L⟩

instance instNonempty (M : MemStructure) : Nonempty M :=
  inferInstance

noncomputable instance (M : MemStructure) : Inhabited M :=
  Classical.inhabited_of_nonempty'

instance (M : MemStructure) :
  Membership M M where
  mem := fun x y ↦ Structure.RelMap (M.hasMem.memSymb) ![y, x]

instance (M : MemStructure) :
  HasSubset M where
  Subset := fun x y ↦ ∀ z ∈ x, z ∈ y

@[simp]
theorem realize_mem {M : MemStructure} (t₁ t₂ : M.L.Term (α ⊕ Fin n)) {v : α → M} {xs : Fin n → M} :
    (t₁ ∈' t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) ∈ t₂.realize (Sum.elim v xs):= by
  simp [mem_boundedFormula, Membership.mem]

/- `M` is extensional -/
class Extensional (M : MemStructure) where
  extensional : ∀ x y : M, ((∀ z : M, (z ∈ x ↔ z ∈ y)) → x = y)

-- export Extensional (extensional)

@[ext]
theorem Extensional.ext (M : MemStructure) [Extensional M] {x y : M}
    (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y :=
  extensional x y h

instance (M : MemStructure) (hM : M ⊨ M.L.extensionality) : Extensional M where
  extensional := by simpa [Sentence.Realize, Formula.Realize, extensionality] using hM

/- `M` has an empty set `∅` -/
class HasEmptyset (M : MemStructure) extends EmptyCollection M where
  -- /-- The empty set -/
  -- emptyset : M
  emptyset_prop : ∀ x : M, x ∉ (∅ : M)

@[grind .]
theorem notin_emptyset (M : MemStructure) [HasEmptyset M] (x : M) : x ∉ (∅ : M) :=
  HasEmptyset.emptyset_prop x

-- export HasEmptyset (emptyset)

-- @[inherit_doc] notation "∅"  => HasEmptyset.emptyset


noncomputable instance (M : MemStructure) (hM : M ⊨ M.L.exEmptyset) : HasEmptyset M where
  emptyCollection := Classical.choose (exists_of_ex hM)
  emptyset_prop := by simpa [Term.isEmptyset] using Classical.choose_spec (exists_of_ex hM)



theorem test (M : MemStructure) [Extensional M] [HasEmptyset M] :
    ∃! x : M, (∀ z : M, z ∉ x) := by
  use ∅
  constructor
  · grind
  · intro y hy
    ext
    -- ext
    -- apply extensional y emptyset
    -- intro z
    -- have : ∀ z : M, z ∉ emptyset := by grind
    grind

/- `M` is closed under `⋃` -/
class HasUnion (M : MemStructure) where
  union : M → M
  union_prop : ∀ x y : M, y ∈ union x ↔ (∃ z ∈ x, y ∈ z)

prefix:110 "⋃ " => HasUnion.union

@[simp, grind =, push]
theorem mem_union_iff (M : MemStructure) [HasUnion M] (x a : M) : x ∈ ⋃ a ↔ ∃ y ∈ a, x ∈ y :=
  HasUnion.union_prop _ _


-- lemma test2 (M : MemStructure) (hM : M ⊨ M.L.exUnion) : True := by
  -- have := realize_all.mp hM

noncomputable instance (M : MemStructure) (hM : M ⊨ M.L.exUnion) : HasUnion M where
  union x := Classical.choose (exists_of_ex (realize_all.mp hM x))
  union_prop := fun x ↦ by simpa using Classical.choose_spec (exists_of_ex (realize_all.mp hM x))


theorem test2 (M : MemStructure) [Extensional M] [HasEmptyset M] [HasUnion M] :
    ⋃ ⋃ (∅ : M) = ∅ := by
  ext
  grind


/- `M` is closed under unordered pairing -/
class HasUnorderedPair (M : MemStructure) where
  unorderedPair : M → M → M
  unorderedPair_prop : ∀ x y z : M, z ∈ unorderedPair x y ↔ (z = x ∨ z = y)

instance (M : MemStructure) [HasUnorderedPair M] : Singleton M M where
  singleton x := HasUnorderedPair.unorderedPair x x

instance (M : MemStructure) [HasUnion M] [HasUnorderedPair M] : Union M where
  union x y := ⋃ (HasUnorderedPair.unorderedPair x y)

instance (M : MemStructure) [HasUnion M] [HasUnorderedPair M] : Insert M M where
  insert x xs := xs ∪ {x}


-- lemma test2 (M : MemStructure) (hM : M ⊨ M.L.exUnion) : True := by
  -- have := realize_all.mp hM

noncomputable instance (M : MemStructure) (hM : M ⊨ M.L.exUnorderedPair) : HasUnorderedPair M where
  unorderedPair x y := Classical.choose (exists_of_ex (realize_all.mp (realize_all.mp hM x) y))
  unorderedPair_prop := fun x y ↦ by
    simpa using Classical.choose_spec (exists_of_ex (realize_all.mp (realize_all.mp hM x) y))

@[simp, grind =, push]
theorem mem_singleton_iff {M : MemStructure} [HasUnorderedPair M] (x y : M) :
    y ∈ ({x} : M) ↔ y = x := by
  simpa using HasUnorderedPair.unorderedPair_prop x x y

theorem notMem_singleton_iff {M : MemStructure} [HasUnorderedPair M] (x y : M) :
    y ∉ ({x} : M) ↔ y ≠ x := by simp

theorem mem_singleton {M : MemStructure} [HasUnorderedPair M] (x : M) :
    x ∈ ({x} : M) := by simp

@[simp]
theorem singleton_eq_singleton_iff {M : MemStructure} [HasUnorderedPair M] (x y : M) :
    ({x} : M) = {y} ↔ x = y := by grind [mem_singleton]

@[simp]
theorem singleton_ne_empty {M : MemStructure} [HasEmptyset M] [HasUnorderedPair M] (x : M) :
    ({x} : M) ≠ ∅ := by grind [mem_singleton]

@[simp, grind =]
theorem singleton_subset_iff {M : MemStructure} [HasUnorderedPair M] (x y : M) :
    ({x} : M) ⊆ y ↔ x ∈ y := by simp [Subset]

@[gcongr]
theorem singleton_subset_singleton {M : MemStructure} [HasUnorderedPair M] (x y : M) :
    ({x} : M) ⊆ {y} ↔ x = y := by grind [mem_singleton]


end MemStructure

end Language

end FirstOrder
