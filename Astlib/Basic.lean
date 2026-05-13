import Astlib.Syntax
import Astlib.ModelTheory.Semantics
import Astlib.Axioms
import Astlib.Fin.Basic

open STLanguage FirstOrder Language BoundedFormula Axiom Fin

section ExUnique
variable {L : Language} [L.Structure M]

-- {T : L.Theory} {M : T.ModelType}

variable {φ : L.BoundedFormula α n}

theorem exists_of_ex {φ : L.BoundedFormula α (n + 1)} {v : α → M}
    {xs : Fin n → M} (h : (∃' φ).Realize v xs) :
    ∃ a : M, φ.Realize v (snoc xs a) := by
  simpa using h

theorem exists_of_ex_empty {φ : L.BoundedFormula Empty (n + 1)}
    {xs : Fin n → M} (h : (∃' φ).Realize default xs) :
    ∃ a : M, φ.Realize default (snoc xs a) :=
  exists_of_ex h

theorem exists_of_ex_empty_one {φ : L.BoundedFormula Empty 1}
    (h : (∃' φ).Realize default (default : _ → M)) :
    ∃ a : M, φ.Realize default ![a] := by
  convert exists_of_ex_empty h
  ext i; simp [snoc]

theorem exists_of_ex_empty_two {φ : L.BoundedFormula Empty 2}
    (h : (∃' φ).Realize default ![x]) :
    ∃ a : M, φ.Realize default ![x, a] := by
  convert exists_of_ex_empty h
  ext i; fin_cases i <;> simp

theorem exists_of_ex_empty_three {φ : L.BoundedFormula Empty 3}
    (h : (∃' φ).Realize default ![x₁, x₂]) :
    ∃ a : M, φ.Realize default ![x₁, x₂, a] := by
  convert exists_of_ex_empty h
  ext i; fin_cases i <;> simp

theorem exists_of_ex_empty_four {φ : L.BoundedFormula Empty 4}
    (h : (∃' φ).Realize default ![x₁, x₂, x₃]) :
    ∃ a : M, φ.Realize default ![x₁, x₂, x₃, a] := by
  convert exists_of_ex_empty h
  ext i; fin_cases i <;> simp

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



open STLanguage FirstOrder Language
open Axiom

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

instance (M : MemStructure) :
  Membership M M where
  mem := fun x y ↦ FirstOrder.Language.Structure.RelMap (memSymb (L := M.L)) ![y, x]


@[simp]
theorem realize_mem {M : MemStructure} (t₁ t₂ : M.L.Term (α ⊕ Fin n)) {v : α → M} {xs : Fin n → M} :
    (t₁ ∈' t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) ∈ t₂.realize (Sum.elim v xs):= by
  simp [mem_boundedFormula, Membership.mem]

class Extensional (M : MemStructure) where
  extensional : ∀ x y : M, ((∀ z : M, (z ∈ x ↔ z ∈ y)) → x = y)

-- export Extensional (extensional)

@[ext]
theorem Extensional.ext (M : MemStructure) [Extensional M] {x y : M}
    (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y :=
  extensional x y h

instance (M : MemStructure) (hM : M ⊨ extensionality (L := M.L)) : Extensional M where
  extensional := by simpa [Sentence.Realize, Formula.Realize, extensionality] using hM

class HasEmptyset (M : MemStructure) where
  emptyset : M
  emptyset_prop : ∀ x : M, x ∉ emptyset

export HasEmptyset (emptyset)

@[grind .]
theorem notin_emptyset (M : MemStructure) [HasEmptyset M] (x : M) : x ∉ emptyset :=
  HasEmptyset.emptyset_prop x

theorem test (M : MemStructure) [Extensional M] [HasEmptyset M] :
    ∃! x : M, (∀ z : M, z ∉ x) := by
  use emptyset
  constructor
  · grind
  · intro y hy
    ext
    -- ext
    -- apply extensional y emptyset
    -- intro z
    -- have : ∀ z : M, z ∉ emptyset := by grind
    grind


end MemStructure

end Language

end FirstOrder

variable {L : Language}
-- variable [HasMem L]

-- noncomputable def emptySet (M : Type*) [L.HasMem] [L.ExEmptyset M] : M :=
--   Classical.choose (exists_of_ex_empty_one (ExEmptyset.exEmptyset (L := L)))

-- -- variable [HasMem L]
-- theorem uniqSetProp (M : Type*) [L.HasMem] [L.ExUniqueEmptyset M] :
--     ((&0).isEmptyset).Realize (L := L) (α := Empty) default ![uniqSet M (L := L)] :=
--   Classical.choose_spec (existsUnique_of_exUnique_sentence
--     (ExUniqueEmptyset.exUniqueEmptyset (L := L))) |>.left
