import Astlib.Basic.SetOperation.Insert

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y : M)

variable (M) in
/- Every nonempty member of `M` has a `∈`-mimimal element -/
class Foundational extends HasEmpty M where
  memMin : M → M
  memMin_prop (x : M) (_ : x ≠ ∅) : memMin x ∈ x ∧ ¬∃ y ∈ x, y ∈ memMin x

export Foundational (memMin memMin_prop)

theorem exists_memMin [M.Extensional] [HasEmpty M] (hM : M ⊨ M.L.foundation) (x : M) :
    ∃ y : M, (x ≠ ∅ → (y ∈ x ∧ ¬∃ z ∈ x, z ∈ y)) := by
  simp only [Sentence.Realize, Formula.Realize, foundation, Nat.reduceAdd, Term.isEmpty,
    Fin.reduceLast, Function.comp_apply, Fin.isValue, Term.castSucc, Nat.succ_eq_add_one,
    Term.castLE_var_inr, Fin.castLE_zero, BoundedFormula.exMem, BoundedFormula.allMem,
    BoundedFormula.realize_all, BoundedFormula.realize_sup, BoundedFormula.realize_not, realize_mem,
    Term.realize_var, Sum.elim_inr, Fin.snoc, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_lt_one,
    ↓reduceDIte, Fin.reduceCastLT, Fin.castSucc_zero, lt_self_iff_false, cast_eq,
    Nat.mod_succ, BoundedFormula.realize_imp, zero_lt_two, Nat.one_mod, Nat.one_lt_ofNat,
    Fin.castSucc_one, not_forall, not_not, not_exists] at hM
  by_cases h : x = ∅
  · use x; tauto
  rw [empty_iff] at h
  grind

noncomputable instance [Extensional M] [HasEmpty M] (hM : M ⊨ M.L.foundation) :
  Foundational M where
  memMin := fun x ↦ Classical.choose (exists_memMin hM x)
  memMin_prop := fun x ↦ Classical.choose_spec (exists_memMin hM x)

theorem memMin_mem [Foundational M] {x : M} (hx : x ≠ ∅) : memMin x ∈ x :=
  memMin_prop x hx |>.left

@[simp]
theorem notMem_memMin [Foundational M] {x y : M} (hy : y ∈ x) :
    y ∉ memMin x := by
  have : x ≠ ∅ := by grind
  grind [memMin_prop]

@[simp]
theorem notMem_of_mem_memMin [Foundational M] {x y : M} (hy : y ∈ memMin x) :
    y ∉ x := by
  grind [notMem_memMin]

@[simp]
theorem notMem_self [ClosedUnderPair M] [Foundational M] : x ∉ x := by
  have := memMin_mem (x := ({x} : M)) (by simp)
  grind [memMin_mem, notMem_memMin]

@[simp]
theorem insert_neq [Extensional M] [ClosedUnderPair M] [ClosedUnderSUnion M] [Foundational M] :
    succ x ≠ x := by
  grind [notMem_self]

end FirstOrder.Language.MemStructure
