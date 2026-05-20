import Astlib.Basic.SetOperation.Insert

namespace FirstOrder.Language

variable {L : FirstOrder.Language} [HasMem L]

/-- The foundation axiom -/
def foundation : L.Sentence := ∀' ((&0).isEmpty ⊔ ∃'∈ &0 ∼(∃'∈ &0 (&2 ∈' &1)))

namespace MemStructure

variable {M : MemStructure} (x y : M)

variable (M) in
/- Every nonempty member of `M` has a `∈`-mimimal element -/
class Foundational extends M.HasEmpty where
  memMin : M → M
  protected memMin_prop (x : M) (_ : x ≠ ∅) : memMin x ∈ x ∧ ¬∃ y ∈ x, y ∈ memMin x

export Foundational (memMin)

theorem exists_memMin [M.Extensional] [M.HasEmpty] (hM : M ⊨ M.L.foundation) (x : M) :
    ∃ y : M, (x ≠ ∅ → (y ∈ x ∧ ¬∃ z ∈ x, z ∈ y)) := by
  simp only [Sentence.Realize, Formula.Realize, foundation, Nat.reduceAdd, Term.isEmpty,
    BoundedFormula.allMem, Fin.reduceLast, Function.comp_apply, Fin.isValue, Term.castSucc,
    Nat.succ_eq_add_one, Term.castLE_var_inr, Fin.castLE_zero, BoundedFormula.exMem,
    BoundedFormula.realize_all, BoundedFormula.realize_sup, BoundedFormula.realize_imp, realize_mem,
    Term.realize_var, Sum.elim_inr, Fin.snoc, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Order.lt_one_iff,
    ↓reduceDIte, Fin.reduceCastLT, Fin.castSucc_zero, lt_self_iff_false, cast_eq,
    Nat.mod_succ, BoundedFormula.realize_bot, imp_false, BoundedFormula.realize_not,
    Order.lt_two_iff, zero_le, Nat.one_mod, Std.le_refl, Fin.castSucc_one, not_forall,
    not_not, not_exists] at hM
  by_cases h : x = ∅
  · use x; tauto
  rw [empty_iff] at h
  grind

noncomputable instance [M.Extensional] [M.HasEmpty] (hM : M ⊨ M.L.foundation) :
  Foundational M where
  memMin := fun x ↦ Classical.choose (exists_memMin hM x)
  memMin_prop := fun x ↦ Classical.choose_spec (exists_memMin hM x)

theorem memMin_mem [Foundational M] {x : M} (hx : x ≠ ∅) : memMin x ∈ x :=
  Foundational.memMin_prop x hx |>.left

@[simp]
theorem notMem_memMin [Foundational M] {x y : M} (hy : y ∈ x) :
    y ∉ memMin x := by
  have : x ≠ ∅ := by grind
  grind [Foundational.memMin_prop]

@[simp]
theorem notMem_of_mem_memMin [Foundational M] {x y : M} (hy : y ∈ memMin x) :
    y ∉ x := by
  grind [notMem_memMin]

@[simp]
theorem notMem_self [M.ClosedUnderPair] [Foundational M] : x ∉ x := by
  have := memMin_mem (x := ({x} : M)) (by simp)
  grind [memMin_mem, notMem_memMin]

@[simp]
theorem insert_neq [M.Extensional] [M.ClosedUnderPair] [M.ClosedUnderSUnion] [Foundational M] :
    succ x ≠ x := by
  grind [notMem_self]

end FirstOrder.Language.MemStructure
