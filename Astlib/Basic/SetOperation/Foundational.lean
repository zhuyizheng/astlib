import Astlib.Basic.SetOperation.Insert

namespace FirstOrder.Language.MemStructure

variable {M : MemStructure} (x y : M)

noncomputable instance : Decidable (∃ a ∈ x, ¬∃ y ∈ x, y ∈ a) :=
  Classical.propDecidable _

noncomputable def memMin (x : M) := dite (∃ a ∈ x, ¬∃ y ∈ x, y ∈ a) Classical.choose default

variable (M) in
/- `M` is closed under `⋃` -/
class Foundational : Prop where
  protected memMin_prop : ∀ (x : M), x ≠ ∅ → memMin x ∈ x ∧ ¬∃ y ∈ x, y ∈ memMin x

noncomputable instance instFoundational [M.Extensional] [M.HasEmpty]
    (h : ∀ x : M, x ≠ ∅ → ∃ a ∈ x, ¬∃ y ∈ x, y ∈ a) : M.Foundational :=
  ⟨fun x hx ↦ by
    specialize h x hx
    suffices memMin x = Classical.choose h by convert Classical.choose_spec h
    simp only [memMin]; split_ifs; simp⟩

@[grind .]
theorem memMin_mem [Foundational M] {x : M} (hx : x ≠ ∅) : memMin x ∈ x :=
  Foundational.memMin_prop x hx |>.left

@[simp, grind →, grind .]
theorem notMem_memMin [M.HasEmpty] [Foundational M] {x y : M} (hy : y ∈ x) :
    y ∉ memMin x := by
  have : x ≠ ∅ := by grind
  grind [Foundational.memMin_prop]

@[simp, grind →]
theorem notMem_of_mem_memMin [M.HasEmpty] [Foundational M] {x y : M} (hy : y ∈ memMin x) :
    y ∉ x := by
  grind

@[simp, grind .]
theorem notMem_self [M.HasEmpty] [M.ClosedUnderPair] [Foundational M] : x ∉ x := by
  have := memMin_mem (x := ({x} : M)) (by simp)
  grind

@[simp, grind .]
theorem insert_neq [M.Extensional] [M.HasEmpty] [M.ClosedUnderPair] [M.ClosedUnderSUnion]
    [Foundational M] :
    succ x ≠ x := by
  grind

end MemStructure


variable {L : FirstOrder.Language} [HasMem L]

/-- The foundation axiom -/
def foundation : L.Sentence := ∀' ((&0).isEmpty ⊔ ∃'∈ &0 ∼(∃'∈ &0 (&2 ∈' &1)))

variable {M : MemStructure}

theorem exists_memMin [M.Extensional] [M.HasEmpty] (hM : M ⊨ M.L.foundation) (x : M)
    (hx : x ≠ ∅) :
    ∃ y : M, (y ∈ x ∧ ¬∃ z ∈ x, z ∈ y) := by
  simp only [Sentence.Realize, Formula.Realize, foundation, Nat.reduceAdd, Term.isEmpty,
    BoundedFormula.allMem, Fin.reduceLast, Function.comp_apply, Fin.isValue, Term.castSucc,
    Nat.succ_eq_add_one, Term.castLE_var_inr, Fin.castLE_zero, BoundedFormula.exMem,
    BoundedFormula.realize_all, BoundedFormula.realize_sup, BoundedFormula.realize_imp,
    MemStructure.realize_mem, Term.realize_var, Sum.elim_inr, Fin.snoc, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, Order.lt_one_iff, ↓reduceDIte, Fin.reduceCastLT, Fin.castSucc_zero,
    lt_self_iff_false, cast_eq, Nat.mod_succ, BoundedFormula.realize_bot,
    imp_false, BoundedFormula.realize_not, Order.lt_two_iff, zero_le, Nat.one_mod, Std.le_refl,
    Fin.castSucc_one, not_forall,  not_not, not_exists] at hM
  rw [M.ne_empty_iff] at hx
  grind

noncomputable instance [M.Extensional] [M.HasEmpty]
    (hM : M ⊨ M.L.foundation) : M.Foundational :=
  M.instFoundational (fun x ↦ exists_memMin hM x)

end FirstOrder.Language
