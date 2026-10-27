/-
Copyright (c) 2026 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.ModelTheory.Encoding
import Mathlib.ModelTheory.Quotients
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Astlib.Mathlib.ModelTheory.Completeness.Proof

/-!
# Henkin extensions and the term model

- `Consistent.union_range_henkinAx`: adding Henkin axioms `ψ(c_ψ) ⟹ ∀' ψ` to a consistent set
  of formulas results in a consistent set, provided that the witnesses `c_ψ` are suitably fresh.
- `Consistent.exists_henkin`: every consistent set `Γ : Set (L.Formula α)` can be translated
  into a maximal consistent set of formulas which has
  Henkin witnesses.

The Henkin witnesses are free variables, rather than new constant symbols. The type of
variables is `α ⊕ ℕ × W`: a witness `(k, w)` has rank `k + 1`, and the witness of `ψ` has
rank bigger than the rank of any variable of `ψ`.

Let `Δ : Set (L.BoundedFormula β 0)` be a maximal consistent set of formulas which has Henkin
witnesses (`IsHenkin Δ`). The term model `hΔ.TermModel` is the quotient of the set of terms
`L.Term (β ⊕ Fin 0)` by the equivalence relation `t₁ =' t₂ ∈ Δ`.

The main result is the truth lemma `IsHenkin.realize_iff_mem`: a formula holds in the term model
(where the variable `b : β` is interpreted as the class of the term `var (Sum.inl b)`) iff it is
in `Δ`.
-/

open Fin FirstOrder Language Structure Cardinal

universe u v w

noncomputable section

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α : Type w} {β : Type*} {n l : ℕ}

namespace BoundedFormula

/-! ### Henkin axioms -/

/-- The substitution turning the free variable `c` into the bound variable `&0`. -/
def genFreeMap [DecidableEq β] (c : β) : β ⊕ Fin 0 → L.Term (β ⊕ Fin 1) :=
  Sum.elim (fun b ↦ if b = c then &0 else Term.var (Sum.inl b)) Fin.elim0

variable [DecidableEq β]

@[simp]
theorem genFreeMap_inl_self (c : β) : genFreeMap (L := L) c (Sum.inl c) = &0 := by
  simp [genFreeMap]

theorem genFreeMap_inl_of_ne {b c : β} (h : b ≠ c) :
    genFreeMap (L := L) c (Sum.inl b) = Term.var (Sum.inl b) := by
  simp [genFreeMap, h]

theorem genFreeMap_eq_elim (c : β) (f : Fin 0 → L.Term (β ⊕ Fin 1)) :
    genFreeMap c = Sum.elim (fun b ↦ genFreeMap c (Sum.inl b)) f := by
  funext x
  rcases x with b | i
  · rfl
  · fin_cases i

/-- The Henkin axiom `ψ(c) ⟹ ∀' ψ` -/
def henkinAx (wit : L.BoundedFormula β 1 → β) (ψ : L.BoundedFormula β 1) : L.BoundedFormula β 0 :=
  ψ.inst (Term.var (Sum.inl (wit ψ))) ⟹ ∀' ψ

/-- If the variable `c` does not occur in `Δ` and `ψ`, then adding the Henkin axiom
`ψ(c) ⟹ ∀' ψ` to `Δ` preserves consistency. -/
theorem Consistent.insert_henkin {Δ : Set (L.BoundedFormula β 0)} {ψ : L.BoundedFormula β 1}
    {c : β} (hcon : Consistent Δ) (hψ : c ∉ ψ.freeVarFinset)
    (hΔ : ∀ δ ∈ Δ, δ.substAll (genFreeMap c) = δ.castSucc) :
    Consistent (insert (ψ.inst (Term.var (Sum.inl c)) ⟹ ∀' ψ) Δ) := by
  intro h
  apply hcon
  have hnhenkin : Δ ⊢' ∼(ψ.inst (Term.var (Sum.inl c)) ⟹ ∀' ψ) := .impI h
  have hinst : Δ ⊢' ψ.inst (Term.var (Sum.inl c)) := by
    refine .byContra (.impE (hnhenkin.mono (Set.subset_insert _ _)) (.impI ?_))
    exact .exFalso (.impE (.ax (.inr (.inl rfl))) (.ax (.inl rfl)))
  have hnall : Δ ⊢' ∼(∀' ψ) :=
    .impI (.impE (hnhenkin.mono (Set.subset_insert _ _)) (.impI (.ax (.inr (.inl rfl)))))
  refine .impE hnall (.gen ?_)
  have hsubst (δ : L.BoundedFormula β 0) (hδ : δ ∈ Δ) :
      Δ ⊢' δ.substAll (Sum.elim (fun b ↦ genFreeMap c (Sum.inl b)) Fin.elim0) := by
    rw [← genFreeMap_eq_elim, hΔ δ hδ]
    exact (Provable.ax hδ).castSucc
  convert hinst.substAll (genFreeMap c) hsubst
  simp only [inst_eq_substAll, substAll_substAll]
  trans ψ.substAll Term.var
  · exact (substAll_var ψ).symm
  refine substAll_congr _ (fun a ha ↦ ?_) (fun i ↦ ?_)
  · simp [genFreeMap_inl_of_ne (b := a) (c := c) (by grind)]
  · fin_cases i
    simp [snoc]

/-- Adding finitely many Henkin axioms to a consistent set of formulas preserves consistency,
provided that the witnesses are sufficiently fresh: add them one at a time, the freshest last -/
theorem Consistent.union_image_henkinAx {Γ : Set (L.BoundedFormula β 0)} (hΓ : Consistent Γ)
    (wit : L.BoundedFormula β 1 → β) (rk : β → ℕ) (hinj : Function.Injective wit)
    (t : Finset (L.BoundedFormula β 1))
    (hrk : ∀ ψ ∈ t, ∀ b ∈ ψ.freeVarFinset, rk b < rk (wit ψ))
    (hfresh : ∀ ψ ∈ t, ∀ γ ∈ Γ, γ.substAll (genFreeMap (wit ψ)) = γ.castSucc) :
    Consistent (Γ ∪ henkinAx wit '' t) := by
  have : DecidableEq (L.BoundedFormula β 1) := Classical.decEq _
  -- induction on `t`, adding a formula with the freshest witness last
  induction t using Finset.induction_on_max_value (fun ψ ↦ rk (wit ψ)) with
  | empty => simpa using hΓ
  | insert a s ha hmax ih =>
    simp only [Finset.coe_insert, Set.image_insert_eq, Set.union_insert]
    have hcon : Consistent (Γ ∪ henkinAx wit '' s) := by grind
    refine hcon.insert_henkin (by grind) ?_
    rintro δ (hδ | ⟨x, hx, rfl⟩)
    · grind
    have hne (b : β) (hb : b ∈ x.freeVarFinset): b ≠ wit a := by grind
    have hxa : wit x ≠ wit a := by grind
    simp only [castSucc_eq_substAll, henkinAx, substAll_imp, substAll_all, inst_eq_substAll,
      substAll_substAll]
    congr 1
    · refine substAll_congr _ (fun b hb ↦ ?_) (fun i ↦ ?_)
      · simp [genFreeMap_inl_of_ne, hne, hb]
      · simp [snoc, genFreeMap_inl_of_ne, hxa]
    congr 1
    refine substAll_congr _ (fun b hb ↦ ?_) (fun i ↦ ?_)
    · simp [genFreeMap_inl_of_ne, hne, hb]
    · obtain rfl : i = last 0 := Fin.ext (by omega)
      simp only [Term.mapCastSucc_inr_last]

/-- Adding all Henkin axioms to a consistent set of formulas preserves consistency, provided
that the witnesses are sufficiently fresh. -/
theorem Consistent.union_range_henkinAx {Γ : Set (L.BoundedFormula β 0)} (hΓ : Consistent Γ)
    (wit : L.BoundedFormula β 1 → β) (rk : β → ℕ) (hinj : Function.Injective wit)
    (hrk : ∀ ψ, ∀ b ∈ ψ.freeVarFinset, rk b < rk (wit ψ))
    (hfresh : ∀ ψ, ∀ γ ∈ Γ, γ.substAll (genFreeMap (wit ψ)) = γ.castSucc) :
    Consistent (Γ ∪ Set.range (henkinAx wit)) := by
  intro h
  obtain ⟨Γ₀, h₀, hfin, hΓ₀⟩ := h.finite
  -- the Henkin axioms in `Γ₀` are the images of finitely many formulas
  obtain ⟨t, ht, htinj⟩ := Set.exists_image_eq_injOn_of_subset_range (f := henkinAx wit)
    (t := Γ₀ \ Γ) (by simpa [Set.sdiff_subset_iff] using h₀)
  have htfin : t.Finite := Set.Finite.of_finite_image (ht ▸ hfin.sdiff) htinj
  refine hΓ.union_image_henkinAx wit rk hinj htfin.toFinset (fun ψ _ ↦ hrk ψ)
    (fun ψ _ ↦ hfresh ψ) ?_
  rw [htfin.coe_toFinset]
  exact hΓ₀.mono (by simp [ht])

end BoundedFormula

/-! ### The type of Henkin variables -/

section HenkinVar

def HenkinIdx (L : Language.{u, v}) (γ : Type w) : Type (max u v w) :=
  (max ℵ₀ (Cardinal.lift.{max u v} #γ + Cardinal.lift.{w} L.card)).out

/-- The type of variables used in the Henkin construction: the original variables in `γ`,
together with the Henkin witnesses. -/
abbrev HenkinVar (L : Language.{u, v}) (γ : Type w) : Type (max u v w) := γ ⊕ ℕ × HenkinIdx L γ

variable (L : Language.{u, v}) (γ : Type w)

theorem mk_boundedFormula_le_mk_henkinIdx :
    #(L.BoundedFormula (HenkinVar L γ) 1) ≤ #(HenkinIdx L γ) := by
  trans #(Σ n, L.BoundedFormula (HenkinVar L γ) n)
  · exact mk_le_of_injective sigma_mk_injective
  trans max ℵ₀ (Cardinal.lift.{max u v} #(HenkinVar L γ) + Cardinal.lift.{max u v w} L.card)
  · exact BoundedFormula.card_le
  simp only [HenkinIdx, mk_out, mk_sum, mk_prod, mk_nat, lift_aleph0, lift_add, lift_mul,
    lift_lift, lift_id]
  rw [lift_umax.{w, max u v}, lift_umax.{max u v, w}, aleph0_mul_eq (le_max_left _ _)]
  grind [add_le_of_le, le_max_left, le_max_right, self_le_add_left, self_le_add_right]

variable {L γ}

noncomputable instance : DecidableEq (HenkinVar L γ) := Classical.decEq _

/-- An injective coding of formulas. -/
def henkinCode : L.BoundedFormula (HenkinVar L γ) 1 → HenkinIdx L γ :=
  ((Cardinal.le_def _ _).mp (mk_boundedFormula_le_mk_henkinIdx L γ)).some

theorem henkinCode_injective : Function.Injective (henkinCode (L := L) (γ := γ)) :=
  ((Cardinal.le_def _ _).mp (mk_boundedFormula_le_mk_henkinIdx L γ)).some.injective

/-- The rank of a Henkin variable. -/
def henkinRank : HenkinVar L γ → ℕ := Sum.elim (fun _ ↦ 0) (fun p ↦ p.fst + 1)

/-- The Henkin witness of the formula `ψ`. -/
def henkinWit (ψ : L.BoundedFormula (HenkinVar L γ) 1) : HenkinVar L γ :=
  Sum.inr (ψ.freeVarFinset.sup henkinRank, henkinCode ψ)

theorem henkinWit_injective : Function.Injective (henkinWit (L := L) (γ := γ)) :=
  fun _ _ h ↦ henkinCode_injective (congrArg Prod.snd (Sum.inr_injective h))

theorem henkinRank_lt_henkinWit (ψ : L.BoundedFormula (HenkinVar L γ) 1) (b : HenkinVar L γ)
    (hb : b ∈ ψ.freeVarFinset) : henkinRank b < henkinRank (henkinWit ψ) :=
  Nat.lt_succ_of_le (Finset.le_sup hb)

end HenkinVar

namespace BoundedFormula

/-- Every consistent set of formulas can be translated into a maximal consistent set of
formulas which has Henkin witnesses. -/
theorem Consistent.exists_henkin {Γ : Set (L.Formula α)} (hΓ : Consistent Γ) :
    ∃ (β : Type (max u v w)) (σ : α ⊕ Fin 0 → L.Term (β ⊕ Fin 0))
      (Δ : Set (L.Formula β)), Maximal Consistent Δ ∧
      (∀ ψ : L.BoundedFormula β 1, ∃ c : β, ψ.inst (Term.var (Sum.inl c)) ⟹ ∀' ψ ∈ Δ) ∧
      ∀ γ ∈ Γ, γ.substAll σ ∈ Δ := by
  let β := HenkinVar L α
  let σ : α ⊕ Fin 0 → L.Term (β ⊕ Fin 0) := Sum.elim (fun a ↦ Term.var (Sum.inl (Sum.inl a)))
    Fin.elim0
  let τ : β ⊕ Fin 0 → L.Term (α ⊕ Fin 1) :=
    Sum.elim (Sum.elim (Term.var ∘ Sum.inl) (fun _ ↦ &0)) Fin.elim0
  have hsubst (δ : L.Formula β) (hδ : δ ∈ (fun γ ↦ γ.substAll σ) '' Γ) :
      Γ ⊢' δ.substAll (Sum.elim (fun b ↦ τ (Sum.inl b)) Fin.elim0) := by
    obtain ⟨γ, hγ, rfl⟩ := hδ
    convert Provable.hyp hγ using 1
    simp only [substAll_substAll, ofFormula_eq_substAll]
    congr 1
    funext x
    rcases x with a | i
    · rfl
    · fin_cases i
  have hΓ' : Consistent ((fun γ ↦ γ.substAll σ) '' Γ) :=
    fun h ↦ hΓ (Provable.bot_of_succ (h.substAll τ hsubst))
  have hfresh (ψ : L.BoundedFormula β 1) (δ : L.Formula β)
      (hδ : δ ∈ (fun γ ↦ γ.substAll σ) '' Γ) :
      δ.substAll (genFreeMap (henkinWit ψ)) = δ.castSucc := by
    obtain ⟨γ, -, rfl⟩ := hδ
    simp only [castSucc_eq_substAll, substAll_substAll]
    congr 1
    ext x
    rcases x with a | i
    · simp [σ, Term.subst, genFreeMap, henkinWit]
    · fin_cases i
  obtain ⟨Δ, hsub, hΔ⟩ := (hΓ'.union_range_henkinAx henkinWit henkinRank henkinWit_injective
    henkinRank_lt_henkinWit hfresh).exists_maximal
  exact ⟨β, σ, Δ, hΔ, fun ψ ↦ ⟨henkinWit ψ, hsub (.inr ⟨ψ, rfl⟩)⟩,
    fun γ hγ ↦ hsub (.inl ⟨γ, hγ, rfl⟩)⟩

end BoundedFormula

/-! ### The term model -/

namespace BoundedFormula

/-- A maximal consistent set of formulas which has Henkin witnesses. -/
structure IsHenkin (Δ : Set (L.BoundedFormula β 0)) : Prop where
  /-- `Δ` is maximal consistent. -/
  maximal : Maximal Consistent Δ
  /-- Every formula `ψ` with one bound variable has a witness `c` such that `ψ(c) ⟹ ∀' ψ` is
  in `Δ`. -/
  henkin : ∀ ψ : L.BoundedFormula β 1, ∃ c : β, ψ.inst (Term.var (Sum.inl c)) ⟹ ∀' ψ ∈ Δ

namespace IsHenkin

variable {Δ : Set (L.BoundedFormula β 0)} (hΔ : IsHenkin Δ)

/-- Two terms are equivalent if `Δ` says that they are equal. -/
def setoid {Δ : Set (L.BoundedFormula β 0)} (hΔ : IsHenkin Δ) :
    Setoid (L.Term (β ⊕ Fin 0)) where
  r t₁ t₂ := t₁ =' t₂ ∈ Δ
  iseqv :=
    ⟨fun t ↦ mem_of_provable hΔ.maximal (.eqRefl t),
      fun h ↦ mem_of_provable hΔ.maximal (.eqSymm (.ax h)),
      fun h₁ h₂ ↦ mem_of_provable hΔ.maximal (.eqTrans (.ax h₁) (.ax h₂))⟩

/-- The structure on terms: a relation holds if `Δ` says so. -/
@[instance_reducible]
def prestructure {Δ : Set (L.BoundedFormula β 0)} (hΔ : IsHenkin Δ) :
    L.Prestructure hΔ.setoid where
  toStructure :=
    { funMap := fun f ts ↦ Term.func f ts
      RelMap := fun R ts ↦ rel R ts ∈ Δ }
  fun_equiv := fun _ _ h ↦ mem_of_provable hΔ.maximal (.funCongr _ fun i ↦ .ax (h i))
  rel_equiv := fun _ _ h ↦ propext
    ⟨fun hx ↦ mem_of_provable hΔ.maximal (.relCongr _ (fun i ↦ .ax (h i)) (.ax hx)),
      fun hy ↦ mem_of_provable hΔ.maximal (.relCongr _ (fun i ↦ .eqSymm (.ax (h i))) (.ax hy))⟩

/-- The term model of a maximal consistent Henkin set. -/
def TermModel {Δ : Set (L.BoundedFormula β 0)} (hΔ : IsHenkin Δ) := Quotient hΔ.setoid

instance {Δ : Set (L.BoundedFormula β 0)} (hΔ : IsHenkin Δ) : L.Structure hΔ.TermModel :=
  @quotientStructure L _ hΔ.setoid hΔ.prestructure

/-- The class of a term in the term model. -/
def toTermModel {Δ : Set (L.BoundedFormula β 0)} (hΔ : IsHenkin Δ) (t : L.Term (β ⊕ Fin 0)) :
    hΔ.TermModel := Quotient.mk hΔ.setoid t

instance {Δ : Set (L.BoundedFormula β 0)} (hΔ : IsHenkin Δ) : Nonempty hΔ.TermModel :=
  let ⟨c, _⟩ := hΔ.henkin ⊥
  ⟨hΔ.toTermModel (Term.var (Sum.inl c))⟩

theorem toTermModel_surjective : Function.Surjective hΔ.toTermModel :=
  Quotient.mk_surjective

theorem toTermModel_eq_iff {t₁ t₂ : L.Term (β ⊕ Fin 0)} :
    hΔ.toTermModel t₁ = hΔ.toTermModel t₂ ↔ t₁ =' t₂ ∈ Δ :=
  @Quotient.eq _ hΔ.setoid _ _

theorem funMap_toTermModel (f : L.Functions l) (ts : Fin l → L.Term (β ⊕ Fin 0)) :
    funMap f (fun i ↦ hΔ.toTermModel (ts i)) = hΔ.toTermModel (Term.func f ts) :=
  @funMap_quotient_mk' L _ hΔ.setoid hΔ.prestructure _ f ts

theorem relMap_toTermModel (R : L.Relations l) (ts : Fin l → L.Term (β ⊕ Fin 0)) :
    RelMap R (fun i ↦ hΔ.toTermModel (ts i)) ↔ rel R ts ∈ Δ :=
  @relMap_quotient_mk' L _ hΔ.setoid hΔ.prestructure _ R ts

theorem realize_toTermModel {γ : Type*} (t : L.Term γ) (σ : γ → L.Term (β ⊕ Fin 0)) :
    t.realize (fun x ↦ hΔ.toTermModel (σ x)) = hΔ.toTermModel (t.subst σ) := by
  induction t with
  | var x => rfl
  | func f ts ih => simp [ih, funMap_toTermModel]

theorem realize_toTermModel_substBound (t : L.Term (β ⊕ Fin n)) (ts : Fin n → L.Term (β ⊕ Fin 0)) :
    t.realize (Sum.elim (fun b ↦ hΔ.toTermModel (Term.var (Sum.inl b)))
      (fun i ↦ hΔ.toTermModel (ts i))) =
      hΔ.toTermModel (t.substBound ts) := by
  rw [Term.substBound_eq_subst, ← realize_toTermModel]
  congr 1
  ext x
  cases x <;> rfl

/-- The truth lemma, for formulas with dangling bound variables. -/
theorem realize_iff_substBound_mem (φ : L.BoundedFormula β n)
    (ts : Fin n → L.Term (β ⊕ Fin 0)) :
    φ.Realize (fun b ↦ hΔ.toTermModel (Term.var (Sum.inl b))) (fun i ↦ hΔ.toTermModel (ts i)) ↔
      φ.substBound ts ∈ Δ := by
  induction φ with
  | falsum =>
    have := bot_notMem hΔ.maximal
    tauto
  | equal t₁ t₂ =>
    simp only [Realize, substBound_equal, realize_toTermModel_substBound, toTermModel_eq_iff]
    rfl
  | rel R us =>
    simp [Realize, realize_toTermModel_substBound, relMap_toTermModel]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp [ih₁, ih₂, imp_mem_iff, hΔ.maximal]
  | all ψ ih =>
    simp only [realize_all, substBound_all]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := hΔ.henkin (ψ.substBound (snoc (fun i ↦ (ts i).castSucc) &(last 0)))
      simp only [imp_mem_iff, hΔ.maximal] at hc
      refine hc ?_
      rw [inst_substBound, ← ih, Fin.comp_snoc' hΔ.toTermModel ts]
      exact h _
    · intro h a
      obtain ⟨t, rfl⟩ := hΔ.toTermModel_surjective a
      rw [← Fin.comp_snoc' hΔ.toTermModel ts, ih, ← inst_substBound]
      exact mem_of_provable hΔ.maximal (.allE t (.ax h))

/-- The truth lemma: a formula holds in the term model iff it is in `Δ`. -/
theorem realize_iff_mem (φ : L.BoundedFormula β 0) :
    φ.Realize (fun b ↦ hΔ.toTermModel (Term.var (Sum.inl b))) default ↔ φ ∈ Δ := by
  have := hΔ.realize_iff_substBound_mem φ (fun i ↦ &i)
  rwa [substBound_var, Subsingleton.elim (fun i ↦ hΔ.toTermModel (&i)) default] at this

end IsHenkin

end BoundedFormula

end Language

end FirstOrder
