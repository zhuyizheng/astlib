import Mathlib.ModelTheory.Semantics

import Astlib.Mathlib.ModelTheory.Syntax
import Astlib.Mathlib.Fin.Basic

open Fin

namespace FirstOrder

namespace Language

variable {m n} {L : Language} {M : Type w} [L.Structure M] {α : Type u'}
  {l : ℕ} {θ : L.BoundedFormula α (l + m)} {ψ : L.BoundedFormula α (l + n)}
  {v : α → M} {xs : Fin l → M}

namespace Term

abbrev realize' (t : L.Term (α ⊕ Fin n)) (v : α → M) (xs : Fin n → M) :=
  t.realize (Sum.elim v xs)

@[simp]
theorem realize_castLE {n n' : ℕ} {t : L.Term (α ⊕ Fin n)} {h : n ≤ n'}
    {v : α ⊕ (Fin n') → M} :
    (t.castLE h).realize v =
      t.realize (v ∘ Sum.map id (Fin.castLE h)) :=
  realize_relabel

end Term

namespace BoundedFormula


@[simp]
theorem realize_all' :
    (θ.all' m).Realize v xs ↔ ∀ ys : Fin m → M, θ.Realize v (append xs ys) := by
  induction m with
  | zero => simp [append_right_nil]
  | succ m ih =>
    simp only [all'_succ, ih]
    refine ⟨fun h zs ↦ ?_, fun h ys a ↦ ?_⟩
    · simpa [← append_snoc] using h (init zs) (zs (last _))
    · simpa [← append_snoc] using h (snoc ys a)

@[simp]
theorem realize_ex' :
    (θ.ex' m).Realize v xs ↔ ∃ ys : Fin m → M, θ.Realize v (append xs ys) := by
  induction m with
  | zero => simp [append_right_nil]
  | succ m ih =>
    simp only [ex'_succ, ih, realize_ex]
    refine ⟨fun ⟨ys, a, h⟩ ↦ ⟨snoc ys a, ?_⟩, fun ⟨zs, h⟩ ↦ ⟨init zs, zs (last _), ?_⟩⟩
    · simpa [append_snoc]
    · simpa [← append_snoc]


theorem realize_liftAt' {n n' m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin (n + n') → M}
    (hmn : m ≤ n) :
    (φ.liftAt n' m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then castAdd n' i else addNat i n') := by
  rw [liftAt]
  induction φ with
  | falsum => simp [mapTermRel, Realize]
  | equal => simp [mapTermRel, Realize, Sum.elim_comp_map]
  | rel => simp [mapTermRel, Realize, Sum.elim_comp_map]
  | imp _ _ ih1 ih2 => simp only [mapTermRel, Realize, ih1 hmn, ih2 hmn]
  | @all k _ ih3 =>
    have h : k + 1 + n' = k + n' + 1 := by rw [add_assoc, add_comm 1 n', ← add_assoc]
    simp only [mapTermRel, Realize, realize_castLE_of_eq h, ih3 (hmn.trans k.le_succ)]
    refine forall_congr' fun x => iff_eq_eq.mpr (congr rfl (funext (lastCases ?_ fun i => ?_)))
    · simp only [Function.comp_apply, val_last, snoc_last]
      refine (congr rfl (Fin.ext ?_)).trans (snoc_last _ _)
      split_ifs <;> dsimp; lia
    · simp only [Function.comp_apply, snoc_castSucc]
      refine (congr rfl (Fin.ext ?_)).trans (snoc_castSucc _ _ _)
      simp only [val_castSucc, val_cast]
      split_ifs <;> simp

theorem realize_imp_ex'_all' [Inhabited M] :
    let φ := (θ.liftAt n (l + m)).cast (Nat.add_assoc _ _ _) ⟹
      (ψ.liftAt m l).cast (by rw [Nat.add_assoc, add_comm n]) |>.all' (m + n)
    φ.Realize v xs ↔ (θ.ex' m ⟹ ψ.all' n).Realize v xs := by
  intro φ
  simp only [realize_all', realize_imp, realize_ex', forall_exists_index, φ]
  refine ⟨fun h ys hys zs ↦ ?_, fun h yzs hys ↦ ?_⟩
  · specialize h (append ys zs)
    repeat rw [cast, realize_castLE_of_eq (by omega), realize_liftAt' (by omega)] at h
    revert hys
    convert h <;> grind [append_nat]
  · specialize h (yzs ∘ castAdd _)
    rw [cast, realize_castLE_of_eq (by omega), realize_liftAt' (by omega)] at hys ⊢
    convert h _ (yzs ∘ natAdd _)
    · ext; simp only [Function.comp_apply, append_nat, val_cast, natAdd_mk]
      grind
    · convert hys
      ext; simp [append_nat]

theorem realize_imp_all'_ex' [Inhabited M] :
    let φ := (θ.liftAt n (l + m)).cast (Nat.add_assoc _ _ _) ⟹
      (ψ.liftAt m l).cast (by rw [Nat.add_assoc, add_comm n]) |>.ex' (m + n)
    φ.Realize v xs ↔ (θ.all' m ⟹ ψ.ex' n).Realize v xs := by
  intro φ
  simp only [realize_ex', realize_imp, realize_all', φ]
  refine ⟨fun ⟨yzs, h⟩ hys ↦ ⟨yzs ∘ natAdd _, ?_⟩, fun h ↦ ?_⟩
  · repeat rw [cast, realize_castLE_of_eq (by omega), realize_liftAt' (by omega)] at h
    simp only [is_lt, ↓reduceIte] at h
    specialize hys (yzs ∘ castAdd _)
    revert hys
    convert h
    · ext; simp [append_nat]
    · ext; simp only [Function.comp_apply, append_nat, val_cast, natAdd_mk]
      grind
  · by_cases hys : (∀ (ys : Fin m → M), θ.Realize v (append xs ys))
    · obtain ⟨zs, hzs⟩ := h hys
      refine ⟨append default zs, fun _ ↦ ?_⟩
      rw [cast, realize_castLE_of_eq (by omega), realize_liftAt' (by omega)]
      convert hzs
      grind [append_nat]
    · simp only [not_forall] at hys
      obtain ⟨ys, hys⟩ := hys
      use (append ys default)
      contrapose! hys
      rw [cast, realize_castLE_of_eq (by omega), realize_liftAt' (by omega)] at hys
      convert hys.left
      grind [append_nat]

end BoundedFormula

end Language

end FirstOrder
