import Astlib.Basic.SetOperation.MemStructure.Semantics
import Astlib.Basic.SetOperation.Rudimentary.Syntax
import Astlib.Basic.SetOperation.Multiclass.Levy
import Astlib.Basic.SetOperation.Extensional

open FirstOrder Language BoundedFormula DeltaZeroBoundedFormula RudimentaryTerm Fin MemStructure

variable {M : MemStructure}

namespace FirstOrder.Language

namespace MemStructure

def IsUnorderedPair (a x y : M) := ∀ z : M, z ∈ a ↔ z = x ∨ z = y

noncomputable instance : Decidable (∃ a : M, IsUnorderedPair a x y) :=
  Classical.propDecidable _

noncomputable def unorderedPair (x y : M) :=
  dite (∃ a : M, IsUnorderedPair a x y) Classical.choose default

@[inherit_doc] scoped[FirstOrder] notation:max "!{" x ", " y "}" =>
  FirstOrder.Language.MemStructure.unorderedPair x y

def IsSDiff (a x y : M) := ∀ z, z ∈ a ↔ z ∈ x ∧ z ∉ y

noncomputable instance : Decidable (∃ a : M, IsSDiff a x y) :=
  Classical.propDecidable _

noncomputable def sdiff (x y : M) :=
  dite (∃ a : M, IsSDiff a x y) Classical.choose default

noncomputable instance : SDiff M := ⟨sdiff⟩

def IsIUnion (a x : M) (A : M.ClassFunction) := ∀ z, z ∈ a ↔ ∃ y ∈ x, z ∈ A y

noncomputable instance : Decidable (∃ a : M, IsIUnion a x A) :=
  Classical.propDecidable _

noncomputable def iUnion (x : M) (A : M.ClassFunction) :=
  dite (∃ a : M, IsIUnion a x A) Classical.choose default

noncomputable instance (R : M.L.Relations n) (xs : Fin n → M) :
  Decidable (Structure.RelMap R xs) := Classical.propDecidable _

noncomputable instance : EmptyCollection M := ⟨default \ default⟩

end MemStructure

namespace RudimentaryTerm

def castLHom {M : MemStructure} {n : ℕ} (r : M.L'.RudimentaryTerm n) :=
  M.LHom.onRudimentaryTerm r

variable (M : MemStructure) {n : ℕ} (r r₁ r₂ ri : M.L'.RudimentaryTerm n)
  (rf : M.L'.RudimentaryTerm (n + 1))

@[simp]
theorem castLHom_var (k : Fin n) :
    (ᵣk : M.L'.RudimentaryTerm n).castLHom = ᵣk :=
  rfl

@[simp]
theorem castLHom_const (c : M.L'.Constants) :
    (const c : M.L'.RudimentaryTerm n).castLHom = const (M.LHom.onFunction c) :=
  rfl

@[simp]
theorem castLHom_unorderedPair :
    (unorderedPair r₁ r₂).castLHom = unorderedPair r₁.castLHom r₂.castLHom :=
  rfl

@[simp]
theorem castLHom_sdiff :
    (sdiff r₁ r₂).castLHom = sdiff r₁.castLHom r₂.castLHom :=
  rfl

@[simp]
theorem castLHom_sdiff' :
    (r₁ \ r₂).castLHom = r₁.castLHom \ r₂.castLHom :=
  rfl

@[simp]
theorem castLHom_iUnion :
    (iUnion ri rf).castLHom = iUnion ri.castLHom rf.castLHom :=
  rfl

@[simp]
theorem castLHom_char (R : M.L'.Relations 1) :
    (char R r).castLHom = char (M.LHom.onRelation R) r.castLHom :=
  rfl

@[simp]
theorem castLHom_substBoundBound (f : Fin n → Fin m) :
    (r.substBoundBound f).castLHom = r.castLHom.substBoundBound f :=
  LHom.onRudimentaryTerm_substBoundBound _ _ _

@[simp]
theorem castLHom_castLE (h : n ≤ n') :
    (r.castLE h).castLHom = r.castLHom.castLE h :=
  LHom.onRudimentaryTerm_substBoundBound _ _ _

@[simp]
theorem castLHom_castAdd (m : ℕ) :
    (r.castAdd m).castLHom = r.castLHom.castAdd m :=
  LHom.onRudimentaryTerm_substBoundBound _ _ _

@[simp]
theorem castLHom_castSucc :
    r.castSucc.castLHom = r.castLHom.castSucc :=
  LHom.onRudimentaryTerm_substBoundBound _ _ _

@[simp]
theorem castLHom_substBoundRud
    (rs : Fin n → M.L'.RudimentaryTerm m) :
    (r.substBoundRud rs).castLHom =
      r.castLHom.substBoundRud (fun i ↦ (rs i).castLHom) :=
  LHom.onRudimentaryTerm_substBoundRud _ _ _

@[simp]
theorem castLHom_toRudimentaryTerm [M.L.ExtraConstantsUnaryRelationsOnly]
     (t : M.L'.Term' n) :
    t.toRudimentaryTerm.castLHom =
      t.castLHom.toRudimentaryTerm :=
  match t with
  | .var (Sum.inr i) => by simp [Term.toRudimentaryTerm]
  | .func F _ (l := 0) => by simp [Term.toRudimentaryTerm]

variable {L : FirstOrder.Language.{u, v}} [L.HasMem]

instance : Singleton (L.RudimentaryTerm n) (L.RudimentaryTerm n) :=
  ⟨fun r ↦ ᵣ{r, r}⟩

@[simp]
theorem castLHom_singleton (M : MemStructure) (r : M.L'.RudimentaryTerm n) :
    ({r} : M.L'.RudimentaryTerm n).castLHom = {r.castLHom} :=
  rfl

variable {M : MemStructure}

noncomputable def realize {n : ℕ} (r : M.L.RudimentaryTerm n) : M.MulticlassFunction n :=
  match r with
  | var i => fun xs ↦ xs i
  | const c => fun _ ↦ M.L.constantMap c
  | unorderedPair r₁ r₂ => fun xs ↦ M.unorderedPair (r₁.realize xs) (r₂.realize xs)
  | sdiff r₁ r₂ => fun xs ↦ M.sdiff (r₁.realize xs) (r₂.realize xs)
  | iUnion ri rf => fun xs ↦ M.iUnion (ri.realize xs) (fun y ↦ rf.realize (snoc xs y))
  | char R r => fun xs ↦ if M.struc.RelMap R ![r.realize xs] then M.unorderedPair ∅ ∅ else ∅

scoped[FirstOrder.Language] notation:max
  r "〘" xs "〙" => RudimentaryTerm.realize r xs

scoped[FirstOrder.Language] notation:max
  r "〘" x "〙₁" => RudimentaryTerm.realize r ![x]

scoped[FirstOrder.Language] notation:max
  r "〘" x ", " y "〙₂" => RudimentaryTerm.realize r ![x, y]

scoped[FirstOrder.Language] notation:max
  r "〘" x ", " y ", " z "〙₃" => RudimentaryTerm.realize r ![x, y, z]

-- @[simp]
-- noncomputable def realize' (r : M.L'.RudimentaryTerm n) : M.MulticlassFunction n :=
--   r.castLHom.realize

-- scoped[FirstOrder.Language] notation:max
--   r "〘" xs "〙'" => RudimentaryTerm.realize' r xs

-- scoped[FirstOrder.Language] notation:max
--   r "〘" x "〙'₁" => RudimentaryTerm.realize' r ![x]

-- scoped[FirstOrder.Language] notation:max
--   r "〘" x ", " y "〙'₂" => RudimentaryTerm.realize' r ![x, y]

-- scoped[FirstOrder.Language] notation:max
--   r "〘" x ", " y ", " z "〙'₃" => RudimentaryTerm.realize' r ![x, y, z]

variable {n : ℕ} (r₁ r₂ r ri : M.L.RudimentaryTerm n) (rf : M.L.RudimentaryTerm (n + 1))
  (xs : Fin n → M)

@[simp, grind =]
theorem realize_basic (i : Fin n) : (ᵣi)〘xs〙 = xs i := by
  simp [realize]

@[simp, grind =]
theorem realize_const (c : M.L.Functions 0) :
    (const c)〘xs〙 = M.L.constantMap c := by
  simp [realize]

@[simp, grind =]
theorem realize_unorderedPair : ᵣ{r₁, r₂}〘xs〙 = MemStructure.unorderedPair r₁〘xs〙 r₂〘xs〙 := by
  simp [realize]

@[simp, grind =]
theorem realize_sdiff' : (r₁.sdiff r₂)〘xs〙 = r₁〘xs〙 \ r₂〘xs〙 := by
  simp [realize, SDiff.sdiff]

@[simp, grind =]
theorem realize_sdiff : (r₁ \ r₂)〘xs〙 = r₁〘xs〙 \ r₂〘xs〙 := realize_sdiff' _ _ _

-- @[simp, grind =]
theorem realize_iUnion :
    (ri.iUnion rf)〘xs〙 = MemStructure.iUnion ri〘xs〙 fun y ↦ rf〘snoc xs y〙 := by
  simp [realize]

@[simp, grind =]
theorem realize_char :
    (char R r)〘xs〙 = if M.struc.RelMap R ![r.realize xs] then M.unorderedPair ∅ ∅ else ∅ := by
  simp [realize]

@[simp, grind =]
theorem realize_substBoundBound {m : ℕ} (f : Fin n → Fin m) (xs : Fin m → M) :
    (r.substBoundBound f)〘xs〙 = r〘xs ∘ f〙 := by
  induction r generalizing m with
  | var i => simp [substBoundBound]
  | const c => simp [substBoundBound]
  | unorderedPair r₁ r₂ ih₁ ih₂ => simp [substBoundBound, ih₁, ih₂]
  | sdiff r₁ r₂ ih₁ ih₂ => simp [substBoundBound, ih₁, ih₂]
  | iUnion ri rf ihi ihf => simp [substBoundBound, ihi, ihf, realize_iUnion]
  | char R r ih => simp [substBoundBound, ih]

@[simp, grind =]
theorem realize_substBoundRud {m : ℕ}
    (rs : Fin n → M.L.RudimentaryTerm m) (xs : Fin m → M) :
    (r.substBoundRud rs)〘xs〙 = r〘fun i ↦ (rs i)〘xs〙〙 := by
  induction r generalizing m with
  | var i => simp [substBoundRud]
  | const c => simp [substBoundRud]
  | unorderedPair r₁ r₂ ih₁ ih₂ => simp [substBoundRud, ih₁, ih₂]
  | sdiff r₁ r₂ ih₁ ih₂ => simp [substBoundRud, ih₁, ih₂]
  | iUnion ri rf ihi ihf =>
    simp only [substBoundRud, realize_iUnion, ihi, ihf]
    congr
    funext y
    congr
    ext i; cases i using Fin.lastCases <;> simp
  | char R r ih => simp [substBoundRud, ih]

@[simp, grind =]
theorem realize_castLE {n' : ℕ} (h : n ≤ n') (xs : Fin n' → M) :
    (r.castLE h)〘xs〙 = r〘xs ∘ Fin.castLE h〙 := by
  simp [castLE]

@[simp]
theorem realize_castSucc (xs : Fin n → M) :
    (r.castSucc)〘snoc xs x〙 = r〘xs〙 := by
  simp [castSucc, castAdd]

variable {M : MemStructure} [M.L'.ExtraConstantsOnly]

@[simp]
theorem realize_insertNth_eq_lowerAt {t : M.L'.Term' (n + 1)} {k : Fin (n + 1)} (h : t ≠ &k)
    (xs : Fin n → M) (y : M) :
    t.castLHom〘k.insertNth y xs〙 = (t.lowerAt h).castLHom〘xs〙 :=
  match t with
  | .var (Sum.inr i) => by
    simp [Term.lowerAt, Fin.lowerAt]
    have hik : i ≠ k := Ne.intro fun a ↦ h (congrArg Language.var (congrArg Sum.inr a))
    by_cases hik₁ : i < k <;> simp [hik, hik₁, Fin.insertNth, Fin.succAboveCases]
  | .func F _ (l := 0) => by
    simp only [Term.castLHom_func, Term.realize'_func, Term.lowerAt]
    congr
    ext i; fin_cases i
  | .func F _ (l := n + 1) => IsEmpty.elim' (by infer_instance) F

@[simp]
theorem _root_.FirstOrder.Language.Term.realize_toRudimentaryTerm {n}
    [M.L.ExtraConstantsUnaryRelationsOnly] (t : M.L.Term' n)
    (xs : Fin n → M) :
    (t.toRudimentaryTerm)〘xs〙 = t〘xs〙 :=
  match t with
  | .var (Sum.inr i) => by simp [Term.toRudimentaryTerm]
  | .func F _ (l := 0) => by
    simp only [Term.toRudimentaryTerm, realize_const, constantMap, Term.realize'_func]
    congr
    ext i; fin_cases i
  | .func F _ (l := n + 1) => IsEmpty.elim (by infer_instance) F

end RudimentaryTerm

namespace MemStructure


class RudClosed (M : MemStructure) : Prop where
  unorderedPairClosed : ∀ x y, ∃ a : M, IsUnorderedPair a x y
  sdiffClosed : ∀ x y, ∃ a : M, IsSDiff a x y
  iUnionClosed : ∀ {n} (ri : M.L.RudimentaryTerm n) (rf : M.L.RudimentaryTerm (n + 1))
    (xs : Fin n → M), ∃ a, IsIUnion a ri〘xs〙 fun y ↦ rf〘snoc xs y〙

variable {n : ℕ} (x y z a : M)

variable [M.RudClosed]

@[simp, grind =]
theorem mem_unorderedPair_iff : x ∈ unorderedPair y z ↔ x = y ∨ x = z := by
  simp only [unorderedPair, RudClosed.unorderedPairClosed, ↓reduceDIte]
  rw [Classical.choose_spec (RudClosed.unorderedPairClosed y z)]

@[simp, grind =]
theorem mem_sdiff_iff : x ∈ y \ z ↔ x ∈ y ∧ x ∉ z := by
  simp only [SDiff.sdiff, sdiff, RudClosed.sdiffClosed, ↓reduceDIte, ]
  rw [Classical.choose_spec (RudClosed.sdiffClosed y z)]

@[simp]
theorem mem_realize_iUnion_iff
    {n : ℕ} (ri : M.L.RudimentaryTerm n) (rf : M.L.RudimentaryTerm (n + 1))
    (xs : Fin n → M) (x : M) :
    x ∈ (ri.iUnion rf)〘xs〙 ↔
      ∃ z ∈ ri〘xs〙, x ∈ rf〘snoc xs z〙 := by
  simp only [iUnion, RudClosed.iUnionClosed, ↓reduceDIte, realize_iUnion]
  rw [Classical.choose_spec (RudClosed.iUnionClosed _ _ _)]

-- @[simp]
-- theorem mem_iUnion_iff {n : ℕ} (ri : M.L.RudimentaryTerm n) (rf : M.L.RudimentaryTerm (n + 1))
--     (xs : Fin n → M) (x : M) :
--     x ∈ iUnion ri〘xs〙 (fun y ↦ rf〘snoc xs y〙) ↔
--       ∃ z ∈ ri〘xs〙, x ∈ rf〘snoc xs z〙 := by
--   simp only [iUnion, RudClosed.iUnionClosed, ↓reduceDIte]
--   rw [Classical.choose_spec (RudClosed.iUnionClosed _ _ _)]

-- @[simp]
-- theorem mem_iUnion_iff' [M.L.ExtraConstantsUnaryRelationsOnly]
--     {n : ℕ} (t : M.L.Term' n) (rf : M.L.RudimentaryTerm (n + 1))
--     (xs : Fin n → M) (x : M) :
--     x ∈ iUnion t〘xs〙 (fun y ↦ rf〘snoc xs y〙) ↔
--       ∃ z ∈ t〘xs〙, x ∈ rf〘snoc xs z〙 := by
--   convert mem_iUnion_iff t.toRudimentaryTerm rf xs x <;> simp


end MemStructure

namespace RudimentaryTerm

variable [M.Extensional] [M.RudClosed]

mutual
  @[simp]
  theorem realize_hasMem {n : ℕ} (r : M.L'.RudimentaryTerm n) (t : M.L'.Term' n)
      (xs : Fin n → M) :
      (r.hasMem t).castLHom.toBoundedFormula 〘xs〙 ↔ t.castLHom〘xs〙 ∈ r.castLHom〘xs〙 :=
    match r with
    | .var i => by simp [hasMem]
    | .const c => by simp [hasMem]
    | .unorderedPair r₁ r₂ => by simp [hasMem, r₁.realize_eq, r₂.realize_eq]
    | .sdiff r₁ r₂ => by simp [hasMem, r₁.realize_hasMem, r₂.realize_hasMem]
    | .iUnion ri rf => by simp [hasMem, ri.realize_exMem, rf.realize_hasMem]
    | .char R _ => IsEmpty.elim (by infer_instance) R
    termination_by (r.depth, 1, 0)
    decreasing_by all_goals simp [depth, Prod.lex_def]

  @[simp]
  theorem realize_eq {n : ℕ} (r : M.L'.RudimentaryTerm n) (t : M.L'.Term' n)
      (xs : Fin n → M) :
      (r.eq t).castLHom.toBoundedFormula 〘xs〙 ↔ t.castLHom〘xs〙 = r.castLHom〘xs〙 :=
    match r with
    | .var i => by simp [eq, castLHom]
    | .const c => by simp [eq, castLHom]
    | .unorderedPair r₁ r₂ => by
      simp only [eq, Function.comp_apply, DeltaZeroBoundedFormula.castLHom_inf,
        DeltaZeroBoundedFormula.castLHom_allMem, DeltaZeroBoundedFormula.castLHom_sup,
        toBoundedFormula_inf, toBoundedFormula, toBoundedFormula_sup, realize'_inf, r₁.realize_mem,
        r₂.realize_mem, BoundedFormula.realize_allMem, realize'_sup, r₁.castSucc.realize_eq,
        Term.castLHom_var', Term.realize'_var', snoc_last, castLHom_castSucc,
        realize_castSucc, r₂.castSucc.realize_eq, castLHom_unorderedPair, realize_unorderedPair]
      rw [MemStructure.ext_iff]
      grind
    | .sdiff r₁ r₂ => by
      simp only [eq, Function.comp_apply, Term.castSucc, Term.castAdd, Term.castLE,
        castLE_succ_castSucc, DeltaZeroBoundedFormula.castLHom_inf,
        DeltaZeroBoundedFormula.castLHom_allMem, DeltaZeroBoundedFormula.castLHom_not,
        toBoundedFormula_inf, toBoundedFormula, toBoundedFormula_not, realize'_inf,
        BoundedFormula.realize_allMem, r₁.castSucc.realize_hasMem, castLHom_castSucc,
        realize_castSucc, Term.castLHom_var', Term.realize'_var', snoc_last, realize'_not,
        r₂.castSucc.realize_hasMem, r₁.realize_allMem, DeltaZeroBoundedFormula.castLHom_sup,
        DeltaZeroBoundedFormula.castLHom_mem, Term.castLHom_substBoundBound, toBoundedFormula_sup,
        realize'_sup, realize'_mem, Term.realize'_substBoundBound, snoc_comp_castSucc,
        castLHom_sdiff, realize_sdiff']
      rw [MemStructure.ext_iff]
      grind
    | .iUnion ri rf => by
      simp only [eq, Function.comp_apply, Term.castAdd, Term.castLE,
        DeltaZeroBoundedFormula.castLHom_inf, DeltaZeroBoundedFormula.castLHom_allMem,
        toBoundedFormula_inf, toBoundedFormula, realize'_inf, BoundedFormula.realize_allMem,
        ri.castSucc.realize_exMem, castLHom_castSucc, realize_castSucc,
        (rf.substBoundBound (snoc (Fin.castAdd 2) (last (n + 1)))).realize_hasMem,
        castLHom_substBoundBound, realize_substBoundBound, snoc_snoc_comp_snoc_castAdd_two_last,
        Term.castLHom_var', Term.realize'_var', snoc_snoc_castAdd_one_last, ri.realize_allMem,
        rf.realize_allMem, DeltaZeroBoundedFormula.castLHom_mem, Term.castLHom_substBoundBound,
        realize'_mem, Term.realize'_substBoundBound, le_add_iff_nonneg_right, _root_.zero_le,
        snoc_comp_castLE, castLE_succ_castSucc, snoc_comp_castSucc, snoc_last, castLHom_iUnion]
      simp only [MemStructure.ext_iff, mem_realize_iUnion_iff]
      grind
    | .char R _ => IsEmpty.elim (by infer_instance) R
    termination_by (r.depth, 1, 0)
    decreasing_by all_goals simp [depth, castSucc, castAdd, castLE, Prod.lex_def]

  @[simp]
  theorem realize_mem {n : ℕ} (r : M.L'.RudimentaryTerm n) (t : M.L'.Term' n)
      (xs : Fin n → M) :
      (r.mem t).castLHom.toBoundedFormula 〘xs〙 ↔ r.castLHom〘xs〙 ∈ t.castLHom〘xs〙 := by
    simp [mem, r.castSucc.realize_eq]
    termination_by (r.depth, 2, 0)
    decreasing_by simp [castSucc, castAdd, castLE, Prod.lex_def]

  @[simp]
  theorem realize_memSelf {n : ℕ} (r : M.L'.RudimentaryTerm n)
      (xs : Fin n → M) :
      (r.memSelf).castLHom.toBoundedFormula 〘xs〙 ↔ r.castLHom〘xs〙 ∈ r.castLHom〘xs〙 := by
    simp [memSelf, r.realize_exMem, r.castSucc.realize_eq]
    termination_by (r.depth, 3, 0)
    decreasing_by all_goals simp [castSucc, castAdd, castLE, Prod.lex_def]

  @[simp]
  theorem realize_allMem {n : ℕ} (r : M.L'.RudimentaryTerm n)
      (φ : M.L'.DeltaZeroBoundedFormula (n + 1)) (xs : Fin n → M) :
      (r.allMem φ).castLHom.toBoundedFormula 〘xs〙 ↔
        ∀ y ∈ r.castLHom〘xs〙, φ.castLHom.toBoundedFormula 〘snoc xs y〙:=
    match r with
    | .var i => by simp [allMem]
    | .const c => by simp [allMem]
    | .unorderedPair r₁ r₂ => by
      simp [allMem, r₁.realize_substLowerAt (k := Fin.last n),
        r₂.realize_substLowerAt (k := Fin.last n)]
    | .sdiff r₁ r₂ => by
      simp only [allMem, Function.comp_apply, r₁.realize_allMem,
        DeltaZeroBoundedFormula.castLHom_sup, toBoundedFormula_sup, realize'_sup,
        r₂.castSucc.realize_hasMem, castLHom_castSucc, realize_castSucc,
        Term.castLHom_var', Term.realize'_var', snoc_last, castLHom_sdiff, realize_sdiff',
        mem_sdiff_iff, and_imp]
      grind
    | .iUnion ri rf => by
      simp only [allMem, ri.realize_allMem, rf.realize_allMem,
        DeltaZeroBoundedFormula.castLHom_substBoundBound, coe_substBoundBound,
        realize'_substBoundBound, snoc_snoc_comp_snoc_castAdd_two_last, castLHom_iUnion,
        mem_realize_iUnion_iff, forall_exists_index, and_imp]
      grind
    | .char R _ => IsEmpty.elim (by infer_instance) R
    termination_by (r.depth, 1, 0)
    decreasing_by all_goals simp [castSucc, castAdd, castLE, depth, Prod.lex_def]

  @[simp]
  theorem realize_exMem {n : ℕ} (r : M.L'.RudimentaryTerm n)
      (φ : M.L'.DeltaZeroBoundedFormula (n + 1)) (xs : Fin n → M) :
      (r.exMem φ).castLHom.toBoundedFormula 〘xs〙 ↔
        ∃ y ∈ r.castLHom〘xs〙, φ.castLHom.toBoundedFormula 〘snoc xs y〙:= by
    simp [exMem, r.realize_allMem]
    termination_by (r.depth, 2, 0)
    decreasing_by all_goals simp [Prod.lex_def]

  @[simp]
  theorem realize_substLowerAt {n : ℕ} {k : Fin (n + 1)}
      (r : M.L'.RudimentaryTerm k.val)
      (φ : M.L'.DeltaZeroBoundedFormula (n + 1)) (xs : Fin n → M) :
      (r.substLowerAt φ).castLHom.toBoundedFormula 〘xs〙 ↔
        φ.castLHom.toBoundedFormula 〘Fin.insertNth k (r.castLHom 〘xs ∘ (Fin.castLE (is_le k))〙) xs〙 :=
  match φ with
  | .falsum => by simp [substLowerAt]
  | .equal t₁ t₂ => by
    simp only [substLowerAt, Function.comp_apply, DeltaZeroBoundedFormula.castLHom_bdEqual,
      toBoundedFormula, realize'_bdEqual]
    split_ifs with h₁₂ h₁ h₂
    · simp [h₁₂]
    · rw [h₁] at h₁₂
      simp [h₁, Ne.symm h₁₂, (r.castLE (is_le k)).realize_eq]
      tauto
    · rw [h₂] at h₁₂
      simp [h₂, h₁₂, (r.castLE (is_le k)).realize_eq]
    · simp [h₁, h₂]
  | .mem t₁ t₂ => by
    simp only [substLowerAt, Function.comp_apply, DeltaZeroBoundedFormula.castLHom_mem,
      toBoundedFormula, realize'_mem]
    split_ifs with h₁ h₁₂ h₂
    · simp [(r.castLE (is_le k)).realize_memSelf, h₁, h₁₂]
    · rw [h₁] at h₁₂
      simp [h₁, h₁₂, (r.castLE (is_le k)).realize_mem]
    · simp [h₁, h₂, (r.castLE (is_le k)).realize_hasMem]
    · simp [h₁, h₂]
  | .imp φ₁ φ₂ => by simp [substLowerAt, r.realize_substLowerAt φ₁, r.realize_substLowerAt φ₂]
  | .allMem t ψ => by
    simp only [substLowerAt, Function.comp_apply, ne_eq, dite_not,
      DeltaZeroBoundedFormula.castLHom_allMem, toBoundedFormula, BoundedFormula.realize_allMem]
    split_ifs with h
    · simp [(r.castLE (is_le k)).realize_allMem, r.realize_substLowerAt (k := k.castSucc) ψ,
        h, is_le k]
    · simp [r.realize_substLowerAt (k := k.castSucc) ψ, h, is_le k]
  | .rel R  _ => IsEmpty.elim (by infer_instance) R
    termination_by (r.depth, 4, sizeOf φ)
    decreasing_by all_goals simp [castLE, Prod.lex_def, Nat.lt_add_right]
end

end RudimentaryTerm

namespace Term

variable {M : MemStructure} [M.L'.ExtraConstantsOnly]

@[simp, grind =]
theorem realize_substBoundRud {m : ℕ} (t : M.L'.Term' n)
    (rs : Fin n → M.L'.RudimentaryTerm m) (xs : Fin m → M) :
    (t.substBoundRud rs).castLHom〘xs〙 = t.castLHom〘fun i ↦ (rs i).castLHom〘xs〙〙 :=
  match t with
  | .var (Sum.inr i) => by simp [substBoundRud]
  | .func F _ (l := 0) => by simp [substBoundRud, funMap_eq_coe_constants]
  | .func F _ (l := n + 1) => IsEmpty.elim (by infer_instance) F

end Term

namespace DeltaZeroBoundedFormula

variable {n m : ℕ} {M : MemStructure} [M.L'.ExtraConstantsOnly] [M.RudClosed] [M.Extensional]

@[simp]
theorem realize_substBoundRud {φ : M.L'.DeltaZeroBoundedFormula n}
    (rs : Fin n → M.L'.RudimentaryTerm m)
    (xs : Fin m → M) :
    (φ.substBoundRud rs).castLHom.toBoundedFormula 〘xs〙 ↔
      φ.castLHom.toBoundedFormula 〘fun i ↦ (rs i).castLHom〘xs〙〙:= by
  induction φ generalizing m with
  | falsum => simp [substBoundRud]
  | equal t₁ t₂ =>
    simp only [substBoundRud, Function.comp_apply, toBoundedFormula_inf, castLHom_inf, realize'_inf,
      RudimentaryTerm.realize_allMem, Term.realize_substBoundRud, realize_hasMem,
      castLHom_castSucc, realize_castSucc, Term.castLHom_var', Term.realize'_var',
      snoc_last, toBoundedFormula, castLHom_bdEqual, realize'_bdEqual]
    rw [MemStructure.ext_iff]
    grind
  | mem t₁ t₂ => simp [substBoundRud, realize'_mem]
  | imp φ₁ φ₂ ih₁ ih₂ => simp [substBoundRud, ih₁, ih₂]
  | allMem t ψ ih =>
    simp only [substBoundRud, RudimentaryTerm.realize_allMem, Term.realize_substBoundRud, ih,
      toBoundedFormula, castLHom_allMem, BoundedFormula.realize_allMem]
    rw [forall_congr]
    intro y
    congr
    funext i; cases i using Fin.lastCases <;> simp
  | rel R t => exact IsEmpty.elim (by infer_instance) R

theorem multiclass_substBoundRud_eq_subst {φ : M.L'.DeltaZeroBoundedFormula n}
    (rs : Fin n → M.L'.RudimentaryTerm m) :
    (φ.substBoundRud rs).castLHom.toBoundedFormula.multiclass =
      φ.castLHom.toBoundedFormula.multiclass.subst (fun i xs ↦ (rs i).castLHom〘xs〙) := by
  funext ys
  simp [Multiclass.subst]

variable {L' : Language} [L'.HasMem] [L'.ExtraConstantsOnly]

noncomputable def _root_.FirstOrder.Language.RudimentaryTerm.toDeltaZeroBoundedFormula
  (r : L'.RudimentaryTerm n) :
  L'.DeltaZeroBoundedFormula (n + 1) :=
  (&0 =₀ &1).substBoundRud ![r.castSucc, ᵣ-1]

theorem _root_.FirstOrder.Language.RudimentaryTerm.realize_eq_toDeltaZeroBoundedFormula
    (r : M.L'.RudimentaryTerm m) :
    r.castLHom.realize = r.toDeltaZeroBoundedFormula.castLHom.toBoundedFormula.multiclass := by
  simp only [toDeltaZeroBoundedFormula, Nat.succ_eq_add_one, Nat.reduceAdd, isValue,
    Function.comp_apply, multiclass_substBoundRud_eq_subst, castLHom_bdEqual, Term.castLHom_var',
    toBoundedFormula]
  funext xs
  rw [← Fin.snoc_init_self xs, MulticlassFunction.toMulticlass_snoc_iff]
  simp [Multiclass.subst, RudimentaryTerm.castSucc, RudimentaryTerm.castAdd, init_def]

end DeltaZeroBoundedFormula

namespace MemStructure

-- namespace Multiclass

-- variable {n m : ℕ} {M : MemStructure} [M.RudClosed] [M.Extensional]
--   (P : Set M)

-- theorem isDeltaZero_subst_rudimentaryTerm {A : M.Multiclass n} [hA : A.DeltaZero P]
--     (rs : Fin n → M.L'.RudimentaryTerm m) :
--     (A.subst fun i xs ↦ (rs i).castLHom〘xs〙).IsDeltaZero P := by
--   obtain ⟨l, _, ⟨⟨φ, rfl⟩⟩, ys, hys, rfl⟩ := hA
--   refine ⟨l,
--     (φ.substBoundRud (append (fun i ↦ (rs i).castAdd l) (fun i ↦ ᵣ(i.natAdd m)))).toBoundedFormula,
--     by infer_instance, ys, hys, ?_⟩
--   simp only [subst_slice_eq_slice_subst, multiclass_substBoundRud_eq_subst]
--   congr
--   funext i; cases i using Fin.addCases
--   · simp only [append_left, RudimentaryTerm.castAdd, realize_castLE]
--     rfl
--   · simp

-- -- theorem isDeltaZero_rudimentaryTerm
-- --     (r : M.L'.RudimentaryTerm m) :
-- --     (r.realize : M.Multiclass (m + 1)).IsDeltaZero P := by
-- --   convert isDeltaZero_subst_rudimentaryTerm (A := Multiclass.Eq 2 0 1) (P := P)
-- --     (rs := ![r.castSucc, ᵣ-1])
-- --   funext ys
-- --   rw [← Fin.snoc_init_self ys, MulticlassFunction.toMulticlass_snoc_iff]
-- --   simp [subst, RudimentaryTerm.castSucc, RudimentaryTerm.castAdd, init_def]

-- instance {A : M.Multiclass n} [A.DeltaZero P] (rs : Fin n → M.L'.RudimentaryTerm m) :
--   (A.subst fun i xs ↦ (rs i).castLHom〘xs〙).DeltaZero P :=
--   ⟨isDeltaZero_subst_rudimentaryTerm _ _⟩

-- instance (r : M.L'.RudimentaryTerm m) :
--   (r.castLHom.realize : M.Multiclass (m + 1)).DeltaZero P := by
--   rw [RudimentaryTerm.realize_eq_toDeltaZeroBoundedFormula]
--   infer_instance

-- end Multiclass

end MemStructure



end FirstOrder.Language
