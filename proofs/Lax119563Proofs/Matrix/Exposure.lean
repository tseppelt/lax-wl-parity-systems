import Lax119563Proofs.Matrix.Shifts

/-!
# Pebbled coordinate sets and exposure

For a set `A` of classes, `Iloc A v` and `Isch A e` are the coordinate sets
`𝔍_v(A)` and `𝔍_e(A)` of the paper. Each class contributes at most one coordinate to each of
them. The geometry lemma: an equation that becomes exposed has at most one variable that
was exposed before.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

variable (I) in
/-- The coordinates contributed to location `v` by an internal class of schema `e` at `c`. -/
def argContrib (e : Fin I.schemas.length) (c : Coord k ℓ) (v : Fin I.numLocations) :
    Finset (Coord k ℓ) :=
  (Finset.univ.filter fun i => argLoc (sch I e) i = v).image fun i => (argPerm (sch I e) i).apply c

/-- The schema and coordinate of an internal class. -/
def inner : ICls I → Option (Fin I.schemas.length × Coord k ℓ)
  | .sum e c => some (e, c)
  | .junc e c => some (e, c)
  | .link e c => some (e, c)
  | .track e _ c => some (e, c)
  | .upd e _ c => some (e, c)
  | _ => none

/-- The coordinates contributed by a class to location `v`. -/
def locContrib (X : ICls I) (v : Fin I.numLocations) : Finset (Coord k ℓ) :=
  match X with
  | .coord v' c => if v' = v then {c} else ∅
  | .coef _ _ => ∅
  | X => match inner X with
    | some (e, c) => argContrib I e c v
    | none => ∅

/-- The coordinates contributed by a class to schema `e`. -/
def schContrib (X : ICls I) (e : Fin I.schemas.length) : Finset (Coord k ℓ) :=
  match inner X with
  | some (e', c) => if e' = e then {c} else ∅
  | none => ∅

/-- The pebbled coordinate set `𝔍_v(A)`. -/
def Iloc (A : Finset (ICls I)) (v : Fin I.numLocations) : Finset (Coord k ℓ) :=
  A.biUnion fun X => locContrib X v

/-- The pebbled coordinate set `𝔍_e(A)`. -/
def Isch (A : Finset (ICls I)) (e : Fin I.schemas.length) : Finset (Coord k ℓ) :=
  A.biUnion fun X => schContrib X e

lemma locContrib_of_inner {X : ICls I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : inner X = some (e, c)) (v : Fin I.numLocations) :
    locContrib X v = argContrib I e c v := by
  cases X <;> simp_all [inner, locContrib]

lemma inner_none {X : ICls I} (h : inner X = none) :
    (∃ v c, X = .coord v c) ∨ ∃ e σ, X = .coef e σ := by
  cases X <;> simp_all [inner]

lemma mem_argContrib {e : Fin I.schemas.length} {c d : Coord k ℓ} {v : Fin I.numLocations} :
    d ∈ argContrib I e c v ↔ ∃ i, argLoc (sch I e) i = v ∧ (argPerm (sch I e) i).apply c = d := by
  simp [argContrib]

lemma card_argContrib_le (e : Fin I.schemas.length) (c : Coord k ℓ) (v : Fin I.numLocations) :
    (argContrib I e c v).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun d hd d' hd' => ?_
  obtain ⟨i, hi, rfl⟩ := mem_argContrib.mp hd
  obtain ⟨j, hj, rfl⟩ := mem_argContrib.mp hd'
  rw [argLoc_injective (sch_wf I e) (hi.trans hj.symm)]

lemma argContrib_self (e : Fin I.schemas.length) (c : Coord k ℓ) (i : Fin (arity (sch I e))) :
    argContrib I e c (argLoc (sch I e) i) = {(argPerm (sch I e) i).apply c} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_argContrib.mpr ⟨i, rfl, rfl⟩, ?_⟩
  intro d hd
  obtain ⟨j, hj, rfl⟩ := mem_argContrib.mp hd
  rw [argLoc_injective (sch_wf I e) hj]

lemma argContrib_nonempty {e : Fin I.schemas.length} {c : Coord k ℓ} {v : Fin I.numLocations}
    (h : (argContrib I e c v).Nonempty) : v ∈ (sch I e).locations := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨i, rfl, -⟩ := mem_argContrib.mp hd
  rw [locations_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

lemma card_locContrib_le (X : ICls I) (v : Fin I.numLocations) : (locContrib X v).card ≤ 1 := by
  cases X with
  | coord v' c => simp only [locContrib]; split <;> simp
  | coef => simp [locContrib]
  | _ => exact card_argContrib_le _ _ _

lemma card_schContrib_le (X : ICls I) (e : Fin I.schemas.length) : (schContrib X e).card ≤ 1 := by
  unfold schContrib
  split
  · split <;> simp
  · simp

lemma card_biUnion_le_card {A : Finset (ICls I)} {f : ICls I → Finset (Coord k ℓ)}
    (h : ∀ X, (f X).card ≤ 1) : (A.biUnion f).card ≤ A.card :=
  (Finset.card_biUnion_le).trans (by simpa using Finset.sum_le_sum fun X (_ : X ∈ A) => h X)

lemma card_Iloc_le (A : Finset (ICls I)) (v : Fin I.numLocations) : (Iloc A v).card ≤ A.card :=
  card_biUnion_le_card fun X => card_locContrib_le X v

lemma card_Isch_le (A : Finset (ICls I)) (e : Fin I.schemas.length) : (Isch A e).card ≤ A.card :=
  card_biUnion_le_card fun X => card_schContrib_le X e

lemma Iloc_mono {A B : Finset (ICls I)} (h : A ⊆ B) (v : Fin I.numLocations) :
    Iloc A v ⊆ Iloc B v := Finset.biUnion_subset_biUnion_of_subset_left _ h

lemma Isch_mono {A B : Finset (ICls I)} (h : A ⊆ B) (e : Fin I.schemas.length) :
    Isch A e ⊆ Isch B e := Finset.biUnion_subset_biUnion_of_subset_left _ h

lemma Iloc_insert (X : ICls I) (A : Finset (ICls I)) (v : Fin I.numLocations) :
    Iloc (insert X A) v = locContrib X v ∪ Iloc A v := Finset.biUnion_insert

lemma Isch_insert (X : ICls I) (A : Finset (ICls I)) (e : Fin I.schemas.length) :
    Isch (insert X A) e = schContrib X e ∪ Isch A e := Finset.biUnion_insert

lemma mem_Isch {A : Finset (ICls I)} {e : Fin I.schemas.length} {c : Coord k ℓ} :
    c ∈ Isch A e ↔ ∃ X ∈ A, inner X = some (e, c) := by
  simp only [Isch, Finset.mem_biUnion, schContrib]
  constructor
  · rintro ⟨X, hX, hc⟩
    split at hc
    · next e' c' h =>
      split at hc
      · next he => simp at hc; subst hc; subst he; exact ⟨X, hX, h⟩
      · simp at hc
    · simp at hc
  · rintro ⟨X, hX, h⟩
    exact ⟨X, hX, by simp [h]⟩

lemma schContrib_of_inner {X : ICls I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : inner X = some (e, c)) (e' : Fin I.schemas.length) :
    schContrib X e' = if e = e' then {c} else ∅ := by
  simp [schContrib, h]

lemma schContrib_of_inner_none {X : ICls I} (h : inner X = none) (e' : Fin I.schemas.length) :
    schContrib X e' = ∅ := by
  simp [schContrib, h]

/-- The argument coordinates of a pebbled schema coordinate are pebbled. -/
lemma Isch_args {A : Finset (ICls I)} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hc : c ∈ Isch A e) (i : Fin (arity (sch I e))) :
    (argPerm (sch I e) i).apply c ∈ Iloc A (argLoc (sch I e) i) := by
  obtain ⟨X, hX, h⟩ := mem_Isch.mp hc
  refine Finset.mem_biUnion.mpr ⟨X, hX, ?_⟩
  rw [locContrib_of_inner h, argContrib_self]
  exact Finset.mem_singleton_self _

/-- Valid classes. -/
def AllValid (A : Finset (ICls I)) : Prop := ∀ X ∈ A, ClsValid I X

lemma ClsValid.inner_dom {X : ICls I} (hX : ClsValid I X) {e : Fin I.schemas.length}
    {c : Coord k ℓ} (h : inner X = some (e, c)) : c ∈ dom I e := by
  cases X <;> simp only [inner, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp_all [ClsValid]

lemma Iloc_subset {A : Finset (ICls I)} (hA : AllValid A) (v : Fin I.numLocations) :
    Iloc A v ⊆ I.domain v := by
  intro d hd0
  obtain ⟨X, hX, hd⟩ := Finset.mem_biUnion.mp hd0
  cases hi : inner X with
  | some p =>
    obtain ⟨e, c⟩ := p
    rw [locContrib_of_inner hi] at hd
    obtain ⟨i, rfl, rfl⟩ := mem_argContrib.mp hd
    exact argPerm_mem (sch_wf I e) ((hA X hX).inner_dom hi) i
  | none =>
    rcases inner_none hi with ⟨v', c, rfl⟩ | ⟨e, σ, rfl⟩
    · simp only [locContrib] at hd
      split at hd
      · next h => subst h; rw [Finset.mem_singleton] at hd; subst hd; exact hA _ hX
      · simp at hd
    · simp [locContrib] at hd

lemma Isch_subset {A : Finset (ICls I)} (hA : AllValid A) (e : Fin I.schemas.length) :
    Isch A e ⊆ dom I e := by
  intro c hc
  obtain ⟨X, hX, h⟩ := mem_Isch.mp hc
  exact (hA X hX).inner_dom h

/-! ### Geometry -/

/-- If an address is covered at location `v` by at most `k` classes, every class contributes
to `v`. -/
lemma cover_all {A : Finset (ICls I)} (hA : A.card ≤ k) {v : Fin I.numLocations}
    {b : Fin k → BlockCoord ℓ} (hb : supp b ⊆ Iloc A v) :
    ∀ X ∈ A, (locContrib X v ∩ supp b).Nonempty := by
  classical
  set F := A.filter fun X => (locContrib X v ∩ supp b).Nonempty
  have hcov : supp b ⊆ F.biUnion fun X => locContrib X v ∩ supp b := by
    intro d hd
    obtain ⟨X, hX, hdX⟩ := Finset.mem_biUnion.mp (hb hd)
    have hne : (locContrib X v ∩ supp b).Nonempty := ⟨d, Finset.mem_inter.mpr ⟨hdX, hd⟩⟩
    exact Finset.mem_biUnion.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, hne⟩,
      Finset.mem_inter.mpr ⟨hdX, hd⟩⟩
  have hk : k ≤ F.card := by
    have := (Finset.card_le_card hcov).trans (card_biUnion_le_card (A := F)
      fun X => (Finset.card_le_card Finset.inter_subset_left).trans (card_locContrib_le X v))
    rwa [card_supp] at this
  have hF : F = A := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (hA.trans hk)
  intro X hX
  rw [← hF] at hX
  exact (Finset.mem_filter.mp hX).2

/-- **Exposure.** If two variables of the equation of schema `e` at address `a` are exposed
for a set of at most `k` classes, the equation itself is exposed. -/
lemma geometry {A : Finset (ICls I)} (hA : A.card ≤ k) (e : Fin I.schemas.length)
    {a : Fin k → BlockCoord ℓ} {i j : Fin (arity (sch I e))} (hij : i ≠ j)
    (hi : supp ((argPerm (sch I e) i).act a) ⊆ Iloc A (argLoc (sch I e) i))
    (hj : supp ((argPerm (sch I e) j).act a) ⊆ Iloc A (argLoc (sch I e) j)) :
    supp a ⊆ Isch A e := by
  have hvv : argLoc (sch I e) i ≠ argLoc (sch I e) j :=
    fun h => hij (argLoc_injective (sch_wf I e) h)
  have hci := cover_all hA hi
  have hcj := cover_all hA hj
  -- every class of `A` is internal to `e`
  have hint : ∀ X ∈ A, ∃ c', inner X = some (e, c') := by
    intro X hX
    obtain ⟨d, hd⟩ := hci X hX
    obtain ⟨d', hd'⟩ := hcj X hX
    have hd1 := (Finset.mem_inter.mp hd).1
    have hd1' := (Finset.mem_inter.mp hd').1
    cases hin : inner X with
    | none =>
      exfalso
      rcases inner_none hin with ⟨v', c, rfl⟩ | ⟨e', σ, rfl⟩
      · simp only [locContrib] at hd1 hd1'
        split at hd1
        · split at hd1'
          · next h1 h2 => exact hvv (h1.symm.trans h2)
          · simp at hd1'
        · simp at hd1
      · simp [locContrib] at hd1
    | some p =>
      obtain ⟨e', c'⟩ := p
      rw [locContrib_of_inner hin] at hd1 hd1'
      by_cases he : e' = e
      · exact ⟨c', he ▸ rfl⟩
      · exfalso
        have l1 := argContrib_nonempty ⟨d, hd1⟩
        have l2 := argContrib_nonempty ⟨d', hd1'⟩
        have m1 : argLoc (sch I e) i ∈ (sch I e).locations := by
          rw [locations_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        have m2 : argLoc (sch I e) j ∈ (sch I e).locations := by
          rw [locations_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact sch_meet' I he hvv l1 l2 m1 m2
  intro c hc
  have hd : (argPerm (sch I e) i).apply c ∈ supp ((argPerm (sch I e) i).act a) := by
    rw [supp_act]; exact Finset.mem_image_of_mem _ hc
  obtain ⟨X, hX, hdX⟩ := Finset.mem_biUnion.mp (hi hd)
  obtain ⟨c', hc'⟩ := hint X hX
  rw [locContrib_of_inner hc', argContrib_self] at hdX
  have : c = c' := bp_apply_injective _ (Finset.mem_singleton.mp hdX)
  subst this
  exact mem_Isch.mpr ⟨X, hX, hc'⟩

end Lax119563Proofs.Matrix
