import Lax119563Proofs.Compiler.OrderDesc

/-!
# Start positions of the classes of the order

Closed formulas for `clsStart I X` (the position of the first name of class `X` in
`ordL I`), as sums of section sizes and ranks, for every class kind.

* Generic: `startIn_append_left`, `startIn_append_right`, `startIn_flatMap` (a class in the
  block of the `i`-th element of a flat map starts after the blocks of the first `i`
  elements), `startIn_map_const` (blocks of equal size).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

section Generic

variable {α β γ : Type*} [DecidableEq β]

/-- The number of names of a list of classes with labels. -/
def sizeOf' (P : List (β × List γ)) : ℕ := (P.map fun p => p.2.length).sum

@[simp] lemma sizeOf'_nil : sizeOf' ([] : List (β × List γ)) = 0 := rfl
@[simp] lemma sizeOf'_cons (p : β × List γ) (P : List (β × List γ)) :
    sizeOf' (p :: P) = p.2.length + sizeOf' P := by simp [sizeOf']
@[simp] lemma sizeOf'_append (P P' : List (β × List γ)) :
    sizeOf' (P ++ P') = sizeOf' P + sizeOf' P' := by simp [sizeOf']
lemma sizeOf'_flatMap (L : List α) (f : α → List (β × List γ)) :
    sizeOf' (L.flatMap f) = (L.map fun a => sizeOf' (f a)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

lemma startIn_append_left {P P' : List (β × List γ)} {X : β} (h : X ∈ P.map Prod.fst) :
    startIn (P ++ P') X = startIn P X := by
  induction P with
  | nil => simp at h
  | cons p P ih =>
    by_cases hp : p.1 = X
    · simp [startIn, List.takeWhile_cons, hp]
    · have h' : X ∈ P.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hp
        · exact h
      have := ih h'
      simp only [startIn, ne_eq, decide_not] at this ⊢
      simp [List.takeWhile_cons, hp, this]

lemma startIn_append_right {P P' : List (β × List γ)} {X : β} (h : X ∉ P.map Prod.fst) :
    startIn (P ++ P') X = sizeOf' P + startIn P' X := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have hp : p.1 ≠ X := fun e => h (by simp [← e])
    have h' : X ∉ P.map Prod.fst := fun h' => h (by simp at h' ⊢; tauto)
    have := ih h'
    simp only [startIn, sizeOf', ne_eq, decide_not] at this ⊢
    simp [List.takeWhile_cons, hp, this]
    omega

lemma startIn_cons_self (X : β) (ls : List γ) (P : List (β × List γ)) :
    startIn ((X, ls) :: P) X = 0 := by
  simp [startIn, List.takeWhile_cons]

/-- **A class in the `i`-th block of a flat map.** -/
lemma startIn_flatMap (L : List α) (f : α → List (β × List γ)) (i : ℕ) (hi : i < L.length)
    {X : β} (hX : X ∈ (f L[i]).map Prod.fst)
    (hdis : ∀ j < i, ∀ hj : j < L.length, X ∉ (f L[j]).map Prod.fst) :
    startIn (L.flatMap f) X =
      ((L.take i).map fun a => sizeOf' (f a)).sum + startIn (f L[i]) X := by
  have hL : L = L.take i ++ L[i] :: L.drop (i + 1) := by simp
  have hnot : X ∉ ((L.take i).flatMap f).map Prod.fst := by
    simp only [List.map_flatMap, List.mem_flatMap, not_exists, not_and]
    intro a ha hX'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    simp only [List.length_take] at hj
    have hji : j < i := by omega
    rw [List.getElem_take] at hX'
    exact hdis j hji (by omega) (by simpa using hX')
  conv_lhs => rw [hL]
  rw [List.flatMap_append, startIn_append_right hnot, List.flatMap_cons,
    startIn_append_left hX, sizeOf'_flatMap]

/-- A class in the block of the element `a` of a duplicate-free list. -/
lemma startIn_flatMap_of_mem (L : List α) [BEq α] [LawfulBEq α] (hL : L.Nodup)
    (f : α → List (β × List γ)) {a : α} (ha : a ∈ L) {X : β} (hX : X ∈ (f a).map Prod.fst)
    (hdis : ∀ b ∈ L, b ≠ a → X ∉ (f b).map Prod.fst) :
    startIn (L.flatMap f) X =
      ((L.take (L.idxOf a)).map fun b => sizeOf' (f b)).sum + startIn (f a) X := by
  have hi : L.idxOf a < L.length := List.idxOf_lt_length_of_mem ha
  have e : L[L.idxOf a] = a := List.getElem_idxOf hi
  have := startIn_flatMap L f (L.idxOf a) hi (by rw [e]; exact hX) (fun j hj hj' => by
    refine hdis _ (List.getElem_mem _) fun h => ?_
    have := (List.Nodup.getElem_inj_iff hL).mp (h.trans e.symm)
    omega)
  rw [this, e]

/-- Blocks of constant size. -/
lemma sum_map_const (L : List α) (n : ℕ) : (L.map fun _ => n).sum = L.length * n := by
  simp [List.sum_replicate]

end Generic

section Generic2

variable {α β γ : Type*} [BEq α] [LawfulBEq α] [DecidableEq β]

/-- Blocks of one class each, all with the labels `ls`. -/
lemma startIn_map_inj (g : α → β) (hg : Function.Injective g) (ls : List γ) (a : α) :
    ∀ L : List α, startIn (L.map fun b => (g b, ls)) (g a) = L.idxOf a * ls.length
  | [] => by simp [startIn]
  | b :: L => by
    by_cases h : b = a
    · subst h; simp [startIn, List.takeWhile_cons]
    · have hgb : g b ≠ g a := fun e => h (hg e)
      have ih := startIn_map_inj g hg ls a L
      simp only [startIn, ne_eq, decide_not] at ih ⊢
      simp only [List.map_cons, List.takeWhile_cons, hgb, decide_false, Bool.not_false,
        if_true, List.sum_cons, ih, List.idxOf_cons_ne _ h]
      rw [Nat.succ_eq_add_one]; ring

lemma sizeOf'_map_const (g : α → β) (ls : List γ) (L : List α) :
    sizeOf' (L.map fun b => (g b, ls)) = L.length * ls.length := by
  induction L with
  | nil => simp
  | cons b L ih => simp [ih]; ring

lemma sum_take_const (L : List α) (i n : ℕ) (hi : i ≤ L.length) :
    ((L.take i).map fun _ => n).sum = i * n := by
  rw [sum_map_const, List.length_take, min_eq_left hi]

end Generic2

/-! ## The sections of the order -/

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The number of names of schema `e`. -/
noncomputable def schSize (e : Fin I.schemas.length) : ℕ :=
  sizeOf' (hubsCls I e ++ nonhubsCls I e)

/-- The position of the first name of schema `e`. -/
noncomputable def schBase (e : Fin I.schemas.length) : ℕ :=
  (((List.finRange I.schemas.length).take e).map (schSize I)).sum

/-- The position of the first coordinate name. -/
noncomputable def locBase : ℕ := ((List.finRange I.schemas.length).map (schSize I)).sum

/-- The number of names of location `v`. -/
def locSize (v : Fin I.numLocations) : ℕ :=
  (coordList (I.domain v)).length * (coordLabs I v).length

/-- The position of the first name of location `v`. -/
noncomputable def locStart (v : Fin I.numLocations) : ℕ :=
  locBase I + (((List.finRange I.numLocations).take v).map (locSize I)).sum

/-- The width of a column in the junction/link section: `4 + 2` (ternary) or `2`. -/
def colW (e : Fin I.schemas.length) : ℕ := (if isTern (sch I e) then 4 else 0) + 2

/-- The number of entries of schema `e`. -/
def nEnt (e : Fin I.schemas.length) : ℕ :=
  ((coordList (dom I e)).map fun c => (stepsC c).length).sum

/-- The number of entries of the columns before `c`. -/
def entBefore (e : Fin I.schemas.length) (c : Coord k ℓ) : ℕ :=
  (((coordList (dom I e)).take ((coordList (dom I e)).idxOf c)).map
    fun c => (stepsC c).length).sum

/-- The number of hub names of schema `e`. -/
def hubSize (e : Fin I.schemas.length) : ℕ :=
  (coordList (dom I e)).length * colW I e + 4 * nEnt I e

/-- The size of the sum section of schema `e`. -/
def sumSize (e : Fin I.schemas.length) : ℕ :=
  if isTern (sch I e) then 2 * (coordList (dom I e)).length else 0

lemma keySchema_of_mem {e : Fin I.schemas.length} {p : ICls I × List Lab}
    (hp : p ∈ hubsCls I e ++ nonhubsCls I e) : keySchema I p.1 = some e := by
  simp only [hubsCls, nonhubsCls, List.mem_append, List.mem_flatMap, List.mem_map] at hp
  rcases hp with (⟨c, -, hp⟩ | ⟨c, -, σ, -, rfl⟩) | (⟨c, -, hp⟩ | ⟨c, -, σ, -, rfl⟩) |
      ⟨σ, -, rfl⟩
  · rcases hp with hp | hp
    · split at hp
      · simp only [List.mem_singleton] at hp; subst hp; rfl
      · simp at hp
    · simp only [List.mem_singleton] at hp; subst hp; rfl
  · rfl
  · split at hp
    · simp only [List.mem_singleton] at hp; subst hp; rfl
    · simp at hp
  · rfl
  · rfl

/-- A class of schema `e` starts at `schBase e` plus its start within the schema. -/
lemma clsStart_sch {e : Fin I.schemas.length} {X : ICls I}
    (hX : X ∈ (hubsCls I e ++ nonhubsCls I e).map Prod.fst) :
    clsStart I X = schBase I e + startIn (hubsCls I e ++ nonhubsCls I e) X := by
  have hk : keySchema I X = some e := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hX; exact keySchema_of_mem I hp
  unfold clsStart ordCls
  rw [startIn_append_left (by
    simp only [List.map_flatMap, List.mem_flatMap]
    exact ⟨e, List.mem_finRange _, hX⟩)]
  rw [startIn_flatMap_of_mem _ (List.nodup_finRange _) _ (List.mem_finRange e) hX
    (fun e' _ hne hX' => by
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hX'
      have := keySchema_of_mem I hp
      rw [he, hk] at this
      exact hne (Option.some.inj this).symm)]
  simp [schBase]
  congr 3; funext b; simp [schSize]


/-- The junction/link block of column `c`. -/
def jlBlock (e : Fin I.schemas.length) (c : Coord k ℓ) : List (ICls I × List Lab) :=
  (if isTern (sch I e) then [(Cls.junc e c, bits2)] else []) ++ [(Cls.link e c, bits1)]

lemma sizeOf'_jlBlock (e : Fin I.schemas.length) (c : Coord k ℓ) :
    sizeOf' (jlBlock I e c) = colW I e := by
  unfold jlBlock colW; split <;> simp [bits1, bits2]

lemma hubsCls_eq (e : Fin I.schemas.length) :
    hubsCls I e = (coordList (dom I e)).flatMap (jlBlock I e) ++
      (coordList (dom I e)).flatMap fun c => (stepsC c).map fun σ => (Cls.upd e σ c, bits2) :=
  rfl

lemma mem_jl_fst {e : Fin I.schemas.length} {c : Coord k ℓ} {X : ICls I}
    (h : X ∈ (jlBlock I e c).map Prod.fst) : X = Cls.junc e c ∨ X = Cls.link e c := by
  unfold jlBlock at h; split at h <;> simp at h <;> tauto

lemma idxOf_le_length {α : Type*} [BEq α] [LawfulBEq α] (L : List α) (a : α) :
    L.idxOf a ≤ L.length := List.idxOf_le_length

/-- **Junctions.** -/
theorem clsStart_junc {e : Fin I.schemas.length} {c : Coord k ℓ} (ht : isTern (sch I e) = true)
    (hc : c ∈ dom I e) :
    clsStart I (Cls.junc e c) = schBase I e + (coordList (dom I e)).idxOf c * colW I e := by
  have hcD : c ∈ coordList (dom I e) := (mem_coordList).mpr hc
  have hJ : Cls.junc e c ∈ (jlBlock I e c).map Prod.fst := by simp [jlBlock, ht]
  have hJ' : Cls.junc e c ∈ ((coordList (dom I e)).flatMap (jlBlock I e)).map Prod.fst := by
    simp only [List.map_flatMap, List.mem_flatMap]; exact ⟨c, hcD, hJ⟩
  rw [clsStart_sch I (X := Cls.junc e c) (by
    rw [List.map_append, List.mem_append, hubsCls_eq, List.map_append, List.mem_append]
    exact Or.inl (Or.inl hJ')), startIn_append_left (by
      rw [hubsCls_eq, List.map_append, List.mem_append]; exact Or.inl hJ'), hubsCls_eq,
    startIn_append_left hJ', startIn_flatMap_of_mem _ (nodup_coordList _) _ hcD hJ
      (fun c' _ hne h => by rcases mem_jl_fst I h with h | h <;> simp at h <;> tauto)]
  simp only [sizeOf'_jlBlock]
  rw [sum_take_const _ _ _ (idxOf_le_length _ _)]
  simp [jlBlock, ht, startIn_cons_self]

/-- **Links.** -/
theorem clsStart_link {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) :
    clsStart I (Cls.link e c) = schBase I e + (coordList (dom I e)).idxOf c * colW I e +
      (if isTern (sch I e) then 4 else 0) := by
  have hcD : c ∈ coordList (dom I e) := (mem_coordList).mpr hc
  have hJ : Cls.link e c ∈ (jlBlock I e c).map Prod.fst := by
    unfold jlBlock; split <;> simp
  have hJ' : Cls.link e c ∈ ((coordList (dom I e)).flatMap (jlBlock I e)).map Prod.fst := by
    simp only [List.map_flatMap, List.mem_flatMap]; exact ⟨c, hcD, hJ⟩
  rw [clsStart_sch I (X := Cls.link e c) (by
    rw [List.map_append, List.mem_append, hubsCls_eq, List.map_append, List.mem_append]
    exact Or.inl (Or.inl hJ')), startIn_append_left (by
      rw [hubsCls_eq, List.map_append, List.mem_append]; exact Or.inl hJ'), hubsCls_eq,
    startIn_append_left hJ', startIn_flatMap_of_mem _ (nodup_coordList _) _ hcD hJ
      (fun c' _ hne h => by rcases mem_jl_fst I h with h | h <;> simp at h <;> tauto)]
  simp only [sizeOf'_jlBlock]
  rw [sum_take_const _ _ _ (idxOf_le_length _ _)]
  unfold jlBlock
  split
  · simp [startIn, List.takeWhile_cons, bits2]; omega
  · simp [startIn_cons_self]


/-- Classes indexed by a column and an entry of the column. -/
lemma startIn_cols {α β γ δ : Type*} [BEq α] [LawfulBEq α] [BEq δ] [LawfulBEq δ]
    [DecidableEq β] (D : List α) (hD : D.Nodup) (S : α → List δ) (g : α → δ → β)
    (hg : ∀ a b a' b', g a b = g a' b' → a = a' ∧ b = b') (ls : List γ) {c : α} (hc : c ∈ D)
    {σ : δ} (hσ : σ ∈ S c) :
    startIn (D.flatMap fun c => (S c).map fun σ => (g c σ, ls)) (g c σ) =
      ((D.take (D.idxOf c)).map fun c => (S c).length).sum * ls.length +
        (S c).idxOf σ * ls.length := by
  rw [startIn_flatMap_of_mem D hD _ hc (by simp; exact ⟨σ, hσ, rfl⟩) (fun c' _ hne h => by
    simp only [List.map_map, List.mem_map, Function.comp_apply] at h
    obtain ⟨σ', -, he⟩ := h
    exact hne (hg _ _ _ _ he).1)]
  rw [startIn_map_inj (g c) (fun b b' h => (hg _ _ _ _ h).2)]
  simp only [sizeOf'_map_const]
  rw [List.sum_map_mul_right]

end Lax119563Proofs.Compiler
