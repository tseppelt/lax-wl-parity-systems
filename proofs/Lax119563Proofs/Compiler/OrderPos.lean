import Lax119563Proofs.Compiler.OrderDesc

/-!
# Start positions of the classes of the order

Closed formulas for `clsStart I X` (the position of the first name of class `X` in
`ordL I`), as sums of section sizes and ranks, for every class kind.

* Generic: `startIn_append_left`, `startIn_append_right`, `startIn_flatMap` (a class in the
  block of the `i`-th element of a flat map starts after the blocks of the first `i`
  elements), `startIn_map_inj`, `startIn_cols`.
* Sections: `schSize`, `schBase`, `locBase`, `locSize`, `locStart`, `colW`, `nEnt`,
  `entBefore`, `hubSize`, `sumSize`; `clsStart_junc`, `clsStart_link`, `clsStart_upd`,
  `clsStart_sum`, `clsStart_track`, `clsStart_coef`, `clsStart_coord`.
* Slots: `slot_mem_ordCls` (every slot class of a name of the order is a class of the order
  with labels `slotLabs`: `[(0,0)]` for initialized coordinate classes, else `bits1`).
* Tracks: `trackAt_stepsC` (the track before the entry `j` of a column is the entry `j - 1`,
  or the start class), `trackAt_numSteps` (the last entry), `stepsC_ne_nil` (`k ≥ 2`).
* Order: `schBase_add_le`.
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


lemma sizeOf'_jl (e : Fin I.schemas.length) :
    sizeOf' ((coordList (dom I e)).flatMap (jlBlock I e)) =
      (coordList (dom I e)).length * colW I e := by
  rw [sizeOf'_flatMap]; simp only [sizeOf'_jlBlock]; rw [sum_map_const]

lemma sizeOf'_ent (e : Fin I.schemas.length) (g : Coord k ℓ → ℕ → ICls I) (ls : List Lab) :
    sizeOf' ((coordList (dom I e)).flatMap fun c => (stepsC c).map fun σ => (g c σ, ls)) =
      nEnt I e * ls.length := by
  rw [sizeOf'_flatMap]; simp only [sizeOf'_map_const]
  rw [nEnt, List.sum_map_mul_right]

lemma sizeOf'_hubsCls (e : Fin I.schemas.length) : sizeOf' (hubsCls I e) = hubSize I e := by
  rw [hubsCls_eq, sizeOf'_append, sizeOf'_jl, sizeOf'_ent]; simp [hubSize, bits2]; ring

/-- The sum part of the non-hubs. -/
def sumPart (e : Fin I.schemas.length) : List (ICls I × List Lab) :=
  (coordList (dom I e)).flatMap fun c => if isTern (sch I e) then [(Cls.sum e c, bits1)] else []

/-- The track part of the non-hubs. -/
def trackPart (e : Fin I.schemas.length) : List (ICls I × List Lab) :=
  (coordList (dom I e)).flatMap fun c => (stepsC c).map fun σ => (Cls.track e σ c, bits1)

lemma nonhubsCls_eq (e : Fin I.schemas.length) :
    nonhubsCls I e = sumPart I e ++ trackPart I e ++
      (coefSteps I e).map fun σ => (Cls.coef e σ, bits1) := rfl

lemma sizeOf'_sumPart (e : Fin I.schemas.length) : sizeOf' (sumPart I e) = sumSize I e := by
  rw [sumPart, sizeOf'_flatMap, sumSize]
  split
  · simp [bits1, sum_map_const]; ring
  · simp

lemma mem_sumPart_fst {e : Fin I.schemas.length} {X : ICls I}
    (h : X ∈ (sumPart I e).map Prod.fst) : ∃ c, X = Cls.sum e c := by
  simp only [sumPart, List.map_flatMap, List.mem_flatMap] at h
  obtain ⟨c, -, h⟩ := h
  split at h <;> simp at h; exact ⟨c, h⟩

lemma mem_trackPart_fst {e : Fin I.schemas.length} {X : ICls I}
    (h : X ∈ (trackPart I e).map Prod.fst) : ∃ σ c, X = Cls.track e σ c := by
  simp only [trackPart, List.map_flatMap, List.mem_flatMap, List.map_map, List.mem_map,
    Function.comp_apply] at h
  obtain ⟨c, -, σ, -, h⟩ := h
  exact ⟨σ, c, h.symm⟩

lemma mem_hubsCls_fst {e : Fin I.schemas.length} {X : ICls I}
    (h : X ∈ (hubsCls I e).map Prod.fst) : isHub I X = true := by
  rw [hubsCls_eq, List.map_append, List.mem_append] at h
  rcases h with h | h
  · simp only [List.map_flatMap, List.mem_flatMap] at h
    obtain ⟨c, -, h⟩ := h
    rcases mem_jl_fst I h with rfl | rfl <;> rfl
  · simp only [List.map_flatMap, List.mem_flatMap, List.map_map, List.mem_map,
      Function.comp_apply] at h
    obtain ⟨c, -, σ, -, rfl⟩ := h
    rfl

/-- A non-hub class of schema `e` starts after the hubs. -/
lemma clsStart_nonhub {e : Fin I.schemas.length} {X : ICls I}
    (hX : X ∈ (nonhubsCls I e).map Prod.fst) (hh : isHub I X = false) :
    clsStart I X = schBase I e + hubSize I e + startIn (nonhubsCls I e) X := by
  rw [clsStart_sch I (by rw [List.map_append, List.mem_append]; exact Or.inr hX),
    startIn_append_right (fun h => by rw [mem_hubsCls_fst I h] at hh; cases hh),
    sizeOf'_hubsCls]
  ring

/-- **Updates.** -/
theorem clsStart_upd {e : Fin I.schemas.length} {c : Coord k ℓ} {σ : ℕ} (hc : c ∈ dom I e)
    (hσ : σ ∈ stepsC c) :
    clsStart I (Cls.upd e σ c) = schBase I e + (coordList (dom I e)).length * colW I e +
      4 * (entBefore I e c + (stepsC c).idxOf σ) := by
  have hcD : c ∈ coordList (dom I e) := (mem_coordList).mpr hc
  have hU : (Cls.upd e σ c : ICls I) ∈ ((coordList (dom I e)).flatMap fun c =>
      (stepsC c).map fun σ => (Cls.upd e σ c, bits2)).map Prod.fst := by
    simp only [List.map_flatMap, List.mem_flatMap, List.map_map, List.mem_map,
      Function.comp_apply]
    exact ⟨c, hcD, σ, hσ, rfl⟩
  have hnJ : (Cls.upd e σ c : ICls I) ∉ ((coordList (dom I e)).flatMap (jlBlock I e)).map Prod.fst := by
    simp only [List.map_flatMap, List.mem_flatMap, not_exists, not_and]
    intro c' _ h; rcases mem_jl_fst I h with h | h <;> cases h
  rw [clsStart_sch I (X := Cls.upd e σ c) (by
      rw [List.map_append, List.mem_append, hubsCls_eq, List.map_append, List.mem_append]
      exact Or.inl (Or.inr hU)),
    startIn_append_left (by rw [hubsCls_eq, List.map_append, List.mem_append]; exact Or.inr hU),
    hubsCls_eq, startIn_append_right hnJ, sizeOf'_jl,
    startIn_cols (coordList (dom I e)) (nodup_coordList _) stepsC (fun c σ => (Cls.upd e σ c : ICls I))
      (fun a b a' b' h => by cases h; exact ⟨rfl, rfl⟩) bits2 hcD hσ]
  simp [entBefore, bits2]; ring

/-- **Sums.** -/
theorem clsStart_sum {e : Fin I.schemas.length} {c : Coord k ℓ} (ht : isTern (sch I e) = true)
    (hc : c ∈ dom I e) :
    clsStart I (Cls.sum e c) = schBase I e + hubSize I e + 2 * (coordList (dom I e)).idxOf c := by
  have hcD : c ∈ coordList (dom I e) := (mem_coordList).mpr hc
  have hS : (Cls.sum e c : ICls I) ∈ (sumPart I e).map Prod.fst := by
    simp only [sumPart, List.map_flatMap, List.mem_flatMap]
    exact ⟨c, hcD, by simp [ht]⟩
  rw [clsStart_nonhub I (by
      rw [nonhubsCls_eq, List.map_append, List.mem_append, List.map_append, List.mem_append]
      exact Or.inl (Or.inl hS)) rfl,
    nonhubsCls_eq, startIn_append_left (by
      rw [List.map_append, List.mem_append]; exact Or.inl hS),
    startIn_append_left hS, sumPart,
    startIn_flatMap_of_mem _ (nodup_coordList _) _ hcD (by simp [ht]) (fun c' _ hne h => by
      split at h <;> simp at h <;> exact hne h.symm)]
  simp only [ht, if_true, sizeOf'_cons, sizeOf'_nil]
  rw [sum_take_const _ _ _ (idxOf_le_length _ _), startIn_cons_self]
  simp [bits1]; ring

/-- **Tracks.** -/
theorem clsStart_track {e : Fin I.schemas.length} {c : Coord k ℓ} {σ : ℕ} (hc : c ∈ dom I e)
    (hσ : σ ∈ stepsC c) :
    clsStart I (Cls.track e σ c) = schBase I e + hubSize I e + sumSize I e +
      2 * (entBefore I e c + (stepsC c).idxOf σ) := by
  have hcD : c ∈ coordList (dom I e) := (mem_coordList).mpr hc
  have hT : (Cls.track e σ c : ICls I) ∈ (trackPart I e).map Prod.fst := by
    simp only [trackPart, List.map_flatMap, List.mem_flatMap, List.map_map, List.mem_map,
      Function.comp_apply]
    exact ⟨c, hcD, σ, hσ, rfl⟩
  rw [clsStart_nonhub I (by
      rw [nonhubsCls_eq, List.map_append, List.mem_append, List.map_append, List.mem_append]
      exact Or.inl (Or.inr hT)) rfl,
    nonhubsCls_eq, startIn_append_left (by
      rw [List.map_append, List.mem_append]; exact Or.inr hT),
    startIn_append_right (fun h => by obtain ⟨c', h⟩ := mem_sumPart_fst I h; cases h),
    sizeOf'_sumPart, trackPart,
    startIn_cols (coordList (dom I e)) (nodup_coordList _) stepsC (fun c σ => (Cls.track e σ c : ICls I))
      (fun a b a' b' h => by cases h; exact ⟨rfl, rfl⟩) bits1 hcD hσ]
  simp [entBefore, bits1]; ring

/-- **Coefficients.** -/
theorem clsStart_coef {e : Fin I.schemas.length} {σ : ℕ} (hσ : σ ∈ coefSteps I e) :
    clsStart I (Cls.coef e σ) = schBase I e + hubSize I e + sumSize I e + 2 * nEnt I e +
      2 * (coefSteps I e).idxOf σ := by
  have hC : (Cls.coef e σ : ICls I) ∈ ((coefSteps I e).map fun σ => (Cls.coef e σ, bits1)).map
      Prod.fst := by simpa using hσ
  rw [clsStart_nonhub I (by
      rw [nonhubsCls_eq, List.map_append, List.mem_append]; exact Or.inr hC) rfl,
    nonhubsCls_eq, startIn_append_right (fun h => by
      rw [List.map_append, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨c', h⟩ := mem_sumPart_fst I h; cases h
      · obtain ⟨_, _, h⟩ := mem_trackPart_fst I h; cases h),
    sizeOf'_append, sizeOf'_sumPart, trackPart, sizeOf'_ent,
    startIn_map_inj (fun σ => (Cls.coef e σ : ICls I)) (fun a b h => by cases h; rfl)]
  simp [bits1]; ring

/-- **Coordinate classes.** -/
theorem clsStart_coord {v : Fin I.numLocations} {c : Coord k ℓ} (hc : c ∈ I.domain v) :
    clsStart I (Cls.coord v c) =
      locStart I v + (coordList (I.domain v)).idxOf c * (coordLabs I v).length := by
  have hcD : c ∈ coordList (I.domain v) := (mem_coordList).mpr hc
  have hnS : (Cls.coord v c : ICls I) ∉ ((List.finRange I.schemas.length).flatMap
      fun e => hubsCls I e ++ nonhubsCls I e).map Prod.fst := by
    simp only [List.map_flatMap, List.mem_flatMap, not_exists, not_and]
    intro e _ h
    obtain ⟨p, hp, he⟩ := List.mem_map.mp h
    have := keySchema_of_mem I hp
    rw [he] at this; cases this
  unfold clsStart ordCls
  rw [startIn_append_right hnS, sizeOf'_flatMap,
    startIn_flatMap_of_mem _ (List.nodup_finRange _) _ (List.mem_finRange v)
      (X := (Cls.coord v c : ICls I)) (by
        simp only [List.map_map, List.mem_map, Function.comp_apply]; exact ⟨c, hcD, rfl⟩)
      (fun v' _ hne h => by
        simp only [List.map_map, List.mem_map, Function.comp_apply] at h
        obtain ⟨_, -, h⟩ := h
        cases h; exact hne rfl),
    startIn_map_inj (fun c => (Cls.coord v c : ICls I)) (fun a b h => by cases h; rfl)]
  have h1 : (List.map (fun a => sizeOf' (hubsCls I a ++ nonhubsCls I a))
      (List.finRange I.schemas.length)).sum = locBase I := rfl
  have h2 : (fun a => sizeOf' ((coordList (I.domain a)).map
      fun c => ((Cls.coord a c : ICls I), coordLabs I a))) = locSize I := by
    funext a; rw [sizeOf'_map_const]; rfl
  rw [h1, h2, List.idxOf_finRange, locStart]
  ring

/-! ## The slot classes are classes of the order -/

/-- The labels of a class in the order. -/
def clsLabs (Y : ICls I) : List Lab :=
  if twoBit I Y then bits2 else if isSingleton I Y then [((0 : ZMod 2), (0 : ZMod 2))] else bits1

lemma labs_of_mem_ordCls {p : ICls I × List Lab} (hp : p ∈ ordCls I) : p.2 = clsLabs I p.1 := by
  simp only [ordCls, hubsCls, nonhubsCls, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and] at hp
  rcases hp with ⟨e, (⟨c, -, hp⟩ | ⟨c, -, σ, -, rfl⟩) | (⟨c, -, hp⟩ | ⟨c, -, σ, -, rfl⟩) |
      ⟨σ, -, rfl⟩⟩ | ⟨v, c, -, rfl⟩
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
  · simp only [clsLabs, coordLabs, twoBit, isSingleton]
    split <;> simp_all

/-- Every valid class is a class of the order, with its labels. -/
lemma mem_ordCls_of_valid {Y : ICls I} (hY : ClsValid I Y) : (Y, clsLabs I Y) ∈ ordCls I := by
  have h0 : (Y, ((0 : ZMod 2), (0 : ZMod 2))) ∈ ordL I := (mem_ordL I _).mpr (valid_zero hY)
  rw [ordL_eq_flatMap, List.mem_flatMap] at h0
  obtain ⟨p, hp, hm⟩ := h0
  obtain ⟨m, -, he⟩ := List.mem_map.mp hm
  have h1 : p.1 = Y := (Prod.mk.inj he).1
  have h2 := labs_of_mem_ordCls I hp
  rw [h1] at h2
  have : p = (Y, clsLabs I Y) := Prod.ext h1 h2
  rw [← this]; exact hp

/-- The slot classes of the names of the order are valid. -/
lemma valid_slots {x : VName I} (hx : x ∈ ordL I) {l : Lab} {s : ICls I × ZMod 2}
    (hs : s ∈ slotsOf I x.1 l) : ClsValid I s.1 := by
  obtain ⟨X, lx⟩ := x
  have hv := ((mem_ordL I _).mp hx).1
  cases X with
  | upd e σ c =>
    obtain ⟨hσ, hc, hent⟩ := hv
    simp only [slotsOf, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact valid_trackAt e hc hσ.le
    · exact ⟨hσ, hc, hent⟩
    · exact ⟨hσ, c, hc, hent⟩
  | junc e c =>
    obtain ⟨ht, hc⟩ := hv
    simp only [slotsOf, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact valid_coordU e hc
    · exact valid_coordV e hc
    · exact ⟨ht, hc⟩
  | link e c =>
    simp only [slotsOf, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact valid_trackAt e hv le_rfl
    · exact valid_endCls e hv
  | coord => simp [slotsOf] at hs
  | sum => simp [slotsOf] at hs
  | track => simp [slotsOf] at hs
  | coef => simp [slotsOf] at hs

/-- The labels of a slot class: one name for initialized coordinate classes, else two. -/
def slotLabs (Y : ICls I) : List Lab :=
  if isSingleton I Y then [((0 : ZMod 2), (0 : ZMod 2))] else bits1

/-- **Slot classes.** The class of every slot of a name of the order is a class of the order
with labels `slotLabs`: `[(0,0)]` for coordinate classes of initialized locations, `bits1`
otherwise, so that `posOpt_single` resp. `posOpt_bits1` applies. -/
theorem slot_mem_ordCls {x : VName I} (hx : x ∈ ordL I) {l : Lab} {s : ICls I × ZMod 2}
    (hs : s ∈ slotsOf I x.1 l) : (s.1, slotLabs I s.1) ∈ ordCls I := by
  have h := mem_ordCls_of_valid I (valid_slots I hx hs)
  have hh : isHub I s.1 = false :=
    (hubB_hub I ((hubB_iff_slotsOf I x.1 s.1 l (s.2, 0)).mpr hs)).2
  have ht : twoBit I s.1 = false := by
    cases h' : s.1 <;> simp_all [twoBit, isHub]
  simpa [clsLabs, slotLabs, ht] using h

/-! ## Tracks: the previous entry of the column -/

lemma prevStep_eq_some {c : Coord k ℓ} {σ σ' : ℕ} (h1 : σ' < σ) (h2 : ent σ' c ≠ 0)
    (h3 : ∀ σ'', σ' < σ'' → σ'' < σ → ent σ'' c = 0) : prevStep c σ = some σ' := by
  rcases hp : prevStep c σ with _ | σ₁
  · exact absurd (prevStep_none hp σ' h1) h2
  · obtain ⟨g1, g2, g3⟩ := prevStep_some hp
    rcases lt_trichotomy σ₁ σ' with h | h | h
    · exact absurd (g3 σ' h h1) h2
    · rw [h]
    · exact absurd (h3 σ₁ h g1) g2

lemma prevStep_eq_none {c : Coord k ℓ} {σ : ℕ} (h : ∀ σ' < σ, ent σ' c = 0) :
    prevStep c σ = none := by
  rcases hp : prevStep c σ with _ | σ₁
  · rfl
  · obtain ⟨g1, g2, -⟩ := prevStep_some hp
    exact absurd (h σ₁ g1) g2

lemma pairwise_stepsC (c : Coord k ℓ) : (stepsC c).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

lemma idx_lt_of_lt {L : List ℕ} (hL : L.Pairwise (· < ·)) {a b : ℕ} (ha : a < L.length)
    (hb : b < L.length) (h : L[a] < L[b]) : a < b := by
  by_contra h'
  rcases Nat.lt_or_eq_of_le (not_lt.mp h') with h'' | h''
  · have := List.pairwise_iff_getElem.mp hL b a hb ha h''; omega
  · subst h''; omega

/-- **The track before an entry.** The track class at the step `σ = (stepsC c)[j]` is the
track of the previous entry `j - 1` of the column, or the start class for `j = 0`. -/
theorem trackAt_stepsC (e : Fin I.schemas.length) (c : Coord k ℓ) {j : ℕ}
    (hj : j < (stepsC c).length) :
    trackAt I e c (stepsC c)[j] =
      if h : j = 0 then startCls I e c else .track e ((stepsC c)[j - 1]'(by omega)) c := by
  have hP := pairwise_stepsC c
  have hmem : ∀ σ, σ < numSteps k ℓ → ent σ c ≠ 0 → ∃ i, ∃ hi : i < (stepsC c).length,
      (stepsC c)[i] = σ := fun σ h1 h2 =>
    List.getElem_of_mem ((mem_stepsC).mpr ⟨h1, h2⟩)
  have hN : (stepsC c)[j] < numSteps k ℓ := ((mem_stepsC).mp (List.getElem_mem hj)).1
  split
  · next h0 =>
    subst h0
    unfold trackAt
    rw [prevStep_eq_none fun σ' hσ' => by
      by_contra hne
      obtain ⟨i, hi, rfl⟩ := hmem σ' (by omega) hne
      have := idx_lt_of_lt hP hi hj hσ'
      omega]
  · next h0 =>
    unfold trackAt
    have hj1 : j - 1 < (stepsC c).length := by omega
    rw [prevStep_eq_some (σ' := (stepsC c)[j - 1])
      (List.pairwise_iff_getElem.mp hP _ _ hj1 hj (by omega))
      ((mem_stepsC).mp (List.getElem_mem hj1)).2 (fun σ'' g1 g2 => by
        by_contra hne
        obtain ⟨i, hi, rfl⟩ := hmem σ'' (by omega) hne
        have a1 := idx_lt_of_lt hP hj1 hi g1
        have a2 := idx_lt_of_lt hP hi hj g2
        omega)]

/-- **The track at the end of the strip**: the track of the last entry of the column (or the
start class if the column has no entry). -/
theorem trackAt_numSteps (e : Fin I.schemas.length) (c : Coord k ℓ) :
    trackAt I e c (numSteps k ℓ) =
      if h : stepsC c = [] then startCls I e c else .track e ((stepsC c).getLast h) c := by
  have hP := pairwise_stepsC c
  have hmem : ∀ σ, σ < numSteps k ℓ → ent σ c ≠ 0 → σ ∈ stepsC c := fun σ h1 h2 =>
    (mem_stepsC).mpr ⟨h1, h2⟩
  by_cases h0 : stepsC c = []
  · rw [dif_pos h0]
    unfold trackAt
    rw [prevStep_eq_none fun σ' hσ' => by
      by_contra hne; have := hmem σ' hσ' hne; rw [h0] at this; simp at this]
  · rw [dif_neg h0]
    unfold trackAt
    have hl : (stepsC c).getLast h0 ∈ stepsC c := List.getLast_mem h0
    rw [prevStep_eq_some (σ' := (stepsC c).getLast h0) ((mem_stepsC).mp hl).1
      ((mem_stepsC).mp hl).2 (fun σ'' g1 g2 => by
        by_contra hne
        have h'' := hmem σ'' g2 hne
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h''
        rw [List.getLast_eq_getElem] at g1
        have := idx_lt_of_lt hP (by have := List.length_pos_of_ne_nil h0; omega) hi g1
        omega)]

/-- For `k ≥ 2` every column has an entry (row `c.1`, or row `0` for the last block). -/
theorem stepsC_ne_nil (hk : 2 ≤ k) (c : Coord k ℓ) : stepsC c ≠ [] := by
  set σ : ℕ := if (c.1 : ℕ) < k - 1 then c.1 else 0 with hσdef
  have hσ : σ < k - 1 := by
    simp only [hσdef]; split_ifs <;> omega
  have hM : 0 < k - 1 + ℓ := by omega
  have hent : ent σ c ≠ 0 := by
    unfold ent stepRow
    rw [dif_pos hM]
    have e1 : (⟨σ % (k - 1 + ℓ), Nat.mod_lt _ hM⟩ : Fin (k - 1 + ℓ)) =
        Fin.castAdd ℓ (⟨σ, hσ⟩ : Fin (k - 1)) := by
      ext; simp [Nat.mod_eq_of_lt (show σ < k - 1 + ℓ by omega)]
    rw [e1, finSumFinEquiv_symm_apply_castAdd]
    simp only [checkMatrix, Matrix.of_apply]
    have : (c.1 : ℕ) = σ ∨ (c.1 : ℕ) = k - 1 := by
      simp only [hσdef]; split_ifs with h
      · left; rfl
      · right; have := c.1.isLt; omega
    rw [if_pos this]; exact one_ne_zero
  intro h
  have : σ ∈ stepsC c := (mem_stepsC).mpr ⟨by unfold numSteps; nlinarith, hent⟩
  rw [h] at this; simp at this

/-! ## Order of the sections -/

lemma schBase_add_le (e : Fin I.schemas.length) :
    schBase I e + schSize I e ≤ locBase I := by
  unfold schBase locBase
  have h := List.take_append_drop (e : ℕ) (List.finRange I.schemas.length)
  conv_rhs => rw [← h]
  rw [List.map_append, List.sum_append]
  have hd : List.drop (e : ℕ) (List.finRange I.schemas.length) =
      e :: List.drop ((e : ℕ) + 1) (List.finRange I.schemas.length) := by
    rw [List.drop_eq_getElem_cons (by simp)]; simp
  rw [hd]; simp

end Lax119563Proofs.Compiler
