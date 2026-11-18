import Lax119563Proofs.Compiler.PRec

/-!
# Sizes of the schema sections (list level, for pass `P2`)

With `M = k - 1 + ℓ` check rows, row `j < k - 1` is nonzero at `c` iff `c.1 = j` or
`c.1 = k - 1`, and row `k - 1 + t` iff `c.2 t ≠ 0` (`ent_ne_zero_iff`). Hence

* `(stepsC c).length = (k + 1) · rowsC c` with `rowsC c = [c.1 + 1 < k ? 1 : k - 1] + popc c.2`
  (`length_stepsC`), so `nEnt I e = (k + 1) Σ_c rowsC c` (`nEnt_eq`);
* `(coefSteps I e).length = (k + 1) (blkRows + orPop)` (`length_coefSteps`), where the
  block rows are `k - 1` if some coordinate lies in block `k - 1` and the number of distinct
  blocks otherwise (`blkRows_eq`), and `orPop` counts the bits set in some coordinate;
* `schSize I e = |D| (tern ? 8 : 2) + 6 nEnt + 2 |coefSteps|` (`schSize_eq'`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ}

/-! ## Rows of the check matrix -/

/-- Row `j` of the check matrix is nonzero at `c`. -/
abbrev rowNZ (j : ℕ) (c : Coord k ℓ) : Prop :=
  (j < k - 1 ∧ ((c.1 : ℕ) = j ∨ (c.1 : ℕ) = k - 1)) ∨
    (k - 1 ≤ j ∧ ∃ t : Fin ℓ, (t : ℕ) = j - (k - 1) ∧ c.2 t ≠ 0)

lemma zmod2_ite_ne_zero (P : Prop) [Decidable P] :
    ((if P then 1 else 0 : ZMod 2) ≠ 0) ↔ P := by
  split_ifs with h <;> simp [h]

lemma ent_ne_zero_iff (σ : ℕ) (c : Coord k ℓ) :
    ent σ c ≠ 0 ↔ rowNZ (σ % (k - 1 + ℓ)) c := by
  unfold ent
  by_cases h : 0 < k - 1 + ℓ
  · rw [dif_pos h]
    have hjM : σ % (k - 1 + ℓ) < k - 1 + ℓ := Nat.mod_lt _ h
    unfold stepRow
    by_cases hj1 : σ % (k - 1 + ℓ) < k - 1
    · rw [show (⟨σ % (k - 1 + ℓ), Nat.mod_lt _ h⟩ : Fin (k - 1 + ℓ)) =
          Fin.castAdd ℓ ⟨σ % (k - 1 + ℓ), hj1⟩ from rfl, finSumFinEquiv_symm_apply_castAdd]
      simp only [checkMatrix, Matrix.of_apply, zmod2_ite_ne_zero, rowNZ, hj1, true_and]
      constructor
      · intro h'; exact Or.inl h'
      · rintro (h' | ⟨h', -⟩)
        · exact h'
        · omega
    · rw [show (⟨σ % (k - 1 + ℓ), Nat.mod_lt _ h⟩ : Fin (k - 1 + ℓ)) =
          Fin.natAdd (k - 1) ⟨σ % (k - 1 + ℓ) - (k - 1), by omega⟩ from Fin.ext (by simp; omega),
        finSumFinEquiv_symm_apply_natAdd]
      simp only [checkMatrix, Matrix.of_apply, rowNZ, hj1, false_and, false_or]
      constructor
      · intro h'; exact ⟨by omega, _, rfl, h'⟩
      · rintro ⟨-, t, ht, h'⟩
        have : t = ⟨σ % (k - 1 + ℓ) - (k - 1), by omega⟩ := Fin.ext ht
        rw [← this]; exact h'
  · rw [dif_neg h]
    have hk : k - 1 = 0 := by omega
    have hl : ℓ = 0 := by omega
    subst hl
    constructor
    · intro h'; exact absurd rfl h'
    · rintro (⟨h', -⟩ | ⟨-, t, -⟩)
      · omega
      · exact t.elim0

/-- Counting steps by their row. -/
lemma countP_range_mod (M : ℕ) (P : ℕ → Bool) : ∀ n : ℕ,
    (List.range (n * M)).countP (fun σ => P (σ % M)) = n * (List.range M).countP P
  | 0 => by simp
  | n + 1 => by
    rw [show (n + 1) * M = n * M + M by ring, List.range_add, List.countP_append,
      countP_range_mod M P n, List.countP_map]
    have : (List.range M).countP ((fun σ => P (σ % M)) ∘ (fun j => n * M + j)) =
        (List.range M).countP P := by
      refine List.countP_congr fun j hj => ?_
      rw [List.mem_range] at hj
      simp only [Function.comp_apply, Nat.mul_add_mod_of_lt hj]
    rw [this]; ring

/-- The number of set bits of a block coordinate. -/
def popc (b : BlockCoord ℓ) : ℕ := (List.finRange ℓ).countP fun t => b t ≠ 0

lemma sum_blockDescription (b : BlockCoord ℓ) : (blockDescription b).sum = popc b := by
  unfold blockDescription popc
  induction (List.finRange ℓ) with
  | nil => rfl
  | cons t ts ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    rcases zmod2_cases (b t) with h | h <;> simp [h, show (1 : ZMod 2).val = 1 from rfl]; ring

/-- The number of nonzero rows of column `c`. -/
def rowsC (c : Coord k ℓ) : ℕ := (if (c.1 : ℕ) + 1 < k then 1 else k - 1) + popc c.2

lemma range_split (k ℓ : ℕ) :
    List.range (k - 1 + ℓ) = List.range (k - 1) ++ (List.range ℓ).map fun t => k - 1 + t := by
  rw [List.range_add]

lemma countP_range_eq (n a : ℕ) : (List.range n).countP (fun j => decide (a = j)) =
    if a < n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases h : a = n
    · subst h; simp
    · have : ¬ a < n + 1 ∨ a < n := by omega
      rcases this with h1 | h1
      · rw [if_neg (by omega), if_neg h1]; simp [h]
      · rw [if_pos h1, if_pos (by omega)]; simp [h]

lemma countP_finRange (ℓ : ℕ) (p : Fin ℓ → Prop) [DecidablePred p] :
    (List.range ℓ).countP (fun t => decide (∃ t' : Fin ℓ, (t' : ℕ) = t ∧ p t')) =
      (List.finRange ℓ).countP fun t => decide (p t) := by
  rw [← map_val_finRange, List.countP_map]
  refine List.countP_congr fun t _ => ?_
  simp only [Function.comp_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨t', ht, hp⟩; rw [← Fin.ext ht]; exact hp
  · intro hp; exact ⟨t, rfl, hp⟩

lemma countP_rowNZ (c : Coord k ℓ) :
    (List.range (k - 1 + ℓ)).countP (fun j => decide (rowNZ j c)) = rowsC c := by
  rw [range_split, List.countP_append, List.countP_map]
  have h1 : (List.range (k - 1)).countP (fun j => decide (rowNZ j c)) =
      if (c.1 : ℕ) + 1 < k then 1 else k - 1 := by
    have hc := c.1.2
    split_ifs with hk
    · have e := countP_range_eq (k - 1) (c.1 : ℕ)
      rw [if_pos (show (c.1 : ℕ) < k - 1 by omega)] at e
      refine Eq.trans (List.countP_congr fun j hj => ?_) e
      rw [List.mem_range] at hj
      simp only [rowNZ, decide_eq_true_eq]
      constructor
      · rintro (⟨-, h | h⟩ | ⟨h, -⟩)
        · exact h
        · omega
        · omega
      · intro h; exact Or.inl ⟨hj, Or.inl h⟩
    · rw [List.countP_eq_length.mpr, List.length_range]
      intro j hj
      rw [List.mem_range] at hj
      simp only [rowNZ, decide_eq_true_eq]
      left; exact ⟨hj, Or.inr (by omega)⟩
  have h2 : (List.range ℓ).countP ((fun j => decide (rowNZ j c)) ∘ fun t => k - 1 + t) =
      popc c.2 := by
    rw [popc, ← countP_finRange ℓ (fun t => c.2 t ≠ 0)]
    refine List.countP_congr fun t _ => ?_
    simp only [Function.comp_apply, rowNZ, decide_eq_true_eq]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, t', ht, h⟩)
      · omega
      · exact ⟨t', by omega, h⟩
    · rintro ⟨t', ht, h⟩
      exact Or.inr ⟨by omega, t', by omega, h⟩
  rw [h1, h2, rowsC]

/-- **The number of steps of a column.** -/
lemma length_stepsC (c : Coord k ℓ) : (stepsC c).length = (k + 1) * rowsC c := by
  rw [stepsC, ← List.countP_eq_length_filter, numSteps, ← countP_rowNZ c,
    ← countP_range_mod (k - 1 + ℓ) (fun j => decide (rowNZ j c)) (k + 1)]
  refine List.countP_congr fun σ _ => ?_
  simp only [ne_eq, decide_eq_true_eq, ← ent_ne_zero_iff]

/-! ## Schema sizes -/

variable (I : ImplicitParitySystem k ℓ)

/-- The sum of the row counts of the columns. -/
def rowsSum (cs : List (Coord k ℓ)) : ℕ := (cs.map rowsC).sum

lemma nEnt_eq (e : Fin I.schemas.length) : nEnt I e = (k + 1) * rowsSum (coordList (dom I e)) := by
  rw [nEnt, rowsSum, ← List.sum_map_mul_left]
  congr 1
  exact List.map_congr_left fun c _ => length_stepsC c

/-- The block rows that are nonzero on a list of coordinates. -/
def blkRows (cs : List (Coord k ℓ)) : ℕ :=
  (List.range (k - 1)).countP fun j => decide (∃ c ∈ cs, (c.1 : ℕ) = j ∨ (c.1 : ℕ) = k - 1)

/-- The bits set in some coordinate of a list. -/
def orPop (cs : List (Coord k ℓ)) : ℕ :=
  (List.finRange ℓ).countP fun t => decide (∃ c ∈ cs, c.2 t ≠ 0)

lemma countP_rowNZ_ex (cs : List (Coord k ℓ)) :
    (List.range (k - 1 + ℓ)).countP (fun j => decide (∃ c ∈ cs, rowNZ j c)) =
      blkRows cs + orPop cs := by
  rw [range_split, List.countP_append, List.countP_map]
  congr 1
  · refine List.countP_congr fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [rowNZ, decide_eq_true_eq, hj, true_and, not_le.mpr hj, false_and, or_false]
  · rw [orPop, ← countP_finRange ℓ (fun t => ∃ c ∈ cs, c.2 t ≠ 0)]
    refine List.countP_congr fun t _ => ?_
    simp only [Function.comp_apply, rowNZ, decide_eq_true_eq]
    constructor
    · rintro ⟨c, hc, ⟨h, -⟩ | ⟨-, t', ht, h⟩⟩
      · omega
      · exact ⟨t', by omega, c, hc, h⟩
    · rintro ⟨t', ht, c, hc, h⟩
      exact ⟨c, hc, Or.inr ⟨by omega, t', by omega, h⟩⟩

open Classical in
/-- **The number of coefficient steps.** -/
lemma length_coefSteps (e : Fin I.schemas.length) :
    (coefSteps I e).length = (k + 1) * (blkRows (coordList (dom I e)) +
      orPop (coordList (dom I e))) := by
  rw [coefSteps, ← List.countP_eq_length_filter, numSteps, ← countP_rowNZ_ex,
    ← countP_range_mod (k - 1 + ℓ) _ (k + 1)]
  refine List.countP_congr fun σ _ => ?_
  simp only [decide_eq_true_eq, ← ent_ne_zero_iff, mem_coordList]

lemma schSize_eq' (e : Fin I.schemas.length) :
    schSize I e = (coordList (dom I e)).length * (if Matrix.isTern (sch I e) then 8 else 2) +
      6 * nEnt I e + 2 * (coefSteps I e).length := by
  rw [schSize_eq, hubSize, sumSize, colW]
  split_ifs <;> ring

/-! ## The distinct blocks of a sorted list -/

/-- The number of changes of value along a list, starting from `p`. -/
def dChg : ℕ → List ℕ → ℕ
  | _, [] => 0
  | p, i :: is => (if i = p then 0 else 1) + dChg i is

lemma dChg_eq : ∀ (p : ℕ) (l : List ℕ), l.Pairwise (· ≤ ·) → ((∀ x ∈ l, p ≤ x) ∨ p ∉ l) →
    dChg p l = (l.toFinset.erase p).card
  | _, [], _, _ => rfl
  | p, i :: is, hs, hp => by
    rw [List.pairwise_cons] at hs
    rw [dChg, dChg_eq i is hs.2 (Or.inl hs.1), List.toFinset_cons]
    by_cases hip : i = p
    · subst hip; rw [if_pos rfl, Finset.erase_insert_eq_erase]; ring
    · have hpn : p ∉ insert i is.toFinset := by
        rw [Finset.mem_insert, List.mem_toFinset, not_or]
        refine ⟨Ne.symm hip, fun h => ?_⟩
        rcases hp with hp | hp
        · have h1 := hp i List.mem_cons_self
          have h2 := hs.1 p h
          omega
        · exact hp (List.mem_cons_of_mem _ h)
      rw [if_neg hip, Finset.erase_eq_of_notMem hpn]
      by_cases hi : i ∈ is.toFinset
      · rw [Finset.insert_eq_of_mem hi, ← Finset.card_erase_add_one hi]; ring
      · rw [Finset.card_insert_of_notMem hi, Finset.erase_eq_of_notMem hi]; ring

/-- The blocks of `coordList D` are nondecreasing. -/
lemma pairwise_blocks (D : Finset (Coord k ℓ)) :
    ((coordList D).map fun c => (c.1 : ℕ)).Pairwise (· ≤ ·) := by
  have hpw : ((coordList D).map coordNum).Pairwise (· < ·) :=
    pairwise_map_coordNum_allCoords.sublist ((List.filter_sublist).map _)
  rw [List.pairwise_map] at hpw ⊢
  refine hpw.imp fun {a b} h => ?_
  rw [← coordNum_div a, ← coordNum_div b]
  exact Nat.div_le_div_right h.le

/-- **The block rows** by the scan: `k - 1` if block `k - 1` occurs, else the number of
changes of the block along the list (from the start value `k`). -/
lemma blkRows_eq (D : Finset (Coord k ℓ)) :
    blkRows (coordList D) = if ∃ c ∈ coordList D, ¬ (c.1 : ℕ) + 1 < k then k - 1 else
      dChg k ((coordList D).map fun c => (c.1 : ℕ)) := by
  set cs := coordList D
  split_ifs with h
  · obtain ⟨c, hc, hl⟩ := h
    rw [blkRows, List.countP_eq_length.mpr, List.length_range]
    intro j _
    simp only [decide_eq_true_eq]
    exact ⟨c, hc, Or.inr (by have := c.1.2; omega)⟩
  · push_neg at h
    rw [dChg_eq k _ (pairwise_blocks D) (Or.inr (by
      simp only [List.mem_map, not_exists, not_and]
      intro c _ hck; have := c.1.2; omega))]
    have hnk : k ∉ (cs.map fun c => (c.1 : ℕ)).toFinset := by
      simp only [List.mem_toFinset, List.mem_map, not_exists, not_and]
      intro c _ hck; have := c.1.2; omega
    rw [Finset.erase_eq_of_notMem hnk, blkRows, List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
    congr 1
    ext j
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq,
      List.mem_map]
    constructor
    · rintro ⟨-, c, hc, hj | hj⟩
      · exact ⟨c, hc, hj⟩
      · have := h c hc; omega
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by have := h c hc; omega, c, hc, Or.inl rfl⟩

/-! ## The OR of the block coordinates -/

/-- The OR of the bits of a list of coordinates. -/
def orsL (cs : List (Coord k ℓ)) : List ℕ :=
  (List.finRange ℓ).map fun t => if ∃ c ∈ cs, c.2 t ≠ 0 then 1 else 0

/-- Bitwise or of two bits. -/
def bor (a b : ℕ) : ℕ := if 0 < a + b then 1 else 0

lemma orsL_nil : orsL ([] : List (Coord k ℓ)) = List.replicate ℓ 0 := by
  simp [orsL, List.map_const']

lemma length_orsL (cs : List (Coord k ℓ)) : (orsL cs).length = ℓ := by simp [orsL]

lemma orsL_append (cs : List (Coord k ℓ)) (c : Coord k ℓ) :
    orsL (cs ++ [c]) = List.zipWith bor (orsL cs) (blockDescription c.2) := by
  unfold orsL blockDescription
  rw [List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun t _ => ?_
  have hv := ZMod.val_lt (c.2 t)
  simp only [List.mem_append, List.mem_singleton, bor]
  by_cases h : ∃ c' ∈ cs, c'.2 t ≠ 0
  · obtain ⟨c', hc', h'⟩ := h
    have h1 : ∃ c'' : Coord k ℓ, (c'' ∈ cs ∨ c'' = c) ∧ c''.2 t ≠ 0 := ⟨c', Or.inl hc', h'⟩
    have h2 : ∃ c'' ∈ cs, c''.2 t ≠ 0 := ⟨c', hc', h'⟩
    rw [if_pos h1, if_pos h2, if_pos (by omega)]
  · rw [if_neg h]
    by_cases hc : c.2 t = 0
    · rw [if_neg, if_neg]
      · rw [hc]; simp
      · rintro ⟨c', hc' | rfl, h'⟩
        · exact h ⟨c', hc', h'⟩
        · exact h' hc
    · have : (c.2 t).val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
      rw [if_pos ⟨c, Or.inr rfl, hc⟩, if_pos (by omega)]

lemma sum_orsL (cs : List (Coord k ℓ)) : (orsL cs).sum = orPop cs := by
  unfold orsL orPop
  induction (List.finRange ℓ) with
  | nil => rfl
  | cons t ts ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : ∃ c ∈ cs, c.2 t ≠ 0 <;> simp only [h, if_true, if_false] <;> simp <;> ring

end Lax119563Proofs.Compiler
