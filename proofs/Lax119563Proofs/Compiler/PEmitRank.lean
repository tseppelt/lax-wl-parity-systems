import Lax119563Proofs.Compiler.PEmitSteps

/-!
# Pass `P4` (list level): the ranks of the rows of a column

The coefficient index of an entry needs `rank j = idxOf j (rowsR I e)` for the rows `j` of the
column. With `bd = blockDescription c.2` (bits of the column) and `os = orsL D` (the OR of the
bits over the domain, from the `P2` record):
* checksum rows (`chkRanks_eq`): the ranks of the rows `k - 1 + t` (`bd[t] = 1`) are
  `chkRk os bd (blkRows D)`, computed by one pass over the bits (`blkRows + Σ_{t'<t} os[t']`);
* block rows (`rank_blk`): `rank j = (range j).countP PA` (`PA j`: some coordinate of the
  domain has block `j` or `k - 1`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Generic -/

/-- The index of an element of a filtered range is the count below it. -/
lemma idxOf_filter_range (P : ℕ → Bool) {j : ℕ} (hj : P j = true) : ∀ n, j < n →
    ((List.range n).filter P).idxOf j = (List.range j).countP P
  | 0, h => absurd h (by omega)
  | n + 1, h => by
    rw [List.range_succ, List.filter_append]
    by_cases hjn : j < n
    · rw [List.idxOf_append_of_mem (List.mem_filter.mpr ⟨List.mem_range.mpr hjn, hj⟩)]
      exact idxOf_filter_range P hj n hjn
    · have : j = n := by omega
      subst this
      rw [List.idxOf_append_of_notMem (by simp), List.countP_eq_length_filter]
      simp [hj]

/-- The checksum ranks along the bits: `bs` the bits of the column, `os` the OR bits. -/
def chkRk : List ℕ → List ℕ → ℕ → List ℕ
  | o :: os, b :: bs, p => (if b = 1 then [p] else []) ++ chkRk os bs (p + o)
  | _, _, _ => []

lemma chkRk_eq : ∀ (os bs : List ℕ) (p : ℕ), os.length = bs.length →
    ((List.range bs.length).filter (fun t => decide (bs.getD t 0 = 1))).map
      (fun t => p + (os.take t).sum) = chkRk os bs p
  | [], [], _, _ => rfl
  | o :: os, b :: bs, p, h => by
    have ih := chkRk_eq os bs (p + o) (by simpa using h)
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map, chkRk, ← ih]
    have e2 : (List.range bs.length).filter ((fun t => decide ((b :: bs).getD t 0 = 1)) ∘
        Nat.succ) = (List.range bs.length).filter (fun t => decide (bs.getD t 0 = 1)) :=
      List.filter_congr fun t _ => by simp
    rw [e2]
    by_cases hb : b = 1 <;> simp [hb, List.map_map, Function.comp_def, add_assoc]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## The rows of the domain -/

lemma range_split' : List.range (k - 1 + ℓ) =
    List.range (k - 1) ++ (List.range ℓ).map fun t => k - 1 + t := List.range_add ..

open Classical in
/-- The block-row predicate of a domain. -/
noncomputable def PA (e : Fin I.schemas.length) (j : ℕ) : Bool :=
  decide (∃ c ∈ coordList (dom I e), (c.1 : ℕ) = j ∨ (c.1 : ℕ) = k - 1)

open Classical in
/-- The checksum-row predicate of a domain. -/
noncomputable def PB (e : Fin I.schemas.length) (t : ℕ) : Bool :=
  decide (∃ t' : Fin ℓ, (t' : ℕ) = t ∧ ∃ c ∈ coordList (dom I e), c.2 t' ≠ 0)

open Classical in
lemma rowsR_eq (e : Fin I.schemas.length) : rowsR I e =
    (List.range (k - 1)).filter (PA I e) ++ ((List.range ℓ).filter (PB I e)).map
      fun t => k - 1 + t := by
  rw [rowsR, range_split', List.filter_append, List.filter_map]
  congr 1
  · refine List.filter_congr fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [PA, rowNZ, mem_coordList, decide_eq_decide]
    constructor
    · rintro ⟨c, hc, ⟨-, h⟩ | ⟨h, -⟩⟩
      · exact ⟨c, hc, h⟩
      · omega
    · rintro ⟨c, hc, h⟩; exact ⟨c, hc, Or.inl ⟨hj, h⟩⟩
  · congr 1
    refine List.filter_congr fun t ht => ?_
    simp only [Function.comp, PB, rowNZ, mem_coordList, decide_eq_decide]
    constructor
    · rintro ⟨c, hc, ⟨h, -⟩ | ⟨-, t', ht', h⟩⟩
      · omega
      · exact ⟨t', by omega, c, hc, h⟩
    · rintro ⟨t', ht', c, hc, h⟩; exact ⟨c, hc, Or.inr ⟨by omega, t', by omega, h⟩⟩

lemma length_filter_PA (e : Fin I.schemas.length) :
    ((List.range (k - 1)).filter (PA I e)).length = blkRows (coordList (dom I e)) := by
  rw [← List.countP_eq_length_filter, blkRows]; rfl

/-- **Block-row ranks.** -/
lemma rank_blk (e : Fin I.schemas.length) {j : ℕ} (hj : j < k - 1) (hP : PA I e j = true) :
    (rowsR I e).idxOf j = (List.range j).countP (PA I e) := by
  rw [rowsR_eq, List.idxOf_append_of_mem (List.mem_filter.mpr ⟨List.mem_range.mpr hj, hP⟩)]
  exact idxOf_filter_range _ hP _ hj

lemma orsL_getD (cs : List (Coord k ℓ)) (t : ℕ) (ht : t < ℓ) :
    (orsL cs).getD t 0 = if ∃ c ∈ cs, c.2 ⟨t, ht⟩ ≠ 0 then 1 else 0 := by
  simp [orsL, List.getD_eq_getElem?_getD, ht]

lemma countP_PB (e : Fin I.schemas.length) : ∀ t, t ≤ ℓ →
    (List.range t).countP (PB I e) = ((orsL (coordList (dom I e))).take t).sum
  | 0, _ => by simp
  | t + 1, h => by
    rw [List.range_succ, List.countP_append, countP_PB e t (by omega)]
    have hl : t < (orsL (coordList (dom I e))).length := by rw [length_orsL]; omega
    rw [List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some, List.sum_append,
      List.sum_singleton]
    congr 1
    have e1 := orsL_getD (coordList (dom I e)) t (by omega)
    rw [List.getD_eq_getElem _ _ hl] at e1
    rw [e1]
    by_cases h' : ∃ c ∈ coordList (dom I e), c.2 ⟨t, by omega⟩ ≠ 0
    · have hP : PB I e t = true := decide_eq_true ⟨⟨t, by omega⟩, rfl, h'⟩
      rw [if_pos h']; simp [List.countP_singleton, hP]
    · have hP : PB I e t = false := by
        refine decide_eq_false ?_
        rintro ⟨t', ht', c, hc, h''⟩
        have : t' = ⟨t, by omega⟩ := Fin.ext ht'
        rw [this] at h''
        exact h' ⟨c, hc, h''⟩
      rw [if_neg h']; simp [List.countP_singleton, hP]

/-- **Checksum-row ranks.** -/
lemma rank_chk (e : Fin I.schemas.length) {t : ℕ} (ht : t < ℓ) (hP : PB I e t = true) :
    (rowsR I e).idxOf (k - 1 + t) =
      blkRows (coordList (dom I e)) + ((orsL (coordList (dom I e))).take t).sum := by
  rw [rowsR_eq, List.idxOf_append_of_notMem (by simp), length_filter_PA]
  congr 1
  have hinj : Function.Injective fun t => k - 1 + t := fun a b h => by simpa using h
  rw [idxOf_map_inj hinj, idxOf_filter_range _ hP _ ht,
    countP_PB I e t ht.le]

/-! ## The rows of a column -/

lemma filter_range_eq_single (a : ℕ) : ∀ n,
    (List.range n).filter (fun j => decide (j = a)) = if a < n then [a] else []
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, filter_range_eq_single a n]
    by_cases h : a = n
    · subst h; simp
    · have : ¬ a < n + 1 ∨ a < n := by omega
      rcases this with h1 | h1
      · rw [if_neg (by omega), if_neg h1]; simp [Ne.symm h]
      · rw [if_pos h1, if_pos (by omega)]; simp [Ne.symm h]

lemma length_blockDescription' (b : BlockCoord ℓ) : (blockDescription b).length = ℓ := by
  simp [blockDescription]

/-- The checksum rows of a column, as bit indices. -/
def chkT (c : Coord k ℓ) : List ℕ :=
  (List.range ℓ).filter fun t => decide ((blockDescription c.2).getD t 0 = 1)

lemma bd_getD (c : Coord k ℓ) {t : ℕ} (ht : t < ℓ) :
    (blockDescription c.2).getD t 0 = (c.2 ⟨t, ht⟩).val := by
  simp [blockDescription, List.getD_eq_getElem?_getD, ht]

/-- **The rows of a column**: the block part, then the checksum rows. -/
lemma rowsL_eq (c : Coord k ℓ) : rowsL c =
    (if (c.1 : ℕ) + 1 < k then [(c.1 : ℕ)] else List.range (k - 1)) ++
      (chkT c).map fun t => k - 1 + t := by
  rw [rowsL, range_split', List.filter_append, List.filter_map]
  have hc := c.1.2
  congr 1
  · split_ifs with h
    · rw [show [(c.1 : ℕ)] = (List.range (k - 1)).filter (fun j => decide (j = (c.1 : ℕ))) by
        rw [filter_range_eq_single, if_pos (by omega)]]
      refine List.filter_congr fun j hj => ?_
      rw [List.mem_range] at hj
      simp only [rowNZ, decide_eq_decide]
      constructor
      · rintro (⟨-, h' | h'⟩ | ⟨h', -⟩) <;> omega
      · intro h'; exact Or.inl ⟨hj, Or.inl h'.symm⟩
    · rw [List.filter_eq_self.mpr]
      intro j hj
      rw [List.mem_range] at hj
      simp only [rowNZ, decide_eq_true_eq]
      exact Or.inl ⟨hj, Or.inr (by omega)⟩
  · congr 1
    unfold chkT
    refine List.filter_congr fun t ht => ?_
    rw [List.mem_range] at ht
    simp only [Function.comp, rowNZ, decide_eq_decide, bd_getD c ht]
    have hv := ZMod.val_lt (c.2 ⟨t, ht⟩)
    constructor
    · rintro (⟨h, -⟩ | ⟨-, t', ht', h⟩)
      · omega
      · have : t' = ⟨t, ht⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
        subst this
        rcases Lax119563Proofs.Reduction.zmod2_cases (c.2 ⟨t, ht⟩) with h0 | h0
        · exact absurd h0 h
        · rw [h0]; rfl
    · intro h
      refine Or.inr ⟨by omega, ⟨t, ht⟩, by simp, fun h0 => ?_⟩
      rw [h0] at h; simp at h

/-- **The checksum ranks of a column** by the bit pass. -/
lemma chkRanks_eq (e : Fin I.schemas.length) {c : Coord k ℓ} (hc : c ∈ dom I e) :
    ((chkT c).map fun t => k - 1 + t).map (rowsR I e).idxOf =
      chkRk (orsL (coordList (dom I e))) (blockDescription c.2)
        (blkRows (coordList (dom I e))) := by
  rw [← chkRk_eq _ _ _ (by rw [length_orsL, length_blockDescription']), List.map_map]
  unfold chkT
  rw [length_blockDescription']
  refine List.map_congr_left fun t ht => ?_
  obtain ⟨ht1, ht2⟩ := List.mem_filter.mp ht
  rw [List.mem_range] at ht1
  simp only [decide_eq_true_eq, bd_getD c ht1] at ht2
  refine rank_chk I e ht1 ?_
  simp only [PB, decide_eq_true_eq]
  refine ⟨⟨t, ht1⟩, rfl, c, mem_coordList.mpr hc, fun h0 => ?_⟩
  rw [h0] at ht2; simp at ht2

end Lax119563Proofs.Compiler
