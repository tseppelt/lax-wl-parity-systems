import Lax119563Proofs.Compiler.PEmitRank

/-!
# Pass `P4` (list level): block ranks by the running count of blocks

For the column `c = D[r]` of a domain `D = coordList (dom I e)` with `c.1 < k - 1`, the rank of
its block row is `c.1` if `blkRows D = k - 1`, and otherwise the number of distinct blocks of
`D[0..r]` minus one, i.e. `dChg k (blocks of D.take (r + 1)) - 1` (`rank_blk_eq`), which the
program keeps in a register (`dChg_append`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma countP_range_all (P : ℕ → Bool) {n m : ℕ} (hm : m ≤ n)
    (h : (List.range n).countP P = n) : (List.range m).countP P = m := by
  have hall := List.countP_eq_length.mp (by rw [List.length_range]; exact h)
  rw [List.countP_eq_length.mpr fun j hj => hall j (List.mem_range.mpr
    (lt_of_lt_of_le (List.mem_range.mp hj) hm)), List.length_range]

/-- **Block-row ranks by the running count of blocks.** -/
theorem rank_blk_eq (e : Fin I.schemas.length) {r : ℕ}
    (hr : r < (coordList (dom I e)).length)
    (hc : ((coordList (dom I e))[r].1 : ℕ) + 1 < k) :
    (rowsR I e).idxOf ((coordList (dom I e))[r].1 : ℕ) =
      if blkRows (coordList (dom I e)) = k - 1 then ((coordList (dom I e))[r].1 : ℕ)
      else dChg k (((coordList (dom I e)).take (r + 1)).map fun c => (c.1 : ℕ)) - 1 := by
  set D := coordList (dom I e) with hD
  set c := D[r] with hcdef
  have hcD : c ∈ D := List.getElem_mem hr
  have hPc : PA I e (c.1 : ℕ) = true := by
    simp only [PA, decide_eq_true_eq]; exact ⟨c, hcD, Or.inl rfl⟩
  rw [rank_blk I e (by omega) hPc]
  split_ifs with hB
  · have h1 : (List.range (k - 1)).countP (PA I e) = blkRows D := by
      rw [blkRows]; exact List.countP_congr (fun j _ => by simp [PA, hD])
    exact countP_range_all _ (show (c.1 : ℕ) ≤ k - 1 by omega) (h1.trans hB)
  · -- no coordinate of block `k - 1`
    have hno : ∀ c' ∈ D, (c'.1 : ℕ) ≠ k - 1 := by
      intro c' hc' h'
      apply hB
      rw [blkRows, List.countP_eq_length.mpr, List.length_range]
      intro j _
      simp only [decide_eq_true_eq]; exact ⟨c', hc', Or.inr h'⟩
    have hPA : ∀ j, PA I e j = true ↔ ∃ c' ∈ D, (c'.1 : ℕ) = j := by
      intro j
      simp only [PA, decide_eq_true_eq, ← hD]
      constructor
      · rintro ⟨c', hc', h | h⟩
        · exact ⟨c', hc', h⟩
        · exact absurd h (hno c' hc')
      · rintro ⟨c', hc', h⟩; exact ⟨c', hc', Or.inl h⟩
    set l := (D.take (r + 1)).map fun c => (c.1 : ℕ) with hl
    have hsorted : l.Pairwise (· ≤ ·) := by
      have := pairwise_blocks (dom I e)
      rw [← hD] at this
      exact this.sublist ((List.take_sublist _ _).map _)
    have hkl : k ∉ l := by
      simp only [hl, List.mem_map, not_exists, not_and]
      intro c' _ h'; have := c'.1.2; omega
    rw [dChg_eq k l hsorted (Or.inr hkl), Finset.erase_eq_of_notMem (by simpa using hkl)]
    -- the blocks of `l` are the blocks `< c.1` of `D`, and `c.1`
    have hpw : ∀ i j (hi : i < D.length) (hj : j < D.length), i < j →
        (D[i].1 : ℕ) ≤ D[j].1 := by
      intro i j hi hj hij
      have := List.pairwise_iff_getElem.mp (pairwise_blocks (dom I e)) i j (by simpa [hD] using hi)
        (by simpa [hD] using hj) hij
      simpa [hD] using this
    have hmem : ∀ x, x ∈ l ↔ x = (c.1 : ℕ) ∨ (x < c.1 ∧ PA I e x = true) := by
      intro x
      rw [hPA]
      constructor
      · intro hx
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hx
        obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.mp hc'
        have hi1 : i ≤ r := by omega
        have hiD : i < D.length := by omega
        rcases Nat.lt_or_eq_of_le hi1 with h | h
        · have := hpw i r hiD hr h
          rw [← hcdef] at this
          rcases Nat.lt_or_eq_of_le this with h' | h'
          · exact Or.inr ⟨h', D[i], List.getElem_mem _, rfl⟩
          · exact Or.inl h'
        · subst h; exact Or.inl rfl
      · rintro (rfl | ⟨hx, c', hc', rfl⟩)
        · exact List.mem_map.mpr ⟨c, List.mem_take_iff_getElem.mpr ⟨r, by omega, rfl⟩, rfl⟩
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc'
          have hir : i ≤ r := by
            by_contra h
            have := hpw r i hr hi (by omega)
            rw [← hcdef] at this
            omega
          exact List.mem_map.mpr ⟨D[i], List.mem_take_iff_getElem.mpr ⟨i, by omega, rfl⟩, rfl⟩
    have hfs : l.toFinset = insert (c.1 : ℕ) ((List.range (c.1 : ℕ)).filter (PA I e)).toFinset := by
      ext x
      simp only [List.mem_toFinset, Finset.mem_insert, List.mem_filter, List.mem_range, hmem]
    rw [hfs, Finset.card_insert_of_notMem (by simp), List.toFinset_card_of_nodup
      ((List.nodup_range).filter _), ← List.countP_eq_length_filter]
    omega

end Lax119563Proofs.Compiler
