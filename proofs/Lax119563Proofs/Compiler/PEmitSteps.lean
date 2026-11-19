import Lax119563Proofs.Compiler.PEmitHub
import Lax119563Proofs.Compiler.PSchSize

/-!
# Pass `P4` (list level): the entries of a column and their coefficient index

With `M = k - 1 + ℓ`, the steps of a column are `q M + j` for `q ≤ k` and the nonzero rows
`j ∈ rowsL c` (increasing), q-major (`stepsC_eq`); the coefficient steps likewise with the rows
`rowsR` nonzero on the domain (`coefSteps_eq`), so the coefficient index of the step `q M + j`
is `q |rowsR| + rank j` (`idxOf_coefSteps`), `rank j = idxOf j (rowsR)`. The ranks
(`rank_blk`, `rank_chk`): a block row `j` has rank `j` if `blkRows = k - 1`, else the number
of distinct blocks up to the column minus one; a checksum row `k - 1 + t` has rank
`blkRows + Σ_{t' < t} or_{t'}`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Generic: ranges in blocks -/

lemma range_mul_eq (M : ℕ) : ∀ n : ℕ,
    List.range (n * M) = (List.range n).flatMap fun q => (List.range M).map fun j => q * M + j
  | 0 => by simp
  | n + 1 => by
    rw [show (n + 1) * M = n * M + M by ring, List.range_add, range_mul_eq M n, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]

lemma filter_range_mul (M n : ℕ) (P : ℕ → Bool) :
    (List.range (n * M)).filter (fun σ => P (σ % M)) =
      (List.range n).flatMap fun q => ((List.range M).filter P).map fun j => q * M + j := by
  rw [range_mul_eq, List.filter_flatMap]
  refine List.flatMap_congr fun q _ => ?_
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun j hj => ?_
  rw [List.mem_range] at hj
  simp [Function.comp, Nat.mul_add_mod_of_lt hj]

lemma idxOf_map_inj {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → β}
    (hf : Function.Injective f) (a : α) : ∀ L : List α, (L.map f).idxOf (f a) = L.idxOf a
  | [] => rfl
  | b :: L => by
    simp only [List.map_cons, List.idxOf_cons, idxOf_map_inj hf a L]
    by_cases h : b = a
    · subst h; simp
    · have : f b ≠ f a := fun h' => h (hf h')
      rw [beq_false_of_ne this, beq_false_of_ne h]

lemma idxOf_blocks (M : ℕ) (L : List ℕ) (hL : ∀ j ∈ L, j < M) {j : ℕ} (hj : j ∈ L) :
    ∀ (n q : ℕ), q < n →
      ((List.range n).flatMap fun q' => L.map fun j' => q' * M + j').idxOf (q * M + j) =
        q * L.length + L.idxOf j
  | 0, _, h => absurd h (by omega)
  | n + 1, q, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hjM := hL j hj
    by_cases hq : q < n
    · rw [List.idxOf_append_of_mem]
      · exact idxOf_blocks M L hL hj n q hq
      · exact List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, List.mem_map.mpr ⟨j, hj, rfl⟩⟩
    · have hqn : q = n := by omega
      subst hqn
      rw [List.idxOf_append_of_notMem]
      · rw [List.length_flatMap]
        simp only [List.length_map, List.map_const', List.sum_replicate, List.length_range,
          smul_eq_mul]
        congr 1
        have hinj : Function.Injective fun j' => q * M + j' := fun a b h => by simpa using h
        rw [idxOf_map_inj hinj]
      · intro hm
        obtain ⟨q', hq', hm⟩ := List.mem_flatMap.mp hm
        obtain ⟨j', hj', he⟩ := List.mem_map.mp hm
        rw [List.mem_range] at hq'
        have := hL j' hj'
        have : q' * M + j' < q * M := by
          calc q' * M + j' < (q' + 1) * M := by rw [add_mul, one_mul]; omega
            _ ≤ q * M := Nat.mul_le_mul_right _ (by omega)
        omega

variable {k ℓ : ℕ}

/-! ## Steps and coefficient steps -/

/-- The nonzero rows of column `c`, increasing. -/
def rowsL (c : Coord k ℓ) : List ℕ := (List.range (k - 1 + ℓ)).filter fun j => decide (rowNZ j c)

/-- **The steps of a column**, q-major. -/
lemma stepsC_eq (c : Coord k ℓ) : stepsC c =
    (List.range (k + 1)).flatMap fun q => (rowsL c).map fun j => q * (k - 1 + ℓ) + j := by
  rw [stepsC, numSteps, rowsL, ← filter_range_mul]
  refine List.filter_congr fun σ _ => ?_
  simp only [ne_eq, ent_ne_zero_iff]

variable (I : ImplicitParitySystem k ℓ)

open Classical in
/-- The rows nonzero on the domain of `e`, increasing. -/
noncomputable def rowsR (e : Fin I.schemas.length) : List ℕ :=
  (List.range (k - 1 + ℓ)).filter fun j => decide (∃ c ∈ dom I e, rowNZ j c)

open Classical in
lemma coefSteps_eq (e : Fin I.schemas.length) : coefSteps I e =
    (List.range (k + 1)).flatMap fun q => (rowsR I e).map fun j => q * (k - 1 + ℓ) + j := by
  rw [coefSteps, numSteps, rowsR, ← filter_range_mul]
  refine List.filter_congr fun σ _ => ?_
  simp only [ne_eq, ent_ne_zero_iff]

lemma rowsL_sub {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) {j : ℕ}
    (hj : j ∈ rowsL c) : j ∈ rowsR I e := by
  simp only [rowsL, rowsR, List.mem_filter, decide_eq_true_eq] at hj ⊢
  exact ⟨hj.1, c, hc, hj.2⟩

/-- **The coefficient index of an entry.** -/
lemma idxOf_coefSteps {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) {q j : ℕ}
    (hq : q < k + 1) (hj : j ∈ rowsL c) :
    (coefSteps I e).idxOf (q * (k - 1 + ℓ) + j) =
      q * (rowsR I e).length + (rowsR I e).idxOf j := by
  rw [coefSteps_eq]
  refine idxOf_blocks _ _ (fun j hj => ?_) (rowsL_sub I hc hj) _ _ hq
  simp only [rowsR, List.mem_filter, List.mem_range] at hj; exact hj.1

end Lax119563Proofs.Compiler
