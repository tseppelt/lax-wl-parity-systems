import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lax119563.WitnessUpperBound
import Lax119563.WitnessFromRounds
import Lax119563.Stabilization
import Lax119563Proofs.UpperBound.Rounds

/-!
# The witness size upper bound

Combines the Döring–Neuen stabilization bound, the bound `r_∞ + 1` on the distinguishing round,
and the construction of witnesses from rounds, followed by the size arithmetic.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.ColoredHomomorphisms
  Lax119563.Stabilization

namespace Lax119563Proofs.UpperBound

/-- For `n ≥ 2` and `L = ⌊log₂ n⌋`: `k · 2 n^k ≤ 2^((3k+1) L)`. -/
theorem base_le (k n : ℕ) (hn : 2 ≤ n) :
    k * (2 * n ^ k) ≤ 2 ^ ((3 * k + 1) * Nat.log 2 n) := by
  set L := Nat.log 2 n with hL
  have hL1 : 1 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  have hnL : n ≤ 2 ^ (2 * L) := by
    have := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n).le
    exact this.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hk : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
  have hnk : n ^ k ≤ 2 ^ (2 * L * k) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hnL k
  calc k * (2 * n ^ k) ≤ 2 ^ k * (2 ^ 1 * 2 ^ (2 * L * k)) :=
        Nat.mul_le_mul hk (Nat.mul_le_mul (by norm_num) hnk)
    _ = 2 ^ (k + 1 + 2 * L * k) := by rw [← pow_add, ← pow_add, add_assoc]
    _ ≤ 2 ^ ((3 * k + 1) * L) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- The final size estimate. -/
theorem size_le (k n C R : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (hR : R ≤ C * n ^ (k - 1) + 1) :
    k * (k * (2 * n ^ k)) ^ R ≤
      2 ^ ((k + (3 * k + 1) * C + (3 * k + 1)) * n ^ (k - 1) * Nat.log 2 n) := by
  set L := Nat.log 2 n with hL
  set m := n ^ (k - 1) with hm
  set a := 3 * k + 1 with ha
  have hL1 : 1 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  have hm1 : 1 ≤ m := Nat.one_le_pow _ _ (by omega)
  have hB1 : 1 ≤ k * (2 * n ^ k) :=
    Nat.mul_pos (by omega) (Nat.mul_pos (by norm_num) (Nat.pow_pos (by omega)))
  calc k * (k * (2 * n ^ k)) ^ R ≤ 2 ^ k * (2 ^ (a * L)) ^ (C * m + 1) :=
        Nat.mul_le_mul (Nat.lt_two_pow_self).le
          ((Nat.pow_le_pow_right hB1 hR).trans (Nat.pow_le_pow_left (base_le k n hn) _))
    _ = 2 ^ (k + a * L * (C * m + 1)) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((k + a * C + a) * m * L) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have h1 : k ≤ k * m * L := by
          calc k = k * 1 * 1 := by ring
            _ ≤ k * m * L := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hm1) hL1
        have h2 : a * L ≤ a * m * L := by
          calc a * L = a * 1 * L := by ring
            _ ≤ a * m * L := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hm1) le_rfl
        nlinarith

/--
---
conclusion: Lax119563.WitnessUpperBound.witness_upper_bound
---
By the stabilization bound (Döring–Neuen) there is `C` such that `k`-WL stabilizes on every
colored graph with `N` vertices after at most `C N^{k-1}` rounds. For `G`, `H` with at most
`n` vertices, both are stable after `r = max(r_G, r_H) ≤ C n^{k-1}` rounds, so if `k`-WL
distinguishes them it does so after some `R ≤ r + 1` rounds. Witnesses from rounds give a
colored graph `F` of treewidth at most `k` with `hom(F, G) ≠ hom(F, H)` and
`|V(F)| ≤ k (k (|V(G)|^k + |V(H)|^k))^R ≤ k (2 k n^k)^{C n^{k-1} + 1}`, which is at most
`2^{C' n^{k-1} ⌊log₂ n⌋}` for `C' = k + (3k+1)(C+1)`, using `n ≤ 2^{2 ⌊log₂ n⌋}`.
-/
theorem witness_upper_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n → ∀ G H : ColoredGraph, G.n ≤ n → H.n ≤ n →
      Distinguishes k G H →
      ∃ F : ColoredGraph, TreewidthAtMost F k ∧ hom F G ≠ hom F H ∧
        F.n ≤ 2 ^ (C * n ^ (k - 1) * Nat.log 2 n) := by
  obtain ⟨C, hC⟩ := stabilization_bound k hk
  refine ⟨k + (3 * k + 1) * C + (3 * k + 1), fun n hn G H hG hH hD => ?_⟩
  obtain ⟨rG, hrG, hsG⟩ := hC G
  obtain ⟨rH, hrH, hsH⟩ := hC H
  have hrG' : rG ≤ C * n ^ (k - 1) :=
    hrG.trans (Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hG _))
  have hrH' : rH ≤ C * n ^ (k - 1) :=
    hrH.trans (Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hH _))
  obtain ⟨R, hR, hDR⟩ := exists_distinguishesAfter_le
    (stabilizesAfter_mono hsG (le_max_left rG rH))
    (stabilizesAfter_mono hsH (le_max_right rG rH)) hD
  obtain ⟨F, htw, hsize, hhom⟩ := Lax119563.WitnessFromRounds.witness_from_rounds hk hDR
  refine ⟨F, htw, hhom, hsize.trans ?_⟩
  have hM : k * (G.n ^ k + H.n ^ k) ≤ k * (2 * n ^ k) := by
    apply Nat.mul_le_mul le_rfl
    have := Nat.pow_le_pow_left hG k
    have := Nat.pow_le_pow_left hH k
    omega
  refine (Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hM R)).trans ?_
  exact size_le k n C R hn (by omega) (hR.trans (by have := max_le hrG' hrH'; omega))

end Lax119563Proofs.UpperBound
