import Lax119563.WitnessLowerBound
import Lax119563.GameCharacterization
import Lax119563.RowSpaceCompiler
import Lax119563Proofs.Witness.Stabilize
import Lax119563Proofs.Witness.RelayTree
import Lax119563Proofs.Witness.RelayConflict
import Lax119563Proofs.Witness.RelaySize

/-!
# A lower bound on the size of homomorphism witnesses

We compile the relay counter `relay k ℓ` with the row-space compiler and combine:

* `relay_hasConflict`: the conflict round `τ` is finite, so Spoiler wins and `k`-WL
  distinguishes the compiled graphs;
* `relay_tree_bound`: every contradiction tree has more than `2^(2^m - 1)` nodes, `m = (k-1)ℓ`;
  by item 4 of the compiler, every witness `F` has `5|V(F)| + 1 > 2^(2^m - 1)`; and since a
  conflict in round `τ` gives a contradiction tree with at most `2^(τ+2) - 1` nodes, also
  `τ ≥ 2^m - 2`;
* `relay_size`: the compiled graphs have `O_k(2^ℓ)` vertices;
* `exists_distinguishesAfter_le`: a distinction by `k`-WL happens within `2n^k` rounds, so
  Duplicator cannot survive `τ - 1 ≥ 2^m - 3` rounds unless `n` is large; this gives `n → ∞`.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.ColoredHomomorphisms
open Lax119563.PebbleGame Lax119563.ImplicitParitySystems Lax119563.RowSpaceCompiler
open Lax119563.GameCharacterization Lax119563.ParitySystems

namespace Lax119563Proofs.Witness

/-- The final arithmetic: from `n ≤ E · 2^ℓ` and `5 F + 1 > 2^(2^m - 1)` with
`m = (k-1)ℓ ≥ 2`, conclude `2^(n^(k-1) / (5 E^(k-1))) ≤ F`. -/
theorem final_arith {k ℓ n E F : ℕ} (hE : 0 < E) (hm : 2 ≤ (k - 1) * ℓ)
    (hn : n ≤ E * 2 ^ ℓ) (hF : 2 ^ (2 ^ ((k - 1) * ℓ) - 1) < 5 * F + 1) :
    2 ^ (n ^ (k - 1) / (5 * E ^ (k - 1))) ≤ F := by
  set Y := 2 ^ ((k - 1) * ℓ) with hY
  have hY4 : 4 ≤ Y := by
    rw [hY]; calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hm
  have hpow : n ^ (k - 1) ≤ E ^ (k - 1) * Y := by
    calc n ^ (k - 1) ≤ (E * 2 ^ ℓ) ^ (k - 1) := Nat.pow_le_pow_left hn _
      _ = E ^ (k - 1) * Y := by rw [mul_pow, ← pow_mul, mul_comm ℓ, hY]
  have hEp : 0 < E ^ (k - 1) := pow_pos hE _
  have hq : n ^ (k - 1) / (5 * E ^ (k - 1)) ≤ Y - 4 := by
    calc n ^ (k - 1) / (5 * E ^ (k - 1)) ≤ (E ^ (k - 1) * Y) / (E ^ (k - 1) * 5) := by
          rw [mul_comm 5]; exact Nat.div_le_div_right hpow
      _ = Y / 5 := Nat.mul_div_mul_left _ _ hEp
      _ ≤ Y - 4 := by omega
  have h8 : 2 ^ (Y - 1) = 2 ^ (Y - 4) * 8 := by
    rw [show Y - 1 = (Y - 4) + 3 by omega, pow_add]; norm_num
  have hZ : 2 ^ (Y - 4) ≤ F := by omega
  exact (Nat.pow_le_pow_right (by norm_num) hq).trans hZ

/--
---
conclusion: Lax119563.WitnessLowerBound.witness_lower_bound
---
We apply the row-space compiler to the relay counter `relay k ℓ` (counting down through the
`2^m` addresses, `m = (k-1)ℓ`, with every decrement realized by a one-way gate), for
`ℓ = 2 n₀^k + k + 3`. Unit propagation reaches a conflict (`relay_hasConflict`), so Spoiler
wins and `k`-WL distinguishes the graphs. A weight argument shows that every contradiction tree
has more than `2^(2^m - 1)` nodes (`relay_tree_bound`); with item 4 of the compiler this bounds
every witness `F` by `5|V(F)| + 1 > 2^(2^m - 1)`. The size parameter is `O_k(2^ℓ)`
(`relay_size`), so the graphs have `n = O_k(2^ℓ)` vertices, giving the bound with
`C = 5 (C_rs · sizeConst k + 1)^(k-1)`. Finally `n ≥ n₀`: the conflict round is at least
`2^m - 2`, since a conflict in round `τ` yields a contradiction tree with fewer than `2^(τ+2)`
nodes; Duplicator survives until then, while `k`-WL distinguishes within `2 n^k` rounds
(`exists_distinguishesAfter_le`), so `2^m < 2 n^k + k + 3`.
-/
theorem witness_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ ∀ n₀ : ℕ, ∃ n ≥ n₀, ∃ G₀ G₁ : ColoredGraph,
      G₀.n = n ∧ G₁.n = n ∧ Distinguishes k G₀ G₁ ∧
      ∀ F : ColoredGraph, TreewidthAtMost F k → hom F G₀ ≠ hom F G₁ →
        2 ^ (n ^ (k - 1) / C) ≤ F.n := by
  obtain ⟨C, hC⟩ := rowspace_compiler
  obtain ⟨Ck, hCk⟩ := hC k hk
  set E := C * sizeConst k + 1 with hE
  refine ⟨5 * E ^ (k - 1), Nat.mul_pos (by norm_num) (pow_pos (by omega) _), fun n₀ => ?_⟩
  set ℓ := 2 * n₀ ^ k + k + 3 with hℓ
  obtain ⟨G₀, G₁, h1, h2, h3, h4⟩ := hCk ℓ (by omega) (relay k ℓ)
  have hm : ℓ ≤ nbits k ℓ := by
    show ℓ ≤ (k - 1) * ℓ
    exact Nat.le_mul_of_pos_left ℓ (by omega)
  have hm2 : 2 ≤ nbits k ℓ := by omega
  -- the conflict round
  have hex : ∃ r, (relay k ℓ).toParitySystem.HasConflict r := ⟨_, relay_hasConflict⟩
  obtain ⟨τ, hτ, hτc⟩ := exists_conflictRound_eq _ hex
  change (relay k ℓ).conflictRound = τ at hτ
  have hτlow : 2 ^ nbits k ℓ - 1 < τ + 2 := by
    have := relay_tree_bound (hasContradictionWithin_of_hasConflict _ hτc)
    by_contra hcon
    push_neg at hcon
    have h1 : 2 ^ (τ + 2) ≤ 2 ^ (2 ^ nbits k ℓ - 1) := Nat.pow_le_pow_right (by norm_num) hcon
    have h2 : 0 < 2 ^ (τ + 2) := Nat.two_pow_pos _
    generalize 2 ^ (τ + 2) = A at *
    generalize 2 ^ (2 ^ nbits k ℓ - 1) = B at *
    omega
  have h4m : 4 ≤ 2 ^ nbits k ℓ := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hm2
  -- equal sizes
  have hsurv0 := h2 0 (by rw [hτ]; exact_mod_cast (show 0 + 1 ≤ τ by omega))
  have hn : G₀.n = G₁.n := hsurv0.1
  -- distinguished
  obtain ⟨r, -, hr⟩ := distinguishesAfter_of_spoilerWinsWithin (by omega) (h1 τ hτ)
  refine ⟨G₀.n, ?_, G₀, G₁, rfl, hn.symm, ⟨r, hr⟩, ?_⟩
  · -- `n ≥ n₀`
    obtain ⟨r', hr', hd⟩ := exists_distinguishesAfter_le G₀ G₁ hr
    have hsp := spoilerWinsWithin_of_distinguishesAfter (by omega) hd
    have hτr : τ ≤ r' + k := by
      by_contra hcon
      exact hsp (h2 _ (by rw [hτ]; exact_mod_cast (show r' + k + 1 ≤ τ by omega)))
    have hℓ2 : ℓ < 2 ^ nbits k ℓ :=
      (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_right (by norm_num) hm)
    by_contra hlt
    push_neg at hlt
    have : G₀.n ^ k ≤ n₀ ^ k := Nat.pow_le_pow_left hlt.le _
    rw [← hn] at hr'
    omega
  · intro F hF hhom
    have hcon := relay_tree_bound (h4 F hF hhom)
    have hsize := relay_size (k := k) (ℓ := ℓ) (by omega)
    have hnE : G₀.n ≤ E * 2 ^ ℓ := by
      calc G₀.n ≤ G₀.n + G₁.n := Nat.le_add_right _ _
        _ ≤ C * rowSpaceSize (relay k ℓ) := h3
        _ ≤ C * (sizeConst k * 2 ^ ℓ) := Nat.mul_le_mul_left _ hsize
        _ ≤ C * (sizeConst k * 2 ^ ℓ) + 2 ^ ℓ := Nat.le_add_right _ _
        _ = E * 2 ^ ℓ := by rw [hE]; ring
    exact final_arith (by omega) hm2 hnE hcon

end Lax119563Proofs.Witness
