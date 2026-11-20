import Lax119563.IterationNumber
import Lax119563.GameCharacterization
import Lax119563Proofs.Counter.Size
import Lax119563Proofs.Counter.Stabilize

/-!
# The iteration number lower bound

We compile the counter `𝓘_ctr^{k,ℓ}` with the row-space compiler, for `k` fixed and `ℓ`
growing.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.PebbleGame
open Lax119563.RowSpaceCompiler

namespace Lax119563Proofs.Counter

/--
---
conclusion: Lax119563.IterationNumber.iteration_number_lower_bound
---
Fix `k = K + 1 ≥ 3` and compile the counter implicit parity system `counter K ℓ` (main
location carrying all `2^{(k-1)ℓ}` counter values, three equality schemas per increment
position, endpoints initialized `0` and `1`) with the row-space compiler.

* Its conflict round `τ` is finite and at least `2^{(k-1)ℓ}` (`counter_conflictRound`, via
  a potential argument along the chain of equalities).
* Its size parameter is at most `C_K 2^ℓ` (`sizeParameter_le`): the coordinates of the
  domain of an increment at position `j` have fixed bits in the rows below `⌊j/K⌋`, which
  bounds both the domain size and the rank of the restricted check matrix.
* Duplicator survives `τ - 1` rounds of the bijective `(k+1)`-pebble game, so the graphs have
  equal size `n` and, by the game characterization, every distinguishing round `r` satisfies
  `τ ≤ r + k`; Spoiler wins eventually, so `k`-WL distinguishes the graphs.
* Hence `n^{k-1} ≤ (C C_K 2^ℓ)^{k-1} ≤ (C C_K)^{k-1} τ ≤ (C C_K)^{k-1}(k+1) r`.
* Since `k`-WL distinguishes two graphs after at most `2 n^k` rounds if at all
  (`exists_distinguishesAfter_le`), `τ ≤ 2 n^k + k`, so choosing `ℓ` large forces `n ≥ n₀`.
-/
theorem iteration_number_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, ∀ n₀ : ℕ, ∃ n ≥ n₀, ∃ G₀ G₁ : ColoredGraph,
      G₀.n = n ∧ G₁.n = n ∧ Distinguishes k G₀ G₁ ∧
      ∀ r : ℕ, DistinguishesAfter k r G₀ G₁ → n ^ (k - 1) ≤ C * r := by
  obtain ⟨C₀, hC₀⟩ := rowspace_compiler
  obtain ⟨Cₖ, hCₖ⟩ := hC₀ k hk
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  obtain ⟨CS, hCS⟩ := sizeParameter_le (K := K) (by omega)
  refine ⟨(C₀ * CS) ^ K * (K + 2), fun n₀ => ?_⟩
  set ℓ := 2 * n₀ ^ (K + 1) + 2 * K + 3 with hℓ
  obtain ⟨G₀, G₁, hspo, hdup, hsize, -⟩ := hCₖ ℓ (by omega) (counter K ℓ)
  obtain ⟨τ, hτ, hτge⟩ := counter_conflictRound (K := K) (ℓ := ℓ)
  have hτℓ : 2 ^ ℓ ≤ τ :=
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right ℓ (by omega))).trans hτge
  have hℓlt : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
  have hsurv : ∀ r : ℕ, r + 1 ≤ τ → DuplicatorSurvives (K + 1 + 1) r G₀ G₁ := fun r hr =>
    hdup r (by rw [hτ]; exact_mod_cast hr)
  have hn : G₀.n = G₁.n := (hsurv 0 (by omega)).1
  have hlow : ∀ r, DistinguishesAfter (K + 1) r G₀ G₁ → τ ≤ r + (K + 1) := by
    intro r hr
    have hw := Lax119563.GameCharacterization.spoilerWinsWithin_of_distinguishesAfter
      (by omega) hr
    by_contra hlt
    exact hw (hsurv _ (by omega))
  have hdist : Distinguishes (K + 1) G₀ G₁ := by
    obtain ⟨r', -, hr'⟩ :=
      Lax119563.GameCharacterization.distinguishesAfter_of_spoilerWinsWithin (by omega)
        (hspo τ hτ)
    exact ⟨r', hr'⟩
  refine ⟨G₀.n, ?_, G₀, G₁, rfl, hn.symm, hdist, ?_⟩
  · by_contra hlt
    push Not at hlt
    obtain ⟨r, hr, hdr⟩ := exists_distinguishesAfter_le G₀ G₁ hdist
    have h1 := hlow r hdr
    have h2 : G₀.n ^ (K + 1) ≤ n₀ ^ (K + 1) := Nat.pow_le_pow_left hlt.le _
    rw [← hn] at hr
    omega
  · intro r hr
    have h1 := hlow r hr
    have hr1 : 1 ≤ r := by
      by_contra h0
      omega
    have hnle : G₀.n ≤ C₀ * CS * 2 ^ ℓ := by
      calc G₀.n ≤ G₀.n + G₁.n := Nat.le_add_right _ _
        _ ≤ C₀ * rowSpaceSize (counter K ℓ) := hsize
        _ ≤ C₀ * (CS * 2 ^ ℓ) := Nat.mul_le_mul_left _ (hCS ℓ)
        _ = C₀ * CS * 2 ^ ℓ := by ring
    rw [Nat.add_sub_cancel]
    calc G₀.n ^ K ≤ (C₀ * CS * 2 ^ ℓ) ^ K := Nat.pow_le_pow_left hnle K
      _ = (C₀ * CS) ^ K * 2 ^ (ℓ * K) := by rw [mul_pow, ← pow_mul]
      _ ≤ (C₀ * CS) ^ K * τ := Nat.mul_le_mul_left _ hτge
      _ ≤ (C₀ * CS) ^ K * ((K + 2) * r) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = (C₀ * CS) ^ K * (K + 2) * r := by ring

end Lax119563Proofs.Counter
