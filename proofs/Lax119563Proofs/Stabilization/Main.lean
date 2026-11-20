import Lax119563.Stabilization
import Lax119563Proofs.Stabilization.HigherDim

/-!
# The stabilization bound

`k`-WL stabilizes after at most `13 n^(k-1)` rounds on colored graphs with `n` vertices.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.Stabilization

namespace Lax119563Proofs.Stabilization

/--
---
conclusion: Lax119563.Stabilization.stabilization_bound
---
We follow Döring and Neuen and take `C = 13`. Let `k = m + 2`, let `G` have `n` vertices,
and suppose `k`-WL does not stabilize after any of the rounds `0, …, r - 1`, i.e.
`χ_0 ≻ χ_1 ≻ … ≻ χ_r`. It suffices to show `r ≤ 3 n^(k-2) + 10 n^(k-1)`, which is
`< 13 n^(k-1) + 1`.

The colorings `χ_i` are refining, compatible with equality and shufflable for every
`σ : [k] → [k]`. For `v ∈ V^(k-2)` let `χ^v_i (a, b) = χ_i (v, a, b)` and let `⟨χ^v_i⟩` be the
space of complex `n × n` matrices constant on the color classes of `χ^v_i`. Then
`ℂ 1, ⟨χ^v_0⟩, ⟨χ^v_1⟩, …` is a weak chain: it contains the identity (compatibility with
equality), is closed under conjugate transposition (shufflability), and
`⟨χ^v_i⟩ ⟨χ^v_i⟩ ⊆ ⟨χ^v_{i+1}⟩` (Lemma 6.2: an entry of a product is a count over the multiset
part of the next color). Since `⟨χ^v_i⟩ = ⟨χ^v_{i+1}⟩` forces `χ^v_i ≡ χ^v_{i+1}` (Lemma 4.7),
the two-dimensional bound (Theorem 5.15, at most `10 n` strict steps of a weak chain in
`M_n(ℂ)`) bounds the number of rounds `i` with `χ^v_i ≻ χ^v_{i+1}` by `10 n`.

For `k = 2` the only `v` is empty and `χ^v_i = χ_i`, so `r ≤ 10 n`. For `k ≥ 3` let
`χ̄_i (v) = χ_i (v, v_{k-2}, v_{k-2})`. Extendability (Lemma 6.4) and shufflability give
Claim 6.5: if `χ_i (v, w_1, w_2)` is not a color `χ_i (v', ·, ·)`, then
`χ̄_{i+2} (v) ≠ χ̄_{i+2} (v')`. Claim 6.6: if `χ_i ≻ χ_{i+1}` is witnessed by
`(v, a, b)`, `(v', c, d)` and no `χ^w` splits in round `i + 1`, then
`χ̄_i (v) = χ̄_i (v')` (shufflability) and, by Claim 6.5 at round `i + 1`,
`χ̄_{i+3} (v) ≠ χ̄_{i+3} (v')`; so `χ̄` splits in round `i + 1`, `i + 2` or `i + 3`.
Every `χ̄` split increases the number of classes of `χ̄`, which is at most `n^(k-2)`. Taking
all `v ∈ V^(k-2)` (instead of the sorted prefixes of the paper),
`r ≤ 3 n^(k-2) + n^(k-2) · 10 n`.
-/
theorem stabilization_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, ∀ G : ColoredGraph, ∃ r ≤ C * G.n ^ (k - 1), StabilizesAfter k r G := by
  refine ⟨13, fun G => ?_⟩
  by_contra hcon
  have hr : ∀ i < 13 * G.n ^ (k - 1) + 1, ¬ StabilizesAfter k i G :=
    fun i hi hs => hcon ⟨i, by omega, hs⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  cases m with
  | zero =>
    have := rounds_le_two hr
    simp only [show 0 + 2 - 1 = 1 from rfl, pow_one] at this
    omega
  | succ m =>
    have := rounds_le hr
    have hle : G.n ^ (m + 1) ≤ G.n ^ (m + 2) := by
      rcases Nat.eq_zero_or_pos G.n with h | h
      · simp [h]
      · exact Nat.pow_le_pow_right h (by omega)
    simp only [show m + 1 + 2 - 1 = m + 2 by omega] at this
    omega

end Lax119563Proofs.Stabilization
