import Lax119563.WeisfeilerLeman

/-!
---
title: A lower bound on the iteration number of k-WL
type: theorem
---
**Theorem.** Let $k \geq 3$ be fixed. For every $n_0 \in \mathbb N$ there are some
$n \geq n_0$ and $n$-vertex colored graphs $G_0, G_1$ such that $k$-WL distinguishes $G_0$
and $G_1$, but only after $\Omega_k(n^{k-1})$ iterations.

This matches the upper bound of $O_k(n^{k-1})$ on the number of iterations after which
$k$-WL stabilizes.

# Implementation notes

The constant hidden in $\Omega_k$ is made explicit: there is a $C$, depending on $k$ only,
such that $k$-WL does not distinguish $G_0$ and $G_1$ after any $r$ rounds with
$C r < n^{k-1}$.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman

namespace Lax119563.IterationNumber

/-- **Iteration number lower bound.** For `k ≥ 3` there are arbitrarily large pairs of
`n`-vertex colored graphs which `k`-WL distinguishes, but not within fewer than
`n ^ (k - 1) / C` rounds. -/
axiom iteration_number_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, ∀ n₀ : ℕ, ∃ n ≥ n₀, ∃ G₀ G₁ : ColoredGraph,
      G₀.n = n ∧ G₁.n = n ∧ Distinguishes k G₀ G₁ ∧
      ∀ r : ℕ, DistinguishesAfter k r G₀ G₁ → n ^ (k - 1) ≤ C * r

end Lax119563.IterationNumber
