import Lax119563.ColoredHomomorphisms
import Lax119563.WeisfeilerLeman

/-!
---
title: A lower bound on the size of homomorphism witnesses
type: theorem
---
**Theorem.** Let $k \geq 3$ be fixed. For every $n_0 \in \mathbb N$ there are some
$n \geq n_0$ and $n$-vertex colored graphs $G_0, G_1$, distinguished by $k$-WL, such that
every colored graph $F$ with $\operatorname{tw}(F) \leq k$ and
$\hom(F, G_0) \neq \hom(F, G_1)$ satisfies $|V(F)| \geq 2^{\Omega_k(n^{k-1})}$.

By the homomorphism characterization of $k$-WL, such graphs $F$ exist. The bound is tight up
to a logarithmic factor in the exponent.

# Implementation notes

The constant hidden in $\Omega_k$ is made explicit: there is a $C > 0$, depending on $k$
only, such that every such $F$ has at least $2^{\lfloor n^{k-1} / C \rfloor}$ vertices.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.ColoredHomomorphisms

namespace Lax119563.WitnessLowerBound

/-- **Witness size lower bound.** For `k ≥ 3` there are arbitrarily large pairs of `n`-vertex
colored graphs which `k`-WL distinguishes, but which are distinguished by the homomorphism
counts of a colored graph of treewidth at most `k` only if it has at least
`2 ^ (n ^ (k - 1) / C)` vertices. -/
axiom witness_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ ∀ n₀ : ℕ, ∃ n ≥ n₀, ∃ G₀ G₁ : ColoredGraph,
      G₀.n = n ∧ G₁.n = n ∧ Distinguishes k G₀ G₁ ∧
      ∀ F : ColoredGraph, TreewidthAtMost F k → hom F G₀ ≠ hom F G₁ →
        2 ^ (n ^ (k - 1) / C) ≤ F.n

end Lax119563.WitnessLowerBound
