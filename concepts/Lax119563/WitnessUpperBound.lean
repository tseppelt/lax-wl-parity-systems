import Mathlib.Data.Nat.Log
import Lax119563.ColoredHomomorphisms
import Lax119563.WeisfeilerLeman

/-!
---
title: An upper bound on the size of homomorphism witnesses
type: corollary
---
**Corollary.** Let $k \geq 2$, and let $G, H$ be colored graphs with at most $n$ vertices
each that are distinguished by $k$-WL. Then some colored graph $F$ with
$\operatorname{tw}(F) \leq k$ and $\hom(F, G) \neq \hom(F, H)$ satisfies
$|V(F)| \leq 2^{O_k(n^{k-1} \log n)}$.

Together with the witness size lower bound, this shows that the lower bound is tight up to a
logarithmic factor in the exponent.

# Implementation notes

The constant hidden in $O_k$ is made explicit: there is a $C$, depending on $k$ only, such
that for all $n \geq 2$ a witness with at most $2^{C n^{k-1} \lfloor \log_2 n \rfloor}$
vertices exists.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.ColoredHomomorphisms

namespace Lax119563.WitnessUpperBound

/-- **Witness size upper bound.** If `k`-WL distinguishes colored graphs `G` and `H` with at
most `n` vertices each, then so do the homomorphism counts of a colored graph of treewidth at
most `k` with at most `2 ^ (C n ^ (k - 1) log₂ n)` vertices. -/
axiom witness_upper_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n → ∀ G H : ColoredGraph, G.n ≤ n → H.n ≤ n →
      Distinguishes k G H →
      ∃ F : ColoredGraph, TreewidthAtMost F k ∧ hom F G ≠ hom F H ∧
        F.n ≤ 2 ^ (C * n ^ (k - 1) * Nat.log 2 n)

end Lax119563.WitnessUpperBound
