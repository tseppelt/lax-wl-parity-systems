import Lax119563.WeisfeilerLeman

/-!
---
title: Stabilization of k-WL
type: theorem
---
Each coloring $\chi^{(r+1)}_k[G]$ refines $\chi^{(r)}_k[G]$. We say that $k$-WL
*stabilizes after $r$ rounds* on a colored graph $G$ if $\chi^{(r)}_k[G]$ and
$\chi^{(r+1)}_k[G]$ induce the same partition of $V(G)^k$.

**Theorem** (Döring and Neuen). Let $k \geq 2$ be fixed. On every colored graph with $n$
vertices, $k$-WL stabilizes after $O_k(n^{k-1})$ rounds.

More precisely, Döring and Neuen prove the bound $5(n - 1)$ for $k = 2$ and the bound
$O(n^{k-1}/(k-2)! + n^{k-2})$ for $k \geq 3$.

# Implementation notes

The constant hidden in $O_k$ is made explicit: there is a $C$, depending on $k$ only, such
that $k$-WL stabilizes after some number $r \leq C n^{k-1}$ of rounds on every colored graph
with $n$ vertices.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman

namespace Lax119563.Stabilization

/-- `k`-WL stabilizes after `r` rounds on `G`: the colorings of rounds `r` and `r + 1`
induce the same partition of the `k`-tuples of vertices. -/
def StabilizesAfter (k r : ℕ) (G : ColoredGraph) : Prop :=
  ∀ p q : Fin k → Fin G.n, color G r p = color G r q ↔ color G (r + 1) p = color G (r + 1) q

/-- **Stabilization bound.** For `k ≥ 2`, `k`-WL stabilizes after `O_k(n ^ (k - 1))` rounds
on every colored graph with `n` vertices. -/
axiom stabilization_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, ∀ G : ColoredGraph, ∃ r ≤ C * G.n ^ (k - 1), StabilizesAfter k r G

end Lax119563.Stabilization
