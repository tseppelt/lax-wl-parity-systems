import Lax119563.ColoredHomomorphisms
import Lax119563.WeisfeilerLeman

/-!
---
title: Homomorphism witnesses from rounds
type: theorem
---
**Theorem.** Let $k \geq 2$ and $r \geq 0$, and let $G, H$ be colored graphs. If $k$-WL
distinguishes $G$ and $H$ after $r$ rounds, then some colored graph $F$ with
$\operatorname{tw}(F) \leq k$ and
$$|V(F)| \leq k (k M)^r, \qquad \text{where } M = |V(G)|^k + |V(H)|^k,$$
satisfies $\hom(F, G) \neq \hom(F, H)$.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.ColoredHomomorphisms

namespace Lax119563.WitnessFromRounds

/-- A distinction by `k`-WL after `r` rounds is witnessed by the homomorphism counts of a
colored graph of treewidth at most `k` with at most `k (k M) ^ r` vertices, where
`M = |V(G)| ^ k + |V(H)| ^ k`. -/
axiom witness_from_rounds {k : ℕ} (hk : 2 ≤ k) {r : ℕ} {G H : ColoredGraph}
    (h : DistinguishesAfter k r G H) :
    ∃ F : ColoredGraph, TreewidthAtMost F k ∧
      F.n ≤ k * (k * (G.n ^ k + H.n ^ k)) ^ r ∧ hom F G ≠ hom F H

end Lax119563.WitnessFromRounds
