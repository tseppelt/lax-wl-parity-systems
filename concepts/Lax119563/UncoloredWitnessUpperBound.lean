import Mathlib.Data.Nat.Log
import Lax871432.HomomorphismIndistinguishability
import Lax119563.TreewidthClasses

/-!
---
title: An upper bound on the size of homomorphism witnesses for uncolored graphs
type: corollary
---
**Corollary.** Let $k \geq 2$, and let $G, H$ be graphs with at most $n$ vertices each that
are not homomorphism indistinguishable over the class $\mathcal T_k$ of graphs of treewidth at
most $k$. Then some graph $F \in \mathcal T_k$ with $\hom(F, G) \neq \hom(F, H)$ satisfies
$|V(F)| \leq 2^{O_k(n^{k-1} \log n)}$.

This is the witness size upper bound for colored graphs, applied to graphs all of whose
vertices have the same color, and phrased in terms of homomorphism indistinguishability.

# Implementation notes

Homomorphism counts and homomorphism indistinguishability $G \equiv_{\mathcal F} H$ are those
of `Lax871432`. As there, witnesses are graphs on vertex sets $\{0, \dots, m - 1\}$. The
constant hidden in $O_k$ is made explicit as in the colored statement.
-/

open Lax871432.HomomorphismCounts Lax871432.HomomorphismIndistinguishability
  Lax119563.TreewidthClasses

namespace Lax119563.UncoloredWitnessUpperBound

/-- **Witness size upper bound for uncolored graphs.** If graphs `G` and `H` with at most `n`
vertices each are not homomorphism indistinguishable over the graphs of treewidth at most
`k`, then some graph of treewidth at most `k` with at most `2 ^ (C n ^ (k - 1) log₂ n)`
vertices has different numbers of homomorphisms to `G` and to `H`. -/
axiom uncolored_witness_upper_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∀ {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
        Fintype.card V ≤ n → Fintype.card W ≤ n → ¬ (G ≡[treewidthClass k] H) →
        ∃ (m : ℕ) (F : SimpleGraph (Fin m)), (treewidthClass k).Mem F ∧
          homCount F G ≠ homCount F H ∧ m ≤ 2 ^ (C * n ^ (k - 1) * Nat.log 2 n)

end Lax119563.UncoloredWitnessUpperBound
