import Mathlib.LinearAlgebra.Matrix.Rank
import Lax119563.ColoredHomomorphisms
import Lax119563.ContradictionTrees
import Lax119563.MatrixCompiler

/-!
---
title: The row-space compiler
type: theorem
---
Let $k \geq 3$ and $\ell \geq 1$, and let $\mathcal I = (W, \mathfrak C, (\mathfrak C_v)_{v \in W},
\mathcal E, \iota)$ be an implicit parity system with coordinates
$\mathfrak C = [k] \times \mathbb F_2^\ell$ and conflict round $\tau = \tau(\mathcal I)$.
Then the row-space construction yields colored graphs $G_0, G_1$ such that:

1. If $\tau < \infty$, then Spoiler wins the bijective pebble game on $(G_0, G_1)$ with
   $k + 1$ pebbles in $O_k(\tau + 1)$ rounds.
2. Duplicator survives the bijective pebble game on $(G_0, G_1)$ with $k + 1$ pebbles for
   $\tau - 1$ rounds, or indefinitely if $\tau = \infty$.
3. With an absolute constant, $|V(G_0)| + |V(G_1)| = O(S)$, where
   $S = \sum_{v \in W} |\mathfrak C_v| + (k + 1) \sum_{e \in \mathcal E}
   \bigl(|\mathfrak C_e| + 2^{\operatorname{rank} B_e}\bigr)$.
4. If a colored graph $F$ with $\operatorname{tw}(F) \leq k$ satisfies
   $\hom(F, G_0) \neq \hom(F, G_1)$, then the parity system of $\mathcal I$ has a
   contradiction tree with at most $5 |V(F)| + 1$ nodes.

Here $B_e$ is the check matrix $B$ restricted to the columns in $\mathfrak C_e$, as for the
matrix compiler; deleting its zero rows does not change its rank.

# Implementation notes

The paper states items 1–3 for the explicit row-space construction, and item 4 as a separate
theorem about the same construction, for graphs $F$ with a tree decomposition of width at
most $k$ in which adjacent bags differ in one vertex; by a theorem of Abramsky, Jakl and
Paine, every graph of treewidth at most $k$ has such a decomposition. Here the graphs are
asserted to exist. The constant of the size bound is absolute, while the constant of the round
bound may depend on $k$.
-/

open Lax119563.ColoredGraphs Lax119563.PebbleGame Lax119563.ImplicitParitySystems
  Lax119563.MatrixCompiler Lax119563.ColoredHomomorphisms Lax119563.ContradictionTrees

namespace Lax119563.RowSpaceCompiler

variable {k ℓ : ℕ}

/-- The rank of `B_e`, the check matrix restricted to the coordinate domain of `e`. -/
noncomputable def rowRank {w : ℕ} (e : Schema k ℓ w) : ℕ :=
  (Matrix.of fun row (c : e.domain) => checkMatrix k ℓ row c).rank

/-- The size parameter `∑_v |𝔠_v| + (k+1) ∑_e (|𝔠_e| + 2^{rank B_e})` of the row-space
construction. -/
noncomputable def sizeParameter (I : ImplicitParitySystem k ℓ) : ℕ :=
  ∑ v, (I.domain v).card + (k + 1) * (I.schemas.map fun e => e.domain.card + 2 ^ rowRank e).sum

/-- **The row-space compiler.** Every implicit parity system with `k ≥ 3` blocks compiles to a
pair of colored graphs on which the bijective `(k+1)`-pebble game follows unit propagation:
Spoiler wins in `O_k(τ+1)` rounds if a conflict occurs in round `τ`, and Duplicator survives
`τ - 1` rounds. The graphs have `O(S)` vertices, and every distinguishing homomorphism count
from a graph of treewidth at most `k` yields a contradiction tree of comparable size. -/
axiom rowspace_compiler : ∃ C : ℕ, ∀ k : ℕ, 3 ≤ k → ∃ Cₖ : ℕ, ∀ ℓ : ℕ, 1 ≤ ℓ →
    ∀ I : ImplicitParitySystem k ℓ, ∃ G₀ G₁ : ColoredGraph,
      (∀ τ : ℕ, I.conflictRound = τ → SpoilerWinsWithin (k + 1) (Cₖ * (τ + 1)) G₀ G₁) ∧
      (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound → DuplicatorSurvives (k + 1) r G₀ G₁) ∧
      G₀.n + G₁.n ≤ C * sizeParameter I ∧
      (∀ F : ColoredGraph, TreewidthAtMost F k → hom F G₀ ≠ hom F G₁ →
        HasContradictionWithin I.toParitySystem (5 * F.n + 1))

end Lax119563.RowSpaceCompiler
