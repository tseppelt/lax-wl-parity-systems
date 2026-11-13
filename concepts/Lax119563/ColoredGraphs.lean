import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: Colored graphs
type: definition
---
A *colored graph* $G = (V(G), E(G), \chi_G)$ consists of a finite vertex set $V(G)$,
an edge set $E(G) \subseteq \binom{V(G)}{2}$, and a vertex coloring
$\chi_G \colon V(G) \to \mathcal{K}$. All graphs are simple and undirected, and every
vertex has exactly one color.

We take $V(G) = \{0, \dots, n-1\}$ for the number $n$ of vertices of $G$, and use the
natural numbers as the set of colors $\mathcal{K}$. Thus any two colored graphs use the
same set of colors and can be compared.
-/

namespace Lax119563.ColoredGraphs

/-- A *colored graph* on the vertex set `{0, …, n-1}`, with colors in `ℕ`. -/
structure ColoredGraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The underlying simple graph; `graph.Adj p q` means that `pq` is an edge. -/
  graph : SimpleGraph (Fin n)
  /-- The vertex coloring. -/
  color : Fin n → ℕ

/-- The number of edges of a colored graph. -/
noncomputable def ColoredGraph.numEdges (G : ColoredGraph) : ℕ :=
  Nat.card G.graph.edgeSet

end Lax119563.ColoredGraphs
