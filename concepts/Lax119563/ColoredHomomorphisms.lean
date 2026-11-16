import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.SetTheory.Cardinal.Finite
import Lax228581.Treewidth
import Lax119563.ColoredGraphs

/-!
---
title: Homomorphism counts and treewidth of colored graphs
type: definition
---
A *homomorphism* from a colored graph $F$ to a colored graph $G$ is a map
$h \colon V(F) \to V(G)$ that sends edges to edges and preserves colors:
$h(u) h(v) \in E(G)$ for every edge $uv \in E(F)$, and $\chi_G(h(v)) = \chi_F(v)$ for every
$v \in V(F)$. We write $\hom(F, G)$ for the number of homomorphisms from $F$ to $G$.

The *treewidth* $\operatorname{tw}(F)$ of a colored graph $F$ is the treewidth of its
underlying graph, i.e., the least $w$ such that the underlying graph has a tree decomposition
whose bags have at most $w + 1$ vertices.

# Implementation notes

Tree decompositions and treewidth are those of `Lax228581.Treewidth`.
-/

open Lax119563.ColoredGraphs Lax228581.Treewidth

namespace Lax119563.ColoredHomomorphisms

/-- $\hom(F, G)$: the number of color-preserving homomorphisms from `F` to `G`. -/
noncomputable def hom (F G : ColoredGraph) : ℕ :=
  Nat.card {h : F.graph →g G.graph // ∀ v, G.color (h v) = F.color v}

/-- $\operatorname{tw}(F) \le w$: the underlying graph of `F` has a tree decomposition whose
bags have at most `w + 1` vertices. -/
def TreewidthAtMost (F : ColoredGraph) (w : ℕ) : Prop :=
  HasTreewidthAtMost F.graph w

end Lax119563.ColoredHomomorphisms
