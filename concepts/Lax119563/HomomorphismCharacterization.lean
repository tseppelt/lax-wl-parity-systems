import Lax119563.ColoredHomomorphisms
import Lax119563.WeisfeilerLeman

/-!
---
title: The homomorphism characterization of Weisfeiler–Leman
type: theorem
---
Dvořák, and Dell, Grohe and Rattan: let $k \geq 2$ and let $G, H$ be colored graphs. Then
$k$-WL distinguishes $G$ and $H$ if and only if there is a colored graph $F$ with
$\operatorname{tw}(F) \leq k$ and $\hom(F, G) \neq \hom(F, H)$.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.ColoredHomomorphisms

namespace Lax119563.HomomorphismCharacterization

/-- `k`-WL distinguishes `G` and `H` if and only if some colored graph of treewidth at most
`k` has different numbers of homomorphisms to `G` and to `H`. -/
axiom distinguishes_iff_exists_hom_ne {k : ℕ} (hk : 2 ≤ k) (G H : ColoredGraph) :
    Distinguishes k G H ↔ ∃ F : ColoredGraph, TreewidthAtMost F k ∧ hom F G ≠ hom F H

end Lax119563.HomomorphismCharacterization
