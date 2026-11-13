import Lax119563.WeisfeilerLeman
import Lax119563.PebbleGame

/-!
---
title: The pebble game characterization of Weisfeiler–Leman
type: theorem
---
Cai, Fürer and Immerman, Immerman and Lander, and Hella: let $k \geq 2$, let $G, H$ be
colored graphs, and let $r \geq 0$.

1. If Spoiler wins $\mathrm{BP}_{k+1}(G, H)$ within $r$ rounds, then $k$-WL distinguishes
   $G$ and $H$ after at most $r$ rounds.
2. If $k$-WL distinguishes $G$ and $H$ after $r$ rounds, then Spoiler wins
   $\mathrm{BP}_{k+1}(G, H)$ within $r + k$ rounds.

In particular, Duplicator wins $\mathrm{BP}_{k+1}(G, H)$ if and only if $k$-WL does not
distinguish $G$ and $H$.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.PebbleGame

namespace Lax119563.GameCharacterization

/-- A win of Spoiler within `r` rounds of `BP_{k+1}(G, H)` yields a distinction by `k`-WL
after at most `r` rounds. -/
axiom distinguishesAfter_of_spoilerWinsWithin {k : ℕ} (hk : 2 ≤ k) {G H : ColoredGraph}
    {r : ℕ} (h : SpoilerWinsWithin (k + 1) r G H) :
    ∃ r' ≤ r, DistinguishesAfter k r' G H

/-- A distinction by `k`-WL after `r` rounds yields a win of Spoiler within `r + k` rounds
of `BP_{k+1}(G, H)`. -/
axiom spoilerWinsWithin_of_distinguishesAfter {k : ℕ} (hk : 2 ≤ k) {G H : ColoredGraph}
    {r : ℕ} (h : DistinguishesAfter k r G H) :
    SpoilerWinsWithin (k + 1) (r + k) G H

/-- Duplicator wins `BP_{k+1}(G, H)` if and only if `k`-WL does not distinguish `G` and `H`. -/
axiom duplicatorWins_iff {k : ℕ} (hk : 2 ≤ k) (G H : ColoredGraph) :
    DuplicatorWins (k + 1) G H ↔ ¬ Distinguishes k G H

end Lax119563.GameCharacterization
