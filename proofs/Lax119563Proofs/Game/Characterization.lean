import Lax119563.GameCharacterization
import Lax119563Proofs.HomTensors.Part1

/-!
# The pebble game characterization of Weisfeiler–Leman

Proofs of the three statements of `Lax119563.GameCharacterization`.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.PebbleGame

namespace Lax119563Proofs.Game

/--
---
conclusion: Lax119563.GameCharacterization.distinguishesAfter_of_spoilerWinsWithin
---
We show that `k`-WL already distinguishes `G` and `H` after exactly `r` rounds. Otherwise
all round-`r` color classes have equal sizes, so `|V(G)| = |V(H)|`, and Duplicator survives
`r` rounds with the invariant that, for every pebble Spoiler may lift, the remaining placed
pebble pairs lie on two `k`-tuples with equal round-`s` colors (`s` the number of remaining
rounds). Equality of round-`(s+1)` colors yields a bijection matching the substituted color
tuples, which keeps the new state a partial isomorphism (using `k ≥ 2`) and, via the
invariance of colors under reindexing tuples, re-establishes the invariant.
-/
theorem distinguishesAfter_of_spoilerWinsWithin {k : ℕ} (hk : 2 ≤ k) {G H : ColoredGraph}
    {r : ℕ} (h : SpoilerWinsWithin (k + 1) r G H) :
    ∃ r' ≤ r, DistinguishesAfter k r' G H :=
  ⟨r, le_rfl, by_contra fun h' => h (duplicatorSurvives_of_not_distinguishesAfter hk h')⟩

/--
---
conclusion: Lax119563.GameCharacterization.spoilerWinsWithin_of_distinguishesAfter
---
If the vertex numbers differ Spoiler wins at once. Otherwise Spoiler uses the first `k`
rounds to place pebbles `0, …, k-1` one by one, always choosing a vertex for which the
number of extensions of the placed prefix with a fixed round-`r` color differs between `G`
and `H`; this ends in tuples with different round-`r` colors. From such tuples Spoiler wins
within `r` more rounds by induction: he places the free pebble on a vertex where the
substituted color tuples differ under Duplicator's bijection and continues with the
`k` pebbles carrying a pair of tuples with different round-`(r-1)` colors.
-/
theorem spoilerWinsWithin_of_distinguishesAfter {k : ℕ} (hk : 2 ≤ k) {G H : ColoredGraph}
    {r : ℕ} (h : DistinguishesAfter k r G H) :
    SpoilerWinsWithin (k + 1) (r + k) G H :=
  spoilerWinsWithin_of_distinguishesAfter' (by omega) h

/--
---
conclusion: Lax119563.GameCharacterization.duplicatorWins_iff
---
Combination of the two directions: a distinction after `r` rounds gives a Spoiler win
within `r + k` rounds, and if no round distinguishes `G` and `H`, Duplicator survives every
number of rounds.
-/
theorem duplicatorWins_iff {k : ℕ} (hk : 2 ≤ k) (G H : ColoredGraph) :
    DuplicatorWins (k + 1) G H ↔ ¬ Distinguishes k G H := by
  constructor
  · rintro hw ⟨r, hr⟩
    exact spoilerWinsWithin_of_distinguishesAfter hk hr (hw (r + k))
  · intro hd r
    exact duplicatorSurvives_of_not_distinguishesAfter hk fun hr => hd ⟨r, hr⟩

end Lax119563Proofs.Game
