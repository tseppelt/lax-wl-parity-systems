import Mathlib.Logic.Equiv.Fin.Basic
import Lax119563.ColoredGraphs

/-!
---
title: The bijective pebble game
type: definition
---
Let $G, H$ be colored graphs and $m \geq 1$. The *bijective $m$-pebble game*
$\mathrm{BP}_m(G, H)$ is played by two players, Spoiler and Duplicator, with $m$ pairs of
pebbles. A *game state* is a partial map $S$ assigning to some pebble indices $i \in [m]$ a
pair $S(i) = (p_i, q_i) \in V(G) \times V(H)$. The game starts in the empty game state. If
$|V(G)| \neq |V(H)|$, Spoiler wins immediately. Otherwise, each round consists of the
following steps:

1. Spoiler chooses $i \in [m]$ and lifts the $i$-th pebble pair.
2. Duplicator chooses a bijection $f \colon V(G) \to V(H)$.
3. Spoiler chooses $p \in V(G)$ and places the $i$-th pebble pair on $p$ and $f(p)$, i.e.,
   sets $S(i) = (p, f(p))$.

Spoiler wins after a round if the map $p_i \mapsto q_i$, for the placed pairs
$S(i) = (p_i, q_i)$, is not a partial isomorphism: for all placed $i, j$ we need
$p_i = p_j \iff q_i = q_j$, $p_i p_j \in E(G) \iff q_i q_j \in E(H)$, and
$\chi_G(p_i) = \chi_H(q_i)$.

For $r \geq 0$, Spoiler *wins within $r$ rounds* if he has a strategy that wins after one of
the first $r$ rounds against every strategy of Duplicator; otherwise Duplicator *survives $r$
rounds*. Duplicator *wins* $\mathrm{BP}_m(G, H)$ if she survives $r$ rounds for every $r$.

# Implementation notes

Survival is defined by recursion on the number of remaining rounds: Duplicator survives
$r + 1$ rounds from a state if, for every pebble index Spoiler may lift, she has a
bijection such that every placement yields a partial isomorphism from which she survives
$r$ further rounds.
-/

open Lax119563.ColoredGraphs

namespace Lax119563.PebbleGame

/-- A game state of the `m`-pebble game: the pebble pairs currently placed. -/
abbrev GameState (m : ℕ) (G H : ColoredGraph) := Fin m → Option (Fin G.n × Fin H.n)

/-- The placed pebble pairs `p_i ↦ q_i` form a partial isomorphism. -/
def IsPartialIso {m : ℕ} (G H : ColoredGraph) (S : GameState m G H) : Prop :=
  ∀ i j : Fin m, ∀ p q p' q', S i = some (p, q) → S j = some (p', q') →
    (p = p' ↔ q = q') ∧ (G.graph.Adj p p' ↔ H.graph.Adj q q') ∧ G.color p = H.color q

/-- Duplicator survives `r` further rounds of `BP_m(G, H)` from the game state `S`. -/
def SurvivesFrom {m : ℕ} (G H : ColoredGraph) : ℕ → GameState m G H → Prop
  | 0, _ => True
  | r + 1, S => ∀ i : Fin m, ∃ f : Fin G.n ≃ Fin H.n, ∀ p : Fin G.n,
      IsPartialIso G H (Function.update S i (some (p, f p))) ∧
        SurvivesFrom G H r (Function.update S i (some (p, f p)))

/-- Duplicator survives `r` rounds of `BP_m(G, H)`, started in the empty game state. -/
def DuplicatorSurvives (m r : ℕ) (G H : ColoredGraph) : Prop :=
  G.n = H.n ∧ SurvivesFrom (m := m) G H r (fun _ => none)

/-- Spoiler wins `BP_m(G, H)` within `r` rounds. -/
def SpoilerWinsWithin (m r : ℕ) (G H : ColoredGraph) : Prop :=
  ¬ DuplicatorSurvives m r G H

/-- Duplicator wins `BP_m(G, H)`. -/
def DuplicatorWins (m : ℕ) (G H : ColoredGraph) : Prop :=
  ∀ r, DuplicatorSurvives m r G H

end Lax119563.PebbleGame
