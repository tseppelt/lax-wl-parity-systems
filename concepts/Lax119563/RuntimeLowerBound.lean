import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lax119563.BinaryEncodings
import Lax119563.DeterministicTime
import Lax119563.WeisfeilerLeman

/-!
---
title: An unconditional time lower bound for k-WL Distinguishing
type: theorem
---
The problem $k$-WL Distinguishing asks, given two colored graphs $G$ and $H$,
whether $k$-WL distinguishes $G$ and $H$.

**Theorem.** For every fixed $k \geq 3$ and $\varepsilon > 0$, no deterministic multitape
Turing machine solves $k$-WL Distinguishing in time $O(n^{k - 1 - \varepsilon})$, where $n$ is
the length of the binary encoding of the input pair.

This almost matches the classical upper bound of $O(n^{k+1} \log n)$.

# Implementation notes

The input graph pair is given by its binary edge-list encoding, and time is measured in the
length $n$ of the encoding `encodeGraphPair G H`. This length is at least the number
$|V(G)| + |V(H)|$ of vertices, so the statement is stronger than one in terms of vertices,
and it also rules out the degenerate case of huge colors, whose codes a machine with a
vertex-based budget could not even read. A machine solving the problem in time
$O(n^{k-1-\varepsilon})$ would, for some constant $C$, decide on every encoded pair within
$C n^{k-1-\varepsilon} + C$ steps whether $k$-WL distinguishes it. The machine is not
required to handle strings that are not encodings of graph pairs, which only strengthens the
lower bound.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563.RuntimeLowerBound

/-- **Unconditional time lower bound.** For `k ≥ 3` and `ε > 0`, no deterministic multitape
Turing machine decides `k`-WL distinguishability of colored graph pairs within
`O(n^{k-1-ε})` steps, where `n` is the length of the binary encoding of the input pair. -/
axiom runtime_lower_bound (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ M : Machine, Deterministic M ∧ ∃ C : ℕ, ∀ G H : ColoredGraph,
      DecidesExactlyWithin M (encodeGraphPair G H) (Distinguishes k G H)
        ⌊C * ((encodeGraphPair G H).length : ℝ) ^ ((k : ℝ) - 1 - ε) + C⌋₊

end Lax119563.RuntimeLowerBound
