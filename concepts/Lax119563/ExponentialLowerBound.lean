import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lax119563.DeterministicTime
import Lax119563.WLProblems

/-!
---
title: An exponential time lower bound for WL Distinguishing
type: corollary
---
**Corollary.** There is a constant $\varepsilon > 0$ such that no deterministic multitape
Turing machine decides WL Distinguishing in time $O(2^{\varepsilon N^{1/5}})$,
where $N$ is the length of the input.

The proof applies the reduction from exponential time to a language in
$\mathsf{DTIME}(2^n) \setminus \mathsf{DTIME}(2^{n/4})$: for inputs of length $n$ it produces
graphs with $O(n^5 / \log n)$ vertices in polynomial time, and the encoded instance has
polynomial length.

# Implementation notes
The input is the instance $(k, G, H)$ in the encoding `encodeWLInstance` of
`Lax119563.WLProblems`, with the dimension $k$ part of the input, and $N$ is the length of
`encodeWLInstance k G H`. Measuring in the input length rather than in the number of vertices
makes the statement stronger, and it accounts for the codes of $k$ and of the colors, which a
machine with a budget in the number of vertices could not even read. A machine deciding the
problem in time $O(2^{\varepsilon N^{1/5}})$ would, for some constant $C$, decide on every
encoded instance within $C 2^{\varepsilon N^{1/5}} + C$ steps whether $k$-WL distinguishes
$G$ and $H$. As in `Lax119563.RuntimeLowerBound`, the machine is not
required to handle other strings.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.DeterministicTime
  Lax119563.WLProblems
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563.ExponentialLowerBound

/-- **Exponential time lower bound.** For some `ε > 0`, no deterministic multitape Turing
machine decides WL Distinguishing on encoded instances of length `N` within
`O(2^{ε N^{1/5}})` steps. -/
axiom exponential_lower_bound :
    ∃ ε : ℝ, 0 < ε ∧ ¬ ∃ M : Machine, Deterministic M ∧ ∃ C : ℕ,
      ∀ (k : ℕ) (G H : ColoredGraph),
        DecidesExactlyWithin M (encodeWLInstance k G H) (Distinguishes k G H)
          ⌊C * (2 : ℝ) ^ (ε * ((encodeWLInstance k G H).length : ℝ) ^ ((1 : ℝ) / 5)) + C⌋₊

end Lax119563.ExponentialLowerBound
