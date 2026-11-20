import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lax119563.DeterministicTime

/-!
---
title: The deterministic time hierarchy theorem
type: theorem
---
Hartmanis and Stearns; Hennie and Stearns: for every integer $s \geq 1$ and every real
$a < s$, there is a language $\mathcal L \subseteq \{0, 1\}^*$ with
$$\mathcal L \in \mathsf{DTIME}(n^s) \setminus \mathsf{DTIME}(n^a),$$
i.e., $\mathcal L$ is decided by a deterministic multitape Turing machine in time $O(n^s)$,
but by no deterministic multitape Turing machine in time $O(n^a)$.

# Implementation notes

The machine model is that of `Lax119563.DeterministicTime`; see there for why the exact
exponent of the main lower bound enters here and for the choice of the model.
-/

open Lax119563.DeterministicTime

namespace Lax119563.TimeHierarchy

/-- **The deterministic time hierarchy theorem** for polynomial time bounds. -/
axiom time_hierarchy (s : ℕ) (hs : 1 ≤ s) (a : ℝ) (ha : a < s) :
    ∃ L : Set (List Bool),
      DecidableInTime L (fun n => (n : ℝ) ^ s) ∧ ¬ DecidableInTime L (fun n => (n : ℝ) ^ a)

end Lax119563.TimeHierarchy
