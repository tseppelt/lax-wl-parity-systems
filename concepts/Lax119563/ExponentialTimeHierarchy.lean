import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lax119563.DeterministicTime

/-!
---
title: The deterministic time hierarchy theorem for exponential time
type: theorem
---
Hartmanis and Stearns; Hennie and Stearns: there is a language
$\mathcal L \subseteq \{0, 1\}^*$ with
$$\mathcal L \in \mathsf{DTIME}(2^n) \setminus \mathsf{DTIME}(2^{n/2}),$$
i.e., $\mathcal L$ is decided by a deterministic multitape Turing machine in time $O(2^n)$,
but by no deterministic multitape Turing machine in time $O(2^{n/2})$.

# Implementation notes
This is the exponential instance of the time hierarchy theorem, in the machine model of the
polynomial instance `Lax119563.TimeHierarchy.time_hierarchy` (see there for the choice of the
model). It applies since $2^n$ is time constructible and
$2^{n/2} \log 2^{n/2} = o(2^n)$.
-/

open Lax119563.DeterministicTime

namespace Lax119563.ExponentialTimeHierarchy

/-- **The deterministic time hierarchy theorem** for the bounds `2^n` and `2^{n/2}`. -/
axiom exp_time_hierarchy :
    ∃ L : Set (List Bool),
      DecidableInTime L (fun n => (2 : ℝ) ^ (n : ℝ)) ∧
        ¬ DecidableInTime L (fun n => (2 : ℝ) ^ ((n : ℝ) / 2))

end Lax119563.ExponentialTimeHierarchy
