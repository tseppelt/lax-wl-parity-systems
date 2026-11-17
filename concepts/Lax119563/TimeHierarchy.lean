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

# Choice of machine model

This is the place where the exact exponent of the main lower
bound enters: Theorem `runtime_lower_bound` rules out running time $O(N^{k-1-\varepsilon})$,
and that exponent depends on the machine model. Polynomially equivalent models are therefore
not interchangeable here. The available Turing machine notions compare as follows.

* **Mathlib, single-tape machines** (`Turing.TM0`, `Turing.TM1`). These are one-tape models.
  A single-tape machine needs $\Omega(n^2)$ steps for tasks that a two-tape machine does in
  linear time, such as recognizing palindromes or copying its input. Our reduction
  (`time_reduction`) runs in quasi-linear time $O(n \log^c n)$ only on several tapes, and the
  sharp hierarchy $\mathsf{DTIME}(n^a) \subsetneq \mathsf{DTIME}(n^s)$ for every real
  $a < s$ is a multitape statement.
* **Mathlib, multi-stack machines** (`Turing.FinTM2` with `TM2OutputsInTime`,
  `TM2ComputableInTime` and `TM2ComputableInPolyTime`). A multitape machine and a multi-stack
  machine simulate each other with constant-factor overhead (one tape is two stacks), so
  this model would be adequate in principle. It has drawbacks for this statement:
  * one step executes a whole statement tree (several pushes, pops and branches);
  * only the input stack is required to have a finite alphabet;
  * a machine outputs a list, and only once all other stacks are empty and the internal
    state is reset, so there is no native notion of deciding with a Boolean answer;
  * mathlib has no time classes for a fixed exponent, and no proof that the model is
    equivalent to multitape Turing machines.

  Hence $\mathsf{DTIME}(n^s)$ would have to be defined here anyway, and the cited theorem,
  which is proven for multitape tapes, would hold for this model only through an unformalized
  simulation.
* **Complexity classes in the archive.** The registered classes on bit strings, such as
  `Lax434930.PolynomialTime.P` and `Lax429075.Reductions.ManyOne` (built on mathlib's
  `FinTM2` in polynomial time), `Lax759944.TuringPolytime` (the same, with equivalence to
  word RAMs), and `Lax434930.ExponentialTime.EXPTIME` (a single-tape machine), only speak
  about polynomial or exponential time up to a polynomial. They cannot separate
  $n^{k-1-\varepsilon}$ from $n^{k-1}$. `Lax251941` models single-tape machines as string
  rewriting, a representation meant for undecidability.
* **The fine-grained multitape model** `Lax489179.TuringMachine` (used here). It is the
  textbook deterministic multitape Turing machine:
  * a fixed finite number of tapes, symbols and states;
  * each transition reads the scanned symbols, writes one symbol per tape and moves each head
    by at most one cell, and costs exactly one step, including the halting transition, so no
    uncharged computation happens inside a transition;
  * the input is laid out on tape $0$, and halting returns a bit.

  This is the model in which Hartmanis–Stearns and Hennie–Stearns state the hierarchy, and in
  which the paper states its reduction and its lower bound, so the cited axiom says exactly
  what the literature proves. It is the registered model of the fine-grained hypotheses
  (SETH, ETH, 3SUM, APSP), so the lower bound lives in the same model as those conditional
  statements. We restrict it to deterministic machines (`Deterministic`), whose transitions
  ignore the random bit.

The price of this choice is that `Lax489179` has no bridge to mathlib's machines or to the
polynomial-time classes of the archive. The machine constructions needed for the reduction
(composition, rewinding and the compiled reduction program) are therefore carried out
directly in this model in the proofs.
-/

open Lax119563.DeterministicTime

namespace Lax119563.TimeHierarchy

/-- **The deterministic time hierarchy theorem** for polynomial time bounds. -/
axiom time_hierarchy (s : ℕ) (hs : 1 ≤ s) (a : ℝ) (ha : a < s) :
    ∃ L : Set (List Bool),
      DecidableInTime L (fun n => (n : ℝ) ^ s) ∧ ¬ DecidableInTime L (fun n => (n : ℝ) ^ a)

end Lax119563.TimeHierarchy
