import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Lax489179.TuringMachine

/-!
---
title: Deterministic multitape Turing machines and running time
type: definition
---
We use deterministic multitape Turing machines with a finite number of tapes, symbols and
states, in which every transition reads the scanned symbols, writes one symbol per tape, and
moves each head by at most one cell. The cells of each tape are indexed by the integers; initially all heads
are at position zero, the first tape (tape $0$) contains the binary input $x$ at positions
$0, \dots, |x| - 1$, and all other cells are blank. Each transition, including the halting
transition, takes one step, and halting returns a bit.

* A machine *halts within $t$ steps* if it has returned its bit after $t$ steps.
* A machine *decides* a property of the input *within $t$ steps* if it halts within $t$ steps
  and returns $1$ exactly when the property holds. It *accepts* $x$ if it halts on $x$ and
  returns $1$.
* A machine *computes $y$ from $x$ within $t$ steps* if on input $x$ it halts within $t$
  steps and, at that point, tape $0$ contains exactly $y$, laid out as an input would be:
  $y$ at positions $0, \dots, |y| - 1$ and blanks elsewhere.
* A language $\mathcal L \subseteq \{0, 1\}^*$ is decidable in time $O(f(n))$ if some
  deterministic machine $M$ and constant $C$ are such that $M$ decides $x \in \mathcal L$
  within $C f(|x|) + C$ steps, for every $x$.

# Implementation notes

The machine model is the one of `Lax489179.TuringMachine`, restricted to deterministic
machines, whose transitions ignore the random bit. Their runs are evaluated with the
constant random bit `false`. Taking a step from a halted configuration does not change it, so
"halts within $t$ steps" means that the answer is present after $t$ steps.

`Lax489179.TuringMachine.DecidesWithin` is the bounded-error notion of deciding for randomized
machines; for deterministic machines it agrees with `DecidesExactlyWithin`
(`Lax489179.DeterministicSemantics.turing_exact`).

# Choice of machine model

The time hierarchy theorem is the place where the exact exponent of the main lower
bound enters: Theorem `runtime_lower_bound` rules out running time $O(N^{k-1-\varepsilon})$,
and that exponent depends on the machine model. Polynomially equivalent models are therefore
not interchangeable here. The available Turing machine notions compare as follows.

* **Mathlib, single-tape machines** (`Turing.TM0`, `Turing.TM1`). These are one-tape models.
  A single-tape machine needs $\Omega(n^2)$ steps for tasks that a two-tape machine does in
  linear time, such as recognizing palindromes or copying its input. Our reduction
  (built from `packed_representation` and `matrix_compiler`) runs in quasi-linear time $O(n \log^c n)$ only on several tapes, and the
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

  Hence $\mathsf{DTIME}(n^s)$ would have to be defined here anyway, and the theorem, which is
  stated in the literature for multitape machines, would transfer to this model only through
  a simulation.
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
  which the paper states its reduction and its lower bound, so the statement says exactly
  what the literature proves. It is the registered model of the fine-grained hypotheses
  (SETH, ETH, 3SUM, APSP), so the lower bound lives in the same model as those conditional
  statements. We restrict it to deterministic machines (`Deterministic`), whose transitions
  ignore the random bit.

Neither mathlib nor the archive provides machine constructions for `Lax489179`, so those
needed here (composition, rewinding, the compiled reduction programs, and a universal machine
for the diagonalization) are carried out directly in this model in the proofs. The
translations to the archive's single-tape and multi-stack models, used for the
$\mathsf{EXPTIME}$-hardness of WL Distinguishing, are `Lax119563.MachineTranslations`.
-/

open Lax489179.TuringMachine

namespace Lax119563.DeterministicTime

/-- The configuration of `M` after `t` steps on input `x`. -/
def runOn (M : Machine) (x : List Bool) (t : ℕ) : Config M :=
  run M t (fun _ => false) (init M x)

/-- `M` halts on input `x` within `t` steps: its answer is present after `t` steps. -/
def HaltsWithin (M : Machine) (x : List Bool) (t : ℕ) : Prop :=
  (runOn M x t).answer.isSome

/-- `M` decides `P` on input `x` within `t` steps: it halts within `t` steps and returns
`true` exactly when `P` holds. -/
def DecidesExactlyWithin (M : Machine) (x : List Bool) (P : Prop) (t : ℕ) : Prop :=
  ∃ b, (runOn M x t).answer = some b ∧ (b = true ↔ P)

/-- `M` accepts `x`: it halts on `x` and returns `true`. -/
def Accepts (M : Machine) (x : List Bool) : Prop :=
  ∃ t, (runOn M x t).answer = some true

/-- `M` computes `y` from `x` within `t` steps: it halts within `t` steps, and then tape `0`
holds `y` in the layout of an input. -/
def ComputesWithin (M : Machine) (x y : List Bool) (t : ℕ) : Prop :=
  HaltsWithin M x t ∧ (runOn M x t).tape 0 = (init M y).tape 0

/-- The language `L` is decidable in time `O(f(n))` by a deterministic multitape Turing
machine. -/
def DecidableInTime (L : Set (List Bool)) (f : ℕ → ℝ) : Prop :=
  ∃ M : Machine, Deterministic M ∧ ∃ C : ℕ,
    ∀ x : List Bool, DecidesExactlyWithin M x (x ∈ L) ⌊C * f x.length + C⌋₊

end Lax119563.DeterministicTime
