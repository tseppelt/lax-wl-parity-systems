import Mathlib.Computability.Partrec
import Mathlib.Computability.TuringMachine.Computable
import Lax434930.ExponentialTime
import Lax759944.RamPolytime
import Lax119563.BinaryEncodings
import Lax119563.DeterministicTime

/-!
---
title: Translations between machine models
type: theorem
---
Our reductions are deterministic multitape Turing machines; the standard complexity classes
of the archive are defined with other machine models. The following simulations translate
between them.
1. **Single-tape machines.** A single-tape machine halting within $T$ steps on an input of
   length $n$ is simulated by a deterministic multitape machine in $O(T + n)$ steps, with the
   same answer.
2. **Multi-stack machines.** A function computed by a deterministic multitape machine in
   polynomial time is computable in polynomial time by a multi-stack machine.
3. **Word RAMs from multitape machines.** A function on lists of natural numbers computed by a
   deterministic multitape machine within $T(x)$ steps, on the binary codes of the lists, is
   computed by one word-RAM program within a fixed polynomial in $|x| + T(x)$ instructions, at
   every word length from a fixed polynomial in $|x| + T(x)$ on.
4. **Multitape machines from word RAMs.** A run of $t$ instructions of a fixed word-RAM program
   at word length $w$ is simulated by one deterministic multitape machine, given $w$ and the
   input, in a fixed polynomial in $|x| + w + t$ steps.
5. **Computable functions.** Every computable function $f\colon \mathbb N \to \mathbb N$ is
   computed by a deterministic multitape machine within $T(k)$ steps on input $k$, for a
   computable function $T$.
Statements 1–3 are proved here. Statements 4 and 5 are classical and cited: the simulation of
random-access machines by multitape Turing machines with polynomial overhead
(Cook and Reckhow), and the equivalence of Turing machines with partial recursive functions,
together with the computability of their running times.

# Implementation notes
* The single-tape machines are `Lax434930.MachineModels.SingleTape`, the model of the
  archive's `EXPTIME`, with halting and answer as in its definition.
* The multi-stack machines are mathlib's `Turing.FinTM2` in polynomial time,
  `Turing.TM2ComputableInPolyTime`, on `List Bool` with the identity encoding, as in the
  archive's many-one reductions `Lax429075.Reductions.ManyOne`.
* The word RAM is `Lax808846.Ram`, with the conventions of `Lax759944.RamPolytime`: the
  program runs on the length-prefixed tape `x.length :: x`, inputs are measured by their bit
  size `bitSize`, and a run at word length `w` is `RunsTo w p tape output t`.
* Multitape machines read lists of natural numbers in the code `encodeNats` of the binary
  encodings of graph pairs, and numbers in the code `encodeNat`.
* Statement 3 has the form of `Lax759944.TuringToRamGenericTime`, and statement 4 drops the
  restriction of `Lax759944.RamToTuringGenericTime` to a word length bounded by a fixed
  polynomial in the input size: the word length is an input of the simulating machine. This
  is needed for algorithms whose word length grows like $|x|^{f(k)}$, as in the class XP.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)
open Lax808846.Ram Lax759944.RamPolytime
open Lax759944.BinaryWordEncoding (bitSize)
open Lax434930.MachineModels Turing

namespace Lax119563.MachineTranslations

/-- **Single-tape machines** are simulated by deterministic multitape machines with linear
overhead: if the single-tape machine `M₀` halts on `w` within `T` steps in the configuration
`c`, then `M` decides within `C (T + |w| + 1)` steps whether `M₀` accepts. -/
axiom singleTape_simulation (M₀ : SingleTape) :
    ∃ M : Machine, Deterministic M ∧ ∃ C : ℕ, ∀ (w : List Bool) (T : ℕ) (c : TM0.Cfg M₀.Γ M₀.Q),
      Nonempty (StateTransition.EvalsToInTime (TM0.step M₀.transition)
        (TM0.init (w.map M₀.input)) (some c) T) →
      TM0.step M₀.transition c = none →
      DecidesWithin M w (M₀.accept c.q = true) (C * (T + w.length + 1))

/-- **Multi-stack machines.** A function on bit strings computed by a deterministic multitape
machine in polynomial time is computable in polynomial time by a multi-stack machine. -/
axiom tm2_of_polyTime {f : List Bool → List Bool} (R : Machine) (hR : Deterministic R)
    (C d : ℕ) (hf : ∀ x, ComputesWithin R x (f x) (C * x.length ^ d + C)) :
    Nonempty (TM2ComputableInPolyTime id id f)

/-- **Word RAMs from multitape machines.** A function on lists of natural numbers computed by
a deterministic multitape machine within `T x` steps is computed by one word-RAM program
within a fixed polynomial in `bitSize x + T x` instructions, at every word length from a fixed
polynomial in `bitSize x + T x` on. -/
axiom ram_of_machine {F : List ℕ → List ℕ} (R : Machine) (hR : Deterministic R)
    (T : List ℕ → ℕ) (hF : ∀ x, ComputesWithin R (encodeNats x) (encodeNats (F x)) (T x)) :
    ∃ (p : Program) (wordBound timeBound : Polynomial ℕ), ∀ (x : List ℕ) (w : ℕ),
      wordBound.eval (bitSize x + T x) ≤ w →
        ∃ t ≤ timeBound.eval (bitSize x + T x), RunsTo w p (x.length :: x) (F x) t

/-- **Multitape machines from word RAMs** (cited). A run of `t` instructions of the program
`p` at word length `w`, on the tape `x.length :: x` with output `out`, is simulated by one
deterministic multitape machine that reads `w` and `x`, within a fixed polynomial in
`bitSize x + w + t` steps. -/
axiom machine_of_ram (p : Program) :
    ∃ M : Machine, Deterministic M ∧ ∃ P : Polynomial ℕ, ∀ (x out : List ℕ) (w t : ℕ),
      FitsInWords w ((x.length :: x) ++ out) → RunsTo w p (x.length :: x) out t →
        ComputesWithin M (encodeNat w ++ encodeNats x) (encodeNats out)
          (P.eval (bitSize x + w + t))

/-- **Computable functions** (cited) are computed by deterministic multitape machines within a
computable running time. -/
axiom machine_of_computable {f : ℕ → ℕ} (hf : Computable f) :
    ∃ M : Machine, Deterministic M ∧ ∃ T : ℕ → ℕ, Computable T ∧
      ∀ k : ℕ, ComputesWithin M (encodeNat k) (encodeNat (f k)) (T k)

end Lax119563.MachineTranslations
