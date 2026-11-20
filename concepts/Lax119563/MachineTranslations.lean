import Mathlib.Computability.TuringMachine.Computable
import Lax434930.ExponentialTime
import Lax119563.BinaryEncodings
import Lax119563.DeterministicTime

/-!
---
title: Translations between machine models
type: theorem
---
Our reductions are deterministic multitape Turing machines, while the archive's standard
classes $\mathsf{EXPTIME}$ and polynomial-time many-one reductions are defined with
single-tape and multi-stack machines. Two simulations translate between them.
1. **Single-tape machines.** A single-tape machine halting within $T$ steps on an input of
   length $n$ is simulated by a deterministic multitape machine in $O(T + n)$ steps, with the
   same answer.
2. **Multi-stack machines.** A function computed by a deterministic multitape machine in
   polynomial time is computable in polynomial time by a multi-stack machine.

# Implementation notes
* The single-tape machines are `Lax434930.MachineModels.SingleTape`, the model of the
  archive's `EXPTIME`, with halting and answer as in its definition.
* The multi-stack machines are mathlib's `Turing.FinTM2` in polynomial time,
  `Turing.TM2ComputableInPolyTime`, on `List Bool` with the identity encoding, as in the
  archive's many-one reductions `Lax429075.Reductions.ManyOne`.
-/

open Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)
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
      DecidesExactlyWithin M w (M₀.accept c.q = true) (C * (T + w.length + 1))

/-- **Multi-stack machines.** A function on bit strings computed by a deterministic multitape
machine in polynomial time is computable in polynomial time by a multi-stack machine. -/
axiom tm2_of_polyTime {f : List Bool → List Bool} (R : Machine) (hR : Deterministic R)
    (C d : ℕ) (hf : ∀ x, ComputesWithin R x (f x) (C * (x.length + 1) ^ d)) :
    Nonempty (TM2ComputableInPolyTime id id f)

end Lax119563.MachineTranslations
