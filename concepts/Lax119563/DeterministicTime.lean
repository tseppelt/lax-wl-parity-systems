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
moves each head by at most one cell. Tapes are indexed by the integers; initially all heads
are at position zero, the first tape (tape $0$) contains the binary input $x$ at positions
$0, \dots, |x| - 1$, and all other cells are blank. Each transition, including the halting
transition, takes one step, and halting returns a bit.

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
-/

open Lax489179.TuringMachine

namespace Lax119563.DeterministicTime

/-- The configuration of `M` after `t` steps on input `x`. -/
def runOn (M : Machine) (x : List Bool) (t : ℕ) : Config M :=
  run M t (fun _ => false) (init M x)

/-- `M` decides `P` on input `x` within `t` steps: it halts within `t` steps and returns
`true` exactly when `P` holds. -/
def DecidesWithin (M : Machine) (x : List Bool) (P : Prop) (t : ℕ) : Prop :=
  ∃ b, (runOn M x t).answer = some b ∧ (b = true ↔ P)

/-- `M` accepts `x`: it halts on `x` and returns `true`. -/
def Accepts (M : Machine) (x : List Bool) : Prop :=
  ∃ t, (runOn M x t).answer = some true

/-- `M` computes `y` from `x` within `t` steps: it halts within `t` steps, and then tape `0`
holds `y` in the layout of an input. -/
def ComputesWithin (M : Machine) (x y : List Bool) (t : ℕ) : Prop :=
  (runOn M x t).answer.isSome ∧ (runOn M x t).tape 0 = (init M y).tape 0

/-- The language `L` is decidable in time `O(f(n))` by a deterministic multitape Turing
machine. -/
def DecidableInTime (L : Set (List Bool)) (f : ℕ → ℝ) : Prop :=
  ∃ M : Machine, Deterministic M ∧ ∃ C : ℕ,
    ∀ x : List Bool, DecidesWithin M x (x ∈ L) ⌊C * f x.length + C⌋₊

end Lax119563.DeterministicTime
