import Mathlib.Data.Nat.Log
import Lax119563.BinaryEncodings
import Lax119563.DeterministicTime
import Lax119563.ImplicitParitySystems
import Lax119563.ImplicitSystemEncodings

/-!
---
title: Packed implicit parity systems for deterministic computations
type: theorem
---
Let $\mathcal M$ be a deterministic multitape Turing machine, $x \in \{0, 1\}^n$ an input with
$n \geq 2$, and $T = 2^h$ a time horizon with $h \geq 2$ and $n \leq T$. For
$2 \leq s \leq h + 2$ put
$$\ell = \max\left\{\lceil \log_2 (n + 2) \rceil, \left\lceil \frac{h + 2}{s} \right\rceil\right\},
\qquad Q = 2^\ell.$$
There is an implicit parity system with $k = s + 1$ coordinate blocks over $\mathbb F_2^\ell$
and $O_{\mathcal M}((h + 1)^2)$ locations and schemas that reaches a conflict if and only if
$\mathcal M$ accepts $x$ within $T$ steps. Its binary encoding can be constructed in time
$s Q (h + 1)^{O(1)}$ by a deterministic multitape Turing machine. The polynomial exponent is
absolute, and the constants may depend on $\mathcal M$.

The system arises from a recursive simulation of deterministic computations due to Koucký
(Shalunov, Appendix B): each
recursive call simulates a time interval on a window of the tapes, the calls of one depth
share their locations, and the addresses, packed into the $s$ data blocks, encode the call
path and the position in the window.

# Implementation notes
* The system is a function `sys x h s` of the input, the horizon exponent and the number of
  data blocks, with $k = s + 1$ blocks of width $\ell$ = `packedWidth |x| h s`.
* The paper simulates exactly $T$ steps. Here the equivalence is stated for machines that
  halt on $x$ within $T$ steps, the only case used: then the system reaches a conflict iff
  $\mathcal M$ accepts $x$.
* One deterministic machine, depending on $\mathcal M$ only, computes the encoding of the
  system from the code of the list $h, s$ followed by $x$, within $C s Q (h + 1)^c$ steps,
  where $c$ is absolute.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime
  Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563.PackedRepresentation

/-- The block width `ℓ = max(⌈log₂(n + 2)⌉, ⌈(h + 2)/s⌉)`. -/
def packedWidth (n h s : ℕ) : ℕ := max (Nat.clog 2 (n + 2)) ((h + 1 + s) / s)

/-- **Packed representation.** For a deterministic machine `M` there are implicit parity
systems `sys x h s` with `s + 1` blocks of width `packedWidth |x| h s` and `O((h+1)^2)`
locations and schemas that reach a conflict iff `M` accepts `x` (if `M` halts on `x` within
`2^h` steps), and one machine computes their encodings in time `s 2^ℓ (h+1)^{O(1)}`. -/
axiom packed_representation : ∃ c : ℕ, ∀ M : Machine, Deterministic M →
    ∃ sys : (x : List Bool) → (h s : ℕ) →
        ImplicitParitySystem (s + 1) (packedWidth x.length h s),
      ∃ C : ℕ,
        (∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s →
          s ≤ h + 2 →
            (HaltsWithin M x (2 ^ h) →
              ((sys x h s).conflictRound < ⊤ ↔ Accepts M x)) ∧
            (sys x h s).numLocations ≤ C * (h + 1) ^ 2 ∧
            (sys x h s).schemas.length ≤ C * (h + 1) ^ 2) ∧
        ∃ R : Machine, Deterministic R ∧
          ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s →
            s ≤ h + 2 →
              ComputesWithin R (encodeNats [h, s] ++ x) (encodeSystem (sys x h s))
                (C * s * 2 ^ packedWidth x.length h s * (h + 1) ^ c)

end Lax119563.PackedRepresentation
