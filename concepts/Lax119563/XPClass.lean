import Mathlib.Computability.Partrec
import Lax496464.WH_A2_FptReductions

/-!
---
title: The class XP
type: definition
---
A parameterized problem $(P, \kappa)$ belongs to $\mathrm{XP}$ if it is decided by an
algorithm in time
$$f(\kappa(x)) \cdot |x|^{f(\kappa(x))}$$
for a computable function $f$ (Flum and Grohe), i.e. in polynomial time for every fixed
value of the parameter, with the degree of the polynomial depending on the parameter.

# Implementation notes
The definition follows the conventions of the archive's fixed-parameter time on the word RAM
(`Lax496464.WH_A1_FptTime`), with the bound $f(k) \cdot (|x| + 1)^{f(k)}$ in place of
$f(k) \cdot (|x| + 1)^d$:
* the machine is the word RAM `Lax808846.Ram`, run on the length-prefixed tape `x.length :: x`;
* the input size $|x|$ is the bit size `Lax759944.BinaryWordEncoding.bitSize`;
* the bound $B$ serves as the time bound and as the least admissible word length: the program
  halts with the correct answer within $B$ instructions at every word length $w \geq B$, and
  the tape and the answer fit into words of length $B$;
* as for `FPT` (`Lax496464.WH_A2_FptReductions.FPT`), the problem must be parameterized (its
  parameter is computable in polynomial time), and the program writes `[1]` on yes-instances
  and `[0]` on no-instances of the domain.
-/

open Lax808846.Ram Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax888481.ParameterizedComplexity (Problem)
open Lax496464.WH_A2_FptReductions (IsParameterized)

namespace Lax119563.XPClass

/-- The XP bound `f(k) · (n + 1)^{f(k)}`, for a parameter value `k` and an input size `n`. -/
def xpBound (f : ℕ → ℕ) (k n : ℕ) : ℕ := f k * (n + 1) ^ f k

/-- On every word `x` of `D`, one program computes `F x` from the tape `x.length :: x` within
`B = f(κ x) · (bitSize x + 1)^{f(κ x)}` instructions at every word length `w ≥ B`, and the tape
and the output fit in words of length `B`, for a computable `f`. -/
def XPTimeOn (D : Set (List ℕ)) (κ : List ℕ → ℕ) (F : List ℕ → List ℕ) : Prop :=
  ∃ (p : Program) (f : ℕ → ℕ), Computable f ∧ ∀ x ∈ D,
    FitsInWords (xpBound f (κ x) (bitSize x)) ((x.length :: x) ++ F x) ∧
      ∀ w : ℕ, xpBound f (κ x) (bitSize x) ≤ w →
        ∃ t ≤ xpBound f (κ x) (bitSize x), RunsTo w p (x.length :: x) (F x) t

open Classical in
/-- **XP**: the parameterized problems decided in time `f(k) · |x|^{f(k)}` for a computable
`f`, the program writing `[1]` on yes-instances and `[0]` on no-instances. -/
def XP : Set Problem :=
  {P | IsParameterized P ∧ XPTimeOn P.Domain P.param fun x => if P.Yes x then [1] else [0]}

end Lax119563.XPClass
