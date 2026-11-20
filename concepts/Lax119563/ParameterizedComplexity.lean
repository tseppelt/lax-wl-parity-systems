import Lax119563.BinaryEncodings
import Lax119563.DeterministicTime

/-!
---
title: Parameterized problems, XP and fpt-reductions
type: definition
---
We follow Flum and Grohe, with deterministic multitape Turing machines as the machine model.

* A **parameterized problem** is a pair $(L, \kappa)$ of a language
  $L \subseteq \{0, 1\}^*$ and a parameterization $\kappa\colon \{0, 1\}^* \to \mathbb N$
  that is computable in polynomial time.
* A function $f\colon \mathbb N \to \mathbb N$ is **computable** if a deterministic multitape
  Turing machine computes $f(k)$ from $k$.
* $(L, \kappa)$ belongs to **XP** if some machine decides $x \in L$ in time
  $f(\kappa(x)) \cdot (|x| + 1)^{f(\kappa(x))}$ for a computable $f$.
* An **fpt-reduction** from $(L, \kappa)$ to $(L', \kappa')$ is a map
  $R\colon \{0, 1\}^* \to \{0, 1\}^*$ such that
  1. $x \in L$ if and only if $R(x) \in L'$;
  2. $R$ is computed by a machine in time $f(\kappa(x)) \cdot (|x| + 1)^d$ for a computable
     $f$ and a constant $d$;
  3. $\kappa'(R(x)) \leq g(\kappa(x))$ for a computable $g$.
* For a class $\mathcal C$ of parameterized problems, $(L', \kappa')$ is
  **$\mathcal C$-hard** if every member of $\mathcal C$ fpt-reduces to it, and
  **$\mathcal C$-complete** if it moreover belongs to $\mathcal C$.

# Implementation notes
* Machines are the deterministic machines of `Lax119563.DeterministicTime`, numbers are
  given to them in the code `encodeNat` of the binary encodings of graph pairs, and deciding
  and computing within a number of steps are `DecidesWithin` and `ComputesWithin`.
* Computability is defined with the same machines, as in Flum and Grohe, rather than with
  mathlib's `Computable`; the two notions agree by the Church–Turing thesis, which is not
  needed here.
* Being parameterized (polynomial-time computable parameter) is part of membership in
  $\mathsf{XP}$, not of the type of parameterized problems, as in the archive's
  W-hierarchy (`Lax496464`).
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563.ParameterizedComplexity

/-- A parameterized problem: a language of bit strings with a parameterization. -/
structure ParameterizedProblem where
  /-- The language. -/
  L : Set (List Bool)
  /-- The parameterization. -/
  κ : List Bool → ℕ

/-- `f` is computable: a deterministic multitape machine computes `f k` from `k`. -/
def MachineComputable (f : ℕ → ℕ) : Prop :=
  ∃ M : Machine, Deterministic M ∧ ∀ k : ℕ, ∃ t : ℕ, ComputesWithin M (encodeNat k) (encodeNat (f k)) t

/-- The parameterization of `P` is computable in polynomial time. -/
def IsParameterized (P : ParameterizedProblem) : Prop :=
  ∃ M : Machine, Deterministic M ∧ ∃ C d : ℕ,
    ∀ x : List Bool, ComputesWithin M x (encodeNat (P.κ x)) (C * x.length ^ d + C)

/-- **XP**: the parameterized problems decided in time `f(κ x) · (|x| + 1)^{f(κ x)}` for a
computable `f`. -/
def XP : Set ParameterizedProblem :=
  {P | IsParameterized P ∧ ∃ M : Machine, Deterministic M ∧ ∃ f : ℕ → ℕ, MachineComputable f ∧
    ∀ x : List Bool, DecidesWithin M x (x ∈ P.L) (f (P.κ x) * (x.length + 1) ^ f (P.κ x))}

/-- `R` is an **fpt-reduction** from `P` to `Q`. -/
structure IsFptReduction (P Q : ParameterizedProblem) (R : List Bool → List Bool) : Prop where
  /-- Yes-instances go to yes-instances, and no-instances to no-instances. -/
  correct : ∀ x : List Bool, x ∈ P.L ↔ R x ∈ Q.L
  /-- `R` is computable in fpt-time. -/
  fpt_time : ∃ M : Machine, Deterministic M ∧ ∃ f : ℕ → ℕ, MachineComputable f ∧ ∃ d : ℕ,
    ∀ x : List Bool, ComputesWithin M x (R x) (f (P.κ x) * (x.length + 1) ^ d)
  /-- The new parameter is bounded by a computable function of the old one. -/
  param_bounded : ∃ g : ℕ → ℕ, MachineComputable g ∧ ∀ x : List Bool, Q.κ (R x) ≤ g (P.κ x)

/-- `P` fpt-reduces to `Q`. -/
def FptReduces (P Q : ParameterizedProblem) : Prop := ∃ R, IsFptReduction P Q R

/-- `Q` is `𝒞`-hard: every member of `𝒞` fpt-reduces to it. -/
def Hard (𝒞 : Set ParameterizedProblem) (Q : ParameterizedProblem) : Prop :=
  ∀ P ∈ 𝒞, FptReduces P Q

/-- `Q` is `𝒞`-complete: it belongs to `𝒞` and is `𝒞`-hard. -/
def Complete (𝒞 : Set ParameterizedProblem) (Q : ParameterizedProblem) : Prop :=
  Q ∈ 𝒞 ∧ Hard 𝒞 Q

end Lax119563.ParameterizedComplexity
