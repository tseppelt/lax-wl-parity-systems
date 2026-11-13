import Mathlib.Data.Nat.Log
import Lax119563.BinaryEncodings
import Lax119563.DeterministicTime
import Lax119563.WeisfeilerLeman

/-!
---
title: A quasi-linear reduction from deterministic time to k-WL Distinguishing
type: theorem
---
Fix an integer $s \geq 2$ and a deterministic multitape Turing machine $\mathcal M$ running in
time $O(n^s)$. Given $x \in \{0, 1\}^n$ with $n \geq 2$, one can construct colored graphs
$G_0(x), G_1(x)$ with $N = n (\log n)^{O(1)}$ vertices in total such that
$$\mathcal M \text{ accepts } x \iff (s + 1)\text{-WL distinguishes } G_0(x) \text{ and } G_1(x),$$
and the binary encoding of the pair can be computed from $x$ in time $n (\log n)^{O(1)}$ by a
deterministic multitape Turing machine. The implicit constants may depend on $\mathcal M$
and $s$; the logarithmic exponent is absolute.

In the paper, this is obtained by composing two steps: the simulation of deterministic time
by a register program with $s$ registers over an alphabet $\mathbb F_2^\ell$ of size
$\Theta_{\mathcal M, s}(n)$ with polylogarithmically many control locations and commands,
and the compilation of register programs into implicit parity systems with $s + 1$ blocks
and further, by the matrix compiler, into graph pairs.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563.TimeReduction

/-- **A quasi-linear reduction from deterministic time `O(n^s)` to `(s+1)`-WL
Distinguishing.** -/
axiom time_reduction : ∃ c : ℕ, ∀ s : ℕ, 2 ≤ s → ∀ M : Machine, Deterministic M →
    (∃ C₀ : ℕ, ∀ x : List Bool, (runOn M x (C₀ * x.length ^ s + C₀)).answer.isSome) →
    ∃ R : Machine, Deterministic R ∧ ∃ C : ℕ, ∀ x : List Bool, 2 ≤ x.length →
      ∃ G₀ G₁ : ColoredGraph,
        (Accepts M x ↔ Distinguishes (s + 1) G₀ G₁) ∧
        G₀.n + G₁.n ≤ C * x.length * Nat.log 2 x.length ^ c ∧
        ComputesWithin R x (encodeGraphPair G₀ G₁) (C * x.length * Nat.log 2 x.length ^ c)

end Lax119563.TimeReduction
