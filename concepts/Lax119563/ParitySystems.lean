import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Defs

/-!
---
title: Parity systems and unit propagation
type: definition
---
A *parity system* $\mathcal P = (V, \mathcal H, K_0)$ consists of a set $V$ of variables, each
taking values in $\mathbb F_2$, a set $\mathcal H$ of homogeneous linear equations, and a set
$K_0 \subseteq V \times \mathbb F_2$ of *initial facts*. Every equation involves two or three
distinct variables; formally, $\mathcal H \subseteq \binom{V}{2} \cup \binom{V}{3}$, where an
equation $h$ states $\sum_{X \in h} X = 0$.

*Unit propagation* infers facts of the form $X = b$ only. For an equation
$h \colon X + Y_1 + \dots + Y_m = 0$ with $m \in \{1, 2\}$, the rule infers
$X = b_1 + \dots + b_m$ from $Y_1 = b_1, \dots, Y_m = b_m$. The facts $K_r$ known after
round $r$ are given by
$$K_{r+1} = K_r \cup \bigl\{(X, b_1 + \dots + b_m) \bigm| \{X, Y_1, \dots, Y_m\} \in \mathcal H,\
(Y_1, b_1), \dots, (Y_m, b_m) \in K_r\bigr\}.$$

A *conflict* occurs when both $X = 0$ and $X = 1$ have been inferred for some variable $X$.
The *conflict round* $\tau(\mathcal P) \in \mathbb N \cup \{\infty\}$ is the first round $r$
such that $K_r$ contains a conflict, or $\infty$ if no conflict occurs.
-/

namespace Lax119563.ParitySystems

/-- A *parity system* with variables of type `V`: homogeneous equations over `𝔽₂` in two or
three distinct variables, each given by its set of variables, and initial facts. -/
structure ParitySystem (V : Type*) where
  /-- The equations; `h` stands for `∑_{X ∈ h} X = 0`. -/
  equations : Set (Finset V)
  /-- Every equation involves two or three variables. -/
  card_equation : ∀ h ∈ equations, h.card = 2 ∨ h.card = 3
  /-- The initial facts `K₀`. -/
  initial : Set (V × ZMod 2)

namespace ParitySystem

variable {V : Type*} [DecidableEq V]

/-- The set `K_r` of facts known after round `r` of unit propagation. In round `r + 1`, an
equation `h` and a variable `X ∈ h` infer `X = ∑_{Y ∈ h \ {X}} b_Y` from known facts
`Y = b_Y` for all other variables `Y ∈ h`. -/
def known (P : ParitySystem V) : ℕ → Set (V × ZMod 2)
  | 0 => P.initial
  | r + 1 => P.known r ∪
      {f | ∃ h ∈ P.equations, f.1 ∈ h ∧ ∃ b : V → ZMod 2,
        (∀ Y ∈ h, Y ≠ f.1 → (Y, b Y) ∈ P.known r) ∧ f.2 = ∑ Y ∈ h.erase f.1, b Y}

/-- `K_r` contains a conflict. -/
def HasConflict (P : ParitySystem V) (r : ℕ) : Prop :=
  ∃ X, (X, 0) ∈ P.known r ∧ (X, 1) ∈ P.known r

/-- The conflict round `τ(P)`: the first round with a conflict, or `⊤ = ∞` if none occurs. -/
noncomputable def conflictRound (P : ParitySystem V) : ℕ∞ :=
  ⨅ (r : ℕ) (_ : P.HasConflict r), (r : ℕ∞)

end ParitySystem

end Lax119563.ParitySystems
