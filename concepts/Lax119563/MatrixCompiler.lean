import Mathlib.Data.Matrix.Basic
import Lax119563.ColoredGraphs
import Lax119563.ImplicitParitySystems
import Lax119563.PebbleGame

/-!
---
title: The matrix compiler
type: theorem
---
Let $k \geq 3$ and $\ell \geq 1$, and let $\mathcal I = (W, \mathfrak C, (\mathfrak C_v)_{v \in W},
\mathcal E, \iota)$ be an implicit parity system with coordinates
$\mathfrak C = [k] \times \mathbb F_2^\ell$ and conflict round $\tau = \tau(\mathcal I)$.
Then there are colored graphs $\widetilde G_0, \widetilde G_1$ such that:

1. If $\tau < \infty$, then Spoiler wins the bijective pebble game on
   $(\widetilde G_0, \widetilde G_1)$ with $k + 1$ pebbles in $O_k(\Lambda(\tau + 1))$ rounds.
2. Duplicator survives the bijective pebble game on $(\widetilde G_0, \widetilde G_1)$ with
   $k + 1$ pebbles for $\tau - 1$ rounds, or indefinitely if $\tau = \infty$.
3. With an absolute constant, $\widetilde N = |V(\widetilde G_0)| + |V(\widetilde G_1)| = O(S)$,
   where $S = \sum_{v \in W} |\mathfrak C_v| + (k + 1) \sum_{e \in \mathcal E}
   \operatorname{nnz}(B_e)$, and the two graphs have at most $3 \widetilde N$ edges.

Here $B \in \mathbb F_2^{(k - 1 + \ell) \times \mathfrak C}$ is the check matrix of the code of
codewords whose blocks have equal parity and whose block coordinates sum to zero: its rows
are the $k - 1$ block-parity checks comparing blocks $1, \dots, k - 1$ with block $k$,
followed by the $\ell$ checksum checks for the sum of the block coordinates. For a schema $e$,
$B_e$ is obtained from $B$ by restricting to the columns in $\mathfrak C_e$ and deleting zero
rows; $m_e$ is its number of rows and $\operatorname{nnz}(B_e)$ its number of nonzero entries.
Finally, $\Lambda = 1 + \max(\{0\} \cup \{m_e : e \in \mathcal E\})$.

# Implementation notes

The paper states this theorem for the explicit graph construction of the matrix compiler,
together with its size bound; here the graphs are asserted to exist. The constant of the
size bound is absolute, while the constant of the round bound may depend on $k$.
-/

open Lax119563.ColoredGraphs Lax119563.PebbleGame Lax119563.ImplicitParitySystems

namespace Lax119563.MatrixCompiler

variable {k ℓ : ℕ}

/-- The check matrix `B`. Row `inl i` is the block-parity check comparing block `i` with the
last block; row `inr t` is the checksum check of bit `t` of the block coordinates. -/
def checkMatrix (k ℓ : ℕ) : Matrix (Fin (k - 1) ⊕ Fin ℓ) (Coord k ℓ) (ZMod 2) :=
  Matrix.of fun row c =>
    match row with
    | .inl i => if (c.1 : ℕ) = i ∨ (c.1 : ℕ) = k - 1 then 1 else 0
    | .inr t => c.2 t

open Classical in
/-- The number `m_e` of rows of `B_e`: rows of `B` that are nonzero on `𝔠_e`. -/
noncomputable def numRows {w : ℕ} (e : Schema k ℓ w) : ℕ :=
  (Finset.univ.filter fun row => ∃ c ∈ e.domain, checkMatrix k ℓ row c ≠ 0).card

open Classical in
/-- The number `nnz(B_e)` of nonzero entries of `B_e`. -/
noncomputable def nnz {w : ℕ} (e : Schema k ℓ w) : ℕ :=
  ((Finset.univ ×ˢ e.domain).filter fun x => checkMatrix k ℓ x.1 x.2 ≠ 0).card

/-- `Λ = 1 + max ({0} ∪ {m_e : e ∈ 𝓔})`. -/
noncomputable def Λ (I : ImplicitParitySystem k ℓ) : ℕ :=
  1 + (I.schemas.map numRows).foldr max 0

/-- The size parameter `S = ∑_v |𝔠_v| + (k+1) ∑_e nnz(B_e)`. -/
noncomputable def sizeParameter (I : ImplicitParitySystem k ℓ) : ℕ :=
  ∑ v, (I.domain v).card + (k + 1) * (I.schemas.map nnz).sum

/-- **The matrix compiler.** Every implicit parity system with `k ≥ 3` blocks compiles to a
pair of colored graphs on which the bijective `(k+1)`-pebble game follows unit propagation:
Spoiler wins in `O_k(Λ(τ+1))` rounds if a conflict occurs in round `τ`, and Duplicator
survives `τ - 1` rounds. The graphs have `O(S)` vertices and at most three times as many
edges as vertices. -/
axiom matrix_compiler : ∃ C : ℕ, ∀ k : ℕ, 3 ≤ k → ∃ Cₖ : ℕ, ∀ ℓ : ℕ, 1 ≤ ℓ →
    ∀ I : ImplicitParitySystem k ℓ, ∃ G₀ G₁ : ColoredGraph,
      (∀ τ : ℕ, I.conflictRound = τ →
        SpoilerWinsWithin (k + 1) (Cₖ * Λ I * (τ + 1)) G₀ G₁) ∧
      (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound → DuplicatorSurvives (k + 1) r G₀ G₁) ∧
      G₀.n + G₁.n ≤ C * sizeParameter I ∧
      G₀.numEdges + G₁.numEdges ≤ 3 * (G₀.n + G₁.n)

end Lax119563.MatrixCompiler
