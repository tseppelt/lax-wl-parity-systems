import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Log
import Lax119563.ColoredGraphs
import Lax119563.DeterministicTime
import Lax119563.ImplicitParitySystems
import Lax119563.ImplicitSystemEncodings
import Lax119563.PebbleGame

/-!
---
title: The matrix compiler
type: theorem
---
Let $k \geq 3$ and $\ell \geq 1$, and let $\mathcal I = (W, \mathfrak C, (\mathfrak C_v)_{v \in W},
\mathcal E, \iota)$ be an implicit parity system with coordinates
$\mathfrak C = [k] \times \mathbb F_2^\ell$ and conflict round $\tau = \tau(\mathcal I)$.
Then there are colored graphs $\widetilde G_0, \widetilde G_1$, constructed from $\mathcal I$, such
that:

1. If $\tau < \infty$, then Spoiler wins the bijective pebble game on
   $(\widetilde G_0, \widetilde G_1)$ with $k + 1$ pebbles in $O_k(\Lambda(\tau + 1))$ rounds.
2. Duplicator survives the bijective pebble game on $(\widetilde G_0, \widetilde G_1)$ with
   $k + 1$ pebbles for $\tau - 1$ rounds, or indefinitely if $\tau = \infty$.
3. With an absolute constant, $\widetilde N = |V(\widetilde G_0)| + |V(\widetilde G_1)| = O(S)$,
   where $S = \sum_{v \in W} |\mathfrak C_v| + (k + 1) \sum_{e \in \mathcal E}
   \operatorname{nnz}(B_e)$, and the two graphs have at most $3 \widetilde N$ edges.
4. The binary encoding of the pair $(\widetilde G_0, \widetilde G_1)$ can be computed from the
   binary encoding of $\mathcal I$ by a deterministic multitape Turing machine in time
   $\widetilde O(H + S)$, where $H$ is the bit length of $\mathcal I$ and $\widetilde O$
   suppresses a fixed power of $\log(H + S + 2)$. The machine and all constants are absolute;
   in particular $k$ and $\ell$ are part of the input.

Here $B \in \mathbb F_2^{(k - 1 + \ell) \times \mathfrak C}$ is the check matrix of the code of
codewords whose blocks have equal parity and whose block coordinates sum to zero: its rows
are the $k - 1$ block-parity checks comparing blocks $1, \dots, k - 1$ with block $k$,
followed by the $\ell$ checksum checks for the sum of the block coordinates. For a schema $e$,
$B_e$ is obtained from $B$ by restricting to the columns in $\mathfrak C_e$ and deleting zero
rows; $m_e$ is its number of rows and $\operatorname{nnz}(B_e)$ its number of nonzero entries.
Finally, $\Lambda = 1 + \max(\{0\} \cup \{m_e : e \in \mathcal E\})$.

# Implementation notes

The paper states this theorem for the explicit graph construction of the matrix compiler,
together with its size bound and construction time (Lemma "Matrix size"). Here the
construction is an unspecified function `compile` from implicit parity systems to graph
pairs; its properties are the game clauses, the size bounds, and that a single deterministic
machine computes it within $C (H + S) \log^c (H + S + 2)$ steps, where $C$ and $c$ are absolute.
Only the constant of the round bound may depend on $k$.

Since $k$ is part of the input of the machine, the statement serves both the quasi-linear
reduction for fixed $k$ and polynomial-time reductions in which $k$ grows with the input.
-/

open Lax119563.ColoredGraphs Lax119563.PebbleGame Lax119563.ImplicitParitySystems
  Lax119563.ImplicitSystemEncodings Lax119563.BinaryEncodings Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

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
/-- The number `m_e` of rows of `B_e`: rows of `B` that are nonzero on `ℭ_e`. -/
noncomputable def numRows {w : ℕ} (e : Schema k ℓ w) : ℕ :=
  (Finset.univ.filter fun row => ∃ c ∈ e.domain, checkMatrix k ℓ row c ≠ 0).card

open Classical in
/-- The number `nnz(B_e)` of nonzero entries of `B_e`. -/
noncomputable def nnz {w : ℕ} (e : Schema k ℓ w) : ℕ :=
  ((Finset.univ ×ˢ e.domain).filter fun x => checkMatrix k ℓ x.1 x.2 ≠ 0).card

/-- `Λ = 1 + max ({0} ∪ {m_e : e ∈ 𝓔})`. -/
noncomputable def Λ (I : ImplicitParitySystem k ℓ) : ℕ :=
  1 + (I.schemas.map numRows).foldr max 0

/-- The size parameter `S = ∑_v |ℭ_v| + (k+1) ∑_e nnz(B_e)`. -/
noncomputable def matrixSize (I : ImplicitParitySystem k ℓ) : ℕ :=
  ∑ v, (I.domain v).card + (k + 1) * (I.schemas.map nnz).sum

/-- **The matrix compiler.** There is a construction `compile` of graph pairs from implicit
parity systems such that, for `k ≥ 3`, the bijective `(k+1)`-pebble game on the pair follows
unit propagation: Spoiler wins in `O_k(Λ(τ+1))` rounds if a conflict occurs in round `τ`, and
Duplicator survives `τ - 1` rounds. The graphs have `O(S)` vertices and at most three times
as many edges as vertices. A single deterministic machine computes the encoding of the pair
from the encoding of the system in time `O((H + S) log^c (H + S + 2))`. -/
axiom matrix_compiler :
    ∃ compile : ∀ {k ℓ : ℕ}, ImplicitParitySystem k ℓ → ColoredGraph × ColoredGraph,
      (∃ C : ℕ, ∀ k : ℕ, 3 ≤ k → ∃ Cₖ : ℕ, ∀ ℓ : ℕ, 1 ≤ ℓ →
        ∀ I : ImplicitParitySystem k ℓ,
          (∀ τ : ℕ, I.conflictRound = τ →
            SpoilerWinsWithin (k + 1) (Cₖ * Λ I * (τ + 1)) (compile I).1 (compile I).2) ∧
          (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound →
            DuplicatorSurvives (k + 1) r (compile I).1 (compile I).2) ∧
          (compile I).1.n + (compile I).2.n ≤ C * matrixSize I ∧
          (compile I).1.numEdges + (compile I).2.numEdges ≤
            3 * ((compile I).1.n + (compile I).2.n)) ∧
      (∃ M : Machine, Deterministic M ∧ ∃ C c : ℕ, ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ →
        ∀ I : ImplicitParitySystem k ℓ,
          ComputesWithin M (encodeSystem I) (encodeGraphPair (compile I).1 (compile I).2)
            (C * (bitLength I + matrixSize I) *
              Nat.log 2 (bitLength I + matrixSize I + 2) ^ c))

end Lax119563.MatrixCompiler
