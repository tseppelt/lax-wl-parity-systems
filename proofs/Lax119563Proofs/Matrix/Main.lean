import Lax119563Proofs.Matrix.Edges
import Lax119563Proofs.Compiler.Prog
import Lax119563Proofs.Compiler.P4SchSpec2

/-!
# The matrix compiler

The explicit pair `matrixGraph I 0, matrixGraph I 1` satisfies the combinatorial claims of the
matrix compiler (`matrixGraph_spec`); the concept statement, including the construction time,
follows from the compiler program `prog p4Sch` (`Compiler/Prog`, `Compiler/P4SchSpec2`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.ColoredGraphs Lax119563.PebbleGame Lax119563.DeterministicTime
open Lax119563.BinaryEncodings
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Matrix

/-- **The matrix compiler for the explicit construction.** For `k ≥ 3`, the graphs
`matrixGraph I 0` and `matrixGraph I 1` satisfy: (I) Spoiler wins within
`(2k + stepConst k) · Λ · (τ + 1)` rounds if the conflict round is `τ`; (II) Duplicator survives
`r` rounds whenever `r + 1 ≤ τ`; both graphs have `nV I ≤ 16 S` vertices and at most
`3 · nV I` edges. -/
theorem matrixGraph_spec {k ℓ : ℕ} (hk : 3 ≤ k) (I : ImplicitParitySystem k ℓ) :
    (∀ τ : ℕ, I.conflictRound = τ →
      SpoilerWinsWithin (k + 1) ((2 * k + stepConst k) * Λ I * (τ + 1))
        (matrixGraph I 0) (matrixGraph I 1)) ∧
    (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound →
      DuplicatorSurvives (k + 1) r (matrixGraph I 0) (matrixGraph I 1)) ∧
    (∀ ε, (matrixGraph I ε).n = nV I) ∧
    nV I ≤ 16 * sizeParameter I ∧
    (∀ ε, (matrixGraph I ε).numEdges ≤ 3 * nV I) :=
  ⟨fun _ hτ => spoilerWins (by omega) hτ,
    fun _ hr => duplicatorSurvives (by omega) (not_hasConflict_of_lt I hr),
    fun _ => rfl, card_vertexList_le (by omega), numEdges_le⟩

/--
---
conclusion: Lax119563.MatrixCompiler.matrix_compiler
---
The construction is the pair of explicit graphs `matrixGraph I 0`, `matrixGraph I 1` (vertices
listed by `vertexList I`, colors the position of the first vertex of a class): Spoiler follows a
derivation of the conflict backwards through the strips with row sweeps, Duplicator maintains
seed descriptions with coefficient bits repaired in an untouched repetition, the size bound
counts the vertex list and the edge bound uses that every edge contains a hub of degree at most
three (`matrixGraph_spec`). The construction time is witnessed by the counter-machine program
`prog p4Sch` (`Compiler/Prog`): the passes `P0`–`P3` compute the location and schema data
and the answers of the join, `P4` emits both graph descriptions, its schema edge part
`p4Sch` meeting the interface `SchSpec` with linear cost (`p4Sch_spec`); the program is
compiled to a Turing machine running in time `O((H + S) log³ (H + S + 2))`.
-/
theorem matrix_compiler :
    ∃ compile : ∀ {k ℓ : ℕ}, ImplicitParitySystem k ℓ → ColoredGraph × ColoredGraph,
      (∃ C : ℕ, ∀ k : ℕ, 3 ≤ k → ∃ Cₖ : ℕ, ∀ ℓ : ℕ, 1 ≤ ℓ →
        ∀ I : ImplicitParitySystem k ℓ,
          (∀ τ : ℕ, I.conflictRound = τ →
            SpoilerWinsWithin (k + 1) (Cₖ * Λ I * (τ + 1)) (compile I).1 (compile I).2) ∧
          (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound →
            DuplicatorSurvives (k + 1) r (compile I).1 (compile I).2) ∧
          (compile I).1.n + (compile I).2.n ≤ C * sizeParameter I ∧
          (compile I).1.numEdges + (compile I).2.numEdges ≤
            3 * ((compile I).1.n + (compile I).2.n)) ∧
      (∃ M : Machine, Deterministic M ∧ ∃ C c : ℕ, ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ →
        ∀ I : ImplicitParitySystem k ℓ,
          ComputesWithin M (encodeSystem I) (encodeGraphPair (compile I).1 (compile I).2)
            (C * (bitLength I + sizeParameter I) *
              Nat.log 2 (bitLength I + sizeParameter I + 2) ^ c)) :=
  Lax119563Proofs.Compiler.matrix_compiler_of_schSpec (SCH := Lax119563Proofs.Compiler.p4Sch)
    (K := 400000) (fun _ hk _ hℓ I => Lax119563Proofs.Compiler.p4Sch_spec I hk hℓ)

end Lax119563Proofs.Matrix
