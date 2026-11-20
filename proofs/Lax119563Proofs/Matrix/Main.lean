import Lax119563Proofs.Matrix.Edges
import Lax119563Proofs.Compiler.Prog
import Lax119563Proofs.Compiler.P4SchSpec2
import Lax119563Proofs.Compiler.Bound

/-!
# The matrix compiler

The construction is `Compiler.compileM I`, the explicit matrix graphs with vertices in the
order of the compiler machine: it satisfies the game, size and edge clauses (`reGraph_spec`,
`Compiler/Clauses`), its encoding has length `O((S + 1) log (S + 2))`
(`Compiler.length_out_le_log`), and it is computed by the compiler program `prog p4Sch`
(`Compiler/Prog`, `Compiler/P4SchSpec2`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.ColoredGraphs Lax119563.PebbleGame Lax119563.DeterministicTime
open Lax119563.BinaryEncodings
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Matrix

/--
---
conclusion: Lax119563.MatrixCompiler.matrix_compiler
---
The construction is the pair of explicit matrix graphs, with vertices listed in the order
`ordL I` produced by the compiler machine and colors the position of the first vertex of a
class (`Compiler.compileM`): Spoiler follows a derivation of the conflict backwards through the
strips with row sweeps, Duplicator maintains seed descriptions with coefficient bits repaired in
an untouched repetition, the size bound counts the vertex list and the edge bound uses that
every edge contains a hub of degree at most three (`Compiler.reGraph_spec`). Colors and edge
endpoints are numbers below `3 |V|`, so the encoding has length `O((S + 1) log (S + 2))`
(`Compiler.length_out_le_log`). The construction time is witnessed by the counter-machine program
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
          (compile I).1.n + (compile I).2.n ≤ C * matrixSize I ∧
          (compile I).1.numEdges + (compile I).2.numEdges ≤
            3 * ((compile I).1.n + (compile I).2.n) ∧
          (encodeGraphPair (compile I).1 (compile I).2).length ≤
            C * (matrixSize I + 1) * (Nat.log 2 (matrixSize I + 2) + 1)) ∧
      (∃ M : Machine, Deterministic M ∧ ∃ C c : ℕ, ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ →
        ∀ I : ImplicitParitySystem k ℓ,
          ComputesWithin M (encodeSystem I) (encodeGraphPair (compile I).1 (compile I).2)
            (C * (bitLength I + matrixSize I) *
              Nat.log 2 (bitLength I + matrixSize I + 2) ^ c)) := by
  obtain ⟨M, hD, C, c, h⟩ := Lax119563Proofs.Compiler.machine_clause_of_schSpec
    (SCH := Lax119563Proofs.Compiler.p4Sch) (K := 400000)
    (fun _ hk _ hℓ I => Lax119563Proofs.Compiler.p4Sch_spec I hk hℓ)
  refine ⟨Lax119563Proofs.Compiler.compileM, ⟨3360, fun k hk => ⟨2 * k + stepConst k,
    fun ℓ _ I => ?_⟩⟩, ⟨M, hD, C, c, fun k hk ℓ hℓ I => ?_⟩⟩
  · obtain ⟨h1, h2, h3, h4⟩ := Lax119563Proofs.Compiler.reGraph_spec hk
      (Lax119563Proofs.Compiler.ordL I) (Lax119563Proofs.Compiler.ordL_perm I)
    refine ⟨h1, h2, h3.trans (Nat.mul_le_mul_right _ (by norm_num)), h4, ?_⟩
    rw [Lax119563Proofs.Compiler.encode_compileM]
    refine (Lax119563Proofs.Compiler.length_out_le_log I (by omega) 0).trans ?_
    rw [zero_add]
    calc 2 * (2 + 7 * (16 * matrixSize I)) * (2 * (Nat.log 2 (matrixSize I + 2) + 7) + 1)
        ≤ (224 * (matrixSize I + 1)) * (15 * (Nat.log 2 (matrixSize I + 2) + 1)) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  · rw [Lax119563Proofs.Compiler.encode_compileM]; exact h k hk ℓ hℓ I

end Lax119563Proofs.Matrix
