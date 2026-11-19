import Lax119563Proofs.Compiler.OutDesc

/-!
# The matrix compiler from the machine

`compileM I := (reGraph I (ordL I) 0, reGraph I (ordL I) 1)` satisfies the game, size and edge
clauses (`compileM_clauses`, from `reGraph_spec` and `ordL_perm`), and its encoding is
`encodeNats (gDesc I 0 ++ gDesc I 1)` (`encode_compileM`). Hence the concept statement follows
from a single machine computing `encodeNats (gDesc I 0 ++ gDesc I 1)` from `encodeSystem I`
within the bound (`matrix_compiler_of_machine`); the machine is item 4 of the plan.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.PebbleGame Lax119563.ImplicitSystemEncodings Lax119563.BinaryEncodings
open Lax119563.DeterministicTime Lax119563Proofs.Matrix
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Compiler

/-- The construction: the matrix graphs with vertices in the machine's order. -/
noncomputable def compileM {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) :
    ColoredGraph × ColoredGraph :=
  (reGraph I (ordL I) 0, reGraph I (ordL I) 1)

/-- The game, size and edge clauses. -/
theorem compileM_clauses :
    ∃ C : ℕ, ∀ k : ℕ, 3 ≤ k → ∃ Cₖ : ℕ, ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∀ I : ImplicitParitySystem k ℓ,
        (∀ τ : ℕ, I.conflictRound = τ →
          SpoilerWinsWithin (k + 1) (Cₖ * Λ I * (τ + 1)) (compileM I).1 (compileM I).2) ∧
        (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound →
          DuplicatorSurvives (k + 1) r (compileM I).1 (compileM I).2) ∧
        (compileM I).1.n + (compileM I).2.n ≤ C * sizeParameter I ∧
        (compileM I).1.numEdges + (compileM I).2.numEdges ≤
          3 * ((compileM I).1.n + (compileM I).2.n) :=
  ⟨32, fun k hk => ⟨2 * k + stepConst k, fun _ _ I =>
    reGraph_spec hk (ordL I) (ordL_perm I)⟩⟩

/-- The encoding of the construction is the list the machine emits. -/
theorem encode_compileM {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) :
    encodeGraphPair (compileM I).1 (compileM I).2 = encodeNats (gDesc I 0 ++ gDesc I 1) :=
  encodeGraphPair_eq I

/-- **Reduction of the concept to the machine.** -/
theorem matrix_compiler_of_machine
    (hM : ∃ M : Machine, Deterministic M ∧ ∃ C c : ℕ, ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∀ I : ImplicitParitySystem k ℓ,
        ComputesWithin M (encodeSystem I) (encodeNats (gDesc I 0 ++ gDesc I 1))
          (C * (bitLength I + sizeParameter I) *
            Nat.log 2 (bitLength I + sizeParameter I + 2) ^ c)) :
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
              Nat.log 2 (bitLength I + sizeParameter I + 2) ^ c)) := by
  obtain ⟨M, hD, C, c, h⟩ := hM
  refine ⟨compileM, compileM_clauses, M, hD, C, c, fun k hk ℓ hℓ I => ?_⟩
  rw [encode_compileM]
  exact h k hk ℓ hℓ I

end Lax119563Proofs.Compiler
