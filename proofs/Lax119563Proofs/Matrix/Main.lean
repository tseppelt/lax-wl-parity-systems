import Lax119563Proofs.Matrix.Edges

/-!
# The matrix compiler

The explicit pair `matrixGraph I 0, matrixGraph I 1` satisfies all claims of the matrix
compiler; the concept statement follows.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.PebbleGame

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
The explicit graphs `matrixGraph I 0` and `matrixGraph I 1` (vertices listed by
`vertexList I`, colors the position of the first vertex of a class) witness the matrix
compiler with the absolute constant `32` and `Cₖ = 2k + (4k + 1)(k + 1) + 8k`. Spoiler follows
a derivation of the conflict backwards through the strips with row sweeps (`spoilerWins`);
Duplicator maintains seed descriptions with coefficient bits repaired in an untouched
repetition (`duplicatorSurvives`); the size bound counts the vertex list and the edge bound
uses that every edge contains a hub of degree at most three.
-/
theorem matrix_compiler : ∃ C : ℕ, ∀ k : ℕ, 3 ≤ k → ∃ Cₖ : ℕ, ∀ ℓ : ℕ, 1 ≤ ℓ →
    ∀ I : ImplicitParitySystem k ℓ, ∃ G₀ G₁ : ColoredGraph,
      (∀ τ : ℕ, I.conflictRound = τ →
        SpoilerWinsWithin (k + 1) (Cₖ * Λ I * (τ + 1)) G₀ G₁) ∧
      (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound → DuplicatorSurvives (k + 1) r G₀ G₁) ∧
      G₀.n + G₁.n ≤ C * sizeParameter I ∧
      G₀.numEdges + G₁.numEdges ≤ 3 * (G₀.n + G₁.n) := by
  refine ⟨32, fun k hk => ⟨2 * k + stepConst k, fun ℓ _ I => ?_⟩⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := matrixGraph_spec hk I
  refine ⟨matrixGraph I 0, matrixGraph I 1, h1, h2, ?_, ?_⟩
  · show nV I + nV I ≤ 32 * sizeParameter I
    omega
  · have := h5 0
    have := h5 1
    show _ ≤ 3 * (nV I + nV I)
    omega

end Lax119563Proofs.Matrix
