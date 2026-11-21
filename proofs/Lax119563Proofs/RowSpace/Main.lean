import Lax119563Proofs.RowSpace.Part1
import Lax119563Proofs.Stabilization.Part1

/-!
# The row-space compiler

The explicit pair `rsGraph I 0, rsGraph I 1` satisfies all claims of the row-space compiler;
the concept statement follows.
-/

open Lax119563.ImplicitParitySystems Lax119563.ColoredGraphs Lax119563.PebbleGame
open Lax119563.ColoredHomomorphisms Lax119563.ContradictionTrees

namespace Lax119563Proofs.RowSpace

/-- **The row-space compiler for the explicit construction.** For `k ≥ 3`, the graphs
`rsGraph I 0` and `rsGraph I 1` satisfy: (1) Spoiler wins within `spoilerConst k · (τ + 1)`
rounds if the conflict round is `τ`; (2) Duplicator survives `r` rounds whenever `r + 1 ≤ τ`;
(3) both graphs have `(names I).card ≤ 10 S` vertices; (4) every colored graph of treewidth at
most `k` distinguishing them by homomorphism counts yields a contradiction tree with at most
`5 |V(F)| + 1` nodes. -/
theorem rsGraph_spec {k ℓ : ℕ} (hk : 3 ≤ k) (I : ImplicitParitySystem k ℓ) :
    (∀ τ : ℕ, I.conflictRound = τ →
      SpoilerWinsWithin (k + 1) (spoilerConst k * (τ + 1)) (rsGraph I 0) (rsGraph I 1)) ∧
    (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound →
      DuplicatorSurvives (k + 1) r (rsGraph I 0) (rsGraph I 1)) ∧
    (∀ ε, (rsGraph I ε).n = (names I).card) ∧
    (names I).card ≤ 10 * Lax119563.RowSpaceCompiler.rowSpaceSize I ∧
    (∀ F : ColoredGraph, TreewidthAtMost F k → hom F (rsGraph I 0) ≠ hom F (rsGraph I 1) →
      HasContradictionWithin I.toParitySystem (5 * F.n + 1)) :=
  ⟨fun _ hτ => spoilerWins hk hτ,
    fun _ hr => duplicatorSurvives hk (Lax119563Proofs.Matrix.not_hasConflict_of_lt I hr),
    fun ε => rs_n ε, card_names_le hk I,
    fun F htw hne => by
      obtain ⟨T⟩ := oneVertexForest_of_treewidth htw
      exact pattern_tree hk T hne⟩

/--
---
conclusion: Lax119563.RowSpaceCompiler.rowspace_compiler
---
The explicit graphs `rsGraph I 0` and `rsGraph I 1` (vertices: class names with effective
labels, colors an injective code of the class) witness the row-space compiler with the
absolute constant `20` and `Cₖ = (4k + 1)(k + 2) + 6k`. Spoiler follows a derivation of the
conflict backwards, sweeping the `k + 2` stages of every strip with the mask vertices
(`spoilerWins`); Duplicator maintains seed descriptions whose masks are repaired in a stage
without pebbled mask class (`duplicatorSurvives`); the size bound counts the vertex classes and
labels, with `2^{rank B_e}` masks per stage (`card_names_le`). For item (4), a graph of
treewidth at most `k` has a one-vertex tree decomposition (Abramsky–Jakl–Paine,
`oneVertexForest_of_treewidth`); by the affine dichotomy it has no homomorphism to `G₁`, so the
tree-like linear system of exposed equations along the decomposition is unsolvable (local
realization), and it yields a contradiction tree (`pattern_tree`).
-/
theorem rowspace_compiler : ∃ C : ℕ, ∀ k : ℕ, 3 ≤ k → ∃ Cₖ : ℕ, ∀ ℓ : ℕ, 1 ≤ ℓ →
    ∀ I : ImplicitParitySystem k ℓ, ∃ G₀ G₁ : ColoredGraph,
      (∀ τ : ℕ, I.conflictRound = τ → SpoilerWinsWithin (k + 1) (Cₖ * (τ + 1)) G₀ G₁) ∧
      (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound → DuplicatorSurvives (k + 1) r G₀ G₁) ∧
      G₀.n + G₁.n ≤ C * Lax119563.RowSpaceCompiler.rowSpaceSize I ∧
      (∀ F : ColoredGraph, TreewidthAtMost F k → hom F G₀ ≠ hom F G₁ →
        HasContradictionWithin I.toParitySystem (5 * F.n + 1)) := by
  refine ⟨20, fun k hk => ⟨spoilerConst k, fun ℓ _ I => ?_⟩⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := rsGraph_spec hk I
  refine ⟨rsGraph I 0, rsGraph I 1, h1, h2, ?_, h5⟩
  rw [h3 0, h3 1]
  omega

end Lax119563Proofs.RowSpace
