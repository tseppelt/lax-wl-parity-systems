import Lax119563Proofs.Stabilization.Defs

/-!
# Stabilization bound: shared definitions and cross-track interface

Weak chains (the `A`-sequences of Döring–Neuen, without strictness) and the statements that
one work track provides to another. The `sorry`s here are placeholders; each is replaced by a
proof in the owning track (see `Plan.lean`). Do not change these statements without
coordinating: other tracks build on them.
-/

open Module

namespace Lax119563Proofs.Stabilization

section Structure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Corner lemma** (track Structure). If `W` is `S`-simple and `2 dim W > dim E`, then `S`
contains every operator with range in `W` vanishing on `Wᗮ`. -/
theorem mem_of_corner (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) (W : Submodule ℂ E)
    (hW : IsSimpleFor S W) (h2 : finrank ℂ E < 2 * finrank ℂ W) (T : E →ₗ[ℂ] E)
    (hT : LinearMap.range T ≤ W) (hT' : Wᗮ ≤ LinearMap.ker T) : T ∈ S := by
  sorry

/-- **Decomposition** (track Structure). `E` splits into `S`-simple subspaces, and restriction
to them is an injective unital `⋆`-algebra homomorphism. -/
theorem exists_decomposition (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) :
    ∃ (m : ℕ) (W : Fin m → Submodule ℂ E), (∀ j, IsSimpleFor S (W j)) ∧
      ∑ j, finrank ℂ (W j) = finrank ℂ E ∧
      ∃ ρ : S →⋆ₐ[ℂ] ((j : Fin m) → (W j →ₗ[ℂ] W j)), Function.Injective ρ := by
  sorry

end Structure

/-- **Two-dimensional bound** (track Algebra, Theorem 5.15 with constant 10). -/
theorem matrix_chainBound (n : ℕ) : ChainBound (Matrix (Fin n) (Fin n) ℂ) (10 * n + 1) := by
  sorry

end Lax119563Proofs.Stabilization
