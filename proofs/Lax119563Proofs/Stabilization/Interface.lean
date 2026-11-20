import Mathlib

/-!
# Stabilization bound: shared definitions and cross-track interface

Weak chains (the `A`-sequences of Döring–Neuen, without strictness) and the statements that
one work track provides to another. The `sorry`s here are placeholders; each is replaced by a
proof in the owning track (see `Plan.lean`). Do not change these statements without
coordinating: other tracks build on them.
-/

open Module

namespace Lax119563Proofs.Stabilization

section Chains

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-- A weak chain of length `ℓ` in a star algebra `A`: `V 0 = ℂ 1`, every `V i` (`i ≤ ℓ`) is
closed under `star`, and `V i * V i ≤ V (i + 1)` for `i < ℓ`. -/
structure IsChain (V : ℕ → Submodule ℂ A) (ℓ : ℕ) : Prop where
  zero : V 0 = ℂ ∙ (1 : A)
  star_mem : ∀ i ≤ ℓ, ∀ x ∈ V i, star x ∈ V i
  mul_le : ∀ i < ℓ, V i * V i ≤ V (i + 1)

/-- The number of strict steps `V i ≠ V (i + 1)`, `i < ℓ`. -/
noncomputable def strictSteps (V : ℕ → Submodule ℂ A) (ℓ : ℕ) : ℕ := by
  classical
  exact ((Finset.range ℓ).filter fun i => V i ≠ V (i + 1)).card

variable (A) in
/-- Every weak chain in `A` has fewer than `N` strict steps. -/
def ChainBound (N : ℕ) : Prop :=
  ∀ (V : ℕ → Submodule ℂ A) (ℓ : ℕ), IsChain V ℓ → strictSteps V ℓ + 1 ≤ N

end Chains

section Structure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- `W` is invariant under every element of `S`. -/
def Invariant (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) (W : Submodule ℂ E) : Prop :=
  ∀ a ∈ S, ∀ x ∈ W, a x ∈ W

/-- `W` is a nonzero `S`-invariant subspace without nontrivial `S`-invariant subspaces. -/
def IsSimpleFor (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) (W : Submodule ℂ E) : Prop :=
  W ≠ ⊥ ∧ Invariant S W ∧ ∀ U : Submodule ℂ E, U ≤ W → Invariant S U → U = ⊥ ∨ U = W

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
