import Mathlib

/-!
# Stabilization bound: shared definitions

Weak chains (the `A`-sequences of Döring–Neuen, without strictness) and the invariance
notions used by the structure track.
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

end Structure

end Lax119563Proofs.Stabilization
