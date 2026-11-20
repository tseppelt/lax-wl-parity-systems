import Lax119563Proofs.Stabilization.Defs
import Lax119563Proofs.Stabilization.Structure

/-!
# Stabilization bound: structure of `⋆`-subalgebras of `End(E)`

The corner lemma and the decomposition into simple invariant subspaces, in the form used by the
two-dimensional bound (`TwoDim.lean`). Proofs in `Structure.lean`; definitions in `Defs.lean`.
-/

open Module

namespace Lax119563Proofs.Stabilization

section Structure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Corner lemma**. If `W` is `S`-simple and `2 dim W > dim E`, then `S`
contains every operator with range in `W` vanishing on `Wᗮ`. -/
theorem mem_of_corner (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) (W : Submodule ℂ E)
    (hW : IsSimpleFor S W) (h2 : finrank ℂ E < 2 * finrank ℂ W) (T : E →ₗ[ℂ] E)
    (hT : LinearMap.range T ≤ W) (hT' : Wᗮ ≤ LinearMap.ker T) : T ∈ S :=
  mem_of_corner' S W hW h2 T hT hT'

/-- **Decomposition**. `E` splits into `S`-simple subspaces, and restriction
to them is an injective unital `⋆`-algebra homomorphism. -/
theorem exists_decomposition (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) :
    ∃ (m : ℕ) (W : Fin m → Submodule ℂ E), (∀ j, IsSimpleFor S (W j)) ∧
      ∑ j, finrank ℂ (W j) = finrank ℂ E ∧
      ∃ ρ : S →⋆ₐ[ℂ] ((j : Fin m) → (W j →ₗ[ℂ] W j)), Function.Injective ρ :=
  exists_decomposition' S

end Structure

end Lax119563Proofs.Stabilization
