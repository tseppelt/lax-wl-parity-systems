import Lax119563.HomomorphismCharacterization
import Lax119563.WitnessFromRounds
import Lax119563Proofs.Stabilization.Part1

/-!
# The homomorphism characterization of Weisfeiler–Leman

Direction (→) is `Lax119563.WitnessFromRounds.witness_from_rounds`. For (←), suppose `k`-WL does not distinguish
`G` and `H`, and let `F` have treewidth at most `k`. A one-vertex forest of `F`
(`RowSpace.oneVertexForest_of_treewidth`) writes `hom(F, ·)` as a product over its roots of sums
over all `k`-tuples of WL-determined tensors (`hom_eq_prod`, `exists_det_root`); these sums agree
on `G` and `H` because all color histograms agree (`sum_eq_of_det`).
-/

namespace Lax119563Proofs.HomChar

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.ColoredHomomorphisms
open Lax119563Proofs.RowSpace

variable {k : ℕ}

/-- If `k`-WL does not distinguish `G` and `H`, then graphs of treewidth at most `k` have equal
homomorphism counts into `G` and `H`. -/
theorem hom_eq_of_not_distinguishes (hk : 2 ≤ k) {G H : ColoredGraph}
    (h : ¬ Distinguishes k G H) {F : ColoredGraph} (hF : TreewidthAtMost F k) :
    hom F G = hom F H := by
  classical
  obtain ⟨T⟩ := oneVertexForest_of_treewidth hF
  have hsum : ∀ φ : Fam k, DetAny φ → ∑ p, φ G p = ∑ q, φ H q :=
    fun φ ⟨r, hr⟩ => sum_eq_of_det hr fun hd => h ⟨r, hd⟩
  have hn : G.n = H.n := by
    have := hsum (fun _ _ => 1) ⟨0, det_const 1⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      smul_eq_mul, mul_one] at this
    exact Nat.pow_left_injective (by omega) this
  by_cases hne : Nonempty (Fin F.n → Fin G.n)
  · obtain ⟨g⟩ := hne
    obtain ⟨g'⟩ : Nonempty (Fin F.n → Fin H.n) := hn ▸ ⟨g⟩
    have hroot : ∀ ρ, ∃ θ : Fam k, DetAny θ ∧
        (ρ ∈ roots T → ∀ G g, Z T G ρ g = ∑ p, θ G p) := by
      intro ρ
      by_cases hρ : ρ ∈ roots T
      · obtain ⟨θ, hθ, hZ⟩ := exists_det_root T hk ρ hρ
        exact ⟨θ, hθ, fun _ => hZ⟩
      · exact ⟨fun _ _ => 0, ⟨0, det_const 0⟩, fun h => absurd h hρ⟩
    choose θ hθ hZ using hroot
    rw [hom_eq_prod T G g, hom_eq_prod T H g']
    refine Finset.prod_congr rfl fun ρ hρ => ?_
    rw [hZ ρ hρ, hZ ρ hρ]
    exact hsum _ (hθ ρ)
  · have hne' : ¬ Nonempty (Fin F.n → Fin H.n) := hn ▸ hne
    rw [not_nonempty_iff] at hne hne'
    rw [hom_eq_sum T G, hom_eq_sum T H]
    simp

/--
---
conclusion: Lax119563.HomomorphismCharacterization.distinguishes_iff_exists_hom_ne
---
(→) is the witness theorem `witness_from_rounds`: a distinction after `r` rounds yields a colored
graph of treewidth at most `k` with different homomorphism counts.

(←) Let `F` have treewidth at most `k`, and take a one-vertex tree decomposition of width `k` of
it (Abramsky–Jakl–Paine): a rooted forest on `V(F)` where each vertex `v` has a bag of at most
`k + 1` vertices containing `v`, the rest of which lies in the bag of the parent, and every edge
lies in a bag. A map `V(F) → V(G)` is a homomorphism if and only if every vertex satisfies its
local condition (color, and edges to the rest of its bag). Counting the maps on the subtree of a
vertex `c`, with the vertices outside given, yields the recursion "choose the image `x` of `c`,
check the local condition at `c`, and multiply the counts for the children of `c`". By induction
from the leaves, the count for `c` is a function of the round-`r` WL color (for some `r`) of the
`k`-tuple formed by images of labels `ℓ` covering the rest of the bag of `c`: the sum over `x`
is a WL refinement step, in which every child either keeps the labels `ℓ` or replaces one
position (not needed for the rest of its bag; it exists since that rest has at most `k - 1`
vertices besides `c`) by `c`. At a root, the count is a sum over all `k`-tuples of a
WL-determined function, so it agrees for `G` and `H` when no round of `k`-WL distinguishes them;
`hom(F, ·)` is the product of these counts over the roots.
-/
theorem distinguishes_iff_exists_hom_ne (hk : 2 ≤ k) (G H : ColoredGraph) :
    Distinguishes k G H ↔ ∃ F : ColoredGraph, TreewidthAtMost F k ∧ hom F G ≠ hom F H := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨F, hF, -, hne⟩ := Lax119563.WitnessFromRounds.witness_from_rounds hk hr
    exact ⟨F, hF, hne⟩
  · rintro ⟨F, hF, hne⟩
    by_contra h
    exact hne (hom_eq_of_not_distinguishes hk h hF)

end Lax119563Proofs.HomChar
