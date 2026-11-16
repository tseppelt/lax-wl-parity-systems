/-!
# HomChar: plan and status

Goal: `Lax119563.HomomorphismCharacterization.distinguishes_iff_exists_hom_ne` (Dvořák; Dell,
Grohe and Rattan): for `k ≥ 2`, `k`-WL distinguishes `G` and `H` iff some `F` of treewidth at
most `k` has `hom(F, G) ≠ hom(F, H)`.

## Design

* (→) is `HomTensors.witness_from_rounds`.
* `Det` — tensor families `Fam k` (a function on the `k`-tuples of every colored graph);
  `Det r φ`: `φ G p̄` is a function of `χ^{(r)}_k[G](p̄)`, uniformly in `G`. Closed under
  products, contains atomic-type functions, and the WL extension
  `p̄ ↦ ∑_x ∏_i ψ_i(p̄[x/i])` raises the round by one (`det_ext`). `Ext`/`ExtAny` package
  `χ(p̄) ∏_i ψ_i(p̄[x/i])` (closed under products). `sum_eq_of_det`: equal round-`r` histograms
  give equal sums of round-`r` determined families.
* `Forest` — for a one-vertex forest (`RowSpace.OneVertexForest`): ancestors `Up`, subtrees `S`,
  children `ch`, roots, `I v = bag v \ {v}`; bags consist of ancestors, so subtrees of distinct
  children are disjoint and see each other only through the parent's bag. Generic sums over
  `agreeOff s g` (maps agreeing with `g` outside `s`): split off a vertex, factor over blocks.
* `Tensor` — local conditions `Ok`/`w`, subtree counts `Z c g`, recursion `Z_rec`,
  `hom_eq_prod` (`hom(F, G) = ∏_roots Z ρ g`), and the main induction `exists_det`: for labels
  `ℓ : Fin k → V(F)` covering `I c` and avoiding the subtree of `c`, `Z c g = φ(g ∘ ℓ)` for a
  WL-determined `φ`. Children seeing `c` get labels `ℓ[c/i]` with a free position `i`
  (`exists_free_pos`, using `|I d \ {c}| ≤ k - 1`). Roots: `exists_det_root` (sum over constant
  tuples).
* `Main` — `hom_eq_of_not_distinguishes` and the concept theorem.

## Status

Complete: `distinguishes_iff_exists_hom_ne` is proven, axioms `propext`, `Classical.choice`,
`Quot.sound`.
-/
