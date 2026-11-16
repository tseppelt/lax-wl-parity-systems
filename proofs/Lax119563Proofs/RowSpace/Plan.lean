/-!
# Plan for the row-space compiler

Goal: `Lax119563.RowSpaceCompiler.rowspace_compiler` — **done** (`RowSpace/Main.lean`, constant
`C = 20`, `Cₖ = spoilerConst k = (4k + 1)(k + 2) + 6k`).

## Files (import order)

* `Construction` — the graphs `rsGraph I ε`. Classes reuse the matrix compiler's `ICls I`
  (`coef e h` plays the mask class of stage `h`, `link` unused). Vertices are pairs of a class and
  an *effective* label in `RLab k ℓ = 𝔽₂ × 𝔽₂ × 𝔽₂^𝔠` (`verts I ε`, names translated by
  `ε • off`); adjacency `radj` via hubs (`hubR`), colors an injective code of the class.
* `Shifts` — descriptions (seeds `z`, masks `x`), translations `tr`, `radj_tr`.
* `Extension` — `DGood`, `Realizes`, **local extension** `local_extend` (round-free).
* `Duplicator` — value choice from `K_r` and the strategy (`duplicatorSurvives`).
* `SpoilerBasics`, `SpoilerStage`, `SpoilerInfer`, `Spoiler` — stage sweeps, inferences, walk
  (`spoilerWins`).
* `Size` — `card_names_le` (`card_maskSet_le : |rowspan B_e| ≤ 2^rank`).
* `OneVertex` — Abramsky–Jakl–Paine: one-vertex tree decompositions as rooted forests.
* `TreeLike` — unsolvable tree-like systems give contradiction trees; transfer along maps.
* `Affine` — affine dichotomy `hom_dichotomy`.
* `Exposed` — at most 4 exposed variables / 1 exposed equation for `≤ k + 1` classes.
* `Realize` — local realization (homomorphism `F → G₁` from compatible local values).
* `PatternTree` — the system `L` on `top`-variables, tree-like order by depth, `pattern_tree`.
* `Main` — `rsGraph_spec` and the concept theorem.

The pieces used by other areas: items (1)–(3) via `rsGraph_spec`; item (4) via `pattern_tree`.
-/
