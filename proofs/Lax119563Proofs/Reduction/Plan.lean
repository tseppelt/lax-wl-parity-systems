/-!
# Plan of the `Reduction` area

Goal: `Lax119563.TimeReduction.time_reduction`.

## Mathematical assembly (`Assembly`, done)

For a register program `P` with `s ≥ 2` registers and a query, the matrix graphs
`matrixGraph (P.compile p₀ a₀) ε` are distinguished by `(s+1)`-WL iff the query accepts
(`distinguishes_matrixGraph_iff`, from the Matrix theorems `spoilerWins`, `duplicatorSurvives`
and the game characterization), and have `O((s+1) 2^ℓ w + (s+1)² 2^ℓ ℓ (r+1))` vertices
(`matrixGraph_n_le`); with the bounds of `Circuits.time_simulation` this is `O(n log^6 n)`.

## Transfer (`Transfer`, done)

The machine does not output `matrixGraph` itself but a renumbered copy with padding.
`duplicatorWins_iff_of_corr`: two pairs of graphs (each pair with common colors) whose
non-junk parts correspond by a bijection preserving adjacency and color equality, where junk
vertices are isolated and carry colors used by no non-junk vertex, are equivalent for the
bijective pebble game. Junk may be present on both sides (e.g. coordinate classes of unused
location codes in the matrix graph, padding slots in the output).

## Output graph (to do)

Vertex numbers are fixed-width bit fields, least significant first:
`z = lab + 4 (b + 2^ℓ (i + 2^wi F))`, with `lab` the two label bits, `b ∈ 𝔽₂^ℓ` and `i` the
coordinate, `F` a family record (hub bit on top, then kind, schema/location fields, step).
Invalid slots are padding (isolated, color `1`); a valid slot has color `2 ⌊z / 4⌋`. All hubs
(`upd`, `junc`, `link`) lie below all non-hubs, so the sorted edge list is: for each hub in
increasing order its neighbors in a statically known order (`coord < sum < track < coef` by
kind; location field above the coordinate fields; `locU < locV` for ternary schemas).

Own register program: `Circuits.compile` with an own injective bit-field location code and an
own location list (`verifier_accepts_iff` and `compile_accepts` allow this), commands
indexed by `(location, move index)`.

## Facts about the compiled system used by the numbering (to prove)

* No moves at `accept`/`reject`, so every command is executable: the last block of every
  schema domain is full, hence every step row is nonzero on every schema (`coef` classes
  exist for all `σ < N`) and every column has a nonzero entry (`k ≥ 3`).
* Block domains `i < s` come from `fieldGuard` (bit pattern of at most three bits),
  `hitGuard` (register `0`: the initial cell at offset `regVal b`, i.e. `x[b]`; other
  registers: the single value `field (2^H) (iℓ) ℓ`) and `missGuard`.
* Permutations: only the first two binary schemas of an assignment gadget carry
  `updatePerm (toUpdate mask)`: `(i, b) ↦ (i, b + δᵢ)` with `δᵢ` the `i`-th register of the
  mask and `δ_s = Σ δᵢ`; all other permutations are identities.
* Singleton classes: `prog accept` (init `0`) and `det out` (init `1`); in `G_ε` the
  effective label of a block-`0` coordinate of `det out` is `ε`.
* `prevStep` by linear search; `trackAt` of a link is never the start class.

## Machine (to do, largest part)

Stack programs (`Hierarchy.Stack`, big-step semantics with exact costs) extended by head
tracking of tape `0` for the output layout (`StackOut`, done: `Prog.RunsH`,
`Prog.compile_endsH`, `Prog.computesWithin`). To put the output at cell `0`: first move `x`
off stack `0` (head at `|x|`), build the reversed output elsewhere, pop the empty stack `0`
`|y| - |x|` times, then push the output. Structure: for each family `F`, for each `b`
(streaming `x` for the membership tables of `hitGuard`), for each label: decide validity,
emit the color; then the same loop for the hub edges into a scratch stack while counting;
emit the count and the edges. Per-slot work is polylogarithmic (recomputing the move of a
location from its fields, `prevStep` by linear search).
-/
