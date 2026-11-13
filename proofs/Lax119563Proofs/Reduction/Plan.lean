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

## Machine (to do, largest part)

Stack programs (`Hierarchy.Stack`, big-step semantics with exact costs) extended by head
tracking of tape `0` for the output layout. Structure: for each family `F`, for each `b`
(streaming `x` for the membership tables of `hitGuard`), for each label: decide validity,
emit the color; then the same loop for the hub edges into a scratch stack while counting;
emit the count and the edges. Per-slot work is polylogarithmic (recomputing the move of a
location from its fields, `prevStep` by linear search).
-/
