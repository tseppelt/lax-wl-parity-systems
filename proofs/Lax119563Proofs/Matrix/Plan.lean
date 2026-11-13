/-!
# Plan for the matrix compiler

Goal: `Lax119563.MatrixCompiler.matrix_compiler`.

## The construction (`Construction.lean`)

For an implicit parity system `I` with `E` schemas we fix `M = k - 1 + ℓ` check rows and
`R = k + 1` repetitions; the strip of a schema has `R * M` *steps* `σ`, step `σ` processes
row `σ % M` (rows `< k - 1` are the block-parity checks, the others the checksum checks).

Vertex classes (`Cls`):
* `coord v c` for `c ∈ 𝔠_v` (a pair, or a singleton at an initialized location),
* `sum e c`, `junc e c` for ternary `e` and `c ∈ 𝔠_e` (junction labels `(s, t, s + t)`),
* `track e σ c` for every nonzero entry `B(row σ, c) = 1`: the track leaving the update of
  step `σ`,
* `upd e σ c` for every nonzero entry (labels `(s, t, s + t)`),
* `coef e σ` for every step whose row is nonzero on `𝔠_e`,
* `link e c` for `c ∈ 𝔠_e`, joining the last track of column `c` to the end coordinate class.

Tracks are identified across zero entries by naming a track after the step that creates
it: the track of column `c` at stage `σ` is `track e σ' c` for the last nonzero step
`σ' < σ`, or the start class (`coord u (σ_e c)` resp. `sum e c`) if there is none.
Compared with the paper, the `link` class replaces the identification of the last track
with the end coordinate class; this keeps all names uniform.

A vertex name is a class with a label in `ZMod 2 × ZMod 2`. Both graphs `G₀, G₁` have
the same explicit list of vertex names, the same colors (the index of the first vertex of
the class in the list), and differ only through the *effective label* of the singleton
coordinate vertices, which is `ε · ι(v)` in the first block.

## Duplicator (`Duplicator*.lean`)

A *description* consists of total seeds `z_v` and coefficient bits `λ_{e,σ}`. It induces a
translation of every class, hence a class-preserving involution `φ_D` on vertex names.
`φ_D` is an isomorphism on the subgraph induced by a set `A` of classes as soon as the
seeds at initialized locations are the initial seeds and the mask-sum condition holds at
the internal coordinates of `A`. The invariant `Good r A D` adds the conditions on
partial seeds (block-even codewords are annihilated, exposed values agree with `K_r`) and
conflict-freeness of `K_r`. The local extension lemma follows the paper (exposure, value
extension, partial seed extension, row-space repair in an untouched repetition); one
repetition per class suffices for the touching argument, hence `R = k + 1`.

## Spoiler (`Spoiler*.lean`)

Spoiler's moves are expressed through `Forces c S P`: from state `S`, Spoiler can force
within `c` rounds a state satisfying `P` (or win). He always pebbles zero vertices of `G₀`
and keeps pebble `k` as spare; replacing a representative costs two rounds (spare, then
copy). Row sweeps, junction steps and the inference walk follow the paper.

## Size (`Size.lean`)

Explicit counts of the vertex list, and the edge bound via the hubs (updates, junctions,
links), each of degree at most three.
-/
