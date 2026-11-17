/-!
# Plan of the `Compiler` area

Goal: `Lax119563.MatrixCompiler.matrix_compiler` in its new form (concepts commit `a514079`):
a construction `compile` with (a) the game/size/edge clauses and (b) one deterministic machine
computing `encodeGraphPair (compile I)` from `encodeSystem I` within
`C (H + S) log₂(H + S + 2)^c` steps, uniformly in `k ≥ 3`, `ℓ ≥ 1`.

## Status

* (a) is done for every vertex order (`Clauses.reGraph_spec`): for any list `L` that is a
  permutation of `vertexList I`, the graphs `reGraph I L ε` (vertex `i` = `L[i]`, adjacency
  `adjN I ε`, color = position of the first name of the class in `L`) satisfy the Spoiler,
  Duplicator, size (`≤ 32 S`) and edge clauses with the constants of `matrixGraph`
  (`Cₖ = 2k + stepConst k`). The transfer is `duplicatorSurvives_iff_of_corr` (round-bounded
  version of `Reduction.duplicatorWins_iff_of_corr`; `survivesFrom_transfer` is round by
  round) and `numEdges_reGraph`. So `compile I := (reGraph I (L I) 0, reGraph I (L I) 1)` for an
  order `L I` chosen to suit the machine; `matrixGraph` is the case `L = vertexList`.
* (b) is **not started** beyond the analysis below. `Matrix/Main.lean` still proves the old
  form and cannot be rewritten before (b) is done (it would need a `sorry`).

## Obstacle: the bound of (b) when `ℓ` is large

`H` counts bits of the input and `S = Σ_v |𝔠_v| + (k+1) Σ_e nnz(B_e)` counts coordinates
and nonzero entries, but neither charges for the bit length `ℓ` of block coordinates that the
compiler has to *compute*. Example (`k = 3`, `ℓ = L`, `m` columns, `E` schemas):
location `u` with `𝔠_u = {(0, j + 2^(L-1)) | j < m}`; locations `v_e` with
`𝔠_{v_e} = {(0, j) | j < m}`; binary schemas `e = (u, v_e, {(0, j) | j < m}, σ, id)` with
`σ = (id; δ₀ = δ₁ = 2^(L-1), δ₂ = 0)` (well formed, pairwise sharing only `u`).
Then `H ≈ mL + E m log m + E L` and `S ≈ E m log m`, but the compiler must identify, for each of
the `E m` pairs `(e, j)`, the coordinate `σ_e(0, j) = (0, j + 2^(L-1))` in `𝔠_u` (the edge to the
coordinate vertex of `u`). Writing these targets costs `E m L`, which for `E = m = L = t` is
`t³` against a budget `t² polylog t`. The paper's sketch (records with `O(log)`-bit names)
silently assumes `ℓ = O(log(H + S))` (true in all applications, where `ℓ = O(log n)`).

Consequences:
1. Every cost model with a uniform word size (the `HProg`/`Stm`/`Gn` layers of `Reduction`,
   `unitCost w` per primitive, all registers `< 2^w`) needs `w ≥ ℓ`, hence costs
   `Ω(ℓ)` per primitive, and the number of primitives is at least `S`: total `Ω(S ℓ)`,
   which is not `Õ(H + S)` when `ℓ ≫ log(H + S)`. A proof of (b) as stated needs
   operations whose cost is the *actual* length of the operands, and
2. a *compressed join*: never materialise `σ_e(c) = (f(i), b + δ_i)` per column. A plausible
   algorithm: for each schema block `(e, i)` and each dyadic level `P = 2^λ` used by the
   columns of that block (`λ = ⌈log₂ bitlen(b)⌉`), locate the range of `𝔠_u` (block `f(i)`)
   whose elements agree with `δ_i` above bit `P` by one sort of range keys (cost
   `bitlen(δ_i) log` per block, i.e. `O(H log)`), give that range the id "rank of its first
   element", key every element of every `𝔠_v` once per level `P ≤ bitlen` by
   `(v, block, id at level P, low P bits)` (cost `O(bitlen · log)` per element) and every
   column by `(u, f(i), id, (δ_i mod 2^P) + b)` (cost `O(bitlen(b) + log)`), and join by one
   sort. This is far beyond the paper and the existing machine infrastructure.

**Recommendation (needs the user, concepts are frozen):** weaken clause (b) to
`C (H + S) (ℓ + 1) log₂(H + S + 2)^c` (or `C (H + S) (log₂(H + S + 2) + ℓ)^c`); this is still
`Õ(H + S)` in every application (`ℓ = O(log n)`) and makes the uniform word-size approach below
sound with `w = O(ℓ + log(H + S))`.

## Why the `Gn` generator framework cannot be reused directly

* `Gn` reads the input only through `loopX` (`inBit x k` for the loop index `k`), and its
  semantics carries no state from one iteration to the next (`out (loopX lim g) ρ =
  (range L).flatMap fun k => out g (ρ ++ [L, k, inBit x k])`). Parsing the self-delimiting
  number list `encodeSystem I` (where the position of the `j`-th number depends on all
  previous numbers) is impossible in one pass, and each extra pass costs `Θ(H)`.
* Lookups (the coordinate vertex of `(u, σ_e(c))`, the shift `δ_{c.1}` of a column) have no
  random access; a scan per lookup is quadratic. Joins need sorting (paper: "resolve endpoint
  names via sorts/joins").
* `HProg.computesWithin` needs `|x| ≤ |output|`, which fails here (`S` can be `0` while `H`
  is large); `Machines.TM.computesWithin_finish` (erase tape `0`, copy) has no such condition.
So the machine needs: (i) a stateful sequential parser of the input (the `Stm`/`HProg` level
has registers and `rd`, `Gn` does not), (ii) work streams (tapes holding number lists, written
sequentially, rewound, read sequentially), (iii) a sort of a stream of fixed-arity tuples
(`Machines.sortRecords_spec`, records = bit strings; use an order-preserving prefix-free
code of numbers, e.g. `1^(bitlen m) 0 (bits m, most significant first)`, so that `recLE` on
concatenated codes is the lexicographic order of tuples), (iv) final `finish`.

## Proposed architecture (for the amended bound; uniform words `w = O(ℓ + log(H + S))`)

A *stream register language* `SProg` (copy-generalise `HProg` into `Compiler/`): registers,
the input cursor (`rdNum r`: parse the next `encodeNat`), streams `s` with `push s e`,
`rewind s`, `pop s r` (with an end test), `clear s`, `sortS s a` (sort as `a`-tuples), `emit e`;
total denotational semantics as for `Stm` (`exec`, `cost`, `Fits`), compiled to a `TM` from the
`Machines` combinators, and `computesWithin` through `finish`.

Vertex order `L I` (chosen so that every edge goes from a hub to a later vertex):
`L = (schemas e in order: hubs(e) ++ nonhubs(e)) ++ (locations v in order: coordVerts v)` with,
for `D = coordList (dom e)` (= increasing `coordNum`, as in the input), `rows c` = the nonzero
rows of column `c` in increasing order (`c.1` if `c.1 < k-1`, all `j < k-1` if `c.1 = k-1`,
then `k-1+t` for the set bits `t` of `c.2`), and entries `(c, j, q)` (step `σ = q M + j`):
* `hubs e`: for `c ∈ D`: `junc e c` (4 labels, ternary only), `link e c` (2); then for
  `c ∈ D`, `j ∈ rows c`, `q ≤ k`: `upd e σ c` (4);
* `nonhubs e`: for `c ∈ D`: `sum e c` (2, ternary); for the entries in the same order:
  `track e σ c` (2); then `coef e σ` (2) for `j ∈ R_e` (nonzero rows of `e`), `q ≤ k`.
Then the edge list is, for each hub in order, its at most three neighbors sorted (non-hubs
are adjacent only to hubs, `hubB_hub`), and all numbers are local except:
* `trackAt e c σ`: the previous entry of the same column (index arithmetic in the
  `(j, q)`-major order: `(q, j_prev)` or `(q - 1, last row)`), or the start class;
* `coef e σ`: `rank_{R_e}(j)`: block rows by a running count of distinct blocks of `D` (or `j`
  if block `k - 1` occurs), checksum rows by `popcount(OR_e mod 2^t)` with `OR_e` the bitwise
  or of the block coordinates of `D` (one pre-scan of the schema);
* `(f(c.1), δ_{c.1})`: merge the domain scan with the permutation descriptions (blocks are
  nondecreasing in `D`), via two work streams;
* the coordinate vertex of `(u, σ(c))` and `ι(u)`: **join** — pass A writes
  `(v, coordNum c', first vertex number, ι(v))` for all locations (already sorted); pass B
  writes requests `(u, coordNum σ(c))` in emission order; sort requests by key with their
  sequence number, merge with pass A, sort answers by sequence number; the emission pass pops
  the answers in order. (Keys of `ℓ + log k` bits: fine only under the amended bound.)
Totals (`n`, offsets of the schema blocks and of the coordinate section) by a counting pass;
the edge count `m` by emitting the edges of `G_ε` to a stream while counting, then
`n, colors, m, edges` for `ε = 0, 1`.

Remaining work, in order: `SProg` with semantics/compiler/cost (largest part, ~3–5k lines by
analogy with `HProg/Stm/Gn`); the stream join lemma (sorted merge semantics); the program;
the list-level proof that its output is `graphDescription (reGraph I (L I) ε)` (relate the
column-major order to `vertexList` by a permutation, `reGraph_spec` does the rest); cost
bounds; `Matrix/Main.lean`.
-/
