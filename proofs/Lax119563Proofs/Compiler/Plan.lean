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
  version of `Compiler.Transfer.duplicatorWins_iff_of_corr`, moved from the deleted `Reduction/Transfer`; `survivesFrom_transfer` is round by
  round) and `numEdges_reGraph`. So `compile I := (reGraph I (L I) 0, reGraph I (L I) 1)` for an
  order `L I` chosen to suit the machine; `matrixGraph` is the case `L = vertexList`.
* (b) is **in progress** (infrastructure, see the architecture below). `Matrix/Main.lean` still proves the old
  form and cannot be rewritten before (b) is done (it would need a `sorry`).

## The bound of (b) and the size of `ℓ` (resolved)

With the first encoding (a block coordinate as the number `Σ b_t 2^t`) the bound was out of
reach of the paper's method: computing the targets `σ_e(c) = (f(i), b + δ_i)` of the columns
costs `Ω(ℓ)` per column, which `H` did not pay for (example: `𝔠_u = {(0, j + 2^(L-1))}`, `E`
binary schemas with domain `{(0, j) | j < m}` and shift `2^(L-1)`, `E m L` against
`(mL + E m log m + E L) polylog`). Concepts commit `a612ac6` (merged) writes block
coordinates and shifts with fixed width `ℓ` (`blockDescription`, `coordNumDescription`), so
every listed coordinate and every shift costs `≥ ℓ` bits of `H`, and the bound stays
`C (H + S) log₂(H + S + 2)^c` (statement unchanged).

**Cost accounting with the new encoding.** Unless the system is *trivial* (no schema and all
domains empty: then both graphs are empty), `ℓ ≤ H`, `W, E ≤ H`, `k ≤ H` if `E > 0`, and
`S ≤ poly(H)`, so `log(H + S + 2) = Θ(log H)`. Hence a *uniform* word size
`w = O(log(H + S + 2))` suffices for all registers **provided `ℓ`-bit vectors are never held
in a register**: a block coordinate is always processed bitwise, as the list of its `ℓ` bits
`b₀, …, b_{ℓ-1}` (exactly as it is written in the input), each bit operation costing `O(w)`.
Operations on vectors happen once per coordinate or shift listed in the input (or a constant
number of times per column of a schema domain), so they cost `O(H w)`; all per-vertex work
(`upd`, `track`, `coef`, indices) uses `O(1)` word operations, `O(S w)`. Exceptional
inputs: `k` (if `E = 0`) and `ℓ` (if the system is trivial) may be exponential in `H`; the
program first checks triviality and reads `k, ℓ` into registers only afterwards (skipping a
number costs its length).

Sorting: records of `ℓ + O(1)` words (join keys `(u, f(i), bits of b + δ_i)`), merge sort
written in the language itself on number stacks: `O(R (ℓ + 1) w log R)` for `R` records,
paid by `H` (one record per column of a schema domain, which costs `≥ ℓ` input bits) up to
the `log` factor.

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

## Architecture

**Language** (`Compiler/…`, copy-generalising `Reduction.HProg/HCompile/HMachine` and the
`Stm` layer): `HProg` with `Q` *number stacks* in addition to the registers:
`spush q r` (push the value of `r`), `spop q r` (`r :=` top or `0`, pop), and conditions that
also see whether each stack is empty; uniform cost `unitCost w` per primitive. On the stack
machine (`Hierarchy.Prog`, alphabet `Fin 2`) stack `q` holds `bs (encodeNats vs)` with the top
number first — the same format as the input stack — so `spop` is the input parser
(`Compiler/NumStack`: `nsPush_runs`, `nsPop_runs`). Queues are two stacks; the input is
parsed with `rd` into numbers. Merge sort of fixed-arity tuples is a program in the language
(proved at the list level). `computesWithin` through `Machines.TM.computesWithin_finish`-style
erasing (no `|x| ≤ |out|` condition: the output may be much shorter than the input).

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
  the answers in order. (Keys are tuples `(u, f(i), bits of b + δ_i)`, built bitwise.)
Totals (`n`, offsets of the schema blocks and of the coordinate section) by a counting pass;
the edge count `m` by emitting the edges of `G_ε` to a stream while counting, then
`n, colors, m, edges` for `ε = 0, 1`.

## Done for (b)

* `NumStack`: `nsPush_runs`, `nsPop_runs` (stack-program routines, cost `O(|bits v|)`).
* `NProg` (language, `NRuns` semantics with uniform word size `w`), `NCompile`
  (**`compileN_runs`**: simulation by `Hierarchy.Prog (R + Q + 7) 0` within the same cost;
  copy-generalised from `Reduction.HCompile`), `NMachine` (`NProg.computesWithin`, needs
  `|x| ≤ |output|`; superseded by `NOutput`).
* (item 1) `NOutput`: **`NProg.computesWithinO`** — no condition on the output length or the
  cursor; cost `t + 20 (|x| + |y|) + 10`. The machine drains the input to a unary helper,
  moves the head of tape `0` left by a raw `Mach.loop` (an empty stack is represented at any
  head position), then pushes the output.
* (item 2) `NLe` (runs within a cost, `NSt.Bdd`, embedding `HProg.toN` so that
  `Reduction.Ex.code` is reused), `CStm` (structured statements `skip, set, emit, push, pop,
  sne, rd, rst, seq, ite, loop` — `loop c body` is a *while* loop; total semantics `exec`
  (a loop runs for the least `n` with condition `0`, via `Nat.find`), `cost`, `Fits`;
  **`CStm.code_spec`**), `CMachine` (**`CStm.computesWithin`**: from the zero state, the machine
  computes `encodeNats (exec …).out` within `cost + 20 (|x| + |out|) + 10`), `CLib`
  (`CStm.Good x w c st st' T` = fits ∧ exec ∧ cost; combinators incl. `Good.loop` along a
  sequence of states; `exec_bdd`/`Good.bdd`: bounds and cursor are kept).
* (item 3, partly) `CStack.moveAllS_good`; `CParse` (**`rdNumS_good`**, `skipNumS_good`,
  `rdNumsS_good`: read / skip a self-delimiting number, read `n` numbers onto a stack;
  explicit final states `rdNumFinal`, `skipNumFinal`, `rnsSt`); `CSortLoop` (`Good.loop_var`:
  loops with variant and potential, `Good.loop_stop`, `Good.loop_cons`; `Frame`;
  **`moveN_good`**: move the top `n` words); `CSortList` (merge sort of records at the list
  level: lexicographic `rle`, `mrg`, `passX`, `passes`, **`finalRecs_eq`**: after `p` passes
  with `|rs| ≤ 2^p` the result is `rs.mergeSort rle`, `cmpW`/`rle_iff_cmpW` for word-by-word
  comparison); `CSort` (stack level: `mvRec_good`, `mvRecsB_good` (move records keeping the
  word order), `cmpS_good` (compare the top records of two stacks), `mrgStk`, `mrg_mv1/mv2`,
  `mrgIte_good` (one merge step)); `CSortMain` (**`sortS_good`**: stack `X` holding
  `rs.flatten` (records of `A ≥ 1` words) ends holding `(rs.mergeSort CSort.rle).flatten`,
  cost `(n+1)(log₂ n + 2) · 700 (a+1) nodeCost`; `mrgS_good`, `passS_good`, `mvAllS_good`,
  `revS_good`). Item 3 is done (queue helpers only if needed).
* (item 5) `OutDesc`: **`graphDescription_eq_gDesc`**, **`encodeGraphPair_eq`**:
  `encodeGraphPair (reGraph I (ordL I) 0) (reGraph I (ordL I) 1) = encodeNats (gDesc I 0 ++
  gDesc I 1)`, where `gDesc I ε = n :: colorsOf 0 (clsSizes I) ++ m :: edges` with `clsSizes`
  the label counts of `ordCls I` and edges `gEdges I ε`: for each schema `e`, each hub class
  `X` of `hubsCls I e` and each label `l` (index `i`), the pairs `(hubStart X + i, v)` for
  `v ∈ hubNbrs ε X l` — the slot positions `slotPos` (closed formulas: `schBase`, `hubSize`,
  `sumSize`, `entBefore`, `nEnt`, `coefSteps`, `locStart`, rank of the coordinate in
  `coordList (I.domain v)`, `initSeed` for singleton coordinate classes), sorted. Sorted forms
  (no sorting needed by the program except for junctions): `hubNbrs_link` (last track, end
  coordinate), `hubNbrs_upd` (previous track or sum, track, coef — unless first entry of a
  binary column), `hubNbrs_upd_first` (track, coef, start coordinate), `hubNbrs_junc` (sum,
  then the two coordinates sorted). Steps: `edgeList_hubsCls` (edges per hub class via
  `zipIdx_flatMap_blocks`), `posOpt_slot`, `clsStart_hubsCls`, `edgeList_eq_gEdges`,
  `schSize_eq`, `ent_lt_nEnt`, section bounds `track_lt_coef`, `coef_lt_locBase`,
  `sum_lt_track`, `coord_ge_locBase`.
* (item 5, partly) `OrderPos`: closed formulas `clsStart_junc/link/upd/sum/track/coef/coord`
  (via `schBase`, `locBase`, `locStart`, `colW`, `nEnt`, `entBefore`, `hubSize`, `sumSize`),
  `slot_mem_ordCls` (every slot class is present with labels `slotLabs`), `trackAt_stepsC`,
  `trackAt_numSteps`, `stepsC_ne_nil`, section bounds, `nbrPos_of_pairwise`.
  Pitfall: upd slots are not always increasing in slot order — for a binary schema at the
  first entry of a column `trackAt` is the start class `coord u (σ c)` (location section),
  so the sorted order is track, coef, coord.
* (item 5, partly) `OrderDesc`: class blocks `ordCls I` (`ordL_eq_flatMap`), **`colors_reGraph`**
  (colors = `colorsOf 0` of the class sizes), neighbor slots `slotsOf` (`hubB_iff_slotsOf`),
  **`edgeList_nbrPos`** (edges per hub = sorted present slot positions `nbrPos`),
  `idxOf_ordL` (position = `clsStart` + label index), `posOpt_bits1`, `posOpt_single`.
* (item 5, partly) `Order`: the vertex order **`ordL I`** (schemas: hubs then non-hubs; then
  locations), with entries in *q-major* order (`stepsC c` = increasing steps, so the
  previous entry of a column is the previous index; `coefSteps`), **`ordL_perm`** (so
  `reGraph_spec` applies). `OrderEdges`: hubs precede their neighbors (`ordL_pairwise`),
  **`edgeList_ordL`**: the edge list is, per position `u`, the increasing `v` with `hubB` from
  `L[u]` to `L[v]`.

## Decisions and pitfalls

* Entries of a column are ordered q-major (increasing step `σ = q M + j`), not `(j, q)` as
  first planned: then `trackAt` is just the previous entry of the column.
* Library specs give explicit final states (or stacks + `Frame`), so `Good` composes.
* Proof hygiene: `ext r` on `NSt` also applies list extensionality; use
  `NSt.ext (funext …) (funext …) ?_ ?_`. `simp` may undo `List.take_add_one`; close list
  goals with `simp only [List.reverse_append, …]`. `set S := … with` on states makes `simp`
  loop; define the loop states as top-level functions (`mvSt`).
* Worktree-isolated agents: shell commands combining `cd` with heredocs/git are refused;
  the shared scratchpad holds other sessions' files (use the `cm2-` prefix).

## Remaining work (in order)

3. **Library programs (rest)**: the stack-level merge sort of records (`A` words per record,
   word-by-word comparison via `cmpW`, merge of two runs using `moveN`, passes `passX`,
   against `CSortList.finalRecs_eq`; cost `O((R A + 1)(log R + 1))` word operations); queue
   helpers as needed.
4. **The compiler program** (as above): triviality check; locations pass; schema pre-scan;
   request pass; sort / join / sort; emission of `n`, colors, `m`, edges for `ε = 0, 1` in the
   order `ordL I`.
5. **List-level correctness (rest)**: only the per-pass correctness of the program against
   `gDesc` remains (the list-level target is done, see `OutDesc` above).
6. **Costs**: `w = O(log(H + S + 2))`, `O((H + S) log)` word operations, then
   `CStm.computesWithin`; finally `Matrix/Main.lean` with
   `compile I := (reGraph I (ordL I) 0, reGraph I (ordL I) 1)` and `reGraph_spec`.
-/
