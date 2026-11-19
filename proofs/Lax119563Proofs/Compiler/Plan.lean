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

## Design of the compiler program (item 4)

One statement `CStm CR CQ` with fixed sizes (`Compiler/PDefs`: `CR` registers, `CQ` stacks,
named constants for every register and stack; distinctness by `decide`). The input is
`x = encodeNats (systemDescription I)`; `H = |x|`.

**Size facts.** Numbers that are *read* into registers must be `≤ H` (then they fit, since
`w` is chosen with `4 (H + S + 2) ≤ 2^w`, `PDefs.bits_lt_of_le`): `W`, every `|D|`, every
init value, `E`, and — only when the system is nontrivial — `ℓ`; `k` and the block indices
`i` only when `E > 0`. Otherwise the numbers are *skipped* (`skipNumS`, any size).

**Passes** (each a module with a `Good` spec against a list function of `I`):
* `P0` (`Compiler/PTriv`): skip `k`, `ℓ`; read `W`; for `v < W` read `ι(v)` and `|D_v|`,
  stopping at the first nonempty domain (its coordinates cannot be skipped without `ℓ`); if
  all are empty read `E`. Result: register `triv = [no coordinate ∧ E = 0]`
  (`PTriv.triv_iff`). If `triv`, the output is `[0,0,0,0]` (`gDesc` of the empty pair) and the
  program stops.
* `P1` (locations, nontrivial case): `rst`; skip `k`; read `ℓ`, `W`; for each location
  read `ι(v)`, `|D_v|` and its coordinates — the block index skipped or read depending on `E`
  (unknown yet: so `P1` skips them and only computes `locSize`, `locStart` (pushed on a
  stack, one per location) and reads `E` at the end); `P1'` (if `E > 0`) re-reads the
  locations pushing the records `(v, i, b₀ … b_{ℓ-1})` for the join (already sorted by key).
* `P2` (schema pre-scan): per schema `schSize`, `colW`, `nEnt`, `|coefSteps|`, `schBase`;
  `locBase = Σ schSize`.
* `P3` (requests): per column and slot argument the key `(u, f(i), b + δ_i bitwise)` with a
  sequence number; `sortS`, merge-join with the `P1'` records (answer: `idxOf c' (coordList
  (I.domain u))`), `sortS` by sequence number.
* `P4` (emission, for `ε = 0` then `ε = 1`, all data reused): `n = Σ clsSizes`, the colors
  `colorsOf 0 clsSizes` (per schema its class sizes, then per location), then the edges of
  `gEdges I ε` pushed to a stack while counting, then `m` and the edges popped in order.
  Both `ε` read the same answer stack (copied non-destructively).

**State of item 4 (branch proofs/compiler-prog).** Done: `PSys` (input structure:
`sd_eq`, `locD`, `locsPre/locsSuf`, `posAt`, `drop_posAt`, `posAt_succ`, `drop_ell`,
`drop_W`; sizes `W_le`, `E_le`, `card_le`, `bits_lt_of_le`); `PTriv` (registers `CR = 40`,
`CQ = 16`, `rT, rP, rW, rJ, rNz, rA, rD, rE, rTriv`; **`p0_good`**: from cursor `0`, `p0` sets
`rTriv = [trivSys I]`, stacks and output kept, cost `200 (H + 1) nodeCost`, under
`2 (H + 1) ≤ 2^w`; `p0Body_good`, `p0End_good`; **`gDesc_triv`**: `gDesc I ε = [0, 0]` for a
trivial system). `CSkip` (**`skipNumsS_good`**: skip `n` numbers of any size,
**`skipBlocksS_good`**: skip `d` blocks of `m` numbers; existential final state with stacks,
cursor, output and the untouched registers). `PLoc` (pass `P1`, branch proofs/compiler-p1):
registers `rL = ℓ`, `rL1 = ℓ + 1`, `rOff`, counters `rK, rI`, stack `qLoc = 0`;
`coordNum_injective`, `card_image_coordNum` (`|D.image coordNum| = |coordList D|`),
`locNums`, `locD_eq'` (`locD = ι :: |D| :: (locNums.map coordNumDescription).flatten`),
`locSize_eq`, `locOff j` (`locStart v = locBase + locOff v`, `locOff_succ`, `locOff_le_H`),
`locOffs`, `schPos`, `drop_schPos`; **`p1_good`**: under `4 (H + 1) ≤ 2^w` and `ℓ ≤ H` (to be
proved for nontrivial systems with `k ≥ 1`), from any state with `pos ≤ H`, `p1` ends at
`schPos I` with `rW = W`, `rL = ℓ`, `rE = E`, `rOff = locOff I W`, `qLoc` :=
`(locOffs I).reverse ++ qLoc`, other stacks and output kept, cost `500 (H + 1) nodeCost`.
`ell_le_H` (`1 ≤ k`, `¬ trivSys I` → `ℓ ≤ H`). `PRec` (pass `P1'`, for `E > 0`):
`k_le_H` (`E > 0` → `k ≤ H`), `coordNum_div`, `labsN v = |coordLabs v|`, records
`locRec I v r = v :: coordNumDescription ℓ (locNums[r]) ++ [locOff v + r · labsN v, labsN v]`
(so the record ends with `clsStart (coord v c) - locBase` and the label count),
`recsV`, `recsUpTo`, `locRecs`; **`p1r_good`**: after `p1` (`rW = W`, `rL1 = ℓ + 1`), under
`k, ℓ ≤ H`, `p1r` sets `qRec := (locRecs I).flatten.reverse ++ qRec` (other stacks, output,
`rW`, `rL1` kept), cost `600 (H + 1) nodeCost`; `p1rIn_good`, `p1rBody_good`. Now `p1r` *reads*
`k` into `rKk` (register 16) and ends at `posAt I W` (the position of `E`); `p1r_good` also
gives every register with `wReg r p1r = false` (e.g. `rL`) unchanged.
Records are in input order: `(v, i, b₀ … b_{ℓ-1})` with `b₀` the *least* significant bit, so
they are **not** sorted by `CSort.rle`; for the join either sort them too (`sortS`) or build
the request keys in the same order and sort both. **`locNums_eq`** (`PLoc`): `locNums I v = (coordList (I.domain v)).map coordNum`, so the
`r`-th record of `v` is the coordinate `(coordList (I.domain v))[r]` and its offset matches
`clsStart_coord` (`idxOf` in `coordList`); helpers `blockNum_cons`,
`map_blockNum_allBlockCoords` (`= range (2^ℓ)`), `pairwise_map_coordNum_allCoords`.
**Branch proofs/compiler-p2.** `CFrame` (`wReg r c`, `wStk q c`, `wOut c`, `wPos c`: syntactic
frames; `Good.env_of/stk_of/out_of/pos_of`, closed by `decide`, e.g. `hall.env_of (by decide)`).
`CArith` (`mulS_good`, `predS_good`, `pushZS_good`, `mvSumN_good`). `PSchSize`
(`ent_ne_zero_iff` with `rowNZ`, `length_stepsC` = `(k+1) rowsC c`, `nEnt_eq`,
`length_coefSteps` = `(k+1)(blkRows + orPop)`, `schSize_eq'` = `|D|(tern?8:2) + 6 nEnt + 2|coef|`,
`dChg`/`blkRows_eq` (block changes of the sorted blocks), `orsL`/`orsL_append`/`sum_orsL`).
`PSchDesc` (`cdesc c = c.1 :: blockDescription c.2`, `domainDescription_eq'`,
`schemaDescription_eq'` = `arity :: schLocs ++ (|D| :: coords) ++ perms`, `schD`, `schAt`,
`drop_schAt`, `schAt_succ`, `schPos_add`). `PSch` (program `p2`; registers 17–35, stacks
`qOr = 2`, `qOr2 = 3`, `qSch = 4`; `p2Bit_good`, `p2Blk_good`, `p2Coord_good`, `p2Fin_good`).
`PSchLoop` (`p2Sch_good`, **`p2_good`**: at `posAt I W` with `rKk = k`, `rL = ℓ`, `rL1 = ℓ+1`,
`qOr = qOr2 = []`, under `1 ≤ k`, `E > 0`, `16 (H + locBase + 1) ≤ 2^w`: `rLB = locBase I`,
`qSch := (schRecsUpTo I E).reverse ++ qSch` with `schRec I e = orsL D ++ [blkRows D, nEnt, |coefSteps|]`,
`pos = H`, cost `2000 (H + 1) nodeCost`).
Order of the passes (nontrivial case, `E > 0`): `p0`, `p1`, `p1r` (reads `k`), `p2` (directly
after `p1r`, at `posAt I W`). Notes for `P3`/`P4`: the cursor can only be rewound (`rst`), so a
pass over the schemas must skip the location section again (write a generic location-skip
loop: per location skip `ι`, read `|D|`, `skipBlocksS |D| (ℓ+1)`; or merge the request
generation into the `p2` scan, which already visits every coordinate but skips the
permutations). Per-entry loops (`k + 1` repetitions of the rows of a column) are paid by `S`;
per-coordinate bit loops by `H`; never loop `ℓ` times per entry (store the row ranks of a
column on a stack once). `Ex` has no subtraction/multiplication: use `predS`, `mulS`,
counters. Cost tips: for a big body, prove the final arithmetic as a standalone lemma over
`ℕ` variables (`p2Sch_cost_arith`) and close with `exact`; `generalize … at *` and `nlinarith`
in a large context time out. Facts stated after `set e := ⟨j, hlt⟩` must be type-ascribed
with `e` (else `omega` sees different atoms).
Next: `P3`. For the costs use the
pattern of `p0_good` (`generalize` the lengths, `nodeCost`, `unitCost`, then `nlinarith`;
if `nlinarith` times out in a big context, `nlinarith only [hU, hU', hint products]`);
for loops `Good.loop_var` with `μ` = remaining iterations and `φ = H - pos` (or
`P - pos` for a fixed end `P` when the loop reads only a sublist).
Pitfall: in `simp`/`rw` proofs about states built with `set`, prefer `show` with the
definitional `Function.update` form (`e5` in `p0_good`). With `open CStm`, write
`CStm.nodeCost_ge`, `CStm.unitCost_ge` (ambiguous with `Reduction.nodeCost_ge`).
**Cost obstruction (resolved):** `sortS` costs `(n+1)(log₂ n + 2) · 700 (a+1) nodeCost`, i.e.
`(L+1)³` per record word; `machine_of_program`/`final_bound` now take any exponent `e ≥ 1`
(`cost ≤ K (H+S+1)(L+1)^e`), so use `e = 3`.

**Branch proofs/compiler-p3 (P3, in progress).** Design (*union sort*, no key comparisons):
location records and requests have the same shape `key ++ [tag, d₁, d₂, d₃]` with
`key = v :: i :: b₀ … b_{ℓ-1}` (`ℓ + 2` words): `locRec I v r = v :: cnd ++ [0, off, labs, ι]`
(`PRec` now pushes this format: tag `0` and `initNum (I.init v)` added; `p1r_good` also gives
`rCnt = |locRecs I|`, register 36), requests `reqRec u π c s = u :: cdesc (π.apply c) ++
[1, s, 0, 0]` (`PReqList`). After `sortS` of the union (stack `qX = 5`), the location record
with the key of a request comes right before it (tag `0 < 1`) and no other location record lies
between (**`Join.scanF_eq`**, `PJoinList`); so one scan answers all requests (**`pJScan_good`**,
`PJoin`: answers `[seq, off, labs, seed]` pushed on `qAns = 12`, `seed = [i = 0 ∧ ι = 2]` =
`(initSeed I v c').val`). Then `sortS` of the answers by `seq`. Sequence numbers are
`ansBase I e + seqOff tern |D| a r` (`PReqList.reqsE`): the order in which `P4` consumes the
answers (ternary: per column `U, V, W`; binary: all `V` (links), then all `U` (first upd)).
Planned P3 program: `moveAllS qRec qJunk` (drop the old records), `p1r` (records again, cursor at
`posAt W`), skip `E`, generation over the schemas (per schema: read arity, locations onto
`qLs → qLs2`, `|D|`, the coordinates onto `qDom → qDom2`; per argument: `f` onto `qF → qF2`,
the shifts onto `qDl → qDl2`, then per column: advance the block (`moveN qDl2 qJunk ℓ`, pop
`f`), `p3Bits` (**done**, `PReqBits`: xor of column bits and shift bits onto `qRec`), restore
the shift (`moveN qAux qDl2 ℓ`), push `1, seq, 0, 0`; afterwards `qF2, qDl2` to `qJunk`,
`qDom → qDom2`), `moveAllS qRec qX`, `sortS` (`A = ℓ + 6`, `N = rCnt + rSB`), `pJScan`,
`sortS` of `qAns` (`A = 4`). Stacks/registers of P3: `PJoin` (`qX … qJunk`, scan registers
20–29) and `PReqBits` (generation stacks 5–11, 14, 15; registers 20–35 scratch; persistent:
`rW, rE, rL, rL1, rKk, rLB, rPL, rCnt = 36, rSB = 37` (request count / seq base)).
Done (all `Good` lemmas with explicit stacks, frames via `wReg`/`wStk`): `p3Bits_good`,
`p3Advs_good`, `p3Col_good` (`PReqCol`), `p3Cols_good` (`PReqCols`: requests `colReqs u π cs s₀ t`,
needs the column blocks nondecreasing, `curB`), `p3Arg_good` (`PReqArg`: one argument, reads
`f`/shifts via `rdNumsS` + `moveAllS`, `p3Seq` sets the first sequence number
`base + sqOff tern a |D|`, stride `sqStr tern`; needs `st.Bdd w` for `moveAllS`),
`p3Args_good` (`PReqArgs`: all arguments, requests `argsReqs locs perms cs base tern A`).
**Done:** `p3Sch_good` (`PReqSch`, commit c58fe26): at a schema description (`hx`), with
`rKk = k`, `rKL = k ℓ`, `rL = ℓ`, `rL1 = ℓ + 1`, `rSB = base`, `rJ = j`, generation stacks empty,
`st.Bdd w`, and one bound `Hb` (`2 (Hb + 1) ≤ 2^w`, all description numbers, `|D|(ℓ+1)`,
`kℓ + k + 1`, `base + 3|D| + 3`, `j + 1`, `ℓ + 2` all `≤ Hb`): pushes
`argsReqs (schLocs sc) (schPerms sc) (coordList D) base tern (arity sc)` (reversed) on `qRec`,
`rSB := base + arity · |D|`, `rJ := j + 1`, stacks empty again, cost
`10000 (|encodeNats (schemaDescription sc)| + 1) nodeCost`.
**P3 program side done (branch proofs/compiler-p3b).** `PReqLoopList` (`argsReqs_eq_reqsE`
via `seqOff_eq`, `reqsUpTo_succ/_all`, `length_reqsUpTo`, sizes `dom_mul_le`, `ansBase_mul_le`,
`length_reqs_mul_le` (`|reqs| (ℓ+1) ≤ 3H`), `length_locRecs_mul_le` (`|locRecs| (ℓ+1) ≤ H`),
`schD_vals_le`); `PReqLoop` (**`p3Loop_good`** = `.loop (rJ < rE) p3Sch`: from `schPos I` with
`rJ = rSB = 0`, `GenEmpty`, pushes `(reqs I).flatten.reverse` on `qRec`, `rSB = |reqs I|`,
`pos = H`, cost `30000 (H+1) N`); `P3Aux` (`p3Union = (union I).mergeSort rle`, `p3Scan`,
`p3Ans_eq` from `p3_answers`, `union_mul_le` (`|union| (ℓ+1) ≤ 4H`)); `P3Gen` (**`p3Gen_good`**:
`moveAllS qRec qJunk; p1r; rdNumS rE; mulS rKL; rSB, rJ := 0; p3Loop; moveAllS qRec qX`, ends
with `qX = (union I).flatten`, cost `32000 (H+1) N`); `P3Join` (sort registers `rsA = 38`,
`rsDone = 39`, others 20–33 (except 28 = `rN`); **`p3Join_good`**: `rN := rCnt + rSB`,
`rsA := ℓ+6`, `sortS qX`, scan data `:= 0`, `pJScan`, `rN := rSB`, `rsA := 4`, `sortS qAns`;
cost `150000 (H+1)(log₂(H+1)+1) N`); `P3` (**`p3_good`**, `p3 = p3Gen; p3Join`): under
`1 ≤ k`, `I.schemas ≠ []`, `16 (H+1) ≤ 2^w`, from a `Bdd` state with `pos ≤ H`, `rW = W`,
`rL = ℓ`, `rL1 = ℓ+1`, `GenEmpty`, `qAns = []`, `|qRec| ≤ 6 (H+1)`: `qAns = (ansAll I).flatten`,
`qX = qRec = []`, generation stacks empty, other stacks except `qJunk` kept, `rW, rL, rL1,
rKk = k, rE = E, rKL = kℓ, rCnt = |locRecs I|, rSB = |reqs I|`, `pos = H`, output kept, frame
`wReg r p3 = false`; cost `200000 (H+1)(log₂(H+1)+1) · nodeCost w` (no open hypotheses).
With `nodeCost_le_sq` (`(L+1)²`) this is `O((H+1)(L+1)³)`, fitting `machine_of_program` with
`e = 3`. Next: `P4` (emission), which reads `qAns` (first answer on top) and must run `p3`
after `p2` (state then: `pos = H`, `qRec = (locRecs I).flatten.reverse` of length
`|locRecs| (ℓ+6) ≤ 6H`, `rL = ℓ`, `rL1 = ℓ+1`, `rW = W`).
Pitfall: `timeout` is not installed on macOS, `timeout … lake env lean` prints nothing — use
`lake build <module>` to confirm.

## P3 list facts (branch proofs/compiler-p3list, `Compiler/PJoinFacts`; done, no sorry)

Item (3) of the P3 remaining work. With `union I := locRecs I ++ reqs I`:
* shapes: `locRecs_eq` (`locRecs I` = per location `v`, per `c ∈ coordList (I.domain v)`,
  `locRecC I v c = v :: cdesc c ++ [0, locOff v + idxOf c · labsN v, labsN v, initNum ι(v)]`),
  `mem_locRecs`, `mem_reqs`, `key_locRecC`/`key_reqRec` (keys `v :: cdesc c` of `ℓ + 2` words),
  `isLoc_locRecC`/`isLoc_reqRec`, `length_of_mem_union` (all `ℓ + 6`);
* **`hG1`** (`gLoc I key` := the location record with that key, `Classical.choose`;
  `locRec_unique` via `cdesc_injective`), **`hG2`** (`req_loc`, `target_mem`: by
  `Schema.WellFormed`, `π.apply c ∈ I.domain u` for each argument `(u, π)` of a schema);
* counts: **`length_reqs`**: `|reqs I| = ansBase I E`; `length_union` (= `|locRecs I| + ansBase I E`);
  `ansBase_le_H` (`arity · |D| ≤ |schemaDescription|`);
* word bounds for systems with a schema (`I.schemas ≠ []`) under `4 (H + 1) ≤ 2^w`:
  `lt_of_mem_union`, `lt_of_mem_ansAll`, `lt_of_mem_jScan` (entries `≤ 2H`, resp. `≤ H`);
* answers: `ansRec I v c' s = [s, clsStart I (coord v c') - locBase I, labsN I v,
  (initSeed I v c').val]` (`labsN = 1 + [ι(v) = ⋆]`); **`ansE I e`** (P4 order: ternary
  `(coordList D).zipIdx.flatMap fun (c, r) => [U, V, W]` with seq `ansBase e + 3r + 0/1/2`; binary
  all `V` (seq `ansBase e + r`) then all `U` (seq `ansBase e + |D| + r`)), `ansAll I :=
  (finRange E).flatMap (ansE I)`, **`map_head_ansAll`**: the sequence numbers are `range (ansBase I E)`;
* **`p3_answers`** (the equation for `P4`): for every `L0 ~ union I` (the record list on `qX`
  before `sortS`) and every initial scan data `c0`,
  `(jScan ℓ c0 (L0.mergeSort rle)).reverse.mergeSort rle = ansAll I`.
  So after `sortS` (on `qX`), `pJScan` (`qAns := (jScan …).reverse.flatten ++ []`) and `sortS`
  of `qAns` (`A = 4`, records `(jScan …).reverse`), `qAns` holds `(ansAll I).flatten` (first
  answer on top). Helpers for the sorts: `jScan_perm`, `length_of_mem_jScan` (`4`),
  `length_jScan` (`ansBase I E`). No ordering problem was found: `seqOff` matches the hub
  order (`hubNbrs_junc` needs `U, V`, `hubNbrs_link` the end `W`/`V`, `hubNbrs_upd_first` `U`).

## P4 (branch proofs/compiler-p4, in progress)

**Start-state interface** (= end of `p3_good`, after `p0, p1, p1r, p2, p3`; nontrivial, `E > 0`):
`qAns = (ansAll I).flatten`, `qSch = (schRecsUpTo I E).reverse` (p3 does not write stacks 0, 2,
3, 4), empty: stacks `1, 2, 3, 5–11, 14, 15` (qOr/qOr2 empty after `p2`); garbage: `qJunk = 13`,
`qLoc = 0`. Registers not written by `p3` (checked with `#eval`, `wReg r p3 = false` exactly for
`r ∈ {2, 4, 8, 9, 10, 17, 18, 19, 34}`) plus those `p3_good` sets: `rW = W`, `rL = ℓ`,
`rL1 = ℓ+1`, `rE = E`, `rKk = k`, `rKm1 = k-1`, `rK1 = k+1`, `rLB = locBase I`, `rPL = k(ℓ+1)`,
`rTriv = 8` (do not write). `pos = H`. (The case `E = 0`, domains nonempty: `gEdges = []`, only
colors; P2/P3 do not run there, so `p4` must then be run with `rLB = 0` and an empty `qSch`,
`qAns`; the schema loop runs `0` times — `k` is never used.)

**Design.** `p4 = rEps := 0; p4Round; rEps := 1; p4Round`, one lemma `p4Round_good ε` (output
`++ gDesc I ε`, `qAns`, `qSch` restored, scratch stacks empty again). `p4Round`:
1. `moveAllS qSch qS2` (records forward); `rst`; skip `k, ℓ, W`; location loop (`ι` → labels
   `1 + [ι = 0]`, `|D_v|`, push the labels `|D_v|` times on `qSzL`, `skipBlocksS |D_v| (ℓ+1)`;
   counts `rNt += …`); skip `E`.
2. schema loop (`p4Sch`): read arity, `tern`, skip locations, read `|D|`; move the record from
   `qS2` back onto `qSch` (restoring it) copying `orsL` to `qOrsF` (forward), `blkRows, nEnt,
   |coef|` to registers; push `schSizes I e` on `qSzS`; section bases `sumBase, trackBase,
   coefBase` (`PEmitHub`); **section 1** per column (index `r`): read block and bits from the
   input, compute the ranks of its rows (`rowsL_eq`: block part `[c.1]` or `range (k-1)`;
   checksum ranks `chkRk (orsL D) bd blkRows` in one pass over the bits with `qOrsF`) and push
   them on `qRk`, its row count on `qCnt`, `rEB += (k+1) rows`; pop the answers (`U, V, W`
   ternary / `V` binary; pushed to `qA2` for restoring) and push the junction/link edges
   (`hubE_junc`, `hubE_link`, `cposA` = `slotPos_coord_ans`); **section 2** per column (ranks and
   counts reversed to forward order): for `q ≤ k`, for the ranks `ρ` (index `p`): entry
   `t = q n + p`, hub `schBase + |D| colW + 4 (EB + t)`, coef index `q |R| + ρ`
   (`idxOf_coefSteps`, `rank_blk`, `chkRanks_eq`); edges `hubE_upd` / `hubE_updF` (binary first
   entry: pops the `U` answer); skip the permutations (`arity · k(ℓ+1)` numbers via `rPL`).
   Each edge `(u, v)`: push `u`, push `v` on `qE`, `rM += 1`.
3. `moveAllS qSzL qSz; moveAllS qSzS qSz` (sizes in order), `moveAllS qE qE2`, `moveAllS qA2
   qAns`; emit `rNt`; `colorsS qSz` (`rP := 0`); emit `rM`; `emitAllS qE2`.

**Done (no sorry):** `CEmit` (`emitAllS_good`), `CColors` (`repS_good`, `colorsS_loop_good`:
output `++ colorsOf P (stk q)`); list level: `PEmitHub` (`cposA`, **`slotPos_coord_ans`**,
`sort2`/`mergeSort_two`, `hubE`, `hubE_bits2/1`, **`hubE_junc`, `hubE_link`, `hubE_upd`,
`hubE_updF`** with explicit `junE1, lnkE1, updE1, updF1`, `sumBase/trackBase/coefBase`,
`prevBase`), `PEmitSteps` (`stepsC_eq` q-major, `rowsR`, `coefSteps_eq`,
**`idxOf_coefSteps`** = `q |rowsR| + idxOf j rowsR`), `PEmitRank` (`rowsL_eq`, `chkT`, `chkRk`,
**`chkRanks_eq`**, `rank_blk` (= `(range j).countP (PA I e)`), `rank_chk`), `PEmitSch`
(**`schE_eq`**: `gEdges = flatMap schE`, `schE e` = section 1 per column `colE1` ++ section 2
per column and entry), `PEmitSizes` (**`clsSizes_eq`** via `schSizes`, `locSizes`).

Also done: `PEmitBlk` (**`rank_blk_eq`**: block-row rank of `D[r]` (`c.1 < k-1`) is `c.1` if
`blkRows D = k-1`, else `dChg k (blocks of D.take (r+1)) - 1` — the program keeps `dChg` as in
`p2Blk`, `dChg_append`), `PEmitCol2` (`rkL`, `updEnt`, **`colE2_eq`**: update edges of a column
as `(range (k+1)).flatMap q, (rkL I e c).zipIdx` with entry `q n + p`, coef index
`q |rowsR| + ρ`), `P4Edge` (program pieces: `q4E = 1`, `r4M = 36`, `r4Eps = 35`, `r4F/r4V =
21/22`; `pairsRev`, **`EdgeEff`** (+ `trans`, `refl`, `of_frame`), `pE_good`, `pEo_good`,
`cposN`, `ansMode` (`2` for two labels, else `ε · seed`), `cposA_eq` (`cposA = cposN …
(ansMode ε a)`), **`cposS_good`**).

**Remaining (P4, all machine level):** hub emitters (junction label loop over `i < 4` with
`half`/`odd`, `junE1` = sum edge then `sort2` of `cposS` for `U, a` and `V, b`; link; update
`updE1`/`updF1`), column loops (section 1: read block (`rdNumS`), bits loop with `qOrsF`,
`chkRk`, block ranks via `rank_blk_eq`, push ranks/count; section 2 via `colE2_eq`), schema
body (record transfer `qS2 → qSch`, sizes push `schSizes`, bases), location loop
(`locSizes`), round assembly (`clsSizes_eq`, `colorsS_loop_good`, `emitAllS_good`,
`graphDescription_eq_gDesc`), `p4_good`, costs.
**Register pressure (obstruction to watch):** `CR = 40` (`PTriv`). Kept: `rT, rP` (parsing),
`rL, rL1, rKk, rKm1, rK1, rLB, rPL, rTriv`; free for `P4`: the other 30 (re-read `W`, `E` from
the input in each round instead of keeping `rW`, `rE`). Estimated need at the deepest point
(section 2): round 6 (`rEps, rM, rNt, rJ, rE, schema base`), schema ~10 (`tern, |D|, nEnt,
blkRows, |R|, sumBase, trackBase, coefBase, upd hub base, perm-skip count`), column ~9
(`r, EB, n, q, q|R|, p, ρ`, `U` answer `off, mode`), hub ~4 (`i`, flag/value, temp): ≈ 29 — fits
only with care; if not, raise `CR` in `PTriv` (all register facts there are `decide` on
numerals) — not done here.

**Intended statement of `p4_good`** (start states of `pre_good`, merged 3e7afe5): for
`¬ trivSys I`, `hw`, `hk : 1 ≤ k`, `w = wordOf H S` (`16384 (H+S+2) ≤ 2^w`), and `st` with
`st.Bdd w`, `st.pos ≤ H`, `ChainLoc I st` and either `ChainNoSch I st` (`E = 0`) or
`ChainSch I st` (`E > 0`):
`∃ st', Good x w p4 st st' (K (H + S + 1) · nodeCost w) ∧ st'.out = st.out ++ gDesc I 0 ++ gDesc I 1`.
Note on the cost form: `P4` emits `|gDesc| = Θ(S)` words, so its cost cannot be bounded by
`K (H+1)(log₂(H+1)+1) · nodeCost w` alone (when `S ≫ H`); it needs a `cost_conv` variant
`K (H+S+1) · nodeCost (wordOf H S) ≤ K' (H+S+1)(log₂(H+S+2)+1)^2` (from `nodeCost_le_sq`).
`ChainSch` does not export `rKm1 = k-1`, `rK1 = k+1`, `rPL = k(ℓ+1)` (they do survive `p3`,
`wReg r p3 = false`), so `P4` recomputes them (`predS`, `mulS`) or `ChainSch` is extended.
In the `E = 0` case `rLB` is not set by the chain: `P4` must use `locBase I = 0` there
(set `rLB := 0` under `ite (rv rE)`), and the location sizes come from its own location scan
(`qLoc` holds only offsets).

## P4 location part / framing (branch proofs/compiler-p4l)

**Round layout:** `p4Round SCH = p4Loc; ite (rv rE) (p4SzS; SCH) skip; p4Emit`, `p4 SCH =
r4Eps := 0; p4Round SCH; r4Eps := 1; p4Round SCH` (`P4Main`). Modules:
* `P4Rep`: `repPushS_good` / `rep2PushS_good` (push a value / a pair `n` times, running total).
* `P4Emit`: registers `rNt = 4` (total of the class sizes), stacks `qSzA = 14`, `qSzB = 15`;
  `descOf L Es` (= `gDesc` for `clsSizes`, `gEdges`, `gDesc_eq_descOf` is `rfl`);
  **`p4Emit_good`**: from `qSzB = L`, `q4E = pairsRev Es`, `qSzA = []`, `rNt = ΣL`,
  `r4M = |Es|`: output `++ descOf L Es`, `qSzB, q4E` emptied (scratch `rT, rP, rJ, rA`).
* `P4Loc` (`p4LLoop_good`, location loop: `labsN v` pushed `|D_v|` times on `qSzA`, `rNt =
  locOff`), `P4LocPass` (**`p4Loc_good`**: `rst`, skips, `rL1 := ℓ+1`, `rNt, r4M := 0`, loop,
  `moveAllS qSzA qSzB`: `qSzB := locAll ++ qSzB`, `pos = schPos`; `locAll_sum`).
* Schema sizes from a scan (`P4SzPush`, `P4SzRec`, `P4SzRead`, `P4SzLoop`, `P4SzS`):
  registers `rC..rS = 20–27` (`rTq = 24`), scratch stack `qT = 2`; the records are moved
  forward from `qSch` to `qT` and pushed back one by one (restoring `qSch`); per schema read
  arity/`|D|`, skip the rest (`arity·k·(ℓ+1)` permutation words), push `szL` (=`schSizes`,
  `schSizes_eq_szL`); **`p4SzS_good`**: `qSzB := schAll ++ qSzB`, `rNt += Σ schAll`, `pos = H`.
* `P4Round`: `P4Inv` (round-start states), `SchPre`, `p4Keep`, **`SchSpec`** (interface of
  the schema edge part), **`p4Round_good`**; `P4Main`: **`p4_good`**, `p4Inv_of_chain`,
  `p4Z_le` (`p4Z ≤ 4H + 5|ordL|`), **`cost_conv_lin`**
  (`K (H+S+1) nodeCost(wordOf H S) ≤ 7744 K (H+S+1)(log₂(H+S+2)+1)^3`).
**Interface expected from `SCH`** (`SchSpec I w SCH C`): for `ε ≤ 1` and every `st` with
`SchPre I ε w st` (schemas nonempty, `Bdd w`, `pos = H`, `r4Eps = ε`, `r4M = 0`, `rTriv = 0`,
`rW = W`, `rL = ℓ`, `rL1 = ℓ+1`, `rE = E`, `rKk = k`, `rKL = kℓ`, `rLB = locBase`, `qAns`,
`qSch` as in `ChainSch`, all stacks other than `qLoc, qSch, qAns, qJunk, qSzB` empty):
`∃ st', Good x w SCH st st' C ∧ EdgeEff st st' (gEdges I ε) ∧ ∀ r ∈ p4Keep, st'.env r = st.env r`
with `p4Keep = [rTriv, rW, rL, rE, rKk, rKL, rLB, rNt]` (`EdgeEff` keeps all stacks but `q4E`,
in particular `qAns, qSch` restored and `qSzB` untouched). `ε` enters as `(ε : ZMod 2)`.
The schema part may use every register except `p4Keep` (and must not touch stack 15).

## P4 schema part (branch proofs/compiler-p4s, in progress)

Target: `p4Sch_spec : SchSpec I w p4Sch C` (see above). Registers (`P4SchLab`): `r4PL = 34`,
schema data `r4SB 5, r4Tn 6, r4D 11, r4BR 12, r4R2 13 (= 2|rowsR|), r4SumB 14, r4TrkB 15`,
column loop `r4Dist 17, r4Prev 18 (section 2: coefBase), r4H 20, r4SP 23, r4TP 24, r4K 25`,
column scratch `rc1..rc8 = 26–30, 37, 32, 33` (`rc6 = 37` since `rKL = 31` is kept); plus
`rT, rP`, `r4F, r4V` (`cposS`), `r4M`. Stacks: `qS2 2` (records forward), `qA2 3` (consumed
answers), `qOrsF 5 / qOrsB 6` (OR bits, also the section-2 temp), `qRk 7 / qRkF 8` (rank codes
`rcode ρ = 2ρ+1` per column, terminated by `0`).
Program per schema: read arity/`tern`, skip locations, read `|D|`, move the record `qS2 → qSch`
(OR bits forward to `qOrsF`, `blkRows, nEnt, |coef|`), section bases; **section 1** per column
(`p4C1`: block (`p4Hd`, `dist1` = running `dChg - 1`), block ranks (`p4Blk`, `blkCodes`), bit
pass (`p4Bits`, `chkRk`), last track (`p4LT`), junction (`c1Jun`, `jLabs`), link (`c1Lnk`,
`lLabs`), advance); `moveAllS qRk qRkF`, skip the permutations; **section 2** per column
(`p4C2`: start answer for binary schemas (`c2Ans`), `q ≤ k` loop (`p4Qs`/`p4QB`: rank loop
`p4Rks` over the codes, entry `p4Ent` = `fLabs`/`uLabs`, codes restored via `qOrsB`), drop
the codes (`p4Drop`)). Edge lists in numbers: `junL, lnkL, updL, updFL, entE, rksE, col2E,
col1E`; `EE`/`EM` = `EdgeEff` restricted to `q4E`/`r4M`.
**Interface target** (coordinator): `p4Sch_spec : SchSpec I (wordOf (H I) (sizeParameter I)) p4Sch
(K (H + S + 1) · nodeCost w)` for `3 ≤ k`, `1 ≤ ℓ`; `SchPre` starts at `pos = H` (so `p4Sch`
must `rst` and skip to `schPos` itself), keeps `p4Keep` (`rKL = 31`, `rNt = 4`), stack 15
untouched. The cost of the schema part is linear (`O(H + locBase)` word operations, no log).
**Done (no sorry, imported):** `P4SchLib` (`Good.loop_idx(C)`, `lf`/`scost`/`good_lf`),
`P4SchLab`/`P4SchLab2`/`P4SchHub` (label and hub emitters, `pAns_good`), `P4SchEnt`
(`p4Ent_good`), `P4SchRk` (`EE`, `p4Rks_good`), `P4SchQ` (`p4QB_good`), `P4SchC2` (`p4Qs_good`,
`p4Drop_good`), `P4SchC2b` (**`p4C2_good`**: one column of section 2), `P4SchBits`
(**`p4Bits_good`**), `P4SchC1` (`p4Hd_good`, `p4Blk_good`), `P4SchC1b` (`p4LT_good`,
`c1Jun_good`, `c1Lnk_good`, `p4Adv1_good`), `P4SchC1c` (`EM`, **`p4C1_good`**: one column of
section 1), `P4SchGlue` (**`codesC_eq`**, `dist1_eq`, `slot_ans`, `memU/V/End`,
**`colE1_eq`**), `P4SchGlue2` (**`col2_eq`**), `P4SchAns` (**`ansE_flatten`**: `a1C`, `a2C`),
`P4SchL1` (`cL`, `entB`, `codesL`, `distR`, column facts), `P4SchL1b` (`p4S1`, invariant
`L1Inv`, `aOff_le`, `ansRec_ok`, `sec_bounds`), `P4SchL1c` (`L1Fix`, `L1Bnd`, `p4S1_step`),
`P4SchL1d` (`p4S1_loop` via `Good.loop_var`, `L1Inv_zero`, `entB_all`, **`p4S1_good`**).

### P4 schema part / section 1 loop (`P4SchL1d`, done)

```
lemma p4S1_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (hk : 2 ≤ k) (hE : I.schemas ≠ [])
    (ε : ZMod 2) (e : Fin I.schemas.length) (R : List ℕ) (restx : List Bool) (s0 : NSt CR CQ)
    (hF : L1Fix I w x ε e restx s0) (hB : L1Bnd I w e s0)
    (hMe : ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2).length ≤ 3 * (ordL I).length)
    (eK : s0.env r4K = 0) (eDi : s0.env r4Dist = 0) (eH : s0.env r4H = schBase I e)
    (eSP : s0.env r4SP = sumBase I e) (eTP : s0.env r4TP = trackBase I e)
    (hV : s0.env r4V < 2 ^ w) (hbd : s0.Bdd w)
    (hA : s0.stk qAns = (cL I e).zipIdx.flatMap (a1C I e) ++ R) :
    ∃ s', Good x w p4S1 s0 s' (2100 * ((encodeNats ((cL I e).flatMap cdesc)).length +
        nEnt I e + (cL I e).length + 1) * Ex.nodeCost w) ∧
      EM s0 s' ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2) ∧
      s'.stk qRk = ((cL I e).flatMap fun c => codesL I e c ++ [0]).reverse ++ s0.stk qRk ∧
      s'.stk qAns = R ∧
      s'.stk qA2 = ((cL I e).zipIdx.flatMap (a1C I e)).reverse ++ s0.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qRk → q ≠ qAns → q ≠ qA2 → s'.stk q = s0.stk q) ∧
      s'.env r4K = (cL I e).length ∧ s'.env r4Dist = distR I e (cL I e).length ∧
      s'.env r4H = schBase I e + (cL I e).length * colW I e ∧
      s'.env r4SP = sumBase I e + 2 * (cL I e).length ∧
      s'.env r4TP = trackBase I e + 2 * nEnt I e ∧ s'.env r4V < 2 ^ w ∧ s'.Bdd w ∧
      s'.pos = s0.pos + (encodeNats ((cL I e).flatMap cdesc)).length ∧ s'.out = s0.out ∧
      ∀ reg, reg ∉ c1W → s'.env reg = s0.env reg
```
`L1Fix` (`P4SchL1c`): `x.drop s0.pos = encodeNats ((cL I e).flatMap cdesc) ++ restx`, `rL = ℓ`,
`rKk = k`, `r4BR = blkRows (cL I e)`, `r4Tn = tnN (isTern (sch I e))`, `rLB = locBase I`,
`r4Eps = ε.val`, `r4D = |cL I e|`, `qOrsF = orsL (cL I e)`, `qOrsB = []`, `s0.pos ≤ |x|`.
`L1Bnd`: `16 (H + |ordL| + 1) ≤ 2^w`, `k(ℓ+1) ≤ H`, `|cL I e| ≤ H`,
`ansBase I e + 3 |cL I e| ≤ 3 H`, `r4M + 3 |ordL| + 16 < 2^w`. `EM s0 s' Es` = `q4E` gets
`pairsRev Es` pushed and `r4M += |Es|`. Glue for the schema body: the edges are the first part
of `schE_eq`; the answers the first part of `ansE_flatten`; after the loop `r4H =
schBase + |cL|·colW` (= the update-hub base of `schE_eq`), `r4TP = coefBase` (`sec_bounds`).

### P4 schema part / section 2 loop (`P4SchL2c`, done)

**Section 2 loop (done, no sorry):** `P4SchL2` (`p4S2 = loop (r4K < r4D) p4C2`, `updBase =
schBase + |cL|·colW`, `colE2`, `L2Fix`, `L2Bnd`, `L2Inv`, `coef_bound`, `codesL_lt`,
`ans2_hyp`), `P4SchL2b` (`p4S2_step`), `P4SchL2c` (`schE_eq2`: `schE e = flatMap colE1 ++
(cL e).flatMap colE2`, and **`p4S2_good`**, via `Good.loop_var` with potential
`coefBase - r4TP`). Exact statement:
```
theorem p4S2_good (hw : 2 ≤ w) (hk : 2 ≤ k) (ε : ZMod 2) (e : Fin I.schemas.length)
    (R Q : List ℕ) (s0 : NSt CR CQ) (hF : L2Fix I x ε e s0) (hB : L2Bnd I w ε e s0)
    (h0R : s0.stk qRkF = (cL I e).flatMap (fun c => codesL I e c ++ [0]) ++ Q)
    (h0B : s0.stk qOrsB = [])
    (h0A : s0.stk qAns = (cL I e).zipIdx.flatMap (a2C I e) ++ R)
    (e0K : s0.env r4K = 0) (e0H : s0.env r4H = updBase I e)
    (e0TP : s0.env r4TP = trackBase I e) (e0SP : s0.env r4SP = sumBase I e) (hbd : s0.Bdd w) :
    ∃ s', Good x w p4S2 s0 s' (3200 * Ex.nodeCost w * nEnt I e +
        (cL I e).length * condCost w (.lt (rv r4K) (rv r4D)) +
        condCost w (.lt (rv r4K) (rv r4D))) ∧
      EE s0 s' ((cL I e).flatMap (colE2 I ε e)) ∧
      s'.stk qRkF = Q ∧ s'.stk qOrsB = [] ∧ s'.stk qAns = R ∧
      s'.stk qA2 = ((cL I e).zipIdx.flatMap (a2C I e)).reverse ++ s0.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qRkF → q ≠ qOrsB → q ≠ qAns → q ≠ qA2 → s'.stk q = s0.stk q) ∧
      s'.env r4K = (cL I e).length ∧ s'.env r4H = updBase I e + 4 * nEnt I e ∧
      s'.env r4TP = coefBase I e ∧ s'.env r4SP = sumBase I e + 2 * (cL I e).length ∧
      s'.Bdd w ∧ ∀ reg, reg ∉ c2W → s'.env reg = s0.env reg
```
where `L2Fix I x ε e s0`: `rKk = k`, `r4Tn = tnN (isTern (sch I e))`, `rLB = locBase`,
`r4Eps = ε.val`, `r4D = |cL|`, `r4R2 = 2 |rowsR I e|`, `r4Prev = coefBase`, `pos ≤ |x|`;
`L2Bnd I w ε e s0`: `16 (H + |ordL| + 1) ≤ 2^w`, `k(ℓ+1) ≤ H`, `|cL| ≤ H`,
`ansBase e + 3|cL| ≤ 3H`, `r4M + |(cL).flatMap colE2| + 12 nEnt + 12 < 2^w` (same first four
as `L1Bnd`). `qRkF` holds the codes forward as `moveAllS qRk qRkF` leaves them (section 1
pushes `(flatMap (codesL ++ [0])).reverse` on `qRk`); `qAns` starts with the section-2 answers
`(cL).zipIdx.flatMap a2C` (`ansE_flatten`); `EE` keeps `pos` and `out`.
`c2W = [rc1..rc8, r4TP, r4H, r4F, r4V, r4M, r4Dist, r4SP, r4K]`.
**Remaining:** the schema
body (read arity → `r4Tn`, skip locations, read `|D|` → `r4D`; record transfer `qS2 → qSch`
with `orsL` forward on `qOrsF` (via `qOrsB`), `r4R2 = 2|rowsR| = 2(blkRows + Σ ors)`,
`r4BR = blkRows`, `nEnt`, `|coef|`; bases `r4H = schBase`, `r4SP = sumBase`, `r4TP =
trackBase`, `r4K, r4Dist := 0`; `p4S1`; `moveAllS qRk qRkF`; `moveAllS qOrsF qJunk`; skip the
`arity·k(ℓ+1)` permutation words; `r4Prev := coefBase` (= `r4TP` after section 1), `r4SP :=
sumBase`, `r4TP := trackBase`, `r4K := 0` (`r4H` is already `updBase`); `p4S2`; next
`schBase`); the prefix of `p4Sch` (`rst`, skip `k, ℓ, W`, the location section
(`skipBlocksS`), `E`; `r4PL = k(ℓ+1)`; `moveAllS qSch qS2`); the schema loop over `rJ < rE`;
the suffix `moveAllS qA2 qAns`; the edge list via `gEdges_eq_schE`, `schE_eq`,
`ansE_flatten`; the cost in the form `K (H + S + 1) nodeCost w` (`locBase_le`).

## Chain P0–P3 (branch proofs/compiler-chain, `Compiler/PChain`, `Compiler/PChainSize`)

Program `pre = p0; ite (rv rTriv) skip (p1; ite (rv rE) (p1r; p2; p3) skip)` (`preNT`,
`preSch`). `p1r` needs `k ≤ H` (only for `E > 0`), `p2`/`p3` need a schema, so for a
nontrivial system with `E = 0` only `p1` runs (then `gDesc` has no hubs and no edges: `P4`
needs only the location data). **`pre_good`** (`hw : 2 ≤ w`, `hk : 1 ≤ k`,
`hS : 16 (H + locBase I + 1) ≤ 2^w`): `∃ st', Good x w pre (NSt.zero CR CQ) st'
(210000 (H+1)(log₂(H+1)+1) · nodeCost w)` (so `pre.Fits` from the zero state is included) with
`st'.out = []`, `st'.Bdd w`, `st'.pos ≤ H`, and
* `trivSys I → st'.env rTriv = 1 ∧ ∀ q, st'.stk q = []` (`P4` emits `[0,0,0,0]`, `gDesc_triv`);
* `¬ trivSys I → ChainLoc I st'`: `rTriv = 0`, `rW = W`, `rL = ℓ`, `rE = E`,
  `qLoc = (locOffs I).reverse`;
* `¬ trivSys I → I.schemas = [] → ChainNoSch I st'`: `rOff = locOff I W`, `pos = schPos I`,
  every stack other than `qLoc` empty;
* `¬ trivSys I → I.schemas ≠ [] → ChainSch I st'`: `qAns = (ansAll I).flatten`,
  `qSch = (schRecsUpTo I E).reverse`, every stack except `qLoc, qSch, qAns, qJunk` empty,
  `rLB = locBase I`, `rL1 = ℓ + 1`, `rKk = k`, `rKL = k ℓ`, `rCnt = |locRecs I|`,
  `rSB = |reqs I|`, `pos = H`. (`rOff` is overwritten by `p1r`; `qJunk` holds garbage.)
Helper: `p1_rL1` (`p1` leaves `rL1 = rL + 1`, via `exec_set_succ` and frames).
Sizes (`PChainSize`): `wordOf H S = 8 (log₂(H+S+2) + 1)` (`a = 8`), `two_pow_word`
(`2^14 (H+S+2) ≤ 2^wordOf`), `locBase_le` (`locBase ≤ |ordL| ≤ 16 S`, `k ≥ 2`), **`word_hS`**
(`16 (H + locBase + 1) ≤ 2^(wordOf H S)`); **`cost_conv`**: `K (H+1)(log₂(H+1)+1) ·
nodeCost (wordOf H S) ≤ 7744 K (H+S+1)(log₂(H+S+2)+1)^3`. Final assembly:
`prog = pre; p4`, apply `machine_of_program` with `a = 8`, `e = 3` (`bitLength I = H I`).

## Remaining work (in order)

3. (done: `sortS_good`; queue helpers only if item 4 needs them.)
4. **The compiler program**, emitting `gDesc I 0 ++ gDesc I 1` (`OutDesc.encodeGraphPair_eq`):
   triviality check (no schema, all domains empty: emit `0,0,0,0`; `k, ℓ` are skipped, not
   read, since they may be exponential in `H` there); locations pass (stack of
   `(v, i, b₀ … b_{ℓ-1})` records with `locStart v`, `ι(v)`); schema pre-scan (sizes
   `schSize`, `colW`, `nEnt`, `|coefSteps|`, union of the set bits for the coef ranks);
   request pass (per column and argument the key `(u, f(i), bits of b + δ_i)` with a sequence
   number); `sortS` / merge-join with the locations / `sortS` by sequence number; emission of
   `clsSizes` sum, `colorsOf`, `|gEdges|` (count while pushing the edges to a stack, then
   emit) and the edges, for `ε = 0, 1`. Suggested split: one module per pass, each with a
   `Good` spec against a list function of `I`, composed with `Good.seq`.
5. **List-level correctness (rest)**: only the per-pass correctness of the program against
   `gDesc` remains (the list-level target is done, see `OutDesc` above).
6. **Costs**: the wrapper is done (see below); what remains is, for the program `c` of
   item 4 with `w = a (L + 1)` (`L = log₂(H + S + 2)`): `c.Fits`, `exec … .out =
   gDesc I 0 ++ gDesc I 1` and `c.cost ≤ K (H + S + 1)(L + 1)^e` for some `e ≥ 1`
   (all program costs are `O(#word operations · nodeCost w)` and `nodeCost_le_sq` bounds
   `nodeCost w` by `64 (a + 3)² (L + 1)²`, so `O((H + S)(L + 1))` word operations suffice
   with `e = 3`, which covers the `log` factor of `sortS`). Then
   `machine_of_program` + `matrix_compiler_of_machine` give the concept statement; rewrite
   `Matrix/Main.lean` (frontmatter `conclusion: Lax119563.MatrixCompiler.matrix_compiler`)
   as these two applications.

   Done for item 6 (`Compiler/Final`, `OutLen`, `Bound`): `compileM I := (reGraph I (ordL I)
   0, reGraph I (ordL I) 1)`, `compileM_clauses`, `encode_compileM`,
   **`matrix_compiler_of_machine`** (the concept statement from a machine emitting
   `encodeNats (gDesc I 0 ++ gDesc I 1)` within the bound); `length_out_le`, `gDesc_le`,
   `length_ordL_le` (`n ≤ 16 S`); `nodeCost_le_sq`, `out_width`, `final_bound`,
   `one_le_bitLength`, `succ_pow_le`, **`machine_of_program`** (branch proofs/compiler-bound:
   for any exponent `e ≥ 1`, the machine of a `CStm` with the three facts above computes the
   output within `((2^(e+1) + 80)(K + 3400) + 30)(H + S) L^e`).
-/
