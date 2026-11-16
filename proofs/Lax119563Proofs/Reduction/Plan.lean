/-!
# Plan of the `Reduction` area

Goal: `Lax119563.TimeReduction.time_reduction`.

## Mathematical assembly (`Assembly`, done)

For a register program `P` with `s ≥ 2` registers and a query, the matrix graphs
`matrixGraph (P.compile p₀ a₀) ε` are distinguished by `(s+1)`-WL iff the query accepts
(`distinguishes_matrixGraph_iff`), and have `O((s+1) 2^ℓ w + (s+1)² 2^ℓ ℓ (r+1))` vertices
(`matrixGraph_n_le`); with the bounds of `Circuits.time_simulation` this is `O(n log^6 n)`.

## Transfer (`Transfer`, done)

`duplicatorWins_iff_of_corr`: two pairs of graphs (each pair with common colors) whose
non-junk parts correspond by a bijection preserving adjacency and color equality, where junk
vertices are isolated and carry colors used by no non-junk vertex, are equivalent for the
bijective pebble game.

## Machines from register programs (`Bits`, `HProg`, `HStack`, `HRoutines`, `HHeads`,
## `HCompile`, `HMachine`, done)

The reduction machine is written in a small language `HProg R` (registers `Fin R` holding
naturals; instructions `clr one dbl half copy add lt emit rd rst`, `seq`, `ite`, `loop` with
conditions on the zero/parity view of the registers). Semantics `HRuns x w p st st' t` with a
word size `w`: every primitive requires the registers it touches to stay `< 2^w` and costs
`unitCost w = 64 (w + 1)`; `rst` (input cursor back to `0`) costs `unitCost w * (pos + 1)`.
The output of a run is the list `st'.out` of emitted numbers.
`HProg.computesWithin`: if `p` runs from the zero state to a state with cursor `0`, and
`|x| ≤ |encodeNats out|`, then `p.machine` (deterministic) computes `encodeNats out` from `x`
within `t + 20 |encodeNats out| + 4` steps. (Stack layout: input tape = unread input, so the
head of tape 0 follows the cursor; registers are binary, least significant digit on top.)

So the remaining work is purely about `HProg` programs and their semantics on `ℕ`.

`HLib` (done): `HLe` (runs within a cost) with seq/ite/loop lemmas, `loop_seq` (loop along
a sequence of states), `inc`, `setC`, `skip`, and counting loops `forUp` (`forUp_spec`).

## Register program (done: `Locs`)

`nodup_allLocs`, `dedup_allLocs`: the commands of `timeProgram` are exactly
`progCmds ℓ (allLocs M H) (moves M x s ℓ H)`, i.e. the moves of the locations of `allLocs`
in list order, so `timeProgram`, `timeProgram_graphs` (Assembly) and all Circuits bounds are
used as they are. Every command has an executable source (no moves at `accept`/`reject`),
so every schema domain contains the whole checksum block `{s} × 𝔽₂^ℓ`.

## Output graph (math layer)

Done (`OutGraph`, `OutCorr`, `OutEdges`, `OutEdgeList`), for any implicit parity system
`I` with `s + 1` blocks:
* `num`, `classNum`, `famNum`, `nOut`; `num_injective`, `num_lt` (on valid names);
* `outGraph I ε` and `distinguishes_outGraph_iff` (via `corr : Corr (matrixPair I)
  (outPair I)` and `duplicatorWins_iff_of_corr`);
* `hubNbrs I ε a` (valid neighbors of a hub, in output order) and `adjN_iff_hubNbrs`;
* `edgeList_outGraph`: the edge list is the concatenation over `u < nOut` of
  `(upNbrs I ε u).map (u, ·)`, with `upNbrs_hub` (`= (hubNbrs I ε a).map num` for a valid
  hub `a`, needs `1 ≤ s` and `TernOrdered I`), `upNbrs_nonhub`, `upNbrs_invalid`.
Done: `ternOrdered_compile` (`TernOrder`) for every compiled register program.
To do: explicit (decodable)
descriptions of `OutValid z` and of `hubNbrs` for the program: decode `z` into
`(lab, b, i, F)`, `F` into the kind and `(e, σ)` / `v`, and evaluate `ClsValid` (domain
membership via the command guard, `ent σ c`), `LabelOK` and the neighbor classes
(`trackAt` by `prevStep`, `permU` shift) from the command data.

## Output graph (design notes)

Let `I = P'.compile p₀ 0`, `E = I.schemas.length`, `W = I.numLocations`, `NS = numSteps`.
Family offsets (hubs first): `upd` `[0, E·NS)`, `junc` `+E`, `link` `+E`, then non-hubs
`coord` `+W`, `sum` `+E`, `track` `+E·NS`, `coef` `+E·NS`; total `FN = 3 E NS + 3 E + W`.
Index within a family: `e·NS + σ`, `e`, or the location `v`. The class number of a class is
`(i + (s+1) F) 2^ℓ + regVal b` for its coordinate `c = (i, b)` (`(0, 0)` for `coef`), and a
name `(X, l)` gets `num = lab l + 4 · classNum X` with `lab (a, b) = a + 2 b`.
Output graphs `G'_ε` on `Fin N'`, `N' = 4 · 2^ℓ (s+1) FN`: slot `z` is valid iff it is `num`
of a valid name; adjacency = `adjN ε` of the names; color `2 (z / 4) + 2` if valid, else `1`.
`Corr` (Transfer) between `matrixGraph I ε` (no junk; `vertexList` lists each valid name
once) and `G'_ε` (junk = invalid slots): `i ↦ num (vertexList I)[i]`.

Edge list: hubs are numbered below non-hubs, so `edgeList G'_ε` is, for each valid hub slot
`u` in increasing order, its valid neighbors in the static order
`upd: trackAt < track σ < coef`, `junc: coord locU < coord locV < sum` (`locU < locV` for all
ternary schemas: slot codes `a1 < b1`, `a2 < b2`, `out1 < out2`, detector `u1 < u2`),
`link: coord locEnd < trackAt N` (`trackAt _ _ N` is never the start class since every
column has a nonzero entry, `k ≥ 3`). A neighbor of a hub with label `l` in class `Y` has
the label prescribed by `hubB` minus `ε · initBit Y`; it is valid iff that label is `0` for
singleton `Y` (`prog accept`, `det out`).

Structural facts needed: `permU` is `updatePerm (toUpdate mask)` for the first two binary
schemas of an assignment gadget (`(i, b) ↦ (i, b + δᵢ)`, `δ_s = Σ δᵢ`) and the identity
otherwise; `permV = permEnd = id`; `coef e σ` exists for all `σ < NS`; domain of a command
schema: `{s} × 𝔽₂^ℓ ∪ {(i, b) | i < s, g i (regVal b)}` for its address guard `g`
(`fieldGuard`, `hitGuard`, `missGuard`, or the detector guard `b = 0`).

## Reduction program: structured-statement layer (done)

* `rd r` now distinguishes the end of the input: `inBit x pos = rdVal (x.drop pos)` is `0`
  at the end, else the bit plus one (`HProg`, `HRoutines.hRdA`, `HCompile`). Without this
  no `HProg` can compute `|x|` (it could not tell `x` from `x ++ [false]`).
* `HFrame`: syntactic writes/emits/cursor moves (`HProg.wr/em/mv`) with frame lemmas;
  `HRuns.bounded` (all registers stay `< 2^w`, needs `2 ≤ w`).
* `SProg`: expressions `Ex R` (`var, const, add, lt, half, odd`) compiled into scratch
  registers (`Ex.code_spec`). User registers `ur D r`, scratch `sc R D k` in `HProg (R+D+1)`.
* `SStm`: statements `Stm R` (`skip, set, emit, seq, ite, loop i lim body,
  loopX i lim xb body` (sets `xb := inBit x i` each iteration), `len r` (`r := |x|`)) with
  a *total denotational semantics* `Stm.exec x c env : valuation × emitted list`, a cost
  bound `Stm.cost x w c env`, `Stm.Fits` (values `< 2^w`), `WF`, `depth`, and the compiler
  `Stm.code R D` with `Stm.code_spec`.
* `SLib`: `Good x w c env out T` (fits, emits `out`, cost `≤ T`) with rules `Good.seq/ite/
  set/emit/len/loop/loopX` (loop bodies are specified for every valuation with the right
  counter agreeing with the initial one on registers the body does not write: the emitted
  list of a loop is `(range L).flatMap g`); `Stm.exec_frame`, `Stm.runLoop_inv`;
  `Stm.computesWithin`: `WF`, `depth ≤ D`, `Good x w c 0 out T`, `|x| ≤ |encodeNats out|`
  give `ComputesWithin (c.code R D).machine x (encodeNats out) (T + 20 |…| + 4)`.

So from now on everything is pure mathematics about `Stm.exec` (no runs).

## Remaining work (in order)

1. Arithmetic library on `Stm` (file `SArith`): `mul` by repeated addition (`O(a)`
   iterations, fine for polylog values), `shl` by a runtime amount (`x·2^k`, `k` doublings),
   truncated subtraction (count up), `div/mod` by a runtime value (count), bit test
   `testBit v p` (`p` halvings then `odd`), XOR of two `ℓ`-bit values (bit loop with a power
   register), `eq`, `and/or/not` on `0/1` (`lt` tricks). Each as a `Stm` with a `Good`
   lemma and an exact `exec` value lemma (via `runLoop_inv`).
2. Parameters: `n := |x|` (`len`), `L := log₂ n` (loop), `ℓ = L + C₀ + 4`, `P = 2^ℓ`,
   `H = sℓ - 2`, radix `H + 1 + cM`, `NS = (s+2)(s+ℓ)`, `numLoc`, `r` (command count, by a
   counting run of the enumerator), `E = Σ (4 or 9) + 4`, `W = numLoc + 8r + 4`,
   `famCount`, `nOut`, and the edge count (counting run of the edge loop).
   Word size: `w = C·(log₂ n + 1)` chosen in the proof so that all values `≤ nOut²` fit.
3. Schema descriptors (math): for `I = (timeProgram M s C₀ x).compile (timeQuery …) 0`
   describe `sch I e` by numbers: `isTern`, `locU/locV/locEnd` (location numbers:
   `prog p ↦ code p`, `slot j t ↦ numLoc + t + 8j`, `det t ↦ numLoc + 8r + t`, see
   `TernOrder.loc_slot_val`), `permU` shift mask (`fieldMask` of the move for the first two
   schemas of an assignment gadget, else `0`), guard kind + parameters. Prove
   `(i, b) ∈ dom I e ↔ i = s ∨ guard i (regVal b)` and the `permU.apply` formula
   (`regVal (b + δᵢ) = regVal b ^^^ field mask (iℓ) ℓ`, checksum block: XOR of all fields).
   Every command source is executable (`moves accept = moves reject = []`).
4. Command enumerator (program + proof): nested loops in `allLocs` order (`d, u` runtime,
   constant fields unrolled at the Lean level), `moves` case analysis with runtime tests,
   body parameterised by a per-schema statement; prove its output is
   `(compiledSchemas).zipIdx.flatMap (body output)`. Consider a generic "template" proof.
5. Per-family bodies (kinds `upd, junc, link, coord, sum, track, coef`, then `i ≤ s`,
   `b < 2^ℓ` via `loopX` to get `x[b]` for `hitGuard`, `lab < 4`): colors
   `outColor z = if OutValid z then 2(z/4)+2 else 1` (z and z/4 are running counters) and,
   for hubs, the numbers of `hubNbrs` (`trackAt` via `prevStep` by a scan over `σ' < σ`,
   `permU` by XOR, multiplication by `2^ℓ` by shifting). Math lemmas: decodable
   `OutValid (num (X,l)) ↔ ClsValid X ∧ LabelOK X l` per kind, `ent σ c` formula
   (row `σ % (s+ℓ)`), `coef` always valid.
6. Assembly: `graphDescription (outGraph I ε) = nOut :: colors ++ m :: edges` with
   `edgeList_outGraph`, `upNbrs_hub/nonhub/invalid`; `distinguishes_outGraph_iff`,
   `timeProgram_graphs` (size), `Stm.computesWithin`; final file with the Lax frontmatter
   (`conclusion: Lax119563.TimeReduction.time_reduction`).
-/
