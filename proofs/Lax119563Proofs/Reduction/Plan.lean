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

## Generators: programs with list semantics (done: `XLang`, `XSpec`, `GLang`, `GSpec`,
## `GMachine`)

Writing the reduction directly as `Stm` would require frame reasoning about registers in
every proof. Instead there is a stack language whose semantics is a *pure list function*,
compiled once and for all:
* `Xp` (`XLang`): expressions over a stack `ρ : List ℕ` (`var i` = `ρ.getD i 0`), with
  `add, lt, half, odd` and loop-based `mulB a b k = a * (b % 2^k)`, `shl a k = a * 2^k`,
  `shr a k = a / 2^k`, `xorM a b k = (a ^^^ b) % 2^k` (cost ~ value of `k`). `Xp.eval`,
  `Xp.Fits B ρ` (all values `< B`, plus `a 2^k < B` for `mulB/shl`, `2^k < B` for `xorM`),
  `Xp.cost` (units of `κ w = 32 nodeCost w`). `Xp.spec` (`XSpec`): the compiled statement is
  `Good` and leaves the value in the target register. No subtraction yet (add a `sub`
  constructor via `SArith.subS` if needed, or count with `Gn.count`).
* `Gn` (`GLang`): `skip, emit e, seq, ite c g h, bind e g` (push), `loop lim g` (pushes
  `L, k`), `loopX lim g` (pushes `L, k, inBit x k`), `len g` (pushes `|x|`), `log e g`
  (pushes `Nat.log 2 e`), `count g h` (runs `g` with a `0` pushed, pushes the *length of its
  output* and runs `h`). Semantics `Gn.out x g ρ` is a plain recursive list function, e.g.
  `out (loop lim g) ρ = (range L).flatMap fun k => out g (ρ ++ [L, k])`; `Gn.Fits x B g ρ`,
  `Gn.cost x g ρ` likewise.
* `Gn.spec` (`GSpec`) and `Gn.computesWithin` (`GMachine`): for any `g` (independent of
  `x`) with `g.need ≤ R`, `g.WFX` (no `loopX/len` inside `loopX` bodies),
  `g.Fits x B []`, `2 B ≤ 2^w`, `2 ≤ w`, `|x| ≤ |encodeNats (g.out x [])|`:
  `ComputesWithin (Gn.machine R g) x (encodeNats (g.out x [])) (κ w * g.cost x [] + 20 |…| + 4)`
  with `Gn.machine_deterministic`.

So the remaining work is: write one generator `prog` (depending only on `M, s, C₀`), prove
`prog.out x [] = graphDescription G₀ ++ graphDescription G₁` (pure list mathematics),
`prog.Fits x (2^(w-1)) []` and `prog.cost x [] ≤ C n L^c'` with `w = O(log n)`.

## Remaining work (in order)

A. Generator toolkit (done: `GTools`): `Xp.eq/not/and/or/mulC/pow2` with `eval` lemmas,
   `Gn.seqL/when/dispatch` with `out_seqL/out_when/out_dispatch`, `fits_*`, `cost_*_le`
   (uniform bounds for loops/dispatch), `Xp.Small W` (values `< 2^W`, loop counts `≤ W`)
   with `Small.fits : Fits (2^(2W))` and `Small.cost_le : cost ≤ size (W + 3)`.
   Pitfall: `simp only [Xp.eval]` on an `if` over `Xp` values keeps the old `Decidable`
   instance and then `split_ifs`/`rw [if_pos]` fail; state the unfolded form with `show`
   first (see `eval_eq_const`).
B. Code-ordered verifier program (done: `CodeOrder`): `decodeLoc`, `locsByCode`,
   `timeProgram'`, `timeQuery'`, `timeProgram'_accepts_iff`, `time_simulation'`,
   `timeProgram'_graphs` (use this program from now on), `verifierCmds'_eq` (the command
   list is `(range numLoc).flatMap` of the moves of the decoded locations).
   The index `j` of a command is the number of commands at smaller codes / earlier moves:
   compute it with `Gn.count` over the code space (polylog² overhead is fine). Same for
   schema indices `e` (4 per assignment, 9 per fork). `Xp` has no subtraction: use
   `count` (`a - b = #{t < a | b ≤ t}`) or add an `Xp.sub` constructor via `SArith.subS`
   (each `Xp` constructor needs a case in `XLang/XSpec/GTools`).
E'. Schema data (started: `SchemaData`): `mem_guardDomain_toGuard` (block `< s`: the address
   guard on `regVal b`; block `s`: `executable`), `updatePerm_toUpdate_apply` (block kept,
   `regVal` XOR `shiftVal s ℓ m i` = `field m (iℓ) ℓ` or `xorFields`), `commandSchemas_assign/
   fork`, `loc_prog_val` (with `TernOrder.loc_slot_val/loc_det_val`). Useful formulas for the
   bodies: bit `j` of `v` with `j = k + t - iℓ` is `odd (shr (shl v (iℓ)) (k + t))` (no
   subtraction); `field (2^H) (iℓ) ℓ = xorM (shr (pow2 H) (iℓ)) 0 ℓ`; `ent` (`OutDecode.ent_eq`)
   by splitting the step loop `σ = q (s+ℓ) + j` into `j < s` (static) and `j = s + j'`;
   `prevStep c σ + 1 = #{σ' < σ | some σ'' ∈ [σ', σ) has ent ≠ 0}` (a nested `count`);
   `hitGuard` on register `0` needs `cfgCell (init M x) ν v` from `inBit x v` (`loopX`).
C. Symbolic moves (done: `GEnum`, `SymLoc`, `SymMoves`).
   * `GEnum`: `Xp.Bnd n e` (reads only levels `< n`) with `Xp.eval_append`; `Xp.mul a b :=
     mulB a b b` (exact product, cost ~ value of `b`, Fits needs `a 2^b < B`); `Gn.bindL`
     (push a list, `out_bindL`), `Gn.bindSub n a b g` (push truncated `a - b` by `count`,
     `out_bindSub`; used instead of an `Xp.sub` constructor), `flatMap_range_mul`.
   * `SymLoc`: `finH H v = ⟨min v H, _⟩`; `SLoc M` (locations with runtime fields `Xp`),
     `SLoc.eval H ρ`, `SLoc.codeX R HX` (location number; runtime fields clamped with
     `minX`, so `eval_codeX` needs only `R ↦ radix M H`, `HX ↦ H`); `SMv M s`
     (`step/fork/hit/miss`), `SMv.eval` to a `Move`, `SMv.recX R HX`: eight numbers
     `[fk, mask, q1, q2, gk, g1, g2, g3]` (`fk` 0 assign / 1 fork; mask
     `(q ^^^ v) * 2^k`; targets; guard `gk` 0 `fieldGuard ℓ g1 g2 g3`, 1 `hitGuard ν c` with
     `g1 = ν`, `g2 = encCV c`, 2 `missGuard i` with `g1 = i`). `CmdDesc`/`GDesc` state this
     for an `ACmd`; `SMv.desc` proves it.
   * `SymMoves`: `RVals` (expressions for `d, u, d-1, u-1, H-d-1, H+2-d, H`, `RVals.Ok`),
     `SKind M` (the 12 kinds with their constant fields), `SKind.loc H d u`, `SKind.brs V`
     (branches `(condition, moves)`, transcribing `moves`), `selBr` (first branch with
     nonzero condition), **`moves_eq`**: `(selBr ρ (K.brs V)).map SMv.eval = moves (K.loc H d u)`.
     Also `kindsOfTag`, `Loc.kind` with `Loc.kind_spec`, `SKind.sloc`.
D. Command enumerator (done: `CmdEnum`). `cmdEnum M s b HX RX body` (`b` = stack depth,
   `HX, RX` read levels `< b` and evaluate to `H, radix M H`): loops `t5 … t1 < R` (levels
   `b … b+9`, digit `t1` at `b+9`, `t4` at `b+3`), pushes `t1-1, t4-1, H-t1-1, H+2-t1, rest`
   (`b+10 … b+14`), then per tag (`firstL` over `kindsOfTag`, test `matchX`) pushes the
   location number (`b+15`) and per move the index `k` (`b+16`) and `recX` (`b+17 … b+24`);
   body runs at depth `b+25`. **`out_cmdEnum`**: output
   `= (range numLoc).flatMap (c ↦ match decodeLoc c with some L ↦ (recsOf L).flatMap
   (r ↦ body.out (stkL ρ L ++ r)) | none ↦ [])` (compare `verifierCmds'_eq`).
   **`desc_recsOf`**: `recsOf L = rs.zipIdx.map (k :: ·)` with
   `Forall₂ (CmdDesc ∘ toACmd ℓ L) (moves L) rs`.
E. Schema enumerator (done: `SchList`, `CountIdx`, `SchEnum`, `CmdStk`, `SchGen`, `SchOut`,
   `SchFinal`).
   * `CmdStk`: `cmdStks` (the stacks of the `cmdEnum` body, one per command, in order),
     `out_cmdEnum'` (output = `cmdStks.flatMap body.out`), `cmdStks_forall₂` (relation
     `StkCmd`: length `b+25`, prefix `ρ`, source number at `b+15`, `CmdDesc` of `drop (b+17)`)
     to `verifierCmds'`, `keys_cmdStks` (keys `(b+15, b+16)` = `keyList`, independent of
     `b, ρ`), `filter_lexLt_eq_take`, **`length_out_before`** (a nested enumerator with body
     `when (beforeX b b') g` outputs `Σ_{first j stacks} |g.out|`).
   * `SchGen`: `SchNum.toL`, `gadgetX`, `GDescQ` (`GDesc` or kind `3` = query guard `v = 0`),
     **`SchRec`** (record `[tern, u, v, en, msk, gk, g1, g2, g3]` describes a schema),
     `blkGen`, `cmdBody` (counts `j` at `b+25`, `e₀` at `b+26`, then the 4/9 records),
     `detGen` (padded by 27 zeros), **`schEnum M s b HX RX NX rX p0X EcX body`**.
   * `SchFinal.out_schEnum`: with globals `HX ↦ H`, `RX ↦ radix M H`, `NX ↦ numLoc M H`,
     `rX ↦ |verifierCmds'|`, `p0X ↦ code query`, `EcX ↦ Σ cmdSz` (all `Bnd b`, `ρ.length = b`):
     `Forall₂ (τ.length = b+37 ∧ τ.take b = ρ ∧ SchRec sc (τ.drop (b+28)))
       ((AP … (verifierCmds' M x s ℓ H)).compiledSchemas query.code 0) schStks`,
     `schStks.map (getD (b+27)) = range schStks.length` (the index), and
     `(schEnum …).out x ρ = schStks.flatMap body.out`. (`ℓ, H` arbitrary; `timeProgram'` is
     this `AP` with `ℓ = timeWidth`, `H = timeHorizon` by `rfl`.)
   Math for F (done): `GuardEval` (`gEval x ℓ H gd i v` numeric guard, `gEval_spec`,
   `initCV`/`encCV_init`: the hit guard needs only `inBit x v`; **`mem_domain_of_schRec`**:
   `c ∈ sc.domain ↔ c.1 = s ∨ gEval (rec.drop 5) c.1 (regVal c.2)`), `OutNum` (`slotNum F i v t
   = t + 4((i + (s+1)F)2^ℓ + v)`, `slotNum_inj`, `ClsBnd`, `famNum_injective'`,
   **`outValid_slotNum`** (slot of a bounded class `X` at `(i,b)` valid ↔ `Valid (X, l)`),
   `not_outValid_slotNum` (for `coef` at `(i,b) ≠ (0,0)`), `outColor_slotNum`), `EntNum`
   (`entB s j i v`, **`ent_ne_zero_iff`** (`j = σ % (s+ℓ)`), `prevCnt`,
   **`prevStep_eq_count`**: `prevStep c σ = if P = 0 then none else some (P-1)` with
   `P = #{σ' < σ | ∃ σ'' < σ, σ' ≤ σ'' ∧ ent σ'' c ≠ 0}`).
   Also done: `DomGen` (**`violGen`**: the domain test as a generator, `violGen_out_eq_nil_iff`
   and **`violGen_nil_iff_mem`**: on a stack extending a schema stack of `out_schEnum`, with
   `iX ↦ c.1`, `vX ↦ regVal c.2`, `xbX ↦ inBit x (regVal c.2)`, `ℓX ↦ ℓ > 0`, `HX ↦ H`, the
   output is `[]` iff `c ∈ sc.domain`; derived Xp `le` and `eval_and'/or'/not'` for 0/1
   values), `ValidKinds` (`valid_*_iff` per kind, `coef_exists`).
F. Family passes (next). Design:
   * Validity per kind (unfold `Valid/ClsValid/LabelOK`, `I.domain v = univ`, `init` =
     `compiledInit`: `some 0` at `code accept`, `some 1` at `N + 8r + 3`): upd `c ∈ dom ∧ ent ≠ 0`
     (any label), junc `tern ∧ c ∈ dom` (any label), link `c ∈ dom ∧ l.2 = 0`, coord
     `l.2 = 0 ∧ (singleton → l.1 = 0)`, sum `tern ∧ c ∈ dom ∧ l.2 = 0`, track like upd with
     `l.2 = 0`, coef `l.2 = 0` (always valid: every domain contains block `s`) but only at
     coordinate `(0,0)`.
   * Colors: `range nOut` = families `F` × `i ≤ s` × `b < 2^ℓ` × `lab < 4` (`flatMap_range_mul`),
     `outColor (slotNum F i b t)` by `outColor_slotNum`/`outValid_slotNum`. Families in kind order;
     `E·NS` kinds: `schEnum` (index `e` at `b+27`) then the step loop as `q < s+2`, `j < s+ℓ`
     (`σ = q (s+ℓ) + j`, `σ % (s+ℓ) = j`); `coord`: loop `v < W`. `b`-loop by `loopX` (gives
     `inBit x b` for the hit guard). Domain test as a generator: `count` of violations
     (`fieldOK`: loop `t < m`; window `iℓ ≤ k+t < iℓ+ℓ`; bit `k+t-iℓ` of `v` is
     `odd (shr (shl v (iℓ)) (k+t))`), result `0` iff in the domain. `entB` without
     subtraction: bit `j - s` of `v` is `odd (shr (shl v s) j)`.
   * Edges: only hub kinds (`upd, junc, link`, numbered first) emit (`edgeList_outGraph`,
     `upNbrs_hub/nonhub/invalid`); neighbors per `nbrCand`, names `nameOfEff` (label
     `r + ε·initBit`, `initBit = 1` only for `coord (N+8r+3)` at block `0`), filtered by
     validity (only singleton coords can fail). `trackAt` via `prevStep_eq_count` (nested
     counts over `(q', j')` pairs); `permU` shift: `regVal ^^^ shiftVal msk i` with
     `field m (iℓ) ℓ = xorM (shr m (iℓ)) 0 ℓ` and `xorFields` unrolled over the constant `s`.
     Edge count `m` = `half` of the `count` of the edge pass.
G. Assembly: globals prelude (`n = |x|` by `len`, `ℓ = log n + C₀ + 4` by `log`, `H = sℓ-2`,
   `R`, `N = 16 R^5`, `r` and `Ec` by counting `cmdEnum`, `p0` by `codeX` of the query
   location, `E = Ec + 4`, `NS = (s+2)(s+ℓ)`, `W = N + 8r + 4`, `famCount`, `nOut`);
   `graphDescription (outGraph I ε) = nOut :: colors ++ m :: edges`,
   `distinguishes_outGraph_iff`, sizes (`timeProgram'_graphs`), `Gn.computesWithin`; Fits and
   cost lemmas (none exist yet for `cmdEnum`/`schEnum`: prove per-generator bounds
   compositionally with `cost_loop_le`-style uniform bounds; only the `b`-loop is `Θ(n)`, all
   other loops polylog); final file with Lax frontmatter
   (`conclusion: Lax119563.TimeReduction.time_reduction`).
   Pitfalls (reduction6): `List.Forall₂.exists_of_mem_left`, `List.getD_take`,
   `List.map_fst_zipIdx` do not exist (local versions `forall₂_exists_of_mem_left`,
   `getD_take'`, `map_fst_zipIdx'`); `simp_all` loops on goals with `lexLt`; `split_ifs` also
   splits nested `if`s (use `by_cases` + `rw [if_pos]`); Xp `Bnd` of `var i` is `i < n` but
   must be given as `bnd_var h` when the expected type is a metavariable; `include`d section
   hypotheses become explicit arguments of every lemma in the section (move helpers out).

## Older notes (superseded by the generator approach where they conflict)


Old remaining-work list:

1. Arithmetic library on `Stm` (file `SArith`). Done: accumulating loops `accum`
   (`exec_accum`: `acc + Σ f k`), `mulS` (`a * b`), `subS` (truncated `a - b`), `shlS`
   (`acc * 2^k`), `shrS` (`acc / 2^k`), `xorS` (`(a ^^^ b) % 2^lim`), each with its exact
   value and frame (costs via `Good.loop`). Still to add if needed: `div/mod` by a runtime
   value (counter with wrap-around, invariant `q·d + r = k`), `eq`, `and/or/not` on `0/1`
   as `Ex` abbreviations (`not a = lt a 1`, `and a b = lt 1 (a + b)`, …), and `Good`
   wrappers for the routines.
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
