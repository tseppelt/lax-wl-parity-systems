/-!
# Plan of the `Reduction` area

Goal: `Lax119563.TimeReduction.time_reduction`.

**Status: DONE** (reduction8). `Reduction/Main.lean`: `Lax119563Proofs.Reduction.time_reduction`
(axioms `propext, Classical.choice, Quot.sound`), with exponent `c = 24`. Final pieces:
* `PassBase`: an 18th global `2^ℓ` at level 17 (`gP`); `slotLoops s PX V body` takes the `loopX`
  limit expression (`gP`, class `P 1 0`), `out_slotLoops` needs `PX.eval τ = 2^ℓ`.
* `CostGlob`: `globTys` (classes of the 18 globals), `Xp.minR` with `hasTy_minR`.
* `CostWF`: closure lemmas for `WFX/NoX` (`Gn.Cl`), `wfx_descGen`.
* `CostPassBase`, `CostColPass`, `CostEdgePass`: **`Gn.hasCost_descGen`**:
  `HasCost globTys (descGen M s ε 18) 1 21`.
* `Prelude`: `Gn.prelude M s C₀ g` (levels `0 … 17`), **`out_prelude`** (`= g.out x globs` with
  `ℓ = timeWidth`, `H = timeHorizon`, `s ≥ 2`), `Gn.hasCost_prelude`, `Gn.wfx_prelude`.
* `Main`: `redGen = prelude (descGen 0 18 ; descGen 1 18)`, `out_redGen`
  (`graphDescription G'_0 ++ graphDescription G'_1`), `nOut_le` (size `O(n L^6)`), and the
  final theorem via `Gn.computesWithin_quasiLinear` (`d = 21`, time `C n L^24`).

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
F. Family passes (reduction7). Done:
   * `SlotList`: `slotL` (slots `i ≤ s`, `v < 2^ℓ`, `t < 4`), `range_nOut_flatMap`,
     `range_fam_flatMap` (seven kinds), `range_mul_flatMap`, `toBlk`/`labOf`, and
     `outValid_upd/track/junc/link/sum/coord/coef` (validity of slot numbers per kind).
   * `PassBase`: `Iv M x s ℓ H` (the compiled code-ordered system, a `def`: as an `abbrev` the
     `with_reducible rfl` of `rw` unfolds it and times out), `globs` (17 globals at levels
     `0 … 16`: `|x|, log, ℓ, H, R, N, r, Ec, p0, acc, E, NS, W, E·NS, famCount, nOut, det`),
     `GlobOK` (`ρ.take 17 = globs`), named globals `gℓ … gdet`, `schEnum_ctx` (schema
     enumerator as `(range E).flatMap` over contexts `SchCtx`), `slotLoops`/`out_slotLoops`,
     `entX`/`eval_entX`.
   * `ColPass`, `ColAll`: **`out_colPass`**: `(colPass M s b).out x ρ = (range nOut).map outColor`
     (needs `ρ.length = b`, `GlobOK ρ`, `0 < ℓ`, `1 ≤ s`).
   * `EdgeMath`: `edgesOf I ε u`, `edgesOf_nonhub`, `edgesOf_hub_slot`, **`edges_flat`** (the
     flattened edge list of `outGraph I ε` = upd ++ junc ++ link slot contributions).
   * `SlotPass` (`schSlots`/`stepSlots` for arbitrary bodies), `EdgeCand` (`candOut`,
     `plainGen`, `coordGen` with the seed of `Iv`), `EdgeJunc` (`shiftX`/`permVX`,
     **`out_edgeJunc`**), `EdgePrev` (`prevGen`, `length_out_prevGen = prevCnt`), `EdgeLink`
     (**`out_edgeLink`**), `EdgeUpd` (**`out_edgeUpd`**).
   * `DescGen`: `edgePass`, **`out_edgePass`** (flattened edge list of `outGraph (Iv …) ε`),
     `descGen M s ε b = seqL [emit gnOut, colPass, count edgePass (seq (emit (half (var b)))
     edgePass)]` and **`out_descGen`**: on a stack `ρ` with `ρ.length = b`, `GlobOK ρ`,
     `0 < ℓ`, `1 ≤ s`, `ε ≤ 1`: `(descGen M s ε b).out x ρ = graphDescription (outGraph (Iv …) ε)`.
   Pitfalls: anything that makes Lean whnf `sch (Iv …) e` (implicit-argument unification of
   validity facts with `Iv`, `rfl` closing `rw`, `congr 1`, `if_pos` on `isTern (sch …)`) times
   out; state such facts as generic lemmas over `I` and apply them with explicit arguments
   (`valid_sum_of_junc`, `valid_track_of_link`, `valid_*_of_upd`, `startCls_of_tern`); do not
   `set` terms containing `Iv`; use `List.append_left_inj` instead of `congr 1`.
G. Assembly (done, see the status above; the notes below are the original plan). The output part is `descGen` (F). Remaining:
   * Prelude pushing exactly `globs M x s ℓ H` (levels `0 … 16`, `ℓ = timeWidth C₀ |x|`,
     `H = timeHorizon s C₀ |x|`; check both definitions in `Circuits`): `len`; `log (var 0)`;
     `ℓ` and `H` by `bind`; `R = H + 1 + cM M`; `N = 16 R^5` (`mulC`, `mul`); `r` = length of
     `count (cmdEnum … (emit 0))` (`out_cmdEnum'`, `cmdStks_forall₂` length); `Ec` = count of
     a `cmdEnum` body emitting `cmdSz` zeros (`szAt_of_stkCmd`, `emitN`); `p0`, `acc` by
     `SLoc.codeX` of the query/accept locations; `E` = count of `schEnum … (emit 0)` (use
     `out_schEnum` directly: `schEnum_ctx` needs all 17 globals); `NS = mulC (s+2) (s + ℓ)`;
     `W = N + 8r + 4` (`= (Iv …).numLocations`, `compiledSize`, `AP_commands`); `E·NS` by
     `mul`; `famCount`; `nOut = mulC 4 (shl (mulC (s+1) fam) ℓ)`; `det = N + 8r + 3`.
     Then `GlobOK` of the prelude stack.
   * `prog := prelude (seq (descGen M s 0 17) (descGen M s 1 17))`, output
     `graphDescription G₀ ++ graphDescription G₁` (encodeGraphPair after `encodeNats`), with
     `distinguishes_outGraph_iff` + `timeProgram'_graphs` (`Iv` with `ℓ = timeWidth`,
     `H = timeHorizon` is `(timeProgram' …).compile (timeQuery' …) _` by `rfl`/`Iv` unfolding),
     sizes `nOut ≤ C n log^c n` (from the matrix-graph bound: `nOut = 4·2^ℓ(s+1)famCount`),
     `|x| ≤ |encodeNats out|` (nOut ≥ |x|).
   * Fits/cost: `HasCost` for `slotLoops` (the `loopX` over `pow2 gℓ`: the cost note above says
     `2^ℓ` needs a direct class; consider adding a global `2^ℓ` and using it as the `loopX`
     limit), `violAt` (`hasCost_violGen`), `colBody`, `entX`, `prevGen` (two nested step
     loops, polylog), `coordGen/plainGen`, `edge*`, `descGen`, prelude; then
     `computesWithin_quasiLinear` and the final file with Lax frontmatter
     (`conclusion: Lax119563.TimeReduction.time_reduction`, style of `Counter/Main.lean`).
   Pitfalls (reduction6): `List.Forall₂.exists_of_mem_left`, `List.getD_take`,
   `List.map_fst_zipIdx` do not exist (local versions `forall₂_exists_of_mem_left`,
   `getD_take'`, `map_fst_zipIdx'`); `simp_all` loops on goals with `lexLt`; `split_ifs` also
   splits nested `if`s (use `by_cases` + `rw [if_pos]`); Xp `Bnd` of `var i` is `i < n` but
   must be given as `bnd_var h` when the expected type is a metavariable; `include`d section
   hypotheses become explicit arguments of every lemma in the section (move helpers out).

## Fits/cost (done: `FitsBasic`, `CostTy`, `CostGn`, `CostMachine`, `CostCmd`, `CostSch`,
## `CostDom`, `CostPrelude`)

Uniform bounds via *growth classes* (`CostTy`): `Ty.P e d` (values `≤ K 2^(eℓ) (ℓ+1)^d`) and
`Ty.big` (values `≤ 2^(K(ℓ+1))`), at a scale `ℓ` with `|x| ≤ 2^ℓ`; `Ag K ℓ τs ρ` (stack agrees
with the classes). `Xp.HasTy τs e τ` (∀ stack constant ∃ `K`: value in class `τ`, fits below
`2^(K(ℓ+1))`, cost `≤ K(ℓ+1)`; loop-based ops need a linear `P 0 1` count), with rules
`hasTy_var/const/add/addBig/lt/half/odd/mulB/mulBBig/shl/shr/xorM/eq/not/and/or/mulC/mul/pow2`,
`HasTy.le/ctx/weaken`. `Gn.HasCost τs g e d` (fits below `2^(K(ℓ+1))`, cost
`≤ K 2^(eℓ) (ℓ+1)^(d+1)`) and `Gn.HasLen` (output length class, for `count`), with rules
`hasCost_skip/emit/seq/ite/bind/loop/loopX/len/log/count/seqL/when/dispatch/bindL/bindSub`
(`CostGn`): a loop over a `P e₀ d₀` range adds `(e₀, d₀)`; `loopX`/`len` force `e ≥ 1`.
* **`Gn.computesWithin_quasiLinear`** (`CostMachine`): `HasCost [] g 1 d`, `g.need ≤ R`,
  `g.WFX` give `∃ C, ∀ x, 2 ≤ |x| → |x| ≤ |encodeNats out| → ComputesWithin (machine R g) x
  (encodeNats out) (C |x| (log₂|x|)^(d+3))` (absolute exponent if `d` is; `w = O(log |x|)`).
* **`hasCost_cmdEnum`** (`CostCmd`): linear `HX, RX` (`LinX`: `P 0 1` and `Bnd`), body
  `HasCost (τs ++ cmdTys) body e d` ⇒ `HasCost τs (cmdEnum …) e (d+6)`; `cmdTys`: digits and
  differences `P 0 1`, `rest`, location number `P 0 5`, index `P 0 0`, record `recTys`
  (`mask` is `big`, `g1` linear). Also `SLoc.codeX_tyB`, `SMv.recX_tyB`, `SKind.brs_ok`.
* **`hasCost_schEnum`** (`CostSch`): globals `NX, rX, p0X, EcX` of class `P 0 7`, body
  `HasCost (τs ++ schTys) body e d` ⇒ `HasCost τs (schEnum …) e (d+12)` (`schTys`: `cmdTys`,
  `j, e₀`, index `P 0 7`, numbers `numTys = [P00, P07, P07, P07, big]`, guard `gdTys`).
* **`hasCost_violGen`** (`CostDom`): block index `P 0 0`, linear `ℓX, HX, g1X, g2X` ⇒ `(0, 1)`.
* **`hasCost_lenLog`** (`CostPrelude`): the prelude `len (log (var n) (bind (shl (const 1)
  (var (n+1))) g))` pushes `|x| : P 1 0`, `L = log₂|x| : P 0 1`, `2^L : P 1 0` (classes forget
  relations between levels, so `2^L` needs this direct proof); `2^ℓ = mulC (2^c) 2^L` is then
  `P 1 0`, so the `b`-loop (`hasCost_loopX`) is the only `e = 1` loop.
Use for G: type the remaining globals (`H, R` linear; `N, r, E, …` polylog `P 0 k`), the family
passes with `hasCost_schEnum`/`hasCost_violGen`/`hasCost_loopX`, then
`computesWithin_quasiLinear`.
Pitfall: `++` is left-associative (`τs ++ l ++ [a]` is `(τs ++ l) ++ [a]`), so weaken in steps.

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
