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

## Own register program (to do)

`P' := Circuits.compile (numLoc M H) Loc.code .accept .reject code_accept_ne_reject
  (progCmds ℓ (allLocs M H) (moves M x s ℓ H))` — as `timeProgram` but over `allLocs`
without `dedup` (acceptance only uses membership in the command list:
`verifier_accepts_iff` needs `∀ L, L ∈ locs`, and `compile_accepts`). Correctness and size
bounds as in `TimeSimulation` (`allLocs` has `O(H²)` entries, each with `O(1)` moves).
Every command has an executable source (no moves at `accept`/`reject`), so every schema
domain contains the whole checksum block `{s} × 𝔽₂^ℓ`.

## Output graph (to do; math layer)

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

## Reduction program (to do; `HProg` layer)

Registers hold `n, ℓ, H, NS, E, W, FN`, loop counters and command data. Structure:
1. Count `n = |x|` (read the input, `rst`), compute `ℓ = log₂ n + C₀ + 4` etc.
2. For `ε ∈ {0, 1}`: emit `N'`; emit the colors of all slots (nested loops over the
   families in offset order, then `i ≤ s`, `b < 2^ℓ`, `lab < 4`; for families of schemas the
   commands are enumerated in list order, maintaining the schema counter `e`); run the hub
   loop in counting mode to get the edge number, emit it, run it again emitting `u, v`.
   `hitGuard` on register `0` needs `x[b]`: the `b`-loop streams the input (`rd`, `rst` per
   family), so each family costs `O(n)` extra.
3. `rst` at the end (cursor `0`, as required by `HProg.computesWithin`).
The commands are enumerated by a program generated from `allLocs` and `moves` at the Lean
level: constant-size fields (`θ, ν, c, β, ρ, …`) are unrolled, `d, u` are runtime counters,
and the runtime conditions of `moves` (`d = 0`, `d < H`, `u < H - d`, `u = 0`) are tests.
Location codes `Loc.code` are computed with multiplication by the runtime radix `H + 1 + cM`.
Cost: `O(N' · polylog)`; word size `w = O(log n)`.

Library still to write on top of `HRuns`: frame lemmas (registers not written are kept),
constants, increment, counting loops with invariants, multiplication, bit tests, XOR.
-/
