/-!
# Plan: deterministic time as a register program

This directory proves the mathematical content of the lemma "Time simulation": for a
deterministic machine `M` halting within `C₀ * n ^ s + C₀` steps (`s ≥ 2`), an explicit
`s`-register program over `𝔽₂^ℓ` with `ℓ = log₂ n + c` and `(log n)^{O(1)}` locations and
commands, together with a query that accepts iff `M` accepts `x`.

## Construction (a binary variant of the recursive window simulation)

Put `H = s * ℓ - 2`, `T = 2 ^ H`. A *call* at depth `d ≤ H` (remaining depth `r = H - d`) is a
number `ω < 2 ^ d`; it covers the steps `[ω 2^r, (ω + 1) 2^r)` and owns, per tape `ν`, a window
of `4 * 2 ^ r` cells starting at the absolute offset `off d ω ν`. The root window starts at
`-T`. A call with `r ≥ 1` has two phases `θ ∈ {0, 1}` of `B = 2 ^ (r - 1)` steps; at the start
of phase `θ` the head of tape `ν` is in block `β ∈ [1, 6]` (blocks of size `B`), and the child
`2 ω + θ` gets the window starting at block `w = min (β - 1) 4`. Invariant: at the start of a
call the head lies in the middle half `[2^r, 3 * 2^r)` of the window.

The *address* of a claim at depth `d` is a number `A < 2 ^ (H + 2) = 2 ^ (s ℓ)`: its high `d`
bits are `ω`, its low `r + 2` bits a local position `j`. The registers hold the bits of `A`
(register `i` holds bits `i ℓ, …, i ℓ + ℓ - 1`). The control location records the claim kind:

* `cell d θ ν c`   : the cell at local position `j` of tape `ν` at the start of phase `θ`
                     (`θ = 2` is the end of the call) has value `c` (symbol, head flag);
* `state d θ p`    : the extended state (state, answer) at that time is `p`;
* `headIn d θ ν u` : the head of tape `ν` lies in the aligned interval of length `2 ^ u`
                     containing `j` (the low `u` bits of `j` are ignored).

Verification rules (existential choices are several commands at a location, universal
ones are forks):
* `cell d (θ+1)`: guess the head block `β`; fork into `headIn d θ ν (r-1)` at block `β` and
  a *restore* step: if the block `q` of `j` lies in the child window, descend into
  `cell (d+1) 2` (the child's end), otherwise use `cell d θ` (frame property).
* `cell (d+1) 0`: read the phase bit `θ`, guess `β`, fork into the head test and a *gather*
  step going up to `cell d θ` at block `w + c'`.
* `state` claims move along the same tree; at the root, `cell 0 0` and `state 0 0` are
  tested against the initial configuration via membership tables (register 0 holds the
  offset of the position from `T` when the other registers agree with `T`).
* base `d = H`: guess state, head positions and scanned symbols, and fork into all of them.

All address changes replace a field of at most three bits (guard on the current value and
XOR with a constant mask). No navigation chain of length `H` is needed.

## Files
* Register programs are `Lax119563Proofs.Programs.RegisterProgram` (area `Programs`).
* `AddrProgram`          — programs over numeric addresses with field guards and XOR
                            masks, compiled to register programs (transfer theorem).
* `Bits`                 — bit fields `field A k m`, `setBits`, XOR lemmas.
* `MachineRun`           — facts about runs of `Lax489179` machines (step, frame, heads).
* `Windows`              — offsets, the middle-half invariant, truth of claims.
* `Verifier`             — locations, commands, soundness and completeness.
* `TimeSimulation`       — parameters, size bounds, the final statement.
-/
