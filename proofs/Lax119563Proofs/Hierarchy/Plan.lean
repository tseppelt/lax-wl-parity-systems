/-!
# Plan for the proof of the deterministic time hierarchy theorem

Target: `Lax119563.TimeHierarchy.time_hierarchy`: for `s ≥ 1` and real `a < s` some language is
in `DTIME(n^s)` but not in `DTIME(n^a)`, for deterministic machines of the model
`Lax489179.TuringMachine` (arbitrary numbers of tapes, symbols and states per machine).

## Strategy: translation (padding) instead of an efficient universal machine

A direct diagonalisation for exponents `a` arbitrarily close to `s` needs a universal machine
with overhead `t^{1+o(1)}` (Hennie–Stearns).  We avoid it with Ibarra's translational method,
so that the universal machine may have any polynomial overhead of fixed degree.

1. *Coarse hierarchy* (`Coarse`): for every `b : ℕ` there are `B : ℕ` and `L` with
   `L ∈ DTIME(n^B) \ DTIME(n^b)`.  Proof: diagonalisation over inputs `code(M) ++ pad`
   by a machine that simulates `M` on its whole input under a clock of `|y|^B` steps, using a
   universal simulation of cost polynomial in `n + t` (degree independent of `M`).
2. *Padding* (`Padding`): for `r ≥ 1`, `1 ≤ a`, `1 ≤ s`: if `L ∈ DTIME(n^{s r})` then some `L'`
   satisfies `L' ∈ DTIME(n^s)` and `L' ∈ DTIME(n^a) → L ∈ DTIME(n^{a r})`.
   `L' = {x ++ [true] ++ 0^j | M_L accepts x within C (j+1)^s steps}`; deciding `L'` uses a clock,
   so no capped format check is needed.  The converse direction writes `0^{|x|^r}`.
3. *Chain* (`Chain`): if `DTIME(n^s) ⊆ DTIME(n^a)` with `1 ≤ a < s`, then
   `DTIME(n^{s r}) ⊆ DTIME(n^{a r}) ⊆ DTIME(n^{s ⌈a r / s⌉})`, and by strong induction on `r`
   every `DTIME(n^{s r})` collapses into `DTIME(n^{s R})` for `R = ⌈s / (s - a)⌉`,
   contradicting 1.  For `s ≥ 2` we may raise `a` to `max a (s - 1/2) ≥ 1`.
4. *Case `s = 1`* (`Locality`): `{x | the last bit of x is true}` is decidable in linear time;
   a machine running fewer than `|x|` steps never reads the last input cell.

## Machine programming infrastructure

* `Mach`: machines with typed finite state sets and *exits*: a transition acts
  (writes/moves) and either continues in a state or exits, or it halts with an answer.
  Sequential composition, conditionals and loops are sums/options of state types; costs add
  exactly.  Lifting to more tapes and larger alphabets; clocked execution; conversion of a Lax
  machine into a `Mach` and of a `Mach` into a Lax machine.
* `Run`: runs with coin `false`; per-tape translation invariance of Lax runs (handing over to
  a machine whose heads are not at zero).
* `Stack`: structured programs over finitely many stacks (each stored on one tape, top at the
  head, rest to the right, blanks elsewhere), big-step semantics with exact costs, and a
  verified compiler to `Mach`.  The input tape is a stack holding the input.
* `Programs`: moving symbols; unary arithmetic (add, multiply, power) with cost bounds.
* `Universal`: the simulator of an encoded Lax machine as a stack program.

## Status

Done (sorry-free): `Run`, `Mach`, `Lax`, `Stack`, `Glue`, `Programs`, `Chain`, `Locality`,
`Padding`, `Reduction` (`time_hierarchy_of_coarse : CoarseHierarchy → ...`).
Remaining: `CoarseHierarchy`, i.e. the universal simulator below.

## Design of the universal simulator (`Universal`)

A stack program `Sim` over tokens (`F T U S R M E N H0 H1 L Z Rt Sep End`).  Correctness is
only needed on inputs `y = code M ++ z`; on other inputs the clock bounds the running time.
* Code: tokens, 4 bits each.  Token stream
  `R^{k+1} Sep R^k Sep table End`, where `k + 1` is the number of tapes of `M`, and `table` is
  the concatenation over all keys `(q, c)` of `key(q, c) ++ [M] ++ (ins (δ q c)).reverse ++ [E]`
  with `key(q, c) = enc q ++ enc c_k ++ … ++ enc c_0`, `enc n = U^n S`,
  `ins (halt b) = [H_b]`, `ins (next q' w mv) = N :: enc q' ++ ⋯ (enc w_j ++ [mv_j]) ⋯`.
* Configuration of `M`: state `q` in unary on `QS`; stack `LS` holds for `j = 0..k` the cells
  left of head `j` (nearest first, encoded) each followed by `R`; `RS` likewise the scanned cell
  and the cells to its right (an empty right part means blank).
* Init: parse the code from stack `0` (keeping the consumed bits on `Y`), move the two `R`
  blocks to `LS`/`RS`, keep the table on `TBL`, push `R` and the input symbols onto `RS`.
* Step: (1) build `KEY` by copying the scanned symbol of each record of `RS` (rotating records
  through `RS2`) and then `enc q`; (2) search `TBL` for the entry whose key equals `KEY`
  (token comparison through `KEY2`/`TBL2`), copy its instruction to `INS` (reversing it);
  (3) on `H_b` push `H_b` on `DONE`; on `N` set `QS := q'` and for each record write `w_j`
  and move (`L`: one symbol `LS → RS`, `Rt`: `RS → LS`), rotating records through `LS2`/`RS2`.
* Cost: every phase is `O((size of all stacks + 1)^2)`; sizes grow by `O(m)` per step, so `T`
  simulated steps cost `c_M (n + T + 1)^3`.  Diagonalisation: `D` runs `Sim` under a clock of
  `(n + 1)^{3 b + 4}` steps and outputs the negated answer.
-/

