/-!
# Plan and guide of the `Machines` area

Infrastructure for writing deterministic multitape Turing machines of the archive model
(`Lax489179.TuringMachine.Machine`) with proven running times, used by the machines of the
hardness results (area Hardness) and the composition lemmas (area Main). Everything listed
below is proven (no `sorry`).

## Layers

1. `Basic`: structured machines `TM k Γ` (finite state type, arbitrary alphabet, transition
   function returning `none` for halting), exact big-step semantics `HaltsFrom`/`HaltsIn`,
   and the bound `RunsWithin T t T'` ("from tapes `T`, halts within `t` transitions on
   `T'`"). Combinators with exact time lemmas: `nop`, `act`, `seq` (notation `;;`, times
   add), `branch`/`ite` (free), `loop c B` (one extra transition per iteration; lemmas
   `loop_runsWithin_exit`, `loop_runsWithin_iter`, `loop_runsWithin` along a sequence of
   tape families, `loop_runsWithin_inv` with an invariant and a potential), and
   `onTapes σ M` running a `k`-tape machine on the tapes `σ 0, …` of a larger machine
   (`onTapes_runsWithin`, result `updateTapes σ U T'`).
2. `Compile`: `TapeAlphabet Γ` (blank and two bit symbols), `inputTapes k x`,
   `TM.compileWith`/`TM.compile` to the archive model (deterministic by construction:
   `TM.deterministic_compile`), and the transfer theorems `TM.computesWithin` (output
   convention of `ComputesWithin`, one extra step for halting) and `TM.decidesWithin`.
3. `Words`, `Routines`, `WordRoutines`: word tapes `Tape.ofWord pre rest` (content
   `pre ++ rest` from position `0`, head on position `|pre|`) and their single-step lemmas;
   `actOn`, `act₂`, `moveR`, `moveL`, `write`, `writeR`, `scanR`, `scanL`, `backTo`,
   `rewind`, `copyR`, `erase`, each with a linear bound.
4. `Numbers`: numbers as `natWord m` (`Nat.bits m`, least significant first); `incr`,
   the equality branch `ifEq` (also for arbitrary blank-free words), and `emitNat`
   appending `encodeNat m`.
5. `Output`: `inputTapes_zero`, `TM.finish o` and `TM.computesWithin_finish`.
6. `Extras`: `whileM` (loop with a test machine), `revCopy` (reversed copy), `countLen`
   (add the length of a word to a counter).

## How to build a reduction machine

Fix an alphabet `Γ` with `[Fintype Γ] [DecidableEq Γ] [TapeAlphabet Γ]` containing the
separators needed. Write the machine as a `TM (k + 1) Γ`
from the combinators, prove `M.RunsWithin (inputTapes k x) t T` by chaining
`seq_runsWithin` and the routine lemmas (most routines are stated for tapes of the form
`Tape.ofWord pre rest` and produce `Function.update T i _`), end with `finish o` to move the
output word `bitsWord y` from tape `o` to tape `0`, and apply `TM.computesWithin_finish` to
get `ComputesWithin (M ;; finish o).compile x y (t + O(|x| + |y|))`.

## Not in this area

The constructions of the graph pair (areas Circuits, Programs, Matrix) and the
composition-with-a-decider and input-patching lemmas (area Main).
-/
