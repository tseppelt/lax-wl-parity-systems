/-!
# Plan of the `Machines` area

Infrastructure for writing deterministic multitape Turing machines of the archive model
(`Lax489179.TuringMachine.Machine`) with proven running times, for use by the quasi-linear
reduction of `Lax119563.TimeReduction.time_reduction`.

## Layers

1. `Basic`: structured machines `TM k Γ` (finite state type, arbitrary finite alphabet,
   transition function returning `none` for halting) with the exact big-step semantics
   `HaltsFrom`/`HaltsIn` and the bound `RunsWithin`. Combinators with exact time lemmas:
   `nop`, `act`, `seq` (`;;`), `branch`, `ite`, `loop`, `onTapes` (run a machine on a
   subset of the tapes). Loop lemmas: by an explicit sequence of tape families, and by an
   invariant with a potential function bounding the remaining time.
2. `Compile`: `TapeAlphabet` (blank and two bit symbols), `TM.compileWith` to the archive
   model, `Deterministic` by construction, and the transfer theorems `TM.computesWithin`
   (output convention of `ComputesWithin`) and `TM.decidesWithin`.
3. `Words`: tapes holding a blank-free word with the head inside it, `Tape.ofWord pre rest`
   (content `pre ++ rest`, head at `|pre|`), and single-tape and two-tape routines on them:
   moving, scanning to a delimiter, rewinding to position `0`, writing, copying (forward and
   reversed), erasing; each with a linear time bound.
4. `Numbers`: natural numbers on a tape as the word `Nat.bits m` (least significant bit
   first); zero test, increment, equality test, writing `encodeNat m` and lists of codes.
5. `Sort`: merge sort of records (bit strings, each followed by a separator symbol) on four
   tapes by repeated distribution and merging of runs delimited by a second separator, in
   time `O(L · (log m + 1))` for `m` records of total encoded length `L`; the result is the
   sorted list (lexicographic order on `List Bool`).
6. `Output`: final convention: erase the input on tape `0` and copy the output word there,
   so that the compiled machine satisfies `ComputesWithin`.

The constructions of the actual graph pair (areas Circuits, Programs, Matrix) and the
composition-with-a-decider and input-patching lemmas (area Main) are not part of this area.
-/
