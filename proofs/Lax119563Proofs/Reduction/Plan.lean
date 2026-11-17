/-!
# Plan of the `Reduction` area

Goal: `Lax119563.TimeReduction.time_reduction`.

**Status: DONE** (reduction9). `Reduction/Main.lean`: `Lax119563Proofs.Reduction.time_reduction`,
proved as in the paper by composing two steps:
1. a generator `redGen M s C₀ = prelude (sysGen M s)` emits `systemDescription I_x` for the
   implicit parity system `I_x = Iv M x s ℓ H` compiled from the code-ordered time simulation
   program (`out_redGen`), so its machine computes `encodeSystem I_x` from `x` in time
   `O(n log^23 n)` (`Gn.computesWithin_quasiLinear`, which also bounds the output length,
   hence `bitLength I_x = O(n log^23 n)`);
2. the matrix compiler, cited as the concept statement
   `Lax119563.MatrixCompiler.matrix_compiler` (no use of the `Matrix` proof internals): its
   machine computes the graph pair from `encodeSystem I_x` in time
   `O((H + S) log^c (H + S + 2))`.
The machines are composed by `Main.Compose.compose_computesWithin` (`Machines/ComposeComputes`:
simulate the first, rewind tape `0`, simulate the second; time `2 t₁ + t₂ + 3`).
Correctness (`accepts_iff_conflict`, `distinguishes_iff_conflict`): `M` accepts `x` iff `I_x`
has a conflict (`timeProgram'_accepts_iff`, `conflictRound_compile_lt_top_iff`), and the game
clauses of the matrix compiler with the game characterization of WL. Size:
`S(I_x) = O(n log^6 n)` (`sizeParameter_compile_le`, `time_simulation'`, `size_poly`), the
graphs have `O(S)` vertices. Exponent `c = 23 + c_matrix`.

## Files

* Machines from register programs: `Bits`, `HProg`, `HStack`, `HRoutines`, `HHeads`
  (`StackOut`), `HCompile`, `HMachine`, `HLib`, `HFrame`.
* Structured statements: `SProg`, `SStm`, `SLib`, `SArith`.
* Generators (stack language with a pure list semantics): `XLang`, `XSpec`, `GLang`, `GSpec`,
  `GMachine`, `GTools`, `GEnum`.
* The time program in code order: `Locs`, `CodeOrder` (`timeProgram'`, `time_simulation'`).
* Schemas: `SchemaParts` (schema accessors, `regVal` facts, location numbers), `SchemaData`,
  `SchList` (`SchMatch`), `SymLoc`, `SymMoves`, `CmdEnum` (command enumerator), `CountIdx`,
  `SchEnum`, `CmdStk`, `SchGen` (`SchRec`, schema enumerator `schEnum`), `SchOut`, `SchFinal`
  (`out_schEnum`), `GuardEval`, `DomGen` (domain test `violGen`).
* Fits and cost: `FitsBasic`, `CostTy`, `CostGn`, `CostMachine`, `CostCmd`, `CostSch`,
  `CostDom`, `CostPrelude`, `CostGlob`, `CostWF`, `CostPassBase`.
* The system generator: `PassBase` (`Iv`, the 14 globals `globs`, `GlobOK`, `schEnum_ctx`,
  `violAt`, `shiftX`), `Prelude` (`out_prelude`), `SysDesc` (the description of a compiled
  system in emittable form: `domainDescription_eq_domL`, `permDescription_of_permDesc`,
  `schemaDescription_of_match`, `locsDesc_compile`), `SysGen` (`sysGen`, **`out_sysGen`**),
  `CostSys` (`hasCost_sysGen`, `wfx_sysGen`), `Main`.

## The system generator

On the globals (depth `14`: `|x|, log₂|x|, ℓ, H, R, N, r, Ec, p0, acc, E, W, det, 2^ℓ`),
`sysGen` emits `s + 1, ℓ, W`, then per location `v < W` its initialization number
(`1` at `accept`, `2` at the detector output, else `0`) and its full domain
`(s+1) 2^ℓ, 0, …, (s+1) 2^ℓ - 1` (`locGen`), then `E` and, by the schema enumerator, per schema
`schBody`: `2, u, v` or `3, u, v, w`, the domain (`domGen`: loops `i ≤ s`, `v < 2^ℓ` by
`loopX`, emitting `i 2^ℓ + v` when the domain test `violAt` is empty; counted first for the
length) and the permutations (`permGen`: `0, …, s` and the shifts `shiftVal s ℓ msk i`; only
the first permutation has a nonzero mask). Cost: `HasCost globTys sysGen 1 20`.

## Generator layers (reference)

* `HProg R`: registers holding naturals, instructions `clr one dbl half copy add lt emit rd
  rst`, `seq`, `ite`, `loop`; `HProg.computesWithin`.
* `Stm`: statements with a total denotational semantics `Stm.exec`, cost `Stm.cost`, compiler
  `Stm.code`; `Stm.computesWithin`.
* `Xp`/`Gn`: expressions over a stack and generators (`skip, emit, seq, ite, bind, loop, loopX,
  len, log, count`) with `Gn.out x g ρ` a plain list function; `Gn.computesWithin`.
* Growth classes (`CostTy`): `Ty.P e d` (values `≤ K 2^(eℓ) (ℓ+1)^d`), `Ty.big`; `Xp.HasTy`,
  `Gn.HasCost τs g e d`, `Gn.HasLen`; `Gn.computesWithin_quasiLinear`: `HasCost [] g 1 d`,
  `g.WFX` give time `C |x| log^(d+3) |x|` and output length within the same bound.
* Command enumerator `cmdEnum` (`out_cmdEnum'`, `cmdStks_forall₂`) and schema enumerator
  `schEnum` (`out_schEnum`: stacks of length `b + 37` with the record
  `[tern, u, v, en, msk, gk, g1, g2, g3]` at `b + 28 …`, `SchRec`).

Pitfalls: anything that makes Lean whnf a schema of `Iv …` times out; state facts generically
over the schema (`out_schBody` takes `sc` with a context `SchCtx`). `++` is left-associative.
`simp only [Xp.eval]` on an `if` over `Xp` values keeps a stale `Decidable` instance; use
`eval_eq_const`.
-/
