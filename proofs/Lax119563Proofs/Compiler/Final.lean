import Lax119563Proofs.Compiler.OutDesc

/-!
# The matrix compiler from the machine

`compileM I := (reGraph I (ordL I) 0, reGraph I (ordL I) 1)` satisfies the game, size and edge
clauses (by `reGraph_spec` and `ordL_perm`), and its encoding is
`encodeNats (gDesc I 0 ++ gDesc I 1)` (`encode_compileM`). Hence the concept statement follows
from a single machine computing `encodeNats (gDesc I 0 ++ gDesc I 1)` from `encodeSystem I`
within the bound (`Compiler/Prog`).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.PebbleGame Lax119563.ImplicitSystemEncodings Lax119563.BinaryEncodings
open Lax119563.DeterministicTime Lax119563Proofs.Matrix
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Compiler

/-- The construction: the matrix graphs with vertices in the machine's order. -/
noncomputable def compileM {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) :
    ColoredGraph × ColoredGraph :=
  (reGraph I (ordL I) 0, reGraph I (ordL I) 1)

/-- The encoding of the construction is the list the machine emits. -/
theorem encode_compileM {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) :
    encodeGraphPair (compileM I).1 (compileM I).2 = encodeNats (gDesc I 0 ++ gDesc I 1) :=
  encodeGraphPair_eq I

end Lax119563Proofs.Compiler
