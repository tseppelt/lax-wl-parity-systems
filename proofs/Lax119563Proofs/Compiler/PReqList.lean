import Lax119563Proofs.Compiler.PReqBits
import Lax119563Proofs.Compiler.PSchDesc

/-!
# Pass `P3`, request generation: the list level

* `fL π`, `dL π`: the numbers `f(0), …, f(k-1)` and the shift descriptions of a block
  permutation (`permDescription π = fL π ++ (dL π).flatten`);
* `reqRec u π c s = u :: cdesc (π.apply c) ++ [1, s, 0, 0]`: the request of column `c` for the
  argument `(u, π)` with sequence number `s` (`reqRec_eq`: computed bitwise by `xorL`);
* `reqsE I e`: the requests of schema `e` (argument by argument, columns in the order of
  `coordList`), with sequence numbers `ansBase I e + seqOff …` in the order in which `P4`
  consumes the answers (ternary: per column `U, V, W`; binary: all `V`, then all `U`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ}

/-- The block images `f(0), …, f(k-1)`. -/
def fL (π : BlockPerm k ℓ) : List ℕ := (List.finRange k).map fun i => (π.perm i : ℕ)

/-- The shift descriptions `δ₀, …, δ_{k-1}`. -/
def dL (π : BlockPerm k ℓ) : List (List ℕ) :=
  (List.finRange k).map fun i => blockDescription (π.shift i)

lemma permDescription_eq (π : BlockPerm k ℓ) : permDescription π = fL π ++ (dL π).flatten := by
  simp [permDescription, fL, dL, List.flatMap_def]

lemma length_fL (π : BlockPerm k ℓ) : (fL π).length = k := by simp [fL]

lemma length_dL (π : BlockPerm k ℓ) : (dL π).length = k := by simp [dL]

lemma bd_add (b d : BlockCoord ℓ) :
    blockDescription (b + d) = xorL (blockDescription b) (blockDescription d) := by
  simp only [blockDescription, xorL, List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun t _ => ?_
  simp [ZMod.val_add]

/-- The request of column `c` for the argument `(u, π)` with sequence number `s`. -/
def reqRec (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) : List ℕ :=
  u :: cdesc (π.apply c) ++ [1, s, 0, 0]

lemma reqRec_eq (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) :
    reqRec u π c s = u :: (fL π).getD c.1 0 ::
      xorL (blockDescription c.2) ((dL π).getD c.1 []) ++ [1, s, 0, 0] := by
  simp [reqRec, cdesc, BlockPerm.apply, fL, dL, bd_add]

/-- The offset of the sequence number of argument `a` at column `r` (of `d` columns). -/
def seqOff (tern : Bool) (d a r : ℕ) : ℕ :=
  if tern then 3 * r + a else if a = 0 then d + r else r

variable (I : ImplicitParitySystem k ℓ)

/-- The number of requests of the first `j` schemas. -/
noncomputable def ansBase (j : ℕ) : ℕ :=
  (((List.finRange I.schemas.length).take j).map fun e =>
    arity (sch I e) * (coordList (dom I e)).length).sum

/-- The requests of schema `e`. -/
noncomputable def reqsE (e : Fin I.schemas.length) : List (List ℕ) :=
  ((schLocs (sch I e)).zip (schPerms (sch I e))).zipIdx.flatMap fun (p : (ℕ × BlockPerm k ℓ) × ℕ) =>
    (coordList (dom I e)).zipIdx.map fun (q : Coord k ℓ × ℕ) =>
      reqRec p.1.1 p.1.2 q.1
        (ansBase I e + seqOff (Matrix.isTern (sch I e)) (coordList (dom I e)).length p.2 q.2)

/-- The requests of the first `j` schemas. -/
noncomputable def reqsUpTo (j : ℕ) : List (List ℕ) :=
  ((List.finRange I.schemas.length).take j).flatMap (reqsE I)

/-- All requests. -/
noncomputable def reqs : List (List ℕ) := (List.finRange I.schemas.length).flatMap (reqsE I)

end Lax119563Proofs.Compiler
