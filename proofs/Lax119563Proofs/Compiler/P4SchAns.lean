import Lax119563Proofs.Compiler.P4SchGlue

/-!
# Pass `P4`, schema part: the answer words of a schema per column

`ansE_flatten`: `(ansE I e).flatten` = the words consumed by section 1 (`a1C`, per column:
ternary `U, V, W`; binary `V` = the end answer) followed by those of section 2 (`a2C`: binary
`U`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The `U` answer of column `q.1` (index `q.2`) with sequence number `s`. -/
noncomputable def aU (e : Fin I.schemas.length) (c : Coord k ℓ) (s : ℕ) : List ℕ :=
  ansRec I (locU (sch I e)) ((permU (sch I e)).apply c) s

noncomputable def aV (e : Fin I.schemas.length) (c : Coord k ℓ) (s : ℕ) : List ℕ :=
  ansRec I (locV (sch I e)) ((permV (sch I e)).apply c) s

noncomputable def aW (e : Fin I.schemas.length) (c : Coord k ℓ) (s : ℕ) : List ℕ :=
  ansRec I (locEnd (sch I e)) ((permEnd (sch I e)).apply c) s

/-- The sequence number of the end answer of column `r`. -/
noncomputable def sW (e : Fin I.schemas.length) (r : ℕ) : ℕ :=
  if isTern (sch I e) then ansBase I e + 3 * r + 2 else ansBase I e + r

/-- The answer words of column `q.2` consumed by section 1. -/
noncomputable def a1C (e : Fin I.schemas.length) (q : Coord k ℓ × ℕ) : List ℕ :=
  ans1 (tnN (isTern (sch I e))) (aU I e q.1 (ansBase I e + 3 * q.2))
    (aV I e q.1 (ansBase I e + 3 * q.2 + 1)) (aW I e q.1 (sW I e q.2))

/-- The answer words of column `q.2` consumed by section 2. -/
noncomputable def a2C (e : Fin I.schemas.length) (q : Coord k ℓ × ℕ) : List ℕ :=
  if isTern (sch I e) then [] else
    aU I e q.1 (ansBase I e + (coordList (dom I e)).length + q.2)

lemma ansE_flatten (e : Fin I.schemas.length) :
    (ansE I e).flatten = (coordList (dom I e)).zipIdx.flatMap (a1C I e) ++
      (coordList (dom I e)).zipIdx.flatMap (a2C I e) := by
  unfold ansE a1C a2C aU aV aW sW dom
  cases h : sch I e with
  | binary u v D σ τ =>
    simp [h, Schema.domain, isTern, tnN, ans1, locU, locV, locEnd, permU, permV, permEnd, List.flatten_append,
      List.flatMap, List.map_map, Function.comp_def]
  | ternary u v w' D σ τ π =>
    simp [h, Schema.domain, isTern, tnN, ans1, locU, locV, locEnd, permU, permV, permEnd, List.flatMap,
      List.map_map, Function.comp_def, List.flatten_flatten]

end Lax119563Proofs.Compiler
