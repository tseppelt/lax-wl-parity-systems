import Lax119563Proofs.Compiler.PEmitSch

/-!
# Pass `P4` (list level): the class sizes

`clsSizes_eq`: the class sizes are, per schema (`schSizes`), `|D|` times `[4, 2]` (ternary)
or `[2]`, then `nEnt` times `4`, then (ternary) `|D|` times `2`, `nEnt` times `2`,
`|coefSteps|` times `2`; then per location `|coordList D_v|` times `labsN v`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The column sizes of the junction/link section. -/
def jlSizes (tern : Bool) : List ℕ := if tern then [4, 2] else [2]

/-- The class sizes of schema `e`. -/
noncomputable def schSizes (e : Fin I.schemas.length) : List ℕ :=
  ((coordList (dom I e)).flatMap fun _ => jlSizes (isTern (sch I e))) ++
    List.replicate (nEnt I e) 4 ++
    ((coordList (dom I e)).flatMap fun _ => if isTern (sch I e) then [2] else []) ++
    List.replicate (nEnt I e) 2 ++ List.replicate (coefSteps I e).length 2

/-- The class sizes of location `v`. -/
def locSizes (v : Fin I.numLocations) : List ℕ :=
  List.replicate (coordList (I.domain v)).length (labsN I v)

lemma map_stepsC_sizes (L : List (Coord k ℓ)) (n : ℕ) :
    L.flatMap (fun c => (stepsC c).map fun _ => n) =
      List.replicate ((L.map fun c => (stepsC c).length).sum) n := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.flatMap_cons, ih, List.map_cons, List.sum_cons, List.replicate_add, List.map_const']

lemma flatMap_rep (L : List (Coord k ℓ)) (n : ℕ) :
    L.flatMap (fun c => List.replicate (stepsC c).length n) =
      List.replicate ((L.map fun c => (stepsC c).length).sum) n := by
  rw [← map_stepsC_sizes]; simp only [List.map_const']

lemma schSizes_eq (e : Fin I.schemas.length) :
    (hubsCls I e ++ nonhubsCls I e).map (fun p => p.2.length) = schSizes I e := by
  simp only [hubsCls, nonhubsCls, List.map_append, List.map_flatMap, List.map_map,
    Function.comp_def, schSizes, nEnt, bits1, bits2, List.length_cons, List.length_nil,
    map_stepsC_sizes, List.append_assoc, List.map_const', List.length_map, flatMap_rep]
  congr 1
  · refine List.flatMap_congr fun c _ => ?_
    unfold jlSizes; split <;> rfl
  · congr 2
    refine List.flatMap_congr fun c _ => ?_
    split <;> rfl

/-- **The class sizes.** -/
theorem clsSizes_eq : clsSizes I =
    (List.finRange I.schemas.length).flatMap (schSizes I) ++
      (List.finRange I.numLocations).flatMap (locSizes I) := by
  rw [clsSizes, ordCls, List.map_append, List.map_flatMap, List.map_flatMap]
  congr 1
  · exact List.flatMap_congr fun e _ => schSizes_eq I e
  · refine List.flatMap_congr fun v _ => ?_
    simp only [locSizes, labsN, List.map_map, Function.comp_def, List.map_const']

end Lax119563Proofs.Compiler
