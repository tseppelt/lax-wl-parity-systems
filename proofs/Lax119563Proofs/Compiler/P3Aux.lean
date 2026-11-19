import Lax119563Proofs.Compiler.PReqLoopList

/-!
# Pass `P3`: list facts used by the assembly

On top of `PJoinFacts` (`union I = locRecs I ++ reqs I`, `p3_answers`, word bounds):
* `p3Union I`: the union sorted by `CSort.rle`; `p3Scan I`: the answers of the scan over it;
* `p3Ans_eq`: the answers sorted by `CSort.rle` are `ansAll I` (the order of `P4`);
* sizes: `length_flatten_union`, `union_mul_le` (`|union I| (ℓ + 1) ≤ 4 H`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma length_flatten_union :
    (union I).flatten.length = ((locRecs I).length + (reqs I).length) * (ℓ + 6) := by
  rw [List.length_flatten]
  have : (union I).map List.length = (union I).map fun _ => ℓ + 6 :=
    List.map_congr_left fun m hm => length_of_mem_union I hm
  rw [this, sum_map_const, union, List.length_append]

lemma union_mul_le : ((locRecs I).length + (reqs I).length) * (ℓ + 1) ≤ 4 * H I := by
  have h1 := length_locRecs_mul_le I
  have h2 := length_reqs_mul_le I
  nlinarith

/-- The sorted union of the location records and the requests. -/
noncomputable def p3Union : List (List ℕ) := (union I).mergeSort CSort.rle

/-- The answers of the scan (in the order of the sorted union). -/
noncomputable def p3Scan : List (List ℕ) := jScan ℓ (0, 0, 0) (p3Union I)

lemma mem_p3Union {m : List ℕ} : m ∈ p3Union I ↔ m ∈ union I :=
  (List.mergeSort_perm _ _).mem_iff

lemma length_p3Union : (p3Union I).length = (locRecs I).length + (reqs I).length := by
  rw [p3Union, List.length_mergeSort, union, List.length_append]

lemma length_p3Scan : (p3Scan I).length = (reqs I).length := by
  rw [p3Scan, p3Union, length_jScan I _ (List.Perm.refl _), length_reqs]

/-- **The answers of `P3`** in the order of `P4`. -/
lemma p3Ans_eq : (p3Scan I).reverse.mergeSort CSort.rle = ansAll I :=
  p3_answers I _ (List.Perm.refl _) _

lemma p3Scan_words (hE : I.schemas ≠ []) {w : ℕ} (hw : 4 * (H I + 1) ≤ 2 ^ w) :
    ∀ y ∈ p3Scan I, y.length = 4 ∧ ∀ z ∈ y, z < 2 ^ w := fun _ hy =>
  ⟨length_of_mem_jScan I _ (List.Perm.refl _) _ hy,
    lt_of_mem_jScan I hE hw _ (List.Perm.refl _) _ hy⟩

end Lax119563Proofs.Compiler
