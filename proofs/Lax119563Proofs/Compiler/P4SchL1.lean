import Lax119563Proofs.Compiler.P4SchAns

/-!
# Pass `P4`, schema part: the column loop of section 1 (`p4S1_good`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## Column facts -/

/-- The columns of schema `e`. -/
noncomputable abbrev cL (e : Fin I.schemas.length) : List (Coord k ℓ) := coordList (dom I e)

/-- The entries of the first `r` columns. -/
noncomputable def entB (e : Fin I.schemas.length) (r : ℕ) : ℕ :=
  (((cL I e).take r).map fun c => (stepsC c).length).sum

/-- The rank codes of a column. -/
noncomputable def codesL (e : Fin I.schemas.length) (c : Coord k ℓ) : List ℕ :=
  (rkL I e c).map rcode

/-- The block-change count before column `r`. -/
noncomputable def distR (e : Fin I.schemas.length) (r : ℕ) : ℕ :=
  if r = 0 then 0 else dChg k (((cL I e).take r).map fun c => (c.1 : ℕ)) - 1

lemma length_stepsC_rowsL (c : Coord k ℓ) : (stepsC c).length = (k + 1) * (rowsL c).length := by
  rw [stepsC_eq, List.length_flatMap]
  simp [List.map_const', List.sum_replicate]

lemma rowsL_pos (hk : 2 ≤ k) (c : Coord k ℓ) : 1 ≤ (rowsL c).length := by
  have h := List.length_pos_of_ne_nil (stepsC_ne_nil hk c)
  rw [length_stepsC_rowsL] at h
  rcases Nat.eq_zero_or_pos (rowsL c).length with h0 | h0
  · rw [h0] at h; omega
  · exact h0

lemma length_codesL (e : Fin I.schemas.length) (c : Coord k ℓ) :
    (codesL I e c).length = (rowsL c).length := by simp [codesL, rkL]

lemma entBefore_get (e : Fin I.schemas.length) {r : ℕ} (hr : r < (cL I e).length) :
    entBefore I e (cL I e)[r] = entB I e r := by
  unfold entBefore entB
  rw [(nodup_coordList (dom I e)).idxOf_getElem]

lemma entB_succ (e : Fin I.schemas.length) {r : ℕ} (hr : r < (cL I e).length) :
    entB I e (r + 1) = entB I e r + (stepsC (cL I e)[r]).length := by
  simp only [entB, List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some,
    List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

lemma entB_le (e : Fin I.schemas.length) (r : ℕ) : entB I e r ≤ nEnt I e := by
  unfold entB nEnt cL
  conv_rhs => rw [← List.take_append_drop r (coordList (dom I e))]
  rw [List.map_append, List.sum_append]; omega

lemma codesL_pos (hk : 2 ≤ k) (e : Fin I.schemas.length) (c : Coord k ℓ) (X : ℕ)
    (hX : X ∈ codesL I e c) : 1 ≤ X := by
  simp only [codesL, List.mem_map] at hX
  obtain ⟨ρ, -, rfl⟩ := hX; unfold rcode; omega

end Lax119563Proofs.Compiler
