import Lax119563Proofs.Compiler.PEmitSch

/-!
# Pass `P4` (list level): the update edges of a column in loop form

`colE2_eq`: the update edges of column `c` are, for `q ≤ k` and the ranks `ρ` of its rows
(`rkL`, index `p`), the edges of the entry `t = q n + p` (`n = |rowsL c|`): hub
`hb + 4 (EB + t)`, coefficient position `coefBase + 2 (q |rowsR| + ρ)` (`updEnt`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (ε : ZMod 2)

/-- The ranks of the rows of a column in the nonzero rows of the domain. -/
noncomputable def rkL (e : Fin I.schemas.length) (c : Coord k ℓ) : List ℕ :=
  (rowsL c).map (rowsR I e).idxOf

/-- The edges of the update with entry index `t` and coefficient index `ci`. -/
noncomputable def updEnt (e : Fin I.schemas.length) (c : Coord k ℓ) (hb t ci : ℕ) :
    List (ℕ × ℕ) :=
  if t = 0 ∧ isTern (sch I e) = false then
    (List.range 4).flatMap fun i =>
      updF1 (hb + 4 * (entBefore I e c + t) + i) (trackBase I e + 2 * entBefore I e c)
        (coefBase I e + 2 * ci) (slotPos I ε (startCls I e c) (((i / 2 : ℕ)) : ZMod 2))
        (i / 2) (i % 2)
  else
    (List.range 4).flatMap fun i =>
      updE1 (hb + 4 * (entBefore I e c + t) + i) (prevBase I e c t)
        (trackBase I e + 2 * (entBefore I e c + t)) (coefBase I e + 2 * ci) (i / 2) (i % 2)

lemma idxOf_of_mem_zipIdx {α : Type*} [BEq α] [LawfulBEq α] {L : List α} (hL : L.Nodup)
    {x : α} {t : ℕ} (h : (x, t) ∈ L.zipIdx) : x ∈ L ∧ L.idxOf x = t := by
  obtain ⟨ht, hx⟩ := List.mem_zipIdx' h
  rw [hx]
  exact ⟨List.getElem_mem _, hL.idxOf_getElem _ _⟩

/-- **The update edges of a column.** -/
theorem colE2_eq {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) (hb : ℕ) :
    (stepsC c).zipIdx.flatMap (fun q => hubE I ε (.upd e q.1 c) bits2
        (hb + 4 * (entBefore I e c + q.2))) =
      (List.range (k + 1)).flatMap fun q => (rkL I e c).zipIdx.flatMap fun x =>
        updEnt I ε e c hb (q * (rowsL c).length + x.2) (q * (rowsR I e).length + x.1) := by
  -- first: per entry, by the hub lemmas
  have h1 : (stepsC c).zipIdx.flatMap (fun q => hubE I ε (.upd e q.1 c) bits2
        (hb + 4 * (entBefore I e c + q.2))) =
      (stepsC c).zipIdx.flatMap fun q => updEnt I ε e c hb q.2 ((coefSteps I e).idxOf q.1) := by
    refine List.flatMap_congr fun q hq => ?_
    obtain ⟨hmem, hidx⟩ := idxOf_of_mem_zipIdx (nodup_stepsC c) (x := q.1) (t := q.2) hq
    unfold updEnt
    split_ifs with h
    · rw [hubE_updF I ε hc hmem (by rw [hidx]; exact h.1) h.2]
    · rw [hubE_upd I ε hc hmem (by
        rcases Nat.eq_zero_or_pos q.2 with h0 | h0
        · right
          cases ht : isTern (sch I e)
          · exact absurd ⟨h0, ht⟩ h
          · rfl
        · left; rw [hidx]; exact h0), hidx]
  rw [h1]
  conv_lhs => rw [stepsC_eq]
  rw [zipIdx_flatMap_range (rowsL c) (fun q j => q * (k - 1 + ℓ) + j)
    (fun q => updEnt I ε e c hb q.2 ((coefSteps I e).idxOf q.1)) (k + 1) 0]
  refine List.flatMap_congr fun q hq => ?_
  rw [rkL, List.zipIdx_map, List.flatMap_map]
  refine List.flatMap_congr fun x hx => ?_
  have hj : x.1 ∈ rowsL c := (List.mem_zipIdx' hx).2 ▸ List.getElem_mem _
  simp only [Prod.map, id, Nat.zero_add]
  rw [idxOf_coefSteps I hc (List.mem_range.mp hq) hj]

end Lax119563Proofs.Compiler
