import Lax119563Proofs.Compiler.P4SchC1c
import Lax119563Proofs.Compiler.PEmitBlk
import Lax119563Proofs.Compiler.PEmitCol2

/-!
# Pass `P4`, schema part: list glue for the rank codes

* `codesC_eq`: the rank codes computed by section 1 for the column `D[r]` are
  `(rkL I e D[r]).map rcode`, with the running block-change count `dChg k (blocks of D[0..r]) - 1`;
* `dist1_eq`: the update of that count by `p4Hd`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma blkRows_le (cs : List (Coord k ℓ)) : blkRows cs ≤ k - 1 := by
  unfold blkRows
  exact (List.countP_le_length).trans (by simp)

lemma idxOf_rowsR_all (e : Fin I.schemas.length) {c : Coord k ℓ}
    (hc : c ∈ coordList (dom I e)) (hck : ¬ (c.1 : ℕ) + 1 < k) {j : ℕ} (hj : j < k - 1) :
    (rowsR I e).idxOf j = j := by
  have hP : ∀ j', PA I e j' = true := fun j' => by
    simp only [PA, decide_eq_true_eq]; exact ⟨c, hc, Or.inr (by have := c.1.2; omega)⟩
  rw [rank_blk I e hj (hP j), List.countP_eq_length.mpr (fun j' _ => hP j'), List.length_range]

/-- **The rank codes of a column.** -/
lemma codesC_eq (hk : 2 ≤ k) (e : Fin I.schemas.length) {r : ℕ}
    (hr : r < (coordList (dom I e)).length) :
    codesC k (blkRows (coordList (dom I e)))
        (dChg k (((coordList (dom I e)).take (r + 1)).map fun c => (c.1 : ℕ)) - 1)
        ((coordList (dom I e))[r].1 : ℕ) (orsL (coordList (dom I e)))
        (blockDescription (coordList (dom I e))[r].2) =
      (rkL I e (coordList (dom I e))[r]).map rcode := by
  set c := (coordList (dom I e))[r] with hcdef
  have hcD : c ∈ coordList (dom I e) := List.getElem_mem hr
  have hce : c ∈ dom I e := mem_coordList.mp hcD
  rw [rkL, rowsL_eq, List.map_append, List.map_append, codesC, chkRanks_eq I e hce]
  congr 1
  unfold blkCodes
  by_cases hck : (c.1 : ℕ) + 1 < k
  · rw [if_pos hck, if_pos hck]
    simp only [List.map_cons, List.map_nil]
    rw [rank_blk_eq I e hr hck]
    have := blkRows_le (coordList (dom I e))
    by_cases hB : blkRows (coordList (dom I e)) = k - 1
    · rw [if_pos hB, if_neg (by omega)]
    · rw [if_neg hB, if_pos (by omega)]
  · rw [if_neg hck, if_neg hck, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp_apply]
    rw [idxOf_rowsR_all I e hcD hck (List.mem_range.mp hj)]

lemma dChg_pos (p : ℕ) : ∀ (l : List ℕ), l ≠ [] → (∀ x ∈ l, x ≠ p) → 1 ≤ dChg p l
  | [], h, _ => absurd rfl h
  | a :: l, _, h => by
    simp only [dChg, if_neg (h a List.mem_cons_self)]; omega

/-- **The block-change count after a column.** -/
lemma dist1_eq (cs : List (Coord k ℓ)) {r : ℕ} (hr : r < cs.length) (P : ℕ)
    (hP : 0 < r → P = (cs[r - 1].1 : ℕ)) :
    dist1 r (if r = 0 then 0 else dChg k ((cs.take r).map fun c => (c.1 : ℕ)) - 1) P
        (cs[r].1 : ℕ) = dChg k ((cs.take (r + 1)).map fun c => (c.1 : ℕ)) - 1 := by
  have hlt : ∀ c : Coord k ℓ, (c.1 : ℕ) ≠ k := fun c => by have := c.1.2; omega
  rw [List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some, List.map_append,
    List.map_singleton, dChg_append]
  unfold dist1
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp [dChg, hlt]
  · rw [if_neg (by omega), if_neg (by omega)]
    have hne : (cs.take r).map (fun c => (c.1 : ℕ)) ≠ [] := by
      intro h; have := congrArg List.length h
      simp only [List.length_map, List.length_take, List.length_nil] at this; omega
    have h1 := dChg_pos k _ hne (by simp only [List.mem_map]; rintro _ ⟨c, -, rfl⟩; exact hlt c)
    have hlast : ((cs.take r).map fun c => (c.1 : ℕ)).getLastD k = (cs[r - 1].1 : ℕ) := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
      simp [List.getElem?_take, show r - 1 < r by omega, List.getElem?_eq_getElem
        (show r - 1 < cs.length by omega), Nat.min_eq_left hr.le]
    rw [hlast, hP hr0]
    omega

/-! ## Coordinate slots by the answers, in numbers -/

lemma labsN_cases (v : Fin I.numLocations) : labsN I v = 1 ∨ labsN I v = 2 := by
  unfold labsN coordLabs
  split_ifs <;> simp [bits1]

lemma slot_ans (ε : ZMod 2) {v : Fin I.numLocations} {c' : Coord k ℓ} (hc : c' ∈ I.domain v)
    {b : ℕ} (hb : b < 2) (s : ℕ) :
    slotPos I ε (.coord v c') ((b : ℕ) : ZMod 2) =
      cposN (locBase I) (aOff (ansRec I v c' s)) (ansMode ε.val (ansRec I v c' s)) b := by
  rw [slotPos_coord_ans I ε hc _ s, val_natCast_lt hb]
  refine cposA_eq _ _ _ _ (by omega) (by have := ZMod.val_lt ε; omega) ?_ ?_
  · simp only [ansRec, List.getD_cons_succ, List.getD_cons_zero]
    have := ZMod.val_lt (initSeed I v c'); omega
  · simpa [ansRec] using labsN_cases I v

lemma memU {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) :
    (permU (sch I e)).apply c ∈ I.domain (locU (sch I e)) := by
  have hw := wf_sch I e
  unfold dom at hc
  generalize sch I e = sc at hw hc
  cases sc with
  | binary u v D σ τ => exact hw.2.1 (Finset.mem_image_of_mem _ hc)
  | ternary u v w' D σ τ π => exact hw.2.2.2.1 (Finset.mem_image_of_mem _ hc)

lemma memV {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) :
    (permV (sch I e)).apply c ∈ I.domain (locV (sch I e)) := by
  have hw := wf_sch I e
  unfold dom at hc
  generalize sch I e = sc at hw hc
  cases sc with
  | binary u v D σ τ => exact hw.2.2 (Finset.mem_image_of_mem _ hc)
  | ternary u v w' D σ τ π => exact hw.2.2.2.2.1 (Finset.mem_image_of_mem _ hc)

lemma memEnd {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) :
    (permEnd (sch I e)).apply c ∈ I.domain (locEnd (sch I e)) := by
  have hw := wf_sch I e
  unfold dom at hc
  generalize sch I e = sc at hw hc
  cases sc with
  | binary u v D σ τ => exact hw.2.2 (Finset.mem_image_of_mem _ hc)
  | ternary u v w' D σ τ π => exact hw.2.2.2.2.2 (Finset.mem_image_of_mem _ hc)

/-- `tern` as a number. -/
def tnN (b : Bool) : ℕ := if b then 1 else 0

/-- **The junction and link edges of a column, in numbers.** -/
lemma colE1_eq (hk : 2 ≤ k) (ε : ZMod 2) (e : Fin I.schemas.length) {c : Coord k ℓ}
    (hc : c ∈ dom I e) (r : ℕ) (hr : (coordList (dom I e)).idxOf c = r) (sU sV sW : ℕ) :
    colE1 I ε e c r = col1E (tnN (isTern (sch I e))) (schBase I e + r * colW I e)
      (sumBase I e + 2 * r) (trackBase I e + 2 * (entBefore I e c + (stepsC c).length - 1))
      (locBase I) ε.val
      (ansRec I (locU (sch I e)) ((permU (sch I e)).apply c) sU)
      (ansRec I (locV (sch I e)) ((permV (sch I e)).apply c) sV)
      (ansRec I (locEnd (sch I e)) ((permEnd (sch I e)).apply c) sW) := by
  have hL : hubE I ε (.link e c) bits1 (schBase I e + r * colW I e +
      (if isTern (sch I e) then 4 else 0)) = lnkL (schBase I e + r * colW I e +
        4 * tnN (isTern (sch I e))) (trackBase I e + 2 * (entBefore I e c + (stepsC c).length - 1))
        (locBase I) (aOff (ansRec I (locEnd (sch I e)) ((permEnd (sch I e)).apply c) sW))
        (ansMode ε.val (ansRec I (locEnd (sch I e)) ((permEnd (sch I e)).apply c) sW)) := by
    rw [hubE_link I ε hk hc, lnkL]
    have h4 : (if isTern (sch I e) then 4 else 0) = 4 * tnN (isTern (sch I e)) := by
      unfold tnN; split_ifs <;> rfl
    rw [h4]
    refine List.flatMap_congr fun a ha => ?_
    have ha2 : a < 2 := List.mem_range.mp ha
    rw [endCls, slot_ans I ε (memEnd I hc) ha2 sW]
  unfold colE1 col1E
  rw [hL]
  congr 1
  cases ht : isTern (sch I e)
  · simp [tnN]
  · simp only [if_true, tnN]
    rw [hubE_junc I ε ht hc, junL, hr]
    refine List.flatMap_congr fun i hi => ?_
    have hi1 : i / 2 < 2 := by have := List.mem_range.mp hi; omega
    have hi2 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rw [coordU, coordV, slot_ans I ε (memU I hc) hi1 sU, slot_ans I ε (memV I hc) hi2 sV]

end Lax119563Proofs.Compiler
