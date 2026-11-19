import Lax119563Proofs.Compiler.P4SchGlue
import Lax119563Proofs.Compiler.P4SchC2b

/-!
# Pass `P4`, schema part: list glue for section 2 and the answers

* `col2_eq`: the update edges of a column are `col2E` of its rank codes;
* `ansE_flatten`: the answer words of a schema, per column for section 1 (`a1C`) and
  section 2 (`a2C`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma rcode_div (ρ : ℕ) : rcode ρ / 2 = ρ := by unfold rcode; omega

lemma length_rkL (e : Fin I.schemas.length) (c : Coord k ℓ) :
    (rkL I e c).length = (rowsL c).length := by simp [rkL]

/-- **The update edges of a column, in numbers** (`oU, mU`: the start answer of a binary
schema; arbitrary for a ternary one). -/
lemma col2_eq (ε : ZMod 2) (e : Fin I.schemas.length) {c : Coord k ℓ} (hc : c ∈ dom I e)
    (r : ℕ) (hr : (coordList (dom I e)).idxOf c = r) (hb : ℕ) (oU mU : ℕ)
    (hU : isTern (sch I e) = false → ∀ a, a < 2 →
      slotPos I ε (startCls I e c) ((a : ℕ) : ZMod 2) = cposN (locBase I) oU mU a) :
    (stepsC c).zipIdx.flatMap (fun q => hubE I ε (.upd e q.1 c) bits2
        (hb + 4 * (entBefore I e c + q.2))) =
      col2E (tnN (isTern (sch I e))) (hb + 4 * entBefore I e c)
        (trackBase I e + 2 * entBefore I e c) (sumBase I e + 2 * r) (coefBase I e)
        (2 * (rowsR I e).length) (locBase I) oU mU k ((rkL I e c).map rcode) := by
  rw [colE2_eq I ε hc hb, col2E]
  refine List.flatMap_congr fun q _ => ?_
  rw [rksE, List.length_map, length_rkL, List.zipIdx_map, List.flatMap_map]
  refine List.flatMap_congr fun x _ => ?_
  simp only [Prod.map, id, rcode_div]
  unfold updEnt entE
  have hci : coefBase I e + 2 * (q * (rowsR I e).length + x.1) =
      coefBase I e + q * (2 * (rowsR I e).length) + 2 * x.1 := by ring
  rw [hci]
  set t := q * (rowsL c).length + x.2 with ht_def
  have e1 : hb + 4 * (entBefore I e c + t) = hb + 4 * entBefore I e c + 4 * t := by ring
  have e2 : trackBase I e + 2 * (entBefore I e c + t) =
      trackBase I e + 2 * entBefore I e c + 2 * t := by ring
  rw [e1, e2]
  by_cases ht : isTern (sch I e) = true
  · have h1 : ¬ (t = 0 ∧ isTern (sch I e) = false) := by simp [ht]
    have h2 : ¬ (t = 0 ∧ tnN (isTern (sch I e)) = 0) := by simp [ht, tnN]
    rw [if_neg h1, if_neg h2, updL]
    unfold prevBase
    split_ifs with h0
    · rw [hr]
    · have e3 : trackBase I e + 2 * (entBefore I e c + t - 1) =
          trackBase I e + 2 * entBefore I e c + 2 * (t - 1) := by omega
      rw [e3]
  · have ht' : isTern (sch I e) = false := by simpa using ht
    by_cases h0 : t = 0
    · rw [if_pos ⟨h0, ht'⟩, if_pos ⟨h0, by simp [ht', tnN]⟩, updFL]
      refine List.flatMap_congr fun i hi => ?_
      have hi2 : i / 2 < 2 := by have := List.mem_range.mp hi; omega
      rw [hU ht' _ hi2, h0]
      simp
    · rw [if_neg (fun h => h0 h.1), if_neg (fun h => h0 h.1), updL, if_neg h0]
      unfold prevBase
      rw [if_neg h0]
      have e3 : trackBase I e + 2 * (entBefore I e c + t - 1) =
          trackBase I e + 2 * entBefore I e c + 2 * (t - 1) := by omega
      rw [e3]

end Lax119563Proofs.Compiler
