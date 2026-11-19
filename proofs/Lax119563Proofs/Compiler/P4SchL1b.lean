import Lax119563Proofs.Compiler.P4SchL1

/-!
# Pass `P4`, schema part: the column loop of section 1, invariant and step
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The column loop of section 1. -/
def p4S1 : CStm CR CQ := .loop (.lt (rv r4K) (rv r4D)) p4C1

/-- The state of the column loop of section 1 after `r` columns. -/
def L1Inv (w : ℕ) (ε : ZMod 2) (e : Fin I.schemas.length) (R : List ℕ) (s0 : NSt CR CQ)
    (r : ℕ) (s : NSt CR CQ) : Prop :=
  EM s0 s (((cL I e).zipIdx.take r).flatMap fun q => colE1 I ε e q.1 q.2) ∧
  s.stk qRk = (((cL I e).take r).flatMap fun c => codesL I e c ++ [0]).reverse ++ s0.stk qRk ∧
  s.stk qAns = ((cL I e).zipIdx.drop r).flatMap (a1C I e) ++ R ∧
  s.stk qA2 = (((cL I e).zipIdx.take r).flatMap (a1C I e)).reverse ++ s0.stk qA2 ∧
  (∀ q, q ≠ q4E → q ≠ qRk → q ≠ qAns → q ≠ qA2 → s.stk q = s0.stk q) ∧
  s.env r4K = r ∧ s.env r4Dist = distR I e r ∧
  (∀ h : r - 1 < (cL I e).length, 0 < r → s.env r4Prev = (((cL I e)[r - 1]'h).1 : ℕ)) ∧
  s.env r4H = schBase I e + r * colW I e ∧ s.env r4SP = sumBase I e + 2 * r ∧
  s.env r4TP = trackBase I e + 2 * entB I e r ∧ s.env r4V < 2 ^ w ∧ s.Bdd w ∧
  s.pos = s0.pos + (encodeNats (((cL I e).take r).flatMap cdesc)).length ∧ s.out = s0.out ∧
  ∀ reg, reg ∉ c1W → s.env reg = s0.env reg

lemma zipIdx_drop_cons {α : Type*} (l : List α) {r : ℕ} (hr : r < l.length) :
    l.zipIdx.drop r = (l[r], r) :: l.zipIdx.drop (r + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hr)]
  simp [List.getElem_zipIdx]

lemma zipIdx_take_succ {α : Type*} (l : List α) {r : ℕ} (hr : r < l.length) :
    l.zipIdx.take (r + 1) = l.zipIdx.take r ++ [(l[r], r)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hr)]
  simp [List.getElem_zipIdx]

lemma cdesc_split (l : List (Coord k ℓ)) {r : ℕ} (hr : r < l.length) :
    l.flatMap cdesc = (l.take r).flatMap cdesc ++
      ((l[r].1 : ℕ) :: blockDescription l[r].2 ++ (l.drop (r + 1)).flatMap cdesc) := by
  have h : l.flatMap cdesc = (l.take r).flatMap cdesc ++ (l.drop r).flatMap cdesc := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [h, List.drop_eq_getElem_cons hr, List.flatMap_cons]
  simp [cdesc]

/-! ## Answers are well formed -/

lemma aOff_le (hE : I.schemas ≠ []) {v : Fin I.numLocations} {c' : Coord k ℓ}
    (hc : c' ∈ I.domain v) (s : ℕ) : aOff (ansRec I v c' s) ≤ 2 * H I := by
  have hm := le_of_mem_locRecs I hE ((mem_locRecs I).mpr ⟨v, c', hc, rfl⟩)
  have h1 := hm (locOff I v + (coordList (I.domain v)).idxOf c' * labsN I v) (by simp [locRecC])
  rw [off_eq I hc] at h1
  simpa [aOff, ansRec] using h1

lemma ansRec_ok {w : ℕ} {v : Fin I.numLocations} {c' : Coord k ℓ} (s : ℕ) (hs : s < 2 ^ w)
    (ho : aOff (ansRec I v c' s) < 2 ^ w) (hw : 2 ≤ w) : AnsOK w (ansRec I v c' s) := by
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  refine ⟨_, _, _, _, rfl, labsN_cases I v, ?_, ?_⟩
  · have := ZMod.val_lt (initSeed I v c'); omega
  · have := ZMod.val_lt (initSeed I v c')
    have := labsN_cases I v
    intro x hx
    simp only [ansRec, List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [aOff, ansRec, List.getD_cons_succ, List.getD_cons_zero] at ho
    rcases hx with rfl | rfl | rfl | rfl <;> omega

/-! ## Section bounds -/

lemma sec_bounds (e : Fin I.schemas.length) :
    schBase I e + (cL I e).length * colW I e + 4 * nEnt I e + sumSize I e + 2 * nEnt I e ≤
      locBase I ∧ sumSize I e = 2 * tnN (Matrix.isTern (sch I e)) * (cL I e).length ∧
      colW I e = 2 + 4 * tnN (Matrix.isTern (sch I e)) ∧
      sumBase I e = schBase I e + (cL I e).length * colW I e + 4 * nEnt I e ∧
      trackBase I e = sumBase I e + sumSize I e ∧ coefBase I e = trackBase I e + 2 * nEnt I e := by
  have h1 := schBase_add_le I e
  rw [schSize_eq] at h1
  refine ⟨by unfold hubSize at h1; simp only [cL]; omega, ?_, ?_,
    by simp [sumBase, hubSize, cL]; omega, rfl, rfl⟩
  · unfold sumSize tnN; split_ifs <;> simp
  · unfold colW tnN; split_ifs <;> omega

end Lax119563Proofs.Compiler
