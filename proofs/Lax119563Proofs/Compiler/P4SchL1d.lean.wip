import Lax119563Proofs.Compiler.P4SchL1c

/-!
# Pass `P4`, schema part: the column loop of section 1 (`p4S1_good`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma length_le_encodeNats : ∀ l : List ℕ, l.length ≤ (encodeNats l).length
  | [] => by simp [encodeNats]
  | v :: l => by
    rw [encNats_cons, List.length_append, length_encodeNat, List.length_cons]
    have := length_le_encodeNats l; omega

lemma col1_cost (N E S ℓ k n : ℕ) (hl : ℓ + 1 ≤ E) (hS : S = (k + 1) * n) (hn : 1 ≤ n) :
    200 * (E + ℓ + (k + 2) * (n + 1) + 10) * N ≤ 800 * N * (E + 2 * S) + 2000 * N := by
  subst hS
  have h1 : (k + 2) * (n + 1) ≤ 4 * ((k + 1) * n) := by nlinarith
  have h2 : 200 * (E + ℓ + (k + 2) * (n + 1) + 10) ≤ 800 * (E + 2 * ((k + 1) * n)) + 2000 := by
    omega
  calc 200 * (E + ℓ + (k + 2) * (n + 1) + 10) * N
      ≤ (800 * (E + 2 * ((k + 1) * n)) + 2000) * N := Nat.mul_le_mul_right _ h2
    _ = 800 * N * (E + 2 * ((k + 1) * n)) + 2000 * N := by ring

set_option maxHeartbeats 8000000 in
/-- **The column loop of section 1.** -/
lemma p4S1_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (hk : 2 ≤ k) (hE : I.schemas ≠ [])
    (ε : ZMod 2) (e : Fin I.schemas.length) (R : List ℕ) (restx : List Bool) (s0 : NSt CR CQ)
    (hF : L1Fix I w x ε e restx s0) (hB : L1Bnd I w e s0)
    (hMe : ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2).length ≤ 3 * (ordL I).length)
    (hI0 : L1Inv I w ε e R s0 0 s0) :
    ∃ s', Good x w p4S1 s0 s' (800 * Ex.nodeCost w *
        ((encodeNats ((cL I e).flatMap cdesc)).length + 2 * nEnt I e) +
        (cL I e).length * (2000 * Ex.nodeCost w + condCost w (.lt (rv r4K) (rv r4D))) +
        condCost w (.lt (rv r4K) (rv r4D))) ∧
      L1Inv I w ε e R s0 (cL I e).length s' := by
  have hD := hF.2.2.2.2.2.2.2.1
  set P1 := s0.pos + (encodeNats ((cL I e).flatMap cdesc)).length
  set T1 := trackBase I e + 2 * nEnt I e
  obtain ⟨s', g, ⟨r, hr, hI⟩, hc⟩ := Good.loop_var (x := x) (w := w)
    (e := .lt (rv r4K) (rv r4D)) (body := p4C1)
    (fun s => ∃ r, r ≤ (cL I e).length ∧ L1Inv I w ε e R s0 r s)
    (fun s => (cL I e).length - s.env r4K) (fun s => (P1 - s.pos) + (T1 - s.env r4TP))
    (800 * Ex.nodeCost w) (2000 * Ex.nodeCost w)
    (by
      rintro s ⟨r, hr, hI⟩
      have eK := hI.2.2.2.2.2.1
      have eD : s.env r4D = (cL I e).length := by rw [hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), hD]
      have hbd := hI.2.2.2.2.2.2.2.2.2.2.2.1
      refine ⟨⟨hbd.1 _, hbd.1 _⟩, fun hc => ?_⟩
      have hr' : r < (cL I e).length := by
        simp only [Ex.eval, rv, eK, eD] at hc; split_ifs at hc with h <;> omega
      obtain ⟨s', g, hI'⟩ := p4S1_step I hw hk hE ε e R restx s0 hF hB hMe r hr' s hI
      have eK' := hI'.2.2.2.2.2.1
      have eTP := hI.2.2.2.2.2.2.2.2.2.2.1
      have eTP' := hI'.2.2.2.2.2.2.2.2.2.2.1
      have ep := hI.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have ep' := hI'.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hst := length_stepsC_rowsL (cL I e)[r]
      have hrow := rowsL_pos hk (cL I e)[r]
      have hsucc := entB_succ I e hr'
      have hle := entB_le I e (r + 1)
      have hlen : ((encodeNats (((cL I e).take (r + 1)).flatMap cdesc)).length =
          (encodeNats (((cL I e).take r).flatMap cdesc)).length +
            (encodeNats (cdesc (cL I e)[r])).length) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hr']
        simp [encodeNats_append]
      have hall : (encodeNats (((cL I e).take (r + 1)).flatMap cdesc)).length ≤
          (encodeNats ((cL I e).flatMap cdesc)).length := by
        conv_rhs => rw [← List.take_append_drop (r + 1) (cL I e)]
        rw [List.flatMap_append, encodeNats_append, List.length_append]; omega
      have hl := length_le_encodeNats (cdesc (cL I e)[r])
      rw [length_cdesc] at hl
      refine ⟨s', g.mono ?_, ⟨r + 1, hr', hI'⟩, by rw [eK, eK']; omega, by omega⟩
      have hΔ : (P1 - s.pos + (T1 - s.env r4TP)) - (P1 - s'.pos + (T1 - s'.env r4TP)) =
          (encodeNats (cdesc (cL I e)[r])).length + 2 * (stepsC (cL I e)[r]).length := by
        rw [eTP, eTP', ep, ep']; simp only [P1, T1]; omega
      rw [hΔ]
      exact col1_cost _ _ _ _ _ _ hl hst hrow)
    s0 ⟨0, by omega, hI0⟩
  have eK := hI.2.2.2.2.2.1
  have eD : s'.env r4D = (cL I e).length := by rw [hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), hD]
  have hr' : r = (cL I e).length := by
    simp only [Ex.eval, rv, eK, eD] at hc; split_ifs at hc with h <;> omega
  subst hr'
  refine ⟨s', g.mono ?_, hI⟩
  have eK0 : s0.env r4K = 0 := hI0.2.2.2.2.2.1
  have eTP0 := hI0.2.2.2.2.2.2.2.2.2.2.1
  simp only [eK0, Nat.sub_zero, eTP0, P1, T1, entB, List.take_zero, List.map_nil, List.sum_nil]
  have : s0.pos + (encodeNats ((cL I e).flatMap cdesc)).length - s0.pos =
    (encodeNats ((cL I e).flatMap cdesc)).length := by omega
  rw [this]
  simp

end Lax119563Proofs.Compiler
