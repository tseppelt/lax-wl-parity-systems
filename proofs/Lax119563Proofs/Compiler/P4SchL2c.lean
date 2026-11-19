import Lax119563Proofs.Compiler.P4SchL2b

/-!
# Pass `P4`, schema part: the column loop of section 2 (`p4S2_good`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The edges of a schema: section 1 per column, then the update edges `colE2` per column. -/
lemma schE_eq2 (ε : ZMod 2) (e : Fin I.schemas.length) : schE I ε e =
    (cL I e).zipIdx.flatMap (fun q => colE1 I ε e q.1 q.2) ++ (cL I e).flatMap (colE2 I ε e) := by
  rw [schE_eq]; rfl

lemma col2_cost (N k n : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) :
    (k + 3) * ((n + 1) * (800 * N)) ≤ 1600 * N * (2 * ((k + 1) * n)) + 0 := by
  have h : (k + 3) * (n + 1) ≤ 4 * ((k + 1) * n) := by nlinarith
  calc (k + 3) * ((n + 1) * (800 * N)) = (k + 3) * (n + 1) * (800 * N) := by ring
    _ ≤ 4 * ((k + 1) * n) * (800 * N) := Nat.mul_le_mul_right _ h
    _ = 1600 * N * (2 * ((k + 1) * n)) + 0 := by ring

set_option maxHeartbeats 8000000 in
/-- **The column loop of section 2** of schema `e`: pushes the update edges of all columns,
consumes the rank codes (each column terminated by `0`) from `qRkF` and the start answers
(`a2C`, binary schemas) from `qAns`. -/
theorem p4S2_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (hk : 2 ≤ k) (ε : ZMod 2)
    (e : Fin I.schemas.length) (R Q : List ℕ) (s0 : NSt CR CQ)
    (hF : L2Fix I x ε e s0) (hB : L2Bnd I w ε e s0)
    (h0R : s0.stk qRkF = (cL I e).flatMap (fun c => codesL I e c ++ [0]) ++ Q)
    (h0B : s0.stk qOrsB = [])
    (h0A : s0.stk qAns = (cL I e).zipIdx.flatMap (a2C I e) ++ R)
    (e0K : s0.env r4K = 0) (e0H : s0.env r4H = updBase I e)
    (e0TP : s0.env r4TP = trackBase I e) (e0SP : s0.env r4SP = sumBase I e) (hbd : s0.Bdd w) :
    ∃ s', Good x w p4S2 s0 s' (3200 * Ex.nodeCost w * nEnt I e +
        (cL I e).length * condCost w (.lt (rv r4K) (rv r4D)) +
        condCost w (.lt (rv r4K) (rv r4D))) ∧
      EE s0 s' ((cL I e).flatMap (colE2 I ε e)) ∧
      s'.stk qRkF = Q ∧ s'.stk qOrsB = [] ∧ s'.stk qAns = R ∧
      s'.stk qA2 = ((cL I e).zipIdx.flatMap (a2C I e)).reverse ++ s0.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qRkF → q ≠ qOrsB → q ≠ qAns → q ≠ qA2 → s'.stk q = s0.stk q) ∧
      s'.env r4K = (cL I e).length ∧ s'.env r4H = updBase I e + 4 * nEnt I e ∧
      s'.env r4TP = coefBase I e ∧ s'.env r4SP = sumBase I e + 2 * (cL I e).length ∧
      s'.Bdd w ∧ ∀ reg, reg ∉ c2W → s'.env reg = s0.env reg := by
  have hD := hF.2.2.2.2.1
  have hI0 : L2Inv I w ε e R Q s0 0 s0 := by
    refine ⟨by simpa using EE.refl s0, by simpa using h0R, h0B, by simpa using h0A, by simp,
      fun _ _ _ _ _ _ => rfl, e0K, by simp [entB, e0H], by simp [entB, e0TP], by simp [e0SP],
      hbd, fun _ _ => rfl⟩
  have hcB : coefBase I e = trackBase I e + 2 * nEnt I e := rfl
  obtain ⟨s', g, ⟨r, hr, hI⟩, hc⟩ := Good.loop_var (x := x) (w := w)
    (e := .lt (rv r4K) (rv r4D)) (body := p4C2)
    (fun s => ∃ r, r ≤ (cL I e).length ∧ L2Inv I w ε e R Q s0 r s)
    (fun s => (cL I e).length - s.env r4K) (fun s => coefBase I e - s.env r4TP)
    (1600 * Ex.nodeCost w) 0
    (by
      rintro s ⟨r, hr, hI⟩
      have eK := hI.2.2.2.2.2.2.1
      have eD : s.env r4D = (cL I e).length := by
        rw [hI.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), hD]
      have hbd := hI.2.2.2.2.2.2.2.2.2.2.1
      refine ⟨⟨hbd.1 _, hbd.1 _⟩, fun hc => ?_⟩
      have hr' : r < (cL I e).length := by
        simp only [Ex.eval, eK, eD] at hc; split_ifs at hc with h <;> omega
      obtain ⟨s', g, hI'⟩ := p4S2_step I hw hk ε e R Q s0 hF hB r hr' s hI
      have eK' := hI'.2.2.2.2.2.2.1
      have eTP := hI.2.2.2.2.2.2.2.2.1
      have eTP' := hI'.2.2.2.2.2.2.2.2.1
      have hst := length_stepsC_rowsL (cL I e)[r]
      have hrow := rowsL_pos hk (cL I e)[r]
      have hsucc := entB_succ I e hr'
      have hle := entB_le I e (r + 1)
      refine ⟨s', g.mono ?_, ⟨r + 1, hr', hI'⟩, by rw [eK, eK']; omega, by omega⟩
      have hΔ : (coefBase I e - s.env r4TP) - (coefBase I e - s'.env r4TP) =
          2 * ((k + 1) * (rowsL (cL I e)[r]).length) := by
        rw [eTP, eTP', hcB]; omega
      rw [hΔ]
      exact col2_cost _ _ _ hk hrow)
    s0 ⟨0, by omega, hI0⟩
  have eK := hI.2.2.2.2.2.2.1
  have eD : s'.env r4D = (cL I e).length := by
    rw [hI.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), hD]
  have hr' : r = (cL I e).length := by
    simp only [Ex.eval, eK, eD] at hc; split_ifs at hc with h <;> omega
  subst hr'
  obtain ⟨hEE, hR, hOB, hA, hA2, hso, eK1, eH, eTP, eSP, hbd1, hfr⟩ := hI
  have hall := entB_all I e
  refine ⟨s', g.mono ?_, by simpa using hEE, by simpa using hR, hOB, by
      rw [hA, List.drop_of_length_le (by simp)]; simp,
    by rw [hA2, List.take_of_length_le (by simp)], hso, eK1, by rw [eH, hall], by rw [eTP, hall, hcB], eSP, hbd1, hfr⟩
  rw [e0K, e0TP, hcB]
  have : trackBase I e + 2 * nEnt I e - trackBase I e = 2 * nEnt I e := by omega
  rw [this, Nat.sub_zero]
  have h2 : 1600 * Ex.nodeCost w * (2 * nEnt I e) = 3200 * Ex.nodeCost w * nEnt I e := by ring
  rw [h2, Nat.zero_add]

end Lax119563Proofs.Compiler
