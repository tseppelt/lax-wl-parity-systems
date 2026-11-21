import Lax119563Proofs.Compiler.P4SchL1c

/-!
# Pass `P4`, schema part: the column loop of section 1 (`p4S1_good`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

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
/-- The column loop of section 1, in terms of the invariant. -/
lemma p4S1_loop {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (hk : 2 ≤ k) (hE : I.schemas ≠ [])
    (ε : ZMod 2) (e : Fin I.schemas.length) (R : List ℕ) (restx : List Bool) (s0 : NSt CR CQ)
    (hF : L1Fix I w x ε e restx s0) (hB : L1Bnd I w e s0)
    (hMe : ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2).length ≤ 3 * (ordL I).length)
    (hI0 : L1Inv I w ε e R s0 0 s0) :
    ∃ s', Good x w p4S1 s0 s' (800 * Ex.nodeCost w *
        ((encodeNats ((cL I e).flatMap cdesc)).length + 2 * nEnt I e) +
        (cL I e).length * (2000 * Ex.nodeCost w + condCost w (.lt (rv r4K) (rv r4D))) +
        condCost w (.lt (rv r4K) (rv r4D))) ∧
      L1Inv I w ε e R s0 (cL I e).length s' := by
  have hD : s0.env r4D = (cL I e).length := hF.2.2.2.2.2.2.2.1
  obtain ⟨P1, hP1⟩ : ∃ P1, P1 = s0.pos + (encodeNats ((cL I e).flatMap cdesc)).length := ⟨_, rfl⟩
  obtain ⟨T1, hT1⟩ : ∃ T1, T1 = trackBase I e + 2 * nEnt I e := ⟨_, rfl⟩
  obtain ⟨s', g, ⟨r, hr, hI⟩, hc⟩ := Good.loop_var (x := x) (w := w)
    (e := .lt (rv r4K) (rv r4D)) (body := p4C1)
    (fun s => ∃ r, r ≤ (cL I e).length ∧ L1Inv I w ε e R s0 r s)
    (fun s => (cL I e).length - s.env r4K) (fun s => (P1 - s.pos) + (T1 - s.env r4TP))
    (800 * Ex.nodeCost w) (2000 * Ex.nodeCost w)
    (by
      rintro s ⟨r, hr, hI⟩
      have eK := hI.2.2.2.2.2.1
      have eD : s.env r4D = (cL I e).length := by
        rw [hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), hD]
      have hbd := hI.2.2.2.2.2.2.2.2.2.2.2.2.1
      refine ⟨⟨by simp only [Ex.Fits]; exact hbd.1 _, by simp only [Ex.Fits]; exact hbd.1 _⟩,
        fun hc => ?_⟩
      have hr' : r < (cL I e).length := by
        by_contra h; apply hc; simp only [Ex.eval, eK, eD]; rw [if_neg h]
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
      have hlen : (encodeNats (((cL I e).take (r + 1)).flatMap cdesc)).length =
          (encodeNats (((cL I e).take r).flatMap cdesc)).length +
            (encodeNats (cdesc (cL I e)[r])).length := by
        rw [List.take_add_one, List.getElem?_eq_getElem hr', Option.toList_some,
          List.flatMap_append, List.flatMap_singleton, encodeNats_append, List.length_append]
      have hall : (encodeNats (((cL I e).take (r + 1)).flatMap cdesc)).length ≤
          (encodeNats ((cL I e).flatMap cdesc)).length := by
        conv_rhs => rw [← List.take_append_drop (r + 1) (cL I e)]
        rw [List.flatMap_append, encodeNats_append, List.length_append]; omega
      have hl := length_le_encodeNats (cdesc (cL I e)[r])
      rw [length_cdesc] at hl
      have hΔ : (P1 - s.pos + (T1 - s.env r4TP)) - (P1 - s'.pos + (T1 - s'.env r4TP)) =
          (encodeNats (cdesc (cL I e)[r])).length + 2 * (stepsC (cL I e)[r]).length := by
        rw [eTP, eTP', ep, ep', hP1, hT1]; omega
      refine ⟨s', g.mono ?_, ⟨r + 1, hr', hI'⟩, by rw [eK, eK']; omega, by
        rw [eTP, eTP', ep, ep', hP1, hT1]; omega⟩
      rw [hΔ]
      exact col1_cost _ _ _ _ _ _ hl hst hrow)
    s0 ⟨0, by omega, hI0⟩
  have eK := hI.2.2.2.2.2.1
  have eD : s'.env r4D = (cL I e).length := by
    rw [hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), hD]
  have hr' : r = (cL I e).length := by
    by_contra h; simp only [Ex.eval, eK, eD] at hc; rw [if_pos (by omega)] at hc
    exact one_ne_zero hc
  subst hr'
  refine ⟨s', g.mono (le_of_eq ?_), hI⟩
  have eK0 : s0.env r4K = 0 := hI0.2.2.2.2.2.1
  have eTP0 : s0.env r4TP = trackBase I e + 2 * entB I e 0 := hI0.2.2.2.2.2.2.2.2.2.2.1
  have hφ : P1 - s0.pos + (T1 - s0.env r4TP) =
      (encodeNats ((cL I e).flatMap cdesc)).length + 2 * nEnt I e := by
    rw [eTP0, hP1, hT1]; simp only [entB, List.take_zero, List.map_nil, List.sum_nil]; omega
  rw [hφ, eK0, Nat.sub_zero]

lemma p4S1_cond (w : ℕ) : condCost w (.lt (rv r4K) (rv r4D)) ≤ 4 * Ex.nodeCost w := by
  have h1 := CStm.nodeCost_ge w
  have h2 := CStm.unitCost_ge w
  simp only [condCost, Ex.size]
  omega

lemma p4S1_costN (N E n m c : ℕ) (hc : c ≤ 4 * N) :
    800 * N * (E + 2 * n) + m * (2000 * N + c) + c ≤ 2100 * (E + n + m + 1) * N := by
  have h1 : m * (2000 * N + c) ≤ m * (2004 * N) := Nat.mul_le_mul_left _ (by omega)
  have h2 : 800 * N * (E + 2 * n) + m * (2004 * N) + 4 * N ≤ 2100 * (E + n + m + 1) * N := by
    nlinarith
  omega

lemma entB_all_L1d (e : Fin I.schemas.length) : entB I e (cL I e).length = nEnt I e := by
  simp [entB, nEnt]

lemma L1Inv_zero {w : ℕ} (ε : ZMod 2) (e : Fin I.schemas.length) (R : List ℕ) (s0 : NSt CR CQ)
    (eK : s0.env r4K = 0) (eDi : s0.env r4Dist = 0) (eH : s0.env r4H = schBase I e)
    (eSP : s0.env r4SP = sumBase I e) (eTP : s0.env r4TP = trackBase I e)
    (hV : s0.env r4V < 2 ^ w) (hbd : s0.Bdd w)
    (hA : s0.stk qAns = (cL I e).zipIdx.flatMap (a1C I e) ++ R) :
    L1Inv I w ε e R s0 0 s0 := by
  refine ⟨⟨by simp [pairsRev], by simp⟩, by simp, by simpa using hA, by simp, fun _ _ _ _ _ => rfl,
    eK, by rw [eDi]; simp [distR], fun _ h => absurd h (lt_irrefl 0), by rw [eH]; simp,
    by rw [eSP]; simp, by rw [eTP]; simp [entB], hV, hbd, by simp [encodeNats], rfl,
    fun _ _ => rfl⟩

set_option maxHeartbeats 4000000 in
/-- **The column loop of section 1** (`p4S1`) over the columns `cL I e` of schema `e`: it pushes
the junction and link edges of all columns (`colE1`, the first part of `schE_eq`), the rank codes
of every column (`codesL`, each list terminated by `0`), moves the section-1 answers
(`a1C`, the first part of `ansE_flatten`) from `qAns` to `qA2`, reads the column descriptions,
and advances the hub/sum/track bases. -/
lemma p4S1_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (hk : 2 ≤ k) (hE : I.schemas ≠ [])
    (ε : ZMod 2) (e : Fin I.schemas.length) (R : List ℕ) (restx : List Bool) (s0 : NSt CR CQ)
    (hF : L1Fix I w x ε e restx s0) (hB : L1Bnd I w e s0)
    (hMe : ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2).length ≤ 3 * (ordL I).length)
    (eK : s0.env r4K = 0) (eDi : s0.env r4Dist = 0) (eH : s0.env r4H = schBase I e)
    (eSP : s0.env r4SP = sumBase I e) (eTP : s0.env r4TP = trackBase I e)
    (hV : s0.env r4V < 2 ^ w) (hbd : s0.Bdd w)
    (hA : s0.stk qAns = (cL I e).zipIdx.flatMap (a1C I e) ++ R) :
    ∃ s', Good x w p4S1 s0 s' (2100 * ((encodeNats ((cL I e).flatMap cdesc)).length +
        nEnt I e + (cL I e).length + 1) * Ex.nodeCost w) ∧
      EM s0 s' ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2) ∧
      s'.stk qRk = ((cL I e).flatMap fun c => codesL I e c ++ [0]).reverse ++ s0.stk qRk ∧
      s'.stk qAns = R ∧
      s'.stk qA2 = ((cL I e).zipIdx.flatMap (a1C I e)).reverse ++ s0.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qRk → q ≠ qAns → q ≠ qA2 → s'.stk q = s0.stk q) ∧
      s'.env r4K = (cL I e).length ∧ s'.env r4Dist = distR I e (cL I e).length ∧
      s'.env r4H = schBase I e + (cL I e).length * colW I e ∧
      s'.env r4SP = sumBase I e + 2 * (cL I e).length ∧
      s'.env r4TP = trackBase I e + 2 * nEnt I e ∧ s'.env r4V < 2 ^ w ∧ s'.Bdd w ∧
      s'.pos = s0.pos + (encodeNats ((cL I e).flatMap cdesc)).length ∧ s'.out = s0.out ∧
      ∀ reg, reg ∉ c1W → s'.env reg = s0.env reg := by
  obtain ⟨s', g, hEM, hRk, hA', hA2, hso, eK', eD', -, eH', eSP', eTP', hV', hbd', hp', ho', hfr'⟩ :=
    p4S1_loop I hw hk hE ε e R restx s0 hF hB hMe
      (L1Inv_zero I ε e R s0 eK eDi eH eSP eTP hV hbd hA)
  have hz : (cL I e).zipIdx.take (cL I e).length = (cL I e).zipIdx :=
    List.take_of_length_le (by simp)
  have hz' : (cL I e).zipIdx.drop (cL I e).length = [] :=
    List.drop_eq_nil_of_le (by simp)
  have ht : (cL I e).take (cL I e).length = cL I e := List.take_length
  rw [hz] at hEM hA2
  rw [hz'] at hA'
  rw [ht] at hRk hp'
  rw [entB_all_L1d] at eTP'
  refine ⟨s', g.mono (p4S1_costN _ _ _ _ _ (p4S1_cond w)), hEM, hRk, by simpa using hA', hA2, hso,
    eK', eD', eH', eSP', eTP', hV', hbd', hp', ho', hfr'⟩

end Lax119563Proofs.Compiler
