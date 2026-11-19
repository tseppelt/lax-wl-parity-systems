import Lax119563Proofs.Compiler.P4SchB5
import Lax119563Proofs.Compiler.P4SchK

/-!
# Pass `P4`, schema part: the program `p4Sch` and its specification

`p4Sch = p4SchPre; p4SLp; moveAllS qA2 qAns`: the prefix rewinds the input, skips `k, ℓ, W`,
the location section and `E`, computes `r4PL = k (ℓ + 1)`, sets `rJ, r4SB := 0` and moves the
records forward onto `qS2`; the loop runs the schema body for `rJ < rE`; the suffix restores
`qAns` (**`p4Sch_spec`**: `SchSpec I (wordOf H S) p4Sch (400000 (H + S + 1) · nodeCost w)`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The prefix of the schema part. -/
def p4SchPre : CStm CR CQ :=
  .seq .rst (.seq (skipNumS rT) (.seq (skipNumS rT) (.seq (skipNumS rT)
    (.seq (.set rJ (.const 0)) (.seq p4KLoop (.seq (skipNumS rT)
      (.seq (mulS r4PL rKk rL1 rc1) (.seq (.set rJ (.const 0)) (.seq (.set r4SB (.const 0))
        (moveAllS qSch qS2 rT rP))))))))))

/-- The schema loop. -/
def p4SLp : CStm CR CQ := .loop (.lt (rv rJ) (rv rE)) p4Body

/-- **The schema edge part of `P4`.** -/
def p4Sch : CStm CR CQ := .seq p4SchPre (.seq p4SLp (moveAllS qA2 qAns rT rP))

/-- Registers written by the prefix. -/
def preW : List (Fin CR) := [rT, rP, r4D, rc2, rc3, rJ, rc1, r4PL, r4SB]

/-! ## The prefix -/

lemma schPre_arith {N U p h a b c d m z : ℕ} (hU : U ≤ N) (hp : p ≤ h) (habcd : a + b + c + d ≤ h)
    (hm : m ≤ h) (hz : z ≤ 4 * h) :
    U * (p + 1) + ((a + 1) * (4 * N) + ((b + 1) * (4 * N) + ((c + 1) * (4 * N) + (N + U +
      (400 * (h + 1) * N + ((d + 1) * (4 * N) + ((m + 1) * (12 * N) + (N + U + (N + U +
        (z + 1) * (10 * N)))))))))) ≤ 1000 * (h + 1) * N := by
  have h1 : (a + b + c + d) * N ≤ h * N := Nat.mul_le_mul_right _ habcd
  have h2 : m * N ≤ h * N := Nat.mul_le_mul_right _ hm
  have h3 : z * N ≤ 4 * h * N := Nat.mul_le_mul_right _ hz
  have h4 : U * (p + 1) ≤ N * (h + 1) := Nat.mul_le_mul hU (by omega)
  nlinarith

set_option maxHeartbeats 4000000 in
lemma p4SchPre_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hk : 1 ≤ k)
    (hE : I.schemas ≠ [])
    (st : NSt CR CQ) (hb : st.Bdd w) (hp : st.pos ≤ H I) (hW : st.env rW = I.numLocations)
    (hL1 : st.env rL1 = ℓ + 1) (hK : st.env rKk = k) (hz : (st.stk qSch).length ≤ 4 * H I) :
    ∃ s0, Good (encodeSystem I) w p4SchPre st s0 (1000 * (H I + 1) * Ex.nodeCost w) ∧
      s0.pos = schPos I ∧ s0.out = st.out ∧
      s0.stk = Function.update (Function.update st.stk qSch []) qS2
        ((st.stk qSch).reverse ++ st.stk qS2) ∧
      s0.env rJ = 0 ∧ s0.env r4SB = 0 ∧ s0.env r4PL = k * (ℓ + 1) ∧
      ∀ r, r ∉ preW → s0.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hkl := kl_le_H I hE
  have hl1 : 1 * (ℓ + 1) ≤ k * (ℓ + 1) := Nat.mul_le_mul_right _ hk
  have hℓ : ℓ ≤ H I := by omega
  have r0 := Good.rst (x := encodeSystem I) (w := w) (st := st)
  set s0 : NSt CR CQ := { st with pos := 0 }
  have r1 := skipNumS_good (Q := CQ) hw (t := rT) s0 k _ (drop_zero_k I)
  set s1 := skipNumFinal s0 rT k
  have r2 := skipNumS_good (Q := CQ) hw (t := rT) s1 ℓ _
    (by show (encodeSystem I).drop (0 + _) = _; rw [zero_add]; exact drop_ell I)
  set s2 := skipNumFinal s1 rT ℓ
  have r3 := skipNumS_good (Q := CQ) hw (t := rT) s2 I.numLocations _
    (by show (encodeSystem I).drop (0 + (encodeNat k).length + (encodeNat ℓ).length) = _
        rw [zero_add]; exact drop_W I)
  set s3 := skipNumFinal s2 rT I.numLocations
  have e3 : ∀ r, r ≠ rT → s3.env r = st.env r := fun r h => by
    rw [skipNumFinal_env_ne h, skipNumFinal_env_ne h, skipNumFinal_env_ne h]
  have r4 := Good.set (x := encodeSystem I) (w := w) (st := s3) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s4 := s3.set rJ ((Ex.const 0 : Ex CR).eval s3.env)
  have e4 : ∀ r, r ≠ rT → r ≠ rJ → s4.env r = st.env r := fun r h1 h2 => by
    simp only [s4, NSt.set_env, Function.update_of_ne h2]; exact e3 r h1
  have h4p : s4.pos = posAt I 0 := by
    show 0 + (encodeNat k).length + (encodeNat ℓ).length + (encodeNat I.numLocations).length = _
    rw [posAt_zero]; ring
  have hI4 : p4KInv I s4 s4 := by
    refine ⟨by rw [e4 _ (by decide) (by decide), hW], by rw [e4 _ (by decide) (by decide), hL1],
      by simp [s4, Ex.eval], by rw [show s4.env rJ = 0 by simp [s4, Ex.eval]]; exact h4p,
      rfl, rfl, fun _ _ => rfl⟩
  obtain ⟨s5, r5, h5p, h5s, h5o, h5f⟩ := p4KLoop_good I hw hH hℓ s4 hI4
    (by simp [s4, Ex.eval])
  have r6 := skipNumS_good (Q := CQ) hw (t := rT) s5 I.schemas.length _
    (by rw [h5p]; exact drop_posAt_W I)
  set s6 := skipNumFinal s5 rT I.schemas.length
  have e6 : ∀ r, r ∉ preW → s6.env r = st.env r := fun r hr => by
    simp only [preW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [skipNumFinal_env_ne hr.1, h5f r (by simp [kW, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1]), e4 r hr.1 hr.2.2.2.2.2.1]
  have r7 := mulS_good (x := encodeSystem I) (w := w) hw (dst := r4PL) (a := rKk) (b := rL1)
    (j := rc1) (by decide) (by decide) (by decide) (by decide) (by decide) s6
    (by rw [e6 _ (by decide), hK]) (by rw [e6 _ (by decide), hL1]) (by omega) (by omega)
  set s7 := (s6.set r4PL (k * (ℓ + 1))).set rc1 (ℓ + 1)
  have r8 := Good.set (x := encodeSystem I) (w := w) (st := s7) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s8 := s7.set rJ ((Ex.const 0 : Ex CR).eval s7.env)
  have r9 := Good.set (x := encodeSystem I) (w := w) (st := s8) (r := r4SB) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s9 := s8.set r4SB ((Ex.const 0 : Ex CR).eval s8.env)
  have r19 := r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9))))))))
  have hb9 := r19.bdd hw hb (hp.trans le_rfl)
  obtain ⟨s10, r10, h10s, h10p, h10o, h10f⟩ := moveAllS_good (x := encodeSystem I) hw
    (q := qSch) (q' := qS2) (t := rT) (f := rP) (by decide) (by decide) s9 hb9.1
  have h9s : s9.stk = st.stk := by
    show s5.stk = _; rw [h5s]; rfl
  have hlen3 : (encodeNat k).length + (encodeNat ℓ).length + (encodeNat I.numLocations).length +
      (encodeNat I.schemas.length).length ≤ H I := by
    have h1 := schAt_le I 0
    rw [schAt_zero, schPos] at h1
    have h3 : posAt I 0 ≤ posAt I I.numLocations := by
      have : ∀ j ≤ I.numLocations, posAt I 0 ≤ posAt I j := by
        intro j
        induction j with
        | zero => intro _; exact le_rfl
        | succ j ih => intro hj; rw [posAt_succ I (by omega)]; have := ih (by omega); omega
      exact this _ le_rfl
    rw [posAt_zero] at h3
    omega
  refine ⟨s10, (r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq
    (r9.seq r10)))))))))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h9s]
    simp only [Ex.size, one_mul]
    have := schPre_arith (N := Ex.nodeCost w) (U := unitCost w) (p := st.pos) (h := H I)
      (a := (encodeNat k).length) (b := (encodeNat ℓ).length)
      (c := (encodeNat I.numLocations).length) (d := (encodeNat I.schemas.length).length)
      (m := ℓ + 1) (z := (st.stk qSch).length) hU hp hlen3 (by omega) hz
    linarith only [this]
  · rw [h10p]; show s5.pos + _ = _; rw [h5p]; rfl
  · rw [h10o]; show s5.out = _; rw [h5o]; rfl
  · rw [h10s, h9s]
  · rw [h10f _ (by decide) (by decide)]
    simp [s9, s8, Ex.eval, Function.update_of_ne (show rJ ≠ r4SB by decide)]
  · rw [h10f _ (by decide) (by decide)]; simp [s9, Ex.eval]
  · rw [h10f _ (by decide) (by decide)]
    simp [s9, s8, s7, Function.update_of_ne (show r4PL ≠ r4SB by decide),
      Function.update_of_ne (show r4PL ≠ rJ by decide),
      Function.update_of_ne (show r4PL ≠ rc1 by decide)]
  · intro r hr
    have h1 : r ≠ rT := fun h => hr (by simp [h, preW])
    have h2 : r ≠ rP := fun h => hr (by simp [h, preW])
    rw [h10f r h1 h2]
    simp only [s9, s8, s7, NSt.set_env]
    rw [Function.update_of_ne (fun h => hr (by simp [h, preW])),
      Function.update_of_ne (fun h => hr (by simp [h, preW])),
      Function.update_of_ne (fun h => hr (by simp [h, preW])),
      Function.update_of_ne (fun h => hr (by simp [h, preW])), e6 r hr]

end Lax119563Proofs.Compiler
