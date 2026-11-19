import Lax119563Proofs.Compiler.PReqLoop
import Lax119563Proofs.Compiler.P3Aux

/-!
# Pass `P3`, first part: the union of location records and requests

`p3Gen` drops the old records (`moveAllS qRec qJunk`), pushes the location records again
(`p1r`, which leaves the cursor at the position of `E`), reads `E`, sets `rKL = k ℓ`,
`rSB = 0`, `rJ = 0`, runs the schema loop `p3Loop` and moves everything onto `qX`, which then
holds `(locRecs I ++ reqs I).flatten` (**`p3Gen_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- **The generation part of `P3`.** -/
def p3Gen : CStm CR CQ :=
  .seq (moveAllS qRec qJunk rT rT2) (.seq p1r (.seq (rdNumS rE rP rT)
    (.seq (mulS rKL rKk rL rGj) (.seq (.set rSB (.const 0)) (.seq (.set rJ (.const 0))
      (.seq p3Loop (moveAllS qRec qX rT rT2)))))))

lemma p3Gen_arith (N U h q ℓ c d lE X : ℕ) (hU : U ≤ N) (hq : q ≤ 6 * (h + 1))
    (hlE : lE ≤ h) (hℓ : ℓ ≤ h) (hX : X * (ℓ + 1) ≤ 4 * h) :
    (q + 1) * (10 * N) + (600 * (h + 1) * N + ((lE + 1) * (20 * N) + ((ℓ + 1) * (12 * N) +
      (1 * N + U + (1 * N + U + (30000 * (h + 1) * N +
        (X * (ℓ + 6) + 1) * (10 * N))))))) ≤ 32000 * (h + 1) * N := by
  have hX6 : X * (ℓ + 6) ≤ 6 * (X * (ℓ + 1)) := by nlinarith
  have e1 : (q + 1) * (10 * N) ≤ (6 * (h + 1) + 1) * (10 * N) := Nat.mul_le_mul_right _ (by omega)
  have e2 : (lE + 1) * (20 * N) ≤ (h + 1) * (20 * N) := Nat.mul_le_mul_right _ (by omega)
  have e3 : (ℓ + 1) * (12 * N) ≤ (h + 1) * (12 * N) := Nat.mul_le_mul_right _ (by omega)
  have e4 : (X * (ℓ + 6) + 1) * (10 * N) ≤ (24 * h + 1) * (10 * N) :=
    Nat.mul_le_mul_right _ (by omega)
  have e5 : (6 * (h + 1) + 1) * (10 * N) + 600 * (h + 1) * N + (h + 1) * (20 * N) +
      (h + 1) * (12 * N) + 1 * N + N + (1 * N + N + (30000 * (h + 1) * N)) +
      (24 * h + 1) * (10 * N) ≤ 32000 * (h + 1) * N := by
    have : (6 * (h + 1) + 1) * (10 * N) + 600 * (h + 1) * N + (h + 1) * (20 * N) +
      (h + 1) * (12 * N) + 1 * N + N + (1 * N + N + (30000 * (h + 1) * N)) +
      (24 * h + 1) * (10 * N) = 31012 * (h * N) + 31024 * N := by ring
    rw [this]
    have : 32000 * (h + 1) * N = 32000 * (h * N) + 32000 * N := by ring
    rw [this]; omega
  omega

set_option maxHeartbeats 4000000 in
/-- **The generation part of `P3`.** From any state with `rW = W`, `rL = ℓ`, `rL1 = ℓ + 1`
and empty generation stacks, `p3Gen` leaves `(locRecs I ++ reqs I).flatten` on `qX`, empties
`qRec` and ends at the end of the input with `rCnt = |locRecs I|`, `rSB = |reqs I|`. -/
theorem p3Gen_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hE : I.schemas ≠ [])
    (hS : 16 * (H I + 1) ≤ 2 ^ w) (st : NSt CR CQ) (hb : st.Bdd w) (hp : st.pos ≤ H I)
    (hW : st.env rW = I.numLocations) (hL : st.env rL = ℓ) (hL1 : st.env rL1 = ℓ + 1)
    (hG : GenEmpty st) (hRecL : (st.stk qRec).length ≤ 6 * (H I + 1)) :
    ∃ st', Good (encodeSystem I) w p3Gen st st' (32000 * (H I + 1) * Ex.nodeCost w) ∧
      st'.stk qX = (locRecs I ++ reqs I).flatten ∧ st'.stk qRec = [] ∧
      st'.stk qLs = [] ∧ st'.stk qLs2 = [] ∧ st'.stk qF2 = [] ∧ st'.stk qDl = [] ∧
      st'.stk qDl2 = [] ∧ st'.stk qDom = [] ∧ st'.stk qDom2 = [] ∧ st'.stk qAux = [] ∧
      OtherStk st st' ∧
      st'.env rW = I.numLocations ∧ st'.env rL = ℓ ∧ st'.env rL1 = ℓ + 1 ∧ st'.env rKk = k ∧
      st'.env rE = I.schemas.length ∧ st'.env rKL = k * ℓ ∧
      st'.env rCnt = (locRecs I).length ∧ st'.env rSB = (reqs I).length ∧
      st'.pos = H I ∧ st'.out = st.out ∧ st'.Bdd w ∧
      ∀ r, wReg r p3Gen = false → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hU0 := Ex.unitCost_le_nodeCost w
  have hkH := k_le_H I hE
  have hℓ := ell_le_H I hk (fun h => hE h.2)
  have hEH := E_le I
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  have hpx : st.pos ≤ (encodeSystem I).length := hp
  -- drop the old records
  obtain ⟨s1, r1, h1S, h1p, h1o, h1e⟩ := moveAllS_good (x := encodeSystem I) hw (q := qRec)
    (q' := qJunk) (t := rT) (f := rT2) (by decide) (by decide) st hb
  -- the location records
  obtain ⟨s2, r2, h2S, h2o, h2p, h2W, h2L1, h2K, h2C, h2e⟩ := p1r_good I hw (by omega) hkH hℓ s1
    (by rw [h1p]; exact hp) (by rw [h1e _ (by decide) (by decide), hW])
    (by rw [h1e _ (by decide) (by decide), hL1])
  -- `E`
  have r3 := rdNumS_good (Q := CQ) hw (r := rE) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s2 I.schemas.length _ (by rw [h2p, drop_posAt_W]) (bits_lt_of_le hEH hH2)
  set s3 := rdNumFinal s2 rE rP rT I.schemas.length
  have e3 : ∀ q, q ≠ rE → q ≠ rP → q ≠ rT → s3.env q = s2.env q :=
    fun q h1 h2 h3 => rdNumFinal_env_ne h1 h2 h3 _
  have e2L : s2.env rL = ℓ := by
    rw [h2e _ (by decide), h1e _ (by decide) (by decide), hL]
  have r4 := mulS_good (x := encodeSystem I) (w := w) (Q := CQ) hw (dst := rKL) (a := rKk)
    (b := rL) (j := rGj) (by decide) (by decide) (by decide) (by decide) (by decide) s3
    (by rw [e3 _ (by decide) (by decide) (by decide), h2K])
    (by rw [e3 _ (by decide) (by decide) (by decide), e2L]) (by nlinarith) (by omega)
  set s4 := (s3.set rKL (k * ℓ)).set rGj ℓ
  have r5 := Good.set (x := encodeSystem I) (w := w) (st := s4) (r := rSB) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s5 := s4.set rSB ((Ex.const 0 : Ex CR).eval s4.env)
  have r6 := Good.set (x := encodeSystem I) (w := w) (st := s5) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s6 := s5.set rJ ((Ex.const 0 : Ex CR).eval s5.env)
  have h36 := r3.seq (r4.seq (r5.seq r6))
  have h46 := r4.seq (r5.seq r6)
  have hpre := r1.seq (r2.seq h36)
  have hb6 := hpre.bdd hw hb hpx
  -- stacks of `s6`
  have h6S : ∀ q, s6.stk q = s2.stk q := fun q => by
    show s3.stk q = _; rfl
  have h2S' : ∀ q, q ≠ qRec → s2.stk q = s1.stk q := fun q hq => by
    rw [h2S, Function.update_of_ne hq]
  have h1S' : ∀ q, q ≠ qRec → q ≠ qJunk → s1.stk q = st.stk q := fun q hq hq' => by
    rw [h1S, Function.update_of_ne hq', Function.update_of_ne hq]
  have hg : ∀ q, q ≠ qRec → q ≠ qJunk → s6.stk q = st.stk q := fun q hq hq' => by
    rw [h6S, h2S' q hq, h1S' q hq hq']
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hG
  have hG6 : GenEmpty s6 := ⟨by rw [hg _ (by decide) (by decide), g1],
    by rw [hg _ (by decide) (by decide), g2], by rw [hg _ (by decide) (by decide), g3],
    by rw [hg _ (by decide) (by decide), g4], by rw [hg _ (by decide) (by decide), g5],
    by rw [hg _ (by decide) (by decide), g6], by rw [hg _ (by decide) (by decide), g7],
    by rw [hg _ (by decide) (by decide), g8], by rw [hg _ (by decide) (by decide), g9]⟩
  have h6Rec : s6.stk qRec = (locRecs I).flatten.reverse := by
    rw [h6S, h2S, Function.update_self, h1S, Function.update_of_ne (by decide),
      Function.update_self, List.append_nil]
  -- the schema loop
  obtain ⟨s7, r7, hG7, h7Rec, hO7, h7SB, h7p, h7o, hb7, h7e⟩ := p3Loop_good I hw hk hE hS s6
    hb6.1 (by simp [s6, Ex.eval])
    (by rw [h46.env_of (by decide)]; exact rdNumFinal_env_r (by decide) (by decide) _)
    (by rw [h36.env_of (by decide), h2K])
    (by simp [s6, s5, s4, Function.update_of_ne (show rKL ≠ rGj by decide)])
    (by rw [h36.env_of (by decide), e2L]) (by rw [h36.env_of (by decide), h2L1])
    (by simp [s6, s5, Ex.eval, Function.update_of_ne (show rSB ≠ rJ by decide)])
    (by show s2.pos + _ = _; rw [h2p]; rfl) hG6
  -- onto `qX`
  obtain ⟨s8, r8, h8S, h8p, h8o, h8e⟩ := moveAllS_good (x := encodeSystem I) hw (q := qRec)
    (q' := qX) (t := rT) (f := rT2) (by decide) (by decide) s7 hb7
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8))))))
  have h8S' : ∀ q, q ≠ qRec → q ≠ qX → s8.stk q = s7.stk q := fun q hq hq' => by
    rw [h8S, Function.update_of_ne hq', Function.update_of_ne hq]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := hG7
  have h7R : s7.stk qRec = ((locRecs I ++ reqs I).flatten).reverse := by
    rw [h7Rec, h6Rec, List.flatten_append, List.reverse_append]
  refine ⟨s8, hall.mono ?_, ?_, ?_, by rw [h8S' _ (by decide) (by decide), k1],
    by rw [h8S' _ (by decide) (by decide), k2], by rw [h8S' _ (by decide) (by decide), k4],
    by rw [h8S' _ (by decide) (by decide), k5], by rw [h8S' _ (by decide) (by decide), k6],
    by rw [h8S' _ (by decide) (by decide), k7], by rw [h8S' _ (by decide) (by decide), k8],
    by rw [h8S' _ (by decide) (by decide), k9], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [h8p, h7p], by rw [h8o, h7o, hall.out_of (by decide)],
    (r8.bdd hw hb7 (by rw [h7p])).1, fun r hr => hall.env_of hr⟩
  · -- cost
    rw [h7R, List.length_reverse, length_flatten_union]
    have hlE : (encodeNat I.schemas.length).length ≤ H I := by
      have h := congrArg List.length (drop_posAt_W I)
      simp only [List.length_drop, List.length_append] at h
      omega
    simp only [condCost, Ex.size, rv]
    exact p3Gen_arith _ _ _ _ _ _ _ _ _ hU0 hRecL hlE hℓ (union_mul_le I)
  · rw [h8S, Function.update_self, h7R, List.reverse_reverse, k3, List.append_nil]
  · rw [h8S, Function.update_of_ne (by decide), Function.update_self]
  · intro q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11
    have hqX : q ≠ qX := n3
    rw [h8S' q n10 hqX, hO7 q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11, hg q n10 n11]
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide), h46.env_of (by decide),
      e3 _ (by decide) (by decide) (by decide), h2W]
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide), h46.env_of (by decide),
      e3 _ (by decide) (by decide) (by decide), e2L]
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide), h46.env_of (by decide),
      e3 _ (by decide) (by decide) (by decide), h2L1]
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide), h46.env_of (by decide),
      e3 _ (by decide) (by decide) (by decide), h2K]
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide), h46.env_of (by decide)]
    exact rdNumFinal_env_r (by decide) (by decide) _
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide)]
    simp [s6, s5, s4, Function.update_of_ne (show rKL ≠ rGj by decide)]
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide), h46.env_of (by decide),
      e3 _ (by decide) (by decide) (by decide), h2C]
  · rw [h8e _ (by decide) (by decide), h7SB]

end Lax119563Proofs.Compiler
