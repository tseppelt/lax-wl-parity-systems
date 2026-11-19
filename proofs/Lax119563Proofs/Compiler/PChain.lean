import Lax119563Proofs.Compiler.P3
import Lax119563Proofs.Compiler.PChainSize

/-!
# The chain of passes `P0`–`P3`

`pre = p0; if rTriv then skip else (p1; if rE then (p1r; p2; p3) else skip)`.

* trivial system (`trivSys I`): `rTriv = 1`, all stacks empty, nothing emitted;
* nontrivial, `E = 0`: `p1` only (`p1r` needs `k ≤ H`, `p2`/`p3` need a schema);
* nontrivial, `E > 0`: all passes.

**`pre_good`**: from `NSt.zero`, under `16 (H + locBase + 1) ≤ 2^w`, with cost
`210000 (H + 1)(log₂(H + 1) + 1) · nodeCost w`; the end state is described by `ChainLoc`
(nontrivial), `ChainNoSch` (`E = 0`) and `ChainSch` (`E > 0`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

/-- The passes `P1'`, `P2`, `P3` (nontrivial systems with a schema). -/
def preSch : CStm CR CQ := .seq p1r (.seq p2 p3)

/-- The passes for a nontrivial system. -/
def preNT : CStm CR CQ := .seq p1 (.ite (rv rE) preSch .skip)

/-- **The passes `P0`–`P3`.** -/
def pre : CStm CR CQ := .seq p0 (.ite (rv rTriv) .skip preNT)

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- End state, nontrivial system. -/
def ChainLoc (st : NSt CR CQ) : Prop :=
  st.env rTriv = 0 ∧ st.env rW = I.numLocations ∧ st.env rL = ℓ ∧
    st.env rE = I.schemas.length ∧ st.stk qLoc = (locOffs I).reverse

/-- End state, nontrivial system without schemas. -/
def ChainNoSch (st : NSt CR CQ) : Prop :=
  st.env rOff = locOff I I.numLocations ∧ st.pos = schPos I ∧ ∀ q, q ≠ qLoc → st.stk q = []

/-- End state, system with a schema. -/
def ChainSch (st : NSt CR CQ) : Prop :=
  st.stk qAns = (ansAll I).flatten ∧ st.stk qSch = (schRecsUpTo I I.schemas.length).reverse ∧
    (∀ q, q ≠ qLoc → q ≠ qSch → q ≠ qAns → q ≠ qJunk → st.stk q = []) ∧
    st.env rLB = locBase I ∧ st.env rL1 = ℓ + 1 ∧ st.env rKk = k ∧ st.env rKL = k * ℓ ∧
    st.env rCnt = (locRecs I).length ∧ st.env rSB = (reqs I).length ∧ st.pos = H I

lemma pre_arith {N h lg c c' u : ℕ} (hc : c ≤ 2 * N) (hc' : c' ≤ 2 * N) (hu : u ≤ N) :
    200 * (h + 1) * N + (c + (500 * (h + 1) * N + (c' + (600 * (h + 1) * N +
      (2000 * (h + 1) * N + 200000 * (h + 1) * (lg + 1) * N))))) ≤
      210000 * (h + 1) * (lg + 1) * N ∧
    200 * (h + 1) * N + (c + (500 * (h + 1) * N + (c' + u))) ≤
      210000 * (h + 1) * (lg + 1) * N ∧
    200 * (h + 1) * N + (c + u) ≤ 210000 * (h + 1) * (lg + 1) * N := by
  have h1 : (h + 1) * N ≤ (h + 1) * (lg + 1) * N := by
    have := Nat.le_mul_of_pos_right (h + 1) (Nat.succ_pos lg)
    exact Nat.mul_le_mul_right _ this
  have h2 : N ≤ (h + 1) * N := Nat.le_mul_of_pos_left N (Nat.succ_pos h)
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

lemma condCost_rv (w : ℕ) (r : Fin CR) : condCost w (rv r) ≤ 2 * Ex.nodeCost w := by
  have := CStm.nodeCost_ge w
  have := CStm.unitCost_ge w
  simp only [condCost, Ex.size]; omega

lemma zero_bdd (w : ℕ) : (NSt.zero CR CQ).Bdd w :=
  ⟨fun _ => Nat.pos_of_ne_zero (by positivity), fun _ v hv => by simp [NSt.zero] at hv⟩

lemma exec_set_succ {b : CStm CR CQ} {r r' : Fin CR} (hne : r ≠ r') (hb : wReg r b = false)
    (hb' : wReg r' b = false) (x : List Bool) (st : NSt CR CQ) :
    (exec x (.seq (.set r (.add (rv r') (.const 1))) b) st).env r =
      (exec x (.seq (.set r (.add (rv r') (.const 1))) b) st).env r' + 1 := by
  simp only [CStm.exec]
  rw [exec_env_of b _ hb, exec_env_of b _ hb']
  simp [NSt.set, Function.update_of_ne hne.symm, Ex.eval]

/-- `p1` leaves `rL1 = rL + 1`. -/
lemma p1_rL1 (x : List Bool) (st : NSt CR CQ) :
    (exec x p1 st).env rL1 = (exec x p1 st).env rL + 1 := by
  have e : exec x p1 st = exec x (.seq (.set rL1 (.add (rv rL) (.const 1)))
      (.seq (rdNumS rW rP rT) (.seq (.set rJ (.const 0)) (.seq (.set rOff (.const 0))
        (.seq p1Loop (rdNumS rE rP rT))))))
      (exec x (rdNumS rL rP rT) (exec x (skipNumS rT) (exec x .rst st))) := by
    simp only [p1, CStm.exec]
  rw [e]
  exact exec_set_succ (by decide) (by decide) (by decide) _ _

set_option maxHeartbeats 4000000 in
/-- **The passes `P0`–`P3`** from the zero state. -/
theorem pre_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hS : 16 * (H I + locBase I + 1) ≤ 2 ^ w) :
    ∃ st', Good (encodeSystem I) w pre (NSt.zero CR CQ) st'
        (210000 * (H I + 1) * (Nat.log 2 (H I + 1) + 1) * Ex.nodeCost w) ∧
      st'.out = [] ∧ st'.Bdd w ∧ st'.pos ≤ H I ∧
      (trivSys I → st'.env rTriv = 1 ∧ ∀ q, st'.stk q = []) ∧
      (¬ trivSys I → ChainLoc I st' ∧ (I.schemas = [] → ChainNoSch I st') ∧
        (I.schemas ≠ [] → ChainSch I st')) := by
  have hU := CStm.nodeCost_ge w
  have hc := condCost_rv w
  have h4 : 4 ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) hw)
  obtain ⟨s0, r0, h0s, h0o, h0t, h0t1⟩ := p0_good I hw (by omega) (NSt.zero CR CQ) rfl
  have hz0 : ∀ q, s0.stk q = [] := fun q => by rw [h0s]; rfl
  have hb0 := r0.bdd hw (zero_bdd w) (Nat.zero_le _)
  have hf0 : (rv rTriv).Fits w s0.env := by
    show s0.env rTriv < 2 ^ w; omega
  by_cases ht : trivSys I
  · have e1 : s0.env rTriv = 1 := h0t.mpr ht
    have r := r0.seq (Good.iteT (q := preNT) hf0 (by show s0.env rTriv ≠ 0; omega) Good.skip)
    exact ⟨s0, r.mono (pre_arith (hc rTriv) (hc rE) hU).2.2, h0o, hb0.1, hb0.2,
      fun _ => ⟨e1, hz0⟩, fun h => absurd ht h⟩
  have e1 : s0.env rTriv = 0 := by
    have := mt h0t.mp ht; omega
  have hℓ := ell_le_H I hk ht
  obtain ⟨s1, r1, h1s, h1o, h1p, h1W, h1L, h1E, h1Off⟩ := p1_good I hw (by omega) hℓ s0 hb0.2
  have hb1 := r1.bdd hw hb0.1 hb0.2
  have e1' : s1.env rTriv = 0 := by rw [r1.env_of (by decide), e1]
  have hf1 : (rv rE).Fits w s1.env := by
    show s1.env rE < 2 ^ w; have := E_le I; omega
  have hLoc1 : s1.stk qLoc = (locOffs I).reverse := by
    rw [h1s, Function.update_self, hz0, List.append_nil]
  have hT0 : (rv rTriv).eval s0.env = 0 := e1
  by_cases hE : I.schemas = []
  · have hE0 : (rv rE).eval s1.env = 0 := by show s1.env rE = 0; rw [h1E, hE]; rfl
    have r := r0.seq (Good.iteF (p := .skip) hf0 hT0
      (r1.seq (Good.iteF (p := preSch) hf1 hE0 Good.skip)))
    refine ⟨s1, r.mono (pre_arith (hc rTriv) (hc rE) hU).2.1, by rw [h1o, h0o]; rfl, hb1.1,
      hb1.2, fun h => absurd h ht, fun _ =>
        ⟨⟨e1', h1W, h1L, h1E, hLoc1⟩, fun _ => ⟨h1Off, h1p, fun q hq => ?_⟩,
          fun h => absurd hE h⟩⟩
    rw [h1s, Function.update_of_ne hq, hz0]
  have hEpos : (rv rE).eval s1.env ≠ 0 := by
    show s1.env rE ≠ 0; rw [h1E]; exact fun h => hE (List.length_eq_zero_iff.mp h)
  have hkH := k_le_H I hE
  have hL1 : s1.env rL1 = ℓ + 1 := by rw [← r1.2.1, p1_rL1, r1.2.1, h1L]
  obtain ⟨s2, r2, h2s, h2o, h2p, h2W, h2L1, h2K, h2C, h2e⟩ :=
    p1r_good I hw (by omega) hkH hℓ s1 hb1.2 h1W hL1
  have hb2 := r2.bdd hw hb1.1 hb1.2
  have h2L : s2.env rL = ℓ := by rw [h2e _ (by decide), h1L]
  have hz2 : ∀ q, q ≠ qLoc → q ≠ qRec → s2.stk q = [] := fun q a b => by
    rw [h2s, Function.update_of_ne b, h1s, Function.update_of_ne a, hz0]
  obtain ⟨s3, r3, h3LB, h3s, h3o, h3p, h3e⟩ := p2_good I hw hk hE hS s2 h2p h2K h2L h2L1
    (hz2 _ (by decide) (by decide)) (hz2 _ (by decide) (by decide))
  have hb3 := r3.bdd hw hb2.1 hb2.2
  have hz3 : ∀ q, q ≠ qLoc → q ≠ qRec → q ≠ qSch → s3.stk q = [] := fun q a b c => by
    rw [h3s, Function.update_of_ne c, hz2 q a b]
  have hRec3 : s3.stk qRec = (locRecs I).flatten.reverse := by
    rw [h3s, Function.update_of_ne (by decide), h2s, Function.update_self, h1s,
      Function.update_of_ne (by decide), hz0, List.append_nil]
  have hG : GenEmpty s3 := ⟨hz3 _ (by decide) (by decide) (by decide),
    hz3 _ (by decide) (by decide) (by decide), hz3 _ (by decide) (by decide) (by decide),
    hz3 _ (by decide) (by decide) (by decide), hz3 _ (by decide) (by decide) (by decide),
    hz3 _ (by decide) (by decide) (by decide), hz3 _ (by decide) (by decide) (by decide),
    hz3 _ (by decide) (by decide) (by decide), hz3 _ (by decide) (by decide) (by decide)⟩
  have hRecL : (s3.stk qRec).length ≤ 6 * (H I + 1) := by
    rw [hRec3, List.length_reverse, List.length_flatten]
    have : (locRecs I).map List.length = (locRecs I).map fun _ => ℓ + 6 :=
      List.map_congr_left fun m hm => length_of_mem_union I (List.mem_append_left _ hm)
    rw [this, sum_map_const]
    have := length_locRecs_mul_le I
    nlinarith
  obtain ⟨s4, r4, gA, gX, gR, gLs, gLs2, gF2, gDl, gDl2, gDom, gDom2, gAux, hO, e4W, e4L, e4L1,
    e4K, e4E, e4KL, e4C, e4SB, h4p, h4o, h4e⟩ := p3_good I hw hk hE (by omega) s3 hb3.1
    hb3.2 (by rw [h3e _ (by decide), h2W])
    (by rw [h3e _ (by decide), h2L]) (by rw [h3e _ (by decide), h2L1]) hG
    (hz3 _ (by decide) (by decide) (by decide)) hRecL
  have r := r0.seq (Good.iteF (p := .skip) hf0 hT0
    (r1.seq (Good.iteT (q := .skip) hf1 hEpos (r2.seq (r3.seq r4)))))
  have hb4 := r4.bdd hw hb3.1 hb3.2
  have h4Loc : s4.stk qLoc = (locOffs I).reverse := by
    rw [hO _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h3s,
      Function.update_of_ne (by decide), h2s, Function.update_of_ne (by decide), hLoc1]
  refine ⟨s4, r.mono (pre_arith (hc rTriv) (hc rE) hU).1, by rw [h4o, h3o, h2o, h1o, h0o]; rfl,
    hb4.1, hb4.2, fun h => absurd h ht, fun _ =>
      ⟨⟨?_, e4W, e4L, e4E, h4Loc⟩, fun h => absurd h hE, fun _ =>
        ⟨gA, ?_, ?_, by rw [h4e _ (by decide), h3LB], e4L1, e4K, e4KL, e4C, e4SB, h4p⟩⟩⟩
  · rw [h4e _ (by decide), h3e _ (by decide), h2e _ (by decide), e1']
  · rw [hO _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h3s,
      Function.update_self, hz2 _ (by decide) (by decide), List.append_nil]
  · intro q a b c d
    by_cases x1 : q = qX
    · rw [x1]; exact gX
    by_cases x2 : q = qRec
    · rw [x2]; exact gR
    by_cases x3 : q = qLs
    · rw [x3]; exact gLs
    by_cases x4 : q = qLs2
    · rw [x4]; exact gLs2
    by_cases x5 : q = qF2
    · rw [x5]; exact gF2
    by_cases x6 : q = qDl
    · rw [x6]; exact gDl
    by_cases x7 : q = qDl2
    · rw [x7]; exact gDl2
    by_cases x8 : q = qDom
    · rw [x8]; exact gDom
    by_cases x9 : q = qDom2
    · rw [x9]; exact gDom2
    by_cases x10 : q = qAux
    · rw [x10]; exact gAux
    rw [hO q x3 x4 x1 x5 x6 x7 x8 x9 x10 x2 d c]
    exact hz3 q a x2 b

end Lax119563Proofs.Compiler
