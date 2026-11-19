import Lax119563Proofs.Compiler.P4LocPass
import Lax119563Proofs.Compiler.P4SzS
import Lax119563Proofs.Compiler.PChain

/-!
# Pass `P4` (program): one round, with the schema edge part as a parameter

`p4Round SCH = p4Loc; (if E ≠ 0 then p4SzS; SCH); p4Emit`, where `SCH` is the schema edge
part, specified by `SchSpec` (from `SchPre`: push `gEdges I ε` via `EdgeEff`, keep `p4Keep`).
**`p4Round_good`**: from a round-start state (`P4Inv`), the output is extended by `gDesc I ε`
and `P4Inv` holds again (all stacks restored).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- One round of `P4`. -/
def p4Round (SCH : CStm CR CQ) : CStm CR CQ :=
  .seq p4Loc (.seq (.ite (rv rE) (.seq p4SzS SCH) .skip) p4Emit)

/-- The round-start states. -/
def P4Inv (w : ℕ) (st : NSt CR CQ) : Prop :=
  st.Bdd w ∧ st.pos ≤ H I ∧ st.env rTriv = 0 ∧ st.env rW = I.numLocations ∧ st.env rL = ℓ ∧
    st.env rE = I.schemas.length ∧
    (I.schemas ≠ [] → st.env rKk = k ∧ st.env rKL = k * ℓ ∧ st.env rLB = locBase I) ∧
    st.stk qAns = (ansAll I).flatten ∧ st.stk qSch = (schRecsUpTo I I.schemas.length).reverse ∧
    ∀ q, q ≠ qLoc → q ≠ qSch → q ≠ qAns → q ≠ qJunk → st.stk q = []

/-- The start states of the schema edge part. -/
def SchPre (ε w : ℕ) (st : NSt CR CQ) : Prop :=
  I.schemas ≠ [] ∧ st.Bdd w ∧ st.pos = H I ∧ st.env r4Eps = ε ∧ st.env r4M = 0 ∧
    st.env rTriv = 0 ∧ st.env rW = I.numLocations ∧ st.env rL = ℓ ∧ st.env rL1 = ℓ + 1 ∧
    st.env rE = I.schemas.length ∧ st.env rKk = k ∧ st.env rKL = k * ℓ ∧
    st.env rLB = locBase I ∧
    st.stk qAns = (ansAll I).flatten ∧ st.stk qSch = (schRecsUpTo I I.schemas.length).reverse ∧
    ∀ q, q ≠ qLoc → q ≠ qSch → q ≠ qAns → q ≠ qJunk → q ≠ qSzB → st.stk q = []

/-- The registers the schema edge part must keep. -/
def p4Keep : List (Fin CR) := [rTriv, rW, rL, rE, rKk, rKL, rLB, rNt]

/-- **The interface of the schema edge part** (cost `C`). -/
def SchSpec (w : ℕ) (SCH : CStm CR CQ) (C : ℕ) : Prop :=
  ∀ ε ≤ 1, ∀ st, SchPre I ε w st → ∃ st', Good (encodeSystem I) w SCH st st' C ∧
    EdgeEff st st' (gEdges I ε) ∧ ∀ r ∈ p4Keep, st'.env r = st.env r

lemma schAll_nil (h : I.schemas = []) : schAll I = [] := by
  have : List.finRange I.schemas.length = [] := List.eq_nil_of_length_eq_zero (by simp (config := { decide := true }) [h])
  rw [schAll, this]; rfl

lemma gEdges_nil (h : I.schemas = []) (ε : ℕ) : gEdges I ε = [] := by
  have : List.finRange I.schemas.length = [] := List.eq_nil_of_length_eq_zero (by simp (config := { decide := true }) [h])
  rw [gEdges, this]; rfl

lemma clsSizes_eq' : clsSizes I = schAll I ++ locAll I := clsSizes_eq I

lemma gDesc_eq_descOf (ε : ℕ) : gDesc I ε = descOf (clsSizes I) (gEdges I ε) := rfl

/-- The size measure of a round. -/
noncomputable def p4Z (ε : ℕ) : ℕ :=
  (schRecsUpTo I I.schemas.length).length + (clsSizes I).length + (clsSizes I).sum +
    (gEdges I ε).length

lemma p4Round_arith {N h Z a b L S M C : ℕ} (hN : 1 ≤ N) (h1 : a + b + L + M ≤ Z)
    (h2 : S ≤ Z) :
    800 * (h + 1) * N + (2 * N + (2000 * (h + a + b + 1) * N + C) +
      (L + S + 2 * M + 8) * (40 * N)) ≤ 4000 * (h + Z + 1) * N + C := by
  have := Nat.mul_le_mul_right N h1
  have := Nat.mul_le_mul_right N h2
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **One round of `P4`.** -/
theorem p4Round_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (hk : 1 ≤ k) (hT : (clsSizes I).sum + 8 < 2 ^ w) {SCH : CStm CR CQ} {C : ℕ}
    (hSpec : SchSpec I w SCH C) {ε : ℕ} (hε1 : ε ≤ 1) (st : NSt CR CQ) (hI : P4Inv I w st)
    (hε : st.env r4Eps = ε) :
    ∃ st', Good (encodeSystem I) w (p4Round SCH) st st'
        (4000 * (H I + p4Z I ε + 1) * Ex.nodeCost w + C) ∧
      st'.out = st.out ++ gDesc I ε ∧ P4Inv I w st' := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hN1 : 1 ≤ Ex.nodeCost w := by omega
  obtain ⟨hb, hp, hTr, hW, hL, hE, hS, hAns, hSch, hemp⟩ := hI
  obtain ⟨s1, r1, h1s, h1p, h1o, h1N, h1M, h1L1⟩ :=
    p4Loc_good I hw hH hℓ st hb hp hW hL (hemp _ (by decide) (by decide) (by decide) (by decide))
  have hb1 := r1.bdd hw hb hp
  have hB0 : st.stk qSzB = [] := hemp _ (by decide) (by decide) (by decide) (by decide)
  have hE0 : st.stk q4E = [] := hemp _ (by decide) (by decide) (by decide) (by decide)
  have hA0 : st.stk qSzA = [] := hemp _ (by decide) (by decide) (by decide) (by decide)
  have hsumC : (clsSizes I).sum = locOff I I.numLocations + (schAll I).sum := by
    rw [clsSizes_eq', List.sum_append, locAll_sum]; ring
  have hlocS := locAll_sum I
  -- the frame shared by both cases: the final stacks are those of `st`
  suffices hmain : ∃ s3, Good (encodeSystem I) w (.ite (rv rE) (.seq p4SzS SCH) .skip) s1 s3
      (2 * Ex.nodeCost w + (2000 * (H I + (schRecsUpTo I I.schemas.length).length +
        (schAll I).sum + 1) * Ex.nodeCost w + C)) ∧
      s3.stk = Function.update (Function.update st.stk qSzB (clsSizes I)) q4E
        (pairsRev (gEdges I ε)) ∧
      s3.env rNt = (clsSizes I).sum ∧ s3.env r4M = (gEdges I ε).length ∧ s3.out = st.out ∧
      (∀ r ∈ p4Keep, r ≠ rNt → s3.env r = st.env r) by
    obtain ⟨s3, r3, h3s, h3N, h3M, h3o, h3k⟩ := hmain
    have hb3 := (r1.seq r3).bdd hw hb hp
    obtain ⟨s4, r4, h4o, h4s, h4p, h4e⟩ := p4Emit_good (x := encodeSystem I) hw s3 (clsSizes I)
      (gEdges I ε) hb3.1 hb3.2 (by rw [h3s]; simp (config := { decide := true }) [Function.update_of_ne (show qSzB ≠ q4E by decide)])
      (by rw [h3s]; simp) (by rw [h3s]; simp (config := { decide := true }) [Function.update_of_ne (show qSzA ≠ q4E by decide),
        Function.update_of_ne (show qSzA ≠ qSzB by decide), hA0]) h3N h3M
    have r := r1.seq (r3.seq r4)
    have hb4 := r.bdd hw hb hp
    have hs4 : s4.stk = st.stk := by
      rw [h4s, h3s]
      funext q
      by_cases h0 : q = q4E
      · subst h0; simp (config := { decide := true }) [hE0]
      by_cases h1 : q = qSzB
      · subst h1; simp (config := { decide := true }) [hB0]
      simp (config := { decide := true }) [Function.update_of_ne h0, Function.update_of_ne h1]
    have hk4 : ∀ r ∈ p4Keep, r ≠ rNt → s4.env r = st.env r := by
      intro r hr hn
      have hr' : r ≠ rT ∧ r ≠ rP ∧ r ≠ rJ ∧ r ≠ rA := by
        simp only [p4Keep, List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [h4e r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2, h3k r hr hn]
    refine ⟨s4, r.mono ?_, by rw [h4o, h3o, gDesc_eq_descOf], ?_⟩
    · unfold p4Z
      have := p4Round_arith (N := Ex.nodeCost w) (h := H I) (Z := p4Z I ε)
        (a := (schRecsUpTo I I.schemas.length).length) (b := (schAll I).sum)
        (L := (clsSizes I).length) (S := (clsSizes I).sum) (M := (gEdges I ε).length)
        (C := C) hN1 (by unfold p4Z; omega) (by unfold p4Z; omega)
      unfold p4Z at this
      omega
    · refine ⟨hb4.1, hb4.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hk4 rTriv (by simp (config := { decide := true }) [p4Keep]) (by decide), hTr]
      · rw [hk4 rW (by simp (config := { decide := true }) [p4Keep]) (by decide), hW]
      · rw [hk4 rL (by simp (config := { decide := true }) [p4Keep]) (by decide), hL]
      · rw [hk4 rE (by simp (config := { decide := true }) [p4Keep]) (by decide), hE]
      · intro hne
        obtain ⟨a, b, c⟩ := hS hne
        exact ⟨by rw [hk4 rKk (by simp (config := { decide := true }) [p4Keep]) (by decide), a], by rw [hk4 rKL (by simp (config := { decide := true }) [p4Keep]) (by decide), b],
          by rw [hk4 rLB (by simp (config := { decide := true }) [p4Keep]) (by decide), c]⟩
      · rw [hs4, hAns]
      · rw [hs4, hSch]
      · intro q a b c d; rw [hs4]; exact hemp q a b c d
  -- the two cases
  have hs1 : s1.stk = Function.update st.stk qSzB (locAll I) := by rw [h1s, hB0, List.append_nil]
  have hfE : (rv rE : Ex CR).Fits w s1.env := hb1.1.1 rE
  have e1 : ∀ r ∈ p4Keep, r ≠ rNt → s1.env r = st.env r := by
    intro r hr hn
    simp only [p4Keep, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hn | exact r1.env_of (by decide)
  by_cases hE' : I.schemas = []
  · have hc : (rv rE : Ex CR).eval s1.env = 0 := by
      show s1.env rE = 0; rw [r1.env_of (by decide), hE, hE']; rfl
    refine ⟨s1, (CStm.Good.iteF hfE hc CStm.Good.skip).mono ?_, ?_, ?_, ?_, h1o, ?_⟩
    · have : Ex.nodeCost w ≤ 2000 * (H I + (schRecsUpTo I I.schemas.length).length +
          (schAll I).sum + 1) * Ex.nodeCost w := Nat.le_mul_of_pos_left _ (by positivity)
      simp only [condCost, rv, Ex.size]; omega
    · rw [hs1, gEdges_nil I hE', clsSizes_eq', schAll_nil I hE']
      funext q
      by_cases h0 : q = q4E
      · subst h0; simp (config := { decide := true }) [hE0, pairsRev]
      · simp (config := { decide := true }) [Function.update_of_ne h0]
    · rw [h1N, hsumC, schAll_nil I hE']; rfl
    · rw [h1M, gEdges_nil I hE']; rfl
    · exact e1
  obtain ⟨hKk, hKL, hLB⟩ := hS hE'
  have hc : (rv rE : Ex CR).eval s1.env ≠ 0 := by
    show s1.env rE ≠ 0
    rw [r1.env_of (by decide), hE]; exact fun h => hE' (List.length_eq_zero_iff.mp h)
  obtain ⟨s2, r2, h2s, h2N, h2p, h2o⟩ := p4SzS_good I hw hH hk s1 hb1.1 h1p
    (by rw [r1.env_of (by decide), hE]) h1L1 (by rw [r1.env_of (by decide), hKk])
    (by rw [r1.stk_of (by decide), hSch])
    (by rw [r1.stk_of (by decide)]; exact hemp _ (by decide) (by decide) (by decide) (by decide))
    (by rw [hs1, Function.update_of_ne (by decide), hA0]) (by rw [h1N]; omega)
  have hb2 := (r1.seq r2).bdd hw hb hp
  have e2 : ∀ r, wReg r p4SzS = false → wReg r p4Loc = false → s2.env r = st.env r :=
    fun r a b => by rw [r2.env_of a, r1.env_of b]
  have hs2 : s2.stk = Function.update st.stk qSzB (clsSizes I) := by
    rw [h2s, hs1, clsSizes_eq']; simp
  have hpre : SchPre I ε w s2 := by
    refine ⟨hE', hb2.1, h2p, by rw [e2 _ (by decide) (by decide), hε],
      by rw [r2.env_of (by decide), h1M], by rw [e2 _ (by decide) (by decide), hTr],
      by rw [e2 _ (by decide) (by decide), hW], by rw [e2 _ (by decide) (by decide), hL],
      by rw [r2.env_of (by decide), h1L1], by rw [e2 _ (by decide) (by decide), hE],
      by rw [e2 _ (by decide) (by decide), hKk], by rw [e2 _ (by decide) (by decide), hKL],
      by rw [e2 _ (by decide) (by decide), hLB],
      by rw [hs2, Function.update_of_ne (by decide), hAns],
      by rw [hs2, Function.update_of_ne (by decide), hSch], fun q a b c d e => ?_⟩
    rw [hs2, Function.update_of_ne e]; exact hemp q a b c d
  obtain ⟨s3, r3, ⟨h3s, h3M, h3p, h3o⟩, h3k⟩ := hSpec ε hε1 s2 hpre
  refine ⟨s3, (CStm.Good.iteT hfE hc (r2.seq r3)).mono ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [condCost, rv, Ex.size]; nlinarith
  · rw [h3s, hs2]
    funext q
    by_cases h0 : q = q4E
    · subst h0; simp (config := { decide := true }) [hE0, Function.update_of_ne (show q4E ≠ qSzB by decide)]
    · simp (config := { decide := true }) [Function.update_of_ne h0]
  · rw [h3k rNt (by simp (config := { decide := true }) [p4Keep]), h2N, h1N, hsumC]
  · rw [h3M, r2.env_of (by decide), h1M]; simp
  · rw [h3o, h2o, h1o]
  · intro r hr hn
    rw [h3k r hr]
    simp only [p4Keep, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hn | exact e2 _ (by decide) (by decide)

end Lax119563Proofs.Compiler
