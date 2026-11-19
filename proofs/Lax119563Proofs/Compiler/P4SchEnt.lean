import Lax119563Proofs.Compiler.P4SchHub

/-!
# Pass `P4`, schema part: one entry of section 2

`p4Ent`: the update hub of the entry `t` of a column (hub `Hc + 4t` in `r4H`, track
`TPc + 2t` in `r4TP`, previous track `rc7`, first-entry flag `rc6`, rank code `rc5`,
coefficient base `rc2`, start answer `rc3, rc4`), then advance (`entE`, `p4Ent_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- The edges of entry `t` of a column (numbers). -/
def entE (T t Hc TPc SP cp LB oU mU : ℕ) : List (ℕ × ℕ) :=
  if t = 0 ∧ T = 0 then updFL (Hc + 4 * t) (TPc + 2 * t) cp LB oU mU
  else updL (Hc + 4 * t) (if t = 0 then SP else TPc + 2 * (t - 1)) (TPc + 2 * t) cp

/-- Advance to the next entry. -/
def p4EntAdv : CStm CR CQ :=
  .seq (.set rc7 (rv r4TP)) (.seq (.set r4TP (.add (rv r4TP) (.const 2)))
    (.seq (.set r4H (.add (rv r4H) (.const 4))) (.set rc6 (.const 0))))

lemma p4EntAdv_good {w : ℕ} {x : List Bool} (s : NSt CR CQ) {TP H : ℕ} (eTP : s.env r4TP = TP)
    (eH : s.env r4H = H) (hTP : TP + 2 < 2 ^ w) (hH : H + 4 < 2 ^ w) :
    Good x w p4EntAdv s ((((s.set rc7 TP).set r4TP (TP + 2)).set r4H (H + 4)).set rc6 0)
      (20 * Ex.nodeCost w) := by
  have hN := CStm.nodeCost_ge w
  have g1 := CStm.Good.set (x := x) (w := w) (st := s) (r := rc7) (e := rv r4TP)
    (by simp only [Ex.Fits, rv, eTP]; omega)
  have g2 := CStm.Good.set (x := x) (w := w) (st := s.set rc7 TP) (r := r4TP)
    (e := .add (rv r4TP) (.const 2)) (by simp +decide [Ex.Fits, rv, eTP, Ex.eval]; omega)
  have g3 := CStm.Good.set (x := x) (w := w) (st := (s.set rc7 TP).set r4TP (TP + 2)) (r := r4H)
    (e := .add (rv r4H) (.const 4)) (by simp +decide [Ex.Fits, rv, eH, Ex.eval]; omega)
  have g4 := CStm.Good.set (x := x) (w := w)
    (st := ((s.set rc7 TP).set r4TP (TP + 2)).set r4H (H + 4)) (r := rc6) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  have e1 : (rv r4TP : Ex CR).eval s.env = TP := by simp [rv, Ex.eval, eTP]
  have e2 : (Ex.add (rv r4TP) (.const 2) : Ex CR).eval (s.set rc7 TP).env = TP + 2 := by
    simp +decide [rv, Ex.eval, eTP]
  have e3 : (Ex.add (rv r4H) (.const 4) : Ex CR).eval ((s.set rc7 TP).set r4TP (TP + 2)).env =
      H + 4 := by simp +decide [rv, Ex.eval, eH]
  rw [e1] at g1; rw [e2] at g2; rw [e3] at g3
  exact (g1.seq (g2.seq (g3.seq g4))).mono (by simp only [Ex.size, rv]; omega)

/-- One entry. -/
def p4Ent : CStm CR CQ :=
  .seq (.ite (.lt (rv r4Tn) (rv rc6)) fLabs
      (.seq (.ite (rv rc6) (.set rc8 (rv r4SP)) (.set rc8 (rv rc7))) uLabs))
    p4EntAdv

/-- Registers written by an entry. -/
def entW : List (Fin CR) := [rc6, rc7, rc8, r4TP, r4H, r4F, r4V, r4M, r4Dist]

set_option maxHeartbeats 2000000 in
lemma p4Ent_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ)
    {T t Hc TPc SP QR X LB oU mU : ℕ} (eT : s.env r4Tn = T) (hT : T ≤ 1)
    (eF : s.env rc6 = if t = 0 then 1 else 0) (eP : 0 < t → s.env rc7 = TPc + 2 * (t - 1))
    (eSP : s.env r4SP = SP) (eH : s.env r4H = Hc + 4 * t) (eTP : s.env r4TP = TPc + 2 * t)
    (eQR : s.env rc2 = QR) (eX : s.env rc5 = X) (eLB : s.env rLB = LB) (eo : s.env rc3 = oU)
    (em : s.env rc4 = mU) (hm2 : mU ≤ 2)
    (hH : Hc + 4 * t + 4 < 2 ^ w) (hTP : TPc + 2 * t + 2 < 2 ^ w) (hSP : SP + 2 < 2 ^ w)
    (hQR : QR + X + 2 < 2 ^ w) (hU : LB + oU + 2 < 2 ^ w) (hV4 : s.env r4V < 2 ^ w)
    (hm : s.env r4M + 12 < 2 ^ w) :
    ∃ s', Good x w p4Ent s s' (500 * Ex.nodeCost w) ∧
      EdgeEff s s' (entE T t Hc TPc SP (QR + 2 * (X / 2)) LB oU mU) ∧
      s'.env rc7 = TPc + 2 * t ∧ s'.env r4TP = TPc + 2 * (t + 1) ∧
      s'.env r4H = Hc + 4 * (t + 1) ∧ s'.env rc6 = 0 ∧ s'.env r4V < 2 ^ w ∧
      ∀ r, r ∉ entW → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hC : (Ex.lt (rv r4Tn) (rv rc6) : Ex CR).Fits w s.env := by
    simp only [Ex.Fits, rv, eT, eF]; split_ifs <;> omega
  -- the hub
  obtain ⟨s1, g1, eff1, v1, fr1⟩ : ∃ s1, Good x w (.ite (.lt (rv r4Tn) (rv rc6)) fLabs
      (.seq (.ite (rv rc6) (.set rc8 (rv r4SP)) (.set rc8 (rv rc7))) uLabs)) s s1
      (400 * Ex.nodeCost w) ∧
      EdgeEff s s1 (entE T t Hc TPc SP (QR + 2 * (X / 2)) LB oU mU) ∧ s1.env r4V < 2 ^ w ∧
      ∀ r, r ∉ [rc8, r4F, r4V, r4M, r4Dist] → s1.env r = s.env r := by
    by_cases hf : t = 0 ∧ T = 0
    · obtain ⟨s1, g, eff, v, fr⟩ := fLabs_good (x := x) hw s eH eTP eQR eX eLB eo em hm2
        (by omega) (by omega) hQR hU hV4 hm
      refine ⟨s1, (CStm.Good.iteT hC (by simp [Ex.eval, rv, eT, eF, hf.1, hf.2]) g).mono ?_, ?_, v,
        fun r hr => fr r (by simp [fW] at hr ⊢; tauto)⟩
      · simp only [condCost, rv, Ex.size]; nlinarith
      · rw [entE, if_pos hf]; exact eff
    · have hc0 : (Ex.lt (rv r4Tn) (rv rc6) : Ex CR).eval s.env = 0 := by
        simp only [Ex.eval, rv, eT, eF]; split_ifs <;> omega
      set PP := if t = 0 then SP else TPc + 2 * (t - 1) with hPP
      have hF6 : (rv rc6 : Ex CR).Fits w s.env := by
        simp only [Ex.Fits, rv, eF]; split_ifs <;> omega
      obtain ⟨s0, g0, e0⟩ : ∃ s0, Good x w (.ite (rv rc6) (.set rc8 (rv r4SP))
          (.set rc8 (rv rc7))) s s0 (10 * Ex.nodeCost w) ∧ s0 = s.set rc8 PP := by
        by_cases ht : t = 0
        · refine ⟨_, (CStm.Good.iteT hF6 (by simp [Ex.eval, rv, eF, ht])
            (CStm.Good.set (r := rc8) (e := rv r4SP) (by simp only [Ex.Fits, rv, eSP]; omega))).mono
            ?_, by simp [hPP, ht, Ex.eval, rv, eSP]⟩
          simp only [condCost, rv, Ex.size]; nlinarith
        · have := eP (by omega)
          refine ⟨_, (CStm.Good.iteF hF6 (by simp [Ex.eval, rv, eF, ht])
            (CStm.Good.set (r := rc8) (e := rv rc7) (by simp only [Ex.Fits, rv, this]; omega))).mono
            ?_, by simp [hPP, ht, Ex.eval, rv, this]⟩
          simp only [condCost, rv, Ex.size]; nlinarith
      subst e0
      have q0 : ∀ r, r ≠ rc8 → (s.set rc8 PP).env r = s.env r := fun r h => by
        simp [Function.update_of_ne h]
      obtain ⟨s1, g, eff, fr⟩ := uLabs_good (x := x) (w := w) (s.set rc8 PP) (PP := PP)
        (by rw [q0 _ (by decide), eH]) (by simp) (by rw [q0 _ (by decide), eTP])
        (by rw [q0 _ (by decide), eQR]) (by rw [q0 _ (by decide), eX]) (by omega)
        (by rw [hPP]; split_ifs <;> omega) (by omega) hQR
        (by rw [q0 _ (by decide)]; omega)
      refine ⟨s1, (CStm.Good.iteF hC hc0 (g0.seq g)).mono ?_, ?_, ?_, ?_⟩
      · simp only [condCost, rv, Ex.size]; nlinarith
      · rw [entE, if_neg hf]
        refine (EdgeEff.of_frame (st := s) (st' := s.set rc8 PP) rfl ?_ rfl rfl).trans eff
          |> fun h => by simpa using h
        simp [Function.update_of_ne (show r4M ≠ rc8 by decide)]
      · rw [fr _ (by decide), q0 _ (by decide)]; exact hV4
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [fr r hr.2.2.2.1, q0 r hr.1]
  -- advance
  have q1 : ∀ r, r ∉ [rc8, r4F, r4V, r4M, r4Dist] → s1.env r = s.env r := fr1
  have e1TP : s1.env r4TP = TPc + 2 * t := by rw [q1 _ (by decide), eTP]
  have e1H : s1.env r4H = Hc + 4 * t := by rw [q1 _ (by decide), eH]
  have gA := p4EntAdv_good (x := x) s1 e1TP e1H (by omega) (by omega)
  set s2 := (((s1.set rc7 (TPc + 2 * t)).set r4TP (TPc + 2 * t + 2)).set r4H
    (Hc + 4 * t + 4)).set rc6 0
  refine ⟨s2, (g1.seq gA).mono (by nlinarith), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := eff1.trans (EdgeEff.of_frame (st := s1) (st' := s2) (by simp [s2])
      (by simp +decide [s2]) rfl rfl)
    simpa using this
  · simp +decide [s2]
  · simp +decide [s2]; ring
  · simp +decide [s2]; ring
  · simp +decide [s2]
  · simp +decide [s2]; exact v1
  · intro r hr
    simp only [entW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hr
    simp only [s2, NSt.set_env, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h4, Function.update_of_ne h5]
    exact q1 r (by simp [h3, h6, h7, h8, h9])

end Lax119563Proofs.Compiler
