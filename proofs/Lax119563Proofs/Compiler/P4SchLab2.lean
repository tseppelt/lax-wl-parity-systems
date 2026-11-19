import Lax119563Proofs.Compiler.P4SchLab

/-!
# Pass `P4`, schema part: link and update label emitters

* `lLab a`: link label `a` (`lnkE1`): last track in `rc1`, end answer in `rc2, rc3`;
* `uLab a b`: update label (`updE1`): previous in `rc8`, track `r4TP`, coefficient base `rc2`,
  rank code `rc5`;
* `fLab a b`: first entry of a column of a binary schema (`updF1`): start answer in `rc3, rc4`.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Link labels -/

/-- The link hub position `r4H + 4 r4Tn + a`. -/
def hL (a : ℕ) : Ex CR :=
  .add (rv r4H) (.add (rv r4Tn) (.add (rv r4Tn) (.add (rv r4Tn) (.add (rv r4Tn) (.const a)))))

lemma hL_eval (a : ℕ) (env : Fin CR → ℕ) : (hL a).eval env = env r4H + 4 * env r4Tn + a := by
  simp only [hL, rv, Ex.eval]; ring

/-- The link label `a`. -/
def lLab (a : ℕ) : CStm CR CQ :=
  .seq (pE (hL a) (.add (rv rc1) (.const a)))
    (.seq (.set rc6 (.const a)) (.seq (cposS rLB rc2 rc3 rc6) (pEo (hL a) r4F r4V)))

set_option maxHeartbeats 1000000 in
lemma lLab_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (a : ℕ) (ha : a ≤ 1)
    (s : NSt CR CQ) {H T LT LB o m : ℕ} (eH : s.env r4H = H) (eT : s.env r4Tn = T)
    (eLT : s.env rc1 = LT) (eLB : s.env rLB = LB) (eo : s.env rc2 = o) (em : s.env rc3 = m)
    (hm2 : m ≤ 2) (hH : H + 4 * T + 2 < 2 ^ w) (hLT : LT + 2 < 2 ^ w)
    (hU : LB + o + 2 < 2 ^ w) (hV4 : s.env r4V < 2 ^ w) (hm : s.env r4M + 2 < 2 ^ w) :
    ∃ s', Good x w (lLab a) s s' (80 * Ex.nodeCost w) ∧
      EdgeEff s s' (lnkE1 (H + 4 * T + a) LT (cposN LB o m a) a) ∧
      s'.env r4V < 2 ^ w ∧ ∀ r, r ∉ labW → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hLf : ∀ env : Fin CR → ℕ, env r4H = H → env r4Tn = T → (hL a).Fits w env := by
    intro env e1 e2; simp only [hL, rv, Ex.Fits, Ex.eval, e1, e2]; omega
  obtain ⟨s1, g1, eff1, fr1⟩ := pE_good (x := x) (w := w) (hL a) (.add (rv rc1) (.const a))
    s (hLf _ eH eT) (by simp only [rv, Ex.Fits, Ex.eval, eLT]; omega) (by omega)
  have g2 := Good.set (x := x) (w := w) (st := s1) (r := rc6) (e := .const a)
    (by simp only [Ex.Fits]; omega)
  set s2 := s1.set rc6 ((Ex.const a : Ex CR).eval s1.env)
  have e2 : ∀ r, r ≠ rc6 → r ≠ r4M → s2.env r = s.env r := fun r h1 h2 => by
    simp only [s2, NSt.set_env, Function.update_of_ne h1]; exact fr1 r h2
  have e26 : s2.env rc6 = a := by simp +decide [s2, Ex.eval]
  obtain ⟨s3, g3, f3, v3, hv3, k3, p3, o3, fr3⟩ := cposS_good (x := x) hw (lb := rLB) (off := rc2)
    (md := rc3) (a := rc6) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s2
    (by rw [e2 _ (by decide) (by decide), em]; exact hm2) (by rw [e26]; exact ha)
    (by rw [e2 _ (by decide) (by decide), e2 _ (by decide) (by decide), eLB, eo]; omega)
    (by rw [e2 _ (by decide) (by decide)]; exact hV4)
  rw [e2 _ (by decide) (by decide), e2 _ (by decide) (by decide), e2 _ (by decide) (by decide),
    e26, eLB, eo, em] at f3 v3
  have e3H : s3.env r4H = H := by
    rw [fr3 _ (by decide) (by decide), e2 _ (by decide) (by decide), eH]
  have e3T : s3.env r4Tn = T := by
    rw [fr3 _ (by decide) (by decide), e2 _ (by decide) (by decide), eT]
  have e3M : s3.env r4M = s.env r4M + 1 := by
    rw [fr3 _ (by decide) (by decide)]
    simp only [s2, NSt.set_env, Function.update_of_ne (show r4M ≠ rc6 by decide), eff1.2.1]
    simp
  obtain ⟨s4, g4, eff4, fr4⟩ := pEo_good (x := x) hw (hL a) r4F r4V (by decide) s3 _ f3 v3
    (hLf _ e3H e3T) hv3 (by rw [e3M]; omega)
  refine ⟨s4, (g1.seq (g2.seq (g3.seq g4))).mono ?_, ?_, ?_, ?_⟩
  · simp only [hL, rv, Ex.size]; nlinarith
  · have eff13 : EdgeEff s1 s3 [] := by
      refine EdgeEff.of_frame ?_ ?_ ?_ ?_
      · rw [k3]; simp +decide [s2]
      · rw [fr3 _ (by decide) (by decide)]; simp +decide [s2]
      · rw [p3]; simp +decide [s2]
      · rw [o3]; simp +decide [s2]
    have := (eff1.trans eff13).trans eff4
    simpa [lnkE1, hL_eval, e3H, e3T, eH, eT, eLT, rv, Ex.eval] using this
  · rw [fr4 _ (by decide)]; exact hv3
  · intro r hr
    simp only [labW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [fr4 r hr.2.2.2.2.2.1, fr3 r hr.2.2.2.1 hr.2.2.2.2.1]
    exact e2 r hr.1 hr.2.2.2.2.2.1

/-! ## Update labels -/

/-- `QR + 2 ⌊X / 2⌋ + d` (coefficient position from the rank code `X = 2ρ + 1` in `rc5`,
coefficient base in `rc2`). -/
def cpE (d : ℕ) : Ex CR :=
  .add (rv rc2) (.add (.half (rv rc5)) (.add (.half (rv rc5)) (.const d)))

lemma cpE_eval (d : ℕ) (env : Fin CR → ℕ) :
    (cpE d).eval env = env rc2 + 2 * (env rc5 / 2) + d := by
  simp only [cpE, rv, Ex.eval]; ring

/-- The update label `2a + b`. -/
def uLab (a b : ℕ) : CStm CR CQ :=
  .seq (pE (hE (2 * a + b)) (.add (rv rc8) (.const a)))
    (.seq (pE (hE (2 * a + b)) (.add (rv r4TP) (.const b)))
      (pE (hE (2 * a + b)) (cpE ((a + b) % 2))))

set_option maxHeartbeats 1000000 in
lemma uLab_good {w : ℕ} {x : List Bool} (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1)
    (s : NSt CR CQ) {H PP TP QR X : ℕ} (eH : s.env r4H = H) (ePP : s.env rc8 = PP)
    (eTP : s.env r4TP = TP) (eQR : s.env rc2 = QR) (eX : s.env rc5 = X)
    (hH : H + 4 < 2 ^ w) (hPP : PP + 2 < 2 ^ w) (hTP : TP + 2 < 2 ^ w)
    (hQR : QR + X + 2 < 2 ^ w) (hm : s.env r4M + 3 < 2 ^ w) :
    ∃ s', Good x w (uLab a b) s s' (60 * Ex.nodeCost w) ∧
      EdgeEff s s' (updE1 (H + (2 * a + b)) PP TP (QR + 2 * (X / 2)) a b) ∧
      ∀ r, r ≠ r4M → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have hX2 : 2 * (X / 2) ≤ X := Nat.mul_div_le X 2
  have hhf : ∀ env : Fin CR → ℕ, env r4H = H → (hE (2 * a + b)).Fits w env := by
    intro env e1; simp only [hE, rv, Ex.Fits, Ex.eval, e1]; omega
  obtain ⟨s1, g1, eff1, fr1⟩ := pE_good (x := x) (w := w) (hE (2 * a + b)) (.add (rv rc8) (.const a))
    s (hhf _ eH) (by simp only [rv, Ex.Fits, Ex.eval, ePP]; omega) (by omega)
  obtain ⟨s2, g2, eff2, fr2⟩ := pE_good (x := x) (w := w) (hE (2 * a + b)) (.add (rv r4TP) (.const b))
    s1 (hhf _ (by rw [fr1 _ (by decide), eH]))
    (by simp only [rv, Ex.Fits, Ex.eval, fr1 r4TP (by decide), eTP]; omega)
    (by rw [eff1.2.1]; simp; omega)
  have e2 : ∀ r, r ≠ r4M → s2.env r = s.env r := fun r h => (fr2 r h).trans (fr1 r h)
  obtain ⟨s3, g3, eff3, fr3⟩ := pE_good (x := x) (w := w) (hE (2 * a + b)) (cpE ((a + b) % 2))
    s2 (hhf _ (by rw [e2 _ (by decide), eH]))
    (by
      have : (a + b) % 2 ≤ 1 := by omega
      simp only [cpE, rv, Ex.Fits, Ex.eval, e2 rc2 (by decide), e2 rc5 (by decide), eQR, eX]
      refine ⟨by omega, ⟨by omega, ⟨by omega, by omega, by omega⟩, by omega⟩, by omega⟩)
    (by rw [eff2.2.1, eff1.2.1]; simp; omega)
  refine ⟨s3, (g1.seq (g2.seq g3)).mono ?_, ?_, fun r h => (fr3 r h).trans (e2 r h)⟩
  · simp only [hE, cpE, rv, Ex.size]; nlinarith
  · have := (eff1.trans eff2).trans eff3
    have h1 := fr1 r4H (by decide)
    have h2 := e2 r4H (by decide)
    have h3 := fr1 r4TP (by decide)
    have h4 := e2 rc2 (by decide)
    have h5 := e2 rc5 (by decide)
    simp only [hE_eval, cpE_eval, rv, Ex.eval, h1, h2, h3, h4, h5, eH, ePP, eTP, eQR, eX]
      at this
    simpa [updE1, add_assoc] using this

/-- Registers written by `fLab`. -/
def fW : List (Fin CR) := [r4F, r4V, r4M, r4Dist]

/-- The update label `2a + b` at the first entry of a column of a binary schema; bit register
`r4Dist`. -/
def fLab (a b : ℕ) : CStm CR CQ :=
  .seq (pE (hE (2 * a + b)) (.add (rv r4TP) (.const b)))
    (.seq (pE (hE (2 * a + b)) (cpE ((a + b) % 2)))
      (.seq (.set r4Dist (.const a)) (.seq (cposS rLB rc3 rc4 r4Dist)
        (pEo (hE (2 * a + b)) r4F r4V))))

set_option maxHeartbeats 1000000 in
lemma fLab_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1)
    (s : NSt CR CQ) {H TP QR X LB o m : ℕ} (eH : s.env r4H = H)
    (eTP : s.env r4TP = TP) (eQR : s.env rc2 = QR) (eX : s.env rc5 = X) (eLB : s.env rLB = LB)
    (eo : s.env rc3 = o) (em : s.env rc4 = m) (hm2 : m ≤ 2)
    (hH : H + 4 < 2 ^ w) (hTP : TP + 2 < 2 ^ w)
    (hQR : QR + X + 2 < 2 ^ w) (hU : LB + o + 2 < 2 ^ w) (hV4 : s.env r4V < 2 ^ w)
    (hm : s.env r4M + 3 < 2 ^ w) :
    ∃ s', Good x w (fLab a b) s s' (80 * Ex.nodeCost w) ∧
      EdgeEff s s' (updF1 (H + (2 * a + b)) TP (QR + 2 * (X / 2)) (cposN LB o m a) a b) ∧
      s'.env r4V < 2 ^ w ∧ ∀ r, r ∉ fW → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hX2 : 2 * (X / 2) ≤ X := Nat.mul_div_le X 2
  have hhf : ∀ env : Fin CR → ℕ, env r4H = H → (hE (2 * a + b)).Fits w env := by
    intro env e1; simp only [hE, rv, Ex.Fits, Ex.eval, e1]; omega
  obtain ⟨s1, g1, eff1, fr1⟩ := pE_good (x := x) (w := w) (hE (2 * a + b)) (.add (rv r4TP) (.const b))
    s (hhf _ eH) (by simp only [rv, Ex.Fits, Ex.eval, eTP]; omega) (by omega)
  obtain ⟨s2, g2, eff2, fr2⟩ := pE_good (x := x) (w := w) (hE (2 * a + b)) (cpE ((a + b) % 2))
    s1 (hhf _ (by rw [fr1 _ (by decide), eH]))
    (by
      have : (a + b) % 2 ≤ 1 := by omega
      simp only [cpE, rv, Ex.Fits, Ex.eval, fr1 rc2 (by decide), fr1 rc5 (by decide), eQR, eX]
      refine ⟨by omega, ⟨by omega, ⟨by omega, by omega, by omega⟩, by omega⟩, by omega⟩)
    (by rw [eff1.2.1]; simp; omega)
  have e2 : ∀ r, r ≠ r4M → s2.env r = s.env r := fun r h => (fr2 r h).trans (fr1 r h)
  have g3 := Good.set (x := x) (w := w) (st := s2) (r := r4Dist) (e := .const a)
    (by simp only [Ex.Fits]; omega)
  set s3 := s2.set r4Dist ((Ex.const a : Ex CR).eval s2.env)
  have e3 : ∀ r, r ≠ r4Dist → r ≠ r4M → s3.env r = s.env r := fun r h1 h2 => by
    simp only [s3, NSt.set_env, Function.update_of_ne h1]; exact e2 r h2
  have e3D : s3.env r4Dist = a := by simp +decide [s3, Ex.eval]
  obtain ⟨s4, g4, f4, v4, hv4, k4, p4, o4, fr4⟩ := cposS_good (x := x) hw (lb := rLB) (off := rc3)
    (md := rc4) (a := r4Dist) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s3
    (by rw [e3 _ (by decide) (by decide), em]; exact hm2) (by rw [e3D]; exact ha)
    (by rw [e3 _ (by decide) (by decide), e3 _ (by decide) (by decide), eLB, eo]; omega)
    (by rw [e3 _ (by decide) (by decide)]; exact hV4)
  rw [e3 _ (by decide) (by decide), e3 _ (by decide) (by decide), e3 _ (by decide) (by decide),
    e3D, eLB, eo, em] at f4 v4
  have e4H : s4.env r4H = H := by
    rw [fr4 _ (by decide) (by decide), e3 _ (by decide) (by decide), eH]
  have e4M : s4.env r4M = s.env r4M + 2 := by
    rw [fr4 _ (by decide) (by decide)]
    simp only [s3, NSt.set_env, Function.update_of_ne (show r4M ≠ r4Dist by decide), eff2.2.1,
      eff1.2.1]
    simp <;> omega
  obtain ⟨s5, g5, eff5, fr5⟩ := pEo_good (x := x) hw (hE (2 * a + b)) r4F r4V (by decide) s4 _
    f4 v4 (hhf _ e4H) hv4 (by rw [e4M]; omega)
  refine ⟨s5, (g1.seq (g2.seq (g3.seq (g4.seq g5)))).mono ?_, ?_, ?_, ?_⟩
  · simp only [hE, cpE, rv, Ex.size]; nlinarith
  · have eff24 : EdgeEff s2 s4 [] := by
      refine EdgeEff.of_frame ?_ ?_ ?_ ?_
      · rw [k4]; simp +decide [s3]
      · rw [fr4 _ (by decide) (by decide)]; simp +decide [s3]
      · rw [p4]; simp +decide [s3]
      · rw [o4]; simp +decide [s3]
    have := ((eff1.trans eff2).trans eff24).trans eff5
    have h1 := fr1 r4H (by decide)
    have h3 := fr1 rc2 (by decide)
    have h5 := fr1 rc5 (by decide)
    simp only [hE_eval, cpE_eval, rv, Ex.eval, h1, h3, h5, e4H, eH, eTP, eQR, eX] at this
    simpa [updF1, add_assoc] using this
  · rw [fr5 _ (by decide)]; exact hv4
  · intro r hr
    simp only [fW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [fr5 r hr.2.2.1, fr4 r hr.1 hr.2.1]
    exact e3 r hr.2.2.2 hr.2.2.1

end Lax119563Proofs.Compiler
