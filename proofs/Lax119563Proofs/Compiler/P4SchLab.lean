import Lax119563Proofs.Compiler.P4SchLib
import Lax119563Proofs.Compiler.PSch

/-!
# Pass `P4`, schema part: registers, stacks and the hub label emitters

Registers of the schema part (besides the parsing registers `rT, rP`, the persistent
`rE, rL, rL1, rKk, rLB, r4Eps, r4M` and `r4F, r4V` of `cposS`): `rJ` (schema index),
`r4PL = k (ℓ + 1)`, schema data `r4SB … r4TrkB`, column loop data `r4Dist … r4K`, column
scratch `rc1 … rc8`. Not written: `rW = 2`, `4`, `37`, `38`, `39`.
Stacks: `qS2` (schema records, forward), `qA2` (consumed answers), `qOrsF`/`qOrsB` (OR bits
of the schema forward / backup), `qRk`/`qRkF` (rank codes `2 ρ + 1` per column, terminated
by `0`).

Label emitters (one label of a hub, edges pushed with `pE`):
* `jLab a b`: junction label `2a + b` (`junE1`);
* `lLab a`: link label `a` (`lnkE1`);
* `uLab a b`: update label (`updE1`);
* `fLab a b`: update label at the first entry of a column of a binary schema (`updF1`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Registers and stacks -/

def r4PL : Fin CR := 34
def r4SB : Fin CR := 5
def r4Tn : Fin CR := 6
def r4D : Fin CR := 11
def r4BR : Fin CR := 12
def r4R2 : Fin CR := 13
def r4SumB : Fin CR := 14
def r4TrkB : Fin CR := 15
def r4Dist : Fin CR := 17
def r4Prev : Fin CR := 18
def r4H : Fin CR := 20
def r4SP : Fin CR := 23
def r4TP : Fin CR := 24
def r4K : Fin CR := 25
def rc1 : Fin CR := 26
def rc2 : Fin CR := 27
def rc3 : Fin CR := 28
def rc4 : Fin CR := 29
def rc5 : Fin CR := 30
def rc6 : Fin CR := 31
def rc7 : Fin CR := 32
def rc8 : Fin CR := 33

def qS2 : Fin CQ := 2
def qA2 : Fin CQ := 3
def qOrsF : Fin CQ := 5
def qOrsB : Fin CQ := 6
def qRk : Fin CQ := 7
def qRkF : Fin CQ := 8

/-- The hub position `r4H + i`. -/
def hE (i : ℕ) : Ex CR := .add (rv r4H) (.const i)

/-! ## Sorting two optional positions -/

/-- Push the present ones of two optional positions (flag `rc7`, value `rc8`; flag `r4F`,
value `r4V`), sorted. -/
def srt2 (h : Ex CR) : CStm CR CQ :=
  .ite (rv rc7)
    (.ite (rv r4F)
      (.ite (.lt (rv r4V) (rv rc8)) (.seq (pE h (rv r4V)) (pE h (rv rc8)))
        (.seq (pE h (rv rc8)) (pE h (rv r4V))))
      (pE h (rv rc8)))
    (pEo h r4F r4V)

lemma flag_fits {w : ℕ} (hw : 2 ≤ w) {env : Fin CR → ℕ} {f : Fin CR} {o : Option ℕ}
    (h : env f = if o.isSome then 1 else 0) : (rv f : Ex CR).Fits w env := by
  have : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  simp only [rv, Ex.Fits, h]; split_ifs <;> omega

lemma srt2_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (h : Ex CR) (s : NSt CR CQ)
    (o₁ o₂ : Option ℕ) (h1 : s.env rc7 = if o₁.isSome then 1 else 0)
    (h1v : ∀ a, o₁ = some a → s.env rc8 = a) (h2 : s.env r4F = if o₂.isSome then 1 else 0)
    (h2v : ∀ a, o₂ = some a → s.env r4V = a) (hv1 : s.env rc8 < 2 ^ w)
    (hv2 : s.env r4V < 2 ^ w) (hh : h.Fits w s.env) (hhr : ∀ env : Fin CR → ℕ,
      (∀ r, r ≠ r4M → env r = s.env r) → h.eval env = h.eval s.env ∧ h.Fits w env)
    (hm : s.env r4M + 2 < 2 ^ w) :
    ∃ s', Good x w (srt2 h) s s' ((2 * h.size + 30) * Ex.nodeCost w) ∧
      EdgeEff s s' ((sort2 o₁ o₂).map fun v => (h.eval s.env, v)) ∧
      ∀ r, r ≠ r4M → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hF1 := flag_fits hw h1
  have hF2 := flag_fits hw h2
  have hv1' : (rv rc8 : Ex CR).Fits w s.env := hv1
  have hv2' : (rv r4V : Ex CR).Fits w s.env := hv2
  cases o₁ with
  | none =>
    obtain ⟨s', g, eff, fr⟩ := pEo_good (x := x) hw h r4F r4V (by decide) s o₂ h2 h2v hh hv2
      (by omega)
    refine ⟨s', (Good.iteF hF1 (by simp [rv, Ex.eval, h1]) g).mono ?_, ?_, fr⟩
    · simp only [condCost, rv, Ex.size]; nlinarith
    · cases o₂ <;> simpa [sort2] using eff
  | some a =>
    have ha := h1v a rfl
    cases o₂ with
    | none =>
      obtain ⟨s', g, eff, fr⟩ := pE_good (x := x) (w := w) h (rv rc8) s hh hv1' (by omega)
      refine ⟨s', (Good.iteT hF1 (by simp [rv, Ex.eval, h1])
        (Good.iteF hF2 (by simp [rv, Ex.eval, h2]) g)).mono ?_, ?_, fr⟩
      · simp only [condCost, rv, Ex.size]; nlinarith
      · simpa [sort2, rv, Ex.eval, ha] using eff
    | some b =>
      have hb := h2v b rfl
      have hF3 : (Ex.lt (rv r4V) (rv rc8) : Ex CR).Fits w s.env := ⟨hv2', hv1'⟩
      by_cases hab : a ≤ b
      · obtain ⟨s1, g1, eff1, fr1⟩ := pE_good (x := x) (w := w) h (rv rc8) s hh hv1' (by omega)
        have e1 := hhr s1.env fr1
        obtain ⟨s2, g2, eff2, fr2⟩ := pE_good (x := x) (w := w) h (rv r4V) s1 e1.2
          (by simpa [rv, Ex.Fits, fr1 r4V (by decide)] using hv2)
          (by rw [eff1.2.1]; simp; omega)
        refine ⟨s2, (Good.iteT hF1 (by simp [rv, Ex.eval, h1])
          (Good.iteT hF2 (by simp [rv, Ex.eval, h2])
            (Good.iteF hF3 (by simp [rv, Ex.eval, ha, hb]; omega) (g1.seq g2)))).mono ?_,
          ?_, fun r hr => (fr2 r hr).trans (fr1 r hr)⟩
        · simp only [condCost, rv, Ex.size]; nlinarith
        · have := eff1.trans eff2
          simpa [sort2, hab, rv, Ex.eval, ha, hb, e1.1, fr1 r4V (by decide)] using this
      · obtain ⟨s1, g1, eff1, fr1⟩ := pE_good (x := x) (w := w) h (rv r4V) s hh hv2' (by omega)
        have e1 := hhr s1.env fr1
        obtain ⟨s2, g2, eff2, fr2⟩ := pE_good (x := x) (w := w) h (rv rc8) s1 e1.2
          (by simpa [rv, Ex.Fits, fr1 rc8 (by decide)] using hv1)
          (by rw [eff1.2.1]; simp; omega)
        refine ⟨s2, (Good.iteT hF1 (by simp [rv, Ex.eval, h1])
          (Good.iteT hF2 (by simp [rv, Ex.eval, h2])
            (Good.iteT hF3 (by simp [rv, Ex.eval, ha, hb]; omega) (g1.seq g2)))).mono ?_,
          ?_, fun r hr => (fr2 r hr).trans (fr1 r hr)⟩
        · simp only [condCost, rv, Ex.size]; nlinarith
        · have := eff1.trans eff2
          simpa [sort2, hab, rv, Ex.eval, ha, hb, e1.1, fr1 rc8 (by decide)] using this


lemma hE_eval (i : ℕ) (env : Fin CR → ℕ) : (hE i).eval env = env r4H + i := rfl

lemma hE_stable {w : ℕ} (i : ℕ) (s : NSt CR CQ) (hh : s.env r4H + i < 2 ^ w) :
    ∀ env : Fin CR → ℕ, (∀ r, r ≠ r4M → env r = s.env r) →
      (hE i).eval env = (hE i).eval s.env ∧ (hE i).Fits w env := by
  intro env he
  have := he r4H (by decide)
  refine ⟨by simp [hE_eval, this], ?_⟩
  simp only [hE, rv, Ex.Fits, Ex.eval, this]; omega

/-! ## Junction labels -/

/-- The junction label `2a + b`: answers `U` in `rc2, rc3` (offset, mode), `V` in `rc4, rc5`. -/
def jLab (a b : ℕ) : CStm CR CQ :=
  .seq (pE (hE (2 * a + b)) (.add (rv r4SP) (.const ((a + b) % 2))))
    (.seq (.set rc6 (.const a)) (.seq (cposS rLB rc2 rc3 rc6)
      (.seq (.set rc7 (rv r4F)) (.seq (.set rc8 (rv r4V))
        (.seq (.set rc6 (.const b)) (.seq (cposS rLB rc4 rc5 rc6) (srt2 (hE (2 * a + b)))))))))

/-- Registers written by the label emitters. -/
def labW : List (Fin CR) := [rc6, rc7, rc8, r4F, r4V, r4M, r4Dist]

set_option maxHeartbeats 1000000 in
lemma jLab_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1)
    (s : NSt CR CQ) {H SP LB oU mU oV mV : ℕ} (eH : s.env r4H = H) (eSP : s.env r4SP = SP)
    (eLB : s.env rLB = LB) (eoU : s.env rc2 = oU) (emU : s.env rc3 = mU) (eoV : s.env rc4 = oV)
    (emV : s.env rc5 = mV) (hmU : mU ≤ 2) (hmV : mV ≤ 2) (hH : H + 4 < 2 ^ w)
    (hSP : SP + 2 < 2 ^ w) (hU : LB + oU + 2 < 2 ^ w) (hV : LB + oV + 2 < 2 ^ w)
    (hV4 : s.env r4V < 2 ^ w) (hm : s.env r4M + 3 < 2 ^ w) :
    ∃ s', Good x w (jLab a b) s s' (100 * Ex.nodeCost w) ∧
      EdgeEff s s' (junE1 (H + (2 * a + b)) SP (cposN LB oU mU a) (cposN LB oV mV b) a b) ∧
      s'.env r4V < 2 ^ w ∧ ∀ r, r ∉ labW → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  set i := 2 * a + b with hi
  have hi3 : i ≤ 3 := by omega
  -- the sum edge
  obtain ⟨s1, g1, eff1, fr1⟩ := pE_good (x := x) (w := w) (hE i) (.add (rv r4SP) (.const ((a + b) % 2)))
    s (by simp only [hE, rv, Ex.Fits, Ex.eval, eH]; omega)
    (by simp only [rv, Ex.Fits, Ex.eval, eSP]; omega) (by omega)
  -- the first coordinate
  have g2 := Good.set (x := x) (w := w) (st := s1) (r := rc6) (e := .const a)
    (by simp only [Ex.Fits]; omega)
  set s2 := s1.set rc6 ((Ex.const a : Ex CR).eval s1.env)
  have e2 : ∀ r, r ≠ rc6 → r ≠ r4M → s2.env r = s.env r := fun r h1 h2 => by
    simp only [s2, NSt.set_env, Function.update_of_ne h1]; exact fr1 r h2
  have e26 : s2.env rc6 = a := by simp +decide [s2, Ex.eval]
  obtain ⟨s3, g3, f3, v3, hv3, k3, p3, o3, fr3⟩ := cposS_good (x := x) hw (lb := rLB) (off := rc2)
    (md := rc3) (a := rc6) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s2
    (by rw [e2 _ (by decide) (by decide), emU]; exact hmU) (by rw [e26]; exact ha)
    (by rw [e2 _ (by decide) (by decide), e2 _ (by decide) (by decide), eLB, eoU]; omega)
    (by rw [e2 _ (by decide) (by decide)]; exact hV4)
  rw [e2 _ (by decide) (by decide), e2 _ (by decide) (by decide), e2 _ (by decide) (by decide),
    e26, eLB, eoU, emU] at f3 v3
  have g4 := Good.set (x := x) (w := w) (st := s3) (r := rc7) (e := rv r4F)
    (by simp only [rv, Ex.Fits, f3]; split_ifs <;> omega)
  set s4 := s3.set rc7 ((rv r4F : Ex CR).eval s3.env)
  have g5 := Good.set (x := x) (w := w) (st := s4) (r := rc8) (e := rv r4V)
    (by simp only [s4, rv, Ex.Fits, NSt.set_env, Function.update_of_ne (show r4V ≠ rc7 by decide)]
        exact hv3)
  set s5 := s4.set rc8 ((rv r4V : Ex CR).eval s4.env)
  have g6 := Good.set (x := x) (w := w) (st := s5) (r := rc6) (e := .const b)
    (by simp only [Ex.Fits]; omega)
  set s6 := s5.set rc6 ((Ex.const b : Ex CR).eval s5.env)
  have e6 : ∀ r, r ≠ rc6 → r ≠ rc7 → r ≠ rc8 → r ≠ r4F → r ≠ r4V → r ≠ r4M →
      s6.env r = s.env r := fun r h1 h2 h3 h4 h5 h6 => by
    simp only [s6, s5, s4, NSt.set_env, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3]
    rw [fr3 r h4 h5]; exact e2 r h1 h6
  have e66 : s6.env rc6 = b := by simp +decide [s6, Ex.eval]
  have e67 : s6.env rc7 = if (cposN LB oU mU a).isSome then 1 else 0 := by
    simp +decide [s6, s5, s4, Ex.eval, rv, f3]
  have e68 : ∀ v, cposN LB oU mU a = some v → s6.env rc8 = v := by
    intro v hv; simp +decide [s6, s5, s4, Ex.eval, rv, v3 v hv]
  have e68' : s6.env rc8 < 2 ^ w := by simp +decide [s6, s5, s4, Ex.eval, rv]; exact hv3
  obtain ⟨s7, g7, f7, v7, hv7, k7, p7, o7, fr7⟩ := cposS_good (x := x) hw (lb := rLB) (off := rc4)
    (md := rc5) (a := rc6) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s6
    (by rw [e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), emV]
        exact hmV) (by rw [e66]; exact hb)
    (by rw [e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), eLB, eoV]
        omega)
    (by simp +decide [s6, s5, s4, Ex.eval, rv]; exact hv3)
  rw [e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e66, eLB, eoV, emV] at f7 v7
  have e7H : s7.env r4H = H := by
    rw [fr7 _ (by decide) (by decide),
      e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), eH]
  have e7M : s7.env r4M = s.env r4M + 1 := by
    rw [fr7 _ (by decide) (by decide)]
    simp only [s6, s5, s4, NSt.set_env, Function.update_of_ne (show r4M ≠ rc6 by decide),
      Function.update_of_ne (show r4M ≠ rc7 by decide),
      Function.update_of_ne (show r4M ≠ rc8 by decide)]
    rw [fr3 _ (by decide) (by decide)]
    simp only [s2, NSt.set_env, Function.update_of_ne (show r4M ≠ rc6 by decide), eff1.2.1]
    simp
  obtain ⟨s8, g8, eff8, fr8⟩ := srt2_good (x := x) hw (hE i) s7 _ _
    (by rw [fr7 _ (by decide) (by decide)]; exact e67)
    (fun v hv => by rw [fr7 _ (by decide) (by decide)]; exact e68 v hv) f7 v7
    (by rw [fr7 _ (by decide) (by decide)]; exact e68') hv7
    (by simp only [hE, rv, Ex.Fits, Ex.eval, e7H]; omega)
    (hE_stable i s7 (by rw [e7H]; omega)) (by rw [e7M]; omega)
  refine ⟨s8, (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq (g7.seq g8))))))).mono ?_,
    ?_, ?_, ?_⟩
  · simp only [hE, rv, Ex.size]; nlinarith
  · have eff17 : EdgeEff s1 s7 [] := by
      refine EdgeEff.of_frame ?_ ?_ ?_ ?_
      · rw [k7]; simp +decide [s6, s5, s4, k3, s2]
      · rw [fr7 _ (by decide) (by decide)]
        simp only [s6, s5, s4, NSt.set_env, Function.update_of_ne (show r4M ≠ rc6 by decide),
          Function.update_of_ne (show r4M ≠ rc7 by decide),
          Function.update_of_ne (show r4M ≠ rc8 by decide)]
        rw [fr3 _ (by decide) (by decide)]
        simp +decide [s2]
      · rw [p7]; simp +decide [s6, s5, s4, p3, s2]
      · rw [o7]; simp +decide [s6, s5, s4, o3, s2]
    have := (eff1.trans eff17).trans eff8
    simpa [junE1, hE_eval, e7H, eH, eSP, rv, Ex.eval] using this
  · rw [fr8 _ (by decide)]; exact hv7
  · intro r hr
    simp only [labW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [fr8 r hr.2.2.2.2.2.1, fr7 r hr.2.2.2.1 hr.2.2.2.2.1]
    exact e6 r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1

end Lax119563Proofs.Compiler
