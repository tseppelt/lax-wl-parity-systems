import Lax119563Proofs.Compiler.P4SchLab2

/-!
# Pass `P4`, schema part: whole hubs and answers

* `pAns o m`: pop one answer `[s, off, labs, seed]` from `qAns` (pushed on `qA2` for
  restoring), `o := off`, `m := ansMode ε` (`pAns_good`);
* `jLabs` (`junL`), `lLabs` (`lnkL`), `uLabs` (`updL`), `fLabs` (`updFL`): the four (two)
  labels of a hub.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Answers -/

/-- Pop a word of `qAns` into `r` and save it on `qA2`. -/
def pp (r : Fin CR) : CStm CR CQ := .seq (.pop qAns r) (.push qA2 (rv r))

lemma pp_good {w : ℕ} {x : List Bool} (r : Fin CR) (s : NSt CR CQ) {v : ℕ} {L : List ℕ}
    (hA : s.stk qAns = v :: L) (hv : v < 2 ^ w) :
    ∃ s', Good x w (pp r) s s' (5 * Ex.nodeCost w) ∧ s'.env = Function.update s.env r v ∧
      s'.stk = Function.update (Function.update s.stk qAns L) qA2 (v :: s.stk qA2) ∧
      s'.pos = s.pos ∧ s'.out = s.out := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have g1 := Good.pop (x := x) (w := w) (st := s) qAns r
  have g2 := Good.push (x := x) (w := w) (st := (s.setS qAns (s.stk qAns).tail).set r
    ((s.stk qAns).headD 0)) (q := qA2) (e := rv r) (by simp [rv, Ex.Fits, hA, hv])
  refine ⟨_, (g1.seq g2).mono ?_, ?_, ?_, rfl, rfl⟩
  · simp only [rv, Ex.size]; omega
  · simp [hA]
  · funext q
    simp only [NSt.setS_stk, NSt.set_stk, rv, Ex.eval, NSt.set_env, Function.update_self, hA,
      List.headD_cons, List.tail_cons]
    by_cases h : q = qA2
    · subst h; simp [Function.update_of_ne (show qA2 ≠ qAns by decide)]
    · simp [Function.update_of_ne h]

/-- The mode of the answer (labels `rc7`, seed `rc8`) into `m`. -/
def modeS (m : Fin CR) : CStm CR CQ :=
  .ite (.lt (rv rc7) (.const 2)) (.ite (rv r4Eps) (.set m (rv rc8)) (.set m (.const 0)))
    (.set m (.const 2))

lemma modeS_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (m : Fin CR) (s : NSt CR CQ)
    {sq off labs sd : ℕ} (e7 : s.env rc7 = labs) (e8 : s.env rc8 = sd)
    (hlabs : labs = 1 ∨ labs = 2) (hsd : sd ≤ 1) (hE : s.env r4Eps ≤ 1) :
    Good x w (modeS m) s (s.set m (ansMode (s.env r4Eps) [sq, off, labs, sd]))
      (10 * Ex.nodeCost w) := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hF : (Ex.lt (rv rc7) (.const 2) : Ex CR).Fits w s.env := by
    simp only [Ex.Fits, rv, e7]; omega
  have hFE : (rv r4Eps : Ex CR).Fits w s.env := by simp only [Ex.Fits, rv]; omega
  unfold ansMode
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rcases hlabs with rfl | rfl
  · rw [if_pos rfl]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hE with h | h
    · refine ((CStm.Good.iteT hF (by simp [Ex.eval, rv, e7]) (CStm.Good.iteF hFE (by simp [rv, Ex.eval, h])
        (Good.set (r := m) (e := .const 0) (by simp only [Ex.Fits]; omega)))).of_eq
        (by simp [h, Ex.eval]) ?_)
      simp only [condCost, rv, Ex.size]; nlinarith
    · refine ((CStm.Good.iteT hF (by simp [Ex.eval, rv, e7]) (CStm.Good.iteT hFE (by simp [rv, Ex.eval, h])
        (Good.set (r := m) (e := rv rc8) (by simp only [Ex.Fits, rv, e8]; omega)))).of_eq
        (by simp [h, Ex.eval, rv, e8]) ?_)
      simp only [condCost, rv, Ex.size]; nlinarith
  · rw [if_neg (by omega)]
    refine ((CStm.Good.iteF hF (by simp [Ex.eval, rv, e7])
      (Good.set (r := m) (e := .const 2) (by simp only [Ex.Fits]; omega))).of_eq
      (by simp [Ex.eval]) ?_)
    simp only [condCost, rv, Ex.size]; nlinarith

/-- Pop one answer: offset to `o`, mode to `m` (scratch `rc6, rc7, rc8`). -/
def pAns (o m : Fin CR) : CStm CR CQ :=
  .seq (pp rc6) (.seq (pp o) (.seq (pp rc7) (.seq (pp rc8) (modeS m))))

set_option maxHeartbeats 2000000 in
lemma pAns_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) {o m : Fin CR} (ho6 : o ≠ rc6)
    (ho7 : o ≠ rc7) (ho8 : o ≠ rc8) (hm6 : m ≠ rc6) (hm7 : m ≠ rc7) (hm8 : m ≠ rc8) (hom : o ≠ m)
    (hmE : m ≠ r4Eps) (hoE : o ≠ r4Eps) (s : NSt CR CQ) {sq off labs sd : ℕ} {rest : List ℕ}
    (hA : s.stk qAns = [sq, off, labs, sd] ++ rest) (hb : ∀ v ∈ [sq, off, labs, sd], v < 2 ^ w)
    (hlabs : labs = 1 ∨ labs = 2) (hsd : sd ≤ 1) (hE : s.env r4Eps ≤ 1) :
    ∃ s', Good x w (pAns o m) s s' (40 * Ex.nodeCost w) ∧
      s'.stk = Function.update (Function.update s.stk qAns rest) qA2
        ([sd, labs, off, sq] ++ s.stk qA2) ∧
      s'.env o = off ∧ s'.env m = ansMode (s.env r4Eps) [sq, off, labs, sd] ∧
      s'.env m ≤ 2 ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rc6 → r ≠ rc7 → r ≠ rc8 → r ≠ o → r ≠ m → s'.env r = s.env r := by
  have hb' := hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb'
  obtain ⟨b1, b2, b3, b4⟩ := hb'
  have hqq : qA2 ≠ qAns := by decide
  obtain ⟨s1, g1, v1, k1, p1, o1⟩ := pp_good (x := x) (w := w) rc6 s (v := sq)
    (L := off :: labs :: sd :: rest) (by simp [hA]) b1
  obtain ⟨s2, g2, v2, k2, p2, o2⟩ := pp_good (x := x) (w := w) o s1 (v := off)
    (L := labs :: sd :: rest) (by simp +decide [k1]) b2
  obtain ⟨s3, g3, v3, k3, p3, o3⟩ := pp_good (x := x) (w := w) rc7 s2 (v := labs)
    (L := sd :: rest) (by simp +decide [k2]) b3
  obtain ⟨s4, g4, v4, k4, p4, o4⟩ := pp_good (x := x) (w := w) rc8 s3 (v := sd)
    (L := rest) (by simp +decide [k3]) b4
  have e4 : ∀ r, r ≠ rc6 → r ≠ rc7 → r ≠ rc8 → r ≠ o → s4.env r = s.env r := by
    intro r h6 h7 h8 ho
    rw [v4, Function.update_of_ne h8, v3, Function.update_of_ne h7, v2, Function.update_of_ne ho,
      v1, Function.update_of_ne h6]
  have e47 : s4.env rc7 = labs := by
    rw [v4, Function.update_of_ne (by decide), v3, Function.update_self]
  have e48 : s4.env rc8 = sd := by rw [v4, Function.update_self]
  have e4o : s4.env o = off := by
    rw [v4, Function.update_of_ne ho8, v3, Function.update_of_ne ho7, v2, Function.update_self]
  have e4E : s4.env r4Eps = s.env r4Eps := e4 _ (by decide) (by decide) (by decide) hoE.symm
  have g5 := modeS_good (x := x) (sq := sq) (off := off) hw m s4 e47 e48 hlabs hsd
    (by rw [e4E]; exact hE)
  refine ⟨_, (g1.seq (g2.seq (g3.seq (g4.seq g5)))).mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [NSt.set_stk, k4, k3, k2, k1]
    funext q
    by_cases h : q = qA2
    · subst h; simp
    · by_cases h' : q = qAns
      · subst h'; simp +decide
      · simp [Function.update_of_ne h, Function.update_of_ne h']
  · simp [Function.update_of_ne hom, e4o]
  · simp [e4E]
  · simp only [NSt.set_env, Function.update_self, e4E]
    unfold ansMode; split_ifs <;> simp <;> nlinarith
  · simp [p4, p3, p2, p1]
  · simp [o4, o3, o2, o1]
  · intro r h6 h7 h8 ho hm
    simp [Function.update_of_ne hm, e4 r h6 h7 h8 ho]

/-! ## Junction hubs -/

lemma range4_flatMap {α : Type*} (f : ℕ → List α) :
    (List.range 4).flatMap f = f 0 ++ (f 1 ++ (f 2 ++ f 3)) := by
  simp [List.range_succ, List.flatMap_append]

lemma range2_flatMap {α : Type*} (f : ℕ → List α) :
    (List.range 2).flatMap f = f 0 ++ f 1 := by
  simp [List.range_succ, List.flatMap_append]

lemma length_sort2 (o₁ o₂ : Option ℕ) : (sort2 o₁ o₂).length ≤ 2 := by
  unfold sort2; split <;> (try split) <;> simp

lemma length_junE1 (h sp : ℕ) (pu pv : Option ℕ) (a b : ℕ) :
    (junE1 h sp pu pv a b).length ≤ 3 := by
  simp only [junE1, List.length_cons, List.length_map]; have := length_sort2 pu pv; omega

/-- The edges of a junction hub (answers `U`: `oU, mU`; `V`: `oV, mV`). -/
def junL (H SP LB oU mU oV mV : ℕ) : List (ℕ × ℕ) :=
  (List.range 4).flatMap fun i =>
    junE1 (H + i) SP (cposN LB oU mU (i / 2)) (cposN LB oV mV (i % 2)) (i / 2) (i % 2)

lemma length_junL (H SP LB oU mU oV mV : ℕ) : (junL H SP LB oU mU oV mV).length ≤ 12 := by
  rw [junL, range4_flatMap]
  simp only [List.length_append]
  have := length_junE1; linarith [this (H + 0) SP (cposN LB oU mU (0 / 2)) (cposN LB oV mV (0 % 2))
    (0 / 2) (0 % 2), this (H + 1) SP (cposN LB oU mU (1 / 2)) (cposN LB oV mV (1 % 2)) (1 / 2)
    (1 % 2), this (H + 2) SP (cposN LB oU mU (2 / 2)) (cposN LB oV mV (2 % 2)) (2 / 2) (2 % 2),
    this (H + 3) SP (cposN LB oU mU (3 / 2)) (cposN LB oV mV (3 % 2)) (3 / 2) (3 % 2)]

/-- The four junction labels. -/
def jLabs : CStm CR CQ := .seq (jLab 0 0) (.seq (jLab 0 1) (.seq (jLab 1 0) (jLab 1 1)))

set_option maxHeartbeats 2000000 in
lemma jLabs_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w)
    (s : NSt CR CQ) {H SP LB oU mU oV mV : ℕ} (eH : s.env r4H = H) (eSP : s.env r4SP = SP)
    (eLB : s.env rLB = LB) (eoU : s.env rc2 = oU) (emU : s.env rc3 = mU) (eoV : s.env rc4 = oV)
    (emV : s.env rc5 = mV) (hmU : mU ≤ 2) (hmV : mV ≤ 2) (hH : H + 4 < 2 ^ w)
    (hSP : SP + 2 < 2 ^ w) (hU : LB + oU + 2 < 2 ^ w) (hV : LB + oV + 2 < 2 ^ w)
    (hV4 : s.env r4V < 2 ^ w) (hm : s.env r4M + 12 < 2 ^ w) :
    ∃ s', Good x w jLabs s s' (400 * Ex.nodeCost w) ∧
      EdgeEff s s' (junL H SP LB oU mU oV mV) ∧
      s'.env r4V < 2 ^ w ∧ ∀ r, r ∉ labW → s'.env r = s.env r := by
  have L := length_junE1
  obtain ⟨s1, g1, f1, v1, r1⟩ := jLab_good (x := x) hw 0 0 (by norm_num) (by norm_num) s eH eSP
    eLB eoU emU eoV emV hmU hmV hH hSP hU hV hV4 (by omega)
  have q1 : ∀ r, r ∉ labW → s1.env r = s.env r := r1
  obtain ⟨s2, g2, f2, v2, r2⟩ := jLab_good (x := x) hw 0 1 (by norm_num) (by norm_num) s1
    (by rw [q1 _ (by decide), eH]) (by rw [q1 _ (by decide), eSP])
    (by rw [q1 _ (by decide), eLB]) (by rw [q1 _ (by decide), eoU])
    (by rw [q1 _ (by decide), emU]) (by rw [q1 _ (by decide), eoV])
    (by rw [q1 _ (by decide), emV]) hmU hmV hH hSP hU hV v1
    (by rw [f1.2.1]; have := L (H + (2 * 0 + 0)) SP (cposN LB oU mU 0) (cposN LB oV mV 0) 0 0
        omega)
  have q2 : ∀ r, r ∉ labW → s2.env r = s.env r := fun r h => (r2 r h).trans (q1 r h)
  obtain ⟨s3, g3, f3, v3, r3⟩ := jLab_good (x := x) hw 1 0 (by norm_num) (by norm_num) s2
    (by rw [q2 _ (by decide), eH]) (by rw [q2 _ (by decide), eSP])
    (by rw [q2 _ (by decide), eLB]) (by rw [q2 _ (by decide), eoU])
    (by rw [q2 _ (by decide), emU]) (by rw [q2 _ (by decide), eoV])
    (by rw [q2 _ (by decide), emV]) hmU hmV hH hSP hU hV v2
    (by rw [f2.2.1, f1.2.1]
        have := L (H + (2 * 0 + 0)) SP (cposN LB oU mU 0) (cposN LB oV mV 0) 0 0
        have := L (H + (2 * 0 + 1)) SP (cposN LB oU mU 0) (cposN LB oV mV 1) 0 1
        omega)
  have q3 : ∀ r, r ∉ labW → s3.env r = s.env r := fun r h => (r3 r h).trans (q2 r h)
  obtain ⟨s4, g4, f4, v4, r4⟩ := jLab_good (x := x) hw 1 1 (by norm_num) (by norm_num) s3
    (by rw [q3 _ (by decide), eH]) (by rw [q3 _ (by decide), eSP])
    (by rw [q3 _ (by decide), eLB]) (by rw [q3 _ (by decide), eoU])
    (by rw [q3 _ (by decide), emU]) (by rw [q3 _ (by decide), eoV])
    (by rw [q3 _ (by decide), emV]) hmU hmV hH hSP hU hV v3
    (by rw [f3.2.1, f2.2.1, f1.2.1]
        have := L (H + (2 * 0 + 0)) SP (cposN LB oU mU 0) (cposN LB oV mV 0) 0 0
        have := L (H + (2 * 0 + 1)) SP (cposN LB oU mU 0) (cposN LB oV mV 1) 0 1
        have := L (H + (2 * 1 + 0)) SP (cposN LB oU mU 1) (cposN LB oV mV 0) 1 0
        omega)
  refine ⟨s4, (g1.seq (g2.seq (g3.seq g4))).mono (by omega), ?_, v4,
    fun r h => (r4 r h).trans (q3 r h)⟩
  have := f1.trans (f2.trans (f3.trans f4))
  rw [junL, range4_flatMap]
  simpa using this

/-! ## Link hubs -/

/-- The edges of a link hub. -/
def lnkL (H LT LB o m : ℕ) : List (ℕ × ℕ) :=
  (List.range 2).flatMap fun a => lnkE1 (H + a) LT (cposN LB o m a) a

/-- The two link labels. -/
def lLabs : CStm CR CQ := .seq (lLab 0) (lLab 1)

lemma length_lnkE1 (h tp : ℕ) (pw : Option ℕ) (a : ℕ) : (lnkE1 h tp pw a).length ≤ 2 := by
  cases pw <;> simp [lnkE1]

set_option maxHeartbeats 1000000 in
lemma lLabs_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w)
    (s : NSt CR CQ) {H T LT LB o m : ℕ} (eH : s.env r4H = H) (eT : s.env r4Tn = T)
    (eLT : s.env rc1 = LT) (eLB : s.env rLB = LB) (eo : s.env rc2 = o) (em : s.env rc3 = m)
    (hm2 : m ≤ 2) (hH : H + 4 * T + 2 < 2 ^ w) (hLT : LT + 2 < 2 ^ w)
    (hU : LB + o + 2 < 2 ^ w) (hV4 : s.env r4V < 2 ^ w) (hm : s.env r4M + 4 < 2 ^ w) :
    ∃ s', Good x w lLabs s s' (160 * Ex.nodeCost w) ∧
      EdgeEff s s' (lnkL (H + 4 * T) LT LB o m) ∧
      s'.env r4V < 2 ^ w ∧ ∀ r, r ∉ labW → s'.env r = s.env r := by
  obtain ⟨s1, g1, f1, v1, r1⟩ := lLab_good (x := x) hw 0 (by norm_num) s eH eT eLT eLB eo em hm2
    hH hLT hU hV4 (by omega)
  obtain ⟨s2, g2, f2, v2, r2⟩ := lLab_good (x := x) hw 1 (by norm_num) s1
    (by rw [r1 _ (by decide), eH]) (by rw [r1 _ (by decide), eT]) (by rw [r1 _ (by decide), eLT])
    (by rw [r1 _ (by decide), eLB]) (by rw [r1 _ (by decide), eo]) (by rw [r1 _ (by decide), em])
    hm2 hH hLT hU v1
    (by rw [f1.2.1]; have := length_lnkE1 (H + 4 * T + 0) LT (cposN LB o m 0) 0; omega)
  refine ⟨s2, (g1.seq g2).mono (by omega), ?_, v2, fun r h => (r2 r h).trans (r1 r h)⟩
  have := f1.trans f2
  rw [lnkL, range2_flatMap]
  simpa using this

/-! ## Update hubs -/

/-- The edges of an update hub. -/
def updL (H PP TP cp : ℕ) : List (ℕ × ℕ) :=
  (List.range 4).flatMap fun i => updE1 (H + i) PP TP cp (i / 2) (i % 2)

/-- The edges of an update hub at the first entry of a column of a binary schema. -/
def updFL (H TP cp LB o m : ℕ) : List (ℕ × ℕ) :=
  (List.range 4).flatMap fun i => updF1 (H + i) TP cp (cposN LB o m (i / 2)) (i / 2) (i % 2)

/-- The four update labels. -/
def uLabs : CStm CR CQ := .seq (uLab 0 0) (.seq (uLab 0 1) (.seq (uLab 1 0) (uLab 1 1)))

/-- The four update labels at a first entry. -/
def fLabs : CStm CR CQ := .seq (fLab 0 0) (.seq (fLab 0 1) (.seq (fLab 1 0) (fLab 1 1)))

set_option maxHeartbeats 1000000 in
lemma uLabs_good {w : ℕ} {x : List Bool}
    (s : NSt CR CQ) {H PP TP QR X : ℕ} (eH : s.env r4H = H) (ePP : s.env rc8 = PP)
    (eTP : s.env r4TP = TP) (eQR : s.env rc2 = QR) (eX : s.env rc5 = X)
    (hH : H + 4 < 2 ^ w) (hPP : PP + 2 < 2 ^ w) (hTP : TP + 2 < 2 ^ w)
    (hQR : QR + X + 2 < 2 ^ w) (hm : s.env r4M + 12 < 2 ^ w) :
    ∃ s', Good x w uLabs s s' (240 * Ex.nodeCost w) ∧
      EdgeEff s s' (updL H PP TP (QR + 2 * (X / 2))) ∧
      ∀ r, r ≠ r4M → s'.env r = s.env r := by
  obtain ⟨s1, g1, f1, r1⟩ := uLab_good (x := x) 0 0 (by norm_num) (by norm_num) s eH ePP eTP eQR
    eX hH hPP hTP hQR (by omega)
  obtain ⟨s2, g2, f2, r2⟩ := uLab_good (x := x) 0 1 (by norm_num) (by norm_num) s1
    (by rw [r1 _ (by decide), eH]) (by rw [r1 _ (by decide), ePP]) (by rw [r1 _ (by decide), eTP])
    (by rw [r1 _ (by decide), eQR]) (by rw [r1 _ (by decide), eX]) hH hPP hTP hQR
    (by rw [f1.2.1]; simp [updE1]; omega)
  have q2 : ∀ r, r ≠ r4M → s2.env r = s.env r := fun r h => (r2 r h).trans (r1 r h)
  obtain ⟨s3, g3, f3, r3⟩ := uLab_good (x := x) 1 0 (by norm_num) (by norm_num) s2
    (by rw [q2 _ (by decide), eH]) (by rw [q2 _ (by decide), ePP]) (by rw [q2 _ (by decide), eTP])
    (by rw [q2 _ (by decide), eQR]) (by rw [q2 _ (by decide), eX]) hH hPP hTP hQR
    (by rw [f2.2.1, f1.2.1]; simp [updE1]; omega)
  have q3 : ∀ r, r ≠ r4M → s3.env r = s.env r := fun r h => (r3 r h).trans (q2 r h)
  obtain ⟨s4, g4, f4, r4⟩ := uLab_good (x := x) 1 1 (by norm_num) (by norm_num) s3
    (by rw [q3 _ (by decide), eH]) (by rw [q3 _ (by decide), ePP]) (by rw [q3 _ (by decide), eTP])
    (by rw [q3 _ (by decide), eQR]) (by rw [q3 _ (by decide), eX]) hH hPP hTP hQR
    (by rw [f3.2.1, f2.2.1, f1.2.1]; simp [updE1]; omega)
  refine ⟨s4, (g1.seq (g2.seq (g3.seq g4))).mono (by omega), ?_,
    fun r h => (r4 r h).trans (q3 r h)⟩
  have := f1.trans (f2.trans (f3.trans f4))
  rw [updL, range4_flatMap]
  simpa using this

lemma length_updF1 (h tp cp : ℕ) (pu : Option ℕ) (a b : ℕ) : (updF1 h tp cp pu a b).length ≤ 3 := by
  cases pu <;> simp [updF1]

set_option maxHeartbeats 2000000 in
lemma fLabs_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w)
    (s : NSt CR CQ) {H TP QR X LB o m : ℕ} (eH : s.env r4H = H)
    (eTP : s.env r4TP = TP) (eQR : s.env rc2 = QR) (eX : s.env rc5 = X) (eLB : s.env rLB = LB)
    (eo : s.env rc3 = o) (em : s.env rc4 = m) (hm2 : m ≤ 2)
    (hH : H + 4 < 2 ^ w) (hTP : TP + 2 < 2 ^ w)
    (hQR : QR + X + 2 < 2 ^ w) (hU : LB + o + 2 < 2 ^ w) (hV4 : s.env r4V < 2 ^ w)
    (hm : s.env r4M + 12 < 2 ^ w) :
    ∃ s', Good x w fLabs s s' (320 * Ex.nodeCost w) ∧
      EdgeEff s s' (updFL H TP (QR + 2 * (X / 2)) LB o m) ∧
      s'.env r4V < 2 ^ w ∧ ∀ r, r ∉ fW → s'.env r = s.env r := by
  have L := length_updF1
  obtain ⟨s1, g1, f1, v1, r1⟩ := fLab_good (x := x) hw 0 0 (by norm_num) (by norm_num) s eH eTP
    eQR eX eLB eo em hm2 hH hTP hQR hU hV4 (by omega)
  obtain ⟨s2, g2, f2, v2, r2⟩ := fLab_good (x := x) hw 0 1 (by norm_num) (by norm_num) s1
    (by rw [r1 _ (by decide), eH]) (by rw [r1 _ (by decide), eTP]) (by rw [r1 _ (by decide), eQR])
    (by rw [r1 _ (by decide), eX]) (by rw [r1 _ (by decide), eLB]) (by rw [r1 _ (by decide), eo])
    (by rw [r1 _ (by decide), em]) hm2 hH hTP hQR hU v1
    (by rw [f1.2.1]; have := L (H + (2 * 0 + 0)) TP (QR + 2 * (X / 2)) (cposN LB o m 0) 0 0
        omega)
  have q2 : ∀ r, r ∉ fW → s2.env r = s.env r := fun r h => (r2 r h).trans (r1 r h)
  obtain ⟨s3, g3, f3, v3, r3⟩ := fLab_good (x := x) hw 1 0 (by norm_num) (by norm_num) s2
    (by rw [q2 _ (by decide), eH]) (by rw [q2 _ (by decide), eTP]) (by rw [q2 _ (by decide), eQR])
    (by rw [q2 _ (by decide), eX]) (by rw [q2 _ (by decide), eLB]) (by rw [q2 _ (by decide), eo])
    (by rw [q2 _ (by decide), em]) hm2 hH hTP hQR hU v2
    (by rw [f2.2.1, f1.2.1]
        have := L (H + (2 * 0 + 0)) TP (QR + 2 * (X / 2)) (cposN LB o m 0) 0 0
        have := L (H + (2 * 0 + 1)) TP (QR + 2 * (X / 2)) (cposN LB o m 0) 0 1
        omega)
  have q3 : ∀ r, r ∉ fW → s3.env r = s.env r := fun r h => (r3 r h).trans (q2 r h)
  obtain ⟨s4, g4, f4, v4, r4⟩ := fLab_good (x := x) hw 1 1 (by norm_num) (by norm_num) s3
    (by rw [q3 _ (by decide), eH]) (by rw [q3 _ (by decide), eTP]) (by rw [q3 _ (by decide), eQR])
    (by rw [q3 _ (by decide), eX]) (by rw [q3 _ (by decide), eLB]) (by rw [q3 _ (by decide), eo])
    (by rw [q3 _ (by decide), em]) hm2 hH hTP hQR hU v3
    (by rw [f3.2.1, f2.2.1, f1.2.1]
        have := L (H + (2 * 0 + 0)) TP (QR + 2 * (X / 2)) (cposN LB o m 0) 0 0
        have := L (H + (2 * 0 + 1)) TP (QR + 2 * (X / 2)) (cposN LB o m 0) 0 1
        have := L (H + (2 * 1 + 0)) TP (QR + 2 * (X / 2)) (cposN LB o m 1) 1 0
        omega)
  refine ⟨s4, (g1.seq (g2.seq (g3.seq g4))).mono (by omega), ?_, v4,
    fun r h => (r4 r h).trans (q3 r h)⟩
  have := f1.trans (f2.trans (f3.trans f4))
  rw [updFL, range4_flatMap]
  simpa using this

end Lax119563Proofs.Compiler
