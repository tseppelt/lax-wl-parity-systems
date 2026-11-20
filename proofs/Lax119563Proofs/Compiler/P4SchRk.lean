import Lax119563Proofs.Compiler.P4SchEnt

/-!
# Pass `P4`, schema part: the rank loop of section 2

`EE st st' Es`: the edge stack and count of `st'` are those of `st` with `Es` pushed (other
stacks not described). `p4Rks`: for one `q`, pop the rank codes `cs` of a column from `qRkF`
(up to the terminator `0`), saving them on `qOrsB`, and emit the entries `t0, t0 + 1, …`
(`p4Rks_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Edge effects on the edge stack only -/

/-- The edge stack and the edge count of `st'` are those of `st` with `Es` pushed; cursor and
output kept. -/
def EE (st st' : NSt CR CQ) (Es : List (ℕ × ℕ)) : Prop :=
  st'.stk q4E = pairsRev Es ++ st.stk q4E ∧ st'.env r4M = st.env r4M + Es.length ∧
    st'.pos = st.pos ∧ st'.out = st.out

lemma EE.trans {st s₁ s₂ : NSt CR CQ} {E₁ E₂ : List (ℕ × ℕ)} (h₁ : EE st s₁ E₁)
    (h₂ : EE s₁ s₂ E₂) : EE st s₂ (E₁ ++ E₂) := by
  obtain ⟨a1, b1, c1, d1⟩ := h₁
  obtain ⟨a2, b2, c2, d2⟩ := h₂
  refine ⟨?_, ?_, c2.trans c1, d2.trans d1⟩
  · rw [a2, a1, pairsRev_append]; simp
  · rw [b2, b1, List.length_append]; ring

lemma EE.refl (st : NSt CR CQ) : EE st st [] := ⟨by simp [pairsRev], by simp, rfl, rfl⟩

lemma EE.of_frame {st st' : NSt CR CQ} (hs : st'.stk q4E = st.stk q4E)
    (hm : st'.env r4M = st.env r4M) (hp : st'.pos = st.pos) (ho : st'.out = st.out) :
    EE st st' [] := ⟨by simp [pairsRev, hs], by simp [hm], hp, ho⟩

lemma EdgeEff.ee {st st' : NSt CR CQ} {Es : List (ℕ × ℕ)} (h : EdgeEff st st' Es) :
    EE st st' Es := ⟨by rw [h.1]; simp, h.2.1, h.2.2.1, h.2.2.2⟩

lemma EdgeEff.stk_ne {st st' : NSt CR CQ} {Es : List (ℕ × ℕ)} (h : EdgeEff st st' Es) {q : Fin CQ}
    (hq : q ≠ q4E) : st'.stk q = st.stk q := by rw [h.1, Function.update_of_ne hq]

lemma length_updL (H PP TP cp : ℕ) : (updL H PP TP cp).length = 12 := by
  simp [updL, range4_flatMap, updE1]

lemma length_updFL_le (H TP cp LB o m : ℕ) : (updFL H TP cp LB o m).length ≤ 12 := by
  rw [updFL, range4_flatMap]
  simp only [List.length_append]
  have := length_updF1 (H + 0) TP cp (cposN LB o m (0 / 2)) (0 / 2) (0 % 2)
  have := length_updF1 (H + 1) TP cp (cposN LB o m (1 / 2)) (1 / 2) (1 % 2)
  have := length_updF1 (H + 2) TP cp (cposN LB o m (2 / 2)) (2 / 2) (2 % 2)
  have := length_updF1 (H + 3) TP cp (cposN LB o m (3 / 2)) (3 / 2) (3 % 2)
  omega

lemma length_entE_le (T t Hc TPc SP cp LB oU mU : ℕ) :
    (entE T t Hc TPc SP cp LB oU mU).length ≤ 12 := by
  unfold entE; split_ifs <;> first | exact length_updFL_le _ _ _ _ _ _ | simp [length_updL]

/-! ## The rank loop -/

/-- The body of the rank loop. -/
def p4RkB : CStm CR CQ := .seq (.push qOrsB (rv rc5)) (.seq p4Ent (.pop qRkF rc5))

/-- The rank loop for one `q`. -/
def p4Rks : CStm CR CQ := .seq (.pop qRkF rc5) (.loop (rv rc5) p4RkB)

/-- The entries `t0 + p` for the codes `cs` (index `p`). -/
def rksE (T t0 Hc TPc SP QR LB oU mU : ℕ) (cs : List ℕ) : List (ℕ × ℕ) :=
  cs.zipIdx.flatMap fun q => entE T (t0 + q.2) Hc TPc SP (QR + 2 * (q.1 / 2)) LB oU mU

lemma rksE_take_succ (T t0 Hc TPc SP QR LB oU mU : ℕ) (cs : List ℕ) {p : ℕ} (hp : p < cs.length) :
    rksE T t0 Hc TPc SP QR LB oU mU (cs.take (p + 1)) =
      rksE T t0 Hc TPc SP QR LB oU mU (cs.take p) ++
        entE T (t0 + p) Hc TPc SP (QR + 2 * (cs[p] / 2)) LB oU mU := by
  simp only [rksE, List.take_add_one, List.getElem?_eq_getElem hp, Option.toList_some,
    List.zipIdx_append, List.flatMap_append]
  simp [List.length_take, min_eq_left hp.le]

lemma length_rksE_le (T t0 Hc TPc SP QR LB oU mU : ℕ) :
    ∀ cs : List ℕ, (rksE T t0 Hc TPc SP QR LB oU mU cs).length ≤ 12 * cs.length := by
  intro cs
  rw [rksE, List.length_flatMap]
  calc (cs.zipIdx.map fun q => (entE T (t0 + q.2) Hc TPc SP (QR + 2 * (q.1 / 2)) LB oU mU).length).sum
      ≤ (cs.zipIdx.map fun _ => 12).sum := List.sum_le_sum (fun q _ => length_entE_le ..)
    _ = 12 * cs.length := by simp [List.sum_replicate, mul_comm]

/-- The state of the rank loop after `p` entries. -/
def rkInv (w T t0 Hc TPc SP QR LB oU mU : ℕ) (cs rest : List ℕ) (s0 : NSt CR CQ) (p : ℕ)
    (s : NSt CR CQ) : Prop :=
  EE s0 s (rksE T t0 Hc TPc SP QR LB oU mU (cs.take p)) ∧
    s.stk qRkF = (cs ++ 0 :: rest).drop (p + 1) ∧ s.stk qOrsB = (cs.take p).reverse ∧
    (∀ q, q ≠ q4E → q ≠ qRkF → q ≠ qOrsB → s.stk q = s0.stk q) ∧
    s.env rc5 = (cs ++ 0 :: rest).getD p 0 ∧
    s.env rc6 = (if t0 + p = 0 then 1 else 0) ∧ (0 < t0 + p → s.env rc7 = TPc + 2 * (t0 + p - 1)) ∧
    s.env r4H = Hc + 4 * (t0 + p) ∧ s.env r4TP = TPc + 2 * (t0 + p) ∧ s.env r4V < 2 ^ w ∧
    ∀ r, r ∉ rc5 :: entW → s.env r = s0.env r

lemma getD_append_cons_lt {cs rest : List ℕ} {p : ℕ} (hp : p < cs.length) :
    (cs ++ 0 :: rest).getD p 0 = cs[p] := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hp]

lemma getD_append_cons_len (cs rest : List ℕ) : (cs ++ 0 :: rest).getD cs.length 0 = 0 := by
  rw [List.getD_eq_getElem _ _ (by simp)]; simp

set_option maxHeartbeats 4000000 in
lemma p4Rks_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s0 : NSt CR CQ)
    {T t0 Hc TPc SP QR LB oU mU : ℕ} (cs rest : List ℕ) (hcs : ∀ X ∈ cs, 1 ≤ X)
    (hR : s0.stk qRkF = cs ++ 0 :: rest) (hB : s0.stk qOrsB = [])
    (eT : s0.env r4Tn = T) (hT : T ≤ 1) (eF : s0.env rc6 = if t0 = 0 then 1 else 0)
    (eP : 0 < t0 → s0.env rc7 = TPc + 2 * (t0 - 1))
    (eSP : s0.env r4SP = SP) (eH : s0.env r4H = Hc + 4 * t0) (eTP : s0.env r4TP = TPc + 2 * t0)
    (eQR : s0.env rc2 = QR) (eLB : s0.env rLB = LB) (eo : s0.env rc3 = oU)
    (em : s0.env rc4 = mU) (hm2 : mU ≤ 2)
    (hH : Hc + 4 * (t0 + cs.length) + 4 < 2 ^ w) (hTP : TPc + 2 * (t0 + cs.length) + 2 < 2 ^ w)
    (hSP : SP + 2 < 2 ^ w) (hQR : ∀ X ∈ cs, QR + X + 2 < 2 ^ w) (hU : LB + oU + 2 < 2 ^ w)
    (hV4 : s0.env r4V < 2 ^ w) (hm : s0.env r4M + 12 * cs.length + 12 < 2 ^ w) :
    ∃ s', Good x w p4Rks s0 s' ((cs.length + 1) * (600 * Ex.nodeCost w)) ∧
      rkInv w T t0 Hc TPc SP QR LB oU mU cs rest s0 cs.length s' := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h1w : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  -- the first pop
  have g0 := CStm.Good.pop (x := x) (w := w) (st := s0) qRkF rc5
  set s1 := (s0.setS qRkF (s0.stk qRkF).tail).set rc5 ((s0.stk qRkF).headD 0)
  have hI0 : rkInv w T t0 Hc TPc SP QR LB oU mU cs rest s0 0 s1 := by
    refine ⟨EE.of_frame (by simp +decide [s1, Function.update_of_ne (show q4E ≠ qRkF by decide)])
      (by simp +decide [s1, Function.update_of_ne (show r4M ≠ rc5 by decide)]) rfl rfl, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp +decide [s1, hR]
    · simp +decide [s1, Function.update_of_ne (show qOrsB ≠ qRkF by decide), hB]
    · intro q h1 h2 h3; simp +decide [s1, Function.update_of_ne h2]
    · simp +decide [s1, hR]; cases cs <;> simp
    · simp +decide [s1, Function.update_of_ne (show rc6 ≠ rc5 by decide), eF]
    · intro h; simp +decide [s1, Function.update_of_ne (show rc7 ≠ rc5 by decide), eP h]
    · simp +decide [s1, Function.update_of_ne (show r4H ≠ rc5 by decide), eH]
    · simp +decide [s1, Function.update_of_ne (show r4TP ≠ rc5 by decide), eTP]
    · simp +decide [s1, Function.update_of_ne (show r4V ≠ rc5 by decide), hV4]
    · intro r hr
      have : r ≠ rc5 := fun h => hr (by simp [h])
      simp +decide [s1, Function.update_of_ne this]
  obtain ⟨s', gl, hI⟩ := CStm.Good.loop_idxC (x := x) (w := w) (e := rv rc5) (body := p4RkB)
    cs.length (rkInv w T t0 Hc TPc SP QR LB oU mU cs rest s0) (520 * Ex.nodeCost w)
    (by
      rintro j hj s ⟨hE, hsR, hsB, hso, h5, h6, h7, hsH, hsTP, hsV, hfr⟩
      rw [getD_append_cons_lt hj] at h5
      have hX1 := hcs _ (List.getElem_mem hj)
      have hXb := hQR _ (List.getElem_mem hj)
      refine ⟨by simp only [rv, Ex.Fits, h5]; omega, by simp only [rv, Ex.eval, h5]; omega, ?_⟩
      have gp := CStm.Good.push (x := x) (w := w) (st := s) (q := qOrsB) (e := rv rc5)
        (by simp only [rv, Ex.Fits, h5]; omega)
      set s2 := s.setS qOrsB ((rv rc5 : Ex CR).eval s.env :: s.stk qOrsB)
      have q2 : ∀ r, s2.env r = s.env r := fun r => rfl
      have hfr' : ∀ r, r ∉ rc5 :: entW → s.env r = s0.env r := hfr
      have hlenE := length_rksE_le T t0 Hc TPc SP QR LB oU mU (cs.take j)
      have hlt : (cs.take j).length = j := by simp; omega
      obtain ⟨s3, g3, eff3, e37, e3TP, e3H, e36, v3, fr3⟩ := p4Ent_good (x := x) hw s2
        (T := T) (t := t0 + j) (Hc := Hc) (TPc := TPc) (SP := SP) (QR := QR) (X := cs[j])
        (LB := LB) (oU := oU) (mU := mU)
        (by rw [q2, hfr' _ (by decide), eT]) hT (by rw [q2, h6]) (fun h => by rw [q2, h7 h])
        (by rw [q2, hfr' _ (by decide), eSP]) (by rw [q2, hsH]) (by rw [q2, hsTP])
        (by rw [q2, hfr' _ (by decide), eQR]) (by rw [q2, h5])
        (by rw [q2, hfr' _ (by decide), eLB]) (by rw [q2, hfr' _ (by decide), eo])
        (by rw [q2, hfr' _ (by decide), em]) hm2 (by omega) (by omega) hSP hXb hU
        (by rw [q2]; exact hsV) (by rw [q2, hE.2.1]; omega)
      have gq := CStm.Good.pop (x := x) (w := w) (st := s3) qRkF rc5
      set s4 := (s3.setS qRkF (s3.stk qRkF).tail).set rc5 ((s3.stk qRkF).headD 0)
      have k3 : ∀ q, q ≠ q4E → s3.stk q = s2.stk q := fun q hq => eff3.stk_ne hq
      refine ⟨s4, (gp.seq (g3.seq gq)).mono ?_, ?_⟩
      · simp only [rv, Ex.size]; nlinarith
      have hdrop : (cs ++ 0 :: rest).drop (j + 1) = (cs ++ 0 :: rest).getD (j + 1) 0 ::
          (cs ++ 0 :: rest).drop (j + 1 + 1) := by
        rw [List.getD_eq_getElem _ _ (by simp; omega)]
        exact List.drop_eq_getElem_cons (by simp; omega)
      have s3R : s3.stk qRkF = (cs ++ 0 :: rest).drop (j + 1) := by
        rw [k3 _ (by decide)]; simp +decide [s2, Function.update_of_ne (show qRkF ≠ qOrsB by decide), hsR]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have ee := hE.trans ((EE.of_frame (st := s) (st' := s2)
          (by simp +decide [s2, Function.update_of_ne (show q4E ≠ qOrsB by decide)]) rfl rfl rfl).trans
          (eff3.ee.trans (EE.of_frame (st := s3) (st' := s4)
            (by simp +decide [s4, Function.update_of_ne (show q4E ≠ qRkF by decide)])
            (by simp +decide [s4, Function.update_of_ne (show r4M ≠ rc5 by decide)]) rfl rfl)))
        rw [rksE_take_succ _ _ _ _ _ _ _ _ _ _ hj]
        simpa [q2, h5] using ee
      · simp only [s4, NSt.set_stk, NSt.setS_stk, Function.update_self, s3R, hdrop,
          List.tail_cons]
      · simp only [s4, NSt.set_stk, NSt.setS_stk, Function.update_of_ne
          (show qOrsB ≠ qRkF by decide), k3 _ (show qOrsB ≠ q4E by decide), s2,
          Function.update_self, hsB, rv, Ex.eval, h5, List.take_add_one,
          List.getElem?_eq_getElem hj, Option.toList_some, List.reverse_append,
          List.reverse_singleton, List.singleton_append]
      · intro q h1 h2 h3
        simp only [s4, NSt.set_stk, NSt.setS_stk, Function.update_of_ne h2, k3 q h1, s2,
          Function.update_of_ne h3]
        exact hso q h1 h2 h3
      · simp +decide [s4, s3R, hdrop]
      · simp +decide [s4, Function.update_of_ne (show rc6 ≠ rc5 by decide), e36]
      · intro _; simp +decide [s4, Function.update_of_ne (show rc7 ≠ rc5 by decide), e37] <;> omega
      · simp +decide [s4, Function.update_of_ne (show r4H ≠ rc5 by decide), e3H]; ring
      · simp +decide [s4, Function.update_of_ne (show r4TP ≠ rc5 by decide), e3TP]; ring
      · simp +decide [s4, Function.update_of_ne (show r4V ≠ rc5 by decide), v3]
      · intro r hr
        have h5' : r ≠ rc5 := fun h => hr (by simp [h])
        have hr' : r ∉ entW := fun h => hr (List.mem_cons_of_mem _ h)
        simp only [s4, NSt.set_env, NSt.setS_env, Function.update_of_ne h5', fr3 r hr', q2]
        exact hfr' r hr)
    (by
      rintro s ⟨-, -, -, -, h5, -⟩
      rw [getD_append_cons_len] at h5
      exact ⟨by simp only [rv, Ex.Fits, h5]; omega, by simp [rv, Ex.eval, h5]⟩)
    s1 hI0
  refine ⟨s', (g0.seq gl).mono ?_, hI⟩
  simp only [condCost, rv, Ex.size]; nlinarith

end Lax119563Proofs.Compiler
