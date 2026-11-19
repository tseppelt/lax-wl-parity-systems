import Lax119563Proofs.Compiler.PReqList

/-!
# Pass `P3`, request generation: one column

`p3Advs` advances the current block of the permutation `π = (f, δ)` to the block `i` of the
column (`qDl2` holds the shifts from the current block on, `qF2` the images after it, `rFi` the
current image; **`p3Advs_good`**); `p3Col` then pushes the request of the column
(**`p3Col_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- Advance by one block. -/
def p3Adv : CStm CR CQ :=
  .seq (moveN qDl2 qJunk rL rI2 rT) (.seq (.pop qF2 rFi) (.set rCur (.add (rv rCur) (.const 1))))

/-- Advance to the block of the column. -/
def p3Advs : CStm CR CQ := .loop (.lt (rv rCur) (rv rGb)) p3Adv

set_option maxHeartbeats 1000000 in
/-- **Advancing the block.** -/
lemma p3Advs_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) {ℓ c i : ℕ}
    (F : List ℕ) (Dl : List (List ℕ)) (hFD : F.length = Dl.length) (hi : i < F.length)
    (hci : c ≤ i) (hDl : ∀ d ∈ Dl, d.length = ℓ ∧ ∀ v ∈ d, v ≤ 1) (hF : ∀ v ∈ F, v < 2 ^ w)
    (hℓw : ℓ + 1 < 2 ^ w) (hiw : i + 1 < 2 ^ w)
    (hC : st.env rCur = c) (hB : st.env rGb = i) (hL : st.env rL = ℓ)
    (hD2 : st.stk qDl2 = (Dl.drop c).flatten) (hF2 : st.stk qF2 = F.drop (c + 1))
    (hFi : st.env rFi = F.getD c 0) :
    ∃ st', Good x w p3Advs st st' ((i - c + 1) * ((ℓ + 3) * (12 * Ex.nodeCost w))) ∧
      st'.env rCur = i ∧ st'.env rFi = F.getD i 0 ∧
      st'.stk qDl2 = (Dl.drop i).flatten ∧ st'.stk qF2 = F.drop (i + 1) ∧
      (∀ q, q ≠ qDl2 → q ≠ qF2 → q ≠ qJunk → st'.stk q = st.stk q) ∧
      st'.pos = st.pos ∧ st'.out = st.out ∧
      ∀ r, wReg r p3Advs = false → st'.env r = st.env r := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set Inv : NSt CR CQ → Prop := fun s => c ≤ s.env rCur ∧ s.env rCur ≤ i ∧ s.env rGb = i ∧
    s.env rL = ℓ ∧ s.stk qDl2 = (Dl.drop (s.env rCur)).flatten ∧
    s.stk qF2 = F.drop (s.env rCur + 1) ∧ s.env rFi = F.getD (s.env rCur) 0 ∧
    (∀ q, q ≠ qDl2 → q ≠ qF2 → q ≠ qJunk → s.stk q = st.stk q) ∧ s.pos = st.pos ∧
    s.out = st.out ∧ ∀ r, wReg r p3Advs = false → s.env r = st.env r with hInv
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv rCur) (rv rGb)) (body := p3Adv)
    Inv (fun s => i - s.env rCur) (fun _ => 0) 0 ((ℓ + 2) * (12 * Ex.nodeCost w)) (by
      intro s ⟨hc1, hc2, hb, hl, hd, hf, hfi, hS, hp, ho, he⟩
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hcond
      have hlt : s.env rCur < i := by simpa [rv, Ex.eval, hb] using hcond
      set m := s.env rCur with hm
      have hmD : m < Dl.length := by omega
      have hdm : Dl.drop m = Dl[m] :: Dl.drop (m + 1) := List.drop_eq_getElem_cons hmD
      have hfm : F.drop (m + 1) = F[m + 1] :: F.drop (m + 2) :=
        List.drop_eq_getElem_cons (by omega)
      obtain ⟨hlm, hbm⟩ := hDl _ (List.getElem_mem hmD)
      obtain ⟨s1, r1, hs1, hf1⟩ := moveN_good (x := x) (w := w) (src := qDl2) (dst := qJunk)
        (cnt := rL) (i := rI2) (t := rT) (by decide) (by decide) (by decide) (by decide) s hl
        (by rw [hd, hdm, List.flatten_cons, List.length_append, hlm]; omega) hℓw (by
          rw [hd, hdm, List.flatten_cons, List.take_append_of_le_length (by omega),
            List.take_of_length_le (by omega)]
          intro v hv; have := hbm v hv
          have : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
          omega)
      have e1F : s1.stk qF2 = F[m + 1] :: F.drop (m + 2) := by
        rw [hs1, movedStk_other _ (by decide) (by decide), hf, hfm]
      have r2 := Good.pop_cons (x := x) (w := w) (r := rFi) e1F
      set s2 := (s1.setS qF2 (F.drop (m + 2))).set rFi F[m + 1]
      have e1 : ∀ r, r ≠ rI2 → r ≠ rT → s1.env r = s.env r := fun r h1 h2 =>
        hf1.2.2 r (by simp [h1, h2])
      have e2C : s2.env rCur = m := by
        simp only [s2, NSt.set_env, NSt.setS_env, Function.update_of_ne (show rCur ≠ rFi by decide)]
        exact e1 _ (by decide) (by decide)
      have r3 := Good.set (x := x) (w := w) (r := rCur) (e := .add (rv rCur) (.const 1)) (st := s2)
        (by simp only [Ex.Fits, Ex.eval, rv, e2C]; omega)
      have hall := r1.seq (r2.seq r3)
      have hev : ∀ r, wReg r p3Adv = false → (s2.set rCur (Ex.eval s2.env
          (.add (rv rCur) (.const 1)))).env r = s.env r := fun r hr => hall.env_of hr
      have e3C : (s2.set rCur (Ex.eval s2.env (.add (rv rCur) (.const 1)))).env rCur = m + 1 := by
        simp [Ex.eval, rv, e2C]
      refine ⟨_, hall.mono ?_, ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega,
        le_rfl⟩
      · simp only [rv, Ex.size]; nlinarith
      · rw [hev _ (by decide), hb]
      · rw [hev _ (by decide), hl]
      · rw [e3C]
        simp only [NSt.set_stk, s2, NSt.setS_stk, Function.update_of_ne (show qDl2 ≠ qF2 by decide)]
        rw [hs1, movedStk_src _ (by decide), hd, hdm, List.flatten_cons,
          List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega)]
        rfl
      · rw [e3C]; simp [s2]
      · rw [e3C]
        simp only [NSt.set_env, s2, NSt.setS_env, Function.update_of_ne (show rFi ≠ rCur by decide),
          Function.update_self]
        rw [List.getD_eq_getElem _ _ (by omega)]
      · intro q n1 n2 n3
        simp only [NSt.set_stk, s2, NSt.setS_stk, Function.update_of_ne n2]
        rw [hs1, movedStk_other _ n1 n3, hS q n1 n2 n3]
      · simp only [NSt.set_pos, s2, NSt.setS_pos]; rw [hf1.1, hp]
      · simp only [NSt.set_out, s2, NSt.setS_out]; rw [hf1.2.1, ho]
      · intro r hr; rw [hev r (by simpa [p3Advs, wReg] using hr), he r hr])
    st ⟨by omega, by omega, hB, hL, by rw [hC, hD2], by rw [hC, hF2], by rw [hC, hFi],
      fun _ _ _ _ => rfl, rfl, rfl, fun _ _ => rfl⟩
  obtain ⟨s', r', ⟨hc1, hc2, hb, -, hd, hf, hfi, hS, hp, ho, he⟩, hc⟩ := hloop
  have hci' : s'.env rCur = i := by
    simp only [Ex.eval, rv, hb] at hc; split_ifs at hc with h <;> omega
  refine ⟨s', r'.mono ?_, hci', by rw [hfi, hci'], by rw [hd, hci'], by rw [hf, hci'], hS, hp, ho,
    he⟩
  rw [hC]
  simp only [condCost, rv, Ex.size, mul_zero, zero_add]
  have : i - c + 1 ≥ 1 := by omega
  nlinarith

/-! ## The stacks of the bit loop -/

section bitsStk
variable (S : Fin CQ → List ℕ) (j : ℕ)
lemma bitsStk_dom2 : bitsStk S j qDom2 = (S qDom2).drop j := by simp [bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide)]
lemma bitsStk_dom : bitsStk S j qDom = ((S qDom2).take j).reverse ++ S qDom := by
  simp [bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide)]
lemma bitsStk_dl2 : bitsStk S j qDl2 = (S qDl2).drop j := by simp [bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide)]
lemma bitsStk_aux : bitsStk S j qAux = ((S qDl2).take j).reverse ++ S qAux := by
  simp [bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide)]
lemma bitsStk_rec : bitsStk S j qRec =
    (xorL ((S qDom2).take j) ((S qDl2).take j)).reverse ++ S qRec := by simp [bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide)]
lemma bitsStk_other {q : Fin CQ} (h1 : q ≠ qDom2) (h2 : q ≠ qDom) (h3 : q ≠ qDl2) (h4 : q ≠ qAux)
    (h5 : q ≠ qRec) : bitsStk S j q = S q := by
  simp [bitsStk, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
    Function.update_of_ne h4, Function.update_of_ne h5]
end bitsStk

/-- One column: push its request. -/
def p3Col : CStm CR CQ :=
  .seq (.pop qDom2 rGb) (.seq (.push qDom (rv rGb)) (.seq p3Advs (.seq (.push qRec (rv rU))
    (.seq (.push qRec (rv rFi)) (.seq p3Bits (.seq (moveN qAux qDl2 rL rI2 rT)
      (.seq (.push qRec (.const 1)) (.seq (.push qRec (rv rSq)) (.seq (.push qRec (.const 0))
        (.seq (.push qRec (.const 0)) (.seq (.set rSq (.add (rv rSq) (rv rStr)))
          (.set rK (.add (rv rK) (.const 1))))))))))))))

lemma Good.push_val {x : List Bool} {w : ℕ} {st : NSt CR CQ} {q : Fin CQ} {e : Ex CR} {v : ℕ}
    (hv : e.eval st.env = v) (h : e.Fits w st.env) :
    Good x w (.push q e : CStm CR CQ) st (st.setS q (v :: st.stk q))
      (e.size * Ex.nodeCost w + unitCost w) := by
  rw [← hv]; exact Good.push h

set_option maxHeartbeats 4000000 in
/-- **One column.** -/
lemma p3Col_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) {ℓ cur i u sq str : ℕ}
    (bs R : List ℕ) (hbs : bs.length = ℓ) (hbsb : ∀ v ∈ bs, v ≤ 1)
    (F : List ℕ) (Dl : List (List ℕ)) (hFD : F.length = Dl.length) (hi : i < F.length)
    (hci : cur ≤ i) (hDl : ∀ d ∈ Dl, d.length = ℓ ∧ ∀ v ∈ d, v ≤ 1) (hF : ∀ v ∈ F, v < 2 ^ w)
    (hℓw : ℓ + 1 < 2 ^ w) (hiw : i + 1 < 2 ^ w) (huw : u < 2 ^ w) (hsw : sq + str < 2 ^ w)
    (hKw : st.env rK + 1 < 2 ^ w)
    (hX2 : st.stk qDom2 = i :: bs ++ R) (hAux : st.stk qAux = [])
    (hC : st.env rCur = cur) (hL : st.env rL = ℓ) (hU : st.env rU = u) (hS : st.env rSq = sq)
    (hT : st.env rStr = str)
    (hD2 : st.stk qDl2 = (Dl.drop cur).flatten) (hF2 : st.stk qF2 = F.drop (cur + 1))
    (hFi : st.env rFi = F.getD cur 0) :
    ∃ st', Good x w p3Col st st' ((i - cur + 1) * ((ℓ + 3) * (12 * Ex.nodeCost w)) +
        (ℓ + 2) * (40 * Ex.nodeCost w)) ∧
      st'.stk qDom2 = R ∧ st'.stk qDom = (i :: bs).reverse ++ st.stk qDom ∧
      st'.stk qDl2 = (Dl.drop i).flatten ∧ st'.stk qF2 = F.drop (i + 1) ∧ st'.stk qAux = [] ∧
      st'.stk qRec = (u :: F.getD i 0 :: xorL bs (Dl.getD i []) ++ [1, sq, 0, 0]).reverse ++
        st.stk qRec ∧
      (∀ q, q ≠ qDom2 → q ≠ qDom → q ≠ qDl2 → q ≠ qF2 → q ≠ qAux → q ≠ qRec → q ≠ qJunk →
        st'.stk q = st.stk q) ∧
      st'.env rCur = i ∧ st'.env rFi = F.getD i 0 ∧ st'.env rSq = sq + str ∧
      st'.env rK = st.env rK + 1 ∧ st'.pos = st.pos ∧ st'.out = st.out ∧
      ∀ r, wReg r p3Col = false → st'.env r = st.env r := by
  have hU0 := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h1w : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hiD : i < Dl.length := by omega
  obtain ⟨hdl, hdb⟩ := hDl _ (List.getElem_mem hiD)
  set d := Dl[i] with hd
  have hdi : Dl.getD i [] = d := List.getD_eq_getElem _ _ hiD
  have hFiw : F.getD i 0 < 2 ^ w := by
    rw [List.getD_eq_getElem _ _ hi]; exact hF _ (List.getElem_mem hi)
  have hdrop : (Dl.drop i).flatten = d ++ (Dl.drop (i + 1)).flatten := by
    rw [List.drop_eq_getElem_cons hiD, List.flatten_cons]
  -- pop the block, save it
  have r1 := Good.pop_cons (x := x) (w := w) (r := rGb) hX2
  set s1 := (st.setS qDom2 (bs ++ R)).set rGb i
  have r2 := Good.push_val (x := x) (w := w) (q := qDom) (e := rv rGb) (st := s1) (v := i)
    (by simp [s1, rv, Ex.eval])
    (by simp only [Ex.Fits, rv, s1, NSt.set_env, Function.update_self]; omega)
  set s2 := s1.setS qDom (i :: s1.stk qDom)
  have e2 : ∀ r, r ≠ rGb → s2.env r = st.env r := fun r h => by
    simp [s2, s1, Function.update_of_ne h]
  -- advance
  obtain ⟨s3, r3, h3C, h3Fi, h3D, h3F, h3S, h3p, h3o, h3e⟩ := p3Advs_good (x := x) hw s2 F Dl
    hFD hi hci hDl hF hℓw hiw (by rw [e2 _ (by decide), hC]) (by simp [s2, s1])
    (by rw [e2 _ (by decide), hL]) (by simp only [s2, s1, NSt.setS_stk, NSt.set_stk, Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qF2 by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qF2 by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qF2 by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qF2 ≠ qDom2 by decide), Function.update_of_ne (show qF2 ≠ qDom by decide), Function.update_of_ne (show qF2 ≠ qDl2 by decide), Function.update_of_ne (show qF2 ≠ qAux by decide), Function.update_of_ne (show qF2 ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qF2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qF2 by decide), Function.update_of_ne (show qRec ≠ qAux by decide)]; exact hD2)
    (by simp only [s2, s1, NSt.setS_stk, NSt.set_stk, Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qF2 by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qF2 by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qF2 by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qF2 ≠ qDom2 by decide), Function.update_of_ne (show qF2 ≠ qDom by decide), Function.update_of_ne (show qF2 ≠ qDl2 by decide), Function.update_of_ne (show qF2 ≠ qAux by decide), Function.update_of_ne (show qF2 ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qF2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qF2 by decide), Function.update_of_ne (show qRec ≠ qAux by decide)]; exact hF2)
    (by rw [e2 _ (by decide), hFi])
  have e3 : ∀ r, r ≠ rGb → wReg r p3Advs = false → s3.env r = st.env r := fun r h h' => by
    rw [h3e r h', e2 r h]
  -- push `u` and `f(i)`
  have r4 := Good.push_val (x := x) (w := w) (q := qRec) (e := rv rU) (st := s3) (v := u)
    (by simp only [rv, Ex.eval]; rw [e3 _ (by decide) (by decide), hU])
    (by simp only [Ex.Fits, rv]; rw [e3 _ (by decide) (by decide), hU]; exact huw)
  set s4 := s3.setS qRec (u :: s3.stk qRec)
  have r5 := Good.push_val (x := x) (w := w) (q := qRec) (e := rv rFi) (st := s4)
    (v := F.getD i 0) (by simp [s4, rv, Ex.eval, h3Fi])
    (by simp only [Ex.Fits, rv, s4, NSt.setS_env, h3Fi]; exact hFiw)
  set s5 := s4.setS qRec (F.getD i 0 :: s4.stk qRec)
  have h5D2 : s5.stk qDom2 = bs ++ R := by
    simp only [s5, s4, NSt.setS_stk, Function.update_of_ne (show qDom2 ≠ qRec by decide)]
    rw [h3S _ (by decide) (by decide) (by decide)]
    simp only [s2, s1, NSt.setS_stk, NSt.set_stk, Function.update_self, Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qF2 by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qF2 by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qF2 by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qF2 ≠ qDom2 by decide), Function.update_of_ne (show qF2 ≠ qDom by decide), Function.update_of_ne (show qF2 ≠ qDl2 by decide), Function.update_of_ne (show qF2 ≠ qAux by decide), Function.update_of_ne (show qF2 ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qF2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qF2 by decide), Function.update_of_ne (show qRec ≠ qAux by decide)]
  have h5Dl : s5.stk qDl2 = d ++ (Dl.drop (i + 1)).flatten := by
    simp only [s5, s4, NSt.setS_stk, Function.update_of_ne (show qDl2 ≠ qRec by decide)]
    rw [h3D, hdrop]
  have h5L : s5.env rL = ℓ := by
    show s3.env rL = ℓ; rw [e3 _ (by decide) (by decide), hL]
  -- the bits
  obtain ⟨s6, r6, h6S, h6p, h6o, h6e⟩ := p3Bits_good (x := x) hw s5 h5L
    (by rw [h5D2]; simp [hbs]) (by rw [h5Dl]; simp [hdl])
    (by rw [h5D2, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        exact hbsb)
    (by rw [h5Dl, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        exact hdb) hℓw
  have htb : (s5.stk qDom2).take ℓ = bs := by
    rw [h5D2, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have htd : (s5.stk qDl2).take ℓ = d := by
    rw [h5Dl, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have h6Aux : s6.stk qAux = d.reverse := by
    rw [h6S, bitsStk_aux, htd]
    simp only [s5, s4, NSt.setS_stk, Function.update_of_ne (show qAux ≠ qRec by decide)]
    rw [h3S _ (by decide) (by decide) (by decide)]
    simp only [s2, s1, NSt.setS_stk, NSt.set_stk, Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qF2 by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qF2 by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qF2 by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qF2 ≠ qDom2 by decide), Function.update_of_ne (show qF2 ≠ qDom by decide), Function.update_of_ne (show qF2 ≠ qDl2 by decide), Function.update_of_ne (show qF2 ≠ qAux by decide), Function.update_of_ne (show qF2 ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qF2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qF2 by decide), Function.update_of_ne (show qRec ≠ qAux by decide)]; rw [hAux]; simp
  have h6L : s6.env rL = ℓ := by rw [h6e _ (by decide), h5L]
  -- restore the shift
  obtain ⟨s7, r7, h7S, h7f⟩ := moveN_good (x := x) (w := w) (src := qAux) (dst := qDl2)
    (cnt := rL) (i := rI2) (t := rT) (by decide) (by decide) (by decide) (by decide) s6 h6L
    (by rw [h6Aux]; simp [hdl]) hℓw (by
      rw [h6Aux, List.take_of_length_le (by simp [hdl])]
      intro v hv; have := hdb v (List.mem_reverse.mp hv); omega)
  have hall7 := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  have hSq7 : s7.env rSq = sq := by rw [hall7.env_of (by decide), hS]
  have hK7 : s7.env rK = st.env rK := hall7.env_of (by decide)
  have hT7 : s7.env rStr = str := by rw [hall7.env_of (by decide), hT]
  have h7C : s7.env rCur = i := by
    rw [h7f.2.2 _ (by decide), h6e _ (by decide)]; exact h3C
  have h7Fi : s7.env rFi = F.getD i 0 := by
    rw [h7f.2.2 _ (by decide), h6e _ (by decide)]; exact h3Fi
  -- the tail of the request
  have r8 := Good.push_val (x := x) (w := w) (q := qRec) (e := .const 1) (st := s7) (v := 1)
    rfl (by simp only [Ex.Fits]; omega)
  set s8 := s7.setS qRec (1 :: s7.stk qRec)
  have r9 := Good.push_val (x := x) (w := w) (q := qRec) (e := rv rSq) (st := s8) (v := sq)
    (by simp [s8, rv, Ex.eval, hSq7]) (by simp only [Ex.Fits, rv, s8, NSt.setS_env, hSq7]; omega)
  set s9 := s8.setS qRec (sq :: s8.stk qRec)
  have r10 := Good.push_val (x := x) (w := w) (q := qRec) (e := .const 0) (st := s9) (v := 0)
    rfl (by simp only [Ex.Fits]; omega)
  set s10 := s9.setS qRec (0 :: s9.stk qRec)
  have r11 := Good.push_val (x := x) (w := w) (q := qRec) (e := .const 0) (st := s10) (v := 0)
    rfl (by simp only [Ex.Fits]; omega)
  set s11 := s10.setS qRec (0 :: s10.stk qRec)
  have r12 := Good.set (x := x) (w := w) (r := rSq) (e := .add (rv rSq) (rv rStr)) (st := s11)
    (by simp only [Ex.Fits, rv, Ex.eval, s11, s10, s9, s8, NSt.setS_env, hSq7, hT7]; omega)
  set s12 := s11.set rSq (Ex.eval s11.env (.add (rv rSq) (rv rStr)))
  have r13 := Good.set (x := x) (w := w) (r := rK) (e := .add (rv rK) (.const 1)) (st := s12)
    (by simp only [Ex.Fits, rv, Ex.eval, s12, s11, s10, s9, s8, NSt.setS_env, NSt.set_env,
          Function.update_of_ne (show rK ≠ rSq by decide), hK7]; omega)
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq
    (r11.seq (r12.seq r13)))))))))))
  have h11 : ∀ q, q ≠ qRec → s11.stk q = s7.stk q := fun q h => by
    simp [s11, s10, s9, s8, Function.update_of_ne h]
  have h7o : ∀ q, q ≠ qAux → q ≠ qDl2 → s7.stk q = s6.stk q := fun q h1 h2 => by
    rw [h7S, movedStk_other _ h1 h2]
  refine ⟨_, hall.mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr => hall.env_of hr⟩
  · simp only [Ex.size, rv]; nlinarith
  · show s11.stk qDom2 = _; rw [h11 _ (by decide), h7o _ (by decide) (by decide), h6S,
      bitsStk_dom2, h5D2, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega)]; rfl
  · show s11.stk qDom = _; rw [h11 _ (by decide), h7o _ (by decide) (by decide), h6S,
      bitsStk_dom, htb]
    simp only [s5, s4, NSt.setS_stk, Function.update_of_ne (show qDom ≠ qRec by decide)]
    rw [h3S _ (by decide) (by decide) (by decide)]; simp [s2, s1, Function.update_of_ne (show qDom ≠ qDom2 by decide)]
  · show s11.stk qDl2 = _; rw [h11 _ (by decide), h7S, movedStk_dst, h6Aux,
      List.take_of_length_le (by simp [hdl]), List.reverse_reverse, h6S, bitsStk_dl2, h5Dl,
      List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), hdrop]; rfl
  · show s11.stk qF2 = _; rw [h11 _ (by decide), h7o _ (by decide) (by decide), h6S,
      bitsStk_other _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s5, s4, NSt.setS_stk, Function.update_of_ne (show qF2 ≠ qRec by decide)]
    exact h3F
  · show s11.stk qAux = _; rw [h11 _ (by decide), h7S, movedStk_src _ (by decide), h6Aux]
    simp [hdl]
  · show s11.stk qRec = _
    simp only [s11, s10, s9, s8, NSt.setS_stk, Function.update_self]
    rw [h7o _ (by decide) (by decide), h6S, bitsStk_rec, htb, htd]
    simp only [s5, s4, NSt.setS_stk, Function.update_self]
    rw [h3S _ (by decide) (by decide) (by decide), hdi]
    simp [s2, s1, Function.update_of_ne (show qRec ≠ qDom2 by decide),
      Function.update_of_ne (show qRec ≠ qDom by decide)]
  · intro q n1 n2 n3 n4 n5 n6 n7
    show s11.stk q = _; rw [h11 _ n6, h7o _ n5 n3, h6S, bitsStk_other _ _ n1 n2 n3 n5 n6]
    simp only [s5, s4, NSt.setS_stk, Function.update_of_ne n6]
    rw [h3S _ n3 n4 n7]; simp [s2, s1, Function.update_of_ne n1, Function.update_of_ne n2]
  · simp [s12, s11, s10, s9, s8, Function.update_of_ne (show rCur ≠ rK by decide),
      Function.update_of_ne (show rCur ≠ rSq by decide), h7C]
  · simp [s12, s11, s10, s9, s8, Function.update_of_ne (show rFi ≠ rK by decide),
      Function.update_of_ne (show rFi ≠ rSq by decide), h7Fi]
  · simp [s12, s11, s10, s9, s8, Function.update_of_ne (show rSq ≠ rK by decide), Ex.eval, rv,
      hSq7, hT7]
  · simp [s12, s11, s10, s9, s8, Function.update_of_ne (show rK ≠ rSq by decide), Ex.eval, rv,
      hK7]
  · simp only [NSt.set_pos, s12, s11, s10, s9, s8, NSt.setS_pos]
    rw [h7f.1, h6p]; simp only [s5, s4, NSt.setS_pos]; rw [h3p]; rfl
  · simp only [NSt.set_out, s12, s11, s10, s9, s8, NSt.setS_out]
    rw [h7f.2.1, h6o]; simp only [s5, s4, NSt.setS_out]; rw [h3o]; rfl

end Lax119563Proofs.Compiler
