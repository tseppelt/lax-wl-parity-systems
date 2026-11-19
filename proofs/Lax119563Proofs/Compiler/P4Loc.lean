import Lax119563Proofs.Compiler.P4Emit
import Lax119563Proofs.Compiler.P4Rep
import Lax119563Proofs.Compiler.PEmitSizes
import Lax119563Proofs.Compiler.PRec

/-!
# Pass `P4` (program): the location sizes

The location loop of `P4` (`p4LLoop`): per location `v` read `ι(v)` and `|D_v|`, push
`labsN v` (`|D_v|` times) on `qSzA`, adding to `rNt`, skip the coordinates
(**`p4LBody_good`**, **`p4LLoop_good`**). Afterwards `qSzA` holds
`((finRange W).flatMap (locSizes I)).reverse` and `rNt = locOff I W`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The location sizes of the first `j` locations. -/
noncomputable def locUpTo (j : ℕ) : List ℕ :=
  ((List.finRange I.numLocations).take j).flatMap (locSizes I)

lemma locUpTo_succ {j : ℕ} (hj : j < I.numLocations) :
    locUpTo I (j + 1) = locUpTo I j ++ locSizes I ⟨j, hj⟩ := by
  rw [locUpTo, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [locUpTo]

lemma locUpTo_all : locUpTo I I.numLocations = (List.finRange I.numLocations).flatMap (locSizes I) := by
  rw [locUpTo, List.take_of_length_le (by simp)]

lemma locSizes_eq_rep (v : Fin I.numLocations) :
    locSizes I v = List.replicate (coordList (I.domain v)).length
      (1 + (if initNum (I.init v) < 1 then 1 else 0)) := by
  rw [locSizes, labsN_eq]

lemma locSize_eq_mul (v : Fin I.numLocations) :
    locSize I v = (coordList (I.domain v)).length *
      (1 + (if initNum (I.init v) < 1 then 1 else 0)) := by
  rw [locSize_eq]; split_ifs <;> ring

/-- The label count of the current location: `1 + [ι = ⋆]`. -/
def labEx : Ex CR := .add (.const 1) (.lt (rv rA) (.const 1))

/-- The body of the location loop of `P4`. -/
def p4LBody : CStm CR CQ :=
  .seq (rdNumS rA rP rT) (.seq (rdNumS rD rP rT) (.seq (.set rLab labEx)
    (.seq (repPushS qSzA rLab rD rK rNt) (.seq (skipBlocksS rD rL1 rK rI rT)
      (.set rJ (.add (rv rJ) (.const 1)))))))

/-- The location loop of `P4`. -/
def p4LLoop : CStm CR CQ := .loop (.lt (rv rJ) (rv rW)) p4LBody

/-- The loop invariant. -/
def p4LInv (st s : NSt CR CQ) : Prop :=
  s.env rW = I.numLocations ∧ s.env rL1 = ℓ + 1 ∧
    s.env rJ ≤ I.numLocations ∧ s.pos = posAt I (s.env rJ) ∧
    s.env rNt = locOff I (s.env rJ) ∧
    s.stk = Function.update st.stk qSzA ((locUpTo I (s.env rJ)).reverse ++ st.stk qSzA) ∧
    s.out = st.out

lemma p4LBody_arith {N U la ld lf d : ℕ} (hU : U ≤ N) (hU' : 64 ≤ U) (hdf : N * d ≤ N * lf) :
    (la + 1) * (20 * N) + ((ld + 1) * (20 * N) + ((1 + (1 + 1 + 1) + 1) * N + U +
      ((d + 1) * (20 * N) + ((lf + d + 1) * (50 * N) + ((1 + 1 + 1) * N + U))))) ≤
      150 * N * (la + ld + lf) + 200 * N := by
  nlinarith

/-- One iteration of the location loop. -/
lemma p4LBody_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (st s : NSt CR CQ) (hI : p4LInv I st s) (hc : (Ex.lt (rv rJ) (rv rW)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p4LBody s s'
        (150 * Ex.nodeCost w * ((H I - s.pos) - (H I - s'.pos)) + 200 * Ex.nodeCost w) ∧
      p4LInv I st s' ∧ I.numLocations - s'.env rJ < I.numLocations - s.env rJ ∧
      H I - s'.pos ≤ H I - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  obtain ⟨hW, hL1, hjW, hpos, hnt, hstk, hout⟩ := hI
  have hlt : s.env rJ < I.numLocations := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hW]; rw [if_neg h]
  set j := s.env rJ with hjdef
  set v : Fin I.numLocations := ⟨j, hlt⟩
  set a := initNum (I.init v)
  set d := (coordList (I.domain v)).length
  set bs := (locNums I v).map (coordNumDescription ℓ)
  have hbsl : bs.length = d := by simp [bs, length_locNums, d]
  have hbsM : ∀ b ∈ bs, b.length = ℓ + 1 := by
    intro b hb
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
    simp [coordNumDescription]
  have hfl : bs.flatten.length = d * (ℓ + 1) := length_flatten_cnd I v
  set rest := encodeNats (locsSuf I (j + 1) ++ I.schemas.length :: schsDesc I)
  have hx : (encodeSystem I).drop s.pos =
      encodeNat a ++ (encodeNat d ++ (encodeNats bs.flatten ++ rest)) := by
    rw [hpos, drop_posAt, locsSuf_cons I hlt, locD_eq', List.append_assoc, List.cons_append,
      List.cons_append, encNats_cons, encNats_cons, encodeNats_append]
  have hposle : s.pos ≤ H I := by rw [hpos]; exact posAt_le I j
  have hlenx : s.pos + (encodeNat a).length + (encodeNat d).length +
      (encodeNats bs.flatten).length ≤ H I := by
    have := congrArg List.length hx
    simp only [List.length_drop, List.length_append] at this
    have : s.pos ≤ (encodeSystem I).length := hposle
    show _ ≤ (encodeSystem I).length
    omega
  have hdf : d ≤ (encodeNats bs.flatten).length :=
    le_trans (by rw [hfl]; nlinarith) (length_le_encodeNats _)
  have hdH : d ≤ H I := by omega
  have ha2 : a ≤ 2 := initNum_le _
  have ha : (Nat.bits a).length < w := bits_lt_of_le (le_trans ha2
    (by have := three_le_H I; omega)) hH2
  have hd : (Nat.bits d).length < w := bits_lt_of_le hdH hH2
  -- reading `ι(v)` and `|D_v|`
  have r1 := rdNumS_good (Q := CQ) hw (r := rA) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s a _ hx ha
  set s1 := rdNumFinal s rA rP rT a
  have hx2 : (encodeSystem I).drop s1.pos = encodeNat d ++ (encodeNats bs.flatten ++ rest) := by
    simp only [s1, rdNumFinal_pos]
    rw [← List.drop_drop, hx, List.drop_left]
  have r2 := rdNumS_good (Q := CQ) hw (r := rD) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s1 d _ hx2 hd
  set s2 := rdNumFinal s1 rD rP rT d
  have e2 : ∀ q, q ≠ rD → q ≠ rA → q ≠ rP → q ≠ rT → s2.env q = s.env q := by
    intro q h1 h2 h3 h4
    rw [rdNumFinal_env_ne h1 h3 h4, rdNumFinal_env_ne h2 h3 h4]
  have e2D : s2.env rD = d := rdNumFinal_env_r (by decide) (by decide) d
  have e2A : s2.env rA = a := by
    rw [rdNumFinal_env_ne (by decide) (by decide) (by decide)]
    exact rdNumFinal_env_r (by decide) (by decide) a
  -- the label count
  set lab := 1 + (if a < 1 then 1 else 0) with hlab
  have r3 := Good.set (x := encodeSystem I) (w := w) (r := rLab) (e := labEx) (st := s2) (by
    simp only [labEx, Ex.Fits, rv, Ex.eval, e2A]
    refine ⟨by omega, ⟨by omega, by omega⟩, by split_ifs <;> omega⟩)
  set s3 := s2.set rLab (labEx.eval s2.env)
  have e3 : ∀ q, q ≠ rLab → s3.env q = s2.env q := fun q hq => by
    simp [s3, Function.update_of_ne hq]
  have e3L : s3.env rLab = lab := by simp [s3, labEx, Ex.eval, rv, e2A, lab]
  have hsz : locOff I (j + 1) = locOff I j + d * lab := by
    rw [locOff_succ I hlt, locSize_eq_mul]
  have hoffH := locOff_le_H I (j + 1)
  have e3N : s3.env rNt = locOff I j := by
    rw [e3 _ (by decide), e2 _ (by decide) (by decide) (by decide) (by decide), hnt]
  -- pushing the sizes
  have r4 := repPushS_good (x := encodeSystem I) (w := w) hw (q := qSzA) (v := rLab) (n := rD)
    (j := rK) (acc := rNt) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) s3 e3L (by rw [e3 _ (by decide), e2D]) e3N (by omega) (by omega)
  set s4 := ((s3.setS qSzA (List.replicate d lab ++ s3.stk qSzA)).set rNt
    (locOff I j + d * lab)).set rK d
  have e4 : ∀ q, q ≠ rK → q ≠ rNt → s4.env q = s3.env q := fun q h1 h2 => by
    simp [s4, Function.update_of_ne h1, Function.update_of_ne h2]
  -- skipping the coordinates
  have hx4 : (encodeSystem I).drop s4.pos = encodeNats bs.flatten ++ rest := by
    show (encodeSystem I).drop s2.pos = _
    simp only [s2, rdNumFinal_pos]
    rw [← List.drop_drop, hx2, List.drop_left]
  obtain ⟨s5, r5, hs5, hp5, ho5, hf5⟩ := skipBlocksS_good (Q := CQ) hw (d := rD) (m := rL1)
    (j := rK) (i := rI) (t := rT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s4 bs (ℓ + 1) hbsM rest hx4
    (by rw [hbsl, e4 _ (by decide) (by decide), e3 _ (by decide)]; exact e2D)
    (by rw [e4 _ (by decide) (by decide), e3 _ (by decide),
        e2 rL1 (by decide) (by decide) (by decide) (by decide), hL1])
    (by rw [hbsl]; omega) (by omega)
  have e5J : s5.env rJ = j := by
    rw [hf5 _ (by decide) (by decide) (by decide), e4 _ (by decide) (by decide),
      e3 _ (by decide), e2 _ (by decide) (by decide) (by decide) (by decide)]
  have r6 := Good.set (x := encodeSystem I) (w := w) (r := rJ) (e := .add (rv rJ) (.const 1))
    (st := s5) (by
      have := W_le I
      simp only [Ex.Fits, Ex.eval, rv, e5J]; omega)
  set s6 := s5.set rJ (Ex.eval s5.env (.add (rv rJ) (.const 1)))
  have e6 : ∀ q, q ≠ rJ → s6.env q = s5.env q := fun q hq => by
    simp [s6, Function.update_of_ne hq]
  have e6J : s6.env rJ = j + 1 := by simp [s6, Ex.eval, rv, e5J]
  have back : ∀ q, q ≠ rJ → q ≠ rK → q ≠ rI → q ≠ rT → q ≠ rNt → q ≠ rLab → q ≠ rD →
      q ≠ rA → q ≠ rP → s6.env q = s.env q := by
    intro q h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [e6 q h1, hf5 q h2 h3 h4, e4 q h2 h5, e3 q h6, e2 q h7 h8 h9 h4]
  have hp6 : s6.pos = s.pos + (encodeNat a).length + (encodeNat d).length +
      (encodeNats bs.flatten).length := by
    rw [NSt.set_pos, hp5]; rfl
  refine ⟨s6, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, ?_, ?_⟩
  · rw [hp6]
    have hΔ : H I - s.pos - (H I - (s.pos + (encodeNat a).length + (encodeNat d).length +
        (encodeNats bs.flatten).length)) = (encodeNat a).length + (encodeNat d).length +
        (encodeNats bs.flatten).length := by omega
    rw [hΔ, hbsl]
    simp only [Ex.size, rv, labEx]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNat a).length = la at *
    generalize (encodeNat d).length = ld at *
    generalize (encodeNats bs.flatten).length = lf at *
    exact p4LBody_arith hU hU' (Nat.mul_le_mul_left N hdf)
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hW]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hL1]
  · rw [e6J]; omega
  · rw [e6J, hp6, hpos, posAt_succ I hlt, locD_eq']
    simp only [encNats_cons, List.length_append]; ring
  · rw [e6J, e6 _ (by decide), hf5 _ (by decide) (by decide) (by decide), hsz]
    simp [s4, Function.update_of_ne (show rNt ≠ rK by decide)]
  · rw [NSt.set_stk, hs5, e6J, locUpTo_succ I hlt, locSizes_eq_rep]
    show Function.update s3.stk qSzA (List.replicate d lab ++ s3.stk qSzA) = _
    have : s3.stk = s.stk := rfl
    rw [this, hstk]
    funext q
    by_cases hq : q = qSzA
    · subst hq; simp [lab, a, d, v]
    · simp [Function.update_of_ne hq]
  · rw [NSt.set_out, ho5]; exact hout
  · rw [e6J]; omega
  · rw [hp6]; omega

/-- **The location loop of `P4`.** -/
lemma p4LLoop_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (st : NSt CR CQ)
    (hI : p4LInv I st st) (hj : st.env rJ = 0) :
    ∃ st', Good (encodeSystem I) w p4LLoop st st' (400 * (H I + 1) * Ex.nodeCost w) ∧
      st'.pos = posAt I I.numLocations ∧ st'.env rNt = locOff I I.numLocations ∧
      st'.stk = Function.update st.stk qSzA
        (((List.finRange I.numLocations).flatMap (locSizes I)).reverse ++ st.stk qSzA) ∧
      st'.out = st.out := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨s7, r7, hI7, hc7⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rW)) (body := p4LBody) (p4LInv I st)
    (fun s => I.numLocations - s.env rJ) (fun s => H I - s.pos) (150 * Ex.nodeCost w)
    (200 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hW, -, hj, -⟩ := hI
      have := W_le I
      simp only [Ex.Fits, rv, hW]; omega, fun hc => p4LBody_good I hw hH hℓ st s hI hc⟩) st hI
  obtain ⟨hW7, -, hj7, hpos7, hnt7, hstk7, hout7⟩ := hI7
  have hjW : s7.env rJ = I.numLocations := by
    simp only [Ex.eval, rv, hW7] at hc7; split_ifs at hc7 with h <;> omega
  refine ⟨s7, r7.mono ?_, by rw [hpos7, hjW], by rw [hnt7, hjW], by
    rw [hstk7, hjW, locUpTo_all], hout7⟩
  have hW := W_le I
  have hc : condCost w (Ex.lt (rv rJ) (rv rW) : Ex CR) ≤ 4 * Ex.nodeCost w := by
    simp only [condCost, Ex.size, rv]; omega
  rw [hj, Nat.sub_zero]
  have hφ : H I - st.pos ≤ H I := Nat.sub_le _ _
  generalize condCost w (Ex.lt (rv rJ) (rv rW) : Ex CR) = c at *
  generalize Ex.nodeCost w = N at *
  generalize H I - st.pos = φ at *
  generalize H I = h at *
  generalize I.numLocations = W at *
  have h1 : 150 * N * φ ≤ 150 * N * h := Nat.mul_le_mul_left _ hφ
  have h2 : W * (200 * N + c) ≤ h * (204 * N) := Nat.mul_le_mul hW (by omega)
  nlinarith

end Lax119563Proofs.Compiler
