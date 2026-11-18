import Lax119563Proofs.Compiler.PLoc

/-!
# Pass `P1'` of the compiler program: the location records

`p1r` (systems with a schema, where `k ≤ H`), run after `p1` (it uses `rW = W` and
`rL1 = ℓ + 1`), rewinds the input and pushes, for every location `v` and every coordinate of
`D_v` (in increasing order of their numbers, the `r`-th one with number `n`), the record
`locRec I v r = v :: i :: b₀ … b_{ℓ-1} ++ [locOff I v + r · |labs v|, |labs v|]`
(`i, b₀ … b_{ℓ-1}` = `coordNumDescription ℓ n`) onto the stack `qRec` (`p1r_good`); the
record ends with the offset of the coordinate class from `locBase` and its number of labels.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-- The number of labels of the current location. -/
def rLab : Fin CR := 14
/-- The value register of the record reader. -/
def rV : Fin CR := 15
/-- The location records. -/
def qRec : Fin CQ := 1

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## The records -/

/-- The number of labels of the coordinate classes of `v`. -/
def labsN (v : Fin I.numLocations) : ℕ := (coordLabs I v).length

lemma labsN_eq (v : Fin I.numLocations) :
    labsN I v = 1 + (if initNum (I.init v) < 1 then 1 else 0) := by
  unfold labsN coordLabs
  rcases h : I.init v with _ | b <;> simp [initNum, bits1]

/-- The record of the `r`-th coordinate of location `v`. -/
noncomputable def locRec (v : Fin I.numLocations) (r : ℕ) : List ℕ :=
  (v : ℕ) :: (coordNumDescription ℓ ((locNums I v).getD r 0) ++
    [locOff I v + r * labsN I v, labsN I v])

/-- The records of location `v`. -/
noncomputable def recsV (v : Fin I.numLocations) : List (List ℕ) :=
  (List.range (coordList (I.domain v)).length).map (locRec I v)

/-- The records of the first `j` locations. -/
noncomputable def recsUpTo (j : ℕ) : List (List ℕ) :=
  ((List.finRange I.numLocations).take j).flatMap (recsV I)

/-- All location records. -/
noncomputable def locRecs : List (List ℕ) := (List.finRange I.numLocations).flatMap (recsV I)

lemma recsUpTo_succ {j : ℕ} (hj : j < I.numLocations) :
    recsUpTo I (j + 1) = recsUpTo I j ++ recsV I ⟨j, hj⟩ := by
  rw [recsUpTo, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [recsUpTo]

lemma recsUpTo_all : recsUpTo I I.numLocations = locRecs I := by
  rw [recsUpTo, locRecs, List.take_of_length_le (by simp)]

lemma recsV_take_succ (v : Fin I.numLocations) {r : ℕ} (hr : r < (coordList (I.domain v)).length) :
    (recsV I v).take (r + 1) = (recsV I v).take r ++ [locRec I v r] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa [recsV] using hr)]
  simp [recsV]

/-! ## Sizes -/

lemma k_le_H (h : I.schemas ≠ []) : k ≤ H I := by
  have h2 := length_sd_le I
  rw [sd_eq] at h2
  simp only [List.length_cons, List.length_append] at h2
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ h
  have h1 : (schemaDescription e).length ≤ (schsDesc I).length := by
    rw [schsDesc, List.length_flatMap]
    exact List.le_sum_of_mem (List.mem_map_of_mem he)
  have : k ≤ (schemaDescription e).length := by
    cases e with
    | binary u v D σ τ =>
      have := length_permDescription σ
      simp only [schemaDescription, List.length_append]; omega
    | ternary u v w' D σ τ π =>
      have := length_permDescription σ
      simp only [schemaDescription, List.length_append]; omega
  omega

lemma coordNum_div (c : Coord k ℓ) : coordNum c / 2 ^ ℓ = c.1 := by
  obtain ⟨i, b⟩ := c
  simp only [coordNum, blockNum_eq_regVal]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (regVal_lt b),
    zero_add]

lemma cnd_le {v : Fin I.numLocations} {n : ℕ} (hn : n ∈ locNums I v) {m : ℕ}
    (hm : m ∈ coordNumDescription ℓ n) : m < k ∨ m ≤ 1 := by
  rw [locNums, Finset.mem_sort, Finset.mem_image] at hn
  obtain ⟨c, -, rfl⟩ := hn
  simp only [coordNumDescription, List.mem_cons, List.mem_map, List.mem_range] at hm
  rcases hm with rfl | ⟨t, -, rfl⟩
  · rw [coordNum_div]; left; exact c.1.2
  · right; split_ifs <;> omega

lemma length_cnd (n : ℕ) : (coordNumDescription ℓ n).length = ℓ + 1 := by
  simp [coordNumDescription]

open CStm

/-! ## The program -/

/-- One coordinate: push its record. -/
def p1rIn : CStm CR CQ :=
  .seq (.push qRec (rv rJ)) (.seq (rdNumsS qRec rL1 rI rV rP rT) (.seq (.push qRec (rv rOff))
    (.seq (.push qRec (rv rLab)) (.seq (.set rOff (.add (rv rOff) (rv rLab)))
      (.set rK (.add (rv rK) (.const 1)))))))

/-- The coordinate loop. -/
def p1rCoords : CStm CR CQ := .loop (.lt (rv rK) (rv rD)) p1rIn

/-- One location. -/
def p1rBody : CStm CR CQ :=
  .seq (rdNumS rA rP rT) (.seq (rdNumS rD rP rT)
    (.seq (.set rLab (.add (.const 1) (.lt (rv rA) (.const 1))))
      (.seq (.set rK (.const 0)) (.seq p1rCoords (.set rJ (.add (rv rJ) (.const 1)))))))

/-- **Pass `P1'`.** -/
def p1r : CStm CR CQ :=
  .seq .rst (.seq (skipNumS rT) (.seq (skipNumS rT) (.seq (skipNumS rT)
    (.seq (.set rJ (.const 0)) (.seq (.set rOff (.const 0))
      (.loop (.lt (rv rJ) (rv rW)) p1rBody))))))

/-- The invariant of the coordinate loop of location `v` (coordinates from position `B`,
stacks `S0`, output `O`). -/
def p1rInInv (v : Fin I.numLocations) (B : ℕ) (S0 : Fin CQ → List ℕ) (O : List ℕ)
    (s : NSt CR CQ) : Prop :=
  s.env rK ≤ (coordList (I.domain v)).length ∧ s.env rD = (coordList (I.domain v)).length ∧
    s.env rJ = v ∧ s.env rL1 = ℓ + 1 ∧ s.env rLab = labsN I v ∧ s.env rW = I.numLocations ∧
    s.env rOff = locOff I v + s.env rK * labsN I v ∧
    s.pos = B + (encodeNats
      (((locNums I v).map (coordNumDescription ℓ)).take (s.env rK)).flatten).length ∧
    s.stk = Function.update S0 qRec
      (((recsV I v).take (s.env rK)).flatten.reverse ++ S0 qRec) ∧ s.out = O

set_option maxHeartbeats 800000 in
/-- One coordinate. -/
lemma p1rIn_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hkH : k ≤ H I)
    (hℓ : ℓ ≤ H I) (v : Fin I.numLocations) (B : ℕ) (S0 : Fin CQ → List ℕ) (O : List ℕ)
    (rest : List Bool)
    (hx : (encodeSystem I).drop B =
      encodeNats ((locNums I v).map (coordNumDescription ℓ)).flatten ++ rest)
    (hoff : locOff I (v.val + 1) ≤ 2 * H I)
    (s : NSt CR CQ) (hI : p1rInInv I v B S0 O s) (hc : (Ex.lt (rv rK) (rv rD)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p1rIn s s'
        (60 * Ex.nodeCost w * ((B + (encodeNats ((locNums I v).map
            (coordNumDescription ℓ)).flatten).length - s.pos) -
          (B + (encodeNats ((locNums I v).map (coordNumDescription ℓ)).flatten).length -
            s'.pos)) + 100 * Ex.nodeCost w) ∧
      p1rInInv I v B S0 O s' ∧
      (coordList (I.domain v)).length - s'.env rK < (coordList (I.domain v)).length - s.env rK ∧
      B + (encodeNats ((locNums I v).map (coordNumDescription ℓ)).flatten).length - s'.pos ≤
        B + (encodeNats ((locNums I v).map (coordNumDescription ℓ)).flatten).length - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨hK, hD, hJ, hL1, hLab, hW, hO, hpos, hstk, hout⟩ := hI
  set d := (coordList (I.domain v)).length
  set bs := (locNums I v).map (coordNumDescription ℓ)
  have hbsl : bs.length = d := by simp [bs, length_locNums, d]
  have hlt : s.env rK < d := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hD]; rw [if_neg h]
  set r := s.env rK with hr
  have hrb : r < bs.length := by omega
  have hrn : r < (locNums I v).length := by rw [length_locNums]; exact hlt
  have hsplit : bs.flatten = (bs.take r).flatten ++ (bs[r] ++ (bs.drop (r + 1)).flatten) := by
    have e := List.take_append_drop r bs
    rw [List.drop_eq_getElem_cons hrb] at e
    conv_lhs => rw [← e]
    simp only [List.flatten_append, List.flatten_cons]
  have hgd : (locNums I v).getD r 0 = (locNums I v)[r] := List.getD_eq_getElem _ _ hrn
  have hvs' : bs[r] = coordNumDescription ℓ ((locNums I v).getD r 0) := by
    simp only [bs, List.getElem_map, hgd]
  set vs := bs[r]
  have hvs : vs = coordNumDescription ℓ ((locNums I v).getD r 0) := hvs'
  have hvl : vs.length = ℓ + 1 := by rw [hvs, length_cnd]
  have hxj : (encodeSystem I).drop s.pos = encodeNats vs ++
      (encodeNats (bs.drop (r + 1)).flatten ++ rest) := by
    rw [hpos, drop_add, hx, hsplit, encodeNats_append, encodeNats_append, List.append_assoc,
      List.drop_left, List.append_assoc]
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  have h3 := three_le_H I
  have hvsw : ∀ m ∈ vs, (Nat.bits m).length < w := by
    intro m hm
    rw [hvs] at hm
    have hmem : (locNums I v).getD r 0 ∈ locNums I v := by rw [hgd]; exact List.getElem_mem hrn
    refine bits_lt_of_le ?_ hH2
    rcases cnd_le I hmem hm with h | h <;> omega
  -- push `v`
  have r1 := Good.push (x := encodeSystem I) (w := w) (q := qRec) (e := rv rJ) (st := s)
    (by simp only [Ex.Fits, rv, hJ]; have := W_le I; omega)
  set s1 := s.setS qRec ((rv rJ : Ex CR).eval s.env :: s.stk qRec)
  have hx1 : (encodeSystem I).drop s1.pos = encodeNats vs ++
      (encodeNats (bs.drop (r + 1)).flatten ++ rest) := hxj
  -- read the coordinate
  obtain ⟨r2, hs2, hp2, ho2, he2⟩ := rdNumsS_good (Q := CQ) (x := encodeSystem I) hw
    (q := qRec) (n := rL1) (i := rI) (r := rV) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) s1 vs _ hx1 (by rw [hvl]; exact hL1) (by rw [hvl]; omega) hvsw
  set s2 := rnsSt s1 qRec rI rV rP rT vs vs.length
  have e2 : ∀ q, q ≠ rI → q ≠ rV → q ≠ rP → q ≠ rT → s2.env q = s.env q :=
    fun q h1 h2 h3 h4 => he2 q h1 h2 h3 h4
  have e2O : s2.env rOff = locOff I v + r * labsN I v := by
    rw [e2 _ (by decide) (by decide) (by decide) (by decide), hO]
  have e2L : s2.env rLab = labsN I v := by
    rw [e2 _ (by decide) (by decide) (by decide) (by decide), hLab]
  have hlabs : labsN I v ≤ 2 := by rw [labsN_eq]; split_ifs <;> omega
  have hoffr : locOff I v + (r + 1) * labsN I v ≤ 2 * H I := by
    refine le_trans ?_ hoff
    rw [locOff_succ I v.2]
    have : locSize I v = d * labsN I v := rfl
    rw [this]; nlinarith
  -- push the offset and the labels
  have r3 := Good.push (x := encodeSystem I) (w := w) (q := qRec) (e := rv rOff) (st := s2)
    (by simp only [Ex.Fits, rv, e2O]; nlinarith)
  set s3 := s2.setS qRec ((rv rOff : Ex CR).eval s2.env :: s2.stk qRec)
  have r4 := Good.push (x := encodeSystem I) (w := w) (q := qRec) (e := rv rLab) (st := s3)
    (by show s2.env rLab < 2 ^ w; rw [e2L]; omega)
  set s4 := s3.setS qRec ((rv rLab : Ex CR).eval s3.env :: s3.stk qRec)
  have r5 := Good.set (x := encodeSystem I) (w := w) (r := rOff) (e := .add (rv rOff) (rv rLab))
    (st := s4) (by
      show s2.env rOff < 2 ^ w ∧ s2.env rLab < 2 ^ w ∧ s2.env rOff + s2.env rLab < 2 ^ w
      rw [e2O, e2L]; refine ⟨by nlinarith, by omega, by nlinarith⟩)
  set s5 := s4.set rOff (Ex.eval s4.env (.add (rv rOff) (rv rLab)))
  have e5 : ∀ q, s5.env q = Function.update s2.env rOff
      (locOff I v + r * labsN I v + labsN I v) q := by
    intro q; simp only [s5, s4, s3, NSt.set_env, NSt.setS_env, Ex.eval, rv, e2O, e2L]
  have e5K : s5.env rK = r := by
    rw [e5, Function.update_of_ne (by decide), e2 _ (by decide) (by decide) (by decide)
      (by decide)]
  have r6 := Good.set (x := encodeSystem I) (w := w) (r := rK) (e := .add (rv rK) (.const 1))
    (st := s5) (by
      have hdH : d ≤ H I := by
        show (coordList (I.domain v)).length ≤ H I
        rw [← card_image_coordNum]; exact card_le I v
      simp only [Ex.Fits, Ex.eval, rv, e5K]; omega)
  set s6 := s5.set rK (Ex.eval s5.env (.add (rv rK) (.const 1)))
  have e6 : ∀ q, s6.env q = Function.update (Function.update s2.env rOff
      (locOff I v + r * labsN I v + labsN I v)) rK (r + 1) q := by
    intro q; simp only [s6, NSt.set_env, Ex.eval, rv, e5K]
    by_cases h : q = rK
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne h, e5]
  have e6K : s6.env rK = r + 1 := by rw [e6, Function.update_self]
  have back : ∀ q, q ≠ rK → q ≠ rOff → q ≠ rI → q ≠ rV → q ≠ rP → q ≠ rT →
      s6.env q = s.env q := by
    intro q h1 h2 h3 h4 h5 h6
    rw [e6, Function.update_of_ne h1, Function.update_of_ne h2, e2 q h3 h4 h5 h6]
  have hp6 : s6.pos = s.pos + (encodeNats vs).length := by
    show s2.pos = _; rw [hp2]; rfl
  have hlen : (encodeNats (bs.take (r + 1)).flatten).length =
      (encodeNats (bs.take r).flatten).length + (encodeNats vs).length := by
    rw [List.take_add_one, List.getElem?_eq_getElem hrb]
    simp only [Option.toList_some, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, encodeNats_append, List.length_append] <;> rfl
  have hle : (encodeNats (bs.take (r + 1)).flatten).length ≤ (encodeNats bs.flatten).length := by
    conv_rhs => rw [← List.take_append_drop (r + 1) bs]
    rw [List.flatten_append, encodeNats_append, List.length_append]; omega
  have hvle : ℓ + 1 ≤ (encodeNats vs).length := by rw [← hvl]; exact length_le_encodeNats _
  refine ⟨s6, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hp6]
    have hΔ : B + (encodeNats bs.flatten).length - s.pos -
        (B + (encodeNats bs.flatten).length - (s.pos + (encodeNats vs).length)) =
        (encodeNats vs).length := by omega
    rw [hΔ, hvl]
    simp only [Ex.size, rv]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNats vs).length = lv at *
    have := Nat.mul_le_mul_left N hvle
    nlinarith only [hU, hU', this]
  · rw [e6K]; omega
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hD]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hJ]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hL1]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hLab]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hW]
  · rw [e6K, e6, Function.update_of_ne (by decide), Function.update_self]; ring
  · rw [e6K, hp6, hpos, hlen]; ring
  · show Function.update s3.stk qRec (Ex.eval s3.env (rv rLab) :: s3.stk qRec) = _
    have hl : Ex.eval s3.env (rv rLab) = labsN I v := e2L
    rw [hl]
    have h3s : s3.stk qRec = (locOff I v + r * labsN I v) :: s2.stk qRec := by
      show Function.update s2.stk qRec _ qRec = _
      rw [Function.update_self]; show s2.env rOff :: _ = _; rw [e2O]
    have hs1 : s1.stk = Function.update s.stk qRec (v.val :: s.stk qRec) := by
      show Function.update s.stk qRec (s.env rJ :: s.stk qRec) = _; rw [hJ]
    rw [e6K, recsV_take_succ I v hlt, List.flatten_append, List.reverse_append]
    funext q
    by_cases hq : q = qRec
    · subst hq
      rw [Function.update_self, Function.update_self, h3s, hs2, Function.update_self, hs1,
        Function.update_self, hstk, Function.update_self]
      simp [locRec, hvs]
    · rw [Function.update_of_ne hq, Function.update_of_ne hq]
      show Function.update s2.stk qRec _ q = _
      rw [Function.update_of_ne hq, hs2, Function.update_of_ne hq, hs1, Function.update_of_ne hq,
        hstk, Function.update_of_ne hq]
  · show s2.out = O; rw [ho2]; exact hout
  · rw [e6K]; omega
  · rw [hp6]; omega

end Lax119563Proofs.Compiler
