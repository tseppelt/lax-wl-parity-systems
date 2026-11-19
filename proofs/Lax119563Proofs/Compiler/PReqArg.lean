import Lax119563Proofs.Compiler.PReqCols

/-!
# Pass `P3`, request generation: one argument of a schema

`p3Arg` (at the description of the permutation `π` of the argument, with its location on top
of `qLs2` and the coordinates of the domain on `qDom2`) reads `f` and the shifts onto stacks,
pushes the requests of all columns (`p3Cols`) with the sequence numbers
`base + sqOff tern a |D| + r · (tern ? 3 : 1)`, restores the domain and discards the rest of
the permutation (**`p3Arg_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ}

/-- The sequence base (number of requests of the previous schemas). -/
def rSB : Fin CR := 37

/-- The first sequence number of argument `a`. -/
def sqOff (tern : Bool) (a d : ℕ) : ℕ := if tern then a else if a = 0 then d else 0

/-- The stride of the sequence numbers. -/
def sqStr (tern : Bool) : ℕ := if tern then 3 else 1

lemma seqOff_eq (tern : Bool) (d a r : ℕ) (ha : a < (if tern then 3 else 2)) :
    seqOff tern d a r = sqOff tern a d + r * sqStr tern := by
  unfold seqOff sqOff sqStr; split_ifs <;> omega

/-- Set the first sequence number. -/
def p3Seq : CStm CR CQ :=
  .ite (rv rTn) (.set rSq (.add (rv rSB) (rv rAi)))
    (.ite (.lt (rv rAi) (.const 1)) (.set rSq (.add (rv rSB) (rv rD))) (.set rSq (rv rSB)))

lemma p3Seq_good {x : List Bool} {w : ℕ} (st : NSt CR CQ) (tern : Bool) {a d b : ℕ}
    (hTn : st.env rTn = if tern then 1 else 0) (hAi : st.env rAi = a) (hD : st.env rD = d)
    (hB : st.env rSB = b) (hw : b + sqOff tern a d < 2 ^ w) (haw : a + 1 < 2 ^ w)
    (hdw : d < 2 ^ w) :
    Good x w p3Seq st (st.set rSq (b + sqOff tern a d)) (12 * Ex.nodeCost w) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h1 : (1 : ℕ) < 2 ^ w := by omega
  unfold p3Seq
  cases tern with
  | true =>
    refine (CStm.Good.iteT (by simp only [Ex.Fits, rv, hTn]; split_ifs <;> omega) (by simp [rv, Ex.eval, hTn])
      (CStm.Good.set (by simp only [Ex.Fits, rv, Ex.eval, hB, hAi]; simp [sqOff] at hw; omega))).of_eq
      (by simp [Ex.eval, rv, hB, hAi, sqOff]) (by simp [condCost, Ex.size, rv]; omega)
  | false =>
    suffices h : Good x w (.ite (.lt (rv rAi) (.const 1)) (.set rSq (.add (rv rSB) (rv rD)))
        (.set rSq (rv rSB))) st (st.set rSq (b + sqOff false a d)) (8 * Ex.nodeCost w) from
      (CStm.Good.iteF (by simp only [Ex.Fits, rv, hTn]; split_ifs <;> omega) (by simp [rv, Ex.eval, hTn])
        h).mono (by simp [condCost, Ex.size, rv]; omega)
    by_cases ha : a = 0
    · refine (CStm.Good.iteT (by simp only [Ex.Fits, rv, hAi]; try omega) (by simp [rv, Ex.eval, hAi, ha])
        (CStm.Good.set (by simp only [Ex.Fits, rv, Ex.eval, hB, hD]; simp [sqOff, ha] at hw; omega))).of_eq
        (by simp [Ex.eval, rv, hB, hD, sqOff, ha]) (by simp [condCost, Ex.size, rv]; omega)
    · refine (CStm.Good.iteF (by simp only [Ex.Fits, rv, hAi]; try omega) (by simp [rv, Ex.eval, hAi]; omega)
        (CStm.Good.set (by simp only [Ex.Fits, rv, hB]; simp [sqOff, ha] at hw; omega))).of_eq
        (by simp [Ex.eval, rv, hB, sqOff, ha]) (by simp [condCost, Ex.size, rv]; omega)

/-- **One argument.** -/
def p3Arg : CStm CR CQ :=
  .seq (.pop qLs2 rU) (.seq (rdNumsS qF rKk rI rV rP rT) (.seq (moveAllS qF qF2 rT rT2)
    (.seq (rdNumsS qDl rKL rI rV rP rT) (.seq (moveAllS qDl qDl2 rT rT2)
      (.seq (.pop qF2 rFi) (.seq (.set rCur (.const 0)) (.seq p3Seq (.seq p3Cols
        (.seq (moveAllS qDom qDom2 rT rT2) (.seq (moveAllS qF2 qJunk rT rT2)
          (.seq (moveAllS qDl2 qJunk rT rT2) (.set rAi (.add (rv rAi) (.const 1))))))))))))))

lemma length_flatten_dL (π : BlockPerm k ℓ) : (dL π).flatten.length = k * ℓ := by
  rw [List.length_flatten]
  have : (dL π).map List.length = (dL π).map fun _ => ℓ :=
    List.map_congr_left fun d hd => (dL_mem π d hd).1
  rw [this, sum_map_const, length_dL]

lemma length_flatten_drop_le (L : List (List ℕ)) (c : ℕ) :
    (L.drop c).flatten.length ≤ L.flatten.length := by
  conv_rhs => rw [← List.take_append_drop c L]
  rw [List.flatten_append, List.length_append]; omega

lemma arg_arith (N U k n ℓ lf ld a b : ℕ) (hU : U ≤ N) (hU' : 64 ≤ U) (hk : 1 ≤ k)
    (hlf : k ≤ lf) (hld : k * ℓ ≤ ld) (ha : a ≤ k) (hb : b ≤ k * ℓ) :
    U + 1 + (lf + 2 * k + 1) * (20 * N) + (k + 1) * (10 * N) + (ld + 2 * (k * ℓ) + 1) * (20 * N)
      + (k * ℓ + 1) * (10 * N) + (U + 1) + (1 * N + U) + 12 * N
      + (k + n + 1) * ((ℓ + 3) * (60 * N)) + (n * (ℓ + 1) + 1) * (10 * N) + (a + 1) * (10 * N)
      + (b + 1) * (10 * N) + (3 * N + U) ≤ 600 * (lf + ld + n * (ℓ + 1) + 1) * N := by
  have hkl : 1 * ℓ ≤ k * ℓ := Nat.mul_le_mul_right ℓ hk
  have h1 : (k + n + 1) * (ℓ + 3) ≤ 6 * (k * ℓ + k) + 3 * (n * (ℓ + 1)) := by nlinarith
  have key : (k + n + 1) * ((ℓ + 3) * (60 * N)) ≤
      360 * (k * ℓ * N) + 360 * (k * N) + 180 * (n * (ℓ + 1) * N) := by
    have := Nat.mul_le_mul_right (60 * N) h1
    calc (k + n + 1) * ((ℓ + 3) * (60 * N)) = (k + n + 1) * (ℓ + 3) * (60 * N) := by ring
      _ ≤ (6 * (k * ℓ + k) + 3 * (n * (ℓ + 1))) * (60 * N) := this
      _ = _ := by ring
  have e2 : a * N ≤ k * N := Nat.mul_le_mul_right _ ha
  have e3 : b * N ≤ k * ℓ * N := Nat.mul_le_mul_right _ hb
  have e4 : k * N ≤ lf * N := Nat.mul_le_mul_right _ hlf
  have e5 : k * ℓ * N ≤ ld * N := Nat.mul_le_mul_right _ hld
  have hN : 64 ≤ N := le_trans hU' hU
  have eq1 : U + 1 + (lf + 2 * k + 1) * (20 * N) + (k + 1) * (10 * N) +
      (ld + 2 * (k * ℓ) + 1) * (20 * N) + (k * ℓ + 1) * (10 * N) + (U + 1) + (1 * N + U) + 12 * N
      + (k + n + 1) * ((ℓ + 3) * (60 * N)) + (n * (ℓ + 1) + 1) * (10 * N) + (a + 1) * (10 * N)
      + (b + 1) * (10 * N) + (3 * N + U) =
      4 * U + 2 + 20 * (lf * N) + 50 * (k * N) + 20 * (ld * N) + 50 * (k * ℓ * N) + 106 * N
      + (k + n + 1) * ((ℓ + 3) * (60 * N)) + 10 * (n * (ℓ + 1) * N) + 10 * (a * N)
      + 10 * (b * N) := by ring
  have eq2 : 600 * (lf + ld + n * (ℓ + 1) + 1) * N =
      600 * (lf * N) + 600 * (ld * N) + 600 * (n * (ℓ + 1) * N) + 600 * N := by ring
  rw [eq1, eq2]
  generalize (k + n + 1) * ((ℓ + 3) * (60 * N)) = K at *
  generalize lf * N = A1 at *
  generalize ld * N = A2 at *
  generalize k * N = A3 at *
  generalize k * ℓ * N = A4 at *
  generalize n * (ℓ + 1) * N = A5 at *
  generalize a * N = A6 at *
  generalize b * N = A7 at *
  omega

set_option maxHeartbeats 8000000 in
/-- **One argument of a schema.** -/
lemma p3Arg_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) (hb : st.Bdd w)
    (hpx : st.pos ≤ x.length) (u : ℕ) (Ls : List ℕ) (π : BlockPerm k ℓ) (cs : List (Coord k ℓ))
    (tern : Bool) (a base : ℕ) (rest : List Bool)
    (hs : (cs.map fun c => (c.1 : ℕ)).Pairwise (· ≤ ·)) (hk : 1 ≤ k)
    (hx : x.drop st.pos = encodeNats (permDescription π) ++ rest)
    (hKw : k * ℓ + k + 1 < 2 ^ w) (hℓw : ℓ + 1 < 2 ^ w) (huw : u < 2 ^ w)
    (hnw : cs.length + 1 < 2 ^ w) (haw : a + 1 < 2 ^ w)
    (hsw : base + sqOff tern a cs.length + cs.length * sqStr tern < 2 ^ w)
    (hbits : ∀ v ∈ permDescription π, (Nat.bits v).length < w)
    (hKk : st.env rKk = k) (hKL : st.env rKL = k * ℓ) (hL : st.env rL = ℓ)
    (hD : st.env rD = cs.length) (hTn : st.env rTn = if tern then 1 else 0)
    (hAi : st.env rAi = a) (hSB : st.env rSB = base) (hStr : st.env rStr = sqStr tern)
    (hLs : st.stk qLs2 = u :: Ls) (hF : st.stk qF = []) (hF2 : st.stk qF2 = [])
    (hDl : st.stk qDl = []) (hDl2 : st.stk qDl2 = []) (hDom : st.stk qDom = [])
    (hDom2 : st.stk qDom2 = cs.flatMap cdesc) (hAux : st.stk qAux = []) :
    ∃ st', Good x w p3Arg st st'
        (600 * ((encodeNats (permDescription π)).length + cs.length * (ℓ + 1) + 1) *
          Ex.nodeCost w) ∧
      st'.stk qLs2 = Ls ∧ st'.stk qF = [] ∧ st'.stk qF2 = [] ∧ st'.stk qDl = [] ∧
      st'.stk qDl2 = [] ∧ st'.stk qDom = [] ∧ st'.stk qDom2 = cs.flatMap cdesc ∧
      st'.stk qAux = [] ∧
      st'.stk qRec = (colReqs u π cs (base + sqOff tern a cs.length) (sqStr tern)).flatten.reverse ++
        st.stk qRec ∧
      (∀ q, q ≠ qLs2 → q ≠ qF → q ≠ qF2 → q ≠ qDl → q ≠ qDl2 → q ≠ qDom → q ≠ qDom2 →
        q ≠ qAux → q ≠ qRec → q ≠ qJunk → st'.stk q = st.stk q) ∧
      st'.env rAi = a + 1 ∧
      st'.pos = st.pos + (encodeNats (permDescription π)).length ∧ st'.out = st.out ∧
      ∀ r, wReg r p3Arg = false → st'.env r = st.env r := by
  have hU0 := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set n := cs.length
  have hfk : (fL π).length = k := length_fL π
  have hdk : (dL π).flatten.length = k * ℓ := length_flatten_dL π
  have hxF : x.drop (st.pos) = encodeNats (fL π) ++ (encodeNats (dL π).flatten ++ rest) := by
    rw [hx, permDescription_eq, encodeNats_append, List.append_assoc]
  -- the location
  have r1 := Good.pop_cons (x := x) (w := w) (r := rU) hLs
  set s1 := (st.setS qLs2 Ls).set rU u
  -- `f`
  obtain ⟨r2, h2S, h2p, h2o, h2e⟩ := rdNumsS_good (Q := CQ) (x := x) hw (q := qF) (n := rKk)
    (i := rI) (r := rV) (p := rP) (t := rT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s1 (fL π)
    (encodeNats (dL π).flatten ++ rest) hxF (by rw [hfk]; simp [s1, Function.update_of_ne
      (show rKk ≠ rU by decide), hKk]) (by rw [hfk]; omega)
    (fun v hv => hbits v (by rw [permDescription_eq]; exact List.mem_append_left _ hv))
  set s2 := rnsSt s1 qF rI rV rP rT (fL π) (fL π).length
  have hb2 := (r1.seq r2).bdd hw hb hpx
  obtain ⟨s3, r3, h3S, h3p, h3o, h3e⟩ := moveAllS_good (x := x) hw (q := qF) (q' := qF2)
    (t := rT) (f := rT2) (by decide) (by decide) s2 hb2.1
  have h2F : s2.stk qF = (fL π).reverse := by rw [h2S]; simp [s1, Function.update_of_ne (show qF ≠ qLs2 by decide), hF]
  have h3F2 : s3.stk qF2 = fL π := by
    rw [h3S, Function.update_self, h2F, List.reverse_reverse, h2S,
      Function.update_of_ne (by decide)]; simp [s1, Function.update_of_ne (show qF2 ≠ qLs2 by decide), hF2]
  -- the shifts
  have hx3 : x.drop s3.pos = encodeNats (dL π).flatten ++ rest := by
    rw [h3p, h2p, ← List.drop_drop, show s1.pos = st.pos from rfl, hxF, List.drop_left]
  have e3 : ∀ r, r ≠ rT → r ≠ rT2 → r ≠ rI → r ≠ rV → r ≠ rP → r ≠ rU → s3.env r = st.env r := by
    intro r n1 n2 n3 n4 n5 n6
    rw [h3e r n1 n2, h2e r n3 n4 n5 n1]; simp [s1, Function.update_of_ne n6]
  obtain ⟨r4, h4S, h4p, h4o, h4e⟩ := rdNumsS_good (Q := CQ) (x := x) hw (q := qDl) (n := rKL)
    (i := rI) (r := rV) (p := rP) (t := rT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s3 (dL π).flatten
    rest hx3 (by rw [hdk, e3 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hKL]) (by rw [hdk]; omega)
    (fun v hv => hbits v (by rw [permDescription_eq]; exact List.mem_append_right _ hv))
  set s4 := rnsSt s3 qDl rI rV rP rT (dL π).flatten (dL π).flatten.length
  have hb4 := (r1.seq (r2.seq (r3.seq r4))).bdd hw hb hpx
  obtain ⟨s5, r5, h5S, h5p, h5o, h5e⟩ := moveAllS_good (x := x) hw (q := qDl) (q' := qDl2)
    (t := rT) (f := rT2) (by decide) (by decide) s4 hb4.1
  have h4Dl : s4.stk qDl = (dL π).flatten.reverse := by
    rw [h4S, Function.update_self, h3S, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), h2S, Function.update_of_ne (by decide)]
    simp [s1, Function.update_of_ne (show qDl ≠ qLs2 by decide), hDl]
  have h5Dl2 : s5.stk qDl2 = (dL π).flatten := by
    rw [h5S, Function.update_self, h4Dl, List.reverse_reverse, h4S,
      Function.update_of_ne (by decide), h3S, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), h2S, Function.update_of_ne (by decide)]
    simp [s1, Function.update_of_ne (show qDl2 ≠ qLs2 by decide), hDl2]
  have h5F2 : s5.stk qF2 = (fL π).getD 0 0 :: (fL π).drop 1 := by
    rw [h5S, Function.update_of_ne (by decide), Function.update_of_ne (by decide), h4S,
      Function.update_of_ne (by decide), h3F2]
    obtain ⟨f0, fs, hfs⟩ : ∃ f0 fs, fL π = f0 :: fs := by
      cases h : fL π with
      | nil => rw [h] at hfk; simp at hfk; omega
      | cons f0 fs => exact ⟨f0, fs, rfl⟩
    rw [hfs]; rfl
  -- the first image
  have r6 := Good.pop_cons (x := x) (w := w) (r := rFi) h5F2
  set s6 := (s5.setS qF2 ((fL π).drop 1)).set rFi ((fL π).getD 0 0)
  have r7 := Good.set (x := x) (w := w) (r := rCur) (e := .const 0) (st := s6)
    (by simp only [Ex.Fits]; omega)
  set s7 := s6.set rCur ((Ex.const 0 : Ex CR).eval s6.env)
  have hpre7 := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  have r8 := p3Seq_good (x := x) (w := w) s7 tern (a := a) (d := n) (b := base)
    (by rw [hpre7.env_of (by decide), hTn]) (by rw [hpre7.env_of (by decide), hAi])
    (by rw [hpre7.env_of (by decide), hD]) (by rw [hpre7.env_of (by decide), hSB])
    (by omega) haw (by omega)
  set s8 := s7.set rSq (base + sqOff tern a n)
  have hpre8 := hpre7.seq r8
  have hsuf2 : ∀ r, r ≠ rI → r ≠ rV → r ≠ rP → r ≠ rT → r ≠ rT2 → r ≠ rFi → r ≠ rCur →
      r ≠ rSq → s8.env r = s1.env r := by
    intro r n1 n2 n3 n4 n5 n6 n7 n8
    simp only [s8, s7, s6, NSt.set_env, NSt.setS_env, Function.update_of_ne n8,
      Function.update_of_ne n7, Function.update_of_ne n6]
    rw [h5e r n4 n5, h4e r n1 n2 n3 n4, h3e r n4 n5, h2e r n1 n2 n3 n4]
  -- the columns
  obtain ⟨s9, r9, h9D2, h9D, h9Dl2, h9F2, h9Aux, h9Rec, h9S, h9p, h9o, h9e⟩ :=
    p3Cols_good (x := x) hw s8 u π cs (base + sqOff tern a n) (sqStr tern) [] []
      (st.stk qRec) hs hk (by nlinarith) hℓw huw hnw hsw
      (by rw [hpre8.env_of (by decide), hD])
      (by rw [hpre8.stk_of (by decide), hDom2, List.append_nil])
      (by rw [hpre8.stk_of (by decide), hDom]) (by rw [hpre8.stk_of (by decide), hAux])
      (by simp [s8, s7, Function.update_of_ne (show rCur ≠ rSq by decide), Ex.eval])
      (by rw [hpre8.env_of (by decide), hL])
      (by rw [hsuf2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]; simp [s1])
      (by simp [s8]) (by rw [hpre8.env_of (by decide), hStr])
      (by simp only [s8, s7, s6, NSt.set_stk, NSt.setS_stk, Function.update_of_ne
        (show qDl2 ≠ qF2 by decide)]; exact h5Dl2)
      (by simp [s8, s7, s6])
      (by simp [s8, s7, s6, Function.update_of_ne (show rFi ≠ rSq by decide),
        Function.update_of_ne (show rFi ≠ rCur by decide)])
      (by rw [hpre8.stk_of (by decide)])
  have hb9 := (hpre8.seq r9).bdd hw hb hpx
  obtain ⟨s10, r10, h10S, h10p, h10o, h10e⟩ := moveAllS_good (x := x) hw (q := qDom)
    (q' := qDom2) (t := rT) (f := rT2) (by decide) (by decide) s9 hb9.1
  have hb10 := ((hpre8.seq r9).seq r10).bdd hw hb hpx
  obtain ⟨s11, r11, h11S, h11p, h11o, h11e⟩ := moveAllS_good (x := x) hw (q := qF2)
    (q' := qJunk) (t := rT) (f := rT2) (by decide) (by decide) s10 hb10.1
  have hb11 := (((hpre8.seq r9).seq r10).seq r11).bdd hw hb hpx
  obtain ⟨s12, r12, h12S, h12p, h12o, h12e⟩ := moveAllS_good (x := x) hw (q := qDl2)
    (q' := qJunk) (t := rT) (f := rT2) (by decide) (by decide) s11 hb11.1
  have r13 := Good.set (x := x) (w := w) (r := rAi) (e := .add (rv rAi) (.const 1)) (st := s12)
    (by
      have : s12.env rAi = a := by
        rw [h12e _ (by decide) (by decide), h11e _ (by decide) (by decide),
          h10e _ (by decide) (by decide), h9e _ (by decide), hpre8.env_of (by decide), hAi]
      simp only [Ex.Fits, Ex.eval, rv, this]; omega)
  set s13 := s12.set rAi (Ex.eval s12.env (.add (rv rAi) (.const 1)))
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq
    (r11.seq (r12.seq r13)))))))))))
  have hsuf2 := r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq
    (r11.seq (r12.seq r13))))))))))
  have hsuf4 := r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12.seq r13))))))))
  have hsuf5 := r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12.seq r13)))))))
  have hsuf6 := r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12.seq r13))))))
  have hsuf10 := r10.seq (r11.seq (r12.seq r13))
  have hsuf11 := r11.seq (r12.seq r13)
  have hsuf12 := r12.seq r13
  have hlen9 : (s9.stk qDom).length = n * (ℓ + 1) := by
    rw [h9D, List.append_nil, List.length_reverse, List.length_flatMap]
    have : cs.map (fun c => (cdesc c).length) = cs.map fun _ => ℓ + 1 :=
      List.map_congr_left fun c _ => length_cdesc c
    rw [this, sum_map_const]
  have hlen10 : (s10.stk qF2).length ≤ k := by
    rw [h10S, Function.update_of_ne (by decide), Function.update_of_ne (by decide), h9F2]
    simp [hfk]
  have hlen11 : (s11.stk qDl2).length ≤ k * ℓ := by
    rw [h11S, Function.update_of_ne (by decide), Function.update_of_ne (by decide), h10S,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), h9Dl2, ← hdk]
    exact length_flatten_drop_le _ _
  have hlenF : (s2.stk qF).length = k := by rw [h2F, List.length_reverse, hfk]
  have hlenD : (s4.stk qDl).length = k * ℓ := by rw [h4Dl, List.length_reverse, hdk]
  have hP : (encodeNats (permDescription π)).length =
      (encodeNats (fL π)).length + (encodeNats (dL π).flatten).length := by
    rw [permDescription_eq, encodeNats_append, List.length_append]
  refine ⟨s13, hall.mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hall.out_of (by decide),
    fun r hr => hall.env_of hr⟩
  · rw [hlenF, hlenD, hlen9, hP, hfk, hdk]
    simp only [condCost, Ex.size, rv]
    have hlf : k ≤ (encodeNats (fL π)).length := by
      have := length_le_encodeNats (fL π); rwa [hfk] at this
    have hld : k * ℓ ≤ (encodeNats (dL π).flatten).length := by
      have := length_le_encodeNats (dL π).flatten; rwa [hdk] at this
    have := arg_arith (Ex.nodeCost w) (unitCost w) k n ℓ (encodeNats (fL π)).length
      (encodeNats (dL π).flatten).length _ _ hU0 hU' hk hlf hld hlen10 hlen11
    linarith
  · rw [hsuf2.stk_of (by decide)]; simp [s1]
  · rw [hsuf4.stk_of (by decide), h3S, Function.update_of_ne (by decide), Function.update_self]
  · rw [hsuf12.stk_of (by decide)]
    show s11.stk qF2 = []
    rw [h11S, Function.update_of_ne (by decide), Function.update_self]
  · rw [hsuf6.stk_of (by decide), h5S, Function.update_of_ne (by decide), Function.update_self]
  · show s12.stk qDl2 = []
    rw [h12S, Function.update_of_ne (by decide), Function.update_self]
  · rw [hsuf11.stk_of (by decide), h10S, Function.update_of_ne (by decide), Function.update_self]
  · rw [hsuf11.stk_of (by decide), h10S, Function.update_self, h9D, h9D2]; simp
  · rw [hsuf10.stk_of (by decide), h9Aux]
  · rw [hsuf10.stk_of (by decide), h9Rec]
  · intro q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
    exact hall.stk_of (by
      simp [p3Arg, p3Seq, p3Cols, p3Col, p3Advs, p3Adv, p3Bits, p3Bit, moveN, moveAllS, rdNumsS,
        rdNumS, wStk, Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6,
        Ne.symm n7, Ne.symm n8, Ne.symm n9, Ne.symm n10])
  · simp only [s13, NSt.set_env, Function.update_self, Ex.eval, rv]
    rw [h12e _ (by decide) (by decide), h11e _ (by decide) (by decide),
      h10e _ (by decide) (by decide), h9e _ (by decide), hpre8.env_of (by decide), hAi]
  · rw [hsuf5.pos_of (by decide), h4p, h3p, h2p, hP]; simp [s1]; ring

end Lax119563Proofs.Compiler
