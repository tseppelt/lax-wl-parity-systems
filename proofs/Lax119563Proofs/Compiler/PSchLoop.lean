import Lax119563Proofs.Compiler.PSch

/-!
# Pass `P2`: the schema loop and the pass (`p2Sch_good`, `p2_good`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## One schema -/

/-- The sum of the sizes of the first `j` schemas. -/
noncomputable def lbUpTo (j : ℕ) : ℕ := (((List.finRange I.schemas.length).take j).map (schSize I)).sum

lemma lbUpTo_succ {j : ℕ} (hj : j < I.schemas.length) :
    lbUpTo I (j + 1) = lbUpTo I j + schSize I ⟨j, hj⟩ := by
  rw [lbUpTo, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [lbUpTo]

lemma lbUpTo_le (j : ℕ) : lbUpTo I j ≤ locBase I := by
  rw [lbUpTo, locBase]
  conv_rhs => rw [← List.take_append_drop j (List.finRange I.schemas.length)]
  rw [List.map_append, List.sum_append]; omega

lemma lbUpTo_all : lbUpTo I I.schemas.length = locBase I := by
  rw [lbUpTo, locBase, List.take_of_length_le (by simp)]

lemma schRecsUpTo_succ {j : ℕ} (hj : j < I.schemas.length) :
    schRecsUpTo I (j + 1) = schRecsUpTo I j ++ schRec I ⟨j, hj⟩ := by
  rw [schRecsUpTo, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [schRecsUpTo]

/-- The invariant of the schema loop. -/
def p2Inv (st s : NSt CR CQ) : Prop :=
  s.env rJ ≤ I.schemas.length ∧ s.env rE = I.schemas.length ∧ s.env rL = ℓ ∧ s.env rKk = k ∧
    s.env rKm1 = k - 1 ∧ s.env rK1 = k + 1 ∧ s.env rPL = k * (ℓ + 1) ∧
    s.env rLB = lbUpTo I (s.env rJ) ∧ s.pos = schAt I (s.env rJ) ∧
    s.stk = Function.update st.stk qSch ((schRecsUpTo I (s.env rJ)).reverse ++ st.stk qSch) ∧
    s.out = st.out

lemma arity_le (s : Schema k ℓ I.numLocations) : arity s ≤ 3 := by
  unfold arity; split_ifs <;> omega

lemma lt_arity_iff (s : Schema k ℓ I.numLocations) :
    (if 2 < arity s then 1 else 0) = (if Matrix.isTern s then 1 else 0) := by
  unfold arity; split_ifs <;> simp_all

lemma p2Sch_cost_arith (N U la ll lo ld ℓ lc d k a lp pl : ℕ) (hU : U ≤ N) (hU' : 64 ≤ U)
    (hd : d ≤ lc) (hℓ : ℓ ≤ lp) (hk : k ≤ lp) (hp : pl ≤ lp) (ha : a ≤ 3) (hlo : lo ≤ ll) :
    (la + 1) * (20 * N) +
      ((1 + 1 + 1) * N + U +
        ((ll + lo + 1) * (20 * N) +
          ((ld + 1) * (20 * N) +
            (12 * N +
              ((ℓ + 1) * (12 * N) +
                (150 * N * lc + d * (150 * N + ((1 + 1 + 1) * N + 1)) + ((1 + 1 + 1) * N + 1) +
                  ((ℓ + k + 10) * (60 * N) +
                    ((a + 1) * (12 * N) +
                      ((lp + pl + 1) * (20 * N) + ((1 + 1 + 1) * N + U)))))))))) ≤
    400 * N * (la + ll + ld + lc + lp) + 1000 * N := by
  have m1 := Nat.mul_le_mul_left N hd
  have m2 := Nat.mul_le_mul_left N hℓ
  have m3 := Nat.mul_le_mul_left N hk
  have m4 := Nat.mul_le_mul_left N hp
  have m6 := Nat.mul_le_mul_left N ha
  have m9 := Nat.mul_le_mul_left N hlo
  have m7 : d ≤ N * lc := le_trans hd (Nat.le_mul_of_pos_left _ (by omega))
  nlinarith

set_option maxHeartbeats 6000000 in
/-- One schema. -/
lemma p2Sch_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hkH : k ≤ H I) (hℓ : ℓ ≤ H I)
    (hS : 16 * (H I + locBase I + 1) ≤ 2 ^ w) (st : NSt CR CQ) (hq1 : st.stk qOr = [])
    (hq2 : st.stk qOr2 = []) (s : NSt CR CQ) (hI : p2Inv I st s)
    (hc : (Ex.lt (rv rJ) (rv rE)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p2Sch s s'
        (400 * Ex.nodeCost w * ((H I - s.pos) - (H I - s'.pos)) + 1000 * Ex.nodeCost w) ∧
      p2Inv I st s' ∧ I.schemas.length - s'.env rJ < I.schemas.length - s.env rJ ∧
      H I - s'.pos ≤ H I - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  have h3H := three_le_H I
  obtain ⟨hJ, hE, hL, hKk, hKm, hK1, hPL, hLB, hpos, hstk, hout⟩ := hI
  have hlt : s.env rJ < I.schemas.length := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hE]; rw [if_neg h]
  obtain ⟨j, hjdef⟩ : ∃ j, s.env rJ = j := ⟨_, rfl⟩
  rw [hjdef] at hlt hLB hpos hstk
  set e : Fin I.schemas.length := ⟨j, hlt⟩
  set sc := sch I e
  set D := coordList (dom I e)
  set d := D.length
  set a := arity sc
  set tern := Matrix.isTern sc
  set locs := schLocs sc
  set perms := (schPerms sc).flatMap permDescription
  have hschD : schD I e = a :: locs ++ (d :: D.flatMap cdesc) ++ perms := by
    rw [schD, schemaDescription_eq']; rfl
  set rest := encodeNats (schsSuf I (j + 1))
  have hx : (encodeSystem I).drop s.pos = encodeNat a ++ (encodeNats locs ++
      (encodeNat d ++ (encodeNats (D.flatMap cdesc) ++ (encodeNats perms ++ rest)))) := by
    rw [hpos, drop_schAt, schsSuf_cons I hlt, encodeNats_append, hschD]
    simp only [List.cons_append, List.append_assoc, encNats_cons, encodeNats_append]
    rfl
  have hΔ : (encodeNats (schD I e)).length = (encodeNat a).length + (encodeNats locs).length +
      (encodeNat d).length + (encodeNats (D.flatMap cdesc)).length + (encodeNats perms).length := by
    rw [hschD]
    simp only [List.cons_append, List.append_assoc, encNats_cons, encodeNats_append,
      List.length_append]; ring
  have hsch : schAt I (j + 1) = schAt I j + (encodeNats (schD I e)).length := schAt_succ I hlt
  have hschle := schAt_le I (j + 1)
  have ha3 : a ≤ 3 := arity_le I sc
  have hlocs : locs.length = a := length_schLocs sc
  have hperms : perms.length = a * (k + k * ℓ) := length_perms sc
  have hcl : (D.flatMap cdesc).length = d * (ℓ + 1) := by
    rw [List.length_flatMap]
    simp [length_cdesc, d]
  have hpe : perms.length ≤ (encodeNats perms).length := length_le_encodeNats _
  have hce : (D.flatMap cdesc).length ≤ (encodeNats (D.flatMap cdesc)).length :=
    length_le_encodeNats _
  have hle_e : (encodeNats (schD I e)).length ≤ H I := schD_le_H I e
  have ha2 : 2 ≤ a := by unfold a arity; split_ifs <;> omega
  have hdH : d ≤ H I := by nlinarith
  have hkp : k ≤ perms.length := by rw [hperms]; nlinarith
  have hℓp : ℓ ≤ perms.length := by rw [hperms]; nlinarith
  have hPLH : k * (ℓ + 1) * a ≤ H I := by
    have : k * (ℓ + 1) * a = perms.length := by rw [hperms]; ring
    omega
  -- sizes
  have hsz := schSize_eq' I e
  have hne := nEnt_eq I e
  have hlb : lbUpTo I j + schSize I e ≤ locBase I := by
    have := lbUpTo_le I (j + 1); rwa [lbUpTo_succ I hlt] at this
  have hrs : rowsSum D ≤ locBase I := by
    have : rowsSum D ≤ nEnt I e := by rw [hne]; nlinarith
    omega
  -- arity
  have r1 := rdNumS_good (Q := CQ) hw (r := rA) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s a _ hx (bits_lt_of_le (by omega) hH2)
  set s1 := rdNumFinal s rA rP rT a
  have e1A : s1.env rA = a := rdNumFinal_env_r (by decide) (by decide) _
  have r2 := Good.set (x := encodeSystem I) (w := w) (st := s1) (r := rTern)
    (e := .lt (.const 2) (rv rA)) (by simp only [Ex.Fits, rv, e1A]; omega)
  set s2 := s1.set rTern ((Ex.lt (.const 2) (rv rA)).eval s1.env)
  have e2T : s2.env rTern = if tern then 1 else 0 := by
    simp only [s2, NSt.set_env, Function.update_self, Ex.eval, rv, e1A]
    exact lt_arity_iff I sc
  have e2A : s2.env rA = a := by
    simp only [s2, NSt.set_env, Function.update_of_ne (show rA ≠ rTern by decide)]; exact e1A
  have hx2 : (encodeSystem I).drop s2.pos = encodeNats locs ++
      (encodeNat d ++ (encodeNats (D.flatMap cdesc) ++ (encodeNats perms ++ rest))) := by
    show (encodeSystem I).drop (s.pos + (encodeNat a).length) = _
    rw [drop_add, hx, List.drop_left]
  obtain ⟨s3, r3, hs3, hp3, ho3, he3⟩ := skipNumsS_good (x := encodeSystem I) (w := w)
    (Q := CQ) hw (n := rA) (i := rI) (t := rT) (by decide) (by decide) (by decide) s2 locs _ hx2
    (by rw [e2A, hlocs]) (by omega)
  have hx3 : (encodeSystem I).drop s3.pos = encodeNat d ++
      (encodeNats (D.flatMap cdesc) ++ (encodeNats perms ++ rest)) := by
    rw [hp3, drop_add, hx2, List.drop_left]
  have r4 := rdNumS_good (Q := CQ) hw (r := rD) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s3 d _ hx3 (bits_lt_of_le hdH hH2)
  set s4 := rdNumFinal s3 rD rP rT d
  have e4 : ∀ q, q ≠ rD → q ≠ rP → q ≠ rT → s4.env q = s3.env q :=
    fun q h1 h2 h3 => rdNumFinal_env_ne h1 h2 h3 _
  -- registers from `s` to `s4`
  have k04 : ∀ q, CStm.wReg q (.seq (rdNumS rA rP rT) (.seq (.set rTern (.lt (.const 2) (rv rA)))
      (.seq (skipNumsS rA rI rT) (rdNumS rD rP rT))) : CStm CR CQ) = false →
      s4.env q = s.env q := fun q hq => (r1.seq (r2.seq (r3.seq r4))).env_of hq
  have e4Kk : s4.env rKk = k := by rw [k04 _ (by decide), hKk]
  -- initialisation
  have hI5 : ∃ s5, Good (encodeSystem I) w p2Init s4 s5 (12 * Ex.nodeCost w) ∧
      s5.env rRows = 0 ∧ s5.env rCol = 0 ∧ s5.env rDist = 0 ∧ s5.env rLast = 0 ∧
      s5.env rPrev = k ∧ s5.env rK = 0 ∧ s5.pos = s4.pos ∧ s5.stk = s4.stk ∧ s5.out = s4.out ∧
      ∀ q, CStm.wReg q p2Init = false → s5.env q = s4.env q := by
    set t1 := s4.set rRows 0
    set t2 := t1.set rCol 0
    set t3 := t2.set rDist 0
    set t4 := t3.set rLast 0
    set t5 := t4.set rPrev k
    have g1 : Good (encodeSystem I) w (.set rRows (.const 0) : CStm CR CQ) s4 t1
        (Ex.nodeCost w + unitCost w) := (CStm.Good.set (by simp only [Ex.Fits]; omega)).mono (by simp [Ex.size])
    have g2 : Good (encodeSystem I) w (.set rCol (.const 0) : CStm CR CQ) t1 t2
        (Ex.nodeCost w + unitCost w) := (CStm.Good.set (by simp only [Ex.Fits]; omega)).mono (by simp [Ex.size])
    have g3 : Good (encodeSystem I) w (.set rDist (.const 0) : CStm CR CQ) t2 t3
        (Ex.nodeCost w + unitCost w) := (CStm.Good.set (by simp only [Ex.Fits]; omega)).mono (by simp [Ex.size])
    have g4 : Good (encodeSystem I) w (.set rLast (.const 0) : CStm CR CQ) t3 t4
        (Ex.nodeCost w + unitCost w) := (CStm.Good.set (by simp only [Ex.Fits]; omega)).mono (by simp [Ex.size])
    have ht4 : t4.env rKk = k := by
      simp [t4, t3, t2, t1, Function.update_of_ne (show rKk ≠ rLast by decide),
        Function.update_of_ne (show rKk ≠ rDist by decide),
        Function.update_of_ne (show rKk ≠ rCol by decide),
        Function.update_of_ne (show rKk ≠ rRows by decide), e4Kk]
    have g5 : Good (encodeSystem I) w (.set rPrev (rv rKk) : CStm CR CQ) t4 t5
        (Ex.nodeCost w + unitCost w) :=
      (CStm.Good.set (by simp only [Ex.Fits, rv, ht4]; omega)).of_eq
        (by simp only [Ex.eval, rv, ht4, t5]) (by simp [Ex.size])
    have g6 : Good (encodeSystem I) w (.set rK (.const 0) : CStm CR CQ) t5 (t5.set rK 0)
        (Ex.nodeCost w + unitCost w) := (CStm.Good.set (by simp only [Ex.Fits]; omega)).mono (by simp [Ex.size])
    have g := g1.seq (g2.seq (g3.seq (g4.seq (g5.seq g6))))
    refine ⟨_, g.mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, fun q hq => g.env_of hq⟩
    · omega
    all_goals simp [t5, t4, t3, t2, t1, NSt.set, Function.update_apply, rRows, rK, rPrev, rCol, rDist, rLast]
  obtain ⟨s5, r5, e5R, e5C, e5D, e5L, e5P, e5K, hp5, hs5, ho5, k45⟩ := hI5
  -- the OR stack
  have e5L' : s5.env rL = ℓ := by rw [k45 _ (by decide), k04 _ (by decide), hL]
  have r6 := pushZS_good (x := encodeSystem I) (w := w) (q := qOr) hw (n := rL) (j := rI)
    (by decide) s5 e5L' (by omega)
  set s6 := (s5.setS qOr (List.replicate ℓ 0 ++ s5.stk qOr)).set rI ℓ
  have hst4 : s4.stk = s.stk := by
    rw [show s4.stk = s3.stk from rfl, hs3]; rfl
  have hs6 : s6.stk = Function.update s.stk qOr (orsL ([] : List (Coord k ℓ))) := by
    simp only [s6, NSt.set_stk, NSt.setS_stk, hs5, hst4, hstk, orsL_nil]
    rw [Function.update_of_ne (show qOr ≠ qSch by decide), hq1, List.append_nil]
  have hs6' : s6.stk = Function.update (Function.update s6.stk qOr (orsL ([] : List (Coord k ℓ))))
      qOr2 [] := by
    rw [hs6]
    funext q
    by_cases h1 : q = qOr2
    · subst h1
      simp [Function.update_of_ne (show qOr2 ≠ qOr by decide), hstk,
        Function.update_of_ne (show qOr2 ≠ qSch by decide), hq2]
    · by_cases h2 : q = qOr
      · subst h2; simp [Function.update_of_ne h1]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  have e6 : ∀ q, q ≠ rI → s6.env q = s5.env q := fun q h => by
    simp [s6, Function.update_of_ne h]
  -- the coordinates
  have hx6 : (encodeSystem I).drop s6.pos = encodeNats (D.flatMap cdesc) ++
      (encodeNats perms ++ rest) := by
    show (encodeSystem I).drop s5.pos = _
    rw [hp5]
    show (encodeSystem I).drop (s3.pos + (encodeNat d).length) = _
    rw [drop_add, hx3, List.drop_left]
  have k46 : ∀ q, q ≠ rI → CStm.wReg q p2Init = false → s6.env q = s4.env q :=
    fun q h1 h2 => by rw [e6 q h1, k45 q h2]
  have e4D : s4.env rD = d := rdNumFinal_env_r (by decide) (by decide) _
  have e4T : s4.env rTern = if tern then 1 else 0 := by
    rw [e4 _ (by decide) (by decide) (by decide), r3.env_of (r := rTern) (by decide), e2T]
  have hI6 : p2CoordInv D tern s6.pos s6.stk s6.out s6 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · rw [e6 _ (by decide), e5K]; omega
    · rw [k46 _ (by decide) (by decide), e4D]
    · rw [k46 _ (by decide) (by decide), k04 _ (by decide), hL]
    · rw [k46 _ (by decide) (by decide), e4Kk]
    · rw [k46 _ (by decide) (by decide), k04 _ (by decide), hKm]
    · rw [k46 _ (by decide) (by decide), e4T]
    · rw [e6 _ (by decide), e5R, e6 _ (by decide), e5K]; rfl
    · rw [e6 _ (by decide), e5C, e6 _ (by decide), e5K]; simp
    · rw [e6 _ (by decide), e5D, e6 _ (by decide), e5K]; rfl
    · rw [e6 _ (by decide), e5P, e6 _ (by decide), e5K]; rfl
    · rw [e6 _ (by decide), e5L, e6 _ (by decide), e5K]; simp
    · rw [e6 _ (by decide), e5K]; simp [encodeNats]
    · rw [e6 _ (by decide), e5K, List.take_zero]; exact hs6'
  obtain ⟨s7, r7, hI7, hc7⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rK) (rv rD)) (body := p2Coord) (p2CoordInv D tern s6.pos s6.stk s6.out)
    (fun s => d - s.env rK) (fun s' => s6.pos + (encodeNats (D.flatMap cdesc)).length - s'.pos)
    (150 * Ex.nodeCost w) (150 * Ex.nodeCost w) (fun s' hI' => ⟨by
      obtain ⟨hK', hD', -⟩ := hI'
      simp only [Ex.Fits, rv, hD']; omega,
      fun hc' => p2Coord_good I hw D hkH hℓ hdH (by omega) tern s6.pos s6.stk s6.out _ hx6
        s' hI' hc'⟩) s6 hI6
  obtain ⟨hK7, hD7, hL7, hKk7, hKm7, hT7, hR7, hC7, hDi7, hP7, hLa7, hp7, hs7, ho7⟩ := hI7
  have hK7' : s7.env rK = d := by
    simp only [Ex.eval, rv, hD7] at hc7; split_ifs at hc7 with h <;> omega
  rw [hK7', List.take_of_length_le le_rfl] at hR7 hDi7 hLa7 hp7 hs7
  rw [hK7'] at hC7
  -- the numbers
  set Lt := if ∃ c ∈ D, ¬ (c.1 : ℕ) + 1 < k then 1 else 0
  set Dt := dChg k (D.map fun c => (c.1 : ℕ))
  have hBR : (if Lt ≠ 0 then k - 1 else Dt) = blkRows D := by
    rw [blkRows_eq]
    by_cases h : ∃ c ∈ D, ¬ (c.1 : ℕ) + 1 < k
    · rw [if_pos h, if_pos (by simp only [Lt, if_pos h]; omega)]
    · rw [if_neg h, if_neg (by simp only [Lt, if_neg h]; omega)]
  have hors7 : s7.stk qOr = orsL D := by
    rw [hs7, Function.update_of_ne (show qOr ≠ qOr2 by decide), Function.update_self]
  have k47 : ∀ q, CStm.wReg q (.seq p2Init (.seq (pushZS qOr rL rI)
      (.loop (.lt (rv rK) (rv rD)) p2Coord)) : CStm CR CQ) = false → s7.env q = s4.env q :=
    fun q hq => (r5.seq (r6.seq r7)).env_of hq
  have e7K1 : s7.env rK1 = k + 1 := by rw [k47 _ (by decide), k04 _ (by decide), hK1]
  have e7LB : s7.env rLB = lbUpTo I j := by rw [k47 _ (by decide), k04 _ (by decide), hLB]
  have hDt : Dt ≤ H I := (dChg_le _ _).trans (by simp [Dt]; omega)
  have hsum : (orsL D).sum = orPop D := sum_orsL D
  have hcoef := length_coefSteps I e
  have hszv : d * colV tern + 6 * (rowsSum D * (k + 1)) +
      2 * (((if Lt ≠ 0 then k - 1 else Dt) + (orsL D).sum) * (k + 1)) = schSize I e := by
    rw [hsz, hne, hcoef, hBR, hsum]
    simp only [colV, tern]; ring
  obtain ⟨s8, r8, e8LB, hs8, hp8, ho8⟩ := p2Fin_good I hw s7 (orsL D) hors7 (length_orsL D)
    (orsL_le D) hL7 hKm7 e7K1 hLa7 (by simp only [Lt]; split_ifs <;> omega) hDi7 hR7 hC7 e7LB
    (by omega)
  -- the permutations
  have k48 : ∀ q, CStm.wReg q (.seq p2Init (.seq (pushZS qOr rL rI)
      (.seq (.loop (.lt (rv rK) (rv rD)) p2Coord) p2Fin)) : CStm CR CQ) = false →
      s8.env q = s4.env q :=
    fun q hq => (r5.seq (r6.seq (r7.seq r8))).env_of hq
  have e8PL : s8.env rPL = k * (ℓ + 1) := by rw [k48 _ (by decide), k04 _ (by decide), hPL]
  have e8A : s8.env rA = a := by
    rw [k48 _ (by decide), e4 _ (by decide) (by decide) (by decide),
      r3.env_of (r := rA) (by decide), e2A]
  have r9 := mulS_good (x := encodeSystem I) (w := w) (Q := CQ) (dst := rPN) (a := rPL)
    (b := rA) (j := rJ2) hw (by decide) (by decide) (by decide) (by decide) (by decide) s8 e8PL
    e8A (by omega) (by omega)
  set s9 := (s8.set rPN (k * (ℓ + 1) * a)).set rJ2 a
  have hx9 : (encodeSystem I).drop s9.pos = encodeNats perms ++ rest := by
    show (encodeSystem I).drop s8.pos = _
    rw [hp8, hp7]
    rw [drop_add, hx6, List.drop_left]
  obtain ⟨s10, r10, hs10, hp10, ho10, he10⟩ := skipNumsS_good (x := encodeSystem I) (w := w)
    (Q := CQ) hw (n := rPN) (i := rI) (t := rT) (by decide) (by decide) (by decide) s9 perms _
    hx9 (by simp [s9, Function.update_of_ne (show rPN ≠ rJ2 by decide), hperms]; ring)
    (by omega)
  have r11 := Good.set (x := encodeSystem I) (w := w) (st := s10) (r := rJ)
    (e := .add (rv rJ) (.const 1)) (by
      have : s10.env rJ = j := by
        rw [he10 _ (by decide) (by decide)]
        simp only [s9, NSt.set_env, Function.update_of_ne (show rJ ≠ rJ2 by decide),
          Function.update_of_ne (show rJ ≠ rPN by decide)]
        rw [k48 _ (by decide), k04 _ (by decide), hjdef]
      have := E_le I
      simp only [Ex.Fits, Ex.eval, rv, this]; omega)
  set s11 := s10.set rJ ((Ex.add (rv rJ) (.const 1)).eval s10.env)
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq
    (r10.seq r11)))))))))
  have htail := r9.seq (r10.seq r11)
  have e11J : s11.env rJ = j + 1 := by
    simp only [s11, NSt.set_env, Function.update_self, Ex.eval, rv]
    rw [he10 _ (by decide) (by decide)]
    simp only [s9, NSt.set_env, Function.update_of_ne (show rJ ≠ rJ2 by decide),
      Function.update_of_ne (show rJ ≠ rPN by decide)]
    rw [k48 _ (by decide), k04 _ (by decide), hjdef]
  have hp11 : s11.pos = s.pos + (encodeNats (schD I e)).length := by
    have q10 : s11.pos = s9.pos + (encodeNats perms).length := hp10
    have q9 : s9.pos = s8.pos := rfl
    have q6 : s6.pos = s4.pos := by show s5.pos = _; exact hp5
    have q4 : s4.pos = s3.pos + (encodeNat d).length := rfl
    have q2 : s2.pos = s.pos + (encodeNat a).length := rfl
    rw [q10, q9, hp8, hp7, q6, q4, hp3, q2, hΔ]; ring
  refine ⟨s11, hall.mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hp11]
    have hΔ' : H I - s.pos - (H I - (s.pos + (encodeNats (schD I e)).length)) =
        (encodeNats (schD I e)).length := by rw [hpos]; omega
    rw [hΔ', hΔ]
    have hφ6 : s6.pos + (encodeNats (D.flatMap cdesc)).length - s6.pos =
        (encodeNats (D.flatMap cdesc)).length := by omega
    have hμ6 : d - s6.env rK = d := by rw [e6 _ (by decide), e5K]; rfl
    rw [hφ6, hμ6]
    have hel : a ≤ (encodeNats locs).length := hlocs ▸ length_le_encodeNats locs
    have hdc : d ≤ (encodeNats (D.flatMap cdesc)).length :=
      le_trans (Nat.le_mul_of_pos_right d (by omega)) (hcl ▸ hce)
    simp only [condCost, Ex.size, rv]
    exact p2Sch_cost_arith _ _ _ _ _ _ _ _ _ _ _ _ _ hU hU' hdc (by omega) (by omega) hpe ha3
      (length_le_encodeNats locs)
  · rw [e11J]; omega
  · rw [hall.env_of (by decide), hE]
  · rw [hall.env_of (by decide), hL]
  · rw [hall.env_of (by decide), hKk]
  · rw [hall.env_of (by decide), hKm]
  · rw [hall.env_of (by decide), hK1]
  · rw [hall.env_of (by decide), hPL]
  · rw [e11J, show lbUpTo I (j + 1) = lbUpTo I j + schSize I e from lbUpTo_succ I hlt,
      htail.env_of (by decide), e8LB, ← hszv]; ring
  · rw [e11J, hp11, hpos, hsch]
  · rw [e11J]
    show s10.stk = _
    rw [hs10]
    show s8.stk = _
    rw [hs8]
    funext q
    by_cases h1 : q = qSch
    · subst h1
      simp only [Function.update_self, hs7, hs6, hstk,
        Function.update_of_ne (show qSch ≠ qOr2 by decide),
        Function.update_of_ne (show qSch ≠ qOr by decide)]
      rw [show schRecsUpTo I (j + 1) = schRecsUpTo I j ++ schRec I e from
        schRecsUpTo_succ I hlt]
      simp only [schRec, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, List.singleton_append, List.append_assoc, hne, hcoef,
        hBR, hsum, List.cons.injEq]
      refine ⟨by ring, by ring, rfl, rfl⟩
    · rw [Function.update_of_ne h1, Function.update_of_ne h1]
      by_cases h2 : q = qOr
      · subst h2; rw [Function.update_self, hq1]
      · rw [Function.update_of_ne h2, hs7]
        by_cases h3 : q = qOr2
        · subst h3; rw [Function.update_self, hq2]
        · rw [Function.update_of_ne h3, Function.update_of_ne h2, hs6, Function.update_of_ne h2,
            hstk, Function.update_of_ne h1]
  · rw [hall.out_of (by decide), hout]
  · rw [e11J]; omega
  · rw [hp11]; omega

/-! ## The pass -/

lemma schsPre_all : schsPre I I.schemas.length = schsDesc I := by
  rw [schsPre, schsDesc_eq, List.take_of_length_le (by simp)]

lemma schAt_all : schAt I I.schemas.length = H I := by
  rw [schAt, schsPre_all, schPos_add]

lemma kl_le_H (hE : I.schemas ≠ []) : k * (ℓ + 1) ≤ H I := by
  have hj : 0 < I.schemas.length := List.length_pos_of_ne_nil hE
  have h1 := schD_length_le I ⟨0, hj⟩
  rw [schD, schemaDescription_eq'] at h1
  have h2 := length_perms (sch I ⟨0, hj⟩)
  have h3 : 2 ≤ arity (sch I ⟨0, hj⟩) := by unfold arity; split_ifs <;> omega
  simp only [List.length_append, List.length_cons] at h1
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **Pass `P2`.** Run at the position of `E` (after `p1r`) with `rKk = k`, `rL = ℓ`,
`rL1 = ℓ + 1` and empty stacks `qOr`, `qOr2`, `p2` computes `rLB = locBase I` and pushes the
schema records onto `qSch`, ending at the end of the input. -/
theorem p2_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hE : I.schemas ≠ [])
    (hS : 16 * (H I + locBase I + 1) ≤ 2 ^ w) (st : NSt CR CQ)
    (hp : st.pos = posAt I I.numLocations) (hKk : st.env rKk = k) (hL : st.env rL = ℓ)
    (hL1 : st.env rL1 = ℓ + 1) (hq1 : st.stk qOr = []) (hq2 : st.stk qOr2 = []) :
    ∃ st', Good (encodeSystem I) w p2 st st' (2000 * (H I + 1) * Ex.nodeCost w) ∧
      st'.env rLB = locBase I ∧
      st'.stk = Function.update st.stk qSch
        ((schRecsUpTo I I.schemas.length).reverse ++ st.stk qSch) ∧
      st'.out = st.out ∧ st'.pos = H I ∧
      ∀ r, CStm.wReg r p2 = false → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  have hkH := k_le_H I hE
  have hℓ := ell_le_H I hk (fun h => hE h.2)
  have hEH := E_le I
  have hPLH := kl_le_H I hE
  have hx : (encodeSystem I).drop st.pos = encodeNat I.schemas.length ++
      encodeNats (schsDesc I) := by rw [hp, drop_posAt_W]
  have r1 := rdNumS_good (Q := CQ) hw (r := rE) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) st I.schemas.length _ hx (bits_lt_of_le hEH hH2)
  set s1 := rdNumFinal st rE rP rT I.schemas.length
  have e1 : ∀ q, q ≠ rE → q ≠ rP → q ≠ rT → s1.env q = st.env q :=
    fun q h1 h2 h3 => rdNumFinal_env_ne h1 h2 h3 _
  have r2 := predS_good (x := encodeSystem I) (w := w) (Q := CQ) hw (dst := rKm1) (n := rKk)
    (by decide) s1 (by rw [e1 _ (by decide) (by decide) (by decide), hKk]) (by omega)
  set s2 := s1.set rKm1 (k - 1)
  have e2K : s2.env rKk = k := by
    simp [s2, Function.update_of_ne (show rKk ≠ rKm1 by decide),
      e1 _ (show rKk ≠ rE by decide) (by decide) (by decide), hKk]
  have r3 := Good.set (x := encodeSystem I) (w := w) (st := s2) (r := rK1)
    (e := .add (rv rKk) (.const 1)) (by simp only [Ex.Fits, Ex.eval, rv, e2K]; omega)
  set s3 := s2.set rK1 ((Ex.add (rv rKk) (.const 1)).eval s2.env)
  have e3K : s3.env rKk = k := by
    simp only [s3, NSt.set_env, Function.update_of_ne (show rKk ≠ rK1 by decide)]; exact e2K
  have e3L1 : s3.env rL1 = ℓ + 1 := by
    simp only [s3, s2, NSt.set_env, Function.update_of_ne (show rL1 ≠ rK1 by decide),
      Function.update_of_ne (show rL1 ≠ rKm1 by decide)]
    rw [e1 _ (by decide) (by decide) (by decide), hL1]
  have r4 := mulS_good (x := encodeSystem I) (w := w) (Q := CQ) (dst := rPL) (a := rKk)
    (b := rL1) (j := rJ2) hw (by decide) (by decide) (by decide) (by decide) (by decide) s3 e3K
    e3L1 (by omega) (by omega)
  set s4 := (s3.set rPL (k * (ℓ + 1))).set rJ2 (ℓ + 1)
  have r5 := Good.set (x := encodeSystem I) (w := w) (st := s4) (r := rLB) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s5 := s4.set rLB ((Ex.const 0 : Ex CR).eval s4.env)
  have r6 := Good.set (x := encodeSystem I) (w := w) (st := s5) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s6 := s5.set rJ ((Ex.const 0 : Ex CR).eval s5.env)
  have hpre := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  have e6J : s6.env rJ = 0 := by simp [s6, Ex.eval]
  have hI6 : p2Inv I st s6 := by
    refine ⟨by rw [e6J]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(r2.seq (r3.seq (r4.seq (r5.seq r6)))).env_of (by decide)]
      exact rdNumFinal_env_r (by decide) (by decide) _
    · rw [hpre.env_of (by decide), hL]
    · rw [hpre.env_of (by decide), hKk]
    · rw [(r3.seq (r4.seq (r5.seq r6))).env_of (by decide)]; simp [s2]
    · rw [(r4.seq (r5.seq r6)).env_of (by decide)]; simp [s3, Ex.eval, rv, e2K]
    · rw [(r5.seq r6).env_of (by decide)]
      simp [s4, Function.update_of_ne (show rPL ≠ rJ2 by decide)]
    · rw [e6J, r6.env_of (by decide)]; simp [s5, Ex.eval, lbUpTo]
    · rw [e6J, schAt_zero, (r2.seq (r3.seq (r4.seq (r5.seq r6)))).pos_of (by decide)]
      show st.pos + (encodeNat I.schemas.length).length = _
      rw [hp]; rfl
    · rw [e6J]
      simp only [schRecsUpTo, List.take_zero, List.flatMap_nil, List.reverse_nil,
        List.nil_append, Function.update_eq_self]
      funext q
      exact hpre.stk_of rfl
    · exact hpre.out_of (by decide)
  obtain ⟨s7, r7, hI7, hc7⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rE)) (body := p2Sch) (p2Inv I st)
    (fun s => I.schemas.length - s.env rJ) (fun s => H I - s.pos) (400 * Ex.nodeCost w)
    (1000 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hj, hE', -⟩ := hI
      simp only [Ex.Fits, rv, hE']; omega,
      fun hc => p2Sch_good I hw hk hkH hℓ hS st hq1 hq2 s hI hc⟩) s6 hI6
  obtain ⟨hJ7, hE7, -, -, -, -, -, hLB7, hp7, hs7, ho7⟩ := hI7
  have hj : s7.env rJ = I.schemas.length := by
    simp only [Ex.eval, rv, hE7] at hc7; split_ifs at hc7 with h <;> omega
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  refine ⟨s7, hall.mono ?_, by rw [hLB7, hj, lbUpTo_all], by rw [hs7, hj], ho7,
    by rw [hp7, hj, schAt_all], fun r hr => hall.env_of hr⟩
  have hφ : H I - s6.pos ≤ H I := by omega
  have hμ : I.schemas.length - s6.env rJ ≤ H I := by omega
  have hlE : (encodeNat I.schemas.length).length ≤ H I := by
    have := congrArg List.length hx
    simp only [List.length_drop, List.length_append] at this
    show _ ≤ (encodeSystem I).length; omega
  simp only [condCost, Ex.size, rv] at *
  generalize Ex.nodeCost w = N at *
  generalize unitCost w = U at *
  generalize H I - s6.pos = φ at *
  generalize I.schemas.length - s6.env rJ = μ at *
  generalize (encodeNat I.schemas.length).length = le at *
  generalize H I = h at *
  nlinarith

end Lax119563Proofs.Compiler
