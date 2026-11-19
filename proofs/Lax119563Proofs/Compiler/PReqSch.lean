import Lax119563Proofs.Compiler.PReqArgs

/-!
# Pass `P3`, request generation: one schema

`p3Sch` reads the arity, the locations (onto `qLs2`), `|D|` and the coordinates (onto `qDom2`),
runs `p3Args`, discards the domain and adds `arity · |D|` to the sequence base `rSB`
(**`p3Sch_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ W : ℕ}

/-- **One schema.** -/
def p3Sch : CStm CR CQ :=
  .seq (rdNumS rA rP rT) (.seq (.set rTn (.lt (.const 2) (rv rA)))
    (.seq (.set rStr (.add (.const 1) (.add (rv rTn) (rv rTn))))
      (.seq (rdNumsS qLs rA rI rV rP rT) (.seq (moveAllS qLs qLs2 rT rT2)
        (.seq (rdNumS rD rP rT) (.seq (mulS rNw rD rL1 rGj)
          (.seq (rdNumsS qDom rNw rI rV rP rT) (.seq (moveAllS qDom qDom2 rT rT2)
            (.seq p3Args (.seq (moveAllS qDom2 qJunk rT rT2) (.seq (mulS rNw rA rD rGj)
              (.seq (.set rSB (.add (rv rSB) (rv rNw)))
                (.set rJ (.add (rv rJ) (.const 1)))))))))))))))

lemma tern_val (s : Schema k ℓ W) :
    (if 2 < arity s then 1 else 0) = (if Matrix.isTern s then 1 else 0) := by
  unfold arity; split_ifs <;> simp_all

lemma arity_le' (s : Schema k ℓ W) : arity s ≤ 3 := by unfold arity; split_ifs <;> omega

lemma sqStr_val (s : Schema k ℓ W) :
    1 + ((if Matrix.isTern s then 1 else 0) + (if Matrix.isTern s then 1 else 0)) =
      sqStr (Matrix.isTern s) := by
  unfold sqStr; split_ifs <;> rfl

lemma length_schPerms (s : Schema k ℓ W) : (schPerms s).length = arity s := by
  cases s <;> simp [schPerms, arity, Matrix.isTern]

lemma sqOff_le (s : Schema k ℓ W) (n : ℕ) {a : ℕ} (ha : a < arity s) :
    sqOff (Matrix.isTern s) a n + n * sqStr (Matrix.isTern s) ≤ 3 * n + 3 := by
  unfold sqOff sqStr; unfold arity at ha; split_ifs at * <;> omega

lemma length_flatMap_cdesc (cs : List (Coord k ℓ)) :
    (cs.flatMap cdesc).length = cs.length * (ℓ + 1) := by
  rw [List.length_flatMap]
  have : cs.map (fun c => (cdesc c).length) = cs.map fun _ => ℓ + 1 :=
    List.map_congr_left fun c _ => length_cdesc c
  rw [this, sum_map_const]

lemma sch_arith (N U la ll lo ln lc cl P A n ℓ : ℕ) (hU : U ≤ N) (hU' : 64 ≤ U) (hA : A ≤ 3)
    (hlo : lo = A) (hcl : cl = n * (ℓ + 1)) (hclc : cl ≤ lc) (hP : ℓ + 1 ≤ P) :
    (la + 1) * (20 * N) + ((1 + 1 + 1) * N + U + ((1 + (1 + 1 + 1) + 1) * N + U +
      ((ll + 2 * lo + 1) * (20 * N) + ((A + 1) * (10 * N) + ((ln + 1) * (20 * N) +
      ((ℓ + 1 + 1) * (12 * N) + ((lc + 2 * cl + 1) * (20 * N) + ((n * (ℓ + 1) + 1) * (10 * N) +
      (600 * (P + A * (n * (ℓ + 1) + 2) + 1) * N + ((n * (ℓ + 1) + 1) * (10 * N) +
      ((n + 1) * (12 * N) + ((1 + 1 + 1) * N + U + ((1 + 1 + 1) * N + U))))))))))))) ≤
      10000 * (la + ll + ln + lc + P + 1) * N := by
  rw [hlo]
  rw [← hcl]
  have hnX : n ≤ cl := by rw [hcl]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hY : A * (cl + 2) ≤ 3 * cl + 6 := by nlinarith
  have key : (la + 1) * (20 * N) + ((1 + 1 + 1) * N + U + ((1 + (1 + 1 + 1) + 1) * N + U +
      ((ll + 2 * A + 1) * (20 * N) + ((A + 1) * (10 * N) + ((ln + 1) * (20 * N) +
      ((ℓ + 1 + 1) * (12 * N) + ((lc + 2 * cl + 1) * (20 * N) + ((cl + 1) * (10 * N) +
      (600 * (P + A * (cl + 2) + 1) * N + ((cl + 1) * (10 * N) +
      ((n + 1) * (12 * N) + ((1 + 1 + 1) * N + U + ((1 + 1 + 1) * N + U))))))))))))) =
      (20 * (la + 1) + 3 + 5 + 20 * (ll + 2 * A + 1) + 10 * (A + 1) + 20 * (ln + 1) +
        12 * (ℓ + 2) + 20 * (lc + 2 * cl + 1) + 10 * (cl + 1) + 600 * (P + A * (cl + 2) + 1) +
        10 * (cl + 1) + 12 * (n + 1) + 3 + 3) * N + 4 * U := by ring
  rw [key]
  generalize A * (cl + 2) = Y at *
  have hE : 20 * (la + 1) + 3 + 5 + 20 * (ll + 2 * A + 1) + 10 * (A + 1) + 20 * (ln + 1) +
      12 * (ℓ + 2) + 20 * (lc + 2 * cl + 1) + 10 * (cl + 1) + 600 * (P + Y + 1) +
      10 * (cl + 1) + 12 * (n + 1) + 3 + 3 + 4 ≤ 10000 * (la + ll + ln + lc + P + 1) := by omega
  have h4 : 4 * U ≤ 4 * N := by omega
  calc _ ≤ (20 * (la + 1) + 3 + 5 + 20 * (ll + 2 * A + 1) + 10 * (A + 1) + 20 * (ln + 1) +
        12 * (ℓ + 2) + 20 * (lc + 2 * cl + 1) + 10 * (cl + 1) + 600 * (P + Y + 1) +
        10 * (cl + 1) + 12 * (n + 1) + 3 + 3) * N + 4 * N := by omega
    _ = (20 * (la + 1) + 3 + 5 + 20 * (ll + 2 * A + 1) + 10 * (A + 1) + 20 * (ln + 1) +
        12 * (ℓ + 2) + 20 * (lc + 2 * cl + 1) + 10 * (cl + 1) + 600 * (P + Y + 1) +
        10 * (cl + 1) + 12 * (n + 1) + 3 + 3 + 4) * N := by ring
    _ ≤ 10000 * (la + ll + ln + lc + P + 1) * N := Nat.mul_le_mul_right _ hE

set_option maxHeartbeats 8000000 in
/-- **One schema.** -/
lemma p3Sch_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) (hb : st.Bdd w)
    (hpx : st.pos ≤ x.length) (sc : Schema k ℓ W) (base j Hb : ℕ) (rest : List Bool)
    (hk : 1 ≤ k) (hx : x.drop st.pos = encodeNats (schemaDescription sc) ++ rest)
    (hHb : 2 * (Hb + 1) ≤ 2 ^ w) (hvals : ∀ v ∈ schemaDescription sc, v ≤ Hb)
    (hnl : (coordList sc.domain).length * (ℓ + 1) ≤ Hb) (hkl : k * ℓ + k + 1 ≤ Hb)
    (hbase : base + 3 * (coordList sc.domain).length + 3 ≤ Hb) (hj : j + 1 ≤ Hb)
    (hℓ : ℓ + 2 ≤ Hb)
    (hKk : st.env rKk = k) (hKL : st.env rKL = k * ℓ) (hL : st.env rL = ℓ)
    (hL1 : st.env rL1 = ℓ + 1) (hSB : st.env rSB = base) (hJ : st.env rJ = j)
    (hLs : st.stk qLs = []) (hLs2 : st.stk qLs2 = []) (hF : st.stk qF = [])
    (hF2 : st.stk qF2 = []) (hDl : st.stk qDl = []) (hDl2 : st.stk qDl2 = [])
    (hDom : st.stk qDom = []) (hDom2 : st.stk qDom2 = []) (hAux : st.stk qAux = []) :
    ∃ st', Good x w p3Sch st st'
        (10000 * ((encodeNats (schemaDescription sc)).length + 1) * Ex.nodeCost w) ∧
      st'.stk qLs = [] ∧ st'.stk qLs2 = [] ∧ st'.stk qF = [] ∧ st'.stk qF2 = [] ∧
      st'.stk qDl = [] ∧ st'.stk qDl2 = [] ∧ st'.stk qDom = [] ∧ st'.stk qDom2 = [] ∧
      st'.stk qAux = [] ∧
      st'.stk qRec = (argsReqs (schLocs sc) (schPerms sc) (coordList sc.domain) base
        (Matrix.isTern sc) (arity sc)).flatten.reverse ++ st.stk qRec ∧
      (∀ q, q ≠ qLs → q ≠ qLs2 → q ≠ qF → q ≠ qF2 → q ≠ qDl → q ≠ qDl2 → q ≠ qDom →
        q ≠ qDom2 → q ≠ qAux → q ≠ qRec → q ≠ qJunk → st'.stk q = st.stk q) ∧
      st'.env rSB = base + arity sc * (coordList sc.domain).length ∧ st'.env rJ = j + 1 ∧
      st'.pos = st.pos + (encodeNats (schemaDescription sc)).length ∧ st'.out = st.out ∧
      ∀ r, wReg r p3Sch = false → st'.env r = st.env r := by
  have hU0 := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have hHw : Hb < 2 ^ w := by omega
  set A := arity sc
  set locs := schLocs sc
  set perms := schPerms sc
  set cs := coordList sc.domain
  set n := cs.length
  set coords := cs.flatMap cdesc
  set tern := Matrix.isTern sc
  have hA3 : A ≤ 3 := arity_le' sc
  have hlocsA : locs.length = A := length_schLocs sc
  have hpermsA : perms.length = A := length_schPerms sc
  have hcl : coords.length = n * (ℓ + 1) := length_flatMap_cdesc cs
  have hdesc := schemaDescription_eq' sc
  have hbits : ∀ v ∈ schemaDescription sc, (Nat.bits v).length < w :=
    fun v hv => bits_lt_of_le (hvals v hv) hHb
  have hmem : ∀ v, (v ∈ [A] ∨ v ∈ locs ∨ v ∈ [n] ∨ v ∈ coords ∨
      v ∈ perms.flatMap permDescription) → v ∈ schemaDescription sc := by
    intro v hv; rw [hdesc]; simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hv ⊢
    tauto
  have hx1 : x.drop st.pos = encodeNat A ++ (encodeNats locs ++ (encodeNat n ++
      (encodeNats coords ++ (encodeNats (perms.flatMap permDescription) ++ rest)))) := by
    rw [hx, hdesc]
    simp only [List.cons_append, encNats_cons, encodeNats_append, List.append_assoc]
    rfl
  -- arity
  have r1 := rdNumS_good (Q := CQ) (x := x) hw (r := rA) (p := rP) (t := rT) (by decide)
    (by decide) (by decide) st A _ hx1 (hbits A (hmem A (by simp)))
  set s1 := rdNumFinal st rA rP rT A
  have e1A : s1.env rA = A := rdNumFinal_env_r (by decide) (by decide) A
  have r2 := Good.set (x := x) (w := w) (r := rTn) (e := .lt (.const 2) (rv rA)) (st := s1)
    (by simp only [Ex.Fits, rv, e1A]; omega)
  set s2 := s1.set rTn (Ex.eval s1.env (.lt (.const 2) (rv rA)))
  have e2T : s2.env rTn = if tern then 1 else 0 := by
    simp only [s2, NSt.set_env, Function.update_self, Ex.eval, rv, e1A]; exact tern_val sc
  have r3 := Good.set (x := x) (w := w) (r := rStr)
    (e := .add (.const 1) (.add (rv rTn) (rv rTn))) (st := s2)
    (by simp only [Ex.Fits, Ex.eval, rv, e2T]; split_ifs <;> omega)
  set s3 := s2.set rStr (Ex.eval s2.env (.add (.const 1) (.add (rv rTn) (rv rTn))))
  have e3S : s3.env rStr = sqStr tern := by
    simp only [s3, NSt.set_env, Function.update_self, Ex.eval, rv, e2T]; exact sqStr_val sc
  -- locations
  have hx3 : x.drop s3.pos = encodeNats locs ++ (encodeNat n ++
      (encodeNats coords ++ (encodeNats (perms.flatMap permDescription) ++ rest))) := by
    show x.drop s1.pos = _
    rw [rdNumFinal_pos, ← List.drop_drop, hx1, List.drop_left]
  obtain ⟨r4, h4S, h4p, h4o, h4e⟩ := rdNumsS_good (Q := CQ) (x := x) hw (q := qLs) (n := rA)
    (i := rI) (r := rV) (p := rP) (t := rT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s3 locs _ hx3
    (by rw [hlocsA]; simp [s3, s2, Function.update_of_ne (show rA ≠ rStr by decide),
      Function.update_of_ne (show rA ≠ rTn by decide), e1A]) (by omega)
    (fun v hv => hbits v (hmem v (by tauto)))
  set s4 := rnsSt s3 qLs rI rV rP rT locs locs.length
  have hb4 := (r1.seq (r2.seq (r3.seq r4))).bdd hw hb hpx
  obtain ⟨s5, r5, h5S, h5p, h5o, h5e⟩ := moveAllS_good (x := x) hw (q := qLs) (q' := qLs2)
    (t := rT) (f := rT2) (by decide) (by decide) s4 hb4.1
  have h5Ls2 : s5.stk qLs2 = locs := by
    rw [h5S, Function.update_self, h4S, Function.update_self, Function.update_of_ne (by decide)]
    simp [s3, s2, s1, hLs, hLs2]
  have h5Ls : s5.stk qLs = [] := by
    rw [h5S, Function.update_of_ne (by decide), Function.update_self]
  -- the domain
  have hx5 : x.drop s5.pos = encodeNat n ++ (encodeNats coords ++
      (encodeNats (perms.flatMap permDescription) ++ rest)) := by
    rw [h5p, h4p, ← List.drop_drop, hx3, List.drop_left]
  have r6 := rdNumS_good (Q := CQ) (x := x) hw (r := rD) (p := rP) (t := rT) (by decide)
    (by decide) (by decide) s5 n _ hx5 (hbits n (hmem n (by simp)))
  set s6 := rdNumFinal s5 rD rP rT n
  have e6D : s6.env rD = n := rdNumFinal_env_r (by decide) (by decide) n
  have hpre6 := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  have r7 := mulS_good (x := x) (w := w) (Q := CQ) hw (dst := rNw) (a := rD) (b := rL1)
    (j := rGj) (by decide) (by decide) (by decide) (by decide) (by decide) s6 e6D
    (by rw [hpre6.env_of (by decide), hL1]) (by omega) (by omega)
  set s7 := (s6.set rNw (n * (ℓ + 1))).set rGj (ℓ + 1)
  have hx7 : x.drop s7.pos = encodeNats coords ++
      (encodeNats (perms.flatMap permDescription) ++ rest) := by
    show x.drop s6.pos = _
    rw [rdNumFinal_pos, ← List.drop_drop, hx5, List.drop_left]
  obtain ⟨r8, h8S, h8p, h8o, h8e⟩ := rdNumsS_good (Q := CQ) (x := x) hw (q := qDom) (n := rNw)
    (i := rI) (r := rV) (p := rP) (t := rT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s7 coords _ hx7
    (by rw [hcl]; simp [s7, Function.update_of_ne (show rNw ≠ rGj by decide)]) (by omega)
    (fun v hv => hbits v (hmem v (by tauto)))
  set s8 := rnsSt s7 qDom rI rV rP rT coords coords.length
  have hpre8 := hpre6.seq (r7.seq r8)
  have hb8 := hpre8.bdd hw hb hpx
  obtain ⟨s9, r9, h9S, h9p, h9o, h9e⟩ := moveAllS_good (x := x) hw (q := qDom) (q' := qDom2)
    (t := rT) (f := rT2) (by decide) (by decide) s8 hb8.1
  have h9D2 : s9.stk qDom2 = coords := by
    rw [h9S, Function.update_self, h8S, Function.update_self, Function.update_of_ne (by decide)]
    have e7a : s7.stk qDom = [] := by rw [(hpre6.seq r7).stk_of (by decide), hDom]
    have e7b : s7.stk qDom2 = [] := by rw [(hpre6.seq r7).stk_of (by decide), hDom2]
    rw [e7a, e7b]; simp
  have h9D : s9.stk qDom = [] := by
    rw [h9S, Function.update_of_ne (by decide), Function.update_self]
  have hpre9 := hpre8.seq r9
  have hsuf2 := r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9))))))
  have hsuf4 := r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9))))
  have hsuf6 := r6.seq (r7.seq (r8.seq r9))
  have hsuf7 := r7.seq (r8.seq r9)
  have hx9 : x.drop s9.pos = encodeNats (perms.flatMap permDescription) ++ rest := by
    rw [h9p, h8p, ← List.drop_drop, hx7, List.drop_left]
  -- the arguments
  obtain ⟨s10, r10, h10Ls2, h10F, h10F2, h10Dl, h10Dl2, h10D, h10D2, h10Aux, h10Rec, h10S, h10p,
      h10o, h10e⟩ := p3Args_good (x := x) hw s9 (hpre9.bdd hw hb hpx).1 (hpre9.bdd hw hb hpx).2
    locs perms cs tern base rest hlocsA
    hpermsA (pairwise_blocks _) hk hx9 (by linarith) (by omega)
    (fun u hu => lt_of_le_of_lt (hvals u (hmem u (by tauto))) hHw) (by nlinarith) (by omega)
    (fun a ha => by
      have h' : sqOff tern a n + n * sqStr tern ≤ 3 * n + 3 := sqOff_le sc n ha
      show base + sqOff tern a n + n * sqStr tern < 2 ^ w
      omega)
    (fun π hπ v hv => hbits v (hmem v (Or.inr (Or.inr (Or.inr (Or.inr
      (List.mem_flatMap.mpr ⟨π, hπ, hv⟩)))))))
    (by rw [hpre9.env_of (by decide), hKk]) (by rw [hpre9.env_of (by decide), hKL])
    (by rw [hpre9.env_of (by decide), hL]) (by rw [hsuf7.env_of (by decide), e6D])
    (by rw [(r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9)))))).env_of (by decide), e2T])
    (by rw [hpre9.env_of (by decide), hSB])
    (by rw [(r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9))))).env_of (by decide), e3S])
    (by rw [hsuf2.env_of (by decide), e1A])
    (by rw [hsuf6.stk_of (by decide), h5Ls2]) (by rw [hpre9.stk_of (by decide), hF])
    (by rw [hpre9.stk_of (by decide), hF2]) (by rw [hpre9.stk_of (by decide), hDl])
    (by rw [hpre9.stk_of (by decide), hDl2]) h9D h9D2 (by rw [hpre9.stk_of (by decide), hAux])
  have hpre10 := hpre9.seq r10
  have hb10 := hpre10.bdd hw hb hpx
  obtain ⟨s11, r11, h11S, h11p, h11o, h11e⟩ := moveAllS_good (x := x) hw (q := qDom2)
    (q' := qJunk) (t := rT) (f := rT2) (by decide) (by decide) s10 hb10.1
  have e10A : s10.env rA = A := by rw [h10e _ (by decide), hsuf2.env_of (by decide), e1A]
  have e10D : s10.env rD = n := by rw [h10e _ (by decide), hsuf7.env_of (by decide), e6D]
  have hAn : A * n ≤ 3 * n := Nat.mul_le_mul_right _ hA3
  have hnX : n ≤ n * (ℓ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have r12 := mulS_good (x := x) (w := w) (Q := CQ) hw (dst := rNw) (a := rA) (b := rD)
    (j := rGj) (by decide) (by decide) (by decide) (by decide) (by decide) s11
    (by rw [h11e _ (by decide) (by decide), e10A]) (by rw [h11e _ (by decide) (by decide), e10D])
    (by omega) (by omega)
  set s12 := (s11.set rNw (A * n)).set rGj n
  have e12B : s12.env rSB = base := by
    simp only [s12, NSt.set_env, Function.update_of_ne (show rSB ≠ rGj by decide),
      Function.update_of_ne (show rSB ≠ rNw by decide)]
    rw [h11e _ (by decide) (by decide), h10e _ (by decide), hpre9.env_of (by decide), hSB]
  have e12N : s12.env rNw = A * n := by
    simp [s12, Function.update_of_ne (show rNw ≠ rGj by decide)]
  have r13 := Good.set (x := x) (w := w) (r := rSB) (e := .add (rv rSB) (rv rNw)) (st := s12)
    (by simp only [Ex.Fits, Ex.eval, rv, e12B, e12N]; omega)
  set s13 := s12.set rSB (Ex.eval s12.env (.add (rv rSB) (rv rNw)))
  have hpre13 := hpre10.seq (r11.seq (r12.seq r13))
  have e13J : s13.env rJ = j := by rw [hpre13.env_of (by decide), hJ]
  have r14 := Good.set (x := x) (w := w) (r := rJ) (e := .add (rv rJ) (.const 1)) (st := s13)
    (by simp only [Ex.Fits, Ex.eval, rv, e13J]; omega)
  set s14 := s13.set rJ (Ex.eval s13.env (.add (rv rJ) (.const 1)))
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq
    (r10.seq (r11.seq (r12.seq (r13.seq r14))))))))))))
  have hsuf11 := r11.seq (r12.seq (r13.seq r14))
  have hsuf12 := r12.seq (r13.seq r14)
  have hsuf6' := r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12.seq (r13.seq r14)))))))
  have hlen4 : (s4.stk qLs).length = A := by
    rw [h4S, Function.update_self]; simp [s3, s2, s1, hLs, hlocsA]
  have hlen8 : (s8.stk qDom).length = n * (ℓ + 1) := by
    rw [h8S, Function.update_self, (hpre6.seq r7).stk_of (by decide), hDom]; simp [hcl]
  have hlen10 : (s10.stk qDom2).length = n * (ℓ + 1) := by rw [h10D2, hcl]
  have hL : (encodeNats (schemaDescription sc)).length = (encodeNat A).length +
      (encodeNats locs).length + (encodeNat n).length + (encodeNats coords).length +
      (encodeNats (perms.flatMap permDescription)).length := by
    rw [hdesc]; simp only [List.cons_append, encNats_cons, encodeNats_append, List.length_append]
    ring
  refine ⟨s14, hall.mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hall.out_of (by decide), fun r hr => hall.env_of hr⟩
  · rw [hlen4, hlen8, hlen10]
    simp only [condCost, Ex.size, rv]
    rw [hL]
    have hPk : ℓ + 1 ≤ (encodeNats (perms.flatMap permDescription)).length := by
      refine le_trans ?_ (length_le_encodeNats _)
      obtain ⟨π, hπ⟩ : ∃ π, π ∈ perms := List.exists_mem_of_length_pos (by
        rw [hpermsA]; unfold A arity; split_ifs <;> omega)
      have h1 : (permDescription π).length ≤ (perms.flatMap permDescription).length := by
        rw [List.length_flatMap]; exact List.le_sum_of_mem (List.mem_map_of_mem hπ)
      have h2 := length_permDescription π
      have : ℓ + 1 ≤ k + k * ℓ := by nlinarith
      omega
    exact sch_arith _ _ _ _ _ _ _ _ _ _ _ ℓ hU0 hU' hA3 hlocsA hcl
      (hcl ▸ length_le_encodeNats coords) hPk
  · rw [hsuf6'.stk_of (by decide), h5Ls]
  · rw [hsuf11.stk_of (by decide), h10Ls2]
  · rw [hsuf11.stk_of (by decide), h10F]
  · rw [hsuf11.stk_of (by decide), h10F2]
  · rw [hsuf11.stk_of (by decide), h10Dl]
  · rw [hsuf11.stk_of (by decide), h10Dl2]
  · rw [hsuf11.stk_of (by decide), h10D]
  · rw [hsuf12.stk_of (by decide), h11S, Function.update_of_ne (by decide), Function.update_self]
  · rw [hsuf11.stk_of (by decide), h10Aux]
  · rw [hsuf11.stk_of (by decide), h10Rec, hpre9.stk_of (by decide)]
  · intro q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11
    exact hall.stk_of (by
      simp [p3Sch, p3Args, p3Arg, p3Seq, p3Cols, p3Col, p3Advs, p3Adv, p3Bits, p3Bit, moveN,
        moveAllS, rdNumsS, rdNumS, mulS, wStk, Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4,
        Ne.symm n5, Ne.symm n6, Ne.symm n7, Ne.symm n8, Ne.symm n9, Ne.symm n10, Ne.symm n11])
  · simp only [s14, NSt.set_env, Function.update_of_ne (show rSB ≠ rJ by decide), s13,
      Function.update_self, Ex.eval, rv, e12B, e12N]
  · simp only [s14, NSt.set_env, Function.update_self, Ex.eval, rv, e13J]
  · show s11.pos = _
    rw [h11p, h10p, h9p, h8p, hL]
    show (rdNumFinal s5 rD rP rT n).pos + _ + _ = _
    rw [rdNumFinal_pos, h5p, h4p]
    show (rdNumFinal st rA rP rT A).pos + _ + _ + _ + _ = _
    rw [rdNumFinal_pos]; ring

end Lax119563Proofs.Compiler
