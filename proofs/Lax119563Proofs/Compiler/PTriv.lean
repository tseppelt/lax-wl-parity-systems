import Lax119563Proofs.Compiler.PSys
import Lax119563Proofs.Compiler.CSortLoop

/-!
# Pass `P0` of the compiler program: the triviality check

The compiler program works with `CR` registers and `CQ` number stacks (`PDefs` below).
`p0` skips `k` and `ℓ` (they may be exponential in `H` for trivial systems), reads `W`, and
for the locations in order reads `ι(v)` and `|D_v|`, stopping at the first nonempty domain;
if all domains are empty it reads `E`. It sets `rTriv = [trivSys I]` where `trivSys I` means
that all domains are empty and there is no schema (`p0_good`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Registers and stacks of the compiler program -/

/-- The number of registers of the compiler program. -/
abbrev CR : ℕ := 40
/-- The number of stacks of the compiler program. -/
abbrev CQ : ℕ := 16

/-- Scratch registers of the number readers. -/
def rT : Fin CR := 0
def rP : Fin CR := 1
/-- `W`. -/
def rW : Fin CR := 2
/-- Location counter. -/
def rJ : Fin CR := 3
/-- Flag: a nonempty domain was found. -/
def rNz : Fin CR := 4
/-- Read values. -/
def rA : Fin CR := 5
def rD : Fin CR := 6
/-- `E`. -/
def rE : Fin CR := 7
/-- The result of `P0`. -/
def rTriv : Fin CR := 8

/-! ## Final states of the readers -/

section Readers

variable {R Q : ℕ}

@[simp] lemma rdNumFinal_stk (st : NSt R Q) (r p t : Fin R) (v : ℕ) :
    (CStm.rdNumFinal st r p t v).stk = st.stk := rfl
@[simp] lemma rdNumFinal_out (st : NSt R Q) (r p t : Fin R) (v : ℕ) :
    (CStm.rdNumFinal st r p t v).out = st.out := rfl
@[simp] lemma rdNumFinal_pos (st : NSt R Q) (r p t : Fin R) (v : ℕ) :
    (CStm.rdNumFinal st r p t v).pos = st.pos + (encodeNat v).length := rfl
lemma rdNumFinal_env_r {st : NSt R Q} {r p t : Fin R} (hrp : r ≠ p) (hrt : r ≠ t) (v : ℕ) :
    (CStm.rdNumFinal st r p t v).env r = v := by
  simp [CStm.rdNumFinal, Function.update_of_ne hrp, Function.update_of_ne hrt]
lemma rdNumFinal_env_ne {st : NSt R Q} {r p t q : Fin R} (h1 : q ≠ r) (h2 : q ≠ p) (h3 : q ≠ t)
    (v : ℕ) : (CStm.rdNumFinal st r p t v).env q = st.env q := by
  simp [CStm.rdNumFinal, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3]

@[simp] lemma skipNumFinal_stk (st : NSt R Q) (t : Fin R) (v : ℕ) :
    (CStm.skipNumFinal st t v).stk = st.stk := rfl
@[simp] lemma skipNumFinal_out (st : NSt R Q) (t : Fin R) (v : ℕ) :
    (CStm.skipNumFinal st t v).out = st.out := rfl
@[simp] lemma skipNumFinal_pos (st : NSt R Q) (t : Fin R) (v : ℕ) :
    (CStm.skipNumFinal st t v).pos = st.pos + (encodeNat v).length := rfl
lemma skipNumFinal_env_ne {st : NSt R Q} {t q : Fin R} (h : q ≠ t) (v : ℕ) :
    (CStm.skipNumFinal st t v).env q = st.env q := by
  simp [CStm.skipNumFinal, Function.update_of_ne h]

end Readers

open CStm

/-! ## The program -/

/-- The body of the location loop of `P0`. -/
def p0Body : CStm CR CQ :=
  .seq (rdNumS rA rP rT) (.seq (rdNumS rD rP rT)
    (.ite (rv rD) (.seq (.set rNz (.const 1)) (.set rJ (rv rW)))
      (.set rJ (.add (rv rJ) (.const 1)))))

/-- The loop over the locations. -/
def p0Loop : CStm CR CQ := .loop (.lt (rv rJ) (rv rW)) p0Body

/-- The end of `P0`. -/
def p0End : CStm CR CQ :=
  .ite (rv rNz) (.set rTriv (.const 0))
    (.seq (rdNumS rE rP rT) (.set rTriv (.lt (rv rE) (.const 1))))

/-- **Pass `P0`.** -/
def p0 : CStm CR CQ :=
  .seq (skipNumS rT) (.seq (skipNumS rT) (.seq (rdNumS rW rP rT)
    (.seq (.set rJ (.const 0)) (.seq (.set rNz (.const 0)) (.seq p0Loop p0End)))))

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- A trivial system: no coordinate and no schema. -/
def trivSys : Prop := (∀ v, I.domain v = ∅) ∧ I.schemas = []

/-- The loop invariant of `P0`. -/
def p0Inv (st s : NSt CR CQ) : Prop :=
  s.env rW = I.numLocations ∧ s.stk = st.stk ∧ s.out = st.out ∧ s.env rJ ≤ I.numLocations ∧
    ((s.env rNz = 0 ∧ s.pos = posAt I (s.env rJ) ∧
        ∀ v : Fin I.numLocations, v.val < s.env rJ → I.domain v = ∅) ∨
      (s.env rNz = 1 ∧ s.env rJ = I.numLocations ∧ ∃ v, I.domain v ≠ ∅))

lemma locD_eq (v : Fin I.numLocations) : ∃ rest, locD I v =
    initNum (I.init v) :: ((I.domain v).image coordNum).card :: rest := by
  obtain ⟨rest, he, -⟩ := domainDescription_head (D := I.domain v)
  exact ⟨rest, by rw [locD, he]⟩

lemma initNum_le (a : Option (ZMod 2)) : initNum a ≤ 2 := by
  rcases a with _ | b
  · simp [initNum]
  · have := ZMod.val_lt b; simp [initNum]; omega

lemma three_le_H : 3 ≤ H I := by
  have := length_sd_le I
  rw [sd_eq] at this; simp at this; omega

/-- One iteration of the location loop. -/
lemma p0Body_good {w : ℕ} (hw : 2 ≤ w) (hH : 2 * (H I + 1) ≤ 2 ^ w) (st s : NSt CR CQ)
    (hI : p0Inv I st s) (hc : (Ex.lt (rv rJ) (rv rW)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p0Body s s'
        (20 * Ex.nodeCost w * ((H I - s.pos) - (H I - s'.pos)) + 50 * Ex.nodeCost w) ∧
      p0Inv I st s' ∧ I.numLocations - s'.env rJ < I.numLocations - s.env rJ ∧
      H I - s'.pos ≤ H I - s.pos := by
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  obtain ⟨hW, hstk, hout, hjW, hcase⟩ := hI
  have hlt : s.env rJ < I.numLocations := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hW]; rw [if_neg h]
  rcases hcase with ⟨hnz, hpos, hemp⟩ | ⟨-, hj, -⟩
  swap; · omega
  set j := s.env rJ with hjdef
  set v : Fin I.numLocations := ⟨j, hlt⟩
  obtain ⟨rest, hloc⟩ := locD_eq I v
  set a := initNum (I.init v)
  set d := ((I.domain v).image coordNum).card
  have hx : (encodeSystem I).drop s.pos =
      encodeNat a ++ (encodeNat d ++ encodeNats (rest ++ (locsSuf I (j + 1) ++
        I.schemas.length :: schsDesc I))) := by
    rw [hpos, drop_posAt, locsSuf_cons I hlt, hloc]
    simp [encNats_cons, encodeNats_append]
  have hposle : s.pos ≤ H I := by rw [hpos]; exact posAt_le I j
  have hlenx : s.pos + (encodeNat a).length + (encodeNat d).length ≤ H I := by
    have := congrArg List.length hx
    simp only [List.length_drop, List.length_append] at this
    show _ ≤ (encodeSystem I).length
    have : s.pos ≤ (encodeSystem I).length := hposle
    omega
  have ha : (Nat.bits a).length < w := bits_lt_of_le (le_trans (initNum_le _)
    (by have := three_le_H I; omega)) hH
  have hd : (Nat.bits d).length < w := bits_lt_of_le (card_le I v) hH
  have r1 := rdNumS_good (Q := CQ) hw (r := rA) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s a _ hx ha
  set s1 := rdNumFinal s rA rP rT a
  have hx2 : (encodeSystem I).drop s1.pos = encodeNat d ++ encodeNats (rest ++
      (locsSuf I (j + 1) ++ I.schemas.length :: schsDesc I)) := by
    simp only [s1, rdNumFinal_pos]
    rw [← List.drop_drop, hx, List.drop_left]
  have r2 := rdNumS_good (Q := CQ) hw (r := rD) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s1 d _ hx2 hd
  set s2 := rdNumFinal s1 rD rP rT d
  have e2D : s2.env rD = d := rdNumFinal_env_r (by decide) (by decide) d
  have e2 : ∀ q, q ≠ rD → q ≠ rA → q ≠ rP → q ≠ rT → s2.env q = s.env q := by
    intro q h1 h2 h3 h4
    rw [rdNumFinal_env_ne h1 h3 h4, rdNumFinal_env_ne h2 h3 h4]
  have hp2 : s2.pos = s.pos + (encodeNat a).length + (encodeNat d).length := rfl
  have hWlt : I.numLocations < 2 ^ w := by have := W_le I; omega
  have hdw : d < 2 ^ w := by have := card_le I v; omega
  by_cases hd0 : d = 0
  · -- empty domain: next location
    have hemp' : I.domain v = ∅ := (card_image_eq_zero_iff).mp hd0
    have hjw : s2.env rJ + 1 < 2 ^ w := by
      have := W_le I
      rw [e2 rJ (by decide) (by decide) (by decide) (by decide)]; omega
    have r3 := Good.set (x := encodeSystem I) (w := w) (r := rJ) (st := s2)
      (e := .add (rv rJ) (.const 1)) (by simp only [Ex.Fits, Ex.eval, rv]; omega)
    refine ⟨_, (r1.seq (r2.seq (Good.iteF (by simp only [Ex.Fits, rv, e2D]; omega)
      (by simp [Ex.eval, rv, e2D, hd0]) r3))).mono ?_, ?_, ?_, ?_⟩
    · simp only [condCost, Ex.size, rv, NSt.set_pos, hp2]
      have hΔ : H I - s.pos - (H I - (s.pos + (encodeNat a).length + (encodeNat d).length)) =
          (encodeNat a).length + (encodeNat d).length := by omega
      rw [hΔ]
      generalize Ex.nodeCost w = N at *
      generalize unitCost w = U at *
      generalize (encodeNat a).length = la at *
      generalize (encodeNat d).length = ld at *
      ring_nf
      nlinarith
    · have hj' : (s2.set rJ (Ex.eval s2.env (.add (rv rJ) (.const 1)))).env rJ = j + 1 := by
        simp [Ex.eval, rv, e2 rJ (by decide) (by decide) (by decide) (by decide), j]
      refine ⟨?_, by simp [s2, s1, hstk], by simp [s2, s1, hout], by rw [hj']; omega,
        Or.inl ⟨?_, ?_, ?_⟩⟩
      · rw [NSt.set_env, Function.update_of_ne (by decide),
          e2 rW (by decide) (by decide) (by decide) (by decide), hW]
      · rw [NSt.set_env, Function.update_of_ne (by decide),
          e2 rNz (by decide) (by decide) (by decide) (by decide), hnz]
      · rw [hj', NSt.set_pos, hp2, hpos, posAt_succ I hlt]
        have : locD I v = [a, 0] := by
          rw [locD, hemp', domainDescription_empty]
        rw [this]; simp [encNats_cons, encodeNats, hd0]; omega
      · intro u hu
        rw [hj'] at hu
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | hu
        · exact hemp u hu
        · have : u = v := Fin.ext hu
          rw [this]; exact hemp'
    · simp only [NSt.set_env, Function.update_self, Ex.eval, rv,
        e2 rJ (by decide) (by decide) (by decide) (by decide)]; omega
    · simp only [NSt.set_pos, hp2]; omega
  · -- nonempty domain: stop
    have hne : I.domain v ≠ ∅ := fun h => hd0 ((card_image_eq_zero_iff).mpr h)
    have r3 := (Good.set (x := encodeSystem I) (w := w) (r := rNz) (st := s2) (e := .const 1)
      (by simp only [Ex.Fits]; omega)).seq
      (Good.set (r := rJ) (e := rv rW) (by
        simp only [Ex.Fits, rv, NSt.set_env, Function.update_of_ne (show rW ≠ rNz by decide),
          e2 rW (by decide) (by decide) (by decide) (by decide), hW]; exact hWlt))
    refine ⟨_, (r1.seq (r2.seq (Good.iteT (by simp only [Ex.Fits, rv, e2D]; omega)
      (by simp [Ex.eval, rv, e2D, hd0]) r3))).mono ?_, ?_, ?_, ?_⟩
    · simp only [condCost, Ex.size, rv, NSt.set_pos, hp2]
      have hΔ : H I - s.pos - (H I - (s.pos + (encodeNat a).length + (encodeNat d).length)) =
          (encodeNat a).length + (encodeNat d).length := by omega
      rw [hΔ]
      generalize Ex.nodeCost w = N at *
      generalize unitCost w = U at *
      generalize (encodeNat a).length = la at *
      generalize (encodeNat d).length = ld at *
      ring_nf
      nlinarith
    · have hj' : ((s2.set rNz (Ex.eval s2.env (.const 1))).set rJ
          (Ex.eval (s2.set rNz (Ex.eval s2.env (.const 1))).env (rv rW))).env rJ =
            I.numLocations := by
        simp [Ex.eval, rv, Function.update_of_ne (show rW ≠ rNz by decide),
          e2 rW (by decide) (by decide) (by decide) (by decide), hW]
      refine ⟨?_, by simp [s2, s1, hstk], by simp [s2, s1, hout], by rw [hj'],
        Or.inr ⟨?_, hj', v, hne⟩⟩
      · simp only [NSt.set_env, Function.update_of_ne (show rW ≠ rJ by decide),
          Function.update_of_ne (show rW ≠ rNz by decide)]
        rw [e2 rW (by decide) (by decide) (by decide) (by decide), hW]
      · simp [Ex.eval, Function.update_of_ne (show rNz ≠ rJ by decide)]
    · simp only [NSt.set_env, Function.update_self, Ex.eval, rv,
        Function.update_of_ne (show rW ≠ rNz by decide),
        e2 rW (by decide) (by decide) (by decide) (by decide), hW]; omega
    · simp only [NSt.set_pos, hp2]; omega

/-- The end of `P0`, after the loop. -/
lemma p0End_good {w : ℕ} (hw : 2 ≤ w) (hH : 2 * (H I + 1) ≤ 2 ^ w) (st s : NSt CR CQ)
    (hI : p0Inv I st s) (hc : (Ex.lt (rv rJ) (rv rW)).eval s.env = 0) :
    ∃ s', Good (encodeSystem I) w p0End s s' (30 * (H I + 1) * Ex.nodeCost w) ∧
      s'.stk = st.stk ∧ s'.out = st.out ∧ (s'.env rTriv = 1 ↔ trivSys I) ∧
      s'.env rTriv ≤ 1 := by
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  have h4 : 4 ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  obtain ⟨hW, hstk, hout, hjW, hcase⟩ := hI
  rcases hcase with ⟨hnz, hpos, hemp⟩ | ⟨hnz, -, v, hne⟩
  · have hj : s.env rJ = I.numLocations := by
      simp only [Ex.eval, rv, hW] at hc; split_ifs at hc with h <;> omega
    have hx : (encodeSystem I).drop s.pos = encodeNat I.schemas.length ++ encodeNats (schsDesc I) := by
      rw [hpos, hj, drop_posAt, locsSuf_all]; simp [encNats_cons]
    have hEH := E_le I
    have r1 := rdNumS_good (Q := CQ) hw (r := rE) (p := rP) (t := rT) (by decide) (by decide)
      (by decide) s _ _ hx (bits_lt_of_le hEH hH)
    set s1 := rdNumFinal s rE rP rT I.schemas.length
    have e1 : s1.env rE = I.schemas.length := rdNumFinal_env_r (by decide) (by decide) _
    have r2 := Good.set (x := encodeSystem I) (w := w) (r := rTriv) (st := s1)
      (e := .lt (rv rE) (.const 1)) (by simp only [Ex.Fits, rv, e1]; omega)
    have hlen : (encodeNat I.schemas.length).length ≤ H I := by
      have := congrArg List.length hx
      simp only [List.length_drop, List.length_append] at this
      show _ ≤ (encodeSystem I).length
      omega
    refine ⟨_, (Good.iteF (by simp only [Ex.Fits, rv]; rw [hnz]; omega)
      (by simp [Ex.eval, rv, hnz]) (r1.seq r2)).mono ?_, by simp [s1, hstk],
      by simp [s1, hout], ?_, ?_⟩
    · simp only [condCost, Ex.size]
      generalize Ex.nodeCost w = N at *
      generalize unitCost w = U at *
      generalize (encodeNat I.schemas.length).length = lE at *
      nlinarith
    · simp only [NSt.set_env, Function.update_self, Ex.eval, rv, e1]
      constructor
      · intro h
        have h0 : I.schemas.length < 1 := by
          by_contra h0; rw [if_neg h0] at h; exact absurd h zero_ne_one
        exact ⟨fun u => hemp u (by rw [hj]; exact u.2), List.eq_nil_of_length_eq_zero (by omega)⟩
      · rintro ⟨-, hs⟩; simp [hs]
    · simp only [NSt.set_env, Function.update_self, Ex.eval, rv, e1]
      by_cases h0 : I.schemas.length < 1 <;> simp [h0]
  · have r1 := Good.set (x := encodeSystem I) (w := w) (r := rTriv) (st := s) (e := .const 0)
      (by simp only [Ex.Fits]; omega)
    refine ⟨_, (Good.iteT (by simp only [Ex.Fits, rv]; rw [hnz]; omega)
      (by simp [Ex.eval, rv, hnz]) r1).mono ?_, hstk, hout, ?_, ?_⟩
    · simp only [condCost, Ex.size]
      generalize Ex.nodeCost w = N at *
      generalize unitCost w = U at *
      nlinarith
    · simp only [NSt.set_env, Function.update_self, Ex.eval]
      constructor
      · intro h; exact absurd h zero_ne_one
      · rintro ⟨h, -⟩; exact absurd (h v) hne
    · simp [Ex.eval]

/-- **Pass `P0`.** From the start of the input, `P0` sets `rTriv` to `[trivSys I]`, keeping
the stacks and the output. -/
theorem p0_good {w : ℕ} (hw : 2 ≤ w) (hH : 2 * (H I + 1) ≤ 2 ^ w) (st : NSt CR CQ)
    (hp : st.pos = 0) :
    ∃ st', Good (encodeSystem I) w p0 st st' (200 * (H I + 1) * Ex.nodeCost w) ∧
      st'.stk = st.stk ∧ st'.out = st.out ∧ (st'.env rTriv = 1 ↔ trivSys I) ∧
      st'.env rTriv ≤ 1 := by
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  have hWH := W_le I
  have h4 : 4 ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have r1 := skipNumS_good (Q := CQ) hw (t := rT) st k _ (by rw [hp]; exact drop_zero_k I)
  set s1 := skipNumFinal st rT k
  have r2 := skipNumS_good (Q := CQ) hw (t := rT) s1 ℓ _
    (by simp only [s1, skipNumFinal_pos, hp, zero_add]; exact drop_ell I)
  set s2 := skipNumFinal s1 rT ℓ
  have r3 := rdNumS_good (Q := CQ) hw (r := rW) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s2 I.numLocations _
    (by simp only [s2, s1, skipNumFinal_pos, hp, zero_add]; exact drop_W I) (bits_lt_of_le hWH hH)
  set s3 := rdNumFinal s2 rW rP rT I.numLocations
  have e3 : s3.env rW = I.numLocations := rdNumFinal_env_r (by decide) (by decide) _
  have r4 := Good.set (x := encodeSystem I) (w := w) (r := rJ) (st := s3) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s4 := s3.set rJ (Ex.eval s3.env (.const 0))
  have r5 := Good.set (x := encodeSystem I) (w := w) (r := rNz) (st := s4) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s5 := s4.set rNz (Ex.eval s4.env (.const 0))
  have hp5 : s5.pos = posAt I 0 := by
    show st.pos + (encodeNat k).length + (encodeNat ℓ).length +
      (encodeNat I.numLocations).length = posAt I 0
    rw [hp, posAt_zero]; ring
  have e5 : ∀ q, s5.env q = Function.update (Function.update s3.env rJ 0) rNz 0 q :=
    fun _ => rfl
  have e5J : s5.env rJ = 0 := by
    rw [e5, Function.update_of_ne (by decide), Function.update_self]
  have hI5 : p0Inv I st s5 := by
    refine ⟨?_, rfl, rfl, by rw [e5J]; omega, Or.inl ⟨?_, ?_,
      fun v hv => absurd hv (by rw [e5J]; omega)⟩⟩
    · rw [e5, Function.update_of_ne (by decide), Function.update_of_ne (by decide), e3]
    · rw [e5, Function.update_self]
    · rw [e5J, hp5]
  -- the loop
  obtain ⟨s6, r6, hI6, hc6⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rW)) (body := p0Body) (p0Inv I st)
    (fun s => I.numLocations - s.env rJ) (fun s => H I - s.pos) (20 * Ex.nodeCost w)
    (50 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hW, -, -, hj, -⟩ := hI
      simp only [Ex.Fits, rv, hW]; omega, fun hc => p0Body_good I hw hH st s hI hc⟩) s5 hI5
  obtain ⟨s7, r7, h7s, h7o, h7t, h7b⟩ := p0End_good I hw hH st s6 hI6 hc6
  refine ⟨s7, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq ((r6.seq r7))))))).mono ?_,
    h7s, h7o, h7t, h7b⟩
  -- the cost
  have hlen : (encodeNat k).length + (encodeNat ℓ).length + (encodeNat I.numLocations).length ≤
      H I := by rw [← posAt_zero]; exact posAt_le I 0
  have hφ : H I - s5.pos + (encodeNat k).length + (encodeNat ℓ).length +
      (encodeNat I.numLocations).length = H I := by rw [hp5, posAt_zero]; omega
  have hμ : I.numLocations - s5.env rJ ≤ H I := by omega
  simp only [condCost, Ex.size, rv] at *
  generalize Ex.nodeCost w = N at *
  generalize unitCost w = U at *
  generalize H I - s5.pos = φ at *
  generalize I.numLocations - s5.env rJ = μ at *
  generalize (encodeNat k).length = lk at *
  generalize (encodeNat ℓ).length = ll at *
  generalize (encodeNat I.numLocations).length = lW at *
  generalize H I = h at *
  nlinarith

end Lax119563Proofs.Compiler
