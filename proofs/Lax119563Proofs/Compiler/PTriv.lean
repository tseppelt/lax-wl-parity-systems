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
    simp only [Ex.eval, rv] at hc; split_ifs at hc with h
    · omega
    · exact absurd rfl hc
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
  have hlenx : s.pos + (encodeNat a).length + (encodeNat d).length ≤ H I := by
    have := congrArg List.length hx
    simp only [List.length_drop, List.length_append] at this
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
      rw [e2 rJ (by decide) (by decide) (by decide) (by decide)]; omega
    have r3 := Good.set (x := encodeSystem I) (w := w) (r := rJ) (st := s2)
      (e := .add (rv rJ) (.const 1)) (by simp only [Ex.Fits, Ex.eval, rv]; omega)
    refine ⟨_, (r1.seq (r2.seq (Good.iteF (by simp only [Ex.Fits, rv, e2D]; omega)
      (by simp [Ex.eval, rv, e2D, hd0]) r3))).mono ?_, ?_, ?_, ?_⟩
    · simp only [condCost, Ex.size, rv, NSt.set_pos, hp2]
      have : H I - (s.pos + (encodeNat a).length + (encodeNat d).length) + (encodeNat a).length +
          (encodeNat d).length = H I - s.pos := by omega
      generalize Ex.nodeCost w = N at *
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
        rw [this]; simp [encNats_cons, encodeNats]; omega
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
      have : H I - (s.pos + (encodeNat a).length + (encodeNat d).length) + (encodeNat a).length +
          (encodeNat d).length = H I - s.pos := by omega
      generalize Ex.nodeCost w = N at *
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
      · simp [Ex.eval]
    · simp only [NSt.set_env, Function.update_self, Ex.eval, rv,
        Function.update_of_ne (show rW ≠ rNz by decide),
        e2 rW (by decide) (by decide) (by decide) (by decide), hW]; omega
    · simp only [NSt.set_pos, hp2]; omega

end Lax119563Proofs.Compiler
