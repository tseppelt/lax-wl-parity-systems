import Lax119563Proofs.Computability.StackLoad

/-!
# Simulating a machine: reading off the output

`extract`: after the simulation loop, tape `0` of the halted machine holds `encodeNat v`
in the layout of an input; the stacks of tape `0` are joined, leading blanks are skipped,
and `v` is read into the register `out` (`extract_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax489179.TuringMachine (Machine Config Instruction Move)

namespace Lax119563Proofs.Computability

open CStm

variable {R Q : ℕ} {x : List Bool} {w : ℕ} {M : Machine}
variable (ρ : Rg (M.tapes + 1) ↪ Fin R) (κ : Sk (M.tapes + 1) ↪ Fin Q)

variable (M) in
/-- Read the number on tape `0` into `out`. -/
def extract : CStm R Q :=
  seqL [moveAllS (κ (.L 0)) (κ (.R 0)) (ρ .tmp) (ρ .flg), skipZ (κ (.R 0)) (ρ .tmp),
    .set (ρ .out) (.const 0), .set (ρ .pw) (.const 1),
    parseB (κ (.R 0)) (ρ .tmp) (ρ .out) (ρ .pw)]

/-- The cost bound of `extract`. -/
def extractCost (w s a : ℕ) : ℕ := (a + 3 * s + 3) * (40 * Ex.nodeCost w)

lemma init_tape_zero (y : List Bool) (z : ℤ) :
    ((Lax489179.TuringMachine.init M y).tape 0 z).val =
      if 0 ≤ z then (syms y).getD z.toNat 0 else 0 := by
  simp only [Lax489179.TuringMachine.init, true_and]
  split_ifs with hz
  · simp only [syms, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases y[z.toNat]? with _ | _ | _ <;> rfl
  · rfl

lemma syms_encodeNat (v : ℕ) : syms (encodeNat v) = syms (pairs v.bits ++ [false]) := by
  rw [encodeNat_eq_pairs]

lemma extract_good (hw : 2 ≤ w) (st : NSt R Q) (hb : st.Bdd w) {c : Config M} {s a : ℕ}
    (hI : Inv ρ κ st c s a 1) (hh : (c.head 0).natAbs ≤ s) {v : ℕ}
    (hc : c.tape 0 = (Lax489179.TuringMachine.init M (encodeNat v)).tape 0)
    (hv : v.bits.length < w) :
    Good x w (extract M ρ κ) st (exec x (extract M ρ κ) st) (extractCost w s a) ∧
      (exec x (extract M ρ κ) st).env (ρ .out) = v ∧
      ((exec x (extract M ρ κ) st).stk (κ (.R 0))).length ≤ a + 3 * s ∧
      (exec x (extract M ρ κ) st).stk (κ (.L 0)) = [] ∧
      ∀ q, q ≠ κ (.L 0) → q ≠ κ (.R 0) → (exec x (extract M ρ κ) st).stk q = st.stk q := by
  obtain ⟨-, -, -, hrep, hlen⟩ := hI
  obtain ⟨hR0rep, hL0rep⟩ := hrep 0
  have hlen0 := hlen 0
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h2 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  set L0 := st.stk (κ (.L 0)) with hL0
  set R0 := st.stk (κ (.R 0)) with hR0
  set y := encodeNat v with hy
  -- joining the stacks
  obtain ⟨st1, g1, e1stk, -, -, e1env⟩ := moveAllS_good (x := x) hw (q := κ (.L 0))
    (q' := κ (.R 0)) (t := ρ .tmp) (f := ρ .flg) (by simp) (by simp) st hb
  set l := L0.reverse ++ R0 with hl
  have hst1R : st1.stk (κ (.R 0)) = l := by rw [e1stk]; simp [hl, hL0, hR0]
  have hst1L : st1.stk (κ (.L 0)) = [] := by rw [e1stk]; simp
  set p := c.head 0 - L0.length with hp
  have hcells : ∀ i : ℕ, l.getD i 0 = (c.tape 0 (p + i)).val := by
    intro i
    rcases Nat.lt_or_ge i L0.length with hi | hi
    · rw [hl, List.getD_append _ _ _ _ (by simpa using hi), List.getD_reverse i hi,
        ← hL0rep]
      congr 2; omega
    · rw [hl, List.getD_append_right _ _ _ _ (by simpa using hi), List.length_reverse,
        ← hR0rep]
      congr 2; omega
  have hblank : ∀ i : ℕ, (c.tape 0 (p - 1 - i)).val = 0 := by
    intro i
    have := hL0rep (L0.length + i)
    rw [List.getD_eq_default _ _ (by omega)] at this
    have e : p - 1 - (i : ℤ) = c.head 0 - 1 - ((L0.length + i : ℕ) : ℤ) := by omega
    rw [e]; exact this
  have hyne : y ≠ [] := by simp [hy, encodeNat]
  have hy0 : (c.tape 0 0).val ≠ 0 := by
    rw [hc, init_tape_zero, if_pos le_rfl]
    obtain ⟨b, l', hb'⟩ := List.exists_cons_of_ne_nil hyne
    rw [hb']; simp [syms]; exact (symOf_pos b).ne'
  have hp0 : p ≤ 0 := by
    by_contra hpos
    have := hblank (p - 1).toNat
    rw [show p - 1 - ((p - 1).toNat : ℤ) = 0 by omega] at this
    exact hy0 this
  set d := (-p).toNat with hd
  have hdp : p = -(d : ℤ) := by omega
  have hm : ∀ i, l.getD i 0 = (List.replicate d 0 ++ syms y).getD i 0 := by
    intro i
    rw [hcells, hc, init_tape_zero]
    conv_rhs => rw [List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge i d with hi | hi
    · rw [if_neg (by omega), List.getElem?_append_left (by simpa using hi),
        List.getElem?_replicate]
      simp [hi]
    · rw [if_pos (by omega), List.getElem?_append_right (by simpa using hi),
        List.length_replicate, ← List.getD_eq_getElem?_getD]
      congr 1; omega
  have hsyne : syms y ≠ [] := by simp [syms, hyne]
  have hlast : (List.replicate d 0 ++ syms y).getD
      ((List.replicate d 0 ++ syms y).length - 1) 0 ≠ 0 := by
    have hmeq : List.replicate d 0 ++ syms y =
        (List.replicate d 0 ++ syms (pairs v.bits)) ++ [1] := by
      simp [hy, encodeNat_eq_pairs, syms, symOf]
    rw [hmeq]; simp
  have hleq := eq_append_drop_of_getD hm (by simp [hsyne]) hlast
  set rest' := l.drop (List.replicate d 0 ++ syms y).length with hrest'
  obtain ⟨a0, tl, htl⟩ := List.exists_cons_of_ne_nil hsyne
  have ha0 : a0 = if 0 < v.bits.length then 2 else 1 := by
    have := syms_head v.bits 0
    rw [List.drop_zero, ← syms_encodeNat, ← hy, htl] at this
    exact this
  -- skipping the blanks
  have hst1R' : st1.stk (κ (.R 0)) = List.replicate d 0 ++ a0 :: (tl ++ rest') := by
    rw [hst1R, hleq, htl]; simp
  obtain ⟨g2, e2R, e2t⟩ := skipZ_good (x := x) (w := w) (t := ρ .tmp) hw st1 d a0 (tl ++ rest')
    (by rw [ha0]; split_ifs <;> omega) (by rw [ha0]; split_ifs <;> omega) hst1R'
  set st2 := exec x (skipZ (κ (.R 0)) (ρ .tmp)) st1 with hst2
  set st3 := (st2.set (ρ .out) 0).set (ρ .pw) 1 with hst3
  have g3a : Good x w (.set (ρ .out) (.const 0) : CStm R Q) st2 (st2.set (ρ .out) 0)
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp [Ex.Fits])).mono (by simp [Ex.size])
  have g3b : Good x w (.set (ρ .pw) (.const 1) : CStm R Q) (st2.set (ρ .out) 0) st3
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp [Ex.Fits]; omega)).mono (by simp [Ex.size])
  obtain ⟨g4, e4o, e4R⟩ := parseB_good (x := x) (q := κ (.R 0)) hw (t := ρ .tmp)
    (o := ρ .out) (p := ρ .pw) (by simp) (by simp) (by simp) st3 v.bits rest' hv
    (by
      simp only [hst3, NSt.set_stk, e2R]
      rw [← syms_encodeNat, ← hy, htl]; rfl)
    (by simp only [hst3, NSt.set_env]; rw [Function.update_of_ne (by simp),
          Function.update_of_ne (by simp), e2t, ha0])
    (by simp [hst3]) (by simp [hst3])
  set st4 := exec x (parseB (κ (.R 0)) (ρ .tmp) (ρ .out) (ρ .pw)) st3 with hst4
  have g : Good x w (extract M ρ κ) st st4 _ :=
    g1.seq (g2.seq (g3a.seq (g3b.seq (g4.seq Good.skip))))
  have hex : exec x (extract M ρ κ) st = st4 := g.2.1
  -- lengths
  have hlenl : l.length ≤ a + 3 * s := by
    simp only [hl, List.length_append, List.length_reverse]; omega
  have hylen : y.length ≤ l.length := by
    have := congrArg List.length hleq; simp [syms] at this; omega
  have hbits : v.bits.length ≤ y.length := by
    simp [hy, encodeNat_eq_pairs]; omega
  have hdle : d ≤ 2 * s := by omega
  refine ⟨?_, ?_, ?_, ?_, fun q hq1 hq2 => ?_⟩
  · rw [hex]; refine g.mono ?_
    simp only [extractCost]
    have hL := hlen0.1
    nlinarith
  · rw [hex, e4o, Machines.valBits_bits]
  · rw [hex, e4R, hrest', List.length_drop]; omega
  · rw [hex]
    have : st4.stk (κ (.L 0)) = st1.stk (κ (.L 0)) :=
      exec_stk_of _ _ (by simp [parseB, skipZ, seqL, wStk]) |>.trans
        (by simp only [hst3, NSt.set_stk]; exact exec_stk_of _ _ (by simp [skipZ, wStk]))
    rw [this, hst1L]
  · rw [hex]
    have h1 : st4.stk q = st1.stk q :=
      exec_stk_of _ _ (by simp [parseB, skipZ, seqL, wStk, Ne.symm hq2]) |>.trans
        (by simp only [hst3, NSt.set_stk]; exact exec_stk_of _ _ (by simp [skipZ, wStk, Ne.symm hq2]))
    rw [h1, e1stk, Function.update_of_ne hq2, Function.update_of_ne hq1]

end Lax119563Proofs.Computability
