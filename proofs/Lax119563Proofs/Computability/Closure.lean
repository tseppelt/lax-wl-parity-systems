import Lax119563Proofs.Computability.Call

/-!
# Closure properties of computable functions

`MachineComputable` is closed under constants, the identity, composition, the arithmetic
operations `+`, `·`, `max`, `^` (pointwise), and has monotone majorants:

* `MachineComputable.const`, `MachineComputable.id'`, `MachineComputable.comp`;
* `MachineComputable.arith` (any `ArithOp`), `.add`, `.mul`, `.max`, `.pow`, and the
  derived `.affine` (`a k + b`), `.pow_const`, `.two_pow`, `.add_const`, `.mul_const`;
* `MachineComputable.exists_monotone_ge`: `f ≤ g` for a computable monotone `g` (the running
  maximum `g k = max_{i ≤ k} f i`, `MachineComputable.runMax`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime Lax119563.ParameterizedComplexity
open Lax489179.TuringMachine (Machine Config Instruction Move Deterministic)

namespace Lax119563Proofs.Computability

open CStm

variable {x : List Bool} {w : ℕ}

/-! ## Powers -/

/-- `o := a ^ b` (counter `s`, scratch `t`, `u`). -/
def powS {R Q : ℕ} (a b o s t u : Fin R) : CStm R Q :=
  seqL [.set o (.const 1), .set s (.const 0), .loop (.lt (.var s) (.var b))
    (seqL [mulS t o a u, .set o (.var t), .set s (.add (.var s) (.const 1))])]

/-- Powers. -/
def powOp : ArithOp (· ^ ·) where
  op a b o s t u := powS a b o s t u
  W A B := A ^ B + A + B + 2
  spec := fun {R Q x w} a b o s t u hnd hw st hW => by
    obtain ⟨hab, hao, has, hat, hau, hbo, hbs, hbt, hbu, hos, hot, hou, hst, hsu, htu⟩ :=
      nodup6 hnd
    set A := st.env a
    set B := st.env b
    have hpow : ∀ j ≤ B, A ^ j ≤ A ^ B + 1 := fun j hj => by
      rcases Nat.eq_zero_or_pos A with h0 | h0
      · rw [h0]; rcases j with _ | j <;> simp
      · exact (Nat.pow_le_pow_right h0 hj).trans (Nat.le_succ _)
    have hlt : ∀ v, v ≤ A ^ B + A + B + 1 → v < 2 ^ w := fun v hv =>
      lt_two_pow_of_le (by omega)
    set st1 := (st.set o 1).set s 0 with hst1
    set body : CStm R Q := seqL [mulS t o a u, .set o (.var t), .set s (.add (.var s) (.const 1))]
    set S : ℕ → NSt R Q := fun j => iter x body st1 j with hS
    -- one iteration, from any state with the right registers
    have hstep : ∀ (S' : NSt R Q) (j : ℕ), j < B → S'.env o = A ^ j → S'.env s = j →
        S'.env a = A → S'.env b = B →
        Fits x w body S' ∧ exec x body S' =
          (((S'.set t (A ^ j * A)).set u A).set o (A ^ j * A)).set s (j + 1) := by
      intro S' j hj ho hs ha hb
      have hAj : A ^ j * A ≤ A ^ B + 1 := by rw [← pow_succ]; exact hpow _ hj
      have g1 := mulS_good (x := x) hw hot.symm hat.symm htu hou hau S' ho ha
        (hlt (A ^ j * A) (by omega)) (hlt A (by omega))
      set S1 := (S'.set t (A ^ j * A)).set u A with hS1
      have e1t : S1.env t = A ^ j * A := by simp [hS1, Function.update_of_ne htu]
      have e1s : S1.env s = j := by
        simp [hS1, Function.update_of_ne hsu, Function.update_of_ne hst, hs]
      have g2 : Good x w (.set o (.var t) : CStm R Q) S1 (S1.set o (A ^ j * A))
          (Ex.nodeCost w + unitCost w) :=
        (Good.set (by simp only [Ex.Fits, e1t]; exact hlt _ (by omega))).of_eq
          (by simp [Ex.eval, e1t]) (by simp [Ex.size])
      have e2s : (S1.set o (A ^ j * A)).env s = j := by
        simp [Function.update_of_ne hos.symm, e1s]
      have g3 : Good x w (.set s (.add (.var s) (.const 1)) : CStm R Q) (S1.set o (A ^ j * A))
          ((S1.set o (A ^ j * A)).set s (j + 1)) (3 * Ex.nodeCost w + unitCost w) :=
        (Good.set (by
          simp only [Ex.Fits, Ex.eval, e2s]
          exact ⟨hlt j (by omega), hlt 1 (by omega), hlt (j + 1) (by omega)⟩)).of_eq
          (by simp [Ex.eval, e2s]) (by simp [Ex.size])
      have g := g1.seq (g2.seq (g3.seq Good.skip))
      exact ⟨g.1, g.2.1⟩
    have hSj : ∀ j ≤ B, (S j).env o = A ^ j ∧ (S j).env s = j ∧ (S j).env a = A ∧
        (S j).env b = B ∧ (∀ r, r ≠ o → r ≠ s → r ≠ t → r ≠ u → (S j).env r = st.env r) ∧
        (S j).stk = st.stk ∧ (S j).pos = st.pos ∧ (S j).out = st.out := by
      intro j
      induction j with
      | zero =>
        intro _
        simp only [hS, iter_zero, hst1, NSt.set_env, NSt.set_stk, NSt.set_pos, NSt.set_out]
        refine ⟨?_, by simp, ?_, ?_, fun r h1 h2 _ _ => ?_, by simp, by simp, by simp⟩
        · simp [Function.update_of_ne hos]
        · simp [Function.update_of_ne has, Function.update_of_ne hao, A]
        · simp [Function.update_of_ne hbs, Function.update_of_ne hbo, B]
        · simp [Function.update_of_ne h1, Function.update_of_ne h2]
      | succ j ih =>
        intro hj
        obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ih (by omega)
        rw [show S (j + 1) = exec x body (S j) from iter_succ _ _ _,
          (hstep (S j) j (by omega) i1 i2 i3 i4).2]
        simp only [NSt.set_env, NSt.set_stk, NSt.set_pos, NSt.set_out]
        refine ⟨?_, by simp, ?_, ?_, fun r h1 h2 h3 h4 => ?_, i6, i7, i8⟩
        · rw [Function.update_of_ne hos, Function.update_self, pow_succ]
        · rw [Function.update_of_ne has, Function.update_of_ne hao, Function.update_of_ne hau,
            Function.update_of_ne hat, i3]
        · rw [Function.update_of_ne hbs, Function.update_of_ne hbo, Function.update_of_ne hbu,
            Function.update_of_ne hbt, i4]
        · rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h4,
            Function.update_of_ne h3, i5 r h1 h2 h3 h4]
    have hloop := Good.loop (x := x) (w := w) (e := .lt (.var s) (.var b)) (body := body) B S
      (fun j => cost x w body (S j))
      (fun j hj => by simp [Ex.eval, (hSj j hj.le).2.1, (hSj j hj.le).2.2.2.1, hj])
      (by simp [Ex.eval, (hSj B le_rfl).2.1, (hSj B le_rfl).2.2.2.1])
      (fun j hj => by
        simp only [Ex.Fits, (hSj j hj).2.1, (hSj j hj).2.2.2.1]
        exact ⟨hlt j (by omega), hlt B (by omega)⟩)
      (fun j hj => by
        obtain ⟨i1, i2, i3, i4, -⟩ := hSj j hj.le
        have := hstep (S j) j hj i1 i2 i3 i4
        rw [show S (j + 1) = exec x body (S j) from iter_succ _ _ _]
        exact ⟨this.1, rfl, le_rfl⟩)
    have g0 := (Good.set (x := x) (w := w) (r := o) (e := .const 1) (st := st)
      (by simp only [Ex.Fits]; exact hlt 1 (by omega))).seq ((Good.set (x := x) (w := w) (r := s)
        (e := .const 0) (st := st.set o 1) (by simp [Ex.Fits])).seq (hloop.seq Good.skip))
    have hex : exec x (powS a b o s t u) st = S B := g0.2.1
    obtain ⟨i1, -, -, -, i5, i6, i7, i8⟩ := hSj B le_rfl
    refine ⟨g0.1, by rw [hex, i1], fun r h1 h2 h3 h4 => by rw [hex, i5 r h1 h2 h3 h4],
      by rw [hex, i6], by rw [hex, i7], by rw [hex, i8]⟩

/-! ## Constants and the identity -/

theorem MachineComputable.const (c : ℕ) : MachineComputable fun _ => c := by
  refine machineComputable_of_stm (.emit (.const c) : CStm 1 0) _ fun k => ⟨c + 2, by omega,
    _, _, Good.emit (by simp only [Ex.Fits]; exact lt_two_pow_of_le (by omega)), rfl⟩

theorem MachineComputable.id' : MachineComputable fun k => k := by
  refine machineComputable_of_stm (seqL [startS 0 3 le_rfl, .emit (.var (ex 0 3 0))]) _
    fun k => ?_
  obtain ⟨st1, T1, g1, e1k, -, -, -, e1o⟩ := start_good 0 3 le_rfl (w := k + 2) (by omega) k
    (by omega)
  have e1k' : st1.env (ex 0 3 0) = k := e1k
  have hf : (Ex.var (ex 0 3 0) : Ex (0 + 3)).Fits (k + 2) st1.env := by
    simp only [Ex.Fits, e1k']; exact lt_two_pow_of_le (by omega)
  refine ⟨k + 2, by omega, _, _, g1.seq ((Good.emit hf).seq Good.skip), ?_⟩
  simp [Ex.eval, e1k', e1o]

/-! ## Composition -/

/-! ## Pointwise arithmetic -/

/-- The statement for `H (f k) (g k)`. -/
noncomputable def arithS {H : ℕ → ℕ → ℕ} (O : ArithOp H) (Mf Mg : Machine) :
    CStm (need Mf + need Mg + 9) (need Mf + need Mg) :=
  seqL [startS _ 9 (by omega), callS Mf _ 9 (by omega) (ex _ 9 0),
    .set (ex _ 9 3) (.var (ρs Mf _ 9 (by omega) .out)),
    callS Mg _ 9 (by omega) (ex _ 9 0),
    .set (ex _ 9 4) (.var (ρs Mg _ 9 (by omega) .out)),
    O.op (ex _ 9 3) (ex _ 9 4) (ex _ 9 5) (ex _ 9 6) (ex _ 9 7) (ex _ 9 8),
    .emit (.var (ex _ 9 5))]

lemma ex_injective (C E : ℕ) : Function.Injective (ex C E) := fun i j h => by
  by_contra hij; exact ex_ne_ex hij h

theorem MachineComputable.arith {H : ℕ → ℕ → ℕ} (O : ArithOp H) {f g : ℕ → ℕ}
    (hf : MachineComputable f) (hg : MachineComputable g) :
    MachineComputable fun k => H (f k) (g k) := by
  obtain ⟨Mf, -, hMf⟩ := hf
  obtain ⟨Mg, -, hMg⟩ := hg
  refine machineComputable_of_stm (arithS O Mf Mg) _ fun k => ?_
  obtain ⟨tf, htf⟩ := hMf k
  obtain ⟨tg, htg⟩ := hMg k
  set C := need Mf + need Mg
  set w := k + haltTime Mf (encodeNat k) + f k + haltTime Mg (encodeNat k) + g k +
    simB Mf + simB Mg + O.W (f k) (g k) + H (f k) (g k) + 2 with hwdef
  have hw : 2 ≤ w := by omega
  refine ⟨w, hw, ?_⟩
  obtain ⟨st1, T1, g1, e1k, e1s, e1b, e1p, e1o⟩ := start_good C 9 (by omega) hw k (by omega)
  obtain ⟨st2, T2, g2, e2o, -, e2s, e2x, e2b, e2p, e2out⟩ := call_good (x := encodeNat k)
    (by omega : need Mf ≤ C) hw (lt_two_pow_of_le (by omega)).le st1 e1b e1p e1s
    (ex _ 9 0) e1k (lt_two_pow_of_le (by omega)) htf (lt_two_pow_of_le (by omega))
    (by have := bits_length_le (f k); omega)
  -- save `f k`
  set st3 := st2.set (ex C 9 3) (f k) with hst3
  have g3 : Good (encodeNat k) w (.set (ex C 9 3) (.var (ρs Mf C 9 (by omega) .out)) :
      CStm (C + 9) C) st2 st3 (Ex.nodeCost w + unitCost w) := by
    have e : st3 = st2.set (ex C 9 3)
        ((Ex.var (ρs Mf C 9 (by omega) .out) : Ex (C + 9)).eval st2.env) := by
      rw [hst3]; congr 1; simp only [Ex.eval]; exact e2o.symm
    rw [e]; exact (Good.set (by simp only [Ex.Fits, e2o]; exact lt_two_pow_of_le (by omega))).mono
      (by simp [Ex.size])
  have hb3 := Good.bdd hw g3 e2b (by omega)
  have e3k : st3.env (ex C 9 ⟨0, by omega⟩) = k := by
    rw [hst3, NSt.set_env, Function.update_of_ne (ex_ne_ex (by simp)), e2x, e1k]
  obtain ⟨st4, T4, g4, e4o, -, e4s, e4x, e4b, e4p, e4out⟩ := call_good (x := encodeNat k)
    (by omega : need Mg ≤ C) hw (lt_two_pow_of_le (by omega)).le st3 hb3.1 hb3.2
    (fun q => by simp [hst3, e2s]) (ex _ 9 0) e3k (lt_two_pow_of_le (by omega)) htg
    (lt_two_pow_of_le (by omega)) (by have := bits_length_le (g k); omega)
  -- save `g k`
  set st5 := st4.set (ex C 9 4) (g k) with hst5
  have g5 : Good (encodeNat k) w (.set (ex C 9 4) (.var (ρs Mg C 9 (by omega) .out)) :
      CStm (C + 9) C) st4 st5 (Ex.nodeCost w + unitCost w) := by
    have e : st5 = st4.set (ex C 9 4)
        ((Ex.var (ρs Mg C 9 (by omega) .out) : Ex (C + 9)).eval st4.env) := by
      rw [hst5]; congr 1; simp only [Ex.eval]; exact e4o.symm
    rw [e]; exact (Good.set (by simp only [Ex.Fits, e4o]; exact lt_two_pow_of_le (by omega))).mono
      (by simp [Ex.size])
  have e5a : st5.env (ex C 9 3) = f k := by
    rw [hst5, NSt.set_env, Function.update_of_ne (ex_ne_ex (by simp)), e4x, hst3]; simp
  have e5b : st5.env (ex C 9 4) = g k := by rw [hst5]; simp
  -- the operation
  have hnd : [ex C 9 3, ex C 9 4, ex C 9 5, ex C 9 6, ex C 9 7, ex C 9 8].Nodup := by
    have : ([3, 4, 5, 6, 7, 8] : List (Fin 9)).Nodup := by decide
    simpa using this.map (ex_injective C 9)
  obtain ⟨o1, o2, -, -, -, o6⟩ := O.spec (x := encodeNat k) (w := w) _ _ _ _ _ _ hnd hw st5
    (by rw [e5a, e5b]; omega)
  set st6 := exec (encodeNat k) (O.op (ex C 9 3) (ex C 9 4) (ex C 9 5) (ex C 9 6) (ex C 9 7)
    (ex C 9 8)) st5 with hst6
  have g6 : Good (encodeNat k) w (O.op (ex C 9 3) (ex C 9 4) (ex C 9 5) (ex C 9 6) (ex C 9 7)
    (ex C 9 8)) st5 st6 _ := ⟨o1, rfl, le_rfl⟩
  rw [e5a, e5b] at o2
  have g7 := Good.emit (x := encodeNat k) (w := w) (st := st6) (e := .var (ex C 9 5))
    (by simp only [Ex.Fits, o2]; exact lt_two_pow_of_le (by omega))
  refine ⟨_, _, g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq (g7.seq Good.skip)))))), ?_⟩
  simp [Ex.eval, o2, o6, hst5, e4out, hst3, e2out, e1o]

theorem MachineComputable.add {f g : ℕ → ℕ} (hf : MachineComputable f)
    (hg : MachineComputable g) : MachineComputable fun k => f k + g k :=
  MachineComputable.arith addOp hf hg

theorem MachineComputable.mul {f g : ℕ → ℕ} (hf : MachineComputable f)
    (hg : MachineComputable g) : MachineComputable fun k => f k * g k :=
  MachineComputable.arith mulOp hf hg

theorem MachineComputable.pow {f g : ℕ → ℕ} (hf : MachineComputable f)
    (hg : MachineComputable g) : MachineComputable fun k => f k ^ g k :=
  MachineComputable.arith powOp hf hg

theorem MachineComputable.pow_const {f : ℕ → ℕ} (hf : MachineComputable f) (e : ℕ) :
    MachineComputable fun k => f k ^ e :=
  MachineComputable.pow hf (MachineComputable.const e)

theorem MachineComputable.add_const {f : ℕ → ℕ} (hf : MachineComputable f) (b : ℕ) :
    MachineComputable fun k => f k + b :=
  MachineComputable.add hf (MachineComputable.const b)

theorem MachineComputable.mul_const {f : ℕ → ℕ} (hf : MachineComputable f) (a : ℕ) :
    MachineComputable fun k => a * f k :=
  MachineComputable.mul (MachineComputable.const a) hf

end Lax119563Proofs.Computability
