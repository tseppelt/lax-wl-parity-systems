import Lax119563Proofs.Computability.Param

/-!
# A machine preparing the parameter for an fpt-reduction

**`exists_param_machine`**: for a parameterized problem `P` with polynomial-time
parameterization and a computable `f`, some deterministic machine computes, from `x`,

  `encodeNats ([P.κ x, f (P.κ x)] ++ x.map Bool.toNat)`

(the parameter, the value of `f` at the parameter, and the bits of `x` as numbers `0`/`1`)
within `F (P.κ x) · (|x| + 1)^e` steps, for a computable `F` and a constant `e`. A reduction
machine reading this layout can be composed after it with `Main.Compose.compose_computesWithin`.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime Lax119563.ParameterizedComplexity
open Lax489179.TuringMachine (Machine Config Instruction Move Deterministic)

namespace Lax119563Proofs.Computability

open CStm

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

/-! ## Emitting the bits of the input -/

/-- Emit the bits of the input from the cursor on, as numbers `0`/`1`. -/
def emitBits (t : Fin R) : CStm R Q :=
  .seq (.rd t) (.loop (.var t) (.seq (.emit (.half (.var t))) (.rd t)))

lemma half_symOf (b : Bool) : symOf b / 2 = b.toNat := by cases b <;> rfl

lemma emitBits_good (hw : 2 ≤ w) {t : Fin R} (st : NSt R Q) (hpos : st.pos = 0) :
    Good x w (emitBits t) st (exec x (emitBits t) st) ((x.length + 1) * (8 * Ex.nodeCost w)) ∧
      (exec x (emitBits t) st).out = st.out ++ x.map Bool.toNat ∧
      (∀ r, r ≠ t → (exec x (emitBits t) st).env r = st.env r) ∧
      (exec x (emitBits t) st).stk = st.stk := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  set B : CStm R Q := .seq (.emit (.half (.var t))) (.rd t) with hB
  set st1 : NSt R Q := exec x (.rd t) st with hst1
  set S : ℕ → NSt R Q := fun j => iter x B st1 j with hS
  have hinb : ∀ j, inBit x j ≤ 2 := fun j => by
    rw [inBit_eq]; split_ifs
    · exact symOf_le _
    · omega
  have hSj : ∀ j ≤ x.length, (S j).env t = inBit x j ∧ (S j).pos = min (j + 1) x.length ∧
      (S j).out = st.out ++ (x.take j).map Bool.toNat ∧
      (∀ r, r ≠ t → (S j).env r = st.env r) ∧ (S j).stk = st.stk := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [hS, iter_zero, hst1, exec, NSt.set_env, Function.update_self, hpos]
      refine ⟨by simp, by simp, by simp, fun r hr => by simp [Function.update_of_ne hr],
        by simp⟩
    | succ j ih =>
      intro hj
      obtain ⟨i1, i2, i3, i4, i5⟩ := ih (by omega)
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      simp only [hB, exec, NSt.set_env, Function.update_self, NSt.set_pos, i2,
        min_eq_left (show j + 1 ≤ x.length by omega)]
      refine ⟨by simp, by simp, ?_, fun r hr => by simp [Function.update_of_ne hr, i4 r hr],
        by simp [i5]⟩
      simp only [NSt.set_out, Ex.eval, i1, i3, inBit_eq, dif_pos (show j < x.length by omega),
        half_symOf, List.take_add_one, List.getElem?_eq_getElem (show j < x.length by omega)]
      simp only [List.map_append, List.map_cons, List.map_nil, Option.toList_some,
        List.append_assoc]
  have hloop := Good.loop_const (x := x) (w := w) (e := .var t) (body := B) x.length S
    (3 * Ex.nodeCost w + 2 * unitCost w)
    (fun j hj => by
      simp only [Ex.eval, (hSj j hj.le).1, inBit_eq, dif_pos hj]; exact (symOf_pos _).ne')
    (by simp only [Ex.eval, (hSj _ le_rfl).1, inBit_eq, dif_neg (lt_irrefl _)])
    (fun j hj => by simp only [Ex.Fits, (hSj j hj).1]; have := hinb j; omega)
    (fun j hj => by
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      refine ((Good.emit ?_).seq (Good.rd t)).mono (by simp [Ex.size]; omega)
      simp only [Ex.Fits, (hSj j hj.le).1]; have := hinb j; omega)
  have g : Good x w (emitBits t) st (S x.length) _ := (Good.rd t).seq hloop
  have hex : exec x (emitBits t) st = S x.length := g.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hex]; refine g.mono ?_; simp only [condCost, Ex.size]; nlinarith
  · rw [hex, (hSj _ le_rfl).2.2.1, List.take_length]
  · rw [hex]; exact (hSj _ le_rfl).2.2.2.1
  · rw [hex]; exact (hSj _ le_rfl).2.2.2.2

/-! ## Arithmetic of the time bound -/

lemma pre_arith {Kκ Kf N U X P g a sκ kk sf L A B : ℕ} (hX : 1 ≤ X) (hP : 1 ≤ P) (hg : 1 ≤ g)
    (hU : U ≤ N) (hN1 : 1 ≤ N) (hN : N ≤ 64 * g ^ 2 * P ^ 2)
    (h1 : a + sκ + 1 ≤ 3 * g * P * X) (h2 : kk + sf + 1 ≤ 2 * g) (h3 : a + 1 ≤ X)
    (h4 : L ≤ 2 * g + 3 * X)
    (hA : A ≤ Kκ * (a + sκ + 1) * N) (hB : B ≤ Kf * (kk + sf + 1) * N) :
    A + B + 9 * N + 2 * (N + U) + U * (a + 1) + (a + 1) * (8 * N) + U + 20 * (a + L) + 10 ≤
      64 * (3 * Kκ + 2 * Kf + 173) * g ^ 3 * (P ^ 3 * X) := by
  have hPX : 1 ≤ P * X := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set Z := g * P * X * N with hZ
  have eA : A ≤ 3 * Kκ * Z := by
    calc A ≤ Kκ * (a + sκ + 1) * N := hA
      _ ≤ Kκ * (3 * g * P * X) * N := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
      _ = 3 * Kκ * Z := by rw [hZ]; ring
  have eB : B ≤ 2 * Kf * Z := by
    calc B ≤ Kf * (kk + sf + 1) * N := hB
      _ ≤ Kf * (2 * g) * N := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
      _ ≤ Kf * (2 * g * (P * X)) * N :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hPX))
      _ = 2 * Kf * Z := by rw [hZ]; ring
  have eX : X * N ≤ Z := by
    rw [hZ]
    calc X * N = 1 * 1 * X * N := by ring
      _ ≤ g * P * X * N :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul hg hP))
  have eC : 9 * N + 2 * (N + U) + U * (a + 1) + (a + 1) * (8 * N) + U ≤ 23 * Z := by
    have c1 : U * (a + 1) ≤ X * N := by rw [mul_comm X]; exact Nat.mul_le_mul hU h3
    have c2 : (a + 1) * (8 * N) ≤ 8 * (X * N) := by
      rw [show (a + 1) * (8 * N) = 8 * ((a + 1) * N) by ring]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h3)
    have c3 : N ≤ X * N := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have eD : 20 * (a + L) + 10 ≤ 150 * Z := by
    have c4 : X ≤ g * X := Nat.le_mul_of_pos_left _ (by omega)
    have c5 : g ≤ g * X := Nat.le_mul_of_pos_right _ (by omega)
    have c7 : g * X ≤ Z := by
      rw [hZ]
      calc g * X = g * 1 * X * 1 := by ring
        _ ≤ g * P * X * N :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hP)) hN1
    omega
  have hZ' : Z ≤ g * P * X * (64 * g ^ 2 * P ^ 2) := by
    rw [hZ]; exact Nat.mul_le_mul_left _ hN
  have e : (3 * Kκ + 2 * Kf + 173) * Z = 3 * Kκ * Z + 2 * Kf * Z + 173 * Z := by ring
  calc _ ≤ (3 * Kκ + 2 * Kf + 173) * Z := by omega
    _ ≤ (3 * Kκ + 2 * Kf + 173) * (g * P * X * (64 * g ^ 2 * P ^ 2)) :=
        Nat.mul_le_mul_left _ hZ'
    _ = 64 * (3 * Kκ + 2 * Kf + 173) * g ^ 3 * (P ^ 3 * X) := by ring

/-! ## The preparation machine -/

lemma length_encodeNats_bits (x : List Bool) :
    (encodeNats (x.map Bool.toNat)).length ≤ 3 * x.length := by
  induction x with
  | nil => simp [encodeNats]
  | cons b x ih =>
    simp only [List.map_cons, encodeNats, List.flatMap_cons, List.length_append,
      List.length_cons] at ih ⊢
    have : (encodeNat b.toNat).length ≤ 3 := by cases b <;> simp [encodeNat, Nat.bits]
    omega

/-- The preparation statement: the parameter, `f` of it, then the bits of the input. -/
noncomputable def preS (Mκ Mf : Machine) : CStm (need Mκ + need Mf + 5) (need Mκ + need Mf) :=
  seqL [paramS Mκ Mf (need Mκ + need Mf) 5 (by omega) (by omega) (by omega),
    .emit (.var (ex _ 5 0)), .emit (.var (ex _ 5 1)), .rst, emitBits (ex _ 5 3)]

/-- **Preparing the parameter.** For `P` with polynomial-time parameterization and a computable
`f`, a machine computes `encodeNats ([P.κ x, f (P.κ x)] ++ x.map Bool.toNat)` from `x` within
`F (P.κ x) · (|x| + 1)^e` steps, for a computable `F`. -/
theorem exists_param_machine {P : ParameterizedProblem} (hP : IsParameterized P) {f : ℕ → ℕ}
    (hf : MachineComputable f) :
    ∃ M : Machine, Deterministic M ∧ ∃ F : ℕ → ℕ, MachineComputable F ∧ ∃ e : ℕ,
      ∀ x : List Bool, ComputesWithin M x
        (encodeNats ([P.κ x, f (P.κ x)] ++ x.map Bool.toNat)) (F (P.κ x) * (x.length + 1) ^ e) := by
  obtain ⟨Mκ, -, Cκ, d, hκ⟩ := hP
  obtain ⟨Mf, -, hMf, hT⟩ := MachineComputable.exists_time hf
  set g : ℕ → ℕ := fun k => 5 + simB Mκ + simB Mf + k + f k + haltTime Mf (encodeNat k) + 2 * Cκ
    with hgdef
  set K := 64 * (3 * simK Mκ + 2 * simK Mf + 173) with hK
  have hG : MachineComputable g :=
    MachineComputable.add_const (MachineComputable.add (MachineComputable.add
      (MachineComputable.add (MachineComputable.const (5 + simB Mκ + simB Mf))
        MachineComputable.id') hf) hT) (2 * Cκ)
  refine ⟨(preS Mκ Mf).machine (preS Mκ Mf).depth, CStm.machine_deterministic _ _,
    fun k => K * g k ^ 3, MachineComputable.mul_const (MachineComputable.pow_const hG 3) K,
    3 * d + 1, fun x => ?_⟩
  have hκx := hκ x
  generalize hk : P.κ x = k at hκx ⊢
  have hgk : g k = 5 + simB Mκ + simB Mf + k + f k + haltTime Mf (encodeNat k) + 2 * Cκ := rfl
  set X := x.length + 1 with hX
  set Pw := X ^ d with hPw
  have hPw1 : 1 ≤ Pw := Nat.one_le_pow _ _ (by omega)
  set w := 2 + simB Mκ + simB Mf + k + f k + haltTime Mf (encodeNat k) + Cκ + Cκ * Pw with hwdef
  have hw : 2 ≤ w := by omega
  have hsκ : haltTime Mκ x ≤ Cκ * Pw + Cκ := by
    refine (haltTime_le_of_computesWithin hκx).trans ?_
    have : x.length ^ d ≤ Pw := Nat.pow_le_pow_left (by omega) d
    have := Nat.mul_le_mul_left Cκ this
    omega
  have hlt : ∀ y, y ≤ w → y < 2 ^ w := fun y hy => lt_two_pow_of_le hy
  obtain ⟨st5, g5, e5k, e5v, -, -, e5s, e5b, e5p, e5o⟩ := paramS_good (x := x) (w := w)
    (C := need Mκ + need Mf) (E := 5) (by omega) (by omega) (by omega) hw
    (hlt _ (by omega)).le (hlt _ (by omega)).le (NSt.zero _ _) (bdd_zero _ _ _)
    (by simp [NSt.zero]) (fun q => by simp [NSt.zero]) hκx (hMf k) (hlt _ (by omega))
    (by have := bits_length_le k; omega) (hlt _ (by omega)) (hlt _ (by omega))
    (by have := bits_length_le (f k); omega) (hlt _ (by omega))
  have g6 := Good.emit (x := x) (w := w) (st := st5) (e := .var (ex _ 5 ⟨0, by omega⟩))
    (by simp only [Ex.Fits, e5k]; exact hlt _ (by omega))
  set st6 : NSt (need Mκ + need Mf + 5) (need Mκ + need Mf) :=
    { st5 with out := st5.out ++ [(Ex.var (ex _ 5 ⟨0, by omega⟩) : Ex _).eval st5.env] } with hst6
  have g7 := Good.emit (x := x) (w := w) (st := st6) (e := .var (ex _ 5 ⟨1, by omega⟩))
    (by simp only [Ex.Fits, hst6, e5v]; exact hlt _ (by omega))
  set st7 : NSt (need Mκ + need Mf + 5) (need Mκ + need Mf) :=
    { st6 with out := st6.out ++ [(Ex.var (ex _ 5 ⟨1, by omega⟩) : Ex _).eval st6.env] } with hst7
  have g8 := Good.rst (x := x) (w := w) (Q := need Mκ + need Mf) (st := st7)
  set st8 : NSt (need Mκ + need Mf + 5) (need Mκ + need Mf) := { st7 with pos := 0 } with hst8
  obtain ⟨g9, e9o, -, -⟩ := emitBits_good (x := x) (t := ex _ 5 ⟨3, by omega⟩) hw st8 rfl
  have gg : Good x w (preS Mκ Mf) (NSt.zero _ _) _ _ :=
    g5.seq (g6.seq (g7.seq (g8.seq (g9.seq Good.skip))))
  have e5k' : st5.env (ex (need Mκ + need Mf) 5 0) = k := e5k
  have e5v' : st5.env (ex (need Mκ + need Mf) 5 1) = f k := e5v
  have hout : (exec x (emitBits (ex _ 5 ⟨3, by omega⟩)) st8).out =
      [k, f k] ++ x.map Bool.toNat := by
    rw [e9o]; simp [hst8, hst7, hst6, Ex.eval, e5k', e5v', e5o, NSt.zero]
  have hc := CStm.computesWithin (D := (preS Mκ Mf).depth) hw le_rfl gg.1
  rw [gg.2.1, hout] at hc
  refine Lax119563Proofs.Reduction.ComputesWithin.mono hc ?_
  have hcost := gg.2.2
  have hp7 : st7.pos = x.length := by simp [hst7, hst6, e5p]
  rw [hp7] at hcost
  -- the arithmetic
  have hN := Ex.unitCost_le_nodeCost w
  have hN1 : 1 ≤ Ex.nodeCost w := by have := unitCost_ge w; omega
  have hNw : Ex.nodeCost w ≤ 64 * g k ^ 2 * Pw ^ 2 := by
    have hw3 : w + 3 ≤ g k * Pw := by
      have h0 : (5 + simB Mκ + simB Mf + k + f k + haltTime Mf (encodeNat k) + Cκ) ≤
          (5 + simB Mκ + simB Mf + k + f k + haltTime Mf (encodeNat k) + Cκ) * Pw :=
        Nat.le_mul_of_pos_right _ hPw1
      have h1 : g k * Pw = (5 + simB Mκ + simB Mf + k + f k + haltTime Mf (encodeNat k) + Cκ) * Pw +
          Cκ * Pw := by rw [hgk]; ring
      omega
    have : Ex.nodeCost w ≤ 64 * (w + 3) ^ 2 := by
      have e : 64 * (w + 3) ^ 2 = (w + 3) * (64 * (w + 3)) := by ring
      rw [e]; simp only [Ex.nodeCost, unitCost]
      exact Nat.mul_le_mul_left _ (by omega)
    calc Ex.nodeCost w ≤ 64 * (w + 3) ^ 2 := this
      _ ≤ 64 * (g k * Pw) ^ 2 := by gcongr
      _ = 64 * g k ^ 2 * Pw ^ 2 := by ring
  have hgk1 : 1 ≤ g k := by rw [hgk]; omega
  have h1 : x.length + haltTime Mκ x + 1 ≤ 3 * g k * Pw * X := by
    rw [show 3 * g k * Pw * X = 3 * (g k * Pw * X) by ring]
    have a1 : X ≤ g k * Pw * X := by
      calc X = 1 * 1 * X := by ring
        _ ≤ g k * Pw * X := Nat.mul_le_mul_right _ (Nat.mul_le_mul hgk1 hPw1)
    have a2 : Cκ * Pw ≤ g k * Pw * X := by
      calc Cκ * Pw = Cκ * Pw * 1 := by ring
        _ ≤ g k * Pw * X := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by rw [hgk]; omega))
            (by omega)
    have a3 : Cκ ≤ g k * Pw * X := by
      calc Cκ = Cκ * 1 * 1 := by ring
        _ ≤ g k * Pw * X := Nat.mul_le_mul (Nat.mul_le_mul (by rw [hgk]; omega) hPw1)
            (by omega)
    omega
  have h2 : (encodeNat k).length + haltTime Mf (encodeNat k) + 1 ≤ 2 * g k := by
    have := bits_length_le k
    rw [length_encodeNat, hgk]; omega
  have h4 : (encodeNats ([k, f k] ++ x.map Bool.toNat)).length ≤ 2 * g k + 3 * X := by
    have hb := length_encodeNats_bits x
    have := bits_length_le k
    have := bits_length_le (f k)
    simp only [encodeNats, List.cons_append, List.flatMap_cons, List.length_append,
      List.nil_append] at hb ⊢
    rw [length_encodeNat, length_encodeNat, hgk]; omega
  have key := pre_arith (Kκ := simK Mκ) (Kf := simK Mf) (U := unitCost w) (X := X) (P := Pw)
    (a := x.length) (sκ := haltTime Mκ x) (kk := (encodeNat k).length)
    (sf := haltTime Mf (encodeNat k)) (by omega) hPw1 hgk1 hN hN1 hNw h1 h2 (by omega) h4
    (simInCost_le Mκ w _ _) (simNatCost_le Mf w _ _)
  have hpow : Pw ^ 3 * X = X ^ (3 * d + 1) := by rw [hPw, ← pow_mul, pow_succ, mul_comm d 3]
  rw [hpow] at key
  simp only [Ex.size] at hcost
  show _ ≤ K * g k ^ 3 * X ^ (3 * d + 1)
  rw [hK]
  omega

end Lax119563Proofs.Computability
