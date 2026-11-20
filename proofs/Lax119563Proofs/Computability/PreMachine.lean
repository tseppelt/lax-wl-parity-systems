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

end Lax119563Proofs.Computability
