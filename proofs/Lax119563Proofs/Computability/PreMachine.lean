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

end Lax119563Proofs.Computability
