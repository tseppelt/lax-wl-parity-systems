import Lax119563Proofs.Computability.Clock

/-!
# Calling a computable function inside a statement

`callS M C E h src`: copy the register `src` into the input register of the simulator of `M`
and run the simulator (`call_good`). Afterwards the output register of the simulator holds
the value computed by `M`, all stacks are empty again, and the extra registers are kept.

`ArithOp H`: a statement computing `H a b` on registers (for large enough word size), with
instances for `+`, `·`, `max` and `^`.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime Lax119563.ParameterizedComplexity
open Lax489179.TuringMachine (Machine Config Instruction Move Deterministic)

namespace Lax119563Proofs.Computability

open CStm

variable {x : List Bool} {w : ℕ}

/-- Run the simulator of `M` on the value of the register `src`. -/
noncomputable def callS (M : Machine) (C E : ℕ) (h : need M ≤ C) (src : Fin (C + E)) :
    CStm (C + E) C :=
  .seq (.set (ρs M C E h .inp) (.var src)) (simNat M (ρs M C E h) (κs M C h))

theorem call_good {M : Machine} {C E : ℕ} (h : need M ≤ C) (hw : 2 ≤ w) (hB : simB M ≤ 2 ^ w)
    (st : NSt (C + E) C) (hb : st.Bdd w) (hp : st.pos ≤ x.length) (hemp : ∀ q, st.stk q = [])
    (src : Fin (C + E)) {k v t : ℕ} (hk : st.env src = k) (hkw : k < 2 ^ w)
    (hM : ComputesWithin M (encodeNat k) (encodeNat v) t)
    (hs : haltTime M (encodeNat k) < 2 ^ w) (hv : v.bits.length < w) :
    ∃ st' T, Good x w (callS M C E h src) st st' T ∧ st'.env (ρs M C E h .out) = v ∧
      st'.env (ρs M C E h .clk) = haltTime M (encodeNat k) ∧ (∀ q, st'.stk q = []) ∧
      (∀ i, st'.env (ex C E i) = st.env (ex C E i)) ∧ st'.Bdd w ∧ st'.pos = st.pos ∧
      st'.out = st.out := by
  set st1 := st.set (ρs M C E h .inp) k with hst1
  have g1 : Good x w (.set (ρs M C E h .inp) (.var src) : CStm (C + E) C) st st1
      (Ex.nodeCost w + unitCost w) := by
    have e : st1 = st.set (ρs M C E h .inp) ((Ex.var src : Ex (C + E)).eval st.env) := by
      rw [hst1]; congr 1; simp only [Ex.eval]; exact hk.symm
    rw [e]; exact (Good.set (by simp only [Ex.Fits, hk]; exact hkw)).mono (by simp [Ex.size])
  have hb1 := Good.bdd hw g1 hb hp
  obtain ⟨T, g2, e1, e2, e3, e4, e5, e6⟩ := simNat_slot (x := x) h hw hB st1 hb1.1 hb1.2
    (fun q => by simp [hst1, hemp]) (by simp [hst1]) hkw hM hs hv
  have g := g1.seq g2
  have hb2 := Good.bdd hw g hb hp
  refine ⟨_, _, g, e1, e2, e3, fun i => ?_, hb2.1, by rw [e5]; rfl, by rw [e6]; rfl⟩
  rw [e4, hst1, NSt.set_env, Function.update_of_ne (ρs_ne_ex M h _ i).symm]

/-! ## Arithmetic statements -/

/-- A statement computing `H a b` into `o` (scratch registers `s, t, u`), fitting whenever
`W a b ≤ w`. -/
structure ArithOp (H : ℕ → ℕ → ℕ) where
  /-- The statement. -/
  op : {R Q : ℕ} → Fin R → Fin R → Fin R → Fin R → Fin R → Fin R → CStm R Q
  /-- The word size needed. -/
  W : ℕ → ℕ → ℕ
  /-- Correctness. -/
  spec : ∀ {R Q : ℕ} {x : List Bool} {w : ℕ} (a b o s t u : Fin R), [a, b, o, s, t, u].Nodup →
    2 ≤ w → ∀ st : NSt R Q, W (st.env a) (st.env b) ≤ w →
      Fits x w (op a b o s t u) st ∧
      (exec x (op a b o s t u) st).env o = H (st.env a) (st.env b) ∧
      (∀ r, r ≠ o → r ≠ s → r ≠ t → r ≠ u → (exec x (op a b o s t u) st).env r = st.env r) ∧
      (exec x (op a b o s t u) st).stk = st.stk ∧ (exec x (op a b o s t u) st).pos = st.pos ∧
      (exec x (op a b o s t u) st).out = st.out

/-- Addition. -/
def addOp : ArithOp (· + ·) where
  op a b o _ _ _ := .set o (.add (.var a) (.var b))
  W A B := A + B
  spec := fun {R Q x w} a b o s t u hnd hw st hW => by
    refine ⟨?_, by simp [exec, Ex.eval], fun r hr _ _ _ => by simp [exec, Function.update_of_ne hr],
      rfl, rfl, rfl⟩
    simp only [Fits, Ex.Fits, Ex.eval]
    exact ⟨lt_two_pow_of_le (by omega), lt_two_pow_of_le (by omega), lt_two_pow_of_le hW⟩

lemma nodup6 {R : ℕ} {a b o s t u : Fin R} (h : [a, b, o, s, t, u].Nodup) :
    a ≠ b ∧ a ≠ o ∧ a ≠ s ∧ a ≠ t ∧ a ≠ u ∧ b ≠ o ∧ b ≠ s ∧ b ≠ t ∧ b ≠ u ∧ o ≠ s ∧ o ≠ t ∧
      o ≠ u ∧ s ≠ t ∧ s ≠ u ∧ t ≠ u := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  tauto

/-- Multiplication. -/
def mulOp : ArithOp (· * ·) where
  op a b o s _ _ := mulS o a b s
  W A B := A * B + B
  spec := fun {R Q x w} a b o s t u hnd hw st hW => by
    obtain ⟨hab, hao, has, -, -, hbo, hbs, -, -, hos, hot, hou, -, -, -⟩ := nodup6 hnd
    have g := mulS_good (x := x) hw hao.symm hbo.symm hos has hbs st rfl rfl
      (lt_two_pow_of_le (by omega)) (lt_two_pow_of_le (by omega))
    rw [g.2.1]
    refine ⟨g.1, by simp [Function.update_of_ne hos], fun r hr hr' _ _ => by
      simp [Function.update_of_ne hr, Function.update_of_ne hr'], rfl, rfl, rfl⟩

end Lax119563Proofs.Computability
