import Lax119563Proofs.Computability.Closure

/-!
# Monotone majorants of computable functions

The running maximum `runMax f k = max_{i ≤ k} f i` of a computable function is computable
(`MachineComputable.runMax`); hence every computable function has a computable monotone
majorant (`MachineComputable.exists_monotone_ge`). The statement computing it calls the
simulator of a machine for `f` on `0, 1, …, k` in a loop.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime Lax119563.ParameterizedComplexity
open Lax489179.TuringMachine (Machine Config Instruction Move Deterministic)

namespace Lax119563Proofs.Computability

open CStm

variable {x : List Bool} {w : ℕ}

/-- The running maximum `max_{i ≤ k} f i`. -/
def runMax (f : ℕ → ℕ) (k : ℕ) : ℕ := (Finset.range (k + 1)).sup f

lemma runMax_monotone (f : ℕ → ℕ) : Monotone (runMax f) := fun a b hab =>
  Finset.sup_mono (Finset.range_subset_range.mpr (by omega))

lemma le_runMax (f : ℕ → ℕ) (k : ℕ) : f k ≤ runMax f k :=
  Finset.le_sup (f := f) (Finset.mem_range.mpr (by omega))

/-- The body of the running-maximum loop. -/
noncomputable def supBody (M : Machine) : CStm (need M + 6) (need M) :=
  seqL [callS M (need M) 6 le_rfl (ex _ 6 4),
    .ite (.lt (.var (ex _ 6 3)) (.var (ρs M (need M) 6 le_rfl .out)))
      (.set (ex _ 6 3) (.var (ρs M (need M) 6 le_rfl .out))) .skip,
    .set (ex _ 6 4) (.add (.var (ex _ 6 4)) (.const 1))]

/-- The statement for the running maximum. -/
noncomputable def supS (M : Machine) : CStm (need M + 6) (need M) :=
  seqL [startS _ 6 (by omega), .set (ex _ 6 3) (.const 0), .set (ex _ 6 4) (.const 0),
    .loop (.lt (.var (ex _ 6 4)) (.add (.var (ex _ 6 0)) (.const 1))) (supBody M),
    .emit (.var (ex _ 6 3))]

/-- The invariant of the running-maximum loop. -/
def SupInv {C : ℕ} (f : ℕ → ℕ) (k a j : ℕ) (w : ℕ) (st : NSt (C + 6) C) : Prop :=
  st.env (ex C 6 0) = k ∧ st.env (ex C 6 3) = (Finset.range j).sup f ∧ st.env (ex C 6 4) = j ∧
    (∀ q, st.stk q = []) ∧ st.Bdd w ∧ st.pos ≤ a ∧ st.out = []

lemma supBody_step {M : Machine} {f : ℕ → ℕ} (hw : 2 ≤ w) (hB : simB M ≤ 2 ^ w) {k j : ℕ}
    (st : NSt (need M + 6) (need M)) (hI : SupInv f k x.length j w st)
    {t : ℕ} (hM : ComputesWithin M (encodeNat j) (encodeNat (f j)) t)
    (hs : haltTime M (encodeNat j) < 2 ^ w) (hv : (f j).bits.length < w)
    (hsup : (Finset.range (j + 1)).sup f + j + 1 < 2 ^ w) :
    Fits x w (supBody M) st ∧ SupInv f k x.length (j + 1) w (exec x (supBody M) st) := by
  have hU := Ex.unitCost_le_nodeCost w
  obtain ⟨i0, i3, i4, is, ib, ip, io⟩ := hI
  have hj2 : j < 2 ^ w := by omega
  obtain ⟨st1, T1, g1, e1o, -, e1s, e1x, e1b, e1p, e1out⟩ := call_good (x := x) le_rfl hw hB st
    ib ip is (ex _ 6 4) i4 hj2 hM hs hv
  have e13 : st1.env (ex _ 6 3) = (Finset.range j).sup f := by rw [e1x, i3]
  set m := (Finset.range j).sup f with hm
  have hsucc : (Finset.range (j + 1)).sup f = max m (f j) := by
    rw [Finset.range_add_one, Finset.sup_insert, max_comm]
  have hm' : m ≤ (Finset.range (j + 1)).sup f := by rw [hsucc]; exact le_max_left _ _
  have hfj : f j ≤ (Finset.range (j + 1)).sup f := by rw [hsucc]; exact le_max_right _ _
  set st2 := st1.set (ex _ 6 3) (max m (f j)) with hst2
  have hfit : (Ex.lt (.var (ex _ 6 3)) (.var (ρs M (need M) 6 le_rfl .out)) :
      Ex (need M + 6)).Fits w st1.env := by
    simp only [Ex.Fits, e13, e1o]; exact ⟨by omega, by omega⟩
  have g2 : Good x w (.ite (.lt (.var (ex _ 6 3)) (.var (ρs M (need M) 6 le_rfl .out)))
      (.set (ex _ 6 3) (.var (ρs M (need M) 6 le_rfl .out))) .skip) st1 st2
      (4 * Ex.nodeCost w + 2 * unitCost w + 1) := by
    by_cases hlt : m < f j
    · refine (Good.iteT hfit (by simp [Ex.eval, e13, e1o, hlt]) (Good.set ?_)).of_eq ?_ ?_
      · simp only [Ex.Fits, e1o]; omega
      · rw [hst2, max_eq_right hlt.le]; simp [Ex.eval, e1o]
      · simp [condCost, Ex.size]; omega
    · refine (Good.iteF hfit (by simp [Ex.eval, e13, e1o, hlt]) Good.skip).of_eq ?_ ?_
      · rw [hst2, max_eq_left (by omega)]
        refine NSt.ext ?_ rfl rfl rfl
        funext r
        by_cases hr : r = ex _ 6 3
        · subst hr; simp [e13]
        · simp [Function.update_of_ne hr]
      · simp [condCost, Ex.size]; omega
  have e24 : st2.env (ex _ 6 4) = j := by
    rw [hst2, NSt.set_env, Function.update_of_ne (ex_ne_ex (by simp)), e1x, i4]
  set st3 := st2.set (ex _ 6 4) (j + 1) with hst3
  have g3 : Good x w (.set (ex _ 6 4) (.add (.var (ex _ 6 4)) (.const 1)) :
      CStm (need M + 6) (need M)) st2 st3 (3 * Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits, Ex.eval, e24]; exact ⟨by omega, by omega, by omega⟩)).of_eq
      (by simp [Ex.eval, e24, hst3]) (by simp [Ex.size])
  have g : Good x w (supBody M) st st3 _ := g1.seq (g2.seq (g3.seq Good.skip))
  have hb := Good.bdd hw g ib (by omega)
  refine ⟨g.1, ?_⟩
  rw [g.2.1]
  refine ⟨?_, ?_, by simp [hst3], fun q => by simp [hst3, hst2, e1s], hb.1, by
    rw [hst3, hst2]; simp only [NSt.set_pos]; omega, by simp [hst3, hst2, e1out, io]⟩
  · rw [hst3, NSt.set_env, Function.update_of_ne (ex_ne_ex (by simp)), hst2, NSt.set_env,
      Function.update_of_ne (ex_ne_ex (by simp)), e1x, i0]
  · rw [hst3, NSt.set_env, Function.update_of_ne (ex_ne_ex (by simp)), hst2, hsucc]; simp

/-- **Running maxima are computable.** -/
theorem MachineComputable.runMax {f : ℕ → ℕ} (hf : MachineComputable f) :
    MachineComputable (Computability.runMax f) := by
  obtain ⟨M, -, hM⟩ := hf
  refine machineComputable_of_stm (supS M) _ fun k => ?_
  set W := ∑ i ∈ Finset.range (k + 1), (haltTime M (encodeNat i) + f i) with hW
  have hWi : ∀ i ≤ k, haltTime M (encodeNat i) + f i ≤ W := fun i hi =>
    Finset.single_le_sum (f := fun i => haltTime M (encodeNat i) + f i) (fun _ _ => by omega)
      (Finset.mem_range.mpr (by omega))
  have hsupW : ∀ j ≤ k + 1, (Finset.range j).sup f ≤ W := fun j hj =>
    Finset.sup_le fun i hi => by
      have := hWi i (by simp at hi; omega); omega
  set w := k + W + simB M + 4 with hwdef
  have hw : 2 ≤ w := by omega
  refine ⟨w, hw, ?_⟩
  obtain ⟨st1, T1, g1, e1k, e1s, e1b, e1p, e1o⟩ := start_good (need M) 6 (by omega) hw k
    (by omega)
  set S0 := (st1.set (ex _ 6 3) 0).set (ex _ 6 4) 0 with hS0
  have g0a : Good (encodeNat k) w (.set (ex _ 6 3) (.const 0) : CStm (need M + 6) (need M)) st1
      (st1.set (ex _ 6 3) 0) _ := Good.set (by simp [Ex.Fits])
  have g0b : Good (encodeNat k) w (.set (ex _ 6 4) (.const 0) : CStm (need M + 6) (need M))
      (st1.set (ex _ 6 3) 0) S0 _ := Good.set (by simp [Ex.Fits])
  have hb0 := Good.bdd hw (g0a.seq g0b) e1b (by omega)
  have I0 : SupInv f k (encodeNat k).length 0 w S0 := by
    refine ⟨?_, ?_, by simp [hS0], fun q => by simp [hS0, e1s], hb0.1, by simp [hS0]; omega,
      by simp [hS0, e1o]⟩
    · rw [hS0, NSt.set_env, Function.update_of_ne (ex_ne_ex (by simp)), NSt.set_env,
        Function.update_of_ne (ex_ne_ex (by simp))]
      exact e1k
    · rw [hS0, NSt.set_env, Function.update_of_ne (ex_ne_ex (by simp))]; simp
  set S : ℕ → NSt (need M + 6) (need M) := fun j => iter (encodeNat k) (supBody M) S0 j with hS
  have hstep : ∀ j ≤ k, SupInv f k (encodeNat k).length j w (S j) →
      Fits (encodeNat k) w (supBody M) (S j) ∧
        SupInv f k (encodeNat k).length (j + 1) w (S (j + 1)) := by
    intro j hj Ij
    obtain ⟨t, ht⟩ := hM j
    rw [show S (j + 1) = exec (encodeNat k) (supBody M) (S j) from iter_succ _ _ _]
    exact supBody_step hw (lt_two_pow_of_le (by omega)).le (S j) Ij ht
      (lt_two_pow_of_le (by have := hWi j hj; omega))
      (by have := bits_length_le (f j); have := hWi j hj; omega)
      (lt_two_pow_of_le (by have := hsupW (j + 1) (by omega); omega))
  have hSj : ∀ j ≤ k + 1, SupInv f k (encodeNat k).length j w (S j) := by
    intro j
    induction j with
    | zero => intro _; exact I0
    | succ j ih => intro hj; exact (hstep j (by omega) (ih (by omega))).2
  have hloop := Good.loop (x := encodeNat k) (w := w)
    (e := .lt (.var (ex _ 6 4)) (.add (.var (ex _ 6 0)) (.const 1))) (body := supBody M) (k + 1) S
    (fun j => cost (encodeNat k) w (supBody M) (S j))
    (fun j hj => by
      obtain ⟨i0, -, i4, -⟩ := hSj j hj.le
      simp [Ex.eval, i0, i4, hj])
    (by
      obtain ⟨i0, -, i4, -⟩ := hSj (k + 1) le_rfl
      simp [Ex.eval, i0, i4])
    (fun j hj => by
      obtain ⟨i0, -, i4, -⟩ := hSj j hj
      simp only [Ex.Fits, Ex.eval, i0, i4]
      exact ⟨lt_two_pow_of_le (by omega), lt_two_pow_of_le (by omega),
        lt_two_pow_of_le (by omega), lt_two_pow_of_le (by omega)⟩)
    (fun j hj => by
      have := hstep j (by omega) (hSj j hj.le)
      rw [show S (j + 1) = exec (encodeNat k) (supBody M) (S j) from iter_succ _ _ _]
      exact ⟨this.1, rfl, le_rfl⟩)
  obtain ⟨-, i3, -, -, -, -, io⟩ := hSj (k + 1) le_rfl
  have hf3 : (Ex.var (ex (need M) 6 3) : Ex (need M + 6)).Fits w (S (k + 1)).env := by
    simp only [Ex.Fits, i3]; exact lt_two_pow_of_le (by have := hsupW (k + 1) le_rfl; omega)
  refine ⟨_, _, g1.seq (g0a.seq (g0b.seq (hloop.seq ((Good.emit hf3).seq Good.skip)))), ?_⟩
  simp [Ex.eval, i3, io, Computability.runMax]

/-- **Monotone majorants.** Every computable function is bounded by a computable monotone
function. -/
theorem MachineComputable.exists_monotone_ge {f : ℕ → ℕ} (hf : MachineComputable f) :
    ∃ g : ℕ → ℕ, MachineComputable g ∧ Monotone g ∧ ∀ k, f k ≤ g k :=
  ⟨Computability.runMax f, MachineComputable.runMax hf, runMax_monotone f, le_runMax f⟩

end Lax119563Proofs.Computability
