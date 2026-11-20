import Lax119563Proofs.Computability.Bridge

/-!
# Computable running times

**`MachineComputable.haltTime`**: if a machine `M` computes `f k` from `k` for every `k`, then
its running time `k ↦ haltTime M (encodeNat k)` (the least number of steps after which it has
halted on `encodeNat k`) is computable. The machine computing it simulates `M` with a step
counter (`Computability.simNat`) and outputs the counter.

**`MachineComputable.exists_time`**: every computable function is computed by a machine
whose running time is a computable function.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime Lax119563.ParameterizedComplexity
open Lax489179.TuringMachine (Machine Config Instruction Move Deterministic)

namespace Lax119563Proofs.Computability

open CStm

variable {w : ℕ}

/-! ## Reading the input number -/

/-- Read the input number into the extra register `0` (scratch: extra registers `1`, `2`). -/
def startS (C E : ℕ) (hE : 3 ≤ E) : CStm (C + E) C :=
  rdNumS (ex C E ⟨0, by omega⟩) (ex C E ⟨1, by omega⟩) (ex C E ⟨2, by omega⟩)

lemma start_good (C E : ℕ) (hE : 3 ≤ E) (hw : 2 ≤ w) (k : ℕ) (hk : k ≤ w - 1) :
    ∃ st T, Good (encodeNat k) w (startS C E hE) (NSt.zero (C + E) C) st T ∧
      st.env (ex C E ⟨0, by omega⟩) = k ∧ (∀ q, st.stk q = []) ∧ st.Bdd w ∧
      st.pos ≤ (encodeNat k).length ∧ st.out = [] := by
  have hn01 : ex C E ⟨0, by omega⟩ ≠ ex C E ⟨1, by omega⟩ := ex_ne_ex (by simp)
  have hn02 : ex C E ⟨0, by omega⟩ ≠ ex C E ⟨2, by omega⟩ := ex_ne_ex (by simp)
  have hn12 : ex C E ⟨1, by omega⟩ ≠ ex C E ⟨2, by omega⟩ := ex_ne_ex (by simp)
  have g := rdNumS_good (x := encodeNat k) (Q := C) hw hn01 hn02 hn12 (NSt.zero (C + E) C) k []
    (by simp [NSt.zero]) (by have := bits_length_le k; omega)
  have hb := Good.bdd hw g (bdd_zero _ _ _) (by simp [NSt.zero])
  refine ⟨_, _, g, ?_, fun q => by simp [rdNumFinal, NSt.zero], hb.1, hb.2, by
    simp [rdNumFinal, NSt.zero]⟩
  simp [rdNumFinal, Function.update_of_ne hn01, Function.update_of_ne hn02]

/-! ## The clock -/

/-- Output the halting time of `M` on `encodeNat k`, for the input `encodeNat k`. -/
noncomputable def clockS (M : Machine) : CStm (need M + 3) (need M) :=
  seqL [startS (need M) 3 le_rfl,
    .set (ρs M (need M) 3 le_rfl .inp) (.var (ex (need M) 3 ⟨0, by omega⟩)),
    simNat M (ρs M (need M) 3 le_rfl) (κs M (need M) le_rfl),
    .emit (.var (ρs M (need M) 3 le_rfl .clk))]

/-- **Running times are computable.** -/
theorem machineComputable_haltTime {M : Machine} {f : ℕ → ℕ}
    (hM : ∀ k, ∃ t, ComputesWithin M (encodeNat k) (encodeNat (f k)) t) :
    MachineComputable fun k => haltTime M (encodeNat k) := by
  refine machineComputable_of_stm (clockS M) _ fun k => ?_
  obtain ⟨t, ht⟩ := hM k
  set s := Computability.haltTime M (encodeNat k) with hs
  set w := k + s + f k + simB M + 2 with hwdef
  have hw : 2 ≤ w := by omega
  refine ⟨w, hw, ?_⟩
  obtain ⟨st1, T1, g1, e1k, e1s, e1b, e1p, e1o⟩ := start_good (need M) 3 le_rfl hw k (by omega)
  have hkw : k < 2 ^ w := lt_two_pow_of_le (by omega)
  set st2 := st1.set (ρs M (need M) 3 le_rfl .inp) k with hst2
  have g2 : Good (encodeNat k) w (.set (ρs M (need M) 3 le_rfl .inp)
      (.var (ex (need M) 3 ⟨0, by omega⟩)) : CStm (need M + 3) (need M))
      st1 st2 (Ex.nodeCost w + unitCost w) := by
    have e : st2 = st1.set (ρs M (need M) 3 le_rfl .inp)
        ((Ex.var (ex (need M) 3 ⟨0, by omega⟩) : Ex (need M + 3)).eval st1.env) := by
      rw [hst2]; congr 1; simp only [Ex.eval]; exact e1k.symm
    rw [e]
    exact (Good.set (by simp only [Ex.Fits, e1k]; exact hkw)).mono (by simp [Ex.size])
  have hb2 := Good.bdd hw g2 e1b (by omega)
  obtain ⟨T3, g3, -, e3c, -, -, -, e3o⟩ := simNat_slot (x := encodeNat k) le_rfl hw
    (lt_two_pow_of_le (by omega)).le st2 hb2.1 hb2.2 (fun q => by simp [hst2, e1s])
    (by simp [hst2]) hkw ht (lt_two_pow_of_le (by omega))
    (by have := bits_length_le (f k); omega)
  set st3 := exec (encodeNat k) (simNat M (ρs M (need M) 3 le_rfl) (κs M (need M) le_rfl)) st2
    with hst3
  have g4 := Good.emit (x := encodeNat k) (w := w) (st := st3)
    (e := .var (ρs M (need M) 3 le_rfl .clk))
    (by simp only [Ex.Fits]; rw [e3c]; exact lt_two_pow_of_le (by omega))
  refine ⟨_, _, g1.seq (g2.seq (g3.seq (g4.seq Good.skip))), ?_⟩
  simp [Ex.eval, e3c, e3o, hst2, e1o, hs]

/-- **Computable functions have computable running times.** -/
theorem MachineComputable.exists_time {f : ℕ → ℕ} (hf : MachineComputable f) :
    ∃ M : Machine, Deterministic M ∧
      (∀ k, ComputesWithin M (encodeNat k) (encodeNat (f k))
        (Computability.haltTime M (encodeNat k))) ∧
      MachineComputable fun k => Computability.haltTime M (encodeNat k) := by
  obtain ⟨M, hM, hc⟩ := hf
  refine ⟨M, hM, fun k => ?_, machineComputable_haltTime hc⟩
  obtain ⟨t, ht⟩ := hc k
  exact (ComputesWithin.haltTime ht).1

end Lax119563Proofs.Computability
