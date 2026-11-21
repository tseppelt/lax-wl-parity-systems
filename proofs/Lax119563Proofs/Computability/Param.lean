import Lax119563Proofs.Computability.Closure

/-!
# Computing a parameter and a computable function of it inside a statement

For the reductions of parameterized complexity: from the input `x`, compute the parameter
`κ x` (with a machine computing `encodeNat (κ x)` from `x`, e.g. the machine of
`IsParameterized`), then `f (κ x)` for a computable `f` together with the running time of
the machine for `f` on `κ x`.

* `paramS Mκ Mf C E …`: the statement, in the layout with registers `Fin (C + E)` and stacks
  `Fin C`; afterwards the extra registers `0, 1, 2` hold `κ x`, `f (κ x)` and the halting
  time of `Mf` on `encodeNat (κ x)`, all stacks are empty, and the other extra registers
  are kept (`paramS_good`). Further statements can be appended in the same layout.
* The cost is `simInCost Mκ w |x| (haltTime Mκ x) + simNatCost Mf w |encodeNat (κ x)|
  (haltTime Mf (encodeNat (κ x))) + 9 · nodeCost w`, where the two simulator costs are at most
  `simK M · (input length + halting time + 1) · nodeCost w` (`simNatCost_le`, `simInCost_le`).
* `haltTime_le_of_computesWithin`: halting times are bounded by any time bound, e.g. by
  `C (|x| + 1)^d` for the machine of `IsParameterized`; for a computable `f`, the halting time
  of a machine computing `f` is itself computable (`machineComputable_haltTime`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime Lax119563.ParameterizedComplexity
open Lax489179.TuringMachine (Machine Config Instruction Move Deterministic)

namespace Lax119563Proofs.Computability

open CStm

variable {x : List Bool} {w : ℕ}

/-! ## Simplified costs -/

/-- A constant for the cost of simulating `M`. -/
noncomputable def simK (M : Machine) : ℕ :=
  (keys M).length * (8 * (M.tapes + 1) + 12) + 10 * (M.tapes + 1) + 24 *
    (allSk (M.tapes + 1)).length + 250

lemma tailCost_le (M : Machine) (w a s : ℕ) :
    tailCost M w a s + 60 * (a + s + 1) * Ex.nodeCost w ≤ simK M * (a + s + 1) * Ex.nodeCost w := by
  have hU := Ex.unitCost_le_nodeCost w
  unfold tailCost coreCost bodyCost extractCost simK
  generalize (keys M).length * (8 * (M.tapes + 1) + 12) = K1 at *
  generalize (allSk (M.tapes + 1)).length = L at *
  generalize M.tapes + 1 = n at *
  generalize Ex.nodeCost w = N at *
  generalize unitCost w = U at *
  nlinarith [Nat.zero_le (K1 * N * a), Nat.zero_le (n * N * a), Nat.zero_le (L * N * a),
    Nat.zero_le (L * N), Nat.zero_le (N * a), Nat.zero_le (N * s)]

lemma simNatCost_le (M : Machine) (w a s : ℕ) :
    simNatCost M w a s ≤ simK M * (a + s + 1) * Ex.nodeCost w := by
  have := tailCost_le M w a s
  have h : loadNatCost w a ≤ 60 * (a + s + 1) * Ex.nodeCost w := by
    simp only [loadNatCost]; nlinarith
  simp only [simNatCost]; omega

lemma simInCost_le (M : Machine) (w a s : ℕ) :
    simInCost M w a s ≤ simK M * (a + s + 1) * Ex.nodeCost w := by
  have := tailCost_le M w a s
  have h : loadInCost w a ≤ 60 * (a + s + 1) * Ex.nodeCost w := by
    simp only [loadInCost]; nlinarith
  simp only [simInCost]; omega

/-- Halting times are bounded by any time bound. -/
lemma haltTime_le_of_computesWithin {M : Machine} {u y : List Bool} {t : ℕ}
    (h : ComputesWithin M u y t) : haltTime M u ≤ t := (ComputesWithin.haltTime h).2

/-! ## The simulator on the input, in a layout -/

/-- The simulator on the input, in a layout, from a state with all stacks empty. -/
theorem simIn_slot {M : Machine} {C E : ℕ} (h : need M ≤ C) (hw : 2 ≤ w) (hB : simB M ≤ 2 ^ w)
    (st : NSt (C + E) C) (hb : st.Bdd w) (hp : st.pos ≤ x.length) (hemp : ∀ q, st.stk q = [])
    {v t : ℕ} (hM : ComputesWithin M x (encodeNat v) t)
    (hs : haltTime M x < 2 ^ w) (hv : v.bits.length < w) :
    Good x w (simIn M (ρs M C E h) (κs M C h)) st (exec x (simIn M (ρs M C E h) (κs M C h)) st)
        (simInCost M w x.length (haltTime M x)) ∧
      (exec x (simIn M (ρs M C E h) (κs M C h)) st).env (ρs M C E h .out) = v ∧
      (∀ q, (exec x (simIn M (ρs M C E h) (κs M C h)) st).stk q = []) ∧
      (∀ i, (exec x (simIn M (ρs M C E h) (κs M C h)) st).env (ex C E i) = st.env (ex C E i)) ∧
      (exec x (simIn M (ρs M C E h) (κs M C h)) st).pos = x.length ∧
      (exec x (simIn M (ρs M C E h) (κs M C h)) st).out = st.out := by
  obtain ⟨g, e1, -, e3, e4, e5, e6, e7⟩ := simIn_good (ρs M C E h) (κs M C h) hw hB st hb hp
    (fun g => hemp _) hM hs hv
  refine ⟨g, e1, fun q => ?_, fun i => e4 _ fun g => ρs_ne_ex M h g i, e6, e7⟩
  by_cases hq : ∃ g, κs M C h g = q
  · obtain ⟨g, rfl⟩ := hq; exact e3 g
  · push Not at hq; rw [e5 q hq, hemp]

/-- The cost of a call. -/
theorem call_cost {M : Machine} {C E : ℕ} (h : need M ≤ C) (hw : 2 ≤ w) (hB : simB M ≤ 2 ^ w)
    (st : NSt (C + E) C) (hb : st.Bdd w) (hp : st.pos ≤ x.length) (hemp : ∀ q, st.stk q = [])
    (src : Fin (C + E)) {k v t : ℕ} (hk : st.env src = k) (hkw : k < 2 ^ w)
    (hM : ComputesWithin M (encodeNat k) (encodeNat v) t)
    (hs : haltTime M (encodeNat k) < 2 ^ w) (hv : v.bits.length < w) :
    Good x w (callS M C E h src) st (exec x (callS M C E h src) st)
      (Ex.nodeCost w + unitCost w + simNatCost M w (encodeNat k).length
        (haltTime M (encodeNat k))) := by
  set st1 := st.set (ρs M C E h .inp) k with hst1
  have g1 : Good x w (.set (ρs M C E h .inp) (.var src) : CStm (C + E) C) st st1
      (Ex.nodeCost w + unitCost w) := by
    have e : st1 = st.set (ρs M C E h .inp) ((Ex.var src : Ex (C + E)).eval st.env) := by
      rw [hst1]; congr 1; simp only [Ex.eval]; exact hk.symm
    rw [e]; exact (CStm.Good.set (by simp only [Ex.Fits, hk]; exact hkw)).mono (by simp [Ex.size])
  have hb1 := CStm.Good.bdd hw g1 hb hp
  have g2 := (simNat_good (ρs M C E h) (κs M C h) hw hB st1 hb1.1 hb1.2
    (fun g => by simp [hst1, hemp]) (by simp [hst1]) hkw hM hs hv).1
  have g := g1.seq g2
  have e : exec x (callS M C E h src) st = _ := g.2.1
  rw [e]; exact g

/-! ## The parameter and a function of it -/

/-- Compute `κ x` (machine `Mκ`) into the extra register `0`, then `f (κ x)` (machine `Mf`)
into the extra register `1` and the halting time of `Mf` into the extra register `2`. -/
noncomputable def paramS (Mκ Mf : Machine) (C E : ℕ) (hκ : need Mκ ≤ C) (hf : need Mf ≤ C)
    (hE : 3 ≤ E) : CStm (C + E) C :=
  seqL [simIn Mκ (ρs Mκ C E hκ) (κs Mκ C hκ),
    .set (ex C E ⟨0, by omega⟩) (.var (ρs Mκ C E hκ .out)),
    callS Mf C E hf (ex C E ⟨0, by omega⟩),
    .set (ex C E ⟨1, by omega⟩) (.var (ρs Mf C E hf .out)),
    .set (ex C E ⟨2, by omega⟩) (.var (ρs Mf C E hf .clk))]

/-- **Computing the parameter and a computable function of it.** -/
theorem paramS_good {Mκ Mf : Machine} {C E : ℕ} (hκ : need Mκ ≤ C) (hf : need Mf ≤ C)
    (hE : 3 ≤ E) (hw : 2 ≤ w) (hBκ : simB Mκ ≤ 2 ^ w) (hBf : simB Mf ≤ 2 ^ w)
    (st : NSt (C + E) C) (hb : st.Bdd w) (hp : st.pos ≤ x.length) (hemp : ∀ q, st.stk q = [])
    {k v tκ tf : ℕ} (hMκ : ComputesWithin Mκ x (encodeNat k) tκ)
    (hMf : ComputesWithin Mf (encodeNat k) (encodeNat v) tf)
    (hsκ : haltTime Mκ x < 2 ^ w) (hk : k.bits.length < w) (hkw : k < 2 ^ w)
    (hsf : haltTime Mf (encodeNat k) < 2 ^ w) (hv : v.bits.length < w) (hvw : v < 2 ^ w) :
    ∃ st', Good x w (paramS Mκ Mf C E hκ hf hE) st st'
        (simInCost Mκ w x.length (haltTime Mκ x) +
          simNatCost Mf w (encodeNat k).length (haltTime Mf (encodeNat k)) +
          9 * Ex.nodeCost w) ∧
      st'.env (ex C E ⟨0, by omega⟩) = k ∧ st'.env (ex C E ⟨1, by omega⟩) = v ∧
      st'.env (ex C E ⟨2, by omega⟩) = haltTime Mf (encodeNat k) ∧
      (∀ i : Fin E, 3 ≤ i.val → st'.env (ex C E i) = st.env (ex C E i)) ∧
      (∀ q, st'.stk q = []) ∧ st'.Bdd w ∧ st'.pos = x.length ∧ st'.out = st.out := by
  have hU := Ex.unitCost_le_nodeCost w
  obtain ⟨g1, e1o, e1s, e1x, e1p, e1out⟩ := simIn_slot (x := x) hκ hw hBκ st hb hp hemp hMκ hsκ hk
  set st1 := exec x (simIn Mκ (ρs Mκ C E hκ) (κs Mκ C hκ)) st with hst1
  set st2 := st1.set (ex C E ⟨0, by omega⟩) k with hst2
  have g2 : Good x w (.set (ex C E ⟨0, by omega⟩) (.var (ρs Mκ C E hκ .out)) : CStm (C + E) C)
      st1 st2 (Ex.nodeCost w + unitCost w) :=
    (CStm.Good.set (by simp only [Ex.Fits, e1o]; exact hkw)).of_eq (by simp [hst2, Ex.eval, e1o])
      (by simp [Ex.size])
  have hb2 := CStm.Good.bdd hw (g1.seq g2) hb hp
  obtain ⟨st3, T3, g3, e3o, e3c, e3s, e3x, e3b, e3p, e3out⟩ := call_good (x := x) hf hw hBf st2
    hb2.1 hb2.2 (fun q => by simp [hst2, e1s]) (ex C E ⟨0, by omega⟩) (by simp [hst2]) hkw hMf
    hsf hv
  set st4 := st3.set (ex C E ⟨1, by omega⟩) v with hst4
  have g4 : Good x w (.set (ex C E ⟨1, by omega⟩) (.var (ρs Mf C E hf .out)) : CStm (C + E) C)
      st3 st4 (Ex.nodeCost w + unitCost w) :=
    (CStm.Good.set (by simp only [Ex.Fits, e3o]; exact hvw)).of_eq (by simp [hst4, Ex.eval, e3o])
      (by simp [Ex.size])
  have e4c : st4.env (ρs Mf C E hf .clk) = haltTime Mf (encodeNat k) := by
    rw [hst4, NSt.set_env, Function.update_of_ne (ρs_ne_ex Mf hf _ _), e3c]
  set st5 := st4.set (ex C E ⟨2, by omega⟩) (haltTime Mf (encodeNat k)) with hst5
  have g5 : Good x w (.set (ex C E ⟨2, by omega⟩) (.var (ρs Mf C E hf .clk)) : CStm (C + E) C)
      st4 st5 (Ex.nodeCost w + unitCost w) :=
    (CStm.Good.set (by simp only [Ex.Fits, e4c]; exact hsf)).of_eq (by simp [hst5, Ex.eval, e4c])
      (by simp [Ex.size])
  have g3' : Good x w (callS Mf C E hf (ex C E ⟨0, by omega⟩)) st2 st3
      (Ex.nodeCost w + unitCost w + simNatCost Mf w (encodeNat k).length
        (haltTime Mf (encodeNat k))) := by
    have := call_cost (x := x) hf hw hBf st2 hb2.1 hb2.2 (fun q => by simp [hst2, e1s])
      (ex C E ⟨0, by omega⟩) (by simp [hst2]) hkw hMf hsf hv
    rwa [g3.2.1] at this
  have g : Good x w (paramS Mκ Mf C E hκ hf hE) st st5 _ :=
    g1.seq (g2.seq (g3'.seq (g4.seq (g5.seq CStm.Good.skip))))
  have hbd := CStm.Good.bdd hw g hb hp
  refine ⟨st5, g.mono (by omega), ?_, ?_, by simp [hst5], fun i hi => ?_, fun q => by
    simp [hst5, hst4, e3s], hbd.1, by simp [hst5, hst4, e3p, hst2, e1p], by
    simp [hst5, hst4, e3out, hst2, e1out]⟩
  · rw [hst5, NSt.set_env, Function.update_of_ne (ex_ne_ex (by simp)), hst4, NSt.set_env,
      Function.update_of_ne (ex_ne_ex (by simp)), e3x, hst2]; simp
  · rw [hst5, NSt.set_env, Function.update_of_ne (ex_ne_ex (by simp)), hst4]; simp
  · have h0 : i ≠ ⟨0, by omega⟩ := fun h => by rw [h] at hi; simp at hi
    have h1 : i ≠ ⟨1, by omega⟩ := fun h => by rw [h] at hi; simp at hi
    have h2 : i ≠ ⟨2, by omega⟩ := fun h => by rw [h] at hi; simp at hi
    rw [hst5, NSt.set_env, Function.update_of_ne (ex_ne_ex h2), hst4, NSt.set_env,
      Function.update_of_ne (ex_ne_ex h1), e3x, hst2, NSt.set_env,
      Function.update_of_ne (ex_ne_ex h0), e1x]

end Lax119563Proofs.Computability
