import Lax119563Proofs.Hierarchy.UnivMain
import Lax119563Proofs.Hierarchy.Padding
import Lax119563Proofs.Hierarchy.Reduction

/-!
# The coarse hierarchy

The diagonal machine runs the universal simulator on its input `y` under a clock of
`|y|^B` steps, `B = 3 b + 3`; the simulator answers the negation of the machine whose code is a
prefix of `y`.  Hence its language is in `DTIME(n^B)` but not in `DTIME(n^b)`.
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime Function

namespace Lax119563Proofs.Hierarchy

open Prog Universal

/-- Stack indices of the clock preparation: scratch stacks after the clock. -/
noncomputable def d3 (k : ℕ) (hk : k < 4 := by omega) : Fin (simMachine.tapes + 1 + 4 + 1) :=
  ⟨simMachine.tapes + 2 + k, by omega⟩

/-- Leave the input in place and put `|y|^B` clock units on the clock stack. -/
noncomputable def clockPrep (B : ℕ) : Prog (simMachine.tapes + 1 + 4 + 1) simMachine.symbols :=
  seq (moveCount 0 (d3 0) (d3 1))
    (seq (moveAll (d3 0) 0) (power (clockIdx simMachine 4) (d3 1) (d3 2) (d3 3) B))

/-- Stacks in the shape used by `clockPrep`. -/
noncomputable def cst (a0 aA aN aK : List (Fin (simMachine.symbols + 2))) :
    Stacks (simMachine.tapes + 1 + 4 + 1) simMachine.symbols := fun i =>
  if i.val = 0 then a0 else if i.val = simMachine.tapes + 2 then aA else
  if i.val = simMachine.tapes + 3 then aN else if i.val = simMachine.tapes + 1 then aK else []

/-- Prove equalities between `cst` stacks and their updates. -/
macro "cst_eq" : tactic =>
  `(tactic| (funext i; simp only [cst, update_apply, Fin.ext_iff, Fin.val_zero, d3, clockIdx]; split_ifs <;> first | omega | rfl | simp_all))

lemma clockPrep_runs (B : ℕ) (hB : 1 ≤ B) (y : List Bool) :
    ∃ s', (clockPrep B).RunsLe (inputStacks _ _ y) s'
        ((2 * simMachine.symbols + 20 + B * (4 * simMachine.symbols + 40)) * (y.length + 1) ^ B
          + 5) ∧
      HandsOver simMachine s' y ∧ (s' (clockIdx simMachine 4)).length = y.length ^ B := by
  have ne : ∀ a b : Fin (simMachine.tapes + 1 + 4 + 1), a.val ≠ b.val → a ≠ b :=
    fun a b h => Fin.ne_of_val_ne h
  set m := simMachine.symbols
  set yb := y.map (bitSym m)
  have hs0 : inputStacks (simMachine.tapes + 1 + 4) m y = cst yb [] [] [] := by
    funext i
    simp only [inputStacks, cst, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> first | omega | rfl
  rw [hs0]
  have h1 : (moveCount 0 (d3 0) (d3 1) : Prog _ m).RunsLe (cst yb [] [] [])
      (cst [] yb.reverse (unary m y.length) []) ((m + 8) * y.length + 1) :=
    (moveCount_runs (ne _ _ (by simp [d3])) (ne _ _ (by simp [d3])) (ne _ _ (by simp [d3])) yb _
      (by simp [cst])).of_eq (by simp only [yb, List.length_map]; cst_eq) (by simp [yb])
  have h2 : (moveAll (d3 0) 0 : Prog _ m).RunsLe (cst [] yb.reverse (unary m y.length) [])
      (cst yb [] (unary m y.length) []) ((m + 6) * y.length + 1) :=
    (moveAll_runs (ne _ _ (by simp [d3])) yb.reverse _ (by simp [cst, d3])).of_eq
      (by simp only [List.reverse_reverse]; cst_eq) (by simp [yb])
  have h3 := power_runs (p := clockIdx simMachine 4) (n := d3 1) (q := d3 2) (h := d3 3)
    (b := y.length) (ne _ _ (by simp [d3, clockIdx])) (ne _ _ (by simp [d3, clockIdx]))
    (ne _ _ (by simp [d3, clockIdx])) (ne _ _ (by simp [d3])) (ne _ _ (by simp [d3]))
    (ne _ _ (by simp [d3])) B (s := cst yb [] (unary m y.length) [])
    (by simp [cst, clockIdx]) (by simp [cst, d3]) (by simp [cst, d3]) (by simp [cst, d3])
  refine ⟨_, (h1.seq (h2.seq h3)).mono ?_, fun i => ⟨fun hi => ?_, fun hi1 hi2 => ?_⟩, ?_⟩
  · have hP : y.length + 1 ≤ (y.length + 1) ^ B := Nat.le_self_pow (by omega) _
    nlinarith
  · simp only [update_apply, Fin.ext_iff, clockIdx, cst]
    split_ifs <;> first | omega | rfl
  · simp only [update_apply, Fin.ext_iff, clockIdx, cst]
    split_ifs <;> first | omega | rfl
  · simp

/-- The language of the diagonal machine for the exponent `b`. -/
noncomputable def diagLang (B : ℕ) : Set (List Bool) :=
  {y | (runOn simMachine y (y.length ^ B)).answer = some true}

/-- The diagonal machine. -/
noncomputable def diagMachine (B : ℕ) : Machine := thenClocked simMachine 4 (clockPrep B)

lemma diagLang_dt (B : ℕ) (hB : 1 ≤ B) : DT (diagLang B) (B : ℝ) := by
  set K₀ := 2 * simMachine.symbols + 20 + B * (4 * simMachine.symbols + 40)
  set K := K₀ + 7
  refine ⟨diagMachine B, thenClocked_deterministic _ _ _, K * 2 ^ B, fun y => ?_⟩
  obtain ⟨s', ⟨t, ht, hr⟩, hH, hK⟩ := clockPrep_runs B hB y
  have hans := thenClocked_answer hr hH hK
  have hdec : Lax119563.DeterministicTime.DecidesExactlyWithin (diagMachine B) y (y ∈ diagLang B)
      (t + y.length ^ B + 1) := by
    refine ⟨_, hans, ?_⟩
    simp only [diagLang, Set.mem_ofPred_eq]
    rcases (runOn simMachine y (y.length ^ B)).answer with _ | _ | _ <;> simp
  refine decidesWithin_mono hdec ?_
  apply Nat.le_floor
  have h1 := succ_pow_le y.length B
  have h2 : y.length ^ B ≤ (y.length + 1) ^ B := Nat.pow_le_pow_left (by omega) B
  have h3 : 1 ≤ (y.length + 1) ^ B := Nat.one_le_pow _ _ (by omega)
  have h4 : t + y.length ^ B + 1 ≤ K * 2 ^ B * y.length ^ B + K * 2 ^ B := by
    calc t + y.length ^ B + 1 ≤ K * (y.length + 1) ^ B := by
          have e : K * (y.length + 1) ^ B = K₀ * (y.length + 1) ^ B + 7 * (y.length + 1) ^ B := by
            simp only [K]; ring
          have ht' : t ≤ K₀ * (y.length + 1) ^ B + 5 := ht
          omega
      _ ≤ K * (2 ^ B * (y.length ^ B + 1)) := Nat.mul_le_mul_left _ h1
      _ = _ := by ring
  beta_reduce
  rw [Real.rpow_natCast]
  exact_mod_cast h4

/-- The running time of the simulator is eventually below `n^{3 b + 3}`. -/
lemma simTime_le (C Tb b : ℕ) : ∃ N0, ∀ n ≥ N0, ∀ T ≤ C * n ^ b + C,
    simTime n Tb T ≤ n ^ (3 * b + 3) := by
  set A := 2 * (C + 1)
  set K₁ := 12 + 2 * A * Tb
  set K₂ := 2003 + 12001 * A * K₁ ^ 2
  refine ⟨K₂ + 1, fun n hn T hT => ?_⟩
  have hn1 : 1 ≤ n := by omega
  set X := n ^ b
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hTA : T ≤ A * X := by
    have e1 : C ≤ C * X := Nat.le_mul_of_pos_right _ hX
    have e2 : A * X = 2 * (C * X) + 2 * X := by simp only [A]; ring
    have e3 : C * n ^ b = C * X := rfl
    omega
  have hnX : 1 ≤ n * X := Nat.mul_le_mul hn1 hX
  have hin : 5 * (n + 1) + (T + 1) * Tb + 1 ≤ K₁ * (n * X) := by
    have e1 : (T + 1) * Tb ≤ (A * X + 1) * Tb := Nat.mul_le_mul_right _ (by omega)
    have e2 : X ≤ n * X := Nat.le_mul_of_pos_left _ (by omega)
    have e3 : n ≤ n * X := Nat.le_mul_of_pos_right _ (by omega)
    have e4 : A * X * Tb ≤ A * Tb * (n * X) := by
      have := Nat.mul_le_mul_left (A * Tb) e2
      calc A * X * Tb = A * Tb * X := by ring
        _ ≤ _ := this
    have hA : 2 ≤ A := by simp only [A]; omega
    have e5 : Tb ≤ A * Tb * (n * X) := by
      calc Tb = 1 * Tb * 1 := by ring
        _ ≤ A * Tb * (n * X) := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) hnX
    have e6 : (A * X + 1) * Tb = A * X * Tb + Tb := by ring
    have e7 : K₁ * (n * X) = 12 * (n * X) + 2 * (A * Tb * (n * X)) := by simp only [K₁]; ring
    omega
  have hsc : stepCost (5 * (n + 1) + (T + 1) * Tb) ≤ 12000 * K₁ ^ 2 * (n * X) ^ 2 := by
    unfold stepCost
    calc 3000 * (5 * (n + 1) + (T + 1) * Tb + 1) ^ 2 ≤ 3000 * (K₁ * (n * X) + 1) ^ 2 := by
          gcongr; omega
      _ ≤ 3000 * (2 * K₁ * (n * X)) ^ 2 := by
          gcongr; have : 1 ≤ K₁ := by simp only [K₁]; omega
          nlinarith
      _ = 12000 * K₁ ^ 2 * (n * X) ^ 2 := by ring
  have hmain : T * (stepCost (5 * (n + 1) + (T + 1) * Tb) + 1) ≤ 12001 * A * K₁ ^ 2 * n ^ 2 * X ^ 3 := by
    have h1 : stepCost (5 * (n + 1) + (T + 1) * Tb) + 1 ≤ 12001 * K₁ ^ 2 * (n * X) ^ 2 := by
      have : 1 ≤ K₁ ^ 2 * (n * X) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      rw [mul_assoc] at hsc ⊢
      omega
    calc T * (stepCost (5 * (n + 1) + (T + 1) * Tb) + 1)
        ≤ (A * X) * (12001 * K₁ ^ 2 * (n * X) ^ 2) := Nat.mul_le_mul hTA h1
      _ = 12001 * A * K₁ ^ 2 * n ^ 2 * X ^ 3 := by ring
  have hpow : n ^ (3 * b + 3) = n * (n ^ 2 * X ^ 3) := by
    simp only [X]; ring
  have hnX3 : 1 ≤ n ^ 2 * X ^ 3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hfin : simTime n Tb T ≤ K₂ * (n ^ 2 * X ^ 3) := by
    simp only [simTime, K₂]
    have e : 1000 * (n + 1) ≤ 2000 * (n ^ 2 * X ^ 3) := by
      have : n ≤ n ^ 2 * X ^ 3 := by
        calc n = n ^ 1 * 1 := by ring
          _ ≤ n ^ 2 * X ^ 3 := Nat.mul_le_mul (Nat.pow_le_pow_right hn1 (by omega))
              (Nat.one_le_pow _ _ hX)
      omega
    have e' : 12001 * A * K₁ ^ 2 * n ^ 2 * X ^ 3 = 12001 * A * K₁ ^ 2 * (n ^ 2 * X ^ 3) := by ring
    nlinarith
  rw [hpow]
  calc simTime n Tb T ≤ K₂ * (n ^ 2 * X ^ 3) := hfin
    _ ≤ n * (n ^ 2 * X ^ 3) := Nat.mul_le_mul_right _ (by omega)

lemma diagLang_not_dt (b : ℕ) : ¬ DT (diagLang (3 * b + 3)) (b : ℝ) := by
  rintro ⟨M, -, C, hC⟩
  obtain ⟨N0, hN0⟩ := simTime_le C (table M).length b
  set y := code M ++ List.replicate N0 false
  have hn : N0 ≤ y.length := by simp [y]
  obtain ⟨β, hβ, hiff⟩ := hC y
  set T := ⌊(C : ℝ) * (fun n : ℕ => (n : ℝ) ^ (b : ℝ)) y.length + C⌋₊
  have hT : T ≤ C * y.length ^ b + C := by
    have e : (C : ℝ) * (y.length : ℝ) ^ (b : ℝ) + C = ((C * y.length ^ b + C : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; push_cast; ring
    simp only [T]
    rw [e, Nat.floor_natCast]
  have hsim := simMachine_answer (z := List.replicate N0 false) hβ
  have hle := hN0 y.length hn T hT
  have hB := drun_answer_mono hsim hle
  have hmem : y ∈ diagLang (3 * b + 3) ↔ (!β) = true := by
    simp only [diagLang, Set.mem_ofPred_eq, runOn_eq_drun] at hB ⊢
    rw [hB]; simp
  cases β <;> simp_all

/-- The coarse hierarchy. -/
theorem coarseHierarchy : CoarseHierarchy := fun b =>
  ⟨3 * b + 3, diagLang (3 * b + 3), diagLang_dt _ (by omega), diagLang_not_dt b⟩

end Lax119563Proofs.Hierarchy
