import Lax119563Proofs.Hierarchy.Coarse

/-!
# The exponential diagonal language

The diagonal machine for exponential time computes a clock of `2^{|y|}` units by doubling a
unary counter `|y|` times (in time `O(2^{|y|})`), and then runs the universal simulator on
its input `y` under this clock; the simulator answers the negation of the machine whose code
is a prefix of `y`.  Hence its language is in `DTIME(2^n)` (`diagExp_dt`).  A machine running
within `C 2^{n/4} + C` steps is simulated in time `O(n^2 2^{3 n / 4})` (the overhead of the
simulator is cubic), which is below `2^n` for long inputs, so the language is not in
`DTIME(2^{n/4})` (`diagExp_not_dt`).
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime Function

namespace Lax119563Proofs.Hierarchy

open Prog Universal

variable {K m : ℕ}

/-! ## Repeated multiplication -/

/-- Multiply the unary number on `p` by the one on `n`, once for every symbol of `c`
(emptying `c`; helpers `q`, `h` empty). -/
def mulLoop (p n q h c : Fin K) : Prog K m :=
  loop (fun r => (r c).isSome) (seq (pop c) (mulBy p n q h))

lemma mulLoop_cost {D a T' k : ℕ} (hD : D = 6 * m + 62)
    (hT' : T' + D * (2 * a) ≤ D * (2 * a * 2 ^ k + k) + 1) :
    1 + (2 * m + 20) * (a + 1) * (2 + 1) + T' + 1 + D * a ≤ D * (a * 2 ^ (k + 1) + (k + 1)) + 1 := by
  subst hD
  have e1 : (6 * m + 62) * (2 * a * 2 ^ k + k) = (6 * m + 62) * (a * 2 ^ (k + 1) + k) := by ring
  have e2 : (6 * m + 62) * (a * 2 ^ (k + 1) + (k + 1)) =
      (6 * m + 62) * (a * 2 ^ (k + 1) + k) + (6 * m + 62) := by ring
  have e3 : (2 * m + 20) * (a + 1) * (2 + 1) + (6 * m + 62) * a + 2 ≤
      (6 * m + 62) * (2 * a) + (6 * m + 62) := by nlinarith
  omega

lemma mulLoop_runs {p n q h c : Fin K} (hpn : p ≠ n) (hpq : p ≠ q) (hph : p ≠ h) (hnq : n ≠ q)
    (hnh : n ≠ h) (hqh : q ≠ h) (hcp : c ≠ p) (hcn : c ≠ n) (hcq : c ≠ q) (hch : c ≠ h) :
    ∀ (k a : ℕ) (s : Stacks K m), s c = unary m k → s p = unary m a → s n = unary m 2 →
      s q = [] → s h = [] →
      ∃ T, (mulLoop p n q h c).RunsLe s (update (update s c []) p (unary m (a * 2 ^ k))) T ∧
        T + (6 * m + 62) * a ≤ (6 * m + 62) * (a * 2 ^ k + k) + 1
  | 0, a, s, hc, _, _, _, _ =>
    ⟨1, (RunsLe.loopF (p := seq (pop c) (mulBy p n q h)) (c := fun r => (r c).isSome) (s := s)
      (by simp [tops, hc])).of_eq (by simp at hc; simp [pow_zero, mul_one]; stacks_eq) le_rfl,
      by simp only [pow_zero, mul_one, add_zero]; omega⟩
  | k + 1, a, s, hc, hp, hn, hq, hh => by
    set s₁ := update (update s c (unary m k)) p (unary m (a * 2)) with hs₁
    have h1 : (seq (pop c) (mulBy p n q h) : Prog K m).RunsLe s s₁
        (1 + (2 * m + 20) * (a + 1) * (2 + 1)) :=
      (RunsLe.pop c s).seq (mulBy_runs (s := update s c (s c).tail) hpn hpq hph hnq hnh hqh
        (by simp [update_of_ne hcp.symm, hp]) (by simp [update_of_ne hcn.symm, hn])
        (by simp [update_of_ne hcq.symm, hq]) (by simp [update_of_ne hch.symm, hh])) |>.of_eq
        (by simp only [hs₁, hc, List.replicate_succ, List.tail_cons]) le_rfl
    obtain ⟨T', h2, hT'⟩ := mulLoop_runs hpn hpq hph hnq hnh hqh hcp hcn hcq hch k (a * 2) s₁
      (by simp [s₁, update_of_ne hcp]) (by simp [s₁])
      (by simp [s₁, update_of_ne hpn.symm, update_of_ne hcn.symm, hn])
      (by simp [s₁, update_of_ne hpq.symm, update_of_ne hcq.symm, hq])
      (by simp [s₁, update_of_ne hph.symm, update_of_ne hch.symm, hh])
    refine ⟨_, (RunsLe.loopT (c := fun r => (r c).isSome) (by simp [tops, hc, List.replicate_succ])
      h1 h2).of_eq ?_ le_rfl, ?_⟩
    · rw [show a * 2 * 2 ^ k = a * 2 ^ (k + 1) by ring, hs₁]
      stacks_eq
    · have := mulLoop_cost (m := m) (a := a) (k := k) (T' := T') rfl
        (by rw [show 2 * a = a * 2 by ring]; exact hT')
      omega

/-! ## The exponential clock -/

/-- Stack indices of the clock preparation: scratch stacks after the clock. -/
noncomputable def e5 (k : ℕ) (hk : k < 5 := by omega) : Fin (simMachine.tapes + 1 + 5 + 1) :=
  ⟨simMachine.tapes + 2 + k, by omega⟩

/-- Leave the input in place and put `2^{|y|}` clock units on the clock stack. -/
noncomputable def expPrep : Prog (simMachine.tapes + 1 + 5 + 1) simMachine.symbols :=
  seq (moveCount 0 (e5 0) (e5 1))
    (seq (moveAll (e5 0) 0)
      (seq (push (e5 2) 0)
        (seq (push (e5 2) 0)
          (seq (push (clockIdx simMachine 5) 0)
            (mulLoop (clockIdx simMachine 5) (e5 2) (e5 3) (e5 4) (e5 1))))))

/-- Stacks in the shape used by `expPrep`. -/
noncomputable def est (a0 aA aN aT aK : List (Fin (simMachine.symbols + 2))) :
    Stacks (simMachine.tapes + 1 + 5 + 1) simMachine.symbols := fun i =>
  if i.val = 0 then a0 else if i.val = simMachine.tapes + 2 then aA else
  if i.val = simMachine.tapes + 3 then aN else if i.val = simMachine.tapes + 4 then aT else
  if i.val = simMachine.tapes + 1 then aK else []

/-- Prove equalities between `est` stacks and their updates. -/
macro "est_eq" : tactic =>
  `(tactic| (funext i; simp only [est, update_apply, Fin.ext_iff, Fin.val_zero, e5, clockIdx]; split_ifs <;> first | omega | rfl | simp_all))

lemma expPrep_cost {m n T : ℕ} (hT : T + (6 * m + 62) * 1 ≤ (6 * m + 62) * (1 * 2 ^ n + n) + 1) :
    (m + 8) * n + 1 + ((m + 6) * n + 1 + (2 + (2 + (2 + T)))) ≤ (14 * m + 145) * 2 ^ n := by
  have hn : n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have e1 : (m + 8) * n + (m + 6) * n ≤ (2 * m + 14) * 2 ^ n := by
    have : (2 * m + 14) * n ≤ (2 * m + 14) * 2 ^ n := Nat.mul_le_mul_left _ hn
    have e : (m + 8) * n + (m + 6) * n = (2 * m + 14) * n := by ring
    omega
  have e2 : (6 * m + 62) * (1 * 2 ^ n + n) ≤ (12 * m + 124) * 2 ^ n := by
    have : (6 * m + 62) * n ≤ (6 * m + 62) * 2 ^ n := Nat.mul_le_mul_left _ hn
    have e : (6 * m + 62) * (1 * 2 ^ n + n) = (6 * m + 62) * 2 ^ n + (6 * m + 62) * n := by ring
    have e' : (12 * m + 124) * 2 ^ n = 2 * ((6 * m + 62) * 2 ^ n) := by ring
    omega
  have e3 : (14 * m + 145) * 2 ^ n = (2 * m + 14) * 2 ^ n + (12 * m + 124) * 2 ^ n +
      7 * 2 ^ n := by ring
  omega

lemma expPrep_runs (y : List Bool) :
    ∃ s', expPrep.RunsLe (inputStacks _ _ y) s' ((14 * simMachine.symbols + 145) * 2 ^ y.length) ∧
      HandsOver simMachine s' y ∧ (s' (clockIdx simMachine 5)).length = 2 ^ y.length := by
  have ne : ∀ a b : Fin (simMachine.tapes + 1 + 5 + 1), a.val ≠ b.val → a ≠ b :=
    fun a b h => Fin.ne_of_val_ne h
  set m := simMachine.symbols
  set yb := y.map (bitSym m)
  have hs0 : inputStacks (simMachine.tapes + 1 + 5) m y = est yb [] [] [] [] := by
    funext i
    simp only [inputStacks, est, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> first | omega | rfl
  rw [hs0]
  have h1 : (moveCount 0 (e5 0) (e5 1) : Prog _ m).RunsLe (est yb [] [] [] [])
      (est [] yb.reverse (unary m y.length) [] []) ((m + 8) * y.length + 1) :=
    (moveCount_runs (ne _ _ (by simp [e5])) (ne _ _ (by simp [e5])) (ne _ _ (by simp [e5])) yb _
      (by simp [est])).of_eq (by simp only [yb, List.length_map]; est_eq) (by simp [yb])
  have h2 : (moveAll (e5 0) 0 : Prog _ m).RunsLe (est [] yb.reverse (unary m y.length) [] [])
      (est yb [] (unary m y.length) [] []) ((m + 6) * y.length + 1) :=
    (moveAll_runs (ne _ _ (by simp [e5])) yb.reverse _ (by simp [est, e5])).of_eq
      (by simp only [List.reverse_reverse]; est_eq) (by simp [yb])
  have h3 : (push (e5 2) 0 : Prog _ m).RunsLe (est yb [] (unary m y.length) [] [])
      (est yb [] (unary m y.length) (unary m 1) []) 2 :=
    (RunsLe.push _ _ _).of_eq (by est_eq) le_rfl
  have h4 : (push (e5 2) 0 : Prog _ m).RunsLe (est yb [] (unary m y.length) (unary m 1) [])
      (est yb [] (unary m y.length) (unary m 2) []) 2 :=
    (RunsLe.push _ _ _).of_eq (by est_eq) le_rfl
  have h5 : (push (clockIdx simMachine 5) 0 : Prog _ m).RunsLe
      (est yb [] (unary m y.length) (unary m 2) [])
      (est yb [] (unary m y.length) (unary m 2) (unary m 1)) 2 :=
    (RunsLe.push _ _ _).of_eq (by est_eq) le_rfl
  obtain ⟨T, h6, hT⟩ := mulLoop_runs (p := clockIdx simMachine 5) (n := e5 2) (q := e5 3)
    (h := e5 4) (c := e5 1)
    (ne _ _ (by simp [e5, clockIdx])) (ne _ _ (by simp [e5, clockIdx]))
    (ne _ _ (by simp [e5, clockIdx])) (ne _ _ (by simp [e5])) (ne _ _ (by simp [e5]))
    (ne _ _ (by simp [e5])) (ne _ _ (by simp [e5, clockIdx])) (ne _ _ (by simp [e5]))
    (ne _ _ (by simp [e5])) (ne _ _ (by simp [e5])) y.length 1
    (est yb [] (unary m y.length) (unary m 2) (unary m 1))
    (by simp [est, e5]) (by simp [est, clockIdx]) (by simp [est, e5]) (by simp [est, e5])
    (by simp [est, e5])
  refine ⟨_, (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))).mono (expPrep_cost hT),
    fun i => ⟨fun hi => ?_, fun hi1 hi2 => ?_⟩, ?_⟩
  · simp only [update_apply, Fin.ext_iff, clockIdx, est, e5]
    split_ifs <;> first | omega | rfl
  · simp only [update_apply, Fin.ext_iff, clockIdx, est, e5]
    split_ifs <;> first | omega | rfl
  · simp

/-! ## The diagonal language -/

/-- The exponential diagonal language. -/
noncomputable def diagExpLang : Set (List Bool) :=
  {y | (runOn simMachine y (2 ^ y.length)).answer = some true}

/-- The exponential diagonal machine. -/
noncomputable def diagExpMachine : Machine := thenClocked simMachine 5 expPrep

theorem diagExp_dt : DecidableInTime diagExpLang (fun n => (2 : ℝ) ^ (n : ℝ)) := by
  set K := 14 * simMachine.symbols + 146
  refine ⟨diagExpMachine, thenClocked_deterministic _ _ _, K, fun y => ?_⟩
  obtain ⟨s', ⟨t, ht, hr⟩, hH, hK⟩ := expPrep_runs y
  have hans := thenClocked_answer hr hH hK
  have hdec : Lax119563.DeterministicTime.DecidesExactlyWithin diagExpMachine y (y ∈ diagExpLang) (t + 2 ^ y.length + 1) := by
    refine ⟨_, hans, ?_⟩
    simp only [diagExpLang, Set.mem_ofPred_eq]
    rcases (runOn simMachine y (2 ^ y.length)).answer with _ | _ | _ <;> simp
  refine decidesWithin_mono hdec ?_
  apply Nat.le_floor
  have h4 : t + 2 ^ y.length + 1 ≤ K * 2 ^ y.length + K := by
    have e : K * 2 ^ y.length = (14 * simMachine.symbols + 145) * 2 ^ y.length + 2 ^ y.length := by
      simp only [K]; ring
    have : 1 ≤ K := by simp only [K]; omega
    omega
  beta_reduce
  rw [Real.rpow_natCast]
  exact_mod_cast h4

/-! ## Simulating machines running in time `O(2^{n/4})` -/

/-- The running time of the simulator is cubic in the simulated time. -/
lemma simTime_le_cubic (C Tb : ℕ) : ∃ K₂, ∀ n X T, 1 ≤ n → 1 ≤ X → T ≤ C * X + C →
    simTime n Tb T ≤ K₂ * (n ^ 2 * X ^ 3) := by
  set A := 2 * (C + 1)
  set K₁ := 12 + 2 * A * Tb
  set K₂ := 2003 + 12001 * A * K₁ ^ 2
  refine ⟨K₂, fun n X T hn1 hX hT => ?_⟩
  have hTA : T ≤ A * X := by
    have e1 : C ≤ C * X := Nat.le_mul_of_pos_right _ hX
    have e2 : A * X = 2 * (C * X) + 2 * X := by simp only [A]; ring
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
  have hmain : T * (stepCost (5 * (n + 1) + (T + 1) * Tb) + 1) ≤
      12001 * A * K₁ ^ 2 * n ^ 2 * X ^ 3 := by
    have h1 : stepCost (5 * (n + 1) + (T + 1) * Tb) + 1 ≤ 12001 * K₁ ^ 2 * (n * X) ^ 2 := by
      have : 1 ≤ K₁ ^ 2 * (n * X) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      rw [mul_assoc] at hsc ⊢
      omega
    calc T * (stepCost (5 * (n + 1) + (T + 1) * Tb) + 1)
        ≤ (A * X) * (12001 * K₁ ^ 2 * (n * X) ^ 2) := Nat.mul_le_mul hTA h1
      _ = 12001 * A * K₁ ^ 2 * n ^ 2 * X ^ 3 := by ring
  simp only [simTime, K₂]
  have e : 1000 * (n + 1) ≤ 2000 * (n ^ 2 * X ^ 3) := by
    have : n ≤ n ^ 2 * X ^ 3 := by
      calc n = n ^ 1 * 1 := by ring
        _ ≤ n ^ 2 * X ^ 3 := Nat.mul_le_mul (Nat.pow_le_pow_right hn1 (by omega))
            (Nat.one_le_pow _ _ hX)
    omega
  have hnX3 : 1 ≤ n ^ 2 * X ^ 3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have e' : 12001 * A * K₁ ^ 2 * n ^ 2 * X ^ 3 = 12001 * A * K₁ ^ 2 * (n ^ 2 * X ^ 3) := by ring
  have e'' : (2003 + 12001 * A * K₁ ^ 2) * (n ^ 2 * X ^ 3) =
      2003 * (n ^ 2 * X ^ 3) + 12001 * A * K₁ ^ 2 * (n ^ 2 * X ^ 3) := by ring
  omega

/-- `n^2 2^{3 n / 4}` is eventually dominated by `2^n`. -/
lemma exp_dom (K n : ℕ) (hn : 16384 * K ≤ n) : K * (n ^ 2 * (2 ^ (n / 4 + 1)) ^ 3) ≤ 2 ^ n := by
  set k := n / 4 with hk
  set j := n / 16 with hj
  have hjk : j = k / 4 := by rw [hj, hk, Nat.div_div_eq_div_mul]
  have h4k : 4 * k ≤ n := by omega
  have h4j : 4 * j ≤ k := by omega
  have hnj : n ≤ 16 * 2 ^ j := by
    have h1 : n < 16 * (j + 1) := by omega
    have h2 : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    omega
  have hn2 : n ^ 2 ≤ 256 * 2 ^ (2 * j) := by
    calc n ^ 2 ≤ (16 * 2 ^ j) ^ 2 := Nat.pow_le_pow_left hnj 2
      _ = 256 * 2 ^ (2 * j) := by rw [mul_pow, ← pow_mul, mul_comm j 2]; norm_num
  have hK : 2048 * K ≤ 2 ^ (2 * j) := by
    have h1 : 2048 * K ≤ 2 * j := by omega
    have h2 : 2 * j < 2 ^ (2 * j) := Nat.lt_two_pow_self
    omega
  have hX : (2 ^ (k + 1)) ^ 3 = 8 * 2 ^ (3 * k) := by
    rw [← pow_mul, show (k + 1) * 3 = 3 * k + 3 by ring, pow_add]; norm_num; ring
  rw [hX]
  calc K * (n ^ 2 * (8 * 2 ^ (3 * k))) ≤ K * (256 * 2 ^ (2 * j) * (8 * 2 ^ (3 * k))) := by gcongr
    _ = (2048 * K) * (2 ^ (2 * j) * 2 ^ (3 * k)) := by ring
    _ ≤ 2 ^ (2 * j) * (2 ^ (2 * j) * 2 ^ (3 * k)) := Nat.mul_le_mul_right _ hK
    _ = 2 ^ (4 * j + 3 * k) := by rw [← pow_add, ← pow_add]; ring_nf
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma two_rpow_quarter_le_pow (n : ℕ) : (2 : ℝ) ^ ((n : ℝ) / 4) ≤ (2 ^ (n / 4 + 1) : ℕ) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h : n ≤ 4 * (n / 4 + 1) := by omega
  have h' : (n : ℝ) ≤ 4 * ((n / 4 + 1 : ℕ) : ℝ) := by exact_mod_cast h
  linarith

theorem diagExp_not_dt :
    ¬ DecidableInTime diagExpLang (fun n => (2 : ℝ) ^ ((n : ℝ) / 4)) := by
  rintro ⟨M, -, C, hC⟩
  obtain ⟨K, hK⟩ := simTime_le_cubic C (table M).length
  set y := code M ++ List.replicate (16384 * K + 1) false
  have hn : 16384 * K + 1 ≤ y.length := by simp [y]
  obtain ⟨β, hβ, hiff⟩ := hC y
  set T := ⌊(C : ℝ) * (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) / 4)) y.length + C⌋₊
  have hT : T ≤ C * 2 ^ (y.length / 4 + 1) + C := by
    apply Nat.floor_le_of_le
    have := two_rpow_quarter_le_pow y.length
    have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
    push_cast at this ⊢
    nlinarith
  have hsim := simMachine_answer (z := List.replicate (16384 * K + 1) false) hβ
  have hle : simTime y.length (table M).length T ≤ 2 ^ y.length :=
    (hK y.length _ T (by omega) Nat.one_le_two_pow hT).trans (exp_dom K y.length (by omega))
  have hB := drun_answer_mono hsim hle
  have hmem : y ∈ diagExpLang ↔ (!β) = true := by
    simp only [diagExpLang, Set.mem_ofPred_eq, runOn_eq_drun] at hB ⊢
    rw [hB]; simp
  cases β <;> simp_all

end Lax119563Proofs.Hierarchy
