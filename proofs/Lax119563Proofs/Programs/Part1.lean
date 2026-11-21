import Lax119563.DeterministicTime
import Lax119563.ImplicitParitySystems
import Lax119563.MatrixCompiler
import Lax119563.ParitySystems
import Lax119563.Stabilization
import Lax119563.WeisfeilerLeman
import Lax119563Proofs.Hierarchy.Part1
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! ### Formerly `Lax119563Proofs.Hierarchy.ExpDiag` -/

section Hierarchy_ExpDiag

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

end Hierarchy_ExpDiag

/-! ### Formerly `Lax119563Proofs.Programs.Propagation` -/

section Programs_Propagation

/-!
# Unit propagation: single steps and invariants

Elementary facts about the rounds `K_r` of unit propagation in a parity system: monotonicity,
single inference steps through binary and ternary equations, and the invariant argument: if a
partial assignment contains the initial facts and is closed under the inference rule of every
equation, then it contains every derived fact, so no conflict ever occurs.
-/

open Lax119563.ParitySystems

namespace Lax119563Proofs.Programs

namespace ParitySystem

variable {V : Type*} [DecidableEq V] (P : ParitySystem V)

theorem known_succ_subset (r : ℕ) : P.known r ⊆ P.known (r + 1) :=
  Set.subset_union_left

theorem known_mono {r r' : ℕ} (h : r ≤ r') : P.known r ⊆ P.known r' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (known_succ_subset P _)

/-- A binary equation `X + Y = 0` transmits the value of `X` to `Y` in one round. -/
theorem known_pair {X Y : V} (hXY : X ≠ Y) (hh : ({X, Y} : Finset V) ∈ P.equations)
    {b : ZMod 2} {r : ℕ} (hX : (X, b) ∈ P.known r) : (Y, b) ∈ P.known (r + 1) := by
  right
  refine ⟨{X, Y}, hh, by simp, fun _ => b, ?_, ?_⟩
  · intro Z hZ hZY
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl
    · exact hX
    · exact absurd rfl hZY
  · simp [Finset.erase_insert_of_ne hXY]

/-- A ternary equation `X + Y + Z = 0` infers `Z` from `X` and `Y` in one round. -/
theorem known_triple {X Y Z : V} (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z)
    (hh : ({X, Y, Z} : Finset V) ∈ P.equations) {b c : ZMod 2} {r : ℕ}
    (hX : (X, b) ∈ P.known r) (hY : (Y, c) ∈ P.known r) : (Z, b + c) ∈ P.known (r + 1) := by
  right
  refine ⟨{X, Y, Z}, hh, by simp, fun W => if W = X then b else c, ?_, ?_⟩
  · intro W hW hWZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl | rfl
    · simpa using hX
    · simpa [hXY.symm] using hY
    · exact absurd rfl hWZ
  · rw [Finset.erase_insert_of_ne hXZ, Finset.erase_insert_of_ne hYZ, Finset.erase_singleton,
      Finset.sum_insert (by simpa using hXY)]
    simp [hXY.symm]

/-- The partial assignment `val` is closed under the inference rule of the equation `h`. -/
def Closed (val : V → Option (ZMod 2)) (h : Finset V) : Prop :=
  ∀ X ∈ h, ∀ b : V → ZMod 2, (∀ Y ∈ h, Y ≠ X → val Y = some (b Y)) →
    val X = some (∑ Y ∈ h.erase X, b Y)

theorem closed_pair {val : V → Option (ZMod 2)} {X Y : V} (hXY : X ≠ Y) (hv : val X = val Y) :
    Closed val {X, Y} := by
  intro W hW b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hW
  rcases hW with rfl | rfl
  · rw [Finset.erase_insert (by simpa using hXY), Finset.sum_singleton, hv]
    exact hb Y (by simp) hXY.symm
  · rw [Finset.erase_insert_of_ne hXY, Finset.erase_singleton, Finset.insert_empty,
      Finset.sum_singleton, ← hv]
    exact hb X (by simp) hXY

theorem closed_triple {val : V → Option (ZMod 2)} {X Y Z : V} (hXY : X ≠ Y) (hXZ : X ≠ Z)
    (hYZ : Y ≠ Z)
    (hX : ∀ b c, val Y = some b → val Z = some c → val X = some (b + c))
    (hY : ∀ b c, val X = some b → val Z = some c → val Y = some (b + c))
    (hZ : ∀ b c, val X = some b → val Y = some c → val Z = some (b + c)) :
    Closed val {X, Y, Z} := by
  intro W hW b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hW
  rcases hW with rfl | rfl | rfl
  · have : ({W, Y, Z} : Finset V).erase W = {Y, Z} :=
      Finset.erase_insert (by simp [hXY, hXZ])
    rw [this, Finset.sum_pair hYZ]
    exact hX _ _ (hb Y (by simp) hXY.symm) (hb Z (by simp) hXZ.symm)
  · rw [Finset.erase_insert_of_ne hXY, Finset.erase_insert (by simpa using hYZ),
      Finset.sum_pair hXZ]
    exact hY _ _ (hb X (by simp) hXY) (hb Z (by simp) hYZ.symm)
  · rw [Finset.erase_insert_of_ne hXZ, Finset.erase_insert_of_ne hYZ, Finset.erase_singleton,
      Finset.insert_empty, Finset.sum_pair hXY]
    exact hZ _ _ (hb X (by simp) hXZ) (hb Y (by simp) hYZ)

/-- If the partial assignment `val` contains the initial facts and is closed under every
equation, then it contains every fact derived by unit propagation. -/
theorem known_subset_of_closed (val : V → Option (ZMod 2))
    (hinit : ∀ f ∈ P.initial, val f.1 = some f.2)
    (hcl : ∀ h ∈ P.equations, Closed val h) : ∀ r, ∀ f ∈ P.known r, val f.1 = some f.2 := by
  intro r
  induction r with
  | zero => exact hinit
  | succ r ih =>
    rintro f (hf | ⟨h, hh, hfh, b, hb, hfb⟩)
    · exact ih f hf
    · rw [hfb]
      exact hcl h hh f.1 hfh b fun Y hY hYf => ih (Y, b Y) (hb Y hY hYf)

theorem not_hasConflict_of_closed (val : V → Option (ZMod 2))
    (hinit : ∀ f ∈ P.initial, val f.1 = some f.2)
    (hcl : ∀ h ∈ P.equations, Closed val h) (r : ℕ) : ¬ P.HasConflict r := by
  rintro ⟨X, h0, h1⟩
  have e0 := known_subset_of_closed P val hinit hcl r _ h0
  have e1 := known_subset_of_closed P val hinit hcl r _ h1
  rw [e0] at e1
  exact absurd (Option.some.inj e1) (by decide : (0 : ZMod 2) ≠ 1)

theorem conflictRound_lt_top_iff : P.conflictRound < ⊤ ↔ ∃ r, P.HasConflict r := by
  simp only [ParitySystem.conflictRound, iInf_lt_iff]
  constructor
  · rintro ⟨r, hr, -⟩
    exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, hr, ENat.natCast_lt_top r⟩

end ParitySystem

end Lax119563Proofs.Programs

end Programs_Propagation

/-! ### Formerly `Lax119563Proofs.Programs.RegisterProgram` -/

section Programs_RegisterProgram

/-!
# Register programs

A register program has `s` registers over `A = 𝔽₂^ℓ`, a finite set of control locations
`{0, …, numLocations - 1}` containing distinct locations `accept` and `reject`, and a list of
guarded commands, each attached to a location:

* `when at p and ⋀ᵢ aᵢ ∈ Dᵢ: a ← T(a); goto q`, where `T(a)ᵢ = a_{σ(i)} + δᵢ` for a
  permutation `σ` of the registers and offsets `δ ∈ A^s`;
* `when at p and ⋀ᵢ aᵢ ∈ Dᵢ: fork q and r`.

A configuration `(p, a)` accepts if `p = accept`, or if `p ∉ {accept, reject}` and some command
at `p` whose guard holds for `a` leads to acceptance: an assignment if `(q, T(a))` accepts, a
fork if both `(q, a)` and `(r, a)` accept. Acceptance is the least such predicate, i.e. the
existence of a finite derivation tree. Commands attached to `accept` or `reject` are never
executed.
-/

namespace Lax119563Proofs.Programs

/-- A guard `⋀ᵢ aᵢ ∈ Dᵢ` on `s` registers over `𝔽₂^ℓ`. -/
structure Guard (s ℓ : ℕ) where
  /-- The sets `Dᵢ`. -/
  sets : Fin s → Finset (Fin ℓ → ZMod 2)

/-- The guard holds for the register valuation `a`. -/
def Guard.Holds {s ℓ : ℕ} (g : Guard s ℓ) (a : Fin s → Fin ℓ → ZMod 2) : Prop :=
  ∀ i, a i ∈ g.sets i

/-- A register update `T(a)ᵢ = a_{σ(i)} + δᵢ`. -/
structure Update (s ℓ : ℕ) where
  /-- The permutation `σ` of the registers. -/
  σ : Equiv.Perm (Fin s)
  /-- The offsets `δ`. -/
  δ : Fin s → Fin ℓ → ZMod 2

/-- Apply the update `T` to the valuation `a`. -/
def Update.apply {s ℓ : ℕ} (T : Update s ℓ) (a : Fin s → Fin ℓ → ZMod 2) :
    Fin s → Fin ℓ → ZMod 2 :=
  fun i => a (T.σ i) + T.δ i

/-- A guarded command of a register program with `n` control locations. -/
inductive Command (s ℓ n : ℕ)
  /-- `when at loc and guard: a ← update(a); goto next`. -/
  | assign (loc : Fin n) (guard : Guard s ℓ) (update : Update s ℓ) (next : Fin n)
  /-- `when at loc and guard: fork left and right`. -/
  | fork (loc : Fin n) (guard : Guard s ℓ) (left right : Fin n)

/-- A register program with `s` registers over `𝔽₂^ℓ`. -/
structure RegisterProgram (s ℓ : ℕ) where
  /-- The number of control locations; the locations are `0, …, numLocations - 1`. -/
  numLocations : ℕ
  /-- The accepting location. -/
  accept : Fin numLocations
  /-- The rejecting location. -/
  reject : Fin numLocations
  accept_ne_reject : accept ≠ reject
  /-- The guarded commands. -/
  commands : List (Command s ℓ numLocations)

namespace RegisterProgram

variable {s ℓ : ℕ}

/-- The configuration `(p, a)` accepts: the least predicate that holds at `accept` and is
closed under executing a command at a location other than `accept` and `reject`. -/
inductive Accepts (R : RegisterProgram s ℓ) :
    Fin R.numLocations → (Fin s → Fin ℓ → ZMod 2) → Prop
  | accept (a : Fin s → Fin ℓ → ZMod 2) : Accepts R R.accept a
  | assign {p q : Fin R.numLocations} {g : Guard s ℓ} {T : Update s ℓ}
      {a : Fin s → Fin ℓ → ZMod 2} :
      Command.assign p g T q ∈ R.commands → p ≠ R.accept → p ≠ R.reject → g.Holds a →
      Accepts R q (T.apply a) → Accepts R p a
  | fork {p q r : Fin R.numLocations} {g : Guard s ℓ} {a : Fin s → Fin ℓ → ZMod 2} :
      Command.fork p g q r ∈ R.commands → p ≠ R.accept → p ≠ R.reject → g.Holds a →
      Accepts R q a → Accepts R r a → Accepts R p a

end RegisterProgram

end Lax119563Proofs.Programs

end Programs_RegisterProgram

/-! ### Formerly `Lax119563Proofs.Programs.Encoding` -/

section Programs_Encoding

/-!
# Encoding register valuations as addresses

A valuation `a ∈ A^s` of `s` registers over `A = 𝔽₂^ℓ` is encoded as the checksum address
`E(a) = (a_1, …, a_s, ∑ᵢ aᵢ)` with `k = s + 1` blocks. A register update
`T(a)ᵢ = a_{σ(i)} + δᵢ` becomes a block-induced permutation `π_T` with `π_T E(a) = E(T(a))`,
and a guard `⋀ᵢ aᵢ ∈ Dᵢ` becomes the coordinate domain `⋃ᵢ {i} × Dᵢ ∪ {k} × A`, whose
allowed addresses are exactly the encodings of the valuations satisfying the guard.
-/

open Lax119563.ImplicitParitySystems

namespace Lax119563Proofs.Programs

variable {s ℓ : ℕ}

/-- The checksum address `E(a) = (a_1, …, a_s, ∑ᵢ aᵢ)`. -/
def encode (a : Fin s → BlockCoord ℓ) : Fin (s + 1) → BlockCoord ℓ :=
  Fin.lastCases (∑ i, a i) a

/-- The register valuation read off the first `s` blocks of an array. -/
def decode (x : Fin (s + 1) → BlockCoord ℓ) : Fin s → BlockCoord ℓ :=
  fun i => x i.castSucc

@[simp] theorem encode_last (a : Fin s → BlockCoord ℓ) : encode a (Fin.last s) = ∑ i, a i := by
  simp [encode]

@[simp] theorem encode_castSucc (a : Fin s → BlockCoord ℓ) (i : Fin s) :
    encode a i.castSucc = a i := by
  simp [encode]

@[simp] theorem decode_encode (a : Fin s → BlockCoord ℓ) : decode (encode a) = a := by
  funext i
  simp [decode]

theorem add_self_blockCoord (b : BlockCoord ℓ) : b + b = 0 := by
  funext t
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize b t = z
  fin_cases z <;> decide

theorem isAddress_encode (a : Fin s → BlockCoord ℓ) : IsAddress (encode a) := by
  rw [IsAddress, Fin.sum_univ_castSucc]
  simp [add_self_blockCoord]

/-- A permutation of `Fin s`, extended to `Fin (s + 1)` by fixing the last element. -/
def liftPerm (σ : Equiv.Perm (Fin s)) : Equiv.Perm (Fin (s + 1)) where
  toFun := Fin.lastCases (Fin.last s) fun i => (σ i).castSucc
  invFun := Fin.lastCases (Fin.last s) fun i => (σ.symm i).castSucc
  left_inv j := by
    induction j using Fin.lastCases <;> simp
  right_inv j := by
    induction j using Fin.lastCases <;> simp

@[simp] theorem liftPerm_last (σ : Equiv.Perm (Fin s)) : liftPerm σ (Fin.last s) = Fin.last s := by
  simp [liftPerm]

@[simp] theorem liftPerm_castSucc (σ : Equiv.Perm (Fin s)) (i : Fin s) :
    liftPerm σ i.castSucc = (σ i).castSucc := by
  simp [liftPerm]

/-- The identity block-induced permutation. -/
def idPerm (s ℓ : ℕ) : BlockPerm (s + 1) ℓ where
  perm := 1
  shift := 0
  sum_shift := by simp

@[simp] theorem idPerm_act (x : Fin (s + 1) → BlockCoord ℓ) : (idPerm s ℓ).act x = x := by
  funext j
  simp [BlockPerm.act, idPerm]; rfl

/-- The block-induced permutation `π_T` of the update `T`: block `σ(i)` moves to block `i` with
shift `δᵢ`, and the checksum block is shifted by `∑ᵢ δᵢ`. -/
def updatePerm (T : Update s ℓ) : BlockPerm (s + 1) ℓ where
  perm := (liftPerm T.σ).symm
  shift := Fin.lastCases (∑ i, T.δ i) fun m => T.δ (T.σ.symm m)
  sum_shift := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [Equiv.sum_comp T.σ.symm T.δ, add_self_blockCoord]

theorem updatePerm_act_castSucc (T : Update s ℓ) (x : Fin (s + 1) → BlockCoord ℓ) (i : Fin s) :
    (updatePerm T).act x i.castSucc = x (T.σ i).castSucc + T.δ i := by
  simp [BlockPerm.act, updatePerm]

theorem decode_updatePerm_act (T : Update s ℓ) (x : Fin (s + 1) → BlockCoord ℓ) :
    decode ((updatePerm T).act x) = T.apply (decode x) := by
  funext i
  simp [decode, Update.apply, updatePerm_act_castSucc]

theorem updatePerm_act_encode (T : Update s ℓ) (a : Fin s → BlockCoord ℓ) :
    (updatePerm T).act (encode a) = encode (T.apply a) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    simp only [BlockPerm.act, updatePerm, Equiv.symm_symm, liftPerm_last, encode_last,
      Fin.lastCases_last, Update.apply, Finset.sum_add_distrib]
    rw [Equiv.sum_comp T.σ (fun i => a i)]
  | cast i =>
    rw [updatePerm_act_castSucc, encode_castSucc, encode_castSucc]
    rfl

/-- The coordinate domain `⋃ᵢ {i} × Dᵢ ∪ {k} × A` of a guard; if `active` is false, the
checksum block is removed as well, so that no address is allowed. -/
def guardDomain (g : Guard s ℓ) (active : Bool) : Finset (Coord (s + 1) ℓ) :=
  Finset.univ.filter fun c =>
    Fin.lastCases (motive := fun _ => Bool) active (fun i => decide (c.2 ∈ g.sets i)) c.1 = true

theorem supp_subset_guardDomain_iff (g : Guard s ℓ) (active : Bool)
    (x : Fin (s + 1) → BlockCoord ℓ) :
    supp x ⊆ guardDomain g active ↔ g.Holds (decode x) ∧ active = true := by
  simp only [supp, guardDomain, Finset.image_subset_iff, Finset.mem_univ, Finset.mem_filter,
    true_and, forall_const]
  rw [Fin.forall_fin_succ']
  simp [Guard.Holds, decode]

end Lax119563Proofs.Programs

end Programs_Encoding

/-! ### Formerly `Lax119563Proofs.Programs.Compile` -/

section Programs_Compile

/-!
# The implicit parity system of a register program and a query

For a register program `R` with `s` registers over `𝔽₂^ℓ`, `w` control locations and `r`
commands, and a query `(p₀, a₀)`, we construct the implicit parity system `I_{R,*}` with
`k = s + 1` blocks. Its locations are

* one location `Y_p` per control location `p` of `R`;
* eight private locations per command (the assignment gadget uses three of them, a fork uses
  all eight: two one-way gadgets with three internal locations each, and the two branch
  locations `b₁, b₂`);
* four locations of the query detector.

Every location has the full coordinate domain. A *one-way gadget* from `X` to `Y` consists of
the four equation schemas `X + A = 0`, `X + B = 0`, `A + B + Z = 0`, `Z + Y = 0` on fresh
locations `A, B, Z`: a value `X = 0` propagates to `Y = 0`, but no value propagates from `Y`
back to `X`.

* An assignment `when p, φ: a ← T(a); goto q` gives a gadget from `Y_q` (at the address
  `π_T E(a) = E(T(a))`) to `Y_p` (at `E(a)`).
* A fork `when p, φ: fork q and q'` gives gadgets from `Y_q` to `b₁` and from `Y_{q'}` to `b₂`
  and the fork schema `b₁ + b₂ + Y_p = 0`.
* The detector is a gadget from `Y_{p₀}` to a location `o` initialized to `1`, guarded by
  `a = a₀`.

All schemas of a command are guarded by the command's guard; commands at `accept` or `reject`
get an empty domain, so they contribute no equations. The location `Y_accept` is initialized
to `0`.
-/

open Lax119563.ImplicitParitySystems

namespace Lax119563Proofs.Programs

/-! ### Locations -/

/-- The eight private locations of a command. -/
inductive Slot
  | a1 | b1 | z1 | a2 | b2 | z2 | out1 | out2
  deriving DecidableEq

/-- The four locations of the query detector. -/
inductive DetSlot
  | u1 | u2 | z | out
  deriving DecidableEq

/-- Numbering of the private locations of a command. -/
def Slot.toFin : Slot → Fin 8
  | a1 => 0 | b1 => 1 | z1 => 2 | a2 => 3 | b2 => 4 | z2 => 5 | out1 => 6 | out2 => 7

/-- Numbering of the locations of the query detector. -/
def DetSlot.toFin : DetSlot → Fin 4
  | u1 => 0 | u2 => 1 | z => 2 | out => 3

/-- The locations of the compiled system: control locations of the program, private locations
of the commands, and locations of the detector. -/
inductive Role (w r : ℕ)
  | prog (p : Fin w)
  | slot (j : Fin r) (t : Slot)
  | det (t : DetSlot)
  deriving DecidableEq

namespace Role

variable {w r : ℕ}

/-- The owner of a location: `none` for control locations, `some (some j)` for the private
locations of command `j`, `some none` for the detector. -/
def key : Role w r → Option (Option (Fin r))
  | prog _ => none
  | slot j _ => some (some j)
  | det _ => some none

/-- The locations as a sum type. -/
def toSum : Role w r → (Fin w ⊕ Fin r × Fin 8) ⊕ Fin 4
  | prog p => .inl (.inl p)
  | slot j t => .inl (.inr (j, t.toFin))
  | det t => .inr t.toFin

/-- Inverse of `toSum`. -/
def ofSum : (Fin w ⊕ Fin r × Fin 8) ⊕ Fin 4 → Role w r
  | .inl (.inl p) => prog p
  | .inl (.inr (j, t)) => slot j (![Slot.a1, .b1, .z1, .a2, .b2, .z2, .out1, .out2] t)
  | .inr t => det (![DetSlot.u1, .u2, .z, .out] t)

/-- The numbering of the locations `Role w r ≃ Fin (w + 8r + 4)`. -/
def equivFin (w r : ℕ) : Role w r ≃ Fin (w + r * 8 + 4) :=
  (Equiv.mk toSum ofSum
      (by intro x; cases x with
        | prog => rfl
        | slot j t => cases t <;> rfl
        | det t => cases t <;> rfl)
      (by rintro ((p | ⟨j, t⟩) | t)
          · rfl
          · fin_cases t <;> rfl
          · fin_cases t <;> rfl)).trans
    ((Equiv.sumCongr (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv) (Equiv.refl _)).trans
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv))

end Role

variable {s ℓ : ℕ}

/-! ### Schemas -/

section Schemas

variable {N : ℕ}

/-- The one-way gadget from `X` (read at the address `π a`) to `Y` with internal locations
`A, B, Z`, guarded by the coordinate domain `D`. -/
def gadget (X : Fin N) (π : BlockPerm (s + 1) ℓ) (A B Z Y : Fin N)
    (D : Finset (Coord (s + 1) ℓ)) : List (Schema (s + 1) ℓ N) :=
  [.binary X A D π (idPerm s ℓ), .binary X B D π (idPerm s ℓ),
    .ternary A B Z D (idPerm s ℓ) (idPerm s ℓ) (idPerm s ℓ),
    .binary Z Y D (idPerm s ℓ) (idPerm s ℓ)]

end Schemas

namespace RegisterProgram

variable (R : RegisterProgram s ℓ)

/-- The number `w + 8r + 4` of locations of the compiled system. -/
abbrev compiledSize : ℕ := R.numLocations + R.commands.length * 8 + 4

/-- The location of the compiled system with the given role. -/
def loc (ρ : Role R.numLocations R.commands.length) : Fin R.compiledSize :=
  Role.equivFin _ _ ρ

/-- Commands at the location `p` are executed: `p` is neither `accept` nor `reject`. -/
def executable (p : Fin R.numLocations) : Bool :=
  decide (p ≠ R.accept ∧ p ≠ R.reject)

/-- The schemas of command number `j`. -/
def commandSchemas (j : Fin R.commands.length) :
    Command s ℓ R.numLocations → List (Schema (s + 1) ℓ R.compiledSize)
  | .assign p g T q =>
    gadget (R.loc (.prog q)) (updatePerm T) (R.loc (.slot j .a1)) (R.loc (.slot j .b1))
      (R.loc (.slot j .z1)) (R.loc (.prog p)) (guardDomain g (R.executable p))
  | .fork p g q q' =>
    gadget (R.loc (.prog q)) (idPerm s ℓ) (R.loc (.slot j .a1)) (R.loc (.slot j .b1))
      (R.loc (.slot j .z1)) (R.loc (.slot j .out1)) (guardDomain g (R.executable p)) ++
    gadget (R.loc (.prog q')) (idPerm s ℓ) (R.loc (.slot j .a2)) (R.loc (.slot j .b2))
      (R.loc (.slot j .z2)) (R.loc (.slot j .out2)) (guardDomain g (R.executable p)) ++
    [.ternary (R.loc (.slot j .out1)) (R.loc (.slot j .out2)) (R.loc (.prog p))
      (guardDomain g (R.executable p)) (idPerm s ℓ) (idPerm s ℓ) (idPerm s ℓ)]

/-- The guard `a = a₀` of the query detector. -/
def queryGuard (a₀ : Fin s → Fin ℓ → ZMod 2) : Guard s ℓ :=
  ⟨fun i => {a₀ i}⟩

/-- The schemas of the query detector. -/
def detectorSchemas (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    List (Schema (s + 1) ℓ R.compiledSize) :=
  gadget (R.loc (.prog p₀)) (idPerm s ℓ) (R.loc (.det .u1)) (R.loc (.det .u2))
    (R.loc (.det .z)) (R.loc (.det .out)) (guardDomain (queryGuard a₀) true)

/-- All schemas of the compiled system. -/
def compiledSchemas (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    List (Schema (s + 1) ℓ R.compiledSize) :=
  (List.finRange R.commands.length).flatMap (fun j => R.commandSchemas j R.commands[j]) ++
    R.detectorSchemas p₀ a₀

/-- The initialization: `0` at `Y_accept`, `1` at the detector output `o`, `⋆` elsewhere. -/
def compiledInit (v : Fin R.compiledSize) : Option (ZMod 2) :=
  if v = R.loc (.prog R.accept) then some 0
  else if v = R.loc (.det .out) then some 1
  else none

@[simp] theorem loc_inj {ρ ρ' : Role R.numLocations R.commands.length} :
    R.loc ρ = R.loc ρ' ↔ ρ = ρ' :=
  (Role.equivFin _ _).apply_eq_iff_eq

/-- The owner of a location of the compiled system, see `Role.key`. -/
def locKey (v : Fin R.compiledSize) : Option (Option (Fin R.commands.length)) :=
  ((Role.equivFin _ _).symm v).key

@[simp] theorem locKey_loc (ρ : Role R.numLocations R.commands.length) :
    R.locKey (R.loc ρ) = ρ.key := by
  simp [locKey, loc]

end RegisterProgram

/-! ### Well-formedness and the meet condition -/

section Meet

variable {k N : ℕ}

/-- Two schemas share at most one location. -/
def Meet (e e' : Schema k ℓ N) : Prop :=
  (e.locations ∩ e'.locations).card ≤ 1

/-- Every location of `e` is `u` or satisfies `Pr`. -/
def HasShape (e : Schema k ℓ N) (u : Fin N) (Pr : Fin N → Prop) : Prop :=
  ∀ x ∈ e.locations, x = u ∨ Pr x

theorem HasShape.mono {e : Schema k ℓ N} {u : Fin N} {Pr Pr' : Fin N → Prop}
    (h : HasShape e u Pr) (hPr : ∀ x, Pr x → Pr' x) : HasShape e u Pr' :=
  fun x hx => (h x hx).imp_right (hPr x)

theorem meet_of_shape {e e' : Schema k ℓ N} {u u' : Fin N} {Pr Pr' : Fin N → Prop}
    (h : HasShape e u Pr) (h' : HasShape e' u' Pr') (hPr : ∀ x, Pr x → x ≠ u' ∧ ¬ Pr' x) :
    Meet e e' := by
  have hu : ∀ x ∈ e.locations ∩ e'.locations, x = u := by
    intro x hx
    rw [Finset.mem_inter] at hx
    rcases h x hx.1 with hx1 | hx1
    · exact hx1
    · rcases h' x hx.2 with hx2 | hx2
      · exact absurd hx2 (hPr x hx1).1
      · exact absurd hx2 (hPr x hx1).2
  exact Finset.card_le_one.2 fun x hx y hy => (hu x hx).trans (hu y hy).symm

/-- All locations of `e` but possibly one location `u` belong to the owner `κ`; the location
`u` belongs to `κ` or to no owner. -/
def Owned {K : Type*} (key : Fin N → Option K) (κ : K) (e : Schema k ℓ N) : Prop :=
  ∃ u, (key u = none ∨ key u = some κ) ∧ HasShape e u fun x => key x = some κ

theorem meet_of_owned {K : Type*} (key : Fin N → Option K) {κ κ' : K} (hκ : κ ≠ κ')
    {e e' : Schema k ℓ N} (h : Owned key κ e) (h' : Owned key κ' e') : Meet e e' := by
  obtain ⟨u, -, hu⟩ := h
  obtain ⟨u', hu', hu'e⟩ := h'
  refine meet_of_shape hu hu'e fun x hx => ⟨?_, ?_⟩
  · rintro rfl
    rcases hu' with h | h <;> rw [hx] at h
    · exact absurd h (by simp)
    · exact hκ (Option.some.inj h)
  · rw [hx]
    exact fun h => hκ (Option.some.inj h)

variable {X A B Z Y : Fin N} {π : BlockPerm (s + 1) ℓ} {D : Finset (Coord (s + 1) ℓ)}

theorem gadget_shape :
    ∀ e ∈ gadget X π A B Z Y D, ∃ u, (u = X ∨ u = Y ∨ u = A) ∧
      HasShape e u fun x => x = A ∨ x = B ∨ x = Z := by
  simp only [gadget, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl)
  · refine ⟨X, by simp, fun x hx => ?_⟩
    simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx
    tauto
  · refine ⟨X, by simp, fun x hx => ?_⟩
    simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx
    tauto
  · refine ⟨A, by simp, fun x hx => ?_⟩
    simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx
    tauto
  · refine ⟨Y, by simp, fun x hx => ?_⟩
    simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx
    tauto

theorem gadget_owned {K : Type*} (key : Fin N → Option K) (κ : K)
    (hX : key X = none ∨ key X = some κ) (hY : key Y = none ∨ key Y = some κ)
    (hA : key A = some κ) (hB : key B = some κ) (hZ : key Z = some κ) :
    ∀ e ∈ gadget X π A B Z Y D, Owned key κ e := by
  intro e he
  obtain ⟨u, hu, hshape⟩ := gadget_shape e he
  refine ⟨u, ?_, hshape.mono ?_⟩
  · rcases hu with rfl | rfl | rfl
    · exact hX
    · exact hY
    · exact Or.inr hA
  · rintro x (rfl | rfl | rfl) <;> assumption

theorem gadget_pairwise (hAB : A ≠ B) (hAZ : A ≠ Z) (hBZ : B ≠ Z) (hXA : X ≠ A) (hXB : X ≠ B)
    (hXZ : X ≠ Z) (hYA : Y ≠ A) (hYB : Y ≠ B) (hYZ : Y ≠ Z) :
    (gadget X π A B Z Y D).Pairwise Meet := by
  simp only [gadget, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
  · refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [Schema.locations, Finset.mem_inter, Finset.mem_insert,
      Finset.mem_singleton] at ha hb
    grind

theorem gadget_wellFormed (hXA : X ≠ A) (hXB : X ≠ B) (hAB : A ≠ B) (hAZ : A ≠ Z)
    (hBZ : B ≠ Z) (hZY : Z ≠ Y) :
    ∀ e ∈ gadget X π A B Z Y D, e.WellFormed fun _ => Finset.univ := by
  simp only [gadget, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl) <;> simp [Schema.WellFormed, *]

end Meet

namespace RegisterProgram

variable (R : RegisterProgram s ℓ)

theorem commandSchemas_wellFormed (j : Fin R.commands.length) (c : Command s ℓ R.numLocations) :
    ∀ e ∈ R.commandSchemas j c, e.WellFormed fun _ => Finset.univ := by
  cases c with
  | assign p g T q =>
    exact gadget_wellFormed (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  | fork p g q q' =>
    simp only [commandSchemas, List.mem_append, List.mem_singleton]
    rintro e ((he | he) | rfl)
    · exact gadget_wellFormed (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) e he
    · exact gadget_wellFormed (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) e he
    · simp [Schema.WellFormed]

theorem commandSchemas_owned (j : Fin R.commands.length) (c : Command s ℓ R.numLocations) :
    ∀ e ∈ R.commandSchemas j c, Owned R.locKey (some j) e := by
  cases c with
  | assign p g T q =>
    exact gadget_owned _ _ (by simp [Role.key]) (by simp [Role.key]) (by simp [Role.key])
      (by simp [Role.key]) (by simp [Role.key])
  | fork p g q q' =>
    simp only [commandSchemas, List.mem_append, List.mem_singleton]
    rintro e ((he | he) | rfl)
    · exact gadget_owned _ _ (by simp [Role.key]) (by simp [Role.key]) (by simp [Role.key])
        (by simp [Role.key]) (by simp [Role.key]) e he
    · exact gadget_owned _ _ (by simp [Role.key]) (by simp [Role.key]) (by simp [Role.key])
        (by simp [Role.key]) (by simp [Role.key]) e he
    · refine ⟨R.loc (.prog p), by simp [Role.key], fun x hx => ?_⟩
      simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp [Role.key]

theorem commandSchemas_pairwise (j : Fin R.commands.length) (c : Command s ℓ R.numLocations) :
    (R.commandSchemas j c).Pairwise Meet := by
  cases c with
  | assign p g T q =>
    exact gadget_pairwise (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp)
  | fork p g q q' =>
    simp only [commandSchemas]
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨gadget_pairwise (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp), gadget_pairwise (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp), ?_⟩, List.pairwise_singleton _ _, ?_⟩
    · intro e he e' he'
      obtain ⟨u, -, hu⟩ := gadget_shape e he
      obtain ⟨u', hu', hu'e⟩ := gadget_shape e' he'
      refine meet_of_shape hu hu'e ?_
      rcases hu' with rfl | rfl | rfl <;> rintro x (rfl | rfl | rfl) <;> simp
    · intro e he e' he'
      rw [List.mem_singleton] at he'
      subst he'
      have hf : HasShape (Schema.ternary (R.loc (.slot j .out1)) (R.loc (.slot j .out2))
          (R.loc (.prog p)) (guardDomain g (R.executable p)) (idPerm s ℓ) (idPerm s ℓ)
          (idPerm s ℓ)) (R.loc (.prog p))
          (fun x => x = R.loc (.slot j .out1) ∨ x = R.loc (.slot j .out2)) := by
        intro x hx
        simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx
        tauto
      rw [List.mem_append] at he
      rcases he with he | he
      · obtain ⟨u, -, hu⟩ := gadget_shape e he
        exact meet_of_shape hu hf (by rintro x (rfl | rfl | rfl) <;> simp)
      · obtain ⟨u, -, hu⟩ := gadget_shape e he
        exact meet_of_shape hu hf (by rintro x (rfl | rfl | rfl) <;> simp)

theorem detectorSchemas_wellFormed (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    ∀ e ∈ R.detectorSchemas p₀ a₀, e.WellFormed fun _ => Finset.univ :=
  gadget_wellFormed (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

theorem detectorSchemas_owned (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    ∀ e ∈ R.detectorSchemas p₀ a₀, Owned R.locKey none e :=
  gadget_owned _ _ (by simp [Role.key]) (by simp [Role.key]) (by simp [Role.key])
    (by simp [Role.key]) (by simp [Role.key])

theorem detectorSchemas_pairwise (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    (R.detectorSchemas p₀ a₀).Pairwise Meet :=
  gadget_pairwise (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp)

theorem mem_compiledSchemas {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2}
    {e : Schema (s + 1) ℓ R.compiledSize} :
    e ∈ R.compiledSchemas p₀ a₀ ↔
      (∃ j : Fin R.commands.length, e ∈ R.commandSchemas j R.commands[j]) ∨
        e ∈ R.detectorSchemas p₀ a₀ := by
  simp [compiledSchemas, List.mem_flatMap]

theorem compiledSchemas_wellFormed (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    ∀ e ∈ R.compiledSchemas p₀ a₀, e.WellFormed fun _ => Finset.univ := by
  intro e he
  rcases R.mem_compiledSchemas.1 he with ⟨j, he⟩ | he
  · exact R.commandSchemas_wellFormed j _ e he
  · exact R.detectorSchemas_wellFormed p₀ a₀ e he

theorem compiledSchemas_pairwise (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    (R.compiledSchemas p₀ a₀).Pairwise Meet := by
  rw [compiledSchemas, List.pairwise_append, List.pairwise_flatMap]
  refine ⟨⟨fun j _ => R.commandSchemas_pairwise j _, ?_⟩, R.detectorSchemas_pairwise p₀ a₀, ?_⟩
  · refine (List.nodup_finRange _).imp fun {j j'} hjj' e he e' he' => ?_
    exact meet_of_owned R.locKey (by simpa using hjj') (R.commandSchemas_owned j _ e he)
      (R.commandSchemas_owned j' _ e' he')
  · intro e he e' he'
    obtain ⟨j, -, he⟩ := List.mem_flatMap.1 he
    exact meet_of_owned R.locKey (by simp) (R.commandSchemas_owned j _ e he)
      (R.detectorSchemas_owned p₀ a₀ e' he')

/-- **The implicit parity system `I_{R,*}`** of the register program `R` and the query
`(p₀, a₀)`, with `k = s + 1` blocks, `w + 8r + 4` locations with full coordinate domains, and
at most `9r + 4` schemas. -/
def compile (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    ImplicitParitySystem (s + 1) ℓ where
  numLocations := R.compiledSize
  domain _ := Finset.univ
  schemas := R.compiledSchemas p₀ a₀
  init := R.compiledInit
  schema_wellFormed := R.compiledSchemas_wellFormed p₀ a₀
  schemas_meet := R.compiledSchemas_pairwise p₀ a₀

end RegisterProgram

end Lax119563Proofs.Programs

end Programs_Compile

/-! ### Formerly `Lax119563Proofs.Programs.Correctness` -/

section Programs_Correctness

/-!
# Correctness of the compiled implicit parity system

For a register program `R` and a query `(p₀, a₀)`, the implicit parity system
`R.compile p₀ a₀` has a conflict if and only if the query accepts.

* If `(p, a)` accepts, then unit propagation derives `Y_{p, E(a)} = 0`, by induction on the
  derivation of acceptance: each one-way gadget transmits the value `0` from its input to its
  output in three rounds, and a fork schema combines the two branch values. For the query,
  the detector then derives `z = 0`, while `z = 1` follows from the initialization of `o`.
* Conversely, if the query does not accept, we exhibit a partial assignment that contains the
  initial facts and is closed under every equation: control locations carry `0` exactly at
  accepting configurations, and the gadget locations carry the values forced by them. Every
  derived fact belongs to this partial assignment, so no conflict occurs.
-/

open Lax119563.ImplicitParitySystems Lax119563.ParitySystems

namespace Lax119563Proofs.Programs

variable {s ℓ : ℕ}

/-! ### Generic facts about gadgets -/

section Gadget

variable {N : ℕ} {X A B Z Y : Fin N} {π : BlockPerm (s + 1) ℓ} {D : Finset (Coord (s + 1) ℓ)}

theorem gadget_domain : ∀ e ∈ gadget X π A B Z Y D, e.domain = D := by
  simp only [gadget, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl) <;> rfl

/-- In a parity system containing the equations of a gadget at the address `x`, the value `0`
at its input propagates to `Z` in two rounds and to the output in three rounds. -/
theorem gadget_propagate {P : ParitySystem (Fin N × (Fin (s + 1) → BlockCoord ℓ))}
    {x : Fin (s + 1) → BlockCoord ℓ}
    (hsub : ∀ e ∈ gadget X π A B Z Y D, e.equation x ∈ P.equations) (hXA : X ≠ A) (hXB : X ≠ B)
    (hAB : A ≠ B) (hAZ : A ≠ Z) (hBZ : B ≠ Z) (hZY : Z ≠ Y) {r : ℕ}
    (hX : ((X, π.act x), 0) ∈ P.known r) :
    ((Z, x), 0) ∈ P.known (r + 2) ∧ ((Y, x), 0) ∈ P.known (r + 3) := by
  have h1 := hsub (.binary X A D π (idPerm s ℓ)) (by simp [gadget])
  have h2 := hsub (.binary X B D π (idPerm s ℓ)) (by simp [gadget])
  have h3 := hsub (.ternary A B Z D (idPerm s ℓ) (idPerm s ℓ) (idPerm s ℓ)) (by simp [gadget])
  have h4 := hsub (.binary Z Y D (idPerm s ℓ) (idPerm s ℓ)) (by simp [gadget])
  simp only [Schema.equation, idPerm_act] at h1 h2 h3 h4
  have hA := ParitySystem.known_pair _ (by simp [hXA]) h1 hX
  have hB := ParitySystem.known_pair _ (by simp [hXB]) h2 hX
  have hZ := ParitySystem.known_triple _ (by simp [hAB]) (by simp [hAZ]) (by simp [hBZ]) h3
    hA hB
  rw [add_zero] at hZ
  exact ⟨hZ, ParitySystem.known_pair _ (by simp [hZY]) h4 hZ⟩

/-- In a parity system containing the equations of a gadget at the address `x`, a value at the
output propagates to `Z` in one round. -/
theorem gadget_back {P : ParitySystem (Fin N × (Fin (s + 1) → BlockCoord ℓ))}
    {x : Fin (s + 1) → BlockCoord ℓ}
    (hsub : ∀ e ∈ gadget X π A B Z Y D, e.equation x ∈ P.equations) (hZY : Z ≠ Y) {r : ℕ}
    {b : ZMod 2} (hY : ((Y, x), b) ∈ P.known r) : ((Z, x), b) ∈ P.known (r + 1) := by
  have h4 := hsub (.binary Z Y D (idPerm s ℓ) (idPerm s ℓ)) (by simp [gadget])
  simp only [Schema.equation, idPerm_act] at h4
  rw [Finset.pair_comm] at h4
  exact ParitySystem.known_pair _ (by simp [hZY.symm]) h4 hY

/-- A partial assignment with the values forced by a gadget is closed under its equations,
provided its input carries at most the value `0`, and only if its output carries `0`. -/
theorem gadget_closed (val : Fin N × (Fin (s + 1) → BlockCoord ℓ) → Option (ZMod 2))
    (hXA : X ≠ A) (hXB : X ≠ B) (hAB : A ≠ B) (hAZ : A ≠ Z) (hBZ : B ≠ Z) (hZY : Z ≠ Y)
    (x : Fin (s + 1) → BlockCoord ℓ)
    (hA : val (A, x) = val (X, π.act x)) (hB : val (B, x) = val (X, π.act x))
    (hZ : val (Z, x) = val (Y, x))
    (h0 : ∀ b, val (X, π.act x) = some b → b = 0 ∧ val (Y, x) = some 0) :
    ∀ e ∈ gadget X π A B Z Y D, ParitySystem.Closed val (e.equation x) := by
  simp only [gadget, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl) <;> simp only [Schema.equation, idPerm_act]
  · exact ParitySystem.closed_pair (by simp [hXA]) hA.symm
  · exact ParitySystem.closed_pair (by simp [hXB]) hB.symm
  · refine ParitySystem.closed_triple (by simp [hAB]) (by simp [hAZ]) (by simp [hBZ])
      ?_ ?_ ?_
    · intro b c hb hc
      rw [hB] at hb
      obtain ⟨rfl, hY⟩ := h0 b hb
      rw [hZ, hY] at hc
      cases hc
      rw [hA, hb]
      rfl
    · intro b c hb hc
      rw [hA] at hb
      obtain ⟨rfl, hY⟩ := h0 b hb
      rw [hZ, hY] at hc
      cases hc
      rw [hB, hb]
      rfl
    · intro b c hb hc
      rw [hA] at hb
      rw [hB, hb] at hc
      cases hc
      obtain ⟨rfl, hY⟩ := h0 b hb
      rw [hZ, hY]
      rfl
  · exact ParitySystem.closed_pair (by simp [hZY]) hZ

end Gadget

namespace RegisterProgram

variable (R : RegisterProgram s ℓ)

/-! ### Completeness: accepting configurations are derived -/

theorem exists_index_of_mem {c : Command s ℓ R.numLocations} (hc : c ∈ R.commands) :
    ∃ j : Fin R.commands.length, R.commands[j] = c := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
  exact ⟨⟨i, hi⟩, rfl⟩

/-- The parity system defined by `R.compile p₀ a₀`, with its variables indexed by
`Fin R.compiledSize`. -/
abbrev compiledParity (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    ParitySystem (Fin R.compiledSize × (Fin (s + 1) → BlockCoord ℓ)) :=
  (R.compile p₀ a₀).toParitySystem

theorem gadget_equations_mem {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2}
    {X A B Z Y : Fin R.compiledSize} {π : BlockPerm (s + 1) ℓ} {D : Finset (Coord (s + 1) ℓ)}
    (hsub : ∀ e ∈ gadget X π A B Z Y D, e ∈ R.compiledSchemas p₀ a₀)
    {x : Fin (s + 1) → BlockCoord ℓ} (hx : IsAddress x) (hD : supp x ⊆ D) :
    ∀ e ∈ gadget X π A B Z Y D, e.equation x ∈ (R.compiledParity p₀ a₀).equations :=
  fun e he => ⟨e, hsub e he, x, hx, (gadget_domain e he).symm ▸ hD, rfl⟩

theorem commandSchemas_subset {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2}
    {j : Fin R.commands.length} {c : Command s ℓ R.numLocations} (hj : R.commands[j] = c) :
    ∀ e ∈ R.commandSchemas j c, e ∈ R.compiledSchemas p₀ a₀ := by
  intro e he
  exact R.mem_compiledSchemas.2 (Or.inl ⟨j, hj ▸ he⟩)

theorem executable_eq_true {p : Fin R.numLocations} (hacc : p ≠ R.accept)
    (hrej : p ≠ R.reject) : R.executable p = true := by
  simp [executable, hacc, hrej]

/-- If `(p, a)` accepts, then `Y_{p, E(a)} = 0` is derived. -/
theorem known_of_accepts (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2)
    {p : Fin R.numLocations} {a : Fin s → Fin ℓ → ZMod 2} (h : R.Accepts p a) :
    ∃ r, ((R.loc (.prog p), encode a), 0) ∈ (R.compiledParity p₀ a₀).known r := by
  induction h with
  | accept a =>
    exact ⟨0, 0, by simp [compile, compiledInit], rfl, isAddress_encode a, by simp [compile]⟩
  | @assign p q g T a hmem hacc hrej hg _ ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨j, hj⟩ := R.exists_index_of_mem hmem
    rw [← updatePerm_act_encode] at hr
    have hD : supp (encode a) ⊆ guardDomain g (R.executable p) := by
      rw [supp_subset_guardDomain_iff, decode_encode]
      exact ⟨hg, R.executable_eq_true hacc hrej⟩
    exact ⟨r + 3, (gadget_propagate
      (R.gadget_equations_mem (R.commandSchemas_subset hj) (isAddress_encode a) hD)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hr).2⟩
  | @fork p q q' g a hmem hacc hrej hg _ _ ih ih' =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := ih'
    obtain ⟨j, hj⟩ := R.exists_index_of_mem hmem
    have hsub := R.commandSchemas_subset (p₀ := p₀) (a₀ := a₀) hj
    simp only [commandSchemas, List.mem_append, List.mem_singleton] at hsub
    have hD : supp (encode a) ⊆ guardDomain g (R.executable p) := by
      rw [supp_subset_guardDomain_iff, decode_encode]
      exact ⟨hg, R.executable_eq_true hacc hrej⟩
    rw [← idPerm_act (encode a)] at hr hr'
    have h1 := (gadget_propagate (R.gadget_equations_mem
      (fun e he => hsub e (Or.inl (Or.inl he))) (isAddress_encode a) hD)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (ParitySystem.known_mono _ (le_max_left r r') hr)).2
    have h2 := (gadget_propagate (R.gadget_equations_mem
      (fun e he => hsub e (Or.inl (Or.inr he))) (isAddress_encode a) hD)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (ParitySystem.known_mono _ (le_max_right r r') hr')).2
    have hf : (Schema.ternary (R.loc (.slot j .out1)) (R.loc (.slot j .out2)) (R.loc (.prog p))
        (guardDomain g (R.executable p)) (idPerm s ℓ) (idPerm s ℓ) (idPerm s ℓ)).equation
          (encode a) ∈ (R.compiledParity p₀ a₀).equations :=
      ⟨_, hsub _ (Or.inr rfl), _, isAddress_encode a, hD, rfl⟩
    simp only [Schema.equation, idPerm_act] at hf
    exact ⟨max r r' + 3 + 1, ParitySystem.known_triple _ (by simp) (by simp) (by simp) hf h1 h2⟩

theorem detectorSchemas_subset {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2} :
    ∀ e ∈ R.detectorSchemas p₀ a₀, e ∈ R.compiledSchemas p₀ a₀ :=
  fun _ he => R.mem_compiledSchemas.2 (Or.inr he)

/-- If the query accepts, the compiled system has a conflict. -/
theorem hasConflict_of_accepts {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2}
    (h : R.Accepts p₀ a₀) : ∃ r, (R.compiledParity p₀ a₀).HasConflict r := by
  obtain ⟨r, hr⟩ := R.known_of_accepts p₀ a₀ h
  have hD : supp (encode a₀) ⊆ guardDomain (queryGuard a₀) true := by
    rw [supp_subset_guardDomain_iff, decode_encode]
    exact ⟨fun i => by simp [queryGuard], rfl⟩
  have hsub := R.gadget_equations_mem (R.detectorSchemas_subset (p₀ := p₀)) (isAddress_encode a₀) hD
  rw [← idPerm_act (encode a₀)] at hr
  have h0 := (gadget_propagate hsub (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) hr).1
  have hout : ((R.loc (.det .out), encode a₀), (1 : ZMod 2)) ∈
      (R.compiledParity p₀ a₀).known 0 :=
    ⟨1, by simp [compile, compiledInit], rfl, isAddress_encode a₀, by simp [compile]⟩
  have h1 := gadget_back hsub (by simp) hout
  exact ⟨r + 2, _, h0, ParitySystem.known_mono _ (by omega) h1⟩

/-! ### Soundness: a closed partial assignment -/

open Classical in
/-- `0` if the configuration `(p, a)` accepts, unknown otherwise. -/
noncomputable def acceptVal (p : Fin R.numLocations) (a : Fin s → Fin ℓ → ZMod 2) :
    Option (ZMod 2) :=
  if R.Accepts p a then some 0 else none

open Classical in
/-- The value of a fork branch location: `0` if the branch target or the fork location accepts. -/
noncomputable def branchVal (p q : Fin R.numLocations) (a : Fin s → Fin ℓ → ZMod 2) :
    Option (ZMod 2) :=
  if R.Accepts q a ∨ R.Accepts p a then some 0 else none

/-- The values at the private locations of a command. -/
noncomputable def slotVal : Command s ℓ R.numLocations → Slot →
    (Fin (s + 1) → BlockCoord ℓ) → Option (ZMod 2)
  | .assign _ _ T q, .a1, x | .assign _ _ T q, .b1, x =>
    R.acceptVal q (decode ((updatePerm T).act x))
  | .assign p _ _ _, .z1, x => R.acceptVal p (decode x)
  | .assign _ _ _ _, _, _ => none
  | .fork _ _ q _, .a1, x | .fork _ _ q _, .b1, x => R.acceptVal q (decode x)
  | .fork p _ q _, .z1, x | .fork p _ q _, .out1, x => R.branchVal p q (decode x)
  | .fork _ _ _ q', .a2, x | .fork _ _ _ q', .b2, x => R.acceptVal q' (decode x)
  | .fork p _ _ q', .z2, x | .fork p _ _ q', .out2, x => R.branchVal p q' (decode x)

/-- The values at a location with the given role. -/
noncomputable def roleVal (p₀ : Fin R.numLocations) :
    Role R.numLocations R.commands.length → (Fin (s + 1) → BlockCoord ℓ) → Option (ZMod 2)
  | .prog p, x => R.acceptVal p (decode x)
  | .slot j t, x => R.slotVal R.commands[j] t x
  | .det .u1, x | .det .u2, x => R.acceptVal p₀ (decode x)
  | .det .z, _ | .det .out, _ => some 1

/-- The closed partial assignment of the compiled system. -/
noncomputable def closedVal (p₀ : Fin R.numLocations) :
    Fin R.compiledSize × (Fin (s + 1) → BlockCoord ℓ) → Option (ZMod 2) :=
  fun v => R.roleVal p₀ ((Role.equivFin _ _).symm v.1) v.2

@[simp] theorem closedVal_loc (p₀ : Fin R.numLocations) (ρ : Role R.numLocations R.commands.length)
    (x : Fin (s + 1) → BlockCoord ℓ) : R.closedVal p₀ (R.loc ρ, x) = R.roleVal p₀ ρ x := by
  simp [closedVal, loc]

theorem acceptVal_eq_some {p : Fin R.numLocations} {a : Fin s → Fin ℓ → ZMod 2} {b : ZMod 2} :
    R.acceptVal p a = some b ↔ R.Accepts p a ∧ b = 0 := by
  unfold acceptVal
  split_ifs with h <;> simp [h, eq_comm]

theorem branchVal_eq_some {p q : Fin R.numLocations} {a : Fin s → Fin ℓ → ZMod 2} {b : ZMod 2} :
    R.branchVal p q a = some b ↔ (R.Accepts q a ∨ R.Accepts p a) ∧ b = 0 := by
  unfold branchVal
  split_ifs with h <;> simp [h, eq_comm]

theorem closed_commandSchemas (p₀ : Fin R.numLocations) (j : Fin R.commands.length)
    {c : Command s ℓ R.numLocations} (hj : R.commands[j] = c) :
    ∀ e ∈ R.commandSchemas j c, ∀ x, supp x ⊆ e.domain →
      ParitySystem.Closed (R.closedVal p₀) (e.equation x) := by
  have hmem : c ∈ R.commands := hj ▸ List.getElem_mem _
  cases c with
  | assign p g T q =>
    intro e he x hx
    rw [gadget_domain e he, supp_subset_guardDomain_iff] at hx
    obtain ⟨hg, hex⟩ := hx
    simp only [executable, decide_eq_true_eq] at hex
    refine gadget_closed _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) x
      ?_ ?_ ?_ ?_ e he
    · simp [roleVal, hj, slotVal]
    · simp [roleVal, hj, slotVal]
    · simp [roleVal, hj, slotVal]
    · intro b hb
      simp only [closedVal_loc, roleVal, acceptVal_eq_some, decode_updatePerm_act] at hb ⊢
      exact ⟨hb.2, Accepts.assign hmem hex.1 hex.2 hg hb.1, trivial⟩
  | fork p g q q' =>
    simp only [commandSchemas, List.mem_append, List.mem_singleton]
    rintro e ((he | he) | rfl) x hx
    · rw [gadget_domain e he, supp_subset_guardDomain_iff] at hx
      refine gadget_closed _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) x
        ?_ ?_ ?_ ?_ e he
      · simp [roleVal, hj, slotVal]
      · simp [roleVal, hj, slotVal]
      · simp [roleVal, hj, slotVal]
      · intro b hb
        simp only [closedVal_loc, roleVal, idPerm_act, acceptVal_eq_some, hj, slotVal,
          branchVal_eq_some] at hb ⊢
        exact ⟨hb.2, Or.inl hb.1, trivial⟩
    · rw [gadget_domain e he, supp_subset_guardDomain_iff] at hx
      refine gadget_closed _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) x
        ?_ ?_ ?_ ?_ e he
      · simp [roleVal, hj, slotVal]
      · simp [roleVal, hj, slotVal]
      · simp [roleVal, hj, slotVal]
      · intro b hb
        simp only [closedVal_loc, roleVal, idPerm_act, acceptVal_eq_some, hj, slotVal,
          branchVal_eq_some] at hb ⊢
        exact ⟨hb.2, Or.inl hb.1, trivial⟩
    · simp only [Schema.domain, supp_subset_guardDomain_iff, executable,
        decide_eq_true_eq] at hx
      obtain ⟨hg, hex⟩ := hx
      simp only [Schema.equation, idPerm_act]
      refine ParitySystem.closed_triple (by simp) (by simp) (by simp) ?_ ?_ ?_ <;>
        intro b c hb hc <;>
        simp only [closedVal_loc, roleVal, hj, slotVal, acceptVal_eq_some,
          branchVal_eq_some] at hb hc ⊢
      · obtain ⟨hp, rfl⟩ := hc
        obtain ⟨-, rfl⟩ := hb
        exact ⟨Or.inr hp, rfl⟩
      · obtain ⟨hp, rfl⟩ := hc
        obtain ⟨-, rfl⟩ := hb
        exact ⟨Or.inr hp, rfl⟩
      · obtain ⟨h1, rfl⟩ := hb
        obtain ⟨h2, rfl⟩ := hc
        refine ⟨?_, rfl⟩
        rcases h1 with h1 | h1
        · rcases h2 with h2 | h2
          · exact Accepts.fork hmem hex.1 hex.2 hg h1 h2
          · exact h2
        · exact h1

theorem closed_detectorSchemas {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2}
    (h : ¬ R.Accepts p₀ a₀) :
    ∀ e ∈ R.detectorSchemas p₀ a₀, ∀ x, supp x ⊆ e.domain →
      ParitySystem.Closed (R.closedVal p₀) (e.equation x) := by
  intro e he x hx
  rw [gadget_domain e he, supp_subset_guardDomain_iff] at hx
  have hx' : decode x = a₀ := funext fun i => by simpa [queryGuard] using hx.1 i
  refine gadget_closed _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) x
    ?_ ?_ ?_ ?_ e he
  · simp [roleVal]
  · simp [roleVal]
  · simp [roleVal]
  · intro b hb
    simp only [closedVal_loc, roleVal, idPerm_act, acceptVal_eq_some, hx'] at hb
    exact absurd hb.1 h

/-- If the query does not accept, the compiled system has no conflict. -/
theorem not_hasConflict {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2}
    (h : ¬ R.Accepts p₀ a₀) (r : ℕ) : ¬ (R.compiledParity p₀ a₀).HasConflict r := by
  refine ParitySystem.not_hasConflict_of_closed _ (R.closedVal p₀) ?_ ?_ r
  · rintro ⟨⟨v, x⟩, b⟩ ⟨b', hinit, rfl, -, -⟩
    simp only [compile, compiledInit] at hinit
    split_ifs at hinit with h1 h2
    · cases hinit
      subst h1
      simpa [roleVal, acceptVal_eq_some] using Accepts.accept (R := R) (decode x)
    · cases hinit
      subst h2
      simp [roleVal]
  · rintro _ ⟨e, he, x, -, hx, rfl⟩
    rcases R.mem_compiledSchemas.1 he with ⟨j, he⟩ | he
    · exact R.closed_commandSchemas p₀ j rfl e he x hx
    · exact R.closed_detectorSchemas h e he x hx

/-! ### Main statements -/

/-- **Program correctness and query detection.** The compiled implicit parity system has a
conflict if and only if the query `(p₀, a₀)` accepts. -/
theorem conflictRound_compile_lt_top_iff (p₀ : Fin R.numLocations)
    (a₀ : Fin s → Fin ℓ → ZMod 2) :
    (R.compile p₀ a₀).conflictRound < ⊤ ↔ R.Accepts p₀ a₀ := by
  rw [ImplicitParitySystem.conflictRound, ParitySystem.conflictRound_lt_top_iff]
  constructor
  · rintro ⟨r, hr⟩
    by_contra h
    exact R.not_hasConflict h r hr
  · exact R.hasConflict_of_accepts

end RegisterProgram

end Lax119563Proofs.Programs

end Programs_Correctness

/-! ### Formerly `Lax119563Proofs.Programs.Size` -/

section Programs_Size

/-!
# Size of the compiled implicit parity system

The compiled system `R.compile p₀ a₀` of a register program with `w` control locations and `r`
commands has exactly `w + 8r + 4` locations, all with the full coordinate domain, and at most
`9r + 4` schemas. Since every schema has `nnz(B_e) ≤ nnz(B) = 2(k-1)·2^ℓ + kℓ·2^ℓ`, the size
parameter of the matrix compiler is `O((s+1)·2^ℓ·w + (s+1)²·2^ℓ·ℓ·(r+1))`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler

namespace Lax119563Proofs.Programs

variable {s ℓ : ℕ}

theorem card_blockCoord : Fintype.card (BlockCoord ℓ) = 2 ^ ℓ := by
  simp [BlockCoord]

theorem card_coord (k : ℕ) : Fintype.card (Coord k ℓ) = k * 2 ^ ℓ := by
  simp [Coord]

/-- The coordinates in a fixed block. -/
theorem card_filter_block_le (k n : ℕ) :
    (Finset.univ.filter fun c : Coord k ℓ => (c.1 : ℕ) = n).card ≤ 2 ^ ℓ := by
  have hsub : (Finset.univ.filter fun c : Coord k ℓ => (c.1 : ℕ) = n) ⊆
      (Finset.univ.filter fun b : Fin k => (b : ℕ) = n) ×ˢ Finset.univ := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp [hc]
  have hone : (Finset.univ.filter fun b : Fin k => (b : ℕ) = n).card ≤ 1 :=
    Finset.card_le_one.2 fun a ha b hb => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact Fin.ext (ha.trans hb.symm)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = _ := by rw [Finset.card_product, Finset.card_univ, card_blockCoord]
    _ ≤ 1 * 2 ^ ℓ := Nat.mul_le_mul_right _ hone
    _ = 2 ^ ℓ := one_mul _

/-- `nnz(B_e) ≤ nnz(B) ≤ 2(k-1)·2^ℓ + ℓk·2^ℓ`. -/
theorem nnz_le {k N : ℕ} (e : Schema k ℓ N) :
    nnz e ≤ (k - 1) * (2 * 2 ^ ℓ) + ℓ * (k * 2 ^ ℓ) := by
  classical
  have hrow : ∀ row, (Finset.univ.filter fun c : Coord k ℓ =>
      checkMatrix k ℓ row c ≠ 0).card ≤
        Sum.elim (fun _ => 2 * 2 ^ ℓ) (fun _ => k * 2 ^ ℓ) row := by
    rintro (i | t)
    · have hsub : (Finset.univ.filter fun c : Coord k ℓ => checkMatrix k ℓ (.inl i) c ≠ 0) ⊆
          (Finset.univ.filter fun c : Coord k ℓ => (c.1 : ℕ) = i) ∪
            (Finset.univ.filter fun c : Coord k ℓ => (c.1 : ℕ) = k - 1) := by
        intro c hc
        simp only [checkMatrix, Matrix.of_apply, Finset.mem_filter, Finset.mem_univ,
          true_and, ne_eq, ite_eq_right_iff, Classical.not_imp] at hc
        simpa using hc.1
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ 2 ^ ℓ + 2 ^ ℓ := Nat.add_le_add (card_filter_block_le _ _) (card_filter_block_le _ _)
        _ = _ := by simp; ring
    · calc _ ≤ (Finset.univ : Finset (Coord k ℓ)).card := Finset.card_filter_le _ _
        _ = _ := by simp
  calc nnz e ≤ (Finset.univ.filter fun x : (Fin (k - 1) ⊕ Fin ℓ) × Coord k ℓ =>
        checkMatrix k ℓ x.1 x.2 ≠ 0).card := by
        unfold nnz
        exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
    _ = ∑ row, (Finset.univ.filter fun c : Coord k ℓ => checkMatrix k ℓ row c ≠ 0).card := by
        rw [Finset.card_filter, Fintype.sum_prod_type]
        simp only [Finset.card_filter]
    _ ≤ ∑ row, Sum.elim (fun _ => 2 * 2 ^ ℓ) (fun _ => k * 2 ^ ℓ) row :=
        Finset.sum_le_sum fun row _ => hrow row
    _ = _ := by simp [Fintype.sum_sum_type]

theorem nnz_le_of_one_le {N : ℕ} (hℓ : 1 ≤ ℓ) (e : Schema (s + 1) ℓ N) :
    nnz e ≤ 3 * (s + 1) * ℓ * 2 ^ ℓ := by
  refine (nnz_le e).trans ?_
  rw [Nat.add_sub_cancel]
  generalize 2 ^ ℓ = Q
  have h : s * (2 * Q) * 1 ≤ (s + 1) * (2 * Q) * ℓ :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_succ s)) hℓ
  calc s * (2 * Q) + ℓ * ((s + 1) * Q) ≤ (s + 1) * (2 * Q) * ℓ + ℓ * ((s + 1) * Q) := by
        rw [mul_one] at h; omega
    _ = _ := by ring

/-- The arithmetic of the size bound: `(w + 8r + 4)·kQ + (k+1)·n ≤ 100·(kQw + k²Qℓ(r+1))`
for `k = s + 1`, `ℓ ≥ 1` and `n ≤ (9r + 4)·3kℓQ`. -/
theorem size_arith {w r Q n : ℕ} (hℓ : 1 ≤ ℓ)
    (hnnz : n ≤ (9 * r + 4) * (3 * (s + 1) * ℓ * Q)) :
    (w + 8 * r + 4) * ((s + 1) * Q) + (s + 1 + 1) * n ≤
      100 * ((s + 1) * Q * w + (s + 1) ^ 2 * Q * ℓ * (r + 1)) := by
  have h1 : (8 * r + 4) * ((s + 1) * Q) ≤ 8 * ((s + 1) ^ 2 * Q * ℓ * (r + 1)) := by
    have : (s + 1) * Q * 1 * 1 ≤ (s + 1) * Q * (s + 1) * ℓ :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hℓ
    nlinarith
  have h2 : (s + 1 + 1) * ((9 * r + 4) * (3 * (s + 1) * ℓ * Q)) ≤
      54 * ((s + 1) ^ 2 * Q * ℓ * (r + 1)) := by
    have ha : s + 1 + 1 ≤ 2 * (s + 1) := by omega
    have hb : 9 * r + 4 ≤ 9 * (r + 1) := by omega
    calc _ ≤ (2 * (s + 1)) * ((9 * (r + 1)) * (3 * (s + 1) * ℓ * Q)) :=
          Nat.mul_le_mul ha (Nat.mul_le_mul_right _ hb)
      _ = _ := by ring
  have h3 : (s + 1 + 1) * n ≤ (s + 1 + 1) * ((9 * r + 4) * (3 * (s + 1) * ℓ * Q)) :=
    Nat.mul_le_mul_left _ hnnz
  rw [show (w + 8 * r + 4) * ((s + 1) * Q) = (s + 1) * Q * w + (8 * r + 4) * ((s + 1) * Q) by
    ring]
  generalize (s + 1) * Q * w = A at *
  generalize (s + 1) ^ 2 * Q * ℓ * (r + 1) = X at *
  generalize (8 * r + 4) * ((s + 1) * Q) = B at *
  generalize (s + 1 + 1) * n = C at *
  generalize (s + 1 + 1) * ((9 * r + 4) * (3 * (s + 1) * ℓ * Q)) = E at *
  omega

namespace RegisterProgram

variable (R : RegisterProgram s ℓ) (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2)

theorem compile_numLocations :
    (R.compile p₀ a₀).numLocations = R.numLocations + 8 * R.commands.length + 4 := by
  simp only [compile, compiledSize]
  ring

theorem compile_domain (v : Fin (R.compile p₀ a₀).numLocations) :
    (R.compile p₀ a₀).domain v = Finset.univ :=
  rfl

theorem commandSchemas_length (j : Fin R.commands.length) (c : Command s ℓ R.numLocations) :
    (R.commandSchemas j c).length ≤ 9 := by
  cases c <;> simp [commandSchemas, gadget]

theorem compile_schemas_length :
    (R.compile p₀ a₀).schemas.length ≤ 9 * R.commands.length + 4 := by
  simp only [compile, compiledSchemas, List.length_append, List.length_flatMap, detectorSchemas,
    gadget, List.length_cons, List.length_nil]
  have := List.sum_le_card_nsmul
    ((List.finRange R.commands.length).map fun j => (R.commandSchemas j R.commands[j]).length) 9
    (by simp only [List.mem_map]; rintro _ ⟨j, -, rfl⟩; exact R.commandSchemas_length j _)
  simp only [List.length_map, List.length_finRange, smul_eq_mul] at this

  omega

/-- **Size of the compiled system.** For `ℓ ≥ 1`, the size parameter of the matrix compiler is
`O((s+1)·2^ℓ·w + (s+1)²·2^ℓ·ℓ·(r+1))` with an absolute constant. -/
theorem sizeParameter_compile_le (hℓ : 1 ≤ ℓ) :
    matrixSize (R.compile p₀ a₀) ≤
      100 * ((s + 1) * 2 ^ ℓ * R.numLocations +
        (s + 1) ^ 2 * 2 ^ ℓ * ℓ * (R.commands.length + 1)) := by
  have hdom : ∑ v, ((R.compile p₀ a₀).domain v).card =
      (R.numLocations + 8 * R.commands.length + 4) * ((s + 1) * 2 ^ ℓ) := by
    simp only [compile_domain, Finset.card_univ, card_coord, Finset.sum_const, smul_eq_mul]
    rw [Fintype.card_fin, compile_numLocations]
  have hnnz : ((R.compile p₀ a₀).schemas.map nnz).sum ≤
      (9 * R.commands.length + 4) * (3 * (s + 1) * ℓ * 2 ^ ℓ) := by
    have hle := List.sum_le_card_nsmul ((R.compile p₀ a₀).schemas.map nnz)
      (3 * (s + 1) * ℓ * 2 ^ ℓ) (by
        simp only [List.mem_map]
        rintro _ ⟨e, -, rfl⟩
        exact nnz_le_of_one_le hℓ e)
    rw [List.length_map, smul_eq_mul] at hle
    exact hle.trans (Nat.mul_le_mul_right _ (R.compile_schemas_length p₀ a₀))
  unfold matrixSize
  rw [hdom]
  exact size_arith hℓ hnnz

end RegisterProgram

end Lax119563Proofs.Programs

end Programs_Size

/-! ### Formerly `Lax119563Proofs.UpperBound.Rounds` -/

section UpperBound_Rounds

/-!
# Distinguishing rounds are bounded by the stabilization round

If `k`-WL stabilizes after `r` rounds on both `G` and `H` and distinguishes them, then it
distinguishes them after at most `r + 1` rounds (paper, fact `wl-compare`).

The argument: if both graphs are stable after `s` rounds and `G`, `H` are not distinguished
after `s + 1` rounds, then any two tuples (of `G` or `H`) with the same round-`s` color have the
same round-`(s+1)` color. Hence round-`(s+1)` colors determine round-`(s+2)` colors uniformly
across both graphs, and `G`, `H` are not distinguished after `s + 2` rounds either.
Stability persists, so by induction `G`, `H` are never distinguished after a round `> r + 1`.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.Stabilization

namespace Lax119563Proofs.UpperBound

/-- Transporting a multiset equality along a relation of the mapping functions. -/
theorem multiset_map_eq_of_map_eq {α β γ δ : Type*} {f : α → γ} {g : β → γ} {f' : α → δ}
    {g' : β → δ} (h : ∀ a b, f a = g b → f' a = g' b) :
    ∀ (s : Multiset α) (t : Multiset β), s.map f = t.map g → s.map f' = t.map g' := by
  classical
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro t ht
    have : t = 0 := by simpa [eq_comm] using ht
    simp [this]
  | cons a s ih =>
    intro t ht
    rw [Multiset.map_cons] at ht
    have hmem : f a ∈ t.map g := ht ▸ Multiset.mem_cons_self _ _
    obtain ⟨b, hb, hfb⟩ := Multiset.mem_map.1 hmem
    rw [← Multiset.cons_erase hb] at ht ⊢
    rw [Multiset.map_cons, hfb] at ht
    have ht' := (Multiset.cons_inj_right _).1 ht
    rw [Multiset.map_cons, Multiset.map_cons, ih _ ht', h a b hfb.symm]

theorem not_distinguishesAfter_self (k r : ℕ) (A : ColoredGraph) :
    ¬ DistinguishesAfter k r A A := fun ⟨_, hc⟩ => hc rfl

theorem not_distinguishesAfter_symm {k r : ℕ} {A B : ColoredGraph}
    (h : ¬ DistinguishesAfter k r A B) : ¬ DistinguishesAfter k r B A :=
  fun ⟨c, hc⟩ => h ⟨c, Ne.symm hc⟩

theorem card_eq_of_not_distinguishesAfter {k r : ℕ} {A B : ColoredGraph}
    (h : ¬ DistinguishesAfter k r A B) (c : Color k r) :
    Nat.card {p : Fin k → Fin A.n // color A r p = c} =
      Nat.card {q : Fin k → Fin B.n // color B r q = c} :=
  not_not.1 fun hc => h ⟨c, hc⟩

/-- A tuple of `B` with color `c` yields a tuple of `A` with color `c`. -/
theorem exists_color_eq {k r : ℕ} {A B : ColoredGraph} (h : ¬ DistinguishesAfter k r A B)
    (y : Fin k → Fin B.n) : ∃ x : Fin k → Fin A.n, color A r x = color B r y := by
  have hy : Nat.card {q : Fin k → Fin B.n // color B r q = color B r y} ≠ 0 :=
    Nat.card_ne_zero.2 ⟨⟨⟨y, rfl⟩⟩, inferInstance⟩
  rw [← card_eq_of_not_distinguishesAfter h] at hy
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.1 hy).1
  exact ⟨x, hx⟩

/-- If `A` is stable after `s` rounds and `A`, `B` are not distinguished after `s + 1` rounds,
then tuples of `A` and `B` with equal round-`s` colors have equal round-`(s+1)` colors. -/
theorem color_succ_eq {k s : ℕ} {A B : ColoredGraph} (hA : StabilizesAfter k s A)
    (hAB : ¬ DistinguishesAfter k (s + 1) A B) {x : Fin k → Fin A.n} {y : Fin k → Fin B.n}
    (h : color A s x = color B s y) : color A (s + 1) x = color B (s + 1) y := by
  obtain ⟨x', hx'⟩ := exists_color_eq hAB y
  have h1 : color A s x' = color B s y := congrArg Prod.fst hx'
  rw [← hx']
  exact (hA x x').1 (h.trans h1.symm)

/-- Under the same hypotheses, equal round-`(s+1)` colors give equal round-`(s+2)` colors. -/
theorem color_succ_succ_eq {k s : ℕ} {A B : ColoredGraph} (hA : StabilizesAfter k s A)
    (hAB : ¬ DistinguishesAfter k (s + 1) A B) {p : Fin k → Fin A.n} {q : Fin k → Fin B.n}
    (h : color A (s + 1) p = color B (s + 1) q) : color A (s + 2) p = color B (s + 2) q := by
  have h2 : (Finset.univ : Finset (Fin A.n)).val.map
      (fun v i => color A s (Function.update p i v)) =
      (Finset.univ : Finset (Fin B.n)).val.map
      (fun v i => color B s (Function.update q i v)) := congrArg Prod.snd h
  change (color A (s + 1) p, (Finset.univ : Finset (Fin A.n)).val.map
      fun v i => color A (s + 1) (Function.update p i v)) =
    (color B (s + 1) q, (Finset.univ : Finset (Fin B.n)).val.map
      fun v i => color B (s + 1) (Function.update q i v))
  rw [h]
  congr 1
  exact multiset_map_eq_of_map_eq
    (fun v w hvw => funext fun i => color_succ_eq hA hAB (congrFun hvw i)) _ _ h2

/-- Stability persists. -/
theorem stabilizesAfter_succ {k s : ℕ} {A : ColoredGraph} (hA : StabilizesAfter k s A) :
    StabilizesAfter k (s + 1) A := fun _ _ =>
  ⟨fun h => color_succ_succ_eq hA (not_distinguishesAfter_self _ _ _) h,
    fun h => congrArg Prod.fst h⟩

theorem stabilizesAfter_add {k s : ℕ} {A : ColoredGraph} (hA : StabilizesAfter k s A) :
    ∀ j, StabilizesAfter k (s + j) A
  | 0 => hA
  | j + 1 => stabilizesAfter_succ (stabilizesAfter_add hA j)

theorem stabilizesAfter_mono {k s t : ℕ} {A : ColoredGraph} (hA : StabilizesAfter k s A)
    (hst : s ≤ t) : StabilizesAfter k t A := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hst
  exact stabilizesAfter_add hA j

/-- The induction step: not distinguished after `s + 1` rounds implies not distinguished after
`s + 2` rounds, when both graphs are stable after `s` rounds. -/
theorem not_distinguishesAfter_succ {k s : ℕ} {G H : ColoredGraph}
    (hG : StabilizesAfter k s G) (hH : StabilizesAfter k s H)
    (hGH : ¬ DistinguishesAfter k (s + 1) G H) : ¬ DistinguishesAfter k (s + 2) G H := by
  rintro ⟨e, he⟩
  by_cases hp : ∃ p, color G (s + 2) p = e
  · obtain ⟨p₀, rfl⟩ := hp
    obtain ⟨q₀, hq₀⟩ := exists_color_eq (not_distinguishesAfter_symm hGH) p₀
    have hpq : color G (s + 2) p₀ = color H (s + 2) q₀ :=
      color_succ_succ_eq hG hGH hq₀.symm
    have eG : Nat.card {p : Fin k → Fin G.n // color G (s + 2) p = color G (s + 2) p₀} =
        Nat.card {p : Fin k → Fin G.n // color G (s + 1) p = color G (s + 1) p₀} :=
      Nat.card_congr <| Equiv.subtypeEquivRight fun p =>
        ⟨fun h => congrArg Prod.fst h,
          fun h => color_succ_succ_eq hG (not_distinguishesAfter_self _ _ _) h⟩
    have eH : Nat.card {q : Fin k → Fin H.n // color H (s + 2) q = color G (s + 2) p₀} =
        Nat.card {q : Fin k → Fin H.n // color H (s + 1) q = color G (s + 1) p₀} := by
      rw [hpq, ← hq₀]
      exact Nat.card_congr <| Equiv.subtypeEquivRight fun q =>
        ⟨fun h => congrArg Prod.fst h,
          fun h => color_succ_succ_eq hH (not_distinguishesAfter_self _ _ _) h⟩
    exact he (by rw [eG, eH]; exact card_eq_of_not_distinguishesAfter hGH _)
  · push Not at hp
    have h0 : Nat.card {p : Fin k → Fin G.n // color G (s + 2) p = e} = 0 :=
      Nat.card_eq_zero.2 (Or.inl ⟨fun ⟨p, hp'⟩ => hp p hp'⟩)
    rw [h0] at he
    obtain ⟨⟨q₀, rfl⟩⟩ := (Nat.card_ne_zero.1 he.symm).1
    obtain ⟨p, hp'⟩ := exists_color_eq hGH q₀
    exact hp p (color_succ_succ_eq hG hGH hp')

/-- **Fact (wl-compare).** If `k`-WL stabilizes after `r` rounds on `G` and on `H` and
distinguishes `G` and `H`, then it distinguishes them after at most `r + 1` rounds. -/
theorem exists_distinguishesAfter_le {k r : ℕ} {G H : ColoredGraph}
    (hG : StabilizesAfter k r G) (hH : StabilizesAfter k r H) (hD : Distinguishes k G H) :
    ∃ R ≤ r + 1, DistinguishesAfter k R G H := by
  obtain ⟨R, hR⟩ := hD
  by_cases hRr : R ≤ r + 1
  · exact ⟨R, hRr, hR⟩
  by_cases h : DistinguishesAfter k (r + 1) G H
  · exact ⟨r + 1, le_rfl, h⟩
  exfalso
  have key : ∀ j, ¬ DistinguishesAfter k (r + 1 + j) G H := by
    intro j
    induction j with
    | zero => simpa using h
    | succ j ih =>
      have e1 : r + 1 + (j + 1) = r + j + 2 := by omega
      have e2 : r + 1 + j = r + j + 1 := by omega
      rw [e1]
      rw [e2] at ih
      exact not_distinguishesAfter_succ (stabilizesAfter_add hG j) (stabilizesAfter_add hH j) ih
  have e : R = r + 1 + (R - (r + 1)) := by omega
  rw [e] at hR
  exact key _ hR

end Lax119563Proofs.UpperBound

end UpperBound_Rounds

/-! ### Formerly `Lax119563Proofs.Bridges.TM2Sim.Defs` -/

section Bridges_TM2Sim_Defs

/-!
# Simulating archive multitape machines by mathlib stack machines: the machine

Given a machine `R` of the archive model `Lax489179.TuringMachine` we build a bundled mathlib
stack machine (`Turing.FinTM2`) simulating it. The stack machine has an input/output stack
`io` over an arbitrary finite alphabet `A`; the conversion between words over `A` and the
bit strings read and written by `R` is done by two finite-state transducers:

* an *input transducer* `InTransducer A` emitting at most two bits per input symbol (and at most
  two bits at the end of the input);
* an *output transducer* `OutTransducer A` emitting at most one symbol per output bit.

For binary words both are the identity; for the three-letter alphabet of
`Lax759944.BinaryWordEncoding` they translate between the two encodings of lists of natural
numbers (see `Bridges/ToTM2`).

Each tape `j` of `R` is kept as two stacks: `R j` holds the cells from the head rightwards
(the scanned cell on top) and `L j` the cells left of the head (the nearest on top). Missing
cells are blank. A stack entry is a pair of a tape symbol and a flag; on tape `0` the flag marks
the cell at position `0`, which is needed at the end to locate the output.

The phases (labels `Lbl`):
1. `inPop`: pop the input symbols, push the transducer output (reversed) on `tmp`;
2. `inRev`: move `tmp` onto `R 0`, so that `R 0` holds the binary input from its first bit;
3. `mark`: flag the cell at the head (position `0`);
4. `sim`: one transition of `R` per stack-machine step: scan all tapes, then either halt
   (go to `gather`) or write and move on all tapes and change the state;
5. `gather`: move `L 0` onto `R 0`; `seek`: pop `R 0` up to the flagged cell;
6. `feed`: read the output bits from position `0` until a non-bit, push the output
   transducer's symbols on `outRev`;
7. `outRev`: move `outRev` onto `io`;
8. `clear`: empty all tape stacks; `done`: reset the variables and halt.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction)
open Turing

namespace Lax119563Proofs.Bridges.TM2Sim

/-- A finite-state transducer from words over `A` to bit strings, emitting at most two bits per
symbol and at most two bits at the end. -/
structure InTransducer (A : Type) where
  Q : Type
  [fin : Fintype Q]
  start : Q
  δ : Q → A → Q × List Bool
  final : Q → List Bool
  δ_len : ∀ q a, (δ q a).2.length ≤ 2
  final_len : ∀ q, (final q).length ≤ 2

attribute [instance] InTransducer.fin

/-- The output of an input transducer from state `q`. -/
def InTransducer.run {A : Type} (τ : InTransducer A) : τ.Q → List A → List Bool
  | q, [] => τ.final q
  | q, a :: u => (τ.δ q a).2 ++ τ.run (τ.δ q a).1 u

/-- A finite-state transducer from bit strings to words over `A`, emitting at most one symbol
per bit. -/
structure OutTransducer (A : Type) where
  Q : Type
  [fin : Fintype Q]
  start : Q
  δ : Q → Bool → Q × Option A

attribute [instance] OutTransducer.fin

/-- The output of an output transducer from state `q`. -/
def OutTransducer.run {A : Type} (τ : OutTransducer A) : τ.Q → List Bool → List A
  | _, [] => []
  | q, b :: y => (τ.δ q b).2.toList ++ τ.run (τ.δ q b).1 y

variable (R : Machine)

/-- Tape symbols of `R`. -/
abbrev Sym := Fin (R.symbols + 3)

/-- Entries of the tape stacks: a symbol and a flag. -/
abbrev G := Sym R × Bool

/-- The blank entry. -/
def g0 : G R := (0, false)

/-- The tape symbol of a bit. -/
def bitSym (b : Bool) : Sym R := if b then 2 else 1

/-- Whether a tape symbol is a bit. -/
def isBit (s : Sym R) : Bool := s = 1 || s = 2

-- Preserve definition unfolding in the generated Fintype instances.
set_option backward.isDefEq.respectTransparency false in
/-- The stacks. -/
inductive Stk (n : ℕ)
  | io
  | outRev
  | tmp
  | L (j : Fin n)
  | R (j : Fin n)
  deriving DecidableEq, Fintype

/-- The stack alphabets: `A` on `io` and `outRev`, tape entries elsewhere. -/
@[reducible] def Γ' (A : Type) : Stk (R.tapes + 1) → Type
  | .io => A
  | .outRev => A
  | .tmp => G R
  | .L _ => G R
  | .R _ => G R

set_option backward.isDefEq.respectTransparency false in
/-- The labels. -/
inductive Lbl
  | inPop | inRev | mark | sim | gather | seek | feed | outRev | clear | done
  deriving DecidableEq, Fintype

variable (A : Type) (τi : InTransducer A) (τo : OutTransducer A)

/-- The variables of the stack machine. -/
structure Var where
  q : Fin (R.states + 1)
  scanned : Fin (R.tapes + 1) → Sym R
  cell : Option (G R)
  qi : τi.Q
  inSym : Option A
  qo : τo.Q
  outSym : Option A
  flag : Bool

/-- `Var` as a product, for finiteness. -/
def Var.equiv : Var R A τi τo ≃
    Fin (R.states + 1) × (Fin (R.tapes + 1) → Sym R) × Option (G R) × τi.Q × Option A ×
      τo.Q × Option A × Bool where
  toFun v := (v.q, v.scanned, v.cell, v.qi, v.inSym, v.qo, v.outSym, v.flag)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance [Fintype A] : Fintype (Var R A τi τo) := by
  classical
  exact Fintype.ofEquiv _ (Var.equiv R A τi τo).symm

/-- The initial variables. -/
def Var.init : Var R A τi τo :=
  ⟨0, fun _ => 0, none, τi.start, none, τo.start, none, false⟩

variable {R A τi τo}

/-- The instruction of `R` for the current state and scanned symbols. -/
def instr (v : Var R A τi τo) : Instruction (R.tapes + 1) (R.symbols + 3) (R.states + 1) :=
  R.transition v.q v.scanned false

/-- Whether an instruction halts. -/
def isHalt {a b c : ℕ} : Instruction a b c → Bool
  | .halt _ => true
  | .next .. => false

/-- The symbol written on tape `j`. -/
def wr (v : Var R A τi τo) (j : Fin (R.tapes + 1)) : Sym R :=
  match instr v with
  | .next _ w _ => w j
  | .halt _ => 0

/-- The move on tape `j`. -/
def mv (v : Var R A τi τo) (j : Fin (R.tapes + 1)) : Move :=
  match instr v with
  | .next _ _ m => m j
  | .halt _ => .stay

/-- The next control state. -/
def nextQ (v : Var R A τi τo) : Fin (R.states + 1) :=
  match instr v with
  | .next q _ _ => q
  | .halt _ => v.q

/-- Whether a move goes left. -/
def isLeft : Move → Bool
  | .left => true
  | _ => false

/-- Whether a move goes right. -/
def isRight : Move → Bool
  | .right => true
  | _ => false

/-- The current input-transducer step (or its final output when the input is exhausted). -/
def inStep (v : Var R A τi τo) : τi.Q × List Bool :=
  match v.inSym with
  | some a => τi.δ v.qi a
  | none => (v.qi, τi.final v.qi)

/-- The bit of the current cell. -/
def cellBit (v : Var R A τi τo) : Bool := (v.cell.getD (g0 R)).1 = 2

/-- The entry written on a tape: the written symbol, keeping the flag of the old cell. -/
def newCell (v : Var R A τi τo) (j : Fin (R.tapes + 1)) : G R :=
  (wr v j, (v.cell.map Prod.snd).getD false)

/-- Statements of the stack machine. -/
abbrev Stmt' (R : Machine) (A : Type) (τi : InTransducer A) (τo : OutTransducer A) :=
  TM2.Stmt (Γ' R A) Lbl (Var R A τi τo)

open TM2.Stmt

/-- Push a bit on `tmp` if there is one. -/
def pushOpt (g : Var R A τi τo → Option Bool) (next : Stmt' R A τi τo) :
    Stmt' R A τi τo :=
  branch (fun v => (g v).isSome)
    (push (Γ := Γ' R A) Stk.tmp (fun v => ((bitSym R ((g v).getD false), false) : G R)) next) next

/-- Scan the tapes in `js`. -/
def scanAll : List (Fin (R.tapes + 1)) → Stmt' R A τi τo →
    Stmt' R A τi τo
  | [], next => next
  | j :: js, next =>
    peek (Γ := Γ' R A) (Stk.R j)
      (fun v o => { v with scanned := Function.update v.scanned j (o.getD (g0 R) : G R).1 })
      (scanAll js next)

/-- Write and move on tape `j`. -/
def applyOne (j : Fin (R.tapes + 1)) (next : Stmt' R A τi τo) :
    Stmt' R A τi τo :=
  pop (Γ := Γ' R A) (Stk.R j) (fun v o => { v with cell := o })
    (branch (fun v => isRight (mv v j))
      (push (Γ := Γ' R A) (Stk.L j) (fun v => newCell v j) next)
      (push (Γ := Γ' R A) (Stk.R j) (fun v => newCell v j)
        (branch (fun v => isLeft (mv v j))
          (pop (Γ := Γ' R A) (Stk.L j) (fun v o => { v with cell := o })
            (push (Γ := Γ' R A) (Stk.R j) (fun v => v.cell.getD (g0 R)) next))
          next)))

/-- Write and move on the tapes in `js`. -/
def applyAllStmt : List (Fin (R.tapes + 1)) → Stmt' R A τi τo →
    Stmt' R A τi τo
  | [], next => next
  | j :: js, next => applyOne j (applyAllStmt js next)

/-- Pop once from `L j` and `R j` for `j ∈ js`, recording in `flag` whether anything was
popped. -/
def popAll : List (Fin (R.tapes + 1)) → Stmt' R A τi τo →
    Stmt' R A τi τo
  | [], next => next
  | j :: js, next =>
    pop (Γ := Γ' R A) (Stk.L j) (fun v o => { v with flag := v.flag || o.isSome })
      (pop (Γ := Γ' R A) (Stk.R j) (fun v o => { v with flag := v.flag || o.isSome })
        (popAll js next))

variable [Inhabited A]

/-- The program. -/
def prog : Lbl → Stmt' R A τi τo
  | .inPop =>
    pop (Γ := Γ' R A) Stk.io (fun v o => { v with inSym := o })
      (pushOpt (fun v => (inStep v).2[0]?) (pushOpt (fun v => (inStep v).2[1]?)
        (branch (fun v => v.inSym.isSome)
          (load (fun v => { v with qi := (inStep v).1 }) (goto fun _ => .inPop))
          (goto fun _ => .inRev))))
  | .inRev =>
    pop (Γ := Γ' R A) Stk.tmp (fun v o => { v with cell := o })
      (branch (fun v => v.cell.isSome)
        (push (Γ := Γ' R A) (Stk.R 0) (fun v => v.cell.getD (g0 R)) (goto fun _ => .inRev))
        (goto fun _ => .mark))
  | .mark =>
    pop (Γ := Γ' R A) (Stk.R 0) (fun v o => { v with cell := o })
      (push (Γ := Γ' R A) (Stk.R 0) (fun v => (((v.cell.getD (g0 R)).1, true) : G R))
        (goto fun _ => .sim))
  | .sim =>
    scanAll (List.finRange (R.tapes + 1))
      (branch (fun v => isHalt (instr v))
        (goto fun _ => .gather)
        (applyAllStmt (List.finRange (R.tapes + 1))
          (load (fun v => { v with q := nextQ v }) (goto fun _ => .sim))))
  | .gather =>
    pop (Γ := Γ' R A) (Stk.L 0) (fun v o => { v with cell := o })
      (branch (fun v => v.cell.isSome)
        (push (Γ := Γ' R A) (Stk.R 0) (fun v => v.cell.getD (g0 R)) (goto fun _ => .gather))
        (goto fun _ => .seek))
  | .seek =>
    pop (Γ := Γ' R A) (Stk.R 0) (fun v o => { v with cell := o })
      (branch (fun v => (v.cell.map Prod.snd).getD false)
        (goto fun _ => .feed)
        (branch (fun v => v.cell.isSome) (goto fun _ => .seek) (goto fun _ => .outRev)))
  | .feed =>
    branch (fun v => isBit R (v.cell.getD (g0 R)).1)
      (branch (fun v => (τo.δ v.qo (cellBit v)).2.isSome)
        (push (Γ := Γ' R A) Stk.outRev (fun v => (τo.δ v.qo (cellBit v)).2.getD default)
          (load (fun v => { v with qo := (τo.δ v.qo (cellBit v)).1 })
            (pop (Γ := Γ' R A) (Stk.R 0) (fun v o => { v with cell := o })
              (goto fun _ => .feed))))
        (load (fun v => { v with qo := (τo.δ v.qo (cellBit v)).1 })
          (pop (Γ := Γ' R A) (Stk.R 0) (fun v o => { v with cell := o })
            (goto fun _ => .feed))))
      (goto fun _ => .outRev)
  | .outRev =>
    pop (Γ := Γ' R A) Stk.outRev (fun v o => { v with outSym := o })
      (branch (fun v => v.outSym.isSome)
        (push (Γ := Γ' R A) Stk.io (fun v => v.outSym.getD default) (goto fun _ => .outRev))
        (goto fun _ => .clear))
  | .clear =>
    load (fun v => { v with flag := false })
      (popAll (List.finRange (R.tapes + 1))
        (branch (fun v => v.flag) (goto fun _ => .clear) (goto fun _ => .done)))
  | .done => load (fun _ => Var.init R A τi τo) halt

variable (R τi τo) in
/-- The bundled stack machine. -/
noncomputable def tm [Fintype A] : FinTM2 where
  K := Stk (R.tapes + 1)
  k₀ := Stk.io
  k₁ := Stk.io
  Γ := Γ' R A
  Λ := Lbl
  main := .inPop
  σ := Var R A τi τo
  initialState := Var.init R A τi τo
  Γk₀Fin := (inferInstance : Fintype A)
  m := prog

end Lax119563Proofs.Bridges.TM2Sim

end Bridges_TM2Sim_Defs

/-! ### Formerly `Lax119563Proofs.Bridges.TM2Sim.Stmts` -/

section Bridges_TM2Sim_Stmts

/-!
# Simulating archive multitape machines by mathlib stack machines: statement semantics

Stack contents are written as `mkStk io outRev tmp Ls Rs`. We compute the effect of the
compound statements (`pushOpt`, `scanAll`, `applyOne`, `applyAllStmt`, `popAll`) on such
stacks, and set up exact step counting (`Reaches`).
-/

open Lax489179.TuringMachine (Machine Config Move Instruction)
open Turing

namespace Lax119563Proofs.Bridges.TM2Sim

variable {R : Machine} {A : Type} {τi : InTransducer A} {τo : OutTransducer A}

/-- Stack contents. -/
def mkStk (io outR : List A) (tmp : List (G R)) (Ls Rs : Fin (R.tapes + 1) → List (G R)) :
    ∀ k, List (Γ' R A k)
  | .io => io
  | .outRev => outR
  | .tmp => tmp
  | .L j => Ls j
  | .R j => Rs j

section mkStk

variable (io outR : List A) (tmp : List (G R)) (Ls Rs : Fin (R.tapes + 1) → List (G R))

@[simp] lemma mkStk_io : mkStk io outR tmp Ls Rs .io = io := rfl
@[simp] lemma mkStk_outRev : mkStk io outR tmp Ls Rs .outRev = outR := rfl
@[simp] lemma mkStk_tmp : mkStk io outR tmp Ls Rs .tmp = tmp := rfl
@[simp] lemma mkStk_L (j) : mkStk io outR tmp Ls Rs (.L j) = Ls j := rfl
@[simp] lemma mkStk_R (j) : mkStk io outR tmp Ls Rs (.R j) = Rs j := rfl

@[simp] lemma update_io (x : List A) :
    Function.update (mkStk io outR tmp Ls Rs) Stk.io x = mkStk x outR tmp Ls Rs := by
  funext k; cases k <;> simp [Function.update, mkStk]

@[simp] lemma update_outRev (x : List A) :
    Function.update (mkStk io outR tmp Ls Rs) Stk.outRev x = mkStk io x tmp Ls Rs := by
  funext k; cases k <;> simp [Function.update, mkStk]

@[simp] lemma update_tmp (x : List (G R)) :
    Function.update (mkStk io outR tmp Ls Rs) Stk.tmp x = mkStk io outR x Ls Rs := by
  funext k; cases k <;> simp [Function.update, mkStk]

@[simp] lemma update_L (j) (x : List (G R)) :
    Function.update (mkStk io outR tmp Ls Rs) (Stk.L j) x =
      mkStk io outR tmp (Function.update Ls j x) Rs := by
  funext k; cases k with
  | L i =>
    by_cases h : i = j
    · subst h; simp [Function.update, mkStk]
    · simp [Function.update, mkStk, h]
  | _ => simp [Function.update, mkStk]

@[simp] lemma update_R (j) (x : List (G R)) :
    Function.update (mkStk io outR tmp Ls Rs) (Stk.R j) x =
      mkStk io outR tmp Ls (Function.update Rs j x) := by
  funext k; cases k with
  | R i =>
    by_cases h : i = j
    · subst h; simp [Function.update, mkStk]
    · simp [Function.update, mkStk, h]
  | _ => simp [Function.update, mkStk]

end mkStk

/-! ## Simple facts about the variables -/

@[simp] lemma wr_cell (v : Var R A τi τo) (o) (j) : wr { v with cell := o } j = wr v j := rfl
@[simp] lemma mv_cell (v : Var R A τi τo) (o) (j) : mv { v with cell := o } j = mv v j := rfl

/-- The entry of a bit. -/
def bitG (b : Bool) : G R := (bitSym R b, false)

/-! ## `pushOpt` -/

open TM2 in
lemma stepAux_pushOpt (g : Var R A τi τo → Option Bool) (next : Stmt' R A τi τo)
    (v : Var R A τi τo) (io outR : List A) (tmp : List (G R)) (Ls Rs) :
    stepAux (pushOpt g next) v (mkStk io outR tmp Ls Rs) =
      stepAux next v (mkStk io outR ((g v).toList.map bitG ++ tmp) Ls Rs) := by
  unfold pushOpt
  cases h : g v with
  | none => simp [h]
  | some b => simp [h, bitG]

lemma pushTwo_eq (l : List Bool) (hl : l.length ≤ 2) :
    l[1]?.toList.map (bitG (R := R)) ++ (l[0]?.toList.map bitG) = (l.map bitG).reverse := by
  match l, hl with
  | [], _ => rfl
  | [a], _ => rfl
  | [a, b], _ => rfl

/-! ## Scanning -/

/-- The scanned symbol of a right stack. -/
def top (l : List (G R)) : Sym R := (l.head?.getD (g0 R)).1

open TM2 in
lemma stepAux_scanAll (js : List (Fin (R.tapes + 1))) (next : Stmt' R A τi τo)
    (v : Var R A τi τo) (io outR : List A) (tmp : List (G R)) (Ls Rs) :
    stepAux (scanAll js next) v (mkStk io outR tmp Ls Rs) =
      stepAux next { v with scanned := fun i => if i ∈ js then top (Rs i) else v.scanned i }
        (mkStk io outR tmp Ls Rs) := by
  induction js generalizing v with
  | nil => simp [scanAll]
  | cons j js ih =>
    simp only [scanAll, stepAux, mkStk_R]
    rw [ih]
    congr 2
    funext i
    by_cases h₁ : i ∈ js
    · simp [h₁]
    · by_cases h₂ : i = j
      · subst h₂; simp [h₁, top]
      · simp [h₁, h₂]

/-! ## Writing and moving -/

/-- The effect of writing `w` and moving by `m` on a tape kept as stacks `L`, `Rl`. -/
def applyTape (L Rl : List (G R)) (w : Sym R) (m : Move) : List (G R) × List (G R) :=
  match m with
  | .right => ((w, (Rl.head?.map Prod.snd).getD false) :: L, Rl.tail)
  | .stay => (L, (w, (Rl.head?.map Prod.snd).getD false) :: Rl.tail)
  | .left => (L.tail, L.head?.getD (g0 R) :: (w, (Rl.head?.map Prod.snd).getD false) :: Rl.tail)

open TM2 in
lemma stepAux_applyOne (j : Fin (R.tapes + 1)) (next : Stmt' R A τi τo)
    (v : Var R A τi τo) (io outR : List A) (tmp : List (G R)) (Ls Rs) :
    ∃ o, stepAux (applyOne j next) v (mkStk io outR tmp Ls Rs) =
      stepAux next { v with cell := o }
        (mkStk io outR tmp (Function.update Ls j (applyTape (Ls j) (Rs j) (wr v j) (mv v j)).1)
          (Function.update Rs j (applyTape (Ls j) (Rs j) (wr v j) (mv v j)).2)) := by
  unfold applyOne
  cases h : mv v j with
  | right =>
    refine ⟨(Rs j).head?, ?_⟩
    simp [h, isRight, applyTape, newCell, Function.update_idem]
  | stay =>
    refine ⟨(Rs j).head?, ?_⟩
    simp [h, isRight, isLeft, applyTape, newCell, Function.update_idem]
  | left =>
    refine ⟨(Ls j).head?, ?_⟩
    simp [h, isRight, isLeft, applyTape, newCell, Function.update_idem]

/-- The tapes after applying the instruction to the tapes in `js`. -/
def applyLs (js : List (Fin (R.tapes + 1))) (v : Var R A τi τo) (Ls Rs : Fin (R.tapes + 1) → List (G R)) :
    Fin (R.tapes + 1) → List (G R) :=
  fun i => if i ∈ js then (applyTape (Ls i) (Rs i) (wr v i) (mv v i)).1 else Ls i

/-- The tapes after applying the instruction to the tapes in `js`. -/
def applyRs (js : List (Fin (R.tapes + 1))) (v : Var R A τi τo) (Ls Rs : Fin (R.tapes + 1) → List (G R)) :
    Fin (R.tapes + 1) → List (G R) :=
  fun i => if i ∈ js then (applyTape (Ls i) (Rs i) (wr v i) (mv v i)).2 else Rs i

open TM2 in
lemma stepAux_applyAll (js : List (Fin (R.tapes + 1))) (hjs : js.Nodup)
    (next : Stmt' R A τi τo)
    (v : Var R A τi τo) (io outR : List A) (tmp : List (G R)) (Ls Rs) :
    ∃ o, stepAux (applyAllStmt js next) v (mkStk io outR tmp Ls Rs) =
      stepAux next { v with cell := o }
        (mkStk io outR tmp (applyLs js v Ls Rs) (applyRs js v Ls Rs)) := by
  induction js generalizing v Ls Rs with
  | nil =>
    have h1 : applyLs [] v Ls Rs = Ls := by funext i; simp [applyLs]
    have h2 : applyRs [] v Ls Rs = Rs := by funext i; simp [applyRs]
    exact ⟨v.cell, by rw [h1, h2]; rfl⟩
  | cons j js ih =>
    rw [List.nodup_cons] at hjs
    obtain ⟨o₁, h₁⟩ := stepAux_applyOne j (applyAllStmt js next) v io outR tmp Ls Rs
    simp only [applyAllStmt]
    rw [h₁]
    obtain ⟨o₂, h₂⟩ := ih hjs.2 { v with cell := o₁ } _ _
    rw [h₂]
    refine ⟨o₂, ?_⟩
    congr 2
    · funext i
      simp only [applyLs, List.mem_cons, wr_cell, mv_cell]
      by_cases hi : i ∈ js
      · have hij : i ≠ j := fun e => hjs.1 (e ▸ hi)
        simp [hi, hij]
      · by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [hi, hij]
    · funext i
      simp only [applyRs, List.mem_cons, wr_cell, mv_cell]
      by_cases hi : i ∈ js
      · have hij : i ≠ j := fun e => hjs.1 (e ▸ hi)
        simp [hi, hij]
      · by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [hi, hij]

/-! ## Clearing -/

lemma any_congr' {α : Type} (l : List α) (p q : α → Bool) (h : ∀ i ∈ l, p i = q i) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun i hi => h i (by simp [hi]))]

open TM2 in
lemma stepAux_popAll (js : List (Fin (R.tapes + 1))) (hjs : js.Nodup)
    (next : Stmt' R A τi τo)
    (v : Var R A τi τo) (io outR : List A) (tmp : List (G R)) (Ls Rs) :
    stepAux (popAll js next) v (mkStk io outR tmp Ls Rs) =
      stepAux next { v with flag := v.flag || js.any (fun j => !(Ls j).isEmpty || !(Rs j).isEmpty) }
        (mkStk io outR tmp (fun i => if i ∈ js then (Ls i).tail else Ls i)
          (fun i => if i ∈ js then (Rs i).tail else Rs i)) := by
  induction js generalizing v Ls Rs with
  | nil => simp [popAll]
  | cons j js ih =>
    rw [List.nodup_cons] at hjs
    simp only [popAll, stepAux, mkStk_L, mkStk_R, update_L, update_R]
    rw [ih hjs.2]
    have hL : (Function.update Ls j (Ls j).tail) j = (Ls j).tail := by simp
    congr 2
    · simp only [List.any_cons]
      have e : ∀ i ∈ js, Function.update Ls j (Ls j).tail i = Ls i ∧
          Function.update Rs j (Rs j).tail i = Rs i := by
        intro i hi
        have hij : i ≠ j := fun e => hjs.1 (e ▸ hi)
        simp [hij]
      rw [any_congr' js _ _ (fun i hi => by rw [(e i hi).1, (e i hi).2])]
      rcases hLj : Ls j with _ | ⟨a, l⟩ <;> rcases hRj : Rs j with _ | ⟨b, l'⟩ <;>
        simp
    · funext i
      by_cases hi : i ∈ js
      · have hij : i ≠ j := fun e => hjs.1 (e ▸ hi)
        simp [hi, hij]
      · by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [hi, hij]
    · funext i
      by_cases hi : i ∈ js
      · have hij : i ≠ j := fun e => hjs.1 (e ▸ hi)
        simp [hi, hij]
      · by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [hi, hij]

end Lax119563Proofs.Bridges.TM2Sim

end Bridges_TM2Sim_Stmts

/-! ### Formerly `Lax119563Proofs.Bridges.TM2Sim.Phases` -/

section Bridges_TM2Sim_Phases

/-!
# Simulating archive multitape machines by mathlib stack machines: the phases

Exact step counts for each phase of the stack machine `prog` (see `Defs`), stated on stack
contents `mkStk io outRev tmp Ls Rs`.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction)
open Turing

namespace Lax119563Proofs.Bridges.TM2Sim

variable {R : Machine} {A : Type} {τi : InTransducer A} {τo : OutTransducer A} [Inhabited A]

variable (R A τi τo) in
/-- Configurations of the stack machine. -/
abbrev Cfg' := TM2.Cfg (Γ' R A) Lbl (Var R A τi τo)

variable (R A τi τo) in
/-- The step function of the stack machine. -/
def stepF : Cfg' R A τi τo → Option (Cfg' R A τi τo) := TM2.step prog

variable (R A τi τo) in
/-- Exactly `n` steps lead from `c` to `c'`. -/
def Reaches (n : ℕ) (c c' : Cfg' R A τi τo) : Prop :=
  (flip bind (stepF R A τi τo))^[n] (some c) = some c'

lemma reaches_zero (c : Cfg' R A τi τo) : Reaches R A τi τo 0 c c := rfl

lemma reaches_succ {n : ℕ} {c c' c'' : Cfg' R A τi τo} (h : stepF R A τi τo c = some c')
    (h' : Reaches R A τi τo n c' c'') : Reaches R A τi τo (n + 1) c c'' := by
  unfold Reaches at *
  rw [Function.iterate_succ_apply]
  simpa [flip, h] using h'

lemma reaches_one {c c' : Cfg' R A τi τo} (h : stepF R A τi τo c = some c') :
    Reaches R A τi τo 1 c c' := reaches_succ h (reaches_zero _)

lemma reaches_trans {n m : ℕ} {c c' c'' : Cfg' R A τi τo} (h : Reaches R A τi τo n c c')
    (h' : Reaches R A τi τo m c' c'') : Reaches R A τi τo (n + m) c c'' := by
  unfold Reaches at *
  rw [add_comm, Function.iterate_add_apply, h, h']

lemma stepF_some (l : Lbl) (v : Var R A τi τo) (S : ∀ k, List (Γ' R A k)) :
    stepF R A τi τo ⟨some l, v, S⟩ = some (TM2.stepAux (prog l) v S) := rfl


/-! ## Input phase -/

lemma step_inPop_cons (a : A) (u : List A) (v : Var R A τi τo) (t : List (G R)) (Ls Rs) :
    stepF R A τi τo ⟨some .inPop, v, mkStk (a :: u) [] t Ls Rs⟩ =
      some ⟨some .inPop, { v with inSym := some a, qi := (τi.δ v.qi a).1 },
        mkStk u [] (((τi.δ v.qi a).2.map bitG).reverse ++ t) Ls Rs⟩ := by
  rw [stepF_some]
  simp only [prog, TM2.stepAux, mkStk_io, update_io, List.head?_cons, List.tail_cons]
  rw [stepAux_pushOpt, stepAux_pushOpt]
  simp only [TM2.stepAux, inStep, Option.isSome_some, cond_true]
  rw [← List.append_assoc, pushTwo_eq _ (τi.δ_len _ _)]

lemma step_inPop_nil (v : Var R A τi τo) (t : List (G R)) (Ls Rs) :
    stepF R A τi τo ⟨some .inPop, v, mkStk [] [] t Ls Rs⟩ =
      some ⟨some .inRev, { v with inSym := none },
        mkStk [] [] (((τi.final v.qi).map bitG).reverse ++ t) Ls Rs⟩ := by
  rw [stepF_some]
  simp only [prog, TM2.stepAux, mkStk_io, update_io, List.head?_nil, List.tail_nil]
  rw [stepAux_pushOpt, stepAux_pushOpt]
  simp only [TM2.stepAux, inStep, Option.isSome_none, cond_false]
  rw [← List.append_assoc, pushTwo_eq _ (τi.final_len _)]

lemma inPop_run (u : List A) : ∀ (v : Var R A τi τo) (t : List (G R)) (Ls Rs),
    ∃ v' : Var R A τi τo, v'.q = v.q ∧ v'.qo = v.qo ∧
      Reaches R A τi τo (u.length + 1) ⟨some .inPop, v, mkStk u [] t Ls Rs⟩
        ⟨some .inRev, v', mkStk [] [] (((τi.run v.qi u).map bitG).reverse ++ t) Ls Rs⟩ := by
  induction u with
  | nil =>
    intro v t Ls Rs
    exact ⟨{ v with inSym := none }, rfl, rfl, by
      simpa [InTransducer.run] using reaches_one (step_inPop_nil v t Ls Rs)⟩
  | cons a u ih =>
    intro v t Ls Rs
    obtain ⟨v', hq, hqo, hr⟩ := ih { v with inSym := some a, qi := (τi.δ v.qi a).1 }
      (((τi.δ v.qi a).2.map bitG).reverse ++ t) Ls Rs
    refine ⟨v', hq, hqo, ?_⟩
    have := reaches_succ (step_inPop_cons a u v t Ls Rs) hr
    simpa [InTransducer.run, List.map_append, List.reverse_append, List.append_assoc,
      Nat.add_comm] using this

lemma inRev_run (t : List (G R)) : ∀ (v : Var R A τi τo) (Ls Rs),
    ∃ v' : Var R A τi τo, v'.q = v.q ∧ v'.qo = v.qo ∧
      Reaches R A τi τo (t.length + 1) ⟨some .inRev, v, mkStk [] [] t Ls Rs⟩
        ⟨some .mark, v', mkStk [] [] [] Ls (Function.update Rs 0 (t.reverse ++ Rs 0))⟩ := by
  induction t with
  | nil =>
    intro v Ls Rs
    refine ⟨{ v with cell := none }, rfl, rfl, reaches_one ?_⟩
    rw [stepF_some]
    simp [prog, TM2.stepAux]
  | cons g t ih =>
    intro v Ls Rs
    obtain ⟨v', hq, hqo, hr⟩ := ih { v with cell := some g } Ls (Function.update Rs 0 (g :: Rs 0))
    refine ⟨v', hq, hqo, ?_⟩
    have hs : stepF R A τi τo ⟨some .inRev, v, mkStk [] [] (g :: t) Ls Rs⟩ =
        some ⟨some .inRev, { v with cell := some g },
          mkStk [] [] t Ls (Function.update Rs 0 (g :: Rs 0))⟩ := by
      rw [stepF_some]
      simp [prog, TM2.stepAux]
    have := reaches_succ hs hr
    simpa [Nat.add_comm] using this

lemma step_mark (v : Var R A τi τo) (Ls Rs) :
    stepF R A τi τo ⟨some .mark, v, mkStk [] [] [] Ls Rs⟩ =
      some ⟨some .sim, { v with cell := (Rs 0).head? },
        mkStk [] [] [] Ls (Function.update Rs 0 ((top (Rs 0), true) :: (Rs 0).tail))⟩ := by
  rw [stepF_some]
  simp [prog, TM2.stepAux, top]


/-! ## Simulation phase -/

/-- The variables after scanning all tapes. -/
def scanV (v : Var R A τi τo) (Rs : Fin (R.tapes + 1) → List (G R)) : Var R A τi τo :=
  { v with scanned := fun i => top (Rs i) }

lemma step_sim_halt (v : Var R A τi τo) (Ls Rs) (h : isHalt (instr (scanV v Rs)) = true) :
    stepF R A τi τo ⟨some .sim, v, mkStk [] [] [] Ls Rs⟩ =
      some ⟨some .gather, scanV v Rs, mkStk [] [] [] Ls Rs⟩ := by
  rw [stepF_some]
  simp only [prog]
  rw [stepAux_scanAll]
  simp only [List.mem_finRange, if_true]
  simp only [scanV] at h
  simp [TM2.stepAux, h, scanV]

lemma step_sim_next (v : Var R A τi τo) (Ls Rs) (h : isHalt (instr (scanV v Rs)) = false) :
    ∃ o, stepF R A τi τo ⟨some .sim, v, mkStk [] [] [] Ls Rs⟩ =
      some ⟨some .sim, { scanV v Rs with cell := o, q := nextQ (scanV v Rs) },
        mkStk [] [] [] (applyLs (List.finRange (R.tapes + 1)) (scanV v Rs) Ls Rs)
          (applyRs (List.finRange (R.tapes + 1)) (scanV v Rs) Ls Rs)⟩ := by
  rw [stepF_some]
  simp only [prog]
  rw [stepAux_scanAll]
  simp only [List.mem_finRange, if_true]
  have h' : isHalt (instr { v with scanned := fun i => top (Rs i) }) = false := h
  simp only [TM2.stepAux, h', cond_false]
  obtain ⟨o, ho⟩ := stepAux_applyAll (List.finRange (R.tapes + 1)) (List.nodup_finRange _)
    (TM2.Stmt.load (fun v => { v with q := nextQ v }) (TM2.Stmt.goto fun _ => Lbl.sim))
    (scanV v Rs) [] [] [] Ls Rs
  refine ⟨o, ?_⟩
  rw [show ({ v with scanned := fun i => top (Rs i) } : Var R A τi τo) = scanV v Rs from rfl, ho]
  rfl

/-! ## Output phases -/

lemma gather_run (l : List (G R)) : ∀ (v : Var R A τi τo) (Ls Rs), Ls 0 = l →
    ∃ v' : Var R A τi τo, v'.qo = v.qo ∧
      Reaches R A τi τo (l.length + 1) ⟨some .gather, v, mkStk [] [] [] Ls Rs⟩
        ⟨some .seek, v', mkStk [] [] [] (Function.update Ls 0 [])
          (Function.update Rs 0 (l.reverse ++ Rs 0))⟩ := by
  induction l with
  | nil =>
    intro v Ls Rs hL
    refine ⟨{ v with cell := none }, rfl, reaches_one ?_⟩
    rw [stepF_some]
    have e1 : Function.update Ls 0 [] = Ls := by rw [← hL]; exact Function.update_eq_self _ _
    simp [prog, TM2.stepAux, hL, e1]
  | cons g l ih =>
    intro v Ls Rs hL
    obtain ⟨v', hqo, hr⟩ := ih { v with cell := some g } (Function.update Ls 0 l)
      (Function.update Rs 0 (g :: Rs 0)) (by simp)
    refine ⟨v', hqo, ?_⟩
    have hs : stepF R A τi τo ⟨some .gather, v, mkStk [] [] [] Ls Rs⟩ =
        some ⟨some .gather, { v with cell := some g },
          mkStk [] [] [] (Function.update Ls 0 l) (Function.update Rs 0 (g :: Rs 0))⟩ := by
      rw [stepF_some]
      simp [prog, TM2.stepAux, hL]
    have := reaches_succ hs hr
    simpa [Nat.add_comm] using this

lemma seek_run (pre : List (G R)) : ∀ (v : Var R A τi τo) (Ls Rs) (g : G R) (post : List (G R)),
    (∀ x ∈ pre, x.2 = false) → g.2 = true → Rs 0 = pre ++ g :: post →
    ∃ v' : Var R A τi τo, v'.qo = v.qo ∧ v'.cell = some g ∧
      Reaches R A τi τo (pre.length + 1) ⟨some .seek, v, mkStk [] [] [] Ls Rs⟩
        ⟨some .feed, v', mkStk [] [] [] Ls (Function.update Rs 0 post)⟩ := by
  induction pre with
  | nil =>
    intro v Ls Rs g post _ hg hR
    refine ⟨{ v with cell := some g }, rfl, rfl, reaches_one ?_⟩
    rw [stepF_some]
    simp [prog, TM2.stepAux, hR, hg]
  | cons x pre ih =>
    intro v Ls Rs g post hpre hg hR
    obtain ⟨v', hqo, hc, hr⟩ := ih { v with cell := some x } Ls
      (Function.update Rs 0 (pre ++ g :: post)) g post
      (fun y hy => hpre y (by simp [hy])) hg (by simp)
    refine ⟨v', hqo, hc, ?_⟩
    have hx : x.2 = false := hpre x (by simp)
    have hs : stepF R A τi τo ⟨some .seek, v, mkStk [] [] [] Ls Rs⟩ =
        some ⟨some .seek, { v with cell := some x },
          mkStk [] [] [] Ls (Function.update Rs 0 (pre ++ g :: post))⟩ := by
      rw [stepF_some]
      simp [prog, TM2.stepAux, hR, hx]
    have := reaches_succ hs hr
    simpa [Function.update_idem, Nat.add_comm] using this

variable (R) in
/-- The symbol at position `i` of the layout of `y` as an input. -/
def cellSym (y : List Bool) (i : ℕ) : Sym R := ((y[i]?).map (bitSym R)).getD 0

lemma val_one' : ((1 : Sym R) : ℕ) = 1 := by simp
lemma val_two' : ((2 : Sym R) : ℕ) = 2 := by simp

lemma bitSym_val (b : Bool) : (bitSym R b).val = if b then 2 else 1 := by
  cases b
  · exact val_one'
  · exact val_two'

@[simp] lemma isBit_bitSym (b : Bool) : isBit R (bitSym R b) = true := by
  cases b <;> simp [isBit, bitSym]

@[simp] lemma isBit_zero : isBit R 0 = false := by
  simp only [isBit, Bool.or_eq_false_iff, decide_eq_false_iff_not, Fin.ext_iff, val_one',
    val_two', Fin.val_zero]
  omega

@[simp] lemma bitSym_eq_two (b : Bool) : decide (bitSym R b = 2) = b := by
  have := bitSym_val (R := R) b
  cases b
  · simp only [decide_eq_false_iff_not, Fin.ext_iff, val_two']
    simp only [Bool.false_eq_true, if_false] at this
    omega
  · simp [bitSym]

lemma getD_head_tail (l : List (G R)) (i : ℕ) :
    ((l.head?.getD (g0 R)) :: l.tail).getD i (g0 R) = l.getD i (g0 R) := by
  cases l with
  | nil => cases i <;> simp
  | cons a l => rfl

lemma feed_run (y : List Bool) : ∀ (v : Var R A τi τo) (outR : List A) (Ls Rs),
    (∀ i : ℕ, ((v.cell.getD (g0 R) :: Rs 0).getD i (g0 R)).1 = cellSym R y i) →
    ∃ (v' : Var R A τi τo) (rest : List (G R)), rest.length ≤ (Rs 0).length ∧
      Reaches R A τi τo (y.length + 1) ⟨some .feed, v, mkStk [] outR [] Ls Rs⟩
        ⟨some .outRev, v', mkStk [] ((τo.run v.qo y).reverse ++ outR) [] Ls
          (Function.update Rs 0 rest)⟩ := by
  induction y with
  | nil =>
    intro v outR Ls Rs H
    refine ⟨v, Rs 0, le_rfl, reaches_one ?_⟩
    have h0 := H 0
    simp only [List.getD_cons_zero, cellSym, List.getElem?_nil, Option.map_none,
      Option.getD_none] at h0
    rw [stepF_some]
    simp [prog, TM2.stepAux, h0, OutTransducer.run]
  | cons b y ih =>
    intro v outR Ls Rs H
    have h0 := H 0
    simp only [List.getD_cons_zero, cellSym, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some] at h0
    set v₁ : Var R A τi τo :=
      { v with qo := (τo.δ v.qo b).1, cell := (Rs 0).head? } with hv₁
    have H₁ : ∀ i : ℕ, ((v₁.cell.getD (g0 R) :: (Function.update Rs 0 (Rs 0).tail) 0).getD i
        (g0 R)).1 = cellSym R y i := by
      intro i
      simp only [hv₁, Function.update_self]
      rw [getD_head_tail]
      have := H (i + 1)
      simpa [cellSym] using this
    obtain ⟨v', rest, hrest, hr⟩ := ih v₁ ((τo.δ v.qo b).2.toList ++ outR) Ls
      (Function.update Rs 0 (Rs 0).tail) H₁
    refine ⟨v', rest, ?_, ?_⟩
    · simp only [Function.update_self, List.length_tail] at hrest; omega
    have hs : stepF R A τi τo ⟨some .feed, v, mkStk [] outR [] Ls Rs⟩ =
        some ⟨some .feed, v₁, mkStk [] ((τo.δ v.qo b).2.toList ++ outR) [] Ls
          (Function.update Rs 0 (Rs 0).tail)⟩ := by
      rw [stepF_some]
      have hc : cellBit v = b := by simp [cellBit, h0]
      simp [prog, TM2.stepAux, h0, hc, hv₁]
      cases (τo.δ v.qo b).2 <;> rfl
    have := reaches_succ hs hr
    have e : (τo.run v.qo (b :: y)).reverse ++ outR =
        (τo.run (τo.δ v.qo b).1 y).reverse ++ ((τo.δ v.qo b).2.toList ++ outR) := by
      simp only [OutTransducer.run, List.reverse_append, List.append_assoc]
      cases (τo.δ v.qo b).2 <;> rfl
    rw [e]
    simpa [Nat.add_comm, hv₁, Function.update_idem] using this

lemma outRev_run (l : List A) : ∀ (v : Var R A τi τo) (io : List A) (Ls Rs),
    ∃ v' : Var R A τi τo,
      Reaches R A τi τo (l.length + 1) ⟨some .outRev, v, mkStk io l [] Ls Rs⟩
        ⟨some .clear, v', mkStk (l.reverse ++ io) [] [] Ls Rs⟩ := by
  induction l with
  | nil =>
    intro v io Ls Rs
    refine ⟨{ v with outSym := none }, reaches_one ?_⟩
    rw [stepF_some]
    simp [prog, TM2.stepAux]
  | cons a l ih =>
    intro v io Ls Rs
    obtain ⟨v', hr⟩ := ih { v with outSym := some a } (a :: io) Ls Rs
    refine ⟨v', ?_⟩
    have hs : stepF R A τi τo ⟨some .outRev, v, mkStk io (a :: l) [] Ls Rs⟩ =
        some ⟨some .outRev, { v with outSym := some a }, mkStk (a :: io) l [] Ls Rs⟩ := by
      rw [stepF_some]
      simp [prog, TM2.stepAux]
    have := reaches_succ hs hr
    simpa [Nat.add_comm] using this

/-- Whether some tape stack is nonempty. -/
def anyNe (Ls Rs : Fin (R.tapes + 1) → List (G R)) : Bool :=
  (List.finRange (R.tapes + 1)).any (fun j => !(Ls j).isEmpty || !(Rs j).isEmpty)

lemma step_clear (v : Var R A τi τo) (io : List A) (Ls Rs) :
    stepF R A τi τo ⟨some .clear, v, mkStk io [] [] Ls Rs⟩ =
      some ⟨some (if anyNe Ls Rs then .clear else .done), { v with flag := anyNe Ls Rs },
        mkStk io [] [] (fun i => (Ls i).tail) (fun i => (Rs i).tail)⟩ := by
  rw [stepF_some]
  simp only [prog, TM2.stepAux]
  rw [stepAux_popAll _ (List.nodup_finRange _)]
  simp only [List.mem_finRange, if_true, Bool.false_or]
  cases h : anyNe Ls Rs <;> simp only [anyNe] at h <;> simp [TM2.stepAux, h]

lemma clear_run (io : List A) (m : ℕ) : ∀ (v : Var R A τi τo) (Ls Rs),
    (∀ j, (Ls j).length ≤ m ∧ (Rs j).length ≤ m) →
    ∃ n ≤ m + 1, ∃ v' : Var R A τi τo,
      Reaches R A τi τo n ⟨some .clear, v, mkStk io [] [] Ls Rs⟩
        ⟨some .done, v', mkStk io [] [] (fun _ => []) (fun _ => [])⟩ := by
  induction m with
  | zero =>
    intro v Ls Rs hm
    have hL : ∀ j, Ls j = [] := fun j => List.eq_nil_of_length_eq_zero (by have := (hm j).1; omega)
    have hR : ∀ j, Rs j = [] := fun j => List.eq_nil_of_length_eq_zero (by have := (hm j).2; omega)
    have ha : anyNe Ls Rs = false := by simp [anyNe, hL, hR]
    refine ⟨1, le_rfl, { v with flag := false }, reaches_one ?_⟩
    rw [step_clear, ha]
    simp [hL, hR]
  | succ m ih =>
    intro v Ls Rs hm
    cases hany : anyNe Ls Rs with
    | true =>
      obtain ⟨n, hn, v', hr⟩ := ih { v with flag := true } (fun i => (Ls i).tail)
        (fun i => (Rs i).tail) (fun j => by
          simp only [List.length_tail]; have := hm j; omega)
      refine ⟨n + 1, by omega, v', reaches_succ ?_ hr⟩
      rw [step_clear, hany]
      rfl
    | false =>
      have hall : ∀ j, Ls j = [] ∧ Rs j = [] := by
        intro j
        have := hany
        simp only [anyNe, List.any_eq_false, List.mem_finRange, true_implies, Bool.or_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, not_or,
          ne_eq, not_not] at this
        simpa using this j
      refine ⟨1, by omega, { v with flag := false }, reaches_one ?_⟩
      rw [step_clear, hany]
      simp [hall]

lemma step_done (v : Var R A τi τo) (S : ∀ k, List (Γ' R A k)) :
    stepF R A τi τo ⟨some .done, v, S⟩ = some ⟨none, Var.init R A τi τo, S⟩ := by
  rw [stepF_some]
  simp [prog, TM2.stepAux]

end Lax119563Proofs.Bridges.TM2Sim

end Bridges_TM2Sim_Phases

/-! ### Formerly `Lax119563Proofs.Bridges.TM2Sim.TapeRep` -/

section Bridges_TM2Sim_TapeRep

/-!
# Simulating archive multitape machines by mathlib stack machines: tape representation

A tape with head `h` and cells `cells` is represented by stacks `L`, `Rl` when
`cells (h + i)` is the symbol of entry `i` of `Rl` and `cells (h - 1 - i)` that of entry `i`
of `L` (missing entries are blank). On tape `0` the flags mark position `0`, which lies in the
explicitly stored range (`OriginRep`). Both are preserved by `applyTape`.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction)

namespace Lax119563Proofs.Bridges.TM2Sim

variable {R : Machine}

/-- Stacks `L`, `Rl` represent the tape with head `h` and cells `cells`. -/
def TapeRep (h : ℤ) (cells : ℤ → Sym R) (L Rl : List (G R)) : Prop :=
  (∀ i : ℕ, cells (h + i) = (Rl.getD i (g0 R)).1) ∧
    (∀ i : ℕ, cells (h - 1 - i) = (L.getD i (g0 R)).1)

/-- The flags of `L`, `Rl` mark position `0`, and position `0` is stored. -/
def OriginRep (h : ℤ) (L Rl : List (G R)) : Prop :=
  (∀ i (hi : i < Rl.length), (Rl[i]).2 = decide (h + i = 0)) ∧
    (∀ i (hi : i < L.length), (L[i]).2 = decide (h - 1 - i = 0)) ∧
    h - L.length ≤ 0 ∧ 0 < h + Rl.length

lemma getD_tail (l : List (G R)) (i : ℕ) : l.tail.getD i (g0 R) = l.getD (i + 1) (g0 R) := by
  cases l <;> simp

lemma getD_head (l : List (G R)) : l.head?.getD (g0 R) = l.getD 0 (g0 R) := by
  cases l <;> simp

lemma applyTape_rep {h : ℤ} {cells : ℤ → Sym R} {L Rl : List (G R)} (H : TapeRep h cells L Rl)
    (w : Sym R) (m : Move) :
    TapeRep (h + m.offset) (fun z => if z = h then w else cells z)
      (applyTape L Rl w m).1 (applyTape L Rl w m).2 := by
  obtain ⟨H1, H2⟩ := H
  cases m with
  | right =>
    rw [show Move.right.offset = 1 from rfl]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [applyTape]
      rw [if_neg (by omega), getD_tail]
      have := H1 (i + 1); push_cast at this; rw [← this]; congr 1; omega
    · simp only [applyTape]
      rcases i with _ | i
      · simp
      · rw [if_neg (by omega)]
        simp only [List.getD_cons_succ]
        have := H2 i; rw [← this]; congr 1 <;> push_cast <;> omega
  | stay =>
    rw [show Move.stay.offset = 0 from rfl]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [applyTape]
      rcases i with _ | i
      · simp
      · rw [if_neg (by omega)]
        simp only [List.getD_cons_succ, getD_tail]
        have := H1 (i + 1); rw [← this]; congr 1 <;> push_cast <;> omega
    · simp only [applyTape]
      rw [if_neg (by omega)]
      have := H2 i; rw [← this]; congr 1; omega
  | left =>
    rw [show Move.left.offset = -1 from rfl]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [applyTape]
      rcases i with _ | _ | i
      · rw [if_neg (by omega)]
        simp only [List.getD_cons_zero, getD_head]
        have := H2 0; rw [← this]; congr 1
      · simp
      · rw [if_neg (by omega)]
        simp only [List.getD_cons_succ, getD_tail]
        have := H1 (i + 1); rw [← this]; congr 1 <;> push_cast <;> omega
    · simp only [applyTape]
      rw [if_neg (by omega), getD_tail]
      have := H2 (i + 1); rw [← this]; congr 1 <;> push_cast <;> omega

lemma applyTape_length (L Rl : List (G R)) (w : Sym R) (m : Move) :
    (applyTape L Rl w m).1.length + (applyTape L Rl w m).2.length ≤ L.length + Rl.length + 2 := by
  cases m <;> simp only [applyTape, List.length_cons, List.length_tail] <;> omega

lemma flag_head {h : ℤ} {L Rl : List (G R)} (H : OriginRep h L Rl) :
    (Rl.head?.map Prod.snd).getD false = decide (h = 0) := by
  obtain ⟨H1, -, -, H4⟩ := H
  cases Rl with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero, add_zero] at H4
    simp; omega
  | cons a Rl =>
    have := H1 0 (by simp)
    simpa using this

lemma applyTape_origin {h : ℤ} {L Rl : List (G R)} (H : OriginRep h L Rl)
    (w : Sym R) (m : Move) :
    OriginRep (h + m.offset) (applyTape L Rl w m).1 (applyTape L Rl w m).2 := by
  have hf := flag_head H
  obtain ⟨H1, H2, H3, H4⟩ := H
  cases m with
  | right =>
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
    · simp only [applyTape, List.getElem_tail, Move.offset] at hi ⊢
      rw [H1 (i + 1) (by simp at hi; omega)]
      congr 1; apply propext; push_cast; constructor <;> intro <;> omega
    · simp only [applyTape, Move.offset] at hi ⊢
      rcases i with _ | i
      · simp only [List.getElem_cons_zero, hf]; congr 1; apply propext; constructor <;> intro <;> omega
      · simp only [List.getElem_cons_succ]
        rw [H2 i (by simp at hi; omega)]
        congr 1; apply propext; push_cast; constructor <;> intro <;> omega
    · simp only [applyTape, Move.offset, List.length_cons, List.length_tail]; push_cast
      rcases Rl with _ | ⟨a, Rl⟩ <;> simp at H4 ⊢ <;> omega
    · simp only [applyTape, Move.offset, List.length_tail]
      rcases Rl with _ | ⟨a, Rl⟩
      · simp at H4 hf ⊢; omega
      · simp at H4 ⊢; omega
  | stay =>
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
    · simp only [applyTape, Move.offset] at hi ⊢
      rcases i with _ | i
      · simp only [List.getElem_cons_zero, hf]; congr 1; apply propext; constructor <;> intro <;> omega
      · simp only [List.getElem_cons_succ, List.getElem_tail]
        rw [H1 (i + 1) (by simp at hi; omega)]
        congr 1; apply propext; push_cast; constructor <;> intro <;> omega
    · simp only [applyTape, Move.offset] at hi ⊢
      rw [H2 i hi]; congr 1; apply propext; constructor <;> intro <;> omega
    · simp only [applyTape, Move.offset]; omega
    · simp only [applyTape, Move.offset, List.length_cons, List.length_tail]; push_cast
      rcases Rl with _ | ⟨a, Rl⟩ <;> simp at H4 ⊢ <;> omega
  | left =>
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
    · simp only [applyTape, Move.offset] at hi ⊢
      rcases i with _ | _ | i
      · simp only [List.getElem_cons_zero]
        rcases L with _ | ⟨a, L⟩
        · simp only [List.length_nil, Nat.cast_zero, sub_zero] at H3
          simp [g0]; omega
        · have := H2 0 (by simp)
          simp only [List.head?_cons, Option.getD_some]
          simp at this ⊢; rw [this]; constructor <;> intro <;> omega
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, hf]
        congr 1; apply propext; constructor <;> intro <;> omega
      · simp only [List.getElem_cons_succ, List.getElem_tail]
        rw [H1 (i + 1) (by simp at hi; omega)]
        congr 1; apply propext; push_cast; constructor <;> intro <;> omega
    · simp only [applyTape, List.getElem_tail, Move.offset] at hi ⊢
      rw [H2 (i + 1) (by simp at hi; omega)]
      congr 1; apply propext; push_cast; constructor <;> intro <;> omega
    · simp only [applyTape, Move.offset, List.length_tail]
      rcases L with _ | ⟨a, L⟩
      · simp at H3 ⊢; omega
      · simp at H3 ⊢; omega
    · simp only [applyTape, Move.offset, List.length_cons, List.length_tail]; push_cast
      rcases Rl with _ | ⟨a, Rl⟩ <;> simp at H4 ⊢ <;> omega

/-! ## The whole explicitly stored part of a tape -/

lemma gathered_rep {h : ℤ} {cells : ℤ → Sym R} {L Rl : List (G R)} (H : TapeRep h cells L Rl)
    (i : ℕ) : cells (h - L.length + i) = ((L.reverse ++ Rl).getD i (g0 R)).1 := by
  obtain ⟨H1, H2⟩ := H
  by_cases hi : i < L.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi),
      List.getElem?_reverse hi]
    have := H2 (L.length - 1 - i)
    rw [List.getD_eq_getElem?_getD] at this
    rw [← this]; congr 1; push_cast [Nat.sub_sub, Nat.cast_sub (show 1 + i ≤ L.length by omega)]
    ring
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    have := H1 (i - L.length)
    rw [List.getD_eq_getElem?_getD] at this
    simp only [List.length_reverse]
    rw [← this]; congr 1; push_cast [Nat.cast_sub (show L.length ≤ i by omega)]; ring

lemma gathered_origin {h : ℤ} {L Rl : List (G R)} (H : OriginRep h L Rl)
    (i : ℕ) (hi : i < (L.reverse ++ Rl).length) :
    ((L.reverse ++ Rl)[i]).2 = decide (h - L.length + i = 0) := by
  obtain ⟨H1, H2, -, -⟩ := H
  by_cases hiL : i < L.length
  · rw [List.getElem_append_left (by simpa using hiL), List.getElem_reverse]
    rw [H2 _ (by omega)]
    congr 1; apply propext; push_cast [Nat.sub_sub, Nat.cast_sub (show 1 + i ≤ L.length by omega)]
    constructor <;> intro <;> omega
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_reverse]
    rw [H1 _ (by simp at hi; omega)]
    congr 1; apply propext; push_cast [Nat.cast_sub (show L.length ≤ i by omega)]
    constructor <;> intro <;> omega

end Lax119563Proofs.Bridges.TM2Sim

end Bridges_TM2Sim_TapeRep
