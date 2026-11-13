import Lax119563.RuntimeLowerBound
import Lax119563.TimeHierarchy
import Lax119563.TimeReduction
import Lax119563Proofs.Main.Asymptotics
import Lax119563Proofs.Main.ComposeMain

/-!
# The unconditional time lower bound for k-WL Distinguishing

Put `s = k - 1`. By the time hierarchy theorem there is a language `L` decidable in time
`O(n^s)` but not in time `O(n^{s - ε/2})`. Composing the quasi-linear reduction from
`DTIME(n^s)` to `k`-WL Distinguishing with a hypothetical `O(N^{k-1-ε})` decider yields a
decider for `L` running in time `O(n^{s - ε/2})`, a contradiction.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Main

/-- Lowering the exponent `k - 1 - ε` to `k - 1 - min ε 1` costs a factor `2`. -/
theorem floor_rpow_le_floor (C N : ℕ) {e₁ e₂ : ℝ} (he : e₁ ≤ e₂) :
    ⌊(C : ℝ) * (N : ℝ) ^ e₁ + C⌋₊ ≤ ⌊((2 * C : ℕ) : ℝ) * (N : ℝ) ^ e₂ + (2 * C : ℕ)⌋₊ := by
  apply Nat.floor_le_floor
  have hpow : (N : ℝ) ^ e₁ ≤ (N : ℝ) ^ e₂ + 1 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have := Real.rpow_nonneg (le_refl (0 : ℝ)) e₂
      have := Real.zero_rpow_le_one e₁
      push_cast
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1 : ℝ) ≤ N) he
      linarith
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hN := Real.rpow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) e₂
  push_cast
  nlinarith

/--
---
conclusion: Lax119563.RuntimeLowerBound.runtime_lower_bound
---
For `k ≥ 3` and `ε > 0`, assume a deterministic machine decides `k`-WL distinguishability
within `C N^{k-1-ε} + C` steps. With `s = k - 1` and `ε' = min ε 1`, the time hierarchy
theorem gives a language `L ∈ DTIME(n^s) \ DTIME(n^{s - ε'/2})`. The reduction maps inputs of
length `n ≥ 2` in time `t₁ = O(n log^c n)` to graph pairs with `N ≤ t₁` vertices that `k`-WL
distinguishes exactly for members of `L`. Running the reduction, rewinding, and then the
fast decider (and answering inputs of length `< 2` directly) decides `L` within
`2 t₁ + O(t₁^{k-1-ε'}) + O(1) = O(n^{s - ε'/2})` steps, contradicting the choice of `L`.
-/
theorem runtime_lower_bound (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ M : Machine, Deterministic M ∧ ∃ C : ℕ, ∀ G H : ColoredGraph,
      DecidesWithin M (encodeGraphPair G H) (Distinguishes k G H)
        ⌊C * ((G.n + H.n : ℕ) : ℝ) ^ ((k : ℝ) - 1 - ε) + C⌋₊ := by
  classical
  rintro ⟨W, -, C, hW⟩
  set ε' : ℝ := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'le : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  set e : ℝ := (k : ℝ) - 1 - ε' with he_def
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have he : 1 ≤ e := by rw [he_def]; linarith
  -- the fast decider, with the exponent `e`
  have hW' : ∀ G H : ColoredGraph, DecidesWithin W (encodeGraphPair G H) (Distinguishes k G H)
      ⌊((2 * C : ℕ) : ℝ) * ((G.n + H.n : ℕ) : ℝ) ^ e + (2 * C : ℕ)⌋₊ := fun G H =>
    decidesWithin_mono (hW G H) (floor_rpow_le_floor C _ (by rw [he_def]; linarith))
  -- the hierarchy language
  set s : ℕ := k - 1 with hs_def
  have hs_cast : (s : ℝ) = k - 1 := by rw [hs_def, Nat.cast_sub (by omega)]; simp
  set a : ℝ := e + ε' / 2 with ha_def
  have ha : a < s := by rw [ha_def, he_def, hs_cast]; linarith
  obtain ⟨L, ⟨ML, hMLdet, CL, hL⟩, hnot⟩ :=
    Lax119563.TimeHierarchy.time_hierarchy s (by omega) a ha
  obtain ⟨c, hred⟩ := Lax119563.TimeReduction.time_reduction
  have hML_halt : ∃ C₀ : ℕ, ∀ x : List Bool,
      (runOn ML x (C₀ * x.length ^ s + C₀)).answer.isSome := by
    refine ⟨CL, fun x => ?_⟩
    obtain ⟨b, hb, -⟩ := hL x
    have hfl : ⌊(CL : ℝ) * ((x.length : ℝ)) ^ s + CL⌋₊ = CL * x.length ^ s + CL := by
      rw [show (CL : ℝ) * ((x.length : ℝ)) ^ s + CL = ((CL * x.length ^ s + CL : ℕ) : ℝ) by
        push_cast; ring]
      exact Nat.floor_natCast _
    rw [hfl] at hb
    simp [hb]
  obtain ⟨Rm, -, CR, hR⟩ := hred s (by omega) ML hMLdet hML_halt
  obtain ⟨K, hK⟩ := composed_time_estimate CR c (2 * C) e (ε' / 2) he (by positivity)
  apply hnot
  refine ⟨(Compose.comp Rm W (decide ([] ∈ L)) (fun b => decide ([b] ∈ L))).toMachine,
    AMachine.toMachine_deterministic _, K + 2, fun x => ?_⟩
  have hpow0 : (0 : ℝ) ≤ (x.length : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg _) a
  by_cases hx : 2 ≤ x.length
  · obtain ⟨G₀, G₁, hacc, hsize, hcomp⟩ := hR x hx
    have hks : s + 1 = k := by omega
    rw [hks, accepts_iff_of_decidesWithin (hL x)] at hacc
    have hD : DecidesWithin W (encodeGraphPair G₀ G₁) (x ∈ L)
        ⌊((2 * C : ℕ) : ℝ) * ((G₀.n + G₁.n : ℕ) : ℝ) ^ e + (2 * C : ℕ)⌋₊ := by
      obtain ⟨b, hb, hP⟩ := hW' G₀ G₁
      exact ⟨b, hb, hP.trans hacc.symm⟩
    refine decidesWithin_mono (Compose.compose_decidesWithin Rm W _ _ hx hcomp hD) ?_
    apply Nat.le_floor
    set t₁ : ℕ := CR * x.length * Nat.log 2 x.length ^ c with ht₁
    have hNt : ((G₀.n + G₁.n : ℕ) : ℝ) ^ e ≤ (t₁ : ℝ) ^ e :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hsize) (by linarith)
    have ht₂ := Nat.floor_le (a := ((2 * C : ℕ) : ℝ) * ((G₀.n + G₁.n : ℕ) : ℝ) ^ e +
      (2 * C : ℕ)) (by positivity)
    have hKx := hK x.length (by omega)
    rw [← ha_def, ← ht₁] at hKx
    have h2C : (0 : ℝ) ≤ ((2 * C : ℕ) : ℝ) := Nat.cast_nonneg _
    have : ((2 * C : ℕ) : ℝ) * ((G₀.n + G₁.n : ℕ) : ℝ) ^ e ≤ ((2 * C : ℕ) : ℝ) * (t₁ : ℝ) ^ e :=
      mul_le_mul_of_nonneg_left hNt h2C
    push_cast at ht₂ hKx this ⊢
    nlinarith
  · refine decidesWithin_mono (Compose.compose_short Rm W (· ∈ L) x (by omega)) ?_
    apply Nat.le_floor
    push_cast
    nlinarith

end Lax119563Proofs.Main
