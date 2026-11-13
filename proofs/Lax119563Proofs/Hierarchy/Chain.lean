import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lax119563Proofs.Hierarchy.Run

/-!
# The translational argument

From a coarse hierarchy (`DTIME(n^B) ⊄ DTIME(n^b)` for some `B` depending on `b`), padding,
and the linear case, we derive the hierarchy theorem for all exponents `a < s`.
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime

namespace Lax119563Proofs.Hierarchy

/-- `L ∈ DTIME(n^α)` for a real exponent `α`. -/
def DT (L : Set (List Bool)) (α : ℝ) : Prop :=
  DecidableInTime L (fun n => (n : ℝ) ^ α)

/-- A larger time bound (up to an additive constant) gives a larger class. -/
lemma decidableInTime_mono {L : Set (List Bool)} {f g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n)
    (hfg : ∀ n, f n ≤ g n + 1) (h : DecidableInTime L f) : DecidableInTime L g := by
  obtain ⟨M, hM, C, hC⟩ := h
  refine ⟨M, hM, 2 * C, fun x => decidesWithin_mono (hC x) ?_⟩
  apply Nat.floor_le_floor
  have h1 := hfg x.length
  have h2 := hg x.length
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  push_cast
  nlinarith

lemma rpow_le_rpow_add_one {α β : ℝ} (h : α ≤ β) (n : ℕ) :
    (n : ℝ) ^ α ≤ (n : ℝ) ^ β + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := Real.zero_rpow_le_one α
    have : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ β := Real.rpow_nonneg (by simp) β
    simp only [Nat.cast_zero] at *
    linarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have := Real.rpow_le_rpow_of_exponent_le this h
    linarith

lemma DT.mono {L : Set (List Bool)} {α β : ℝ} (h : α ≤ β) (hL : DT L α) : DT L β :=
  decidableInTime_mono (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) β)
    (rpow_le_rpow_add_one h) hL

lemma dt_natCast_iff (L : Set (List Bool)) (s : ℕ) :
    DT L (s : ℝ) ↔ DecidableInTime L (fun n => (n : ℝ) ^ s) := by
  simp only [DT, Real.rpow_natCast]

/-- The translational argument proper. -/
theorem chain (s : ℕ) (a : ℝ) (ha : 1 ≤ a) (has : a < s)
    (pad : ∀ r : ℕ, 1 ≤ r → ∀ L, DT L ((s : ℝ) * r) →
      ∃ L', DT L' (s : ℝ) ∧ (DT L' a → DT L (a * r)))
    (coarse : ∀ b : ℕ, ∃ B : ℕ, ∃ L, DT L (B : ℝ) ∧ ¬ DT L (b : ℝ)) :
    ∃ L, DT L (s : ℝ) ∧ ¬ DT L a := by
  by_contra hne
  push Not at hne
  have hs : (0 : ℝ) < s := by linarith
  have hsa : (0 : ℝ) < s - a := by linarith
  -- one translation step
  have step : ∀ r : ℕ, 1 ≤ r → ∀ L, DT L ((s : ℝ) * r) → DT L (a * r) := by
    intro r hr L hL
    obtain ⟨L', h1, h2⟩ := pad r hr L hL
    exact h2 (hne L' h1)
  set R : ℕ := ⌈(s : ℝ) / (s - a)⌉₊ with hR
  have hRge : (s : ℝ) / (s - a) ≤ R := Nat.le_ceil _
  have collapse : ∀ r : ℕ, ∀ L, DT L ((s : ℝ) * r) → DT L ((s : ℝ) * R) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro L hL
      by_cases hrR : r ≤ R
      · exact hL.mono (by gcongr)
      · push Not at hrR
        have hr1 : 1 ≤ r := by
          have : (0 : ℝ) < s / (s - a) := div_pos hs hsa
          have : (0 : ℝ) < R := lt_of_lt_of_le this hRge
          have : 0 < R := by exact_mod_cast this
          omega
        have h1 := step r hr1 L hL
        set r' : ℕ := ⌈a * r / s⌉₊ with hr'
        have hr'ge : a * r / s ≤ r' := Nat.le_ceil _
        have hle : a * r ≤ (s : ℝ) * r' := by
          rw [div_le_iff₀ hs] at hr'ge; linarith
        have hr'lt : r' < r := by
          have hrR' : (s : ℝ) / (s - a) < r := lt_of_le_of_lt hRge (by exact_mod_cast hrR)
          rw [div_lt_iff₀ hsa] at hrR'
          have : a * r / s ≤ ((r - 1 : ℕ) : ℝ) := by
            rw [div_le_iff₀ hs]
            push_cast [hr1]
            nlinarith
          have := Nat.ceil_le.mpr this
          omega
        exact ih r' hr'lt L (h1.mono hle)
  obtain ⟨B, L, hB, hnot⟩ := coarse (s * R)
  apply hnot
  have h1 : DT L ((s : ℝ) * B) := hB.mono (by
    have : (1 : ℝ) ≤ s := by linarith
    have : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    nlinarith)
  have := collapse B L h1
  push_cast
  exact this

/-- The hierarchy theorem from its three ingredients. -/
theorem hierarchy_of
    (pad : ∀ (s : ℕ) (a : ℝ), 1 ≤ s → 1 ≤ a → ∀ r : ℕ, 1 ≤ r → ∀ L, DT L ((s : ℝ) * r) →
      ∃ L', DT L' (s : ℝ) ∧ (DT L' a → DT L (a * r)))
    (coarse : ∀ b : ℕ, ∃ B : ℕ, ∃ L, DT L (B : ℝ) ∧ ¬ DT L (b : ℝ))
    (lin : ∀ a : ℝ, a < 1 → ∃ L, DT L 1 ∧ ¬ DT L a)
    (s : ℕ) (hs : 1 ≤ s) (a : ℝ) (ha : a < s) :
    ∃ L : Set (List Bool),
      DecidableInTime L (fun n => (n : ℝ) ^ s) ∧ ¬ DecidableInTime L (fun n => (n : ℝ) ^ a) := by
  rcases Nat.eq_or_lt_of_le hs with rfl | hs2
  · obtain ⟨L, h1, h2⟩ := lin a (by exact_mod_cast ha)
    refine ⟨L, (dt_natCast_iff L 1).mp (by exact_mod_cast h1), h2⟩
  · set a' := max a ((s : ℝ) - 1 / 2) with ha'
    have hs2' : (2 : ℝ) ≤ s := by exact_mod_cast hs2
    have h1 : 1 ≤ a' := le_trans (by linarith) (le_max_right _ _)
    have h2 : a' < s := max_lt ha (by linarith)
    obtain ⟨L, hL1, hL2⟩ := chain s a' h1 h2 (fun r hr L hL => pad s a' hs h1 r hr L hL) coarse
    refine ⟨L, (dt_natCast_iff L s).mp hL1, fun h => hL2 (DT.mono (le_max_left _ _) h)⟩

end Lax119563Proofs.Hierarchy
