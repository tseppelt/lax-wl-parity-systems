import Lax119563.DeterministicTime

/-!
# Basic facts about deterministic runs

Runs evaluated with the constant coin `false`, monotonicity of halting, and per-tape
translation invariance of runs.
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime

namespace Lax119563Proofs.Hierarchy

/-- The run of `M` for `t` steps from `c` with the constant coin `false`. -/
def drun (M : Machine) (t : ℕ) (c : Config M) : Config M :=
  run M t (fun _ => false) c

@[simp] lemma drun_zero (M : Machine) (c : Config M) : drun M 0 c = c := rfl

lemma drun_succ (M : Machine) (t : ℕ) (c : Config M) :
    drun M (t + 1) c = drun M t (step M false c) := rfl

lemma drun_add (M : Machine) (t₁ t₂ : ℕ) (c : Config M) :
    drun M (t₁ + t₂) c = drun M t₂ (drun M t₁ c) := by
  induction t₁ generalizing c with
  | zero => simp
  | succ t ih =>
    rw [show t + 1 + t₂ = (t + t₂) + 1 by omega, drun_succ, ih, drun_succ]

lemma runOn_eq_drun (M : Machine) (x : List Bool) (t : ℕ) :
    runOn M x t = drun M t (init M x) := rfl

lemma step_of_answer {M : Machine} {c : Config M} {b : Bool} (h : c.answer = some b)
    (coin : Bool) : step M coin c = c := by
  simp [step, h]

lemma drun_of_answer {M : Machine} {c : Config M} {b : Bool} (h : c.answer = some b)
    (t : ℕ) : drun M t c = c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [drun_succ, step_of_answer h, ih]

/-- Once an answer is present it stays. -/
lemma drun_answer_mono {M : Machine} {c : Config M} {t t' : ℕ} {b : Bool}
    (h : (drun M t c).answer = some b) (ht : t ≤ t') : (drun M t' c).answer = some b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [drun_add, drun_of_answer h]
  exact h

lemma decidesWithin_mono {M : Machine} {x : List Bool} {P : Prop} {t t' : ℕ}
    (h : Lax119563.DeterministicTime.DecidesExactlyWithin M x P t) (ht : t ≤ t') :
    Lax119563.DeterministicTime.DecidesExactlyWithin M x P t' := by
  obtain ⟨b, hb, hP⟩ := h
  exact ⟨b, drun_answer_mono hb ht, hP⟩

/-! ## Translation invariance -/

/-- Shift every tape `j` (contents and head) by `δ j`. -/
def shiftC {M : Machine} (δ : Fin (M.tapes + 1) → ℤ) (c : Config M) : Config M where
  state := c.state
  head j := c.head j + δ j
  tape j z := c.tape j (z - δ j)
  answer := c.answer

lemma step_shiftC {M : Machine} (δ : Fin (M.tapes + 1) → ℤ) (coin : Bool) (c : Config M) :
    step M coin (shiftC δ c) = shiftC δ (step M coin c) := by
  have hread : (fun j => (shiftC δ c).tape j ((shiftC δ c).head j)) =
      fun j => c.tape j (c.head j) := by
    funext j; simp [shiftC]
  unfold step
  rcases hc : c.answer with _ | b
  · have : (shiftC δ c).answer = none := hc
    simp only [this]
    rw [show (shiftC δ c).state = c.state from rfl, hread]
    rcases M.transition c.state (fun j => c.tape j (c.head j)) coin with b | ⟨q, w, mv⟩
    · rfl
    · simp only [shiftC, Config.mk.injEq, true_and]
      refine ⟨?_, ?_, trivial⟩
      · funext j; ring
      · funext j z
        by_cases h : z = c.head j + δ j
        · have : z - δ j = c.head j := by omega
          simp [h, this]
        · have : z - δ j ≠ c.head j := by omega
          simp [h, this]
  · have : (shiftC δ c).answer = some b := hc
    simp [this]

lemma drun_shiftC {M : Machine} (δ : Fin (M.tapes + 1) → ℤ) (t : ℕ) (c : Config M) :
    drun M t (shiftC δ c) = shiftC δ (drun M t c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih => rw [drun_succ, step_shiftC, ih, drun_succ]

@[simp] lemma shiftC_answer {M : Machine} (δ : Fin (M.tapes + 1) → ℤ) (c : Config M) :
    (shiftC δ c).answer = c.answer := rfl

end Lax119563Proofs.Hierarchy
