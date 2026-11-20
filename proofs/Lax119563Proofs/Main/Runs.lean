import Lax119563.DeterministicTime

/-!
# Elementary facts about deterministic runs

Runs evaluated with the constant coin `false`: unfolding from the end, persistence of a
halted configuration, and monotonicity of `DecidesExactlyWithin` in the time bound.
-/

open Lax489179.TuringMachine (Machine Config step run init)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Main

theorem run_false_succ (M : Machine) (t : ℕ) (c : Config M) :
    run M (t + 1) (fun _ => false) c = step M false (run M t (fun _ => false) c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    show run M (t + 1) (fun _ => false) (step M false c) = _
    rw [ih]; rfl

theorem run_false_add (M : Machine) (a b : ℕ) (c : Config M) :
    run M (a + b) (fun _ => false) c =
      run M b (fun _ => false) (run M a (fun _ => false) c) := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, run_false_succ, ih, run_false_succ]

theorem run_false_of_halted (M : Machine) (t : ℕ) (c : Config M) (h : c.answer.isSome) :
    run M t (fun _ => false) c = c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_false_succ, ih]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    simp [step, hb]

theorem runOn_succ (M : Machine) (x : List Bool) (t : ℕ) :
    runOn M x (t + 1) = step M false (runOn M x t) :=
  run_false_succ M t _

/-- Once halted, a run stays in the same configuration. -/
theorem runOn_eq_of_le (M : Machine) (x : List Bool) {t t' : ℕ} (htt : t ≤ t')
    (h : (runOn M x t).answer.isSome) : runOn M x t' = runOn M x t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htt
  unfold runOn
  rw [run_false_add]
  exact run_false_of_halted M d _ h

theorem decidesWithin_mono {M : Machine} {x : List Bool} {P : Prop} {t t' : ℕ}
    (h : DecidesExactlyWithin M x P t) (htt : t ≤ t') : DecidesExactlyWithin M x P t' := by
  obtain ⟨b, hb, hP⟩ := h
  refine ⟨b, ?_, hP⟩
  rw [runOn_eq_of_le M x htt (by simp [hb]), hb]

/-- A machine that decides `P` within some time accepts exactly when `P` holds. -/
theorem accepts_iff_of_decidesWithin {M : Machine} {x : List Bool} {P : Prop} {t : ℕ}
    (h : DecidesExactlyWithin M x P t) : Accepts M x ↔ P := by
  obtain ⟨b, hb, hP⟩ := h
  constructor
  · rintro ⟨t', ht'⟩
    have key : runOn M x (max t t') = runOn M x t :=
      runOn_eq_of_le M x (le_max_left _ _) (by simp [hb])
    have key' : runOn M x (max t t') = runOn M x t' :=
      runOn_eq_of_le M x (le_max_right _ _) (by simp [ht'])
    have e := congrArg Config.answer (key.symm.trans key')
    rw [hb, ht'] at e
    cases e
    exact hP.mp rfl
  · intro hp
    exact ⟨t, by rw [hb, hP.mpr hp]⟩

end Lax119563Proofs.Main
