import Lax119563Proofs.Hierarchy.UnivInit
import Lax119563Proofs.Hierarchy.Glue

/-!
# Correctness of the universal simulator

If `M` halts on `code M ++ z` within `t` steps with answer `b`, the simulator, run on the same
input, halts with answer `!b` after a number of steps polynomial in the input length and `t`.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog Function Lax489179.TuringMachine Lax119563.DeterministicTime

lemma stepCost_mono {Z Z' : ℕ} (h : Z ≤ Z') : stepCost Z ≤ stepCost Z' := by
  unfold stepCost; gcongr

/-- The main loop. -/
def mainLoop : SProg := loop (isEmpty DONE) simStep

theorem mainLoop_runs {M : Machine} {b : Bool} :
    ∀ (t : ℕ) (c : Config M) (s : Stacks 16 13), Rel M c s → (drun M t c).answer = some b →
      ∃ s', mainLoop.RunsLe s s'
          (t * (stepCost (recSize s + (t + 1) * (table M).length) + 1) + 2) ∧
        s' DONE = [haltTok b]
  | 0, c, s, hR, h => by simp [hR.1] at h
  | t + 1, c, s, hR, h => by
    have hD : s DONE = [] := by
      obtain ⟨-, _, _, -, -, -, -, -, h0⟩ := hR
      exact h0 DONE (by decide) (by decide) (by decide) (by decide)
    have hc : isEmpty DONE (tops s) = true := by simp [tops, isEmpty, hD]
    rw [drun_succ] at h
    rcases htr : M.transition c.state (fun j => c.tape j (c.head j)) false with b' | ⟨q', w, mv⟩
    · have hs : step M false c = { c with answer := some b' } := by
        simp [Lax489179.TuringMachine.step, hR.1, htr]
      rw [hs, drun_of_answer rfl] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨s', h1, hd⟩ := simStep_halt hR htr
      have h2 := RunsLe.loopF (c := isEmpty DONE) (p := simStep) (s := s')
        (by simp [tops, isEmpty, hd])
      refine ⟨s', (RunsLe.loopT hc h1 h2).mono ?_, hd⟩
      have := stepCost_mono (show recSize s + (table M).length ≤
        recSize s + (t + 1 + 1) * (table M).length by nlinarith)
      nlinarith
    · obtain ⟨s₁, h1, hR₁, hsz⟩ := simStep_next hR htr
      obtain ⟨s', h2, hd⟩ := mainLoop_runs t _ s₁ hR₁ h
      refine ⟨s', (RunsLe.loopT hc h1 h2).mono ?_, hd⟩
      have e1 := stepCost_mono (show recSize s + (table M).length ≤
        recSize s + (t + 1 + 1) * (table M).length by nlinarith)
      have e2 := stepCost_mono (show recSize s₁ + (t + 1) * (table M).length ≤
        recSize s + (t + 1 + 1) * (table M).length by nlinarith)
      have e3 := Nat.mul_le_mul_left t (Nat.add_le_add_right e2 1)
      nlinarith

/-- The simulator as a machine of the model. -/
noncomputable def simMachine : Machine := Prog.toMachine sim simAns

lemma simMachine_deterministic : Deterministic simMachine := Prog.toMachine_deterministic _ _

/-- The running time bound of the simulator. -/
def simTime (n T t : ℕ) : ℕ := 1000 * (n + 1) + (t * (stepCost (5 * (n + 1) + (t + 1) * T) + 1) + 2) + 1

theorem simMachine_answer {M : Machine} {z : List Bool} {t : ℕ} {b : Bool}
    (h : (runOn M (code M ++ z) t).answer = some b) :
    (runOn simMachine (code M ++ z) (simTime (code M ++ z).length (table M).length t)).answer =
      some !b := by
  obtain ⟨s₁, ⟨t₁, ht₁, h₁⟩, hR, hsz⟩ := init_runs M z
  obtain ⟨s', ⟨t₂, ht₂, h₂⟩, hd⟩ := mainLoop_runs t _ s₁ hR h
  have := Prog.toMachine_answer (ans := simAns) (Runs.seq h₁ h₂)
  have hans : simAns (tops s') = !b := by
    cases b <;> simp [simAns, tops, hd, haltTok]
  rw [hans] at this
  refine drun_answer_mono this ?_
  have e := stepCost_mono (show recSize s₁ + (t + 1) * (table M).length ≤
    5 * ((code M ++ z).length + 1) + (t + 1) * (table M).length by omega)
  have e' := Nat.mul_le_mul_left t (Nat.add_le_add_right e 1)
  simp only [simTime]
  omega

end Lax119563Proofs.Hierarchy.Universal
