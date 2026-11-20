import Mathlib
import Lax119563.PebbleGame

/-!
# Generic facts about the bijective pebble game

* survival is antitone in the number of rounds;
* `Forces c S P`: from `S`, Spoiler can force within `c` rounds a state satisfying `P`
  (unless he wins earlier); this composes like a monad and turns into Spoiler wins;
* the basic Spoiler move: lift a pebble and place it on a chosen vertex of `G`.
-/

open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Matrix

variable {m : ℕ} {G H : ColoredGraph}

lemma survivesFrom_succ {r : ℕ} {S : GameState m G H} (h : SurvivesFrom G H (r + 1) S) :
    SurvivesFrom G H r S := by
  induction r generalizing S with
  | zero => trivial
  | succ r ih =>
    intro i
    obtain ⟨f, hf⟩ := h i
    exact ⟨f, fun p => ⟨(hf p).1, ih (hf p).2⟩⟩

lemma survivesFrom_mono {r r' : ℕ} (hr : r ≤ r') {S : GameState m G H}
    (h : SurvivesFrom G H r' S) : SurvivesFrom G H r S := by
  induction hr with
  | refl => exact h
  | step _ ih => exact ih (survivesFrom_succ h)

/-- Spoiler wins from `S` within `r` rounds. -/
def SWins (r : ℕ) (S : GameState m G H) : Prop := ¬ SurvivesFrom G H r S

lemma SWins.mono {r r' : ℕ} (hr : r ≤ r') {S : GameState m G H} (h : SWins r S) :
    SWins r' S := fun h' => h (survivesFrom_mono hr h')

/-- From `S`, Spoiler can force within `c` rounds a state satisfying `P`, or win. -/
def Forces (c : ℕ) (S : GameState m G H) (P : GameState m G H → Prop) : Prop :=
  ∀ r, (∀ S', P S' → SWins r S') → SWins (r + c) S

lemma Forces.ret {S : GameState m G H} {P : GameState m G H → Prop} (h : P S) : Forces 0 S P :=
  fun _ hr => hr S h

lemma Forces.bind {c d : ℕ} {S : GameState m G H} {P Q : GameState m G H → Prop}
    (h : Forces c S P) (h' : ∀ S', P S' → Forces d S' Q) : Forces (c + d) S Q := by
  intro r hr
  have := h (r + d) fun S' hS' => h' S' hS' r hr
  rwa [Nat.add_comm c d, ← Nat.add_assoc]

lemma Forces.mono {c c' : ℕ} (hc : c ≤ c') {S : GameState m G H} {P : GameState m G H → Prop}
    (h : Forces c S P) : Forces c' S P :=
  fun r hr => (h r hr).mono (Nat.add_le_add_left hc r)

lemma Forces.weaken {c : ℕ} {S : GameState m G H} {P Q : GameState m G H → Prop}
    (h : Forces c S P) (hPQ : ∀ S', P S' → Q S') : Forces c S Q :=
  fun r hr => h r fun S' hS' => hr S' (hPQ S' hS')

/-- Spoiler lifts pebble `i` and places it on `p`; Duplicator answers with some `q`, and
unless the result is not a partial isomorphism (a win), the game continues from there. -/
lemma Forces.place (S : GameState m G H) (i : Fin m) (p : Fin G.n) :
    Forces 1 S fun S' => ∃ q, S' = Function.update S i (some (p, q)) ∧ IsPartialIso G H S' := by
  intro r hr hS
  obtain ⟨f, hf⟩ := hS i
  by_cases hpi : IsPartialIso G H (Function.update S i (some (p, f p)))
  · exact hr _ ⟨f p, rfl, hpi⟩ (hf p).2
  · exact hpi (hf p).1

end Lax119563Proofs.Matrix
