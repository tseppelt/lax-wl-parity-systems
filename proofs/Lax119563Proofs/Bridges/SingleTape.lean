import Lax119563.MachineTranslations
import Lax119563Proofs.Machines.Compile
import Lax119563Proofs.Main.Runs

/-!
# From elementary single-tape machines to the multitape model

The archive's class `EXPTIME` (`Lax434930.ExponentialTime.EXPTIME`) is defined with the
elementary single-tape machines `Lax434930.MachineModels.SingleTape`: a mathlib `TM0` machine
over a finite alphabet `Γ` with blank `default`, input bits written as `M₀.input b`, starting
in state `default` on the tape `Tape.mk₁ (w.map M₀.input)`, and answering `M₀.accept q` when
it halts in state `q` (that is, when `TM0.step` returns `none`).

We simulate such a machine step by step by a deterministic machine of the archive model
`Lax489179.TuringMachine` with a single tape, using `M₀.Γ` itself as tape alphabet (blank
`default`, bits `M₀.input`). One `TM0` transition is one transition of the simulating machine,
and halting costs one more step.

Main results:
* `singleTape_simulation_succ`: for every `M₀` there is a deterministic machine `M` (independent of
  the input and the time bound) such that, whenever `M₀` halts on `w` within `T` steps in the
  configuration `c`, `M` decides `M₀.accept c.q = true` within `T + 1` steps.
* `exptime_decidesWithin`: every language in `EXPTIME` is decided by a deterministic machine of
  the archive model within `2 ^ p(|w|) + 1` steps, for a polynomial `p`.
* `Lax119563Proofs.Bridges.singleTape_simulation`: the concept statement
  `Lax119563.MachineTranslations.singleTape_simulation` (with `C = 1`).
-/

open Turing
open Lax434930.MachineModels
open Lax489179.TuringMachine (Machine Config Move Deterministic)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Bridges.SingleTapeSim

open Lax119563Proofs.Machines

open scoped Classical

variable (M₀ : SingleTape)

/-- The tape alphabet of the simulation: the alphabet of `M₀`, with blank `default` and bits
`M₀.input`. -/
@[reducible] def tapeAlphabet : TapeAlphabet M₀.Γ where
  blank := default
  bit := M₀.input
  bit_injective := M₀.input.injective
  bit_ne_blank := M₀.input_ne_blank

attribute [local instance] tapeAlphabet

/-- The head move of a `TM0` direction. -/
def dirMove : Dir → Move
  | .left => .left
  | .right => .right

/-- The action of a `TM0` statement on the scanned symbol `a`. -/
def stmtAction : TM0.Stmt M₀.Γ → M₀.Γ → Action 1 M₀.Γ
  | .move d, a => (fun _ => a, fun _ => dirMove d)
  | .write b, _ => (fun _ => b, fun _ => .stay)

/-- The simulating structured one-tape machine. -/
@[reducible] noncomputable def simTM : TM 1 M₀.Γ :=
  { Q := M₀.Q
    start := default
    δ := fun q s => (M₀.transition q (s 0)).map fun p => (p.1, stmtAction M₀ p.2 (s 0)) }

/-- The simulating machine of the archive model; on halting in state `q` it returns
`M₀.accept q`. -/
noncomputable def simMachine : Machine :=
  (simTM M₀).compileWith fun q _ => M₀.accept q

/-- A structured tape represents a mathlib tape when they agree relative to the head. -/
def Rel (T : Tapes 1 M₀.Γ) (tape : Turing.Tape M₀.Γ) : Prop :=
  ∀ i : ℤ, tape.nth i = (T 0).cells ((T 0).head + i)

lemma Rel.read {T : Tapes 1 M₀.Γ} {tape : Turing.Tape M₀.Γ} (h : Rel M₀ T tape) :
    readAll T 0 = tape.head := by
  have := h 0
  simp only [Tape.nth_zero, add_zero] at this
  rw [this]; rfl

lemma Rel.step {T : Tapes 1 M₀.Γ} {tape : Turing.Tape M₀.Γ} (h : Rel M₀ T tape)
    (s : TM0.Stmt M₀.Γ) :
    Rel M₀ (applyAll T (stmtAction M₀ s tape.head).1 (stmtAction M₀ s tape.head).2)
      (match s with
        | .move d => tape.move d
        | .write a => tape.write a) := by
  have hr := h.read
  intro i
  cases s with
  | move d =>
    have hupd : Function.update (T 0).cells (T 0).head tape.head = (T 0).cells := by
      rw [← hr]; exact Function.update_eq_self _ _
    cases d with
    | left =>
      simp only [applyAll, stmtAction, dirMove, Machines.Tape.act_cells, Machines.Tape.act_head,
        hupd, Tape.move_left_nth, h (i - 1), Move.offset_left]
      congr 1; ring
    | right =>
      simp only [applyAll, stmtAction, dirMove, Machines.Tape.act_cells, Machines.Tape.act_head,
        hupd, Tape.move_right_nth, h (i + 1), Move.offset_right]
      congr 1; ring
  | write a =>
    simp only [applyAll, stmtAction, Machines.Tape.act_cells, Machines.Tape.act_head,
      Tape.write_nth, Move.offset_stay, add_zero, Function.update_apply]
    by_cases hi : i = 0
    · simp [hi]
    · rw [if_neg hi, if_neg (by omega), h i]

/-- The initial tapes represent the initial tape of `M₀`. -/
lemma rel_init (w : List Bool) :
    Rel M₀ (inputTapes 0 w) (TM0.init (w.map M₀.input) : TM0.Cfg M₀.Γ M₀.Q).Tape := by
  intro i
  simp only [TM0.init, inputTapes, zero_add, if_true, listCells]
  show (Tape.mk₁ (w.map M₀.input)).nth i = _
  rcases i with (n | n)
  · simp only [Int.ofNat_eq_natCast, Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk,
      Nat.cast_nonneg, if_true, Int.toNat_natCast]
    rw [List.getI_eq_getElem?_getD]
    rfl
  · rw [if_neg (not_le.mpr (Int.negSucc_lt_zero n))]
    simp only [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', ListBlank.nth_mk]
    rfl

/-- Core simulation: if `M₀` gets from `c₁` to the halting configuration `c` in `n` steps, then
the compiled machine started from the corresponding configuration has returned
`M₀.accept c.q` after any `t ≥ n + 1` steps. -/
lemma run_sim (ans : (simTM M₀).Q → (Fin 1 → M₀.Γ) → Bool) (hans : ∀ q s, ans q s = M₀.accept q)
    (c : TM0.Cfg M₀.Γ M₀.Q) (hc : TM0.step M₀.transition c = none) :
    ∀ (n : ℕ) (c₁ : TM0.Cfg M₀.Γ M₀.Q) (T : Tapes 1 M₀.Γ),
      (flip bind (TM0.step M₀.transition))^[n] (some c₁) = some c → Rel M₀ T c₁.Tape →
      ∀ t, n + 1 ≤ t →
        (Lax489179.TuringMachine.run ((simTM M₀).compileWith ans) t (fun _ => false)
          ((simTM M₀).toConfig ans c₁.q T)).answer = some (M₀.accept c.q) := by
  classical
  intro n
  induction n with
  | zero =>
    intro c₁ T hit hT t ht
    simp only [Function.iterate_zero, id, Option.some.injEq] at hit
    subst hit
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' ht
    have hδ : (simTM M₀).δ c₁.q (readAll T) = none := by
      have hstep := hc
      simp only [TM0.step, Option.map_eq_none_iff] at hstep
      simp only [simTM, Option.map_eq_none_iff]
      rw [hT.read]; exact hstep
    rw [TM.run_succ_false, TM.step_toConfig_none _ _ hδ,
      TM.run_of_answer_isSome _ _ _ (by simp)]
    simp [hans]
  | succ n ih =>
    intro c₁ T hit hT t ht
    rw [Function.iterate_succ_apply] at hit
    cases hs : TM0.step M₀.transition c₁ with
    | none =>
      exfalso
      have : (flip bind (TM0.step M₀.transition)) (some c₁) = none := by
        simp [flip, hs]
      rw [this] at hit
      have hnone : ∀ m, (flip bind (TM0.step M₀.transition))^[m] none = none := by
        intro m; induction m with
        | zero => rfl
        | succ m ihm => rw [Function.iterate_succ_apply]; simpa [flip] using ihm
      rw [hnone] at hit
      simp at hit
    | some c₂ =>
      have h1 : (flip bind (TM0.step M₀.transition)) (some c₁) = some c₂ := by
        simp [flip, hs]
      rw [h1] at hit
      obtain ⟨q₁, tape₁⟩ := c₁
      simp only [TM0.step, Option.map_eq_some_iff] at hs
      obtain ⟨⟨q', s⟩, hq, rfl⟩ := hs
      have hδ : (simTM M₀).δ q₁ (readAll T) =
          some (q', (stmtAction M₀ s tape₁.head).1, (stmtAction M₀ s tape₁.head).2) := by
        simp only [simTM]
        rw [hT.read, hq]; rfl
      obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ t by omega)
      rw [TM.run_succ_false, TM.step_toConfig_some _ _ hδ]
      cases s <;> exact ih _ _ hit (hT.step M₀ _) u (by omega)

/-- **Simulation of elementary single-tape machines.** For every single-tape machine `M₀` there
is a deterministic machine `M` of the archive model such that, whenever `M₀` started on `w`
halts within `T` steps in the configuration `c`, `M` decides `M₀.accept c.q = true` within
`T + 1` steps. -/
theorem singleTape_simulation_succ (M₀ : SingleTape) :
    ∃ M : Machine, Deterministic M ∧
      ∀ (w : List Bool) (c : TM0.Cfg M₀.Γ M₀.Q) (T : ℕ),
        StateTransition.EvalsToInTime (TM0.step M₀.transition)
          (TM0.init (w.map M₀.input)) (some c) T →
        TM0.step M₀.transition c = none →
        DecidesExactlyWithin M w (M₀.accept c.q = true) (T + 1) := by
  classical
  refine ⟨simMachine M₀, TM.deterministic_compileWith _ _, ?_⟩
  intro w c T hev hc
  refine ⟨M₀.accept c.q, ?_, Iff.rfl⟩
  have key := run_sim M₀ (fun q _ => M₀.accept q) (fun _ _ => rfl) c hc hev.steps
    (TM0.init (w.map M₀.input)) (inputTapes 0 w) hev.evals_in_steps (rel_init M₀ w) (T + 1)
    (by have := hev.steps_le_m; omega)
  unfold simMachine
  rw [runOn, TM.init_eq_toConfig]
  exact key

end Lax119563Proofs.Bridges.SingleTapeSim

namespace Lax119563Proofs.Bridges

open SingleTapeSim

/--
---
conclusion: Lax119563.MachineTranslations.singleTape_simulation
---
The simulating machine `simMachine M₀` performs one transition per `TM0` transition and one more
for halting, so it decides within `T + 1 ≤ 1 · (T + |w| + 1)` steps (`singleTape_simulation_succ`).
-/
theorem singleTape_simulation (M₀ : SingleTape) :
    ∃ M : Machine, Deterministic M ∧ ∃ C : ℕ, ∀ (w : List Bool) (T : ℕ) (c : TM0.Cfg M₀.Γ M₀.Q),
      Nonempty (StateTransition.EvalsToInTime (TM0.step M₀.transition)
        (TM0.init (w.map M₀.input)) (some c) T) →
      TM0.step M₀.transition c = none →
      DecidesExactlyWithin M w (M₀.accept c.q = true) (C * (T + w.length + 1)) := by
  obtain ⟨M, hM, h⟩ := singleTape_simulation_succ M₀
  refine ⟨M, hM, 1, fun w T c ⟨hev⟩ hc => ?_⟩
  exact Lax119563Proofs.Main.decidesWithin_mono (h w c T hev hc) (by omega)

end Lax119563Proofs.Bridges
