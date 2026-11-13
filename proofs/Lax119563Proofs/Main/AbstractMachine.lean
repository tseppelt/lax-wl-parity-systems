import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Card
import Lax119563Proofs.Main.Runs

/-!
# Deterministic machines with structured state and tape types

To build machines by composition it is convenient to index control states and tapes by
arbitrary finite types instead of initial segments of `ℕ`. An `AMachine σ ι S` has control
states `Option σ` (with initial state `none`), tapes `Option ι` (with input tape `none`),
and tape alphabet `Fin (S + 3)`, with the same conventions for blank (`0`), `false` (`1`)
and `true` (`2`) as `Lax489179.TuringMachine`. Every such machine is translated into a
deterministic `Machine` whose runs are, up to renaming of states and tapes, the same.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Main

/-- An instruction of a structured machine. -/
inductive AInstr (σ ι : Type) (S : ℕ)
  | halt (answer : Bool)
  | next (state : Option σ) (write : Option ι → Fin (S + 3)) (move : Option ι → Move)

/-- A deterministic machine with control states `Option σ`, tapes `Option ι`, and
alphabet `Fin (S + 3)`. -/
structure AMachine (σ ι : Type) (S : ℕ) where
  δ : Option σ → (Option ι → Fin (S + 3)) → AInstr σ ι S

/-- A configuration of a structured machine. -/
structure AConfig (σ ι : Type) (S : ℕ) where
  state : Option σ
  head : Option ι → ℤ
  tape : Option ι → ℤ → Fin (S + 3)
  answer : Option Bool

namespace AMachine

variable {σ ι : Type} {S : ℕ}

/-- The initial configuration on input `x`. -/
def init (x : List Bool) : AConfig σ ι S where
  state := none
  head := fun _ => 0
  tape := fun o z =>
    if o = none ∧ 0 ≤ z then
      match x[z.toNat]? with
      | none => 0
      | some false => 1
      | some true => 2
    else 0
  answer := none

/-- One step; a halted configuration is unchanged. -/
def step (A : AMachine σ ι S) (c : AConfig σ ι S) : AConfig σ ι S :=
  match c.answer with
  | some _ => c
  | none =>
    match A.δ c.state (fun o => c.tape o (c.head o)) with
    | .halt b => { c with answer := some b }
    | .next q w m =>
      { state := q
        head := fun o => c.head o + (m o).offset
        tape := fun o z => if z = c.head o then w o else c.tape o z
        answer := none }

/-- `t` steps. -/
def run (A : AMachine σ ι S) : ℕ → AConfig σ ι S → AConfig σ ι S
  | 0, c => c
  | t + 1, c => run A t (A.step c)

theorem run_succ (A : AMachine σ ι S) (t : ℕ) (c : AConfig σ ι S) :
    A.run (t + 1) c = A.step (A.run t c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih => exact ih (A.step c)

theorem run_add (A : AMachine σ ι S) (a b : ℕ) (c : AConfig σ ι S) :
    A.run (a + b) c = A.run b (A.run a c) := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, run_succ, ih, run_succ]

theorem step_of_halted (A : AMachine σ ι S) (c : AConfig σ ι S) (h : c.answer.isSome) :
    A.step c = c := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
  simp [step, hb]

theorem step_eq_next (A : AMachine σ ι S) {c : AConfig σ ι S} (hc : c.answer = none)
    {q : Option σ} {w : Option ι → Fin (S + 3)} {m : Option ι → Move}
    (h : A.δ c.state (fun o => c.tape o (c.head o)) = .next q w m) :
    A.step c = { state := q
                 head := fun o => c.head o + (m o).offset
                 tape := fun o z => if z = c.head o then w o else c.tape o z
                 answer := none } := by
  simp [step, hc, h]

theorem step_eq_halt (A : AMachine σ ι S) {c : AConfig σ ι S} (hc : c.answer = none)
    {b : Bool} (h : A.δ c.state (fun o => c.tape o (c.head o)) = .halt b) :
    A.step c = { c with answer := some b } := by
  simp [step, hc, h]

/-- Writing back the scanned symbol leaves a tape unchanged. -/
theorem write_back {α : Type} (f : ℤ → α) (h : ℤ) :
    (fun z => if z = h then f h else f z) = f := by
  funext z
  split_ifs with hz
  · rw [hz]
  · rfl

/-! ### Translation into `Lax489179.TuringMachine` -/

variable [Fintype σ] [Fintype ι]

/-- Numbering of the control states, with `none ↦ 0`. -/
noncomputable def eS (σ : Type) [Fintype σ] : Option σ ≃ Fin (Fintype.card σ + 1) :=
  (Equiv.optionCongr (Fintype.equivFin σ)).trans (finSuccEquiv _).symm

/-- Numbering of the tapes, with `none ↦ 0`. -/
noncomputable def eT (ι : Type) [Fintype ι] : Option ι ≃ Fin (Fintype.card ι + 1) :=
  (Equiv.optionCongr (Fintype.equivFin ι)).trans (finSuccEquiv _).symm

theorem eT_none : eT ι none = 0 := by simp [eT]

theorem eT_symm_eq_none_iff (j : Fin (Fintype.card ι + 1)) :
    (eT ι).symm j = none ↔ j = 0 := by
  constructor
  · intro h
    have := congrArg (eT ι) h
    rwa [Equiv.apply_symm_apply, eT_none] at this
  · rintro rfl
    rw [← eT_none, Equiv.symm_apply_apply]

/-- Translation of an instruction. -/
noncomputable def trInstr : AInstr σ ι S →
    Instruction (Fintype.card ι + 1) (S + 3) (Fintype.card σ + 1)
  | .halt b => .halt b
  | .next q w m => .next (eS σ q) (fun j => w ((eT ι).symm j)) (fun j => m ((eT ι).symm j))

/-- The translated machine. -/
noncomputable def toMachine (A : AMachine σ ι S) : Machine where
  tapes := Fintype.card ι
  symbols := S
  states := Fintype.card σ
  transition q sc _ := trInstr (A.δ ((eS σ).symm q) (fun o => sc (eT ι o)))

theorem toMachine_deterministic (A : AMachine σ ι S) : Deterministic A.toMachine :=
  fun _ _ => rfl

/-- Translation of a configuration. -/
noncomputable def enc (A : AMachine σ ι S) (c : AConfig σ ι S) : Config A.toMachine where
  state := eS σ c.state
  head := fun j => c.head ((eT ι).symm j)
  tape := fun j => c.tape ((eT ι).symm j)
  answer := c.answer

theorem step_enc (A : AMachine σ ι S) (c : AConfig σ ι S) :
    Lax489179.TuringMachine.step A.toMachine false (A.enc c) = A.enc (A.step c) := by
  rcases hc : c.answer with _ | b
  · have hsc : (fun o => (A.enc c).tape (eT ι o) ((A.enc c).head (eT ι o))) =
        fun o => c.tape o (c.head o) := by
      funext o; simp only [enc, Equiv.symm_apply_apply]; rfl
    have hδ : A.toMachine.transition (A.enc c).state
        (fun j => (A.enc c).tape j ((A.enc c).head j)) false =
        trInstr (A.δ c.state (fun o => c.tape o (c.head o))) := by
      simp only [toMachine]
      rw [hsc]
      simp [enc]
    simp only [Lax489179.TuringMachine.step, enc, hc] at hδ ⊢
    rw [hδ]
    simp only [AMachine.step, hc]
    cases A.δ c.state (fun o => c.tape o (c.head o)) <;> rfl
  · simp [Lax489179.TuringMachine.step, AMachine.step, enc, hc]

theorem init_enc (A : AMachine σ ι S) (x : List Bool) :
    Lax489179.TuringMachine.init A.toMachine x = A.enc (AMachine.init x) := by
  simp only [Lax489179.TuringMachine.init, enc, AMachine.init]
  congr 1
  funext j z
  have hj : (eT ι).symm j = none ↔ j = 0 := eT_symm_eq_none_iff (ι := ι) j
  by_cases h1 : j = 0 ∧ 0 ≤ z
  · rw [if_pos h1, if_pos ⟨hj.mpr h1.1, h1.2⟩]
    rcases x[z.toNat]? with _ | _ | _ <;> rfl
  · rw [if_neg h1, if_neg (fun h => h1 ⟨hj.mp h.1, h.2⟩)]
    rfl

theorem runOn_toMachine (A : AMachine σ ι S) (x : List Bool) (t : ℕ) :
    runOn A.toMachine x t = A.enc (A.run t (AMachine.init x)) := by
  induction t with
  | zero => exact init_enc A x
  | succ t ih => rw [runOn_succ, ih, step_enc, run_succ]

theorem decidesWithin_toMachine (A : AMachine σ ι S) (x : List Bool) (P : Prop) (t : ℕ)
    (b : Bool) (hb : (A.run t (AMachine.init x)).answer = some b) (hP : b = true ↔ P) :
    DecidesWithin A.toMachine x P t :=
  ⟨b, by rw [runOn_toMachine]; exact hb, hP⟩

end AMachine

end Lax119563Proofs.Main
