import Mathlib
import Lax119563.DeterministicTime

/-!
# Runs of multitape machines

Elementary facts about the deterministic runs `runOn M x t` of a `Lax489179` machine: one
more step is one application of `step`, heads move by at most one cell per step, a cell not
under the head keeps its symbol, halted configurations are fixed, and one step is a local
function of the extended state `(state, answer)` and the scanned symbols.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

variable {M : Machine}

/-- Tape symbols. -/
abbrev Sym (M : Machine) := Fin (M.symbols + 3)
/-- Tapes. -/
abbrev Tape (M : Machine) := Fin (M.tapes + 1)
/-- Extended states: the control state together with the answer (`none` while running). -/
abbrev ExtState (M : Machine) := Fin (M.states + 1) × Option Bool
/-- Cell values: a symbol and the flag "the head is here". -/
abbrev CellVal (M : Machine) := Sym M × Bool

lemma run_succ_const (t : ℕ) (c : Config M) :
    run M (t + 1) (fun _ => false) c = step M false (run M t (fun _ => false) c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    change run M (t + 1) (fun _ => false) (step M false c) = _
    rw [ih]
    rfl

lemma runOn_succ (x : List Bool) (t : ℕ) :
    runOn M x (t + 1) = step M false (runOn M x t) :=
  run_succ_const t _

lemma runOn_zero (x : List Bool) : runOn M x 0 = init M x := rfl

lemma step_of_halted {c : Config M} (h : c.answer.isSome) : step M false c = c := by
  unfold step
  cases hc : c.answer with
  | none => simp [hc] at h
  | some b => rfl

lemma step_head (c : Config M) (ν : Tape M) :
    |(step M false c).head ν - c.head ν| ≤ 1 := by
  unfold step
  cases c.answer with
  | some b => simp
  | none =>
    simp only
    cases M.transition c.state (fun j => c.tape j (c.head j)) false with
    | halt b => simp
    | next q write move =>
      simp only [add_sub_cancel_left]
      cases move ν <;> simp [Move.offset]

lemma step_tape_of_ne (c : Config M) (ν : Tape M) (z : ℤ) (hz : c.head ν ≠ z) :
    (step M false c).tape ν z = c.tape ν z := by
  unfold step
  cases c.answer with
  | some b => rfl
  | none =>
    simp only
    cases M.transition c.state (fun j => c.tape j (c.head j)) false with
    | halt b => rfl
    | next q write move =>
      simp only
      rw [if_neg (Ne.symm hz)]

lemma runOn_head_dist (x : List Bool) (ν : Tape M) (t k : ℕ) :
    |(runOn M x (t + k)).head ν - (runOn M x t).head ν| ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, runOn_succ]
    have h := step_head (runOn M x (t + k)) ν
    calc |(step M false (runOn M x (t + k))).head ν - (runOn M x t).head ν|
        ≤ |(step M false (runOn M x (t + k))).head ν - (runOn M x (t + k)).head ν| +
          |(runOn M x (t + k)).head ν - (runOn M x t).head ν| := abs_sub_le _ _ _
      _ ≤ 1 + k := add_le_add h ih
      _ = ((k + 1 : ℕ) : ℤ) := by push_cast; ring

/-- Frame property: a cell that is never under the head keeps its symbol. -/
lemma runOn_tape_frame (x : List Bool) (ν : Tape M) (z : ℤ) (t k : ℕ)
    (h : ∀ i < k, (runOn M x (t + i)).head ν ≠ z) :
    (runOn M x (t + k)).tape ν z = (runOn M x t).tape ν z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, runOn_succ, step_tape_of_ne _ _ _ (h k (by omega))]
    exact ih fun i hi => h i (by omega)

lemma runOn_halted (x : List Bool) {t : ℕ} (h : (runOn M x t).answer.isSome) (k : ℕ) :
    runOn M x (t + k) = runOn M x t := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, runOn_succ, ih, step_of_halted h]

/-- The extended state of a configuration. -/
def cfgExt (c : Config M) : ExtState M := (c.state, c.answer)

/-- The extended state after one step, from the extended state and the scanned symbols. -/
def nextExt (p : ExtState M) (scan : Tape M → Sym M) : ExtState M :=
  match p.2 with
  | some _ => p
  | none =>
    match M.transition p.1 scan false with
    | .halt b => (p.1, some b)
    | .next q _ _ => (q, none)

/-- The value after one step of the cell at relative position `j` of tape `ν`, from the
extended state, the scanned symbols, the relative head position `h` of tape `ν`, and the old
value of the cell. -/
def nextCell (p : ExtState M) (scan : Tape M → Sym M) (ν : Tape M) (h j : ℤ)
    (old : CellVal M) : CellVal M :=
  match p.2 with
  | some _ => old
  | none =>
    match M.transition p.1 scan false with
    | .halt _ => old
    | .next _ write move => (if j = h then write ν else old.1, decide (j = h + (move ν).offset))

/-- The value of a cell in a configuration. -/
def cfgCell (c : Config M) (ν : Tape M) (z : ℤ) : CellVal M :=
  (c.tape ν z, decide (c.head ν = z))

lemma step_ext (c : Config M) :
    cfgExt (step M false c) = nextExt (cfgExt c) (fun ν => c.tape ν (c.head ν)) := by
  rcases c with ⟨st, hd, tp, ans⟩
  unfold step nextExt cfgExt
  cases ans with
  | some b => rfl
  | none =>
    simp only
    cases M.transition st (fun j => tp j (hd j)) false with
    | halt b => rfl
    | next q write move => rfl

lemma step_cell (c : Config M) (ν : Tape M) (o z : ℤ) :
    cfgCell (step M false c) ν z =
      nextCell (cfgExt c) (fun ν => c.tape ν (c.head ν)) ν (c.head ν - o) (z - o) (cfgCell c ν z) := by
  rcases c with ⟨st, hd, tp, ans⟩
  unfold step nextCell cfgExt cfgCell
  cases ans with
  | some b => rfl
  | none =>
    simp only
    cases M.transition st (fun j => tp j (hd j)) false with
    | halt b => rfl
    | next q write move =>
      simp only [sub_left_inj, Prod.mk.injEq]
      constructor
      · simp
      · have : (hd ν + (move ν).offset = z) ↔ (z - o = hd ν - o + (move ν).offset) := by
          constructor <;> intro h <;> linarith
        simp [this]

end Lax119563Proofs.Circuits
