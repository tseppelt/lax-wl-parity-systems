import Lax119563.BinaryEncodings
import Lax119563.DeterministicTime
import Lax119563Proofs.Programs.Part1
import Lax489179.TuringMachine
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

/-! ### Formerly `Lax119563Proofs.Machines.Basic` -/

section Machines_Basic

/-!
# Structured multitape Turing machines

A `TM k Γ` is a deterministic Turing machine with `k` tapes over an arbitrary finite alphabet
`Γ` and an arbitrary finite type of control states. Its transition function either halts
(`none`) or writes one symbol per tape, moves each head and changes state.

The semantics is the big-step relation `M.HaltsFrom q T t T'`: started in state `q` on tapes
`T`, the machine performs exactly `t` transitions and then halts with tapes `T'`. Halting
itself is not counted here; the compilation to `Lax489179.TuringMachine.Machine` (file
`Compile`) adds one step for it.

Machines are assembled from combinators (`act`, `seq`, `branch`, `ite`, `loop`, `onTapes`)
whose lemmas compute the running time exactly. Routine specifications are stated with
`RunsWithin`, an upper bound on the running time.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type}

/-- A tape: head position and cell contents, both indexed by the integers. -/
@[ext]
structure Tape (Γ : Type) where
  head : ℤ
  cells : ℤ → Γ

namespace Tape

/-- The scanned symbol. -/
def read (T : Tape Γ) : Γ := T.cells T.head

/-- Write `a` at the head and then move the head by `m`. -/
def act (T : Tape Γ) (a : Γ) (m : Move) : Tape Γ :=
  ⟨T.head + m.offset, Function.update T.cells T.head a⟩

@[simp] lemma act_head (T : Tape Γ) (a : Γ) (m : Move) :
    (T.act a m).head = T.head + m.offset := rfl

@[simp] lemma act_cells (T : Tape Γ) (a : Γ) (m : Move) :
    (T.act a m).cells = Function.update T.cells T.head a := rfl

@[simp] lemma act_read_stay (T : Tape Γ) : T.act T.read .stay = T := by
  cases T; simp [act, read, Move.offset]

/-- Move the head without writing. -/
def move (T : Tape Γ) (m : Move) : Tape Γ := ⟨T.head + m.offset, T.cells⟩

lemma act_read (T : Tape Γ) (m : Move) : T.act T.read m = T.move m := by
  cases T; simp [act, read, move]

@[simp] lemma move_head (T : Tape Γ) (m : Move) : (T.move m).head = T.head + m.offset := rfl
@[simp] lemma move_cells (T : Tape Γ) (m : Move) : (T.move m).cells = T.cells := rfl

end Tape

@[simp] lemma Move.offset_left : Move.offset .left = -1 := rfl
@[simp] lemma Move.offset_right : Move.offset .right = 1 := rfl
@[simp] lemma Move.offset_stay : Move.offset .stay = 0 := rfl

/-- A family of `k` tapes. -/
abbrev Tapes (k : ℕ) (Γ : Type) := Fin k → Tape Γ

variable {k : ℕ}

/-- The scanned symbols. -/
def readAll (T : Tapes k Γ) : Fin k → Γ := fun i => (T i).read

/-- Apply one transition (written symbols and moves) to all tapes. -/
def applyAll (T : Tapes k Γ) (w : Fin k → Γ) (m : Fin k → Move) : Tapes k Γ :=
  fun i => (T i).act (w i) (m i)

@[simp] lemma applyAll_read_stay (T : Tapes k Γ) :
    applyAll T (readAll T) (fun _ => .stay) = T := by
  funext i; simp [applyAll, readAll]

/-- What a single non-halting transition does: written symbols and head moves. -/
abbrev Action (k : ℕ) (Γ : Type) := (Fin k → Γ) × (Fin k → Move)

/-- A deterministic `k`-tape machine over `Γ` with a finite type of states. -/
structure TM (k : ℕ) (Γ : Type) where
  /-- Control states. -/
  Q : Type
  [finQ : Fintype Q]
  [decQ : DecidableEq Q]
  /-- The initial state. -/
  start : Q
  /-- The transition function; `none` means halting. -/
  δ : Q → (Fin k → Γ) → Option (Q × Action k Γ)

attribute [instance] TM.finQ TM.decQ

namespace TM

/-- `M.HaltsFrom q T t T'`: started in `q` on `T`, the machine performs exactly `t`
transitions and then halts on `T'`. -/
inductive HaltsFrom (M : TM k Γ) : M.Q → Tapes k Γ → ℕ → Tapes k Γ → Prop
  | halt {q : M.Q} {T : Tapes k Γ} : M.δ q (readAll T) = none → M.HaltsFrom q T 0 T
  | step {q q' : M.Q} {T T' : Tapes k Γ} {w : Fin k → Γ} {m : Fin k → Move} {t : ℕ} :
      M.δ q (readAll T) = some (q', w, m) →
      M.HaltsFrom q' (applyAll T w m) t T' → M.HaltsFrom q T (t + 1) T'

/-- Run from the initial state for exactly `t` transitions, then halt on `T'`. -/
def HaltsIn (M : TM k Γ) (T : Tapes k Γ) (t : ℕ) (T' : Tapes k Γ) : Prop :=
  M.HaltsFrom M.start T t T'

/-- Run from the initial state and halt on `T'` after at most `t` transitions. -/
def RunsWithin (M : TM k Γ) (T : Tapes k Γ) (t : ℕ) (T' : Tapes k Γ) : Prop :=
  ∃ t' ≤ t, M.HaltsIn T t' T'

variable {M N : TM k Γ}

theorem HaltsIn.runsWithin {T T' : Tapes k Γ} {t : ℕ} (h : M.HaltsIn T t T') :
    M.RunsWithin T t T' := ⟨t, le_rfl, h⟩

theorem RunsWithin.mono {T T' : Tapes k Γ} {t t' : ℕ} (h : M.RunsWithin T t T')
    (ht : t ≤ t') : M.RunsWithin T t' T' := by
  obtain ⟨s, hs, h⟩ := h; exact ⟨s, hs.trans ht, h⟩

theorem RunsWithin.congr_right {T T' T'' : Tapes k Γ} {t : ℕ} (h : M.RunsWithin T t T')
    (e : T' = T'') : M.RunsWithin T t T'' := e ▸ h

/-- Two states with the same transition on the scanned symbols behave identically. -/
theorem HaltsFrom.congr_state {q₁ q₂ : M.Q} {T : Tapes k Γ}
    (hq : M.δ q₁ (readAll T) = M.δ q₂ (readAll T)) {t : ℕ} {T' : Tapes k Γ}
    (h : M.HaltsFrom q₁ T t T') : M.HaltsFrom q₂ T t T' := by
  cases h with
  | halt h => exact .halt (hq ▸ h)
  | step h hr => exact .step (hq ▸ h) hr

/-- Simulation along a state map that commutes with non-halting transitions: a halting run
of `M` followed by a halting run of `N` from the image of the final state. -/
theorem HaltsFrom.map (f : M.Q → N.Q)
    (hf : ∀ q s q' a, M.δ q s = some (q', a) → N.δ (f q) s = some (f q', a))
    {q : M.Q} {T T' : Tapes k Γ} {t : ℕ} (h : M.HaltsFrom q T t T') {t₂ : ℕ}
    {T₂ : Tapes k Γ}
    (hend : ∀ q', M.δ q' (readAll T') = none → N.HaltsFrom (f q') T' t₂ T₂) :
    N.HaltsFrom (f q) T (t + t₂) T₂ := by
  induction h with
  | halt hq => simpa using hend _ hq
  | step hq _ ih =>
    rw [Nat.add_right_comm]
    exact .step (hf _ _ _ _ hq) (ih hend)

/-! ## Combinators -/

/-- The machine that halts immediately. -/
def nop : TM k Γ where
  Q := Unit
  start := ()
  δ _ _ := none

theorem nop_haltsIn (T : Tapes k Γ) : (nop : TM k Γ).HaltsIn T 0 T := .halt rfl

/-- One transition, given as a function of the scanned symbols, then halt. -/
def act (f : (Fin k → Γ) → Action k Γ) : TM k Γ where
  Q := Bool
  start := false
  δ q s := if q then none else some (true, f s)

theorem act_haltsIn (f : (Fin k → Γ) → Action k Γ) (T : Tapes k Γ) :
    (act f).HaltsIn T 1 (applyAll T (f (readAll T)).1 (f (readAll T)).2) :=
  .step (by simp [act]; rfl) (.halt (by simp [act]))

/-- Sequential composition. The first transition of `M₂` is taken directly from the halting
state of `M₁`, so running times add up exactly. -/
def seq (M₁ M₂ : TM k Γ) : TM k Γ where
  Q := M₁.Q ⊕ M₂.Q
  start := .inl M₁.start
  δ
    | .inl q, s => match M₁.δ q s with
      | some (q', a) => some (.inl q', a)
      | none => (M₂.δ M₂.start s).map fun p => (.inr p.1, p.2)
    | .inr q, s => (M₂.δ q s).map fun p => (.inr p.1, p.2)

@[inherit_doc] infixl:60 " ;; " => seq

theorem seq_haltsIn {M₁ M₂ : TM k Γ} {T T₁ T₂ : Tapes k Γ} {t₁ t₂ : ℕ}
    (h₁ : M₁.HaltsIn T t₁ T₁) (h₂ : M₂.HaltsIn T₁ t₂ T₂) :
    (M₁ ;; M₂).HaltsIn T (t₁ + t₂) T₂ := by
  have h₂' : (M₁ ;; M₂).HaltsFrom (.inr M₂.start) T₁ t₂ T₂ := by
    have := h₂.map (N := M₁ ;; M₂) Sum.inr
      (fun q s q' a hq => by simp [seq, hq]) (t₂ := 0) (T₂ := T₂)
      (fun q' hq => .halt (by simp [seq, hq]))
    simpa using this
  exact h₁.map (N := M₁ ;; M₂) Sum.inl (fun q s q' a hq => by simp [seq, hq])
    (fun q' hq => h₂'.congr_state (by simp [seq, hq]))

theorem seq_runsWithin {M₁ M₂ : TM k Γ} {T T₁ T₂ : Tapes k Γ} {t₁ t₂ : ℕ}
    (h₁ : M₁.RunsWithin T t₁ T₁) (h₂ : M₂.RunsWithin T₁ t₂ T₂) :
    (M₁ ;; M₂).RunsWithin T (t₁ + t₂) T₂ := by
  obtain ⟨s₁, hs₁, h₁⟩ := h₁; obtain ⟨s₂, hs₂, h₂⟩ := h₂
  exact ⟨s₁ + s₂, by omega, seq_haltsIn h₁ h₂⟩

/-- `while c do B`: test `c` on the scanned symbols; if it holds, run `B` (one extra
transition per iteration) and repeat. -/
def loop (c : (Fin k → Γ) → Bool) (B : TM k Γ) : TM k Γ where
  Q := Option B.Q
  start := none
  δ
    | none, s => if c s then some (some B.start, s, fun _ => .stay) else none
    | some q, s => match B.δ q s with
      | some (q', a) => some (some q', a)
      | none => if c s then some (some B.start, s, fun _ => .stay) else none

theorem loop_haltsIn_exit {c : (Fin k → Γ) → Bool} {B : TM k Γ} {T : Tapes k Γ}
    (hc : c (readAll T) = false) : (loop c B).HaltsIn T 0 T :=
  .halt (by simp [loop, hc])

theorem loop_haltsIn_iter {c : (Fin k → Γ) → Bool} {B : TM k Γ} {T T₁ T₂ : Tapes k Γ}
    {t₁ t₂ : ℕ} (hc : c (readAll T) = true) (h₁ : B.HaltsIn T t₁ T₁)
    (h₂ : (loop c B).HaltsIn T₁ t₂ T₂) : (loop c B).HaltsIn T (t₁ + t₂ + 1) T₂ := by
  have := h₁.map (N := loop c B) some (fun q s q' a hq => by simp [loop, hq])
    (fun q' hq => h₂.congr_state (by simp [loop, hq]))
  refine .step (q' := some B.start) (w := readAll T) (m := fun _ => .stay)
    (by simp [loop, hc]) ?_
  simpa using this

theorem loop_runsWithin_exit {c : (Fin k → Γ) → Bool} {B : TM k Γ} {T : Tapes k Γ}
    (hc : c (readAll T) = false) : (loop c B).RunsWithin T 0 T :=
  (loop_haltsIn_exit hc).runsWithin

theorem loop_runsWithin_iter {c : (Fin k → Γ) → Bool} {B : TM k Γ} {T T₁ T₂ : Tapes k Γ}
    {t₁ t₂ : ℕ} (hc : c (readAll T) = true) (h₁ : B.RunsWithin T t₁ T₁)
    (h₂ : (loop c B).RunsWithin T₁ t₂ T₂) : (loop c B).RunsWithin T (t₁ + t₂ + 1) T₂ := by
  obtain ⟨s₁, hs₁, h₁⟩ := h₁; obtain ⟨s₂, hs₂, h₂⟩ := h₂
  exact ⟨s₁ + s₂ + 1, by omega, loop_haltsIn_iter hc h₁ h₂⟩

/-! ## Running a machine on a subset of the tapes -/

/-- Run a `k`-tape machine on the tapes `σ 0, …, σ (k-1)` of a `k'`-tape machine; the other
tapes are left unchanged. -/
noncomputable def onTapes {k' : ℕ} (σ : Fin k ↪ Fin k') (M : TM k Γ) : TM k' Γ where
  Q := M.Q
  start := M.start
  δ q s := (M.δ q (s ∘ σ)).map fun p =>
    (p.1, Function.extend σ p.2.1 s, Function.extend σ p.2.2 fun _ => .stay)

/-- Replace the tapes `σ i` of `U` by `T i`. -/
noncomputable def updateTapes {k' : ℕ} (σ : Fin k ↪ Fin k') (U : Tapes k' Γ) (T : Tapes k Γ) :
    Tapes k' Γ :=
  Function.extend σ T U

@[simp] lemma updateTapes_apply_self {k' : ℕ} (σ : Fin k ↪ Fin k') (U : Tapes k' Γ)
    (T : Tapes k Γ) (i : Fin k) : updateTapes σ U T (σ i) = T i :=
  σ.injective.extend_apply _ _ _

lemma updateTapes_apply_of_not_mem {k' : ℕ} (σ : Fin k ↪ Fin k') (U : Tapes k' Γ)
    (T : Tapes k Γ) {j : Fin k'} (hj : ∀ i, σ i ≠ j) : updateTapes σ U T j = U j :=
  Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact hj i hi)

@[simp] lemma updateTapes_comp {k' : ℕ} (σ : Fin k ↪ Fin k') (U : Tapes k' Γ)
    (T : Tapes k Γ) : updateTapes σ U T ∘ σ = T := by
  funext i; simp

@[simp] lemma updateTapes_updateTapes {k' : ℕ} (σ : Fin k ↪ Fin k') (U : Tapes k' Γ)
    (T T' : Tapes k Γ) : updateTapes σ (updateTapes σ U T) T' = updateTapes σ U T' := by
  funext j
  by_cases hj : ∃ i, σ i = j
  · obtain ⟨i, rfl⟩ := hj; simp
  · push Not at hj
    rw [updateTapes_apply_of_not_mem _ _ _ hj, updateTapes_apply_of_not_mem _ _ _ hj,
      updateTapes_apply_of_not_mem _ _ _ hj]

@[simp] lemma updateTapes_self {k' : ℕ} (σ : Fin k ↪ Fin k') (U : Tapes k' Γ) :
    updateTapes σ U (U ∘ σ) = U := by
  funext j
  by_cases hj : ∃ i, σ i = j
  · obtain ⟨i, rfl⟩ := hj; simp
  · push Not at hj; rw [updateTapes_apply_of_not_mem _ _ _ hj]

lemma applyAll_extend {k' : ℕ} (σ : Fin k ↪ Fin k') (U : Tapes k' Γ) (w : Fin k → Γ)
    (m : Fin k → Move) :
    applyAll U (Function.extend σ w (readAll U)) (Function.extend σ m fun _ => .stay) =
      updateTapes σ U (applyAll (U ∘ σ) w m) := by
  funext j
  by_cases hj : ∃ i, σ i = j
  · obtain ⟨i, rfl⟩ := hj
    simp [applyAll, σ.injective.extend_apply]
  · push Not at hj
    have hj' : ¬ ∃ i, σ i = j := by rintro ⟨i, hi⟩; exact hj i hi
    rw [updateTapes_apply_of_not_mem _ _ _ hj]
    simp only [applyAll, Function.extend_apply' _ _ _ hj']
    exact Tape.act_read_stay _

theorem onTapes_haltsFrom {k' : ℕ} (σ : Fin k ↪ Fin k') (M : TM k Γ) {q : M.Q}
    {T T' : Tapes k Γ} {t : ℕ} (h : M.HaltsFrom q T t T') (U : Tapes k' Γ) (hU : U ∘ σ = T) :
    (onTapes σ M).HaltsFrom q U t (updateTapes σ U T') := by
  have hr : ∀ V : Tapes k' Γ, readAll V ∘ σ = readAll (V ∘ σ) := fun _ => rfl
  induction h generalizing U with
  | halt hq =>
    subst hU
    simp only [updateTapes_self]
    exact .halt (by show Option.map _ (M.δ _ (readAll U ∘ σ)) = none; rw [hr, hq]; rfl)
  | @step q q' T T' w m t hq _ ih =>
    subst hU
    have hδ : (onTapes σ M).δ q (readAll U) =
        some (q', Function.extend σ w (readAll U), Function.extend σ m fun _ => .stay) := by
      show Option.map _ (M.δ _ (readAll U ∘ σ)) = _; rw [hr, hq]; rfl
    refine .step hδ ?_
    rw [applyAll_extend]
    have := ih (updateTapes σ U (applyAll (U ∘ σ) w m)) (by simp)
    simpa using this

theorem onTapes_runsWithin {k' : ℕ} (σ : Fin k ↪ Fin k') {M : TM k Γ} {U : Tapes k' Γ}
    {t : ℕ} {T' : Tapes k Γ} (h : M.RunsWithin (U ∘ σ) t T') :
    (onTapes σ M).RunsWithin U t (updateTapes σ U T') := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hs, onTapes_haltsFrom σ M h U rfl⟩

end TM

end Lax119563Proofs.Machines

end Machines_Basic

/-! ### Formerly `Lax119563Proofs.Machines.Compile` -/

section Machines_Compile

/-!
# Compiling structured machines to `Lax489179.TuringMachine.Machine`

A `TM (k+1) Γ` over an alphabet with a designated blank and two bit symbols is compiled
to a machine of the archive model by enumerating states (initial state first) and symbols
(blank, `false`, `true` first). A run of `t` transitions followed by halting becomes a run of
`t + 1` steps. The compiled machine is deterministic by construction.

Main result: `TM.computesWithin`, which turns a `RunsWithin` specification on the input tapes
`inputTapes k x` into `ComputesWithin` for the compiled machine.
-/

open Lax489179.TuringMachine
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Machines

/-- A tape alphabet: a blank symbol and two distinct non-blank bit symbols. -/
class TapeAlphabet (Γ : Type) where
  blank : Γ
  bit : Bool → Γ
  bit_injective : Function.Injective bit
  bit_ne_blank : ∀ b, bit b ≠ blank

export TapeAlphabet (blank bit)

variable {Γ : Type}

@[simp] lemma bit_ne_blank' [TapeAlphabet Γ] (b : Bool) : bit b ≠ (blank : Γ) :=
  TapeAlphabet.bit_ne_blank b

@[simp] lemma blank_ne_bit [TapeAlphabet Γ] (b : Bool) : (blank : Γ) ≠ bit b :=
  (TapeAlphabet.bit_ne_blank b).symm

@[simp] lemma bit_inj [TapeAlphabet Γ] {b c : Bool} : (bit b : Γ) = bit c ↔ b = c :=
  TapeAlphabet.bit_injective.eq_iff

/-- The cells of a tape holding `l` at positions `0, …, |l|-1` and blanks elsewhere. -/
def listCells [TapeAlphabet Γ] (l : List Γ) : ℤ → Γ :=
  fun z => if 0 ≤ z then (l[z.toNat]?).getD blank else blank

/-- The initial tapes on input `x`: `x` on tape `0` from position `0`, all heads at `0`,
everything else blank. -/
def inputTapes [TapeAlphabet Γ] (k : ℕ) (x : List Bool) : Tapes (k + 1) Γ :=
  fun i => ⟨0, if i = 0 then listCells (x.map bit) else fun _ => blank⟩

/-! ## Enumerations of symbols and states -/

private lemma swap_step {α β : Type} [DecidableEq β] (e : α ≃ β) (x : α) (y : β) :
    (e.trans (Equiv.swap (e x) y)) x = y ∧
      ∀ z, e z ≠ y → z ≠ x → (e.trans (Equiv.swap (e x) y)) z = e z := by
  refine ⟨by simp, fun z hz hzx => ?_⟩
  simp only [Equiv.trans_apply]
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hzx (e.injective h)) hz

lemma exists_equiv_fin_three {α : Type} [Fintype α] [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ e : α ≃ Fin (Fintype.card α - 3 + 3), e a = 0 ∧ e b = 1 ∧ e c = 2 := by
  have h3 : 3 ≤ Fintype.card α := by
    have := Finset.card_le_univ ({a, b, c} : Finset α)
    rwa [Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩] at this
  let e₁ : α ≃ Fin (Fintype.card α - 3 + 3) :=
    (Fintype.equivFin α).trans (finCongr (by omega))
  let e₂ := e₁.trans (Equiv.swap (e₁ a) 0)
  have h₂ := swap_step e₁ a 0
  have h₂a : e₂ a = 0 := h₂.1
  let e₃ := e₂.trans (Equiv.swap (e₂ b) 1)
  have h₃ := swap_step e₂ b 1
  have h₃b : e₃ b = 1 := h₃.1
  have h₃a : e₃ a = 0 := by
    rw [h₃.2 a (by rw [h₂a]; simp) hab, h₂a]
  let e₄ := e₃.trans (Equiv.swap (e₃ c) 2)
  have h₄ := swap_step e₃ c 2
  refine ⟨e₄, ?_, ?_, h₄.1⟩
  · rw [h₄.2 a (by rw [h₃a]; simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < Fintype.card α - 3 + 3 by omega)]) hac, h₃a]
  · rw [h₄.2 b (by rw [h₃b]; simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < Fintype.card α - 3 + 3 by omega)]) hbc, h₃b]

lemma exists_equiv_fin_one {α : Type} [Fintype α] (a : α) :
    ∃ e : α ≃ Fin (Fintype.card α - 1 + 1), e a = 0 := by
  classical
  have h1 : 1 ≤ Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  let e₁ : α ≃ Fin (Fintype.card α - 1 + 1) :=
    (Fintype.equivFin α).trans (finCongr (by omega))
  exact ⟨e₁.trans (Equiv.swap (e₁ a) 0), by simp⟩

section Compile

variable [Fintype Γ] [DecidableEq Γ] [TapeAlphabet Γ]

omit [Fintype Γ] [DecidableEq Γ] in
private lemma blank_ne_false : (blank : Γ) ≠ bit false := blank_ne_bit false
omit [Fintype Γ] [DecidableEq Γ] in
private lemma blank_ne_true : (blank : Γ) ≠ bit true := blank_ne_bit true
omit [Fintype Γ] [DecidableEq Γ] in
private lemma false_ne_true : (bit false : Γ) ≠ bit true := by simp

/-- The enumeration of symbols used by the compiled machine. -/
noncomputable def symEquiv (Γ : Type) [Fintype Γ] [DecidableEq Γ] [TapeAlphabet Γ] :
    Γ ≃ Fin (Fintype.card Γ - 3 + 3) :=
  Classical.choose (exists_equiv_fin_three (blank_ne_false (Γ := Γ)) blank_ne_true
    false_ne_true)

lemma symEquiv_blank : symEquiv Γ blank = 0 :=
  (Classical.choose_spec (exists_equiv_fin_three (blank_ne_false (Γ := Γ)) blank_ne_true
    false_ne_true)).1

lemma symEquiv_bit (b : Bool) : symEquiv Γ (bit b) = if b then 2 else 1 := by
  have := Classical.choose_spec (exists_equiv_fin_three (blank_ne_false (Γ := Γ))
    blank_ne_true false_ne_true)
  cases b
  · exact this.2.1
  · exact this.2.2

variable {k : ℕ}

/-- The enumeration of states used by the compiled machine. -/
noncomputable def TM.stateEquiv (M : TM k Γ) : M.Q ≃ Fin (Fintype.card M.Q - 1 + 1) :=
  Classical.choose (exists_equiv_fin_one M.start)

omit [Fintype Γ] [DecidableEq Γ] [TapeAlphabet Γ] in
lemma TM.stateEquiv_start (M : TM k Γ) : M.stateEquiv M.start = 0 :=
  Classical.choose_spec (exists_equiv_fin_one M.start)

/-- The compiled machine; on halting in state `q` with scanned symbols `s` it returns
`ans q s`. -/
noncomputable def TM.compileWith (M : TM (k + 1) Γ) (ans : M.Q → (Fin (k + 1) → Γ) → Bool) :
    Machine where
  tapes := k
  symbols := Fintype.card Γ - 3
  states := Fintype.card M.Q - 1
  transition q s _ :=
    match M.δ (M.stateEquiv.symm q) (fun i => (symEquiv Γ).symm (s i)) with
    | none => .halt (ans (M.stateEquiv.symm q) (fun i => (symEquiv Γ).symm (s i)))
    | some (q', w, m) => .next (M.stateEquiv q') (fun i => symEquiv Γ (w i)) m

/-- The compiled machine returning `false` on halting. -/
noncomputable def TM.compile (M : TM (k + 1) Γ) : Machine := M.compileWith fun _ _ => false

theorem TM.deterministic_compileWith (M : TM (k + 1) Γ)
    (ans : M.Q → (Fin (k + 1) → Γ) → Bool) : Deterministic (M.compileWith ans) :=
  fun _ _ => rfl

theorem TM.deterministic_compile (M : TM (k + 1) Γ) : Deterministic M.compile :=
  M.deterministic_compileWith _

namespace TM

variable (M : TM (k + 1) Γ) (ans : M.Q → (Fin (k + 1) → Γ) → Bool)

/-- The configuration of the compiled machine corresponding to state `q` and tapes `T`. -/
noncomputable def toConfig (q : M.Q) (T : Tapes (k + 1) Γ) : Config (M.compileWith ans) where
  state := M.stateEquiv q
  head := fun i => (T i).head
  tape := fun i z => symEquiv Γ ((T i).cells z)
  answer := none

lemma step_toConfig_some {q q' : M.Q} {T : Tapes (k + 1) Γ} {w : Fin (k + 1) → Γ}
    {m : Fin (k + 1) → Move} (h : M.δ q (readAll T) = some (q', w, m)) :
    step (M.compileWith ans) false (M.toConfig ans q T) =
      M.toConfig ans q' (applyAll T w m) := by
  have h' : M.δ (M.stateEquiv.symm (M.stateEquiv q))
      (fun i => (symEquiv Γ).symm (symEquiv Γ ((T i).cells (T i).head))) =
      some (q', w, m) := by simp only [Equiv.symm_apply_apply]; exact h
  simp only [step, toConfig, compileWith, h']
  congr 1
  funext i z
  simp only [applyAll, Tape.act_cells, Function.update_apply]
  by_cases hz : z = (T i).head <;> simp [hz]

lemma step_toConfig_none {q : M.Q} {T : Tapes (k + 1) Γ} (h : M.δ q (readAll T) = none) :
    step (M.compileWith ans) false (M.toConfig ans q T) =
      { M.toConfig ans q T with answer := some (ans q (readAll T)) } := by
  have h' : M.δ (M.stateEquiv.symm (M.stateEquiv q))
      (fun i => (symEquiv Γ).symm (symEquiv Γ ((T i).cells (T i).head))) = none := by
    simp only [Equiv.symm_apply_apply]; exact h
  have h'' : M.δ q (fun i => (T i).cells (T i).head) = none := h
  simp only [step, toConfig, compileWith, Equiv.symm_apply_apply, h'']
  rfl

lemma run_succ_false (M' : Machine) (t : ℕ) (c : Config M') :
    run M' (t + 1) (fun _ => false) c = run M' t (fun _ => false) (step M' false c) := rfl

lemma run_of_answer_isSome (M' : Machine) (t : ℕ) (c : Config M') (hc : c.answer.isSome) :
    run M' t (fun _ => false) c = c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ_false]
    have : step M' false c = c := by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hc
      simp [step, hb]
    rw [this, ih]

theorem run_toConfig {q : M.Q} {T T' : Tapes (k + 1) Γ} {t : ℕ}
    (h : M.HaltsFrom q T t T') :
    ∃ q', M.δ q' (readAll T') = none ∧ ∀ t' ≥ t + 1,
      run (M.compileWith ans) t' (fun _ => false) (M.toConfig ans q T) =
        { M.toConfig ans q' T' with answer := some (ans q' (readAll T')) } := by
  induction h with
  | @halt q T hq =>
    refine ⟨q, hq, fun t' ht' => ?_⟩
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' ht'
    rw [run_succ_false, step_toConfig_none M ans hq, run_of_answer_isSome _ _ _ (by simp)]
  | step hq _ ih =>
    obtain ⟨q', hq', hrun⟩ := ih
    refine ⟨q', hq', fun t' ht' => ?_⟩
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ t' by omega)
    rw [run_succ_false, step_toConfig_some M ans hq, hrun s (by omega)]

private lemma init_cell (x : List Bool) (i : Fin (k + 1)) (z : ℤ) :
    (if i = 0 ∧ 0 ≤ z then
      (match x[z.toNat]? with
        | none => 0
        | some false => 1
        | some true => 2 : Fin (Fintype.card Γ - 3 + 3))
    else 0) = symEquiv Γ ((inputTapes (Γ := Γ) k x i).cells z) := by
  simp only [inputTapes]
  by_cases hi : i = 0
  · rw [if_pos hi]
    by_cases hz : 0 ≤ z
    · rw [if_pos ⟨hi, hz⟩]
      simp only [hz, listCells, List.getElem?_map, if_true]
      cases x[z.toNat]? with
      | none => simp [symEquiv_blank]
      | some b => cases b <;> simp [symEquiv_bit]
    · rw [if_neg (fun h => hz h.2)]
      simp [hz, listCells, symEquiv_blank]
  · rw [if_neg (fun h => hi h.1), if_neg hi, symEquiv_blank]

lemma init_eq_toConfig (x : List Bool) :
    init (M.compileWith ans) x = M.toConfig ans M.start (inputTapes k x) := by
  simp only [init, toConfig, stateEquiv_start]
  congr 1
  funext i z
  exact init_cell x i z

/-- Running the compiled machine on `x` past the halting time of `M`. -/
theorem runOn_compileWith {x : List Bool} {t : ℕ} {T' : Tapes (k + 1) Γ}
    (h : M.RunsWithin (inputTapes k x) t T') :
    ∃ q', M.δ q' (readAll T') = none ∧
      runOn (M.compileWith ans) x (t + 1) =
        { M.toConfig ans q' T' with answer := some (ans q' (readAll T')) } := by
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨q', hq', hrun⟩ := M.run_toConfig ans h
  exact ⟨q', hq', by rw [runOn, init_eq_toConfig]; exact hrun _ (by omega)⟩

/-- **Output convention.** If `M` halts within `t` transitions on the input tapes of `x`,
leaving exactly `y` on tape `0` (from position `0`, blanks elsewhere), then the compiled
machine computes `y` from `x` within `t + 1` steps. -/
theorem computesWithin {x y : List Bool} {t : ℕ} {T' : Tapes (k + 1) Γ}
    (h : M.RunsWithin (inputTapes k x) t T') (hy : (T' 0).cells = listCells (y.map bit)) :
    ComputesWithin (M.compileWith ans) x y (t + 1) := by
  obtain ⟨q', -, hrun⟩ := M.runOn_compileWith ans h
  refine ⟨by simp [HaltsWithin, hrun], ?_⟩
  rw [hrun, init_eq_toConfig]
  funext z
  show symEquiv Γ ((T' 0).cells z) = symEquiv Γ ((inputTapes k y 0).cells z)
  rw [hy]
  simp [inputTapes]

end TM

end Compile

end Lax119563Proofs.Machines

end Machines_Compile

/-! ### Formerly `Lax119563Proofs.Machines.Words` -/

section Machines_Words

/-!
# Tapes holding words

`Tape.ofWord pre rest` is the tape whose cells hold `pre ++ rest` from position `0` (blanks
elsewhere) with the head on position `|pre|`, i.e. on the first symbol of `rest` (or on the
blank after the word if `rest = []`). The lemmas below describe the effect of single
transitions on such tapes.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type} [TapeAlphabet Γ]

/-! ## Cells of a list -/

lemma listCells_natCast (l : List Γ) (n : ℕ) : listCells l (n : ℤ) = l[n]?.getD blank := by
  simp [listCells]

lemma listCells_of_neg (l : List Γ) {z : ℤ} (hz : z < 0) : listCells l z = blank := by
  simp [listCells, not_le.mpr hz]

@[simp] lemma listCells_nil : listCells ([] : List Γ) = fun _ => blank := by
  funext z; simp [listCells]

lemma update_listCells {l l' : List Γ} {n : ℕ} {b : Γ}
    (h : ∀ m : ℕ, l'[m]?.getD blank = if m = n then b else l[m]?.getD blank) :
    Function.update (listCells l) (n : ℤ) b = listCells l' := by
  funext z
  rw [Function.update_apply]
  by_cases hz : 0 ≤ z
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    rw [listCells_natCast, listCells_natCast, h m]
    simp only [Nat.cast_inj]
  · have hzn : z ≠ (n : ℤ) := by omega
    rw [if_neg hzn, listCells_of_neg _ (by omega), listCells_of_neg _ (by omega)]

/-- Overwriting position `|pre|` of `pre ++ rest`. -/
lemma getD_set_mid (pre rest : List Γ) (b : Γ) (m : ℕ) :
    (pre ++ b :: rest.tail)[m]?.getD blank =
      if m = pre.length then b else (pre ++ rest)[m]?.getD blank := by
  rcases lt_trichotomy m pre.length with h | rfl | h
  · rw [if_neg (by omega), List.getElem?_append_left h, List.getElem?_append_left h]
  · simp
  · rw [if_neg (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega)]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    rw [show pre.length + j + 1 - pre.length = j + 1 by omega, List.getElem?_cons_succ]
    cases rest <;> simp

/-! ## Word tapes -/

/-- The tape holding `pre ++ rest` from position `0`, with the head on position `|pre|`. -/
def Tape.ofWord (pre rest : List Γ) : Tape Γ := ⟨pre.length, listCells (pre ++ rest)⟩

namespace Tape

@[simp] lemma ofWord_head (pre rest : List Γ) : (ofWord pre rest).head = pre.length := rfl

@[simp] lemma ofWord_cells (pre rest : List Γ) :
    (ofWord pre rest).cells = listCells (pre ++ rest) := rfl

lemma read_ofWord (pre rest : List Γ) : (ofWord pre rest).read = rest.headD blank := by
  simp only [read, ofWord, listCells_natCast]
  cases rest <;> simp

@[simp] lemma read_ofWord_cons (pre rest : List Γ) (a : Γ) :
    (ofWord pre (a :: rest)).read = a := by simp [read_ofWord]

@[simp] lemma read_ofWord_nil (pre : List Γ) : (ofWord pre []).read = blank := by
  simp [read_ofWord]

/-- Writing and moving right. -/
lemma act_ofWord_right (pre rest : List Γ) (b : Γ) :
    (ofWord pre rest).act b .right = ofWord (pre ++ [b]) rest.tail := by
  ext
  · simp
  · simp only [act_cells, ofWord_cells, ofWord_head]
    rw [update_listCells (l' := pre ++ [b] ++ rest.tail)]
    intro m
    rw [List.append_assoc, List.singleton_append]
    exact getD_set_mid pre rest b m

/-- Writing without moving. -/
lemma act_ofWord_stay (pre rest : List Γ) (b : Γ) :
    (ofWord pre rest).act b .stay = ofWord pre (b :: rest.tail) := by
  ext
  · simp
  · simp only [act_cells, ofWord_cells, ofWord_head]
    exact congrFun (update_listCells (getD_set_mid pre rest b)) _

lemma move_ofWord_right (pre rest : List Γ) (a : Γ) :
    (ofWord pre (a :: rest)).move .right = ofWord (pre ++ [a]) rest := by
  ext <;> simp

end Tape

end Lax119563Proofs.Machines

end Machines_Words

/-! ### Formerly `Lax119563Proofs.Machines.Routines` -/

section Machines_Routines

/-!
# Basic routines on word tapes

Single transitions on one or two tapes (`actOn`, `act₂`), head moves and writes, scanning
over symbols satisfying a predicate in either direction (`scanR`, `scanL`, `backTo`,
`rewind`), copying (`copyR`) and erasing (`erase`). All bounds are linear in the number of
cells passed over.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type} {k : ℕ}

open Function (update)

namespace TM

/-! ## One transition on one or two tapes -/

/-- One transition on tape `i` only, as a function of the symbol scanned there. -/
def actOn (i : Fin k) (f : Γ → Γ × Move) : TM k Γ :=
  act fun s => (update s i (f (s i)).1, update (fun _ => Move.stay) i (f (s i)).2)

lemma applyAll_update (T : Tapes k Γ) (i : Fin k) (a : Γ) (m : Move) :
    applyAll T (update (readAll T) i a) (update (fun _ => .stay) i m) =
      update T i ((T i).act a m) := by
  funext j
  by_cases h : j = i
  · subst h; simp [applyAll]
  · simp only [applyAll, Function.update_of_ne h]
    exact Tape.act_read_stay _

theorem actOn_runsWithin (i : Fin k) (f : Γ → Γ × Move) (T : Tapes k Γ) :
    (actOn i f).RunsWithin T 1
      (update T i ((T i).act (f (T i).read).1 (f (T i).read).2)) := by
  have := act_haltsIn
    (fun s => (update s i (f (s i)).1, update (fun _ => Move.stay) i (f (s i)).2)) T
  simp only at this
  rw [show readAll T i = (T i).read from rfl, applyAll_update] at this
  exact this.runsWithin

/-- One transition on tapes `i` and `j`, as a function of the two scanned symbols. -/
def act₂ (i j : Fin k) (f : Γ → Γ → (Γ × Move) × (Γ × Move)) : TM k Γ :=
  act fun s => (update (update s i (f (s i) (s j)).1.1) j (f (s i) (s j)).2.1,
    update (update (fun _ => Move.stay) i (f (s i) (s j)).1.2) j (f (s i) (s j)).2.2)

theorem act₂_runsWithin {i j : Fin k} (hij : i ≠ j) (f : Γ → Γ → (Γ × Move) × (Γ × Move))
    (T : Tapes k Γ) :
    (act₂ i j f).RunsWithin T 1
      (update (update T i ((T i).act (f (T i).read (T j).read).1.1
          (f (T i).read (T j).read).1.2))
        j ((T j).act (f (T i).read (T j).read).2.1 (f (T i).read (T j).read).2.2)) := by
  have h := (act_haltsIn (fun s => (update (update s i (f (s i) (s j)).1.1) j (f (s i) (s j)).2.1,
    update (update (fun _ => Move.stay) i (f (s i) (s j)).1.2) j (f (s i) (s j)).2.2)) T).runsWithin
  refine h.congr_right ?_
  funext l
  simp only [applyAll]
  by_cases hl : l = j
  · subst hl; simp [readAll]
  · by_cases hl' : l = i
    · subst hl'; simp [Function.update_of_ne hl, readAll]
    · simp only [Function.update_of_ne hl, Function.update_of_ne hl']
      exact Tape.act_read_stay (T l)

/-! ## Moves and writes -/

/-- Move the head of tape `i` right. -/
def moveR (i : Fin k) : TM k Γ := actOn i fun a => (a, .right)
/-- Move the head of tape `i` left. -/
def moveL (i : Fin k) : TM k Γ := actOn i fun a => (a, .left)
/-- Write `b` on tape `i` without moving. -/
def write (i : Fin k) (b : Γ) : TM k Γ := actOn i fun _ => (b, .stay)
/-- Write `b` on tape `i` and move right. -/
def writeR (i : Fin k) (b : Γ) : TM k Γ := actOn i fun _ => (b, .right)

theorem moveR_runsWithin (i : Fin k) (T : Tapes k Γ) :
    (moveR i).RunsWithin T 1 (update T i ((T i).move .right)) := by
  exact (actOn_runsWithin i (fun a => (a, Move.right)) T).congr_right (by rw [Tape.act_read])

theorem moveL_runsWithin (i : Fin k) (T : Tapes k Γ) :
    (moveL i).RunsWithin T 1 (update T i ((T i).move .left)) := by
  exact (actOn_runsWithin i (fun a => (a, Move.left)) T).congr_right (by rw [Tape.act_read])

theorem write_runsWithin (i : Fin k) (b : Γ) (T : Tapes k Γ) :
    (write i b).RunsWithin T 1 (update T i ((T i).act b .stay)) :=
  actOn_runsWithin i _ T

theorem writeR_runsWithin (i : Fin k) (b : Γ) (T : Tapes k Γ) :
    (writeR i b).RunsWithin T 1 (update T i ((T i).act b .right)) :=
  actOn_runsWithin i _ T

/-! ## Scanning -/

/-- Move right on tape `i` while the scanned symbol satisfies `p`. -/
def scanR (i : Fin k) (p : Γ → Bool) : TM k Γ := loop (fun s => p (s i)) (moveR i)

/-- Move left on tape `i` while the scanned symbol satisfies `p`. -/
def scanL (i : Fin k) (p : Γ → Bool) : TM k Γ := loop (fun s => p (s i)) (moveL i)

theorem scanR_raw (i : Fin k) (p : Γ → Bool) (d : ℕ) (T : Tapes k Γ)
    (hd : ∀ j < d, p ((T i).cells ((T i).head + j)) = true)
    (hend : p ((T i).cells ((T i).head + d)) = false) :
    (scanR i p).RunsWithin T (2 * d) (update T i ⟨(T i).head + d, (T i).cells⟩) := by
  unfold scanR
  induction d generalizing T with
  | zero =>
    exact (loop_runsWithin_exit (B := moveR i) (c := fun s => p (s i)) (T := T)
      (by simpa [readAll, Tape.read] using hend)).congr_right (by simp)
  | succ d ih =>
    have h0 := hd 0 (by omega)
    have := ih (update T i ((T i).move .right))
      (fun j hj => by simpa [add_assoc, add_comm (1 : ℤ)] using hd (j + 1) (by omega))
      (by simpa [add_assoc, add_comm (1 : ℤ)] using hend)
    have h := loop_runsWithin_iter (c := fun s => p (s i)) (B := moveR i)
      (by simpa [readAll, Tape.read] using h0) (moveR_runsWithin i T) this
    refine (h.mono (by omega)).congr_right ?_
    simp only [Function.update_idem, Function.update_self, Tape.move_head, Tape.move_cells,
      Move.offset_right]
    rw [show (T i).head + 1 + (d : ℤ) = (T i).head + ((d + 1 : ℕ) : ℤ) by push_cast; ring]

end TM

end Lax119563Proofs.Machines

end Machines_Routines

/-! ### Formerly `Lax119563Proofs.Machines.WordRoutines` -/

section Machines_WordRoutines

/-!
# Scanning, rewinding, copying and erasing word tapes

Specifications of the routines of `Routines` on tapes of the form `Tape.ofWord pre rest`.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type} {k : ℕ}

open Function (update)

namespace TM

theorem scanL_raw (i : Fin k) (p : Γ → Bool) (d : ℕ) (T : Tapes k Γ)
    (hd : ∀ j < d, p ((T i).cells ((T i).head - j)) = true)
    (hend : p ((T i).cells ((T i).head - d)) = false) :
    (scanL i p).RunsWithin T (2 * d) (update T i ⟨(T i).head - d, (T i).cells⟩) := by
  unfold scanL
  induction d generalizing T with
  | zero =>
    exact (loop_runsWithin_exit (B := moveL i) (c := fun s => p (s i)) (T := T)
      (by simpa [readAll, Tape.read] using hend)).congr_right (by simp)
  | succ d ih =>
    have h0 := hd 0 (by omega)
    have := ih (update T i ((T i).move .left))
      (fun j hj => by
        have := hd (j + 1) (by omega)
        simp only [Function.update_self, Tape.move_head, Tape.move_cells, Move.offset_left]
        rw [show (T i).head + -1 - (j : ℤ) = (T i).head - ((j + 1 : ℕ) : ℤ) by push_cast; ring]
        exact this)
      (by
        simp only [Function.update_self, Tape.move_head, Tape.move_cells, Move.offset_left]
        rw [show (T i).head + -1 - (d : ℤ) = (T i).head - ((d + 1 : ℕ) : ℤ) by push_cast; ring]
        exact hend)
    have h := loop_runsWithin_iter (c := fun s => p (s i)) (B := moveL i)
      (by simpa [readAll, Tape.read] using h0) (moveL_runsWithin i T) this
    refine (h.mono (by omega)).congr_right ?_
    simp only [Function.update_idem, Function.update_self, Tape.move_head, Tape.move_cells,
      Move.offset_left]
    rw [show (T i).head + -1 - (d : ℤ) = (T i).head - ((d + 1 : ℕ) : ℤ) by push_cast; ring]

end TM

/-! ## Cells of word tapes -/

variable [TapeAlphabet Γ]

lemma listCells_add (pre l : List Γ) (j : ℕ) :
    listCells (pre ++ l) ((pre.length : ℤ) + j) = l[j]?.getD blank := by
  rw [show (pre.length : ℤ) + j = ((pre.length + j : ℕ) : ℤ) by push_cast; rfl,
    listCells_natCast, List.getElem?_append_right (by omega)]
  simp

lemma listCells_of_length_le (l : List Γ) {z : ℤ} (hz : (l.length : ℤ) ≤ z) :
    listCells l z = blank := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ z)
  rw [listCells_natCast, List.getElem?_eq_none (by omega)]
  rfl

lemma listCells_of_lt (l : List Γ) {n : ℕ} (hn : n < l.length) :
    listCells l (n : ℤ) = l[n] := by
  rw [listCells_natCast, List.getElem?_eq_getElem hn]
  rfl

namespace TM

theorem scanR_ofWord (i : Fin k) (p : Γ → Bool) {T : Tapes k Γ} {pre u rest : List Γ}
    (hT : T i = .ofWord pre (u ++ rest)) (hu : ∀ a ∈ u, p a = true)
    (hr : p (rest.headD blank) = false) :
    (scanR i p).RunsWithin T (2 * u.length) (update T i (.ofWord (pre ++ u) rest)) := by
  refine (scanR_raw i p u.length T (fun j hj => ?_) ?_).congr_right ?_
  · rw [hT, Tape.ofWord_head, Tape.ofWord_cells, listCells_add,
      List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
    exact hu _ (List.getElem_mem _)
  · rw [hT, Tape.ofWord_head, Tape.ofWord_cells, listCells_add, List.getElem?_append_right le_rfl]
    cases rest <;> simpa using hr
  · rw [hT]
    congr 1
    ext
    · simp
    · simp

/-- Move left to just after the nearest cell (to the left of the head) violating `p`: from
the head on the cell after `u` back to the first cell of `u`. -/
def backTo (i : Fin k) (p : Γ → Bool) : TM k Γ := moveL i ;; scanL i p ;; moveR i

theorem backTo_ofWord (i : Fin k) (p : Γ → Bool) {T : Tapes k Γ} {pre u rest : List Γ}
    (hT : T i = .ofWord (pre ++ u) rest) (hu : ∀ a ∈ u, p a = true)
    (hpre : p (pre.getLast?.getD blank) = false) :
    (backTo i p).RunsWithin T (2 * u.length + 2) (update T i (.ofWord pre (u ++ rest))) := by
  have h₁ := moveL_runsWithin i T
  set T₁ := update T i ((T i).move .left) with hT₁
  have hT₁i : T₁ i = ⟨(pre.length : ℤ) + u.length - 1, listCells (pre ++ (u ++ rest))⟩ := by
    rw [hT₁, Function.update_self, hT]
    ext
    · simp; ring
    · simp
  have h₂ := scanL_raw i p u.length T₁ (fun j hj => ?_) ?_
  · have h₃ := moveR_runsWithin i (update T₁ i ⟨(T₁ i).head - u.length, (T₁ i).cells⟩)
    refine ((seq_runsWithin (seq_runsWithin h₁ h₂) h₃).mono (by omega)).congr_right ?_
    simp only [Function.update_idem, Function.update_self, Tape.move_head, Tape.move_cells,
      Move.offset_right, hT₁i]
    rw [hT₁, Function.update_idem]
    congr 1
    ext
    · simp; ring
    · simp
  · rw [hT₁i]
    simp only
    rw [show (pre.length : ℤ) + u.length - 1 - j = (pre.length : ℤ) + ((u.length - 1 - j : ℕ) : ℤ)
      by omega,
      listCells_add, List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
    exact hu _ (List.getElem_mem _)
  · rw [hT₁i]
    simp only
    rw [show (pre.length : ℤ) + u.length - 1 - u.length = (pre.length : ℤ) - 1 by ring]
    rcases List.eq_nil_or_concat pre with rfl | ⟨pre', b, rfl⟩
    · simpa [listCells_of_neg] using hpre
    · simp only [List.concat_eq_append] at hpre ⊢
      rw [show ((pre' ++ [b]).length : ℤ) - 1 = (pre'.length : ℤ) + ((0 : ℕ) : ℤ) by simp,
        List.append_assoc, listCells_add]
      simpa using hpre

/-- Move the head of tape `i` back to position `0`, over a blank-free prefix. -/
def rewind [DecidableEq Γ] (i : Fin k) : TM k Γ := backTo i fun a => decide (a ≠ blank)

theorem rewind_ofWord [DecidableEq Γ] (i : Fin k) {T : Tapes k Γ} {pre rest : List Γ}
    (hT : T i = .ofWord pre rest) (hpre : ∀ a ∈ pre, a ≠ blank) :
    (rewind i).RunsWithin T (2 * pre.length + 2) (update T i (.ofWord [] (pre ++ rest))) :=
  backTo_ofWord i _ (pre := []) (by simpa using hT) (by simpa using hpre) (by simp)

omit [TapeAlphabet Γ] in
lemma update_update_update_update {α : Type} {T : Fin k → α} {i j : Fin k} (hij : i ≠ j)
    (A B X Y : α) :
    update (update (update (update T i A) j B) i X) j Y = update (update T i X) j Y := by
  funext l
  by_cases hl : l = j
  · subst hl; simp
  · by_cases hl' : l = i
    · subst hl'; simp [Function.update_of_ne hl]
    · simp [Function.update_of_ne hl, Function.update_of_ne hl']

/-- Copy the symbols satisfying `p` from tape `i` (moving right) to tape `j` (moving
right), up to the first symbol on tape `i` violating `p`. -/
def copyR (i j : Fin k) (p : Γ → Bool) : TM k Γ :=
  loop (fun s => p (s i)) (act₂ i j fun a _ => ((a, .right), (a, .right)))

theorem copyR_ofWord {i j : Fin k} (hij : i ≠ j) (p : Γ → Bool) {T : Tapes k Γ}
    {pre u rest dpre drest : List Γ}
    (hTi : T i = .ofWord pre (u ++ rest)) (hu : ∀ a ∈ u, p a = true)
    (hr : p (rest.headD blank) = false) (hTj : T j = .ofWord dpre drest) :
    (copyR i j p).RunsWithin T (2 * u.length)
      (update (update T i (.ofWord (pre ++ u) rest)) j
        (.ofWord (dpre ++ u) (drest.drop u.length))) := by
  unfold copyR
  induction u generalizing pre dpre drest T with
  | nil =>
    refine (loop_runsWithin_exit
      (by simpa [readAll, hTi, Tape.read_ofWord] using hr)).congr_right ?_
    simp only [List.nil_append] at hTi
    simp [← hTi, ← hTj]
  | cons a u ih =>
    have h₁ := act₂_runsWithin hij (fun a _ => ((a, Move.right), (a, Move.right))) T
    simp only [hTi, hTj, List.cons_append, Tape.read_ofWord_cons, Tape.act_ofWord_right,
      List.tail_cons] at h₁
    have h₂ := ih (pre := pre ++ [a]) (dpre := dpre ++ [a]) (drest := drest.tail)
      (T := update (update T i (Tape.ofWord (pre ++ [a]) (u ++ rest))) j
        (Tape.ofWord (dpre ++ [a]) drest.tail))
      (by simp [Function.update_of_ne hij]) (fun b hb => hu b (by simp [hb])) (by simp)
    have h := loop_runsWithin_iter (c := fun s => p (s i))
      (by simpa [readAll, hTi] using hu a (by simp)) h₁ h₂
    refine (h.mono (by simp; omega)).congr_right ?_
    rw [update_update_update_update hij]
    congr 2
    · simp
    · simp
    · cases drest <;> simp

/-- Move left on tape `i`, erasing, while the scanned symbol is not blank. -/
def eraseL [DecidableEq Γ] (i : Fin k) : TM k Γ :=
  loop (fun s => decide (s i ≠ blank)) (actOn i fun _ => (blank, .left))

theorem eraseL_raw [DecidableEq Γ] (i : Fin k) (d : ℕ) (T : Tapes k Γ)
    (hd : ∀ j < d, (T i).cells ((T i).head - j) ≠ blank)
    (hend : (T i).cells ((T i).head - d) = blank) :
    (eraseL i).RunsWithin T (2 * d) (update T i ⟨(T i).head - d,
      fun z => if (T i).head - d < z ∧ z ≤ (T i).head then blank else (T i).cells z⟩) := by
  unfold eraseL
  induction d generalizing T with
  | zero =>
    refine (loop_runsWithin_exit (T := T)
      (by simp at hend; simp [readAll, Tape.read, hend])).congr_right ?_
    conv_lhs => rw [← Function.update_eq_self i T]
    congr 1
    ext z
    · simp
    · simp only [Nat.cast_zero, sub_zero]
      split_ifs with h
      · omega
      · rfl
  | succ d ih =>
    have h₁ := actOn_runsWithin i (fun _ => ((blank : Γ), Move.left)) T
    have := ih (update T i ((T i).act blank .left))
      (fun j hj => by
        have := hd (j + 1) (by omega)
        simp only [Function.update_self, Tape.act_head, Tape.act_cells, Move.offset_left]
        rw [Function.update_of_ne (by omega)]
        rw [show (T i).head + -1 - (j : ℤ) = (T i).head - ((j + 1 : ℕ) : ℤ) by push_cast; ring]
        exact this)
      (by
        simp only [Function.update_self, Tape.act_head, Tape.act_cells, Move.offset_left]
        rw [Function.update_of_ne (by omega)]
        rw [show (T i).head + -1 - (d : ℤ) = (T i).head - ((d + 1 : ℕ) : ℤ) by push_cast; ring]
        exact hend)
    have h := loop_runsWithin_iter (c := fun s => decide (s i ≠ blank))
      (by have := hd 0 (by omega); simp at this; simp [readAll, Tape.read, this]) h₁ this
    refine (h.mono (by omega)).congr_right ?_
    simp only [Function.update_idem, Function.update_self, Tape.act_head, Tape.act_cells,
      Move.offset_left]
    congr 1
    ext z
    · simp; ring
    · simp only [Function.update_apply]
      push_cast
      split_ifs <;> first | rfl | omega

/-- Erase the blank-free word on tape `i` and put the head on position `0`. -/
def erase [DecidableEq Γ] (i : Fin k) : TM k Γ :=
  scanR i (fun a => decide (a ≠ blank)) ;; moveL i ;; eraseL i ;; moveR i

theorem erase_ofWord [DecidableEq Γ] (i : Fin k) {T : Tapes k Γ} {pre rest : List Γ}
    (hT : T i = .ofWord pre rest) (hw : ∀ a ∈ pre ++ rest, a ≠ blank) :
    (erase i).RunsWithin T (2 * rest.length + 2 * (pre ++ rest).length + 2)
      (update T i (.ofWord [] [])) := by
  have h₁ := scanR_ofWord i (fun a => decide (a ≠ blank)) (T := T) (pre := pre) (u := rest)
    (rest := []) (by simpa using hT) (fun a ha => by simpa using hw a (by simp [ha])) (by simp)
  set w := pre ++ rest with hw'
  set T₁ := update T i (Tape.ofWord w []) with hT₁
  have h₂ := moveL_runsWithin i T₁
  set T₂ := update T₁ i ((T₁ i).move .left) with hT₂
  have hT₂i : T₂ i = ⟨(w.length : ℤ) - 1, listCells w⟩ := by
    rw [hT₂, Function.update_self, hT₁, Function.update_self]
    ext
    · simp; ring
    · simp
  have h₃ := eraseL_raw i w.length T₂ (fun j hj => ?_) ?_
  · have h₄ := moveR_runsWithin i (update T₂ i ⟨(T₂ i).head - w.length,
      fun z => if (T₂ i).head - w.length < z ∧ z ≤ (T₂ i).head then blank else (T₂ i).cells z⟩)
    refine ((seq_runsWithin (seq_runsWithin (seq_runsWithin h₁ h₂) h₃) h₄).mono
      (by omega)).congr_right ?_
    simp only [Function.update_idem, Function.update_self, Tape.move_head, Tape.move_cells,
      Move.offset_right, hT₂i]
    rw [hT₂, hT₁, Function.update_idem, Function.update_idem]
    congr 1
    ext z
    · simp
    · simp only [Tape.move_cells, Tape.ofWord_cells, List.append_nil, listCells_nil]
      split_ifs with h
      · rfl
      · rcases not_and_or.mp h with h | h
        · exact listCells_of_neg _ (by omega)
        · exact listCells_of_length_le _ (by omega)
  · rw [hT₂i]
    simp only
    rw [show (w.length : ℤ) - 1 - j = ((w.length - 1 - j : ℕ) : ℤ) by omega,
      listCells_of_lt _ (by omega)]
    exact hw _ (List.getElem_mem _)
  · rw [hT₂i]
    dsimp only
    exact listCells_of_neg _ (by omega)

end TM

end Lax119563Proofs.Machines

end Machines_WordRoutines

/-! ### Formerly `Lax119563Proofs.Machines.Numbers` -/

section Machines_Numbers

/-!
# Binary numbers on tapes

A natural number `m` is stored on a tape as the word `natWord m`, its binary digits least
significant first (`Nat.bits m`, no leading zeros, empty for `0`), normally with the head on
position `0`. Routine: increment (`incr`).
-/

open Lax489179.TuringMachine (Move)
open Lax119563.BinaryEncodings

namespace Lax119563Proofs.Machines

variable {Γ : Type} {k : ℕ}

open Function (update)

/-! ## Binary digits -/

/-- Increment on little-endian digit lists. -/
def incBits : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: incBits l

lemma bits_succ (m : ℕ) : (m + 1).bits = incBits m.bits := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa [incBits, Nat.zero_bits] using Nat.bit1_bits 0
      · rw [Nat.bit1_bits, Nat.bit0_bits n (by omega)]
        rfl
    · rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, Nat.bit0_bits _ (by omega), Nat.bit1_bits,
        ih n (by omega)]
      rfl

lemma incBits_eq (l : List Bool) :
    incBits l = (l.takeWhile id).map (fun _ => false) ++ true :: (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [incBits, ih]

lemma bits_eq_nil_iff (m : ℕ) : m.bits = [] ↔ m = 0 := by
  constructor
  · intro h
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rfl
      · rw [Nat.bit0_bits n (by omega)] at h; cases h
    · rw [Nat.bit1_bits] at h; cases h
  · rintro rfl; exact Nat.zero_bits

/-- The value of a little-endian digit list. -/
def valBits : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * valBits l

lemma valBits_bits (m : ℕ) : valBits m.bits = m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [Nat.zero_bits, valBits]
      · rw [Nat.bit0_bits n (by omega), valBits, ih n (by omega)]
        simp
    · rw [Nat.bit1_bits, valBits, ih n (by omega)]
      simp; ring

lemma bits_injective : Function.Injective Nat.bits := by
  intro a b h
  rw [← valBits_bits a, ← valBits_bits b, h]

variable [TapeAlphabet Γ]

/-- The word of the binary digits of `m`, least significant first. -/
def natWord (m : ℕ) : List Γ := (Nat.bits m).map bit

/-- The word of a list of bits. -/
def bitsWord (l : List Bool) : List Γ := l.map bit

lemma bit_ne_blank_of_mem_bitsWord {l : List Bool} {a : Γ} (ha : a ∈ bitsWord l) :
    a ≠ blank := by
  simp only [bitsWord, List.mem_map] at ha
  obtain ⟨b, -, rfl⟩ := ha
  simp

lemma mem_natWord_ne_blank {m : ℕ} {a : Γ} (ha : a ∈ natWord m) : a ≠ blank :=
  bit_ne_blank_of_mem_bitsWord ha

namespace TM

variable [DecidableEq Γ]

/-! ## Increment -/

/-- Increment the number on tape `i` (head on position `0`; the head returns there). -/
def incr (i : Fin k) : TM k Γ :=
  loop (fun s => decide (s i = bit true)) (writeR i (bit false)) ;; write i (bit true) ;;
    rewind i

theorem incrLoop_ofWord (i : Fin k) (l : List Bool) {T : Tapes k Γ} {pre : List Γ}
    (hT : T i = .ofWord pre (bitsWord l)) :
    (loop (fun s => decide (s i = bit true)) (writeR i (bit false))).RunsWithin T
      (2 * (l.takeWhile id).length)
      (update T i (.ofWord (pre ++ bitsWord ((l.takeWhile id).map fun _ => false))
        (bitsWord (l.dropWhile id)))) := by
  induction l generalizing pre T with
  | nil =>
    refine (loop_runsWithin_exit (by simp [readAll, hT, bitsWord])).congr_right ?_
    rw [eq_comm, Function.update_eq_self_iff, hT]
    simp [bitsWord]
  | cons b l ih =>
    cases b with
    | false =>
      refine (loop_runsWithin_exit (by simp [readAll, hT, bitsWord])).congr_right ?_
      rw [eq_comm, Function.update_eq_self_iff, hT]
      simp [bitsWord]
    | true =>
      have h₁ := writeR_runsWithin i (bit false) T
      rw [hT] at h₁
      simp only [bitsWord, List.map_cons, Tape.act_ofWord_right, List.tail_cons] at h₁
      have h₂ := ih (pre := pre ++ [bit false]) (T := update T i
        (Tape.ofWord (pre ++ [bit false]) (bitsWord l))) (by simp [bitsWord])
      have h := loop_runsWithin_iter (c := fun s => decide (s i = bit true))
        (by simp [readAll, hT, bitsWord]) h₁ h₂
      refine (h.mono (by simp; omega)).congr_right ?_
      simp [bitsWord]

theorem incr_ofWord (i : Fin k) (m : ℕ) {T : Tapes k Γ} (hT : T i = .ofWord [] (natWord m)) :
    (incr i).RunsWithin T (4 * (m.bits.length) + 5) (update T i (.ofWord [] (natWord (m + 1)))) := by
  have h₁ := incrLoop_ofWord i m.bits (pre := []) (by simpa [natWord, bitsWord] using hT)
  set P : List Γ := bitsWord ((m.bits.takeWhile id).map fun _ => false)
  set T₁ := update T i (Tape.ofWord ([] ++ P) (bitsWord (m.bits.dropWhile id)))
  have h₂ := write_runsWithin i (bit true) T₁
  have hT₂ : update T₁ i ((T₁ i).act (bit true) .stay) =
      update T i (Tape.ofWord P (bitsWord (true :: (m.bits.dropWhile id).tail))) := by
    simp [T₁, Tape.act_ofWord_stay, bitsWord]
  rw [hT₂] at h₂
  have h₃ := rewind_ofWord i (T := update T i
    (Tape.ofWord P (bitsWord (true :: (m.bits.dropWhile id).tail)))) (pre := P)
    (rest := bitsWord (true :: (m.bits.dropWhile id).tail)) (by simp)
    (fun a ha => by
      simp only [P, bitsWord, List.mem_map] at ha
      obtain ⟨b, -, rfl⟩ := ha; simp)
  have hlen : P.length ≤ m.bits.length := by
    simp only [P, bitsWord, List.length_map]
    exact List.Sublist.length_le (List.takeWhile_sublist _)
  have htw : (m.bits.takeWhile id).length ≤ m.bits.length :=
    List.Sublist.length_le (List.takeWhile_sublist _)
  refine ((seq_runsWithin (seq_runsWithin h₁ h₂) h₃).mono (by omega)).congr_right ?_
  rw [Function.update_idem]
  congr 2
  simp only [P, natWord, bits_succ, incBits_eq, bitsWord, List.map_append, List.map_cons]

/-! ## Equality test -/

/-! ## Writing codes -/

end TM

end Lax119563Proofs.Machines

end Machines_Numbers

/-! ### Formerly `Lax119563Proofs.Machines.Extras` -/

section Machines_Extras

/-!
# Counting the length of a word

* `TM.countLen`: add the length of a word to a counter.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type} {k : ℕ}

open Function (update)

namespace TM

variable [TapeAlphabet Γ]


/-- The `d` cells at and to the left of the head, read from right to left. -/
def _root_.Lax119563Proofs.Machines.Tape.leftWord (t : Tape Γ) : ℕ → List Γ
  | 0 => []
  | d + 1 => t.read :: Tape.leftWord ⟨t.head - 1, t.cells⟩ d

/-- Add the length of the word on tape `i` (from the head on) to the number on tape `c`. -/
def countLen [DecidableEq Γ] (i c : Fin k) : TM k Γ :=
  loop (fun s => decide (s i ≠ blank)) (moveR i ;; incr c)

theorem countLen_ofWord [DecidableEq Γ] {i c : Fin k} (hic : i ≠ c) (w : List Γ)
    (hw : ∀ a ∈ w, a ≠ blank) : ∀ (pre : List Γ) (m : ℕ) (T : Tapes k Γ),
    T i = .ofWord pre w → T c = .ofWord [] (natWord m) →
    (countLen i c).RunsWithin T (w.length * (4 * Nat.size (m + w.length) + 7))
      (update (update T i (.ofWord (pre ++ w) [])) c (.ofWord [] (natWord (m + w.length)))) := by
  induction w with
  | nil =>
    intro pre m T hTi hTc
    unfold countLen
    refine ((loop_runsWithin_exit (c := fun s => decide (s i ≠ blank)) (B := moveR i ;; incr c)
      (T := T) (by simp [readAll, hTi])).mono (Nat.zero_le _)).congr_right ?_
    funext l
    by_cases hl : l = c
    · subst hl; simp [hTc]
    · by_cases hl' : l = i
      · subst hl'; simp [Function.update_of_ne hl, hTi]
      · simp [Function.update_of_ne hl, Function.update_of_ne hl']
  | cons a w ih =>
    intro pre m T hTi hTc
    have ha : a ≠ blank := hw a (by simp)
    have h₁ := moveR_runsWithin i T
    rw [hTi, Tape.move_ofWord_right] at h₁
    have h₂ := incr_ofWord c m (T := update T i (Tape.ofWord (pre ++ [a]) w))
      (by simp [Function.update_of_ne hic.symm, hTc])
    have h₃ := ih (fun b hb => hw b (by simp [hb])) (pre ++ [a]) (m + 1)
      (update (update T i (Tape.ofWord (pre ++ [a]) w)) c (Tape.ofWord [] (natWord (m + 1))))
      (by simp [Function.update_of_ne hic]) (by simp)
    have h := loop_runsWithin_iter (c := fun s => decide (s i ≠ blank))
      (by simp [readAll, hTi, ha]) (seq_runsWithin h₁ h₂) h₃
    have hsize : m.bits.length ≤ Nat.size (m + (a :: w).length) := by
      rw [Nat.size_eq_bits_len]; exact Nat.size_le_size (by simp)
    refine (h.mono ?_).congr_right ?_
    · have e : m + 1 + w.length = m + (a :: w).length := by simp; ring
      rw [e]
      simp only [List.length_cons] at hsize ⊢
      nlinarith
    · rw [update_update_update_update hic]
      simp [show m + 1 + w.length = m + (w.length + 1) by ring]

end TM

end Lax119563Proofs.Machines

end Machines_Extras

/-! ### Formerly `Lax119563Proofs.Machines.Output` -/

section Machines_Output

/-!
# The output convention

The input tapes are word tapes (`inputTapes_zero`, `inputTapes_ne_zero`). The routine
`finish o` erases tape `0` and copies the word on tape `o` there; combined with
`TM.computesWithin` this yields the output convention of `ComputesWithin`
(`TM.computesWithin_finish`).
-/

open Lax489179.TuringMachine (Machine)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Machines

variable {Γ : Type} [TapeAlphabet Γ] {k : ℕ}

open Function (update)

lemma inputTapes_zero (x : List Bool) :
    inputTapes (Γ := Γ) k x 0 = .ofWord [] (bitsWord x) := by
  simp [inputTapes, Tape.ofWord, bitsWord]

lemma inputTapes_ne_zero (x : List Bool) {i : Fin (k + 1)} (hi : i ≠ 0) :
    inputTapes (Γ := Γ) k x i = .ofWord [] [] := by
  simp [inputTapes, Tape.ofWord, hi]

namespace TM

variable [DecidableEq Γ]

/-- Replace the content of tape `0` by the word on tape `o`. -/
def finish (o : Fin (k + 1)) : TM (k + 1) Γ :=
  erase 0 ;; rewind o ;; copyR o 0 fun a => decide (a ≠ blank)

theorem finish_ofWord {o : Fin (k + 1)} (ho : o ≠ 0) {T : Tapes (k + 1) Γ}
    {pre rest opre orest : List Γ} (h0 : T 0 = .ofWord pre rest)
    (hw : ∀ a ∈ pre ++ rest, a ≠ blank) (hTo : T o = .ofWord opre orest)
    (hy : ∀ a ∈ opre ++ orest, a ≠ blank) :
    ∃ T' : Tapes (k + 1) Γ, (finish o).RunsWithin T
        (2 * rest.length + 2 * (pre ++ rest).length + 2 * opre.length + 2 * (opre ++ orest).length + 4) T' ∧
      T' 0 = .ofWord (opre ++ orest) [] := by
  have h₁ := erase_ofWord 0 h0 hw
  have h₂ := rewind_ofWord o (T := update T 0 (Tape.ofWord [] [])) (pre := opre) (rest := orest)
    (by simp [Function.update_of_ne ho, hTo]) (fun a ha => hy a (by simp [ha]))
  have h₃ := copyR_ofWord ho (fun a => decide (a ≠ blank)) (pre := []) (u := opre ++ orest)
    (rest := []) (dpre := []) (drest := [])
    (T := update (update T 0 (Tape.ofWord [] [])) o (Tape.ofWord [] (opre ++ orest)))
    (by simp) (fun a ha => by simpa using hy a ha) (by simp)
    (by simp [Function.update_of_ne ho.symm])
  refine ⟨_, (seq_runsWithin (seq_runsWithin h₁ h₂) h₃).mono (by simp; omega), by simp⟩

/-- **Output convention for a machine followed by `finish o`.** If `M` runs on the input
tapes of `x` within `t` transitions and leaves a blank-free word on tape `0` and the word of
`y` on tape `o`, then the compiled machine `M ;; finish o` computes `y` from `x`. -/
theorem computesWithin_finish [Fintype Γ] (M : TM (k + 1) Γ) {o : Fin (k + 1)} (ho : o ≠ 0)
    {x y : List Bool} {t : ℕ} {T : Tapes (k + 1) Γ}
    {pre rest opre orest : List Γ}
    (hM : M.RunsWithin (inputTapes k x) t T)
    (h0 : T 0 = .ofWord pre rest) (hw : ∀ a ∈ pre ++ rest, a ≠ blank)
    (hTo : T o = .ofWord opre orest) (hy : opre ++ orest = bitsWord y) :
    ComputesWithin (M ;; finish o).compile x y
      (t + 2 * rest.length + 2 * (pre ++ rest).length + 2 * opre.length +
        2 * (opre ++ orest).length + 4 + 1) := by
  obtain ⟨T', hfin, hT'⟩ := finish_ofWord ho h0 hw hTo
    (by rw [hy]; exact fun a ha => bit_ne_blank_of_mem_bitsWord ha)
  have := (M ;; finish o).computesWithin (fun _ _ => false) (x := x) (y := y)
    (seq_runsWithin hM hfin) (by rw [hT', hy]; simp [bitsWord])
  simpa [Nat.add_assoc, TM.compile] using this

end TM

end Lax119563Proofs.Machines

end Machines_Output

/-! ### Formerly `Lax119563Proofs.Main.Asymptotics` -/

section Main_Asymptotics

/-!
# The running-time estimate for the composed decider

Polylogarithmic factors are absorbed by an arbitrarily small polynomial factor, which yields
the bound `2 t₁ + C t₁^e + C + 3 = O(n^{e + δ})` for `t₁ = C' n (log n)^c`.
-/

namespace Lax119563Proofs.Main

/-- A real power of `log₂ n` is at most a constant times an arbitrarily small power of `n`. -/
theorem natLog_rpow_le (m δ : ℝ) (hm : 0 ≤ m) (hδ : 0 < δ) :
    ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → ((Nat.log 2 n : ℕ) : ℝ) ^ m ≤ K * (n : ℝ) ^ δ := by
  rcases hm.eq_or_lt with rfl | hm
  · refine ⟨1, fun n hn => ?_⟩
    rw [Real.rpow_zero, one_mul]
    exact Real.one_le_rpow (by exact_mod_cast hn) hδ.le
  set η := δ / m with hη
  have hηpos : 0 < η := div_pos hδ hm
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(1 / (η * Real.log 2)) ^ m, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set L : ℕ := Nat.log 2 n
  have hL : (L : ℝ) * Real.log 2 ≤ Real.log n := by
    have h2 : ((2 ^ L : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have := Real.log_le_log (by positivity) h2
    simpa [Real.log_pow] using this
  have hlogn : Real.log n ≤ (n : ℝ) ^ η / η := Real.log_le_rpow_div hn0.le hηpos
  have hLle : (L : ℝ) ≤ 1 / (η * Real.log 2) * (n : ℝ) ^ η := by
    have h1 : (L : ℝ) ≤ Real.log n / Real.log 2 := (le_div_iff₀ hlog2).mpr hL
    calc (L : ℝ) ≤ Real.log n / Real.log 2 := h1
      _ ≤ ((n : ℝ) ^ η / η) / Real.log 2 := by gcongr
      _ = 1 / (η * Real.log 2) * (n : ℝ) ^ η := by field_simp
  calc ((L : ℝ)) ^ m ≤ (1 / (η * Real.log 2) * (n : ℝ) ^ η) ^ m :=
        Real.rpow_le_rpow (by positivity) hLle hm.le
    _ = (1 / (η * Real.log 2)) ^ m * (n : ℝ) ^ δ := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hn0.le, hη,
          div_mul_cancel₀ _ hm.ne']

/-- The total running time of reduction followed by the fast decider is `O(n^{e + δ})`. -/
theorem composed_time_estimate (CR c Cw : ℕ) (e δ : ℝ) (he : 1 ≤ e) (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ n : ℕ, 1 ≤ n →
      2 * ((CR * n * Nat.log 2 n ^ c : ℕ) : ℝ) +
          (Cw * ((CR * n * Nat.log 2 n ^ c : ℕ) : ℝ) ^ e + Cw) + 3 ≤
        K * (n : ℝ) ^ (e + δ) + K := by
  obtain ⟨K₁, hK₁⟩ := natLog_rpow_le c δ (by positivity) hδ
  obtain ⟨K₂, hK₂⟩ := natLog_rpow_le (c * e) δ (by positivity) hδ
  set A : ℝ := 2 * CR * K₁ + Cw * (CR : ℝ) ^ e * K₂
  refine ⟨⌈A⌉₊ + Cw + 3, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set L : ℝ := ((Nat.log 2 n : ℕ) : ℝ)
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hcast : ((CR * n * Nat.log 2 n ^ c : ℕ) : ℝ) = CR * n * L ^ c := by push_cast; rfl
  rw [hcast]
  have hpow := Real.rpow_nonneg hn0.le (e + δ)
  -- the linear term
  have h1 : (CR : ℝ) * n * L ^ c ≤ CR * K₁ * (n : ℝ) ^ (e + δ) := by
    have hLc : L ^ c ≤ K₁ * (n : ℝ) ^ δ := by
      have := hK₁ n hn; rwa [Real.rpow_natCast] at this
    have hn_le : (n : ℝ) * (n : ℝ) ^ δ ≤ (n : ℝ) ^ (e + δ) := by
      rw [Real.rpow_add hn0]
      gcongr
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ e := Real.rpow_le_rpow_of_exponent_le hn1 he
    calc (CR : ℝ) * n * L ^ c ≤ CR * n * (K₁ * (n : ℝ) ^ δ) := by gcongr
      _ = CR * K₁ * (n * (n : ℝ) ^ δ) := by ring
      _ ≤ CR * K₁ * (n : ℝ) ^ (e + δ) := by
          have hK₁0 : 0 ≤ K₁ := by
            by_contra hneg
            rw [not_le] at hneg
            have := mul_neg_of_neg_of_pos hneg (Real.rpow_pos_of_pos hn0 δ)
            have := Real.rpow_nonneg hL0 (c : ℝ)
            linarith [hK₁ n hn]
          gcongr
  -- the power term
  have h2 : ((CR : ℝ) * n * L ^ c) ^ e ≤ (CR : ℝ) ^ e * K₂ * (n : ℝ) ^ (e + δ) := by
    have hLce : (L ^ c) ^ e = L ^ ((c : ℝ) * e) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hn0.le,
      hLce, Real.rpow_add hn0]
    have := hK₂ n hn
    have hcr := Real.rpow_nonneg (Nat.cast_nonneg CR) e
    have hne := Real.rpow_nonneg hn0.le e
    calc (CR : ℝ) ^ e * (n : ℝ) ^ e * L ^ ((c : ℝ) * e)
        ≤ (CR : ℝ) ^ e * (n : ℝ) ^ e * (K₂ * (n : ℝ) ^ δ) := by gcongr
      _ = (CR : ℝ) ^ e * K₂ * ((n : ℝ) ^ e * (n : ℝ) ^ δ) := by ring
  have hA : A ≤ ⌈A⌉₊ := Nat.le_ceil A
  have hCw : (0 : ℝ) ≤ Cw := Nat.cast_nonneg _
  push_cast
  calc 2 * ((CR : ℝ) * n * L ^ c) + (Cw * ((CR : ℝ) * n * L ^ c) ^ e + Cw) + 3
      ≤ 2 * (CR * K₁ * (n : ℝ) ^ (e + δ)) +
          (Cw * ((CR : ℝ) ^ e * K₂ * (n : ℝ) ^ (e + δ)) + Cw) + 3 := by gcongr
    _ = A * (n : ℝ) ^ (e + δ) + Cw + 3 := by ring
    _ ≤ ⌈A⌉₊ * (n : ℝ) ^ (e + δ) + Cw + 3 := by gcongr
    _ ≤ (⌈A⌉₊ + Cw + 3) * (n : ℝ) ^ (e + δ) + (⌈A⌉₊ + Cw + 3) := by
        have : (0 : ℝ) ≤ (Cw + 3) * (n : ℝ) ^ (e + δ) := by positivity
        have : (0 : ℝ) ≤ ⌈A⌉₊ := Nat.cast_nonneg _
        nlinarith

end Lax119563Proofs.Main

end Main_Asymptotics

/-! ### Formerly `Lax119563Proofs.Main.Runs` -/

section Main_Runs

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

end Main_Runs

/-! ### Formerly `Lax119563Proofs.Main.AbstractMachine` -/

section Main_AbstractMachine

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
    DecidesExactlyWithin A.toMachine x P t :=
  ⟨b, by rw [runOn_toMachine]; exact hb, hP⟩

end AMachine

end Lax119563Proofs.Main

end Main_AbstractMachine

/-! ### Formerly `Lax119563Proofs.Main.Compose` -/

section Main_Compose

/-!
# Composing a reduction with a decider

Given deterministic machines `R` (a reduction, computing `y` from `x` on tape `0`) and `D`
(a decider), we build one deterministic machine that, on input `x`,

1. inspects the first two input cells and answers directly on inputs of length `< 2`
   (the answers are fixed parameters), and otherwise marks the origin on an extra tape;
2. simulates `R` on its own tapes, moving the head of the marker tape together with the
   head of tape `0` and remembering on which side of the origin that head is;
3. once `R` halts (its answer is ignored), moves the head of tape `0` back to the origin;
4. simulates `D` on tape `0` and fresh tapes of its own, returning `D`'s answer.

If `R` computes `y` within `t₁` steps and `D` decides `P` on `y` within `t₂` steps, the
composed machine decides `P` on `x` within `2 t₁ + t₂ + 3` steps.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Main.Compose

open AMachine

/-- Control states of the composed machine other than the initial one. -/
inductive St (R D : Machine) : Type
  | chk (b : Bool)
  | sim (q : Fin (R.states + 1)) (sg : Bool)
  | rew (sg : Bool)
  | dec (q : Fin (D.states + 1))
  deriving DecidableEq, Fintype

/-- Tapes of the composed machine other than tape `0`: the tapes `1, …` of `R`, a marker
tape, and the tapes `1, …` of `D`. -/
inductive Tp (R D : Machine) : Type
  | r (j : Fin R.tapes)
  | mk
  | d (j : Fin D.tapes)
  deriving DecidableEq, Fintype

variable (R D : Machine)

/-- The alphabet size parameter of the composed machine. -/
abbrev S : ℕ := max R.symbols D.symbols

/-- Reading a symbol of a larger alphabet in a smaller one (unused symbols become blank). -/
def clamp {m : ℕ} (n : ℕ) (v : Fin m) : Fin (n + 3) :=
  if h : v.val < n + 3 then ⟨v.val, h⟩ else 0

theorem clamp_castLE {n m : ℕ} (h : n + 3 ≤ m) (v : Fin (n + 3)) :
    clamp n (Fin.castLE h v) = v := by
  simp [clamp, v.isLt]

def embR : Fin (R.symbols + 3) → Fin (S R D + 3) :=
  Fin.castLE (Nat.add_le_add_right (le_max_left _ _) 3)

def embD : Fin (D.symbols + 3) → Fin (S R D + 3) :=
  Fin.castLE (Nat.add_le_add_right (le_max_right _ _) 3)

/-- Tape `j` of `R` as a tape of the composed machine. -/
def rT (j : Fin (R.tapes + 1)) : Option (Tp R D) := Fin.cases none (fun j => some (.r j)) j

/-- Tape `j` of `D` as a tape of the composed machine. -/
def dT (j : Fin (D.tapes + 1)) : Option (Tp R D) := Fin.cases none (fun j => some (.d j)) j

@[simp] theorem rT_zero : rT R D 0 = none := rfl
@[simp] theorem rT_succ (j : Fin R.tapes) : rT R D j.succ = some (.r j) := rfl
@[simp] theorem dT_zero : dT R D 0 = none := rfl
@[simp] theorem dT_succ (j : Fin D.tapes) : dT R D j.succ = some (.d j) := rfl

/-- The marker symbol. -/
def mark : Fin (S R D + 3) := 1

/-- The contents of the marker tape: a mark at the origin. -/
def mkTape : ℤ → Fin (S R D + 3) := fun z => if z = 0 then mark R D else 0

theorem mark_ne_zero : mark R D ≠ 0 := by
  simp [mark]

theorem mkTape_eq_mark_iff (z : ℤ) : mkTape R D z = mark R D ↔ z = 0 := by
  unfold mkTape
  split_ifs with h
  · simp [h]
  · simp [h, (mark_ne_zero R D).symm]

variable {R D}

/-- Whether a move goes to the right. -/
def isRight : Move → Bool
  | .right => true
  | _ => false

/-- Writes of a simulated step of `R`. -/
def rWrite (w : Fin (R.tapes + 1) → Fin (R.symbols + 3))
    (sc : Option (Tp R D) → Fin (S R D + 3)) : Option (Tp R D) → Fin (S R D + 3)
  | none => embR R D (w 0)
  | some (.r j) => embR R D (w j.succ)
  | some .mk => sc (some .mk)
  | some (.d j) => sc (some (.d j))

/-- Moves of a simulated step of `R`; the marker head moves with the head of tape `0`. -/
def rMove (m : Fin (R.tapes + 1) → Move) : Option (Tp R D) → Move
  | none => m 0
  | some (.r j) => m j.succ
  | some .mk => m 0
  | some (.d _) => .stay

/-- Writes of a simulated step of `D`. -/
def dWrite (w : Fin (D.tapes + 1) → Fin (D.symbols + 3))
    (sc : Option (Tp R D) → Fin (S R D + 3)) : Option (Tp R D) → Fin (S R D + 3)
  | none => embD R D (w 0)
  | some (.r j) => sc (some (.r j))
  | some .mk => sc (some .mk)
  | some (.d j) => embD R D (w j.succ)

/-- Moves of a simulated step of `D`. -/
def dMove (m : Fin (D.tapes + 1) → Move) : Option (Tp R D) → Move
  | none => m 0
  | some (.r _) => .stay
  | some .mk => .stay
  | some (.d j) => m j.succ

theorem rWrite_rT (w : Fin (R.tapes + 1) → Fin (R.symbols + 3))
    (sc : Option (Tp R D) → Fin (S R D + 3)) (j : Fin (R.tapes + 1)) :
    rWrite w sc (rT R D j) = embR R D (w j) := by
  cases j using Fin.cases <;> rfl

theorem rMove_rT (m : Fin (R.tapes + 1) → Move) (j : Fin (R.tapes + 1)) :
    rMove (D := D) m (rT R D j) = m j := by
  cases j using Fin.cases <;> rfl

theorem dWrite_dT (w : Fin (D.tapes + 1) → Fin (D.symbols + 3))
    (sc : Option (Tp R D) → Fin (S R D + 3)) (j : Fin (D.tapes + 1)) :
    dWrite w sc (dT R D j) = embD R D (w j) := by
  cases j using Fin.cases <;> rfl

theorem dMove_dT (m : Fin (D.tapes + 1) → Move) (j : Fin (D.tapes + 1)) :
    dMove (R := R) m (dT R D j) = m j := by
  cases j using Fin.cases <;> rfl

/-- The transition function of the composed machine; `a₀` and `a₁ b` are the answers on the
inputs `[]` and `[b]`. -/
def δ (a₀ : Bool) (a₁ : Bool → Bool) :
    Option (St R D) → (Option (Tp R D) → Fin (S R D + 3)) → AInstr (St R D) (Tp R D) (S R D)
  | none, sc =>
    if sc none = 0 then .halt a₀
    else .next (some (.chk (decide (sc none = 2))))
      (fun o => if o = some .mk then mark R D else sc o)
      (fun o => if o = none then .right else .stay)
  | some (.chk b), sc =>
    if sc none = 0 then .halt (a₁ b)
    else .next (some (.sim 0 true)) sc (fun o => if o = none then .left else .stay)
  | some (.sim q sg), sc =>
    match R.transition q (fun j => clamp R.symbols (sc (rT R D j))) false with
    | .halt _ => .next (some (.rew sg)) sc (fun _ => .stay)
    | .next q' w m =>
      .next (some (.sim q' (if sc (some .mk) = mark R D then isRight (m 0) else sg)))
        (rWrite w sc) (rMove m)
  | some (.rew sg), sc =>
    if sc (some .mk) = mark R D then .next (some (.dec 0)) sc (fun _ => .stay)
    else .next (some (.rew sg)) sc
      (fun o => if o = none ∨ o = some .mk then (if sg then .left else .right) else .stay)
  | some (.dec q), sc =>
    match D.transition q (fun j => clamp D.symbols (sc (dT R D j))) false with
    | .halt b => .halt b
    | .next q' w m => .next (some (.dec q')) (dWrite w sc) (dMove m)

variable (R D) in
/-- The composed machine, as a structured machine. -/
def comp (a₀ : Bool) (a₁ : Bool → Bool) : AMachine (St R D) (Tp R D) (S R D) := ⟨δ a₀ a₁⟩

end Lax119563Proofs.Main.Compose

end Main_Compose

/-! ### Formerly `Lax119563Proofs.Main.ComposeCorrect` -/

section Main_ComposeCorrect

/-!
# Correctness and running time of the composed machine
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Main.Compose

open AMachine

variable {R D : Machine} {a₀ : Bool} {a₁ : Bool → Bool}

/-- Configurations of the composed machine. -/
abbrev Cfg (R D : Machine) := AConfig (St R D) (Tp R D) (S R D)

/-- The private tapes of `D` are still blank with their heads at the origin. -/
def Fresh (c : Cfg R D) : Prop :=
  ∀ j : Fin D.tapes, c.head (some (.d j)) = 0 ∧ c.tape (some (.d j)) = fun _ => 0

/-- `c` simulates the configuration `d` of `R` (phase 2). -/
def SimR (c : Cfg R D) (d : Config R) : Prop :=
  ∃ sg, c.state = some (.sim d.state sg) ∧ c.answer = none ∧
    (∀ j, c.head (rT R D j) = d.head j ∧ c.tape (rT R D j) = fun z => embR R D (d.tape j z)) ∧
    c.head (some .mk) = d.head 0 ∧ c.tape (some .mk) = mkTape R D ∧ Fresh c ∧
    (0 < d.head 0 → sg = true) ∧ (d.head 0 < 0 → sg = false)

/-- `c` is rewinding tape `0`, which holds `tp`, with the head at `p` (phase 3). -/
def Rew (c : Cfg R D) (tp : ℤ → Fin (S R D + 3)) (p : ℤ) : Prop :=
  ∃ sg, c.state = some (.rew sg) ∧ c.answer = none ∧ c.head none = p ∧ c.tape none = tp ∧
    c.head (some .mk) = p ∧ c.tape (some .mk) = mkTape R D ∧ Fresh c ∧
    (0 < p → sg = true) ∧ (p < 0 → sg = false)

/-- `c` simulates the configuration `e` of `D` (phase 4). -/
def SimD (c : Cfg R D) (e : Config D) : Prop :=
  c.state = some (.dec e.state) ∧ c.answer = e.answer ∧
    ∀ j, c.head (dT R D j) = e.head j ∧ c.tape (dT R D j) = fun z => embD R D (e.tape j z)

theorem offset_bound (m : Move) : -1 ≤ m.offset ∧ m.offset ≤ 1 := by
  cases m <;> simp [Move.offset]

theorem isRight_of_pos (m : Move) (h : 0 < m.offset) : isRight m = true := by
  cases m <;> simp_all [Move.offset, isRight]

theorem isRight_of_neg (m : Move) (h : m.offset < 0) : isRight m = false := by
  cases m <;> simp_all [Move.offset, isRight]

theorem scan_R {c : Cfg R D} {d : Config R}
    (hR : ∀ j, c.head (rT R D j) = d.head j ∧ c.tape (rT R D j) = fun z => embR R D (d.tape j z)) :
    (fun j => clamp R.symbols (c.tape (rT R D j) (c.head (rT R D j)))) =
      fun j => d.tape j (d.head j) := by
  funext j
  rw [(hR j).1, (hR j).2]
  exact clamp_castLE _ _

/-- A non-halting step of `R` is simulated by one step. -/
theorem simR_step_next {c : Cfg R D} {d : Config R} (h : SimR c d) (hd : d.answer = none)
    (hd' : (step R false d).answer = none) :
    SimR ((comp R D a₀ a₁).step c) (step R false d) := by
  obtain ⟨sg, hst, hans, hR, hmkh, hmkt, hfr, hpos, hneg⟩ := h
  cases ht : R.transition d.state (fun j => d.tape j (d.head j)) false with
  | halt b => simp [Lax489179.TuringMachine.step, hd, ht] at hd'
  | next q w m =>
    have hδ : (comp R D a₀ a₁).δ c.state (fun o => c.tape o (c.head o)) =
        .next (some (.sim q (if c.tape (some .mk) (c.head (some .mk)) = mark R D
            then isRight (m 0) else sg)))
          (rWrite w (fun o => c.tape o (c.head o))) (rMove m) := by
      rw [hst]
      simp only [comp, δ]
      rw [scan_R hR, ht]
    rw [step_eq_next _ hans hδ]
    have hd2 : step R false d =
        { state := q
          head := fun j => d.head j + (m j).offset
          tape := fun j z => if z = d.head j then w j else d.tape j z
          answer := none } := by
      simp [Lax489179.TuringMachine.step, hd, ht]
    rw [hd2]
    refine ⟨_, rfl, rfl, fun j => ⟨?_, ?_⟩, ?_, ?_, fun j => ⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [rMove_rT, (hR j).1]
    · funext z
      simp only [rWrite_rT, (hR j).1, (hR j).2]
      split_ifs <;> rfl
    · simp only [rMove, hmkh]
    · simp only [rWrite, hmkt]
      exact write_back _ _
    · simp only [rMove, (hfr j).1, Move.offset]; simp
    · simp only [rWrite, (hfr j).2]
      funext z; split_ifs <;> rfl
    · intro hp
      dsimp only at hp ⊢
      simp only [hmkh, hmkt, mkTape_eq_mark_iff]
      have := offset_bound (m 0)
      split_ifs with h0
      · exact isRight_of_pos _ (by omega)
      · exact hpos (by omega)
    · intro hp
      dsimp only at hp ⊢
      simp only [hmkh, hmkt, mkTape_eq_mark_iff]
      have := offset_bound (m 0)
      split_ifs with h0
      · exact isRight_of_neg _ (by omega)
      · exact hneg (by omega)

/-- The halting step of `R` starts the rewinding phase. -/
theorem simR_step_halt {c : Cfg R D} {d : Config R} (h : SimR c d) (hd : d.answer = none)
    (hd' : (step R false d).answer.isSome) :
    Rew ((comp R D a₀ a₁).step c) (fun z => embR R D ((step R false d).tape 0 z))
      ((step R false d).head 0) := by
  obtain ⟨sg, hst, hans, hR, hmkh, hmkt, hfr, hpos, hneg⟩ := h
  cases ht : R.transition d.state (fun j => d.tape j (d.head j)) false with
  | next q w m => simp [Lax489179.TuringMachine.step, hd, ht] at hd'
  | halt b =>
    have hδ : (comp R D a₀ a₁).δ c.state (fun o => c.tape o (c.head o)) =
        .next (some (.rew sg)) (fun o => c.tape o (c.head o)) (fun _ => .stay) := by
      rw [hst]
      simp only [comp, δ]
      rw [scan_R hR, ht]
    rw [step_eq_next _ hans hδ]
    have hd2 : step R false d = { d with answer := some b } := by
      simp [Lax489179.TuringMachine.step, hd, ht]
    rw [hd2]
    have h0 := hR 0
    simp only [rT_zero] at h0
    refine ⟨sg, rfl, rfl, ?_, ?_, ?_, ?_, fun j => ⟨?_, ?_⟩, hpos, hneg⟩
    · simp [Move.offset, h0.1]
    · exact (write_back _ _).trans h0.2
    · simp [Move.offset, hmkh]
    · exact (write_back _ _).trans hmkt
    · simp [Move.offset, (hfr j).1]
    · exact (write_back _ _).trans (hfr j).2

/-- One rewinding step moves the head of tape `0` towards the origin. -/
theorem rew_step {c : Cfg R D} {tp : ℤ → Fin (S R D + 3)} {p : ℤ} (h : Rew c tp p)
    (hp : p ≠ 0) :
    Rew ((comp R D a₀ a₁).step c) tp (if 0 < p then p - 1 else p + 1) := by
  obtain ⟨sg, hst, hans, hh0, ht0, hmkh, hmkt, hfr, hpos, hneg⟩ := h
  have hnm : ¬ c.tape (some .mk) (c.head (some .mk)) = mark R D := by
    rw [hmkt, hmkh, mkTape_eq_mark_iff]; exact hp
  have hδ : (comp R D a₀ a₁).δ c.state (fun o => c.tape o (c.head o)) =
      .next (some (.rew sg)) (fun o => c.tape o (c.head o))
        (fun o => if o = none ∨ o = some .mk then (if sg then .left else .right) else .stay) := by
    rw [hst]
    simp only [comp, δ]
    rw [if_neg hnm]
  rw [step_eq_next _ hans hδ]
  have hsg : sg = decide (0 < p) := by
    rcases lt_or_gt_of_ne hp with h | h
    · simp [hneg h, not_lt.mpr h.le]
    · simp [hpos h, h]
  refine ⟨sg, rfl, rfl, ?_, ?_, ?_, ?_, fun j => ⟨?_, ?_⟩, ?_, ?_⟩
  · dsimp only
    rw [hh0, hsg]
    by_cases h : 0 < p <;> simp [h, Move.offset]; omega
  · exact (write_back _ _).trans ht0
  · dsimp only
    rw [hmkh, hsg]
    by_cases h : 0 < p <;> simp [h, Move.offset]; omega
  · exact (write_back _ _).trans hmkt
  · simp [Move.offset, (hfr j).1]
  · exact (write_back _ _).trans (hfr j).2
  · intro h; rw [hsg]; split_ifs at h <;> simp <;> omega
  · intro h; rw [hsg]; split_ifs at h <;> simp <;> omega

theorem rew_run {tp : ℤ → Fin (S R D + 3)} :
    ∀ (n : ℕ) (c : Cfg R D) (p : ℤ), p.natAbs = n → Rew c tp p →
      Rew ((comp R D a₀ a₁).run n c) tp 0 := by
  intro n
  induction n with
  | zero =>
    intro c p hp h
    rw [Int.natAbs_eq_zero.mp hp] at h
    exact h
  | succ n ih =>
    intro c p hp h
    have hp0 : p ≠ 0 := by omega
    exact ih _ _ (by split_ifs <;> omega) (rew_step h hp0)

/-- At the origin, the rewinding phase hands over to the simulation of `D` on `y`. -/
theorem simD_of_rew {c : Cfg R D} {y : List Bool}
    (h : Rew c (fun z => embD R D ((init D y).tape 0 z)) 0) :
    SimD ((comp R D a₀ a₁).step c) (init D y) := by
  obtain ⟨sg, hst, hans, hh0, ht0, hmkh, hmkt, hfr, -, -⟩ := h
  have hm : c.tape (some .mk) (c.head (some .mk)) = mark R D := by
    rw [hmkt, hmkh, mkTape_eq_mark_iff]
  have hδ : (comp R D a₀ a₁).δ c.state (fun o => c.tape o (c.head o)) =
      .next (some (.dec 0)) (fun o => c.tape o (c.head o)) (fun _ => .stay) := by
    rw [hst]
    simp only [comp, δ]
    rw [if_pos hm]
  rw [step_eq_next _ hans hδ]
  refine ⟨rfl, rfl, fun j => ?_⟩
  cases j using Fin.cases with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [Move.offset, hh0, Lax489179.TuringMachine.init]
    · exact (write_back _ _).trans ht0
  | succ j =>
    refine ⟨?_, ?_⟩
    · simp [Move.offset, (hfr j).1, Lax489179.TuringMachine.init]
    · refine (write_back _ _).trans ?_
      rw [dT_succ, (hfr j).2]
      funext z
      simp [Lax489179.TuringMachine.init, Fin.succ_ne_zero]; rfl

theorem scan_D {c : Cfg R D} {e : Config D}
    (hD : ∀ j, c.head (dT R D j) = e.head j ∧ c.tape (dT R D j) = fun z => embD R D (e.tape j z)) :
    (fun j => clamp D.symbols (c.tape (dT R D j) (c.head (dT R D j)))) =
      fun j => e.tape j (e.head j) := by
  funext j
  rw [(hD j).1, (hD j).2]
  exact clamp_castLE _ _

/-- A step of `D` is simulated by one step. -/
theorem simD_step {c : Cfg R D} {e : Config D} (h : SimD c e) :
    SimD ((comp R D a₀ a₁).step c) (step D false e) := by
  obtain ⟨hst, hans, hD⟩ := h
  rcases he : e.answer with _ | b
  · rw [he] at hans
    cases ht : D.transition e.state (fun j => e.tape j (e.head j)) false with
    | halt b =>
      have hδ : (comp R D a₀ a₁).δ c.state (fun o => c.tape o (c.head o)) = .halt b := by
        rw [hst]
        simp only [comp, δ]
        rw [scan_D hD, ht]
      rw [step_eq_halt _ hans hδ]
      have he2 : step D false e = { e with answer := some b } := by
        simp [Lax489179.TuringMachine.step, he, ht]
      rw [he2]
      exact ⟨hst, rfl, hD⟩
    | next q w m =>
      have hδ : (comp R D a₀ a₁).δ c.state (fun o => c.tape o (c.head o)) =
          .next (some (.dec q)) (dWrite w (fun o => c.tape o (c.head o))) (dMove m) := by
        rw [hst]
        simp only [comp, δ]
        rw [scan_D hD, ht]
      rw [step_eq_next _ hans hδ]
      have he2 : step D false e =
          { state := q
            head := fun j => e.head j + (m j).offset
            tape := fun j z => if z = e.head j then w j else e.tape j z
            answer := none } := by
        simp [Lax489179.TuringMachine.step, he, ht]
      rw [he2]
      refine ⟨rfl, rfl, fun j => ⟨?_, ?_⟩⟩
      · simp only [dMove_dT, (hD j).1]
      · funext z
        simp only [dWrite_dT, (hD j).1, (hD j).2]
        split_ifs <;> rfl
  · rw [he] at hans
    have h1 : (comp R D a₀ a₁).step c = c := step_of_halted _ c (by simp [hans])
    have h2 : step D false e = e := by simp [Lax489179.TuringMachine.step, he]
    rw [h1, h2]
    exact ⟨hst, by rw [hans, he], hD⟩

theorem simD_run {c : Cfg R D} {e : Config D} (h : SimD c e) (n : ℕ) :
    SimD ((comp R D a₀ a₁).run n c) (run D n (fun _ => false) e) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [AMachine.run_succ, run_false_succ]; exact simD_step ih

end Lax119563Proofs.Main.Compose

end Main_ComposeCorrect

/-! ### Formerly `Lax119563Proofs.Main.ComposeMain` -/

section Main_ComposeMain

/-!
# The composition theorem

If `R` computes `y` from `x` within `t₁` steps and `D` decides `P` on `y` within `t₂` steps,
then the composed machine decides `P` on `x` within `2 t₁ + t₂ + 3` steps, provided
`|x| ≥ 2`; on inputs of length `< 2` it returns its built-in answers within `2` steps.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction step run Deterministic)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Main.Compose

open AMachine

variable {R D : Machine} {a₀ : Bool} {a₁ : Bool → Bool}

/-- Heads move by at most one cell per step. -/
theorem head_natAbs_le (M : Machine) (x : List Bool) (j : Fin (M.tapes + 1)) (t : ℕ) :
    ((runOn M x t).head j).natAbs ≤ t := by
  induction t with
  | zero => simp [runOn, Lax489179.TuringMachine.run, Lax489179.TuringMachine.init]
  | succ t ih =>
    rw [runOn_succ]
    unfold Lax489179.TuringMachine.step
    rcases (runOn M x t).answer with _ | b
    · dsimp only
      split
      · dsimp only; omega
      · dsimp only
        have := offset_bound (‹Fin (M.tapes + 1) → Move› j)
        omega
    · dsimp only; omega

theorem two_ne_zero' : (2 : Fin (S R D + 3)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 2 < S R D + 3 by omega)] at this

theorem one_ne_two' : (1 : Fin (S R D + 3)) ≠ 2 := by
  intro h
  have := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 2 < S R D + 3 by omega)] at this

/-- The symbol of a bit. -/
theorem init_tape_none_cons (b : Bool) (x : List Bool) :
    (AMachine.init (b :: x) : Cfg R D).tape none 0 = if b then 2 else 1 := by
  cases b <;> rfl

theorem init_tape_none_cons_cons (b₀ b : Bool) (x : List Bool) :
    (AMachine.init (b₀ :: b :: x) : Cfg R D).tape none 1 = if b then 2 else 1 := by
  cases b <;> rfl

theorem bitSym_ne_zero (b : Bool) : ((if b then 2 else 1 : Fin (S R D + 3))) ≠ 0 := by
  cases b
  · simp
  · exact two_ne_zero'

theorem decide_bitSym (b : Bool) : decide ((if b then 2 else 1 : Fin (S R D + 3)) = 2) = b := by
  cases b
  · simpa using one_ne_two'
  · simp

/-- The input tape of the composed machine is the embedded input tape of `R`. -/
theorem init_tape_none_embR (x : List Bool) :
    (AMachine.init x : Cfg R D).tape none =
      fun z => embR R D ((Lax489179.TuringMachine.init R x).tape 0 z) := by
  funext z
  simp only [AMachine.init, Lax489179.TuringMachine.init, true_and]
  split_ifs
  · rcases x[z.toNat]? with _ | _ | _ <;> rfl
  · rfl

theorem embR_init_eq_embD_init (y : List Bool) :
    (fun z => embR R D ((Lax489179.TuringMachine.init R y).tape 0 z)) =
      fun z => embD R D ((Lax489179.TuringMachine.init D y).tape 0 z) := by
  funext z
  simp only [Lax489179.TuringMachine.init, true_and]
  split_ifs
  · rcases y[z.toNat]? with _ | _ | _ <;> rfl
  · rfl

/-- After the two inspection steps on an input of length `≥ 2`, the composed machine starts
simulating `R`. -/
theorem simR_init (x : List Bool) (hx : 2 ≤ x.length) :
    SimR ((comp R D a₀ a₁).run 2 (AMachine.init x)) (Lax489179.TuringMachine.init R x) := by
  obtain ⟨b₀, b, x, rfl⟩ : ∃ b₀ b x', x = b₀ :: b :: x' := by
    match x, hx with
    | b₀ :: b :: x', _ => exact ⟨b₀, b, x', rfl⟩
  set c₀ : Cfg R D := AMachine.init (b₀ :: b :: x) with hc₀
  have h0 : c₀.tape none (c₀.head none) = if b₀ then 2 else 1 := init_tape_none_cons b₀ _
  have hδ₁ : (comp R D a₀ a₁).δ c₀.state (fun o => c₀.tape o (c₀.head o)) =
      .next (some (.chk b₀)) (fun o => if o = some .mk then mark R D else c₀.tape o (c₀.head o))
        (fun o => if o = none then .right else .stay) := by
    have hs : c₀.state = none := rfl
    rw [hs]
    simp only [comp, Compose.δ, h0, if_neg (bitSym_ne_zero b₀), decide_bitSym]
  set c₁ := (comp R D a₀ a₁).step c₀ with hc₁
  have hc₁' := step_eq_next (comp R D a₀ a₁) (c := c₀) rfl hδ₁
  have h1 : c₁.tape none (c₁.head none) = if b then 2 else 1 := by
    rw [hc₁, hc₁']
    exact init_tape_none_cons_cons b₀ b x
  have hδ₂ : (comp R D a₀ a₁).δ c₁.state (fun o => c₁.tape o (c₁.head o)) =
      .next (some (.sim 0 true)) (fun o => c₁.tape o (c₁.head o))
        (fun o => if o = none then .left else .stay) := by
    have hs : c₁.state = some (.chk b₀) := by rw [hc₁, hc₁']
    rw [hs]
    simp only [comp, Compose.δ, h1, if_neg (bitSym_ne_zero b)]
  have hc₂ := step_eq_next (comp R D a₀ a₁) (c := c₁) (by rw [hc₁, hc₁']) hδ₂
  show SimR ((comp R D a₀ a₁).step c₁) _
  rw [hc₂]
  rw [hc₁, hc₁']
  refine ⟨true, rfl, rfl, fun j => ⟨?_, ?_⟩, ?_, ?_, fun j => ⟨?_, ?_⟩, ?_, ?_⟩
  · cases j using Fin.cases <;> simp [Move.offset, hc₀, AMachine.init, Lax489179.TuringMachine.init]
  · refine (write_back _ _).trans ?_
    funext z
    cases j using Fin.cases with
    | zero =>
      simp only [rT_zero, reduceCtorEq, if_false]
      rw [← congrFun (init_tape_none_embR (R := R) (D := D) (b₀ :: b :: x)) z]
      split_ifs with hz
      · rw [hz]
      · rfl
    | succ j =>
      simp [hc₀, AMachine.init, Lax489179.TuringMachine.init, Fin.succ_ne_zero]
      rfl
  · simp [Move.offset, hc₀, AMachine.init, Lax489179.TuringMachine.init]
  · refine (write_back _ _).trans ?_
    funext z
    simp [hc₀, AMachine.init, mkTape]
  · simp [Move.offset, hc₀, AMachine.init]
  · refine (write_back _ _).trans ?_
    funext z
    simp [hc₀, AMachine.init]
  · simp [Lax489179.TuringMachine.init]
  · simp [Lax489179.TuringMachine.init]

theorem answer_nil : ((comp R D a₀ a₁).run 1 (AMachine.init [])).answer = some a₀ := by
  have hδ : (comp R D a₀ a₁).δ (AMachine.init [] : Cfg R D).state
      (fun o => (AMachine.init [] : Cfg R D).tape o ((AMachine.init [] : Cfg R D).head o)) =
      .halt a₀ := by
    have hs : (AMachine.init [] : Cfg R D).state = none := rfl
    rw [hs]
    simp only [comp, Compose.δ]
    exact if_pos rfl
  show ((comp R D a₀ a₁).step _).answer = _
  rw [step_eq_halt _ rfl hδ]

theorem answer_single (b : Bool) :
    ((comp R D a₀ a₁).run 2 (AMachine.init [b])).answer = some (a₁ b) := by
  set c₀ : Cfg R D := AMachine.init [b] with hc₀
  have h0 : c₀.tape none (c₀.head none) = if b then 2 else 1 := init_tape_none_cons b _
  have hδ₁ : (comp R D a₀ a₁).δ c₀.state (fun o => c₀.tape o (c₀.head o)) =
      .next (some (.chk b)) (fun o => if o = some .mk then mark R D else c₀.tape o (c₀.head o))
        (fun o => if o = none then .right else .stay) := by
    have hs : c₀.state = none := rfl
    rw [hs]
    simp only [comp, Compose.δ, h0, if_neg (bitSym_ne_zero b), decide_bitSym]
  set c₁ := (comp R D a₀ a₁).step c₀ with hc₁
  have hc₁' := step_eq_next (comp R D a₀ a₁) (c := c₀) rfl hδ₁
  have h1 : c₁.tape none (c₁.head none) = 0 := by
    rw [hc₁, hc₁']
    rfl
  have hδ₂ : (comp R D a₀ a₁).δ c₁.state (fun o => c₁.tape o (c₁.head o)) = .halt (a₁ b) := by
    have hs : c₁.state = some (.chk b) := by rw [hc₁, hc₁']
    rw [hs]
    simp only [comp, Compose.δ, h1, if_true]
  show ((comp R D a₀ a₁).step c₁).answer = _
  rw [step_eq_halt _ (by rw [hc₁, hc₁']) hδ₂]

/-- **Composition.** -/
theorem compose_decidesWithin (R D : Machine) (a₀ : Bool) (a₁ : Bool → Bool)
    {x y : List Bool} {P : Prop} {t₁ t₂ : ℕ} (hx : 2 ≤ x.length)
    (hR : ComputesWithin R x y t₁) (hD : DecidesExactlyWithin D y P t₂) :
    DecidesExactlyWithin (comp R D a₀ a₁).toMachine x P (2 * t₁ + t₂ + 3) := by
  classical
  have hex : ∃ t, (runOn R x t).answer.isSome := ⟨t₁, hR.1⟩
  have hth : (runOn R x (Nat.find hex)).answer.isSome := Nat.find_spec hex
  have hth_le : Nat.find hex ≤ t₁ := Nat.find_min' hex hR.1
  have hbefore : ∀ t < Nat.find hex, (runOn R x t).answer = none := fun t ht => by
    have := Nat.find_min hex ht
    simpa using this
  obtain ⟨t', ht'⟩ : ∃ t', Nat.find hex = t' + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    rw [h0] at hth
    simp [runOn, Lax489179.TuringMachine.run, Lax489179.TuringMachine.init] at hth
  rw [ht'] at hth hth_le hbefore
  have hsim : ∀ t ≤ t', SimR ((comp R D a₀ a₁).run (2 + t) (AMachine.init x)) (runOn R x t) := by
    intro t
    induction t with
    | zero => intro _; exact simR_init x hx
    | succ t ih =>
      intro ht
      rw [← Nat.add_assoc, AMachine.run_succ, runOn_succ]
      exact simR_step_next (ih (by omega)) (hbefore t (by omega))
        (by rw [← runOn_succ]; exact hbefore (t + 1) (by omega))
  set d := runOn R x (t' + 1) with hd
  have hrew : Rew ((comp R D a₀ a₁).run (2 + t' + 1) (AMachine.init x))
      (fun z => embR R D (d.tape 0 z)) (d.head 0) := by
    rw [AMachine.run_succ, hd, runOn_succ]
    exact simR_step_halt (hsim t' le_rfl) (hbefore t' (by omega))
      (by rw [← runOn_succ]; exact hth)
  have htape : d.tape 0 = (Lax489179.TuringMachine.init R y).tape 0 := by
    rw [hd, ← runOn_eq_of_le R x hth_le hth]
    exact hR.2
  rw [htape, embR_init_eq_embD_init] at hrew
  have hp : (d.head 0).natAbs ≤ t₁ := (head_natAbs_le R x 0 _).trans hth_le
  have hrew0 := rew_run (a₀ := a₀) (a₁ := a₁) _ _ _ rfl hrew
  have hsimD := simD_run (a₀ := a₀) (a₁ := a₁) (simD_of_rew (a₀ := a₀) (a₁ := a₁) hrew0) t₂
  obtain ⟨b, hb, hP⟩ := hD
  have hans := hsimD.2.1
  change _ = (runOn D y t₂).answer at hans
  rw [hb] at hans
  refine decidesWithin_mono (t := 2 + t' + 1 + (d.head 0).natAbs + 1 + t₂) ?_ (by omega)
  refine decidesWithin_toMachine _ x P _ b ?_ hP
  rw [AMachine.run_add, AMachine.run_succ, AMachine.run_add]
  exact hans

/-- **Short inputs.** -/
theorem compose_short (R D : Machine) (Q : List Bool → Prop) [DecidablePred Q]
    (x : List Bool) (hx : x.length < 2) :
    DecidesExactlyWithin (comp R D (decide (Q [])) (fun b => decide (Q [b]))).toMachine x (Q x) 2 := by
  match x, hx with
  | [], _ =>
    refine decidesWithin_mono (t := 1) ?_ (by omega)
    exact decidesWithin_toMachine _ _ _ _ _ answer_nil (by simp)
  | [b], _ =>
    exact decidesWithin_toMachine _ _ _ _ _ (answer_single b) (by simp)

end Lax119563Proofs.Main.Compose

end Main_ComposeMain

/-! ### Formerly `Lax119563Proofs.Bridges.TM2Sim.Sim` -/

section Bridges_TM2Sim_Sim

/-!
# Simulating archive multitape machines by mathlib stack machines: correctness

If `R` computes `y` from the binary input `τi.run τi.start u` within `T` steps, the stack
machine `tm R τi τo` turns `u` into `τo.run τo.start y` within `30 (|u| + T) + 30` steps
(`simulate`). Each transition of `R` is one step of the stack machine; the input, output and
clearing phases are linear in `|u| + T`.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction step run init)
open Lax119563.DeterministicTime
open Turing

namespace Lax119563Proofs.Bridges.TM2Sim

variable {R : Machine} {A : Type} {τi : InTransducer A} {τo : OutTransducer A} [Inhabited A]

/-- The simulation invariant: the variables and stacks represent the configuration `c`, and
every tape is stored in at most `B` entries. -/
def SimRel (c : Config R) (v : Var R A τi τo) (Ls Rs : Fin (R.tapes + 1) → List (G R))
    (B : ℕ) : Prop :=
  v.q = c.state ∧ v.qo = τo.start ∧ (∀ j, TapeRep (c.head j) (c.tape j) (Ls j) (Rs j)) ∧
    OriginRep (c.head 0) (Ls 0) (Rs 0) ∧ ∀ j, (Ls j).length + (Rs j).length ≤ B

/-- The scanned symbols of `R`. -/
def scanOf (c : Config R) : Fin (R.tapes + 1) → Sym R := fun j => c.tape j (c.head j)

lemma instr_scanV {c : Config R} {v : Var R A τi τo} {Ls Rs} {B : ℕ}
    (H : SimRel c v Ls Rs B) :
    instr (scanV v Rs) = R.transition c.state (scanOf c) false := by
  obtain ⟨hq, -, hT, -⟩ := H
  have : (fun i => top (Rs i)) = scanOf c := by
    funext j
    have := (hT j).1 0
    simp only [Nat.cast_zero, add_zero] at this
    simp [scanOf, top, getD_head, this]
  simp [instr, this, hq, scanV]

lemma lax_step_next (c : Config R) (hc : c.answer = none) {q w m}
    (h : R.transition c.state (scanOf c) false = .next q w m) :
    step R false c = ⟨q, fun j => c.head j + (m j).offset,
      fun j z => if z = c.head j then w j else c.tape j z, none⟩ := by
  simp only [step, hc]
  rw [show (fun j => c.tape j (c.head j)) = scanOf c from rfl, h]

lemma lax_step_halt (c : Config R) (hc : c.answer = none) {b}
    (h : R.transition c.state (scanOf c) false = .halt b) :
    step R false c = { c with answer := some b } := by
  simp only [step, hc]
  rw [show (fun j => c.tape j (c.head j)) = scanOf c from rfl, h]

lemma sim_next {c : Config R} {v : Var R A τi τo} {Ls Rs} {B : ℕ} (H : SimRel c v Ls Rs B)
    (hc : c.answer = none) {q w m}
    (h : R.transition c.state (scanOf c) false = .next q w m) :
    ∃ v' Ls' Rs', stepF R A τi τo ⟨some .sim, v, mkStk [] [] [] Ls Rs⟩ =
        some ⟨some .sim, v', mkStk [] [] [] Ls' Rs'⟩ ∧
      SimRel (step R false c) v' Ls' Rs' (B + 2) ∧ (step R false c).answer = none := by
  have hi := instr_scanV H
  rw [h] at hi
  have hh : isHalt (instr (scanV v Rs)) = false := by rw [hi]; rfl
  obtain ⟨o, ho⟩ := step_sim_next v Ls Rs hh
  refine ⟨_, _, _, ho, ?_, by rw [lax_step_next c hc h]⟩
  have hw : ∀ j, wr (scanV v Rs) j = w j := fun j => by simp [wr, hi]
  have hm : ∀ j, mv (scanV v Rs) j = m j := fun j => by simp [mv, hi]
  have hq : nextQ (scanV v Rs) = q := by simp [nextQ, hi]
  obtain ⟨-, hqo, hT, hO, hB⟩ := H
  rw [lax_step_next c hc h]
  refine ⟨by simp [hq], by simpa [scanV] using hqo, fun j => ?_, ?_, fun j => ?_⟩
  · simp only [applyLs, applyRs, List.mem_finRange, if_true, hw, hm]
    exact applyTape_rep (hT j) (w j) (m j)
  · simp only [applyLs, applyRs, List.mem_finRange, if_true, hw, hm]
    exact applyTape_origin hO (w 0) (m 0)
  · simp only [applyLs, applyRs, List.mem_finRange, if_true, hw, hm]
    have := applyTape_length (Ls j) (Rs j) (w j) (m j)
    have := hB j
    omega

/-- Runs of `R` that have not halted are simulated step by step. -/
lemma sim_run {x : List Bool} {v₀ : Var R A τi τo} {Ls₀ Rs₀} {B₀ : ℕ}
    (H₀ : SimRel (runOn R x 0) v₀ Ls₀ Rs₀ B₀) :
    ∀ t, (runOn R x t).answer = none → ∃ v Ls Rs,
      Reaches R A τi τo t ⟨some .sim, v₀, mkStk [] [] [] Ls₀ Rs₀⟩
        ⟨some .sim, v, mkStk [] [] [] Ls Rs⟩ ∧ SimRel (runOn R x t) v Ls Rs (B₀ + 2 * t) := by
  intro t
  induction t with
  | zero => intro _; exact ⟨v₀, Ls₀, Rs₀, reaches_zero _, by simpa using H₀⟩
  | succ t ih =>
    intro ht
    rw [Lax119563Proofs.Main.runOn_succ] at ht ⊢
    have hc : (runOn R x t).answer = none := by
      cases h : (runOn R x t).answer with
      | none => rfl
      | some b => simp [step, h] at ht
    obtain ⟨v, Ls, Rs, hr, H⟩ := ih hc
    cases hI : R.transition (runOn R x t).state (scanOf (runOn R x t)) false with
    | halt b => rw [lax_step_halt _ hc hI] at ht; simp at ht
    | next q w m =>
      obtain ⟨v', Ls', Rs', hs, H', -⟩ := sim_next H hc hI
      refine ⟨v', Ls', Rs', reaches_trans hr (reaches_one hs), ?_⟩
      rw [show B₀ + 2 * (t + 1) = B₀ + 2 * t + 2 by ring]
      exact H'

/-! ## Auxiliary facts -/

lemma inRun_length (u : List A) : ∀ q, (τi.run q u).length ≤ 2 * u.length + 2 := by
  induction u with
  | nil => intro q; simpa [InTransducer.run] using τi.final_len q
  | cons a u ih =>
    intro q
    simp only [InTransducer.run, List.length_append, List.length_cons]
    have := τi.δ_len q a
    have := ih (τi.δ q a).1
    omega

lemma outRun_length (y : List Bool) : ∀ q, (τo.run q y).length ≤ y.length := by
  induction y with
  | nil => intro q; simp [OutTransducer.run]
  | cons b y ih =>
    intro q
    simp only [OutTransducer.run, List.length_append, List.length_cons]
    have := ih (τo.δ q b).1
    cases (τo.δ q b).2 <;> simp <;> omega

lemma bitSym_ne_zero (b : Bool) : bitSym R b ≠ 0 := by
  intro h
  have := bitSym_val (R := R) b
  rw [h] at this
  cases b <;> simp at this

lemma length_le_of_cellSym {l : List (G R)} {y : List Bool}
    (H : ∀ i, (l.getD i (g0 R)).1 = cellSym R y i) : y.length ≤ l.length := by
  by_contra hlt
  push_neg at hlt
  have := H l.length
  rw [List.getD_eq_default _ _ le_rfl] at this
  simp only [cellSym, List.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some] at this
  exact bitSym_ne_zero _ (this.symm.trans rfl)

lemma init_tape_zero (x : List Bool) (i : ℕ) : (init R x).tape 0 (i : ℤ) = cellSym R x i := by
  simp only [init, true_and, Nat.cast_nonneg, if_true, Int.toNat_natCast, cellSym]
  cases x[i]? with
  | none => rfl
  | some b => cases b <;> rfl

lemma init_tape_neg (x : List Bool) (j) (z : ℤ) (hz : z < 0) : (init R x).tape j z = 0 := by
  simp only [init]
  rw [if_neg (by omega)]

lemma init_tape_other (x : List Bool) (j) (hj : j ≠ 0) (z : ℤ) : (init R x).tape j z = 0 := by
  simp only [init]
  rw [if_neg (by tauto)]

lemma getD_map_bitG (x : List Bool) (i : ℕ) :
    ((x.map (bitG (R := R))).getD i (g0 R)).1 = cellSym R x i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, cellSym]
  cases x[i]? <;> rfl

/-! ## The initial invariant -/

/-- The tape stacks after the input phase. -/
def markedInput (x : List Bool) : List (G R) :=
  (top (x.map bitG), true) :: (x.map (bitG (R := R))).tail

lemma simRel_init (x : List Bool) (v : Var R A τi τo) (hq : v.q = 0) (hqo : v.qo = τo.start) :
    SimRel (init R x) v (fun _ => []) (Function.update (fun _ => []) 0 (markedInput x))
      (x.length + 1) := by
  refine ⟨hq, hqo, fun j => ⟨fun i => ?_, fun i => ?_⟩, ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩,
    fun j => ?_⟩
  · rw [show (init R x).head j = 0 from rfl, zero_add]
    by_cases hj : j = 0
    · subst hj
      rw [init_tape_zero x i, Function.update_self]
      rcases i with _ | i
      · simp only [markedInput, List.getD_cons_zero, top]; rw [getD_head, getD_map_bitG]
      · simp only [markedInput, List.getD_cons_succ, getD_tail, getD_map_bitG]
    · rw [init_tape_other x j hj _, Function.update_of_ne hj]
      simp [g0]
  · rw [init_tape_neg x j _ (by simp [init]; omega)]
    simp [g0]
  · simp only [Function.update_self] at hi ⊢
    simp only [markedInput] at hi ⊢
    rcases i with _ | i
    · simp [init]
    · simp [bitG, init]; omega
  · simp at hi
  · simp [init]
  · simp [init, markedInput]
  · by_cases hj : j = 0
    · subst hj; simp [markedInput]
    · simp [Function.update_of_ne hj]

end Lax119563Proofs.Bridges.TM2Sim

end Bridges_TM2Sim_Sim

/-! ### Formerly `Lax119563Proofs.Bridges.TM2Sim.Correct` -/

section Bridges_TM2Sim_Correct

/-!
# Simulating archive multitape machines by mathlib stack machines: the main theorem

`simulate`: if `R` computes `y` from `τi.run τi.start u` within `T` steps, then the stack
machine `tm R τi τo` outputs `τo.run τo.start y` on input `u` within `30 (|u| + T) + 30`
steps.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction step run init)
open Lax119563.DeterministicTime
open Turing

namespace Lax119563Proofs.Bridges.TM2Sim

variable {R : Machine} {A : Type} {τi : InTransducer A} {τo : OutTransducer A} [Inhabited A]

lemma getD_drop (l : List (G R)) (k i : ℕ) :
    (l.drop k).getD i (g0 R) = l.getD (k + i) (g0 R) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **Output phase.** From a simulated configuration in which `R` halts, with tape `0` holding
`y` as an input, the stack machine halts with `τo.run τo.start y` on `io` within
`5 B + 6` steps. -/
lemma output_run {c : Config R} {v : Var R A τi τo} {Ls Rs} {B : ℕ} (H : SimRel c v Ls Rs B)
    {b : Bool} (hI : R.transition c.state (scanOf c) false = .halt b) (y : List Bool)
    (hy : c.tape 0 = (init R y).tape 0) :
    ∃ n ≤ 5 * B + 6, Reaches R A τi τo n ⟨some .sim, v, mkStk [] [] [] Ls Rs⟩
      ⟨none, Var.init R A τi τo, mkStk (τo.run τo.start y) [] [] (fun _ => []) (fun _ => [])⟩ := by
  have hh : isHalt (instr (scanV v Rs)) = true := by rw [instr_scanV H, hI]; rfl
  have h1 := step_sim_halt v Ls Rs hh
  obtain ⟨-, hqo, hT, hO, hB⟩ := H
  obtain ⟨v₁, hqo₁, hr₁⟩ := gather_run (Ls 0) (scanV v Rs) Ls Rs rfl
  set Lst := (Ls 0).reverse ++ Rs 0 with hLst
  have hLen : Lst.length = (Ls 0).length + (Rs 0).length := by simp [hLst]
  have hO3 := hO.2.2.1
  have hO4 := hO.2.2.2
  set k : ℕ := ((Ls 0).length - c.head 0).toNat with hk
  have hkz : (k : ℤ) = (Ls 0).length - c.head 0 := by rw [hk]; omega
  have hkL : k < Lst.length := by rw [hLen]; omega
  have hsplit : Lst = Lst.take k ++ Lst[k] :: Lst.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hkL, List.take_append_drop]
  have hpre : ∀ x ∈ Lst.take k, x.2 = false := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_take, gathered_origin hO (i := i)]
    · simp only [List.length_take] at hi; simp; omega
  have hg : (Lst[k]).2 = true := by
    rw [gathered_origin hO]; simp; omega
  obtain ⟨v₂, hqo₂, hc₂, hr₂⟩ := seek_run (Lst.take k) v₁ (Function.update Ls 0 [])
    (Function.update Rs 0 Lst) Lst[k] (Lst.drop (k + 1)) hpre hg
    (by rw [Function.update_self]; exact hsplit)
  have hfeed : ∀ i : ℕ, ((v₂.cell.getD (g0 R) ::
      (Function.update (Function.update Rs 0 Lst) 0 (Lst.drop (k + 1))) 0).getD i (g0 R)).1 =
      cellSym R y i := by
    intro i
    rw [hc₂, Function.update_self, Option.getD_some, ← List.drop_eq_getElem_cons hkL,
      getD_drop, ← gathered_rep (hT 0) (k + i), hy]
    rw [show c.head 0 - ((Ls 0).length : ℤ) + ((k + i : ℕ) : ℤ) = (i : ℤ) by push_cast; omega]
    exact init_tape_zero y i
  have hylen : y.length ≤ Lst.length := by
    have := length_le_of_cellSym hfeed
    rw [Function.update_self] at this
    simp at this
    omega
  obtain ⟨v₃, rest, hrest, hr₃⟩ := feed_run y v₂ [] (Function.update Ls 0 [])
    (Function.update (Function.update Rs 0 Lst) 0 (Lst.drop (k + 1))) hfeed
  have hq₂ : v₂.qo = τo.start := by rw [hqo₂, hqo₁]; exact hqo
  rw [hq₂, List.append_nil] at hr₃
  obtain ⟨v₄, hr₄⟩ := outRev_run (τo.run τo.start y).reverse v₃ [] (Function.update Ls 0 [])
    (Function.update (Function.update (Function.update Rs 0 Lst) 0 (Lst.drop (k + 1))) 0 rest)
  rw [List.reverse_reverse, List.append_nil] at hr₄
  have hbounds : ∀ j, (Function.update Ls 0 [] j).length ≤ B ∧
      (Function.update (Function.update (Function.update Rs 0 Lst) 0 (Lst.drop (k + 1))) 0 rest
        j).length ≤ B := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp only [Function.update_self, List.length_nil, Nat.zero_le, true_and]
      simp only [Function.update_self, List.length_drop] at hrest
      have := hB 0; omega
    · simp only [Function.update_of_ne hj]
      have := hB j; omega
  obtain ⟨n, hn, v₅, hr₅⟩ := clear_run (τo.run τo.start y) B v₄ _ _ hbounds
  have hr₆ := reaches_one (step_done (τi := τi) (τo := τo) v₅
    (mkStk (τo.run τo.start y) [] [] (fun _ => []) (fun _ => [])))
  have hout := outRun_length (τo := τo) y τo.start
  have hL0 := hB 0
  refine ⟨_, ?_, reaches_succ h1 (reaches_trans hr₁ (reaches_trans hr₂ (reaches_trans hr₃
    (reaches_trans hr₄ (reaches_trans hr₅ hr₆)))))⟩
  simp only [List.length_take, List.length_reverse] at *
  omega


variable [Fintype A]

lemma initList_eq (u : List A) :
    initList (tm R τi τo) u =
      (⟨some .inPop, Var.init R A τi τo, mkStk u [] [] (fun _ => []) (fun _ => [])⟩ :
        Cfg' R A τi τo) := by
  unfold initList
  congr 1
  funext k
  cases k <;> rfl

lemma haltList_eq (l : List A) :
    haltList (tm R τi τo) l =
      (⟨none, Var.init R A τi τo, mkStk l [] [] (fun _ => []) (fun _ => [])⟩ :
        Cfg' R A τi τo) := by
  unfold haltList
  congr 1
  funext k
  cases k <;> rfl

lemma evals_of_reaches {u l : List A} {n : ℕ}
    (h : Reaches R A τi τo n
      ⟨some .inPop, Var.init R A τi τo, mkStk u [] [] (fun _ => []) (fun _ => [])⟩
      ⟨none, Var.init R A τi τo, mkStk l [] [] (fun _ => []) (fun _ => [])⟩) :
    (flip bind (tm R τi τo).step)^[n] (some (initList (tm R τi τo) u)) =
      Option.map (haltList (tm R τi τo)) (some l) := by
  have e1 := initList_eq (R := R) (τi := τi) (τo := τo) u
  have e2 := haltList_eq (R := R) (τi := τi) (τo := τo) l
  unfold Reaches at h
  exact (e1 ▸ e2 ▸ h : _)

/-- **Simulation by a stack machine.** If `R` computes `y` from the binary input
`τi.run τi.start u` within `T` steps, then `tm R τi τo` outputs `τo.run τo.start y` on input
`u` within `30 (|u| + T) + 30` steps. -/
theorem simulate (u : List A) (y : List Bool) (T : ℕ)
    (h : ComputesWithin R (τi.run τi.start u) y T) :
    Nonempty (TM2OutputsInTime (tm R τi τo) u (some (τo.run τo.start y))
      (30 * (u.length + T) + 30)) := by
  classical
  set x := τi.run τi.start u with hx
  -- input phase
  obtain ⟨v₁, hq₁, hqo₁, hr₁⟩ := inPop_run u (Var.init R A τi τo) [] (fun _ => []) (fun _ => [])
  obtain ⟨v₂, hq₂, hqo₂, hr₂⟩ := inRev_run ((x.map bitG).reverse ++ []) v₁
    (fun _ => []) (fun _ => [])
  have hm := reaches_one (step_mark v₂ (fun _ => [])
    (Function.update (fun _ => []) 0 ((((x.map bitG).reverse ++ []).reverse ++ []))))
  have hmk : Function.update (Function.update (fun _ : Fin (R.tapes + 1) => ([] : List (G R))) 0
      (((x.map bitG).reverse ++ []).reverse ++ [])) 0
      ((top ((Function.update (fun _ : Fin (R.tapes + 1) => ([] : List (G R))) 0
        (((x.map bitG).reverse ++ []).reverse ++ [])) 0), true) ::
        ((Function.update (fun _ : Fin (R.tapes + 1) => ([] : List (G R))) 0
          (((x.map bitG).reverse ++ []).reverse ++ [])) 0).tail) =
      Function.update (fun _ : Fin (R.tapes + 1) => ([] : List (G R))) 0 (markedInput x) := by
    simp [markedInput]
  rw [hmk] at hm
  have H₀ : SimRel (τo := τo) (runOn R x 0) { v₂ with cell := (Function.update (fun _ : Fin (R.tapes + 1) => ([] : List (G R))) 0
      (((x.map bitG).reverse ++ []).reverse ++ []) 0).head? } (fun _ => [])
      (Function.update (fun _ : Fin (R.tapes + 1) => ([] : List (G R))) 0 (markedInput x)) (x.length + 1) :=
    simRel_init x _ (by rw [hq₂, hq₁]; rfl) (by rw [hqo₂, hqo₁]; rfl)
  -- the halting time
  have hex : ∃ t, (runOn R x t).answer.isSome := ⟨T, h.1⟩
  have ht₀ : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    simp [runOn, run, init] at this
  set t₁ := Nat.find hex - 1 with ht₁
  have hle : Nat.find hex ≤ T := Nat.find_min' hex h.1
  have hnone : (runOn R x t₁).answer = none := by
    have := Nat.find_min hex (show t₁ < Nat.find hex by omega)
    simpa using this
  obtain ⟨v, Ls, Rs, hr, H⟩ := sim_run H₀ t₁ hnone
  have hsucc : Nat.find hex = t₁ + 1 := by omega
  have hspec := Nat.find_spec hex
  rw [hsucc, Lax119563Proofs.Main.runOn_succ] at hspec
  cases hI : R.transition (runOn R x t₁).state (scanOf (runOn R x t₁)) false with
  | next q w m => rw [lax_step_next _ hnone hI] at hspec; simp at hspec
  | halt b =>
    have hy : (runOn R x t₁).tape 0 = (init R y).tape 0 := by
      have e1 := Lax119563Proofs.Main.runOn_eq_of_le R x hle (Nat.find_spec hex)
      rw [hsucc, Lax119563Proofs.Main.runOn_succ, lax_step_halt _ hnone hI] at e1
      rw [← h.2, e1]
    obtain ⟨n, hn, hro⟩ := output_run H hI y hy
    have hall := reaches_trans hr₁ (reaches_trans hr₂ (reaches_trans hm (reaches_trans hr hro)))
    have hxl := inRun_length (τi := τi) u τi.start
    refine ⟨⟨⟨_, evals_of_reaches hall⟩, ?_⟩⟩
    · simp only [List.length_append, List.length_reverse, List.length_map, List.length_nil,
        add_zero] at hn ⊢
      rw [← hx] at hxl
      omega

end Lax119563Proofs.Bridges.TM2Sim

end Bridges_TM2Sim_Correct
