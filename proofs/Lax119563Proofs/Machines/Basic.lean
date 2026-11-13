import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Lax489179.TuringMachine

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

theorem HaltsFrom.deterministic {q : M.Q} {T T₁ T₂ : Tapes k Γ} {t₁ t₂ : ℕ}
    (h₁ : M.HaltsFrom q T t₁ T₁) (h₂ : M.HaltsFrom q T t₂ T₂) : t₁ = t₂ ∧ T₁ = T₂ := by
  induction h₁ generalizing t₂ with
  | halt h => cases h₂ with
    | halt _ => exact ⟨rfl, rfl⟩
    | step h' _ => simp [h] at h'
  | step h _ ih => cases h₂ with
    | halt h' => simp [h] at h'
    | step h' hr =>
      rw [h] at h'
      cases h'
      obtain ⟨rfl, rfl⟩ := ih hr
      exact ⟨rfl, rfl⟩

theorem HaltsIn.runsWithin {T T' : Tapes k Γ} {t : ℕ} (h : M.HaltsIn T t T') :
    M.RunsWithin T t T' := ⟨t, le_rfl, h⟩

theorem RunsWithin.mono {T T' : Tapes k Γ} {t t' : ℕ} (h : M.RunsWithin T t T')
    (ht : t ≤ t') : M.RunsWithin T t' T' := by
  obtain ⟨s, hs, h⟩ := h; exact ⟨s, hs.trans ht, h⟩

theorem RunsWithin.unique {T T₁ T₂ : Tapes k Γ} {t₁ t₂ : ℕ} (h₁ : M.RunsWithin T t₁ T₁)
    (h₂ : M.RunsWithin T t₂ T₂) : T₁ = T₂ := by
  obtain ⟨_, _, h₁⟩ := h₁; obtain ⟨_, _, h₂⟩ := h₂
  exact (h₁.deterministic h₂).2

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

/-- Branch on a function of the scanned symbols, at no cost. -/
def branch {ι : Type} [Fintype ι] [DecidableEq ι] (g : (Fin k → Γ) → ι)
    (M : ι → TM k Γ) : TM k Γ where
  Q := Option (Σ i, (M i).Q)
  start := none
  δ
    | none, s => ((M (g s)).δ (M (g s)).start s).map fun p => (some ⟨g s, p.1⟩, p.2)
    | some ⟨i, q⟩, s => ((M i).δ q s).map fun p => (some ⟨i, p.1⟩, p.2)

theorem branch_haltsIn {ι : Type} [Fintype ι] [DecidableEq ι] (g : (Fin k → Γ) → ι)
    (M : ι → TM k Γ) {T T' : Tapes k Γ} {t : ℕ}
    (h : (M (g (readAll T))).HaltsIn T t T') : (branch g M).HaltsIn T t T' := by
  have := h.map (N := branch g M) (fun q => some ⟨g (readAll T), q⟩)
    (fun q s q' a hq => by simp [branch, hq]) (t₂ := 0) (T₂ := T')
    (fun q' hq => .halt (by simp [branch, hq]))
  simp only [add_zero] at this
  exact this.congr_state (by simp [branch])

theorem branch_runsWithin {ι : Type} [Fintype ι] [DecidableEq ι] (g : (Fin k → Γ) → ι)
    (M : ι → TM k Γ) {T T' : Tapes k Γ} {t : ℕ}
    (h : (M (g (readAll T))).RunsWithin T t T') : (branch g M).RunsWithin T t T' := by
  obtain ⟨s, hs, h⟩ := h; exact ⟨s, hs, branch_haltsIn g M h⟩

/-- Conditional on a predicate of the scanned symbols, at no cost. -/
def ite (c : (Fin k → Γ) → Bool) (M₁ M₂ : TM k Γ) : TM k Γ :=
  branch c fun b => bif b then M₁ else M₂

theorem ite_runsWithin_true {c : (Fin k → Γ) → Bool} {M₁ M₂ : TM k Γ} {T T' : Tapes k Γ}
    {t : ℕ} (hc : c (readAll T) = true) (h : M₁.RunsWithin T t T') :
    (ite c M₁ M₂).RunsWithin T t T' :=
  branch_runsWithin _ _ (by simpa [hc] using h)

theorem ite_runsWithin_false {c : (Fin k → Γ) → Bool} {M₁ M₂ : TM k Γ} {T T' : Tapes k Γ}
    {t : ℕ} (hc : c (readAll T) = false) (h : M₂.RunsWithin T t T') :
    (ite c M₁ M₂).RunsWithin T t T' :=
  branch_runsWithin _ _ (by simpa [hc] using h)

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

/-- A loop running through a sequence of tape families `f 0, …, f n`: the condition holds
exactly before the `n` iterations, and iteration `i` takes `f i` to `f (i+1)` within
`t i` transitions. -/
theorem loop_runsWithin {c : (Fin k → Γ) → Bool} {B : TM k Γ} (n : ℕ)
    (f : ℕ → Tapes k Γ) (t : ℕ → ℕ)
    (hc : ∀ i < n, c (readAll (f i)) = true) (hn : c (readAll (f n)) = false)
    (hB : ∀ i < n, B.RunsWithin (f i) (t i) (f (i + 1))) :
    (loop c B).RunsWithin (f 0) (∑ i ∈ Finset.range n, (t i + 1)) (f n) := by
  induction n generalizing f t with
  | zero => simpa using loop_runsWithin_exit hn
  | succ n ih =>
    have := ih (fun i => f (i + 1)) (fun i => t (i + 1)) (fun i hi => hc _ (by omega)) hn
      (fun i hi => hB _ (by omega))
    rw [Finset.sum_range_succ']
    have h := loop_runsWithin_iter (hc 0 (by omega)) (hB 0 (by omega)) this
    exact h.mono (by omega)

/-- A loop with a uniform time bound `t` per iteration. -/
theorem loop_runsWithin_const {c : (Fin k → Γ) → Bool} {B : TM k Γ} (n : ℕ)
    (f : ℕ → Tapes k Γ) (t : ℕ)
    (hc : ∀ i < n, c (readAll (f i)) = true) (hn : c (readAll (f n)) = false)
    (hB : ∀ i < n, B.RunsWithin (f i) t (f (i + 1))) :
    (loop c B).RunsWithin (f 0) (n * (t + 1)) (f n) := by
  simpa using loop_runsWithin n f (fun _ => t) hc hn hB

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
