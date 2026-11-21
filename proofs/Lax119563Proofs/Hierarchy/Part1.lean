import Lax119563.DeterministicTime
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases

/-! ### Formerly `Lax119563Proofs.Hierarchy.Run` -/

section Hierarchy_Run

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

end Hierarchy_Run

/-! ### Formerly `Lax119563Proofs.Hierarchy.Chain` -/

section Hierarchy_Chain

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

end Hierarchy_Chain

/-! ### Formerly `Lax119563Proofs.Hierarchy.Mach` -/

section Hierarchy_Mach

/-!
# Machines with typed states and exits

A `Mach k Γ Λ` is a multitape machine with `k` tapes over the alphabet `Γ` and control states
`Λ`.  It has the same step semantics as `Lax489179.TuringMachine`, but a transition may *exit*
after acting; exits are the glue for sequential composition, conditionals and loops.  The
relation `M.Ends q T o T' t` says that started in state `q` on tapes `T`, the machine ends
after exactly `t` transitions with tapes `T'`, by exiting (`o = none`) or by halting with
answer `b` (`o = some b`).
-/

open Lax489179.TuringMachine

namespace Lax119563Proofs.Hierarchy

/-- Heads and tape contents of a `k`-tape machine. -/
@[ext] structure Tapes (k : ℕ) (Γ : Type) where
  head : Fin k → ℤ
  tape : Fin k → ℤ → Γ

namespace Tapes

variable {k : ℕ} {Γ : Type}

/-- The scanned symbols. -/
def read (T : Tapes k Γ) (j : Fin k) : Γ := T.tape j (T.head j)

/-- Write `w` under the heads, then move the heads by `mv`. -/
def apply (T : Tapes k Γ) (w : Fin k → Γ) (mv : Fin k → Move) : Tapes k Γ where
  head j := T.head j + (mv j).offset
  tape j z := if z = T.head j then w j else T.tape j z

@[simp] lemma apply_read_stay (T : Tapes k Γ) : T.apply T.read (fun _ => .stay) = T := by
  ext j z
  · simp [apply, Move.offset]
  · simp only [apply, read]
    split_ifs with h <;> simp [h]

end Tapes

/-- One transition: halt with an answer, or write, move, and continue in a state (`some q`)
or exit (`none`). -/
inductive Act (k : ℕ) (Γ Λ : Type) where
  | halt (b : Bool)
  | act (next : Option Λ) (write : Fin k → Γ) (move : Fin k → Move)

/-- Rename the states of an action. -/
def Act.map {k : ℕ} {Γ Λ Λ' : Type} (f : Λ → Λ') : Act k Γ Λ → Act k Γ Λ'
  | .halt b => .halt b
  | .act q w mv => .act (q.map f) w mv

/-- A machine with typed states. -/
structure Mach (k : ℕ) (Γ Λ : Type) where
  trans : Λ → (Fin k → Γ) → Act k Γ Λ

namespace Mach

variable {k : ℕ} {Γ Λ Λ₁ Λ₂ : Type}

/-- Ending a run: exactly `t` transitions from state `q` on tapes `T`, ending with tapes `T'`,
by exiting (`none`) or halting (`some b`). -/
inductive Ends (M : Mach k Γ Λ) : Λ → Tapes k Γ → Option Bool → Tapes k Γ → ℕ → Prop
  | halt {q : Λ} {T : Tapes k Γ} {b : Bool} :
      M.trans q T.read = .halt b → M.Ends q T (some b) T 1
  | exit {q : Λ} {T : Tapes k Γ} {w : Fin k → Γ} {mv : Fin k → Move} :
      M.trans q T.read = .act none w mv → M.Ends q T none (T.apply w mv) 1
  | next {q q' : Λ} {T : Tapes k Γ} {w : Fin k → Γ} {mv : Fin k → Move} {o : Option Bool}
      {T' : Tapes k Γ} {t : ℕ} :
      M.trans q T.read = .act (some q') w mv → M.Ends q' (T.apply w mv) o T' t →
        M.Ends q T o T' (t + 1)

/-! ## Primitive machines -/

/-- One action depending on the scanned symbols, then exit. -/
def prim (f : (Fin k → Γ) → (Fin k → Γ) × (Fin k → Move)) : Mach k Γ Unit where
  trans _ r := .act none (f r).1 (f r).2

lemma prim_ends (f : (Fin k → Γ) → (Fin k → Γ) × (Fin k → Move)) (T : Tapes k Γ) :
    (prim f).Ends () T none (T.apply (f T.read).1 (f T.read).2) 1 :=
  .exit rfl

/-- Halt with an answer depending on the scanned symbols. -/
def haltWith (f : (Fin k → Γ) → Bool) : Mach k Γ Unit where
  trans _ r := .halt (f r)

lemma haltWith_ends (f : (Fin k → Γ) → Bool) (T : Tapes k Γ) :
    (haltWith f).Ends () T (some (f T.read)) T 1 :=
  .halt rfl

/-! ## Sequential composition -/

/-- Run `M₁`; when it exits, continue with `M₂` from `s₂`. -/
def seq (M₁ : Mach k Γ Λ₁) (M₂ : Mach k Γ Λ₂) (s₂ : Λ₂) : Mach k Γ (Λ₁ ⊕ Λ₂) where
  trans
    | .inl q, r =>
      match M₁.trans q r with
      | .halt b => .halt b
      | .act none w mv => .act (some (.inr s₂)) w mv
      | .act (some q') w mv => .act (some (.inl q')) w mv
    | .inr q, r => (M₂.trans q r).map Sum.inr

lemma seq_right {M₁ : Mach k Γ Λ₁} {M₂ : Mach k Γ Λ₂} {s₂ : Λ₂} {q : Λ₂} {T T' : Tapes k Γ}
    {o : Option Bool} {t : ℕ} (h : M₂.Ends q T o T' t) : (seq M₁ M₂ s₂).Ends (.inr q) T o T' t := by
  induction h with
  | halt h => exact .halt (by simp [seq, h, Act.map])
  | exit h => exact .exit (by simp [seq, h, Act.map])
  | next h _ ih => exact .next (by simp [seq, h, Act.map]) ih

lemma seq_left_exit {M₁ : Mach k Γ Λ₁} {M₂ : Mach k Γ Λ₂} {s₂ : Λ₂} {q : Λ₁}
    {T T₁ T₂ : Tapes k Γ} {o : Option Bool} {t₁ t₂ : ℕ} (h₁ : M₁.Ends q T none T₁ t₁)
    (h₂ : M₂.Ends s₂ T₁ o T₂ t₂) : (seq M₁ M₂ s₂).Ends (.inl q) T o T₂ (t₁ + t₂) := by
  generalize ho : (none : Option Bool) = o' at h₁
  induction h₁ with
  | halt h => cases ho
  | exit h =>
    rw [Nat.add_comm]
    exact .next (by simp [seq, h]) (seq_right h₂)
  | next h _ ih =>
    rw [Nat.add_right_comm]
    exact .next (by simp [seq, h]) (ih h₂ ho)

/-! ## Conditionals and loops -/

/-- Test the scanned symbols (one step without action), then run `M₁` from `s₁` or `M₂`
from `s₂`. -/
def branch (c : (Fin k → Γ) → Bool) (M₁ : Mach k Γ Λ₁) (s₁ : Λ₁) (M₂ : Mach k Γ Λ₂) (s₂ : Λ₂) :
    Mach k Γ (Option (Λ₁ ⊕ Λ₂)) where
  trans
    | none, r => .act (some (some (if c r then .inl s₁ else .inr s₂))) r (fun _ => .stay)
    | some (.inl q), r => (M₁.trans q r).map (fun q => some (.inl q))
    | some (.inr q), r => (M₂.trans q r).map (fun q => some (.inr q))

lemma branch_left_aux {c : (Fin k → Γ) → Bool} {M₁ : Mach k Γ Λ₁} {s₁ : Λ₁} {M₂ : Mach k Γ Λ₂}
    {s₂ : Λ₂} {q : Λ₁} {T T' : Tapes k Γ} {o : Option Bool} {t : ℕ}
    (h : M₁.Ends q T o T' t) : (branch c M₁ s₁ M₂ s₂).Ends (some (.inl q)) T o T' t := by
  induction h with
  | halt h => exact .halt (by simp [branch, h, Act.map])
  | exit h => exact .exit (by simp [branch, h, Act.map])
  | next h _ ih => exact .next (by simp [branch, h, Act.map]) ih

lemma branch_right_aux {c : (Fin k → Γ) → Bool} {M₁ : Mach k Γ Λ₁} {s₁ : Λ₁} {M₂ : Mach k Γ Λ₂}
    {s₂ : Λ₂} {q : Λ₂} {T T' : Tapes k Γ} {o : Option Bool} {t : ℕ}
    (h : M₂.Ends q T o T' t) : (branch c M₁ s₁ M₂ s₂).Ends (some (.inr q)) T o T' t := by
  induction h with
  | halt h => exact .halt (by simp [branch, h, Act.map])
  | exit h => exact .exit (by simp [branch, h, Act.map])
  | next h _ ih => exact .next (by simp [branch, h, Act.map]) ih

lemma branch_true {c : (Fin k → Γ) → Bool} {M₁ : Mach k Γ Λ₁} {s₁ : Λ₁} {M₂ : Mach k Γ Λ₂}
    {s₂ : Λ₂} {T T' : Tapes k Γ} {o : Option Bool} {t : ℕ} (hc : c T.read = true)
    (h : M₁.Ends s₁ T o T' t) : (branch c M₁ s₁ M₂ s₂).Ends none T o T' (t + 1) := by
  refine .next (q' := some (.inl s₁)) (w := T.read) (mv := fun _ => .stay) ?_ ?_
  · simp [branch, hc]
  · rw [Tapes.apply_read_stay]; exact branch_left_aux h

lemma branch_false {c : (Fin k → Γ) → Bool} {M₁ : Mach k Γ Λ₁} {s₁ : Λ₁} {M₂ : Mach k Γ Λ₂}
    {s₂ : Λ₂} {T T' : Tapes k Γ} {o : Option Bool} {t : ℕ} (hc : c T.read = false)
    (h : M₂.Ends s₂ T o T' t) : (branch c M₁ s₁ M₂ s₂).Ends none T o T' (t + 1) := by
  refine .next (q' := some (.inr s₂)) (w := T.read) (mv := fun _ => .stay) ?_ ?_
  · simp [branch, hc]
  · rw [Tapes.apply_read_stay]; exact branch_right_aux h

/-- `while c do M`: test (one step without action); if the test fails exit, otherwise run
`M` from `s` and test again when it exits. -/
def loop (c : (Fin k → Γ) → Bool) (M : Mach k Γ Λ) (s : Λ) : Mach k Γ (Option Λ) where
  trans
    | none, r => .act (if c r then some (some s) else none) r (fun _ => .stay)
    | some q, r =>
      match M.trans q r with
      | .halt b => .halt b
      | .act none w mv => .act (some none) w mv
      | .act (some q') w mv => .act (some (some q')) w mv

lemma loop_false {c : (Fin k → Γ) → Bool} {M : Mach k Γ Λ} {s : Λ} {T : Tapes k Γ}
    (hc : c T.read = false) : (loop c M s).Ends none T none T 1 := by
  have := Ends.exit (M := loop c M s) (q := none) (T := T) (w := T.read) (mv := fun _ => .stay)
    (by simp [loop, hc])
  rwa [Tapes.apply_read_stay] at this

lemma loop_body_exit {c : (Fin k → Γ) → Bool} {M : Mach k Γ Λ} {s : Λ} {q : Λ}
    {T T₁ T₂ : Tapes k Γ} {o : Option Bool} {t₁ t₂ : ℕ} (h₁ : M.Ends q T none T₁ t₁)
    (h₂ : (loop c M s).Ends none T₁ o T₂ t₂) : (loop c M s).Ends (some q) T o T₂ (t₁ + t₂) := by
  generalize ho : (none : Option Bool) = o' at h₁
  induction h₁ with
  | halt h => cases ho
  | exit h =>
    rw [Nat.add_comm]
    exact .next (by simp [loop, h]) h₂
  | next h _ ih =>
    rw [Nat.add_right_comm]
    exact .next (by simp [loop, h]) (ih h₂ ho)

lemma loop_true {c : (Fin k → Γ) → Bool} {M : Mach k Γ Λ} {s : Λ} {T T₁ T₂ : Tapes k Γ}
    {o : Option Bool} {t₁ t₂ : ℕ} (hc : c T.read = true) (h₁ : M.Ends s T none T₁ t₁)
    (h₂ : (loop c M s).Ends none T₁ o T₂ t₂) : (loop c M s).Ends none T o T₂ (t₁ + t₂ + 1) := by
  refine .next (q' := some s) (w := T.read) (mv := fun _ => .stay) ?_ ?_
  · simp [loop, hc]
  · rw [Tapes.apply_read_stay]; exact loop_body_exit h₁ h₂

/-! ## Determinism -/

end Mach

end Lax119563Proofs.Hierarchy

end Hierarchy_Mach

/-! ### Formerly `Lax119563Proofs.Hierarchy.Lax` -/

section Hierarchy_Lax

/-!
# From and to the machines of `Lax489179.TuringMachine`

* `Mach.liftT`: run a machine on the first `a` of `b ≥ a` tapes.
* `Mach.toMachine`: a `Mach` with a start state as a deterministic machine of the model.
* `ofMachine`: a machine of the model as a `Mach` (deterministic behaviour, coin `false`).
* `clocked`: a machine of the model run under a unary clock on an additional last tape.
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime

namespace Lax119563Proofs.Hierarchy

variable {Γ Λ : Type}

/-! ## More tapes -/

namespace Tapes

variable {a b : ℕ}

/-- The first `a` tapes. -/
def restrict (h : a ≤ b) (T : Tapes b Γ) : Tapes a Γ :=
  ⟨fun i => T.head (Fin.castLE h i), fun i => T.tape (Fin.castLE h i)⟩

/-- Replace the first `a` tapes. -/
def overwrite (h : a ≤ b) (T : Tapes b Γ) (T' : Tapes a Γ) : Tapes b Γ :=
  ⟨fun j => if hj : j.val < a then T'.head ⟨j, hj⟩ else T.head j,
   fun j => if hj : j.val < a then T'.tape ⟨j, hj⟩ else T.tape j⟩

/-- Extend a write on the first `a` tapes by writing back the scanned symbol elsewhere. -/
def extW (h : a ≤ b) (r : Fin b → Γ) (w : Fin a → Γ) : Fin b → Γ :=
  fun j => if hj : j.val < a then w ⟨j, hj⟩ else r j

/-- Extend a move on the first `a` tapes by staying elsewhere. -/
def extM (h : a ≤ b) (mv : Fin a → Move) : Fin b → Move :=
  fun j => if hj : j.val < a then mv ⟨j, hj⟩ else .stay

lemma restrict_apply (h : a ≤ b) (T : Tapes b Γ) (w : Fin a → Γ) (mv : Fin a → Move) :
    (T.apply (extW h T.read w) (extM h mv)).restrict h = (T.restrict h).apply w mv := by
  ext i z
  · simp [restrict, apply, extM]
  · simp only [restrict, apply, extW]
    split_ifs <;> simp_all

lemma overwrite_apply_restrict (h : a ≤ b) (T : Tapes b Γ) (w : Fin a → Γ) (mv : Fin a → Move)
    (T' : Tapes a Γ) :
    (T.apply (extW h T.read w) (extM h mv)).overwrite h T' = T.overwrite h T' := by
  ext j z
  · simp only [overwrite, apply, extM]
    split_ifs <;> simp [Move.offset]
  · simp only [overwrite, apply, extW, read]
    split_ifs with h1 h2 <;> simp_all

lemma overwrite_restrict (h : a ≤ b) (T : Tapes b Γ) : T.overwrite h (T.restrict h) = T := by
  ext j z
  · simp only [overwrite, restrict]
    split_ifs <;> rfl
  · simp only [overwrite, restrict]
    split_ifs <;> rfl

lemma overwrite_apply (h : a ≤ b) (T : Tapes b Γ) (w : Fin a → Γ) (mv : Fin a → Move) :
    T.overwrite h ((T.restrict h).apply w mv) = T.apply (extW h T.read w) (extM h mv) := by
  ext j z
  · simp only [overwrite, restrict, apply, extM]
    split_ifs <;> simp [Move.offset]
  · have hc : ∀ (j : Fin b) (hj : j.val < a), Fin.castLE h ⟨j, hj⟩ = j := fun j hj => Fin.ext rfl
    simp only [overwrite, restrict, apply, extW, read]
    split_ifs <;> simp_all

end Tapes

namespace Mach

variable {a b : ℕ}

/-- Run `M` on the first `a` tapes; the others are left unchanged. -/
def liftT (h : a ≤ b) (M : Mach a Γ Λ) : Mach b Γ Λ where
  trans q r :=
    match M.trans q (fun i => r (Fin.castLE h i)) with
    | .halt c => .halt c
    | .act q' w mv => .act q' (Tapes.extW h r w) (Tapes.extM h mv)

lemma liftT_ends (h : a ≤ b) {M : Mach a Γ Λ} {q : Λ} {T : Tapes b Γ} {o : Option Bool}
    {T' : Tapes a Γ} {t : ℕ} (hM : M.Ends q (T.restrict h) o T' t) :
    (liftT h M).Ends q T o (T.overwrite h T') t := by
  generalize hR : T.restrict h = R at hM
  induction hM generalizing T with
  | halt hq =>
    subst hR
    rw [Tapes.overwrite_restrict]
    exact .halt (by simp only [liftT]; rw [show (fun i => T.read (Fin.castLE h i)) =
      (T.restrict h).read from rfl, hq])
  | exit hq =>
    subst hR
    rw [Tapes.overwrite_apply]
    exact .exit (by simp only [liftT]; rw [show (fun i => T.read (Fin.castLE h i)) =
      (T.restrict h).read from rfl, hq])
  | next hq _ ih =>
    subst hR
    refine .next (by simp only [liftT]; rw [show (fun i => T.read (Fin.castLE h i)) =
      (T.restrict h).read from rfl, hq]) ?_
    rw [← Tapes.overwrite_apply_restrict h T]
    exact ih (Tapes.restrict_apply h T _ _)

end Mach

/-! ## A `Mach` as a machine of the model -/

section ToMachine

variable [Fintype Λ]

lemma card_pos_of (s : Λ) : Fintype.card Λ = Fintype.card Λ - 1 + 1 := by
  have : 0 < Fintype.card Λ := Fintype.card_pos_iff.mpr ⟨s⟩
  omega

/-- An enumeration of the states sending the start state `s` to `0`. -/
noncomputable def stateEquiv [DecidableEq Λ] (s : Λ) : Λ ≃ Fin (Fintype.card Λ - 1 + 1) :=
  let e := (Fintype.equivFin Λ).trans (finCongr (card_pos_of s))
  e.trans (Equiv.swap (e s) 0)

lemma stateEquiv_start [DecidableEq Λ] (s : Λ) : stateEquiv s s = 0 := by
  simp [stateEquiv]

variable [DecidableEq Λ] {n m : ℕ}

/-- The machine of the model running `M` from the start state `s`.  Exits are turned into
halting with answer `false` (they are not used by the machines we convert). -/
noncomputable def Mach.toMachine (M : Mach (n + 1) (Fin (m + 3)) Λ) (s : Λ) : Machine where
  tapes := n
  symbols := m
  states := Fintype.card Λ - 1
  transition q r _ :=
    match M.trans ((stateEquiv s).symm q) r with
    | .halt b => .halt b
    | .act (some q') w mv => .next (stateEquiv s q') w mv
    | .act none _ _ => .halt false

lemma Mach.toMachine_deterministic (M : Mach (n + 1) (Fin (m + 3)) Λ) (s : Λ) :
    Deterministic (M.toMachine s) := fun _ _ => rfl

/-- The configuration of `M.toMachine s` in state `q` on tapes `T`. -/
noncomputable def Mach.cfg (M : Mach (n + 1) (Fin (m + 3)) Λ) (s q : Λ)
    (T : Tapes (n + 1) (Fin (m + 3))) : Config (M.toMachine s) :=
  ⟨stateEquiv s q, T.head, T.tape, none⟩

lemma Mach.toMachine_ends {M : Mach (n + 1) (Fin (m + 3)) Λ} {s q : Λ}
    {T T' : Tapes (n + 1) (Fin (m + 3))} {b : Bool} {t : ℕ}
    (h : M.Ends q T (some b) T' t) : (drun (M.toMachine s) t (M.cfg s q T)).answer = some b := by
  generalize ho : (some b : Option Bool) = o at h
  induction h with
  | @halt q T b' hq =>
    cases ho
    rw [drun_succ]
    have : step (M.toMachine s) false (M.cfg s q T) = { M.cfg s q T with answer := some b } := by
      simp only [step, Mach.cfg, Mach.toMachine, Equiv.symm_apply_apply]
      rw [show (fun j => T.tape j (T.head j)) = T.read from rfl, hq]
    rw [this, drun_of_answer rfl]
  | exit hq => cases ho
  | @next q q' T w mv o T' t hq _ ih =>
    rw [drun_succ]
    have : step (M.toMachine s) false (M.cfg s q T) = M.cfg s q' (T.apply w mv) := by
      simp only [step, Mach.cfg, Mach.toMachine, Equiv.symm_apply_apply]
      rw [show (fun j => T.tape j (T.head j)) = T.read from rfl, hq]
      rfl
    rw [this]
    exact ih ho

/-- The tapes of the initial configuration on input `x`. -/
def inputTapes (n m : ℕ) (x : List Bool) : Tapes (n + 1) (Fin (m + 3)) :=
  ⟨fun _ => 0, fun j z =>
    if j = 0 ∧ 0 ≤ z then
      match x[z.toNat]? with
      | none => 0
      | some false => 1
      | some true => 2
    else 0⟩

lemma Mach.init_toMachine (M : Mach (n + 1) (Fin (m + 3)) Λ) (s : Λ) (x : List Bool) :
    init (M.toMachine s) x = M.cfg s s (inputTapes n m x) := by
  simp only [init, Mach.cfg, inputTapes, stateEquiv_start]
  rfl

lemma Mach.toMachine_decides {M : Mach (n + 1) (Fin (m + 3)) Λ} {s : Λ} {x : List Bool}
    {T' : Tapes (n + 1) (Fin (m + 3))} {b : Bool} {t : ℕ}
    (h : M.Ends s (inputTapes n m x) (some b) T' t) :
    (runOn (M.toMachine s) x t).answer = some b := by
  rw [runOn_eq_drun, Mach.init_toMachine]
  exact Mach.toMachine_ends h

end ToMachine

/-! ## A machine of the model as a `Mach` -/

/-- The tapes of a configuration. -/
def tapesOf {M : Machine} (c : Config M) : Tapes (M.tapes + 1) (Fin (M.symbols + 3)) :=
  ⟨c.head, c.tape⟩

/-- `M` as a `Mach` (with coin `false`). -/
def ofMachine (M : Machine) : Mach (M.tapes + 1) (Fin (M.symbols + 3)) (Fin (M.states + 1)) where
  trans q r :=
    match M.transition q r false with
    | .halt b => .halt b
    | .next q' w mv => .act (some q') w mv

lemma ofMachine_ends {M : Machine} {b : Bool} :
    ∀ (t : ℕ) (c : Config M), c.answer = none → (drun M t c).answer = some b →
      ∃ t' ≤ t, ∃ T', (ofMachine M).Ends c.state (tapesOf c) (some b) T' t'
  | 0, c, hc, h => by simp [hc] at h
  | t + 1, c, hc, h => by
    rw [drun_succ] at h
    have hread : (fun j => c.tape j (c.head j)) = (tapesOf c).read := rfl
    rcases htr : M.transition c.state (fun j => c.tape j (c.head j)) false with b' | ⟨q', w, mv⟩
    · have hs : step M false c = { c with answer := some b' } := by
        simp [step, hc, htr]
      rw [hs, drun_of_answer rfl] at h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨1, by omega, _, .halt ?_⟩
      simp only [ofMachine]; rw [← hread, htr]
    · have hs : step M false c = ⟨q', fun j => c.head j + (mv j).offset,
          fun j z => if z = c.head j then w j else c.tape j z, none⟩ := by
        simp [step, hc, htr]
      rw [hs] at h
      obtain ⟨t', ht', T', hE⟩ := ofMachine_ends t _ rfl h
      refine ⟨t' + 1, by omega, T', .next ?_ hE⟩
      simp only [ofMachine]; rw [← hread, htr]

/-! ## Clocked runs -/

/-- `M` run under a clock on the extra last tape: each step needs a nonblank cell under the
clock head, and every non-halting step erases it and moves the clock head right.  When the
clock cell is blank the machine halts with answer `false`. -/
def clocked (M : Machine) :
    Mach (M.tapes + 1 + 1) (Fin (M.symbols + 3)) (Fin (M.states + 1)) where
  trans q r :=
    if r (Fin.last _) = 0 then .halt false else
    match M.transition q (fun j => r j.castSucc) false with
    | .halt b => .halt b
    | .next q' w mv =>
      .act (some q') (Fin.lastCases (motive := fun _ => Fin (M.symbols + 3)) 0 w)
        (Fin.lastCases (motive := fun _ => Move) .right mv)

/-- The clock tape holds exactly `u` nonblank cells from its head on. -/
def ClockOK {k : ℕ} {Γ' : Type} [Zero Γ'] (T : Tapes (k + 1) Γ') (u : ℕ) : Prop :=
  (∀ i < u, T.tape (Fin.last k) (T.head (Fin.last k) + i) ≠ 0) ∧
    T.tape (Fin.last k) (T.head (Fin.last k) + u) = 0

/-- The first tapes of `T` are those of `c`. -/
def Agrees {M : Machine} (T : Tapes (M.tapes + 1 + 1) (Fin (M.symbols + 3))) (c : Config M) :
    Prop :=
  ∀ j, T.head j.castSucc = c.head j ∧ T.tape j.castSucc = c.tape j

/-- A clocked run ends within `u + 1` steps, with the answer of `M` if `M` halts within `u`
steps, and with `false` otherwise. -/
theorem clocked_ends (M : Machine) :
    ∀ (u : ℕ) (c : Config M) (T : Tapes (M.tapes + 1 + 1) (Fin (M.symbols + 3))),
      c.answer = none → Agrees T c → ClockOK T u →
      ∃ T' t, (clocked M).Ends c.state T (some ((drun M u c).answer.getD false)) T' t ∧
        t ≤ u + 1
  | 0, c, T, hc, _, hT => by
    refine ⟨T, 1, .halt ?_, le_refl _⟩
    have : T.read (Fin.last _) = 0 := by simpa [Tapes.read] using hT.2
    simp [clocked, this, hc]
  | u + 1, c, T, hc, hA, hT => by
    have hclk : T.read (Fin.last _) ≠ 0 := by simpa [Tapes.read] using hT.1 0 (by omega)
    have hread : (fun j => T.read j.castSucc) = fun j => c.tape j (c.head j) := by
      funext j; simp [Tapes.read, (hA j).1, (hA j).2]
    rcases htr : M.transition c.state (fun j => c.tape j (c.head j)) false with b' | ⟨q', w, mv⟩
    · refine ⟨T, 1, .halt ?_, by omega⟩
      have hs : step M false c = { c with answer := some b' } := by simp [step, hc, htr]
      rw [drun_succ, hs, drun_of_answer rfl]
      simp only [clocked, hclk, if_false]
      rw [hread, htr]; rfl
    · have hs : step M false c = ⟨q', fun j => c.head j + (mv j).offset,
          fun j z => if z = c.head j then w j else c.tape j z, none⟩ := by
        simp [step, hc, htr]
      set T₁ := T.apply (Fin.lastCases (motive := fun _ => Fin (M.symbols + 3)) 0 w)
        (Fin.lastCases (motive := fun _ => Move) .right mv) with hT₁
      have hA₁ : Agrees T₁ (step M false c) := by
        intro j
        rw [hs]
        refine ⟨?_, ?_⟩
        · simp [hT₁, Tapes.apply, (hA j).1]
        · funext z; simp [hT₁, Tapes.apply, (hA j).1, (hA j).2]
      have hT₁' : ClockOK T₁ u := by
        have hh : T₁.head (Fin.last _) = T.head (Fin.last _) + 1 := by
          simp [hT₁, Tapes.apply, Move.offset]
        refine ⟨fun i hi => ?_, ?_⟩
        · simp only [hT₁, Tapes.apply, Fin.lastCases_last, Move.offset] at hh ⊢
          rw [if_neg (by omega)]
          have := hT.1 (i + 1) (by omega)
          rwa [show T.head (Fin.last _) + 1 + (i : ℤ) = T.head (Fin.last _) + ((i + 1 : ℕ) : ℤ)
            by push_cast; ring]
        · simp only [hT₁, Tapes.apply, Fin.lastCases_last, Move.offset]
          rw [if_neg (by omega)]
          have := hT.2
          rwa [show T.head (Fin.last _) + 1 + (u : ℤ) = T.head (Fin.last _) + ((u + 1 : ℕ) : ℤ)
            by push_cast; ring]
      obtain ⟨T', t, hE, ht⟩ := clocked_ends M u (step M false c) T₁ (by rw [hs]) hA₁ hT₁'
      refine ⟨T', t + 1, .next (q' := q')
        (w := Fin.lastCases (motive := fun _ => Fin (M.symbols + 3)) 0 w)
        (mv := Fin.lastCases (motive := fun _ => Move) .right mv) ?_ ?_, by omega⟩
      · simp only [clocked, hclk, if_false]
        rw [hread, htr]
      · rw [drun_succ]
        rw [hs] at hE ⊢
        exact hE

end Lax119563Proofs.Hierarchy

end Hierarchy_Lax

/-! ### Formerly `Lax119563Proofs.Hierarchy.Stack` -/

section Hierarchy_Stack

/-!
# Stack programs

Structured programs over `K` stacks of symbols `Fin (m + 2)`, compiled to `Mach`.  Stack `i`
lives on tape `i`: its top is under the head, the rest follows to the right, all other cells
are blank.  On the tape, the stack symbol `a` is `a.succ`, and `0` is the blank; so the bits
`false`, `true` of an input are the stack symbols `0`, `1`, and the input tape holds the input
as a stack.

`Prog.Runs p s s' t` is a big-step semantics whose cost `t` is exactly the number of steps of
the compiled machine (`Prog.compile_ends`).
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime

namespace Lax119563Proofs.Hierarchy

variable {K m : ℕ}

/-- Contents of `K` stacks; the head of a list is the top. -/
abbrev Stacks (K m : ℕ) := Fin K → List (Fin (m + 2))

/-- The top symbols. -/
def tops (s : Stacks K m) : Fin K → Option (Fin (m + 2)) := fun i => (s i).head?

/-- A structured stack program.  Conditions inspect the top symbols of all stacks. -/
inductive Prog (K m : ℕ) where
  | skip
  | push (i : Fin K) (a : Fin (m + 2))
  | pop (i : Fin K)
  | seq (p q : Prog K m)
  | ite (c : (Fin K → Option (Fin (m + 2))) → Bool) (p q : Prog K m)
  | loop (c : (Fin K → Option (Fin (m + 2))) → Bool) (body : Prog K m)

namespace Prog

/-- Big-step semantics with exact costs. -/
inductive Runs : Prog K m → Stacks K m → Stacks K m → ℕ → Prop
  | skip {s} : Runs skip s s 1
  | push {i a s} : Runs (push i a) s (Function.update s i (a :: s i)) 2
  | pop {i s} : Runs (pop i) s (Function.update s i (s i).tail) 1
  | seq {p q s₁ s₂ s₃ t₁ t₂} : Runs p s₁ s₂ t₁ → Runs q s₂ s₃ t₂ → Runs (seq p q) s₁ s₃ (t₁ + t₂)
  | iteT {c p q s s' t} : c (tops s) = true → Runs p s s' t → Runs (ite c p q) s s' (t + 1)
  | iteF {c p q s s' t} : c (tops s) = false → Runs q s s' t → Runs (ite c p q) s s' (t + 1)
  | loopF {c p s} : c (tops s) = false → Runs (loop c p) s s 1
  | loopT {c p s₁ s₂ s₃ t₁ t₂} : c (tops s₁) = true → Runs p s₁ s₂ t₁ → Runs (loop c p) s₂ s₃ t₂ →
      Runs (loop c p) s₁ s₃ (t₁ + t₂ + 1)

/-- States of the compiled machine. -/
def St : Prog K m → Type
  | skip => Unit
  | push _ _ => Unit ⊕ Unit
  | pop _ => Unit
  | seq p q => p.St ⊕ q.St
  | ite _ p q => Option (p.St ⊕ q.St)
  | loop _ p => Option p.St

instance instFintypeSt : (p : Prog K m) → Fintype p.St
  | skip => inferInstanceAs (Fintype Unit)
  | push _ _ => inferInstanceAs (Fintype (Unit ⊕ Unit))
  | pop _ => inferInstanceAs (Fintype Unit)
  | seq p q =>
    letI := instFintypeSt p; letI := instFintypeSt q; inferInstanceAs (Fintype (p.St ⊕ q.St))
  | ite _ p q =>
    letI := instFintypeSt p; letI := instFintypeSt q
    inferInstanceAs (Fintype (Option (p.St ⊕ q.St)))
  | loop _ p => letI := instFintypeSt p; inferInstanceAs (Fintype (Option p.St))

instance instDecEqSt : (p : Prog K m) → DecidableEq p.St
  | skip => inferInstanceAs (DecidableEq Unit)
  | push _ _ => inferInstanceAs (DecidableEq (Unit ⊕ Unit))
  | pop _ => inferInstanceAs (DecidableEq Unit)
  | seq p q =>
    letI := instDecEqSt p; letI := instDecEqSt q; inferInstanceAs (DecidableEq (p.St ⊕ q.St))
  | ite _ p q =>
    letI := instDecEqSt p; letI := instDecEqSt q
    inferInstanceAs (DecidableEq (Option (p.St ⊕ q.St)))
  | loop _ p => letI := instDecEqSt p; inferInstanceAs (DecidableEq (Option p.St))

/-- The start state. -/
def start : (p : Prog K m) → p.St
  | skip => ()
  | push _ _ => .inl ()
  | pop _ => ()
  | seq p _ => .inl p.start
  | ite _ _ _ => none
  | loop _ _ => none

end Prog

/-- Decode a tape symbol into an optional stack symbol. -/
def decSym (x : Fin (m + 3)) : Option (Fin (m + 2)) :=
  if h : x = 0 then none else some (x.pred h)

@[simp] lemma decSym_zero : decSym (0 : Fin (m + 3)) = none := by simp [decSym]

@[simp] lemma decSym_succ (a : Fin (m + 2)) : decSym a.succ = some a := by
  simp [decSym, Fin.succ_ne_zero]

/-- The tape cell at offset `d` from the head of a tape holding the stack `l`. -/
def cell (l : List (Fin (m + 2))) (d : ℤ) : Fin (m + 3) :=
  if 0 ≤ d then
    match l[d.toNat]? with
    | some a => a.succ
    | none => 0
  else 0

@[simp] lemma cell_nil (d : ℤ) : cell ([] : List (Fin (m + 2))) d = 0 := by
  unfold cell; split_ifs <;> simp

lemma cell_zero (l : List (Fin (m + 2))) : decSym (cell l 0) = l.head? := by
  cases l <;> simp [cell]

lemma cell_neg (l : List (Fin (m + 2))) {d : ℤ} (hd : d < 0) : cell l d = 0 := by
  simp [cell, not_le.mpr hd]

lemma cell_cons_pos (a : Fin (m + 2)) (l : List (Fin (m + 2))) {d : ℤ} (hd : 0 < d) :
    cell (a :: l) d = cell l (d - 1) := by
  have h1 : (d - 1).toNat + 1 = d.toNat := by omega
  simp only [cell, show 0 ≤ d by omega, show 0 ≤ d - 1 by omega, if_true]
  rw [← h1, List.getElem?_cons_succ]

lemma cell_cons_zero (a : Fin (m + 2)) (l : List (Fin (m + 2))) : cell (a :: l) 0 = a.succ := by
  simp [cell]

/-- The tapes `T` hold the stacks `s` (heads arbitrary). -/
def Rep (s : Stacks K m) (T : Tapes K (Fin (m + 3))) : Prop :=
  ∀ i z, T.tape i z = cell (s i) (z - T.head i)

lemma Rep.tops {s : Stacks K m} {T : Tapes K (Fin (m + 3))} (h : Rep s T) :
    (fun i => decSym (T.read i)) = tops s := by
  funext i
  simp [Tapes.read, h i, cell_zero, Hierarchy.tops]

namespace Prog

/-- Writing back the scanned symbols and staying. -/
def noop (r : Fin K → Fin (m + 3)) : (Fin K → Fin (m + 3)) × (Fin K → Move) :=
  (r, fun _ => .stay)

/-- First half of a push: move the head of tape `i` left. -/
def pushL (i : Fin K) (r : Fin K → Fin (m + 3)) : (Fin K → Fin (m + 3)) × (Fin K → Move) :=
  (r, fun j => if j = i then .left else .stay)

/-- Second half of a push: write `a` on tape `i`. -/
def pushW (i : Fin K) (a : Fin (m + 2)) (r : Fin K → Fin (m + 3)) :
    (Fin K → Fin (m + 3)) × (Fin K → Move) :=
  (Function.update r i a.succ, fun _ => .stay)

/-- A pop: erase the cell under the head of tape `i` and move right. -/
def popA (i : Fin K) (r : Fin K → Fin (m + 3)) : (Fin K → Fin (m + 3)) × (Fin K → Move) :=
  (Function.update r i 0, fun j => if j = i then .right else .stay)

/-- The compiled machine. -/
def compile : (p : Prog K m) → Mach K (Fin (m + 3)) p.St
  | skip => Mach.prim noop
  | push i a => Mach.seq (Mach.prim (pushL i)) (Mach.prim (pushW i a)) ()
  | pop i => Mach.prim (popA i)
  | seq p q => Mach.seq p.compile q.compile q.start
  | ite c p q => Mach.branch (fun r => c (fun i => decSym (r i))) p.compile p.start
      q.compile q.start
  | loop c p => Mach.loop (fun r => c (fun i => decSym (r i))) p.compile p.start

lemma rep_noop {s : Stacks K m} {T : Tapes K (Fin (m + 3))} (h : Rep s T) :
    Rep s (T.apply (noop T.read).1 (noop T.read).2) := by
  simpa [noop] using h

lemma rep_pop {s : Stacks K m} {T : Tapes K (Fin (m + 3))} (h : Rep s T) (i : Fin K) :
    Rep (Function.update s i (s i).tail) (T.apply (popA i T.read).1 (popA i T.read).2) := by
  intro j z
  by_cases hj : j = i
  · subst hj
    simp only [Tapes.apply, popA, Function.update_self, if_true, Move.offset]
    by_cases hz : z = T.head j
    · subst hz; simp [cell_neg]
    · rw [if_neg hz, h j z]
      rcases hs : s j with _ | ⟨a, l⟩
      · simp
      · simp only [List.tail_cons]
        rcases lt_trichotomy (z - T.head j) 0 with hd | hd | hd
        · rw [cell_neg _ hd, cell_neg _ (by omega)]
        · omega
        · rw [cell_cons_pos _ _ hd]; congr 1; ring
  · simp only [Tapes.apply, popA, Function.update_of_ne hj, if_neg hj, Move.offset, add_zero]
    rw [h j z]
    split_ifs with hz
    · subst hz; simp [Tapes.read, h j]
    · rfl

lemma rep_push {s : Stacks K m} {T : Tapes K (Fin (m + 3))} (h : Rep s T) (i : Fin K)
    (a : Fin (m + 2)) :
    let T₁ := T.apply (pushL i T.read).1 (pushL i T.read).2
    Rep (Function.update s i (a :: s i)) (T₁.apply (pushW i a T₁.read).1 (pushW i a T₁.read).2) := by
  intro T₁ j z
  have hT₁ : ∀ j z, T₁.tape j z = T.tape j z := by
    intro j z
    simp only [T₁, Tapes.apply, pushL, Tapes.read]
    split_ifs with hz <;> simp [hz]
  have hT₁h : ∀ j, T₁.head j = T.head j + if j = i then -1 else 0 := by
    intro j; simp only [T₁, Tapes.apply, pushL]; split_ifs <;> simp [Move.offset]
  by_cases hj : j = i
  · subst hj
    simp only [Tapes.apply, pushW, Function.update_self, Move.offset, add_zero]
    rw [hT₁h j, if_pos rfl]
    by_cases hz : z = T.head j + -1
    · rw [if_pos hz]
      rw [show z - (T.head j + -1) = 0 by omega, cell_cons_zero]
    · rw [if_neg hz, hT₁, h j z]
      rcases lt_trichotomy (z - (T.head j + -1)) 0 with hd | hd | hd
      · rw [cell_neg _ hd, cell_neg _ (by omega)]
      · omega
      · rw [cell_cons_pos _ _ hd]; congr 1; ring
  · simp only [Tapes.apply, pushW, Function.update_of_ne hj, Move.offset, add_zero]
    rw [hT₁h j, if_neg hj, add_zero]
    split_ifs with hz
    · simp only [Tapes.read, hT₁]
      rw [hz, hT₁h j, if_neg hj, add_zero, h j]
    · rw [hT₁, h j z]

/-- Correctness of the compiler. -/
theorem compile_ends {p : Prog K m} {s s' : Stacks K m} {t : ℕ} (hp : p.Runs s s' t)
    {T : Tapes K (Fin (m + 3))} (hT : Rep s T) :
    ∃ T', Rep s' T' ∧ p.compile.Ends p.start T none T' t := by
  induction hp generalizing T with
  | skip => exact ⟨_, rep_noop hT, Mach.prim_ends _ _⟩
  | @push i a s =>
    refine ⟨_, rep_push hT i a, ?_⟩
    exact Mach.seq_left_exit (Mach.prim_ends _ _) (Mach.prim_ends _ _)
  | @pop i s => exact ⟨_, rep_pop hT i, Mach.prim_ends _ _⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨T₁, h₁, e₁⟩ := ih₁ hT
    obtain ⟨T₂, h₂, e₂⟩ := ih₂ h₁
    exact ⟨T₂, h₂, Mach.seq_left_exit e₁ e₂⟩
  | iteT hc _ ih =>
    obtain ⟨T', h', e⟩ := ih hT
    refine ⟨T', h', Mach.branch_true ?_ e⟩
    rw [hT.tops]; exact hc
  | iteF hc _ ih =>
    obtain ⟨T', h', e⟩ := ih hT
    refine ⟨T', h', Mach.branch_false ?_ e⟩
    rw [hT.tops]; exact hc
  | loopF hc =>
    refine ⟨T, hT, Mach.loop_false ?_⟩
    rw [hT.tops]; exact hc
  | loopT hc _ _ ih₁ ih₂ =>
    obtain ⟨T₁, h₁, e₁⟩ := ih₁ hT
    obtain ⟨T₂, h₂, e₂⟩ := ih₂ h₁
    refine ⟨T₂, h₂, Mach.loop_true ?_ e₁ e₂⟩
    rw [hT.tops]; exact hc

/-! ## Determinism -/

end Prog

/-! ## Inputs -/

/-- A bit as a stack symbol. -/
def bitSym (m : ℕ) (b : Bool) : Fin (m + 2) := if b then 1 else 0

/-- The stacks at the start on input `x`: stack `0` holds `x`. -/
def inputStacks (K m : ℕ) (x : List Bool) : Stacks (K + 1) m :=
  fun i => if i = 0 then x.map (bitSym m) else []

lemma rep_input (K m : ℕ) (x : List Bool) : Rep (inputStacks K m x) (inputTapes K m x) := by
  intro i z
  simp only [inputTapes, inputStacks, sub_zero]
  by_cases hi : i = 0
  · subst hi
    simp only [true_and, if_true]
    by_cases hz : 0 ≤ z
    · simp only [hz, if_true, cell, List.getElem?_map]
      rcases x[z.toNat]? with _ | _ | _ <;> rfl
    · simp [hz, cell]
  · simp [hi]

end Lax119563Proofs.Hierarchy

end Hierarchy_Stack

/-! ### Formerly `Lax119563Proofs.Hierarchy.Glue` -/

section Hierarchy_Glue

/-!
# Gluing stack programs and machines

* `Prog.toMachine p ans`: run the stack program `p` on the input, then halt with answer
  `ans` of the top symbols.
* `thenRun M E P`: run the preparation program `P`, then the machine `M` on the first tapes.
* `thenClocked M E P`: run `P`, then `M` under a clock whose units `P` leaves on the stack
  just after the tapes of `M`.

In both compositions `P` must leave the new input `x'` on stack `0` and empty stacks on the
other tapes of `M`; by translation invariance the heads need not be at `0`.
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime

namespace Lax119563Proofs.Hierarchy

/-! ## Stack programs as machines -/

section ToMachine

variable {K m : ℕ}

/-- The machine running `p` and then halting with the answer `ans` of the top symbols. -/
noncomputable def Prog.toMachine (p : Prog (K + 1) m)
    (ans : (Fin (K + 1) → Option (Fin (m + 2))) → Bool) : Machine :=
  Mach.toMachine (Mach.seq p.compile (Mach.haltWith (fun r => ans (fun i => decSym (r i)))) ())
    (.inl p.start)

lemma Prog.toMachine_deterministic (p : Prog (K + 1) m)
    (ans : (Fin (K + 1) → Option (Fin (m + 2))) → Bool) : Deterministic (p.toMachine ans) :=
  Mach.toMachine_deterministic _ _

theorem Prog.toMachine_answer {p : Prog (K + 1) m}
    {ans : (Fin (K + 1) → Option (Fin (m + 2))) → Bool} {x : List Bool} {s' : Stacks (K + 1) m}
    {t : ℕ} (h : p.Runs (inputStacks K m x) s' t) :
    (runOn (p.toMachine ans) x (t + 1)).answer = some (ans (tops s')) := by
  obtain ⟨T', hT', hE⟩ := Prog.compile_ends h (rep_input K m x)
  have := Mach.seq_left_exit (M₂ := Mach.haltWith (fun r => ans (fun i => decSym (r i))))
    hE (Mach.haltWith_ends _ T')
  rw [hT'.tops] at this
  exact Mach.toMachine_decides this

end ToMachine

/-! ## Handing over to a machine -/

section Handover

variable (M : Machine)

/-- The stacks `s` hold `x'` on stack `0` and nothing on the other tapes of `M`. -/
def HandsOver {N : ℕ} (s : Stacks N M.symbols) (x' : List Bool) : Prop :=
  ∀ i : Fin N, (i.val = 0 → s i = x'.map (bitSym M.symbols)) ∧
    (1 ≤ i.val → i.val ≤ M.tapes → s i = [])

variable {M}

lemma cell_handsOver {N : ℕ} {s : Stacks N M.symbols} {x' : List Bool} (hs : HandsOver M s x')
    (j : Fin (M.tapes + 1)) (i : Fin N) (hij : i.val = j.val) (d : ℤ) :
    cell (s i) d = (init M x').tape j d := by
  by_cases hj : j = 0
  · subst hj
    rw [(hs i).1 hij]
    simp only [init, true_and]
    by_cases hd : 0 ≤ d
    · simp only [hd, if_true, cell, List.getElem?_map]
      rcases x'[d.toNat]? with _ | _ | _ <;> rfl
    · simp [hd, cell]
  · have : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr (fun h => hj (Fin.ext h))
    rw [(hs i).2 (by omega) (by omega)]
    simp [init, hj]

/-- The first tapes are the initial configuration of `M` on `x'`, shifted. -/
lemma restrict_handsOver {N : ℕ} {s : Stacks N M.symbols} {x' : List Bool}
    (hs : HandsOver M s x') {T : Tapes N (Fin (M.symbols + 3))} (hT : Rep s T)
    (h : M.tapes + 1 ≤ N) :
    T.restrict h = tapesOf (shiftC (fun j => T.head (Fin.castLE h j)) (init M x')) := by
  ext j z
  · simp [Tapes.restrict, tapesOf, shiftC, init]
  · simp only [Tapes.restrict, tapesOf, shiftC]
    rw [hT, cell_handsOver hs j _ rfl]

/-- Run `P`, then `M` on the first `M.tapes + 1` of `M.tapes + 1 + E` tapes. -/
noncomputable def thenRun (M : Machine) (E : ℕ) (P : Prog (M.tapes + E + 1) M.symbols) : Machine :=
  Mach.toMachine (Mach.seq P.compile (Mach.liftT (by omega) (ofMachine M)) 0) (.inl P.start)

lemma thenRun_deterministic (M : Machine) (E : ℕ) (P : Prog (M.tapes + E + 1) M.symbols) :
    Deterministic (thenRun M E P) := Mach.toMachine_deterministic _ _

theorem thenRun_answer {E : ℕ} {P : Prog (M.tapes + E + 1) M.symbols} {y x' : List Bool}
    {s' : Stacks (M.tapes + E + 1) M.symbols} {t tM : ℕ} {b : Bool}
    (hP : P.Runs (inputStacks _ _ y) s' t) (hs : HandsOver M s' x')
    (hM : (runOn M x' tM).answer = some b) :
    (runOn (thenRun M E P) y (t + tM)).answer = some b := by
  obtain ⟨T', hT', hE⟩ := Prog.compile_ends hP (rep_input _ _ y)
  have hle : M.tapes + 1 ≤ M.tapes + E + 1 := by omega
  set c := shiftC (fun j => T'.head (Fin.castLE hle j)) (init M x') with hc
  have hrun : (drun M tM c).answer = some b := by
    rw [hc, drun_shiftC, shiftC_answer]; exact hM
  obtain ⟨t', ht', T'', hE'⟩ := ofMachine_ends tM c rfl hrun
  rw [← restrict_handsOver hs hT' hle] at hE'
  have := Mach.seq_left_exit hE (Mach.liftT_ends hle hE')
  have h2 := Mach.toMachine_decides this
  exact drun_answer_mono h2 (show t + t' ≤ t + tM by omega)

/-- The index of the clock stack. -/
def clockIdx (M : Machine) (E : ℕ) : Fin (M.tapes + 1 + E + 1) := ⟨M.tapes + 1, by omega⟩

/-- Run `P`, then `M` under a clock on stack `clockIdx M E`. -/
noncomputable def thenClocked (M : Machine) (E : ℕ) (P : Prog (M.tapes + 1 + E + 1) M.symbols) : Machine :=
  Mach.toMachine (Mach.seq P.compile (Mach.liftT (by omega) (clocked M)) 0) (.inl P.start)

lemma thenClocked_deterministic (M : Machine) (E : ℕ) (P : Prog (M.tapes + 1 + E + 1) M.symbols) :
    Deterministic (thenClocked M E P) := Mach.toMachine_deterministic _ _

/-- After `P` leaves `x'` and a clock of `u` units, the composite machine answers within
`t + u + 1` steps as `M` does within `u` steps (and `false` if `M` has not halted). -/
theorem thenClocked_answer {E : ℕ} {P : Prog (M.tapes + 1 + E + 1) M.symbols}
    {y x' : List Bool} {s' : Stacks (M.tapes + 1 + E + 1) M.symbols} {t u : ℕ}
    (hP : P.Runs (inputStacks _ _ y) s' t) (hs : HandsOver M s' x')
    (hclk : (s' (clockIdx M E)).length = u) :
    (runOn (thenClocked M E P) y (t + u + 1)).answer =
      some ((runOn M x' u).answer.getD false) := by
  obtain ⟨T', hT', hE⟩ := Prog.compile_ends hP (rep_input _ _ y)
  have hle : M.tapes + 1 + 1 ≤ M.tapes + 1 + E + 1 := by omega
  have hle' : M.tapes + 1 ≤ M.tapes + 1 + E + 1 := by omega
  set c := shiftC (fun j => T'.head (Fin.castLE hle' j)) (init M x') with hc
  have hA : Agrees (T'.restrict hle) c := by
    intro j
    have := congrArg Tapes.head (restrict_handsOver hs hT' hle')
    have h2 := congrArg Tapes.tape (restrict_handsOver hs hT' hle')
    refine ⟨?_, ?_⟩
    · exact congrFun this j
    · exact congrFun h2 j
  have hK : ClockOK (T'.restrict hle) u := by
    have hcl : Fin.castLE hle (Fin.last (M.tapes + 1)) = clockIdx M E := rfl
    refine ⟨fun i hi => ?_, ?_⟩
    · show T'.tape (Fin.castLE hle (Fin.last _)) (T'.head (Fin.castLE hle (Fin.last _)) + i) ≠ 0
      rw [hcl, hT', add_sub_cancel_left]
      simp only [cell, Nat.cast_nonneg, if_true, Int.toNat_natCast]
      rw [List.getElem?_eq_getElem (by omega)]
      exact Fin.succ_ne_zero _
    · show T'.tape (Fin.castLE hle (Fin.last _)) (T'.head (Fin.castLE hle (Fin.last _)) + u) = 0
      rw [hcl, hT', add_sub_cancel_left]
      simp only [cell, Nat.cast_nonneg, if_true, Int.toNat_natCast]
      rw [List.getElem?_eq_none (by omega)]
  obtain ⟨T'', t₂, hE', ht₂⟩ := clocked_ends M u c _ rfl hA hK
  rw [show c.state = 0 from rfl] at hE'
  have := Mach.seq_left_exit hE (Mach.liftT_ends hle hE')
  have h2 := Mach.toMachine_decides this
  have h3 : (runOn (thenClocked M E P) y (t + u + 1)).answer = _ :=
    drun_answer_mono h2 (show t + t₂ ≤ t + u + 1 by omega)
  rw [h3, hc, drun_shiftC, shiftC_answer]
  rfl

end Handover

end Lax119563Proofs.Hierarchy

end Hierarchy_Glue

/-! ### Formerly `Lax119563Proofs.Hierarchy.Locality` -/

section Hierarchy_Locality

/-!
# The linear case

The language of words whose last bit is `true` is decidable in linear time, but not in time
`O(n^a)` for `a < 1`: in fewer than `n - 1` steps a machine never scans the last input cell.
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime Filter Topology

namespace Lax119563Proofs.Hierarchy

/-! ## Locality -/

/-- Two configurations that agree except possibly on cell `p` of tape `0`, with the head of
tape `0` at most `i`. -/
def CloseAt (M : Machine) (p : ℤ) (i : ℕ) (c c' : Config M) : Prop :=
  c.state = c'.state ∧ c.head = c'.head ∧ c.answer = c'.answer ∧
    (∀ j z, ¬ (j = 0 ∧ z = p) → c.tape j z = c'.tape j z) ∧ c.head 0 ≤ i

lemma CloseAt.step {M : Machine} {p : ℤ} {i : ℕ} {c c' : Config M} (h : CloseAt M p i c c')
    (hi : (i : ℤ) < p) : CloseAt M p (i + 1) (step M false c) (step M false c') := by
  obtain ⟨hs, hh, ha, ht, h0⟩ := h
  have hread : (fun j => c.tape j (c.head j)) = fun j => c'.tape j (c'.head j) := by
    funext j
    rw [← hh]
    apply ht
    rintro ⟨rfl, hz⟩
    omega
  unfold Lax489179.TuringMachine.step
  rw [← ha, ← hs, ← hread]
  rcases hca : c.answer with _ | b
  · dsimp only
    rcases M.transition c.state (fun j => c.tape j (c.head j)) false with b | ⟨q, w, mv⟩
    · exact ⟨rfl, hh, rfl, ht, by simp; omega⟩
    · refine ⟨rfl, by rw [hh], rfl, ?_, ?_⟩
      · intro j z hjz
        simp only
        rw [← hh]
        split_ifs
        · rfl
        · exact ht j z hjz
      · simp only
        rcases mv 0 <;> simp [Move.offset] <;> omega
  · dsimp only
    exact ⟨hs, hh, ha, ht, by omega⟩

lemma closeAt_drun {M : Machine} {p : ℤ} :
    ∀ (t i : ℕ) (c c' : Config M), CloseAt M p i c c' → (i + t : ℤ) ≤ p →
      (drun M t c).answer = (drun M t c').answer
  | 0, _, _, _, h, _ => h.2.2.1
  | t + 1, i, c, c', h, hp => by
    rw [drun_succ, drun_succ]
    exact closeAt_drun t (i + 1) _ _ (h.step (by omega)) (by push_cast; omega)

/-! ## The language and its decision -/

/-- Words whose last bit is `true`. -/
def lastTrue : Set (List Bool) := {x | x.getLast? = some true}

/-- Remember the last symbol of stack `0` on stack `1` while emptying stack `0`. -/
def lastProg (m : ℕ) : Prog 2 m :=
  .loop (fun r => (r 0).isSome)
    (.seq (.pop 1) (.seq (.ite (fun r => r 0 == some 1) (.push 1 1) (.push 1 0)) (.pop 0)))

lemma lastProg_runs (m : ℕ) :
    ∀ (l : List (Fin (m + 2))) (s : Stacks 2 m), s 0 = l →
      ∃ s', (lastProg m).Runs s s' (6 * l.length + 1) ∧
        tops s' 1 = match l.getLast? with
          | some a => some (if a = 1 then 1 else 0)
          | none => tops s 1
  | [], s, hs => ⟨s, .loopF (by simp [tops, hs]), by simp⟩
  | a :: l, s, hs => by
    set s₁ := Function.update s 1 (s 1).tail
    set b : Fin (m + 2) := if a = 1 then 1 else 0
    set s₂ := Function.update s₁ 1 (b :: s₁ 1)
    set s₃ := Function.update s₂ 0 (s₂ 0).tail
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have hs₁0 : s₁ 0 = a :: l := by simp [s₁, Function.update_of_ne h01, hs]
    have hs₂0 : s₂ 0 = a :: l := by simp [s₂, Function.update_of_ne h01, hs₁0]
    have hs₃0 : s₃ 0 = l := by simp [s₃, hs₂0]
    have hs₃1 : s₃ 1 = b :: (s 1).tail := by
      simp [s₃, s₂, s₁, Function.update_of_ne h01.symm]
    have hbody : (Prog.seq (.pop 1) (.seq (.ite (fun r => r 0 == some 1) (.push 1 1) (.push 1 0))
        (.pop 0))).Runs s s₃ 5 := by
      refine .seq (t₁ := 1) (t₂ := 4) .pop (.seq (t₁ := 3) (t₂ := 1) ?_ .pop)
      by_cases ha : a = 1
      · have : b = 1 := by simp [b, ha]
        rw [show s₂ = Function.update s₁ 1 (1 :: s₁ 1) by rw [← this]]
        exact .iteT (by simp [tops, hs₁0, hs, ha]) .push
      · have : b = 0 := by simp [b, ha]
        rw [show s₂ = Function.update s₁ 1 (0 :: s₁ 1) by rw [← this]]
        exact .iteF (by simp [tops, hs₁0, hs, ha]) .push
    obtain ⟨s', hr, htop⟩ := lastProg_runs m l s₃ hs₃0
    refine ⟨s', ?_, ?_⟩
    · have := Prog.Runs.loopT
        (by simp [tops, hs] : (fun r : Fin 2 → Option (Fin (m + 2)) => (r 0).isSome) (tops s) = true)
        hbody hr
      rw [show 6 * (a :: l).length + 1 = 5 + (6 * l.length + 1) + 1 by
        rw [List.length_cons]; ring]
      exact this
    · rw [htop]
      cases l with
      | nil => simp [tops, hs₃1, b]
      | cons a' l' => simp only [List.getLast?_cons_cons, List.getLast?_cons, Option.getD_some]

/-- `lastTrue` is decidable in linear time. -/
lemma lastTrue_dt : DT lastTrue 1 := by
  let P := lastProg 0
  let ans : (Fin 2 → Option (Fin 2)) → Bool := fun r => r 1 == some 1
  refine ⟨P.toMachine ans, Prog.toMachine_deterministic _ _, 6, fun x => ?_⟩
  obtain ⟨s', hr, htop⟩ := lastProg_runs 0 (x.map (bitSym 0)) (inputStacks 1 0 x) rfl
  have hans := Prog.toMachine_answer (ans := ans) hr
  refine decidesWithin_mono ⟨_, hans, ?_⟩ ?_
  · simp only [ans, htop, lastTrue, Set.mem_setOf_eq, List.getLast?_map]
    rcases x.getLast? with _ | _ | _
    · simp [tops, inputStacks]
    · simp [bitSym]
    · simp [bitSym]
  · apply Nat.le_floor
    simp only [List.length_map, Real.rpow_one]
    push_cast
    linarith

/-- For `a < 1`, a machine running in time `C n^a + C` misses the last cell of long inputs. -/
lemma exists_len (C : ℕ) {a : ℝ} (ha : a < 1) :
    ∃ n : ℕ, 1 ≤ n ∧ (C : ℝ) * (n : ℝ) ^ a + C ≤ n - 1 := by
  have hy : 0 < 1 - a := by linarith
  have hpos : (0 : ℝ) < 1 / (2 * C + 2) := by positivity
  have e1 : ∀ᶠ x : ℝ in atTop, x ^ (-(1 - a)) < 1 / (2 * C + 2) :=
    (tendsto_order.1 (tendsto_rpow_neg_atTop hy)).2 _ hpos
  have e2 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually e1
  have e3 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2 * C + 2 : ℝ))
  obtain ⟨n, h1, h2, h3⟩ := (e2.and (e3.and (eventually_ge_atTop 1))).exists
  refine ⟨n, h3, ?_⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast h3
  have hsplit : (n : ℝ) ^ a = n * (n : ℝ) ^ (-(1 - a)) := by
    conv_lhs => rw [show a = 1 + -(1 - a) by ring]
    rw [Real.rpow_add hn, Real.rpow_one]
  rw [hsplit]
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have h4 : (C : ℝ) * (n * (n : ℝ) ^ (-(1 - a))) ≤ n / 2 := by
    have h5 : (n : ℝ) ^ (-(1 - a)) * (2 * C + 2) ≤ 1 := by
      rw [lt_div_iff₀ (by positivity)] at h1; linarith
    have h6 : 0 ≤ (n : ℝ) ^ (-(1 - a)) := Real.rpow_nonneg hn.le _
    nlinarith
  linarith

lemma lastTrue_not_dt {a : ℝ} (ha : a < 1) : ¬ DT lastTrue a := by
  rintro ⟨M, -, C, hC⟩
  obtain ⟨n, hn1, hn⟩ := exists_len C ha
  set x₀ := List.replicate (n - 1) false ++ [false]
  set x₁ := List.replicate (n - 1) false ++ [true]
  have hl₀ : x₀.length = n := by simp [x₀]; omega
  have hl₁ : x₁.length = n := by simp [x₁]; omega
  have ht : ⌊(C : ℝ) * (n : ℝ) ^ a + C⌋₊ ≤ n - 1 := by
    apply Nat.floor_le_of_le
    push_cast [hn1]
    linarith
  obtain ⟨b₀, hb₀, hP₀⟩ := hC x₀
  obtain ⟨b₁, hb₁, hP₁⟩ := hC x₁
  rw [hl₀] at hb₀
  rw [hl₁] at hb₁
  have hclose : CloseAt M ((n - 1 : ℕ) : ℤ) 0 (init M x₀) (init M x₁) := by
    refine ⟨rfl, rfl, rfl, ?_, by simp [init]⟩
    intro j z hjz
    simp only [init]
    by_cases hj : j = 0
    · subst hj
      by_cases hz : 0 ≤ z
      · simp only [true_and, hz, if_true]
        have hz' : z.toNat ≠ n - 1 := by
          intro h; apply hjz; refine ⟨rfl, ?_⟩; omega
        simp only [x₀, x₁]
        rcases lt_or_gt_of_ne hz' with h | h
        · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
        · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
      · simp [hz]
    · simp [hj]
  have heq := closeAt_drun _ 0 _ _ hclose (show ((0 : ℕ) : ℤ) + _ ≤ _ by exact_mod_cast
    (by omega : 0 + ⌊(C : ℝ) * (n : ℝ) ^ a + C⌋₊ ≤ n - 1))
  rw [← runOn_eq_drun, ← runOn_eq_drun] at heq
  beta_reduce at hb₀ hb₁
  rw [hb₀, hb₁] at heq
  cases heq
  have h0 : x₀ ∉ lastTrue := by simp [x₀, lastTrue]
  have h1 : x₁ ∈ lastTrue := by simp [x₁, lastTrue]
  exact h0 (hP₀.mp (hP₁.mpr h1))

theorem lin (a : ℝ) (ha : a < 1) : ∃ L, DT L 1 ∧ ¬ DT L a :=
  ⟨lastTrue, lastTrue_dt, lastTrue_not_dt ha⟩

end Lax119563Proofs.Hierarchy

end Hierarchy_Locality

/-! ### Formerly `Lax119563Proofs.Hierarchy.Programs` -/

section Hierarchy_Programs

/-!
# A small library of stack programs

Specifications are exact descriptions of the final stacks (as `Function.update`s of the initial
ones) together with upper bounds on the cost (`Prog.RunsLe`).  Unary numbers are stacks
`List.replicate n 0`.
-/

open Function

namespace Lax119563Proofs.Hierarchy

variable {K m : ℕ}

namespace Prog

/-- `p` runs from `s` to `s'` within cost `T`. -/
def RunsLe (p : Prog K m) (s s' : Stacks K m) (T : ℕ) : Prop := ∃ t ≤ T, p.Runs s s' t

lemma Runs.le {p : Prog K m} {s s' : Stacks K m} {t : ℕ} (h : p.Runs s s' t) :
    p.RunsLe s s' t := ⟨t, le_rfl, h⟩

lemma RunsLe.mono {p : Prog K m} {s s' : Stacks K m} {T T' : ℕ} (h : p.RunsLe s s' T)
    (hT : T ≤ T') : p.RunsLe s s' T' := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, by omega, h⟩

lemma RunsLe.seq {p q : Prog K m} {s₁ s₂ s₃ : Stacks K m} {T₁ T₂ : ℕ} (h₁ : p.RunsLe s₁ s₂ T₁)
    (h₂ : q.RunsLe s₂ s₃ T₂) : (seq p q).RunsLe s₁ s₃ (T₁ + T₂) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂, by omega, .seq h₁ h₂⟩

lemma RunsLe.iteT {c} {p q : Prog K m} {s s' : Stacks K m} {T : ℕ} (hc : c (tops s) = true)
    (h : p.RunsLe s s' T) : (ite c p q).RunsLe s s' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteT hc h⟩

lemma RunsLe.iteF {c} {p q : Prog K m} {s s' : Stacks K m} {T : ℕ} (hc : c (tops s) = false)
    (h : q.RunsLe s s' T) : (ite c p q).RunsLe s s' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteF hc h⟩

lemma RunsLe.loopF {c} {p : Prog K m} {s : Stacks K m} (hc : c (tops s) = false) :
    (loop c p).RunsLe s s 1 := (Runs.loopF hc).le

lemma RunsLe.loopT {c} {p : Prog K m} {s₁ s₂ s₃ : Stacks K m} {T₁ T₂ : ℕ}
    (hc : c (tops s₁) = true) (h₁ : p.RunsLe s₁ s₂ T₁) (h₂ : (loop c p).RunsLe s₂ s₃ T₂) :
    (loop c p).RunsLe s₁ s₃ (T₁ + T₂ + 1) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂ + 1, by omega, .loopT hc h₁ h₂⟩

lemma RunsLe.skip (s : Stacks K m) : (skip : Prog K m).RunsLe s s 1 := Runs.skip.le

lemma RunsLe.push (i : Fin K) (a : Fin (m + 2)) (s : Stacks K m) :
    (push i a).RunsLe s (update s i (a :: s i)) 2 := Runs.push.le

lemma RunsLe.pop (i : Fin K) (s : Stacks K m) :
    (pop i).RunsLe s (update s i (s i).tail) 1 := Runs.pop.le

lemma RunsLe.of_eq {p : Prog K m} {s s₁ s₂ : Stacks K m} {T T' : ℕ} (h : p.RunsLe s s₁ T)
    (hs : s₁ = s₂) (hT : T ≤ T') : p.RunsLe s s₂ T' := hs ▸ h.mono hT

/-- Prove an equality of stacks given by `Function.update`s pointwise. -/
macro "stacks_eq" : tactic =>
  `(tactic| (funext k; simp only [Function.update_apply]; split_ifs <;> simp_all))

/-- Repeat a program `n` times. -/
def rep (p : Prog K m) : ℕ → Prog K m
  | 0 => skip
  | n + 1 => seq p (rep p n)

/-! ## Moving symbols -/

/-- Push onto `j` the top symbol of `i`, provided it occurs in `as`. -/
def pushTopOf (i j : Fin K) : List (Fin (m + 2)) → Prog K m
  | [] => skip
  | a :: as => ite (fun r => r i == some a) (push j a) (pushTopOf i j as)

lemma pushTopOf_runs (i j : Fin K) {s : Stacks K m} {a : Fin (m + 2)}
    (ha : tops s i = some a) :
    ∀ as : List (Fin (m + 2)), a ∈ as →
      (pushTopOf i j as).RunsLe s (update s j (a :: s j)) (as.length + 2)
  | [], h => by simp at h
  | b :: as, h => by
    by_cases hb : b = a
    · subst hb
      exact ((RunsLe.push j b s).iteT (by simp [ha])).mono (by simp)
    · have : a ∈ as := by simp at h; tauto
      exact ((pushTopOf_runs i j ha as this).iteF (by simp [ha, Ne.symm hb])).mono (by simp)

/-- Move the top symbol of `i` onto `j`. -/
def moveOne (i j : Fin K) : Prog K m := seq (pushTopOf i j (List.finRange (m + 2))) (pop i)

lemma moveOne_runs {i j : Fin K} (hij : i ≠ j) {s : Stacks K m} {a : Fin (m + 2)}
    {l : List (Fin (m + 2))} (hs : s i = a :: l) :
    (moveOne i j).RunsLe s (update (update s i l) j (a :: s j)) (m + 5) := by
  have h1 := pushTopOf_runs i j (s := s) (by simp [tops, hs]) (List.finRange (m + 2))
    (List.mem_finRange a)
  have h2 := RunsLe.pop i (update s j (a :: s j))
  exact (h1.seq h2).of_eq (by stacks_eq) (by simp)

/-- Move all of `i` onto `j` (reversing it). -/
def moveAll (i j : Fin K) : Prog K m := loop (fun r => (r i).isSome) (moveOne i j)

lemma moveAll_runs {i j : Fin K} (hij : i ≠ j) :
    ∀ (l : List (Fin (m + 2))) (s : Stacks K m), s i = l →
      (moveAll i j).RunsLe s (update (update s i []) j (l.reverse ++ s j))
        ((m + 6) * l.length + 1)
  | [], s, hs =>
    (RunsLe.loopF (p := moveOne i j) (c := fun r => (r i).isSome) (s := s)
      (by simp [tops, hs])).of_eq (by stacks_eq) (by simp)
  | a :: l, s, hs => by
    have h1 := moveOne_runs hij hs
    have h2 := moveAll_runs hij l (update (update s i l) j (a :: s j))
      (by simp [update_of_ne hij])
    exact (RunsLe.loopT (c := fun r => (r i).isSome) (by simp [tops, hs]) h1 h2).of_eq
      (by stacks_eq) (le_of_eq (by simp only [List.length_cons]; ring))

/-! ## Unary numbers -/

/-- The unary number `n`. -/
abbrev unary (m n : ℕ) : List (Fin (m + 2)) := List.replicate n 0

/-- Empty stack `i`. -/
def clear (i : Fin K) : Prog K m := loop (fun r => (r i).isSome) (pop i)

lemma clear_runs (i : Fin K) :
    ∀ (l : List (Fin (m + 2))) (s : Stacks K m), s i = l →
      (clear i).RunsLe s (update s i []) (2 * l.length + 1)
  | [], s, hs =>
    (RunsLe.loopF (p := pop i) (c := fun r => (r i).isSome) (s := s)
      (by simp [tops, hs])).of_eq (by stacks_eq) (by simp)
  | a :: l, s, hs => by
    have h2 := clear_runs i l (update s i (s i).tail) (by simp [hs])
    exact (RunsLe.loopT (c := fun r => (r i).isSome) (by simp [tops, hs]) (RunsLe.pop i s)
      h2).of_eq (by stacks_eq) (le_of_eq (by simp only [List.length_cons]; ring))

/-- Move the unary number on `i` to `j` and `h` (adding it to both). -/
def splitTwo (i j h : Fin K) : Prog K m :=
  loop (fun r => (r i).isSome) (seq (pop i) (seq (push h 0) (push j 0)))

lemma splitTwo_runs {i j h : Fin K} (hij : i ≠ j) (hih : i ≠ h) (hjh : j ≠ h) :
    ∀ (n : ℕ) (s : Stacks K m), s i = unary m n →
      (splitTwo i j h).RunsLe s
        (update (update (update s i []) j (unary m n ++ s j)) h (unary m n ++ s h)) (6 * n + 1)
  | 0, s, hs =>
    (RunsLe.loopF (p := seq (pop i) (seq (push h 0) (push j 0)))
      (c := fun r => (r i).isSome) (s := s) (by simp [tops, hs])).of_eq (by stacks_eq) (by simp)
  | n + 1, s, hs => by
    set s₁ := update (update (update s i (unary m n)) h (0 :: s h)) j (0 :: s j)
    have hb : (seq (pop i) (seq (push h 0) (push j 0)) : Prog K m).RunsLe s s₁ 5 :=
      ((RunsLe.pop i s).seq ((RunsLe.push h 0 _).seq (RunsLe.push j 0 _))).of_eq
        (by simp only [s₁, hs, List.replicate_succ, List.tail_cons]; stacks_eq) (by simp)
    have h2 := splitTwo_runs hij hih hjh n s₁ (by simp [s₁, update_of_ne hij, update_of_ne hih])
    exact (RunsLe.loopT (c := fun r => (r i).isSome) (by simp [tops, hs]) hb h2).of_eq
      (by simp only [s₁, List.replicate_succ']; stacks_eq) (le_of_eq (by ring))

/-- Add the unary number on `i` to `j`, restoring `i` through the empty helper `h`. -/
def addTo (i j h : Fin K) : Prog K m := seq (splitTwo i j h) (moveAll h i)

lemma addTo_runs {i j h : Fin K} (hij : i ≠ j) (hih : i ≠ h) (hjh : j ≠ h) {n : ℕ}
    {s : Stacks K m} (hs : s i = unary m n) (hh : s h = []) :
    (addTo i j h).RunsLe s (update s j (unary m n ++ s j)) ((m + 12) * n + 2) := by
  have h1 := splitTwo_runs hij hih hjh n s hs
  have h2 := moveAll_runs hih.symm (unary m n)
    (update (update (update s i []) j (unary m n ++ s j)) h (unary m n ++ s h))
    (by simp [hh])
  exact (h1.seq h2).of_eq (by stacks_eq) (le_of_eq (by simp; ring))

/-- Pop the symbols `0` from the top of `i`, counting them in unary on `j`. -/
def popZeros (i j : Fin K) : Prog K m :=
  loop (fun r => r i == some 0) (seq (pop i) (push j 0))

lemma popZeros_runs {i j : Fin K} (hij : i ≠ j) (l : List (Fin (m + 2)))
    (hl : l.head? ≠ some 0) :
    ∀ (n : ℕ) (s : Stacks K m), s i = unary m n ++ l →
      (popZeros i j).RunsLe s (update (update s i l) j (unary m n ++ s j)) (4 * n + 1)
  | 0, s, hs =>
    (RunsLe.loopF (p := seq (pop i) (push j 0)) (c := fun r => r i == some 0) (s := s)
      (by simpa [tops, hs] using hl)).of_eq (by simp at hs; stacks_eq) (by simp)
  | n + 1, s, hs => by
    set s₁ := update (update s i (unary m n ++ l)) j (0 :: s j) with hs₁
    have h1 : (seq (pop i) (push j 0) : Prog K m).RunsLe s s₁ 3 :=
      ((RunsLe.pop i s).seq (RunsLe.push j 0 _)).of_eq
        (by simp only [hs₁, hs, List.replicate_succ, List.cons_append, List.tail_cons]; stacks_eq)
        le_rfl
    have h2 := popZeros_runs hij l hl n s₁ (by simp [s₁, update_of_ne hij])
    exact (RunsLe.loopT (c := fun r => r i == some 0) (by simp [tops, hs, List.replicate_succ])
      h1 h2).of_eq (by simp only [hs₁, List.replicate_succ', List.append_assoc,
        List.singleton_append]; stacks_eq) (le_of_eq (by ring))

/-- Move all of `i` onto `j` (reversing it), counting the symbols in unary on `c`. -/
def moveCount (i j c : Fin K) : Prog K m :=
  loop (fun r => (r i).isSome) (seq (moveOne i j) (push c 0))

lemma moveCount_runs {i j c : Fin K} (hij : i ≠ j) (hic : i ≠ c) (hjc : j ≠ c) :
    ∀ (l : List (Fin (m + 2))) (s : Stacks K m), s i = l →
      (moveCount i j c).RunsLe s
        (update (update (update s i []) j (l.reverse ++ s j)) c (unary m l.length ++ s c))
        ((m + 8) * l.length + 1)
  | [], s, hs =>
    (RunsLe.loopF (p := seq (moveOne i j) (push c 0)) (c := fun r => (r i).isSome) (s := s)
      (by simp [tops, hs])).of_eq (by stacks_eq) (by simp)
  | a :: l, s, hs => by
    set s₁ := update (update (update s i l) j (a :: s j)) c (0 :: s c) with hs₁
    have h1 : (seq (moveOne i j) (push c 0) : Prog K m).RunsLe s s₁ (m + 7) :=
      ((moveOne_runs hij hs).seq (RunsLe.push c 0 _)).of_eq (by stacks_eq) le_rfl
    have h2 := moveCount_runs hij hic hjc l s₁ (by simp [s₁, update_of_ne hij, update_of_ne hic])
    exact (RunsLe.loopT (c := fun r => (r i).isSome) (by simp [tops, hs]) h1 h2).of_eq
      (by simp only [hs₁, List.length_cons, List.replicate_succ', List.append_assoc,
        List.singleton_append, List.reverse_cons]; stacks_eq)
      (le_of_eq (by simp only [List.length_cons]; ring))

/-- Multiply the unary number on `p` by the one on `n` (helpers `q`, `h` empty). -/
def mulBy (p n q h : Fin K) : Prog K m :=
  seq (loop (fun r => (r p).isSome) (seq (pop p) (addTo n q h))) (moveAll q p)

lemma mulBy_loop_runs {p n q h : Fin K} (hpn : p ≠ n) (hpq : p ≠ q) (hph : p ≠ h) (hnq : n ≠ q)
    (hnh : n ≠ h) (hqh : q ≠ h) {b : ℕ} :
    ∀ (a : ℕ) (s : Stacks K m), s p = unary m a → s n = unary m b → s h = [] →
      (loop (fun r => (r p).isSome) (seq (pop p) (addTo n q h))).RunsLe s
        (update (update s p []) q (unary m (a * b) ++ s q)) (a * ((m + 12) * b + 4) + 1)
  | 0, s, hs, _, _ =>
    (RunsLe.loopF (p := seq (pop p) (addTo n q h)) (c := fun r => (r p).isSome) (s := s)
      (by simp [tops, hs])).of_eq (by simp at hs; stacks_eq) (by simp)
  | a + 1, s, hs, hn, hh => by
    set s₁ := update (update s p (unary m a)) q (unary m b ++ s q) with hs₁
    have h1 : (seq (pop p) (addTo n q h) : Prog K m).RunsLe s s₁ ((m + 12) * b + 3) :=
      ((RunsLe.pop p s).seq (addTo_runs (n := b) (s := update s p (s p).tail) hnq hnh hqh
        (by simp [update_of_ne hpn.symm, hn]) (by simp [update_of_ne hph.symm, hh]))).of_eq
        (by simp only [hs₁, hs, List.replicate_succ, List.tail_cons]; stacks_eq) (by omega)
    have h2 := mulBy_loop_runs (b := b) hpn hpq hph hnq hnh hqh a s₁
      (by simp [s₁, update_of_ne hpq])
      (by simp [s₁, update_of_ne hnq, update_of_ne hpn.symm, hn])
      (by simp [s₁, update_of_ne hqh.symm, update_of_ne hph.symm, hh])
    refine (RunsLe.loopT (c := fun r => (r p).isSome) (by simp [tops, hs, List.replicate_succ])
      h1 h2).of_eq ?_ (le_of_eq (by ring))
    have : unary m ((a + 1) * b) = unary m (a * b) ++ unary m b := by
      rw [List.replicate_append_replicate]; congr 1; ring
    rw [this, hs₁, List.append_assoc]
    stacks_eq

lemma mulBy_runs {p n q h : Fin K} (hpn : p ≠ n) (hpq : p ≠ q) (hph : p ≠ h) (hnq : n ≠ q)
    (hnh : n ≠ h) (hqh : q ≠ h) {a b : ℕ} {s : Stacks K m} (hs : s p = unary m a)
    (hn : s n = unary m b) (hq : s q = []) (hh : s h = []) :
    (mulBy p n q h).RunsLe s (update s p (unary m (a * b))) ((2 * m + 20) * (a + 1) * (b + 1)) := by
  have h1 := mulBy_loop_runs hpn hpq hph hnq hnh hqh a s hs hn hh
  have h2 := moveAll_runs hpq.symm (unary m (a * b))
    (update (update s p []) q (unary m (a * b) ++ s q)) (by simp [hq])
  refine (h1.seq h2).of_eq (by simp only [List.reverse_replicate]; stacks_eq) ?_
  simp only [List.length_replicate]
  nlinarith [Nat.zero_le (a * b), Nat.zero_le m, Nat.zero_le a, Nat.zero_le b]

lemma rep_seq_runs {p : Prog K m} {f : ℕ → Stacks K m} {c : ℕ → ℕ}
    (h : ∀ k, p.RunsLe (f k) (f (k + 1)) (c k)) :
    ∀ r k, (rep p r).RunsLe (f k) (f (k + r)) ((Finset.range r).sum (fun i => c (k + i)) + 1)
  | 0, k => (RunsLe.skip _).of_eq (by simp) (by simp)
  | r + 1, k => by
    have := (h k).seq (rep_seq_runs h r (k + 1))
    refine this.of_eq (by rw [show k + 1 + r = k + (r + 1) by omega]) (le_of_eq ?_)
    rw [Finset.sum_range_succ']
    simp only [add_zero]
    have : ∀ i, k + 1 + i = k + (i + 1) := fun i => by omega
    simp only [this]
    ring

/-- Compute on `p` (empty) the `r`-th power of the unary number on `n` (helpers `q`, `h`
empty). -/
def power (p n q h : Fin K) (r : ℕ) : Prog K m := seq (push p 0) (rep (mulBy p n q h) r)

lemma power_runs {p n q h : Fin K} (hpn : p ≠ n) (hpq : p ≠ q) (hph : p ≠ h) (hnq : n ≠ q)
    (hnh : n ≠ h) (hqh : q ≠ h) {b : ℕ} (r : ℕ) {s : Stacks K m} (hp : s p = [])
    (hn : s n = unary m b) (hq : s q = []) (hh : s h = []) :
    (power p n q h r).RunsLe s (update s p (unary m (b ^ r)))
      (r * ((4 * m + 40) * (b + 1) ^ r) + 3) := by
  set f : ℕ → Stacks K m := fun k => update s p (unary m (b ^ k))
  have hstep : ∀ k, (mulBy p n q h).RunsLe (f k) (f (k + 1))
      ((2 * m + 20) * (b ^ k + 1) * (b + 1)) := by
    intro k
    refine (mulBy_runs hpn hpq hph hnq hnh hqh (s := f k) (by simp [f])
      (by simp [f, update_of_ne hpn.symm, hn]) (by simp [f, update_of_ne hpq.symm, hq])
      (by simp [f, update_of_ne hph.symm, hh])).of_eq (by simp [f, pow_succ]) le_rfl
  have h2 := rep_seq_runs hstep r 0
  have h1 : (push p 0 : Prog K m).RunsLe s (f 0) 2 :=
    (RunsLe.push p 0 s).of_eq (by simp [f, hp]) le_rfl
  refine (h1.seq (h2.of_eq (s₂ := f r) (by simp) le_rfl)).of_eq rfl ?_
  · simp only [zero_add]
    have hb : ∀ i < r, (2 * m + 20) * (b ^ i + 1) * (b + 1) ≤ (4 * m + 40) * (b + 1) ^ r := by
      intro i hi
      have h3 : b ^ i + 1 ≤ 2 * (b + 1) ^ i := by
        have := Nat.pow_le_pow_left (show b ≤ b + 1 by omega) i
        have := Nat.one_le_pow i (b + 1) (Nat.succ_pos b)
        omega
      have h4 : (b + 1) ^ i * (b + 1) ≤ (b + 1) ^ r := by
        rw [← pow_succ]; exact Nat.pow_le_pow_right (Nat.succ_pos b) hi
      calc (2 * m + 20) * (b ^ i + 1) * (b + 1) ≤ (2 * m + 20) * (2 * (b + 1) ^ i) * (b + 1) := by
            gcongr
        _ = (4 * m + 40) * ((b + 1) ^ i * (b + 1)) := by ring
        _ ≤ (4 * m + 40) * (b + 1) ^ r := by gcongr
    have := Finset.sum_le_sum (fun i hi => hb i (Finset.mem_range.mp hi))
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
    omega

/-! ## Moving up to a delimiter, duplicating -/

/-- Move symbols from `i` to `j` while the top of `i` is not `a`. -/
def moveWhileNot (i j : Fin K) (a : Fin (m + 2)) : Prog K m :=
  loop (fun r => (r i).isSome && r i != some a) (moveOne i j)

lemma moveWhileNot_runs {i j : Fin K} (hij : i ≠ j) (a : Fin (m + 2)) (l₂ : List (Fin (m + 2)))
    (hl₂ : l₂.head? = some a ∨ l₂ = []) :
    ∀ (l₁ : List (Fin (m + 2))) (s : Stacks K m), a ∉ l₁ → s i = l₁ ++ l₂ →
      (moveWhileNot i j a).RunsLe s (update (update s i l₂) j (l₁.reverse ++ s j))
        ((m + 6) * l₁.length + 1)
  | [], s, _, hs =>
    (RunsLe.loopF (p := moveOne i j) (c := fun r => (r i).isSome && r i != some a) (s := s)
      (by rcases hl₂ with h | h <;> simp_all [tops])).of_eq (by simp at hs; stacks_eq) (by simp)
  | b :: l, s, ha, hs => by
    have hb : b ≠ a := fun h => ha (by simp [h])
    have h1 := moveOne_runs (l := l ++ l₂) hij hs
    have h2 := moveWhileNot_runs hij a l₂ hl₂ l (update (update s i (l ++ l₂)) j (b :: s j))
      (fun h => ha (by simp [h])) (by simp [update_of_ne hij])
    exact (RunsLe.loopT (c := fun r => (r i).isSome && r i != some a) (by simp [tops, hs, hb])
      h1 h2).of_eq (by stacks_eq) (le_of_eq (by simp only [List.length_cons]; ring))

/-- Move symbols from `i` to `j` up to and including the first `a`. -/
def moveThrough (i j : Fin K) (a : Fin (m + 2)) : Prog K m := seq (moveWhileNot i j a) (moveOne i j)

lemma moveThrough_runs {i j : Fin K} (hij : i ≠ j) {a : Fin (m + 2)} {l₁ l₂ : List (Fin (m + 2))}
    {s : Stacks K m} (ha : a ∉ l₁) (hs : s i = l₁ ++ a :: l₂) :
    (moveThrough i j a).RunsLe s (update (update s i l₂) j (a :: (l₁.reverse ++ s j)))
      ((m + 6) * (l₁.length + 1)) := by
  have h1 := moveWhileNot_runs hij a (a :: l₂) (by simp) l₁ s ha hs
  have h2 := moveOne_runs (s := update (update s i (a :: l₂)) j (l₁.reverse ++ s j)) hij
    (a := a) (l := l₂) (by simp [update_of_ne hij])
  exact (h1.seq h2).of_eq (by stacks_eq) (le_of_eq (by ring))

/-- Move all of `i` onto both `j` and `k` (reversing it). -/
def dupAll (i j k : Fin K) : Prog K m :=
  loop (fun r => (r i).isSome)
    (seq (pushTopOf i j (List.finRange (m + 2))) (seq (pushTopOf i k (List.finRange (m + 2)))
      (pop i)))

lemma dupAll_runs {i j k : Fin K} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∀ (l : List (Fin (m + 2))) (s : Stacks K m), s i = l →
      (dupAll i j k).RunsLe s
        (update (update (update s i []) j (l.reverse ++ s j)) k (l.reverse ++ s k))
        ((2 * m + 10) * l.length + 1)
  | [], s, hs =>
    (RunsLe.loopF (c := fun r => (r i).isSome) (s := s)
      (p := seq (pushTopOf i j (List.finRange (m + 2))) (seq (pushTopOf i k
        (List.finRange (m + 2))) (pop i))) (by simp [tops, hs])).of_eq (by stacks_eq) (by simp)
  | a :: l, s, hs => by
    set s₁ := update (update (update s i l) j (a :: s j)) k (a :: s k)
    have hb : (seq (pushTopOf i j (List.finRange (m + 2))) (seq (pushTopOf i k
        (List.finRange (m + 2))) (pop i)) : Prog K m).RunsLe s s₁ (2 * m + 9) := by
      have h1 := pushTopOf_runs i j (s := s) (by simp [tops, hs]) (List.finRange (m + 2))
        (List.mem_finRange a)
      have h2 := pushTopOf_runs i k (s := update s j (a :: s j))
        (by simp [tops, update_of_ne hij, hs]) (List.finRange (m + 2)) (List.mem_finRange a)
      have h3 := RunsLe.pop i (update (update s j (a :: s j)) k (a :: update s j (a :: s j) k))
      refine (h1.seq (h2.seq h3)).of_eq ?_ (by simp; omega)
      simp only [s₁]; stacks_eq
    have h2 := dupAll_runs hij hik hjk l s₁ (by simp [s₁, update_of_ne hij, update_of_ne hik])
    exact (RunsLe.loopT (c := fun r => (r i).isSome) (by simp [tops, hs]) hb h2).of_eq
      (by simp only [s₁]; stacks_eq) (le_of_eq (by simp only [List.length_cons]; ring))

end Prog

end Lax119563Proofs.Hierarchy

end Hierarchy_Programs

/-! ### Formerly `Lax119563Proofs.Hierarchy.Padding` -/

section Hierarchy_Padding

/-!
# Padding

For a machine `ML` and constants `C s`, the padded language
`padLang ML C s = {x ++ [true] ++ 0^j | ML accepts x within ((C + 1) (j + 1))^s steps}`
is decidable in time `O(n^s)` by a clocked run of `ML` (`padLang_dt`).  Conversely, if
`ML` decides `L` within `C n^{s r} + C` steps and `padLang ML C s ∈ DTIME(n^a)` with `a ≥ 1`,
then `L ∈ DTIME(n^{a r})`: write `0^{|x|^r}` behind `x ++ [true]` and run the decider of the
padded language (`dt_of_padLang`).
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime Function

namespace Lax119563Proofs.Hierarchy

open Prog

/-! ## Words with a last `true` -/

lemma split_last_true (y : List Bool) :
    (∃ x j, y = x ++ true :: List.replicate j false) ∨ ∃ n, y = List.replicate n false := by
  induction y using List.reverseRecOn with
  | nil => exact .inr ⟨0, rfl⟩
  | append_singleton y b ih =>
    cases b
    · rcases ih with ⟨x, j, rfl⟩ | ⟨n, rfl⟩
      · exact .inl ⟨x, j + 1, by simp [List.replicate_succ']⟩
      · exact .inr ⟨n + 1, by simp [List.replicate_succ']⟩
    · exact .inl ⟨y, 0, rfl⟩

lemma replicate_true_cancel :
    ∀ (j j' : ℕ) (l l' : List Bool),
      List.replicate j false ++ true :: l = List.replicate j' false ++ true :: l' → j = j' ∧ l = l'
  | 0, 0, l, l', h => by simpa using h
  | 0, j' + 1, l, l', h => by simp [List.replicate_succ] at h
  | j + 1, 0, l, l', h => by simp [List.replicate_succ] at h
  | j + 1, j' + 1, l, l', h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨h1, h2⟩ := replicate_true_cancel j j' l l' h
    exact ⟨by omega, h2⟩

lemma last_true_unique {x x' : List Bool} {j j' : ℕ}
    (h : x ++ true :: List.replicate j false = x' ++ true :: List.replicate j' false) :
    x = x' ∧ j = j' := by
  have := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc,
    List.singleton_append] at this
  obtain ⟨h1, h2⟩ := replicate_true_cancel j j' _ _ this
  exact ⟨by simpa using h2, h1⟩

/-! ## The padded language and its decider -/

section Decider

variable (ML : Machine) (C s : ℕ)

/-- The padded language. -/
def padLang : Set (List Bool) :=
  {y | ∃ x j, y = x ++ true :: List.replicate j false ∧
    (runOn ML x (((C + 1) * (j + 1)) ^ s)).answer = some true}

/-- Stack indices of the decider: scratch stacks after the clock. -/
def d1 (k : ℕ) (hk : k < 5 := by omega) : Fin (ML.tapes + 1 + 5 + 1) := ⟨ML.tapes + 2 + k, by omega⟩

/-- The preparation of the decider of `padLang`. -/
def padPrep : Prog (ML.tapes + 1 + 5 + 1) ML.symbols :=
  seq (moveAll 0 (d1 ML 0))
    (seq (popZeros (d1 ML 0) (d1 ML 1))
      (ite (fun r => r (d1 ML 0) == some 1)
        (seq (pop (d1 ML 0))
          (seq (moveAll (d1 ML 0) 0)
            (seq (push (d1 ML 1) 0)
              (seq (rep (addTo (d1 ML 1) (d1 ML 2) (d1 ML 3)) (C + 1))
                (power (clockIdx ML 5) (d1 ML 2) (d1 ML 4) (d1 ML 3) s)))))
        skip))

/-- The decider of `padLang`. -/
noncomputable def padDecider : Machine := thenClocked ML 5 (padPrep ML C s)

end Decider

section Spec

variable {ML : Machine} {C s : ℕ}

lemma map_bitSym_pad (m : ℕ) (x : List Bool) (j : ℕ) :
    ((x ++ true :: List.replicate j false).map (bitSym m)).reverse =
      unary m j ++ (1 :: (x.map (bitSym m)).reverse) := by
  simp [List.reverse_append, List.map_replicate, bitSym, List.reverse_replicate]

/-- The cost bound of `padPrep` when the input has a last `true`. -/
def padCost (m n j xl C s : ℕ) : ℕ :=
  (m + 6) * n + 1 + (4 * j + 1 + (1 + ((m + 6) * xl + 1 + (2 +
    ((Finset.range (C + 1)).sum (fun _ => (m + 12) * (j + 1) + 2) + 1 +
      (s * ((4 * m + 40) * ((C + 1) * (j + 1) + 1) ^ s) + 3)))) + 1))

/-- Stacks of the decider in the shape used by `padPrep`. -/
def pst (ML : Machine) (a0 aA aJ aB aK : List (Fin (ML.symbols + 2))) :
    Stacks (ML.tapes + 1 + 5 + 1) ML.symbols := fun i =>
  if i.val = 0 then a0 else if i.val = ML.tapes + 2 then aA else
  if i.val = ML.tapes + 3 then aJ else if i.val = ML.tapes + 4 then aB else
  if i.val = ML.tapes + 1 then aK else []

/-- Prove equalities between `pst` stacks and their updates. -/
macro "pst_eq" : tactic =>
  `(tactic| (funext i; simp only [pst, Function.update_apply, Fin.ext_iff, Fin.val_zero, d1,
    clockIdx]; split_ifs <;> first | omega | rfl | simp_all))

lemma padPrep_runs_true (x : List Bool) (j : ℕ) :
    ∃ s', (padPrep ML C s).RunsLe (inputStacks _ _ (x ++ true :: List.replicate j false)) s'
        (padCost ML.symbols (x ++ true :: List.replicate j false).length j x.length C s) ∧
      HandsOver ML s' x ∧ (s' (clockIdx ML 5)).length = ((C + 1) * (j + 1)) ^ s := by
  have ne : ∀ a b : Fin (ML.tapes + 1 + 5 + 1), a.val ≠ b.val → a ≠ b :=
    fun a b h => Fin.ne_of_val_ne h
  have v0 : (0 : Fin (ML.tapes + 1 + 5 + 1)).val = 0 := rfl
  set m := ML.symbols
  set y := x ++ true :: List.replicate j false
  have hs0 : inputStacks (ML.tapes + 1 + 5) m y = pst ML (y.map (bitSym m)) [] [] [] [] := by
    funext i
    simp only [inputStacks, pst, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> first | omega | rfl
  rw [hs0]
  -- 1. reverse the input onto `A`
  have h1 : (moveAll 0 (d1 ML 0) : Prog _ m).RunsLe (pst ML (y.map (bitSym m)) [] [] [] [])
      (pst ML [] (unary m j ++ (1 :: (x.map (bitSym m)).reverse)) [] [] []) ((m + 6) * y.length + 1) :=
    (moveAll_runs (ne _ _ (by simp [d1])) (y.map (bitSym m)) _ (by simp [pst])).of_eq
      (by rw [map_bitSym_pad]; pst_eq) (by simp)
  -- 2. count the trailing `false`s on `J`
  have h2 : (popZeros (d1 ML 0) (d1 ML 1) : Prog _ m).RunsLe
      (pst ML [] (unary m j ++ (1 :: (x.map (bitSym m)).reverse)) [] [] [])
      (pst ML [] (1 :: (x.map (bitSym m)).reverse) (unary m j) [] []) (4 * j + 1) :=
    (popZeros_runs (ne _ _ (by simp [d1])) (1 :: (x.map (bitSym m)).reverse) (by simp) j _
      (by simp [pst, d1])).of_eq (by pst_eq) le_rfl
  -- 3. the branch on the `true`
  have h3 : (pop (d1 ML 0) : Prog _ m).RunsLe (pst ML [] (1 :: (x.map (bitSym m)).reverse) (unary m j) [] [])
      (pst ML [] (x.map (bitSym m)).reverse (unary m j) [] []) 1 :=
    (RunsLe.pop _ _).of_eq (by pst_eq) le_rfl
  have h4 : (moveAll (d1 ML 0) 0 : Prog _ m).RunsLe (pst ML [] (x.map (bitSym m)).reverse (unary m j) [] [])
      (pst ML (x.map (bitSym m)) [] (unary m j) [] []) ((m + 6) * x.length + 1) :=
    (moveAll_runs (ne _ _ (by simp [d1])) (x.map (bitSym m)).reverse _ (by simp [pst, d1])).of_eq
      (by pst_eq) (by simp)
  set f : ℕ → Stacks _ m := fun k => pst ML (x.map (bitSym m)) [] (unary m (j + 1)) (unary m (k * (j + 1))) []
  have h5 : (push (d1 ML 1) 0 : Prog _ m).RunsLe (pst ML (x.map (bitSym m)) [] (unary m j) [] []) (f 0) 2 :=
    (RunsLe.push _ _ _).of_eq (by simp only [f, List.replicate_succ]; pst_eq) le_rfl
  have hstep : ∀ k, (addTo (d1 ML 1) (d1 ML 2) (d1 ML 3) : Prog _ m).RunsLe (f k) (f (k + 1))
      ((m + 12) * (j + 1) + 2) := by
    intro k
    refine (addTo_runs (n := j + 1) (ne _ _ (by simp [d1])) (ne _ _ (by simp [d1]))
      (ne _ _ (by simp [d1])) (by simp [f, pst, d1]) (by simp [f, pst, d1])).of_eq ?_ le_rfl
    have : unary m (j + 1) ++ unary m (k * (j + 1)) = unary m ((k + 1) * (j + 1)) := by
      rw [List.replicate_append_replicate]; congr 1; ring
    simp only [f]
    rw [show pst ML (x.map (bitSym m)) [] (unary m (j + 1)) (unary m (k * (j + 1))) [] (d1 ML 2) =
      unary m (k * (j + 1)) by simp [pst, d1], this]
    pst_eq
  have h6 := rep_seq_runs hstep (C + 1) 0
  simp only [zero_add] at h6
  set Bv := (C + 1) * (j + 1)
  have h7 := power_runs (p := clockIdx ML 5) (n := d1 ML 2) (q := d1 ML 4) (h := d1 ML 3) (b := Bv)
    (ne _ _ (by simp [d1, clockIdx])) (ne _ _ (by simp [d1, clockIdx]))
    (ne _ _ (by simp [d1, clockIdx])) (ne _ _ (by simp [d1])) (ne _ _ (by simp [d1]))
    (ne _ _ (by simp [d1])) s (s := f (C + 1))
    (by simp [f, pst, clockIdx]) (by simp [f, pst, d1, Bv]) (by simp [f, pst, d1])
    (by simp [f, pst, d1])
  have hc : (fun r : Fin (ML.tapes + 1 + 5 + 1) → Option (Fin (m + 2)) => r (d1 ML 0) == some 1)
      (tops (pst ML [] (1 :: (x.map (bitSym m)).reverse) (unary m j) [] [])) = true := by
    simp [tops, pst, d1]
  refine ⟨_, h1.seq (h2.seq (RunsLe.iteT hc (h3.seq (h4.seq (h5.seq (h6.seq h7)))))), ?_, ?_⟩
  · intro i
    refine ⟨fun hi => ?_, fun hi1 hi2 => ?_⟩
    · simp only [f, update_apply, Fin.ext_iff, clockIdx, pst]
      split_ifs <;> first | omega | rfl
    · simp only [f, update_apply, Fin.ext_iff, clockIdx, pst]
      split_ifs <;> first | omega | rfl
  · simp

lemma padPrep_runs_false (n : ℕ) :
    ∃ s', (padPrep ML C s).RunsLe (inputStacks _ _ (List.replicate n false)) s'
        ((ML.symbols + 6) * n + 1 + (4 * n + 1 + (1 + 1))) ∧
      HandsOver ML s' [] ∧ (s' (clockIdx ML 5)).length = 0 := by
  have ne : ∀ a b : Fin (ML.tapes + 1 + 5 + 1), a.val ≠ b.val → a ≠ b :=
    fun a b h => Fin.ne_of_val_ne h
  set m := ML.symbols
  have hs0 : inputStacks (ML.tapes + 1 + 5) m (List.replicate n false) =
      pst ML (unary m n) [] [] [] [] := by
    funext i
    simp only [inputStacks, pst, Fin.ext_iff, Fin.val_zero, List.map_replicate]
    split_ifs <;> first | omega | rfl | simp_all [bitSym]
  rw [hs0]
  have h1 : (moveAll 0 (d1 ML 0) : Prog _ m).RunsLe (pst ML (unary m n) [] [] [] [])
      (pst ML [] (unary m n ++ []) [] [] []) ((m + 6) * n + 1) :=
    (moveAll_runs (ne _ _ (by simp [d1])) (unary m n) _ (by simp [pst])).of_eq
      (by simp only [List.reverse_replicate]; pst_eq) (by simp)
  have h2 : (popZeros (d1 ML 0) (d1 ML 1) : Prog _ m).RunsLe
      (pst ML [] (unary m n ++ []) [] [] []) (pst ML [] [] (unary m n) [] []) (4 * n + 1) :=
    (popZeros_runs (ne _ _ (by simp [d1])) [] (by simp) n _ (by simp [pst, d1])).of_eq
      (by pst_eq) le_rfl
  have hc : (fun r : Fin (ML.tapes + 1 + 5 + 1) → Option (Fin (m + 2)) => r (d1 ML 0) == some 1)
      (tops (pst ML [] [] (unary m n) [] [])) = false := by
    simp [tops, pst, d1]
  refine ⟨_, h1.seq (h2.seq (RunsLe.iteF hc (RunsLe.skip _))), ?_, ?_⟩
  · intro i
    refine ⟨fun hi => ?_, fun hi1 hi2 => ?_⟩
    · simp only [pst]; split_ifs <;> first | omega | rfl
    · simp only [pst]; split_ifs <;> first | omega | rfl
  · simp [pst, clockIdx]

/-- The constant of the time bound of `padDecider`. -/
def padK (m C s : ℕ) : ℕ := 2 * m + 28 + (C + 1) * (m + 14) + (s + 1) * (4 * m + 40) * (C + 2) ^ s

lemma padCost_le {m n j xl C s : ℕ} (hs : 1 ≤ s) (hj : j ≤ n) (hxl : xl ≤ n) :
    padCost m n j xl C s + ((C + 1) * (j + 1)) ^ s + 1 ≤ padK m C s * (n + 1) ^ s := by
  set P := (n + 1) ^ s
  have hP : n + 1 ≤ P := Nat.le_self_pow (by omega) _
  have hQ : ((C + 1) * (j + 1) + 1) ^ s ≤ (C + 2) ^ s * P := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) s
  have hU : ((C + 1) * (j + 1)) ^ s ≤ (C + 2) ^ s * P :=
    le_trans (Nat.pow_le_pow_left (by omega) s) hQ
  unfold padCost padK
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h_a : (2 * m + 16) * (n + 1) ≤ (2 * m + 16) * P := Nat.mul_le_mul_left _ hP
  have h_b : (C + 1) * (m + 14) * (n + 1) ≤ (C + 1) * (m + 14) * P := Nat.mul_le_mul_left _ hP
  have h_c : s * ((4 * m + 40) * ((C + 1) * (j + 1) + 1) ^ s) ≤
      s * ((4 * m + 40) * ((C + 2) ^ s * P)) := by gcongr
  have h_f : (C + 2) ^ s * P ≤ (4 * m + 40) * ((C + 2) ^ s * P) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have h_g : (C + 1) * ((m + 12) * (j + 1) + 2) ≤ (C + 1) * (m + 14) * (n + 1) := by
    rw [mul_assoc]; gcongr; nlinarith
  have h_h : (m + 6) * xl ≤ (m + 6) * n := Nat.mul_le_mul_left _ hxl
  nlinarith

lemma succ_pow_le (n s : ℕ) : (n + 1) ^ s ≤ 2 ^ s * (n ^ s + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [zero_add, one_pow]; exact Nat.mul_pos (Nat.two_pow_pos s) (Nat.succ_pos _)
  · calc (n + 1) ^ s ≤ (2 * n) ^ s := Nat.pow_le_pow_left (by omega) s
      _ = 2 ^ s * n ^ s := mul_pow 2 n s
      _ ≤ 2 ^ s * (n ^ s + 1) := by gcongr; omega

lemma padDecider_decides (hs : 1 ≤ s) (y : List Bool) :
    ∃ t, t ≤ padK ML.symbols C s * (y.length + 1) ^ s ∧
      Lax119563.DeterministicTime.DecidesExactlyWithin (padDecider ML C s) y (y ∈ padLang ML C s) t := by
  rcases split_last_true y with ⟨x, j, rfl⟩ | ⟨n, rfl⟩
  · obtain ⟨s', ⟨t, ht, hr⟩, hH, hK⟩ := padPrep_runs_true (C := C) (s := s) x j
    have hans := thenClocked_answer hr hH hK
    refine ⟨_, ?_, _, hans, ?_⟩
    · have := padCost_le (m := ML.symbols) (C := C) hs (j := j) (xl := x.length)
        (n := (x ++ true :: List.replicate j false).length) (by simp; omega) (by simp)
      omega
    · constructor
      · intro h
        refine ⟨x, j, rfl, ?_⟩
        revert h
        rcases (runOn ML x (((C + 1) * (j + 1)) ^ s)).answer with _ | _ | _ <;> simp
      · rintro ⟨x', j', hy, hacc⟩
        obtain ⟨rfl, rfl⟩ := last_true_unique hy
        rw [hacc]; rfl
  · obtain ⟨s', ⟨t, ht, hr⟩, hH, hK⟩ := padPrep_runs_false (C := C) (s := s) (ML := ML) n
    have hans := thenClocked_answer hr hH hK
    refine ⟨_, ?_, _, hans, ?_⟩
    · have hP : n + 1 ≤ (n + 1) ^ s := Nat.le_self_pow (by omega) _
      simp only [List.length_replicate]
      calc t + 0 + 1 ≤ (2 * ML.symbols + 28) * (n + 1) := by nlinarith
        _ ≤ (2 * ML.symbols + 28) * (n + 1) ^ s := Nat.mul_le_mul_left _ hP
        _ ≤ padK ML.symbols C s * (n + 1) ^ s := Nat.mul_le_mul_right _
          (by unfold padK; exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    · have h0 : (runOn ML [] 0).answer = none := rfl
      rw [h0]
      constructor
      · simp
      · rintro ⟨x', j', hy, -⟩
        have : true ∈ List.replicate n false := by rw [hy]; simp
        simp at this

theorem padLang_dt (ML : Machine) (C s : ℕ) (hs : 1 ≤ s) : DT (padLang ML C s) (s : ℝ) := by
  refine ⟨padDecider ML C s, thenClocked_deterministic _ _ _, padK ML.symbols C s * 2 ^ s,
    fun y => ?_⟩
  obtain ⟨t, ht, hd⟩ := padDecider_decides (ML := ML) (C := C) hs y
  refine decidesWithin_mono hd ?_
  apply Nat.le_floor
  have h1 := succ_pow_le y.length s
  have h2 : t ≤ padK ML.symbols C s * 2 ^ s * y.length ^ s + padK ML.symbols C s * 2 ^ s := by
    calc t ≤ padK ML.symbols C s * (y.length + 1) ^ s := ht
      _ ≤ padK ML.symbols C s * (2 ^ s * (y.length ^ s + 1)) := Nat.mul_le_mul_left _ h1
      _ = _ := by ring
  beta_reduce
  rw [Real.rpow_natCast]
  exact_mod_cast h2

end Spec

/-! ## Unpadding -/

section Unpad

variable (MP : Machine) (r : ℕ)

/-- Stack indices of the unpadding machine: scratch stacks after the tapes of `MP`. -/
def d2 (k : ℕ) (hk : k < 5 := by omega) : Fin (MP.tapes + 5 + 1) := ⟨MP.tapes + 1 + k, by omega⟩

/-- Write `x ++ [true] ++ 0^{|x|^r}` on stack `0`. -/
def unpadPrep : Prog (MP.tapes + 5 + 1) MP.symbols :=
  seq (moveCount 0 (d2 MP 0) (d2 MP 1))
    (seq (power (d2 MP 2) (d2 MP 1) (d2 MP 3) (d2 MP 4) r)
      (seq (moveAll (d2 MP 2) 0) (seq (push 0 1) (moveAll (d2 MP 0) 0))))

/-- Stacks in the shape used by `unpadPrep`. -/
def qst (a0 aA aN aP : List (Fin (MP.symbols + 2))) : Stacks (MP.tapes + 5 + 1) MP.symbols :=
  fun i => if i.val = 0 then a0 else if i.val = MP.tapes + 1 then aA else
    if i.val = MP.tapes + 2 then aN else if i.val = MP.tapes + 3 then aP else []

/-- Prove equalities between `qst` stacks and their updates. -/
macro "qst_eq" : tactic =>
  `(tactic| (funext i; simp only [qst, update_apply, Fin.ext_iff, Fin.val_zero, d2]; split_ifs <;>
    first | omega | rfl | simp_all))

/-- The cost bound of `unpadPrep`. -/
def unpadCost (m n r : ℕ) : ℕ :=
  (m + 8) * n + 1 + (r * ((4 * m + 40) * (n + 1) ^ r) + 3 + ((m + 6) * n ^ r + 1 + (2 +
    ((m + 6) * n + 1))))

variable {MP r}

lemma unpadPrep_runs (x : List Bool) :
    ∃ s', (unpadPrep MP r).RunsLe (inputStacks _ _ x) s' (unpadCost MP.symbols x.length r) ∧
      HandsOver MP s' (x ++ true :: List.replicate (x.length ^ r) false) := by
  have ne : ∀ a b : Fin (MP.tapes + 5 + 1), a.val ≠ b.val → a ≠ b :=
    fun a b h => Fin.ne_of_val_ne h
  set m := MP.symbols
  have hs0 : inputStacks (MP.tapes + 5) m x = qst MP (x.map (bitSym m)) [] [] [] := by
    funext i
    simp only [inputStacks, qst, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> first | omega | rfl
  rw [hs0]
  have h1 : (moveCount 0 (d2 MP 0) (d2 MP 1) : Prog _ m).RunsLe (qst MP (x.map (bitSym m)) [] [] [])
      (qst MP [] (x.map (bitSym m)).reverse (unary m x.length) []) ((m + 8) * x.length + 1) :=
    (moveCount_runs (ne _ _ (by simp [d2])) (ne _ _ (by simp [d2])) (ne _ _ (by simp [d2]))
      (x.map (bitSym m)) _ (by simp [qst])).of_eq (by simp only [List.length_map]; qst_eq)
      (by simp)
  have h2 := power_runs (p := d2 MP 2) (n := d2 MP 1) (q := d2 MP 3) (h := d2 MP 4) (b := x.length)
    (ne _ _ (by simp [d2])) (ne _ _ (by simp [d2])) (ne _ _ (by simp [d2])) (ne _ _ (by simp [d2]))
    (ne _ _ (by simp [d2])) (ne _ _ (by simp [d2])) r
    (s := qst MP [] (x.map (bitSym m)).reverse (unary m x.length) [])
    (by simp [qst, d2]) (by simp [qst, d2]) (by simp [qst, d2]) (by simp [qst, d2])
  have h2' := h2.of_eq (s₂ := qst MP [] (x.map (bitSym m)).reverse (unary m x.length) (unary m (x.length ^ r)))
    (by qst_eq) le_rfl
  have h3 : (moveAll (d2 MP 2) 0 : Prog _ m).RunsLe
      (qst MP [] (x.map (bitSym m)).reverse (unary m x.length) (unary m (x.length ^ r)))
      (qst MP (unary m (x.length ^ r)) (x.map (bitSym m)).reverse (unary m x.length) []) ((m + 6) * x.length ^ r + 1) :=
    (moveAll_runs (ne _ _ (by simp [d2])) (unary m (x.length ^ r)) _ (by simp [qst, d2])).of_eq
      (by simp only [List.reverse_replicate]; qst_eq) (by simp)
  have h4 : (push 0 1 : Prog _ m).RunsLe
      (qst MP (unary m (x.length ^ r)) (x.map (bitSym m)).reverse (unary m x.length) [])
      (qst MP (1 :: unary m (x.length ^ r)) (x.map (bitSym m)).reverse (unary m x.length) []) 2 :=
    (RunsLe.push _ _ _).of_eq (by qst_eq) le_rfl
  have h5 : (moveAll (d2 MP 0) 0 : Prog _ m).RunsLe
      (qst MP (1 :: unary m (x.length ^ r)) (x.map (bitSym m)).reverse (unary m x.length) [])
      (qst MP ((x ++ true :: List.replicate (x.length ^ r) false).map (bitSym m)) [] (unary m x.length) [])
      ((m + 6) * x.length + 1) :=
    (moveAll_runs (ne _ _ (by simp [d2])) (x.map (bitSym m)).reverse _ (by simp [qst, d2])).of_eq
      (by simp only [List.reverse_reverse, List.map_append, List.map_cons, List.map_replicate];
          qst_eq) (by simp)
  refine ⟨_, h1.seq (h2'.seq (h3.seq (h4.seq h5))), fun i => ⟨fun hi => ?_, fun hi1 hi2 => ?_⟩⟩
  · simp only [qst]; split_ifs <;> first | omega | rfl
  · simp only [qst]; split_ifs <;> first | omega | rfl

lemma unpadCost_le (m n r : ℕ) (hr : 1 ≤ r) :
    unpadCost m n r ≤ (3 * m + 28 + r * (4 * m + 40)) * (n + 1) ^ r := by
  unfold unpadCost
  set P := (n + 1) ^ r
  have hP : n + 1 ≤ P := Nat.le_self_pow (by omega) _
  have hP' : n ^ r ≤ P := Nat.pow_le_pow_left (by omega) r
  have h1 : (m + 8) * n ≤ (m + 8) * P := Nat.mul_le_mul_left _ (by omega)
  have h2 : (m + 6) * n ^ r ≤ (m + 6) * P := Nat.mul_le_mul_left _ hP'
  have h3 : (m + 6) * n ≤ (m + 6) * P := Nat.mul_le_mul_left _ (by omega)
  nlinarith

lemma succ_pow_le_rpow (n r : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    (((n + 1) ^ r : ℕ) : ℝ) ≤ 2 ^ r * (n : ℝ) ^ (a * r) + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ (a * r) := Real.rpow_nonneg (by simp) _
    simp only [zero_add, one_pow, Nat.cast_one] at *
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) r]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : (((n + 1) ^ r : ℕ) : ℝ) ≤ 2 ^ r * (n : ℝ) ^ r := by
      rw [← mul_pow]; push_cast
      exact pow_le_pow_left₀ (by positivity) (by linarith) r
    have h2 : (n : ℝ) ^ r ≤ (n : ℝ) ^ (a * r) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
    have : (0 : ℝ) ≤ 2 ^ r := by positivity
    nlinarith

lemma padLen_rpow_le (n r : ℕ) (hr : 1 ≤ r) {a : ℝ} (ha : 1 ≤ a) :
    (((n + (n ^ r + 1) : ℕ) : ℝ)) ^ a ≤ 3 ^ a * (n : ℝ) ^ (a * r) + 1 := by
  have h3 : (0 : ℝ) ≤ 3 ^ a * (n : ℝ) ^ (a * r) := by positivity
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [zero_add, zero_pow (by omega : r ≠ 0), Nat.cast_one, Real.one_rpow]
    linarith
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hle : ((n + (n ^ r + 1) : ℕ) : ℝ) ≤ 3 * (n : ℝ) ^ (r : ℝ) := by
      rw [Real.rpow_natCast]
      have : (n : ℝ) ≤ (n : ℝ) ^ r := by
        calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (n : ℝ) ^ r := pow_le_pow_right₀ hn1 hr
      have : (1 : ℝ) ≤ (n : ℝ) ^ r := one_le_pow₀ hn1
      push_cast; linarith
    calc (((n + (n ^ r + 1) : ℕ) : ℝ)) ^ a ≤ (3 * (n : ℝ) ^ (r : ℝ)) ^ a :=
          Real.rpow_le_rpow (by positivity) hle (by linarith)
      _ = 3 ^ a * (n : ℝ) ^ (a * r) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity),
            mul_comm (r : ℝ) a]
      _ ≤ _ := by linarith

lemma pad_mem_iff {L : Set (List Bool)} {ML : Machine} {C s r : ℕ} (hs : 1 ≤ s)
    (hML : ∀ x, Lax119563.DeterministicTime.DecidesExactlyWithin ML x (x ∈ L)
      ⌊(C : ℝ) * (x.length : ℝ) ^ ((s : ℝ) * r) + C⌋₊) (x : List Bool) :
    x ++ true :: List.replicate (x.length ^ r) false ∈ padLang ML C s ↔ x ∈ L := by
  set U := ((C + 1) * (x.length ^ r + 1)) ^ s
  obtain ⟨b, hb, hiff⟩ := hML x
  have hT : ⌊(C : ℝ) * (x.length : ℝ) ^ ((s : ℝ) * r) + C⌋₊ ≤ U := by
    apply Nat.floor_le_of_le
    have e : (x.length : ℝ) ^ ((s : ℝ) * r) = (((x.length ^ r) ^ s : ℕ) : ℝ) := by
      rw [mul_comm, Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast, Real.rpow_natCast]
      push_cast; ring
    rw [e]
    have key : C * (x.length ^ r) ^ s + C ≤ U := by
      set N := x.length ^ r
      have h1 : N ^ s + 1 ≤ (N + 1) ^ s := by
        obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
        rw [pow_succ, pow_succ]
        have := Nat.pow_le_pow_left (Nat.le_succ N) k
        have := Nat.one_le_pow k (N + 1) (Nat.succ_pos N)
        nlinarith
      have h2 : C + 1 ≤ (C + 1) ^ s := Nat.le_self_pow (by omega) _
      calc C * N ^ s + C ≤ C * N ^ s + C + (N ^ s + 1) := Nat.le_add_right _ _
        _ = (C + 1) * (N ^ s + 1) := by ring
        _ ≤ (C + 1) ^ s * (N + 1) ^ s := Nat.mul_le_mul h2 h1
        _ = U := by rw [← mul_pow]
    exact_mod_cast key
  have hb' : (runOn ML x U).answer = some b := drun_answer_mono hb hT
  constructor
  · rintro ⟨x', j', hy, hacc⟩
    obtain ⟨rfl, rfl⟩ := last_true_unique hy
    rw [hb'] at hacc
    exact hiff.mp (Option.some.inj hacc)
  · intro hx
    refine ⟨x, x.length ^ r, rfl, ?_⟩
    rw [hb', hiff.mpr hx]

/-- Unpadding: a fast decider of the padded language gives a fast decider of `L`. -/
theorem dt_of_padLang {L : Set (List Bool)} {ML : Machine} {C s r : ℕ} {a : ℝ} (hs : 1 ≤ s)
    (hr : 1 ≤ r) (ha : 1 ≤ a)
    (hML : ∀ x, Lax119563.DeterministicTime.DecidesExactlyWithin ML x (x ∈ L)
      ⌊(C : ℝ) * (x.length : ℝ) ^ ((s : ℝ) * r) + C⌋₊)
    (hP : DT (padLang ML C s) a) : DT L (a * r) := by
  obtain ⟨MP, hMP, CP, hCP⟩ := hP
  set K2 := 3 * MP.symbols + 28 + r * (4 * MP.symbols + 40)
  set C'' := ⌈(K2 : ℝ) * 2 ^ r + CP * 3 ^ a⌉₊ + K2 + 2 * CP
  refine ⟨thenRun MP 5 (unpadPrep MP r), thenRun_deterministic _ _ _, C'', fun x => ?_⟩
  obtain ⟨s', ⟨t, ht, hrun⟩, hH⟩ := unpadPrep_runs (MP := MP) (r := r) x
  set x' := x ++ true :: List.replicate (x.length ^ r) false
  obtain ⟨b, hb, hiff⟩ := hCP x'
  have hans := thenRun_answer hrun hH hb
  refine decidesWithin_mono ⟨b, hans, ?_⟩ ?_
  · rw [hiff, pad_mem_iff hs hML]
  · apply Nat.le_floor
    have hlen : x'.length = x.length + (x.length ^ r + 1) := by simp [x']
    beta_reduce
    rw [hlen, Nat.cast_add]
    have hC'' : (C'' : ℝ) = ⌈(K2 : ℝ) * 2 ^ r + CP * 3 ^ a⌉₊ + K2 + 2 * CP := by
      simp only [C'']; push_cast; ring
    rw [hC'']
    have e1 := unpadCost_le MP.symbols x.length r hr
    have e2 := succ_pow_le_rpow x.length r ha
    have e3 := padLen_rpow_le x.length r hr ha
    have e4 : ((⌊(CP : ℝ) * ((x.length + (x.length ^ r + 1) : ℕ) : ℝ) ^ a + CP⌋₊ : ℕ) : ℝ) ≤
        CP * ((x.length + (x.length ^ r + 1) : ℕ) : ℝ) ^ a + CP :=
      Nat.floor_le (by positivity)
    have e5 : ((t : ℕ) : ℝ) ≤ K2 * (((x.length + 1) ^ r : ℕ) : ℝ) := by
      exact_mod_cast le_trans ht e1
    have e6 := Nat.le_ceil ((K2 : ℝ) * 2 ^ r + CP * 3 ^ a)
    set X := (x.length : ℝ) ^ (a * r)
    have hX : 0 ≤ X := by positivity
    have hK2 : (0 : ℝ) ≤ K2 := Nat.cast_nonneg _
    have hCP0 : (0 : ℝ) ≤ CP := Nat.cast_nonneg _
    have f1 : (t : ℝ) ≤ K2 * 2 ^ r * X + K2 := by
      have := mul_le_mul_of_nonneg_left e2 hK2; linarith
    have f2 : ((⌊(CP : ℝ) * (x.length + (x.length ^ r + 1) : ℕ) ^ a + CP⌋₊ : ℕ) : ℝ) ≤
        CP * 3 ^ a * X + 2 * CP := by
      have := mul_le_mul_of_nonneg_left e3 hCP0; linarith
    have f3 := mul_le_mul_of_nonneg_right e6 hX
    have f4 : 0 ≤ ((K2 : ℝ) + 2 * CP) * X := by positivity
    have f5 : (0 : ℝ) ≤ ⌈(K2 : ℝ) * 2 ^ r + CP * 3 ^ a⌉₊ := Nat.cast_nonneg _
    nlinarith

end Unpad

/-- The padding step of the translational argument. -/
theorem pad_step (s : ℕ) (a : ℝ) (hs : 1 ≤ s) (ha : 1 ≤ a) (r : ℕ) (hr : 1 ≤ r)
    (L : Set (List Bool)) (hL : DT L ((s : ℝ) * r)) :
    ∃ L', DT L' (s : ℝ) ∧ (DT L' a → DT L (a * r)) := by
  obtain ⟨ML, -, C, hC⟩ := hL
  exact ⟨padLang ML C s, padLang_dt ML C s hs, fun h => dt_of_padLang hs hr ha hC h⟩


end Lax119563Proofs.Hierarchy

end Hierarchy_Padding

/-! ### Formerly `Lax119563Proofs.Hierarchy.Reduction` -/

section Hierarchy_Reduction

/-!
# Reduction of the hierarchy theorem to a coarse hierarchy

With padding (`pad_step`) and the linear case (`lin`), the translational argument reduces the
time hierarchy theorem to the statement that for every `b` some `DTIME(n^B)` is not contained
in `DTIME(n^b)`.
-/

open Lax119563.DeterministicTime

namespace Lax119563Proofs.Hierarchy

/-- A coarse hierarchy: for every exponent `b` some polynomial class escapes `DTIME(n^b)`. -/
def CoarseHierarchy : Prop := ∀ b : ℕ, ∃ B : ℕ, ∃ L, DT L (B : ℝ) ∧ ¬ DT L (b : ℝ)

theorem time_hierarchy_of_coarse (coarse : CoarseHierarchy) (s : ℕ) (hs : 1 ≤ s) (a : ℝ)
    (ha : a < s) :
    ∃ L : Set (List Bool),
      DecidableInTime L (fun n => (n : ℝ) ^ s) ∧ ¬ DecidableInTime L (fun n => (n : ℝ) ^ a) :=
  hierarchy_of pad_step coarse lin s hs a ha

end Lax119563Proofs.Hierarchy

end Hierarchy_Reduction

/-! ### Formerly `Lax119563Proofs.Hierarchy.UnivSim` -/

section Hierarchy_UnivSim

/-!
# The universal simulator as a stack program

Tokens, stack names and the program `Universal.sim`, a stack program over the tokens
`F T U S R M E N H0 H1 L Z Rt Sep End`. Correctness is only needed on inputs
`y = code M ++ z`; on other inputs a clock bounds the running time.

* Code: tokens, 4 bits each. Token stream `R^{k+1} Sep R^k Sep table End`, where `k + 1` is
  the number of tapes of `M`, and `table` is the concatenation over all keys `(q, c)` of
  `key(q, c) ++ [M] ++ (ins (δ q c)).reverse ++ [E]` with
  `key(q, c) = enc q ++ enc c_k ++ … ++ enc c_0`, `enc n = U^n S`, `ins (halt b) = [H_b]`,
  `ins (next q' w mv) = N :: enc q' ++ ⋯ (enc w_j ++ [mv_j]) ⋯`.
* Configuration of `M`: state `q` in unary on `QS`; stack `LS` holds for `j = 0..k` the cells
  left of head `j` (nearest first, encoded) each followed by `R`; `RS` likewise the scanned
  cell and the cells to its right (an empty right part means blank).
* Init: parse the code from stack `0` (keeping the consumed bits on `Y`), move the two `R`
  blocks to `LS`/`RS`, keep the table on `TBL`, push `R` and the input symbols onto `RS`.
* Step: (1) build `KEY` by copying the scanned symbol of each record of `RS` (rotating
  records through `RS2`) and then `enc q`; (2) search `TBL` for the entry whose key equals
  `KEY` (token comparison through `KEY2`/`TBL2`), copy its instruction to `INS` (reversing
  it); (3) on `H_b` push `H_b` on `DONE`; on `N` set `QS := q'` and for each record write
  `w_j` and move (`L`: one symbol `LS → RS`, `Rt`: `RS → LS`), rotating records through
  `LS2`/`RS2`.
* Cost: every phase is `O((size of all stacks + 1)^2)`; sizes grow by `O(m)` per step, so `T`
  simulated steps cost `c_M (n + T + 1)^3`.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog

/-- Tokens. -/
abbrev Tok := Fin 15

abbrev tT : Tok := 1
/-- Unary unit and end of a number. -/
abbrev tU : Tok := 2
abbrev tS : Tok := 3
/-- End of a tape record. -/
abbrev tR : Tok := 4
/-- End of a key, end of a table entry. -/
abbrev tM : Tok := 5
abbrev tE : Tok := 6
/-- Instruction heads: continue, halt with `false`/`true`. -/
abbrev tN : Tok := 7
abbrev tH0 : Tok := 8
abbrev tH1 : Tok := 9
/-- Head moves. -/
abbrev tL : Tok := 10
abbrev tZ : Tok := 11
abbrev tRt : Tok := 12
/-- Block separator and end of the code. -/
abbrev tSep : Tok := 13
abbrev tEnd : Tok := 14

/-- The stacks of the simulator. -/
abbrev Stk := Fin 16

abbrev IN : Stk := 0
abbrev Y : Stk := 1
abbrev P : Stk := 2
abbrev LS : Stk := 3
abbrev RS : Stk := 4
abbrev LS2 : Stk := 5
abbrev RS2 : Stk := 6
abbrev QS : Stk := 7
abbrev KEY : Stk := 8
abbrev KEY2 : Stk := 9
abbrev TBL : Stk := 10
abbrev TBL2 : Stk := 11
abbrev INS : Stk := 12
abbrev TMP : Stk := 13
abbrev DONE : Stk := 14
abbrev FLG : Stk := 15

attribute [simp] IN Y P LS RS LS2 RS2 QS KEY KEY2 TBL TBL2 INS TMP DONE FLG
attribute [simp] tT tU tS tR tM tE tN tH0 tH1 tL tZ tRt tSep tEnd

/-- Programs of the simulator. -/
abbrev SProg := Prog 16 13

/-- Top-symbol conditions. -/
abbrev Cond := (Stk → Option Tok) → Bool

def isTop (i : Stk) (a : Tok) : Cond := fun r => r i == some a
def nonempty (i : Stk) : Cond := fun r => (r i).isSome
def isEmpty (i : Stk) : Cond := fun r => (r i).isNone

/-! ## Parsing the code -/

/-- The token with a 4-bit code `v`, or `none` for the end of the code. -/
def tokOf (v : ℕ) : Option Tok := if h : v < 12 then some ⟨v + 2, by omega⟩ else none

/-- Read `k` bits from `IN` (keeping them on `Y`), then emit the token of the accumulated
value: push it on `P`, or flag the end of the code on `FLG`. -/
def readBits : ℕ → ℕ → SProg
  | 0, acc =>
    match tokOf acc with
    | some t => push P t
    | none => push FLG 0
  | k + 1, acc =>
    ite (isTop IN tT) (seq (moveOne IN Y) (readBits k (2 * acc + 1)))
      (seq (moveOne IN Y) (readBits k (2 * acc)))

/-- Parse the code into `P` (reversed) and move the rest of the input to `Y`. -/
def parse : SProg :=
  seq (loop (isEmpty FLG) (readBits 4 0)) (seq (moveAll IN Y) (pop FLG))

/-- Encode the input bits on `Y` (reversed) as the right part of tape `0` on `RS`. -/
def inputToRS : SProg :=
  loop (nonempty Y)
    (seq (ite (isTop Y tT) (seq (push RS tS) (seq (push RS tU) (push RS tU)))
      (seq (push RS tS) (push RS tU))) (pop Y))

/-- Initialisation. -/
def init : SProg :=
  seq parse
    (seq (moveAll P TBL)
      (seq (moveWhileNot TBL LS tSep)
        (seq (pop TBL)
          (seq (moveWhileNot TBL RS tSep)
            (seq (pop TBL) (seq (push RS tR) inputToRS))))))

/-! ## One simulated step -/

/-- Copy the scanned symbol of the top record of `RS` to `KEY` (blank if the record's right part
is empty). -/
def copyScanned : SProg :=
  ite (isTop RS tR) (push KEY tS) (seq (moveThrough RS TMP tS) (dupAll TMP RS KEY))

/-- Build the key: scanned symbols of all tapes, then the state. -/
def buildKey : SProg :=
  seq (loop (nonempty RS) (seq copyScanned (moveThrough RS RS2 tR)))
    (seq (moveAll RS2 RS) (seq (push KEY tS) (seq (dupAll QS TMP KEY) (moveAll TMP QS))))

/-- Duplicate tokens from `i` onto `j` and `k` while the top of `i` is not `a`. -/
def dupWhileNot (i j k : Stk) (a : Tok) : SProg :=
  loop (fun r => (r i).isSome && r i != some a)
    (seq (pushTopOf i j (List.finRange 15)) (seq (pushTopOf i k (List.finRange 15)) (pop i)))

/-- Compare `KEY` with the key of the current table entry. -/
def compare : SProg :=
  loop (fun r => (r KEY).isSome && r KEY == r TBL) (seq (moveOne KEY KEY2) (moveOne TBL TBL2))

/-- Examine one table entry: on a match copy its instruction to `INS` and flag it. -/
def examine : SProg :=
  seq compare
    (seq (ite (fun r => (r KEY).isNone && r TBL == some tM)
        (seq (push FLG 0) (seq (moveOne TBL TBL2) (dupWhileNot TBL TBL2 INS tE)))
        (moveThrough TBL TBL2 tE))
      (moveAll KEY2 KEY))

/-- Look the key up in the table. -/
def lookup : SProg :=
  seq (loop (fun r => (r TBL).isSome && (r FLG).isNone) examine)
    (seq (moveAll TBL2 TBL) (seq (pop FLG) (clear KEY)))

/-- Erase the scanned symbol of the top record of `RS` (if any). -/
def eraseScanned : SProg :=
  ite (isTop RS tR) skip (seq (moveThrough RS TMP tS) (clear TMP))

/-- Write the next symbol of the instruction on top of `RS`. -/
def writeSym : SProg := seq (moveThrough INS TMP tS) (moveAll TMP RS)

/-- Move the head of the top record according to the next token of the instruction. -/
def moveHead : SProg :=
  ite (isTop INS tL)
    (seq (pop INS)
      (ite (isTop LS tR) (push RS tS) (seq (moveThrough LS TMP tS) (moveAll TMP RS))))
    (ite (isTop INS tRt)
      (seq (pop INS) (seq (moveThrough RS TMP tS) (moveAll TMP LS)))
      (pop INS))

/-- Apply a `next` instruction. -/
def applyNext : SProg :=
  seq (pop INS)
    (seq (clear QS) (seq (moveWhileNot INS QS tS) (seq (pop INS)
      (seq (loop (nonempty RS)
          (seq eraseScanned (seq writeSym (seq moveHead
            (seq (moveThrough LS LS2 tR) (moveThrough RS RS2 tR))))))
        (seq (moveAll LS2 LS) (moveAll RS2 RS))))))

/-- Apply the instruction on `INS`. -/
def apply : SProg :=
  ite (fun r => r INS == some tH0 || r INS == some tH1) (moveOne INS DONE) applyNext

/-- One simulated step. -/
def simStep : SProg := seq buildKey (seq lookup apply)

/-- The simulator. -/
def sim : SProg := seq init (loop (isEmpty DONE) simStep)

/-- The answer of the simulator: the negation of the simulated answer. -/
def simAns (r : Stk → Option Tok) : Bool := r DONE == some tH0

end Lax119563Proofs.Hierarchy.Universal

end Hierarchy_UnivSim

/-! ### Formerly `Lax119563Proofs.Hierarchy.UnivKey` -/

section Hierarchy_UnivKey

/-!
# Encodings of configurations, and building the key

Symbols are natural numbers encoded in unary (`encN n = U^n S`); a tape record is a list of
encoded symbols followed by `R`.  `buildKey` pushes on `KEY` the encoded scanned symbols of all
records of `RS` (last record first) and then the encoded state.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog Function

/-- The unary encoding of a number. -/
def encN (n : ℕ) : List Tok := List.replicate n tU ++ [tS]

/-- The encoding of a list of numbers. -/
def encL (l : List ℕ) : List Tok := l.flatMap encN

/-- A tape record. -/
def record (l : List ℕ) : List Tok := encL l ++ [tR]

/-- The encoding of a list of records. -/
def records (rs : List (List ℕ)) : List Tok := rs.flatMap record

lemma tS_not_mem_rep (n : ℕ) : tS ∉ List.replicate n tU := by
  simp only [List.mem_replicate]; intro h; exact absurd h.2 (by decide)

lemma tR_not_mem_encL (l : List ℕ) : tR ∉ encL l := by
  simp only [encL, encN, List.mem_flatMap, List.mem_append, List.mem_replicate, List.mem_singleton,
    not_exists, not_and, not_or]
  intro x _; exact ⟨fun _ => by decide, by decide⟩

@[simp] lemma length_encN (n : ℕ) : (encN n).length = n + 1 := by simp [encN]

@[simp] lemma length_record (l : List ℕ) : (record l).length = (encL l).length + 1 := by
  simp [record]

/-- The key contribution of a right part: its first symbol, blank if empty. -/
def scannedOf (r : List ℕ) : ℕ := r.headD 0

/-- Shorthand for the cost constant of symbol transfers. -/
abbrev cK : ℕ := 100

lemma copyScanned_runs (r : List ℕ) (rest : List (List ℕ)) (s : Stacks 16 13) (hs : s RS = record r ++ records rest)
    (hT : s TMP = []) :
    copyScanned.RunsLe s (update s KEY (encN (scannedOf r) ++ s KEY))
      (cK * ((encN (scannedOf r)).length + 1)) := by
  cases r with
  | nil =>
    refine ((RunsLe.push KEY tS s).iteT (by simp [tops, hs, record, encL, isTop])).of_eq ?_
      (by simp [scannedOf, cK])
    simp [scannedOf, encN]
  | cons c r =>
    have hs' : s RS = List.replicate c tU ++ tS :: (encL r ++ [tR] ++ records rest) := by
      rw [hs]; simp [record, encL, encN]
    have h1 := moveThrough_runs (i := RS) (j := TMP) (by decide) (tS_not_mem_rep c) hs'
    rw [hT, List.append_nil] at h1
    have h2 := dupAll_runs (i := TMP) (j := RS) (k := KEY) (by decide) (by decide) (by decide)
      (tS :: (List.replicate c tU).reverse)
      (update (update s RS (encL r ++ [tR] ++ records rest)) TMP (tS :: (List.replicate c tU).reverse))
      (by simp)
    have hc : isTop RS tR (tops s) = false := by
      cases c <;> simp [tops, hs', isTop, List.replicate_succ] <;> decide
    refine ((h1.seq h2).iteF hc).of_eq ?_ ?_
    · clear h1 h2 hc
      simp only [List.reverse_cons, List.reverse_reverse, List.reverse_replicate, scannedOf,
        List.headD_cons, encN]
      funext k
      simp only [update_apply]
      split_ifs <;> simp_all (config := { decide := true }) [record, encL, encN]
    · simp only [scannedOf, List.headD_cons, length_encN, List.length_cons, List.length_reverse,
        List.length_replicate]
      nlinarith

/-- Prove equalities between updated simulator stacks. -/
macro "sim_eq" : tactic =>
  `(tactic| (funext k; fin_cases k <;> simp_all (config := {decide := true}) [Function.update_apply]))

lemma length_encN_scanned_le (r : List ℕ) : (encN (scannedOf r)).length ≤ (record r).length := by
  cases r with
  | nil => simp [scannedOf, record, encL]
  | cons c r => simp [scannedOf, record, encL]

lemma records_cons (r : List ℕ) (rs : List (List ℕ)) :
    records (r :: rs) = record r ++ records rs := by simp [records]

/-- The loop of `buildKey`. -/
def keyLoop : SProg := loop (nonempty RS) (seq copyScanned (moveThrough RS RS2 tR))

lemma keyLoop_runs :
    ∀ (rs : List (List ℕ)) (s : Stacks 16 13), s RS = records rs → s TMP = [] →
      keyLoop.RunsLe s (update (update (update s RS []) RS2 ((records rs).reverse ++ s RS2)) KEY
        ((rs.map (fun r => encN (scannedOf r))).reverse.flatten ++ s KEY))
        (4 * cK * (records rs).length + 1)
  | [], s, hs, _ =>
    (RunsLe.loopF (c := nonempty RS) (s := s) (p := seq copyScanned (moveThrough RS RS2 tR))
      (by simp [tops, hs, nonempty, records])).of_eq (by simp [records] at hs; sim_eq)
      (by simp)
  | r :: rs, s, hs, hT => by
    rw [records_cons] at hs
    have h1 := copyScanned_runs r rs s hs hT
    set s₁ := update s KEY (encN (scannedOf r) ++ s KEY)
    have hs₁ : s₁ RS = encL r ++ tR :: records rs := by simp (config := {decide := true}) [Function.update_apply, s₁, hs, record]
    have h2 := moveThrough_runs (i := RS) (j := RS2) (by decide) (tR_not_mem_encL r) hs₁
    set s₂ := update (update s₁ RS (records rs)) RS2 (tR :: ((encL r).reverse ++ s₁ RS2))
    have h3 := keyLoop_runs rs s₂ (by simp (config := {decide := true}) [Function.update_apply, s₂]) (by simp (config := {decide := true}) [Function.update_apply, s₂, s₁, hT])
    have hc : nonempty RS (tops s) = true := by
      cases r <;> simp [tops, hs, nonempty, record, encL, encN] <;> cases ‹ℕ› <;> simp
    refine (RunsLe.loopT hc (h1.seq h2) h3).of_eq ?_ ?_
    · simp only [s₂, s₁, records_cons, record, List.map_cons, List.reverse_cons,
        List.flatten_append, List.reverse_append, List.append_assoc]
      sim_eq
    · have := length_encN_scanned_le r
      simp only [records_cons, List.length_append, length_record] at this ⊢
      nlinarith

/-- The key of a configuration: the encoded state and the scanned symbols (last tape first). -/
def keyOf (q : ℕ) (rs : List (List ℕ)) : List Tok :=
  encN q ++ (rs.map (fun r => encN (scannedOf r))).reverse.flatten

lemma buildKey_runs (rs : List (List ℕ)) (q : ℕ) (s : Stacks 16 13) (hs : s RS = records rs)
    (hT : s TMP = []) (hR2 : s RS2 = []) (hQ : s QS = List.replicate q tU) (hK : s KEY = []) :
    buildKey.RunsLe s (update s KEY (keyOf q rs)) (5 * cK * ((records rs).length + q + 1)) := by
  have h1 := keyLoop_runs rs s hs hT
  set s₁ := update (update (update s RS []) RS2 ((records rs).reverse ++ s RS2)) KEY
    ((rs.map (fun r => encN (scannedOf r))).reverse.flatten ++ s KEY)
  have h2 := moveAll_runs (i := RS2) (j := RS) (by decide) ((records rs).reverse) s₁
    (by simp (config := {decide := true}) [Function.update_apply, s₁, hR2])
  set s₂ := update (update s₁ RS2 []) RS ((records rs).reverse.reverse ++ s₁ RS)
  have h3 := RunsLe.push KEY tS s₂
  set s₃ := update s₂ KEY (tS :: s₂ KEY)
  have h4 := dupAll_runs (i := QS) (j := TMP) (k := KEY) (by decide) (by decide) (by decide)
    (List.replicate q tU) s₃ (by simp (config := {decide := true}) [Function.update_apply, s₃, s₂, s₁, hQ])
  set s₄ := update (update (update s₃ QS []) TMP ((List.replicate q tU).reverse ++ s₃ TMP)) KEY
    ((List.replicate q tU).reverse ++ s₃ KEY)
  have h5 := moveAll_runs (i := TMP) (j := QS) (by decide) (List.replicate q tU) s₄
    (by simp (config := {decide := true}) [Function.update_apply, s₄, s₃, s₂, s₁, hT])
  refine (h1.seq (h2.seq (h3.seq (h4.seq h5)))).of_eq ?_ ?_
  · simp only [s₄, s₃, s₂, s₁, keyOf, encN, List.reverse_reverse, List.reverse_replicate]
    sim_eq
  · simp only [List.length_reverse, List.length_replicate]
    nlinarith

end Lax119563Proofs.Hierarchy.Universal

end Hierarchy_UnivKey

/-! ### Formerly `Lax119563Proofs.Hierarchy.UnivLookup` -/

section Hierarchy_UnivLookup

/-!
# Looking up the key in the table

A table is a list of entries `(key, ins)`, laid out as `key ++ [M] ++ ins.reverse ++ [E]`.
`lookup` finds the first entry whose key equals `KEY` and leaves its instruction on `INS`.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog Function

/-- The layout of a table entry. -/
def entryToks (e : List Tok × List Tok) : List Tok := e.1 ++ tM :: e.2.reverse ++ [tE]

/-- The layout of a table. -/
def tableToks (es : List (List Tok × List Tok)) : List Tok := es.flatMap entryToks

/-- Keys use only the tokens `U` and `S`; instructions do not use `E`. -/
def WellFormed (e : List Tok × List Tok) : Prop :=
  (∀ t ∈ e.1, t = tU ∨ t = tS) ∧ tE ∉ e.2

lemma dupWhileNot_runs {i j k : Stk} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a : Tok)
    (l₂ : List Tok) (hl₂ : l₂.head? = some a) :
    ∀ (l : List Tok) (s : Stacks 16 13), a ∉ l → s i = l ++ l₂ →
      (dupWhileNot i j k a).RunsLe s
        (update (update (update s i l₂) j (l.reverse ++ s j)) k (l.reverse ++ s k))
        (40 * l.length + 1)
  | [], s, _, hs =>
    (RunsLe.loopF (c := fun r => (r i).isSome && r i != some a) (s := s)
      (p := seq (pushTopOf i j (List.finRange 15)) (seq (pushTopOf i k (List.finRange 15)) (pop i)))
      (by simp [tops, hs, hl₂])).of_eq (by simp at hs; stacks_eq) (by simp)
  | b :: l, s, ha, hs => by
    have hb : b ≠ a := fun h => ha (by simp [h])
    set s₁ := update (update (update s i (l ++ l₂)) j (b :: s j)) k (b :: s k)
    have hbody : (seq (pushTopOf i j (List.finRange 15)) (seq (pushTopOf i k (List.finRange 15))
        (pop i)) : SProg).RunsLe s s₁ 39 := by
      have h1 := pushTopOf_runs i j (s := s) (by simp [tops, hs]) (List.finRange 15)
        (List.mem_finRange b)
      have h2 := pushTopOf_runs i k (s := update s j (b :: s j))
        (by simp [tops, update_of_ne hij, hs]) (List.finRange 15) (List.mem_finRange b)
      have h3 := RunsLe.pop i (update (update s j (b :: s j)) k (b :: update s j (b :: s j) k))
      refine (h1.seq (h2.seq h3)).of_eq ?_ (by simp)
      funext x
      simp only [s₁, update_apply]
      split_ifs <;> simp_all
    have h2 := dupWhileNot_runs hij hik hjk a l₂ hl₂ l s₁ (fun h => ha (by simp [h]))
      (by simp [s₁, update_of_ne hij, update_of_ne hik])
    refine (RunsLe.loopT (c := fun r => (r i).isSome && r i != some a) (by simp [tops, hs, hb])
      hbody h2).of_eq ?_ (le_of_eq (by simp only [List.length_cons]; ring))
    funext x
    simp only [s₁, update_apply]
    split_ifs <;> simp_all

lemma compare_runs :
    ∀ (c a b : List Tok) (s : Stacks 16 13), s KEY = c ++ a → s TBL = c ++ b →
      (a = [] ∨ a.head? ≠ b.head?) →
      compare.RunsLe s (update (update (update (update s KEY a) KEY2 (c.reverse ++ s KEY2)) TBL b)
        TBL2 (c.reverse ++ s TBL2)) (40 * c.length + 1)
  | [], a, b, s, hK, hT, hab =>
    (RunsLe.loopF (c := fun r => (r KEY).isSome && r KEY == r TBL) (s := s)
      (p := seq (moveOne KEY KEY2) (moveOne TBL TBL2)) (by
        rcases hab with rfl | h
        · simp [tops, hK]
        · simp only [List.nil_append] at hK hT
          simp [tops, hK, hT, h])).of_eq (by simp at hK hT; sim_eq) (by simp)
  | x :: c, a, b, s, hK, hT, hab => by
    set s₁ := update (update (update (update s KEY (c ++ a)) KEY2 (x :: s KEY2)) TBL (c ++ b))
      TBL2 (x :: s TBL2)
    have h1 := moveOne_runs (i := KEY) (j := KEY2) (by decide) (s := s) (a := x) (l := c ++ a)
      (by simp [hK])
    have h2 := moveOne_runs (i := TBL) (j := TBL2) (by decide) (a := x) (l := c ++ b)
      (s := update (update s KEY (c ++ a)) KEY2 (x :: s KEY2)) (by simp [hT])
    have hbody : (seq (moveOne KEY KEY2) (moveOne TBL TBL2) : SProg).RunsLe s s₁ 36 :=
      (h1.seq h2).of_eq (by simp only [s₁]; sim_eq) (by simp)
    have h3 := compare_runs c a b s₁ (by simp [s₁]) (by simp [s₁]) hab
    refine (RunsLe.loopT (c := fun r => (r KEY).isSome && r KEY == r TBL) (by simp [tops, hK, hT])
      hbody h3).of_eq ?_ (by simp only [List.length_cons]; omega)
    simp only [s₁]
    sim_eq

/-- The longest common prefix decomposition. -/
lemma exists_lcp {α : Type} [DecidableEq α] :
    ∀ x y : List α, ∃ c a b, x = c ++ a ∧ y = c ++ b ∧ (a = [] ∨ a.head? ≠ b.head?)
  | [], y => ⟨[], [], y, rfl, rfl, .inl rfl⟩
  | h :: x, [] => ⟨[], h :: x, [], rfl, rfl, .inr (by simp)⟩
  | h :: x, h' :: y => by
    by_cases hh : h = h'
    · subst hh
      obtain ⟨c, a, b, rfl, rfl, hab⟩ := exists_lcp x y
      exact ⟨h :: c, a, b, rfl, rfl, hab⟩
    · exact ⟨[], h :: x, h' :: y, rfl, rfl, .inr (by simp [hh])⟩

lemma append_cons_cancel {α : Type} {x : α} :
    ∀ {l₁ l₂ r₁ r₂ : List α}, x ∉ l₁ → x ∉ l₂ → l₁ ++ x :: r₁ = l₂ ++ x :: r₂ → l₁ = l₂ ∧ r₁ = r₂
  | [], [], _, _, _, _, h => by simpa using h
  | [], y :: l₂, _, _, _, h₂, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h₂
  | y :: l₁, [], _, _, h₁, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h₁
  | y :: l₁, y' :: l₂, _, _, h₁, h₂, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := append_cons_cancel (fun hm => h₁ (List.mem_cons_of_mem _ hm))
      (fun hm => h₂ (List.mem_cons_of_mem _ hm)) h
    exact ⟨rfl, rfl⟩

lemma key_no_M {key : List Tok} (hk : ∀ t ∈ key, t = tU ∨ t = tS) : tM ∉ key := by
  intro h; rcases hk _ h with h | h <;> exact absurd h (by decide)

lemma key_no_E {key : List Tok} (hk : ∀ t ∈ key, t = tU ∨ t = tS) : tE ∉ key := by
  intro h; rcases hk _ h with h | h <;> exact absurd h (by decide)

/-- An entry whose key matches. -/
lemma examine_match {key ins rest : List Tok} (hk : ∀ t ∈ key, t = tU ∨ t = tS) (hi : tE ∉ ins)
    (s : Stacks 16 13) (hK : s KEY = key) (hT : s TBL = entryToks (key, ins) ++ rest)
    (hK2 : s KEY2 = []) :
    examine.RunsLe s (update (update (update (update s FLG (0 :: s FLG)) TBL (tE :: rest)) TBL2
      (ins ++ tM :: (key.reverse ++ s TBL2))) INS (ins ++ s INS))
      (100 * ((entryToks (key, ins)).length + 1)) := by
  have hT' : s TBL = key ++ (tM :: (ins.reverse ++ tE :: rest)) := by
    rw [hT]; simp [entryToks]
  have h1 := compare_runs key [] _ s (by simp [hK]) hT' (.inl rfl)
  set s₁ := update (update (update (update s KEY []) KEY2 (key.reverse ++ s KEY2)) TBL
    (tM :: (ins.reverse ++ tE :: rest))) TBL2 (key.reverse ++ s TBL2)
  have hc : (fun r : Stk → Option Tok => (r KEY).isNone && r TBL == some tM) (tops s₁) = true := by
    simp [tops, s₁]
  have h2 := RunsLe.push FLG 0 s₁
  set s₂ := update s₁ FLG (0 :: s₁ FLG)
  have h3 := moveOne_runs (i := TBL) (j := TBL2) (by decide) (s := s₂) (a := tM)
    (l := ins.reverse ++ tE :: rest) (by simp [s₂, s₁])
  set s₃ := update (update s₂ TBL (ins.reverse ++ tE :: rest)) TBL2 (tM :: s₂ TBL2)
  have h4 := dupWhileNot_runs (i := TBL) (j := TBL2) (k := INS) (by decide) (by decide)
    (by decide) tE (tE :: rest) (by simp) ins.reverse s₃ (by simpa using hi) (by simp [s₃])
  set s₄ := update (update (update s₃ TBL (tE :: rest)) TBL2 (ins.reverse.reverse ++ s₃ TBL2)) INS
    (ins.reverse.reverse ++ s₃ INS)
  have h5 := moveAll_runs (i := KEY2) (j := KEY) (by decide) key.reverse s₄
    (by simp [s₄, s₃, s₂, s₁, hK2])
  refine (h1.seq (((h2.seq (h3.seq h4)).iteT hc).seq h5)).of_eq ?_ ?_
  · simp only [s₄, s₃, s₂, s₁, List.reverse_reverse]
    sim_eq
  · simp only [entryToks, List.length_append, List.length_cons, List.length_reverse,
      List.length_nil]
    nlinarith

/-- An entry whose key does not match. -/
lemma examine_mismatch {key rest : List Tok} {e : List Tok × List Tok}
    (hk : ∀ t ∈ key, t = tU ∨ t = tS) (he : WellFormed e) (hne : e.1 ≠ key)
    (s : Stacks 16 13) (hK : s KEY = key) (hT : s TBL = entryToks e ++ rest)
    (hK2 : s KEY2 = []) :
    examine.RunsLe s (update (update s TBL rest) TBL2 ((entryToks e).reverse ++ s TBL2))
      (100 * ((entryToks e).length + key.length + 1)) := by
  set u := e.1 ++ tM :: e.2.reverse with hu
  have hEu : tE ∉ u := by
    simp only [u, List.mem_append, List.mem_cons, List.mem_reverse, not_or]
    exact ⟨key_no_E he.1, by decide, he.2⟩
  have hT' : s TBL = u ++ tE :: rest := by rw [hT]; simp [entryToks, u]
  obtain ⟨c, a, b, hka, hcb, hab⟩ := exists_lcp key (u ++ tE :: rest)
  have hEc : tE ∉ c := fun h => key_no_E hk (hka ▸ List.mem_append_left _ h)
  -- `c` is a prefix of `u`
  obtain ⟨b₀, hub, hb⟩ : ∃ b₀, u = c ++ b₀ ∧ b = b₀ ++ tE :: rest := by
    rcases List.append_eq_append_iff.mp hcb.symm with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
    · exact ⟨a', h1, h2⟩
    · cases c' with
      | nil => exact ⟨[], by simpa using h1.symm, by simpa using h2.symm⟩
      | cons t c' =>
        simp only [List.cons_append, List.cons.injEq] at h2
        exact absurd (h1 ▸ h2.1 ▸ List.mem_append_right _ List.mem_cons_self) hEc
  have h1 := compare_runs c a b s (by rw [hK, hka]) (by rw [hT', hcb]) hab
  set s₁ := update (update (update (update s KEY a) KEY2 (c.reverse ++ s KEY2)) TBL b) TBL2
    (c.reverse ++ s TBL2)
  have hc : (fun r : Stk → Option Tok => (r KEY).isNone && r TBL == some tM) (tops s₁) = false := by
    simp only [tops, s₁]
    rcases a with _ | ⟨t, a⟩
    · -- the key is a prefix of the entry; it must not be followed by `M`
      simp only [List.append_nil] at hka
      subst hka
      cases b with
      | nil => simp
      | cons t b =>
        by_cases ht : t = tM
        · subst ht
          exfalso
          have := hcb
          rw [show u ++ tE :: rest = e.1 ++ tM :: (e.2.reverse ++ tE :: rest) by simp [u]] at this
          exact hne (append_cons_cancel (key_no_M he.1) (key_no_M hk) this).1
        · simp [ht]
    · simp
  have h2 := moveThrough_runs (i := TBL) (j := TBL2) (by decide) (s := s₁) (l₁ := b₀) (l₂ := rest)
    (fun h => hEu (hub ▸ List.mem_append_right _ h)) (by simp [s₁, hb])
  set s₂ := update (update s₁ TBL rest) TBL2 (tE :: (b₀.reverse ++ s₁ TBL2))
  have h3 := moveAll_runs (i := KEY2) (j := KEY) (by decide) c.reverse s₂ (by simp [s₂, s₁, hK2])
  refine (h1.seq ((h2.iteF hc).seq h3)).of_eq ?_ ?_
  · have hent : (entryToks e).reverse = tE :: (b₀.reverse ++ c.reverse) := by
      simp [entryToks, ← hu, hub]
    simp only [s₂, s₁, List.reverse_reverse, hent]
    funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hK, hka, hK2]
  · have hcl : c.length ≤ key.length := by rw [hka]; simp
    have hcl' : (entryToks e).length = c.length + b₀.length + 1 := by
      have : entryToks e = u ++ [tE] := by simp [entryToks, u]
      rw [this, hub, List.length_append, List.length_append]; rfl
    simp only [List.length_reverse]
    nlinarith

lemma tableToks_cons (e : List Tok × List Tok) (es : List (List Tok × List Tok)) :
    tableToks (e :: es) = entryToks e ++ tableToks es := by simp [tableToks]

lemma two_le_entry (e : List Tok × List Tok) : 2 ≤ (entryToks e).length := by
  simp [entryToks]; omega

/-- The loop of `lookup`. -/
def lookupLoop : SProg := loop (fun r => (r TBL).isSome && (r FLG).isNone) examine

lemma lookupLoop_runs {key ins rest : List Tok} (hk : ∀ t ∈ key, t = tU ∨ t = tS)
    (hi : tE ∉ ins) :
    ∀ (es₁ : List (List Tok × List Tok)) (s : Stacks 16 13),
      (∀ e ∈ es₁, WellFormed e ∧ e.1 ≠ key) → s KEY = key → s KEY2 = [] → s FLG = [] →
      s TBL = tableToks es₁ ++ entryToks (key, ins) ++ rest →
      lookupLoop.RunsLe s (update (update (update (update s FLG [0]) TBL (tE :: rest)) TBL2
        (ins ++ tM :: (key.reverse ++ ((tableToks es₁).reverse ++ s TBL2)))) INS (ins ++ s INS))
        (200 * ((tableToks es₁).length + (entryToks (key, ins)).length + 1) * (key.length + 1))
  | [], s, _, hK, hK2, hF, hT => by
    have h1 := examine_match hk hi s hK (by simpa [tableToks] using hT) hK2
    set s₁ := update (update (update (update s FLG (0 :: s FLG)) TBL (tE :: rest)) TBL2
      (ins ++ tM :: (key.reverse ++ s TBL2))) INS (ins ++ s INS)
    have h2 := RunsLe.loopF (c := fun r => (r TBL).isSome && (r FLG).isNone) (p := examine)
      (s := s₁) (by simp [tops, s₁])
    have hc : (fun r : Stk → Option Tok => (r TBL).isSome && (r FLG).isNone) (tops s) = true := by
      have : (tableToks ([] : List (List Tok × List Tok)) ++ entryToks (key, ins) ++ rest).head?
          = (key ++ [tM]).head? := by
        cases key <;> simp [tableToks, entryToks]
      simp only [tops, hT, hF, this]
      cases key <;> simp
    refine (RunsLe.loopT hc h1 h2).of_eq ?_ ?_
    · simp only [s₁, hF, tableToks, List.flatMap_nil, List.reverse_nil, List.nil_append]
    · have := two_le_entry (key, ins)
      simp only [tableToks, List.flatMap_nil, List.length_nil]
      nlinarith
  | e :: es₁, s, hes, hK, hK2, hF, hT => by
    have he := hes e List.mem_cons_self
    have h1 := examine_mismatch (rest := tableToks es₁ ++ entryToks (key, ins) ++ rest) hk he.1
      he.2 s hK (by rw [hT, tableToks_cons]; simp only [List.append_assoc]) hK2
    set s₁ := update (update s TBL (tableToks es₁ ++ entryToks (key, ins) ++ rest)) TBL2
      ((entryToks e).reverse ++ s TBL2)
    have h2 := lookupLoop_runs (key := key) (ins := ins) (rest := rest) hk hi es₁ s₁ (fun e' h => hes e' (List.mem_cons_of_mem _ h))
      (by simp [s₁, hK]) (by simp [s₁, hK2]) (by simp [s₁, hF]) (by simp [s₁])
    have hc : (fun r : Stk → Option Tok => (r TBL).isSome && (r FLG).isNone) (tops s) = true := by
      have hne : tableToks (e :: es₁) ++ entryToks (key, ins) ++ rest ≠ [] := by
        simp [tableToks_cons, entryToks]
      simp only [tops, hT, hF]
      cases h : (tableToks (e :: es₁) ++ entryToks (key, ins) ++ rest) with
      | nil => exact absurd h hne
      | cons _ _ => simp
    refine (RunsLe.loopT hc h1 h2).of_eq ?_ ?_
    · simp only [s₁, tableToks_cons, List.reverse_append, List.append_assoc]
      sim_eq
    · have h2e := two_le_entry e
      simp only [tableToks_cons, List.length_append]
      nlinarith

/-- Looking up a key present in the table. -/
lemma lookup_runs {key ins : List Tok} {es₁ es₂ : List (List Tok × List Tok)}
    (hk : ∀ t ∈ key, t = tU ∨ t = tS) (hi : tE ∉ ins)
    (hes : ∀ e ∈ es₁, WellFormed e ∧ e.1 ≠ key) (s : Stacks 16 13)
    (hK : s KEY = key) (hK2 : s KEY2 = []) (hF : s FLG = []) (hT2 : s TBL2 = [])
    (hT : s TBL = tableToks (es₁ ++ (key, ins) :: es₂)) :
    lookup.RunsLe s (update (update s KEY []) INS (ins ++ s INS))
      (300 * ((tableToks (es₁ ++ (key, ins) :: es₂)).length + 1) * (key.length + 1)) := by
  have hT' : s TBL = tableToks es₁ ++ entryToks (key, ins) ++ tableToks es₂ := by
    rw [hT]; simp [tableToks]
  have h1 := lookupLoop_runs hk hi es₁ s hes hK hK2 hF hT'
  set s₁ := update (update (update (update s FLG [0]) TBL (tE :: tableToks es₂)) TBL2
    (ins ++ tM :: (key.reverse ++ ((tableToks es₁).reverse ++ s TBL2)))) INS (ins ++ s INS)
  have h2 := moveAll_runs (i := TBL2) (j := TBL) (by decide)
    (ins ++ tM :: (key.reverse ++ (tableToks es₁).reverse)) s₁ (by simp [s₁, hT2])
  set s₂ := update (update s₁ TBL2 []) TBL
    ((ins ++ tM :: (key.reverse ++ (tableToks es₁).reverse)).reverse ++ s₁ TBL)
  have h3 := RunsLe.pop FLG s₂
  set s₃ := update s₂ FLG (s₂ FLG).tail
  have h4 := clear_runs KEY key s₃ (by simp [s₃, s₂, s₁, hK])
  refine (h1.seq (h2.seq (h3.seq h4))).of_eq ?_ ?_
  · have : (ins ++ tM :: (key.reverse ++ (tableToks es₁).reverse)).reverse ++ tE :: tableToks es₂
        = tableToks (es₁ ++ (key, ins) :: es₂) := by
      simp [tableToks, entryToks]
    simp only [s₃, s₂, s₁]
    funext k; fin_cases k <;>
      simp (config := {decide := true}) [update_apply, hT, hT2, hF, tableToks, entryToks]
  · have htl : (tableToks (es₁ ++ (key, ins) :: es₂)).length =
        (tableToks es₁).length + (entryToks (key, ins)).length + (tableToks es₂).length := by
      simp only [tableToks, List.flatMap_append, List.flatMap_cons, List.length_append]; omega
    have hent : (entryToks (key, ins)).length = key.length + ins.length + 2 := by
      simp [entryToks]; omega
    simp only [List.length_append, List.length_cons, List.length_reverse]
    rw [htl]
    nlinarith

end Lax119563Proofs.Hierarchy.Universal

end Hierarchy_UnivLookup

/-! ### Formerly `Lax119563Proofs.Hierarchy.UnivApply` -/

section Hierarchy_UnivApply

/-!
# Applying an instruction to the tape records

For each tape, `applyNext` erases the scanned symbol, writes the new one and moves the head
(transferring one symbol between the left and the right part).
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog Function Lax489179.TuringMachine

/-- The token of a head move. -/
def mvTok : Move → Tok
  | .left => tL
  | .stay => tZ
  | .right => tRt

/-- The effect of writing `w` and moving by `mv` on a tape given by its left and right parts. -/
def tapeUpd (l r : List ℕ) (w : ℕ) : Move → List ℕ × List ℕ
  | .left => match l with
    | [] => ([], 0 :: w :: r.tail)
    | c :: l' => (l', c :: w :: r.tail)
  | .stay => (l, w :: r.tail)
  | .right => (w :: l, r.tail)

lemma record_cons (c : ℕ) (l : List ℕ) : record (c :: l) = encN c ++ record l := by
  simp [record, encL]

lemma eraseScanned_runs (r : List ℕ) (R : List Tok) (s : Stacks 16 13)
    (hs : s RS = record r ++ R) (hT : s TMP = []) :
    eraseScanned.RunsLe s (update s RS (record r.tail ++ R)) (cK * (r.headD 0 + 2)) := by
  cases r with
  | nil =>
    refine ((RunsLe.skip s).iteT (by simp [tops, isTop, hs, record, encL])).of_eq ?_
      (by simp [cK])
    funext k; by_cases hk : k = RS
    · subst hk; simp [hs]
    · simp [update_of_ne hk]
  | cons c r =>
    have hs' : s RS = List.replicate c tU ++ tS :: (record r ++ R) := by
      rw [hs, record_cons]; simp [encN]
    have h1 := moveThrough_runs (i := RS) (j := TMP) (by decide) (tS_not_mem_rep c) hs'
    have h2 := clear_runs TMP (tS :: ((List.replicate c tU).reverse ++ s TMP))
      (update (update s RS (record r ++ R)) TMP (tS :: ((List.replicate c tU).reverse ++ s TMP)))
      (by simp)
    have hc : isTop RS tR (tops s) = false := by
      cases c <;> simp [tops, hs', isTop, List.replicate_succ]
    refine ((h1.seq h2).iteF hc).of_eq ?_ ?_
    · funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hT]
    · simp [hT, cK]; nlinarith

lemma writeSym_runs (w : ℕ) (I : List Tok) (s : Stacks 16 13) (hs : s INS = encN w ++ I)
    (hT : s TMP = []) :
    writeSym.RunsLe s (update (update s INS I) RS (encN w ++ s RS)) (cK * (w + 2)) := by
  have hs' : s INS = List.replicate w tU ++ tS :: I := by rw [hs]; simp [encN]
  have h1 := moveThrough_runs (i := INS) (j := TMP) (by decide) (tS_not_mem_rep w) hs'
  have h2 := moveAll_runs (i := TMP) (j := RS) (by decide)
    (tS :: ((List.replicate w tU).reverse ++ s TMP))
    (update (update s INS I) TMP (tS :: ((List.replicate w tU).reverse ++ s TMP))) (by simp)
  refine (h1.seq h2).of_eq ?_ ?_
  · funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hT, encN]
  · simp [hT, cK]; nlinarith

lemma moveHead_runs (l r : List ℕ) (w : ℕ) (mv : Move) (I L R : List Tok) (s : Stacks 16 13)
    (hI : s INS = mvTok mv :: I) (hL : s LS = record l ++ L) (hR : s RS = record (w :: r.tail) ++ R)
    (hT : s TMP = []) :
    moveHead.RunsLe s (update (update (update s INS I) LS (record (tapeUpd l r w mv).1 ++ L)) RS
      (record (tapeUpd l r w mv).2 ++ R)) (cK * (w + l.headD 0 + 3)) := by
  cases mv with
  | left =>
    have hc : isTop INS tL (tops s) = true := by simp [tops, isTop, hI, mvTok]
    have h1 := RunsLe.pop INS s
    set s₁ := update s INS (s INS).tail
    cases l with
    | nil =>
      have hc2 : isTop LS tR (tops s₁) = true := by simp [tops, isTop, s₁, hL, record, encL]
      have h2 := RunsLe.push RS tS s₁
      refine ((h1.seq ((h2.iteT hc2))).iteT hc).of_eq ?_ (by simp [cK]; omega)
      funext k; fin_cases k <;>
        simp (config := {decide := true}) [update_apply, s₁, hI, hL, hR, tapeUpd, record_cons, encN]
    | cons c l =>
      have hL' : s₁ LS = List.replicate c tU ++ tS :: (record l ++ L) := by
        simp [s₁, hL, record_cons, encN]
      have hc2 : isTop LS tR (tops s₁) = false := by
        cases c <;> simp [tops, isTop, s₁, hL, record_cons, encN, List.replicate_succ]
      have h2 := moveThrough_runs (i := LS) (j := TMP) (by decide) (tS_not_mem_rep c) hL'
      set s₂ := update (update s₁ LS (record l ++ L)) TMP
        (tS :: ((List.replicate c tU).reverse ++ s₁ TMP))
      have h3 := moveAll_runs (i := TMP) (j := RS) (by decide)
        (tS :: ((List.replicate c tU).reverse ++ s₁ TMP)) s₂ (by simp [s₂])
      refine ((h1.seq ((h2.seq h3).iteF hc2)).iteT hc).of_eq ?_ ?_
      · funext k; fin_cases k <;>
          simp (config := {decide := true}) [update_apply, s₂, s₁, hI, hL, hR, hT, tapeUpd,
            record_cons, encN]
      · simp [s₁, hT, cK]; nlinarith
  | stay =>
    have hc : isTop INS tL (tops s) = false := by simp [tops, isTop, hI, mvTok]
    have hc2 : isTop INS tRt (tops s) = false := by simp [tops, isTop, hI, mvTok]
    refine (((RunsLe.pop INS s).iteF hc2).iteF hc).of_eq ?_ (by simp [cK]; omega)
    funext k; fin_cases k <;>
      simp (config := {decide := true}) [update_apply, hI, hL, hR, tapeUpd]
  | right =>
    have hc : isTop INS tL (tops s) = false := by simp [tops, isTop, hI, mvTok]
    have hc2 : isTop INS tRt (tops s) = true := by simp [tops, isTop, hI, mvTok]
    have h1 := RunsLe.pop INS s
    set s₁ := update s INS (s INS).tail
    have hR' : s₁ RS = List.replicate w tU ++ tS :: (record r.tail ++ R) := by
      simp [s₁, hR, record_cons, encN]
    have h2 := moveThrough_runs (i := RS) (j := TMP) (by decide) (tS_not_mem_rep w) hR'
    set s₂ := update (update s₁ RS (record r.tail ++ R)) TMP
      (tS :: ((List.replicate w tU).reverse ++ s₁ TMP))
    have h3 := moveAll_runs (i := TMP) (j := LS) (by decide)
      (tS :: ((List.replicate w tU).reverse ++ s₁ TMP)) s₂ (by simp [s₂])
    refine (((h1.seq (h2.seq h3)).iteT hc2).iteF hc).of_eq ?_ ?_
    · funext k; fin_cases k <;>
        simp (config := {decide := true}) [update_apply, s₂, s₁, hI, hL, hR, hT, tapeUpd,
          record_cons, encN]
    · simp [s₁, hT, cK]; nlinarith

@[simp] lemma length_encL_cons (c : ℕ) (l : List ℕ) :
    (encL (c :: l)).length = c + 1 + (encL l).length := by simp [encL]

lemma length_encL_tail (r : List ℕ) :
    (encL r.tail).length + (r.headD 0 + 1) ≤ (encL r).length + 1 := by
  cases r <;> simp <;> omega

lemma tapeUpd_length (l r : List ℕ) (w : ℕ) (mv : Move) :
    (encL (tapeUpd l r w mv).1).length + (encL (tapeUpd l r w mv).2).length ≤
      (encL l).length + (encL r).length + w + 2 := by
  have := length_encL_tail r
  cases mv with
  | left => cases l <;> simp [tapeUpd] <;> omega
  | stay => simp [tapeUpd]; omega
  | right => simp [tapeUpd]; omega

lemma head_le_encL (l : List ℕ) : l.headD 0 ≤ (encL l).length := by
  cases l <;> simp <;> omega

/-- The work on one tape record. -/
def recBody : SProg :=
  seq eraseScanned (seq writeSym (seq moveHead
    (seq (moveThrough LS LS2 tR) (moveThrough RS RS2 tR))))

lemma recBody_runs (l r : List ℕ) (w : ℕ) (mv : Move) (I L R : List Tok) (s : Stacks 16 13)
    (hI : s INS = encN w ++ mvTok mv :: I) (hL : s LS = record l ++ L) (hR : s RS = record r ++ R)
    (hT : s TMP = []) :
    recBody.RunsLe s (update (update (update (update (update s INS I) LS L) RS R) LS2
      ((record (tapeUpd l r w mv).1).reverse ++ s LS2)) RS2
      ((record (tapeUpd l r w mv).2).reverse ++ s RS2))
      (3 * cK * ((encL l).length + (encL r).length + w + 3)) := by
  have h1 := eraseScanned_runs r R s hR hT
  set s₁ := update s RS (record r.tail ++ R)
  have h2 := writeSym_runs w (mvTok mv :: I) s₁ (by simp [s₁, hI]) (by simp [s₁, hT])
  set s₂ := update (update s₁ INS (mvTok mv :: I)) RS (encN w ++ s₁ RS)
  have h3 := moveHead_runs l r w mv I L R s₂ (by simp [s₂]) (by simp [s₂, s₁, hL])
    (by simp [s₂, s₁, record_cons]) (by simp [s₂, s₁, hT])
  set s₃ := update (update (update s₂ INS I) LS (record (tapeUpd l r w mv).1 ++ L)) RS
    (record (tapeUpd l r w mv).2 ++ R)
  have h4 := moveThrough_runs (i := LS) (j := LS2) (by decide) (s := s₃) (l₂ := L)
    (tR_not_mem_encL (tapeUpd l r w mv).1) (by simp [s₃, record])
  set s₄ := update (update s₃ LS L) LS2 (tR :: ((encL (tapeUpd l r w mv).1).reverse ++ s₃ LS2))
  have h5 := moveThrough_runs (i := RS) (j := RS2) (by decide) (s := s₄) (l₂ := R)
    (tR_not_mem_encL (tapeUpd l r w mv).2) (by simp [s₄, s₃, record])
  refine (h1.seq (h2.seq (h3.seq (h4.seq h5)))).of_eq ?_ ?_
  · funext k; fin_cases k <;>
      simp (config := {decide := true}) [update_apply, s₄, s₃, s₂, s₁, hT, record]
  · have e1 := tapeUpd_length l r w mv
    have e2 := head_le_encL l
    have e3 := head_le_encL r
    simp only [cK]
    nlinarith

/-- The tapes as left part, right part, symbol to write and move. -/
abbrev Tp := List ℕ × List ℕ × ℕ × Move

/-- The instruction tokens for the tapes. -/
def insPairs (ts : List Tp) : List Tok := ts.flatMap (fun t => encN t.2.2.1 ++ [mvTok t.2.2.2])

/-- The loop over the tape records in `applyNext`. -/
def recLoop : SProg := loop (nonempty RS) recBody

lemma recLoop_runs :
    ∀ (ts : List Tp) (s : Stacks 16 13), s INS = insPairs ts → s LS = records (ts.map (·.1)) →
      s RS = records (ts.map (·.2.1)) → s TMP = [] →
      recLoop.RunsLe s (update (update (update (update (update s INS []) LS []) RS []) LS2
        ((records (ts.map (fun t => (tapeUpd t.1 t.2.1 t.2.2.1 t.2.2.2).1))).reverse ++ s LS2)) RS2
        ((records (ts.map (fun t => (tapeUpd t.1 t.2.1 t.2.2.1 t.2.2.2).2))).reverse ++ s RS2))
        (3 * cK * ((s LS).length + (s RS).length + (s INS).length + 1) + 1)
  | [], s, hI, hL, hR, _ =>
    (RunsLe.loopF (c := nonempty RS) (p := recBody) (s := s) (by simp [tops, nonempty, hR,
      records])).of_eq (by
        simp only [insPairs, records, List.map_nil, List.flatMap_nil] at hI hL hR
        funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hI, hL, hR])
      (by omega)
  | ⟨l, r, w, mv⟩ :: ts, s, hI, hL, hR, hT => by
    have h1 := recBody_runs l r w mv (insPairs ts) (records (ts.map (·.1)))
      (records (ts.map (·.2.1))) s (by simp [hI, insPairs]) (by simp [hL, records_cons])
      (by simp [hR, records_cons]) hT
    set s₁ := update (update (update (update (update s INS (insPairs ts)) LS
      (records (ts.map (·.1)))) RS (records (ts.map (·.2.1)))) LS2
      ((record (tapeUpd l r w mv).1).reverse ++ s LS2)) RS2
      ((record (tapeUpd l r w mv).2).reverse ++ s RS2)
    have h2 := recLoop_runs ts s₁ (by simp [s₁]) (by simp [s₁]) (by simp [s₁]) (by simp [s₁, hT])
    have hc : nonempty RS (tops s) = true := by
      cases r <;> simp [tops, nonempty, hR, records_cons, record, encL, encN] <;>
        cases ‹ℕ› <;> simp
    refine (RunsLe.loopT hc h1 h2).of_eq ?_ ?_
    · funext k; fin_cases k <;>
        simp (config := {decide := true}) [update_apply, s₁, records_cons, List.reverse_append]
    · have eL : (s LS).length = (encL l).length + 1 + (s₁ LS).length := by
        simp [s₁, hL, records_cons]
      have eR : (s RS).length = (encL r).length + 1 + (s₁ RS).length := by
        simp [s₁, hR, records_cons]
      have eI : (s INS).length = w + 2 + (s₁ INS).length := by
        simp [s₁, hI, insPairs]; omega
      rw [eL, eR, eI]
      simp only [cK]
      omega

/-- The new left parts. -/
def newLefts (ts : List Tp) : List (List ℕ) := ts.map (fun t => (tapeUpd t.1 t.2.1 t.2.2.1 t.2.2.2).1)

/-- The new right parts. -/
def newRights (ts : List Tp) : List (List ℕ) :=
  ts.map (fun t => (tapeUpd t.1 t.2.1 t.2.2.1 t.2.2.2).2)

lemma newRecords_length :
    ∀ ts : List Tp, (records (newLefts ts)).length + (records (newRights ts)).length ≤
      (records (ts.map (·.1))).length + (records (ts.map (·.2.1))).length + (insPairs ts).length
  | [] => by simp [newLefts, newRights, records, insPairs]
  | ⟨l, r, w, mv⟩ :: ts => by
    have := newRecords_length ts
    have h := tapeUpd_length l r w mv
    simp only [newLefts, newRights, List.map_cons, records_cons, List.length_append,
      length_record, insPairs, List.flatMap_cons, length_encN, List.length_singleton] at this h ⊢
    omega

lemma applyNext_runs (q' : ℕ) (ts : List Tp) (Q : List Tok) (s : Stacks 16 13)
    (hI : s INS = tN :: (encN q' ++ insPairs ts)) (hQ : s QS = Q)
    (hL : s LS = records (ts.map (·.1))) (hR : s RS = records (ts.map (·.2.1)))
    (hT : s TMP = []) (hL2 : s LS2 = []) (hR2 : s RS2 = []) :
    applyNext.RunsLe s (update (update (update (update s INS []) QS (List.replicate q' tU)) LS
      (records (newLefts ts))) RS (records (newRights ts)))
      (6 * cK * ((s LS).length + (s RS).length + (s INS).length + Q.length + 1)) := by
  have h1 := RunsLe.pop INS s
  set s₁ := update s INS (s INS).tail
  have h2 := clear_runs QS Q s₁ (by simp [s₁, hQ])
  set s₂ := update s₁ QS []
  have h3 := moveWhileNot_runs (i := INS) (j := QS) (by decide) tS (tS :: insPairs ts) (by simp)
    (List.replicate q' tU) s₂ (tS_not_mem_rep q') (by simp [s₂, s₁, hI, encN])
  set s₃ := update (update s₂ INS (tS :: insPairs ts)) QS
    ((List.replicate q' tU).reverse ++ s₂ QS)
  have h4 := RunsLe.pop INS s₃
  set s₄ := update s₃ INS (s₃ INS).tail
  have h5 := recLoop_runs ts s₄ (by simp [s₄, s₃]) (by simp [s₄, s₃, s₂, s₁, hL])
    (by simp [s₄, s₃, s₂, s₁, hR]) (by simp [s₄, s₃, s₂, s₁, hT])
  set s₅ := update (update (update (update (update s₄ INS []) LS []) RS []) LS2
    ((records (ts.map (fun t => (tapeUpd t.1 t.2.1 t.2.2.1 t.2.2.2).1))).reverse ++ s₄ LS2)) RS2
    ((records (ts.map (fun t => (tapeUpd t.1 t.2.1 t.2.2.1 t.2.2.2).2))).reverse ++ s₄ RS2)
  have h6 := moveAll_runs (i := LS2) (j := LS) (by decide)
    (records (newLefts ts)).reverse s₅ (by simp [s₅, s₄, s₃, s₂, s₁, hL2, newLefts])
  set s₆ := update (update s₅ LS2 []) LS ((records (newLefts ts)).reverse.reverse ++ s₅ LS)
  have h7 := moveAll_runs (i := RS2) (j := RS) (by decide)
    (records (newRights ts)).reverse s₆ (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hR2, newRights])
  refine (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))).of_eq ?_ ?_
  · funext k; fin_cases k <;>
      simp (config := {decide := true}) [update_apply, s₆, s₅, s₄, s₃, s₂, s₁, hL2, hR2]
  · have e := newRecords_length ts
    have eL : (s₄ LS).length = (s LS).length := by simp [s₄, s₃, s₂, s₁]
    have eR : (s₄ RS).length = (s RS).length := by simp [s₄, s₃, s₂, s₁]
    have eI : (s₄ INS).length = (insPairs ts).length := by simp [s₄, s₃]
    have eI' : (s INS).length = q' + 2 + (insPairs ts).length := by simp [hI]; omega
    rw [eL, eR, eI]
    rw [← hL, ← hR] at e
    simp only [List.length_reverse, List.length_replicate, cK]
    simp only [newLefts, newRights] at e ⊢
    omega

/-- The halting token. -/
def haltTok (b : Bool) : Tok := if b then tH1 else tH0

lemma apply_halt (b : Bool) (s : Stacks 16 13) (hI : s INS = [haltTok b]) (hD : s DONE = []) :
    apply.RunsLe s (update (update s INS []) DONE [haltTok b]) 20 := by
  have hc : (fun r : Stk → Option Tok => r INS == some tH0 || r INS == some tH1) (tops s) = true := by
    cases b <;> simp [tops, hI, haltTok]
  refine ((moveOne_runs (i := INS) (j := DONE) (by decide) (l := []) hI).iteT hc).of_eq
    (by funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hD]) (by omega)

lemma apply_next (q' : ℕ) (ts : List Tp) (Q : List Tok) (s : Stacks 16 13)
    (hI : s INS = tN :: (encN q' ++ insPairs ts)) (hQ : s QS = Q)
    (hL : s LS = records (ts.map (·.1))) (hR : s RS = records (ts.map (·.2.1)))
    (hT : s TMP = []) (hL2 : s LS2 = []) (hR2 : s RS2 = []) :
    apply.RunsLe s (update (update (update (update s INS []) QS (List.replicate q' tU)) LS
      (records (newLefts ts))) RS (records (newRights ts)))
      (6 * cK * ((s LS).length + (s RS).length + (s INS).length + Q.length + 1) + 1) := by
  have hc : (fun r : Stk → Option Tok => r INS == some tH0 || r INS == some tH1) (tops s) = false := by
    simp [tops, hI]
  exact (applyNext_runs q' ts Q s hI hQ hL hR hT hL2 hR2).iteF hc

end Lax119563Proofs.Hierarchy.Universal

end Hierarchy_UnivApply

/-! ### Formerly `Lax119563Proofs.Hierarchy.UnivCode` -/

section Hierarchy_UnivCode

/-!
# The transition table of a machine

For a machine `M` of the model, the table has one entry per pair `(q, c)` of a state and a
tuple of scanned symbols: the key `enc q ++ enc c_k ++ ⋯ ++ enc c_0` and the instruction
`δ(q, c, false)` in the token form used by `apply`.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog Function Lax489179.TuringMachine

/-- The tokens of a key with state `q` and scanned symbols `c = [c_0, …, c_k]`. -/
def keyToks (q : ℕ) (c : List ℕ) : List Tok := encN q ++ encL c.reverse

lemma keyOf_eq (q : ℕ) (rs : List (List ℕ)) : keyOf q rs = keyToks q (rs.map scannedOf) := by
  simp only [keyOf, keyToks, encL, List.flatMap_def, List.map_reverse, List.map_map]
  rfl

lemma encN_cancel : ∀ {a b : ℕ} {l l' : List Tok}, encN a ++ l = encN b ++ l' → a = b ∧ l = l'
  | 0, 0, l, l', h => by simpa [encN] using h
  | 0, b + 1, l, l', h => by simp [encN, List.replicate_succ] at h
  | a + 1, 0, l, l', h => by simp [encN, List.replicate_succ] at h
  | a + 1, b + 1, l, l', h => by
    simp only [encN, List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    have := encN_cancel (a := a) (b := b) (l := l) (l' := l') (by simpa [encN] using h)
    exact ⟨by omega, this.2⟩

lemma encL_cons (c : ℕ) (l : List ℕ) : encL (c :: l) = encN c ++ encL l := by simp [encL]

lemma encL_inj : ∀ {l l' : List ℕ}, encL l = encL l' → l = l'
  | [], [], _ => rfl
  | [], c :: l, h => by simp [encL, encN] at h
  | c :: l, [], h => by simp [encL, encN] at h
  | c :: l, c' :: l', h => by
    rw [encL_cons, encL_cons] at h
    obtain ⟨rfl, h'⟩ := encN_cancel h
    rw [encL_inj h']

lemma keyToks_inj {q q' : ℕ} {c c' : List ℕ} (h : keyToks q c = keyToks q' c') :
    q = q' ∧ c = c' := by
  obtain ⟨rfl, h'⟩ := encN_cancel h
  exact ⟨rfl, List.reverse_injective (encL_inj h')⟩

lemma keyToks_tokens (q : ℕ) (c : List ℕ) : ∀ t ∈ keyToks q c, t = tU ∨ t = tS := by
  intro t ht
  simp only [keyToks, encL, encN, List.mem_append, List.mem_flatMap, List.mem_replicate,
    List.mem_singleton] at ht
  rcases ht with (⟨_, h⟩ | h) | ⟨_, _, (⟨_, h⟩ | h)⟩ <;> simp [h]

variable (M : Machine)

/-- Keys of the table. -/
abbrev Key := Fin (M.states + 1) × (Fin (M.tapes + 1) → Fin (M.symbols + 3))

/-- The tokens of the write/move part of an instruction. -/
def insPart (w : Fin (M.tapes + 1) → Fin (M.symbols + 3)) (mv : Fin (M.tapes + 1) → Move) :
    List Tok :=
  (List.ofFn fun j => encN (w j).val ++ [mvTok (mv j)]).flatten

/-- The tokens of an instruction. -/
def insOf : Instruction (M.tapes + 1) (M.symbols + 3) (M.states + 1) → List Tok
  | .halt b => [haltTok b]
  | .next q w mv => tN :: (encN q.val ++ insPart M w mv)

/-- The table entry of a key. -/
def entryOf (x : Key M) : List Tok × List Tok :=
  (keyToks x.1.val (List.ofFn fun j => (x.2 j).val), insOf M (M.transition x.1 x.2 false))

/-- The entries of the table. -/
noncomputable def entries : List (List Tok × List Tok) :=
  (Finset.univ : Finset (Key M)).toList.map (entryOf M)

/-- The table. -/
noncomputable def table : List Tok := tableToks (entries M)

variable {M}

lemma insOf_noE (i : Instruction (M.tapes + 1) (M.symbols + 3) (M.states + 1)) :
    tE ∉ insOf M i := by
  cases i with
  | halt b => cases b <;> simp [insOf, haltTok]
  | next q w mv =>
    simp only [insOf, insPart, encN, List.mem_cons, List.mem_append, List.mem_replicate,
      List.mem_flatten, List.mem_ofFn, List.mem_singleton, not_or]
    refine ⟨by decide, ⟨fun h => absurd h.2 (by decide), by decide⟩, ?_⟩
    rintro ⟨l, ⟨j, rfl⟩, h⟩
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at h
    rcases h with (⟨_, h⟩ | h) | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rcases hmv : mv j <;> simp [mvTok, hmv] at h

lemma entryOf_wf (x : Key M) : WellFormed (entryOf M x) :=
  ⟨keyToks_tokens _ _, insOf_noE _⟩

lemma entryOf_key_inj {x y : Key M} (h : (entryOf M x).1 = (entryOf M y).1) : x = y := by
  obtain ⟨h1, h2⟩ := keyToks_inj h
  have h2' : (fun j => (x.2 j).val) = fun j => (y.2 j).val := List.ofFn_injective h2
  ext1
  · exact Fin.ext h1
  · funext j; exact Fin.ext (congrFun h2' j)

lemma entries_split (x : Key M) :
    ∃ es₁ es₂, entries M = es₁ ++ entryOf M x :: es₂ ∧
      ∀ e ∈ es₁, WellFormed e ∧ e.1 ≠ (entryOf M x).1 := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem (Finset.mem_toList.mpr (Finset.mem_univ x))
  have hnd := Finset.nodup_toList (Finset.univ : Finset (Key M))
  rw [hst] at hnd
  have hx : x ∉ s := by
    intro hm
    have := List.nodup_append.mp hnd
    exact this.2.2 x hm x List.mem_cons_self rfl
  refine ⟨s.map (entryOf M), t.map (entryOf M), by simp [entries, hst], ?_⟩
  intro e he
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
  exact ⟨entryOf_wf y, fun h => hx (entryOf_key_inj h ▸ hy)⟩

end Lax119563Proofs.Hierarchy.Universal

end Hierarchy_UnivCode

/-! ### Formerly `Lax119563Proofs.Hierarchy.UnivTape` -/

section Hierarchy_UnivTape

/-!
# Tapes as left and right parts

`TapeRep T h l r`: the cells right of and at the head `h` are `r`, those left of it are `l`
(nearest first), and all others are blank.  Writing and moving acts as `tapeUpd`.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Lax489179.TuringMachine

/-- The tape `T` with head `h` is described by its left part `l` and right part `r`. -/
def TapeRep {n : ℕ} (T : ℤ → Fin (n + 3)) (h : ℤ) (l r : List ℕ) : Prop :=
  (∀ i : ℕ, (T (h + i)).val = r.getD i 0) ∧ (∀ i : ℕ, (T (h - 1 - i)).val = l.getD i 0)

lemma getD_tail (r : List ℕ) (i : ℕ) : r.tail.getD i 0 = r.getD (i + 1) 0 := by
  cases r <;> simp

lemma tapeRep_step {n : ℕ} {T : ℤ → Fin (n + 3)} {h : ℤ} {l r : List ℕ} (hT : TapeRep T h l r)
    (w : Fin (n + 3)) (mv : Move) :
    TapeRep (fun z => if z = h then w else T z) (h + mv.offset) (tapeUpd l r w.val mv).1
      (tapeUpd l r w.val mv).2 := by
  have hr : ∀ (z : ℤ) (i : ℕ), z = h + i → (T z).val = r.getD i 0 := by
    rintro z i rfl; exact hT.1 i
  have hl : ∀ (z : ℤ) (i : ℕ), z = h - 1 - i → (T z).val = l.getD i 0 := by
    rintro z i rfl; exact hT.2 i
  cases mv with
  | stay =>
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rcases i with _ | i
      · simp [tapeUpd, Move.offset]
      · simp only [tapeUpd]
        rw [if_neg (by simp only [Move.offset]; push_cast; omega), hr _ (i + 1) (by simp only [Move.offset]; push_cast; ring)]
        simp [getD_tail]
    · simp only [tapeUpd]
      rw [if_neg (by simp only [Move.offset]; omega), hl _ i (by simp only [Move.offset]; ring)]
  | right =>
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [tapeUpd]
      rw [if_neg (by simp only [Move.offset]; omega), hr _ (i + 1) (by simp only [Move.offset]; push_cast; ring), getD_tail]
    · rcases i with _ | i
      · simp [tapeUpd, Move.offset]
      · simp only [tapeUpd]
        rw [if_neg (by simp only [Move.offset]; push_cast; omega), hl _ i (by simp only [Move.offset]; push_cast; ring)]
        simp
  | left =>
    cases l with
    | nil =>
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rcases i with _ | _ | i
        · simp only [tapeUpd]
          rw [if_neg (by simp only [Move.offset]; omega), hl _ 0 (by simp only [Move.offset]; ring)]; simp
        · simp [tapeUpd, Move.offset]
        · simp only [tapeUpd]
          rw [if_neg (by simp only [Move.offset]; push_cast; omega), hr _ (i + 1) (by simp only [Move.offset]; push_cast; ring)]
          simp [getD_tail]
      · simp only [tapeUpd]
        rw [if_neg (by simp only [Move.offset]; omega), hl _ (i + 1) (by simp only [Move.offset]; push_cast; ring)]; simp
    | cons c l =>
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rcases i with _ | _ | i
        · simp only [tapeUpd]
          rw [if_neg (by simp only [Move.offset]; omega), hl _ 0 (by simp only [Move.offset]; ring)]; simp
        · simp [tapeUpd, Move.offset]
        · simp only [tapeUpd]
          rw [if_neg (by simp only [Move.offset]; push_cast; omega), hr _ (i + 1) (by simp only [Move.offset]; push_cast; ring)]
          simp [getD_tail]
      · simp only [tapeUpd]
        rw [if_neg (by simp only [Move.offset]; omega), hl _ (i + 1) (by simp only [Move.offset]; push_cast; ring)]; simp

end Lax119563Proofs.Hierarchy.Universal

end Hierarchy_UnivTape

/-! ### Formerly `Lax119563Proofs.Hierarchy.UnivStep` -/

section Hierarchy_UnivStep

/-!
# One simulated step

`Rel M c s`: the stacks `s` of the simulator represent the configuration `c` of `M`.  One run
of `simStep` either reproduces a step of `M` (`simStep_next`) or records its answer
(`simStep_halt`), at cost quadratic in the size of the stacks.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog Function Lax489179.TuringMachine

/-- The stacks represent the (running) configuration `c`. -/
def Rel (M : Machine) (c : Config M) (s : Stacks 16 13) : Prop :=
  c.answer = none ∧ ∃ lefts rights : Fin (M.tapes + 1) → List ℕ,
    (∀ j, TapeRep (c.tape j) (c.head j) (lefts j) (rights j)) ∧
    s LS = records (List.ofFn lefts) ∧ s RS = records (List.ofFn rights) ∧
    s QS = List.replicate c.state.val tU ∧ s TBL = table M ∧
    ∀ i, i ≠ LS → i ≠ RS → i ≠ QS → i ≠ TBL → s i = []

/-- The size of the tape records. -/
def recSize (s : Stacks 16 13) : ℕ := (s LS).length + (s RS).length

/-- The cost bound of one simulated step. -/
def stepCost (Z : ℕ) : ℕ := 3000 * (Z + 1) ^ 2

lemma length_encL_reverse (l : List ℕ) : (encL l.reverse).length = (encL l).length := by
  simp [encL, List.length_flatMap, List.map_reverse, List.sum_reverse]

lemma encL_scanned_le : ∀ rs : List (List ℕ),
    (encL (rs.map scannedOf)).length ≤ (records rs).length
  | [] => by simp [encL, records]
  | r :: rs => by
    have := encL_scanned_le rs
    have h := length_encN_scanned_le r
    simp only [List.map_cons, encL_cons, records_cons, List.length_append] at this h ⊢
    omega

lemma entry_le_table : ∀ {es : List (List Tok × List Tok)} {e}, e ∈ es →
    (entryToks e).length ≤ (tableToks es).length
  | e' :: es, e, h => by
    rw [tableToks_cons, List.length_append]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := entry_le_table h; omega

lemma entryOf_le_table {M : Machine} (x : Key M) :
    (entryToks (entryOf M x)).length ≤ (table M).length :=
  entry_le_table (List.mem_map.mpr ⟨x, Finset.mem_toList.mpr (Finset.mem_univ x), rfl⟩)

lemma state_le_table {M : Machine} (q : Fin (M.states + 1)) : q.val + 1 ≤ (table M).length := by
  have := entryOf_le_table (M := M) (q, fun _ => 0)
  simp only [entryOf, entryToks, keyToks, List.length_append, length_encN, List.length_cons,
    List.length_nil] at this
  omega

lemma ins_le_table {M : Machine} (x : Key M) :
    (insOf M (M.transition x.1 x.2 false)).length ≤ (table M).length := by
  have := entryOf_le_table (M := M) x
  simp only [entryOf, entryToks, List.length_append, List.length_cons, List.length_reverse,
    List.length_nil] at this
  omega

lemma cost_arith (L R T q K : ℕ) (hq : q + 1 ≤ T) (hK : K ≤ q + 1 + R) :
    5 * cK * (R + q + 1) + 300 * (T + 1) * (K + 1) ≤ 2000 * (L + R + T + 1) ^ 2 := by
  have h1 : R + q + 1 ≤ 2 * (L + R + T + 1) := by omega
  have h2 : T + 1 ≤ L + R + T + 1 := by omega
  have h3 : K + 1 ≤ 2 * (L + R + T + 1) := by omega
  have h4 : 1 ≤ L + R + T + 1 := by omega
  have h5 : (T + 1) * (K + 1) ≤ (L + R + T + 1) * (2 * (L + R + T + 1)) := Nat.mul_le_mul h2 h3
  simp only [cK]
  nlinarith

lemma RunsLe.assoc {p q r : SProg} {s s' : Stacks 16 13} {T : ℕ}
    (h : (seq (seq p q) r).RunsLe s s' T) : (seq p (seq q r)).RunsLe s s' T := by
  obtain ⟨t, ht, h⟩ := h
  cases h with
  | seq h₁ h₂ =>
    cases h₁ with
    | seq h₃ h₄ => exact ⟨_, by omega, .seq h₃ (.seq h₄ h₂)⟩

section

variable {M : Machine} {c : Config M} {s : Stacks 16 13}

lemma scanned_eq {lefts rights : Fin (M.tapes + 1) → List ℕ}
    (hT : ∀ j, TapeRep (c.tape j) (c.head j) (lefts j) (rights j)) :
    (List.ofFn rights).map scannedOf = List.ofFn (fun j => (c.tape j (c.head j)).val) := by
  rw [List.map_ofFn]
  congr 1
  funext j
  have := (hT j).1 0
  simp only [Nat.cast_zero, add_zero] at this
  rw [this]
  simp only [comp_apply, scannedOf]
  cases rights j <;> rfl

/-- Building the key and looking it up. -/
lemma keyLookup_runs {lefts rights : Fin (M.tapes + 1) → List ℕ}
    (hT : ∀ j, TapeRep (c.tape j) (c.head j) (lefts j) (rights j))
    (hL : s LS = records (List.ofFn lefts)) (hR : s RS = records (List.ofFn rights))
    (hQ : s QS = List.replicate c.state.val tU) (hTb : s TBL = table M)
    (h0 : ∀ i, i ≠ LS → i ≠ RS → i ≠ QS → i ≠ TBL → s i = []) :
    (seq buildKey lookup).RunsLe s
      (update s INS (insOf M (M.transition c.state (fun j => c.tape j (c.head j)) false)))
      (2000 * (recSize s + (table M).length + 1) ^ 2) := by
  have h1 := buildKey_runs (List.ofFn rights) c.state.val s hR (h0 _ (by decide) (by decide)
    (by decide) (by decide)) (h0 _ (by decide) (by decide) (by decide) (by decide)) hQ
    (h0 _ (by decide) (by decide) (by decide) (by decide))
  set x : Key M := (c.state, fun j => c.tape j (c.head j))
  have hkey : keyOf c.state.val (List.ofFn rights) = (entryOf M x).1 := by
    have := scanned_eq hT
    simp only [keyOf_eq, this, entryOf, x]
  obtain ⟨es₁, es₂, hes, hne⟩ := entries_split x
  have h2 := lookup_runs (key := (entryOf M x).1) (ins := (entryOf M x).2) (es₁ := es₁)
    (es₂ := es₂) (keyToks_tokens _ _) (insOf_noE _) hne (update s KEY (keyOf c.state.val
      (List.ofFn rights))) (by simp only [update_self]; exact hkey)
    (by simp [h0 KEY2 (by decide) (by decide) (by decide) (by decide)])
    (by simp [h0 FLG (by decide) (by decide) (by decide) (by decide)])
    (by simp [h0 TBL2 (by decide) (by decide) (by decide) (by decide)])
    (by simp [hTb, table, hes])
  refine (h1.seq h2).of_eq ?_ ?_
  · funext k; fin_cases k <;>
      simp (config := {decide := true}) [update_apply, entryOf, x,
        h0 INS (by decide) (by decide) (by decide) (by decide),
        h0 KEY (by decide) (by decide) (by decide) (by decide)]
  · -- costs
    have e1 : (keyOf c.state.val (List.ofFn rights)).length ≤ c.state.val + 1 + (s RS).length := by
      rw [keyOf_eq, hR]
      simp only [keyToks, List.length_append, length_encN, length_encL_reverse]
      have := encL_scanned_le (List.ofFn rights)
      omega
    have e2 := state_le_table c.state
    have hR' : (records (List.ofFn rights)).length = (s RS).length := by rw [hR]
    rw [hR', ← hes, ← table, ← hkey]
    simp only [recSize]
    exact cost_arith _ _ _ _ _ e2 e1

lemma simStep_halt {b : Bool} (hR : Rel M c s)
    (htr : M.transition c.state (fun j => c.tape j (c.head j)) false = .halt b) :
    ∃ s', simStep.RunsLe s s' (stepCost (recSize s + (table M).length)) ∧
      s' DONE = [haltTok b] := by
  obtain ⟨-, lefts, rights, hT, hL, hR, hQ, hTb, h0⟩ := hR
  have h1 := keyLookup_runs hT hL hR hQ hTb h0
  rw [htr] at h1
  have h2 := apply_halt b (update s INS (insOf M (.halt b))) (by simp [insOf])
    (by simp [h0 DONE (by decide) (by decide) (by decide) (by decide)])
  refine ⟨_, RunsLe.assoc ((h1.seq h2).mono ?_), by simp⟩
  have : 1 ≤ (recSize s + (table M).length + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [stepCost]; omega

lemma simStep_next {q' : Fin (M.states + 1)} {w : Fin (M.tapes + 1) → Fin (M.symbols + 3)}
    {mv : Fin (M.tapes + 1) → Move} (hR : Rel M c s)
    (htr : M.transition c.state (fun j => c.tape j (c.head j)) false = .next q' w mv) :
    ∃ s', simStep.RunsLe s s' (stepCost (recSize s + (table M).length)) ∧
      Rel M (step M false c) s' ∧ recSize s' ≤ recSize s + (table M).length := by
  obtain ⟨hans, lefts, rights, hT, hL, hR, hQ, hTb, h0⟩ := hR
  have h1 := keyLookup_runs hT hL hR hQ hTb h0
  rw [htr] at h1
  set ts : List Tp := List.ofFn (fun j => (lefts j, rights j, (w j).val, mv j))
  have hins : insPart M w mv = insPairs ts := by
    simp only [insPart, insPairs, ts, List.flatMap_def, List.map_ofFn]; rfl
  set s₁ := update s INS (insOf M (.next q' w mv))
  have h2 := apply_next q'.val ts (List.replicate c.state.val tU) s₁
    (by simp [s₁, insOf, hins]) (by simp [s₁, hQ])
    (by simp [s₁, hL, ts, List.map_ofFn]; rfl) (by simp [s₁, hR, ts, List.map_ofFn]; rfl)
    (by simp [s₁, h0 TMP (by decide) (by decide) (by decide) (by decide)])
    (by simp [s₁, h0 LS2 (by decide) (by decide) (by decide) (by decide)])
    (by simp [s₁, h0 RS2 (by decide) (by decide) (by decide) (by decide)])
  have hstep : step M false c = ⟨q', fun j => c.head j + (mv j).offset,
      fun j z => if z = c.head j then w j else c.tape j z, none⟩ := by
    simp [Lax489179.TuringMachine.step, hans, htr]
  have hnl : newLefts ts = List.ofFn (fun j => (tapeUpd (lefts j) (rights j) (w j).val (mv j)).1) :=
    by simp [newLefts, ts, List.map_ofFn]; rfl
  have hnr : newRights ts =
      List.ofFn (fun j => (tapeUpd (lefts j) (rights j) (w j).val (mv j)).2) := by
    simp [newRights, ts, List.map_ofFn]; rfl
  refine ⟨_, RunsLe.assoc ((h1.seq h2).mono ?_),
    ⟨by rw [hstep], fun j => (tapeUpd (lefts j) (rights j) (w j).val (mv j)).1,
      fun j => (tapeUpd (lefts j) (rights j) (w j).val (mv j)).2, fun j => ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_⟩
  · -- cost
    have e1 := ins_le_table (M := M) (c.state, fun j => c.tape j (c.head j))
    rw [htr] at e1
    have e2 := state_le_table c.state
    have eL : (s₁ LS).length = (s LS).length := by simp [s₁]
    have eR : (s₁ RS).length = (s RS).length := by simp [s₁]
    have eI : (s₁ INS).length = (insOf M (.next q' w mv)).length := by simp [s₁]
    rw [eL, eR, eI]
    simp only [stepCost, recSize, cK, List.length_replicate] at *
    nlinarith
  · rw [hstep]; exact tapeRep_step (hT j) (w j) (mv j)
  · rw [hnl]; simp
  · rw [hnr]; simp
  · rw [hstep]; simp
  · simp [s₁, hTb]
  · intro i h1 h2 h3 h4
    fin_cases i <;> simp_all (config := {decide := true}) [update_apply, s₁]
  · -- size
    have e := newRecords_length ts
    have e1 := ins_le_table (M := M) (c.state, fun j => c.tape j (c.head j))
    rw [htr] at e1
    have : (insPairs ts).length ≤ (insOf M (.next q' w mv)).length := by
      simp [insOf, hins]; omega
    have eL : (records (ts.map (·.1))).length = (s LS).length := by
      rw [hL]; simp [ts, List.map_ofFn]; rfl
    have eR : (records (ts.map (·.2.1))).length = (s RS).length := by
      rw [hR]; simp [ts, List.map_ofFn]; rfl
    simp only [recSize]
    simp (config := {decide := true}) only [update_apply, if_true, if_false]
    omega

end

end Lax119563Proofs.Hierarchy.Universal

end Hierarchy_UnivStep

/-! ### Formerly `Lax119563Proofs.Hierarchy.UnivInit` -/

section Hierarchy_UnivInit

/-!
# The code of a machine and the initialisation of the simulator

The code of `M` is its token stream `R^{k+1} Sep R^k Sep table End`, each token written with
4 bits.  On an input `code M ++ z` the initialisation of the simulator reaches stacks that
represent the initial configuration of `M` on the whole input.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog Function Lax489179.TuringMachine

/-- Four bits of a token. -/
def tokBits (t : Tok) : List Bool :=
  [decide ((t.val - 2) / 8 % 2 = 1), decide ((t.val - 2) / 4 % 2 = 1),
    decide ((t.val - 2) / 2 % 2 = 1), decide ((t.val - 2) % 2 = 1)]

/-- Accumulating one bit. -/
def bstep (acc : ℕ) (b : Bool) : ℕ := 2 * acc + if b then 1 else 0

lemma tokBits_val : ∀ t : Tok, 2 ≤ t.val → (tokBits t).foldl bstep 0 = t.val - 2 := by decide

lemma tokOf_tok : ∀ t : Tok, 2 ≤ t.val → t.val ≤ 13 → tokOf (t.val - 2) = some t := by decide

lemma tokOf_end : tokOf (tEnd.val - 2) = none := by decide

/-- The effect of emitting the token with code `v`. -/
def emit (v : ℕ) (s : Stacks 16 13) : Stacks 16 13 :=
  match tokOf v with
  | some t => update s P (t :: s P)
  | none => update s FLG (0 :: s FLG)

/-- The bits as input symbols. -/
abbrev bitsToks (bs : List Bool) : List Tok := bs.map (bitSym 13)

lemma readBits_runs :
    ∀ (bs : List Bool) (acc : ℕ) (s : Stacks 16 13) (rest : List Tok),
      s IN = bitsToks bs ++ rest →
      (readBits bs.length acc).RunsLe s
        (emit (bs.foldl bstep acc) (update (update s IN rest) Y ((bitsToks bs).reverse ++ s Y)))
        (30 * bs.length + 2)
  | [], acc, s, rest, hs => by
    simp only [List.map_nil, List.nil_append] at hs
    simp only [List.length_nil, List.foldl_nil, List.map_nil, List.reverse_nil, List.nil_append]
    rcases h : tokOf acc with _ | t
    · simp only [readBits, emit, h]
      refine (RunsLe.push _ _ _).of_eq ?_ (by simp)
      funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hs]
    · simp only [readBits, emit, h]
      refine (RunsLe.push _ _ _).of_eq ?_ (by simp)
      funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hs]
  | b :: bs, acc, s, rest, hs => by
    have h1 := moveOne_runs (i := IN) (j := Y) (by decide) (a := bitSym 13 b)
      (l := bitsToks bs ++ rest) (s := s) (by simp [hs])
    set s₁ := update (update s IN (bitsToks bs ++ rest)) Y (bitSym 13 b :: s Y)
    have h2 := readBits_runs bs (bstep acc b) s₁ rest (by simp [s₁])
    have he : emit ((b :: bs).foldl bstep acc)
        (update (update s IN rest) Y ((bitsToks (b :: bs)).reverse ++ s Y)) =
        emit (bs.foldl bstep (bstep acc b))
          (update (update s₁ IN rest) Y ((bitsToks bs).reverse ++ s₁ Y)) := by
      congr 1
      funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, s₁]
    rw [he]
    cases b
    · exact ((h1.seq h2).iteF (by simp [tops, isTop, hs, bitSym])).mono (by simp; omega)
    · exact ((h1.seq h2).iteT (by simp [tops, isTop, hs, bitSym])).mono (by simp; omega)

lemma length_tokBits (t : Tok) : (tokBits t).length = 4 := rfl

/-- Parsing tokens up to the end token. -/
lemma parseLoop_runs (rest : List Tok) :
    ∀ (ts : List Tok) (s : Stacks 16 13), (∀ t ∈ ts, 2 ≤ t.val ∧ t.val ≤ 13) → s FLG = [] →
      s IN = bitsToks ((ts ++ [tEnd]).flatMap tokBits) ++ rest →
      (loop (isEmpty FLG) (readBits 4 0)).RunsLe s
        (update (update (update (update s IN rest) Y
          ((bitsToks ((ts ++ [tEnd]).flatMap tokBits)).reverse ++ s Y)) P (ts.reverse ++ s P))
          FLG [0]) (200 * (ts.length + 1))
  | [], s, _, hF, hs => by
    have h1 := readBits_runs (tokBits tEnd) 0 s rest (by simpa using hs)
    rw [tokBits_val tEnd (by decide)] at h1
    simp only [emit, tokOf_end] at h1
    have h2 := RunsLe.loopF (c := isEmpty FLG) (p := readBits 4 0)
      (s := update (update (update s IN rest) Y ((bitsToks (tokBits tEnd)).reverse ++ s Y)) FLG
        (0 :: update (update s IN rest) Y ((bitsToks (tokBits tEnd)).reverse ++ s Y) FLG))
      (by simp [tops, isEmpty])
    refine (RunsLe.loopT (by simp [tops, isEmpty, hF]) h1 h2).of_eq ?_ (by simp [length_tokBits])
    funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hF]
  | t :: ts, s, hts, hF, hs => by
    have ht := hts t List.mem_cons_self
    have h1 := readBits_runs (tokBits t) 0 s
      (bitsToks ((ts ++ [tEnd]).flatMap tokBits) ++ rest) (by simp [hs])
    rw [tokBits_val t ht.1] at h1
    simp only [emit, tokOf_tok t ht.1 ht.2] at h1
    set s₁ := update (update (update s IN (bitsToks ((ts ++ [tEnd]).flatMap tokBits) ++ rest)) Y
      ((bitsToks (tokBits t)).reverse ++ s Y)) P (t :: s P)
    have h2 := parseLoop_runs rest ts s₁ (fun t h => hts t (List.mem_cons_of_mem _ h))
      (by simp [s₁, hF]) (by simp [s₁])
    refine (RunsLe.loopT (by simp [tops, isEmpty, hF]) h1 h2).of_eq ?_ ?_
    · funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, s₁]
    · simp [length_tokBits]; omega

/-- The value of an input bit as a symbol of the tape. -/
def symOfBit (b : Bool) : ℕ := if b then 2 else 1

lemma inputToRS_runs :
    ∀ (bs : List Bool) (s : Stacks 16 13), s Y = bitsToks bs →
      inputToRS.RunsLe s (update (update s Y []) RS (encL (bs.reverse.map symOfBit) ++ s RS))
        (10 * bs.length + 1)
  | [], s, hs => (RunsLe.loopF (by simp [tops, nonempty, hs])).of_eq
      (by funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hs, encL])
      (by simp)
  | b :: bs, s, hs => by
    set s₁ := update (update s RS (encN (symOfBit b) ++ s RS)) Y (bitsToks bs)
    have hb : (seq (ite (isTop Y tT) (seq (push RS tS) (seq (push RS tU) (push RS tU)))
        (seq (push RS tS) (push RS tU))) (pop Y) : SProg).RunsLe s s₁ 8 := by
      cases b
      · refine ((((RunsLe.push RS tS s).seq (RunsLe.push RS tU _)).iteF
          (by simp [tops, isTop, hs, bitSym])).seq (RunsLe.pop Y _)).of_eq ?_ (by simp)
        funext k; fin_cases k <;>
          simp (config := {decide := true}) [update_apply, s₁, hs, symOfBit, encN]
      · refine ((((RunsLe.push RS tS s).seq ((RunsLe.push RS tU _).seq
          (RunsLe.push RS tU _))).iteT (by simp [tops, isTop, hs, bitSym])).seq
          (RunsLe.pop Y _)).of_eq ?_ (by simp)
        funext k; fin_cases k <;>
          simp (config := {decide := true}) [update_apply, s₁, hs, symOfBit, encN]
    have h2 := inputToRS_runs bs s₁ (by simp [s₁])
    refine (RunsLe.loopT (by simp [tops, nonempty, hs]) hb h2).of_eq ?_ ?_
    · funext k; fin_cases k <;>
        simp (config := {decide := true}) [update_apply, s₁, encL]
    · simp; omega

/-! ## The code of a machine -/

/-- The token stream of the code of `M` (without the end token). -/
noncomputable def codeToks (M : Machine) : List Tok :=
  List.replicate (M.tapes + 1) tR ++ tSep :: (List.replicate M.tapes tR ++ tSep :: table M)

/-- The code of `M` as bits. -/
noncomputable def code (M : Machine) : List Bool := (codeToks M ++ [tEnd]).flatMap tokBits

lemma insOf_tokens {M : Machine} (i : Instruction (M.tapes + 1) (M.symbols + 3) (M.states + 1)) :
    ∀ t ∈ insOf M i, 2 ≤ t.val ∧ t.val ≤ 12 := by
  intro t ht
  cases i with
  | halt b => cases b <;> simp [insOf, haltTok] at ht <;> subst ht <;> decide
  | next q w mv =>
    simp only [insOf, insPart, encN, List.mem_cons, List.mem_append, List.mem_replicate,
      List.mem_flatten, List.mem_ofFn, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | (⟨_, rfl⟩ | rfl) | ⟨l, ⟨j, rfl⟩, h⟩
    · decide
    · decide
    · decide
    · simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at h
      rcases h with (⟨_, rfl⟩ | rfl) | rfl
      · decide
      · decide
      · rcases mv j <;> decide

lemma table_tokens (M : Machine) : ∀ t ∈ table M, 2 ≤ t.val ∧ t.val ≤ 12 := by
  intro t ht
  simp only [table, tableToks, entries, List.flatMap_map, List.mem_flatMap] at ht
  obtain ⟨x, -, ht⟩ := ht
  simp only [entryToks, entryOf, List.mem_append, List.mem_cons, List.mem_reverse,
    List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with (h | rfl | h) | rfl
  · rcases keyToks_tokens _ _ t h with rfl | rfl <;> decide
  · decide
  · exact insOf_tokens _ t h
  · decide

lemma codeToks_tokens (M : Machine) : ∀ t ∈ codeToks M, 2 ≤ t.val ∧ t.val ≤ 13 := by
  intro t ht
  simp only [codeToks, List.mem_append, List.mem_cons, List.mem_replicate] at ht
  rcases ht with ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl | h
  · decide
  · decide
  · decide
  · decide
  · have := table_tokens M t h; omega

lemma length_code (M : Machine) : (code M).length = 4 * ((codeToks M).length + 1) := by
  simp only [code, List.length_flatMap, length_tokBits]
  simp [List.sum_replicate, List.map_const']
  ring

/-! ## Initialisation -/

/-- Stacks in the shape used during the initialisation. -/
def ist (aIN aY aP aLS aRS aTBL aFLG : List Tok) : Stacks 16 13 := fun i =>
  if i = IN then aIN else if i = Y then aY else if i = P then aP else if i = LS then aLS else
  if i = RS then aRS else if i = TBL then aTBL else if i = FLG then aFLG else []

lemma records_replicate_nil (n : ℕ) : records (List.replicate n []) = List.replicate n tR := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, records_cons, ih, List.replicate_succ]; simp [record, encL]

lemma encL_symOfBit_le (y : List Bool) : (encL (y.map symOfBit)).length ≤ 3 * y.length := by
  induction y with
  | nil => simp [encL]
  | cons b y ih =>
    simp only [List.map_cons, encL_cons, List.length_append, length_encN, List.length_cons]
    cases b <;> simp [symOfBit] <;> omega

theorem init_runs (M : Machine) (z : List Bool) :
    ∃ s', init.RunsLe (inputStacks 15 13 (code M ++ z)) s'
        (1000 * ((code M ++ z).length + 1)) ∧
      Rel M (Lax489179.TuringMachine.init M (code M ++ z)) s' ∧
      recSize s' ≤ 5 * ((code M ++ z).length + 1) := by
  set y := code M ++ z with hy
  have hct := codeToks_tokens M
  have hlen := length_code M
  have h0 : inputStacks 15 13 y = ist (bitsToks y) [] [] [] [] [] [] := by
    funext i; fin_cases i <;> simp (config := {decide := true}) [inputStacks, ist]
  rw [h0]
  -- parsing
  have h1 := parseLoop_runs (bitsToks z) (codeToks M) (ist (bitsToks y) [] [] [] [] [] []) hct
    (by simp [ist]) (by simp [ist, y, code])
  have h1' := h1.of_eq (s₂ := ist (bitsToks z) (bitsToks (code M)).reverse (codeToks M).reverse [] [] [] [0])
    (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist, code])
    le_rfl
  have h2 := (moveAll_runs (i := IN) (j := Y) (by decide) (bitsToks z)
    (ist (bitsToks z) (bitsToks (code M)).reverse (codeToks M).reverse [] [] [] [0]) (by simp [ist])).of_eq
    (s₂ := ist [] (bitsToks y).reverse (codeToks M).reverse [] [] [] [0])
    (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist, y]) le_rfl
  have h3 := (RunsLe.pop FLG (ist [] (bitsToks y).reverse (codeToks M).reverse [] [] [] [0])).of_eq
    (s₂ := ist [] (bitsToks y).reverse (codeToks M).reverse [] [] [] [])
    (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist]) le_rfl
  have hparse : parse.RunsLe (ist (bitsToks y) [] [] [] [] [] [])
      (ist [] (bitsToks y).reverse (codeToks M).reverse [] [] [] [])
      (200 * ((codeToks M).length + 1) + (19 * z.length + 1 + 1)) := by
    refine (h1'.seq (h2.seq h3)).mono (by simp)
  -- distributing the code
  have h4 : (moveAll P TBL : SProg).RunsLe (ist [] (bitsToks y).reverse (codeToks M).reverse [] [] [] [])
      (ist [] (bitsToks y).reverse [] [] [] (codeToks M) []) (19 * (codeToks M).length + 1) :=
    (moveAll_runs (by decide) (codeToks M).reverse _ (by simp [ist])).of_eq
      (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist]) (by simp)
  have hsep : tSep ∉ List.replicate (M.tapes + 1) tR := by simp [List.mem_replicate]
  have hsep' : tSep ∉ List.replicate M.tapes tR := by simp [List.mem_replicate]
  have h5 : (moveWhileNot TBL LS tSep : SProg).RunsLe (ist [] (bitsToks y).reverse [] [] [] (codeToks M) [])
      (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR) []
        (tSep :: (List.replicate M.tapes tR ++ tSep :: table M)) []) (19 * (M.tapes + 1) + 1) :=
    (moveWhileNot_runs (by decide) tSep (tSep :: (List.replicate M.tapes tR ++ tSep :: table M))
      (by simp) (List.replicate (M.tapes + 1) tR) _ hsep (by simp [ist, codeToks])).of_eq
      (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist])
      (by simp)
  have h6 : (pop TBL : SProg).RunsLe (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR) []
        (tSep :: (List.replicate M.tapes tR ++ tSep :: table M)) [])
      (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR) []
        (List.replicate M.tapes tR ++ tSep :: table M) []) 1 :=
    (RunsLe.pop _ _).of_eq
      (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist]) le_rfl
  have h7 : (moveWhileNot TBL RS tSep : SProg).RunsLe (ist [] (bitsToks y).reverse []
        (List.replicate (M.tapes + 1) tR) [] (List.replicate M.tapes tR ++ tSep :: table M) [])
      (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR) (List.replicate M.tapes tR)
        (tSep :: table M) []) (19 * M.tapes + 1) :=
    (moveWhileNot_runs (by decide) tSep (tSep :: table M) (by simp) (List.replicate M.tapes tR) _ hsep'
      (by simp [ist])).of_eq
      (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist])
      (by simp)
  have h8 : (pop TBL : SProg).RunsLe (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR)
        (List.replicate M.tapes tR) (tSep :: table M) [])
      (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR) (List.replicate M.tapes tR)
        (table M) []) 1 :=
    (RunsLe.pop _ _).of_eq
      (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist]) le_rfl
  have h9 : (push RS tR : SProg).RunsLe (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR)
        (List.replicate M.tapes tR) (table M) [])
      (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR) (List.replicate (M.tapes + 1) tR)
        (table M) []) 2 :=
    (RunsLe.push _ _ _).of_eq
      (by funext i; fin_cases i <;>
        simp (config := {decide := true}) [update_apply, ist, List.replicate_succ]) le_rfl
  have h10 := inputToRS_runs y.reverse (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR)
    (List.replicate (M.tapes + 1) tR) (table M) []) (by simp [ist, List.map_reverse])
  set sF := ist [] [] [] (List.replicate (M.tapes + 1) tR)
    (encL (y.map symOfBit) ++ List.replicate (M.tapes + 1) tR) (table M) []
  have h10' := h10.of_eq (s₂ := sF)
    (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist, sF]) le_rfl
  have hk : M.tapes + 1 ≤ (codeToks M).length := by simp [codeToks]
  have hcy : 4 * ((codeToks M).length + 1) ≤ y.length := by rw [hy, List.length_append, hlen]; omega
  refine ⟨sF, (hparse.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq h10'))))))).mono ?_,
    ⟨rfl, fun _ => [], fun j => if j = 0 then y.map symOfBit else [], fun j => ?_, ?_, ?_, ?_, ?_,
      ?_⟩, ?_⟩
  · simp only [List.length_reverse]
    have : z.length ≤ y.length := by simp [hy]
    omega
  · by_cases hj : j = 0
    · subst hj
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simp only [Lax489179.TuringMachine.init, true_and, if_true, zero_add]
        rw [if_pos (by omega)]
        simp only [Int.toNat_natCast]
        rcases h : y[i]? with _ | _ | _ <;> simp [List.getD_eq_getElem?_getD, h, symOfBit]
      · simp only [Lax489179.TuringMachine.init]
        rw [if_neg (by omega)]
        simp
    · refine ⟨fun i => ?_, fun i => ?_⟩
      · simp [Lax489179.TuringMachine.init, hj]
      · simp [Lax489179.TuringMachine.init, hj]
  · simp only [sF, ist]
    simp (config := {decide := true}) only [if_true, if_false]
    rw [List.ofFn_const, records_replicate_nil]
  · simp only [sF, ist]
    simp (config := {decide := true}) only [if_true, if_false]
    rw [List.ofFn_succ]
    simp only [if_true, Fin.succ_ne_zero, if_false, records_cons, record]
    rw [List.ofFn_const, records_replicate_nil, List.replicate_succ]
    simp
  · simp [sF, ist, Lax489179.TuringMachine.init]
  · simp [sF, ist]
  · intro i h1 h2 h3 h4
    fin_cases i <;> simp_all (config := {decide := true}) [sF, ist]
  · simp only [recSize, sF, ist]
    simp (config := {decide := true}) only [if_true, if_false]
    have := encL_symOfBit_le y
    simp only [List.length_append, List.length_replicate]
    omega

end Lax119563Proofs.Hierarchy.Universal

end Hierarchy_UnivInit

/-! ### Formerly `Lax119563Proofs.Hierarchy.UnivMain` -/

section Hierarchy_UnivMain

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

end Hierarchy_UnivMain

/-! ### Formerly `Lax119563Proofs.Hierarchy.Coarse` -/

section Hierarchy_Coarse

/-!
# The coarse hierarchy

The diagonal machine runs the universal simulator on its input `y` under a clock of
`|y|^B` steps, `B = 3 b + 3`; the simulator answers the negation of the machine whose code is a
prefix of `y`.  Hence its language is in `DTIME(n^B)` but not in `DTIME(n^b)`.
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime Function

namespace Lax119563Proofs.Hierarchy

open Prog Universal

/-- Stack indices of the clock preparation: scratch stacks after the clock. -/
noncomputable def d3 (k : ℕ) (hk : k < 4 := by omega) : Fin (simMachine.tapes + 1 + 4 + 1) :=
  ⟨simMachine.tapes + 2 + k, by omega⟩

/-- Leave the input in place and put `|y|^B` clock units on the clock stack. -/
noncomputable def clockPrep (B : ℕ) : Prog (simMachine.tapes + 1 + 4 + 1) simMachine.symbols :=
  seq (moveCount 0 (d3 0) (d3 1))
    (seq (moveAll (d3 0) 0) (power (clockIdx simMachine 4) (d3 1) (d3 2) (d3 3) B))

/-- Stacks in the shape used by `clockPrep`. -/
noncomputable def cst (a0 aA aN aK : List (Fin (simMachine.symbols + 2))) :
    Stacks (simMachine.tapes + 1 + 4 + 1) simMachine.symbols := fun i =>
  if i.val = 0 then a0 else if i.val = simMachine.tapes + 2 then aA else
  if i.val = simMachine.tapes + 3 then aN else if i.val = simMachine.tapes + 1 then aK else []

/-- Prove equalities between `cst` stacks and their updates. -/
macro "cst_eq" : tactic =>
  `(tactic| (funext i; simp only [cst, update_apply, Fin.ext_iff, Fin.val_zero, d3, clockIdx]; split_ifs <;> first | omega | rfl | simp_all))

lemma clockPrep_runs (B : ℕ) (hB : 1 ≤ B) (y : List Bool) :
    ∃ s', (clockPrep B).RunsLe (inputStacks _ _ y) s'
        ((2 * simMachine.symbols + 20 + B * (4 * simMachine.symbols + 40)) * (y.length + 1) ^ B
          + 5) ∧
      HandsOver simMachine s' y ∧ (s' (clockIdx simMachine 4)).length = y.length ^ B := by
  have ne : ∀ a b : Fin (simMachine.tapes + 1 + 4 + 1), a.val ≠ b.val → a ≠ b :=
    fun a b h => Fin.ne_of_val_ne h
  set m := simMachine.symbols
  set yb := y.map (bitSym m)
  have hs0 : inputStacks (simMachine.tapes + 1 + 4) m y = cst yb [] [] [] := by
    funext i
    simp only [inputStacks, cst, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> first | omega | rfl
  rw [hs0]
  have h1 : (moveCount 0 (d3 0) (d3 1) : Prog _ m).RunsLe (cst yb [] [] [])
      (cst [] yb.reverse (unary m y.length) []) ((m + 8) * y.length + 1) :=
    (moveCount_runs (ne _ _ (by simp [d3])) (ne _ _ (by simp [d3])) (ne _ _ (by simp [d3])) yb _
      (by simp [cst])).of_eq (by simp only [yb, List.length_map]; cst_eq) (by simp [yb])
  have h2 : (moveAll (d3 0) 0 : Prog _ m).RunsLe (cst [] yb.reverse (unary m y.length) [])
      (cst yb [] (unary m y.length) []) ((m + 6) * y.length + 1) :=
    (moveAll_runs (ne _ _ (by simp [d3])) yb.reverse _ (by simp [cst, d3])).of_eq
      (by simp only [List.reverse_reverse]; cst_eq) (by simp [yb])
  have h3 := power_runs (p := clockIdx simMachine 4) (n := d3 1) (q := d3 2) (h := d3 3)
    (b := y.length) (ne _ _ (by simp [d3, clockIdx])) (ne _ _ (by simp [d3, clockIdx]))
    (ne _ _ (by simp [d3, clockIdx])) (ne _ _ (by simp [d3])) (ne _ _ (by simp [d3]))
    (ne _ _ (by simp [d3])) B (s := cst yb [] (unary m y.length) [])
    (by simp [cst, clockIdx]) (by simp [cst, d3]) (by simp [cst, d3]) (by simp [cst, d3])
  refine ⟨_, (h1.seq (h2.seq h3)).mono ?_, fun i => ⟨fun hi => ?_, fun hi1 hi2 => ?_⟩, ?_⟩
  · have hP : y.length + 1 ≤ (y.length + 1) ^ B := Nat.le_self_pow (by omega) _
    nlinarith
  · simp only [update_apply, Fin.ext_iff, clockIdx, cst]
    split_ifs <;> first | omega | rfl
  · simp only [update_apply, Fin.ext_iff, clockIdx, cst]
    split_ifs <;> first | omega | rfl
  · simp

/-- The language of the diagonal machine for the exponent `b`. -/
noncomputable def diagLang (B : ℕ) : Set (List Bool) :=
  {y | (runOn simMachine y (y.length ^ B)).answer = some true}

/-- The diagonal machine. -/
noncomputable def diagMachine (B : ℕ) : Machine := thenClocked simMachine 4 (clockPrep B)

lemma diagLang_dt (B : ℕ) (hB : 1 ≤ B) : DT (diagLang B) (B : ℝ) := by
  set K₀ := 2 * simMachine.symbols + 20 + B * (4 * simMachine.symbols + 40)
  set K := K₀ + 7
  refine ⟨diagMachine B, thenClocked_deterministic _ _ _, K * 2 ^ B, fun y => ?_⟩
  obtain ⟨s', ⟨t, ht, hr⟩, hH, hK⟩ := clockPrep_runs B hB y
  have hans := thenClocked_answer hr hH hK
  have hdec : Lax119563.DeterministicTime.DecidesExactlyWithin (diagMachine B) y (y ∈ diagLang B)
      (t + y.length ^ B + 1) := by
    refine ⟨_, hans, ?_⟩
    simp only [diagLang, Set.mem_ofPred_eq]
    rcases (runOn simMachine y (y.length ^ B)).answer with _ | _ | _ <;> simp
  refine decidesWithin_mono hdec ?_
  apply Nat.le_floor
  have h1 := succ_pow_le y.length B
  have h2 : y.length ^ B ≤ (y.length + 1) ^ B := Nat.pow_le_pow_left (by omega) B
  have h3 : 1 ≤ (y.length + 1) ^ B := Nat.one_le_pow _ _ (by omega)
  have h4 : t + y.length ^ B + 1 ≤ K * 2 ^ B * y.length ^ B + K * 2 ^ B := by
    calc t + y.length ^ B + 1 ≤ K * (y.length + 1) ^ B := by
          have e : K * (y.length + 1) ^ B = K₀ * (y.length + 1) ^ B + 7 * (y.length + 1) ^ B := by
            simp only [K]; ring
          have ht' : t ≤ K₀ * (y.length + 1) ^ B + 5 := ht
          omega
      _ ≤ K * (2 ^ B * (y.length ^ B + 1)) := Nat.mul_le_mul_left _ h1
      _ = _ := by ring
  beta_reduce
  rw [Real.rpow_natCast]
  exact_mod_cast h4

/-- The running time of the simulator is eventually below `n^{3 b + 3}`. -/
lemma simTime_le (C Tb b : ℕ) : ∃ N0, ∀ n ≥ N0, ∀ T ≤ C * n ^ b + C,
    simTime n Tb T ≤ n ^ (3 * b + 3) := by
  set A := 2 * (C + 1)
  set K₁ := 12 + 2 * A * Tb
  set K₂ := 2003 + 12001 * A * K₁ ^ 2
  refine ⟨K₂ + 1, fun n hn T hT => ?_⟩
  have hn1 : 1 ≤ n := by omega
  set X := n ^ b
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hTA : T ≤ A * X := by
    have e1 : C ≤ C * X := Nat.le_mul_of_pos_right _ hX
    have e2 : A * X = 2 * (C * X) + 2 * X := by simp only [A]; ring
    have e3 : C * n ^ b = C * X := rfl
    omega
  have hnX : 1 ≤ n * X := Nat.mul_le_mul hn1 hX
  have hin : 5 * (n + 1) + (T + 1) * Tb + 1 ≤ K₁ * (n * X) := by
    have e1 : (T + 1) * Tb ≤ (A * X + 1) * Tb := Nat.mul_le_mul_right _ (by omega)
    have e2 : X ≤ n * X := Nat.le_mul_of_pos_left _ (by omega)
    have e3 : n ≤ n * X := Nat.le_mul_of_pos_right _ (by omega)
    have e4 : A * X * Tb ≤ A * Tb * (n * X) := by
      have := Nat.mul_le_mul_left (A * Tb) e2
      calc A * X * Tb = A * Tb * X := by ring
        _ ≤ _ := this
    have hA : 2 ≤ A := by simp only [A]; omega
    have e5 : Tb ≤ A * Tb * (n * X) := by
      calc Tb = 1 * Tb * 1 := by ring
        _ ≤ A * Tb * (n * X) := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) hnX
    have e6 : (A * X + 1) * Tb = A * X * Tb + Tb := by ring
    have e7 : K₁ * (n * X) = 12 * (n * X) + 2 * (A * Tb * (n * X)) := by simp only [K₁]; ring
    omega
  have hsc : stepCost (5 * (n + 1) + (T + 1) * Tb) ≤ 12000 * K₁ ^ 2 * (n * X) ^ 2 := by
    unfold stepCost
    calc 3000 * (5 * (n + 1) + (T + 1) * Tb + 1) ^ 2 ≤ 3000 * (K₁ * (n * X) + 1) ^ 2 := by
          gcongr; omega
      _ ≤ 3000 * (2 * K₁ * (n * X)) ^ 2 := by
          gcongr; have : 1 ≤ K₁ := by simp only [K₁]; omega
          nlinarith
      _ = 12000 * K₁ ^ 2 * (n * X) ^ 2 := by ring
  have hmain : T * (stepCost (5 * (n + 1) + (T + 1) * Tb) + 1) ≤ 12001 * A * K₁ ^ 2 * n ^ 2 * X ^ 3 := by
    have h1 : stepCost (5 * (n + 1) + (T + 1) * Tb) + 1 ≤ 12001 * K₁ ^ 2 * (n * X) ^ 2 := by
      have : 1 ≤ K₁ ^ 2 * (n * X) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      rw [mul_assoc] at hsc ⊢
      omega
    calc T * (stepCost (5 * (n + 1) + (T + 1) * Tb) + 1)
        ≤ (A * X) * (12001 * K₁ ^ 2 * (n * X) ^ 2) := Nat.mul_le_mul hTA h1
      _ = 12001 * A * K₁ ^ 2 * n ^ 2 * X ^ 3 := by ring
  have hpow : n ^ (3 * b + 3) = n * (n ^ 2 * X ^ 3) := by
    simp only [X]; ring
  have hnX3 : 1 ≤ n ^ 2 * X ^ 3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hfin : simTime n Tb T ≤ K₂ * (n ^ 2 * X ^ 3) := by
    simp only [simTime, K₂]
    have e : 1000 * (n + 1) ≤ 2000 * (n ^ 2 * X ^ 3) := by
      have : n ≤ n ^ 2 * X ^ 3 := by
        calc n = n ^ 1 * 1 := by ring
          _ ≤ n ^ 2 * X ^ 3 := Nat.mul_le_mul (Nat.pow_le_pow_right hn1 (by omega))
              (Nat.one_le_pow _ _ hX)
      omega
    have e' : 12001 * A * K₁ ^ 2 * n ^ 2 * X ^ 3 = 12001 * A * K₁ ^ 2 * (n ^ 2 * X ^ 3) := by ring
    nlinarith
  rw [hpow]
  calc simTime n Tb T ≤ K₂ * (n ^ 2 * X ^ 3) := hfin
    _ ≤ n * (n ^ 2 * X ^ 3) := Nat.mul_le_mul_right _ (by omega)

lemma diagLang_not_dt (b : ℕ) : ¬ DT (diagLang (3 * b + 3)) (b : ℝ) := by
  rintro ⟨M, -, C, hC⟩
  obtain ⟨N0, hN0⟩ := simTime_le C (table M).length b
  set y := code M ++ List.replicate N0 false
  have hn : N0 ≤ y.length := by simp [y]
  obtain ⟨β, hβ, hiff⟩ := hC y
  set T := ⌊(C : ℝ) * (fun n : ℕ => (n : ℝ) ^ (b : ℝ)) y.length + C⌋₊
  have hT : T ≤ C * y.length ^ b + C := by
    have e : (C : ℝ) * (y.length : ℝ) ^ (b : ℝ) + C = ((C * y.length ^ b + C : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; push_cast; ring
    simp only [T]
    rw [e, Nat.floor_natCast]
  have hsim := simMachine_answer (z := List.replicate N0 false) hβ
  have hle := hN0 y.length hn T hT
  have hB := drun_answer_mono hsim hle
  have hmem : y ∈ diagLang (3 * b + 3) ↔ (!β) = true := by
    simp only [diagLang, Set.mem_ofPred_eq, runOn_eq_drun] at hB ⊢
    rw [hB]; simp
  cases β <;> simp_all

/-- The coarse hierarchy. -/
theorem coarseHierarchy : CoarseHierarchy := fun b =>
  ⟨3 * b + 3, diagLang (3 * b + 3), diagLang_dt _ (by omega), diagLang_not_dt b⟩

end Lax119563Proofs.Hierarchy

end Hierarchy_Coarse
