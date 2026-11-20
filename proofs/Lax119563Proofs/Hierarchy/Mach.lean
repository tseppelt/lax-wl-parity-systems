import Lax119563Proofs.Hierarchy.Run

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
