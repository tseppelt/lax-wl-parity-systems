import Lax119563Proofs.Hierarchy.Lax

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

theorem Runs.det {p : Prog K m} {s s₁ s₂ : Stacks K m} {t₁ t₂ : ℕ} (h₁ : p.Runs s s₁ t₁)
    (h₂ : p.Runs s s₂ t₂) : s₁ = s₂ ∧ t₁ = t₂ := by
  induction h₁ generalizing s₂ t₂ with
  | skip => cases h₂; simp
  | push => cases h₂; simp
  | pop => cases h₂; simp
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h h' =>
      obtain ⟨rfl, rfl⟩ := ih₁ h
      obtain ⟨rfl, rfl⟩ := ih₂ h'
      simp
  | iteT hc _ ih =>
    cases h₂ with
    | iteT _ h => obtain ⟨rfl, rfl⟩ := ih h; simp
    | iteF hc' _ => simp_all
  | iteF hc _ ih =>
    cases h₂ with
    | iteT hc' _ => simp_all
    | iteF _ h => obtain ⟨rfl, rfl⟩ := ih h; simp
  | loopF hc =>
    cases h₂ with
    | loopF _ => simp
    | loopT hc' _ _ => simp_all
  | loopT hc _ _ ih₁ ih₂ =>
    cases h₂ with
    | loopF hc' => simp_all
    | loopT _ h h' =>
      obtain ⟨rfl, rfl⟩ := ih₁ h
      obtain ⟨rfl, rfl⟩ := ih₂ h'
      simp

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
