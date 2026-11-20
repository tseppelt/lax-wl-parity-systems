import Lax119563Proofs.Compiler.CMachine
import Lax119563Proofs.Compiler.CArith
import Lax119563Proofs.Compiler.CParse
import Lax119563Proofs.Compiler.CFrame
import Lax119563Proofs.Main.Runs

/-!
# Simulating a machine by a structured statement: definitions

A deterministic machine `M` of `Lax489179.TuringMachine` is simulated step by step by a
structured statement (`Compiler.CStm`). Tape `j` of `M` is kept in two number stacks
`L j` (the cells left of the head, nearest first) and `R j` (the cells from the head on);
symbols are stored by their index, and popping an empty stack gives `0`, the blank. The
control state is kept in a register. A step pops the scanned symbols, looks up the
transition in a chain of conditionals over all pairs (state, scanned symbols), and applies
it; a step counter (`clk`) is incremented in every iteration.

Registers and stacks of the simulator are given by embeddings `ρ : Rg n ↪ Fin R` and
`κ : Sk n ↪ Fin Q` (`n` the number of tapes), so that the simulator can be placed into
larger statements.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax489179.TuringMachine (Machine Config Instruction Move)

namespace Lax119563Proofs.Computability

/-- Registers of the simulator of a machine with `n` tapes. -/
inductive Rg (n : ℕ) : Type
  | inp | out | clk | st | halt | tmp | flg | pw
  | sc (j : Fin n)
  deriving DecidableEq, Fintype

/-- Stacks of the simulator of a machine with `n` tapes. -/
inductive Sk (n : ℕ) : Type
  | aux
  | L (j : Fin n)
  | R (j : Fin n)
  deriving DecidableEq, Fintype

/-! ## Expressions -/

/-- `[env r ≠ v]`. -/
def neqE {R : ℕ} (r : Fin R) (v : ℕ) : Ex R := .add (.lt (.var r) (.const v)) (.lt (.const v) (.var r))

/-- The sum of a list of expressions. -/
def sumE {R : ℕ} : List (Ex R) → Ex R
  | [] => .const 0
  | e :: es => .add e (sumE es)

/-- A list of statements in sequence. -/
def seqL {R Q : ℕ} : List (CStm R Q) → CStm R Q
  | [] => .skip
  | c :: cs => .seq c (seqL cs)

section Defs

variable {R Q : ℕ} (M : Machine)

/-- Lookup keys: a control state and the scanned symbols. -/
abbrev Key (M : Machine) := Fin (M.states + 1) × (Fin (M.tapes + 1) → Fin (M.symbols + 3))

/-- All keys. -/
noncomputable def keys : List (Key M) := (Finset.univ : Finset (Key M)).toList

variable (ρ : Rg (M.tapes + 1) ↪ Fin R) (κ : Sk (M.tapes + 1) ↪ Fin Q)

/-- The registers hold the key `p`. -/
def matchE (p : Key M) : Ex R :=
  .lt (sumE (neqE (ρ .st) p.1.val ::
    (List.finRange (M.tapes + 1)).map fun j => neqE (ρ (.sc j)) (p.2 j).val)) (.const 1)

/-- Write `a` on tape `j` and move by `m` (the scanned cell has been popped already). -/
def opT (j : Fin (M.tapes + 1)) (a : ℕ) : Move → CStm R Q
  | .stay => .push (κ (.R j)) (.const a)
  | .right => .push (κ (.L j)) (.const a)
  | .left => .seq (.pop (κ (.L j)) (ρ .tmp))
      (.seq (.push (κ (.R j)) (.const a)) (.push (κ (.R j)) (.var (ρ .tmp))))

/-- Pop the scanned symbol of tape `j`. -/
def popT (j : Fin (M.tapes + 1)) : CStm R Q := .pop (κ (.R j)) (ρ (.sc j))

/-- Push the scanned symbol of tape `j` back. -/
def pushT (j : Fin (M.tapes + 1)) : CStm R Q := .push (κ (.R j)) (.var (ρ (.sc j)))

/-- The statement for one transition. -/
def leaf (p : Key M) : CStm R Q :=
  match M.transition p.1 p.2 false with
  | .halt _ => .seq (.set (ρ .halt) (.const 1))
      (seqL ((List.finRange (M.tapes + 1)).map (pushT M ρ κ)))
  | .next q w m => .seq (.set (ρ .st) (.const q.val))
      (seqL ((List.finRange (M.tapes + 1)).map fun j => opT M ρ κ j (w j).val (m j)))

/-- The lookup chain. -/
def chain (l : List (Key M)) : CStm R Q :=
  l.foldr (fun p c => .ite (matchE M ρ p) (leaf M ρ κ p) c) .skip

/-- One iteration of the simulation loop. -/
noncomputable def body : CStm R Q :=
  .seq (seqL ((List.finRange (M.tapes + 1)).map (popT M ρ κ)))
    (.seq (chain M ρ κ (keys M)) (.set (ρ .clk) (.add (.var (ρ .clk)) (.const 1))))

/-- The loop condition: not halted. -/
def condE : Ex R := .lt (.var (ρ .halt)) (.const 1)

/-- The simulation loop, started in state `0` with the counter at `0`. -/
noncomputable def core : CStm R Q :=
  .seq (.set (ρ .halt) (.const 0)) (.seq (.set (ρ .st) (.const 0))
    (.seq (.set (ρ .clk) (.const 0)) (.loop (condE M ρ) (body M ρ κ))))

end Defs

/-! ## Evaluation of the expressions -/

section Eval

variable {R : ℕ}

lemma neqE_eval (env : Fin R → ℕ) (r : Fin R) (v : ℕ) :
    (neqE r v).eval env = if env r = v then 0 else 1 := by
  simp only [neqE, Ex.eval]
  by_cases h1 : env r < v <;> by_cases h2 : v < env r <;> by_cases h3 : env r = v <;>
    simp [h1, h2, h3] <;> omega

lemma neqE_size (r : Fin R) (v : ℕ) : (neqE r v).size = 7 := rfl

lemma sumE_eval (env : Fin R → ℕ) (es : List (Ex R)) :
    (sumE es).eval env = (es.map (Ex.eval env)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [sumE, Ex.eval, ih]

lemma sumE_size (es : List (Ex R)) : (sumE es).size = (es.map Ex.size).sum + es.length + 1 := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [sumE, Ex.size, ih]; ring

lemma sumE_fits {w : ℕ} (env : Fin R → ℕ) (es : List (Ex R)) (h0 : 0 < 2 ^ w)
    (hf : ∀ e ∈ es, e.Fits w env) (hs : (es.map (Ex.eval env)).sum < 2 ^ w) :
    (sumE es).Fits w env := by
  induction es with
  | nil => simp only [sumE, Ex.Fits]; exact h0
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons] at hs
    refine ⟨hf e (by simp), ih (fun e' he' => hf e' (by simp [he'])) (by omega), ?_⟩
    rw [sumE_eval]; exact hs

lemma neqE_le (env : Fin R → ℕ) (r : Fin R) (v : ℕ) : (neqE r v).eval env ≤ 1 := by
  rw [neqE_eval]; split_ifs <;> omega

lemma neqE_fits {w : ℕ} (env : Fin R → ℕ) (r : Fin R) (v : ℕ) (hr : env r < 2 ^ w)
    (hv : v < 2 ^ w) (h2 : 2 ≤ 2 ^ w) : (neqE r v).Fits w env := by
  have h1 := neqE_le env r v
  simp only [neqE, Ex.Fits, Ex.eval] at h1 ⊢
  exact ⟨⟨hr, hv⟩, ⟨hv, hr⟩, by omega⟩

lemma sum_map_eq_zero_iff {α : Type} (l : List α) (f : α → ℕ) :
    (l.map f).sum = 0 ↔ ∀ a ∈ l, f a = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma sum_map_le_length {α : Type} (l : List α) (f : α → ℕ) (h : ∀ a ∈ l, f a ≤ 1) :
    (l.map f).sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a (by simp)
    have := ih (fun b hb => h b (by simp [hb]))
    omega

end Eval

section MatchEval

variable {R Q : ℕ} (M : Machine) (ρ : Rg (M.tapes + 1) ↪ Fin R)

lemma matchE_eval (env : Fin R → ℕ) (p : Key M) :
    (matchE M ρ p).eval env =
      if env (ρ .st) = p.1.val ∧ ∀ j, env (ρ (.sc j)) = (p.2 j).val then 1 else 0 := by
  simp only [matchE, Ex.eval, sumE_eval]
  have key : ((neqE (ρ .st) p.1.val :: (List.finRange (M.tapes + 1)).map fun j =>
      neqE (ρ (.sc j)) (p.2 j).val).map (Ex.eval env)).sum = 0 ↔
      env (ρ .st) = p.1.val ∧ ∀ j, env (ρ (.sc j)) = (p.2 j).val := by
    rw [sum_map_eq_zero_iff]
    simp only [List.mem_cons, List.mem_map, List.mem_finRange, true_and]
    constructor
    · intro h
      refine ⟨?_, fun j => ?_⟩
      · have := h _ (Or.inl rfl); rw [neqE_eval] at this; split_ifs at this with hh
        · exact hh
      · have := h _ (Or.inr ⟨j, rfl⟩); rw [neqE_eval] at this; split_ifs at this with hh
        · exact hh
    · rintro ⟨h1, h2⟩ e (rfl | ⟨j, rfl⟩)
      · rw [neqE_eval, if_pos h1]
      · rw [neqE_eval, if_pos (h2 j)]
  by_cases h : env (ρ .st) = p.1.val ∧ ∀ j, env (ρ (.sc j)) = (p.2 j).val
  · rw [if_pos h, if_pos (by rw [key.mpr h]; omega)]
  · rw [if_neg h, if_neg (by intro hlt; exact h (key.mp (by omega)))]

lemma matchE_size (p : Key M) : (matchE M ρ p).size = 8 * (M.tapes + 1) + 11 := by
  simp only [matchE, Ex.size, sumE_size, List.map_cons, List.map_map, List.sum_cons,
    List.length_cons, List.length_map, List.length_finRange]
  have : ((List.finRange (M.tapes + 1)).map (Ex.size ∘ fun j => neqE (ρ (.sc j)) (p.2 j).val)).sum
      = 7 * (M.tapes + 1) := by
    simp [Function.comp_def, neqE_size, List.sum_replicate, mul_comm]
  rw [this, neqE_size]; ring

/-- A bound for all small constants of the simulator. -/
def simB (M : Machine) : ℕ := M.states + M.symbols + M.tapes + 8

lemma matchE_fits {w : ℕ} (env : Fin R → ℕ) (p : Key M) (hB : simB M ≤ 2 ^ w)
    (hst : env (ρ .st) < 2 ^ w) (hsc : ∀ j, env (ρ (.sc j)) < 2 ^ w) :
    (matchE M ρ p).Fits w env := by
  have h2 : 2 ≤ 2 ^ w := by unfold simB at hB; omega
  have hp1 : p.1.val < 2 ^ w := by have := p.1.isLt; unfold simB at hB; omega
  have hp2 : ∀ j, (p.2 j).val < 2 ^ w := fun j => by
    have := (p.2 j).isLt; unfold simB at hB; omega
  have hsum : ((neqE (ρ .st) p.1.val :: (List.finRange (M.tapes + 1)).map fun j =>
      neqE (ρ (.sc j)) (p.2 j).val).map (Ex.eval env)).sum < 2 ^ w := by
    refine lt_of_le_of_lt (sum_map_le_length _ _ ?_) ?_
    · intro e he
      simp only [List.mem_cons, List.mem_map, List.mem_finRange, true_and] at he
      rcases he with rfl | ⟨j, rfl⟩ <;> exact neqE_le _ _ _
    · simp only [List.length_cons, List.length_map, List.length_finRange]
      unfold simB at hB; omega
  refine ⟨sumE_fits env _ (by omega) ?_ hsum, by simp only [Ex.Fits]; omega⟩
  intro e he
  simp only [List.mem_cons, List.mem_map, List.mem_finRange, true_and] at he
  rcases he with rfl | ⟨j, rfl⟩
  · exact neqE_fits env _ _ hst hp1 h2
  · exact neqE_fits env _ _ (hsc j) (hp2 j) h2

end MatchEval

end Lax119563Proofs.Computability
