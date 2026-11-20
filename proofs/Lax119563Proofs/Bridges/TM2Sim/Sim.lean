import Lax119563Proofs.Bridges.TM2Sim.TapeRep
import Lax119563Proofs.Main.Runs

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
