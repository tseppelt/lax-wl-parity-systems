import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Lax119563.DeterministicTime
import Lax119563Proofs.Machines.Basic

/-!
# Compiling structured machines to `Lax489179.TuringMachine.Machine`

A `TM (k+1) Γ` over an alphabet with a designated blank and two bit symbols is compiled
to a machine of the archive model by enumerating states (initial state first) and symbols
(blank, `false`, `true` first). A run of `t` transitions followed by halting becomes a run of
`t + 1` steps. The compiled machine is deterministic by construction.

Main results: `TM.computesWithin` and `TM.decidesWithin`, which turn a `RunsWithin`
specification on the input tapes `inputTapes k x` into `ComputesWithin` and `DecidesWithin`
for the compiled machine.
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
  refine ⟨by simp [hrun], ?_⟩
  rw [hrun, init_eq_toConfig]
  funext z
  show symEquiv Γ ((T' 0).cells z) = symEquiv Γ ((inputTapes k y 0).cells z)
  rw [hy]
  simp [inputTapes]

/-- **Deciding.** If `M` halts within `t` transitions on the input tapes of `x` and the answer
assigned to every halting situation is correct, the compiled machine decides `P`. -/
theorem decidesWithin {x : List Bool} {t : ℕ} {T' : Tapes (k + 1) Γ} {P : Prop}
    (h : M.RunsWithin (inputTapes k x) t T')
    (hans : ∀ q, M.δ q (readAll T') = none → (ans q (readAll T') = true ↔ P)) :
    Lax119563.DeterministicTime.DecidesWithin (M.compileWith ans) x P (t + 1) := by
  obtain ⟨q', hq', hrun⟩ := M.runOn_compileWith ans h
  exact ⟨_, by rw [hrun], hans q' hq'⟩

end TM

end Compile

end Lax119563Proofs.Machines
