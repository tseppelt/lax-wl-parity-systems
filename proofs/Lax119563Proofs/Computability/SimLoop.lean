import Lax119563Proofs.Computability.SimStep

/-!
# Simulating a machine: the loop

`haltTime M u` is the number of steps after which `M` halts on `u` (the least `t` with
`(runOn M u t).answer.isSome`, if any). Started with input `u` on the stack of tape `0`
(and the other tape stacks empty), the simulation loop `core` ends after `haltTime M u`
iterations, representing the halted configuration and with the counter `clk` at
`haltTime M u` (`core_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Config Instruction Move)

namespace Lax119563Proofs.Computability

open CStm

/-! ## Halting time -/

open Classical in
/-- The number of steps after which `M` halts on `u` (`0` if it does not halt). -/
noncomputable def haltTime (M : Machine) (u : List Bool) : ℕ :=
  if h : ∃ t, (runOn M u t).answer.isSome then Nat.find h else 0

section Halt

variable {M : Machine} {u : List Bool}

lemma haltTime_spec (h : ∃ t, (runOn M u t).answer.isSome) :
    (runOn M u (haltTime M u)).answer.isSome := by
  classical
  rw [haltTime, dif_pos h]; exact Nat.find_spec h

lemma haltTime_le {t : ℕ} (h : (runOn M u t).answer.isSome) : haltTime M u ≤ t := by
  classical
  rw [haltTime, dif_pos ⟨t, h⟩]; exact Nat.find_min' _ h

lemma haltTime_min (h : ∃ t, (runOn M u t).answer.isSome) {t : ℕ} (ht : t < haltTime M u) :
    (runOn M u t).answer = none := by
  classical
  rw [haltTime, dif_pos h] at ht
  have := Nat.find_min h ht
  simpa using this

/-- A machine computing `y` from `u` does so within `haltTime M u` steps. -/
lemma ComputesWithin.haltTime {y : List Bool} {t : ℕ} (h : ComputesWithin M u y t) :
    ComputesWithin M u y (haltTime M u) ∧ haltTime M u ≤ t := by
  have hle := haltTime_le h.1
  have e := Main.runOn_eq_of_le M u hle (haltTime_spec ⟨t, h.1⟩)
  refine ⟨?_, hle⟩
  unfold ComputesWithin HaltsWithin at h ⊢
  rw [← e]; exact h

end Halt

/-! ## The loop -/

/-- The stack symbol of an input bit. -/
def symOf (b : Bool) : ℕ := if b then 2 else 1

variable {R Q : ℕ} {x : List Bool} {w : ℕ} {M : Machine}
variable (ρ : Rg (M.tapes + 1) ↪ Fin R) (κ : Sk (M.tapes + 1) ↪ Fin Q)

variable (M) in
/-- The cost of the simulation loop for `s` steps. -/
noncomputable def coreCost (w s : ℕ) : ℕ := (s + 1) * (bodyCost M w + 10 * Ex.nodeCost w)

lemma repT_init (u : List Bool) (j : Fin (M.tapes + 1)) :
    RepT M (Lax489179.TuringMachine.init M u) j [] (if j = 0 then u.map symOf else []) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · by_cases hj : j = 0
    · subst hj
      simp only [Lax489179.TuringMachine.init, zero_add, if_true]
      rw [if_pos ⟨trivial, by positivity⟩]
      simp only [Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_map]
      rcases u[i]? with _ | _ | _ <;> simp [symOf]
    · simp [Lax489179.TuringMachine.init, hj]
  · simp only [Lax489179.TuringMachine.init]
    rw [if_neg (by omega)]; simp

theorem core_good (hB : simB M ≤ 2 ^ w) (u : List Bool) (st : NSt R Q)
    (hL : ∀ j, st.stk (κ (.L j)) = [])
    (hR : ∀ j, st.stk (κ (.R j)) = if j = 0 then u.map symOf else [])
    (hh : ∃ t, (runOn M u t).answer.isSome) (hs : haltTime M u < 2 ^ w) :
    Good x w (core M ρ κ) st (exec x (core M ρ κ) st) (coreCost M w (haltTime M u)) ∧
      Inv ρ κ (exec x (core M ρ κ) st) (runOn M u (haltTime M u)) (haltTime M u) u.length 1 := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h2 : 2 ≤ 2 ^ w := by unfold simB at hB; omega
  set s := haltTime M u with hsdef
  set S0 := ((st.set (ρ .halt) 0).set (ρ .st) 0).set (ρ .clk) 0 with hS0
  have I0 : Inv ρ κ S0 (Lax489179.TuringMachine.init M u) 0 u.length 0 := by
    refine ⟨by simp [hS0, Lax489179.TuringMachine.init], by simp [hS0], by simp [hS0],
      fun j => ?_, fun j => ?_⟩
    · simp only [hS0, NSt.set_stk, hL, hR]; exact repT_init u j
    · simp only [hS0, NSt.set_stk, hL, hR]; split_ifs <;> simp
  set S : ℕ → NSt R Q := fun j => iter x (body M ρ κ) S0 j with hS
  have hsucc : ∀ j, S (j + 1) = exec x (body M ρ κ) (S j) := fun j => iter_succ _ _ _
  have hI : ∀ j ≤ s, Inv ρ κ (S j) (runOn M u j) j u.length (if j = s then 1 else 0) ∧
      (j < s → Good x w (body M ρ κ) (S j) (S (j + 1)) (bodyCost M w)) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hs0 : s ≠ 0 := by
        intro h0
        have := haltTime_spec hh
        rw [← hsdef, h0] at this
        simp [runOn, Lax489179.TuringMachine.run, Lax489179.TuringMachine.init] at this
      have e0 : (if (0 : ℕ) = s then 1 else 0) = 0 := if_neg (Ne.symm hs0)
      rw [e0]
      refine ⟨I0, fun _ => ?_⟩
      have := iter_step ρ κ (x := x) hB I0
        (by simp [Lax489179.TuringMachine.init]) (by omega)
      rw [hsucc]; exact this.1
    | succ j ih =>
      intro hj
      obtain ⟨Ij, -⟩ := ih (by omega)
      have hjs : j ≠ s := by omega
      rw [if_neg hjs] at Ij
      have hc := haltTime_min hh (show j < s by omega)
      have := iter_step ρ κ (x := x) hB Ij hc (by omega)
      rw [← Main.runOn_succ] at this
      have hans : (if (runOn M u (j + 1)).answer.isSome then 1 else 0) =
          (if j + 1 = s then 1 else 0) := by
        by_cases hjs' : j + 1 = s
        · rw [if_pos hjs', if_pos (by rw [hjs']; exact haltTime_spec hh)]
        · rw [if_neg hjs', haltTime_min hh (show j + 1 < s by omega)]; rfl
      rw [hans, ← hsucc] at this
      refine ⟨this.2, fun hj' => ?_⟩
      have := iter_step ρ κ (x := x) hB (by simpa [show j + 1 ≠ s by omega] using this.2)
        (haltTime_min hh hj') (by omega)
      rw [hsucc (j + 1)]; exact this.1
  have hloop := Good.loop (x := x) (w := w) (e := condE M ρ) (body := body M ρ κ) s S
    (fun _ => bodyCost M w)
    (fun j hj => by
      have := (hI j hj.le).1.2.1
      rw [if_neg (by omega)] at this
      simp [condE, Ex.eval, this])
    (by
      have := (hI s le_rfl).1.2.1
      rw [if_pos rfl] at this
      simp [condE, Ex.eval, this])
    (fun j hj => by
      have := (hI j hj).1.2.1
      simp only [condE, Ex.Fits, this]
      split_ifs <;> omega)
    (fun j hj => (hI j hj.le).2 hj)
  have gc : Good x w (core M ρ κ) st (S s) _ :=
    (Good.set (by simp [Ex.Fits])).seq ((Good.set (by simp [Ex.Fits])).seq
      ((Good.set (by simp [Ex.Fits])).seq hloop))
  refine ⟨?_, ?_⟩
  · rw [gc.2.1]
    refine gc.mono ?_
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, condCost, condE, Ex.size,
      coreCost]
    nlinarith
  · rw [gc.2.1]
    simpa using (hI s le_rfl).1

end Lax119563Proofs.Computability
