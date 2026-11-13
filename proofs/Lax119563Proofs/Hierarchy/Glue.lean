import Lax119563Proofs.Hierarchy.Stack

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
