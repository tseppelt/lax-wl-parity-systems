import Lax119563Proofs.Main.Compose

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

theorem embD_zero : embD R D 0 = 0 := rfl

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
      simp [Lax489179.TuringMachine.init, Fin.succ_ne_zero, embD_zero]

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
