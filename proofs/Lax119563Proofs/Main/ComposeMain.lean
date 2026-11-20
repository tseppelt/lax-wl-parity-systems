import Lax119563Proofs.Main.ComposeCorrect

/-!
# The composition theorem

If `R` computes `y` from `x` within `t₁` steps and `D` decides `P` on `y` within `t₂` steps,
then the composed machine decides `P` on `x` within `2 t₁ + t₂ + 3` steps, provided
`|x| ≥ 2`; on inputs of length `< 2` it returns its built-in answers within `2` steps.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction step run Deterministic)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Main.Compose

open AMachine

variable {R D : Machine} {a₀ : Bool} {a₁ : Bool → Bool}

/-- Heads move by at most one cell per step. -/
theorem head_natAbs_le (M : Machine) (x : List Bool) (j : Fin (M.tapes + 1)) (t : ℕ) :
    ((runOn M x t).head j).natAbs ≤ t := by
  induction t with
  | zero => simp [runOn, Lax489179.TuringMachine.run, Lax489179.TuringMachine.init]
  | succ t ih =>
    rw [runOn_succ]
    unfold Lax489179.TuringMachine.step
    rcases (runOn M x t).answer with _ | b
    · dsimp only
      split
      · dsimp only; omega
      · dsimp only
        have := offset_bound (‹Fin (M.tapes + 1) → Move› j)
        omega
    · dsimp only; omega

theorem two_ne_zero' : (2 : Fin (S R D + 3)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 2 < S R D + 3 by omega)] at this

theorem one_ne_two' : (1 : Fin (S R D + 3)) ≠ 2 := by
  intro h
  have := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 2 < S R D + 3 by omega)] at this

/-- The symbol of a bit. -/
theorem init_tape_none_cons (b : Bool) (x : List Bool) :
    (AMachine.init (b :: x) : Cfg R D).tape none 0 = if b then 2 else 1 := by
  cases b <;> rfl

theorem init_tape_none_cons_cons (b₀ b : Bool) (x : List Bool) :
    (AMachine.init (b₀ :: b :: x) : Cfg R D).tape none 1 = if b then 2 else 1 := by
  cases b <;> rfl

theorem bitSym_ne_zero (b : Bool) : ((if b then 2 else 1 : Fin (S R D + 3))) ≠ 0 := by
  cases b
  · simp
  · exact two_ne_zero'

theorem decide_bitSym (b : Bool) : decide ((if b then 2 else 1 : Fin (S R D + 3)) = 2) = b := by
  cases b
  · simpa using one_ne_two'
  · simp

/-- The input tape of the composed machine is the embedded input tape of `R`. -/
theorem init_tape_none_embR (x : List Bool) :
    (AMachine.init x : Cfg R D).tape none =
      fun z => embR R D ((Lax489179.TuringMachine.init R x).tape 0 z) := by
  funext z
  simp only [AMachine.init, Lax489179.TuringMachine.init, true_and]
  split_ifs
  · rcases x[z.toNat]? with _ | _ | _ <;> rfl
  · rfl

theorem embR_init_eq_embD_init (y : List Bool) :
    (fun z => embR R D ((Lax489179.TuringMachine.init R y).tape 0 z)) =
      fun z => embD R D ((Lax489179.TuringMachine.init D y).tape 0 z) := by
  funext z
  simp only [Lax489179.TuringMachine.init, true_and]
  split_ifs
  · rcases y[z.toNat]? with _ | _ | _ <;> rfl
  · rfl

/-- After the two inspection steps on an input of length `≥ 2`, the composed machine starts
simulating `R`. -/
theorem simR_init (x : List Bool) (hx : 2 ≤ x.length) :
    SimR ((comp R D a₀ a₁).run 2 (AMachine.init x)) (Lax489179.TuringMachine.init R x) := by
  obtain ⟨b₀, b, x, rfl⟩ : ∃ b₀ b x', x = b₀ :: b :: x' := by
    match x, hx with
    | b₀ :: b :: x', _ => exact ⟨b₀, b, x', rfl⟩
  set c₀ : Cfg R D := AMachine.init (b₀ :: b :: x) with hc₀
  have h0 : c₀.tape none (c₀.head none) = if b₀ then 2 else 1 := init_tape_none_cons b₀ _
  have hδ₁ : (comp R D a₀ a₁).δ c₀.state (fun o => c₀.tape o (c₀.head o)) =
      .next (some (.chk b₀)) (fun o => if o = some .mk then mark R D else c₀.tape o (c₀.head o))
        (fun o => if o = none then .right else .stay) := by
    have hs : c₀.state = none := rfl
    rw [hs]
    simp only [comp, Compose.δ, h0, if_neg (bitSym_ne_zero b₀), decide_bitSym]
  set c₁ := (comp R D a₀ a₁).step c₀ with hc₁
  have hc₁' := step_eq_next (comp R D a₀ a₁) (c := c₀) rfl hδ₁
  have h1 : c₁.tape none (c₁.head none) = if b then 2 else 1 := by
    rw [hc₁, hc₁']
    exact init_tape_none_cons_cons b₀ b x
  have hδ₂ : (comp R D a₀ a₁).δ c₁.state (fun o => c₁.tape o (c₁.head o)) =
      .next (some (.sim 0 true)) (fun o => c₁.tape o (c₁.head o))
        (fun o => if o = none then .left else .stay) := by
    have hs : c₁.state = some (.chk b₀) := by rw [hc₁, hc₁']
    rw [hs]
    simp only [comp, Compose.δ, h1, if_neg (bitSym_ne_zero b)]
  have hc₂ := step_eq_next (comp R D a₀ a₁) (c := c₁) (by rw [hc₁, hc₁']) hδ₂
  show SimR ((comp R D a₀ a₁).step c₁) _
  rw [hc₂]
  rw [hc₁, hc₁']
  refine ⟨true, rfl, rfl, fun j => ⟨?_, ?_⟩, ?_, ?_, fun j => ⟨?_, ?_⟩, ?_, ?_⟩
  · cases j using Fin.cases <;> simp [Move.offset, hc₀, AMachine.init, Lax489179.TuringMachine.init]
  · refine (write_back _ _).trans ?_
    funext z
    cases j using Fin.cases with
    | zero =>
      simp only [rT_zero, reduceCtorEq, if_false]
      rw [← congrFun (init_tape_none_embR (R := R) (D := D) (b₀ :: b :: x)) z]
      split_ifs with hz
      · rw [hz]
      · rfl
    | succ j =>
      simp [hc₀, AMachine.init, Lax489179.TuringMachine.init, Fin.succ_ne_zero]
      rfl
  · simp [Move.offset, hc₀, AMachine.init, Lax489179.TuringMachine.init]
  · refine (write_back _ _).trans ?_
    funext z
    simp [hc₀, AMachine.init, mkTape]
  · simp [Move.offset, hc₀, AMachine.init]
  · refine (write_back _ _).trans ?_
    funext z
    simp [hc₀, AMachine.init]
  · simp [Lax489179.TuringMachine.init]
  · simp [Lax489179.TuringMachine.init]

theorem answer_nil : ((comp R D a₀ a₁).run 1 (AMachine.init [])).answer = some a₀ := by
  have hδ : (comp R D a₀ a₁).δ (AMachine.init [] : Cfg R D).state
      (fun o => (AMachine.init [] : Cfg R D).tape o ((AMachine.init [] : Cfg R D).head o)) =
      .halt a₀ := by
    have hs : (AMachine.init [] : Cfg R D).state = none := rfl
    rw [hs]
    simp only [comp, Compose.δ]
    exact if_pos rfl
  show ((comp R D a₀ a₁).step _).answer = _
  rw [step_eq_halt _ rfl hδ]

theorem answer_single (b : Bool) :
    ((comp R D a₀ a₁).run 2 (AMachine.init [b])).answer = some (a₁ b) := by
  set c₀ : Cfg R D := AMachine.init [b] with hc₀
  have h0 : c₀.tape none (c₀.head none) = if b then 2 else 1 := init_tape_none_cons b _
  have hδ₁ : (comp R D a₀ a₁).δ c₀.state (fun o => c₀.tape o (c₀.head o)) =
      .next (some (.chk b)) (fun o => if o = some .mk then mark R D else c₀.tape o (c₀.head o))
        (fun o => if o = none then .right else .stay) := by
    have hs : c₀.state = none := rfl
    rw [hs]
    simp only [comp, Compose.δ, h0, if_neg (bitSym_ne_zero b), decide_bitSym]
  set c₁ := (comp R D a₀ a₁).step c₀ with hc₁
  have hc₁' := step_eq_next (comp R D a₀ a₁) (c := c₀) rfl hδ₁
  have h1 : c₁.tape none (c₁.head none) = 0 := by
    rw [hc₁, hc₁']
    rfl
  have hδ₂ : (comp R D a₀ a₁).δ c₁.state (fun o => c₁.tape o (c₁.head o)) = .halt (a₁ b) := by
    have hs : c₁.state = some (.chk b) := by rw [hc₁, hc₁']
    rw [hs]
    simp only [comp, Compose.δ, h1, if_true]
  show ((comp R D a₀ a₁).step c₁).answer = _
  rw [step_eq_halt _ (by rw [hc₁, hc₁']) hδ₂]

/-- **Composition.** -/
theorem compose_decidesWithin (R D : Machine) (a₀ : Bool) (a₁ : Bool → Bool)
    {x y : List Bool} {P : Prop} {t₁ t₂ : ℕ} (hx : 2 ≤ x.length)
    (hR : ComputesWithin R x y t₁) (hD : DecidesExactlyWithin D y P t₂) :
    DecidesExactlyWithin (comp R D a₀ a₁).toMachine x P (2 * t₁ + t₂ + 3) := by
  classical
  have hex : ∃ t, (runOn R x t).answer.isSome := ⟨t₁, hR.1⟩
  have hth : (runOn R x (Nat.find hex)).answer.isSome := Nat.find_spec hex
  have hth_le : Nat.find hex ≤ t₁ := Nat.find_min' hex hR.1
  have hbefore : ∀ t < Nat.find hex, (runOn R x t).answer = none := fun t ht => by
    have := Nat.find_min hex ht
    simpa using this
  obtain ⟨t', ht'⟩ : ∃ t', Nat.find hex = t' + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    rw [h0] at hth
    simp [runOn, Lax489179.TuringMachine.run, Lax489179.TuringMachine.init] at hth
  rw [ht'] at hth hth_le hbefore
  have hsim : ∀ t ≤ t', SimR ((comp R D a₀ a₁).run (2 + t) (AMachine.init x)) (runOn R x t) := by
    intro t
    induction t with
    | zero => intro _; exact simR_init x hx
    | succ t ih =>
      intro ht
      rw [← Nat.add_assoc, AMachine.run_succ, runOn_succ]
      exact simR_step_next (ih (by omega)) (hbefore t (by omega))
        (by rw [← runOn_succ]; exact hbefore (t + 1) (by omega))
  set d := runOn R x (t' + 1) with hd
  have hrew : Rew ((comp R D a₀ a₁).run (2 + t' + 1) (AMachine.init x))
      (fun z => embR R D (d.tape 0 z)) (d.head 0) := by
    rw [AMachine.run_succ, hd, runOn_succ]
    exact simR_step_halt (hsim t' le_rfl) (hbefore t' (by omega))
      (by rw [← runOn_succ]; exact hth)
  have htape : d.tape 0 = (Lax489179.TuringMachine.init R y).tape 0 := by
    rw [hd, ← runOn_eq_of_le R x hth_le hth]
    exact hR.2
  rw [htape, embR_init_eq_embD_init] at hrew
  have hp : (d.head 0).natAbs ≤ t₁ := (head_natAbs_le R x 0 _).trans hth_le
  have hrew0 := rew_run (a₀ := a₀) (a₁ := a₁) _ _ _ rfl hrew
  have hsimD := simD_run (a₀ := a₀) (a₁ := a₁) (simD_of_rew (a₀ := a₀) (a₁ := a₁) hrew0) t₂
  obtain ⟨b, hb, hP⟩ := hD
  have hans := hsimD.2.1
  change _ = (runOn D y t₂).answer at hans
  rw [hb] at hans
  refine decidesWithin_mono (t := 2 + t' + 1 + (d.head 0).natAbs + 1 + t₂) ?_ (by omega)
  refine decidesWithin_toMachine _ x P _ b ?_ hP
  rw [AMachine.run_add, AMachine.run_succ, AMachine.run_add]
  exact hans

/-- **Short inputs.** -/
theorem compose_short (R D : Machine) (Q : List Bool → Prop) [DecidablePred Q]
    (x : List Bool) (hx : x.length < 2) :
    DecidesExactlyWithin (comp R D (decide (Q [])) (fun b => decide (Q [b]))).toMachine x (Q x) 2 := by
  match x, hx with
  | [], _ =>
    refine decidesWithin_mono (t := 1) ?_ (by omega)
    exact decidesWithin_toMachine _ _ _ _ _ answer_nil (by simp)
  | [b], _ =>
    exact decidesWithin_toMachine _ _ _ _ _ (answer_single b) (by simp)

end Lax119563Proofs.Main.Compose
