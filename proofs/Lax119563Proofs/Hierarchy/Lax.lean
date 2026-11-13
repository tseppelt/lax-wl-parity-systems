import Lax119563Proofs.Hierarchy.Mach

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
