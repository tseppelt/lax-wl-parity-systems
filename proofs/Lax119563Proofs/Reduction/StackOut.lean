import Lax119563Proofs.Hierarchy.Glue

/-!
# Stack programs computing outputs

The big-step semantics `Prog.Runs` of stack programs (area `Hierarchy`) forgets the head
positions. For the output convention of `ComputesWithin` the output must start at cell `0`
of tape `0`, so we track the heads: `Prog.RunsH p (s, h) (s', h') t` additionally records the
head positions (a push moves the head left, a pop moves it right, also on an empty stack).

`Prog.computesWithin`: if `p` runs from the input stacks with head `0` and ends with `y` on
stack `0` and head `0` on tape `0`, then `p.toMachine ans` computes `y` from `x`.
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime Lax119563Proofs.Hierarchy

namespace Lax119563Proofs.Reduction

variable {K m : ℕ}

namespace Prog

open Hierarchy.Prog

/-- Stack contents together with the head positions. -/
abbrev SH (K m : ℕ) := Stacks K m × (Fin K → ℤ)

/-- Big-step semantics with head positions. -/
inductive RunsH : Hierarchy.Prog K m → SH K m → SH K m → ℕ → Prop
  | skip {s} : RunsH .skip s s 1
  | push {i a s h} : RunsH (.push i a) (s, h)
      (Function.update s i (a :: s i), Function.update h i (h i - 1)) 2
  | pop {i s h} : RunsH (.pop i) (s, h)
      (Function.update s i (s i).tail, Function.update h i (h i + 1)) 1
  | seq {p q x₁ x₂ x₃ t₁ t₂} : RunsH p x₁ x₂ t₁ → RunsH q x₂ x₃ t₂ →
      RunsH (.seq p q) x₁ x₃ (t₁ + t₂)
  | iteT {c p q x x' t} : c (tops x.1) = true → RunsH p x x' t → RunsH (.ite c p q) x x' (t + 1)
  | iteF {c p q x x' t} : c (tops x.1) = false → RunsH q x x' t → RunsH (.ite c p q) x x' (t + 1)
  | loopF {c p x} : c (tops x.1) = false → RunsH (.loop c p) x x 1
  | loopT {c p x₁ x₂ x₃ t₁ t₂} : c (tops x₁.1) = true → RunsH p x₁ x₂ t₁ →
      RunsH (.loop c p) x₂ x₃ t₂ → RunsH (.loop c p) x₁ x₃ (t₁ + t₂ + 1)

/-- Forgetting the heads. -/
theorem RunsH.runs {p : Hierarchy.Prog K m} {x x' : SH K m} {t : ℕ} (h : RunsH p x x' t) :
    p.Runs x.1 x'.1 t := by
  induction h with
  | skip => exact .skip
  | push => exact .push
  | pop => exact .pop
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteT hc _ ih => exact .iteT hc ih
  | iteF hc _ ih => exact .iteF hc ih
  | loopF hc => exact .loopF hc
  | loopT hc _ _ ih₁ ih₂ => exact .loopT hc ih₁ ih₂

/-- Every run can be equipped with head positions. -/
theorem Runs.runsH {p : Hierarchy.Prog K m} {s s' : Stacks K m} {t : ℕ} (h : p.Runs s s' t)
    (hd : Fin K → ℤ) : ∃ hd', RunsH p (s, hd) (s', hd') t := by
  induction h generalizing hd with
  | skip => exact ⟨hd, .skip⟩
  | push => exact ⟨_, .push⟩
  | pop => exact ⟨_, .pop⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨h₁, e₁⟩ := ih₁ hd
    obtain ⟨h₂, e₂⟩ := ih₂ h₁
    exact ⟨h₂, .seq e₁ e₂⟩
  | iteT hc _ ih => obtain ⟨h₁, e₁⟩ := ih hd; exact ⟨h₁, .iteT hc e₁⟩
  | iteF hc _ ih => obtain ⟨h₁, e₁⟩ := ih hd; exact ⟨h₁, .iteF hc e₁⟩
  | loopF hc => exact ⟨hd, .loopF hc⟩
  | loopT hc _ _ ih₁ ih₂ =>
    obtain ⟨h₁, e₁⟩ := ih₁ hd
    obtain ⟨h₂, e₂⟩ := ih₂ h₁
    exact ⟨h₂, .loopT hc e₁ e₂⟩

lemma head_noop (T : Tapes K (Fin (m + 3))) :
    (T.apply (noop T.read).1 (noop T.read).2).head = T.head := by
  funext j; simp [noop, Tapes.apply, Move.offset]

lemma head_pop (T : Tapes K (Fin (m + 3))) (i : Fin K) :
    (T.apply (popA i T.read).1 (popA i T.read).2).head =
      Function.update T.head i (T.head i + 1) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [popA, Tapes.apply, Move.offset]
  · simp [popA, Tapes.apply, Move.offset, hj]

lemma head_push (T : Tapes K (Fin (m + 3))) (i : Fin K) (a : Fin (m + 2)) :
    let T₁ := T.apply (pushL i T.read).1 (pushL i T.read).2
    (T₁.apply (pushW i a T₁.read).1 (pushW i a T₁.read).2).head =
      Function.update T.head i (T.head i - 1) := by
  intro T₁
  funext j
  by_cases hj : j = i
  · subst hj; simp [T₁, pushL, pushW, Tapes.apply, Move.offset]; ring
  · simp [T₁, pushL, pushW, Tapes.apply, Move.offset, hj]

/-- Correctness of the compiler, with head positions. -/
theorem compile_endsH {p : Hierarchy.Prog K m} {x x' : SH K m} {t : ℕ} (hp : RunsH p x x' t)
    {T : Tapes K (Fin (m + 3))} (hT : Rep x.1 T) (hh : T.head = x.2) :
    ∃ T', Rep x'.1 T' ∧ T'.head = x'.2 ∧ p.compile.Ends p.start T none T' t := by
  induction hp generalizing T with
  | skip => exact ⟨_, rep_noop hT, (head_noop T).trans hh, Mach.prim_ends _ _⟩
  | @push i a s h =>
    refine ⟨_, rep_push hT i a, ?_, Mach.seq_left_exit (Mach.prim_ends _ _) (Mach.prim_ends _ _)⟩
    rw [head_push]; subst hh; rfl
  | @pop i s h =>
    refine ⟨_, rep_pop hT i, ?_, Mach.prim_ends _ _⟩
    rw [head_pop]; subst hh; rfl
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨T₁, h₁, g₁, e₁⟩ := ih₁ hT hh
    obtain ⟨T₂, h₂, g₂, e₂⟩ := ih₂ h₁ g₁
    exact ⟨T₂, h₂, g₂, Mach.seq_left_exit e₁ e₂⟩
  | iteT hc _ ih =>
    obtain ⟨T', h', g', e⟩ := ih hT hh
    refine ⟨T', h', g', Mach.branch_true ?_ e⟩
    rw [hT.tops]; exact hc
  | iteF hc _ ih =>
    obtain ⟨T', h', g', e⟩ := ih hT hh
    refine ⟨T', h', g', Mach.branch_false ?_ e⟩
    rw [hT.tops]; exact hc
  | loopF hc =>
    refine ⟨T, hT, hh, Mach.loop_false ?_⟩
    rw [hT.tops]; exact hc
  | loopT hc _ _ ih₁ ih₂ =>
    obtain ⟨T₁, h₁, g₁, e₁⟩ := ih₁ hT hh
    obtain ⟨T₂, h₂, g₂, e₂⟩ := ih₂ h₁ g₁
    refine ⟨T₂, h₂, g₂, Mach.loop_true ?_ e₁ e₂⟩
    rw [hT.tops]; exact hc

end Prog

section Final

variable {Λ : Type} [Fintype Λ] [DecidableEq Λ] {n : ℕ}

/-- A halting run of a `Mach` ends in the configuration with the final tapes. -/
lemma Mach.toMachine_ends_tapes {M : Mach (n + 1) (Fin (m + 3)) Λ} {s q : Λ}
    {T T' : Tapes (n + 1) (Fin (m + 3))} {b : Bool} {t : ℕ}
    (h : M.Ends q T (some b) T' t) :
    (drun (M.toMachine s) t (M.cfg s q T)).answer = some b ∧
      (drun (M.toMachine s) t (M.cfg s q T)).tape = T'.tape := by
  generalize ho : (some b : Option Bool) = o at h
  induction h with
  | @halt q T b' hq =>
    cases ho
    rw [drun_succ]
    have : step (M.toMachine s) false (M.cfg s q T) = { M.cfg s q T with answer := some b } := by
      simp only [step, Mach.cfg, Mach.toMachine, Equiv.symm_apply_apply]
      rw [show (fun j => T.tape j (T.head j)) = T.read from rfl, hq]
    rw [this, drun_of_answer rfl]
    exact ⟨rfl, rfl⟩
  | exit hq => cases ho
  | @next q q' T w mv o T' t hq _ ih =>
    rw [drun_succ]
    have : step (M.toMachine s) false (M.cfg s q T) = M.cfg s q' (T.apply w mv) := by
      simp only [step, Mach.cfg, Mach.toMachine, Equiv.symm_apply_apply]
      rw [show (fun j => T.tape j (T.head j)) = T.read from rfl, hq]
      rfl
    rw [this]
    exact ih ho

end Final

/-- **Output of a stack program.** If `p` runs from the input stacks of `x` (heads at `0`) to
stacks with `y` on stack `0` and the head of tape `0` back at `0`, then the machine
`p.toMachine ans` computes `y` from `x` within `t + 1` steps. -/
theorem Prog.computesWithin {p : Hierarchy.Prog (K + 1) m}
    {ans : (Fin (K + 1) → Option (Fin (m + 2))) → Bool} {x y : List Bool}
    {s' : Stacks (K + 1) m} {hd' : Fin (K + 1) → ℤ} {t : ℕ}
    (h : Prog.RunsH p (inputStacks K m x, fun _ => 0) (s', hd') t)
    (hy : s' 0 = y.map (bitSym m)) (hh : hd' 0 = 0) :
    ComputesWithin (p.toMachine ans) x y (t + 1) := by
  obtain ⟨T', hT', hH', hE⟩ := Prog.compile_endsH h (rep_input K m x) rfl
  have hE' := Mach.seq_left_exit (M₂ := Mach.haltWith (fun r => ans (fun i => decSym (r i))))
    hE (Mach.haltWith_ends _ T')
  have := Mach.toMachine_ends_tapes (s := .inl p.start) hE'
  unfold ComputesWithin HaltsWithin
  rw [runOn_eq_drun, Hierarchy.Prog.toMachine, Mach.init_toMachine, this.1, this.2,
    Mach.init_toMachine]
  refine ⟨rfl, ?_⟩
  funext z
  show T'.tape 0 z = (inputTapes K m y).tape 0 z
  have h1 := hT' 0 z
  have h2 := rep_input K m y 0 z
  have h3 : (inputTapes K m y).head 0 = 0 := rfl
  rw [hH'] at h1
  rw [h1, h2, h3]
  simp [hh, hy, inputStacks]

end Lax119563Proofs.Reduction
