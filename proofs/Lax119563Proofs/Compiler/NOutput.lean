import Lax119563Proofs.Compiler.NMachine

/-!
# Machines of register programs with outputs shorter than the input

`NProg.computesWithin` (`Compiler.NMachine`) needs `|x| ≤ |encodeNats out|`: in the stack
model a pop moves the head right and a push moves it left and writes, so a stack program
cannot move the head of tape `0` left over the erased input without leaving symbols behind.

`NProg.machineO p` removes this condition (and the condition that the cursor is back at `0`):
1. the stack program `outP₁ p` runs `compileN p`, moves the output to helper `nT0`, and drains
   the unread input (stack `nIo`) and the read input (stack `nXl`), pushing one unary symbol
   per symbol onto helper `nT1`; now stack `nIo` is empty and its head is at `|x|`;
2. the raw machine `leftLoop` pops `nT1` and moves the head of tape `0` left once per
   symbol (`rep_moveL`: an empty stack is represented with any head position), so the head of
   tape `0` is back at `0`;
3. the stack program `outP₂` moves the output to `nT1` while popping the empty stack `nIo`
   (moving its head to `|y|`) and pushes it back onto `nIo` (moving the head to `0`).

**`NProg.computesWithinO`**: every run of `p` from the zero state gives a computation of
`encodeNats out` within `t + 20 (|x| + |encodeNats out|) + 10` steps.
-/

open Function Lax119563.BinaryEncodings Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Compiler

open Hierarchy Hierarchy.Prog Lax119563Proofs.Reduction Lax119563Proofs.Reduction.Prog

variable {R Q : ℕ}

/-! ## Draining a stack into a unary counter -/

/-- Pop stack `i` completely, pushing one symbol `0` onto `j` per popped symbol. -/
def drainP {K : ℕ} (i j : Fin K) : Hierarchy.Prog K 0 :=
  .loop (fun t => (t i).isSome) (.seq (.pop i) (.push j 0))

lemma drainP_runsH {K : ℕ} {i j : Fin K} (hij : i ≠ j) :
    ∀ (l : List (Fin 2)) (s : Stacks K 0) (hd : Fin K → ℤ), s i = l →
      RunsLeH (drainP i j) (s, hd)
        (update (update s i []) j (unary 0 l.length ++ s j),
          update (update hd i (hd i + l.length)) j (hd j - l.length))
        (4 * l.length + 1)
  | [], s, hd, hs => by
    refine (RunsLeH.loopF (p := .seq (.pop i) (.push j 0)) (c := fun r => (r i).isSome)
      (x := (s, hd)) (by simp [tops, hs])).of_eq ?_ (by simp)
    refine Prod.ext ?_ ?_
    · funext k; simp only [update_apply]; split_ifs <;> simp_all
    · funext k; simp only [update_apply]; split_ifs <;> simp_all
  | a :: l, s, hd, hs => by
    have h1 : RunsLeH (.seq (.pop i) (.push j 0)) (s, hd)
        (update (update s i (s i).tail) j (0 :: update s i (s i).tail j),
          update (update hd i (hd i + 1)) j (update hd i (hd i + 1) j - 1)) 3 :=
      ⟨3, le_rfl, .seq .pop .push⟩
    have e1 : update (update s i (s i).tail) j (0 :: update s i (s i).tail j) =
        update (update s i l) j (0 :: s j) := by
      rw [hs, update_of_ne hij.symm]; rfl
    have e2 : update (update hd i (hd i + 1)) j (update hd i (hd i + 1) j - 1) =
        update (update hd i (hd i + 1)) j (hd j - 1) := by
      rw [update_of_ne hij.symm]
    rw [e1, e2] at h1
    have h2 := drainP_runsH hij l (update (update s i l) j (0 :: s j))
      (update (update hd i (hd i + 1)) j (hd j - 1)) (by simp [update_of_ne hij])
    refine (RunsLeH.loopT (c := fun r => (r i).isSome) (by simp [tops, hs]) h1 h2).of_eq ?_
      (by simp only [List.length_cons]; omega)
    refine Prod.ext ?_ ?_
    · funext k; simp only [update_apply]
      split_ifs <;> simp_all [List.replicate_succ']
    · funext k
      simp only [update_apply, List.length_cons]
      split_ifs <;> simp_all <;> ring

/-! ## Moving the head of an empty stack -/

lemma rep_moveL {K : ℕ} {s : Stacks K 0} {T : Tapes K (Fin (0 + 3))} (h : Rep s T) {i : Fin K}
    (hs : s i = []) : Rep s (T.apply (pushL i T.read).1 (pushL i T.read).2) := by
  intro j z
  have ht : (T.apply (pushL i T.read).1 (pushL i T.read).2).tape j z = T.tape j z := by
    simp only [Tapes.apply, pushL, Tapes.read]
    split_ifs with hz <;> simp [hz]
  rw [ht, h j z]
  by_cases hj : j = i
  · subst hj; simp [hs]
  · simp [Tapes.apply, pushL, hj, Lax489179.TuringMachine.Move.offset]

lemma head_moveL {K : ℕ} (T : Tapes K (Fin (0 + 3))) (i : Fin K) :
    (T.apply (pushL i T.read).1 (pushL i T.read).2).head = update T.head i (T.head i - 1) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [pushL, Tapes.apply, Lax489179.TuringMachine.Move.offset]; ring
  · simp [pushL, Tapes.apply, Lax489179.TuringMachine.Move.offset, hj]

/-- Pop the unary counter `c` and move the head of tape `i` left, until `c` is empty. -/
def leftLoop {K : ℕ} (i c : Fin K) : Mach K (Fin (0 + 3)) (Option (Unit ⊕ Unit)) :=
  Mach.loop (fun r => (decSym (r c)).isSome)
    (Mach.seq (Mach.prim (popA c)) (Mach.prim (pushL i)) ()) (.inl ())

lemma leftLoop_ends {K : ℕ} {i c : Fin K} (hic : i ≠ c) :
    ∀ (n : ℕ) (s : Stacks K 0) (T : Tapes K (Fin (0 + 3))), Rep s T → s i = [] → s c = unary 0 n →
      ∃ T', Rep (update s c []) T' ∧
        T'.head = update (update T.head c (T.head c + n)) i (T.head i - n) ∧
        (leftLoop i c).Ends none T none T' (3 * n + 1)
  | 0, s, T, hT, _, hc => by
    refine ⟨T, ?_, ?_, Mach.loop_false ?_⟩
    · rw [show ([] : List (Fin (0 + 2))) = s c by rw [hc]; rfl, update_eq_self]; exact hT
    · funext j; simp only [update_apply]; split_ifs <;> simp_all
    · have := congrFun hT.tops c
      simp only [tops, hc] at this
      simp [Tapes.read] at this ⊢; simpa using this
  | n + 1, s, T, hT, hi, hc => by
    -- the body: pop the counter, move the head of tape `i` left
    set T₁ := T.apply (popA c T.read).1 (popA c T.read).2
    have h₁ : Rep (update s c (s c).tail) T₁ := rep_pop hT c
    set T₂ := T₁.apply (pushL i T₁.read).1 (pushL i T₁.read).2
    have hi₁ : update s c (s c).tail i = [] := by rw [update_of_ne hic, hi]
    have h₂ : Rep (update s c (s c).tail) T₂ := rep_moveL h₁ hi₁
    have hb : (Mach.seq (Mach.prim (popA c)) (Mach.prim (pushL i)) ()).Ends (.inl ()) T none T₂ 2 :=
      Mach.seq_left_exit (Mach.prim_ends _ _) (Mach.prim_ends _ _)
    have hc' : update s c (s c).tail c = unary 0 n := by
      rw [update_self, hc]; rfl
    obtain ⟨T', h', hh', he'⟩ := leftLoop_ends hic n (update s c (s c).tail) T₂ h₂ hi₁ hc'
    refine ⟨T', ?_, ?_, ?_⟩
    · simpa using h'
    · rw [hh', head_moveL, head_pop]
      funext j; simp only [update_apply]
      split_ifs <;> simp_all <;> ring
    · have hcond : (fun r : Fin K → Fin (0 + 3) => (decSym (r c)).isSome) T.read = true := by
        have := congrFun hT.tops c
        simp only [tops, hc] at this
        simp only [this]; simp
      rw [show 3 * (n + 1) + 1 = 2 + (3 * n + 1) + 1 by ring]
      exact Mach.loop_true hcond hb he'

/-! ## The machine -/

/-- Phase 1: run the program, move the output to `nT0`, drain the input into `nT1`. -/
def outP₁ (p : NProg R Q) : Hierarchy.Prog (R + Q + 7) 0 :=
  .seq (compileN p) (.seq (moveAll nOut nT0) (.seq (drainP nIo nT1) (drainP nXl nT1)))

/-- Phase 3: move the output to `nT1` popping (the empty) `nIo`, then push it onto `nIo`. -/
def outP₂ : Hierarchy.Prog (R + Q + 7) 0 := .seq countLoopN (moveAll nT1 nIo)

/-- The three phases followed by halting. -/
def machOMach (p : NProg R Q) :=
  Mach.seq (Mach.seq (Mach.seq (outP₁ p).compile (leftLoop nIo nT1) none)
    (outP₂ (R := R) (Q := Q)).compile (outP₂ (R := R) (Q := Q)).start)
    (Mach.haltWith (k := R + Q + 7) (Γ := Fin (0 + 3)) (fun _ => false)) ()

/-- The machine of a register program, for outputs of any length. -/
noncomputable def NProg.machineO (p : NProg R Q) : Machine :=
  Mach.toMachine (n := R + Q + 6) (m := 0) (machOMach p) (.inl (.inl (.inl (outP₁ p).start)))

lemma NProg.machineO_deterministic (p : NProg R Q) : Deterministic p.machineO :=
  Mach.toMachine_deterministic _ _

/-- **Machines of register programs, outputs of any length.** -/
theorem NProg.computesWithinO {p : NProg R Q} {x : List Bool} {w t : ℕ} {st' : NSt R Q}
    (h : NRuns x w p ⟨fun _ => 0, fun _ => [], 0, []⟩ st' t) :
    ComputesWithin p.machineO x (encodeNats st'.out)
      (t + 20 * (x.length + (encodeNats st'.out).length) + 10) := by
  set y := encodeNats st'.out
  have hpos : st'.pos ≤ x.length := h.pos_le (by simp)
  have hoi : (nOut : Fin (R + Q + 7)) ≠ nIo := by ndist
  have h0i : (nT0 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have h1i : (nT1 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have ho0 : (nOut : Fin (R + Q + 7)) ≠ nT0 := by ndist
  have ho1 : (nOut : Fin (R + Q + 7)) ≠ nT1 := by ndist
  have h01 : (nT0 : Fin (R + Q + 7)) ≠ nT1 := by ndist
  have hx1 : (nXl : Fin (R + Q + 7)) ≠ nT1 := by ndist
  have hxi : (nXl : Fin (R + Q + 7)) ≠ nIo := by ndist
  have hx0 : (nXl : Fin (R + Q + 7)) ≠ nT0 := by ndist
  have hxo : (nXl : Fin (R + Q + 7)) ≠ nOut := by ndist
  -- phase 1
  obtain ⟨hd₁, e₁, r₁⟩ := compileN_runs h (by simp) (fun _ => 0) (by simp)
  have a₂ := moveAll_runs ho0 (m := 0) ((bs y).reverse) (encN x st') (encN_out x st')
  obtain ⟨hd₂, e₂, r₂⟩ := RunsLe.toH a₂ (avoids_moveAll hoi h0i) hd₁
  set S₂ := update (update (encN x st') nOut []) nT0 ((bs y).reverse.reverse ++ encN x st' nT0)
  have r₃ := drainP_runsH h1i.symm (bs (x.drop st'.pos)) S₂ hd₂
    (by simp [S₂, update_of_ne hoi.symm, update_of_ne h0i.symm])
  set S₃ := update (update S₂ nIo []) nT1 (unary 0 (bs (x.drop st'.pos)).length ++ S₂ nT1)
  set hd₃ := update (update hd₂ nIo (hd₂ nIo + ((bs (x.drop st'.pos)).length : ℤ))) nT1
    (hd₂ nT1 - ((bs (x.drop st'.pos)).length : ℤ))
  have r₄ := drainP_runsH hx1 ((bs (x.take st'.pos)).reverse) S₃ hd₃
    (by simp [S₃, S₂, update_of_ne hx1, update_of_ne hxi, update_of_ne hx0, update_of_ne hxo])
  set S₄ := update (update S₃ nXl []) nT1
    (unary 0 (bs (x.take st'.pos)).reverse.length ++ S₃ nT1)
  set hd₄ := update (update hd₃ nXl (hd₃ nXl + ((bs (x.take st'.pos)).reverse.length : ℤ))) nT1
    (hd₃ nT1 - ((bs (x.take st'.pos)).reverse.length : ℤ))
  obtain ⟨t₁, ht₁, R₁⟩ := r₁.seq (r₂.seq (r₃.seq r₄))
  rw [encN_init] at R₁
  obtain ⟨T₁, hT₁, hH₁, E₁⟩ := Prog.compile_endsH (p := outP₁ p) R₁ (rep_input _ 0 x) rfl
  have hS₄io : S₄ nIo = [] := by
    simp [S₄, S₃, update_of_ne hxi.symm, update_of_ne h1i.symm]
  have hS₄t1 : S₄ nT1 = unary 0 x.length := by
    simp only [S₄, S₃, S₂, update_self, update_of_ne h01.symm, update_of_ne ho1.symm,
      encN_t1, List.append_nil, List.length_reverse, length_bs,
      List.length_take, List.length_drop]
    rw [List.replicate_append_replicate]; congr 1; omega
  have hd₄io : hd₄ nIo = x.length := by
    simp only [hd₄, hd₃, update_of_ne hxi.symm, update_of_ne h1i.symm, update_self, e₂, e₁,
      length_bs, List.length_drop]
    push_cast [hpos]; ring
  -- phase 2
  obtain ⟨T₂, hT₂, hH₂, E₂⟩ := leftLoop_ends h1i.symm (n := x.length) S₄ T₁ hT₁ hS₄io
    hS₄t1
  -- phase 3
  set S₅ := update S₄ nT1 []
  have hS₅0 : S₅ nT0 = bs y := by
    simp [S₅, S₄, S₃, S₂, update_of_ne h01, update_of_ne hx0.symm, update_of_ne h0i.symm.symm]
  obtain ⟨hd₆, e₆, r₆⟩ := countLoopN_runsH (R := R) (Q := Q) (bs y) S₅ T₂.head hS₅0
  set S₆ := update (update (update S₅ nT0 []) nT1 ((bs y).reverse ++ S₅ nT1)) nIo
    ((S₅ nIo).drop (bs y).length)
  have r₇ := moveAll_runsH h1i (m := 0) ((bs y).reverse) S₆ hd₆
    (by simp [S₆, S₅, update_of_ne h1i])
  obtain ⟨t₂, ht₂, R₂⟩ := r₆.seq r₇
  obtain ⟨T₃, hT₃, hH₃, E₃⟩ := Prog.compile_endsH (p := outP₂ (R := R) (Q := Q)) R₂ hT₂ rfl
  have E := Mach.seq_left_exit (Mach.seq_left_exit (Mach.seq_left_exit E₁ E₂) E₃)
    (Mach.haltWith_ends (k := R + Q + 7) (Γ := Fin (0 + 3)) (fun _ => false) T₃)
  have hE := Mach.toMachine_ends_tapes (n := R + Q + 6) (m := 0) (M := machOMach p)
    (s := .inl (.inl (.inl (outP₁ p).start))) E
  have hc : ComputesWithin p.machineO x y (t₁ + (3 * x.length + 1) + t₂ + 1) := by
    unfold ComputesWithin HaltsWithin
    rw [runOn_eq_drun, NProg.machineO, Mach.init_toMachine, hE.1, hE.2, Mach.init_toMachine]
    refine ⟨rfl, ?_⟩
    funext z
    show T₃.tape 0 z = (inputTapes (R + Q + 6) 0 y).tape 0 z
    have h1 := hT₃ 0 z
    have h2 := rep_input (R + Q + 6) 0 y 0 z
    have h3 : (inputTapes (R + Q + 6) 0 y).head 0 = 0 := rfl
    rw [hH₃] at h1
    rw [h1, h2, h3]
    have hio : S₆ nIo = [] := by simp [S₆, S₅, hS₄io, update_of_ne h1i.symm]
    have hhd : hd₆ nIo = (bs y).length := by
      rw [e₆, hH₂]; simp [hH₁, hd₄io]
    show cell (update (update S₆ nT1 []) nIo ((bs y).reverse.reverse ++ S₆ nIo) nIo) (z - _) = _
    rw [update_self, hio, List.reverse_reverse, List.append_nil]
    show cell (bs y) (z - update (update hd₆ nT1 (hd₆ nT1 + ((bs y).reverse.length : ℤ))) nIo
      (hd₆ nIo - ((bs y).reverse.length : ℤ)) nIo) = _
    rw [update_self, hhd, List.length_reverse, sub_self, sub_zero]
    simp only [inputStacks, if_true]
    congr 1
  refine ComputesWithin.mono hc ?_
  simp only [length_bs, List.length_reverse, List.length_take, List.length_drop] at ht₁ ht₂
  omega

end Lax119563Proofs.Compiler
