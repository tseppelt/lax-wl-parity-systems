import Lax119563Proofs.Bridges.TM2Sim.Stmts

/-!
# Simulating archive multitape machines by mathlib stack machines: the phases

Exact step counts for each phase of the stack machine `prog` (see `Defs`), stated on stack
contents `mkStk io outRev tmp Ls Rs`.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction)
open Turing

namespace Lax119563Proofs.Bridges.TM2Sim

variable {R : Machine} {A : Type} {τi : InTransducer A} {τo : OutTransducer A} [Inhabited A]

variable (R A τi τo) in
/-- Configurations of the stack machine. -/
abbrev Cfg' := TM2.Cfg (Γ' R A) Lbl (Var R A τi τo)

variable (R A τi τo) in
/-- The step function of the stack machine. -/
def stepF : Cfg' R A τi τo → Option (Cfg' R A τi τo) := TM2.step prog

variable (R A τi τo) in
/-- Exactly `n` steps lead from `c` to `c'`. -/
def Reaches (n : ℕ) (c c' : Cfg' R A τi τo) : Prop :=
  (flip bind (stepF R A τi τo))^[n] (some c) = some c'

lemma reaches_zero (c : Cfg' R A τi τo) : Reaches R A τi τo 0 c c := rfl

lemma reaches_succ {n : ℕ} {c c' c'' : Cfg' R A τi τo} (h : stepF R A τi τo c = some c')
    (h' : Reaches R A τi τo n c' c'') : Reaches R A τi τo (n + 1) c c'' := by
  unfold Reaches at *
  rw [Function.iterate_succ_apply]
  simpa [flip, h] using h'

lemma reaches_one {c c' : Cfg' R A τi τo} (h : stepF R A τi τo c = some c') :
    Reaches R A τi τo 1 c c' := reaches_succ h (reaches_zero _)

lemma reaches_trans {n m : ℕ} {c c' c'' : Cfg' R A τi τo} (h : Reaches R A τi τo n c c')
    (h' : Reaches R A τi τo m c' c'') : Reaches R A τi τo (n + m) c c'' := by
  unfold Reaches at *
  rw [add_comm, Function.iterate_add_apply, h, h']

lemma stepF_some (l : Lbl) (v : Var R A τi τo) (S : ∀ k, List (Γ' R A k)) :
    stepF R A τi τo ⟨some l, v, S⟩ = some (TM2.stepAux (prog l) v S) := rfl


/-! ## Input phase -/

lemma step_inPop_cons (a : A) (u : List A) (v : Var R A τi τo) (t : List (G R)) (Ls Rs) :
    stepF R A τi τo ⟨some .inPop, v, mkStk (a :: u) [] t Ls Rs⟩ =
      some ⟨some .inPop, { v with inSym := some a, qi := (τi.δ v.qi a).1 },
        mkStk u [] (((τi.δ v.qi a).2.map bitG).reverse ++ t) Ls Rs⟩ := by
  rw [stepF_some]
  simp only [prog, TM2.stepAux, mkStk_io, update_io, List.head?_cons, List.tail_cons]
  rw [stepAux_pushOpt, stepAux_pushOpt]
  simp only [TM2.stepAux, inStep, Option.isSome_some, cond_true]
  rw [← List.append_assoc, pushTwo_eq _ (τi.δ_len _ _)]

lemma step_inPop_nil (v : Var R A τi τo) (t : List (G R)) (Ls Rs) :
    stepF R A τi τo ⟨some .inPop, v, mkStk [] [] t Ls Rs⟩ =
      some ⟨some .inRev, { v with inSym := none },
        mkStk [] [] (((τi.final v.qi).map bitG).reverse ++ t) Ls Rs⟩ := by
  rw [stepF_some]
  simp only [prog, TM2.stepAux, mkStk_io, update_io, List.head?_nil, List.tail_nil]
  rw [stepAux_pushOpt, stepAux_pushOpt]
  simp only [TM2.stepAux, inStep, Option.isSome_none, cond_false]
  rw [← List.append_assoc, pushTwo_eq _ (τi.final_len _)]

lemma inPop_run (u : List A) : ∀ (v : Var R A τi τo) (t : List (G R)) (Ls Rs),
    ∃ v' : Var R A τi τo, v'.q = v.q ∧ v'.qo = v.qo ∧
      Reaches R A τi τo (u.length + 1) ⟨some .inPop, v, mkStk u [] t Ls Rs⟩
        ⟨some .inRev, v', mkStk [] [] (((τi.run v.qi u).map bitG).reverse ++ t) Ls Rs⟩ := by
  induction u with
  | nil =>
    intro v t Ls Rs
    exact ⟨{ v with inSym := none }, rfl, rfl, by
      simpa [InTransducer.run] using reaches_one (step_inPop_nil v t Ls Rs)⟩
  | cons a u ih =>
    intro v t Ls Rs
    obtain ⟨v', hq, hqo, hr⟩ := ih { v with inSym := some a, qi := (τi.δ v.qi a).1 }
      (((τi.δ v.qi a).2.map bitG).reverse ++ t) Ls Rs
    refine ⟨v', hq, hqo, ?_⟩
    have := reaches_succ (step_inPop_cons a u v t Ls Rs) hr
    simpa [InTransducer.run, List.map_append, List.reverse_append, List.append_assoc,
      Nat.add_comm] using this

lemma inRev_run (t : List (G R)) : ∀ (v : Var R A τi τo) (Ls Rs),
    ∃ v' : Var R A τi τo, v'.q = v.q ∧ v'.qo = v.qo ∧
      Reaches R A τi τo (t.length + 1) ⟨some .inRev, v, mkStk [] [] t Ls Rs⟩
        ⟨some .mark, v', mkStk [] [] [] Ls (Function.update Rs 0 (t.reverse ++ Rs 0))⟩ := by
  induction t with
  | nil =>
    intro v Ls Rs
    refine ⟨{ v with cell := none }, rfl, rfl, reaches_one ?_⟩
    rw [stepF_some]
    simp [prog, TM2.stepAux]
  | cons g t ih =>
    intro v Ls Rs
    obtain ⟨v', hq, hqo, hr⟩ := ih { v with cell := some g } Ls (Function.update Rs 0 (g :: Rs 0))
    refine ⟨v', hq, hqo, ?_⟩
    have hs : stepF R A τi τo ⟨some .inRev, v, mkStk [] [] (g :: t) Ls Rs⟩ =
        some ⟨some .inRev, { v with cell := some g },
          mkStk [] [] t Ls (Function.update Rs 0 (g :: Rs 0))⟩ := by
      rw [stepF_some]
      simp [prog, TM2.stepAux]
    have := reaches_succ hs hr
    simpa [Nat.add_comm] using this

lemma step_mark (v : Var R A τi τo) (Ls Rs) :
    stepF R A τi τo ⟨some .mark, v, mkStk [] [] [] Ls Rs⟩ =
      some ⟨some .sim, { v with cell := (Rs 0).head? },
        mkStk [] [] [] Ls (Function.update Rs 0 ((top (Rs 0), true) :: (Rs 0).tail))⟩ := by
  rw [stepF_some]
  simp [prog, TM2.stepAux, top]


/-! ## Simulation phase -/

/-- The variables after scanning all tapes. -/
def scanV (v : Var R A τi τo) (Rs : Fin (R.tapes + 1) → List (G R)) : Var R A τi τo :=
  { v with scanned := fun i => top (Rs i) }

lemma step_sim_halt (v : Var R A τi τo) (Ls Rs) (h : isHalt (instr (scanV v Rs)) = true) :
    stepF R A τi τo ⟨some .sim, v, mkStk [] [] [] Ls Rs⟩ =
      some ⟨some .gather, scanV v Rs, mkStk [] [] [] Ls Rs⟩ := by
  rw [stepF_some]
  simp only [prog]
  rw [stepAux_scanAll]
  simp only [List.mem_finRange, if_true]
  simp only [scanV] at h
  simp [TM2.stepAux, h, scanV]

lemma step_sim_next (v : Var R A τi τo) (Ls Rs) (h : isHalt (instr (scanV v Rs)) = false) :
    ∃ o, stepF R A τi τo ⟨some .sim, v, mkStk [] [] [] Ls Rs⟩ =
      some ⟨some .sim, { scanV v Rs with cell := o, q := nextQ (scanV v Rs) },
        mkStk [] [] [] (applyLs (List.finRange (R.tapes + 1)) (scanV v Rs) Ls Rs)
          (applyRs (List.finRange (R.tapes + 1)) (scanV v Rs) Ls Rs)⟩ := by
  rw [stepF_some]
  simp only [prog]
  rw [stepAux_scanAll]
  simp only [List.mem_finRange, if_true]
  have h' : isHalt (instr { v with scanned := fun i => top (Rs i) }) = false := h
  simp only [TM2.stepAux, h', cond_false]
  obtain ⟨o, ho⟩ := stepAux_applyAll (List.finRange (R.tapes + 1)) (List.nodup_finRange _)
    (TM2.Stmt.load (fun v => { v with q := nextQ v }) (TM2.Stmt.goto fun _ => Lbl.sim))
    (scanV v Rs) [] [] [] Ls Rs
  refine ⟨o, ?_⟩
  rw [show ({ v with scanned := fun i => top (Rs i) } : Var R A τi τo) = scanV v Rs from rfl, ho]
  rfl

/-! ## Output phases -/

lemma gather_run (l : List (G R)) : ∀ (v : Var R A τi τo) (Ls Rs), Ls 0 = l →
    ∃ v' : Var R A τi τo, v'.qo = v.qo ∧
      Reaches R A τi τo (l.length + 1) ⟨some .gather, v, mkStk [] [] [] Ls Rs⟩
        ⟨some .seek, v', mkStk [] [] [] (Function.update Ls 0 [])
          (Function.update Rs 0 (l.reverse ++ Rs 0))⟩ := by
  induction l with
  | nil =>
    intro v Ls Rs hL
    refine ⟨{ v with cell := none }, rfl, reaches_one ?_⟩
    rw [stepF_some]
    have e1 : Function.update Ls 0 [] = Ls := by rw [← hL]; exact Function.update_eq_self _ _
    simp [prog, TM2.stepAux, hL, e1]
  | cons g l ih =>
    intro v Ls Rs hL
    obtain ⟨v', hqo, hr⟩ := ih { v with cell := some g } (Function.update Ls 0 l)
      (Function.update Rs 0 (g :: Rs 0)) (by simp)
    refine ⟨v', hqo, ?_⟩
    have hs : stepF R A τi τo ⟨some .gather, v, mkStk [] [] [] Ls Rs⟩ =
        some ⟨some .gather, { v with cell := some g },
          mkStk [] [] [] (Function.update Ls 0 l) (Function.update Rs 0 (g :: Rs 0))⟩ := by
      rw [stepF_some]
      simp [prog, TM2.stepAux, hL]
    have := reaches_succ hs hr
    simpa [Nat.add_comm] using this

lemma seek_run (pre : List (G R)) : ∀ (v : Var R A τi τo) (Ls Rs) (g : G R) (post : List (G R)),
    (∀ x ∈ pre, x.2 = false) → g.2 = true → Rs 0 = pre ++ g :: post →
    ∃ v' : Var R A τi τo, v'.qo = v.qo ∧ v'.cell = some g ∧
      Reaches R A τi τo (pre.length + 1) ⟨some .seek, v, mkStk [] [] [] Ls Rs⟩
        ⟨some .feed, v', mkStk [] [] [] Ls (Function.update Rs 0 post)⟩ := by
  induction pre with
  | nil =>
    intro v Ls Rs g post _ hg hR
    refine ⟨{ v with cell := some g }, rfl, rfl, reaches_one ?_⟩
    rw [stepF_some]
    simp [prog, TM2.stepAux, hR, hg]
  | cons x pre ih =>
    intro v Ls Rs g post hpre hg hR
    obtain ⟨v', hqo, hc, hr⟩ := ih { v with cell := some x } Ls
      (Function.update Rs 0 (pre ++ g :: post)) g post
      (fun y hy => hpre y (by simp [hy])) hg (by simp)
    refine ⟨v', hqo, hc, ?_⟩
    have hx : x.2 = false := hpre x (by simp)
    have hs : stepF R A τi τo ⟨some .seek, v, mkStk [] [] [] Ls Rs⟩ =
        some ⟨some .seek, { v with cell := some x },
          mkStk [] [] [] Ls (Function.update Rs 0 (pre ++ g :: post))⟩ := by
      rw [stepF_some]
      simp [prog, TM2.stepAux, hR, hx]
    have := reaches_succ hs hr
    simpa [Function.update_idem, Nat.add_comm] using this

variable (R) in
/-- The symbol at position `i` of the layout of `y` as an input. -/
def cellSym (y : List Bool) (i : ℕ) : Sym R := ((y[i]?).map (bitSym R)).getD 0

lemma val_one' : ((1 : Sym R) : ℕ) = 1 := Nat.mod_eq_of_lt (by omega)
lemma val_two' : ((2 : Sym R) : ℕ) = 2 := Nat.mod_eq_of_lt (by omega)

lemma bitSym_val (b : Bool) : (bitSym R b).val = if b then 2 else 1 := by
  cases b
  · exact val_one'
  · exact val_two'

@[simp] lemma isBit_bitSym (b : Bool) : isBit R (bitSym R b) = true := by
  cases b <;> simp [isBit, bitSym]

@[simp] lemma isBit_zero : isBit R 0 = false := by
  simp only [isBit, Bool.or_eq_false_iff, decide_eq_false_iff_not, Fin.ext_iff, val_one',
    val_two', Fin.val_zero]
  omega

@[simp] lemma bitSym_eq_two (b : Bool) : decide (bitSym R b = 2) = b := by
  have := bitSym_val (R := R) b
  cases b
  · simp only [decide_eq_false_iff_not, Fin.ext_iff, val_two']
    simp only [Bool.false_eq_true, if_false] at this
    omega
  · simp [bitSym]

lemma getD_head_tail (l : List (G R)) (i : ℕ) :
    ((l.head?.getD (g0 R)) :: l.tail).getD i (g0 R) = l.getD i (g0 R) := by
  cases l with
  | nil => cases i <;> simp
  | cons a l => rfl

lemma feed_run (y : List Bool) : ∀ (v : Var R A τi τo) (outR : List A) (Ls Rs),
    (∀ i : ℕ, ((v.cell.getD (g0 R) :: Rs 0).getD i (g0 R)).1 = cellSym R y i) →
    ∃ (v' : Var R A τi τo) (rest : List (G R)), rest.length ≤ (Rs 0).length ∧
      Reaches R A τi τo (y.length + 1) ⟨some .feed, v, mkStk [] outR [] Ls Rs⟩
        ⟨some .outRev, v', mkStk [] ((τo.run v.qo y).reverse ++ outR) [] Ls
          (Function.update Rs 0 rest)⟩ := by
  induction y with
  | nil =>
    intro v outR Ls Rs H
    refine ⟨v, Rs 0, le_rfl, reaches_one ?_⟩
    have h0 := H 0
    simp only [List.getD_cons_zero, cellSym, List.getElem?_nil, Option.map_none,
      Option.getD_none] at h0
    rw [stepF_some]
    simp [prog, TM2.stepAux, h0, OutTransducer.run]
  | cons b y ih =>
    intro v outR Ls Rs H
    have h0 := H 0
    simp only [List.getD_cons_zero, cellSym, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some] at h0
    set v₁ : Var R A τi τo :=
      { v with qo := (τo.δ v.qo b).1, cell := (Rs 0).head? } with hv₁
    have H₁ : ∀ i : ℕ, ((v₁.cell.getD (g0 R) :: (Function.update Rs 0 (Rs 0).tail) 0).getD i
        (g0 R)).1 = cellSym R y i := by
      intro i
      simp only [hv₁, Function.update_self]
      rw [getD_head_tail]
      have := H (i + 1)
      simpa [cellSym] using this
    obtain ⟨v', rest, hrest, hr⟩ := ih v₁ ((τo.δ v.qo b).2.toList ++ outR) Ls
      (Function.update Rs 0 (Rs 0).tail) H₁
    refine ⟨v', rest, ?_, ?_⟩
    · simp only [Function.update_self, List.length_tail] at hrest; omega
    have hs : stepF R A τi τo ⟨some .feed, v, mkStk [] outR [] Ls Rs⟩ =
        some ⟨some .feed, v₁, mkStk [] ((τo.δ v.qo b).2.toList ++ outR) [] Ls
          (Function.update Rs 0 (Rs 0).tail)⟩ := by
      rw [stepF_some]
      have hc : cellBit v = b := by simp [cellBit, h0]
      simp [prog, TM2.stepAux, h0, hc, hv₁]
      trace_state
      sorry
    have := reaches_succ hs hr
    have e : (τo.run v.qo (b :: y)).reverse ++ outR =
        (τo.run (τo.δ v.qo b).1 y).reverse ++ ((τo.δ v.qo b).2.toList ++ outR) := by
      cases (τo.δ v.qo b).2 <;> simp [OutTransducer.run]
    rw [e]
    simpa [Nat.add_comm, hv₁, Function.update_idem] using this

lemma outRev_run (l : List A) : ∀ (v : Var R A τi τo) (io : List A) (Ls Rs),
    ∃ v' : Var R A τi τo,
      Reaches R A τi τo (l.length + 1) ⟨some .outRev, v, mkStk io l [] Ls Rs⟩
        ⟨some .clear, v', mkStk (l.reverse ++ io) [] [] Ls Rs⟩ := by
  induction l with
  | nil =>
    intro v io Ls Rs
    refine ⟨{ v with outSym := none }, reaches_one ?_⟩
    rw [stepF_some]
    simp [prog, TM2.stepAux]
  | cons a l ih =>
    intro v io Ls Rs
    obtain ⟨v', hr⟩ := ih { v with outSym := some a } (a :: io) Ls Rs
    refine ⟨v', ?_⟩
    have hs : stepF R A τi τo ⟨some .outRev, v, mkStk io (a :: l) [] Ls Rs⟩ =
        some ⟨some .outRev, { v with outSym := some a }, mkStk (a :: io) l [] Ls Rs⟩ := by
      rw [stepF_some]
      simp [prog, TM2.stepAux]
    have := reaches_succ hs hr
    simpa [Nat.add_comm] using this

lemma step_clear (v : Var R A τi τo) (io : List A) (Ls Rs) :
    stepF R A τi τo ⟨some .clear, v, mkStk io [] [] Ls Rs⟩ =
      some ⟨some (if (List.finRange (R.tapes + 1)).any
          (fun j => !(Ls j).isEmpty || !(Rs j).isEmpty) then .clear else .done),
        { v with flag := (List.finRange (R.tapes + 1)).any
          (fun j => !(Ls j).isEmpty || !(Rs j).isEmpty) },
        mkStk io [] [] (fun i => (Ls i).tail) (fun i => (Rs i).tail)⟩ := by
  rw [stepF_some]
  simp only [prog, TM2.stepAux]
  rw [stepAux_popAll _ (List.nodup_finRange _)]
  simp only [List.mem_finRange, if_true, Bool.false_or]
  cases h : (List.finRange (R.tapes + 1)).any (fun j => !(Ls j).isEmpty || !(Rs j).isEmpty) <;>
    simp [TM2.stepAux, h]

lemma clear_run (io : List A) (m : ℕ) : ∀ (v : Var R A τi τo) (Ls Rs),
    (∀ j, (Ls j).length ≤ m ∧ (Rs j).length ≤ m) →
    ∃ n ≤ m + 1, ∃ v' : Var R A τi τo,
      Reaches R A τi τo n ⟨some .clear, v, mkStk io [] [] Ls Rs⟩
        ⟨some .done, v', mkStk io [] [] (fun _ => []) (fun _ => [])⟩ := by
  induction m with
  | zero =>
    intro v Ls Rs hm
    have hL : ∀ j, Ls j = [] := fun j => List.eq_nil_of_length_eq_zero (by have := (hm j).1; omega)
    have hR : ∀ j, Rs j = [] := fun j => List.eq_nil_of_length_eq_zero (by have := (hm j).2; omega)
    refine ⟨1, le_rfl, _, reaches_one ?_⟩
    rw [step_clear]
    simp [hL, hR]
    rfl
  | succ m ih =>
    intro v Ls Rs hm
    by_cases hany : (List.finRange (R.tapes + 1)).any
        (fun j => !(Ls j).isEmpty || !(Rs j).isEmpty) = true
    · obtain ⟨n, hn, v', hr⟩ := ih { v with flag := true } (fun i => (Ls i).tail)
        (fun i => (Rs i).tail) (fun j => by
          simp only [List.length_tail]; have := hm j; omega)
      refine ⟨n + 1, by omega, v', reaches_succ ?_ hr⟩
      rw [step_clear, hany]
      rfl
    · have hall : ∀ j, Ls j = [] ∧ Rs j = [] := by
        intro j
        simp only [List.any_eq_true, List.mem_finRange, true_and, not_exists, Bool.or_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, not_or,
          ne_eq, not_not] at hany
        simpa using hany j
      refine ⟨1, by omega, _, reaches_one ?_⟩
      rw [step_clear]
      simp only [Bool.not_eq_true] at hany
      rw [hany]
      simp only [hall, List.tail_nil]
      rfl

lemma step_done (v : Var R A τi τo) (S : ∀ k, List (Γ' R A k)) :
    stepF R A τi τo ⟨some .done, v, S⟩ = some ⟨none, Var.init R A τi τo, S⟩ := by
  rw [stepF_some]
  simp [prog, TM2.stepAux]

end Lax119563Proofs.Bridges.TM2Sim
