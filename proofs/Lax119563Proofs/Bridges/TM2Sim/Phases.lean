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

end Lax119563Proofs.Bridges.TM2Sim
