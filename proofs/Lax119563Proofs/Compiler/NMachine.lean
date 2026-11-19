import Lax119563Proofs.Compiler.NCompile
import Lax119563Proofs.Reduction.HMachine
import Lax119563Proofs.Circuits.MachineRun

/-!
# Machines computing the output of register programs with number stacks

Copy-generalised from `Reduction.HMachine`.

`NProg.machine p` runs the compiled program `p` and then moves the output to tape `0`
(popping the input tape once per output symbol, so that the head returns to cell `0` after
the output has been pushed). `NProg.computesWithin`: if `p` runs from the zero state to a
state with cursor `0` that has emitted `out`, with `|x| ≤ |encodeNats out|`, then the machine
computes `encodeNats out` from `x` within the cost of the run plus `O(|encodeNats out|)`.
-/

open Function Lax119563.BinaryEncodings Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Compiler

open Hierarchy Hierarchy.Prog Lax119563Proofs.Reduction Lax119563Proofs.Reduction.Prog

variable {R Q : ℕ}

/-- Move the reversed output from `t₀` to `t₁`, popping the input tape once per symbol. -/
def countLoopN : Hierarchy.Prog (R + Q + 7) 0 :=
  .loop (fun t => (t nT0).isSome) (.seq (moveOne nT0 nT1) (.pop nIo))

/-- The output phase. -/
def finalPN : Hierarchy.Prog (R + Q + 7) 0 :=
  .seq (moveAll nOut nT0) (.seq countLoopN (moveAll nT1 nIo))

/-- The machine of a register program. -/
noncomputable def NProg.machine (p : NProg R Q) : Machine :=
  Hierarchy.Prog.toMachine (K := R + Q + 6) (.seq (compileN p) finalPN) (fun _ => false)

lemma NProg.machine_deterministic (p : NProg R Q) : Deterministic p.machine :=
  Hierarchy.Prog.toMachine_deterministic _ _

lemma countLoopN_runsH : ∀ (l : List Sym) (S : Stacks (R + Q + 7) 0) (hd : Fin (R + Q + 7) → ℤ),
    S nT0 = l →
    ∃ hd' : Fin (R + Q + 7) → ℤ, hd' nIo = hd nIo + l.length ∧
      RunsLeH countLoopN (S, hd)
        (update (update (update S nT0 []) nT1 (l.reverse ++ S nT1)) nIo
          ((S nIo).drop l.length), hd') (7 * l.length + 1)
  | [], S, hd, hS => by
    refine ⟨hd, by simp, (RunsLeH.loopF (by simp [tops, hS])).of_eq ?_ (by simp)⟩
    refine Prod.ext ?_ rfl
    funext k; simp only [update_apply]; split_ifs <;> simp_all
  | a :: l, S, hd, hS => by
    have h01 : (nT0 : Fin (R + Q + 7)) ≠ nT1 := by ndist
    have h0i : (nT0 : Fin (R + Q + 7)) ≠ nIo := by ndist
    have h1i : (nT1 : Fin (R + Q + 7)) ≠ nIo := by ndist
    have r₁ := moveOne_runsH h01 (hd := hd) hS
    set S₁ := update (update S nT0 l) nT1 (a :: S nT1)
    set hd₁ := update (update hd nT0 (hd nT0 + 1)) nT1 (hd nT1 - 1)
    have r₂ : RunsLeH (.pop nIo) (S₁, hd₁)
        (update S₁ nIo (S₁ nIo).tail, update hd₁ nIo (hd₁ nIo + 1)) 1 := ⟨1, le_rfl, .pop⟩
    obtain ⟨hd', e', r₃⟩ := countLoopN_runsH l (update S₁ nIo (S₁ nIo).tail)
      (update hd₁ nIo (hd₁ nIo + 1)) (by simp [S₁, update_of_ne h0i, update_of_ne h01])
    refine ⟨hd', ?_, (RunsLeH.loopT (by simp [tops, hS]) (r₁.seq r₂) r₃).of_eq ?_ ?_⟩
    · rw [e']
      simp [hd₁, update_of_ne h0i.symm, update_of_ne h1i.symm]; ring
    · refine Prod.ext ?_ rfl
      have e1 : S₁ nIo = S nIo := by simp [S₁, update_of_ne h0i.symm, update_of_ne h1i.symm]
      funext k
      simp only [update_apply, S₁] at *
      split_ifs <;> simp_all [List.drop_tail]
    · simp; omega

lemma encN_init (x : List Bool) :
    encN x (⟨fun _ => 0, fun _ => [], 0, []⟩ : NSt R Q) = inputStacks (R + Q + 6) 0 x := by
  funext i
  unfold encN inputStacks
  by_cases h0 : i = 0
  · subst h0; simp [bs, sym, bitSym]
  · have : i.val ≠ 0 := fun e => h0 (Fin.ext e)
    simp [h0, this, encodeNats]

/-- **Machines of register programs.** -/
theorem NProg.computesWithin {p : NProg R Q} {x : List Bool} {w t : ℕ} {st' : NSt R Q}
    (h : NRuns x w p ⟨fun _ => 0, fun _ => [], 0, []⟩ st' t) (hpos : st'.pos = 0)
    (hlen : x.length ≤ (encodeNats st'.out).length) :
    ComputesWithin p.machine x (encodeNats st'.out)
      (t + 20 * (encodeNats st'.out).length + 4) := by
  set y := encodeNats st'.out
  obtain ⟨hd₁, e₁, r₁⟩ := compileN_runs h (by simp) (fun _ => 0) (by simp)
  rw [hpos] at e₁
  -- the output phase
  have hoi : (nOut : Fin (R + Q + 7)) ≠ nIo := by ndist
  have h0i : (nT0 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have h1i : (nT1 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have ho0 : (nOut : Fin (R + Q + 7)) ≠ nT0 := by ndist
  have ho1 : (nOut : Fin (R + Q + 7)) ≠ nT1 := by ndist
  have h01 : (nT0 : Fin (R + Q + 7)) ≠ nT1 := by ndist
  have a₁ := moveAll_runs ho0 (m := 0) ((bs y).reverse) (encN x st') (encN_out x st')
  obtain ⟨hd₂, e₂, r₂⟩ := RunsLe.toH a₁ (avoids_moveAll hoi h0i) hd₁
  set S₂ := update (update (encN x st') nOut []) nT0 ((bs y).reverse.reverse ++ encN x st' nT0)
  obtain ⟨hd₃, e₃, r₃⟩ := countLoopN_runsH (bs y) S₂ hd₂ (by simp [S₂])
  set S₃ := update (update (update S₂ nT0 []) nT1 ((bs y).reverse ++ S₂ nT1)) nIo
    ((S₂ nIo).drop (bs y).length)
  have r₄ := moveAll_runsH h1i (m := 0) ((bs y).reverse) S₃ hd₃
    (by simp [S₃, S₂, update_of_ne h1i, update_of_ne h01.symm, update_of_ne ho1.symm])
  have hrun := ((r₁.seq (r₂.seq (r₃.seq r₄))))
  obtain ⟨t₀, ht₀, hrunH⟩ := hrun
  rw [encN_init] at hrunH
  have hc := Prog.computesWithin (K := R + Q + 6) (ans := fun _ => false) (y := y) hrunH ?_ ?_
  · refine ComputesWithin.mono hc ?_
    simp only [length_bs, List.length_reverse] at ht₀
    omega
  · -- the input tape holds the output
    have hio : S₃ nIo = [] := by
      simp only [S₃, update_self, S₂, update_of_ne hoi.symm, update_of_ne h0i.symm,
        encN_io, hpos, List.drop_zero, length_bs]
      exact List.drop_eq_nil_of_le (by simpa using hlen)
    show update (update S₃ nT1 []) nIo ((bs y).reverse.reverse ++ S₃ nIo) nIo = _
    rw [update_self, hio, List.reverse_reverse, List.append_nil]
    rfl
  · show update (update hd₃ nT1 (hd₃ nT1 + _)) nIo (hd₃ nIo - _) nIo = 0
    rw [update_self, e₃, e₂, e₁]
    simp

end Lax119563Proofs.Compiler
