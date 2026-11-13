import Lax119563Proofs.Reduction.HCompile
import Lax119563Proofs.Circuits.MachineRun

/-!
# Machines computing the output of register programs

`HProg.machine p` runs the compiled program `p` and then moves the output to tape `0`
(popping the input tape once per output symbol, so that the head returns to cell `0` after
the output has been pushed). `HProg.computesWithin`: if `p` runs from the zero state to a
state with cursor `0` that has emitted `out`, with `|x| ≤ |encodeNats out|`, then the machine
computes `encodeNats out` from `x` within the cost of the run plus `O(|encodeNats out|)`.
-/

open Function Lax119563.BinaryEncodings Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Reduction

open Hierarchy Hierarchy.Prog Prog

variable {R : ℕ}

/-- Move the reversed output from `t₀` to `t₁`, popping the input tape once per symbol. -/
def countLoop : Hierarchy.Prog (R + 7) 0 :=
  .loop (fun t => (t sT0).isSome) (.seq (moveOne sT0 sT1) (.pop sIo))

/-- The output phase. -/
def finalP : Hierarchy.Prog (R + 7) 0 :=
  .seq (moveAll sOut sT0) (.seq countLoop (moveAll sT1 sIo))

/-- The machine of a register program. -/
noncomputable def HProg.machine (p : HProg R) : Machine :=
  Hierarchy.Prog.toMachine (K := R + 6) (.seq (compileH p) finalP) (fun _ => false)

lemma HProg.machine_deterministic (p : HProg R) : Deterministic p.machine :=
  Hierarchy.Prog.toMachine_deterministic _ _

lemma countLoop_runsH : ∀ (l : List Sym) (S : Stacks (R + 7) 0) (hd : Fin (R + 7) → ℤ),
    S sT0 = l →
    ∃ hd' : Fin (R + 7) → ℤ, hd' sIo = hd sIo + l.length ∧
      RunsLeH countLoop (S, hd)
        (update (update (update S sT0 []) sT1 (l.reverse ++ S sT1)) sIo
          ((S sIo).drop l.length), hd') (7 * l.length + 1)
  | [], S, hd, hS => by
    refine ⟨hd, by simp, (RunsLeH.loopF (by simp [tops, hS])).of_eq ?_ (by simp)⟩
    refine Prod.ext ?_ rfl
    funext k; simp only [update_apply]; split_ifs <;> simp_all
  | a :: l, S, hd, hS => by
    have h01 : (sT0 : Fin (R + 7)) ≠ sT1 := by dist
    have h0i : (sT0 : Fin (R + 7)) ≠ sIo := by dist
    have h1i : (sT1 : Fin (R + 7)) ≠ sIo := by dist
    have r₁ := moveOne_runsH h01 (hd := hd) hS
    set S₁ := update (update S sT0 l) sT1 (a :: S sT1)
    set hd₁ := update (update hd sT0 (hd sT0 + 1)) sT1 (hd sT1 - 1)
    have r₂ : RunsLeH (.pop sIo) (S₁, hd₁)
        (update S₁ sIo (S₁ sIo).tail, update hd₁ sIo (hd₁ sIo + 1)) 1 := ⟨1, le_rfl, .pop⟩
    obtain ⟨hd', e', r₃⟩ := countLoop_runsH l (update S₁ sIo (S₁ sIo).tail)
      (update hd₁ sIo (hd₁ sIo + 1)) (by simp [S₁, update_of_ne h0i, update_of_ne h01])
    refine ⟨hd', ?_, (RunsLeH.loopT (by simp [tops, hS]) (r₁.seq r₂) r₃).of_eq ?_ ?_⟩
    · rw [e']
      simp [hd₁, update_of_ne h0i.symm, update_of_ne h1i.symm]; ring
    · refine Prod.ext ?_ rfl
      have e1 : S₁ sIo = S sIo := by simp [S₁, update_of_ne h0i.symm, update_of_ne h1i.symm]
      funext k
      simp only [update_apply, S₁] at *
      split_ifs <;> simp_all [List.drop_tail]
    · simp; omega

lemma enc_init (x : List Bool) :
    enc x (⟨fun _ => 0, 0, []⟩ : HSt R) = inputStacks (R + 6) 0 x := by
  funext i
  unfold enc inputStacks
  by_cases h0 : i = 0
  · subst h0; simp [bs, sym, bitSym]
  · have : i.val ≠ 0 := fun e => h0 (Fin.ext e)
    simp [h0, this, encodeNats]

lemma ComputesWithin.mono {M : Machine} {x y : List Bool} {t t' : ℕ}
    (h : ComputesWithin M x y t) (ht : t ≤ t') : ComputesWithin M x y t' := by
  have e := Circuits.runOn_halted (M := M) x h.1 (t' - t)
  rw [Nat.add_sub_cancel' ht] at e
  unfold ComputesWithin
  rw [e]; exact h

/-- **Machines of register programs.** -/
theorem HProg.computesWithin {p : HProg R} {x : List Bool} {w t : ℕ} {st' : HSt R}
    (h : HRuns x w p ⟨fun _ => 0, 0, []⟩ st' t) (hpos : st'.pos = 0)
    (hlen : x.length ≤ (encodeNats st'.out).length) :
    ComputesWithin p.machine x (encodeNats st'.out)
      (t + 20 * (encodeNats st'.out).length + 4) := by
  set y := encodeNats st'.out
  obtain ⟨hd₁, e₁, r₁⟩ := compileH_runs h (by simp) (fun _ => 0) (by simp)
  rw [hpos] at e₁
  -- the output phase
  have hoi : (sOut : Fin (R + 7)) ≠ sIo := by dist
  have h0i : (sT0 : Fin (R + 7)) ≠ sIo := by dist
  have h1i : (sT1 : Fin (R + 7)) ≠ sIo := by dist
  have ho0 : (sOut : Fin (R + 7)) ≠ sT0 := by dist
  have ho1 : (sOut : Fin (R + 7)) ≠ sT1 := by dist
  have h01 : (sT0 : Fin (R + 7)) ≠ sT1 := by dist
  have a₁ := moveAll_runs ho0 (m := 0) ((bs y).reverse) (enc x st') (enc_out x st')
  obtain ⟨hd₂, e₂, r₂⟩ := RunsLe.toH a₁ (avoids_moveAll hoi h0i) hd₁
  set S₂ := update (update (enc x st') sOut []) sT0 ((bs y).reverse.reverse ++ enc x st' sT0)
  obtain ⟨hd₃, e₃, r₃⟩ := countLoop_runsH (bs y) S₂ hd₂ (by simp [S₂])
  set S₃ := update (update (update S₂ sT0 []) sT1 ((bs y).reverse ++ S₂ sT1)) sIo
    ((S₂ sIo).drop (bs y).length)
  have r₄ := moveAll_runsH h1i (m := 0) ((bs y).reverse) S₃ hd₃
    (by simp [S₃, S₂, update_of_ne h1i, update_of_ne h01.symm, update_of_ne ho1.symm])
  have hrun := ((r₁.seq (r₂.seq (r₃.seq r₄))))
  obtain ⟨t₀, ht₀, hrunH⟩ := hrun
  rw [enc_init] at hrunH
  have hc := Prog.computesWithin (K := R + 6) (ans := fun _ => false) (y := y) hrunH ?_ ?_
  · refine ComputesWithin.mono hc ?_
    simp only [length_bs, List.length_reverse] at ht₀
    omega
  · -- the input tape holds the output
    have hio : S₃ sIo = [] := by
      simp only [S₃, update_self, S₂, update_of_ne hoi.symm, update_of_ne h0i.symm,
        enc_io, hpos, List.drop_zero, length_bs]
      exact List.drop_eq_nil_of_le (by simpa using hlen)
    show update (update S₃ sT1 []) sIo ((bs y).reverse.reverse ++ S₃ sIo) sIo = _
    rw [update_self, hio, List.reverse_reverse, List.append_nil]
    rfl
  · show update (update hd₃ sT1 (hd₃ sT1 + _)) sIo (hd₃ sIo - _) sIo = 0
    rw [update_self, e₃, e₂, e₁]
    simp

end Lax119563Proofs.Reduction
