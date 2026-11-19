import Lax119563Proofs.Compiler.P4Edge

/-!
# Pass `P4`, schema part: generic tools

* `Good.loop_idx`: a loop that runs exactly `n` times, along a family of predicates
  `P j` (the state after `j` iterations), with per-iteration costs `C j`.
* Straight-line statements (`lf`: no loops, no `rst`) cost at most `scost c · nodeCost w`
  (`cost_le_scost`, `good_lf`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

namespace Good

lemma loop_idx_aux {e : Ex R} {body : CStm R Q} (n : ℕ) (P : ℕ → NSt R Q → Prop)
    (C : ℕ → ℕ)
    (hstep : ∀ j < n, ∀ s, P j s → e.Fits w s.env ∧ e.eval s.env ≠ 0 ∧
      ∃ s', Good x w body s s' (C j) ∧ P (j + 1) s')
    (hend : ∀ s, P n s → e.Fits w s.env ∧ e.eval s.env = 0) :
    ∀ d m, m + d = n → ∀ s, P m s → ∃ s', Good x w (.loop e body) s s'
      (∑ j ∈ Finset.range d, (C (m + j) + condCost w e) + condCost w e) ∧ P n s' := by
  intro d
  induction d with
  | zero =>
    intro m hm s hs
    rw [Nat.add_zero] at hm; subst hm
    obtain ⟨hf, h0⟩ := hend s hs
    exact ⟨s, (loop_stop hf h0).mono (by simp), hs⟩
  | succ d ih =>
    intro m hm s hs
    obtain ⟨hf, hc, s₁, h₁, hs₁⟩ := hstep m (by omega) s hs
    obtain ⟨s', h', hs'⟩ := ih (m + 1) (by omega) s₁ hs₁
    refine ⟨s', (loop_cons hf hc h₁ h').mono (le_of_eq ?_), hs'⟩
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    ring

/-- **Loops running exactly `n` times.** -/
lemma loop_idx {e : Ex R} {body : CStm R Q} (n : ℕ) (P : ℕ → NSt R Q → Prop) (C : ℕ → ℕ)
    (hstep : ∀ j < n, ∀ s, P j s → e.Fits w s.env ∧ e.eval s.env ≠ 0 ∧
      ∃ s', Good x w body s s' (C j) ∧ P (j + 1) s')
    (hend : ∀ s, P n s → e.Fits w s.env ∧ e.eval s.env = 0) (s : NSt R Q) (hs : P 0 s) :
    ∃ s', Good x w (.loop e body) s s'
      (∑ j ∈ Finset.range n, (C j + condCost w e) + condCost w e) ∧ P n s' := by
  obtain ⟨s', h, hP⟩ := loop_idx_aux n P C hstep hend n 0 (by omega) s hs
  exact ⟨s', h.mono (by simp), hP⟩

/-- **Loops running exactly `n` times**, uniform cost. -/
lemma loop_idxC {e : Ex R} {body : CStm R Q} (n : ℕ) (P : ℕ → NSt R Q → Prop) (C : ℕ)
    (hstep : ∀ j < n, ∀ s, P j s → e.Fits w s.env ∧ e.eval s.env ≠ 0 ∧
      ∃ s', Good x w body s s' C ∧ P (j + 1) s')
    (hend : ∀ s, P n s → e.Fits w s.env ∧ e.eval s.env = 0) (s : NSt R Q) (hs : P 0 s) :
    ∃ s', Good x w (.loop e body) s s' (n * (C + condCost w e) + condCost w e) ∧ P n s' := by
  obtain ⟨s', h, hP⟩ := loop_idx n P (fun _ => C) hstep hend s hs
  exact ⟨s', h.mono (by simp), hP⟩

end Good

/-! ## Straight-line statements -/

/-- No loops and no `rst`. -/
def lf : CStm R Q → Bool
  | rst => false
  | loop _ _ => false
  | seq p q => lf p && lf q
  | ite _ p q => lf p && lf q
  | _ => true

/-- A static cost bound in units of `nodeCost`. -/
def scost : CStm R Q → ℕ
  | skip => 1
  | set _ e => e.size + 1
  | emit e => e.size + 1
  | push _ e => e.size + 1
  | pop _ _ => 2
  | sne _ _ => 3
  | rd _ => 1
  | rst => 0
  | seq p q => scost p + scost q
  | ite c p q => c.size + 1 + max (scost p) (scost q)
  | loop _ _ => 0

lemma cost_le_scost : ∀ (c : CStm R Q) (st : NSt R Q), lf c = true →
    cost x w c st ≤ scost c * Ex.nodeCost w
  | skip, _, _ => by
    have := Ex.unitCost_le_nodeCost w; simp only [cost, scost]; omega
  | set _ e, _, _ => by
    have := Ex.unitCost_le_nodeCost w; simp only [cost, scost]; nlinarith
  | emit e, _, _ => by
    have := Ex.unitCost_le_nodeCost w; simp only [cost, scost]; nlinarith
  | push _ e, _, _ => by
    have := Ex.unitCost_le_nodeCost w; simp only [cost, scost]; nlinarith
  | pop _ _, _, _ => by
    have := Ex.unitCost_le_nodeCost w; have := unitCost_ge w
    simp only [cost, scost]; omega
  | sne _ _, _, _ => by
    have := Ex.unitCost_le_nodeCost w; have := unitCost_ge w
    have : 2 * unitCost w ≤ Ex.nodeCost w := by
      unfold Ex.nodeCost; nlinarith
    simp only [cost, scost]; omega
  | rd _, _, _ => by
    have := Ex.unitCost_le_nodeCost w; simp only [cost, scost]; omega
  | rst, _, h => by simp [lf] at h
  | loop _ _, _, h => by simp [lf] at h
  | seq p q, st, h => by
    simp only [lf, Bool.and_eq_true] at h
    have h1 := cost_le_scost p st h.1
    have h2 := cost_le_scost q (exec x p st) h.2
    simp only [cost, scost]; rw [add_mul]; omega
  | ite c p q, st, h => by
    simp only [lf, Bool.and_eq_true] at h
    have h1 := cost_le_scost p st h.1
    have h2 := cost_le_scost q st h.2
    have hU := Ex.unitCost_le_nodeCost w
    have hU' := unitCost_ge w
    have hp : scost p * Ex.nodeCost w ≤ max (scost p) (scost q) * Ex.nodeCost w :=
      Nat.mul_le_mul_right _ (le_max_left _ _)
    have hq : scost q * Ex.nodeCost w ≤ max (scost p) (scost q) * Ex.nodeCost w :=
      Nat.mul_le_mul_right _ (le_max_right _ _)
    simp only [cost, scost, condCost, add_mul]
    split_ifs <;> nlinarith

/-- **Straight-line statements.** -/
lemma good_lf {c : CStm R Q} {st : NSt R Q} (hlf : lf c = true) (hf : Fits x w c st) :
    Good x w c st (exec x c st) (scost c * Ex.nodeCost w) :=
  ⟨hf, rfl, cost_le_scost c st hlf⟩

end CStm

end Lax119563Proofs.Compiler
