import Lax119563Proofs.Main.ComposeMain

/-!
# Composing two machines that compute functions

The composed machine of `Main.Compose` (simulate `R`, rewind tape `0`, simulate `D` on tape `0`)
also composes *computations*: if `R` computes `y` from `x` within `t₁` steps and `D` computes
`z` from `y` within `t₂` steps, the composed machine computes `z` from `x` within
`2 t₁ + t₂ + 3` steps (for `|x| ≥ 2`; **`compose_computesWithin`**). At the end of the
simulation of `D`, tape `0` of the composed machine is the embedded tape `0` of `D`, which is
the input layout of `z` in the alphabet of the composed machine.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction step run Deterministic)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Main.Compose

open AMachine

variable {R D : Machine} {a₀ : Bool} {a₁ : Bool → Bool}

/-- `ComputesWithin` is monotone in the time bound. -/
lemma computesWithin_mono' {M : Machine} {x y : List Bool} {t t' : ℕ}
    (h : ComputesWithin M x y t) (ht : t ≤ t') : ComputesWithin M x y t' := by
  have e : runOn M x t' = runOn M x t := runOn_eq_of_le M x ht h.1
  unfold ComputesWithin
  rw [e]; exact h

/-- **Composition of computations.** -/
theorem compose_computesWithin (R D : Machine) (a₀ : Bool) (a₁ : Bool → Bool)
    {x y z : List Bool} {t₁ t₂ : ℕ} (hx : 2 ≤ x.length)
    (hR : ComputesWithin R x y t₁) (hD : ComputesWithin D y z t₂) :
    ComputesWithin (comp R D a₀ a₁).toMachine x z (2 * t₁ + t₂ + 3) := by
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
  set T := 2 + t' + 1 + (d.head 0).natAbs + 1 + t₂ with hT
  have hrun : (comp R D a₀ a₁).run T (AMachine.init x) =
      (comp R D a₀ a₁).run t₂ ((comp R D a₀ a₁).step ((comp R D a₀ a₁).run (d.head 0).natAbs
        ((comp R D a₀ a₁).run (2 + t' + 1) (AMachine.init x)))) := by
    rw [hT, AMachine.run_add, AMachine.run_succ, AMachine.run_add]
  refine computesWithin_mono' (t := T) ⟨?_, ?_⟩ (by omega)
  · rw [AMachine.runOn_toMachine, hrun]
    have hans := hsimD.2.1
    change _ = (runOn D y t₂).answer at hans
    show ((comp R D a₀ a₁).run t₂ _).answer.isSome
    rw [hans]; exact hD.1
  · rw [AMachine.runOn_toMachine, hrun, AMachine.init_enc]
    have ht0 := (hsimD.2.2 0).2
    change _ = fun w => embD R D ((runOn D y t₂).tape 0 w) at ht0
    rw [hD.2, ← embR_init_eq_embD_init (R := R), ← init_tape_none_embR (R := R) (D := D)] at ht0
    show ((comp R D a₀ a₁).run t₂ _).tape ((eT (Tp R D)).symm 0) =
      (AMachine.init z : Cfg R D).tape ((eT (Tp R D)).symm 0)
    have h0 : (eT (Tp R D)).symm 0 = none := (eT_symm_eq_none_iff 0).mpr rfl
    rw [h0]
    exact ht0

end Lax119563Proofs.Main.Compose
