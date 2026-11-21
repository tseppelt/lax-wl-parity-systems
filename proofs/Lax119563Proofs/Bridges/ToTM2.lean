import Lax119563.MachineTranslations
import Lax119563Proofs.Machines.Part1

/-!
# Polynomial-time multitape machines give polynomial-time mathlib stack machines

For binary words both transducers of the stack-machine simulation (`Bridges/TM2Sim`) are the
identity. A deterministic multitape machine computing `f` within `C |x|^d + C` steps is then
simulated by the stack machine `tm R idIn idOut` within `30 (|x| + C |x|^d + C) + 30` steps,
which gives `Turing.TM2ComputableInPolyTime id id f`.
-/

open Lax489179.TuringMachine (Machine Deterministic)
open Lax119563.DeterministicTime
open Turing

namespace Lax119563Proofs.Bridges

open TM2Sim

/-- The identity input transducer on bits. -/
def idIn : InTransducer Bool where
  Q := Unit
  start := ()
  δ _ b := ((), [b])
  final _ := []
  δ_len _ _ := by simp
  final_len _ := by simp

/-- The identity output transducer on bits. -/
def idOut : OutTransducer Bool where
  Q := Unit
  start := ()
  δ _ b := ((), some b)

lemma idIn_run (u : List Bool) : idIn.run () u = u := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    show [a] ++ idIn.run () u = a :: u
    rw [ih]; rfl

lemma idOut_run (y : List Bool) : idOut.run () y = y := by
  induction y with
  | nil => rfl
  | cons a y ih =>
    show [a] ++ idOut.run () y = a :: y
    rw [ih]; rfl

/-- Raising the time bound of `EvalsToInTime`. -/
def evalsToInTime_mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : StateTransition.EvalsToInTime f a b m) (hm : m ≤ m') :
    StateTransition.EvalsToInTime f a b m' :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hm⟩

/--
---
conclusion: Lax119563.MachineTranslations.tm2_of_polyTime
---
The stack machine `tm R idIn idOut` simulates `R` (`TM2Sim.simulate`) within
`30 (|x| + T) + 30` steps for `T = C (|x| + 1)^d`, a polynomial in `|x|`.
-/
theorem tm2_of_polyTime {f : List Bool → List Bool} (R : Machine) (_hR : Deterministic R)
    (C d : ℕ) (hf : ∀ x, ComputesWithin R x (f x) (C * (x.length + 1) ^ d)) :
    Nonempty (TM2ComputableInPolyTime id id f) := by
  refine ⟨{
    tm := tm R idIn idOut
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := 30 * (Polynomial.X + Polynomial.C C * (Polynomial.X + 1) ^ d) + 30
    outputsFun := fun x => ?_ }⟩
  have hx : ComputesWithin R (idIn.run idIn.start x) (f x) (C * (x.length + 1) ^ d) := by
    rw [show idIn.start = () from rfl, idIn_run]; exact hf x
  have h := Classical.choice (simulate (τo := idOut) x (f x) _ hx)
  rw [show idOut.start = () from rfl, idOut_run] at h
  have hle : 30 * (x.length + (C * (x.length + 1) ^ d)) + 30 ≤ Polynomial.eval x.length
      (30 * (Polynomial.X + Polynomial.C C * (Polynomial.X + 1) ^ d) + 30) := by
    simp
  have h' := evalsToInTime_mono h hle
  have e : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => List.map_id l
  have key : ∀ a b : List Bool, a = x → b = f x →
      TM2OutputsInTime (tm R idIn idOut) a (some b) (Polynomial.eval x.length
        (30 * (Polynomial.X + Polynomial.C C * (Polynomial.X + 1) ^ d) + 30)) := by
    rintro a b rfl rfl; exact h'
  exact key _ _ (e x) (e (f x))

end Lax119563Proofs.Bridges
