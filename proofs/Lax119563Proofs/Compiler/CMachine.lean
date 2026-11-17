import Lax119563Proofs.Compiler.CStm
import Lax119563Proofs.Compiler.NOutput

/-!
# Machines of structured statements

`CStm.computesWithin`: the machine of the compiled statement computes the encoding of the
emitted list of the denotation from the zero state, within the cost bound plus
`O(|x| + |output|)`.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime Lax119563Proofs.Reduction
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ}

/-- The zero state. -/
def NSt.zero (R Q : ℕ) : NSt R Q := ⟨fun _ => 0, fun _ => [], 0, []⟩

/-- The machine of a statement compiled with `D + 1` scratch registers. -/
noncomputable def CStm.machine (D : ℕ) (c : CStm R Q) : Machine := (CStm.code R D c).machineO

lemma CStm.machine_deterministic (D : ℕ) (c : CStm R Q) : Deterministic (c.machine D) :=
  NProg.machineO_deterministic _

/-- **Machines of structured statements.** -/
theorem CStm.computesWithin {D : ℕ} {c : CStm R Q} {x : List Bool} {w : ℕ} (hw : 2 ≤ w)
    (hd : c.depth ≤ D) (hf : c.Fits x w (NSt.zero R Q)) :
    ComputesWithin (c.machine D) x (encodeNats (c.exec x (NSt.zero R Q)).out)
      (c.cost x w (NSt.zero R Q) +
        20 * (x.length + (encodeNats (c.exec x (NSt.zero R Q)).out).length) + 10) := by
  have hb : (NSt.zero (R + D + 1) Q).Bdd w :=
    ⟨fun _ => by simp [NSt.zero], fun _ v hv => by simp [NSt.zero] at hv⟩
  obtain ⟨st', ⟨t, ht, hr⟩, hc⟩ := CStm.code_spec (D := D) hw c (NSt.zero R Q)
    (NSt.zero (R + D + 1) Q) hd hf ⟨rfl, rfl, rfl, rfl⟩ hb (Nat.zero_le _)
  have h := NProg.computesWithinO hr
  rw [hc.2.2.2] at h
  exact ComputesWithin.mono h (by omega)

end Lax119563Proofs.Compiler
