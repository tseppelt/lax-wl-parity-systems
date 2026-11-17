import Lax119563Proofs.Reduction.SchemaParts

/-!
# Numeric descriptions of the schemas of compiled address programs

For a guard `g` of an address program and a register program command compiled from it:
* `mem_guardDomain_toGuard`: `(i, b) ∈ guardDomain (toGuard g) act` iff `act` for the
  checksum block `i = s`, and `g i (regVal b)` for `i < s`;
* `updatePerm_toUpdate_apply`: the permutation `updatePerm (toUpdate m)` keeps the block and
  XORs the value `regVal b` with `field m (i ℓ) ℓ` on block `i < s`, and with the XOR of all
  these fields on the checksum block (`regVal_shift`);
* the schemas of the commands: `commandSchemas_assign`, `commandSchemas_fork`.
-/

open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Circuits

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ}

lemma mem_guardDomain_last (g : Guard s ℓ) (act : Bool) (b : BlockCoord ℓ) :
    ((Fin.last s, b) : Coord (s + 1) ℓ) ∈ guardDomain g act ↔ act = true := by
  simp [guardDomain]

lemma mem_guardDomain_castSucc (g : Guard s ℓ) (act : Bool) (i : Fin s) (b : BlockCoord ℓ) :
    ((i.castSucc, b) : Coord (s + 1) ℓ) ∈ guardDomain g act ↔ b ∈ g.sets i := by
  simp [guardDomain]

lemma mem_toGuard (g : Fin s → ℕ → Bool) (i : Fin s) (b : BlockCoord ℓ) :
    b ∈ (toGuard g : Guard s ℓ).sets i ↔ g i (regVal b) = true := by
  simp [toGuard]

/-- Domain membership for a compiled address guard, by the block number. -/
lemma mem_guardDomain_toGuard (g : Fin s → ℕ → Bool) (act : Bool) (c : Coord (s + 1) ℓ) :
    c ∈ guardDomain (toGuard g : Guard s ℓ) act ↔
      if h : c.1.val < s then g ⟨c.1.val, h⟩ (regVal c.2) = true else act = true := by
  obtain ⟨i, b⟩ := c
  induction i using Fin.lastCases with
  | last => simp [mem_guardDomain_last]
  | cast i =>
    rw [mem_guardDomain_castSucc, mem_toGuard]
    simp

/-! ## The shift of an update -/

lemma regVal_add (b c : BlockCoord ℓ) : regVal (b + c) = regVal b ^^^ regVal c := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_xor]
  simp only [regVal, testBit_ofBits]
  by_cases ht : t < ℓ
  · simp only [ht, decide_true, Bool.true_and, dif_pos, Pi.add_apply]
    rw [zmod2_add_eq_one]
  · simp [ht]

lemma regVal_ofAddr (m : ℕ) (i : Fin s) :
    regVal ((ofAddr m : Fin s → Fin ℓ → ZMod 2) i) = field m (i * ℓ) ℓ := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_field]
  simp only [regVal, testBit_ofBits, ofAddr]
  by_cases ht : t < ℓ
  · simp only [ht, decide_true, Bool.true_and, dif_pos]
    rw [Nat.add_comm t]
    split_ifs <;> simp_all
  · simp [ht]

/-- The XOR of the register fields of a mask: the shift of the checksum block. -/
def xorFields (ℓ : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | s + 1, m => xorFields ℓ s m ^^^ field m (s * ℓ) ℓ

lemma regVal_sum_ofAddr (m : ℕ) : ∀ s : ℕ,
    regVal (∑ i, (ofAddr m : Fin s → Fin ℓ → ZMod 2) i) = xorFields ℓ s m
  | 0 => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty, xorFields]
    apply Nat.eq_of_testBit_eq; intro t
    simp [regVal, testBit_ofBits]
  | s + 1 => by
    have e1 : (∑ i : Fin s, (ofAddr m : Fin (s + 1) → Fin ℓ → ZMod 2) i.castSucc) =
        ∑ i : Fin s, (ofAddr m : Fin s → Fin ℓ → ZMod 2) i :=
      Finset.sum_congr rfl fun i _ => by funext k; simp [ofAddr]
    have e2 : regVal ((ofAddr m : Fin (s + 1) → Fin ℓ → ZMod 2) (Fin.last s)) =
        field m (s * ℓ) ℓ := by rw [regVal_ofAddr]; simp
    rw [Fin.sum_univ_castSucc, regVal_add, e1, regVal_sum_ofAddr m s, e2, xorFields]

/-- The shift of block `i` under the update XOR-ing with `m`. -/
def shiftVal (s ℓ m : ℕ) (i : ℕ) : ℕ := if i < s then field m (i * ℓ) ℓ else xorFields ℓ s m

lemma updatePerm_toUpdate_apply (m : ℕ) (c : Coord (s + 1) ℓ) :
    ((updatePerm (toUpdate m : Update s ℓ)).apply c).1 = c.1 ∧
      regVal ((updatePerm (toUpdate m : Update s ℓ)).apply c).2 =
        regVal c.2 ^^^ shiftVal s ℓ m c.1.val := by
  obtain ⟨i, b⟩ := c
  induction i using Fin.lastCases with
  | last =>
    refine ⟨by
      simp only [BlockPerm.apply, updatePerm, toUpdate]
      rw [Equiv.symm_apply_eq]; simp, ?_⟩
    simp only [BlockPerm.apply, updatePerm, toUpdate, Fin.lastCases_last]
    rw [regVal_add, regVal_sum_ofAddr]
    simp [shiftVal]
  | cast i =>
    refine ⟨by
      simp only [BlockPerm.apply, updatePerm, toUpdate]
      rw [Equiv.symm_apply_eq]; simp, ?_⟩
    simp only [BlockPerm.apply, updatePerm, toUpdate, Fin.lastCases_castSucc]
    rw [regVal_add]
    show regVal b ^^^ regVal ((ofAddr m : Fin s → Fin ℓ → ZMod 2) i) = _
    simp [shiftVal, regVal_ofAddr]

/-! ## The schemas of compiled commands -/

section Commands

variable {L : Type} {N : ℕ} (code : L → Fin N) (acc rej : L) (hne : code acc ≠ code rej)
  (cmds : List (ACmd L s))

/-- The register program compiled from an address program. -/
abbrev AP : RegisterProgram s ℓ := compile N code acc rej hne cmds

lemma AP_commands : (AP (ℓ := ℓ) code acc rej hne cmds).commands = cmds.map (ACmd.toCmd code) :=
  rfl

lemma commandSchemas_assign (j : Fin (AP (ℓ := ℓ) code acc rej hne cmds).commands.length)
    (p : L) (g : Fin s → ℕ → Bool) (m : ℕ) (q : L) :
    (AP (ℓ := ℓ) code acc rej hne cmds).commandSchemas j ((ACmd.assign p g m q).toCmd code) =
      let R := AP (ℓ := ℓ) code acc rej hne cmds
      gadget (R.loc (.prog (code q))) (updatePerm (toUpdate m)) (R.loc (.slot j .a1))
        (R.loc (.slot j .b1)) (R.loc (.slot j .z1)) (R.loc (.prog (code p)))
        (guardDomain (toGuard g) (R.executable (code p))) := rfl

lemma commandSchemas_fork (j : Fin (AP (ℓ := ℓ) code acc rej hne cmds).commands.length)
    (p : L) (g : Fin s → ℕ → Bool) (q r : L) :
    (AP (ℓ := ℓ) code acc rej hne cmds).commandSchemas j ((ACmd.fork p g q r).toCmd code) =
      let R := AP (ℓ := ℓ) code acc rej hne cmds
      gadget (R.loc (.prog (code q))) (idPerm s ℓ) (R.loc (.slot j .a1)) (R.loc (.slot j .b1))
        (R.loc (.slot j .z1)) (R.loc (.slot j .out1)) (guardDomain (toGuard g) (R.executable (code p))) ++
      gadget (R.loc (.prog (code r))) (idPerm s ℓ) (R.loc (.slot j .a2)) (R.loc (.slot j .b2))
        (R.loc (.slot j .z2)) (R.loc (.slot j .out2)) (guardDomain (toGuard g) (R.executable (code p))) ++
      [.ternary (R.loc (.slot j .out1)) (R.loc (.slot j .out2)) (R.loc (.prog (code p)))
        (guardDomain (toGuard g) (R.executable (code p))) (idPerm s ℓ) (idPerm s ℓ) (idPerm s ℓ)] :=
  rfl

lemma loc_prog_val (p : Fin (AP (ℓ := ℓ) code acc rej hne cmds).numLocations) :
    ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.prog p)).val = p.val := by
  simp [RegisterProgram.loc, Role.equivFin, Role.toSum, finSumFinEquiv]

end Commands

end Lax119563Proofs.Reduction
