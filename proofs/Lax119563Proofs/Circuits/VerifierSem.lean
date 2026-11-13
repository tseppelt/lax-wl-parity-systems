import Lax119563Proofs.Circuits.Verifier

/-!
# Meaning of the verifier's locations

`Sem L A` states what the configuration `(L, A)` asserts about the run: e.g. `cell d θ ν c`
at address `A` asserts that the cell at window position `cj d A` of tape `ν` of call
`cω d A` at the start of phase `θ` has value `c`. The program is shown to accept exactly the
configurations whose assertion is true (with `A < 2 ^ (H + 2)`). `rank` decreases along the
moves used in the completeness proof.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

section Defs

variable (M : Machine) (x : List Bool) (H : ℕ)

/-- The call encoded in the address `A` of a claim at depth `d`. -/
def cω (d A : ℕ) : ℕ := A / 2 ^ (H - d + 2)

/-- The window position encoded in the address `A` of a claim at depth `d`. -/
def cj (d A : ℕ) : ℕ := A % 2 ^ (H - d + 2)

/-- The claim `cell d θ ν c` at address `A`. -/
def semCell (d θ : ℕ) (ν : Tape M) (c : CellVal M) (A : ℕ) : Prop :=
  (θ = 1 → d < H) ∧ cellT M x H d (cω H d A) θ ν (cj H d A) = c

/-- The claim `state d θ p` at address `A`. -/
def semState (d θ : ℕ) (p : ExtState M) (A : ℕ) : Prop :=
  (θ = 1 → d < H) ∧ extT M x H d (cω H d A) θ = p

/-- The claim `headIn d θ ν u` at address `A`: the head lies at a window position that agrees
with `cj d A` except possibly in the lowest `u` bits. -/
def semHead (d θ : ℕ) (ν : Tape M) (u A : ℕ) : Prop :=
  u < H - d ∧ ∃ y < 2 ^ u, rel M x H d (cω H d A) θ ν = (cj H d (setBits A 0 u y) : ℤ)

/-- The meaning of a configuration of the verifier. -/
def Sem : Loc M H → ℕ → Prop
  | .accept, _ => True
  | .reject, _ => False
  | .query, _ => (cfgExt (runOn M x (2 ^ H))).2 = some true
  | .cell d θ ν c, A => semCell M x H d θ ν c A
  | .state d θ p, A => semState M x H d θ p A
  | .headIn d θ ν u, A => semHead M x H d θ ν u A
  | .headSet d θ ν β, A => d.val < H ∧
      semHead M x H d θ ν (bpos H d) (setBits A (bpos H d) 3 β)
  | .restore d θ ν c β, A => d.val < H ∧
      if sel β ≤ field A (bpos H d) 3 ∧ field A (bpos H d) 3 < sel β + 4 then
        semCell M x H (d + 1) 2 ν c
          (setBits A (bpos H d) 3 (4 * θ.val + (field A (bpos H d) 3 - sel β)))
      else semCell M x H d θ ν c A
  | .gather d θ ν c β, A => d.val < H ∧ field A (bpos H d) 3 / 4 = θ.val ∧
      semCell M x H d θ ν c (setBits A (bpos H d) 3 (sel β + field A (bpos H d) 3 % 4))
  | .baseCell ν ρ old k, A =>
      (∀ i : Tape M, k.val ≤ i.val →
        semCell M x H H 0 i (ρ.2.2 i, true) (setBits A 0 2 ((ρ.2.1 i).val + 1))) ∧
      semState M x H H 0 ρ.1 A ∧ semCell M x H H 0 ν old A
  | .baseState ρ k, A =>
      (∀ i : Tape M, k.val ≤ i.val →
        semCell M x H H 0 i (ρ.2.2 i, true) (setBits A 0 2 ((ρ.2.1 i).val + 1))) ∧
      semState M x H H 0 ρ.1 A
  | .setJ ν h c, A => semCell M x H H 0 ν c (setBits A 0 2 h)

/-- Level weights of the rank. -/
def wG : ℕ := M.tapes + 4
/-- Base level of the phase-zero claims. -/
def wP : ℕ := wG M * (H + 2)
/-- Spacing of the depths among the phase-zero claims. -/
def wQ : ℕ := H + 4
/-- Multiplier of the time in the rank. -/
def wK : ℕ := wP M H + 2 * (H + 1) * wQ H

/-- The rank of a configuration: the time it refers to, then a level. -/
def rank : Loc M H → ℕ → ℕ
  | .accept, _ => 0
  | .reject, _ => 0
  | .query, _ => (2 ^ H + 1) * wK M H
  | .cell d θ _ _, A => ptime H d (cω H d A) θ * wK M H +
      (if θ.val = 0 then wP M H + 2 * d * wQ H else wG M * (H - d) + wG M - 1)
  | .state d θ _, A => ptime H d (cω H d A) θ * wK M H +
      (if θ.val = 0 then wP M H + 2 * d * wQ H else wG M * (H - d) + wG M - 1)
  | .headIn d θ _ u, A => ptime H d (cω H d A) θ * wK M H + wP M H + 2 * d * wQ H + 1 + u
  | .headSet d θ _ _, A => ptime H d (cω H d A) θ * wK M H + wP M H + 2 * d * wQ H + H + 2
  | .gather d θ _ _ _, A => ptime H d (cω H d A) θ * wK M H + wP M H + 2 * d * wQ H + H + 2
  | .restore d θ _ _ _, A => ptime H d (cω H d A) (θ + 1) * wK M H +
      (wG M * (H - d) + wG M - 2)
  | .baseCell _ _ _ k, A => ptime H H (cω H H A) 2 * wK M H + (M.tapes + 2 - k)
  | .baseState _ k, A => ptime H H (cω H H A) 2 * wK M H + (M.tapes + 2 - k)
  | .setJ _ _ _, A => ptime H H (cω H H A) 2 * wK M H

end Defs

/-! ## Address arithmetic -/

section Arith

variable {H : ℕ}

lemma cω_lt {d A : ℕ} (hd : d ≤ H) (hA : A < 2 ^ (H + 2)) : cω H d A < 2 ^ d := by
  unfold cω
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  rwa [show d + (H - d + 2) = H + 2 by omega]

lemma cω_setBits {d A k m v : ℕ} (hv : v < 2 ^ m) (h : k + m ≤ H - d + 2) :
    cω H d (setBits A k m v) = cω H d A :=
  setBits_div_of_le hv h

lemma bpos_add_three {d : ℕ} (hd : d < H) : H - d + 2 = bpos H d + 3 := by
  unfold bpos; omega

lemma bpos_add_two {d : ℕ} (_hd : d < H) : H - (d + 1) + 2 = bpos H d + 2 := by
  unfold bpos; omega

lemma bsz_eq_bpos (d : ℕ) : bsz H d = 2 ^ bpos H d := rfl

lemma cj_eq {d : ℕ} (hd : d < H) (A : ℕ) :
    cj H d A = field A (bpos H d) 3 * 2 ^ bpos H d + A % 2 ^ bpos H d := by
  unfold cj
  rw [bpos_add_three hd, show bpos H d + 3 = bpos H d + 3 by rfl, mod_eq_field_add]

lemma cω_child {d : ℕ} (hd : d < H) (A : ℕ) :
    cω H (d + 1) A = 2 * cω H d A + field A (bpos H d) 3 / 4 := by
  unfold cω
  rw [bpos_add_two hd, bpos_add_three hd]
  exact (split_field3 A _).1

lemma cj_child {d : ℕ} (hd : d < H) (A : ℕ) :
    cj H (d + 1) A = field A (bpos H d) 3 % 4 * 2 ^ bpos H d + A % 2 ^ bpos H d := by
  unfold cj
  rw [bpos_add_two hd]
  exact (split_field3 A _).2

lemma field_top_bit (A k : ℕ) : field A (k + 2) 1 = field A k 3 / 4 := by
  unfold field
  rw [show (2 : ℕ) ^ 3 = 4 * 2 by norm_num, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul]
  rw [pow_add]; norm_num

lemma setBits_self {A k m q : ℕ} (h : field A k m = q) : setBits A k m q = A := by
  rw [setBits, h, Nat.xor_self, Nat.zero_shiftLeft, Nat.xor_zero]

lemma cj_setBits_low {d : ℕ} (hd : d < H) {A' y : ℕ} (hy : y < 2 ^ bpos H d) :
    cj H d (setBits A' 0 (bpos H d) y) = field A' (bpos H d) 3 * 2 ^ bpos H d + y := by
  rw [cj_eq hd, field_setBits_of_disjoint hy (Or.inr (by simp)), ← field_zero_eq_mod,
    field_setBits hy]

/-- Merging a bit replacement into a low-bits replacement. -/
lemma setBits_merge {A n e y : ℕ} (he : e < 2 ^ 1) (hy : y < 2 ^ n) :
    setBits (setBits A n 1 e) 0 n y = setBits A 0 (n + 1) (setBits y n 1 e) := by
  have hy' : setBits y n 1 e < 2 ^ (n + 1) :=
    setBits_lt he (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega))) le_rfl
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_setBits hy, testBit_setBits hy', testBit_setBits he]
  by_cases h1 : i < n
  · rw [if_pos (by omega), if_pos (by omega), testBit_setBits he, if_neg (by omega)]
  · by_cases h2 : i = n
    · subst h2
      rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), testBit_setBits he,
        if_pos (by omega)]
      simp
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Splitting a low-bits value into its top bit and the rest. -/
lemma split_low {n y : ℕ} (hy : y < 2 ^ (n + 1)) :
    setBits (y % 2 ^ n) n 1 (field y n 1) = y := by
  have hf : field y n 1 < 2 ^ 1 := field_lt _ _ _
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_setBits hf]
  split_ifs with h
  · rw [testBit_field, show i - n = 0 by omega]
    simp [show 0 + n = i by omega]
  · rw [Nat.testBit_mod_two_pow]
    by_cases h' : i < n
    · simp [h']
    · simp only [h', decide_false, Bool.false_and]
      exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy
        (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

end Arith

end Lax119563Proofs.Circuits
