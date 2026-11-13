import Lax119563Proofs.Circuits.VerifierSem

/-!
# Semantic rules of the verifier

The rules of `Windows` restated in terms of addresses: guessing the head block, restoring
after a phase, gathering the input of a child, moving state claims up and down the tree,
base calls, and the root input tests.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

variable {M : Machine} {x : List Bool} {H : ℕ}

/-- The guessed head block `β` is correct iff the head test at block `β` holds. -/
lemma headBlock_iff {d θ A β : ℕ} (hd : d < H) (hA : A < 2 ^ (H + 2)) (hθ : θ < 2)
    (hβ : β < 2 ^ 3) (ν : Tape M) :
    semHead M x H d θ ν (bpos H d) (setBits A (bpos H d) 3 β) ↔
      blk M x H d (cω H d A) θ ν = β := by
  have hω : cω H d (setBits A (bpos H d) 3 β) = cω H d A :=
    cω_setBits hβ (by rw [bpos_add_three hd])
  have hB : (bsz H d : ℤ) = 2 ^ bpos H d := by rw [bsz_eq_bpos]; push_cast; rfl
  unfold semHead
  rw [hω]
  constructor
  · rintro ⟨-, y, hy, hrel⟩
    rw [cj_setBits_low hd hy, field_setBits hβ] at hrel
    apply blk_eq
    · rw [hrel, hB]; push_cast; linarith
    · rw [hrel, hB]; push_cast
      have : (y : ℤ) < 2 ^ bpos H d := by exact_mod_cast hy
      linarith
  · intro hblk
    obtain ⟨-, -, e1, e2, -⟩ := phase_facts (x := x) hd hθ ν
      (rel_mem d hd.le _ (cω_lt hd.le hA) ν)
    rw [hblk, hB] at e1 e2
    refine ⟨by unfold bpos; omega, (rel M x H d (cω H d A) θ ν - β * 2 ^ bpos H d).toNat, ?_, ?_⟩
    · have : rel M x H d (cω H d A) θ ν - β * 2 ^ bpos H d < 2 ^ bpos H d := by linarith
      have h2 : ((2 ^ bpos H d : ℕ) : ℤ) = 2 ^ bpos H d := by push_cast; rfl
      omega
    · rw [cj_setBits_low hd, field_setBits hβ]
      · push_cast
        rw [Int.toNat_of_nonneg (by linarith)]
        ring
      · have : rel M x H d (cω H d A) θ ν - β * 2 ^ bpos H d < 2 ^ bpos H d := by linarith
        have h2 : ((2 ^ bpos H d : ℕ) : ℤ) = 2 ^ bpos H d := by push_cast; rfl
        omega

lemma cj_div_bsz {d A : ℕ} (hd : d < H) : cj H d A / bsz H d = field A (bpos H d) 3 := by
  rw [cj_eq hd, bsz_eq_bpos, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity)), zero_add]

lemma cj_mod_bsz {d A : ℕ} (hd : d < H) : cj H d A % bsz H d = A % 2 ^ bpos H d := by
  rw [cj_eq hd, bsz_eq_bpos, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]

/-- The restore rule in terms of addresses. -/
lemma restore_iff {d θ A β : ℕ} (hd : d < H) (hA : A < 2 ^ (H + 2)) (hθ : θ < 2)
    (ν : Tape M) (c : CellVal M) (hβ : blk M x H d (cω H d A) θ ν = β) :
    (if sel β ≤ field A (bpos H d) 3 ∧ field A (bpos H d) 3 < sel β + 4 then
        semCell M x H (d + 1) 2 ν c
          (setBits A (bpos H d) 3 (4 * θ + (field A (bpos H d) 3 - sel β)))
      else semCell M x H d θ ν c A) ↔ semCell M x H d (θ + 1) ν c A := by
  have hres := cellT_restore (x := x) hd (cω_lt hd.le hA) hθ ν (cj H d A)
  rw [cj_div_bsz hd, cj_mod_bsz hd, hβ] at hres
  unfold semCell
  rw [hres]
  split_ifs with hin
  · set f := field A (bpos H d) 3
    have hv : 4 * θ + (f - sel β) < 2 ^ 3 := by norm_num; omega
    have h1 : cω H (d + 1) (setBits A (bpos H d) 3 (4 * θ + (f - sel β))) =
        2 * cω H d A + θ := by
      rw [cω_child hd, field_setBits hv, cω_setBits hv (by rw [bpos_add_three hd])]
      congr 1; omega
    have h2 : cj H (d + 1) (setBits A (bpos H d) 3 (4 * θ + (f - sel β))) =
        (f - sel β) * bsz H d + A % 2 ^ bpos H d := by
      rw [cj_child hd, field_setBits hv, setBits_mod hv, bsz_eq_bpos]
      congr 2; omega
    rw [h1, h2]
    simp [hd]
  · constructor <;> rintro ⟨-, h⟩ <;> exact ⟨fun _ => hd, h⟩

/-- The gather rule in terms of addresses. -/
lemma gather_iff {d θ A β : ℕ} (hd : d < H) (hθ : θ < 2) (ν : Tape M) (c : CellVal M)
    (hβ : blk M x H d (cω H d A) θ ν = β) (hf : field A (bpos H d) 3 / 4 = θ) :
    semCell M x H d θ ν c (setBits A (bpos H d) 3 (sel β + field A (bpos H d) 3 % 4)) ↔
      semCell M x H (d + 1) 0 ν c A := by
  subst hf
  have hsel : sel β ≤ 4 := min_le_right _ _
  have hv : sel β + field A (bpos H d) 3 % 4 < 2 ^ 3 := by
    have := Nat.mod_lt (field A (bpos H d) 3) (by norm_num : 4 > 0); norm_num; omega
  unfold semCell
  rw [cω_child hd, cj_child hd, cellT_gather hd (by omega), hβ,
    cω_setBits hv (by rw [bpos_add_three hd]), cj_eq hd, field_setBits hv, setBits_mod hv,
    bsz_eq_bpos]
  have : (sel β + field A (bpos H d) 3 % 4) * 2 ^ bpos H d + A % 2 ^ bpos H d =
      sel β * 2 ^ bpos H d + (field A (bpos H d) 3 % 4 * 2 ^ bpos H d + A % 2 ^ bpos H d) := by
    ring
  rw [this]
  constructor <;> rintro ⟨-, h⟩ <;> exact ⟨fun _ => by omega, h⟩

/-- A child state claim at phase `0` is the parent's state claim at the child's phase. -/
lemma stateUp_iff {d θ A : ℕ} (hd : d < H) (hθ : θ < 2) (p : ExtState M)
    (hf : field A (bpos H d + 2) 1 = θ) :
    semState M x H d θ p A ↔ semState M x H (d + 1) 0 p A := by
  rw [field_top_bit] at hf
  unfold semState
  rw [cω_child hd, hf, extT_up hd hθ]
  simp [hd]

/-- A state claim at phase `θ + 1` is the final state claim of child `θ`. -/
lemma stateDown_iff {d θ A : ℕ} (hd : d < H) (hθ : θ < 2) (p : ExtState M) :
    semState M x H (d + 1) 2 p (setBits A (bpos H d + 2) 1 θ) ↔
      semState M x H d (θ + 1) p A := by
  have hv : θ < 2 ^ 1 := by simpa using hθ
  unfold semState
  rw [cω_child hd, ← field_top_bit, field_setBits hv,
    cω_setBits hv (by rw [bpos_add_three hd])]
  try rw [← extT_down hd]
  try simp [hd]

/-! ## Base calls -/

lemma cω_base (A : ℕ) : cω H H A = A / 4 := by simp [cω]

lemma cj_base (A : ℕ) : cj H H A = A % 4 := by simp [cj]

/-- A head claim of a base call. -/
lemma baseHead_iff {A h : ℕ} (hh : h < 2 ^ 2) (ν : Tape M) (γ : Sym M) :
    semCell M x H H 0 ν (γ, true) (setBits A 0 2 h) ↔
      rel M x H H (A / 4) 0 ν = h ∧ scanT M x (A / 4) ν = γ := by
  have h1 : cω H H (setBits A 0 2 h) = A / 4 := by
    rw [cω_base, show (4 : ℕ) = 2 ^ (0 + 2) by norm_num, setBits_div hh]
  have h2 : cj H H (setBits A 0 2 h) = h := by
    rw [cj_base, show (4 : ℕ) = 2 ^ 2 by norm_num, ← field_zero_eq_mod, field_setBits hh]
  unfold semCell
  rw [h1, h2]
  have hc : cellT M x H H (A / 4) 0 ν h = ((runOn M x (A / 4)).tape ν
      (off M x H H (A / 4) ν + h), decide ((runOn M x (A / 4)).head ν =
        off M x H H (A / 4) ν + h)) := by
    simp [cellT, cfgCell, ptime_base]
  rw [hc]
  simp only [rel, scanT, hd, ptime_base, Nat.zero_div, add_zero, Prod.mk.injEq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨by rw [h2]; ring, by rw [h2]; exact h1⟩
  · rintro ⟨h1, h2⟩
    have : (runOn M x (A / 4)).head ν = off M x H H (A / 4) ν + h := by linarith
    exact ⟨by simp, by rw [← this]; exact h2, this⟩

/-! ## The root -/

lemma init_cell_outside {z : ℤ} (hz : z < 0 ∨ ((x.length : ℤ) ≤ z ∧ 0 < z)) (ν : Tape M) :
    cfgCell (init M x) ν z = (0, false) := by
  unfold cfgCell init
  simp only [Prod.mk.injEq]
  constructor
  · split_ifs with h
    · rcases hz with hz | ⟨hz1, -⟩
      · omega
      · have : x[z.toNat]? = none := List.getElem?_eq_none (by omega)
        rw [this]
    · rfl
  · simp only [decide_eq_false_iff_not]
    omega

/-- Agreement of the registers above register `0`. -/
lemma regs_agree_iff {s ℓ A T : ℕ} (hA : A < 2 ^ (s * ℓ)) (hT : T < 2 ^ (s * ℓ)) :
    (∀ i : Fin s, i.val ≠ 0 → field A (i * ℓ) ℓ = field T (i * ℓ) ℓ) ↔
      A / 2 ^ ℓ = T / 2 ^ ℓ := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro t
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    by_cases ht : t + ℓ < s * ℓ
    · have hℓ : 0 < ℓ := by
        rcases Nat.eq_zero_or_pos ℓ with h0 | h0
        · subst h0; simp at ht
        · exact h0
      set i := (t + ℓ) / ℓ
      have hi : i < s := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hi0 : i ≠ 0 := by
        have : 1 ≤ i := (Nat.le_div_iff_mul_le hℓ).mpr (by omega)
        omega
      have key := congrArg (fun v => v.testBit ((t + ℓ) % ℓ)) (h ⟨i, hi⟩ hi0)
      simp only [testBit_field, Nat.mod_lt _ hℓ, decide_true, Bool.true_and] at key
      have e : (t + ℓ) % ℓ + i * ℓ = t + ℓ := Nat.mod_add_div' _ _
      rwa [e] at key
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num)
        (by omega))), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hT
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · intro h i hi
    apply Nat.eq_of_testBit_eq
    intro t
    rw [testBit_field, testBit_field]
    by_cases ht : t < ℓ
    · simp only [ht, decide_true, Bool.true_and]
      have hle : ℓ ≤ t + i * ℓ := by
        have : 1 ≤ i.val := Nat.pos_of_ne_zero hi
        nlinarith
      have := congrArg (fun v => v.testBit (t + i * ℓ - ℓ)) h
      simp only [Nat.testBit_div_two_pow, Nat.sub_add_cancel hle] at this
      exact this
    · simp [ht]

end Lax119563Proofs.Circuits
