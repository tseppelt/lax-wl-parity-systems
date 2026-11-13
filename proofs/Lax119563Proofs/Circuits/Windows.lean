import Lax119563Proofs.Circuits.MachineRun

/-!
# Recursive windows of a run

Fix a horizon `H`. A *call* at depth `d ≤ H` is a number `ω < 2 ^ d`; it covers the steps
`[ω 2^r, (ω + 1) 2^r)` with `r = H - d`, in two phases of `B = 2^(r-1)` steps if `r ≥ 1`
(`ptime d ω θ` is the start of phase `θ`, and `θ = 2` is the end of the call). Per tape it
owns a window of `4 * 2^r` cells starting at the offset `off d ω ν`. The root window starts at
`-2^H`; the window of the child `2 ω + θ` starts at block `sel d ω θ ν = min (β - 1) 4` of the
parent window, where `β = blk d ω θ ν` is the block of the head at the start of phase `θ`.

The invariant `rel_mem`: at the start of a call, the head lies in the middle half
`[2^r, 3 * 2^r)` of its window. All truth values of the verifier's claims are values of the
run at these times and window positions; the rules below relate them.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

variable (M : Machine) (x : List Bool) (H : ℕ)

/-- The head position of tape `ν` after `t` steps. -/
def hd (t : ℕ) (ν : Tape M) : ℤ := (runOn M x t).head ν

/-- The start of phase `θ` of call `ω` at depth `d` (`θ = 2`: the end of the call). -/
def ptime (d ω θ : ℕ) : ℕ := ω * 2 ^ (H - d) + θ * 2 ^ (H - d) / 2

/-- The block size `2^(H - d - 1)` of a call at depth `d < H`. -/
def bsz (d : ℕ) : ℕ := 2 ^ (H - d - 1)

/-- The selected first block of the child window, for the head in block `β`. -/
def sel (β : ℕ) : ℕ := min (β - 1) 4

/-- The block of size `B` containing the relative position `R ≥ 0`. -/
def blkOf (R : ℤ) (B : ℕ) : ℕ := (R / (B : ℤ)).toNat

/-- The window offsets. -/
def off : ℕ → ℕ → Tape M → ℤ
  | 0, _, _ => -(2 ^ H : ℤ)
  | d + 1, ω, ν =>
    off d (ω / 2) ν +
      (sel (blkOf (hd M x (ptime H d (ω / 2) (ω % 2)) ν - off d (ω / 2) ν) (bsz H d)) : ℤ) *
        (bsz H d : ℤ)

/-- The head position relative to the window, at the start of phase `θ`. -/
def rel (d ω θ : ℕ) (ν : Tape M) : ℤ := hd M x (ptime H d ω θ) ν - off M x H d ω ν

/-- The block of the head at the start of phase `θ`. -/
def blk (d ω θ : ℕ) (ν : Tape M) : ℕ := blkOf (rel M x H d ω θ ν) (bsz H d)

/-- The value of the cell at window position `j` at the start of phase `θ`. -/
def cellT (d ω θ : ℕ) (ν : Tape M) (j : ℕ) : CellVal M :=
  cfgCell (runOn M x (ptime H d ω θ)) ν (off M x H d ω ν + j)

/-- The extended state at the start of phase `θ`. -/
def extT (d ω θ : ℕ) : ExtState M := cfgExt (runOn M x (ptime H d ω θ))

variable {M x H}

lemma off_succ (d ω : ℕ) (ν : Tape M) :
    off M x H (d + 1) ω ν = off M x H d (ω / 2) ν +
      (sel (blk M x H d (ω / 2) (ω % 2) ν) : ℤ) * (bsz H d : ℤ) := rfl

lemma pow_eq_two_mul_bsz {d : ℕ} (hdH : d < H) : 2 ^ (H - d) = 2 * bsz H d := by
  rw [bsz, ← pow_succ']
  congr 1
  omega

lemma bsz_succ (d : ℕ) : bsz H d = 2 ^ (H - (d + 1)) := by
  rw [bsz]; congr 1

lemma bsz_pos (d : ℕ) : 0 < bsz H d := by unfold bsz; positivity

lemma ptime_phase {d : ℕ} (hdH : d < H) (ω θ : ℕ) :
    ptime H d ω θ = ω * (2 * bsz H d) + θ * bsz H d := by
  rw [ptime, pow_eq_two_mul_bsz hdH]
  congr 1
  rw [Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num)]

lemma ptime_child (d ω θ' : ℕ) (hdH : d < H) :
    ptime H (d + 1) ω θ' = ptime H d (ω / 2) (ω % 2) + θ' * bsz H d / 2 := by
  rw [ptime_phase hdH, ptime, ← bsz_succ]
  have := Nat.div_add_mod ω 2
  rw [← this]
  have h2 : (2 * (ω / 2) + ω % 2) / 2 = ω / 2 := by omega
  have h3 : (2 * (ω / 2) + ω % 2) % 2 = ω % 2 := by omega
  rw [h2, h3]
  ring

lemma ptime_child_zero (d ω : ℕ) (hdH : d < H) :
    ptime H (d + 1) ω 0 = ptime H d (ω / 2) (ω % 2) := by
  rw [ptime_child d ω 0 hdH]; simp

lemma ptime_child_end (d ω θ : ℕ) (hdH : d < H) :
    ptime H (d + 1) (2 * ω + θ) 2 = ptime H d ω (θ + 1) := by
  have hθ : θ < 2 ∨ 2 ≤ θ := by omega
  rw [ptime_child d _ 2 hdH, ptime_phase hdH, ptime_phase hdH]
  rcases Nat.even_or_odd' θ with ⟨k, rfl | rfl⟩
  · have h1 : (2 * ω + 2 * k) / 2 = ω + k := by omega
    have h2 : (2 * ω + 2 * k) % 2 = 0 := by omega
    rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num)]
    ring
  · have h1 : (2 * ω + (2 * k + 1)) / 2 = ω + k := by omega
    have h2 : (2 * ω + (2 * k + 1)) % 2 = 1 := by omega
    rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num)]
    ring

lemma off_child (d ω θ : ℕ) (hθ : θ < 2) (ν : Tape M) :
    off M x H (d + 1) (2 * ω + θ) ν =
      off M x H d ω ν + (sel (blk M x H d ω θ ν) : ℤ) * (bsz H d : ℤ) := by
  rw [off_succ]
  have h1 : (2 * ω + θ) / 2 = ω := by omega
  have h2 : (2 * ω + θ) % 2 = θ := by omega
  rw [h1, h2]

lemma hd_dist (t k : ℕ) (ν : Tape M) : |hd M x (t + k) ν - hd M x t ν| ≤ k :=
  runOn_head_dist x ν t k

/-- The block of a head position in `[B, 7B)` lies in `[1, 6]` and determines it. -/
lemma blk_spec_aux {R B : ℤ} (hB : 0 < B) (h1 : B ≤ R) (h2 : R < 7 * B) :
    1 ≤ R / B ∧ R / B ≤ 6 ∧ R / B * B ≤ R ∧ R < (R / B + 1) * B := by
  have e1 : R / B * B ≤ R := Int.ediv_mul_le R (ne_of_gt hB)
  have e2 : R < (R / B + 1) * B := by
    have := Int.emod_lt_of_pos R hB
    have := Int.emod_add_ediv_mul R B
    nlinarith
  refine ⟨?_, ?_, e1, e2⟩
  · by_contra h
    have : R / B ≤ 0 := by omega
    nlinarith
  · by_contra h
    have : 7 ≤ R / B := by omega
    nlinarith

lemma blk_eq {d ω θ : ℕ} {ν : Tape M} {β : ℕ}
    (h1 : (β : ℤ) * bsz H d ≤ rel M x H d ω θ ν) (h2 : rel M x H d ω θ ν < (β + 1) * bsz H d) :
    blk M x H d ω θ ν = β := by
  have hB : (0 : ℤ) < bsz H d := by exact_mod_cast bsz_pos d
  rw [blk, blkOf, (Int.ediv_eq_iff_of_pos hB).mpr ⟨h1, by linarith⟩]
  simp

lemma hd_zero (ν : Tape M) : hd M x 0 ν = 0 := rfl

lemma rel_phase {d ω θ : ℕ} (hdH : d < H) (_hθ : θ < 2) (ν : Tape M) :
    |rel M x H d ω θ ν - rel M x H d ω 0 ν| ≤ θ * bsz H d := by
  unfold rel
  rw [ptime_phase hdH ω θ, ptime_phase hdH ω 0]
  simp only [zero_mul, add_zero, sub_sub_sub_cancel_right]
  exact_mod_cast hd_dist _ _ ν

lemma rel_child (d ω : ℕ) (hdH : d < H) (ν : Tape M) :
    rel M x H (d + 1) ω 0 ν =
      rel M x H d (ω / 2) (ω % 2) ν - (sel (blk M x H d (ω / 2) (ω % 2) ν) : ℤ) * bsz H d := by
  unfold rel
  rw [ptime_child_zero d ω hdH, off_succ]
  ring

/-- Window facts in a phase, given the middle-half invariant at the start of the call. -/
lemma phase_facts {d ω θ : ℕ} (hdH : d < H) (hθ : θ < 2) (ν : Tape M)
    (hinv : (2 ^ (H - d) : ℤ) ≤ rel M x H d ω 0 ν ∧ rel M x H d ω 0 ν < 3 * 2 ^ (H - d)) :
    1 ≤ blk M x H d ω θ ν ∧ blk M x H d ω θ ν ≤ 6 ∧
      (blk M x H d ω θ ν : ℤ) * (bsz H d : ℤ) ≤ rel M x H d ω θ ν ∧
      rel M x H d ω θ ν < ((blk M x H d ω θ ν : ℤ) + 1) * (bsz H d : ℤ) ∧
      ((sel (blk M x H d ω θ ν) : ℤ) + 1) * (bsz H d : ℤ) ≤ rel M x H d ω θ ν ∧
      rel M x H d ω θ ν < ((sel (blk M x H d ω θ ν) : ℤ) + 3) * (bsz H d : ℤ) ∧
      sel (blk M x H d ω θ ν) ≤ 4 := by
  have hB : (0 : ℤ) < (bsz H d : ℤ) := by exact_mod_cast bsz_pos d
  have hpow : (2 ^ (H - d) : ℤ) = 2 * (bsz H d : ℤ) := by exact_mod_cast pow_eq_two_mul_bsz hdH
  have hph := rel_phase (x := x) hdH hθ ν (ω := ω)
  rw [hpow] at hinv
  have hθB : ((θ * bsz H d : ℕ) : ℤ) ≤ (bsz H d : ℤ) := by
    have : θ * bsz H d ≤ bsz H d := by
      have : θ ≤ 1 := by omega
      nlinarith
    exact_mod_cast this
  have hR := abs_le.mp (le_trans hph hθB)
  obtain ⟨b1, b6, e1, e2⟩ := blk_spec_aux hB (R := rel M x H d ω θ ν)
    (by linarith [hinv.1, hR.1]) (by linarith [hinv.2, hR.2])
  have hβ : (blk M x H d ω θ ν : ℤ) = rel M x H d ω θ ν / (bsz H d : ℤ) := by
    simp only [blk, blkOf]
    exact Int.toNat_of_nonneg (by omega)
  rw [← hβ] at b1 b6 e1 e2
  have hβ1 : 1 ≤ blk M x H d ω θ ν := by exact_mod_cast b1
  have hβ6 : blk M x H d ω θ ν ≤ 6 := by exact_mod_cast b6
  refine ⟨hβ1, hβ6, e1, e2, ?_⟩
  have key : ∀ n : ℕ, 1 ≤ n → n ≤ 6 → (n : ℤ) * (bsz H d : ℤ) ≤ rel M x H d ω θ ν →
      rel M x H d ω θ ν < (n + 1) * (bsz H d : ℤ) →
      ((sel n : ℤ) + 1) * (bsz H d : ℤ) ≤ rel M x H d ω θ ν ∧
        rel M x H d ω θ ν < ((sel n : ℤ) + 3) * (bsz H d : ℤ) ∧ sel n ≤ 4 := by
    intro n h1 h6 hl hu
    interval_cases n <;> simp [sel] <;> constructor <;> push_cast at hl hu ⊢ <;> linarith
  exact key _ hβ1 hβ6 e1 e2

/-- The middle-half invariant: at the start of a call, each head lies in the middle half of
its window. -/
theorem rel_mem : ∀ d, d ≤ H → ∀ ω, ω < 2 ^ d → ∀ ν : Tape M,
    (2 ^ (H - d) : ℤ) ≤ rel M x H d ω 0 ν ∧ rel M x H d ω 0 ν < 3 * 2 ^ (H - d) := by
  intro d
  induction d with
  | zero =>
    intro _ ω hω ν
    have : ω = 0 := by simpa using hω
    subst this
    simp only [rel, ptime, off, zero_mul, Nat.zero_div, add_zero, Nat.sub_zero]
    rw [hd_zero]
    constructor <;> linarith [pow_pos (by norm_num : (0 : ℤ) < 2) H]
  | succ d ih =>
    intro hdH ω hω ν
    have hdH : d < H := by omega
    have hω2 : ω / 2 < 2 ^ d := by rw [pow_succ] at hω; omega
    have hθ : ω % 2 < 2 := Nat.mod_lt _ (by norm_num)
    obtain ⟨-, -, -, -, l, u, -⟩ := phase_facts (x := x) hdH hθ ν (ih (by omega) _ hω2 ν)
    have hp : (2 : ℤ) ^ (H - (d + 1)) = (bsz H d : ℤ) := by rw [bsz_succ]; push_cast; rfl
    rw [rel_child d ω hdH, hp]
    constructor <;> nlinarith

lemma ptime_child_zero' (d ω θ : ℕ) (hdH : d < H) (hθ : θ < 2) :
    ptime H (d + 1) (2 * ω + θ) 0 = ptime H d ω θ := by
  rw [ptime_child_zero d _ hdH]
  congr 1 <;> omega

/-- Restore rule: the cells after a phase are the child's final cells inside the child
window, and unchanged outside of it. -/
theorem cellT_restore {d ω θ : ℕ} (hdH : d < H) (hω : ω < 2 ^ d) (hθ : θ < 2) (ν : Tape M)
    (j : ℕ) :
    cellT M x H d ω (θ + 1) ν j =
      if sel (blk M x H d ω θ ν) ≤ j / bsz H d ∧ j / bsz H d < sel (blk M x H d ω θ ν) + 4 then
        cellT M x H (d + 1) (2 * ω + θ) 2 ν
          ((j / bsz H d - sel (blk M x H d ω θ ν)) * bsz H d + j % bsz H d)
      else cellT M x H d ω θ ν j := by
  set w := sel (blk M x H d ω θ ν) with hw
  set B := bsz H d with hB
  have hBpos : 0 < B := bsz_pos d
  have hjB := Nat.div_add_mod' j B
  split_ifs with hin
  · unfold cellT
    rw [ptime_child_end d ω θ hdH, off_child d ω θ hθ]
    congr 1
    rw [← hw, ← hB]
    have : (((j / B - w) * B + j % B : ℕ) : ℤ) = (j : ℤ) - w * B := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hin.1]
      have : ((j / B : ℕ) : ℤ) * B + (j % B : ℕ) = j := by exact_mod_cast hjB
      linarith
    rw [this]; ring
  · obtain ⟨-, -, -, -, l, u, -⟩ := phase_facts (x := x) hdH hθ ν (rel_mem d hdH.le ω hω ν)
    rw [← hw, ← hB] at l u
    have hout : (j : ℤ) < w * B ∨ ((w : ℤ) + 4) * B ≤ j := by
      rcases not_and_or.mp hin with h | h
      · left
        have : j < w * B := by
          rw [not_le] at h
          exact (Nat.div_lt_iff_lt_mul hBpos).mp h
        exact_mod_cast this
      · right
        have : (w + 4) * B ≤ j := (Nat.le_div_iff_mul_le hBpos).mp (not_lt.mp h)
        exact_mod_cast this
    have t1 : ptime H d ω (θ + 1) = ptime H d ω θ + B := by
      rw [ptime_phase hdH, ptime_phase hdH]; ring
    have far : ∀ i ≤ B, hd M x (ptime H d ω θ + i) ν ≠ off M x H d ω ν + j := by
      intro i hi heq
      have hdist := abs_le.mp (hd_dist (x := x) (ptime H d ω θ) i ν)
      have hi' : (i : ℤ) ≤ B := by exact_mod_cast hi
      unfold rel at l u
      rcases hout with h | h <;> nlinarith
    unfold cellT cfgCell
    rw [t1]
    have htape := runOn_tape_frame x ν (off M x H d ω ν + j) (ptime H d ω θ) B
      (fun i hi => far i hi.le)
    rw [htape]
    have f1 := far B le_rfl
    have f0 := far 0 (Nat.zero_le _)
    simp only [add_zero] at f0
    simp only [Circuits.hd] at f1 f0
    simp [f1, f0]

/-- Gather rule: the cells of a child at its start are cells of the parent. -/
theorem cellT_gather {d ω θ : ℕ} (hdH : d < H) (hθ : θ < 2) (ν : Tape M) (j : ℕ) :
    cellT M x H (d + 1) (2 * ω + θ) 0 ν j =
      cellT M x H d ω θ ν (sel (blk M x H d ω θ ν) * bsz H d + j) := by
  unfold cellT
  rw [ptime_child_zero' d ω θ hdH hθ, off_child d ω θ hθ]
  push_cast
  ring_nf

theorem extT_up {d ω θ : ℕ} (hdH : d < H) (hθ : θ < 2) :
    extT M x H (d + 1) (2 * ω + θ) 0 = extT M x H d ω θ := by
  unfold extT
  rw [ptime_child_zero' d ω θ hdH hθ]

theorem extT_down {d ω θ : ℕ} (hdH : d < H) :
    extT M x H d ω (θ + 1) = extT M x H (d + 1) (2 * ω + θ) 2 := by
  unfold extT
  rw [ptime_child_end d ω θ hdH]

lemma ptime_base (ω θ : ℕ) : ptime H H ω θ = ω + θ / 2 := by
  simp [ptime]

/-- The scanned symbols at the start of a base call. -/
def scanT (M : Machine) (x : List Bool) (ω : ℕ) : Tape M → Sym M := fun ν => (runOn M x ω).tape ν (hd M x ω ν)

theorem extT_base (ω : ℕ) :
    extT M x H H ω 2 = nextExt (extT M x H H ω 0) (scanT M x ω) := by
  unfold extT
  rw [ptime_base, ptime_base, show ω + 2 / 2 = ω + 1 by norm_num, runOn_succ, step_ext]
  rfl

theorem cellT_base (ω : ℕ) (ν : Tape M) (j : ℕ) :
    cellT M x H H ω 2 ν j =
      nextCell (extT M x H H ω 0) (scanT M x ω) ν (rel M x H H ω 0 ν) j
        (cellT M x H H ω 0 ν j) := by
  unfold cellT extT rel
  rw [ptime_base, ptime_base, show ω + 2 / 2 = ω + 1 by norm_num, runOn_succ,
    step_cell _ ν (off M x H H ω ν)]
  simp only [add_sub_cancel_left, Nat.zero_div, add_zero]; rfl

theorem cellT_root (ν : Tape M) (j : ℕ) :
    cellT M x H 0 0 0 ν j = cfgCell (init M x) ν ((j : ℤ) - 2 ^ H) := by
  unfold cellT
  simp [ptime, off, runOn_zero]
  ring_nf

theorem extT_root : extT M x H 0 0 0 = (0, none) := by
  simp [extT, ptime, runOn_zero, cfgExt, init]

theorem extT_query : extT M x H 0 0 2 = cfgExt (runOn M x (2 ^ H)) := by
  simp [extT, ptime]

end Lax119563Proofs.Circuits
