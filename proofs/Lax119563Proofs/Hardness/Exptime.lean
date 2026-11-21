import Lax119563.EXPTIMEHardness
import Lax119563.MachineTranslations
import Lax119563Proofs.Hardness.Part1
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# WL Distinguishing is EXPTIME-hard

Let `L ∈ EXPTIME`. By the single-tape simulation (`singleTape_simulation`, cited) a
deterministic machine `M` decides `x ∈ L` within `C (2^{p(n)} + n + 1)` steps. Composed with
`dropMachine`, it decides `x ∈ L` on the padded input `true :: true :: x` (of length at least
`2`, as the pipeline requires). The reduction `redTM R d` (with `R` the pipeline machine of
the padded decider and a constant `d`) computes `h = 2^(d (|bits n| + 1)) - 1`, which lies
between `p(n) + n + C + 25` and `(4 (n + 1))^d`, and runs `R` on
`encodeNats [h, h] ++ true :: true :: x`, with `s = h` data blocks. Then the block width is
`ℓ = max(⌈log₂(n + 4)⌉, 2)`, so `2^ℓ = O(n)`, the padded decider halts within `2^h` steps,
and the pipeline time `C (h 2^ℓ (h + 1))^c` is polynomial in `n`. The multitape machine is
translated to a multi-stack machine by `tm2_of_polyTime` (cited).
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime Lax119563.PackedRepresentation Lax119563.WLProblems
open Lax434930.ExponentialTime Lax429075.Reductions
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

/-! ## Arithmetic -/

lemma poly_eval_le (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) * (n + 1) ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply Nat.mul_le_mul_left
  calc n ^ i ≤ (n + 1) ^ i := Nat.pow_le_pow_left (by omega) _
    _ ≤ (n + 1) ^ p.natDegree :=
      Nat.pow_le_pow_right (by omega) (by simp at hi; omega)

lemma two_mul_le_two_pow (B : ℕ) : 2 * B ≤ 2 ^ B := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := B)
    omega

lemma halt_arith {B X n : ℕ} (hX : 1 ≤ X) :
    B * (X + n + 1) ≤ X * 2 ^ n * 2 ^ B := by
  have h1 : X + n + 1 ≤ 2 * (X * (n + 1)) := by nlinarith
  have h2 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h3 := two_mul_le_two_pow B
  calc B * (X + n + 1) ≤ B * (2 * (X * (n + 1))) := Nat.mul_le_mul_left _ h1
    _ = X * (n + 1) * (2 * B) := by ring
    _ ≤ X * 2 ^ n * 2 ^ B := Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h3

lemma horizon_arith {A D B W d : ℕ} (hW : 1 ≤ W) (hd : d = A + D + B + 2) :
    A * W ^ D + W + B + 2 ≤ 2 ^ d * W ^ d := by
  have h1 : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
  have h2 : W ^ D ≤ W ^ d := Nat.pow_le_pow_right hW (by omega)
  have h3 : W ≤ W ^ d := by
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ d := Nat.pow_le_pow_right hW (by omega)
  have h4 : (A + B + 3) * W ^ d ≤ 2 ^ d * W ^ d := Nat.mul_le_mul_right _ (by omega)
  have h5 : A * W ^ D ≤ A * W ^ d := Nat.mul_le_mul_left _ h2
  have h6 : (B + 3) * W ≤ (B + 3) * W ^ d := Nat.mul_le_mul_left _ h3
  have h7 : W + B + 2 ≤ (B + 3) * W := by nlinarith
  have e : (A + B + 3) * W ^ d = A * W ^ d + (B + 3) * W ^ d := by ring
  omega

lemma two_pow_size_le (n : ℕ) : 2 ^ Nat.size n ≤ 2 * (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hs : 0 < Nat.size n := Nat.size_pos.mpr hn
    have : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.mp (by omega)
    have e : 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

lemma two_pow_clog_le (m : ℕ) (hm : 1 < m) : 2 ^ Nat.clog 2 m ≤ 2 * m := by
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hm
  have hpos : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) hm
  have e : 2 ^ Nat.clog 2 m = 2 * 2 ^ (Nat.clog 2 m).pred := by
    rw [← pow_succ']; congr 1; exact (Nat.succ_pred_eq_of_pos hpos).symm
  omega

lemma two_pow_packedWidth_le (n h : ℕ) (hh : 2 ≤ h) :
    2 ^ packedWidth (n + 2) h h ≤ 8 * (n + 1) := by
  have hdiv : (h + 1 + h) / h = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  unfold packedWidth
  rw [hdiv]
  rcases le_total (Nat.clog 2 (n + 2 + 2)) 2 with hle | hle
  · rw [max_eq_right hle]; norm_num; omega
  · rw [max_eq_left hle]
    have := two_pow_clog_le (n + 2 + 2) (by omega)
    omega

lemma pre_arith {n L S d Y : ℕ} (hS : S ≤ n) (hL : L ≤ n)
    (hY : Y = 2 * (2 * d * (L + 1) + 1) + n + 2) :
    n * (4 * S + 7) + 2 * (d * (5 * L + 4) + 1) + 2 + (2 * n + 2) + 2 * n + (2 * n + 2) +
      3 * (2 * Y + 2) + 1 ≤ 100 * (d + 1) * (n + 1) ^ 2 := by
  subst hY
  have h1 : n * S ≤ n * n := Nat.mul_le_mul_left _ hS
  have h2 : d * L ≤ d * n := Nat.mul_le_mul_left _ hL
  have h3 : d * n ≤ d * (n * n) + d := by
    have : n ≤ n * n + 1 := by nlinarith
    calc d * n ≤ d * (n * n + 1) := Nat.mul_le_mul_left _ this
      _ = d * (n * n) + d := by ring
  nlinarith

/-- The final time bound. -/
lemma total_arith {n d C c hh Q P t pre : ℕ} (hW : pre ≤ 100 * (d + 1) * (n + 1) ^ 2)
    (hh1 : hh + 1 ≤ (4 * (n + 1)) ^ d) (hQ : Q ≤ 8 * (n + 1))
    (hP : P = hh * Q * (hh + 1)) (ht : t = C * P ^ c) :
    pre + 2 * t + 1 ≤ (100 * (d + 1) + 2 * C * 8 ^ ((2 * d + 1) * c) + 1) *
      (n + 1) ^ ((2 * d + 1) * c + 2) := by
  set W := n + 1 with hWdef
  have hW1 : 1 ≤ W := by omega
  have e8 : (4 * W) ^ d ≤ (8 * W) ^ d := Nat.pow_le_pow_left (by omega) d
  have hPle : P ≤ (8 * W) ^ (2 * d + 1) := by
    rw [hP, show 2 * d + 1 = d + 1 + d by ring, pow_add, pow_succ]
    exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) hQ) (by omega)
  have hPc : P ^ c ≤ 8 ^ ((2 * d + 1) * c) * W ^ ((2 * d + 1) * c) := by
    calc P ^ c ≤ ((8 * W) ^ (2 * d + 1)) ^ c := Nat.pow_le_pow_left hPle c
      _ = 8 ^ ((2 * d + 1) * c) * W ^ ((2 * d + 1) * c) := by rw [← pow_mul, mul_pow]
  set E0 := (2 * d + 1) * c
  have a1 : W ^ 2 ≤ W ^ (E0 + 2) := Nat.pow_le_pow_right hW1 (by omega)
  have a2 : W ^ E0 ≤ W ^ (E0 + 2) := Nat.pow_le_pow_right hW1 (by omega)
  have a3 : 1 ≤ W ^ (E0 + 2) := Nat.one_le_pow _ _ hW1
  have b1 : 100 * (d + 1) * W ^ 2 ≤ 100 * (d + 1) * W ^ (E0 + 2) := Nat.mul_le_mul_left _ a1
  have b2 : 2 * t ≤ 2 * C * 8 ^ E0 * W ^ (E0 + 2) := by
    rw [ht]
    calc 2 * (C * P ^ c) ≤ 2 * (C * (8 ^ E0 * W ^ E0)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hPc)
      _ ≤ 2 * (C * (8 ^ E0 * W ^ (E0 + 2))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ a2))
      _ = 2 * C * 8 ^ E0 * W ^ (E0 + 2) := by ring
  have e : (100 * (d + 1) + 2 * C * 8 ^ E0 + 1) * W ^ (E0 + 2) =
      100 * (d + 1) * W ^ (E0 + 2) + 2 * C * 8 ^ E0 * W ^ (E0 + 2) + W ^ (E0 + 2) := by ring
  omega

/-! ## Deciders -/

/-- EXPTIME in the multitape model, from the cited single-tape simulation. -/
lemma exptime_decides {L : Set (List Bool)} (hL : L ∈ EXPTIME) :
    ∃ M : Machine, Deterministic M ∧ ∃ C : ℕ, ∃ p : Polynomial ℕ, ∀ w : List Bool,
      DecidesExactlyWithin M w (w ∈ L) (C * (2 ^ p.eval w.length + w.length + 1)) := by
  obtain ⟨M₀, p, hM₀⟩ := hL
  obtain ⟨M, hM, C, h⟩ := Lax119563.MachineTranslations.singleTape_simulation M₀
  refine ⟨M, hM, C, p, fun w => ?_⟩
  obtain ⟨c, hev, hc, hacc⟩ := hM₀ w
  obtain ⟨b, hb, hbP⟩ := h w _ c hev hc
  exact ⟨b, hb, hbP.trans hacc⟩

/-- The decider on padded inputs. -/
lemma padded_decides {L : Set (List Bool)} {M : Machine} {C : ℕ} {p : Polynomial ℕ}
    (h : ∀ w : List Bool, DecidesExactlyWithin M w (w ∈ L) (C * (2 ^ p.eval w.length + w.length + 1)))
    (x : List Bool) :
    DecidesExactlyWithin (Main.Compose.comp dropMachine M false fun _ => false).toMachine
      (true :: true :: x) (x ∈ L) ((C + 25) * (2 ^ p.eval x.length + x.length + 1)) := by
  have hc := Main.Compose.compose_decidesWithin dropMachine M false (fun _ => false)
    (x := true :: true :: x) (by simp) (drop_computesWithin x) (h x)
  refine Main.decidesWithin_mono hc ?_
  have := Nat.one_le_two_pow (n := p.eval x.length)
  have e : (C + 25) * (2 ^ p.eval x.length + x.length + 1) =
      C * (2 ^ p.eval x.length + x.length + 1) + 25 * (2 ^ p.eval x.length + x.length + 1) := by
    ring
  omega

/-! ## The reduction -/

/--
---
conclusion: Lax119563.EXPTIMEHardness.wl_exptime_hard
---
For `L ∈ EXPTIME`, a deterministic decider (from `singleTape_simulation`) is run on padded
inputs `true :: true :: x` (`padded_decides`); the machine `redTM R d` writes
`encodeNats [h, h] ++ true :: true :: x` with `h = 2^(d (|bits n| + 1)) - 1` and runs the
pipeline machine `R` of `pipeline_language`. The choice `d = A + D + B + 2` (from the
coefficient sum `A` and degree `D` of the polynomial and the constant `B` of the decider)
gives `h ≥ p(n) + n + B`, so the decider halts within `2^h` steps, while
`h + 1 ≤ (4 (n + 1))^d` and `2^ℓ ≤ 8 (n + 1)` make the running time polynomial. The machine
is translated by `tm2_of_polyTime`.
-/
theorem wl_exptime_hard : ∀ L ∈ EXPTIME, ManyOne L WLDistinguishing := by
  intro L hL
  obtain ⟨M, -, CM, p, hdec⟩ := exptime_decides hL
  have hM' : Deterministic (Main.Compose.comp dropMachine M false fun _ => false).toMachine :=
    Main.AMachine.toMachine_deterministic _
  obtain ⟨c, hpipe⟩ := pipeline_language
  obtain ⟨R, hR, C, hC⟩ := hpipe _ hM'
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = A + p.natDegree + (CM + 25) + 2 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = (2 * d + 1) * c + 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = 100 * (d + 1) + 2 * C * 8 ^ ((2 * d + 1) * c) + 1 := ⟨_, rfl⟩
  have key : ∀ x : List Bool, ∃ z : List Bool, (x ∈ L ↔ z ∈ WLDistinguishing) ∧
      ComputesWithin (redTM R d).compile x z (K * (x.length + 1) ^ E) := by
    intro x
    set n := x.length with hn
    set hh := hOf d n with hhh
    set Lb := (Nat.bits n).length with hLb
    have hLs : Lb = Nat.size n := by rw [hLb, Nat.size_eq_bits_len]
    -- the horizon
    have hpow : hh + 1 = 2 ^ (d * (Lb + 1)) := by
      have := Nat.one_le_two_pow (n := d * (Lb + 1)); rw [hhh, hOf, ← hLb]; omega
    have hnL : n + 1 ≤ 2 ^ Lb := by rw [hLs]; exact Nat.lt_size_self n
    have hlow : 2 ^ d * (n + 1) ^ d ≤ hh + 1 := by
      rw [hpow, ← mul_pow, pow_mul']
      exact Nat.pow_le_pow_left (show 2 * (n + 1) ≤ 2 ^ (Lb + 1) by rw [pow_succ]; omega) d
    have hup : hh + 1 ≤ (4 * (n + 1)) ^ d := by
      rw [hpow, pow_mul']
      refine Nat.pow_le_pow_left (show 2 ^ (Lb + 1) ≤ 4 * (n + 1) from ?_) d
      have := two_pow_size_le n
      rw [pow_succ, hLs]; omega
    have hpe := poly_eval_le p n
    rw [← hA] at hpe
    have hhor := horizon_arith (A := A) (D := p.natDegree) (B := CM + 25) (W := n + 1)
      (by omega) hd
    have hbig : p.eval n + n + (CM + 25) ≤ hh := by omega
    have hh2 : 2 ≤ hh := by omega
    have hhpow : hh < 2 ^ hh := Nat.lt_two_pow_self
    -- the padded decider halts within `2^h` steps
    have hdec' := padded_decides hdec x
    have htime : (CM + 25) * (2 ^ p.eval n + n + 1) ≤ 2 ^ hh := by
      have h1 := halt_arith (B := CM + 25) (X := 2 ^ p.eval n) (n := n) Nat.one_le_two_pow
      have h2 : 2 ^ p.eval n * 2 ^ n * 2 ^ (CM + 25) ≤ 2 ^ hh := by
        rw [← pow_add, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) hbig
      omega
    have hhalt : (Lax119563.DeterministicTime.runOn
        (Main.Compose.comp dropMachine M false fun _ => false).toMachine
        (true :: true :: x) (2 ^ hh)).answer.isSome := by
      obtain ⟨b, hb, -⟩ := Main.decidesWithin_mono hdec' htime
      simp [hb]
    -- the pipeline
    obtain ⟨G₀, G₁, hacc, -, -, hcomp⟩ := hC (true :: true :: x) hh hh (by simp)
      hh2 (by simp; omega) hh2 (by omega)
    refine ⟨encodeWLInstance (hh + 1) G₀ G₁, ?_, ?_⟩
    · rw [← hacc hhalt]
      exact (Main.accepts_iff_of_decidesWithin hdec').symm
    · have hcomp' : ComputesWithin R (redInput d x) (encodeWLInstance (hh + 1) G₀ G₁)
          (C * (hh * 2 ^ packedWidth (n + 2) hh hh * (hh + 1)) ^ c) := by
        simpa [redInput] using hcomp
      obtain ⟨T', hrun, hT'⟩ := redTM_runsWithin d hcomp'
      have hcw := (redTM R d).computesWithin (fun _ _ => false) hrun
        (y := encodeWLInstance (hh + 1) G₀ G₁) (by rw [hT']; simp [Machines.bitsWord])
      refine Main.Compose.computesWithin_mono' hcw ?_
      have hpre := pre_arith (n := n) (L := Lb) (S := Nat.size n) (d := d)
        (Y := (redInput d x).length) (Nat.size_le.mpr Nat.lt_two_pow_self)
        (by rw [hLs]; exact Nat.size_le.mpr Nat.lt_two_pow_self)
        (by rw [length_redInput])
      have htot := total_arith hpre hup (two_pow_packedWidth_le n hh hh2) rfl rfl
        (C := C) (c := c)
      rw [← hn, ← hLb]
      rw [hK, hE]
      exact htot
  choose f hf1 hf2 using key
  exact ⟨f, Lax119563.MachineTranslations.tm2_of_polyTime (redTM R d).compile
    (redTM_deterministic R d) K E hf2, hf1⟩

end Lax119563Proofs.Hardness
