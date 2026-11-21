import Lax119563.XPHardness
import Lax119563Proofs.Hardness.Part1
import Lax119563Proofs.Hardness.Part2

/-!
# WL Distinguishing is XP-hard

Let `P ∈ XP` with a decider `M` running in time `f(k) (n + 1)^{f(k)}` (`k = κ x`,
`n = |x|`), and let `F k = 2 f(k) + 4`. On input `x`, the reduction works on the padded
input `y = true :: true :: x` (of length `n + 2 ≥ 2`, as the pipeline and the composition of
machines require):

* the statement `xpS` (`xp_prog`) computes `k` (with the parameter machine composed after
  `dropMachine`), `F k`, `a = ⌈log₂ (n + 4)⌉`, and emits `[h, s]` with `h = F k · a` and
  `s = F k + 1`; `withSuffix` appends `y`;
* the pipeline machine of the padded decider (`dropMachine` composed with `M`) maps
  `encodeNats [h, s] ++ y` to `encodeWLInstance (s + 1) G₀ G₁`;
* `padTM` writes `y` from `x` and runs the composition of the two machines.

Since `2^h ≥ (n + 4)^{F k}`, the padded decider halts within `2^h` steps (`xp_halt_arith`).
The block width is `ℓ ≤ a + 1`, so `2^ℓ ≤ 4 (n + 4)`, and the pipeline time
`C (s 2^ℓ (h + 1))^c` is at most `C 64^c (F k + 1)^{2c} (n + 1)^{2c}`: polynomial in `n` with
a degree independent of `k`. The new parameter is `s + 1 = 2 f(k) + 6`.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime Lax119563.PackedRepresentation Lax119563.WLProblems
open Lax119563.ParameterizedComplexity
open Lax489179.TuringMachine (Machine Deterministic)
open Lax119563Proofs.Computability

namespace Lax119563Proofs.Hardness

/-! ## Arithmetic -/

/-- The running time of the parameter machine on padded inputs. -/
lemma xp_kappa_arith (n Cκ d : ℕ) :
    2 * (8 * n + 11) + (Cκ * n ^ d + Cκ) + 3 ≤ (Cκ + 25) * (n + 2 + 1) ^ (d + 1) := by
  obtain ⟨W, hW⟩ : ∃ W, W = n + 2 + 1 := ⟨_, rfl⟩
  rw [← hW]
  have h1 : n ^ d ≤ W ^ d := Nat.pow_le_pow_left (by omega) d
  have h2 : 1 ≤ W ^ d := Nat.one_le_pow _ _ (by omega)
  have h3 : W ^ (d + 1) = W ^ d * W := pow_succ W d
  have h4 : W ^ d * 2 ≤ W ^ d * W := Nat.mul_le_mul_left _ (by omega)
  have h5 : W ≤ W ^ (d + 1) := by rw [h3]; exact Nat.le_mul_of_pos_left _ (by omega)
  have h6 : Cκ * (n ^ d + 1) ≤ Cκ * W ^ (d + 1) :=
    Nat.mul_le_mul_left _ (by rw [h3]; omega)
  have e : (Cκ + 25) * W ^ (d + 1) = Cκ * W ^ (d + 1) + 25 * W ^ (d + 1) := by ring
  have e2 : Cκ * (n ^ d + 1) = Cκ * n ^ d + Cκ := by ring
  omega

/-- The padded decider halts within `2^h` steps. -/
lemma xp_halt_arith (n f : ℕ) :
    2 * (8 * n + 11) + f * (n + 1) ^ f + 3 ≤ (n + 4) ^ (2 * f + 4) := by
  have hA1 : (n + 1) ^ f ≤ (n + 4) ^ f := Nat.pow_le_pow_left (by omega) f
  have hA2 : f + 1 ≤ (n + 4) ^ f := by
    have : 2 ^ f ≤ (n + 4) ^ f := Nat.pow_le_pow_left (by omega) f
    have := Nat.lt_two_pow_self (n := f)
    omega
  have hV : 64 * (n + 4) ≤ (n + 4) ^ 4 := by
    have : 4 ^ 3 ≤ (n + 4) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    rw [pow_succ]
    calc 64 * (n + 4) = 4 ^ 3 * (n + 4) := by norm_num
      _ ≤ (n + 4) ^ 3 * (n + 4) := Nat.mul_le_mul_right _ this
  have e : (n + 4) ^ (2 * f + 4) = (n + 4) ^ f * (n + 4) ^ f * (n + 4) ^ 4 := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [e]
  obtain ⟨A, hA⟩ : ∃ A, A = (n + 4) ^ f := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (n + 1) ^ f := ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V, V = (n + 4) ^ 4 := ⟨_, rfl⟩
  rw [← hA, ← hB, ← hVd]
  rw [← hA, ← hB] at hA1
  rw [← hA] at hA2
  rw [← hVd] at hV
  have hB1 : 1 ≤ B := by rw [hB]; exact Nat.one_le_pow _ _ (by omega)
  have s1 : (f + 1) * B * V ≤ A * A * V :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul hA2 hA1)
  have s2 : f * B ≤ f * B * V := Nat.le_mul_of_pos_right _ (by omega)
  have s3 : V ≤ B * V := Nat.le_mul_of_pos_left _ (by omega)
  have e2 : (f + 1) * B * V = f * B * V + B * V := by ring
  omega

/-- The block width. -/
lemma xp_width_le (n F : ℕ) :
    packedWidth (n + 2) (F * parA (n + 2)) (F + 1) ≤ parA (n + 2) + 1 := by
  have ha := one_le_parA (n + 2)
  unfold packedWidth
  refine max_le (by unfold parA; omega) ?_
  refine Nat.div_le_of_le_mul ?_
  have e : (F + 1) * (parA (n + 2) + 1) = F * parA (n + 2) + F + parA (n + 2) + 1 := by ring
  omega

/-- The final time bound. -/
lemma xp_total_arith {n K1 H Fp Cp c E1 tD Pp : ℕ} (hH : Fp ≤ H) (hH1 : 1 ≤ H)
    (htD : tD ≤ K1 * H ^ 3 * (n + 2 + 1) ^ E1) (hP : Pp ≤ 64 * Fp ^ 2 * (n + 1) ^ 2) :
    20 * n + 41 + 2 * (2 * (16 * (tD + (n + 2) + 1)) + Cp * Pp ^ c + 3) ≤
      (64 * K1 * 3 ^ E1 + 2 * Cp * 64 ^ c + 400) * H ^ (3 + 2 * c) *
        (n + 1) ^ (E1 + 2 * c + 1) := by
  obtain ⟨W, hW⟩ : ∃ W, W = n + 1 := ⟨_, rfl⟩
  rw [← hW]
  have hW1 : 1 ≤ W := by omega
  obtain ⟨Hp, hHp⟩ : ∃ Hp, Hp = H ^ (3 + 2 * c) := ⟨_, rfl⟩
  obtain ⟨We, hWe⟩ : ∃ We, We = W ^ (E1 + 2 * c + 1) := ⟨_, rfl⟩
  rw [← hHp, ← hWe]
  have hHp1 : 1 ≤ Hp := by rw [hHp]; exact Nat.one_le_pow _ _ hH1
  have hWe1 : W ≤ We := by
    rw [hWe]
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ (E1 + 2 * c + 1) := Nat.pow_le_pow_right hW1 (by omega)
  -- the program
  have hn3 : n + 2 + 1 ≤ 3 * W := by omega
  have t1 : (n + 2 + 1) ^ E1 ≤ 3 ^ E1 * We := by
    calc (n + 2 + 1) ^ E1 ≤ (3 * W) ^ E1 := Nat.pow_le_pow_left hn3 E1
      _ = 3 ^ E1 * W ^ E1 := mul_pow _ _ _
      _ ≤ 3 ^ E1 * We := Nat.mul_le_mul_left _ (by
          rw [hWe]; exact Nat.pow_le_pow_right hW1 (by omega))
  have t2 : H ^ 3 ≤ Hp := by rw [hHp]; exact Nat.pow_le_pow_right hH1 (by omega)
  have htD' : tD ≤ K1 * 3 ^ E1 * (Hp * We) := by
    calc tD ≤ K1 * H ^ 3 * (n + 2 + 1) ^ E1 := htD
      _ ≤ K1 * Hp * (3 ^ E1 * We) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ t2) t1
      _ = K1 * 3 ^ E1 * (Hp * We) := by ring
  -- the pipeline
  have hPc : Pp ^ c ≤ 64 ^ c * (Hp * We) := by
    have u1 : Pp ^ c ≤ (64 * Fp ^ 2 * W ^ 2) ^ c := Nat.pow_le_pow_left (by rw [hW]; exact hP) c
    have u2 : (64 * Fp ^ 2 * W ^ 2) ^ c = 64 ^ c * (Fp ^ (2 * c) * W ^ (2 * c)) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]; ring
    have u3 : Fp ^ (2 * c) ≤ Hp := by
      calc Fp ^ (2 * c) ≤ H ^ (2 * c) := Nat.pow_le_pow_left hH _
        _ ≤ Hp := by rw [hHp]; exact Nat.pow_le_pow_right hH1 (by omega)
    have u4 : W ^ (2 * c) ≤ We := by rw [hWe]; exact Nat.pow_le_pow_right hW1 (by omega)
    calc Pp ^ c ≤ 64 ^ c * (Fp ^ (2 * c) * W ^ (2 * c)) := u2 ▸ u1
      _ ≤ 64 ^ c * (Hp * We) := Nat.mul_le_mul_left _ (Nat.mul_le_mul u3 u4)
  have hCp : Cp * Pp ^ c ≤ Cp * 64 ^ c * (Hp * We) := by
    calc Cp * Pp ^ c ≤ Cp * (64 ^ c * (Hp * We)) := Nat.mul_le_mul_left _ hPc
      _ = Cp * 64 ^ c * (Hp * We) := by ring
  -- the rest
  have hHW : We ≤ Hp * We := Nat.le_mul_of_pos_left _ hHp1
  have e : (64 * K1 * 3 ^ E1 + 2 * Cp * 64 ^ c + 400) * Hp * We =
      64 * (K1 * 3 ^ E1 * (Hp * We)) + 2 * (Cp * 64 ^ c * (Hp * We)) + 400 * (Hp * We) := by
    ring
  rw [e]
  omega

/-! ## The reduction -/

/-- The parameter machine on padded inputs. -/
lemma xp_kappa_padded {Mκ : Machine} {κ : List Bool → ℕ} {Cκ d : ℕ}
    (hκ : ∀ x, ComputesWithin Mκ x (encodeNat (κ x)) (Cκ * x.length ^ d + Cκ)) (x : List Bool) :
    ComputesWithin (Main.Compose.comp dropMachine Mκ false fun _ => false).toMachine
      (true :: true :: x) (encodeNat (κ x))
      ((Cκ + 25) * ((true :: true :: x).length + 1) ^ (d + 1)) := by
  have hc := Main.Compose.compose_computesWithin dropMachine Mκ false (fun _ => false)
    (x := true :: true :: x) (by simp) (drop_computesWithin x) (hκ x)
  refine Main.Compose.computesWithin_mono' hc ?_
  have := xp_kappa_arith x.length Cκ d
  simp only [List.length_cons]
  omega

/-- The decider on padded inputs. -/
lemma xp_padded_decides {P : ParameterizedProblem} {M : Machine} {f : ℕ → ℕ}
    (hdec : ∀ x : List Bool, DecidesExactlyWithin M x (x ∈ P.L) (f (P.κ x) * (x.length + 1) ^ f (P.κ x)))
    (x : List Bool) :
    DecidesExactlyWithin (Main.Compose.comp dropMachine M false fun _ => false).toMachine
      (true :: true :: x) (x ∈ P.L) ((x.length + 4) ^ (2 * f (P.κ x) + 4)) := by
  have hc := Main.Compose.compose_decidesWithin dropMachine M false (fun _ => false)
    (x := true :: true :: x) (by simp) (drop_computesWithin x) (hdec x)
  exact Main.decidesWithin_mono hc (xp_halt_arith _ _)

lemma succ_pow_le (n E : ℕ) : (n + 1) ^ E ≤ 2 ^ E * n ^ E + 2 ^ E := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := Nat.one_le_two_pow (n := E)
    simp only [zero_add, one_pow]
    omega
  · have : (n + 1) ^ E ≤ (2 * n) ^ E := Nat.pow_le_pow_left (by omega) E
    rw [mul_pow] at this
    exact this.trans (Nat.le_add_right _ _)

/--
---
conclusion: Lax119563.XPHardness.wl_xp_hard
---
For `P ∈ XP` with decider `M` in time `f(k) (n + 1)^{f(k)}`, let `F k = 2 f(k) + 4`. The
reduction machine `padTM Q` writes the padded input `y = true :: true :: x` and runs `Q`, the
composition of `withSuffix` of the machine of `xpS` (which computes `[h, s]` with
`h = F(k) ⌈log₂ (|x| + 4)⌉` and `s = F(k) + 1`, `xp_prog`) with the pipeline machine
(`pipeline_language`) of the padded decider. The padded decider halts within
`(|x| + 4)^{F k} ≤ 2^h` steps (`xp_halt_arith`), so the pipeline is correct; its running time
is polynomial in `|x|` with a degree independent of `k`, since the block width is at most
`⌈log₂ (|x| + 4)⌉ + 1` (`xp_width_le`, `xp_total_arith`). The new parameter is
`s + 1 = 2 f(k) + 6`.
-/
theorem wl_xp_hard : ∀ P ∈ XP, FptReduces P paramWLProblem := by
  intro P hP
  obtain ⟨⟨Mκ, -, Cκ₀, d, hκ₀⟩, M, -, f, hf, hdec⟩ := hP
  obtain ⟨Cκ, hCκ⟩ : ∃ C, C = Cκ₀ * 2 ^ d := ⟨_, rfl⟩
  have hκ : ∀ x, ComputesWithin Mκ x (encodeNat (P.κ x)) (Cκ * x.length ^ d + Cκ) := fun x =>
    Main.Compose.computesWithin_mono' (hκ₀ x) (by
      rw [hCκ]
      calc Cκ₀ * (x.length + 1) ^ d ≤ Cκ₀ * (2 ^ d * x.length ^ d + 2 ^ d) :=
            Nat.mul_le_mul_left _ (succ_pow_le x.length d)
        _ = Cκ₀ * 2 ^ d * x.length ^ d + Cκ₀ * 2 ^ d := by ring)
  have hF : MachineComputable fun k => 2 * f k + 4 :=
    MachineComputable.add_const (MachineComputable.mul_const hf 2) 4
  obtain ⟨Mf, -, hMf, hT⟩ := MachineComputable.exists_time hF
  have hM' : Deterministic (Main.Compose.comp dropMachine M false fun _ => false).toMachine :=
    Main.AMachine.toMachine_deterministic _
  obtain ⟨c, hpipe⟩ := pipeline_language
  obtain ⟨R, -, Cp, hC⟩ := hpipe _ hM'
  obtain ⟨Mκ', hMκ'⟩ : ∃ Mκ', Mκ' = (Main.Compose.comp dropMachine Mκ false fun _ => false).toMachine :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (xpS Mκ' Mf).machine (xpS Mκ' Mf).depth := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (Main.Compose.comp (withSuffix D).compile R false fun _ => false).toMachine :=
    ⟨_, rfl⟩
  -- the time bound
  obtain ⟨E1, hE1⟩ : ∃ E1, E1 = 3 * (d + 1 + 1) + 1 := ⟨_, rfl⟩
  obtain ⟨K1, hK1⟩ : ∃ K1, K1 = xpK Mκ' Mf := ⟨_, rfl⟩
  obtain ⟨Kt, hKt⟩ : ∃ Kt, Kt = 64 * K1 * 3 ^ E1 + 2 * Cp * 64 ^ c + 400 := ⟨_, rfl⟩
  set H : ℕ → ℕ := fun k => xpG Mκ' Mf (fun k => 2 * f k + 4) (Cκ + 25) k with hH
  have hHc : MachineComputable H := by
    have := MachineComputable.add (MachineComputable.add_const (MachineComputable.add
      (MachineComputable.add (MachineComputable.add
        (MachineComputable.const (5 + simB Mκ' + simB Mf)) MachineComputable.id') hF) hT)
        (2 * (Cκ + 25))) (MachineComputable.mul_const (MachineComputable.add_const hF 1) 16)
    exact this
  have key : ∀ x : List Bool, ∃ z : List Bool, (x ∈ P.L ↔ z ∈ WLDistinguishing) ∧
      leadingNat z = 2 * f (P.κ x) + 6 ∧
      ComputesWithin (padTM Q).compile x z
        (Kt * H (P.κ x) ^ (3 + 2 * c) * (x.length + 1) ^ (E1 + 2 * c + 1)) := by
    intro x
    obtain ⟨n, hn⟩ : ∃ n, x.length = n := ⟨_, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k, P.κ x = k := ⟨_, rfl⟩
    obtain ⟨Fk, hFk⟩ : ∃ Fk, 2 * f k + 4 = Fk := ⟨_, rfl⟩
    have hyl : (true :: true :: x).length = n + 2 := by simp [hn]
    obtain ⟨a, ha⟩ : ∃ a, parA (n + 2) = a := ⟨_, rfl⟩
    have ha1 : 1 ≤ a := ha ▸ one_le_parA _
    have hapow : n + 2 + 2 ≤ 2 ^ a := ha ▸ le_pow_parA _
    have hapow' : 2 ^ a ≤ 2 * (n + 2 + 2) := ha ▸ pow_parA_le _
    have haln : a ≤ n + 2 + 2 := ha ▸ parA_le _
    -- the program
    have hκ' := xp_kappa_padded hκ x
    rw [← hMκ', hk] at hκ'
    have hDc := xp_prog (F := fun k => 2 * f k + 4) Mκ' Mf hMf hκ'
    rw [← hD, hyl] at hDc
    simp only [hFk, ha] at hDc
    have hW := withSuffix_computesWithin hDc
    -- the pipeline
    have hh2 : 2 ≤ Fk * a := by
      calc 2 ≤ Fk * 1 := by omega
        _ ≤ Fk * a := Nat.mul_le_mul_left _ ha1
    have hah : a ≤ Fk * a := Nat.le_mul_of_pos_left _ (by omega)
    have hpowh : 2 ^ a ≤ 2 ^ (Fk * a) := Nat.pow_le_pow_right (by norm_num) hah
    have hFa : Fk ≤ Fk * a := Nat.le_mul_of_pos_right _ ha1
    obtain ⟨G₀, G₁, hacc, hlead, -, hcomp⟩ := hC (true :: true :: x) (Fk * a) (Fk + 1)
      (by rw [hyl]; omega) hh2 (by rw [hyl]; omega) (by omega) (by omega)
    refine ⟨encodeWLInstance (Fk + 1 + 1) G₀ G₁, ?_, ?_, ?_⟩
    · -- correctness
      have hdec' := xp_padded_decides hdec x
      rw [hn, hk, hFk] at hdec'
      have htime : (n + 4) ^ Fk ≤ 2 ^ (Fk * a) := by
        rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left (by omega) Fk
      have hhalt : (runOn (Main.Compose.comp dropMachine M false fun _ => false).toMachine
          (true :: true :: x) (2 ^ (Fk * a))).answer.isSome := by
        obtain ⟨b, hb, -⟩ := Main.decidesWithin_mono hdec' htime
        simp [hb]
      rw [← hacc hhalt]
      exact (Main.accepts_iff_of_decidesWithin hdec').symm
    · rw [hlead, hk]; omega
    · -- the time bound
      have hQc := Main.Compose.compose_computesWithin (withSuffix D).compile R false
        (fun _ => false) (x := true :: true :: x) (by simp) hW hcomp
      rw [← hQ] at hQc
      have hfin := padTM_computesWithin hQc
      refine Main.Compose.computesWithin_mono' hfin ?_
      rw [hyl, hn, hk]
      have hwid := xp_width_le n Fk
      rw [ha] at hwid
      have hℓ : 2 ^ packedWidth (true :: true :: x).length (Fk * a) (Fk + 1) ≤ 4 * (n + 4) := by
        rw [hyl]
        calc 2 ^ packedWidth (n + 2) (Fk * a) (Fk + 1) ≤ 2 ^ (a + 1) :=
              Nat.pow_le_pow_right (by norm_num) hwid
          _ = 2 * 2 ^ a := by ring
          _ ≤ 4 * (n + 4) := by omega
      have hP : (Fk + 1) * 2 ^ packedWidth (true :: true :: x).length (Fk * a) (Fk + 1) *
          (Fk * a + 1) ≤ 64 * (Fk + 1) ^ 2 * (n + 1) ^ 2 := by
        have h1 : Fk * a + 1 ≤ (Fk + 1) * (n + 4) := by
          have : Fk * a ≤ Fk * (n + 4) := Nat.mul_le_mul_left _ (by omega)
          have e : (Fk + 1) * (n + 4) = Fk * (n + 4) + (n + 4) := by ring
          omega
        calc (Fk + 1) * 2 ^ packedWidth (true :: true :: x).length (Fk * a) (Fk + 1) *
              (Fk * a + 1) ≤ (Fk + 1) * (4 * (n + 4)) * ((Fk + 1) * (n + 4)) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ hℓ) h1
          _ = 4 * (Fk + 1) ^ 2 * (n + 4) ^ 2 := by ring
          _ ≤ 4 * (Fk + 1) ^ 2 * (4 * (n + 1)) ^ 2 :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
          _ = 64 * (Fk + 1) ^ 2 * (n + 1) ^ 2 := by ring
      have hHk : Fk + 1 ≤ H k := by
        simp only [hH, xpG]; rw [hFk]; omega
      have hH1 : 1 ≤ H k := by omega
      have htD : xpK Mκ' Mf * xpG Mκ' Mf (fun k => 2 * f k + 4) (Cκ + 25) k ^ 3 *
          (n + 2 + 1) ^ (3 * (d + 1 + 1) + 1) ≤ K1 * H k ^ 3 * (n + 2 + 1) ^ E1 := by
        rw [hK1, hE1]
      rw [hyl] at hP
      have htot := xp_total_arith (n := n) (Cp := Cp) (c := c) hHk hH1 htD hP
      rw [hKt]
      exact htot
  choose red h1 h2 h3 using key
  refine ⟨red, h1, ⟨(padTM Q).compile, padTM_deterministic Q, fun k => Kt * H k ^ (3 + 2 * c),
    MachineComputable.mul_const (MachineComputable.pow_const hHc _) Kt, E1 + 2 * c + 1, h3⟩,
    ⟨fun k => 2 * f k + 6, MachineComputable.add_const (MachineComputable.mul_const hf 2) 6,
      fun x => (h2 x).le⟩⟩

end Lax119563Proofs.Hardness
