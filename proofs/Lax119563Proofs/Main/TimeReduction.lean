import Lax119563Proofs.Hardness.Pipeline
import Lax119563Proofs.Hardness.HorizonMachine

/-!
# The quasi-linear reduction from `DTIME(n^s)` to `(s+1)`-WL Distinguishing

The reduction of the time lower bound at fixed dimension (paper, "The time lower bound at
fixed dimension"). For a decider running within `C₀ n^s + C₀` steps, take the horizon
`h = s ⌈log₂ (n + 2)⌉ + c₀` with `2^{c₀} ≥ C₀`, so that `2^h ≥ C₀ n^s + C₀`. The packed
representation with `s` data blocks has block width `ℓ = packedWidth n h s ≤ ⌈log₂(n+2)⌉ + c₀ + 2`,
so `2^ℓ = O(n)` and `h = O(log n)`.

* `pipeline_fine`: the generator of `packed_representation` followed by the machine of
  `matrix_compiler` computes `encodeGraphPair G₀ G₁` from `encodeNats [h, s] ++ x` within
  `C 2^ℓ (h+1)^c` steps with an absolute exponent `c` (the matrix compiler's polylogarithmic
  factor is a power of `log₂ (H + S + 2) = O(h)`).
* `time_reduction`: preceded by the horizon machine (`Hardness.horizon_machine`), this is a
  reduction running in time `C n (log n)^c`, whose output thus has length `≤ C n (log n)^c`.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime Lax119563.ImplicitSystemEncodings
  Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.PackedRepresentation
open Lax489179.TuringMachine (Machine Deterministic)
open Lax119563Proofs.Hardness

namespace Lax119563Proofs.Main

/-! ## The pipeline with a quasi-linear time bound -/

lemma packedWidth_le_succ {n h s : ℕ} (hn : n ≤ 2 ^ h) (hh : 1 ≤ h) (hs : 2 ≤ s) :
    packedWidth n h s ≤ h + 1 := by
  unfold packedWidth
  refine max_le ?_ ?_
  · refine Nat.clog_le_of_le_pow ?_
    have : 2 ≤ 2 ^ h := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
    rw [pow_succ]; omega
  · refine Nat.div_le_of_le_mul ?_
    have : 2 * h ≤ s * h := Nat.mul_le_mul_right _ hs
    have e : s * (h + 1) = s * h + s := by ring
    omega

/-- `log₂ N = O(Y)` for `N ≤ A 2^ℓ Y^d` with `ℓ ≤ Y`. -/
lemma log_le_of_le {N A ℓ Y d : ℕ} (hN : N ≤ A * (2 ^ ℓ * Y ^ d)) (hℓ : ℓ ≤ Y) (hY1 : 1 ≤ Y) :
    Nat.log 2 N ≤ (A + d + 1) * Y := by
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · simp
  have hA : A < 2 ^ A := Nat.lt_two_pow_self
  have hY : Y ^ d ≤ 2 ^ (Y * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have hlt : N < 2 ^ (A + ℓ + Y * d) := by
    have h1 : A * (2 ^ ℓ * Y ^ d) < 2 ^ A * (2 ^ ℓ * 2 ^ (Y * d)) :=
      Nat.mul_lt_mul_of_lt_of_le hA (Nat.mul_le_mul_left _ hY) (by positivity)
    rw [pow_add, pow_add]
    calc N ≤ A * (2 ^ ℓ * Y ^ d) := hN
      _ < 2 ^ A * (2 ^ ℓ * 2 ^ (Y * d)) := h1
      _ = 2 ^ A * 2 ^ ℓ * 2 ^ (Y * d) := by ring
  have := Nat.log_lt_of_lt_pow (by omega) hlt
  have e : (A + d + 1) * Y = A * Y + Y * d + Y := by ring
  have : A ≤ A * Y := Nat.le_mul_of_pos_right _ hY1
  omega

/-- The time bound of the fine pipeline. -/
lemma fine_time_arith {n s h ℓ T1 H S T2 xin Cs Cc cp cc : ℕ}
    (hs : s ≤ h + 2) (hℓ : ℓ ≤ h + 1) (hn : n ≤ 2 ^ ℓ)
    (hxin : xin ≤ 2 * h + 1 + (2 * s + 1) + n)
    (hT1 : T1 ≤ Cs * s * 2 ^ ℓ * (h + 1) ^ cp) (hH : H ≤ xin + T1)
    (hS : S ≤ 5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 * 2 ^ ℓ * (ℓ + 1))
    (hT2 : T2 ≤ Cc * (H + S) * Nat.log 2 (H + S + 2) ^ cc) :
    2 * T1 + T2 + 3 ≤
      (4 * Cs + Cc * (9 + 92 * Cs) * (9 + 92 * Cs + (cp + 5) + 1) ^ cc + 3) * 2 ^ ℓ *
        (h + 1) ^ (cp + 5 + cc) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = h + 1 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2 ^ ℓ := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = Q * Y ^ (cp + 5) := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := by omega
  have hQ1 : 1 ≤ Q := hQ ▸ Nat.one_le_two_pow
  have hYk : ∀ k, k ≤ cp + 5 → Q * Y ^ k ≤ P := fun k hk =>
    hP ▸ Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 hk)
  rw [← hQ] at hn hT1 hS ⊢
  rw [← hY] at hT1 hS ⊢
  have hs' : s ≤ 2 * Y := by omega
  -- T1
  have hT1' : T1 ≤ 2 * Cs * P := by
    calc T1 ≤ Cs * s * Q * Y ^ cp := hT1
      _ ≤ Cs * (2 * Y) * Q * Y ^ cp :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hs'))
      _ = 2 * Cs * (Q * Y ^ (cp + 1)) := by ring
      _ ≤ 2 * Cs * P := Nat.mul_le_mul_left _ (hYk _ (by omega))
  -- xin
  have hxin' : xin ≤ 7 * P := by
    have h1 : Y ≤ Q * Y ^ 1 := by simpa using Nat.mul_le_mul_right Y hQ1
    have := hYk 1 (by omega)
    have := hYk 0 (by omega)
    simp at this
    omega
  -- S
  have hS' : S ≤ 90 * Cs * P := by
    calc S ≤ 5 * (Cs * Y ^ 2) * (s + 1) ^ 2 * Q * (ℓ + 1) := hS
      _ ≤ 5 * (Cs * Y ^ 2) * (3 * Y) ^ 2 * Q * (2 * Y) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
            (Nat.pow_le_pow_left (by omega) _))) (by omega)
      _ = 90 * Cs * (Q * Y ^ 5) := by ring
      _ ≤ 90 * Cs * P := Nat.mul_le_mul_left _ (hYk _ (by omega))
  have hHS : H + S + 2 ≤ (9 + 92 * Cs) * P := by
    have : 1 ≤ P := le_trans (by simpa using hQ1) (hYk 0 (by omega))
    have e : (9 + 92 * Cs) * P = 9 * P + 92 * Cs * P := by ring
    have e2 : 92 * Cs * P = 2 * Cs * P + 90 * Cs * P := by ring
    omega
  obtain ⟨A, hA⟩ : ∃ A, A = 9 + 92 * Cs := ⟨_, rfl⟩
  rw [← hA] at hHS ⊢
  have hlog : Nat.log 2 (H + S + 2) ≤ (A + (cp + 5) + 1) * Y :=
    log_le_of_le (hHS.trans_eq (by rw [hP, hQ])) (by omega) hY1
  have hT2' : T2 ≤ Cc * A * (A + (cp + 5) + 1) ^ cc * (P * Y ^ cc) := by
    calc T2 ≤ Cc * (H + S) * Nat.log 2 (H + S + 2) ^ cc := hT2
      _ ≤ Cc * (A * P) * ((A + (cp + 5) + 1) * Y) ^ cc :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left hlog _)
      _ = _ := by rw [mul_pow]; ring
  have hPY : P ≤ P * Y ^ cc := Nat.le_mul_of_pos_right _ (by positivity)
  have e : (4 * Cs + Cc * A * (A + (cp + 5) + 1) ^ cc + 3) * Q * Y ^ (cp + 5 + cc) =
      4 * Cs * (P * Y ^ cc) + Cc * A * (A + (cp + 5) + 1) ^ cc * (P * Y ^ cc) +
        3 * (P * Y ^ cc) := by rw [hP]; ring
  rw [e]
  have h1 : 2 * Cs * P ≤ 2 * Cs * (P * Y ^ cc) := Nat.mul_le_mul_left _ hPY
  have h2 : 1 ≤ P := le_trans (by simpa using hQ1) (hYk 0 (by omega))
  have e3 : 4 * Cs * (P * Y ^ cc) = 2 * (2 * Cs * (P * Y ^ cc)) := by ring
  omega

/-- **The pipeline with a quasi-linear time bound**: the packed generator followed by the
matrix compiler, without the leading dimension. -/
theorem pipeline_fine : ∃ c : ℕ, ∀ M : Machine, Deterministic M →
    ∃ R : Machine, Deterministic R ∧ ∃ C : ℕ,
      ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s →
        s ≤ h + 2 →
        ∃ G₀ G₁ : ColoredGraph,
          ((runOn M x (2 ^ h)).answer.isSome → (Accepts M x ↔ Distinguishes (s + 1) G₀ G₁)) ∧
          ComputesWithin R (encodeNats [h, s] ++ x) (encodeGraphPair G₀ G₁)
            (C * 2 ^ packedWidth x.length h s * (h + 1) ^ c) := by
  obtain ⟨cp, hpack⟩ := packed_representation
  obtain ⟨compile, ⟨Cn, hgame⟩, ⟨Mc, -, Cc, cc, hMc⟩⟩ := matrix_compiler
  refine ⟨cp + 5 + cc, fun M hM => ?_⟩
  obtain ⟨sys, Cs, hsys, Rp, -, hRp⟩ := hpack M hM
  refine ⟨(Compose.comp Rp Mc false fun _ => false).toMachine,
    AMachine.toMachine_deterministic _,
    4 * Cs + Cc * (9 + 92 * Cs) * (9 + 92 * Cs + (cp + 5) + 1) ^ cc + 3,
    fun x h s hx hh hxh hs hsh => ?_⟩
  have hℓ1 := one_le_packedWidth x.length h s
  have hQ := length_add_two_le x.length h s
  obtain ⟨hcorr, hloc, hsch⟩ := hsys x h s hx hh hxh hs hsh
  obtain ⟨Ck, hCk⟩ := hgame (s + 1) (by omega)
  obtain ⟨hsp, hdu, -, -⟩ := hCk _ hℓ1 (sys x h s)
  have hSz : matrixSize (sys x h s) ≤ 5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 *
      2 ^ packedWidth x.length h s * (packedWidth x.length h s + 1) :=
    (sizeParameter_le _).trans (size_arith hloc hsch)
  refine ⟨(compile (sys x h s)).1, (compile (sys x h s)).2, fun hhalt => ?_, ?_⟩
  · exact (hcorr hhalt).symm.trans
      (Hardness.distinguishes_iff_conflict (by omega) _ hsp hdu).symm
  · have h1 := hRp x h s hx hh hxh hs hsh
    have h2 := hMc (s + 1) (by omega) _ hℓ1 (sys x h s)
    have hxin2 : 2 ≤ (encodeNats [h, s] ++ x).length := by simp; omega
    have hc := Compose.compose_computesWithin Rp Mc false (fun _ => false) hxin2 h1 h2
    refine Compose.computesWithin_mono' hc ?_
    have hxin : (encodeNats [h, s] ++ x).length ≤ 2 * h + 1 + (2 * s + 1) + x.length := by
      have e1 := length_encodeNat_le h
      have e2 := length_encodeNat_le s
      simp only [encodeNats, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_append]
      omega
    have hH := length_le_of_computesWithin h1
    exact fine_time_arith hsh (packedWidth_le_succ hxh (by omega) hs) (by omega)
      hxin le_rfl hH hSz le_rfl

/-! ## The reduction -/

lemma parA_le_log {n : ℕ} (hn : 2 ≤ n) : parA n ≤ Nat.log 2 n + 2 := by
  unfold parA
  refine Nat.clog_le_of_le_pow ?_
  have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  rw [pow_succ] at h1 ⊢
  rw [pow_succ]
  have : 1 ≤ 2 ^ Nat.log 2 n := Nat.one_le_two_pow
  omega

lemma one_le_log {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Nat.log 2 n :=
  Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)

lemma packedWidth_le_horizon (n s a c₀ : ℕ) (hs : 1 ≤ s) (ha : Nat.clog 2 (n + 2) = a) :
    packedWidth n (s * a + c₀) s ≤ a + c₀ + 2 := by
  unfold packedWidth
  refine max_le (by omega) (Nat.div_le_of_le_mul ?_)
  have : c₀ ≤ s * c₀ := Nat.le_mul_of_pos_left _ hs
  have e : s * (a + c₀ + 2) = s * a + s * c₀ + 2 * s := by ring
  omega

/-- The halting bound: `C₀ n^s + C₀ ≤ 2^{s a + c₀}` for `n + 2 ≤ 2^a` and `C₀ < 2^{c₀}`. -/
lemma halt_le {C₀ n s a c₀ : ℕ} (hs : 1 ≤ s) (ha : n + 2 ≤ 2 ^ a) (hc : C₀ ≤ 2 ^ c₀) :
    C₀ * n ^ s + C₀ ≤ 2 ^ (s * a + c₀) := by
  have h1 : n ^ s < (n + 2) ^ s := Nat.pow_lt_pow_left (by omega) (by omega)
  have h2 : (n + 2) ^ s ≤ (2 ^ a) ^ s := Nat.pow_le_pow_left ha _
  have e : 2 ^ (s * a + c₀) = (2 ^ a) ^ s * 2 ^ c₀ := by rw [pow_add, ← pow_mul, mul_comm a s]
  rw [e]
  calc C₀ * n ^ s + C₀ = C₀ * (n ^ s + 1) := by ring
    _ ≤ 2 ^ c₀ * (2 ^ a) ^ s := Nat.mul_le_mul hc (by omega)
    _ = _ := by ring

/-- The time bound of the reduction. -/
lemma red_arith {n Lg a TP TR KP Cf E B cf : ℕ} (hn : 1 ≤ n) (hLg : 1 ≤ Lg)
    (ha : a + 1 ≤ 4 * Lg) (hTP : TP ≤ KP * (n + 1) * (a + 1) ^ 2)
    (hTR : TR ≤ Cf * (E * n) * (B * Lg) ^ cf) :
    n + (2 * TP + TR + 3) ≤ (64 * KP + Cf * E * B ^ cf + 4) * n * Lg ^ (cf + 2) := by
  obtain ⟨W, hW⟩ : ∃ W, W = n * Lg ^ (cf + 2) := ⟨_, rfl⟩
  have hL2 : Lg ^ 2 ≤ Lg ^ (cf + 2) := Nat.pow_le_pow_right hLg (by omega)
  have hLc : Lg ^ cf ≤ Lg ^ (cf + 2) := Nat.pow_le_pow_right hLg (by omega)
  have hnW : n ≤ W := hW ▸ Nat.le_mul_of_pos_right _ (by positivity)
  have hTP' : TP ≤ 32 * KP * W := by
    calc TP ≤ KP * (2 * n) * (4 * Lg) ^ 2 :=
          hTP.trans (Nat.mul_le_mul (Nat.mul_le_mul_left KP (show n + 1 ≤ 2 * n by omega))
            (Nat.pow_le_pow_left ha 2))
      _ = 32 * KP * (n * Lg ^ 2) := by ring
      _ ≤ 32 * KP * W := Nat.mul_le_mul_left _ (hW ▸ Nat.mul_le_mul_left _ hL2)
  have hTR' : TR ≤ Cf * E * B ^ cf * W := by
    calc TR ≤ Cf * (E * n) * (B * Lg) ^ cf := hTR
      _ = Cf * E * B ^ cf * (n * Lg ^ cf) := by rw [mul_pow]; ring
      _ ≤ Cf * E * B ^ cf * W := Nat.mul_le_mul_left _ (hW ▸ Nat.mul_le_mul_left _ hLc)
  have e : (64 * KP + Cf * E * B ^ cf + 4) * n * Lg ^ (cf + 2) =
      2 * (32 * KP * W) + Cf * E * B ^ cf * W + 4 * W := by rw [hW]; ring
  omega

/-- **The quasi-linear reduction from `DTIME(n^s)` to `(s+1)`-WL Distinguishing** (with an
absolute exponent `c`). The output length is bounded by the running time. -/
theorem time_reduction : ∃ c : ℕ, ∀ s : ℕ, 2 ≤ s → ∀ M : Machine, Deterministic M →
    (∃ C₀ : ℕ, ∀ x : List Bool, (runOn M x (C₀ * x.length ^ s + C₀)).answer.isSome) →
    ∃ R : Machine, Deterministic R ∧ ∃ C : ℕ, ∀ x : List Bool, 2 ≤ x.length →
      ∃ G₀ G₁ : ColoredGraph,
        (Accepts M x ↔ Distinguishes (s + 1) G₀ G₁) ∧
        (encodeGraphPair G₀ G₁).length ≤ C * x.length * Nat.log 2 x.length ^ c ∧
        ComputesWithin R x (encodeGraphPair G₀ G₁) (C * x.length * Nat.log 2 x.length ^ c) := by
  obtain ⟨cf, hfine⟩ := pipeline_fine
  refine ⟨cf + 2, fun s hs M hM ⟨C₀, hC₀⟩ => ?_⟩
  obtain ⟨Rf, -, Cf, hRf⟩ := hfine M hM
  obtain ⟨Pm, -, KP, hP⟩ := horizon_machine s (C₀ + 2)
  refine ⟨(Compose.comp Pm Rf false fun _ => false).toMachine,
    AMachine.toMachine_deterministic _,
    64 * KP + Cf * 2 ^ (C₀ + 2 + 4) * (3 * s + (C₀ + 2) + 1) ^ cf + 4, fun x hx => ?_⟩
  obtain ⟨a, ha⟩ : ∃ a, a = parA x.length := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := ha ▸ one_le_parA _
  have hapow : x.length + 2 ≤ 2 ^ a := ha ▸ le_pow_parA _
  have hapow' : 2 ^ a ≤ 2 * (x.length + 2) := ha ▸ pow_parA_le _
  have hsa : s ≤ s * a := Nat.le_mul_of_pos_right _ ha1
  have hxh : x.length ≤ 2 ^ (s * a + (C₀ + 2)) :=
    le_trans (by omega) (Nat.pow_le_pow_right (by norm_num) (show a ≤ s * a + (C₀ + 2) by
      have : a ≤ s * a := Nat.le_mul_of_pos_left _ (by omega)
      omega))
  obtain ⟨G₀, G₁, hacc, hcomp⟩ := hRf x (s * a + (C₀ + 2)) s hx (by omega) hxh hs (by omega)
  -- the machine halts within `2^h` steps
  have hhalt : (runOn M x (2 ^ (s * a + (C₀ + 2)))).answer.isSome := by
    have hle := halt_le (C₀ := C₀) (n := x.length) (s := s) (c₀ := C₀ + 2) (by omega) hapow
      (le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [runOn_eq_of_le M x hle (hC₀ x)]
    exact hC₀ x
  -- the reduction
  have hPx := hP x
  rw [← ha] at hPx
  have hred := Compose.compose_computesWithin Pm Rf false (fun _ => false) hx hPx hcomp
  obtain ⟨Lg, hLg⟩ : ∃ Lg, Lg = Nat.log 2 x.length := ⟨_, rfl⟩
  have hLg1 : 1 ≤ Lg := hLg ▸ one_le_log hx
  have haL : a ≤ Lg + 2 := ha ▸ hLg ▸ parA_le_log hx
  have hℓ : packedWidth x.length (s * a + (C₀ + 2)) s ≤ a + (C₀ + 2) + 2 :=
    packedWidth_le_horizon _ _ _ _ (by omega) ha.symm
  have hQ : 2 ^ packedWidth x.length (s * a + (C₀ + 2)) s ≤ 2 ^ (C₀ + 2 + 4) * x.length := by
    calc 2 ^ packedWidth x.length (s * a + (C₀ + 2)) s ≤ 2 ^ (a + (C₀ + 2) + 2) :=
          Nat.pow_le_pow_right (by norm_num) hℓ
      _ = 2 ^ a * 2 ^ (C₀ + 2 + 2) := by rw [← pow_add]; ring_nf
      _ ≤ (4 * x.length) * 2 ^ (C₀ + 2 + 2) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (C₀ + 2 + 4) * x.length := by rw [pow_add 2 (C₀ + 2) 4, pow_add 2 (C₀ + 2) 2]; ring
  have hY : s * a + (C₀ + 2) + 1 ≤ (3 * s + (C₀ + 2) + 1) * Lg := by
    have : s * a ≤ s * (3 * Lg) := Nat.mul_le_mul_left _ (by omega)
    have e : (3 * s + (C₀ + 2) + 1) * Lg = s * (3 * Lg) + (C₀ + 2 + 1) * Lg := by ring
    have : (C₀ + 2 + 1) * 1 ≤ (C₀ + 2 + 1) * Lg := Nat.mul_le_mul_left _ hLg1
    omega
  have hTR : Cf * 2 ^ packedWidth x.length (s * a + (C₀ + 2)) s * (s * a + (C₀ + 2) + 1) ^ cf ≤
      Cf * (2 ^ (C₀ + 2 + 4) * x.length) * ((3 * s + (C₀ + 2) + 1) * Lg) ^ cf :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hQ) (Nat.pow_le_pow_left hY _)
  have hT := red_arith (n := x.length) (a := a) (Lg := Lg) (KP := KP) (by omega) hLg1 (by omega)
    le_rfl hTR
  rw [← hLg]
  have hlen := length_le_of_computesWithin hred
  refine ⟨G₀, G₁, ?_, ?_, Compose.computesWithin_mono' hred ?_⟩
  · rw [hacc hhalt]
  · omega
  · omega

end Lax119563Proofs.Main
