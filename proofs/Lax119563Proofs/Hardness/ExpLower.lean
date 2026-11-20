import Lax119563.ExponentialLowerBound
import Lax119563.ExponentialTimeHierarchy
import Lax119563Proofs.Hardness.ParMachine
import Lax119563Proofs.Hardness.PipelineLen
import Lax119563Proofs.Hardness.ExpAsymptotics

/-!
# The exponential time lower bound for WL Distinguishing

By the exponential time hierarchy theorem there is a language `L` decidable in time `O(2^n)`
but not in time `O(2^{n/4})`. For an input `x` of length `n ≥ 2` choose the horizon
`h = n + c₀` (so that the decider of `L` halts within `2^h` steps), `a = ⌈log₂ (n + 2)⌉` and
the least `s` with `s a ≥ h + 2`. Then the packed width is `a`, and the pipeline produces
in polynomial time an instance of length `N = O((h + 4)^5)` (`pipeline_len`; the matrix
compiler's output has length `O(S log S)`, and here `S = O(h^4 2^a / a)`).
A decider for WL Distinguishing running in time `O(2^{ε N^{1/5}})` with `ε` small would then
decide `L` in time `O(2^{n/4})`.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime Lax119563.WLProblems Lax119563.PackedRepresentation
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

/-! ## Arithmetic -/

/-- The length bound: the instance has length `O(m^5)`. The factor `log₂ S = O(a)` of the
encoding is absorbed by `(s + 1) a = O(m)`. -/
lemma exp_len_arith {Cl Cs n s a h m c₀ : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ n + 2) (hn2 : n + 2 ≤ 2 ^ a)
    (h2a : 2 ^ a ≤ 2 * (n + 2)) (hsa : s * a ≤ h + 2 + a) (hs : s + 1 ≤ h + 3)
    (hh : h = n + c₀) (hm : m = h + 4) :
    2 * (s + 1) + 1 + Cl * (Cs * (h + 1) ^ 2 * (s + 1) ^ 2 * 2 ^ a * (a + 1) + 1) *
      (Nat.log 2 (Cs * (h + 1) ^ 2 * (s + 1) ^ 2 * 2 ^ a * (a + 1) + 2) + 1) ≤
      (Cl * (2 * Cs + 6 * c₀ + 21) * (36 * Cs + 1) + 3) * m ^ 5 := by
  obtain ⟨Sb, hSb⟩ : ∃ Sb, Sb = Cs * (h + 1) ^ 2 * (s + 1) ^ 2 * 2 ^ a * (a + 1) := ⟨_, rfl⟩
  rw [← hSb]
  have hm1 : 1 ≤ m := by omega
  have ham : a + 1 ≤ m := by omega
  -- (i) a crude bound for the logarithm
  have hSb6 : Sb + 2 ≤ (2 * Cs + 2) * m ^ 6 := by
    have h1 : (h + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : (s + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h3 : 2 ^ a ≤ 2 * m := by omega
    have h4 : Sb ≤ Cs * m ^ 2 * m ^ 2 * (2 * m) * m := by
      rw [hSb]
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2) h3) ham
    have e : Cs * m ^ 2 * m ^ 2 * (2 * m) * m = 2 * Cs * m ^ 6 := by ring
    have h5 : 1 ≤ m ^ 6 := Nat.one_le_pow _ _ hm1
    have e2 : (2 * Cs + 2) * m ^ 6 = 2 * Cs * m ^ 6 + 2 * m ^ 6 := by ring
    omega
  -- (ii) `m ≤ 2^{a + c₀ + 2}`
  have hmp : m ≤ 2 ^ (a + (c₀ + 2)) := by
    have h1 : c₀ + 2 < 2 ^ (c₀ + 2) := Nat.lt_two_pow_self
    have h2 : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha1
    have h3 : 4 ≤ 2 ^ (c₀ + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (c₀ + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_add]
    have : 2 ^ a + 2 ^ (c₀ + 2) ≤ 2 ^ a * 2 ^ (c₀ + 2) := by nlinarith
    omega
  -- (iii) `log₂ (S + 2) + 1 ≤ K₁ a`
  have hlog : Nat.log 2 (Sb + 2) + 1 ≤ (2 * Cs + 6 * c₀ + 21) * a := by
    have h1 : Sb + 2 < 2 ^ (2 * Cs + 2 + 6 * (a + (c₀ + 2))) := by
      have hA : 2 * Cs + 2 < 2 ^ (2 * Cs + 2) := Nat.lt_two_pow_self
      have hB : m ^ 6 ≤ 2 ^ (6 * (a + (c₀ + 2))) := by
        rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left hmp 6
      have hB1 : 1 ≤ m ^ 6 := Nat.one_le_pow _ _ hm1
      calc Sb + 2 ≤ (2 * Cs + 2) * m ^ 6 := hSb6
        _ < 2 ^ (2 * Cs + 2) * 2 ^ (6 * (a + (c₀ + 2))) :=
          Nat.mul_lt_mul_of_lt_of_le hA hB (by omega)
        _ = _ := by rw [← pow_add]
    have h2 := Nat.log_lt_of_lt_pow (by omega) h1
    have h3 : (2 * Cs + 6 * c₀ + 15) * 1 ≤ (2 * Cs + 6 * c₀ + 15) * a :=
      Nat.mul_le_mul_left _ ha1
    have e : (2 * Cs + 6 * c₀ + 21) * a = (2 * Cs + 6 * c₀ + 15) * a + 6 * a := by ring
    omega
  -- (iv) `(S + 1) a = O(m^5)`
  have hSa : (Sb + 1) * a ≤ (36 * Cs + 1) * m ^ 5 := by
    have hsa' : (s + 1) * a ≤ 3 * m := by
      have : (s + 1) * a = s * a + a := by ring
      omega
    have h1 : (s + 1) ^ 2 * (a + 1) * a ≤ 18 * m ^ 2 := by
      calc (s + 1) ^ 2 * (a + 1) * a ≤ (s + 1) ^ 2 * (2 * a) * a :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
        _ = 2 * ((s + 1) * a) ^ 2 := by ring
        _ ≤ 2 * (3 * m) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsa' 2)
        _ = 18 * m ^ 2 := by ring
    have h2 : Sb * a ≤ 36 * Cs * m ^ 5 := by
      calc Sb * a = Cs * (h + 1) ^ 2 * 2 ^ a * ((s + 1) ^ 2 * (a + 1) * a) := by rw [hSb]; ring
        _ ≤ Cs * m ^ 2 * (2 * m) * (18 * m ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _
            (Nat.pow_le_pow_left (by omega) 2)) (by omega)) h1
        _ = 36 * Cs * m ^ 5 := by ring
    have h3 : a ≤ m ^ 5 := le_trans (by omega) (Nat.le_self_pow (by norm_num) m)
    have e : (Sb + 1) * a = Sb * a + a := by ring
    have e2 : (36 * Cs + 1) * m ^ 5 = 36 * Cs * m ^ 5 + m ^ 5 := by ring
    omega
  have hfin : Cl * (Sb + 1) * (Nat.log 2 (Sb + 2) + 1) ≤
      Cl * (2 * Cs + 6 * c₀ + 21) * (36 * Cs + 1) * m ^ 5 := by
    calc Cl * (Sb + 1) * (Nat.log 2 (Sb + 2) + 1)
        ≤ Cl * (Sb + 1) * ((2 * Cs + 6 * c₀ + 21) * a) := Nat.mul_le_mul_left _ hlog
      _ = Cl * (2 * Cs + 6 * c₀ + 21) * ((Sb + 1) * a) := by ring
      _ ≤ Cl * (2 * Cs + 6 * c₀ + 21) * ((36 * Cs + 1) * m ^ 5) := Nat.mul_le_mul_left _ hSa
      _ = _ := by ring
  have hs3 : 2 * (s + 1) + 1 ≤ 3 * m ^ 5 := by
    have : m ≤ m ^ 5 := Nat.le_self_pow (by norm_num) m
    omega
  exact (Nat.add_le_add hs3 hfin).trans (le_of_eq (by ring))

/-- The time of the reduction: polynomial in `m`. -/
lemma exp_time_arith {tP tR KP CR c s ℓ h m : ℕ} (htP : tP ≤ KP * m ^ 3)
    (htR : tR ≤ CR * (s * 2 ^ ℓ * (h + 1)) ^ c) (hs : s ≤ m) (hℓ : 2 ^ ℓ ≤ 2 * m)
    (hh : h + 1 ≤ m) (hm : 1 ≤ m) :
    2 * tP + tR + 3 ≤ (2 * KP + CR * 2 ^ c + 3) * m ^ (3 * c + 3) := by
  have h1 : s * 2 ^ ℓ * (h + 1) ≤ 2 * m ^ 3 := by
    calc s * 2 ^ ℓ * (h + 1) ≤ m * (2 * m) * m := Nat.mul_le_mul (Nat.mul_le_mul hs hℓ) hh
      _ = 2 * m ^ 3 := by ring
  have h2 : tR ≤ CR * 2 ^ c * m ^ (3 * c) := by
    calc tR ≤ CR * (2 * m ^ 3) ^ c := htR.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 c))
      _ = CR * 2 ^ c * m ^ (3 * c) := by rw [mul_pow, ← pow_mul, mul_comm 3 c, mul_assoc]
  have p1 : m ^ 3 ≤ m ^ (3 * c + 3) := Nat.pow_le_pow_right hm (by omega)
  have p2 : m ^ (3 * c) ≤ m ^ (3 * c + 3) := Nat.pow_le_pow_right hm (by omega)
  have p3 : 1 ≤ m ^ (3 * c + 3) := Nat.one_le_pow _ _ hm
  have q1 : KP * m ^ 3 ≤ KP * m ^ (3 * c + 3) := Nat.mul_le_mul_left _ p1
  have q2 : CR * 2 ^ c * m ^ (3 * c) ≤ CR * 2 ^ c * m ^ (3 * c + 3) := Nat.mul_le_mul_left _ p2
  have e : (2 * KP + CR * 2 ^ c + 3) * m ^ (3 * c + 3) =
      2 * (KP * m ^ (3 * c + 3)) + CR * 2 ^ c * m ^ (3 * c + 3) + 3 * m ^ (3 * c + 3) := by ring
  omega

/-- The final estimate of the running time of the composed decider. -/
lemma exp_final_arith (t₁ t₂ A d CW E Q m : ℕ) (X Y Z : ℝ) (hX : 0 ≤ X) (_hZ0 : 0 ≤ Z)
    (ht₁ : t₁ ≤ A * m ^ d) (ht₂ : (t₂ : ℝ) ≤ CW * Y + CW) (hY : Y ≤ Z)
    (hmZ : (m : ℝ) ^ d ≤ Q * Z) (hZ : Z ≤ E * X) :
    ((2 * t₁ + t₂ + 3 : ℕ) : ℝ) ≤
      ((2 * A * Q * E + CW * E + CW + 3 : ℕ) : ℝ) * X + ((2 * A * Q * E + CW * E + CW + 3 : ℕ) : ℝ) := by
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hE : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hCW : (0 : ℝ) ≤ CW := Nat.cast_nonneg _
  have h1 : (t₁ : ℝ) ≤ A * Q * E * X := by
    have : (t₁ : ℝ) ≤ A * (m : ℝ) ^ d := by exact_mod_cast ht₁
    calc (t₁ : ℝ) ≤ A * (m : ℝ) ^ d := this
      _ ≤ A * (Q * Z) := by gcongr
      _ ≤ A * (Q * (E * X)) := by gcongr
      _ = A * Q * E * X := by ring
  have h2 : (t₂ : ℝ) ≤ CW * E * X + CW := by
    calc (t₂ : ℝ) ≤ CW * Y + CW := ht₂
      _ ≤ CW * (E * X) + CW := by gcongr; exact hY.trans hZ
      _ = CW * E * X + CW := by ring
  have hK : (0 : ℝ) ≤ (CW + 3) * X := by positivity
  have hK' : (0 : ℝ) ≤ 2 * A * Q * E + CW * E := by positivity
  push_cast
  have e : (2 * (A : ℝ) * Q * E + CW * E + CW + 3) * X = 2 * (A * Q * E * X) + CW * E * X +
      (CW + 3) * X := by ring
  rw [e]
  linarith

/-! ## The theorem -/

/-- `⌊C 2^n + C⌋₊ ≤ 2^{n + c₀}` for `c₀ = 2 C + 2`. -/
lemma floor_two_pow_le (C₀ n : ℕ) :
    ⌊(C₀ : ℝ) * (2 : ℝ) ^ (n : ℝ) + C₀⌋₊ ≤ 2 ^ (n + (2 * C₀ + 2)) := by
  rw [Real.rpow_natCast, show (C₀ : ℝ) * (2 : ℝ) ^ n + C₀ = ((C₀ * 2 ^ n + C₀ : ℕ) : ℝ) by
    push_cast; ring, Nat.floor_natCast]
  have h1 : 2 * C₀ + 2 < 2 ^ (2 * C₀ + 2) := Nat.lt_two_pow_self
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [pow_add]
  have : 2 ^ n * (2 * C₀ + 2) ≤ 2 ^ n * 2 ^ (2 * C₀ + 2) := Nat.mul_le_mul_left _ h1.le
  have e : 2 ^ n * (2 * C₀ + 2) = 2 * (C₀ * 2 ^ n) + 2 * 2 ^ n := by ring
  have : C₀ ≤ C₀ * 2 ^ n := Nat.le_mul_of_pos_right _ h2
  omega

/--
---
conclusion: Lax119563.ExponentialLowerBound.exponential_lower_bound
---
Let `L ∈ DTIME(2^n) \ DTIME(2^{n/4})` be decided by `M` within `C₀ 2^n + C₀` steps, and
put `c₀ = 2 C₀ + 2`. For `|x| = n ≥ 2`, `h = n + c₀`, `a = ⌈log₂(n + 2)⌉` and `s` the least
number with `s a ≥ h + 2`, a machine computes `encodeNats [h, s] ++ x` in time `O(m^3)`
(`m = n + c₀ + 4`), and the pipeline turns it in time `m^{O(1)}` into an instance
`(s + 1, G₀, G₁)` of length `N ≤ B m^5` (`exp_len_arith`), which `(s+1)`-WL distinguishes iff
`x ∈ L`. With `ε = 1 / (4 (B + 1)^{1/5})`, a decider for WL Distinguishing within
`C 2^{ε N^{1/5}} + C` steps runs within `C 2^{m/4} + C` steps on these instances; together
with the polynomial reduction this decides `L` in time `O(2^{n/4})`, a contradiction.
-/
theorem exponential_lower_bound :
    ∃ ε : ℝ, 0 < ε ∧ ¬ ∃ M : Machine, Deterministic M ∧ ∃ C : ℕ,
      ∀ (k : ℕ) (G H : ColoredGraph),
        DecidesExactlyWithin M (encodeWLInstance k G H) (Distinguishes k G H)
          ⌊C * (2 : ℝ) ^ (ε * ((encodeWLInstance k G H).length : ℝ) ^ ((1 : ℝ) / 5)) + C⌋₊ := by
  classical
  obtain ⟨L, ⟨M, hMdet, C₀, hM⟩, hnot⟩ := Lax119563.ExponentialTimeHierarchy.exp_time_hierarchy
  obtain ⟨c, Cl, hpipe⟩ := pipeline_len
  obtain ⟨R, -, CR, Cs, hR⟩ := hpipe M hMdet
  obtain ⟨B, hB⟩ : ∃ B, B = Cl * (2 * Cs + 6 * (2 * C₀ + 2) + 21) * (36 * Cs + 1) + 3 :=
    ⟨_, rfl⟩
  obtain ⟨P, -, KP, hP⟩ := par_machine (2 * C₀ + 2)
  refine ⟨1 / (4 * ((B : ℝ) + 1) ^ ((1 : ℝ) / 5)), by positivity, ?_⟩
  rintro ⟨W, -, CW, hW⟩
  apply hnot
  set A := 2 * KP + CR * 2 ^ c + 3 with hA
  set d := 3 * c + 3 with hd
  set Q := (4 * d + 4) ^ d with hQ
  set E := 2 ^ (2 * C₀ + 2 + 4) with hE
  set K := 2 * A * Q * E + CW * E + CW + 3 with hK
  refine ⟨(Main.Compose.comp (Main.Compose.comp P R false fun _ => false).toMachine W
    (decide ([] ∈ L)) (fun b => decide ([b] ∈ L))).toMachine,
    Main.AMachine.toMachine_deterministic _, K, fun x => ?_⟩
  have hX : (0 : ℝ) ≤ (2 : ℝ) ^ ((x.length : ℝ) / 4) := by positivity
  by_cases hx : 2 ≤ x.length
  · have hc₀ : 1 ≤ 2 * C₀ + 2 := by omega
    have ha1 := one_le_parA x.length
    have ha2 := parA_le x.length
    have h2a := pow_parA_le x.length
    have hsa := parS_mul_le (2 * C₀ + 2) x.length
    have hsle := parS_le (2 * C₀ + 2) x.length
    have hs2' := two_le_parS hc₀ x.length
    have hn2 := le_pow_parA x.length
    have hpw := packedWidth_par (2 * C₀ + 2) x.length
    have hxh : x.length ≤ 2 ^ (x.length + (2 * C₀ + 2)) := (Nat.lt_two_pow_self).le.trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    obtain ⟨G₀, G₁, hacc, hlen, hcomp⟩ := hR x (x.length + (2 * C₀ + 2))
      (parS (2 * C₀ + 2) x.length) hx (by omega) hxh hs2' (by omega)
    rw [hpw] at hlen hcomp
    -- the decider of `L` halts within `2^h` steps
    have hMx : DecidesExactlyWithin M x (x ∈ L) ⌊(C₀ : ℝ) * (2 : ℝ) ^ (x.length : ℝ) + C₀⌋₊ := hM x
    have hhalt : HaltsWithin M x (2 ^ (x.length + (2 * C₀ + 2))) := by
      obtain ⟨b, hb, -⟩ := Main.decidesWithin_mono hMx (floor_two_pow_le C₀ _)
      simp [HaltsWithin, hb]
    have hiff : x ∈ L ↔ Distinguishes (parS (2 * C₀ + 2) x.length + 1) G₀ G₁ :=
      (Main.accepts_iff_of_decidesWithin hMx).symm.trans (hacc hhalt)
    -- the reduction
    have hred := Main.Compose.compose_computesWithin P R false (fun _ => false)
      hx (hP x) hcomp
    have hD : DecidesExactlyWithin W (encodeWLInstance (parS (2 * C₀ + 2) x.length + 1) G₀ G₁) (x ∈ L)
        ⌊CW * (2 : ℝ) ^ (1 / (4 * ((B : ℝ) + 1) ^ ((1 : ℝ) / 5)) *
          ((encodeWLInstance (parS (2 * C₀ + 2) x.length + 1) G₀ G₁).length : ℝ) ^ ((1 : ℝ) / 5)) + CW⌋₊ := by
      obtain ⟨b, hb, hPb⟩ := hW (parS (2 * C₀ + 2) x.length + 1) G₀ G₁
      exact ⟨b, hb, hPb.trans hiff.symm⟩
    refine Main.decidesWithin_mono (Main.Compose.compose_decidesWithin _ W _ _ hx hred hD) ?_
    apply Nat.le_floor
    clear hred hD hiff hhalt hMx hacc hcomp
    generalize hn : x.length = n at *
    generalize hs : parS (2 * C₀ + 2) n = s at *
    generalize ha : parA n = a at *
    generalize hh : n + (2 * C₀ + 2) = h at *
    generalize hm : h + 4 = m at *
    -- the estimates
    have hN : (encodeWLInstance (s + 1) G₀ G₁).length ≤ B * m ^ 5 := by
      rw [hB]
      exact hlen.trans (exp_len_arith ha1 (by omega) hn2 h2a (by omega) (by omega) hh.symm hm.symm)
    have hε := eps_mul_rpow_le B _ m hN
    have ht₁ := exp_time_arith (tP := KP * m ^ 3)
      (tR := CR * (s * 2 ^ a * (h + 1)) ^ c) (KP := KP) (CR := CR) (c := c) (s := s) (ℓ := a)
      (h := h) (m := m) le_rfl le_rfl (by omega) (h2a.trans (by omega)) (by omega) (by omega)
    have hY : (2 : ℝ) ^ (1 / (4 * ((B : ℝ) + 1) ^ ((1 : ℝ) / 5)) *
          ((encodeWLInstance (s + 1) G₀ G₁).length : ℝ) ^ ((1 : ℝ) / 5)) ≤ (2 : ℝ) ^ ((m : ℝ) / 4) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith
    have hmZ : (m : ℝ) ^ d ≤ (Q : ℝ) * (2 : ℝ) ^ ((m : ℝ) / 4) := by
      rw [hQ]; push_cast; exact_mod_cast pow_le_two_rpow_quarter m d
    have hZ : (2 : ℝ) ^ ((m : ℝ) / 4) ≤ (E : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 4) := by
      have := two_rpow_quarter_add_le n (2 * C₀ + 2 + 4)
      rw [hE]
      convert this using 3
      rw [← hm, ← hh]; push_cast; ring
    have ht₂ := Nat.floor_le (a := (CW : ℝ) * (2 : ℝ) ^ (1 / (4 * ((B : ℝ) + 1) ^
      ((1 : ℝ) / 5)) * ((encodeWLInstance (s + 1) G₀ G₁).length : ℝ) ^ ((1 : ℝ) / 5)) + CW) (by positivity)
    have := exp_final_arith _ _ A d CW E Q m _ _ _ hX (by positivity) ht₁ ht₂ hY hmZ hZ
    rw [hK]
    exact_mod_cast this
  · refine Main.decidesWithin_mono (Main.Compose.compose_short _ W (· ∈ L) x (by omega)) ?_
    apply Nat.le_floor
    have h2K : 2 ≤ K := by rw [hK]; omega
    have : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast h2K
    have := mul_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K) hX
    push_cast
    linarith

end Lax119563Proofs.Hardness
