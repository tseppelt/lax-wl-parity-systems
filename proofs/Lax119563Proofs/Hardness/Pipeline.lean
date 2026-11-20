import Lax119563.PackedRepresentation
import Lax119563.WLProblems
import Lax119563Proofs.Hardness.LeadMachine
import Lax119563Proofs.Hardness.SizeBound
import Lax119563Proofs.Game.Characterization

/-!
# From deterministic machine runs to WL instances

The common pipeline of the hardness results (EXPTIME-hardness, XP-hardness, and the
exponential lower bound): for a deterministic machine `M`, an input `x`, a horizon `2^h` and
a number `s` of data blocks, the packed implicit parity system of
`Lax119563.PackedRepresentation.packed_representation` is compiled by
`Lax119563.MatrixCompiler.matrix_compiler` into a pair of colored graphs, and the dimension
`s + 1` is put in front of their encoding.

**`pipeline`**: there are an absolute exponent `c` and, for every deterministic `M`, a
deterministic machine `R` and a constant `C` such that for `2 ≤ |x|`, `2 ≤ h`, `|x| ≤ 2^h`,
`2 ≤ s ≤ h + 2`, with `ℓ = packedWidth |x| h s`, there are graphs `G₀, G₁` with
* if `M` halts on `x` within `2^h` steps, then `M` accepts `x` iff `(s+1)`-WL distinguishes
  `G₀` and `G₁`;
* `|V(G₀)| + |V(G₁)| ≤ C (s+1)^2 2^ℓ (ℓ+1) (h+1)^2`;
* `R` computes `encodeWLInstance (s+1) G₀ G₁` from `encodeNats [h, s] ++ x` within
  `C (s 2^ℓ (h+1))^c` steps.

The machine `R` composes (`Main.Compose.compose_computesWithin`) the generator of the packed
system with `withLead` of the machine of the matrix compiler, which keeps the leading number
`k = s + 1` of the encoding of the system in front of the encoding of the graph pair.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime Lax119563.PebbleGame Lax119563.ImplicitSystemEncodings
  Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.PackedRepresentation
  Lax119563.WLProblems
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

/-- The game clauses of the matrix compiler give the WL characterization. -/
lemma distinguishes_iff_conflict {k ℓ : ℕ} (hk : 2 ≤ k) (I : ImplicitParitySystem k ℓ)
    {G₀ G₁ : ColoredGraph} {Ck Λ' : ℕ}
    (hsp : ∀ τ : ℕ, I.conflictRound = τ → SpoilerWinsWithin (k + 1) (Ck * Λ' * (τ + 1)) G₀ G₁)
    (hdu : ∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound → DuplicatorSurvives (k + 1) r G₀ G₁) :
    Distinguishes k G₀ G₁ ↔ I.conflictRound < ⊤ := by
  constructor
  · intro hd
    by_contra hlt
    have htop : I.conflictRound = ⊤ := not_lt_top_iff.mp hlt
    have hw : DuplicatorWins (k + 1) G₀ G₁ := fun r => hdu r (by rw [htop]; exact le_top)
    exact (Game.duplicatorWins_iff hk _ _).mp hw hd
  · intro hlt
    obtain ⟨τ, hτ⟩ := ENat.ne_top_iff_exists.mp hlt.ne
    obtain ⟨r, -, hr⟩ := Game.distinguishesAfter_of_spoilerWinsWithin hk (hsp τ hτ.symm)
    exact ⟨r, hr⟩

/-! ## Encodings -/

lemma encodeNats_cons (a : ℕ) (l : List ℕ) : encodeNats (a :: l) = encodeNat a ++ encodeNats l := by
  simp [encodeNats]

lemma encodeSystem_eq {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) :
    encodeSystem I = encodeNat k ++ encodeNats ((systemDescription I).tail) := by
  rw [encodeSystem, ← encodeNats_cons]
  congr 1

lemma encodeWLInstance_eq (k : ℕ) (G H : ColoredGraph) :
    encodeWLInstance k G H = encodeNat k ++ encodeGraphPair G H := by
  rw [encodeWLInstance, wlWord, encodeNats_cons, encodeGraphPair]

lemma length_encodeNat_le (m : ℕ) : (encodeNat m).length ≤ 2 * m + 1 := by
  have h1 : (Nat.bits m).length ≤ m := by
    rw [Nat.size_eq_bits_len, Nat.size_le]; exact Nat.lt_two_pow_self
  simp [encodeNat]; omega

/-! ## Arithmetic -/

/-- The size bound. -/
lemma size_arith {L E s Q ℓ A : ℕ} (hL : L ≤ A) (hE : E ≤ A) :
    L * ((s + 1) * Q) + (s + 1 + 1) * (E * ((2 + ℓ) * ((s + 1) * Q))) ≤
      5 * A * (s + 1) ^ 2 * Q * (ℓ + 1) := by
  have e1 : L * ((s + 1) * Q) ≤ A * ((s + 1) * Q) := Nat.mul_le_mul_right _ hL
  have e2 : (s + 1 + 1) * (E * ((2 + ℓ) * ((s + 1) * Q))) ≤
      (2 * (s + 1)) * (A * ((2 * (ℓ + 1)) * ((s + 1) * Q))) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul hE (Nat.mul_le_mul_right _ (by omega)))
  have e3 : A * ((s + 1) * Q) ≤ A * (s + 1) ^ 2 * Q * (ℓ + 1) := by
    have : (s + 1) * 1 ≤ (s + 1) * (s + 1) := Nat.mul_le_mul_left _ (by omega)
    calc A * ((s + 1) * Q) = A * ((s + 1) * 1) * Q * 1 := by ring
      _ ≤ A * ((s + 1) * (s + 1)) * Q * (ℓ + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)) (by omega)
      _ = _ := by ring
  have e4 : (2 * (s + 1)) * (A * ((2 * (ℓ + 1)) * ((s + 1) * Q))) =
      4 * (A * (s + 1) ^ 2 * Q * (ℓ + 1)) := by ring
  have e5 : 5 * A * (s + 1) ^ 2 * Q * (ℓ + 1) = 5 * (A * (s + 1) ^ 2 * Q * (ℓ + 1)) := by ring
  omega

/-- The time bound. -/
lemma time_arith {X xin T1 H S T2 Cs Cc cp cc : ℕ} (hX : 1 ≤ X) (hxin : xin ≤ 5 * X)
    (hT1 : T1 ≤ Cs * X ^ (cp + 1)) (hH : H ≤ xin + T1) (hS : S ≤ 20 * Cs * X ^ 2)
    (hT2 : T2 ≤ Cc * (H + S + 2) ^ (cc + 1)) :
    2 * T1 + 16 * (T2 + H + 1) + 3 ≤
      (2 * Cs + 16 * Cc * (21 * Cs + 7) ^ (cc + 1) + 16 * (5 + Cs) + 19) *
        X ^ ((cp + 2) * (cc + 1)) := by
  obtain ⟨P, hP⟩ : ∃ P, P = X ^ (cp + 2) := ⟨_, rfl⟩
  have hP1 : 1 ≤ P := hP ▸ Nat.one_le_pow _ _ hX
  have hXP : X ≤ P := hP ▸ (by simpa using Nat.pow_le_pow_right hX (show 1 ≤ cp + 2 by omega))
  have hX1P : X ^ (cp + 1) ≤ P := hP ▸ Nat.pow_le_pow_right hX (by omega)
  have hX2P : X ^ 2 ≤ P := hP ▸ Nat.pow_le_pow_right hX (by omega)
  have hPe : X ^ ((cp + 2) * (cc + 1)) = P ^ (cc + 1) := by rw [hP, pow_mul]
  have hPP : P ≤ P ^ (cc + 1) := by simpa using Nat.pow_le_pow_right hP1 (show 1 ≤ cc + 1 by omega)
  have hT1' : T1 ≤ Cs * P := hT1.trans (Nat.mul_le_mul_left _ hX1P)
  have hH' : H ≤ (5 + Cs) * P := by
    have : 5 * X ≤ 5 * P := Nat.mul_le_mul_left _ hXP
    have : (5 + Cs) * P = 5 * P + Cs * P := by ring
    omega
  have hS' : S ≤ 20 * Cs * P := hS.trans (Nat.mul_le_mul_left _ hX2P)
  have hHS : H + S + 2 ≤ (21 * Cs + 7) * P := by
    have : (21 * Cs + 7) * P = (5 + Cs) * P + 20 * Cs * P + 2 * P := by ring
    omega
  have hT2' : T2 ≤ Cc * (21 * Cs + 7) ^ (cc + 1) * P ^ (cc + 1) := by
    calc T2 ≤ Cc * (H + S + 2) ^ (cc + 1) := hT2
      _ ≤ Cc * ((21 * Cs + 7) * P) ^ (cc + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hHS _)
      _ = _ := by rw [mul_pow, mul_assoc]
  rw [hPe]
  generalize P ^ (cc + 1) = Pe at hPP hT2' ⊢
  generalize (21 * Cs + 7) ^ (cc + 1) = B at hT2' ⊢
  have a1 : Cs * P ≤ Cs * Pe := Nat.mul_le_mul_left _ hPP
  have a2 : (5 + Cs) * P ≤ (5 + Cs) * Pe := Nat.mul_le_mul_left _ hPP
  have key : (2 * Cs + 16 * Cc * B + 16 * (5 + Cs) + 19) * Pe =
      2 * (Cs * Pe) + 16 * (Cc * B * Pe) + 16 * ((5 + Cs) * Pe) + 19 * Pe := by ring
  rw [key]
  omega

lemma X_facts {s Q h : ℕ} (hs : 1 ≤ s) (hQ : 1 ≤ Q) :
    h + 1 ≤ s * Q * (h + 1) ∧ s ≤ s * Q * (h + 1) ∧ Q ≤ s * Q * (h + 1) ∧
      s * Q ≤ s * Q * (h + 1) := by
  have hsQ : 1 ≤ s * Q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using Nat.mul_le_mul_right (h + 1) hsQ
  · calc s = s * 1 * 1 := by ring
      _ ≤ s * Q * (h + 1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hQ) (by omega)
  · calc Q = 1 * Q * 1 := by ring
      _ ≤ s * Q * (h + 1) := Nat.mul_le_mul (Nat.mul_le_mul_right _ hs) (by omega)
  · simpa using Nat.mul_le_mul_left (s * Q) (show 1 ≤ h + 1 by omega)

lemma T1_le {Cs s Q h cp : ℕ} (hs : 1 ≤ s) (hQ : 1 ≤ Q) :
    Cs * s * Q * (h + 1) ^ cp ≤ Cs * (s * Q * (h + 1)) ^ (cp + 1) := by
  obtain ⟨h1, -, -, h4⟩ := X_facts (h := h) hs hQ
  calc Cs * s * Q * (h + 1) ^ cp = Cs * (s * Q) * (h + 1) ^ cp := by ring
    _ ≤ Cs * (s * Q * (h + 1)) * (s * Q * (h + 1)) ^ cp :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ h4) (Nat.pow_le_pow_left h1 _)
    _ = _ := by ring

lemma S_le {S Cs s Q h ℓ : ℕ} (hS : S ≤ 5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 * Q * (ℓ + 1))
    (hℓ : ℓ + 1 ≤ Q) (hs : 1 ≤ s) : S ≤ 20 * Cs * (s * Q * (h + 1)) ^ 2 := by
  refine hS.trans ?_
  have h2 : (s + 1) ^ 2 ≤ 4 * s ^ 2 := by
    have : s + 1 ≤ 2 * s := by omega
    calc (s + 1) ^ 2 ≤ (2 * s) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 4 * s ^ 2 := by ring
  calc 5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 * Q * (ℓ + 1)
      ≤ 5 * (Cs * (h + 1) ^ 2) * (4 * s ^ 2) * Q * Q :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)) hℓ
    _ = _ := by ring

lemma T2_le {Cc HS cc : ℕ} :
    Cc * HS * Nat.log 2 (HS + 2) ^ cc ≤ Cc * (HS + 2) ^ (cc + 1) := by
  calc Cc * HS * Nat.log 2 (HS + 2) ^ cc ≤ Cc * (HS + 2) * (HS + 2) ^ cc :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
          (Nat.pow_le_pow_left (Nat.log_le_self 2 _) _)
    _ = _ := by ring

lemma one_le_packedWidth (n h s : ℕ) : 1 ≤ packedWidth n h s :=
  le_trans (Nat.clog_pos (by norm_num) (by omega)) (le_max_left _ _)

lemma length_add_two_le (n h s : ℕ) : n + 2 ≤ 2 ^ packedWidth n h s :=
  (Nat.le_pow_clog (by norm_num) _).trans
    (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))

/-- **The pipeline from deterministic machine runs to WL instances.** -/
theorem pipeline : ∃ c : ℕ, ∀ M : Machine, Deterministic M →
    ∃ R : Machine, Deterministic R ∧ ∃ C : ℕ,
      ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s →
        s ≤ h + 2 →
        ∃ G₀ G₁ : ColoredGraph,
          ((runOn M x (2 ^ h)).answer.isSome → (Accepts M x ↔ Distinguishes (s + 1) G₀ G₁)) ∧
          G₀.n + G₁.n ≤ C * (s + 1) ^ 2 * 2 ^ packedWidth x.length h s *
            (packedWidth x.length h s + 1) * (h + 1) ^ 2 ∧
          ComputesWithin R (encodeNats [h, s] ++ x) (encodeWLInstance (s + 1) G₀ G₁)
            (C * (s * 2 ^ packedWidth x.length h s * (h + 1)) ^ c) := by
  obtain ⟨cp, hpack⟩ := packed_representation
  obtain ⟨compile, ⟨Cn, hgame⟩, ⟨Mc, -, Cc, cc, hMc⟩⟩ := matrix_compiler
  refine ⟨(cp + 2) * (cc + 1), fun M hM => ?_⟩
  obtain ⟨sys, Cs, hsys, Rp, -, hRp⟩ := hpack M hM
  obtain ⟨Kt, hKt⟩ : ∃ K, K = 2 * Cs + 16 * Cc * (21 * Cs + 7) ^ (cc + 1) + 16 * (5 + Cs) + 19 :=
    ⟨_, rfl⟩
  refine ⟨(Main.Compose.comp Rp (withLead Mc).compile false fun _ => false).toMachine,
    Main.AMachine.toMachine_deterministic _, 5 * Cn * Cs + Kt,
    fun x h s hx hh hxh hs hsh => ?_⟩
  have hℓ1 := one_le_packedWidth x.length h s
  have hQ := length_add_two_le x.length h s
  obtain ⟨hcorr, hloc, hsch⟩ := hsys x h s hx hh hxh hs hsh
  obtain ⟨Ck, hCk⟩ := hgame (s + 1) (by omega)
  obtain ⟨hsp, hdu, hsize, -⟩ := hCk _ hℓ1 (sys x h s)
  have hSz : sizeParameter (sys x h s) ≤ 5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 *
      2 ^ packedWidth x.length h s * (packedWidth x.length h s + 1) :=
    (sizeParameter_le _).trans (size_arith hloc hsch)
  refine ⟨(compile (sys x h s)).1, (compile (sys x h s)).2, fun hhalt => ?_, ?_, ?_⟩
  · exact (hcorr hhalt).symm.trans (distinguishes_iff_conflict (by omega) _ hsp hdu).symm
  · calc _ ≤ Cn * sizeParameter (sys x h s) := hsize
      _ ≤ Cn * (5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 * 2 ^ packedWidth x.length h s *
            (packedWidth x.length h s + 1)) := Nat.mul_le_mul_left _ hSz
      _ = 5 * Cn * Cs * (s + 1) ^ 2 * 2 ^ packedWidth x.length h s *
            (packedWidth x.length h s + 1) * (h + 1) ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (Nat.mul_le_mul_right _ (by omega))))
  · have h1 := hRp x h s hx hh hxh hs hsh
    have h2 := hMc (s + 1) (by omega) _ hℓ1 (sys x h s)
    rw [encodeSystem_eq] at h2
    have h3 := withLead_computesWithin h2
    rw [← encodeSystem_eq, ← encodeWLInstance_eq] at h3
    have hxin2 : 2 ≤ (encodeNats [h, s] ++ x).length := by simp; omega
    have hc := Main.Compose.compose_computesWithin Rp (withLead Mc).compile false
      (fun _ => false) hxin2 h1 h3
    refine Main.Compose.computesWithin_mono' hc ?_
    obtain ⟨hX1, hX2, hX3, -⟩ := X_facts (h := h) (show 1 ≤ s by omega)
      (show 1 ≤ 2 ^ packedWidth x.length h s by omega)
    have hxin : (encodeNats [h, s] ++ x).length ≤
        5 * (s * 2 ^ packedWidth x.length h s * (h + 1)) := by
      have e1 := length_encodeNat_le h
      have e2 := length_encodeNat_le s
      simp only [encodeNats, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_append]
      omega
    have hH := length_le_of_computesWithin h1
    have hl : packedWidth x.length h s + 1 ≤ 2 ^ packedWidth x.length h s :=
      Nat.lt_two_pow_self
    have ht := time_arith (Cs := Cs) (Cc := Cc) (cp := cp) (cc := cc)
      (X := s * 2 ^ packedWidth x.length h s * (h + 1)) (by omega) hxin
      (T1_le (show 1 ≤ s by omega) (by omega)) hH (S_le hSz hl (by omega)) T2_le
    rw [← hKt] at ht
    refine le_trans ?_ (ht.trans (Nat.mul_le_mul_right _ (by omega)))
    exact le_rfl

end Lax119563Proofs.Hardness
