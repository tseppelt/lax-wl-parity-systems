import Lax119563.TimeReduction
import Lax119563.MatrixCompiler
import Lax119563Proofs.Reduction.CostSys
import Lax119563Proofs.Reduction.CostMachine
import Lax119563Proofs.Machines.ComposeComputes
import Lax119563Proofs.Game.Characterization
import Lax119563Proofs.Programs.Correctness
import Lax119563Proofs.Programs.Size

/-!
# The quasi-linear reduction from deterministic time to `(s+1)`-WL Distinguishing

As in the paper, the reduction is the composition of two steps:
1. the compilation of the time simulation program into the implicit parity system
   `I_x = Iv M x s ℓ H` (`ℓ = timeWidth`, `H = timeHorizon`), whose explicit description is
   emitted by the generator `redGen M s C₀ = prelude (sysGen M s)` (`out_redGen`) in time
   `O(n log^24 n)` (`Gn.computesWithin_quasiLinear`), and
2. the matrix compiler (`Lax119563.MatrixCompiler.matrix_compiler`), which computes the graph
   pair from the encoding of `I_x` in time `O((H + S) log^c (H + S + 2))`.
The two machines are composed by `Main.Compose.compose_computesWithin`.
Correctness: `M` accepts `x` iff `I_x` has a conflict (`timeProgram'_accepts_iff`,
`conflictRound_compile_lt_top_iff`), and the game clauses of the matrix compiler with the
game characterization of WL. Size: `S(I_x) = O(n log^6 n)` (`sizeParameter_compile_le` and
the bounds of `time_simulation'`), and the encoding of `I_x` has `O(n log^24 n)` bits.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime Lax119563.PebbleGame Lax119563.ImplicitSystemEncodings
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Reduction

open Circuits Xp Lax119563.ImplicitParitySystems Lax119563Proofs.Programs
  Lax119563.MatrixCompiler

/-! ## The generator -/

namespace Gn

/-- **The reduction generator**: the description of the compiled system. -/
def redGen (M : Machine) (s C₀ : ℕ) : Gn := prelude M s C₀ (sysGen M s)

end Gn

variable {M : Machine} {x : List Bool} {s : ℕ}

/-- The compiled system `I_x`. -/
noncomputable abbrev sysI (M : Machine) (s C₀ : ℕ) (x : List Bool) :
    ImplicitParitySystem (s + 1) (timeWidth C₀ x.length) :=
  Iv M x s (timeWidth C₀ x.length) (timeHorizon s C₀ x.length)

theorem out_redGen {C₀ : ℕ} (hs : 2 ≤ s) :
    (Gn.redGen M s C₀).out x [] = systemDescription (sysI M s C₀ x) := by
  have hℓ : 0 < timeWidth C₀ x.length := by unfold timeWidth; omega
  rw [Gn.redGen, out_prelude hs, out_sysGen hℓ]

lemma length_le_encodeNats (l : List ℕ) : l.length ≤ (encodeNats l).length := by
  induction l with
  | nil => simp [encodeNats]
  | cons a l ih =>
    simp only [encodeNats, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have : 1 ≤ (encodeNat a).length := by simp [encodeNat]
    omega

lemma length_le_flatMap {α β : Type} (l : List α) (f : α → List β) (hf : ∀ a, f a ≠ []) :
    l.length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := List.length_pos_iff.mpr (hf a)
    omega

/-- The description of the system is longer than the input. -/
lemma length_le_desc {C₀ : ℕ} :
    x.length ≤ (systemDescription (sysI M s C₀ x)).length := by
  set ℓ := timeWidth C₀ x.length
  set H := timeHorizon s C₀ x.length
  have hW : 0 < (Iv M x s ℓ H).numLocations := by rw [Iv_numLocations]; omega
  have hmem : (⟨0, hW⟩ : Fin (Iv M x s ℓ H).numLocations) ∈
      List.finRange (Iv M x s ℓ H).numLocations := List.mem_finRange _
  have h1 := List.le_sum_of_mem (List.mem_map_of_mem (f := fun v => (initNum
    ((Iv M x s ℓ H).init v) :: domainDescription ((Iv M x s ℓ H).domain v)).length) hmem)
  have hdom : (Iv M x s ℓ H).domain ⟨0, hW⟩ = Finset.univ := rfl
  simp only [hdom, domainDescription_univ, List.length_cons, List.length_range] at h1
  have h2 : x.length < 2 ^ ℓ := lt_two_pow_timeWidth C₀ x.length
  have h3 : 2 ^ ℓ ≤ ((List.range (s + 1)).flatMap fun i =>
      (List.range (2 ^ ℓ)).flatMap fun v => i :: bitsL ℓ v).length := by
    rw [List.length_flatMap]
    refine le_trans ?_ (List.le_sum_of_mem (List.mem_map_of_mem
      (f := fun i => ((List.range (2 ^ ℓ)).flatMap fun v => i :: bitsL ℓ v).length)
      (List.mem_range.mpr (Nat.succ_pos s))))
    simpa using length_le_flatMap (List.range (2 ^ ℓ)) (fun v => 0 :: bitsL ℓ v)
      (fun _ => List.cons_ne_nil _ _)
  show x.length ≤ (systemDescription (Iv M x s ℓ H)).length
  unfold systemDescription
  simp only [List.length_append, List.length_cons, List.length_flatMap]
  omega

/-! ## Correctness -/

/-- `M` accepts `x` iff the compiled system has a conflict. -/
lemma accepts_iff_conflict {C₀ : ℕ} (hs : 2 ≤ s)
    (hC₀ : ∀ x : List Bool, (runOn M x (C₀ * x.length ^ s + C₀)).answer.isSome)
    (hx : 2 ≤ x.length) : Accepts M x ↔ (sysI M s C₀ x).conflictRound < ⊤ := by
  change _ ↔ ((timeProgram' M s C₀ x).compile (timeQuery' M s C₀ x) (fun _ _ => 0)).conflictRound < ⊤
  rw [RegisterProgram.conflictRound_compile_lt_top_iff]
  exact (timeProgram'_accepts_iff hs hC₀ hx).symm

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

/-! ## Size -/

/-- The arithmetic of the size bound: with `w, r ≤ A L^5`, `2^ℓ ≤ A n` and `ℓ ≤ A L`
(`L ≥ 1`), the bound of `sizeParameter_compile_le` is at most `C n L^6`. -/
lemma size_poly {s A n L w r ℓ : ℕ} (hL : 1 ≤ L) (hw : w ≤ A * L ^ 5) (hr : r ≤ A * L ^ 5)
    (h2 : 2 ^ ℓ ≤ A * n) (hℓ : ℓ ≤ A * L) :
    (s + 1) * 2 ^ ℓ * w + (s + 1) ^ 2 * 2 ^ ℓ * ℓ * (r + 1) ≤
      3 * (s + 1) ^ 2 * (A + 1) ^ 3 * n * L ^ 6 := by
  have hs : s + 1 ≤ (s + 1) ^ 2 := by nlinarith
  have hL56 : L ^ 5 ≤ L ^ 6 := Nat.pow_le_pow_right hL (by norm_num)
  have hAA : A * A ≤ (A + 1) ^ 3 := by nlinarith
  have hAAA : A * A * A ≤ (A + 1) ^ 3 := by
    have : A * A * A ≤ (A + 1) * (A + 1) * (A + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    nlinarith
  have hL6 : L * L ^ 5 = L ^ 6 := by ring
  generalize 2 ^ ℓ = X at *
  have e1 : (s + 1) * X * w ≤ (s + 1) ^ 2 * (A + 1) ^ 3 * n * L ^ 6 := by
    have a : (s + 1) * X * w ≤ (s + 1) ^ 2 * (A * n) * (A * L ^ 5) :=
      Nat.mul_le_mul (Nat.mul_le_mul hs h2) hw
    have b : A * n * (A * L ^ 5) ≤ (A + 1) ^ 3 * n * L ^ 6 := by
      calc A * n * (A * L ^ 5) = A * A * n * L ^ 5 := by ring
        _ ≤ (A + 1) ^ 3 * n * L ^ 6 := Nat.mul_le_mul (Nat.mul_le_mul hAA le_rfl) hL56
    calc (s + 1) * X * w ≤ (s + 1) ^ 2 * (A * n) * (A * L ^ 5) := a
      _ = (s + 1) ^ 2 * (A * n * (A * L ^ 5)) := by ring
      _ ≤ (s + 1) ^ 2 * ((A + 1) ^ 3 * n * L ^ 6) := Nat.mul_le_mul_left _ b
      _ = _ := by ring
  have e2 : (s + 1) ^ 2 * X * ℓ * (r + 1) ≤ 2 * ((s + 1) ^ 2 * (A + 1) ^ 3 * n * L ^ 6) := by
    have hr1 : r + 1 ≤ 2 * (A * L ^ 5) ∨ A = 0 := by
      rcases Nat.eq_zero_or_pos A with h | h
      · exact Or.inr h
      · left; have : 1 ≤ A * L ^ 5 := Nat.one_le_iff_ne_zero.mpr (by positivity); omega
    rcases hr1 with hr1 | hA0
    · have a : (s + 1) ^ 2 * X * ℓ * (r + 1) ≤
          (s + 1) ^ 2 * (A * n) * (A * L) * (2 * (A * L ^ 5)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl h2) hℓ) hr1
      calc _ ≤ (s + 1) ^ 2 * (A * n) * (A * L) * (2 * (A * L ^ 5)) := a
        _ = 2 * ((s + 1) ^ 2 * (A * A * A) * n * (L * L ^ 5)) := by ring
        _ ≤ 2 * ((s + 1) ^ 2 * (A + 1) ^ 3 * n * L ^ 6) := by
          rw [hL6]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul
            (Nat.mul_le_mul_left _ hAAA) le_rfl) le_rfl)
    · subst hA0
      have : X = 0 := by omega
      subst this; simp
  calc (s + 1) * X * w + (s + 1) ^ 2 * X * ℓ * (r + 1)
      ≤ (s + 1) ^ 2 * (A + 1) ^ 3 * n * L ^ 6 +
          2 * ((s + 1) ^ 2 * (A + 1) ^ 3 * n * L ^ 6) := Nat.add_le_add e1 e2
    _ = _ := by ring

/-- **Size of the compiled system**: `S(I_x) = O(n log^6 n)`. -/
lemma sizeParameter_sysI_le {C₀ : ℕ} (hs : 2 ≤ s)
    (hC₀ : ∀ x : List Bool, (runOn M x (C₀ * x.length ^ s + C₀)).answer.isSome) :
    ∃ K : ℕ, ∀ x : List Bool, 2 ≤ x.length →
      sizeParameter (sysI M s C₀ x) ≤ K * x.length * Nat.log 2 x.length ^ 6 := by
  obtain ⟨C, hC⟩ := time_simulation' M s hs C₀ hC₀
  refine ⟨100 * (3 * (s + 1) ^ 2 * (C + C₀ + 5 + 1) ^ 3), fun x hx => ?_⟩
  obtain ⟨hℓ, -, -, h2, hw, hr⟩ := hC x hx
  have hL : 1 ≤ Nat.log 2 x.length := (Circuits.log_facts hx).1
  change sizeParameter ((timeProgram' M s C₀ x).compile (timeQuery' M s C₀ x) (fun _ _ => 0)) ≤ _
  refine (RegisterProgram.sizeParameter_compile_le _ _ _ hℓ).trans ?_
  have hℓ' : Circuits.timeWidth C₀ x.length ≤ (C + C₀ + 5) * Nat.log 2 x.length := by
    unfold Circuits.timeWidth; nlinarith
  have := size_poly (s := s) (A := C + C₀ + 5) hL
    (hw.trans (Nat.mul_le_mul_right _ (by omega)))
    (hr.trans (Nat.mul_le_mul_right _ (by omega)))
    (h2.trans (Nat.mul_le_mul_right _ (by omega))) hℓ'
  calc _ ≤ 100 * (3 * (s + 1) ^ 2 * (C + C₀ + 5 + 1) ^ 3 * x.length * Nat.log 2 x.length ^ 6) :=
        Nat.mul_le_mul_left _ this
    _ = _ := by ring

/-! ## Logarithms -/

/-- `log₂ (K n L^c + 2) ≤ (log₂ (K + 2) + 2c + 4) L` for `L = log₂ n ≥ 1`. -/
lemma log_le_mul_log {K n c : ℕ} (hL : 1 ≤ Nat.log 2 n) :
    Nat.log 2 (K * n * Nat.log 2 n ^ c + 2) ≤
      (Nat.log 2 (K + 2) + 2 * c + 4) * Nat.log 2 n := by
  set L := Nat.log 2 n
  have hn : n ≠ 0 := by intro h; simp [L, h] at hL
  have hn2 : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hLn : L < 2 ^ (L + 1) := lt_trans (Nat.lt_two_pow_self) (Nat.pow_lt_pow_right (by norm_num)
    (by omega))
  have hK : K + 2 < 2 ^ (Nat.log 2 (K + 2) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  set a := Nat.log 2 (K + 2) + 1
  have hbound : K * n * L ^ c + 2 < 2 ^ (a + (L + 1) + c * (L + 1) + 1) := by
    have e1 : K * n * L ^ c + 2 ≤ (K + 2) * n * L ^ c + 2 * 1 * 1 := by
      have : K * n * L ^ c ≤ (K + 2) * n * L ^ c :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      omega
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hLc : 1 ≤ L ^ c := Nat.one_le_pow _ _ hL
    have e2 : (K + 2) * n * L ^ c + 2 * 1 * 1 ≤ 2 * ((K + 2) * n * L ^ c) := by
      have : 2 * 1 * 1 ≤ (K + 2) * n * L ^ c := by
        calc 2 * 1 * 1 ≤ (K + 2) * 1 * 1 := by omega
          _ ≤ (K + 2) * n * L ^ c := Nat.mul_le_mul (Nat.mul_le_mul_left _ hn1) hLc
      omega
    have e3 : (K + 2) * n * L ^ c < 2 ^ a * 2 ^ (L + 1) * (2 ^ (L + 1)) ^ c := by
      calc (K + 2) * n * L ^ c < 2 ^ a * n * L ^ c :=
            Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hK (by omega))
              (by positivity)
        _ ≤ 2 ^ a * 2 ^ (L + 1) * (2 ^ (L + 1)) ^ c :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hn2.le) (Nat.pow_le_pow_left hLn.le _)
    have e4 : 2 ^ a * 2 ^ (L + 1) * (2 ^ (L + 1)) ^ c = 2 ^ (a + (L + 1) + c * (L + 1)) := by
      rw [← pow_mul, ← pow_add, ← pow_add, Nat.mul_comm (L + 1) c]
    have : 2 * ((K + 2) * n * L ^ c) < 2 * 2 ^ (a + (L + 1) + c * (L + 1)) := by
      rw [← e4]; omega
    rw [pow_succ]; omega
  have hlog := Nat.log_lt_of_lt_pow (by omega) hbound
  have : a + (L + 1) + c * (L + 1) + 1 ≤ (Nat.log 2 (K + 2) + 2 * c + 4) * L + 1 := by
    simp only [a]; nlinarith
  omega

/-- The arithmetic of the running time. -/
lemma time_arith {n L HS lg C₁ Cn KS Kh Cc cc lk : ℕ} (hL : 1 ≤ L) (hHS : HS ≤ Kh * n * L ^ 24)
    (hlog : lg ≤ lk * L) (hn : 1 ≤ n) :
    2 * (C₁ * n * L ^ (21 + 3)) + Cc * HS * lg ^ cc + 3 ≤
      (Cn * KS + 2 * C₁ + Cc * Kh * lk ^ cc + 3) * n * L ^ (24 + cc) := by
  have hL23 : L ^ 24 ≤ L ^ (24 + cc) := Nat.pow_le_pow_right hL (by omega)
  have hT2 : Cc * HS * lg ^ cc ≤ Cc * Kh * lk ^ cc * n * L ^ (24 + cc) :=
    calc Cc * HS * lg ^ cc ≤ Cc * (Kh * n * L ^ 24) * (lk * L) ^ cc :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hHS) (Nat.pow_le_pow_left hlog _)
      _ = Cc * Kh * lk ^ cc * n * L ^ (24 + cc) := by ring
  have hT1 : C₁ * n * L ^ (21 + 3) ≤ C₁ * n * L ^ (24 + cc) := Nat.mul_le_mul_left _ hL23
  have h3 : 3 ≤ 3 * n * L ^ (24 + cc) := by
    have : 1 ≤ L ^ (24 + cc) := Nat.one_le_pow _ _ hL
    have : 1 ≤ n * L ^ (24 + cc) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  have hC : (Cn * KS + 2 * C₁ + Cc * Kh * lk ^ cc + 3) * n * L ^ (24 + cc) =
      Cn * KS * n * L ^ (24 + cc) + 2 * (C₁ * n * L ^ (24 + cc)) +
        Cc * Kh * lk ^ cc * n * L ^ (24 + cc) + 3 * n * L ^ (24 + cc) := by ring
  rw [hC]
  have : 0 ≤ Cn * KS * n * L ^ (24 + cc) := Nat.zero_le _
  omega

/-! ## The final theorem -/

/--
---
conclusion: Lax119563.TimeReduction.time_reduction
---
As in the paper, the reduction composes two steps. First, a generator program (a stack
language with a pure list semantics, compiled once and for all into a deterministic multitape
machine) emits the explicit description of the implicit parity system `I_x` compiled from the
code-ordered time simulation program (`ℓ = log₂ n + C₀ + 4`): a prelude computes the global
parameters (the numbers of locations, commands and schemas), then the locations with their
initializations and domains and, by the schema enumerator, the schemas with their locations,
domains and permutations are emitted. All values have `O(log n)` bits and the generator has
cost `O(n log^22 n)`, so `encodeSystem I_x` is computed in time `O(n log^24 n)`. Second, the
machine of the matrix compiler computes the graph pair from `encodeSystem I_x` in time
`O((H + S) log^c (H + S + 2))` with `H = O(n log^24 n)` and `S = O(n log^6 n)`. The two
machines are composed (simulate the first, rewind, simulate the second). Correctness: `M`
accepts `x` iff `I_x` has a conflict, and by the game clauses of the matrix compiler and the
game characterization this holds iff `(s+1)`-WL distinguishes the two graphs; they have
`O(S)` vertices.
-/
theorem time_reduction : ∃ c : ℕ, ∀ s : ℕ, 2 ≤ s → ∀ M : Machine, Deterministic M →
    (∃ C₀ : ℕ, ∀ x : List Bool, (runOn M x (C₀ * x.length ^ s + C₀)).answer.isSome) →
    ∃ R : Machine, Deterministic R ∧ ∃ C : ℕ, ∀ x : List Bool, 2 ≤ x.length →
      ∃ G₀ G₁ : ColoredGraph,
        (Accepts M x ↔ Distinguishes (s + 1) G₀ G₁) ∧
        G₀.n + G₁.n ≤ C * x.length * Nat.log 2 x.length ^ c ∧
        ComputesWithin R x (encodeGraphPair G₀ G₁) (C * x.length * Nat.log 2 x.length ^ c) := by
  obtain ⟨compile, ⟨Cn, hgame⟩, ⟨Mc, -, Cc, cc, hMc⟩⟩ := matrix_compiler
  refine ⟨24 + cc, fun s hs M _ ⟨C₀, hC₀⟩ => ?_⟩
  have hcost : Gn.HasCost [] (Gn.redGen M s C₀) 1 21 :=
    Gn.hasCost_prelude M s C₀ (by norm_num) (hasCost_sysGen M s)
  have hwf : (Gn.redGen M s C₀).WFX := Gn.wfx_prelude M s C₀ (wfx_sysGen M s)
  obtain ⟨C₁, hC₁⟩ := Gn.computesWithin_quasiLinear hcost le_rfl hwf
  obtain ⟨KS, hKS⟩ := sizeParameter_sysI_le hs hC₀
  obtain ⟨Ck, hCk⟩ := hgame (s + 1) (by omega)
  obtain ⟨Kh, hKh⟩ : ∃ K, K = C₁ + KS := ⟨_, rfl⟩
  obtain ⟨lk, hlk⟩ : ∃ l, l = Nat.log 2 (Kh + 2) + 2 * 24 + 4 := ⟨_, rfl⟩
  refine ⟨(Main.Compose.comp (Gn.machine (Gn.redGen M s C₀).need (Gn.redGen M s C₀)) Mc false
      fun _ => false).toMachine, Main.AMachine.toMachine_deterministic _,
    Cn * KS + 2 * C₁ + Cc * Kh * lk ^ cc + 3, fun x hx => ?_⟩
  have hL : 1 ≤ Nat.log 2 x.length := (Circuits.log_facts hx).1
  have hℓ1 : 1 ≤ timeWidth C₀ x.length := by unfold timeWidth; omega
  obtain ⟨hsp, hdu, hsize, -⟩ := hCk (timeWidth C₀ x.length) hℓ1 (sysI M s C₀ x)
  have hS := hKS x hx
  have hL6 : Nat.log 2 x.length ^ 6 ≤ Nat.log 2 x.length ^ (24 + cc) :=
    Nat.pow_le_pow_right hL (by omega)
  have hL23 : Nat.log 2 x.length ^ 24 ≤ Nat.log 2 x.length ^ (24 + cc) :=
    Nat.pow_le_pow_right hL (by omega)
  refine ⟨(compile (sysI M s C₀ x)).1, (compile (sysI M s C₀ x)).2, ?_, ?_, ?_⟩
  · exact (accepts_iff_conflict hs hC₀ hx).trans
      (distinguishes_iff_conflict (by omega) _ hsp hdu).symm
  · calc _ ≤ Cn * sizeParameter (sysI M s C₀ x) := hsize
      _ ≤ Cn * (KS * x.length * Nat.log 2 x.length ^ 6) := Nat.mul_le_mul_left _ hS
      _ ≤ Cn * (KS * x.length * Nat.log 2 x.length ^ (24 + cc)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hL6)
      _ = Cn * KS * x.length * Nat.log 2 x.length ^ (24 + cc) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  · have hout := out_redGen (M := M) (x := x) (C₀ := C₀) hs
    have hlen : x.length ≤ (encodeNats ((Gn.redGen M s C₀).out x [])).length := by
      rw [hout]; exact length_le_desc.trans (length_le_encodeNats _)
    obtain ⟨h1, hH⟩ := hC₁ x hx hlen
    rw [hout] at h1 hH
    have h2 := hMc (s + 1) (by omega) _ hℓ1 (sysI M s C₀ x)
    have hc := Main.Compose.compose_computesWithin _ Mc false (fun _ => false) hx h1 h2
    refine ComputesWithin.mono hc ?_
    have hHb : bitLength (sysI M s C₀ x) ≤ C₁ * x.length * Nat.log 2 x.length ^ 24 := hH
    have hHS : bitLength (sysI M s C₀ x) + sizeParameter (sysI M s C₀ x) ≤
        Kh * x.length * Nat.log 2 x.length ^ 24 := by
      have : KS * x.length * Nat.log 2 x.length ^ 6 ≤ KS * x.length * Nat.log 2 x.length ^ 24 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL (by omega))
      have e : Kh * x.length * Nat.log 2 x.length ^ 24 =
          C₁ * x.length * Nat.log 2 x.length ^ 24 + KS * x.length * Nat.log 2 x.length ^ 24 := by
        rw [hKh]; ring
      omega
    have hlog : Nat.log 2 (bitLength (sysI M s C₀ x) + sizeParameter (sysI M s C₀ x) + 2) ≤
        lk * Nat.log 2 x.length := by
      rw [hlk]
      exact (Nat.log_mono_right (by omega)).trans (log_le_mul_log (K := Kh) (c := 24) hL)
    exact time_arith hL hHS hlog (by omega)

end Lax119563Proofs.Reduction
