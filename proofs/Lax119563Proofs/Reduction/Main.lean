import Lax119563.TimeReduction
import Lax119563Proofs.Reduction.Prelude
import Lax119563Proofs.Reduction.CostMachine

/-!
# The quasi-linear reduction from deterministic time to `(s+1)`-WL Distinguishing

The reduction generator `redGen M s C₀ = prelude (descGen 0 ; descGen 1)` emits the
descriptions of the two output graphs `outGraph (Iv …) 0` and `outGraph (Iv …) 1` of the
compiled code-ordered time program (`out_redGen`); it has quasi-linear cost (`hasCost_prelude`,
`hasCost_descGen`), so its machine computes `encodeGraphPair` within `C n log^24 n` steps
(`Gn.computesWithin_quasiLinear`). Correctness: `distinguishes_outGraph_iff` and
`timeProgram'_graphs`; size: `nOut = 4 · 2^ℓ (s+1) famCount` with the bounds of
`time_simulation'`.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Reduction

open Circuits Xp Lax119563.ImplicitParitySystems Lax119563Proofs.Programs
  Lax119563Proofs.Matrix

/-! ## Number of schemas -/

lemma length_compiledSchemas_le {s ℓ : ℕ} (R : RegisterProgram s ℓ)
    (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    (R.compiledSchemas p₀ a₀).length ≤ 9 * R.commands.length + 4 := by
  unfold RegisterProgram.compiledSchemas
  rw [List.length_append, List.length_flatMap]
  have h1 : ∀ j c, (R.commandSchemas j c).length ≤ 9 := by
    intro j c
    cases c <;> simp [RegisterProgram.commandSchemas, gadget]
  have h2 : (R.detectorSchemas p₀ a₀).length = 4 := by
    simp [RegisterProgram.detectorSchemas, gadget]
  have h3 := List.sum_le_card_nsmul ((List.finRange R.commands.length).map
    fun j => (R.commandSchemas j R.commands[j]).length) 9 (by
      intro a ha
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
      exact h1 _ _)
  simp only [List.length_map, List.length_finRange, smul_eq_mul] at h3
  omega

/-! ## The generator -/

namespace Gn

/-- **The reduction generator.** -/
def redGen (M : Machine) (s C₀ : ℕ) : Gn :=
  prelude M s C₀ (seq (descGen M s 0 18) (descGen M s 1 18))

end Gn

variable {M : Machine} {x : List Bool} {s : ℕ}

/-- The output graphs. -/
noncomputable abbrev outG (M : Machine) (s C₀ : ℕ) (x : List Bool) (ε : ZMod 2) :
    ColoredGraph :=
  outGraph (Iv M x s (timeWidth C₀ x.length) (timeHorizon s C₀ x.length)) ε

theorem out_redGen {C₀ : ℕ} (hs : 2 ≤ s) :
    (Gn.redGen M s C₀).out x [] =
      graphDescription (outG M s C₀ x 0) ++ graphDescription (outG M s C₀ x 1) := by
  have hℓ : 0 < timeWidth C₀ x.length := by unfold timeWidth; omega
  have hG : GlobOK M x s (timeWidth C₀ x.length) (timeHorizon s C₀ x.length)
      (globs M x s (timeWidth C₀ x.length) (timeHorizon s C₀ x.length)) := by
    unfold GlobOK; exact List.take_of_length_le (by rw [length_globs])
  rw [Gn.redGen, out_prelude hs]
  simp only [Gn.out]
  rw [out_descGen length_globs hG hℓ (by omega) (by norm_num),
    out_descGen length_globs hG hℓ (by omega) le_rfl]
  simp

lemma length_le_encodeNats (l : List ℕ) : l.length ≤ (encodeNats l).length := by
  induction l with
  | nil => simp [encodeNats]
  | cons a l ih =>
    simp only [encodeNats, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have : 1 ≤ (encodeNat a).length := by simp [encodeNat]
    omega

/-- The size of the output graphs. -/
lemma nOut_le {C₀ A n L : ℕ} (hL : 1 ≤ L) (h2 : 2 ^ timeWidth C₀ n ≤ A * n)
    (hℓ : timeWidth C₀ n ≤ A * L) {E r N : ℕ} (hE : E ≤ 9 * r + 4) (hr : r ≤ A * L ^ 5)
    (hN : N ≤ A * L ^ 5) :
    4 * (2 ^ timeWidth C₀ n * ((s + 1) *
      (3 * (E * ((s + 1 + 1) * (s + 1 - 1 + timeWidth C₀ n))) + 3 * E + (N + r * 8 + 4)))) ≤
      364 * (s + 1) * A * ((A + 1) * (s + 2) * (s + A + 1)) ^ 2 * n * L ^ 6 := by
  set ℓ := timeWidth C₀ n
  set T := (A + 1) * (s + 2) * (s + A + 1) with hT
  have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hAT : A + 1 ≤ T := by
    rw [hT]
    calc A + 1 = (A + 1) * 1 * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) (by omega)
  have hL5 : L ^ 5 ≤ L ^ 6 := Nat.pow_le_pow_right hL (by norm_num)
  have hL1 : 1 ≤ L ^ 5 := Nat.one_le_pow _ _ hL
  have hE' : E ≤ 13 * T * L ^ 5 := by nlinarith
  have hNS : (s + 1 + 1) * (s + 1 - 1 + ℓ) ≤ T * L := by
    have e1 : s + 1 - 1 + ℓ ≤ (s + A + 1) * L := by
      rw [Nat.add_sub_cancel]; nlinarith
    have e2 : (s + 2) * (s + A + 1) ≤ T := by
      rw [hT, mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
    calc (s + 1 + 1) * (s + 1 - 1 + ℓ) ≤ (s + 2) * ((s + A + 1) * L) := Nat.mul_le_mul le_rfl e1
      _ = (s + 2) * (s + A + 1) * L := by ring
      _ ≤ T * L := Nat.mul_le_mul_right _ e2
  have a1 : E * ((s + 1 + 1) * (s + 1 - 1 + ℓ)) ≤ 13 * T ^ 2 * L ^ 6 :=
    calc E * ((s + 1 + 1) * (s + 1 - 1 + ℓ)) ≤ (13 * T * L ^ 5) * (T * L) := Nat.mul_le_mul hE' hNS
      _ = 13 * T ^ 2 * (L ^ 5 * L) := by ring
      _ = _ := by rw [← pow_succ]
  have a2 : 3 * E + (N + r * 8 + 4) ≤ 52 * T ^ 2 * L ^ 6 := by
    have b1 : 3 * E + (N + r * 8 + 4) ≤ 52 * T * L ^ 5 := by nlinarith
    have b2 : 52 * T * L ^ 5 ≤ 52 * T ^ 2 * L ^ 6 := by
      have : T ≤ T ^ 2 := by nlinarith
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ this) hL5
    omega
  have hF : 3 * (E * ((s + 1 + 1) * (s + 1 - 1 + ℓ))) + 3 * E + (N + r * 8 + 4) ≤
      91 * T ^ 2 * L ^ 6 := by linarith
  calc 4 * (2 ^ ℓ * ((s + 1) * (3 * (E * ((s + 1 + 1) * (s + 1 - 1 + ℓ))) + 3 * E +
        (N + r * 8 + 4)))) ≤ 4 * ((A * n) * ((s + 1) * (91 * T ^ 2 * L ^ 6))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 (Nat.mul_le_mul_left _ hF))
    _ = _ := by ring

lemma famCount_Iv {ℓ H : ℕ} : famCount (Iv M x s ℓ H) =
    3 * ((Iv M x s ℓ H).schemas.length * ((s + 1 + 1) * (s + 1 - 1 + ℓ))) +
      3 * (Iv M x s ℓ H).schemas.length +
      (numLoc M H + (verifierCmds' M x s ℓ H).length * 8 + 4) := by
  have := Iv_numLocations (M := M) (x := x) (s := s) (ℓ := ℓ) (H := H)
  simp only [famCount, numSteps]
  linarith

lemma schemas_Iv_le {ℓ H : ℕ} :
    (Iv M x s ℓ H).schemas.length ≤ 9 * (verifierCmds' M x s ℓ H).length + 4 := by
  have hc : (APv M x s ℓ H).commands.length = (verifierCmds' M x s ℓ H).length := by
    simp only [AP_commands]; exact List.length_map _
  rw [Iv_schemas, ← hc]
  exact length_compiledSchemas_le _ _ _

lemma pow_le_nOut {ℓ H : ℕ} : 2 ^ ℓ ≤ nOut (Iv M x s ℓ H) := by
  have h1 : 1 ≤ (s + 1) * famCount (Iv M x s ℓ H) := by
    rw [famCount_Iv]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold nOut
  calc 2 ^ ℓ = 2 ^ ℓ * 1 := (mul_one _).symm
    _ ≤ 2 ^ ℓ * ((s + 1) * famCount (Iv M x s ℓ H)) := Nat.mul_le_mul_left _ h1
    _ ≤ _ := Nat.le_mul_of_pos_left _ (by norm_num)

/-- The length of the output dominates the input length. -/
lemma length_le_out {C₀ : ℕ} (hs : 2 ≤ s) :
    x.length ≤ (encodeNats ((Gn.redGen M s C₀).out x [])).length := by
  refine le_trans ?_ (length_le_encodeNats _)
  rw [out_redGen hs, List.length_append]
  have h1 : (outG M s C₀ x 0).n + 1 ≤ (graphDescription (outG M s C₀ x 0)).length := by
    simp [graphDescription]
  have h2 : (outG M s C₀ x 0).n = nOut (Iv M x s (timeWidth C₀ x.length)
      (timeHorizon s C₀ x.length)) := rfl
  have h3 := pow_le_nOut (M := M) (x := x) (s := s) (ℓ := timeWidth C₀ x.length)
    (H := timeHorizon s C₀ x.length)
  have h4 := lt_two_pow_timeWidth C₀ x.length
  omega

end Lax119563Proofs.Reduction

namespace Lax119563Proofs.Reduction

open Circuits Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

/--
---
conclusion: Lax119563.TimeReduction.time_reduction
---
The reduction is a generator program (a stack language with a pure list semantics, compiled
once and for all into a deterministic multitape machine): a prelude computes the global
parameters of the code-ordered time simulation program (`ℓ = log₂ n + C₀ + 4`, the horizon,
the numbers of locations, commands and schemas), then two passes emit the descriptions of the
output graphs `G'_0, G'_1`, a renumbering of the matrix graphs of the compiled implicit parity
system (colours by a loop over all classes, edges by loops over the hub classes). Correctness
comes from the composition of the time simulation, the compiler to implicit parity systems and
the matrix compiler (`timeProgram'_graphs`) and the renumbering (`distinguishes_outGraph_iff`);
the graphs have `O(n log^6 n)` vertices. All values have `O(log n)` bits and the generator has
cost `O(n log^22 n)` (growth classes), giving running time `O(n log^24 n)`.
-/
theorem time_reduction : ∃ c : ℕ, ∀ s : ℕ, 2 ≤ s → ∀ M : Machine, Deterministic M →
    (∃ C₀ : ℕ, ∀ x : List Bool, (runOn M x (C₀ * x.length ^ s + C₀)).answer.isSome) →
    ∃ R : Machine, Deterministic R ∧ ∃ C : ℕ, ∀ x : List Bool, 2 ≤ x.length →
      ∃ G₀ G₁ : ColoredGraph,
        (Accepts M x ↔ Distinguishes (s + 1) G₀ G₁) ∧
        G₀.n + G₁.n ≤ C * x.length * Nat.log 2 x.length ^ c ∧
        ComputesWithin R x (encodeGraphPair G₀ G₁) (C * x.length * Nat.log 2 x.length ^ c) := by
  refine ⟨24, fun s hs M _ ⟨C₀, hC₀⟩ => ?_⟩
  have hcost : Gn.HasCost [] (Gn.redGen M s C₀) 1 21 :=
    Gn.hasCost_prelude M s C₀ (by norm_num)
      (Gn.hasCost_seq (Gn.hasCost_descGen M s 0) (Gn.hasCost_descGen M s 1))
  have hwf : (Gn.redGen M s C₀).WFX :=
    Gn.wfx_prelude M s C₀ ⟨Gn.wfx_descGen M s 0 18, Gn.wfx_descGen M s 1 18⟩
  obtain ⟨C₁, hC₁⟩ := Gn.computesWithin_quasiLinear hcost le_rfl hwf
  obtain ⟨Ct, hCt⟩ := time_simulation' M s hs C₀ hC₀
  obtain ⟨Cg, hCg⟩ := timeProgram'_graphs (M := M) hs C₀ hC₀
  obtain ⟨Ks, hKs⟩ : ∃ K, K = 364 * (s + 1) * (Ct + C₀ + 5) * ((Ct + C₀ + 5 + 1) * (s + 2) *
      (s + (Ct + C₀ + 5) + 1)) ^ 2 := ⟨_, rfl⟩
  refine ⟨Gn.machine (Gn.redGen M s C₀).need (Gn.redGen M s C₀), Gn.machine_deterministic _ _,
    C₁ + 2 * Ks, fun x hx => ?_⟩
  set n := x.length with hn
  set L := Nat.log 2 n with hLdef
  have hL : 1 ≤ L := (Circuits.log_facts hx).1
  have hL24 : L ^ 6 ≤ L ^ 24 := Nat.pow_le_pow_right hL (by norm_num)
  refine ⟨outG M s C₀ x 0, outG M s C₀ x 1, ?_, ?_, ?_⟩
  · exact (hCg x hx).1.trans (distinguishes_outGraph_iff
      (Iv M x s (timeWidth C₀ x.length) (timeHorizon s C₀ x.length)) (by omega)).symm
  · obtain ⟨-, -, -, h2, hN, hr⟩ := hCt x hx
    have hcr : (timeProgram' M s C₀ x).commands.length =
        (verifierCmds' M x s (timeWidth C₀ n) (timeHorizon s C₀ n)).length := List.length_map _
    rw [hcr] at hr
    have hN' : numLoc M (timeHorizon s C₀ n) ≤ Ct * L ^ 5 := hN
    have hℓ : timeWidth C₀ n ≤ (Ct + C₀ + 5) * L := by
      unfold Circuits.timeWidth; nlinarith
    have key := nOut_le (s := s) (C₀ := C₀) (A := Ct + C₀ + 5) (n := n) (L := L) hL
      (h2.trans (Nat.mul_le_mul_right _ (by omega))) hℓ schemas_Iv_le
      (hr.trans (Nat.mul_le_mul_right _ (by omega))) (hN'.trans (Nat.mul_le_mul_right _ (by omega)))
    rw [← famCount_Iv] at key
    have e : (outG M s C₀ x 0).n + (outG M s C₀ x 1).n =
        2 * nOut (Iv M x s (timeWidth C₀ n) (timeHorizon s C₀ n)) := by
      show nOut _ + nOut _ = _; ring
    rw [e]
    have key' : nOut (Iv M x s (timeWidth C₀ n) (timeHorizon s C₀ n)) ≤ Ks * n * L ^ 6 := by
      rw [hKs]; exact key
    have : Ks * n * L ^ 6 ≤ Ks * n * L ^ 24 := Nat.mul_le_mul_left _ hL24
    have : C₁ * n * L ^ 24 + 2 * (Ks * n * L ^ 24) = (C₁ + 2 * Ks) * n * L ^ 24 := by ring
    omega
  · have H := hC₁ x hx (length_le_out hs)
    rw [out_redGen hs] at H
    refine ComputesWithin.mono H ?_
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))

end Lax119563Proofs.Reduction
