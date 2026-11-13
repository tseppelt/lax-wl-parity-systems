import Lax119563Proofs.Matrix.SpoilerMain
import Lax119563Proofs.Matrix.Duplicator
import Lax119563Proofs.Matrix.Size
import Lax119563Proofs.Game.Characterization
import Lax119563Proofs.Programs.Correctness
import Lax119563Proofs.Programs.Size
import Lax119563Proofs.Circuits.TimeSimulation

/-!
# Mathematical assembly of the reduction

For a register program `P` with `s ≥ 2` registers and a query `(p₀, a₀)`, the matrix graphs of
the compiled implicit parity system are distinguished by `(s+1)`-WL iff the query accepts
(`distinguishes_matrixGraph_iff`), and their vertex numbers are bounded in terms of the numbers
of locations and commands (`matrixGraph_n_le`).
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.PebbleGame
open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler
open Lax119563Proofs.Programs Lax119563Proofs.Matrix

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ}

/-- **Correctness of the composition** register program → implicit parity system → matrix
graphs: `(s+1)`-WL distinguishes the two graphs iff the query accepts. -/
theorem distinguishes_matrixGraph_iff (hs : 2 ≤ s) (P : RegisterProgram s ℓ)
    (p₀ : Fin P.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    Distinguishes (s + 1) (matrixGraph (P.compile p₀ a₀) 0) (matrixGraph (P.compile p₀ a₀) 1) ↔
      P.Accepts p₀ a₀ := by
  have hk : 2 ≤ s + 1 := by omega
  rw [← P.conflictRound_compile_lt_top_iff p₀ a₀]
  constructor
  · intro hd
    by_contra hlt
    have htop : (P.compile p₀ a₀).conflictRound = ⊤ := not_lt_top_iff.mp hlt
    have hw : DuplicatorWins (s + 1 + 1) (matrixGraph (P.compile p₀ a₀) 0)
        (matrixGraph (P.compile p₀ a₀) 1) := by
      intro r
      apply duplicatorSurvives hk
      intro hc
      have := ParitySystem.conflictRound_le _ hc
      rw [ImplicitParitySystem.conflictRound] at htop
      rw [htop] at this
      exact absurd this (by simp)
    exact (Game.duplicatorWins_iff hk _ _).mp hw hd
  · intro hlt
    obtain ⟨τ, hτ⟩ := ENat.ne_top_iff_exists.mp hlt.ne
    obtain ⟨r, -, hr⟩ := Game.distinguishesAfter_of_spoilerWinsWithin hk
      (spoilerWins (I := P.compile p₀ a₀) hk hτ.symm)
    exact ⟨r, hr⟩

/-- Both matrix graphs have the vertex list of the system as vertex set. -/
lemma matrixGraph_n {k : ℕ} (I : ImplicitParitySystem k ℓ) (ε : ZMod 2) :
    (matrixGraph I ε).n = (vertexList I).length := rfl

/-- **Size of the composition.** -/
theorem matrixGraph_n_le (hs : 1 ≤ s) (hℓ : 1 ≤ ℓ) (P : RegisterProgram s ℓ)
    (p₀ : Fin P.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    (matrixGraph (P.compile p₀ a₀) 0).n + (matrixGraph (P.compile p₀ a₀) 1).n ≤
      3200 * ((s + 1) * 2 ^ ℓ * P.numLocations +
        (s + 1) ^ 2 * 2 ^ ℓ * ℓ * (P.commands.length + 1)) := by
  have h1 := card_vertexList_le (I := P.compile p₀ a₀) (by omega)
  have h2 := P.sizeParameter_compile_le p₀ a₀ hℓ
  show (vertexList (P.compile p₀ a₀)).length + (vertexList (P.compile p₀ a₀)).length ≤ _
  linarith

/-- The arithmetic of the final size bound: with `w, r ≤ A L^5`, `2^ℓ ≤ A n` and
`ℓ ≤ A L` (`L ≥ 1`), the bound of `matrixGraph_n_le` is at most `C n L^6`. -/
lemma size_poly {s A n L w r ℓ : ℕ} (hL : 1 ≤ L) (hw : w ≤ A * L ^ 5) (hr : r ≤ A * L ^ 5)
    (h2 : 2 ^ ℓ ≤ A * n) (hℓ : ℓ ≤ A * L) :
    3200 * ((s + 1) * 2 ^ ℓ * w + (s + 1) ^ 2 * 2 ^ ℓ * ℓ * (r + 1)) ≤
      12800 * (s + 1) ^ 2 * (A + 1) ^ 3 * n * L ^ 6 := by
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
  calc 3200 * ((s + 1) * X * w + (s + 1) ^ 2 * X * ℓ * (r + 1))
      ≤ 3200 * ((s + 1) ^ 2 * (A + 1) ^ 3 * n * L ^ 6 +
          2 * ((s + 1) ^ 2 * (A + 1) ^ 3 * n * L ^ 6)) := by
        exact Nat.mul_le_mul_left _ (Nat.add_le_add e1 e2)
    _ = 9600 * ((s + 1) ^ 2 * (A + 1) ^ 3 * n * L ^ 6) := by ring
    _ ≤ 12800 * ((s + 1) ^ 2 * (A + 1) ^ 3 * n * L ^ 6) := Nat.mul_le_mul_right _ (by norm_num)
    _ = _ := by ring

open Lax119563.DeterministicTime in
/-- **Assembly for the time simulation program.** The matrix graphs of the compiled
`timeProgram` are distinguished by `(s+1)`-WL iff `M` accepts `x`, and have `O(n log^6 n)`
vertices. -/
theorem timeProgram_graphs {M : Lax489179.TuringMachine.Machine} {s : ℕ} (hs : 2 ≤ s) (C₀ : ℕ)
    (hC₀ : ∀ x : List Bool, (runOn M x (C₀ * x.length ^ s + C₀)).answer.isSome) :
    ∃ C : ℕ, ∀ x : List Bool, 2 ≤ x.length →
      let I := (Circuits.timeProgram M s C₀ x).compile (Circuits.timeQuery M s C₀ x)
        (fun _ _ => 0)
      (Accepts M x ↔ Distinguishes (s + 1) (matrixGraph I 0) (matrixGraph I 1)) ∧
      (matrixGraph I 0).n + (matrixGraph I 1).n ≤ C * x.length * Nat.log 2 x.length ^ 6 := by
  obtain ⟨C, hC⟩ := Circuits.time_simulation M s hs C₀ hC₀
  refine ⟨12800 * (s + 1) ^ 2 * (C + C₀ + 5 + 1) ^ 3, fun x hx => ?_⟩
  obtain ⟨hℓ, hacc, -, h2, hw, hr⟩ := hC x hx
  have hL : 1 ≤ Nat.log 2 x.length := (Circuits.log_facts hx).1
  refine ⟨(hacc.symm.trans (distinguishes_matrixGraph_iff hs _ _ _).symm), ?_⟩
  refine (matrixGraph_n_le (by omega) hℓ _ _ _).trans ?_
  have hℓ' : Circuits.timeWidth C₀ x.length ≤ (C + C₀ + 5) * Nat.log 2 x.length := by
    unfold Circuits.timeWidth; nlinarith
  have := size_poly (s := s) (A := C + C₀ + 5) hL
    (hw.trans (Nat.mul_le_mul_right _ (by omega)))
    (hr.trans (Nat.mul_le_mul_right _ (by omega)))
    (h2.trans (Nat.mul_le_mul_right _ (by omega))) hℓ'
  exact this

end Lax119563Proofs.Reduction
