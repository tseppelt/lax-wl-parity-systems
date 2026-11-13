import Lax119563.ParitySystems
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Order.CompleteLattice.Basic

/-!
# Unit propagation: single steps and invariants

Elementary facts about the rounds `K_r` of unit propagation in a parity system: monotonicity,
single inference steps through binary and ternary equations, and the invariant argument: if a
partial assignment contains the initial facts and is closed under the inference rule of every
equation, then it contains every derived fact, so no conflict ever occurs.
-/

open Lax119563.ParitySystems

namespace Lax119563Proofs.Programs

namespace ParitySystem

variable {V : Type*} [DecidableEq V] (P : ParitySystem V)

theorem known_succ_subset (r : ℕ) : P.known r ⊆ P.known (r + 1) :=
  Set.subset_union_left

theorem known_mono {r r' : ℕ} (h : r ≤ r') : P.known r ⊆ P.known r' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (known_succ_subset P _)

/-- A binary equation `X + Y = 0` transmits the value of `X` to `Y` in one round. -/
theorem known_pair {X Y : V} (hXY : X ≠ Y) (hh : ({X, Y} : Finset V) ∈ P.equations)
    {b : ZMod 2} {r : ℕ} (hX : (X, b) ∈ P.known r) : (Y, b) ∈ P.known (r + 1) := by
  right
  refine ⟨{X, Y}, hh, by simp, fun _ => b, ?_, ?_⟩
  · intro Z hZ hZY
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl
    · exact hX
    · exact absurd rfl hZY
  · simp [Finset.erase_insert_of_ne hXY]

/-- A ternary equation `X + Y + Z = 0` infers `Z` from `X` and `Y` in one round. -/
theorem known_triple {X Y Z : V} (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z)
    (hh : ({X, Y, Z} : Finset V) ∈ P.equations) {b c : ZMod 2} {r : ℕ}
    (hX : (X, b) ∈ P.known r) (hY : (Y, c) ∈ P.known r) : (Z, b + c) ∈ P.known (r + 1) := by
  right
  refine ⟨{X, Y, Z}, hh, by simp, fun W => if W = X then b else c, ?_, ?_⟩
  · intro W hW hWZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl | rfl
    · simpa using hX
    · simpa [hXY.symm] using hY
    · exact absurd rfl hWZ
  · rw [Finset.erase_insert_of_ne hXZ, Finset.erase_insert_of_ne hYZ, Finset.erase_singleton,
      Finset.sum_insert (by simpa using hXY)]
    simp [hXY.symm]

/-- The partial assignment `val` is closed under the inference rule of the equation `h`. -/
def Closed (val : V → Option (ZMod 2)) (h : Finset V) : Prop :=
  ∀ X ∈ h, ∀ b : V → ZMod 2, (∀ Y ∈ h, Y ≠ X → val Y = some (b Y)) →
    val X = some (∑ Y ∈ h.erase X, b Y)

theorem closed_pair {val : V → Option (ZMod 2)} {X Y : V} (hXY : X ≠ Y) (hv : val X = val Y) :
    Closed val {X, Y} := by
  intro W hW b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hW
  rcases hW with rfl | rfl
  · rw [Finset.erase_insert (by simpa using hXY), Finset.sum_singleton, hv]
    exact hb Y (by simp) hXY.symm
  · rw [Finset.erase_insert_of_ne hXY, Finset.erase_singleton, Finset.insert_empty,
      Finset.sum_singleton, ← hv]
    exact hb X (by simp) hXY

theorem closed_triple {val : V → Option (ZMod 2)} {X Y Z : V} (hXY : X ≠ Y) (hXZ : X ≠ Z)
    (hYZ : Y ≠ Z)
    (hX : ∀ b c, val Y = some b → val Z = some c → val X = some (b + c))
    (hY : ∀ b c, val X = some b → val Z = some c → val Y = some (b + c))
    (hZ : ∀ b c, val X = some b → val Y = some c → val Z = some (b + c)) :
    Closed val {X, Y, Z} := by
  intro W hW b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hW
  rcases hW with rfl | rfl | rfl
  · have : ({W, Y, Z} : Finset V).erase W = {Y, Z} :=
      Finset.erase_insert (by simp [hXY, hXZ])
    rw [this, Finset.sum_pair hYZ]
    exact hX _ _ (hb Y (by simp) hXY.symm) (hb Z (by simp) hXZ.symm)
  · rw [Finset.erase_insert_of_ne hXY, Finset.erase_insert (by simpa using hYZ),
      Finset.sum_pair hXZ]
    exact hY _ _ (hb X (by simp) hXY) (hb Z (by simp) hYZ.symm)
  · rw [Finset.erase_insert_of_ne hXZ, Finset.erase_insert_of_ne hYZ, Finset.erase_singleton,
      Finset.insert_empty, Finset.sum_pair hXY]
    exact hZ _ _ (hb X (by simp) hXZ) (hb Y (by simp) hYZ)

/-- If the partial assignment `val` contains the initial facts and is closed under every
equation, then it contains every fact derived by unit propagation. -/
theorem known_subset_of_closed (val : V → Option (ZMod 2))
    (hinit : ∀ f ∈ P.initial, val f.1 = some f.2)
    (hcl : ∀ h ∈ P.equations, Closed val h) : ∀ r, ∀ f ∈ P.known r, val f.1 = some f.2 := by
  intro r
  induction r with
  | zero => exact hinit
  | succ r ih =>
    rintro f (hf | ⟨h, hh, hfh, b, hb, hfb⟩)
    · exact ih f hf
    · rw [hfb]
      exact hcl h hh f.1 hfh b fun Y hY hYf => ih (Y, b Y) (hb Y hY hYf)

theorem not_hasConflict_of_closed (val : V → Option (ZMod 2))
    (hinit : ∀ f ∈ P.initial, val f.1 = some f.2)
    (hcl : ∀ h ∈ P.equations, Closed val h) (r : ℕ) : ¬ P.HasConflict r := by
  rintro ⟨X, h0, h1⟩
  have e0 := known_subset_of_closed P val hinit hcl r _ h0
  have e1 := known_subset_of_closed P val hinit hcl r _ h1
  rw [e0] at e1
  exact absurd (Option.some.inj e1) (by decide : (0 : ZMod 2) ≠ 1)

theorem conflictRound_lt_top_iff : P.conflictRound < ⊤ ↔ ∃ r, P.HasConflict r := by
  simp only [ParitySystem.conflictRound, iInf_lt_iff]
  constructor
  · rintro ⟨r, hr, -⟩
    exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, hr, ENat.natCast_lt_top r⟩

theorem conflictRound_le {r : ℕ} (h : P.HasConflict r) : P.conflictRound ≤ r :=
  iInf₂_le r h

end ParitySystem

end Lax119563Proofs.Programs
