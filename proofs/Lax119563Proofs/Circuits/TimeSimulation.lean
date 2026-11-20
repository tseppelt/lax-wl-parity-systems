import Lax119563Proofs.Circuits.VerifierComplete
import Lax119563Proofs.Circuits.LocCode

/-!
# Deterministic time as a register program

The mathematical content of the lemma "Time simulation": for a machine `M` halting within
`C₀ n^s + C₀` steps (`s ≥ 2`), the explicit `s`-register program `timeProgram M s C₀ x` over
`𝔽₂^ℓ` with `ℓ = timeWidth C₀ n = log₂ n + C₀ + 4` accepts the query
`(timeQuery M s C₀ x, 0)` iff `M` accepts `x`; it has at most `C (log₂ n)^5` locations and
commands (`time_simulation`).

The program depends on `x` only through `n = |x|`, except for the membership tables of the
guards `hitGuard` on register `0`, which list the offsets `u < 2^ℓ` at which the initial
first tape carries a given cell value.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime Programs

variable {M : Machine} {H : ℕ}

instance : DecidableEq (Loc M H) := fun a b =>
  decidable_of_iff (a.code = b.code) Loc.code_injective.eq_iff

/-- The register width `ℓ = log₂ n + C₀ + 4`. -/
def timeWidth (C₀ n : ℕ) : ℕ := Nat.log 2 n + C₀ + 4

/-- The horizon `H = s ℓ - 2`; the simulation covers `2^H` steps. -/
def timeHorizon (s C₀ n : ℕ) : ℕ := s * timeWidth C₀ n - 2

/-- The address commands of the verifier, over the listed locations without repetitions. -/
def verifierCmds (M : Machine) (x : List Bool) (s ℓ H : ℕ) : List (ACmd (Loc M H) s) :=
  progCmds ℓ (allLocs M H).dedup (moves M x s ℓ H)

lemma code_accept_ne_reject : (Loc.accept : Loc M H).code ≠ Loc.reject.code := fun h => by
  have := Loc.code_injective h
  cases this

/-- The register program simulating `M` on `x`. -/
def timeProgram (M : Machine) (s C₀ : ℕ) (x : List Bool) :
    RegisterProgram s (timeWidth C₀ x.length) :=
  compile (numLoc M (timeHorizon s C₀ x.length)) Loc.code .accept .reject
    code_accept_ne_reject
    (verifierCmds M x s (timeWidth C₀ x.length) (timeHorizon s C₀ x.length))

/-- The query location of `timeProgram`; the query valuation is zero. -/
def timeQuery (M : Machine) (s C₀ : ℕ) (x : List Bool) :
    Fin (timeProgram M s C₀ x).numLocations :=
  (Loc.query : Loc M (timeHorizon s C₀ x.length)).code

/-! ## Correctness -/

lemma accepts_iff_answer {x : List Bool} {T : ℕ} (hT : (runOn M x T).answer.isSome) :
    Accepts M x ↔ (runOn M x T).answer = some true := by
  constructor
  · rintro ⟨t, ht⟩
    rcases le_or_gt t T with h | h
    · have hh : (runOn M x t).answer.isSome := by rw [ht]; rfl
      have := runOn_halted x hh (T - t)
      rw [Nat.add_sub_cancel' h] at this
      rw [this]; exact ht
    · have := runOn_halted x hT (t - T)
      rw [Nat.add_sub_cancel' h.le] at this
      rw [← this]; exact ht
  · intro h; exact ⟨T, h⟩

/-! ## Size bounds -/

lemma length_flatMap_le {α β : Type} {l : List α} {f : α → List β} {k : ℕ}
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := h a (by simp)
    have := ih fun b hb => h b (by simp [hb])
    nlinarith

/-- A bound on the number of moves at a location other than the root cells `cell 0 0 ν c`. -/
def movBound0 (M : Machine) : ℕ := 16 + 8 * (M.symbols + 3) * rowBound M

/-- A bound on the number of moves at a location. -/
def movBound (M : Machine) (s : ℕ) : ℕ := s + movBound0 M

/-- `1` at the root cells `cell 0 0 ν c` (which carry the `s - 1` tests `missGuard`), else `0`. -/
def Loc.rootCount : Loc M H → ℕ
  | .cell d θ _ _ => if θ.val = 0 ∧ d.val = 0 then 1 else 0
  | _ => 0

lemma Loc.rootCount_le_one (L : Loc M H) : L.rootCount ≤ 1 := by
  cases L <;> simp only [Loc.rootCount] <;> (try split_ifs) <;> omega

lemma length_allRows : (allRows M).length = rowBound M := by
  simp [allRows, allExt, allFun, allOptBool, List.length_product, rowBound]
  ring

lemma moves_length_le' (x : List Bool) (s ℓ : ℕ) (L : Loc M H) :
    (moves M x s ℓ H L).length ≤ movBound0 M + L.rootCount * s := by
  have hR : 3 * (M.states + 1) ≤ rowBound M := by
    unfold rowBound; exact Nat.le_mul_of_pos_right _ (by positivity)
  have hR1 : 1 ≤ rowBound M := le_trans (by omega) hR
  have hS : M.symbols + 3 ≤ 8 * (M.symbols + 3) * rowBound M := by nlinarith
  have hRS : rowBound M ≤ 8 * (M.symbols + 3) * rowBound M := by nlinarith
  have hE : (allExt M).length = 3 * (M.states + 1) := by
    simp [allExt, allOptBool, List.length_product]; ring
  unfold movBound0
  cases L with
  | accept => simp [moves, Loc.rootCount]
  | reject => simp [moves, Loc.rootCount]
  | query =>
    simp only [Loc.rootCount, zero_mul, add_zero]
    simp only [moves, List.length_map]
    have := List.length_filter_le (fun p : ExtState M => decide (p.2 = some true)) (allExt M)
    omega
  | cell d θ ν c =>
    simp only [Loc.rootCount]
    by_cases hr : θ.val = 0 ∧ d.val = 0
    · rw [if_pos hr, one_mul]
      simp only [moves, if_pos hr.1, if_pos hr.2]
      split_ifs
      · simp only [List.length_cons, List.length_map]
        have := List.length_filter_le (fun i : Fin s => decide (i.val ≠ 0)) (List.finRange s)
        simp only [List.length_finRange] at this
        omega
      · simp; omega
    rw [if_neg hr, zero_mul, add_zero]
    simp only [moves]
    split_ifs
    · exact absurd ⟨‹_›, ‹_›⟩ hr
    · exact absurd ⟨‹_›, ‹_›⟩ hr
    · (simp [List.length_flatMap] <;> omega)
    · (simp <;> omega)
    · have : ((allRows M).flatMap fun ρ => (allCV M).flatMap fun old =>
          ((List.finRange 4).filter fun jj =>
            decide (nextCell ρ.1 ρ.2.2 ν ((ρ.2.1 ν).val + 1 : ℤ) (jj.val : ℤ) old = c)).map
            fun jj => (Move.step 0 2 jj.val jj.val (.baseCell ν ρ old 0) : Move (Loc M H) s)).length
          ≤ (allRows M).length * ((allCV M).length * 4) := by
        apply length_flatMap_le
        intro ρ _
        apply length_flatMap_le
        intro old _
        simp only [List.length_map]
        exact le_trans (List.length_filter_le _ _) (by simp)
      have hcv : (allCV M).length = 2 * (M.symbols + 3) := by
        simp [allCV, allBool, List.length_product]; ring
      rw [length_allRows, hcv] at this
      nlinarith
    · (simp <;> omega)
  | state d θ p =>
    simp only [Loc.rootCount, zero_mul, add_zero]
    simp only [moves]
    split_ifs
    · (simp <;> omega)
    · (simp <;> omega)
    · (simp <;> omega)
    · (simp <;> omega)
    · simp only [List.length_map]
      have := List.length_filter_le (fun ρ : Row M => decide (nextExt ρ.1 ρ.2.2 = p)) (allRows M)
      rw [length_allRows] at this
      nlinarith
    · (simp <;> omega)
  | headIn d θ ν u =>
    simp only [Loc.rootCount, zero_mul, add_zero]
    simp only [moves]
    split_ifs
    · simp only [List.length_map, List.length_finRange]; omega
    · (simp [List.length_flatMap] <;> omega)
    · (simp <;> omega)
  | headSet d θ ν β => simp only [Loc.rootCount, zero_mul, add_zero]; simp only [moves]; split_ifs <;> (simp <;> omega)
  | restore d θ ν c β => simp only [Loc.rootCount, zero_mul, add_zero]; simp only [moves]; split_ifs <;> (simp <;> omega)
  | gather d θ ν c β => simp only [Loc.rootCount, zero_mul, add_zero]; simp only [moves]; split_ifs <;> (simp <;> omega)
  | baseCell ν ρ old k => simp only [Loc.rootCount, zero_mul, add_zero]; simp only [moves]; split_ifs <;> (simp <;> omega)
  | baseState ρ k => simp only [Loc.rootCount, zero_mul, add_zero]; simp only [moves]; split_ifs <;> (simp <;> omega)
  | setJ ν h c => simp [moves, Loc.rootCount]; omega

end Lax119563Proofs.Circuits
