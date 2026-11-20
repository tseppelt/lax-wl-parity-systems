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

lemma log_facts {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Nat.log 2 n ∧ n < 2 ^ (Nat.log 2 n + 1) ∧
    2 ^ Nat.log 2 n ≤ n := by
  refine ⟨Nat.le_log_of_pow_le (by norm_num) (by simpa using hn),
    Nat.lt_pow_succ_log_self (by norm_num) n, Nat.pow_log_le_self 2 (by omega)⟩

lemma params_of {s C₀ : ℕ} (hs : 2 ≤ s) {x : List Bool} (hx : 2 ≤ x.length) :
    Params x s (timeWidth C₀ x.length) (timeHorizon s C₀ x.length) := by
  obtain ⟨-, h2, -⟩ := log_facts hx
  have hℓ : 4 ≤ timeWidth C₀ x.length := by unfold timeWidth; omega
  have hsl : 2 * timeWidth C₀ x.length ≤ s * timeWidth C₀ x.length :=
    Nat.mul_le_mul_right _ hs
  refine ⟨?_, by omega, ?_, ?_⟩
  · unfold timeHorizon; omega
  · unfold timeHorizon; omega
  · calc x.length < 2 ^ (Nat.log 2 x.length + 1) := h2
      _ ≤ 2 ^ timeWidth C₀ x.length := Nat.pow_le_pow_right (by norm_num) (by unfold timeWidth; omega)

lemma halts_by_horizon {s C₀ : ℕ} (hs : 2 ≤ s)
    (hC₀ : ∀ x : List Bool, (runOn M x (C₀ * x.length ^ s + C₀)).answer.isSome)
    {x : List Bool} (hx : 2 ≤ x.length) :
    (runOn M x (2 ^ timeHorizon s C₀ x.length)).answer.isSome := by
  set n := x.length
  obtain ⟨-, h2, -⟩ := log_facts hx
  have hns : n ^ s ≤ 2 ^ ((Nat.log 2 n + 1) * s) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h2.le s
  have hpos : 1 ≤ n ^ s := Nat.one_le_pow _ _ (by omega)
  have hC : 2 * C₀ ≤ 2 ^ (C₀ + 1) := by
    rw [pow_succ]; have := Nat.lt_two_pow_self (n := C₀); omega
  have hT : C₀ * n ^ s + C₀ ≤ 2 ^ timeHorizon s C₀ n := by
    calc C₀ * n ^ s + C₀ ≤ 2 * C₀ * n ^ s := by nlinarith
      _ ≤ 2 ^ (C₀ + 1) * 2 ^ ((Nat.log 2 n + 1) * s) := Nat.mul_le_mul hC hns
      _ = 2 ^ ((Nat.log 2 n + 1) * s + C₀ + 1) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ timeHorizon s C₀ n := by
        apply Nat.pow_le_pow_right (by norm_num)
        unfold timeHorizon timeWidth
        have : s * (Nat.log 2 n + C₀ + 4) = (Nat.log 2 n + 1) * s + s * C₀ + 3 * s := by ring
        have : C₀ ≤ s * C₀ := Nat.le_mul_of_pos_left _ (by omega)
        omega
  have := runOn_halted x (hC₀ x) (2 ^ timeHorizon s C₀ n - (C₀ * n ^ s + C₀))
  rw [Nat.add_sub_cancel' hT] at this
  rw [this]; exact hC₀ x

/-- Correctness: the query accepts iff `M` accepts `x`. -/
theorem timeProgram_accepts_iff {s C₀ : ℕ} (hs : 2 ≤ s)
    (hC₀ : ∀ x : List Bool, (runOn M x (C₀ * x.length ^ s + C₀)).answer.isSome)
    {x : List Bool} (hx : 2 ≤ x.length) :
    (timeProgram M s C₀ x).Accepts (timeQuery M s C₀ x) (fun _ _ => 0) ↔ Accepts M x := by
  have P := params_of (C₀ := C₀) hs hx
  have hmask : MasksBounded s (timeWidth C₀ x.length)
      (verifierCmds M x s (timeWidth C₀ x.length) (timeHorizon s C₀ x.length)) :=
    progCmds_masks P.hH fun src _ => moves_wf src
  unfold timeProgram timeQuery
  rw [compile_accepts Loc.code_injective _ hmask, addr_zero]
  unfold verifierCmds
  rw [verifier_accepts_iff P (fun L => List.mem_dedup.mpr (mem_allLocs M _ L)) _
    (by positivity)]
  rw [accepts_iff_answer (halts_by_horizon hs hC₀ hx)]
  rfl

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

lemma moves_length_le (x : List Bool) (s ℓ : ℕ) (L : Loc M H) :
    (moves M x s ℓ H L).length ≤ movBound M s := by
  have h1 := moves_length_le' x s ℓ L
  have h2 : L.rootCount * s ≤ 1 * s := Nat.mul_le_mul_right _ L.rootCount_le_one
  unfold movBound; omega

lemma dedup_length_le : (allLocs M H).dedup.length ≤ numLoc M H := by
  have h : ((allLocs M H).dedup.map Loc.code).Nodup :=
    (List.nodup_dedup _).map Loc.code_injective
  have := h.length_le_card
  simpa using this

lemma timeProgram_numLocations (s C₀ : ℕ) (x : List Bool) :
    (timeProgram M s C₀ x).numLocations = numLoc M (timeHorizon s C₀ x.length) := rfl

lemma timeProgram_commands_le (s C₀ : ℕ) (x : List Bool) :
    (timeProgram M s C₀ x).commands.length ≤
      numLoc M (timeHorizon s C₀ x.length) * movBound M s := by
  simp only [timeProgram, compile, List.length_map, verifierCmds, progCmds]
  calc _ ≤ (allLocs M (timeHorizon s C₀ x.length)).dedup.length * movBound M s :=
        length_flatMap_le fun L _ => by rw [List.length_map]; exact moves_length_le _ _ _ L
    _ ≤ _ := Nat.mul_le_mul_right _ dedup_length_le

lemma numLoc_le_pow : numLoc M H ≤ 16 * radix M H ^ 5 := by
  rw [numLoc_eq]
  have := cM_le_radix (M := M) (H := H)
  calc 16 * cM M ^ 3 * radix M H ^ 2 ≤ 16 * radix M H ^ 3 * radix M H ^ 2 := by gcongr
    _ = _ := by ring

lemma numLoc_le {s C₀ : ℕ} (hs : 1 ≤ s) {x : List Bool} (hx : 2 ≤ x.length) :
    numLoc M (timeHorizon s C₀ x.length) ≤
      16 * (s * (C₀ + 5) + cM M) ^ 5 * Nat.log 2 x.length ^ 5 := by
  obtain ⟨h1, -, -⟩ := log_facts hx
  obtain ⟨L, hL⟩ : ∃ L, Nat.log 2 x.length = L := ⟨_, rfl⟩
  rw [hL] at h1 ⊢
  have hr : radix M (timeHorizon s C₀ x.length) ≤ (s * (C₀ + 5) + cM M) * L := by
    unfold radix timeHorizon timeWidth
    rw [hL]
    have h2 : s * (L + C₀ + 4) ≤ s * (C₀ + 5) * L := by
      have : L + C₀ + 4 ≤ (C₀ + 5) * L := by nlinarith
      calc s * (L + C₀ + 4) ≤ s * ((C₀ + 5) * L) := Nat.mul_le_mul_left _ this
        _ = _ := by ring
    have h3 : cM M ≤ cM M * L := Nat.le_mul_of_pos_right _ h1
    have h4 : s * (L + C₀ + 4) - 2 + 1 ≤ s * (L + C₀ + 4) := by
      have : L + C₀ + 4 ≤ s * (L + C₀ + 4) := Nat.le_mul_of_pos_left _ hs
      omega
    have e : (s * (C₀ + 5) + cM M) * L = s * (C₀ + 5) * L + cM M * L := by ring
    omega
  calc numLoc M (timeHorizon s C₀ x.length) ≤ 16 * radix M (timeHorizon s C₀ x.length) ^ 5 :=
        numLoc_le_pow
    _ ≤ 16 * ((s * (C₀ + 5) + cM M) * L) ^ 5 := by gcongr
    _ = _ := by ring

/-- **Time simulation.** For a machine `M` halting within `C₀ n^s + C₀` steps with `s ≥ 2`,
the register program `timeProgram M s C₀ x` with `s` registers over `𝔽₂^ℓ`,
`ℓ = timeWidth C₀ |x|`, and the query `(timeQuery M s C₀ x, 0)` satisfy, for `|x| ≥ 2`:
the query accepts iff `M` accepts `x`; `n ≤ 2^ℓ ≤ C n`; and the numbers of control locations
and of commands are at most `C (log₂ n)^5`. -/
theorem time_simulation (M : Machine) (s : ℕ) (hs : 2 ≤ s) (C₀ : ℕ)
    (hC₀ : ∀ x : List Bool, (runOn M x (C₀ * x.length ^ s + C₀)).answer.isSome) :
    ∃ C : ℕ, ∀ x : List Bool, 2 ≤ x.length →
      1 ≤ timeWidth C₀ x.length ∧
      ((timeProgram M s C₀ x).Accepts (timeQuery M s C₀ x) (fun _ _ => 0) ↔ Accepts M x) ∧
      x.length ≤ C * 2 ^ timeWidth C₀ x.length ∧
      2 ^ timeWidth C₀ x.length ≤ C * x.length ∧
      (timeProgram M s C₀ x).numLocations ≤ C * Nat.log 2 x.length ^ 5 ∧
      (timeProgram M s C₀ x).commands.length ≤ C * Nat.log 2 x.length ^ 5 := by
  refine ⟨16 * (s * (C₀ + 5) + cM M) ^ 5 * (movBound M s + 1) + 2 ^ (C₀ + 4), ?_⟩
  intro x hx
  have hNL := numLoc_le (M := M) (s := s) (C₀ := C₀) (by omega) hx
  generalize hK : 16 * (s * (C₀ + 5) + cM M) ^ 5 = K at hNL ⊢
  have hKC0 : K ≤ K * (movBound M s + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hKC1 : K * movBound M s ≤ K * (movBound M s + 1) := Nat.mul_le_mul_left _ (by omega)
  generalize hC : K * (movBound M s + 1) + 2 ^ (C₀ + 4) = C
  obtain ⟨-, -, h3⟩ := log_facts hx
  have P := params_of (C₀ := C₀) hs hx
  have hC1 : K * (movBound M s + 1) ≤ C := hC ▸ Nat.le_add_right _ _
  have hC2 : 2 ^ (C₀ + 4) ≤ C := hC ▸ Nat.le_add_left _ _
  have hKC : K ≤ C := le_trans hKC0 hC1
  refine ⟨by unfold timeWidth; omega, timeProgram_accepts_iff hs hC₀ hx, ?_, ?_, ?_, ?_⟩
  · have := P.hx
    have : 1 ≤ C := le_trans Nat.one_le_two_pow hC2
    nlinarith
  · have e : 2 ^ timeWidth C₀ x.length = 2 ^ Nat.log 2 x.length * 2 ^ (C₀ + 4) := by
      unfold timeWidth; rw [← pow_add]; ring_nf
    rw [e]
    have : 2 ^ (C₀ + 4) ≤ C := hC2
    calc 2 ^ Nat.log 2 x.length * 2 ^ (C₀ + 4) ≤ x.length * C := Nat.mul_le_mul h3 this
      _ = C * x.length := Nat.mul_comm _ _
  · rw [timeProgram_numLocations]
    exact le_trans hNL (Nat.mul_le_mul_right _ hKC)
  · calc _ ≤ numLoc M (timeHorizon s C₀ x.length) * movBound M s := timeProgram_commands_le _ _ _
      _ ≤ K * Nat.log 2 x.length ^ 5 * movBound M s := Nat.mul_le_mul_right _ hNL
      _ ≤ C * Nat.log 2 x.length ^ 5 := by
        have : K * movBound M s ≤ C := le_trans hKC1 hC1
        calc K * Nat.log 2 x.length ^ 5 * movBound M s
            = K * movBound M s * Nat.log 2 x.length ^ 5 := by ring
          _ ≤ C * Nat.log 2 x.length ^ 5 := Nat.mul_le_mul_right _ this

end Lax119563Proofs.Circuits
