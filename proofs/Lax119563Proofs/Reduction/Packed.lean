import Lax119563.MatrixCompiler
import Lax119563Proofs.Reduction.Prelude
import Lax119563Proofs.Programs.Correctness
import Lax119563Proofs.Programs.Size

/-!
# The packed size of the time simulation system

The implicit parity system `Iv M x s ℓ H` (the compiled code-ordered verifier program, the
system that the reduction generator emits) has, under the standing hypotheses
`Params x s ℓ H` (`H + 2 ≤ s ℓ`, `0 < ℓ ≤ H`, `|x| < 2^ℓ`) and `s ≤ H + 2`,

* `O_M((H + 1)^2)` locations: the verifier locations are numbered densely enough
  (`numLoc M H = 16 cM^3 (H + 1 + cM)^2`, only the two depth fields `d, u` grow with `H`),
  and there are `O_M((H + 1)^2)` commands, each with at most eight private locations;
* `O_M((H + 1)^2)` schemas (at most nine per command, plus four);
* size parameter `S ≤ C_M (s + 1)^2 2^ℓ (ℓ + 1) (H + 1)^2`, from
  `S = O((s+1) 2^ℓ w + (s+1)^2 2^ℓ ℓ (r + 1))` (`sizeParameter_compile_le`).

The commands: every location has at most `movBound0 M` moves except the root cells
`cell 0 0 ν c`, which have `s` more (the tests `missGuard i`, one per register); there are
`(tapes + 1) · 2 (symbols + 3)` root cells and `s ≤ H + 2`. All constants depend on `M` only.

Correctness: if `M` halts on `x` within `2^H` steps, the system has a conflict iff `M`
accepts `x` (`verifier_accepts_iff`, `compile_accepts`, `conflictRound_compile_lt_top_iff`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563.MatrixCompiler

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

/-! ## Counting commands -/

/-- The root cells `cell 0 0 ν c`. -/
def rootLocs (M : Machine) (H : ℕ) : List (Loc M H) :=
  (List.finRange (M.tapes + 1) ×ˢ allCV M).map fun a => Loc.cell 0 0 a.1 a.2

lemma length_rootLocs : (rootLocs M H).length = (M.tapes + 1) * (2 * (M.symbols + 3)) := by
  simp [rootLocs, allCV, allBool, List.length_product]; ring

lemma mem_rootLocs_of_rootCount {L : Loc M H} (h : L.rootCount = 1) : L ∈ rootLocs M H := by
  cases L with
  | cell d θ ν c =>
    simp only [Loc.rootCount] at h
    split_ifs at h with hc
    have hd : d = 0 := Fin.ext hc.2
    have hθ : θ = 0 := Fin.ext hc.1
    rw [hd, hθ]
    exact List.mem_map.mpr ⟨(ν, c), List.mem_product.mpr ⟨List.mem_finRange _, mem_allCV c⟩, rfl⟩
  | _ => simp [Loc.rootCount] at h

lemma nodup_locsByCode : (locsByCode M H).Nodup := by
  refine (List.nodup_range).filterMap ?_
  intro a a' b ha ha'
  rw [← code_of_decodeLoc (Option.mem_def.mp ha), ← code_of_decodeLoc (Option.mem_def.mp ha')]

lemma sum_rootCount_eq (l : List (Loc M H)) :
    (l.map Loc.rootCount).sum = (l.filter fun L => decide (L.rootCount = 1)).length := by
  induction l with
  | nil => rfl
  | cons L l ih =>
    have := L.rootCount_le_one
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons]
    by_cases h : L.rootCount = 1
    · simp [h]; omega
    · have h0 : L.rootCount = 0 := by omega
      simp [h0]

lemma sum_rootCount_le {l : List (Loc M H)} (hl : l.Nodup) :
    (l.map Loc.rootCount).sum ≤ (M.tapes + 1) * (2 * (M.symbols + 3)) := by
  rw [sum_rootCount_eq, ← length_rootLocs (H := H)]
  refine ((hl.filter _).subperm fun L hL => ?_).length_le
  exact mem_rootLocs_of_rootCount (by simpa using (List.mem_filter.mp hL).2)

/-- The number of root cells. -/
def numRoot (M : Machine) : ℕ := (M.tapes + 1) * (2 * (M.symbols + 3))

/-- The commands: `movBound0 M` per location and `s` more per root cell. -/
lemma verifierCmds'_length_le :
    (verifierCmds' M x s ℓ H).length ≤ movBound0 M * numLoc M H + s * numRoot M := by
  have hlen : (verifierCmds' M x s ℓ H).length =
      ((locsByCode M H).map fun L => (moves M x s ℓ H L).length).sum := by
    simp [verifierCmds', progCmds, List.length_flatMap]
  rw [hlen]
  have h1 : ((locsByCode M H).map fun L => (moves M x s ℓ H L).length).sum ≤
      ((locsByCode M H).map fun L => movBound0 M + L.rootCount * s).sum :=
    List.sum_le_sum fun L _ => moves_length_le' x s ℓ L
  have h2 : ((locsByCode M H).map fun L => movBound0 M + L.rootCount * s).sum =
      movBound0 M * (locsByCode M H).length + ((locsByCode M H).map Loc.rootCount).sum * s := by
    rw [List.sum_map_add, List.sum_map_mul_right]
    simp [Nat.mul_comm]
  have h3 := sum_rootCount_le (M := M) (H := H) nodup_locsByCode
  have h4 : movBound0 M * (locsByCode M H).length ≤ movBound0 M * numLoc M H :=
    Nat.mul_le_mul_left _ length_locsByCode_le
  have h5 : ((locsByCode M H).map Loc.rootCount).sum * s ≤ s * numRoot M := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ h3
  omega

/-! ## The bounds -/

/-- `numLoc M H ≤ A_M (H + 1)^2`. -/
def locConst (M : Machine) : ℕ := 16 * cM M ^ 3 * (cM M + 1) ^ 2

lemma numLoc_le_sq : numLoc M H ≤ locConst M * (H + 1) ^ 2 := by
  rw [numLoc_eq, locConst]
  have : radix M H ≤ (cM M + 1) * (H + 1) := by unfold radix; nlinarith
  calc 16 * cM M ^ 3 * radix M H ^ 2 ≤ 16 * cM M ^ 3 * ((cM M + 1) * (H + 1)) ^ 2 := by gcongr
    _ = _ := by ring

/-- The constant of the command bound. -/
def cmdConst (M : Machine) : ℕ := movBound0 M * locConst M + 2 * numRoot M

lemma cmds_le_sq (hsH : s ≤ H + 2) :
    (verifierCmds' M x s ℓ H).length ≤ cmdConst M * (H + 1) ^ 2 := by
  have h := verifierCmds'_length_le (M := M) (x := x) (s := s) (ℓ := ℓ) (H := H)
  have h1 : movBound0 M * numLoc M H ≤ movBound0 M * (locConst M * (H + 1) ^ 2) :=
    Nat.mul_le_mul_left _ numLoc_le_sq
  have h2 : s * numRoot M ≤ 2 * numRoot M * (H + 1) ^ 2 := by
    have : s ≤ 2 * (H + 1) ^ 2 := by nlinarith
    calc s * numRoot M ≤ 2 * (H + 1) ^ 2 * numRoot M := Nat.mul_le_mul_right _ this
      _ = _ := by ring
  unfold cmdConst
  calc _ ≤ _ := h
    _ ≤ movBound0 M * (locConst M * (H + 1) ^ 2) + 2 * numRoot M * (H + 1) ^ 2 := by omega
    _ = _ := by ring

/-- Correctness of `Iv` for general parameters. -/
theorem Iv_conflict_iff (P : Params x s ℓ H) (hT : (runOn M x (2 ^ H)).answer.isSome) :
    (Iv M x s ℓ H).conflictRound < ⊤ ↔ Accepts M x := by
  have hmask : MasksBounded s ℓ (verifierCmds' M x s ℓ H) :=
    progCmds_masks P.hH fun src _ => moves_wf src
  refine (RegisterProgram.conflictRound_compile_lt_top_iff (APv M x s ℓ H)
    (Loc.query : Loc M H).code (fun _ _ => 0)).trans ?_
  rw [compile_accepts Loc.code_injective _ hmask, addr_zero]
  unfold verifierCmds'
  rw [verifier_accepts_iff P mem_locsByCode _ (by positivity)]
  rw [accepts_iff_answer hT]
  rfl

lemma packed_arith1 {N r A B E : ℕ} (hN : N ≤ A * E) (hr : r ≤ B * E) (hE : 1 ≤ E) :
    N + r * 8 + 4 ≤ 100 * (A + 9 * B + 4) * E := by nlinarith

lemma packed_arith2 {r B E A : ℕ} (hr : r ≤ B * E) (hE : 1 ≤ E) :
    9 * r + 4 ≤ 100 * (A + 9 * B + 4) * E := by nlinarith

/-- **Packed size of the time simulation system.** For a machine `M` there is a constant
`C` such that for every input `x` and parameters `s, ℓ, H` with `Params x s ℓ H`
(`H + 2 ≤ s ℓ`, `0 < ℓ ≤ H`, `|x| < 2^ℓ`) and `s ≤ H + 2`, the implicit parity system
`Iv M x s ℓ H` with `s + 1` blocks over `𝔽₂^ℓ` (the system emitted by the reduction
generator)
1. reaches a conflict iff `M` accepts `x`, provided `M` halts on `x` within `2^H` steps;
2. has at most `C (H + 1)^2` locations;
3. has at most `C (H + 1)^2` schemas;
4. has size parameter `S ≤ C (s + 1)^2 2^ℓ (ℓ + 1) (H + 1)^2`, i.e.
   `S = O(k w Q + k^2 Q ℓ e)` with `k = s + 1`, `Q = 2^ℓ`, `w, e = O((H+1)^2)`.
The constant `C` depends only on `M`. -/
theorem packed_bounds (M : Machine) : ∃ C : ℕ, ∀ (x : List Bool) (s ℓ H : ℕ),
    Params x s ℓ H → s ≤ H + 2 →
      ((runOn M x (2 ^ H)).answer.isSome → ((Iv M x s ℓ H).conflictRound < ⊤ ↔ Accepts M x)) ∧
      (Iv M x s ℓ H).numLocations ≤ C * (H + 1) ^ 2 ∧
      (Iv M x s ℓ H).schemas.length ≤ C * (H + 1) ^ 2 ∧
      matrixSize (Iv M x s ℓ H) ≤ C * (s + 1) ^ 2 * 2 ^ ℓ * (ℓ + 1) * (H + 1) ^ 2 := by
  refine ⟨100 * (locConst M + 9 * cmdConst M + 4), fun x s ℓ H P hsH => ?_⟩
  set A := locConst M
  set B := cmdConst M
  have hW := numLoc_le_sq (M := M) (H := H)
  have hr := cmds_le_sq (M := M) (x := x) (ℓ := ℓ) hsH
  set r := (verifierCmds' M x s ℓ H).length with hr_def
  set N := numLoc M H
  set E := (H + 1) ^ 2 with hE
  have hE1 : 1 ≤ E := Nat.one_le_pow _ _ (by omega)
  have hAE : A * E ≤ 100 * (A + 9 * B + 4) * E :=
    Nat.mul_le_mul_right _ (by omega)
  refine ⟨Iv_conflict_iff P, ?_, ?_, ?_⟩
  · rw [Iv_numLocations]
    exact packed_arith1 hW hr hE1
  · have hsch : (Iv M x s ℓ H).schemas.length ≤ 9 * (APv M x s ℓ H).commands.length + 4 :=
      RegisterProgram.compile_schemas_length _ _ _
    have hc : (APv M x s ℓ H).commands.length = r := by
      simp only [AP_commands]; exact List.length_map _
    rw [hc] at hsch
    exact hsch.trans (packed_arith2 hr hE1)
  · have hS := RegisterProgram.sizeParameter_compile_le (APv M x s ℓ H)
      (Loc.query : Loc M H).code (fun _ _ => 0) P.hℓ
    have hc : (APv M x s ℓ H).commands.length = r := by
      simp only [AP_commands]; exact List.length_map _
    have hn : (APv M x s ℓ H).numLocations = N := rfl
    rw [hc, hn] at hS
    change matrixSize (Iv M x s ℓ H) ≤ _ at hS
    refine hS.trans ?_
    set Q := 2 ^ ℓ
    set k := s + 1
    have hk : k ≤ k ^ 2 := by nlinarith
    have hl : 1 ≤ ℓ + 1 := by omega
    -- first term
    have t1 : k * Q * N ≤ A * (k ^ 2 * Q * (ℓ + 1) * E) := by
      calc k * Q * N ≤ k ^ 2 * Q * (A * E) := Nat.mul_le_mul (Nat.mul_le_mul_right _ hk) hW
        _ = A * (k ^ 2 * Q * 1 * E) := by ring
        _ ≤ A * (k ^ 2 * Q * (ℓ + 1) * E) := by gcongr
    have t2 : k ^ 2 * Q * ℓ * (r + 1) ≤ (B + 1) * (k ^ 2 * Q * (ℓ + 1) * E) := by
      have : r + 1 ≤ (B + 1) * E := by nlinarith
      calc k ^ 2 * Q * ℓ * (r + 1) ≤ k ^ 2 * Q * (ℓ + 1) * ((B + 1) * E) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) this
        _ = _ := by ring
    have : 100 * (k * Q * N + k ^ 2 * Q * ℓ * (r + 1)) ≤
        100 * (A + 9 * B + 4) * k ^ 2 * Q * (ℓ + 1) * E := by
      have e : 100 * (A + 9 * B + 4) * k ^ 2 * Q * (ℓ + 1) * E =
          100 * ((A + 9 * B + 4) * (k ^ 2 * Q * (ℓ + 1) * E)) := by ring
      rw [e]
      apply Nat.mul_le_mul_left
      have : (A + 9 * B + 4) * (k ^ 2 * Q * (ℓ + 1) * E) ≥
          A * (k ^ 2 * Q * (ℓ + 1) * E) + (B + 1) * (k ^ 2 * Q * (ℓ + 1) * E) := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    exact this

/-! ## The parameters of the packed representation

For a horizon exponent `h` and `s` data blocks, the width
`ℓ = max(⌈log₂(n + 2)⌉, ⌈(h + 2)/s⌉)` (`pkWidth`, as `packedWidth` of the concept
`PackedRepresentation`) and the horizon `H = max(h, ℓ) ≤ h + 1` satisfy `Params`, so the
bounds hold in terms of `h`. -/

/-- The block width `max(⌈log₂(n + 2)⌉, ⌈(h + 2)/s⌉)`. -/
def pkWidth (n h s : ℕ) : ℕ := max (Nat.clog 2 (n + 2)) ((h + 1 + s) / s)

/-- The simulated horizon `max(h, ℓ)`. -/
def pkHorizon (n h s : ℕ) : ℕ := max h (pkWidth n h s)

lemma pk_params {x : List Bool} {h s : ℕ} (hx : 2 ≤ x.length) (hh : 2 ≤ h)
    (hxh : x.length ≤ 2 ^ h) (hs : 2 ≤ s) :
    Params x s (pkWidth x.length h s) (pkHorizon x.length h s) ∧
      pkHorizon x.length h s ≤ h + 1 := by
  set n := x.length
  set ℓ := pkWidth n h s
  have hc2 : 2 ≤ Nat.clog 2 (n + 2) :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num; omega)
  have hcx : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) := Nat.le_pow_clog (by norm_num) _
  have hch : Nat.clog 2 (n + 2) ≤ h + 1 := by
    apply Nat.clog_le_of_le_pow
    have : 2 ≤ 2 ^ h := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]; omega
  have hq : (h + 1 + s) / s ≤ h + 1 := by
    apply Nat.div_le_of_le_mul; nlinarith
  have hsq : h + 2 ≤ s * ((h + 1 + s) / s) := by
    have := Nat.div_add_mod (h + 1 + s) s
    have := Nat.mod_lt (h + 1 + s) (show 0 < s by omega)
    omega
  have hℓ2 : 2 ≤ ℓ := le_trans hc2 (le_max_left _ _)
  have hℓh : ℓ ≤ h + 1 := max_le hch hq
  have hsl : s * ((h + 1 + s) / s) ≤ s * ℓ := Nat.mul_le_mul_left _ (le_max_right _ _)
  have hsl2 : 2 * ℓ ≤ s * ℓ := Nat.mul_le_mul_right _ hs
  have hxℓ : n < 2 ^ ℓ := lt_of_lt_of_le (by omega)
    (le_trans hcx (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)))
  refine ⟨⟨?_, by omega, le_max_right _ _, hxℓ⟩, max_le (by omega) hℓh⟩
  show max h ℓ + 2 ≤ s * ℓ
  rcases le_total h ℓ with hl | hl
  · rw [max_eq_right hl]; omega
  · rw [max_eq_left hl]; omega

/-- **The packed representation, size and correctness clauses.** For a machine `M` there is a
constant `C` such that for all inputs `x` with `2 ≤ |x| ≤ 2^h`, `2 ≤ h` and `2 ≤ s ≤ h + 2`,
the system `Iv M x s ℓ H` with `ℓ = pkWidth |x| h s` and `H = pkHorizon |x| h s` reaches a
conflict iff `M` accepts `x` (if `M` halts on `x` within `2^h` steps), and has at most
`C (h + 1)^2` locations and schemas and size parameter at most
`C (s + 1)^2 2^ℓ (ℓ + 1) (h + 1)^2`. -/
theorem packed_bounds_h (M : Machine) : ∃ C : ℕ, ∀ (x : List Bool) (h s : ℕ),
    2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s → s ≤ h + 2 →
      ((runOn M x (2 ^ h)).answer.isSome →
        ((Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s)).conflictRound < ⊤ ↔
          Accepts M x)) ∧
      (Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s)).numLocations ≤
        C * (h + 1) ^ 2 ∧
      (Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s)).schemas.length ≤
        C * (h + 1) ^ 2 ∧
      matrixSize (Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s)) ≤
        C * (s + 1) ^ 2 * 2 ^ pkWidth x.length h s * (pkWidth x.length h s + 1) *
          (h + 1) ^ 2 := by
  obtain ⟨C, hC⟩ := packed_bounds M
  refine ⟨4 * C, fun x h s hx hh hxh hs hsh => ?_⟩
  obtain ⟨P, hH⟩ := pk_params hx hh hxh hs
  set ℓ := pkWidth x.length h s
  set H := pkHorizon x.length h s
  have hhH : h ≤ H := le_max_left _ _
  obtain ⟨c1, c2, c3, c4⟩ := hC x s ℓ H P (by omega)
  have hsq : (H + 1) ^ 2 ≤ 4 * (h + 1) ^ 2 := by
    have : H + 1 ≤ 2 * (h + 1) := by omega
    calc (H + 1) ^ 2 ≤ (2 * (h + 1)) ^ 2 := Nat.pow_le_pow_left this 2
      _ = _ := by ring
  refine ⟨fun hT => c1 ?_, ?_, ?_, ?_⟩
  · have := runOn_halted x hT (2 ^ H - 2 ^ h)
    rw [Nat.add_sub_cancel' (Nat.pow_le_pow_right (by norm_num) hhH)] at this
    rw [this]; exact hT
  · calc _ ≤ C * (H + 1) ^ 2 := c2
      _ ≤ C * (4 * (h + 1) ^ 2) := Nat.mul_le_mul_left _ hsq
      _ = _ := by ring
  · calc _ ≤ C * (H + 1) ^ 2 := c3
      _ ≤ C * (4 * (h + 1) ^ 2) := Nat.mul_le_mul_left _ hsq
      _ = _ := by ring
  · calc _ ≤ C * (s + 1) ^ 2 * 2 ^ ℓ * (ℓ + 1) * (H + 1) ^ 2 := c4
      _ ≤ C * (s + 1) ^ 2 * 2 ^ ℓ * (ℓ + 1) * (4 * (h + 1) ^ 2) := Nat.mul_le_mul_left _ hsq
      _ = _ := by ring

end Lax119563Proofs.Reduction
