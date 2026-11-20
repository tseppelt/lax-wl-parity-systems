import Lax119563Proofs.Circuits.AddrProgram

/-!
# Programs given by local moves

An address program is described by a list of *moves* at each location: replacing a bit field
with known current value (`step`), forking under a field test (`fork`), or moving under an
arbitrary register guard (`test`). Soundness and completeness of such a program with respect
to a semantic predicate `Sem` on configurations reduce to local conditions on the moves:
every move is sound for `Sem`, and every configuration satisfying `Sem` has a move that fires
into configurations satisfying `Sem` of smaller rank.
-/

namespace Lax119563Proofs.Circuits

variable {L : Type} {s : ℕ}

/-- A move at a location. -/
inductive Move (L : Type) (s : ℕ)
  /-- If `field A k m = q`, replace that field by `v` and go to `dst`. -/
  | step (k m q v : ℕ) (dst : L)
  /-- If `field A k m = q`, fork into `left` and `right`. -/
  | fork (k m q : ℕ) (left right : L)
  /-- If the register guard `g` holds, go to `dst`. -/
  | test (g : Fin s → ℕ → Bool) (dst : L)

/-- An unconditional jump. -/
def Move.goto (dst : L) : Move L s := .step 0 0 0 0 dst

/-- An unconditional fork. -/
def Move.fork' (left right : L) : Move L s := .fork 0 0 0 left right

/-- The address command of a move at `src`. -/
def Move.toACmd (ℓ : ℕ) (src : L) : Move L s → ACmd L s
  | .step k m q v dst => .assign src (fieldGuard ℓ k m q) (fieldMask k q v) dst
  | .fork k m q l r => .fork src (fieldGuard ℓ k m q) l r
  | .test g dst => .assign src g 0 dst

/-- The commands of all moves at the locations `locs`. -/
def progCmds (ℓ : ℕ) (locs : List L) (moves : L → List (Move L s)) : List (ACmd L s) :=
  locs.flatMap fun src => (moves src).map (Move.toACmd ℓ src)

/-- The fields of a move lie inside the low `B` bits of the address and its constants fit
into them. -/
def Move.WF (B : ℕ) : Move L s → Prop
  | .step k m q v _ => k + m ≤ B ∧ q < 2 ^ m ∧ v < 2 ^ m
  | .fork k m q _ _ => k + m ≤ B ∧ q < 2 ^ m
  | .test _ _ => True

/-- A move at `src` is sound for `Sem` on the addresses below `2 ^ B`. -/
def Move.Sound (ℓ B : ℕ) (Sem : L → ℕ → Prop) (src : L) : Move L s → Prop
  | .step k m q v dst => ∀ A, A < 2 ^ B → field A k m = q →
      Sem dst (setBits A k m v) → Sem src A
  | .fork k m q l r => ∀ A, A < 2 ^ B → field A k m = q → Sem l A → Sem r A → Sem src A
  | .test g dst => ∀ A, A < 2 ^ B → Enabled ℓ g A → Sem dst A → Sem src A

/-- A move at `src` fires at address `A` into configurations satisfying `Sem` of smaller rank. -/
def Move.Fires (ℓ : ℕ) (Sem : L → ℕ → Prop) (rank : L → ℕ → ℕ) (src : L) (A : ℕ) :
    Move L s → Prop
  | .step k m q v dst => field A k m = q ∧ Sem dst (setBits A k m v) ∧
      rank dst (setBits A k m v) < rank src A
  | .fork k m q l r => field A k m = q ∧ Sem l A ∧ Sem r A ∧ rank l A < rank src A ∧
      rank r A < rank src A
  | .test g dst => Enabled ℓ g A ∧ Sem dst A ∧ rank dst A < rank src A

lemma field_zero_width (A k : ℕ) : field A k 0 = 0 := by simp [field, Nat.mod_one]

lemma setBits_zero_width (A k : ℕ) : setBits A k 0 0 = A := by
  simp [setBits, field_zero_width]

lemma progCmds_masks {ℓ B : ℕ} (hB : B ≤ s * ℓ) {locs : List L} {moves : L → List (Move L s)}
    (hwf : ∀ src ∈ locs, ∀ mv ∈ moves src, mv.WF B) :
    MasksBounded s ℓ (progCmds ℓ locs moves) := by
  intro p g m q hc
  simp only [progCmds, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨src, hsrc, mv, hmv, heq⟩ := hc
  have hw := hwf src hsrc mv hmv
  cases mv with
  | step k m' q' v dst =>
    simp only [Move.toACmd, ACmd.assign.injEq] at heq
    obtain ⟨-, -, rfl, -⟩ := heq
    exact fieldMask_lt hw.2.1 hw.2.2 (hw.1.trans hB)
  | fork => simp [Move.toACmd] at heq
  | test g' dst =>
    simp only [Move.toACmd, ACmd.assign.injEq] at heq
    obtain ⟨-, -, rfl, -⟩ := heq
    positivity

section

variable {ℓ : ℕ} {locs : List L} {moves : L → List (Move L s)} {Sem : L → ℕ → Prop}
  {acc rej : L} {B : ℕ}

/-- Soundness from local soundness. -/
theorem progCmds_sound (hℓ : 0 < ℓ) (hB : B ≤ s * ℓ)
    (hwf : ∀ src ∈ locs, ∀ mv ∈ moves src, mv.WF B)
    (hs : ∀ src ∈ locs, ∀ mv ∈ moves src, mv.Sound ℓ B Sem src)
    (hacc : ∀ A, Sem acc A) {p : L} {A : ℕ}
    (h : AAccepts ℓ (progCmds ℓ locs moves) acc rej p A) (hA : A < 2 ^ B) :
    Sem p A := by
  induction h with
  | accept A => exact hacc A
  | @assign p g m q A hc _ _ hg _ ih =>
    simp only [progCmds, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨src, hsrc, mv, hmv, heq⟩ := hc
    have hw := hwf src hsrc mv hmv
    have hso := hs src hsrc mv hmv
    cases mv with
    | step k m' q' v dst =>
      simp only [Move.toACmd, ACmd.assign.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      have hf : field A k m' = q' := (enabled_fieldGuard hℓ (hw.1.trans hB) hw.2.1).mp hg
      rw [xor_fieldMask hf] at ih
      exact hso A hA hf (ih (setBits_lt hw.2.2 hA hw.1))
    | fork => simp [Move.toACmd] at heq
    | test g' dst =>
      simp only [Move.toACmd, ACmd.assign.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      rw [Nat.xor_zero] at ih
      exact hso A hA hg (ih hA)
  | @fork p g q r A hc _ _ hg _ _ ih₁ ih₂ =>
    simp only [progCmds, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨src, hsrc, mv, hmv, heq⟩ := hc
    have hw := hwf src hsrc mv hmv
    have hso := hs src hsrc mv hmv
    cases mv with
    | step => simp [Move.toACmd] at heq
    | fork k m' q' l r' =>
      simp only [Move.toACmd, ACmd.fork.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      exact hso A hA ((enabled_fieldGuard hℓ (hw.1.trans hB) hw.2).mp hg) (ih₁ hA) (ih₂ hA)
    | test => simp [Move.toACmd] at heq

/-- Completeness from local progress. -/
theorem progCmds_complete (hℓ : 0 < ℓ) (hB : B ≤ s * ℓ) (rank : L → ℕ → ℕ)
    (hmem : ∀ src, src ∈ locs)
    (hwf : ∀ src ∈ locs, ∀ mv ∈ moves src, mv.WF B)
    (hrej : ∀ A, ¬ Sem rej A)
    (hc : ∀ src A, A < 2 ^ B → Sem src A → src = acc ∨
      ∃ mv ∈ moves src, mv.Fires ℓ Sem rank src A) :
    ∀ src A, A < 2 ^ B → Sem src A → AAccepts ℓ (progCmds ℓ locs moves) acc rej src A := by
  suffices ∀ n, ∀ src A, rank src A = n → A < 2 ^ B → Sem src A →
      AAccepts ℓ (progCmds ℓ locs moves) acc rej src A from
    fun src A => this _ src A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro src A hn hA hS
  rcases hc src A hA hS with rfl | ⟨mv, hmv, hf⟩
  · exact AAccepts.accept A
  by_cases hacc : src = acc
  · subst hacc; exact AAccepts.accept A
  have hrj : src ≠ rej := by rintro rfl; exact hrej A hS
  have hw := hwf src (hmem src) mv hmv
  have hcmd : Move.toACmd ℓ src mv ∈ progCmds ℓ locs moves :=
    List.mem_flatMap.mpr ⟨src, hmem src, List.mem_map.mpr ⟨mv, hmv, rfl⟩⟩
  cases mv with
  | step k m q v dst =>
    obtain ⟨hfq, hS', hr⟩ := hf
    refine AAccepts.assign hcmd hacc hrj ((enabled_fieldGuard hℓ (hw.1.trans hB) hw.2.1).mpr hfq) ?_
    rw [xor_fieldMask hfq]
    exact ih _ (hn ▸ hr) dst _ rfl (setBits_lt hw.2.2 hA hw.1) hS'
  | fork k m q l r =>
    obtain ⟨hfq, hl, hr, hrl, hrr⟩ := hf
    exact AAccepts.fork hcmd hacc hrj ((enabled_fieldGuard hℓ (hw.1.trans hB) hw.2).mpr hfq)
      (ih _ (hn ▸ hrl) l A rfl hA hl) (ih _ (hn ▸ hrr) r A rfl hA hr)
  | test g dst =>
    obtain ⟨hg, hS', hr⟩ := hf
    refine AAccepts.assign hcmd hacc hrj hg ?_
    rw [Nat.xor_zero]
    exact ih _ (hn ▸ hr) dst A rfl hA hS'

end

end Lax119563Proofs.Circuits
