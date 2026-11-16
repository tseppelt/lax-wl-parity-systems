import Lax119563Proofs.Reduction.OutNum

/-!
# Check rows and previous steps, numerically

* `entB s j i v`: whether row `j` (of `s + ℓ` rows) of the check matrix is nonzero at block
  `i`, register value `v` (`ent_ne_zero_iff`, for `σ % (s + ℓ) = j`);
* `prevStep_eq_count`: the previous step is determined by the number of steps `σ' < σ` such
  that some step in `[σ', σ)` has a nonzero entry.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563Proofs.Matrix

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ}

/-- Row `j` of the check matrix is nonzero at block `i` with register value `v`. -/
def entB (s j i v : ℕ) : Bool :=
  if j < s then decide (i = j ∨ i = s) else v.testBit (j - s)

lemma zmod2_ne_zero_iff (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by
  rcases zmod2_eq_zero_or_one a with h | h <;> simp [h]

lemma testBit_regVal (b : BlockCoord ℓ) (t : Fin ℓ) :
    (Circuits.regVal b).testBit t.val = decide (b t = 1) := by
  rw [Circuits.regVal, Circuits.testBit_ofBits]
  simp [t.isLt]

lemma ent_ne_zero_iff (h : 0 < s + ℓ) (σ : ℕ) (c : Coord (s + 1) ℓ) :
    ent σ c ≠ 0 ↔ entB s (σ % (s + ℓ)) c.1.val (Circuits.regVal c.2) = true := by
  rw [ent_eq h, entB]
  by_cases hj : σ % (s + ℓ) < s
  · rw [dif_pos hj, if_pos hj]
    by_cases hc : c.1.val = σ % (s + ℓ) ∨ c.1.val = s <;> simp [hc]
  · rw [dif_neg hj, if_neg hj, zmod2_ne_zero_iff]
    have hlt : σ % (s + ℓ) - s < ℓ := by have := Nat.mod_lt σ h; omega
    have := testBit_regVal c.2 ⟨σ % (s + ℓ) - s, hlt⟩
    simp only at this
    rw [this]
    simp

/-- The number of steps `σ' < σ` followed by a nonzero entry before `σ`. -/
def prevCnt (f : ℕ → Bool) (σ : ℕ) : ℕ :=
  ((List.range σ).filter fun σ' => (List.range σ).any fun σ'' => decide (σ' ≤ σ'') && f σ'').length

lemma prevCnt_succ (f : ℕ → Bool) (σ : ℕ) :
    prevCnt f (σ + 1) = if f σ then σ + 1 else prevCnt f σ := by
  unfold prevCnt
  by_cases hf : f σ
  · rw [if_pos hf, List.filter_eq_self.mpr, List.length_range]
    intro σ' hσ'
    rw [List.mem_range] at hσ'
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨σ, by omega, by omega, hf⟩
  · rw [if_neg hf, List.range_succ, List.filter_append, List.length_append]
    have h1 : ∀ σ' ∈ List.range σ, ((List.range σ ++ [σ]).any fun σ'' =>
        decide (σ' ≤ σ'') && f σ'') = ((List.range σ).any fun σ'' => decide (σ' ≤ σ'') && f σ'') := by
      intro σ' _
      simp [List.any_append, hf]
    rw [List.filter_congr h1]
    have h2 : ([σ].filter fun σ' => (List.range σ ++ [σ]).any fun σ'' =>
        decide (σ' ≤ σ'') && f σ'') = [] := by
      simp only [List.filter_cons, List.filter_nil, List.any_append, List.any_cons,
        List.any_nil, le_refl, decide_true, Bool.true_and, hf, Bool.or_false]
      rw [if_neg]
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, not_exists,
        not_and]
      intro σ'' h h'
      omega
    rw [h2]
    rfl

/-- **The previous step by counting.** -/
lemma prevStep_eq_count (c : Coord (s + 1) ℓ) (σ : ℕ) :
    prevStep c σ = if prevCnt (fun σ' => decide (ent σ' c ≠ 0)) σ = 0 then none
      else some (prevCnt (fun σ' => decide (ent σ' c ≠ 0)) σ - 1) := by
  induction σ with
  | zero => simp [prevStep, prevCnt]
  | succ σ ih =>
    rw [prevCnt_succ, prevStep]
    by_cases h : ent σ c ≠ 0
    · simp [h]
    · simp only [h, decide_false, if_false, Bool.false_eq_true]
      exact ih

end Lax119563Proofs.Reduction
