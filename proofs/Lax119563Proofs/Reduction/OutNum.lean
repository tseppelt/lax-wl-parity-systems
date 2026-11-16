import Lax119563Proofs.Reduction.OutDecode

/-!
# Decoding output numbers

A number `slotNum F i v t = t + 4 ((i + (s+1) F) 2^ℓ + v)` (`i ≤ s`, `v < 2^ℓ`, `t < 4`)
determines `F, i, v, t` (`slotNum_inj`). Every name has the number
`slotNum (famNum X) i (regVal b) (labNum l)` for its class `X` with coordinate `(i, b)`.
Classes with `σ < numSteps` (`ClsBnd`) are determined by their family and coordinate
(`famNum_injective'`), so (`outValid_slotNum`) the number of the slot of a bounded class `X`
with coordinate `(i, b)` is valid iff the name `(X, l)` is valid, and slot numbers whose
coordinate is not that of the class of the family are invalid (`not_outValid_slotNum`).
-/

open Lax119563.ImplicitParitySystems Lax119563Proofs.Matrix

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ} (I : ImplicitParitySystem (s + 1) ℓ)

/-- The number of the slot with family `F`, block `i`, register value `v`, label number `t`. -/
def slotNum (s ℓ F i v t : ℕ) : ℕ := t + 4 * ((i + (s + 1) * F) * 2 ^ ℓ + v)

lemma num_eq_slotNum (a : VName I) :
    num I a = slotNum s ℓ (famNum I a.1) (coordOf I a.1).1.val
      (Circuits.regVal (coordOf I a.1).2) (labNum a.2) := rfl

lemma slotNum_inj {F i v t F' i' v' t' : ℕ} (hi : i < s + 1) (hi' : i' < s + 1)
    (hv : v < 2 ^ ℓ) (hv' : v' < 2 ^ ℓ) (ht : t < 4) (ht' : t' < 4)
    (h : slotNum s ℓ F i v t = slotNum s ℓ F' i' v' t') :
    F = F' ∧ i = i' ∧ v = v' ∧ t = t' := by
  unfold slotNum at h
  have h1 := congrArg (· / 4) h
  have h2 := congrArg (· % 4) h
  simp only [Nat.add_comm t, Nat.add_comm t', Nat.mul_add_div (show 0 < 4 by omega),
    Nat.div_eq_of_lt ht, Nat.div_eq_of_lt ht', Nat.mul_add_mod, Nat.mod_eq_of_lt ht,
    Nat.mod_eq_of_lt ht', add_zero] at h1 h2
  have hp : 0 < 2 ^ ℓ := by positivity
  have h3 := congrArg (· / 2 ^ ℓ) h1
  have h4 := congrArg (· % 2 ^ ℓ) h1
  simp only [Nat.mul_comm _ (2 ^ ℓ), Nat.mul_add_div hp, Nat.div_eq_of_lt hv,
    Nat.div_eq_of_lt hv', Nat.mul_add_mod, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hv',
    add_zero] at h3 h4
  have h5 := congrArg (· / (s + 1)) h3
  have h6 := congrArg (· % (s + 1)) h3
  simp only [Nat.add_comm _ ((s + 1) * _), Nat.mul_add_div (show 0 < s + 1 by omega),
    Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hi', Nat.mul_add_mod, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt hi', add_zero] at h5 h6
  exact ⟨h5, h6, h4, h2⟩

/-- Classes with an in-range step. -/
def ClsBnd : ICls I → Prop
  | .upd _ σ _ => σ < numSteps (s + 1) ℓ
  | .track _ σ _ => σ < numSteps (s + 1) ℓ
  | .coef _ σ => σ < numSteps (s + 1) ℓ
  | _ => True

lemma ClsValid.bnd {X : ICls I} (h : ClsValid I X) : ClsBnd I X := by
  cases X <;> first | exact h.1 | trivial

lemma innerOf_lt' {X : ICls I} (hX : ClsBnd I X) :
    innerOf I X <
      kindSize I.schemas.length (numSteps (s + 1) ℓ) I.numLocations (kindOf I X) := by
  have hNS : ∀ (e : Fin I.schemas.length) (σ : ℕ), σ < numSteps (s + 1) ℓ →
      e.val * numSteps (s + 1) ℓ + σ < I.schemas.length * numSteps (s + 1) ℓ := by
    intro e σ hσ
    have := e.isLt
    calc e.val * numSteps (s + 1) ℓ + σ < (e.val + 1) * numSteps (s + 1) ℓ := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ this
  cases X with
  | upd e σ c => exact hNS e σ hX
  | track e σ c => exact hNS e σ hX
  | coef e σ => exact hNS e σ hX
  | junc e c => exact e.isLt
  | link e c => exact e.isLt
  | sum e c => exact e.isLt
  | coord v c => exact v.isLt

lemma famNum_injective' {X Y : ICls I} (hX : ClsBnd I X) (hY : ClsBnd I Y)
    (h : famNum I X = famNum I Y) (hc : coordOf I X = coordOf I Y) : X = Y := by
  rw [famNum_eq, famNum_eq] at h
  obtain ⟨hk, hi⟩ := kindOff_inj _ _ (innerOf_lt' I hX) (innerOf_lt' I hY) h
  have hdiv : ∀ (e e' : Fin I.schemas.length) (σ σ' : ℕ), σ < numSteps (s + 1) ℓ →
      σ' < numSteps (s + 1) ℓ → e.val * numSteps (s + 1) ℓ + σ =
        e'.val * numSteps (s + 1) ℓ + σ' → e = e' ∧ σ = σ' := by
    intro e e' σ σ' hσ hσ' heq
    have hpos : 0 < numSteps (s + 1) ℓ := by omega
    have h1 := congrArg (· / numSteps (s + 1) ℓ) heq
    have h2 := congrArg (· % numSteps (s + 1) ℓ) heq
    simp only [Nat.mul_comm _ (numSteps (s + 1) ℓ), Nat.mul_add_div hpos,
      Nat.div_eq_of_lt hσ, Nat.div_eq_of_lt hσ', Nat.mul_add_mod, Nat.mod_eq_of_lt hσ,
      Nat.mod_eq_of_lt hσ'] at h1 h2
    exact ⟨Fin.ext (by simpa using h1), h2⟩
  cases X <;> cases Y <;> simp only [kindOf, innerOf, coordOf, Fin.reduceEq] at hk hi hc <;>
    (try cases hk) <;> (try subst hc)
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := hdiv _ _ _ _ hX hY hi; rfl)
    | (rw [Fin.ext hi])

/-- **Validity of slot numbers.** -/
lemma outValid_slotNum_iff {F i v t : ℕ} (hi : i < s + 1) (hv : v < 2 ^ ℓ) (ht : t < 4) :
    OutValid I (slotNum s ℓ F i v t) ↔ ∃ a : VName I, Valid I a ∧ famNum I a.1 = F ∧
      (coordOf I a.1).1.val = i ∧ Circuits.regVal (coordOf I a.1).2 = v ∧ labNum a.2 = t := by
  constructor
  · rintro ⟨a, ha, hn⟩
    rw [num_eq_slotNum] at hn
    obtain ⟨h1, h2, h3, h4⟩ := slotNum_inj (coordOf I a.1).1.isLt hi (regVal_lt _) hv
      (labNum_lt _) ht hn
    exact ⟨a, ha, h1, h2, h3, h4⟩
  · rintro ⟨a, ha, h1, h2, h3, h4⟩
    exact ⟨a, ha, by rw [num_eq_slotNum, h1, h2, h3, h4]⟩

/-- The slot of a bounded class `X` with coordinate `(i, b)` is valid iff the name is. -/
lemma outValid_slotNum {X : ICls I} (hX : ClsBnd I X) {i : Fin (s + 1)} {b : BlockCoord ℓ}
    (hc : coordOf I X = (i, b)) (l : Lab) :
    OutValid I (slotNum s ℓ (famNum I X) i.val (Circuits.regVal b) (labNum l)) ↔
      Valid I (X, l) := by
  rw [outValid_slotNum_iff I i.isLt (regVal_lt b) (labNum_lt l)]
  constructor
  · rintro ⟨a, ha, h1, h2, h3, h4⟩
    have hc' : coordOf I a.1 = coordOf I X := by
      rw [hc]; exact Prod.ext (Fin.ext h2) (regVal_injective h3)
    have := famNum_injective' I (ClsValid.bnd I ha.1) hX h1 hc'
    have hl := labNum_injective h4
    obtain ⟨Y, m⟩ := a
    simp only at this hl
    subst this hl
    exact ha
  · intro h
    exact ⟨(X, l), h, rfl, by rw [hc], by rw [hc], rfl⟩

/-- A slot whose coordinate is not that of the bounded class `X` of its family is invalid. -/
lemma not_outValid_slotNum {X : ICls I} (hX : ClsBnd I X) {i : Fin (s + 1)}
    {b : BlockCoord ℓ} (hc : coordOf I X ≠ (i, b)) (t : ℕ) (ht : t < 4)
    (hF : ∀ Y : ICls I, ClsBnd I Y → famNum I Y = famNum I X → Y = X) :
    ¬ OutValid I (slotNum s ℓ (famNum I X) i.val (Circuits.regVal b) t) := by
  rw [outValid_slotNum_iff I i.isLt (regVal_lt b) ht]
  rintro ⟨a, ha, h1, h2, h3, -⟩
  have := hF a.1 (ClsValid.bnd I ha.1) h1
  apply hc
  rw [← this]
  exact Prod.ext (Fin.ext h2) (regVal_injective h3)

open Classical in
/-- The color of a slot. -/
lemma outColor_slotNum {F i v t : ℕ} (ht : t < 4) :
    outColor I (slotNum s ℓ F i v t) =
      if OutValid I (slotNum s ℓ F i v t) then 2 * ((i + (s + 1) * F) * 2 ^ ℓ + v) + 2 else 1 := by
  unfold outColor slotNum
  congr 3
  omega

end Lax119563Proofs.Reduction
