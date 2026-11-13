import Lax119563Proofs.Matrix.VertexList
import Lax119563Proofs.Reduction.Transfer
import Lax119563Proofs.Game.Characterization
import Lax119563Proofs.Circuits.AddrProgram

/-!
# The output graphs

For an implicit parity system `I` with `k = s + 1` blocks, the machine outputs renumbered
copies of the matrix graphs with padding. Classes are grouped into *families* (`famNum`):
hubs first (`upd`, `junc`, `link`), then `coord`, `sum`, `track`, `coef`. The class number of
a class with coordinate `(i, b)` in family `F` is `(i + (s + 1) F) 2^ℓ + regVal b`
(`coef` classes use the coordinate `(0, 0)`), and a vertex name `(X, l)` gets the number
`labNum l + 4 · classNum X`. The output graph `outGraph I ε` has the vertices `0, …, nOut - 1`;
the numbers of valid names are adjacent as the names are in `G_ε`; all other numbers are
isolated padding vertices of color `1`, and a valid number `z` has color `2 (z / 4) + 2`.

`distinguishes_outGraph_iff`: the output graphs are distinguished by `(s+1)`-WL iff the
matrix graphs are.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.PebbleGame
open Lax119563.ImplicitParitySystems Lax119563Proofs.Matrix

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ} (I : ImplicitParitySystem (s + 1) ℓ)

/-! ## Numbering -/

/-- The number of families. -/
def famCount : ℕ :=
  3 * (I.schemas.length * numSteps (s + 1) ℓ) + 3 * I.schemas.length + I.numLocations

/-- The family of a class. -/
def famNum : ICls I → ℕ
  | .upd e σ _ => e.val * numSteps (s + 1) ℓ + σ
  | .junc e _ => I.schemas.length * numSteps (s + 1) ℓ + e.val
  | .link e _ => I.schemas.length * numSteps (s + 1) ℓ + I.schemas.length + e.val
  | .coord v _ => I.schemas.length * numSteps (s + 1) ℓ + 2 * I.schemas.length + v.val
  | .sum e _ => I.schemas.length * numSteps (s + 1) ℓ + 2 * I.schemas.length +
      I.numLocations + e.val
  | .track e σ _ => I.schemas.length * numSteps (s + 1) ℓ + 3 * I.schemas.length +
      I.numLocations + (e.val * numSteps (s + 1) ℓ + σ)
  | .coef e σ => 2 * (I.schemas.length * numSteps (s + 1) ℓ) + 3 * I.schemas.length +
      I.numLocations + (e.val * numSteps (s + 1) ℓ + σ)

/-- The coordinate of a class (`(0, 0)` for coefficient classes). -/
def coordOf : ICls I → Coord (s + 1) ℓ
  | .coord _ c => c
  | .sum _ c => c
  | .junc _ c => c
  | .link _ c => c
  | .track _ _ c => c
  | .upd _ _ c => c
  | .coef _ _ => (0, 0)

/-- The number of a class. -/
def classNum (X : ICls I) : ℕ :=
  ((coordOf I X).1.val + (s + 1) * famNum I X) * 2 ^ ℓ + Circuits.regVal (coordOf I X).2

/-- The number of a label. -/
def labNum (l : Lab) : ℕ := l.1.val + 2 * l.2.val

/-- The number of a vertex name. -/
def num (a : VName I) : ℕ := labNum a.2 + 4 * classNum I a.1

/-- The number of vertices of the output graphs. -/
def nOut : ℕ := 4 * (2 ^ ℓ * ((s + 1) * famCount I))

/-! ### Injectivity -/

lemma regVal_lt (b : BlockCoord ℓ) : Circuits.regVal b < 2 ^ ℓ := by
  unfold Circuits.regVal
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Circuits.testBit_ofBits]
  simp; omega

lemma regVal_injective : Function.Injective (Circuits.regVal (ℓ := ℓ)) := by
  intro b b' h
  funext t
  have := congrArg (fun n => n.testBit t) h
  simp only [Circuits.regVal, Circuits.testBit_ofBits, t.isLt, decide_true, Bool.true_and,
    dif_pos] at this
  have h1 := zmod2_eq_zero_or_one (b t)
  have h2 := zmod2_eq_zero_or_one (b' t)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all

lemma labNum_lt (l : Lab) : labNum l < 4 := by
  unfold labNum
  have := l.1.isLt; have := l.2.isLt
  change l.1.val < 2 at *; change l.2.val < 2 at *
  omega

lemma labNum_injective : Function.Injective labNum := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  unfold labNum at h
  have ha := a.isLt; have hb := b.isLt; have ha' := a'.isLt; have hb' := b'.isLt
  change a.val < 2 at ha; change b.val < 2 at hb
  change a'.val < 2 at ha'; change b'.val < 2 at hb'
  simp only at h
  have e1 : a.val = a'.val := by omega
  have e2 : b.val = b'.val := by omega
  exact Prod.ext (Fin.ext e1) (Fin.ext e2)

lemma famNum_lt {X : ICls I} (hX : ClsValid I X) : famNum I X < famCount I := by
  have hNS : ∀ (e : Fin I.schemas.length) (σ : ℕ), σ < numSteps (s + 1) ℓ →
      e.val * numSteps (s + 1) ℓ + σ < I.schemas.length * numSteps (s + 1) ℓ := by
    intro e σ hσ
    have := e.isLt
    calc e.val * numSteps (s + 1) ℓ + σ < (e.val + 1) * numSteps (s + 1) ℓ := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ this
  unfold famCount
  cases X with
  | upd e σ c => have := hNS e σ hX.1; simp only [famNum]; omega
  | junc e c => have := e.isLt; simp only [famNum]; omega
  | link e c => have := e.isLt; simp only [famNum]; omega
  | coord v c => have := v.isLt; simp only [famNum]; omega
  | sum e c => have := e.isLt; simp only [famNum]; omega
  | track e σ c => have := hNS e σ hX.1; simp only [famNum]; omega
  | coef e σ => have := hNS e σ hX.1; simp only [famNum]; omega

/-- The kind of a class (the block of families it belongs to). -/
def kindOf : ICls I → Fin 7
  | .upd .. => 0
  | .junc .. => 1
  | .link .. => 2
  | .coord .. => 3
  | .sum .. => 4
  | .track .. => 5
  | .coef .. => 6

/-- The index of a class within its kind. -/
def innerOf : ICls I → ℕ
  | .upd e σ _ => e.val * numSteps (s + 1) ℓ + σ
  | .junc e _ => e.val
  | .link e _ => e.val
  | .coord v _ => v.val
  | .sum e _ => e.val
  | .track e σ _ => e.val * numSteps (s + 1) ℓ + σ
  | .coef e σ => e.val * numSteps (s + 1) ℓ + σ

/-- The offsets of the kinds, for `E` schemas, `N` steps and `W` locations. -/
def kindOff (E N W : ℕ) : Fin 7 → ℕ
  | 0 => 0
  | 1 => E * N
  | 2 => E * N + E
  | 3 => E * N + 2 * E
  | 4 => E * N + 2 * E + W
  | 5 => E * N + 3 * E + W
  | 6 => 2 * (E * N) + 3 * E + W

/-- The sizes of the kinds. -/
def kindSize (E N W : ℕ) : Fin 7 → ℕ
  | 0 => E * N
  | 1 => E
  | 2 => E
  | 3 => W
  | 4 => E
  | 5 => E * N
  | 6 => E * N

lemma famNum_eq (X : ICls I) :
    famNum I X = kindOff I.schemas.length (numSteps (s + 1) ℓ) I.numLocations (kindOf I X) +
      innerOf I X := by
  cases X <;> simp [famNum, kindOf, innerOf, kindOff]

lemma innerOf_lt {X : ICls I} (hX : ClsValid I X) :
    innerOf I X <
      kindSize I.schemas.length (numSteps (s + 1) ℓ) I.numLocations (kindOf I X) := by
  have hNS : ∀ (e : Fin I.schemas.length) (σ : ℕ), σ < numSteps (s + 1) ℓ →
      e.val * numSteps (s + 1) ℓ + σ < I.schemas.length * numSteps (s + 1) ℓ := by
    intro e σ hσ
    have := e.isLt
    calc e.val * numSteps (s + 1) ℓ + σ < (e.val + 1) * numSteps (s + 1) ℓ := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ this
  cases X with
  | upd e σ c => exact hNS e σ hX.1
  | track e σ c => exact hNS e σ hX.1
  | coef e σ => exact hNS e σ hX.1
  | junc e c => exact e.isLt
  | link e c => exact e.isLt
  | sum e c => exact e.isLt
  | coord v c => exact v.isLt

lemma kindOff_inj {E N W : ℕ} (k k' : Fin 7) {i i' : ℕ} (hi : i < kindSize E N W k)
    (hi' : i' < kindSize E N W k') (h : kindOff E N W k + i = kindOff E N W k' + i') :
    k = k' ∧ i = i' := by
  fin_cases k <;> fin_cases k' <;> simp only [kindOff, kindSize] at hi hi' h <;>
    first | (exact ⟨rfl, by omega⟩) | (exfalso; omega)

lemma famNum_injective {X Y : ICls I} (hX : ClsValid I X) (hY : ClsValid I Y)
    (h : famNum I X = famNum I Y) (hc : coordOf I X = coordOf I Y) : X = Y := by
  rw [famNum_eq, famNum_eq] at h
  obtain ⟨hk, hi⟩ := kindOff_inj _ _ (innerOf_lt I hX) (innerOf_lt I hY) h
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
    | (obtain ⟨rfl, rfl⟩ := hdiv _ _ _ _ hX.1 hY.1 hi; rfl)
    | (rw [Fin.ext hi])

lemma classNum_injective {X Y : ICls I} (hX : ClsValid I X) (hY : ClsValid I Y)
    (h : classNum I X = classNum I Y) : X = Y := by
  unfold classNum at h
  have r1 := regVal_lt (coordOf I X).2
  have r2 := regVal_lt (coordOf I Y).2
  have h1 := congrArg (· / 2 ^ ℓ) h
  have h2 := congrArg (· % 2 ^ ℓ) h
  have hp : 0 < 2 ^ ℓ := by positivity
  simp only [Nat.mul_comm _ (2 ^ ℓ), Nat.mul_add_div hp, Nat.div_eq_of_lt r1,
    Nat.div_eq_of_lt r2, Nat.mul_add_mod, Nat.mod_eq_of_lt r1, Nat.mod_eq_of_lt r2,
    add_zero] at h1 h2
  have i1 := (coordOf I X).1.isLt
  have i2 := (coordOf I Y).1.isLt
  have h3 := congrArg (· / (s + 1)) h1
  have h4 := congrArg (· % (s + 1)) h1
  simp only [Nat.add_comm _ ((s + 1) * _), Nat.mul_add_div (show 0 < s + 1 by omega),
    Nat.div_eq_of_lt i1, Nat.div_eq_of_lt i2, Nat.mul_add_mod, Nat.mod_eq_of_lt i1,
    Nat.mod_eq_of_lt i2, add_zero] at h3 h4
  exact famNum_injective I hX hY h3 (Prod.ext (Fin.ext h4) (regVal_injective h2))

lemma num_injective {a b : VName I} (ha : Valid I a) (hb : Valid I b)
    (h : num I a = num I b) : a = b := by
  unfold num at h
  have l1 := labNum_lt a.2
  have l2 := labNum_lt b.2
  have h1 := congrArg (· / 4) h
  have h2 := congrArg (· % 4) h
  simp only [Nat.add_comm (labNum _), Nat.mul_add_div (show 0 < 4 by omega),
    Nat.div_eq_of_lt l1, Nat.div_eq_of_lt l2, Nat.mul_add_mod, Nat.mod_eq_of_lt l1,
    Nat.mod_eq_of_lt l2, add_zero] at h1 h2
  exact Prod.ext (classNum_injective I ha.1 hb.1 h1) (labNum_injective h2)

lemma num_div_four (a : VName I) : num I a / 4 = classNum I a.1 := by
  unfold num
  have := labNum_lt a.2
  omega

lemma num_lt {a : VName I} (ha : Valid I a) : num I a < nOut I := by
  unfold num nOut classNum
  have l1 := labNum_lt a.2
  have r1 := regVal_lt (coordOf I a.1).2
  have i1 := (coordOf I a.1).1.isLt
  have f1 := famNum_lt I ha.1
  have h3 : ((coordOf I a.1).1.val + (s + 1) * famNum I a.1) < (s + 1) * famCount I := by
    have : (s + 1) * (famNum I a.1 + 1) ≤ (s + 1) * famCount I := Nat.mul_le_mul_left _ f1
    nlinarith
  have h4 : ((coordOf I a.1).1.val + (s + 1) * famNum I a.1) * 2 ^ ℓ +
      Circuits.regVal (coordOf I a.1).2 < 2 ^ ℓ * ((s + 1) * famCount I) := by
    have h5 : (((coordOf I a.1).1.val + (s + 1) * famNum I a.1) + 1) * 2 ^ ℓ ≤
        ((s + 1) * famCount I) * 2 ^ ℓ := Nat.mul_le_mul_right _ h3
    nlinarith
  omega

end Lax119563Proofs.Reduction
