import Lax119563Proofs.Reduction.ValidKinds
import Lax119563Proofs.Reduction.OutEdgeList
import Lax119563Proofs.Reduction.DomGen

/-!
# The output lists slot by slot

The numbers `0, …, nOut - 1` are enumerated as families `F`, blocks `i ≤ s`, register values
`v < 2^ℓ` and label numbers `t < 4` (`range_nOut_flatMap`), i.e. as the slot numbers
`slotNum F i v t`; the families split into the seven kinds (`range_fam_flatMap`).

Validity of slot numbers, kind by kind (`outValid_upd` …): for every kind except `coef`, the
slot `(F, i, v, t)` of a family is the name `(X, labOf t)` of the class `X` of the family with
coordinate `(i, toBlk v)`.
-/

open Lax119563.ColoredGraphs Lax119563.BinaryEncodings Lax119563.ImplicitParitySystems
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ}

/-! ## Enumerating slots -/

/-- The slots of one family, in output order. -/
def slotL {β : Type} (s ℓ : ℕ) (f : ℕ → ℕ → ℕ → List β) : List β :=
  (List.range (s + 1)).flatMap fun i => (List.range (2 ^ ℓ)).flatMap fun v =>
    (List.range 4).flatMap fun t => f i v t

lemma range_nOut_flatMap {β : Type} (n : ℕ) (f : ℕ → List β) :
    (List.range (4 * (2 ^ ℓ * ((s + 1) * n)))).flatMap f =
      (List.range n).flatMap fun F => slotL s ℓ fun i v t => f (slotNum s ℓ F i v t) := by
  rw [Gn.flatMap_range_mul]
  rw [Gn.flatMap_range_mul]
  rw [Gn.flatMap_range_mul]
  unfold slotL slotNum
  refine List.flatMap_congr fun F _ => List.flatMap_congr fun i _ =>
    List.flatMap_congr fun v _ => List.flatMap_congr fun t _ => ?_
  congr 1; ring

lemma range_add_flatMap {β : Type} (a b : ℕ) (g : ℕ → List β) :
    (List.range (a + b)).flatMap g =
      (List.range a).flatMap g ++ (List.range b).flatMap fun j => g (a + j) := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]

/-- The families split into kinds. -/
lemma range_fam_flatMap {β : Type} (E N W : ℕ) (g : ℕ → List β) :
    (List.range (3 * (E * N) + 3 * E + W)).flatMap g =
      (List.range (E * N)).flatMap g ++
      (List.range E).flatMap (fun j => g (E * N + j)) ++
      (List.range E).flatMap (fun j => g (E * N + E + j)) ++
      (List.range W).flatMap (fun j => g (E * N + 2 * E + j)) ++
      (List.range E).flatMap (fun j => g (E * N + 2 * E + W + j)) ++
      (List.range (E * N)).flatMap (fun j => g (E * N + 3 * E + W + j)) ++
      (List.range (E * N)).flatMap (fun j => g (2 * (E * N) + 3 * E + W + j)) := by
  have h : 3 * (E * N) + 3 * E + W =
      E * N + E + E + W + E + E * N + E * N := by ring
  rw [h]
  have e1 : ∀ j, E * N + E + E + j = E * N + 2 * E + j := fun j => by ring
  rw [range_add_flatMap, range_add_flatMap, range_add_flatMap, range_add_flatMap,
    range_add_flatMap, range_add_flatMap]
  have e5 : ∀ j, E * N + 2 * E + W + E + j = E * N + 3 * E + W + j := fun j => by ring
  have e7 : ∀ j, E * N + 3 * E + W + E * N + j = 2 * (E * N) + 3 * E + W + j :=
    fun j => by ring
  simp only [List.append_assoc, e1, e5, e7]

/-- Families indexed by `(e, σ)`. -/
lemma range_mul_flatMap {β : Type} (E N : ℕ) (g : ℕ → List β) :
    (List.range (E * N)).flatMap g =
      (List.range E).flatMap fun e => (List.range N).flatMap fun σ => g (e * N + σ) := by
  rw [Nat.mul_comm, Gn.flatMap_range_mul]
  refine List.flatMap_congr fun e _ => List.flatMap_congr fun σ _ => ?_
  congr 1; ring

/-! ## Slots as names -/

/-- The block coordinate with register value `v`. -/
def toBlk (ℓ v : ℕ) : BlockCoord ℓ := (Circuits.ofAddr v : Fin 1 → Fin ℓ → ZMod 2) 0

lemma regVal_toBlk {v : ℕ} (hv : v < 2 ^ ℓ) : Circuits.regVal (toBlk ℓ v) = v := by
  rw [toBlk, regVal_ofAddr]
  simp [Circuits.field, Nat.mod_eq_of_lt hv]

/-- The label with number `t`. -/
def labOf (t : ℕ) : Lab := (⟨t % 2, Nat.mod_lt _ (by omega)⟩, ⟨t / 2 % 2, Nat.mod_lt _ (by omega)⟩)

lemma labNum_labOf {t : ℕ} (ht : t < 4) : labNum (labOf t) = t := by
  simp only [labNum, labOf]
  show t % 2 + 2 * (t / 2 % 2) = t
  omega

lemma labOf_fst_eq_zero {t : ℕ} : (labOf t).1 = 0 ↔ t % 2 = 0 := by
  simp only [labOf]
  constructor
  · intro h; exact congrArg Fin.val h
  · intro h; exact Fin.ext h

lemma labOf_snd_eq_zero {t : ℕ} (ht : t < 4) : (labOf t).2 = 0 ↔ t < 2 := by
  simp only [labOf]
  constructor
  · intro h; have := congrArg Fin.val h; simp at this; omega
  · intro h; exact Fin.ext (by show t / 2 % 2 = 0; omega)

variable (I : ImplicitParitySystem (s + 1) ℓ)

/-- The slot of a name of a bounded class `X` with coordinate `(i, toBlk v)`. -/
lemma outValid_slot {X : ICls I} (hX : ClsBnd I X) {i v t : ℕ} (hi : i < s + 1)
    (hv : v < 2 ^ ℓ) (ht : t < 4) (hc : coordOf I X = (⟨i, hi⟩, toBlk ℓ v)) :
    OutValid I (slotNum s ℓ (famNum I X) i v t) ↔ Valid I (X, labOf t) := by
  have := outValid_slotNum I hX hc (labOf t)
  rwa [regVal_toBlk hv, labNum_labOf ht] at this

section Kinds

variable {i v t : ℕ} (hi : i < s + 1) (hv : v < 2 ^ ℓ) (ht : t < 4)
include hi hv ht

lemma outValid_upd (e : Fin I.schemas.length) {σ : ℕ} (hσ : σ < numSteps (s + 1) ℓ)
    (hsℓ : 0 < s + ℓ) :
    OutValid I (slotNum s ℓ (e.val * numSteps (s + 1) ℓ + σ) i v t) ↔
      (⟨i, hi⟩, toBlk ℓ v) ∈ dom I e ∧ entB s (σ % (s + ℓ)) i v = true := by
  have h := outValid_slot I (X := .upd e σ (⟨i, hi⟩, toBlk ℓ v)) hσ hi hv ht rfl
  simp only [famNum] at h
  rw [h, valid_upd_iff, ent_ne_zero_iff hsℓ, regVal_toBlk hv]
  simp [hσ]

lemma outValid_track (e : Fin I.schemas.length) {σ : ℕ} (hσ : σ < numSteps (s + 1) ℓ)
    (hsℓ : 0 < s + ℓ) :
    OutValid I (slotNum s ℓ (I.schemas.length * numSteps (s + 1) ℓ + 3 * I.schemas.length +
        I.numLocations + (e.val * numSteps (s + 1) ℓ + σ)) i v t) ↔
      ((⟨i, hi⟩, toBlk ℓ v) ∈ dom I e ∧ entB s (σ % (s + ℓ)) i v = true) ∧ t < 2 := by
  have h := outValid_slot I (X := .track e σ (⟨i, hi⟩, toBlk ℓ v)) hσ hi hv ht rfl
  simp only [famNum] at h
  rw [h, valid_track_iff, ent_ne_zero_iff hsℓ, regVal_toBlk hv, labOf_snd_eq_zero ht]
  simp [hσ]

lemma outValid_junc (e : Fin I.schemas.length) :
    OutValid I (slotNum s ℓ (I.schemas.length * numSteps (s + 1) ℓ + e.val) i v t) ↔
      isTern (sch I e) = true ∧ (⟨i, hi⟩, toBlk ℓ v) ∈ dom I e := by
  have h := outValid_slot I (X := .junc e (⟨i, hi⟩, toBlk ℓ v)) trivial hi hv ht rfl
  simp only [famNum] at h
  rw [h, valid_junc_iff]

lemma outValid_link (e : Fin I.schemas.length) :
    OutValid I (slotNum s ℓ (I.schemas.length * numSteps (s + 1) ℓ + I.schemas.length + e.val)
        i v t) ↔ (⟨i, hi⟩, toBlk ℓ v) ∈ dom I e ∧ t < 2 := by
  have h := outValid_slot I (X := .link e (⟨i, hi⟩, toBlk ℓ v)) trivial hi hv ht rfl
  simp only [famNum] at h
  rw [h, valid_link_iff, labOf_snd_eq_zero ht]

lemma outValid_sum (e : Fin I.schemas.length) :
    OutValid I (slotNum s ℓ (I.schemas.length * numSteps (s + 1) ℓ + 2 * I.schemas.length +
        I.numLocations + e.val) i v t) ↔
      (isTern (sch I e) = true ∧ (⟨i, hi⟩, toBlk ℓ v) ∈ dom I e) ∧ t < 2 := by
  have h := outValid_slot I (X := .sum e (⟨i, hi⟩, toBlk ℓ v)) trivial hi hv ht rfl
  simp only [famNum] at h
  rw [h, valid_sum_iff, labOf_snd_eq_zero ht]

lemma outValid_coord (w : Fin I.numLocations) (hdom : I.domain w = Finset.univ) :
    OutValid I (slotNum s ℓ (I.schemas.length * numSteps (s + 1) ℓ + 2 * I.schemas.length +
        w.val) i v t) ↔ t < 2 ∧ ((I.init w).isSome = true → t = 0) := by
  have h := outValid_slot I (X := .coord w (⟨i, hi⟩, toBlk ℓ v)) trivial hi hv ht rfl
  simp only [famNum] at h
  rw [h, valid_coord_iff, labOf_snd_eq_zero ht, labOf_fst_eq_zero, hdom]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => by have := h2 h; omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => by rw [h2 h]⟩

end Kinds

lemma famNum_coef_unique {e : Fin I.schemas.length} {σ : ℕ} (Y : ICls I) (hY : ClsBnd I Y)
    (hσ : σ < numSteps (s + 1) ℓ) (h : famNum I Y = famNum I (.coef e σ)) : Y = .coef e σ := by
  have h' := h
  rw [famNum_eq, famNum_eq] at h'
  obtain ⟨hk, -⟩ := kindOff_inj _ _ (innerOf_lt' I hY) (innerOf_lt' I (X := .coef e σ) hσ) h'
  cases Y with
  | coef e' σ' => exact famNum_injective' I hY hσ h rfl
  | _ => simp [kindOf] at hk

lemma outValid_coef (hs : 1 ≤ s) (e : Fin I.schemas.length) {σ : ℕ}
    (hσ : σ < numSteps (s + 1) ℓ)
    (hdom : ∀ b : BlockCoord ℓ, ((Fin.last s, b) : Coord (s + 1) ℓ) ∈ dom I e)
    {i v t : ℕ} (hi : i < s + 1) (hv : v < 2 ^ ℓ) (ht : t < 4) :
    OutValid I (slotNum s ℓ (2 * (I.schemas.length * numSteps (s + 1) ℓ) +
        3 * I.schemas.length + I.numLocations + (e.val * numSteps (s + 1) ℓ + σ)) i v t) ↔
      (i = 0 ∧ v = 0) ∧ t < 2 := by
  have hF : famNum I (.coef e σ) = 2 * (I.schemas.length * numSteps (s + 1) ℓ) +
      3 * I.schemas.length + I.numLocations + (e.val * numSteps (s + 1) ℓ + σ) := rfl
  rw [← hF]
  by_cases hc : i = 0 ∧ v = 0
  · obtain ⟨rfl, rfl⟩ := hc
    have h := outValid_slot I (X := .coef e σ) hσ hi hv ht
      (by
        show ((0 : Fin (s + 1)), (0 : BlockCoord ℓ)) = _
        refine Prod.ext rfl ?_
        apply regVal_injective
        rw [regVal_toBlk hv, regVal_zero])
    rw [h, valid_coef_iff, labOf_snd_eq_zero ht]
    simp only [true_and, and_self, hσ, coef_exists I hs hdom σ]
  · rw [iff_false_intro hc, false_and, iff_false]
    have := not_outValid_slotNum I (X := .coef e σ) hσ (i := ⟨i, hi⟩) (b := toBlk ℓ v)
      (by
        intro h
        apply hc
        have h1 := congrArg (fun c => c.1.val) h
        have h2 := congrArg (fun c => Circuits.regVal c.2) h
        simp only [coordOf, Fin.val_zero, regVal_zero, regVal_toBlk hv] at h1 h2
        exact ⟨h1.symm, h2.symm⟩) t ht
      (fun Y hY hYF => famNum_coef_unique I Y hY hσ hYF)
    rwa [regVal_toBlk hv] at this

end Lax119563Proofs.Reduction
