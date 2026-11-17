import Lax119563Proofs.Reduction.ColAll

/-!
# The edge list slot by slot

`edgesOf I ε u = (upNbrs I ε u).flatMap fun w => [u, w]` is the part of the flattened edge list
of `outGraph I ε` contributed by `u`.

* `edgesOf_nonhub`: slots of non-hub families contribute nothing;
* `edgesOf_hub_slot`: the slot of a hub class `X` with coordinate `(i, toBlk v)` and label
  number `t` contributes, if valid, for each candidate `(Y, r)` of `nbrCand` whose name
  `nameOfEff ε Y r` is valid, the pair `[u, num (nameOfEff ε Y r)]`;
* numbers and validity of candidate names (`num_nameOfEff`, `valid_nameOfEff_coord`,
  `valid_nameOfEff_plain`).
-/

namespace Lax119563Proofs.Reduction

open Lax119563.ColoredGraphs Lax119563.ImplicitParitySystems Lax119563Proofs.Matrix
open Lax119563.BinaryEncodings

variable {s ℓ : ℕ} (I : ImplicitParitySystem (s + 1) ℓ)

open Classical in
/-- The contribution of `u` to the flattened edge list. -/
noncomputable def edgesOf (ε : ZMod 2) (u : ℕ) : List ℕ :=
  (upNbrs I ε u).flatMap fun w => [u, w]

lemma edgesOf_invalid (ε : ZMod 2) {u : ℕ} (hu : ¬ OutValid I u) : edgesOf I ε u = [] := by
  rw [edgesOf, upNbrs_invalid I ε hu]; rfl

lemma edgesOf_nonhub (ε : ZMod 2) {F i v t : ℕ} (hi : i < s + 1) (hv : v < 2 ^ ℓ) (ht : t < 4)
    (hF : I.schemas.length * numSteps (s + 1) ℓ + 2 * I.schemas.length ≤ F) :
    edgesOf I ε (slotNum s ℓ F i v t) = [] := by
  by_cases hu : OutValid I (slotNum s ℓ F i v t)
  · obtain ⟨a, ha, h1, h2, h3, h4⟩ := (outValid_slotNum_iff I hi hv ht).mp hu
    have hnum : num I a = slotNum s ℓ F i v t := by rw [num_eq_slotNum, h1, h2, h3, h4]
    have hh : isHub I a.1 = false := by
      by_contra hc
      have := famNum_hub_lt I ha.1 (by simpa using hc)
      omega
    rw [edgesOf, ← hnum, upNbrs_nonhub I ε ha hh]; rfl
  · exact edgesOf_invalid I ε hu

lemma flatMap_filter_map {α β : Type} (f : α → β) (P : β → Prop) [DecidablePred P] (g : β → ℕ)
    (u : ℕ) (l : List α) :
    (((l.map f).filter fun b => decide (P b)).map g).flatMap (fun w => [u, w]) =
      l.flatMap fun p => if P (f p) then [u, g (f p)] else [] := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.filter_cons, List.flatMap_cons]
    by_cases h : P (f p)
    · simp only [h, decide_true, if_true, List.map_cons, List.flatMap_cons, ← ih]
    · simp only [h, decide_false, Bool.false_eq_true, if_false, ← ih]
      rfl

open Classical in
/-- **The contribution of a hub slot.** -/
lemma edgesOf_hub_slot (hs : 1 ≤ s) (hT : TernOrdered I) (ε : ZMod 2) {X : ICls I}
    (hX : ClsBnd I X) (hh : isHub I X = true) {i v t : ℕ} (hi : i < s + 1) (hv : v < 2 ^ ℓ)
    (ht : t < 4) (hc : coordOf I X = (⟨i, hi⟩, toBlk ℓ v)) :
    edgesOf I ε (slotNum s ℓ (famNum I X) i v t) =
      if Valid I (X, labOf t) then
        (nbrCand I X (labOf t)).flatMap fun p =>
          if Valid I (nameOfEff I ε p.1 p.2) then
            [slotNum s ℓ (famNum I X) i v t, num I (nameOfEff I ε p.1 p.2)] else []
      else [] := by
  have hnum : num I (X, labOf t) = slotNum s ℓ (famNum I X) i v t := by
    rw [num_eq_slotNum]; simp only [hc, regVal_toBlk hv, labNum_labOf ht]
  by_cases hV : Valid I (X, labOf t)
  · rw [if_pos hV, edgesOf, ← hnum, upNbrs_hub I hs hT ε hV hh, hubNbrs]
    exact flatMap_filter_map _ _ _ _ _
  · rw [if_neg hV]
    exact edgesOf_invalid I ε fun h => hV ((outValid_slot I hX hi hv ht hc).mp h)

/-! ## Candidate names -/

lemma num_nameOfEff (ε : ZMod 2) (Y : ICls I) (r : ZMod 2) :
    num I (nameOfEff I ε Y r) = (r - ε * initBit I Y).val + 4 * classNum I Y := by
  simp [num, nameOfEff, labNum]

lemma valid_nameOfEff_plain (ε : ZMod 2) {Y : ICls I} (hY1 : twoBit I Y = false)
    (hY2 : isSingleton I Y = false) (r : ZMod 2) :
    Valid I (nameOfEff I ε Y r) ↔ ClsValid I Y := by
  simp [Valid, LabelOK, nameOfEff, hY1, hY2]

lemma valid_nameOfEff_coord (ε : ZMod 2) (w : Fin I.numLocations) (c : Coord (s + 1) ℓ)
    (hdom : I.domain w = Finset.univ) (r : ZMod 2) :
    Valid I (nameOfEff I ε (.coord w c) r) ↔
      ((I.init w).isSome = true → r - ε * initSeed I w c = 0) := by
  simp [Valid, ClsValid, LabelOK, nameOfEff, twoBit, isSingleton, hdom, initBit]

lemma initBit_plain {Y : ICls I} (h : ∀ w c, Y ≠ .coord w c) : initBit I Y = 0 := by
  cases Y with
  | coord w c => exact absurd rfl (h w c)
  | _ => rfl

/-! ## The flattened edge list -/

lemma slotL_nil {F : ℕ} (ε : ZMod 2)
    (hF : I.schemas.length * numSteps (s + 1) ℓ + 2 * I.schemas.length ≤ F) :
    slotL s ℓ (fun i v t => edgesOf I ε (slotNum s ℓ F i v t)) = [] := by
  unfold slotL
  simp only [List.flatMap_eq_nil_iff, List.mem_range]
  intro i hi v hv t ht
  exact edgesOf_nonhub I ε hi hv ht hF

/-- **The flattened edge list**: only the hub kinds contribute. -/
theorem edges_flat (ε : ZMod 2) :
    (edgeList (outGraph I ε)).flatMap (fun e => [e.1, e.2]) =
      (List.range (I.schemas.length * numSteps (s + 1) ℓ)).flatMap (fun F =>
          slotL s ℓ fun i v t => edgesOf I ε (slotNum s ℓ F i v t)) ++
        (List.range I.schemas.length).flatMap (fun j =>
          slotL s ℓ fun i v t => edgesOf I ε
            (slotNum s ℓ (I.schemas.length * numSteps (s + 1) ℓ + j) i v t)) ++
        (List.range I.schemas.length).flatMap (fun j =>
          slotL s ℓ fun i v t => edgesOf I ε (slotNum s ℓ
            (I.schemas.length * numSteps (s + 1) ℓ + I.schemas.length + j) i v t)) := by
  rw [edgeList_outGraph, List.flatMap_assoc]
  have e1 : ∀ u, ((upNbrs I ε u).map fun v => (u, v)).flatMap (fun e => [e.1, e.2]) =
      edgesOf I ε u := fun u => by rw [edgesOf, List.flatMap_map]
  simp only [e1]
  rw [nOut, range_nOut_flatMap, famCount, range_fam_flatMap]
  have z : ∀ (n off : ℕ), I.schemas.length * numSteps (s + 1) ℓ + 2 * I.schemas.length ≤ off →
      (List.range n).flatMap (fun j => slotL s ℓ fun i v t =>
        edgesOf I ε (slotNum s ℓ (off + j) i v t)) = [] := by
    intro n off h
    simp only [List.flatMap_eq_nil_iff]
    intro j _
    exact slotL_nil I ε (by omega)
  rw [z _ (I.schemas.length * numSteps (s + 1) ℓ + 2 * I.schemas.length) le_rfl,
    z _ (I.schemas.length * numSteps (s + 1) ℓ + 2 * I.schemas.length + I.numLocations)
      (by omega),
    z _ (I.schemas.length * numSteps (s + 1) ℓ + 3 * I.schemas.length + I.numLocations)
      (by omega),
    z _ (2 * (I.schemas.length * numSteps (s + 1) ℓ) + 3 * I.schemas.length + I.numLocations)
      (by omega)]
  simp only [List.append_nil]

end Lax119563Proofs.Reduction
