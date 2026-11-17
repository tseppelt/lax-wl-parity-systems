import Lax119563.ImplicitSystemEncodings
import Lax119563Proofs.Reduction.PassBase

/-!
# The description of the compiled system (mathematics)

Explicit forms of the parts of `systemDescription` for the compiled systems of register
programs, in terms that a generator can emit:
* `blockNum_eq_regVal`: block coordinates are numbered by `regVal`;
* `domainDescription_eq_domL`: the description of a coordinate domain is the list of the
  numbers `i 2^ℓ + v` of its members, enumerated by `i < k`, `v < 2^ℓ` (`domL`), preceded by its
  length; for the full domain this is `range (k 2^ℓ)`;
* `permDescription_of_permDesc`: the description of a permutation described by a mask;
* `schemaDescription_of_match`: the description of a schema matching its numbers;
* `locsDesc_compile`: the location part of the description of a compiled system.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563Proofs.Programs

variable {s ℓ : ℕ}

/-! ## Block coordinates -/

lemma map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n :=
  List.ext_getElem (by simp) fun i _ _ => by simp

lemma flatMap_finRange {β : Type} (n : ℕ) (f : ℕ → List β) :
    (List.finRange n).flatMap (fun v => f v.val) = (List.range n).flatMap f := by
  rw [← map_val_finRange, List.flatMap_map]


lemma ofBits_eq_sum : ∀ (n : ℕ) (f : ℕ → Bool),
    ofBits n f = ∑ t : Fin n, (f t).toNat * 2 ^ (t : ℕ)
  | 0, _ => rfl
  | n + 1, f => by
    rw [ofBits, ofBits_eq_sum n, Fin.sum_univ_succ, Nat.bit_val]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    rw [Finset.mul_sum]
    have : ∀ t : Fin n, 2 * ((f (t + 1)).toNat * 2 ^ (t : ℕ)) = (f (t + 1)).toNat * (2 ^ (t : ℕ) * 2) :=
      fun t => by ring
    simp only [this]
    ring

lemma blockNum_eq_regVal (b : BlockCoord ℓ) : blockNum b = regVal b := by
  rw [blockNum, regVal, ofBits_eq_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [dif_pos t.isLt]
  rcases zmod2_cases (b t) with h | h <;> simp [h] <;> rfl

lemma toBlk_regVal (b : BlockCoord ℓ) : toBlk ℓ (regVal b) = b :=
  regVal_injective (regVal_toBlk (regVal_lt b))

/-- The number of the coordinate `(i, toBlk v)`. -/
lemma coordNum_toBlk {k i v : ℕ} (hi : i < k) (hv : v < 2 ^ ℓ) :
    coordNum ((⟨i, hi⟩, toBlk ℓ v) : Coord k ℓ) = i * 2 ^ ℓ + v := by
  simp [coordNum, blockNum_eq_regVal, regVal_toBlk hv]

/-- The fixed-width binary digits `v_0, …, v_{ℓ-1}` of `v`. -/
def bitsL (ℓ v : ℕ) : List ℕ := (List.range ℓ).map fun t => if v.testBit t then 1 else 0

lemma blockDescription_eq (b : BlockCoord ℓ) : blockDescription b = bitsL ℓ (regVal b) := by
  refine List.ext_getElem (by simp [blockDescription, bitsL]) fun t h1 h2 => ?_
  have ht : t < ℓ := by simpa [blockDescription] using h1
  simp only [blockDescription, bitsL, List.getElem_map, List.getElem_finRange, List.getElem_range,
    regVal, testBit_ofBits, ht, decide_true, Bool.true_and, dif_pos]
  rcases zmod2_cases (b ⟨t, ht⟩) with h | h <;> simp [h] <;> rfl

lemma coordNumDescription_eq {i v : ℕ} (hv : v < 2 ^ ℓ) :
    coordNumDescription ℓ (i * 2 ^ ℓ + v) = i :: bitsL ℓ v := by
  have h1 : (i * 2 ^ ℓ + v) / 2 ^ ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv, zero_add]
  rw [coordNumDescription, h1, bitsL]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [List.mem_range] at ht
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hv, if_pos ht]

/-! ## Coordinate domains -/

lemma range_mul_flatMap {β : Type} (E N : ℕ) (g : ℕ → List β) :
    (List.range (E * N)).flatMap g =
      (List.range E).flatMap fun e => (List.range N).flatMap fun σ => g (e * N + σ) := by
  rw [Nat.mul_comm, Gn.flatMap_range_mul]
  refine List.flatMap_congr fun e _ => List.flatMap_congr fun σ _ => ?_
  congr 1; ring

/-- The numbers `i 2^ℓ + v` (`i < k`, `v < 2^ℓ`) with `m i v`, in increasing order. -/
def domL (k ℓ : ℕ) (m : ℕ → ℕ → Bool) : List ℕ :=
  (List.range k).flatMap fun i => (List.range (2 ^ ℓ)).flatMap fun v =>
    if m i v then [i * 2 ^ ℓ + v] else []

lemma flatMap_ite_singleton (l : List ℕ) (p : ℕ → Bool) :
    l.flatMap (fun n => if p n then [n] else []) = l.filter p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, ih, List.filter_cons]
    split_ifs <;> rfl

lemma domL_eq_filter (k ℓ : ℕ) (m : ℕ → ℕ → Bool) :
    domL k ℓ m = (List.range (k * 2 ^ ℓ)).filter fun n => m (n / 2 ^ ℓ) (n % 2 ^ ℓ) := by
  rw [← flatMap_ite_singleton, range_mul_flatMap]
  unfold domL
  refine List.flatMap_congr fun i _ => List.flatMap_congr fun v hv => ?_
  rw [List.mem_range] at hv
  have h1 : (i * 2 ^ ℓ + v) / 2 ^ ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv, zero_add]
  have h2 : (i * 2 ^ ℓ + v) % 2 ^ ℓ = v := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
  rw [h1, h2]

/-- The coordinate descriptions `i, bits v` of the members `(i, v)` with `m i v`. -/
def cdL (k ℓ : ℕ) (m : ℕ → ℕ → Bool) : List ℕ :=
  (List.range k).flatMap fun i => (List.range (2 ^ ℓ)).flatMap fun v =>
    if m i v then i :: bitsL ℓ v else []

lemma domL_flatMap (k ℓ : ℕ) (m : ℕ → ℕ → Bool) :
    (domL k ℓ m).flatMap (coordNumDescription ℓ) = cdL k ℓ m := by
  unfold domL cdL
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun i _ => ?_
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun v hv => ?_
  rw [List.mem_range] at hv
  split <;> simp [coordNumDescription_eq hv]

/-- **Descriptions of coordinate domains.** -/
theorem domainDescription_eq_domL {k : ℕ} (D : Finset (Coord k ℓ)) (m : ℕ → ℕ → Bool)
    (hm : ∀ i (hi : i < k), ∀ v < 2 ^ ℓ, m i v = true ↔ ((⟨i, hi⟩, toBlk ℓ v) : Coord k ℓ) ∈ D) :
    domainDescription D = (domL k ℓ m).length :: cdL k ℓ m := by
  have hsort : (D.image coordNum).sort (· ≤ ·) = domL k ℓ m := by
    have hnd : (domL k ℓ m).Nodup := by
      rw [domL_eq_filter]; exact (List.nodup_range).filter _
    have hpw : (domL k ℓ m).Pairwise (· ≤ ·) := by
      rw [domL_eq_filter]
      exact (List.pairwise_lt_range.imp le_of_lt).filter _
    have hfs : (domL k ℓ m).toFinset = D.image coordNum := by
      ext n
      rw [List.mem_toFinset, domL_eq_filter, List.mem_filter, List.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hn, hmn⟩
        have hq : n / 2 ^ ℓ < k := by
          rw [Nat.div_lt_iff_lt_mul (by positivity)]; exact hn
        have hr : n % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt _ (by positivity)
        refine ⟨_, (hm _ hq _ hr).mp hmn, ?_⟩
        rw [coordNum_toBlk hq hr, Nat.mul_comm]
        exact Nat.div_add_mod n (2 ^ ℓ)
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨⟨i, hi⟩, b⟩ := c
        have hb := regVal_lt b
        have e : ((⟨i, hi⟩, b) : Coord k ℓ) = (⟨i, hi⟩, toBlk ℓ (regVal b)) := by
          rw [toBlk_regVal]
        rw [e] at hc ⊢
        rw [coordNum_toBlk hi hb]
        have h1 : (i * 2 ^ ℓ + regVal b) / 2 ^ ℓ = i := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hb,
            zero_add]
        have h2 : (i * 2 ^ ℓ + regVal b) % 2 ^ ℓ = regVal b := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
        refine ⟨?_, ?_⟩
        · calc i * 2 ^ ℓ + regVal b < i * 2 ^ ℓ + 2 ^ ℓ := by omega
            _ = (i + 1) * 2 ^ ℓ := by ring
            _ ≤ k * 2 ^ ℓ := Nat.mul_le_mul_right _ hi
        · rw [h1, h2]; exact (hm i hi _ hb).mpr hc
    rw [← hfs]
    exact (List.toFinset_sort _ hnd).mpr hpw
  unfold domainDescription
  simp only
  rw [hsort, domL_flatMap]

/-- The full domain. -/
lemma domL_true (k ℓ : ℕ) : domL k ℓ (fun _ _ => true) = List.range (k * 2 ^ ℓ) := by
  rw [domL_eq_filter, List.filter_true]

lemma domainDescription_univ (k ℓ : ℕ) :
    domainDescription (Finset.univ : Finset (Coord k ℓ)) =
      (k * 2 ^ ℓ) :: (List.range k).flatMap fun i => (List.range (2 ^ ℓ)).flatMap fun v =>
        i :: bitsL ℓ v := by
  rw [domainDescription_eq_domL _ (fun _ _ => true) (fun _ _ _ _ => by simp), domL_true,
    List.length_range]
  simp [cdL]

/-! ## Permutations -/

/-- The description of a permutation keeping the blocks and shifting by the mask. -/
lemma permDescription_of_permDesc {π : BlockPerm (s + 1) ℓ} {msk : ℕ} (h : PermDesc π msk) :
    permDescription π =
      List.range (s + 1) ++
        (List.range (s + 1)).flatMap (fun i => bitsL ℓ (shiftVal s ℓ msk i)) := by
  have hp : ∀ i, (π.perm i : ℕ) = i := fun i => by
    have := (h (i, 0)).1
    simp only [BlockPerm.apply] at this
    rw [this]
  have hs : ∀ i, blockDescription (π.shift i) = bitsL ℓ (shiftVal s ℓ msk i) := fun i => by
    have := (h (i, 0)).2
    simp only [BlockPerm.apply, zero_add, regVal_zero, Nat.zero_xor] at this
    rw [blockDescription_eq, this]
  unfold permDescription
  simp only [hp, hs]
  rw [← map_val_finRange, List.flatMap_map]

lemma permDesc_of_permId {π : BlockPerm (s + 1) ℓ} (h : PermId π) : PermDesc π 0 := by
  intro c
  rw [h c, shiftVal_zero]
  simp

/-! ## Schemas -/

/-- The emitted description of a schema with numbers `n`, domain list `dl` and mask `msk`. -/
def schDescN (s : ℕ) (ℓ : ℕ) (n : SchNum) (dl cd : List ℕ) : List ℕ :=
  let pd := fun m => List.range (s + 1) ++
    (List.range (s + 1)).flatMap (fun i => bitsL ℓ (shiftVal s ℓ m i))
  if n.tern then [3, n.u, n.v, n.en] ++ (dl.length :: cd) ++ pd n.msk ++ pd 0 ++ pd 0
  else [2, n.u, n.v] ++ (dl.length :: cd) ++ pd n.msk ++ pd 0

/-- **The description of a schema** from its numbers and its domain. -/
theorem schemaDescription_of_match {N : ℕ} {D : Finset (Coord (s + 1) ℓ)}
    {e : Schema (s + 1) ℓ N} {n : SchNum} (h : SchMatch D e n) (m : ℕ → ℕ → Bool)
    (hm : ∀ i (hi : i < s + 1), ∀ v < 2 ^ ℓ,
      m i v = true ↔ ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) ∈ e.domain) :
    schemaDescription e = schDescN s ℓ n (domL (s + 1) ℓ m) (cdL (s + 1) ℓ m) := by
  obtain ⟨ht, hu, hv, hen, hpu, hpv, hpe, -⟩ := h
  have hpv' := permDescription_of_permDesc (permDesc_of_permId hpv)
  have hpe' := permDescription_of_permDesc (permDesc_of_permId hpe)
  have hpu' := permDescription_of_permDesc hpu
  cases e with
  | binary u v D' σ τ =>
    simp only [isTern] at ht
    simp only [locU, locV] at hu hv
    simp only [permU] at hpu'
    simp only [permV] at hpv'
    simp only [Schema.domain] at hm
    simp only [schemaDescription, schDescN, ← ht, Bool.false_eq_true, if_false, hu, hv,
      hpu', hpv', domainDescription_eq_domL D' m hm, List.append_assoc, List.cons_append,
      List.nil_append]
  | ternary u v w D' σ τ π =>
    simp only [isTern] at ht
    simp only [locU, locV, locEnd] at hu hv hen
    simp only [permU] at hpu'
    simp only [permV] at hpv'
    simp only [permEnd] at hpe'
    simp only [Schema.domain] at hm
    simp only [schemaDescription, schDescN, ← ht, if_true, hu, hv, hen,
      hpu', hpv', hpe', domainDescription_eq_domL D' m hm, List.append_assoc, List.cons_append,
      List.nil_append]

/-! ## Locations -/

/-- The location part of the description of a compiled system. -/
theorem locsDesc_compile (R : RegisterProgram s ℓ) (p₀ : Fin R.numLocations)
    (a₀ : Fin s → Fin ℓ → ZMod 2) :
    (List.finRange (R.compile p₀ a₀).numLocations).flatMap
        (fun v => initNum ((R.compile p₀ a₀).init v) :: domainDescription ((R.compile p₀ a₀).domain v)) =
      (List.range R.compiledSize).flatMap fun v =>
        ((if v = (R.loc (.prog R.accept)).val then 1 else 0) +
          2 * (if v = (R.loc (.det .out)).val then 1 else 0)) ::
          ((s + 1) * 2 ^ ℓ) :: (List.range (s + 1)).flatMap fun i =>
            (List.range (2 ^ ℓ)).flatMap fun w => i :: bitsL ℓ w := by
  have hne : (R.loc (.prog R.accept)).val ≠ (R.loc (.det .out)).val := fun h =>
    absurd (R.loc_inj.mp (Fin.ext h)) (by simp)
  show (List.finRange R.compiledSize).flatMap
        (fun v => initNum (R.compiledInit v) :: domainDescription (Finset.univ : Finset (Coord (s + 1) ℓ))) = _
  rw [← flatMap_finRange]
  refine List.flatMap_congr fun v _ => ?_
  rw [domainDescription_univ]
  congr 1
  unfold RegisterProgram.compiledInit
  by_cases h1 : v = R.loc (.prog R.accept)
  · have h2 : v.val ≠ (R.loc (.det .out)).val := by rw [h1]; exact hne
    rw [if_pos h1, if_pos (congrArg Fin.val h1), if_neg h2]
    rfl
  · have h1' : v.val ≠ (R.loc (.prog R.accept)).val := fun h => h1 (Fin.ext h)
    rw [if_neg h1, if_neg h1']
    by_cases h2 : v = R.loc (.det .out)
    · rw [if_pos h2, if_pos (congrArg Fin.val h2)]; rfl
    · have h2' : v.val ≠ (R.loc (.det .out)).val := fun h => h2 (Fin.ext h)
      rw [if_neg h2, if_neg h2']; rfl

end Lax119563Proofs.Reduction
