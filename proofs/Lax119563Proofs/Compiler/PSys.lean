import Lax119563Proofs.Compiler.OutDesc
import Lax119563Proofs.Compiler.CParse

/-!
# The structure of the input of the compiler program

`systemDescription I = k :: ℓ :: W :: (locsDesc I ++ E :: schsDesc I)` (`sd_eq`), with the
locations described by `locD I v = ι(v) :: domainDescription (I.domain v)`.

* Positions: `encodeNats_drop`: dropping the code of a prefix leaves the code of the rest.
* Sizes: the numbers `W`, `|D_v|`, `E` are at most the bit length `H` (`W_le`, `card_le`,
  `E_le`), so they fit into words when `2 (H + 1) ≤ 2 ^ w` (`bits_lt_of_le`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Codes of lists -/

lemma encNats_cons (v : ℕ) (l : List ℕ) :
    encodeNats (v :: l) = encodeNat v ++ encodeNats l := by simp [encodeNats]

lemma encodeNats_append (A B : List ℕ) :
    encodeNats (A ++ B) = encodeNats A ++ encodeNats B := by
  simp [encodeNats]

lemma encodeNats_drop (A B : List ℕ) :
    (encodeNats (A ++ B)).drop (encodeNats A).length = encodeNats B := by
  rw [encodeNats_append, List.drop_left]

lemma length_le_encodeNats : ∀ L : List ℕ, L.length ≤ (encodeNats L).length
  | [] => le_rfl
  | v :: L => by
    rw [encNats_cons, List.length_append, List.length_cons]
    have := length_le_encodeNats L
    have : 1 ≤ (encodeNat v).length := by simp [encodeNat]
    omega

/-- A number below `H + 1 ≤ 2 ^ (w - 1)` has fewer than `w` bits. -/
lemma bits_lt_of_le {v H w : ℕ} (hv : v ≤ H) (hH : 2 * (H + 1) ≤ 2 ^ w) :
    (Nat.bits v).length < w := by
  rw [Nat.size_eq_bits_len]
  rcases w with _ | w
  · simp at hH; omega
  · have h1 : v < 2 ^ w := by rw [pow_succ] at hH; omega
    have := Nat.size_le.mpr h1
    omega

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## The description of a system -/

/-- The description of location `v`. -/
def locD (v : Fin I.numLocations) : List ℕ :=
  initNum (I.init v) :: domainDescription (I.domain v)

/-- The descriptions of all locations. -/
def locsDesc : List ℕ := (List.finRange I.numLocations).flatMap (locD I)

/-- The descriptions of all schemas. -/
def schsDesc : List ℕ := I.schemas.flatMap schemaDescription

lemma sd_eq : systemDescription I =
    k :: ℓ :: I.numLocations :: (locsDesc I ++ I.schemas.length :: schsDesc I) := by
  simp [systemDescription, locsDesc, schsDesc]; rfl

lemma encodeSystem_eq : encodeSystem I = encodeNats (systemDescription I) := rfl

/-- The descriptions of the first `j` locations. -/
def locsPre (j : ℕ) : List ℕ :=
  ((List.finRange I.numLocations).take j).flatMap (locD I)

/-- The descriptions of the locations from `j` on. -/
def locsSuf (j : ℕ) : List ℕ :=
  ((List.finRange I.numLocations).drop j).flatMap (locD I)

lemma locsDesc_split (j : ℕ) : locsDesc I = locsPre I j ++ locsSuf I j := by
  rw [locsDesc, locsPre, locsSuf, ← List.flatMap_append, List.take_append_drop]

lemma locsSuf_cons {j : ℕ} (hj : j < I.numLocations) :
    locsSuf I j = locD I ⟨j, hj⟩ ++ locsSuf I (j + 1) := by
  rw [locsSuf, List.drop_eq_getElem_cons (by simpa using hj), List.flatMap_cons, locsSuf]
  simp

lemma locsPre_succ {j : ℕ} (hj : j < I.numLocations) :
    locsPre I (j + 1) = locsPre I j ++ locD I ⟨j, hj⟩ := by
  rw [locsPre, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [locsPre]

lemma locsPre_all : locsPre I I.numLocations = locsDesc I := by
  rw [locsPre, locsDesc, List.take_of_length_le (by simp)]

lemma locsSuf_all : locsSuf I I.numLocations = [] := by
  rw [locsSuf, List.drop_of_length_le (by simp)]; rfl

/-- The position of the description of location `j` in the input. -/
def posAt (j : ℕ) : ℕ := (encodeNats ([k, ℓ, I.numLocations] ++ locsPre I j)).length

lemma sd_split (j : ℕ) : systemDescription I =
    ([k, ℓ, I.numLocations] ++ locsPre I j) ++ (locsSuf I j ++ I.schemas.length :: schsDesc I) := by
  rw [sd_eq, locsDesc_split I j]; simp

lemma drop_posAt (j : ℕ) : (encodeSystem I).drop (posAt I j) =
    encodeNats (locsSuf I j ++ I.schemas.length :: schsDesc I) := by
  rw [encodeSystem_eq, sd_split I j, posAt, encodeNats_drop]

lemma posAt_le (j : ℕ) : posAt I j ≤ (encodeSystem I).length := by
  rw [encodeSystem_eq, sd_split I j, posAt,
    encodeNats_append ([k, ℓ, I.numLocations] ++ locsPre I j), List.length_append]; omega

lemma posAt_succ {j : ℕ} (hj : j < I.numLocations) :
    posAt I (j + 1) = posAt I j + (encodeNats (locD I ⟨j, hj⟩)).length := by
  simp only [posAt, locsPre_succ I hj, ← List.append_assoc, encodeNats_append,
    List.length_append]

/-- The start of the input: `k`, `ℓ`, `W`. -/
lemma posAt_zero : posAt I 0 = (encodeNat k).length + (encodeNat ℓ).length +
    (encodeNat I.numLocations).length := by
  simp [posAt, locsPre, encNats_cons, encodeNats]; ring

lemma drop_zero_k : (encodeSystem I).drop 0 = encodeNat k ++
    encodeNats (ℓ :: I.numLocations :: (locsDesc I ++ I.schemas.length :: schsDesc I)) := by
  rw [List.drop_zero, encodeSystem_eq, sd_eq, encNats_cons]

lemma drop_ell : (encodeSystem I).drop (encodeNat k).length = encodeNat ℓ ++
    encodeNats (I.numLocations :: (locsDesc I ++ I.schemas.length :: schsDesc I)) := by
  rw [encodeSystem_eq, sd_eq, encNats_cons, List.drop_left, encNats_cons]

lemma drop_W : (encodeSystem I).drop ((encodeNat k).length + (encodeNat ℓ).length) =
    encodeNat I.numLocations ++
      encodeNats (locsDesc I ++ I.schemas.length :: schsDesc I) := by
  rw [encodeSystem_eq, sd_eq, encNats_cons, encNats_cons, ← List.append_assoc,
    show (encodeNat k).length + (encodeNat ℓ).length = (encodeNat k ++ encodeNat ℓ).length by
      simp, List.drop_left, encNats_cons]

/-! ## Sizes -/

/-- The bit length of the input. -/
abbrev H : ℕ := (encodeSystem I).length

lemma length_sd_le : (systemDescription I).length ≤ H I := length_le_encodeNats _

lemma two_le_locD (v : Fin I.numLocations) : 2 ≤ (locD I v).length := by
  simp [locD, domainDescription]

lemma W_le_locsDesc : I.numLocations ≤ (locsDesc I).length := by
  rw [locsDesc, List.length_flatMap]
  have : ∀ v ∈ List.finRange I.numLocations, 1 ≤ (locD I v).length :=
    fun v _ => le_trans (by norm_num) (two_le_locD I v)
  calc I.numLocations = ((List.finRange I.numLocations).map fun _ => 1).sum := by simp
    _ ≤ _ := List.sum_le_sum (by simpa using this)

lemma W_le : I.numLocations ≤ H I := by
  have := length_sd_le I
  have := W_le_locsDesc I
  rw [sd_eq] at *; simp at *; omega

lemma E_le_schsDesc : I.schemas.length ≤ (schsDesc I).length := by
  rw [schsDesc, List.length_flatMap]
  have : ∀ e ∈ I.schemas, 1 ≤ (schemaDescription e).length := by
    intro e _; cases e <;> simp [schemaDescription]
  calc I.schemas.length = (I.schemas.map fun _ => 1).sum := by simp
    _ ≤ _ := List.sum_le_sum (by simpa using this)

lemma E_le : I.schemas.length ≤ H I := by
  have := length_sd_le I
  have := E_le_schsDesc I
  rw [sd_eq] at *; simp at *; omega

/-- The number `|D|` of coordinates (the head of the domain description). -/
lemma domainDescription_head {D : Finset (Coord k ℓ)} :
    ∃ rest, domainDescription D = (D.image coordNum).card :: rest ∧
      (D.image coordNum).card ≤ rest.length := by
  refine ⟨((D.image coordNum).sort (· ≤ ·)).flatMap (coordNumDescription ℓ), ?_, ?_⟩
  · rw [domainDescription]; simp [Finset.length_sort]
  rw [List.length_flatMap]
  have : ∀ c ∈ (D.image coordNum).sort (· ≤ ·), 1 ≤ (coordNumDescription ℓ c).length := by
    intro c _; simp [coordNumDescription]
  calc (D.image coordNum).card = (((D.image coordNum).sort (· ≤ ·)).map fun _ => 1).sum := by
        simp
    _ ≤ _ := List.sum_le_sum (by simpa using this)

lemma card_image_eq_zero_iff {D : Finset (Coord k ℓ)} : (D.image coordNum).card = 0 ↔ D = ∅ := by
  simp

lemma domainDescription_empty : domainDescription (∅ : Finset (Coord k ℓ)) = [0] := by
  simp [domainDescription]

lemma card_le (v : Fin I.numLocations) : ((I.domain v).image coordNum).card ≤ H I := by
  obtain ⟨rest, he, hl⟩ := domainDescription_head (D := I.domain v)
  have h1 : (locD I v).length ≤ (locsDesc I).length := by
    rw [locsDesc, List.length_flatMap]
    exact List.le_sum_of_mem (List.mem_map_of_mem (List.mem_finRange v))
  have h2 := length_sd_le I
  rw [sd_eq] at h2
  simp only [List.length_cons, List.length_append] at h2
  simp only [locD, he, List.length_cons] at h1
  omega

end Lax119563Proofs.Compiler
