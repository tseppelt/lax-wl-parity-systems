import Lax119563Proofs.Compiler.PSchSize

/-!
# The schema section of the input (for pass `P2`)

`schD I e = a :: locations ++ |D| :: coordinates ++ permutations` with `a ∈ {2, 3}` the arity,
`a` locations and `a` permutation descriptions of `k + k ℓ` numbers each
(`schemaDescription_eq'`); the coordinates of `D` are listed as `cdesc c = c.1 :: b₀ … b_{ℓ-1}`
in the order of `coordList D` (`domainDescription_eq'`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ W : ℕ}

/-- The description of a coordinate: its block, then its bits. -/
def cdesc (c : Coord k ℓ) : List ℕ := (c.1 : ℕ) :: blockDescription c.2

lemma length_cdesc (c : Coord k ℓ) : (cdesc c).length = ℓ + 1 := by
  simp [cdesc, blockDescription]

lemma sortNums_eq (D : Finset (Coord k ℓ)) :
    (D.image coordNum).sort (· ≤ ·) = (coordList D).map coordNum := by
  have hpw : ((coordList D).map coordNum).Pairwise (· < ·) :=
    pairwise_map_coordNum_allCoords.sublist ((List.filter_sublist).map _)
  have hfs : ((coordList D).map coordNum).toFinset = D.image coordNum := by
    ext n; simp
  rw [← hfs]
  exact (List.toFinset_sort _ hpw.nodup).mpr (hpw.imp le_of_lt)

lemma coordNumDescription_coordNum (c : Coord k ℓ) :
    coordNumDescription ℓ (coordNum c) = cdesc c := by
  rw [coordNum, blockNum_eq_regVal, coordNumDescription_eq (regVal_lt c.2), cdesc,
    blockDescription_eq]

lemma domainDescription_eq' (D : Finset (Coord k ℓ)) :
    domainDescription D = (coordList D).length :: (coordList D).flatMap cdesc := by
  rw [domainDescription]
  simp only [sortNums_eq, List.length_map, List.flatMap_map, coordNumDescription_coordNum]

/-- The locations of a schema. -/
def schLocs : Schema k ℓ W → List ℕ
  | .binary u v .. => [u, v]
  | .ternary u v w' .. => [u, v, w']

/-- The permutations of a schema. -/
def schPerms : Schema k ℓ W → List (BlockPerm k ℓ)
  | .binary _ _ _ σ τ => [σ, τ]
  | .ternary _ _ _ _ σ τ π => [σ, τ, π]

/-- The arity of a schema. -/
def arity (s : Schema k ℓ W) : ℕ := if Matrix.isTern s then 3 else 2

lemma length_schLocs (s : Schema k ℓ W) : (schLocs s).length = arity s := by
  cases s <;> simp [schLocs, arity, Matrix.isTern]

lemma length_perms (s : Schema k ℓ W) :
    ((schPerms s).flatMap permDescription).length = arity s * (k + k * ℓ) := by
  cases s <;> simp [schPerms, arity, Matrix.isTern, length_permDescription] <;> ring

lemma schemaDescription_eq' (s : Schema k ℓ W) :
    schemaDescription s = arity s :: schLocs s ++
      ((coordList s.domain).length :: (coordList s.domain).flatMap cdesc) ++
        (schPerms s).flatMap permDescription := by
  cases s <;> simp [schemaDescription, arity, Matrix.isTern, schLocs, schPerms, Schema.domain,
    domainDescription_eq']

lemma schLocs_le (s : Schema k ℓ W) : ∀ u ∈ schLocs s, u < W := by
  cases s <;> simp [schLocs]

variable (I : ImplicitParitySystem k ℓ)

/-- The description of schema `e`. -/
def schD (e : Fin I.schemas.length) : List ℕ := schemaDescription (sch I e)

lemma schsDesc_eq : schsDesc I = (List.finRange I.schemas.length).flatMap (schD I) := by
  have : I.schemas = (List.finRange I.schemas.length).map (sch I) :=
    List.ext_getElem (by simp) fun i h1 h2 => by simp [sch]
  rw [schsDesc]
  conv_lhs => rw [this]
  rw [List.flatMap_map]; rfl

/-- The descriptions of the first `j` schemas. -/
def schsPre (j : ℕ) : List ℕ := ((List.finRange I.schemas.length).take j).flatMap (schD I)

/-- The descriptions of the schemas from `j` on. -/
def schsSuf (j : ℕ) : List ℕ := ((List.finRange I.schemas.length).drop j).flatMap (schD I)

lemma schsDesc_split (j : ℕ) : schsDesc I = schsPre I j ++ schsSuf I j := by
  rw [schsDesc_eq, schsPre, schsSuf, ← List.flatMap_append, List.take_append_drop]

lemma schsSuf_cons {j : ℕ} (hj : j < I.schemas.length) :
    schsSuf I j = schD I ⟨j, hj⟩ ++ schsSuf I (j + 1) := by
  rw [schsSuf, List.drop_eq_getElem_cons (by simpa using hj), List.flatMap_cons, schsSuf]
  simp

lemma schsPre_succ {j : ℕ} (hj : j < I.schemas.length) :
    schsPre I (j + 1) = schsPre I j ++ schD I ⟨j, hj⟩ := by
  rw [schsPre, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [schsPre]

/-- The position of the description of schema `j`. -/
def schAt (j : ℕ) : ℕ := schPos I + (encodeNats (schsPre I j)).length

lemma drop_schAt (j : ℕ) : (encodeSystem I).drop (schAt I j) = encodeNats (schsSuf I j) := by
  rw [schAt, ← List.drop_drop, drop_schPos, schsDesc_split I j, encodeNats_append,
    List.drop_left]

lemma schPos_add : schPos I + (encodeNats (schsDesc I)).length = H I := by
  show _ = (encodeSystem I).length
  rw [schPos, posAt, locsPre_all, encodeSystem_eq, sd_eq]
  simp only [encNats_cons, encodeNats_append, List.length_append, List.cons_append,
    List.nil_append, List.singleton_append]
  ring

lemma schAt_le (j : ℕ) : schAt I j ≤ H I := by
  have h2 := schPos_add I
  rw [schsDesc_split I j, encodeNats_append, List.length_append] at h2
  unfold schAt; omega

lemma schAt_succ {j : ℕ} (hj : j < I.schemas.length) :
    schAt I (j + 1) = schAt I j + (encodeNats (schD I ⟨j, hj⟩)).length := by
  simp only [schAt, schsPre_succ I hj, encodeNats_append, List.length_append]; ring

lemma schAt_zero : schAt I 0 = schPos I := by simp [schAt, schsPre, encodeNats]

lemma schD_le_H (e : Fin I.schemas.length) : (encodeNats (schD I e)).length ≤ H I := by
  have h := schAt_le I (e.val + 1)
  rw [schAt_succ I e.2] at h
  have : schAt I e.val ≥ 0 := Nat.zero_le _
  simp only [Fin.eta] at h
  omega

lemma schD_length_le (e : Fin I.schemas.length) : (schD I e).length ≤ H I :=
  (length_le_encodeNats _).trans (schD_le_H I e)

end Lax119563Proofs.Compiler
