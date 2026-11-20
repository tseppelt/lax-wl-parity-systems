import Lax119563Proofs.Reduction.PkSys

/-!
# The preprocessed input of the packed generator

The packed generator reads `h, s` and `x` from the input `pkInput x h s`: for every position
`k < m = max(|x|, h, s, 2^⌈(h+2)/s⌉)` a record of two numbers with fixed binary lengths
(`8 + x_k + 2 [k < |x|] + 4 [k < h]` and `4 + [k < s]`), whose codes take `16` symbols, so
that the bit of position `16 k + j` is the bit `j` of the record `k` (`inBit_pkInput`):
`x_k` at `j = 1`, `[k < |x|]` at `j = 3`, `[k < h]` at `j = 5`, `[k < s]` at `j = 10`.
The counts of the flags are `|x|, h, s` (`count_pkInput`).
-/

namespace Lax119563Proofs.Reduction

open Lax119563.BinaryEncodings Xp

/-! ## The format -/

/-- The number of records. -/
def pkLen (n h s : ℕ) : ℕ := max (max n h) (max s (2 ^ ((h + 1 + s) / s)))

/-- The two numbers of record `k`. -/
def pkRec (x : List Bool) (h s k : ℕ) : List ℕ :=
  [8 + (x.getD k false).toNat + 2 * (decide (k < x.length)).toNat + 4 * (decide (k < h)).toNat,
    4 + (decide (k < s)).toNat]

/-- The preprocessed input. -/
def pkInput (x : List Bool) (h s : ℕ) : List Bool :=
  encodeNats ((List.range (pkLen x.length h s)).flatMap (pkRec x h s))

/-- The `16` symbols of a record. -/
def pkBlk (a b c d : Bool) : List Bool :=
  [true, a, true, b, true, c, true, true, false, true, d, true, false, true, true, false]

lemma encodeNats_rec (a b c d : Bool) :
    encodeNats [8 + a.toNat + 2 * b.toNat + 4 * c.toNat, 4 + d.toNat] = pkBlk a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

lemma pkInput_eq (x : List Bool) (h s : ℕ) :
    pkInput x h s = (List.range (pkLen x.length h s)).flatMap fun k =>
      pkBlk (x.getD k false) (decide (k < x.length)) (decide (k < h)) (decide (k < s)) := by
  rw [pkInput, encodeNats, List.flatMap_assoc]
  refine List.flatMap_congr fun k _ => ?_
  rw [← encodeNats_rec]
  rfl

lemma length_pkBlk (a b c d : Bool) : (pkBlk a b c d).length = 16 := rfl

lemma getElem?_blocks (blk : ℕ → List Bool) (hb : ∀ k, (blk k).length = 16) :
    ∀ m k j, j < 16 → ((List.range m).flatMap blk)[j + 16 * k]? =
      if k < m then (blk k)[j]? else none
  | 0, k, j, _ => by simp
  | m + 1, k, j, hj => by
    have hl : ((List.range m).flatMap blk).length = 16 * m := by
      rw [List.length_flatMap]; simp [hb, Nat.mul_comm]
    rw [List.range_succ, List.flatMap_append, List.getElem?_append]
    by_cases hk : k < m
    · rw [if_pos (by omega), getElem?_blocks blk hb m k j hj, if_pos hk, if_pos (by omega)]
    · rw [if_neg (by omega), List.flatMap_singleton, hl]
      by_cases hkm : k = m
      · subst hkm
        rw [if_pos (by omega), show j + 16 * k - 16 * k = j by omega]
      · rw [if_neg (by omega), List.getElem?_eq_none (by rw [hb]; omega)]

lemma inBit_eq_getElem? (l : List Bool) (p : ℕ) :
    inBit l p = (l[p]?).elim 0 (fun b => b.toNat + 1) := by
  unfold inBit
  rcases Nat.lt_or_ge p l.length with h | h
  · rw [List.drop_eq_getElem_cons h, List.getElem?_eq_getElem h]; rfl
  · rw [List.drop_eq_nil_of_le h, List.getElem?_eq_none h]; rfl

/-- **The bits of the preprocessed input.** -/
lemma inBit_pkInput (x : List Bool) (h s k j : ℕ) (hj : j < 16) :
    inBit (pkInput x h s) (j + 16 * k) =
      if k < pkLen x.length h s then
        ((pkBlk (x.getD k false) (decide (k < x.length)) (decide (k < h)) (decide (k < s)))[j]?).elim
          0 (fun b => b.toNat + 1)
      else 0 := by
  rw [inBit_eq_getElem?, pkInput_eq, getElem?_blocks _ (fun _ => length_pkBlk _ _ _ _) _ k j hj]
  split_ifs <;> rfl

lemma length_pkInput (x : List Bool) (h s : ℕ) :
    (pkInput x h s).length = 16 * pkLen x.length h s := by
  rw [pkInput_eq, List.length_flatMap]; simp [length_pkBlk, Nat.mul_comm]

/-- The bit of `x` at `16 v + 1`. -/
lemma inBit_pkInput_x (x : List Bool) (h s : ℕ) {v : ℕ} (hv : v < x.length) :
    inBit (pkInput x h s) (1 + 16 * v) = inBit x v := by
  have hm : v < pkLen x.length h s := by unfold pkLen; omega
  rw [inBit_pkInput x h s v 1 (by omega), if_pos hm, inBit_eq_getElem?, List.getElem?_eq_getElem hv,
    List.getD_eq_getElem _ _ hv]
  rfl

/-! ## Counting flags -/

/-- `k % 16 = t`. -/
def isMod (t : ℕ) (kX : Xp) : Xp := eq kX (add (shl (shr kX (const 4)) (const 4)) (const t))

lemma eval_isMod (t : ℕ) (kX : Xp) (ρ : List ℕ) :
    (isMod t kX).eval ρ = if kX.eval ρ = kX.eval ρ / 16 * 16 + t then 1 else 0 := by
  rw [isMod, Xp.eval_eq]
  simp only [Xp.eval_add, Xp.eval_shl, Xp.eval_shr, Xp.eval_const]
  norm_num

/-- The count of the positions `k ≡ t (mod 16)` with input bit `1`, by a generator at depth
`d` (inside a `loopX`: `k` at `d + 1`, the input value at `d + 2`). -/
def flagGen (t d : ℕ) : Gn :=
  Gn.when (and (isMod t (var (d + 1))) (eq (var (d + 2)) (const 2))) (.emit (const 0))

lemma count_blocks {m : ℕ} (F : ℕ → ℕ → List ℕ) (t : ℕ) (ht : t < 16)
    (hF : ∀ q r, r < 16 → F q r = if r = t then F q t else []) :
    ((List.range (16 * m)).flatMap fun k => F (k / 16) (k % 16)) =
      (List.range m).flatMap fun q => F q t := by
  rw [Gn.flatMap_range_mul]
  refine List.flatMap_congr fun q _ => ?_
  have e : ∀ r ∈ List.range 16, F ((r + 16 * q) / 16) ((r + 16 * q) % 16) =
      if t = r then F q r else [] := fun r hr => by
    rw [List.mem_range] at hr
    rw [show (r + 16 * q) / 16 = q by omega, show (r + 16 * q) % 16 = r by omega, hF q r hr]
    by_cases h : r = t
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [List.flatMap_congr e, Gn.flatMap_range_ite, if_pos ht]

lemma length_flatMap_lt : ∀ m n : ℕ,
    ((List.range m).flatMap fun q => if q < n then [0] else []).length = min m n
  | 0, n => by simp
  | m + 1, n => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_lt m n]
    by_cases h : m < n
    · simp [h]; omega
    · simp [h]; omega

end Lax119563Proofs.Reduction
