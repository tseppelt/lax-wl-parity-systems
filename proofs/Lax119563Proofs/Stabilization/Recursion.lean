import Mathlib

/-!
# Arithmetic of the recursion (replaces Döring–Neuen, Lemmas 5.13 and Claim 5.14)

With `c = Nat.clog 2` and the weight `recW d = 2 c(d) + 9`, the bound `h(n) = 10 n - recW n`
satisfies the recursion of Theorem 5.15. Stated additively: for a list `L` of dimensions with
sum `n`,
* (some `d ∈ L` with `n < 2 d < 2 n`) `recW n + 2 + c(n - d) ≤ Σ_L recW`;
* (all `2 d ≤ n`, `2 ≤ n`) `recW n + 1 + c(n²) ≤ Σ_L recW`.
-/

namespace Lax119563Proofs.Stabilization

/-- The weight `2 ⌈log₂ d⌉ + 9`. -/
def recW (d : ℕ) : ℕ := 2 * Nat.clog 2 d + 9

theorem clog_le_of_le_two_pow_mul {n m k : ℕ} (h : n ≤ 2 ^ k * m) :
    Nat.clog 2 n ≤ Nat.clog 2 m + k := by
  apply Nat.clog_le_of_le_pow
  have hm := Nat.le_pow_clog (by norm_num : 1 < 2) m
  calc n ≤ 2 ^ k * m := h
    _ ≤ 2 ^ k * 2 ^ Nat.clog 2 m := Nat.mul_le_mul_left _ hm
    _ = 2 ^ (Nat.clog 2 m + k) := by rw [pow_add, mul_comm]

theorem clog_add_le (a b : ℕ) : Nat.clog 2 (a + b) ≤ Nat.clog 2 a + Nat.clog 2 b + 1 := by
  rcases le_total a b with h | h
  · have := clog_le_of_le_two_pow_mul (n := a + b) (m := b) (k := 1) (by omega)
    omega
  · have := clog_le_of_le_two_pow_mul (n := a + b) (m := a) (k := 1) (by omega)
    omega

theorem clog_mul_self_le (n : ℕ) : Nat.clog 2 (n * n) ≤ 2 * Nat.clog 2 n := by
  apply Nat.clog_le_of_le_pow
  have hn := Nat.le_pow_clog (by norm_num : 1 < 2) n
  calc n * n ≤ 2 ^ Nat.clog 2 n * 2 ^ Nat.clog 2 n := Nat.mul_le_mul hn hn
    _ = 2 ^ (2 * Nat.clog 2 n) := by rw [← pow_add, two_mul]

theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem recW_add (a b : ℕ) : recW (a + b) ≤ recW a + recW b := by
  unfold recW; have := clog_add_le a b; omega

/-- Subadditivity of `recW` over a list with positive sum. -/
theorem recW_sum_le (L : List ℕ) (h : 1 ≤ L.sum) : recW L.sum ≤ (L.map recW).sum := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    simp only [List.sum_cons, List.map_cons]
    by_cases hL : L.sum = 0
    · rw [hL, add_zero]; exact Nat.le_add_right _ _
    · have := ih (by omega)
      have := recW_add a L.sum
      omega

/-- Recursion, case of a large block `2 d > n`. -/
theorem recursion_big (L : List ℕ) (n d : ℕ) (hsum : L.sum = n) (hd : d ∈ L) (hdn : d < n)
    (h2 : n < 2 * d) : recW n + 2 + Nat.clog 2 (n - d) ≤ (L.map recW).sum := by
  have hp := List.perm_cons_erase hd
  have hs : L.sum = d + (L.erase d).sum := by rw [hp.sum_eq, List.sum_cons]
  have hs' : (L.map recW).sum = recW d + ((L.erase d).map recW).sum := by
    rw [(hp.map recW).sum_eq, List.map_cons, List.sum_cons]
  have hrest := recW_sum_le (L.erase d) (by omega)
  have hrest' : (L.erase d).sum = n - d := by omega
  rw [hrest'] at hrest
  have hc : Nat.clog 2 n ≤ Nat.clog 2 d + 1 := clog_le_of_le_two_pow_mul (by omega)
  rw [hs']
  unfold recW at hrest ⊢
  omega

/-- Recursion, case of only small blocks `2 d ≤ n` (two groups of sum `≥ n / 4`). -/
theorem recursion_small (L : List ℕ) (n : ℕ) (hn : 2 ≤ n) (hsum : L.sum = n)
    (hsmall : ∀ x ∈ L, 2 * x ≤ n) : recW n + 1 + Nat.clog 2 (n * n) ≤ (L.map recW).sum := by
  classical
  have hex : ∃ k, n ≤ 4 * (L.take k).sum := ⟨L.length, by rw [List.take_length]; omega⟩
  set k := Nat.find hex with hk
  have hk1 : n ≤ 4 * (L.take k).sum := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h; rw [h, List.take_zero, List.sum_nil] at hk1; omega
  have hk2 : ¬ n ≤ 4 * (L.take (k - 1)).sum := Nat.find_min hex (by omega)
  have hlen : k - 1 < L.length := by
    by_contra hcon
    rw [List.take_of_length_le (by omega)] at hk2
    omega
  have htk : (L.take k).sum = (L.take (k - 1)).sum + L[k - 1] := by
    rw [← List.sum_take_succ _ _ hlen, Nat.sub_add_cancel (by omega)]
  have hmem := hsmall _ (List.getElem_mem hlen)
  have hsplit := List.sum_take_add_sum_drop L k
  have hsplit' : (L.map recW).sum = ((L.take k).map recW).sum + ((L.drop k).map recW).sum := by
    rw [← List.sum_take_add_sum_drop (L.map recW) k, List.map_take, List.map_drop]
  have h1 := recW_sum_le (L.take k) (by omega)
  have h2 := recW_sum_le (L.drop k) (by omega)
  have c1 : Nat.clog 2 n ≤ Nat.clog 2 (L.take k).sum + 2 :=
    clog_le_of_le_two_pow_mul (by norm_num; omega)
  have c2 : Nat.clog 2 n ≤ Nat.clog 2 (L.drop k).sum + 2 :=
    clog_le_of_le_two_pow_mul (by norm_num; omega)
  have c3 := clog_mul_self_le n
  rw [hsplit']
  unfold recW at h1 h2 ⊢
  omega

end Lax119563Proofs.Stabilization
