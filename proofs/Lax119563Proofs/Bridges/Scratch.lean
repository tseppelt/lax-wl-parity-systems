import Mathlib
example (n : ℕ) : ((1 : Fin (n + 3)) : ℕ) = 1 := by simp
example (n : ℕ) : ((2 : Fin (n + 3)) : ℕ) = 2 := by simp
example (n : ℕ) : ((2 : Fin (n + 3)) : ℕ) = 2 := Nat.mod_eq_of_lt (by omega)
example (n : ℕ) : ((2 : Fin (n + 3)) : ℕ) = 2 := by rw [Fin.val_ofNat]; omega
