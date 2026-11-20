import Lax119563Proofs.Reduction.SLib

/-!
# Arithmetic with structured statements

Accumulating loops `acc := acc + e` (`Stm.exec_accum`) and derived routines:
multiplication by repeated addition (`mulS`), truncated subtraction by counting (`subS`),
multiplication by a power of two by repeated doubling (`shlS`), and halving `p` times
(`shrS`). Each comes with its exact value; costs follow from `Good.loop`.
-/

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

namespace Stm

/-- The accumulating loop `for i < lim: acc := acc + e`. -/
def accum (i lim acc : Fin R) (e : Ex R) : Stm R :=
  loop i lim (set acc (Ex.add (Ex.var acc) e))

/-- `acc := a * b` (by `b` additions; `i` is a counter). -/
def mulS (a b acc i : Fin R) : Stm R :=
  seq (set acc (Ex.const 0)) (accum i b acc (Ex.var a))

/-- `acc := a - b` (truncated; by counting `t < a` with `b ≤ t`). -/
def subS (a b acc i : Fin R) : Stm R :=
  seq (set acc (Ex.const 0))
    (accum i a acc (Ex.lt (Ex.var b) (Ex.add (Ex.var i) (Ex.const 1))))

/-- `acc := acc * 2 ^ k` (by `k` doublings). -/
def shlS (k acc i : Fin R) : Stm R := loop i k (set acc (Ex.add (Ex.var acc) (Ex.var acc)))

lemma exec_shlS {k acc i : Fin R} (hia : i ≠ acc) (hka : k ≠ acc) (env : Fin R → ℕ) :
    (exec x (shlS k acc i) env).1 acc = env acc * 2 ^ env k ∧
    ∀ q, q ≠ i → q ≠ acc → (exec x (shlS k acc i) env).1 q = env q := by
  set F : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ :=
    fun j e' => exec x (set acc (Ex.add (Ex.var acc) (Ex.var acc))) (Function.update e' i j)
  have H := runLoop_inv (f := F) (L := env k) (env := env)
    (fun j e' => e' acc = env acc * 2 ^ j ∧ ∀ q, q ≠ i → q ≠ acc → e' q = env q)
    ⟨by simp, fun _ _ _ => rfl⟩
    (by
      intro j _ e' ⟨h1, h2⟩
      refine ⟨?_, fun q hqi hqa => ?_⟩
      · simp only [F, exec, Function.update_self, Ex.eval, Function.update_of_ne (Ne.symm hia)]
        rw [h1, pow_succ]; ring
      · simp only [F, exec, Function.update_of_ne hqa, Function.update_of_ne hqi]
        exact h2 q hqi hqa)
    (env k) le_rfl
  refine ⟨?_, fun q hqi hqa => ?_⟩
  · simp only [shlS, exec, Function.update_of_ne (Ne.symm hia)]; exact H.1
  · simp only [shlS, exec, Function.update_of_ne hqi]; exact H.2 q hqi hqa

/-- `acc := acc / 2 ^ k` (by `k` halvings). -/
def shrS (k acc i : Fin R) : Stm R := loop i k (set acc (Ex.half (Ex.var acc)))

lemma exec_shrS {k acc i : Fin R} (hia : i ≠ acc) (hka : k ≠ acc) (env : Fin R → ℕ) :
    (exec x (shrS k acc i) env).1 acc = env acc / 2 ^ env k ∧
    ∀ q, q ≠ i → q ≠ acc → (exec x (shrS k acc i) env).1 q = env q := by
  set F : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ :=
    fun j e' => exec x (set acc (Ex.half (Ex.var acc))) (Function.update e' i j)
  have H := runLoop_inv (f := F) (L := env k) (env := env)
    (fun j e' => e' acc = env acc / 2 ^ j ∧ ∀ q, q ≠ i → q ≠ acc → e' q = env q)
    ⟨by simp, fun _ _ _ => rfl⟩
    (by
      intro j _ e' ⟨h1, h2⟩
      refine ⟨?_, fun q hqi hqa => ?_⟩
      · simp only [F, exec, Function.update_self, Ex.eval, Function.update_of_ne (Ne.symm hia)]
        rw [h1, pow_succ, Nat.div_div_eq_div_mul]
      · simp only [F, exec, Function.update_of_ne hqa, Function.update_of_ne hqi]
        exact h2 q hqi hqa)
    (env k) le_rfl
  refine ⟨?_, fun q hqi hqa => ?_⟩
  · simp only [shrS, exec, Function.update_of_ne (Ne.symm hia)]; exact H.1
  · simp only [shrS, exec, Function.update_of_ne hqi]; exact H.2 q hqi hqa

/-- One step of the XOR loop. -/
def xorBody (a b res pw : Fin R) : Stm R :=
  seq (ite (Ex.odd (Ex.add (Ex.odd (Ex.var a)) (Ex.odd (Ex.var b))))
      (set res (Ex.add (Ex.var res) (Ex.var pw))) skip)
    (seq (set a (Ex.half (Ex.var a))) (seq (set b (Ex.half (Ex.var b)))
      (set pw (Ex.add (Ex.var pw) (Ex.var pw)))))

/-- `res := (a ^^^ b) % 2 ^ lim`; destroys `a, b`, uses `pw` and the counter `t`. -/
def xorS (a b res pw t lim : Fin R) : Stm R :=
  seq (set res (Ex.const 0)) (seq (set pw (Ex.const 1)) (loop t lim (xorBody a b res pw)))

lemma xor_step (a b k : ℕ) : (a ^^^ b) % 2 ^ (k + 1) =
    (a ^^^ b) % 2 ^ k + (if (a / 2 ^ k % 2 + b / 2 ^ k % 2) % 2 ≠ 0 then 2 ^ k else 0) := by
  rw [Nat.mod_pow_succ]
  have : (a ^^^ b) / 2 ^ k % 2 = (a / 2 ^ k % 2 + b / 2 ^ k % 2) % 2 := by
    rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib, Nat.xor_mod_two_eq,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]; omega
  rw [this]
  split_ifs with h
  · rw [show (a / 2 ^ k % 2 + b / 2 ^ k % 2) % 2 = 1 by omega, mul_one]
  · rw [show (a / 2 ^ k % 2 + b / 2 ^ k % 2) % 2 = 0 by omega, mul_zero]

lemma exec_xorS {a b res pw t lim : Fin R} (hab : a ≠ b) (har : a ≠ res) (hap : a ≠ pw)
    (hat : a ≠ t) (hbr : b ≠ res) (hbp : b ≠ pw) (hbt : b ≠ t) (hrp : res ≠ pw)
    (hrt : res ≠ t) (hpt : pw ≠ t) (hla : lim ≠ a) (hlb : lim ≠ b) (hlr : lim ≠ res)
    (hlp : lim ≠ pw) (env : Fin R → ℕ) :
    (exec x (xorS a b res pw t lim) env).1 res = (env a ^^^ env b) % 2 ^ env lim ∧
    ∀ q, q ≠ a → q ≠ b → q ≠ res → q ≠ pw → q ≠ t →
      (exec x (xorS a b res pw t lim) env).1 q = env q := by
  set env₀ := Function.update (Function.update env res 0) pw 1
  set F : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ :=
    fun j e' => exec x (xorBody a b res pw) (Function.update e' t j)
  have H := runLoop_inv (f := F) (L := env lim) (env := env₀)
    (fun j e' => e' res = (env a ^^^ env b) % 2 ^ j ∧ e' a = env a / 2 ^ j ∧
      e' b = env b / 2 ^ j ∧ e' pw = 2 ^ j ∧
      ∀ q, q ≠ a → q ≠ b → q ≠ res → q ≠ pw → q ≠ t → e' q = env₀ q)
    ⟨by simp [env₀, Function.update_apply, hrp, Nat.mod_one], by simp [env₀, Function.update_apply, hap, har],
      by simp [env₀, Function.update_apply, hbp, hbr], by simp [env₀],
      fun _ _ _ _ _ _ => rfl⟩
    (by
      intro j _ e' ⟨h1, h2, h3, h4, h5⟩
      have ea : Function.update e' t j a = env a / 2 ^ j := by
        rw [Function.update_of_ne hat, h2]
      have eb : Function.update e' t j b = env b / 2 ^ j := by
        rw [Function.update_of_ne hbt, h3]
      have er : Function.update e' t j res = (env a ^^^ env b) % 2 ^ j := by
        rw [Function.update_of_ne hrt, h1]
      have ep : Function.update e' t j pw = 2 ^ j := by
        rw [Function.update_of_ne hpt, h4]
      have hstep := xor_step (env a) (env b) j
      rw [pow_succ] at hstep
      simp only [F, xorBody, exec, Ex.eval, ea, eb]
      split_ifs with hc
      all_goals simp only [exec, Ex.eval]
      all_goals refine ⟨?_, ?_, ?_, ?_, fun q q1 q2 q3 q4 q5 => by
        simp only [Function.update_apply, q1, q2, q3, q4, q5, if_false]; exact h5 q q1 q2 q3 q4 q5⟩
      all_goals simp only [Function.update_apply, hab, hab.symm, har, har.symm, hap, hap.symm,
        hat, hat.symm, hbr, hbr.symm, hbp, hbp.symm, hbt, hbt.symm, hrp, hrp.symm, hrt,
        hrt.symm, hpt, hpt.symm, if_false, if_true, h1, h2, h3, h4, hstep, pow_succ,
        Nat.div_div_eq_div_mul, hc]
      all_goals first | rfl | (rw [if_pos hc]) | (rw [if_neg hc]) | omega | ring)
    (env lim) le_rfl
  have hL : env₀ lim = env lim := by simp [env₀, Function.update_apply, hlr, hlp]
  have hxe : exec x (xorS a b res pw t lim) env =
      exec x (loop t lim (xorBody a b res pw)) env₀ := by
    simp [xorS, exec, Ex.eval, env₀]
  rw [hxe]
  simp only [exec, hL]
  refine ⟨?_, fun q q1 q2 q3 q4 q5 => ?_⟩
  · rw [Function.update_of_ne hrt]; exact H.1
  · rw [Function.update_of_ne q5, H.2.2.2.2 q q1 q2 q3 q4 q5]
    simp [env₀, Function.update_apply, q3, q4]

end Stm

end Lax119563Proofs.Reduction
