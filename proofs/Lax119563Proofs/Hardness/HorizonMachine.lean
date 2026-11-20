import Lax119563Proofs.Hardness.ParMachine
import Lax119563Proofs.Compiler.Bound

/-!
# The machine putting the horizon in front of the input

For constants `s` and `c₀`, the structured program `hzProg s c₀` reads its input `x`, counts
its length `n`, computes `a = ⌈log₂ (n + 2)⌉` (`parA n`) by repeated doubling (as `parProg`),
then `s a` by `s` additions, and emits `[s a + c₀, s]`. Run with word size
`w = a + 2 s + c₀ + 9 = O(log n)`, each word operation costs `O(log² n)`, so the machine
`(withSuffix (hzProg s c₀).machine)` computes `encodeNats [s a + c₀, s] ++ x` from `x`
within `K (n + 1) (a + 1)^2` steps (`horizon_machine`), which is quasi-linear.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime Lax119563Proofs.Reduction
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

open Compiler Compiler.CStm

/-- The program. -/
def hzProg (s c₀ : ℕ) : CStm 6 0 :=
  .seq (.seq (.rd 0) (.loop (.var 0) (.seq (.set 1 (.add (.var 1) (.const 1))) (.rd 0))))
  (.seq (.seq (.set 2 (.const 1)) (.loop (.lt (.var 2) (.add (.var 1) (.const 2)))
      (.seq (.set 2 (.add (.var 2) (.var 2))) (.set 3 (.add (.var 3) (.const 1))))))
  (.seq (.loop (.lt (.var 5) (.const s))
      (.seq (.set 4 (.add (.var 4) (.var 3))) (.set 5 (.add (.var 5) (.const 1)))))
  (.seq (.emit (.add (.var 4) (.const c₀))) (.emit (.var 5)))))

lemma hzProg_depth (s c₀ : ℕ) : (hzProg s c₀).depth ≤ 10 := by
  simp [hzProg, CStm.depth, Ex.depth]

section Good

variable {x : List Bool} {w : ℕ}

local notation "NC" => Ex.nodeCost w

/-- Phase 3: `s a` by `s` additions. -/
lemma good_hz3 (s n p a : ℕ) (hw : s * a + s < 2 ^ w) :
    Good x w (.loop (.lt (.var 5) (.const s))
      (.seq (.set 4 (.add (.var 4) (.var 3))) (.set 5 (.add (.var 5) (.const 1)))))
      (st6 0 n p a (0 * a) 0 n []) (st6 0 n p a (s * a) s n [])
      ((s + 1) * (20 * NC)) := by
  have hS : ∀ j < s, Good x w
      (.seq (.set 4 (.add (.var 4) (.var 3))) (.set 5 (.add (.var 5) (.const 1))) : CStm 6 0)
      (st6 0 n p a (j * a) j n []) (st6 0 n p a ((j + 1) * a) (j + 1) n []) (8 * NC) := by
    intro j hj
    have hja : j * a + a ≤ s * a := by
      have := Nat.mul_le_mul_right a hj
      rwa [Nat.succ_mul] at this
    have hf1 : (Ex.add (.var 4) (.var 3) : Ex 6).Fits w (st6 0 n p a (j * a) j n []).env := by
      simp [Ex.Fits, st6, Ex.eval]; omega
    have hf2 : (Ex.add (.var 5) (.const 1) : Ex 6).Fits w
        ((st6 0 n p a (j * a) j n []).set 4 (j * a + a)).env := by
      simp [Ex.Fits, st6, Ex.eval, Function.update]
      refine ⟨by omega, ?_, by omega⟩
      rintro rfl
      simp at hw
      omega
    refine ((CStm.Good.set hf1).seq (CStm.Good.set hf2)).of_eq ?_ ?_
    · refine NSt.ext (funext fun i => ?_) rfl rfl rfl
      fin_cases i <;> simp [st6, Ex.eval, Function.update] <;> ring
    · simp only [Ex.size]; have := @unit_le_nc w; omega
  have hl := Good.loop_const (x := x) (w := w)
    (e := (Ex.lt (.var 5) (.const s))) s
    (fun j => st6 0 n p a (j * a) j n []) (8 * NC)
    (fun j hj => by simp [st6, Ex.eval, hj])
    (by simp [st6, Ex.eval])
    (fun j hj => by simp [Ex.Fits, st6]; omega)
    hS
  refine hl.mono ?_
  have := cond_le (w := w) (.lt (.var 5) (.const s)) (by simp [Ex.size])
  have e : (s + 1) * (20 * NC) = s * (20 * NC) + 20 * NC := by ring
  have e2 : s * (8 * NC + condCost w (Ex.lt (.var 5) (.const s) : Ex 6)) ≤
      s * (20 * NC) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Phase 4: the output. -/
lemma good_hz4 (s c₀ n p a : ℕ) (hw : s * a + c₀ + s < 2 ^ w) :
    Good x w (.seq (.emit (.add (.var 4) (.const c₀))) (.emit (.var 5)) : CStm 6 0)
      (st6 0 n p a (s * a) s n []) (st6 0 n p a (s * a) s n [s * a + c₀, s]) (8 * NC) := by
  refine ((CStm.Good.emit (by simp [Ex.Fits, st6, Ex.eval]; omega)).seq
    (CStm.Good.emit (by simp [Ex.Fits, st6]; omega))).of_eq ?_ ?_
  · simp [st6, Ex.eval]
  · simp only [Ex.size]; have := @unit_le_nc w; omega

/-- **The program.** -/
lemma good_hzProg (s c₀ : ℕ) (hw2 : 2 ≤ w)
    (hw : 4 * (x.length + 4) + s * (x.length + 2) + c₀ + s < 2 ^ w) :
    Good x w (hzProg s c₀) (NSt.zero 6 0)
      (st6 0 x.length (2 ^ parA x.length) (parA x.length) (s * parA x.length) s x.length
        [s * parA x.length + c₀, s])
      (40 * (x.length + s + 4) * NC) := by
  have ha := parA_le x.length
  have hsa : s * parA x.length ≤ s * (x.length + 2) := Nat.mul_le_mul_left _ ha
  have h1 := good_phase1 (x := x) hw2 (by omega)
  have h2 := good_phase2 (x := x) x.length hw2 (by omega)
  have h3 := good_hz3 (x := x) (w := w) s x.length (2 ^ parA x.length) (parA x.length)
    (by omega)
  have h4 := good_hz4 (x := x) (w := w) s c₀ x.length (2 ^ parA x.length) (parA x.length)
    (by omega)
  rw [show (st6 0 x.length (2 ^ parA x.length) (parA x.length) 0 0 x.length [] : NSt 6 0) =
    st6 0 x.length (2 ^ parA x.length) (parA x.length) (0 * parA x.length) 0 x.length [] by
      simp] at h2
  refine (h1.seq (h2.seq (h3.seq h4))).mono ?_
  have e1 : (x.length + 1) * (20 * NC) + ((parA x.length + 1) * (20 * NC) +
      ((s + 1) * (20 * NC) + 8 * NC)) ≤
      (x.length + parA x.length + s + 4) * (20 * NC) := by
    have : 8 * NC ≤ 20 * NC := by omega
    have e : (x.length + parA x.length + s + 4) * (20 * NC) = (x.length + 1) * (20 * NC) +
        ((parA x.length + 1) * (20 * NC) + ((s + 1) * (20 * NC) + 20 * NC)) := by ring
    omega
  have e2 : (x.length + parA x.length + s + 4) * (20 * NC) ≤
      (2 * (x.length + s + 4)) * (20 * NC) := Nat.mul_le_mul_right _ (by omega)
  have e3 : 40 * (x.length + s + 4) * NC = (2 * (x.length + s + 4)) * (20 * NC) := by ring
  omega

end Good

/-! ## The machine -/

/-- The time bound. -/
lemma hz_time_arith {n a s c₀ D cost NC out : ℕ}
    (hcost : cost ≤ 40 * (n + s + 4) * NC) (hNC : NC ≤ 64 * (D + 4) ^ 2 * (a + 1) ^ 2)
    (hout : out ≤ 2 * (s * a + c₀) + 1 + (2 * s + 1)) :
    16 * (cost + 20 * (n + out) + 10 + n + 1) ≤
      16 * (40 * (s + 4) * (64 * (D + 4) ^ 2) + 80 * s + 40 * c₀ + 72) *
        (n + 1) * (a + 1) ^ 2 := by
  obtain ⟨P, hP⟩ : ∃ P, P = (n + 1) * (a + 1) ^ 2 := ⟨_, rfl⟩
  have hA1 : 1 ≤ (a + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hP1 : n + 1 ≤ P := by
    rw [hP]; simpa using Nat.mul_le_mul_left (n + 1) hA1
  have haP : a ≤ P := by
    rw [hP]
    calc a ≤ 1 * (a + 1) ^ 1 := by simp
      _ ≤ (n + 1) * (a + 1) ^ 2 :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  obtain ⟨A, hA⟩ : ∃ A, A = 64 * (D + 4) ^ 2 := ⟨_, rfl⟩
  rw [← hA] at hNC ⊢
  have h1 : (n + s + 4) * NC ≤ (s + 4) * A * P := by
    calc (n + s + 4) * NC ≤ ((s + 4) * (n + 1)) * (A * (a + 1) ^ 2) :=
          Nat.mul_le_mul (by nlinarith) hNC
      _ = (s + 4) * A * P := by rw [hP]; ring
  have h2 : s * a ≤ s * P := Nat.mul_le_mul_left _ haP
  have h3 : c₀ ≤ c₀ * P := Nat.le_mul_of_pos_right _ (by omega)
  have h4 : 40 * (n + s + 4) * NC = 40 * ((n + s + 4) * NC) := by ring
  have e : 16 * (40 * (s + 4) * A + 80 * s + 40 * c₀ + 72) * (n + 1) * (a + 1) ^ 2 =
      16 * (40 * ((s + 4) * A * P) + 80 * (s * P) + 40 * (c₀ * P) + 72 * P) := by
    rw [hP]; ring
  rw [e]
  have h5 : s ≤ s * P := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- **The horizon machine.** For constants `s` and `c₀` there is a deterministic machine
computing `encodeNats [s ⌈log₂ (n + 2)⌉ + c₀, s] ++ x` from an input `x` of length `n`
within `K (n + 1) (⌈log₂ (n + 2)⌉ + 1)^2` steps. -/
theorem horizon_machine (s c₀ : ℕ) : ∃ P : Machine, Deterministic P ∧ ∃ K : ℕ,
    ∀ x : List Bool,
      ComputesWithin P x (encodeNats [s * parA x.length + c₀, s] ++ x)
        (K * (x.length + 1) * (parA x.length + 1) ^ 2) := by
  obtain ⟨D, hD⟩ : ∃ D, D = 2 * s + c₀ + 9 := ⟨_, rfl⟩
  refine ⟨(withSuffix ((hzProg s c₀).machine 10)).compile, withSuffix_deterministic,
    16 * (40 * (s + 4) * (64 * (D + 4) ^ 2) + 80 * s + 40 * c₀ + 72), fun x => ?_⟩
  obtain ⟨w, hw⟩ : ∃ w, w = parA x.length + D := ⟨_, rfl⟩
  have ha1 := one_le_parA x.length
  have hw2 : 2 ≤ w := by omega
  have hwb : 4 * (x.length + 4) + s * (x.length + 2) + c₀ + s < 2 ^ w := by
    have h1 : 2 ^ w = 2 ^ parA x.length * 2 ^ D := by rw [hw, pow_add]
    have h2 : (x.length + 2) * 2 ^ D ≤ 2 ^ parA x.length * 2 ^ D :=
      Nat.mul_le_mul_right _ (le_pow_parA x.length)
    have h3 : (x.length + 2) * D < (x.length + 2) * 2 ^ D :=
      Nat.mul_lt_mul_of_pos_left Nat.lt_two_pow_self (by omega)
    have h4 : 4 * (x.length + 4) + s * (x.length + 2) + c₀ + s ≤ (x.length + 2) * D := by
      have e : (x.length + 2) * D = (x.length + 2) * (2 * s + c₀ + 9) := by rw [hD]
      have : c₀ + s ≤ (x.length + 2) * (c₀ + s) := Nat.le_mul_of_pos_left _ (by omega)
      rw [e]; nlinarith
    omega
  obtain ⟨hf, he, hc⟩ := good_hzProg (x := x) s c₀ hw2 hwb
  have h := CStm.computesWithin (D := 10) hw2 (hzProg_depth s c₀) hf
  rw [he] at h
  simp only [st6] at h
  have h2 := withSuffix_computesWithin h
  refine Main.Compose.computesWithin_mono' h2 ?_
  have hlen : (encodeNats [s * parA x.length + c₀, s]).length ≤
      2 * (s * parA x.length + c₀) + 1 + (2 * s + 1) := by
    have e1 := length_encodeNat_le (s * parA x.length + c₀)
    have e2 := length_encodeNat_le s
    simp only [encodeNats, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append]
    omega
  have hNC : Ex.nodeCost w ≤ 64 * (D + 1 + 3) ^ 2 * (parA x.length + 1) ^ 2 :=
    nodeCost_le_sq (by rw [hw]; nlinarith)
  exact hz_time_arith hc hNC hlen

end Lax119563Proofs.Hardness
