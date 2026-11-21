import Lax119563Proofs.Compiler.CMachine
import Lax119563Proofs.Compiler.CLib

/-!
# Computing the parameters of the exponential lower bound

For a constant `c₀`, the structured program `parProg c₀` reads its input `x`, counts its
length `n`, computes `a = ⌈log₂ (n + 2)⌉` (`parA n`) by repeated doubling and
`s = ⌊(n + c₀ + 1) / a⌋ + 1` (`parS c₀ n`, the least `s` with `s a ≥ n + c₀ + 2`) by repeated
addition, and emits `[n + c₀, s]`. Its machine computes `encodeNats [n + c₀, s]` from `x`
within `K (n + 1)^3` steps (`parMachine_computesWithin`).
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime Lax119563Proofs.Reduction
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

open Compiler Compiler.CStm

/-- `⌈log₂ (n + 2)⌉`. -/
def parA (n : ℕ) : ℕ := Nat.clog 2 (n + 2)

/-- The number of data blocks: the least `s` with `s · parA n ≥ n + c₀ + 2`. -/
def parS (c₀ n : ℕ) : ℕ := (n + c₀ + 1) / parA n + 1

lemma one_le_parA (n : ℕ) : 1 ≤ parA n := Nat.clog_pos (by norm_num) (by omega)

lemma le_pow_parA (n : ℕ) : n + 2 ≤ 2 ^ parA n := Nat.le_pow_clog (by norm_num) _

lemma pow_parA_le (n : ℕ) : 2 ^ parA n ≤ 2 * (n + 2) := by
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n + 2) (by omega)
  have h1 := one_le_parA n
  unfold parA at h1 ⊢
  obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 (n + 2) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
  rw [hk] at h ⊢
  simp only [Nat.pred_succ] at h
  rw [pow_succ]; omega

lemma parA_le (n : ℕ) : parA n ≤ n + 2 :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

lemma pow_lt_of_lt_parA {n j : ℕ} (hj : j < parA n) : 2 ^ j < n + 2 :=
  (Nat.lt_clog_iff_pow_lt (by norm_num)).mp hj

lemma one_le_parS (c₀ n : ℕ) : 1 ≤ parS c₀ n := Nat.le_add_left 1 _

lemma parS_spec (c₀ n : ℕ) :
    n + c₀ + 2 ≤ parS c₀ n * parA n ∧ ∀ j < parS c₀ n, j * parA n < n + c₀ + 2 := by
  have ha := one_le_parA n
  refine ⟨?_, fun j hj => ?_⟩
  · unfold parS
    have := Nat.lt_div_mul_add (a := n + c₀ + 1) ha
    rw [add_mul, one_mul]; omega
  · unfold parS at hj
    have hj' : j ≤ (n + c₀ + 1) / parA n := by omega
    have := (Nat.le_div_iff_mul_le ha).mp hj'
    omega

/-! ## The program -/

/-- States of the program: registers `b, n, p, a, acc, s`. -/
def st6 (b n p a c s pos : ℕ) (out : List ℕ) : NSt 6 0 :=
  ⟨![b, n, p, a, c, s], fun _ => [], pos, out⟩

/-- The program. -/
def parProg (c₀ : ℕ) : CStm 6 0 :=
  .seq (.seq (.rd 0) (.loop (.var 0) (.seq (.set 1 (.add (.var 1) (.const 1))) (.rd 0))))
  (.seq (.seq (.set 2 (.const 1)) (.loop (.lt (.var 2) (.add (.var 1) (.const 2)))
      (.seq (.set 2 (.add (.var 2) (.var 2))) (.set 3 (.add (.var 3) (.const 1))))))
  (.seq (.loop (.lt (.var 4) (.add (.var 1) (.const (c₀ + 2))))
      (.seq (.set 4 (.add (.var 4) (.var 3))) (.set 5 (.add (.var 5) (.const 1)))))
  (.seq (.emit (.add (.var 1) (.const c₀))) (.emit (.var 5)))))

lemma parProg_depth (c₀ : ℕ) : (parProg c₀).depth ≤ 10 := by
  simp [parProg, CStm.depth, Ex.depth]

lemma inBit_lt {x : List Bool} {j : ℕ} (hj : j < x.length) : inBit x j ≠ 0 := by
  rw [inBit_eqN, List.drop_eq_getElem_cons hj]
  simp [rdVal]

lemma inBit_len (x : List Bool) : inBit x x.length = 0 := by
  rw [inBit_eqN]; simp [rdVal]

lemma inBit_le' (x : List Bool) (pos : ℕ) : inBit x pos ≤ 2 := by
  rw [inBit_eqN]
  rcases x.drop pos with _ | ⟨b, _⟩
  · simp [rdVal]
  · cases b <;> simp [rdVal]

section Good

variable {x : List Bool} {w : ℕ}

/-- Abbreviation of the cost of an expression node. -/
local notation "NC" => Ex.nodeCost w

lemma unit_le_nc : unitCost w ≤ NC := Ex.unitCost_le_nodeCost w

lemma cond_le (e : Ex 6) (hs : e.size ≤ 5) : condCost w e ≤ 6 * NC := by
  unfold condCost
  have : 1 ≤ unitCost w := by unfold unitCost; omega
  have := @unit_le_nc w
  calc e.size * NC + 1 ≤ 5 * NC + NC := by gcongr; omega
    _ = 6 * NC := by ring

/-- Phase 1: reading the input. -/
lemma good_phase1 (hw2 : 2 ≤ w) (hw : x.length + 3 < 2 ^ w) :
    Good x w (.seq (.rd 0) (.loop (.var 0) (.seq (.set 1 (.add (.var 1) (.const 1))) (.rd 0))))
      (NSt.zero 6 0) (st6 0 x.length 0 0 0 0 x.length []) ((x.length + 1) * (20 * NC)) := by
  have h1 : Good x w (.rd 0 : CStm 6 0) (NSt.zero 6 0) (st6 (inBit x 0) 0 0 0 0 0 (min 1 x.length) [])
      (unitCost w) := by
    refine (CStm.Good.rd 0).of_eq ?_ le_rfl
    refine NSt.ext (funext fun i => ?_) (funext fun i => i.elim0) rfl rfl
    fin_cases i <;> simp [NSt.zero, st6]
  have hS : ∀ j < x.length, Good x w (.seq (.set 1 (.add (.var 1) (.const 1))) (.rd 0) : CStm 6 0)
      (st6 (inBit x j) j 0 0 0 0 (min (j + 1) x.length) [])
      (st6 (inBit x (j + 1)) (j + 1) 0 0 0 0 (min (j + 1 + 1) x.length) []) (8 * NC) := by
    intro j hj
    have hf : (Ex.add (.var 1) (.const 1) : Ex 6).Fits w
        (st6 (inBit x j) j 0 0 0 0 (min (j + 1) x.length) []).env := by
      simp [Ex.Fits, st6, Ex.eval]
      omega
    refine ((CStm.Good.set hf).seq (CStm.Good.rd 0)).of_eq ?_ ?_
    · refine NSt.ext (funext fun i => ?_) rfl ?_ rfl
      · fin_cases i <;> simp [st6, Ex.eval, Function.update, show min (j + 1) x.length = j + 1 by omega]
      · simp [st6]; omega
    · simp only [Ex.size]
      have := @unit_le_nc w
      omega
  have hl := CStm.Good.loop_const (x := x) (w := w) (e := (.var 0 : Ex 6)) x.length
    (fun j => st6 (inBit x j) j 0 0 0 0 (min (j + 1) x.length) []) (8 * NC)
    (fun j hj => by simpa [st6, Ex.eval] using inBit_lt hj)
    (by simpa [st6, Ex.eval] using inBit_len x)
    (fun j hj => by
      have := inBit_le' x j
      simp [Ex.Fits, st6]; omega)
    hS
  refine (h1.seq (hl.of_eq ?_ le_rfl)).of_eq rfl ?_
  · simp [st6, inBit_len]
  · have := cond_le (w := w) (.var 0) (by simp [Ex.size])
    have := @unit_le_nc w
    have e : (x.length + 1) * (20 * NC) = x.length * (20 * NC) + 20 * NC := by ring
    have e2 : x.length * (8 * NC + condCost w (.var 0 : Ex 6)) ≤ x.length * (20 * NC) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

/-- Phase 2: `a = ⌈log₂ (n + 2)⌉` by doubling. -/
lemma good_phase2 (n : ℕ) (hw2 : 2 ≤ w) (hw : 4 * (n + 4) < 2 ^ w) :
    Good x w (.seq (.set 2 (.const 1)) (.loop (.lt (.var 2) (.add (.var 1) (.const 2)))
      (.seq (.set 2 (.add (.var 2) (.var 2))) (.set 3 (.add (.var 3) (.const 1))))))
      (st6 0 n 0 0 0 0 n []) (st6 0 n (2 ^ parA n) (parA n) 0 0 n [])
      ((parA n + 1) * (20 * NC)) := by
  have hA := pow_parA_le n
  have h1 : Good x w (.set 2 (.const 1) : CStm 6 0) (st6 0 n 0 0 0 0 n [])
      (st6 0 n (2 ^ 0) 0 0 0 n []) (2 * NC) := by
    refine (CStm.Good.set (by simp [Ex.Fits]; omega)).of_eq ?_ ?_
    · refine NSt.ext (funext fun i => ?_) rfl rfl rfl
      fin_cases i <;> simp [st6, Ex.eval]
    · simp only [Ex.size]; have := @unit_le_nc w; omega
  have hS : ∀ j < parA n, Good x w
      (.seq (.set 2 (.add (.var 2) (.var 2))) (.set 3 (.add (.var 3) (.const 1))) : CStm 6 0)
      (st6 0 n (2 ^ j) j 0 0 n []) (st6 0 n (2 ^ (j + 1)) (j + 1) 0 0 n []) (8 * NC) := by
    intro j hj
    have hj2 : 2 ^ (j + 1) ≤ 2 ^ parA n := Nat.pow_le_pow_right (by norm_num) hj
    have hja : j + 1 ≤ n + 2 := by have := parA_le n; omega
    rw [pow_succ] at hj2
    have hf1 : (Ex.add (.var 2) (.var 2) : Ex 6).Fits w (st6 0 n (2 ^ j) j 0 0 n []).env := by
      simp [Ex.Fits, st6, Ex.eval]; omega
    have hf2 : (Ex.add (.var 3) (.const 1) : Ex 6).Fits w
        ((st6 0 n (2 ^ j) j 0 0 n []).set 2 (2 ^ j + 2 ^ j)).env := by
      simp [Ex.Fits, st6, Ex.eval, Function.update]; omega
    refine ((CStm.Good.set hf1).seq (CStm.Good.set hf2)).of_eq ?_ ?_
    · refine NSt.ext (funext fun i => ?_) rfl rfl rfl
      fin_cases i <;> simp [st6, Ex.eval, Function.update, pow_succ] <;> ring
    · simp only [Ex.size]; have := @unit_le_nc w; omega
  have hl := CStm.Good.loop_const (x := x) (w := w)
    (e := (.lt (.var 2) (.add (.var 1) (.const 2)) : Ex 6)) (parA n)
    (fun j => st6 0 n (2 ^ j) j 0 0 n []) (8 * NC)
    (fun j hj => by simp [st6, Ex.eval, pow_lt_of_lt_parA hj])
    (by simp [st6, Ex.eval, not_lt.mpr (le_pow_parA n)])
    (fun j hj => by
      have : 2 ^ j ≤ 2 ^ parA n := Nat.pow_le_pow_right (by norm_num) hj
      simp [Ex.Fits, st6, Ex.eval]; omega)
    hS
  refine (h1.seq hl).mono ?_
  have := cond_le (w := w) (.lt (.var 2) (.add (.var 1) (.const 2))) (by simp [Ex.size])
  have e : (parA n + 1) * (20 * NC) = parA n * (20 * NC) + 20 * NC := by ring
  have e2 : parA n * (8 * NC + condCost w (.lt (.var 2) (.add (.var 1) (.const 2)) : Ex 6)) ≤
      parA n * (20 * NC) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Phase 3: `s` by repeated addition. -/
lemma good_phase3 (c₀ n : ℕ) (hw2 : 2 ≤ w) (hw : 4 * (n + c₀ + 4) < 2 ^ w) :
    Good x w (.loop (.lt (.var 4) (.add (.var 1) (.const (c₀ + 2))))
      (.seq (.set 4 (.add (.var 4) (.var 3))) (.set 5 (.add (.var 5) (.const 1)))))
      (st6 0 n (2 ^ parA n) (parA n) (0 * parA n) 0 n [])
      (st6 0 n (2 ^ parA n) (parA n) (parS c₀ n * parA n) (parS c₀ n) n [])
      ((parS c₀ n + 1) * (20 * NC)) := by
  obtain ⟨hs1, hs2⟩ := parS_spec c₀ n
  have ha := parA_le n
  have hsa : parS c₀ n * parA n ≤ n + c₀ + 2 + parA n := by
    have := hs2 (parS c₀ n - 1) (by have := one_le_parS c₀ n; omega)
    have e : parS c₀ n * parA n = (parS c₀ n - 1) * parA n + parA n := by
      have : 1 ≤ parS c₀ n := one_le_parS c₀ n
      obtain ⟨k, hk⟩ : ∃ k, parS c₀ n = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos this).symm⟩
      rw [hk]; simp; ring
    omega
  have hsle : parS c₀ n ≤ n + c₀ + 2 := by
    have := hs2 (parS c₀ n - 1) (by have := one_le_parS c₀ n; omega)
    have h1 := one_le_parA n
    have : parS c₀ n - 1 ≤ (parS c₀ n - 1) * parA n := Nat.le_mul_of_pos_right _ h1
    omega
  have hS : ∀ j < parS c₀ n, Good x w
      (.seq (.set 4 (.add (.var 4) (.var 3))) (.set 5 (.add (.var 5) (.const 1))) : CStm 6 0)
      (st6 0 n (2 ^ parA n) (parA n) (j * parA n) j n [])
      (st6 0 n (2 ^ parA n) (parA n) ((j + 1) * parA n) (j + 1) n []) (8 * NC) := by
    intro j hj
    have hj' := hs2 j hj
    have hf1 : (Ex.add (.var 4) (.var 3) : Ex 6).Fits w
        (st6 0 n (2 ^ parA n) (parA n) (j * parA n) j n []).env := by
      simp [Ex.Fits, st6, Ex.eval]; omega
    have hf2 : (Ex.add (.var 5) (.const 1) : Ex 6).Fits w
        ((st6 0 n (2 ^ parA n) (parA n) (j * parA n) j n []).set 4
          (j * parA n + parA n)).env := by
      simp [Ex.Fits, st6, Ex.eval, Function.update]; omega
    refine ((CStm.Good.set hf1).seq (CStm.Good.set hf2)).of_eq ?_ ?_
    · refine NSt.ext (funext fun i => ?_) rfl rfl rfl
      fin_cases i <;> simp [st6, Ex.eval, Function.update] <;> ring
    · simp only [Ex.size]; have := @unit_le_nc w; omega
  have hl := CStm.Good.loop_const (x := x) (w := w)
    (e := (Ex.lt (.var 4) (.add (.var 1) (.const (c₀ + 2))))) (parS c₀ n)
    (fun j => st6 0 n (2 ^ parA n) (parA n) (j * parA n) j n []) (8 * NC)
    (fun j hj => by
      have := hs2 j hj
      simp [st6, Ex.eval, show j * parA n < n + (c₀ + 2) by omega])
    (by simp [st6, Ex.eval, not_lt.mpr (show n + (c₀ + 2) ≤ parS c₀ n * parA n by omega)])
    (fun j hj => by
      have : j * parA n ≤ parS c₀ n * parA n := Nat.mul_le_mul_right _ hj
      simp [Ex.Fits, st6, Ex.eval]; omega)
    hS
  refine hl.mono ?_
  have := cond_le (w := w) (.lt (.var 4) (.add (.var 1) (.const (c₀ + 2)))) (by simp [Ex.size])
  have e : (parS c₀ n + 1) * (20 * NC) = parS c₀ n * (20 * NC) + 20 * NC := by ring
  have e2 : parS c₀ n * (8 * NC +
      condCost w (Ex.lt (.var 4) (.add (.var 1) (.const (c₀ + 2))))) ≤
      parS c₀ n * (20 * NC) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Phase 4: the output. -/
lemma good_phase4 (c₀ n p a c s : ℕ) (hw : n + c₀ + s < 2 ^ w) :
    Good x w (.seq (.emit (.add (.var 1) (.const c₀))) (.emit (.var 5)) : CStm 6 0)
      (st6 0 n p a c s n []) (st6 0 n p a c s n [n + c₀, s]) (8 * NC) := by
  refine ((CStm.Good.emit (by simp [Ex.Fits, st6, Ex.eval]; omega)).seq
    (CStm.Good.emit (by simp [Ex.Fits, st6]; omega))).of_eq ?_ ?_
  · simp [st6, Ex.eval]
  · simp only [Ex.size]; have := @unit_le_nc w; omega

/-- **The program.** -/
lemma good_parProg (c₀ : ℕ) (hw2 : 2 ≤ w) (hw : 4 * (x.length + c₀ + 4) < 2 ^ w) :
    Good x w (parProg c₀) (NSt.zero 6 0)
      (st6 0 x.length (2 ^ parA x.length) (parA x.length) (parS c₀ x.length * parA x.length)
        (parS c₀ x.length) x.length [x.length + c₀, parS c₀ x.length])
      (100 * (x.length + c₀ + 4) * NC) := by
  have h1 := good_phase1 (x := x) hw2 (by omega)
  have h2 := good_phase2 (x := x) x.length hw2 (by omega)
  have h3 := good_phase3 (x := x) c₀ x.length hw2 hw
  have hsle : parS c₀ x.length ≤ x.length + c₀ + 2 := by
    obtain ⟨-, hs2⟩ := parS_spec c₀ x.length
    have := hs2 (parS c₀ x.length - 1)
      (by have := one_le_parS c₀ x.length; omega)
    have h1 := one_le_parA x.length
    have : parS c₀ x.length - 1 ≤ (parS c₀ x.length - 1) * parA x.length :=
      Nat.le_mul_of_pos_right _ h1
    omega
  have h4 := good_phase4 (x := x) (w := w) c₀ x.length (2 ^ parA x.length) (parA x.length)
    (parS c₀ x.length * parA x.length) (parS c₀ x.length) (by omega)
  rw [show (st6 0 x.length (2 ^ parA x.length) (parA x.length) 0 0 x.length [] : NSt 6 0) =
    st6 0 x.length (2 ^ parA x.length) (parA x.length) (0 * parA x.length) 0 x.length [] by
      simp] at h2
  refine (h1.seq (h2.seq (h3.seq h4))).mono ?_
  have ha := parA_le x.length
  have e1 : (x.length + 1) * (20 * NC) + ((parA x.length + 1) * (20 * NC) +
      ((parS c₀ x.length + 1) * (20 * NC) + 8 * NC)) =
      (x.length + parA x.length + parS c₀ x.length + 3) * (20 * NC) + 8 * NC := by ring
  have e2 : (x.length + parA x.length + parS c₀ x.length + 3) * (20 * NC) ≤
      (3 * (x.length + c₀ + 4)) * (20 * NC) := Nat.mul_le_mul_right _ (by omega)
  have e3 : 100 * (x.length + c₀ + 4) * NC = (3 * (x.length + c₀ + 4)) * (20 * NC) +
      (40 * (x.length + c₀ + 4)) * NC := by ring
  have e4 : 8 * NC ≤ (40 * (x.length + c₀ + 4)) * NC := Nat.mul_le_mul_right _ (by omega)
  omega

end Good

end Lax119563Proofs.Hardness
