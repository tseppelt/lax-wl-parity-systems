import Lax119563Proofs.Computability.PreMachine
import Lax119563Proofs.Hardness.PrefixProgram

/-!
# Computing the parameters of the XP reduction

For machines `Mκ` (computing a parameter `k` from the input) and `Mf` (computing a function
`F`), the structured statement `xpS Mκ Mf` reads its input `y` with `n = |y|`, computes
`k` and `F k` (`paramS`), then `a = ⌈log₂ (n + 2)⌉` (`parA n`) by doubling and
`h = F k · a` by repeated addition, and emits `[h, F k + 1]`. Its machine computes
`encodeNats [F k · a, F k + 1]` from `y` within `K · g(k)^3 · (n + 1)^(3 (d + 1) + 1)` steps
(`xp_prog`), where `C (n + 1)^d` bounds the running time of `Mκ` and `g` is a computable
function of `k` (`xpG`).

States in the layout of `paramS` with nine extra registers are described by a base state and
the values of the extra registers (`stV`).
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime Lax119563Proofs.Reduction
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

open Compiler Compiler.CStm Computability

variable {C : ℕ}

/-! ## States with nine extra registers -/

/-- The state with base `b` (for the registers below `C` and the stacks) and the values `v`
of the nine extra registers. -/
def stV (b : NSt (C + 9) C) (v : Fin 9 → ℕ) (pos : ℕ) (out : List ℕ) : NSt (C + 9) C :=
  ⟨fun r => if h : C ≤ r.val then v ⟨r.val - C, by omega⟩ else b.env r, b.stk, pos, out⟩

section StV

variable (b : NSt (C + 9) C) (v : Fin 9 → ℕ) (pos : ℕ) (out : List ℕ)

@[simp] lemma stV_ex (i : Fin 9) : (stV b v pos out).env (ex C 9 i) = v i := by
  simp [stV, ex]

lemma stV_set (i : Fin 9) (u : ℕ) :
    (stV b v pos out).set (ex C 9 i) u = stV b (Function.update v i u) pos out := by
  refine NSt.ext (funext fun r => ?_) rfl rfl rfl
  simp only [NSt.set_env, stV]
  by_cases hr : r = ex C 9 i
  · subst hr; simp [ex]
  · rw [Function.update_of_ne hr]
    split_ifs with h
    · have : (⟨r.val - C, by omega⟩ : Fin 9) ≠ i := fun e => hr (by
        ext; simp only [ex, ← e]; omega)
      rw [Function.update_of_ne this]
    · rfl

@[simp] lemma stV_pos' (p : ℕ) : { stV b v pos out with pos := p } = stV b v p out := rfl

@[simp] lemma stV_out' (o : List ℕ) : { stV b v pos out with out := o } = stV b v pos o := rfl

@[simp] lemma stV_pos : (stV b v pos out).pos = pos := rfl
@[simp] lemma stV_outF : (stV b v pos out).out = out := rfl
@[simp] lemma stV_stk : (stV b v pos out).stk = b.stk := rfl

end StV

/-! ## The statement -/

/-- Shorthand for the extra registers. -/
abbrev xr (C : ℕ) (i : Fin 9) : Fin (C + 9) := ex C 9 i

/-- After `paramS`: count the input, compute `a = parA n`, `h = F · a`, and emit `[h, F + 1]`. -/
def tailS (C : ℕ) : CStm (C + 9) C :=
  seqL [.rst, .rd (xr C 3),
    .loop (.var (xr C 3)) (.seq (.set (xr C 4) (.add (.var (xr C 4)) (.const 1))) (.rd (xr C 3))),
    .set (xr C 5) (.const 1),
    .loop (.lt (.var (xr C 5)) (.add (.var (xr C 4)) (.const 2)))
      (.seq (.set (xr C 5) (.add (.var (xr C 5)) (.var (xr C 5))))
        (.set (xr C 6) (.add (.var (xr C 6)) (.const 1)))),
    .loop (.lt (.var (xr C 8)) (.var (xr C 1)))
      (.seq (.set (xr C 7) (.add (.var (xr C 7)) (.var (xr C 6))))
        (.set (xr C 8) (.add (.var (xr C 8)) (.const 1)))),
    .emit (.var (xr C 7)), .emit (.add (.var (xr C 1)) (.const 1))]

/-- The statement of the XP reduction. -/
noncomputable def xpS (Mκ Mf : Machine) : CStm (need Mκ + need Mf + 9) (need Mκ + need Mf) :=
  .seq (paramS Mκ Mf (need Mκ + need Mf) 9 (by omega) (by omega) (by omega))
    (tailS (need Mκ + need Mf))

/-! ## The tail -/

section Tail

variable {x : List Bool} {w : ℕ}

local notation "NC" => Ex.nodeCost w

lemma unit_le_nc' : unitCost w ≤ NC := Ex.unitCost_le_nodeCost w

lemma cond_le' {R : ℕ} (e : Ex R) (hs : e.size ≤ 5) : condCost w e ≤ 6 * NC := by
  unfold condCost
  have : 1 ≤ unitCost w := by unfold unitCost; omega
  have := @unit_le_nc' w
  calc e.size * NC + 1 ≤ 5 * NC + NC := by gcongr; omega
    _ = 6 * NC := by ring

variable (b : NSt (C + 9) C) (k F t : ℕ)

/-- Phase 1: counting the input. -/
lemma tail_phase1 (hw2 : 2 ≤ w) (hw : x.length + 3 < 2 ^ w) :
    Good x w (.loop (.var (xr C 3))
        (.seq (.set (xr C 4) (.add (.var (xr C 4)) (.const 1))) (.rd (xr C 3))) :
        CStm (C + 9) C)
      (stV b ![k, F, t, inBit x 0, 0, 0, 0, 0, 0] (min (0 + 1) x.length) [])
      (stV b ![k, F, t, 0, x.length, 0, 0, 0, 0] x.length [])
      (x.length * (20 * NC) + 6 * NC) := by
  have hS : ∀ j < x.length, Good x w
      (.seq (.set (xr C 4) (.add (.var (xr C 4)) (.const 1))) (.rd (xr C 3)) : CStm (C + 9) C)
      (stV b ![k, F, t, inBit x j, j, 0, 0, 0, 0] (min (j + 1) x.length) [])
      (stV b ![k, F, t, inBit x (j + 1), j + 1, 0, 0, 0, 0] (min (j + 1 + 1) x.length) [])
      (8 * NC) := by
    intro j hj
    have hf : (Ex.add (.var (xr C 4)) (.const 1) : Ex (C + 9)).Fits w
        (stV b ![k, F, t, inBit x j, j, 0, 0, 0, 0] (min (j + 1) x.length) []).env := by
      simp only [Ex.Fits, Ex.eval, xr, stV_ex]
      simp
      omega
    refine ((Good.set hf).seq (Good.rd _)).of_eq ?_ ?_
    · rw [stV_set, stV_set]
      simp only [stV_pos', stV_pos, Ex.eval, stV_ex, show min (j + 1) x.length = j + 1 by omega]
      congr 1; funext i; fin_cases i <;> rfl
    · simp only [Ex.size]
      have := @unit_le_nc' w
      omega
  have hl := Good.loop_const (x := x) (w := w) (e := (.var (xr C 3) : Ex (C + 9))) x.length
    (fun j => stV b ![k, F, t, inBit x j, j, 0, 0, 0, 0] (min (j + 1) x.length) []) (8 * NC)
    (fun j hj => by simpa [Ex.eval] using inBit_lt hj)
    (by simpa [Ex.eval] using inBit_len x)
    (fun j hj => by
      have := inBit_le' x j
      simp [Ex.Fits]; omega)
    hS
  refine hl.of_eq ?_ ?_
  · simp only [inBit_len]
    congr 1; omega
  · have := cond_le' (w := w) (.var (xr C 3)) (by simp [Ex.size])
    have e2 : x.length * (8 * NC + condCost w (.var (xr C 3) : Ex (C + 9))) ≤
        x.length * (20 * NC) := Nat.mul_le_mul_left _ (by omega)
    omega

/-- Phase 2: `a = ⌈log₂ (n + 2)⌉` by doubling. -/
lemma tail_phase2 (hw2 : 2 ≤ w) (n : ℕ) (hw : 4 * (n + 4) < 2 ^ w) :
    Good x w (.loop (.lt (.var (xr C 5)) (.add (.var (xr C 4)) (.const 2)))
      (.seq (.set (xr C 5) (.add (.var (xr C 5)) (.var (xr C 5))))
        (.set (xr C 6) (.add (.var (xr C 6)) (.const 1)))) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, n, 2 ^ 0, 0, 0, 0] n [])
      (stV b ![k, F, t, 0, n, 2 ^ parA n, parA n, 0, 0] n [])
      (parA n * (20 * NC) + 6 * NC) := by
  have hA := pow_parA_le n
  have hS : ∀ j < parA n, Good x w
      (.seq (.set (xr C 5) (.add (.var (xr C 5)) (.var (xr C 5))))
        (.set (xr C 6) (.add (.var (xr C 6)) (.const 1))) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, n, 2 ^ j, j, 0, 0] n [])
      (stV b ![k, F, t, 0, n, 2 ^ (j + 1), j + 1, 0, 0] n []) (8 * NC) := by
    intro j hj
    have hj2 : 2 ^ (j + 1) ≤ 2 ^ parA n := Nat.pow_le_pow_right (by norm_num) hj
    have hja : j + 1 ≤ n + 2 := by have := parA_le n; omega
    rw [pow_succ] at hj2
    have hf1 : (Ex.add (.var (xr C 5)) (.var (xr C 5)) : Ex (C + 9)).Fits w
        (stV b ![k, F, t, 0, n, 2 ^ j, j, 0, 0] n []).env := by
      simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp; omega
    refine ((Good.set hf1).seq (Good.set ?_)).of_eq ?_ ?_
    · rw [stV_set]; simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp [Function.update_apply]
      omega
    · rw [stV_set, stV_set]
      simp only [Ex.eval, xr, stV_ex]
      rw [show 2 ^ (j + 1) = 2 ^ j + 2 ^ j by ring]
      congr 1; funext i; fin_cases i <;> rfl
    · simp only [Ex.size]; have := @unit_le_nc' w; omega
  have hl := Good.loop_const (x := x) (w := w)
    (e := (.lt (.var (xr C 5)) (.add (.var (xr C 4)) (.const 2)) : Ex (C + 9))) (parA n)
    (fun j => stV b ![k, F, t, 0, n, 2 ^ j, j, 0, 0] n []) (8 * NC)
    (fun j hj => by simp [Ex.eval, pow_lt_of_lt_parA hj])
    (by simp [Ex.eval, not_lt.mpr (le_pow_parA n)])
    (fun j hj => by
      have : 2 ^ j ≤ 2 ^ parA n := Nat.pow_le_pow_right (by norm_num) hj
      simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp; omega)
    hS
  refine hl.mono ?_
  have := cond_le' (w := w) (.lt (.var (xr C 5)) (.add (.var (xr C 4)) (.const 2)) : Ex (C + 9))
    (by simp [Ex.size])
  have e2 : parA n * (8 * NC + condCost w
      (.lt (.var (xr C 5)) (.add (.var (xr C 4)) (.const 2)) : Ex (C + 9))) ≤
      parA n * (20 * NC) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Phase 3: `h = F · a` by repeated addition. -/
lemma tail_phase3 (hw2 : 2 ≤ w) (n a : ℕ) (ha : a ≤ n + 2) (p : ℕ)
    (hw : 4 * ((F + 1) * (n + 4)) < 2 ^ w) :
    Good x w (.loop (.lt (.var (xr C 8)) (.var (xr C 1)))
      (.seq (.set (xr C 7) (.add (.var (xr C 7)) (.var (xr C 6))))
        (.set (xr C 8) (.add (.var (xr C 8)) (.const 1)))) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, n, p, a, 0 * a, 0] n [])
      (stV b ![k, F, t, 0, n, p, a, F * a, F] n [])
      (F * (20 * NC) + 6 * NC) := by
  have hFa : F * a ≤ F * (n + 2) := Nat.mul_le_mul_left _ ha
  have e1 : (F + 1) * (n + 4) = F * (n + 2) + 2 * F + n + 4 := by ring
  have hS : ∀ j < F, Good x w
      (.seq (.set (xr C 7) (.add (.var (xr C 7)) (.var (xr C 6))))
        (.set (xr C 8) (.add (.var (xr C 8)) (.const 1))) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, n, p, a, j * a, j] n [])
      (stV b ![k, F, t, 0, n, p, a, (j + 1) * a, j + 1] n []) (8 * NC) := by
    intro j hj
    have hja : (j + 1) * a ≤ F * a := Nat.mul_le_mul_right _ hj
    have e2 : (j + 1) * a = j * a + a := by ring
    have hf1 : (Ex.add (.var (xr C 7)) (.var (xr C 6)) : Ex (C + 9)).Fits w
        (stV b ![k, F, t, 0, n, p, a, j * a, j] n []).env := by
      simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp; omega
    refine ((Good.set hf1).seq (Good.set ?_)).of_eq ?_ ?_
    · rw [stV_set]; simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp [Function.update_apply]
      omega
    · rw [stV_set, stV_set]
      simp only [Ex.eval, xr, stV_ex]
      rw [e2]
      congr 1; funext i; fin_cases i <;> rfl
    · simp only [Ex.size]; have := @unit_le_nc' w; omega
  have hl := Good.loop_const (x := x) (w := w)
    (e := (.lt (.var (xr C 8)) (.var (xr C 1)) : Ex (C + 9))) F
    (fun j => stV b ![k, F, t, 0, n, p, a, j * a, j] n []) (8 * NC)
    (fun j hj => by simp [Ex.eval, hj])
    (by simp [Ex.eval])
    (fun j hj => by simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp; omega)
    hS
  refine hl.mono ?_
  have := cond_le' (w := w) (.lt (.var (xr C 8)) (.var (xr C 1)) : Ex (C + 9))
    (by simp [Ex.size])
  have e2 : F * (8 * NC + condCost w (.lt (.var (xr C 8)) (.var (xr C 1)) : Ex (C + 9))) ≤
      F * (20 * NC) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- **The tail.** -/
lemma tail_good (hw2 : 2 ≤ w) (hw : 4 * ((F + 1) * (x.length + 4)) < 2 ^ w) :
    Good x w (tailS C) (stV b ![k, F, t, 0, 0, 0, 0, 0, 0] x.length [])
      (stV b ![k, F, t, 0, x.length, 2 ^ parA x.length, parA x.length, F * parA x.length, F]
        x.length [F * parA x.length, F + 1])
      (30 * (x.length + parA x.length + F + 1) * NC) := by
  have hn4 : x.length + 4 ≤ (F + 1) * (x.length + 4) := Nat.le_mul_of_pos_left _ (by omega)
  have hFn : F + 1 ≤ (F + 1) * (x.length + 4) := Nat.le_mul_of_pos_right _ (by omega)
  have ha := parA_le x.length
  have hA := pow_parA_le x.length
  have hFa : F * parA x.length ≤ (F + 1) * (x.length + 4) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hU := @unit_le_nc' w
  have g0 := Good.rst (x := x) (w := w) (st := stV b ![k, F, t, 0, 0, 0, 0, 0, 0] x.length [])
  simp only [stV_pos', stV_pos] at g0
  have g1 : Good x w (.rd (xr C 3) : CStm (C + 9) C) (stV b ![k, F, t, 0, 0, 0, 0, 0, 0] 0 [])
      (stV b ![k, F, t, inBit x 0, 0, 0, 0, 0, 0] (min (0 + 1) x.length) []) (unitCost w) := by
    refine (Good.rd _).of_eq ?_ le_rfl
    rw [stV_set]; simp only [stV_pos', stV_pos]
    congr 1; funext i; fin_cases i <;> rfl
  have g2 := tail_phase1 (x := x) (w := w) b k F t hw2 (by omega)
  have g3 : Good x w (.set (xr C 5) (.const 1) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, x.length, 0, 0, 0, 0] x.length [])
      (stV b ![k, F, t, 0, x.length, 2 ^ 0, 0, 0, 0] x.length []) (2 * NC) := by
    refine (Good.set (by simp only [Ex.Fits]; omega)).of_eq ?_ (by simp only [Ex.size]; omega)
    rw [stV_set]; simp only [Ex.eval]
    congr 1; funext i; fin_cases i <;> rfl
  have g4 := tail_phase2 (x := x) (w := w) b k F t hw2 x.length (by omega)
  have g5 := tail_phase3 (x := x) (w := w) b k F t hw2 x.length (parA x.length) ha
    (2 ^ parA x.length) hw
  rw [zero_mul] at g5
  have g6 : Good x w (.emit (.var (xr C 7)) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, x.length, 2 ^ parA x.length, parA x.length, F * parA x.length, F]
        x.length [])
      (stV b ![k, F, t, 0, x.length, 2 ^ parA x.length, parA x.length, F * parA x.length, F]
        x.length [F * parA x.length]) (2 * NC) := by
    refine (Good.emit ?_).of_eq ?_ (by simp only [Ex.size]; omega)
    · simp only [Ex.Fits, xr, stV_ex]; simp; omega
    · simp only [Ex.eval, xr, stV_ex, stV_out', stV_outF]; simp
  have g7 : Good x w (.emit (.add (.var (xr C 1)) (.const 1)) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, x.length, 2 ^ parA x.length, parA x.length, F * parA x.length, F]
        x.length [F * parA x.length])
      (stV b ![k, F, t, 0, x.length, 2 ^ parA x.length, parA x.length, F * parA x.length, F]
        x.length [F * parA x.length, F + 1]) (4 * NC) := by
    refine (Good.emit ?_).of_eq ?_ (by simp only [Ex.size]; omega)
    · simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp; omega
    · simp only [Ex.eval, xr, stV_ex, stV_out', stV_outF]; simp
  refine (g0.seq (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq (g7.seq
    Good.skip)))))))).mono ?_
  have e : 30 * (x.length + parA x.length + F + 1) * NC =
      30 * (x.length * NC) + 30 * (parA x.length * NC) + 30 * (F * NC) + 30 * NC := by ring
  have e1 : unitCost w * (x.length + 1) ≤ NC * (x.length + 1) := Nat.mul_le_mul_right _ hU
  have e2 : NC * (x.length + 1) = x.length * NC + NC := by ring
  have e3 : x.length * (20 * NC) = 20 * (x.length * NC) := by ring
  have e4 : parA x.length * (20 * NC) = 20 * (parA x.length * NC) := by ring
  have e5 : F * (20 * NC) = 20 * (F * NC) := by ring
  omega

end Tail

end Lax119563Proofs.Hardness
