import Lax119563Proofs.Computability.Param
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
open Lax119563Proofs.Computability Lax119563Proofs.Compiler Lax119563Proofs.Compiler.CStm

namespace Lax119563Proofs.Hardness

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
    · rw [stV_set]; simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp
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
    · rw [stV_set]; simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp
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
    (fun j hj => by simp only [Ex.Fits, xr, stV_ex]; simp; omega)
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

/-! ## The whole statement -/

lemma length_encodeNat_le' (m : ℕ) : (encodeNat m).length ≤ 2 * m + 1 := by
  have h1 : (Nat.bits m).length ≤ m := by
    rw [Nat.size_eq_bits_len, Nat.size_le]; exact Nat.lt_two_pow_self
  simp [encodeNat]; omega

/-- The arithmetic of the time bound. -/
lemma xp_arith {Kκ Kf N X P g a sκ kk sf m n L A B : ℕ} (hX : 1 ≤ X) (hP : 1 ≤ P)
    (hg : 1 ≤ g) (hN1 : 1 ≤ N) (hN : N ≤ 64 * g ^ 2 * P ^ 2)
    (h1 : a + sκ + 1 ≤ 3 * g * P * X) (h2 : kk + sf + 1 ≤ 2 * g) (h3 : m ≤ 4 * (g * X))
    (h4 : n + L ≤ 11 * (g * X))
    (hA : A ≤ Kκ * (a + sκ + 1) * N) (hB : B ≤ Kf * (kk + sf + 1) * N) :
    A + B + 9 * N + 30 * m * N + (20 * (n + L) + 10) ≤
      64 * (3 * Kκ + 2 * Kf + 360) * g ^ 3 * (P ^ 3 * X) := by
  have hPX : 1 ≤ P * X := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hgX : 1 ≤ g * X := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set Z := g * P * X * N with hZ
  have eA : A ≤ 3 * Kκ * Z := by
    calc A ≤ Kκ * (a + sκ + 1) * N := hA
      _ ≤ Kκ * (3 * g * P * X) * N := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
      _ = 3 * Kκ * Z := by rw [hZ]; ring
  have eB : B ≤ 2 * Kf * Z := by
    calc B ≤ Kf * (kk + sf + 1) * N := hB
      _ ≤ Kf * (2 * g) * N := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
      _ ≤ Kf * (2 * g * (P * X)) * N :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hPX))
      _ = 2 * Kf * Z := by rw [hZ]; ring
  have eG : g * X * N ≤ Z := by
    rw [hZ]
    calc g * X * N = g * 1 * X * N := by ring
      _ ≤ g * P * X * N :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hP))
  have eN : N ≤ g * X * N := Nat.le_mul_of_pos_left _ hgX
  have eM : 30 * m * N ≤ 120 * (g * X * N) := by
    calc 30 * m * N ≤ 30 * (4 * (g * X)) * N :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
      _ = 120 * (g * X * N) := by ring
  have eL : g * X ≤ g * X * N := Nat.le_mul_of_pos_right _ hN1
  have hZ' : Z ≤ g * P * X * (64 * g ^ 2 * P ^ 2) := by
    rw [hZ]; exact Nat.mul_le_mul_left _ hN
  have e : (3 * Kκ + 2 * Kf + 360) * Z = 3 * Kκ * Z + 2 * Kf * Z + 360 * Z := by ring
  calc _ ≤ (3 * Kκ + 2 * Kf + 360) * Z := by omega
    _ ≤ (3 * Kκ + 2 * Kf + 360) * (g * P * X * (64 * g ^ 2 * P ^ 2)) :=
        Nat.mul_le_mul_left _ hZ'
    _ = 64 * (3 * Kκ + 2 * Kf + 360) * g ^ 3 * (P ^ 3 * X) := by ring

/-- The computable function of the parameter in the time bound. -/
noncomputable def xpG (Mκ Mf : Machine) (F : ℕ → ℕ) (Cκ k : ℕ) : ℕ :=
  5 + simB Mκ + simB Mf + k + F k + haltTime Mf (encodeNat k) + 2 * Cκ + 16 * (F k + 1)

/-- The constant of the time bound. -/
noncomputable def xpK (Mκ Mf : Machine) : ℕ := 64 * (3 * simK Mκ + 2 * simK Mf + 360)

/-- **The machine of the statement.** If `Mκ` computes `k` from `y` within `Cκ (|y| + 1)^d`
steps, the machine of `xpS Mκ Mf` computes `encodeNats [F k · parA |y|, F k + 1]` from `y`. -/
theorem xp_prog (Mκ Mf : Machine) {F : ℕ → ℕ}
    (hMf : ∀ k, ComputesWithin Mf (encodeNat k) (encodeNat (F k)) (haltTime Mf (encodeNat k)))
    {Cκ d : ℕ} {y : List Bool} {k : ℕ}
    (hκ : ComputesWithin Mκ y (encodeNat k) (Cκ * (y.length + 1) ^ d)) :
    ComputesWithin ((xpS Mκ Mf).machine (xpS Mκ Mf).depth) y
      (encodeNats [F k * parA y.length, F k + 1])
      (xpK Mκ Mf * xpG Mκ Mf F Cκ k ^ 3 * (y.length + 1) ^ (3 * (d + 1) + 1)) := by
  set n := y.length with hn
  set X := n + 1 with hX
  set Pw := X ^ (d + 1) with hPw
  have hPw1 : 1 ≤ Pw := Nat.one_le_pow _ _ (by omega)
  have hXPw : X ≤ Pw := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ Pw := Nat.pow_le_pow_right (by omega) (by omega)
  have hXd : X ^ d ≤ Pw := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨ht, hht⟩ : ∃ ht, haltTime Mf (encodeNat k) = ht := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, xpG Mκ Mf F Cκ k = g := ⟨_, rfl⟩
  have hgk : g = 5 + simB Mκ + simB Mf + k + F k + ht + 2 * Cκ + 16 * (F k + 1) := by
    rw [← hg, ← hht]; rfl
  rw [hg]
  obtain ⟨w, hwdef⟩ : ∃ w, w = 2 + simB Mκ + simB Mf + k + F k + ht + Cκ + Cκ * Pw +
    4 * ((F k + 1) * (n + 4)) := ⟨_, rfl⟩
  have hw : 2 ≤ w := by omega
  have hsκ : haltTime Mκ y ≤ Cκ * Pw := by
    refine (haltTime_le_of_computesWithin hκ).trans ?_
    exact Nat.mul_le_mul_left _ hXd
  have hlt : ∀ v, v ≤ w → v < 2 ^ w := fun v hv => lt_two_pow_of_le hv
  obtain ⟨st5, g5, e5k, e5v, e5t, e5x, -, -, e5p, e5o⟩ := paramS_good (x := y) (w := w)
    (C := need Mκ + need Mf) (E := 9) (by omega) (by omega) (by omega) hw
    (hlt _ (by omega)).le (hlt _ (by omega)).le (NSt.zero _ _) (bdd_zero _ _ _)
    (by simp [NSt.zero]) (fun q => by simp [NSt.zero]) hκ (hMf k) (hlt _ (by omega))
    (by have := bits_length_le k; omega) (hlt _ (by omega)) (hlt _ (by omega))
    (by have := bits_length_le (F k); omega) (hlt _ (by omega))
  have hv : ∀ i : Fin 9, st5.env (ex _ 9 i) = ![k, F k, ht, 0, 0, 0, 0, 0, 0] i := by
    intro i
    fin_cases i
    · exact e5k
    · exact e5v
    · exact e5t.trans hht
    all_goals (rw [e5x _ (by simp)]; rfl)
  have hst : st5 = stV st5 ![k, F k, ht, 0, 0, 0, 0, 0, 0] n [] := by
    refine NSt.ext (funext fun r => ?_) rfl e5p (by rw [e5o]; rfl)
    simp only [stV]
    split_ifs with h
    · rw [← hv]; congr 1; ext; simp [ex]; omega
    · rfl
  have hW : 4 * ((F k + 1) * (y.length + 4)) ≤ w := by rw [← hn]; omega
  have gt := tail_good (x := y) (w := w) st5 k (F k) ht hw (hlt _ hW)
  rw [← hst] at gt
  have gg : Good y w (xpS Mκ Mf) _ _ _ := g5.seq gt
  have hc := CStm.computesWithin (D := (xpS Mκ Mf).depth) hw le_rfl gg.1
  rw [gg.2.1] at hc
  simp only [stV_outF] at hc
  refine Lax119563Proofs.Reduction.ComputesWithin.mono hc ?_
  have hcost := gg.2.2
  rw [hht] at hcost
  -- the arithmetic
  have hN := Ex.unitCost_le_nodeCost w
  have hN1 : 1 ≤ Ex.nodeCost w := by have := unitCost_ge w; omega
  have hNw : Ex.nodeCost w ≤ 64 * g ^ 2 * Pw ^ 2 := by
    have hw3 : w + 3 ≤ g * Pw := by
      have h0 : (5 + simB Mκ + simB Mf + k + F k + ht + Cκ) ≤
          (5 + simB Mκ + simB Mf + k + F k + ht + Cκ) * Pw := Nat.le_mul_of_pos_right _ hPw1
      have h4 : 4 * ((F k + 1) * (n + 4)) ≤ 16 * (F k + 1) * Pw := by
        have : n + 4 ≤ 4 * Pw := by omega
        calc 4 * ((F k + 1) * (n + 4)) ≤ 4 * ((F k + 1) * (4 * Pw)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
          _ = 16 * (F k + 1) * Pw := by ring
      have h1 : g * Pw = (5 + simB Mκ + simB Mf + k + F k + ht + Cκ) * Pw + Cκ * Pw +
          16 * (F k + 1) * Pw := by rw [hgk]; ring
      omega
    have : Ex.nodeCost w ≤ 64 * (w + 3) ^ 2 := by
      have e : 64 * (w + 3) ^ 2 = (w + 3) * (64 * (w + 3)) := by ring
      rw [e]; simp only [Ex.nodeCost, unitCost]
      exact Nat.mul_le_mul_left _ (by omega)
    calc Ex.nodeCost w ≤ 64 * (w + 3) ^ 2 := this
      _ ≤ 64 * (g * Pw) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw3 2)
      _ = 64 * g ^ 2 * Pw ^ 2 := by ring
  have hg1 : 1 ≤ g := by rw [hgk]; omega
  have h1 : n + haltTime Mκ y + 1 ≤ 3 * g * Pw * X := by
    rw [show 3 * g * Pw * X = 3 * (g * Pw * X) by ring]
    have a1 : X ≤ g * Pw * X := by
      calc X = 1 * 1 * X := by ring
        _ ≤ g * Pw * X := Nat.mul_le_mul_right _ (Nat.mul_le_mul hg1 hPw1)
    have a2 : Cκ * Pw ≤ g * Pw * X := by
      calc Cκ * Pw = Cκ * Pw * 1 := by ring
        _ ≤ g * Pw * X := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by rw [hgk]; omega))
            (by omega)
    omega
  have h2 : (encodeNat k).length + ht + 1 ≤ 2 * g := by
    have := bits_length_le k
    rw [length_encodeNat, hgk]; omega
  have ha := parA_le n
  have hFX : F k + 1 ≤ g * X := by
    calc F k + 1 ≤ g := by rw [hgk]; omega
      _ ≤ g * X := Nat.le_mul_of_pos_right _ (by omega)
  have hnX : n + 1 ≤ g * X := by
    calc n + 1 = 1 * X := by omega
      _ ≤ g * X := Nat.mul_le_mul_right _ hg1
  have h3 : n + parA n + F k + 1 ≤ 4 * (g * X) := by omega
  have h4 : n + (encodeNats [F k * parA n, F k + 1]).length ≤ 11 * (g * X) := by
    have l1 := length_encodeNat_le' (F k * parA n)
    have l2 := length_encodeNat_le' (F k + 1)
    have hFa : F k * parA n ≤ (F k + 1) * (2 * X) := Nat.mul_le_mul (by omega) (by omega)
    have hFa' : (F k + 1) * (2 * X) ≤ 2 * (g * X) := by
      calc (F k + 1) * (2 * X) ≤ g * (2 * X) := Nat.mul_le_mul_right _ (by rw [hgk]; omega)
        _ = 2 * (g * X) := by ring
    simp only [encodeNats, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append]
    omega
  have key := xp_arith (Kκ := simK Mκ) (Kf := simK Mf) (X := X) (P := Pw)
    (a := n) (sκ := haltTime Mκ y) (kk := (encodeNat k).length) (sf := ht)
    (L := (encodeNats [F k * parA n, F k + 1]).length) (by omega) hPw1 hg1 hN1 hNw h1 h2 h3 h4
    (simInCost_le Mκ w _ _) (simNatCost_le Mf w _ _)
  have hpow : Pw ^ 3 * X = X ^ (3 * (d + 1) + 1) := by
    rw [hPw, ← pow_mul, pow_succ, mul_comm (d + 1) 3]
  rw [hpow] at key
  show _ ≤ xpK Mκ Mf * g ^ 3 * X ^ (3 * (d + 1) + 1)
  unfold xpK
  rw [← hn] at hcost ⊢
  omega

end Lax119563Proofs.Hardness
