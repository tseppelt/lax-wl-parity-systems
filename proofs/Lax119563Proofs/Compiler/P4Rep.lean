import Lax119563Proofs.Compiler.CArith

/-!
# Pushing a value repeatedly, with a running total

`repPushS q v n j acc`: push the value of `v` onto `q`, `n` times (counter `j`), adding it to
`acc` each time (`repPushS_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

/-- Push `v` `n` times on `q`, adding it to `acc` each time. -/
def repPushS (q : Fin Q) (v n j acc : Fin R) : CStm R Q :=
  .seq (.set j (.const 0)) (.loop (.lt (rv j) (rv n))
    (.seq (.push q (rv v)) (.seq (.set acc (.add (rv acc) (rv v)))
      (.set j (.add (rv j) (.const 1))))))

lemma repPushS_good (hw : 2 ≤ w) {q : Fin Q} {v n j acc : Fin R} (hvn : v ≠ n) (hvj : v ≠ j)
    (hva : v ≠ acc) (hnj : n ≠ j) (hna : n ≠ acc) (hja : j ≠ acc) (st : NSt R Q) {V N A : ℕ}
    (hV : st.env v = V) (hN : st.env n = N) (hA : st.env acc = A) (hNw : N + 1 < 2 ^ w)
    (hAw : A + N * V < 2 ^ w) :
    Good x w (repPushS q v n j acc) st
      (((st.setS q (List.replicate N V ++ st.stk q)).set acc (A + N * V)).set j N)
      ((N + 1) * (20 * Ex.nodeCost w)) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set S : ℕ → NSt R Q := fun i =>
    ((st.setS q (List.replicate i V ++ st.stk q)).set acc (A + i * V)).set j i with hS
  have eJ : ∀ i, (S i).env j = i := fun i => by simp [S]
  have eN : ∀ i, (S i).env n = N := fun i => by
    simp [S, Function.update_of_ne hnj, Function.update_of_ne hna, hN]
  have eV : ∀ i, (S i).env v = V := fun i => by
    simp [S, Function.update_of_ne hvj, Function.update_of_ne hva, hV]
  have eA : ∀ i, (S i).env acc = A + i * V := fun i => by
    simp [S, Function.update_of_ne (Ne.symm hja)]
  have hloop := Good.loop_const (x := x) (w := w) (e := .lt (rv j) (rv n))
    (body := .seq (.push q (rv v)) (.seq (.set acc (.add (rv acc) (rv v)))
      (.set j (.add (rv j) (.const 1))))) N S (12 * Ex.nodeCost w)
    (fun i hi => by simp only [Ex.eval, rv, eJ, eN, if_pos hi]; omega)
    (by simp only [Ex.eval, rv, eJ, eN]; simp)
    (fun i hi => by simp only [Ex.Fits, rv, eJ, eN]; omega)
    (fun i hi => by
      have hiV : (i + 1) * V ≤ N * V := Nat.mul_le_mul_right _ hi
      refine ((Good.push ?_).seq ((Good.set ?_).seq (Good.set ?_))).of_eq ?_ ?_
      · simp only [Ex.Fits, rv, eV]; nlinarith
      · simp only [Ex.Fits, rv, Ex.eval, NSt.setS_env, eA, eV]
        refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
      · simp only [Ex.Fits, rv, Ex.eval, NSt.setS_env, NSt.set_env,
          Function.update_of_ne hja, eJ]
        omega
      · simp only [S]
        rcases st with ⟨env, stk, pos, out⟩
        simp only [NSt.set, NSt.setS, Ex.eval, rv, NSt.mk.injEq, and_true]
        refine ⟨?_, ?_⟩
        · funext r
          simp only [Function.update_apply]
          split_ifs <;> simp_all <;> ring
        · funext r
          simp only [Function.update_apply]
          split_ifs <;> simp_all [List.replicate_succ]
      · simp only [Ex.size, rv]; omega)
  have hS0 : st.set j ((Ex.const 0 : Ex R).eval st.env) = S 0 := by
    rcases st with ⟨env, stk, pos, out⟩
    simp only [S, NSt.set, NSt.setS, Ex.eval, NSt.mk.injEq, and_true, List.replicate_zero,
      List.nil_append, zero_mul, add_zero]
    refine ⟨?_, ?_⟩
    · funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
    · funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
  have h0 := Good.set (x := x) (w := w) (r := j) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  rw [hS0] at h0
  refine (h0.seq hloop).mono ?_
  simp only [condCost, Ex.size, rv]
  nlinarith

/-- Push `v₁` then `v₂`, `n` times, adding both to `acc` each time. -/
def rep2PushS (q : Fin Q) (v₁ v₂ n j acc : Fin R) : CStm R Q :=
  .seq (.set j (.const 0)) (.loop (.lt (rv j) (rv n))
    (.seq (.push q (rv v₁)) (.seq (.push q (rv v₂))
      (.seq (.set acc (.add (rv acc) (.add (rv v₁) (rv v₂))))
      (.set j (.add (rv j) (.const 1)))))))

lemma rep2PushS_good (hw : 2 ≤ w) {q : Fin Q} {v₁ v₂ n j acc : Fin R} (h1n : v₁ ≠ n)
    (h1j : v₁ ≠ j) (h1a : v₁ ≠ acc) (h2n : v₂ ≠ n) (h2j : v₂ ≠ j) (h2a : v₂ ≠ acc)
    (hnj : n ≠ j) (hna : n ≠ acc) (hja : j ≠ acc) (st : NSt R Q) {V₁ V₂ N A : ℕ}
    (hV₁ : st.env v₁ = V₁) (hV₂ : st.env v₂ = V₂) (hN : st.env n = N) (hA : st.env acc = A)
    (hNw : N + 1 < 2 ^ w) (hAw : A + N * (V₁ + V₂) < 2 ^ w) :
    Good x w (rep2PushS q v₁ v₂ n j acc) st
      (((st.setS q ((List.replicate N [V₂, V₁]).flatten ++ st.stk q)).set acc
        (A + N * (V₁ + V₂))).set j N)
      ((N + 1) * (30 * Ex.nodeCost w)) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set S : ℕ → NSt R Q := fun i =>
    ((st.setS q ((List.replicate i [V₂, V₁]).flatten ++ st.stk q)).set acc
      (A + i * (V₁ + V₂))).set j i with hS
  have eJ : ∀ i, (S i).env j = i := fun i => by simp [S]
  have eN : ∀ i, (S i).env n = N := fun i => by
    simp [S, Function.update_of_ne hnj, Function.update_of_ne hna, hN]
  have eV₁ : ∀ i, (S i).env v₁ = V₁ := fun i => by
    simp [S, Function.update_of_ne h1j, Function.update_of_ne h1a, hV₁]
  have eV₂ : ∀ i, (S i).env v₂ = V₂ := fun i => by
    simp [S, Function.update_of_ne h2j, Function.update_of_ne h2a, hV₂]
  have eA : ∀ i, (S i).env acc = A + i * (V₁ + V₂) := fun i => by
    simp [S, Function.update_of_ne (Ne.symm hja)]
  have hloop := Good.loop_const (x := x) (w := w) (e := .lt (rv j) (rv n))
    (body := .seq (.push q (rv v₁)) (.seq (.push q (rv v₂))
      (.seq (.set acc (.add (rv acc) (.add (rv v₁) (rv v₂))))
      (.set j (.add (rv j) (.const 1)))))) N S (20 * Ex.nodeCost w)
    (fun i hi => by simp only [Ex.eval, rv, eJ, eN, if_pos hi]; omega)
    (by simp only [Ex.eval, rv, eJ, eN]; simp)
    (fun i hi => by simp only [Ex.Fits, rv, eJ, eN]; omega)
    (fun i hi => by
      have hiV : (i + 1) * (V₁ + V₂) ≤ N * (V₁ + V₂) := Nat.mul_le_mul_right _ hi
      refine ((Good.push ?_).seq ((Good.push ?_).seq ((Good.set ?_).seq
        (Good.set ?_)))).of_eq ?_ ?_
      · simp only [Ex.Fits, rv, eV₁]; nlinarith
      · simp only [Ex.Fits, rv, NSt.setS_env, eV₂]; nlinarith
      · simp only [Ex.Fits, rv, Ex.eval, NSt.setS_env, eA, eV₁, eV₂]
        refine ⟨by nlinarith, ⟨by nlinarith, by nlinarith, by nlinarith⟩, by nlinarith⟩
      · simp only [Ex.Fits, rv, Ex.eval, NSt.setS_env, NSt.set_env,
          Function.update_of_ne hja, eJ]
        omega
      · simp only [S]
        rcases st with ⟨env, stk, pos, out⟩
        simp only [NSt.set, NSt.setS, Ex.eval, rv, NSt.mk.injEq, and_true]
        refine ⟨?_, ?_⟩
        · funext r
          simp only [Function.update_apply]
          split_ifs <;> simp_all <;> ring
        · funext r
          simp only [Function.update_apply]
          split_ifs <;> simp_all [List.replicate_succ]
      · simp only [Ex.size, rv]; omega)
  have hS0 : st.set j ((Ex.const 0 : Ex R).eval st.env) = S 0 := by
    rcases st with ⟨env, stk, pos, out⟩
    simp only [S, NSt.set, NSt.setS, Ex.eval, NSt.mk.injEq, and_true, List.replicate_zero,
      List.flatten_nil, List.nil_append, zero_mul, add_zero]
    refine ⟨?_, ?_⟩
    · funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
    · funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
  have h0 := Good.set (x := x) (w := w) (r := j) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  rw [hS0] at h0
  refine (h0.seq hloop).mono ?_
  simp only [condCost, Ex.size, rv]
  nlinarith

end CStm

end Lax119563Proofs.Compiler
