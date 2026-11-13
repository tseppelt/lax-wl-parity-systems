import Lax119563Proofs.Reduction.HStack
import Lax119563.BinaryEncodings

/-!
# Binary registers on stacks: addition, comparison, output, input

Stack routines for `add`, `lt`, `emit`, `rd` and `rst` of `HProg`.
-/

open Function Lax119563.BinaryEncodings

namespace Lax119563Proofs.Reduction

open Hierarchy Hierarchy.Prog
open Machines (valBits valBits_bits)

variable {K : ℕ}

/-- Copy `r` onto the empty stack `d` through the empty helper `t`. -/
def copyE (r d t : Fin K) : Prog K 0 := seq (moveAll r t) (dupAll t r d)

/-! ## Addition -/

/-- `r := r + b` with empty helpers `t₀, t₁, t₂`. -/
def hAdd (r b t₀ t₁ t₂ : Fin K) : Prog K 0 :=
  seq (copyE b t₁ t₀) (seq (ripple r t₁ t₂ t₀) (moveAll t₀ r))

lemma hAdd_runs {r b t₀ t₁ t₂ : Fin K} (hrb : r ≠ b) (hr0 : r ≠ t₀) (hr1 : r ≠ t₁)
    (hr2 : r ≠ t₂) (hb0 : b ≠ t₀) (hb1 : b ≠ t₁) (hb2 : b ≠ t₂) (h01 : t₀ ≠ t₁)
    (h02 : t₀ ≠ t₂) (h12 : t₁ ≠ t₂) {s : Stacks K 0} {u v : ℕ} (hr : s r = nst u)
    (hb : s b = nst v) (h0 : s t₀ = []) (h1 : s t₁ = []) (h2 : s t₂ = []) :
    (hAdd r b t₀ t₁ t₂).RunsLe s (update s r (nst (u + v)))
      (16 * (nst v).length + 17 * (nst (u + v)).length + 4) := by
  have c1 := hCopy_runs_empty hb1 hb0 h01.symm hb h0 h1
  have c2 := ripple_runs hr1 hr2 hr0 h12 h01.symm h02.symm (Nat.bits u) (Nat.bits v) false
    (update s t₁ (nst v)) (by simp [update_of_ne hr1, hr, nst]) (by simp [nst])
    (by simp [update_of_ne h12.symm, h2])
  have e : (bs (addL (Nat.bits u) (Nat.bits v) false)) = nst (u + v) := by
    rw [nst, bits_add]
  rw [e] at c2
  refine (c1.seq (c2.seq (moveAll_runs hr0.symm (m := 0) ((nst (u + v)).reverse) _ ?_))).of_eq
    ?_ ?_
  · simp [update_of_ne h01, h0]
  · funext k
    simp only [update_apply]
    split_ifs <;> simp_all
  · have : (addL (Nat.bits u) (Nat.bits v) false).length = (nst (u + v)).length := by
      rw [← e]; simp
    simp only [List.length_reverse, this]; omega

/-! ## Comparison -/

/-- A comparison result as a stack. -/
def ordSt : Ordering → List Sym
  | .lt => [1]
  | .gt => [0]
  | .eq => []

@[simp] lemma ordSt_tail (o : Ordering) : (ordSt o).tail = [] := by cases o <;> rfl

/-- One step of the comparison scan of `i` and `j`, with the result so far on `k`. -/
def cmpLeaf (i j k : Fin K) (x y : Bool) : Prog K 0 :=
  seq (pop i) (seq (pop j) (if x = y then skip else seq (pop k) (push k (if y then 1 else 0))))

/-- The comparison scan. -/
def cmpLoop (i j k : Fin K) : Prog K 0 :=
  loop (fun t => (t i).isSome || (t j).isSome) (bit2 i j (cmpLeaf i j k))

section Cmp

variable {i j k : Fin K} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
include hij hik hjk

lemma cmpLeaf_runs {s : Stacks K 0} {x y : Bool} {l l' : List Bool} {o : Ordering}
    (hi : (s i).tail = bs l) (hj : (s j).tail = bs l') (hk : s k = ordSt o) :
    (cmpLeaf i j k x y).RunsLe s
      (update (update (update s i (bs l)) j (bs l')) k (ordSt ((compare x y).then o))) 6 := by
  unfold cmpLeaf
  by_cases hxy : x = y
  · subst hxy
    simp only [if_true]
    refine ((RunsLe.pop i s).seq ((RunsLe.pop j _).seq (RunsLe.skip _))).of_eq ?_ (by norm_num)
    funext k'
    have e : (compare x x).then o = o := by cases x <;> rfl
    simp only [update_apply, e]
    split_ifs <;> simp_all
  · simp only [hxy, if_false]
    refine ((RunsLe.pop i s).seq ((RunsLe.pop j _).seq ((RunsLe.pop k _).seq
      (RunsLe.push k _ _)))).of_eq ?_ (by norm_num)
    have e : ordSt ((compare x y).then o) = [if y then 1 else 0] := by
      cases x <;> cases y <;> simp_all [ordSt, compare, compareOfLessAndEq]
    have e2 : (s k).tail = [] := by rw [hk]; cases o <;> rfl
    funext k'
    simp only [update_apply, e]
    split_ifs <;> simp_all

lemma cmpLoop_runs : ∀ (l l' : List Bool) (o : Ordering) (s : Stacks K 0), s i = bs l →
    s j = bs l' → s k = ordSt o →
    (cmpLoop i j k).RunsLe s (update (update (update s i []) j []) k (ordSt (cmpL l l' o)))
      (9 * (l.length + l'.length) + 1)
  | [], [], o, s, hi, hj, hk => by
    refine (RunsLe.loopF (by simp [tops, hi, hj])).of_eq ?_ (by simp)
    funext k'
    simp only [update_apply, cmpL]
    split_ifs <;> simp_all
  | x :: l, [], o, s, hi, hj, hk => by
    refine (RunsLe.loopT (by simp [tops, hi]) (bit2_runs (a := x) (b := false)
      (by rw [tops_bs s i _ hi]; rfl) (by rw [tops_bs s j [] hj]; rfl)
      (cmpLeaf_runs hij hik hjk (l := l) (l' := []) (by simp [hi]) (by simp [hj]) hk))
      (cmpLoop_runs l [] ((compare x false).then o) _ ?_ ?_ ?_)).of_eq ?_ (by simp; omega)
    · simp [update_of_ne hij, update_of_ne hik]
    · simp [update_of_ne hjk]
    · simp
    · funext k'
      simp only [update_apply, cmpL]
      split_ifs <;> simp_all
  | [], y :: l', o, s, hi, hj, hk => by
    refine (RunsLe.loopT (by simp [tops, hj]) (bit2_runs (a := false) (b := y)
      (by rw [tops_bs s i [] hi]; rfl) (by rw [tops_bs s j _ hj]; rfl)
      (cmpLeaf_runs hij hik hjk (l := []) (l' := l') (by simp [hi]) (by simp [hj]) hk))
      (cmpLoop_runs [] l' ((compare false y).then o) _ ?_ ?_ ?_)).of_eq ?_ (by simp; omega)
    · simp [update_of_ne hij, update_of_ne hik]
    · simp [update_of_ne hjk]
    · simp
    · funext k'
      simp only [update_apply, cmpL]
      split_ifs <;> simp_all
  | x :: l, y :: l', o, s, hi, hj, hk => by
    refine (RunsLe.loopT (by simp [tops, hi]) (bit2_runs (a := x) (b := y)
      (by rw [tops_bs s i _ hi]; rfl) (by rw [tops_bs s j _ hj]; rfl)
      (cmpLeaf_runs hij hik hjk (l := l) (l' := l') (by simp [hi]) (by simp [hj]) hk))
      (cmpLoop_runs l l' ((compare x y).then o) _ ?_ ?_ ?_)).of_eq ?_ (by simp; omega)
    · simp [update_of_ne hij, update_of_ne hik]
    · simp [update_of_ne hjk]
    · simp
    · funext k'
      simp only [update_apply, cmpL]
      split_ifs <;> simp_all
  termination_by l l' => l.length + l'.length

end Cmp

/-- `f := [a < b]` with empty helpers `t₀, …, t₃`. -/
def hLt (f a b t₀ t₁ t₂ t₃ : Fin K) : Prog K 0 :=
  seq (copyE a t₁ t₀) (seq (copyE b t₂ t₀) (seq (cmpLoop t₁ t₂ t₃) (seq (clear f)
    (seq (ite (fun t => t t₃ == some 1) (push f 1) skip) (pop t₃)))))

lemma nst_one : nst 1 = [1] := by
  have := nst_bit1 0; simpa using this

lemma hLt_runs {f a b t₀ t₁ t₂ t₃ : Fin K}
    (hfa : f ≠ a) (hfb : f ≠ b) (hf0 : f ≠ t₀) (hf1 : f ≠ t₁) (hf2 : f ≠ t₂) (hf3 : f ≠ t₃)
    (hab : a ≠ b) (ha0 : a ≠ t₀) (ha1 : a ≠ t₁) (ha2 : a ≠ t₂) (ha3 : a ≠ t₃)
    (hb0 : b ≠ t₀) (hb1 : b ≠ t₁) (hb2 : b ≠ t₂) (hb3 : b ≠ t₃)
    (h01 : t₀ ≠ t₁) (h02 : t₀ ≠ t₂) (h03 : t₀ ≠ t₃) (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃)
    (h23 : t₂ ≠ t₃) {s : Stacks K 0} {u v : ℕ} (ha : s a = nst u)
    (hb : s b = nst v) (h0 : s t₀ = []) (h1 : s t₁ = []) (h2 : s t₂ = []) (h3 : s t₃ = []) :
    (hLt f a b t₀ t₁ t₂ t₃).RunsLe s (update s f (nst (if u < v then 1 else 0)))
      (2 * (s f).length + 25 * ((nst u).length + (nst v).length) + 12) := by
  have c1 := hCopy_runs_empty ha1 ha0 h01.symm ha h0 h1
  have c2 := hCopy_runs_empty hb2 hb0 h02.symm (s := update s t₁ (nst u)) (v := v)
    (by simp [update_of_ne hb1, hb]) (by simp [update_of_ne h01, h0])
    (by simp [update_of_ne h12.symm, h2])
  have c3 := cmpLoop_runs h12 h13 h23 (Nat.bits u) (Nat.bits v) .eq
    (update (update s t₁ (nst u)) t₂ (nst v)) (by simp [update_of_ne h12, nst])
    (by simp [nst]) (by simp [update_of_ne h13.symm, update_of_ne h23.symm, h3, ordSt])
  rw [cmpL_spec, valBits_bits, valBits_bits, Ordering.then_eq] at c3
  set s₃ := update (update (update (update (update s t₁ (nst u)) t₂ (nst v)) t₁ []) t₂ [])
    t₃ (ordSt (compare u v)) with hs₃
  have c4 := clear_runs f (s₃ f) s₃ rfl
  have hf3' : update s₃ f [] t₃ = ordSt (compare u v) := by
    simp [hs₃, update_of_ne hf3.symm]
  have c5 : (ite (fun t => t t₃ == some 1) (push f 1) skip : Prog K 0).RunsLe (update s₃ f [])
      (update (update s₃ f []) f (nst (if u < v then 1 else 0))) 3 := by
    rcases lt_trichotomy u v with huv | rfl | huv
    · refine ((RunsLe.push f 1 _).iteT ?_).of_eq ?_ le_rfl
      · simp [tops, hf3', compare_lt_iff_lt.mpr huv, ordSt]
      · simp [huv, nst_one]
    · refine ((RunsLe.skip _).iteF ?_).of_eq ?_ (by norm_num)
      · simp [tops, hf3', ordSt]
      · simp
    · refine ((RunsLe.skip _).iteF ?_).of_eq ?_ (by norm_num)
      · simp [tops, hf3', compare_gt_iff_gt.mpr huv, ordSt]
      · simp [not_lt.mpr huv.le]
  have c6 := RunsLe.pop t₃ (update (update s₃ f []) f (nst (if u < v then 1 else 0)))
  have hlen : ∀ o : Ordering, (ordSt o).length ≤ 1 := fun o => by cases o <;> simp [ordSt]
  refine (c1.seq (c2.seq (c3.seq (c4.seq (c5.seq c6))))).of_eq ?_ ?_
  · funext k
    simp only [hs₃, update_apply]
    split_ifs <;> simp_all
  · have : (s₃ f) = s f := by
      simp [hs₃, update_of_ne hf1, update_of_ne hf2, update_of_ne hf3]
    rw [this]; simp only [nst, length_bs]; omega

/-! ## Output -/

/-- Push the codes `1 d` of the digits on `i` onto `o`. -/
def emitLoop (i o : Fin K) : Prog K 0 :=
  loop (fun t => (t i).isSome) (bit1 i fun d => seq (pop i) (seq (push o 1) (push o (sym d))))

lemma emitLoop_runs {i o : Fin K} (hio : i ≠ o) : ∀ (l : List Bool) (s : Stacks K 0),
    s i = bs l →
    (emitLoop i o).RunsLe s
      (update (update s i []) o ((bs (l.flatMap fun d => [true, d])).reverse ++ s o))
      (7 * l.length + 1)
  | [], s, hs => by
    refine (RunsLe.loopF (by simp [tops, hs])).of_eq ?_ (by simp)
    funext k; simp only [update_apply]; split_ifs <;> simp_all
  | d :: l, s, hs => by
    refine (RunsLe.loopT (by simp [tops, hs]) (bit1_runs (a := d)
      (by rw [tops_bs s i _ hs]; rfl) ((RunsLe.pop i s).seq ((RunsLe.push o 1 _).seq
        (RunsLe.push o (sym d) _)))) (emitLoop_runs hio l _ ?_)).of_eq ?_ (by simp; omega)
    · simp [update_of_ne hio, hs]
    · funext k
      simp only [update_apply]
      split_ifs <;> simp_all [bs_append]

/-- Append `encodeNat` of `r` to the reversed output on `o`, with empty helpers `t₀, t₁`. -/
def hEmit (r o t₀ t₁ : Fin K) : Prog K 0 := seq (copyE r t₁ t₀) (seq (emitLoop t₁ o) (push o 0))

lemma bs_encodeNat_reverse (v : ℕ) :
    (bs (encodeNat v)).reverse = 0 :: (bs ((Nat.bits v).flatMap fun d => [true, d])).reverse := by
  simp [encodeNat, bs_append]

lemma hEmit_runs {r o t₀ t₁ : Fin K} (hro : r ≠ o) (hr0 : r ≠ t₀) (hr1 : r ≠ t₁)
    (ho0 : o ≠ t₀) (ho1 : o ≠ t₁) (h01 : t₀ ≠ t₁) {s : Stacks K 0} {v : ℕ}
    (hr : s r = nst v) (h0 : s t₀ = []) (h1 : s t₁ = []) :
    (hEmit r o t₀ t₁).RunsLe s (update s o ((bs (encodeNat v)).reverse ++ s o))
      (23 * (nst v).length + 5) := by
  have c1 := hCopy_runs_empty hr1 hr0 h01.symm hr h0 h1
  have c2 := emitLoop_runs ho1.symm (Nat.bits v) (update s t₁ (nst v)) (by simp [nst])
  have c3 := RunsLe.push o 0 (update (update (update s t₁ (nst v)) t₁ []) o
    ((bs ((Nat.bits v).flatMap fun d => [true, d])).reverse ++ update s t₁ (nst v) o))
  refine (c1.seq (c2.seq c3)).of_eq ?_ ?_
  · funext k
    simp only [update_apply, bs_encodeNat_reverse]
    split_ifs <;> simp_all
  · simp [nst]; omega

/-! ## Input -/

/-- Read the top bit of the remaining input `xr` into `r`. -/
def hRdA (r xr : Fin K) : Prog K 0 :=
  seq (clear r) (ite (fun t => t xr == some 1) (push r 1) skip)

lemma hRdA_runs {r xr : Fin K} (hrr : r ≠ xr) {s : Stacks K 0} {l : List Bool}
    (hs : s xr = bs l) :
    (hRdA r xr).RunsLe s (update s r (nst (l.headD false).toNat)) (2 * (s r).length + 4) := by
  have c1 := clear_runs r (s r) s rfl
  have hxr : update s r [] xr = bs l := by simp [update_of_ne hrr.symm, hs]
  have c2 : (ite (fun t => t xr == some 1) (push r 1) skip : Prog K 0).RunsLe
      (update s r []) (update (update s r []) r (nst (l.headD false).toNat)) 3 := by
    cases l with
    | nil => exact ((RunsLe.skip _).iteF (by simp [tops, hxr])).of_eq (by simp) (by norm_num)
    | cons d l =>
      cases d
      · exact ((RunsLe.skip _).iteF (by simp [tops, hxr])).of_eq (by simp) (by norm_num)
      · exact ((RunsLe.push r 1 _).iteT (by simp [tops, hxr])).of_eq
          (by simp [nst_one]) (by norm_num)
  exact (c1.seq c2).of_eq (by simp) (by omega)

/-- Move the top symbol of the remaining input `xr` (if any) to `xl`. -/
def hRdB (xl xr : Fin K) : Prog K 0 := ite (fun t => (t xr).isSome) (moveOne xr xl) skip

/-- Read a bit of the remaining input. -/
def hRd (r xl xr : Fin K) : Prog K 0 := seq (hRdA r xr) (hRdB xl xr)

end Lax119563Proofs.Reduction
