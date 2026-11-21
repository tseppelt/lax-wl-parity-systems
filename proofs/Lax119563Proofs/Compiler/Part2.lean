import Lax119563Proofs.Circuits.Part1
import Lax119563Proofs.Compiler.Part1
import Lax119563Proofs.Hardness.Part1
import Lax119563Proofs.Matrix.Part1
import Lax119563Proofs.Reduction.Part1
import Lax119563Proofs.Reduction.Part2

/-! ### Formerly `Lax119563Proofs.Compiler.CSortMain` -/

section Compiler_CSortMain

/-!
# Merge sort of records on number stacks: merging, passes, the sort

* `mrgS_good`: the merge loop computes `CSort.mrg`;
* `pairBody_good`, `passS_good`: one merge pass computes `CSort.passX` (the two runs are split
  off with `mvRecsB`, merged onto `Y`, and finally moved back);
* `mvAllS_good`, `revS_good`: moving all records, reversing their order;
* **`sortS_good`**: passes with run lengths `1, 2, 4, …` while `r < N`, then a reversal if the
  last direction is descending; the records end sorted (`CSort.finalRecs_eq`), within
  `(N + 1)(log₂ N + 2) · 700 (A + 1) · nodeCost w`.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

lemma length_flatten_const {l : List (List ℕ)} {a : ℕ} (h : ∀ y ∈ l, y.length = a) :
    l.flatten.length = a * l.length := by
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [List.flatten_cons, List.length_append, h y (by simp),
      ih (fun z hz => h z (by simp [hz]))]
    simp; ring

lemma mem_mrgStep (d : Bool) {u v acc : List (List ℕ)} {y : List ℕ}
    (hy : y ∈ (CSort.mrgStep d (u, v, acc)).1 ++ (CSort.mrgStep d (u, v, acc)).2.1) :
    y ∈ u ++ v := by
  rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩
  · simpa [CSort.mrgStep] using hy
  · simp only [CSort.mrgStep] at hy; simp at hy ⊢; tauto
  · simp only [CSort.mrgStep] at hy; simp at hy ⊢; tauto
  · simp only [CSort.mrgStep] at hy
    split_ifs at hy <;> simp at hy ⊢ <;> tauto

lemma nef_mrgStk {S : Fin Q → List ℕ} {T1 T2 Y : Fin Q} {u v acc : List (List ℕ)} {a : ℕ}
    (ha : 1 ≤ a) (hrec : ∀ y ∈ u ++ v, y.length = a) (h0 : T1 ≠ T2) (h1 : T1 ≠ Y)
    (h2 : T2 ≠ Y) :
    (if (mrgStk S T1 T2 Y u v acc T1).isEmpty then 0 else 1) = nef u ∧
      (if (mrgStk S T1 T2 Y u v acc T2).isEmpty then 0 else 1) = nef v := by
  rw [mrgStk_T1 h0 h1, mrgStk_T2 h2]
  have hu := flatten_eq_nil_iff (l := u) ha (fun y hy => hrec y (by simp [hy]))
  have hv := flatten_eq_nil_iff (l := v) ha (fun y hy => hrec y (by simp [hy]))
  constructor
  · unfold nef; by_cases h : u = []
    · simp [h]
    · have : u.flatten ≠ [] := fun e => h (hu.mp e)
      simp [h, List.isEmpty_iff, this]
  · unfold nef; by_cases h : v = []
    · simp [h]
    · have : v.flatten ≠ [] := fun e => h (hv.mp e)
      simp [h, List.isEmpty_iff, this]

section Merge

variable {T1 T2 Y tmp C1 C2 : Fin Q} {A dir c f1 f2 kc t1 t2 i t : Fin R}

/-- **The merge loop.** -/
lemma mrgS_good (hw2 : 2 ≤ w) (hstk : [T1, T2, Y, tmp, C1, C2].Nodup)
    (hreg : [A, dir, c, f1, f2, kc, t1, t2, i, t].Nodup)
    (S : Fin Q → List ℕ) (d : Bool) (s : NSt R Q) {a : ℕ} (u v acc : List (List ℕ))
    (ha : s.env A = a) (ha1 : 1 ≤ a) (hdir : s.env dir = if d then 1 else 0)
    (hs : s.stk = mrgStk S T1 T2 Y u v acc)
    (hrec : ∀ y ∈ u ++ v, y.length = a ∧ ∀ z ∈ y, z < 2 ^ w) (hw : a + 1 < 2 ^ w) :
    ∃ s', Good x w (mrgS T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t) s s'
        ((u.length + v.length + 1) * (140 * (a + 1) * Ex.nodeCost w)) ∧
      s'.stk = mrgStk S T1 T2 Y [] [] (CSort.mrg d u v acc) ∧
      Frame s s' [c, kc, t1, t2, i, t, f1, f2] := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 := two_le_pow hw2
  have h0 : T1 ≠ T2 := by ndup hstk
  have h1 : T1 ≠ Y := by ndup hstk
  have h2 : T2 ≠ Y := by ndup hstk
  have hf12 : f1 ≠ f2 := by ndup hreg
  set regs : List (Fin R) := [c, kc, t1, t2, i, t, f1, f2] with hregs
  have hAr : A ∉ regs := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg
    simp only [hregs, List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto
  have hdr : dir ∉ regs := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg
    simp only [hregs, List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto
  set Inv : NSt R Q → Prop := fun s₁ => ∃ u' v' acc', s₁.stk = mrgStk S T1 T2 Y u' v' acc' ∧
    CSort.mrg d u' v' acc' = CSort.mrg d u v acc ∧ s₁.env f1 = nef u' ∧ s₁.env f2 = nef v' ∧
    (∀ y ∈ u' ++ v', y ∈ u ++ v) ∧ Frame s s₁ regs
  set μ : NSt R Q → ℕ := fun s₁ => ((s₁.stk T1).length + (s₁.stk T2).length) / a
  have hμ : ∀ s₁ u' v' acc', s₁.stk = mrgStk S T1 T2 Y u' v' acc' →
      (∀ y ∈ u' ++ v', y ∈ u ++ v) → μ s₁ = u'.length + v'.length := by
    intro s₁ u' v' acc' hs₁ hsub
    simp only [μ, hs₁, mrgStk_T1 h0 h1, mrgStk_T2 h2]
    rw [length_flatten_const (a := a) (fun y hy => (hrec y (hsub y (by simp [hy]))).1),
      length_flatten_const (a := a) (fun y hy => (hrec y (hsub y (by simp [hy]))).1),
      ← mul_add, Nat.mul_div_cancel_left _ (by omega)]
  have hloop := Good.loop_var (x := x) (w := w) (e := .add (rv f1) (rv f2))
    (body := mrgBody T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t)
    Inv μ (fun _ => 0) 0 (104 * Ex.nodeCost w * a + 130 * Ex.nodeCost w) (by
      intro s₁ hI
      obtain ⟨u', v', acc', hs₁, hm, hg1, hg2, hsub, hfr⟩ := hI
      have hnef : ∀ l : List (List ℕ), nef l ≤ 1 := fun l => by unfold nef; split_ifs <;> omega
      refine ⟨⟨show s₁.env f1 < 2 ^ w by rw [hg1]; have := hnef u'; omega,
        show s₁.env f2 < 2 ^ w by rw [hg2]; have := hnef v'; omega,
        by simp only [rv, Ex.eval, hg1, hg2]; have := hnef u'; have := hnef v'; omega⟩, ?_⟩
      intro hc
      have huv : u' ≠ [] ∨ v' ≠ [] := by
        by_contra hn; simp only [not_or, not_not] at hn
        apply hc; simp [rv, Ex.eval, hg1, hg2, hn.1, hn.2, nef]
      have hA₁ : s₁.env A = a := by
        rw [hfr.2.2 A hAr, ha]
      have hdir₁ : s₁.env dir = if d then 1 else 0 := by
        rw [hfr.2.2 dir hdr, hdir]
      obtain ⟨s₂, g₂, k₂, fr₂⟩ := mrgIte_good (x := x) (tmp := tmp) (C1 := C1) (C2 := C2)
        (c := c) (kc := kc) (t1 := t1) (t2 := t2) (i := i) (t := t) hw2 hstk hreg S d s₁ u' v' acc' hA₁
        hdir₁ hs₁ hg1 hg2 (fun y hy => hrec y (hsub y hy)) hw huv
      set st3 := CSort.mrgStep d (u', v', acc')
      have hsub3 : ∀ y ∈ st3.1 ++ st3.2.1, y ∈ u ++ v := fun y hy => hsub y (mem_mrgStep d hy)
      have hne := nef_mrgStk (S := S) (acc := st3.2.2) ha1
        (fun y hy => (hrec y (hsub3 y hy)).1) h0 h1 h2
      have gs1 : Good x w (.sne f1 T1 : CStm R Q) s₂ (s₂.set f1 (nef st3.1)) (2 * unitCost w + 1) :=
        (Good.sne f1 T1).of_eq (by rw [k₂, hne.1]) le_rfl
      have gs2 : Good x w (.sne f2 T2 : CStm R Q) (s₂.set f1 (nef st3.1))
          ((s₂.set f1 (nef st3.1)).set f2 (nef st3.2.1)) (2 * unitCost w + 1) :=
        (Good.sne f2 T2).of_eq (by simp only [NSt.set_stk, k₂, hne.2]) le_rfl
      have hlen : st3.1.length + st3.2.1.length + 1 = u'.length + v'.length :=
        CSort.mrgStep_length d u' v' acc' huv
      refine ⟨_, (g₂.seq (gs1.seq gs2)).mono (by simp; omega),
        ⟨st3.1, st3.2.1, st3.2.2, by simp only [NSt.set_stk]; exact k₂, ?_, by simp [Function.update_of_ne hf12],
          by simp, hsub3, ?_⟩, ?_, le_rfl⟩
      · rw [← hm, CSort.mrg_step d u' v' acc' huv]
      · refine hfr.trans (Frame.trans (fr₂.mono (by intro r hr; simp [regs] at hr ⊢; tauto))
          ⟨rfl, rfl, fun r hr => ?_⟩)
        simp only [regs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [Function.update_of_ne hr.2.2.2.2.2.2.1, Function.update_of_ne hr.2.2.2.2.2.2.2]
      · rw [hμ _ _ _ _ (by simp only [NSt.set_stk]; exact k₂) hsub3, hμ _ _ _ _ hs₁ hsub]
        omega)
  -- the initialization
  have hne0 := nef_mrgStk (S := S) (acc := acc) ha1 (fun y hy => (hrec y hy).1) h0 h1 h2
  have g1 : Good x w (.sne f1 T1 : CStm R Q) s (s.set f1 (nef u)) (2 * unitCost w + 1) :=
    (Good.sne f1 T1).of_eq (by rw [hs, hne0.1]) le_rfl
  have g2 : Good x w (.sne f2 T2 : CStm R Q) (s.set f1 (nef u))
      ((s.set f1 (nef u)).set f2 (nef v)) (2 * unitCost w + 1) :=
    (Good.sne f2 T2).of_eq (by simp only [NSt.set_stk, hs, hne0.2]) le_rfl
  have hI0 : Inv ((s.set f1 (nef u)).set f2 (nef v)) :=
    ⟨u, v, acc, by simpa using hs, rfl, by simp [Function.update_of_ne hf12], by simp, fun y hy => hy,
      ⟨rfl, rfl, fun r hr => by
        simp only [regs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [Function.update_of_ne hr.2.2.2.2.2.2.1, Function.update_of_ne hr.2.2.2.2.2.2.2]⟩⟩
  obtain ⟨s', g', ⟨u', v', acc', hs', hm, hg1, hg2, hsub, hfr⟩, hend⟩ := hloop _ hI0
  have hu' : u' = [] := by
    by_contra h; simp [rv, Ex.eval, hg1, nef, h] at hend
  have hv' : v' = [] := by
    by_contra h; simp [rv, Ex.eval, hg2, nef, h] at hend
  subst hu' hv'
  have hμ0 := hμ ((s.set f1 (nef u)).set f2 (nef v)) u v acc (by simpa using hs) (fun y hy => hy)
  refine ⟨s', (g1.seq (g2.seq g')).mono ?_, ?_, hfr⟩
  · rw [hμ0]
    simp only [condCost, rv, Ex.size, mul_zero, zero_add]
    have hN : Ex.nodeCost w ≤ a * Ex.nodeCost w := Nat.le_mul_of_pos_left _ (by omega)
    set N := Ex.nodeCost w
    set m := u.length + v.length
    have e1 : 104 * N * a + 130 * N + ((1 + 1 + 1) * N + 1) ≤ 140 * (a + 1) * N := by nlinarith
    have e2 : m * (104 * N * a + 130 * N + ((1 + 1 + 1) * N + 1)) ≤ m * (140 * (a + 1) * N) :=
      Nat.mul_le_mul_left _ e1
    nlinarith
  · rw [hs', ← hm, CSort.mrg_nil]

end Merge

/-! ## One pass -/

/-- Proves `a ∉ l` for entries of a duplicate-free list `h`. -/
macro "nmem" h:ident : tactic =>
  `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; (repeat' apply And.intro); all_goals first | (intro hh; subst hh; simp at $h:ident) | simp))

/-- Proves `l.Nodup` for a list of entries of a duplicate-free list `h`. -/
macro "nodupT" h:ident : tactic =>
  `(tactic| (simp only [List.nodup_cons, List.nodup_nil, and_true]; (repeat' apply And.intro); all_goals nmem $h))

lemma take_min_len (l : List (List ℕ)) (r : ℕ) : l.take (min r l.length) = l.take r := by
  rcases le_total r l.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.take_of_length_le le_rfl, List.take_of_length_le h]

lemma drop_min_len (l : List (List ℕ)) (r : ℕ) : l.drop (min r l.length) = l.drop r := by
  rcases le_total r l.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.drop_eq_nil_of_le le_rfl, List.drop_eq_nil_of_le h]

/-- The stacks during a pass: the unprocessed records `rs'` on `X`, the merged runs `Lacc`
on top of `Y`. -/
def passStk (S : Fin Q → List ℕ) (X Y : Fin Q) (rs' Lacc : List (List ℕ)) : Fin Q → List ℕ :=
  Function.update (Function.update S X rs'.flatten) Y (Lacc.flatten ++ S Y)

/-- Split off two runs of `r` records and merge them onto `Y`. -/
def pairBody (X T1 T2 Y tmp C1 C2 : Fin Q) (A dir c f1 f2 kc t1 t2 i t r N done k : Fin R) :
    CStm R Q :=
  .seq (mvRecsB X T1 tmp A r done N k i t)
    (.seq (mvRecsB X T2 tmp A r done N k i t) (mrgS T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t))

section Pass

variable {X T1 T2 Y tmp C1 C2 : Fin Q} {A dir c f1 f2 kc t1 t2 i t r N done k lim2 : Fin R}

set_option maxHeartbeats 1000000 in
lemma pairBody_good (hw2 : 2 ≤ w) (hstk : [X, T1, T2, Y, tmp, C1, C2].Nodup)
    (hreg : [A, dir, c, f1, f2, kc, t1, t2, i, t, r, N, done, k].Nodup)
    (S : Fin Q → List ℕ) (hT1 : S T1 = []) (hT2 : S T2 = []) (d : Bool) (s : NSt R Q)
    {a rr n : ℕ} (rs' Lacc : List (List ℕ)) (hne : rs' ≠ [])
    (hs : s.stk = passStk S X Y rs' Lacc) (ha : s.env A = a) (ha1 : 1 ≤ a)
    (hdir : s.env dir = if d then 1 else 0) (hr : s.env r = rr) (hr1 : 1 ≤ rr)
    (hn : s.env N = n) (hd : s.env done = n - rs'.length) (hl : rs'.length ≤ n)
    (hrec : ∀ y ∈ rs', y.length = a ∧ ∀ z ∈ y, z < 2 ^ w) (hw : a + 1 < 2 ^ w)
    (hwr : rr + 1 < 2 ^ w) (hwn : n + 1 < 2 ^ w) :
    ∃ s', Good x w (pairBody X T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t r N done k) s s'
        ((rs'.length - (rs'.drop (2 * rr)).length + 1) * (240 * (a + 1) * Ex.nodeCost w)) ∧
      s'.stk = passStk S X Y (rs'.drop (2 * rr))
        (CSort.mrg d (rs'.take rr).reverse ((rs'.drop rr).take rr).reverse [] ++ Lacc) ∧
      s'.env done = n - (rs'.drop (2 * rr)).length ∧
      Frame s s' [k, done, i, t, c, kc, t1, t2, f1, f2] := by
  have hXT1 : X ≠ T1 := by ndup hstk
  have hXT2 : X ≠ T2 := by ndup hstk
  have hXY : X ≠ Y := by ndup hstk
  have hXt : X ≠ tmp := by ndup hstk
  have hT1Y : T1 ≠ Y := by ndup hstk
  have hT2Y : T2 ≠ Y := by ndup hstk
  have hT12 : T1 ≠ T2 := by ndup hstk
  have hmreg : [A, r, done, N, k, i, t].Nodup := by nodupT hreg
  have hgreg : [A, dir, c, f1, f2, kc, t1, t2, i, t].Nodup := by nodupT hreg
  have hgstk : [T1, T2, Y, tmp, C1, C2].Nodup := by nodupT hstk
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have hsX : s.stk X = rs'.flatten ++ [] := by
    rw [hs]; simp [passStk, Function.update_of_ne hXY]
  -- the first run
  obtain ⟨s1, g1, k1, d1, fr1⟩ := mvRecsB_good (x := x) hw2 (src := X) (dst := T1) (tmp := tmp)
    (by ndup hstk) (by ndup hstk) hXT1 hmreg s rs' [] ha hr hn hd (by omega) hsX
    hrec (by omega) hw hwr hwn
  set m1 := min rr (n - (n - rs'.length)) with hm1
  have hm1' : m1 = min rr rs'.length := by rw [hm1]; congr 1; omega
  have e1 : ∀ q, q ∉ [k, done, i, t] → s1.env q = s.env q := fun q hq => fr1.2.2 q hq
  have hA1 : s1.env A = a := by rw [e1 A (by nmem hreg), ha]
  have hr1' : s1.env r = rr := by rw [e1 r (by nmem hreg), hr]
  have hn1 : s1.env N = n := by rw [e1 N (by nmem hreg), hn]
  have hsX1 : s1.stk X = (rs'.drop m1).flatten ++ [] := by
    rw [k1]; simp [recsStk, Function.update_of_ne hXT1]
  have hlen1 : (rs'.drop m1).length = rs'.length - m1 := List.length_drop
  have hm1le : m1 ≤ rs'.length := by rw [hm1']; exact min_le_right _ _
  -- the second run
  obtain ⟨s2, g2, k2, d2, fr2⟩ := mvRecsB_good (x := x) hw2 (src := X) (dst := T2) (tmp := tmp)
    (by ndup hstk) (by ndup hstk) hXT2 hmreg s1 (rs'.drop m1) [] hA1 hr1' hn1 d1 (by omega)
    hsX1 (fun y hy => hrec y (List.mem_of_mem_drop hy)) (by rw [hlen1]; omega) hw hwr hwn
  set m2 := min rr (n - (n - rs'.length + m1)) with hm2
  have hm2' : m2 = min rr (rs'.drop m1).length := by rw [hm2, hlen1]; congr 1; omega
  have e2 : ∀ q, q ∉ [k, done, i, t] → s2.env q = s1.env q := fun q hq => fr2.2.2 q hq
  have hA2 : s2.env A = a := by rw [e2 A (by nmem hreg), hA1]
  have hdir2 : s2.env dir = if d then 1 else 0 := by
    rw [e2 dir (by nmem hreg), e1 dir (by nmem hreg), hdir]
  have hm2le : m2 ≤ (rs'.drop m1).length := by rw [hm2']; exact min_le_right _ _
  -- the stacks before the merge
  set u := (rs'.take m1).reverse
  set v := ((rs'.drop m1).take m2).reverse
  have hs2T1 : s2.stk T1 = u.flatten := by
    rw [k2]; simp only [recsStk, Function.update_of_ne hT12, Function.update_of_ne hXT1.symm]
    rw [k1]; simp [recsStk, hs, passStk, Function.update_of_ne hT1Y, Function.update_of_ne hXT1.symm, hT1, u]
  have hs2T2 : s2.stk T2 = v.flatten := by
    rw [k2]; simp only [recsStk, Function.update_self]
    rw [k1]; simp [recsStk, hs, passStk, Function.update_of_ne hT2Y, Function.update_of_ne hXT2.symm,
      Function.update_of_ne hT12.symm, hT2, v]
  have hs2m : s2.stk = mrgStk s2.stk T1 T2 Y u v [] := by
    funext q
    simp only [mrgStk, Function.update_apply, List.flatten_nil, List.nil_append]
    split_ifs with h1 h2 h3
    · rw [h1]
    · rw [h2, hs2T2]
    · rw [h3, hs2T1]
    · rfl
  -- the merge
  obtain ⟨s3, g3, k3, fr3⟩ := mrgS_good (x := x) (tmp := tmp) (C1 := C1) (C2 := C2) (c := c)
    (f1 := f1) (f2 := f2) (kc := kc) (t1 := t1) (t2 := t2) (i := i) (t := t) hw2 hgstk hgreg
    s2.stk d s2 u v [] hA2 ha1 hdir2 hs2m
    (fun y hy => by
      simp only [List.mem_append, List.mem_reverse, u, v] at hy
      rcases hy with hy | hy
      · exact hrec y (List.mem_of_mem_take hy)
      · exact hrec y (List.mem_of_mem_drop (List.mem_of_mem_take hy))) hw
  -- the list identities
  have htu : rs'.take m1 = rs'.take rr := by rw [hm1']; exact take_min_len rs' rr
  have hdu : rs'.drop m1 = rs'.drop rr := by rw [hm1']; exact drop_min_len rs' rr
  have htv : (rs'.drop m1).take m2 = (rs'.drop rr).take rr := by
    rw [hm2', take_min_len, hdu]
  have hdv : (rs'.drop m1).drop m2 = rs'.drop (2 * rr) := by
    rw [hm2', drop_min_len, hdu, CSort.drop_drop_two]
  have hlen2 : ((rs'.drop m1).drop m2).length = (rs'.drop m1).length - m2 := List.length_drop
  refine ⟨s3, (g1.seq (g2.seq g3)).mono ?_, ?_, ?_, ?_⟩
  · simp only [u, v, List.length_reverse, List.length_take]
    rw [← hdv, hlen2, hlen1]
    have hmin1 : min m1 rs'.length = m1 := min_eq_left hm1le
    have hmin2 : min m2 (rs'.drop m1).length = m2 := min_eq_left hm2le
    have hmin2' : min m2 (rs'.length - m1) = m2 := by rw [← hlen1]; exact hmin2
    rw [hmin1, hmin2']
    have : rs'.length - (rs'.length - m1 - m2) = m1 + m2 := by rw [hlen1] at hm2le; omega
    rw [this]
    have key : 50 * (m1 + 1) + 50 * (m2 + 1) + 140 * (m1 + m2 + 1) ≤ 240 * (m1 + m2 + 1) := by
      omega
    calc _ = (50 * (m1 + 1) + 50 * (m2 + 1) + 140 * (m1 + m2 + 1)) *
          ((a + 1) * Ex.nodeCost w) := by ring
      _ ≤ (240 * (m1 + m2 + 1)) * ((a + 1) * Ex.nodeCost w) := Nat.mul_le_mul_right _ key
      _ = _ := by ring
  · rw [k3]
    funext q
    unfold mrgStk passStk
    by_cases hqY : q = Y
    · subst hqY
      simp only [Function.update_self, List.flatten_append, List.append_assoc]
      congr 1
      · simp only [u, v, htu, htv]
      · rw [k2]; simp only [recsStk, Function.update_of_ne hT2Y.symm, Function.update_of_ne hXY.symm]
        rw [k1]; simp [recsStk, Function.update_of_ne hT1Y.symm, Function.update_of_ne hXY.symm, hs,
          passStk]
    · by_cases hq2 : q = T2
      · subst hq2
        simp [Function.update_of_ne hqY, Function.update_of_ne hXT2.symm, hT2]
      · by_cases hq1 : q = T1
        · subst hq1
          simp [Function.update_of_ne hqY, Function.update_of_ne hq2, Function.update_of_ne hXT1.symm, hT1]
        · simp only [Function.update_of_ne hqY, Function.update_of_ne hq2, Function.update_of_ne hq1]
          rw [k2]; simp only [recsStk, Function.update_of_ne hq2]
          by_cases hqX : q = X
          · subst hqX; simp [hdv]
          · simp only [Function.update_of_ne hqX]
            rw [k1]; simp [recsStk, Function.update_of_ne hq1, Function.update_of_ne hqX, hs,
              passStk, Function.update_of_ne hqY]
  · rw [fr3.2.2 done (by nmem hreg), d2, ← hdv, hlen2, hlen1]
    rw [hlen1] at hm2le; omega
  · have s1 : [k, done, i, t] ⊆ [k, done, i, t, c, kc, t1, t2, f1, f2] := by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with h | h | h | h <;> simp [h]
    have s3 : [c, kc, t1, t2, i, t, f1, f2] ⊆ [k, done, i, t, c, kc, t1, t2, f1, f2] := by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with h | h | h | h | h | h | h | h <;> simp [h]
    exact (fr1.mono s1).trans ((fr2.mono s1).trans (fr3.mono s3))

/-- One merge pass with run length `r` on the `N` records of `X`. -/
def passS (X T1 T2 Y tmp C1 C2 : Fin Q) (A dir c f1 f2 kc t1 t2 i t r N done k lim2 : Fin R) :
    CStm R Q :=
  .seq (.set done (.const 0))
    (.seq (.loop (.lt (rv done) (rv N))
        (pairBody X T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t r N done k))
      (.seq (.set done (.const 0)) (.seq (.set lim2 (rv N))
        (mvRecsB Y X tmp A lim2 done N k i t))))

set_option maxHeartbeats 1000000 in
/-- **One merge pass.** -/
lemma passS_good (hw2 : 2 ≤ w) (hstk : [X, T1, T2, Y, tmp, C1, C2].Nodup)
    (hreg : [A, dir, c, f1, f2, kc, t1, t2, i, t, r, N, done, k, lim2].Nodup)
    (d : Bool) (s : NSt R Q) {a rr n : ℕ} (rs : List (List ℕ))
    (hX : s.stk X = rs.flatten) (hT1 : s.stk T1 = []) (hT2 : s.stk T2 = [])
    (ha : s.env A = a) (ha1 : 1 ≤ a)
    (hdir : s.env dir = if d then 1 else 0) (hr : s.env r = rr) (hr1 : 1 ≤ rr)
    (hn : s.env N = n) (hl : rs.length = n)
    (hrec : ∀ y ∈ rs, y.length = a ∧ ∀ z ∈ y, z < 2 ^ w) (hw : a + 1 < 2 ^ w)
    (hwr : rr + 1 < 2 ^ w) (hwn : n + 1 < 2 ^ w) :
    ∃ s', Good x w (passS X T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t r N done k lim2) s s'
        ((n + 1) * (600 * (a + 1) * Ex.nodeCost w)) ∧
      s'.stk = Function.update s.stk X (CSort.passX d rr rs).flatten ∧
      Frame s s' [k, done, i, t, c, kc, t1, t2, f1, f2, lim2] := by
  have hXY : X ≠ Y := by ndup hstk
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 := two_le_pow hw2
  have hpreg : [A, dir, c, f1, f2, kc, t1, t2, i, t, r, N, done, k].Nodup := by nodupT hreg
  have hmreg : [A, lim2, done, N, k, i, t].Nodup := by nodupT hreg
  set S := s.stk
  set regs : List (Fin R) := [k, done, i, t, c, kc, t1, t2, f1, f2, lim2] with hregs
  set K := 240 * (a + 1) * Ex.nodeCost w
  -- the pair loop
  set Inv : NSt R Q → Prop := fun s₁ => ∃ rs' Lacc, s₁.stk = passStk S X Y rs' Lacc ∧
    (CSort.passX d rr rs').reverse ++ Lacc = (CSort.passX d rr rs).reverse ∧
    (∀ y ∈ rs', y ∈ rs) ∧ s₁.env done = n - rs'.length ∧ rs'.length ≤ n ∧
    s₁.env A = a ∧ s₁.env dir = (if d then 1 else 0) ∧ s₁.env r = rr ∧ s₁.env N = n ∧
    Frame s s₁ regs
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv done) (rv N))
    (body := pairBody X T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t r N done k)
    Inv (fun s₁ => n - s₁.env done) (fun s₁ => n - s₁.env done) K K (by
      intro s₁ hI
      obtain ⟨rs', Lacc, hs₁, hp, hsub, hd, hle, hA, hdr, hrr, hN, hfr⟩ := hI
      refine ⟨⟨show s₁.env done < 2 ^ w by omega, show s₁.env N < 2 ^ w by omega⟩, ?_⟩
      intro hc
      have hne : rs' ≠ [] := by
        rintro rfl
        apply hc; simp [rv, Ex.eval, hd, hN]
      obtain ⟨s₂, g, k₂, d₂, fr⟩ := pairBody_good (x := x) (C1 := C1) (C2 := C2) (c := c)
        (f1 := f1) (f2 := f2) (kc := kc) (t1 := t1) (t2 := t2) (i := i) (t := t)
        hw2 hstk hpreg S
        (by simp [S, hT1]) (by simp [S, hT2]) d s₁ rs' Lacc hne hs₁ hA ha1 hdr hrr hr1 hN hd hle
        (fun y hy => hrec y (hsub y hy)) hw hwr hwn
      have hlt : (rs'.drop (2 * rr)).length < rs'.length := by
        have : rs'.length ≠ 0 := by simpa using hne
        simp; omega
      have hfr' : ∀ q, q ∉ [k, done, i, t, c, kc, t1, t2, f1, f2] → s₂.env q = s₁.env q :=
        fun q hq => fr.2.2 q hq
      refine ⟨s₂, g.mono (le_of_eq ?_), ⟨rs'.drop (2 * rr), _, k₂, ?_, ?_, d₂, by omega,
        by rw [hfr' A (by nmem hreg), hA], by rw [hfr' dir (by nmem hreg), hdr],
        by rw [hfr' r (by nmem hreg), hrr], by rw [hfr' N (by nmem hreg), hN],
        hfr.trans (fr.mono (by
          intro q hq; simp only [hregs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
          rcases hq with h | h | h | h | h | h | h | h | h | h <;> simp [h]))⟩, ?_, ?_⟩
      · rw [d₂, hd]
        have : (rs'.drop (2 * rr)).length ≤ rs'.length := by simp
        have e : n - (n - rs'.length) - (n - (n - (rs'.drop (2 * rr)).length)) =
            rs'.length - (rs'.drop (2 * rr)).length := by omega
        rw [e]; simp only [K]; ring
      · rw [← hp, CSort.passX_cons d (by omega) hne, List.reverse_append, List.reverse_reverse,
          List.append_assoc]
      · exact fun y hy => hsub y (List.mem_of_mem_drop hy)
      · rw [d₂, hd]; omega
      · rw [d₂, hd]; omega)
  -- initialization
  have g0 : Good x w (.set done (.const 0) : CStm R Q) s (s.set done 0)
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; omega)).of_eq (by simp [Ex.eval]) (by simp [Ex.size])
  have hne' : ∀ q, q ≠ done → (s.set done 0).env q = s.env q := fun q hq => by
    simp [Function.update_of_ne hq]
  have hI0 : Inv (s.set done 0) := by
    refine ⟨rs, [], ?_, by simp, fun y hy => hy, by simp [hl], by omega,
      by rw [hne' A (by ndup hreg), ha], by rw [hne' dir (by ndup hreg), hdir],
      by rw [hne' r (by ndup hreg), hr], by rw [hne' N (by ndup hreg), hn],
      ⟨rfl, rfl, fun q hq => hne' q (by intro h; subst h; simp [hregs] at hq)⟩⟩
    funext q
    simp only [NSt.set_stk, passStk, List.flatten_nil, List.nil_append, Function.update_apply]
    split_ifs with h1 h2
    · rw [h1]
    · rw [h2, ← hX]
    · rfl
  obtain ⟨s₁, g₁, ⟨rs', Lacc, hs₁, hp, hsub, hd, hle, hA, hdr, hrr, hN, hfr⟩, hend⟩ :=
    hloop _ hI0
  have hrs' : rs' = [] := by
    by_contra h
    have : rs'.length ≠ 0 := by simpa using h
    have hh : s₁.env N ≤ s₁.env done := by
      by_contra hh0; rw [not_le] at hh0; simp [rv, Ex.eval, hh0] at hend
    rw [hd, hN] at hh; omega
  subst hrs'
  simp only [CSort.passX_nil, List.reverse_nil, List.nil_append] at hp
  -- move back
  have g2 : Good x w (.set done (.const 0) : CStm R Q) s₁ (s₁.set done 0)
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; omega)).of_eq (by simp [Ex.eval]) (by simp [Ex.size])
  have g3 : Good x w (.set lim2 (rv N) : CStm R Q) (s₁.set done 0) ((s₁.set done 0).set lim2 n)
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [rv, Ex.Fits, NSt.set_env, Function.update_of_ne
      (show N ≠ done by ndup hreg), hN]; omega)).of_eq
      (by simp [rv, Ex.eval, Function.update_of_ne (show N ≠ done by ndup hreg), hN])
      (by simp [rv, Ex.size])
  set s₃ := (s₁.set done 0).set lim2 n
  have e3 : ∀ q, q ≠ done → q ≠ lim2 → s₃.env q = s₁.env q := fun q h1 h2 => by
    simp [s₃, Function.update_of_ne h1, Function.update_of_ne h2]
  have hY3 : s₃.stk Y = (CSort.passX d rr rs).reverse.flatten ++ S Y := by
    simp [s₃, hs₁, passStk, ← hp]
  have hlenP : (CSort.passX d rr rs).reverse.length = n := by
    simp [CSort.passX_length, hl]
  obtain ⟨s₄, g₄, k₄, d₄, fr₄⟩ := mvRecsB_good (x := x) hw2 (src := Y) (dst := X) (tmp := tmp)
    (by ndup hstk) (by ndup hstk) hXY.symm hmreg s₃ (CSort.passX d rr rs).reverse (S Y)
    (by rw [e3 A (by ndup hreg) (by ndup hreg), hA]) (by simp [s₃])
    (by rw [e3 N (by ndup hreg) (by ndup hreg), hN])
    (by simp [s₃, Function.update_of_ne (show done ≠ lim2 by ndup hreg)]) (Nat.zero_le _) hY3
    (fun y hy => hrec y ((CSort.passX_perm d rr rs).subset (List.mem_reverse.mp hy)))
    (by rw [hlenP]; omega) hw hwn hwn
  refine ⟨s₄, (g0.seq (g₁.seq (g2.seq (g3.seq g₄)))).mono ?_, ?_, ?_⟩
  · simp only [condCost, rv, Ex.size, NSt.set_env, Function.update_self, Nat.sub_zero, K]
    have hP : 1 ≤ (a + 1) * Ex.nodeCost w := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    have hmin : min n n = n := min_self n
    rw [hmin]
    have hN1 : Ex.nodeCost w ≤ (a + 1) * Ex.nodeCost w := Nat.le_mul_of_pos_left _ (by omega)
    set P := (a + 1) * Ex.nodeCost w
    have e1 : 240 * (a + 1) * Ex.nodeCost w = 240 * P := by ring
    rw [e1]
    have e2 : 600 * (a + 1) * Ex.nodeCost w = 600 * P := by ring
    rw [e2]
    have hNP : (1 + 1 + 1) * Ex.nodeCost w + 1 ≤ 4 * P := by omega
    have hnK : n * (240 * P + ((1 + 1 + 1) * Ex.nodeCost w + 1)) ≤ n * (244 * P) :=
      Nat.mul_le_mul_left _ (by omega)
    have hnK' : (n + 1) * (50 * P) = n * (50 * P) + 50 * P := by ring
    have hgoal : (n + 1) * (600 * P) = n * (600 * P) + 600 * P := by ring
    have : 240 * P * n = n * (240 * P) := by ring
    nlinarith
  · funext q
    rw [k₄]
    unfold recsStk
    have hdrop : (CSort.passX d rr rs).reverse.drop n = [] := List.drop_eq_nil_of_le (by omega)
    have htake : (CSort.passX d rr rs).reverse.take n = (CSort.passX d rr rs).reverse :=
      List.take_of_length_le (by omega)
    by_cases hqX : q = X
    · subst hqX
      simp [htake, s₃, hs₁, passStk, Function.update_of_ne hXY]
    · by_cases hqY : q = Y
      · subst hqY; simp [Function.update_of_ne hqX, hdrop, Function.update_of_ne hXY.symm]
      · simp [Function.update_of_ne hqX, Function.update_of_ne hqY, s₃, hs₁, passStk]
  · have s1 : [k, done, i, t] ⊆ regs := by
      intro q hq; simp only [hregs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with h | h | h | h <;> simp [h]
    refine hfr.trans (Frame.trans (show Frame s₁ s₃ regs from ⟨rfl, rfl, fun q hq => ?_⟩) (fr₄.mono s1))
    simp only [hregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    exact e3 q hq.2.1 hq.2.2.2.2.2.2.2.2.2.2

/-! ## Moving all records, reversing -/

/-- Move all `N` records of `src` onto `dst` (reversing the record order); `lim2 = N`. -/
def mvAllS (src dst tmp : Fin Q) (A N done k i t lim2 : Fin R) : CStm R Q :=
  .seq (.set done (.const 0)) (mvRecsB src dst tmp A lim2 done N k i t)

lemma mvAllS_good (hw2 : 2 ≤ w) {src dst : Fin Q} (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hsd : src ≠ dst) (hmreg : [A, lim2, done, N, k, i, t].Nodup) (s : NSt R Q) {a n : ℕ}
    (l : List (List ℕ)) (hS : s.stk src = l.flatten) (ha : s.env A = a)
    (hn : s.env N = n) (hl2 : s.env lim2 = n) (hl : l.length = n)
    (hrec : ∀ y ∈ l, y.length = a ∧ ∀ z ∈ y, z < 2 ^ w) (hw : a + 1 < 2 ^ w)
    (hwn : n + 1 < 2 ^ w) :
    ∃ s', Good x w (mvAllS src dst tmp A N done k i t lim2) s s'
        ((n + 1) * (60 * ((a + 1) * Ex.nodeCost w))) ∧
      s'.stk = Function.update (Function.update s.stk src []) dst
        (l.reverse.flatten ++ s.stk dst) ∧ Frame s s' [k, done, i, t] := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 := two_le_pow hw2
  have hdn : done ≠ N := by ndup hmreg
  have g0 : Good x w (.set done (.const 0) : CStm R Q) s (s.set done 0)
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; omega)).of_eq (by simp [Ex.eval]) (by simp [Ex.size])
  obtain ⟨s', g, k', d', fr⟩ := mvRecsB_good (x := x) hw2 hst htd hsd hmreg (s.set done 0) l []
    (by simp [Function.update_of_ne (show A ≠ done by ndup hmreg), ha])
    (by simp [Function.update_of_ne (show lim2 ≠ done by ndup hmreg), hl2])
    (by simp [Function.update_of_ne hdn.symm, hn]) (by simp) (Nat.zero_le _)
    (by simp [hS]) hrec (by rw [hl]; omega) hw hwn hwn
  refine ⟨s', (g0.seq g).mono ?_, ?_, ?_⟩
  · simp only [Nat.sub_zero, min_self]
    have : 1 ≤ (a + 1) * Ex.nodeCost w := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    have hN1 : Ex.nodeCost w ≤ (a + 1) * Ex.nodeCost w := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  · rw [k']
    simp only [Nat.sub_zero, min_self, recsStk, NSt.set_stk]
    rw [List.drop_eq_nil_of_le (by omega), List.take_of_length_le (by omega)]
    simp
  · refine (show Frame s (s.set done 0) [k, done, i, t] from ⟨rfl, rfl, fun q hq => ?_⟩).trans fr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [Function.update_of_ne hq.2.1]

/-- Reverse the record order of the `N` records on `X` (via `Y` and `T1`). -/
def revS (X T1 Y tmp : Fin Q) (A N done k i t lim2 : Fin R) : CStm R Q :=
  .seq (.set lim2 (rv N)) (.seq (mvAllS X Y tmp A N done k i t lim2)
    (.seq (mvAllS Y T1 tmp A N done k i t lim2) (mvAllS T1 X tmp A N done k i t lim2)))

lemma revS_good (hw2 : 2 ≤ w) (hstk : [X, T1, Y, tmp].Nodup)
    (hmreg : [A, lim2, done, N, k, i, t].Nodup) (s : NSt R Q) {a n : ℕ}
    (l : List (List ℕ)) (hX : s.stk X = l.flatten) (hT1 : s.stk T1 = []) (hY : s.stk Y = [])
    (ha : s.env A = a) (hn : s.env N = n) (hl : l.length = n)
    (hrec : ∀ y ∈ l, y.length = a ∧ ∀ z ∈ y, z < 2 ^ w) (hw : a + 1 < 2 ^ w)
    (hwn : n + 1 < 2 ^ w) :
    ∃ s', Good x w (revS X T1 Y tmp A N done k i t lim2) s s'
        ((n + 1) * (200 * ((a + 1) * Ex.nodeCost w))) ∧
      s'.stk = Function.update s.stk X l.reverse.flatten ∧ Frame s s' [k, done, i, t, lim2] := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have hXT : X ≠ T1 := by ndup hstk
  have hXY : X ≠ Y := by ndup hstk
  have hTY : T1 ≠ Y := by ndup hstk
  have hl2N : lim2 ≠ N := by ndup hmreg
  have g0 : Good x w (.set lim2 (rv N) : CStm R Q) s (s.set lim2 n)
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [rv, Ex.Fits, hn]; omega)).of_eq (by simp [rv, Ex.eval, hn])
      (by simp [rv, Ex.size])
  have hrec' : ∀ y ∈ l.reverse, y.length = a ∧ ∀ z ∈ y, z < 2 ^ w :=
    fun y hy => hrec y (List.mem_reverse.mp hy)
  have e0 : ∀ q, q ≠ lim2 → (s.set lim2 n).env q = s.env q := fun q hq => by
    simp [Function.update_of_ne hq]
  obtain ⟨s1, g1, k1, f1⟩ := mvAllS_good (x := x) hw2 (tmp := tmp) (by ndup hstk) (by ndup hstk)
    hXY hmreg (s.set lim2 n) l hX (by rw [e0 A (by ndup hmreg), ha])
    (by rw [e0 N hl2N.symm, hn]) (by simp) hl hrec hw hwn
  have e1 : ∀ q, q ∉ [k, done, i, t] → s1.env q = s.env q ∨ q = lim2 := fun q hq => by
    by_cases h : q = lim2
    · exact Or.inr h
    · exact Or.inl ((f1.2.2 q hq).trans (e0 q h))
  have hA1 : s1.env A = a := by
    rw [f1.2.2 A (by nmem hmreg), e0 A (by ndup hmreg), ha]
  have hN1 : s1.env N = n := by rw [f1.2.2 N (by nmem hmreg), e0 N hl2N.symm, hn]
  have hL1 : s1.env lim2 = n := by rw [f1.2.2 lim2 (by nmem hmreg)]; simp
  obtain ⟨s2, g2, k2, f2⟩ := mvAllS_good (x := x) hw2 (tmp := tmp) (by ndup hstk) (by ndup hstk)
    hTY.symm hmreg s1 l.reverse (by rw [k1]; simp [hY]) hA1 hN1 hL1 (by simp [hl]) hrec' hw hwn
  have hA2 : s2.env A = a := by rw [f2.2.2 A (by nmem hmreg), hA1]
  have hN2 : s2.env N = n := by rw [f2.2.2 N (by nmem hmreg), hN1]
  have hL2 : s2.env lim2 = n := by rw [f2.2.2 lim2 (by nmem hmreg), hL1]
  obtain ⟨s3, g3, k3, f3⟩ := mvAllS_good (x := x) hw2 (tmp := tmp) (by ndup hstk) (by ndup hstk)
    hXT.symm hmreg s2 l (by
      rw [k2]; simp [Function.update_of_ne hTY, k1, Function.update_of_ne hXT.symm, hT1])
    hA2 hN2 hL2 hl hrec hw hwn
  refine ⟨s3, (g0.seq (g1.seq (g2.seq g3))).mono ?_, ?_, ?_⟩
  · show _ ≤ _
    have : 1 ≤ (a + 1) * Ex.nodeCost w := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    have hN1 : Ex.nodeCost w ≤ (a + 1) * Ex.nodeCost w := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  · rw [k3, k2, k1]
    funext q
    by_cases hqX : q = X
    · subst hqX
      simp [Function.update_of_ne hXT, Function.update_of_ne hXY]
    · by_cases hqT : q = T1
      · subst hqT
        simp [Function.update_of_ne hqX, Function.update_of_ne hTY, hT1]
      · by_cases hqY : q = Y
        · subst hqY
          simp [Function.update_of_ne hqX, Function.update_of_ne hqT, hY]
        · simp [Function.update_of_ne hqX, Function.update_of_ne hqT, Function.update_of_ne hqY]
  · refine (show Frame s (s.set lim2 n) [k, done, i, t, lim2] from
      ⟨rfl, rfl, fun q hq => ?_⟩).trans ((f1.trans (f2.trans f3)).mono ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      exact e0 q hq.2.2.2.2
    · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; tauto

/-! ## The sort -/

/-- Sort the `N` records (of `A` words) on `X` (`CSort.rle`, smallest on top). -/
def sortS (X T1 T2 Y tmp C1 C2 : Fin Q) (A dir c f1 f2 kc t1 t2 i t r N done k lim2 : Fin R) :
    CStm R Q :=
  .seq (.set r (.const 1)) (.seq (.set dir (.const 0))
    (.seq (.loop (.lt (rv r) (rv N))
        (.seq (passS X T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t r N done k lim2)
          (.seq (.set r (.add (rv r) (rv r))) (.set dir (.lt (rv dir) (.const 1))))))
      (.ite (rv dir) (revS X T1 Y tmp A N done k i t lim2) .skip)))

lemma log_two_mul_le (n : ℕ) : Nat.log 2 (2 * n) ≤ Nat.log 2 n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]

set_option maxHeartbeats 2000000 in
/-- **Merge sort of records on a stack.** -/
theorem sortS_good (hw2 : 2 ≤ w) (hstk : [X, T1, T2, Y, tmp, C1, C2].Nodup)
    (hreg : [A, dir, c, f1, f2, kc, t1, t2, i, t, r, N, done, k, lim2].Nodup)
    (s : NSt R Q) {a n : ℕ} (rs : List (List ℕ))
    (hX : s.stk X = rs.flatten) (hT1 : s.stk T1 = []) (hT2 : s.stk T2 = []) (hY : s.stk Y = [])
    (ha : s.env A = a) (ha1 : 1 ≤ a) (hn : s.env N = n) (hl : rs.length = n)
    (hrec : ∀ y ∈ rs, y.length = a ∧ ∀ z ∈ y, z < 2 ^ w) (hw : a + 1 < 2 ^ w)
    (hwn : 2 * n + 1 < 2 ^ w) :
    ∃ s', Good x w (sortS X T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t r N done k lim2) s s'
        ((n + 1) * (Nat.log 2 n + 2) * (700 * (a + 1) * Ex.nodeCost w)) ∧
      s'.stk = Function.update s.stk X (rs.mergeSort CSort.rle).flatten ∧
      Frame s s' [k, done, i, t, c, kc, t1, t2, f1, f2, lim2, r, dir] := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 := two_le_pow hw2
  have hXT1 : X ≠ T1 := by ndup hstk
  have hXT2 : X ≠ T2 := by ndup hstk
  have hXY : X ≠ Y := by ndup hstk
  have hmreg : [A, lim2, done, N, k, i, t].Nodup := by nodupT hreg
  have hrstk : [X, T1, Y, tmp].Nodup := by nodupT hstk
  have hrd : r ≠ dir := by ndup hreg
  set S := s.stk
  set regs : List (Fin R) := [k, done, i, t, c, kc, t1, t2, f1, f2, lim2, r, dir] with hregs
  set P := (a + 1) * Ex.nodeCost w with hPdef
  have hP : 64 ≤ P := by
    have : Ex.nodeCost w ≤ P := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hNP : Ex.nodeCost w ≤ P := Nat.le_mul_of_pos_left _ (by omega)
  set K₀ := (n + 1) * (610 * P)
  set Inv : NSt R Q → Prop := fun s₁ => ∃ j, s₁.env r = 2 ^ j ∧ (j = 0 ∨ 2 ^ j < 2 * n) ∧
    s₁.env dir = (if CSort.dirOf j then 1 else 0) ∧
    s₁.stk = Function.update S X (CSort.passes rs j).flatten ∧ s₁.env A = a ∧ s₁.env N = n ∧
    Frame s s₁ regs
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv r) (rv N))
    (body := .seq (passS X T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t r N done k lim2)
      (.seq (.set r (.add (rv r) (rv r))) (.set dir (.lt (rv dir) (.const 1)))))
    Inv (fun s₁ => Nat.log 2 (2 * n) - Nat.log 2 (s₁.env r)) (fun _ => 0) 0 K₀ (by
      intro s₁ hI
      obtain ⟨j, hr, hj, hdir, hs₁, hA, hN, hfr⟩ := hI
      have hrw : 2 ^ j < 2 ^ w := by
        rcases hj with rfl | hj
        · simp; omega
        · omega
      refine ⟨⟨show s₁.env r < 2 ^ w by omega, show s₁.env N < 2 ^ w by omega⟩, ?_⟩
      intro hc
      have hjn : 2 ^ j < n := by
        by_contra hh; rw [not_lt] at hh
        apply hc; simp only [rv, Ex.eval, hr, hN]; rw [if_neg (by omega)]
      have hpl : (CSort.passes rs j).length = n := by
        rw [(CSort.passes_perm rs j).length_eq, hl]
      obtain ⟨s₂, g₂, k₂, f₂⟩ := passS_good (x := x) (C1 := C1) (C2 := C2) (c := c) (f1 := f1)
        (f2 := f2) (kc := kc) (t1 := t1) (t2 := t2) (i := i) (t := t) (k := k) (done := done)
        (lim2 := lim2) hw2 hstk hreg (CSort.dirOf j) s₁ (CSort.passes rs j)
        (by rw [hs₁]; simp) (by rw [hs₁]; simp [Function.update_of_ne hXT1.symm, S, hT1])
        (by rw [hs₁]; simp [Function.update_of_ne hXT2.symm, S, hT2]) hA ha1 hdir hr
        (Nat.one_le_two_pow) hN hpl
        (fun y hy => hrec y ((CSort.passes_perm rs j).subset hy)) hw (by omega) (by omega)
      have e2 : ∀ q, q ∉ [k, done, i, t, c, kc, t1, t2, f1, f2, lim2] → s₂.env q = s₁.env q :=
        fun q hq => f₂.2.2 q hq
      have hr2 : s₂.env r = 2 ^ j := by rw [e2 r (by nmem hreg), hr]
      have hdir2 : s₂.env dir = (if CSort.dirOf j then 1 else 0) := by
        rw [e2 dir (by nmem hreg), hdir]
      have g3 : Good x w (.set r (.add (rv r) (rv r)) : CStm R Q) s₂ (s₂.set r (2 ^ (j + 1)))
          (3 * Ex.nodeCost w + unitCost w) :=
        (Good.set (show (Ex.add (rv r) (rv r) : Ex R).Fits w s₂.env from
          ⟨show s₂.env r < 2 ^ w by omega, show s₂.env r < 2 ^ w by omega,
            show s₂.env r + s₂.env r < 2 ^ w by omega⟩)).of_eq
          (by simp [rv, Ex.eval, hr2, pow_succ]; ring_nf) (by simp [Ex.size])
      have hdir3 : (s₂.set r (2 ^ (j + 1))).env dir = (if CSort.dirOf j then 1 else 0) := by
        simp [Function.update_of_ne hrd.symm, hdir2]
      have g4 : Good x w (.set dir (.lt (rv dir) (.const 1)) : CStm R Q) (s₂.set r (2 ^ (j + 1)))
          ((s₂.set r (2 ^ (j + 1))).set dir (if CSort.dirOf (j + 1) then 1 else 0))
          (3 * Ex.nodeCost w + unitCost w) :=
        (Good.set (by
          simp only [rv, Ex.Fits, hdir3]; refine ⟨by split_ifs <;> omega, by omega⟩)).of_eq
          (by
            congr 1
            simp only [rv, Ex.eval, hdir3, CSort.dirOf_succ]
            cases CSort.dirOf j <;> simp) (by simp [Ex.size])
      refine ⟨_, (g₂.seq (g3.seq g4)).mono ?_, ⟨j + 1, by simp [Function.update_of_ne hrd],
        Or.inr (by rw [pow_succ]; omega), by simp, ?_, ?_, ?_, ?_⟩, ?_, le_rfl⟩
      · simp only [K₀, zero_mul, zero_add]
        have : (n + 1) * (600 * (a + 1) * Ex.nodeCost w) = (n + 1) * (600 * P) := by
          simp only [hPdef]; ring
        rw [this]
        nlinarith
      · simp only [NSt.set_stk, k₂, hs₁, Function.update_idem]
        rfl
      · simp [Function.update_of_ne (show A ≠ dir by ndup hreg),
          Function.update_of_ne (show A ≠ r by ndup hreg), e2 A (by nmem hreg), hA]
      · simp [Function.update_of_ne (show N ≠ dir by ndup hreg),
          Function.update_of_ne (show N ≠ r by ndup hreg), e2 N (by nmem hreg), hN]
      · refine hfr.trans (Frame.trans (f₂.mono ?_) ⟨rfl, rfl, fun q hq => ?_⟩)
        · intro q hq; simp only [hregs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
          tauto
        · simp only [hregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
          simp [Function.update_of_ne hq.2.2.2.2.2.2.2.2.2.2.2.1,
            Function.update_of_ne hq.2.2.2.2.2.2.2.2.2.2.2.2]
      · simp only [NSt.set_env, Function.update_of_ne hrd, Function.update_self]
        rw [hr, Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)]
        have : j + 1 ≤ Nat.log 2 (2 * n) :=
          Nat.le_log_of_pow_le (by norm_num) (by rw [pow_succ]; omega)
        omega)
  -- initialization
  have g0 : Good x w (.set r (.const 1) : CStm R Q) s (s.set r 1) (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; omega)).of_eq (by simp [Ex.eval]) (by simp [Ex.size])
  have g1 : Good x w (.set dir (.const 0) : CStm R Q) (s.set r 1) ((s.set r 1).set dir 0)
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; omega)).of_eq (by simp [Ex.eval]) (by simp [Ex.size])
  have hI0 : Inv ((s.set r 1).set dir 0) := by
    refine ⟨0, by simp [Function.update_of_ne hrd], Or.inl rfl, by simp [CSort.dirOf], ?_,
      by simp [Function.update_of_ne (show A ≠ dir by ndup hreg),
        Function.update_of_ne (show A ≠ r by ndup hreg), ha],
      by simp [Function.update_of_ne (show N ≠ dir by ndup hreg),
        Function.update_of_ne (show N ≠ r by ndup hreg), hn],
      ⟨rfl, rfl, fun q hq => ?_⟩⟩
    · simp only [NSt.set_stk, CSort.passes]; rw [← hX]; exact (Function.update_eq_self X S).symm
    · simp only [hregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp [Function.update_of_ne hq.2.2.2.2.2.2.2.2.2.2.2.1,
        Function.update_of_ne hq.2.2.2.2.2.2.2.2.2.2.2.2]
  obtain ⟨s₁, g₁, ⟨p, hr, hj, hdir, hs₁, hA, hN, hfr⟩, hend⟩ := hloop _ hI0
  have hnp : n ≤ 2 ^ p := by
    by_contra hh; rw [not_le] at hh
    simp [rv, Ex.eval, hr, hN, hh] at hend
  have hfinal := CSort.finalRecs_eq rs (p := p) (by omega)
  have hpl : (CSort.passes rs p).length = n := by
    rw [(CSort.passes_perm rs p).length_eq, hl]
  have hμ0 : Nat.log 2 (2 * n) - Nat.log 2 (((s.set r 1).set dir 0).env r) ≤ Nat.log 2 n + 1 := by
    simp [Function.update_of_ne hrd]; exact log_two_mul_le n
  -- the final orientation
  have hdv : (rv dir : Ex R).Fits w s₁.env := by
    show s₁.env dir < 2 ^ w; rw [hdir]; split_ifs <;> omega
  obtain ⟨s', g', k', f', hc'⟩ : ∃ s', Good x w (.ite (rv dir) (revS X T1 Y tmp A N done k i t lim2)
      .skip) s₁ s' (Ex.nodeCost w + 1 + (n + 1) * (200 * P)) ∧
      s'.stk = Function.update S X (CSort.finalRecs rs p).flatten ∧
      Frame s₁ s' [k, done, i, t, lim2] ∧ True := by
    by_cases hd : CSort.dirOf p
    · obtain ⟨s', g', k', f'⟩ := revS_good (x := x) hw2 hrstk hmreg s₁ (CSort.passes rs p)
        (by rw [hs₁]; simp) (by rw [hs₁]; simp [Function.update_of_ne hXT1.symm, S, hT1])
        (by rw [hs₁]; simp [Function.update_of_ne hXY.symm, S, hY]) hA hN hpl
        (fun y hy => hrec y ((CSort.passes_perm rs p).subset hy)) hw (by omega)
      refine ⟨s', (Good.iteT hdv (by simp [rv, Ex.eval, hdir, hd]) g').mono
        (by simp only [condCost, rv, Ex.size]; rw [← hPdef]; omega), ?_, f', trivial⟩
      rw [k', hs₁, Function.update_idem]; simp [CSort.finalRecs, hd]
    · refine ⟨s₁, (Good.iteF hdv (by simp [rv, Ex.eval, hdir, hd]) Good.skip).mono
        (by simp only [condCost, rv, Ex.size]; nlinarith), ?_, Frame.refl _ _, trivial⟩
      rw [hs₁]; simp [CSort.finalRecs, hd]
  refine ⟨s', (g0.seq (g1.seq (g₁.seq g'))).mono ?_, ?_, ?_⟩
  · simp only [condCost, rv, Ex.size, K₀, mul_zero, zero_add, zero_mul]
    set L := Nat.log 2 n
    set μ := Nat.log 2 (2 * n) - Nat.log 2 (((s.set r 1).set dir 0).env r)
    have h1 : μ * ((n + 1) * (610 * P) + ((1 + 1 + 1) * Ex.nodeCost w + 1)) ≤
        (L + 1) * ((n + 1) * (620 * P)) := by
      apply Nat.mul_le_mul hμ0
      nlinarith
    have e : (n + 1) * (L + 2) * (700 * (a + 1) * Ex.nodeCost w) =
        (L + 1) * ((n + 1) * (700 * P)) + (n + 1) * (700 * P) := by
      simp only [hPdef]; ring
    rw [e]
    have h2 : (L + 1) * ((n + 1) * (620 * P)) ≤ (L + 1) * ((n + 1) * (700 * P)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have h3 : (n + 1) * (200 * P) + 10 * P ≤ (n + 1) * (700 * P) := by nlinarith
    omega
  · rw [k', hfinal]; rfl
  · refine hfr.trans (f'.mono ?_)
    intro q hq; simp only [hregs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; tauto

end Pass

end CStm

end Lax119563Proofs.Compiler

end Compiler_CSortMain

/-! ### Formerly `Lax119563Proofs.Compiler.NMachine` -/

section Compiler_NMachine

/-!
# Machines computing the output of register programs with number stacks

Copy-generalised from `Reduction.HMachine`.

`NProg.machine p` runs the compiled program `p` and then moves the output to tape `0`
(popping the input tape once per output symbol, so that the head returns to cell `0` after
the output has been pushed). `NProg.computesWithin`: if `p` runs from the zero state to a
state with cursor `0` that has emitted `out`, with `|x| ≤ |encodeNats out|`, then the machine
computes `encodeNats out` from `x` within the cost of the run plus `O(|encodeNats out|)`.
-/

open Function Lax119563.BinaryEncodings Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Compiler

open Hierarchy Hierarchy.Prog Lax119563Proofs.Reduction Lax119563Proofs.Reduction.Prog

variable {R Q : ℕ}

/-- Move the reversed output from `t₀` to `t₁`, popping the input tape once per symbol. -/
def countLoopN : Hierarchy.Prog (R + Q + 7) 0 :=
  .loop (fun t => (t nT0).isSome) (.seq (moveOne nT0 nT1) (.pop nIo))

lemma countLoopN_runsH : ∀ (l : List Sym) (S : Stacks (R + Q + 7) 0) (hd : Fin (R + Q + 7) → ℤ),
    S nT0 = l →
    ∃ hd' : Fin (R + Q + 7) → ℤ, hd' nIo = hd nIo + l.length ∧
      RunsLeH countLoopN (S, hd)
        (update (update (update S nT0 []) nT1 (l.reverse ++ S nT1)) nIo
          ((S nIo).drop l.length), hd') (7 * l.length + 1)
  | [], S, hd, hS => by
    refine ⟨hd, by simp, (RunsLeH.loopF (by simp [tops, hS])).of_eq ?_ (by simp)⟩
    refine Prod.ext ?_ rfl
    funext k; simp only [update_apply]; split_ifs <;> simp_all
  | a :: l, S, hd, hS => by
    have h01 : (nT0 : Fin (R + Q + 7)) ≠ nT1 := by ndist
    have h0i : (nT0 : Fin (R + Q + 7)) ≠ nIo := by ndist
    have h1i : (nT1 : Fin (R + Q + 7)) ≠ nIo := by ndist
    have r₁ := moveOne_runsH h01 (hd := hd) hS
    set S₁ := update (update S nT0 l) nT1 (a :: S nT1)
    set hd₁ := update (update hd nT0 (hd nT0 + 1)) nT1 (hd nT1 - 1)
    have r₂ : RunsLeH (.pop nIo) (S₁, hd₁)
        (update S₁ nIo (S₁ nIo).tail, update hd₁ nIo (hd₁ nIo + 1)) 1 := ⟨1, le_rfl, .pop⟩
    obtain ⟨hd', e', r₃⟩ := countLoopN_runsH l (update S₁ nIo (S₁ nIo).tail)
      (update hd₁ nIo (hd₁ nIo + 1)) (by simp [S₁, update_of_ne h0i, update_of_ne h01])
    refine ⟨hd', ?_, (RunsLeH.loopT (by simp [tops, hS]) (r₁.seq r₂) r₃).of_eq ?_ ?_⟩
    · rw [e']
      simp [hd₁, update_of_ne h0i.symm, update_of_ne h1i.symm]; ring
    · refine Prod.ext ?_ rfl
      have e1 : S₁ nIo = S nIo := by simp [S₁, update_of_ne h0i.symm, update_of_ne h1i.symm]
      funext k
      simp only [update_apply, S₁] at *
      split_ifs <;> simp_all [List.drop_tail]
    · simp; omega

lemma encN_init (x : List Bool) :
    encN x (⟨fun _ => 0, fun _ => [], 0, []⟩ : NSt R Q) = inputStacks (R + Q + 6) 0 x := by
  funext i
  unfold encN inputStacks
  by_cases h0 : i = 0
  · subst h0; simp [bs, sym, bitSym]
  · have : i.val ≠ 0 := fun e => h0 (Fin.ext e)
    simp [h0, this, encodeNats]

end Lax119563Proofs.Compiler

end Compiler_NMachine

/-! ### Formerly `Lax119563Proofs.Compiler.NOutput` -/

section Compiler_NOutput

/-!
# Machines of register programs with outputs shorter than the input

`NProg.computesWithin` (`Compiler.NMachine`) needs `|x| ≤ |encodeNats out|`: in the stack
model a pop moves the head right and a push moves it left and writes, so a stack program
cannot move the head of tape `0` left over the erased input without leaving symbols behind.

`NProg.machineO p` removes this condition (and the condition that the cursor is back at `0`):
1. the stack program `outP₁ p` runs `compileN p`, moves the output to helper `nT0`, and drains
   the unread input (stack `nIo`) and the read input (stack `nXl`), pushing one unary symbol
   per symbol onto helper `nT1`; now stack `nIo` is empty and its head is at `|x|`;
2. the raw machine `leftLoop` pops `nT1` and moves the head of tape `0` left once per
   symbol (`rep_moveL`: an empty stack is represented with any head position), so the head of
   tape `0` is back at `0`;
3. the stack program `outP₂` moves the output to `nT1` while popping the empty stack `nIo`
   (moving its head to `|y|`) and pushes it back onto `nIo` (moving the head to `0`).

**`NProg.computesWithinO`**: every run of `p` from the zero state gives a computation of
`encodeNats out` within `t + 20 (|x| + |encodeNats out|) + 10` steps.
-/

open Function Lax119563.BinaryEncodings Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Compiler

open Hierarchy Hierarchy.Prog Lax119563Proofs.Reduction Lax119563Proofs.Reduction.Prog

variable {R Q : ℕ}

/-! ## Draining a stack into a unary counter -/

/-- Pop stack `i` completely, pushing one symbol `0` onto `j` per popped symbol. -/
def drainP {K : ℕ} (i j : Fin K) : Hierarchy.Prog K 0 :=
  .loop (fun t => (t i).isSome) (.seq (.pop i) (.push j 0))

lemma drainP_runsH {K : ℕ} {i j : Fin K} (hij : i ≠ j) :
    ∀ (l : List (Fin 2)) (s : Stacks K 0) (hd : Fin K → ℤ), s i = l →
      RunsLeH (drainP i j) (s, hd)
        (update (update s i []) j (unary 0 l.length ++ s j),
          update (update hd i (hd i + l.length)) j (hd j - l.length))
        (4 * l.length + 1)
  | [], s, hd, hs => by
    refine (RunsLeH.loopF (p := .seq (.pop i) (.push j 0)) (c := fun r => (r i).isSome)
      (x := (s, hd)) (by simp [tops, hs])).of_eq ?_ (by simp)
    refine Prod.ext ?_ ?_
    · funext k; simp only [update_apply]; split_ifs <;> simp_all
    · funext k; simp only [update_apply]; split_ifs <;> simp_all
  | a :: l, s, hd, hs => by
    have h1 : RunsLeH (.seq (.pop i) (.push j 0)) (s, hd)
        (update (update s i (s i).tail) j (0 :: update s i (s i).tail j),
          update (update hd i (hd i + 1)) j (update hd i (hd i + 1) j - 1)) 3 :=
      ⟨3, le_rfl, .seq .pop .push⟩
    have e1 : update (update s i (s i).tail) j (0 :: update s i (s i).tail j) =
        update (update s i l) j (0 :: s j) := by
      rw [hs, update_of_ne hij.symm]; rfl
    have e2 : update (update hd i (hd i + 1)) j (update hd i (hd i + 1) j - 1) =
        update (update hd i (hd i + 1)) j (hd j - 1) := by
      rw [update_of_ne hij.symm]
    rw [e1, e2] at h1
    have h2 := drainP_runsH hij l (update (update s i l) j (0 :: s j))
      (update (update hd i (hd i + 1)) j (hd j - 1)) (by simp [update_of_ne hij])
    refine (RunsLeH.loopT (c := fun r => (r i).isSome) (by simp [tops, hs]) h1 h2).of_eq ?_
      (by simp only [List.length_cons]; omega)
    refine Prod.ext ?_ ?_
    · funext k; simp only [update_apply]
      split_ifs <;> simp_all [List.replicate_succ']
    · funext k
      simp only [update_apply, List.length_cons]
      split_ifs <;> simp_all <;> ring

/-! ## Moving the head of an empty stack -/

lemma rep_moveL {K : ℕ} {s : Stacks K 0} {T : Tapes K (Fin (0 + 3))} (h : Rep s T) {i : Fin K}
    (hs : s i = []) : Rep s (T.apply (pushL i T.read).1 (pushL i T.read).2) := by
  intro j z
  have ht : (T.apply (pushL i T.read).1 (pushL i T.read).2).tape j z = T.tape j z := by
    simp only [Tapes.apply, pushL, Tapes.read]
    split_ifs with hz <;> simp [hz]
  rw [ht, h j z]
  by_cases hj : j = i
  · subst hj; simp [hs]
  · simp [Tapes.apply, pushL, hj, Lax489179.TuringMachine.Move.offset]

lemma head_moveL {K : ℕ} (T : Tapes K (Fin (0 + 3))) (i : Fin K) :
    (T.apply (pushL i T.read).1 (pushL i T.read).2).head = update T.head i (T.head i - 1) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [pushL, Tapes.apply, Lax489179.TuringMachine.Move.offset]; ring
  · simp [pushL, Tapes.apply, Lax489179.TuringMachine.Move.offset, hj]

/-- Pop the unary counter `c` and move the head of tape `i` left, until `c` is empty. -/
def leftLoop {K : ℕ} (i c : Fin K) : Mach K (Fin (0 + 3)) (Option (Unit ⊕ Unit)) :=
  Mach.loop (fun r => (decSym (r c)).isSome)
    (Mach.seq (Mach.prim (popA c)) (Mach.prim (pushL i)) ()) (.inl ())

lemma leftLoop_ends {K : ℕ} {i c : Fin K} (hic : i ≠ c) :
    ∀ (n : ℕ) (s : Stacks K 0) (T : Tapes K (Fin (0 + 3))), Rep s T → s i = [] → s c = unary 0 n →
      ∃ T', Rep (update s c []) T' ∧
        T'.head = update (update T.head c (T.head c + n)) i (T.head i - n) ∧
        (leftLoop i c).Ends none T none T' (3 * n + 1)
  | 0, s, T, hT, _, hc => by
    refine ⟨T, ?_, ?_, Mach.loop_false ?_⟩
    · rw [show ([] : List (Fin (0 + 2))) = s c by rw [hc]; rfl, update_eq_self]; exact hT
    · funext j; simp only [update_apply]; split_ifs <;> simp_all
    · have := congrFun hT.tops c
      simp only [tops, hc] at this
      simp [Tapes.read] at this ⊢; simpa using this
  | n + 1, s, T, hT, hi, hc => by
    -- the body: pop the counter, move the head of tape `i` left
    set T₁ := T.apply (popA c T.read).1 (popA c T.read).2
    have h₁ : Rep (update s c (s c).tail) T₁ := rep_pop hT c
    set T₂ := T₁.apply (pushL i T₁.read).1 (pushL i T₁.read).2
    have hi₁ : update s c (s c).tail i = [] := by rw [update_of_ne hic, hi]
    have h₂ : Rep (update s c (s c).tail) T₂ := rep_moveL h₁ hi₁
    have hb : (Mach.seq (Mach.prim (popA c)) (Mach.prim (pushL i)) ()).Ends (.inl ()) T none T₂ 2 :=
      Mach.seq_left_exit (Mach.prim_ends _ _) (Mach.prim_ends _ _)
    have hc' : update s c (s c).tail c = unary 0 n := by
      rw [update_self, hc]; rfl
    obtain ⟨T', h', hh', he'⟩ := leftLoop_ends hic n (update s c (s c).tail) T₂ h₂ hi₁ hc'
    refine ⟨T', ?_, ?_, ?_⟩
    · simpa using h'
    · rw [hh', head_moveL, head_pop]
      funext j; simp only [update_apply]
      split_ifs <;> simp_all <;> ring
    · have hcond : (fun r : Fin K → Fin (0 + 3) => (decSym (r c)).isSome) T.read = true := by
        have := congrFun hT.tops c
        simp only [tops, hc] at this
        simp only [this]; simp
      rw [show 3 * (n + 1) + 1 = 2 + (3 * n + 1) + 1 by ring]
      exact Mach.loop_true hcond hb he'

/-! ## The machine -/

/-- Phase 1: run the program, move the output to `nT0`, drain the input into `nT1`. -/
def outP₁ (p : NProg R Q) : Hierarchy.Prog (R + Q + 7) 0 :=
  .seq (compileN p) (.seq (moveAll nOut nT0) (.seq (drainP nIo nT1) (drainP nXl nT1)))

/-- Phase 3: move the output to `nT1` popping (the empty) `nIo`, then push it onto `nIo`. -/
def outP₂ : Hierarchy.Prog (R + Q + 7) 0 := .seq countLoopN (moveAll nT1 nIo)

/-- The three phases followed by halting. -/
def machOMach (p : NProg R Q) :=
  Mach.seq (Mach.seq (Mach.seq (outP₁ p).compile (leftLoop nIo nT1) none)
    (outP₂ (R := R) (Q := Q)).compile (outP₂ (R := R) (Q := Q)).start)
    (Mach.haltWith (k := R + Q + 7) (Γ := Fin (0 + 3)) (fun _ => false)) ()

/-- The machine of a register program, for outputs of any length. -/
noncomputable def NProg.machineO (p : NProg R Q) : Machine :=
  Mach.toMachine (n := R + Q + 6) (m := 0) (machOMach p) (.inl (.inl (.inl (outP₁ p).start)))

lemma NProg.machineO_deterministic (p : NProg R Q) : Deterministic p.machineO :=
  Mach.toMachine_deterministic _ _

/-- **Machines of register programs, outputs of any length.** -/
theorem NProg.computesWithinO {p : NProg R Q} {x : List Bool} {w t : ℕ} {st' : NSt R Q}
    (h : NRuns x w p ⟨fun _ => 0, fun _ => [], 0, []⟩ st' t) :
    ComputesWithin p.machineO x (encodeNats st'.out)
      (t + 20 * (x.length + (encodeNats st'.out).length) + 10) := by
  set y := encodeNats st'.out
  have hpos : st'.pos ≤ x.length := h.pos_le (by simp)
  have hoi : (nOut : Fin (R + Q + 7)) ≠ nIo := by ndist
  have h0i : (nT0 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have h1i : (nT1 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have ho0 : (nOut : Fin (R + Q + 7)) ≠ nT0 := by ndist
  have ho1 : (nOut : Fin (R + Q + 7)) ≠ nT1 := by ndist
  have h01 : (nT0 : Fin (R + Q + 7)) ≠ nT1 := by ndist
  have hx1 : (nXl : Fin (R + Q + 7)) ≠ nT1 := by ndist
  have hxi : (nXl : Fin (R + Q + 7)) ≠ nIo := by ndist
  have hx0 : (nXl : Fin (R + Q + 7)) ≠ nT0 := by ndist
  have hxo : (nXl : Fin (R + Q + 7)) ≠ nOut := by ndist
  -- phase 1
  obtain ⟨hd₁, e₁, r₁⟩ := compileN_runs h (by simp) (fun _ => 0) (by simp)
  have a₂ := moveAll_runs ho0 (m := 0) ((bs y).reverse) (encN x st') (encN_out x st')
  obtain ⟨hd₂, e₂, r₂⟩ := RunsLe.toH a₂ (avoids_moveAll hoi h0i) hd₁
  set S₂ := update (update (encN x st') nOut []) nT0 ((bs y).reverse.reverse ++ encN x st' nT0)
  have r₃ := drainP_runsH h1i.symm (bs (x.drop st'.pos)) S₂ hd₂
    (by simp [S₂, update_of_ne hoi.symm, update_of_ne h0i.symm])
  set S₃ := update (update S₂ nIo []) nT1 (unary 0 (bs (x.drop st'.pos)).length ++ S₂ nT1)
  set hd₃ := update (update hd₂ nIo (hd₂ nIo + ((bs (x.drop st'.pos)).length : ℤ))) nT1
    (hd₂ nT1 - ((bs (x.drop st'.pos)).length : ℤ))
  have r₄ := drainP_runsH hx1 ((bs (x.take st'.pos)).reverse) S₃ hd₃
    (by simp [S₃, S₂, update_of_ne hx1, update_of_ne hxi, update_of_ne hx0, update_of_ne hxo])
  set S₄ := update (update S₃ nXl []) nT1
    (unary 0 (bs (x.take st'.pos)).reverse.length ++ S₃ nT1)
  set hd₄ := update (update hd₃ nXl (hd₃ nXl + ((bs (x.take st'.pos)).reverse.length : ℤ))) nT1
    (hd₃ nT1 - ((bs (x.take st'.pos)).reverse.length : ℤ))
  obtain ⟨t₁, ht₁, R₁⟩ := r₁.seq (r₂.seq (r₃.seq r₄))
  rw [encN_init] at R₁
  obtain ⟨T₁, hT₁, hH₁, E₁⟩ := Prog.compile_endsH (p := outP₁ p) R₁ (rep_input _ 0 x) rfl
  have hS₄io : S₄ nIo = [] := by
    simp [S₄, S₃, update_of_ne hxi.symm, update_of_ne h1i.symm]
  have hS₄t1 : S₄ nT1 = unary 0 x.length := by
    simp only [S₄, S₃, S₂, update_self, update_of_ne h01.symm, update_of_ne ho1.symm,
      encN_t1, List.append_nil, List.length_reverse, length_bs,
      List.length_take, List.length_drop]
    rw [List.replicate_append_replicate]; congr 1; omega
  have hd₄io : hd₄ nIo = x.length := by
    simp only [hd₄, hd₃, update_of_ne hxi.symm, update_of_ne h1i.symm, update_self, e₂, e₁,
      length_bs, List.length_drop]
    push_cast [hpos]; ring
  -- phase 2
  obtain ⟨T₂, hT₂, hH₂, E₂⟩ := leftLoop_ends h1i.symm (n := x.length) S₄ T₁ hT₁ hS₄io
    hS₄t1
  -- phase 3
  set S₅ := update S₄ nT1 []
  have hS₅0 : S₅ nT0 = bs y := by
    simp [S₅, S₄, S₃, S₂, update_of_ne h01, update_of_ne hx0.symm, update_of_ne h0i.symm.symm]
  obtain ⟨hd₆, e₆, r₆⟩ := countLoopN_runsH (R := R) (Q := Q) (bs y) S₅ T₂.head hS₅0
  set S₆ := update (update (update S₅ nT0 []) nT1 ((bs y).reverse ++ S₅ nT1)) nIo
    ((S₅ nIo).drop (bs y).length)
  have r₇ := moveAll_runsH h1i (m := 0) ((bs y).reverse) S₆ hd₆
    (by simp [S₆, S₅, update_of_ne h1i])
  obtain ⟨t₂, ht₂, R₂⟩ := r₆.seq r₇
  obtain ⟨T₃, hT₃, hH₃, E₃⟩ := Prog.compile_endsH (p := outP₂ (R := R) (Q := Q)) R₂ hT₂ rfl
  have E := Mach.seq_left_exit (Mach.seq_left_exit (Mach.seq_left_exit E₁ E₂) E₃)
    (Mach.haltWith_ends (k := R + Q + 7) (Γ := Fin (0 + 3)) (fun _ => false) T₃)
  have hE := Mach.toMachine_ends_tapes (n := R + Q + 6) (m := 0) (M := machOMach p)
    (s := .inl (.inl (.inl (outP₁ p).start))) E
  have hc : ComputesWithin p.machineO x y (t₁ + (3 * x.length + 1) + t₂ + 1) := by
    unfold ComputesWithin HaltsWithin
    rw [runOn_eq_drun, NProg.machineO, Mach.init_toMachine, hE.1, hE.2, Mach.init_toMachine]
    refine ⟨rfl, ?_⟩
    funext z
    show T₃.tape 0 z = (inputTapes (R + Q + 6) 0 y).tape 0 z
    have h1 := hT₃ 0 z
    have h2 := rep_input (R + Q + 6) 0 y 0 z
    have h3 : (inputTapes (R + Q + 6) 0 y).head 0 = 0 := rfl
    rw [hH₃] at h1
    rw [h1, h2, h3]
    have hio : S₆ nIo = [] := by simp [S₆, S₅, hS₄io, update_of_ne h1i.symm]
    have hhd : hd₆ nIo = (bs y).length := by
      rw [e₆, hH₂]; simp [hH₁, hd₄io]
    show cell (update (update S₆ nT1 []) nIo ((bs y).reverse.reverse ++ S₆ nIo) nIo) (z - _) = _
    rw [update_self, hio, List.reverse_reverse, List.append_nil]
    show cell (bs y) (z - update (update hd₆ nT1 (hd₆ nT1 + ((bs y).reverse.length : ℤ))) nIo
      (hd₆ nIo - ((bs y).reverse.length : ℤ)) nIo) = _
    rw [update_self, hhd, List.length_reverse, sub_self, sub_zero]
    simp only [inputStacks, if_true]
    congr 1
  refine ComputesWithin.mono hc ?_
  simp only [length_bs, List.length_reverse, List.length_take, List.length_drop] at ht₁ ht₂
  omega

end Lax119563Proofs.Compiler

end Compiler_NOutput

/-! ### Formerly `Lax119563Proofs.Compiler.CMachine` -/

section Compiler_CMachine

/-!
# Machines of structured statements

`CStm.computesWithin`: the machine of the compiled statement computes the encoding of the
emitted list of the denotation from the zero state, within the cost bound plus
`O(|x| + |output|)`.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime Lax119563Proofs.Reduction
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ}

/-- The zero state. -/
def NSt.zero (R Q : ℕ) : NSt R Q := ⟨fun _ => 0, fun _ => [], 0, []⟩

/-- The machine of a statement compiled with `D + 1` scratch registers. -/
noncomputable def CStm.machine (D : ℕ) (c : CStm R Q) : Machine := (CStm.code R D c).machineO

lemma CStm.machine_deterministic (D : ℕ) (c : CStm R Q) : Deterministic (c.machine D) :=
  NProg.machineO_deterministic _

/-- **Machines of structured statements.** -/
theorem CStm.computesWithin {D : ℕ} {c : CStm R Q} {x : List Bool} {w : ℕ} (hw : 2 ≤ w)
    (hd : c.depth ≤ D) (hf : c.Fits x w (NSt.zero R Q)) :
    ComputesWithin (c.machine D) x (encodeNats (c.exec x (NSt.zero R Q)).out)
      (c.cost x w (NSt.zero R Q) +
        20 * (x.length + (encodeNats (c.exec x (NSt.zero R Q)).out).length) + 10) := by
  have hb : (NSt.zero (R + D + 1) Q).Bdd w :=
    ⟨fun _ => by simp [NSt.zero], fun _ v hv => by simp [NSt.zero] at hv⟩
  obtain ⟨st', ⟨t, ht, hr⟩, hc⟩ := CStm.code_spec (D := D) hw c (NSt.zero R Q)
    (NSt.zero (R + D + 1) Q) hd hf ⟨rfl, rfl, rfl, rfl⟩ hb (Nat.zero_le _)
  have h := NProg.computesWithinO hr
  rw [hc.2.2.2] at h
  exact ComputesWithin.mono h (by omega)

end Lax119563Proofs.Compiler

end Compiler_CMachine

/-! ### Formerly `Lax119563Proofs.Compiler.Order` -/

section Compiler_Order

/-!
# The vertex order of the compiler machine

`ordL I` lists the vertex names in the order in which the machine numbers them:
first, for each schema `e` (in list order), its *hubs* and then its *non-hubs*; finally, for
each location `v` (in order), its coordinate vertices (`coordVerts I v`). With
`D = coordList (dom I e)` (increasing coordinate numbers, as in the input):

* `hubsE e`: for `c ∈ D`: `junc e c` (labels `bits2`, ternary only), `link e c` (`bits1`);
  then for `c ∈ D` and its steps `σ ∈ stepsC c`: `upd e σ c` (`bits2`);
* `nonhubsE e`: for `c ∈ D`: `sum e c` (`bits1`, ternary only); for `c ∈ D`, `σ ∈ stepsC c`:
  `track e σ c` (`bits1`); then `coef e σ` (`bits1`) for `σ ∈ coefSteps e`.

`stepsC c` are the steps `σ < N` with `ent σ c ≠ 0` in increasing order; since `σ = q M + j`
(row `j = σ % M`, repetition `q = σ / M`), this is the *q-major* order of the entries `(q, j)`,
`q ≤ k`, `j` a nonzero row of column `c`. Likewise `coefSteps e` are the steps whose row is
nonzero on `𝔠_e`, in increasing (q-major) order, so `coef e (q M + j)` has index
`q |R_e| + rank_{R_e}(j)` in the coef section.

`ordL_perm`: `ordL I` is a permutation of `vertexList I`, so `reGraph_spec` applies to
`reGraph I (ordL I) ε`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The steps of column `c`, increasing. -/
def stepsC (c : Coord k ℓ) : List ℕ :=
  (List.range (numSteps k ℓ)).filter fun σ => ent σ c ≠ 0

open Classical in
/-- The steps whose row is nonzero on the domain of `e`, increasing. -/
noncomputable def coefSteps (e : Fin I.schemas.length) : List ℕ :=
  (List.range (numSteps k ℓ)).filter fun σ => ∃ c ∈ dom I e, ent σ c ≠ 0

/-- The hubs of schema `e`. -/
def hubsE (e : Fin I.schemas.length) : List (VName I) :=
  (coordList (dom I e)).flatMap (fun c =>
      (if isTern (sch I e) then bits2.map (fun l => (Cls.junc e c, l)) else []) ++
        bits1.map fun l => (Cls.link e c, l)) ++
    (coordList (dom I e)).flatMap fun c =>
      (stepsC c).flatMap fun σ => bits2.map fun l => (Cls.upd e σ c, l)

/-- The non-hubs of schema `e`. -/
noncomputable def nonhubsE (e : Fin I.schemas.length) : List (VName I) :=
  (coordList (dom I e)).flatMap (fun c =>
      if isTern (sch I e) then bits1.map (fun l => (Cls.sum e c, l)) else []) ++
    (coordList (dom I e)).flatMap (fun c =>
      (stepsC c).flatMap fun σ => bits1.map fun l => (Cls.track e σ c, l)) ++
    (coefSteps I e).flatMap fun σ => bits1.map fun l => (Cls.coef e σ, l)

/-- The vertex order of the machine. -/
noncomputable def ordL : List (VName I) :=
  (List.finRange I.schemas.length).flatMap (fun e => hubsE I e ++ nonhubsE I e) ++
    (List.finRange I.numLocations).flatMap (coordVerts I)

@[simp] lemma mem_stepsC {c : Coord k ℓ} {σ : ℕ} :
    σ ∈ stepsC c ↔ σ < numSteps k ℓ ∧ ent σ c ≠ 0 := by
  simp [stepsC]

@[simp] lemma mem_coefSteps {e : Fin I.schemas.length} {σ : ℕ} :
    σ ∈ coefSteps I e ↔ σ < numSteps k ℓ ∧ ∃ c ∈ dom I e, ent σ c ≠ 0 := by
  simp [coefSteps]

/-- The names of the order are the valid names. -/
theorem mem_ordL (x : VName I) : x ∈ ordL I ↔ Valid I x := by
  obtain ⟨X, l⟩ := x
  cases X with
  | coord v c =>
    simp only [ordL, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
      mem_coordVerts]
    constructor
    · rintro (⟨e, h⟩ | ⟨v', -, h⟩)
      · exfalso
        simp [hubsE, nonhubsE] at h
      · exact h
    · intro h; exact Or.inr ⟨v, ⟨c, rfl⟩, h⟩
  | _ =>
    simp only [ordL, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
      mem_coordVerts, hubsE, nonhubsE, List.mem_map, mem_stepsC, mem_coefSteps, mem_coordList,
      Valid, ClsValid, LabelOK, twoBit, isSingleton, Prod.mk.injEq, mem_bits1, mem_bits2]
    constructor
    · intro h
      rcases h with ⟨e, h⟩ | ⟨v, ⟨c, hc⟩, -⟩
      · split_ifs at h <;> aesop
      · cases hc
    · intro h
      left
      aesop

lemma nodup_stepsC (c : Coord k ℓ) : (stepsC c).Nodup := List.nodup_range.filter _

lemma nodup_coefSteps (e : Fin I.schemas.length) : (coefSteps I e).Nodup :=
  List.nodup_range.filter _

/-- The steps of the columns, each with the labels `L`, are duplicate-free. -/
lemma nodup_colSteps (L : List Lab) (hL : L.Nodup) (C : Coord k ℓ → ℕ → ICls I)
    (hC : ∀ c σ, keyCoord I (C c σ) = some c ∧ keyStep I (C c σ) = some σ)
    (D : List (Coord k ℓ)) (hD : D.Nodup) :
    (D.flatMap fun c => (stepsC c).flatMap fun σ => L.map fun l => (C c σ, l)).Nodup := by
  refine nodup_flatMap_of_key (fun x => keyCoord I x.1) hD (fun c _ => ?_) (fun c _ x hx => ?_)
  · refine nodup_flatMap_of_key (fun x => keyStep I x.1) (nodup_stepsC c)
      (fun σ _ => nodup_map_label I _ hL) (fun σ _ x hx => ?_)
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
    exact (hC c σ).2
  · obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
    exact (hC c σ).1

lemma isHub_of_mem_hubsE {e : Fin I.schemas.length} {x : VName I} (hx : x ∈ hubsE I e) :
    isHub I x.1 = true ∧ keySchema I x.1 = some e := by
  simp only [hubsE, List.mem_append, List.mem_flatMap] at hx
  rcases hx with ⟨c, -, hx⟩ | ⟨c, -, σ, -, hx⟩
  · rcases hx with hx | hx
    · split at hx
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; exact ⟨rfl, rfl⟩
      · simp at hx
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; exact ⟨rfl, rfl⟩
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; exact ⟨rfl, rfl⟩

lemma not_hub_of_mem_nonhubsE {e : Fin I.schemas.length} {x : VName I}
    (hx : x ∈ nonhubsE I e) : isHub I x.1 = false ∧ keySchema I x.1 = some e := by
  simp only [nonhubsE, List.mem_append, List.mem_flatMap] at hx
  rcases hx with (⟨c, -, hx⟩ | ⟨c, -, σ, -, hx⟩) | ⟨σ, -, hx⟩
  · split at hx
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; exact ⟨rfl, rfl⟩
    · simp at hx
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; exact ⟨rfl, rfl⟩
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; exact ⟨rfl, rfl⟩

lemma nodup_hubsE (e : Fin I.schemas.length) : (hubsE I e).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 ≠ 5) ?_
    (nodup_colSteps I bits2 nodup_bits2 (fun c σ => .upd e σ c) (fun _ _ => ⟨rfl, rfl⟩) _
      (nodup_coordList _)) ?_ ?_
  · refine nodup_flatMap_of_key (fun x => keyCoord I x.1) (nodup_coordList _) (fun c _ => ?_)
      (fun c _ x hx => ?_)
    · refine nodup_append_of_key (fun x => tag I x.1 = 2) ?_ (nodup_map_label I _ nodup_bits1)
        ?_ ?_
      · split
        · exact nodup_map_label I _ nodup_bits2
        · exact List.nodup_nil
      · intro x hx
        split at hx
        · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
        · simp at hx
      · intro x hx
        obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
    · rcases List.mem_append.mp hx with hx | hx
      · split at hx
        · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
        · simp at hx
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
  · intro x hx
    obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp hx with hx | hx
    · split at hx
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
      · simp at hx
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
  · intro x hx
    obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]

lemma nodup_nonhubsE (e : Fin I.schemas.length) : (nonhubsE I e).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 ≠ 6) ?_ ?_ ?_ ?_
  · refine nodup_append_of_key (fun x => tag I x.1 = 1) ?_
      (nodup_colSteps I bits1 nodup_bits1 (fun c σ => .track e σ c) (fun _ _ => ⟨rfl, rfl⟩) _
        (nodup_coordList _)) ?_ ?_
    · refine nodup_flatMap_of_key (fun x => keyCoord I x.1) (nodup_coordList _)
        (fun c _ => ?_) (fun c _ x hx => ?_)
      · split
        · exact nodup_map_label I _ nodup_bits1
        · exact List.nodup_nil
      · split at hx
        · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
        · simp at hx
    · intro x hx
      obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
      split at hx
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
      · simp at hx
    · intro x hx
      obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
  · refine nodup_flatMap_of_key (fun x => keyStep I x.1) (nodup_coefSteps I e)
      (fun σ _ => nodup_map_label I _ nodup_bits1) (fun σ _ x hx => ?_)
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
      split at hx
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
      · simp at hx
    · obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
  · intro x hx
    obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]

theorem nodup_ordL : (ordL I).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 ≠ 0) ?_ ?_ ?_ ?_
  · refine nodup_flatMap_of_key (fun x => keySchema I x.1) (List.nodup_finRange _)
      (fun e _ => ?_) (fun e _ x hx => ?_)
    · refine nodup_append_of_key (fun x => isHub I x.1 = true) (nodup_hubsE I e)
        (nodup_nonhubsE I e) (fun x hx => (isHub_of_mem_hubsE I hx).1) (fun x hx => ?_)
      rw [(not_hub_of_mem_nonhubsE I hx).1]; simp
    · rcases List.mem_append.mp hx with hx | hx
      · exact (isHub_of_mem_hubsE I hx).2
      · exact (not_hub_of_mem_nonhubsE I hx).2
  · refine nodup_flatMap_of_key (fun x => keyLoc I x.1) (List.nodup_finRange _)
      (fun v _ => nodup_coordVerts I v) (fun v _ x hx => ?_)
    obtain ⟨⟨c, h⟩, -⟩ := (mem_coordVerts I v x).mp hx
    rw [h]; rfl
  · intro x hx
    obtain ⟨e, -, hx⟩ := List.mem_flatMap.mp hx
    have : keySchema I x.1 = some e := by
      rcases List.mem_append.mp hx with hx | hx
      · exact (isHub_of_mem_hubsE I hx).2
      · exact (not_hub_of_mem_nonhubsE I hx).2
    intro h
    rcases x with ⟨X, l⟩
    cases X <;> simp_all [tag, keySchema]
  · intro x hx
    obtain ⟨v, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨⟨c, h⟩, -⟩ := (mem_coordVerts I v x).mp hx
    rw [h]; simp [tag]

/-- **The order is a permutation of the vertex list.** -/
theorem ordL_perm : (ordL I).Perm (vertexList I) :=
  (List.perm_ext_iff_of_nodup (nodup_ordL I) (nodup_vertexList I)).mpr fun x => by
    rw [mem_ordL, mem_vertexList]

end Lax119563Proofs.Compiler

end Compiler_Order

/-! ### Formerly `Lax119563Proofs.Compiler.OrderEdges` -/

section Compiler_OrderEdges

/-!
# Edges of the reordered graphs

In `ordL I` every hub comes before all its neighbors (`ordL_pairwise`: no name is a
`hubB`-neighbor of a later hub). Hence the edges `u < v` of `reGraph I (ordL I) ε` are exactly
the pairs with `hubB` from `u` to `v` (`adj_lt_iff`), and the edge list is, for each position
`u` in order, the increasing positions `v` with `hubB` from `L[u]` to `L[v]`
(`edgeList_ordL`).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- A `hubB`-neighbor lies in the schema of the hub or is a coordinate class. -/
lemma hubB_key {X Y : ICls I} {l m : Lab} (h : hubB I X l Y m = true) :
    keySchema I Y = keySchema I X ∨ tag I Y = 0 := by
  have htr : ∀ (e : Fin I.schemas.length) c σ,
      keySchema I (trackAt I e c σ) = some e ∨ tag I (trackAt I e c σ) = 0 := by
    intro e c σ
    rcases trackAt_cases e c σ with h | ⟨σ', -, h⟩ <;> rw [h]
    · rcases startCls_cases e c with h' | h' <;> rw [h'] <;> simp [keySchema, tag]
    · simp [keySchema]
  cases X with
  | upd e σ c =>
    simp only [hubB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩)
    · simpa [keySchema] using htr e c σ
    · simp [keySchema]
    · simp [keySchema]
  | junc e c =>
    simp only [hubB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩) <;> simp [keySchema, tag]
  | link e c =>
    simp only [hubB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with (⟨rfl, -⟩ | ⟨rfl, -⟩)
    · simpa [keySchema] using htr e c _
    · simp [endCls, tag]
  | coord => simp [hubB] at h
  | sum => simp [hubB] at h
  | track => simp [hubB] at h
  | coef => simp [hubB] at h

/-- `b` is not a `hubB`-hub of `a`. -/
def NoBack (a b : VName I) : Prop := ∀ l m, hubB I b.1 l a.1 m = false

lemma noBack_of {a b : VName I}
    (h : isHub I a.1 = true ∨ isHub I b.1 = false ∨
      ∃ e₁ e₂, keySchema I a.1 = some e₁ ∧ keySchema I b.1 = some e₂ ∧ e₁ ≠ e₂) :
    NoBack I a b := by
  intro l m
  by_contra hb
  rw [Bool.not_eq_false] at hb
  have h1 := hubB_hub I hb
  rcases h with h | h | ⟨e₁, e₂, h₁, h₂, hne⟩
  · rw [h] at h1; exact absurd h1.2 (by simp)
  · rw [h] at h1; exact absurd h1.1 (by simp)
  · rcases hubB_key I hb with h3 | h3
    · rw [h₁, h₂] at h3; exact hne (Option.some.inj h3)
    · rcases a with ⟨X, _⟩
      cases X <;> simp_all [tag, keySchema]

lemma keySchema_of_mem_block {e : Fin I.schemas.length} {x : VName I}
    (hx : x ∈ hubsE I e ++ nonhubsE I e) : keySchema I x.1 = some e := by
  rcases List.mem_append.mp hx with hx | hx
  · exact (isHub_of_mem_hubsE I hx).2
  · exact (not_hub_of_mem_nonhubsE I hx).2

lemma isHub_coordVerts {v : Fin I.numLocations} {x : VName I} (hx : x ∈ coordVerts I v) :
    isHub I x.1 = false := by
  obtain ⟨⟨c, h⟩, -⟩ := (mem_coordVerts I v x).mp hx
  rw [h]; rfl

/-- **Hubs come first.** No name is a `hubB`-neighbor of a later hub. -/
theorem ordL_pairwise : (ordL I).Pairwise (NoBack I) := by
  unfold ordL
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_flatMap]
    refine ⟨fun e _ => ?_, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨List.Pairwise.imp_of_mem ?_ (List.pairwise_of_forall (R := fun _ _ => True)
          (fun _ _ => trivial)), List.Pairwise.imp_of_mem ?_ (List.pairwise_of_forall
          (R := fun _ _ => True) (fun _ _ => trivial)), fun a ha b hb => ?_⟩
      · intro a b ha _ _
        exact noBack_of I (Or.inl (isHub_of_mem_hubsE I ha).1)
      · intro a b _ hb _
        exact noBack_of I (Or.inr (Or.inl (not_hub_of_mem_nonhubsE I hb).1))
      · exact noBack_of I (Or.inr (Or.inl (not_hub_of_mem_nonhubsE I hb).1))
    · refine (List.nodup_finRange _).imp_of_mem ?_
      intro e₁ e₂ _ _ hne a ha b hb
      exact noBack_of I (Or.inr (Or.inr ⟨e₁, e₂, keySchema_of_mem_block I ha,
        keySchema_of_mem_block I hb, hne⟩))
  · refine List.Pairwise.imp_of_mem ?_ (List.pairwise_of_forall (R := fun _ _ => True)
      (fun _ _ => trivial))
    intro a b _ hb _
    obtain ⟨v, -, hb⟩ := List.mem_flatMap.mp hb
    exact noBack_of I (Or.inr (Or.inl (isHub_coordVerts I hb)))
  · intro a _ b hb
    obtain ⟨v, -, hb⟩ := List.mem_flatMap.mp hb
    exact noBack_of I (Or.inr (Or.inl (isHub_coordVerts I hb)))

/-- The edges `u < v` of the reordered graph are the `hubB`-pairs. -/
theorem adj_lt_iff (ε : ZMod 2) (u v : Fin (ordL I).length) :
    (u < v ∧ adjN I ε (ordL I)[(u : ℕ)] (ordL I)[(v : ℕ)]) ↔
      hubB I (ordL I)[(u : ℕ)].1 (eff I ε (ordL I)[(u : ℕ)]) (ordL I)[(v : ℕ)].1
        (eff I ε (ordL I)[(v : ℕ)]) = true := by
  have hP := List.pairwise_iff_getElem.mp (ordL_pairwise I)
  constructor
  · rintro ⟨huv, h | h⟩
    · exact h
    · exact absurd h (by rw [hP u v u.2 v.2 huv]; simp)
  · intro h
    refine ⟨?_, Or.inl h⟩
    rcases lt_trichotomy u v with huv | rfl | hvu
    · exact huv
    · have := hubB_hub I h; rw [this.1] at this; exact absurd this.2 (by simp)
    · exact absurd h (by rw [hP v u v.2 u.2 hvu]; simp)

/-- **The edge list of the reordered graph.** -/
theorem edgeList_ordL (ε : ZMod 2) :
    edgeList (reGraph I (ordL I) ε) =
      (List.finRange (ordL I).length).flatMap fun (u : Fin (ordL I).length) =>
        ((List.finRange (ordL I).length).filter fun (v : Fin (ordL I).length) =>
          hubB I (ordL I)[(u : ℕ)].1 (eff I ε (ordL I)[(u : ℕ)]) (ordL I)[(v : ℕ)].1
            (eff I ε (ordL I)[(v : ℕ)])).map fun (v : Fin (ordL I).length) =>
              ((u : ℕ), (v : ℕ)) := by
  unfold edgeList
  refine List.flatMap_congr fun u _ => ?_
  rw [List.filter_congr (q := fun (v : Fin (ordL I).length) =>
    hubB I (ordL I)[(u : ℕ)].1 (eff I ε (ordL I)[(u : ℕ)]) (ordL I)[(v : ℕ)].1
      (eff I ε (ordL I)[(v : ℕ)])) (fun v _ => by
        rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; exact adj_lt_iff I ε u v)]
  simp only [List.map_eq_flatMap]
  change List.flatMap _ (List.flatMap (fun a : Fin (ordL I).length => [(a : ℕ)]) _) = _
  rw [List.flatMap_assoc]
  simp

end Lax119563Proofs.Compiler

end Compiler_OrderEdges

/-! ### Formerly `Lax119563Proofs.Compiler.OrderDesc` -/

section Compiler_OrderDesc

/-!
# The description of the reordered graphs, numerically

The output of the compiler machine, as lists that a sequential program can emit.

* `ordCls I`: the classes of `ordL I` in order, each with its list of labels; `ordL I` is the
  concatenation of the blocks `labs.map (X, ·)` (`ordL_eq_flatMap`).
* **Colors** (`colors_reGraph`): the color list of `reGraph I (ordL I) ε` is `colorsOf 0` of
  the block sizes: each class contributes its start position, repeated once per label.
* **Edges** (`edgeList_nbrPos`): for each position `u`, the edges `(u, v)`, `v` in
  `nbrPos ε L[u]`, the sorted positions of the names prescribed by the (at most three)
  neighbor slots `slotsOf` (class, required effective bit) of the hub; `posOpt` gives the
  position of the slot's name if present.
* **Positions** (`idxOf_ordL`): the name `(X, l)` sits at `clsStart X + ls.idxOf l`;
  `posOpt_bits1` (two-name classes: `clsStart Y + (b - ε·initBit Y)`), `posOpt_single`
  (initialized coordinate classes: present iff `b = ε·initBit Y`).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Colors of block lists -/

/-- Start positions repeated per block: blocks of sizes `ns` starting at `s`. -/
def colorsOf : ℕ → List ℕ → List ℕ
  | _, [] => []
  | s, n :: ns => List.replicate n s ++ colorsOf (s + n) ns

section Generic

variable {α β : Type*} [DecidableEq β] (cls : α → β)

lemma map_findIdx_blocks (blocks : List (List α))
    (hne : ∀ b ∈ blocks, b ≠ [])
    (hcls : ∀ b ∈ blocks, ∀ x ∈ b, ∀ y ∈ b, cls x = cls y)
    (hdis : blocks.Pairwise fun b b' => ∀ x ∈ b, ∀ y ∈ b', cls x ≠ cls y) :
    ∀ (pre : List α), (∀ x ∈ pre, ∀ b ∈ blocks, ∀ y ∈ b, cls x ≠ cls y) →
      blocks.flatten.map (fun y => (pre ++ blocks.flatten).findIdx
        fun x => decide (cls x = cls y)) = colorsOf pre.length (blocks.map List.length) := by
  induction blocks with
  | nil => intro _ _; rfl
  | cons b bs ih =>
    intro pre hpre
    simp only [List.flatten_cons, List.map_append, List.map_cons, colorsOf]
    obtain ⟨z, b', rfl⟩ : ∃ z b', b = z :: b' := by
      cases b with
      | nil => exact absurd rfl (hne _ List.mem_cons_self)
      | cons z b' => exact ⟨z, b', rfl⟩
    congr 1
    · apply List.eq_replicate_iff.mpr
      refine ⟨by simp, fun n hn => ?_⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hn
      rw [List.findIdx_append]
      have h1 : pre.findIdx (fun x => decide (cls x = cls y)) = pre.length :=
        List.findIdx_eq_length.mpr fun x hx => by
          simpa using hpre x hx _ List.mem_cons_self y hy
      rw [h1, if_neg (lt_irrefl _), List.cons_append, List.findIdx_cons]
      have : cls z = cls y := hcls _ List.mem_cons_self z List.mem_cons_self y hy
      simp [this]
    · have hih := ih (fun b hb => hne b (List.mem_cons_of_mem _ hb))
        (fun b hb => hcls b (List.mem_cons_of_mem _ hb)) (List.pairwise_cons.mp hdis).2
        (pre ++ z :: b') (by
          intro x hx b'' hb'' y hy
          rcases List.mem_append.mp hx with hx | hx
          · exact hpre x hx b'' (List.mem_cons_of_mem _ hb'') y hy
          · exact (List.pairwise_cons.mp hdis).1 b'' hb'' x hx y hy)
      rw [List.append_assoc] at hih
      rw [hih, List.length_append]

/-- **Colors of a list of class blocks.** -/
theorem colors_blocks (blocks : List (List α))
    (hne : ∀ b ∈ blocks, b ≠ [])
    (hcls : ∀ b ∈ blocks, ∀ x ∈ b, ∀ y ∈ b, cls x = cls y)
    (hdis : blocks.Pairwise fun b b' => ∀ x ∈ b, ∀ y ∈ b', cls x ≠ cls y) :
    (List.finRange blocks.flatten.length).map (fun i : Fin blocks.flatten.length =>
        blocks.flatten.findIdx fun x => decide (cls x = cls (blocks.flatten[(i : ℕ)]'i.2))) =
      colorsOf 0 (blocks.map List.length) := by
  have h := map_findIdx_blocks cls blocks hne hcls hdis [] (by simp)
  simp only [List.nil_append, List.length_nil] at h
  rw [← h]
  set L := blocks.flatten
  rw [show (fun i : Fin L.length => L.findIdx fun x => decide (cls x = cls (L[(i : ℕ)]'i.2))) =
      (fun y => L.findIdx fun x => decide (cls x = cls y)) ∘ L.get from rfl, ← List.map_map,
    List.map_get_finRange]

end Generic

/-! ## The classes of the order -/

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The block of names of a class with a list of labels. -/
def blk (p : ICls I × List Lab) : List (VName I) := p.2.map fun l => (p.1, l)

/-- The classes of the hubs of schema `e`, with their labels. -/
def hubsCls (e : Fin I.schemas.length) : List (ICls I × List Lab) :=
  (coordList (dom I e)).flatMap (fun c =>
      (if isTern (sch I e) then [(Cls.junc e c, bits2)] else []) ++ [(Cls.link e c, bits1)]) ++
    (coordList (dom I e)).flatMap fun c => (stepsC c).map fun σ => (Cls.upd e σ c, bits2)

/-- The classes of the non-hubs of schema `e`, with their labels. -/
noncomputable def nonhubsCls (e : Fin I.schemas.length) : List (ICls I × List Lab) :=
  (coordList (dom I e)).flatMap (fun c =>
      if isTern (sch I e) then [(Cls.sum e c, bits1)] else []) ++
    (coordList (dom I e)).flatMap (fun c => (stepsC c).map fun σ => (Cls.track e σ c, bits1)) ++
    (coefSteps I e).map fun σ => (Cls.coef e σ, bits1)

/-- The labels of the coordinate classes of location `v`. -/
def coordLabs (v : Fin I.numLocations) : List Lab :=
  if (I.init v).isSome then [((0 : ZMod 2), (0 : ZMod 2))] else bits1

/-- The classes of the order, with their labels. -/
noncomputable def ordCls : List (ICls I × List Lab) :=
  (List.finRange I.schemas.length).flatMap (fun e => hubsCls I e ++ nonhubsCls I e) ++
    (List.finRange I.numLocations).flatMap fun v =>
      (coordList (I.domain v)).map fun c => (Cls.coord v c, coordLabs I v)

lemma hubsE_eq (e : Fin I.schemas.length) : hubsE I e = (hubsCls I e).flatMap (blk I) := by
  simp only [hubsE, hubsCls, List.flatMap_append, List.flatMap_assoc]
  congr 1
  · refine List.flatMap_congr fun c _ => ?_
    split <;> simp [blk]
  · refine List.flatMap_congr fun c _ => ?_
    simp [blk, List.flatMap_map]

lemma nonhubsE_eq (e : Fin I.schemas.length) :
    nonhubsE I e = (nonhubsCls I e).flatMap (blk I) := by
  simp only [nonhubsE, nonhubsCls, List.flatMap_append, List.flatMap_assoc]
  congr 1
  · congr 1
    · refine List.flatMap_congr fun c _ => ?_
      split <;> simp [blk]
    · refine List.flatMap_congr fun c _ => ?_
      simp [blk, List.flatMap_map]
  · simp [blk, List.flatMap_map]

/-- **The order as blocks of classes.** -/
theorem ordL_eq_flatMap : ordL I = (ordCls I).flatMap (blk I) := by
  simp only [ordL, ordCls, List.flatMap_append, List.flatMap_assoc]
  congr 1
  · refine List.flatMap_congr fun e _ => ?_
    rw [hubsE_eq, nonhubsE_eq]
  · refine List.flatMap_congr fun v _ => ?_
    simp [coordVerts, coordLabs, blk, List.flatMap_map]

lemma mem_labs_zero {p : ICls I × List Lab} (hp : p ∈ ordCls I) :
    ((0 : ZMod 2), (0 : ZMod 2)) ∈ p.2 := by
  have h1 : ((0 : ZMod 2), (0 : ZMod 2)) ∈ bits1 := by simp
  have h2 : ((0 : ZMod 2), (0 : ZMod 2)) ∈ bits2 := by simp
  simp only [ordCls, hubsCls, nonhubsCls, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and] at hp
  rcases hp with ⟨e, (⟨c, -, hp⟩ | ⟨c, -, σ, -, rfl⟩) | (⟨c, -, hp⟩ | ⟨c, -, σ, -, rfl⟩) |
      ⟨σ, -, rfl⟩⟩ | ⟨v, c, -, rfl⟩
  · rcases hp with hp | hp
    · split at hp
      · simp only [List.mem_singleton] at hp; subst hp; exact h2
      · simp at hp
    · simp only [List.mem_singleton] at hp; subst hp; exact h1
  · exact h2
  · split at hp
    · simp only [List.mem_singleton] at hp; subst hp; exact h1
    · simp at hp
  · exact h1
  · exact h1
  · simp only [coordLabs]; split
    · simp
    · exact h1

/-- The blocks of the order. -/
noncomputable def ordBlocks : List (List (VName I)) := (ordCls I).map (blk I)

lemma ordL_eq_flatten : ordL I = (ordBlocks I).flatten := by
  rw [ordL_eq_flatMap, ordBlocks, List.flatMap_def]

lemma ordBlocks_pairwise :
    (ordBlocks I).Pairwise fun b b' => ∀ x ∈ b, ∀ y ∈ b', x.1 ≠ y.1 := by
  have hnd := nodup_ordL I
  rw [ordL_eq_flatten] at hnd
  have hdis := (List.nodup_flatten.mp hnd).2
  unfold ordBlocks at hdis ⊢
  rw [List.pairwise_map] at hdis ⊢
  refine List.Pairwise.imp_of_mem ?_ hdis
  intro p p' hp hp' hd x hx y hy hxy
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
  obtain ⟨l', -, rfl⟩ := List.mem_map.mp hy
  simp only at hxy
  have h0 : (p.1, ((0 : ZMod 2), (0 : ZMod 2))) ∈ blk I p :=
    List.mem_map.mpr ⟨_, mem_labs_zero I hp, rfl⟩
  have h0' : (p.1, ((0 : ZMod 2), (0 : ZMod 2))) ∈ blk I p' := by
    rw [hxy]; exact List.mem_map.mpr ⟨_, mem_labs_zero I hp', rfl⟩
  exact hd h0 h0'

/-- **The colors of the reordered graphs.** Each class of `ordCls I` contributes its start
position, repeated once per label. -/
theorem colors_reGraph (ε : ZMod 2) :
    (List.finRange (reGraph I (ordL I) ε).n).map (reGraph I (ordL I) ε).color =
      colorsOf 0 ((ordCls I).map fun p => p.2.length) := by
  have h := colors_blocks (fun x : VName I => x.1) (ordBlocks I)
    (fun b hb => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
      intro h; have := mem_labs_zero I hp
      simp [blk] at h; rw [h] at this; simp at this)
    (fun b hb x hx y hy => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hb
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
      obtain ⟨l', -, rfl⟩ := List.mem_map.mp hy
      rfl)
    (ordBlocks_pairwise I)
  have e1 : (ordBlocks I).map List.length = (ordCls I).map fun p => p.2.length := by
    simp [ordBlocks, blk, Function.comp_def]
  rw [← e1, ← h]
  have e2 := ordL_eq_flatten I
  simp only [listGraph_n]
  revert e2
  generalize ordL I = L
  rintro rfl
  simp only [Fin.getElem_fin]

/-! ## Edges: neighbor slots of the hubs -/

/-- The neighbor slots of a hub class with (effective) label `l`: the neighbor class and the
first effective label bit required there. -/
def slotsOf : ICls I → Lab → List (ICls I × ZMod 2)
  | .upd e σ c, l => [(trackAt I e c σ, l.1), (.track e σ c, l.2), (.coef e σ, l.1 + l.2)]
  | .junc e c, l => [(coordU e c, l.1), (coordV e c, l.2), (.sum e c, l.1 + l.2)]
  | .link e c, l => [(trackAt I e c (numSteps k ℓ), l.1), (endCls I e c, l.1)]
  | _, _ => []

lemma hubB_iff_slotsOf (X Y : ICls I) (l m : Lab) :
    hubB I X l Y m = true ↔ (Y, m.1) ∈ slotsOf I X l := by
  cases X with
  | upd e σ c => rw [hubB_upd]; simp [slotsOf, Prod.ext_iff]
  | junc e c => rw [hubB_junc']; simp [slotsOf, Prod.ext_iff]
  | link e c => rw [hubB_link]; simp [slotsOf, Prod.ext_iff]
  | coord => simp [hubB, slotsOf]
  | sum => simp [hubB, slotsOf]
  | track => simp [hubB, slotsOf]
  | coef => simp [hubB, slotsOf]

/-- The classes of the slots of a hub in the order are distinct. -/
lemma nodup_slotsOf {x : VName I} (hx : x ∈ ordL I) :
    ((slotsOf I x.1 x.2).map Prod.fst).Nodup := by
  obtain ⟨X, l⟩ := x
  have hv := (mem_ordL I _).mp hx
  cases X with
  | upd e σ c =>
    simp only [slotsOf, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨trackAt_ne_track e c σ, trackAt_ne_coef e c σ σ⟩, by simp⟩
  | junc e c =>
    have ht : isTern (sch I e) = true := hv.1.1
    simp only [slotsOf, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨coordU_ne_coordV ht c, by simp [coordU]⟩, by simp [coordV]⟩
  | link e c =>
    simp only [slotsOf, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨trackAt_ne_endCls e c _, by simp⟩
  | coord => simp [slotsOf]
  | sum => simp [slotsOf]
  | track => simp [slotsOf]
  | coef => simp [slotsOf]

variable (ε : ZMod 2)

/-- The label of the name of class `Y` whose first effective bit in `G_ε` is `b`. -/
def labOf (Y : ICls I) (b : ZMod 2) : Lab := (b - ε * initBit I Y, 0)

open Classical in
/-- The position of the name of class `Y` with first effective bit `b`, if present. -/
noncomputable def posOpt (Y : ICls I) (b : ZMod 2) : Option ℕ :=
  if (Y, labOf I ε Y b) ∈ ordL I then some ((ordL I).idxOf (Y, labOf I ε Y b)) else none

/-- A non-hub name of the order is the one prescribed by its class and effective bit. -/
lemma eq_labOf {y : VName I} (hy : y ∈ ordL I) (hh : isHub I y.1 = false) :
    y = (y.1, labOf I ε y.1 (eff I ε y).1) := by
  obtain ⟨Y, m⟩ := y
  have h2 : m.2 = 0 := ((mem_ordL I _).mp hy).2.1 (twoBit_of_not_hub hh)
  ext <;> simp [labOf, eff, h2]

/-- The sorted positions of the neighbors of the name `x`. -/
noncomputable def nbrPos (x : VName I) : List ℕ :=
  ((slotsOf I x.1 (eff I ε x)).filterMap fun s => posOpt I ε s.1 s.2).mergeSort
    fun a b => decide (a ≤ b)

lemma eff_hub {x : VName I} (h : isHub I x.1 = true) : eff I ε x = x.2 := by
  obtain ⟨X, l⟩ := x
  cases X <;> simp_all [isHub, eff, initBit]

/-- The neighbor positions of a name of the order. -/
theorem filter_hubB_eq_nbrPos' (x : VName I) (hxL : x ∈ ordL I) :
    ((List.finRange (ordL I).length).filter (fun v : Fin (ordL I).length =>
        hubB I x.1 (eff I ε x) (ordL I)[(v : ℕ)].1 (eff I ε (ordL I)[(v : ℕ)]))).map Fin.val =
      nbrPos I ε x := by
  have hnd : (ordL I).Nodup := nodup_ordL I
  -- membership
  have hmem : ∀ v : ℕ, v ∈ ((List.finRange (ordL I).length).filter (fun v : Fin (ordL I).length =>
        hubB I x.1 (eff I ε x) (ordL I)[(v : ℕ)].1 (eff I ε (ordL I)[(v : ℕ)]))).map Fin.val ↔
      v ∈ nbrPos I ε x := by
    intro v
    simp only [nbrPos, List.mem_mergeSort, List.mem_filterMap, List.mem_map, List.mem_filter,
      List.mem_finRange, true_and]
    constructor
    · rintro ⟨v', hv', rfl⟩
      have hs := (hubB_iff_slotsOf I _ _ _ _).mp hv'
      have hnh := (hubB_hub I hv').2
      have hy : (ordL I)[(v' : ℕ)] ∈ ordL I := List.getElem_mem _
      refine ⟨_, hs, ?_⟩
      have he := eq_labOf I ε hy hnh
      simp only [posOpt]
      rw [← he, if_pos hy, hnd.idxOf_getElem]
    · rintro ⟨s, hs, hp⟩
      simp only [posOpt] at hp
      split_ifs at hp with hin
      cases hp
      refine ⟨⟨_, List.idxOf_lt_length_of_mem hin⟩, ?_, rfl⟩
      simp only [List.getElem_idxOf]
      rw [hubB_iff_slotsOf]
      convert hs using 2
      simp [eff, labOf]
  -- both sides are sorted and duplicate-free
  have hs₁ : (((List.finRange (ordL I).length).filter (fun v : Fin (ordL I).length =>
        hubB I x.1 (eff I ε x) (ordL I)[(v : ℕ)].1 (eff I ε (ordL I)[(v : ℕ)]))).map
          Fin.val).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact (List.pairwise_lt_finRange _).filter _
  have hs₂ : (nbrPos I ε x).Pairwise (· ≤ ·) := by
    have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c h₁ h₂ => by simp at *; omega) (fun a b => by simp; omega)
      ((slotsOf I x.1 (eff I ε x)).filterMap fun s => posOpt I ε s.1 s.2)
    simpa [nbrPos] using this
  have hnd₂ : (nbrPos I ε x).Nodup := by
    refine (List.mergeSort_perm _ _).nodup_iff.mpr ?_
    have hslots := nodup_slotsOf I hxL
    rw [show slotsOf I x.1 (eff I ε x) = slotsOf I x.1 x.2 by
      by_cases hh : isHub I x.1 = true
      · rw [eff_hub I ε hh]
      · cases hX : x.1 <;> simp_all [isHub, slotsOf]]
    refine List.Nodup.filterMap ?_ (List.Nodup.of_map _ hslots)
    intro s s' a ha ha'
    have key : ∀ t : ICls I × ZMod 2, a ∈ posOpt I ε t.1 t.2 →
        (t.1, labOf I ε t.1 t.2) ∈ ordL I ∧ (ordL I).idxOf (t.1, labOf I ε t.1 t.2) = a := by
      intro t ht
      unfold posOpt at ht
      split_ifs at ht with h
      · simp only [Option.mem_def, Option.some.injEq] at ht; exact ⟨h, ht⟩
      · simp at ht
    obtain ⟨h₁, e₁⟩ := key s ha
    obtain ⟨h₂, e₂⟩ := key s' ha'
    have := (List.idxOf_inj h₁).mp (e₁.trans e₂.symm)
    obtain ⟨hY, hb⟩ := Prod.mk.inj this
    simp only [labOf, Prod.mk.injEq] at hb
    rw [hY] at hb
    exact Prod.ext hY (sub_left_inj.mp hb.1)
  exact List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h1 h2) (hs₁.imp le_of_lt) hs₂
    ((List.perm_ext_iff_of_nodup (hs₁.imp ne_of_lt) hnd₂).mpr hmem)

/-- **The edge list of the reordered graphs, per hub.** For every position `u`, the edges
`(u, v)` with `v` in the sorted neighbor positions `nbrPos` of the name at `u` (empty for
non-hubs; at most three slots `slotsOf`, each giving the position of the name of the slot
class with the required effective bit, `posOpt`). -/
theorem edgeList_nbrPos :
    edgeList (reGraph I (ordL I) ε) =
      (List.finRange (ordL I).length).flatMap fun u : Fin (ordL I).length =>
        (nbrPos I ε (ordL I)[(u : ℕ)]).map fun v => ((u : ℕ), v) := by
  rw [edgeList_ordL]
  refine List.flatMap_congr fun u _ => ?_
  rw [← filter_hubB_eq_nbrPos' I ε _ (List.getElem_mem _), List.map_map]
  rfl

/-! ## Positions of names: class starts and label offsets -/

section Starts

variable {β γ : Type*} [DecidableEq β] [BEq γ] [LawfulBEq γ]

/-- The start position of the class `X` in a list of classes with labels. -/
def startIn (P : List (β × List γ)) (X : β) : ℕ :=
  ((P.takeWhile fun p => p.1 ≠ X).map fun p => p.2.length).sum

lemma idxOf_map_pair (X : β) (l : γ) : ∀ ls : List γ,
    (ls.map fun m => (X, m)).idxOf (X, l) = ls.idxOf l
  | [] => rfl
  | m :: ls => by
    by_cases h : m = l
    · subst h; simp
    · rw [List.map_cons, List.idxOf_cons_ne _ (by simp [h]), List.idxOf_cons_ne _ h,
        idxOf_map_pair X l ls]

/-- **Positions in a list of class blocks.** -/
theorem idxOf_flatMap_blocks : ∀ (P : List (β × List γ)), (P.map Prod.fst).Nodup →
    ∀ (X : β) (ls : List γ) (l : γ), (X, ls) ∈ P → l ∈ ls →
      (P.flatMap fun p => p.2.map fun m => (p.1, m)).idxOf (X, l) = startIn P X + ls.idxOf l
  | [], _, _, _, _, h, _ => by simp at h
  | (Y, ms) :: P, hnd, X, ls, l, hX, hl => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rw [List.flatMap_cons]
    by_cases hY : Y = X
    · subst hY
      have hls : ms = ls := by
        rcases List.mem_cons.mp hX with h | h
        · exact (Prod.mk.inj h).2.symm
        · exact absurd ⟨_, h, rfl⟩ hnd.1
      subst hls
      rw [List.idxOf_append_of_mem (List.mem_map.mpr ⟨l, hl, rfl⟩), idxOf_map_pair]
      simp [startIn]
    · have hX' : (X, ls) ∈ P := by
        rcases List.mem_cons.mp hX with h | h
        · exact absurd (Prod.mk.inj h).1.symm hY
        · exact h
      rw [List.idxOf_append_of_notMem (by simp [hY]),
        idxOf_flatMap_blocks P hnd.2 X ls l hX' hl]
      simp [startIn, hY]
      omega

end Starts

lemma nodup_ordCls_fst : ((ordCls I).map Prod.fst).Nodup := by
  have h := ordBlocks_pairwise I
  unfold ordBlocks at h
  rw [List.pairwise_map] at h
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ h
  intro p p' hp hp' hd heq
  exact hd _ (List.mem_map.mpr ⟨_, mem_labs_zero I hp, rfl⟩) _
    (List.mem_map.mpr ⟨_, mem_labs_zero I hp', rfl⟩) (by simpa using heq)

/-- The start position of a class in the order. -/
noncomputable def clsStart (X : ICls I) : ℕ := startIn (ordCls I) X

/-- **Positions of names.** The name `(X, l)` of a class `X` with labels `ls` in `ordCls I`
sits at `clsStart X + ls.idxOf l`. -/
theorem idxOf_ordL {X : ICls I} {ls : List Lab} (hX : (X, ls) ∈ ordCls I) {l : Lab}
    (hl : l ∈ ls) : (ordL I).idxOf (X, l) = clsStart I X + ls.idxOf l := by
  rw [ordL_eq_flatMap]
  exact idxOf_flatMap_blocks (ordCls I) (nodup_ordCls_fst I) X ls l hX hl

/-- The names of a class of `ordCls I` in the order are those with its labels. -/
lemma mem_ordL_iff_of_mem {X : ICls I} {ls : List Lab} (hX : (X, ls) ∈ ordCls I) (l : Lab) :
    (X, l) ∈ ordL I ↔ l ∈ ls := by
  rw [ordL_eq_flatMap, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hl⟩
    obtain ⟨m, hm, he⟩ := List.mem_map.mp hl
    obtain ⟨h1, rfl⟩ := Prod.mk.inj he
    have : p = (X, ls) := List.inj_on_of_nodup_map (nodup_ordCls_fst I) hp hX h1
    subst this; exact hm
  · intro hl; exact ⟨_, hX, List.mem_map.mpr ⟨l, hl, rfl⟩⟩

/-- **Slot positions.** For a class `Y` of `ordCls I` with labels `ls`, the slot `(Y, b)`
gives the name with label `labOf Y b` if that label is present. -/
theorem posOpt_of_mem {Y : ICls I} {ls : List Lab} (hY : (Y, ls) ∈ ordCls I) (b : ZMod 2) :
    posOpt I ε Y b =
      if labOf I ε Y b ∈ ls then some (clsStart I Y + ls.idxOf (labOf I ε Y b)) else none := by
  unfold posOpt
  by_cases h : labOf I ε Y b ∈ ls
  · rw [if_pos ((mem_ordL_iff_of_mem I hY _).mpr h), if_pos h, idxOf_ordL I hY h]
  · rw [if_neg (fun h' => h ((mem_ordL_iff_of_mem I hY _).mp h')), if_neg h]

lemma idxOf_bits1 (a : ZMod 2) : bits1.idxOf (a, (0 : ZMod 2)) = a.val := by
  fin_cases a <;> decide

/-- Slots of a two-name class (labels `bits1`): always present, offset the required label. -/
theorem posOpt_bits1 {Y : ICls I} (hY : (Y, bits1) ∈ ordCls I) (b : ZMod 2) :
    posOpt I ε Y b = some (clsStart I Y + (b - ε * initBit I Y).val) := by
  rw [posOpt_of_mem I ε hY, if_pos (by simp [labOf]), labOf, idxOf_bits1]

/-- Slots of a singleton class (an initialized coordinate class): present iff the required
bit is the effective label of its single name. -/
theorem posOpt_single {Y : ICls I} (hY : (Y, [((0 : ZMod 2), (0 : ZMod 2))]) ∈ ordCls I)
    (b : ZMod 2) :
    posOpt I ε Y b = if b = ε * initBit I Y then some (clsStart I Y) else none := by
  rw [posOpt_of_mem I ε hY]
  by_cases h : b = ε * initBit I Y
  · rw [if_pos (by simp [labOf, h]), if_pos h]; simp [labOf, h]
  · rw [if_neg (by simp [labOf, sub_eq_zero, h]), if_neg h]

end Lax119563Proofs.Compiler

end Compiler_OrderDesc

/-! ### Formerly `Lax119563Proofs.Compiler.CColors` -/

section Compiler_CColors

/-!
# Emitting the colors of a list of class sizes

`colorsS q t f p i`: pop the class sizes on `q`; for a size `n` emit `n` times the current
position `p` and advance `p` by `n` (`colorsS_good`: the output is extended by
`colorsOf P (stk q)`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

/-- Emit `p`, `t` times (counter `i`). -/
def repS (t p i : Fin R) : CStm R Q :=
  .loop (.lt (rv i) (rv t)) (.seq (.emit (rv p)) (.set i (.add (rv i) (.const 1))))

/-- The body of `colorsS`. -/
def colBody (q : Fin Q) (t f p i : Fin R) : CStm R Q :=
  .seq (.pop q t) (.seq (.set i (.const 0)) (.seq (repS t p i)
    (.seq (.set p (.add (rv p) (rv t))) (.sne f q))))

/-- Emit the colors of the class sizes on `q`. -/
def colorsS (q : Fin Q) (t f p i : Fin R) : CStm R Q :=
  .seq (.sne f q) (.loop (rv f) (colBody q t f p i))

lemma repS_good (hw : 2 ≤ w) {t p i : Fin R} (hti : t ≠ i) (hpi : p ≠ i) (st : NSt R Q) (n : ℕ)
    (hi : st.env i = 0) (ht : st.env t = n) (hn : n < 2 ^ w) (hp : st.env p < 2 ^ w) :
    Good x w (repS t p i) st
      { (st.set i n) with out := st.out ++ List.replicate n (st.env p) }
      ((n + 1) * (10 * Ex.nodeCost w)) := by
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  have h := Good.loop_const (x := x) (w := w) (e := .lt (rv i) (rv t))
    (body := .seq (.emit (rv p)) (.set i (.add (rv i) (.const 1)))) n
    (fun j => { (st.set i j) with out := st.out ++ List.replicate j (st.env p) })
    (6 * Ex.nodeCost w)
    (fun j hj => by
      simp [Ex.eval, rv, Function.update_of_ne hti, ht, hj])
    (by simp [Ex.eval, rv, Function.update_of_ne hti, ht])
    (fun j hj => by
      simp only [Ex.Fits, rv, NSt.set_env, Function.update_self, Function.update_of_ne hti, ht]
      omega)
    (fun j hj => by
      refine ((Good.emit ?_).seq (Good.set ?_)).of_eq ?_ ?_
      · simp only [Ex.Fits, rv, NSt.set_env, Function.update_of_ne hpi]; exact hp
      · simp only [Ex.Fits, rv, NSt.set_env, Function.update_self, Ex.eval]
        have : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
        omega
      · refine NSt.ext (funext fun r => ?_) rfl rfl ?_
        · simp only [NSt.set_env, Ex.eval, rv, Function.update_self]
          by_cases hr : r = i
          · subst hr; simp
          · simp [Function.update_of_ne hr]
        · simp [Ex.eval, rv, Function.update_of_ne hpi, List.replicate_succ']
      · simp only [Ex.size, rv]; omega)
  have e0 : ({ (st.set i 0) with out := st.out ++ List.replicate 0 (st.env p) } : NSt R Q) =
      st := by
    refine NSt.ext ?_ rfl rfl (by simp)
    funext r
    by_cases hr : r = i
    · subst hr; simp [hi]
    · simp [NSt.set_env, Function.update_of_ne hr]
  simp only [e0] at h
  refine h.mono ?_
  simp only [condCost, Ex.size, rv]; nlinarith

/-- **Colors from a stack of class sizes.** -/
lemma colorsS_loop_good (hw : 2 ≤ w) {q : Fin Q} {t f p i : Fin R} (htf : t ≠ f) (hti : t ≠ i)
    (htp : t ≠ p) (hfp : f ≠ p) (hfi : f ≠ i) (hpi : p ≠ i) :
    ∀ (L : List ℕ) (st : NSt R Q), st.stk q = L → st.env f = (if L = [] then 0 else 1) →
      st.env p + L.sum < 2 ^ w →
      ∃ st' : NSt R Q, Good x w (.loop (rv f) (colBody q t f p i)) st st'
          ((L.length + L.sum + 1) * (30 * Ex.nodeCost w)) ∧
        st'.stk = Function.update st.stk q [] ∧ st'.pos = st.pos ∧
        st'.out = st.out ++ colorsOf (st.env p) L ∧ st'.env p = st.env p + L.sum ∧
        ∀ r, r ≠ t → r ≠ f → r ≠ p → r ≠ i → st'.env r = st.env r
  | [], st, hq, hf, _ => by
    have hU := nodeCost_ge w
    have hU' := unitCost_ge w
    have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    refine ⟨st, (Good.loop_stop (by simp only [Ex.Fits, rv, hf] <;> simp <;> omega)
      (by simp [Ex.eval, rv, hf])).mono ?_,
      ?_, rfl, by simp [colorsOf], by simp, fun _ _ _ _ _ => rfl⟩
    · simp only [condCost, rv, Ex.size, List.length_nil, List.sum_nil]; omega
    · rw [← hq]; simp
  | n :: L, st, hq, hf, hP => by
    have hU := nodeCost_ge w
    have hU' := unitCost_ge w
    have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    simp only [List.sum_cons] at hP
    -- the body
    have r1 := Good.pop (x := x) (w := w) (st := st) q t
    set s1 := (st.setS q (st.stk q).tail).set t ((st.stk q).headD 0)
    have e1t : s1.env t = n := by simp [s1, hq]
    have e1p : s1.env p = st.env p := by simp [s1, Function.update_of_ne htp.symm]
    have r2 := Good.set (x := x) (w := w) (st := s1) (r := i) (e := .const 0)
      (by simp only [Ex.Fits]; omega)
    set s2 := s1.set i ((Ex.const 0 : Ex R).eval s1.env)
    have r3 := repS_good (x := x) (w := w) hw hti hpi s2 n (by simp [s2, Ex.eval])
      (by simp [s2, Function.update_of_ne hti, e1t]) (by omega)
      (by simp [s2, Function.update_of_ne hpi, e1p]; omega)
    set s3 := { (s2.set i n) with out := s2.out ++ List.replicate n (s2.env p) }
    have e3t : s3.env t = n := by simp [s3, s2, Function.update_of_ne hti, e1t]
    have e3p : s3.env p = st.env p := by simp [s3, s2, Function.update_of_ne hpi, e1p]
    have r4 := Good.set (x := x) (w := w) (st := s3) (r := p) (e := .add (rv p) (rv t))
      (by simp only [Ex.Fits, rv, Ex.eval, e3t, e3p]; omega)
    set s4 := s3.set p ((Ex.add (rv p) (rv t)).eval s3.env)
    have r5 := Good.sne (x := x) (w := w) (st := s4) f q
    set s5 := s4.set f (if (s4.stk q).isEmpty then 0 else 1)
    have e5q : s5.stk q = L := by simp [s5, s4, s3, s2, s1, hq]
    have e5f : s5.env f = if L = [] then 0 else 1 := by
      simp only [s5, NSt.set_env, Function.update_self]
      rw [show s4.stk q = L from e5q]
      cases L <;> rfl
    have e5p : s5.env p = st.env p + n := by
      simp [s5, s4, Function.update_of_ne hfp.symm, Ex.eval, rv, e3t, e3p]
    have hbody := r1.seq (r2.seq (r3.seq (r4.seq r5)))
    obtain ⟨st', h', hs', hp', ho', hP', he'⟩ :=
      colorsS_loop_good hw htf hti htp hfp hfi hpi L s5 e5q e5f (by rw [e5p]; omega)
    have hst5 : s5.stk = Function.update st.stk q L := by
      funext r; by_cases hr : r = q
      · subst hr; simp [e5q]
      · simp [s5, s4, s3, s2, s1, Function.update_of_ne hr]
    refine ⟨st', (Good.loop_cons (by simp only [Ex.Fits, rv, hf]; simpa using h2)
      (by simp [Ex.eval, rv, hf]) hbody h').mono ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [condCost, Ex.size, rv, List.length_cons, List.sum_cons]
      generalize Ex.nodeCost w = N at hU hU' ⊢
      generalize unitCost w = U at hU hU' ⊢
      rw [show L.length + 1 + (n + L.sum) + 1 = (L.length + L.sum + 1) + (n + 1) by ring]
      generalize L.length + L.sum + 1 = m
      nlinarith
    · rw [hs', hst5]; simp
    · rw [hp']; rfl
    · rw [ho', e5p]
      simp [s5, s4, s3, s2, s1, colorsOf, Function.update_of_ne hpi, Function.update_of_ne htp.symm]
    · rw [hP', e5p, List.sum_cons]; ring
    · intro r h1 h2' h3 h4
      rw [he' r h1 h2' h3 h4]
      simp [s5, s4, s3, s2, s1, Function.update_of_ne h1, Function.update_of_ne h2',
        Function.update_of_ne h3, Function.update_of_ne h4]

end CStm

end Lax119563Proofs.Compiler

end Compiler_CColors

/-! ### Formerly `Lax119563Proofs.Compiler.OrderPos` -/

section Compiler_OrderPos

/-!
# Start positions of the classes of the order

Closed formulas for `clsStart I X` (the position of the first name of class `X` in
`ordL I`), as sums of section sizes and ranks, for every class kind.

* Generic: `startIn_append_left`, `startIn_append_right`, `startIn_flatMap` (a class in the
  block of the `i`-th element of a flat map starts after the blocks of the first `i`
  elements), `startIn_map_inj`, `startIn_cols`.
* Sections: `schSize`, `schBase`, `locBase`, `locSize`, `locStart`, `colW`, `nEnt`,
  `entBefore`, `hubSize`, `sumSize`; `clsStart_junc`, `clsStart_link`, `clsStart_upd`,
  `clsStart_sum`, `clsStart_track`, `clsStart_coef`, `clsStart_coord`.
* Slots: `slot_mem_ordCls` (every slot class of a name of the order is a class of the order
  with labels `slotLabs`: `[(0,0)]` for initialized coordinate classes, else `bits1`).
* Tracks: `trackAt_stepsC` (the track before the entry `j` of a column is the entry `j - 1`,
  or the start class), `trackAt_numSteps` (the last entry), `stepsC_ne_nil` (`k ≥ 2`).
* Order: `schBase_add_le`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

section Generic

variable {α β γ : Type*} [DecidableEq β]

/-- The number of names of a list of classes with labels. -/
def sizeOf' (P : List (β × List γ)) : ℕ := (P.map fun p => p.2.length).sum

@[simp] lemma sizeOf'_nil : sizeOf' ([] : List (β × List γ)) = 0 := rfl
@[simp] lemma sizeOf'_cons (p : β × List γ) (P : List (β × List γ)) :
    sizeOf' (p :: P) = p.2.length + sizeOf' P := by simp [sizeOf']
@[simp] lemma sizeOf'_append (P P' : List (β × List γ)) :
    sizeOf' (P ++ P') = sizeOf' P + sizeOf' P' := by simp [sizeOf']
lemma sizeOf'_flatMap (L : List α) (f : α → List (β × List γ)) :
    sizeOf' (L.flatMap f) = (L.map fun a => sizeOf' (f a)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

lemma startIn_append_left {P P' : List (β × List γ)} {X : β} (h : X ∈ P.map Prod.fst) :
    startIn (P ++ P') X = startIn P X := by
  induction P with
  | nil => simp at h
  | cons p P ih =>
    by_cases hp : p.1 = X
    · simp [startIn, List.takeWhile_cons, hp]
    · have h' : X ∈ P.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hp
        · exact h
      have := ih h'
      simp only [startIn, ne_eq, decide_not] at this ⊢
      simp [List.takeWhile_cons, hp, this]

lemma startIn_append_right {P P' : List (β × List γ)} {X : β} (h : X ∉ P.map Prod.fst) :
    startIn (P ++ P') X = sizeOf' P + startIn P' X := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have hp : p.1 ≠ X := fun e => h (by simp [← e])
    have h' : X ∉ P.map Prod.fst := fun h' => h (by simp at h' ⊢; tauto)
    have := ih h'
    simp only [startIn, sizeOf', ne_eq, decide_not] at this ⊢
    simp [List.takeWhile_cons, hp, this]
    omega

lemma startIn_cons_self (X : β) (ls : List γ) (P : List (β × List γ)) :
    startIn ((X, ls) :: P) X = 0 := by
  simp [startIn, List.takeWhile_cons]

/-- **A class in the `i`-th block of a flat map.** -/
lemma startIn_flatMap (L : List α) (f : α → List (β × List γ)) (i : ℕ) (hi : i < L.length)
    {X : β} (hX : X ∈ (f L[i]).map Prod.fst)
    (hdis : ∀ j < i, ∀ hj : j < L.length, X ∉ (f L[j]).map Prod.fst) :
    startIn (L.flatMap f) X =
      ((L.take i).map fun a => sizeOf' (f a)).sum + startIn (f L[i]) X := by
  have hL : L = L.take i ++ L[i] :: L.drop (i + 1) := by simp
  have hnot : X ∉ ((L.take i).flatMap f).map Prod.fst := by
    simp only [List.map_flatMap, List.mem_flatMap, not_exists, not_and]
    intro a ha hX'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    simp only [List.length_take] at hj
    have hji : j < i := by omega
    rw [List.getElem_take] at hX'
    exact hdis j hji (by omega) (by simpa using hX')
  conv_lhs => rw [hL]
  rw [List.flatMap_append, startIn_append_right hnot, List.flatMap_cons,
    startIn_append_left hX, sizeOf'_flatMap]

/-- A class in the block of the element `a` of a duplicate-free list. -/
lemma startIn_flatMap_of_mem (L : List α) [BEq α] [LawfulBEq α] (hL : L.Nodup)
    (f : α → List (β × List γ)) {a : α} (ha : a ∈ L) {X : β} (hX : X ∈ (f a).map Prod.fst)
    (hdis : ∀ b ∈ L, b ≠ a → X ∉ (f b).map Prod.fst) :
    startIn (L.flatMap f) X =
      ((L.take (L.idxOf a)).map fun b => sizeOf' (f b)).sum + startIn (f a) X := by
  have hi : L.idxOf a < L.length := List.idxOf_lt_length_of_mem ha
  have e : L[L.idxOf a] = a := List.getElem_idxOf hi
  have := startIn_flatMap L f (L.idxOf a) hi (by rw [e]; exact hX) (fun j hj hj' => by
    refine hdis _ (List.getElem_mem _) fun h => ?_
    have := (List.Nodup.getElem_inj_iff hL).mp (h.trans e.symm)
    omega)
  rw [this, e]

/-- Blocks of constant size. -/
lemma sum_map_const (L : List α) (n : ℕ) : (L.map fun _ => n).sum = L.length * n := by
  simp [List.sum_replicate]

end Generic

section Generic2

variable {α β γ : Type*} [BEq α] [LawfulBEq α] [DecidableEq β]

/-- Blocks of one class each, all with the labels `ls`. -/
lemma startIn_map_inj (g : α → β) (hg : Function.Injective g) (ls : List γ) (a : α) :
    ∀ L : List α, startIn (L.map fun b => (g b, ls)) (g a) = L.idxOf a * ls.length
  | [] => by simp [startIn]
  | b :: L => by
    by_cases h : b = a
    · subst h; simp [startIn, List.takeWhile_cons]
    · have hgb : g b ≠ g a := fun e => h (hg e)
      have ih := startIn_map_inj g hg ls a L
      simp only [startIn, ne_eq, decide_not] at ih ⊢
      simp only [List.map_cons, List.takeWhile_cons, hgb, decide_false, Bool.not_false,
        if_true, List.sum_cons, ih, List.idxOf_cons_ne _ h]
      rw [Nat.succ_eq_add_one]; ring

lemma sizeOf'_map_const (g : α → β) (ls : List γ) (L : List α) :
    sizeOf' (L.map fun b => (g b, ls)) = L.length * ls.length := by
  induction L with
  | nil => simp
  | cons b L ih => simp [ih]; ring

lemma sum_take_const (L : List α) (i n : ℕ) (hi : i ≤ L.length) :
    ((L.take i).map fun _ => n).sum = i * n := by
  rw [sum_map_const, List.length_take, min_eq_left hi]

end Generic2

/-! ## The sections of the order -/

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The number of names of schema `e`. -/
noncomputable def schSize (e : Fin I.schemas.length) : ℕ :=
  sizeOf' (hubsCls I e ++ nonhubsCls I e)

/-- The position of the first name of schema `e`. -/
noncomputable def schBase (e : Fin I.schemas.length) : ℕ :=
  (((List.finRange I.schemas.length).take e).map (schSize I)).sum

/-- The position of the first coordinate name. -/
noncomputable def locBase : ℕ := ((List.finRange I.schemas.length).map (schSize I)).sum

/-- The number of names of location `v`. -/
def locSize (v : Fin I.numLocations) : ℕ :=
  (coordList (I.domain v)).length * (coordLabs I v).length

/-- The position of the first name of location `v`. -/
noncomputable def locStart (v : Fin I.numLocations) : ℕ :=
  locBase I + (((List.finRange I.numLocations).take v).map (locSize I)).sum

/-- The width of a column in the junction/link section: `4 + 2` (ternary) or `2`. -/
def colW (e : Fin I.schemas.length) : ℕ := (if isTern (sch I e) then 4 else 0) + 2

/-- The number of entries of schema `e`. -/
def nEnt (e : Fin I.schemas.length) : ℕ :=
  ((coordList (dom I e)).map fun c => (stepsC c).length).sum

/-- The number of entries of the columns before `c`. -/
def entBefore (e : Fin I.schemas.length) (c : Coord k ℓ) : ℕ :=
  (((coordList (dom I e)).take ((coordList (dom I e)).idxOf c)).map
    fun c => (stepsC c).length).sum

/-- The number of hub names of schema `e`. -/
def hubSize (e : Fin I.schemas.length) : ℕ :=
  (coordList (dom I e)).length * colW I e + 4 * nEnt I e

/-- The size of the sum section of schema `e`. -/
def sumSize (e : Fin I.schemas.length) : ℕ :=
  if isTern (sch I e) then 2 * (coordList (dom I e)).length else 0

lemma keySchema_of_mem {e : Fin I.schemas.length} {p : ICls I × List Lab}
    (hp : p ∈ hubsCls I e ++ nonhubsCls I e) : keySchema I p.1 = some e := by
  simp only [hubsCls, nonhubsCls, List.mem_append, List.mem_flatMap, List.mem_map] at hp
  rcases hp with (⟨c, -, hp⟩ | ⟨c, -, σ, -, rfl⟩) | (⟨c, -, hp⟩ | ⟨c, -, σ, -, rfl⟩) |
      ⟨σ, -, rfl⟩
  · rcases hp with hp | hp
    · split at hp
      · simp only [List.mem_singleton] at hp; subst hp; rfl
      · simp at hp
    · simp only [List.mem_singleton] at hp; subst hp; rfl
  · rfl
  · split at hp
    · simp only [List.mem_singleton] at hp; subst hp; rfl
    · simp at hp
  · rfl
  · rfl

/-- A class of schema `e` starts at `schBase e` plus its start within the schema. -/
lemma clsStart_sch {e : Fin I.schemas.length} {X : ICls I}
    (hX : X ∈ (hubsCls I e ++ nonhubsCls I e).map Prod.fst) :
    clsStart I X = schBase I e + startIn (hubsCls I e ++ nonhubsCls I e) X := by
  have hk : keySchema I X = some e := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hX; exact keySchema_of_mem I hp
  unfold clsStart ordCls
  rw [startIn_append_left (by
    simp only [List.map_flatMap, List.mem_flatMap]
    exact ⟨e, List.mem_finRange _, hX⟩)]
  rw [startIn_flatMap_of_mem _ (List.nodup_finRange _) _ (List.mem_finRange e) hX
    (fun e' _ hne hX' => by
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hX'
      have := keySchema_of_mem I hp
      rw [he, hk] at this
      exact hne (Option.some.inj this).symm)]
  simp [schBase]
  congr 3; funext b; simp [schSize]


/-- The junction/link block of column `c`. -/
def jlBlock (e : Fin I.schemas.length) (c : Coord k ℓ) : List (ICls I × List Lab) :=
  (if isTern (sch I e) then [(Cls.junc e c, bits2)] else []) ++ [(Cls.link e c, bits1)]

lemma sizeOf'_jlBlock (e : Fin I.schemas.length) (c : Coord k ℓ) :
    sizeOf' (jlBlock I e c) = colW I e := by
  unfold jlBlock colW; split <;> simp [bits1, bits2]

lemma hubsCls_eq (e : Fin I.schemas.length) :
    hubsCls I e = (coordList (dom I e)).flatMap (jlBlock I e) ++
      (coordList (dom I e)).flatMap fun c => (stepsC c).map fun σ => (Cls.upd e σ c, bits2) :=
  rfl

lemma mem_jl_fst {e : Fin I.schemas.length} {c : Coord k ℓ} {X : ICls I}
    (h : X ∈ (jlBlock I e c).map Prod.fst) : X = Cls.junc e c ∨ X = Cls.link e c := by
  unfold jlBlock at h; split at h <;> simp at h <;> tauto

lemma idxOf_le_length {α : Type*} [BEq α] [LawfulBEq α] (L : List α) (a : α) :
    L.idxOf a ≤ L.length := List.idxOf_le_length

/-- **Junctions.** -/
theorem clsStart_junc {e : Fin I.schemas.length} {c : Coord k ℓ} (ht : isTern (sch I e) = true)
    (hc : c ∈ dom I e) :
    clsStart I (Cls.junc e c) = schBase I e + (coordList (dom I e)).idxOf c * colW I e := by
  have hcD : c ∈ coordList (dom I e) := (mem_coordList).mpr hc
  have hJ : Cls.junc e c ∈ (jlBlock I e c).map Prod.fst := by simp [jlBlock, ht]
  have hJ' : Cls.junc e c ∈ ((coordList (dom I e)).flatMap (jlBlock I e)).map Prod.fst := by
    simp only [List.map_flatMap, List.mem_flatMap]; exact ⟨c, hcD, hJ⟩
  rw [clsStart_sch I (X := Cls.junc e c) (by
    rw [List.map_append, List.mem_append, hubsCls_eq, List.map_append, List.mem_append]
    exact Or.inl (Or.inl hJ')), startIn_append_left (by
      rw [hubsCls_eq, List.map_append, List.mem_append]; exact Or.inl hJ'), hubsCls_eq,
    startIn_append_left hJ', startIn_flatMap_of_mem _ (nodup_coordList _) _ hcD hJ
      (fun c' _ hne h => by rcases mem_jl_fst I h with h | h <;> simp at h <;> tauto)]
  simp only [sizeOf'_jlBlock]
  rw [sum_take_const _ _ _ (idxOf_le_length _ _)]
  simp [jlBlock, ht, startIn_cons_self]

/-- **Links.** -/
theorem clsStart_link {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) :
    clsStart I (Cls.link e c) = schBase I e + (coordList (dom I e)).idxOf c * colW I e +
      (if isTern (sch I e) then 4 else 0) := by
  have hcD : c ∈ coordList (dom I e) := (mem_coordList).mpr hc
  have hJ : Cls.link e c ∈ (jlBlock I e c).map Prod.fst := by
    unfold jlBlock; split <;> simp
  have hJ' : Cls.link e c ∈ ((coordList (dom I e)).flatMap (jlBlock I e)).map Prod.fst := by
    simp only [List.map_flatMap, List.mem_flatMap]; exact ⟨c, hcD, hJ⟩
  rw [clsStart_sch I (X := Cls.link e c) (by
    rw [List.map_append, List.mem_append, hubsCls_eq, List.map_append, List.mem_append]
    exact Or.inl (Or.inl hJ')), startIn_append_left (by
      rw [hubsCls_eq, List.map_append, List.mem_append]; exact Or.inl hJ'), hubsCls_eq,
    startIn_append_left hJ', startIn_flatMap_of_mem _ (nodup_coordList _) _ hcD hJ
      (fun c' _ hne h => by rcases mem_jl_fst I h with h | h <;> simp at h <;> tauto)]
  simp only [sizeOf'_jlBlock]
  rw [sum_take_const _ _ _ (idxOf_le_length _ _)]
  unfold jlBlock
  split
  · simp [startIn, List.takeWhile_cons, bits2]; omega
  · simp [startIn_cons_self]


/-- Classes indexed by a column and an entry of the column. -/
lemma startIn_cols {α β γ δ : Type*} [BEq α] [LawfulBEq α] [BEq δ] [LawfulBEq δ]
    [DecidableEq β] (D : List α) (hD : D.Nodup) (S : α → List δ) (g : α → δ → β)
    (hg : ∀ a b a' b', g a b = g a' b' → a = a' ∧ b = b') (ls : List γ) {c : α} (hc : c ∈ D)
    {σ : δ} (hσ : σ ∈ S c) :
    startIn (D.flatMap fun c => (S c).map fun σ => (g c σ, ls)) (g c σ) =
      ((D.take (D.idxOf c)).map fun c => (S c).length).sum * ls.length +
        (S c).idxOf σ * ls.length := by
  rw [startIn_flatMap_of_mem D hD _ hc (by simp; exact ⟨σ, hσ, rfl⟩) (fun c' _ hne h => by
    simp only [List.map_map, List.mem_map, Function.comp_apply] at h
    obtain ⟨σ', -, he⟩ := h
    exact hne (hg _ _ _ _ he).1)]
  rw [startIn_map_inj (g c) (fun b b' h => (hg _ _ _ _ h).2)]
  simp only [sizeOf'_map_const]
  rw [List.sum_map_mul_right]


lemma sizeOf'_jl (e : Fin I.schemas.length) :
    sizeOf' ((coordList (dom I e)).flatMap (jlBlock I e)) =
      (coordList (dom I e)).length * colW I e := by
  rw [sizeOf'_flatMap]; simp only [sizeOf'_jlBlock]; rw [sum_map_const]

lemma sizeOf'_ent (e : Fin I.schemas.length) (g : Coord k ℓ → ℕ → ICls I) (ls : List Lab) :
    sizeOf' ((coordList (dom I e)).flatMap fun c => (stepsC c).map fun σ => (g c σ, ls)) =
      nEnt I e * ls.length := by
  rw [sizeOf'_flatMap]; simp only [sizeOf'_map_const]
  rw [nEnt, List.sum_map_mul_right]

lemma sizeOf'_hubsCls (e : Fin I.schemas.length) : sizeOf' (hubsCls I e) = hubSize I e := by
  rw [hubsCls_eq, sizeOf'_append, sizeOf'_jl, sizeOf'_ent]; simp [hubSize, bits2]; ring

/-- The sum part of the non-hubs. -/
def sumPart (e : Fin I.schemas.length) : List (ICls I × List Lab) :=
  (coordList (dom I e)).flatMap fun c => if isTern (sch I e) then [(Cls.sum e c, bits1)] else []

/-- The track part of the non-hubs. -/
def trackPart (e : Fin I.schemas.length) : List (ICls I × List Lab) :=
  (coordList (dom I e)).flatMap fun c => (stepsC c).map fun σ => (Cls.track e σ c, bits1)

lemma nonhubsCls_eq (e : Fin I.schemas.length) :
    nonhubsCls I e = sumPart I e ++ trackPart I e ++
      (coefSteps I e).map fun σ => (Cls.coef e σ, bits1) := rfl

lemma sizeOf'_sumPart (e : Fin I.schemas.length) : sizeOf' (sumPart I e) = sumSize I e := by
  rw [sumPart, sizeOf'_flatMap, sumSize]
  split
  · simp [bits1, sum_map_const]; ring
  · simp

lemma mem_sumPart_fst {e : Fin I.schemas.length} {X : ICls I}
    (h : X ∈ (sumPart I e).map Prod.fst) : ∃ c, X = Cls.sum e c := by
  simp only [sumPart, List.map_flatMap, List.mem_flatMap] at h
  obtain ⟨c, -, h⟩ := h
  split at h <;> simp at h; exact ⟨c, h⟩

lemma mem_trackPart_fst {e : Fin I.schemas.length} {X : ICls I}
    (h : X ∈ (trackPart I e).map Prod.fst) : ∃ σ c, X = Cls.track e σ c := by
  simp only [trackPart, List.map_flatMap, List.mem_flatMap, List.map_map, List.mem_map,
    Function.comp_apply] at h
  obtain ⟨c, -, σ, -, h⟩ := h
  exact ⟨σ, c, h.symm⟩

lemma mem_hubsCls_fst {e : Fin I.schemas.length} {X : ICls I}
    (h : X ∈ (hubsCls I e).map Prod.fst) : isHub I X = true := by
  rw [hubsCls_eq, List.map_append, List.mem_append] at h
  rcases h with h | h
  · simp only [List.map_flatMap, List.mem_flatMap] at h
    obtain ⟨c, -, h⟩ := h
    rcases mem_jl_fst I h with rfl | rfl <;> rfl
  · simp only [List.map_flatMap, List.mem_flatMap, List.map_map, List.mem_map,
      Function.comp_apply] at h
    obtain ⟨c, -, σ, -, rfl⟩ := h
    rfl

/-- A non-hub class of schema `e` starts after the hubs. -/
lemma clsStart_nonhub {e : Fin I.schemas.length} {X : ICls I}
    (hX : X ∈ (nonhubsCls I e).map Prod.fst) (hh : isHub I X = false) :
    clsStart I X = schBase I e + hubSize I e + startIn (nonhubsCls I e) X := by
  rw [clsStart_sch I (by rw [List.map_append, List.mem_append]; exact Or.inr hX),
    startIn_append_right (fun h => by rw [mem_hubsCls_fst I h] at hh; cases hh),
    sizeOf'_hubsCls]
  ring

/-- **Updates.** -/
theorem clsStart_upd {e : Fin I.schemas.length} {c : Coord k ℓ} {σ : ℕ} (hc : c ∈ dom I e)
    (hσ : σ ∈ stepsC c) :
    clsStart I (Cls.upd e σ c) = schBase I e + (coordList (dom I e)).length * colW I e +
      4 * (entBefore I e c + (stepsC c).idxOf σ) := by
  have hcD : c ∈ coordList (dom I e) := (mem_coordList).mpr hc
  have hU : (Cls.upd e σ c : ICls I) ∈ ((coordList (dom I e)).flatMap fun c =>
      (stepsC c).map fun σ => (Cls.upd e σ c, bits2)).map Prod.fst := by
    simp only [List.map_flatMap, List.mem_flatMap, List.map_map, List.mem_map,
      Function.comp_apply]
    exact ⟨c, hcD, σ, hσ, rfl⟩
  have hnJ : (Cls.upd e σ c : ICls I) ∉ ((coordList (dom I e)).flatMap (jlBlock I e)).map Prod.fst := by
    simp only [List.map_flatMap, List.mem_flatMap, not_exists, not_and]
    intro c' _ h; rcases mem_jl_fst I h with h | h <;> cases h
  rw [clsStart_sch I (X := Cls.upd e σ c) (by
      rw [List.map_append, List.mem_append, hubsCls_eq, List.map_append, List.mem_append]
      exact Or.inl (Or.inr hU)),
    startIn_append_left (by rw [hubsCls_eq, List.map_append, List.mem_append]; exact Or.inr hU),
    hubsCls_eq, startIn_append_right hnJ, sizeOf'_jl,
    startIn_cols (coordList (dom I e)) (nodup_coordList _) stepsC (fun c σ => (Cls.upd e σ c : ICls I))
      (fun a b a' b' h => by cases h; exact ⟨rfl, rfl⟩) bits2 hcD hσ]
  simp [entBefore, bits2]; ring

/-- **Sums.** -/
theorem clsStart_sum {e : Fin I.schemas.length} {c : Coord k ℓ} (ht : isTern (sch I e) = true)
    (hc : c ∈ dom I e) :
    clsStart I (Cls.sum e c) = schBase I e + hubSize I e + 2 * (coordList (dom I e)).idxOf c := by
  have hcD : c ∈ coordList (dom I e) := (mem_coordList).mpr hc
  have hS : (Cls.sum e c : ICls I) ∈ (sumPart I e).map Prod.fst := by
    simp only [sumPart, List.map_flatMap, List.mem_flatMap]
    exact ⟨c, hcD, by simp [ht]⟩
  rw [clsStart_nonhub I (by
      rw [nonhubsCls_eq, List.map_append, List.mem_append, List.map_append, List.mem_append]
      exact Or.inl (Or.inl hS)) rfl,
    nonhubsCls_eq, startIn_append_left (by
      rw [List.map_append, List.mem_append]; exact Or.inl hS),
    startIn_append_left hS, sumPart,
    startIn_flatMap_of_mem _ (nodup_coordList _) _ hcD (by simp [ht]) (fun c' _ hne h => by
      split at h <;> simp at h <;> exact hne h.symm)]
  simp only [ht, if_true, sizeOf'_cons, sizeOf'_nil]
  rw [sum_take_const _ _ _ (idxOf_le_length _ _), startIn_cons_self]
  simp [bits1]; ring

/-- **Tracks.** -/
theorem clsStart_track {e : Fin I.schemas.length} {c : Coord k ℓ} {σ : ℕ} (hc : c ∈ dom I e)
    (hσ : σ ∈ stepsC c) :
    clsStart I (Cls.track e σ c) = schBase I e + hubSize I e + sumSize I e +
      2 * (entBefore I e c + (stepsC c).idxOf σ) := by
  have hcD : c ∈ coordList (dom I e) := (mem_coordList).mpr hc
  have hT : (Cls.track e σ c : ICls I) ∈ (trackPart I e).map Prod.fst := by
    simp only [trackPart, List.map_flatMap, List.mem_flatMap, List.map_map, List.mem_map,
      Function.comp_apply]
    exact ⟨c, hcD, σ, hσ, rfl⟩
  rw [clsStart_nonhub I (by
      rw [nonhubsCls_eq, List.map_append, List.mem_append, List.map_append, List.mem_append]
      exact Or.inl (Or.inr hT)) rfl,
    nonhubsCls_eq, startIn_append_left (by
      rw [List.map_append, List.mem_append]; exact Or.inr hT),
    startIn_append_right (fun h => by obtain ⟨c', h⟩ := mem_sumPart_fst I h; cases h),
    sizeOf'_sumPart, trackPart,
    startIn_cols (coordList (dom I e)) (nodup_coordList _) stepsC (fun c σ => (Cls.track e σ c : ICls I))
      (fun a b a' b' h => by cases h; exact ⟨rfl, rfl⟩) bits1 hcD hσ]
  simp [entBefore, bits1]; ring

/-- **Coefficients.** -/
theorem clsStart_coef {e : Fin I.schemas.length} {σ : ℕ} (hσ : σ ∈ coefSteps I e) :
    clsStart I (Cls.coef e σ) = schBase I e + hubSize I e + sumSize I e + 2 * nEnt I e +
      2 * (coefSteps I e).idxOf σ := by
  have hC : (Cls.coef e σ : ICls I) ∈ ((coefSteps I e).map fun σ => (Cls.coef e σ, bits1)).map
      Prod.fst := by simpa using hσ
  rw [clsStart_nonhub I (by
      rw [nonhubsCls_eq, List.map_append, List.mem_append]; exact Or.inr hC) rfl,
    nonhubsCls_eq, startIn_append_right (fun h => by
      rw [List.map_append, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨c', h⟩ := mem_sumPart_fst I h; cases h
      · obtain ⟨_, _, h⟩ := mem_trackPart_fst I h; cases h),
    sizeOf'_append, sizeOf'_sumPart, trackPart, sizeOf'_ent,
    startIn_map_inj (fun σ => (Cls.coef e σ : ICls I)) (fun a b h => by cases h; rfl)]
  simp [bits1]; ring

/-- **Coordinate classes.** -/
theorem clsStart_coord {v : Fin I.numLocations} {c : Coord k ℓ} (hc : c ∈ I.domain v) :
    clsStart I (Cls.coord v c) =
      locStart I v + (coordList (I.domain v)).idxOf c * (coordLabs I v).length := by
  have hcD : c ∈ coordList (I.domain v) := (mem_coordList).mpr hc
  have hnS : (Cls.coord v c : ICls I) ∉ ((List.finRange I.schemas.length).flatMap
      fun e => hubsCls I e ++ nonhubsCls I e).map Prod.fst := by
    simp only [List.map_flatMap, List.mem_flatMap, not_exists, not_and]
    intro e _ h
    obtain ⟨p, hp, he⟩ := List.mem_map.mp h
    have := keySchema_of_mem I hp
    rw [he] at this; cases this
  unfold clsStart ordCls
  rw [startIn_append_right hnS, sizeOf'_flatMap,
    startIn_flatMap_of_mem _ (List.nodup_finRange _) _ (List.mem_finRange v)
      (X := (Cls.coord v c : ICls I)) (by
        simp only [List.map_map, List.mem_map, Function.comp_apply]; exact ⟨c, hcD, rfl⟩)
      (fun v' _ hne h => by
        simp only [List.map_map, List.mem_map, Function.comp_apply] at h
        obtain ⟨_, -, h⟩ := h
        cases h; exact hne rfl),
    startIn_map_inj (fun c => (Cls.coord v c : ICls I)) (fun a b h => by cases h; rfl)]
  have h1 : (List.map (fun a => sizeOf' (hubsCls I a ++ nonhubsCls I a))
      (List.finRange I.schemas.length)).sum = locBase I := rfl
  have h2 : (fun a => sizeOf' ((coordList (I.domain a)).map
      fun c => ((Cls.coord a c : ICls I), coordLabs I a))) = locSize I := by
    funext a; rw [sizeOf'_map_const]; rfl
  rw [h1, h2, List.idxOf_finRange, locStart]
  ring

/-! ## The slot classes are classes of the order -/

/-- The labels of a class in the order. -/
def clsLabs (Y : ICls I) : List Lab :=
  if twoBit I Y then bits2 else if isSingleton I Y then [((0 : ZMod 2), (0 : ZMod 2))] else bits1

lemma labs_of_mem_ordCls {p : ICls I × List Lab} (hp : p ∈ ordCls I) : p.2 = clsLabs I p.1 := by
  simp only [ordCls, hubsCls, nonhubsCls, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and] at hp
  rcases hp with ⟨e, (⟨c, -, hp⟩ | ⟨c, -, σ, -, rfl⟩) | (⟨c, -, hp⟩ | ⟨c, -, σ, -, rfl⟩) |
      ⟨σ, -, rfl⟩⟩ | ⟨v, c, -, rfl⟩
  · rcases hp with hp | hp
    · split at hp
      · simp only [List.mem_singleton] at hp; subst hp; rfl
      · simp at hp
    · simp only [List.mem_singleton] at hp; subst hp; rfl
  · rfl
  · split at hp
    · simp only [List.mem_singleton] at hp; subst hp; rfl
    · simp at hp
  · rfl
  · rfl
  · simp only [clsLabs, coordLabs, twoBit, isSingleton]
    split <;> simp_all

/-- Every valid class is a class of the order, with its labels. -/
lemma mem_ordCls_of_valid {Y : ICls I} (hY : ClsValid I Y) : (Y, clsLabs I Y) ∈ ordCls I := by
  have h0 : (Y, ((0 : ZMod 2), (0 : ZMod 2))) ∈ ordL I := (mem_ordL I _).mpr (valid_zero hY)
  rw [ordL_eq_flatMap, List.mem_flatMap] at h0
  obtain ⟨p, hp, hm⟩ := h0
  obtain ⟨m, -, he⟩ := List.mem_map.mp hm
  have h1 : p.1 = Y := (Prod.mk.inj he).1
  have h2 := labs_of_mem_ordCls I hp
  rw [h1] at h2
  have : p = (Y, clsLabs I Y) := Prod.ext h1 h2
  rw [← this]; exact hp

/-- The slot classes of the names of the order are valid. -/
lemma valid_slots {x : VName I} (hx : x ∈ ordL I) {l : Lab} {s : ICls I × ZMod 2}
    (hs : s ∈ slotsOf I x.1 l) : ClsValid I s.1 := by
  obtain ⟨X, lx⟩ := x
  have hv := ((mem_ordL I _).mp hx).1
  cases X with
  | upd e σ c =>
    obtain ⟨hσ, hc, hent⟩ := hv
    simp only [slotsOf, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact valid_trackAt e hc hσ.le
    · exact ⟨hσ, hc, hent⟩
    · exact ⟨hσ, c, hc, hent⟩
  | junc e c =>
    obtain ⟨ht, hc⟩ := hv
    simp only [slotsOf, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact valid_coordU e hc
    · exact valid_coordV e hc
    · exact ⟨ht, hc⟩
  | link e c =>
    simp only [slotsOf, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact valid_trackAt e hv le_rfl
    · exact valid_endCls e hv
  | coord => simp [slotsOf] at hs
  | sum => simp [slotsOf] at hs
  | track => simp [slotsOf] at hs
  | coef => simp [slotsOf] at hs

/-- The labels of a slot class: one name for initialized coordinate classes, else two. -/
def slotLabs (Y : ICls I) : List Lab :=
  if isSingleton I Y then [((0 : ZMod 2), (0 : ZMod 2))] else bits1

/-- **Slot classes.** The class of every slot of a name of the order is a class of the order
with labels `slotLabs`: `[(0,0)]` for coordinate classes of initialized locations, `bits1`
otherwise, so that `posOpt_single` resp. `posOpt_bits1` applies. -/
theorem slot_mem_ordCls {x : VName I} (hx : x ∈ ordL I) {l : Lab} {s : ICls I × ZMod 2}
    (hs : s ∈ slotsOf I x.1 l) : (s.1, slotLabs I s.1) ∈ ordCls I := by
  have h := mem_ordCls_of_valid I (valid_slots I hx hs)
  have hh : isHub I s.1 = false :=
    (hubB_hub I ((hubB_iff_slotsOf I x.1 s.1 l (s.2, 0)).mpr hs)).2
  have ht : twoBit I s.1 = false := by
    cases h' : s.1 <;> simp_all [twoBit, isHub]
  simpa [clsLabs, slotLabs, ht] using h

/-! ## Tracks: the previous entry of the column -/

lemma prevStep_eq_some {c : Coord k ℓ} {σ σ' : ℕ} (h1 : σ' < σ) (h2 : ent σ' c ≠ 0)
    (h3 : ∀ σ'', σ' < σ'' → σ'' < σ → ent σ'' c = 0) : prevStep c σ = some σ' := by
  rcases hp : prevStep c σ with _ | σ₁
  · exact absurd (prevStep_none hp σ' h1) h2
  · obtain ⟨g1, g2, g3⟩ := prevStep_some hp
    rcases lt_trichotomy σ₁ σ' with h | h | h
    · exact absurd (g3 σ' h h1) h2
    · rw [h]
    · exact absurd (h3 σ₁ h g1) g2

lemma prevStep_eq_none {c : Coord k ℓ} {σ : ℕ} (h : ∀ σ' < σ, ent σ' c = 0) :
    prevStep c σ = none := by
  rcases hp : prevStep c σ with _ | σ₁
  · rfl
  · obtain ⟨g1, g2, -⟩ := prevStep_some hp
    exact absurd (h σ₁ g1) g2

lemma pairwise_stepsC (c : Coord k ℓ) : (stepsC c).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

lemma idx_lt_of_lt {L : List ℕ} (hL : L.Pairwise (· < ·)) {a b : ℕ} (ha : a < L.length)
    (hb : b < L.length) (h : L[a] < L[b]) : a < b := by
  by_contra h'
  rcases Nat.lt_or_eq_of_le (not_lt.mp h') with h'' | h''
  · have := List.pairwise_iff_getElem.mp hL b a hb ha h''; omega
  · subst h''; omega

/-- **The track before an entry.** The track class at the step `σ = (stepsC c)[j]` is the
track of the previous entry `j - 1` of the column, or the start class for `j = 0`. -/
theorem trackAt_stepsC (e : Fin I.schemas.length) (c : Coord k ℓ) {j : ℕ}
    (hj : j < (stepsC c).length) :
    trackAt I e c (stepsC c)[j] =
      if h : j = 0 then startCls I e c else .track e ((stepsC c)[j - 1]'(by omega)) c := by
  have hP := pairwise_stepsC c
  have hmem : ∀ σ, σ < numSteps k ℓ → ent σ c ≠ 0 → ∃ i, ∃ hi : i < (stepsC c).length,
      (stepsC c)[i] = σ := fun σ h1 h2 =>
    List.getElem_of_mem ((mem_stepsC).mpr ⟨h1, h2⟩)
  have hN : (stepsC c)[j] < numSteps k ℓ := ((mem_stepsC).mp (List.getElem_mem hj)).1
  split
  · next h0 =>
    subst h0
    unfold trackAt
    rw [prevStep_eq_none fun σ' hσ' => by
      by_contra hne
      obtain ⟨i, hi, rfl⟩ := hmem σ' (by omega) hne
      have := idx_lt_of_lt hP hi hj hσ'
      omega]
  · next h0 =>
    unfold trackAt
    have hj1 : j - 1 < (stepsC c).length := by omega
    rw [prevStep_eq_some (σ' := (stepsC c)[j - 1])
      (List.pairwise_iff_getElem.mp hP _ _ hj1 hj (by omega))
      ((mem_stepsC).mp (List.getElem_mem hj1)).2 (fun σ'' g1 g2 => by
        by_contra hne
        obtain ⟨i, hi, rfl⟩ := hmem σ'' (by omega) hne
        have a1 := idx_lt_of_lt hP hj1 hi g1
        have a2 := idx_lt_of_lt hP hi hj g2
        omega)]

/-- **The track at the end of the strip**: the track of the last entry of the column (or the
start class if the column has no entry). -/
theorem trackAt_numSteps (e : Fin I.schemas.length) (c : Coord k ℓ) :
    trackAt I e c (numSteps k ℓ) =
      if h : stepsC c = [] then startCls I e c else .track e ((stepsC c).getLast h) c := by
  have hP := pairwise_stepsC c
  have hmem : ∀ σ, σ < numSteps k ℓ → ent σ c ≠ 0 → σ ∈ stepsC c := fun σ h1 h2 =>
    (mem_stepsC).mpr ⟨h1, h2⟩
  by_cases h0 : stepsC c = []
  · rw [dif_pos h0]
    unfold trackAt
    rw [prevStep_eq_none fun σ' hσ' => by
      by_contra hne; have := hmem σ' hσ' hne; rw [h0] at this; simp at this]
  · rw [dif_neg h0]
    unfold trackAt
    have hl : (stepsC c).getLast h0 ∈ stepsC c := List.getLast_mem h0
    rw [prevStep_eq_some (σ' := (stepsC c).getLast h0) ((mem_stepsC).mp hl).1
      ((mem_stepsC).mp hl).2 (fun σ'' g1 g2 => by
        by_contra hne
        have h'' := hmem σ'' g2 hne
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h''
        rw [List.getLast_eq_getElem] at g1
        have := idx_lt_of_lt hP (by have := List.length_pos_of_ne_nil h0; omega) hi g1
        omega)]

/-- For `k ≥ 2` every column has an entry (row `c.1`, or row `0` for the last block). -/
theorem stepsC_ne_nil (hk : 2 ≤ k) (c : Coord k ℓ) : stepsC c ≠ [] := by
  set σ : ℕ := if (c.1 : ℕ) < k - 1 then c.1 else 0 with hσdef
  have hσ : σ < k - 1 := by
    simp only [hσdef]; split_ifs <;> omega
  have hM : 0 < k - 1 + ℓ := by omega
  have hent : ent σ c ≠ 0 := by
    unfold ent stepRow
    rw [dif_pos hM]
    have e1 : (⟨σ % (k - 1 + ℓ), Nat.mod_lt _ hM⟩ : Fin (k - 1 + ℓ)) =
        Fin.castAdd ℓ (⟨σ, hσ⟩ : Fin (k - 1)) := by
      ext; simp [Nat.mod_eq_of_lt (show σ < k - 1 + ℓ by omega)]
    rw [e1, finSumFinEquiv_symm_apply_castAdd]
    simp only [checkMatrix, Matrix.of_apply]
    have : (c.1 : ℕ) = σ ∨ (c.1 : ℕ) = k - 1 := by
      simp only [hσdef]; split_ifs with h
      · left; rfl
      · right; have := c.1.isLt; omega
    rw [if_pos this]; exact one_ne_zero
  intro h
  have : σ ∈ stepsC c := (mem_stepsC).mpr ⟨by unfold numSteps; nlinarith, hent⟩
  rw [h] at this; simp at this

/-! ## Order of the sections -/

lemma schBase_add_le (e : Fin I.schemas.length) :
    schBase I e + schSize I e ≤ locBase I := by
  unfold schBase locBase
  have h := List.take_append_drop (e : ℕ) (List.finRange I.schemas.length)
  conv_rhs => rw [← h]
  rw [List.map_append, List.sum_append]
  have hd : List.drop (e : ℕ) (List.finRange I.schemas.length) =
      e :: List.drop ((e : ℕ) + 1) (List.finRange I.schemas.length) := by
    rw [List.drop_eq_getElem_cons (by simp)]; simp
  rw [hd]; simp

end Lax119563Proofs.Compiler

end Compiler_OrderPos

/-! ### Formerly `Lax119563Proofs.Compiler.OutDesc` -/

section Compiler_OutDesc

/-!
# The output of the compiler as a program-shaped list

`gDesc I ε` describes `graphDescription (reGraph I (ordL I) ε)` by data a sequential program
computes from the input (`graphDescription_eq_gDesc`, `encodeGraphPair_eq`):
* `n` (the sum of the class sizes), the colors `colorsOf 0` of the class sizes of `ordCls I`;
* `m`, then for every schema `e`, every hub class of `hubsCls I e` and every label `l` (with
  index `i`), the pairs `(hubStart X + i, v)` for `v ∈ hubNbrs ε X l`: the slot positions
  `slotPos` (closed formulas of `OrderPos`: `schBase`, `hubSize`, `sumSize`, `entBefore`,
  `nEnt`, `coefSteps`, `locStart` and the rank of a coordinate in `coordList (I.domain v)`),
  sorted.

Sorted forms: `hubNbrs_link`, `hubNbrs_upd`, `hubNbrs_upd_first` need no sorting (the slot
order, resp. track, coefficient, start coordinate); `hubNbrs_junc` is the sum followed by the
two coordinate positions sorted.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Generic: indexed flatMaps over blocks -/

section Generic

variable {α β γ δ : Type*}

lemma finRange_map_getElem (L : List α) :
    (List.finRange L.length).map (fun u : Fin L.length => (L[(u : ℕ)], (u : ℕ))) = L.zipIdx := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

lemma finRange_flatMap_eq_zipIdx (L : List α) (g : ℕ → α → List δ) :
    (List.finRange L.length).flatMap (fun u : Fin L.length => g u L[(u : ℕ)]) =
      L.zipIdx.flatMap fun p => g p.2 p.1 := by
  rw [← finRange_map_getElem, List.flatMap_map]

lemma zipIdx_map_pair (G : β × γ → ℕ → List δ) (X : β) : ∀ (ls : List γ) (s : ℕ),
    ((ls.map fun m => (X, m)).zipIdx s).flatMap (fun q => G q.1 q.2) =
      (ls.zipIdx s).flatMap fun q => G (X, q.1) q.2
  | [], _ => rfl
  | m :: ls, s => by
    simp only [List.map_cons, List.zipIdx_cons, List.flatMap_cons]
    rw [zipIdx_map_pair G X ls (s + 1)]

variable [DecidableEq β]

/-- Indexed flatMap over a list of blocks: each block is indexed from its start. -/
lemma zipIdx_flatMap_blocks (G : β × γ → ℕ → List δ) :
    ∀ (P : List (β × List γ)) (s : ℕ), (P.map Prod.fst).Nodup →
      ((P.flatMap fun p => p.2.map fun m => (p.1, m)).zipIdx s).flatMap (fun q => G q.1 q.2) =
        P.flatMap fun p => (p.2.zipIdx (s + startIn P p.1)).flatMap fun q => G (p.1, q.1) q.2
  | [], _, _ => rfl
  | (X, ls) :: P, s, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.flatMap_cons, List.zipIdx_append, List.flatMap_append,
      zipIdx_flatMap_blocks G P _ hnd.2, List.flatMap_cons]
    congr 1
    · have : startIn ((X, ls) :: P) X = 0 := startIn_cons_self X ls P
      rw [this, Nat.add_zero]
      exact zipIdx_map_pair G X ls s
    · refine List.flatMap_congr fun p hp => ?_
      have hne : p.1 ≠ X := fun h => hnd.1 (h ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
      have e1 : startIn ((X, ls) :: P) p.1 = ls.length + startIn P p.1 := by
        have := startIn_append_right (P := [(X, ls)]) (P' := P) (X := p.1) (by simpa using hne)
        simpa [sizeOf'] using this
      rw [e1, List.length_map, Nat.add_assoc]

lemma filterMap_congr' {f g : α → Option β} : ∀ {l : List α}, (∀ a ∈ l, f a = g a) →
    l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a (by simp),
      filterMap_congr' (fun b hb => h b (List.mem_cons_of_mem _ hb))]

end Generic

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (ε : ZMod 2)

/-! ## Edges per hub class -/

lemma nbrPos_of_not_hub {x : VName I} (h : isHub I x.1 = false) : nbrPos I ε x = [] := by
  obtain ⟨X, l⟩ := x
  cases X <;> simp_all [isHub, nbrPos, slotsOf]

/-- **The edges, per hub class.** For every schema and every hub class `X` of `hubsCls I e`
with labels `ls`, the label with index `i` sits at `clsStart X + i`. -/
theorem edgeList_hubsCls :
    edgeList (reGraph I (ordL I) ε) =
      (List.finRange I.schemas.length).flatMap fun e => (hubsCls I e).flatMap fun p =>
        (p.2.zipIdx (clsStart I p.1)).flatMap fun q =>
          (nbrPos I ε (p.1, q.1)).map fun v => (q.2, v) := by
  rw [edgeList_nbrPos]
  have h1 := finRange_flatMap_eq_zipIdx (ordL I)
    (fun u x => (nbrPos I ε x).map fun v => (u, v))
  rw [h1]
  have h2 := zipIdx_flatMap_blocks (fun x u => (nbrPos I ε x).map fun v => (u, v)) (ordCls I) 0
    (nodup_ordCls_fst I)
  have h3 : (ordCls I).flatMap (fun p => p.2.map fun m => (p.1, m)) = ordL I :=
    (ordL_eq_flatMap I).symm
  rw [h3] at h2
  rw [h2]
  simp only [Nat.zero_add]
  have hc : ∀ F : ICls I × List Lab → List (ℕ × ℕ), (ordCls I).flatMap F =
      ((List.finRange I.schemas.length).flatMap fun e => hubsCls I e ++ nonhubsCls I e).flatMap F
        ++ ((List.finRange I.numLocations).flatMap fun v =>
          (coordList (I.domain v)).map fun c => (Cls.coord v c, coordLabs I v)).flatMap F :=
    fun F => by rw [ordCls, List.flatMap_append]
  rw [hc, List.flatMap_assoc]
  have hloc : ((List.finRange I.numLocations).flatMap fun v =>
      (coordList (I.domain v)).map fun c => (Cls.coord v c, coordLabs I v)).flatMap
        (fun p => (p.2.zipIdx (startIn (ordCls I) p.1)).flatMap fun q =>
          (nbrPos I ε (p.1, q.1)).map fun v => (q.2, v)) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro p hp
    simp only [List.mem_flatMap, List.mem_map] at hp
    obtain ⟨v, -, c, -, rfl⟩ := hp
    rw [List.flatMap_eq_nil_iff]
    intro q _
    rw [nbrPos_of_not_hub I ε rfl]; rfl
  rw [hloc, List.append_nil]
  refine List.flatMap_congr fun e _ => ?_
  rw [List.flatMap_append]
  have hnon : (nonhubsCls I e).flatMap
      (fun p => (p.2.zipIdx (startIn (ordCls I) p.1)).flatMap fun q =>
          (nbrPos I ε (p.1, q.1)).map fun v => (q.2, v)) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro p hp
    rw [List.flatMap_eq_nil_iff]
    intro q hq
    have hl : q.1 ∈ p.2 := by
      have := List.mem_iff_getElem.mp hq
      obtain ⟨i, hi, he⟩ := this
      rw [← he, List.getElem_zipIdx]; exact List.getElem_mem _
    have hx : (p.1, q.1) ∈ nonhubsE I e := by
      rw [nonhubsE_eq, List.mem_flatMap]
      exact ⟨p, hp, List.mem_map.mpr ⟨q.1, hl, rfl⟩⟩
    rw [nbrPos_of_not_hub I ε (not_hub_of_mem_nonhubsE I hx).1]; rfl
  rw [hnon, List.append_nil]
  rfl

/-! ## Slot positions by closed formulas -/

/-- The position of the slot `(Y, b)` (class `Y`, required first effective bit `b`) in the
order, by the closed formulas: a coordinate class of an initialized location has one name
(present iff `b = ε · initSeed`), all other slot classes two names (offset `b`). -/
noncomputable def slotPos : ICls I → ZMod 2 → Option ℕ
  | .coord v c, b =>
    if (I.init v).isSome then
      (if b = ε * initSeed I v c then some (locStart I v + (coordList (I.domain v)).idxOf c)
        else none)
    else some (locStart I v + (coordList (I.domain v)).idxOf c * 2 + b.val)
  | .sum e c, b => some (schBase I e + hubSize I e + 2 * (coordList (dom I e)).idxOf c + b.val)
  | .track e σ c, b => some (schBase I e + hubSize I e + sumSize I e +
      2 * (entBefore I e c + (stepsC c).idxOf σ) + b.val)
  | .coef e σ, b => some (schBase I e + hubSize I e + sumSize I e + 2 * nEnt I e +
      2 * (coefSteps I e).idxOf σ + b.val)
  | _, _ => none

/-- **Slot positions.** -/
theorem posOpt_slot {x : VName I} (hx : x ∈ ordL I) {l : Lab} {s : ICls I × ZMod 2}
    (hs : s ∈ slotsOf I x.1 l) : posOpt I ε s.1 s.2 = slotPos I ε s.1 s.2 := by
  have hm := slot_mem_ordCls I hx hs
  have hv := valid_slots I hx hs
  have hh : isHub I s.1 = false :=
    (hubB_hub I ((hubB_iff_slotsOf I x.1 s.1 l (s.2, 0)).mpr hs)).2
  obtain ⟨Y, b⟩ := s
  simp only at hm hv hh ⊢
  cases Y with
  | coord v c =>
    have hc : c ∈ I.domain v := hv
    by_cases hi : (I.init v).isSome
    · have hm' : (Cls.coord v c, [((0 : ZMod 2), (0 : ZMod 2))]) ∈ ordCls I := by
        simpa [slotLabs, isSingleton, hi] using hm
      rw [posOpt_single I ε hm', clsStart_coord I hc]
      simp [slotPos, hi, coordLabs, initBit]
    · have hm' : (Cls.coord v c, bits1) ∈ ordCls I := by
        simpa [slotLabs, isSingleton, hi] using hm
      have hn : I.init v = none := Option.not_isSome_iff_eq_none.mp hi
      rw [posOpt_bits1 I ε hm', clsStart_coord I hc]
      simp [slotPos, hi, coordLabs, initBit, initSeed, hn, bits1]
  | sum e c =>
    obtain ⟨ht, hc⟩ := hv
    have hm' : (Cls.sum e c, bits1) ∈ ordCls I := by simpa [slotLabs, isSingleton] using hm
    rw [posOpt_bits1 I ε hm', clsStart_sum I ht hc]
    simp [slotPos, initBit]
  | track e σ c =>
    obtain ⟨hσ, hc, hent⟩ := hv
    have hm' : (Cls.track e σ c, bits1) ∈ ordCls I := by simpa [slotLabs, isSingleton] using hm
    rw [posOpt_bits1 I ε hm', clsStart_track I hc ((mem_stepsC).mpr ⟨hσ, hent⟩)]
    simp [slotPos, initBit]
  | coef e σ =>
    have hm' : (Cls.coef e σ, bits1) ∈ ordCls I := by simpa [slotLabs, isSingleton] using hm
    rw [posOpt_bits1 I ε hm', clsStart_coef I ((mem_coefSteps I).mpr hv)]
    simp [slotPos, initBit]
  | upd => simp [isHub] at hh
  | junc => simp [isHub] at hh
  | link => simp [isHub] at hh

/-! ## Hubs -/

/-- The start of a hub class, by the closed formulas. -/
noncomputable def hubStart : ICls I → ℕ
  | .junc e c => schBase I e + (coordList (dom I e)).idxOf c * colW I e
  | .link e c => schBase I e + (coordList (dom I e)).idxOf c * colW I e +
      (if isTern (sch I e) then 4 else 0)
  | .upd e σ c => schBase I e + (coordList (dom I e)).length * colW I e +
      4 * (entBefore I e c + (stepsC c).idxOf σ)
  | _ => 0

lemma clsStart_hubsCls {e : Fin I.schemas.length} {p : ICls I × List Lab}
    (hp : p ∈ hubsCls I e) : clsStart I p.1 = hubStart I p.1 := by
  simp only [hubsCls, List.mem_append, List.mem_flatMap, List.mem_map] at hp
  rcases hp with ⟨c, hc, hp⟩ | ⟨c, hc, σ, hσ, rfl⟩
  · have hc' : c ∈ dom I e := mem_coordList.mp hc
    rcases hp with hp | hp
    · split at hp
      · next ht =>
        simp only [List.mem_singleton] at hp; subst hp
        exact clsStart_junc I ht hc'
      · simp at hp
    · simp only [List.mem_singleton] at hp; subst hp
      exact clsStart_link I hc'
  · exact clsStart_upd I (mem_coordList.mp hc) hσ

/-- The sorted neighbor positions of the hub name `(X, l)`, by the closed formulas. -/
noncomputable def hubNbrs (X : ICls I) (l : Lab) : List ℕ :=
  ((slotsOf I X l).filterMap fun s => slotPos I ε s.1 s.2).mergeSort fun a b => decide (a ≤ b)

lemma mem_ordCls_of_hubsCls {e : Fin I.schemas.length} {p : ICls I × List Lab}
    (hp : p ∈ hubsCls I e) : p ∈ ordCls I := by
  unfold ordCls
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, List.mem_finRange e,
    List.mem_append_left _ hp⟩)

lemma nbrPos_hubsCls {e : Fin I.schemas.length} {p : ICls I × List Lab}
    (hp : p ∈ hubsCls I e) {l : Lab} (hl : l ∈ p.2) :
    nbrPos I ε (p.1, l) = hubNbrs I ε p.1 l := by
  have hx : (p.1, l) ∈ ordL I := by
    rw [ordL_eq_flatMap, List.mem_flatMap]
    exact ⟨p, mem_ordCls_of_hubsCls I hp, List.mem_map.mpr ⟨l, hl, rfl⟩⟩
  have hhub : isHub I p.1 = true :=
    mem_hubsCls_fst I (List.mem_map.mpr ⟨p, hp, rfl⟩)
  unfold nbrPos hubNbrs
  rw [eff_hub I ε (x := (p.1, l)) hhub]
  congr 1
  exact filterMap_congr' fun s hs => posOpt_slot I ε hx hs

/-- The edges of `G_ε` by the closed formulas: per schema, hub class and label. -/
noncomputable def gEdges : List (ℕ × ℕ) :=
  (List.finRange I.schemas.length).flatMap fun e => (hubsCls I e).flatMap fun p =>
    (p.2.zipIdx (hubStart I p.1)).flatMap fun q =>
      (hubNbrs I ε p.1 q.1).map fun v => (q.2, v)

/-- **The edge list by closed formulas.** -/
theorem edgeList_eq_gEdges : edgeList (reGraph I (ordL I) ε) = gEdges I ε := by
  rw [edgeList_hubsCls, gEdges]
  refine List.flatMap_congr fun e _ => List.flatMap_congr fun p hp => ?_
  rw [clsStart_hubsCls I hp]
  refine List.flatMap_congr fun q hq => ?_
  have hl : q.1 ∈ p.2 := by
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hq
    rw [← he, List.getElem_zipIdx]; exact List.getElem_mem _
  rw [nbrPos_hubsCls I ε hp hl]

/-! ## The description of the graphs -/

/-- The class sizes in the order. -/
noncomputable def clsSizes : List ℕ := (ordCls I).map fun p => p.2.length

/-- **The description of `G_ε` by closed formulas**: `n`, the colors, `m`, the edges. -/
noncomputable def gDesc : List ℕ :=
  (clsSizes I).sum :: colorsOf 0 (clsSizes I) ++
    (gEdges I ε).length :: (gEdges I ε).flatMap fun e => [e.1, e.2]

lemma length_ordL : (ordL I).length = (clsSizes I).sum := by
  rw [ordL_eq_flatMap, List.length_flatMap, clsSizes]
  simp [blk]

/-- **The output of the compiler.** -/
theorem graphDescription_eq_gDesc :
    graphDescription (reGraph I (ordL I) ε) = gDesc I ε := by
  have hc := colors_reGraph I ε
  unfold graphDescription gDesc
  rw [hc, edgeList_eq_gEdges]
  simp only [List.cons_append, List.cons.injEq]
  refine ⟨?_, ?_⟩
  · show (ordL I).length = _
    exact length_ordL I
  · rfl

/-- **The encoding of the output pair.** -/
theorem encodeGraphPair_eq :
    encodeGraphPair (reGraph I (ordL I) 0) (reGraph I (ordL I) 1) =
      encodeNats (gDesc I 0 ++ gDesc I 1) := by
  rw [encodeGraphPair, graphDescription_eq_gDesc, graphDescription_eq_gDesc]

/-! ## Sorted forms of the neighbor lists -/

/-- `mergeSort` returns the sorted permutation. -/
lemma mergeSort_eq_of {L L' : List ℕ} (hp : L'.Perm L) (hs : L'.Pairwise (· ≤ ·)) :
    L.mergeSort (fun a b => decide (a ≤ b)) = L' := by
  have h1 := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
    (fun a b c h₁ h₂ => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) L
  refine List.Perm.eq_of_pairwise (le := fun a b : ℕ => a ≤ b)
    (fun a b _ _ h₁ h₂ => le_antisymm h₁ h₂) (by simpa using h1) hs
    ((List.mergeSort_perm L _).trans hp.symm)

lemma schSize_eq (e : Fin I.schemas.length) :
    schSize I e = hubSize I e + sumSize I e + 2 * nEnt I e + 2 * (coefSteps I e).length := by
  rw [schSize, sizeOf'_append, sizeOf'_hubsCls, nonhubsCls_eq, sizeOf'_append, sizeOf'_append,
    sizeOf'_sumPart, trackPart, sizeOf'_ent, sizeOf'_map_const]
  simp [bits1]; ring

lemma ent_lt_nEnt {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) {σ : ℕ}
    (hσ : σ ∈ stepsC c) : entBefore I e c + (stepsC c).idxOf σ < nEnt I e := by
  have hcD : c ∈ coordList (dom I e) := mem_coordList.mpr hc
  have hi : (coordList (dom I e)).idxOf c < (coordList (dom I e)).length :=
    List.idxOf_lt_length_of_mem hcD
  have hj : (stepsC c).idxOf σ < (stepsC c).length := List.idxOf_lt_length_of_mem hσ
  unfold nEnt entBefore
  have e1 := List.take_append_drop ((coordList (dom I e)).idxOf c) (coordList (dom I e))
  rw [List.drop_eq_getElem_cons hi, List.getElem_idxOf hi] at e1
  conv_rhs => rw [← e1]
  rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  omega

lemma val_lt_two (b : ZMod 2) : b.val < 2 := ZMod.val_lt b

/-- Track positions lie before the coefficient section. -/
lemma track_lt_coef {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) {σ : ℕ}
    (hσ : σ ∈ stepsC c) (b : ZMod 2) :
    schBase I e + hubSize I e + sumSize I e + 2 * (entBefore I e c + (stepsC c).idxOf σ) +
      b.val < schBase I e + hubSize I e + sumSize I e + 2 * nEnt I e := by
  have := ent_lt_nEnt I hc hσ; have := val_lt_two b; omega

/-- Coefficient positions lie before the location section. -/
lemma coef_lt_locBase {e : Fin I.schemas.length} {σ : ℕ} (hσ : σ ∈ coefSteps I e)
    (b : ZMod 2) :
    schBase I e + hubSize I e + sumSize I e + 2 * nEnt I e + 2 * (coefSteps I e).idxOf σ +
      b.val < locBase I := by
  have h1 := schBase_add_le I e
  rw [schSize_eq] at h1
  have := List.idxOf_lt_length_of_mem hσ; have := val_lt_two b; omega

lemma coord_ge_locBase {v : Fin I.numLocations} {c : Coord k ℓ} {b : ZMod 2} {q : ℕ}
    (h : slotPos I ε (.coord v c) b = some q) : locBase I ≤ q := by
  simp only [slotPos] at h
  split_ifs at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> rw [← h] <;>
    simp only [locStart] <;> omega

lemma coef_mem {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) {σ : ℕ}
    (hσ : σ ∈ stepsC c) : σ ∈ coefSteps I e :=
  (mem_coefSteps I).mpr ⟨((mem_stepsC).mp hσ).1, c, hc, ((mem_stepsC).mp hσ).2⟩

/-- All elements of `o.toList` are at least `a`. -/
lemma pairwise_cons_toList {a : ℕ} {o : Option ℕ} (h : ∀ q, o = some q → a ≤ q) :
    (a :: o.toList).Pairwise (· ≤ ·) := by
  cases o with
  | none => simp
  | some q => simp [h q rfl]

/-- **Links**: the last track of the column, then the end coordinate (if present). -/
theorem hubNbrs_link (hk : 2 ≤ k) {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hc : c ∈ dom I e) (l : Lab) :
    hubNbrs I ε (.link e c) l =
      (slotPos I ε (trackAt I e c (numSteps k ℓ)) l.1).toList ++
        (slotPos I ε (endCls I e c) l.1).toList := by
  have hne := stepsC_ne_nil hk c
  have hσ : (stepsC c).getLast hne ∈ stepsC c := List.getLast_mem hne
  rw [hubNbrs, trackAt_numSteps, dif_neg hne]
  refine mergeSort_eq_of ?_ ?_
  · simp only [slotsOf, trackAt_numSteps, dif_neg hne, List.filterMap_cons, List.filterMap_nil]
    cases h1 : slotPos I ε (Cls.track e ((stepsC c).getLast hne) c) l.1 <;>
      cases h2 : slotPos I ε (endCls I e c) l.1 <;> simp
  · simp only [slotPos, Option.toList_some, List.singleton_append]
    apply pairwise_cons_toList
    intro q hq
    have h1 := coord_ge_locBase I ε hq
    have h2 := track_lt_coef I hc hσ l.1
    have h3 := coef_lt_locBase I (coef_mem I hc hσ) 0
    omega

/-- Sum positions lie before the track section. -/
lemma sum_lt_track {e : Fin I.schemas.length} {c : Coord k ℓ} (ht : isTern (sch I e) = true)
    (hc : c ∈ dom I e) (b : ZMod 2) :
    schBase I e + hubSize I e + 2 * (coordList (dom I e)).idxOf c + b.val <
      schBase I e + hubSize I e + sumSize I e := by
  have := List.idxOf_lt_length_of_mem (mem_coordList.mpr hc)
  have := val_lt_two b
  simp only [sumSize, ht, if_true]; omega

/-- **Updates (sorted in slot order)**: unless the update is the first entry of a column of a
binary schema, its neighbors are the previous track (or the sum), the track and the
coefficient, in this order. -/
theorem hubNbrs_upd {e : Fin I.schemas.length} {c : Coord k ℓ} {σ : ℕ} (hc : c ∈ dom I e)
    (hσ : σ ∈ stepsC c) (h : 0 < (stepsC c).idxOf σ ∨ isTern (sch I e) = true) (l : Lab) :
    hubNbrs I ε (.upd e σ c) l =
      (slotsOf I (.upd e σ c) l).filterMap fun s => slotPos I ε s.1 s.2 := by
  have hj : (stepsC c).idxOf σ < (stepsC c).length := List.idxOf_lt_length_of_mem hσ
  have hget : (stepsC c)[(stepsC c).idxOf σ] = σ := List.getElem_idxOf hj
  have htr := trackAt_stepsC I e c hj
  rw [hget] at htr
  obtain ⟨p0, hp0, hlt⟩ : ∃ p0, slotPos I ε (trackAt I e c σ) l.1 = some p0 ∧
      p0 < schBase I e + hubSize I e + sumSize I e +
        2 * (entBefore I e c + (stepsC c).idxOf σ) := by
    rw [htr]
    split
    · next h0 =>
      have ht : isTern (sch I e) = true := by rcases h with h | h; omega; exact h
      simp only [startCls, ht, if_true, slotPos]
      exact ⟨_, rfl, by have := sum_lt_track I ht hc l.1; omega⟩
    · next h0 =>
      simp only [slotPos]
      refine ⟨_, rfl, ?_⟩
      rw [(nodup_stepsC c).idxOf_getElem _ (by omega)]
      have := val_lt_two l.1; omega
  rw [hubNbrs]
  apply List.mergeSort_of_pairwise
  have h2 := track_lt_coef I hc hσ l.2
  have h3 := val_lt_two (l.1 + l.2)
  simp only [slotsOf, List.filterMap_cons, List.filterMap_nil, hp0]
  simp only [slotPos, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, decide_eq_true_eq, List.Pairwise.nil, and_true]
  exact ⟨⟨by omega, by omega⟩, by omega, fun _ h => h.elim⟩

/-- **Updates at the first entry of a column of a binary schema**: the track, the coefficient,
then the start coordinate (if present). -/
theorem hubNbrs_upd_first {e : Fin I.schemas.length} {c : Coord k ℓ} {σ : ℕ}
    (hc : c ∈ dom I e) (hσ : σ ∈ stepsC c) (h0 : (stepsC c).idxOf σ = 0)
    (ht : isTern (sch I e) = false) (l : Lab) :
    hubNbrs I ε (.upd e σ c) l =
      (slotPos I ε (.track e σ c) l.2).toList ++ (slotPos I ε (.coef e σ) (l.1 + l.2)).toList ++
        (slotPos I ε (startCls I e c) l.1).toList := by
  have hj : (stepsC c).idxOf σ < (stepsC c).length := List.idxOf_lt_length_of_mem hσ
  have hget : (stepsC c)[(stepsC c).idxOf σ] = σ := List.getElem_idxOf hj
  have htr := trackAt_stepsC I e c hj
  rw [hget, dif_pos h0] at htr
  have h2 := track_lt_coef I hc hσ l.2
  have h3 := coef_lt_locBase I (coef_mem I hc hσ) (l.1 + l.2)
  have hst : ∀ q, slotPos I ε (startCls I e c) l.1 = some q → locBase I ≤ q := fun q h1 => by
    simp only [startCls, ht, Bool.false_eq_true, if_false] at h1
    exact coord_ge_locBase I ε h1
  set tp := schBase I e + hubSize I e + sumSize I e +
    2 * (entBefore I e c + (stepsC c).idxOf σ) + l.2.val with htp
  set cp := schBase I e + hubSize I e + sumSize I e + 2 * nEnt I e +
    2 * (coefSteps I e).idxOf σ + (l.1 + l.2).val with hcp
  have et : slotPos I ε (.track e σ c) l.2 = some tp := rfl
  have ec : slotPos I ε (.coef e σ) (l.1 + l.2) = some cp := rfl
  rw [hubNbrs, et, ec]
  refine mergeSort_eq_of ?_ ?_
  · simp only [slotsOf, List.filterMap_cons, List.filterMap_nil, htr, et, ec]
    cases h1 : slotPos I ε (startCls I e c) l.1 with
    | none => simp
    | some q => simpa using List.perm_append_comm (l₁ := [tp, cp]) (l₂ := [q])
  · cases h1 : slotPos I ε (startCls I e c) l.1 with
    | none => simp; omega
    | some q => have := hst q h1; simp; omega

/-- **Junctions**: the sum, then the two coordinates (present ones) sorted. -/
theorem hubNbrs_junc {e : Fin I.schemas.length} {c : Coord k ℓ} (ht : isTern (sch I e) = true)
    (hc : c ∈ dom I e) (l : Lab) :
    hubNbrs I ε (.junc e c) l =
      (slotPos I ε (.sum e c) (l.1 + l.2)).toList ++
        ([(coordU e c, l.1), (coordV e c, l.2)].filterMap fun s => slotPos I ε s.1 s.2).mergeSort
          fun a b => decide (a ≤ b) := by
  set M := [(coordU e c, l.1), (coordV e c, l.2)].filterMap fun s => slotPos I ε s.1 s.2
  have hM : ∀ q ∈ M, locBase I ≤ q := by
    intro q hq
    simp only [M, List.filterMap_cons, List.filterMap_nil] at hq
    revert hq
    cases h1 : slotPos I ε (coordU e c) l.1 <;> cases h2 : slotPos I ε (coordV e c) l.2 <;>
      simp only [List.not_mem_nil, List.mem_cons, IsEmpty.forall_iff, or_false,
        forall_eq_or_imp, forall_eq] <;>
      first
        | exact coord_ge_locBase I ε h1
        | exact coord_ge_locBase I ε h2
        | exact fun h => (h ▸ coord_ge_locBase I ε h1)
        | exact fun h => (h ▸ coord_ge_locBase I ε h2)
        | (intro h; rcases h with rfl | rfl
           · exact coord_ge_locBase I ε h1
           · exact coord_ge_locBase I ε h2)
  set sp := schBase I e + hubSize I e + 2 * (coordList (dom I e)).idxOf c + (l.1 + l.2).val
    with hsp
  have es : slotPos I ε (.sum e c) (l.1 + l.2) = some sp := rfl
  have hL : (slotsOf I (.junc e c) l).filterMap (fun s => slotPos I ε s.1 s.2) = M ++ [sp] := by
    show List.filterMap _ ([(coordU e c, l.1), (coordV e c, l.2)] ++ [(Cls.sum e c, l.1 + l.2)]) = _
    rw [List.filterMap_append]
    simp only [List.filterMap_cons, List.filterMap_nil, es]
    rfl
  rw [hubNbrs, hL, es]
  refine mergeSort_eq_of ?_ ?_
  · exact (List.Perm.cons sp (List.mergeSort_perm M _)).trans
      (List.perm_append_comm (l₁ := [sp]) (l₂ := M))
  · have hs := sum_lt_track I ht hc (l.1 + l.2)
    have h1 := schBase_add_le I e
    rw [schSize_eq] at h1
    simp only [Option.toList_some, List.singleton_append]
    refine List.pairwise_cons.mpr ⟨fun q hq => ?_, ?_⟩
    · have := hM q ((List.mergeSort_perm M _).mem_iff.mp hq); omega
    · have h5 := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
        (fun a b c h₁ h₂ => by simp only [decide_eq_true_eq] at *; omega)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) M
      simpa using h5

end Lax119563Proofs.Compiler

end Compiler_OutDesc

/-! ### Formerly `Lax119563Proofs.Compiler.Final` -/

section Compiler_Final

/-!
# The matrix compiler from the machine

`compileM I := (reGraph I (ordL I) 0, reGraph I (ordL I) 1)` satisfies the game, size and edge
clauses (by `reGraph_spec` and `ordL_perm`), and its encoding is
`encodeNats (gDesc I 0 ++ gDesc I 1)` (`encode_compileM`). Hence the concept statement follows
from a single machine computing `encodeNats (gDesc I 0 ++ gDesc I 1)` from `encodeSystem I`
within the bound (`Compiler/Prog`).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.PebbleGame Lax119563.ImplicitSystemEncodings Lax119563.BinaryEncodings
open Lax119563.DeterministicTime Lax119563Proofs.Matrix
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Compiler

/-- The construction: the matrix graphs with vertices in the machine's order. -/
noncomputable def compileM {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) :
    ColoredGraph × ColoredGraph :=
  (reGraph I (ordL I) 0, reGraph I (ordL I) 1)

/-- The encoding of the construction is the list the machine emits. -/
theorem encode_compileM {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) :
    encodeGraphPair (compileM I).1 (compileM I).2 = encodeNats (gDesc I 0 ++ gDesc I 1) :=
  encodeGraphPair_eq I

end Lax119563Proofs.Compiler

end Compiler_Final

/-! ### Formerly `Lax119563Proofs.Compiler.OutLen` -/

section Compiler_OutLen

/-!
# The length of the output

With `n = |ordL I|` vertices per graph: every entry of `gDesc I ε` is at most `3 n`
(`gDesc_le`), `gDesc I ε` has at most `2 + 7 n` entries (`length_gDesc_le`), hence
`|encodeNats (gDesc I 0 ++ gDesc I 1)| ≤ 2 (2 + 7 n) (2 w + 1)` whenever `3 n < 2 ^ w`
(`length_out_le`), and `n ≤ 16 S` for `k ≥ 2` (`length_ordL_le`).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

lemma lt_of_mem_colorsOf : ∀ (s : ℕ) (ns : List ℕ) (c : ℕ), c ∈ colorsOf s ns → c < s + ns.sum
  | _, [], c, h => by simp [colorsOf] at h
  | s, n :: ns, c, h => by
    simp only [colorsOf, List.mem_append, List.mem_replicate] at h
    rcases h with ⟨hn, rfl⟩ | h
    · simp; omega
    · have := lt_of_mem_colorsOf (s + n) ns c h
      simp; omega

lemma length_colorsOf : ∀ (s : ℕ) (ns : List ℕ), (colorsOf s ns).length = ns.sum
  | _, [] => rfl
  | s, n :: ns => by simp [colorsOf, length_colorsOf (s + n) ns]

lemma edgeList_lt (G : ColoredGraph) {e : ℕ × ℕ} (he : e ∈ edgeList G) :
    e.1 < G.n ∧ e.2 < G.n := by
  classical
  unfold edgeList at he
  simp only [List.mem_flatMap, List.mem_map] at he
  obtain ⟨u, -, v, hv, rfl⟩ := he
  refine ⟨u.2, ?_⟩
  change v ∈ List.flatMap (fun a : Fin G.n => [(a : ℕ)]) _ at hv
  simp only [List.mem_flatMap, List.mem_singleton] at hv
  obtain ⟨a, -, rfl⟩ := hv
  exact a.2

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (ε : ZMod 2)

lemma length_slotsOf (X : ICls I) (l : Lab) : (slotsOf I X l).length ≤ 3 := by
  cases X <;> simp [slotsOf]

lemma length_nbrPos (x : VName I) : (nbrPos I ε x).length ≤ 3 := by
  unfold nbrPos
  rw [List.length_mergeSort]
  exact (List.length_filterMap_le _ _).trans (length_slotsOf I _ _)

lemma length_gEdges : (gEdges I ε).length ≤ 3 * (ordL I).length := by
  rw [← edgeList_eq_gEdges, edgeList_nbrPos, List.length_flatMap]
  calc ((List.finRange (ordL I).length).map fun u : Fin (ordL I).length =>
          ((nbrPos I ε (ordL I)[(u : ℕ)]).map fun v => ((u : ℕ), v)).length).sum
      ≤ ((List.finRange (ordL I).length).map fun _ => 3).sum := by
        apply List.sum_le_sum
        intro u _
        simpa using length_nbrPos I ε _
    _ = 3 * (ordL I).length := by simp [Nat.mul_comm]

lemma mem_gEdges_lt {e : ℕ × ℕ} (he : e ∈ gEdges I ε) :
    e.1 < (ordL I).length ∧ e.2 < (ordL I).length := by
  rw [← edgeList_eq_gEdges] at he
  exact edgeList_lt _ he

/-- Every entry of `gDesc I ε` is at most `3 n`. -/
lemma gDesc_le {v : ℕ} (hv : v ∈ gDesc I ε) : v ≤ 3 * (ordL I).length := by
  have hn := length_ordL I
  have hm := length_gEdges I ε
  simp only [gDesc, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap] at hv
  rcases hv with rfl | h | rfl | ⟨e, he, hv⟩
  · omega
  · have := lt_of_mem_colorsOf 0 _ _ h; omega
  · exact hm
  · have := mem_gEdges_lt I ε he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> omega

lemma length_gDesc_le : (gDesc I ε).length ≤ 2 + 7 * (ordL I).length := by
  have hn := length_ordL I
  have hm := length_gEdges I ε
  have e2 : ((gEdges I ε).flatMap fun e => [e.1, e.2]).length = 2 * (gEdges I ε).length := by
    rw [List.length_flatMap]; simp [Nat.mul_comm]
  simp only [gDesc, List.cons_append, List.length_cons, List.length_append, length_colorsOf, e2]
  omega

/-- **The length of the output.** -/
theorem length_out_le {w : ℕ} (hw : 3 * (ordL I).length < 2 ^ w) :
    (encodeNats (gDesc I 0 ++ gDesc I 1)).length ≤
      2 * (2 + 7 * (ordL I).length) * (2 * w + 1) := by
  have h := length_encodeNats_le (l := gDesc I 0 ++ gDesc I 1) (w := w) fun v hv => by
    rcases List.mem_append.mp hv with h | h
    · exact lt_of_le_of_lt (gDesc_le I 0 h) hw
    · exact lt_of_le_of_lt (gDesc_le I 1 h) hw
  have h0 := length_gDesc_le I 0
  have h1 := length_gDesc_le I 1
  rw [List.length_append] at h
  calc _ ≤ _ := h
    _ ≤ (2 * (2 + 7 * (ordL I).length)) * (2 * w + 1) :=
      Nat.mul_le_mul_right _ (by omega)

lemma length_ordL_le (hk : 2 ≤ k) : (ordL I).length ≤ 16 * matrixSize I := by
  rw [(ordL_perm I).length_eq]; exact card_vertexList_le hk

end Lax119563Proofs.Compiler

end Compiler_OutLen

/-! ### Formerly `Lax119563Proofs.Compiler.Bound` -/

section Compiler_Bound

/-!
# Arithmetic of the time bound

With `L = log₂(H + S + 2)` (so `L ≥ 1`):
* `nodeCost_le_sq`: for word size `w ≤ a (L + 1)`, `nodeCost w ≤ 64 (a + 3)² (L + 1)²`;
* `out_width`: `3 n < 2 ^ (L + 7)` for `n ≤ 16 S`, so the output has length
  `O((S + 1)(L + 1))` (`length_out_le_log`);
* `final_bound`: a time `K (H + S + 1)(L + 1)^e + 20 (H + Y) + 10` with
  `Y ≤ K (S + 1)(L + 1)` is at most `((2^(e+1) + 80) K + 30)(H + S) L^e` (for `H, e ≥ 1`);
  the program cost has `e = 3` because of the merge sort (`(L + 1)²` per word operation
  times a `log` factor).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

lemma nodeCost_le_sq {w a L : ℕ} (hw : w ≤ a * (L + 1)) :
    Ex.nodeCost w ≤ 64 * (a + 3) ^ 2 * (L + 1) ^ 2 := by
  have h1 : w + 3 ≤ (a + 3) * (L + 1) := by nlinarith
  have h2 : w + 1 ≤ (a + 3) * (L + 1) := by omega
  unfold Ex.nodeCost unitCost
  calc (w + 3) * (64 * (w + 1)) = 64 * ((w + 3) * (w + 1)) := by ring
    _ ≤ 64 * (((a + 3) * (L + 1)) * ((a + 3) * (L + 1))) := by
        apply Nat.mul_le_mul_left; exact Nat.mul_le_mul h1 h2
    _ = 64 * (a + 3) ^ 2 * (L + 1) ^ 2 := by ring

lemma one_le_log (H S : ℕ) : 1 ≤ Nat.log 2 (H + S + 2) :=
  Nat.le_log_of_pow_le (by norm_num) (by omega)

lemma lt_pow_log (N : ℕ) : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N

/-- The width of the output numbers. -/
lemma out_width {H S n : ℕ} (hn : n ≤ 16 * S) :
    3 * n < 2 ^ (Nat.log 2 (H + S + 2) + 7) := by
  have h := lt_pow_log (H + S + 2)
  rw [pow_add] at h ⊢
  have : (2 : ℕ) ^ 7 = 2 ^ 6 * 2 := by norm_num
  rw [this]
  nlinarith

/-- The output length in terms of `S` and `L`. -/
theorem length_out_le_log {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (hk : 2 ≤ k) (H : ℕ) :
    (encodeNats (gDesc I 0 ++ gDesc I 1)).length ≤
      2 * (2 + 7 * (16 * matrixSize I)) * (2 * (Nat.log 2 (H + matrixSize I + 2) + 7) + 1) := by
  have hn := length_ordL_le I hk
  refine (length_out_le I (out_width (H := H) hn)).trans ?_
  exact Nat.mul_le_mul_right _ (by omega)

/-- `(L + 1)^e ≤ 2^e L^e` for `L ≥ 1`. -/
lemma succ_pow_le {L : ℕ} (hL : 1 ≤ L) (e : ℕ) : (L + 1) ^ e ≤ 2 ^ e * L ^ e := by
  rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) e

/-- **The final arithmetic**, for any exponent `e ≥ 1` of the program cost. -/
theorem final_bound {H S L T K Y e : ℕ} (hH : 1 ≤ H) (hL : 1 ≤ L) (he : 1 ≤ e)
    (hT : T ≤ K * (H + S + 1) * (L + 1) ^ e + 20 * (H + Y) + 10)
    (hY : Y ≤ K * (S + 1) * (L + 1)) :
    T ≤ ((2 ^ (e + 1) + 80) * K + 30) * (H + S) * L ^ e := by
  have e1 : H + S + 1 ≤ 2 * (H + S) := by omega
  have e2 : L + 1 ≤ 2 * L := by omega
  have e3 : S + 1 ≤ 2 * (H + S) := by omega
  have hLe : 1 ≤ L ^ e := Nat.one_le_pow _ _ hL
  have hLL : L ≤ L ^ e := Nat.le_self_pow (by omega) L
  have t1 : K * (H + S + 1) * (L + 1) ^ e ≤ 2 ^ (e + 1) * K * (H + S) * L ^ e := by
    calc K * (H + S + 1) * (L + 1) ^ e ≤ K * (2 * (H + S)) * (2 ^ e * L ^ e) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ e1) (succ_pow_le hL e)
      _ = 2 ^ (e + 1) * K * (H + S) * L ^ e := by ring
  have t2 : Y ≤ 4 * K * (H + S) * L ^ e := by
    calc Y ≤ K * (2 * (H + S)) * (2 * L) := hY.trans
          (Nat.mul_le_mul (Nat.mul_le_mul_left _ e3) e2)
      _ = 4 * K * (H + S) * L := by ring
      _ ≤ 4 * K * (H + S) * L ^ e := Nat.mul_le_mul_left _ hLL
  have t3 : H ≤ (H + S) * L ^ e := by nlinarith
  have t4 : 10 ≤ 10 * ((H + S) * L ^ e) := by nlinarith
  calc T ≤ 2 ^ (e + 1) * K * (H + S) * L ^ e +
        20 * ((H + S) * L ^ e + 4 * K * (H + S) * L ^ e) + 10 * ((H + S) * L ^ e) := by omega
    _ = ((2 ^ (e + 1) + 80) * K + 30) * (H + S) * L ^ e := by ring

/-- `H ≥ 1`: the encoding of a system is nonempty. -/
lemma one_le_bitLength {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) : 1 ≤ bitLength I := by
  unfold bitLength encodeSystem systemDescription encodeNats
  simp [encodeNat]; omega

/-- **The concept from a structured program.** A statement `c` that, for word size
`w = a (L + 1)`, fits, emits `gDesc I 0 ++ gDesc I 1` from the zero state on the input
`encodeSystem I`, and costs at most `K (H + S + 1)(L + 1)^e` (`e ≥ 1`) yields a machine for the
machine clause of the matrix compiler, with time `((2^(e+1) + 80)(K + 3400) + 30)(H + S) L^e`. -/
theorem machine_of_program {R Q D : ℕ} (c : CStm R Q) (hd : c.depth ≤ D) (a K e : ℕ)
    (ha : 2 ≤ a) (he : 1 ≤ e)
    (hc : ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ I : ImplicitParitySystem k ℓ,
      let w := a * (Nat.log 2 (bitLength I + matrixSize I + 2) + 1)
      c.Fits (encodeSystem I) w (NSt.zero R Q) ∧
      (c.exec (encodeSystem I) (NSt.zero R Q)).out = gDesc I 0 ++ gDesc I 1 ∧
      c.cost (encodeSystem I) w (NSt.zero R Q) ≤
        K * (bitLength I + matrixSize I + 1) *
          (Nat.log 2 (bitLength I + matrixSize I + 2) + 1) ^ e) :
    ∃ M : Lax489179.TuringMachine.Machine, Lax489179.TuringMachine.Deterministic M ∧
      ∃ C c : ℕ, ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∀ I : ImplicitParitySystem k ℓ,
        Lax119563.DeterministicTime.ComputesWithin M (encodeSystem I)
          (encodeNats (gDesc I 0 ++ gDesc I 1))
          (C * (bitLength I + matrixSize I) *
            Nat.log 2 (bitLength I + matrixSize I + 2) ^ c) := by
  refine ⟨c.machine D, CStm.machine_deterministic D c, (2 ^ (e + 1) + 80) * (K + 3400) + 30, e,
    fun k hk ℓ hℓ I => ?_⟩
  obtain ⟨hf, ho, hco⟩ := hc k hk ℓ hℓ I
  set L := Nat.log 2 (bitLength I + matrixSize I + 2)
  have hw : 2 ≤ a * (L + 1) := by nlinarith
  have h := CStm.computesWithin (D := D) hw hd hf
  rw [ho] at h
  refine Lax119563Proofs.Reduction.ComputesWithin.mono h ?_
  have hY := length_out_le_log I (by omega) (bitLength I)
  have hL := one_le_log (bitLength I) (matrixSize I)
  have hH := one_le_bitLength I
  have hY' : (encodeNats (gDesc I 0 ++ gDesc I 1)).length ≤
      (K + 3400) * (matrixSize I + 1) * (L + 1) := by
    refine hY.trans ?_
    have : 2 * (L + 7) + 1 ≤ 15 * (L + 1) := by omega
    calc 2 * (2 + 7 * (16 * matrixSize I)) * (2 * (L + 7) + 1)
        ≤ 2 * (2 + 7 * (16 * matrixSize I)) * (15 * (L + 1)) := Nat.mul_le_mul_left _ this
      _ ≤ (K + 3400) * (matrixSize I + 1) * (L + 1) := by
          have hS : 2 * (2 + 7 * (16 * matrixSize I)) * 15 ≤ (K + 3400) * (matrixSize I + 1) := by nlinarith
          calc _ = 2 * (2 + 7 * (16 * matrixSize I)) * 15 * (L + 1) := by ring
            _ ≤ _ := Nat.mul_le_mul_right _ hS
  have hco' : c.cost (encodeSystem I) (a * (L + 1)) (NSt.zero R Q) ≤
      (K + 3400) * (bitLength I + matrixSize I + 1) * (L + 1) ^ e :=
    hco.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
  exact final_bound (K := K + 3400) hH hL he (by unfold bitLength at *; omega) hY'

end Lax119563Proofs.Compiler

end Compiler_Bound

/-! ### Formerly `Lax119563Proofs.Compiler.P4Rep` -/

section Compiler_P4Rep

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

end Compiler_P4Rep

/-! ### Formerly `Lax119563Proofs.Compiler.PChainSize` -/

section Compiler_PChainSize

/-!
# Word size and cost conversion for the compiler program

With `L = log₂(H + S + 2)` the program runs with word size `w = 8 (L + 1)`:
* `two_pow_word`: `2^14 (H + S + 2) ≤ 2^w`;
* `locBase_le`: `locBase I ≤ 16 S` (for `k ≥ 2`), so `16 (H + locBase + 1) ≤ 2^w`
  (`word_hS`), the hypothesis of `p2_good` (and, a fortiori, of `p0`, `p1`, `p1r`, `p3`);
* `cost_conv`: `K (H + 1)(log₂(H + 1) + 1) · nodeCost w ≤ 7744 K (H + S + 1)(L + 1)^3`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-- The word size of the compiler program. -/
def wordOf (H S : ℕ) : ℕ := 8 * (Nat.log 2 (H + S + 2) + 1)

lemma two_le_wordOf (H S : ℕ) : 2 ≤ wordOf H S := by unfold wordOf; omega

/-- `2^14 (H + S + 2) ≤ 2^w`. -/
lemma two_pow_word (H S : ℕ) : 16384 * (H + S + 2) ≤ 2 ^ wordOf H S := by
  have hL := one_le_log H S
  have hN := lt_pow_log (H + S + 2)
  set L := Nat.log 2 (H + S + 2)
  have e : 8 * (L + 1) = (L + 1) + (14 + 7 * (L - 1)) := by omega
  have h14 : (2 : ℕ) ^ 14 ≤ 2 ^ (14 + 7 * (L - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold wordOf
  rw [e, pow_add]
  have : (16384 : ℕ) = 2 ^ 14 := by norm_num
  rw [this, mul_comm]
  exact Nat.mul_le_mul hN.le h14

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The schema section is part of the vertex order. -/
lemma locBase_le_length : locBase I ≤ (ordL I).length := by
  rw [length_ordL]
  have h1 : (clsSizes I).sum = sizeOf' (ordCls I) := rfl
  rw [h1, ordCls, sizeOf'_append, sizeOf'_flatMap]
  have h2 : ((List.finRange I.schemas.length).map
      fun e => sizeOf' (hubsCls I e ++ nonhubsCls I e)) =
      (List.finRange I.schemas.length).map (schSize I) := rfl
  rw [h2]
  exact Nat.le_add_right _ _

lemma locBase_le (hk : 2 ≤ k) : locBase I ≤ 16 * matrixSize I :=
  (locBase_le_length I).trans (length_ordL_le I hk)

/-- **The word-size hypothesis** of the passes `P0`–`P3`. -/
lemma word_hS (hk : 2 ≤ k) :
    16 * ((encodeSystem I).length + locBase I + 1) ≤
      2 ^ wordOf (encodeSystem I).length (matrixSize I) := by
  have h1 := locBase_le I hk
  have h2 := two_pow_word (encodeSystem I).length (matrixSize I)
  omega

/-- **Cost conversion**: `nodeCost_le_sq` with `a = 8`. -/
lemma cost_conv (K H S : ℕ) :
    K * (H + 1) * (Nat.log 2 (H + 1) + 1) * Ex.nodeCost (wordOf H S) ≤
      7744 * K * (H + S + 1) * (Nat.log 2 (H + S + 2) + 1) ^ 3 := by
  have hn := nodeCost_le_sq (a := 8) (L := Nat.log 2 (H + S + 2)) (w := wordOf H S) le_rfl
  have hl : Nat.log 2 (H + 1) ≤ Nat.log 2 (H + S + 2) := Nat.log_mono_right (by omega)
  set L := Nat.log 2 (H + S + 2)
  set l := Nat.log 2 (H + 1)
  set N := Ex.nodeCost (wordOf H S)
  have e1 : K * (H + 1) * (l + 1) ≤ K * (H + S + 1) * (L + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  calc K * (H + 1) * (l + 1) * N ≤ K * (H + S + 1) * (L + 1) * (64 * (8 + 3) ^ 2 * (L + 1) ^ 2) :=
        Nat.mul_le_mul e1 hn
    _ = 7744 * K * (H + S + 1) * (L + 1) ^ 3 := by ring

end Lax119563Proofs.Compiler

end Compiler_PChainSize

/-! ### Formerly `Lax119563Proofs.Compiler.PSys` -/

section Compiler_PSys

/-!
# The structure of the input of the compiler program

`systemDescription I = k :: ℓ :: W :: (locsDesc I ++ E :: schsDesc I)` (`sd_eq`), with the
locations described by `locD I v = ι(v) :: domainDescription (I.domain v)`.

* Positions: `encodeNats_drop`: dropping the code of a prefix leaves the code of the rest.
* Sizes: the numbers `W`, `|D_v|`, `E` are at most the bit length `H` (`W_le`, `card_le`,
  `E_le`), so they fit into words when `2 (H + 1) ≤ 2 ^ w` (`bits_lt_of_le`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Codes of lists -/

lemma encNats_cons (v : ℕ) (l : List ℕ) :
    encodeNats (v :: l) = encodeNat v ++ encodeNats l := by simp [encodeNats]

lemma encodeNats_append (A B : List ℕ) :
    encodeNats (A ++ B) = encodeNats A ++ encodeNats B := by
  simp [encodeNats]

lemma encodeNats_drop (A B : List ℕ) :
    (encodeNats (A ++ B)).drop (encodeNats A).length = encodeNats B := by
  rw [encodeNats_append, List.drop_left]

lemma length_le_encodeNats : ∀ L : List ℕ, L.length ≤ (encodeNats L).length
  | [] => le_rfl
  | v :: L => by
    rw [encNats_cons, List.length_append, List.length_cons]
    have := length_le_encodeNats L
    have : 1 ≤ (encodeNat v).length := by simp [encodeNat]
    omega

/-- A number below `H + 1 ≤ 2 ^ (w - 1)` has fewer than `w` bits. -/
lemma bits_lt_of_le {v H w : ℕ} (hv : v ≤ H) (hH : 2 * (H + 1) ≤ 2 ^ w) :
    (Nat.bits v).length < w := by
  rw [Nat.size_eq_bits_len]
  rcases w with _ | w
  · simp at hH; omega
  · have h1 : v < 2 ^ w := by rw [pow_succ] at hH; omega
    have := Nat.size_le.mpr h1
    omega

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## The description of a system -/

/-- The description of location `v`. -/
def locD (v : Fin I.numLocations) : List ℕ :=
  initNum (I.init v) :: domainDescription (I.domain v)

/-- The descriptions of all locations. -/
def locsDesc : List ℕ := (List.finRange I.numLocations).flatMap (locD I)

/-- The descriptions of all schemas. -/
def schsDesc : List ℕ := I.schemas.flatMap schemaDescription

lemma sd_eq : systemDescription I =
    k :: ℓ :: I.numLocations :: (locsDesc I ++ I.schemas.length :: schsDesc I) := by
  simp [systemDescription, locsDesc, schsDesc]; rfl

lemma encodeSystem_eq : encodeSystem I = encodeNats (systemDescription I) := rfl

/-- The descriptions of the first `j` locations. -/
def locsPre (j : ℕ) : List ℕ :=
  ((List.finRange I.numLocations).take j).flatMap (locD I)

/-- The descriptions of the locations from `j` on. -/
def locsSuf (j : ℕ) : List ℕ :=
  ((List.finRange I.numLocations).drop j).flatMap (locD I)

lemma locsDesc_split (j : ℕ) : locsDesc I = locsPre I j ++ locsSuf I j := by
  rw [locsDesc, locsPre, locsSuf, ← List.flatMap_append, List.take_append_drop]

lemma locsSuf_cons {j : ℕ} (hj : j < I.numLocations) :
    locsSuf I j = locD I ⟨j, hj⟩ ++ locsSuf I (j + 1) := by
  rw [locsSuf, List.drop_eq_getElem_cons (by simpa using hj), List.flatMap_cons, locsSuf]
  simp

lemma locsPre_succ {j : ℕ} (hj : j < I.numLocations) :
    locsPre I (j + 1) = locsPre I j ++ locD I ⟨j, hj⟩ := by
  rw [locsPre, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [locsPre]

lemma locsPre_all : locsPre I I.numLocations = locsDesc I := by
  rw [locsPre, locsDesc, List.take_of_length_le (by simp)]

lemma locsSuf_all : locsSuf I I.numLocations = [] := by
  rw [locsSuf, List.drop_of_length_le (by simp)]; rfl

/-- The position of the description of location `j` in the input. -/
def posAt (j : ℕ) : ℕ := (encodeNats ([k, ℓ, I.numLocations] ++ locsPre I j)).length

lemma sd_split (j : ℕ) : systemDescription I =
    ([k, ℓ, I.numLocations] ++ locsPre I j) ++ (locsSuf I j ++ I.schemas.length :: schsDesc I) := by
  rw [sd_eq, locsDesc_split I j]; simp

lemma drop_posAt (j : ℕ) : (encodeSystem I).drop (posAt I j) =
    encodeNats (locsSuf I j ++ I.schemas.length :: schsDesc I) := by
  rw [encodeSystem_eq, sd_split I j, posAt, encodeNats_drop]

lemma posAt_le (j : ℕ) : posAt I j ≤ (encodeSystem I).length := by
  rw [encodeSystem_eq, sd_split I j, posAt,
    encodeNats_append ([k, ℓ, I.numLocations] ++ locsPre I j), List.length_append]; omega

lemma posAt_succ {j : ℕ} (hj : j < I.numLocations) :
    posAt I (j + 1) = posAt I j + (encodeNats (locD I ⟨j, hj⟩)).length := by
  simp only [posAt, locsPre_succ I hj, ← List.append_assoc, encodeNats_append,
    List.length_append]

/-- The start of the input: `k`, `ℓ`, `W`. -/
lemma posAt_zero : posAt I 0 = (encodeNat k).length + (encodeNat ℓ).length +
    (encodeNat I.numLocations).length := by
  simp [posAt, locsPre, encNats_cons, encodeNats]; ring

lemma drop_zero_k : (encodeSystem I).drop 0 = encodeNat k ++
    encodeNats (ℓ :: I.numLocations :: (locsDesc I ++ I.schemas.length :: schsDesc I)) := by
  rw [List.drop_zero, encodeSystem_eq, sd_eq, encNats_cons]

lemma drop_ell : (encodeSystem I).drop (encodeNat k).length = encodeNat ℓ ++
    encodeNats (I.numLocations :: (locsDesc I ++ I.schemas.length :: schsDesc I)) := by
  rw [encodeSystem_eq, sd_eq, encNats_cons, List.drop_left, encNats_cons]

lemma drop_W : (encodeSystem I).drop ((encodeNat k).length + (encodeNat ℓ).length) =
    encodeNat I.numLocations ++
      encodeNats (locsDesc I ++ I.schemas.length :: schsDesc I) := by
  rw [encodeSystem_eq, sd_eq, encNats_cons, encNats_cons, ← List.append_assoc,
    show (encodeNat k).length + (encodeNat ℓ).length = (encodeNat k ++ encodeNat ℓ).length by
      simp, List.drop_left, encNats_cons]

/-! ## Sizes -/

/-- The bit length of the input. -/
abbrev H : ℕ := (encodeSystem I).length

lemma length_sd_le : (systemDescription I).length ≤ H I := length_le_encodeNats _

lemma two_le_locD (v : Fin I.numLocations) : 2 ≤ (locD I v).length := by
  simp [locD, domainDescription]

lemma W_le_locsDesc : I.numLocations ≤ (locsDesc I).length := by
  rw [locsDesc, List.length_flatMap]
  have : ∀ v ∈ List.finRange I.numLocations, 1 ≤ (locD I v).length :=
    fun v _ => le_trans (by norm_num) (two_le_locD I v)
  calc I.numLocations = ((List.finRange I.numLocations).map fun _ => 1).sum := by simp
    _ ≤ _ := List.sum_le_sum (by simpa using this)

lemma W_le : I.numLocations ≤ H I := by
  have := length_sd_le I
  have := W_le_locsDesc I
  rw [sd_eq] at *; simp at *; omega

lemma E_le_schsDesc : I.schemas.length ≤ (schsDesc I).length := by
  rw [schsDesc, List.length_flatMap]
  have : ∀ e ∈ I.schemas, 1 ≤ (schemaDescription e).length := by
    intro e _; cases e <;> simp [schemaDescription]
  calc I.schemas.length = (I.schemas.map fun _ => 1).sum := by simp
    _ ≤ _ := List.sum_le_sum (by simpa using this)

lemma E_le : I.schemas.length ≤ H I := by
  have := length_sd_le I
  have := E_le_schsDesc I
  rw [sd_eq] at *; simp at *; omega

/-- The number `|D|` of coordinates (the head of the domain description). -/
lemma domainDescription_head {D : Finset (Coord k ℓ)} :
    ∃ rest, domainDescription D = (D.image coordNum).card :: rest ∧
      (D.image coordNum).card ≤ rest.length := by
  refine ⟨((D.image coordNum).sort (· ≤ ·)).flatMap (coordNumDescription ℓ), ?_, ?_⟩
  · rw [domainDescription]; simp [Finset.length_sort]
  rw [List.length_flatMap]
  have : ∀ c ∈ (D.image coordNum).sort (· ≤ ·), 1 ≤ (coordNumDescription ℓ c).length := by
    intro c _; simp [coordNumDescription]
  calc (D.image coordNum).card = (((D.image coordNum).sort (· ≤ ·)).map fun _ => 1).sum := by
        simp
    _ ≤ _ := List.sum_le_sum (by simpa using this)

lemma card_image_eq_zero_iff {D : Finset (Coord k ℓ)} : (D.image coordNum).card = 0 ↔ D = ∅ := by
  simp

lemma domainDescription_empty : domainDescription (∅ : Finset (Coord k ℓ)) = [0] := by
  simp [domainDescription]

lemma card_le (v : Fin I.numLocations) : ((I.domain v).image coordNum).card ≤ H I := by
  obtain ⟨rest, he, hl⟩ := domainDescription_head (D := I.domain v)
  have h1 : (locD I v).length ≤ (locsDesc I).length := by
    rw [locsDesc, List.length_flatMap]
    exact List.le_sum_of_mem (List.mem_map_of_mem (List.mem_finRange v))
  have h2 := length_sd_le I
  rw [sd_eq] at h2
  simp only [List.length_cons, List.length_append] at h2
  simp only [locD, he, List.length_cons] at h1
  omega

end Lax119563Proofs.Compiler

end Compiler_PSys

/-! ### Formerly `Lax119563Proofs.Compiler.PTriv` -/

section Compiler_PTriv

/-!
# Pass `P0` of the compiler program: the triviality check

The compiler program works with `CR` registers and `CQ` number stacks (`PDefs` below).
`p0` skips `k` and `ℓ` (they may be exponential in `H` for trivial systems), reads `W`, and
for the locations in order reads `ι(v)` and `|D_v|`, stopping at the first nonempty domain;
if all domains are empty it reads `E`. It sets `rTriv = [trivSys I]` where `trivSys I` means
that all domains are empty and there is no schema (`p0_good`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Registers and stacks of the compiler program -/

/-- The number of registers of the compiler program. -/
abbrev CR : ℕ := 40
/-- The number of stacks of the compiler program. -/
abbrev CQ : ℕ := 16

/-- Scratch registers of the number readers. -/
def rT : Fin CR := 0
def rP : Fin CR := 1
/-- `W`. -/
def rW : Fin CR := 2
/-- Location counter. -/
def rJ : Fin CR := 3
/-- Flag: a nonempty domain was found. -/
def rNz : Fin CR := 4
/-- Read values. -/
def rA : Fin CR := 5
def rD : Fin CR := 6
/-- `E`. -/
def rE : Fin CR := 7
/-- The result of `P0`. -/
def rTriv : Fin CR := 8

/-! ## Final states of the readers -/

section Readers

variable {R Q : ℕ}

@[simp] lemma rdNumFinal_stk (st : NSt R Q) (r p t : Fin R) (v : ℕ) :
    (CStm.rdNumFinal st r p t v).stk = st.stk := rfl
@[simp] lemma rdNumFinal_out (st : NSt R Q) (r p t : Fin R) (v : ℕ) :
    (CStm.rdNumFinal st r p t v).out = st.out := rfl
@[simp] lemma rdNumFinal_pos (st : NSt R Q) (r p t : Fin R) (v : ℕ) :
    (CStm.rdNumFinal st r p t v).pos = st.pos + (encodeNat v).length := rfl
lemma rdNumFinal_env_r {st : NSt R Q} {r p t : Fin R} (hrp : r ≠ p) (hrt : r ≠ t) (v : ℕ) :
    (CStm.rdNumFinal st r p t v).env r = v := by
  simp [CStm.rdNumFinal, Function.update_of_ne hrp, Function.update_of_ne hrt]
lemma rdNumFinal_env_ne {st : NSt R Q} {r p t q : Fin R} (h1 : q ≠ r) (h2 : q ≠ p) (h3 : q ≠ t)
    (v : ℕ) : (CStm.rdNumFinal st r p t v).env q = st.env q := by
  simp [CStm.rdNumFinal, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3]

@[simp] lemma skipNumFinal_stk (st : NSt R Q) (t : Fin R) (v : ℕ) :
    (CStm.skipNumFinal st t v).stk = st.stk := rfl
@[simp] lemma skipNumFinal_out (st : NSt R Q) (t : Fin R) (v : ℕ) :
    (CStm.skipNumFinal st t v).out = st.out := rfl
@[simp] lemma skipNumFinal_pos (st : NSt R Q) (t : Fin R) (v : ℕ) :
    (CStm.skipNumFinal st t v).pos = st.pos + (encodeNat v).length := rfl
lemma skipNumFinal_env_ne {st : NSt R Q} {t q : Fin R} (h : q ≠ t) (v : ℕ) :
    (CStm.skipNumFinal st t v).env q = st.env q := by
  simp [CStm.skipNumFinal, Function.update_of_ne h]

end Readers

open CStm

/-! ## The program -/

/-- The body of the location loop of `P0`. -/
def p0Body : CStm CR CQ :=
  .seq (rdNumS rA rP rT) (.seq (rdNumS rD rP rT)
    (.ite (rv rD) (.seq (.set rNz (.const 1)) (.set rJ (rv rW)))
      (.set rJ (.add (rv rJ) (.const 1)))))

/-- The loop over the locations. -/
def p0Loop : CStm CR CQ := .loop (.lt (rv rJ) (rv rW)) p0Body

/-- The end of `P0`. -/
def p0End : CStm CR CQ :=
  .ite (rv rNz) (.set rTriv (.const 0))
    (.seq (rdNumS rE rP rT) (.set rTriv (.lt (rv rE) (.const 1))))

/-- **Pass `P0`.** -/
def p0 : CStm CR CQ :=
  .seq (skipNumS rT) (.seq (skipNumS rT) (.seq (rdNumS rW rP rT)
    (.seq (.set rJ (.const 0)) (.seq (.set rNz (.const 0)) (.seq p0Loop p0End)))))

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- A trivial system: no coordinate and no schema. -/
def trivSys : Prop := (∀ v, I.domain v = ∅) ∧ I.schemas = []

/-- The output for a trivial system: two empty graphs. -/
theorem gDesc_triv (h : trivSys I) (ε : ZMod 2) : gDesc I ε = [0, 0] := by
  have hE : I.schemas.length = 0 := by rw [h.2]; rfl
  have hc : ordCls I = [] := by
    rw [ordCls, List.append_eq_nil_iff]
    constructor
    · rw [List.flatMap_eq_nil_iff]; intro e; exact absurd e.2 (by omega)
    · rw [List.flatMap_eq_nil_iff]; intro v _
      simp [h.1 v, coordList]
  have he : gEdges I ε = [] := by
    rw [gEdges, List.flatMap_eq_nil_iff]; intro e; exact absurd e.2 (by omega)
  simp [gDesc, clsSizes, hc, he, colorsOf]

/-- The loop invariant of `P0`. -/
def p0Inv (st s : NSt CR CQ) : Prop :=
  s.env rW = I.numLocations ∧ s.stk = st.stk ∧ s.out = st.out ∧ s.env rJ ≤ I.numLocations ∧
    ((s.env rNz = 0 ∧ s.pos = posAt I (s.env rJ) ∧
        ∀ v : Fin I.numLocations, v.val < s.env rJ → I.domain v = ∅) ∨
      (s.env rNz = 1 ∧ s.env rJ = I.numLocations ∧ ∃ v, I.domain v ≠ ∅))

lemma locD_eq (v : Fin I.numLocations) : ∃ rest, locD I v =
    initNum (I.init v) :: ((I.domain v).image coordNum).card :: rest := by
  obtain ⟨rest, he, -⟩ := domainDescription_head (D := I.domain v)
  exact ⟨rest, by rw [locD, he]⟩

lemma initNum_le (a : Option (ZMod 2)) : initNum a ≤ 2 := by
  rcases a with _ | b
  · simp [initNum]
  · have := ZMod.val_lt b; simp [initNum]; omega

lemma three_le_H : 3 ≤ H I := by
  have := length_sd_le I
  rw [sd_eq] at this; simp at this; omega

/-- One iteration of the location loop. -/
lemma p0Body_good {w : ℕ} (hw : 2 ≤ w) (hH : 2 * (H I + 1) ≤ 2 ^ w) (st s : NSt CR CQ)
    (hI : p0Inv I st s) (hc : (Ex.lt (rv rJ) (rv rW)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p0Body s s'
        (20 * Ex.nodeCost w * ((H I - s.pos) - (H I - s'.pos)) + 50 * Ex.nodeCost w) ∧
      p0Inv I st s' ∧ I.numLocations - s'.env rJ < I.numLocations - s.env rJ ∧
      H I - s'.pos ≤ H I - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := unitCost_ge w
  obtain ⟨hW, hstk, hout, hjW, hcase⟩ := hI
  have hlt : s.env rJ < I.numLocations := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hW]; rw [if_neg h]
  rcases hcase with ⟨hnz, hpos, hemp⟩ | ⟨-, hj, -⟩
  swap; · omega
  set j := s.env rJ with hjdef
  set v : Fin I.numLocations := ⟨j, hlt⟩
  obtain ⟨rest, hloc⟩ := locD_eq I v
  set a := initNum (I.init v)
  set d := ((I.domain v).image coordNum).card
  have hx : (encodeSystem I).drop s.pos =
      encodeNat a ++ (encodeNat d ++ encodeNats (rest ++ (locsSuf I (j + 1) ++
        I.schemas.length :: schsDesc I))) := by
    rw [hpos, drop_posAt, locsSuf_cons I hlt, hloc]
    simp [encNats_cons, encodeNats_append]
  have hposle : s.pos ≤ H I := by rw [hpos]; exact posAt_le I j
  have hlenx : s.pos + (encodeNat a).length + (encodeNat d).length ≤ H I := by
    have := congrArg List.length hx
    simp only [List.length_drop, List.length_append] at this
    show _ ≤ (encodeSystem I).length
    have : s.pos ≤ (encodeSystem I).length := hposle
    omega
  have ha : (Nat.bits a).length < w := bits_lt_of_le (le_trans (initNum_le _)
    (by have := three_le_H I; omega)) hH
  have hd : (Nat.bits d).length < w := bits_lt_of_le (card_le I v) hH
  have r1 := rdNumS_good (Q := CQ) hw (r := rA) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s a _ hx ha
  set s1 := rdNumFinal s rA rP rT a
  have hx2 : (encodeSystem I).drop s1.pos = encodeNat d ++ encodeNats (rest ++
      (locsSuf I (j + 1) ++ I.schemas.length :: schsDesc I)) := by
    simp only [s1, rdNumFinal_pos]
    rw [← List.drop_drop, hx, List.drop_left]
  have r2 := rdNumS_good (Q := CQ) hw (r := rD) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s1 d _ hx2 hd
  set s2 := rdNumFinal s1 rD rP rT d
  have e2D : s2.env rD = d := rdNumFinal_env_r (by decide) (by decide) d
  have e2 : ∀ q, q ≠ rD → q ≠ rA → q ≠ rP → q ≠ rT → s2.env q = s.env q := by
    intro q h1 h2 h3 h4
    rw [rdNumFinal_env_ne h1 h3 h4, rdNumFinal_env_ne h2 h3 h4]
  have hp2 : s2.pos = s.pos + (encodeNat a).length + (encodeNat d).length := rfl
  have hWlt : I.numLocations < 2 ^ w := by have := W_le I; omega
  have hdw : d < 2 ^ w := by have := card_le I v; omega
  by_cases hd0 : d = 0
  · -- empty domain: next location
    have hemp' : I.domain v = ∅ := (card_image_eq_zero_iff).mp hd0
    have hjw : s2.env rJ + 1 < 2 ^ w := by
      have := W_le I
      rw [e2 rJ (by decide) (by decide) (by decide) (by decide)]; omega
    have r3 := Good.set (x := encodeSystem I) (w := w) (r := rJ) (st := s2)
      (e := .add (rv rJ) (.const 1)) (by simp only [Ex.Fits, Ex.eval, rv]; omega)
    refine ⟨_, (r1.seq (r2.seq (Good.iteF (by simp only [Ex.Fits, rv, e2D]; omega)
      (by simp [Ex.eval, rv, e2D, hd0]) r3))).mono ?_, ?_, ?_, ?_⟩
    · simp only [condCost, Ex.size, rv, NSt.set_pos, hp2]
      have hΔ : H I - s.pos - (H I - (s.pos + (encodeNat a).length + (encodeNat d).length)) =
          (encodeNat a).length + (encodeNat d).length := by omega
      rw [hΔ]
      generalize Ex.nodeCost w = N at *
      generalize unitCost w = U at *
      generalize (encodeNat a).length = la at *
      generalize (encodeNat d).length = ld at *
      ring_nf
      nlinarith
    · have hj' : (s2.set rJ (Ex.eval s2.env (.add (rv rJ) (.const 1)))).env rJ = j + 1 := by
        simp [Ex.eval, rv, e2 rJ (by decide) (by decide) (by decide) (by decide), j]
      refine ⟨?_, by simp [s2, s1, hstk], by simp [s2, s1, hout], by rw [hj']; omega,
        Or.inl ⟨?_, ?_, ?_⟩⟩
      · rw [NSt.set_env, Function.update_of_ne (by decide),
          e2 rW (by decide) (by decide) (by decide) (by decide), hW]
      · rw [NSt.set_env, Function.update_of_ne (by decide),
          e2 rNz (by decide) (by decide) (by decide) (by decide), hnz]
      · rw [hj', NSt.set_pos, hp2, hpos, posAt_succ I hlt]
        have : locD I v = [a, 0] := by
          rw [locD, hemp', domainDescription_empty]
        rw [this]; simp [encNats_cons, encodeNats, hd0]; omega
      · intro u hu
        rw [hj'] at hu
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | hu
        · exact hemp u hu
        · have : u = v := Fin.ext hu
          rw [this]; exact hemp'
    · simp only [NSt.set_env, Function.update_self, Ex.eval, rv,
        e2 rJ (by decide) (by decide) (by decide) (by decide)]; omega
    · simp only [NSt.set_pos, hp2]; omega
  · -- nonempty domain: stop
    have hne : I.domain v ≠ ∅ := fun h => hd0 ((card_image_eq_zero_iff).mpr h)
    have r3 := (Good.set (x := encodeSystem I) (w := w) (r := rNz) (st := s2) (e := .const 1)
      (by simp only [Ex.Fits]; omega)).seq
      (Good.set (r := rJ) (e := rv rW) (by
        simp only [Ex.Fits, rv, NSt.set_env, Function.update_of_ne (show rW ≠ rNz by decide),
          e2 rW (by decide) (by decide) (by decide) (by decide), hW]; exact hWlt))
    refine ⟨_, (r1.seq (r2.seq (Good.iteT (by simp only [Ex.Fits, rv, e2D]; omega)
      (by simp [Ex.eval, rv, e2D, hd0]) r3))).mono ?_, ?_, ?_, ?_⟩
    · simp only [condCost, Ex.size, rv, NSt.set_pos, hp2]
      have hΔ : H I - s.pos - (H I - (s.pos + (encodeNat a).length + (encodeNat d).length)) =
          (encodeNat a).length + (encodeNat d).length := by omega
      rw [hΔ]
      generalize Ex.nodeCost w = N at *
      generalize unitCost w = U at *
      generalize (encodeNat a).length = la at *
      generalize (encodeNat d).length = ld at *
      ring_nf
      nlinarith
    · have hj' : ((s2.set rNz (Ex.eval s2.env (.const 1))).set rJ
          (Ex.eval (s2.set rNz (Ex.eval s2.env (.const 1))).env (rv rW))).env rJ =
            I.numLocations := by
        simp [Ex.eval, rv, Function.update_of_ne (show rW ≠ rNz by decide),
          e2 rW (by decide) (by decide) (by decide) (by decide), hW]
      refine ⟨?_, by simp [s2, s1, hstk], by simp [s2, s1, hout], by rw [hj'],
        Or.inr ⟨?_, hj', v, hne⟩⟩
      · simp only [NSt.set_env, Function.update_of_ne (show rW ≠ rJ by decide),
          Function.update_of_ne (show rW ≠ rNz by decide)]
        rw [e2 rW (by decide) (by decide) (by decide) (by decide), hW]
      · simp [Ex.eval, Function.update_of_ne (show rNz ≠ rJ by decide)]
    · simp only [NSt.set_env, Function.update_self, Ex.eval, rv,
        Function.update_of_ne (show rW ≠ rNz by decide),
        e2 rW (by decide) (by decide) (by decide) (by decide), hW]; omega
    · simp only [NSt.set_pos, hp2]; omega

/-- The end of `P0`, after the loop. -/
lemma p0End_good {w : ℕ} (hw : 2 ≤ w) (hH : 2 * (H I + 1) ≤ 2 ^ w) (st s : NSt CR CQ)
    (hI : p0Inv I st s) (hc : (Ex.lt (rv rJ) (rv rW)).eval s.env = 0) :
    ∃ s', Good (encodeSystem I) w p0End s s' (30 * (H I + 1) * Ex.nodeCost w) ∧
      s'.stk = st.stk ∧ s'.out = st.out ∧ (s'.env rTriv = 1 ↔ trivSys I) ∧
      s'.env rTriv ≤ 1 := by
  have hU := CStm.nodeCost_ge w
  have hU' := unitCost_ge w
  have h4 : 4 ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  obtain ⟨hW, hstk, hout, hjW, hcase⟩ := hI
  rcases hcase with ⟨hnz, hpos, hemp⟩ | ⟨hnz, -, v, hne⟩
  · have hj : s.env rJ = I.numLocations := by
      simp only [Ex.eval, rv, hW] at hc; split_ifs at hc with h <;> omega
    have hx : (encodeSystem I).drop s.pos = encodeNat I.schemas.length ++ encodeNats (schsDesc I) := by
      rw [hpos, hj, drop_posAt, locsSuf_all]; simp [encNats_cons]
    have hEH := E_le I
    have r1 := rdNumS_good (Q := CQ) hw (r := rE) (p := rP) (t := rT) (by decide) (by decide)
      (by decide) s _ _ hx (bits_lt_of_le hEH hH)
    set s1 := rdNumFinal s rE rP rT I.schemas.length
    have e1 : s1.env rE = I.schemas.length := rdNumFinal_env_r (by decide) (by decide) _
    have r2 := Good.set (x := encodeSystem I) (w := w) (r := rTriv) (st := s1)
      (e := .lt (rv rE) (.const 1)) (by simp only [Ex.Fits, rv, e1]; omega)
    have hlen : (encodeNat I.schemas.length).length ≤ H I := by
      have := congrArg List.length hx
      simp only [List.length_drop, List.length_append] at this
      show _ ≤ (encodeSystem I).length
      omega
    refine ⟨_, (Good.iteF (by simp only [Ex.Fits, rv]; rw [hnz]; omega)
      (by simp [Ex.eval, rv, hnz]) (r1.seq r2)).mono ?_, by simp [s1, hstk],
      by simp [s1, hout], ?_, ?_⟩
    · simp only [condCost, Ex.size]
      generalize Ex.nodeCost w = N at *
      generalize unitCost w = U at *
      generalize (encodeNat I.schemas.length).length = lE at *
      nlinarith
    · simp only [NSt.set_env, Function.update_self, Ex.eval, rv, e1]
      constructor
      · intro h
        have h0 : I.schemas.length < 1 := by
          by_contra h0; rw [if_neg h0] at h; exact absurd h zero_ne_one
        exact ⟨fun u => hemp u (by rw [hj]; exact u.2), List.eq_nil_of_length_eq_zero (by omega)⟩
      · rintro ⟨-, hs⟩; simp [hs]
    · simp only [NSt.set_env, Function.update_self, Ex.eval, rv, e1]
      by_cases h0 : I.schemas.length < 1 <;> simp [h0]
  · have r1 := Good.set (x := encodeSystem I) (w := w) (r := rTriv) (st := s) (e := .const 0)
      (by simp only [Ex.Fits]; omega)
    refine ⟨_, (Good.iteT (by simp only [Ex.Fits, rv]; rw [hnz]; omega)
      (by simp [Ex.eval, rv, hnz]) r1).mono ?_, hstk, hout, ?_, ?_⟩
    · simp only [condCost, Ex.size]
      generalize Ex.nodeCost w = N at *
      generalize unitCost w = U at *
      nlinarith
    · simp only [NSt.set_env, Function.update_self, Ex.eval]
      constructor
      · intro h; exact absurd h zero_ne_one
      · rintro ⟨h, -⟩; exact absurd (h v) hne
    · simp [Ex.eval]

/-- **Pass `P0`.** From the start of the input, `P0` sets `rTriv` to `[trivSys I]`, keeping
the stacks and the output. -/
theorem p0_good {w : ℕ} (hw : 2 ≤ w) (hH : 2 * (H I + 1) ≤ 2 ^ w) (st : NSt CR CQ)
    (hp : st.pos = 0) :
    ∃ st', Good (encodeSystem I) w p0 st st' (200 * (H I + 1) * Ex.nodeCost w) ∧
      st'.stk = st.stk ∧ st'.out = st.out ∧ (st'.env rTriv = 1 ↔ trivSys I) ∧
      st'.env rTriv ≤ 1 := by
  have hU := CStm.nodeCost_ge w
  have hU' := unitCost_ge w
  have hWH := W_le I
  have h4 : 4 ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have r1 := skipNumS_good (Q := CQ) hw (t := rT) st k _ (by rw [hp]; exact drop_zero_k I)
  set s1 := skipNumFinal st rT k
  have r2 := skipNumS_good (Q := CQ) hw (t := rT) s1 ℓ _
    (by simp only [s1, skipNumFinal_pos, hp, zero_add]; exact drop_ell I)
  set s2 := skipNumFinal s1 rT ℓ
  have r3 := rdNumS_good (Q := CQ) hw (r := rW) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s2 I.numLocations _
    (by simp only [s2, s1, skipNumFinal_pos, hp, zero_add]; exact drop_W I) (bits_lt_of_le hWH hH)
  set s3 := rdNumFinal s2 rW rP rT I.numLocations
  have e3 : s3.env rW = I.numLocations := rdNumFinal_env_r (by decide) (by decide) _
  have r4 := Good.set (x := encodeSystem I) (w := w) (r := rJ) (st := s3) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s4 := s3.set rJ (Ex.eval s3.env (.const 0))
  have r5 := Good.set (x := encodeSystem I) (w := w) (r := rNz) (st := s4) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s5 := s4.set rNz (Ex.eval s4.env (.const 0))
  have hp5 : s5.pos = posAt I 0 := by
    show st.pos + (encodeNat k).length + (encodeNat ℓ).length +
      (encodeNat I.numLocations).length = posAt I 0
    rw [hp, posAt_zero]; ring
  have e5 : ∀ q, s5.env q = Function.update (Function.update s3.env rJ 0) rNz 0 q :=
    fun _ => rfl
  have e5J : s5.env rJ = 0 := by
    rw [e5, Function.update_of_ne (by decide), Function.update_self]
  have hI5 : p0Inv I st s5 := by
    refine ⟨?_, rfl, rfl, by rw [e5J]; omega, Or.inl ⟨?_, ?_,
      fun v hv => absurd hv (by rw [e5J]; omega)⟩⟩
    · rw [e5, Function.update_of_ne (by decide), Function.update_of_ne (by decide), e3]
    · rw [e5, Function.update_self]
    · rw [e5J, hp5]
  -- the loop
  obtain ⟨s6, r6, hI6, hc6⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rW)) (body := p0Body) (p0Inv I st)
    (fun s => I.numLocations - s.env rJ) (fun s => H I - s.pos) (20 * Ex.nodeCost w)
    (50 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hW, -, -, hj, -⟩ := hI
      simp only [Ex.Fits, rv, hW]; omega, fun hc => p0Body_good I hw hH st s hI hc⟩) s5 hI5
  obtain ⟨s7, r7, h7s, h7o, h7t, h7b⟩ := p0End_good I hw hH st s6 hI6 hc6
  refine ⟨s7, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq ((r6.seq r7))))))).mono ?_,
    h7s, h7o, h7t, h7b⟩
  -- the cost
  have hlen : (encodeNat k).length + (encodeNat ℓ).length + (encodeNat I.numLocations).length ≤
      H I := by rw [← posAt_zero]; exact posAt_le I 0
  have hφ : H I - s5.pos + (encodeNat k).length + (encodeNat ℓ).length +
      (encodeNat I.numLocations).length = H I := by rw [hp5, posAt_zero]; omega
  have hμ : I.numLocations - s5.env rJ ≤ H I := by omega
  simp only [condCost, Ex.size, rv] at *
  generalize Ex.nodeCost w = N at *
  generalize unitCost w = U at *
  generalize H I - s5.pos = φ at *
  generalize I.numLocations - s5.env rJ = μ at *
  generalize (encodeNat k).length = lk at *
  generalize (encodeNat ℓ).length = ll at *
  generalize (encodeNat I.numLocations).length = lW at *
  generalize H I = h at *
  nlinarith

end Lax119563Proofs.Compiler

end Compiler_PTriv
