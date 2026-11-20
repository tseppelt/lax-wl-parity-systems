import Lax119563Proofs.Compiler.CSort

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
