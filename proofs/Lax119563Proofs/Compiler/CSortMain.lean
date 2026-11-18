import Lax119563Proofs.Compiler.CSort

/-!
# Merge sort of records on number stacks: merging, passes, the sort

* `mrgS_good`: the merge loop computes `CSort.mrg`.
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

lemma update_self_eq {S : Fin Q → List ℕ} {q : Fin Q} {l : List ℕ} (h : S q = l) :
    Function.update S q l = S := by
  subst h; exact Function.update_eq_self _ _

section Pass

variable {X T1 T2 Y tmp C1 C2 : Fin Q} {A dir c f1 f2 kc t1 t2 i t r N done k : Fin R}

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

end Pass

end CStm

end Lax119563Proofs.Compiler
