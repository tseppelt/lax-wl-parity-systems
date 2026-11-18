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

end CStm

end Lax119563Proofs.Compiler
