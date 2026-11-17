import Lax119563Proofs.Compiler.CSortLoop
import Lax119563Proofs.Compiler.CSortList

/-!
# Merge sort of records on number stacks

Records are lists of `A` words; a list of records `rs` is stored on a stack as `rs.flatten`
(first record on top, words in order).

* `mvRec`: move the top record of a stack onto another, keeping its word order
  (`mvRec_good`);
* `mvRecsB`: move records one by one while a counter is below a limit and `done < nr`
  (`mvRecsB_good`); the record order is reversed.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

/-- Proves `a ≠ b` for two entries of a duplicate-free list `hreg`. -/
macro "ndup" hreg:ident : tactic =>
  `(tactic| (intro h; subst h; simp at $hreg:ident))

/-! ## Moving one record -/

/-- Move the top `A` words of `src` onto `dst` keeping their order (via `tmp`). -/
def mvRec (src dst tmp : Fin Q) (A i t : Fin R) : CStm R Q :=
  .seq (moveN src tmp A i t) (moveN tmp dst A i t)

lemma mvRec_good {src dst tmp : Fin Q} {A i t : Fin R} (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hsd : src ≠ dst) (hAi : A ≠ i) (hAt : A ≠ t) (hit : i ≠ t) (st : NSt R Q) {a : ℕ}
    (ha : st.env A = a) (hlen : a ≤ (st.stk src).length) (hw : a + 1 < 2 ^ w)
    (hb : ∀ v ∈ (st.stk src).take a, v < 2 ^ w) :
    ∃ st', Good x w (mvRec src dst tmp A i t) st st' (2 * ((a + 1) * (12 * Ex.nodeCost w))) ∧
      st'.stk = Function.update (Function.update st.stk src ((st.stk src).drop a)) dst
        ((st.stk src).take a ++ st.stk dst) ∧ Frame st st' [i, t] := by
  obtain ⟨s1, g1, k1, f1⟩ := moveN_good (x := x) hst hAi hAt hit st ha hlen hw hb
  have ha1 : s1.env A = a := (f1.2.2 A (by simp [hAi, hAt])).trans ha
  have hta : ((st.stk src).take a).length = a := by simp; omega
  have h1t : s1.stk tmp = ((st.stk src).take a).reverse ++ st.stk tmp := by
    rw [k1, movedStk_dst]
  obtain ⟨s2, g2, k2, f2⟩ := moveN_good (x := x) htd hAi hAt hit s1 ha1
    (by rw [h1t]; simp; omega) hw
    (by
      intro v hv
      rw [h1t, List.take_left' (by simpa using hta)] at hv
      exact hb v (List.mem_reverse.mp hv))
  refine ⟨s2, (g1.seq g2).mono (by omega), ?_, f1.trans f2⟩
  rw [k2]
  funext q
  unfold movedStk
  rw [h1t, List.drop_left' (by simpa using hta), List.take_left' (by simpa using hta),
    List.reverse_reverse]
  by_cases hqd : q = dst
  · subst hqd; simp [k1, movedStk_other _ hsd.symm htd.symm]
  · by_cases hqt : q = tmp
    · subst hqt; simp [Function.update_of_ne hqd, Function.update_of_ne hst.symm]
    · by_cases hqs : q = src
      · subst hqs; simp [Function.update_of_ne hqd, Function.update_of_ne hqt, k1,
          movedStk_src _ hst]
      · simp [Function.update_of_ne hqd, Function.update_of_ne hqt, Function.update_of_ne hqs,
          k1, movedStk_other _ hqs hqt]

/-! ## Moving several records -/

/-- Move records from `src` to `dst` while `k < lim` and `done < nr` (counting both). -/
def mvRecsB (src dst tmp : Fin Q) (A lim done nr k i t : Fin R) : CStm R Q :=
  .seq (.set k (.const 0))
    (.loop (.lt (.const 1) (.add (.lt (rv k) (rv lim)) (.lt (rv done) (rv nr))))
      (.seq (mvRec src dst tmp A i t)
        (.seq (.set k (.add (rv k) (.const 1))) (.set done (.add (rv done) (.const 1))))))

/-- The stacks after moving the first `j` records of `l`. -/
def recsStk (S : Fin Q → List ℕ) (src dst : Fin Q) (l : List (List ℕ)) (L : List ℕ) (j : ℕ) :
    Fin Q → List ℕ :=
  Function.update (Function.update S src ((l.drop j).flatten ++ L)) dst
    ((l.take j).reverse.flatten ++ S dst)

lemma flatten_drop_eq {l : List (List ℕ)} {j : ℕ} (hj : j < l.length) :
    (l.drop j).flatten = l[j] ++ (l.drop (j + 1)).flatten := by
  rw [List.drop_eq_getElem_cons hj, List.flatten_cons]

lemma recsStk_step (S : Fin Q → List ℕ) {src dst : Fin Q} (hsd : src ≠ dst)
    (l : List (List ℕ)) (L : List ℕ) {j : ℕ} (hj : j < l.length) :
    Function.update (Function.update (recsStk S src dst l L j) src
      ((l.drop (j + 1)).flatten ++ L)) dst (l[j] ++ recsStk S src dst l L j dst) =
      recsStk S src dst l L (j + 1) := by
  funext q
  unfold recsStk
  by_cases hqd : q = dst
  · subst hqd
    simp only [Function.update_self]
    have ht : l.take (j + 1) = l.take j ++ [l[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    rw [ht, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.flatten_cons, List.append_assoc]
  · by_cases hqs : q = src
    · subst hqs; simp [Function.update_of_ne hqd]
    · simp [Function.update_of_ne hqd, Function.update_of_ne hqs]

lemma two_le_pow {w : ℕ} (hw : 2 ≤ w) : 4 ≤ 2 ^ w :=
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw

lemma mvRecsB_good (hw2 : 2 ≤ w) {src dst tmp : Fin Q} {A lim done nr k i t : Fin R}
    (hst : src ≠ tmp) (htd : tmp ≠ dst) (hsd : src ≠ dst)
    (hreg : [A, lim, done, nr, k, i, t].Nodup) (st : NSt R Q) (l : List (List ℕ))
    (L : List ℕ) {a rl n d0 : ℕ} (ha : st.env A = a) (hl : st.env lim = rl)
    (hn : st.env nr = n) (hd : st.env done = d0) (hd0 : d0 ≤ n)
    (hS : st.stk src = l.flatten ++ L) (hrec : ∀ y ∈ l, y.length = a ∧ ∀ v ∈ y, v < 2 ^ w)
    (hm : min rl (n - d0) ≤ l.length) (hw : a + 1 < 2 ^ w) (hwl : rl + 1 < 2 ^ w)
    (hwn : n + 1 < 2 ^ w) :
    ∃ st', Good x w (mvRecsB src dst tmp A lim done nr k i t) st st'
        ((min rl (n - d0) + 1) * (50 * ((a + 1) * Ex.nodeCost w))) ∧
      st'.stk = recsStk st.stk src dst l L (min rl (n - d0)) ∧
      st'.env done = d0 + min rl (n - d0) ∧ Frame st st' [k, done, i, t] := by
  have hAi : A ≠ i := by ndup hreg
  have hAt : A ≠ t := by ndup hreg
  have hit : i ≠ t := by ndup hreg
  have hkd : k ≠ done := by ndup hreg
  have hkl : k ≠ lim := by ndup hreg
  have hkn : k ≠ nr := by ndup hreg
  have hkA : k ≠ A := by ndup hreg
  have hdl : done ≠ lim := by ndup hreg
  have hdn : done ≠ nr := by ndup hreg
  have hdA : done ≠ A := by ndup hreg
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 := two_le_pow hw2
  set m := min rl (n - d0) with hmdef
  set Inv : NSt R Q → Prop := fun s => ∃ j ≤ m, s.env k = j ∧ s.env done = d0 + j ∧
    s.env lim = rl ∧ s.env nr = n ∧ s.env A = a ∧ s.stk = recsStk st.stk src dst l L j ∧
    Frame st s [k, done, i, t]
  set e : Ex R := .lt (.const 1) (.add (.lt (rv k) (rv lim)) (.lt (rv done) (rv nr)))
  have hev : ∀ s, Inv s → (e.eval s.env ≠ 0 ↔ s.env k < m) := by
    rintro s ⟨j, hj, hk, hdn', hl', hn', -⟩
    simp only [e, rv, Ex.eval, hk, hdn', hl', hn']
    constructor
    · intro h; split_ifs at h with h1 h2 h3 <;> omega
    · intro h; have h1 : j < rl := by omega
      have h2 : d0 + j < n := by omega
      simp [h1, h2]
  have hloop := Good.loop_var (x := x) (w := w) (e := e)
    (body := .seq (mvRec src dst tmp A i t)
        (.seq (.set k (.add (rv k) (.const 1))) (.set done (.add (rv done) (.const 1)))))
    Inv (fun s => m - s.env k) (fun _ => 0) 0 (32 * ((a + 1) * Ex.nodeCost w)) (by
      intro s hI
      obtain ⟨j, hj, hk, hdn', hl', hn', hA', hs, hf⟩ := hI
      refine ⟨?_, ?_⟩
      · simp only [e, rv, Ex.Fits, Ex.eval, hk, hdn', hl', hn']
        refine ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
        split_ifs <;> omega
      intro hc
      have hjm : j < m := by rw [← hk]; exact (hev s ⟨j, hj, hk, hdn', hl', hn', hA', hs, hf⟩).mp hc
      have hjl : j < l.length := by omega
      have hrj := hrec _ (List.getElem_mem hjl)
      have hsrc : s.stk src = l[j] ++ ((l.drop (j + 1)).flatten ++ L) := by
        rw [hs]; simp [recsStk, Function.update_of_ne hsd, flatten_drop_eq hjl]
      obtain ⟨s1, g1, k1, f1⟩ := mvRec_good (x := x) hst htd hsd hAi hAt hit s hA'
        (by rw [hsrc]; simp; omega) hw
        (by rw [hsrc, List.take_left' hrj.1]; exact hrj.2)
      have e1 : ∀ r, r ≠ i → r ≠ t → s1.env r = s.env r := fun r h1 h2 =>
        f1.2.2 r (by simp [h1, h2])
      have hk1 : s1.env k = j := by rw [e1 k (by ndup hreg) (by ndup hreg), hk]
      have hd1 : s1.env done = d0 + j := by rw [e1 done (by ndup hreg) (by ndup hreg), hdn']
      have g2 : Good x w (.set k (.add (rv k) (.const 1)) : CStm R Q) s1 (s1.set k (j + 1))
          (3 * Ex.nodeCost w + unitCost w) :=
        (Good.set (by simp only [rv, Ex.Fits, Ex.eval, hk1]; omega)).of_eq
          (by simp [rv, Ex.eval, hk1]) (by simp [Ex.size])
      have g3 : Good x w (.set done (.add (rv done) (.const 1)) : CStm R Q) (s1.set k (j + 1))
          ((s1.set k (j + 1)).set done (d0 + j + 1)) (3 * Ex.nodeCost w + unitCost w) :=
        (Good.set (by simp only [rv, Ex.Fits, Ex.eval, NSt.set_env,
            Function.update_of_ne hkd.symm, hd1]; omega)).of_eq
          (by simp [rv, Ex.eval, Function.update_of_ne hkd.symm, hd1]) (by simp [Ex.size])
      refine ⟨_, (g1.seq (g2.seq g3)).mono (by nlinarith), ⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_⟩, ?_, le_rfl⟩
      · simp [Function.update_of_ne hkd]
      · simp; omega
      · simp only [NSt.set_env, Function.update_of_ne hdl.symm, Function.update_of_ne hkl.symm]
        rw [e1 lim (by ndup hreg) (by ndup hreg), hl']
      · simp only [NSt.set_env, Function.update_of_ne hdn.symm, Function.update_of_ne hkn.symm]
        rw [e1 nr (by ndup hreg) (by ndup hreg), hn']
      · simp only [NSt.set_env, Function.update_of_ne hdA.symm, Function.update_of_ne hkA.symm]
        rw [e1 A hAi hAt, hA']
      · simp only [NSt.set_stk]
        rw [k1, hsrc, List.drop_left' hrj.1, List.take_left' hrj.1, hs]
        have := recsStk_step st.stk hsd l L hjl
        rw [hs] at hsrc
        convert this using 3
      · refine ⟨?_, ?_, fun r hr => ?_⟩
        · simp [f1.1, hf.1]
        · simp [f1.2.1, hf.2.1]
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [NSt.set_env, Function.update_of_ne hr.2.1, Function.update_of_ne hr.1]
          rw [e1 r hr.2.2.1 hr.2.2.2]
          exact hf.2.2 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])
      · simp [Function.update_of_ne hkd]; omega)
  have g0 : Good x w (.set k (.const 0) : CStm R Q) st (st.set k 0)
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; omega)).of_eq (by simp [Ex.eval]) (by simp [Ex.size])
  obtain ⟨s', g', ⟨j, hj, hk, hdn', hl', hn', hA', hs, hf⟩, hend⟩ := hloop (st.set k 0)
    ⟨0, Nat.zero_le _, by simp, by simp [Function.update_of_ne hkd.symm, hd],
      by simp [Function.update_of_ne hkl.symm, hl], by simp [Function.update_of_ne hkn.symm, hn],
      by simp [Function.update_of_ne hkA.symm, ha],
      by
        funext q; unfold recsStk
        by_cases hqd : q = dst
        · subst hqd; simp
        · by_cases hqs : q = src
          · subst hqs; simp [Function.update_of_ne hqd, hS]
          · simp [Function.update_of_ne hqd, Function.update_of_ne hqs],
      ⟨rfl, rfl, fun r hr => by
        simp only [List.mem_cons, not_or] at hr; simp [Function.update_of_ne hr.1]⟩⟩
  have hjm : j = m := by
    have := (hev s' ⟨j, hj, hk, hdn', hl', hn', hA', hs, hf⟩)
    by_contra hne
    exact (this.mpr (by omega)) hend
  subst hjm
  refine ⟨s', (g0.seq g').mono ?_, hs, hdn', hf⟩
  simp only [condCost, e, rv, Ex.size, NSt.set_env, Function.update_self, Nat.sub_zero,
    mul_zero, zero_add]
  have hP : Ex.nodeCost w ≤ (a + 1) * Ex.nodeCost w := Nat.le_mul_of_pos_left _ (by omega)
  have h1 : m * Ex.nodeCost w ≤ m * ((a + 1) * Ex.nodeCost w) := Nat.mul_le_mul_left _ hP
  have h2 : m ≤ m * Ex.nodeCost w := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

end CStm

end Lax119563Proofs.Compiler
