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

/-! ## Comparing the top records of two stacks -/

lemma NSt.set_self' (s : NSt R Q) (r : Fin R) : s.set r (s.env r) = s := by
  cases s; simp [NSt.set]

/-- One step of the word-by-word comparison: `d := cmpStep d t1 t2`. -/
def cmpIte (d t1 t2 : Fin R) : CStm R Q :=
  .ite (rv d) .skip (.ite (.lt (rv t1) (rv t2)) (.set d (.const 1))
    (.ite (.lt (rv t2) (rv t1)) (.set d (.const 2)) .skip))

lemma cmpIte_good (hw2 : 2 ≤ w) {d t1 t2 : Fin R} (s : NSt R Q) (hd : s.env d < 2 ^ w)
    (h1 : s.env t1 < 2 ^ w) (h2 : s.env t2 < 2 ^ w) :
    Good x w (cmpIte d t1 t2 : CStm R Q) s
      (s.set d (CSort.cmpStep (s.env d) (s.env t1) (s.env t2))) (20 * Ex.nodeCost w) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 := two_le_pow hw2
  by_cases hd0 : s.env d = 0
  · have hfd : (rv d : Ex R).Fits w s.env := hd
    by_cases hab : s.env t1 < s.env t2
    · refine (Good.iteF hfd (by simp [rv, Ex.eval, hd0]) (Good.iteT (e := .lt (rv t1) (rv t2)) (show (Ex.lt (rv t1) (rv t2) : Ex R).Fits w s.env from ⟨h1, h2⟩)
        (by simp [rv, Ex.eval, hab]) (Good.set (r := d) (e := .const 1)
          (by simp only [Ex.Fits]; omega)))).of_eq (by simp [CSort.cmpStep, hd0, hab, Ex.eval])
        (by simp only [condCost, rv, Ex.size]; omega)
    · by_cases hba : s.env t2 < s.env t1
      · refine (Good.iteF hfd (by simp [rv, Ex.eval, hd0]) (Good.iteF (e := .lt (rv t1) (rv t2)) (show (Ex.lt (rv t1) (rv t2) : Ex R).Fits w s.env from ⟨h1, h2⟩)
          (by simp [rv, Ex.eval, hab]) (Good.iteT (e := .lt (rv t2) (rv t1)) (show (Ex.lt (rv t2) (rv t1) : Ex R).Fits w s.env from ⟨h2, h1⟩) (by simp [rv, Ex.eval, hba])
            (Good.set (r := d) (e := .const 2) (by simp only [Ex.Fits]; omega))))).of_eq
          (by simp [CSort.cmpStep, hd0, hab, hba, Ex.eval])
          (by simp only [condCost, rv, Ex.size]; omega)
      · refine (Good.iteF hfd (by simp [rv, Ex.eval, hd0]) (Good.iteF (e := .lt (rv t1) (rv t2)) (show (Ex.lt (rv t1) (rv t2) : Ex R).Fits w s.env from ⟨h1, h2⟩)
          (by simp [rv, Ex.eval, hab]) (Good.iteF (e := .lt (rv t2) (rv t1)) (show (Ex.lt (rv t2) (rv t1) : Ex R).Fits w s.env from ⟨h2, h1⟩) (by simp [rv, Ex.eval, hba])
            Good.skip))).of_eq
          (by
            have : CSort.cmpStep (s.env d) (s.env t1) (s.env t2) = s.env d := by
              simp [CSort.cmpStep, hd0, hab, hba]
            rw [this, NSt.set_self'])
          (by simp only [condCost, rv, Ex.size]; omega)
  · refine (Good.iteT (e := rv d) hd (by simpa [rv, Ex.eval] using hd0) Good.skip).of_eq ?_
      (by simp only [condCost, rv, Ex.size]; omega)
    have : CSort.cmpStep (s.env d) (s.env t1) (s.env t2) = s.env d := by
      simp [CSort.cmpStep, hd0]
    rw [this, NSt.set_self']

lemma cmpW_le : ∀ (d : ℕ) (as bs : List ℕ), d ≤ 2 → CSort.cmpW d as bs ≤ 2
  | d, a :: as, b :: bs, h => by
    simp only [CSort.cmpW]
    exact cmpW_le _ as bs (by unfold CSort.cmpStep; split_ifs <;> omega)
  | _, [], _, h => h
  | _, _ :: _, [], h => h

/-- The body of the comparison loop. -/
def cmpBody (s1 s2 c1 c2 : Fin Q) (d kc t1 t2 : Fin R) : CStm R Q :=
  .seq (.pop s1 t1) (.seq (.pop s2 t2) (.seq (.push c1 (rv t1)) (.seq (.push c2 (rv t2))
    (.seq (cmpIte d t1 t2) (.set kc (.add (rv kc) (.const 1)))))))

/-- Compare the top records (of `A` words) of `s1` and `s2`: `d := cmpW 0 a₁ a₂`; both stacks
are restored (via `c1`, `c2`). -/
def cmpS (s1 s2 c1 c2 : Fin Q) (A d kc t1 t2 i t : Fin R) : CStm R Q :=
  .seq (.set d (.const 0)) (.seq (.set kc (.const 0))
    (.seq (.loop (.lt (rv kc) (rv A)) (cmpBody s1 s2 c1 c2 d kc t1 t2))
      (.seq (moveN c1 s1 A i t) (moveN c2 s2 A i t))))

/-- The stacks of the comparison after `j` words. -/
def cmpStk (S : Fin Q → List ℕ) (s1 s2 c1 c2 : Fin Q) (a1 a2 L1 L2 : List ℕ) (j : ℕ) :
    Fin Q → List ℕ :=
  Function.update (Function.update (Function.update (Function.update S s1 (a1.drop j ++ L1))
    s2 (a2.drop j ++ L2)) c1 ((a1.take j).reverse ++ S c1)) c2 ((a2.take j).reverse ++ S c2)

lemma take_succ_rev {l : List ℕ} {j : ℕ} (hj : j < l.length) :
    (l.take (j + 1)).reverse = l[j] :: (l.take j).reverse := by
  have ht : l.take (j + 1) = l.take j ++ [l[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  rw [ht, List.reverse_append, List.reverse_singleton, List.singleton_append]

section CmpStk

variable {S : Fin Q → List ℕ} {s1 s2 c1 c2 : Fin Q} {a1 a2 L1 L2 : List ℕ} {j : ℕ}

lemma cmpStk_c2 : cmpStk S s1 s2 c1 c2 a1 a2 L1 L2 j c2 = (a2.take j).reverse ++ S c2 := by
  simp [cmpStk]

lemma cmpStk_c1 (h : c1 ≠ c2) :
    cmpStk S s1 s2 c1 c2 a1 a2 L1 L2 j c1 = (a1.take j).reverse ++ S c1 := by
  simp [cmpStk, Function.update_of_ne h]

lemma cmpStk_s2 (h1 : s2 ≠ c1) (h2 : s2 ≠ c2) :
    cmpStk S s1 s2 c1 c2 a1 a2 L1 L2 j s2 = a2.drop j ++ L2 := by
  simp [cmpStk, Function.update_of_ne h1, Function.update_of_ne h2]

lemma cmpStk_s1 (h0 : s1 ≠ s2) (h1 : s1 ≠ c1) (h2 : s1 ≠ c2) :
    cmpStk S s1 s2 c1 c2 a1 a2 L1 L2 j s1 = a1.drop j ++ L1 := by
  simp [cmpStk, Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2]

lemma cmpStk_other {q : Fin Q} (h0 : q ≠ s1) (h1 : q ≠ s2) (h2 : q ≠ c1) (h3 : q ≠ c2) :
    cmpStk S s1 s2 c1 c2 a1 a2 L1 L2 j q = S q := by
  simp [cmpStk, Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3]

end CmpStk

lemma cmpS_good (hw2 : 2 ≤ w) {s1 s2 c1 c2 : Fin Q} {A d kc t1 t2 i t : Fin R}
    (hstk : [s1, s2, c1, c2].Nodup) (hreg : [A, d, kc, t1, t2, i, t].Nodup)
    (st : NSt R Q) {a : ℕ} (a1 a2 L1 L2 : List ℕ) (ha : st.env A = a)
    (h1 : st.stk s1 = a1 ++ L1) (h2 : st.stk s2 = a2 ++ L2) (hl1 : a1.length = a)
    (hl2 : a2.length = a) (hb1 : ∀ v ∈ a1, v < 2 ^ w) (hb2 : ∀ v ∈ a2, v < 2 ^ w)
    (hw : a + 1 < 2 ^ w) :
    ∃ st', Good x w (cmpS s1 s2 c1 c2 A d kc t1 t2 i t) st st'
        ((a + 1) * (80 * Ex.nodeCost w)) ∧
      st'.stk = st.stk ∧ st'.env d = CSort.cmpW 0 a1 a2 ∧ Frame st st' [d, kc, t1, t2, i, t] := by
  have hs12 : s1 ≠ s2 := by ndup hstk
  have hs1c1 : s1 ≠ c1 := by ndup hstk
  have hs1c2 : s1 ≠ c2 := by ndup hstk
  have hs2c1 : s2 ≠ c1 := by ndup hstk
  have hs2c2 : s2 ≠ c2 := by ndup hstk
  have hc12 : c1 ≠ c2 := by ndup hstk
  have hAd : A ≠ d := by ndup hreg
  have hAk : A ≠ kc := by ndup hreg
  have hAi : A ≠ i := by ndup hreg
  have hAt : A ≠ t := by ndup hreg
  have hit : i ≠ t := by ndup hreg
  have hdk : d ≠ kc := by ndup hreg
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 := two_le_pow hw2
  set Inv : NSt R Q → Prop := fun s => ∃ j ≤ a, s.env kc = j ∧ s.env A = a ∧
    s.env d = CSort.cmpW 0 (a1.take j) (a2.take j) ∧ s.stk = cmpStk st.stk s1 s2 c1 c2 a1 a2 L1 L2 j ∧
    Frame st s [d, kc, t1, t2, i, t]
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv kc) (rv A))
    (body := cmpBody s1 s2 c1 c2 d kc t1 t2)
    Inv (fun s => a - s.env kc) (fun _ => 0) 0 (40 * Ex.nodeCost w) (by
      intro s hI
      obtain ⟨j, hj, hk, hA', hd', hs, hf⟩ := hI
      refine ⟨⟨by simp only [rv, Ex.Fits, hk]; omega, by simp only [rv, Ex.Fits, hA']; omega⟩, ?_⟩
      intro hc
      have hja : j < a := by
        simp only [rv, Ex.eval, hk, hA'] at hc; split_ifs at hc with h <;> omega
      have hj1 : j < a1.length := by omega
      have hj2 : j < a2.length := by omega
      have hs1 : s.stk s1 = a1[j] :: (a1.drop (j + 1) ++ L1) := by
        rw [hs, cmpStk_s1 hs12 hs1c1 hs1c2, List.drop_eq_getElem_cons hj1, List.cons_append]
      have hs2 : s.stk s2 = a2[j] :: (a2.drop (j + 1) ++ L2) := by
        rw [hs, cmpStk_s2 hs2c1 hs2c2, List.drop_eq_getElem_cons hj2, List.cons_append]
      have hv1 : a1[j] < 2 ^ w := hb1 _ (List.getElem_mem _)
      have hv2 : a2[j] < 2 ^ w := hb2 _ (List.getElem_mem _)
      have hdle : s.env d ≤ 2 := by rw [hd']; exact cmpW_le 0 _ _ (by omega)
      -- the states of the body
      set u1 := (s.setS s1 (a1.drop (j + 1) ++ L1)).set t1 a1[j]
      set u2 := (u1.setS s2 (a2.drop (j + 1) ++ L2)).set t2 a2[j]
      set u3 := u2.setS c1 (a1[j] :: u2.stk c1)
      set u4 := u3.setS c2 (a2[j] :: u3.stk c2)
      have ht1 : u4.env t1 = a1[j] := by
        simp [u4, u3, u2, u1, Function.update_of_ne (show t1 ≠ t2 by ndup hreg)]
      have ht2 : u4.env t2 = a2[j] := by simp [u4, u3, u2]
      have hd4 : u4.env d = s.env d := by
        simp [u4, u3, u2, u1, Function.update_of_ne (show d ≠ t2 by ndup hreg),
          Function.update_of_ne (show d ≠ t1 by ndup hreg)]
      have hk4 : u4.env kc = j := by
        simp [u4, u3, u2, u1, Function.update_of_ne (show kc ≠ t2 by ndup hreg),
          Function.update_of_ne (show kc ≠ t1 by ndup hreg), hk]
      set u5 := u4.set d (CSort.cmpStep (u4.env d) (u4.env t1) (u4.env t2))
      have gp1 : Good x w (.pop s1 t1 : CStm R Q) s u1 (unitCost w + 1) :=
        (Good.pop s1 t1).of_eq (by simp [u1, hs1]) le_rfl
      have gp2 : Good x w (.pop s2 t2 : CStm R Q) u1 u2 (unitCost w + 1) :=
        (Good.pop s2 t2).of_eq (by simp [u2, u1, Function.update_of_ne hs12.symm, hs2]) le_rfl
      have gq1 : Good x w (.push c1 (rv t1) : CStm R Q) u2 u3 (Ex.nodeCost w + unitCost w) :=
        (Good.push (by
          simp only [rv, Ex.Fits, u2, u1, NSt.set_env, NSt.setS_env,
            Function.update_of_ne (show t1 ≠ t2 by ndup hreg), Function.update_self]
          exact hv1)).of_eq
          (by simp [u3, u2, u1, rv, Ex.eval, Function.update_of_ne (show t1 ≠ t2 by ndup hreg)])
          (by simp [rv, Ex.size])
      have gq2 : Good x w (.push c2 (rv t2) : CStm R Q) u3 u4 (Ex.nodeCost w + unitCost w) :=
        (Good.push (by simp only [rv, Ex.Fits, u3, u2, NSt.set_env, NSt.setS_env,
          Function.update_self]; exact hv2)).of_eq
          (by simp [u4, u3, u2, rv, Ex.eval]) (by simp [rv, Ex.size])
      have gi : Good x w (cmpIte d t1 t2 : CStm R Q) u4 u5 (20 * Ex.nodeCost w) :=
        cmpIte_good hw2 u4 (by rw [hd4]; omega) (by rw [ht1]; exact hv1) (by rw [ht2]; exact hv2)
      have hk5 : u5.env kc = j := by
        simp only [u5, NSt.set_env, Function.update_of_ne hdk.symm]; exact hk4
      have gk : Good x w (.set kc (.add (rv kc) (.const 1)) : CStm R Q) u5 (u5.set kc (j + 1))
          (3 * Ex.nodeCost w + unitCost w) :=
        (Good.set (by simp only [rv, Ex.Fits, Ex.eval, hk5]; omega)).of_eq
          (by simp [rv, Ex.eval, hk5]) (by simp [Ex.size])
      refine ⟨_, (gp1.seq (gp2.seq (gq1.seq (gq2.seq (gi.seq gk))))).mono (by omega),
        ⟨j + 1, by omega, by simp, ?_, ?_, ?_, ?_⟩, ?_, le_rfl⟩
      · simp only [NSt.set_env, Function.update_of_ne hAk, u5, Function.update_of_ne hAd, u4,
          u3, u2, u1, NSt.setS_env, Function.update_of_ne (show A ≠ t2 by ndup hreg),
          Function.update_of_ne (show A ≠ t1 by ndup hreg)]
        exact hA'
      · simp only [NSt.set_env, Function.update_of_ne hdk, u5, Function.update_self]
        rw [hd4, ht1, ht2, hd', CSort.cmpW_take_succ 0 a1 a2 j hj1 hj2]
      · simp only [u5, u4, u3, u2, u1, NSt.set_stk, NSt.setS_stk]
        funext q
        by_cases hq2 : q = c2
        · subst hq2
          simp [Function.update_of_ne hs1c2.symm, Function.update_of_ne hs2c2.symm,
            Function.update_of_ne hc12.symm, hs, cmpStk_c2, take_succ_rev hj2]
        · by_cases hq1 : q = c1
          · subst hq1
            simp [Function.update_of_ne hs1c1.symm, Function.update_of_ne hs2c1.symm,
              Function.update_of_ne hc12, hs, cmpStk_c1 hc12, take_succ_rev hj1]
          · by_cases hqs2 : q = s2
            · subst hqs2
              simp [Function.update_of_ne hs2c1, Function.update_of_ne hs2c2,
                cmpStk_s2 hs2c1 hs2c2]
            · by_cases hqs1 : q = s1
              · subst hqs1
                simp [Function.update_of_ne hs1c1, Function.update_of_ne hs1c2,
                  Function.update_of_ne hs12, cmpStk_s1 hs12 hs1c1 hs1c2]
              · simp [Function.update_of_ne hq1, Function.update_of_ne hq2,
                  Function.update_of_ne hqs1, Function.update_of_ne hqs2, hs,
                  cmpStk_other hqs1 hqs2 hq1 hq2]
      · refine ⟨by simp [u5, u4, u3, u2, u1, hf.1], by simp [u5, u4, u3, u2, u1, hf.2.1],
          fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [u5, u4, u3, u2, u1, NSt.set_env, NSt.setS_env, Function.update_of_ne hr.1,
          Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2.1,
          Function.update_of_ne hr.2.2.2.1]
        exact hf.2.2 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
          hr.2.2.2.2.2])
      · simp; omega)
  -- the initialization
  have g0 : Good x w (.set d (.const 0) : CStm R Q) st (st.set d 0)
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; omega)).of_eq (by simp [Ex.eval]) (by simp [Ex.size])
  have g1 : Good x w (.set kc (.const 0) : CStm R Q) (st.set d 0) ((st.set d 0).set kc 0)
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; omega)).of_eq (by simp [Ex.eval]) (by simp [Ex.size])
  have hC0 : cmpStk st.stk s1 s2 c1 c2 a1 a2 L1 L2 0 = st.stk := by
    funext q
    by_cases hq2 : q = c2
    · subst hq2; simp [cmpStk_c2]
    · by_cases hq1 : q = c1
      · subst hq1; simp [cmpStk_c1 hc12]
      · by_cases hqs2 : q = s2
        · subst hqs2; simp [cmpStk_s2 hs2c1 hs2c2, h2]
        · by_cases hqs1 : q = s1
          · subst hqs1; simp [cmpStk_s1 hs12 hs1c1 hs1c2, h1]
          · simp [cmpStk_other hqs1 hqs2 hq1 hq2]
  obtain ⟨s', g', ⟨j, hj, hk, hA', hd', hs, hf⟩, hend⟩ := hloop ((st.set d 0).set kc 0)
    ⟨0, Nat.zero_le _, by simp, by simp [Function.update_of_ne hAk, Function.update_of_ne hAd, ha],
      by simp [Function.update_of_ne hdk, CSort.cmpW], by simp [hC0],
      ⟨rfl, rfl, fun r hr => by
        simp only [List.mem_cons, not_or] at hr
        simp [Function.update_of_ne hr.1, Function.update_of_ne hr.2.1]⟩⟩
  have hja : j = a := by
    simp only [rv, Ex.eval, hk, hA'] at hend; split_ifs at hend with h <;> omega
  subst hja
  -- restore the stacks
  have hsc1 : s'.stk c1 = a1.reverse ++ st.stk c1 := by
    rw [hs, cmpStk_c1 hc12, List.take_of_length_le (by omega)]
  obtain ⟨m1, gm1, km1, fm1⟩ := moveN_good (x := x) hs1c1.symm hAi hAt hit s' hA'
    (by rw [hsc1]; simp; omega) hw
    (by
      intro v hv
      rw [hsc1, List.take_left' (by simpa using hl1)] at hv
      exact hb1 v (List.mem_reverse.mp hv))
  have hAm : m1.env A = j := (fm1.2.2 A (by simp [hAi, hAt])).trans hA'
  have hsc2 : m1.stk c2 = a2.reverse ++ st.stk c2 := by
    rw [km1, movedStk_other _ hc12.symm hs1c2.symm, hs, cmpStk_c2,
      List.take_of_length_le (by omega)]
  obtain ⟨m2, gm2, km2, fm2⟩ := moveN_good (x := x) hs2c2.symm hAi hAt hit m1 hAm
    (by rw [hsc2]; simp; omega) hw
    (by
      intro v hv
      rw [hsc2, List.take_left' (by simpa using hl2)] at hv
      exact hb2 v (List.mem_reverse.mp hv))
  refine ⟨m2, (g0.seq (g1.seq (g'.seq (gm1.seq gm2)))).mono ?_, ?_, ?_,
    hf.trans ((fm1.trans fm2).mono (by intro r hr; simp at hr ⊢; tauto))⟩
  · simp only [condCost, rv, Ex.size, NSt.set_env, Function.update_self, Nat.sub_zero,
      mul_zero, zero_add]
    have h2 : j ≤ j * Ex.nodeCost w := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  · funext q
    rw [km2]
    by_cases hq2 : q = c2
    · subst hq2
      rw [movedStk_src _ hs2c2.symm, hsc2, List.drop_left' (by simpa using hl2)]
    · by_cases hqs2 : q = s2
      · subst hqs2
        rw [movedStk_dst, hsc2, List.take_left' (by simpa using hl2), List.reverse_reverse,
          km1, movedStk_other _ hs2c1 hs12.symm, hs, cmpStk_s2 hs2c1 hs2c2,
          List.drop_of_length_le (by omega), List.nil_append, h2]
      · rw [movedStk_other _ hq2 hqs2, km1]
        by_cases hq1 : q = c1
        · subst hq1
          rw [movedStk_src _ hs1c1.symm, hs, cmpStk_c1 hc12, List.take_of_length_le (by omega),
            List.drop_left' (by simpa using hl1)]
        · by_cases hqs1 : q = s1
          · subst hqs1
            rw [movedStk_dst, hs, cmpStk_c1 hc12, cmpStk_s1 hs12 hs1c1 hs1c2,
              List.take_of_length_le (l := a1) (by omega), List.take_left' (by simpa using hl1),
              List.reverse_reverse, List.drop_of_length_le (l := a1) (by omega), List.nil_append, h1]
          · rw [movedStk_other _ hq1 hqs1, hs, cmpStk_other hqs1 hqs2 hq1 hq2]
  · rw [fm2.2.2 d (by simp [show d ≠ i by ndup hreg, show d ≠ t by ndup hreg]),
      fm1.2.2 d (by simp [show d ≠ i by ndup hreg, show d ≠ t by ndup hreg]), hd',
      List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-! ## Merging two runs -/

/-- The stacks during a merge: `u`, `v` on `T1`, `T2`, the merged records `acc` on top of
`Y`. -/
def mrgStk (S : Fin Q → List ℕ) (T1 T2 Y : Fin Q) (u v acc : List (List ℕ)) : Fin Q → List ℕ :=
  Function.update (Function.update (Function.update S T1 u.flatten) T2 v.flatten) Y
    (acc.flatten ++ S Y)

section MrgStk

variable {S : Fin Q → List ℕ} {T1 T2 Y : Fin Q} {u v acc : List (List ℕ)}

lemma mrgStk_Y : mrgStk S T1 T2 Y u v acc Y = acc.flatten ++ S Y := by simp [mrgStk]

lemma mrgStk_T2 (h : T2 ≠ Y) : mrgStk S T1 T2 Y u v acc T2 = v.flatten := by
  simp [mrgStk, Function.update_of_ne h]

lemma mrgStk_T1 (h0 : T1 ≠ T2) (h1 : T1 ≠ Y) : mrgStk S T1 T2 Y u v acc T1 = u.flatten := by
  simp [mrgStk, Function.update_of_ne h0, Function.update_of_ne h1]

lemma mrgStk_other {q : Fin Q} (h0 : q ≠ T1) (h1 : q ≠ T2) (h2 : q ≠ Y) :
    mrgStk S T1 T2 Y u v acc q = S q := by
  simp [mrgStk, Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2]

lemma mrgStk_mv1 (h0 : T1 ≠ T2) (h1 : T1 ≠ Y) (h2 : T2 ≠ Y) {a0 : List ℕ}
    {u' : List (List ℕ)} :
    Function.update (Function.update (mrgStk S T1 T2 Y (a0 :: u') v acc) T1 u'.flatten) Y
      (a0 ++ mrgStk S T1 T2 Y (a0 :: u') v acc Y) = mrgStk S T1 T2 Y u' v (a0 :: acc) := by
  funext q
  by_cases hY : q = Y
  · subst hY; simp [mrgStk_Y]
  · by_cases hq1 : q = T1
    · subst hq1; simp [Function.update_of_ne hY, mrgStk_T1 h0 h1]
    · by_cases hq2 : q = T2
      · subst hq2; simp [Function.update_of_ne hY, Function.update_of_ne hq1, mrgStk_T2 h2]
      · simp [Function.update_of_ne hY, Function.update_of_ne hq1, mrgStk_other hq1 hq2 hY]

lemma mrgStk_mv2 (h0 : T1 ≠ T2) (h1 : T1 ≠ Y) (h2 : T2 ≠ Y) {b0 : List ℕ}
    {v' : List (List ℕ)} :
    Function.update (Function.update (mrgStk S T1 T2 Y u (b0 :: v') acc) T2 v'.flatten) Y
      (b0 ++ mrgStk S T1 T2 Y u (b0 :: v') acc Y) = mrgStk S T1 T2 Y u v' (b0 :: acc) := by
  funext q
  by_cases hY : q = Y
  · subst hY; simp [mrgStk_Y]
  · by_cases hq2 : q = T2
    · subst hq2; simp [Function.update_of_ne hY, mrgStk_T2 h2]
    · by_cases hq1 : q = T1
      · subst hq1; simp [Function.update_of_ne hY, Function.update_of_ne hq2, mrgStk_T1 h0 h1]
      · simp [Function.update_of_ne hY, Function.update_of_ne hq2, mrgStk_other hq1 hq2 hY]

end MrgStk

/-- Flags: `1` for a nonempty list. -/
def nef {α : Type} (l : List α) : ℕ := if l = [] then 0 else 1

lemma flatten_eq_nil_iff {l : List (List ℕ)} {a : ℕ} (ha : 1 ≤ a)
    (h : ∀ y ∈ l, y.length = a) : l.flatten = [] ↔ l = [] := by
  constructor
  · intro hl
    rcases l with _ | ⟨y, l⟩
    · rfl
    · have := h y (by simp)
      simp only [List.flatten_cons, List.append_eq_nil_iff] at hl
      rw [hl.1] at this; simp at this; omega
  · rintro rfl; rfl

section Merge

variable {T1 T2 Y tmp C1 C2 : Fin Q} {A dir c f1 f2 kc t1 t2 i t : Fin R}

lemma mrg_mv1 (hstk : [T1, T2, Y, tmp, C1, C2].Nodup) (hAi : A ≠ i) (hAt : A ≠ t) (hit : i ≠ t)
    (S : Fin Q → List ℕ) (s : NSt R Q) {a : ℕ} {a0 : List ℕ} {u v acc : List (List ℕ)}
    (hs : s.stk = mrgStk S T1 T2 Y (a0 :: u) v acc) (ha : s.env A = a) (hl : a0.length = a)
    (hb : ∀ z ∈ a0, z < 2 ^ w) (hw : a + 1 < 2 ^ w) :
    ∃ s', Good x w (mvRec T1 Y tmp A i t) s s' (2 * ((a + 1) * (12 * Ex.nodeCost w))) ∧
      s'.stk = mrgStk S T1 T2 Y u v (a0 :: acc) ∧ Frame s s' [i, t] := by
  have h0 : T1 ≠ T2 := by ndup hstk
  have h1 : T1 ≠ Y := by ndup hstk
  have h2 : T2 ≠ Y := by ndup hstk
  have hT : s.stk T1 = a0 ++ u.flatten := by rw [hs, mrgStk_T1 h0 h1, List.flatten_cons]
  obtain ⟨s', g, k, f⟩ := mvRec_good (x := x) (dst := Y) (tmp := tmp) (by ndup hstk)
    (by ndup hstk) h1 hAi hAt hit s ha (by rw [hT]; simp; omega) hw
    (by rw [hT, List.take_left' hl]; exact hb)
  refine ⟨s', g, ?_, f⟩
  rw [k, hT, List.drop_left' hl, List.take_left' hl, hs]
  exact mrgStk_mv1 h0 h1 h2

lemma mrg_mv2 (hstk : [T1, T2, Y, tmp, C1, C2].Nodup) (hAi : A ≠ i) (hAt : A ≠ t) (hit : i ≠ t)
    (S : Fin Q → List ℕ) (s : NSt R Q) {a : ℕ} {b0 : List ℕ} {u v acc : List (List ℕ)}
    (hs : s.stk = mrgStk S T1 T2 Y u (b0 :: v) acc) (ha : s.env A = a) (hl : b0.length = a)
    (hb : ∀ z ∈ b0, z < 2 ^ w) (hw : a + 1 < 2 ^ w) :
    ∃ s', Good x w (mvRec T2 Y tmp A i t) s s' (2 * ((a + 1) * (12 * Ex.nodeCost w))) ∧
      s'.stk = mrgStk S T1 T2 Y u v (b0 :: acc) ∧ Frame s s' [i, t] := by
  have h0 : T1 ≠ T2 := by ndup hstk
  have h1 : T1 ≠ Y := by ndup hstk
  have h2 : T2 ≠ Y := by ndup hstk
  have hT : s.stk T2 = b0 ++ v.flatten := by rw [hs, mrgStk_T2 h2, List.flatten_cons]
  obtain ⟨s', g, k, f⟩ := mvRec_good (x := x) (dst := Y) (tmp := tmp) (by ndup hstk)
    (by ndup hstk) h2 hAi hAt hit s ha (by rw [hT]; simp; omega) hw
    (by rw [hT, List.take_left' hl]; exact hb)
  refine ⟨s', g, ?_, f⟩
  rw [k, hT, List.drop_left' hl, List.take_left' hl, hs]
  exact mrgStk_mv2 h0 h1 h2

/-- The branching part of the merge body. -/
def mrgIteInner (T1 T2 Y tmp C1 C2 : Fin Q) (A dir c f1 f2 kc t1 t2 i t : Fin R) : CStm R Q :=
  .ite (rv f2)
    (.seq (.ite (rv dir) (cmpS T1 T2 C1 C2 A c kc t1 t2 i t) (cmpS T2 T1 C1 C2 A c kc t1 t2 i t))
      (.ite (.lt (rv c) (.const 2)) (mvRec T1 Y tmp A i t) (mvRec T2 Y tmp A i t)))
    (mvRec T1 Y tmp A i t)

/-- The branching part of the merge body. -/
def mrgIte (T1 T2 Y tmp C1 C2 : Fin Q) (A dir c f1 f2 kc t1 t2 i t : Fin R) : CStm R Q :=
  .ite (rv f1) (mrgIteInner T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t) (mvRec T2 Y tmp A i t)

lemma mrgIte_good (hw2 : 2 ≤ w) (hstk : [T1, T2, Y, tmp, C1, C2].Nodup)
    (hreg : [A, dir, c, f1, f2, kc, t1, t2, i, t].Nodup)
    (S : Fin Q → List ℕ) (d : Bool) (s : NSt R Q) {a : ℕ} (u v acc : List (List ℕ))
    (ha : s.env A = a) (hdir : s.env dir = if d then 1 else 0)
    (hs : s.stk = mrgStk S T1 T2 Y u v acc) (hf1 : s.env f1 = nef u) (hf2 : s.env f2 = nef v)
    (hrec : ∀ y ∈ u ++ v, y.length = a ∧ ∀ z ∈ y, z < 2 ^ w) (hw : a + 1 < 2 ^ w)
    (huv : u ≠ [] ∨ v ≠ []) :
    ∃ s', Good x w (mrgIte T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t) s s'
        (104 * Ex.nodeCost w * a + 120 * Ex.nodeCost w) ∧
      s'.stk = mrgStk S T1 T2 Y (CSort.mrgStep d (u, v, acc)).1 (CSort.mrgStep d (u, v, acc)).2.1
        (CSort.mrgStep d (u, v, acc)).2.2 ∧
      Frame s s' [c, kc, t1, t2, i, t] := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 := two_le_pow hw2
  have hAi : A ≠ i := by ndup hreg
  have hAt : A ≠ t := by ndup hreg
  have hit : i ≠ t := by ndup hreg
  have hsub : ∀ {r : List (Fin R)}, r ⊆ [c, kc, t1, t2, i, t] → ∀ {s₁ s₂ : NSt R Q},
      Frame s₁ s₂ r → Frame s₁ s₂ [c, kc, t1, t2, i, t] := fun h _ _ f => f.mono h
  have hf1v : (rv f1 : Ex R).Fits w s.env := by
    show s.env f1 < 2 ^ w; rw [hf1]; unfold nef; split_ifs <;> omega
  have hf2v : (rv f2 : Ex R).Fits w s.env := by
    show s.env f2 < 2 ^ w; rw [hf2]; unfold nef; split_ifs <;> omega
  rcases u with _ | ⟨a0, u⟩ <;> rcases v with _ | ⟨b0, v⟩
  · simp at huv
  · -- only `T2` is nonempty
    have hb := hrec b0 (by simp)
    obtain ⟨s', g, k, f⟩ := mrg_mv2 (x := x) hstk hAi hAt hit S s hs ha hb.1 hb.2 hw
    refine ⟨s', (Good.iteF hf1v (by simp [rv, Ex.eval, hf1, nef]) g).mono ?_, by simpa [CSort.mrgStep] using k,
      hsub (by intro r hr; simp at hr ⊢; tauto) f⟩
    simp only [condCost, rv, Ex.size]; nlinarith
  · -- only `T1` is nonempty
    have hb := hrec a0 (by simp)
    obtain ⟨s', g, k, f⟩ := mrg_mv1 (x := x) hstk hAi hAt hit S s hs ha hb.1 hb.2 hw
    refine ⟨s', (Good.iteT hf1v (by simp [rv, Ex.eval, hf1, nef])
      (Good.iteF hf2v (by simp [rv, Ex.eval, hf2, nef]) g)).mono ?_,
      by simpa [CSort.mrgStep] using k, hsub (by intro r hr; simp at hr ⊢; tauto) f⟩
    simp only [condCost, rv, Ex.size]; nlinarith
  · -- both nonempty: compare
    have ha0 := hrec a0 (by simp)
    have hb0 := hrec b0 (by simp)
    have hT1 : s.stk T1 = a0 ++ u.flatten := by
      rw [hs, mrgStk_T1 (by ndup hstk) (by ndup hstk), List.flatten_cons]
    have hT2 : s.stk T2 = b0 ++ v.flatten := by
      rw [hs, mrgStk_T2 (by ndup hstk), List.flatten_cons]
    have hcreg : [A, c, kc, t1, t2, i, t].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true] at hreg ⊢
      tauto
    -- the comparison
    obtain ⟨sc, gc, kc', ec, hc2le, fc⟩ : ∃ sc, Good x w (.ite (rv dir) (cmpS T1 T2 C1 C2 A c kc t1 t2 i t)
          (cmpS T2 T1 C1 C2 A c kc t1 t2 i t)) s sc (Ex.nodeCost w + 1 + (a + 1) * (80 * Ex.nodeCost w)) ∧
        sc.stk = s.stk ∧ (CSort.ordD d b0 a0 = true ↔ sc.env c < 2) ∧ sc.env c ≤ 2 ∧
        Frame s sc [c, kc, t1, t2, i, t] := by
      have hdv : (rv dir : Ex R).Fits w s.env := by
        show s.env dir < 2 ^ w; rw [hdir]; split_ifs <;> omega
      cases d
      · obtain ⟨sc, g, k, e, f⟩ := cmpS_good (x := x) hw2 (s1 := T2) (s2 := T1) (c1 := C1)
          (c2 := C2) (by
            have : [T2, T1, C1, C2].Perm [T1, T2, C1, C2] := List.Perm.swap _ _ _
            refine this.nodup_iff.mpr ?_
            have hsl : [T1, T2, C1, C2].Sublist [T1, T2, Y, tmp, C1, C2] := by simp
            exact hsl.nodup hstk) hcreg s b0 a0 v.flatten u.flatten ha hT2 hT1 hb0.1 ha0.1
          hb0.2 ha0.2 hw
        refine ⟨sc, (Good.iteF hdv (by simp [rv, Ex.eval, hdir]) g).mono (by
          simp only [condCost, rv, Ex.size]; omega), k, ?_, by rw [e]; exact cmpW_le 0 _ _ (by omega), f⟩
        rw [e, CSort.ordD, if_neg (by simp), CSort.rle_iff_cmpW b0 a0 (by rw [ha0.1, hb0.1])]
        have := cmpW_le 0 b0 a0 (by omega)
        omega
      · obtain ⟨sc, g, k, e, f⟩ := cmpS_good (x := x) hw2 (s1 := T1) (s2 := T2) (c1 := C1)
          (c2 := C2) (by
            have hsl : [T1, T2, C1, C2].Sublist [T1, T2, Y, tmp, C1, C2] := by simp
            exact hsl.nodup hstk) hcreg s a0 b0 u.flatten v.flatten ha hT1 hT2 ha0.1 hb0.1
          ha0.2 hb0.2 hw
        refine ⟨sc, (Good.iteT hdv (by simp [rv, Ex.eval, hdir]) g).mono (by
          simp only [condCost, rv, Ex.size]; omega), k, ?_, by rw [e]; exact cmpW_le 0 _ _ (by omega), f⟩
        rw [e, CSort.ordD, if_pos rfl, CSort.rle_iff_cmpW a0 b0 (by rw [ha0.1, hb0.1])]
        have := cmpW_le 0 a0 b0 (by omega)
        omega
    have hsc : sc.stk = mrgStk S T1 T2 Y (a0 :: u) (b0 :: v) acc := kc'.trans hs
    have hAc : sc.env A = a := by
      rw [fc.2.2 A (by simp [hAi, hAt, show A ≠ c by ndup hreg, show A ≠ kc by ndup hreg,
        show A ≠ t1 by ndup hreg, show A ≠ t2 by ndup hreg]), ha]
    have hcf : (Ex.lt (rv c) (.const 2) : Ex R).Fits w sc.env :=
      ⟨show sc.env c < 2 ^ w by omega, show 2 < 2 ^ w by omega⟩
    by_cases hord : CSort.ordD d b0 a0 = true
    · obtain ⟨s', g, k, f⟩ := mrg_mv1 (x := x) hstk hAi hAt hit S sc hsc hAc ha0.1 ha0.2 hw
      refine ⟨s', (Good.iteT hf1v (by simp [rv, Ex.eval, hf1, nef])
        (Good.iteT hf2v (by simp [rv, Ex.eval, hf2, nef])
          (gc.seq (Good.iteT hcf (show (if sc.env c < 2 then 1 else 0) ≠ 0 by rw [if_pos (ec.mp hord)]; decide) g)))).mono ?_, ?_,
        fc.trans (f.mono (regs' := [c, kc, t1, t2, i, t]) (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          rcases hr with rfl | rfl <;> simp))⟩
      · simp only [condCost, rv, Ex.size]; ring_nf; omega
      · rw [k]; simp [CSort.mrgStep, hord]
    · have hc2 : ¬ sc.env c < 2 := fun h => hord (ec.mpr h)
      obtain ⟨s', g, k, f⟩ := mrg_mv2 (x := x) hstk hAi hAt hit S sc hsc hAc hb0.1 hb0.2 hw
      have hfr : Frame s s' [c, kc, t1, t2, i, t] :=
        fc.trans (f.mono (regs' := [c, kc, t1, t2, i, t]) (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          rcases hr with rfl | rfl <;> simp))
      have hev : Ex.eval sc.env (Ex.lt (rv c) (.const 2)) = 0 := by
        show (if sc.env c < 2 then 1 else 0) = 0
        exact if_neg hc2
      have G := Good.iteT (p := mrgIteInner T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t)
        (q := mvRec T2 Y tmp A i t) hf1v (by simp [rv, Ex.eval, hf1, nef])
        (Good.iteT (q := mvRec T1 Y tmp A i t) hf2v (by simp [rv, Ex.eval, hf2, nef])
          (gc.seq (Good.iteF (p := mvRec T1 Y tmp A i t) hcf hev g)))
      refine ⟨s', G.mono ?_, ?_, hfr⟩
      · simp only [condCost, rv, Ex.size]; ring_nf; omega
      · rw [k]; simp [CSort.mrgStep, hord]

/-- The body of the merge loop. -/
def mrgBody (T1 T2 Y tmp C1 C2 : Fin Q) (A dir c f1 f2 kc t1 t2 i t : Fin R) : CStm R Q :=
  .seq (mrgIte T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t) (.seq (.sne f1 T1) (.sne f2 T2))

/-- Merge the runs on `T1` and `T2` onto `Y` (`CSort.mrg`, direction in `dir`). -/
def mrgS (T1 T2 Y tmp C1 C2 : Fin Q) (A dir c f1 f2 kc t1 t2 i t : Fin R) : CStm R Q :=
  .seq (.sne f1 T1) (.seq (.sne f2 T2)
    (.loop (.add (rv f1) (rv f2)) (mrgBody T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t)))

end Merge

end CStm

end Lax119563Proofs.Compiler
