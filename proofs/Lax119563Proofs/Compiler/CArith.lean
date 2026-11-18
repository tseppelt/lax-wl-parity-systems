import Lax119563Proofs.Compiler.CFrame

/-!
# Small arithmetic and stack routines

* `mulS dst a b j`: `dst := a · b` by repeated addition (`mulS_good`);
* `predS dst n`: `dst := n - 1` by counting (`predS_good`);
* `pushZS q n j`: push `n` zeros onto `q` (`pushZS_good`);
* `mvSumN src dst n j t acc`: move the top `n` words of `src` onto `dst` (reversed),
  adding them to `acc` (`mvSumN_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

lemma set_set_comm (st : NSt R Q) {r r' : Fin R} (h : r ≠ r') (u v : ℕ) :
    (st.set r u).set r' v = (st.set r' v).set r u := by
  simp only [NSt.set, Function.update_comm h]

lemma set_set_same (st : NSt R Q) (r : Fin R) (u v : ℕ) :
    (st.set r u).set r v = st.set r v := by
  simp only [NSt.set, Function.update_idem]

/-! ## Multiplication -/

/-- `dst := a · b` (counter `j`). -/
def mulS (dst a b j : Fin R) : CStm R Q :=
  .seq (.set dst (.const 0)) (.seq (.set j (.const 0))
    (.loop (.lt (rv j) (rv b))
      (.seq (.set dst (.add (rv dst) (rv a))) (.set j (.add (rv j) (.const 1))))))

lemma mulS_good (hw : 2 ≤ w) {dst a b j : Fin R} (hda : dst ≠ a) (hdb : dst ≠ b) (hdj : dst ≠ j)
    (haj : a ≠ j) (hbj : b ≠ j) (st : NSt R Q) {A B : ℕ} (hA : st.env a = A)
    (hB : st.env b = B) (hAB : A * B < 2 ^ w) (hBw : B < 2 ^ w) :
    Good x w (mulS dst a b j) st ((st.set dst (A * B)).set j B)
      ((B + 1) * (12 * Ex.nodeCost w)) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h1 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  set S : ℕ → NSt R Q := fun i => (st.set dst (A * i)).set j i with hS
  have eA : ∀ i, (S i).env a = A := fun i => by
    simp [S, Function.update_of_ne haj, Function.update_of_ne (Ne.symm hda), hA]
  have eB : ∀ i, (S i).env b = B := fun i => by
    simp [S, Function.update_of_ne hbj, Function.update_of_ne (Ne.symm hdb), hB]
  have eD : ∀ i, (S i).env dst = A * i := fun i => by
    simp [S, Function.update_of_ne hdj]
  have eJ : ∀ i, (S i).env j = i := fun i => by simp [S]
  have hloop := Good.loop_const (x := x) (w := w) (e := .lt (rv j) (rv b))
    (body := .seq (.set dst (.add (rv dst) (rv a))) (.set j (.add (rv j) (.const 1))))
    B S (8 * Ex.nodeCost w)
    (fun i hi => by simp only [Ex.eval, rv, eJ, eB, if_pos hi]; omega)
    (by simp only [Ex.eval, rv, eJ, eB]; simp)
    (fun i hi => by simp only [Ex.Fits, rv, eJ, eB]; omega)
    (fun i hi => by
      have hAi : A * (i + 1) ≤ A * B := Nat.mul_le_mul_left _ hi
      refine ((Good.set ?_).seq (Good.set ?_)).of_eq ?_ ?_
      · simp only [Ex.Fits, rv, eD, eA, Ex.eval]
        refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
      · simp only [Ex.Fits, rv, Ex.eval, NSt.set_env, Function.update_of_ne (Ne.symm hdj), eJ]
        omega
      · simp only [S]
        rcases st with ⟨env, stk, pos, out⟩
        simp only [NSt.set, Ex.eval, rv, NSt.mk.injEq, and_true]
        funext r
        simp only [Function.update_apply]
        split_ifs <;> simp_all <;> ring
      · simp only [Ex.size]; omega)
  have h0 := Good.set (x := x) (w := w) (r := dst) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  have h0' := Good.set (x := x) (w := w) (r := j) (e := .const 0)
    (st := st.set dst ((Ex.const 0 : Ex R).eval st.env)) (by simp only [Ex.Fits]; omega)
  have hS0 : (st.set dst ((Ex.const 0 : Ex R).eval st.env)).set j
      ((Ex.const 0 : Ex R).eval (st.set dst ((Ex.const 0 : Ex R).eval st.env)).env) = S 0 := by
    simp [S, Ex.eval]
  rw [hS0] at h0'
  refine ((h0.seq (h0'.seq hloop)).mono ?_)
  simp only [condCost, Ex.size, rv]
  nlinarith

/-! ## Predecessor -/

/-- `dst := n - 1` (for `n ≥ 1`; `0` for `n = 0`). -/
def predS (dst n : Fin R) : CStm R Q :=
  .seq (.set dst (.const 0)) (.loop (.lt (.add (rv dst) (.const 1)) (rv n))
    (.set dst (.add (rv dst) (.const 1))))

lemma predS_good (hw : 2 ≤ w) {dst n : Fin R} (hdn : dst ≠ n) (st : NSt R Q) {N : ℕ}
    (hN : st.env n = N) (hNw : N + 1 < 2 ^ w) :
    Good x w (predS dst n) st (st.set dst (N - 1)) ((N + 1) * (12 * Ex.nodeCost w)) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set S : ℕ → NSt R Q := fun i => st.set dst i with hS
  have eD : ∀ i, (S i).env dst = i := fun i => by simp [S]
  have eN : ∀ i, (S i).env n = N := fun i => by simp [S, Function.update_of_ne (Ne.symm hdn), hN]
  have hloop := Good.loop_const (x := x) (w := w) (e := .lt (.add (rv dst) (.const 1)) (rv n))
    (body := .set dst (.add (rv dst) (.const 1))) (N - 1) S (4 * Ex.nodeCost w)
    (fun i hi => by simp only [Ex.eval, rv, eD, eN]; rw [if_pos (by omega)]; omega)
    (by simp only [Ex.eval, rv, eD, eN]; rw [if_neg (by omega)])
    (fun i hi => by simp only [Ex.Fits, Ex.eval, rv, eD, eN]; omega)
    (fun i hi => (Good.set (by simp only [Ex.Fits, Ex.eval, rv, eD]; omega)).of_eq
      (by simp only [Ex.eval, rv, eD, S, set_set_same]) (by simp only [Ex.size]; omega))
  refine (((Good.set (by simp only [Ex.Fits]; omega)).seq hloop).of_eq rfl ?_)
  simp only [condCost, Ex.size, rv]
  have : N - 1 ≤ N := Nat.sub_le N 1
  nlinarith

/-! ## Pushing zeros -/

/-- Push `n` zeros onto `q` (counter `j`). -/
def pushZS (q : Fin Q) (n j : Fin R) : CStm R Q :=
  .seq (.set j (.const 0)) (.loop (.lt (rv j) (rv n))
    (.seq (.push q (.const 0)) (.set j (.add (rv j) (.const 1)))))

lemma pushZS_good (hw : 2 ≤ w) {q : Fin Q} {n j : Fin R} (hnj : n ≠ j) (st : NSt R Q) {N : ℕ}
    (hN : st.env n = N) (hNw : N + 1 < 2 ^ w) :
    Good x w (pushZS q n j) st ((st.setS q (List.replicate N 0 ++ st.stk q)).set j N)
      ((N + 1) * (12 * Ex.nodeCost w)) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set S : ℕ → NSt R Q := fun i => (st.setS q (List.replicate i 0 ++ st.stk q)).set j i with hS
  have eJ : ∀ i, (S i).env j = i := fun i => by simp [S]
  have eN : ∀ i, (S i).env n = N := fun i => by simp [S, Function.update_of_ne hnj, hN]
  have hloop := Good.loop_const (x := x) (w := w) (e := .lt (rv j) (rv n))
    (body := .seq (.push q (.const 0)) (.set j (.add (rv j) (.const 1)))) N S
    (6 * Ex.nodeCost w)
    (fun i hi => by simp only [Ex.eval, rv, eJ, eN, if_pos hi]; omega)
    (by simp only [Ex.eval, rv, eJ, eN]; simp)
    (fun i hi => by simp only [Ex.Fits, rv, eJ, eN]; omega)
    (fun i hi => ((Good.push (by simp only [Ex.Fits]; omega)).seq
      (Good.set (by simp only [Ex.Fits, Ex.eval, rv, NSt.setS_env, eJ]; omega))).of_eq
      (by
        simp only [Ex.eval, rv, NSt.setS_env, eJ, S]
        simp only [NSt.set, NSt.setS, Function.update_idem, Function.update_self,
          List.replicate_succ, List.cons_append])
      (by simp only [Ex.size]; omega))
  have hS0 : st.set j ((Ex.const 0 : Ex R).eval st.env) = S 0 := by
    simp [S, Ex.eval, NSt.setS]
  have h0 := Good.set (x := x) (w := w) (r := j) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  rw [hS0] at h0
  refine (h0.seq hloop).mono ?_
  simp only [condCost, Ex.size, rv]
  nlinarith

/-! ## Moving and summing -/

/-- Move the top `n` words of `src` onto `dst`, adding them to `acc`. -/
def mvSumN (src dst : Fin Q) (n j t acc : Fin R) : CStm R Q :=
  .seq (.set j (.const 0)) (.loop (.lt (rv j) (rv n))
    (.seq (.pop src t) (.seq (.push dst (rv t))
      (.seq (.set acc (.add (rv acc) (rv t))) (.set j (.add (rv j) (.const 1)))))))

lemma mvSumN_good (hw : 2 ≤ w) {src dst : Fin Q} {n j t acc : Fin R} (hsd : src ≠ dst)
    (hnj : n ≠ j) (hnt : n ≠ t) (hna : n ≠ acc) (hjt : j ≠ t) (hja : j ≠ acc) (hta : t ≠ acc)
    (st : NSt R Q) {N : ℕ} (hN : st.env n = N) (hlen : N ≤ (st.stk src).length)
    (hNw : N + 1 < 2 ^ w) (hsum : st.env acc + ((st.stk src).take N).sum < 2 ^ w) :
    ∃ st', Good x w (mvSumN src dst n j t acc) st st' ((N + 1) * (16 * Ex.nodeCost w)) ∧
      st'.stk = movedStk st.stk src dst N ∧
      st'.env acc = st.env acc + ((st.stk src).take N).sum ∧ Frame st st' [j, t, acc] := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set A0 := st.env acc
  set L := st.stk src
  set Inv : NSt R Q → Prop := fun s => s.env j ≤ N ∧ s.env n = N ∧
    s.stk = movedStk st.stk src dst (s.env j) ∧ s.env acc = A0 + (L.take (s.env j)).sum ∧
    Frame st s [j, t, acc]
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv j) (rv n))
    (body := .seq (.pop src t) (.seq (.push dst (rv t))
      (.seq (.set acc (.add (rv acc) (rv t))) (.set j (.add (rv j) (.const 1))))))
    Inv (fun s => N - s.env j) (fun _ => 0) 0 (12 * Ex.nodeCost w) (by
      intro s ⟨hi, hn, hs, ha, hf⟩
      refine ⟨by simp only [Ex.Fits, rv, hn]; omega, fun hc => ?_⟩
      have hlt : s.env j < N := by simpa [rv, Ex.eval, hn] using hc
      obtain ⟨i, hi'⟩ : ∃ i, s.env j = i := ⟨_, rfl⟩
      rw [hi'] at hlt hs ha hi
      have hsrc : s.stk src = L.drop i := by rw [hs, movedStk_src _ hsd]
      have hd := List.drop_eq_getElem_cons (show i < L.length by omega)
      have hsplit : (L.take (i + 1)).sum = (L.take i).sum + L[i] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
          List.sum_append, List.sum_singleton]
      have hmono : (L.take (i + 1)).sum ≤ (L.take N).sum := by
        rw [← List.take_append_drop (i + 1) (L.take N), List.take_take,
          min_eq_left (by omega), List.sum_append]; omega
      have hhead : (s.stk src).headD 0 = L[i] := by rw [hsrc, hd]; rfl
      have htail : (s.stk src).tail = L.drop (i + 1) := by rw [hsrc, hd]; rfl
      set s1 := (s.setS src (s.stk src).tail).set t ((s.stk src).headD 0)
      have e1t : s1.env t = L[i] := by simp only [s1, NSt.set_env, Function.update_self]; exact hhead
      have e1a : s1.env acc = A0 + (L.take i).sum := by
        simp [s1, Function.update_of_ne hta.symm, ha]
      have e1j : s1.env j = i := by simp [s1, Function.update_of_ne hjt, hi']
      have e1n : s1.env n = N := by simp [s1, Function.update_of_ne hnt, hn]
      have e1s : s1.stk = Function.update s.stk src (L.drop (i + 1)) := by simp [s1, htail]
      set s2 := s1.setS dst ((rv t : Ex R).eval s1.env :: s1.stk dst)
      have e2 : s2.env = s1.env := rfl
      set s3 := s2.set acc ((Ex.add (rv acc) (rv t)).eval s2.env)
      have e3a : s3.env acc = A0 + (L.take (i + 1)).sum := by
        simp [s3, e2, Ex.eval, rv, e1a, e1t, hsplit]; ring
      have e3j : s3.env j = i := by simp [s3, Function.update_of_ne hja, e2, e1j]
      set s4 := s3.set j ((Ex.add (rv j) (.const 1)).eval s3.env)
      have e4j : s4.env j = i + 1 := by simp [s4, Ex.eval, rv, e3j]
      have e4 : ∀ r, r ≠ j → r ≠ acc → r ≠ t → s4.env r = s.env r := by
        intro r h1 h2 h3
        simp [s4, s3, e2, s1, Function.update_of_ne h1, Function.update_of_ne h2,
          Function.update_of_ne h3]
      refine ⟨s4, ((Good.pop src t).seq ((Good.push ?_).seq ((Good.set ?_).seq
        (Good.set ?_)))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, le_rfl⟩
      · show s1.env t < 2 ^ w
        rw [e1t]; omega
      · show s1.env acc < 2 ^ w ∧ s1.env t < 2 ^ w ∧ s1.env acc + s1.env t < 2 ^ w
        rw [e1t, e1a]; omega
      · show s3.env j < 2 ^ w ∧ 1 < 2 ^ w ∧ s3.env j + 1 < 2 ^ w
        rw [e3j]; omega
      · simp only [Ex.size, rv]; omega
      · rw [e4j]; omega
      · rw [e4 _ hnj hna hnt, hn]
      · rw [e4j]
        show Function.update s1.stk dst (s1.env t :: s1.stk dst) = _
        rw [e1t, e1s, hs]
        funext q
        unfold movedStk
        by_cases h1 : q = dst
        · subst h1
          simp only [Function.update_self, Function.update_of_ne hsd.symm]
          rw [show st.stk src = L from rfl, List.take_add_one,
            List.getElem?_eq_getElem (by omega)]
          simp only [List.reverse_append, Option.toList_some, List.reverse_cons,
            List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append]
        · by_cases h2 : q = src
          · subst h2; simp [Function.update_of_ne h1]; rfl
          · simp [Function.update_of_ne h1, Function.update_of_ne h2]
      · rw [e4j]; simpa [s4, Function.update_of_ne hja.symm] using e3a
      · refine ⟨hf.1, hf.2.1, fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [e4 r hr.1 hr.2.2 hr.2.1]
        exact hf.2.2 r (by simp [hr.1, hr.2.1, hr.2.2])
      · rw [e4j]; omega)
  have h0 := Good.set (x := x) (w := w) (r := j) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  obtain ⟨s', h', ⟨hi', hn', hs', ha', hf'⟩, hend⟩ := hloop (st.set j (Ex.eval st.env (.const 0)))
    ⟨by simp [Ex.eval], by simp [Function.update_of_ne hnj, hN],
      by simp [Ex.eval, movedStk_zero _ _ _ hsd],
      by simp [Ex.eval, Function.update_of_ne (Ne.symm hja), A0],
      ⟨rfl, rfl, fun r hr => by
        simp at hr; simp [Function.update_of_ne hr.1]⟩⟩
  have hin : s'.env j = N := by
    simp only [rv, Ex.eval, hn'] at hend; split_ifs at hend <;> omega
  refine ⟨s', (h0.seq h').mono ?_, by rw [hs', hin], by rw [ha', hin], hf'⟩
  simp only [condCost, rv, Ex.size, Nat.sub_zero, mul_zero, zero_add, NSt.set_env,
    Function.update_self, Ex.eval]
  nlinarith

end CStm

end Lax119563Proofs.Compiler
