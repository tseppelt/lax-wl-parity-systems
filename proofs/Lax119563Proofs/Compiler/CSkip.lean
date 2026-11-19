import Lax119563Proofs.Compiler.PTriv

/-!
# Skipping lists of numbers

* `skipNumsS n i t`: skip the next `n` numbers (any sizes; counter `i`, scratch `t`),
  `skipNumsS_good`.
* `skipBlocksS d m j i t`: skip the next `d` blocks of `m` numbers each, `skipBlocksS_good`.

Both specifications give the cursor, stacks, output and all registers but the counters and
the scratch register explicitly; the cost is linear in the number of bits skipped.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

lemma length_encodeNats_take_le (vs : List ℕ) (j : ℕ) :
    (encodeNats (vs.take j)).length ≤ (encodeNats vs).length := by
  conv_rhs => rw [← List.take_append_drop j vs]
  rw [encodeNats_append, List.length_append]; omega

lemma encodeNats_split (vs : List ℕ) {j : ℕ} (hj : j < vs.length) :
    encodeNats vs = encodeNats (vs.take j) ++
      (encodeNat vs[j] ++ encodeNats (vs.drop (j + 1))) := by
  conv_lhs => rw [← List.take_append_drop j vs, List.drop_eq_getElem_cons hj]
  simp only [encodeNats, List.flatMap_append, List.flatMap_cons]

namespace CStm

/-- Skip the next `n` numbers (counter `i`, scratch `t`). -/
def skipNumsS (n i t : Fin R) : CStm R Q :=
  .seq (.set i (.const 0)) (.loop (.lt (rv i) (rv n))
    (.seq (skipNumS t) (.set i (.add (rv i) (.const 1)))))

/-- **Skipping a list of numbers.** -/
lemma skipNumsS_good (hw : 2 ≤ w) {n i t : Fin R} (hni : n ≠ i) (hnt : n ≠ t) (hit : i ≠ t)
    (st : NSt R Q) (vs : List ℕ) (rest : List Bool)
    (hx : x.drop st.pos = encodeNats vs ++ rest) (hn : st.env n = vs.length)
    (hnw : vs.length + 1 < 2 ^ w) :
    ∃ st', Good x w (skipNumsS n i t : CStm R Q) st st'
        (((encodeNats vs).length + vs.length + 1) * (20 * Ex.nodeCost w)) ∧
      st'.stk = st.stk ∧ st'.pos = st.pos + (encodeNats vs).length ∧ st'.out = st.out ∧
      ∀ r, r ≠ i → r ≠ t → st'.env r = st.env r := by
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  set P := st.pos + (encodeNats vs).length with hP
  set Inv : NSt R Q → Prop := fun s => s.env i ≤ vs.length ∧ s.stk = st.stk ∧
    s.pos = st.pos + (encodeNats (vs.take (s.env i))).length ∧ s.out = st.out ∧
    ∀ r, r ≠ i → r ≠ t → s.env r = st.env r with hInv
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv i) (rv n))
    (body := .seq (skipNumS t) (.set i (.add (rv i) (.const 1)))) Inv
    (fun s => vs.length - s.env i) (fun s => P - s.pos) (4 * Ex.nodeCost w)
    (10 * Ex.nodeCost w) (by
      intro s ⟨hi, hs, hp, ho, hf⟩
      have hns : s.env n = vs.length := by rw [hf n hni hnt, hn]
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hc
      have hlt : s.env i < vs.length := by
        by_contra h; apply hc; simp only [Ex.eval, rv, hns]; rw [if_neg h]
      set j := s.env i with hj
      have hxj : x.drop s.pos = encodeNat vs[j] ++ (encodeNats (vs.drop (j + 1)) ++ rest) := by
        rw [hp, drop_add, hx, encodeNats_split vs hlt, List.append_assoc, List.drop_left,
          List.append_assoc]
      have h1 := skipNumS_good (Q := Q) hw (t := t) s vs[j] _ hxj
      set s1 := skipNumFinal s t vs[j]
      have hi1 : s1.env i = j := skipNumFinal_env_ne hit _
      have h2 := Good.set (x := x) (w := w) (r := i) (e := Ex.add (rv i) (.const 1)) (st := s1)
        (by simp only [Ex.Fits, Ex.eval, rv, hi1]; omega)
      have hlen : (encodeNats (vs.take (j + 1))).length =
          (encodeNats (vs.take j)).length + (encodeNat vs[j]).length := by
        rw [encodeNats_take_succ vs hlt, List.length_append]
      have hle := length_encodeNats_take_le vs (j + 1)
      have hp1 : s1.pos = s.pos + (encodeNat vs[j]).length := rfl
      have hi2 : (s1.set i (Ex.eval s1.env (Ex.add (rv i) (.const 1)))).env i = j + 1 := by
        simp [Ex.eval, rv, hi1]
      refine ⟨_, (h1.seq h2).mono ?_, ⟨by rw [hi2]; omega, by simp [s1, hs], ?_,
        by simp [s1, ho], fun r h1 h2 => ?_⟩, ?_, ?_⟩
      · simp only [Ex.size, rv, NSt.set_pos, hp1]
        have hΔ : P - s.pos - (P - (s.pos + (encodeNat vs[j]).length)) =
            (encodeNat vs[j]).length := by omega
        rw [hΔ]
        generalize Ex.nodeCost w = N at *
        generalize unitCost w = U at *
        generalize (encodeNat vs[j]).length = lv at *
        nlinarith
      · rw [hi2, NSt.set_pos, hp1, hp, hlen]; ring
      · simp only [NSt.set_env, Function.update_of_ne h1]
        rw [skipNumFinal_env_ne h2, hf r h1 h2]
      · rw [hi2]; omega
      · simp only [NSt.set_pos, hp1]; omega)
  have h0 := Good.set (x := x) (w := w) (r := i) (e := (.const 0 : Ex R)) (st := st)
    (by simp only [Ex.Fits]; omega)
  have hI0 : Inv (st.set i (Ex.eval st.env (.const 0))) := by
    refine ⟨by simp [Ex.eval], rfl, by simp [Ex.eval, encodeNats], rfl, fun r h1 _ => ?_⟩
    simp [Function.update_of_ne h1]
  obtain ⟨s', h', ⟨hi', hs', hp', ho', hf'⟩, hend⟩ := hloop _ hI0
  have hns : s'.env n = vs.length := by rw [hf' n hni hnt, hn]
  have hin : s'.env i = vs.length := by
    simp only [rv, Ex.eval, hns] at hend; split_ifs at hend <;> omega
  refine ⟨s', (h0.seq h').mono ?_, hs', by rw [hp', hin, List.take_of_length_le le_rfl], ho',
    hf'⟩
  simp only [condCost, rv, Ex.size, Ex.eval, NSt.set_env, NSt.set_pos, Function.update_self,
    Nat.sub_zero]
  have hφ : P - st.pos = (encodeNats vs).length := by omega
  rw [hφ]
  generalize Ex.nodeCost w = N at *
  generalize unitCost w = U at *
  generalize (encodeNats vs).length = le at *
  nlinarith

/-- Skip the next `d` blocks of `m` numbers each (counters `j`, `i`, scratch `t`). -/
def skipBlocksS (d m j i t : Fin R) : CStm R Q :=
  .seq (.set j (.const 0)) (.loop (.lt (rv j) (rv d))
    (.seq (skipNumsS m i t) (.set j (.add (rv j) (.const 1)))))

/-- **Skipping blocks of numbers.** -/
lemma skipBlocksS_good (hw : 2 ≤ w) {d m j i t : Fin R} (hdj : d ≠ j) (hdi : d ≠ i)
    (hdt : d ≠ t) (hmj : m ≠ j) (hmi : m ≠ i) (hmt : m ≠ t) (hji : j ≠ i) (hjt : j ≠ t)
    (hit : i ≠ t) (st : NSt R Q) (bs : List (List ℕ)) (M : ℕ) (hbs : ∀ b ∈ bs, b.length = M)
    (rest : List Bool) (hx : x.drop st.pos = encodeNats bs.flatten ++ rest)
    (hd : st.env d = bs.length) (hm : st.env m = M) (hdw : bs.length + 1 < 2 ^ w)
    (hmw : M + 1 < 2 ^ w) :
    ∃ st', Good x w (skipBlocksS d m j i t : CStm R Q) st st'
        (((encodeNats bs.flatten).length + bs.length + 1) * (50 * Ex.nodeCost w)) ∧
      st'.stk = st.stk ∧ st'.pos = st.pos + (encodeNats bs.flatten).length ∧
      st'.out = st.out ∧ ∀ r, r ≠ j → r ≠ i → r ≠ t → st'.env r = st.env r := by
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  set P := st.pos + (encodeNats bs.flatten).length with hP
  set Inv : NSt R Q → Prop := fun s => s.env j ≤ bs.length ∧ s.stk = st.stk ∧
    s.pos = st.pos + (encodeNats (bs.take (s.env j)).flatten).length ∧ s.out = st.out ∧
    ∀ r, r ≠ j → r ≠ i → r ≠ t → s.env r = st.env r with hInv
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv j) (rv d))
    (body := .seq (skipNumsS m i t) (.set j (.add (rv j) (.const 1)))) Inv
    (fun s => bs.length - s.env j) (fun s => P - s.pos) (40 * Ex.nodeCost w)
    (30 * Ex.nodeCost w) (by
      intro s ⟨hj, hs, hp, ho, hf⟩
      have hds : s.env d = bs.length := by rw [hf d hdj hdi hdt, hd]
      have hms : s.env m = M := by rw [hf m hmj hmi hmt, hm]
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hc
      have hlt : s.env j < bs.length := by
        by_contra h; apply hc; simp only [Ex.eval, rv, hds]; rw [if_neg h]
      set a := s.env j with ha
      have hsplit : bs.flatten = (bs.take a).flatten ++ (bs[a] ++ (bs.drop (a + 1)).flatten) := by
        have e := List.take_append_drop a bs
        rw [List.drop_eq_getElem_cons hlt] at e
        conv_lhs => rw [← e]
        simp only [List.flatten_append, List.flatten_cons]
      have hxj : x.drop s.pos = encodeNats bs[a] ++
          (encodeNats (bs.drop (a + 1)).flatten ++ rest) := by
        rw [hp, drop_add, hx, hsplit, encodeNats_append, encodeNats_append, List.append_assoc,
          List.drop_left, List.append_assoc]
      have hba : bs[a].length = M := hbs _ (List.getElem_mem hlt)
      obtain ⟨s1, h1, hs1, hp1, ho1, hf1⟩ := skipNumsS_good (Q := Q) hw hmi hmt hit s bs[a] _
        hxj (by rw [hms, hba]) (by rw [hba]; exact hmw)
      have hj1 : s1.env j = a := hf1 j hji hjt
      have h2 := Good.set (x := x) (w := w) (r := j) (e := Ex.add (rv j) (.const 1)) (st := s1)
        (by simp only [Ex.Fits, Ex.eval, rv, hj1]; omega)
      have htake : (bs.take (a + 1)).flatten = (bs.take a).flatten ++ bs[a] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.flatten_append, List.flatten_cons, List.flatten_nil,
          List.append_nil]
      have hlen : (encodeNats (bs.take (a + 1)).flatten).length =
          (encodeNats (bs.take a).flatten).length + (encodeNats bs[a]).length := by
        rw [htake, encodeNats_append, List.length_append]
      have hle : (encodeNats (bs.take (a + 1)).flatten).length ≤
          (encodeNats bs.flatten).length := by
        conv_rhs => rw [← List.take_append_drop (a + 1) bs]
        rw [List.flatten_append, encodeNats_append, List.length_append]; omega
      have hM : M ≤ (encodeNats bs[a]).length := by
        rw [← hba]; exact length_le_encodeNats _
      have hj2 : (s1.set j (Ex.eval s1.env (Ex.add (rv j) (.const 1)))).env j = a + 1 := by
        simp [Ex.eval, rv, hj1]
      refine ⟨_, (h1.seq h2).mono ?_, ⟨by rw [hj2]; omega, by simp [hs1, hs], ?_,
        by simp [ho1, ho], fun r r1 r2 r3 => ?_⟩, ?_, ?_⟩
      · simp only [Ex.size, rv, NSt.set_pos, hp1]
        have hΔ : P - s.pos - (P - (s.pos + (encodeNats bs[a]).length)) =
            (encodeNats bs[a]).length := by omega
        rw [hΔ]
        generalize Ex.nodeCost w = N at *
        generalize unitCost w = U at *
        generalize (encodeNats bs[a]).length = lv at *
        nlinarith
      · rw [hj2, NSt.set_pos, hp1, hp, hlen]; ring
      · simp only [NSt.set_env, Function.update_of_ne r1]
        rw [hf1 r r2 r3, hf r r1 r2 r3]
      · rw [hj2]; omega
      · simp only [NSt.set_pos, hp1]; omega)
  have h0 := Good.set (x := x) (w := w) (r := j) (e := (.const 0 : Ex R)) (st := st)
    (by simp only [Ex.Fits]; omega)
  have hI0 : Inv (st.set j (Ex.eval st.env (.const 0))) := by
    refine ⟨by simp [Ex.eval], rfl, by simp [Ex.eval, encodeNats], rfl, fun r h1 _ _ => ?_⟩
    simp [Function.update_of_ne h1]
  obtain ⟨s', h', ⟨hj', hs', hp', ho', hf'⟩, hend⟩ := hloop _ hI0
  have hds : s'.env d = bs.length := by rw [hf' d hdj hdi hdt, hd]
  have hjn : s'.env j = bs.length := by
    simp only [rv, Ex.eval, hds] at hend; split_ifs at hend <;> omega
  refine ⟨s', (h0.seq h').mono ?_, hs', by rw [hp', hjn, List.take_of_length_le le_rfl], ho',
    hf'⟩
  simp only [condCost, rv, Ex.size, Ex.eval, NSt.set_env, NSt.set_pos, Function.update_self,
    Nat.sub_zero]
  have hφ : P - st.pos = (encodeNats bs.flatten).length := by omega
  rw [hφ]
  generalize Ex.nodeCost w = N at *
  generalize unitCost w = U at *
  generalize (encodeNats bs.flatten).length = le at *
  nlinarith

end CStm

end Lax119563Proofs.Compiler
