import Lax119563Proofs.Circuits.Part1
import Lax119563Proofs.Compiler.Part1
import Lax119563Proofs.Compiler.Part2
import Lax119563Proofs.Reduction.Part3

/-! ### Formerly `Lax119563Proofs.Compiler.CSkip` -/

section Compiler_CSkip

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

end Compiler_CSkip

/-! ### Formerly `Lax119563Proofs.Compiler.PLoc` -/

section Compiler_PLoc

/-!
# Pass `P1` of the compiler program: the locations

`p1` (nontrivial systems, where `ℓ ≤ H`) rewinds the input, skips `k`, reads `ℓ` and `W`,
and for each location `v` reads `ι(v)` and `|D_v|`, pushes the offset
`locOff I v = locStart I v - locBase I` of its first coordinate name onto the stack `qLoc`
and skips its coordinates; finally it reads `E` (`p1_good`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Registers and stacks -/

/-- `ℓ` and `ℓ + 1`. -/
def rL : Fin CR := 9
def rL1 : Fin CR := 10
/-- The running offset of the coordinate names. -/
def rOff : Fin CR := 11
/-- Counters of the skipping loops. -/
def rK : Fin CR := 12
def rI : Fin CR := 13
/-- The offsets of the locations. -/
def qLoc : Fin CQ := 0

/-! ## Coordinates and sizes -/

section Sizes

variable {k ℓ : ℕ}

lemma coordNum_injective : Function.Injective (coordNum : Coord k ℓ → ℕ) := by
  rintro ⟨i, b⟩ ⟨i', b'⟩ h
  simp only [coordNum, blockNum_eq_regVal] at h
  have hb := regVal_lt b
  have hb' := regVal_lt b'
  have e1 : ((i : ℕ) * 2 ^ ℓ + Circuits.regVal b) / 2 ^ ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hb, zero_add]
  have e2 : ((i' : ℕ) * 2 ^ ℓ + Circuits.regVal b') / 2 ^ ℓ = i' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hb', zero_add]
  have hi : (i : ℕ) = i' := by rw [← e1, ← e2, h]
  have hr : Circuits.regVal b = Circuits.regVal b' := by rw [hi] at h; omega
  rw [Fin.ext hi, regVal_injective hr]

lemma card_image_coordNum (D : Finset (Coord k ℓ)) :
    (D.image coordNum).card = (coordList D).length := by
  rw [Finset.card_image_of_injective _ coordNum_injective,
    ← List.toFinset_card_of_nodup (nodup_coordList D)]
  congr 1; ext c; simp

end Sizes

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The sorted coordinate numbers of location `v`. -/
noncomputable def locNums (v : Fin I.numLocations) : List ℕ :=
  ((I.domain v).image coordNum).sort (· ≤ ·)

lemma length_locNums (v : Fin I.numLocations) :
    (locNums I v).length = (coordList (I.domain v)).length := by
  rw [locNums, Finset.length_sort, card_image_coordNum]

lemma locD_eq' (v : Fin I.numLocations) : locD I v = initNum (I.init v) ::
    (coordList (I.domain v)).length :: ((locNums I v).map (coordNumDescription ℓ)).flatten := by
  rw [locD, domainDescription, ← length_locNums, List.flatMap_def]; rfl

lemma length_flatten_cnd (v : Fin I.numLocations) :
    (((locNums I v).map (coordNumDescription ℓ)).flatten).length =
      (coordList (I.domain v)).length * (ℓ + 1) := by
  rw [List.length_flatten, List.map_map, ← length_locNums]
  have : ((locNums I v).map (List.length ∘ coordNumDescription ℓ)) =
      (locNums I v).map fun _ => ℓ + 1 := by
    refine List.map_congr_left fun c _ => ?_
    simp [coordNumDescription]
  rw [this, sum_map_const]

lemma locSize_eq (v : Fin I.numLocations) : locSize I v = (coordList (I.domain v)).length +
    (if initNum (I.init v) < 1 then (coordList (I.domain v)).length else 0) := by
  unfold locSize coordLabs
  rcases h : I.init v with _ | b
  · simp [initNum, bits1]; ring
  · simp [initNum]

lemma locSize_le (v : Fin I.numLocations) : locSize I v ≤ 2 * (locD I v).length := by
  rw [locSize_eq, locD_eq']
  have := length_flatten_cnd I v
  simp only [List.length_cons]
  split_ifs <;> nlinarith

/-- The offset of the first coordinate name of location `j` from `locBase`. -/
noncomputable def locOff (j : ℕ) : ℕ :=
  (((List.finRange I.numLocations).take j).map (locSize I)).sum

/-- The offsets of all locations. -/
noncomputable def locOffs : List ℕ := (List.range I.numLocations).map (locOff I)

lemma locStart_eq (v : Fin I.numLocations) : locStart I v = locBase I + locOff I v := rfl

lemma locOff_zero : locOff I 0 = 0 := by simp [locOff]

lemma locOff_succ {j : ℕ} (hj : j < I.numLocations) :
    locOff I (j + 1) = locOff I j + locSize I ⟨j, hj⟩ := by
  rw [locOff, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [locOff]

lemma locOff_le (j : ℕ) : locOff I j ≤ 2 * (locsPre I j).length := by
  rw [locOff, locsPre, List.length_flatMap, ← List.sum_map_mul_left]
  exact List.sum_le_sum fun v _ => locSize_le I v

lemma locsPre_le (j : ℕ) : (locsPre I j).length ≤ H I := by
  have h1 := length_sd_le I
  rw [sd_eq, locsDesc_split I j] at h1
  simp only [List.length_cons, List.length_append] at h1
  omega

lemma locOff_le_H (j : ℕ) : locOff I j ≤ 2 * H I :=
  (locOff_le I j).trans (by have := locsPre_le I j; omega)

/-- The position of the schema descriptions in the input. -/
def schPos : ℕ := posAt I I.numLocations + (encodeNat I.schemas.length).length

lemma drop_posAt_W : (encodeSystem I).drop (posAt I I.numLocations) =
    encodeNat I.schemas.length ++ encodeNats (schsDesc I) := by
  rw [drop_posAt, locsSuf_all]; simp [encNats_cons]

lemma drop_schPos : (encodeSystem I).drop (schPos I) = encodeNats (schsDesc I) := by
  rw [schPos, ← List.drop_drop, drop_posAt_W, List.drop_left]

/-! ## `ℓ ≤ H` for nontrivial systems -/

lemma length_permDescription (π : BlockPerm k ℓ) :
    (permDescription π).length = k + k * ℓ := by
  simp [permDescription, blockDescription, List.length_flatMap, sum_map_const]

lemma length_schemaDescription_ge (hk : 1 ≤ k) (e : Schema k ℓ I.numLocations) :
    ℓ ≤ (schemaDescription e).length := by
  cases e with
  | binary u v D σ τ =>
    have := length_permDescription σ
    simp only [schemaDescription, List.length_append]
    nlinarith
  | ternary u v w' D σ τ π =>
    have := length_permDescription σ
    simp only [schemaDescription, List.length_append]
    nlinarith

lemma ell_le_H (hk : 1 ≤ k) (h : ¬ trivSys I) : ℓ ≤ H I := by
  have h2 := length_sd_le I
  rw [sd_eq] at h2
  simp only [List.length_cons, List.length_append] at h2
  by_cases hd : ∀ v, I.domain v = ∅
  · have hs : I.schemas ≠ [] := fun hs => h ⟨hd, hs⟩
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hs
    have h1 : (schemaDescription e).length ≤ (schsDesc I).length := by
      rw [schsDesc, List.length_flatMap]
      exact List.le_sum_of_mem (List.mem_map_of_mem he)
    have := length_schemaDescription_ge I hk e
    omega
  · push Not at hd
    obtain ⟨v, hv⟩ := hd
    have h1 : (locD I v).length ≤ (locsDesc I).length := by
      rw [locsDesc, List.length_flatMap]
      exact List.le_sum_of_mem (List.mem_map_of_mem (List.mem_finRange v))
    have hpos : 1 ≤ (coordList (I.domain v)).length := by
      rw [← card_image_coordNum]
      exact Nat.one_le_iff_ne_zero.mpr (fun h0 => (Finset.nonempty_iff_ne_empty.mp hv) ((card_image_eq_zero_iff).mp h0))
    have := length_flatten_cnd I v
    rw [locD_eq'] at h1
    simp only [List.length_cons] at h1
    nlinarith

open CStm

/-! ## The program -/

/-- Add the size of the current location to `rOff`. -/
def p1Add : CStm CR CQ :=
  .seq (.set rOff (.add (rv rOff) (rv rD)))
    (.ite (.lt (rv rA) (.const 1)) (.set rOff (.add (rv rOff) (rv rD))) .skip)

/-- The body of the location loop of `P1`. -/
def p1Body : CStm CR CQ :=
  .seq (rdNumS rA rP rT) (.seq (rdNumS rD rP rT) (.seq (.push qLoc (rv rOff))
    (.seq (skipBlocksS rD rL1 rK rI rT) (.seq p1Add (.set rJ (.add (rv rJ) (.const 1)))))))

/-- The location loop of `P1`. -/
def p1Loop : CStm CR CQ := .loop (.lt (rv rJ) (rv rW)) p1Body

/-- **Pass `P1`.** -/
def p1 : CStm CR CQ :=
  .seq .rst (.seq (skipNumS rT) (.seq (rdNumS rL rP rT)
    (.seq (.set rL1 (.add (rv rL) (.const 1))) (.seq (rdNumS rW rP rT)
      (.seq (.set rJ (.const 0)) (.seq (.set rOff (.const 0))
        (.seq p1Loop (rdNumS rE rP rT))))))))

/-- The size step. -/
lemma p1Add_good {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ)
    (hf : s.env rOff + 2 * s.env rD < 2 ^ w) (hA : s.env rA < 2 ^ w) :
    ∃ s', Good (encodeSystem I) w p1Add s s' (20 * Ex.nodeCost w) ∧
      s'.env rOff = s.env rOff + s.env rD + (if s.env rA < 1 then s.env rD else 0) ∧
      (∀ r, r ≠ rOff → s'.env r = s.env r) ∧ s'.stk = s.stk ∧ s'.pos = s.pos ∧
      s'.out = s.out := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have h1 := Good.set (x := encodeSystem I) (w := w) (r := rOff) (e := .add (rv rOff) (rv rD))
    (st := s) (by simp only [Ex.Fits, Ex.eval, rv]; omega)
  set s1 := s.set rOff (Ex.eval s.env (.add (rv rOff) (rv rD)))
  have e1 : ∀ r, s1.env r = Function.update s.env rOff (s.env rOff + s.env rD) r := fun _ => rfl
  have e1O : s1.env rOff = s.env rOff + s.env rD := by rw [e1, Function.update_self]
  have e1D : s1.env rD = s.env rD := by rw [e1, Function.update_of_ne (by decide)]
  have e1A : s1.env rA = s.env rA := by rw [e1, Function.update_of_ne (by decide)]
  have hcf : (Ex.lt (rv rA) (.const 1) : Ex CR).Fits w s1.env := by
    simp only [Ex.Fits, rv, e1A]; exact ⟨hA, Nat.one_lt_two_pow (by omega)⟩
  by_cases ha : s.env rA < 1
  · have h2 := Good.set (x := encodeSystem I) (w := w) (r := rOff)
      (e := .add (rv rOff) (rv rD)) (st := s1) (by simp only [Ex.Fits, Ex.eval, rv, e1O, e1D]; omega)
    refine ⟨_, (h1.seq (Good.iteT hcf (by simp [Ex.eval, rv, e1A, ha]) h2)).mono ?_, ?_,
      fun r hr => ?_, rfl, rfl, rfl⟩
    · simp only [condCost, Ex.size, rv]; nlinarith
    · simp [Ex.eval, rv, e1O, e1D, ha]
    · simp only [NSt.set_env, Function.update_of_ne hr]; rw [e1, Function.update_of_ne hr]
  · refine ⟨_, (h1.seq (Good.iteF hcf (by simp [Ex.eval, rv, e1A, ha]) Good.skip)).mono ?_, ?_,
      fun r hr => ?_, rfl, rfl, rfl⟩
    · simp only [condCost, Ex.size, rv]; nlinarith
    · rw [e1O, if_neg ha]; rfl
    · rw [e1, Function.update_of_ne hr]

/-- The loop invariant of `P1`. -/
def p1Inv (st s : NSt CR CQ) : Prop :=
  s.env rW = I.numLocations ∧ s.env rL = ℓ ∧ s.env rL1 = ℓ + 1 ∧
    s.env rJ ≤ I.numLocations ∧ s.pos = posAt I (s.env rJ) ∧
    s.env rOff = locOff I (s.env rJ) ∧
    s.stk = Function.update st.stk qLoc
      (((List.range (s.env rJ)).map (locOff I)).reverse ++ st.stk qLoc) ∧
    s.out = st.out

/-- One iteration of the location loop of `P1`. -/
lemma p1Body_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (st s : NSt CR CQ) (hI : p1Inv I st s) (hc : (Ex.lt (rv rJ) (rv rW)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p1Body s s'
        (100 * Ex.nodeCost w * ((H I - s.pos) - (H I - s'.pos)) + 200 * Ex.nodeCost w) ∧
      p1Inv I st s' ∧ I.numLocations - s'.env rJ < I.numLocations - s.env rJ ∧
      H I - s'.pos ≤ H I - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  obtain ⟨hW, hL, hL1, hjW, hpos, hoff, hstk, hout⟩ := hI
  have hlt : s.env rJ < I.numLocations := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hW]; rw [if_neg h]
  set j := s.env rJ with hjdef
  set v : Fin I.numLocations := ⟨j, hlt⟩
  set a := initNum (I.init v)
  set d := (coordList (I.domain v)).length
  set bs := (locNums I v).map (coordNumDescription ℓ)
  have hbsl : bs.length = d := by simp [bs, length_locNums, d]
  have hbsM : ∀ b ∈ bs, b.length = ℓ + 1 := by
    intro b hb
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
    simp [coordNumDescription]
  have hfl : bs.flatten.length = d * (ℓ + 1) := length_flatten_cnd I v
  set rest := encodeNats (locsSuf I (j + 1) ++ I.schemas.length :: schsDesc I)
  have hx : (encodeSystem I).drop s.pos =
      encodeNat a ++ (encodeNat d ++ (encodeNats bs.flatten ++ rest)) := by
    rw [hpos, drop_posAt, locsSuf_cons I hlt, locD_eq', List.append_assoc, List.cons_append,
      List.cons_append, encNats_cons, encNats_cons, encodeNats_append]
  have hposle : s.pos ≤ H I := by rw [hpos]; exact posAt_le I j
  have hlenx : s.pos + (encodeNat a).length + (encodeNat d).length +
      (encodeNats bs.flatten).length ≤ H I := by
    have := congrArg List.length hx
    simp only [List.length_drop, List.length_append] at this
    have : s.pos ≤ (encodeSystem I).length := hposle
    show _ ≤ (encodeSystem I).length
    omega
  have hdf : d ≤ (encodeNats bs.flatten).length :=
    le_trans (by rw [hfl]; nlinarith) (length_le_encodeNats _)
  have hdH : d ≤ H I := by omega
  have ha2 : a ≤ 2 := initNum_le _
  have ha : (Nat.bits a).length < w := bits_lt_of_le (le_trans ha2
    (by have := three_le_H I; omega)) hH2
  have hd : (Nat.bits d).length < w := bits_lt_of_le hdH hH2
  -- reading `ι(v)` and `|D_v|`
  have r1 := rdNumS_good (Q := CQ) hw (r := rA) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s a _ hx ha
  set s1 := rdNumFinal s rA rP rT a
  have hx2 : (encodeSystem I).drop s1.pos = encodeNat d ++ (encodeNats bs.flatten ++ rest) := by
    simp only [s1, rdNumFinal_pos]
    rw [← List.drop_drop, hx, List.drop_left]
  have r2 := rdNumS_good (Q := CQ) hw (r := rD) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s1 d _ hx2 hd
  set s2 := rdNumFinal s1 rD rP rT d
  have e2 : ∀ q, q ≠ rD → q ≠ rA → q ≠ rP → q ≠ rT → s2.env q = s.env q := by
    intro q h1 h2 h3 h4
    rw [rdNumFinal_env_ne h1 h3 h4, rdNumFinal_env_ne h2 h3 h4]
  have e2D : s2.env rD = d := rdNumFinal_env_r (by decide) (by decide) d
  have e2A : s2.env rA = a := by
    rw [rdNumFinal_env_ne (by decide) (by decide) (by decide)]
    exact rdNumFinal_env_r (by decide) (by decide) a
  have e2O : s2.env rOff = locOff I j := by
    rw [e2 rOff (by decide) (by decide) (by decide) (by decide), hoff]
  have hp2 : s2.pos = s.pos + (encodeNat a).length + (encodeNat d).length := rfl
  -- pushing the offset
  have hoffH := locOff_le_H I (j + 1)
  have hsz : locOff I (j + 1) = locOff I j + d + (if a < 1 then d else 0) := by
    rw [locOff_succ I hlt, locSize_eq]; ring
  have r3 := Good.push (x := encodeSystem I) (w := w) (q := qLoc) (e := rv rOff) (st := s2)
    (by simp only [Ex.Fits, rv, e2O]; split_ifs at hsz <;> omega)
  set s3 := s2.setS qLoc ((rv rOff : Ex CR).eval s2.env :: s2.stk qLoc)
  -- skipping the coordinates
  have hx3 : (encodeSystem I).drop s3.pos = encodeNats bs.flatten ++ rest := by
    show (encodeSystem I).drop s2.pos = _
    simp only [s2, rdNumFinal_pos]
    rw [← List.drop_drop, hx2, List.drop_left]
  obtain ⟨s4, r4, hs4, hp4, ho4, hf4⟩ := skipBlocksS_good (Q := CQ) hw (d := rD) (m := rL1)
    (j := rK) (i := rI) (t := rT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s3 bs (ℓ + 1) hbsM rest hx3
    (by rw [hbsl]; exact e2D)
    (by show s2.env rL1 = _; rw [e2 rL1 (by decide) (by decide) (by decide) (by decide), hL1])
    (by rw [hbsl]; omega) (by omega)
  have e4 : ∀ q, q ≠ rK → q ≠ rI → q ≠ rT → s4.env q = s2.env q := fun q h1 h2 h3 =>
    hf4 q h1 h2 h3
  -- adding the size
  obtain ⟨s5, r5, e5O, e5, hs5, hp5, ho5⟩ := p1Add_good I hw s4
    (by rw [e4 _ (by decide) (by decide) (by decide), e4 _ (by decide) (by decide) (by decide),
      e2O, e2D]; split_ifs at hsz <;> omega)
    (by rw [e4 _ (by decide) (by decide) (by decide), e2A]; omega)
  have e5J : s5.env rJ = j := by
    rw [e5 _ (by decide), e4 _ (by decide) (by decide) (by decide),
      e2 _ (by decide) (by decide) (by decide) (by decide)]
  have r6 := Good.set (x := encodeSystem I) (w := w) (r := rJ) (e := .add (rv rJ) (.const 1))
    (st := s5) (by
      have := W_le I
      simp only [Ex.Fits, Ex.eval, rv, e5J]; omega)
  have e6 : ∀ q, (s5.set rJ (Ex.eval s5.env (.add (rv rJ) (.const 1)))).env q =
      Function.update s5.env rJ (j + 1) q := by
    intro q; simp [Ex.eval, rv, e5J]
  have e6J : (s5.set rJ (Ex.eval s5.env (.add (rv rJ) (.const 1)))).env rJ = j + 1 := by
    rw [e6, Function.update_self]
  have back : ∀ q, q ≠ rJ → q ≠ rOff → q ≠ rK → q ≠ rI → q ≠ rT → q ≠ rD → q ≠ rA →
      q ≠ rP → (s5.set rJ (Ex.eval s5.env (.add (rv rJ) (.const 1)))).env q = s.env q := by
    intro q h1 h2 h3 h4 h5 h6 h7 h8
    rw [e6, Function.update_of_ne h1, e5 q h2, e4 q h3 h4 h5, e2 q h6 h7 h8 h5]
  have hp6 : (s5.set rJ (Ex.eval s5.env (.add (rv rJ) (.const 1)))).pos =
      s.pos + (encodeNat a).length + (encodeNat d).length + (encodeNats bs.flatten).length := by
    rw [NSt.set_pos, hp5, hp4]; rfl
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ?_, ?_⟩
  · rw [hp6]
    have hΔ : H I - s.pos - (H I - (s.pos + (encodeNat a).length + (encodeNat d).length +
        (encodeNats bs.flatten).length)) = (encodeNat a).length + (encodeNat d).length +
        (encodeNats bs.flatten).length := by omega
    rw [hΔ, hbsl]
    simp only [Ex.size, rv]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNat a).length = la at *
    generalize (encodeNat d).length = ld at *
    generalize (encodeNats bs.flatten).length = lf at *
    have := Nat.mul_le_mul_left N hdf
    nlinarith only [hU, hU', this]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hW]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hL]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hL1]
  · rw [e6J]; omega
  · rw [e6J, hp6, hpos, posAt_succ I hlt, locD_eq']
    simp only [encNats_cons, List.length_append]; ring
  · rw [e6J, e6, Function.update_of_ne (by decide), e5O,
      e4 _ (by decide) (by decide) (by decide), e4 _ (by decide) (by decide) (by decide),
      e4 _ (by decide) (by decide) (by decide), e2O, e2D, e2A, hsz]
  · rw [NSt.set_stk, hs5, hs4]
    show Function.update s2.stk qLoc (s2.env rOff :: s2.stk qLoc) = _
    rw [e2O]
    have : s2.stk = s.stk := rfl
    rw [this, hstk, e6J, List.range_succ, List.map_append,
      List.reverse_append]
    funext q
    by_cases hq : q = qLoc
    · subst hq; simp
    · simp [Function.update_of_ne hq]
  · rw [NSt.set_out, ho5, ho4]; exact hout
  · rw [e6J]; omega
  · rw [hp6]; omega

/-- **Pass `P1`.** For `ℓ ≤ H` and any start state, `P1` ends after `E` (at `schPos I`) with
`W, ℓ, E` and the total offset `locOff I W` in registers and the offsets of the locations
pushed onto `qLoc` (the last on top); the other stacks and the output are kept. -/
theorem p1_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (st : NSt CR CQ) (hp : st.pos ≤ H I) :
    ∃ st', Good (encodeSystem I) w p1 st st' (500 * (H I + 1) * Ex.nodeCost w) ∧
      st'.stk = Function.update st.stk qLoc ((locOffs I).reverse ++ st.stk qLoc) ∧
      st'.out = st.out ∧ st'.pos = schPos I ∧ st'.env rW = I.numLocations ∧
      st'.env rL = ℓ ∧ st'.env rE = I.schemas.length ∧
      st'.env rOff = locOff I I.numLocations := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  have hWH := W_le I
  have hEH := E_le I
  have r0 := Good.rst (x := encodeSystem I) (w := w) (st := st)
  set s0 : NSt CR CQ := { st with pos := 0 }
  have r1 := skipNumS_good (Q := CQ) hw (t := rT) s0 k _ (drop_zero_k I)
  set s1 := skipNumFinal s0 rT k
  have r2 := rdNumS_good (Q := CQ) hw (r := rL) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s1 ℓ _ (by show (encodeSystem I).drop (0 + _) = _; rw [zero_add]; exact drop_ell I)
    (bits_lt_of_le hℓ hH2)
  set s2 := rdNumFinal s1 rL rP rT ℓ
  have e2 : s2.env rL = ℓ := rdNumFinal_env_r (by decide) (by decide) _
  have r3 := Good.set (x := encodeSystem I) (w := w) (r := rL1) (e := .add (rv rL) (.const 1))
    (st := s2) (by simp only [Ex.Fits, Ex.eval, rv, e2]; omega)
  set s3 := s2.set rL1 (Ex.eval s2.env (.add (rv rL) (.const 1)))
  have r4 := rdNumS_good (Q := CQ) hw (r := rW) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s3 I.numLocations _
    (by show (encodeSystem I).drop (0 + (encodeNat k).length + (encodeNat ℓ).length) = _
        rw [zero_add]; exact drop_W I) (bits_lt_of_le hWH hH2)
  set s4 := rdNumFinal s3 rW rP rT I.numLocations
  have r5 := Good.set (x := encodeSystem I) (w := w) (r := rJ) (e := .const 0) (st := s4)
    (by simp only [Ex.Fits]; omega)
  set s5 := s4.set rJ (Ex.eval s4.env (.const 0))
  have r6 := Good.set (x := encodeSystem I) (w := w) (r := rOff) (e := .const 0) (st := s5)
    (by simp only [Ex.Fits]; omega)
  set s6 := s5.set rOff (Ex.eval s5.env (.const 0))
  have e6 : ∀ q, s6.env q = Function.update (Function.update s4.env rJ 0) rOff 0 q :=
    fun _ => rfl
  have e4 : ∀ q, q ≠ rW → q ≠ rP → q ≠ rT → s4.env q = s3.env q := fun q h1 h2 h3 =>
    rdNumFinal_env_ne h1 h2 h3 _
  have e3 : s3.env rL1 = ℓ + 1 := by
    show Function.update s2.env rL1 (Ex.eval s2.env (.add (rv rL) (.const 1))) rL1 = ℓ + 1
    rw [Function.update_self]; simp only [Ex.eval, rv, e2]
  have e3L : s3.env rL = ℓ := by
    show Function.update s2.env rL1 (Ex.eval s2.env (.add (rv rL) (.const 1))) rL = ℓ
    rw [Function.update_of_ne (by decide), e2]
  have hp6 : s6.pos = posAt I 0 := by
    show 0 + (encodeNat k).length + (encodeNat ℓ).length + (encodeNat I.numLocations).length = _
    rw [posAt_zero]; ring
  have e6J : s6.env rJ = 0 := by
    rw [e6, Function.update_of_ne (by decide), Function.update_self]
  have hI6 : p1Inv I st s6 := by
    refine ⟨?_, ?_, ?_, by rw [e6J]; omega, by rw [e6J, hp6], ?_, ?_, rfl⟩
    · rw [e6, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      exact rdNumFinal_env_r (by decide) (by decide) _
    · rw [e6, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        e4 _ (by decide) (by decide) (by decide), e3L]
    · rw [e6, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        e4 _ (by decide) (by decide) (by decide), e3]
    · rw [e6J, locOff_zero, e6, Function.update_self]
    · rw [e6J]; simp only [List.range_zero, List.map_nil, List.reverse_nil, List.nil_append,
        Function.update_eq_self]; rfl
  -- the loop
  obtain ⟨s7, r7, hI7, hc7⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rW)) (body := p1Body) (p1Inv I st)
    (fun s => I.numLocations - s.env rJ) (fun s => H I - s.pos) (100 * Ex.nodeCost w)
    (200 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hW, -, -, hj, -⟩ := hI
      simp only [Ex.Fits, rv, hW]; omega, fun hc => p1Body_good I hw hH hℓ st s hI hc⟩) s6 hI6
  obtain ⟨hW7, hL7, -, hj7, hpos7, hoff7, hstk7, hout7⟩ := hI7
  have hj : s7.env rJ = I.numLocations := by
    simp only [Ex.eval, rv, hW7] at hc7; split_ifs at hc7 with h <;> omega
  have r8 := rdNumS_good (Q := CQ) hw (r := rE) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s7 I.schemas.length _ (by rw [hpos7, hj]; exact drop_posAt_W I)
    (bits_lt_of_le hEH hH2)
  refine ⟨_, (r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8)))))))).mono ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hlen : (encodeNat k).length + (encodeNat ℓ).length +
        (encodeNat I.numLocations).length ≤ H I := by rw [← posAt_zero]; exact posAt_le I 0
    have hlE : (encodeNat I.schemas.length).length ≤ H I := by
      have := congrArg List.length (drop_posAt_W I)
      simp only [List.length_drop, List.length_append] at this
      show _ ≤ (encodeSystem I).length; omega
    have hφ : H I - s6.pos ≤ H I := by omega
    have hμ : I.numLocations - s6.env rJ ≤ H I := by omega
    simp only [condCost, Ex.size, rv] at *
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize H I - s6.pos = φ at *
    generalize I.numLocations - s6.env rJ = μ at *
    generalize (encodeNat k).length = lk at *
    generalize (encodeNat ℓ).length = ll at *
    generalize (encodeNat I.numLocations).length = lW at *
    generalize (encodeNat I.schemas.length).length = lE at *
    generalize st.pos = p at *
    generalize H I = h at *
    nlinarith
  · rw [rdNumFinal_stk, hstk7, hj]; rfl
  · rw [rdNumFinal_out, hout7]
  · rw [rdNumFinal_pos, hpos7, hj]; rfl
  · rw [rdNumFinal_env_ne (by decide) (by decide) (by decide), hW7]
  · rw [rdNumFinal_env_ne (by decide) (by decide) (by decide), hL7]
  · exact rdNumFinal_env_r (by decide) (by decide) _
  · rw [rdNumFinal_env_ne (by decide) (by decide) (by decide), hoff7, hj]

/-! ## The coordinate numbers of a domain are increasing in `coordList` -/

lemma blockNum_cons {ℓ : ℕ} (a : ZMod 2) (b : BlockCoord ℓ) :
    blockNum (Fin.cons a b : BlockCoord (ℓ + 1)) = a.val + 2 * blockNum b := by
  simp only [blockNum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero,
    mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => by ring

lemma flatMap_range_pairs : ∀ n : ℕ,
    (List.range n).flatMap (fun r => [2 * r, 2 * r + 1]) = List.range (2 * n)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_pairs n,
      show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ]
    simp

lemma map_blockNum_allBlockCoords : ∀ ℓ : ℕ,
    (allBlockCoords ℓ).map blockNum = List.range (2 ^ ℓ)
  | 0 => by simp [allBlockCoords, blockNum]
  | ℓ + 1 => by
    rw [allBlockCoords, List.map_flatMap]
    have : (fun b : BlockCoord ℓ => ([Fin.cons 0 b, Fin.cons 1 b] : List (BlockCoord (ℓ + 1))).map
        blockNum) = (fun r => [2 * r, 2 * r + 1]) ∘ blockNum := by
      funext b
      simp only [List.map_cons, List.map_nil, Function.comp_apply, blockNum_cons]
      simp [ZMod.val_one]; omega
    have e : ((allBlockCoords ℓ).map blockNum).flatMap (fun r => [2 * r, 2 * r + 1]) =
        (allBlockCoords ℓ).flatMap ((fun r => [2 * r, 2 * r + 1]) ∘ blockNum) := by
      rw [List.flatMap_map]; rfl
    rw [this, ← e, map_blockNum_allBlockCoords ℓ, flatMap_range_pairs, pow_succ, mul_comm]

lemma pairwise_map_coordNum_allCoords {k ℓ : ℕ} :
    ((allCoords k ℓ).map coordNum).Pairwise (· < ·) := by
  rw [allCoords, List.map_flatMap, List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.map_map]
    have : (coordNum ∘ fun b => ((i, b) : Coord k ℓ)) = (fun r => (i : ℕ) * 2 ^ ℓ + r) ∘
        blockNum := by funext b; rfl
    rw [this, ← List.map_map, map_blockNum_allBlockCoords, List.pairwise_map]
    exact List.pairwise_lt_range.imp (by omega)
  · refine (List.pairwise_lt_finRange k).imp fun {i i'} h => ?_
    intro x hx y hy
    simp only [List.map_map, List.mem_map] at hx hy
    obtain ⟨b, -, rfl⟩ := hx
    obtain ⟨b', -, rfl⟩ := hy
    simp only [Function.comp_apply, coordNum]
    have hb : blockNum b < 2 ^ ℓ := by rw [blockNum_eq_regVal]; exact regVal_lt b
    have hi : (i : ℕ) + 1 ≤ i' := h
    nlinarith

/-- **The sorted coordinate numbers** are the numbers of `coordList`. -/
theorem locNums_eq (v : Fin I.numLocations) :
    locNums I v = (coordList (I.domain v)).map coordNum := by
  have hpw : ((coordList (I.domain v)).map coordNum).Pairwise (· < ·) :=
    pairwise_map_coordNum_allCoords.sublist ((List.filter_sublist).map _)
  have hfs : ((coordList (I.domain v)).map coordNum).toFinset = (I.domain v).image coordNum := by
    ext n; simp
  rw [locNums, ← hfs]
  exact (List.toFinset_sort _ hpw.nodup).mpr (hpw.imp le_of_lt)

end Lax119563Proofs.Compiler

end Compiler_PLoc

/-! ### Formerly `Lax119563Proofs.Compiler.PRec` -/

section Compiler_PRec

/-!
# Pass `P1'` of the compiler program: the location records

`p1r` (systems with a schema, where `k ≤ H`), run after `p1` (it uses `rW = W` and
`rL1 = ℓ + 1`), rewinds the input and pushes, for every location `v` and every coordinate of
`D_v` (in increasing order of their numbers, the `r`-th one with number `n`), the record
`locRec I v r = v :: i :: b₀ … b_{ℓ-1} ++ [locOff I v + r · |labs v|, |labs v|]`
(`i, b₀ … b_{ℓ-1}` = `coordNumDescription ℓ n`) onto the stack `qRec` (`p1r_good`); the
record ends with the offset of the coordinate class from `locBase` and its number of labels.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-- The number of labels of the current location. -/
def rLab : Fin CR := 14
/-- The value register of the record reader. -/
def rV : Fin CR := 15
/-- The location records. -/
def qRec : Fin CQ := 1
/-- `k` (read by `P1'`). -/
def rKk : Fin CR := 16
/-- The number of location records (computed by `P1'`). -/
def rCnt : Fin CR := 36

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## The records -/

/-- The number of labels of the coordinate classes of `v`. -/
def labsN (v : Fin I.numLocations) : ℕ := (coordLabs I v).length

lemma labsN_eq (v : Fin I.numLocations) :
    labsN I v = 1 + (if initNum (I.init v) < 1 then 1 else 0) := by
  unfold labsN coordLabs
  rcases h : I.init v with _ | b <;> simp [initNum, bits1]

/-- The record of the `r`-th coordinate of location `v`. -/
noncomputable def locRec (v : Fin I.numLocations) (r : ℕ) : List ℕ :=
  (v : ℕ) :: (coordNumDescription ℓ ((locNums I v).getD r 0) ++
    [0, locOff I v + r * labsN I v, labsN I v, initNum (I.init v)])

/-- The records of location `v`. -/
noncomputable def recsV (v : Fin I.numLocations) : List (List ℕ) :=
  (List.range (coordList (I.domain v)).length).map (locRec I v)

/-- The records of the first `j` locations. -/
noncomputable def recsUpTo (j : ℕ) : List (List ℕ) :=
  ((List.finRange I.numLocations).take j).flatMap (recsV I)

/-- All location records. -/
noncomputable def locRecs : List (List ℕ) := (List.finRange I.numLocations).flatMap (recsV I)

lemma recsUpTo_succ {j : ℕ} (hj : j < I.numLocations) :
    recsUpTo I (j + 1) = recsUpTo I j ++ recsV I ⟨j, hj⟩ := by
  rw [recsUpTo, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [recsUpTo]

lemma recsUpTo_all : recsUpTo I I.numLocations = locRecs I := by
  rw [recsUpTo, locRecs, List.take_of_length_le (by simp)]

lemma recsV_take_succ (v : Fin I.numLocations) {r : ℕ} (hr : r < (coordList (I.domain v)).length) :
    (recsV I v).take (r + 1) = (recsV I v).take r ++ [locRec I v r] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa [recsV] using hr)]
  simp [recsV]

/-! ## Sizes -/

lemma k_le_H (h : I.schemas ≠ []) : k ≤ H I := by
  have h2 := length_sd_le I
  rw [sd_eq] at h2
  simp only [List.length_cons, List.length_append] at h2
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ h
  have h1 : (schemaDescription e).length ≤ (schsDesc I).length := by
    rw [schsDesc, List.length_flatMap]
    exact List.le_sum_of_mem (List.mem_map_of_mem he)
  have : k ≤ (schemaDescription e).length := by
    cases e with
    | binary u v D σ τ =>
      have := length_permDescription σ
      simp only [schemaDescription, List.length_append]; omega
    | ternary u v w' D σ τ π =>
      have := length_permDescription σ
      simp only [schemaDescription, List.length_append]; omega
  omega

lemma coordNum_div (c : Coord k ℓ) : coordNum c / 2 ^ ℓ = c.1 := by
  obtain ⟨i, b⟩ := c
  simp only [coordNum, blockNum_eq_regVal]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (regVal_lt b),
    zero_add]

lemma cnd_le {v : Fin I.numLocations} {n : ℕ} (hn : n ∈ locNums I v) {m : ℕ}
    (hm : m ∈ coordNumDescription ℓ n) : m < k ∨ m ≤ 1 := by
  rw [locNums, Finset.mem_sort, Finset.mem_image] at hn
  obtain ⟨c, -, rfl⟩ := hn
  simp only [coordNumDescription, List.mem_cons, List.mem_map, List.mem_range] at hm
  rcases hm with rfl | ⟨t, -, rfl⟩
  · rw [coordNum_div]; left; exact c.1.2
  · right; split_ifs <;> omega

lemma length_cnd (n : ℕ) : (coordNumDescription ℓ n).length = ℓ + 1 := by
  simp [coordNumDescription]

open CStm

/-! ## The program -/

/-- One coordinate: push its record. -/
def p1rIn : CStm CR CQ :=
  .seq (.push qRec (rv rJ)) (.seq (rdNumsS qRec rL1 rI rV rP rT) (.seq (.push qRec (.const 0))
    (.seq (.push qRec (rv rOff)) (.seq (.push qRec (rv rLab)) (.seq (.push qRec (rv rA))
      (.seq (.set rOff (.add (rv rOff) (rv rLab))) (.set rK (.add (rv rK) (.const 1)))))))))

/-- The coordinate loop. -/
def p1rCoords : CStm CR CQ := .loop (.lt (rv rK) (rv rD)) p1rIn

/-- One location. -/
def p1rBody : CStm CR CQ :=
  .seq (rdNumS rA rP rT) (.seq (rdNumS rD rP rT)
    (.seq (.set rLab (.add (.const 1) (.lt (rv rA) (.const 1))))
      (.seq (.set rK (.const 0)) (.seq p1rCoords (.seq (.set rCnt (.add (rv rCnt) (rv rD)))
        (.set rJ (.add (rv rJ) (.const 1))))))))

/-- **Pass `P1'`.** -/
def p1r : CStm CR CQ :=
  .seq .rst (.seq (rdNumS rKk rP rT) (.seq (skipNumS rT) (.seq (skipNumS rT)
    (.seq (.set rJ (.const 0)) (.seq (.set rOff (.const 0)) (.seq (.set rCnt (.const 0))
      (.loop (.lt (rv rJ) (rv rW)) p1rBody)))))))

/-- The invariant of the coordinate loop of location `v` (coordinates from position `B`,
stacks `S0`, output `O`). -/
def p1rInInv (v : Fin I.numLocations) (B : ℕ) (S0 : Fin CQ → List ℕ) (O : List ℕ)
    (s : NSt CR CQ) : Prop :=
  s.env rK ≤ (coordList (I.domain v)).length ∧ s.env rD = (coordList (I.domain v)).length ∧
    s.env rJ = v ∧ s.env rL1 = ℓ + 1 ∧ s.env rLab = labsN I v ∧
    s.env rA = initNum (I.init v) ∧ s.env rW = I.numLocations ∧
    s.env rOff = locOff I v + s.env rK * labsN I v ∧
    s.pos = B + (encodeNats
      (((locNums I v).map (coordNumDescription ℓ)).take (s.env rK)).flatten).length ∧
    s.stk = Function.update S0 qRec
      (((recsV I v).take (s.env rK)).flatten.reverse ++ S0 qRec) ∧ s.out = O

set_option maxHeartbeats 800000 in
/-- One coordinate. -/
lemma p1rIn_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hkH : k ≤ H I)
    (hℓ : ℓ ≤ H I) (v : Fin I.numLocations) (B : ℕ) (S0 : Fin CQ → List ℕ) (O : List ℕ)
    (rest : List Bool)
    (hx : (encodeSystem I).drop B =
      encodeNats ((locNums I v).map (coordNumDescription ℓ)).flatten ++ rest)
    (hoff : locOff I (v.val + 1) ≤ 2 * H I)
    (s : NSt CR CQ) (hI : p1rInInv I v B S0 O s) (hc : (Ex.lt (rv rK) (rv rD)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p1rIn s s'
        (60 * Ex.nodeCost w * ((B + (encodeNats ((locNums I v).map
            (coordNumDescription ℓ)).flatten).length - s.pos) -
          (B + (encodeNats ((locNums I v).map (coordNumDescription ℓ)).flatten).length -
            s'.pos)) + 100 * Ex.nodeCost w) ∧
      p1rInInv I v B S0 O s' ∧
      (coordList (I.domain v)).length - s'.env rK < (coordList (I.domain v)).length - s.env rK ∧
      B + (encodeNats ((locNums I v).map (coordNumDescription ℓ)).flatten).length - s'.pos ≤
        B + (encodeNats ((locNums I v).map (coordNumDescription ℓ)).flatten).length - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨hK, hD, hJ, hL1, hLab, hA, hW, hO, hpos, hstk, hout⟩ := hI
  set d := (coordList (I.domain v)).length
  set bs := (locNums I v).map (coordNumDescription ℓ)
  have hbsl : bs.length = d := by simp [bs, length_locNums, d]
  have hlt : s.env rK < d := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hD]; rw [if_neg h]
  set r := s.env rK with hr
  have hrb : r < bs.length := by omega
  have hrn : r < (locNums I v).length := by rw [length_locNums]; exact hlt
  have hsplit : bs.flatten = (bs.take r).flatten ++ (bs[r] ++ (bs.drop (r + 1)).flatten) := by
    have e := List.take_append_drop r bs
    rw [List.drop_eq_getElem_cons hrb] at e
    conv_lhs => rw [← e]
    simp only [List.flatten_append, List.flatten_cons]
  have hgd : (locNums I v).getD r 0 = (locNums I v)[r] := List.getD_eq_getElem _ _ hrn
  have hvs' : bs[r] = coordNumDescription ℓ ((locNums I v).getD r 0) := by
    simp only [bs, List.getElem_map, hgd]
  set vs := bs[r]
  have hvs : vs = coordNumDescription ℓ ((locNums I v).getD r 0) := hvs'
  have hvl : vs.length = ℓ + 1 := by rw [hvs, length_cnd]
  have hxj : (encodeSystem I).drop s.pos = encodeNats vs ++
      (encodeNats (bs.drop (r + 1)).flatten ++ rest) := by
    rw [hpos, drop_add, hx, hsplit, encodeNats_append, encodeNats_append, List.append_assoc,
      List.drop_left, List.append_assoc]
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  have h3 := three_le_H I
  have hvsw : ∀ m ∈ vs, (Nat.bits m).length < w := by
    intro m hm
    rw [hvs] at hm
    have hmem : (locNums I v).getD r 0 ∈ locNums I v := by rw [hgd]; exact List.getElem_mem hrn
    refine bits_lt_of_le ?_ hH2
    rcases cnd_le I hmem hm with h | h <;> omega
  -- push `v`
  have r1 := Good.push (x := encodeSystem I) (w := w) (q := qRec) (e := rv rJ) (st := s)
    (by simp only [Ex.Fits, rv, hJ]; have := W_le I; omega)
  set s1 := s.setS qRec ((rv rJ : Ex CR).eval s.env :: s.stk qRec)
  have hx1 : (encodeSystem I).drop s1.pos = encodeNats vs ++
      (encodeNats (bs.drop (r + 1)).flatten ++ rest) := hxj
  -- read the coordinate
  obtain ⟨r2, hs2, hp2, ho2, he2⟩ := rdNumsS_good (Q := CQ) (x := encodeSystem I) hw
    (q := qRec) (n := rL1) (i := rI) (r := rV) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) s1 vs _ hx1 (by rw [hvl]; exact hL1) (by rw [hvl]; omega) hvsw
  set s2 := rnsSt s1 qRec rI rV rP rT vs vs.length
  have e2 : ∀ q, q ≠ rI → q ≠ rV → q ≠ rP → q ≠ rT → s2.env q = s.env q :=
    fun q h1 h2 h3 h4 => he2 q h1 h2 h3 h4
  have e2O : s2.env rOff = locOff I v + r * labsN I v := by
    rw [e2 _ (by decide) (by decide) (by decide) (by decide), hO]
  have e2L : s2.env rLab = labsN I v := by
    rw [e2 _ (by decide) (by decide) (by decide) (by decide), hLab]
  have hlabs : labsN I v ≤ 2 := by rw [labsN_eq]; split_ifs <;> omega
  have hoffr : locOff I v + (r + 1) * labsN I v ≤ 2 * H I := by
    refine le_trans ?_ hoff
    rw [locOff_succ I v.2]
    have : locSize I v = d * labsN I v := rfl
    rw [this]; nlinarith
  have e2A : s2.env rA = initNum (I.init v) := by
    rw [e2 _ (by decide) (by decide) (by decide) (by decide), hA]
  -- push the tag, the offset, the labels and `ι`
  have r3a := Good.push (x := encodeSystem I) (w := w) (q := qRec) (e := .const 0) (st := s2)
    (by simp only [Ex.Fits]; omega)
  set s2a := s2.setS qRec ((Ex.const 0 : Ex CR).eval s2.env :: s2.stk qRec)
  have r3 := Good.push (x := encodeSystem I) (w := w) (q := qRec) (e := rv rOff) (st := s2a)
    (by show s2.env rOff < 2 ^ w; rw [e2O]; nlinarith)
  set s3 := s2a.setS qRec ((rv rOff : Ex CR).eval s2a.env :: s2a.stk qRec)
  have r4 := Good.push (x := encodeSystem I) (w := w) (q := qRec) (e := rv rLab) (st := s3)
    (by show s2.env rLab < 2 ^ w; rw [e2L]; omega)
  set s4a := s3.setS qRec ((rv rLab : Ex CR).eval s3.env :: s3.stk qRec)
  have r4a := Good.push (x := encodeSystem I) (w := w) (q := qRec) (e := rv rA) (st := s4a)
    (by show s2.env rA < 2 ^ w; rw [e2A]; have := initNum_le (I.init v); omega)
  set s4 := s4a.setS qRec ((rv rA : Ex CR).eval s4a.env :: s4a.stk qRec)
  have r5 := Good.set (x := encodeSystem I) (w := w) (r := rOff) (e := .add (rv rOff) (rv rLab))
    (st := s4) (by
      show s2.env rOff < 2 ^ w ∧ s2.env rLab < 2 ^ w ∧ s2.env rOff + s2.env rLab < 2 ^ w
      rw [e2O, e2L]; refine ⟨by nlinarith, by omega, by nlinarith⟩)
  set s5 := s4.set rOff (Ex.eval s4.env (.add (rv rOff) (rv rLab)))
  have e5 : ∀ q, s5.env q = Function.update s2.env rOff
      (locOff I v + r * labsN I v + labsN I v) q := by
    intro q; simp only [s5, s4, s4a, s3, s2a, NSt.set_env, NSt.setS_env, Ex.eval, rv, e2O, e2L]
  have e5K : s5.env rK = r := by
    rw [e5, Function.update_of_ne (by decide), e2 _ (by decide) (by decide) (by decide)
      (by decide)]
  have r6 := Good.set (x := encodeSystem I) (w := w) (r := rK) (e := .add (rv rK) (.const 1))
    (st := s5) (by
      have hdH : d ≤ H I := by
        show (coordList (I.domain v)).length ≤ H I
        rw [← card_image_coordNum]; exact card_le I v
      simp only [Ex.Fits, Ex.eval, rv, e5K]; omega)
  set s6 := s5.set rK (Ex.eval s5.env (.add (rv rK) (.const 1)))
  have e6 : ∀ q, s6.env q = Function.update (Function.update s2.env rOff
      (locOff I v + r * labsN I v + labsN I v)) rK (r + 1) q := by
    intro q; simp only [s6, NSt.set_env, Ex.eval, rv, e5K]
    by_cases h : q = rK
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne h, e5]
  have e6K : s6.env rK = r + 1 := by rw [e6, Function.update_self]
  have back : ∀ q, q ≠ rK → q ≠ rOff → q ≠ rI → q ≠ rV → q ≠ rP → q ≠ rT →
      s6.env q = s.env q := by
    intro q h1 h2 h3 h4 h5 h6
    rw [e6, Function.update_of_ne h1, Function.update_of_ne h2, e2 q h3 h4 h5 h6]
  have hp6 : s6.pos = s.pos + (encodeNats vs).length := by
    show s2.pos = _; rw [hp2]; rfl
  have hlen : (encodeNats (bs.take (r + 1)).flatten).length =
      (encodeNats (bs.take r).flatten).length + (encodeNats vs).length := by
    rw [List.take_add_one, List.getElem?_eq_getElem hrb]
    simp only [Option.toList_some, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, encodeNats_append, List.length_append] <;> rfl
  have hle : (encodeNats (bs.take (r + 1)).flatten).length ≤ (encodeNats bs.flatten).length := by
    conv_rhs => rw [← List.take_append_drop (r + 1) bs]
    rw [List.flatten_append, encodeNats_append, List.length_append]; omega
  have hvle : ℓ + 1 ≤ (encodeNats vs).length := by rw [← hvl]; exact length_le_encodeNats _
  refine ⟨s6, (r1.seq (r2.seq (r3a.seq (r3.seq (r4.seq (r4a.seq (r5.seq r6))))))).mono ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hp6]
    have hΔ : B + (encodeNats bs.flatten).length - s.pos -
        (B + (encodeNats bs.flatten).length - (s.pos + (encodeNats vs).length)) =
        (encodeNats vs).length := by omega
    rw [hΔ, hvl]
    simp only [Ex.size, rv]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNats vs).length = lv at *
    have := Nat.mul_le_mul_left N hvle
    nlinarith only [hU, hU', this]
  · rw [e6K]; omega
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hD]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hJ]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hL1]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hLab]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hA]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hW]
  · rw [e6K, e6, Function.update_of_ne (by decide), Function.update_self]; ring
  · rw [e6K, hp6, hpos, hlen]; ring
  · show Function.update s4a.stk qRec (Ex.eval s4a.env (rv rA) :: s4a.stk qRec) = _
    have hl : Ex.eval s4a.env (rv rA) = initNum (I.init v) := e2A
    rw [hl]
    have h3s : s4a.stk qRec = labsN I v :: (locOff I v + r * labsN I v) :: 0 :: s2.stk qRec := by
      show Function.update s3.stk qRec _ qRec = _
      rw [Function.update_self]; show s2.env rLab :: _ = _; rw [e2L]
      show _ :: Function.update s2a.stk qRec _ qRec = _
      rw [Function.update_self]; show _ :: s2.env rOff :: _ = _; rw [e2O]
      show _ :: _ :: Function.update s2.stk qRec _ qRec = _
      rw [Function.update_self]; rfl
    have hs1 : s1.stk = Function.update s.stk qRec (v.val :: s.stk qRec) := by
      show Function.update s.stk qRec (s.env rJ :: s.stk qRec) = _; rw [hJ]
    rw [e6K, recsV_take_succ I v hlt, List.flatten_append, List.reverse_append]
    funext q
    by_cases hq : q = qRec
    · subst hq
      rw [Function.update_self, Function.update_self, h3s, hs2, Function.update_self, hs1,
        Function.update_self, hstk, Function.update_self]
      simp [locRec, hvs]
    · rw [Function.update_of_ne hq, Function.update_of_ne hq]
      show Function.update s3.stk qRec _ q = _
      rw [Function.update_of_ne hq]
      show Function.update s2a.stk qRec _ q = _
      rw [Function.update_of_ne hq]
      show Function.update s2.stk qRec _ q = _
      rw [Function.update_of_ne hq, hs2, Function.update_of_ne hq, hs1, Function.update_of_ne hq,
        hstk, Function.update_of_ne hq]
  · show s2.out = O; rw [ho2]; exact hout
  · rw [e6K]; omega
  · rw [hp6]; omega

lemma length_recsUpTo_le : ∀ j, j ≤ I.numLocations →
    (recsUpTo I j).length ≤ (locsPre I j).length
  | 0, _ => by simp [recsUpTo]
  | j + 1, hj => by
    have ih := length_recsUpTo_le j (by omega)
    rw [recsUpTo_succ I (by omega), locsPre_succ I (by omega), List.length_append,
      List.length_append, locD_eq']
    have := length_flatten_cnd I ⟨j, by omega⟩
    simp only [recsV, List.length_map, List.length_range, List.length_cons]
    nlinarith

/-- The loop invariant of `P1'`. -/
def p1rInv (st s : NSt CR CQ) : Prop :=
  s.env rW = I.numLocations ∧ s.env rL1 = ℓ + 1 ∧ s.env rJ ≤ I.numLocations ∧
    s.pos = posAt I (s.env rJ) ∧ s.env rOff = locOff I (s.env rJ) ∧
    s.env rCnt = (recsUpTo I (s.env rJ)).length ∧
    s.stk = Function.update st.stk qRec
      ((recsUpTo I (s.env rJ)).flatten.reverse ++ st.stk qRec) ∧ s.out = st.out

set_option maxHeartbeats 800000 in
/-- One location of `P1'`. -/
lemma p1rBody_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hkH : k ≤ H I)
    (hℓ : ℓ ≤ H I) (st s : NSt CR CQ) (hI : p1rInv I st s)
    (hc : (Ex.lt (rv rJ) (rv rW)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p1rBody s s'
        (200 * Ex.nodeCost w * ((H I - s.pos) - (H I - s'.pos)) + 200 * Ex.nodeCost w) ∧
      p1rInv I st s' ∧ I.numLocations - s'.env rJ < I.numLocations - s.env rJ ∧
      H I - s'.pos ≤ H I - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  obtain ⟨hW, hL1, hjW, hpos, hoff, hcnt, hstk, hout⟩ := hI
  have hlt : s.env rJ < I.numLocations := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hW]; rw [if_neg h]
  set j := s.env rJ with hjdef
  set v : Fin I.numLocations := ⟨j, hlt⟩
  set a := initNum (I.init v)
  set d := (coordList (I.domain v)).length
  set bs := (locNums I v).map (coordNumDescription ℓ)
  have hbsl : bs.length = d := by simp [bs, length_locNums, d]
  have hfl : bs.flatten.length = d * (ℓ + 1) := length_flatten_cnd I v
  set rest := encodeNats (locsSuf I (j + 1) ++ I.schemas.length :: schsDesc I)
  have hx : (encodeSystem I).drop s.pos =
      encodeNat a ++ (encodeNat d ++ (encodeNats bs.flatten ++ rest)) := by
    rw [hpos, drop_posAt, locsSuf_cons I hlt, locD_eq', List.append_assoc, List.cons_append,
      List.cons_append, encNats_cons, encNats_cons, encodeNats_append]
  have hposle : s.pos ≤ H I := by rw [hpos]; exact posAt_le I j
  have hlenx : s.pos + (encodeNat a).length + (encodeNat d).length +
      (encodeNats bs.flatten).length ≤ H I := by
    have := congrArg List.length hx
    simp only [List.length_drop, List.length_append] at this
    have : s.pos ≤ (encodeSystem I).length := hposle
    show _ ≤ (encodeSystem I).length
    omega
  have hdf : d ≤ (encodeNats bs.flatten).length :=
    le_trans (by rw [hfl]; nlinarith) (length_le_encodeNats _)
  have hdH : d ≤ H I := by omega
  have ha2 : a ≤ 2 := initNum_le _
  have ha : (Nat.bits a).length < w := bits_lt_of_le (le_trans ha2
    (by have := three_le_H I; omega)) hH2
  have hd : (Nat.bits d).length < w := bits_lt_of_le hdH hH2
  -- reading `ι(v)` and `|D_v|`
  have r1 := rdNumS_good (Q := CQ) hw (r := rA) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s a _ hx ha
  set s1 := rdNumFinal s rA rP rT a
  have hx2 : (encodeSystem I).drop s1.pos = encodeNat d ++ (encodeNats bs.flatten ++ rest) := by
    simp only [s1, rdNumFinal_pos]
    rw [← List.drop_drop, hx, List.drop_left]
  have r2 := rdNumS_good (Q := CQ) hw (r := rD) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s1 d _ hx2 hd
  set s2 := rdNumFinal s1 rD rP rT d
  have e2 : ∀ q, q ≠ rD → q ≠ rA → q ≠ rP → q ≠ rT → s2.env q = s.env q := by
    intro q h1 h2 h3 h4
    rw [rdNumFinal_env_ne h1 h3 h4, rdNumFinal_env_ne h2 h3 h4]
  have e2D : s2.env rD = d := rdNumFinal_env_r (by decide) (by decide) d
  have e2A : s2.env rA = a := by
    rw [rdNumFinal_env_ne (by decide) (by decide) (by decide)]
    exact rdNumFinal_env_r (by decide) (by decide) a
  have hp2 : s2.pos = s.pos + (encodeNat a).length + (encodeNat d).length := rfl
  -- the labels and the counter
  have h1w : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have r3 := Good.set (x := encodeSystem I) (w := w) (r := rLab)
    (e := .add (.const 1) (.lt (rv rA) (.const 1))) (st := s2) (by
      simp only [Ex.Fits, Ex.eval, rv, e2A]
      refine ⟨h1w, ⟨by omega, h1w⟩, ?_⟩
      split_ifs <;> omega)
  set s3 := s2.set rLab (Ex.eval s2.env (.add (.const 1) (.lt (rv rA) (.const 1))))
  have r4 := Good.set (x := encodeSystem I) (w := w) (r := rK) (e := .const 0) (st := s3)
    (by simp only [Ex.Fits]; omega)
  set s4 := s3.set rK (Ex.eval s3.env (.const 0))
  have e4 : ∀ q, s4.env q = Function.update (Function.update s2.env rLab (labsN I v)) rK 0 q := by
    intro q
    show Function.update (Function.update s2.env rLab
      (Ex.eval s2.env (.add (.const 1) (.lt (rv rA) (.const 1))))) rK 0 q = _
    rw [labsN_eq]; simp only [Ex.eval, rv, e2A] <;> rfl
  have back4 : ∀ q, q ≠ rK → q ≠ rLab → q ≠ rD → q ≠ rA → q ≠ rP → q ≠ rT →
      s4.env q = s.env q := by
    intro q h1 h2 h3 h4 h5 h6
    rw [e4, Function.update_of_ne h1, Function.update_of_ne h2, e2 q h3 h4 h5 h6]
  have hB : (encodeSystem I).drop s4.pos = encodeNats bs.flatten ++ rest := by
    show (encodeSystem I).drop s2.pos = _
    simp only [s2, rdNumFinal_pos]
    rw [← List.drop_drop, hx2, List.drop_left]
  have hI4 : p1rInInv I v s4.pos s.stk s.out s4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · rw [e4, Function.update_self]; omega
    · rw [e4, Function.update_of_ne (by decide), Function.update_of_ne (by decide), e2D]
    · rw [back4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [back4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hL1]
    · rw [e4, Function.update_of_ne (by decide), Function.update_self]
    · rw [e4, Function.update_of_ne (by decide), Function.update_of_ne (by decide), e2A]
    · rw [back4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hW]
    · rw [back4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hoff,
        e4, Function.update_self]; simp; rfl
    · rw [e4, Function.update_self]; simp [encodeNats]
    · rw [e4, Function.update_self]; simp only [List.take_zero, List.flatten_nil,
        List.reverse_nil, List.nil_append, Function.update_eq_self]; rfl
  -- the coordinates
  obtain ⟨s5, r5, hI5, hc5⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rK) (rv rD)) (body := p1rIn) (p1rInInv I v s4.pos s.stk s.out)
    (fun s => d - s.env rK) (fun s' => s4.pos + (encodeNats bs.flatten).length - s'.pos)
    (60 * Ex.nodeCost w) (100 * Ex.nodeCost w) (fun s' hI' => ⟨by
      obtain ⟨hK, hD, -⟩ := hI'
      simp only [Ex.Fits, rv, hD]; omega,
      fun hc' => p1rIn_good I hw hH hkH hℓ v s4.pos s.stk s.out rest hB
        (locOff_le_H I _) s' hI' hc'⟩) s4 hI4
  obtain ⟨hK5, hD5, hJ5, hL15, hLab5, -, hW5, hO5, hp5, hs5, ho5⟩ := hI5
  have hK5' : s5.env rK = d := by
    simp only [Ex.eval, rv, hD5] at hc5; split_ifs at hc5 with h <;> omega
  have hcnt5 : s5.env rCnt = (recsUpTo I j).length := by
    rw [r5.env_of (by decide), back4 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hcnt]
  have hrl : (recsUpTo I (j + 1)).length = (recsUpTo I j).length + d := by
    rw [recsUpTo_succ I hlt]; simp [recsV]; rfl
  have hrH : (recsUpTo I (j + 1)).length ≤ H I :=
    (length_recsUpTo_le I (j + 1) (by omega)).trans (locsPre_le I _)
  have r5c := Good.set (x := encodeSystem I) (w := w) (r := rCnt) (e := .add (rv rCnt) (rv rD))
    (st := s5) (by simp only [Ex.Fits, Ex.eval, rv, hcnt5, hD5]; omega)
  set s5c := s5.set rCnt (Ex.eval s5.env (.add (rv rCnt) (rv rD)))
  have e5c : ∀ q, q ≠ rCnt → s5c.env q = s5.env q := fun q h => by
    simp [s5c, Function.update_of_ne h]
  have r6 := Good.set (x := encodeSystem I) (w := w) (r := rJ) (e := .add (rv rJ) (.const 1))
    (st := s5c) (by
      have := W_le I
      simp only [Ex.Fits, Ex.eval, rv, e5c _ (show rJ ≠ rCnt by decide), hJ5]; omega)
  set s6 := s5c.set rJ (Ex.eval s5c.env (.add (rv rJ) (.const 1)))
  have e6J : s6.env rJ = j + 1 := by
    simp [s6, Ex.eval, rv, e5c _ (show rJ ≠ rCnt by decide), hJ5, v]
  have e6 : ∀ q, q ≠ rJ → q ≠ rCnt → s6.env q = s5.env q := fun q h h' => by
    simp only [s6, NSt.set_env, Function.update_of_ne h]; exact e5c q h'
  have e6C : s6.env rCnt = (recsUpTo I (j + 1)).length := by
    simp only [s6, NSt.set_env, Function.update_of_ne (show rCnt ≠ rJ by decide), s5c,
      Function.update_self, Ex.eval, rv, hcnt5, hD5, hrl]; rfl
  have hp6 : s6.pos = s.pos + (encodeNat a).length + (encodeNat d).length +
      (encodeNats bs.flatten).length := by
    show s5.pos = _
    rw [hp5, hK5', List.take_of_length_le (le_of_eq hbsl)]; rfl
  have hφ4 : s4.pos + (encodeNats bs.flatten).length - s4.pos =
      (encodeNats bs.flatten).length := by omega
  refine ⟨s6, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r5c.seq r6)))))).mono ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hp6, hφ4]
    have hΔ : H I - s.pos - (H I - (s.pos + (encodeNat a).length + (encodeNat d).length +
        (encodeNats bs.flatten).length)) = (encodeNat a).length + (encodeNat d).length +
        (encodeNats bs.flatten).length := by omega
    have hμ : d - s4.env rK = d := by rw [e4, Function.update_self]; rfl
    rw [hΔ, hμ]
    simp only [condCost, Ex.size, rv]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNat a).length = la at *
    generalize (encodeNat d).length = ld at *
    generalize (encodeNats bs.flatten).length = lf at *
    have := Nat.mul_le_mul_left N hdf
    nlinarith only [hU, hU', this]
  · rw [e6 _ (by decide) (by decide), hW5]
  · rw [e6 _ (by decide) (by decide), hL15]
  · rw [e6J]; omega
  · rw [e6J, hp6, hpos, posAt_succ I hlt, locD_eq']
    simp only [encNats_cons, List.length_append]; ring
  · rw [e6J, e6 _ (by decide) (by decide), hO5, hK5', locOff_succ I hlt]; rfl
  · rw [e6J, e6C]
  · rw [NSt.set_stk, show s5c.stk = s5.stk from rfl, hs5, hK5', e6J, recsUpTo_succ I hlt, hstk]
    have hrv : (recsV I v).take d = recsV I v := List.take_of_length_le (by simp [recsV, d])
    rw [hrv, List.flatten_append, List.reverse_append]
    funext q
    by_cases hq : q = qRec
    · subst hq; simp; rfl
    · simp [Function.update_of_ne hq]
  · rw [NSt.set_out, show s5c.out = s5.out from rfl, ho5, hout]
  · rw [e6J]; omega
  · rw [hp6]; omega

/-- **Pass `P1'`.** Run after `p1` (with `rW = W`, `rL1 = ℓ + 1`) on a system with
`k, ℓ ≤ H`, `p1r` pushes all location records onto `qRec` (the last word on top), keeping the
other stacks, the output and `rW`, `rL1`. -/
theorem p1r_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hkH : k ≤ H I)
    (hℓ : ℓ ≤ H I) (st : NSt CR CQ) (hp : st.pos ≤ H I) (hW : st.env rW = I.numLocations)
    (hL1 : st.env rL1 = ℓ + 1) :
    ∃ st', Good (encodeSystem I) w p1r st st' (600 * (H I + 1) * Ex.nodeCost w) ∧
      st'.stk = Function.update st.stk qRec ((locRecs I).flatten.reverse ++ st.stk qRec) ∧
      st'.out = st.out ∧ st'.pos = posAt I I.numLocations ∧ st'.env rW = I.numLocations ∧
      st'.env rL1 = ℓ + 1 ∧ st'.env rKk = k ∧ st'.env rCnt = (locRecs I).length ∧
      ∀ r, CStm.wReg r p1r = false → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hWH := W_le I
  have r0 := Good.rst (x := encodeSystem I) (w := w) (st := st)
  set s0 : NSt CR CQ := { st with pos := 0 }
  have r1 := rdNumS_good (Q := CQ) hw (r := rKk) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s0 k _ (drop_zero_k I) (bits_lt_of_le hkH (by omega))
  set s1 := rdNumFinal s0 rKk rP rT k
  have r2 := skipNumS_good (Q := CQ) hw (t := rT) s1 ℓ _
    (by show (encodeSystem I).drop (0 + _) = _; rw [zero_add]; exact drop_ell I)
  set s2 := skipNumFinal s1 rT ℓ
  have r3 := skipNumS_good (Q := CQ) hw (t := rT) s2 I.numLocations _
    (by show (encodeSystem I).drop (0 + _ + _) = _; rw [zero_add]; exact drop_W I)
  set s3 := skipNumFinal s2 rT I.numLocations
  have r4 := Good.set (x := encodeSystem I) (w := w) (r := rJ) (e := .const 0) (st := s3)
    (by simp only [Ex.Fits]; omega)
  set s4 := s3.set rJ (Ex.eval s3.env (.const 0))
  have r5 := Good.set (x := encodeSystem I) (w := w) (r := rOff) (e := .const 0) (st := s4)
    (by simp only [Ex.Fits]; omega)
  set s5 := s4.set rOff (Ex.eval s4.env (.const 0))
  have e5 : ∀ q, s5.env q = Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
        (Function.update st.env rKk k) rP (2 ^ (Nat.bits k).length)) rT 1) rT 1) rT 1) rJ 0)
      rOff 0 q := fun _ => rfl
  have r5b := Good.set (x := encodeSystem I) (w := w) (r := rCnt) (e := .const 0) (st := s5)
    (by simp only [Ex.Fits]; omega)
  set s5b := s5.set rCnt (Ex.eval s5.env (.const 0))
  have e5b : ∀ q, s5b.env q = Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
        (Function.update st.env rKk k) rP (2 ^ (Nat.bits k).length)) rT 1) rT 1) rT 1) rJ 0)
      rOff 0) rCnt 0 q := fun _ => rfl
  have hp5 : s5b.pos = posAt I 0 := by
    show 0 + (encodeNat k).length + (encodeNat ℓ).length + (encodeNat I.numLocations).length = _
    rw [posAt_zero]; ring
  have e5J : s5b.env rJ = 0 := by
    rw [e5b, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]
  have hI5 : p1rInv I st s5b := by
    refine ⟨?_, ?_, by rw [e5J]; omega, by rw [e5J, hp5], ?_, by rw [e5J, e5b, Function.update_self]; rfl, ?_, rfl⟩
    · rw [e5b]; simp only [Function.update_of_ne (show rW ≠ rCnt by decide), Function.update_of_ne (show rW ≠ rOff by decide),
        Function.update_of_ne (show rW ≠ rJ by decide), Function.update_of_ne (show rW ≠ rT by decide),
        Function.update_of_ne (show rW ≠ rP by decide), Function.update_of_ne (show rW ≠ rKk by decide)]
      exact hW
    · rw [e5b]; simp only [Function.update_of_ne (show rL1 ≠ rCnt by decide), Function.update_of_ne (show rL1 ≠ rOff by decide),
        Function.update_of_ne (show rL1 ≠ rJ by decide),
        Function.update_of_ne (show rL1 ≠ rT by decide), Function.update_of_ne (show rL1 ≠ rP by decide),
        Function.update_of_ne (show rL1 ≠ rKk by decide)]
      exact hL1
    · rw [e5J, locOff_zero, e5b, Function.update_of_ne (by decide), Function.update_self]
    · rw [e5J]; simp only [recsUpTo, List.take_zero, List.flatMap_nil, List.flatten_nil,
        List.reverse_nil, List.nil_append, Function.update_eq_self]; rfl
  obtain ⟨s6, r6, hI6, hc6⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rW)) (body := p1rBody) (p1rInv I st)
    (fun s => I.numLocations - s.env rJ) (fun s => H I - s.pos) (200 * Ex.nodeCost w)
    (200 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hW', -, hj, -⟩ := hI
      simp only [Ex.Fits, rv, hW']; omega, fun hc => p1rBody_good I hw hH hkH hℓ st s hI hc⟩)
    s5b hI5
  obtain ⟨hW6, hL6, hj6, hpos6, -, hcnt6, hstk6, hout6⟩ := hI6
  have hj : s6.env rJ = I.numLocations := by
    simp only [Ex.eval, rv, hW6] at hc6; split_ifs at hc6 with h <;> omega
  have hall := r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r5b.seq r6))))))
  have hK5 : s5b.env rKk = k := by
    rw [e5b]; simp only [Function.update_of_ne (show rKk ≠ rCnt by decide), Function.update_of_ne (show rKk ≠ rOff by decide),
      Function.update_of_ne (show rKk ≠ rJ by decide), Function.update_of_ne (show rKk ≠ rT by decide),
      Function.update_of_ne (show rKk ≠ rP by decide), Function.update_self]
  refine ⟨s6, hall.mono ?_, by rw [hstk6, hj, recsUpTo_all], hout6, by rw [hpos6, hj], hW6, hL6,
    by rw [r6.env_of (by decide), hK5], by rw [hcnt6, hj, recsUpTo_all], fun r hr => hall.env_of hr⟩
  have hlen : (encodeNat k).length + (encodeNat ℓ).length +
      (encodeNat I.numLocations).length ≤ H I := by rw [← posAt_zero]; exact posAt_le I 0
  have hφ : H I - s5b.pos ≤ H I := by omega
  have hμ : I.numLocations - s5b.env rJ ≤ H I := by omega
  simp only [condCost, Ex.size, rv] at *
  generalize Ex.nodeCost w = N at *
  generalize unitCost w = U at *
  generalize H I - s5b.pos = φ at *
  generalize I.numLocations - s5b.env rJ = μ at *
  generalize (encodeNat k).length = lk at *
  generalize (encodeNat ℓ).length = ll at *
  generalize (encodeNat I.numLocations).length = lW at *
  generalize st.pos = p at *
  generalize H I = h at *
  nlinarith only [hU, hU', hφ, hμ, hlen, hp]

end Lax119563Proofs.Compiler

end Compiler_PRec

/-! ### Formerly `Lax119563Proofs.Compiler.PJoin` -/

section Compiler_PJoin

/-!
# The join of pass `P3`: the scan program

Registers and stacks of `P3`, and the scan `pJScan` over the sorted union of the location
records and the requests on `qX` (records `v :: i :: b₀ … b_{ℓ-1} ++ [tag, d₁, d₂, d₃]`):
a location record (tag `0`, data `off, labs, ι`) sets the current data
`(off, labs, seed)` with `seed = [i = 0 ∧ ι = 2]`; a request (tag `1`, data `seq, 0, 0`)
pushes the answer `[seq, off, labs, seed]` onto `qAns` (**`pJScan_good`**, against
`Join.scanF`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

/-! ## Registers and stacks of `P3` -/

/-- The union of records to be sorted. -/
def qX : Fin CQ := 5
/-- Scratch stacks of the sort (empty outside of it). -/
def qT1 : Fin CQ := 6
def qT2 : Fin CQ := 7
def qY : Fin CQ := 8
def qTmp : Fin CQ := 9
def qC1 : Fin CQ := 10
def qC2 : Fin CQ := 11
/-- The answers. -/
def qAns : Fin CQ := 12
/-- Discarded words. -/
def qJunk : Fin CQ := 13

/-- Scan registers. -/
def rTg : Fin CR := 20
def rD1 : Fin CR := 21
def rD2 : Fin CR := 22
def rD3 : Fin CR := 23
def rCo : Fin CR := 24
def rCl : Fin CR := 25
def rCs : Fin CR := 27
def rN : Fin CR := 28
def rJi : Fin CR := 29

open CStm

/-! ## The program -/

/-- The seed `[i = 0 ∧ ι = 2]`. -/
def seedEx : Ex CR := .half (.add (.lt (rv rJi) (.const 1)) (.lt (.const 1) (rv rD3)))

/-- Pop a record. -/
def pJPop : CStm CR CQ :=
  .seq (.pop qX rV) (.seq (.pop qX rJi) (.seq (moveN qX qJunk rL rI rT)
    (.seq (.pop qX rTg) (.seq (.pop qX rD1) (.seq (.pop qX rD2) (.pop qX rD3))))))

/-- Answer a request. -/
def pJAns : CStm CR CQ :=
  .seq (.push qAns (rv rCs)) (.seq (.push qAns (rv rCl))
    (.seq (.push qAns (rv rCo)) (.push qAns (rv rD1))))

/-- Remember a location record. -/
def pJLoc : CStm CR CQ :=
  .seq (.set rCo (rv rD1)) (.seq (.set rCl (rv rD2)) (.set rCs seedEx))

/-- One record. -/
def pJStep : CStm CR CQ :=
  .seq pJPop (.seq (.ite (rv rTg) pJAns pJLoc) (.set rK (.add (rv rK) (.const 1))))

/-- **The scan** over `rN` records. -/
def pJScan : CStm CR CQ := .seq (.set rK (.const 0)) (.loop (.lt (rv rK) (rv rN)) pJStep)

/-! ## The list level -/

/-- The seed value. -/
def seedV (i d : ℕ) : ℕ := ((if i < 1 then 1 else 0) + (if 1 < d then 1 else 0)) / 2

/-- The data of a location record. -/
def jCur (ℓ : ℕ) (m : List ℕ) : ℕ × ℕ × ℕ :=
  (m.getD (ℓ + 3) 0, m.getD (ℓ + 4) 0, seedV (m.getD 1 0) (m.getD (ℓ + 5) 0))

/-- The answer to a request. -/
def jAns (ℓ : ℕ) (c : ℕ × ℕ × ℕ) (r : List ℕ) : List ℕ := [r.getD (ℓ + 3) 0, c.1, c.2.1, c.2.2]

/-- The scan. -/
abbrev jScan (ℓ : ℕ) (c0 : ℕ × ℕ × ℕ) (L : List (List ℕ)) : List (List ℕ) :=
  Join.scanF (ℓ + 2) (jCur ℓ) (jAns ℓ) c0 L

/-- The current data after a prefix. -/
abbrev jCurAfter (ℓ : ℕ) (c0 : ℕ × ℕ × ℕ) (L : List (List ℕ)) : ℕ × ℕ × ℕ :=
  Join.curAfter (ℓ + 2) (jCur ℓ) c0 L

/-! ## Popping a record -/

lemma Good.pop_cons {x : List Bool} {w : ℕ} {st : NSt CR CQ} {q : Fin CQ} {r : Fin CR} {a : ℕ}
    {rest : List ℕ} (h : st.stk q = a :: rest) :
    Good x w (.pop q r : CStm CR CQ) st ((st.setS q rest).set r a) (unitCost w + 1) := by
  have := Good.pop (x := x) (w := w) (st := st) q r
  rwa [h] at this

lemma ex_rec (ℓ : ℕ) (r : List ℕ) (h : r.length = ℓ + 6) :
    ∃ a b bits tg d1 d2 d3, r = a :: b :: bits ++ [tg, d1, d2, d3] ∧ bits.length = ℓ := by
  match r, h with
  | a :: b :: t, h =>
    have ht : t.length = ℓ + 4 := by simp at h; omega
    have hd : (t.drop ℓ).length = 4 := by simp [ht]
    match hdr : t.drop ℓ, hd with
    | [tg, d1, d2, d3], _ =>
      refine ⟨a, b, t.take ℓ, tg, d1, d2, d3, ?_, by simp [ht]⟩
      rw [← hdr]; simp

set_option maxHeartbeats 1000000 in
lemma pJPop_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) {ℓ a b tg d1 d2 d3 : ℕ}
    {bits rest : List ℕ} (hbits : bits.length = ℓ) (hX : s.stk qX = a :: b :: bits ++
      [tg, d1, d2, d3] ++ rest) (hL : s.env rL = ℓ) (hℓw : ℓ + 1 < 2 ^ w)
    (hbw : ∀ v ∈ bits, v < 2 ^ w) :
    ∃ s', Good x w pJPop s s' ((ℓ + 8) * (12 * Ex.nodeCost w)) ∧
      s'.stk qX = rest ∧ (∀ q, q ≠ qX → q ≠ qJunk → s'.stk q = s.stk q) ∧
      s'.env rJi = b ∧ s'.env rTg = tg ∧ s'.env rD1 = d1 ∧ s'.env rD2 = d2 ∧ s'.env rD3 = d3 ∧
      s'.pos = s.pos ∧ s'.out = s.out ∧ ∀ r, wReg r pJPop = false → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have r1 := Good.pop_cons (x := x) (w := w) (r := rV) (st := s) (q := qX) hX
  set s1 := (s.setS qX (b :: bits ++ [tg, d1, d2, d3] ++ rest)).set rV a
  have r2 := Good.pop_cons (x := x) (w := w) (r := rJi) (st := s1) (q := qX)
    (a := b) (rest := bits ++ [tg, d1, d2, d3] ++ rest) (by simp [s1])
  set s2 := (s1.setS qX (bits ++ [tg, d1, d2, d3] ++ rest)).set rJi b
  have hs2X : s2.stk qX = bits ++ [tg, d1, d2, d3] ++ rest := by simp [s2]
  have hs2L : s2.env rL = ℓ := by
    simp only [s2, s1, NSt.set_env, NSt.setS_env]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hL]
  obtain ⟨s3, r3, hs3, hf3⟩ := moveN_good (x := x) (w := w) (src := qX) (dst := qJunk)
    (cnt := rL) (i := rI) (t := rT) (by decide) (by decide) (by decide) (by decide) s2 hs2L
    (by rw [hs2X]; simp [hbits]) hℓw (by
      rw [hs2X, List.append_assoc, List.take_append_of_le_length (by omega),
        List.take_of_length_le (le_of_eq hbits)]
      exact hbw)
  have hs3X : s3.stk qX = tg :: d1 :: d2 :: d3 :: rest := by
    rw [hs3, movedStk_src _ (by decide), hs2X, List.append_assoc, List.drop_append_of_le_length
      (by omega), List.drop_eq_nil_of_le (by omega)]
    rfl
  have r4 := Good.pop_cons (x := x) (w := w) (r := rTg) hs3X
  set s4 := (s3.setS qX (d1 :: d2 :: d3 :: rest)).set rTg tg
  have r5 := Good.pop_cons (x := x) (w := w) (r := rD1) (st := s4) (q := qX) (a := d1)
    (rest := d2 :: d3 :: rest) (by simp [s4])
  set s5 := (s4.setS qX (d2 :: d3 :: rest)).set rD1 d1
  have r6 := Good.pop_cons (x := x) (w := w) (r := rD2) (st := s5) (q := qX) (a := d2)
    (rest := d3 :: rest) (by simp [s5])
  set s6 := (s5.setS qX (d3 :: rest)).set rD2 d2
  have r7 := Good.pop_cons (x := x) (w := w) (r := rD3) (st := s6) (q := qX) (a := d3)
    (rest := rest) (by simp [s6])
  set s7 := (s6.setS qX rest).set rD3 d3
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  have e3 : ∀ r, r ≠ rI → r ≠ rT → s3.env r = s2.env r := fun r h1 h2 => hf3.2.2 r (by
    simp [h1, h2])
  refine ⟨s7, hall.mono ?_, by simp [s7], fun q h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr => hall.env_of hr⟩
  · nlinarith
  · simp only [s7, s6, s5, s4, NSt.set_stk, NSt.setS_stk, Function.update_of_ne h1]
    rw [hs3, movedStk_other _ h1 h2]
    simp [s2, s1, Function.update_of_ne h1]
  · simp only [s7, s6, s5, s4, NSt.set_env, NSt.setS_env]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      e3 _ (by decide) (by decide)]
    simp [s2]
  · simp [s7, s6, s5, s4, Function.update_of_ne (show rTg ≠ rD1 by decide),
      Function.update_of_ne (show rTg ≠ rD2 by decide), Function.update_of_ne (show rTg ≠ rD3 by decide)]
  · simp [s7, s6, s5, Function.update_of_ne (show rD1 ≠ rD2 by decide),
      Function.update_of_ne (show rD1 ≠ rD3 by decide)]
  · simp [s7, s6, Function.update_of_ne (show rD2 ≠ rD3 by decide)]
  · simp [s7]
  · simp only [s7, s6, s5, s4, NSt.set_pos, NSt.setS_pos]; rw [hf3.1]; rfl
  · simp only [s7, s6, s5, s4, NSt.set_out, NSt.setS_out]; rw [hf3.2.1]; rfl

lemma rec_getD {ℓ a b tg d1 d2 d3 : ℕ} {bits : List ℕ} (hbits : bits.length = ℓ) :
    (a :: b :: bits ++ [tg, d1, d2, d3]).getD 1 0 = b ∧
    (a :: b :: bits ++ [tg, d1, d2, d3]).getD (ℓ + 2) 0 = tg ∧
    (a :: b :: bits ++ [tg, d1, d2, d3]).getD (ℓ + 3) 0 = d1 ∧
    (a :: b :: bits ++ [tg, d1, d2, d3]).getD (ℓ + 4) 0 = d2 ∧
    (a :: b :: bits ++ [tg, d1, d2, d3]).getD (ℓ + 5) 0 = d3 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, hbits]

lemma seedV_le (i d : ℕ) : seedV i d ≤ 1 := by
  unfold seedV; split_ifs <;> omega

set_option maxHeartbeats 1000000 in
/-- One record of the scan. -/
lemma pJStep_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) {ℓ : ℕ}
    (r rest : List ℕ) (hr : r.length = ℓ + 6) (hX : s.stk qX = r ++ rest) (hL : s.env rL = ℓ)
    (hℓw : ℓ + 1 < 2 ^ w) (hrw : ∀ v ∈ r, v < 2 ^ w) (c : ℕ × ℕ × ℕ)
    (hc : (s.env rCo, s.env rCl, s.env rCs) = c) (hcw : c.1 < 2 ^ w ∧ c.2.1 < 2 ^ w ∧ c.2.2 < 2 ^ w)
    (hK : s.env rK + 1 < 2 ^ w) :
    ∃ s', Good x w pJStep s s' ((ℓ + 20) * (12 * Ex.nodeCost w)) ∧
      s'.stk qX = rest ∧
      s'.stk qAns = (if Join.isLoc (ℓ + 2) r then [] else jAns ℓ c r) ++ s.stk qAns ∧
      (∀ q, q ≠ qX → q ≠ qAns → q ≠ qJunk → s'.stk q = s.stk q) ∧
      (s'.env rCo, s'.env rCl, s'.env rCs) =
        (if Join.isLoc (ℓ + 2) r then jCur ℓ r else c) ∧
      s'.env rK = s.env rK + 1 ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ q, wReg q pJStep = false → s'.env q = s.env q := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨a, b, bits, tg, d1, d2, d3, rfl, hbits⟩ := ex_rec ℓ r hr
  obtain ⟨g1, g2, g3, g4, g5⟩ := rec_getD (a := a) (b := b) (tg := tg) (d1 := d1) (d2 := d2)
    (d3 := d3) hbits
  have hw1 : ∀ v ∈ bits, v < 2 ^ w := fun v hv => hrw v (by simp [hv])
  have hd1 : d1 < 2 ^ w := hrw d1 (by simp)
  have hd2 : d2 < 2 ^ w := hrw d2 (by simp)
  have hd3 : d3 < 2 ^ w := hrw d3 (by simp)
  have hb : b < 2 ^ w := hrw b (by simp)
  have htw : tg < 2 ^ w := hrw tg (by simp)
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  obtain ⟨s1, r1, h1X, h1S, h1i, h1t, h1d1, h1d2, h1d3, h1p, h1o, h1e⟩ :=
    pJPop_good (x := x) hw s hbits (by rw [hX]) hL hℓw hw1
  have e1 : ∀ q, q ≠ rV → q ≠ rJi → q ≠ rI → q ≠ rT → q ≠ rTg → q ≠ rD1 → q ≠ rD2 →
      q ≠ rD3 → s1.env q = s.env q := by
    intro q n1 n2 n3 n4 n5 n6 n7 n8
    refine h1e q ?_
    simp [pJPop, moveN, wReg, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm,
      n8.symm]
  have eCo : s1.env rCo = c.1 := by
    rw [e1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ← hc]
  have eCl : s1.env rCl = c.2.1 := by
    rw [e1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ← hc]
  have eCs : s1.env rCs = c.2.2 := by
    rw [e1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ← hc]
  have eK : s1.env rK = s.env rK := by
    rw [e1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  set r := a :: b :: bits ++ [tg, d1, d2, d3]
  by_cases htg : tg = 0
  · -- a location record
    have hloc : Join.isLoc (ℓ + 2) r = true := by
      simp only [Join.isLoc, g2, htg, beq_self_eq_true]
    have r2a := Good.set (x := x) (w := w) (r := rCo) (e := rv rD1) (st := s1)
      (by simp only [Ex.Fits, rv, h1d1]; exact hd1)
    set s2a := s1.set rCo ((rv rD1 : Ex CR).eval s1.env)
    have r2b := Good.set (x := x) (w := w) (r := rCl) (e := rv rD2) (st := s2a)
      (by simp only [Ex.Fits, rv, s2a, NSt.set_env, Function.update_of_ne (show rD2 ≠ rCo by decide), h1d2]; exact hd2)
    set s2b := s2a.set rCl ((rv rD2 : Ex CR).eval s2a.env)
    have ei : s2b.env rJi = b := by
      simp [s2b, s2a, Function.update_of_ne (show rJi ≠ rCl by decide),
        Function.update_of_ne (show rJi ≠ rCo by decide), h1i]
    have e3 : s2b.env rD3 = d3 := by
      simp [s2b, s2a, Function.update_of_ne (show rD3 ≠ rCl by decide),
        Function.update_of_ne (show rD3 ≠ rCo by decide), h1d3]
    have r2c := Good.set (x := x) (w := w) (r := rCs) (e := seedEx) (st := s2b) (by
      simp only [seedEx, Ex.Fits, Ex.eval, rv, ei, e3]
      split_ifs <;> (repeat' constructor) <;> omega)
    set s2 := s2b.set rCs (seedEx.eval s2b.env)
    have r2 := Good.iteF (x := x) (w := w) (e := rv rTg) (p := pJAns) (q := pJLoc) (st := s1)
      (by simp only [Ex.Fits, rv, h1t]; omega) (by simp [rv, Ex.eval, h1t, htg])
      (r2a.seq (r2b.seq r2c))
    have eK2 : s2.env rK = s.env rK := by
      simp [s2, s2b, s2a, Function.update_of_ne (show rK ≠ rCs by decide),
        Function.update_of_ne (show rK ≠ rCl by decide),
        Function.update_of_ne (show rK ≠ rCo by decide), eK]
    have r3 := Good.set (x := x) (w := w) (r := rK) (e := .add (rv rK) (.const 1)) (st := s2)
      (by simp only [Ex.Fits, Ex.eval, rv, eK2]; omega)
    have hall := r1.seq (r2.seq r3)
    refine ⟨_, hall.mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => hall.env_of hq⟩
    · simp only [condCost, rv, Ex.size, seedEx]; nlinarith
    · exact h1X
    · simp only [hloc, if_true, List.nil_append]
      simp only [NSt.set_stk, s2, s2b, s2a]; exact h1S _ (by decide) (by decide)
    · intro q n1 n2 n3; simp only [NSt.set_stk, s2, s2b, s2a]; exact h1S q n1 n3
    · simp only [hloc, if_true, jCur, g1, g3, g4, g5]
      simp [s2, s2b, s2a, Function.update_of_ne (show rCo ≠ rK by decide),
        Function.update_of_ne (show rCl ≠ rK by decide),
        Function.update_of_ne (show rCs ≠ rK by decide),
        Function.update_of_ne (show rCo ≠ rCs by decide),
        Function.update_of_ne (show rCl ≠ rCs by decide),
        Function.update_of_ne (show rCo ≠ rCl by decide), h1d1, h1d2, ei, e3, seedEx, seedV,
        Function.update_of_ne (show rD2 ≠ rCo by decide), Function.update_of_ne (show rJi ≠ rCl by decide),
        Function.update_of_ne (show rJi ≠ rCo by decide), Function.update_of_ne (show rD3 ≠ rCl by decide),
        Function.update_of_ne (show rD3 ≠ rCo by decide), h1i, h1d3,
        Ex.eval, rv]
    · simp [eK2, Ex.eval, rv]
    · simp [s2, s2b, s2a, h1p]
    · simp [s2, s2b, s2a, h1o]
  · -- a request
    have hloc : Join.isLoc (ℓ + 2) r = false := by
      simp only [Join.isLoc, g2]; simpa using htg
    have r2a := Good.push (x := x) (w := w) (q := qAns) (e := rv rCs) (st := s1)
      (by simp only [Ex.Fits, rv, eCs]; exact hcw.2.2)
    set s2a := s1.setS qAns ((rv rCs : Ex CR).eval s1.env :: s1.stk qAns)
    have r2b := Good.push (x := x) (w := w) (q := qAns) (e := rv rCl) (st := s2a)
      (by simp only [Ex.Fits, rv, s2a, NSt.setS_env, eCl]; exact hcw.2.1)
    set s2b := s2a.setS qAns ((rv rCl : Ex CR).eval s2a.env :: s2a.stk qAns)
    have r2c := Good.push (x := x) (w := w) (q := qAns) (e := rv rCo) (st := s2b)
      (by simp only [Ex.Fits, rv, s2b, s2a, NSt.setS_env, eCo]; exact hcw.1)
    set s2c := s2b.setS qAns ((rv rCo : Ex CR).eval s2b.env :: s2b.stk qAns)
    have r2d := Good.push (x := x) (w := w) (q := qAns) (e := rv rD1) (st := s2c)
      (by simp only [Ex.Fits, rv, s2c, s2b, s2a, NSt.setS_env, h1d1]; exact hd1)
    set s2 := s2c.setS qAns ((rv rD1 : Ex CR).eval s2c.env :: s2c.stk qAns)
    have r2 := Good.iteT (x := x) (w := w) (e := rv rTg) (p := pJAns) (q := pJLoc) (st := s1)
      (by simp only [Ex.Fits, rv, h1t]; omega) (by simp [rv, Ex.eval, h1t, htg])
      (r2a.seq (r2b.seq (r2c.seq r2d)))
    have eK2 : s2.env rK = s.env rK := eK
    have r3 := Good.set (x := x) (w := w) (r := rK) (e := .add (rv rK) (.const 1)) (st := s2)
      (by simp only [Ex.Fits, Ex.eval, rv, eK2]; omega)
    have hall := r1.seq (r2.seq r3)
    refine ⟨_, hall.mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => hall.env_of hq⟩
    · simp only [condCost, rv, Ex.size]; nlinarith
    · simp only [NSt.set_stk, s2, s2c, s2b, s2a, NSt.setS_stk]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), h1X]
    · simp only [hloc, Bool.false_eq_true, if_false, jAns, g3]
      simp only [NSt.set_stk, s2, s2c, s2b, s2a, NSt.setS_stk, Function.update_self, NSt.setS_env,
        Ex.eval, rv, eCo, eCl, eCs, h1d1]
      rw [h1S _ (by decide) (by decide)]; rfl
    · intro q n1 n2 n3
      simp only [NSt.set_stk, s2, s2c, s2b, s2a, NSt.setS_stk]
      rw [Function.update_of_ne n2, Function.update_of_ne n2, Function.update_of_ne n2,
        Function.update_of_ne n2, h1S q n1 n3]
    · simp only [hloc, Bool.false_eq_true, if_false]
      simp only [NSt.set_env, s2, s2c, s2b, s2a, NSt.setS_env,
        Function.update_of_ne (show rCo ≠ rK by decide),
        Function.update_of_ne (show rCl ≠ rK by decide),
        Function.update_of_ne (show rCs ≠ rK by decide), eCo, eCl, eCs]
    · simp [eK2, Ex.eval, rv]
    · simp [s2, s2c, s2b, s2a, h1p]
    · simp [s2, s2c, s2b, s2a, h1o]

lemma getD_lt {r : List ℕ} {w : ℕ} (hrw : ∀ v ∈ r, v < 2 ^ w) (hw : 0 < 2 ^ w) (i : ℕ) :
    r.getD i 0 < 2 ^ w := by
  rw [List.getD_eq_getElem?_getD]
  cases h : r[i]? with
  | none => simpa using hw
  | some v => exact hrw v (List.mem_of_getElem? h)

set_option maxHeartbeats 1000000 in
/-- **The scan.** Over the records `L` on `qX` (each of `ℓ + 6` words), `pJScan` pushes the
answers of `jScan` onto `qAns` (the last answer on top). -/
theorem pJScan_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) {ℓ : ℕ}
    (L : List (List ℕ)) (hX : st.stk qX = L.flatten) (hL : st.env rL = ℓ)
    (hN : st.env rN = L.length) (hlen : ∀ r ∈ L, r.length = ℓ + 6)
    (hrw : ∀ r ∈ L, ∀ v ∈ r, v < 2 ^ w) (hℓw : ℓ + 1 < 2 ^ w) (hnw : L.length + 1 < 2 ^ w)
    (hcw : st.env rCo < 2 ^ w ∧ st.env rCl < 2 ^ w ∧ st.env rCs < 2 ^ w) :
    ∃ st', Good x w pJScan st st' ((L.length + 1) * ((ℓ + 21) * (12 * Ex.nodeCost w))) ∧
      st'.stk qX = [] ∧
      st'.stk qAns = (jScan ℓ (st.env rCo, st.env rCl, st.env rCs) L).reverse.flatten ++
        st.stk qAns ∧
      (∀ q, q ≠ qX → q ≠ qAns → q ≠ qJunk → st'.stk q = st.stk q) ∧
      st'.pos = st.pos ∧ st'.out = st.out ∧
      ∀ q, wReg q pJScan = false → st'.env q = st.env q := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hw0 : 0 < 2 ^ w := by positivity
  set c0 := (st.env rCo, st.env rCl, st.env rCs)
  set n := L.length
  have hcur : ∀ j, (jCurAfter ℓ c0 (L.take j)).1 < 2 ^ w ∧
      (jCurAfter ℓ c0 (L.take j)).2.1 < 2 ^ w ∧ (jCurAfter ℓ c0 (L.take j)).2.2 < 2 ^ w := by
    intro j
    rcases Join.curAfter_cases (ℓ + 2) (jCur ℓ) c0 (L.take j) with h | ⟨m, hm, h⟩
    · simp only [jCurAfter]; rw [h]; exact hcw
    · simp only [jCurAfter]; rw [h]
      have hm' := hrw m (List.mem_of_mem_take hm)
      refine ⟨getD_lt hm' hw0 _, getD_lt hm' hw0 _, ?_⟩
      have := seedV_le (m.getD 1 0) (m.getD (ℓ + 5) 0)
      have : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
      simp only [jCur]; omega
  have r0 := Good.set (x := x) (w := w) (r := rK) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  set s0 := st.set rK ((Ex.const 0 : Ex CR).eval st.env)
  set Inv : NSt CR CQ → Prop := fun s => s.env rK ≤ n ∧ s.env rN = n ∧ s.env rL = ℓ ∧
    s.stk qX = (L.drop (s.env rK)).flatten ∧
    s.stk qAns = (jScan ℓ c0 (L.take (s.env rK))).reverse.flatten ++ st.stk qAns ∧
    (∀ q, q ≠ qX → q ≠ qAns → q ≠ qJunk → s.stk q = st.stk q) ∧
    (s.env rCo, s.env rCl, s.env rCs) = jCurAfter ℓ c0 (L.take (s.env rK)) ∧
    s.pos = st.pos ∧ s.out = st.out ∧ ∀ q, wReg q pJScan = false → s.env q = st.env q
    with hInv
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv rK) (rv rN)) (body := pJStep)
    Inv (fun s => n - s.env rK) (fun _ => 0) 0 ((ℓ + 20) * (12 * Ex.nodeCost w)) (by
      intro s ⟨hk, hn, hl, hx, ha, hS, hc, hp, ho, he⟩
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hcond
      have hlt : s.env rK < n := by simpa [rv, Ex.eval, hn] using hcond
      set j := s.env rK
      have hjL : j < L.length := hlt
      have hd : L.drop j = L[j] :: L.drop (j + 1) := List.drop_eq_getElem_cons hjL
      obtain ⟨s', r', h1, h2, h3, h4, h5, h6, h7, h8⟩ := pJStep_good (x := x) hw s L[j]
        (L.drop (j + 1)).flatten (hlen _ (List.getElem_mem _)) (by rw [hx, hd]; rfl) hl hℓw
        (hrw _ (List.getElem_mem _)) _ hc (hcur j) (by omega)
      have htk : L.take (j + 1) = L.take j ++ [L[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hjL]; rfl
      refine ⟨s', r'.mono (by simp), ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega,
        le_rfl⟩
      · rw [h8 _ (by decide), hn]
      · rw [h8 _ (by decide), hl]
      · rw [h5, h1]
      · rw [h5, h2, htk, jScan, Join.scanF_append_single, ha]
        split_ifs <;> simp
      · intro q n1 n2 n3; rw [h3 q n1 n2 n3, hS q n1 n2 n3]
      · rw [h4, h5, htk]; simp only [jCurAfter]; rw [Join.curAfter_append_single]
      · rw [h6, hp]
      · rw [h7, ho]
      · intro q hq
        rw [h8 q (by simp only [pJScan, wReg, Bool.or_eq_false_iff] at hq; exact hq.2), he q hq])
    s0 ⟨by simp [s0, Ex.eval], by simp [s0, Function.update_of_ne (show rN ≠ rK by decide), hN],
      by simp [s0, Function.update_of_ne (show rL ≠ rK by decide), hL],
      by simp [s0, Ex.eval, hX], by simp [s0, Ex.eval, jScan, Join.scanF],
      fun q _ _ _ => rfl,
      by simp [s0, Ex.eval, jCurAfter, Join.curAfter, c0,
        Function.update_of_ne (show rCo ≠ rK by decide),
        Function.update_of_ne (show rCl ≠ rK by decide),
        Function.update_of_ne (show rCs ≠ rK by decide)],
      rfl, rfl, fun q hq => by
        simp only [pJScan, wReg, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hq
        simp [s0, Function.update_of_ne (Ne.symm hq.1)]⟩
  obtain ⟨s', r', ⟨hk, hn, -, hx, ha, hS, -, hp, ho, he⟩, hc⟩ := hloop
  have hkn : s'.env rK = n := by
    simp only [Ex.eval, rv, hn] at hc; split_ifs at hc with h <;> omega
  refine ⟨s', (r0.seq r').mono ?_, ?_, ?_, hS, hp, ho, he⟩
  · have h0 : n - s0.env rK = n := by simp [s0, Ex.eval]
    rw [h0]; simp only [condCost, rv, Ex.size]; nlinarith
  · rw [hx, hkn]; simp [n]
  · rw [ha, hkn, List.take_of_length_le (le_of_eq rfl)]

end Lax119563Proofs.Compiler

end Compiler_PJoin

/-! ### Formerly `Lax119563Proofs.Compiler.PReqBits` -/

section Compiler_PReqBits

/-!
# Pass `P3`, request generation: registers, stacks and the bit loop

The request of a column `c` of a schema for the argument with permutation
`π = (f, δ)` and location `u` is `u :: f(c.1) :: bits of (c.2 + δ_{c.1}) ++ [1, seq, 0, 0]`.
The bits of `c.2 + δ_{c.1}` are computed by `p3Bits`: it pops the bits of the column from
`qDom2` (pushing them onto `qDom`), the bits of the shift from `qDl2` (pushing them onto
`qAux`) and pushes their sums mod `2` onto `qRec` (**`p3Bits_good`**).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

/-! ## Stacks and registers of the request generation -/

def qF : Fin CQ := 5
def qF2 : Fin CQ := 6
def qDl : Fin CQ := 7
def qDl2 : Fin CQ := 8
def qAux : Fin CQ := 9
def qLs : Fin CQ := 10
def qLs2 : Fin CQ := 11
def qDom : Fin CQ := 14
def qDom2 : Fin CQ := 15

def rU : Fin CR := 20
def rFi : Fin CR := 21
def rCur : Fin CR := 22
def rGb : Fin CR := 23
def rGx : Fin CR := 24
def rDb : Fin CR := 25
def rSq : Fin CR := 26
def rStr : Fin CR := 27
def rAi : Fin CR := 28
def rTn : Fin CR := 29
def rNw : Fin CR := 30
def rKL : Fin CR := 31
def rGj : Fin CR := 32
def rI2 : Fin CR := 33
def rT2 : Fin CR := 35

open CStm

/-- Bitwise sums mod `2`. -/
def xorL (bs ds : List ℕ) : List ℕ := List.zipWith (fun a b => (a + b) % 2) bs ds

lemma xorL_take_succ (bs ds : List ℕ) {j : ℕ} (h1 : j < bs.length) (h2 : j < ds.length) :
    xorL (bs.take (j + 1)) (ds.take (j + 1)) =
      xorL (bs.take j) (ds.take j) ++ [(bs[j] + ds[j]) % 2] := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2]
  simp only [Option.toList_some, xorL]
  rw [List.zipWith_append (by simp; omega)]
  rfl

/-- One bit. -/
def p3Bit : CStm CR CQ :=
  .seq (.pop qDom2 rGx) (.seq (.push qDom (rv rGx)) (.seq (.pop qDl2 rDb)
    (.seq (.push qAux (rv rDb)) (.seq (.push qRec (.odd (.add (rv rGx) (rv rDb))))
      (.set rI (.add (rv rI) (.const 1)))))))

/-- The bit loop. -/
def p3Bits : CStm CR CQ := .seq (.set rI (.const 0)) (.loop (.lt (rv rI) (rv rL)) p3Bit)

/-- The stacks after `j` bits. -/
def bitsStk (S : Fin CQ → List ℕ) (j : ℕ) : Fin CQ → List ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update S
    qDom2 ((S qDom2).drop j)) qDom (((S qDom2).take j).reverse ++ S qDom))
    qDl2 ((S qDl2).drop j)) qAux (((S qDl2).take j).reverse ++ S qAux))
    qRec ((xorL ((S qDom2).take j) ((S qDl2).take j)).reverse ++ S qRec)

lemma bitsStk_zero (S : Fin CQ → List ℕ) : bitsStk S 0 = S := by
  funext q
  simp only [bitsStk, List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append, xorL,
    List.zipWith_nil_left]
  simp [Function.update_eq_self]

set_option maxHeartbeats 1000000 in
/-- **The bit loop.** -/
lemma p3Bits_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) {ℓ : ℕ}
    (hL : st.env rL = ℓ) (h1 : ℓ ≤ (st.stk qDom2).length) (h2 : ℓ ≤ (st.stk qDl2).length)
    (hb1 : ∀ v ∈ (st.stk qDom2).take ℓ, v ≤ 1) (hb2 : ∀ v ∈ (st.stk qDl2).take ℓ, v ≤ 1)
    (hℓw : ℓ + 1 < 2 ^ w) :
    ∃ st', Good x w p3Bits st st' ((ℓ + 1) * (20 * Ex.nodeCost w)) ∧
      st'.stk = bitsStk st.stk ℓ ∧ st'.pos = st.pos ∧ st'.out = st.out ∧
      ∀ r, wReg r p3Bits = false → st'.env r = st.env r := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  set S := st.stk
  set Inv : NSt CR CQ → Prop := fun s => s.env rI ≤ ℓ ∧ s.env rL = ℓ ∧
    s.stk = bitsStk S (s.env rI) ∧ s.pos = st.pos ∧ s.out = st.out with hInv
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv rI) (rv rL)) (body := p3Bit)
    Inv (fun s => ℓ - s.env rI) (fun _ => 0) 0 (16 * Ex.nodeCost w) (by
      intro s ⟨hi, hl, hs, hp, ho⟩
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hcond
      have hlt : s.env rI < ℓ := by simpa [rv, Ex.eval, hl] using hcond
      set j := s.env rI with hj
      have hd1 : (S qDom2).drop j = (S qDom2)[j] :: (S qDom2).drop (j + 1) :=
        List.drop_eq_getElem_cons (by omega)
      have hd2 : (S qDl2).drop j = (S qDl2)[j] :: (S qDl2).drop (j + 1) :=
        List.drop_eq_getElem_cons (by omega)
      have hv1 : (S qDom2)[j] ≤ 1 :=
        hb1 _ (List.mem_take_iff_getElem.mpr ⟨j, by simp; omega, rfl⟩)
      have hv2 : (S qDl2)[j] ≤ 1 :=
        hb2 _ (List.mem_take_iff_getElem.mpr ⟨j, by simp; omega, rfl⟩)
      have e1 : s.stk qDom2 = (S qDom2)[j] :: (S qDom2).drop (j + 1) := by
        rw [hs, ← hd1]; simp [bitsStk, qRec, qAux, qDl2, qDom, qDom2]
      have r1 := Good.pop_cons (x := x) (w := w) (r := rGx) e1
      set s1 := (s.setS qDom2 ((S qDom2).drop (j + 1))).set rGx (S qDom2)[j]
      have r2 := Good.push (x := x) (w := w) (q := qDom) (e := rv rGx) (st := s1)
        (by simp only [Ex.Fits, rv, s1, NSt.set_env, Function.update_self]; omega)
      set s2 := s1.setS qDom ((rv rGx : Ex CR).eval s1.env :: s1.stk qDom)
      have e2 : s2.stk qDl2 = (S qDl2)[j] :: (S qDl2).drop (j + 1) := by
        simp only [s2, s1, NSt.setS_stk, NSt.set_stk]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hs, ← hd2]
        simp [bitsStk, qRec, qAux, qDl2, qDom, qDom2]
      have r3 := Good.pop_cons (x := x) (w := w) (r := rDb) e2
      set s3 := (s2.setS qDl2 ((S qDl2).drop (j + 1))).set rDb (S qDl2)[j]
      have r4 := Good.push (x := x) (w := w) (q := qAux) (e := rv rDb) (st := s3)
        (by simp only [Ex.Fits, rv, s3, NSt.set_env, Function.update_self]; omega)
      set s4 := s3.setS qAux ((rv rDb : Ex CR).eval s3.env :: s3.stk qAux)
      have eB : s4.env rGx = (S qDom2)[j] := by
        simp [s4, s3, s2, s1, Function.update_of_ne (show rGx ≠ rDb by decide)]
      have eD : s4.env rDb = (S qDl2)[j] := by simp [s4, s3]
      have r5 := Good.push (x := x) (w := w) (q := qRec) (e := .odd (.add (rv rGx) (rv rDb)))
        (st := s4) (by
          simp only [Ex.Fits, Ex.eval, rv, eB, eD]
          have := Nat.mod_lt ((S qDom2)[j] + (S qDl2)[j]) (show 2 > 0 by norm_num)
          (repeat' constructor) <;> omega)
      set s5 := s4.setS qRec ((Ex.odd (.add (rv rGx) (rv rDb)) : Ex CR).eval s4.env :: s4.stk qRec)
      have eI : s5.env rI = j := by
        show Function.update (Function.update s.env rGx (S qDom2)[j]) rDb (S qDl2)[j] rI = j
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      have r6 := Good.set (x := x) (w := w) (r := rI) (e := .add (rv rI) (.const 1)) (st := s5)
        (by simp only [Ex.Fits, Ex.eval, rv, eI]; omega)
      refine ⟨_, ((r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6)))))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_⟩,
        ?_, le_rfl⟩
      · simp only [rv, Ex.size]; omega
      · simp only [NSt.set_env, Function.update_self, Ex.eval, rv, eI]; omega
      · simp only [NSt.set_env, Function.update_of_ne (show rL ≠ rI by decide)]
        simp [s5, s4, s3, s2, s1, Function.update_of_ne (show rL ≠ rDb by decide),
          Function.update_of_ne (show rL ≠ rGx by decide), hl]
      · simp only [NSt.set_env, Function.update_self, Ex.eval, rv, eI, NSt.set_stk]
        funext q
        by_cases q1 : q = qRec
        · subst q1
          simp [s5, s4, s3, s2, s1, hs, bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_self, Ex.eval, rv,
            eB, eD, Function.update_of_ne (show rGx ≠ rDb by decide)]
          rw [xorL_take_succ _ _ (by omega) (by omega)]; simp
        by_cases q2 : q = qAux
        · subst q2
          simp [s5, s4, s3, s2, s1, hs, bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_self, Ex.eval, rv, Function.update_of_ne (show rGx ≠ rDb by decide)]
          rw [List.take_add_one, List.getElem?_eq_getElem (show j < (S qDl2).length by omega)]
          simp only [Option.toList_some, List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]
        by_cases q3 : q = qDl2
        · subst q3
          simp [s5, s4, s3, s2, s1, hs, bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_self]
        by_cases q4 : q = qDom
        · subst q4
          simp [s5, s4, s3, s2, s1, hs, bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_self, Ex.eval, rv, Function.update_of_ne (show rGx ≠ rDb by decide)]
          rw [List.take_add_one, List.getElem?_eq_getElem (show j < (S qDom2).length by omega)]
          simp only [Option.toList_some, List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]
        by_cases q5 : q = qDom2
        · subst q5
          simp [s5, s4, s3, s2, s1, hs, bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_self]
        simp [s5, s4, s3, s2, s1, hs, bitsStk, Function.update_apply, q1, q2, q3, q4, q5]
      · simp [s5, s4, s3, s2, s1, hp]
      · simp [s5, s4, s3, s2, s1, ho]
      · simp only [NSt.set_env, Function.update_self, Ex.eval, rv, eI]; omega)
  have r0 := Good.set (x := x) (w := w) (r := rI) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  obtain ⟨s', r', ⟨hi, hl, hs, hp, ho⟩, hc⟩ := hloop (st.set rI 0) ⟨by simp,
    by simp [Function.update_of_ne (show rL ≠ rI by decide), hL],
    by simp [bitsStk_zero, S], rfl, rfl⟩
  have hiℓ : s'.env rI = ℓ := by
    simp only [Ex.eval, rv, hl] at hc; split_ifs at hc with h <;> omega
  have hall := r0.seq r'
  refine ⟨s', hall.mono ?_, by rw [hs, hiℓ], hp, ho, fun r hr => hall.env_of hr⟩
  simp only [condCost, rv, Ex.size, Ex.eval, NSt.set_env, Function.update_self, Nat.sub_zero,
    mul_zero, zero_add]
  nlinarith

end Lax119563Proofs.Compiler

end Compiler_PReqBits

/-! ### Formerly `Lax119563Proofs.Compiler.PSchSize` -/

section Compiler_PSchSize

/-!
# Sizes of the schema sections (list level, for pass `P2`)

With `M = k - 1 + ℓ` check rows, row `j < k - 1` is nonzero at `c` iff `c.1 = j` or
`c.1 = k - 1`, and row `k - 1 + t` iff `c.2 t ≠ 0` (`ent_ne_zero_iff`). Hence

* `(stepsC c).length = (k + 1) · rowsC c` with `rowsC c = [c.1 + 1 < k ? 1 : k - 1] + popc c.2`
  (`length_stepsC`), so `nEnt I e = (k + 1) Σ_c rowsC c` (`nEnt_eq`);
* `(coefSteps I e).length = (k + 1) (blkRows + orPop)` (`length_coefSteps`), where the
  block rows are `k - 1` if some coordinate lies in block `k - 1` and the number of distinct
  blocks otherwise (`blkRows_eq`), and `orPop` counts the bits set in some coordinate;
* `schSize I e = |D| (tern ? 8 : 2) + 6 nEnt + 2 |coefSteps|` (`schSize_eq'`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ}

/-! ## Rows of the check matrix -/

/-- Row `j` of the check matrix is nonzero at `c`. -/
abbrev rowNZ (j : ℕ) (c : Coord k ℓ) : Prop :=
  (j < k - 1 ∧ ((c.1 : ℕ) = j ∨ (c.1 : ℕ) = k - 1)) ∨
    (k - 1 ≤ j ∧ ∃ t : Fin ℓ, (t : ℕ) = j - (k - 1) ∧ c.2 t ≠ 0)

lemma zmod2_ite_ne_zero (P : Prop) [Decidable P] :
    ((if P then 1 else 0 : ZMod 2) ≠ 0) ↔ P := by
  split_ifs with h <;> simp [h]

lemma ent_ne_zero_iff (σ : ℕ) (c : Coord k ℓ) :
    ent σ c ≠ 0 ↔ rowNZ (σ % (k - 1 + ℓ)) c := by
  unfold ent
  by_cases h : 0 < k - 1 + ℓ
  · rw [dif_pos h]
    have hjM : σ % (k - 1 + ℓ) < k - 1 + ℓ := Nat.mod_lt _ h
    unfold stepRow
    by_cases hj1 : σ % (k - 1 + ℓ) < k - 1
    · rw [show (⟨σ % (k - 1 + ℓ), Nat.mod_lt _ h⟩ : Fin (k - 1 + ℓ)) =
          Fin.castAdd ℓ ⟨σ % (k - 1 + ℓ), hj1⟩ from rfl, finSumFinEquiv_symm_apply_castAdd]
      simp only [checkMatrix, Matrix.of_apply, zmod2_ite_ne_zero, rowNZ, hj1, true_and]
      constructor
      · intro h'; exact Or.inl h'
      · rintro (h' | ⟨h', -⟩)
        · exact h'
        · omega
    · rw [show (⟨σ % (k - 1 + ℓ), Nat.mod_lt _ h⟩ : Fin (k - 1 + ℓ)) =
          Fin.natAdd (k - 1) ⟨σ % (k - 1 + ℓ) - (k - 1), by omega⟩ from Fin.ext (by simp; omega),
        finSumFinEquiv_symm_apply_natAdd]
      simp only [checkMatrix, Matrix.of_apply, rowNZ, hj1, false_and, false_or]
      constructor
      · intro h'; exact ⟨by omega, _, rfl, h'⟩
      · rintro ⟨-, t, ht, h'⟩
        have : t = ⟨σ % (k - 1 + ℓ) - (k - 1), by omega⟩ := Fin.ext ht
        rw [← this]; exact h'
  · rw [dif_neg h]
    have hk : k - 1 = 0 := by omega
    have hl : ℓ = 0 := by omega
    subst hl
    constructor
    · intro h'; exact absurd rfl h'
    · rintro (⟨h', -⟩ | ⟨-, t, -⟩)
      · omega
      · exact t.elim0

/-- Counting steps by their row. -/
lemma countP_range_mod (M : ℕ) (P : ℕ → Bool) : ∀ n : ℕ,
    (List.range (n * M)).countP (fun σ => P (σ % M)) = n * (List.range M).countP P
  | 0 => by simp
  | n + 1 => by
    rw [show (n + 1) * M = n * M + M by ring, List.range_add, List.countP_append,
      countP_range_mod M P n, List.countP_map]
    have : (List.range M).countP ((fun σ => P (σ % M)) ∘ (fun j => n * M + j)) =
        (List.range M).countP P := by
      refine List.countP_congr fun j hj => ?_
      rw [List.mem_range] at hj
      simp only [Function.comp_apply, Nat.mul_add_mod_of_lt hj]
    rw [this]; ring

/-- The number of set bits of a block coordinate. -/
def popc (b : BlockCoord ℓ) : ℕ := (List.finRange ℓ).countP fun t => b t ≠ 0

lemma sum_blockDescription (b : BlockCoord ℓ) : (blockDescription b).sum = popc b := by
  unfold blockDescription popc
  induction (List.finRange ℓ) with
  | nil => rfl
  | cons t ts ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    rcases zmod2_cases (b t) with h | h <;> simp [h, show (1 : ZMod 2).val = 1 from rfl]; ring

/-- The number of nonzero rows of column `c`. -/
def rowsC (c : Coord k ℓ) : ℕ := (if (c.1 : ℕ) + 1 < k then 1 else k - 1) + popc c.2

lemma range_split (k ℓ : ℕ) :
    List.range (k - 1 + ℓ) = List.range (k - 1) ++ (List.range ℓ).map fun t => k - 1 + t := by
  rw [List.range_add]

lemma countP_range_eq (n a : ℕ) : (List.range n).countP (fun j => decide (a = j)) =
    if a < n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases h : a = n
    · subst h; simp
    · have : ¬ a < n + 1 ∨ a < n := by omega
      rcases this with h1 | h1
      · rw [if_neg (by omega), if_neg h1]; simp [h]
      · rw [if_pos h1, if_pos (by omega)]; simp [h]

lemma countP_finRange (ℓ : ℕ) (p : Fin ℓ → Prop) [DecidablePred p] :
    (List.range ℓ).countP (fun t => decide (∃ t' : Fin ℓ, (t' : ℕ) = t ∧ p t')) =
      (List.finRange ℓ).countP fun t => decide (p t) := by
  rw [← map_val_finRange, List.countP_map]
  refine List.countP_congr fun t _ => ?_
  simp only [Function.comp_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨t', ht, hp⟩; rw [← Fin.ext ht]; exact hp
  · intro hp; exact ⟨t, rfl, hp⟩

lemma countP_rowNZ (c : Coord k ℓ) :
    (List.range (k - 1 + ℓ)).countP (fun j => decide (rowNZ j c)) = rowsC c := by
  rw [range_split, List.countP_append, List.countP_map]
  have h1 : (List.range (k - 1)).countP (fun j => decide (rowNZ j c)) =
      if (c.1 : ℕ) + 1 < k then 1 else k - 1 := by
    have hc := c.1.2
    split_ifs with hk
    · have e := countP_range_eq (k - 1) (c.1 : ℕ)
      rw [if_pos (show (c.1 : ℕ) < k - 1 by omega)] at e
      refine Eq.trans (List.countP_congr fun j hj => ?_) e
      rw [List.mem_range] at hj
      simp only [rowNZ, decide_eq_true_eq]
      constructor
      · rintro (⟨-, h | h⟩ | ⟨h, -⟩)
        · exact h
        · omega
        · omega
      · intro h; exact Or.inl ⟨hj, Or.inl h⟩
    · rw [List.countP_eq_length.mpr, List.length_range]
      intro j hj
      rw [List.mem_range] at hj
      simp only [rowNZ, decide_eq_true_eq]
      left; exact ⟨hj, Or.inr (by omega)⟩
  have h2 : (List.range ℓ).countP ((fun j => decide (rowNZ j c)) ∘ fun t => k - 1 + t) =
      popc c.2 := by
    rw [popc, ← countP_finRange ℓ (fun t => c.2 t ≠ 0)]
    refine List.countP_congr fun t _ => ?_
    simp only [Function.comp_apply, rowNZ, decide_eq_true_eq]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, t', ht, h⟩)
      · omega
      · exact ⟨t', by omega, h⟩
    · rintro ⟨t', ht, h⟩
      exact Or.inr ⟨by omega, t', by omega, h⟩
  rw [h1, h2, rowsC]

/-- **The number of steps of a column.** -/
lemma length_stepsC (c : Coord k ℓ) : (stepsC c).length = (k + 1) * rowsC c := by
  rw [stepsC, ← List.countP_eq_length_filter, numSteps, ← countP_rowNZ c,
    ← countP_range_mod (k - 1 + ℓ) (fun j => decide (rowNZ j c)) (k + 1)]
  refine List.countP_congr fun σ _ => ?_
  simp only [ne_eq, decide_eq_true_eq, ← ent_ne_zero_iff]

/-! ## Schema sizes -/

variable (I : ImplicitParitySystem k ℓ)

/-- The sum of the row counts of the columns. -/
def rowsSum (cs : List (Coord k ℓ)) : ℕ := (cs.map rowsC).sum

lemma nEnt_eq (e : Fin I.schemas.length) : nEnt I e = (k + 1) * rowsSum (coordList (dom I e)) := by
  rw [nEnt, rowsSum, ← List.sum_map_mul_left]
  congr 1
  exact List.map_congr_left fun c _ => length_stepsC c

/-- The block rows that are nonzero on a list of coordinates. -/
def blkRows (cs : List (Coord k ℓ)) : ℕ :=
  (List.range (k - 1)).countP fun j => decide (∃ c ∈ cs, (c.1 : ℕ) = j ∨ (c.1 : ℕ) = k - 1)

/-- The bits set in some coordinate of a list. -/
def orPop (cs : List (Coord k ℓ)) : ℕ :=
  (List.finRange ℓ).countP fun t => decide (∃ c ∈ cs, c.2 t ≠ 0)

lemma countP_rowNZ_ex (cs : List (Coord k ℓ)) :
    (List.range (k - 1 + ℓ)).countP (fun j => decide (∃ c ∈ cs, rowNZ j c)) =
      blkRows cs + orPop cs := by
  rw [range_split, List.countP_append, List.countP_map]
  congr 1
  · refine List.countP_congr fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [rowNZ, decide_eq_true_eq, hj, true_and, not_le.mpr hj, false_and, or_false]
  · rw [orPop, ← countP_finRange ℓ (fun t => ∃ c ∈ cs, c.2 t ≠ 0)]
    refine List.countP_congr fun t _ => ?_
    simp only [Function.comp_apply, rowNZ, decide_eq_true_eq]
    constructor
    · rintro ⟨c, hc, ⟨h, -⟩ | ⟨-, t', ht, h⟩⟩
      · omega
      · exact ⟨t', by omega, c, hc, h⟩
    · rintro ⟨t', ht, c, hc, h⟩
      exact ⟨c, hc, Or.inr ⟨by omega, t', by omega, h⟩⟩

open Classical in
/-- **The number of coefficient steps.** -/
lemma length_coefSteps (e : Fin I.schemas.length) :
    (coefSteps I e).length = (k + 1) * (blkRows (coordList (dom I e)) +
      orPop (coordList (dom I e))) := by
  rw [coefSteps, ← List.countP_eq_length_filter, numSteps, ← countP_rowNZ_ex,
    ← countP_range_mod (k - 1 + ℓ) _ (k + 1)]
  refine List.countP_congr fun σ _ => ?_
  simp only [decide_eq_true_eq, ← ent_ne_zero_iff, mem_coordList]

lemma schSize_eq' (e : Fin I.schemas.length) :
    schSize I e = (coordList (dom I e)).length * (if Matrix.isTern (sch I e) then 8 else 2) +
      6 * nEnt I e + 2 * (coefSteps I e).length := by
  rw [schSize_eq, hubSize, sumSize, colW]
  split_ifs <;> ring

/-! ## The distinct blocks of a sorted list -/

/-- The number of changes of value along a list, starting from `p`. -/
def dChg : ℕ → List ℕ → ℕ
  | _, [] => 0
  | p, i :: is => (if i = p then 0 else 1) + dChg i is

lemma dChg_eq : ∀ (p : ℕ) (l : List ℕ), l.Pairwise (· ≤ ·) → ((∀ x ∈ l, p ≤ x) ∨ p ∉ l) →
    dChg p l = (l.toFinset.erase p).card
  | _, [], _, _ => rfl
  | p, i :: is, hs, hp => by
    rw [List.pairwise_cons] at hs
    rw [dChg, dChg_eq i is hs.2 (Or.inl hs.1), List.toFinset_cons]
    by_cases hip : i = p
    · subst hip; rw [if_pos rfl, Finset.erase_insert_eq_erase]; ring
    · have hpn : p ∉ insert i is.toFinset := by
        rw [Finset.mem_insert, List.mem_toFinset, not_or]
        refine ⟨Ne.symm hip, fun h => ?_⟩
        rcases hp with hp | hp
        · have h1 := hp i List.mem_cons_self
          have h2 := hs.1 p h
          omega
        · exact hp (List.mem_cons_of_mem _ h)
      rw [if_neg hip, Finset.erase_eq_of_notMem hpn]
      by_cases hi : i ∈ is.toFinset
      · rw [Finset.insert_eq_of_mem hi, ← Finset.card_erase_add_one hi]; ring
      · rw [Finset.card_insert_of_notMem hi, Finset.erase_eq_of_notMem hi]; ring

/-- The blocks of `coordList D` are nondecreasing. -/
lemma pairwise_blocks (D : Finset (Coord k ℓ)) :
    ((coordList D).map fun c => (c.1 : ℕ)).Pairwise (· ≤ ·) := by
  have hpw : ((coordList D).map coordNum).Pairwise (· < ·) :=
    pairwise_map_coordNum_allCoords.sublist ((List.filter_sublist).map _)
  rw [List.pairwise_map] at hpw ⊢
  refine hpw.imp fun {a b} h => ?_
  rw [← coordNum_div a, ← coordNum_div b]
  exact Nat.div_le_div_right h.le

/-- **The block rows** by the scan: `k - 1` if block `k - 1` occurs, else the number of
changes of the block along the list (from the start value `k`). -/
lemma blkRows_eq (D : Finset (Coord k ℓ)) :
    blkRows (coordList D) = if ∃ c ∈ coordList D, ¬ (c.1 : ℕ) + 1 < k then k - 1 else
      dChg k ((coordList D).map fun c => (c.1 : ℕ)) := by
  set cs := coordList D
  split_ifs with h
  · obtain ⟨c, hc, hl⟩ := h
    rw [blkRows, List.countP_eq_length.mpr, List.length_range]
    intro j _
    simp only [decide_eq_true_eq]
    exact ⟨c, hc, Or.inr (by have := c.1.2; omega)⟩
  · push_neg at h
    rw [dChg_eq k _ (pairwise_blocks D) (Or.inr (by
      simp only [List.mem_map, not_exists, not_and]
      intro c _ hck; have := c.1.2; omega))]
    have hnk : k ∉ (cs.map fun c => (c.1 : ℕ)).toFinset := by
      simp only [List.mem_toFinset, List.mem_map, not_exists, not_and]
      intro c _ hck; have := c.1.2; omega
    rw [Finset.erase_eq_of_notMem hnk, blkRows, List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
    congr 1
    ext j
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq,
      List.mem_map]
    constructor
    · rintro ⟨-, c, hc, hj | hj⟩
      · exact ⟨c, hc, hj⟩
      · have := h c hc; omega
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by have := h c hc; omega, c, hc, Or.inl rfl⟩

/-! ## The OR of the block coordinates -/

/-- The OR of the bits of a list of coordinates. -/
def orsL (cs : List (Coord k ℓ)) : List ℕ :=
  (List.finRange ℓ).map fun t => if ∃ c ∈ cs, c.2 t ≠ 0 then 1 else 0

/-- Bitwise or of two bits. -/
def bor (a b : ℕ) : ℕ := if 0 < a + b then 1 else 0

lemma orsL_nil : orsL ([] : List (Coord k ℓ)) = List.replicate ℓ 0 := by
  simp [orsL, List.map_const']

lemma length_orsL (cs : List (Coord k ℓ)) : (orsL cs).length = ℓ := by simp [orsL]

lemma orsL_append (cs : List (Coord k ℓ)) (c : Coord k ℓ) :
    orsL (cs ++ [c]) = List.zipWith bor (orsL cs) (blockDescription c.2) := by
  unfold orsL blockDescription
  rw [List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun t _ => ?_
  have hv := ZMod.val_lt (c.2 t)
  simp only [List.mem_append, List.mem_singleton, bor]
  by_cases h : ∃ c' ∈ cs, c'.2 t ≠ 0
  · obtain ⟨c', hc', h'⟩ := h
    have h1 : ∃ c'' : Coord k ℓ, (c'' ∈ cs ∨ c'' = c) ∧ c''.2 t ≠ 0 := ⟨c', Or.inl hc', h'⟩
    have h2 : ∃ c'' ∈ cs, c''.2 t ≠ 0 := ⟨c', hc', h'⟩
    rw [if_pos h1, if_pos h2, if_pos (by omega)]
  · rw [if_neg h]
    by_cases hc : c.2 t = 0
    · rw [if_neg, if_neg]
      · rw [hc]; simp
      · rintro ⟨c', hc' | rfl, h'⟩
        · exact h ⟨c', hc', h'⟩
        · exact h' hc
    · have : (c.2 t).val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
      rw [if_pos ⟨c, Or.inr rfl, hc⟩, if_pos (by omega)]

lemma sum_orsL (cs : List (Coord k ℓ)) : (orsL cs).sum = orPop cs := by
  unfold orsL orPop
  induction (List.finRange ℓ) with
  | nil => rfl
  | cons t ts ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : ∃ c ∈ cs, c.2 t ≠ 0 <;> simp only [h, if_true, if_false] <;> simp <;> ring

end Lax119563Proofs.Compiler

end Compiler_PSchSize

/-! ### Formerly `Lax119563Proofs.Compiler.PSchDesc` -/

section Compiler_PSchDesc

/-!
# The schema section of the input (for pass `P2`)

`schD I e = a :: locations ++ |D| :: coordinates ++ permutations` with `a ∈ {2, 3}` the arity,
`a` locations and `a` permutation descriptions of `k + k ℓ` numbers each
(`schemaDescription_eq'`); the coordinates of `D` are listed as `cdesc c = c.1 :: b₀ … b_{ℓ-1}`
in the order of `coordList D` (`domainDescription_eq'`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ W : ℕ}

/-- The description of a coordinate: its block, then its bits. -/
def cdesc (c : Coord k ℓ) : List ℕ := (c.1 : ℕ) :: blockDescription c.2

lemma length_cdesc (c : Coord k ℓ) : (cdesc c).length = ℓ + 1 := by
  simp [cdesc, blockDescription]

lemma sortNums_eq (D : Finset (Coord k ℓ)) :
    (D.image coordNum).sort (· ≤ ·) = (coordList D).map coordNum := by
  have hpw : ((coordList D).map coordNum).Pairwise (· < ·) :=
    pairwise_map_coordNum_allCoords.sublist ((List.filter_sublist).map _)
  have hfs : ((coordList D).map coordNum).toFinset = D.image coordNum := by
    ext n; simp
  rw [← hfs]
  exact (List.toFinset_sort _ hpw.nodup).mpr (hpw.imp le_of_lt)

lemma coordNumDescription_coordNum (c : Coord k ℓ) :
    coordNumDescription ℓ (coordNum c) = cdesc c := by
  rw [coordNum, blockNum_eq_regVal, coordNumDescription_eq (regVal_lt c.2), cdesc,
    blockDescription_eq]

lemma domainDescription_eq' (D : Finset (Coord k ℓ)) :
    domainDescription D = (coordList D).length :: (coordList D).flatMap cdesc := by
  rw [domainDescription]
  simp only [sortNums_eq, List.length_map, List.flatMap_map, coordNumDescription_coordNum]

/-- The locations of a schema. -/
def schLocs : Schema k ℓ W → List ℕ
  | .binary u v .. => [u, v]
  | .ternary u v w' .. => [u, v, w']

/-- The permutations of a schema. -/
def schPerms : Schema k ℓ W → List (BlockPerm k ℓ)
  | .binary _ _ _ σ τ => [σ, τ]
  | .ternary _ _ _ _ σ τ π => [σ, τ, π]

/-- The arity of a schema. -/
def arity (s : Schema k ℓ W) : ℕ := if Matrix.isTern s then 3 else 2

lemma length_schLocs (s : Schema k ℓ W) : (schLocs s).length = arity s := by
  cases s <;> simp [schLocs, arity, Matrix.isTern]

lemma length_perms (s : Schema k ℓ W) :
    ((schPerms s).flatMap permDescription).length = arity s * (k + k * ℓ) := by
  cases s <;> simp [schPerms, arity, Matrix.isTern, length_permDescription] <;> ring

lemma schemaDescription_eq' (s : Schema k ℓ W) :
    schemaDescription s = arity s :: schLocs s ++
      ((coordList s.domain).length :: (coordList s.domain).flatMap cdesc) ++
        (schPerms s).flatMap permDescription := by
  cases s <;> simp [schemaDescription, arity, Matrix.isTern, schLocs, schPerms, Schema.domain,
    domainDescription_eq']

lemma schLocs_le (s : Schema k ℓ W) : ∀ u ∈ schLocs s, u < W := by
  cases s <;> simp [schLocs]

variable (I : ImplicitParitySystem k ℓ)

/-- The description of schema `e`. -/
def schD (e : Fin I.schemas.length) : List ℕ := schemaDescription (sch I e)

lemma schsDesc_eq : schsDesc I = (List.finRange I.schemas.length).flatMap (schD I) := by
  have : I.schemas = (List.finRange I.schemas.length).map (sch I) :=
    List.ext_getElem (by simp) fun i h1 h2 => by simp [sch]
  rw [schsDesc]
  conv_lhs => rw [this]
  rw [List.flatMap_map]; rfl

/-- The descriptions of the first `j` schemas. -/
def schsPre (j : ℕ) : List ℕ := ((List.finRange I.schemas.length).take j).flatMap (schD I)

/-- The descriptions of the schemas from `j` on. -/
def schsSuf (j : ℕ) : List ℕ := ((List.finRange I.schemas.length).drop j).flatMap (schD I)

lemma schsDesc_split (j : ℕ) : schsDesc I = schsPre I j ++ schsSuf I j := by
  rw [schsDesc_eq, schsPre, schsSuf, ← List.flatMap_append, List.take_append_drop]

lemma schsSuf_cons {j : ℕ} (hj : j < I.schemas.length) :
    schsSuf I j = schD I ⟨j, hj⟩ ++ schsSuf I (j + 1) := by
  rw [schsSuf, List.drop_eq_getElem_cons (by simpa using hj), List.flatMap_cons, schsSuf]
  simp

lemma schsPre_succ {j : ℕ} (hj : j < I.schemas.length) :
    schsPre I (j + 1) = schsPre I j ++ schD I ⟨j, hj⟩ := by
  rw [schsPre, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [schsPre]

/-- The position of the description of schema `j`. -/
def schAt (j : ℕ) : ℕ := schPos I + (encodeNats (schsPre I j)).length

lemma drop_schAt (j : ℕ) : (encodeSystem I).drop (schAt I j) = encodeNats (schsSuf I j) := by
  rw [schAt, ← List.drop_drop, drop_schPos, schsDesc_split I j, encodeNats_append,
    List.drop_left]

lemma schPos_add : schPos I + (encodeNats (schsDesc I)).length = H I := by
  show _ = (encodeSystem I).length
  rw [schPos, posAt, locsPre_all, encodeSystem_eq, sd_eq]
  simp only [encNats_cons, encodeNats_append, List.length_append, List.cons_append,
    List.nil_append, List.singleton_append]
  ring

lemma schAt_le (j : ℕ) : schAt I j ≤ H I := by
  have h2 := schPos_add I
  rw [schsDesc_split I j, encodeNats_append, List.length_append] at h2
  unfold schAt; omega

lemma schAt_succ {j : ℕ} (hj : j < I.schemas.length) :
    schAt I (j + 1) = schAt I j + (encodeNats (schD I ⟨j, hj⟩)).length := by
  simp only [schAt, schsPre_succ I hj, encodeNats_append, List.length_append]; ring

lemma schAt_zero : schAt I 0 = schPos I := by simp [schAt, schsPre, encodeNats]

lemma schD_le_H (e : Fin I.schemas.length) : (encodeNats (schD I e)).length ≤ H I := by
  have h := schAt_le I (e.val + 1)
  rw [schAt_succ I e.2] at h
  have : schAt I e.val ≥ 0 := Nat.zero_le _
  simp only [Fin.eta] at h
  omega

lemma schD_length_le (e : Fin I.schemas.length) : (schD I e).length ≤ H I :=
  (length_le_encodeNats _).trans (schD_le_H I e)

end Lax119563Proofs.Compiler

end Compiler_PSchDesc

/-! ### Formerly `Lax119563Proofs.Compiler.PReqList` -/

section Compiler_PReqList

/-!
# Pass `P3`, request generation: the list level

* `fL π`, `dL π`: the numbers `f(0), …, f(k-1)` and the shift descriptions of a block
  permutation (`permDescription π = fL π ++ (dL π).flatten`);
* `reqRec u π c s = u :: cdesc (π.apply c) ++ [1, s, 0, 0]`: the request of column `c` for the
  argument `(u, π)` with sequence number `s` (`reqRec_eq`: computed bitwise by `xorL`);
* `reqsE I e`: the requests of schema `e` (argument by argument, columns in the order of
  `coordList`), with sequence numbers `ansBase I e + seqOff …` in the order in which `P4`
  consumes the answers (ternary: per column `U, V, W`; binary: all `V`, then all `U`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ}

/-- The block images `f(0), …, f(k-1)`. -/
def fL (π : BlockPerm k ℓ) : List ℕ := (List.finRange k).map fun i => (π.perm i : ℕ)

/-- The shift descriptions `δ₀, …, δ_{k-1}`. -/
def dL (π : BlockPerm k ℓ) : List (List ℕ) :=
  (List.finRange k).map fun i => blockDescription (π.shift i)

lemma permDescription_eq (π : BlockPerm k ℓ) : permDescription π = fL π ++ (dL π).flatten := by
  simp [permDescription, fL, dL, List.flatMap_def]

lemma length_fL (π : BlockPerm k ℓ) : (fL π).length = k := by simp [fL]

lemma length_dL (π : BlockPerm k ℓ) : (dL π).length = k := by simp [dL]

lemma bd_add (b d : BlockCoord ℓ) :
    blockDescription (b + d) = xorL (blockDescription b) (blockDescription d) := by
  simp only [blockDescription, xorL, List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun t _ => ?_
  simp [ZMod.val_add]

/-- The request of column `c` for the argument `(u, π)` with sequence number `s`. -/
def reqRec (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) : List ℕ :=
  u :: cdesc (π.apply c) ++ [1, s, 0, 0]

lemma reqRec_eq (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) :
    reqRec u π c s = u :: (fL π).getD c.1 0 ::
      xorL (blockDescription c.2) ((dL π).getD c.1 []) ++ [1, s, 0, 0] := by
  simp [reqRec, cdesc, BlockPerm.apply, fL, dL, bd_add]

/-- The offset of the sequence number of argument `a` at column `r` (of `d` columns). -/
def seqOff (tern : Bool) (d a r : ℕ) : ℕ :=
  if tern then 3 * r + a else if a = 0 then d + r else r

variable (I : ImplicitParitySystem k ℓ)

/-- The number of requests of the first `j` schemas. -/
noncomputable def ansBase (j : ℕ) : ℕ :=
  (((List.finRange I.schemas.length).take j).map fun e =>
    arity (sch I e) * (coordList (dom I e)).length).sum

/-- The requests of schema `e`. -/
noncomputable def reqsE (e : Fin I.schemas.length) : List (List ℕ) :=
  ((schLocs (sch I e)).zip (schPerms (sch I e))).zipIdx.flatMap fun (p : (ℕ × BlockPerm k ℓ) × ℕ) =>
    (coordList (dom I e)).zipIdx.map fun (q : Coord k ℓ × ℕ) =>
      reqRec p.1.1 p.1.2 q.1
        (ansBase I e + seqOff (Matrix.isTern (sch I e)) (coordList (dom I e)).length p.2 q.2)

/-- The requests of the first `j` schemas. -/
noncomputable def reqsUpTo (j : ℕ) : List (List ℕ) :=
  ((List.finRange I.schemas.length).take j).flatMap (reqsE I)

/-- All requests. -/
noncomputable def reqs : List (List ℕ) := (List.finRange I.schemas.length).flatMap (reqsE I)

end Lax119563Proofs.Compiler

end Compiler_PReqList

/-! ### Formerly `Lax119563Proofs.Compiler.PJoinFacts` -/

section Compiler_PJoinFacts

/-!
# Pass `P3`: the list facts of the join

The union of the location records `locRecs I` and the requests `reqs I` satisfies the
hypotheses of `Join.scanF_eq` (keys of `ℓ + 2` words):
* `locRecs_eq`: `locRecs I` lists `locRecC I v c` (`v :: cdesc c ++ [0, off, labs, ι]`) for
  every location `v` and `c ∈ coordList (I.domain v)`;
* **`hG1`** (`locRec_unique`): a location record is determined by its key (`cdesc_injective`);
* **`hG2`** (`req_has_loc`): the key `u :: cdesc (π.apply c)` of every request is the key of a
  location record (`Schema.WellFormed`: `π.apply c ∈ I.domain u`);
* lengths `ℓ + 6` (`length_of_mem_union`), word bounds (`lt_of_mem_locRecs`,
  `lt_of_mem_reqs`), the number of requests (`length_reqs`, `ansBase_le_H`);
* **`p3_answers`**: for any permutation `L0` of `locRecs I ++ reqs I`, scanning
  `L0.mergeSort rle` and sorting the (reversed) answers by `rle` gives `ansAll I`, the answers
  in the order of `P4`: per schema (`ansE`), ternary: per column `U, V, W`; binary: all `V`,
  then all `U`; each answer is `ansRec I v c' s = [s, clsStart (coord v c') - locBase, labs,
  (initSeed I v c').val]` with `s` running through `0, 1, 2, …` (`map_head_ansAll`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## Location records -/

lemma cdesc_injective : Function.Injective (cdesc : Coord k ℓ → List ℕ) := by
  rintro ⟨i, b⟩ ⟨i', b'⟩ h
  simp only [cdesc, List.cons.injEq] at h
  obtain ⟨h1, h2⟩ := h
  refine Prod.ext (Fin.ext h1) (funext fun t => ?_)
  have := congrArg (fun l => l[(t : ℕ)]?) h2
  simp [blockDescription] at this
  exact ZMod.val_injective _ this

/-- The location record of the coordinate `c` of `v`. -/
noncomputable def locRecC (v : Fin I.numLocations) (c : Coord k ℓ) : List ℕ :=
  (v : ℕ) :: cdesc c ++ [0, locOff I v + (coordList (I.domain v)).idxOf c * labsN I v,
    labsN I v, initNum (I.init v)]

lemma locRec_eq (v : Fin I.numLocations) {r : ℕ} (hr : r < (coordList (I.domain v)).length) :
    locRec I v r = locRecC I v (coordList (I.domain v))[r] := by
  have hn : (locNums I v).getD r 0 = coordNum (coordList (I.domain v))[r] := by
    rw [locNums_eq, List.getD_eq_getElem _ _ (by simpa using hr)]; simp
  rw [locRec, locRecC, hn, coordNumDescription_coordNum,
    List.Nodup.idxOf_getElem (nodup_coordList _)]
  rfl

lemma recsV_eq (v : Fin I.numLocations) :
    recsV I v = (coordList (I.domain v)).map (locRecC I v) := by
  refine List.ext_getElem (by simp [recsV]) fun r h1 h2 => ?_
  simp only [recsV, List.getElem_map]
  rw [List.getElem_range]
  exact locRec_eq I v (by simpa using h2)

lemma locRecs_eq : locRecs I =
    (List.finRange I.numLocations).flatMap fun v => (coordList (I.domain v)).map (locRecC I v) := by
  rw [locRecs]; exact congrArg (fun f => List.flatMap f _) (funext (recsV_eq I))

lemma mem_locRecs {m : List ℕ} :
    m ∈ locRecs I ↔ ∃ v, ∃ c ∈ I.domain v, m = locRecC I v c := by
  rw [locRecs_eq]
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map, mem_coordList]
  constructor
  · rintro ⟨v, c, hc, rfl⟩; exact ⟨v, c, hc, rfl⟩
  · rintro ⟨v, c, hc, rfl⟩; exact ⟨v, c, hc, rfl⟩

lemma length_locRecC (v : Fin I.numLocations) (c : Coord k ℓ) :
    (locRecC I v c).length = ℓ + 6 := by
  simp [locRecC, length_cdesc]

lemma key_locRecC (v : Fin I.numLocations) (c : Coord k ℓ) :
    (locRecC I v c).take (ℓ + 2) = (v : ℕ) :: cdesc c := by
  rw [locRecC, List.cons_append, List.take_succ_cons,
    List.take_append_of_le_length (by simp [length_cdesc]),
    List.take_of_length_le (by simp [length_cdesc])]

lemma getD_rec (a : ℕ) (d : List ℕ) (x0 x1 x2 x3 i n : ℕ) (hn : n = d.length + 1 + i)
    (hi : i < 4) : (a :: d ++ [x0, x1, x2, x3]).getD n 0 = [x0, x1, x2, x3].getD i 0 := by
  rw [List.cons_append, hn, show d.length + 1 + i = (d.length + i) + 1 by omega]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by omega), show d.length + i - d.length = i by omega]

lemma isLoc_locRecC (v : Fin I.numLocations) (c : Coord k ℓ) :
    Join.isLoc (ℓ + 2) (locRecC I v c) = true := by
  have := getD_rec (v : ℕ) (cdesc c) 0 (locOff I v + (coordList (I.domain v)).idxOf c * labsN I v)
    (labsN I v) (initNum (I.init v)) 0 (ℓ + 2) (by simp [length_cdesc]) (by omega)
  simp only [Join.isLoc, locRecC, this]; rfl

/-! ## Requests -/

lemma length_reqRec (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) :
    (reqRec u π c s).length = ℓ + 6 := by
  simp [reqRec, length_cdesc]

lemma key_reqRec (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) :
    (reqRec u π c s).take (ℓ + 2) = u :: cdesc (π.apply c) := by
  rw [reqRec, List.cons_append, List.take_succ_cons,
    List.take_append_of_le_length (by simp [length_cdesc]),
    List.take_of_length_le (by simp [length_cdesc])]

lemma isLoc_reqRec (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) :
    Join.isLoc (ℓ + 2) (reqRec u π c s) = false := by
  have := getD_rec u (cdesc (π.apply c)) 1 s 0 0 0 (ℓ + 2) (by simp [length_cdesc]) (by omega)
  simp only [Join.isLoc, reqRec, this]; rfl

lemma mem_reqs {r : List ℕ} (hr : r ∈ reqs I) :
    ∃ e : Fin I.schemas.length, ∃ p ∈ (schLocs (sch I e)).zip (schPerms (sch I e)),
      ∃ c ∈ dom I e, ∃ s, r = reqRec p.1 p.2 c s := by
  simp only [reqs, reqsE, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hr
  obtain ⟨e, p, hp, q, hq, rfl⟩ := hr
  exact ⟨e, p.1, List.fst_mem_of_mem_zipIdx hp, q.1,
    mem_coordList.mp (List.fst_mem_of_mem_zipIdx hq), _, rfl⟩

/-- Well-formedness: the target of a column lies in the domain of the location. -/
lemma target_mem {W : ℕ} {dm : Fin W → Finset (Coord k ℓ)} {s : Schema k ℓ W}
    (hs : s.WellFormed dm) {p : ℕ × BlockPerm k ℓ} (hp : p ∈ (schLocs s).zip (schPerms s))
    {c : Coord k ℓ} (hc : c ∈ s.domain) : ∃ h : p.1 < W, p.2.apply c ∈ dm ⟨p.1, h⟩ := by
  cases s with
  | binary u v D σ τ =>
    simp only [schLocs, schPerms, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    obtain ⟨-, h1, h2⟩ := hs
    rcases hp with rfl | rfl
    · exact ⟨u.2, h1 (Finset.mem_image_of_mem _ hc)⟩
    · exact ⟨v.2, h2 (Finset.mem_image_of_mem _ hc)⟩
  | ternary u v w' D σ τ π =>
    simp only [schLocs, schPerms, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    obtain ⟨-, -, -, h1, h2, h3⟩ := hs
    rcases hp with rfl | rfl | rfl
    · exact ⟨u.2, h1 (Finset.mem_image_of_mem _ hc)⟩
    · exact ⟨v.2, h2 (Finset.mem_image_of_mem _ hc)⟩
    · exact ⟨w'.2, h3 (Finset.mem_image_of_mem _ hc)⟩

lemma wf_sch (e : Fin I.schemas.length) : (sch I e).WellFormed I.domain :=
  I.schema_wellFormed _ (List.get_mem _ _)

/-! ## The hypotheses of `Join.scanF_eq` -/

/-- The union of location records and requests. -/
noncomputable def union : List (List ℕ) := locRecs I ++ reqs I

lemma length_of_mem_union {r : List ℕ} (hr : r ∈ union I) : r.length = ℓ + 6 := by
  rcases List.mem_append.mp hr with h | h
  · obtain ⟨v, c, -, rfl⟩ := (mem_locRecs I).mp h; exact length_locRecC I v c
  · obtain ⟨e, p, -, c, -, s, rfl⟩ := mem_reqs I h; exact length_reqRec _ _ _ _

lemma isLoc_of_mem_union {r : List ℕ} (hr : r ∈ union I) :
    Join.isLoc (ℓ + 2) r = true ↔ r ∈ locRecs I := by
  constructor
  · intro hl
    rcases List.mem_append.mp hr with h | h
    · exact h
    · obtain ⟨e, p, -, c, -, s, rfl⟩ := mem_reqs I h
      rw [isLoc_reqRec] at hl; exact absurd hl (by simp)
  · intro h
    obtain ⟨v, c, -, rfl⟩ := (mem_locRecs I).mp h; exact isLoc_locRecC I v c

/-- **Keys are unique** among the location records. -/
lemma locRec_unique {m m' : List ℕ} (hm : m ∈ locRecs I) (hm' : m' ∈ locRecs I)
    (h : m.take (ℓ + 2) = m'.take (ℓ + 2)) : m = m' := by
  obtain ⟨v, c, -, rfl⟩ := (mem_locRecs I).mp hm
  obtain ⟨v', c', -, rfl⟩ := (mem_locRecs I).mp hm'
  rw [key_locRecC, key_locRecC, List.cons.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Fin.ext h1, cdesc_injective h2]

open Classical in
/-- The location record with a given key. -/
noncomputable def gLoc (key : List ℕ) : List ℕ :=
  if h : ∃ m' ∈ locRecs I, m'.take (ℓ + 2) = key then h.choose else []

lemma gLoc_eq {m : List ℕ} (hm : m ∈ locRecs I) : gLoc I (m.take (ℓ + 2)) = m := by
  have h : ∃ m' ∈ locRecs I, m'.take (ℓ + 2) = m.take (ℓ + 2) := ⟨m, hm, rfl⟩
  rw [gLoc, dif_pos h]
  exact locRec_unique I h.choose_spec.1 hm h.choose_spec.2

/-- `hG1`. -/
lemma hG1 : ∀ m ∈ union I, Join.isLoc (ℓ + 2) m = true → gLoc I (m.take (ℓ + 2)) = m :=
  fun _ hm hl => gLoc_eq I ((isLoc_of_mem_union I hm).mp hl)

/-- The location record answering the request of column `c` of argument `p` of schema `e`. -/
lemma req_loc {e : Fin I.schemas.length} {p : ℕ × BlockPerm k ℓ}
    (hp : p ∈ (schLocs (sch I e)).zip (schPerms (sch I e))) {c : Coord k ℓ} (hc : c ∈ dom I e)
    (s : ℕ) : ∃ h : p.1 < I.numLocations, p.2.apply c ∈ I.domain ⟨p.1, h⟩ ∧
      gLoc I ((reqRec p.1 p.2 c s).take (ℓ + 2)) = locRecC I ⟨p.1, h⟩ (p.2.apply c) := by
  obtain ⟨h, hd⟩ := target_mem (wf_sch I e) hp hc
  refine ⟨h, hd, ?_⟩
  rw [key_reqRec, show p.1 :: cdesc (p.2.apply c) =
    (locRecC I ⟨p.1, h⟩ (p.2.apply c)).take (ℓ + 2) by rw [key_locRecC]]
  exact gLoc_eq I ((mem_locRecs I).mpr ⟨_, _, hd, rfl⟩)

/-- `hG2`. -/
lemma hG2 : ∀ r ∈ union I, Join.isLoc (ℓ + 2) r = false →
    ∃ m ∈ union I, Join.isLoc (ℓ + 2) m = true ∧ m.take (ℓ + 2) = r.take (ℓ + 2) := by
  intro r hr hl
  have hr' : r ∈ reqs I := by
    rcases List.mem_append.mp hr with h | h
    · rw [(isLoc_of_mem_union I hr).mpr h] at hl; exact absurd hl (by simp)
    · exact h
  obtain ⟨e, p, hp, c, hc, s, rfl⟩ := mem_reqs I hr'
  obtain ⟨h, hd, -⟩ := req_loc I hp hc s
  refine ⟨locRecC I ⟨p.1, h⟩ (p.2.apply c),
    List.mem_append_left _ ((mem_locRecs I).mpr ⟨_, _, hd, rfl⟩), isLoc_locRecC I _ _, ?_⟩
  rw [key_locRecC, key_reqRec]

/-! ## The answers -/

/-- The answer `[s, off, labs, seed]` for the coordinate `c'` of location `v`. -/
noncomputable def ansRec (v : Fin I.numLocations) (c' : Coord k ℓ) (s : ℕ) : List ℕ :=
  [s, clsStart I (Cls.coord v c') - locBase I, labsN I v, (initSeed I v c').val]

/-- `ansRec` for a location given as a number. -/
noncomputable def ansU (u : ℕ) (c' : Coord k ℓ) (s : ℕ) : List ℕ :=
  if h : u < I.numLocations then ansRec I ⟨u, h⟩ c' s else []

@[simp] lemma ansU_fin (v : Fin I.numLocations) (c' : Coord k ℓ) (s : ℕ) :
    ansU I v c' s = ansRec I v c' s := by
  simp [ansU, v.2]

lemma seedV_eq (v : Fin I.numLocations) (c' : Coord k ℓ) :
    seedV c'.1 (initNum (I.init v)) = (initSeed I v c').val := by
  unfold initSeed
  have v0 : (0 : ZMod 2).val = 0 := rfl
  have v1 : (1 : ZMod 2).val = 1 := rfl
  rcases h : I.init v with _ | b
  · by_cases hc : (c'.1 : ℕ) = 0 <;> simp [seedV, initNum, hc, v0]
  · have hb : b = 0 ∨ b = 1 := by fin_cases b; exacts [Or.inl rfl, Or.inr rfl]
    rcases hb with rfl | rfl <;> by_cases hc : (c'.1 : ℕ) = 0 <;> simp [seedV, initNum, hc, v0, v1]

lemma off_eq {v : Fin I.numLocations} {c' : Coord k ℓ} (hc : c' ∈ I.domain v) :
    locOff I v + (coordList (I.domain v)).idxOf c' * labsN I v =
      clsStart I (Cls.coord v c') - locBase I := by
  rw [clsStart_coord I hc, locStart_eq, labsN]; omega

/-- The answer computed by the scan for a request `r` (`Join.scanF_eq` with `gLoc`). -/
noncomputable def ansF (r : List ℕ) : List ℕ := jAns ℓ (jCur ℓ (gLoc I (r.take (ℓ + 2)))) r

lemma jAns_locRecC {v : Fin I.numLocations} {c' : Coord k ℓ} (hc : c' ∈ I.domain v)
    (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) :
    jAns ℓ (jCur ℓ (locRecC I v c')) (reqRec u π c s) = ansRec I v c' s := by
  have h3 := getD_rec (v : ℕ) (cdesc c') 0 (locOff I v + (coordList (I.domain v)).idxOf c' *
    labsN I v) (labsN I v) (initNum (I.init v)) 1 (ℓ + 3) (by simp [length_cdesc]) (by omega)
  have h4 := getD_rec (v : ℕ) (cdesc c') 0 (locOff I v + (coordList (I.domain v)).idxOf c' *
    labsN I v) (labsN I v) (initNum (I.init v)) 2 (ℓ + 4) (by simp [length_cdesc]) (by omega)
  have h5 := getD_rec (v : ℕ) (cdesc c') 0 (locOff I v + (coordList (I.domain v)).idxOf c' *
    labsN I v) (labsN I v) (initNum (I.init v)) 3 (ℓ + 5) (by simp [length_cdesc]) (by omega)
  have hr := getD_rec u (cdesc (π.apply c)) 1 s 0 0 1 (ℓ + 3) (by simp [length_cdesc]) (by omega)
  have h1 : (locRecC I v c').getD 1 0 = c'.1 := by simp [locRecC, cdesc]
  rw [jAns, jCur, h1]
  rw [locRecC, reqRec]
  rw [h3, h4, h5, hr]
  simp [ansRec, seedV_eq, off_eq I hc]

lemma ansF_req {e : Fin I.schemas.length} {p : ℕ × BlockPerm k ℓ}
    (hp : p ∈ (schLocs (sch I e)).zip (schPerms (sch I e))) {c : Coord k ℓ} (hc : c ∈ dom I e)
    (s : ℕ) : ansF I (reqRec p.1 p.2 c s) = ansU I p.1 (p.2.apply c) s := by
  obtain ⟨h, hd, hg⟩ := req_loc I hp hc s
  rw [ansF, hg, jAns_locRecC I hd, ansU, dif_pos h]

lemma length_ansF (r : List ℕ) : (ansF I r).length = 4 := rfl

lemma headD_ansF (r : List ℕ) : (ansF I r).headD 0 = r.getD (ℓ + 3) 0 := rfl

/-! ## The answers in the order of `P4` -/

/-- **The answers of schema `e` in the order of `P4`**: ternary: per column the answers for
`U, V, W`; binary: the answers for `V` (all columns), then for `U`. Sequence numbers
`ansBase I e, ansBase I e + 1, …`. -/
noncomputable def ansE (e : Fin I.schemas.length) : List (List ℕ) :=
  match sch I e with
  | .binary u v D σ τ =>
      (coordList D).zipIdx.map (fun q => ansRec I v (τ.apply q.1) (ansBase I e + q.2)) ++
      (coordList D).zipIdx.map
        (fun q => ansRec I u (σ.apply q.1) (ansBase I e + (coordList D).length + q.2))
  | .ternary u v w' D σ τ π =>
      (coordList D).zipIdx.flatMap fun q =>
        [ansRec I u (σ.apply q.1) (ansBase I e + 3 * q.2),
         ansRec I v (τ.apply q.1) (ansBase I e + 3 * q.2 + 1),
         ansRec I w' (π.apply q.1) (ansBase I e + 3 * q.2 + 2)]

/-- **All answers in the order of `P4`.** -/
noncomputable def ansAll : List (List ℕ) := (List.finRange I.schemas.length).flatMap (ansE I)

lemma perm3 {α β : Type*} (x y z : α → β) :
    ∀ l : List α, (l.map x ++ (l.map y ++ l.map z)).Perm (l.flatMap fun a => [x a, y a, z a])
  | [] => by simp
  | a :: t => by
    have ih := perm3 x y z t
    simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append]
    refine List.Perm.cons _ ?_
    refine List.perm_middle.trans (List.Perm.cons _ ?_)
    rw [← List.append_assoc]
    refine List.perm_middle.trans (List.Perm.cons _ ?_)
    rw [List.append_assoc]
    exact ih

lemma map_reqsE_perm (e : Fin I.schemas.length) :
    ((reqsE I e).map (ansF I)).Perm (ansE I e) := by
  have hstep : (reqsE I e).map (ansF I) =
      ((schLocs (sch I e)).zip (schPerms (sch I e))).zipIdx.flatMap fun p =>
        (coordList (dom I e)).zipIdx.map fun q => ansU I p.1.1 (p.1.2.apply q.1)
          (ansBase I e + seqOff (Matrix.isTern (sch I e)) (coordList (dom I e)).length p.2 q.2) := by
    rw [reqsE, List.map_flatMap]
    refine List.flatMap_congr fun p hp => ?_
    rw [List.map_map]
    refine List.map_congr_left fun q hq => ?_
    exact ansF_req I (List.fst_mem_of_mem_zipIdx hp)
      (mem_coordList.mp (List.fst_mem_of_mem_zipIdx hq)) _
  rw [hstep]
  unfold ansE dom
  cases h : sch I e with
  | binary u v D σ τ =>
    simp only [schLocs, schPerms, List.zip_cons_cons, List.zip_nil_right, List.zipIdx_cons,
      List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, Matrix.isTern,
      seqOff, Schema.domain, ansU_fin, Bool.false_eq_true, if_false, if_true]
    refine List.perm_append_comm.trans (List.Perm.of_eq ?_)
    congr 1
    refine List.map_congr_left fun q _ => ?_
    simp [add_assoc]
  | ternary u v w' D σ τ π =>
    simp only [schLocs, schPerms, List.zip_cons_cons, List.zip_nil_right, List.zipIdx_cons,
      List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, Matrix.isTern,
      seqOff, Schema.domain, ansU_fin, if_true]
    refine List.Perm.trans (List.Perm.of_eq ?_) (perm3 _ _ _ _)
    simp [add_assoc]

lemma map_reqs_perm : ((reqs I).map (ansF I)).Perm (ansAll I) := by
  rw [reqs, List.map_flatMap]
  exact List.Perm.flatMap_left _ fun e _ => map_reqsE_perm I e

lemma length_reqs_eq : (reqs I).length = (ansAll I).length := by
  rw [← (map_reqs_perm I).length_eq, List.length_map]

/-! ## Sequence numbers -/

lemma map_zipIdx_add {α : Type*} (l : List α) (b : ℕ) :
    l.zipIdx.map (fun q => b + q.2) = List.range' b l.length := by
  have : l.zipIdx.map (fun q => b + q.2) = (l.zipIdx.map Prod.snd).map (b + ·) := by
    rw [List.map_map]; rfl
  rw [this, List.zipIdx_map_snd, List.map_add_range', add_zero]

lemma flatMap_zipIdx_three {α : Type*} (b : ℕ) : ∀ (l : List α) (i : ℕ),
    (l.zipIdx i).flatMap (fun q => [b + 3 * q.2, b + 3 * q.2 + 1, b + 3 * q.2 + 2]) =
      List.range' (b + 3 * i) (3 * l.length)
  | [], _ => by simp
  | a :: t, i => by
    rw [List.zipIdx_cons, List.flatMap_cons, flatMap_zipIdx_three b t (i + 1)]
    rw [show 3 * (a :: t).length = 3 * t.length + 1 + 1 + 1 by simp; ring]
    simp only [List.range'_succ, List.cons_append, List.nil_append]
    congr 3

lemma map_head_ansE (e : Fin I.schemas.length) :
    (ansE I e).map (·.headD 0) =
      List.range' (ansBase I e) (arity (sch I e) * (coordList (dom I e)).length) := by
  unfold ansE dom
  cases h : sch I e with
  | binary u v D σ τ =>
    simp only [List.map_append, List.map_map, Function.comp_def, ansRec, List.headD_cons,
      arity, Matrix.isTern, Schema.domain, Bool.false_eq_true, if_false]
    rw [map_zipIdx_add, map_zipIdx_add, List.range'_append_1]
    congr 1; ring
  | ternary u v w' D σ τ π =>
    simp only [List.map_flatMap, List.map_cons, List.map_nil, ansRec, List.headD_cons,
      arity, Matrix.isTern, Schema.domain, if_true]
    rw [flatMap_zipIdx_three, mul_zero, add_zero]

lemma ansBase_zero : ansBase I 0 = 0 := by simp [ansBase]

lemma ansBase_succ {j : ℕ} (hj : j < I.schemas.length) :
    ansBase I (j + 1) = ansBase I j +
      arity (sch I ⟨j, hj⟩) * (coordList (dom I ⟨j, hj⟩)).length := by
  rw [ansBase, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [ansBase]

lemma map_head_upTo : ∀ j, j ≤ I.schemas.length →
    (((List.finRange I.schemas.length).take j).flatMap (ansE I)).map (·.headD 0) =
      List.range' 0 (ansBase I j)
  | 0, _ => by simp [ansBase_zero]
  | j + 1, hj => by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
    simp only [List.getElem_finRange, Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, List.map_append, Fin.cast_mk]
    rw [map_head_upTo j (by omega), map_head_ansE, ansBase_succ I (by omega)]
    have := List.range'_append_1 (s := 0) (m := ansBase I j)
      (n := arity (sch I ⟨j, by omega⟩) * (coordList (dom I ⟨j, by omega⟩)).length)
    rw [zero_add] at this
    convert this using 2

/-- **The sequence numbers** of `ansAll I` are `0, 1, …, ansBase I E - 1`. -/
theorem map_head_ansAll :
    (ansAll I).map (·.headD 0) = List.range (ansBase I I.schemas.length) := by
  rw [ansAll, ← List.take_of_length_le (l := List.finRange _) (le_of_eq (List.length_finRange)),
    map_head_upTo I _ le_rfl, List.range_eq_range']

lemma length_of_mem_ansAll {a : List ℕ} (ha : a ∈ ansAll I) : a.length = 4 := by
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp ((map_reqs_perm I).mem_iff.mpr ha)
  exact length_ansF I r

lemma pairwise_ansAll : (ansAll I).Pairwise fun a b => CSort.rle a b = true := by
  have h := List.pairwise_lt_range (n := ansBase I I.schemas.length)
  rw [← map_head_ansAll, List.pairwise_map] at h
  refine h.imp_of_mem fun {a b} ha hb hab => ?_
  match a, b, length_of_mem_ansAll I ha, length_of_mem_ansAll I hb with
  | x :: as, y :: bs, _, _ =>
    simp only [List.headD_cons] at hab
    simp [CSort.rle, hab]

/-! ## The join -/

/-- **The answers of the join.** For any permutation `L0` of the location records and the
requests, the scan over `L0` sorted by `rle`, with its answers (pushed in reverse order) sorted
by `rle`, gives the answers in the order of `P4`. -/
theorem jScan_perm (L0 : List (List ℕ)) (hp : L0.Perm (union I)) (c0 : ℕ × ℕ × ℕ) :
    (jScan ℓ c0 (L0.mergeSort CSort.rle)).Perm (ansAll I) := by
  set S := L0.mergeSort CSort.rle
  have hS : S.Perm (union I) := (List.mergeSort_perm _ _).trans hp
  have hsorted : S.Pairwise fun a b => CSort.rle a b = true :=
    List.pairwise_mergeSort CSort.rle_trans (fun a b => by
      rcases CSort.rle_total a b with h | h <;> simp [h]) L0
  have hscan := Join.scanF_eq (ℓ + 2) (jCur ℓ) (jAns ℓ) (gLoc I) S
    (fun r hr => by rw [length_of_mem_union I (hS.mem_iff.mp hr)]; omega)
    (fun m hm hl => hG1 I m (hS.mem_iff.mp hm) hl)
    (fun r hr hl => by
      obtain ⟨m, hm, h1, h2⟩ := hG2 I r (hS.mem_iff.mp hr) hl
      exact ⟨m, hS.mem_iff.mpr hm, h1, h2⟩) hsorted c0
  have hfilt : (S.filter fun r => !Join.isLoc (ℓ + 2) r).Perm (reqs I) := by
    refine (hS.filter _).trans (List.Perm.of_eq ?_)
    rw [union, List.filter_append, List.filter_eq_nil_iff.mpr, List.filter_eq_self.mpr,
      List.nil_append]
    · intro r hr
      obtain ⟨e, p, -, c, -, s, rfl⟩ := mem_reqs I hr
      simp [isLoc_reqRec]
    · intro r hr
      obtain ⟨v, c, -, rfl⟩ := (mem_locRecs I).mp hr
      simp [isLoc_locRecC]
  rw [jScan, hscan]
  exact (hfilt.map (ansF I)).trans (map_reqs_perm I)

theorem p3_answers (L0 : List (List ℕ)) (hp : L0.Perm (union I)) (c0 : ℕ × ℕ × ℕ) :
    (jScan ℓ c0 (L0.mergeSort CSort.rle)).reverse.mergeSort CSort.rle = ansAll I :=
  (CSort.eq_sortedRecs ((List.reverse_perm _).trans (jScan_perm I L0 hp c0)).symm
    (pairwise_ansAll I)).symm

/-- The answers of the scan have four words. -/
lemma length_of_mem_jScan (L0 : List (List ℕ)) (hp : L0.Perm (union I)) (c0 : ℕ × ℕ × ℕ)
    {a : List ℕ} (ha : a ∈ jScan ℓ c0 (L0.mergeSort CSort.rle)) : a.length = 4 :=
  length_of_mem_ansAll I ((jScan_perm I L0 hp c0).mem_iff.mp ha)

/-- The number of answers. -/
lemma length_jScan (L0 : List (List ℕ)) (hp : L0.Perm (union I)) (c0 : ℕ × ℕ × ℕ) :
    (jScan ℓ c0 (L0.mergeSort CSort.rle)).length = ansBase I I.schemas.length := by
  rw [(jScan_perm I L0 hp c0).length_eq, ← List.length_map (f := fun a : List ℕ => a.headD 0),
    map_head_ansAll, List.length_range]

/-! ## Counts and word bounds -/

/-- The number of requests. -/
theorem length_reqs : (reqs I).length = ansBase I I.schemas.length := by
  rw [length_reqs_eq, ← List.length_map (f := fun a : List ℕ => a.headD 0), map_head_ansAll,
    List.length_range]

lemma length_coordList_le (D : Finset (Coord k ℓ)) : (coordList D).length ≤ k * 2 ^ ℓ := by
  have h1 : (allBlockCoords ℓ).length = 2 ^ ℓ := by
    rw [← List.length_map (f := blockNum), map_blockNum_allBlockCoords, List.length_range]
  have h2 : (allCoords k ℓ).length = k * 2 ^ ℓ := by
    simp [allCoords, List.length_flatMap, h1]
  rw [← h2]; exact List.length_filter_le _ _

lemma arity_mul_le {W : ℕ} (s : Schema k ℓ W) :
    arity s * (coordList s.domain).length ≤ (schemaDescription s).length := by
  rw [schemaDescription_eq']
  have hp := length_perms s
  have hc : ((coordList s.domain).flatMap cdesc).length = (coordList s.domain).length * (ℓ + 1) := by
    rw [List.length_flatMap]; simp [length_cdesc]
  have ha : arity s ≤ 3 := by unfold arity; split_ifs <;> omega
  have hd := length_coordList_le s.domain
  simp only [List.length_cons, List.length_append, hc, hp]
  rcases Nat.lt_or_ge ℓ 2 with hl | hl
  · have h2 : 2 ^ ℓ = ℓ + 1 := by interval_cases ℓ <;> rfl
    have : arity s * (coordList s.domain).length ≤ arity s * (k + k * ℓ) :=
      Nat.mul_le_mul_left _ (by rw [h2] at hd; linarith)
    omega
  · have : arity s * (coordList s.domain).length ≤ (coordList s.domain).length * (ℓ + 1) := by
      nlinarith
    omega

lemma ansBase_le_H : ansBase I I.schemas.length ≤ H I := by
  have h1 : ansBase I I.schemas.length ≤ (schsDesc I).length := by
    rw [ansBase, List.take_of_length_le (by simp), schsDesc_eq, List.length_flatMap]
    exact List.sum_le_sum fun e _ => arity_mul_le (sch I e)
  have h2 := length_sd_le I
  rw [sd_eq] at h2
  simp only [List.length_cons, List.length_append] at h2
  omega

lemma val_le_one (b : ZMod 2) : b.val ≤ 1 := Nat.le_of_lt_succ (ZMod.val_lt b)

lemma lt_of_mem_bd {b : BlockCoord ℓ} {x : ℕ} (hx : x ∈ blockDescription b) : x ≤ 1 := by
  simp only [blockDescription, List.mem_map, List.mem_finRange, true_and] at hx
  obtain ⟨t, rfl⟩ := hx
  exact val_le_one _

/-- Entries of location records are at most `2 H` (systems with a schema). -/
lemma le_of_mem_locRecs (hE : I.schemas ≠ []) {m : List ℕ} (hm : m ∈ locRecs I) :
    ∀ x ∈ m, x ≤ 2 * H I := by
  obtain ⟨v, c, hc, rfl⟩ := (mem_locRecs I).mp hm
  have hW := W_le I
  have hv := v.2
  have hk := k_le_H I hE
  have hlab : labsN I v ≤ 2 := by rw [labsN_eq]; split_ifs <;> omega
  have hlab1 : 1 ≤ labsN I v := by rw [labsN_eq]; omega
  have hinit : initNum (I.init v) ≤ 2 := by
    unfold initNum; split
    · omega
    · have := val_le_one ‹ZMod 2›; omega
  have hidx : (coordList (I.domain v)).idxOf c < (coordList (I.domain v)).length :=
    List.idxOf_lt_length_of_mem (mem_coordList.mpr hc)
  have hoff : locOff I v + (coordList (I.domain v)).idxOf c * labsN I v ≤ 2 * H I := by
    have h1 := locOff_succ I v.2
    have h2 := locOff_le_H I (v + 1)
    have h3 : (coordList (I.domain v)).idxOf c * labsN I v + labsN I v ≤ locSize I v := by
      rw [locSize, ← labsN]; nlinarith
    have : locSize I ⟨v, v.2⟩ = locSize I v := rfl
    omega
  intro x hx
  simp only [locRecC, cdesc, List.cons_append, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | hx | rfl | rfl | rfl | rfl
  · omega
  · have := c.1.2; omega
  · have := lt_of_mem_bd hx; omega
  · omega
  · exact hoff
  · omega
  · omega

/-- The sequence number of a request is below the number of requests. -/
lemma seq_lt {r : List ℕ} (hr : r ∈ reqs I) : r.getD (ℓ + 3) 0 < ansBase I I.schemas.length := by
  have h : (ansF I r).headD 0 ∈ (ansAll I).map (·.headD 0) :=
    List.mem_map_of_mem ((map_reqs_perm I).mem_iff.mp (List.mem_map_of_mem hr))
  rw [map_head_ansAll, List.mem_range, headD_ansF] at h
  exact h

/-- Entries of requests are at most `H` (systems with a schema). -/
lemma le_of_mem_reqs (hE : I.schemas ≠ []) {r : List ℕ} (hr : r ∈ reqs I) :
    ∀ x ∈ r, x ≤ H I := by
  have hs := seq_lt I hr
  have hN := ansBase_le_H I
  obtain ⟨e, p, hp, c, hc, s, rfl⟩ := mem_reqs I hr
  have hsr : (reqRec p.1 p.2 c s).getD (ℓ + 3) 0 = s :=
    getD_rec p.1 (cdesc (p.2.apply c)) 1 s 0 0 1 (ℓ + 3) (by simp [length_cdesc]) (by omega)
  rw [hsr] at hs
  have hW := W_le I
  have hk := k_le_H I hE
  have hu := schLocs_le (sch I e) p.1 (List.of_mem_zip hp).1
  intro x hx
  simp only [reqRec, cdesc, List.cons_append, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | hx | rfl | rfl | rfl | rfl
  · omega
  · have := (p.2.apply c).1.2; omega
  · have := lt_of_mem_bd hx; have := E_le I
    have : 0 < I.schemas.length := List.length_pos_of_ne_nil hE
    omega
  · have : 0 < I.schemas.length := List.length_pos_of_ne_nil hE
    have := E_le I; omega
  · omega
  · omega
  · omega

/-- **Word bounds** of the union (systems with a schema): every entry is below `2 ^ w`. -/
theorem lt_of_mem_union (hE : I.schemas ≠ []) {w : ℕ} (hw : 4 * (H I + 1) ≤ 2 ^ w)
    {r : List ℕ} (hr : r ∈ union I) : ∀ x ∈ r, x < 2 ^ w := by
  intro x hx
  rcases List.mem_append.mp hr with h | h
  · have := le_of_mem_locRecs I hE h x hx; omega
  · have := le_of_mem_reqs I hE h x hx; omega

/-- **Word bounds** of the answers (systems with a schema). -/
theorem lt_of_mem_ansAll (hE : I.schemas ≠ []) {w : ℕ} (hw : 4 * (H I + 1) ≤ 2 ^ w)
    {a : List ℕ} (ha : a ∈ ansAll I) : ∀ x ∈ a, x < 2 ^ w := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ((map_reqs_perm I).mem_iff.mpr ha)
  obtain ⟨e, p, hp, c, hc, s, rfl⟩ := mem_reqs I hr
  rw [ansF_req I hp hc]
  obtain ⟨h, hd, -⟩ := req_loc I hp hc s
  have hm := le_of_mem_locRecs I hE ((mem_locRecs I).mpr ⟨_, _, hd, rfl⟩)
  have hs := seq_lt I hr
  have hN := ansBase_le_H I
  have hsr : (reqRec p.1 p.2 c s).getD (ℓ + 3) 0 = s :=
    getD_rec p.1 (cdesc (p.2.apply c)) 1 s 0 0 1 (ℓ + 3) (by simp [length_cdesc]) (by omega)
  rw [hsr] at hs
  have hoff := hm _ (show locOff I p.1 + (coordList (I.domain ⟨p.1, h⟩)).idxOf (p.2.apply c) *
      labsN I ⟨p.1, h⟩ ∈ locRecC I ⟨p.1, h⟩ (p.2.apply c) by simp [locRecC])
  rw [off_eq I hd] at hoff
  have hlab : labsN I ⟨p.1, h⟩ ≤ 2 := by rw [labsN_eq]; split_ifs <;> omega
  have hseed := val_le_one (initSeed I ⟨p.1, h⟩ (p.2.apply c))
  intro x hx
  simp only [ansU, dif_pos h, ansRec, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> omega

/-- Word bounds of the answers of the scan. -/
lemma lt_of_mem_jScan (hE : I.schemas ≠ []) {w : ℕ} (hw : 4 * (H I + 1) ≤ 2 ^ w)
    (L0 : List (List ℕ)) (hp : L0.Perm (union I)) (c0 : ℕ × ℕ × ℕ)
    {a : List ℕ} (ha : a ∈ jScan ℓ c0 (L0.mergeSort CSort.rle)) : ∀ x ∈ a, x < 2 ^ w :=
  lt_of_mem_ansAll I hE hw ((jScan_perm I L0 hp c0).mem_iff.mp ha)

end Lax119563Proofs.Compiler

end Compiler_PJoinFacts

/-! ### Formerly `Lax119563Proofs.Compiler.PEmitHub` -/

section Compiler_PEmitHub

/-!
# Pass `P4` (list level): the edges of one hub class in program form

`P4` emits, for every hub class, its labels in order and for each label the sorted neighbor
positions (`gEdges`, `OutDesc`). Here these lists are written with natural-number bits
`a = i / 2`, `b = i % 2` for the label index `i` (`hubE_bits2`, `hubE_bits1`) and with
explicit numbers:
* coordinate slots by the join answers (`slotPos_coord_ans`: the answer
  `[s, off, labs, seed]` gives the position `locBase + off (+ b)`, present unless `labs = 1`
  and `b ≠ ε · seed`, `cposA`);
* two optional positions sorted (`sort2`);
* junctions (`junE`), links (`lnkE`), updates (`updE`, `updFE` for the first entry of a column
  of a binary schema).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Generic helpers -/

/-- Two optional positions, the present ones sorted. -/
def sort2 : Option ℕ → Option ℕ → List ℕ
  | some x, some y => if x ≤ y then [x, y] else [y, x]
  | some x, none => [x]
  | none, some y => [y]
  | none, none => []

lemma mergeSort_two (o₁ o₂ : Option ℕ) :
    ([o₁, o₂].filterMap id).mergeSort (fun a b => decide (a ≤ b)) = sort2 o₁ o₂ := by
  cases o₁ with
  | none => cases o₂ <;> simp [sort2, List.filterMap_cons]
  | some x =>
    cases o₂ with
    | none => simp [sort2, List.filterMap_cons]
    | some y =>
      simp only [List.filterMap_cons, id, List.filterMap_nil, sort2]
      split_ifs with h
      · exact mergeSort_eq_of (List.Perm.refl _) (by simp [h])
      · exact mergeSort_eq_of (List.Perm.swap x y []) (by simp; omega)

/-- The position of a coordinate slot from a join answer `[s, off, labs, seed]`. -/
def cposA (LB e : ℕ) (a : List ℕ) (b : ℕ) : Option ℕ :=
  if a.getD 2 0 = 1 then (if b = e * a.getD 3 0 then some (LB + a.getD 1 0) else none)
  else some (LB + a.getD 1 0 + b)

/-- The label with index `i` of a two-bit class (`bits2`). -/
def lab2 (i : ℕ) : Lab := (((i / 2 : ℕ) : ZMod 2), ((i % 2 : ℕ) : ZMod 2))

lemma val_natCast_lt {a : ℕ} (h : a < 2) : ((a : ZMod 2)).val = a := by
  rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt h

lemma val_add_natCast (a b : ℕ) : (((a : ℕ) : ZMod 2) + ((b : ℕ) : ZMod 2)).val = (a + b) % 2 := by
  rw [← Nat.cast_add, ZMod.val_natCast]

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (ε : ZMod 2)

/-! ## Coordinate slots by the answers -/

lemma val_mul_z2 (x y : ZMod 2) : (x * y).val = x.val * y.val := by
  rcases Lax119563Proofs.Reduction.zmod2_cases x with rfl | rfl <;> rcases Lax119563Proofs.Reduction.zmod2_cases y with rfl | rfl <;> rfl

/-- **Coordinate slots by the join answers.** -/
lemma slotPos_coord_ans {v : Fin I.numLocations} {c' : Coord k ℓ} (hc : c' ∈ I.domain v)
    (b : ZMod 2) (s : ℕ) :
    slotPos I ε (.coord v c') b = cposA (locBase I) ε.val (ansRec I v c' s) b.val := by
  have h1 := clsStart_coord I hc
  have h2 : locBase I ≤ locStart I v := by simp only [locStart]; omega
  simp only [slotPos, cposA, ansRec, List.getD_cons_succ, List.getD_cons_zero, labsN]
  by_cases hi : (I.init v).isSome
  · have hl : (coordLabs I v).length = 1 := by simp [coordLabs, hi]
    rw [if_pos hi, hl, if_pos rfl]
    rw [hl, Nat.mul_one] at h1
    rw [h1]
    have e1 : (b = ε * initSeed I v c') ↔ b.val = ε.val * (initSeed I v c').val := by
      rw [← val_mul_z2]; exact ⟨fun h => h ▸ rfl, fun h => ZMod.val_injective _ h⟩
    by_cases hb : b = ε * initSeed I v c'
    · rw [if_pos hb, if_pos (e1.mp hb)]; congr 1; omega
    · rw [if_neg hb, if_neg (fun h => hb (e1.mpr h))]
  · have hl : (coordLabs I v).length = 2 := by simp [coordLabs, hi, bits1]
    rw [hl] at h1
    rw [h1, hl, if_neg hi, if_neg (by omega)]
    congr 1; omega

/-! ## Hub edges -/

/-- The edges of the hub class `X` with labels `ls` starting at position `h`. -/
noncomputable def hubE (X : ICls I) (ls : List Lab) (h : ℕ) : List (ℕ × ℕ) :=
  (ls.zipIdx h).flatMap fun q => (hubNbrs I ε X q.1).map fun v => (q.2, v)

lemma hubE_bits2 (X : ICls I) (h : ℕ) : hubE I ε X bits2 h =
    (List.range 4).flatMap fun i => (hubNbrs I ε X (lab2 i)).map fun v => (h + i, v) := by
  simp only [hubE, bits2, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_singleton, lab2]
  norm_num

lemma hubE_bits1 (X : ICls I) (h : ℕ) : hubE I ε X bits1 h =
    (List.range 2).flatMap fun a =>
      (hubNbrs I ε X (((a : ℕ) : ZMod 2), 0)).map fun v => (h + a, v) := by
  simp only [hubE, bits1, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_singleton]
  norm_num

/-! ## Section bases -/

/-- The start of the sum section of schema `e`. -/
noncomputable def sumBase (e : Fin I.schemas.length) : ℕ := schBase I e + hubSize I e

/-- The start of the track section of schema `e`. -/
noncomputable def trackBase (e : Fin I.schemas.length) : ℕ := sumBase I e + sumSize I e

/-- The start of the coefficient section of schema `e`. -/
noncomputable def coefBase (e : Fin I.schemas.length) : ℕ := trackBase I e + 2 * nEnt I e

/-! ## Junctions -/

/-- The edges of one junction label: the sum, then the two coordinates sorted. -/
def junE1 (h sp : ℕ) (pu pv : Option ℕ) (a b : ℕ) : List (ℕ × ℕ) :=
  (h, sp + (a + b) % 2) :: (sort2 pu pv).map fun v => (h, v)

lemma lab2_fst {i : ℕ} : (lab2 i).1 = (((i / 2 : ℕ)) : ZMod 2) := rfl
lemma lab2_snd {i : ℕ} : (lab2 i).2 = (((i % 2 : ℕ)) : ZMod 2) := rfl

/-- **Junctions.** -/
theorem hubE_junc {e : Fin I.schemas.length} {c : Coord k ℓ} (ht : isTern (sch I e) = true)
    (hc : c ∈ dom I e) (h : ℕ) :
    hubE I ε (.junc e c) bits2 h = (List.range 4).flatMap fun i =>
      junE1 (h + i) (sumBase I e + 2 * (coordList (dom I e)).idxOf c)
        (slotPos I ε (coordU e c) (((i / 2 : ℕ)) : ZMod 2))
        (slotPos I ε (coordV e c) (((i % 2 : ℕ)) : ZMod 2)) (i / 2) (i % 2) := by
  rw [hubE_bits2]
  refine List.flatMap_congr fun i _ => ?_
  rw [hubNbrs_junc I ε ht hc]
  have e1 : ([(coordU e c, (lab2 i).1), (coordV e c, (lab2 i).2)].filterMap
      fun s => slotPos I ε s.1 s.2) =
      [slotPos I ε (coordU e c) (lab2 i).1, slotPos I ε (coordV e c) (lab2 i).2].filterMap id := by
    simp only [List.filterMap_cons, List.filterMap_nil, id]
  rw [e1, mergeSort_two]
  simp only [slotPos, Option.toList_some, List.singleton_append, List.map_cons, junE1,
    lab2_fst, lab2_snd, val_add_natCast, sumBase]

/-! ## Links -/

/-- The edges of one link label: the last track of the column, then the end coordinate. -/
def lnkE1 (h tp : ℕ) (pw : Option ℕ) (a : ℕ) : List (ℕ × ℕ) :=
  (h, tp + a) :: pw.toList.map fun v => (h, v)

/-- **Links** (`k ≥ 2`). -/
theorem hubE_link (hk : 2 ≤ k) {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e)
    (h : ℕ) :
    hubE I ε (.link e c) bits1 h = (List.range 2).flatMap fun a =>
      lnkE1 (h + a) (trackBase I e + 2 * (entBefore I e c + (stepsC c).length - 1))
        (slotPos I ε (endCls I e c) ((a : ℕ) : ZMod 2)) a := by
  rw [hubE_bits1]
  have hne := stepsC_ne_nil hk c
  have hσ : (stepsC c).getLast hne ∈ stepsC c := List.getLast_mem hne
  have hidx : (stepsC c).idxOf ((stepsC c).getLast hne) = (stepsC c).length - 1 := by
    rw [List.getLast_eq_getElem]
    exact (nodup_stepsC c).idxOf_getElem _ _
  have hpos : 0 < (stepsC c).length := List.length_pos_of_ne_nil hne
  refine List.flatMap_congr fun a ha => ?_
  have ha2 : a < 2 := List.mem_range.mp ha
  rw [hubNbrs_link I ε hk hc, trackAt_numSteps, dif_neg hne]
  simp only [slotPos, Option.toList_some, List.singleton_append, List.map_cons, lnkE1,
    val_natCast_lt ha2, hidx, trackBase, sumBase]
  congr 2
  omega

/-! ## Updates -/

/-- The edges of one update label: the previous track (or sum), the track, the coefficient. -/
def updE1 (h pp tp cp : ℕ) (a b : ℕ) : List (ℕ × ℕ) :=
  [(h, pp + a), (h, tp + b), (h, cp + (a + b) % 2)]

/-- The edges of one update label at the first entry of a column of a binary schema: the
track, the coefficient, then the start coordinate. -/
def updF1 (h tp cp : ℕ) (pu : Option ℕ) (a b : ℕ) : List (ℕ × ℕ) :=
  [(h, tp + b), (h, cp + (a + b) % 2)] ++ pu.toList.map fun v => (h, v)

/-- The base of the previous track (or of the sum) of an update. -/
noncomputable def prevBase (e : Fin I.schemas.length) (c : Coord k ℓ) (t : ℕ) : ℕ :=
  if t = 0 then sumBase I e + 2 * (coordList (dom I e)).idxOf c
  else trackBase I e + 2 * (entBefore I e c + t - 1)

/-- **Updates** (not the first entry of a column of a binary schema). -/
theorem hubE_upd {e : Fin I.schemas.length} {c : Coord k ℓ} {σ : ℕ} (hc : c ∈ dom I e)
    (hσ : σ ∈ stepsC c) (h0 : 0 < (stepsC c).idxOf σ ∨ isTern (sch I e) = true) (h : ℕ) :
    hubE I ε (.upd e σ c) bits2 h = (List.range 4).flatMap fun i =>
      updE1 (h + i) (prevBase I e c ((stepsC c).idxOf σ))
        (trackBase I e + 2 * (entBefore I e c + (stepsC c).idxOf σ))
        (coefBase I e + 2 * (coefSteps I e).idxOf σ) (i / 2) (i % 2) := by
  rw [hubE_bits2]
  have hj : (stepsC c).idxOf σ < (stepsC c).length := List.idxOf_lt_length_of_mem hσ
  have hget : (stepsC c)[(stepsC c).idxOf σ] = σ := List.getElem_idxOf hj
  have htr := trackAt_stepsC I e c hj
  rw [hget] at htr
  refine List.flatMap_congr fun i hi => ?_
  have hi2 : i / 2 < 2 := by have := List.mem_range.mp hi; omega
  have hi3 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [hubNbrs_upd I ε hc hσ h0]
  have hp : slotPos I ε (trackAt I e c σ) (lab2 i).1 =
      some (prevBase I e c ((stepsC c).idxOf σ) + i / 2) := by
    rw [htr, lab2_fst]
    unfold prevBase
    split
    · next h00 =>
      have ht : isTern (sch I e) = true := by rcases h0 with h0 | h0; omega; exact h0
      simp only [startCls, ht, if_true, slotPos, if_pos h00, sumBase, val_natCast_lt hi2]
    · next h00 =>
      simp only [slotPos, if_neg h00, trackBase, sumBase, val_natCast_lt hi2]
      rw [(nodup_stepsC c).idxOf_getElem _ (by omega)]
      congr 1; omega
  simp only [slotsOf, List.filterMap_cons, List.filterMap_nil, hp]
  simp only [slotPos, List.map_cons, List.map_nil, updE1, lab2_fst, lab2_snd, val_add_natCast,
    val_natCast_lt hi3, trackBase, sumBase, coefBase]

/-- **Updates at the first entry of a column of a binary schema.** -/
theorem hubE_updF {e : Fin I.schemas.length} {c : Coord k ℓ} {σ : ℕ} (hc : c ∈ dom I e)
    (hσ : σ ∈ stepsC c) (h0 : (stepsC c).idxOf σ = 0) (ht : isTern (sch I e) = false)
    (h : ℕ) :
    hubE I ε (.upd e σ c) bits2 h = (List.range 4).flatMap fun i =>
      updF1 (h + i) (trackBase I e + 2 * entBefore I e c)
        (coefBase I e + 2 * (coefSteps I e).idxOf σ)
        (slotPos I ε (startCls I e c) (((i / 2 : ℕ)) : ZMod 2)) (i / 2) (i % 2) := by
  rw [hubE_bits2]
  refine List.flatMap_congr fun i hi => ?_
  have hi3 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [hubNbrs_upd_first I ε hc hσ h0 ht]
  simp only [slotPos, Option.toList_some, List.singleton_append, List.map_cons, List.map_append,
    updF1, lab2_fst, lab2_snd, val_add_natCast, val_natCast_lt hi3, h0, trackBase, sumBase,
    coefBase, Nat.add_zero, List.cons_append, List.map_nil, List.nil_append, List.append_assoc]

end Lax119563Proofs.Compiler

end Compiler_PEmitHub

/-! ### Formerly `Lax119563Proofs.Compiler.P4Edge` -/

section Compiler_P4Edge

/-!
# Pass `P4` (program): pushing edges

Edges are pushed on the stack `q4E` (first `u`, then `v`, so that the stack holds the edges
reversed) and counted in `r4M` (`EdgeEff`). `pE h v` pushes one edge (`pE_good`); `cposS`
computes the optional position of a coordinate slot from the answer data `(off, mode)` with
`mode = 2` for two labels and `mode = ε · seed` for one label (`cposS_good`, matching
`cposA`); `pEo h f v` pushes `(h, v)` if the flag `f` is set (`pEo_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Registers and stacks of `P4` -/

/-- The edge stack. -/
def q4E : Fin CQ := 1
def r4Eps : Fin CR := 35
/-- The edge count. -/
def r4M : Fin CR := 36
/-- A computed flag and value (optional position). -/
def r4F : Fin CR := 21
def r4V : Fin CR := 22

/-! ## Edge effects -/

/-- The words of a list of edges on the stack (reversed). -/
def pairsRev (Es : List (ℕ × ℕ)) : List ℕ := (Es.flatMap fun e => [e.1, e.2]).reverse

lemma pairsRev_append (E₁ E₂ : List (ℕ × ℕ)) : pairsRev (E₁ ++ E₂) = pairsRev E₂ ++ pairsRev E₁ := by
  simp [pairsRev]

/-- `st'` is `st` with the edges `Es` pushed and counted (output and cursor kept). -/
def EdgeEff (st st' : NSt CR CQ) (Es : List (ℕ × ℕ)) : Prop :=
  st'.stk = Function.update st.stk q4E (pairsRev Es ++ st.stk q4E) ∧
    st'.env r4M = st.env r4M + Es.length ∧ st'.pos = st.pos ∧ st'.out = st.out

lemma EdgeEff.trans {st s₁ s₂ : NSt CR CQ} {E₁ E₂ : List (ℕ × ℕ)} (h₁ : EdgeEff st s₁ E₁)
    (h₂ : EdgeEff s₁ s₂ E₂) : EdgeEff st s₂ (E₁ ++ E₂) := by
  obtain ⟨a1, b1, c1, d1⟩ := h₁
  obtain ⟨a2, b2, c2, d2⟩ := h₂
  refine ⟨?_, ?_, c2.trans c1, d2.trans d1⟩
  · rw [a2, a1, pairsRev_append]; simp
  · rw [b2, b1, List.length_append]; ring

lemma EdgeEff.refl (st : NSt CR CQ) : EdgeEff st st [] := by
  refine ⟨?_, by simp, rfl, rfl⟩
  funext q; by_cases h : q = q4E
  · subst h; simp [pairsRev]
  · simp [Function.update_of_ne h]

lemma EdgeEff.of_frame {st st' : NSt CR CQ} (hs : st'.stk = st.stk) (hm : st'.env r4M = st.env r4M)
    (hp : st'.pos = st.pos) (ho : st'.out = st.out) : EdgeEff st st' [] := by
  have := EdgeEff.refl st
  obtain ⟨a, b, -, -⟩ := this
  exact ⟨by rw [hs, ← a], by rw [hm]; simp, hp, ho⟩

/-! ## One edge -/

/-- Push the edge `(h, v)` and count it. -/
def pE (h v : Ex CR) : CStm CR CQ :=
  .seq (.push q4E h) (.seq (.push q4E v) (.set r4M (.add (rv r4M) (.const 1))))

lemma pE_good {w : ℕ} {x : List Bool} (h v : Ex CR) (st : NSt CR CQ) (hh : h.Fits w st.env)
    (hv : v.Fits w st.env) (hm : st.env r4M + 1 < 2 ^ w) :
    ∃ st', Good x w (pE h v) st st' ((h.size + v.size + 3) * Ex.nodeCost w + 3 * unitCost w) ∧
      EdgeEff st st' [(h.eval st.env, v.eval st.env)] ∧
      ∀ r, r ≠ r4M → st'.env r = st.env r := by
  have r1 := CStm.Good.push (x := x) (q := q4E) hh
  have r2 := CStm.Good.push (x := x) (q := q4E) (st := st.setS q4E (h.eval st.env :: st.stk q4E)) hv
  set s2 := (st.setS q4E (h.eval st.env :: st.stk q4E)).setS q4E
    (v.eval st.env :: (st.setS q4E (h.eval st.env :: st.stk q4E)).stk q4E)
  have r3 := CStm.Good.set (x := x) (w := w) (st := s2) (r := r4M) (e := .add (rv r4M) (.const 1))
    (by simp only [Ex.Fits, rv, Ex.eval, s2, NSt.setS_env]; exact ⟨by omega, by omega, hm⟩)
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp only [Ex.size, rv]; nlinarith), ⟨?_, ?_, rfl, rfl⟩,
    fun r hr => by simp [Function.update_of_ne hr, s2]⟩
  · funext q; by_cases hq : q = q4E
    · subst hq; simp [s2, pairsRev]
    · simp [s2, Function.update_of_ne hq]
  · simp [s2, Ex.eval, rv]

/-! ## Optional edges -/

/-- Push `(h, v)` if the flag `f` is set. -/
def pEo (h : Ex CR) (f v : Fin CR) : CStm CR CQ := .ite (rv f) (pE h (rv v)) .skip

lemma pEo_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (h : Ex CR) (f v : Fin CR) (hf : f ≠ r4M)
    (st : NSt CR CQ) (o : Option ℕ) (ho : st.env f = (if o.isSome then 1 else 0))
    (hv : ∀ a, o = some a → st.env v = a) (hh : h.Fits w st.env) (hvw : st.env v < 2 ^ w)
    (hm : st.env r4M + 1 < 2 ^ w) :
    ∃ st', Good x w (pEo h f v) st st' ((h.size + 10) * Ex.nodeCost w) ∧
      EdgeEff st st' (o.toList.map fun a => (h.eval st.env, a)) ∧
      ∀ r, r ≠ r4M → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hfF : (rv f : Ex CR).Fits w st.env := by
    simp only [rv, Ex.Fits, ho]; split_ifs <;> omega
  cases o with
  | none =>
    refine ⟨st, (CStm.Good.iteF hfF (by simp [rv, Ex.eval, ho]) CStm.Good.skip).mono ?_,
      EdgeEff.refl st, fun _ _ => rfl⟩
    simp only [condCost, rv, Ex.size]; nlinarith
  | some a =>
    obtain ⟨st', g, eff, fr⟩ := pE_good (x := x) h (rv v) st hh (by simpa [rv, Ex.Fits] using hvw)
      hm
    refine ⟨st', (CStm.Good.iteT hfF (by simp [rv, Ex.eval, ho]) g).mono ?_, ?_, fr⟩
    · simp only [condCost, rv, Ex.size]; nlinarith
    · simpa [rv, Ex.eval, hv a rfl] using eff

/-! ## Coordinate slots -/

/-- The position of a coordinate slot: answer offset `off`, mode `md` (`2`: two labels; else
the bit `ε · seed` of the single label), bit `a`, base `lb`: flag `r4F`, value `r4V`. -/
def cposS (lb off md a : Fin CR) : CStm CR CQ :=
  .ite (.lt (.const 1) (rv md))
    (.seq (.set r4F (.const 1)) (.set r4V (.add (rv lb) (.add (rv off) (rv a)))))
    (.ite (.odd (.add (rv a) (rv md))) (.set r4F (.const 0))
      (.seq (.set r4F (.const 1)) (.set r4V (.add (rv lb) (rv off)))))

/-- The mode of an answer `[s, off, labs, seed]` in `G_ε`. -/
def ansMode (e : ℕ) (a : List ℕ) : ℕ := if a.getD 2 0 = 1 then e * a.getD 3 0 else 2

/-- The optional position computed by `cposS`. -/
def cposN (lb off md a : ℕ) : Option ℕ :=
  if 1 < md then some (lb + (off + a)) else if (a + md) % 2 = 1 then none else some (lb + off)

lemma cposA_eq (LB e : ℕ) (a : List ℕ) (b : ℕ) (hb : b ≤ 1) (he : e ≤ 1) (hs : a.getD 3 0 ≤ 1)
    (hl : a.getD 2 0 = 1 ∨ a.getD 2 0 = 2) :
    cposA LB e a b = cposN LB (a.getD 1 0) (ansMode e a) b := by
  unfold cposA ansMode cposN
  have hes : e * a.getD 3 0 ≤ 1 := by
    calc e * a.getD 3 0 ≤ 1 * 1 := Nat.mul_le_mul he hs
      _ = 1 := rfl
  rcases hl with hl | hl
  · simp only [hl, if_true]
    rw [if_neg (show ¬ 1 < e * a.getD 3 0 by omega)]
    by_cases hb' : b = e * a.getD 3 0
    · rw [if_pos hb', if_neg (show ¬ (b + e * a.getD 3 0) % 2 = 1 by omega)]
    · rw [if_neg hb', if_pos (show (b + e * a.getD 3 0) % 2 = 1 by omega)]
  · simp only [hl, show (2 : ℕ) ≠ 1 by decide, if_false, show (1 : ℕ) < 2 by decide, if_true]
    congr 1; omega

lemma cposS_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) {lb off md a : Fin CR}
    (d1 : lb ≠ r4F) (d2 : off ≠ r4F) (d3 : md ≠ r4F) (d4 : a ≠ r4F) (d5 : lb ≠ r4V)
    (d6 : off ≠ r4V) (d7 : md ≠ r4V) (d8 : a ≠ r4V)
    (st : NSt CR CQ) (hmd : st.env md ≤ 2) (ha : st.env a ≤ 1)
    (hlt : st.env lb + st.env off + 2 < 2 ^ w) (hV : st.env r4V < 2 ^ w) :
    ∃ st', Good x w (cposS lb off md a) st st' (20 * Ex.nodeCost w) ∧
      st'.env r4F = (if (cposN (st.env lb) (st.env off) (st.env md) (st.env a)).isSome
        then 1 else 0) ∧
      (∀ v, cposN (st.env lb) (st.env off) (st.env md) (st.env a) = some v → st'.env r4V = v) ∧
      st'.env r4V < 2 ^ w ∧ st'.stk = st.stk ∧ st'.pos = st.pos ∧ st'.out = st.out ∧
      ∀ r, r ≠ r4F → r ≠ r4V → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have h2 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hF1 : (Ex.lt (.const 1) (rv md) : Ex CR).Fits w st.env := by
    simp only [Ex.Fits, rv]; omega
  by_cases hc : 1 < st.env md
  · have r1 := CStm.Good.set (x := x) (w := w) (st := st) (r := r4F) (e := .const 1)
      (by simp only [Ex.Fits]; omega)
    set s1 := st.set r4F ((Ex.const 1 : Ex CR).eval st.env)
    have r2 := CStm.Good.set (x := x) (w := w) (st := s1) (r := r4V)
      (e := .add (rv lb) (.add (rv off) (rv a))) (by
        simp only [Ex.Fits, rv, Ex.eval, s1, NSt.set_env, Function.update_of_ne d1,
          Function.update_of_ne d2, Function.update_of_ne d4]
        omega)
    refine ⟨_, (CStm.Good.iteT hF1 (by simp [Ex.eval, rv, hc]) (r1.seq r2)).mono ?_, ?_, ?_, ?_,
      rfl, rfl, rfl, fun r h1 h2 => ?_⟩
    · simp only [condCost, Ex.size, rv]; nlinarith
    · simp [s1, cposN, hc, Ex.eval, Function.update_of_ne (show r4F ≠ r4V by decide)]
    · intro v hv
      simp only [cposN, if_pos hc, Option.some.injEq] at hv
      simp [s1, Ex.eval, rv, Function.update_of_ne d1, Function.update_of_ne d2,
        Function.update_of_ne d4, ← hv]
    · simp [s1, Ex.eval, rv, Function.update_of_ne d1, Function.update_of_ne d2,
        Function.update_of_ne d4]; omega
    · simp [s1, Function.update_of_ne h1, Function.update_of_ne h2]
  · have hF2 : (Ex.odd (.add (rv a) (rv md)) : Ex CR).Fits w st.env := by
      simp only [Ex.Fits, rv, Ex.eval]; omega
    by_cases hodd : (st.env a + st.env md) % 2 = 1
    · have r1 := CStm.Good.set (x := x) (w := w) (st := st) (r := r4F) (e := .const 0)
        (by simp only [Ex.Fits]; omega)
      refine ⟨_, (CStm.Good.iteF hF1 (by simp [Ex.eval, rv, hc])
        (CStm.Good.iteT hF2 (by simp [Ex.eval, rv, hodd]) r1)).mono ?_, ?_, ?_, ?_, rfl, rfl, rfl,
        fun r h1 h2 => ?_⟩
      · simp only [condCost, Ex.size, rv]; nlinarith
      · simp [cposN, hc, hodd, Ex.eval]
      · intro v hv; simp [cposN, hc, hodd] at hv
      · simpa [Function.update_of_ne (show r4V ≠ r4F by decide)] using hV
      · simp [Function.update_of_ne h1]
    · have r1 := CStm.Good.set (x := x) (w := w) (st := st) (r := r4F) (e := .const 1)
        (by simp only [Ex.Fits]; omega)
      set s1 := st.set r4F ((Ex.const 1 : Ex CR).eval st.env)
      have r2 := CStm.Good.set (x := x) (w := w) (st := s1) (r := r4V)
        (e := .add (rv lb) (rv off)) (by
          simp only [Ex.Fits, rv, Ex.eval, s1, NSt.set_env, Function.update_of_ne d1,
            Function.update_of_ne d2]
          omega)
      refine ⟨_, (CStm.Good.iteF hF1 (by simp [Ex.eval, rv, hc])
        (CStm.Good.iteF hF2 (by simp [Ex.eval, rv]; omega) (r1.seq r2))).mono ?_, ?_, ?_, ?_,
        rfl, rfl, rfl, fun r h1 h2 => ?_⟩
      · simp only [condCost, Ex.size, rv]; nlinarith
      · simp [s1, cposN, hc, hodd, Ex.eval, Function.update_of_ne (show r4F ≠ r4V by decide)]
      · intro v hv
        simp only [cposN, if_neg hc, if_neg hodd, Option.some.injEq] at hv
        simp [s1, Ex.eval, rv, Function.update_of_ne d1, Function.update_of_ne d2, ← hv]
      · simp [s1, Ex.eval, rv, Function.update_of_ne d1, Function.update_of_ne d2]; omega
      · simp [s1, Function.update_of_ne h1, Function.update_of_ne h2]

end Lax119563Proofs.Compiler

end Compiler_P4Edge

/-! ### Formerly `Lax119563Proofs.Compiler.P4Emit` -/

section Compiler_P4Emit

/-!
# Pass `P4` (program): the emission of one graph description

Registers and stacks of the location part and the framing of `P4` (`rNt = 4`: the total of
the class sizes, `qSzA = 14`, `qSzB = 15`: the class-size stacks). `p4Emit` emits `n` (from
`rNt`), the colors of the class sizes on `qSzB` (`colorsS`), `m` (from `r4M`) and the edges
on `q4E` in order (`moveAllS q4E qSzA`, `emitAllS qSzA`): **`p4Emit_good`**.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Registers and stacks of the location part / framing of `P4` -/

/-- The total of the class sizes (kept by the schema part). -/
def rNt : Fin CR := 4
/-- Scratch stack of class sizes. -/
def qSzA : Fin CQ := 14
/-- The class sizes, in order (kept by the schema part). -/
def qSzB : Fin CQ := 15

/-- **The emission**: `n`, colors, `m`, edges. Scratch registers `rT, rP, rJ, rA`. -/
def p4Emit : CStm CR CQ :=
  .seq (.emit (rv rNt)) (.seq (.set rJ (.const 0)) (.seq (colorsS qSzB rT rP rJ rA)
    (.seq (.emit (rv r4M)) (.seq (moveAllS q4E qSzA rT rP) (emitAllS qSzA rT rP)))))

/-- The words of a graph description with class sizes `L` and edges `Es`. -/
def descOf (L : List ℕ) (Es : List (ℕ × ℕ)) : List ℕ :=
  L.sum :: colorsOf 0 L ++ Es.length :: Es.flatMap fun e => [e.1, e.2]

lemma p4Emit_arith {N U a b c : ℕ} (hU : U ≤ N) (hU' : 64 ≤ U) :
    2 * N + U + (2 * N + U + ((2 * U + 1) + ((a + b + 1) * (30 * N) + (2 * N + U +
      ((c + 1) * (10 * N) + (c + 1) * (10 * N)))))) ≤ (a + b + 2 * c + 8) * (40 * N) := by
  nlinarith

/-- **The emission.** -/
lemma p4Emit_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) (L : List ℕ)
    (Es : List (ℕ × ℕ)) (hb : st.Bdd w) (hp : st.pos ≤ x.length) (hB : st.stk qSzB = L)
    (hE : st.stk q4E = pairsRev Es) (hA : st.stk qSzA = []) (hN : st.env rNt = L.sum)
    (hM : st.env r4M = Es.length) :
    ∃ st', Good x w p4Emit st st'
        ((L.length + L.sum + 2 * Es.length + 8) * (40 * Ex.nodeCost w)) ∧
      st'.out = st.out ++ descOf L Es ∧
      st'.stk = Function.update (Function.update st.stk qSzB []) q4E [] ∧
      st'.pos = st.pos ∧
      ∀ r, r ≠ rT → r ≠ rP → r ≠ rJ → r ≠ rA → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hNw : L.sum < 2 ^ w := by rw [← hN]; exact hb.1 _
  have hMw : st.env r4M < 2 ^ w := hb.1 _
  have r1 := Good.emit (x := x) (w := w) (st := st) (e := rv rNt) (hb.1 _)
  set s1 : NSt CR CQ := { st with out := st.out ++ [(rv rNt : Ex CR).eval st.env] }
  have r2 := Good.set (x := x) (w := w) (st := s1) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s2 := s1.set rJ ((Ex.const 0 : Ex CR).eval s1.env)
  have r3 := Good.sne (x := x) (w := w) (st := s2) rP qSzB
  set s3 := s2.set rP (if (s2.stk qSzB).isEmpty then 0 else 1)
  have e3B : s3.stk qSzB = L := hB
  have e3f : s3.env rP = if L = [] then 0 else 1 := by
    simp only [s3, NSt.set_env, Function.update_self]
    rw [show s2.stk qSzB = L from hB]; cases L <;> rfl
  have e3p : s3.env rJ = 0 := by
    simp [s3, s2, Ex.eval, Function.update_of_ne (show rJ ≠ rP by decide)]
  obtain ⟨s4, r4, h4s, h4p, h4o, h4P, h4e⟩ := colorsS_loop_good (x := x) hw
    (t := rT) (f := rP) (p := rJ) (i := rA) (q := qSzB) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) L s3 e3B e3f (by rw [e3p]; omega)
  have e4M : s4.env r4M = st.env r4M := by
    rw [h4e _ (by decide) (by decide) (by decide) (by decide)]
    simp [s3, s2, s1, Function.update_of_ne (show r4M ≠ rP by decide),
      Function.update_of_ne (show r4M ≠ rJ by decide)]
  have r5 := Good.emit (x := x) (w := w) (st := s4) (e := rv r4M)
    (by show s4.env r4M < 2 ^ w; rw [e4M]; exact hMw)
  set s5 : NSt CR CQ := { s4 with out := s4.out ++ [(rv r4M : Ex CR).eval s4.env] }
  have r15 := r1.seq (r2.seq (r3.seq (r4.seq r5)))
  have hb5 := r15.bdd hw hb hp
  obtain ⟨s6, r6, h6s, h6p, h6o, h6e⟩ := moveAllS_good (x := x) hw (q := q4E) (q' := qSzA)
    (t := rT) (f := rP) (by decide) (by decide) s5 hb5.1
  have hb6 := r6.bdd hw hb5.1 hb5.2
  obtain ⟨s7, r7, h7s, h7p, h7o, h7e⟩ := emitAllS_good (x := x) hw (q := qSzA) (t := rT)
    (f := rP) (by decide) s6 hb6.1
  have e5s : s5.stk = Function.update st.stk qSzB [] := by
    show s4.stk = _; rw [h4s]; rfl
  have e6A : s6.stk qSzA = Es.flatMap fun e => [e.1, e.2] := by
    rw [h6s, Function.update_self, e5s]
    simp [Function.update_of_ne (show q4E ≠ qSzB by decide),
      Function.update_of_ne (show qSzA ≠ qSzB by decide), hA, hE, pairsRev]
  have e6E : (s5.stk q4E).length = 2 * Es.length := by
    rw [e5s, Function.update_of_ne (by decide), hE, pairsRev, List.length_reverse,
      List.length_flatMap]
    simp [sum_map_const]; ring
  refine ⟨s7, (r1.seq (r2.seq ((r3.seq r4).seq (r5.seq (r6.seq r7))))).mono ?_, ?_, ?_, ?_, ?_⟩
  · have hl : (Es.flatMap fun e => [e.1, e.2]).length = 2 * Es.length := by
      induction Es with
      | nil => rfl
      | cons a l ih => simp [ih]; ring
    rw [e6A, e6E, hl]
    simp only [rv, Ex.size]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    have := p4Emit_arith (N := N) (U := U) (a := L.length) (b := L.sum) (c := 2 * Es.length) hU hU'
    nlinarith
  · rw [h7o, e6A, h6o]
    show s4.out ++ [s4.env r4M] ++ _ = _
    rw [h4o, e4M, e3p, hM]
    simp [s3, s2, s1, descOf, Ex.eval, rv, hN]
  · rw [h7s, h6s, e5s]
    funext q
    by_cases hqA : q = qSzA
    · subst hqA; simp [Function.update_of_ne (show qSzA ≠ q4E by decide),
        Function.update_of_ne (show qSzA ≠ qSzB by decide), hA]
    · rw [Function.update_of_ne hqA, Function.update_of_ne hqA]
  · rw [h7p, h6p]; show s4.pos = _; rw [h4p]; rfl
  · intro r h1 h2 h3 h4
    rw [h7e r h1 h2, h6e r h1 h2]
    show s4.env r = _
    rw [h4e r h1 h2 h3 h4]
    simp [s3, s2, s1, Function.update_of_ne h2, Function.update_of_ne h3]

end Lax119563Proofs.Compiler

end Compiler_P4Emit

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchLib` -/

section Compiler_P4SchLib

/-!
# Pass `P4`, schema part: generic tools

* `Good.loop_idx`: a loop that runs exactly `n` times, along a family of predicates
  `P j` (the state after `j` iterations), with per-iteration costs `C j`.
* Straight-line statements (`lf`: no loops, no `rst`) cost at most `scost c · nodeCost w`
  (`cost_le_scost`, `good_lf`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

namespace Good

lemma loop_idx_aux {e : Ex R} {body : CStm R Q} (n : ℕ) (P : ℕ → NSt R Q → Prop)
    (C : ℕ → ℕ)
    (hstep : ∀ j < n, ∀ s, P j s → e.Fits w s.env ∧ e.eval s.env ≠ 0 ∧
      ∃ s', Good x w body s s' (C j) ∧ P (j + 1) s')
    (hend : ∀ s, P n s → e.Fits w s.env ∧ e.eval s.env = 0) :
    ∀ d m, m + d = n → ∀ s, P m s → ∃ s', Good x w (.loop e body) s s'
      (∑ j ∈ Finset.range d, (C (m + j) + condCost w e) + condCost w e) ∧ P n s' := by
  intro d
  induction d with
  | zero =>
    intro m hm s hs
    rw [Nat.add_zero] at hm; subst hm
    obtain ⟨hf, h0⟩ := hend s hs
    exact ⟨s, (loop_stop hf h0).mono (by simp), hs⟩
  | succ d ih =>
    intro m hm s hs
    obtain ⟨hf, hc, s₁, h₁, hs₁⟩ := hstep m (by omega) s hs
    obtain ⟨s', h', hs'⟩ := ih (m + 1) (by omega) s₁ hs₁
    refine ⟨s', (loop_cons hf hc h₁ h').mono (le_of_eq ?_), hs'⟩
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    ring

/-- **Loops running exactly `n` times.** -/
lemma loop_idx {e : Ex R} {body : CStm R Q} (n : ℕ) (P : ℕ → NSt R Q → Prop) (C : ℕ → ℕ)
    (hstep : ∀ j < n, ∀ s, P j s → e.Fits w s.env ∧ e.eval s.env ≠ 0 ∧
      ∃ s', Good x w body s s' (C j) ∧ P (j + 1) s')
    (hend : ∀ s, P n s → e.Fits w s.env ∧ e.eval s.env = 0) (s : NSt R Q) (hs : P 0 s) :
    ∃ s', Good x w (.loop e body) s s'
      (∑ j ∈ Finset.range n, (C j + condCost w e) + condCost w e) ∧ P n s' := by
  obtain ⟨s', h, hP⟩ := loop_idx_aux n P C hstep hend n 0 (by omega) s hs
  exact ⟨s', h.mono (by simp), hP⟩

/-- **Loops running exactly `n` times**, uniform cost. -/
lemma loop_idxC {e : Ex R} {body : CStm R Q} (n : ℕ) (P : ℕ → NSt R Q → Prop) (C : ℕ)
    (hstep : ∀ j < n, ∀ s, P j s → e.Fits w s.env ∧ e.eval s.env ≠ 0 ∧
      ∃ s', Good x w body s s' C ∧ P (j + 1) s')
    (hend : ∀ s, P n s → e.Fits w s.env ∧ e.eval s.env = 0) (s : NSt R Q) (hs : P 0 s) :
    ∃ s', Good x w (.loop e body) s s' (n * (C + condCost w e) + condCost w e) ∧ P n s' := by
  obtain ⟨s', h, hP⟩ := loop_idx n P (fun _ => C) hstep hend s hs
  exact ⟨s', h.mono (by simp), hP⟩

end Good

/-! ## Straight-line statements -/

/-- No loops and no `rst`. -/
def lf : CStm R Q → Bool
  | rst => false
  | loop _ _ => false
  | seq p q => lf p && lf q
  | ite _ p q => lf p && lf q
  | _ => true

/-- A static cost bound in units of `nodeCost`. -/
def scost : CStm R Q → ℕ
  | skip => 1
  | set _ e => e.size + 1
  | emit e => e.size + 1
  | push _ e => e.size + 1
  | pop _ _ => 2
  | sne _ _ => 3
  | rd _ => 1
  | rst => 0
  | seq p q => scost p + scost q
  | ite c p q => c.size + 1 + max (scost p) (scost q)
  | loop _ _ => 0

lemma cost_le_scost : ∀ (c : CStm R Q) (st : NSt R Q), lf c = true →
    cost x w c st ≤ scost c * Ex.nodeCost w
  | skip, _, _ => by
    have := Ex.unitCost_le_nodeCost w; simp only [cost, scost]; omega
  | set _ e, _, _ => by
    have := Ex.unitCost_le_nodeCost w; simp only [cost, scost]; nlinarith
  | emit e, _, _ => by
    have := Ex.unitCost_le_nodeCost w; simp only [cost, scost]; nlinarith
  | push _ e, _, _ => by
    have := Ex.unitCost_le_nodeCost w; simp only [cost, scost]; nlinarith
  | pop _ _, _, _ => by
    have := Ex.unitCost_le_nodeCost w; have := unitCost_ge w
    simp only [cost, scost]; omega
  | sne _ _, _, _ => by
    have := Ex.unitCost_le_nodeCost w; have := unitCost_ge w
    have : 2 * unitCost w ≤ Ex.nodeCost w := by
      unfold Ex.nodeCost; nlinarith
    simp only [cost, scost]; omega
  | rd _, _, _ => by
    have := Ex.unitCost_le_nodeCost w; simp only [cost, scost]; omega
  | rst, _, h => by simp [lf] at h
  | loop _ _, _, h => by simp [lf] at h
  | seq p q, st, h => by
    simp only [lf, Bool.and_eq_true] at h
    have h1 := cost_le_scost p st h.1
    have h2 := cost_le_scost q (exec x p st) h.2
    simp only [cost, scost]; rw [add_mul]; omega
  | ite c p q, st, h => by
    simp only [lf, Bool.and_eq_true] at h
    have h1 := cost_le_scost p st h.1
    have h2 := cost_le_scost q st h.2
    have hU := Ex.unitCost_le_nodeCost w
    have hU' := unitCost_ge w
    have hp : scost p * Ex.nodeCost w ≤ max (scost p) (scost q) * Ex.nodeCost w :=
      Nat.mul_le_mul_right _ (le_max_left _ _)
    have hq : scost q * Ex.nodeCost w ≤ max (scost p) (scost q) * Ex.nodeCost w :=
      Nat.mul_le_mul_right _ (le_max_right _ _)
    simp only [cost, scost, condCost, add_mul]
    split_ifs <;> nlinarith

/-- **Straight-line statements.** -/
lemma good_lf {c : CStm R Q} {st : NSt R Q} (hlf : lf c = true) (hf : Fits x w c st) :
    Good x w c st (exec x c st) (scost c * Ex.nodeCost w) :=
  ⟨hf, rfl, cost_le_scost c st hlf⟩

end CStm

end Lax119563Proofs.Compiler

end Compiler_P4SchLib

/-! ### Formerly `Lax119563Proofs.Compiler.PEmitSteps` -/

section Compiler_PEmitSteps

/-!
# Pass `P4` (list level): the entries of a column and their coefficient index

With `M = k - 1 + ℓ`, the steps of a column are `q M + j` for `q ≤ k` and the nonzero rows
`j ∈ rowsL c` (increasing), q-major (`stepsC_eq`); the coefficient steps likewise with the rows
`rowsR` nonzero on the domain (`coefSteps_eq`), so the coefficient index of the step `q M + j`
is `q |rowsR| + rank j` (`idxOf_coefSteps`), `rank j = idxOf j (rowsR)`. The ranks
(`rank_blk`, `rank_chk`): a block row `j` has rank `j` if `blkRows = k - 1`, else the number
of distinct blocks up to the column minus one; a checksum row `k - 1 + t` has rank
`blkRows + Σ_{t' < t} or_{t'}`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Generic: ranges in blocks -/

lemma range_mul_eq (M : ℕ) : ∀ n : ℕ,
    List.range (n * M) = (List.range n).flatMap fun q => (List.range M).map fun j => q * M + j
  | 0 => by simp
  | n + 1 => by
    rw [show (n + 1) * M = n * M + M by ring, List.range_add, range_mul_eq M n, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]

lemma filter_range_mul (M n : ℕ) (P : ℕ → Bool) :
    (List.range (n * M)).filter (fun σ => P (σ % M)) =
      (List.range n).flatMap fun q => ((List.range M).filter P).map fun j => q * M + j := by
  rw [range_mul_eq, List.filter_flatMap]
  refine List.flatMap_congr fun q _ => ?_
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun j hj => ?_
  rw [List.mem_range] at hj
  simp [Function.comp, Nat.mul_add_mod_of_lt hj]

lemma idxOf_map_inj {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → β}
    (hf : Function.Injective f) (a : α) : ∀ L : List α, (L.map f).idxOf (f a) = L.idxOf a
  | [] => rfl
  | b :: L => by
    simp only [List.map_cons, List.idxOf_cons, idxOf_map_inj hf a L]
    by_cases h : b = a
    · subst h; simp
    · have : f b ≠ f a := fun h' => h (hf h')
      rw [beq_false_of_ne this, beq_false_of_ne h]

lemma idxOf_blocks (M : ℕ) (L : List ℕ) (hL : ∀ j ∈ L, j < M) {j : ℕ} (hj : j ∈ L) :
    ∀ (n q : ℕ), q < n →
      ((List.range n).flatMap fun q' => L.map fun j' => q' * M + j').idxOf (q * M + j) =
        q * L.length + L.idxOf j
  | 0, _, h => absurd h (by omega)
  | n + 1, q, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hjM := hL j hj
    by_cases hq : q < n
    · rw [List.idxOf_append_of_mem]
      · exact idxOf_blocks M L hL hj n q hq
      · exact List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, List.mem_map.mpr ⟨j, hj, rfl⟩⟩
    · have hqn : q = n := by omega
      subst hqn
      rw [List.idxOf_append_of_notMem]
      · rw [List.length_flatMap]
        simp only [List.length_map, List.map_const', List.sum_replicate, List.length_range,
          smul_eq_mul]
        congr 1
        have hinj : Function.Injective fun j' => q * M + j' := fun a b h => by simpa using h
        rw [idxOf_map_inj hinj]
      · intro hm
        obtain ⟨q', hq', hm⟩ := List.mem_flatMap.mp hm
        obtain ⟨j', hj', he⟩ := List.mem_map.mp hm
        rw [List.mem_range] at hq'
        have := hL j' hj'
        have : q' * M + j' < q * M := by
          calc q' * M + j' < (q' + 1) * M := by rw [add_mul, one_mul]; omega
            _ ≤ q * M := Nat.mul_le_mul_right _ (by omega)
        omega

variable {k ℓ : ℕ}

/-! ## Steps and coefficient steps -/

/-- The nonzero rows of column `c`, increasing. -/
def rowsL (c : Coord k ℓ) : List ℕ := (List.range (k - 1 + ℓ)).filter fun j => decide (rowNZ j c)

/-- **The steps of a column**, q-major. -/
lemma stepsC_eq (c : Coord k ℓ) : stepsC c =
    (List.range (k + 1)).flatMap fun q => (rowsL c).map fun j => q * (k - 1 + ℓ) + j := by
  rw [stepsC, numSteps, rowsL, ← filter_range_mul]
  refine List.filter_congr fun σ _ => ?_
  simp only [ne_eq, ent_ne_zero_iff]

variable (I : ImplicitParitySystem k ℓ)

open Classical in
/-- The rows nonzero on the domain of `e`, increasing. -/
noncomputable def rowsR (e : Fin I.schemas.length) : List ℕ :=
  (List.range (k - 1 + ℓ)).filter fun j => decide (∃ c ∈ dom I e, rowNZ j c)

open Classical in
lemma coefSteps_eq (e : Fin I.schemas.length) : coefSteps I e =
    (List.range (k + 1)).flatMap fun q => (rowsR I e).map fun j => q * (k - 1 + ℓ) + j := by
  rw [coefSteps, numSteps, rowsR, ← filter_range_mul]
  refine List.filter_congr fun σ _ => ?_
  simp only [ne_eq, ent_ne_zero_iff]

lemma rowsL_sub {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) {j : ℕ}
    (hj : j ∈ rowsL c) : j ∈ rowsR I e := by
  simp only [rowsL, rowsR, List.mem_filter, decide_eq_true_eq] at hj ⊢
  exact ⟨hj.1, c, hc, hj.2⟩

/-- **The coefficient index of an entry.** -/
lemma idxOf_coefSteps {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) {q j : ℕ}
    (hq : q < k + 1) (hj : j ∈ rowsL c) :
    (coefSteps I e).idxOf (q * (k - 1 + ℓ) + j) =
      q * (rowsR I e).length + (rowsR I e).idxOf j := by
  rw [coefSteps_eq]
  refine idxOf_blocks _ _ (fun j hj => ?_) (rowsL_sub I hc hj) _ _ hq
  simp only [rowsR, List.mem_filter, List.mem_range] at hj; exact hj.1

end Lax119563Proofs.Compiler

end Compiler_PEmitSteps

/-! ### Formerly `Lax119563Proofs.Compiler.PEmitRank` -/

section Compiler_PEmitRank

/-!
# Pass `P4` (list level): the ranks of the rows of a column

The coefficient index of an entry needs `rank j = idxOf j (rowsR I e)` for the rows `j` of the
column. With `bd = blockDescription c.2` (bits of the column) and `os = orsL D` (the OR of the
bits over the domain, from the `P2` record):
* checksum rows (`chkRanks_eq`): the ranks of the rows `k - 1 + t` (`bd[t] = 1`) are
  `chkRk os bd (blkRows D)`, computed by one pass over the bits (`blkRows + Σ_{t'<t} os[t']`);
* block rows (`rank_blk`): `rank j = (range j).countP PA` (`PA j`: some coordinate of the
  domain has block `j` or `k - 1`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Generic -/

/-- The index of an element of a filtered range is the count below it. -/
lemma idxOf_filter_range (P : ℕ → Bool) {j : ℕ} (hj : P j = true) : ∀ n, j < n →
    ((List.range n).filter P).idxOf j = (List.range j).countP P
  | 0, h => absurd h (by omega)
  | n + 1, h => by
    rw [List.range_succ, List.filter_append]
    by_cases hjn : j < n
    · rw [List.idxOf_append_of_mem (List.mem_filter.mpr ⟨List.mem_range.mpr hjn, hj⟩)]
      exact idxOf_filter_range P hj n hjn
    · have : j = n := by omega
      subst this
      rw [List.idxOf_append_of_notMem (by simp), List.countP_eq_length_filter]
      simp [hj]

/-- The checksum ranks along the bits: `bs` the bits of the column, `os` the OR bits. -/
def chkRk : List ℕ → List ℕ → ℕ → List ℕ
  | o :: os, b :: bs, p => (if b = 1 then [p] else []) ++ chkRk os bs (p + o)
  | _, _, _ => []

lemma chkRk_eq : ∀ (os bs : List ℕ) (p : ℕ), os.length = bs.length →
    ((List.range bs.length).filter (fun t => decide (bs.getD t 0 = 1))).map
      (fun t => p + (os.take t).sum) = chkRk os bs p
  | [], [], _, _ => rfl
  | o :: os, b :: bs, p, h => by
    have ih := chkRk_eq os bs (p + o) (by simpa using h)
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map, chkRk, ← ih]
    have e2 : (List.range bs.length).filter ((fun t => decide ((b :: bs).getD t 0 = 1)) ∘
        Nat.succ) = (List.range bs.length).filter (fun t => decide (bs.getD t 0 = 1)) :=
      List.filter_congr fun t _ => by simp
    rw [e2]
    by_cases hb : b = 1 <;> simp [hb, List.map_map, Function.comp_def, add_assoc]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## The rows of the domain -/

lemma range_split' : List.range (k - 1 + ℓ) =
    List.range (k - 1) ++ (List.range ℓ).map fun t => k - 1 + t := List.range_add ..

open Classical in
/-- The block-row predicate of a domain. -/
noncomputable def PA (e : Fin I.schemas.length) (j : ℕ) : Bool :=
  decide (∃ c ∈ coordList (dom I e), (c.1 : ℕ) = j ∨ (c.1 : ℕ) = k - 1)

open Classical in
/-- The checksum-row predicate of a domain. -/
noncomputable def PB (e : Fin I.schemas.length) (t : ℕ) : Bool :=
  decide (∃ t' : Fin ℓ, (t' : ℕ) = t ∧ ∃ c ∈ coordList (dom I e), c.2 t' ≠ 0)

open Classical in
lemma rowsR_eq (e : Fin I.schemas.length) : rowsR I e =
    (List.range (k - 1)).filter (PA I e) ++ ((List.range ℓ).filter (PB I e)).map
      fun t => k - 1 + t := by
  rw [rowsR, range_split', List.filter_append, List.filter_map]
  congr 1
  · refine List.filter_congr fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [PA, rowNZ, mem_coordList, decide_eq_decide]
    constructor
    · rintro ⟨c, hc, ⟨-, h⟩ | ⟨h, -⟩⟩
      · exact ⟨c, hc, h⟩
      · omega
    · rintro ⟨c, hc, h⟩; exact ⟨c, hc, Or.inl ⟨hj, h⟩⟩
  · congr 1
    refine List.filter_congr fun t ht => ?_
    simp only [Function.comp, PB, rowNZ, mem_coordList, decide_eq_decide]
    constructor
    · rintro ⟨c, hc, ⟨h, -⟩ | ⟨-, t', ht', h⟩⟩
      · omega
      · exact ⟨t', by omega, c, hc, h⟩
    · rintro ⟨t', ht', c, hc, h⟩; exact ⟨c, hc, Or.inr ⟨by omega, t', by omega, h⟩⟩

lemma length_filter_PA (e : Fin I.schemas.length) :
    ((List.range (k - 1)).filter (PA I e)).length = blkRows (coordList (dom I e)) := by
  rw [← List.countP_eq_length_filter, blkRows]; rfl

/-- **Block-row ranks.** -/
lemma rank_blk (e : Fin I.schemas.length) {j : ℕ} (hj : j < k - 1) (hP : PA I e j = true) :
    (rowsR I e).idxOf j = (List.range j).countP (PA I e) := by
  rw [rowsR_eq, List.idxOf_append_of_mem (List.mem_filter.mpr ⟨List.mem_range.mpr hj, hP⟩)]
  exact idxOf_filter_range _ hP _ hj

lemma orsL_getD (cs : List (Coord k ℓ)) (t : ℕ) (ht : t < ℓ) :
    (orsL cs).getD t 0 = if ∃ c ∈ cs, c.2 ⟨t, ht⟩ ≠ 0 then 1 else 0 := by
  simp [orsL, List.getD_eq_getElem?_getD, ht]

lemma countP_PB (e : Fin I.schemas.length) : ∀ t, t ≤ ℓ →
    (List.range t).countP (PB I e) = ((orsL (coordList (dom I e))).take t).sum
  | 0, _ => by simp
  | t + 1, h => by
    rw [List.range_succ, List.countP_append, countP_PB e t (by omega)]
    have hl : t < (orsL (coordList (dom I e))).length := by rw [length_orsL]; omega
    rw [List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some, List.sum_append,
      List.sum_singleton]
    congr 1
    have e1 := orsL_getD (coordList (dom I e)) t (by omega)
    rw [List.getD_eq_getElem _ _ hl] at e1
    rw [e1]
    by_cases h' : ∃ c ∈ coordList (dom I e), c.2 ⟨t, by omega⟩ ≠ 0
    · have hP : PB I e t = true := decide_eq_true ⟨⟨t, by omega⟩, rfl, h'⟩
      rw [if_pos h']; simp [List.countP_singleton, hP]
    · have hP : PB I e t = false := by
        refine decide_eq_false ?_
        rintro ⟨t', ht', c, hc, h''⟩
        have : t' = ⟨t, by omega⟩ := Fin.ext ht'
        rw [this] at h''
        exact h' ⟨c, hc, h''⟩
      rw [if_neg h']; simp [List.countP_singleton, hP]

/-- **Checksum-row ranks.** -/
lemma rank_chk (e : Fin I.schemas.length) {t : ℕ} (ht : t < ℓ) (hP : PB I e t = true) :
    (rowsR I e).idxOf (k - 1 + t) =
      blkRows (coordList (dom I e)) + ((orsL (coordList (dom I e))).take t).sum := by
  rw [rowsR_eq, List.idxOf_append_of_notMem (by simp), length_filter_PA]
  congr 1
  have hinj : Function.Injective fun t => k - 1 + t := fun a b h => by simpa using h
  rw [idxOf_map_inj hinj, idxOf_filter_range _ hP _ ht,
    countP_PB I e t ht.le]

/-! ## The rows of a column -/

lemma filter_range_eq_single (a : ℕ) : ∀ n,
    (List.range n).filter (fun j => decide (j = a)) = if a < n then [a] else []
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, filter_range_eq_single a n]
    by_cases h : a = n
    · subst h; simp
    · have : ¬ a < n + 1 ∨ a < n := by omega
      rcases this with h1 | h1
      · rw [if_neg (by omega), if_neg h1]; simp [Ne.symm h]
      · rw [if_pos h1, if_pos (by omega)]; simp [Ne.symm h]

lemma length_blockDescription' (b : BlockCoord ℓ) : (blockDescription b).length = ℓ := by
  simp [blockDescription]

/-- The checksum rows of a column, as bit indices. -/
def chkT (c : Coord k ℓ) : List ℕ :=
  (List.range ℓ).filter fun t => decide ((blockDescription c.2).getD t 0 = 1)

lemma bd_getD (c : Coord k ℓ) {t : ℕ} (ht : t < ℓ) :
    (blockDescription c.2).getD t 0 = (c.2 ⟨t, ht⟩).val := by
  simp [blockDescription, List.getD_eq_getElem?_getD, ht]

/-- **The rows of a column**: the block part, then the checksum rows. -/
lemma rowsL_eq (c : Coord k ℓ) : rowsL c =
    (if (c.1 : ℕ) + 1 < k then [(c.1 : ℕ)] else List.range (k - 1)) ++
      (chkT c).map fun t => k - 1 + t := by
  rw [rowsL, range_split', List.filter_append, List.filter_map]
  have hc := c.1.2
  congr 1
  · split_ifs with h
    · rw [show [(c.1 : ℕ)] = (List.range (k - 1)).filter (fun j => decide (j = (c.1 : ℕ))) by
        rw [filter_range_eq_single, if_pos (by omega)]]
      refine List.filter_congr fun j hj => ?_
      rw [List.mem_range] at hj
      simp only [rowNZ, decide_eq_decide]
      constructor
      · rintro (⟨-, h' | h'⟩ | ⟨h', -⟩) <;> omega
      · intro h'; exact Or.inl ⟨hj, Or.inl h'.symm⟩
    · rw [List.filter_eq_self.mpr]
      intro j hj
      rw [List.mem_range] at hj
      simp only [rowNZ, decide_eq_true_eq]
      exact Or.inl ⟨hj, Or.inr (by omega)⟩
  · congr 1
    unfold chkT
    refine List.filter_congr fun t ht => ?_
    rw [List.mem_range] at ht
    simp only [Function.comp, rowNZ, decide_eq_decide, bd_getD c ht]
    have hv := ZMod.val_lt (c.2 ⟨t, ht⟩)
    constructor
    · rintro (⟨h, -⟩ | ⟨-, t', ht', h⟩)
      · omega
      · have : t' = ⟨t, ht⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
        subst this
        rcases Lax119563Proofs.Reduction.zmod2_cases (c.2 ⟨t, ht⟩) with h0 | h0
        · exact absurd h0 h
        · rw [h0]; rfl
    · intro h
      refine Or.inr ⟨by omega, ⟨t, ht⟩, by simp, fun h0 => ?_⟩
      rw [h0] at h; simp at h

/-- **The checksum ranks of a column** by the bit pass. -/
lemma chkRanks_eq (e : Fin I.schemas.length) {c : Coord k ℓ} (hc : c ∈ dom I e) :
    ((chkT c).map fun t => k - 1 + t).map (rowsR I e).idxOf =
      chkRk (orsL (coordList (dom I e))) (blockDescription c.2)
        (blkRows (coordList (dom I e))) := by
  rw [← chkRk_eq _ _ _ (by rw [length_orsL, length_blockDescription']), List.map_map]
  unfold chkT
  rw [length_blockDescription']
  refine List.map_congr_left fun t ht => ?_
  obtain ⟨ht1, ht2⟩ := List.mem_filter.mp ht
  rw [List.mem_range] at ht1
  simp only [decide_eq_true_eq, bd_getD c ht1] at ht2
  refine rank_chk I e ht1 ?_
  simp only [PB, decide_eq_true_eq]
  refine ⟨⟨t, ht1⟩, rfl, c, mem_coordList.mpr hc, fun h0 => ?_⟩
  rw [h0] at ht2; simp at ht2

end Lax119563Proofs.Compiler

end Compiler_PEmitRank

/-! ### Formerly `Lax119563Proofs.Compiler.PEmitBlk` -/

section Compiler_PEmitBlk

/-!
# Pass `P4` (list level): block ranks by the running count of blocks

For the column `c = D[r]` of a domain `D = coordList (dom I e)` with `c.1 < k - 1`, the rank of
its block row is `c.1` if `blkRows D = k - 1`, and otherwise the number of distinct blocks of
`D[0..r]` minus one, i.e. `dChg k (blocks of D.take (r + 1)) - 1` (`rank_blk_eq`), which the
program keeps in a register (`dChg_append`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma countP_range_all (P : ℕ → Bool) {n m : ℕ} (hm : m ≤ n)
    (h : (List.range n).countP P = n) : (List.range m).countP P = m := by
  have hall := List.countP_eq_length.mp (by rw [List.length_range]; exact h)
  rw [List.countP_eq_length.mpr fun j hj => hall j (List.mem_range.mpr
    (lt_of_lt_of_le (List.mem_range.mp hj) hm)), List.length_range]

/-- **Block-row ranks by the running count of blocks.** -/
theorem rank_blk_eq (e : Fin I.schemas.length) {r : ℕ}
    (hr : r < (coordList (dom I e)).length)
    (hc : ((coordList (dom I e))[r].1 : ℕ) + 1 < k) :
    (rowsR I e).idxOf ((coordList (dom I e))[r].1 : ℕ) =
      if blkRows (coordList (dom I e)) = k - 1 then ((coordList (dom I e))[r].1 : ℕ)
      else dChg k (((coordList (dom I e)).take (r + 1)).map fun c => (c.1 : ℕ)) - 1 := by
  set D := coordList (dom I e) with hD
  set c := D[r] with hcdef
  have hcD : c ∈ D := List.getElem_mem hr
  have hPc : PA I e (c.1 : ℕ) = true := by
    simp only [PA, decide_eq_true_eq]; exact ⟨c, hcD, Or.inl rfl⟩
  rw [rank_blk I e (by omega) hPc]
  split_ifs with hB
  · have h1 : (List.range (k - 1)).countP (PA I e) = blkRows D := by
      rw [blkRows]; exact List.countP_congr (fun j _ => by simp [PA, hD])
    exact countP_range_all _ (show (c.1 : ℕ) ≤ k - 1 by omega) (h1.trans hB)
  · -- no coordinate of block `k - 1`
    have hno : ∀ c' ∈ D, (c'.1 : ℕ) ≠ k - 1 := by
      intro c' hc' h'
      apply hB
      rw [blkRows, List.countP_eq_length.mpr, List.length_range]
      intro j _
      simp only [decide_eq_true_eq]; exact ⟨c', hc', Or.inr h'⟩
    have hPA : ∀ j, PA I e j = true ↔ ∃ c' ∈ D, (c'.1 : ℕ) = j := by
      intro j
      simp only [PA, decide_eq_true_eq, ← hD]
      constructor
      · rintro ⟨c', hc', h | h⟩
        · exact ⟨c', hc', h⟩
        · exact absurd h (hno c' hc')
      · rintro ⟨c', hc', h⟩; exact ⟨c', hc', Or.inl h⟩
    set l := (D.take (r + 1)).map fun c => (c.1 : ℕ) with hl
    have hsorted : l.Pairwise (· ≤ ·) := by
      have := pairwise_blocks (dom I e)
      rw [← hD] at this
      exact this.sublist ((List.take_sublist _ _).map _)
    have hkl : k ∉ l := by
      simp only [hl, List.mem_map, not_exists, not_and]
      intro c' _ h'; have := c'.1.2; omega
    rw [dChg_eq k l hsorted (Or.inr hkl), Finset.erase_eq_of_notMem (by simpa using hkl)]
    -- the blocks of `l` are the blocks `< c.1` of `D`, and `c.1`
    have hpw : ∀ i j (hi : i < D.length) (hj : j < D.length), i < j →
        (D[i].1 : ℕ) ≤ D[j].1 := by
      intro i j hi hj hij
      have := List.pairwise_iff_getElem.mp (pairwise_blocks (dom I e)) i j (by simpa [hD] using hi)
        (by simpa [hD] using hj) hij
      simpa [hD] using this
    have hmem : ∀ x, x ∈ l ↔ x = (c.1 : ℕ) ∨ (x < c.1 ∧ PA I e x = true) := by
      intro x
      rw [hPA]
      constructor
      · intro hx
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hx
        obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.mp hc'
        have hi1 : i ≤ r := by omega
        have hiD : i < D.length := by omega
        rcases Nat.lt_or_eq_of_le hi1 with h | h
        · have := hpw i r hiD hr h
          rw [← hcdef] at this
          rcases Nat.lt_or_eq_of_le this with h' | h'
          · exact Or.inr ⟨h', D[i], List.getElem_mem _, rfl⟩
          · exact Or.inl h'
        · subst h; exact Or.inl rfl
      · rintro (rfl | ⟨hx, c', hc', rfl⟩)
        · exact List.mem_map.mpr ⟨c, List.mem_take_iff_getElem.mpr ⟨r, by omega, rfl⟩, rfl⟩
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc'
          have hir : i ≤ r := by
            by_contra h
            have := hpw r i hr hi (by omega)
            rw [← hcdef] at this
            omega
          exact List.mem_map.mpr ⟨D[i], List.mem_take_iff_getElem.mpr ⟨i, by omega, rfl⟩, rfl⟩
    have hfs : l.toFinset = insert (c.1 : ℕ) ((List.range (c.1 : ℕ)).filter (PA I e)).toFinset := by
      ext x
      simp only [List.mem_toFinset, Finset.mem_insert, List.mem_filter, List.mem_range, hmem]
    rw [hfs, Finset.card_insert_of_notMem (by simp), List.toFinset_card_of_nodup
      ((List.nodup_range).filter _), ← List.countP_eq_length_filter]
    omega

end Lax119563Proofs.Compiler

end Compiler_PEmitBlk

/-! ### Formerly `Lax119563Proofs.Compiler.PEmitSch` -/

section Compiler_PEmitSch

/-!
# Pass `P4` (list level): the edges of a schema in program form

`schE_eq`: the edges of schema `e` are the junction/link edges per column (`colE1`, with the
column index `r`) followed by the update edges per column and entry (`colE2`): for
`q ≤ k` and the rows `j ∈ rowsL c` (index `p`), the entry `t = q |rowsL c| + p` has the hub
`schBase + |D| colW + 4 (entBefore + t)` and the coefficient index `q |rowsR| + rank j`
(`updEnt`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Generic -/

lemma zipIdx_eq_map_idxOf {α : Type*} [BEq α] [LawfulBEq α] {L : List α} (hL : L.Nodup) :
    L.zipIdx = L.map fun c => (c, L.idxOf c) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_zipIdx, List.getElem_map, Nat.zero_add]
  rw [hL.idxOf_getElem]

lemma flatMap_idxOf {α β : Type*} [BEq α] [LawfulBEq α] {L : List α} (hL : L.Nodup)
    (g : α → ℕ → List β) :
    L.flatMap (fun c => g c (L.idxOf c)) = L.zipIdx.flatMap fun q => g q.1 q.2 := by
  rw [zipIdx_eq_map_idxOf hL, List.flatMap_map]

lemma zipIdx_flatMap_range {α β γ : Type*} (L : List α) (g : ℕ → α → β)
    (F : β × ℕ → List γ) : ∀ (m s : ℕ),
    (((List.range m).flatMap fun q => L.map (g q)).zipIdx s).flatMap F =
      (List.range m).flatMap fun q => L.zipIdx.flatMap fun x =>
        F (g q x.1, s + q * L.length + x.2)
  | 0, _ => rfl
  | m + 1, s => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.zipIdx_append,
      List.flatMap_append, zipIdx_flatMap_range L g F m s, List.flatMap_append,
      List.flatMap_singleton]
    congr 1
    rw [List.zipIdx_map, List.flatMap_map]
    have hl : ((List.range m).flatMap fun q => L.map (g q)).length = m * L.length := by
      rw [List.length_flatMap]; simp [List.map_const', List.sum_replicate]
    rw [hl]
    have : ∀ (t : ℕ), (L.zipIdx t) = (L.zipIdx).map fun x => (x.1, t + x.2) := by
      intro t; rw [List.zipIdx_eq_map_add]
    rw [this, List.flatMap_map]
    rfl

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (ε : ZMod 2)

/-! ## The sections of a schema -/

/-- The junction and link edges of column `c` (index `r`) of schema `e`. -/
noncomputable def colE1 (e : Fin I.schemas.length) (c : Coord k ℓ) (r : ℕ) : List (ℕ × ℕ) :=
  (if isTern (sch I e) then hubE I ε (.junc e c) bits2 (schBase I e + r * colW I e) else []) ++
    hubE I ε (.link e c) bits1
      (schBase I e + r * colW I e + (if isTern (sch I e) then 4 else 0))

/-- The edges of schema `e`. -/
noncomputable def schE (e : Fin I.schemas.length) : List (ℕ × ℕ) :=
  (hubsCls I e).flatMap fun p => hubE I ε p.1 p.2 (hubStart I p.1)

lemma gEdges_eq_schE : gEdges I ε = (List.finRange I.schemas.length).flatMap (schE I ε) := rfl

/-- **The edges of a schema, by sections.** -/
theorem schE_eq (e : Fin I.schemas.length) : schE I ε e =
    (coordList (dom I e)).zipIdx.flatMap (fun q => colE1 I ε e q.1 q.2) ++
      (coordList (dom I e)).flatMap fun c => (stepsC c).zipIdx.flatMap fun q =>
        hubE I ε (.upd e q.1 c) bits2 (schBase I e + (coordList (dom I e)).length * colW I e +
          4 * (entBefore I e c + q.2)) := by
  have hnd := nodup_coordList (dom I e)
  rw [schE, hubsCls, List.flatMap_append, List.flatMap_assoc, List.flatMap_assoc]
  congr 1
  · rw [← flatMap_idxOf hnd (fun c r => colE1 I ε e c r)]
    refine List.flatMap_congr fun c _ => ?_
    unfold colE1
    split <;> next h => simp [hubStart, h]
  · refine List.flatMap_congr fun c _ => ?_
    rw [List.flatMap_map, ← flatMap_idxOf (nodup_stepsC c)
      (fun σ t => hubE I ε (.upd e σ c) bits2 (schBase I e + (coordList (dom I e)).length *
        colW I e + 4 * (entBefore I e c + t)))]
    rfl

end Lax119563Proofs.Compiler

end Compiler_PEmitSch
