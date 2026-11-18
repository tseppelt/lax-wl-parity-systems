import Lax119563Proofs.Compiler.CSkip
import Lax119563Proofs.Reduction.SysDesc

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

end Lax119563Proofs.Compiler
