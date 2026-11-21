import Lax119563Proofs.Compiler.Part1
import Lax119563Proofs.Compiler.Part2
import Lax119563Proofs.Compiler.Part3

/-! ### Formerly `Lax119563Proofs.Compiler.PEmitCol2` -/

section Compiler_PEmitCol2

/-!
# Pass `P4` (list level): the update edges of a column in loop form

`colE2_eq`: the update edges of column `c` are, for `q ≤ k` and the ranks `ρ` of its rows
(`rkL`, index `p`), the edges of the entry `t = q n + p` (`n = |rowsL c|`): hub
`hb + 4 (EB + t)`, coefficient position `coefBase + 2 (q |rowsR| + ρ)` (`updEnt`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (ε : ZMod 2)

/-- The ranks of the rows of a column in the nonzero rows of the domain. -/
noncomputable def rkL (e : Fin I.schemas.length) (c : Coord k ℓ) : List ℕ :=
  (rowsL c).map (rowsR I e).idxOf

/-- The edges of the update with entry index `t` and coefficient index `ci`. -/
noncomputable def updEnt (e : Fin I.schemas.length) (c : Coord k ℓ) (hb t ci : ℕ) :
    List (ℕ × ℕ) :=
  if t = 0 ∧ isTern (sch I e) = false then
    (List.range 4).flatMap fun i =>
      updF1 (hb + 4 * (entBefore I e c + t) + i) (trackBase I e + 2 * entBefore I e c)
        (coefBase I e + 2 * ci) (slotPos I ε (startCls I e c) (((i / 2 : ℕ)) : ZMod 2))
        (i / 2) (i % 2)
  else
    (List.range 4).flatMap fun i =>
      updE1 (hb + 4 * (entBefore I e c + t) + i) (prevBase I e c t)
        (trackBase I e + 2 * (entBefore I e c + t)) (coefBase I e + 2 * ci) (i / 2) (i % 2)

lemma idxOf_of_mem_zipIdx {α : Type*} [BEq α] [LawfulBEq α] {L : List α} (hL : L.Nodup)
    {x : α} {t : ℕ} (h : (x, t) ∈ L.zipIdx) : x ∈ L ∧ L.idxOf x = t := by
  obtain ⟨ht, hx⟩ := List.mem_zipIdx' h
  rw [hx]
  exact ⟨List.getElem_mem _, hL.idxOf_getElem _ _⟩

/-- **The update edges of a column.** -/
theorem colE2_eq {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) (hb : ℕ) :
    (stepsC c).zipIdx.flatMap (fun q => hubE I ε (.upd e q.1 c) bits2
        (hb + 4 * (entBefore I e c + q.2))) =
      (List.range (k + 1)).flatMap fun q => (rkL I e c).zipIdx.flatMap fun x =>
        updEnt I ε e c hb (q * (rowsL c).length + x.2) (q * (rowsR I e).length + x.1) := by
  -- first: per entry, by the hub lemmas
  have h1 : (stepsC c).zipIdx.flatMap (fun q => hubE I ε (.upd e q.1 c) bits2
        (hb + 4 * (entBefore I e c + q.2))) =
      (stepsC c).zipIdx.flatMap fun q => updEnt I ε e c hb q.2 ((coefSteps I e).idxOf q.1) := by
    refine List.flatMap_congr fun q hq => ?_
    obtain ⟨hmem, hidx⟩ := idxOf_of_mem_zipIdx (nodup_stepsC c) (x := q.1) (t := q.2) hq
    unfold updEnt
    split_ifs with h
    · rw [hubE_updF I ε hc hmem (by rw [hidx]; exact h.1) h.2]
    · rw [hubE_upd I ε hc hmem (by
        rcases Nat.eq_zero_or_pos q.2 with h0 | h0
        · right
          cases ht : isTern (sch I e)
          · exact absurd ⟨h0, ht⟩ h
          · rfl
        · left; rw [hidx]; exact h0), hidx]
  rw [h1]
  conv_lhs => rw [stepsC_eq]
  rw [zipIdx_flatMap_range (rowsL c) (fun q j => q * (k - 1 + ℓ) + j)
    (fun q => updEnt I ε e c hb q.2 ((coefSteps I e).idxOf q.1)) (k + 1) 0]
  refine List.flatMap_congr fun q hq => ?_
  rw [rkL, List.zipIdx_map, List.flatMap_map]
  refine List.flatMap_congr fun x hx => ?_
  have hj : x.1 ∈ rowsL c := (List.mem_zipIdx' hx).2 ▸ List.getElem_mem _
  simp only [Prod.map, id, Nat.zero_add]
  rw [idxOf_coefSteps I hc (List.mem_range.mp hq) hj]

end Lax119563Proofs.Compiler

end Compiler_PEmitCol2

/-! ### Formerly `Lax119563Proofs.Compiler.PEmitSizes` -/

section Compiler_PEmitSizes

/-!
# Pass `P4` (list level): the class sizes

`clsSizes_eq`: the class sizes are, per schema (`schSizes`), `|D|` times `[4, 2]` (ternary)
or `[2]`, then `nEnt` times `4`, then (ternary) `|D|` times `2`, `nEnt` times `2`,
`|coefSteps|` times `2`; then per location `|coordList D_v|` times `labsN v`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The column sizes of the junction/link section. -/
def jlSizes (tern : Bool) : List ℕ := if tern then [4, 2] else [2]

/-- The class sizes of schema `e`. -/
noncomputable def schSizes (e : Fin I.schemas.length) : List ℕ :=
  ((coordList (dom I e)).flatMap fun _ => jlSizes (isTern (sch I e))) ++
    List.replicate (nEnt I e) 4 ++
    ((coordList (dom I e)).flatMap fun _ => if isTern (sch I e) then [2] else []) ++
    List.replicate (nEnt I e) 2 ++ List.replicate (coefSteps I e).length 2

/-- The class sizes of location `v`. -/
def locSizes (v : Fin I.numLocations) : List ℕ :=
  List.replicate (coordList (I.domain v)).length (labsN I v)

lemma map_stepsC_sizes (L : List (Coord k ℓ)) (n : ℕ) :
    L.flatMap (fun c => (stepsC c).map fun _ => n) =
      List.replicate ((L.map fun c => (stepsC c).length).sum) n := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.flatMap_cons, ih, List.map_cons, List.sum_cons, List.replicate_add, List.map_const']

lemma flatMap_rep (L : List (Coord k ℓ)) (n : ℕ) :
    L.flatMap (fun c => List.replicate (stepsC c).length n) =
      List.replicate ((L.map fun c => (stepsC c).length).sum) n := by
  rw [← map_stepsC_sizes]; simp only [List.map_const']

lemma schSizes_eq (e : Fin I.schemas.length) :
    (hubsCls I e ++ nonhubsCls I e).map (fun p => p.2.length) = schSizes I e := by
  simp only [hubsCls, nonhubsCls, List.map_append, List.map_flatMap, List.map_map,
    Function.comp_def, schSizes, nEnt, bits1, bits2, List.length_cons, List.length_nil,
    map_stepsC_sizes, List.append_assoc, List.map_const', List.length_map, flatMap_rep]
  congr 1
  · refine List.flatMap_congr fun c _ => ?_
    unfold jlSizes; split <;> rfl
  · congr 2
    refine List.flatMap_congr fun c _ => ?_
    split <;> rfl

/-- **The class sizes.** -/
theorem clsSizes_eq : clsSizes I =
    (List.finRange I.schemas.length).flatMap (schSizes I) ++
      (List.finRange I.numLocations).flatMap (locSizes I) := by
  rw [clsSizes, ordCls, List.map_append, List.map_flatMap, List.map_flatMap]
  congr 1
  · exact List.flatMap_congr fun e _ => schSizes_eq I e
  · refine List.flatMap_congr fun v _ => ?_
    simp only [locSizes, labsN, List.map_map, Function.comp_def, List.map_const']

end Lax119563Proofs.Compiler

end Compiler_PEmitSizes

/-! ### Formerly `Lax119563Proofs.Compiler.P4Loc` -/

section Compiler_P4Loc

/-!
# Pass `P4` (program): the location sizes

The location loop of `P4` (`p4LLoop`): per location `v` read `ι(v)` and `|D_v|`, push
`labsN v` (`|D_v|` times) on `qSzA`, adding to `rNt`, skip the coordinates
(**`p4LBody_good`**, **`p4LLoop_good`**). Afterwards `qSzA` holds
`((finRange W).flatMap (locSizes I)).reverse` and `rNt = locOff I W`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The location sizes of the first `j` locations. -/
noncomputable def locUpTo (j : ℕ) : List ℕ :=
  ((List.finRange I.numLocations).take j).flatMap (locSizes I)

lemma locUpTo_succ {j : ℕ} (hj : j < I.numLocations) :
    locUpTo I (j + 1) = locUpTo I j ++ locSizes I ⟨j, hj⟩ := by
  rw [locUpTo, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [locUpTo]

lemma locUpTo_all : locUpTo I I.numLocations = (List.finRange I.numLocations).flatMap (locSizes I) := by
  rw [locUpTo, List.take_of_length_le (by simp)]

lemma locSizes_eq_rep (v : Fin I.numLocations) :
    locSizes I v = List.replicate (coordList (I.domain v)).length
      (1 + (if initNum (I.init v) < 1 then 1 else 0)) := by
  rw [locSizes, labsN_eq]

lemma locSize_eq_mul (v : Fin I.numLocations) :
    locSize I v = (coordList (I.domain v)).length *
      (1 + (if initNum (I.init v) < 1 then 1 else 0)) := by
  rw [locSize_eq]; split_ifs <;> ring

/-- The label count of the current location: `1 + [ι = ⋆]`. -/
def labEx : Ex CR := .add (.const 1) (.lt (rv rA) (.const 1))

/-- The body of the location loop of `P4`. -/
def p4LBody : CStm CR CQ :=
  .seq (rdNumS rA rP rT) (.seq (rdNumS rD rP rT) (.seq (.set rLab labEx)
    (.seq (repPushS qSzA rLab rD rK rNt) (.seq (skipBlocksS rD rL1 rK rI rT)
      (.set rJ (.add (rv rJ) (.const 1)))))))

/-- The location loop of `P4`. -/
def p4LLoop : CStm CR CQ := .loop (.lt (rv rJ) (rv rW)) p4LBody

/-- The loop invariant. -/
def p4LInv (st s : NSt CR CQ) : Prop :=
  s.env rW = I.numLocations ∧ s.env rL1 = ℓ + 1 ∧
    s.env rJ ≤ I.numLocations ∧ s.pos = posAt I (s.env rJ) ∧
    s.env rNt = locOff I (s.env rJ) ∧
    s.stk = Function.update st.stk qSzA ((locUpTo I (s.env rJ)).reverse ++ st.stk qSzA) ∧
    s.out = st.out

lemma p4LBody_arith {N U la ld lf d : ℕ} (hU : U ≤ N) (hU' : 64 ≤ U) (hdf : N * d ≤ N * lf) :
    (la + 1) * (20 * N) + ((ld + 1) * (20 * N) + ((1 + (1 + 1 + 1) + 1) * N + U +
      ((d + 1) * (20 * N) + ((lf + d + 1) * (50 * N) + ((1 + 1 + 1) * N + U))))) ≤
      150 * N * (la + ld + lf) + 200 * N := by
  nlinarith

/-- One iteration of the location loop. -/
lemma p4LBody_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (st s : NSt CR CQ) (hI : p4LInv I st s) (hc : (Ex.lt (rv rJ) (rv rW)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p4LBody s s'
        (150 * Ex.nodeCost w * ((H I - s.pos) - (H I - s'.pos)) + 200 * Ex.nodeCost w) ∧
      p4LInv I st s' ∧ I.numLocations - s'.env rJ < I.numLocations - s.env rJ ∧
      H I - s'.pos ≤ H I - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  obtain ⟨hW, hL1, hjW, hpos, hnt, hstk, hout⟩ := hI
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
  -- the label count
  set lab := 1 + (if a < 1 then 1 else 0) with hlab
  have r3 := Good.set (x := encodeSystem I) (w := w) (r := rLab) (e := labEx) (st := s2) (by
    simp only [labEx, Ex.Fits, rv, Ex.eval, e2A]
    refine ⟨by omega, ⟨by omega, by omega⟩, by split_ifs <;> omega⟩)
  set s3 := s2.set rLab (labEx.eval s2.env)
  have e3 : ∀ q, q ≠ rLab → s3.env q = s2.env q := fun q hq => by
    simp [s3, Function.update_of_ne hq]
  have e3L : s3.env rLab = lab := by simp [s3, labEx, Ex.eval, rv, e2A, lab]
  have hsz : locOff I (j + 1) = locOff I j + d * lab := by
    rw [locOff_succ I hlt, locSize_eq_mul]
  have hoffH := locOff_le_H I (j + 1)
  have e3N : s3.env rNt = locOff I j := by
    rw [e3 _ (by decide), e2 _ (by decide) (by decide) (by decide) (by decide), hnt]
  -- pushing the sizes
  have r4 := repPushS_good (x := encodeSystem I) (w := w) hw (q := qSzA) (v := rLab) (n := rD)
    (j := rK) (acc := rNt) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) s3 e3L (by rw [e3 _ (by decide), e2D]) e3N (by omega) (by omega)
  set s4 := ((s3.setS qSzA (List.replicate d lab ++ s3.stk qSzA)).set rNt
    (locOff I j + d * lab)).set rK d
  have e4 : ∀ q, q ≠ rK → q ≠ rNt → s4.env q = s3.env q := fun q h1 h2 => by
    simp [s4, Function.update_of_ne h1, Function.update_of_ne h2]
  -- skipping the coordinates
  have hx4 : (encodeSystem I).drop s4.pos = encodeNats bs.flatten ++ rest := by
    show (encodeSystem I).drop s2.pos = _
    simp only [s2, rdNumFinal_pos]
    rw [← List.drop_drop, hx2, List.drop_left]
  obtain ⟨s5, r5, hs5, hp5, ho5, hf5⟩ := skipBlocksS_good (Q := CQ) hw (d := rD) (m := rL1)
    (j := rK) (i := rI) (t := rT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s4 bs (ℓ + 1) hbsM rest hx4
    (by rw [hbsl, e4 _ (by decide) (by decide), e3 _ (by decide)]; exact e2D)
    (by rw [e4 _ (by decide) (by decide), e3 _ (by decide),
        e2 rL1 (by decide) (by decide) (by decide) (by decide), hL1])
    (by rw [hbsl]; omega) (by omega)
  have e5J : s5.env rJ = j := by
    rw [hf5 _ (by decide) (by decide) (by decide), e4 _ (by decide) (by decide),
      e3 _ (by decide), e2 _ (by decide) (by decide) (by decide) (by decide)]
  have r6 := Good.set (x := encodeSystem I) (w := w) (r := rJ) (e := .add (rv rJ) (.const 1))
    (st := s5) (by
      have := W_le I
      simp only [Ex.Fits, Ex.eval, rv, e5J]; omega)
  set s6 := s5.set rJ (Ex.eval s5.env (.add (rv rJ) (.const 1)))
  have e6 : ∀ q, q ≠ rJ → s6.env q = s5.env q := fun q hq => by
    simp [s6, Function.update_of_ne hq]
  have e6J : s6.env rJ = j + 1 := by simp [s6, Ex.eval, rv, e5J]
  have back : ∀ q, q ≠ rJ → q ≠ rK → q ≠ rI → q ≠ rT → q ≠ rNt → q ≠ rLab → q ≠ rD →
      q ≠ rA → q ≠ rP → s6.env q = s.env q := by
    intro q h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [e6 q h1, hf5 q h2 h3 h4, e4 q h2 h5, e3 q h6, e2 q h7 h8 h9 h4]
  have hp6 : s6.pos = s.pos + (encodeNat a).length + (encodeNat d).length +
      (encodeNats bs.flatten).length := by
    rw [NSt.set_pos, hp5]; rfl
  refine ⟨s6, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, ?_, ?_⟩
  · rw [hp6]
    have hΔ : H I - s.pos - (H I - (s.pos + (encodeNat a).length + (encodeNat d).length +
        (encodeNats bs.flatten).length)) = (encodeNat a).length + (encodeNat d).length +
        (encodeNats bs.flatten).length := by omega
    rw [hΔ, hbsl]
    simp only [Ex.size, rv, labEx]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNat a).length = la at *
    generalize (encodeNat d).length = ld at *
    generalize (encodeNats bs.flatten).length = lf at *
    exact p4LBody_arith hU hU' (Nat.mul_le_mul_left N hdf)
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hW]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hL1]
  · rw [e6J]; omega
  · rw [e6J, hp6, hpos, posAt_succ I hlt, locD_eq']
    simp only [encNats_cons, List.length_append]; ring
  · rw [e6J, e6 _ (by decide), hf5 _ (by decide) (by decide) (by decide), hsz]
    simp [s4, Function.update_of_ne (show rNt ≠ rK by decide)]
  · rw [NSt.set_stk, hs5, e6J, locUpTo_succ I hlt, locSizes_eq_rep]
    show Function.update s3.stk qSzA (List.replicate d lab ++ s3.stk qSzA) = _
    have : s3.stk = s.stk := rfl
    rw [this, hstk]
    funext q
    by_cases hq : q = qSzA
    · subst hq; simp [lab, a, d, v]
    · simp [Function.update_of_ne hq]
  · rw [NSt.set_out, ho5]; exact hout
  · rw [e6J]; omega
  · rw [hp6]; omega

/-- **The location loop of `P4`.** -/
lemma p4LLoop_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (st : NSt CR CQ)
    (hI : p4LInv I st st) (hj : st.env rJ = 0) :
    ∃ st', Good (encodeSystem I) w p4LLoop st st' (400 * (H I + 1) * Ex.nodeCost w) ∧
      st'.pos = posAt I I.numLocations ∧ st'.env rNt = locOff I I.numLocations ∧
      st'.stk = Function.update st.stk qSzA
        (((List.finRange I.numLocations).flatMap (locSizes I)).reverse ++ st.stk qSzA) ∧
      st'.out = st.out := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨s7, r7, hI7, hc7⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rW)) (body := p4LBody) (p4LInv I st)
    (fun s => I.numLocations - s.env rJ) (fun s => H I - s.pos) (150 * Ex.nodeCost w)
    (200 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hW, -, hj, -⟩ := hI
      have := W_le I
      simp only [Ex.Fits, rv, hW]; omega, fun hc => p4LBody_good I hw hH hℓ st s hI hc⟩) st hI
  obtain ⟨hW7, -, hj7, hpos7, hnt7, hstk7, hout7⟩ := hI7
  have hjW : s7.env rJ = I.numLocations := by
    simp only [Ex.eval, rv, hW7] at hc7; split_ifs at hc7 with h <;> omega
  refine ⟨s7, r7.mono ?_, by rw [hpos7, hjW], by rw [hnt7, hjW], by
    rw [hstk7, hjW, locUpTo_all], hout7⟩
  have hW := W_le I
  have hc : condCost w (Ex.lt (rv rJ) (rv rW) : Ex CR) ≤ 4 * Ex.nodeCost w := by
    simp only [condCost, Ex.size, rv]; omega
  rw [hj, Nat.sub_zero]
  have hφ : H I - st.pos ≤ H I := Nat.sub_le _ _
  generalize condCost w (Ex.lt (rv rJ) (rv rW) : Ex CR) = c at *
  generalize Ex.nodeCost w = N at *
  generalize H I - st.pos = φ at *
  generalize H I = h at *
  generalize I.numLocations = W at *
  have h1 : 150 * N * φ ≤ 150 * N * h := Nat.mul_le_mul_left _ hφ
  have h2 : W * (200 * N + c) ≤ h * (204 * N) := Nat.mul_le_mul hW (by omega)
  nlinarith

end Lax119563Proofs.Compiler

end Compiler_P4Loc

/-! ### Formerly `Lax119563Proofs.Compiler.P4LocPass` -/

section Compiler_P4LocPass

/-!
# Pass `P4` (program): the location part of a round

`p4Loc`: `rst`, skip `k, ℓ, W`, `rL1 := rL + 1`, `rNt, r4M, rJ := 0`, the location loop,
skip `E`, `moveAllS qSzA qSzB` (**`p4Loc_good`**: `qSzB := locAll ++ qSzB`,
`rNt = locOff I W = Σ locAll`, cursor at `schPos I`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The class sizes of all locations. -/
noncomputable def locAll : List ℕ := (List.finRange I.numLocations).flatMap (locSizes I)

lemma locAll_sum : (locAll I).sum = locOff I I.numLocations := by
  rw [locAll, ← locUpTo_all]
  suffices h : ∀ j ≤ I.numLocations, (locUpTo I j).sum = locOff I j from h _ le_rfl
  intro j
  induction j with
  | zero => intro _; simp (config := { decide := true }) [locUpTo, locOff_zero]
  | succ j ih =>
    intro hj
    rw [locUpTo_succ I (by omega), List.sum_append, ih (by omega), locOff_succ I (by omega),
      locSize_eq_mul, locSizes_eq_rep, List.sum_replicate, smul_eq_mul]

/-- **The location part of a round.** -/
def p4Loc : CStm CR CQ :=
  .seq .rst (.seq (skipNumS rT) (.seq (skipNumS rT) (.seq (skipNumS rT)
    (.seq (.set rL1 (.add (rv rL) (.const 1))) (.seq (.set rNt (.const 0))
      (.seq (.set r4M (.const 0)) (.seq (.set rJ (.const 0)) (.seq p4LLoop
        (.seq (skipNumS rT) (moveAllS qSzA qSzB rT rP))))))))))

set_option maxHeartbeats 1000000 in
theorem p4Loc_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (st : NSt CR CQ) (hb : st.Bdd w) (hp : st.pos ≤ H I) (hW : st.env rW = I.numLocations)
    (hL : st.env rL = ℓ) (hA : st.stk qSzA = []) :
    ∃ st', Good (encodeSystem I) w p4Loc st st' (800 * (H I + 1) * Ex.nodeCost w) ∧
      st'.stk = Function.update st.stk qSzB (locAll I ++ st.stk qSzB) ∧
      st'.pos = schPos I ∧ st'.out = st.out ∧ st'.env rNt = locOff I I.numLocations ∧
      st'.env r4M = 0 ∧ st'.env rL1 = ℓ + 1 := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have r0 := Good.rst (x := encodeSystem I) (w := w) (st := st)
  set s0 : NSt CR CQ := { st with pos := 0 }
  have r1 := skipNumS_good (Q := CQ) hw (t := rT) s0 k _ (drop_zero_k I)
  set s1 := skipNumFinal s0 rT k
  have r2 := skipNumS_good (Q := CQ) hw (t := rT) s1 ℓ _
    (by show (encodeSystem I).drop (0 + _) = _; rw [zero_add]; exact drop_ell I)
  set s2 := skipNumFinal s1 rT ℓ
  have r3 := skipNumS_good (Q := CQ) hw (t := rT) s2 I.numLocations _
    (by show (encodeSystem I).drop (0 + (encodeNat k).length + (encodeNat ℓ).length) = _
        rw [zero_add]; exact drop_W I)
  set s3 := skipNumFinal s2 rT I.numLocations
  have e3 : ∀ r, r ≠ rT → s3.env r = st.env r := fun r h => by
    rw [skipNumFinal_env_ne h, skipNumFinal_env_ne h, skipNumFinal_env_ne h]
  have r4 := Good.set (x := encodeSystem I) (w := w) (st := s3) (r := rL1)
    (e := .add (rv rL) (.const 1)) (by
      simp only [Ex.Fits, Ex.eval, rv, e3 _ (show rL ≠ rT by decide), hL]; omega)
  set s4 := s3.set rL1 ((Ex.add (rv rL) (.const 1) : Ex CR).eval s3.env)
  have r5 := Good.set (x := encodeSystem I) (w := w) (st := s4) (r := rNt) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s5 := s4.set rNt ((Ex.const 0 : Ex CR).eval s4.env)
  have r6 := Good.set (x := encodeSystem I) (w := w) (st := s5) (r := r4M) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s6 := s5.set r4M ((Ex.const 0 : Ex CR).eval s5.env)
  have r7 := Good.set (x := encodeSystem I) (w := w) (st := s6) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s7 := s6.set rJ ((Ex.const 0 : Ex CR).eval s6.env)
  have e7 : ∀ r, r ≠ rT → r ≠ rL1 → r ≠ rNt → r ≠ r4M → r ≠ rJ → s7.env r = st.env r :=
    fun r h1 h2 h3 h4 h5 => by
      simp only [s7, s6, s5, s4, NSt.set_env, Function.update_of_ne h2, Function.update_of_ne h3,
        Function.update_of_ne h4, Function.update_of_ne h5]
      exact e3 r h1
  have e7L1 : s7.env rL1 = ℓ + 1 := by
    simp (config := { decide := true }) [s7, s6, s5, s4, Ex.eval, rv, e3 _ (show rL ≠ rT by decide), hL]
  have e7N : s7.env rNt = 0 := by simp (config := { decide := true }) [s7, s6, s5, Ex.eval]
  have e7M : s7.env r4M = 0 := by simp (config := { decide := true }) [s7, s6, Ex.eval]
  have e7J : s7.env rJ = 0 := by simp (config := { decide := true }) [s7, Ex.eval]
  have h7p : s7.pos = posAt I 0 := by
    show 0 + (encodeNat k).length + (encodeNat ℓ).length + (encodeNat I.numLocations).length = _
    rw [posAt_zero]; ring
  have hI7 : p4LInv I s7 s7 := by
    refine ⟨by rw [e7 _ (by decide) (by decide) (by decide) (by decide) (by decide), hW],
      e7L1, by rw [e7J]; omega, by rw [e7J, h7p], by rw [e7J, e7N, locOff_zero], ?_, rfl⟩
    rw [e7J]; simp (config := { decide := true }) [locUpTo]
  obtain ⟨s8, r8, h8p, h8N, h8s, h8o⟩ := p4LLoop_good I hw hH hℓ s7 hI7 e7J
  have r9 := skipNumS_good (Q := CQ) hw (t := rT) s8 I.schemas.length _
    (by rw [h8p]; exact drop_posAt_W I)
  set s9 := skipNumFinal s8 rT I.schemas.length
  have r19 := r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9))))))))
  have hb9 := r19.bdd hw hb hp
  obtain ⟨s10, r10, h10s, h10p, h10o, h10e⟩ := moveAllS_good (x := encodeSystem I) hw
    (q := qSzA) (q' := qSzB) (t := rT) (f := rP) (by decide) (by decide) s9 hb9.1
  have e9A : s9.stk qSzA = (locAll I).reverse := by
    show s8.stk qSzA = _; rw [h8s]; simp (config := { decide := true }) [s7, s6, s5, s4, s3, s2, s1, s0, hA, locAll]
  have hlenA : (locAll I).length ≤ 2 * H I := by
    have h1 : (locAll I).length ≤ (locAll I).sum := by
      have : ∀ v ∈ locAll I, 1 ≤ v := by
        intro v hv
        simp only [locAll, List.mem_flatMap, locSizes_eq_rep, List.mem_replicate] at hv
        obtain ⟨_, -, -, rfl⟩ := hv; omega
      calc (locAll I).length = ((locAll I).map fun _ => 1).sum := by simp
        _ ≤ (locAll I).sum := by
          have := List.sum_le_sum (l := locAll I) (f := fun _ => 1) (g := id) this
          simpa using this
    rw [locAll_sum] at h1; have := locOff_le_H I I.numLocations; omega
  have hmono : ∀ j ≤ I.numLocations, posAt I 0 ≤ posAt I j := by
    intro j
    induction j with
    | zero => intro _; exact le_rfl
    | succ j ih => intro hj; rw [posAt_succ I (by omega)]; have := ih (by omega); omega
  have hlen3 : (encodeNat k).length + (encodeNat ℓ).length + (encodeNat I.numLocations).length +
      (encodeNat I.schemas.length).length ≤ H I := by
    have h1 := schAt_le I 0
    rw [schAt_zero, schPos] at h1
    have h3 := hmono _ le_rfl
    rw [posAt_zero] at h3
    omega
  refine ⟨s10, (r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq
    (r9.seq r10)))))))))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e9A, List.length_reverse]
    simp only [Ex.size, rv]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNat k).length = a at *
    generalize (encodeNat ℓ).length = b at *
    generalize (encodeNat I.numLocations).length = c at *
    generalize (encodeNat I.schemas.length).length = d at *
    generalize (locAll I).length = n at *
    generalize st.pos = p at *
    generalize H I = h at *
    nlinarith
  · rw [h10s, e9A, List.reverse_reverse]
    show Function.update (Function.update s8.stk qSzA []) qSzB (locAll I ++ s8.stk qSzB) = _
    rw [h8s]
    funext q
    by_cases h0 : q = qSzB
    · subst h0; simp (config := { decide := true }) [s7, s6, s5, s4, s3, s2, s1, s0]
    by_cases h1 : q = qSzA
    · subst h1; simp (config := { decide := true }) [hA]
    simp (config := { decide := true }) [Function.update_of_ne h0, Function.update_of_ne h1, s7, s6, s5, s4, s3, s2, s1, s0]
  · rw [h10p]; show s8.pos + _ = _; rw [h8p]; rfl
  · rw [h10o]; show s8.out = _; rw [h8o]; rfl
  · rw [h10e _ (by decide) (by decide)]
    show (skipNumFinal s8 rT _).env rNt = _
    rw [skipNumFinal_env_ne (by decide), h8N]
  · rw [h10e _ (by decide) (by decide)]
    show (skipNumFinal s8 rT _).env r4M = _
    rw [skipNumFinal_env_ne (by decide), r8.env_of (by decide), e7M]
  · rw [h10e _ (by decide) (by decide)]
    show (skipNumFinal s8 rT _).env rL1 = _
    rw [skipNumFinal_env_ne (by decide), r8.env_of (by decide), e7L1]

end Lax119563Proofs.Compiler

end Compiler_P4LocPass

/-! ### Formerly `Lax119563Proofs.Compiler.P4SzPush` -/

section Compiler_P4SzPush

/-!
# Pass `P4` (program): the class sizes of one schema

From the arity (`rA`), `|D|` (`rD`), `nEnt` (`rNe`) and `|coefSteps|` (`rNc`), `p4SPush`
pushes `schSizes I e` (in order, so reversed on the stack) on `qSzA`, adding them to `rNt`
(**`p4SPush_good`**, list form `szL`, `schSizes_eq_szL`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Registers of the schema-size scan -/

def rC : Fin CR := 20
def rC2 : Fin CR := 21
def rNe : Fin CR := 22
def rNc : Fin CR := 23
def rTq : Fin CR := 24
def rV4 : Fin CR := 25
def rV2 : Fin CR := 26
def rS : Fin CR := 27
/-- Scratch stack for the schema records (forward). -/
def qT : Fin CQ := 2

/-! ## List form -/

/-- The class sizes of a schema with arity flag `t`, `|D| = d`, `nEnt = nE`, `|coef| = nC`. -/
def szL (t : Bool) (d nE nC : ℕ) : List ℕ :=
  (List.replicate d (jlSizes t)).flatten ++ List.replicate nE 4 ++
    (List.replicate d (if t then [2] else [])).flatten ++ List.replicate nE 2 ++
      List.replicate nC 2

lemma flatMap_const' {α β : Type*} (l : List α) (m : List β) :
    l.flatMap (fun _ => m) = (List.replicate l.length m).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => simp (config := { decide := true }) [ih, List.replicate_succ]

lemma schSizes_eq_szL {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (e : Fin I.schemas.length) :
    schSizes I e = szL (Matrix.isTern (sch I e)) (coordList (dom I e)).length (nEnt I e)
      (coefSteps I e).length := by
  rw [schSizes, szL, flatMap_const', flatMap_const']

lemma rep_pair_rev (a b : ℕ) : ∀ d : ℕ,
    ((List.replicate d [a, b]).flatten).reverse = (List.replicate d [b, a]).flatten
  | 0 => rfl
  | d + 1 => by
    rw [List.replicate_succ', List.flatten_append, List.reverse_append, rep_pair_rev a b d,
      List.replicate_succ]
    simp

lemma rep_two_flatten (d : ℕ) : (List.replicate d [2]).flatten = List.replicate d 2 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [List.replicate_succ, List.flatten_cons, ih]; rfl

lemma rep_nil_flatten (d : ℕ) : (List.replicate d ([] : List ℕ)).flatten = [] := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [List.replicate_succ, List.flatten_cons, ih]; rfl

lemma szL_rev (t : Bool) (d nE nC : ℕ) :
    (szL t d nE nC).reverse =
      List.replicate nC 2 ++ List.replicate nE 2 ++ List.replicate (if t then d else 0) 2 ++
        (List.replicate nE 4 ++
          (if t then (List.replicate d [2, 4]).flatten else List.replicate d 2)) := by
  cases t
  · simp only [szL, jlSizes, Bool.false_eq_true, if_false, rep_two_flatten, rep_nil_flatten,
      List.reverse_append, List.reverse_replicate, List.reverse_nil, List.replicate_zero,
      List.append_assoc, List.nil_append, List.append_nil]
  · simp only [szL, jlSizes, if_true, rep_two_flatten, List.reverse_append,
      List.reverse_replicate, rep_pair_rev, List.append_assoc]

lemma szL_sum (t : Bool) (d nE nC : ℕ) :
    (szL t d nE nC).sum = d * (if t then 6 else 2) + nE * 4 + (if t then d else 0) * 2 +
      nE * 2 + nC * 2 := by
  have h1 : ∀ m : List ℕ, ((List.replicate d m).flatten).sum = d * m.sum := by
    intro m; induction d with
    | zero => simp
    | succ d ih => rw [List.replicate_succ, List.flatten_cons, List.sum_append, ih]; ring
  simp only [szL, List.sum_append, List.sum_replicate, h1, smul_eq_mul, jlSizes]
  cases t <;> simp <;> ring

/-! ## The program -/

/-- Push the class sizes of the current schema. -/
def p4SPush : CStm CR CQ :=
  .seq (.set rTq (.lt (.const 2) (rv rA))) (.seq (.set rV4 (.const 4)) (.seq (.set rV2 (.const 2))
    (.seq (.ite (rv rTq) (rep2PushS qSzA rV4 rV2 rD rK rNt) (repPushS qSzA rV2 rD rK rNt))
    (.seq (repPushS qSzA rV4 rNe rK rNt) (.seq (.set rS (.add (rv rNe) (rv rNc)))
    (.seq (.ite (rv rTq) (.set rS (.add (rv rS) (rv rD))) .skip)
      (repPushS qSzA rV2 rS rK rNt)))))))

lemma p4SPush_arith {N U d nE nC td : ℕ} (hU : U ≤ N) (hU' : 64 ≤ U) (htd : td ≤ d) :
    (1 + 1 + 1) * N + U + (1 * N + U + (1 * N + U + (2 * N + 1 + (d + 1) * (30 * N) +
      ((nE + 1) * (20 * N) + ((1 + 1 + 1) * N + U + (2 * N + 1 + (3 * N + U) +
        (td + nE + nC + 1) * (20 * N))))))) ≤ (2 * d + 2 * nE + nC + 10) * (30 * N) := by
  nlinarith

/-- **The class sizes of one schema.** -/
lemma p4SPush_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) (t : Bool)
    {d nE nC A : ℕ} (hA : s.env rA = if t then 3 else 2) (hD : s.env rD = d)
    (hE : s.env rNe = nE) (hC : s.env rNc = nC) (hN : s.env rNt = A)
    (hw' : A + (szL t d nE nC).sum + 8 < 2 ^ w) :
    ∃ s', Good x w p4SPush s s' ((2 * d + 2 * nE + nC + 10) * (30 * Ex.nodeCost w)) ∧
      s'.stk = Function.update s.stk qSzA ((szL t d nE nC).reverse ++ s.stk qSzA) ∧
      s'.env rNt = A + (szL t d nE nC).sum ∧ s'.pos = s.pos ∧ s'.out = s.out := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hsum := szL_sum t d nE nC
  have hAw : s.env rA < 2 ^ w := by rw [hA]; split_ifs <;> omega
  have r1 := Good.set (x := x) (w := w) (st := s) (r := rTq) (e := .lt (.const 2) (rv rA))
    (by simp only [Ex.Fits, rv]; omega)
  set s1 := s.set rTq ((Ex.lt (.const 2) (rv rA) : Ex CR).eval s.env)
  have r2 := Good.set (x := x) (w := w) (st := s1) (r := rV4) (e := .const 4)
    (by simp only [Ex.Fits]; omega)
  set s2 := s1.set rV4 ((Ex.const 4 : Ex CR).eval s1.env)
  have r3 := Good.set (x := x) (w := w) (st := s2) (r := rV2) (e := .const 2)
    (by simp only [Ex.Fits]; omega)
  set s3 := s2.set rV2 ((Ex.const 2 : Ex CR).eval s2.env)
  have e3 : ∀ r, r ≠ rTq → r ≠ rV4 → r ≠ rV2 → s3.env r = s.env r := fun r h1 h2 h3 => by
    simp (config := { decide := true }) [s3, s2, s1, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3]
  have e3T : s3.env rTq = if t then 1 else 0 := by
    simp (config := { decide := true }) [s3, s2, s1, Ex.eval, rv, hA]; cases t <;> simp
  have e3V4 : s3.env rV4 = 4 := by simp (config := { decide := true }) [s3, s2, Ex.eval]
  have e3V2 : s3.env rV2 = 2 := by simp (config := { decide := true }) [s3, Ex.eval]
  have hTF : (rv rTq : Ex CR).Fits w s3.env := by
    simp only [Ex.Fits, rv, e3T]; split_ifs <;> omega
  -- the junction/link sizes
  obtain ⟨B1, hB1⟩ : ∃ B1, B1 = d * (if t then 6 else 2) := ⟨_, rfl⟩
  obtain ⟨td, htd⟩ : ∃ td, td = if t then d else 0 := ⟨_, rfl⟩
  have hdB1 : d ≤ B1 := by rw [hB1]; cases t <;> simp <;> omega
  have htdd : td ≤ d := by rw [htd]; cases t <;> simp
  have hsum' : (szL t d nE nC).sum = B1 + nE * 4 + td * 2 + nE * 2 + nC * 2 := by
    rw [hsum, hB1, htd]
  clear hsum
  obtain ⟨P1, hP1⟩ : ∃ P1 : List ℕ, P1 = if t then (List.replicate d [2, 4]).flatten
      else List.replicate d 2 := ⟨_, rfl⟩
  have hD3 : s3.env rD = d := by rw [e3 _ (by decide) (by decide) (by decide), hD]
  have hN3 : s3.env rNt = A := by rw [e3 _ (by decide) (by decide) (by decide), hN]
  have hdw : d + 1 < 2 ^ w := by omega
  obtain ⟨s4, r4, e4⟩ : ∃ s4, Good x w (.ite (rv rTq) (rep2PushS qSzA rV4 rV2 rD rK rNt)
      (repPushS qSzA rV2 rD rK rNt)) s3 s4 (2 * Ex.nodeCost w + 1 + (d + 1) * (30 * Ex.nodeCost w)) ∧
      s4 = ((s3.setS qSzA (P1 ++ s3.stk qSzA)).set rNt (A + B1)).set rK d := by
    cases t
    · simp only [Bool.false_eq_true, if_false] at hB1 hP1
      subst hB1 hP1
      have g := repPushS_good (x := x) (w := w) hw (q := qSzA) (v := rV2) (n := rD) (j := rK)
        (acc := rNt) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        s3 e3V2 hD3 hN3 hdw (by omega)
      refine ⟨_, (CStm.Good.iteF hTF (by simp (config := { decide := true }) [rv, Ex.eval, e3T]) g).mono ?_, rfl⟩
      have : (d + 1) * (20 * Ex.nodeCost w) ≤ (d + 1) * (30 * Ex.nodeCost w) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [condCost, rv, Ex.size]; omega
    · simp only [if_true] at hB1 hP1
      subst hB1 hP1
      have g := rep2PushS_good (x := x) (w := w) hw (q := qSzA) (v₁ := rV4) (v₂ := rV2)
        (n := rD) (j := rK) (acc := rNt) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        s3 e3V4 e3V2 hD3 hN3 hdw (by omega)
      refine ⟨_, (CStm.Good.iteT hTF (by simp (config := { decide := true }) [rv, Ex.eval, e3T]) g).mono ?_, rfl⟩
      simp only [condCost, rv, Ex.size]; omega
  have e4r : ∀ r, r ≠ rK → r ≠ rNt → s4.env r = s3.env r := fun r h1 h2 => by
    rw [e4]; simp (config := { decide := true }) [Function.update_of_ne h1, Function.update_of_ne h2]
  -- the entry sizes
  have hE4 : s4.env rNe = nE := by
    rw [e4r _ (by decide) (by decide), e3 _ (by decide) (by decide) (by decide), hE]
  have r5 := repPushS_good (x := x) (w := w) hw (q := qSzA) (v := rV4) (n := rNe) (j := rK)
    (acc := rNt) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    s4 (V := 4) (N := nE) (A := A + B1) (by rw [e4r _ (by decide) (by decide), e3V4]) hE4
    (by rw [e4]; simp (config := { decide := true })) (by omega) (by omega)
  set s5 := ((s4.setS qSzA (List.replicate nE 4 ++ s4.stk qSzA)).set rNt
    (A + B1 + nE * 4)).set rK nE
  have e5r : ∀ r, r ≠ rK → r ≠ rNt → s5.env r = s3.env r := fun r h1 h2 => by
    rw [← e4r r h1 h2]; simp (config := { decide := true }) [s5, Function.update_of_ne h1, Function.update_of_ne h2]
  have e5E : s5.env rNe = nE := by rw [e5r _ (by decide) (by decide), e3 _ (by decide) (by decide) (by decide), hE]
  have e5C : s5.env rNc = nC := by rw [e5r _ (by decide) (by decide), e3 _ (by decide) (by decide) (by decide), hC]
  have r6 := Good.set (x := x) (w := w) (st := s5) (r := rS) (e := .add (rv rNe) (rv rNc))
    (by simp only [Ex.Fits, rv, Ex.eval, e5E, e5C]; refine ⟨?_, ?_, ?_⟩ <;> omega)
  set s6 := s5.set rS ((Ex.add (rv rNe) (rv rNc) : Ex CR).eval s5.env)
  have e6r : ∀ r, r ≠ rS → r ≠ rK → r ≠ rNt → s6.env r = s3.env r := fun r h0 h1 h2 => by
    rw [← e5r r h1 h2]; simp (config := { decide := true }) [s6, Function.update_of_ne h0]
  have e6S : s6.env rS = nE + nC := by simp (config := { decide := true }) [s6, Ex.eval, rv, e5E, e5C]
  obtain ⟨s7, r7, e7S, e7r, e7s, e7p, e7o⟩ : ∃ s7, Good x w (.ite (rv rTq)
      (.set rS (.add (rv rS) (rv rD))) .skip) s6 s7 (2 * Ex.nodeCost w + 1 + (3 * Ex.nodeCost w +
        unitCost w)) ∧
      s7.env rS = td + nE + nC ∧ (∀ r, r ≠ rS → s7.env r = s6.env r) ∧ s7.stk = s6.stk ∧
      s7.pos = s6.pos ∧ s7.out = s6.out := by
    have hTF6 : (rv rTq : Ex CR).Fits w s6.env := by
      simp only [Ex.Fits, rv, e6r _ (show rTq ≠ rS by decide) (by decide) (by decide)]
      exact hTF
    have hT6 : s6.env rTq = if t then 1 else 0 := by
      rw [e6r _ (by decide) (by decide) (by decide), e3T]
    cases t
    · simp only [Bool.false_eq_true, if_false] at htd; subst htd
      refine ⟨s6, (CStm.Good.iteF hTF6 (by simp (config := { decide := true }) [rv, Ex.eval, hT6]) CStm.Good.skip).mono ?_, ?_,
        fun _ _ => rfl, rfl, rfl, rfl⟩
      · simp only [condCost, rv, Ex.size]; omega
      · rw [e6S]; ring
    · simp only [if_true] at htd
      have hD6 : s6.env rD = d := by
        rw [e6r _ (by decide) (by decide) (by decide), e3 _ (by decide) (by decide) (by decide), hD]
      have g := Good.set (x := x) (w := w) (st := s6) (r := rS) (e := .add (rv rS) (rv rD))
        (by simp only [Ex.Fits, rv, Ex.eval, e6S, hD6]; refine ⟨?_, ?_, ?_⟩ <;> omega)
      refine ⟨_, (CStm.Good.iteT hTF6 (by simp (config := { decide := true }) [rv, Ex.eval, hT6]) g).mono ?_, ?_,
        fun r hr => by simp (config := { decide := true }) [Function.update_of_ne hr], rfl, rfl, rfl⟩
      · simp only [condCost, rv, Ex.size]; omega
      · rw [htd]; simp (config := { decide := true }) [Ex.eval, rv, e6S, hD6]; ring
  have hN7 : s7.env rNt = A + B1 + nE * 4 := by
    rw [e7r _ (by decide)]; simp (config := { decide := true }) [s6, s5]
  have r8 := repPushS_good (x := x) (w := w) hw (q := qSzA) (v := rV2) (n := rS) (j := rK)
    (acc := rNt) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    s7 (V := 2) (N := td + nE + nC) (A := A + B1 + nE * 4)
    (by rw [e7r _ (by decide), e6r _ (by decide) (by decide) (by decide), e3V2]) e7S hN7
    (by omega) (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8))))))).mono ?_,
    ?_, ?_, ?_, ?_⟩
  · simp only [Ex.size, rv, condCost]
    exact p4SPush_arith hU hU' htdd
  · simp only [NSt.set_stk, NSt.setS_stk, e7s]
    show Function.update (Function.update s4.stk qSzA (List.replicate nE 4 ++ s4.stk qSzA)) qSzA
      (List.replicate (td + nE + nC) 2 ++ Function.update s4.stk qSzA
        (List.replicate nE 4 ++ s4.stk qSzA) qSzA) = _
    rw [e4]
    simp only [NSt.set_stk, NSt.setS_stk, Function.update_self, Function.update_idem]
    rw [szL_rev, show td + nE + nC = nC + nE + td by ring, List.replicate_add,
      List.replicate_add, ← htd, ← hP1]
    show Function.update s.stk qSzA _ = _
    simp only [List.append_assoc]; rfl
  · simp only [NSt.set_env, Function.update_of_ne (show rNt ≠ rK by decide), Function.update_self]
    rw [hsum']; ring
  · simp only [NSt.set_pos, NSt.setS_pos]; rw [e7p]
    show s4.pos = _; rw [e4]; rfl
  · simp only [NSt.set_out, NSt.setS_out]; rw [e7o]
    show s4.out = _; rw [e4]; rfl

end Lax119563Proofs.Compiler

end Compiler_P4SzPush

/-! ### Formerly `Lax119563Proofs.Compiler.PReqCol` -/

section Compiler_PReqCol

/-!
# Pass `P3`, request generation: one column

`p3Advs` advances the current block of the permutation `π = (f, δ)` to the block `i` of the
column (`qDl2` holds the shifts from the current block on, `qF2` the images after it, `rFi` the
current image; **`p3Advs_good`**); `p3Col` then pushes the request of the column
(**`p3Col_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- Advance by one block. -/
def p3Adv : CStm CR CQ :=
  .seq (moveN qDl2 qJunk rL rI2 rT) (.seq (.pop qF2 rFi) (.set rCur (.add (rv rCur) (.const 1))))

/-- Advance to the block of the column. -/
def p3Advs : CStm CR CQ := .loop (.lt (rv rCur) (rv rGb)) p3Adv

set_option maxHeartbeats 1000000 in
/-- **Advancing the block.** -/
lemma p3Advs_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) {ℓ c i : ℕ}
    (F : List ℕ) (Dl : List (List ℕ)) (hFD : F.length = Dl.length) (hi : i < F.length)
    (hci : c ≤ i) (hDl : ∀ d ∈ Dl, d.length = ℓ ∧ ∀ v ∈ d, v ≤ 1) (hF : ∀ v ∈ F, v < 2 ^ w)
    (hℓw : ℓ + 1 < 2 ^ w) (hiw : i + 1 < 2 ^ w)
    (hC : st.env rCur = c) (hB : st.env rGb = i) (hL : st.env rL = ℓ)
    (hD2 : st.stk qDl2 = (Dl.drop c).flatten) (hF2 : st.stk qF2 = F.drop (c + 1))
    (hFi : st.env rFi = F.getD c 0) :
    ∃ st', Good x w p3Advs st st' ((i - c + 1) * ((ℓ + 3) * (12 * Ex.nodeCost w))) ∧
      st'.env rCur = i ∧ st'.env rFi = F.getD i 0 ∧
      st'.stk qDl2 = (Dl.drop i).flatten ∧ st'.stk qF2 = F.drop (i + 1) ∧
      (∀ q, q ≠ qDl2 → q ≠ qF2 → q ≠ qJunk → st'.stk q = st.stk q) ∧
      st'.pos = st.pos ∧ st'.out = st.out ∧
      ∀ r, wReg r p3Advs = false → st'.env r = st.env r := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set Inv : NSt CR CQ → Prop := fun s => c ≤ s.env rCur ∧ s.env rCur ≤ i ∧ s.env rGb = i ∧
    s.env rL = ℓ ∧ s.stk qDl2 = (Dl.drop (s.env rCur)).flatten ∧
    s.stk qF2 = F.drop (s.env rCur + 1) ∧ s.env rFi = F.getD (s.env rCur) 0 ∧
    (∀ q, q ≠ qDl2 → q ≠ qF2 → q ≠ qJunk → s.stk q = st.stk q) ∧ s.pos = st.pos ∧
    s.out = st.out ∧ ∀ r, wReg r p3Advs = false → s.env r = st.env r with hInv
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv rCur) (rv rGb)) (body := p3Adv)
    Inv (fun s => i - s.env rCur) (fun _ => 0) 0 ((ℓ + 2) * (12 * Ex.nodeCost w)) (by
      intro s ⟨hc1, hc2, hb, hl, hd, hf, hfi, hS, hp, ho, he⟩
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hcond
      have hlt : s.env rCur < i := by simpa [rv, Ex.eval, hb] using hcond
      set m := s.env rCur with hm
      have hmD : m < Dl.length := by omega
      have hdm : Dl.drop m = Dl[m] :: Dl.drop (m + 1) := List.drop_eq_getElem_cons hmD
      have hfm : F.drop (m + 1) = F[m + 1] :: F.drop (m + 2) :=
        List.drop_eq_getElem_cons (by omega)
      obtain ⟨hlm, hbm⟩ := hDl _ (List.getElem_mem hmD)
      obtain ⟨s1, r1, hs1, hf1⟩ := moveN_good (x := x) (w := w) (src := qDl2) (dst := qJunk)
        (cnt := rL) (i := rI2) (t := rT) (by decide) (by decide) (by decide) (by decide) s hl
        (by rw [hd, hdm, List.flatten_cons, List.length_append, hlm]; omega) hℓw (by
          rw [hd, hdm, List.flatten_cons, List.take_append_of_le_length (by omega),
            List.take_of_length_le (by omega)]
          intro v hv; have := hbm v hv
          have : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
          omega)
      have e1F : s1.stk qF2 = F[m + 1] :: F.drop (m + 2) := by
        rw [hs1, movedStk_other _ (by decide) (by decide), hf, hfm]
      have r2 := Good.pop_cons (x := x) (w := w) (r := rFi) e1F
      set s2 := (s1.setS qF2 (F.drop (m + 2))).set rFi F[m + 1]
      have e1 : ∀ r, r ≠ rI2 → r ≠ rT → s1.env r = s.env r := fun r h1 h2 =>
        hf1.2.2 r (by simp [h1, h2])
      have e2C : s2.env rCur = m := by
        simp only [s2, NSt.set_env, NSt.setS_env, Function.update_of_ne (show rCur ≠ rFi by decide)]
        exact e1 _ (by decide) (by decide)
      have r3 := Good.set (x := x) (w := w) (r := rCur) (e := .add (rv rCur) (.const 1)) (st := s2)
        (by simp only [Ex.Fits, Ex.eval, rv, e2C]; omega)
      have hall := r1.seq (r2.seq r3)
      have hev : ∀ r, wReg r p3Adv = false → (s2.set rCur (Ex.eval s2.env
          (.add (rv rCur) (.const 1)))).env r = s.env r := fun r hr => hall.env_of hr
      have e3C : (s2.set rCur (Ex.eval s2.env (.add (rv rCur) (.const 1)))).env rCur = m + 1 := by
        simp [Ex.eval, rv, e2C]
      refine ⟨_, hall.mono ?_, ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega,
        le_rfl⟩
      · simp only [rv, Ex.size]; nlinarith
      · rw [hev _ (by decide), hb]
      · rw [hev _ (by decide), hl]
      · rw [e3C]
        simp only [NSt.set_stk, s2, NSt.setS_stk, Function.update_of_ne (show qDl2 ≠ qF2 by decide)]
        rw [hs1, movedStk_src _ (by decide), hd, hdm, List.flatten_cons,
          List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega)]
        rfl
      · rw [e3C]; simp [s2]
      · rw [e3C]
        simp only [NSt.set_env, s2, NSt.setS_env, Function.update_of_ne (show rFi ≠ rCur by decide),
          Function.update_self]
        rw [List.getD_eq_getElem _ _ (by omega)]
      · intro q n1 n2 n3
        simp only [NSt.set_stk, s2, NSt.setS_stk, Function.update_of_ne n2]
        rw [hs1, movedStk_other _ n1 n3, hS q n1 n2 n3]
      · simp only [NSt.set_pos, s2, NSt.setS_pos]; rw [hf1.1, hp]
      · simp only [NSt.set_out, s2, NSt.setS_out]; rw [hf1.2.1, ho]
      · intro r hr; rw [hev r (by simpa [p3Advs, wReg] using hr), he r hr])
    st ⟨by omega, by omega, hB, hL, by rw [hC, hD2], by rw [hC, hF2], by rw [hC, hFi],
      fun _ _ _ _ => rfl, rfl, rfl, fun _ _ => rfl⟩
  obtain ⟨s', r', ⟨hc1, hc2, hb, -, hd, hf, hfi, hS, hp, ho, he⟩, hc⟩ := hloop
  have hci' : s'.env rCur = i := by
    simp only [Ex.eval, rv, hb] at hc; split_ifs at hc with h <;> omega
  refine ⟨s', r'.mono ?_, hci', by rw [hfi, hci'], by rw [hd, hci'], by rw [hf, hci'], hS, hp, ho,
    he⟩
  rw [hC]
  simp only [condCost, rv, Ex.size, mul_zero, zero_add]
  have : i - c + 1 ≥ 1 := by omega
  nlinarith

/-! ## The stacks of the bit loop -/

section bitsStk
variable (S : Fin CQ → List ℕ) (j : ℕ)
lemma bitsStk_dom2 : bitsStk S j qDom2 = (S qDom2).drop j := by simp [bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide)]
lemma bitsStk_dom : bitsStk S j qDom = ((S qDom2).take j).reverse ++ S qDom := by
  simp [bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide)]
lemma bitsStk_dl2 : bitsStk S j qDl2 = (S qDl2).drop j := by simp [bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide)]
lemma bitsStk_aux : bitsStk S j qAux = ((S qDl2).take j).reverse ++ S qAux := by
  simp [bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide)]
lemma bitsStk_rec : bitsStk S j qRec =
    (xorL ((S qDom2).take j) ((S qDl2).take j)).reverse ++ S qRec := by simp [bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide)]
lemma bitsStk_other {q : Fin CQ} (h1 : q ≠ qDom2) (h2 : q ≠ qDom) (h3 : q ≠ qDl2) (h4 : q ≠ qAux)
    (h5 : q ≠ qRec) : bitsStk S j q = S q := by
  simp [bitsStk, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
    Function.update_of_ne h4, Function.update_of_ne h5]
end bitsStk

/-- One column: push its request. -/
def p3Col : CStm CR CQ :=
  .seq (.pop qDom2 rGb) (.seq (.push qDom (rv rGb)) (.seq p3Advs (.seq (.push qRec (rv rU))
    (.seq (.push qRec (rv rFi)) (.seq p3Bits (.seq (moveN qAux qDl2 rL rI2 rT)
      (.seq (.push qRec (.const 1)) (.seq (.push qRec (rv rSq)) (.seq (.push qRec (.const 0))
        (.seq (.push qRec (.const 0)) (.seq (.set rSq (.add (rv rSq) (rv rStr)))
          (.set rK (.add (rv rK) (.const 1))))))))))))))

lemma Good.push_val {x : List Bool} {w : ℕ} {st : NSt CR CQ} {q : Fin CQ} {e : Ex CR} {v : ℕ}
    (hv : e.eval st.env = v) (h : e.Fits w st.env) :
    Good x w (.push q e : CStm CR CQ) st (st.setS q (v :: st.stk q))
      (e.size * Ex.nodeCost w + unitCost w) := by
  rw [← hv]; exact Good.push h

set_option maxHeartbeats 4000000 in
/-- **One column.** -/
lemma p3Col_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) {ℓ cur i u sq str : ℕ}
    (bs R : List ℕ) (hbs : bs.length = ℓ) (hbsb : ∀ v ∈ bs, v ≤ 1)
    (F : List ℕ) (Dl : List (List ℕ)) (hFD : F.length = Dl.length) (hi : i < F.length)
    (hci : cur ≤ i) (hDl : ∀ d ∈ Dl, d.length = ℓ ∧ ∀ v ∈ d, v ≤ 1) (hF : ∀ v ∈ F, v < 2 ^ w)
    (hℓw : ℓ + 1 < 2 ^ w) (hiw : i + 1 < 2 ^ w) (huw : u < 2 ^ w) (hsw : sq + str < 2 ^ w)
    (hKw : st.env rK + 1 < 2 ^ w)
    (hX2 : st.stk qDom2 = i :: bs ++ R) (hAux : st.stk qAux = [])
    (hC : st.env rCur = cur) (hL : st.env rL = ℓ) (hU : st.env rU = u) (hS : st.env rSq = sq)
    (hT : st.env rStr = str)
    (hD2 : st.stk qDl2 = (Dl.drop cur).flatten) (hF2 : st.stk qF2 = F.drop (cur + 1))
    (hFi : st.env rFi = F.getD cur 0) :
    ∃ st', Good x w p3Col st st' ((i - cur + 1) * ((ℓ + 3) * (12 * Ex.nodeCost w)) +
        (ℓ + 2) * (40 * Ex.nodeCost w)) ∧
      st'.stk qDom2 = R ∧ st'.stk qDom = (i :: bs).reverse ++ st.stk qDom ∧
      st'.stk qDl2 = (Dl.drop i).flatten ∧ st'.stk qF2 = F.drop (i + 1) ∧ st'.stk qAux = [] ∧
      st'.stk qRec = (u :: F.getD i 0 :: xorL bs (Dl.getD i []) ++ [1, sq, 0, 0]).reverse ++
        st.stk qRec ∧
      (∀ q, q ≠ qDom2 → q ≠ qDom → q ≠ qDl2 → q ≠ qF2 → q ≠ qAux → q ≠ qRec → q ≠ qJunk →
        st'.stk q = st.stk q) ∧
      st'.env rCur = i ∧ st'.env rFi = F.getD i 0 ∧ st'.env rSq = sq + str ∧
      st'.env rK = st.env rK + 1 ∧ st'.pos = st.pos ∧ st'.out = st.out ∧
      ∀ r, wReg r p3Col = false → st'.env r = st.env r := by
  have hU0 := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h1w : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hiD : i < Dl.length := by omega
  obtain ⟨hdl, hdb⟩ := hDl _ (List.getElem_mem hiD)
  set d := Dl[i] with hd
  have hdi : Dl.getD i [] = d := List.getD_eq_getElem _ _ hiD
  have hFiw : F.getD i 0 < 2 ^ w := by
    rw [List.getD_eq_getElem _ _ hi]; exact hF _ (List.getElem_mem hi)
  have hdrop : (Dl.drop i).flatten = d ++ (Dl.drop (i + 1)).flatten := by
    rw [List.drop_eq_getElem_cons hiD, List.flatten_cons]
  -- pop the block, save it
  have r1 := Good.pop_cons (x := x) (w := w) (r := rGb) hX2
  set s1 := (st.setS qDom2 (bs ++ R)).set rGb i
  have r2 := Good.push_val (x := x) (w := w) (q := qDom) (e := rv rGb) (st := s1) (v := i)
    (by simp [s1, rv, Ex.eval])
    (by simp only [Ex.Fits, rv, s1, NSt.set_env, Function.update_self]; omega)
  set s2 := s1.setS qDom (i :: s1.stk qDom)
  have e2 : ∀ r, r ≠ rGb → s2.env r = st.env r := fun r h => by
    simp [s2, s1, Function.update_of_ne h]
  -- advance
  obtain ⟨s3, r3, h3C, h3Fi, h3D, h3F, h3S, h3p, h3o, h3e⟩ := p3Advs_good (x := x) hw s2 F Dl
    hFD hi hci hDl hF hℓw hiw (by rw [e2 _ (by decide), hC]) (by simp [s2, s1])
    (by rw [e2 _ (by decide), hL]) (by simp only [s2, s1, NSt.setS_stk, NSt.set_stk, Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qF2 by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qF2 by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qF2 by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qF2 ≠ qDom2 by decide), Function.update_of_ne (show qF2 ≠ qDom by decide), Function.update_of_ne (show qF2 ≠ qDl2 by decide), Function.update_of_ne (show qF2 ≠ qAux by decide), Function.update_of_ne (show qF2 ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qF2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qF2 by decide), Function.update_of_ne (show qRec ≠ qAux by decide)]; exact hD2)
    (by simp only [s2, s1, NSt.setS_stk, NSt.set_stk, Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qF2 by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qF2 by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qF2 by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qF2 ≠ qDom2 by decide), Function.update_of_ne (show qF2 ≠ qDom by decide), Function.update_of_ne (show qF2 ≠ qDl2 by decide), Function.update_of_ne (show qF2 ≠ qAux by decide), Function.update_of_ne (show qF2 ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qF2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qF2 by decide), Function.update_of_ne (show qRec ≠ qAux by decide)]; exact hF2)
    (by rw [e2 _ (by decide), hFi])
  have e3 : ∀ r, r ≠ rGb → wReg r p3Advs = false → s3.env r = st.env r := fun r h h' => by
    rw [h3e r h', e2 r h]
  -- push `u` and `f(i)`
  have r4 := Good.push_val (x := x) (w := w) (q := qRec) (e := rv rU) (st := s3) (v := u)
    (by simp only [rv, Ex.eval]; rw [e3 _ (by decide) (by decide), hU])
    (by simp only [Ex.Fits, rv]; rw [e3 _ (by decide) (by decide), hU]; exact huw)
  set s4 := s3.setS qRec (u :: s3.stk qRec)
  have r5 := Good.push_val (x := x) (w := w) (q := qRec) (e := rv rFi) (st := s4)
    (v := F.getD i 0) (by simp [s4, rv, Ex.eval, h3Fi])
    (by simp only [Ex.Fits, rv, s4, NSt.setS_env, h3Fi]; exact hFiw)
  set s5 := s4.setS qRec (F.getD i 0 :: s4.stk qRec)
  have h5D2 : s5.stk qDom2 = bs ++ R := by
    simp only [s5, s4, NSt.setS_stk, Function.update_of_ne (show qDom2 ≠ qRec by decide)]
    rw [h3S _ (by decide) (by decide) (by decide)]
    simp only [s2, s1, NSt.setS_stk, NSt.set_stk, Function.update_self, Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qF2 by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qF2 by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qF2 by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qF2 ≠ qDom2 by decide), Function.update_of_ne (show qF2 ≠ qDom by decide), Function.update_of_ne (show qF2 ≠ qDl2 by decide), Function.update_of_ne (show qF2 ≠ qAux by decide), Function.update_of_ne (show qF2 ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qF2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qF2 by decide), Function.update_of_ne (show qRec ≠ qAux by decide)]
  have h5Dl : s5.stk qDl2 = d ++ (Dl.drop (i + 1)).flatten := by
    simp only [s5, s4, NSt.setS_stk, Function.update_of_ne (show qDl2 ≠ qRec by decide)]
    rw [h3D, hdrop]
  have h5L : s5.env rL = ℓ := by
    show s3.env rL = ℓ; rw [e3 _ (by decide) (by decide), hL]
  -- the bits
  obtain ⟨s6, r6, h6S, h6p, h6o, h6e⟩ := p3Bits_good (x := x) hw s5 h5L
    (by rw [h5D2]; simp [hbs]) (by rw [h5Dl]; simp [hdl])
    (by rw [h5D2, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        exact hbsb)
    (by rw [h5Dl, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        exact hdb) hℓw
  have htb : (s5.stk qDom2).take ℓ = bs := by
    rw [h5D2, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have htd : (s5.stk qDl2).take ℓ = d := by
    rw [h5Dl, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have h6Aux : s6.stk qAux = d.reverse := by
    rw [h6S, bitsStk_aux, htd]
    simp only [s5, s4, NSt.setS_stk, Function.update_of_ne (show qAux ≠ qRec by decide)]
    rw [h3S _ (by decide) (by decide) (by decide)]
    simp only [s2, s1, NSt.setS_stk, NSt.set_stk, Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qF2 by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qF2 by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qF2 by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qF2 ≠ qDom2 by decide), Function.update_of_ne (show qF2 ≠ qDom by decide), Function.update_of_ne (show qF2 ≠ qDl2 by decide), Function.update_of_ne (show qF2 ≠ qAux by decide), Function.update_of_ne (show qF2 ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qF2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qF2 by decide), Function.update_of_ne (show qRec ≠ qAux by decide)]; rw [hAux]; simp
  have h6L : s6.env rL = ℓ := by rw [h6e _ (by decide), h5L]
  -- restore the shift
  obtain ⟨s7, r7, h7S, h7f⟩ := moveN_good (x := x) (w := w) (src := qAux) (dst := qDl2)
    (cnt := rL) (i := rI2) (t := rT) (by decide) (by decide) (by decide) (by decide) s6 h6L
    (by rw [h6Aux]; simp [hdl]) hℓw (by
      rw [h6Aux, List.take_of_length_le (by simp [hdl])]
      intro v hv; have := hdb v (List.mem_reverse.mp hv); omega)
  have hall7 := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  have hSq7 : s7.env rSq = sq := by rw [hall7.env_of (by decide), hS]
  have hK7 : s7.env rK = st.env rK := hall7.env_of (by decide)
  have hT7 : s7.env rStr = str := by rw [hall7.env_of (by decide), hT]
  have h7C : s7.env rCur = i := by
    rw [h7f.2.2 _ (by decide), h6e _ (by decide)]; exact h3C
  have h7Fi : s7.env rFi = F.getD i 0 := by
    rw [h7f.2.2 _ (by decide), h6e _ (by decide)]; exact h3Fi
  -- the tail of the request
  have r8 := Good.push_val (x := x) (w := w) (q := qRec) (e := .const 1) (st := s7) (v := 1)
    rfl (by simp only [Ex.Fits]; omega)
  set s8 := s7.setS qRec (1 :: s7.stk qRec)
  have r9 := Good.push_val (x := x) (w := w) (q := qRec) (e := rv rSq) (st := s8) (v := sq)
    (by simp [s8, rv, Ex.eval, hSq7]) (by simp only [Ex.Fits, rv, s8, NSt.setS_env, hSq7]; omega)
  set s9 := s8.setS qRec (sq :: s8.stk qRec)
  have r10 := Good.push_val (x := x) (w := w) (q := qRec) (e := .const 0) (st := s9) (v := 0)
    rfl (by simp only [Ex.Fits]; omega)
  set s10 := s9.setS qRec (0 :: s9.stk qRec)
  have r11 := Good.push_val (x := x) (w := w) (q := qRec) (e := .const 0) (st := s10) (v := 0)
    rfl (by simp only [Ex.Fits]; omega)
  set s11 := s10.setS qRec (0 :: s10.stk qRec)
  have r12 := Good.set (x := x) (w := w) (r := rSq) (e := .add (rv rSq) (rv rStr)) (st := s11)
    (by simp only [Ex.Fits, rv, Ex.eval, s11, s10, s9, s8, NSt.setS_env, hSq7, hT7]; omega)
  set s12 := s11.set rSq (Ex.eval s11.env (.add (rv rSq) (rv rStr)))
  have r13 := Good.set (x := x) (w := w) (r := rK) (e := .add (rv rK) (.const 1)) (st := s12)
    (by simp only [Ex.Fits, rv, Ex.eval, s12, s11, s10, s9, s8, NSt.setS_env, NSt.set_env,
          Function.update_of_ne (show rK ≠ rSq by decide), hK7]; omega)
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq
    (r11.seq (r12.seq r13)))))))))))
  have h11 : ∀ q, q ≠ qRec → s11.stk q = s7.stk q := fun q h => by
    simp [s11, s10, s9, s8, Function.update_of_ne h]
  have h7o : ∀ q, q ≠ qAux → q ≠ qDl2 → s7.stk q = s6.stk q := fun q h1 h2 => by
    rw [h7S, movedStk_other _ h1 h2]
  refine ⟨_, hall.mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr => hall.env_of hr⟩
  · simp only [Ex.size, rv]; nlinarith
  · show s11.stk qDom2 = _; rw [h11 _ (by decide), h7o _ (by decide) (by decide), h6S,
      bitsStk_dom2, h5D2, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega)]; rfl
  · show s11.stk qDom = _; rw [h11 _ (by decide), h7o _ (by decide) (by decide), h6S,
      bitsStk_dom, htb]
    simp only [s5, s4, NSt.setS_stk, Function.update_of_ne (show qDom ≠ qRec by decide)]
    rw [h3S _ (by decide) (by decide) (by decide)]; simp [s2, s1, Function.update_of_ne (show qDom ≠ qDom2 by decide)]
  · show s11.stk qDl2 = _; rw [h11 _ (by decide), h7S, movedStk_dst, h6Aux,
      List.take_of_length_le (by simp [hdl]), List.reverse_reverse, h6S, bitsStk_dl2, h5Dl,
      List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), hdrop]; rfl
  · show s11.stk qF2 = _; rw [h11 _ (by decide), h7o _ (by decide) (by decide), h6S,
      bitsStk_other _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s5, s4, NSt.setS_stk, Function.update_of_ne (show qF2 ≠ qRec by decide)]
    exact h3F
  · show s11.stk qAux = _; rw [h11 _ (by decide), h7S, movedStk_src _ (by decide), h6Aux]
    simp [hdl]
  · show s11.stk qRec = _
    simp only [s11, s10, s9, s8, NSt.setS_stk, Function.update_self]
    rw [h7o _ (by decide) (by decide), h6S, bitsStk_rec, htb, htd]
    simp only [s5, s4, NSt.setS_stk, Function.update_self]
    rw [h3S _ (by decide) (by decide) (by decide), hdi]
    simp [s2, s1, Function.update_of_ne (show qRec ≠ qDom2 by decide),
      Function.update_of_ne (show qRec ≠ qDom by decide)]
  · intro q n1 n2 n3 n4 n5 n6 n7
    show s11.stk q = _; rw [h11 _ n6, h7o _ n5 n3, h6S, bitsStk_other _ _ n1 n2 n3 n5 n6]
    simp only [s5, s4, NSt.setS_stk, Function.update_of_ne n6]
    rw [h3S _ n3 n4 n7]; simp [s2, s1, Function.update_of_ne n1, Function.update_of_ne n2]
  · simp [s12, s11, s10, s9, s8, Function.update_of_ne (show rCur ≠ rK by decide),
      Function.update_of_ne (show rCur ≠ rSq by decide), h7C]
  · simp [s12, s11, s10, s9, s8, Function.update_of_ne (show rFi ≠ rK by decide),
      Function.update_of_ne (show rFi ≠ rSq by decide), h7Fi]
  · simp [s12, s11, s10, s9, s8, Function.update_of_ne (show rSq ≠ rK by decide), Ex.eval, rv,
      hSq7, hT7]
  · simp [s12, s11, s10, s9, s8, Function.update_of_ne (show rK ≠ rSq by decide), Ex.eval, rv,
      hK7]
  · simp only [NSt.set_pos, s12, s11, s10, s9, s8, NSt.setS_pos]
    rw [h7f.1, h6p]; simp only [s5, s4, NSt.setS_pos]; rw [h3p]; rfl
  · simp only [NSt.set_out, s12, s11, s10, s9, s8, NSt.setS_out]
    rw [h7f.2.1, h6o]; simp only [s5, s4, NSt.setS_out]; rw [h3o]; rfl

end Lax119563Proofs.Compiler

end Compiler_PReqCol

/-! ### Formerly `Lax119563Proofs.Compiler.PSch` -/

section Compiler_PSch

/-!
# Pass `P2` of the compiler program: the schema pre-scan

`p2` (systems with a schema; run after `p1r`, at the position `posAt I W` of `E`, with
`rKk = k`, `rL = ℓ`, `rL1 = ℓ + 1`) reads `E` and scans the schemas. For schema `e` with
`D = coordList (dom I e)` it reads the arity, skips the locations, scans the coordinates
(counting the rows `rowsSum D`, the block changes, whether block `k - 1` occurs, and the OR of
the block coordinates on the stack `qOr`), pushes the record
`schRec I e = orsL D ++ [blkRows D, nEnt I e, |coefSteps I e|]` onto `qSch`, adds
`schSize I e` to `rLB` and skips the permutations (`p2_good`). At the end `rLB = locBase I`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Registers and stacks -/

def rKm1 : Fin CR := 17
def rK1 : Fin CR := 18
/-- The running sum of the schema sizes (`locBase` at the end). -/
def rLB : Fin CR := 19
def rTern : Fin CR := 20
def rRows : Fin CR := 21
def rCol : Fin CR := 22
def rDist : Fin CR := 23
def rLast : Fin CR := 24
def rPrev : Fin CR := 25
def rBi : Fin CR := 26
def rB : Fin CR := 27
def rO : Fin CR := 28
def rBR : Fin CR := 29
def rNE : Fin CR := 30
def rNC : Fin CR := 31
def rOrp : Fin CR := 32
def rJ2 : Fin CR := 33
/-- `k (ℓ + 1)`, the length of a permutation description. -/
def rPL : Fin CR := 34
def rPN : Fin CR := 35
/-- The OR of the block coordinates and its scratch stack. -/
def qOr : Fin CQ := 2
def qOr2 : Fin CQ := 3
/-- The schema records. -/
def qSch : Fin CQ := 4

open CStm

/-! ## The program -/

/-- One bit of a coordinate. -/
def p2Bit : CStm CR CQ :=
  .seq (rdNumS rB rP rT) (.seq (.pop qOr rO)
    (.seq (.push qOr2 (.lt (.const 0) (.add (rv rO) (rv rB))))
      (.seq (.set rRows (.add (rv rRows) (rv rB))) (.set rI (.add (rv rI) (.const 1))))))

/-- The bit loop. -/
def p2Bits : CStm CR CQ := .loop (.lt (rv rI) (rv rL)) p2Bit

/-- The block of a coordinate. -/
def p2Blk : CStm CR CQ :=
  .seq (.set rDist (.add (rv rDist)
      (.lt (.const 0) (.add (.lt (rv rBi) (rv rPrev)) (.lt (rv rPrev) (rv rBi))))))
    (.seq (.set rPrev (rv rBi))
      (.seq (.ite (.lt (.add (rv rBi) (.const 1)) (rv rKk))
          (.set rRows (.add (rv rRows) (.const 1)))
          (.seq (.set rRows (.add (rv rRows) (rv rKm1))) (.set rLast (.const 1))))
        (.ite (rv rTern) (.set rCol (.add (rv rCol) (.const 8)))
          (.set rCol (.add (rv rCol) (.const 2))))))

/-- One coordinate. -/
def p2Coord : CStm CR CQ :=
  .seq (rdNumS rBi rP rT) (.seq p2Blk (.seq (.set rI (.const 0)) (.seq p2Bits
    (.seq (moveN qOr2 qOr rL rI rO) (.set rK (.add (rv rK) (.const 1)))))))

/-- `6 a + 2 b`. -/
def six2 (a b : Fin CR) : Ex CR :=
  .add (rv a) (.add (rv a) (.add (rv a) (.add (rv a) (.add (rv a) (.add (rv a)
    (.add (rv b) (rv b)))))))

/-- The numbers of a schema. -/
def p2Fin : CStm CR CQ :=
  .seq (.set rOrp (.const 0)) (.seq (mvSumN qOr qSch rL rI rO rOrp)
    (.seq (.ite (rv rLast) (.set rBR (rv rKm1)) (.set rBR (rv rDist)))
      (.seq (.push qSch (rv rBR)) (.seq (.set rBR (.add (rv rBR) (rv rOrp)))
        (.seq (mulS rNE rRows rK1 rJ2) (.seq (mulS rNC rBR rK1 rJ2)
          (.seq (.push qSch (rv rNE)) (.seq (.push qSch (rv rNC))
            (.set rLB (.add (rv rLB) (.add (rv rCol) (six2 rNE rNC))))))))))))

/-- The initialisation of the coordinate scan. -/
def p2Init : CStm CR CQ :=
  .seq (.set rRows (.const 0)) (.seq (.set rCol (.const 0)) (.seq (.set rDist (.const 0))
    (.seq (.set rLast (.const 0)) (.seq (.set rPrev (rv rKk)) (.set rK (.const 0))))))

/-- One schema. -/
def p2Sch : CStm CR CQ :=
  .seq (rdNumS rA rP rT) (.seq (.set rTern (.lt (.const 2) (rv rA)))
    (.seq (skipNumsS rA rI rT) (.seq (rdNumS rD rP rT) (.seq p2Init
      (.seq (pushZS qOr rL rI) (.seq (.loop (.lt (rv rK) (rv rD)) p2Coord)
        (.seq p2Fin (.seq (mulS rPN rPL rA rJ2) (.seq (skipNumsS rPN rI rT)
          (.set rJ (.add (rv rJ) (.const 1))))))))))))

/-- **Pass `P2`.** -/
def p2 : CStm CR CQ :=
  .seq (rdNumS rE rP rT) (.seq (predS rKm1 rKk)
    (.seq (.set rK1 (.add (rv rKk) (.const 1))) (.seq (mulS rPL rKk rL1 rJ2)
      (.seq (.set rLB (.const 0)) (.seq (.set rJ (.const 0))
        (.loop (.lt (rv rJ) (rv rE)) p2Sch))))))

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The record of schema `e`. -/
noncomputable def schRec (e : Fin I.schemas.length) : List ℕ :=
  orsL (coordList (dom I e)) ++ [blkRows (coordList (dom I e)), nEnt I e, (coefSteps I e).length]

/-- The records of the first `j` schemas. -/
noncomputable def schRecsUpTo (j : ℕ) : List ℕ :=
  ((List.finRange I.schemas.length).take j).flatMap (schRec I)

/-! ## The bit loop -/

lemma bor_le (a b : ℕ) : bor a b ≤ 1 := by unfold bor; split_ifs <;> omega

/-- The invariant of the bit loop (bits `bs`, OR bits `ors`, start position `B`, stacks `S0`
with `S0 qOr2 = []`, row count `R0`). -/
def p2BitInv (bs ors : List ℕ) (B R0 : ℕ) (S0 : Fin CQ → List ℕ) (O : List ℕ) (s : NSt CR CQ) :
    Prop :=
  s.env rI ≤ bs.length ∧ s.env rL = bs.length ∧
    s.pos = B + (encodeNats (bs.take (s.env rI))).length ∧
    s.env rRows = R0 + (bs.take (s.env rI)).sum ∧
    s.stk = Function.update (Function.update S0 qOr (ors.drop (s.env rI))) qOr2
      (List.zipWith bor (ors.take (s.env rI)) (bs.take (s.env rI))).reverse ∧ s.out = O

lemma bits_le_one {v w : ℕ} (hv : v ≤ 1) (hw : 2 ≤ w) : (Nat.bits v).length < w := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with rfl | rfl <;> simp <;> omega

set_option maxHeartbeats 800000 in
lemma p2Bit_good {w : ℕ} (hw : 2 ≤ w) (bs ors : List ℕ) (hbs : ∀ b ∈ bs, b ≤ 1)
    (hors : ∀ o ∈ ors, o ≤ 1)
    (hlen : ors.length = bs.length) (B R0 : ℕ) (S0 : Fin CQ → List ℕ) (O : List ℕ)
    (rest : List Bool) (hx : (encodeSystem I).drop B = encodeNats bs ++ rest)
    (hS0 : S0 qOr2 = []) (hR : R0 + bs.sum + 1 < 2 ^ w) (hbw : bs.length + 1 < 2 ^ w)
    (s : NSt CR CQ) (hI : p2BitInv bs ors B R0 S0 O s)
    (hc : (Ex.lt (rv rI) (rv rL)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p2Bit s s'
        (40 * Ex.nodeCost w * ((B + (encodeNats bs).length - s.pos) -
          (B + (encodeNats bs).length - s'.pos)) + 40 * Ex.nodeCost w) ∧
      p2BitInv bs ors B R0 S0 O s' ∧ bs.length - s'.env rI < bs.length - s.env rI ∧
      B + (encodeNats bs).length - s'.pos ≤ B + (encodeNats bs).length - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨hi, hL, hpos, hrows, hstk, hout⟩ := hI
  have hlt : s.env rI < bs.length := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hL]; rw [if_neg h]
  set i := s.env rI with hidef
  have hsplit : bs = bs.take i ++ (bs[i] :: bs.drop (i + 1)) := by
    rw [← List.drop_eq_getElem_cons hlt, List.take_append_drop]
  have hx1 : (encodeSystem I).drop s.pos = encodeNat bs[i] ++
      (encodeNats (bs.drop (i + 1)) ++ rest) := by
    have he : encodeNats bs = encodeNats (bs.take i) ++
        (encodeNat bs[i] ++ encodeNats (bs.drop (i + 1))) := by
      conv_lhs => rw [hsplit]
      rw [encodeNats_append, encNats_cons]
    rw [hpos, drop_add, hx, he, List.append_assoc, List.drop_left, List.append_assoc]
  have hbi : bs[i] ≤ 1 := hbs _ (List.getElem_mem hlt)
  have r1 := rdNumS_good (Q := CQ) hw (r := rB) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s bs[i] _ hx1 (bits_le_one hbi hw)
  set s1 := rdNumFinal s rB rP rT bs[i]
  have e1 : ∀ q, q ≠ rB → q ≠ rP → q ≠ rT → s1.env q = s.env q :=
    fun q h1 h2 h3 => rdNumFinal_env_ne h1 h2 h3 _
  have e1B : s1.env rB = bs[i] := rdNumFinal_env_r (by decide) (by decide) _
  have hilo : i < ors.length := by omega
  have hdo : ors.drop i = ors[i] :: ors.drop (i + 1) := List.drop_eq_getElem_cons hilo
  have hq1 : s1.stk qOr = ors[i] :: ors.drop (i + 1) := by
    simp only [s1, rdNumFinal_stk, hstk, Function.update_of_ne (show qOr ≠ qOr2 by decide),
      Function.update_self, hdo]
  have r2 := Good.pop (x := encodeSystem I) (w := w) (st := s1) qOr rO
  set s2 := (s1.setS qOr (s1.stk qOr).tail).set rO ((s1.stk qOr).headD 0)
  have e2O : s2.env rO = ors[i] := by
    simp only [s2, NSt.set_env, Function.update_self, hq1, List.headD_cons]
  have e2B : s2.env rB = bs[i] := by simp [s2, Function.update_of_ne (show rB ≠ rO by decide), e1B]
  have hoi : ors[i] ≤ 1 := hors _ (List.getElem_mem hilo)
  have r3 := Good.push (x := encodeSystem I) (w := w) (st := s2) (q := qOr2)
    (e := .lt (.const 0) (.add (rv rO) (rv rB))) (by
      have h4 : 4 ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
      simp only [Ex.Fits, Ex.eval, rv, e2O, e2B]; omega)
  set s3 := s2.setS qOr2 ((Ex.lt (.const 0) (.add (rv rO) (rv rB))).eval s2.env :: s2.stk qOr2)
  have e3R : s3.env rRows = R0 + (bs.take i).sum := by
    simp only [s3, s2, NSt.setS_env, NSt.set_env, Function.update_of_ne (show rRows ≠ rO by decide)]
    rw [e1 _ (by decide) (by decide) (by decide), hrows]
  have e3B : s3.env rB = bs[i] := e2B
  have hsum1 : (bs.take (i + 1)).sum = (bs.take i).sum + bs[i] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.sum_append,
      List.sum_singleton]
  have hsumle : (bs.take (i + 1)).sum ≤ bs.sum := by
    conv_rhs => rw [← List.take_append_drop (i + 1) bs]
    rw [List.sum_append]; omega
  have r4 := Good.set (x := encodeSystem I) (w := w) (st := s3) (r := rRows)
    (e := .add (rv rRows) (rv rB)) (by simp only [Ex.Fits, Ex.eval, rv, e3R, e3B]; omega)
  set s4 := s3.set rRows ((Ex.add (rv rRows) (rv rB)).eval s3.env)
  have e4I : s4.env rI = i := by
    simp only [s4, s3, s2, NSt.set_env, NSt.setS_env,
      Function.update_of_ne (show rI ≠ rRows by decide), Function.update_of_ne (show rI ≠ rO by decide)]
    rw [e1 _ (by decide) (by decide) (by decide)]
  have r5 := Good.set (x := encodeSystem I) (w := w) (st := s4) (r := rI)
    (e := .add (rv rI) (.const 1)) (by simp only [Ex.Fits, Ex.eval, rv, e4I]; omega)
  set s5 := s4.set rI ((Ex.add (rv rI) (.const 1)).eval s4.env)
  have e5I : s5.env rI = i + 1 := by simp [s5, Ex.eval, e4I]
  have e5 : ∀ q, q ≠ rI → q ≠ rRows → q ≠ rO → q ≠ rB → q ≠ rP → q ≠ rT →
      s5.env q = s.env q := by
    intro q h1 h2 h3 h4 h5 h6
    simp only [s5, s4, s3, s2, NSt.set_env, NSt.setS_env, Function.update_of_ne h1,
      Function.update_of_ne h2, Function.update_of_ne h3]
    exact e1 q h4 h5 h6
  have e5R : s5.env rRows = R0 + (bs.take (i + 1)).sum := by
    simp only [s5, s4, NSt.set_env, Function.update_of_ne (show rRows ≠ rI by decide),
      Function.update_self, Ex.eval, rv, e3R, e3B, hsum1]; ring
  have hp5 : s5.pos = s.pos + (encodeNat bs[i]).length := rfl
  have hlen1 : (encodeNats (bs.take (i + 1))).length =
      (encodeNats (bs.take i)).length + (encodeNat bs[i]).length := by
    rw [encodeNats_take_succ bs hlt, List.length_append]
  have hle : (encodeNats (bs.take (i + 1))).length ≤ (encodeNats bs).length := by
    conv_rhs => rw [← List.take_append_drop (i + 1) bs]
    rw [encodeNats_append, List.length_append]; omega
  have hev : 1 ≤ (encodeNat bs[i]).length := by rw [length_encodeNat]; omega
  refine ⟨s5, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hp5]
    have hΔ : B + (encodeNats bs).length - s.pos -
        (B + (encodeNats bs).length - (s.pos + (encodeNat bs[i]).length)) =
        (encodeNat bs[i]).length := by omega
    rw [hΔ]
    simp only [Ex.size, rv]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNat bs[i]).length = lv at *
    nlinarith
  · rw [e5I]; omega
  · rw [e5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hL]
  · rw [e5I, hp5, hpos, hlen1]; ring
  · rw [e5I, e5R]
  · show Function.update s2.stk qOr2 _ = _
    have hv : (Ex.lt (.const 0) (.add (rv rO) (rv rB))).eval s2.env = bor ors[i] bs[i] := by
      simp only [Ex.eval, rv, e2O, e2B, bor]
    rw [hv, e5I]
    have hz : List.zipWith bor (ors.take (i + 1)) (bs.take (i + 1)) =
        List.zipWith bor (ors.take i) (bs.take i) ++ [bor ors[i] bs[i]] := by
      rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hilo,
        List.getElem?_eq_getElem hlt, Option.toList_some, Option.toList_some,
        List.zipWith_append (by simp; omega)]
      rfl
    rw [hz, List.reverse_append]
    funext q
    by_cases h1 : q = qOr2
    · subst h1
      simp only [Function.update_self, s2, NSt.set_stk, NSt.setS_stk,
        Function.update_of_ne (show qOr2 ≠ qOr by decide), s1, rdNumFinal_stk, hstk]
      simp
    · by_cases h2 : q = qOr
      · subst h2
        simp only [Function.update_of_ne h1, Function.update_self, s2, NSt.set_stk,
          NSt.setS_stk, hq1, List.tail_cons]
      · simp only [Function.update_of_ne h1, s2, NSt.set_stk, NSt.setS_stk,
          Function.update_of_ne h2, s1, rdNumFinal_stk, hstk]
  · show s.out = O; exact hout
  · rw [e5I]; omega
  · rw [hp5]; omega

/-! ## The block of a coordinate -/

lemma dChg_append : ∀ (p : ℕ) (l : List ℕ) (i : ℕ),
    dChg p (l ++ [i]) = dChg p l + (if i = l.getLastD p then 0 else 1)
  | p, [], i => by simp [dChg]
  | p, a :: l, i => by
    simp only [List.cons_append, dChg, dChg_append a l i, List.getLastD_cons]; ring

set_option maxHeartbeats 800000 in
lemma p2Blk_good {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) {i p R Cl Dt Lt T : ℕ}
    (hi : s.env rBi = i) (hp : s.env rPrev = p) (hR : s.env rRows = R) (hC : s.env rCol = Cl)
    (hD : s.env rDist = Dt) (hL : s.env rLast = Lt) (hK : s.env rKk = k)
    (hKm : s.env rKm1 = k - 1) (hT : s.env rTern = T)
    (hb : k + p + i + R + Cl + Dt + Lt + T + 10 < 2 ^ w) :
    Good (encodeSystem I) w p2Blk s (((((s.set rDist (Dt + if i = p then 0 else 1)).set rPrev i).set
      rRows (R + if i + 1 < k then 1 else k - 1)).set rLast (if i + 1 < k then Lt else 1)).set rCol
      (Cl + if T = 0 then 2 else 8)) (60 * Ex.nodeCost w) := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have r1 := Good.set (x := encodeSystem I) (w := w) (st := s) (r := rDist)
    (e := .add (rv rDist) (.lt (.const 0) (.add (.lt (rv rBi) (rv rPrev)) (.lt (rv rPrev) (rv rBi)))))
    (by
      have h4 : 4 ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
      simp only [Ex.Fits, Ex.eval, rv, hi, hp, hD]; split_ifs <;> omega)
  have ev1 : (Ex.add (rv rDist) (.lt (.const 0) (.add (.lt (rv rBi) (rv rPrev))
      (.lt (rv rPrev) (rv rBi))))).eval s.env = Dt + if i = p then 0 else 1 := by
    simp only [Ex.eval, rv, hi, hp, hD]
    split_ifs <;> omega
  rw [ev1] at r1
  set s1 := s.set rDist (Dt + if i = p then 0 else 1)
  have r2 := Good.set (x := encodeSystem I) (w := w) (st := s1) (r := rPrev) (e := rv rBi)
    (by simp only [Ex.Fits, Ex.eval, rv, s1, NSt.set_env, Function.update_of_ne (show rBi ≠ rDist by decide), hi]; omega)
  have ev2 : (rv rBi : Ex CR).eval s1.env = i := by
    simp only [Ex.eval, rv, s1, NSt.set_env, Function.update_of_ne (show rBi ≠ rDist by decide), hi]
  rw [ev2] at r2
  set s2 := s1.set rPrev i
  have e2 : ∀ q, q ≠ rPrev → q ≠ rDist → s2.env q = s.env q := fun q h1 h2 => by
    simp [s2, s1, Function.update_of_ne h1, Function.update_of_ne h2]
  have e2i : s2.env rBi = i := by rw [e2 _ (by decide) (by decide), hi]
  have e2R : s2.env rRows = R := by rw [e2 _ (by decide) (by decide), hR]
  have e2K : s2.env rKk = k := by rw [e2 _ (by decide) (by decide), hK]
  have e2Km : s2.env rKm1 = k - 1 := by rw [e2 _ (by decide) (by decide), hKm]
  have hc3 : (Ex.lt (.add (rv rBi) (.const 1)) (rv rKk)).Fits w s2.env := by
    simp only [Ex.Fits, Ex.eval, rv, e2i, e2K]; omega
  have r3 : Good (encodeSystem I) w (.ite (.lt (.add (rv rBi) (.const 1)) (rv rKk))
      (.set rRows (.add (rv rRows) (.const 1)))
      (.seq (.set rRows (.add (rv rRows) (rv rKm1))) (.set rLast (.const 1)))) s2
      ((s2.set rRows (R + if i + 1 < k then 1 else k - 1)).set rLast (if i + 1 < k then Lt else 1))
      (condCost w (.lt (.add (rv rBi) (.const 1)) (rv rKk)) + 2 * (4 * Ex.nodeCost w)) := by
    by_cases hik : i + 1 < k
    · refine Good.iteT hc3 (by simp [Ex.eval, rv, e2i, e2K, hik]) ((CStm.Good.set ?_).of_eq ?_ ?_)
      · simp only [Ex.Fits, Ex.eval, rv, e2R]; omega
      · simp only [if_pos hik, Ex.eval, rv, e2R]
        have hL2 : (s2.set rRows (R + 1)).env rLast = Lt := by
          have e2L : s2.env rLast = Lt := by rw [e2 _ (by decide) (by decide), hL]
          simp [Function.update_of_ne (show rLast ≠ rRows by decide), e2L]
        rw [← hL2]; rcases s2 with ⟨e, st, ps, ot⟩; simp [NSt.set]
      · simp only [Ex.size]; omega
    · refine Good.iteF hc3 (by simp [Ex.eval, rv, e2i, e2K, hik]) (((CStm.Good.set ?_).seq
        (Good.set ?_)).of_eq ?_ ?_)
      · simp only [Ex.Fits, Ex.eval, rv, e2R, e2Km]; omega
      · simp [Ex.Fits]; omega
      · simp only [if_neg hik, Ex.eval, rv, e2R, e2Km]
      · simp only [Ex.size]; omega
  set s3 := (s2.set rRows (R + if i + 1 < k then 1 else k - 1)).set rLast (if i + 1 < k then Lt else 1)
  have e2T : s2.env rTern = T := by rw [e2 _ (by decide) (by decide), hT]
  have e2C : s2.env rCol = Cl := by rw [e2 _ (by decide) (by decide), hC]
  have e3T : s3.env rTern = T := by
    simp [s3, Function.update_of_ne (show rTern ≠ rLast by decide),
      Function.update_of_ne (show rTern ≠ rRows by decide), e2T]
  have e3C : s3.env rCol = Cl := by
    simp [s3, Function.update_of_ne (show rCol ≠ rLast by decide),
      Function.update_of_ne (show rCol ≠ rRows by decide), e2C]
  have r4 : Good (encodeSystem I) w (.ite (rv rTern) (.set rCol (.add (rv rCol) (.const 8)))
      (.set rCol (.add (rv rCol) (.const 2)))) s3 (s3.set rCol (Cl + if T = 0 then 2 else 8))
      (condCost w (rv rTern) + 4 * Ex.nodeCost w) := by
    by_cases hT0 : T = 0
    · refine Good.iteF (by simp only [Ex.Fits, Ex.eval, rv, e3T]; omega) (by simp [Ex.eval, rv, e3T, hT0])
        ((CStm.Good.set ?_).of_eq ?_ ?_)
      · simp only [Ex.Fits, Ex.eval, rv, e3C]; omega
      · simp [Ex.eval, rv, e3C, hT0]
      · simp only [Ex.size]; omega
    · refine Good.iteT (by simp only [Ex.Fits, Ex.eval, rv, e3T]; omega) (by simp [Ex.eval, rv, e3T, hT0])
        ((CStm.Good.set ?_).of_eq ?_ ?_)
      · simp only [Ex.Fits, Ex.eval, rv, e3C]; omega
      · simp [Ex.eval, rv, e3C, hT0]
      · simp only [Ex.size]; omega
  refine (r1.seq (r2.seq (r3.seq r4))).mono ?_
  simp only [condCost, Ex.size, rv]
  omega

/-! ## One coordinate -/

/-- The weight of a column in the junction, link and sum sections: `8` or `2`. -/
def colV (tern : Bool) : ℕ := if tern then 8 else 2

lemma dChg_le : ∀ (p : ℕ) (l : List ℕ), dChg p l ≤ l.length
  | _, [] => le_rfl
  | p, i :: l => by
    have := dChg_le i l
    simp only [dChg, List.length_cons]; split_ifs <;> omega

lemma getLastD_le {l : List ℕ} {p m : ℕ} (hp : p ≤ m) (hl : ∀ x ∈ l, x ≤ m) :
    l.getLastD p ≤ m := by
  rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
  · exact hp
  · rw [List.concat_eq_append, List.getLastD_concat]; exact hl b (by simp)

lemma rowsSum_take_le (cs : List (Coord k ℓ)) (r : ℕ) : rowsSum (cs.take r) ≤ rowsSum cs := by
  conv_rhs => rw [← List.take_append_drop r cs]
  simp only [rowsSum, List.map_append, List.sum_append]; omega

lemma rowsSum_take_succ (cs : List (Coord k ℓ)) {r : ℕ} (hr : r < cs.length) :
    rowsSum (cs.take (r + 1)) = rowsSum (cs.take r) + rowsC cs[r] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some, rowsSum,
    List.map_append, List.sum_append]
  simp [rowsSum]

/-- The invariant of the coordinate loop of a schema with coordinates `cs`. -/
def p2CoordInv (cs : List (Coord k ℓ)) (tern : Bool) (B : ℕ) (S0 : Fin CQ → List ℕ)
    (O : List ℕ) (s : NSt CR CQ) : Prop :=
  s.env rK ≤ cs.length ∧ s.env rD = cs.length ∧ s.env rL = ℓ ∧ s.env rKk = k ∧
    s.env rKm1 = k - 1 ∧ s.env rTern = (if tern then 1 else 0) ∧
    s.env rRows = rowsSum (cs.take (s.env rK)) ∧ s.env rCol = s.env rK * colV tern ∧
    s.env rDist = dChg k ((cs.take (s.env rK)).map fun c => (c.1 : ℕ)) ∧
    s.env rPrev = ((cs.take (s.env rK)).map fun c => (c.1 : ℕ)).getLastD k ∧
    s.env rLast = (if ∃ c ∈ cs.take (s.env rK), ¬ (c.1 : ℕ) + 1 < k then 1 else 0) ∧
    s.pos = B + (encodeNats ((cs.take (s.env rK)).flatMap cdesc)).length ∧
    s.stk = Function.update (Function.update S0 qOr (orsL (cs.take (s.env rK)))) qOr2 [] ∧
    s.out = O

lemma blockDescription_le (b : BlockCoord ℓ) : ∀ v ∈ blockDescription b, v ≤ 1 := by
  intro v hv
  simp only [blockDescription, List.mem_map] at hv
  obtain ⟨t, -, rfl⟩ := hv
  have := ZMod.val_lt (b t); omega

lemma orsL_le (cs : List (Coord k ℓ)) : ∀ v ∈ orsL cs, v ≤ 1 := by
  intro v hv
  simp only [orsL, List.mem_map] at hv
  obtain ⟨t, -, rfl⟩ := hv
  split_ifs <;> omega

lemma length_blockDescription (b : BlockCoord ℓ) : (blockDescription b).length = ℓ := by
  simp [blockDescription]

set_option maxHeartbeats 3000000 in
/-- One coordinate. -/
lemma p2Coord_good {w : ℕ} (hw : 2 ≤ w) (cs : List (Coord k ℓ)) (hkH : k ≤ H I)
    (hℓ : ℓ ≤ H I) (hdH : cs.length ≤ H I) (hb : 16 * (H I + 1) + rowsSum cs ≤ 2 ^ w)
    (tern : Bool) (B : ℕ) (S0 : Fin CQ → List ℕ) (O : List ℕ) (rest : List Bool)
    (hx : (encodeSystem I).drop B = encodeNats (cs.flatMap cdesc) ++ rest)
    (s : NSt CR CQ) (hI : p2CoordInv cs tern B S0 O s)
    (hc : (Ex.lt (rv rK) (rv rD)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p2Coord s s'
        (150 * Ex.nodeCost w * ((B + (encodeNats (cs.flatMap cdesc)).length - s.pos) -
          (B + (encodeNats (cs.flatMap cdesc)).length - s'.pos)) + 150 * Ex.nodeCost w) ∧
      p2CoordInv cs tern B S0 O s' ∧ cs.length - s'.env rK < cs.length - s.env rK ∧
      B + (encodeNats (cs.flatMap cdesc)).length - s'.pos ≤
        B + (encodeNats (cs.flatMap cdesc)).length - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨hK, hD, hL, hKk, hKm, hT, hR, hC, hDi, hP, hLa, hpos, hstk, hout⟩ := hI
  have hlt : s.env rK < cs.length := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hD]; rw [if_neg h]
  obtain ⟨r, hrdef⟩ : ∃ r, s.env rK = r := ⟨_, rfl⟩
  rw [hrdef] at hlt hK hR hC hDi hP hLa hpos hstk
  set c := cs[r]
  set bs := blockDescription c.2
  have hbsl : bs.length = ℓ := length_blockDescription _
  have hsplit : cs.flatMap cdesc = (cs.take r).flatMap cdesc ++
      ((c.1 : ℕ) :: bs ++ (cs.drop (r + 1)).flatMap cdesc) := by
    have e := List.take_append_drop r cs
    rw [List.drop_eq_getElem_cons hlt] at e
    conv_lhs => rw [← e]
    rw [List.flatMap_append, List.flatMap_cons]; rfl
  set rest1 := encodeNats ((cs.drop (r + 1)).flatMap cdesc) ++ rest
  have hx1 : (encodeSystem I).drop s.pos = encodeNat (c.1 : ℕ) ++ (encodeNats bs ++ rest1) := by
    rw [hpos, drop_add, hx, hsplit, encodeNats_append, List.append_assoc, List.drop_left,
      List.cons_append, encNats_cons, encodeNats_append, List.append_assoc, List.append_assoc]
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  have hck : (c.1 : ℕ) < k := c.1.2
  -- read the block
  have r1 := rdNumS_good (Q := CQ) hw (r := rBi) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s (c.1 : ℕ) _ hx1 (bits_lt_of_le (by omega) hH2)
  set s1 := rdNumFinal s rBi rP rT (c.1 : ℕ)
  have e1 : ∀ q, q ≠ rBi → q ≠ rP → q ≠ rT → s1.env q = s.env q :=
    fun q h1 h2 h3 => rdNumFinal_env_ne h1 h2 h3 _
  have hRle : rowsSum (cs.take r) ≤ rowsSum cs := rowsSum_take_le cs r
  have hPle : ((cs.take r).map fun c => (c.1 : ℕ)).getLastD k ≤ k :=
    getLastD_le le_rfl (by simp only [List.mem_map]; rintro _ ⟨c', -, rfl⟩; exact c'.1.2.le)
  have hDle : dChg k ((cs.take r).map fun c => (c.1 : ℕ)) ≤ H I :=
    (dChg_le _ _).trans (by simp; omega)
  have hcv : colV tern ≤ 8 := by unfold colV; split_ifs <;> omega
  have hCle : r * colV tern ≤ 8 * H I := by nlinarith
  have hLle : (if ∃ c ∈ cs.take r, ¬ (c.1 : ℕ) + 1 < k then 1 else 0) ≤ 1 := by
    split_ifs <;> omega
  have hTle : (if tern then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have r2 := p2Blk_good I hw s1 (i := (c.1 : ℕ)) (rdNumFinal_env_r (by decide) (by decide) _)
    (by rw [e1 _ (by decide) (by decide) (by decide), hP])
    (by rw [e1 _ (by decide) (by decide) (by decide), hR])
    (by rw [e1 _ (by decide) (by decide) (by decide), hC])
    (by rw [e1 _ (by decide) (by decide) (by decide), hDi])
    (by rw [e1 _ (by decide) (by decide) (by decide), hLa])
    (by rw [e1 _ (by decide) (by decide) (by decide), hKk])
    (by rw [e1 _ (by decide) (by decide) (by decide), hKm])
    (by rw [e1 _ (by decide) (by decide) (by decide), hT])
    (by omega)
  set s2 := ((((s1.set rDist (dChg k ((cs.take r).map fun c => (c.1 : ℕ)) +
      if (c.1 : ℕ) = ((cs.take r).map fun c => (c.1 : ℕ)).getLastD k then 0 else 1)).set rPrev
      (c.1 : ℕ)).set rRows (rowsSum (cs.take r) + if (c.1 : ℕ) + 1 < k then 1 else k - 1)).set
      rLast (if (c.1 : ℕ) + 1 < k then (if ∃ c ∈ cs.take r, ¬ (c.1 : ℕ) + 1 < k then 1 else 0)
        else 1)).set rCol (r * colV tern + if (if tern then 1 else 0) = 0 then 2 else 8)
  have r3 := Good.set (x := encodeSystem I) (w := w) (st := s2) (r := rI) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s3 := s2.set rI ((Ex.const 0 : Ex CR).eval s2.env)
  have e3 : ∀ q, q ≠ rI → q ≠ rCol → q ≠ rLast → q ≠ rRows → q ≠ rPrev → q ≠ rDist →
      s3.env q = s1.env q := by
    intro q h1 h2 h3 h4 h5 h6
    simp [s3, s2, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6]
  have e3L : s3.env rL = ℓ := by
    rw [e3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      e1 _ (by decide) (by decide) (by decide), hL]
  set R0 := rowsSum (cs.take r) + if (c.1 : ℕ) + 1 < k then 1 else k - 1
  have e3R : s3.env rRows = R0 := by
    simp [s3, s2, Function.update_of_ne (show rRows ≠ rI by decide),
      Function.update_of_ne (show rRows ≠ rCol by decide),
      Function.update_of_ne (show rRows ≠ rLast by decide), R0]
  have hrc : rowsSum (cs.take (r + 1)) = R0 + bs.sum := by
    rw [rowsSum_take_succ cs hlt, sum_blockDescription]; simp only [R0, rowsC]; ring
  have hR1 : rowsSum (cs.take (r + 1)) ≤ rowsSum cs := rowsSum_take_le cs (r + 1)
  -- the bits
  set ors := orsL (cs.take r)
  have hs3 : s3.stk = Function.update (Function.update S0 qOr ors) qOr2 [] := by
    show s.stk = _; exact hstk
  have hx3 : (encodeSystem I).drop s3.pos = encodeNats bs ++ rest1 := by
    show (encodeSystem I).drop (s.pos + (encodeNat (c.1 : ℕ)).length) = _
    rw [drop_add, hx1, List.drop_left]
  have h03 : s3.env rI = 0 := by simp [s3, Ex.eval]
  have hI3 : p2BitInv bs ors s3.pos R0 s3.stk s3.out s3 := by
    refine ⟨by rw [h03]; omega, by rw [e3L, hbsl], by rw [h03]; simp [encodeNats],
      by rw [h03, e3R, List.take_zero, List.sum_nil, Nat.add_zero], ?_, rfl⟩
    rw [h03, List.drop_zero, List.take_zero, List.take_zero]
    simp only [List.zipWith_nil_left, List.reverse_nil]
    rw [hs3]
    funext q
    by_cases h1 : q = qOr2
    · subst h1; simp
    · by_cases h2 : q = qOr
      · subst h2; simp [Function.update_of_ne (show qOr ≠ qOr2 by decide)]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  have hors : ors.length = bs.length := by rw [length_orsL, hbsl]
  obtain ⟨s4, r4, hI4, hc4⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rI) (rv rL)) (body := p2Bit) (p2BitInv bs ors s3.pos R0 s3.stk s3.out)
    (fun s => bs.length - s.env rI) (fun s' => s3.pos + (encodeNats bs).length - s'.pos)
    (40 * Ex.nodeCost w) (40 * Ex.nodeCost w) (fun s' hI' => ⟨by
      obtain ⟨hi', hL', -⟩ := hI'
      simp only [Ex.Fits, rv, hL']; omega,
      fun hc' => p2Bit_good I hw bs ors (blockDescription_le _) (orsL_le _) hors s3.pos R0 s3.stk
        s3.out rest1 hx3 (by rw [hs3]; simp) (by rw [← hrc]; omega) (by omega) s' hI' hc'⟩)
    s3 hI3
  obtain ⟨hi4, hL4, hp4, hR4, hs4, ho4⟩ := hI4
  have hi4' : s4.env rI = bs.length := by
    simp only [Ex.eval, rv, hL4] at hc4; split_ifs at hc4 with h <;> omega
  rw [hi4'] at hp4 hR4 hs4
  rw [List.take_of_length_le le_rfl] at hp4 hR4
  rw [List.take_of_length_le (by omega), List.take_of_length_le le_rfl,
    List.drop_of_length_le (by omega)] at hs4
  set z := List.zipWith bor ors bs
  have hzl : z.length = ℓ := by simp [z, hors, hbsl]
  have hz : z = orsL (cs.take (r + 1)) := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, orsL_append]
  -- move the OR back
  obtain ⟨s5, r5, hs5, hf5⟩ := moveN_good (x := encodeSystem I) (w := w) (src := qOr2) (dst := qOr)
    (cnt := rL) (i := rI) (t := rO) (by decide) (by decide) (by decide) (by decide) s4
    (n := ℓ) (by rw [hL4, hbsl])
    (by rw [hs4, Function.update_self, List.length_reverse, hzl])
    (by omega)
    (by
      intro v hv
      rw [hs4, Function.update_self] at hv
      have := List.mem_of_mem_take hv
      rw [List.mem_reverse] at this
      have : v ≤ 1 := by
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp this
        simp only [z, List.getElem_zipWith]; exact bor_le _ _
      omega)
  have e5K : s5.env rK = r := by
    rw [hf5.2.2 _ (by decide), r4.env_of (r := rK) (by decide),
      e3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      e1 _ (by decide) (by decide) (by decide), hrdef]
  have r6 := Good.set (x := encodeSystem I) (w := w) (st := s5) (r := rK)
    (e := .add (rv rK) (.const 1)) (by simp only [Ex.Fits, Ex.eval, rv, e5K]; omega)
  set s6 := s5.set rK ((Ex.add (rv rK) (.const 1)).eval s5.env)
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  have htail := r4.seq (r5.seq r6)
  have e6K : s6.env rK = r + 1 := by simp [s6, Ex.eval, e5K]
  have hp6 : s6.pos = s4.pos := by
    show s5.pos = _; exact hf5.1
  have hlen1 : (encodeNats ((cs.take (r + 1)).flatMap cdesc)).length =
      (encodeNats ((cs.take r).flatMap cdesc)).length + (encodeNat (c.1 : ℕ)).length +
        (encodeNats bs).length := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt]
    simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, encodeNats_append, List.length_append, cdesc, encNats_cons, c, bs]
    ring
  have hle : (encodeNats ((cs.take (r + 1)).flatMap cdesc)).length ≤
      (encodeNats (cs.flatMap cdesc)).length := by
    conv_rhs => rw [← List.take_append_drop (r + 1) cs]
    rw [List.flatMap_append, encodeNats_append, List.length_append]; omega
  have hp4' : s4.pos = s.pos + (encodeNat (c.1 : ℕ)).length + (encodeNats bs).length := by
    rw [hp4]; rfl
  have hbsE : ℓ ≤ (encodeNats bs).length := hbsl ▸ length_le_encodeNats bs
  have hcE : 1 ≤ (encodeNat (c.1 : ℕ)).length := by rw [length_encodeNat]; omega
  refine ⟨s6, hall.mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hp6, hp4']
    have hΔ : B + (encodeNats (cs.flatMap cdesc)).length - s.pos -
        (B + (encodeNats (cs.flatMap cdesc)).length - (s.pos + (encodeNat (c.1 : ℕ)).length +
          (encodeNats bs).length)) = (encodeNat (c.1 : ℕ)).length + (encodeNats bs).length := by
      rw [hpos] at ⊢; omega
    rw [hΔ]
    have hφ3 : s3.pos + (encodeNats bs).length - s3.pos = (encodeNats bs).length := by omega
    have hμ3 : bs.length - s3.env rI = ℓ := by rw [h03, hbsl]; rfl
    rw [hφ3, hμ3]
    simp only [condCost, Ex.size, rv]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNat (c.1 : ℕ)).length = lc at *
    generalize (encodeNats bs).length = lb at *
    nlinarith
  · rw [e6K]; omega
  · rw [hall.env_of (by decide), hD]
  · rw [hall.env_of (by decide), hL]
  · rw [hall.env_of (by decide), hKk]
  · rw [hall.env_of (by decide), hKm]
  · rw [hall.env_of (by decide), hT]
  · rw [e6K, hrc, ← hR4]
    show s5.env rRows = s4.env rRows
    exact hf5.2.2 _ (by decide)
  · rw [e6K, htail.env_of (by decide)]
    cases tern <;> simp [s3, s2, Function.update_of_ne (show rCol ≠ rI by decide), colV] <;> ring
  · rw [e6K, htail.env_of (by decide)]
    simp only [s3, s2, NSt.set_env, Function.update_of_ne (show rDist ≠ rI by decide),
      Function.update_of_ne (show rDist ≠ rCol by decide),
      Function.update_of_ne (show rDist ≠ rLast by decide),
      Function.update_of_ne (show rDist ≠ rRows by decide),
      Function.update_of_ne (show rDist ≠ rPrev by decide), Function.update_self]
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append,
      List.map_singleton, dChg_append]
  · rw [e6K, htail.env_of (by decide)]
    simp only [s3, s2, NSt.set_env, Function.update_of_ne (show rPrev ≠ rI by decide),
      Function.update_of_ne (show rPrev ≠ rCol by decide),
      Function.update_of_ne (show rPrev ≠ rLast by decide),
      Function.update_of_ne (show rPrev ≠ rRows by decide), Function.update_self]
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append,
      List.map_singleton, List.getLastD_concat]
  · rw [e6K, htail.env_of (by decide)]
    simp only [s3, s2, NSt.set_env, Function.update_of_ne (show rLast ≠ rI by decide),
      Function.update_of_ne (show rLast ≠ rCol by decide), Function.update_self]
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some]
    simp only [List.mem_append, List.mem_singleton]
    by_cases h1 : (c.1 : ℕ) + 1 < k
    · rw [if_pos h1]
      by_cases h2 : ∃ c' ∈ cs.take r, ¬ (c'.1 : ℕ) + 1 < k
      · rw [if_pos h2, if_pos (by obtain ⟨c', h, h'⟩ := h2; exact ⟨c', Or.inl h, h'⟩)]
      · rw [if_neg h2, if_neg]
        rintro ⟨c', h | h, h'⟩
        · exact h2 ⟨c', h, h'⟩
        · subst h; exact h' h1
    · rw [if_neg h1, if_pos ⟨c, Or.inr rfl, h1⟩]
  · rw [e6K, hp6, hp4', hpos, hlen1]; ring
  · rw [e6K]
    show s5.stk = _
    rw [hs5, hs4]
    funext q
    unfold movedStk
    by_cases h1 : q = qOr
    · subst h1
      simp only [Function.update_self, Function.update_of_ne (show qOr ≠ qOr2 by decide),
        List.append_nil]
      rw [List.take_of_length_le (by simp [hzl]), List.reverse_reverse, hz]
    · by_cases h2 : q = qOr2
      · subst h2
        simp [Function.update_of_ne (show qOr2 ≠ qOr by decide), hzl]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2, hs3]
  · rw [hall.out_of (by decide), hout]
  · rw [e6K]; omega
  · rw [hp6, hp4']; omega

/-! ## The numbers of a schema -/

set_option maxHeartbeats 3000000 in
lemma p2Fin_good {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) (ors : List ℕ) (hors : s.stk qOr = ors)
    (hlen : ors.length = ℓ) (hle : ∀ o ∈ ors, o ≤ 1) {Lt Dt R Cl LB : ℕ}
    (hL : s.env rL = ℓ) (hKm : s.env rKm1 = k - 1) (hK1 : s.env rK1 = k + 1)
    (hLa : s.env rLast = Lt) (hLt : Lt ≤ 1) (hDi : s.env rDist = Dt) (hR : s.env rRows = R)
    (hC : s.env rCol = Cl) (hLB : s.env rLB = LB)
    (hb : LB + Cl + 6 * (R * (k + 1)) + 2 * (((if Lt ≠ 0 then k - 1 else Dt) + ors.sum) * (k + 1))
      + ℓ + k + Dt + 4 < 2 ^ w) :
    ∃ s', Good (encodeSystem I) w p2Fin s s' ((ℓ + k + 10) * (60 * Ex.nodeCost w)) ∧
      s'.env rLB = LB + Cl + 6 * (R * (k + 1)) +
        2 * (((if Lt ≠ 0 then k - 1 else Dt) + ors.sum) * (k + 1)) ∧
      s'.stk = Function.update (Function.update s.stk qOr []) qSch
        ((((if Lt ≠ 0 then k - 1 else Dt) + ors.sum) * (k + 1)) :: (R * (k + 1)) ::
          (if Lt ≠ 0 then k - 1 else Dt) :: (ors.reverse ++ s.stk qSch)) ∧
      s'.pos = s.pos ∧ s'.out = s.out := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  set BR := if Lt ≠ 0 then k - 1 else Dt
  have hsum : ors.sum ≤ ℓ := by
    have : ors.sum ≤ ors.length * 1 := List.sum_le_card_nsmul ors 1 hle
    omega
  have r1 := Good.set (x := encodeSystem I) (w := w) (st := s) (r := rOrp) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s1 := s.set rOrp ((Ex.const 0 : Ex CR).eval s.env)
  have e1 : ∀ q, q ≠ rOrp → s1.env q = s.env q := fun q h => by
    simp [s1, Function.update_of_ne h]
  obtain ⟨s2, r2, hs2, ha2, hf2⟩ := mvSumN_good (x := encodeSystem I) (w := w) (src := qOr)
    (dst := qSch) (n := rL) (j := rI) (t := rO) (acc := rOrp) hw (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) s1 (N := ℓ)
    (by rw [e1 _ (by decide), hL]) (by simp [s1, hors, hlen])
    (by omega) (by
      simp only [s1, NSt.set_env, Function.update_self, Ex.eval, NSt.set_stk, hors,
        List.take_of_length_le (le_of_eq hlen)]
      omega)
  have e2 : ∀ q, q ≠ rI → q ≠ rO → q ≠ rOrp → s2.env q = s.env q := by
    intro q h1 h2 h3
    rw [hf2.2.2 q (by simp [h1, h2, h3]), e1 q h3]
  have e2O : s2.env rOrp = ors.sum := by
    rw [ha2]; simp [s1, Ex.eval, hors, List.take_of_length_le (le_of_eq hlen)]
  have hstk2 : s2.stk = Function.update (Function.update s.stk qOr []) qSch
      (ors.reverse ++ s.stk qSch) := by
    rw [hs2]
    funext q
    unfold movedStk
    simp only [s1, NSt.set_stk, hors, List.take_of_length_le (le_of_eq hlen),
      List.drop_of_length_le (le_of_eq hlen)]
  -- the block rows
  have r3 : Good (encodeSystem I) w (.ite (rv rLast) (.set rBR (rv rKm1)) (.set rBR (rv rDist)))
      s2 (s2.set rBR BR) (condCost w (rv rLast) + 2 * Ex.nodeCost w) := by
    have hLa2 : s2.env rLast = Lt := by rw [e2 _ (by decide) (by decide) (by decide), hLa]
    by_cases h : Lt ≠ 0
    · refine Good.iteT (by simp only [Ex.Fits, rv, hLa2]; omega)
        (by simp only [Ex.eval, rv, hLa2]; exact h)
        ((CStm.Good.set ?_).of_eq ?_ ?_)
      · simp only [Ex.Fits, rv]; rw [e2 _ (by decide) (by decide) (by decide), hKm]; omega
      · simp only [Ex.eval, rv, BR, if_pos h]; rw [e2 _ (by decide) (by decide) (by decide), hKm]
      · simp only [Ex.size]; omega
    · refine Good.iteF (by simp only [Ex.Fits, rv, hLa2]; omega)
        (by simp only [Ex.eval, rv, hLa2]; omega)
        ((CStm.Good.set ?_).of_eq ?_ ?_)
      · simp only [Ex.Fits, rv]; rw [e2 _ (by decide) (by decide) (by decide), hDi]; omega
      · simp only [Ex.eval, rv, BR, if_neg h]; rw [e2 _ (by decide) (by decide) (by decide), hDi]
      · simp only [Ex.size]; omega
  set s3 := s2.set rBR BR
  have hBR : BR ≤ k + Dt := by simp only [BR]; split_ifs <;> omega
  have r4 := Good.push (x := encodeSystem I) (w := w) (st := s3) (q := qSch) (e := rv rBR)
    (by simp only [Ex.Fits, rv, s3, NSt.set_env, Function.update_self]; omega)
  set s4 := s3.setS qSch ((rv rBR : Ex CR).eval s3.env :: s3.stk qSch)
  have e4 : ∀ q, q ≠ rBR → s4.env q = s2.env q := fun q h => by
    simp [s4, s3, Function.update_of_ne h]
  have e4B : s4.env rBR = BR := by simp [s4, s3]
  have e4O : s4.env rOrp = ors.sum := by rw [e4 _ (by decide), e2O]
  have r5 := Good.set (x := encodeSystem I) (w := w) (st := s4) (r := rBR)
    (e := .add (rv rBR) (rv rOrp)) (by simp only [Ex.Fits, Ex.eval, rv, e4B, e4O]; omega)
  set s5 := s4.set rBR ((Ex.add (rv rBR) (rv rOrp)).eval s4.env)
  have e5 : ∀ q, q ≠ rBR → s5.env q = s2.env q := fun q h => by
    simp only [s5, NSt.set_env, Function.update_of_ne h]; exact e4 q h
  have e5B : s5.env rBR = BR + ors.sum := by simp [s5, Ex.eval, e4B, e4O]
  have e5R : s5.env rRows = R := by
    rw [e5 _ (by decide), e2 _ (by decide) (by decide) (by decide), hR]
  have e5K : s5.env rK1 = k + 1 := by
    rw [e5 _ (by decide), e2 _ (by decide) (by decide) (by decide), hK1]
  have r6 := mulS_good (x := encodeSystem I) (w := w) (Q := CQ) (dst := rNE) (a := rRows)
    (b := rK1) (j := rJ2) hw (by decide) (by decide) (by decide) (by decide) (by decide) s5 e5R
    e5K (by omega) (by omega)
  set s6 := (s5.set rNE (R * (k + 1))).set rJ2 (k + 1)
  have e6 : ∀ q, q ≠ rNE → q ≠ rJ2 → s6.env q = s5.env q := fun q h1 h2 => by
    simp [s6, Function.update_of_ne h1, Function.update_of_ne h2]
  have r7 := mulS_good (x := encodeSystem I) (w := w) (Q := CQ) (dst := rNC) (a := rBR)
    (b := rK1) (j := rJ2) hw (by decide) (by decide) (by decide) (by decide) (by decide) s6
    (by rw [e6 _ (by decide) (by decide), e5B]) (by rw [e6 _ (by decide) (by decide), e5K])
    (by omega) (by omega)
  set s7 := (s6.set rNC ((BR + ors.sum) * (k + 1))).set rJ2 (k + 1)
  have e7 : ∀ q, q ≠ rNC → q ≠ rJ2 → s7.env q = s6.env q := fun q h1 h2 => by
    simp [s7, Function.update_of_ne h1, Function.update_of_ne h2]
  have e7E : s7.env rNE = R * (k + 1) := by
    rw [e7 _ (by decide) (by decide)]; simp [s6, Function.update_of_ne (show rNE ≠ rJ2 by decide)]
  have e7C : s7.env rNC = (BR + ors.sum) * (k + 1) := by
    simp [s7, Function.update_of_ne (show rNC ≠ rJ2 by decide)]
  have r8 := Good.push (x := encodeSystem I) (w := w) (st := s7) (q := qSch) (e := rv rNE)
    (by simp only [Ex.Fits, rv, e7E]; omega)
  set s8 := s7.setS qSch ((rv rNE : Ex CR).eval s7.env :: s7.stk qSch)
  have r9 := Good.push (x := encodeSystem I) (w := w) (st := s8) (q := qSch) (e := rv rNC)
    (by simp only [Ex.Fits, rv, s8, NSt.setS_env, e7C]; omega)
  set s9 := s8.setS qSch ((rv rNC : Ex CR).eval s8.env :: s8.stk qSch)
  have e9 : ∀ q, s9.env q = s7.env q := fun q => rfl
  have e9LB : s9.env rLB = LB := by
    rw [e9, e7 _ (by decide) (by decide), e6 _ (by decide) (by decide), e5 _ (by decide),
      e2 _ (by decide) (by decide) (by decide), hLB]
  have e9C : s9.env rCol = Cl := by
    rw [e9, e7 _ (by decide) (by decide), e6 _ (by decide) (by decide), e5 _ (by decide),
      e2 _ (by decide) (by decide) (by decide), hC]
  have r10 := Good.set (x := encodeSystem I) (w := w) (st := s9) (r := rLB)
    (e := .add (rv rLB) (.add (rv rCol) (six2 rNE rNC))) (by
      simp only [six2, Ex.Fits, Ex.eval, rv, e9LB, e9C, e9, e7E, e7C]; omega)
  set s10 := s9.set rLB ((Ex.add (rv rLB) (.add (rv rCol) (six2 rNE rNC))).eval s9.env)
  refine ⟨s10, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq
    r10))))))))).mono ?_, ?_, ?_, ?_, ?_⟩
  · simp only [condCost, Ex.size, rv, six2]
    nlinarith
  · simp only [s10, NSt.set_env, Function.update_self, six2, Ex.eval, rv, e9LB, e9C, e9, e7E, e7C]
    ring
  · show Function.update s8.stk qSch (s8.env rNC :: s8.stk qSch) = _
    have h8 : s8.stk qSch = R * (k + 1) :: BR :: (ors.reverse ++ s.stk qSch) := by
      show Function.update s7.stk qSch (s7.env rNE :: s7.stk qSch) qSch = _
      rw [Function.update_self, e7E]
      show R * (k + 1) :: Function.update s3.stk qSch (s3.env rBR :: s3.stk qSch) qSch = _
      rw [Function.update_self]
      simp [s3, hstk2]
    have h8' : s8.stk = Function.update s2.stk qSch (R * (k + 1) :: BR :: (ors.reverse ++ s.stk qSch)) := by
      funext q
      by_cases hq : q = qSch
      · subst hq; rw [h8, Function.update_self]
      · show Function.update s7.stk qSch _ q = _
        rw [Function.update_of_ne hq, Function.update_of_ne hq]
        show Function.update s3.stk qSch _ q = _
        rw [Function.update_of_ne hq]; rfl
    rw [h8', show s8.env rNC = (BR + ors.sum) * (k + 1) from e7C, hstk2]
    funext q
    by_cases hq : q = qSch
    · subst hq; simp
    · simp [Function.update_of_ne hq]
  · show s2.pos = s.pos
    rw [hf2.1]; rfl
  · show s2.out = s.out
    rw [hf2.2.1]; rfl

end Lax119563Proofs.Compiler

end Compiler_PSch

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchLab` -/

section Compiler_P4SchLab

/-!
# Pass `P4`, schema part: registers, stacks and the hub label emitters

Registers of the schema part (besides the parsing registers `rT, rP`, the persistent
`rE, rL, rL1, rKk, rLB, r4Eps, r4M` and `r4F, r4V` of `cposS`): `rJ` (schema index),
`r4PL = k (ℓ + 1)`, schema data `r4SB … r4R2`, column loop data `r4Dist … r4K`, column
scratch `rc1 … rc8`. Not written: the registers of `p4Keep` (`rTriv, rW, rL, rE, rKk, rKL = 31, rLB, rNt = 4`), `38`, `39`.
Stacks: `qS2` (schema records, forward), `qA2` (consumed answers), `qOrsF`/`qOrsB` (OR bits
of the schema forward / backup), `qRk`/`qRkF` (rank codes `2 ρ + 1` per column, terminated
by `0`).

Label emitters (one label of a hub, edges pushed with `pE`):
* `jLab a b`: junction label `2a + b` (`junE1`);
* `lLab a`: link label `a` (`lnkE1`);
* `uLab a b`: update label (`updE1`);
* `fLab a b`: update label at the first entry of a column of a binary schema (`updF1`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Registers and stacks -/

def r4PL : Fin CR := 34
def r4SB : Fin CR := 5
def r4Tn : Fin CR := 6
def r4D : Fin CR := 11
def r4BR : Fin CR := 12
def r4R2 : Fin CR := 13
def r4Dist : Fin CR := 17
def r4Prev : Fin CR := 18
def r4H : Fin CR := 20
def r4SP : Fin CR := 23
def r4TP : Fin CR := 24
def r4K : Fin CR := 25
def rc1 : Fin CR := 26
def rc2 : Fin CR := 27
def rc3 : Fin CR := 28
def rc4 : Fin CR := 29
def rc5 : Fin CR := 30
def rc6 : Fin CR := 37
def rc7 : Fin CR := 32
def rc8 : Fin CR := 33

def qS2 : Fin CQ := 2
def qA2 : Fin CQ := 3
def qOrsF : Fin CQ := 5
def qOrsB : Fin CQ := 6
def qRk : Fin CQ := 7
def qRkF : Fin CQ := 8

/-- The hub position `r4H + i`. -/
def hE (i : ℕ) : Ex CR := .add (rv r4H) (.const i)

/-! ## Sorting two optional positions -/

/-- Push the present ones of two optional positions (flag `rc7`, value `rc8`; flag `r4F`,
value `r4V`), sorted. -/
def srt2 (h : Ex CR) : CStm CR CQ :=
  .ite (rv rc7)
    (.ite (rv r4F)
      (.ite (.lt (rv r4V) (rv rc8)) (.seq (pE h (rv r4V)) (pE h (rv rc8)))
        (.seq (pE h (rv rc8)) (pE h (rv r4V))))
      (pE h (rv rc8)))
    (pEo h r4F r4V)

lemma flag_fits {w : ℕ} (hw : 2 ≤ w) {env : Fin CR → ℕ} {f : Fin CR} {o : Option ℕ}
    (h : env f = if o.isSome then 1 else 0) : (rv f : Ex CR).Fits w env := by
  have : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  simp only [rv, Ex.Fits, h]; split_ifs <;> omega

lemma srt2_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (h : Ex CR) (s : NSt CR CQ)
    (o₁ o₂ : Option ℕ) (h1 : s.env rc7 = if o₁.isSome then 1 else 0)
    (h1v : ∀ a, o₁ = some a → s.env rc8 = a) (h2 : s.env r4F = if o₂.isSome then 1 else 0)
    (h2v : ∀ a, o₂ = some a → s.env r4V = a) (hv1 : s.env rc8 < 2 ^ w)
    (hv2 : s.env r4V < 2 ^ w) (hh : h.Fits w s.env) (hhr : ∀ env : Fin CR → ℕ,
      (∀ r, r ≠ r4M → env r = s.env r) → h.eval env = h.eval s.env ∧ h.Fits w env)
    (hm : s.env r4M + 2 < 2 ^ w) :
    ∃ s', Good x w (srt2 h) s s' ((2 * h.size + 30) * Ex.nodeCost w) ∧
      EdgeEff s s' ((sort2 o₁ o₂).map fun v => (h.eval s.env, v)) ∧
      ∀ r, r ≠ r4M → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hF1 := flag_fits hw h1
  have hF2 := flag_fits hw h2
  have hv1' : (rv rc8 : Ex CR).Fits w s.env := hv1
  have hv2' : (rv r4V : Ex CR).Fits w s.env := hv2
  cases o₁ with
  | none =>
    obtain ⟨s', g, eff, fr⟩ := pEo_good (x := x) hw h r4F r4V (by decide) s o₂ h2 h2v hh hv2
      (by omega)
    refine ⟨s', (Good.iteF hF1 (by simp [rv, Ex.eval, h1]) g).mono ?_, ?_, fr⟩
    · simp only [condCost, rv, Ex.size]; nlinarith
    · cases o₂ <;> simpa [sort2] using eff
  | some a =>
    have ha := h1v a rfl
    cases o₂ with
    | none =>
      obtain ⟨s', g, eff, fr⟩ := pE_good (x := x) (w := w) h (rv rc8) s hh hv1' (by omega)
      refine ⟨s', (Good.iteT hF1 (by simp [rv, Ex.eval, h1])
        (Good.iteF hF2 (by simp [rv, Ex.eval, h2]) g)).mono ?_, ?_, fr⟩
      · simp only [condCost, rv, Ex.size]; nlinarith
      · simpa [sort2, rv, Ex.eval, ha] using eff
    | some b =>
      have hb := h2v b rfl
      have hF3 : (Ex.lt (rv r4V) (rv rc8) : Ex CR).Fits w s.env := ⟨hv2', hv1'⟩
      by_cases hab : a ≤ b
      · obtain ⟨s1, g1, eff1, fr1⟩ := pE_good (x := x) (w := w) h (rv rc8) s hh hv1' (by omega)
        have e1 := hhr s1.env fr1
        obtain ⟨s2, g2, eff2, fr2⟩ := pE_good (x := x) (w := w) h (rv r4V) s1 e1.2
          (by simpa [rv, Ex.Fits, fr1 r4V (by decide)] using hv2)
          (by rw [eff1.2.1]; simp; omega)
        refine ⟨s2, (Good.iteT hF1 (by simp [rv, Ex.eval, h1])
          (Good.iteT hF2 (by simp [rv, Ex.eval, h2])
            (Good.iteF hF3 (by simp [rv, Ex.eval, ha, hb]; omega) (g1.seq g2)))).mono ?_,
          ?_, fun r hr => (fr2 r hr).trans (fr1 r hr)⟩
        · simp only [condCost, rv, Ex.size]; nlinarith
        · have := eff1.trans eff2
          simpa [sort2, hab, rv, Ex.eval, ha, hb, e1.1, fr1 r4V (by decide)] using this
      · obtain ⟨s1, g1, eff1, fr1⟩ := pE_good (x := x) (w := w) h (rv r4V) s hh hv2' (by omega)
        have e1 := hhr s1.env fr1
        obtain ⟨s2, g2, eff2, fr2⟩ := pE_good (x := x) (w := w) h (rv rc8) s1 e1.2
          (by simpa [rv, Ex.Fits, fr1 rc8 (by decide)] using hv1)
          (by rw [eff1.2.1]; simp; omega)
        refine ⟨s2, (Good.iteT hF1 (by simp [rv, Ex.eval, h1])
          (Good.iteT hF2 (by simp [rv, Ex.eval, h2])
            (Good.iteT hF3 (by simp [rv, Ex.eval, ha, hb]; omega) (g1.seq g2)))).mono ?_,
          ?_, fun r hr => (fr2 r hr).trans (fr1 r hr)⟩
        · simp only [condCost, rv, Ex.size]; nlinarith
        · have := eff1.trans eff2
          simpa [sort2, hab, rv, Ex.eval, ha, hb, e1.1, fr1 rc8 (by decide)] using this


lemma hE_eval (i : ℕ) (env : Fin CR → ℕ) : (hE i).eval env = env r4H + i := rfl

lemma hE_stable {w : ℕ} (i : ℕ) (s : NSt CR CQ) (hh : s.env r4H + i < 2 ^ w) :
    ∀ env : Fin CR → ℕ, (∀ r, r ≠ r4M → env r = s.env r) →
      (hE i).eval env = (hE i).eval s.env ∧ (hE i).Fits w env := by
  intro env he
  have := he r4H (by decide)
  refine ⟨by simp [hE_eval, this], ?_⟩
  simp only [hE, rv, Ex.Fits, Ex.eval, this]; omega

/-! ## Junction labels -/

/-- The junction label `2a + b`: answers `U` in `rc2, rc3` (offset, mode), `V` in `rc4, rc5`. -/
def jLab (a b : ℕ) : CStm CR CQ :=
  .seq (pE (hE (2 * a + b)) (.add (rv r4SP) (.const ((a + b) % 2))))
    (.seq (.set rc6 (.const a)) (.seq (cposS rLB rc2 rc3 rc6)
      (.seq (.set rc7 (rv r4F)) (.seq (.set rc8 (rv r4V))
        (.seq (.set rc6 (.const b)) (.seq (cposS rLB rc4 rc5 rc6) (srt2 (hE (2 * a + b)))))))))

/-- Registers written by the label emitters. -/
def labW : List (Fin CR) := [rc6, rc7, rc8, r4F, r4V, r4M]

set_option maxHeartbeats 1000000 in
lemma jLab_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1)
    (s : NSt CR CQ) {H SP LB oU mU oV mV : ℕ} (eH : s.env r4H = H) (eSP : s.env r4SP = SP)
    (eLB : s.env rLB = LB) (eoU : s.env rc2 = oU) (emU : s.env rc3 = mU) (eoV : s.env rc4 = oV)
    (emV : s.env rc5 = mV) (hmU : mU ≤ 2) (hmV : mV ≤ 2) (hH : H + 4 < 2 ^ w)
    (hSP : SP + 2 < 2 ^ w) (hU : LB + oU + 2 < 2 ^ w) (hV : LB + oV + 2 < 2 ^ w)
    (hV4 : s.env r4V < 2 ^ w) (hm : s.env r4M + 3 < 2 ^ w) :
    ∃ s', Good x w (jLab a b) s s' (100 * Ex.nodeCost w) ∧
      EdgeEff s s' (junE1 (H + (2 * a + b)) SP (cposN LB oU mU a) (cposN LB oV mV b) a b) ∧
      s'.env r4V < 2 ^ w ∧ ∀ r, r ∉ labW → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  set i := 2 * a + b with hi
  have hi3 : i ≤ 3 := by omega
  -- the sum edge
  obtain ⟨s1, g1, eff1, fr1⟩ := pE_good (x := x) (w := w) (hE i) (.add (rv r4SP) (.const ((a + b) % 2)))
    s (by simp only [hE, rv, Ex.Fits, Ex.eval, eH]; omega)
    (by simp only [rv, Ex.Fits, Ex.eval, eSP]; omega) (by omega)
  -- the first coordinate
  have g2 := Good.set (x := x) (w := w) (st := s1) (r := rc6) (e := .const a)
    (by simp only [Ex.Fits]; omega)
  set s2 := s1.set rc6 ((Ex.const a : Ex CR).eval s1.env)
  have e2 : ∀ r, r ≠ rc6 → r ≠ r4M → s2.env r = s.env r := fun r h1 h2 => by
    simp only [s2, NSt.set_env, Function.update_of_ne h1]; exact fr1 r h2
  have e26 : s2.env rc6 = a := by simp +decide [s2, Ex.eval]
  obtain ⟨s3, g3, f3, v3, hv3, k3, p3, o3, fr3⟩ := cposS_good (x := x) hw (lb := rLB) (off := rc2)
    (md := rc3) (a := rc6) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s2
    (by rw [e2 _ (by decide) (by decide), emU]; exact hmU) (by rw [e26]; exact ha)
    (by rw [e2 _ (by decide) (by decide), e2 _ (by decide) (by decide), eLB, eoU]; omega)
    (by rw [e2 _ (by decide) (by decide)]; exact hV4)
  rw [e2 _ (by decide) (by decide), e2 _ (by decide) (by decide), e2 _ (by decide) (by decide),
    e26, eLB, eoU, emU] at f3 v3
  have g4 := Good.set (x := x) (w := w) (st := s3) (r := rc7) (e := rv r4F)
    (by simp only [rv, Ex.Fits, f3]; split_ifs <;> omega)
  set s4 := s3.set rc7 ((rv r4F : Ex CR).eval s3.env)
  have g5 := Good.set (x := x) (w := w) (st := s4) (r := rc8) (e := rv r4V)
    (by simp only [s4, rv, Ex.Fits, NSt.set_env, Function.update_of_ne (show r4V ≠ rc7 by decide)]
        exact hv3)
  set s5 := s4.set rc8 ((rv r4V : Ex CR).eval s4.env)
  have g6 := Good.set (x := x) (w := w) (st := s5) (r := rc6) (e := .const b)
    (by simp only [Ex.Fits]; omega)
  set s6 := s5.set rc6 ((Ex.const b : Ex CR).eval s5.env)
  have e6 : ∀ r, r ≠ rc6 → r ≠ rc7 → r ≠ rc8 → r ≠ r4F → r ≠ r4V → r ≠ r4M →
      s6.env r = s.env r := fun r h1 h2 h3 h4 h5 h6 => by
    simp only [s6, s5, s4, NSt.set_env, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3]
    rw [fr3 r h4 h5]; exact e2 r h1 h6
  have e66 : s6.env rc6 = b := by simp +decide [s6, Ex.eval]
  have e67 : s6.env rc7 = if (cposN LB oU mU a).isSome then 1 else 0 := by
    simp +decide [s6, s5, s4, Ex.eval, rv, f3]
  have e68 : ∀ v, cposN LB oU mU a = some v → s6.env rc8 = v := by
    intro v hv; simp +decide [s6, s5, s4, Ex.eval, rv, v3 v hv]
  have e68' : s6.env rc8 < 2 ^ w := by simp +decide [s6, s5, s4, Ex.eval, rv]; exact hv3
  obtain ⟨s7, g7, f7, v7, hv7, k7, p7, o7, fr7⟩ := cposS_good (x := x) hw (lb := rLB) (off := rc4)
    (md := rc5) (a := rc6) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s6
    (by rw [e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), emV]
        exact hmV) (by rw [e66]; exact hb)
    (by rw [e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), eLB, eoV]
        omega)
    (by simp +decide [s6, s5, s4, Ex.eval, rv]; exact hv3)
  rw [e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    e66, eLB, eoV, emV] at f7 v7
  have e7H : s7.env r4H = H := by
    rw [fr7 _ (by decide) (by decide),
      e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), eH]
  have e7M : s7.env r4M = s.env r4M + 1 := by
    rw [fr7 _ (by decide) (by decide)]
    simp only [s6, s5, s4, NSt.set_env, Function.update_of_ne (show r4M ≠ rc6 by decide),
      Function.update_of_ne (show r4M ≠ rc7 by decide),
      Function.update_of_ne (show r4M ≠ rc8 by decide)]
    rw [fr3 _ (by decide) (by decide)]
    simp only [s2, NSt.set_env, Function.update_of_ne (show r4M ≠ rc6 by decide), eff1.2.1]
    simp
  obtain ⟨s8, g8, eff8, fr8⟩ := srt2_good (x := x) hw (hE i) s7 _ _
    (by rw [fr7 _ (by decide) (by decide)]; exact e67)
    (fun v hv => by rw [fr7 _ (by decide) (by decide)]; exact e68 v hv) f7 v7
    (by rw [fr7 _ (by decide) (by decide)]; exact e68') hv7
    (by simp only [hE, rv, Ex.Fits, Ex.eval, e7H]; omega)
    (hE_stable i s7 (by rw [e7H]; omega)) (by rw [e7M]; omega)
  refine ⟨s8, (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq (g7.seq g8))))))).mono ?_,
    ?_, ?_, ?_⟩
  · simp only [hE, rv, Ex.size]; nlinarith
  · have eff17 : EdgeEff s1 s7 [] := by
      refine EdgeEff.of_frame ?_ ?_ ?_ ?_
      · rw [k7]; simp +decide [s6, s5, s4, k3, s2]
      · rw [fr7 _ (by decide) (by decide)]
        simp only [s6, s5, s4, NSt.set_env, Function.update_of_ne (show r4M ≠ rc6 by decide),
          Function.update_of_ne (show r4M ≠ rc7 by decide),
          Function.update_of_ne (show r4M ≠ rc8 by decide)]
        rw [fr3 _ (by decide) (by decide)]
        simp +decide [s2]
      · rw [p7]; simp +decide [s6, s5, s4, p3, s2]
      · rw [o7]; simp +decide [s6, s5, s4, o3, s2]
    have := (eff1.trans eff17).trans eff8
    simpa [junE1, hE_eval, e7H, eH, eSP, rv, Ex.eval] using this
  · rw [fr8 _ (by decide)]; exact hv7
  · intro r hr
    simp only [labW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [fr8 r hr.2.2.2.2.2, fr7 r hr.2.2.2.1 hr.2.2.2.2.1]
    exact e6 r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2

end Lax119563Proofs.Compiler

end Compiler_P4SchLab

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchK` -/

section Compiler_P4SchK

/-!
# Pass `P4`, schema part: skipping the location section

`p4KLoop` skips the descriptions of all locations (per location: `ι`, `|D|`, the coordinates)
(**`p4KLoop_good`**: from `posAt I 0` with `rJ = 0` to `posAt I W`, writing only
`rT, rP, r4D, rc2, rc3, rJ`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- Skip the description of one location. -/
def p4KBody : CStm CR CQ :=
  .seq (skipNumS rT) (.seq (rdNumS r4D rP rT) (.seq (skipBlocksS r4D rL1 rc2 rc3 rT)
    (.set rJ (.add (rv rJ) (.const 1)))))

/-- Skip the location section. -/
def p4KLoop : CStm CR CQ := .loop (.lt (rv rJ) (rv rW)) p4KBody

/-- Registers written by `p4KLoop`. -/
def kW : List (Fin CR) := [rT, rP, r4D, rc2, rc3, rJ]

/-- The loop invariant. -/
def p4KInv (st s : NSt CR CQ) : Prop :=
  s.env rW = I.numLocations ∧ s.env rL1 = ℓ + 1 ∧
    s.env rJ ≤ I.numLocations ∧ s.pos = posAt I (s.env rJ) ∧ s.stk = st.stk ∧
    s.out = st.out ∧ ∀ r, r ∉ kW → s.env r = st.env r

lemma p4KBody_arith {N U la ld lf d : ℕ} (hU : U ≤ N) (hU' : 64 ≤ U) (hdf : N * d ≤ N * lf) :
    (la + 1) * (4 * N) + ((ld + 1) * (20 * N) + ((lf + d + 1) * (50 * N) +
      ((1 + 1 + 1) * N + U))) ≤ 150 * N * (la + ld + lf) + 200 * N := by
  nlinarith

lemma p4KBody_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (st s : NSt CR CQ) (hI : p4KInv I st s) (hc : (Ex.lt (rv rJ) (rv rW)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p4KBody s s'
        (150 * Ex.nodeCost w * ((H I - s.pos) - (H I - s'.pos)) + 200 * Ex.nodeCost w) ∧
      p4KInv I st s' ∧ I.numLocations - s'.env rJ < I.numLocations - s.env rJ ∧
      H I - s'.pos ≤ H I - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  obtain ⟨hW, hL1, hjW, hpos, hstk, hout, hfr⟩ := hI
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
  have hd : (Nat.bits d).length < w := bits_lt_of_le hdH hH2
  -- skipping `ι(v)`, reading `|D_v|`
  have r1 := skipNumS_good (Q := CQ) hw (t := rT) s a _ hx
  set s1 := skipNumFinal s rT a
  have hx2 : (encodeSystem I).drop s1.pos = encodeNat d ++ (encodeNats bs.flatten ++ rest) := by
    simp only [s1, skipNumFinal]
    rw [← List.drop_drop, hx, List.drop_left]
  have r2 := rdNumS_good (Q := CQ) hw (r := r4D) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s1 d _ hx2 hd
  set s2 := rdNumFinal s1 r4D rP rT d
  have e2 : ∀ q, q ≠ r4D → q ≠ rP → q ≠ rT → s2.env q = s.env q := by
    intro q h1 h3 h4
    rw [rdNumFinal_env_ne h1 h3 h4, skipNumFinal_env_ne h4]
  have e2D : s2.env r4D = d := rdNumFinal_env_r (by decide) (by decide) d
  -- skipping the coordinates
  have hx4 : (encodeSystem I).drop s2.pos = encodeNats bs.flatten ++ rest := by
    simp only [s2, rdNumFinal_pos]
    rw [← List.drop_drop, hx2, List.drop_left]
  obtain ⟨s5, r5, hs5, hp5, ho5, hf5⟩ := skipBlocksS_good (Q := CQ) hw (d := r4D) (m := rL1)
    (j := rc2) (i := rc3) (t := rT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s2 bs (ℓ + 1) hbsM rest hx4
    (by rw [hbsl, e2D])
    (by rw [e2 rL1 (by decide) (by decide) (by decide), hL1])
    (by rw [hbsl]; omega) (by omega)
  have e5J : s5.env rJ = j := by
    rw [hf5 _ (by decide) (by decide) (by decide), e2 _ (by decide) (by decide) (by decide)]
  have r6 := Good.set (x := encodeSystem I) (w := w) (r := rJ) (e := .add (rv rJ) (.const 1))
    (st := s5) (by
      have := W_le I
      simp only [Ex.Fits, Ex.eval, rv, e5J]; omega)
  set s6 := s5.set rJ (Ex.eval s5.env (.add (rv rJ) (.const 1)))
  have e6 : ∀ q, q ≠ rJ → s6.env q = s5.env q := fun q hq => by
    simp [s6, Function.update_of_ne hq]
  have e6J : s6.env rJ = j + 1 := by simp [s6, Ex.eval, rv, e5J]
  have back : ∀ q, q ∉ kW → s6.env q = s.env q := by
    intro q hq
    simp only [kW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    rw [e6 q h6, hf5 q h4 h5 h1, e2 q h3 h2 h1]
  have hp6 : s6.pos = s.pos + (encodeNat a).length + (encodeNat d).length +
      (encodeNats bs.flatten).length := by
    rw [NSt.set_pos, hp5]; rfl
  refine ⟨s6, (r1.seq (r2.seq (r5.seq r6))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
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
    exact p4KBody_arith hU hU' (Nat.mul_le_mul_left N hdf)
  · rw [back _ (by decide), hW]
  · rw [back _ (by decide), hL1]
  · rw [e6J]; omega
  · rw [e6J, hp6, hpos, posAt_succ I hlt, locD_eq']
    simp only [encNats_cons, List.length_append]; ring
  · rw [NSt.set_stk, hs5]; exact hstk
  · rw [NSt.set_out, ho5]; exact hout
  · intro r hr; rw [back r hr, hfr r hr]
  · rw [e6J]; omega
  · rw [hp6]; omega

/-- **Skipping the location section.** -/
lemma p4KLoop_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (st : NSt CR CQ) (hI : p4KInv I st st) (hj : st.env rJ = 0) :
    ∃ st', Good (encodeSystem I) w p4KLoop st st' (400 * (H I + 1) * Ex.nodeCost w) ∧
      st'.pos = posAt I I.numLocations ∧ st'.stk = st.stk ∧ st'.out = st.out ∧
      ∀ r, r ∉ kW → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨s7, r7, hI7, hc7⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rW)) (body := p4KBody) (p4KInv I st)
    (fun s => I.numLocations - s.env rJ) (fun s => H I - s.pos) (150 * Ex.nodeCost w)
    (200 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hW, -, hj, -⟩ := hI
      have := W_le I
      simp only [Ex.Fits, rv, hW]; omega, fun hc => p4KBody_good I hw hH hℓ st s hI hc⟩) st hI
  obtain ⟨hW7, -, hj7, hpos7, hstk7, hout7, hfr7⟩ := hI7
  have hjW : s7.env rJ = I.numLocations := by
    simp only [Ex.eval, rv, hW7] at hc7; split_ifs at hc7 with h <;> omega
  refine ⟨s7, r7.mono ?_, by rw [hpos7, hjW], hstk7, hout7, hfr7⟩
  have hW := W_le I
  have hc : condCost w (Ex.lt (rv rJ) (rv rW) : Ex CR) ≤ 4 * Ex.nodeCost w := by
    simp only [condCost, Ex.size, rv]; omega
  rw [hj, Nat.sub_zero]
  have hφ : H I - st.pos ≤ H I := Nat.sub_le _ _
  generalize condCost w (Ex.lt (rv rJ) (rv rW) : Ex CR) = c at *
  generalize Ex.nodeCost w = N at *
  generalize H I - st.pos = φ at *
  generalize H I = h at *
  generalize I.numLocations = W at *
  have h1 : 150 * N * φ ≤ 150 * N * h := Nat.mul_le_mul_left _ hφ
  have h2 : W * (200 * N + c) ≤ h * (204 * N) := Nat.mul_le_mul hW (by omega)
  nlinarith

end Lax119563Proofs.Compiler

end Compiler_P4SchK

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchLab2` -/

section Compiler_P4SchLab2

/-!
# Pass `P4`, schema part: link and update label emitters

* `lLab a`: link label `a` (`lnkE1`): last track in `rc1`, end answer in `rc2, rc3`;
* `uLab a b`: update label (`updE1`): previous in `rc8`, track `r4TP`, coefficient base `rc2`,
  rank code `rc5`;
* `fLab a b`: first entry of a column of a binary schema (`updF1`): start answer in `rc3, rc4`.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Link labels -/

/-- The link hub position `r4H + 4 r4Tn + a`. -/
def hL (a : ℕ) : Ex CR :=
  .add (rv r4H) (.add (rv r4Tn) (.add (rv r4Tn) (.add (rv r4Tn) (.add (rv r4Tn) (.const a)))))

lemma hL_eval (a : ℕ) (env : Fin CR → ℕ) : (hL a).eval env = env r4H + 4 * env r4Tn + a := by
  simp only [hL, rv, Ex.eval]; ring

/-- The link label `a`. -/
def lLab (a : ℕ) : CStm CR CQ :=
  .seq (pE (hL a) (.add (rv rc1) (.const a)))
    (.seq (.set rc6 (.const a)) (.seq (cposS rLB rc2 rc3 rc6) (pEo (hL a) r4F r4V)))

set_option maxHeartbeats 1000000 in
lemma lLab_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (a : ℕ) (ha : a ≤ 1)
    (s : NSt CR CQ) {H T LT LB o m : ℕ} (eH : s.env r4H = H) (eT : s.env r4Tn = T)
    (eLT : s.env rc1 = LT) (eLB : s.env rLB = LB) (eo : s.env rc2 = o) (em : s.env rc3 = m)
    (hm2 : m ≤ 2) (hH : H + 4 * T + 2 < 2 ^ w) (hLT : LT + 2 < 2 ^ w)
    (hU : LB + o + 2 < 2 ^ w) (hV4 : s.env r4V < 2 ^ w) (hm : s.env r4M + 2 < 2 ^ w) :
    ∃ s', Good x w (lLab a) s s' (80 * Ex.nodeCost w) ∧
      EdgeEff s s' (lnkE1 (H + 4 * T + a) LT (cposN LB o m a) a) ∧
      s'.env r4V < 2 ^ w ∧ ∀ r, r ∉ labW → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hLf : ∀ env : Fin CR → ℕ, env r4H = H → env r4Tn = T → (hL a).Fits w env := by
    intro env e1 e2; simp only [hL, rv, Ex.Fits, Ex.eval, e1, e2]; omega
  obtain ⟨s1, g1, eff1, fr1⟩ := pE_good (x := x) (w := w) (hL a) (.add (rv rc1) (.const a))
    s (hLf _ eH eT) (by simp only [rv, Ex.Fits, Ex.eval, eLT]; omega) (by omega)
  have g2 := Good.set (x := x) (w := w) (st := s1) (r := rc6) (e := .const a)
    (by simp only [Ex.Fits]; omega)
  set s2 := s1.set rc6 ((Ex.const a : Ex CR).eval s1.env)
  have e2 : ∀ r, r ≠ rc6 → r ≠ r4M → s2.env r = s.env r := fun r h1 h2 => by
    simp only [s2, NSt.set_env, Function.update_of_ne h1]; exact fr1 r h2
  have e26 : s2.env rc6 = a := by simp +decide [s2, Ex.eval]
  obtain ⟨s3, g3, f3, v3, hv3, k3, p3, o3, fr3⟩ := cposS_good (x := x) hw (lb := rLB) (off := rc2)
    (md := rc3) (a := rc6) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s2
    (by rw [e2 _ (by decide) (by decide), em]; exact hm2) (by rw [e26]; exact ha)
    (by rw [e2 _ (by decide) (by decide), e2 _ (by decide) (by decide), eLB, eo]; omega)
    (by rw [e2 _ (by decide) (by decide)]; exact hV4)
  rw [e2 _ (by decide) (by decide), e2 _ (by decide) (by decide), e2 _ (by decide) (by decide),
    e26, eLB, eo, em] at f3 v3
  have e3H : s3.env r4H = H := by
    rw [fr3 _ (by decide) (by decide), e2 _ (by decide) (by decide), eH]
  have e3T : s3.env r4Tn = T := by
    rw [fr3 _ (by decide) (by decide), e2 _ (by decide) (by decide), eT]
  have e3M : s3.env r4M = s.env r4M + 1 := by
    rw [fr3 _ (by decide) (by decide)]
    simp only [s2, NSt.set_env, Function.update_of_ne (show r4M ≠ rc6 by decide), eff1.2.1]
    simp
  obtain ⟨s4, g4, eff4, fr4⟩ := pEo_good (x := x) hw (hL a) r4F r4V (by decide) s3 _ f3 v3
    (hLf _ e3H e3T) hv3 (by rw [e3M]; omega)
  refine ⟨s4, (g1.seq (g2.seq (g3.seq g4))).mono ?_, ?_, ?_, ?_⟩
  · simp only [hL, rv, Ex.size]; nlinarith
  · have eff13 : EdgeEff s1 s3 [] := by
      refine EdgeEff.of_frame ?_ ?_ ?_ ?_
      · rw [k3]; simp +decide [s2]
      · rw [fr3 _ (by decide) (by decide)]; simp +decide [s2]
      · rw [p3]; simp +decide [s2]
      · rw [o3]; simp +decide [s2]
    have := (eff1.trans eff13).trans eff4
    simpa [lnkE1, hL_eval, e3H, e3T, eH, eT, eLT, rv, Ex.eval] using this
  · rw [fr4 _ (by decide)]; exact hv3
  · intro r hr
    simp only [labW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [fr4 r hr.2.2.2.2.2, fr3 r hr.2.2.2.1 hr.2.2.2.2.1]
    exact e2 r hr.1 hr.2.2.2.2.2

/-! ## Update labels -/

/-- `QR + 2 ⌊X / 2⌋ + d` (coefficient position from the rank code `X = 2ρ + 1` in `rc5`,
coefficient base in `rc2`). -/
def cpE (d : ℕ) : Ex CR :=
  .add (rv rc2) (.add (.half (rv rc5)) (.add (.half (rv rc5)) (.const d)))

lemma cpE_eval (d : ℕ) (env : Fin CR → ℕ) :
    (cpE d).eval env = env rc2 + 2 * (env rc5 / 2) + d := by
  simp only [cpE, rv, Ex.eval]; ring

/-- The update label `2a + b`. -/
def uLab (a b : ℕ) : CStm CR CQ :=
  .seq (pE (hE (2 * a + b)) (.add (rv rc8) (.const a)))
    (.seq (pE (hE (2 * a + b)) (.add (rv r4TP) (.const b)))
      (pE (hE (2 * a + b)) (cpE ((a + b) % 2))))

set_option maxHeartbeats 1000000 in
lemma uLab_good {w : ℕ} {x : List Bool} (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1)
    (s : NSt CR CQ) {H PP TP QR X : ℕ} (eH : s.env r4H = H) (ePP : s.env rc8 = PP)
    (eTP : s.env r4TP = TP) (eQR : s.env rc2 = QR) (eX : s.env rc5 = X)
    (hH : H + 4 < 2 ^ w) (hPP : PP + 2 < 2 ^ w) (hTP : TP + 2 < 2 ^ w)
    (hQR : QR + X + 2 < 2 ^ w) (hm : s.env r4M + 3 < 2 ^ w) :
    ∃ s', Good x w (uLab a b) s s' (60 * Ex.nodeCost w) ∧
      EdgeEff s s' (updE1 (H + (2 * a + b)) PP TP (QR + 2 * (X / 2)) a b) ∧
      ∀ r, r ≠ r4M → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have hX2 : 2 * (X / 2) ≤ X := Nat.mul_div_le X 2
  have hhf : ∀ env : Fin CR → ℕ, env r4H = H → (hE (2 * a + b)).Fits w env := by
    intro env e1; simp only [hE, rv, Ex.Fits, Ex.eval, e1]; omega
  obtain ⟨s1, g1, eff1, fr1⟩ := pE_good (x := x) (w := w) (hE (2 * a + b)) (.add (rv rc8) (.const a))
    s (hhf _ eH) (by simp only [rv, Ex.Fits, Ex.eval, ePP]; omega) (by omega)
  obtain ⟨s2, g2, eff2, fr2⟩ := pE_good (x := x) (w := w) (hE (2 * a + b)) (.add (rv r4TP) (.const b))
    s1 (hhf _ (by rw [fr1 _ (by decide), eH]))
    (by simp only [rv, Ex.Fits, Ex.eval, fr1 r4TP (by decide), eTP]; omega)
    (by rw [eff1.2.1]; simp; omega)
  have e2 : ∀ r, r ≠ r4M → s2.env r = s.env r := fun r h => (fr2 r h).trans (fr1 r h)
  obtain ⟨s3, g3, eff3, fr3⟩ := pE_good (x := x) (w := w) (hE (2 * a + b)) (cpE ((a + b) % 2))
    s2 (hhf _ (by rw [e2 _ (by decide), eH]))
    (by
      have : (a + b) % 2 ≤ 1 := by omega
      simp only [cpE, rv, Ex.Fits, Ex.eval, e2 rc2 (by decide), e2 rc5 (by decide), eQR, eX]
      refine ⟨by omega, ⟨by omega, ⟨by omega, by omega, by omega⟩, by omega⟩, by omega⟩)
    (by rw [eff2.2.1, eff1.2.1]; simp; omega)
  refine ⟨s3, (g1.seq (g2.seq g3)).mono ?_, ?_, fun r h => (fr3 r h).trans (e2 r h)⟩
  · simp only [hE, cpE, rv, Ex.size]; nlinarith
  · have := (eff1.trans eff2).trans eff3
    have h1 := fr1 r4H (by decide)
    have h2 := e2 r4H (by decide)
    have h3 := fr1 r4TP (by decide)
    have h4 := e2 rc2 (by decide)
    have h5 := e2 rc5 (by decide)
    simp only [hE_eval, cpE_eval, rv, Ex.eval, h1, h2, h3, h4, h5, eH, ePP, eTP, eQR, eX]
      at this
    simpa [updE1, add_assoc] using this

/-- Registers written by `fLab`. -/
def fW : List (Fin CR) := [r4F, r4V, r4M, r4Dist]

/-- The update label `2a + b` at the first entry of a column of a binary schema; bit register
`r4Dist`. -/
def fLab (a b : ℕ) : CStm CR CQ :=
  .seq (pE (hE (2 * a + b)) (.add (rv r4TP) (.const b)))
    (.seq (pE (hE (2 * a + b)) (cpE ((a + b) % 2)))
      (.seq (.set r4Dist (.const a)) (.seq (cposS rLB rc3 rc4 r4Dist)
        (pEo (hE (2 * a + b)) r4F r4V))))

set_option maxHeartbeats 1000000 in
lemma fLab_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1)
    (s : NSt CR CQ) {H TP QR X LB o m : ℕ} (eH : s.env r4H = H)
    (eTP : s.env r4TP = TP) (eQR : s.env rc2 = QR) (eX : s.env rc5 = X) (eLB : s.env rLB = LB)
    (eo : s.env rc3 = o) (em : s.env rc4 = m) (hm2 : m ≤ 2)
    (hH : H + 4 < 2 ^ w) (hTP : TP + 2 < 2 ^ w)
    (hQR : QR + X + 2 < 2 ^ w) (hU : LB + o + 2 < 2 ^ w) (hV4 : s.env r4V < 2 ^ w)
    (hm : s.env r4M + 3 < 2 ^ w) :
    ∃ s', Good x w (fLab a b) s s' (80 * Ex.nodeCost w) ∧
      EdgeEff s s' (updF1 (H + (2 * a + b)) TP (QR + 2 * (X / 2)) (cposN LB o m a) a b) ∧
      s'.env r4V < 2 ^ w ∧ ∀ r, r ∉ fW → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hX2 : 2 * (X / 2) ≤ X := Nat.mul_div_le X 2
  have hhf : ∀ env : Fin CR → ℕ, env r4H = H → (hE (2 * a + b)).Fits w env := by
    intro env e1; simp only [hE, rv, Ex.Fits, Ex.eval, e1]; omega
  obtain ⟨s1, g1, eff1, fr1⟩ := pE_good (x := x) (w := w) (hE (2 * a + b)) (.add (rv r4TP) (.const b))
    s (hhf _ eH) (by simp only [rv, Ex.Fits, Ex.eval, eTP]; omega) (by omega)
  obtain ⟨s2, g2, eff2, fr2⟩ := pE_good (x := x) (w := w) (hE (2 * a + b)) (cpE ((a + b) % 2))
    s1 (hhf _ (by rw [fr1 _ (by decide), eH]))
    (by
      have : (a + b) % 2 ≤ 1 := by omega
      simp only [cpE, rv, Ex.Fits, Ex.eval, fr1 rc2 (by decide), fr1 rc5 (by decide), eQR, eX]
      refine ⟨by omega, ⟨by omega, ⟨by omega, by omega, by omega⟩, by omega⟩, by omega⟩)
    (by rw [eff1.2.1]; simp; omega)
  have e2 : ∀ r, r ≠ r4M → s2.env r = s.env r := fun r h => (fr2 r h).trans (fr1 r h)
  have g3 := Good.set (x := x) (w := w) (st := s2) (r := r4Dist) (e := .const a)
    (by simp only [Ex.Fits]; omega)
  set s3 := s2.set r4Dist ((Ex.const a : Ex CR).eval s2.env)
  have e3 : ∀ r, r ≠ r4Dist → r ≠ r4M → s3.env r = s.env r := fun r h1 h2 => by
    simp only [s3, NSt.set_env, Function.update_of_ne h1]; exact e2 r h2
  have e3D : s3.env r4Dist = a := by simp +decide [s3, Ex.eval]
  obtain ⟨s4, g4, f4, v4, hv4, k4, p4, o4, fr4⟩ := cposS_good (x := x) hw (lb := rLB) (off := rc3)
    (md := rc4) (a := r4Dist) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s3
    (by rw [e3 _ (by decide) (by decide), em]; exact hm2) (by rw [e3D]; exact ha)
    (by rw [e3 _ (by decide) (by decide), e3 _ (by decide) (by decide), eLB, eo]; omega)
    (by rw [e3 _ (by decide) (by decide)]; exact hV4)
  rw [e3 _ (by decide) (by decide), e3 _ (by decide) (by decide), e3 _ (by decide) (by decide),
    e3D, eLB, eo, em] at f4 v4
  have e4H : s4.env r4H = H := by
    rw [fr4 _ (by decide) (by decide), e3 _ (by decide) (by decide), eH]
  have e4M : s4.env r4M = s.env r4M + 2 := by
    rw [fr4 _ (by decide) (by decide)]
    simp only [s3, NSt.set_env, Function.update_of_ne (show r4M ≠ r4Dist by decide), eff2.2.1,
      eff1.2.1]
    simp <;> omega
  obtain ⟨s5, g5, eff5, fr5⟩ := pEo_good (x := x) hw (hE (2 * a + b)) r4F r4V (by decide) s4 _
    f4 v4 (hhf _ e4H) hv4 (by rw [e4M]; omega)
  refine ⟨s5, (g1.seq (g2.seq (g3.seq (g4.seq g5)))).mono ?_, ?_, ?_, ?_⟩
  · simp only [hE, cpE, rv, Ex.size]; nlinarith
  · have eff24 : EdgeEff s2 s4 [] := by
      refine EdgeEff.of_frame ?_ ?_ ?_ ?_
      · rw [k4]; simp +decide [s3]
      · rw [fr4 _ (by decide) (by decide)]; simp +decide [s3]
      · rw [p4]; simp +decide [s3]
      · rw [o4]; simp +decide [s3]
    have := ((eff1.trans eff2).trans eff24).trans eff5
    have h1 := fr1 r4H (by decide)
    have h3 := fr1 rc2 (by decide)
    have h5 := fr1 rc5 (by decide)
    simp only [hE_eval, cpE_eval, rv, Ex.eval, h1, h3, h5, e4H, eH, eTP, eQR, eX] at this
    simpa [updF1, add_assoc] using this
  · rw [fr5 _ (by decide)]; exact hv4
  · intro r hr
    simp only [fW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [fr5 r hr.2.2.1, fr4 r hr.1 hr.2.1]
    exact e3 r hr.2.2.2 hr.2.2.1

end Lax119563Proofs.Compiler

end Compiler_P4SchLab2

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchHub` -/

section Compiler_P4SchHub

/-!
# Pass `P4`, schema part: whole hubs and answers

* `pAns o m`: pop one answer `[s, off, labs, seed]` from `qAns` (pushed on `qA2` for
  restoring), `o := off`, `m := ansMode ε` (`pAns_good`);
* `jLabs` (`junL`), `lLabs` (`lnkL`), `uLabs` (`updL`), `fLabs` (`updFL`): the four (two)
  labels of a hub.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Answers -/

/-- Pop a word of `qAns` into `r` and save it on `qA2`. -/
def pp (r : Fin CR) : CStm CR CQ := .seq (.pop qAns r) (.push qA2 (rv r))

lemma pp_good {w : ℕ} {x : List Bool} (r : Fin CR) (s : NSt CR CQ) {v : ℕ} {L : List ℕ}
    (hA : s.stk qAns = v :: L) (hv : v < 2 ^ w) :
    ∃ s', Good x w (pp r) s s' (5 * Ex.nodeCost w) ∧ s'.env = Function.update s.env r v ∧
      s'.stk = Function.update (Function.update s.stk qAns L) qA2 (v :: s.stk qA2) ∧
      s'.pos = s.pos ∧ s'.out = s.out := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have g1 := Good.pop (x := x) (w := w) (st := s) qAns r
  have g2 := Good.push (x := x) (w := w) (st := (s.setS qAns (s.stk qAns).tail).set r
    ((s.stk qAns).headD 0)) (q := qA2) (e := rv r) (by simp [rv, Ex.Fits, hA, hv])
  refine ⟨_, (g1.seq g2).mono ?_, ?_, ?_, rfl, rfl⟩
  · simp only [rv, Ex.size]; omega
  · simp [hA]
  · funext q
    simp only [NSt.setS_stk, NSt.set_stk, rv, Ex.eval, NSt.set_env, Function.update_self, hA,
      List.headD_cons, List.tail_cons]
    by_cases h : q = qA2
    · subst h; simp [Function.update_of_ne (show qA2 ≠ qAns by decide)]
    · simp [Function.update_of_ne h]

/-- The mode of the answer (labels `rc7`, seed `rc8`) into `m`. -/
def modeS (m : Fin CR) : CStm CR CQ :=
  .ite (.lt (rv rc7) (.const 2)) (.ite (rv r4Eps) (.set m (rv rc8)) (.set m (.const 0)))
    (.set m (.const 2))

lemma modeS_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (m : Fin CR) (s : NSt CR CQ)
    {sq off labs sd : ℕ} (e7 : s.env rc7 = labs) (e8 : s.env rc8 = sd)
    (hlabs : labs = 1 ∨ labs = 2) (hsd : sd ≤ 1) (hE : s.env r4Eps ≤ 1) :
    Good x w (modeS m) s (s.set m (ansMode (s.env r4Eps) [sq, off, labs, sd]))
      (10 * Ex.nodeCost w) := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hF : (Ex.lt (rv rc7) (.const 2) : Ex CR).Fits w s.env := by
    simp only [Ex.Fits, rv, e7]; omega
  have hFE : (rv r4Eps : Ex CR).Fits w s.env := by simp only [Ex.Fits, rv]; omega
  unfold ansMode
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rcases hlabs with rfl | rfl
  · rw [if_pos rfl]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hE with h | h
    · refine ((CStm.Good.iteT hF (by simp [Ex.eval, rv, e7]) (CStm.Good.iteF hFE (by simp [rv, Ex.eval, h])
        (Good.set (r := m) (e := .const 0) (by simp only [Ex.Fits]; omega)))).of_eq
        (by simp [h, Ex.eval]) ?_)
      simp only [condCost, rv, Ex.size]; nlinarith
    · refine ((CStm.Good.iteT hF (by simp [Ex.eval, rv, e7]) (CStm.Good.iteT hFE (by simp [rv, Ex.eval, h])
        (Good.set (r := m) (e := rv rc8) (by simp only [Ex.Fits, rv, e8]; omega)))).of_eq
        (by simp [h, Ex.eval, rv, e8]) ?_)
      simp only [condCost, rv, Ex.size]; nlinarith
  · rw [if_neg (by omega)]
    refine ((CStm.Good.iteF hF (by simp [Ex.eval, rv, e7])
      (Good.set (r := m) (e := .const 2) (by simp only [Ex.Fits]; omega))).of_eq
      (by simp [Ex.eval]) ?_)
    simp only [condCost, rv, Ex.size]; nlinarith

/-- Pop one answer: offset to `o`, mode to `m` (scratch `rc6, rc7, rc8`). -/
def pAns (o m : Fin CR) : CStm CR CQ :=
  .seq (pp rc6) (.seq (pp o) (.seq (pp rc7) (.seq (pp rc8) (modeS m))))

set_option maxHeartbeats 2000000 in
lemma pAns_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) {o m : Fin CR} (ho6 : o ≠ rc6)
    (ho7 : o ≠ rc7) (ho8 : o ≠ rc8) (hm6 : m ≠ rc6) (hm7 : m ≠ rc7) (hm8 : m ≠ rc8) (hom : o ≠ m)
    (hmE : m ≠ r4Eps) (hoE : o ≠ r4Eps) (s : NSt CR CQ) {sq off labs sd : ℕ} {rest : List ℕ}
    (hA : s.stk qAns = [sq, off, labs, sd] ++ rest) (hb : ∀ v ∈ [sq, off, labs, sd], v < 2 ^ w)
    (hlabs : labs = 1 ∨ labs = 2) (hsd : sd ≤ 1) (hE : s.env r4Eps ≤ 1) :
    ∃ s', Good x w (pAns o m) s s' (40 * Ex.nodeCost w) ∧
      s'.stk = Function.update (Function.update s.stk qAns rest) qA2
        ([sd, labs, off, sq] ++ s.stk qA2) ∧
      s'.env o = off ∧ s'.env m = ansMode (s.env r4Eps) [sq, off, labs, sd] ∧
      s'.env m ≤ 2 ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rc6 → r ≠ rc7 → r ≠ rc8 → r ≠ o → r ≠ m → s'.env r = s.env r := by
  have hb' := hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb'
  obtain ⟨b1, b2, b3, b4⟩ := hb'
  have hqq : qA2 ≠ qAns := by decide
  obtain ⟨s1, g1, v1, k1, p1, o1⟩ := pp_good (x := x) (w := w) rc6 s (v := sq)
    (L := off :: labs :: sd :: rest) (by simp [hA]) b1
  obtain ⟨s2, g2, v2, k2, p2, o2⟩ := pp_good (x := x) (w := w) o s1 (v := off)
    (L := labs :: sd :: rest) (by simp +decide [k1]) b2
  obtain ⟨s3, g3, v3, k3, p3, o3⟩ := pp_good (x := x) (w := w) rc7 s2 (v := labs)
    (L := sd :: rest) (by simp +decide [k2]) b3
  obtain ⟨s4, g4, v4, k4, p4, o4⟩ := pp_good (x := x) (w := w) rc8 s3 (v := sd)
    (L := rest) (by simp +decide [k3]) b4
  have e4 : ∀ r, r ≠ rc6 → r ≠ rc7 → r ≠ rc8 → r ≠ o → s4.env r = s.env r := by
    intro r h6 h7 h8 ho
    rw [v4, Function.update_of_ne h8, v3, Function.update_of_ne h7, v2, Function.update_of_ne ho,
      v1, Function.update_of_ne h6]
  have e47 : s4.env rc7 = labs := by
    rw [v4, Function.update_of_ne (by decide), v3, Function.update_self]
  have e48 : s4.env rc8 = sd := by rw [v4, Function.update_self]
  have e4o : s4.env o = off := by
    rw [v4, Function.update_of_ne ho8, v3, Function.update_of_ne ho7, v2, Function.update_self]
  have e4E : s4.env r4Eps = s.env r4Eps := e4 _ (by decide) (by decide) (by decide) hoE.symm
  have g5 := modeS_good (x := x) (sq := sq) (off := off) hw m s4 e47 e48 hlabs hsd
    (by rw [e4E]; exact hE)
  refine ⟨_, (g1.seq (g2.seq (g3.seq (g4.seq g5)))).mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [NSt.set_stk, k4, k3, k2, k1]
    funext q
    by_cases h : q = qA2
    · subst h; simp
    · by_cases h' : q = qAns
      · subst h'; simp +decide
      · simp [Function.update_of_ne h, Function.update_of_ne h']
  · simp [Function.update_of_ne hom, e4o]
  · simp [e4E]
  · simp only [NSt.set_env, Function.update_self, e4E]
    unfold ansMode; split_ifs <;> simp <;> nlinarith
  · simp [p4, p3, p2, p1]
  · simp [o4, o3, o2, o1]
  · intro r h6 h7 h8 ho hm
    simp [Function.update_of_ne hm, e4 r h6 h7 h8 ho]

/-! ## Junction hubs -/

lemma range4_flatMap {α : Type*} (f : ℕ → List α) :
    (List.range 4).flatMap f = f 0 ++ (f 1 ++ (f 2 ++ f 3)) := by
  simp [List.range_succ, List.flatMap_append]

lemma range2_flatMap {α : Type*} (f : ℕ → List α) :
    (List.range 2).flatMap f = f 0 ++ f 1 := by
  simp [List.range_succ, List.flatMap_append]

lemma length_sort2 (o₁ o₂ : Option ℕ) : (sort2 o₁ o₂).length ≤ 2 := by
  unfold sort2; split <;> (try split) <;> simp

lemma length_junE1 (h sp : ℕ) (pu pv : Option ℕ) (a b : ℕ) :
    (junE1 h sp pu pv a b).length ≤ 3 := by
  simp only [junE1, List.length_cons, List.length_map]; have := length_sort2 pu pv; omega

/-- The edges of a junction hub (answers `U`: `oU, mU`; `V`: `oV, mV`). -/
def junL (H SP LB oU mU oV mV : ℕ) : List (ℕ × ℕ) :=
  (List.range 4).flatMap fun i =>
    junE1 (H + i) SP (cposN LB oU mU (i / 2)) (cposN LB oV mV (i % 2)) (i / 2) (i % 2)

lemma length_junL (H SP LB oU mU oV mV : ℕ) : (junL H SP LB oU mU oV mV).length ≤ 12 := by
  rw [junL, range4_flatMap]
  simp only [List.length_append]
  have := length_junE1; linarith [this (H + 0) SP (cposN LB oU mU (0 / 2)) (cposN LB oV mV (0 % 2))
    (0 / 2) (0 % 2), this (H + 1) SP (cposN LB oU mU (1 / 2)) (cposN LB oV mV (1 % 2)) (1 / 2)
    (1 % 2), this (H + 2) SP (cposN LB oU mU (2 / 2)) (cposN LB oV mV (2 % 2)) (2 / 2) (2 % 2),
    this (H + 3) SP (cposN LB oU mU (3 / 2)) (cposN LB oV mV (3 % 2)) (3 / 2) (3 % 2)]

/-- The four junction labels. -/
def jLabs : CStm CR CQ := .seq (jLab 0 0) (.seq (jLab 0 1) (.seq (jLab 1 0) (jLab 1 1)))

set_option maxHeartbeats 2000000 in
lemma jLabs_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w)
    (s : NSt CR CQ) {H SP LB oU mU oV mV : ℕ} (eH : s.env r4H = H) (eSP : s.env r4SP = SP)
    (eLB : s.env rLB = LB) (eoU : s.env rc2 = oU) (emU : s.env rc3 = mU) (eoV : s.env rc4 = oV)
    (emV : s.env rc5 = mV) (hmU : mU ≤ 2) (hmV : mV ≤ 2) (hH : H + 4 < 2 ^ w)
    (hSP : SP + 2 < 2 ^ w) (hU : LB + oU + 2 < 2 ^ w) (hV : LB + oV + 2 < 2 ^ w)
    (hV4 : s.env r4V < 2 ^ w) (hm : s.env r4M + 12 < 2 ^ w) :
    ∃ s', Good x w jLabs s s' (400 * Ex.nodeCost w) ∧
      EdgeEff s s' (junL H SP LB oU mU oV mV) ∧
      s'.env r4V < 2 ^ w ∧ ∀ r, r ∉ labW → s'.env r = s.env r := by
  have L := length_junE1
  obtain ⟨s1, g1, f1, v1, r1⟩ := jLab_good (x := x) hw 0 0 (by norm_num) (by norm_num) s eH eSP
    eLB eoU emU eoV emV hmU hmV hH hSP hU hV hV4 (by omega)
  have q1 : ∀ r, r ∉ labW → s1.env r = s.env r := r1
  obtain ⟨s2, g2, f2, v2, r2⟩ := jLab_good (x := x) hw 0 1 (by norm_num) (by norm_num) s1
    (by rw [q1 _ (by decide), eH]) (by rw [q1 _ (by decide), eSP])
    (by rw [q1 _ (by decide), eLB]) (by rw [q1 _ (by decide), eoU])
    (by rw [q1 _ (by decide), emU]) (by rw [q1 _ (by decide), eoV])
    (by rw [q1 _ (by decide), emV]) hmU hmV hH hSP hU hV v1
    (by rw [f1.2.1]; have := L (H + (2 * 0 + 0)) SP (cposN LB oU mU 0) (cposN LB oV mV 0) 0 0
        omega)
  have q2 : ∀ r, r ∉ labW → s2.env r = s.env r := fun r h => (r2 r h).trans (q1 r h)
  obtain ⟨s3, g3, f3, v3, r3⟩ := jLab_good (x := x) hw 1 0 (by norm_num) (by norm_num) s2
    (by rw [q2 _ (by decide), eH]) (by rw [q2 _ (by decide), eSP])
    (by rw [q2 _ (by decide), eLB]) (by rw [q2 _ (by decide), eoU])
    (by rw [q2 _ (by decide), emU]) (by rw [q2 _ (by decide), eoV])
    (by rw [q2 _ (by decide), emV]) hmU hmV hH hSP hU hV v2
    (by rw [f2.2.1, f1.2.1]
        have := L (H + (2 * 0 + 0)) SP (cposN LB oU mU 0) (cposN LB oV mV 0) 0 0
        have := L (H + (2 * 0 + 1)) SP (cposN LB oU mU 0) (cposN LB oV mV 1) 0 1
        omega)
  have q3 : ∀ r, r ∉ labW → s3.env r = s.env r := fun r h => (r3 r h).trans (q2 r h)
  obtain ⟨s4, g4, f4, v4, r4⟩ := jLab_good (x := x) hw 1 1 (by norm_num) (by norm_num) s3
    (by rw [q3 _ (by decide), eH]) (by rw [q3 _ (by decide), eSP])
    (by rw [q3 _ (by decide), eLB]) (by rw [q3 _ (by decide), eoU])
    (by rw [q3 _ (by decide), emU]) (by rw [q3 _ (by decide), eoV])
    (by rw [q3 _ (by decide), emV]) hmU hmV hH hSP hU hV v3
    (by rw [f3.2.1, f2.2.1, f1.2.1]
        have := L (H + (2 * 0 + 0)) SP (cposN LB oU mU 0) (cposN LB oV mV 0) 0 0
        have := L (H + (2 * 0 + 1)) SP (cposN LB oU mU 0) (cposN LB oV mV 1) 0 1
        have := L (H + (2 * 1 + 0)) SP (cposN LB oU mU 1) (cposN LB oV mV 0) 1 0
        omega)
  refine ⟨s4, (g1.seq (g2.seq (g3.seq g4))).mono (by omega), ?_, v4,
    fun r h => (r4 r h).trans (q3 r h)⟩
  have := f1.trans (f2.trans (f3.trans f4))
  rw [junL, range4_flatMap]
  simpa using this

/-! ## Link hubs -/

/-- The edges of a link hub. -/
def lnkL (H LT LB o m : ℕ) : List (ℕ × ℕ) :=
  (List.range 2).flatMap fun a => lnkE1 (H + a) LT (cposN LB o m a) a

/-- The two link labels. -/
def lLabs : CStm CR CQ := .seq (lLab 0) (lLab 1)

lemma length_lnkE1 (h tp : ℕ) (pw : Option ℕ) (a : ℕ) : (lnkE1 h tp pw a).length ≤ 2 := by
  cases pw <;> simp [lnkE1]

set_option maxHeartbeats 1000000 in
lemma lLabs_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w)
    (s : NSt CR CQ) {H T LT LB o m : ℕ} (eH : s.env r4H = H) (eT : s.env r4Tn = T)
    (eLT : s.env rc1 = LT) (eLB : s.env rLB = LB) (eo : s.env rc2 = o) (em : s.env rc3 = m)
    (hm2 : m ≤ 2) (hH : H + 4 * T + 2 < 2 ^ w) (hLT : LT + 2 < 2 ^ w)
    (hU : LB + o + 2 < 2 ^ w) (hV4 : s.env r4V < 2 ^ w) (hm : s.env r4M + 4 < 2 ^ w) :
    ∃ s', Good x w lLabs s s' (160 * Ex.nodeCost w) ∧
      EdgeEff s s' (lnkL (H + 4 * T) LT LB o m) ∧
      s'.env r4V < 2 ^ w ∧ ∀ r, r ∉ labW → s'.env r = s.env r := by
  obtain ⟨s1, g1, f1, v1, r1⟩ := lLab_good (x := x) hw 0 (by norm_num) s eH eT eLT eLB eo em hm2
    hH hLT hU hV4 (by omega)
  obtain ⟨s2, g2, f2, v2, r2⟩ := lLab_good (x := x) hw 1 (by norm_num) s1
    (by rw [r1 _ (by decide), eH]) (by rw [r1 _ (by decide), eT]) (by rw [r1 _ (by decide), eLT])
    (by rw [r1 _ (by decide), eLB]) (by rw [r1 _ (by decide), eo]) (by rw [r1 _ (by decide), em])
    hm2 hH hLT hU v1
    (by rw [f1.2.1]; have := length_lnkE1 (H + 4 * T + 0) LT (cposN LB o m 0) 0; omega)
  refine ⟨s2, (g1.seq g2).mono (by omega), ?_, v2, fun r h => (r2 r h).trans (r1 r h)⟩
  have := f1.trans f2
  rw [lnkL, range2_flatMap]
  simpa using this

/-! ## Update hubs -/

/-- The edges of an update hub. -/
def updL (H PP TP cp : ℕ) : List (ℕ × ℕ) :=
  (List.range 4).flatMap fun i => updE1 (H + i) PP TP cp (i / 2) (i % 2)

/-- The edges of an update hub at the first entry of a column of a binary schema. -/
def updFL (H TP cp LB o m : ℕ) : List (ℕ × ℕ) :=
  (List.range 4).flatMap fun i => updF1 (H + i) TP cp (cposN LB o m (i / 2)) (i / 2) (i % 2)

/-- The four update labels. -/
def uLabs : CStm CR CQ := .seq (uLab 0 0) (.seq (uLab 0 1) (.seq (uLab 1 0) (uLab 1 1)))

/-- The four update labels at a first entry. -/
def fLabs : CStm CR CQ := .seq (fLab 0 0) (.seq (fLab 0 1) (.seq (fLab 1 0) (fLab 1 1)))

set_option maxHeartbeats 1000000 in
lemma uLabs_good {w : ℕ} {x : List Bool}
    (s : NSt CR CQ) {H PP TP QR X : ℕ} (eH : s.env r4H = H) (ePP : s.env rc8 = PP)
    (eTP : s.env r4TP = TP) (eQR : s.env rc2 = QR) (eX : s.env rc5 = X)
    (hH : H + 4 < 2 ^ w) (hPP : PP + 2 < 2 ^ w) (hTP : TP + 2 < 2 ^ w)
    (hQR : QR + X + 2 < 2 ^ w) (hm : s.env r4M + 12 < 2 ^ w) :
    ∃ s', Good x w uLabs s s' (240 * Ex.nodeCost w) ∧
      EdgeEff s s' (updL H PP TP (QR + 2 * (X / 2))) ∧
      ∀ r, r ≠ r4M → s'.env r = s.env r := by
  obtain ⟨s1, g1, f1, r1⟩ := uLab_good (x := x) 0 0 (by norm_num) (by norm_num) s eH ePP eTP eQR
    eX hH hPP hTP hQR (by omega)
  obtain ⟨s2, g2, f2, r2⟩ := uLab_good (x := x) 0 1 (by norm_num) (by norm_num) s1
    (by rw [r1 _ (by decide), eH]) (by rw [r1 _ (by decide), ePP]) (by rw [r1 _ (by decide), eTP])
    (by rw [r1 _ (by decide), eQR]) (by rw [r1 _ (by decide), eX]) hH hPP hTP hQR
    (by rw [f1.2.1]; simp [updE1]; omega)
  have q2 : ∀ r, r ≠ r4M → s2.env r = s.env r := fun r h => (r2 r h).trans (r1 r h)
  obtain ⟨s3, g3, f3, r3⟩ := uLab_good (x := x) 1 0 (by norm_num) (by norm_num) s2
    (by rw [q2 _ (by decide), eH]) (by rw [q2 _ (by decide), ePP]) (by rw [q2 _ (by decide), eTP])
    (by rw [q2 _ (by decide), eQR]) (by rw [q2 _ (by decide), eX]) hH hPP hTP hQR
    (by rw [f2.2.1, f1.2.1]; simp [updE1]; omega)
  have q3 : ∀ r, r ≠ r4M → s3.env r = s.env r := fun r h => (r3 r h).trans (q2 r h)
  obtain ⟨s4, g4, f4, r4⟩ := uLab_good (x := x) 1 1 (by norm_num) (by norm_num) s3
    (by rw [q3 _ (by decide), eH]) (by rw [q3 _ (by decide), ePP]) (by rw [q3 _ (by decide), eTP])
    (by rw [q3 _ (by decide), eQR]) (by rw [q3 _ (by decide), eX]) hH hPP hTP hQR
    (by rw [f3.2.1, f2.2.1, f1.2.1]; simp [updE1]; omega)
  refine ⟨s4, (g1.seq (g2.seq (g3.seq g4))).mono (by omega), ?_,
    fun r h => (r4 r h).trans (q3 r h)⟩
  have := f1.trans (f2.trans (f3.trans f4))
  rw [updL, range4_flatMap]
  simpa using this

lemma length_updF1 (h tp cp : ℕ) (pu : Option ℕ) (a b : ℕ) : (updF1 h tp cp pu a b).length ≤ 3 := by
  cases pu <;> simp [updF1]

set_option maxHeartbeats 2000000 in
lemma fLabs_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w)
    (s : NSt CR CQ) {H TP QR X LB o m : ℕ} (eH : s.env r4H = H)
    (eTP : s.env r4TP = TP) (eQR : s.env rc2 = QR) (eX : s.env rc5 = X) (eLB : s.env rLB = LB)
    (eo : s.env rc3 = o) (em : s.env rc4 = m) (hm2 : m ≤ 2)
    (hH : H + 4 < 2 ^ w) (hTP : TP + 2 < 2 ^ w)
    (hQR : QR + X + 2 < 2 ^ w) (hU : LB + o + 2 < 2 ^ w) (hV4 : s.env r4V < 2 ^ w)
    (hm : s.env r4M + 12 < 2 ^ w) :
    ∃ s', Good x w fLabs s s' (320 * Ex.nodeCost w) ∧
      EdgeEff s s' (updFL H TP (QR + 2 * (X / 2)) LB o m) ∧
      s'.env r4V < 2 ^ w ∧ ∀ r, r ∉ fW → s'.env r = s.env r := by
  have L := length_updF1
  obtain ⟨s1, g1, f1, v1, r1⟩ := fLab_good (x := x) hw 0 0 (by norm_num) (by norm_num) s eH eTP
    eQR eX eLB eo em hm2 hH hTP hQR hU hV4 (by omega)
  obtain ⟨s2, g2, f2, v2, r2⟩ := fLab_good (x := x) hw 0 1 (by norm_num) (by norm_num) s1
    (by rw [r1 _ (by decide), eH]) (by rw [r1 _ (by decide), eTP]) (by rw [r1 _ (by decide), eQR])
    (by rw [r1 _ (by decide), eX]) (by rw [r1 _ (by decide), eLB]) (by rw [r1 _ (by decide), eo])
    (by rw [r1 _ (by decide), em]) hm2 hH hTP hQR hU v1
    (by rw [f1.2.1]; have := L (H + (2 * 0 + 0)) TP (QR + 2 * (X / 2)) (cposN LB o m 0) 0 0
        omega)
  have q2 : ∀ r, r ∉ fW → s2.env r = s.env r := fun r h => (r2 r h).trans (r1 r h)
  obtain ⟨s3, g3, f3, v3, r3⟩ := fLab_good (x := x) hw 1 0 (by norm_num) (by norm_num) s2
    (by rw [q2 _ (by decide), eH]) (by rw [q2 _ (by decide), eTP]) (by rw [q2 _ (by decide), eQR])
    (by rw [q2 _ (by decide), eX]) (by rw [q2 _ (by decide), eLB]) (by rw [q2 _ (by decide), eo])
    (by rw [q2 _ (by decide), em]) hm2 hH hTP hQR hU v2
    (by rw [f2.2.1, f1.2.1]
        have := L (H + (2 * 0 + 0)) TP (QR + 2 * (X / 2)) (cposN LB o m 0) 0 0
        have := L (H + (2 * 0 + 1)) TP (QR + 2 * (X / 2)) (cposN LB o m 0) 0 1
        omega)
  have q3 : ∀ r, r ∉ fW → s3.env r = s.env r := fun r h => (r3 r h).trans (q2 r h)
  obtain ⟨s4, g4, f4, v4, r4⟩ := fLab_good (x := x) hw 1 1 (by norm_num) (by norm_num) s3
    (by rw [q3 _ (by decide), eH]) (by rw [q3 _ (by decide), eTP]) (by rw [q3 _ (by decide), eQR])
    (by rw [q3 _ (by decide), eX]) (by rw [q3 _ (by decide), eLB]) (by rw [q3 _ (by decide), eo])
    (by rw [q3 _ (by decide), em]) hm2 hH hTP hQR hU v3
    (by rw [f3.2.1, f2.2.1, f1.2.1]
        have := L (H + (2 * 0 + 0)) TP (QR + 2 * (X / 2)) (cposN LB o m 0) 0 0
        have := L (H + (2 * 0 + 1)) TP (QR + 2 * (X / 2)) (cposN LB o m 0) 0 1
        have := L (H + (2 * 1 + 0)) TP (QR + 2 * (X / 2)) (cposN LB o m 1) 1 0
        omega)
  refine ⟨s4, (g1.seq (g2.seq (g3.seq g4))).mono (by omega), ?_, v4,
    fun r h => (r4 r h).trans (q3 r h)⟩
  have := f1.trans (f2.trans (f3.trans f4))
  rw [updFL, range4_flatMap]
  simpa using this

end Lax119563Proofs.Compiler

end Compiler_P4SchHub

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchBits` -/

section Compiler_P4SchBits

/-!
# Pass `P4`, schema part: the bit pass of a column (checksum ranks)

`p4Bits`: with the OR bits `os` on `qOrsF` and the column bits `bs` in the input, push the codes
`2 ρ + 1` of the checksum ranks `chkRk os bs BR` on `qRk`, then the terminator `0`; count them
in `rc2`; `qOrsF` is restored (`p4Bits_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Reading a number (wrapper) -/

lemma rdN_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) {r : Fin CR} (hrp : r ≠ rP) (hrt : r ≠ rT)
    (s : NSt CR CQ) (v : ℕ) (rest : List Bool) (hx : x.drop s.pos = encodeNat v ++ rest)
    (hv : (Nat.bits v).length < w) :
    ∃ s', Good x w (rdNumS r rP rT) s s' (((encodeNat v).length + 1) * (20 * Ex.nodeCost w)) ∧
      s'.env r = v ∧ s'.pos = s.pos + (encodeNat v).length ∧ s'.stk = s.stk ∧ s'.out = s.out ∧
      ∀ q, q ≠ r → q ≠ rP → q ≠ rT → s'.env q = s.env q :=
  ⟨_, rdNumS_good hw hrp hrt (by decide) s v rest hx hv, rdNumFinal_env_r hrp hrt v, rfl, rfl,
    rfl, fun _ h1 h2 h3 => rdNumFinal_env_ne h1 h2 h3 v⟩

lemma length_encodeNat_le_one {v : ℕ} (hv : v ≤ 1) : (encodeNat v).length ≤ 3 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with rfl | rfl <;> decide

/-! ## Checksum ranks, one bit at a time -/

lemma chkRk_snoc : ∀ (os bs : List ℕ) (o b p : ℕ), os.length = bs.length →
    chkRk (os ++ [o]) (bs ++ [b]) p = chkRk os bs p ++ (if b = 1 then [p + os.sum] else [])
  | [], [], o, b, p, _ => by simp [chkRk]
  | o' :: os, b' :: bs, o, b, p, h => by
    simp only [List.cons_append, chkRk]
    rw [chkRk_snoc os bs o b (p + o') (by simpa using h)]
    simp [List.sum_cons, add_assoc]
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h

lemma chkRk_take_succ (os bs : List ℕ) (p : ℕ) {j : ℕ} (hj : j < bs.length)
    (hl : os.length = bs.length) :
    chkRk (os.take (j + 1)) (bs.take (j + 1)) p = chkRk (os.take j) (bs.take j) p ++
      (if bs[j] = 1 then [p + (os.take j).sum] else []) := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem (by omega), Option.toList_some, Option.toList_some,
    chkRk_snoc _ _ _ _ _ (by simp; omega)]

lemma length_chkRk_le : ∀ (os bs : List ℕ) (p : ℕ), (chkRk os bs p).length ≤ bs.length
  | o :: os, b :: bs, p => by
    simp only [chkRk, List.length_append, List.length_cons]
    have := length_chkRk_le os bs (p + o); split_ifs <;> simp <;> omega
  | [], _, _ => by simp [chkRk]
  | _ :: _, [], _ => by simp [chkRk]

/-- The rank code of a rank. -/
def rcode (ρ : ℕ) : ℕ := 2 * ρ + 1

/-! ## One bit -/

/-- One bit: read `b`, move `o` from `qOrsF` to `qOrsB`, push the code of the rank base `rc1`
if `b = 1` (count in `rc2`), `rc1 += o`, `rc3 += 1`. -/
def p4BitT : CStm CR CQ :=
  .seq (.pop qOrsF rc5) (.seq (.push qOrsB (rv rc5))
    (.seq (.ite (rv rc4) (.seq (.push qRk (.add (rv rc1) (.add (rv rc1) (.const 1))))
        (.set rc2 (.add (rv rc2) (.const 1)))) .skip)
      (.seq (.set rc1 (.add (rv rc1) (rv rc5))) (.set rc3 (.add (rv rc3) (.const 1))))))

def p4Bit : CStm CR CQ := .seq (rdNumS rc4 rP rT) p4BitT

/-- The bit pass. -/
def p4Bits : CStm CR CQ :=
  .seq (.set rc1 (rv r4BR)) (.seq (.set rc3 (.const 0))
    (.seq (.loop (.lt (rv rc3) (rv rL)) p4Bit)
      (.seq (moveAllS qOrsB qOrsF rc3 rc4) (.push qRk (.const 0)))))

/-- Registers written by the bit pass. -/
def bitW : List (Fin CR) := [rc1, rc2, rc3, rc4, rc5, rP, rT]

/-- The state of the bit loop after `j` bits. -/
def bitInv (os bs : List ℕ) (BR n0 P0 : ℕ) (S0 : Fin CQ → List ℕ) (s0 : NSt CR CQ) (j : ℕ)
    (s : NSt CR CQ) : Prop :=
  s.env rc3 = j ∧ s.env rc1 = BR + (os.take j).sum ∧
    s.env rc2 = n0 + (chkRk (os.take j) (bs.take j) BR).length ∧
    s.stk = Function.update (Function.update (Function.update S0 qOrsF (os.drop j)) qOrsB
      (os.take j).reverse) qRk
      (((chkRk (os.take j) (bs.take j) BR).map rcode).reverse ++ S0 qRk) ∧
    s.pos = P0 + (encodeNats (bs.take j)).length ∧ s.out = s0.out ∧
    ∀ r, r ∉ bitW → s.env r = s0.env r

/-- The tail of a bit step with explicit final state. -/
lemma p4BitT_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {o b v c j : ℕ}
    {L : List ℕ} (hF : s.stk qOrsF = o :: L) (eb : s.env rc4 = b) (hb : b ≤ 1) (ho : o ≤ 1)
    (e1 : s.env rc1 = v) (e2 : s.env rc2 = c) (e3 : s.env rc3 = j)
    (hv : 2 * v + 2 < 2 ^ w) (hc : c + 1 < 2 ^ w) (hj : j + 1 < 2 ^ w) :
    Good x w p4BitT s
      (((if b = 1 then
          ((((s.setS qOrsF L).set rc5 o).setS qOrsB (o :: s.stk qOrsB)).setS qRk
            ((2 * v + 1) :: s.stk qRk)).set rc2 (c + 1)
        else (((s.setS qOrsF L).set rc5 o).setS qOrsB (o :: s.stk qOrsB))).set rc1
          (v + o)).set rc3 (j + 1)) (30 * Ex.nodeCost w) := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have g1 := CStm.Good.pop (x := x) (w := w) (st := s) qOrsF rc5
  rw [hF] at g1
  simp only [List.tail_cons, List.headD_cons] at g1
  set s2 := (s.setS qOrsF L).set rc5 o
  have g2 := CStm.Good.push (x := x) (w := w) (st := s2) (q := qOrsB) (e := rv rc5)
    (by simp [s2, rv, Ex.Fits]; omega)
  have ev2 : (rv rc5 : Ex CR).eval s2.env = o := by simp [s2, rv, Ex.eval]
  rw [ev2] at g2
  set s3 := s2.setS qOrsB (o :: s2.stk qOrsB)
  have e3b : s3.env rc4 = b := by simp +decide [s3, s2, eb]
  have e31 : s3.env rc1 = v := by simp +decide [s3, s2, e1]
  have e32 : s3.env rc2 = c := by simp +decide [s3, s2, e2]
  have hs3 : s2.stk qOrsB = s.stk qOrsB := by simp +decide [s2]
  have hs3' : s3.stk qRk = s.stk qRk := by simp +decide [s3, s2]
  have hFb : (rv rc4 : Ex CR).Fits w s3.env := by simp only [rv, Ex.Fits, e3b]; omega
  obtain ⟨s4, g4, e4⟩ : ∃ s4, Good x w (.ite (rv rc4) (.seq (.push qRk (.add (rv rc1)
      (.add (rv rc1) (.const 1)))) (.set rc2 (.add (rv rc2) (.const 1)))) .skip) s3 s4
      (12 * Ex.nodeCost w) ∧ s4 = if b = 1 then (s3.setS qRk ((2 * v + 1) :: s.stk qRk)).set rc2
        (c + 1) else s3 := by
    by_cases hb1 : b = 1
    · have ga := CStm.Good.push (x := x) (w := w) (st := s3) (q := qRk)
        (e := .add (rv rc1) (.add (rv rc1) (.const 1))) (by simp only [Ex.Fits, rv, Ex.eval, e31]; omega)
      have gb := CStm.Good.set (x := x) (w := w)
        (st := s3.setS qRk ((Ex.add (rv rc1) (.add (rv rc1) (.const 1)) : Ex CR).eval s3.env ::
          s3.stk qRk)) (r := rc2) (e := .add (rv rc2) (.const 1))
        (by simp only [Ex.Fits, rv, Ex.eval, NSt.setS_env, e32]; omega)
      refine ⟨_, (CStm.Good.iteT hFb (by simp [rv, Ex.eval, e3b, hb1]) (ga.seq gb)).mono ?_, ?_⟩
      · simp only [condCost, Ex.size, rv]; nlinarith
      · rw [if_pos hb1]; simp only [Ex.eval, rv, e31, NSt.setS_env, e32, hs3']; ring_nf
    · refine ⟨_, (CStm.Good.iteF hFb (by simp [rv, Ex.eval, e3b]; omega) CStm.Good.skip).mono ?_,
        by rw [if_neg hb1]⟩
      simp only [condCost, Ex.size, rv]; nlinarith
  have e41 : s4.env rc1 = v := by rw [e4]; split_ifs <;> simp +decide [e31]
  have e45 : s4.env rc5 = o := by rw [e4]; split_ifs <;> simp +decide [s3, s2]
  have g5 := CStm.Good.set (x := x) (w := w) (st := s4) (r := rc1) (e := .add (rv rc1) (rv rc5))
    (by simp only [Ex.Fits, rv, Ex.eval, e41, e45]; omega)
  have ev5 : (Ex.add (rv rc1) (rv rc5) : Ex CR).eval s4.env = v + o := by
    simp [Ex.eval, rv, e41, e45]
  rw [ev5] at g5
  have e53 : (s4.set rc1 (v + o)).env rc3 = j := by
    rw [e4]; split_ifs <;> simp +decide [s3, s2, e3]
  have g6 := CStm.Good.set (x := x) (w := w) (st := s4.set rc1 (v + o)) (r := rc3)
    (e := .add (rv rc3) (.const 1)) (by simp only [Ex.Fits, rv, Ex.eval, e53]; omega)
  have ev6 : (Ex.add (rv rc3) (.const 1) : Ex CR).eval (s4.set rc1 (v + o)).env = j + 1 := by
    simp only [Ex.eval, rv, e53]
  rw [ev6] at g6
  refine (g1.seq (g2.seq (g4.seq (g5.seq g6)))).of_eq ?_ ?_
  · rw [e4]; simp only [s3, hs3]
  · simp only [Ex.size, rv]; nlinarith

set_option maxHeartbeats 4000000 in
lemma p4Bit_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (os bs : List ℕ) (BR n0 P0 : ℕ)
    (S0 : Fin CQ → List ℕ) (s0 : NSt CR CQ) (hl : os.length = bs.length)
    (hbs : ∀ b ∈ bs, b ≤ 1) (hos : ∀ o ∈ os, o ≤ 1) (rest : List Bool)
    (hx : x.drop P0 = encodeNats bs ++ rest)
    (hW : 2 * (BR + bs.length) + n0 + 2 < 2 ^ w)
    (j : ℕ) (hj : j < bs.length) (s : NSt CR CQ) (hI : bitInv os bs BR n0 P0 S0 s0 j s) :
    ∃ s', Good x w p4Bit s s' (120 * Ex.nodeCost w) ∧ bitInv os bs BR n0 P0 S0 s0 (j + 1) s' := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  obtain ⟨e3, e1, e2, est, epos, eout, efr⟩ := hI
  have hbj : bs[j] ≤ 1 := hbs _ (List.getElem_mem hj)
  have hjo : j < os.length := by omega
  have hoj : os[j] ≤ 1 := hos _ (List.getElem_mem hjo)
  have hsplit : encodeNats bs = encodeNats (bs.take j) ++
      (encodeNat bs[j] ++ encodeNats (bs.drop (j + 1))) := by
    conv_lhs => rw [← List.take_append_drop j bs, List.drop_eq_getElem_cons hj]
    rw [encodeNats_append, encNats_cons]
  have hx1 : x.drop s.pos = encodeNat bs[j] ++ (encodeNats (bs.drop (j + 1)) ++ rest) := by
    rw [epos, drop_add, hx, hsplit, List.append_assoc, List.drop_left, List.append_assoc]
  obtain ⟨s1, g1, v1, p1, k1, o1, f1⟩ := rdN_good (x := x) hw (r := rc4) (by decide) (by decide)
    s bs[j] _ hx1 (bits_le_one hbj hw)
  have hsum : (os.take j).sum ≤ j := by
    have := List.sum_le_card_nsmul (os.take j) 1 (fun o ho => hos o (List.mem_of_mem_take ho))
    simp at this; omega
  have hcl := length_chkRk_le (os.take j) (bs.take j) BR
  have hcl' : (bs.take j).length = j := by simp; omega
  have hQ : s1.stk qOrsF = os[j] :: os.drop (j + 1) := by
    rw [k1, est, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, List.drop_eq_getElem_cons hjo]
  have e11 : s1.env rc1 = BR + (os.take j).sum := by rw [f1 _ (by decide) (by decide) (by decide), e1]
  have e12 : s1.env rc2 = n0 + (chkRk (os.take j) (bs.take j) BR).length := by
    rw [f1 _ (by decide) (by decide) (by decide), e2]
  have e13 : s1.env rc3 = j := by rw [f1 _ (by decide) (by decide) (by decide), e3]
  have gT := p4BitT_good (x := x) hw s1 hQ v1 hbj hoj e11 e12 e13 (by omega) (by omega) (by omega)
  refine ⟨_, (g1.seq gT).mono ?_, ?_⟩
  · have := length_encodeNat_le_one hbj
    nlinarith
  have hts := chkRk_take_succ os bs BR hj hl
  have hsum1 : (os.take (j + 1)).sum = (os.take j).sum + os[j] := List.sum_take_succ _ _ hjo
  have htk : (os.take (j + 1)).reverse = os[j] :: (os.take j).reverse := by
    rw [List.take_add_one, List.getElem?_eq_getElem hjo]; simp
  have hB1 : s1.stk qOrsB = (os.take j).reverse := by rw [k1, est]; simp +decide
  have hR1 : s1.stk qRk = ((chkRk (os.take j) (bs.take j) BR).map rcode).reverse ++ S0 qRk := by
    rw [k1, est]; simp +decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · split_ifs <;> simp +decide
  · split_ifs <;> simp +decide [hsum1, e11] <;> ring
  · rw [hts]
    by_cases hb : bs[j] = 1
    · simp +decide [hb, e12]; ring
    · simp +decide [hb, e12]
  · funext q
    rw [hts, htk]
    by_cases hb : bs[j] = 1
    · simp only [hb, if_true]
      by_cases h1 : q = qRk
      · subst h1; simp +decide [hR1, rcode]; (try ring_nf)
      · by_cases h2 : q = qOrsB
        · subst h2; simp +decide [hB1]
        · by_cases h3 : q = qOrsF
          · subst h3; simp +decide
          · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3, k1,
              est]
    · simp only [hb, if_false, List.append_nil]
      by_cases h1 : q = qRk
      · subst h1; simp +decide [hR1]
      · by_cases h2 : q = qOrsB
        · subst h2; simp +decide [hB1]
        · by_cases h3 : q = qOrsF
          · subst h3; simp +decide
          · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3, k1,
              est]
  · have : (encodeNats (bs.take (j + 1))).length = (encodeNats (bs.take j)).length +
        (encodeNat bs[j]).length := by rw [encodeNats_take_succ bs hj, List.length_append]
    split_ifs <;> simp [p1, epos, this] <;> ring
  · split_ifs <;> simp [o1, eout]
  · intro r hr
    simp only [bitW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    have := f1 r h4 h6 h7
    split_ifs <;> simp [Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h5, this, efr r (by
        simp [bitW, h1, h2, h3, h4, h5, h6, h7])]


set_option maxHeartbeats 4000000 in
/-- **The bit pass of a column.** -/
lemma p4Bits_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (os bs : List ℕ) (s : NSt CR CQ)
    {BR n0 : ℕ} (hl : os.length = bs.length) (hbs : ∀ b ∈ bs, b ≤ 1) (hos : ∀ o ∈ os, o ≤ 1)
    (rest : List Bool) (hx : x.drop s.pos = encodeNats bs ++ rest)
    (eBR : s.env r4BR = BR) (e2 : s.env rc2 = n0) (eL : s.env rL = bs.length)
    (hF : s.stk qOrsF = os) (hB : s.stk qOrsB = []) (hbd : s.Bdd w) (hpos : s.pos ≤ x.length)
    (hW : 2 * (BR + bs.length) + n0 + 2 < 2 ^ w) :
    ∃ s', Good x w p4Bits s s' ((bs.length + 1) * (200 * Ex.nodeCost w)) ∧
      s'.stk = Function.update s.stk qRk
        (0 :: ((chkRk os bs BR).map rcode).reverse ++ s.stk qRk) ∧
      s'.env rc2 = n0 + (chkRk os bs BR).length ∧
      s'.pos = s.pos + (encodeNats bs).length ∧ s'.out = s.out ∧
      ∀ r, r ∉ bitW → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have ga := CStm.Good.set (x := x) (w := w) (st := s) (r := rc1) (e := rv r4BR)
    (by simp only [Ex.Fits, rv, eBR]; omega)
  have gb := CStm.Good.set (x := x) (w := w) (st := s.set rc1 BR) (r := rc3) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  have ev : (rv r4BR : Ex CR).eval s.env = BR := by simp [rv, Ex.eval, eBR]
  rw [ev] at ga
  set sa := (s.set rc1 BR).set rc3 ((Ex.const 0 : Ex CR).eval (s.set rc1 BR).env)
  have hI0 : bitInv os bs BR n0 s.pos s.stk s 0 sa := by
    refine ⟨by simp +decide [sa, Ex.eval], by simp +decide [sa], by simp +decide [sa, e2, chkRk],
      ?_, by simp [sa, encodeNats], by simp [sa], ?_⟩
    · funext q; simp only [sa, NSt.set_stk, List.drop_zero, List.take_zero, List.reverse_nil,
        List.map_nil, List.nil_append]
      by_cases h1 : q = qRk
      · subst h1; simp +decide [chkRk]
      · by_cases h2 : q = qOrsB
        · subst h2; simp +decide [hB]
        · by_cases h3 : q = qOrsF
          · subst h3; simp +decide [hF]
          · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
    · intro r hr
      simp only [bitW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [sa, Function.update_of_ne hr.1, Function.update_of_ne hr.2.2.1]
  obtain ⟨s1, gl, hI⟩ := CStm.Good.loop_idxC (x := x) (w := w) (e := .lt (rv rc3) (rv rL))
    (body := p4Bit) bs.length (bitInv os bs BR n0 s.pos s.stk s) (120 * Ex.nodeCost w)
    (by
      intro j hj s' hs'
      have e3 := hs'.1
      have eL' : s'.env rL = bs.length := by rw [hs'.2.2.2.2.2.2 _ (by decide), eL]
      refine ⟨by simp only [Ex.Fits, rv, e3, eL']; omega, by simp [Ex.eval, rv, e3, eL', hj], ?_⟩
      exact p4Bit_good hw os bs BR n0 s.pos s.stk s hl hbs hos rest hx hW j hj s' hs')
    (by
      intro s' hs'
      have e3 := hs'.1
      have eL' : s'.env rL = bs.length := by rw [hs'.2.2.2.2.2.2 _ (by decide), eL]
      exact ⟨by simp only [Ex.Fits, rv, e3, eL']; omega, by simp [Ex.eval, rv, e3, eL']⟩)
    sa hI0
  obtain ⟨e3, e1, e2', est, epos, eout, efr⟩ := hI
  have t1 : os.take bs.length = os := List.take_of_length_le (by omega)
  have t2 : bs.take bs.length = bs := List.take_of_length_le (by omega)
  have t3 : os.drop bs.length = [] := List.drop_of_length_le (by omega)
  rw [t1] at e1
  rw [t1, t2] at e2'
  rw [t1, t2, t3] at est
  have hbs1 := ((ga.seq gb).seq gl).bdd hw hbd hpos
  obtain ⟨s2, g2, k2, p2, o2, f2⟩ := moveAllS_good (x := x) hw (q := qOrsB) (q' := qOrsF)
    (t := rc3) (f := rc4) (by decide) (by decide) s1 hbs1.1
  have g3 := CStm.Good.push (x := x) (w := w) (st := s2) (q := qRk) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  have hl2 : (s1.stk qOrsB).length = bs.length := by
    rw [est]; simp +decide; omega
  refine ⟨_, (ga.seq (gb.seq (gl.seq (g2.seq g3)))).mono ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl2]; simp only [condCost, Ex.size, rv]; nlinarith
  · funext q
    simp only [NSt.setS_stk, k2, est, Ex.eval]
    by_cases h1 : q = qRk
    · subst h1; simp +decide
    · by_cases h2 : q = qOrsB
      · subst h2; simp +decide [hB]
      · by_cases h3 : q = qOrsF
        · subst h3; simp +decide [hF]
        · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  · simp only [NSt.setS_env]; rw [f2 _ (by decide) (by decide), e2']
  · simp only [NSt.setS]; rw [p2, epos, t2]
  · simp only [NSt.setS]; rw [o2, eout]
  · intro r hr
    simp only [NSt.setS_env]
    simp only [bitW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f2 r hr.2.2.1 hr.2.2.2.1]
    exact efr r (by simp [bitW]; tauto)

end Lax119563Proofs.Compiler

end Compiler_P4SchBits

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchC1` -/

section Compiler_P4SchC1

/-!
# Pass `P4`, schema part: section 1 of a column, the rank part

* `p4Hd`: read the block `i` of the column into `rc1`, update the count of block changes
  `r4Dist` (from the second column on) and `r4Prev` (`p4Hd_good`, `dist1`);
* `p4Blk`: push the codes of the block ranks (`blkCodes`; count in `rc2`) (`p4Blk_good`);
* `p4LT`: the last track position `TP + 2 ((k + 1) n - 1)` into `rc1`, `r4TP += 2 (k + 1) n`
  (`p4LT_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## The block of a column -/

/-- The count of block changes after a column with block `i` (column index `K`). -/
def dist1 (K D P i : ℕ) : ℕ := if K = 0 then D else D + (if i = P then 0 else 1)

def p4Hd : CStm CR CQ :=
  .seq (rdNumS rc1 rP rT) (.seq (.ite (rv r4K) (.set r4Dist (.add (rv r4Dist)
      (.lt (.const 0) (.add (.lt (rv rc1) (rv r4Prev)) (.lt (rv r4Prev) (rv rc1)))))) .skip)
    (.set r4Prev (rv rc1)))

set_option maxHeartbeats 2000000 in
lemma p4Hd_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {i K D P : ℕ}
    (rest : List Bool) (hx : x.drop s.pos = encodeNat i ++ rest) (hi : (Nat.bits i).length < w)
    (eK : s.env r4K = K) (eD : s.env r4Dist = D) (eP : s.env r4Prev = P)
    (hK : K < 2 ^ w) (hD : D + 1 < 2 ^ w) (hP : P < 2 ^ w) :
    ∃ s', Good x w p4Hd s s' (((encodeNat i).length + 1) * (20 * Ex.nodeCost w) +
        30 * Ex.nodeCost w) ∧
      s'.env rc1 = i ∧ s'.env r4Dist = dist1 K D P i ∧ s'.env r4Prev = i ∧
      s'.pos = s.pos + (encodeNat i).length ∧ s'.stk = s.stk ∧ s'.out = s.out ∧
      ∀ r, r ∉ [rc1, rP, rT, r4Dist, r4Prev] → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hiw : i < 2 ^ w := lt_of_bits_length hi
  obtain ⟨s1, g1, v1, p1, k1, o1, f1⟩ := rdN_good (x := x) hw (r := rc1) (by decide) (by decide)
    s i rest hx hi
  have e1K : s1.env r4K = K := by rw [f1 _ (by decide) (by decide) (by decide), eK]
  have e1D : s1.env r4Dist = D := by rw [f1 _ (by decide) (by decide) (by decide), eD]
  have e1P : s1.env r4Prev = P := by rw [f1 _ (by decide) (by decide) (by decide), eP]
  have hFK : (rv r4K : Ex CR).Fits w s1.env := by simp only [rv, Ex.Fits, e1K]; exact hK
  obtain ⟨s2, g2, e2⟩ : ∃ s2, Good x w (.ite (rv r4K) (.set r4Dist (.add (rv r4Dist)
      (.lt (.const 0) (.add (.lt (rv rc1) (rv r4Prev)) (.lt (rv r4Prev) (rv rc1)))))) .skip)
      s1 s2 (20 * Ex.nodeCost w) ∧ s2 = s1.set r4Dist (dist1 K D P i) := by
    by_cases hK0 : K = 0
    · refine ⟨s1, (CStm.Good.iteF hFK (by simp [rv, Ex.eval, e1K, hK0]) CStm.Good.skip).mono ?_,
        ?_⟩
      · simp only [condCost, rv, Ex.size]; nlinarith
      · rw [dist1, if_pos hK0]
        cases s1; simp only [NSt.set, NSt.mk.injEq, and_true]
        funext r; by_cases h : r = r4Dist
        · subst h; simpa using e1D
        · simp [Function.update_of_ne h]
    · have g := CStm.Good.set (x := x) (w := w) (st := s1) (r := r4Dist)
        (e := .add (rv r4Dist) (.lt (.const 0) (.add (.lt (rv rc1) (rv r4Prev))
          (.lt (rv r4Prev) (rv rc1))))) (by
          simp only [Ex.Fits, rv, Ex.eval, e1D, e1P, v1]
          refine ⟨by omega, ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩, ?_⟩ <;>
            split_ifs <;> omega)
      refine ⟨_, (CStm.Good.iteT hFK (by simp [rv, Ex.eval, e1K, hK0]) g).mono ?_, ?_⟩
      · simp only [condCost, rv, Ex.size]; nlinarith
      · rw [dist1, if_neg hK0]
        simp only [Ex.eval, rv, e1D, e1P, v1]
        congr 1
        by_cases h : i = P
        · subst h; simp
        · rw [if_neg h]
          rcases Nat.lt_or_gt_of_ne h with h' | h' <;> simp [h', Nat.not_lt.mpr h'.le]
  have e2c : s2.env rc1 = i := by rw [e2]; simp +decide [v1]
  have g3 := CStm.Good.set (x := x) (w := w) (st := s2) (r := r4Prev) (e := rv rc1)
    (by simp only [rv, Ex.Fits, e2c]; exact hiw)
  have ev : (rv rc1 : Ex CR).eval s2.env = i := by simp [rv, Ex.eval, e2c]
  rw [ev] at g3
  refine ⟨_, (g1.seq (g2.seq g3)).mono (by simp only [rv, Ex.size]; nlinarith), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simp +decide [e2c]
  · rw [e2]; simp +decide
  · simp
  · simp [e2, p1]
  · simp [e2, k1]
  · simp [e2, o1]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [NSt.set_env, Function.update_of_ne hr.2.2.2.2, e2, Function.update_of_ne hr.2.2.2.1]
    exact f1 r hr.1 hr.2.1 hr.2.2.1

/-! ## The block ranks -/

/-- The rank codes of the block rows of a column with block `i` (`k` blocks, `BR` block rows of
the domain, block-change count `d`). -/
def blkCodes (k BR d i : ℕ) : List ℕ :=
  if i + 1 < k then [rcode (if BR + 1 < k then d else i)] else (List.range (k - 1)).map rcode

/-- All block rows. -/
def blkAll : CStm CR CQ :=
  .seq (.set rc3 (.const 0)) (.seq (.loop (.lt (.add (rv rc3) (.const 1)) (rv rKk))
      (.seq (.push qRk (.add (rv rc3) (.add (rv rc3) (.const 1))))
        (.set rc3 (.add (rv rc3) (.const 1)))))
    (.set rc2 (rv rc3)))

/-- The block ranks. -/
def p4Blk : CStm CR CQ :=
  .seq (.set rc2 (.const 0)) (.ite (.lt (.add (rv rc1) (.const 1)) (rv rKk))
    (.seq (.ite (.lt (.add (rv r4BR) (.const 1)) (rv rKk))
        (.push qRk (.add (rv r4Dist) (.add (rv r4Dist) (.const 1))))
        (.push qRk (.add (rv rc1) (.add (rv rc1) (.const 1)))))
      (.set rc2 (.const 1)))
    blkAll)

set_option maxHeartbeats 4000000 in
lemma blkAll_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {k : ℕ}
    (ek : s.env rKk = k) (hk1 : 1 ≤ k) (hk : 2 * k + 2 < 2 ^ w) :
    ∃ s', Good x w blkAll s s' ((k + 1) * (20 * Ex.nodeCost w)) ∧
      s'.stk = Function.update s.stk qRk
        (((List.range (k - 1)).map rcode).reverse ++ s.stk qRk) ∧
      s'.env rc2 = k - 1 ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rc2 → r ≠ rc3 → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have ga := CStm.Good.set (x := x) (w := w) (st := s) (r := rc3) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  simp only [Ex.eval] at ga
  let P : ℕ → NSt CR CQ → Prop := fun j s' =>
    s'.env rc3 = j ∧ s'.stk = Function.update s.stk qRk
      (((List.range j).map rcode).reverse ++ s.stk qRk) ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rc3 → s'.env r = s.env r
  have hP0 : P 0 (s.set rc3 0) := by
    refine ⟨by simp, ?_, rfl, rfl, fun r h => by simp [Function.update_of_ne h]⟩
    funext q; by_cases h : q = qRk
    · subst h; simp
    · simp [Function.update_of_ne h]
  obtain ⟨s1, gl, h1, k1, p1, o1, f1⟩ := CStm.Good.loop_idxC (x := x) (w := w)
    (e := .lt (.add (rv rc3) (.const 1)) (rv rKk))
    (body := .seq (.push qRk (.add (rv rc3) (.add (rv rc3) (.const 1))))
      (.set rc3 (.add (rv rc3) (.const 1)))) (k - 1) P (10 * Ex.nodeCost w)
    (by
      rintro j hj s' ⟨e3, ks, ps, os, fs⟩
      have ek' : s'.env rKk = k := by rw [fs _ (by decide), ek]
      refine ⟨by simp only [Ex.Fits, rv, Ex.eval, e3, ek']; omega,
        by simp [Ex.eval, rv, e3, ek']; omega, ?_⟩
      have gp := CStm.Good.push (x := x) (w := w) (st := s') (q := qRk)
        (e := .add (rv rc3) (.add (rv rc3) (.const 1)))
        (by simp only [Ex.Fits, rv, Ex.eval, e3]; omega)
      have gs := CStm.Good.set (x := x) (w := w) (st := s'.setS qRk
        ((Ex.add (rv rc3) (.add (rv rc3) (.const 1)) : Ex CR).eval s'.env :: s'.stk qRk))
        (r := rc3) (e := .add (rv rc3) (.const 1))
        (by simp only [Ex.Fits, rv, Ex.eval, NSt.setS_env, e3]; omega)
      refine ⟨_, (gp.seq gs).mono (by simp only [Ex.size, rv]; nlinarith), ?_, ?_, ps, os, ?_⟩
      · simp [Ex.eval, rv, e3]
      · funext q
        simp only [NSt.set_stk, NSt.setS_stk, Ex.eval, rv, e3, ks]
        by_cases h : q = qRk
        · subst h; simp [List.range_succ, rcode]; ring
        · simp [Function.update_of_ne h]
      · intro r h; simp [Function.update_of_ne h, fs r h])
    (by
      rintro s' ⟨e3, -, -, -, fs⟩
      have ek' : s'.env rKk = k := by rw [fs _ (by decide), ek]
      exact ⟨by simp only [Ex.Fits, rv, Ex.eval, e3, ek']; omega,
        by simp [Ex.eval, rv, e3, ek']; omega⟩)
    _ hP0
  have gb := CStm.Good.set (x := x) (w := w) (st := s1) (r := rc2) (e := rv rc3)
    (by simp only [Ex.Fits, rv, h1]; omega)
  refine ⟨_, (ga.seq (gl.seq gb)).mono ?_, by simp [k1], by simp [Ex.eval, rv, h1], p1, o1, ?_⟩
  · simp only [condCost, Ex.size, rv]
    have : k - 1 + 1 = k := by omega
    nlinarith
  · intro r h2 h3; simp [Function.update_of_ne h2, f1 r h3]

lemma length_blkCodes_pos (k BR d i : ℕ) (hk : 2 ≤ k) : 1 ≤ (blkCodes k BR d i).length := by
  unfold blkCodes; split_ifs <;> simp; omega

set_option maxHeartbeats 4000000 in
lemma p4Blk_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {k BR d i : ℕ}
    (e1 : s.env rc1 = i) (ek : s.env rKk = k) (eBR : s.env r4BR = BR) (eD : s.env r4Dist = d)
    (hk1 : 1 ≤ k) (hk : 2 * k + 2 < 2 ^ w) (hi : 2 * i + 2 < 2 ^ w) (hd : 2 * d + 2 < 2 ^ w)
    (hBR : BR + 1 < 2 ^ w) :
    ∃ s', Good x w p4Blk s s' ((k + 2) * (30 * Ex.nodeCost w)) ∧
      s'.stk = Function.update s.stk qRk ((blkCodes k BR d i).reverse ++ s.stk qRk) ∧
      s'.env rc2 = (blkCodes k BR d i).length ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rc2 → r ≠ rc3 → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have ga := CStm.Good.set (x := x) (w := w) (st := s) (r := rc2) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  simp only [Ex.eval] at ga
  set s1 := s.set rc2 0
  have q1 : ∀ r, r ≠ rc2 → s1.env r = s.env r := fun r h => by simp [s1, Function.update_of_ne h]
  have hC : (Ex.lt (.add (rv rc1) (.const 1)) (rv rKk) : Ex CR).Fits w s1.env := by
    simp only [Ex.Fits, rv, Ex.eval, q1 rc1 (by decide), q1 rKk (by decide), e1, ek]; omega
  by_cases hik : i + 1 < k
  · have hC2 : (Ex.lt (.add (rv r4BR) (.const 1)) (rv rKk) : Ex CR).Fits w s1.env := by
      simp only [Ex.Fits, rv, Ex.eval, q1 r4BR (by decide), q1 rKk (by decide), eBR, ek]; omega
    set v := if BR + 1 < k then d else i with hv
    obtain ⟨s2, g2, e2⟩ : ∃ s2, Good x w (.ite (.lt (.add (rv r4BR) (.const 1)) (rv rKk))
        (.push qRk (.add (rv r4Dist) (.add (rv r4Dist) (.const 1))))
        (.push qRk (.add (rv rc1) (.add (rv rc1) (.const 1))))) s1 s2 (20 * Ex.nodeCost w) ∧
        s2 = s1.setS qRk (rcode v :: s1.stk qRk) := by
      by_cases hb : BR + 1 < k
      · refine ⟨_, (CStm.Good.iteT hC2 (by simp [Ex.eval, rv, q1 r4BR (by decide),
          q1 rKk (by decide), eBR, ek, hb]) (CStm.Good.push (by
            simp only [Ex.Fits, rv, Ex.eval, q1 r4Dist (by decide), eD]; omega))).mono ?_, ?_⟩
        · simp only [condCost, Ex.size, rv]; nlinarith
        · simp [Ex.eval, rv, q1 r4Dist (by decide), eD, hv, hb, rcode]; ring_nf
      · have c0 : (Ex.lt (.add (rv r4BR) (.const 1)) (rv rKk) : Ex CR).eval s1.env = 0 := by
          simp [Ex.eval, rv, q1 r4BR (by decide), q1 rKk (by decide), eBR, ek]; omega
        refine ⟨_, (CStm.Good.iteF hC2 c0 (CStm.Good.push (by
            simp only [Ex.Fits, rv, Ex.eval, q1 rc1 (by decide), e1]; omega))).mono ?_, ?_⟩
        · simp only [condCost, Ex.size, rv]; nlinarith
        · simp [Ex.eval, rv, q1 rc1 (by decide), e1, hv, hb, rcode]; ring_nf
    have g3 := CStm.Good.set (x := x) (w := w) (st := s2) (r := rc2) (e := .const 1)
      (by simp only [Ex.Fits]; omega)
    simp only [Ex.eval] at g3
    refine ⟨_, (ga.seq (CStm.Good.iteT hC (by simp [Ex.eval, rv, q1 rc1 (by decide),
      q1 rKk (by decide), e1, ek, hik]) (g2.seq g3))).mono ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [condCost, Ex.size, rv]; nlinarith
    · rw [e2]; simp [s1, blkCodes, hik, hv]
    · simp [blkCodes, hik]
    · rw [e2]; rfl
    · rw [e2]; rfl
    · intro r h2 h3; rw [e2]; simp [Function.update_of_ne h2, q1 r h2]
  · obtain ⟨s2, g2, k2, e22, p2, o2, f2⟩ := blkAll_good (x := x) hw s1
      (by rw [q1 _ (by decide), ek]) hk1 hk
    have c0 : (Ex.lt (.add (rv rc1) (.const 1)) (rv rKk) : Ex CR).eval s1.env = 0 := by
      simp [Ex.eval, rv, q1 rc1 (by decide), q1 rKk (by decide), e1, ek]; omega
    refine ⟨s2, (ga.seq (CStm.Good.iteF hC c0 g2)).mono ?_, ?_, ?_, p2, o2, ?_⟩
    · simp only [condCost, Ex.size, rv]; nlinarith
    · rw [k2]; simp [s1, blkCodes, hik]
    · rw [e22]; simp [blkCodes, hik]
    · intro r h2 h3; rw [f2 r h2 h3, q1 r h2]

end Lax119563Proofs.Compiler

end Compiler_P4SchC1

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchEnt` -/

section Compiler_P4SchEnt

/-!
# Pass `P4`, schema part: one entry of section 2

`p4Ent`: the update hub of the entry `t` of a column (hub `Hc + 4t` in `r4H`, track
`TPc + 2t` in `r4TP`, previous track `rc7`, first-entry flag `rc6`, rank code `rc5`,
coefficient base `rc2`, start answer `rc3, rc4`), then advance (`entE`, `p4Ent_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- The edges of entry `t` of a column (numbers). -/
def entE (T t Hc TPc SP cp LB oU mU : ℕ) : List (ℕ × ℕ) :=
  if t = 0 ∧ T = 0 then updFL (Hc + 4 * t) (TPc + 2 * t) cp LB oU mU
  else updL (Hc + 4 * t) (if t = 0 then SP else TPc + 2 * (t - 1)) (TPc + 2 * t) cp

/-- Advance to the next entry. -/
def p4EntAdv : CStm CR CQ :=
  .seq (.set rc7 (rv r4TP)) (.seq (.set r4TP (.add (rv r4TP) (.const 2)))
    (.seq (.set r4H (.add (rv r4H) (.const 4))) (.set rc6 (.const 0))))

lemma p4EntAdv_good {w : ℕ} {x : List Bool} (s : NSt CR CQ) {TP H : ℕ} (eTP : s.env r4TP = TP)
    (eH : s.env r4H = H) (hTP : TP + 2 < 2 ^ w) (hH : H + 4 < 2 ^ w) :
    Good x w p4EntAdv s ((((s.set rc7 TP).set r4TP (TP + 2)).set r4H (H + 4)).set rc6 0)
      (20 * Ex.nodeCost w) := by
  have hN := CStm.nodeCost_ge w
  have g1 := CStm.Good.set (x := x) (w := w) (st := s) (r := rc7) (e := rv r4TP)
    (by simp only [Ex.Fits, rv, eTP]; omega)
  have g2 := CStm.Good.set (x := x) (w := w) (st := s.set rc7 TP) (r := r4TP)
    (e := .add (rv r4TP) (.const 2)) (by simp +decide [Ex.Fits, rv, eTP, Ex.eval]; omega)
  have g3 := CStm.Good.set (x := x) (w := w) (st := (s.set rc7 TP).set r4TP (TP + 2)) (r := r4H)
    (e := .add (rv r4H) (.const 4)) (by simp +decide [Ex.Fits, rv, eH, Ex.eval]; omega)
  have g4 := CStm.Good.set (x := x) (w := w)
    (st := ((s.set rc7 TP).set r4TP (TP + 2)).set r4H (H + 4)) (r := rc6) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  have e1 : (rv r4TP : Ex CR).eval s.env = TP := by simp [rv, Ex.eval, eTP]
  have e2 : (Ex.add (rv r4TP) (.const 2) : Ex CR).eval (s.set rc7 TP).env = TP + 2 := by
    simp +decide [rv, Ex.eval, eTP]
  have e3 : (Ex.add (rv r4H) (.const 4) : Ex CR).eval ((s.set rc7 TP).set r4TP (TP + 2)).env =
      H + 4 := by simp +decide [rv, Ex.eval, eH]
  rw [e1] at g1; rw [e2] at g2; rw [e3] at g3
  exact (g1.seq (g2.seq (g3.seq g4))).mono (by simp only [Ex.size, rv]; omega)

/-- One entry. -/
def p4Ent : CStm CR CQ :=
  .seq (.ite (.lt (rv r4Tn) (rv rc6)) fLabs
      (.seq (.ite (rv rc6) (.set rc8 (rv r4SP)) (.set rc8 (rv rc7))) uLabs))
    p4EntAdv

/-- Registers written by an entry. -/
def entW : List (Fin CR) := [rc6, rc7, rc8, r4TP, r4H, r4F, r4V, r4M, r4Dist]

set_option maxHeartbeats 2000000 in
lemma p4Ent_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ)
    {T t Hc TPc SP QR X LB oU mU : ℕ} (eT : s.env r4Tn = T) (hT : T ≤ 1)
    (eF : s.env rc6 = if t = 0 then 1 else 0) (eP : 0 < t → s.env rc7 = TPc + 2 * (t - 1))
    (eSP : s.env r4SP = SP) (eH : s.env r4H = Hc + 4 * t) (eTP : s.env r4TP = TPc + 2 * t)
    (eQR : s.env rc2 = QR) (eX : s.env rc5 = X) (eLB : s.env rLB = LB) (eo : s.env rc3 = oU)
    (em : s.env rc4 = mU) (hm2 : mU ≤ 2)
    (hH : Hc + 4 * t + 4 < 2 ^ w) (hTP : TPc + 2 * t + 2 < 2 ^ w) (hSP : SP + 2 < 2 ^ w)
    (hQR : QR + X + 2 < 2 ^ w) (hU : LB + oU + 2 < 2 ^ w) (hV4 : s.env r4V < 2 ^ w)
    (hm : s.env r4M + 12 < 2 ^ w) :
    ∃ s', Good x w p4Ent s s' (500 * Ex.nodeCost w) ∧
      EdgeEff s s' (entE T t Hc TPc SP (QR + 2 * (X / 2)) LB oU mU) ∧
      s'.env rc7 = TPc + 2 * t ∧ s'.env r4TP = TPc + 2 * (t + 1) ∧
      s'.env r4H = Hc + 4 * (t + 1) ∧ s'.env rc6 = 0 ∧ s'.env r4V < 2 ^ w ∧
      ∀ r, r ∉ entW → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hC : (Ex.lt (rv r4Tn) (rv rc6) : Ex CR).Fits w s.env := by
    simp only [Ex.Fits, rv, eT, eF]; split_ifs <;> omega
  -- the hub
  obtain ⟨s1, g1, eff1, v1, fr1⟩ : ∃ s1, Good x w (.ite (.lt (rv r4Tn) (rv rc6)) fLabs
      (.seq (.ite (rv rc6) (.set rc8 (rv r4SP)) (.set rc8 (rv rc7))) uLabs)) s s1
      (400 * Ex.nodeCost w) ∧
      EdgeEff s s1 (entE T t Hc TPc SP (QR + 2 * (X / 2)) LB oU mU) ∧ s1.env r4V < 2 ^ w ∧
      ∀ r, r ∉ [rc8, r4F, r4V, r4M, r4Dist] → s1.env r = s.env r := by
    by_cases hf : t = 0 ∧ T = 0
    · obtain ⟨s1, g, eff, v, fr⟩ := fLabs_good (x := x) hw s eH eTP eQR eX eLB eo em hm2
        (by omega) (by omega) hQR hU hV4 hm
      refine ⟨s1, (CStm.Good.iteT hC (by simp [Ex.eval, rv, eT, eF, hf.1, hf.2]) g).mono ?_, ?_, v,
        fun r hr => fr r (by simp [fW] at hr ⊢; tauto)⟩
      · simp only [condCost, rv, Ex.size]; nlinarith
      · rw [entE, if_pos hf]; exact eff
    · have hc0 : (Ex.lt (rv r4Tn) (rv rc6) : Ex CR).eval s.env = 0 := by
        simp only [Ex.eval, rv, eT, eF]; split_ifs <;> omega
      set PP := if t = 0 then SP else TPc + 2 * (t - 1) with hPP
      have hF6 : (rv rc6 : Ex CR).Fits w s.env := by
        simp only [Ex.Fits, rv, eF]; split_ifs <;> omega
      obtain ⟨s0, g0, e0⟩ : ∃ s0, Good x w (.ite (rv rc6) (.set rc8 (rv r4SP))
          (.set rc8 (rv rc7))) s s0 (10 * Ex.nodeCost w) ∧ s0 = s.set rc8 PP := by
        by_cases ht : t = 0
        · refine ⟨_, (CStm.Good.iteT hF6 (by simp [Ex.eval, rv, eF, ht])
            (CStm.Good.set (r := rc8) (e := rv r4SP) (by simp only [Ex.Fits, rv, eSP]; omega))).mono
            ?_, by simp [hPP, ht, Ex.eval, rv, eSP]⟩
          simp only [condCost, rv, Ex.size]; nlinarith
        · have := eP (by omega)
          refine ⟨_, (CStm.Good.iteF hF6 (by simp [Ex.eval, rv, eF, ht])
            (CStm.Good.set (r := rc8) (e := rv rc7) (by simp only [Ex.Fits, rv, this]; omega))).mono
            ?_, by simp [hPP, ht, Ex.eval, rv, this]⟩
          simp only [condCost, rv, Ex.size]; nlinarith
      subst e0
      have q0 : ∀ r, r ≠ rc8 → (s.set rc8 PP).env r = s.env r := fun r h => by
        simp [Function.update_of_ne h]
      obtain ⟨s1, g, eff, fr⟩ := uLabs_good (x := x) (w := w) (s.set rc8 PP) (PP := PP)
        (by rw [q0 _ (by decide), eH]) (by simp) (by rw [q0 _ (by decide), eTP])
        (by rw [q0 _ (by decide), eQR]) (by rw [q0 _ (by decide), eX]) (by omega)
        (by rw [hPP]; split_ifs <;> omega) (by omega) hQR
        (by rw [q0 _ (by decide)]; omega)
      refine ⟨s1, (CStm.Good.iteF hC hc0 (g0.seq g)).mono ?_, ?_, ?_, ?_⟩
      · simp only [condCost, rv, Ex.size]; nlinarith
      · rw [entE, if_neg hf]
        refine (EdgeEff.of_frame (st := s) (st' := s.set rc8 PP) rfl ?_ rfl rfl).trans eff
          |> fun h => by simpa using h
        simp [Function.update_of_ne (show r4M ≠ rc8 by decide)]
      · rw [fr _ (by decide), q0 _ (by decide)]; exact hV4
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [fr r hr.2.2.2.1, q0 r hr.1]
  -- advance
  have q1 : ∀ r, r ∉ [rc8, r4F, r4V, r4M, r4Dist] → s1.env r = s.env r := fr1
  have e1TP : s1.env r4TP = TPc + 2 * t := by rw [q1 _ (by decide), eTP]
  have e1H : s1.env r4H = Hc + 4 * t := by rw [q1 _ (by decide), eH]
  have gA := p4EntAdv_good (x := x) s1 e1TP e1H (by omega) (by omega)
  set s2 := (((s1.set rc7 (TPc + 2 * t)).set r4TP (TPc + 2 * t + 2)).set r4H
    (Hc + 4 * t + 4)).set rc6 0
  refine ⟨s2, (g1.seq gA).mono (by nlinarith), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := eff1.trans (EdgeEff.of_frame (st := s1) (st' := s2) (by simp [s2])
      (by simp +decide [s2]) rfl rfl)
    simpa using this
  · simp +decide [s2]
  · simp +decide [s2]; ring
  · simp +decide [s2]; ring
  · simp +decide [s2]
  · simp +decide [s2]; exact v1
  · intro r hr
    simp only [entW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hr
    simp only [s2, NSt.set_env, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h4, Function.update_of_ne h5]
    exact q1 r (by simp [h3, h6, h7, h8, h9])

end Lax119563Proofs.Compiler

end Compiler_P4SchEnt

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchRk` -/

section Compiler_P4SchRk

/-!
# Pass `P4`, schema part: the rank loop of section 2

`EE st st' Es`: the edge stack and count of `st'` are those of `st` with `Es` pushed (other
stacks not described). `p4Rks`: for one `q`, pop the rank codes `cs` of a column from `qRkF`
(up to the terminator `0`), saving them on `qOrsB`, and emit the entries `t0, t0 + 1, …`
(`p4Rks_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Edge effects on the edge stack only -/

/-- The edge stack and the edge count of `st'` are those of `st` with `Es` pushed; cursor and
output kept. -/
def EE (st st' : NSt CR CQ) (Es : List (ℕ × ℕ)) : Prop :=
  st'.stk q4E = pairsRev Es ++ st.stk q4E ∧ st'.env r4M = st.env r4M + Es.length ∧
    st'.pos = st.pos ∧ st'.out = st.out

lemma EE.trans {st s₁ s₂ : NSt CR CQ} {E₁ E₂ : List (ℕ × ℕ)} (h₁ : EE st s₁ E₁)
    (h₂ : EE s₁ s₂ E₂) : EE st s₂ (E₁ ++ E₂) := by
  obtain ⟨a1, b1, c1, d1⟩ := h₁
  obtain ⟨a2, b2, c2, d2⟩ := h₂
  refine ⟨?_, ?_, c2.trans c1, d2.trans d1⟩
  · rw [a2, a1, pairsRev_append]; simp
  · rw [b2, b1, List.length_append]; ring

lemma EE.refl (st : NSt CR CQ) : EE st st [] := ⟨by simp [pairsRev], by simp, rfl, rfl⟩

lemma EE.of_frame {st st' : NSt CR CQ} (hs : st'.stk q4E = st.stk q4E)
    (hm : st'.env r4M = st.env r4M) (hp : st'.pos = st.pos) (ho : st'.out = st.out) :
    EE st st' [] := ⟨by simp [pairsRev, hs], by simp [hm], hp, ho⟩

lemma EdgeEff.ee {st st' : NSt CR CQ} {Es : List (ℕ × ℕ)} (h : EdgeEff st st' Es) :
    EE st st' Es := ⟨by rw [h.1]; simp, h.2.1, h.2.2.1, h.2.2.2⟩

lemma EdgeEff.stk_ne {st st' : NSt CR CQ} {Es : List (ℕ × ℕ)} (h : EdgeEff st st' Es) {q : Fin CQ}
    (hq : q ≠ q4E) : st'.stk q = st.stk q := by rw [h.1, Function.update_of_ne hq]

lemma length_updL (H PP TP cp : ℕ) : (updL H PP TP cp).length = 12 := by
  simp [updL, range4_flatMap, updE1]

lemma length_updFL_le (H TP cp LB o m : ℕ) : (updFL H TP cp LB o m).length ≤ 12 := by
  rw [updFL, range4_flatMap]
  simp only [List.length_append]
  have := length_updF1 (H + 0) TP cp (cposN LB o m (0 / 2)) (0 / 2) (0 % 2)
  have := length_updF1 (H + 1) TP cp (cposN LB o m (1 / 2)) (1 / 2) (1 % 2)
  have := length_updF1 (H + 2) TP cp (cposN LB o m (2 / 2)) (2 / 2) (2 % 2)
  have := length_updF1 (H + 3) TP cp (cposN LB o m (3 / 2)) (3 / 2) (3 % 2)
  omega

lemma length_entE_le (T t Hc TPc SP cp LB oU mU : ℕ) :
    (entE T t Hc TPc SP cp LB oU mU).length ≤ 12 := by
  unfold entE; split_ifs <;> first | exact length_updFL_le _ _ _ _ _ _ | simp [length_updL]

/-! ## The rank loop -/

/-- The body of the rank loop. -/
def p4RkB : CStm CR CQ := .seq (.push qOrsB (rv rc5)) (.seq p4Ent (.pop qRkF rc5))

/-- The rank loop for one `q`. -/
def p4Rks : CStm CR CQ := .seq (.pop qRkF rc5) (.loop (rv rc5) p4RkB)

/-- The entries `t0 + p` for the codes `cs` (index `p`). -/
def rksE (T t0 Hc TPc SP QR LB oU mU : ℕ) (cs : List ℕ) : List (ℕ × ℕ) :=
  cs.zipIdx.flatMap fun q => entE T (t0 + q.2) Hc TPc SP (QR + 2 * (q.1 / 2)) LB oU mU

lemma rksE_take_succ (T t0 Hc TPc SP QR LB oU mU : ℕ) (cs : List ℕ) {p : ℕ} (hp : p < cs.length) :
    rksE T t0 Hc TPc SP QR LB oU mU (cs.take (p + 1)) =
      rksE T t0 Hc TPc SP QR LB oU mU (cs.take p) ++
        entE T (t0 + p) Hc TPc SP (QR + 2 * (cs[p] / 2)) LB oU mU := by
  simp only [rksE, List.take_add_one, List.getElem?_eq_getElem hp, Option.toList_some,
    List.zipIdx_append, List.flatMap_append]
  simp [List.length_take, min_eq_left hp.le]

lemma length_rksE_le (T t0 Hc TPc SP QR LB oU mU : ℕ) :
    ∀ cs : List ℕ, (rksE T t0 Hc TPc SP QR LB oU mU cs).length ≤ 12 * cs.length := by
  intro cs
  rw [rksE, List.length_flatMap]
  calc (cs.zipIdx.map fun q => (entE T (t0 + q.2) Hc TPc SP (QR + 2 * (q.1 / 2)) LB oU mU).length).sum
      ≤ (cs.zipIdx.map fun _ => 12).sum := List.sum_le_sum (fun q _ => length_entE_le ..)
    _ = 12 * cs.length := by simp [List.sum_replicate, mul_comm]

/-- The state of the rank loop after `p` entries. -/
def rkInv (w T t0 Hc TPc SP QR LB oU mU : ℕ) (cs rest : List ℕ) (s0 : NSt CR CQ) (p : ℕ)
    (s : NSt CR CQ) : Prop :=
  EE s0 s (rksE T t0 Hc TPc SP QR LB oU mU (cs.take p)) ∧
    s.stk qRkF = (cs ++ 0 :: rest).drop (p + 1) ∧ s.stk qOrsB = (cs.take p).reverse ∧
    (∀ q, q ≠ q4E → q ≠ qRkF → q ≠ qOrsB → s.stk q = s0.stk q) ∧
    s.env rc5 = (cs ++ 0 :: rest).getD p 0 ∧
    s.env rc6 = (if t0 + p = 0 then 1 else 0) ∧ (0 < t0 + p → s.env rc7 = TPc + 2 * (t0 + p - 1)) ∧
    s.env r4H = Hc + 4 * (t0 + p) ∧ s.env r4TP = TPc + 2 * (t0 + p) ∧ s.env r4V < 2 ^ w ∧
    ∀ r, r ∉ rc5 :: entW → s.env r = s0.env r

lemma getD_append_cons_lt {cs rest : List ℕ} {p : ℕ} (hp : p < cs.length) :
    (cs ++ 0 :: rest).getD p 0 = cs[p] := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hp]

lemma getD_append_cons_len (cs rest : List ℕ) : (cs ++ 0 :: rest).getD cs.length 0 = 0 := by
  rw [List.getD_eq_getElem _ _ (by simp)]; simp

set_option maxHeartbeats 4000000 in
lemma p4Rks_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s0 : NSt CR CQ)
    {T t0 Hc TPc SP QR LB oU mU : ℕ} (cs rest : List ℕ) (hcs : ∀ X ∈ cs, 1 ≤ X)
    (hR : s0.stk qRkF = cs ++ 0 :: rest) (hB : s0.stk qOrsB = [])
    (eT : s0.env r4Tn = T) (hT : T ≤ 1) (eF : s0.env rc6 = if t0 = 0 then 1 else 0)
    (eP : 0 < t0 → s0.env rc7 = TPc + 2 * (t0 - 1))
    (eSP : s0.env r4SP = SP) (eH : s0.env r4H = Hc + 4 * t0) (eTP : s0.env r4TP = TPc + 2 * t0)
    (eQR : s0.env rc2 = QR) (eLB : s0.env rLB = LB) (eo : s0.env rc3 = oU)
    (em : s0.env rc4 = mU) (hm2 : mU ≤ 2)
    (hH : Hc + 4 * (t0 + cs.length) + 4 < 2 ^ w) (hTP : TPc + 2 * (t0 + cs.length) + 2 < 2 ^ w)
    (hSP : SP + 2 < 2 ^ w) (hQR : ∀ X ∈ cs, QR + X + 2 < 2 ^ w) (hU : LB + oU + 2 < 2 ^ w)
    (hV4 : s0.env r4V < 2 ^ w) (hm : s0.env r4M + 12 * cs.length + 12 < 2 ^ w) :
    ∃ s', Good x w p4Rks s0 s' ((cs.length + 1) * (600 * Ex.nodeCost w)) ∧
      rkInv w T t0 Hc TPc SP QR LB oU mU cs rest s0 cs.length s' := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h1w : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  -- the first pop
  have g0 := CStm.Good.pop (x := x) (w := w) (st := s0) qRkF rc5
  set s1 := (s0.setS qRkF (s0.stk qRkF).tail).set rc5 ((s0.stk qRkF).headD 0)
  have hI0 : rkInv w T t0 Hc TPc SP QR LB oU mU cs rest s0 0 s1 := by
    refine ⟨EE.of_frame (by simp +decide [s1, Function.update_of_ne (show q4E ≠ qRkF by decide)])
      (by simp +decide [s1, Function.update_of_ne (show r4M ≠ rc5 by decide)]) rfl rfl, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp +decide [s1, hR]
    · simp +decide [s1, Function.update_of_ne (show qOrsB ≠ qRkF by decide), hB]
    · intro q h1 h2 h3; simp +decide [s1, Function.update_of_ne h2]
    · simp +decide [s1, hR]; cases cs <;> simp
    · simp +decide [s1, Function.update_of_ne (show rc6 ≠ rc5 by decide), eF]
    · intro h; simp +decide [s1, Function.update_of_ne (show rc7 ≠ rc5 by decide), eP h]
    · simp +decide [s1, Function.update_of_ne (show r4H ≠ rc5 by decide), eH]
    · simp +decide [s1, Function.update_of_ne (show r4TP ≠ rc5 by decide), eTP]
    · simp +decide [s1, Function.update_of_ne (show r4V ≠ rc5 by decide), hV4]
    · intro r hr
      have : r ≠ rc5 := fun h => hr (by simp [h])
      simp +decide [s1, Function.update_of_ne this]
  obtain ⟨s', gl, hI⟩ := CStm.Good.loop_idxC (x := x) (w := w) (e := rv rc5) (body := p4RkB)
    cs.length (rkInv w T t0 Hc TPc SP QR LB oU mU cs rest s0) (520 * Ex.nodeCost w)
    (by
      rintro j hj s ⟨hE, hsR, hsB, hso, h5, h6, h7, hsH, hsTP, hsV, hfr⟩
      rw [getD_append_cons_lt hj] at h5
      have hX1 := hcs _ (List.getElem_mem hj)
      have hXb := hQR _ (List.getElem_mem hj)
      refine ⟨by simp only [rv, Ex.Fits, h5]; omega, by simp only [rv, Ex.eval, h5]; omega, ?_⟩
      have gp := CStm.Good.push (x := x) (w := w) (st := s) (q := qOrsB) (e := rv rc5)
        (by simp only [rv, Ex.Fits, h5]; omega)
      set s2 := s.setS qOrsB ((rv rc5 : Ex CR).eval s.env :: s.stk qOrsB)
      have q2 : ∀ r, s2.env r = s.env r := fun r => rfl
      have hfr' : ∀ r, r ∉ rc5 :: entW → s.env r = s0.env r := hfr
      have hlenE := length_rksE_le T t0 Hc TPc SP QR LB oU mU (cs.take j)
      have hlt : (cs.take j).length = j := by simp; omega
      obtain ⟨s3, g3, eff3, e37, e3TP, e3H, e36, v3, fr3⟩ := p4Ent_good (x := x) hw s2
        (T := T) (t := t0 + j) (Hc := Hc) (TPc := TPc) (SP := SP) (QR := QR) (X := cs[j])
        (LB := LB) (oU := oU) (mU := mU)
        (by rw [q2, hfr' _ (by decide), eT]) hT (by rw [q2, h6]) (fun h => by rw [q2, h7 h])
        (by rw [q2, hfr' _ (by decide), eSP]) (by rw [q2, hsH]) (by rw [q2, hsTP])
        (by rw [q2, hfr' _ (by decide), eQR]) (by rw [q2, h5])
        (by rw [q2, hfr' _ (by decide), eLB]) (by rw [q2, hfr' _ (by decide), eo])
        (by rw [q2, hfr' _ (by decide), em]) hm2 (by omega) (by omega) hSP hXb hU
        (by rw [q2]; exact hsV) (by rw [q2, hE.2.1]; omega)
      have gq := CStm.Good.pop (x := x) (w := w) (st := s3) qRkF rc5
      set s4 := (s3.setS qRkF (s3.stk qRkF).tail).set rc5 ((s3.stk qRkF).headD 0)
      have k3 : ∀ q, q ≠ q4E → s3.stk q = s2.stk q := fun q hq => eff3.stk_ne hq
      refine ⟨s4, (gp.seq (g3.seq gq)).mono ?_, ?_⟩
      · simp only [rv, Ex.size]; nlinarith
      have hdrop : (cs ++ 0 :: rest).drop (j + 1) = (cs ++ 0 :: rest).getD (j + 1) 0 ::
          (cs ++ 0 :: rest).drop (j + 1 + 1) := by
        rw [List.getD_eq_getElem _ _ (by simp; omega)]
        exact List.drop_eq_getElem_cons (by simp; omega)
      have s3R : s3.stk qRkF = (cs ++ 0 :: rest).drop (j + 1) := by
        rw [k3 _ (by decide)]; simp +decide [s2, Function.update_of_ne (show qRkF ≠ qOrsB by decide), hsR]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have ee := hE.trans ((EE.of_frame (st := s) (st' := s2)
          (by simp +decide [s2, Function.update_of_ne (show q4E ≠ qOrsB by decide)]) rfl rfl rfl).trans
          (eff3.ee.trans (EE.of_frame (st := s3) (st' := s4)
            (by simp +decide [s4, Function.update_of_ne (show q4E ≠ qRkF by decide)])
            (by simp +decide [s4, Function.update_of_ne (show r4M ≠ rc5 by decide)]) rfl rfl)))
        rw [rksE_take_succ _ _ _ _ _ _ _ _ _ _ hj]
        simpa [q2, h5] using ee
      · simp only [s4, NSt.set_stk, NSt.setS_stk, Function.update_self, s3R, hdrop,
          List.tail_cons]
      · simp only [s4, NSt.set_stk, NSt.setS_stk, Function.update_of_ne
          (show qOrsB ≠ qRkF by decide), k3 _ (show qOrsB ≠ q4E by decide), s2,
          Function.update_self, hsB, rv, Ex.eval, h5, List.take_add_one,
          List.getElem?_eq_getElem hj, Option.toList_some, List.reverse_append,
          List.reverse_singleton, List.singleton_append]
      · intro q h1 h2 h3
        simp only [s4, NSt.set_stk, NSt.setS_stk, Function.update_of_ne h2, k3 q h1, s2,
          Function.update_of_ne h3]
        exact hso q h1 h2 h3
      · simp +decide [s4, s3R, hdrop]
      · simp +decide [s4, Function.update_of_ne (show rc6 ≠ rc5 by decide), e36]
      · intro _; simp +decide [s4, Function.update_of_ne (show rc7 ≠ rc5 by decide), e37] <;> omega
      · simp +decide [s4, Function.update_of_ne (show r4H ≠ rc5 by decide), e3H]; ring
      · simp +decide [s4, Function.update_of_ne (show r4TP ≠ rc5 by decide), e3TP]; ring
      · simp +decide [s4, Function.update_of_ne (show r4V ≠ rc5 by decide), v3]
      · intro r hr
        have h5' : r ≠ rc5 := fun h => hr (by simp [h])
        have hr' : r ∉ entW := fun h => hr (List.mem_cons_of_mem _ h)
        simp only [s4, NSt.set_env, NSt.setS_env, Function.update_of_ne h5', fr3 r hr', q2]
        exact hfr' r hr)
    (by
      rintro s ⟨-, -, -, -, h5, -⟩
      rw [getD_append_cons_len] at h5
      exact ⟨by simp only [rv, Ex.Fits, h5]; omega, by simp [rv, Ex.eval, h5]⟩)
    s1 hI0
  refine ⟨s', (g0.seq gl).mono ?_, hI⟩
  simp only [condCost, rv, Ex.size]; nlinarith

end Lax119563Proofs.Compiler

end Compiler_P4SchRk

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchC1b` -/

section Compiler_P4SchC1b

/-!
# Pass `P4`, schema part: section 1 of a column, last track and hub edges

* `p4LT_good`: the last track position;
* `c1Jun_good`: the junction hub (ternary schemas: answers `U`, `V`);
* `c1Lnk_good`: the link hub (answer of the end location);
* `p4Adv1_good`: advance the column pointers.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## The last track -/

def p4LT : CStm CR CQ :=
  .seq (mulS rc3 rKk rc2 rc4) (.seq (.set rc3 (.add (rv rc3) (rv rc2))) (.seq (predS rc5 rc3)
    (.seq (.set rc1 (.add (rv r4TP) (.add (rv rc5) (rv rc5))))
      (.set r4TP (.add (rv rc1) (.const 2))))))

set_option maxHeartbeats 4000000 in
lemma p4LT_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {k n TP : ℕ}
    (e2 : s.env rc2 = n) (ek : s.env rKk = k) (eTP : s.env r4TP = TP) (hn : 1 ≤ n)
    (hb : TP + 2 * ((k + 1) * n) + 2 < 2 ^ w) :
    ∃ s', Good x w p4LT s s' ((k + 2) * (n + 1) * (40 * Ex.nodeCost w)) ∧
      s'.env rc1 = TP + 2 * ((k + 1) * n - 1) ∧ s'.env r4TP = TP + 2 * ((k + 1) * n) ∧
      s'.stk = s.stk ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ∉ [rc1, rc3, rc4, rc5, r4TP] → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have hkn : k * n ≤ (k + 1) * n := Nat.mul_le_mul_right _ (by omega)
  have hkn' : (k + 1) * n = k * n + n := by ring
  have g1 := mulS_good (x := x) (Q := CQ) hw (dst := rc3) (a := rKk) (b := rc2) (j := rc4)
    (by decide) (by decide) (by decide) (by decide) (by decide) s ek e2 (by omega) (by omega)
  set s1 := (s.set rc3 (k * n)).set rc4 n
  have g2 := CStm.Good.set (x := x) (w := w) (st := s1) (r := rc3) (e := .add (rv rc3) (rv rc2))
    (by simp +decide [s1, Ex.Fits, rv, Ex.eval, e2]; omega)
  have ev2 : (Ex.add (rv rc3) (rv rc2) : Ex CR).eval s1.env = (k + 1) * n := by
    simp +decide [s1, Ex.eval, rv, e2]; ring
  rw [ev2] at g2
  set s2 := s1.set rc3 ((k + 1) * n)
  have g3 := predS_good (x := x) (Q := CQ) hw (dst := rc5) (n := rc3) (by decide) s2
    (N := (k + 1) * n) (by simp [s2]) (by omega)
  set s3 := s2.set rc5 ((k + 1) * n - 1)
  have e3TP : s3.env r4TP = TP := by simp +decide [s3, s2, s1, eTP]
  have e35 : s3.env rc5 = (k + 1) * n - 1 := by simp [s3]
  have g4 := CStm.Good.set (x := x) (w := w) (st := s3) (r := rc1)
    (e := .add (rv r4TP) (.add (rv rc5) (rv rc5)))
    (by simp only [Ex.Fits, rv, Ex.eval, e3TP, e35]; omega)
  have ev4 : (Ex.add (rv r4TP) (.add (rv rc5) (rv rc5)) : Ex CR).eval s3.env =
      TP + 2 * ((k + 1) * n - 1) := by simp only [Ex.eval, rv, e3TP, e35]; ring
  rw [ev4] at g4
  set s4 := s3.set rc1 (TP + 2 * ((k + 1) * n - 1))
  have g5 := CStm.Good.set (x := x) (w := w) (st := s4) (r := r4TP) (e := .add (rv rc1) (.const 2))
    (by simp +decide [s4, Ex.Fits, rv, Ex.eval]; omega)
  have ev5 : (Ex.add (rv rc1) (.const 2) : Ex CR).eval s4.env = TP + 2 * ((k + 1) * n) := by
    simp +decide [s4, Ex.eval, rv]
    have : 1 ≤ (k + 1) * n := by nlinarith
    omega
  rw [ev5] at g5
  refine ⟨_, (g1.seq (g2.seq (g3.seq (g4.seq g5)))).mono ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [Ex.size, rv]
    nlinarith
  · simp +decide [s4]
  · simp
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [s4, s3, s2, s1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
      Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2.1,
      Function.update_of_ne hr.2.2.2.2]

/-! ## Junction and link hubs -/

/-- The junction hub of a column (ternary schemas only). -/
def c1Jun : CStm CR CQ := .ite (rv r4Tn) (.seq (pAns rc2 rc3) (.seq (pAns rc4 rc5) jLabs)) .skip

/-- The link hub of a column. -/
def c1Lnk : CStm CR CQ := .seq (pAns rc2 rc3) lLabs

/-- An answer `[s, off, labs, seed]` as consumed by `P4`. -/
def AnsOK (w : ℕ) (A : List ℕ) : Prop :=
  ∃ sq off labs sd, A = [sq, off, labs, sd] ∧ (labs = 1 ∨ labs = 2) ∧ sd ≤ 1 ∧
    ∀ v ∈ A, v < 2 ^ w

/-- The offset of an answer. -/
def aOff (A : List ℕ) : ℕ := A.getD 1 0

lemma ansMode_le {eps : ℕ} (he : eps ≤ 1) {A : List ℕ} {w : ℕ} (h : AnsOK w A) :
    ansMode eps A ≤ 2 := by
  obtain ⟨sq, off, labs, sd, rfl, -, hsd, -⟩ := h
  unfold ansMode; simp only [List.getD_cons_succ, List.getD_cons_zero]
  split_ifs
  · have : eps * sd ≤ 1 * 1 := Nat.mul_le_mul he hsd
    omega
  · omega

set_option maxHeartbeats 4000000 in
lemma c1Jun_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {T H SP LB : ℕ}
    (AU AV rest : List ℕ) (eT : s.env r4Tn = T) (hT : T ≤ 1) (eH : s.env r4H = H)
    (eSP : s.env r4SP = SP) (eLB : s.env rLB = LB) (hE : s.env r4Eps ≤ 1)
    (hA : s.stk qAns = (if T = 1 then AU ++ AV else []) ++ rest)
    (hU : T = 1 → AnsOK w AU) (hV : T = 1 → AnsOK w AV)
    (hH : H + 4 < 2 ^ w) (hSP : SP + 2 < 2 ^ w)
    (hbU : T = 1 → LB + aOff AU + 2 < 2 ^ w) (hbV : T = 1 → LB + aOff AV + 2 < 2 ^ w)
    (hV4 : s.env r4V < 2 ^ w) (hm : s.env r4M + 12 < 2 ^ w) :
    ∃ s', Good x w c1Jun s s' (600 * Ex.nodeCost w) ∧
      EE s s' (if T = 1 then junL H SP LB (aOff AU) (ansMode (s.env r4Eps) AU) (aOff AV)
        (ansMode (s.env r4Eps) AV) else []) ∧
      s'.stk qAns = rest ∧
      s'.stk qA2 = (if T = 1 then AV.reverse ++ AU.reverse else []) ++ s.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qAns → q ≠ qA2 → s'.stk q = s.stk q) ∧ s'.env r4V < 2 ^ w ∧
      ∀ r, r ∉ [rc2, rc3, rc4, rc5, rc6, rc7, rc8, r4F, r4V, r4M] → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have hF : (rv r4Tn : Ex CR).Fits w s.env := by
    have : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    simp only [rv, Ex.Fits, eT]; omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hT with rfl | rfl
  · refine ⟨s, (CStm.Good.iteF hF (by simp [rv, Ex.eval, eT]) CStm.Good.skip).mono ?_,
      by simpa using EE.refl s, by simpa using hA, by simp, fun _ _ _ _ => rfl, hV4,
      fun _ _ => rfl⟩
    simp only [condCost, rv, Ex.size]; nlinarith
  · obtain ⟨sq, oU, lU, dU, rfl, hlU, hdU, hbU'⟩ := hU rfl
    obtain ⟨sv, oV, lV, dV, rfl, hlV, hdV, hbV'⟩ := hV rfl
    simp only [if_true] at hA
    obtain ⟨s1, g1, k1, v1, m1, mm1, p1, o1, f1⟩ := pAns_good (x := x) hw (o := rc2) (m := rc3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) s (rest := [sv, oV, lV, dV] ++ rest) (by rw [hA]; simp) hbU' hlU
      hdU hE
    have e1E : s1.env r4Eps = s.env r4Eps := f1 _ (by decide) (by decide) (by decide)
      (by decide) (by decide)
    obtain ⟨s2, g2, k2, v2, m2, mm2, p2, o2, f2⟩ := pAns_good (x := x) hw (o := rc4) (m := rc5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) s1 (rest := rest) (by rw [k1]; simp +decide) hbV' hlV hdV
      (by rw [e1E]; exact hE)
    have q2 : ∀ r, r ∉ [rc2, rc3, rc4, rc5, rc6, rc7, rc8] → s2.env r = s.env r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [f2 r hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2 hr.2.2.1 hr.2.2.2.1,
        f1 r hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2 hr.1 hr.2.1]
    have e2U : s2.env rc2 = oU := by
      rw [f2 _ (by decide) (by decide) (by decide) (by decide) (by decide), v1]
    have e2m : s2.env rc3 = ansMode (s.env r4Eps) [sq, oU, lU, dU] := by
      rw [f2 _ (by decide) (by decide) (by decide) (by decide) (by decide), m1]
    have hmU := ansMode_le (w := w) hE ⟨sq, oU, lU, dU, rfl, hlU, hdU, hbU'⟩
    have hmV := ansMode_le (w := w) hE ⟨sv, oV, lV, dV, rfl, hlV, hdV, hbV'⟩
    obtain ⟨s3, g3, eff3, v3, f3⟩ := jLabs_good (x := x) hw s2 (H := H) (SP := SP) (LB := LB)
      (by rw [q2 _ (by decide), eH]) (by rw [q2 _ (by decide), eSP])
      (by rw [q2 _ (by decide), eLB]) e2U e2m v2 (by rw [m2, e1E]) hmU hmV hH hSP
      (by have := hbU rfl; simpa [aOff] using this) (by have := hbV rfl; simpa [aOff] using this)
      (by rw [q2 _ (by decide)]; exact hV4) (by rw [q2 _ (by decide)]; exact hm)
    have ee : EE s s2 [] := EE.of_frame (by rw [k2, k1]; simp +decide)
      (by rw [q2 _ (by decide)]) (by rw [p2, p1]) (by rw [o2, o1])
    refine ⟨s3, (CStm.Good.iteT hF (by simp [rv, Ex.eval, eT]) (g1.seq (g2.seq g3))).mono ?_,
      ?_, ?_, ?_, ?_, v3, ?_⟩
    · simp only [condCost, rv, Ex.size]; nlinarith
    · have := ee.trans eff3.ee
      simpa [aOff] using this
    · rw [eff3.stk_ne (by decide), k2]; simp +decide
    · rw [eff3.stk_ne (by decide), k2, k1]; simp +decide
    · intro q h1 h2 h3
      rw [eff3.stk_ne h1, k2, k1]
      simp [Function.update_of_ne h2, Function.update_of_ne h3]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [f3 r (by simp [labW]; tauto)]
      exact q2 r (by simp; tauto)

set_option maxHeartbeats 4000000 in
lemma c1Lnk_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {T H LT LB : ℕ}
    (AW rest : List ℕ) (eT : s.env r4Tn = T) (eH : s.env r4H = H) (e1 : s.env rc1 = LT)
    (eLB : s.env rLB = LB) (hE : s.env r4Eps ≤ 1)
    (hA : s.stk qAns = AW ++ rest) (hW : AnsOK w AW)
    (hH : H + 4 * T + 2 < 2 ^ w) (hLT : LT + 2 < 2 ^ w) (hbW : LB + aOff AW + 2 < 2 ^ w)
    (hV4 : s.env r4V < 2 ^ w) (hm : s.env r4M + 4 < 2 ^ w) :
    ∃ s', Good x w c1Lnk s s' (200 * Ex.nodeCost w) ∧
      EE s s' (lnkL (H + 4 * T) LT LB (aOff AW) (ansMode (s.env r4Eps) AW)) ∧
      s'.stk qAns = rest ∧ s'.stk qA2 = AW.reverse ++ s.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qAns → q ≠ qA2 → s'.stk q = s.stk q) ∧ s'.env r4V < 2 ^ w ∧
      ∀ r, r ∉ [rc2, rc3, rc6, rc7, rc8, r4F, r4V, r4M] → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  obtain ⟨sq, o, l, d, rfl, hl, hd, hb⟩ := hW
  obtain ⟨s1, g1, k1, v1, m1, mm1, p1, o1, f1⟩ := pAns_good (x := x) hw (o := rc2) (m := rc3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s (rest := rest) hA hb hl hd hE
  have q1 : ∀ r, r ∉ [rc2, rc3, rc6, rc7, rc8] → s1.env r = s.env r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact f1 r hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2 hr.1 hr.2.1
  obtain ⟨s2, g2, eff2, v2, f2⟩ := lLabs_good (x := x) hw s1 (H := H) (T := T) (LT := LT)
    (LB := LB) (by rw [q1 _ (by decide), eH]) (by rw [q1 _ (by decide), eT])
    (by rw [q1 _ (by decide), e1]) (by rw [q1 _ (by decide), eLB]) v1 m1 (by rw [← m1]; exact mm1) hH hLT
    (by simpa [aOff] using hbW) (by rw [q1 _ (by decide)]; exact hV4)
    (by rw [q1 _ (by decide)]; exact hm)
  have ee : EE s s1 [] := EE.of_frame (by rw [k1]; simp +decide) (by rw [q1 _ (by decide)])
    p1 o1
  refine ⟨s2, (g1.seq g2).mono (by nlinarith), ?_, ?_, ?_, ?_, v2, ?_⟩
  · have := ee.trans eff2.ee
    simpa [aOff] using this
  · rw [eff2.stk_ne (by decide), k1]; simp +decide
  · rw [eff2.stk_ne (by decide), k1]; simp +decide
  · intro q h1 h2 h3
    rw [eff2.stk_ne h1, k1]
    simp [Function.update_of_ne h2, Function.update_of_ne h3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f2 r (by simp [labW]; tauto)]
    exact q1 r (by simp; tauto)

/-! ## Advancing -/

def p4Adv1 : CStm CR CQ :=
  .seq (.set r4H (.add (rv r4H) (.add (.const 2) (.add (rv r4Tn) (.add (rv r4Tn)
      (.add (rv r4Tn) (rv r4Tn)))))))
    (.seq (.set r4SP (.add (rv r4SP) (.const 2))) (.set r4K (.add (rv r4K) (.const 1))))

lemma p4Adv1_good {w : ℕ} {x : List Bool} (s : NSt CR CQ) {H T SP K : ℕ}
    (eH : s.env r4H = H) (eT : s.env r4Tn = T) (eSP : s.env r4SP = SP) (eK : s.env r4K = K)
    (hH : H + 2 + 4 * T < 2 ^ w) (hSP : SP + 2 < 2 ^ w) (hK : K + 1 < 2 ^ w) :
    Good x w p4Adv1 s (((s.set r4H (H + 2 + 4 * T)).set r4SP (SP + 2)).set r4K (K + 1))
      (30 * Ex.nodeCost w) := by
  have hN := CStm.nodeCost_ge w
  have g1 := CStm.Good.set (x := x) (w := w) (st := s) (r := r4H)
    (e := .add (rv r4H) (.add (.const 2) (.add (rv r4Tn) (.add (rv r4Tn)
      (.add (rv r4Tn) (rv r4Tn)))))) (by simp only [Ex.Fits, rv, Ex.eval, eH, eT]; omega)
  have ev1 : (Ex.add (rv r4H) (.add (.const 2) (.add (rv r4Tn) (.add (rv r4Tn)
      (.add (rv r4Tn) (rv r4Tn))))) : Ex CR).eval s.env = H + 2 + 4 * T := by
    simp only [Ex.eval, rv, eH, eT]; ring
  rw [ev1] at g1
  have g2 := CStm.Good.set (x := x) (w := w) (st := s.set r4H (H + 2 + 4 * T)) (r := r4SP)
    (e := .add (rv r4SP) (.const 2)) (by simp +decide [Ex.Fits, rv, Ex.eval, eSP]; omega)
  have ev2 : (Ex.add (rv r4SP) (.const 2) : Ex CR).eval (s.set r4H (H + 2 + 4 * T)).env =
      SP + 2 := by simp +decide [Ex.eval, rv, eSP]
  rw [ev2] at g2
  have g3 := CStm.Good.set (x := x) (w := w)
    (st := (s.set r4H (H + 2 + 4 * T)).set r4SP (SP + 2)) (r := r4K)
    (e := .add (rv r4K) (.const 1)) (by
      have : ((s.set r4H (H + 2 + 4 * T)).set r4SP (SP + 2)).env r4K = K := by
        simp only [NSt.set_env]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), eK]
      simp only [Ex.Fits, rv, Ex.eval, this]; omega)
  have ev3 : (Ex.add (rv r4K) (.const 1) : Ex CR).eval
      ((s.set r4H (H + 2 + 4 * T)).set r4SP (SP + 2)).env = K + 1 := by
    simp +decide [Ex.eval, rv, eK]
  rw [ev3] at g3
  exact (g1.seq (g2.seq g3)).mono (by simp only [Ex.size, rv]; omega)

end Lax119563Proofs.Compiler

end Compiler_P4SchC1b

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchC1c` -/

section Compiler_P4SchC1c

/-!
# Pass `P4`, schema part: one column of section 1 (`p4C1_good`)

Reads the column `i, b₀ … b_{ℓ-1}` from the input, pushes its rank codes (`codesC`, then the
terminator `0`) on `qRk`, pops its answers (ternary: `U, V, W`; binary: `V`) and pushes the
junction and link edges (`col1E`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- The edge stack and count of `st'` are those of `st` with `Es` pushed. -/
def EM (st st' : NSt CR CQ) (Es : List (ℕ × ℕ)) : Prop :=
  st'.stk q4E = pairsRev Es ++ st.stk q4E ∧ st'.env r4M = st.env r4M + Es.length

lemma EM.trans {st s₁ s₂ : NSt CR CQ} {E₁ E₂ : List (ℕ × ℕ)} (h₁ : EM st s₁ E₁)
    (h₂ : EM s₁ s₂ E₂) : EM st s₂ (E₁ ++ E₂) := by
  obtain ⟨a1, b1⟩ := h₁
  obtain ⟨a2, b2⟩ := h₂
  refine ⟨?_, ?_⟩
  · rw [a2, a1, pairsRev_append]; simp
  · rw [b2, b1, List.length_append]; ring

lemma EE.em {st st' : NSt CR CQ} {Es : List (ℕ × ℕ)} (h : EE st st' Es) : EM st st' Es :=
  ⟨h.1, h.2.1⟩

lemma EM.of_frame {st st' : NSt CR CQ} (hs : st'.stk q4E = st.stk q4E)
    (hm : st'.env r4M = st.env r4M) : EM st st' [] := ⟨by simp [pairsRev, hs], by simp [hm]⟩

/-- One column of section 1. -/
def p4C1 : CStm CR CQ :=
  .seq p4Hd (.seq p4Blk (.seq p4Bits (.seq p4LT (.seq c1Jun (.seq c1Lnk p4Adv1)))))

/-- The rank codes of a column. -/
def codesC (k BR d i : ℕ) (os bs : List ℕ) : List ℕ :=
  blkCodes k BR d i ++ (chkRk os bs BR).map rcode

/-- The junction and link edges of a column (numbers). -/
def col1E (T H SP LT LB eps : ℕ) (AU AV AW : List ℕ) : List (ℕ × ℕ) :=
  (if T = 1 then junL H SP LB (aOff AU) (ansMode eps AU) (aOff AV) (ansMode eps AV) else []) ++
    lnkL (H + 4 * T) LT LB (aOff AW) (ansMode eps AW)

/-- The answer words consumed by a column in section 1. -/
def ans1 (T : ℕ) (AU AV AW : List ℕ) : List ℕ := (if T = 1 then AU ++ AV else []) ++ AW

/-- Registers written by a column of section 1. -/
def c1W : List (Fin CR) :=
  [rc1, rc2, rc3, rc4, rc5, rc6, rc7, rc8, rP, rT, r4Dist, r4Prev, r4TP, r4H, r4SP, r4K, r4F,
    r4V, r4M]

set_option maxHeartbeats 16000000 in
/-- **One column of section 1.** -/
lemma p4C1_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ)
    {i k BR K D P H SP TP T LB : ℕ} (bs os : List ℕ) (rest : List Bool) (AU AV AW ansRest : List ℕ)
    (hx : x.drop s.pos = encodeNats (i :: bs) ++ rest) (hi : (Nat.bits i).length < w)
    (hbs : ∀ b ∈ bs, b ≤ 1) (hos : ∀ o ∈ os, o ≤ 1) (hl : os.length = bs.length)
    (eL : s.env rL = bs.length) (hF : s.stk qOrsF = os) (hB : s.stk qOrsB = [])
    (hA : s.stk qAns = ans1 T AU AV AW ++ ansRest)
    (hU : T = 1 → AnsOK w AU) (hV : T = 1 → AnsOK w AV) (hW : AnsOK w AW)
    (ek : s.env rKk = k) (eBR : s.env r4BR = BR) (eK : s.env r4K = K) (eD : s.env r4Dist = D)
    (eP : s.env r4Prev = P) (eH : s.env r4H = H) (eSP : s.env r4SP = SP) (eTP : s.env r4TP = TP)
    (eT : s.env r4Tn = T) (hT : T ≤ 1) (eLB : s.env rLB = LB) (hE : s.env r4Eps ≤ 1)
    (hV4 : s.env r4V < 2 ^ w) (hbd : s.Bdd w) (hpos : s.pos ≤ x.length)
    (hk : 2 ≤ k) (hik : i < k)
    (B : ℕ) (hBw : B < 2 ^ w)
    (hb1 : 2 * k + 2 ≤ B) (hb2 : 2 * (D + 1) + 2 ≤ B) (hb3 : BR + 1 ≤ B) (hb4 : K + 2 ≤ B)
    (hb5 : P ≤ B) (hb6 : H + 8 ≤ B) (hb7 : SP + 4 ≤ B)
    (hb8 : TP + 2 * ((k + 1) * (codesC k BR (dist1 K D P i) i os bs).length) + 2 ≤ B)
    (hb9 : 2 * (BR + bs.length) + k + 2 ≤ B)
    (hbU : T = 1 → LB + aOff AU + 2 ≤ B) (hbV : T = 1 → LB + aOff AV + 2 ≤ B)
    (hbW : LB + aOff AW + 2 ≤ B) (hm : s.env r4M + 16 ≤ B) :
    ∃ s', Good x w p4C1 s s' (200 * ((encodeNats (i :: bs)).length + bs.length +
        (k + 2) * ((codesC k BR (dist1 K D P i) i os bs).length + 1) + 10) * Ex.nodeCost w) ∧
      EM s s' (col1E T H SP (TP + 2 * ((k + 1) * (codesC k BR (dist1 K D P i) i os bs).length - 1))
        LB (s.env r4Eps) AU AV AW) ∧
      s'.stk qRk = (codesC k BR (dist1 K D P i) i os bs ++ [0]).reverse ++ s.stk qRk ∧
      s'.stk qAns = ansRest ∧ s'.stk qA2 = (ans1 T AU AV AW).reverse ++ s.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qRk → q ≠ qAns → q ≠ qA2 → s'.stk q = s.stk q) ∧
      s'.env r4Dist = dist1 K D P i ∧ s'.env r4Prev = i ∧
      s'.env r4TP = TP + 2 * ((k + 1) * (codesC k BR (dist1 K D P i) i os bs).length) ∧
      s'.env r4H = H + 2 + 4 * T ∧ s'.env r4SP = SP + 2 ∧ s'.env r4K = K + 1 ∧
      s'.env r4V < 2 ^ w ∧ s'.Bdd w ∧ s'.pos = s.pos + (encodeNats (i :: bs)).length ∧
      s'.out = s.out ∧ ∀ r, r ∉ c1W → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  set d := dist1 K D P i with hd
  have hdD : d ≤ D + 1 := by simp only [hd, dist1]; split_ifs <;> omega
  -- the block
  have hx1 : x.drop s.pos = encodeNat i ++ (encodeNats bs ++ rest) := by
    rw [hx, encNats_cons, List.append_assoc]
  obtain ⟨s1, g1, e11, e1D, e1P, p1, k1, o1, f1⟩ := p4Hd_good (x := x) hw s (rest :=
    encodeNats bs ++ rest) hx1 hi eK eD eP (by omega) (by omega) (by omega)
  have q1 : ∀ r, r ∉ [rc1, rP, rT, r4Dist, r4Prev] → s1.env r = s.env r := f1
  have b1 := g1.bdd hw hbd hpos
  -- block ranks
  obtain ⟨s2, g2, k2, e22, p2, o2, f2⟩ := p4Blk_good (x := x) hw s1 (k := k) (BR := BR) (d := d)
    (i := i) e11 (by rw [q1 _ (by decide), ek]) (by rw [q1 _ (by decide), eBR]) e1D (by omega)
    (by omega) (by omega) (by omega) (by omega)
  have b2 := g2.bdd hw b1.1 b1.2
  have hblk : (blkCodes k BR d i).length ≤ k := by
    unfold blkCodes; split_ifs <;> simp <;> omega
  have hblk1 := length_blkCodes_pos k BR d i hk
  -- bits
  have hx2 : x.drop s2.pos = encodeNats bs ++ rest := by
    rw [p2, p1, drop_add, hx1, List.drop_left]
  obtain ⟨s3, g3, k3, e32, p3, o3, f3⟩ := p4Bits_good (x := x) hw os bs s2 (BR := BR)
    (n0 := (blkCodes k BR d i).length) hl hbs hos rest hx2
    (by rw [f2 _ (by decide) (by decide), q1 _ (by decide), eBR]) e22
    (by rw [f2 _ (by decide) (by decide), q1 _ (by decide), eL])
    (by rw [k2, Function.update_of_ne (by decide), k1, hF])
    (by rw [k2, Function.update_of_ne (by decide), k1, hB]) b2.1 b2.2 (by omega)
  have b3 := g3.bdd hw b2.1 b2.2
  set n := (codesC k BR d i os bs).length with hn
  have hn' : n = (blkCodes k BR d i).length + (chkRk os bs BR).length := by
    simp [hn, codesC]
  have hcl := length_chkRk_le os bs BR
  have hnk : n ≤ k + bs.length := by omega
  -- last track
  have q3 : ∀ r, r ∉ [rc1, rc2, rc3, rc4, rc5, rP, rT, r4Dist, r4Prev] → s3.env r = s.env r := by
    intro r hr
    rw [f3 r (by simp [bitW] at hr ⊢; tauto), f2 r (by simp at hr; tauto) (by simp at hr; tauto)]
    exact q1 r (by simp at hr ⊢; tauto)
  have hkn : (k + 1) * n ≤ (k + 1) * (k + bs.length) := Nat.mul_le_mul_left _ hnk
  obtain ⟨s4, g4, e41, e4TP, k4, p4, o4, f4⟩ := p4LT_good (x := x) hw s3 (k := k) (n := n)
    (TP := TP) (by rw [e32, hn']) (by rw [q3 _ (by decide), ek]) (by rw [q3 _ (by decide), eTP])
    (by omega) (by omega)
  have b4 := g4.bdd hw b3.1 b3.2
  have q4 : ∀ r, r ∉ [rc1, rc2, rc3, rc4, rc5, rP, rT, r4Dist, r4Prev, r4TP] →
      s4.env r = s.env r := by
    intro r hr
    rw [f4 r (by simp at hr ⊢; tauto)]
    exact q3 r (by simp at hr ⊢; tauto)
  -- junction
  have hA4 : s4.stk qAns = (if T = 1 then AU ++ AV else []) ++ (AW ++ ansRest) := by
    rw [k4, k3, Function.update_of_ne (by decide), k2, Function.update_of_ne (by decide), k1, hA,
      ans1, List.append_assoc]
  obtain ⟨s5, g5, ee5, k5A, k5A2, k5o, v5, f5⟩ := c1Jun_good (x := x) hw s4 (T := T) (H := H)
    (SP := SP) (LB := LB) AU AV (AW ++ ansRest) (by rw [q4 _ (by decide), eT]) hT
    (by rw [q4 _ (by decide), eH]) (by rw [q4 _ (by decide), eSP]) (by rw [q4 _ (by decide), eLB])
    (by rw [q4 _ (by decide)]; exact hE) hA4 hU hV (by omega) (by omega)
    (fun h => by have := hbU h; omega) (fun h => by have := hbV h; omega)
    (by rw [f4 _ (by decide), f3 _ (by decide), f2 _ (by decide) (by decide),
      q1 _ (by decide)]; exact hV4)
    (by rw [q4 _ (by decide)]; omega)
  have q5 : ∀ r, r ∉ [rc1, rc2, rc3, rc4, rc5, rc6, rc7, rc8, rP, rT, r4Dist, r4Prev, r4TP,
      r4F, r4V, r4M] → s5.env r = s.env r := by
    intro r hr
    rw [f5 r (by simp at hr ⊢; tauto)]
    exact q4 r (by simp at hr ⊢; tauto)
  have e5E : s5.env r4Eps = s.env r4Eps := q5 _ (by decide)
  have e4E : s4.env r4Eps = s.env r4Eps := q4 _ (by decide)
  have e5M : s5.env r4M ≤ s.env r4M + 12 := by
    rw [ee5.2.1, q4 _ (by decide)]
    split_ifs
    · have := length_junL H SP LB (aOff AU) (ansMode (s4.env r4Eps) AU) (aOff AV)
        (ansMode (s4.env r4Eps) AV)
      omega
    · simp
  have e51 : s5.env rc1 = TP + 2 * ((k + 1) * n - 1) := by rw [f5 _ (by decide), e41]
  obtain ⟨s6, g6, ee6, k6A, k6A2, k6o, v6, f6⟩ := c1Lnk_good (x := x) hw s5 (T := T) (H := H)
    (LT := TP + 2 * ((k + 1) * n - 1)) (LB := LB) AW ansRest
    (by rw [q5 _ (by decide), eT]) (by rw [q5 _ (by decide), eH]) e51
    (by rw [q5 _ (by decide), eLB]) (by rw [e5E]; exact hE) k5A hW (by omega) (by omega)
    (by omega) v5 (by omega)
  have q6 : ∀ r, r ∉ [rc1, rc2, rc3, rc4, rc5, rc6, rc7, rc8, rP, rT, r4Dist, r4Prev, r4TP,
      r4F, r4V, r4M] → s6.env r = s.env r := by
    intro r hr
    rw [f6 r (by simp at hr ⊢; tauto)]
    exact q5 r hr
  have g7 := p4Adv1_good (x := x) (w := w) s6 (H := H) (T := T) (SP := SP) (K := K)
    (by rw [q6 _ (by decide), eH]) (by rw [q6 _ (by decide), eT]) (by rw [q6 _ (by decide), eSP])
    (by rw [q6 _ (by decide), eK]) (by omega) (by omega) (by omega)
  set s7 := ((s6.set r4H (H + 2 + 4 * T)).set r4SP (SP + 2)).set r4K (K + 1)
  have b7 := (g4.seq (g5.seq (g6.seq g7))).bdd hw b3.1 b3.2
  have q76 : ∀ r, r ≠ r4H → r ≠ r4SP → r ≠ r4K → s7.env r = s6.env r := by
    intro r h1 h2 h3; simp [s7, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3]
  have e6D : s6.env r4Dist = d := by
    rw [f6 _ (by decide), f5 _ (by decide), f4 _ (by decide), f3 _ (by decide),
      f2 _ (by decide) (by decide), e1D]
  refine ⟨s7, (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq g7)))))).mono ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, b7.1, ?_, ?_, ?_⟩
  · -- cost
    have hl1 : (encodeNats (i :: bs)).length = (encodeNat i).length + (encodeNats bs).length := by
      rw [encNats_cons, List.length_append]
    have hkn2 : (k + 2) * (n + 1) ≥ (k + 2) := by nlinarith
    rw [hl1]
    nlinarith
  · -- edges
    have e04 : EM s s4 [] := EM.of_frame (by rw [k4, k3, k2, k1]; simp +decide)
      (by rw [q4 _ (by decide)])
    have e67 : EM s6 s7 [] := EM.of_frame (by simp [s7]) (q76 _ (by decide) (by decide) (by decide))
    have := ((e04.trans ee5.em).trans ee6.em).trans e67
    rw [e4E, e5E] at this
    simpa [col1E] using this
  · simp only [s7, NSt.set_stk]
    rw [k6o _ (by decide) (by decide) (by decide), k5o _ (by decide) (by decide) (by decide), k4,
      k3, k2, k1]
    simp [codesC]
  · simp only [s7, NSt.set_stk]; exact k6A
  · simp only [s7, NSt.set_stk]
    rw [k6A2, k5A2, k4, k3, Function.update_of_ne (by decide), k2, Function.update_of_ne (by decide),
      k1, ans1]
    split_ifs <;> simp
  · intro q h1 h2 h3 h4
    simp only [s7, NSt.set_stk]
    rw [k6o q h1 h3 h4, k5o q h1 h3 h4, k4, k3, Function.update_of_ne h2, k2,
      Function.update_of_ne h2, k1]
  · rw [q76 _ (by decide) (by decide) (by decide)]; exact e6D
  · rw [q76 _ (by decide) (by decide) (by decide), f6 _ (by decide), f5 _ (by decide),
      f4 _ (by decide), f3 _ (by decide), f2 _ (by decide) (by decide), e1P]
  · rw [q76 _ (by decide) (by decide) (by decide), f6 _ (by decide), f5 _ (by decide), e4TP]
  · simp +decide [s7]
  · simp +decide [s7]
  · simp +decide [s7]
  · rw [q76 _ (by decide) (by decide) (by decide)]; exact v6
  · simp only [s7]
    show s6.pos = _
    rw [ee6.2.2.1, ee5.2.2.1, p4, p3, p2, p1, encNats_cons, List.length_append]; ring
  · simp only [s7]
    show s6.out = _
    rw [ee6.2.2.2, ee5.2.2.2, o4, o3, o2, o1]
  · intro r hr
    simp only [c1W, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [q76 r (by tauto) (by tauto) (by tauto)]
    exact q6 r (by simp; tauto)

end Lax119563Proofs.Compiler

end Compiler_P4SchC1c
