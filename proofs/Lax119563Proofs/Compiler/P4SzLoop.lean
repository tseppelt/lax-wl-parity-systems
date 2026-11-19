import Lax119563Proofs.Compiler.P4SzRead
import Lax119563Proofs.Compiler.PSchLoop

/-!
# Pass `P4` (program): the schema-size scan

`p4SzS` (run at `schPos I` with the records `(schRecsUpTo I E).reverse` on `qSch`): moves the
records forward onto `qT`, and per schema reads its description (`p4SRead`), moves its
record back onto `qSch` (`p4SRec`) and pushes its class sizes (`p4SPush`); finally the
sizes are moved onto `qSzB` (**`p4SzS_good`**: `qSzB := schAll ++ qSzB`, `qSch` restored,
`rNt += Σ schAll`, cursor at `H`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The class sizes of the first `j` schemas. -/
noncomputable def schSzUpTo (j : ℕ) : List ℕ :=
  ((List.finRange I.schemas.length).take j).flatMap (schSizes I)

/-- The records of the schemas from `j` on. -/
noncomputable def schRecsFrom (j : ℕ) : List ℕ :=
  ((List.finRange I.schemas.length).drop j).flatMap (schRec I)

/-- The class sizes of all schemas. -/
noncomputable def schAll : List ℕ := (List.finRange I.schemas.length).flatMap (schSizes I)

lemma schSzUpTo_succ {j : ℕ} (hj : j < I.schemas.length) :
    schSzUpTo I (j + 1) = schSzUpTo I j ++ schSizes I ⟨j, hj⟩ := by
  rw [schSzUpTo, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp (config := { decide := true }) [schSzUpTo]

lemma schSzUpTo_all : schSzUpTo I I.schemas.length = schAll I := by
  rw [schSzUpTo, List.take_of_length_le (by simp), schAll]

lemma schSzUpTo_sum_le (j : ℕ) : (schSzUpTo I j).sum ≤ (schAll I).sum := by
  have : schAll I = schSzUpTo I j ++
      ((List.finRange I.schemas.length).drop j).flatMap (schSizes I) := by
    rw [schAll, schSzUpTo, ← List.flatMap_append, List.take_append_drop]
  rw [this, List.sum_append]; omega

lemma schRecsFrom_cons {j : ℕ} (hj : j < I.schemas.length) :
    schRecsFrom I j = schRec I ⟨j, hj⟩ ++ schRecsFrom I (j + 1) := by
  rw [schRecsFrom, List.drop_eq_getElem_cons (by simpa using hj), List.flatMap_cons, schRecsFrom]
  simp

lemma schRecsFrom_sub (j : ℕ) : ∀ v ∈ schRecsFrom I j, v ∈ schRecsUpTo I I.schemas.length := by
  intro v hv
  simp only [schRecsFrom, List.mem_flatMap] at hv
  obtain ⟨e, he, hv⟩ := hv
  simp only [schRecsUpTo, List.mem_flatMap]
  exact ⟨e, by rw [List.take_of_length_le (by simp)]; exact List.mem_finRange e, hv⟩

lemma schRecsFrom_zero : schRecsFrom I 0 = schRecsUpTo I I.schemas.length := by
  rw [schRecsFrom, schRecsUpTo, List.drop_zero, List.take_of_length_le (by simp)]

lemma schRecsFrom_all : schRecsFrom I I.schemas.length = [] := by
  rw [schRecsFrom, List.drop_of_length_le (by simp)]; rfl

lemma schRec_split (e : Fin I.schemas.length) :
    schRec I e = (orsL (coordList (dom I e)) ++ [blkRows (coordList (dom I e))]) ++
      nEnt I e :: (coefSteps I e).length :: [] := by
  simp (config := { decide := true }) [schRec]

/-! ## The loop -/

/-- The body of the schema-size loop. -/
def p4SBody : CStm CR CQ :=
  .seq p4SRead (.seq p4SRec (.seq p4SPush (.set rJ (.add (rv rJ) (.const 1)))))

/-- The schema-size loop. -/
def p4SLoop : CStm CR CQ := .loop (.lt (rv rJ) (rv rE)) p4SBody

/-- The loop invariant (`st`: the state before the loop). -/
def p4SInv (st s : NSt CR CQ) : Prop :=
  s.env rE = I.schemas.length ∧ s.env rL1 = ℓ + 1 ∧ s.env rKk = k ∧
    s.env rJ ≤ I.schemas.length ∧ s.pos = schAt I (s.env rJ) ∧
    s.env rNt = st.env rNt + (schSzUpTo I (s.env rJ)).sum ∧
    s.stk = Function.update (Function.update (Function.update st.stk qT
      (schRecsFrom I (s.env rJ))) qSch (schRecsUpTo I (s.env rJ)).reverse) qSzA
      ((schSzUpTo I (s.env rJ)).reverse ++ st.stk qSzA) ∧
    s.out = st.out

/-- The potential of the loop. -/
noncomputable def p4SPot (st s : NSt CR CQ) : ℕ :=
  (H I - s.pos) + (st.env rNt + (schAll I).sum - s.env rNt)

lemma p4SBody_arith {N U P l d nE nC Z : ℕ} (hU : U ≤ N) (hl : l ≤ P) (hd : d ≤ Z)
    (hE : nE ≤ Z) (hC : nC ≤ Z) :
    150 * N * P + 200 * N + ((l + 1 + 5) * (12 * N) + ((2 * d + 2 * nE + nC + 10) * (30 * N) +
      (3 * N + U))) ≤ 200 * N * (P + Z) + 700 * N := by
  nlinarith

lemma p4SBody_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hk : 1 ≤ k)
    (st s : NSt CR CQ) (hrec : ∀ v ∈ schRecsUpTo I I.schemas.length, v < 2 ^ w)
    (hT : st.env rNt + (schAll I).sum + 8 < 2 ^ w)
    (hI : p4SInv I st s) (hc : (Ex.lt (rv rJ) (rv rE)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p4SBody s s'
        (200 * Ex.nodeCost w * (p4SPot I st s - p4SPot I st s') + 700 * Ex.nodeCost w) ∧
      p4SInv I st s' ∧ I.schemas.length - s'.env rJ < I.schemas.length - s.env rJ ∧
      p4SPot I st s' ≤ p4SPot I st s := by
  have hU := CStm.nodeCost_ge w
  obtain ⟨hE, hL1, hK, hjE, hpos, hnt, hstk, hout⟩ := hI
  have hlt : s.env rJ < I.schemas.length := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hE]; rw [if_neg h]
  set j := s.env rJ with hjdef
  set e : Fin I.schemas.length := ⟨j, hlt⟩
  set D := coordList (dom I e)
  -- reading
  obtain ⟨sA, rA', hAp, hAs, hAo, hAA, hAD⟩ := p4SRead_good I hw hH hk s hlt hpos hL1 hK
  have eA : ∀ r, wReg r p4SRead = false → sA.env r = s.env r := fun r h => rA'.env_of h
  -- the record
  have hTs : sA.stk qT = (orsL D ++ [blkRows D]) ++ nEnt I e :: (coefSteps I e).length ::
      schRecsFrom I (j + 1) := by
    rw [hAs, hstk, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, schRecsFrom_cons I hlt, schRec_split]
    simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl
  have hmem : ∀ v ∈ schRecsFrom I j, v < 2 ^ w := fun v hv => hrec v (schRecsFrom_sub I j v hv)
  rw [schRecsFrom_cons I hlt, schRec_split] at hmem
  obtain ⟨sB, rB, hBs, hBe, hBc, hBp, hBo, hBf⟩ := p4SRec_good (x := encodeSystem I) (w := w)
    sA (orsL D ++ [blkRows D]) (schRecsFrom I (j + 1)) (nEnt I e) (coefSteps I e).length hTs
    (by rw [eA _ (by decide), hL1]; simp (config := { decide := true }) [length_orsL])
    (fun v hv => hmem v (List.mem_append_left _ (List.mem_append_left _ hv)))
    (hmem _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..))))
    (hmem _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    (by
      have h1 := length_schemaDescription_ge I hk (sch I e)
      have h2 := schD_length_le I e
      simp only [schD] at h2
      simp only [List.length_append, length_orsL, List.length_singleton]; omega)
  -- the sizes
  have hszE : schSizes I e = szL (Matrix.isTern (sch I e)) D.length (nEnt I e) (coefSteps I e).length :=
    schSizes_eq_szL I e
  have hsumle := schSzUpTo_sum_le I (j + 1)
  rw [schSzUpTo_succ I hlt, List.sum_append] at hsumle
  replace hsumle : (schSzUpTo I j).sum + (schSizes I e).sum ≤ (schAll I).sum := hsumle
  obtain ⟨sC, rC', hCs, hCn, hCp, hCo⟩ := p4SPush_good (x := encodeSystem I) hw sB
    (Matrix.isTern (sch I e)) (d := D.length) (nE := nEnt I e) (nC := (coefSteps I e).length)
    (A := st.env rNt + (schSzUpTo I j).sum)
    (by rw [hBf _ (by decide) (by decide) (by decide) (by decide), hAA]; rfl)
    (by rw [hBf _ (by decide) (by decide) (by decide) (by decide), hAD])
    hBe hBc
    (by rw [hBf _ (by decide) (by decide) (by decide) (by decide), eA _ (by decide), hnt])
    (by rw [← hszE]; omega)
  have hCJ : sC.env rJ = j := by
    rw [rC'.env_of (by decide), hBf _ (by decide) (by decide) (by decide) (by decide),
      eA _ (by decide)]
  have rD' := Good.set (x := encodeSystem I) (w := w) (st := sC) (r := rJ)
    (e := .add (rv rJ) (.const 1)) (by
      have := E_le I
      simp only [Ex.Fits, Ex.eval, rv, hCJ]; omega)
  set s' := sC.set rJ ((Ex.add (rv rJ) (.const 1) : Ex CR).eval sC.env)
  have e'J : s'.env rJ = j + 1 := by simp (config := { decide := true }) [s', Ex.eval, rv, hCJ]
  have e' : ∀ r, r ≠ rJ → wReg r p4SPush = false → r ≠ rI → r ≠ rT → r ≠ rNe → r ≠ rNc →
      wReg r p4SRead = false → s'.env r = s.env r := fun r h0 h1 h2 h3 h4 h5 h6 => by
    simp only [s', NSt.set_env, Function.update_of_ne h0]
    rw [rC'.env_of h1, hBf r h2 h3 h4 h5, eA r h6]
  have hp' : s'.pos = s.pos + (encodeNats (schD I e)).length := by
    simp only [s', NSt.set_pos]; rw [hCp, hBp, hAp]
  have hn' : s'.env rNt = st.env rNt + (schSzUpTo I (j + 1)).sum := by
    simp only [s', NSt.set_env, Function.update_of_ne (show rNt ≠ rJ by decide)]
    rw [hCn, schSzUpTo_succ I hlt, List.sum_append, hszE]; ring
  have hposH : s.pos + (encodeNats (schD I e)).length ≤ H I := by
    have := schAt_le I (j + 1); rw [schAt_succ I hlt] at this; rw [hpos]; exact this
  have hZ : (schSizes I e).sum = (szL (Matrix.isTern (sch I e)) D.length (nEnt I e)
      (coefSteps I e).length).sum := by rw [hszE]
  have hpot : p4SPot I st s - p4SPot I st s' =
      (encodeNats (schD I e)).length + (szL (Matrix.isTern (sch I e)) D.length (nEnt I e)
        (coefSteps I e).length).sum := by
    unfold p4SPot; rw [hp', hn', hnt, schSzUpTo_succ I hlt, List.sum_append, hszE]; omega
  have hℓ : ℓ ≤ (encodeNats (schD I e)).length :=
    (length_schemaDescription_ge I hk (sch I e)).trans (length_le_encodeNats _)
  have hsz := szL_sum (Matrix.isTern (sch I e)) D.length (nEnt I e) (coefSteps I e).length
  refine ⟨s', (rA'.seq (rB.seq (rC'.seq rD'))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, by rw [e'J]; exact hn', ?_, ?_⟩, ?_, ?_⟩
  · rw [hpot]
    have hR : (orsL D ++ [blkRows D]).length = ℓ + 1 := by simp [length_orsL]
    rw [hR]
    have hdZ : D.length ≤ (szL (Matrix.isTern (sch I e)) D.length (nEnt I e)
        (coefSteps I e).length).sum := by rw [hsz]; split_ifs <;> omega
    have hEZ : nEnt I e ≤ (szL (Matrix.isTern (sch I e)) D.length (nEnt I e)
        (coefSteps I e).length).sum := by rw [hsz]; omega
    have hCZ : (coefSteps I e).length ≤ (szL (Matrix.isTern (sch I e)) D.length (nEnt I e)
        (coefSteps I e).length).sum := by rw [hsz]; omega
    have := p4SBody_arith (N := Ex.nodeCost w) (U := unitCost w)
      (P := (encodeNats (schD I e)).length) (l := ℓ) hU (by omega) hdZ hEZ hCZ
    simp only [Ex.size, rv]
    linarith
  · rw [e' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hE]
  · rw [e' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hL1]
  · rw [e' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hK]
  · rw [e'J]; omega
  · rw [e'J, hp', hpos, schAt_succ I hlt]
  · rw [e'J]
    simp only [s', NSt.set_stk]
    rw [hCs, hBs, hAs, hstk, schSzUpTo_succ I hlt, schRecsUpTo_succ I hlt, ← hszE]
    funext q
    by_cases h1 : q = qSzA
    · subst h1; simp (config := { decide := true }); rfl
    by_cases h2 : q = qSch
    · subst h2; simp (config := { decide := true }) [Function.update_of_ne (show qSch ≠ qSzA by decide),
        Function.update_of_ne (show qSch ≠ qT by decide), schRec_split]
      exact ⟨rfl, rfl, rfl, rfl⟩
    by_cases h3 : q = qT
    · subst h3; simp (config := { decide := true }) [Function.update_of_ne (show qT ≠ qSzA by decide),
        Function.update_of_ne (show qT ≠ qSch by decide)]
    simp (config := { decide := true }) [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  · simp only [s', NSt.set_out]; rw [hCo, hBo, hAo, hout]
  · rw [e'J]; omega
  · have hZ' := hZ
    unfold p4SPot; rw [hp', hn', hnt, schSzUpTo_succ I hlt, List.sum_append]
    change _ + (_ - (_ + ((schSzUpTo I j).sum + (schSizes I e).sum))) ≤ _
    omega

end Lax119563Proofs.Compiler
