import Lax119563Proofs.Compiler.P4SchL1d
import Lax119563Proofs.Compiler.P4SchL2c
import Lax119563Proofs.Compiler.P4SzS

/-!
# Pass `P4`, schema part: the schema body, reading the header

* registers of the schema body: `r4NE` (`nEnt`), `r4NC` (`|coefSteps|`), `r4SuB` (sum base),
  `r4TrB` (track base); the schema base is kept in `r4SB`, the schema index in `rJ`;
* `p4Rd`: read the arity (→ `r4Tn`), skip the locations, read `|D|` (→ `r4D`)
  (**`p4Rd_good`**); `schD_len`: the length of a schema description by parts.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- `nEnt` of the current schema. -/
def r4NE : Fin CR := 14
/-- `|coefSteps|` of the current schema. -/
def r4NC : Fin CR := 15
/-- The sum base of the current schema. -/
def r4SuB : Fin CR := 38
/-- The track base of the current schema. -/
def r4TrB : Fin CR := 39

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The header of a schema description: arity, locations, `|D|`. -/
noncomputable def hdrL (e : Fin I.schemas.length) : ℕ :=
  (encodeNat (arity (sch I e))).length + (encodeNats (schLocs (sch I e))).length +
    (encodeNat (cL I e).length).length

/-- The permutation words of a schema. -/
noncomputable def permsL (e : Fin I.schemas.length) : List ℕ :=
  (schPerms (sch I e)).flatMap permDescription

lemma schD_split (e : Fin I.schemas.length) :
    schD I e = arity (sch I e) :: schLocs (sch I e) ++
      ((cL I e).length :: (cL I e).flatMap cdesc) ++ permsL I e := by
  rw [schD, schemaDescription_eq']; rfl

lemma schD_len (e : Fin I.schemas.length) :
    (encodeNats (schD I e)).length = hdrL I e + (encodeNats ((cL I e).flatMap cdesc)).length +
      (encodeNats (permsL I e)).length := by
  rw [schD_split]
  simp only [hdrL, List.cons_append, encNats_cons, List.append_assoc, encodeNats_append,
    List.length_append]
  ring

lemma length_permsL (e : Fin I.schemas.length) :
    (permsL I e).length = arity (sch I e) * (k * (ℓ + 1)) := by
  rw [permsL, length_perms]; ring

/-- Read the header of the schema at the cursor. -/
def p4Rd : CStm CR CQ :=
  .seq (rdNumS rc1 rP rT) (.seq (.set r4Tn (.lt (.const 2) (rv rc1)))
    (.seq (skipNumsS rc1 rc2 rT) (rdNumS r4D rP rT)))

lemma arity_eq (s : Schema k ℓ I.numLocations) :
    arity s = 2 + tnN (Matrix.isTern s) := by
  unfold arity tnN; split_ifs <;> rfl

set_option maxHeartbeats 4000000 in
lemma p4Rd_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (s : NSt CR CQ) {j : ℕ}
    (hj : j < I.schemas.length) (hpos : s.pos = schAt I j) :
    ∃ s', Good (encodeSystem I) w p4Rd s s' (100 * Ex.nodeCost w * (hdrL I ⟨j, hj⟩ + 1)) ∧
      s'.pos = s.pos + hdrL I ⟨j, hj⟩ ∧
      (encodeSystem I).drop s'.pos = encodeNats ((cL I ⟨j, hj⟩).flatMap cdesc) ++
        (encodeNats (permsL I ⟨j, hj⟩) ++ encodeNats (schsSuf I (j + 1))) ∧
      s'.stk = s.stk ∧ s'.out = s.out ∧ s'.env r4Tn = tnN (Matrix.isTern (sch I ⟨j, hj⟩)) ∧
      s'.env r4D = (cL I ⟨j, hj⟩).length ∧
      ∀ r, r ∉ [rc1, rc2, rP, rT, r4Tn, r4D] → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  have hDH := schD_le_H I ⟨j, hj⟩
  rw [schD_len] at hDH
  have hpH : s.pos + (encodeNats (schD I ⟨j, hj⟩)).length ≤ H I := by
    have := schAt_le I (j + 1); rw [schAt_succ I hj] at this; rw [hpos]; exact this
  rw [schD_len] at hpH
  unfold hdrL at hDH hpH
  set e : Fin I.schemas.length := ⟨j, hj⟩
  set sc := sch I e
  set a := arity sc
  set locs := schLocs sc
  set d := (cL I e).length
  set cs := (cL I e).flatMap cdesc
  set perms := permsL I e
  set rest := encodeNats (schsSuf I (j + 1))
  have hx : (encodeSystem I).drop s.pos = encodeNat a ++ (encodeNats locs ++ (encodeNat d ++
      (encodeNats cs ++ (encodeNats perms ++ rest)))) := by
    rw [hpos, drop_schAt, schsSuf_cons I hj, encodeNats_append, schD_split]
    simp only [List.cons_append, encNats_cons, List.append_assoc, encodeNats_append]; rfl
  have hla : locs.length = a := length_schLocs sc
  have ha23 : 2 ≤ a ∧ a ≤ 3 := by simp only [a, arity]; split_ifs <;> omega
  have hlo := length_le_encodeNats locs
  have hd1 := length_le_encodeNats cs
  have hdcs : d ≤ cs.length := by
    simp only [cs, d, List.length_flatMap, length_cdesc]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hdH : d ≤ H I := by omega
  -- reading the arity
  have r1 := rdNumS_good (Q := CQ) hw (r := rc1) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s a _ hx (bits_lt_of_le (by have := three_le_H I; omega) hH2)
  set s1 := rdNumFinal s rc1 rP rT a
  have e1A : s1.env rc1 = a := rdNumFinal_env_r (by decide) (by decide) a
  have r2 := Good.set (x := encodeSystem I) (w := w) (st := s1) (r := r4Tn)
    (e := .lt (.const 2) (rv rc1)) (by
      simp only [Ex.Fits, rv, e1A]; constructor <;> omega)
  set s2 := s1.set r4Tn ((Ex.lt (.const 2) (rv rc1) : Ex CR).eval s1.env)
  have e2T : s2.env r4Tn = tnN (Matrix.isTern sc) := by
    simp only [s2, NSt.set_env, Function.update_self, Ex.eval, rv, e1A, a, arity, tnN]
    split_ifs <;> omega
  have e2A : s2.env rc1 = a := by
    simp only [s2, NSt.set_env, Function.update_of_ne (show rc1 ≠ r4Tn by decide)]; exact e1A
  -- skipping the locations
  obtain ⟨s3, r3, h3s, h3p, h3o, h3f⟩ := skipNumsS_good (Q := CQ) hw (n := rc1) (i := rc2)
    (t := rT) (by decide) (by decide) (by decide) s2 locs _
    (by show (encodeSystem I).drop s1.pos = _
        simp only [s1, rdNumFinal_pos]; rw [← List.drop_drop, hx, List.drop_left])
    (by rw [e2A, hla]) (by have := e2A; have := hla; omega)
  -- reading `|D|`
  have r4 := rdNumS_good (Q := CQ) hw (r := r4D) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s3 d _ (by
      rw [h3p]; show (encodeSystem I).drop (s1.pos + _) = _
      simp only [s1, rdNumFinal_pos]
      rw [← List.drop_drop, ← List.drop_drop, hx, List.drop_left, List.drop_left])
    (bits_lt_of_le hdH hH2)
  set s4 := rdNumFinal s3 r4D rP rT d
  have hp4 : s4.pos = s.pos + hdrL I e := by
    simp only [s4, rdNumFinal_pos]; rw [h3p]; show s1.pos + _ + _ = _
    simp only [s1, rdNumFinal_pos, hdrL]; ring
  refine ⟨s4, (r1.seq (r2.seq (r3.seq r4))).mono ?_, hp4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Ex.size, rv]
    have hl2 : (encodeNats locs).length + locs.length ≤ 2 * (encodeNats locs).length := by omega
    unfold hdrL
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNat (arity (sch I e))).length = la at *
    generalize (encodeNats (schLocs (sch I e))).length = llo at *
    generalize (encodeNat (cL I e).length).length = ld at *
    nlinarith
  · have hh : hdrL I e = (encodeNat a ++ (encodeNats locs ++ encodeNat d)).length := by
      simp only [hdrL, List.length_append]; ring
    rw [hp4, hh, ← List.drop_drop, hx,
      show encodeNat a ++ (encodeNats locs ++ (encodeNat d ++ (encodeNats cs ++
        (encodeNats perms ++ rest)))) = (encodeNat a ++ (encodeNats locs ++ encodeNat d)) ++
        (encodeNats cs ++ (encodeNats perms ++ rest)) by simp, List.drop_left]
  · simp only [s4, rdNumFinal_stk]; rw [h3s]; rfl
  · simp only [s4, rdNumFinal_out]; rw [h3o]; rfl
  · rw [rdNumFinal_env_ne (by decide) (by decide) (by decide), h3f _ (by decide) (by decide)]
    exact e2T
  · exact rdNumFinal_env_r (by decide) (by decide) d
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [rdNumFinal_env_ne h6 h3 h4, h3f r h2 h4]
    simp only [s2, NSt.set_env, Function.update_of_ne h5, s1]
    rw [rdNumFinal_env_ne h1 h3 h4]

end Lax119563Proofs.Compiler
