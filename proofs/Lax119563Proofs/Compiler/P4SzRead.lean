import Lax119563Proofs.Compiler.P4SzRec

/-!
# Pass `P4` (program): reading one schema description for its sizes

`p4SRead` reads the arity (`rA`) and `|D|` (`rD`) of the schema at the cursor and skips the
rest of its description (locations, coordinates, `arity · k (ℓ + 1)` permutation words)
(**`p4SRead_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- Read arity and `|D|` of the schema at the cursor, skip the rest of its description. -/
def p4SRead : CStm CR CQ :=
  .seq (rdNumS rA rP rT) (.seq (skipNumsS rA rI rT) (.seq (rdNumS rD rP rT)
    (.seq (skipBlocksS rD rL1 rK rI rT) (.seq (mulS rC rA rKk rI) (.seq (mulS rC2 rC rL1 rI)
      (skipNumsS rC2 rI rT))))))

lemma flatMap_eq_map_flatten {α β : Type*} (l : List α) (f : α → List β) :
    l.flatMap f = (l.map f).flatten := List.flatMap_def

lemma p4SRead_arith {N U la llo ld lf lp a d k ℓ np : ℕ} (hU : U ≤ N) (ha : a ≤ llo)
    (hd : d ≤ lf) (hk : k ≤ lp) (hl : ℓ + 1 ≤ lp) (hp : np ≤ lp) :
    (la + 1) * (20 * N) + ((llo + a + 1) * (20 * N) + ((ld + 1) * (20 * N) +
      ((lf + d + 1) * (50 * N) + ((k + 1) * (12 * N) + ((ℓ + 1 + 1) * (12 * N) +
        (lp + np + 1) * (20 * N)))))) ≤
      150 * N * (la + llo + ld + lf + lp) + 200 * N := by
  nlinarith

lemma p4SRead_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hk : 1 ≤ k)
    (s : NSt CR CQ) {j : ℕ} (hj : j < I.schemas.length) (hpos : s.pos = schAt I j)
    (hL1 : s.env rL1 = ℓ + 1) (hK : s.env rKk = k) :
    ∃ s', Good (encodeSystem I) w p4SRead s s'
        (150 * Ex.nodeCost w * (encodeNats (schD I ⟨j, hj⟩)).length + 200 * Ex.nodeCost w) ∧
      s'.pos = s.pos + (encodeNats (schD I ⟨j, hj⟩)).length ∧ s'.stk = s.stk ∧
      s'.out = s.out ∧ s'.env rA = arity (sch I ⟨j, hj⟩) ∧
      s'.env rD = (coordList (dom I ⟨j, hj⟩)).length := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  set e : Fin I.schemas.length := ⟨j, hj⟩
  set sc := sch I e
  set a := arity sc
  set locs := schLocs sc
  set D := coordList (dom I e)
  set d := D.length
  set cs := D.map cdesc
  set perms := (schPerms sc).flatMap permDescription
  set rest := encodeNats (schsSuf I (j + 1))
  have hcsM : ∀ b ∈ cs, b.length = ℓ + 1 := by
    intro b hb; obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb; exact length_cdesc c
  have hcsl : cs.length = d := by simp (config := { decide := true }) [cs, d]
  have hfl : cs.flatten.length = d * (ℓ + 1) := by
    rw [List.length_flatten, List.map_congr_left hcsM, sum_map_const, hcsl]
  have hD : schD I e = a :: locs ++ (d :: cs.flatten) ++ perms := by
    rw [schD, schemaDescription_eq', ← flatMap_eq_map_flatten]; rfl
  have hx : (encodeSystem I).drop s.pos = encodeNat a ++ (encodeNats locs ++ (encodeNat d ++
      (encodeNats cs.flatten ++ (encodeNats perms ++ rest)))) := by
    rw [hpos, drop_schAt, schsSuf_cons I hj, encodeNats_append, hD]
    simp only [List.cons_append, encNats_cons, List.append_assoc, encodeNats_append]; rfl
  have hlenD : (encodeNats (schD I e)).length = (encodeNat a).length +
      (encodeNats locs).length + (encodeNat d).length + (encodeNats cs.flatten).length +
      (encodeNats perms).length := by
    rw [hD]; simp only [List.cons_append, encNats_cons, List.append_assoc, encodeNats_append,
      List.length_append]; ring
  have hDH := schD_le_H I e
  have hla : locs.length = a := length_schLocs sc
  have hp : perms.length = a * k * (ℓ + 1) := by
    rw [length_perms]; ring
  have ha23 : 2 ≤ a ∧ a ≤ 3 := by simp only [a, arity]; split_ifs <;> omega
  have hlo := length_le_encodeNats locs
  have hpe := length_le_encodeNats perms
  have hfe := length_le_encodeNats cs.flatten
  have hak : 0 < a * k := Nat.mul_pos (by omega) (by omega)
  have hkp : k ≤ perms.length := by
    rw [hp]
    exact le_trans (Nat.le_mul_of_pos_left k (by omega : 0 < a)) (Nat.le_mul_of_pos_right _ (by omega))
  have hlp : ℓ + 1 ≤ perms.length := by rw [hp]; exact Nat.le_mul_of_pos_left _ hak
  have hdf : d ≤ (encodeNats cs.flatten).length := by
    have : d ≤ cs.flatten.length := by rw [hfl]; exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hpH : perms.length ≤ H I := by omega
  have hdH : d ≤ H I := by omega
  -- reading the arity
  have r1 := rdNumS_good (Q := CQ) hw (r := rA) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s a _ hx (bits_lt_of_le (by omega) hH2)
  set s1 := rdNumFinal s rA rP rT a
  have e1A : s1.env rA = a := rdNumFinal_env_r (by decide) (by decide) a
  -- skipping the locations
  obtain ⟨s2, r2, h2s, h2p, h2o, h2f⟩ := skipNumsS_good (Q := CQ) hw (n := rA) (i := rI)
    (t := rT) (by decide) (by decide) (by decide) s1 locs _
    (by simp only [s1, rdNumFinal_pos]; rw [← List.drop_drop, hx, List.drop_left])
    (by rw [e1A, hla]) (by omega)
  -- reading `|D|`
  have r3 := rdNumS_good (Q := CQ) hw (r := rD) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s2 d _ (by
      rw [h2p]; simp only [s1, rdNumFinal_pos]
      rw [← List.drop_drop, ← List.drop_drop, hx, List.drop_left, List.drop_left])
    (bits_lt_of_le hdH hH2)
  set s3 := rdNumFinal s2 rD rP rT d
  have e3 : ∀ r, r ≠ rD → r ≠ rP → r ≠ rT → r ≠ rI → s3.env r = s1.env r := fun r h1 h2 h3 h4 => by
    rw [rdNumFinal_env_ne h1 h2 h3, h2f r h4 h3]
  -- skipping the coordinates
  obtain ⟨s4, r4, h4s, h4p, h4o, h4f⟩ := skipBlocksS_good (Q := CQ) hw (d := rD) (m := rL1)
    (j := rK) (i := rI) (t := rT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s3 cs (ℓ + 1) hcsM _
    (by
      simp only [s3, rdNumFinal_pos]; rw [h2p]; simp only [s1, rdNumFinal_pos]
      rw [← List.drop_drop, ← List.drop_drop, ← List.drop_drop, hx, List.drop_left,
        List.drop_left, List.drop_left])
    (by rw [hcsl]; exact rdNumFinal_env_r (by decide) (by decide) d)
    (by rw [e3 _ (by decide) (by decide) (by decide) (by decide),
      rdNumFinal_env_ne (by decide) (by decide) (by decide), hL1])
    (by rw [hcsl]; omega) (by omega)
  have e4 : ∀ r, r ≠ rK → r ≠ rI → r ≠ rT → r ≠ rD → r ≠ rP → s4.env r = s1.env r :=
    fun r h1 h2 h3 h4 h5 => by rw [h4f r h1 h2 h3, e3 r h4 h5 h3 h2]
  have e4A : s4.env rA = a := by rw [e4 _ (by decide) (by decide) (by decide) (by decide) (by decide), e1A]
  have e4K : s4.env rKk = k := by
    rw [e4 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      rdNumFinal_env_ne (by decide) (by decide) (by decide), hK]
  have e4L : s4.env rL1 = ℓ + 1 := by
    rw [e4 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      rdNumFinal_env_ne (by decide) (by decide) (by decide), hL1]
  -- the number of permutation words
  have r5 := mulS_good (x := encodeSystem I) (w := w) hw (dst := rC) (a := rA) (b := rKk)
    (j := rI) (by decide) (by decide) (by decide) (by decide) (by decide) s4 e4A e4K
    (by nlinarith) (by omega)
  set s5 := (s4.set rC (a * k)).set rI k
  have r6 := mulS_good (x := encodeSystem I) (w := w) hw (dst := rC2) (a := rC) (b := rL1)
    (j := rI) (by decide) (by decide) (by decide) (by decide) (by decide) s5 (A := a * k) (B := ℓ + 1)
    (by simp (config := { decide := true }) [s5, Function.update_of_ne (show rC ≠ rI by decide)])
    (by simp (config := { decide := true }) [s5, Function.update_of_ne (show rL1 ≠ rI by decide),
      Function.update_of_ne (show rL1 ≠ rC by decide), e4L])
    (by rw [← hp]; omega) (by omega)
  set s6 := (s5.set rC2 (a * k * (ℓ + 1))).set rI (ℓ + 1)
  -- skipping the permutations
  obtain ⟨s7, r7, h7s, h7p, h7o, h7f⟩ := skipNumsS_good (Q := CQ) hw (n := rC2) (i := rI)
    (t := rT) (by decide) (by decide) (by decide) s6 perms rest
    (by
      simp only [s6, s5, NSt.set_pos]; rw [h4p]; simp only [s3, rdNumFinal_pos]; rw [h2p]
      simp only [s1, rdNumFinal_pos]
      rw [← List.drop_drop, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop, hx,
        List.drop_left, List.drop_left, List.drop_left, List.drop_left])
    (by simp (config := { decide := true }) [s6, Function.update_of_ne (show rC2 ≠ rI by decide), hp]) (by omega)
  refine ⟨s7, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [hlenD]
    have := p4SRead_arith (N := Ex.nodeCost w) (U := unitCost w)
      (la := (encodeNat a).length) (llo := (encodeNats locs).length)
      (ld := (encodeNat d).length) (lf := (encodeNats cs.flatten).length)
      (lp := (encodeNats perms).length) (a := locs.length) (d := cs.length) (k := k) (ℓ := ℓ)
      (np := perms.length) hU hlo (by rw [hcsl]; exact hdf) (by omega) (by omega) hpe
    exact this
  · rw [h7p]; simp only [s6, s5, NSt.set_pos]; rw [h4p]; simp only [s3, rdNumFinal_pos]
    rw [h2p]; simp only [s1, rdNumFinal_pos]; rw [hlenD]; ring
  · rw [h7s]; simp only [s6, s5, NSt.set_stk]; rw [h4s]; simp only [s3, rdNumFinal_stk]
    rw [h2s]; rfl
  · rw [h7o]; simp only [s6, s5, NSt.set_out]; rw [h4o]; simp only [s3, rdNumFinal_out]
    rw [h2o]; rfl
  · rw [h7f _ (by decide) (by decide)]
    simp (config := { decide := true }) [s6, s5, Function.update_of_ne (show rA ≠ rI by decide),
      Function.update_of_ne (show rA ≠ rC2 by decide), Function.update_of_ne (show rA ≠ rC by decide)]
    exact e4A
  · rw [h7f _ (by decide) (by decide)]
    simp (config := { decide := true }) [s6, s5, Function.update_of_ne (show rD ≠ rI by decide),
      Function.update_of_ne (show rD ≠ rC2 by decide), Function.update_of_ne (show rD ≠ rC by decide)]
    rw [h4f _ (by decide) (by decide) (by decide)]
    exact rdNumFinal_env_r (by decide) (by decide) d

end Lax119563Proofs.Compiler
