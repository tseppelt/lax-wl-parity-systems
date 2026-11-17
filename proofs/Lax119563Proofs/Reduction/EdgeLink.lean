import Lax119563Proofs.Reduction.EdgePrev

/-!
# The edge pass of the `link` kind

A valid `link e c` slot with label `l` is adjacent to the end coordinate `coord (locEnd) c`
(effective label `l.1`) and to the last track `trackAt e c NS = track e (P - 1) c`, where
`P = prevCnt … NS ≠ 0` is computed by `prevGen` under a `count`, and `P - 1` by `bindSub`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Matrix

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

lemma valid_track_of_prev (I : ImplicitParitySystem (s + 1) ℓ) (ε : ZMod 2)
    {e : Fin I.schemas.length} {c : Coord (s + 1) ℓ} {σ σ' : ℕ} (hσ : σ ≤ numSteps (s + 1) ℓ)
    (hp : prevStep c σ = some σ') (hd : c ∈ dom I e) (r : ZMod 2) :
    Valid I (nameOfEff I ε (.track e σ' c) r) := by
  obtain ⟨h1, h2, -⟩ := prevStep_some hp
  exact (valid_nameOfEff_plain I ε rfl rfl r).mpr ⟨by omega, hd, h2⟩

lemma valid_track_of_link (I : ImplicitParitySystem (s + 1) ℓ) (ε : ZMod 2)
    {e : Fin I.schemas.length} {c : Coord (s + 1) ℓ} {l : Lab} (h : Valid I (.link e c, l))
    {σ σ' : ℕ} (hσ : σ ≤ numSteps (s + 1) ℓ) (hp : prevStep c σ = some σ') (r : ZMod 2) :
    Valid I (nameOfEff I ε (.track e σ' c) r) :=
  valid_track_of_prev I ε hσ hp ((valid_link_iff I).mp h).1 r

lemma trackAt_of_prevCnt (I : ImplicitParitySystem (s + 1) ℓ) (e : Fin I.schemas.length)
    (c : Coord (s + 1) ℓ) {σ : ℕ} (h : prevCnt (fun σ' => decide (ent σ' c ≠ 0)) σ ≠ 0) :
    prevStep c σ = some (prevCnt (fun σ' => decide (ent σ' c ≠ 0)) σ - 1) ∧
      trackAt I e c σ = .track e (prevCnt (fun σ' => decide (ent σ' c ≠ 0)) σ - 1) c := by
  have hp : prevStep c σ = some (prevCnt (fun σ' => decide (ent σ' c ≠ 0)) σ - 1) := by
    rw [prevStep_eq_count, if_neg h]
  exact ⟨hp, by rw [trackAt, hp]⟩

lemma prevCnt_numSteps_ne_zero (hs : 1 ≤ s) (c : Coord (s + 1) ℓ) :
    prevCnt (fun σ' => decide (ent σ' c ≠ 0)) (numSteps (s + 1) ℓ) ≠ 0 := by
  intro h
  apply prevStep_numSteps_ne_none hs c
  rw [prevStep_eq_count, if_pos h]

lemma bnd_uX {s : ℕ} (d : ℕ) {FX : Xp} (hF : FX.Bnd (d + 8)) (hd : 17 ≤ d) :
    (uX s d FX).Bnd (d + 8) := by
  unfold uX numX
  refine ⟨show _ < _ by omega, Xp.bnd_mulC ?_ _⟩
  exact ⟨⟨⟨show _ < _ by omega, Xp.bnd_mulC hF _⟩, show _ < _ by omega⟩, show _ < _ by omega⟩

namespace Gn

/-- The edges of a `link` slot (slot loops at depth `b + 37`). -/
def edgeLinkBody (s ε b : ℕ) : Gn :=
  let d := b + 37
  let u := uX s d (add (add gENS gE) (var (b + 27)))
  ite (and (inDomX d) (lab2X d))
    (seq (coordGen s ε u (var (b + 31)) (var (d + 1)) (var (d + 3)) (odd (var (d + 7))))
      (count (prevGen s (d + 9) gNS (var (d + 1)) (var (d + 3)))
        (bindSub (d + 9) (var (d + 8)) (const 1)
          (plainGen s u (odd (var (d + 7)))
            (add (add (add gENS (mulC 3 gE)) gW) (add (mul (var (b + 27)) gNS) (var (d + 9))))
            (var (d + 1)) (var (d + 3))))))
    skip

/-- The edges of the `link` families. -/
def edgeLink (M : Machine) (s ε b : ℕ) : Gn := schSlots M s b (edgeLinkBody s ε b)

end Gn

theorem out_edgeLink {ρ : List ℕ} {b ε : ℕ} (hρ : ρ.length = b) (hG : GlobOK M x s ℓ H ρ)
    (hℓ : 0 < ℓ) (hs : 1 ≤ s) (hε : ε ≤ 1) :
    (Gn.edgeLink M s ε b).out x ρ =
      (List.range (Iv M x s ℓ H).schemas.length).flatMap fun e =>
        slotL s ℓ fun i v t => edgesOf (Iv M x s ℓ H) (ε : ZMod 2)
          (slotNum s ℓ ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ +
            (Iv M x s ℓ H).schemas.length + e) i v t) := by
  refine out_schSlots hρ hG _ _ ?_
  intro e he τ hc i hi v hv t ht
  have hGσ : GlobOK M x s ℓ H (slotStk s ℓ x τ (violAt s b (b + 37)) i v t) :=
    (hG.of_take hρ hc.2.1).append _
  have hσl : (slotStk s ℓ x τ (violAt s b (b + 37)) i v t).length = b + 45 := by
    rw [slotStk_length, hc.1]
  obtain ⟨h1, -, h3, h4, h5⟩ := schSlot_facts hG hρ hc (List.take_of_length_le (by rw [hc.1]))
    hc.1 le_rfl hℓ t hi hv
  obtain ⟨-, -, -, m4, -, -, m7⟩ := schCtx_match hc
  have hlt : ∀ k, k < b + 37 → (slotStk s ℓ x τ (violAt s b (b + 37)) i v t).getD k 0 =
      τ.getD k 0 := fun k hk => slotStk_lt _ _ _ _ (by rw [hc.1]; omega)
  have hX : famNum (Iv M x s ℓ H) (.link (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length)
      ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)) = (Iv M x s ℓ H).schemas.length *
        numSteps (s + 1) ℓ + (Iv M x s ℓ H).schemas.length + e := rfl
  rw [← hX, edgesOf_hub_slot (Iv M x s ℓ H) hs (ternOrdered_compile _ _ _) _
    (X := .link ⟨e, he⟩ (⟨i, hi⟩, toBlk ℓ v)) trivial rfl hi hv ht rfl, hX]
  have hu : (uX s (b + 37) (add (add gENS gE) (var (b + 27)))).eval
      (slotStk s ℓ x τ (violAt s b (b + 37)) i v t) = slotNum s ℓ
        ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ + (Iv M x s ℓ H).schemas.length + e)
        i v t := by
    rw [uX, eval_numX hGσ]
    simp only [eval_var, eval_add, h3, h4, h5, hGσ.eENS, hGσ.eE, hlt (b + 27) (by omega), hc.2.2.1]
    simp [slotNum]
  have hvalid : (and (inDomX (b + 37)) (lab2X (b + 37))).eval
      (slotStk s ℓ x τ (violAt s b (b + 37)) i v t) ≠ 0 ↔
      Valid (Iv M x s ℓ H) (.link (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length)
        ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ), labOf t) := by
    rw [inDomX, lab2X, eval_and' (eval_eq' _ _) (eval_lt_eq _ _), ite_ne_zero_iff]
    simp only [eval_var, eval_const]
    rw [h1, h5, valid_link_iff, labOf_snd_eq_zero ht]
    rfl
  simp only [Gn.edgeLinkBody, Gn.out]
  by_cases hV : Valid (Iv M x s ℓ H) (.link (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length)
      ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ), labOf t)
  · rw [if_pos (hvalid.mpr hV), if_pos hV]
    simp only [nbrCand, List.flatMap_cons, List.flatMap_nil, List.append_nil, endCls]
    have hA := out_coordGen (wX := var (b + 31)) (iX := var (b + 37 + 1))
      (vX := var (b + 37 + 3)) (rX := odd (var (b + 37 + 7))) hGσ hε
      (locEnd (sch (Iv M x s ℓ H) ⟨e, he⟩))
      ((permEnd (sch (Iv M x s ℓ H) ⟨e, he⟩)).apply (⟨i, hi⟩, toBlk ℓ v)) (labOf t).1 hu
      (by rw [eval_var, hlt (b + 31) (by omega), ← m4]) (by rw [eval_var, h3, m7])
      (by rw [eval_var, h4, m7, regVal_toBlk hv])
      (by rw [eval_odd, eval_var, h5, (labOf_val t ht).1])
    rw [hA]
    -- the last track
    set P := prevCnt (fun σ' => decide (ent σ' ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) ≠ 0))
      (numSteps (s + 1) ℓ) with hP
    have hP0 : P ≠ 0 := prevCnt_numSteps_ne_zero hs _
    obtain ⟨hp, htr⟩ := trackAt_of_prevCnt (Iv M x s ℓ H) ⟨e, he⟩
      ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) hP0
    have hlen := length_out_prevGen (D := b + 37 + 9) (by simp [hσl])
      (hGσ.append [0]) (σX := gNS) (iX := var (b + 37 + 1)) (vX := var (b + 37 + 3))
      (bnd_glob (by omega) (by omega)) (show _ < _ by omega) (show _ < _ by omega)
      (hGσ.append [0]).eNS le_rfl (by omega) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)
      (by rw [eval_append hσl _ (show _ < _ by omega), eval_var, h3])
      (by rw [eval_append hσl _ (show _ < _ by omega), eval_var, h4, regVal_toBlk hv])
    rw [hlen, ← hP]
    set σ1 := slotStk s ℓ x τ (violAt s b (b + 37)) i v t ++ [P]
    have hσ1 : σ1.length = b + 37 + 9 := by simp [σ1, hσl]
    rw [Gn.out_bindSub hσ1 (show (var (b + 37 + 8)).Bnd (b + 37 + 9) from
      show b + 37 + 8 < b + 37 + 9 by omega) (show (const 1).Bnd (b + 37 + 9) from trivial)]
    have hPv : (var (b + 37 + 8)).eval σ1 = P := by
      rw [eval_var, show b + 37 + 8 = (slotStk s ℓ x τ (violAt s b (b + 37)) i v t).length + 0 by
        rw [hσl], getD_app]; rfl
    rw [hPv, eval_const]
    have hG2 : GlobOK M x s ℓ H (σ1 ++ [P - 1]) := (hGσ.append _).append _
    have ev2 : ∀ k, k < b + 45 → (var k).eval (σ1 ++ [P - 1]) =
        (slotStk s ℓ x τ (violAt s b (b + 37)) i v t).getD k 0 := fun k hk => by
      rw [eval_var, List.append_assoc, getD_app_lt _ (by rw [hσl]; omega)]
    have hval := valid_track_of_link (Iv M x s ℓ H) (ε : ZMod 2) hV le_rfl hp (labOf t).1
    have hstk : σ1 ++ [P - 1] = slotStk s ℓ x τ (violAt s b (b + 37)) i v t ++ [P, P - 1] := by
      simp [σ1]
    have evB : ∀ {e : Xp}, e.Bnd (b + 45) →
        e.eval (σ1 ++ [P - 1]) = e.eval (slotStk s ℓ x τ (violAt s b (b + 37)) i v t) :=
      fun he => by rw [hstk]; exact eval_append hσl _ he
    have hB := out_plainGen (Iv M x s ℓ H) hG2 (ε := (ε : ZMod 2)) (r := (labOf t).1)
      (uX := uX s (b + 37) (add (add gENS gE) (var (b + 27)))) (labX := odd (var (b + 37 + 7)))
      (FX := add (add (add gENS (mulC 3 gE)) gW) (add (mul (var (b + 27)) gNS)
        (var (b + 37 + 9))))
      (iX := var (b + 37 + 1)) (vX := var (b + 37 + 3))
      (Y := .track ⟨e, he⟩ (P - 1) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)) rfl
      (by rw [evB (bnd_uX (b + 37) (FX := add (add gENS gE) (var (b + 27)))
            ⟨⟨bnd_glob (by omega) (by omega), bnd_glob (by omega) (by omega)⟩,
              show b + 27 < b + 37 + 8 by omega⟩ (by omega))])
      (by rw [evB (show (odd (var (b + 37 + 7))).Bnd (b + 45) from show _ < _ by omega), eval_odd,
            eval_var, h5, (labOf_val t ht).1])
      (by
        simp only [eval_add, eval_mulC, eval_mul, hG2.eENS, hG2.eE, hG2.eW, hG2.eNS, eval_var]
        rw [hstk, getD_app_lt _ (by rw [hσl]; omega), hlt (b + 27) (by omega), hc.2.2.1,
          show b + 37 + 9 = (slotStk s ℓ x τ (violAt s b (b + 37)) i v t).length + 1 by
            rw [hσl], getD_app]
        rfl)
      (by rw [ev2 _ (by omega), h3]; rfl)
      (by rw [ev2 _ (by omega), h4]; exact (regVal_toBlk hv).symm)
    rw [hu] at hB
    rw [hB, htr, ← hP]
    simp only [candOut]
    rw [← hP] at hval
    rw [if_pos hval]
  · rw [if_neg (fun h => hV (hvalid.mp h)), if_neg hV]

end Lax119563Proofs.Reduction
