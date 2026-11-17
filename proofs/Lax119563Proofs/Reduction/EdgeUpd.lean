import Lax119563Proofs.Reduction.EdgeLink

/-!
# The edge pass of the `upd` kind

A valid `upd e σ c` slot with label `l` is adjacent to the incoming track `trackAt e c σ`
(label `l.1`; `track e (P-1) c` if `P = prevCnt … σ ≠ 0`, else the start class: `sum e c` for
ternary schemas, `coord (locU) (permU c)` otherwise), the outgoing track `track e σ c`
(label `l.2`) and the coefficient `coef e σ` (label `l.1 + l.2`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Matrix

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

section Valid

variable (I : ImplicitParitySystem (s + 1) ℓ) (ε : ZMod 2) {e : Fin I.schemas.length}
  {σ : ℕ} {c : Coord (s + 1) ℓ} {l : Lab} (h : Valid I (.upd e σ c, l))
include h

lemma valid_track_of_upd (r : ZMod 2) : Valid I (nameOfEff I ε (.track e σ c) r) :=
  (valid_nameOfEff_plain I ε rfl rfl r).mpr ((valid_upd_iff I).mp h)

lemma valid_coef_of_upd (r : ZMod 2) : Valid I (nameOfEff I ε (.coef e σ) r) :=
  (valid_nameOfEff_plain I ε rfl rfl r).mpr
    ⟨((valid_upd_iff I).mp h).1, c, ((valid_upd_iff I).mp h).2⟩

lemma valid_prev_of_upd {σ' : ℕ} (hp : prevStep c σ = some σ') (r : ZMod 2) :
    Valid I (nameOfEff I ε (.track e σ' c) r) :=
  valid_track_of_prev I ε ((valid_upd_iff I).mp h).1.le hp ((valid_upd_iff I).mp h).2.1 r

lemma valid_sum_of_upd (hT : isTern (sch I e) = true) (r : ZMod 2) :
    Valid I (nameOfEff I ε (.sum e c) r) :=
  valid_nameOfEff_sum I ε hT ((valid_upd_iff I).mp h).2.1 r

end Valid

lemma trackAt_of_prevCnt_zero (I : ImplicitParitySystem (s + 1) ℓ) (e : Fin I.schemas.length)
    (c : Coord (s + 1) ℓ) {σ : ℕ} (h : prevCnt (fun σ' => decide (ent σ' c ≠ 0)) σ = 0) :
    trackAt I e c σ = startCls I e c := by
  rw [trackAt, prevStep_eq_count, if_pos h]

lemma startCls_of_tern (I : ImplicitParitySystem (s + 1) ℓ) (e : Fin I.schemas.length)
    (c : Coord (s + 1) ℓ) (h : isTern (sch I e) = true) : startCls I e c = .sum e c := by
  simp [startCls, h]

lemma startCls_of_not_tern (I : ImplicitParitySystem (s + 1) ℓ) (e : Fin I.schemas.length)
    (c : Coord (s + 1) ℓ) (h : ¬ isTern (sch I e) = true) :
    startCls I e c = .coord (locU (sch I e)) ((permU (sch I e)).apply c) := by
  simp [startCls, h]

namespace Gn

/-- The edges of an `upd` slot (slot loops at depth `b + 41`). -/
def edgeUpdBody (s ε b : ℕ) : Gn :=
  let d := b + 41
  let σX := stepX s (b + 37)
  let u := uX s d (add (mul (var (b + 27)) gNS) σX)
  ite (and (inDomX d) (entX s (var (b + 40)) (var (d + 1)) (var (d + 3))))
    (seq (count (prevGen s (d + 9) σX (var (d + 1)) (var (d + 3)))
        (ite (eq (var (d + 8)) (const 0))
          (ite (ternX b)
            (plainGen s u (odd (var (d + 7))) (add (add (add gENS (mulC 2 gE)) gW) (var (b + 27)))
              (var (d + 1)) (var (d + 3)))
            (coordGen s ε u (var (b + 29)) (var (d + 1))
              (permVX s (var (b + 32)) (var (d + 1)) (var (d + 3))) (odd (var (d + 7)))))
          (bindSub (d + 9) (var (d + 8)) (const 1)
            (plainGen s u (odd (var (d + 7)))
              (add (add (add gENS (mulC 3 gE)) gW) (add (mul (var (b + 27)) gNS) (var (d + 9))))
              (var (d + 1)) (var (d + 3))))))
      (seq (plainGen s u (half (var (d + 7)))
          (add (add (add gENS (mulC 3 gE)) gW) (add (mul (var (b + 27)) gNS) σX))
          (var (d + 1)) (var (d + 3)))
        (plainGen s u (odd (add (odd (var (d + 7))) (half (var (d + 7)))))
          (add (add (add (mulC 2 gENS) (mulC 3 gE)) gW) (add (mul (var (b + 27)) gNS) σX))
          (const 0) (const 0))))
    skip

/-- The edges of the `upd` families. -/
def edgeUpd (M : Machine) (s ε b : ℕ) : Gn := stepSlots M s b (edgeUpdBody s ε b)

end Gn

end Lax119563Proofs.Reduction

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Matrix

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

lemma bnd_stepX {D n : ℕ} (h : D + 3 < n) (h2 : 17 ≤ n) : (stepX s D).Bnd n :=
  ⟨⟨show D + 1 < n by omega, ⟨trivial, show 2 < n by omega⟩, ⟨trivial, show 2 < n by omega⟩⟩,
    show D + 3 < n by omega⟩

theorem out_edgeUpd {ρ : List ℕ} {b ε : ℕ} (hρ : ρ.length = b) (hG : GlobOK M x s ℓ H ρ)
    (hℓ : 0 < ℓ) (hs : 1 ≤ s) (hε : ε ≤ 1) :
    (Gn.edgeUpd M s ε b).out x ρ =
      (List.range ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ)).flatMap fun F =>
        slotL s ℓ fun i v t => edgesOf (Iv M x s ℓ H) (ε : ZMod 2) (slotNum s ℓ F i v t) := by
  rw [range_mul_flatMap]
  refine out_stepSlots hρ hG _ (fun e σ i v t => edgesOf (Iv M x s ℓ H) (ε : ZMod 2)
    (slotNum s ℓ (e * numSteps (s + 1) ℓ + σ) i v t)) ?_
  intro e he τ hc q hq j hj i hi v hv t ht
  have hb := hρ ▸ hG.le
  have hl : (τ ++ [s + 2, q, s + ℓ, j]).length = b + 41 := by simp [hc.1]
  set SS := slotStk s ℓ x (τ ++ [s + 2, q, s + ℓ, j]) (violAt s b (b + 41)) i v t with hSS
  have hSl : SS.length = b + 49 := by rw [hSS, slotStk_length, hl]
  have hGτ : GlobOK M x s ℓ H τ := hG.of_take hρ hc.2.1
  have hGS : GlobOK M x s ℓ H SS := (hGτ.append _).append _
  obtain ⟨h1, -, h3, h4, h5⟩ := schSlot_facts hG hρ hc
    (by rw [List.take_append_of_le_length (by rw [hc.1]), List.take_of_length_le (by rw [hc.1])])
    hl (by omega) hℓ t hi hv
  obtain ⟨m1, m2, -, -, m5, -, -⟩ := schCtx_match hc
  have h3' : SS.getD (b + 42) 0 = i := h3
  have h4' : SS.getD (b + 44) 0 = v := h4
  have h5' : SS.getD (b + 48) 0 = t := h5
  have hlt : ∀ k, k < b + 37 → SS.getD k 0 = τ.getD k 0 := fun k hk => by
    rw [hSS, slotStk_lt _ _ _ _ (by rw [hl]; omega), getD_app_lt _ (by rw [hc.1]; omega)]
  have hj' : SS.getD (b + 40) 0 = j := by
    rw [hSS, slotStk_lt _ _ _ _ (by rw [hl]; omega), show b + 40 = τ.length + 3 by rw [hc.1],
      getD_app]; rfl
  have hσS : ∀ l : List ℕ, (stepX s (b + 37)).eval (SS ++ l) = q * (s + ℓ) + j := fun l => by
    rw [hSS, slotStk, List.append_assoc]
    exact eval_stepX hc.1 hGτ _
  have hσ0 : (stepX s (b + 37)).eval SS = q * (s + ℓ) + j := by
    have := hσS []; rwa [List.append_nil] at this
  have hσN := step_lt (s := s) (ℓ := ℓ) hq hj
  have hX : famNum (Iv M x s ℓ H) (.upd (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length)
      (q * (s + ℓ) + j) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)) =
      e * numSteps (s + 1) ℓ + (q * (s + ℓ) + j) := rfl
  show (Gn.edgeUpdBody s ε b).out x SS = _
  rw [← hX, edgesOf_hub_slot (Iv M x s ℓ H) hs (ternOrdered_compile _ _ _) _
    (X := .upd ⟨e, he⟩ (q * (s + ℓ) + j) (⟨i, hi⟩, toBlk ℓ v)) hσN rfl hi hv ht rfl, hX]
  set u := slotNum s ℓ (e * numSteps (s + 1) ℓ + (q * (s + ℓ) + j)) i v t with hu_def
  have huB : (uX s (b + 41) (add (mul (var (b + 27)) gNS) (stepX s (b + 37)))).Bnd (b + 49) :=
    bnd_uX (b + 41) ⟨⟨show b + 27 < b + 41 + 8 by omega, bnd_glob (by omega) (by omega),
      bnd_glob (by omega) (by omega)⟩, bnd_stepX (by omega) (by omega)⟩ (by omega)
  have hu : ∀ l : List ℕ,
      (uX s (b + 41) (add (mul (var (b + 27)) gNS) (stepX s (b + 37)))).eval (SS ++ l) = u := by
    intro l
    rw [eval_append hSl l huB, uX, eval_numX hGS]
    simp only [eval_var, eval_add, eval_mul, h3', h4', h5', hGS.eNS, hσ0, hlt (b + 27) (by omega),
      hc.2.2.1]
    simp [hu_def, slotNum]
  have hvalid : (and (inDomX (b + 41)) (entX s (var (b + 40)) (var (b + 41 + 1))
      (var (b + 41 + 3)))).eval SS ≠ 0 ↔
      Valid (Iv M x s ℓ H) (.upd (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) (q * (s + ℓ) + j)
        ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ), labOf t) := by
    rw [inDomX, eval_and' (eval_eq' _ _) (eval_entX _ _ _), ite_ne_zero_iff]
    simp only [eval_var, eval_const]
    rw [h1, h3, h4, hj', valid_upd_iff, ent_ne_zero_iff (by omega), mod_step hj, regVal_toBlk hv]
    simp [hσN]
    exact fun _ => Iff.rfl
  have evS : ∀ {f : Xp}, f.Bnd (b + 49) → ∀ l, f.eval (SS ++ l) = f.eval SS :=
    fun hf l => eval_append hSl l hf
  have hu0 : (uX s (b + 41) (add (mul (var (b + 27)) gNS) (stepX s (b + 37)))).eval SS = u := by
    have := hu []; rwa [List.append_nil] at this
  simp only [Gn.edgeUpdBody, Gn.out]
  by_cases hV : Valid (Iv M x s ℓ H) (.upd (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) (q * (s + ℓ) + j) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ), labOf t)
  · rw [if_pos (hvalid.mpr hV), if_pos hV]
    simp only [nbrCand, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    -- the outgoing track and the coefficient
    have hB := out_plainGen (Iv M x s ℓ H) hGS (ε := (ε : ZMod 2)) (r := (labOf t).2)
      (uX := uX s (b + 41) (add (mul (var (b + 27)) gNS) (stepX s (b + 37))))
      (labX := half (var (b + 41 + 7)))
      (FX := add (add (add gENS (mulC 3 gE)) gW) (add (mul (var (b + 27)) gNS) (stepX s (b + 37))))
      (iX := var (b + 41 + 1)) (vX := var (b + 41 + 3))
      (Y := .track (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) (q * (s + ℓ) + j) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)) rfl hu0
      (by rw [Xp.eval_half', eval_var, h5, (labOf_val t ht).2.1])
      (by
        simp only [eval_add, eval_mulC, eval_mul, eval_var, hGS.eENS, hGS.eE, hGS.eW, hGS.eNS, hσ0,
          hlt (b + 27) (by omega), hc.2.2.1]
        rfl)
      (by rw [eval_var, h3]; rfl) (by rw [eval_var, h4]; exact (regVal_toBlk hv).symm)
    have hC := out_plainGen (Iv M x s ℓ H) hGS (ε := (ε : ZMod 2)) (r := (labOf t).1 + (labOf t).2)
      (uX := uX s (b + 41) (add (mul (var (b + 27)) gNS) (stepX s (b + 37))))
      (labX := odd (add (odd (var (b + 41 + 7))) (half (var (b + 41 + 7)))))
      (FX := add (add (add (mulC 2 gENS) (mulC 3 gE)) gW)
        (add (mul (var (b + 27)) gNS) (stepX s (b + 37))))
      (iX := const 0) (vX := const 0)
      (Y := .coef (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) (q * (s + ℓ) + j)) rfl hu0
      (by simp only [eval_odd, eval_add, Xp.eval_half', eval_var]
          rw [h5, (labOf_val t ht).2.2])
      (by
        simp only [eval_add, eval_mulC, eval_mul, eval_var, hGS.eENS, hGS.eE, hGS.eW, hGS.eNS, hσ0,
          hlt (b + 27) (by omega), hc.2.2.1]
        rfl)
      rfl (by rw [eval_const]; exact (regVal_zero ℓ).symm)
    simp only [hB, hC, if_pos (valid_track_of_upd (Iv M x s ℓ H) (ε : ZMod 2) hV _),
      if_pos (valid_coef_of_upd (Iv M x s ℓ H) (ε : ZMod 2) hV _), List.append_left_inj]
    -- the incoming track
    set P := prevCnt (fun σ' => decide (ent σ' ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) ≠ 0)) (q * (s + ℓ) + j) with hP
    have hlen := length_out_prevGen (D := b + 41 + 9) (by simp [hSl]) (hGS.append [0])
      (σX := stepX s (b + 37)) (iX := var (b + 41 + 1)) (vX := var (b + 41 + 3))
      (bnd_stepX (by omega) (by omega)) (show _ < _ by omega) (show _ < _ by omega) (hσS [0])
      hσN.le (by omega) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)
      (by rw [evS (show (var (b + 41 + 1)).Bnd (b + 49) from show _ < _ by omega), eval_var, h3])
      (by rw [evS (show (var (b + 41 + 3)).Bnd (b + 49) from show _ < _ by omega), eval_var, h4,
            regVal_toBlk hv])
    simp only [hlen, ← hP]
    have hGP : GlobOK M x s ℓ H (SS ++ [P]) := hGS.append _
    have hPv : (var (b + 41 + 8)).eval (SS ++ [P]) = P := by
      rw [eval_var, show b + 41 + 8 = SS.length + 0 by rw [hSl], getD_app]; rfl
    have hev1 : ∀ {f : Xp}, f.Bnd (b + 49) → f.eval (SS ++ [P]) = f.eval SS := fun hf => evS hf _
    have heq0 : (eq (var (b + 41 + 8)) (const 0)).eval (SS ++ [P]) = if P = 0 then 1 else 0 := by
      rw [eval_eq', hPv]; rfl
    simp only [heq0]
    by_cases hP0 : P = 0
    · have h1ne : (if P = 0 then 1 else 0 : ℕ) ≠ 0 := by rw [if_pos hP0]; omega
      simp only [if_pos h1ne]
      have htv : (ternX b).eval (SS ++ [P]) = if τ.getD (b + 28) 0 = 1 then 1 else 0 := by
        rw [ternX, eval_eq', eval_var, getD_app_lt _ (by rw [hSl]; omega), hlt (b + 28) (by omega),
          eval_const]
      by_cases hT : isTern (sch (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length)) = true
      · have hne : (ternX b).eval (SS ++ [P]) ≠ 0 := by rw [htv, if_pos (m1.mp hT)]; omega
        simp only [if_pos hne]
        have htr0 : trackAt (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) (q * (s + ℓ) + j) = .sum (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) := by
          rw [trackAt_of_prevCnt_zero (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) hP0, startCls_of_tern (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) hT]
        rewrite [htr0]
        have hA := out_plainGen (Iv M x s ℓ H) hGP (ε := (ε : ZMod 2)) (r := (labOf t).1)
          (uX := uX s (b + 41) (add (mul (var (b + 27)) gNS) (stepX s (b + 37))))
          (labX := odd (var (b + 41 + 7)))
          (FX := add (add (add gENS (mulC 2 gE)) gW) (var (b + 27)))
          (iX := var (b + 41 + 1)) (vX := var (b + 41 + 3))
          (Y := .sum (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)) (u := u) rfl (hu [P])
          (by rw [hev1 (show (odd (var (b + 41 + 7))).Bnd (b + 49) from show _ < _ by omega),
                eval_odd, eval_var, h5, (labOf_val t ht).1])
          (by
            simp only [eval_add, eval_mulC, eval_var, hGP.eENS, hGP.eE, hGP.eW]
            rw [getD_app_lt _ (by rw [hSl]; omega), hlt (b + 27) (by omega), hc.2.2.1]
            rfl)
          (by rw [hev1 (show (var (b + 41 + 1)).Bnd (b + 49) from show _ < _ by omega), eval_var,
                h3]; rfl)
          (by rw [hev1 (show (var (b + 41 + 3)).Bnd (b + 49) from show _ < _ by omega), eval_var,
                h4]; exact (regVal_toBlk hv).symm)
        rewrite [hA, if_pos (valid_sum_of_upd (Iv M x s ℓ H) (ε : ZMod 2) hV hT _)]
        rfl
      · have hne : ¬ (ternX b).eval (SS ++ [P]) ≠ 0 := by
          rw [htv, if_neg (fun h => hT (m1.mpr h))]; omega
        simp only [if_neg hne]
        have htr0 : trackAt (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) (q * (s + ℓ) + j) = .coord (locU (sch (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length)))
            ((permU (sch (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length))).apply ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)) := by
          rw [trackAt_of_prevCnt_zero (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) hP0, startCls_of_not_tern (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) hT]
        rewrite [htr0]
        have hv4 : (var (b + 41 + 3)).eval (SS ++ [P]) < 2 ^ ℓ := by
          rw [eval_var, getD_app_lt _ (by rw [hSl]; omega), h4]; exact hv
        have hPU := m5 ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)
        have hA := out_coordGen (wX := var (b + 29)) (iX := var (b + 41 + 1))
          (vX := permVX s (var (b + 32)) (var (b + 41 + 1)) (var (b + 41 + 3)))
          (rX := odd (var (b + 41 + 7))) hGP hε
          (locU (sch (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length))) ((permU (sch (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length))).apply ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)) (labOf t).1 (hu [P])
          (by rw [eval_var, getD_app_lt _ (by rw [hSl]; omega), hlt (b + 29) (by omega), ← m2])
          (by rw [hev1 (show (var (b + 41 + 1)).Bnd (b + 49) from show _ < _ by omega), eval_var,
                h3, hPU.1])
          (by
            rw [eval_permVX hGP _ _ _ hv4]
            simp only [eval_var]
            rw [getD_app_lt _ (by rw [hSl]; omega), getD_app_lt _ (by rw [hSl]; omega),
              getD_app_lt _ (by rw [hSl]; omega), h3, h4, hlt (b + 32) (by omega), hPU.2,
              regVal_toBlk hv])
          (by rw [hev1 (show (odd (var (b + 41 + 7))).Bnd (b + 49) from show _ < _ by omega),
                eval_odd, eval_var, h5, (labOf_val t ht).1])
        rewrite [hA]
        rfl
    · have h0 : ¬ (if P = 0 then 1 else 0 : ℕ) ≠ 0 := by rw [if_neg hP0]; omega
      simp only [if_neg h0]
      obtain ⟨hp, htr⟩ := trackAt_of_prevCnt (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) hP0
      rw [← hP] at hp htr
      rewrite [htr]
      have hσ1 : (SS ++ [P]).length = b + 41 + 9 := by simp [hSl]
      simp only [Gn.out_bindSub hσ1 (show (var (b + 41 + 8)).Bnd (b + 41 + 9) from
        show b + 41 + 8 < b + 41 + 9 by omega) (show (const 1).Bnd (b + 41 + 9) from trivial),
        hPv, eval_const]
      have hG2 : GlobOK M x s ℓ H (SS ++ [P] ++ [P - 1]) := hGP.append _
      have hstk : SS ++ [P] ++ [P - 1] = SS ++ [P, P - 1] := by simp
      have hA := out_plainGen (Iv M x s ℓ H) hG2 (ε := (ε : ZMod 2)) (r := (labOf t).1)
        (uX := uX s (b + 41) (add (mul (var (b + 27)) gNS) (stepX s (b + 37))))
        (labX := odd (var (b + 41 + 7)))
        (FX := add (add (add gENS (mulC 3 gE)) gW) (add (mul (var (b + 27)) gNS) (var (b + 41 + 9))))
        (iX := var (b + 41 + 1)) (vX := var (b + 41 + 3))
        (Y := .track (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) (P - 1) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)) rfl (u := u) (by rw [hstk]; exact hu [P, P - 1])
        (by rw [hstk, evS (show (odd (var (b + 41 + 7))).Bnd (b + 49) from show _ < _ by omega),
              eval_odd, eval_var, h5, (labOf_val t ht).1])
        (by
          simp only [eval_add, eval_mulC, eval_mul, eval_var, hG2.eENS, hG2.eE, hG2.eW, hG2.eNS]
          rw [hstk, getD_app_lt _ (by rw [hSl]; omega), hlt (b + 27) (by omega), hc.2.2.1,
            show b + 41 + 9 = SS.length + 1 by rw [hSl], getD_app]
          rfl)
        (by rw [hstk, evS (show (var (b + 41 + 1)).Bnd (b + 49) from show _ < _ by omega), eval_var,
              h3]; rfl)
        (by rw [hstk, evS (show (var (b + 41 + 3)).Bnd (b + 49) from show _ < _ by omega), eval_var,
              h4]; exact (regVal_toBlk hv).symm)
      rewrite [hA, if_pos (valid_prev_of_upd (Iv M x s ℓ H) (ε : ZMod 2) hV hp _)]
      rfl
  · rw [if_neg (fun h => hV (hvalid.mp h)), if_neg hV]

end Lax119563Proofs.Reduction
