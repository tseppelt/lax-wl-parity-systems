import Lax119563Proofs.Reduction.SlotPass

/-!
# Candidate neighbours as generators

`candOut I ε u Y r` is the contribution `[u, num (nameOfEff ε Y r)]` of a candidate neighbour
`(Y, r)` of the hub slot `u` (empty if the name is invalid).

* `plainGen`: a candidate that is not a coordinate class (always valid in our uses; no
  initial seed), `out_plainGen`;
* `coordGen`: a coordinate candidate `coord w c` of the compiled time program: its seed is `1`
  exactly at the detector output on block `0` (`initSeed_Iv`), it is valid unless `w` is
  initialised and the effective label is `1` (`out_coordGen`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Matrix

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

open Classical in
/-- The contribution of a candidate neighbour. -/
noncomputable def candOut (I : ImplicitParitySystem (s + 1) ℓ) (ε : ZMod 2) (u : ℕ) (Y : ICls I)
    (r : ZMod 2) : List ℕ :=
  if Valid I (nameOfEff I ε Y r) then [u, num I (nameOfEff I ε Y r)] else []

/-- The number `lab + 4 ((i + (s+1) F) 2^ℓ + v)`. -/
def numX (s : ℕ) (labX FX iX vX : Xp) : Xp :=
  add labX (mulC 4 (add (shl (add iX (mulC (s + 1) FX)) gℓ) vX))

lemma eval_numX {σ : List ℕ} (hG : GlobOK M x s ℓ H σ) (labX FX iX vX : Xp) :
    (numX s labX FX iX vX).eval σ =
      labX.eval σ + 4 * ((iX.eval σ + (s + 1) * FX.eval σ) * 2 ^ ℓ + vX.eval σ) := by
  simp [numX, hG.eℓ]

namespace Gn

/-- Emit `[u, n]`. -/
def pairGen (uX nX : Xp) : Gn := .seq (.emit uX) (.emit nX)

/-- A plain candidate. -/
def plainGen (s : ℕ) (uX labX FX iX vX : Xp) : Gn := pairGen uX (numX s labX FX iX vX)

/-- The seed bit of a coordinate candidate. -/
def seedX (wX iX : Xp) : Xp := and (eq wX gdet) (eq iX (const 0))

/-- The effective label of a coordinate candidate. -/
def effX (ε : ℕ) (wX iX rX : Xp) : Xp := odd (add rX (mulC ε (seedX wX iX)))

/-- A coordinate candidate `coord w c` (block `i`, register value `v`, label `r`). -/
def coordGen (s ε : ℕ) (uX wX iX vX rX : Xp) : Gn :=
  when (or (not (or (eq wX gacc) (eq wX gdet))) (eq (effX ε wX iX rX) (const 0)))
    (pairGen uX (numX s (effX ε wX iX rX) (add (add gENS (mulC 2 gE)) wX) iX vX))

end Gn

lemma zmod2_val_lt (a : ZMod 2) : a.val < 2 := ZMod.val_lt a

lemma zmod2_sub_val (r ε a : ZMod 2) : (r - ε * a).val = (r.val + ε.val * a.val) % 2 := by
  fin_cases r <;> fin_cases ε <;> fin_cases a <;> rfl

lemma zmod2_eq_zero_iff_val (a : ZMod 2) : a = 0 ↔ a.val = 0 := (ZMod.val_eq_zero a).symm

/-! ## The seed of the compiled time program -/

lemma initSeed_Iv (w : Fin (Iv M x s ℓ H).numLocations) (c : Coord (s + 1) ℓ) :
    (initSeed (Iv M x s ℓ H) w c).val =
      if w.val = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 ∧ c.1.val = 0 then 1
      else 0 := by
  have e1 : ((APv M x s ℓ H).loc (.prog (APv M x s ℓ H).accept)).val =
      (Loc.code (Loc.accept : Loc M H)).val := loc_prog_val _ _ _ _ _ _
  have e2 : ((APv M x s ℓ H).loc (.det .out)).val =
      numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 := by
    rw [loc_det_val, AP_commands]
    erw [List.length_map]
    show numLoc M H + _ + 3 = _
    ring
  unfold initSeed
  show (match (APv M x s ℓ H).compiledInit w with
    | some b => if (c.1 : ℕ) = 0 then b else 0
    | none => 0 : ZMod 2).val = _
  unfold RegisterProgram.compiledInit
  split_ifs with h1 h2 h3 h4 h5 <;> simp_all
  · have := (Loc.code (Loc.accept : Loc M H)).isLt; omega
  · rfl
  · rename_i h; exact h5 (Fin.ext (h.1.trans e2.symm))

/-! ## Outputs -/

lemma out_plainGen (I : ImplicitParitySystem (s + 1) ℓ) {σ : List ℕ} (hG : GlobOK M x s ℓ H σ)
    {uX labX FX iX vX : Xp} {u : ℕ} {ε : ZMod 2} {Y : ICls I} {r : ZMod 2}
    (hinit : initBit I Y = 0) (hu : uX.eval σ = u) (hlab : labX.eval σ = r.val)
    (hF : FX.eval σ = famNum I Y) (hi : iX.eval σ = (coordOf I Y).1.val)
    (hv : vX.eval σ = regVal (coordOf I Y).2) :
    (Gn.plainGen s uX labX FX iX vX).out x σ = [u, num I (nameOfEff I ε Y r)] := by
  simp only [Gn.plainGen, Gn.pairGen, Gn.out, List.singleton_append]
  rw [eval_numX hG, num_nameOfEff, hinit, hu, hlab, hF, hi, hv]
  simp [classNum]

lemma candOut_of_valid (I : ImplicitParitySystem (s + 1) ℓ) {ε : ZMod 2} {u : ℕ} {Y : ICls I}
    {r : ZMod 2} (h : Valid I (nameOfEff I ε Y r)) :
    candOut I ε u Y r = [u, num I (nameOfEff I ε Y r)] := by
  rw [candOut, if_pos h]

lemma natCast_zmod2_val {ε : ℕ} (hε : ε ≤ 1) : ((ε : ZMod 2)).val = ε := by
  rw [ZMod.val_natCast]; omega

lemma out_coordGen {σ : List ℕ} (hG : GlobOK M x s ℓ H σ) {uX wX iX vX rX : Xp} {u ε : ℕ}
    (hε : ε ≤ 1) (w : Fin (Iv M x s ℓ H).numLocations) (c : Coord (s + 1) ℓ) (r : ZMod 2)
    (hu : uX.eval σ = u) (hw : wX.eval σ = w.val) (hi : iX.eval σ = c.1.val)
    (hv : vX.eval σ = regVal c.2) (hr : rX.eval σ = r.val) :
    (Gn.coordGen s ε uX wX iX vX rX).out x σ = candOut (Iv M x s ℓ H) (ε : ZMod 2) u (.coord w c) r := by
  classical
  set det := numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3
  set acc := (Loc.code (Loc.accept : Loc M H)).val
  set a : ℕ := if w.val = det ∧ c.1.val = 0 then 1 else 0 with ha
  have hseed : (Gn.seedX wX iX).eval σ = a := by
    rw [Gn.seedX, eval_and' (eval_eq' _ _) (eval_eq' _ _), hw, hi, hG.edet]
    simp [ha, det]
  have heff : (Gn.effX ε wX iX rX).eval σ = (r.val + ε * a) % 2 := by
    simp only [Gn.effX, eval_odd, eval_add, eval_mulC, hseed, hr]
  have hval : (r - (ε : ZMod 2) * initSeed (Iv M x s ℓ H) w c).val = (r.val + ε * a) % 2 := by
    rw [zmod2_sub_val, natCast_zmod2_val hε, initSeed_Iv]
  have hok : (or (not (or (eq wX gacc) (eq wX gdet))) (eq (Gn.effX ε wX iX rX) (const 0))).eval σ
      = if ¬ (w.val = acc ∨ w.val = det) ∨ (r.val + ε * a) % 2 = 0 then 1 else 0 := by
    rw [eval_or' (eval_not' (eval_or' (eval_eq' _ _) (eval_eq' _ _))) (eval_eq' _ _), hw, hG.eacc,
      hG.edet, heff]
    rfl
  rw [candOut, valid_nameOfEff_coord _ _ w c rfl, Iv_init_isSome, zmod2_eq_zero_iff_val, hval]
  simp only [Gn.coordGen, Gn.out_when, hok, Gn.pairGen, Gn.out, List.singleton_append]
  have hnum : num (Iv M x s ℓ H) (nameOfEff (Iv M x s ℓ H) (ε : ZMod 2) (.coord w c) r) =
      (numX s (Gn.effX ε wX iX rX) (add (add gENS (mulC 2 gE)) wX) iX vX).eval σ := by
    rw [eval_numX hG, num_nameOfEff, heff, hi, hv]
    show (r - (ε : ZMod 2) * initSeed (Iv M x s ℓ H) w c).val + _ = _
    rw [hval]
    simp [classNum, famNum, coordOf, hG.eENS, hG.eE, hw]
  rw [hnum, hu]
  by_cases h : w.val = acc ∨ w.val = det
  · by_cases h2 : (r.val + ε * a) % 2 = 0
    · simp only [h, h2, not_true, or_true, if_true, ne_eq, one_ne_zero, not_false_eq_true,
        implies_true]
    · have h3 : ¬ (¬ (w.val = acc ∨ w.val = det) ∨ (r.val + ε * a) % 2 = 0) := by tauto
      have h4 : ¬ ((w.val = acc ∨ w.val = det) → (r.val + ε * a) % 2 = 0) := fun h' => h2 (h' h)
      rw [if_neg h3, if_neg h4]
      simp
  · have h3 : ¬ (w.val = acc ∨ w.val = det) ∨ (r.val + ε * a) % 2 = 0 := Or.inl h
    have h4 : (w.val = acc ∨ w.val = det) → (r.val + ε * a) % 2 = 0 := fun h' => absurd h' h
    rw [if_pos h3, if_pos h4]
    simp

end Lax119563Proofs.Reduction
