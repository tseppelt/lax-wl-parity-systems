import Lax119563Proofs.Reduction.PassBase

/-!
# The colour pass: generic parts

* `colBody valid F i v`: emits the colour `2 ((i + (s+1) F) 2^ℓ + v) + 2` if `valid ≠ 0`, else `1`
  (`out_colBody`: this is `outColor` of the slot when `valid` decides `OutValid`);
* `violAt s b d`: the domain test of the schema record of a schema stack (levels `b + 28 …`)
  at the slot coordinate, run at depth `d + 6` inside `slotLoops` (`violAt_nil_iff`);
* `colSch`: a pass over the families of a kind indexed by schemas (`out_colSch`);
* `colStep`: a pass over the families of a kind indexed by `(schema, step)`, the step loop
  being `q < s + 2`, `j < s + ℓ` (`out_colStep`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Matrix

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

lemma ite_ne_zero_iff {P : Prop} [Decidable P] : ((if P then 1 else 0 : ℕ) ≠ 0) ↔ P := by
  split_ifs with h <;> simp [h]

lemma GlobOK.of_take {ρ τ : List ℕ} {b : ℕ} (h : GlobOK M x s ℓ H ρ) (hρ : ρ.length = b)
    (ht : τ.take b = ρ) : GlobOK M x s ℓ H τ := by
  have hb := hρ ▸ h.le
  unfold GlobOK
  rw [← h, ← ht, List.take_take, Nat.min_eq_left hb]

/-! ## The colour of a slot -/

/-- The colour of a valid slot. -/
def colX (s : ℕ) (FX iX vX : Xp) : Xp :=
  add (mulC 2 (add (shl (add iX (mulC (s + 1) FX)) gℓ) vX)) (const 2)

namespace Gn

/-- Emit the colour of the slot. -/
def colBody (s : ℕ) (validX FX iX vX : Xp) : Gn :=
  .ite validX (.emit (colX s FX iX vX)) (.emit (const 1))

end Gn

lemma out_colBody (I : ImplicitParitySystem (s + 1) ℓ) {σ : List ℕ} (hG : GlobOK M x s ℓ H σ)
    {validX FX iX vX : Xp} {F i v t : ℕ} (ht : t < 4)
    (hvalid : validX.eval σ ≠ 0 ↔ OutValid I (slotNum s ℓ F i v t))
    (hF : FX.eval σ = F) (hi : iX.eval σ = i) (hv : vX.eval σ = v) :
    (Gn.colBody s validX FX iX vX).out x σ = [outColor I (slotNum s ℓ F i v t)] := by
  classical
  rw [outColor_slotNum I ht]
  simp only [Gn.colBody, Gn.out, colX, eval_add, eval_mulC, eval_shl, eval_const, hF, hi, hv,
    hG.eℓ]
  by_cases h : OutValid I (slotNum s ℓ F i v t)
  · rw [if_pos (hvalid.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hvalid.mp h')), if_neg h]

/-! ## The domain test -/

/-- The domain violations of the schema of a schema stack (record at `b + 28 …`) at the
coordinate of the slot loops entered at depth `d`. -/
def violAt (s b d : ℕ) : Gn :=
  violGen s (d + 6) (var (d + 1)) (var (d + 3)) (var (d + 4)) (var (b + 33)) (var (b + 34))
    (var (b + 35)) (var (b + 36)) gℓ gH

lemma violAt_nil_iff {ρ τ τ' : List ℕ} {b d e : ℕ}
    {sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations}
    (hG : GlobOK M x s ℓ H ρ) (hρ : ρ.length = b) (hctx : SchCtx M x s ℓ H b ρ τ e sc)
    (hτ' : τ'.take (b + 37) = τ) (hd : τ'.length = d) (hbd : b + 37 ≤ d) (hℓ : 0 < ℓ)
    {i v : ℕ} (hi : i < s + 1) (hv : v < 2 ^ ℓ) :
    (violAt s b d).out x (τ' ++ [s + 1, i, 2 ^ ℓ, v, inBit x v, 0]) = [] ↔
      ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) ∈ sc.domain := by
  have hb := hρ ▸ hG.le
  have hGτ : GlobOK M x s ℓ H τ := hG.of_take hρ hctx.2.1
  have hGτ' : GlobOK M x s ℓ H τ' := hGτ.of_take hctx.1 hτ'
  have hGσ := hGτ'.append [s + 1, i, 2 ^ ℓ, v, inBit x v, 0]
  subst hd
  refine violGen_nil_iff_mem (τ := τ) hctx.1 hctx.2.2.2 (by simp) ?_ (by omega) ?_ _ ?_ ?_ ?_
    hGσ.eℓ hGσ.eH hℓ
  · rw [List.take_append_of_le_length hbd, hτ']
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨show _ < _ by simp, show _ < _ by simp, show _ < _ by simp,
      bnd_glob (by omega) (by simp; omega), bnd_glob (by omega) (by simp; omega)⟩
  · simp
  · simp [regVal_toBlk hv]
  · simp [regVal_toBlk hv]

/-! ## Passes over schema-indexed families -/

namespace Gn

/-- The colour pass over the families `off + e` (`e` a schema). -/
def colSch (M : Machine) (s b : ℕ) (off validX : Xp) : Gn :=
  schEnum M s b gH gR gN gr gp0 gEc
    (slotLoops s gP (violAt s b (b + 37))
      (colBody s validX (add off (var (b + 27))) (var (b + 38)) (var (b + 40))))

end Gn

theorem out_colSch {ρ : List ℕ} {b : ℕ} (hρ : ρ.length = b) (hG : GlobOK M x s ℓ H ρ)
    {off validX : Xp} {O : ℕ} (hoffb : off.Bnd b) (hoff : off.eval ρ = O)
    (hvalid : ∀ e (he : e < (Iv M x s ℓ H).schemas.length) τ,
      SchCtx M x s ℓ H b ρ τ e (sch (Iv M x s ℓ H) ⟨e, he⟩) →
      ∀ i < s + 1, ∀ v < 2 ^ ℓ, ∀ t < 4,
        (validX.eval (slotStk s ℓ x τ (violAt s b (b + 37)) i v t) ≠ 0 ↔
          OutValid (Iv M x s ℓ H) (slotNum s ℓ (O + e) i v t))) :
    (Gn.colSch M s b off validX).out x ρ =
      (List.range (Iv M x s ℓ H).schemas.length).flatMap fun e =>
        slotL s ℓ fun i v t => [outColor (Iv M x s ℓ H) (slotNum s ℓ (O + e) i v t)] := by
  obtain ⟨T, hT, hctx⟩ := schEnum_ctx hρ hG
  rw [Gn.colSch, hT]
  refine List.flatMap_congr fun e he => ?_
  rw [List.mem_range] at he
  have hc := hctx e he
  have hGτ : GlobOK M x s ℓ H (T e) := hG.of_take hρ hc.2.1
  have hb := hρ ▸ hG.le
  rw [out_slotLoops (bnd_glob (by omega) (by rw [hc.1]; omega)) hGτ.eP]
  unfold slotL
  refine List.flatMap_congr fun i hi => List.flatMap_congr fun v hv =>
    List.flatMap_congr fun t ht => ?_
  rw [List.mem_range] at hi hv ht
  have hGσ := hGτ.append [s + 1, i, 2 ^ ℓ, v, inBit x v,
    ((violAt s b (b + 37)).out x (T e ++ [s + 1, i, 2 ^ ℓ, v, inBit x v, 0])).length, 4, t]
  have hS := slotStk_getD (s := s) (ℓ := ℓ) (x := x) (τ := T e) (violAt s b (b + 37)) i v t
  rw [hc.1] at hS
  refine out_colBody _ hGσ ht (hvalid e he _ hc i hi v hv t ht) ?_ hS.1 hS.2.1
  have h1 : off.eval (T e) = O := by
    rw [← List.take_append_drop b (T e), hc.2.1, eval_append hρ _ hoffb, hoff]
  simp only [eval_add, eval_var]
  rw [getD_app_lt _ (by rw [hc.1]; omega), hc.2.2.1,
    eval_append rfl _ (hoffb.mono (by rw [hc.1]; omega)), h1]

/-! ## Passes over `(schema, step)`-indexed families -/

/-- The family `off + e NS + q (s + ℓ) + j` in the step loops. -/
def stepFX (s b : ℕ) (off : Xp) : Xp :=
  add off (add (mul (var (b + 27)) gNS) (add (mul (var (b + 38)) (add (const s) gℓ)) (var (b + 40))))

namespace Gn

/-- The step loops `q < s + 2`, `j < s + ℓ` (entered at depth `b + 37`). -/
def stepLoops (s : ℕ) (body : Gn) : Gn :=
  .loop (const (s + 2)) (.loop (add (const s) gℓ) body)

/-- The colour pass over the families `off + e NS + σ`. -/
def colStep (M : Machine) (s b : ℕ) (off validX : Xp) : Gn :=
  schEnum M s b gH gR gN gr gp0 gEc
    (stepLoops s (slotLoops s gP (violAt s b (b + 41))
      (colBody s validX (stepFX s b off) (var (b + 42)) (var (b + 44)))))

end Gn

lemma numSteps_succ (s ℓ : ℕ) : numSteps (s + 1) ℓ = (s + 2) * (s + ℓ) := by
  simp [numSteps]

lemma out_stepLoops {τ : List ℕ} (hG : GlobOK M x s ℓ H τ) (body : Gn) :
    (Gn.stepLoops s body).out x τ = (List.range (s + 2)).flatMap fun q =>
      (List.range (s + ℓ)).flatMap fun j => body.out x (τ ++ [s + 2, q, s + ℓ, j]) := by
  simp only [Gn.stepLoops, Gn.out, eval_const, eval_add, (hG.append _).eℓ, List.append_assoc,
    List.cons_append, List.nil_append]

theorem out_colStep {ρ : List ℕ} {b : ℕ} (hρ : ρ.length = b) (hG : GlobOK M x s ℓ H ρ)
    {off validX : Xp} {O : ℕ} (hoffb : off.Bnd b) (hoff : off.eval ρ = O)
    (hvalid : ∀ e (he : e < (Iv M x s ℓ H).schemas.length) τ,
      SchCtx M x s ℓ H b ρ τ e (sch (Iv M x s ℓ H) ⟨e, he⟩) →
      ∀ q < s + 2, ∀ j < s + ℓ, ∀ i < s + 1, ∀ v < 2 ^ ℓ, ∀ t < 4,
        (validX.eval (slotStk s ℓ x (τ ++ [s + 2, q, s + ℓ, j]) (violAt s b (b + 41)) i v t) ≠ 0 ↔
          OutValid (Iv M x s ℓ H)
            (slotNum s ℓ (O + (e * numSteps (s + 1) ℓ + (q * (s + ℓ) + j))) i v t))) :
    (Gn.colStep M s b off validX).out x ρ =
      (List.range ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ)).flatMap fun F =>
        slotL s ℓ fun i v t => [outColor (Iv M x s ℓ H) (slotNum s ℓ (O + F) i v t)] := by
  obtain ⟨T, hT, hctx⟩ := schEnum_ctx hρ hG
  rw [Gn.colStep, hT, range_mul_flatMap]
  refine List.flatMap_congr fun e he => ?_
  rw [List.mem_range] at he
  have hc := hctx e he
  have hGτ : GlobOK M x s ℓ H (T e) := hG.of_take hρ hc.2.1
  have hb := hρ ▸ hG.le
  rw [out_stepLoops hGτ, show List.range (numSteps (s + 1) ℓ) = List.range ((s + 2) * (s + ℓ))
    by rw [numSteps_succ], range_mul_flatMap]
  refine List.flatMap_congr fun q hq => List.flatMap_congr fun j hj => ?_
  rw [List.mem_range] at hq hj
  have hGτ' := hGτ.append [s + 2, q, s + ℓ, j]
  have hlen : (T e ++ [s + 2, q, s + ℓ, j]).length = b + 41 := by simp [hc.1]
  rw [out_slotLoops (bnd_glob (by omega) (by rw [hlen]; omega)) hGτ'.eP]
  unfold slotL
  refine List.flatMap_congr fun i hi => List.flatMap_congr fun v hv =>
    List.flatMap_congr fun t ht => ?_
  rw [List.mem_range] at hi hv ht
  have hGσ := hGτ'.append [s + 1, i, 2 ^ ℓ, v, inBit x v,
    ((violAt s b (b + 41)).out x (T e ++ [s + 2, q, s + ℓ, j] ++
      [s + 1, i, 2 ^ ℓ, v, inBit x v, 0])).length, 4, t]
  have hS := slotStk_getD (s := s) (ℓ := ℓ) (x := x) (τ := T e ++ [s + 2, q, s + ℓ, j])
    (violAt s b (b + 41)) i v t
  rw [hlen] at hS
  refine out_colBody _ hGσ ht (hvalid e he _ hc q hq j hj i hi v hv t ht) ?_ hS.1 hS.2.1
  have h1 : off.eval (T e) = O := by
    rw [← List.take_append_drop b (T e), hc.2.1, eval_append hρ _ hoffb, hoff]
  simp only [stepFX, eval_add, eval_mul, eval_const, hGσ.eℓ, hGσ.eNS]
  simp only [List.append_assoc, List.cons_append, List.nil_append, eval_var]
  rw [eval_append rfl _ (hoffb.mono (by rw [hc.1]; omega)), h1,
    getD_app_lt _ (by rw [hc.1]; omega), hc.2.2.1,
    show b + 38 = (T e).length + 1 by rw [hc.1], show b + 40 = (T e).length + 3 by rw [hc.1],
    getD_app, getD_app]
  simp

end Lax119563Proofs.Reduction
