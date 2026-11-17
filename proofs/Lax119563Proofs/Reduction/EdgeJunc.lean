import Lax119563Proofs.Reduction.EdgeCand

/-!
# The edge pass: shared parts and the `junc` kind

* `schCtx_match`: the numbers of a schema stack (ternary flag, locations, mask of the first
  permutation; the other permutations are the identity);
* `shiftX`: the shift `shiftVal s ℓ m i` of the first permutation (`field` for `i < s`, the
  XOR of all fields for `i = s`, unrolled over the constant `s`), `permVX`;
* `uX`: the number of the current slot;
* `edgeJunc`: the hub edge pass of the `junc` families, `out_edgeJunc`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Matrix

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

lemma schCtx_match {ρ τ : List ℕ} {b e : ℕ} {sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations}
    (hc : SchCtx M x s ℓ H b ρ τ e sc) :
    (isTern sc = true ↔ τ.getD (b + 28) 0 = 1) ∧ (locU sc).val = τ.getD (b + 29) 0 ∧
      (locV sc).val = τ.getD (b + 30) 0 ∧ (locEnd sc).val = τ.getD (b + 31) 0 ∧
      PermDesc (permU sc) (τ.getD (b + 32) 0) ∧ PermId (permV sc) ∧ PermId (permEnd sc) := by
  obtain ⟨g, -, hm⟩ := hc.2.2.2
  simp only [getD_drop'] at hm
  refine ⟨?_, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2.1⟩
  rw [hm.1]; simp

@[simp] lemma Xp.eval_half' {ρ : List ℕ} (a : Xp) : (half a).eval ρ = a.eval ρ / 2 := rfl

/-! ## The shift of the first permutation -/

/-- `field m k ℓ`. -/
def fieldmX (mX kX : Xp) : Xp := xorM (shr mX kX) (const 0) gℓ

/-- `xorFields ℓ k m`. -/
def xfX (mX : Xp) : ℕ → Xp
  | 0 => const 0
  | k + 1 => xorM (xfX mX k) (fieldmX mX (mulC k gℓ)) gℓ

/-- `shiftVal s ℓ m i`. -/
def shiftX (s : ℕ) (mX iX : Xp) : Xp :=
  add (mul (fieldmX mX (mul iX gℓ)) (lt iX (const s))) (mul (xfX mX s) (not (lt iX (const s))))

/-- The register value of the image of `(i, v)` under the first permutation. -/
def permVX (s : ℕ) (mX iX vX : Xp) : Xp := xorM vX (shiftX s mX iX) gℓ

lemma field_lt' (m k ℓ : ℕ) : field m k ℓ < 2 ^ ℓ := Nat.mod_lt _ (by positivity)

lemma xorFields_lt (m : ℕ) : ∀ k, xorFields ℓ k m < 2 ^ ℓ
  | 0 => by simp [xorFields]
  | k + 1 => Nat.xor_lt_two_pow (xorFields_lt m k) (field_lt' _ _ _)

lemma shiftVal_lt (m i : ℕ) : shiftVal s ℓ m i < 2 ^ ℓ := by
  unfold shiftVal; split_ifs
  · exact field_lt' _ _ _
  · exact xorFields_lt _ _

section Eval

variable {σ : List ℕ} (hG : GlobOK M x s ℓ H σ)
include hG

lemma eval_fieldmX (mX kX : Xp) : (fieldmX mX kX).eval σ = field (mX.eval σ) (kX.eval σ) ℓ := by
  simp [fieldmX, hG.eℓ, field]

lemma eval_xfX (mX : Xp) : ∀ k, (xfX mX k).eval σ = xorFields ℓ k (mX.eval σ)
  | 0 => rfl
  | k + 1 => by
    simp only [xfX, eval_xorM, eval_xfX mX k, eval_fieldmX hG, eval_mulC, hG.eℓ, xorFields]
    exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (xorFields_lt _ _) (field_lt' _ _ _))

lemma eval_shiftX (mX iX : Xp) :
    (shiftX s mX iX).eval σ = shiftVal s ℓ (mX.eval σ) (iX.eval σ) := by
  simp only [shiftX, eval_add, eval_mul, eval_fieldmX hG, eval_xfX hG, eval_lt_eq, eval_const,
    eval_not, hG.eℓ, shiftVal]
  by_cases h : iX.eval σ < s <;> simp [h, Nat.mul_comm]

lemma eval_permVX (mX iX vX : Xp) (hv : vX.eval σ < 2 ^ ℓ) :
    (permVX s mX iX vX).eval σ = vX.eval σ ^^^ shiftVal s ℓ (mX.eval σ) (iX.eval σ) := by
  simp only [permVX, eval_xorM, eval_shiftX hG, hG.eℓ]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hv (shiftVal_lt _ _))

end Eval

lemma valid_nameOfEff_sum (I : ImplicitParitySystem (s + 1) ℓ) (ε : ZMod 2)
    {e : Fin I.schemas.length} {c : Coord (s + 1) ℓ} (h : isTern (sch I e) = true)
    (hd : c ∈ dom I e) (r : ZMod 2) : Valid I (nameOfEff I ε (.sum e c) r) :=
  (valid_nameOfEff_plain I ε rfl rfl r).mpr ⟨h, hd⟩

lemma valid_sum_of_junc (I : ImplicitParitySystem (s + 1) ℓ) (ε : ZMod 2)
    {e : Fin I.schemas.length} {c : Coord (s + 1) ℓ} {l : Lab} (h : Valid I (.junc e c, l))
    (r : ZMod 2) : Valid I (nameOfEff I ε (.sum e c) r) :=
  valid_nameOfEff_sum I ε ((valid_junc_iff I).mp h).1 ((valid_junc_iff I).mp h).2 r

/-! ## The slot number -/

/-- The number of the slot with family `F` (slot loops entered at depth `d`). -/
def uX (s d : ℕ) (FX : Xp) : Xp := numX s (var (d + 7)) FX (var (d + 1)) (var (d + 3))

/-! ## The `junc` kind -/

namespace Gn

/-- The edges of a `junc` slot (slot loops at depth `b + 37`). -/
def edgeJuncBody (s ε b : ℕ) : Gn :=
  let d := b + 37
  let u := uX s d (add gENS (var (b + 27)))
  ite (and (ternX b) (inDomX d))
    (seqL [coordGen s ε u (var (b + 29)) (var (d + 1))
        (permVX s (var (b + 32)) (var (d + 1)) (var (d + 3))) (odd (var (d + 7))),
      coordGen s ε u (var (b + 30)) (var (d + 1)) (var (d + 3)) (half (var (d + 7))),
      plainGen s u (odd (add (odd (var (d + 7))) (half (var (d + 7)))))
        (add (add (add gENS (mulC 2 gE)) gW) (var (b + 27))) (var (d + 1)) (var (d + 3))])
    skip

/-- The edges of the `junc` families. -/
def edgeJunc (M : Machine) (s ε b : ℕ) : Gn := schSlots M s b (edgeJuncBody s ε b)

end Gn

lemma labOf_val (t : ℕ) (ht : t < 4) :
    (labOf t).1.val = t % 2 ∧ (labOf t).2.val = t / 2 ∧
      ((labOf t).1 + (labOf t).2).val = (t % 2 + t / 2) % 2 := by
  refine ⟨rfl, show t / 2 % 2 = t / 2 by omega, ?_⟩
  rw [ZMod.val_add]
  show (t % 2 + t / 2 % 2) % 2 = _
  rw [show t / 2 % 2 = t / 2 by omega]

theorem out_edgeJunc {ρ : List ℕ} {b ε : ℕ} (hρ : ρ.length = b) (hG : GlobOK M x s ℓ H ρ)
    (hℓ : 0 < ℓ) (hs : 1 ≤ s) (hε : ε ≤ 1) :
    (Gn.edgeJunc M s ε b).out x ρ =
      (List.range (Iv M x s ℓ H).schemas.length).flatMap fun e =>
        slotL s ℓ fun i v t => edgesOf (Iv M x s ℓ H) (ε : ZMod 2)
          (slotNum s ℓ ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ + e) i v t) := by
  refine out_schSlots hρ hG _ _ ?_
  intro e he τ hc i hi v hv t ht
  have hGσ : GlobOK M x s ℓ H (slotStk s ℓ x τ (violAt s b (b + 37)) i v t) := (hG.of_take hρ hc.2.1).append _
  obtain ⟨h1, h2, h3, h4, h5⟩ := schSlot_facts hG hρ hc (List.take_of_length_le (by rw [hc.1]))
    hc.1 le_rfl hℓ t hi hv
  obtain ⟨m1, m2, m3, -, m5, m6, -⟩ := schCtx_match hc
  have hlt : ∀ k, k < b + 37 → (slotStk s ℓ x τ (violAt s b (b + 37)) i v t).getD k 0 = τ.getD k 0 := fun k hk =>
    slotStk_lt _ _ _ _ (by rw [hc.1]; omega)
  have hX : famNum (Iv M x s ℓ H) (.junc (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)) = (Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ + e := rfl
  rw [← hX, edgesOf_hub_slot (Iv M x s ℓ H) hs (ternOrdered_compile _ _ _) _ (X := .junc (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)) trivial rfl hi
    hv ht rfl, hX]
  have hu : (uX s (b + 37) (add gENS (var (b + 27)))).eval (slotStk s ℓ x τ (violAt s b (b + 37)) i v t) =
      slotNum s ℓ ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ + e) i v t := by
    rw [uX, eval_numX hGσ]
    simp only [eval_var, eval_add, h3, h4, h5, hGσ.eENS, hlt (b + 27) (by omega), hc.2.2.1]
    simp [slotNum]
  have hvalid : (and (ternX b) (inDomX (b + 37))).eval (slotStk s ℓ x τ (violAt s b (b + 37)) i v t) ≠ 0 ↔ Valid (Iv M x s ℓ H) (.junc (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ), labOf t) := by
    rw [ternX, inDomX, eval_and' (eval_eq' _ _) (eval_eq' _ _), ite_ne_zero_iff]
    simp only [eval_var, eval_const]
    rw [h1, h2, valid_junc_iff]
    rfl
  simp only [Gn.edgeJuncBody, Gn.out]
  by_cases hV : Valid (Iv M x s ℓ H) (.junc (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ), labOf t)
  · rw [if_pos (hvalid.mpr hV), if_pos hV]
    simp only [Gn.out_seqL, List.flatMap_cons, List.flatMap_nil, List.append_nil, nbrCand]
    have hPU := m5 ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)
    have hb32 := hlt (b + 32) (by omega)
    have hA := out_coordGen (wX := var (b + 29)) (iX := var (b + 37 + 1))
      (vX := permVX s (var (b + 32)) (var (b + 37 + 1)) (var (b + 37 + 3)))
      (rX := odd (var (b + 37 + 7))) hGσ hε (locU (sch (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length))) ((permU (sch (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length))).apply ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ))
      (labOf t).1 hu (by rw [eval_var, hlt (b + 29) (by omega), ← m2]) (by rw [eval_var, h3, hPU.1])
      (by rw [eval_permVX hGσ _ _ _ (by rw [eval_var, h4]; exact hv)]
          simp only [eval_var]
          rw [h3, h4, hb32, hPU.2, regVal_toBlk hv])
      (by rw [eval_odd, eval_var, h5, (labOf_val t ht).1])
    have hB := out_coordGen (wX := var (b + 30)) (iX := var (b + 37 + 1))
      (vX := var (b + 37 + 3)) (rX := half (var (b + 37 + 7))) hGσ hε (locV (sch (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length))) ((permV (sch (Iv M x s ℓ H) (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length))).apply ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ))
      (labOf t).2 hu (by rw [eval_var, hlt (b + 30) (by omega), ← m3]) (by rw [eval_var, h3, m6 ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)])
      (by rw [eval_var, h4, m6 ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ), regVal_toBlk hv])
      (by rw [Xp.eval_half', eval_var, h5, (labOf_val t ht).2.1])
    have hval := valid_sum_of_junc (Iv M x s ℓ H) (ε : ZMod 2) hV ((labOf t).1 + (labOf t).2)
    have hC : (Gn.plainGen s (uX s (b + 37) (add gENS (var (b + 27))))
        (odd (add (odd (var (b + 37 + 7))) (half (var (b + 37 + 7)))))
        (add (add (add gENS (mulC 2 gE)) gW) (var (b + 27))) (var (b + 37 + 1))
        (var (b + 37 + 3))).out x (slotStk s ℓ x τ (violAt s b (b + 37)) i v t) =
        candOut (Iv M x s ℓ H) (ε : ZMod 2) (slotNum s ℓ ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ + e) i v t)
          (.sum (⟨e, he⟩ : Fin (Iv M x s ℓ H).schemas.length) ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ)) ((labOf t).1 + (labOf t).2) := by
      rw [candOut_of_valid _ hval]
      refine out_plainGen (Iv M x s ℓ H) hGσ rfl hu ?_ ?_ (by rw [eval_var, h3]; rfl)
        (by rw [eval_var, h4]; exact (regVal_toBlk hv).symm)
      · simp only [eval_odd, eval_add, Xp.eval_half', eval_var, h5, (labOf_val t ht).2.2]
      · simp only [eval_add, eval_mulC, eval_var, hGσ.eENS, hGσ.eE, hGσ.eW,
          hlt (b + 27) (by omega), hc.2.2.1]
        rfl
    rw [hA, hB, hC]
    simp only [candOut]
  · rw [if_neg (fun h => hV (hvalid.mp h)), if_neg hV]

end Lax119563Proofs.Reduction
