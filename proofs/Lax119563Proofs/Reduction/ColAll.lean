import Lax119563Proofs.Reduction.ColPass

/-!
# The colour pass

The seven kind passes (`colUpd`, `colJunc`, `colLink`, `colCoord`, `colSum`, `colTrack`,
`colCoef`) and `colPass`, their concatenation. **`out_colPass`**: on a stack starting with the
globals, `colPass` emits `outColor` of `0, …, nOut - 1`, i.e. the colour list of the output
graphs of the compiled code-ordered time program.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Matrix

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

/-! ## Facts on slot stacks under a schema stack -/

lemma schSlot_facts {ρ τ τ' : List ℕ} {b d e : ℕ}
    {sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations}
    (hG : GlobOK M x s ℓ H ρ) (hρ : ρ.length = b) (hctx : SchCtx M x s ℓ H b ρ τ e sc)
    (hτ' : τ'.take (b + 37) = τ) (hd : τ'.length = d) (hbd : b + 37 ≤ d) (hℓ : 0 < ℓ)
    {i v : ℕ} (t : ℕ) (hi : i < s + 1) (hv : v < 2 ^ ℓ) :
    ((slotStk s ℓ x τ' (violAt s b d) i v t).getD (d + 5) 0 = 0 ↔
        ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) ∈ sc.domain) ∧
      ((slotStk s ℓ x τ' (violAt s b d) i v t).getD (b + 28) 0 = 1 ↔ isTern sc = true) ∧
      (slotStk s ℓ x τ' (violAt s b d) i v t).getD (d + 1) 0 = i ∧
      (slotStk s ℓ x τ' (violAt s b d) i v t).getD (d + 3) 0 = v ∧
      (slotStk s ℓ x τ' (violAt s b d) i v t).getD (d + 7) 0 = t := by
  have hS := slotStk_getD (s := s) (ℓ := ℓ) (x := x) (τ := τ') (violAt s b d) i v t
  rw [hd] at hS
  refine ⟨?_, ?_, hS.1, hS.2.1, hS.2.2.2.2⟩
  · rw [hS.2.2.2.1, List.length_eq_zero_iff]
    exact violAt_nil_iff hG hρ hctx hτ' hd hbd hℓ hi hv
  · rw [slotStk_lt _ _ _ _ (by omega), ← getD_take' (n := b + 37) (by omega), hτ',
      show b + 28 = b + 28 + 0 by rfl, ← getD_drop']
    obtain ⟨g, -, hm⟩ := hctx.2.2.2
    rw [hm.1]
    simp

lemma Iv_init_isSome (w : Fin (Iv M x s ℓ H).numLocations) :
    ((Iv M x s ℓ H).init w).isSome = true ↔ w.val = (Loc.code (Loc.accept : Loc M H)).val ∨
      w.val = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 := by
  show ((APv M x s ℓ H).compiledInit w).isSome = true ↔ _
  have e1 : ((APv M x s ℓ H).loc (.prog (APv M x s ℓ H).accept)).val =
      (Loc.code (Loc.accept : Loc M H)).val := loc_prog_val _ _ _ _ _ _
  have e2 : ((APv M x s ℓ H).loc (.det .out)).val =
      numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 := by
    rw [loc_det_val, AP_commands]
    erw [List.length_map]
    show numLoc M H + _ + 3 = _
    ring
  unfold RegisterProgram.compiledInit
  split_ifs with h1 h2
  · have := congrArg Fin.val h1; simp only [Option.isSome_some, true_iff]; left; rw [this, e1]
  · have := congrArg Fin.val h2; simp only [Option.isSome_some, true_iff]; right; rw [this, e2]
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_or]
    exact ⟨fun h => h1 (Fin.ext (h.trans e1.symm)), fun h => h2 (Fin.ext (h.trans e2.symm))⟩

/-! ## Validity expressions -/

/-- The slot coordinate is in the domain (slot loops entered at depth `d`). -/
def inDomX (d : ℕ) : Xp := eq (var (d + 5)) (const 0)

/-- The label has a zero second bit. -/
def lab2X (d : ℕ) : Xp := lt (var (d + 7)) (const 2)

/-- The schema is ternary. -/
def ternX (b : ℕ) : Xp := eq (var (b + 28)) (const 1)

namespace Gn

/-- The `upd` families. -/
def colUpd (M : Machine) (s b : ℕ) : Gn :=
  colStep M s b (const 0)
    (and (inDomX (b + 41)) (entX s (var (b + 40)) (var (b + 42)) (var (b + 44))))

/-- The `junc` families. -/
def colJunc (M : Machine) (s b : ℕ) : Gn :=
  colSch M s b gENS (and (ternX b) (inDomX (b + 37)))

/-- The `link` families. -/
def colLink (M : Machine) (s b : ℕ) : Gn :=
  colSch M s b (add gENS gE) (and (inDomX (b + 37)) (lab2X (b + 37)))

/-- The `sum` families. -/
def colSum (M : Machine) (s b : ℕ) : Gn :=
  colSch M s b (add (add gENS (mulC 2 gE)) gW)
    (and (and (ternX b) (inDomX (b + 37))) (lab2X (b + 37)))

/-- The `track` families. -/
def colTrack (M : Machine) (s b : ℕ) : Gn :=
  colStep M s b (add (add gENS (mulC 3 gE)) gW)
    (and (and (inDomX (b + 41)) (entX s (var (b + 40)) (var (b + 42)) (var (b + 44))))
      (lab2X (b + 41)))

/-- The `coef` families. -/
def colCoef (M : Machine) (s b : ℕ) : Gn :=
  colStep M s b (add (add (mulC 2 gENS) (mulC 3 gE)) gW)
    (and (and (eq (var (b + 42)) (const 0)) (eq (var (b + 44)) (const 0))) (lab2X (b + 41)))

/-- The `coord` families (loop over locations `w < W`, slot loops at depth `b + 2`). -/
def colCoord (s b : ℕ) : Gn :=
  .loop gW (slotLoops s gP skip
    (colBody s (and (lt (var (b + 9)) (const 2))
        (or (eq (var (b + 9)) (const 0)) (not (or (eq (var (b + 1)) gacc) (eq (var (b + 1)) gdet)))))
      (add (add gENS (mulC 2 gE)) (var (b + 1))) (var (b + 3)) (var (b + 5))))

/-- **The colour pass.** -/
def colPass (M : Machine) (s b : ℕ) : Gn :=
  seqL [colUpd M s b, colJunc M s b, colLink M s b, colCoord s b, colSum M s b, colTrack M s b,
    colCoef M s b]

end Gn

/-! ## The kinds -/

lemma bnd_g {ρ : List ℕ} {b : ℕ} (hρ : ρ.length = b) (hG : GlobOK M x s ℓ H ρ) {k : ℕ}
    (hk : k < 18) : (Xp.var k).Bnd b := bnd_glob hk (hρ ▸ hG.le)

lemma mod_step {q j : ℕ} (hj : j < s + ℓ) : (q * (s + ℓ) + j) % (s + ℓ) = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

lemma step_lt {q j : ℕ} (hq : q < s + 2) (hj : j < s + ℓ) :
    q * (s + ℓ) + j < numSteps (s + 1) ℓ := by
  rw [numSteps_succ]
  calc q * (s + ℓ) + j < (q + 1) * (s + ℓ) := by rw [Nat.succ_mul]; omega
    _ ≤ (s + 2) * (s + ℓ) := Nat.mul_le_mul_right _ hq


section Kinds

variable {ρ : List ℕ} {b : ℕ} (hρ : ρ.length = b) (hG : GlobOK M x s ℓ H ρ) (hℓ : 0 < ℓ)
include hρ hG hℓ

theorem out_colJunc :
    (Gn.colJunc M s b).out x ρ =
      (List.range (Iv M x s ℓ H).schemas.length).flatMap fun e =>
        slotL s ℓ fun i v t => [outColor (Iv M x s ℓ H)
          (slotNum s ℓ ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ + e) i v t)] := by
  refine out_colSch hρ hG (bnd_g hρ hG (by omega)) hG.eENS ?_
  intro e he τ hc i hi v hv t ht
  obtain ⟨h1, h2, h3, -, -⟩ := schSlot_facts hG hρ hc (List.take_of_length_le (by rw [hc.1]))
    hc.1 le_rfl hℓ t hi hv
  rw [ternX, inDomX, eval_and' (eval_eq' _ _) (eval_eq' _ _), ite_ne_zero_iff]
  simp only [eval_var, eval_const]
  rw [h1, h2, outValid_junc _ hi hv ht ⟨e, he⟩]
  rfl

theorem out_colLink :
    (Gn.colLink M s b).out x ρ =
      (List.range (Iv M x s ℓ H).schemas.length).flatMap fun e =>
        slotL s ℓ fun i v t => [outColor (Iv M x s ℓ H)
          (slotNum s ℓ ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ +
            (Iv M x s ℓ H).schemas.length + e) i v t)] := by
  refine out_colSch hρ hG ⟨bnd_g hρ hG (by omega), bnd_g hρ hG (by omega)⟩
    (by simp only [eval_add, hG.eENS, hG.eE]) ?_
  intro e he τ hc i hi v hv t ht
  obtain ⟨h1, -, -, -, h5⟩ := schSlot_facts hG hρ hc (List.take_of_length_le (by rw [hc.1]))
    hc.1 le_rfl hℓ t hi hv
  rw [inDomX, lab2X, eval_and' (eval_eq' _ _) (eval_lt_eq _ _), ite_ne_zero_iff]
  simp only [eval_var, eval_const]
  rw [h1, h5, outValid_link _ hi hv ht ⟨e, he⟩]
  rfl

theorem out_colSum :
    (Gn.colSum M s b).out x ρ =
      (List.range (Iv M x s ℓ H).schemas.length).flatMap fun e =>
        slotL s ℓ fun i v t => [outColor (Iv M x s ℓ H)
          (slotNum s ℓ ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ +
            2 * (Iv M x s ℓ H).schemas.length + (Iv M x s ℓ H).numLocations + e) i v t)] := by
  refine out_colSch hρ hG ⟨⟨bnd_g hρ hG (by omega), Xp.bnd_mulC (bnd_g hρ hG (by omega)) _⟩,
    bnd_g hρ hG (by omega)⟩ (by simp only [eval_add, eval_mulC, hG.eENS, hG.eE, hG.eW]) ?_
  intro e he τ hc i hi v hv t ht
  obtain ⟨h1, h2, -, -, h5⟩ := schSlot_facts hG hρ hc (List.take_of_length_le (by rw [hc.1]))
    hc.1 le_rfl hℓ t hi hv
  rw [ternX, inDomX, lab2X, eval_and' (eval_and' (eval_eq' _ _) (eval_eq' _ _)) (eval_lt_eq _ _),
    ite_ne_zero_iff]
  simp only [eval_var, eval_const]
  rw [h1, h2, h5, outValid_sum _ hi hv ht ⟨e, he⟩]
  rfl

theorem out_colUpd :
    (Gn.colUpd M s b).out x ρ =
      (List.range ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ)).flatMap fun F =>
        slotL s ℓ fun i v t => [outColor (Iv M x s ℓ H) (slotNum s ℓ F i v t)] := by
  have := out_colStep (validX := and (inDomX (b + 41))
    (entX s (var (b + 40)) (var (b + 42)) (var (b + 44)))) hρ hG (off := const 0) trivial rfl ?_
  · show (Gn.colStep M s b _ _).out x ρ = _
    simpa only [eval_const, zero_add] using this
  intro e he τ hc q hq j hj i hi v hv t ht
  have hl : (τ ++ [s + 2, q, s + ℓ, j]).length = b + 41 := by simp [hc.1]
  obtain ⟨h1, -, h3, h4, -⟩ := schSlot_facts hG hρ hc
    (by rw [List.take_append_of_le_length (by rw [hc.1]), List.take_of_length_le (by rw [hc.1])])
    hl (by omega) hℓ t hi hv
  have hj' : (slotStk s ℓ x (τ ++ [s + 2, q, s + ℓ, j]) (violAt s b (b + 41)) i v t).getD
      (b + 40) 0 = j := by
    rw [slotStk_lt _ _ _ _ (by rw [hl]; omega), show b + 40 = τ.length + 3 by rw [hc.1], getD_app]
    rfl
  rw [inDomX, eval_and' (eval_eq' _ _) (eval_entX _ _ _), ite_ne_zero_iff]
  simp only [eval_var, eval_const]
  rw [h1, h3, h4, hj', zero_add, outValid_upd _ hi hv ht ⟨e, he⟩ (step_lt hq hj) (by omega),
    mod_step hj]
  rfl

theorem out_colTrack :
    (Gn.colTrack M s b).out x ρ =
      (List.range ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ)).flatMap fun F =>
        slotL s ℓ fun i v t => [outColor (Iv M x s ℓ H)
          (slotNum s ℓ ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ +
            3 * (Iv M x s ℓ H).schemas.length + (Iv M x s ℓ H).numLocations + F) i v t)] := by
  refine out_colStep hρ hG ⟨⟨bnd_g hρ hG (by omega), Xp.bnd_mulC (bnd_g hρ hG (by omega)) _⟩,
    bnd_g hρ hG (by omega)⟩ (by simp only [eval_add, eval_mulC, hG.eENS, hG.eE, hG.eW]) ?_
  intro e he τ hc q hq j hj i hi v hv t ht
  have hl : (τ ++ [s + 2, q, s + ℓ, j]).length = b + 41 := by simp [hc.1]
  obtain ⟨h1, -, h3, h4, h5⟩ := schSlot_facts hG hρ hc
    (by rw [List.take_append_of_le_length (by rw [hc.1]), List.take_of_length_le (by rw [hc.1])])
    hl (by omega) hℓ t hi hv
  have hj' : (slotStk s ℓ x (τ ++ [s + 2, q, s + ℓ, j]) (violAt s b (b + 41)) i v t).getD
      (b + 40) 0 = j := by
    rw [slotStk_lt _ _ _ _ (by rw [hl]; omega), show b + 40 = τ.length + 3 by rw [hc.1], getD_app]
    rfl
  rw [inDomX, lab2X, eval_and' (eval_and' (eval_eq' _ _) (eval_entX _ _ _)) (eval_lt_eq _ _),
    ite_ne_zero_iff]
  simp only [eval_var, eval_const]
  rw [h1, h3, h4, h5, hj', outValid_track _ hi hv ht ⟨e, he⟩ (step_lt hq hj) (by omega),
    mod_step hj]
  rfl

theorem out_colCoef (hs : 1 ≤ s) :
    (Gn.colCoef M s b).out x ρ =
      (List.range ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ)).flatMap fun F =>
        slotL s ℓ fun i v t => [outColor (Iv M x s ℓ H)
          (slotNum s ℓ (2 * ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ) +
            3 * (Iv M x s ℓ H).schemas.length + (Iv M x s ℓ H).numLocations + F) i v t)] := by
  refine out_colStep hρ hG ⟨⟨Xp.bnd_mulC (bnd_g hρ hG (by omega)) _, Xp.bnd_mulC (bnd_g hρ hG (by omega)) _⟩,
    bnd_g hρ hG (by omega)⟩ (by simp only [eval_add, eval_mulC, hG.eENS, hG.eE, hG.eW]) ?_
  intro e he τ hc q hq j hj i hi v hv t ht
  have hl : (τ ++ [s + 2, q, s + ℓ, j]).length = b + 41 := by simp [hc.1]
  obtain ⟨-, -, h3, h4, h5⟩ := schSlot_facts hG hρ hc
    (by rw [List.take_append_of_le_length (by rw [hc.1]), List.take_of_length_le (by rw [hc.1])])
    hl (by omega) hℓ t hi hv
  rw [lab2X, eval_and' (eval_and' (eval_eq' _ _) (eval_eq' _ _)) (eval_lt_eq _ _),
    ite_ne_zero_iff]
  simp only [eval_var, eval_const]
  have h6 := outValid_coef (Iv M x s ℓ H) hs ⟨e, he⟩ (step_lt hq hj)
    (fun c h => by
      unfold Lax119563Proofs.Matrix.dom; rw [mem_domain_of_schRec hc.2.2.2 c]; exact Or.inl h)
    hi hv ht
  rw [h3, h4, h5, h6]

omit hℓ in
theorem out_colCoord :
    (Gn.colCoord s b).out x ρ =
      (List.range (Iv M x s ℓ H).numLocations).flatMap fun w =>
        slotL s ℓ fun i v t => [outColor (Iv M x s ℓ H)
          (slotNum s ℓ ((Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ +
            2 * (Iv M x s ℓ H).schemas.length + w) i v t)] := by
  simp only [Gn.colCoord, Gn.out, hG.eW]
  refine List.flatMap_congr fun w hw => ?_
  rw [List.mem_range] at hw
  have hGτ := hG.append [(Iv M x s ℓ H).numLocations, w]
  have hl : (ρ ++ [(Iv M x s ℓ H).numLocations, w]).length = b + 2 := by simp [hρ]
  rw [out_slotLoops (bnd_glob (by omega) (by rw [hl]; have := hρ ▸ hG.le; omega)) hGτ.eP]
  unfold slotL
  refine List.flatMap_congr fun i hi => List.flatMap_congr fun v hv =>
    List.flatMap_congr fun t ht => ?_
  rw [List.mem_range] at hi hv ht
  have hGσ := hGτ.append [s + 1, i, 2 ^ ℓ, v, inBit x v,
    (Gn.skip.out x (ρ ++ [(Iv M x s ℓ H).numLocations, w] ++
      [s + 1, i, 2 ^ ℓ, v, inBit x v, 0])).length, 4, t]
  have hS := slotStk_getD (s := s) (ℓ := ℓ) (x := x) (τ := ρ ++ [(Iv M x s ℓ H).numLocations, w])
    Gn.skip i v t
  rw [hl] at hS
  have hw' : (slotStk s ℓ x (ρ ++ [(Iv M x s ℓ H).numLocations, w]) Gn.skip i v t).getD
      (b + 1) 0 = w := by
    rw [slotStk_lt _ _ _ _ (by rw [hl]; omega), ← hρ, getD_app]; rfl
  simp only [slotStk] at hS hw'
  refine out_colBody _ hGσ ht ?_ ?_ hS.1 hS.2.1
  · rw [eval_and' (eval_lt_eq _ _) (eval_or' (eval_eq' _ _) (eval_not' (eval_or' (eval_eq' _ _)
      (eval_eq' _ _)))), ite_ne_zero_iff]
    simp only [eval_var, eval_const, hS.2.2.2.2, hw']
    rw [hGσ.getD (by norm_num : 9 < 18), hGσ.getD (by norm_num : 16 < 18)]
    simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
    rw [outValid_coord (Iv M x s ℓ H) hi hv ht ⟨w, hw⟩ rfl, Iv_init_isSome]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => by tauto⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by tauto⟩
  · simp only [eval_add, eval_mulC, eval_var, hGσ.eENS, hGσ.eE, hw']

/-- **The colour pass** emits the colours of `0, …, nOut - 1`. -/
theorem out_colPass (hs : 1 ≤ s) :
    (Gn.colPass M s b).out x ρ = (List.range (nOut (Iv M x s ℓ H))).map (outColor (Iv M x s ℓ H)) := by
  rw [← flatMap_singleton_eq_map, nOut, range_nOut_flatMap, famCount, range_fam_flatMap]
  simp only [Gn.colPass, Gn.out_seqL, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [out_colUpd hρ hG hℓ, out_colJunc hρ hG hℓ, out_colLink hρ hG hℓ, out_colCoord hρ hG,
    out_colSum hρ hG hℓ, out_colTrack hρ hG hℓ, out_colCoef hρ hG hℓ hs]
  simp only [List.append_assoc]

end Kinds

end Lax119563Proofs.Reduction
