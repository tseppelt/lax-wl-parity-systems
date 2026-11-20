import Lax119563Proofs.Reduction.PkCostSys
import Lax119563Proofs.Reduction.CostMachine

/-!
# The machine of the packed generator

**`redGenP_computesWithin`**: the machine of the packed generator computes
`encodeSystem (Iv M x s ℓ H)` (`ℓ = packedWidth |x| h s`, `H = pkHorizon |x| h s`) from the
preprocessed input `pkInput x h s` within `C 2^ℓ (h + 1)^c` steps, with `c` absolute.

The growth classes are taken at the scale `l = ℓ + log₂(h + 3) + 5` (so that the input length
`16 max(|x|, h, s, 2^⌈(h+2)/s⌉)` is at most `2^l`) and `L = (h + 3)^2 + l` (so that `h, s`,
`Λ = (h + 3)^2` and the bit positions `i ℓ` are linear). The first five steps of the prelude
(`|y|` and the counts `n, h, s` and `Λ`) are analysed directly.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp Ty Gn
open Lax119563.BinaryEncodings Lax119563.ImplicitSystemEncodings

variable {M : Machine}

/-- The scale of the analysis. -/
def scP (n h s : ℕ) : Sc :=
  ⟨pkWidth n h s + (Nat.log 2 (h + 3) + 5), (h + 3) ^ 2 + pkWidth n h s + (Nat.log 2 (h + 3) + 5),
    by omega⟩

/-! ## The flags -/

lemma len_flag (x : List Bool) (h s : ℕ) {ρ : List ℕ} (hρ0 : ρ.getD 0 0 = 16 * pkLen x.length h s)
    (hρl : 0 < ρ.length) (t : ℕ) (ht : t < 16) (j : ℕ)
    (hb : ∀ q, q < pkLen x.length h s → (((pkBlk (x.getD q false) (decide (q < x.length))
      (decide (q < h)) (decide (q < s)))[t]?).elim 0 (fun b => b.toNat + 1) = 2 ↔ q < j))
    (hjm : j ≤ pkLen x.length h s) :
    ((Gn.loopX (var 0) (flagGen t (ρ.length + 1))).out (pkInput x h s) (ρ ++ [0])).length = j := by
  have hlim : (var 0).eval (ρ ++ [0]) = 16 * pkLen x.length h s := by
    rw [eval_var, List.getD_append _ _ _ _ hρl, hρ0]
  simp only [Gn.out, hlim]
  exact count_flag x h s (σ := ρ ++ [0]) (by simp) t ht j hb hjm

lemma hasCost_flagLoop {τs : List Ty} (h0 : τs.getD 0 (P 0 0) = P 1 0) (t d : ℕ) :
    HasCost τs (Gn.loopX (var 0) (flagGen t d)) 1 0 := by
  have hb : HasCost (τs ++ [P 1 0, P 1 0, P 0 0]) (flagGen t d) 0 0 := by
    unfold flagGen isMod
    exact hasCost_when (τ := P 0 0)
      (hasTy_and (hasTy_eq (hasTy_var _) (hasTy_addBig (hasTy_shl (hasTy_shr (hasTy_var _)
        ((hasTy_const 4).le ⟨le_rfl, by omega⟩)) ((hasTy_const 4).le ⟨le_rfl, by omega⟩))
        (hasTy_const _))) (hasTy_eq (hasTy_var _) (hasTy_const 2)))
      (hasCost_emit (hasTy_const 0))
  have := hasCost_loopX (hasTy_var' h0) hb
  exact this.mono (by simp) (by simp)

lemma cost_flagCount (y : List Bool) (t d : ℕ) (g : Gn) (ρ : List ℕ) :
    (Gn.flagCount t d g).cost y ρ = 1 + (Gn.loopX (var 0) (flagGen t (d + 1))).cost y (ρ ++ [0]) +
      g.cost y (ρ ++ [((Gn.loopX (var 0) (flagGen t (d + 1))).out y (ρ ++ [0])).length]) := rfl

lemma fits_flagCount (y : List Bool) (t d : ℕ) (g : Gn) (ρ : List ℕ) (B : ℕ) :
    (Gn.flagCount t d g).Fits y B ρ ↔
      ((Gn.loopX (var 0) (flagGen t (d + 1))).out y (ρ ++ [0])).length < B ∧
      (Gn.loopX (var 0) (flagGen t (d + 1))).Fits y B (ρ ++ [0]) ∧
      g.Fits y B (ρ ++ [((Gn.loopX (var 0) (flagGen t (d + 1))).out y (ρ ++ [0])).length]) :=
  Iff.rfl

/-! ## Bounds on the scale -/

lemma pkLen_le {n h s : ℕ} (hn : n < 2 ^ pkWidth n h s) (hsh : s ≤ h + 2) :
    pkLen n h s ≤ 2 ^ pkWidth n h s + h + 2 := by
  have : 2 ^ ((h + 1 + s) / s) ≤ 2 ^ pkWidth n h s :=
    Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  unfold pkLen; omega

lemma two_pow_scP {n h s : ℕ} :
    2 ^ (scP n h s).l = 2 ^ pkWidth n h s * (32 * 2 ^ Nat.log 2 (h + 3)) := by
  simp only [scP]; rw [pow_add, pow_add]; ring

lemma len_le_scP {n h s : ℕ} (hn : n < 2 ^ pkWidth n h s) (hsh : s ≤ h + 2) :
    16 * pkLen n h s ≤ 2 ^ (scP n h s).l := by
  rw [two_pow_scP]
  have h1 := pkLen_le hn hsh
  have h2 : h + 3 < 2 * 2 ^ Nat.log 2 (h + 3) := by
    have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (h + 3)
    rw [pow_succ] at this; omega
  have h3 : 1 ≤ 2 ^ pkWidth n h s := Nat.one_le_two_pow
  generalize 2 ^ pkWidth n h s = A at h1 h3
  generalize 2 ^ Nat.log 2 (h + 3) = B at h2
  nlinarith

lemma le_two_pow_L {n h s : ℕ} {v : ℕ} (hv : v ≤ 2 ^ (scP n h s).l) (K : ℕ) (hK : 1 ≤ K) :
    v < 2 ^ (K * ((scP n h s : ℕ) + 1)) := by
  have h1 := (scP n h s).le
  have : 2 ^ (scP n h s).l < 2 ^ (K * ((scP n h s : ℕ) + 1)) :=
    Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  omega

lemma bnd_P_le {e d d' K : ℕ} (σ : Sc) (he : e ≤ 1) (hd : d ≤ d') :
    (P e d).bnd K σ ≤ K * (2 ^ σ.l * ((σ : ℕ) + 1) ^ d') := by
  simp only [Ty.bnd]
  have h1 : 2 ^ (e * σ.l) ≤ 2 ^ σ.l := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h2 : ((σ : ℕ) + 1) ^ d ≤ ((σ : ℕ) + 1) ^ d' := Nat.pow_le_pow_right (by omega) hd
  rw [← Nat.mul_assoc]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

lemma auxX1 (a b : ℕ) : 1 ≤ 2 ^ a * (b + 1) ^ 16 :=
  Nat.one_le_iff_ne_zero.mpr (by positivity)

lemma auxX2 (a b : ℕ) : b + 1 ≤ 2 ^ a * (b + 1) ^ 16 :=
  calc b + 1 ≤ (b + 1) ^ 16 := Nat.le_self_pow (by norm_num) _
    _ ≤ 2 ^ a * (b + 1) ^ 16 := Nat.le_mul_of_pos_left _ (by positivity)

lemma auxX3 {v a : ℕ} (b : ℕ) (h : v ≤ 2 ^ a) : v ≤ 2 ^ a * (b + 1) ^ 16 :=
  le_trans h (Nat.le_mul_of_pos_right _ (by positivity))

/-- The expression of `Λ`. -/
abbrev ΛX : Xp := mul (add (var 2) (const 3)) (add (var 2) (const 3))

lemma hasTy_ΛX : HasTy [P 1 0, P 1 0, P 0 1, P 0 1] ΛX (P 0 2) := by
  have h := hasTy_add (τs := [P 1 0, P 1 0, P 0 1, P 0 1]) (hasTy_var' (i := 2) rfl)
    (hasTy_lin_const 3)
  simpa using hasTy_mul h h h

set_option maxHeartbeats 1000000 in
/-- **Fits and cost of the packed generator.** -/
theorem redGenP_cost (M : Machine) : ∃ K : ℕ, 1 ≤ K ∧ ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length →
    2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s → s ≤ h + 2 →
    (Gn.redGenP M).Fits (pkInput x h s) (2 ^ (K * ((scP x.length h s : ℕ) + 1))) [] ∧
    (Gn.redGenP M).cost (pkInput x h s) [] ≤
      K * 2 ^ (scP x.length h s).l * ((scP x.length h s : ℕ) + 1) ^ 16 := by
  obtain ⟨Km, hKm⟩ := hasCost_midP M (by norm_num : 12 ≤ 15) (hasCost_sysGenP M) 1
  obtain ⟨K1, hK1⟩ := hasCost_flagLoop (τs := [P 1 0, P 0 0]) rfl 3 2 1
  obtain ⟨K2, hK2⟩ := hasCost_flagLoop (τs := [P 1 0, P 1 0, P 0 0]) rfl 5 3 1
  obtain ⟨K3, hK3⟩ := hasCost_flagLoop (τs := [P 1 0, P 1 0, P 0 1, P 0 0]) rfl 10 4 1
  obtain ⟨KΛ, hKΛ⟩ := hasTy_ΛX 1
  refine ⟨Km + K1 + K2 + K3 + KΛ + 8, by omega, fun x h s hx hh hxh hs hsh => ?_⟩
  obtain ⟨hPar, hH⟩ := pk_params hx hh hxh hs
  set σ := scP x.length h s with hσ
  set y := pkInput x h s with hy
  set K := Km + K1 + K2 + K3 + KΛ + 8 with hK
  have hyl : y.length = 16 * pkLen x.length h s := length_pkInput x h s
  have hyσ : y.length ≤ 2 ^ σ.l := by rw [hyl]; exact len_le_scP hPar.hx hsh
  have hnm : x.length ≤ pkLen x.length h s := by unfold pkLen; omega
  have hhm : h ≤ pkLen x.length h s := by unfold pkLen; omega
  have hsm : s ≤ pkLen x.length h s := by unfold pkLen; omega
  have hL : (h + 3) ^ 2 ≤ (σ : ℕ) := by simp only [hσ, scP]; omega
  have hlL := σ.le
  -- the counts
  have hblk : ∀ (a b c d : Bool), ((pkBlk a b c d)[3]?.elim 0 (fun b => b.toNat + 1) = 2 ↔
      b = true) ∧ ((pkBlk a b c d)[5]?.elim 0 (fun b => b.toNat + 1) = 2 ↔ c = true) ∧
      ((pkBlk a b c d)[10]?.elim 0 (fun b => b.toNat + 1) = 2 ↔ d = true) := by
    intro a b c d; cases a <;> cases b <;> cases c <;> cases d <;> decide
  have l1 : ((Gn.loopX (var 0) (flagGen 3 2)).out y ([y.length] ++ [0])).length = x.length :=
    len_flag x h s (ρ := [y.length]) (by simp [hyl]) (by simp) 3 (by omega) x.length
      (fun q _ => by rw [(hblk _ _ _ _).1]; simp) hnm
  have l2 : ((Gn.loopX (var 0) (flagGen 5 3)).out y ([y.length, x.length] ++ [0])).length = h :=
    len_flag x h s (ρ := [y.length, x.length]) (by simp [hyl]) (by simp) 5 (by omega) h
      (fun q _ => by rw [(hblk _ _ _ _).2.1]; simp) hhm
  have l3 : ((Gn.loopX (var 0) (flagGen 10 4)).out y ([y.length, x.length, h] ++ [0])).length =
      s :=
    len_flag x h s (ρ := [y.length, x.length, h]) (by simp [hyl]) (by simp) 10 (by omega) s
      (fun q _ => by rw [(hblk _ _ _ _).2.2]; simp) hsm
  -- the classes of the stacks
  have b10 : ∀ v, v ≤ 2 ^ σ.l → v ≤ (Ty.P 1 0).bnd 1 σ := fun v hv => by
    simp only [Ty.bnd]; simpa using hv
  have b01 : ∀ v, v ≤ (σ : ℕ) + 1 → v ≤ (Ty.P 0 1).bnd 1 σ := fun v hv => by
    simp only [Ty.bnd]; simpa using hv
  have b00 : (0 : ℕ) ≤ (Ty.P 0 0).bnd 1 σ := Nat.zero_le _
  have hn2 : x.length ≤ 2 ^ σ.l := le_trans hnm (by omega)
  have hh2 : h ≤ 2 ^ σ.l := le_trans hhm (by omega)
  have hs2 : s ≤ 2 ^ σ.l := le_trans hsm (by omega)
  have A1 : Ag 1 σ [P 1 0, P 0 0] [y.length, 0] := .cons (b10 _ hyσ) (.cons b00 .nil)
  have A2 : Ag 1 σ [P 1 0, P 1 0, P 0 0] [y.length, x.length, 0] :=
    .cons (b10 _ hyσ) (.cons (b10 _ hn2) (.cons b00 .nil))
  have A3 : Ag 1 σ [P 1 0, P 1 0, P 0 1, P 0 0] [y.length, x.length, h, 0] :=
    .cons (b10 _ hyσ) (.cons (b10 _ hn2) (.cons (b01 _ (by nlinarith)) (.cons b00 .nil)))
  have A4 : Ag 1 σ [P 1 0, P 1 0, P 0 1, P 0 1] [y.length, x.length, h, s] :=
    .cons (b10 _ hyσ) (.cons (b10 _ hn2) (.cons (b01 _ (by nlinarith)) (.cons
      (b01 _ (by nlinarith)) .nil)))
  have eΛ : ΛX.eval [y.length, x.length, h, s] = (h + 3) * (h + 3) := by
    simp only [ΛX, eval_mul, eval_add, eval_var, eval_const]; rfl
  have A5 : Ag 1 σ Γ5 [y.length, x.length, h, s, (h + 3) * (h + 3)] :=
    .cons (b10 _ hyσ) (.cons (b10 _ hn2) (.cons (b01 _ (by nlinarith)) (.cons
      (b01 _ (by nlinarith)) (.cons (b01 _ (by nlinarith)) .nil))))
  obtain ⟨f1, c1⟩ := hK1 σ y _ hyσ A1
  obtain ⟨f2, c2⟩ := hK2 σ y _ hyσ A2
  obtain ⟨f3, c3⟩ := hK3 σ y _ hyσ A3
  obtain ⟨fΛ1, fΛ2, cΛ⟩ := hKΛ σ _ A4
  obtain ⟨fm, cm⟩ := hKm σ y _ hyσ A5
  have hK1 : 1 ≤ K := by omega
  constructor
  · -- fits
    rw [Gn.redGenP, Gn.preludeP]
    refine ⟨le_two_pow_L hyσ K hK1, ?_⟩
    rw [show [] ++ [y.length] = [y.length] from rfl, fits_flagCount, l1]
    refine ⟨le_two_pow_L hn2 K hK1, fits_up (by omega) f1, ?_⟩
    rw [show [y.length] ++ [x.length] = [y.length, x.length] from rfl, fits_flagCount, l2]
    refine ⟨le_two_pow_L hh2 K hK1, fits_up (by omega) f2, ?_⟩
    rw [show [y.length, x.length] ++ [h] = [y.length, x.length, h] from rfl, fits_flagCount, l3]
    refine ⟨le_two_pow_L hs2 K hK1, fits_up (by omega) f3, ?_⟩
    refine ⟨xfits_up (by omega) fΛ2, ?_⟩
    rw [show [y.length, x.length, h] ++ [s] = [y.length, x.length, h, s] from rfl, eΛ]
    exact fits_up (by omega) fm
  · -- cost
    rw [Gn.redGenP, Gn.preludeP]
    show y.length + 1 + (Gn.flagCount 3 1 _).cost y ([] ++ [y.length]) ≤ _
    rw [show [] ++ [y.length] = [y.length] from rfl, cost_flagCount, l1,
      show [y.length] ++ [x.length] = [y.length, x.length] from rfl, cost_flagCount, l2,
      show [y.length, x.length] ++ [h] = [y.length, x.length, h] from rfl, cost_flagCount, l3,
      show [y.length, x.length, h] ++ [s] = [y.length, x.length, h, s] from rfl]
    show y.length + 1 + (1 + _ + (1 + _ + (1 + _ + (ΛX.cost [y.length, x.length, h, s] +
      (Gn.midP M (Gn.sysGenP M)).cost y ([y.length, x.length, h, s] ++
        [ΛX.eval [y.length, x.length, h, s]]))))) ≤ _
    rw [eΛ]
    have d1 := bnd_P_le (K := K1) σ le_rfl (show 0 + 1 ≤ 16 by omega)
    have d2 := bnd_P_le (K := K2) σ le_rfl (show 0 + 1 ≤ 16 by omega)
    have d3 := bnd_P_le (K := K3) σ le_rfl (show 0 + 1 ≤ 16 by omega)
    have dm := bnd_P_le (K := Km) σ le_rfl (show 15 + 1 ≤ 16 by omega)
    have hX : 1 ≤ 2 ^ σ.l * ((σ : ℕ) + 1) ^ 16 := auxX1 _ _
    have hX2 : (σ : ℕ) + 1 ≤ 2 ^ σ.l * ((σ : ℕ) + 1) ^ 16 := auxX2 _ _
    have hX3 : y.length ≤ 2 ^ σ.l * ((σ : ℕ) + 1) ^ 16 := auxX3 _ hyσ
    have e : K * 2 ^ σ.l * ((σ : ℕ) + 1) ^ 16 = K * (2 ^ σ.l * ((σ : ℕ) + 1) ^ 16) := by ring
    rw [e]
    generalize 2 ^ σ.l * ((σ : ℕ) + 1) ^ 16 = X at hX hX2 hX3 d1 d2 d3 dm
    have dΛ : KΛ * ((σ : ℕ) + 1) ≤ KΛ * X := Nat.mul_le_mul_left _ hX2
    have eK : K * X = Km * X + K1 * X + K2 * X + K3 * X + KΛ * X + 8 * X := by rw [hK]; ring
    rw [eK]
    simp only [List.cons_append, List.nil_append, Nat.reduceAdd]
    omega

/-! ## The output is longer than the input -/

lemma length_le_encodeNatsP (l : List ℕ) : l.length ≤ (encodeNats l).length := by
  induction l with
  | nil => simp [encodeNats]
  | cons a l ih =>
    simp only [encodeNats, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have : 1 ≤ (encodeNat a).length := by simp [encodeNat]
    omega

lemma two_pow_le_locBlock (s ℓ : ℕ) :
    2 ^ ℓ ≤ ((List.range (s + 1)).flatMap fun i =>
      (List.range (2 ^ ℓ)).flatMap fun w => i :: bitsL ℓ w).length := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.length_append]
  have : 2 ^ ℓ ≤ ((List.range (2 ^ ℓ)).flatMap fun w => 0 :: bitsL ℓ w).length := by
    rw [List.length_flatMap]
    have h : ∀ w ∈ List.range (2 ^ ℓ), 1 ≤ (0 :: bitsL ℓ w).length := fun w _ => by simp
    calc 2 ^ ℓ = ((List.range (2 ^ ℓ)).map fun _ => 1).sum := by simp
      _ ≤ _ := List.sum_le_sum h
  omega

lemma numLoc_ge (R C H : ℕ) (hR : H + 1 ≤ R) (hC : 1 ≤ C) :
    16 * ((H + 1) * (H + 1)) ≤ 16 * (R * (C * (C * (R * C)))) := by
  have h1 : (H + 1) * (H + 1) ≤ R * R := Nat.mul_le_mul hR hR
  have h2 : 1 ≤ C * C * C := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega))
  have h3 : R * R ≤ R * R * (C * C * C) := Nat.le_mul_of_pos_right _ h2
  have e : R * (C * (C * (R * C))) = R * R * (C * C * C) := by ring
  rw [e]; omega

lemma len_le_descP {x : List Bool} {h s : ℕ} (hx : 2 ≤ x.length) (hh : 2 ≤ h)
    (hxh : x.length ≤ 2 ^ h) (hs : 2 ≤ s) (hsh : s ≤ h + 2) :
    16 * pkLen x.length h s ≤
      (systemDescription (Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s))).length := by
  obtain ⟨hPar, hH⟩ := pk_params hx hh hxh hs
  set ℓ := pkWidth x.length h s with hℓ
  set H := pkHorizon x.length h s with hHd
  have hhH : h ≤ H := le_max_left _ _
  have hW : numLoc M H ≤ (Iv M x s ℓ H).numLocations := by rw [Iv_numLocations]; omega
  have hR : H + 1 ≤ radix M H := by unfold radix; omega
  have hC : 1 ≤ cM M := by unfold cM; omega
  have hN : 16 * ((H + 1) * (H + 1)) ≤ numLoc M H := by
    unfold numLoc; exact numLoc_ge _ _ _ hR hC
  have hloc : (Iv M x s ℓ H).numLocations * 2 ^ ℓ ≤
      ((List.finRange (Iv M x s ℓ H).numLocations).flatMap
        (fun v => initNum ((Iv M x s ℓ H).init v) ::
          domainDescription ((Iv M x s ℓ H).domain v))).length := by
    rw [locsDesc_IvP, List.length_flatMap]
    have h : ∀ v ∈ List.range (Iv M x s ℓ H).numLocations, 2 ^ ℓ ≤
        (((if v = (Loc.code (Loc.accept : Loc M H)).val then 1 else 0) +
          2 * (if v = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 then 1 else 0)) ::
          ((s + 1) * 2 ^ ℓ) :: (List.range (s + 1)).flatMap fun i =>
            (List.range (2 ^ ℓ)).flatMap fun w => i :: bitsL ℓ w).length := fun v _ => by
      have := two_pow_le_locBlock s ℓ
      simp only [List.length_cons]; omega
    calc (Iv M x s ℓ H).numLocations * 2 ^ ℓ =
          ((List.range (Iv M x s ℓ H).numLocations).map fun _ => 2 ^ ℓ).sum := by simp
      _ ≤ _ := List.sum_le_sum h
  have hpk : pkLen x.length h s ≤ (H + 1) * (H + 1) * 2 ^ ℓ := by
    have h1 := pkLen_le hPar.hx hsh
    have h2 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
    have h3 : h + 3 ≤ (H + 1) * (H + 1) := by nlinarith
    calc pkLen x.length h s ≤ 2 ^ ℓ + h + 2 := h1
      _ ≤ (h + 3) * 2 ^ ℓ := by nlinarith
      _ ≤ (H + 1) * (H + 1) * 2 ^ ℓ := Nat.mul_le_mul_right _ h3
  have hdesc : ((List.finRange (Iv M x s ℓ H).numLocations).flatMap
        (fun v => initNum ((Iv M x s ℓ H).init v) ::
          domainDescription ((Iv M x s ℓ H).domain v))).length ≤
      (systemDescription (Iv M x s ℓ H)).length := by
    unfold systemDescription
    simp only [List.length_append, List.length_cons]
    omega
  have hW2 : 16 * ((H + 1) * (H + 1)) * 2 ^ ℓ ≤ (Iv M x s ℓ H).numLocations * 2 ^ ℓ :=
    Nat.mul_le_mul_right _ (le_trans hN hW)
  calc 16 * pkLen x.length h s ≤ 16 * ((H + 1) * (H + 1) * 2 ^ ℓ) := Nat.mul_le_mul_left _ hpk
    _ = 16 * ((H + 1) * (H + 1)) * 2 ^ ℓ := by ring
    _ ≤ _ := le_trans hW2 (le_trans hloc hdesc)

/-! ## The machine -/

lemma scP_L_le {n h s : ℕ} (hℓ : pkWidth n h s ≤ h + 1) :
    (scP n h s : ℕ) + 1 ≤ 3 * (h + 3) ^ 2 := by
  have h1 : Nat.log 2 (h + 3) ≤ h + 3 := Nat.log_le_self 2 _
  show (h + 3) ^ 2 + pkWidth n h s + (Nat.log 2 (h + 3) + 5) + 1 ≤ 3 * (h + 3) ^ 2
  nlinarith

lemma two_pow_scP_le {n h s : ℕ} :
    2 ^ (scP n h s).l ≤ 32 * (h + 3) * 2 ^ pkWidth n h s := by
  rw [two_pow_scP]
  have : 2 ^ Nat.log 2 (h + 3) ≤ h + 3 := Nat.pow_log_le_self 2 (by omega)
  calc 2 ^ pkWidth n h s * (32 * 2 ^ Nat.log 2 (h + 3)) ≤ 2 ^ pkWidth n h s * (32 * (h + 3)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
    _ = _ := by ring

lemma κ_boundP (w : ℕ) : κ w + 20 * (2 * w + 1) ≤ 2088 * (w + 3) ^ 2 := by
  simp only [κ, Ex.nodeCost, unitCost]; nlinarith

lemma w3_boundP {K L A w : ℕ} (hL : L + 1 ≤ 3 * A ^ 2) (hw : w = K * (L + 1) + 1)
    (hA : 1 ≤ A) : w + 3 ≤ 3 * (K + 2) * A ^ 2 := by
  have h1 : K * (L + 1) ≤ K * (3 * A ^ 2) := Nat.mul_le_mul_left _ hL
  have h2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA
  have e : 3 * (K + 2) * A ^ 2 = K * (3 * A ^ 2) + 6 * A ^ 2 := by ring
  rw [hw, e]; omega

lemma cost_boundP {K c A Q X L : ℕ} (hc : c ≤ K * X * (L + 1) ^ 16)
    (hX : X ≤ 32 * A * Q) (hL : L + 1 ≤ 3 * A ^ 2) : c ≤ K * 32 * 3 ^ 16 * Q * A ^ 33 := by
  calc c ≤ K * X * (L + 1) ^ 16 := hc
    _ ≤ K * (32 * A * Q) * (3 * A ^ 2) ^ 16 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hX) (Nat.pow_le_pow_left hL 16)
    _ = _ := by ring

/-- The arithmetic of the time bound. -/
lemma time_arithP {K c w T A Q X L : ℕ} (hc : c ≤ K * X * (L + 1) ^ 16)
    (hX : X ≤ 32 * A * Q) (hL : L + 1 ≤ 3 * A ^ 2) (hw : w = K * (L + 1) + 1) (hA : 1 ≤ A)
    (hQ : 1 ≤ Q) (hT : T ≤ (κ w + 20 * (2 * w + 1)) * c + 4) :
    T ≤ (2088 * (3 * (K + 2)) ^ 2 * (K * 32 * 3 ^ 16) + 4) * Q * A ^ 37 := by
  have hw3 := w3_boundP hL hw hA
  have h1 : κ w + 20 * (2 * w + 1) ≤ 2088 * (3 * (K + 2)) ^ 2 * A ^ 4 := by
    calc _ ≤ 2088 * (w + 3) ^ 2 := κ_boundP w
      _ ≤ 2088 * (3 * (K + 2) * A ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw3 2)
      _ = _ := by ring
  have h2 := cost_boundP hc hX hL
  have h4 := Nat.mul_le_mul h1 h2
  have e : 2088 * (3 * (K + 2)) ^ 2 * A ^ 4 * (K * 32 * 3 ^ 16 * Q * A ^ 33) =
      2088 * (3 * (K + 2)) ^ 2 * (K * 32 * 3 ^ 16) * (Q * A ^ 37) := by ring
  rw [e] at h4
  have e2 : (2088 * (3 * (K + 2)) ^ 2 * (K * 32 * 3 ^ 16) + 4) * Q * A ^ 37 =
      2088 * (3 * (K + 2)) ^ 2 * (K * 32 * 3 ^ 16) * (Q * A ^ 37) + 4 * (Q * A ^ 37) := by ring
  rw [e2]
  have h5 : 1 ≤ Q * A ^ 37 := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by positivity))
  generalize 2088 * (3 * (K + 2)) ^ 2 * (K * 32 * 3 ^ 16) * (Q * A ^ 37) = Z at h4 ⊢
  generalize (κ w + 20 * (2 * w + 1)) * c = Y at hT h4
  omega

/-- **The machine of the packed generator.** -/
theorem redGenP_computesWithin (M : Machine) : ∃ C : ℕ, ∀ (x : List Bool) (h s : ℕ),
    2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s → s ≤ h + 2 →
    ComputesWithin (Gn.machine (Gn.redGenP M).need (Gn.redGenP M)) (pkInput x h s)
      (encodeSystem (Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s)))
      (C * 2 ^ pkWidth x.length h s * (h + 3) ^ 37) := by
  obtain ⟨K, hK1, hK⟩ := redGenP_cost M
  refine ⟨2088 * (3 * (K + 2)) ^ 2 * (K * 32 * 3 ^ 16) + 4, fun x h s hx hh hxh hs hsh => ?_⟩
  obtain ⟨hPar, hH⟩ := pk_params hx hh hxh hs
  obtain ⟨hF, hC⟩ := hK x h s hx hh hxh hs hsh
  set σ := scP x.length h s with hσ
  set y := pkInput x h s with hy
  set w := K * ((σ : ℕ) + 1) + 1 with hw
  have hout := out_redGenP (M := M) hx hh hxh hs hsh
  have hB : 2 * 2 ^ (K * ((σ : ℕ) + 1)) ≤ 2 ^ w := by rw [hw, pow_succ]; omega
  have hw2 : 2 ≤ w := by
    have : 1 ≤ K * ((σ : ℕ) + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
      (by omega))
    omega
  have hlen : y.length ≤ (encodeNats ((Gn.redGenP M).out y [])).length := by
    rw [hout, length_pkInput]
    exact le_trans (len_le_descP hx hh hxh hs hsh) (length_le_encodeNatsP _)
  have H := Gn.computesWithin hw2 hB le_rfl (Gn.wfx_redGenP M) hF hlen
  rw [hout] at H
  refine ComputesWithin.mono H ?_
  have henc : (encodeNats (systemDescription (Iv M x s (pkWidth x.length h s)
      (pkHorizon x.length h s)))).length ≤ (Gn.redGenP M).cost y [] * (2 * w + 1) := by
    rw [← hout]
    refine le_trans (length_encodeNats_le (w := w) fun v hv => ?_)
      (Nat.mul_le_mul_right _ (length_out_le_cost _ []))
    have hle : 2 ^ (K * ((σ : ℕ) + 1)) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (lt_of_mem_out _ hF v hv) hle
  rw [← hout] at henc ⊢
  refine time_arithP (c := (Gn.redGenP M).cost y []) (X := 2 ^ σ.l) (L := (σ : ℕ)) hC
    two_pow_scP_le (scP_L_le (le_trans hPar.hℓH hH)) hw (by omega) Nat.one_le_two_pow ?_
  have := Nat.mul_le_mul_left 20 henc
  have e : (κ w + 20 * (2 * w + 1)) * (Gn.redGenP M).cost y [] =
      κ w * (Gn.redGenP M).cost y [] + 20 * ((Gn.redGenP M).cost y [] * (2 * w + 1)) := by ring
  rw [e]
  omega

end Lax119563Proofs.Reduction
