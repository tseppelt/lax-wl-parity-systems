import Lax119563Proofs.Reduction.PkFmt
import Lax119563Proofs.Reduction.Packed

/-!
# The prelude of the packed generator

`preludeP M g` computes the `19` globals of `GlobP` from the preprocessed input
`pkInput x h s` and runs `g` on them (**`out_preludeP`**): `|y|`, the counts `n = |x|`, `h`,
`s` of the flags, `Λ = (h + 3)^2`, `log₂(n + 1)`, `q = ⌈(h + 2)/s⌉` (a count),
`ℓ = max(log₂(n + 1) + 1, q) = packedWidth n h s`, `H = max(h, ℓ)`, `R`, `N`, the command
count `r` and the schema count `Ec` (counting runs of `cmdEnumP`), the codes of `query` and
`accept`, the number of schemas `E` (a counting run of `schEnumP`), `W`, `det` and
`2^ℓ = min(2^ℓ, |y|)`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs
open Lax119563.ImplicitSystemEncodings

/-- `max a b`. -/
def maxQ (a b : Xp) : Xp :=
  add (mulB a (Xp.not (lt a b)) (const 1)) (mulB b (lt a b) (const 1))

lemma eval_maxQ (a b : Xp) (ρ : List ℕ) : (maxQ a b).eval ρ = max (a.eval ρ) (b.eval ρ) := by
  simp only [maxQ, eval, Xp.not]
  by_cases h : a.eval ρ < b.eval ρ
  · simp [h, max_eq_right h.le]
  · simp [h, max_eq_left (by omega : b.eval ρ ≤ a.eval ρ)]

namespace Gn

/-- A count of the flags at positions `≡ t (mod 16)` (at depth `d`). -/
def flagCount (t d : ℕ) (g : Gn) : Gn := .count (.loopX (var 0) (flagGen t (d + 1))) g

/-- The size count body (record at `b + 17`). -/
def szBodyP (b : ℕ) : Gn := .ite (var (b + 17)) (emitN 9) (emitN 4)

/-- **The prelude of the packed generator.** -/
def preludeP (M : Machine) (g : Gn) : Gn :=
  len <|
  flagCount 3 1 <|
  flagCount 5 2 <|
  flagCount 10 3 <|
  bind (mul (add (var 2) (const 3)) (add (var 2) (const 3))) <|
  log (add (var 1) (const 1)) <|
  count (loop (add (var 2) (const 2)) (when (Xp.le (mul (var 3) (add (var 8) (const 1)))
    (add (add (var 2) (const 1)) (var 3))) (emit (const 0)))) <|
  bind (maxQ (add (var 5) (const 1)) (var 6)) <|
  bind (maxQ (var 2) (var 7)) <|
  bind (add (var 8) (const (1 + cM M))) <|
  bind (mulC (16 * cM M ^ 3) (mul (var 9) (var 9))) <|
  count (cmdEnumP M 12 qS (var 8) (var 9) (emit (const 0))) <|
  count (cmdEnumP M 13 qS (var 8) (var 9) (szBodyP 13)) <|
  bind (const 2) <|
  bind (const 0) <|
  count (schEnumP M 16 qS qH qR qN qr qp0 qEc (emit (const 0))) <|
  bind (add (add (var 10) (mulC 8 (var 11))) (const 4)) <|
  bind (add (add (var 10) (mulC 8 (var 11))) (const 3)) <|
  bind (minQ (pow2 (var 7)) (var 0)) g

end Gn

/-! ## The globals -/

variable {M : Machine}

/-- The globals for given `ℓ, H`. -/
noncomputable def globsL (M : Machine) (x : List Bool) (h s ℓ H : ℕ) : List ℕ :=
  [16 * pkLen x.length h s, x.length, h, s, (h + 3) * (h + 3), Nat.log 2 (x.length + 1),
    (h + 1 + s) / s, ℓ, H,
    radix M H, numLoc M H, (verifierCmds' M x s ℓ H).length,
    ((verifierCmds' M x s ℓ H).map cmdSz).sum, (Loc.code (Loc.query : Loc M H)).val,
    (Loc.code (Loc.accept : Loc M H)).val, (Iv M x s ℓ H).schemas.length,
    (Iv M x s ℓ H).numLocations, numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3, 2 ^ ℓ]

/-- The globals computed by the prelude. -/
noncomputable def globsP (M : Machine) (x : List Bool) (h s : ℕ) : List ℕ :=
  globsL M x h s (pkWidth x.length h s) (pkHorizon x.length h s)

lemma length_globsP (x : List Bool) (h s : ℕ) : (globsP M x h s).length = 19 := rfl

lemma clog_eq_log (n : ℕ) : Nat.clog 2 (n + 2) = Nat.log 2 (n + 1) + 1 := by
  apply le_antisymm
  · apply Nat.clog_le_of_le_pow
    have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (n + 1)
    omega
  · have h1 : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
    have := (Nat.lt_clog_iff_pow_lt (show 1 < 2 by norm_num)).mpr
      (show 2 ^ Nat.log 2 (n + 1) < n + 2 by omega)
    omega

lemma pkWidth_eq (n h s : ℕ) : pkWidth n h s = max (Nat.log 2 (n + 1) + 1) ((h + 1 + s) / s) := by
  rw [pkWidth, clog_eq_log]

lemma two_pow_pkWidth_le {n h s : ℕ} (hh : 2 ≤ h) :
    2 ^ pkWidth n h s ≤ 16 * pkLen n h s := by
  rw [pkWidth_eq]
  have h1 : 2 ^ (Nat.log 2 (n + 1) + 1) ≤ 2 * (n + 1) := by
    rw [pow_succ]; have := Nat.pow_log_le_self 2 (show n + 1 ≠ 0 by omega); omega
  have h2 : n ≤ pkLen n h s := by unfold pkLen; omega
  have h3 : h ≤ pkLen n h s := by unfold pkLen; omega
  have h4 : 2 ^ ((h + 1 + s) / s) ≤ pkLen n h s := by unfold pkLen; omega
  rcases le_total (Nat.log 2 (n + 1) + 1) ((h + 1 + s) / s) with h5 | h5
  · rw [max_eq_right h5]; omega
  · rw [max_eq_left h5]; omega

lemma count_div (h s : ℕ) (hs : 1 ≤ s) :
    ((List.range (h + 2)).flatMap fun k =>
      if s * (k + 1) ≤ h + 1 + s then [0] else []).length = (h + 1 + s) / s := by
  have e : ∀ k ∈ List.range (h + 2), (if s * (k + 1) ≤ h + 1 + s then [(0 : ℕ)] else []) =
      if k < (h + 1 + s) / s then [0] else [] := fun k _ => by
    have : s * (k + 1) ≤ h + 1 + s ↔ k < (h + 1 + s) / s := by
      rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le (by omega)]; omega
    simp only [this]
  rw [List.flatMap_congr e, length_flatMap_lt]
  apply min_eq_right
  apply Nat.div_le_of_le_mul; nlinarith

/-! ## Steps -/

section Steps

variable {y : List Bool} {G : List ℕ}

lemma out_log_step {k : ℕ} (hk : k < G.length) {e : Xp} {g : Gn}
    (he : Nat.log 2 (e.eval (G.take k)) = G.getD k 0) :
    (Gn.log e g).out y (G.take k) = g.out y (G.take (k + 1)) := by
  simp only [Gn.out, he, take_succ_getD hk]

lemma out_len_step (hk : 0 < G.length) {g : Gn} (he : y.length = G.getD 0 0) :
    (Gn.len g).out y (G.take 0) = g.out y (G.take 1) := by
  simp only [Gn.out, he, ← take_succ_getD hk]

lemma out_flagGen {σ : List ℕ} {d : ℕ} (hσ : σ.length = d) (t : ℕ) (L k : ℕ) :
    (flagGen t d).out y (σ ++ [L, k, inBit y k]) =
      if k % 16 = t ∧ inBit y k = 2 then [0] else [] := by
  have e1 : (var (d + 1)).eval (σ ++ [L, k, inBit y k]) = k := by
    rw [eval_var, ← hσ, getD_app]; rfl
  have e2 : (var (d + 2)).eval (σ ++ [L, k, inBit y k]) = inBit y k := by
    rw [eval_var, ← hσ, getD_app]; rfl
  have a1 : (isMod t (var (d + 1))).eval (σ ++ [L, k, inBit y k]) ≤ 1 := by
    rw [eval_isMod]; split_ifs <;> omega
  have a2 : (eq (var (d + 2)) (const 2)).eval (σ ++ [L, k, inBit y k]) ≤ 1 := by
    rw [Xp.eval_eq]; split_ifs <;> omega
  rw [flagGen, Gn.out_when, Xp.eval_and a1 a2, eval_isMod, Xp.eval_eq, e1, e2, Xp.eval_const]
  have c1 : (if k = k / 16 * 16 + t then 1 else 0) = (if k % 16 = t then 1 else 0) := by
    split_ifs <;> omega
  rw [c1]
  by_cases h1 : k % 16 = t <;> by_cases h2 : inBit y k = 2 <;> simp [h1, h2, Gn.out]

end Steps

/-- The count of a flag of the preprocessed input. -/
lemma count_flag (x : List Bool) (h s : ℕ) {σ : List ℕ} {d : ℕ} (hσ : σ.length = d) (t : ℕ)
    (ht : t < 16) (j : ℕ)
    (hj : ∀ q, q < pkLen x.length h s → (((pkBlk (x.getD q false) (decide (q < x.length))
      (decide (q < h)) (decide (q < s)))[t]?).elim 0 (fun b => b.toNat + 1) = 2 ↔ q < j))
    (hjm : j ≤ pkLen x.length h s) :
    ((List.range (16 * pkLen x.length h s)).flatMap fun k =>
      (flagGen t d).out (pkInput x h s) (σ ++ [16 * pkLen x.length h s, k,
        inBit (pkInput x h s) k])).length = j := by
  simp only [out_flagGen hσ]
  have hcb := count_blocks (m := pkLen x.length h s)
    (fun q r => if r = t ∧ inBit (pkInput x h s) (r + 16 * q) = 2 then [(0 : ℕ)] else []) t ht
    (fun q r _ => by by_cases hr : r = t <;> simp [hr])
  have e : (fun k => if k % 16 = t ∧ inBit (pkInput x h s) k = 2 then [(0 : ℕ)] else []) =
      (fun k => if k % 16 = t ∧ inBit (pkInput x h s) (k % 16 + 16 * (k / 16)) = 2 then [(0 : ℕ)]
        else []) := funext fun k => by rw [show k % 16 + 16 * (k / 16) = k by omega]
  rw [e, hcb]
  have e2 : ∀ q ∈ List.range (pkLen x.length h s),
      (if t = t ∧ inBit (pkInput x h s) (t + 16 * q) = 2 then [(0 : ℕ)] else []) =
        if q < j then [0] else [] := fun q hq => by
    rw [List.mem_range] at hq
    rw [inBit_pkInput x h s q t ht, if_pos hq]
    by_cases hq' : q < j
    · rw [if_pos ⟨rfl, (hj q hq).mpr hq'⟩, if_pos hq']
    · rw [if_neg (fun h => hq' ((hj q hq).mp h.2)), if_neg hq']
  rw [List.flatMap_congr e2, length_flatMap_lt, min_eq_right hjm]

set_option maxHeartbeats 1000000 in
/-- **The prelude computes the globals.** -/
theorem out_preludeP {x : List Bool} {h s : ℕ} (hx : 2 ≤ x.length) (hh : 2 ≤ h)
    (hxh : x.length ≤ 2 ^ h) (hs : 2 ≤ s) (hsh : s ≤ h + 2) (g : Gn) :
    (Gn.preludeP M g).out (pkInput x h s) [] = g.out (pkInput x h s) (globsP M x h s) := by
  have hyl : (pkInput x h s).length = 16 * pkLen x.length h s := length_pkInput x h s
  have hnm : x.length ≤ pkLen x.length h s := by unfold pkLen; omega
  have hhm : h ≤ pkLen x.length h s := by unfold pkLen; omega
  have hsm : s ≤ pkLen x.length h s := by unfold pkLen; omega
  have hw := pkWidth_eq x.length h s
  have h2l := two_pow_pkWidth_le (n := x.length) (s := s) hh
  have hHdef : pkHorizon x.length h s = max h (pkWidth x.length h s) := rfl
  unfold globsP
  generalize pkWidth x.length h s = ℓ at hw h2l hHdef
  generalize pkHorizon x.length h s = H at hHdef
  generalize hy : pkInput x h s = y at hyl
  set G := globsL M x h s ℓ H with hG
  have hGl : G.length = 19 := rfl
  have h0 : (Gn.preludeP M g).out y [] = (Gn.preludeP M g).out y (G.take 0) := rfl
  rw [h0, Gn.preludeP]
  -- level 0: |y|
  rw [out_len_step (by omega) (by rw [hyl]; rfl)]
  -- levels 1, 2, 3: the flags
  have hflag : ∀ (k t j : ℕ), 0 < k → k < 19 → t < 16 → G.getD k 0 = j →
      j ≤ pkLen x.length h s →
      (∀ q, q < pkLen x.length h s → (((pkBlk (x.getD q false) (decide (q < x.length))
        (decide (q < h)) (decide (q < s)))[t]?).elim 0 (fun b => b.toNat + 1) = 2 ↔ q < j)) →
      ∀ g' : Gn, (Gn.flagCount t k g').out y (G.take k) = g'.out y (G.take (k + 1)) := by
    intro k t j hk0 hk ht hj hjm hb g'
    refine out_count_step (by omega) ?_
    have hl : (G.take k ++ [0]).length = k + 1 := by simp; omega
    have hlim : (var 0).eval (G.take k ++ [0]) = 16 * pkLen x.length h s := by
      rw [eval_var, getD_take_app (by omega) (by omega)]; rfl
    simp only [Gn.out, hlim]
    rw [hj, ← hy]
    exact count_flag x h s hl t ht j hb hjm
  have hblk : ∀ (a b c d : Bool), ((pkBlk a b c d)[3]?.elim 0 (fun b => b.toNat + 1) = 2 ↔
      b = true) ∧ ((pkBlk a b c d)[5]?.elim 0 (fun b => b.toNat + 1) = 2 ↔ c = true) ∧
      ((pkBlk a b c d)[10]?.elim 0 (fun b => b.toNat + 1) = 2 ↔ d = true) := by
    intro a b c d; cases a <;> cases b <;> cases c <;> cases d <;> decide
  rw [hflag 1 3 x.length (by omega) (by omega) (by omega) rfl hnm (fun q _ => by
    rw [(hblk _ _ _ _).1]; simp)]
  rw [hflag 2 5 h (by omega) (by omega) (by omega) rfl hhm (fun q _ => by
    rw [(hblk _ _ _ _).2.1]; simp)]
  rw [hflag 3 10 s (by omega) (by omega) (by omega) rfl hsm (fun q _ => by
    rw [(hblk _ _ _ _).2.2]; simp)]
  have hs1 : 1 ≤ s := by omega
  have ev : ∀ k, k ≤ 19 → ∀ i < k, (G.take k ++ [0]).getD i 0 = G.getD i 0 := fun k hk i hi =>
    getD_take_app hi (by omega) 0
  -- level 4: Λ
  rw [out_bind_step (by omega) (by
    simp only [eval_mul, eval_add, eval_var, eval_const, getD_take_lt (show 2 < 4 by omega)]
    rfl)]
  -- level 5: log₂(n + 1)
  rw [out_log_step (by omega) (by
    simp only [eval_add, eval_var, eval_const, getD_take_lt (show 1 < 5 by omega)]
    rfl)]
  -- level 6: q
  rw [out_count_step (by omega) (by
    have e2 : (add (var 2) (const 2)).eval (G.take 6 ++ [0]) = h + 2 := by
      simp only [eval_add, eval_var, eval_const, ev 6 (by omega) 2 (by omega)]; rfl
    simp only [Gn.out, e2]
    have e : ∀ k ∈ List.range (h + 2), (Gn.when (Xp.le (mul (var 3) (add (var 8) (const 1)))
        (add (add (var 2) (const 1)) (var 3))) (Gn.emit (const 0))).out y
        (G.take 6 ++ [0] ++ [h + 2, k]) = if s * (k + 1) ≤ h + 1 + s then [0] else [] := by
      intro k _
      have g8 : (var 8).eval (G.take 6 ++ [0] ++ [h + 2, k]) = k := by
        rw [eval_var, show 8 = (G.take 6 ++ [0]).length + 1 by simp; omega, getD_app]; rfl
      have g3 : (var 3).eval (G.take 6 ++ [0] ++ [h + 2, k]) = s := by
        rw [eval_var, List.getD_append _ _ _ _ (by simp; omega), ev 6 (by omega) 3 (by omega)]
        rfl
      have g2 : (var 2).eval (G.take 6 ++ [0] ++ [h + 2, k]) = h := by
        rw [eval_var, List.getD_append _ _ _ _ (by simp; omega), ev 6 (by omega) 2 (by omega)]
        rfl
      rw [Gn.out_when, Xp.eval_le]
      simp only [eval_mul, eval_add, eval_const, g8, g3, g2]
      split_ifs <;> simp_all [Gn.out]
    rw [List.flatMap_congr e, count_div h s hs1]
    rfl)]
  -- level 7: ℓ
  rw [out_bind_step (by omega) (by
    simp only [eval_maxQ, eval_add, eval_var, eval_const, getD_take_lt (show 5 < 7 by omega),
      getD_take_lt (show 6 < 7 by omega)]
    exact hw.symm)]
  -- level 8: H
  rw [out_bind_step (by omega) (by
    simp only [eval_maxQ, eval_var, getD_take_lt (show 2 < 8 by omega),
      getD_take_lt (show 7 < 8 by omega)]
    exact hHdef.symm)]
  -- level 9: R
  rw [out_bind_step (by omega) (by
    simp only [eval_add, eval_var, eval_const, getD_take_lt (show 8 < 9 by omega)]
    show H + (1 + cM M) = radix M H
    rw [radix]; omega)]
  -- level 10: N
  rw [out_bind_step (by omega) (by
    simp only [eval_mul, eval_var, eval_mulC, getD_take_lt (show 9 < 10 by omega)]
    show 16 * cM M ^ 3 * (radix M H * radix M H) = numLoc M H
    rw [numLoc]; ring)]
  -- level 11: r
  have bnd : ∀ k i, i < k → (var i).Bnd k := fun k i hi => show i < k from hi
  have hl12 : (G.take 11 ++ [0]).length = 12 := by simp [hGl]
  have eH12 : (var 8).eval (G.take 11 ++ [0]) = H := by
    simp only [eval_var, ev 11 (by omega) 8 (by omega)]; rfl
  have eR12 : (var 9).eval (G.take 11 ++ [0]) = radix M H := by
    simp only [eval_var, ev 11 (by omega) 9 (by omega)]; rfl
  have eS12 : qS.eval (G.take 11 ++ [0]) = s := by
    simp only [eval_var, ev 11 (by omega) 3 (by omega)]; rfl
  rw [out_count_step (by omega) (by
    rw [out_cmdEnumP' hl12 (bnd 12 8 (by omega)) (bnd 12 9 (by omega)) eH12 eR12 _
      (bnd 12 3 (by omega)) eS12 hs1, length_flatMap_emit _ _ (fun _ => rfl),
      (cmdStksP_forall₂ (x := x) (s := s) hl12 (bnd 12 8 (by omega)) (bnd 12 9 (by omega)) eH12
        eR12 ℓ).length_eq]
    rfl)]
  -- level 12: Ec
  have hl13 : (G.take 12 ++ [0]).length = 13 := by simp [hGl]
  have eH13 : (var 8).eval (G.take 12 ++ [0]) = H := by
    simp only [eval_var, ev 12 (by omega) 8 (by omega)]; rfl
  have eR13 : (var 9).eval (G.take 12 ++ [0]) = radix M H := by
    simp only [eval_var, ev 12 (by omega) 9 (by omega)]; rfl
  have eS13 : qS.eval (G.take 12 ++ [0]) = s := by
    simp only [eval_var, ev 12 (by omega) 3 (by omega)]; rfl
  rw [out_count_step (by omega) (by
    rw [out_cmdEnumP' hl13 (bnd 13 8 (by omega)) (bnd 13 9 (by omega)) eH13 eR13 _
      (bnd 13 3 (by omega)) eS13 hs1, List.length_flatMap]
    have hF := cmdStksP_forall₂ (x := x) (s := s) hl13 (bnd 13 8 (by omega))
      (bnd 13 9 (by omega)) eH13 eR13 ℓ
    rw [sum_map_forall₂ (g := cmdSz) hF (fun τ cmd h => ?_)]
    · rfl
    · rw [← szAt_of_stkCmd h]
      unfold szAt
      simp only [Gn.szBodyP, Gn.out, eval_var]
      split <;> rename_i hc <;> simp only [ne_eq, hc, not_false_eq_true, not_true_eq_false,
        if_true, if_false, ite_true, ite_false, Decidable.not_not] <;> exact Gn.length_out_emitN _)]
  -- levels 13, 14: the codes of `query` and `accept`
  rw [out_bind_step (by omega) (by
    simp only [eval_const]
    exact code_query_val.symm)]
  rw [out_bind_step (by omega) (by
    simp only [eval_const]
    exact code_accept_val.symm)]
  -- level 15: E
  have hl16 : (G.take 15 ++ [0]).length = 16 := by simp [hGl]
  have hS := out_schEnumP (M := M) (s := s) (x := x) (y := y) (ℓ := ℓ) (H := H)
    (SX := qS) hl16 (bnd 16 8 (by omega))
    (bnd 16 9 (by omega)) (by simp only [eval_var, ev 15 (by omega) 8 (by omega)]; rfl)
    (by simp only [eval_var, ev 15 (by omega) 9 (by omega)]; rfl) (bnd 16 10 (by omega))
    (by simp only [eval_var, ev 15 (by omega) 10 (by omega)]; rfl) (bnd 16 11 (by omega))
    (by simp only [eval_var, ev 15 (by omega) 11 (by omega)]; rfl) (bnd 16 13 (by omega))
    (by simp only [eval_var, ev 15 (by omega) 13 (by omega)]; rfl) (bnd 16 12 (by omega))
    (by simp only [eval_var, ev 15 (by omega) 12 (by omega)]; rfl) (bnd 16 3 (by omega))
    (by simp only [eval_var, ev 15 (by omega) 3 (by omega)]; rfl) hs1 (Gn.emit (const 0))
  rw [out_count_step (by omega) (by
    rw [hS.2.2, length_flatMap_emit _ _ (fun _ => rfl), ← hS.1.length_eq, hG]
    simp only [globsL, List.getD_cons_succ, List.getD_cons_zero]
    exact (congrArg List.length (Iv_schemas (M := M) (x := x) (s := s) (ℓ := ℓ) (H := H))).symm)]
  -- level 16: W
  rw [out_bind_step (by omega) (by
    simp only [eval_add, eval_var, eval_const, eval_mulC, getD_take_lt (show 10 < 16 by omega),
      getD_take_lt (show 11 < 16 by omega)]
    show numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 4 = (Iv M x s ℓ H).numLocations
    rw [Iv_numLocations]; ring)]
  -- level 17: det
  rw [out_bind_step (by omega) (by
    simp only [eval_add, eval_var, eval_const, eval_mulC, getD_take_lt (show 10 < 17 by omega),
      getD_take_lt (show 11 < 17 by omega)]
    rfl)]
  -- level 18: 2^ℓ
  rw [out_bind_step (by omega) (by
    simp only [eval_minQ, eval_pow2, eval_var, getD_take_lt (show 7 < 18 by omega),
      getD_take_lt (show 0 < 18 by omega)]
    show min (2 ^ ℓ) (16 * pkLen x.length h s) = 2 ^ ℓ
    exact min_eq_left h2l)]
  rw [List.take_of_length_le (by omega)]

lemma globP_globsL {x : List Bool} {h s ℓ H : ℕ} (hΛ : (s + 1) * ℓ ≤ (h + 3) * (h + 3)) :
    GlobP M x s ℓ H (globsL M x h s ℓ H) := by
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [globsL, List.getD_cons_succ, List.getD_cons_zero]
  exact hΛ

/-- The globals of `globsP` are those read by the packed generator. -/
lemma globP_globsP {x : List Bool} {h s : ℕ} (hx : 2 ≤ x.length) (hh : 2 ≤ h)
    (hxh : x.length ≤ 2 ^ h) (hs : 2 ≤ s) (hsh : s ≤ h + 2) :
    GlobP M x s (pkWidth x.length h s) (pkHorizon x.length h s) (globsP M x h s) := by
  obtain ⟨P, hH⟩ := pk_params hx hh hxh hs
  have h1 := P.hℓH
  have : pkWidth x.length h s ≤ h + 3 := by omega
  exact globP_globsL (Nat.mul_le_mul (by omega) this)

/-- The packed generator: the prelude followed by the system generator. -/
def Gn.redGenP (M : Machine) : Gn := Gn.preludeP M (Gn.sysGenP M)

/-- **The packed generator emits the description of the packed system.** -/
theorem out_redGenP {x : List Bool} {h s : ℕ} (hx : 2 ≤ x.length) (hh : 2 ≤ h)
    (hxh : x.length ≤ 2 ^ h) (hs : 2 ≤ s) (hsh : s ≤ h + 2) :
    (Gn.redGenP M).out (pkInput x h s) [] =
      systemDescription (Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s)) := by
  obtain ⟨P, -⟩ := pk_params hx hh hxh hs
  rw [Gn.redGenP, out_preludeP hx hh hxh hs hsh]
  exact out_sysGenP (length_globsP x h s) (globP_globsP hx hh hxh hs hsh) (by omega) P.hℓ
    (fun v hv => inBit_pkInput_x x h s hv)

end Lax119563Proofs.Reduction
