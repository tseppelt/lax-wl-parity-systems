import Lax119563Proofs.Reduction.PkPass
import Lax119563Proofs.Reduction.SysDesc

/-!
# The packed system generator

`sysGenP M` (run on the globals `GlobP`, depth `19`) emits `systemDescription (Iv M x s ℓ H)`
(**`out_sysGenP`**), as `sysGen` of `SysGen`, but with the number `s` of data blocks read from
the globals. The input `y` of the generator holds the bit `x_v` of the input of the machine at
position `16 v + 1` (`hy`), so the domain loops run a `loopX` over `16 · 2^ℓ` positions and use
those with `k % 16 = 1`. The checksum shift (`i = s`) is emitted bit by bit as parities of
counts (`xorFields_testBit`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563Proofs.Programs

/-! ## Expressions -/

/-- `min a b` (by products with `0/1` factors). -/
def minQ (a b : Xp) : Xp :=
  add (mulB a (lt a b) (const 1)) (mulB b (Xp.not (lt a b)) (const 1))

lemma eval_minQ (a b : Xp) (ρ : List ℕ) : (minQ a b).eval ρ = min (a.eval ρ) (b.eval ρ) := by
  simp only [minQ, eval, Xp.not]
  by_cases h : a.eval ρ < b.eval ρ
  · simp [h, min_eq_left h.le]
  · simp [h, min_eq_right (by omega : b.eval ρ ≤ a.eval ρ)]

lemma bnd_minQ {n : ℕ} {a b : Xp} (ha : a.Bnd n) (hb : b.Bnd n) : (minQ a b).Bnd n :=
  ⟨⟨ha, ⟨ha, hb⟩, trivial⟩, ⟨hb, ⟨⟨ha, hb⟩, trivial⟩, trivial⟩⟩

/-- The bit position `i ℓ` of block `i` (the value of `iX`), clamped to `Λ`. -/
def posX (iX : Xp) : Xp := minQ (mul qℓ iX) qΛ

/-- `k % 16 = 1`. -/
def isX1 (kX : Xp) : Xp := eq kX (add (shl (shr kX (const 4)) (const 4)) (const 1))

lemma eval_isX1 (kX : Xp) (ρ : List ℕ) :
    (isX1 kX).eval ρ = if kX.eval ρ % 16 = 1 then 1 else 0 := by
  rw [isX1, Xp.eval_eq]
  simp only [Xp.eval_add, Xp.eval_shl, Xp.eval_shr, Xp.eval_const]
  norm_num
  split_ifs <;> omega

namespace Gn

/-- Loops over blocks `i ≤ s` and register values `v < 2^ℓ`, entered at depth `D`: a `loopX`
over `16 · 2^ℓ` positions `k`, using `k = 16 v + 1`; the stack is
`[s + 1, i, 16 · 2^ℓ, k, inBit y k, v]` followed by the count of the output of `V`. -/
def domLoopsP (D : ℕ) (V body : Gn) : Gn :=
  .loop (add qS (const 1)) (.loopX (mulC 16 qP)
    (when (isX1 (var (D + 3))) (.bind (shr (var (D + 3)) (const 4)) (.count V body))))

/-- The `ℓ` binary digits of the value of `vX` (run at depth `D`). -/
def bitsGenP (vX : Xp) (D : ℕ) : Gn :=
  .loop qℓ (.emit (odd (shr vX (var (D + 1)))))

/-- Emit the coordinate number `i 2^ℓ + v` if the count is zero. -/
def domBodyP (D : ℕ) : Gn :=
  when (Xp.eq (var (D + 6)) (const 0)) (.emit (add (shl (var (D + 1)) qℓ) (var (D + 5))))

/-- Emit the coordinate description `i, bits v` if the count is zero. -/
def domBodyP' (D : ℕ) : Gn :=
  when (Xp.eq (var (D + 6)) (const 0))
    (.seq (.emit (var (D + 1))) (bitsGenP (var (D + 5)) (D + 7)))

/-- The domain violations of the schema of a schema stack (record at `b + 28 …`) at the
coordinate of the domain loops entered at depth `D`. -/
def violAtP (b D : ℕ) : Gn :=
  violGenP (D + 7) qS (var (D + 1)) (posX (var (D + 1))) (var (D + 5))
    (mul (var (D + 4)) (lt (var (D + 5)) (var 1))) (var (b + 33)) (var (b + 34)) (var (b + 35)) (var (b + 36)) qℓ qH

/-- The description of the domain of the schema of a schema stack, run at depth `D`. -/
def domGenP (b D : ℕ) : Gn :=
  .count (domLoopsP (D + 1) (violAtP b (D + 1)) (domBodyP (D + 1)))
    (.seq (.emit (var D)) (domLoopsP (D + 1) (violAtP b (D + 1)) (domBodyP' (D + 1))))

/-- The description of the permutation with the shifts of the mask `mX`, run at depth `D`. -/
def permGenP (mX : Xp) (D : ℕ) : Gn :=
  .seq (.loop (add qS (const 1)) (.emit (var (D + 1))))
    (.loop (add qS (const 1)) (.loop qℓ (.ite (lt (var (D + 1)) qS)
      (.emit (odd (shr mX (add (posX (var (D + 1))) (var (D + 3))))))
      (.count (.loop qS (when (odd (shr mX (add (posX (var (D + 6))) (var (D + 3)))))
          (.emit (const 0))))
        (.emit (odd (var (D + 4))))))))

/-- The description of the schema of a schema stack (depth `b + 37`). -/
def schBodyP (b : ℕ) : Gn :=
  .ite (Xp.eq (var (b + 28)) (const 1))
    (seqL [.emit (const 3), .emit (var (b + 29)), .emit (var (b + 30)), .emit (var (b + 31)),
      domGenP b (b + 37), permGenP (var (b + 32)) (b + 37), permGenP (const 0) (b + 37),
      permGenP (const 0) (b + 37)])
    (seqL [.emit (const 2), .emit (var (b + 29)), .emit (var (b + 30)),
      domGenP b (b + 37), permGenP (var (b + 32)) (b + 37), permGenP (const 0) (b + 37)])

/-- The initialization number of location `v`. -/
def initXP (vX : Xp) : Xp := add (Xp.eq vX qacc) (mulC 2 (Xp.eq vX qdet))

/-- The locations (run at depth `b`). -/
def locGenP (b : ℕ) : Gn :=
  .loop qW (seqL [.emit (initXP (var (b + 1))), .emit (mul qP (add qS (const 1))),
    .loop (add qS (const 1)) (.loop qP (.seq (.emit (var (b + 3))) (bitsGenP (var (b + 5))
      (b + 6))))])

/-- **The packed generator of the system description** (run on the globals). -/
def sysGenP (M : Machine) : Gn :=
  seqL [.emit (add qS (const 1)), .emit qℓ, .emit qW, locGenP 19, .emit qE,
    schEnumP M 19 qS qH qR qN qr qp0 qEc (schBodyP 19)]

end Gn

variable {M : Machine} {x y : List Bool} {s ℓ H : ℕ}

lemma eval_posX {σ : List ℕ} (hG : GlobP M x s ℓ H σ) {iX : Xp} (hi : iX.eval σ ≤ s) :
    (posX iX).eval σ = iX.eval σ * ℓ := by
  rw [posX, eval_minQ, Xp.eval_mul, hG.vℓ, show qΛ.eval σ = σ.getD 4 0 from rfl]
  have h1 := hG.eΛ
  have h2 : ℓ * iX.eval σ ≤ (s + 1) * ℓ := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
  rw [min_eq_left (le_trans h2 h1), Nat.mul_comm]

/-! ## Domains -/

lemma flatMap_range16 {β : Type} (q : ℕ) (G : ℕ → List β) :
    (List.range 16).flatMap (fun r => if (r + 16 * q) % 16 = 1 then G r else []) = G 1 := by
  have : ∀ r ∈ List.range 16, (if (r + 16 * q) % 16 = 1 then G r else []) =
      if 1 = r then G r else [] := fun r hr => by
    rw [List.mem_range] at hr
    have e : (r + 16 * q) % 16 = r := by omega
    rw [e]
    by_cases h : r = 1
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [List.flatMap_congr this, Gn.flatMap_range_ite]
  simp

lemma out_domLoopsP {τ : List ℕ} {D : ℕ} (hτ : τ.length = D) (hG : GlobP M x s ℓ H τ)
    (V body : Gn) :
    (Gn.domLoopsP D V body).out y τ =
      (List.range (s + 1)).flatMap fun i => (List.range (2 ^ ℓ)).flatMap fun v =>
        body.out y (τ ++ [s + 1, i, 16 * 2 ^ ℓ, 1 + 16 * v, inBit y (1 + 16 * v), v,
          (V.out y (τ ++ [s + 1, i, 16 * 2 ^ ℓ, 1 + 16 * v, inBit y (1 + 16 * v), v,
            0])).length]) := by
  have hS : (add qS (const 1)).eval τ = s + 1 := by rw [Xp.eval_add, hG.vS]; rfl
  simp only [Gn.domLoopsP, Gn.out, hS]
  refine List.flatMap_congr fun i _ => ?_
  have hP : (mulC 16 qP).eval (τ ++ [s + 1, i]) = 16 * 2 ^ ℓ := by
    rw [Xp.eval_mulC, (hG.append _).vP]
  rw [hP, Gn.flatMap_range_mul]
  refine List.flatMap_congr fun v _ => ?_
  have hk : ∀ r, (var (D + 3)).eval (τ ++ [s + 1, i] ++ [16 * 2 ^ ℓ, r + 16 * v,
      inBit y (r + 16 * v)]) = r + 16 * v := fun r => by
    rw [Xp.eval_var, List.append_assoc, show D + 3 = τ.length + 3 by omega, getD_app]; rfl
  simp only [Gn.out_when, eval_isX1, hk]
  have e : ∀ r, (if (if (r + 16 * v) % 16 = 1 then 1 else 0) ≠ 0 then
      (Gn.bind (shr (var (D + 3)) (const 4)) (Gn.count V body)).out y
        (τ ++ [s + 1, i] ++ [16 * 2 ^ ℓ, r + 16 * v, inBit y (r + 16 * v)]) else []) =
      if (r + 16 * v) % 16 = 1 then
      (Gn.bind (shr (var (D + 3)) (const 4)) (Gn.count V body)).out y
        (τ ++ [s + 1, i] ++ [16 * 2 ^ ℓ, r + 16 * v, inBit y (r + 16 * v)]) else [] := by
    intro r; split_ifs <;> simp_all
  simp only [e]
  rw [flatMap_range16 v (fun r => (Gn.bind (shr (var (D + 3)) (const 4)) (Gn.count V body)).out y
        (τ ++ [s + 1, i] ++ [16 * 2 ^ ℓ, r + 16 * v, inBit y (r + 16 * v)]))]
  have hv : (shr (var (D + 3)) (const 4)).eval
      (τ ++ [s + 1, i, 16 * 2 ^ ℓ, 1 + 16 * v, inBit y (1 + 16 * v)]) = v := by
    have := hk 1
    simp only [List.append_assoc, List.cons_append, List.nil_append] at this
    rw [Xp.eval_shr, this, Xp.eval_const]; norm_num; omega
  simp only [Gn.out, List.append_assoc, List.cons_append, List.nil_append]
  simp only [hv]

lemma out_bitsGenP {σ : List ℕ} {D : ℕ} (hσ : σ.length = D) (hG : GlobP M x s ℓ H σ) (vX : Xp)
    (hv : vX.Bnd D) : (Gn.bitsGenP vX D).out y σ = bitsL ℓ (vX.eval σ) := by
  simp only [Gn.bitsGenP, Gn.out, hG.vℓ]
  rw [← List.map_eq_flatMap, bitsL]
  refine List.map_congr_left fun t _ => ?_
  rw [eval_odd, eval_shr, eval_append hσ _ hv, eval_var, ← hσ, getD_app]
  show _ = if (vX.eval σ).testBit t then 1 else 0
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  have := Nat.mod_two_eq_zero_or_one (vX.eval σ / 2 ^ t)
  rcases this with h | h <;> simp [h]

/-- The stack of the domain loops at a coordinate. -/
abbrev dstk (τ : List ℕ) (s ℓ i v : ℕ) (y : List Bool) (c : ℕ) : List ℕ :=
  τ ++ [s + 1, i, 16 * 2 ^ ℓ, 1 + 16 * v, inBit y (1 + 16 * v), v, c]

lemma dstk_getD {τ : List ℕ} {D : ℕ} (hτ : τ.length = D) (i v c : ℕ) :
    (dstk τ s ℓ i v y c).getD (D + 1) 0 = i ∧ (dstk τ s ℓ i v y c).getD (D + 4) 0 =
      inBit y (1 + 16 * v) ∧ (dstk τ s ℓ i v y c).getD (D + 5) 0 = v ∧
      (dstk τ s ℓ i v y c).getD (D + 6) 0 = c := by
  subst hτ
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [dstk, getD_app] <;> rfl

lemma out_domBodyP' {σ : List ℕ} {D : ℕ} (hσ : σ.length = D) (hG : GlobP M x s ℓ H σ)
    (i v c : ℕ) :
    (Gn.domBodyP' D).out y (dstk σ s ℓ i v y c) = if c = 0 then i :: bitsL ℓ v else [] := by
  have hG' := hG.append [s + 1, i, 16 * 2 ^ ℓ, 1 + 16 * v, inBit y (1 + 16 * v), v, c]
  have hl : (dstk σ s ℓ i v y c).length = D + 7 := by simp [hσ]
  obtain ⟨e1, -, e5, e6⟩ := dstk_getD (s := s) (ℓ := ℓ) (y := y) hσ i v c
  rw [Gn.domBodyP', Gn.out_when, eval_eq_const, eval_var, e6]
  by_cases hc : c = 0
  · subst hc
    simp only [if_true, ne_eq, one_ne_zero, not_false_eq_true]
    simp only [Gn.out]
    rw [out_bitsGenP hl hG' _ (show (var (D + 5)).Bnd (D + 7) from show D + 5 < D + 7 by omega),
      Xp.eval_var, Xp.eval_var, e1, e5]
    rfl
  · simp [hc]

lemma out_domBodyP {σ : List ℕ} {D : ℕ} (hσ : σ.length = D) (hG : GlobP M x s ℓ H σ)
    (i v c : ℕ) :
    (Gn.domBodyP D).out y (dstk σ s ℓ i v y c) = if c = 0 then [i * 2 ^ ℓ + v] else [] := by
  have hG' := hG.append [s + 1, i, 16 * 2 ^ ℓ, 1 + 16 * v, inBit y (1 + 16 * v), v, c]
  obtain ⟨e1, -, e5, e6⟩ := dstk_getD (s := s) (ℓ := ℓ) (y := y) hσ i v c
  rw [Gn.domBodyP, Gn.out_when, eval_eq_const, eval_var, e6]
  by_cases hc : c = 0
  · subst hc
    simp only [if_true, ne_eq, one_ne_zero, not_false_eq_true]
    simp only [Gn.out, eval_add, eval_shl, eval_var, e1, e5, hG'.vℓ]
  · simp [hc]

open Classical in
/-- Membership of `(i, toBlk v)` in the domain of a schema. -/
noncomputable def memBP {N : ℕ} (sc : Schema (s + 1) ℓ N) (i v : ℕ) : Bool :=
  if h : i < s + 1 then decide (((⟨i, h⟩, toBlk ℓ v) : Coord (s + 1) ℓ) ∈ sc.domain) else false

lemma memBP_iff {N : ℕ} (sc : Schema (s + 1) ℓ N) {i : ℕ} (hi : i < s + 1) (v : ℕ) :
    memBP sc i v = true ↔ ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) ∈ sc.domain := by
  classical
  simp [memBP, hi]

lemma violAtP_nil_iff {ρ τ τ' : List ℕ} {b D e : ℕ}
    {sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations}
    (hG : GlobP M x s ℓ H ρ) (hρ : ρ.length = b) (hctx : SchCtx M x s ℓ H b ρ τ e sc)
    (hτ' : τ'.take (b + 37) = τ) (hD : τ'.length = D) (hbD : b + 37 ≤ D) (hℓ : 0 < ℓ)
    (hy : ∀ v < x.length, inBit y (1 + 16 * v) = inBit x v)
    {i v : ℕ} (hi : i < s + 1) (hv : v < 2 ^ ℓ) :
    (Gn.violAtP b D).out y (dstk τ' s ℓ i v y 0) = [] ↔
      ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) ∈ sc.domain := by
  have hb := hρ ▸ hG.len
  have hGτ : GlobP M x s ℓ H τ := hG.of_take hρ hctx.2.1
  have hGτ' : GlobP M x s ℓ H τ' := hGτ.of_take hctx.1 hτ'
  have hGσ := hGτ'.append [s + 1, i, 16 * 2 ^ ℓ, 1 + 16 * v, inBit y (1 + 16 * v), v, 0]
  obtain ⟨e1, e4, e5, -⟩ := dstk_getD (s := s) (ℓ := ℓ) (y := y) hD i v 0
  have hl : (dstk τ' s ℓ i v y 0).length = D + 7 := by simp [hD]
  refine violGenP_nil_iff_mem (τ := τ) hctx.1 hctx.2.2.2 hl ?_ (by omega) ?_ _ hGσ.vS
    (by rw [eval_var, e1]) ?_ (by rw [eval_var, e5]; simp [regVal_toBlk hv])
    ?_ hGσ.vℓ hGσ.vH hℓ
  · rw [dstk, List.take_append_of_le_length (by omega), hτ']
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨show _ < _ by omega, bnd_minQ ⟨show 7 < D + 7 by omega, show D + 1 < D + 7 by omega,
      show D + 1 < D + 7 by omega⟩ (show 4 < D + 7 by omega), show _ < _ by omega,
      ⟨show D + 4 < D + 7 by omega, ⟨show D + 5 < D + 7 by omega, show 1 < D + 7 by omega⟩,
        ⟨show D + 5 < D + 7 by omega, show 1 < D + 7 by omega⟩⟩,
      show 7 < D + 7 by omega, show 8 < D + 7 by omega⟩
  · rw [eval_posX hGσ (by rw [eval_var, e1]; omega), eval_var, e1]
  · rw [regVal_toBlk hv, eval_mul, eval_lt_eq, eval_var, eval_var, eval_var, e4, e5,
      show (dstk τ' s ℓ i v y 0).getD 1 0 = x.length from hGσ.en]
    by_cases hvx : v < x.length
    · rw [if_pos hvx, Nat.mul_one, hy v hvx]
    · rw [if_neg hvx, Nat.mul_zero]
      unfold inBit
      rw [List.drop_eq_nil_of_le (by omega)]
      rfl

lemma out_domPassP {ρ τ τ' : List ℕ} {b D e : ℕ}
    {sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations}
    (hG : GlobP M x s ℓ H ρ) (hρ : ρ.length = b) (hctx : SchCtx M x s ℓ H b ρ τ e sc)
    (hτ' : τ'.take (b + 37) = τ) (hD : τ'.length = D) (hbD : b + 37 ≤ D) (hℓ : 0 < ℓ)
    (hy : ∀ v < x.length, inBit y (1 + 16 * v) = inBit x v) :
    (Gn.domLoopsP D (Gn.violAtP b D) (Gn.domBodyP D)).out y τ' = domL (s + 1) ℓ (memBP sc) := by
  have hGτ : GlobP M x s ℓ H τ := hG.of_take hρ hctx.2.1
  have hGτ' : GlobP M x s ℓ H τ' := hGτ.of_take hctx.1 hτ'
  rw [out_domLoopsP hD hGτ']
  unfold domL
  refine List.flatMap_congr fun i hi => List.flatMap_congr fun v hv => ?_
  rw [List.mem_range] at hi hv
  have hviol := violAtP_nil_iff hG hρ hctx hτ' hD hbD hℓ hy hi hv
  rw [← memBP_iff sc hi v] at hviol
  rw [show τ' ++ [s + 1, i, 16 * 2 ^ ℓ, 1 + 16 * v, inBit y (1 + 16 * v), v,
    ((Gn.violAtP b D).out y (dstk τ' s ℓ i v y 0)).length] =
    dstk τ' s ℓ i v y ((Gn.violAtP b D).out y (dstk τ' s ℓ i v y 0)).length from rfl,
    out_domBodyP hD hGτ']
  by_cases hm : memBP sc i v = true
  · rw [if_pos (List.length_eq_zero_iff.mpr (hviol.mpr hm)), if_pos hm]
  · rw [if_neg (fun h => hm (hviol.mp (List.length_eq_zero_iff.mp h))), if_neg hm]

lemma out_domPassP' {ρ τ τ' : List ℕ} {b D e : ℕ}
    {sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations}
    (hG : GlobP M x s ℓ H ρ) (hρ : ρ.length = b) (hctx : SchCtx M x s ℓ H b ρ τ e sc)
    (hτ' : τ'.take (b + 37) = τ) (hD : τ'.length = D) (hbD : b + 37 ≤ D) (hℓ : 0 < ℓ)
    (hy : ∀ v < x.length, inBit y (1 + 16 * v) = inBit x v) :
    (Gn.domLoopsP D (Gn.violAtP b D) (Gn.domBodyP' D)).out y τ' = cdL (s + 1) ℓ (memBP sc) := by
  have hGτ : GlobP M x s ℓ H τ := hG.of_take hρ hctx.2.1
  have hGτ' : GlobP M x s ℓ H τ' := hGτ.of_take hctx.1 hτ'
  rw [out_domLoopsP hD hGτ']
  unfold cdL
  refine List.flatMap_congr fun i hi => List.flatMap_congr fun v hv => ?_
  rw [List.mem_range] at hi hv
  have hviol := violAtP_nil_iff hG hρ hctx hτ' hD hbD hℓ hy hi hv
  rw [← memBP_iff sc hi v] at hviol
  rw [show τ' ++ [s + 1, i, 16 * 2 ^ ℓ, 1 + 16 * v, inBit y (1 + 16 * v), v,
    ((Gn.violAtP b D).out y (dstk τ' s ℓ i v y 0)).length] =
    dstk τ' s ℓ i v y ((Gn.violAtP b D).out y (dstk τ' s ℓ i v y 0)).length from rfl,
    out_domBodyP' hD hGτ']
  by_cases hm : memBP sc i v = true
  · rw [if_pos (List.length_eq_zero_iff.mpr (hviol.mpr hm)), if_pos hm]
  · rw [if_neg (fun h => hm (hviol.mp (List.length_eq_zero_iff.mp h))), if_neg hm]

lemma out_domGenP {ρ τ τ' : List ℕ} {b D e : ℕ}
    {sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations}
    (hG : GlobP M x s ℓ H ρ) (hρ : ρ.length = b) (hctx : SchCtx M x s ℓ H b ρ τ e sc)
    (hτ' : τ'.take (b + 37) = τ) (hD : τ'.length = D) (hbD : b + 37 ≤ D) (hℓ : 0 < ℓ)
    (hy : ∀ v < x.length, inBit y (1 + 16 * v) = inBit x v) :
    (Gn.domGenP b D).out y τ' =
      (domL (s + 1) ℓ (memBP sc)).length :: cdL (s + 1) ℓ (memBP sc) := by
  have ht : ∀ c, (τ' ++ [c]).take (b + 37) = τ := fun c => by
    rw [List.take_append_of_le_length (by omega), hτ']
  have hl : ∀ c, (τ' ++ [c]).length = D + 1 := fun c => by simp [hD]
  simp only [Gn.domGenP, Gn.out]
  rw [out_domPassP hG hρ hctx (ht 0) (hl 0) (by omega) hℓ hy,
    out_domPassP' hG hρ hctx (ht _) (hl _) (by omega) hℓ hy]
  simp only [eval_var, List.singleton_append]
  rw [← hD, List.getD_append_right _ _ _ _ le_rfl]
  simp

/-! ## Permutations -/

lemma bit_val (m k : ℕ) : (if m.testBit k then 1 else 0) = m / 2 ^ k % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ k) with h | h <;> simp [h]

lemma out_permGenP {σ : List ℕ} {D : ℕ} (hσ : σ.length = D) (hG : GlobP M x s ℓ H σ) (mX : Xp)
    (hm : mX.Bnd D) :
    (Gn.permGenP mX D).out y σ =
      List.range (s + 1) ++
        (List.range (s + 1)).flatMap (fun i => bitsL ℓ (shiftVal s ℓ (mX.eval σ) i)) := by
  have hS : (add qS (const 1)).eval σ = s + 1 := by rw [Xp.eval_add, hG.vS]; rfl
  simp only [Gn.permGenP, Gn.out, hS]
  congr 1
  · rw [← List.map_eq_flatMap]
    conv_rhs => rw [← List.map_id (List.range (s + 1))]
    refine List.map_congr_left fun k _ => ?_
    rw [eval_var, ← hσ, getD_app]; rfl
  · refine List.flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    have hG2 := hG.append [s + 1, i]
    rw [hG2.vℓ, bitsL, List.map_eq_flatMap]
    refine List.flatMap_congr fun t ht => ?_
    rw [List.mem_range] at ht
    set τ := σ ++ [s + 1, i] ++ [ℓ, t] with hτ
    have hGτ : GlobP M x s ℓ H τ := hG2.append _
    have hτl : τ.length = D + 4 := by simp [hτ, hσ]
    have ei : (var (D + 1)).eval τ = i := by
      rw [eval_var, hτ, List.append_assoc, ← hσ, getD_app]; rfl
    have et : (var (D + 3)).eval τ = t := by
      rw [eval_var, hτ, List.append_assoc, ← hσ, getD_app]; rfl
    have emτ : mX.eval τ = mX.eval σ := by
      rw [hτ, List.append_assoc]; exact eval_append hσ _ hm
    try simp only [Gn.out]
    rw [Xp.eval_lt_eq, ei, hGτ.vS]
    by_cases his : i < s
    · rw [if_pos his]
      simp only [ne_eq, one_ne_zero, not_false_eq_true, if_true, Gn.out]
      rw [eval_odd, eval_shr, eval_add, eval_posX hGτ (by rw [ei]; omega), ei, et, emτ]
      rw [shiftVal, if_pos his, ← bit_val, testBit_field]
      simp [ht, Nat.add_comm t]
    · rw [if_neg his]
      simp only [ne_eq, not_true_eq_false, if_false, Gn.out]
      have his' : i = s := by omega
      have hGτ0 : GlobP M x s ℓ H (τ ++ [0]) := hGτ.append _
      have hc : (List.flatMap (fun k => Gn.out y (Gn.when (odd (shr mX (add (posX (var (D + 6)))
          (var (D + 3))))) (Gn.emit (const 0))) (τ ++ [0] ++ [qS.eval (τ ++ [0]), k]))
          (List.range (qS.eval (τ ++ [0])))) =
          (List.range s).flatMap fun i' => if (mX.eval σ).testBit (i' * ℓ + t) then [0] else [] := by
        rw [hGτ0.vS]
        refine List.flatMap_congr fun i' hi' => ?_
        rw [List.mem_range] at hi'
        set τ' := τ ++ [0] ++ [s, i'] with hτ'
        have hGτ' : GlobP M x s ℓ H τ' := hGτ0.append _
        have ei' : (var (D + 6)).eval τ' = i' := by
          rw [eval_var, hτ', List.append_assoc, show D + 6 = τ.length + 2 by omega, getD_app]
          rfl
        have et' : (var (D + 3)).eval τ' = t := by
          rw [hτ', List.append_assoc]
          rw [eval_append hτl _ (show (var (D + 3)).Bnd (D + 4) from show D + 3 < D + 4 by omega)]
          exact et
        have em' : mX.eval τ' = mX.eval σ := by
          rw [hτ', List.append_assoc, eval_append hτl _ (hm.mono (by omega)), emτ]
        rw [Gn.out_when, eval_odd, eval_shr, eval_add, eval_posX hGτ' (by rw [ei']; omega), ei',
          et', em', ← bit_val]
        by_cases hb : (mX.eval σ).testBit (i' * ℓ + t) <;> simp [hb, Gn.out]
      rw [hc, ← cntBits_eq]
      have e4 : (var (D + 4)).eval (τ ++ [cntBits ℓ (mX.eval σ) t s]) =
          cntBits ℓ (mX.eval σ) t s := by
        rw [eval_var, ← hτl]; simp
      rw [eval_odd, e4, his', shiftVal, if_neg (lt_irrefl s), xorFields_testBit _ ht]
      rcases Nat.mod_two_eq_zero_or_one (cntBits ℓ (mX.eval σ) t s) with h | h <;> simp [h]

/-! ## Schemas -/

/-- **The description of a schema.** -/
theorem out_schBodyP {ρ τ : List ℕ} {b e : ℕ}
    {sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations}
    (hG : GlobP M x s ℓ H ρ) (hρ : ρ.length = b) (hctx : SchCtx M x s ℓ H b ρ τ e sc)
    (hℓ : 0 < ℓ) (hy : ∀ v < x.length, inBit y (1 + 16 * v) = inBit x v) :
    (Gn.schBodyP b).out y τ = schemaDescription sc := by
  have hb := hρ ▸ hG.len
  have hGτ : GlobP M x s ℓ H τ := hG.of_take hρ hctx.2.1
  obtain ⟨g, -, hm⟩ := hctx.2.2.2
  simp only [getD_drop'] at hm
  rw [schemaDescription_of_match hm (memBP sc) (fun i hi v _ => memBP_iff sc hi v)]
  have hdom := out_domGenP hG hρ hctx (List.take_of_length_le (by rw [hctx.1])) hctx.1 le_rfl hℓ
    hy
  have hp0 := out_permGenP (y := y) hctx.1 hGτ (const 0) trivial
  have hpm := out_permGenP (y := y) hctx.1 hGτ (var (b + 32)) (show b + 32 < b + 37 by omega)
  simp only [eval_const, eval_var] at hp0 hpm
  simp only [Gn.schBodyP, Gn.out, eval_eq_const, eval_var, Gn.out_seqL, List.flatMap_cons,
    List.flatMap_nil, eval_const]
  unfold schDescN
  by_cases ht : τ.getD (b + 28) 0 = 1
  · simp only [ht, if_true, ne_eq, one_ne_zero, not_false_eq_true, decide_true]
    rw [hdom, hpm, hp0]
    simp
  · simp only [ht, if_false, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true]
    rw [hdom, hpm, hp0]
    simp

/-! ## Locations -/

lemma out_locGenP {ρ : List ℕ} {b : ℕ} (hρ : ρ.length = b) (hG : GlobP M x s ℓ H ρ) :
    (Gn.locGenP b).out y ρ =
      (List.range (Iv M x s ℓ H).numLocations).flatMap fun v =>
        ((if v = (Loc.code (Loc.accept : Loc M H)).val then 1 else 0) +
          2 * (if v = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 then 1 else 0)) ::
          ((s + 1) * 2 ^ ℓ) :: (List.range (s + 1)).flatMap fun i =>
            (List.range (2 ^ ℓ)).flatMap fun w => i :: bitsL ℓ w := by
  simp only [Gn.locGenP, Gn.out, hG.vW, Gn.out_seqL, List.flatMap_cons, List.flatMap_nil]
  refine List.flatMap_congr fun v _ => ?_
  have hG' := hG.append [(Iv M x s ℓ H).numLocations, v]
  have hv : (var (b + 1)).eval (ρ ++ [(Iv M x s ℓ H).numLocations, v]) = v := by
    rw [eval_var, ← hρ, getD_app]; rfl
  have hS : (add qS (const 1)).eval (ρ ++ [(Iv M x s ℓ H).numLocations, v]) = s + 1 := by
    rw [Xp.eval_add, hG'.vS]; rfl
  simp only [Gn.initXP, eval_add, eval_mulC, eval_eq, hv, hG'.vacc, hG'.vdet, hG'.vP, eval_mul,
    hS, List.append_nil, List.cons_append, List.nil_append, List.cons.injEq, true_and]
  refine ⟨Nat.mul_comm _ _, ?_⟩
  have hP : ∀ i, qP.eval (ρ ++ [(Iv M x s ℓ H).numLocations, v] ++ [s + 1, i]) = 2 ^ ℓ :=
    fun i => (hG'.append _).vP
  simp only [hP]
  refine List.flatMap_congr fun i _ => List.flatMap_congr fun w _ => ?_
  set σ := ρ ++ [(Iv M x s ℓ H).numLocations, v] ++ [s + 1, i] ++ [2 ^ ℓ, w] with hσ
  have hGσ : GlobP M x s ℓ H σ := (hG'.append _).append _
  have hl : σ.length = b + 6 := by simp [hσ, hρ]
  have e3 : (var (b + 3)).eval σ = i := by
    rw [eval_var, show b + 3 = (ρ ++ [(Iv M x s ℓ H).numLocations, v]).length + 1 by simp [hρ],
      hσ, List.append_assoc, getD_app]; rfl
  have e5 : (var (b + 5)).eval σ = w := by
    rw [eval_var, show b + 5 = (ρ ++ [(Iv M x s ℓ H).numLocations, v] ++ [s + 1, i]).length + 1 by
      simp [hρ], hσ, getD_app]; rfl
  rw [out_bitsGenP hl hGσ _ (show (var (b + 5)).Bnd (b + 6) from show b + 5 < b + 6 by omega), e3,
    e5]

/-- The location part of the description of `Iv`. -/
lemma locsDesc_IvP :
    (List.finRange (Iv M x s ℓ H).numLocations).flatMap
        (fun v => initNum ((Iv M x s ℓ H).init v) ::
          domainDescription ((Iv M x s ℓ H).domain v)) =
      (List.range (Iv M x s ℓ H).numLocations).flatMap fun v =>
        ((if v = (Loc.code (Loc.accept : Loc M H)).val then 1 else 0) +
          2 * (if v = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 then 1 else 0)) ::
          ((s + 1) * 2 ^ ℓ) :: (List.range (s + 1)).flatMap fun i =>
            (List.range (2 ^ ℓ)).flatMap fun w => i :: bitsL ℓ w := by
  have h1 := locsDesc_compile (APv M x s ℓ H) (Loc.query : Loc M H).code (fun _ _ => 0)
  have hacc : ((APv M x s ℓ H).loc (.prog (APv M x s ℓ H).accept)).val =
      (Loc.code (Loc.accept : Loc M H)).val := by
    rw [loc_prog_val]; rfl
  have hc : (APv M x s ℓ H).commands.length = (verifierCmds' M x s ℓ H).length := by
    simp only [AP_commands]; exact List.length_map _
  have hdet : ((APv M x s ℓ H).loc (.det .out)).val =
      numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 := by
    rw [loc_det_val, hc]
    simp only [DetSlot.toFin]
    show numLoc M H + _ * 8 + 3 = _
    ring
  rw [hacc, hdet] at h1
  exact h1

lemma flatMap_eq_range_getP {α β : Type} (l : List α) (f : α → List β) :
    l.flatMap f = (List.range l.length).flatMap fun e => (l[e]?).elim [] f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, ih, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp

/-- **The packed generator emits the description of the system.** -/
theorem out_sysGenP {ρ : List ℕ} (hρ : ρ.length = 19) (hG : GlobP M x s ℓ H ρ) (hs : 1 ≤ s)
    (hℓ : 0 < ℓ) (hy : ∀ v < x.length, inBit y (1 + 16 * v) = inBit x v) :
    (Gn.sysGenP M).out y ρ = systemDescription (Iv M x s ℓ H) := by
  obtain ⟨T, hT, hctx⟩ := schEnum_ctxP hρ hG hs
  have hS : (Iv M x s ℓ H).schemas.flatMap schemaDescription =
      (List.range (Iv M x s ℓ H).schemas.length).flatMap fun e =>
        (Gn.schBodyP 19).out y (T e) := by
    rw [flatMap_eq_range_getP]
    refine List.flatMap_congr fun e he => ?_
    rw [List.mem_range] at he
    rw [List.getElem?_eq_getElem he, Option.elim_some, out_schBodyP hG hρ (hctx e he) hℓ hy]
  have hS1 : (add qS (const 1)).eval ρ = s + 1 := by rw [Xp.eval_add, hG.vS]; rfl
  simp only [Gn.sysGenP, Gn.out_seqL, List.flatMap_cons, List.flatMap_nil, Gn.out, hS1,
    hG.vℓ, hG.vW, hG.vE, List.append_nil]
  rw [out_locGenP hρ hG, hT, systemDescription, locsDesc_IvP, hS]
  simp

end Lax119563Proofs.Reduction
