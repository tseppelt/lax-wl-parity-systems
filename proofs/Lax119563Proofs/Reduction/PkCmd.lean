import Lax119563Proofs.Reduction.CmdStk

/-!
# The command enumerator for a runtime number of blocks

`cmdEnumP M b SX HX RX body` is the command enumerator of `CmdEnum` with the number `s` of
data blocks given at runtime (the value of `SX`): the generator does not depend on `s`.
The only commands whose number depends on `s` are the tests `miss i` (`1 ≤ i < s`) of the
root cells `cell 0 0 ν (0, false)`; they are enumerated by a loop `j < s` around the moves of
each location (`j = 0`: the moves of `brs (s := 0)`, i.e. all moves but the tests `miss i`;
`j = i ≥ 1`: the test `miss i`).

To keep the stack layout of `CmdEnum` above the location number (level `b + 15`: the location
number, `b + 16`: the index of the move, `b + 17 …`: the command), the two digit loops
`t3, t2 < C` are merged into one loop `u = t2 + C t3 < C^2` (only `u` enters the location
number). The stack below the record is
`[C, t5, R, t4, C^2, u, R, t1, t1 - 1, t4 - 1, H - t1 - 1, H + 2 - t1, rest, s, j, code]`.

`out_cmdEnumP`: the body runs on the stacks `stksP` of the locations, which correspond to the
moves (`stksP_spec`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp

variable {M : Machine} {s : ℕ}

/-! ## Moves without the tests `miss i` -/

/-- A move of `SMv M 0` (no test `miss`) as a move of `SMv M s`. -/
def SMv.lift : SMv M 0 → SMv M s
  | .step k m q v dst => .step k m q v dst
  | .fork k m q l r => .fork k m q l r
  | .hit ν c dst => .hit ν c dst
  | .miss i _ => i.elim0

lemma SMv.recX_lift (R HX : Xp) (m : SMv M 0) : (m.lift (s := s)).recX R HX = m.recX R HX := by
  cases m with
  | miss i _ => exact i.elim0
  | _ => rfl

lemma SMv.bnd_lift {n : ℕ} (m : SMv M 0) (h : m.Bnd n) : (m.lift (s := s)).Bnd n := by
  cases m with
  | miss i _ => exact i.elim0
  | _ => exact h

/-- The kinds with tests `miss i` (in the branch `d = 0`): the root cells `(0, false)` of
phase `0`. -/
def SKind.missFam : SKind M → Bool
  | .cell θ _ c => decide (θ.val = 0) && decide (c = (0, false))
  | _ => false

/-- The tests `miss i`, `1 ≤ i < s`. -/
def missL (M : Machine) (s : ℕ) : List (SMv M s) :=
  ((List.finRange s).filter fun i => decide (i.val ≠ 0)).map fun i => SMv.miss i .accept

lemma map_lift_goto (dst : SLoc M) : (SMv.goto dst : SMv M 0).lift (s := s) = SMv.goto dst := rfl

/-- The branches of `brs (s := s)` are those of `brs (s := 0)`, with the tests `miss i`
appended in the branch `d = 0` of the root cells. -/
theorem selBr_brs (σ : List ℕ) (V : RVals) (K : SKind M) :
    selBr σ (K.brs (s := s) V) = (selBr σ (K.brs (s := 0) V)).map SMv.lift ++
      (if K.missFam = true ∧ V.d.eval σ = 0 then missL M s else []) := by
  cases K with
  | cell θ ν c =>
    simp only [SKind.brs, SKind.missFam]
    by_cases hθ : θ.val = 0
    · simp only [hθ, if_true]
      by_cases hd : V.d.eval σ = 0
      · have h1 : (eq V.d (const 0)).eval σ ≠ 0 := by simp [Xp.eval_eq, hd]
        simp only [selBr, h1, if_true, ne_eq, not_false_eq_true]
        by_cases hc : c = (0, false)
        · simp [hc, hd, missL, SMv.lift]
        · simp [hc, SMv.lift]
      · have h1 : ¬ (eq V.d (const 0)).eval σ ≠ 0 := by simp [Xp.eval_eq, hd]
        simp only [selBr, h1, if_false, hd, and_false, List.append_nil, Xp.eval_const, ne_eq,
          one_ne_zero, not_false_eq_true, if_true, List.map_flatMap, List.map_map]
        rfl
    · simp only [hθ, if_false, decide_false, Bool.false_and, Bool.false_eq_true, false_and,
        List.append_nil]
      by_cases hl : (lt V.d V.H).eval σ ≠ 0
      · simp only [selBr, hl, if_true, ne_eq, not_false_eq_true, List.map_map]
        rfl
      · simp only [selBr, hl, if_false, Xp.eval_const, ne_eq, one_ne_zero, not_false_eq_true,
          if_true]
        split_ifs
        · simp only [List.map_flatMap, List.map_map]; rfl
        · rfl
  | state θ p =>
    simp only [SKind.brs, SKind.missFam, Bool.false_eq_true, false_and, if_false,
      List.append_nil]
    split_ifs <;> simp only [selBr] <;> split_ifs <;> (try split_ifs) <;> simp [SMv.lift, SMv.goto]
  | headSet θ ν β =>
    simp only [SKind.brs, SKind.missFam, Bool.false_eq_true, false_and, if_false,
      List.append_nil, selBr]
    split_ifs <;> simp [SMv.lift]
  | restore θ ν c β =>
    simp only [SKind.brs, SKind.missFam, Bool.false_eq_true, false_and, if_false,
      List.append_nil, selBr]
    split_ifs
    · simp only [List.map_map]
      refine List.map_congr_left fun q _ => ?_
      simp only [Function.comp]
      split_ifs <;> rfl
    · rfl
  | baseCell ν ρ old k =>
    simp only [SKind.brs, SKind.missFam, Bool.false_eq_true, false_and, if_false,
      List.append_nil, selBr, Xp.eval_const, ne_eq, one_ne_zero, not_false_eq_true, if_true]
    split_ifs <;> rfl
  | baseState ρ k =>
    simp only [SKind.brs, SKind.missFam, Bool.false_eq_true, false_and, if_false,
      List.append_nil, selBr, Xp.eval_const, ne_eq, one_ne_zero, not_false_eq_true, if_true]
    split_ifs <;> rfl
  | _ =>
    simp only [SKind.brs, SKind.missFam, Bool.false_eq_true, false_and, if_false,
      List.append_nil, selBr]
    repeat' split_ifs
    all_goals simp only [List.map_flatMap, List.map_map, List.map_cons, List.map_nil,
      Function.comp_def, SMv.lift, SMv.goto, SMv.fork']

lemma length_selBr_brs0 (σ : List ℕ) (V : RVals) (K : SKind M) (hK : K.missFam = true)
    (hd : V.d.eval σ = 0) : (selBr σ (K.brs (s := 0) V)).length = 1 := by
  cases K with
  | cell θ ν c =>
    simp only [SKind.missFam, Bool.and_eq_true, decide_eq_true_eq] at hK
    have h1 : (eq V.d (const 0)).eval σ ≠ 0 := by simp [Xp.eval_eq, hd]
    simp only [SKind.brs, hK.1, if_true, selBr, h1, ne_eq, not_false_eq_true, if_true]
    split_ifs <;> simp
  | _ => simp [SKind.missFam] at hK

lemma map_val_finRange' (n : ℕ) : (List.finRange n).map Fin.val = List.range n :=
  List.ext_getElem (by simp) fun i _ _ => by simp

lemma filter_range_ne_zero (n : ℕ) :
    (List.range n).filter (fun i => decide (i ≠ 0)) = List.range' 1 (n - 1) := by
  rcases n with _ | n
  · rfl
  · rw [List.range_succ_eq_map, List.filter_cons]
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false,
      Nat.add_sub_cancel]
    rw [List.filter_eq_self.mpr (by simp)]
    exact List.ext_getElem (by simp) fun i h1 h2 => by simp; omega

/-! ## The enumerator -/

section Enum

variable (M)

/-- The runtime values at base `b` (`d = t1` at `b + 7`, `u = t4` at `b + 3`). -/
def rvP (b : ℕ) (HX : Xp) : RVals :=
  ⟨var (b + 7), var (b + 3), var (b + 8), var (b + 9), var (b + 10), var (b + 11), HX⟩

/-- `t1 + R (u + C^2 (t4 + R t5))`. -/
def restXP (C b : ℕ) (RX : Xp) : Xp :=
  add (var (b + 7)) (mul (add (var (b + 5)) (mulC (C * C) (add (var (b + 3))
    (mul (var (b + 1)) RX)))) RX)

/-- The runtime values are in range. -/
def validXP (b : ℕ) (HX : Xp) : SKind M → Xp
  | .cell .. | .state .. | .headSet .. | .restore .. | .gather .. =>
      lt (var (b + 7)) (add HX (const 1))
  | .headIn .. => and (lt (var (b + 7)) (add HX (const 1))) (lt (var (b + 3)) (add HX (const 1)))
  | _ => const 1

/-- The kind `K` has location number `tag + 16 rest`. -/
def matchXP (b : ℕ) (HX RX : Xp) (K : SKind M) : Xp :=
  and (eq ((K.sloc (var (b + 7)) (var (b + 3))).codeX RX HX)
    (add (const (K.sloc (var (b + 7)) (var (b + 3))).tag) (mulC 16 (var (b + 12)))))
    (validXP M b HX K)

/-- The record of the test `miss j` (`j` at level `b + 14`). -/
def missRecX (b : ℕ) (HX RX : Xp) : List Xp :=
  [var (b + 14), const 0, const 0, (SLoc.accept : SLoc M).codeX RX HX, const 0, const 2,
    var (b + 14), const 0, const 0]

/-- The test `miss j` for `j ≥ 1`, at a root cell of depth `0`. -/
def missGen (b : ℕ) (HX RX : Xp) (body : Gn) (K : SKind M) : Gn :=
  if K.missFam then
    Gn.when (and (Xp.not (eq (var (b + 14)) (const 0))) (eq (var (b + 7)) (const 0)))
      (Gn.bindL (missRecX M b HX RX) body)
  else .skip

/-- The commands of the location of kind `K`: a loop `j < s`; for `j = 0` the moves of
`brs (s := 0)`, for `j ≥ 1` the test `miss j` (root cells). -/
def kindGenP (b : ℕ) (SX HX RX : Xp) (body : Gn) (K : SKind M) : Gn :=
  .loop SX (.bind ((K.sloc (var (b + 7)) (var (b + 3))).codeX RX HX)
    (.seq (Gn.when (eq (var (b + 14)) (const 0)) (Gn.brGen RX HX body (K.brs (s := 0) (rvP b HX))))
      (missGen M b HX RX body K)))

/-- The commands of the locations with given digits, in order of the tag. -/
def tupleGenP (b : ℕ) (SX HX RX : Xp) (body : Gn) : Gn :=
  Gn.seqL ((List.range 16).map fun t =>
    Gn.firstL (matchXP M b HX RX) (kindGenP M b SX HX RX body) (kindsOfTag M t))

/-- **The command enumerator** for a runtime number `s` of blocks (the value of `SX`). -/
def cmdEnumP (b : ℕ) (SX HX RX : Xp) (body : Gn) : Gn :=
  .loop (const (cM M)) (.loop RX (.loop (const (cM M * cM M)) (.loop RX (
    Gn.bindSub (b + 8) (var (b + 7)) (const 1) (
    Gn.bindSub (b + 9) (var (b + 3)) (const 1) (
    Gn.bindSub (b + 10) HX (add (var (b + 7)) (const 1)) (
    Gn.bindSub (b + 11) (add HX (const 2)) (var (b + 7)) (
    .bind (restXP (cM M) b RX) (tupleGenP M b SX HX RX body)))))))))

/-- The stack below the location number, for the digits `t = (tag, t1, …, t5)`. -/
def stkTP (ρ : List ℕ) (H R C : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : List ℕ :=
  ρ ++ [C, t.2.2.2.2.2, R, t.2.2.2.2.1, C * C, t.2.2.1 + C * t.2.2.2.1, R, t.2.1,
    t.2.1 - 1, t.2.2.2.2.1 - 1, H - (t.2.1 + 1), H + 2 - t.2.1,
    pack R t.2.1 (pack C t.2.2.1 (pack C t.2.2.2.1 (pack R t.2.2.2.2.1 t.2.2.2.2.2)))]

/-- The stack of the body for the location `L` and the iteration `j`, below the record. -/
def stkLP (ρ : List ℕ) (H s j : ℕ) (L : Loc M H) : List ℕ :=
  stkTP ρ H (radix M H) (cM M) L.tuple ++ [s, j, (Loc.code L).val]

/-- The stacks of the body for the location `L`. -/
def stksP (b : ℕ) (HX RX : Xp) (ρ : List ℕ) (s H : ℕ) (L : Loc M H) : List (List ℕ) :=
  ((selBr (stkLP M ρ H s 0 L) (L.kind.brs (s := 0) (rvP b HX))).zipIdx.map fun p =>
    stkLP M ρ H s 0 L ++ p.2 :: (p.1.recX RX HX).map fun e => e.eval (stkLP M ρ H s 0 L)) ++
  (if L.kind.missFam = true ∧ L.tuple.2.1 = 0 then
    ((List.range s).filter fun i => decide (i ≠ 0)).map fun i =>
      stkLP M ρ H s i L ++ [i, 0, 0, (Loc.code (Loc.accept : Loc M H)).val, 0, 2, i, 0, 0]
   else [])

end Enum

/-! ## Correctness -/

section Out

variable {x y : List Bool} {ρ : List ℕ} {b H : ℕ} {SX HX RX : Xp} {body : Gn}

lemma eval_matchXP {τ : List ℕ} (hH : HX.eval τ = H) (hR : RX.eval τ = radix M H)
    (K : SKind M) :
    (matchXP M b HX RX K).eval τ ≠ 0 ↔
      K.Valid H (τ.getD (b + 7) 0) (τ.getD (b + 3) 0) ∧
      (Loc.code (K.loc H (τ.getD (b + 7) 0) (τ.getD (b + 3) 0))).val =
        (K.loc H (τ.getD (b + 7) 0) (τ.getD (b + 3) 0)).tuple.1 + 16 * τ.getD (b + 12) 0 := by
  have va : ∀ i, (lt (var (b + i)) (add HX (const 1))).eval τ =
      if τ.getD (b + i) 0 ≤ H then 1 else 0 := fun i => by
    simp only [Xp.eval_lt_eq, Xp.eval_add, Xp.eval_const, Xp.eval_var, hH]
    by_cases h : τ.getD (b + i) 0 ≤ H
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hv : (validXP M b HX K).eval τ ≤ 1 ∧
      ((validXP M b HX K).eval τ = 1 ↔ K.Valid H (τ.getD (b + 7) 0) (τ.getD (b + 3) 0)) := by
    have c1 : (const 1).eval τ ≤ 1 ∧ ((const 1).eval τ = 1 ↔ True) :=
      ⟨le_rfl, iff_of_true rfl trivial⟩
    have c2 : (lt (var (b + 7)) (add HX (const 1))).eval τ ≤ 1 ∧
        ((lt (var (b + 7)) (add HX (const 1))).eval τ = 1 ↔ τ.getD (b + 7) 0 ≤ H) := by
      rw [va]
      by_cases h : τ.getD (b + 7) 0 ≤ H
      · rw [if_pos h]; exact ⟨le_rfl, iff_of_true rfl h⟩
      · rw [if_neg h]; exact ⟨by omega, iff_of_false (by omega) h⟩
    have c3 : (and (lt (var (b + 7)) (add HX (const 1)))
        (lt (var (b + 3)) (add HX (const 1)))).eval τ ≤ 1 ∧
        ((and (lt (var (b + 7)) (add HX (const 1)))
          (lt (var (b + 3)) (add HX (const 1)))).eval τ = 1 ↔
          τ.getD (b + 7) 0 ≤ H ∧ τ.getD (b + 3) 0 ≤ H) := by
      rw [Xp.eval_and (by rw [va]; split_ifs <;> omega) (by rw [va]; split_ifs <;> omega), va, va]
      by_cases h : τ.getD (b + 7) 0 ≤ H <;> by_cases h' : τ.getD (b + 3) 0 ≤ H <;>
        simp only [h, h', if_true, if_false] <;> simp
    cases K <;> simp only [validXP, SKind.Valid] <;> first | exact c1 | exact c2 | exact c3
  have heq : (eq ((K.sloc (var (b + 7)) (var (b + 3))).codeX RX HX)
      (add (const (K.sloc (var (b + 7)) (var (b + 3))).tag)
        (mulC 16 (var (b + 12))))).eval τ ≤ 1 := by
    rw [Xp.eval_eq]; split_ifs <;> omega
  have hcx := SLoc.eval_codeX hR hH (K.sloc (var (b + 7)) (var (b + 3)))
  rw [SKind.eval_sloc] at hcx
  simp only [Xp.eval_var] at hcx
  have key : ((K.sloc (var (b + 7)) (var (b + 3))).codeX RX HX).eval τ =
      (add (const (K.sloc (var (b + 7)) (var (b + 3))).tag) (mulC 16 (var (b + 12)))).eval τ ↔
      (Loc.code (K.loc H (τ.getD (b + 7) 0) (τ.getD (b + 3) 0))).val =
        (K.loc H (τ.getD (b + 7) 0) (τ.getD (b + 3) 0)).tuple.1 + 16 * τ.getD (b + 12) 0 := by
    rw [hcx]
    simp only [Xp.eval_add, Xp.eval_const, Xp.eval_mulC, Xp.eval_var,
      SKind.tag_sloc (H := H) (d := τ.getD (b + 7) 0) (u := τ.getD (b + 3) 0)]
  unfold matchXP
  rw [Xp.eval_and heq hv.1, Xp.eval_eq]
  by_cases hc : ((K.sloc (var (b + 7)) (var (b + 3))).codeX RX HX).eval τ =
      (add (const (K.sloc (var (b + 7)) (var (b + 3))).tag) (mulC 16 (var (b + 12)))).eval τ
  · rw [if_pos hc]
    by_cases hval : (validXP M b HX K).eval τ = 1
    · rw [if_pos ⟨rfl, hval⟩]
      exact iff_of_true one_ne_zero ⟨hv.2.mp hval, key.mp hc⟩
    · rw [if_neg (fun h => hval h.2)]
      exact iff_of_false (fun h => h rfl) (fun h => hval (hv.2.mpr h.1))
  · rw [if_neg hc, if_neg (fun h => absurd h.1 (by norm_num))]
    exact iff_of_false (fun h => h rfl) (fun h => hc (key.mpr h.2))

lemma rvP_bnd (hHb : HX.Bnd b) : (rvP b HX).Bnd (b + 16) :=
  ⟨by show b + 7 < b + 16; omega, by show b + 3 < b + 16; omega,
    by show b + 8 < b + 16; omega, by show b + 9 < b + 16; omega,
    by show b + 10 < b + 16; omega, by show b + 11 < b + 16; omega,
    Xp.Bnd.mono (by omega) hHb⟩

lemma rvP_ok (hρ : ρ.length = b) (hH : HX.eval ρ = H) (hHb : HX.Bnd b) (R C : ℕ)
    (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (l : List ℕ) :
    (rvP b HX).Ok H (stkTP ρ H R C t ++ l) t.2.1 t.2.2.2.2.1 := by
  have e : ∀ i, (stkTP ρ H R C t ++ l).getD (b + i) 0 =
      ([C, t.2.2.2.2.2, R, t.2.2.2.2.1, C * C, t.2.2.1 + C * t.2.2.2.1, R, t.2.1,
      t.2.1 - 1, t.2.2.2.2.1 - 1, H - (t.2.1 + 1), H + 2 - t.2.1,
      pack R t.2.1 (pack C t.2.2.1 (pack C t.2.2.2.1 (pack R t.2.2.2.2.1 t.2.2.2.2.2)))] ++
        l).getD i 0 := fun i => by
    rw [stkTP, List.append_assoc, getD_stk hρ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp only [rvP, Xp.eval_var, e]; rfl)
    | (simp only [rvP]; rw [stkTP, List.append_assoc]; exact (Xp.eval_append hρ _ hHb).trans hH)
    | (simp only [rvP, Xp.eval_var, e, List.cons_append, List.getD_cons_succ,
        List.getD_cons_zero]; omega)

lemma length_stkTP (hρ : ρ.length = b) (R C : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :
    (stkTP ρ H R C t).length = b + 13 := by
  simp [stkTP, hρ]

lemma length_stkLP (hρ : ρ.length = b) (j : ℕ) (L : Loc M H) :
    (stkLP M ρ H s j L).length = b + 16 := by
  simp [stkLP, stkTP, hρ]

lemma flatMap_filter_eq {β : Type} (p : ℕ → Bool) (B : ℕ → List β) (l : List ℕ) :
    (l.filter p).flatMap B = l.flatMap fun j => if p j then B j else [] := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [List.filter_cons, h, ih]

lemma flatMap_range_first {β : Type} {n : ℕ} (hn : 1 ≤ n) (A : List β) (Y : ℕ → List β)
    (hY : Y 0 = []) :
    (List.range n).flatMap (fun j => (if j = 0 then A else []) ++ Y j) =
      A ++ (List.range n).flatMap Y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_cons, hY, List.flatMap_map,
    List.flatMap_map]
  simp only [if_true, List.append_nil, Nat.succ_ne_zero, if_false, List.nil_append]

section Kind

variable (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hSb : SX.Bnd b)
  (hH : HX.eval ρ = H) (hR : RX.eval ρ = radix M H) (hS : SX.eval ρ = s)
include hρ hHb hRb hSb hH hR hS

/-- The commands of one location. -/
lemma out_kindGenP (hs : 1 ≤ s) (L : Loc M H) :
    (kindGenP M b SX HX RX body L.kind).out y (stkTP ρ H (radix M H) (cM M) L.tuple) =
      (stksP M b HX RX ρ s H L).flatMap (body.out y) := by
  set τ := stkTP ρ H (radix M H) (cM M) L.tuple with hτ
  have hτl : τ.length = b + 13 := length_stkTP hρ _ _ _
  have ev : ∀ {e : Xp}, e.Bnd b → ∀ l, e.eval (τ ++ l) = e.eval ρ := fun he l => by
    rw [hτ, stkTP, List.append_assoc]; exact Xp.eval_append hρ _ he
  have hV : ∀ l, (rvP b HX).Ok H (τ ++ l) L.tuple.2.1 L.tuple.2.2.2.2.1 :=
    fun l => rvP_ok hρ hH hHb _ _ _ l
  obtain ⟨-, hval, hloc⟩ := L.kind_spec
  have hcode : ∀ j, ((L.kind.sloc (var (b + 7)) (var (b + 3))).codeX RX HX).eval
      (τ ++ [s, j]) = (Loc.code L).val := fun j => by
    have e7 : (var (b + 7)).eval (τ ++ [s, j]) = L.tuple.2.1 := (hV [s, j]).d
    have e3 : (var (b + 3)).eval (τ ++ [s, j]) = L.tuple.2.2.2.2.1 := (hV [s, j]).u
    rw [SLoc.eval_codeX ((ev hRb _).trans hR) ((ev hHb _).trans hH), SKind.eval_sloc, e7, e3,
      hloc]
  have hstk : ∀ j, τ ++ [s, j] ++ [(Loc.code L).val] = stkLP M ρ H s j L := fun j => by
    simp [stkLP, hτ]
  have hσl : ∀ j, (stkLP M ρ H s j L).length = b + 16 := fun j => length_stkLP hρ j L
  have gj : ∀ j, (stkLP M ρ H s j L).getD (b + 14) 0 = j := fun j => by
    rw [← hstk, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hτl]
    simp
  have g7 : ∀ j, (stkLP M ρ H s j L).getD (b + 7) 0 = L.tuple.2.1 := fun j => by
    have := (hV ([s, j] ++ [(Loc.code L).val])).d
    rw [← List.append_assoc, hstk] at this
    simpa [rvP] using this
  have hSτ : SX.eval τ = s := by have := ev hSb []; simpa using this.trans hS
  simp only [kindGenP, Gn.out, hSτ, hcode, hstk]
  -- the two parts of one iteration
  have hA : ∀ j, (Gn.when (eq (var (b + 14)) (const 0))
      (Gn.brGen RX HX body (L.kind.brs (s := 0) (rvP b HX)))).out y (stkLP M ρ H s j L) =
      if j = 0 then ((selBr (stkLP M ρ H s 0 L) (L.kind.brs (s := 0) (rvP b HX))).zipIdx.flatMap
        fun p => body.out y (stkLP M ρ H s 0 L ++ (p.2 :: (p.1.recX RX HX).map
          fun e => e.eval (stkLP M ρ H s 0 L)))) else [] := fun j => by
    rw [Gn.out_when, Xp.eval_eq, Xp.eval_var, gj, Xp.eval_const]
    by_cases hj : j = 0
    · subst hj
      simp only [if_true, ne_eq, one_ne_zero, not_false_eq_true]
      have hRσ : RX.Bnd (b + 16) := Xp.Bnd.mono (by omega) hRb
      have hHσ : HX.Bnd (b + 16) := Xp.Bnd.mono (by omega) hHb
      exact Gn.out_brGen (hσl 0) hRσ hHσ body _ (SKind.bnd_brs (rvP_bnd hHb) L.kind)
    · simp [hj]
  have hB : ∀ j, (missGen M b HX RX body L.kind).out y (stkLP M ρ H s j L) =
      if L.kind.missFam = true ∧ L.tuple.2.1 = 0 ∧ j ≠ 0 then
        body.out y (stkLP M ρ H s j L ++
          [j, 0, 0, (Loc.code (Loc.accept : Loc M H)).val, 0, 2, j, 0, 0]) else [] := fun j => by
    unfold missGen
    by_cases hm : L.kind.missFam = true
    · simp only [hm, if_true, true_and]
      rw [Gn.out_when]
      have e1 : (Xp.not (eq (var (b + 14)) (const 0))).eval (stkLP M ρ H s j L) ≤ 1 := by
        simp only [Xp.eval_not, Xp.eval_lt_eq]; split_ifs <;> omega
      have e2 : (eq (var (b + 7)) (const 0)).eval (stkLP M ρ H s j L) ≤ 1 := by
        rw [Xp.eval_eq]; split_ifs <;> omega
      have hcond : (and (Xp.not (eq (var (b + 14)) (const 0))) (eq (var (b + 7)) (const 0))).eval
          (stkLP M ρ H s j L) ≠ 0 ↔ (L.tuple.2.1 = 0 ∧ j ≠ 0) := by
        rw [Xp.eval_and e1 e2]
        simp only [Xp.eval_not, Xp.eval_eq, Xp.eval_var, gj, g7, Xp.eval_const]
        by_cases h1 : L.tuple.2.1 = 0 <;> by_cases h2 : j = 0 <;> simp [h1, h2]
      by_cases hc : L.tuple.2.1 = 0 ∧ j ≠ 0
      · rw [if_pos (hcond.mpr hc), if_pos hc, Gn.out_bindL body _ (hσl j)]
        · congr 2
          have hRj : RX.eval (stkLP M ρ H s j L) = radix M H := by
            rw [← hstk, List.append_assoc]; exact (ev hRb _).trans hR
          have hHj : HX.eval (stkLP M ρ H s j L) = H := by
            rw [← hstk, List.append_assoc]; exact (ev hHb _).trans hH
          simp only [missRecX, List.map_cons, List.map_nil, Xp.eval_var, gj, Xp.eval_const,
            SLoc.eval_codeX hRj hHj, SLoc.eval]
        · intro e he
          simp only [missRecX, List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals first
            | trivial
            | exact (show b + 14 < b + 16 by omega)
            | exact SLoc.bnd_codeX (Xp.Bnd.mono (by omega) hRb) (Xp.Bnd.mono (by omega) hHb) _
                trivial
      · rw [if_neg (fun h => hc (hcond.mp h)), if_neg hc]
    · simp only [hm, Bool.false_eq_true, if_false, false_and]; rfl
  simp only [hA, hB]
  rw [flatMap_range_first hs _ _ (by simp)]
  rw [stksP, List.flatMap_append, List.flatMap_map]
  congr 1
  by_cases hc : L.kind.missFam = true ∧ L.tuple.2.1 = 0
  · rw [if_pos hc, List.flatMap_map, flatMap_filter_eq]
    refine List.flatMap_congr fun j _ => ?_
    by_cases hj : j = 0 <;> simp [hj, hc]
  · rw [if_neg hc]
    simp only [List.flatMap_nil]
    refine List.flatMap_eq_nil_iff.mpr fun j _ => ?_
    rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩)]

/-- The output for one tag and given digits. -/
lemma out_tagP (hs : 1 ≤ s) {t t1 t2 t3 t4 t5 : ℕ} (ht : t < 16)
    (h1 : t1 < radix M H) (h2 : t2 < cM M) (h3 : t3 < cM M) (h4 : t4 < radix M H)
    (h5 : t5 < cM M) :
    (Gn.firstL (matchXP M b HX RX) (kindGenP M b SX HX RX body) (kindsOfTag M t)).out y
        (stkTP ρ H (radix M H) (cM M) (t, t1, t2, t3, t4, t5)) =
      match decodeLoc M H (pack 16 t (pack (radix M H) t1 (pack (cM M) t2
          (pack (cM M) t3 (pack (radix M H) t4 t5))))) with
      | some L => (stksP M b HX RX ρ s H L).flatMap (body.out y)
      | none => [] := by
  set τ := stkTP ρ H (radix M H) (cM M) (t, t1, t2, t3, t4, t5) with hτ
  have g : ∀ i, τ.getD (b + i) 0 = ([cM M, t5, radix M H, t4, cM M * cM M, t2 + cM M * t3,
      radix M H, t1, t1 - 1, t4 - 1, H - (t1 + 1), H + 2 - t1,
      pack (radix M H) t1 (pack (cM M) t2 (pack (cM M) t3
        (pack (radix M H) t4 t5)))]).getD i 0 := fun i => by
    rw [hτ, stkTP, getD_stk hρ]
  have g7 : τ.getD (b + 7) 0 = t1 := by rw [g]; rfl
  have g3 : τ.getD (b + 3) 0 = t4 := by rw [g]; rfl
  have g12 : τ.getD (b + 12) 0 = pack (radix M H) t1 (pack (cM M) t2 (pack (cM M) t3
      (pack (radix M H) t4 t5))) := by rw [g]; rfl
  have hHτ : HX.eval τ = H := by rw [hτ, stkTP]; exact (Xp.eval_append hρ _ hHb).trans hH
  have hRτ : RX.eval τ = radix M H := by
    rw [hτ, stkTP]; exact (Xp.eval_append hρ _ hRb).trans hR
  rw [Gn.out_firstL]
  cases hf : (kindsOfTag M t).find? (fun K => (matchXP M b HX RX K).eval τ ≠ 0) with
  | some K =>
    have hK := List.mem_of_find?_eq_some hf
    have hm := List.find?_some hf
    simp only [decide_eq_true_eq] at hm
    rw [eval_matchXP hHτ hRτ, g7, g3, g12, tag_of_mem_kindsOfTag hK] at hm
    obtain ⟨hV, hc⟩ := hm
    set L := K.loc H t1 t4 with hL
    have hcode : (Loc.code L).val = pack 16 t (pack (radix M H) t1 (pack (cM M) t2
        (pack (cM M) t3 (pack (radix M H) t4 t5)))) := hc
    have htup := tuple_of_code ht h1 h2 h3 h4 h5 hcode
    rw [← hcode, decodeLoc_code]
    simp only
    have hkind : L.kind = K := SKind.kind_loc K
    have := out_kindGenP (body := body) (y := y) hρ hHb hRb hSb hH hR hS hs L
    rw [hkind, htup] at this
    exact this
  | none =>
    cases hd : decodeLoc M H (pack 16 t (pack (radix M H) t1 (pack (cM M) t2
        (pack (cM M) t3 (pack (radix M H) t4 t5))))) with
    | none => rfl
    | some L =>
      exfalso
      have hcode := code_of_decodeLoc hd
      have htup := tuple_of_code ht h1 h2 h3 h4 h5 hcode
      obtain ⟨hmem, hval, hloc⟩ := L.kind_spec
      rw [htup] at hmem hval hloc
      simp only at hmem hval hloc
      have := List.find?_eq_none.mp hf L.kind hmem
      apply this
      simp only [decide_eq_true_eq]
      rw [eval_matchXP hHτ hRτ, g7, g3, g12, hloc, htup]
      exact ⟨hval, hcode⟩

/-- **The output of the command enumerator.** -/
theorem out_cmdEnumP (hs : 1 ≤ s) :
    (cmdEnumP M b SX HX RX body).out y ρ = (List.range (numLoc M H)).flatMap fun c =>
      match decodeLoc M H c with
      | some L => (stksP M b HX RX ρ s H L).flatMap (body.out y)
      | none => [] := by
  rw [numLoc, flatMap_range_digits]
  have hCe : ∀ l, (const (cM M)).eval (ρ ++ l) = cM M := fun _ => rfl
  have hCCe : ∀ l, (const (cM M * cM M)).eval (ρ ++ l) = cM M * cM M := fun _ => rfl
  have hRe : ∀ l, RX.eval (ρ ++ l) = radix M H := fun l => (Xp.eval_append hρ l hRb).trans hR
  have hHe : ∀ l, HX.eval (ρ ++ l) = H := fun l => (Xp.eval_append hρ l hHb).trans hH
  simp only [cmdEnumP, Gn.out, List.append_assoc, List.cons_append, List.nil_append, hRe, hR,
    hCe, hCCe, Xp.eval_const]
  refine List.flatMap_congr fun t5 ht5 => List.flatMap_congr fun t4 ht4 => ?_
  rw [Gn.flatMap_range_mul]
  refine List.flatMap_congr fun t3 ht3 => List.flatMap_congr fun t2 ht2 =>
    List.flatMap_congr fun t1 ht1 => ?_
  rw [List.mem_range] at ht5 ht4 ht3 ht2 ht1
  have hl : ∀ k (l : List ℕ), l.length = k → (ρ ++ l).length = b + k := fun k l h => by
    simp [hρ, h]
  rw [Gn.out_bindSub (a := var (b + 7)) (b := const 1) (hl 8 _ rfl)
    (by show b + 7 < b + 8; omega) trivial]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [Gn.out_bindSub (a := var (b + 3)) (b := const 1) (hl 9 _ rfl)
    (by show b + 3 < b + 9; omega) trivial]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [Gn.out_bindSub (a := HX) (b := add (var (b + 7)) (const 1)) (hl 10 _ rfl)
    (Xp.Bnd.mono (by omega) hHb)
    ⟨(by show b + 7 < b + 10; omega), trivial⟩]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [Gn.out_bindSub (a := add HX (const 2)) (b := var (b + 7)) (hl 11 _ rfl)
    ⟨Xp.Bnd.mono (by omega) hHb, trivial⟩
    (by show b + 7 < b + 11; omega)]
  simp only [Gn.out, tupleGenP, Gn.out_seqL, List.flatMap_map, List.append_assoc,
    List.cons_append, List.nil_append]
  refine List.flatMap_congr fun t ht => ?_
  rw [List.mem_range] at ht
  rw [← out_tagP hρ hHb hRb hSb hH hR hS hs ht ht1 ht2 ht3 ht4 ht5]
  congr 1
  have hg : ∀ (l : List ℕ) (i : ℕ), (ρ ++ l).getD (b + i) 0 = l.getD i 0 :=
    fun l i => getD_stk hρ i
  simp only [stkTP, restXP, List.append_assoc, List.cons_append, List.nil_append, Xp.eval_var,
    Xp.eval_add, Xp.eval_mul, Xp.eval_mulC, Xp.eval_const, hg, hHe, hRe, List.getD_cons_succ,
    List.getD_cons_zero]
  simp only [List.cons.injEq, List.append_cancel_left_eq, and_true, true_and, pack]
  ring

end Kind

lemma map_fst_zipIdxP {α : Type} : ∀ (l : List α) (k : ℕ), (l.zipIdx k).map Prod.fst = l
  | [], _ => rfl
  | a :: l, k => by rw [List.zipIdx_cons, List.map_cons, map_fst_zipIdxP l (k + 1)]

lemma take_stkLP (hρ : ρ.length = b) (j : ℕ) (L : Loc M H) (l : List ℕ) :
    (stkLP M ρ H s j L ++ l).take b = ρ := by
  simp [stkLP, stkTP, ← hρ]

lemma getD_stkLP_code (hρ : ρ.length = b) (j : ℕ) (L : Loc M H) (l : List ℕ) :
    (stkLP M ρ H s j L ++ l).getD (b + 15) 0 = (Loc.code L).val := by
  rw [List.getD_append _ _ _ _ (by rw [length_stkLP hρ]; omega)]
  rw [stkLP, List.getD_append_right _ _ _ _ (by rw [length_stkTP hρ]; omega), length_stkTP hρ]
  simp

lemma getD_stkLP_idx (hρ : ρ.length = b) (j : ℕ) (L : Loc M H) (k : ℕ) (r : List ℕ) :
    (stkLP M ρ H s j L ++ k :: r).getD (b + 16) 0 = k := by
  rw [List.getD_append_right _ _ _ _ (by rw [length_stkLP hρ]), length_stkLP hρ]
  simp

lemma drop_stkLP (hρ : ρ.length = b) (j : ℕ) (L : Loc M H) (k : ℕ) (r : List ℕ) :
    (stkLP M ρ H s j L ++ k :: r).drop (b + 17) = r := by
  rw [show stkLP M ρ H s j L ++ k :: r = (stkLP M ρ H s j L ++ [k]) ++ r by simp]
  rw [show b + 17 = (stkLP M ρ H s j L ++ [k]).length by simp [length_stkLP hρ]]
  exact List.drop_left

lemma zipIdx_snd_finRange {s : ℕ} :
    ∀ p ∈ ((List.finRange s).filter fun i => decide (i.val ≠ 0)).zipIdx 1, p.2 = p.1.val := by
  set I := (List.finRange s).filter fun i => decide (i.val ≠ 0) with hI
  have hmap : I.map Fin.val = List.range' 1 (s - 1) := by
    rw [hI, ← filter_range_ne_zero, ← map_val_finRange', List.filter_map]
    rfl
  intro p hp
  rw [List.mem_zipIdx_iff_le_and_getElem?_sub] at hp
  obtain ⟨h1, h2⟩ := hp
  have h3 := congrArg (fun l => l[p.2 - 1]?) hmap
  simp only [List.getElem?_map, h2, Option.map_some] at h3
  have hlt : p.2 - 1 < s - 1 := by
    have := congrArg List.length hmap
    simp only [List.length_map, List.length_range'] at this
    have := (List.getElem?_eq_some_iff.mp h2).1
    omega
  rw [List.getElem?_range' hlt] at h3
  simp only [Option.some.injEq] at h3
  omega

/-- **The stacks of a location belong to its moves.** -/
theorem stksP_spec (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
    (hR : RX.eval ρ = radix M H) (ℓ : ℕ) (L : Loc M H) :
    List.Forall₂ (fun (p : Move (Loc M H) s × ℕ) τ => τ.length = b + 25 ∧ τ.take b = ρ ∧
        τ.getD (b + 15) 0 = (Loc.code L).val ∧ τ.getD (b + 16) 0 = p.2 ∧
        CmdDesc M x s ℓ H (Move.toACmd ℓ L p.1) (τ.drop (b + 17)))
      ((moves M x s ℓ H L).zipIdx) (stksP M b HX RX ρ s H L) := by
  set σ := stkLP M ρ H s 0 L with hσ
  have hσ' : σ = stkTP ρ H (radix M H) (cM M) L.tuple ++ [s, 0, (Loc.code L).val] := rfl
  have hV : (rvP b HX).Ok H σ L.tuple.2.1 L.tuple.2.2.2.2.1 := by
    rw [hσ']; exact rvP_ok hρ hH hHb _ _ _ _
  obtain ⟨-, hval, hloc⟩ := L.kind_spec
  have hmv := moves_eq (s := s) (x := x) (ℓ := ℓ) hV L.kind hval
  rw [hloc] at hmv
  have evj : ∀ j, ∀ {e : Xp}, e.Bnd b → e.eval (stkLP M ρ H s j L) = e.eval ρ := fun j e he => by
    simp only [stkLP, stkTP, List.append_assoc]; exact Xp.eval_append hρ _ he
  have hRσ : ∀ j, RX.eval (stkLP M ρ H s j L) = radix M H := fun j => (evj j hRb).trans hR
  have hHσ : ∀ j, HX.eval (stkLP M ρ H s j L) = H := fun j => (evj j hHb).trans hH
  rw [← hmv, selBr_brs, List.map_append, List.zipIdx_append, stksP]
  refine List.rel_append ?_ ?_
  · rw [List.map_map, List.zipIdx_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun p _ => ?_
    have hd := SMv.desc (x := x) (ℓ := ℓ) (hRσ 0) (hHσ 0) L (p.1.lift (s := s))
    rw [SMv.recX_lift] at hd
    refine ⟨?_, take_stkLP hρ 0 L _, getD_stkLP_code hρ 0 L _, getD_stkLP_idx hρ 0 L _ _, ?_⟩
    · have := CmdDesc.length hd
      simp only [List.length_map] at this
      simp [length_stkLP hρ, this]
    · rw [drop_stkLP hρ]; exact hd
  · have hd0 : (rvP b HX).d.eval σ = L.tuple.2.1 := hV.d
    rw [hd0]
    by_cases hc : L.kind.missFam = true ∧ L.tuple.2.1 = 0
    · rw [if_pos hc, if_pos hc]
      have hlen := length_selBr_brs0 σ (rvP b HX) L.kind hc.1 (by rw [hd0]; exact hc.2)
      set I := (List.finRange s).filter fun i => decide (i.val ≠ 0) with hI
      have hrange : (List.range s).filter (fun i => decide (i ≠ 0)) = I.map Fin.val := by
        rw [hI, ← map_val_finRange', List.filter_map]; rfl
      simp only [List.length_map, hlen, zero_add, missL, List.map_map, List.zipIdx_map, ← hI]
      rw [hrange, List.map_map]
      conv_rhs => rw [← map_fst_zipIdxP I 1, List.map_map]
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine List.forall₂_same.mpr fun p hp => ?_
      have hpi := zipIdx_snd_finRange p hp
      simp only [Function.comp, Prod.map_fst, Prod.map_snd, id]
      have hd := SMv.desc (x := x) (ℓ := ℓ) (hRσ p.1.val) (hHσ p.1.val) L
        (SMv.miss p.1 .accept)
      have hrec : ((SMv.miss p.1 .accept : SMv M s).recX RX HX).map
          (fun e => e.eval (stkLP M ρ H s p.1.val L)) =
          [0, 0, (Loc.code (Loc.accept : Loc M H)).val, 0, 2, p.1.val, 0, 0] := by
        simp [SMv.recX, SLoc.eval_codeX (hRσ _) (hHσ _), SLoc.eval]
      rw [hrec] at hd
      refine ⟨by simp [length_stkLP hρ], take_stkLP hρ _ L _, getD_stkLP_code hρ _ L _, ?_, ?_⟩
      · rw [getD_stkLP_idx hρ, hpi]
      · rw [drop_stkLP hρ]; exact hd
    · rw [if_neg hc, if_neg hc]
      exact List.Forall₂.nil

end Out

end Lax119563Proofs.Reduction
