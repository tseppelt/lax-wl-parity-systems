import Lax119563.ImplicitSystemEncodings
import Lax119563.MatrixCompiler
import Lax119563Proofs.Programs.Part1
import Lax119563Proofs.Reduction.Part2

/-! ### Formerly `Lax119563Proofs.Reduction.PkCmd` -/

section Reduction_PkCmd

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

/-- The kinds with tests `miss i` (in the branch `d = 0`): the root cells `(0, false)` of
phase `0`. -/
def SKind.missFam : SKind M → Bool
  | .cell θ _ c => decide (θ.val = 0) && decide (c = (0, false))
  | _ => false

/-- The tests `miss i`, `1 ≤ i < s`. -/
def missL (M : Machine) (s : ℕ) : List (SMv M s) :=
  ((List.finRange s).filter fun i => decide (i.val ≠ 0)).map fun i => SMv.miss i .accept

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

end Reduction_PkCmd

/-! ### Formerly `Lax119563Proofs.Reduction.PkStk` -/

section Reduction_PkStk

/-!
# The stacks of the command enumerator for a runtime number of blocks

For the command enumerator `cmdEnumP`: `cmdStksP` (the stacks of the body, one per command,
in order),
`out_cmdEnumP'`, `cmdStksP_forall₂` (relation `StkCmd`), `keys_cmdStksP` (the keys are
`keyList`) and `length_out_beforeP` (counting the commands before a given one).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp

variable {M : Machine} {s : ℕ}

variable (M) in
/-- The stacks on which the body of the command enumerator runs, in order. -/
noncomputable def cmdStksP (b : ℕ) (HX RX : Xp) (ρ : List ℕ) (s H : ℕ) : List (List ℕ) :=
  (List.range (numLoc M H)).flatMap fun c =>
    match decodeLoc M H c with
    | some L => stksP M b HX RX ρ s H L
    | none => []

lemma forall₂_flipP {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → List.Forall₂ (fun b a => R a b) l' l
  | [], [], List.Forall₂.nil => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t => List.Forall₂.cons h (forall₂_flipP t)

lemma map_eq_of_forall₂P {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ a b, R a b → f a = g b) →
      l₁.map f = l₂.map g
  | [], [], List.Forall₂.nil, _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h t, hf => by
    rw [List.map_cons, List.map_cons, hf _ _ h, map_eq_of_forall₂P t hf]

section Stacks

variable {x y : List Bool} {ρ : List ℕ} {b H : ℕ} {SX HX RX : Xp}

lemma stksP_rel (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
    (hR : RX.eval ρ = radix M H) (ℓ : ℕ) (L : Loc M H) :
    List.Forall₂ (StkCmd x s ℓ H b ρ) (stksP M b HX RX ρ s H L)
      ((moves M x s ℓ H L).map (Move.toACmd ℓ L)) := by
  have h := stksP_spec (x := x) (s := s) hρ hHb hRb hH hR ℓ L
  rw [← map_fst_zipIdxP (moves M x s ℓ H L) 0, List.map_map, List.forall₂_map_right_iff]
  refine (forall₂_flipP h).imp fun {τ p} hp => ?_
  obtain ⟨h1, h2, h3, -, h5⟩ := hp
  exact ⟨h1, h2, by simp only [Function.comp, src_toACmd]; exact h3, h5⟩

lemma stksP_keys (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
    (hR : RX.eval ρ = radix M H) (ℓ : ℕ) (L : Loc M H) :
    (stksP M b HX RX ρ s H L).map (keyAt b) =
      (List.range (moves M x s ℓ H L).length).map ((Loc.code L).val, ·) := by
  have h := stksP_spec (x := x) (s := s) hρ hHb hRb hH hR ℓ L
  rw [List.range_eq_range', ← map_zipIdx_snd (fun k => ((Loc.code L).val, k))
    (moves M x s ℓ H L) 0]
  exact map_eq_of_forall₂P (forall₂_flipP h) fun τ p hp => by
    simp only [keyAt, hp.2.2.1, hp.2.2.2.1]

variable (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hSb : SX.Bnd b)
  (hH : HX.eval ρ = H) (hR : RX.eval ρ = radix M H) (hS : SX.eval ρ = s) (hs : 1 ≤ s)
include hρ hHb hRb hH hR

/-- **The output of the command enumerator, by stacks.** -/
theorem out_cmdEnumP' (body : Gn) (hSb : SX.Bnd b) (hS : SX.eval ρ = s) (hs : 1 ≤ s) :
    (cmdEnumP M b SX HX RX body).out y ρ = (cmdStksP M b HX RX ρ s H).flatMap (body.out y) := by
  rw [out_cmdEnumP hρ hHb hRb hSb hH hR hS hs, cmdStksP, List.flatMap_assoc]
  refine List.flatMap_congr fun c _ => ?_
  cases decodeLoc M H c with
  | none => rfl
  | some L => rfl

/-- **The stacks belong to the commands, in order.** -/
theorem cmdStksP_forall₂ (ℓ : ℕ) :
    List.Forall₂ (StkCmd x s ℓ H b ρ) (cmdStksP M b HX RX ρ s H) (verifierCmds' M x s ℓ H) := by
  rw [verifierCmds'_eq, cmdStksP]
  refine forall₂_flatMap (List.forall₂_same.mpr fun c _ => ?_)
  cases decodeLoc M H c with
  | none => exact List.Forall₂.nil
  | some L => exact stksP_rel hρ hHb hRb hH hR ℓ L

/-- **The keys of the stacks.** -/
theorem keys_cmdStksP (ℓ : ℕ) :
    (cmdStksP M b HX RX ρ s H).map (keyAt b) = keyList M s x ℓ H := by
  rw [cmdStksP, keyList, List.map_flatMap]
  refine List.flatMap_congr fun c _ => ?_
  cases decodeLoc M H c with
  | none => rfl
  | some L => exact stksP_keys hρ hHb hRb hH hR ℓ L

end Stacks

theorem keyList_pairwise' {x : List Bool} {ℓ H : ℕ} :
    (keyList M s x ℓ H).Pairwise (fun p q => lexLt p q = true) :=
  keyList_pairwise (M := M) (s := s) (x := x) (ρ := []) (b := 0) (HX := const H)
    (RX := const (radix M H)) rfl trivial trivial rfl rfl ℓ

variable {x y : List Bool} {b H : ℕ} {SX HX RX : Xp}

/-- **Counting before**: the length of the output of a nested enumerator whose body is
`when (beforeX b b') g` is a sum over the stacks before the outer one. -/
theorem length_out_beforeP {ρ σ : List ℕ} (ℓ : ℕ) (hρ : ρ.length = b) (hHb : HX.Bnd b)
    (hRb : RX.Bnd b) (hSb : SX.Bnd b) (hH : HX.eval ρ = H) (hR : RX.eval ρ = radix M H)
    (hS : SX.eval ρ = s) (hs : 1 ≤ s)
    {b' : ℕ} (hb' : b + 25 ≤ b') (hσ : σ.length = b') (hσρ : σ.take b = ρ)
    {j : ℕ} (hj : j < (cmdStksP M b HX RX ρ s H).length)
    (hστ : σ.take (b + 25) = (cmdStksP M b HX RX ρ s H)[j]) (g : Gn) :
    ((cmdEnumP M b' SX HX RX (Gn.when (beforeX b b') g)).out y σ).length =
      (((cmdStksP M b' HX RX σ s H).take j).map fun τ' => (g.out y τ').length).sum := by
  have hσsplit : σ = ρ ++ σ.drop b := by rw [← hσρ, List.take_append_drop]
  have hHσ : HX.eval σ = H := by rw [hσsplit]; exact (Xp.eval_append hρ _ hHb).trans hH
  have hRσ : RX.eval σ = radix M H := by rw [hσsplit]; exact (Xp.eval_append hρ _ hRb).trans hR
  have hSσ : SX.eval σ = s := by rw [hσsplit]; exact (Xp.eval_append hρ _ hSb).trans hS
  have hHσb : HX.Bnd b' := Xp.Bnd.mono (by omega) hHb
  have hRσb : RX.Bnd b' := Xp.Bnd.mono (by omega) hRb
  have hSσb : SX.Bnd b' := Xp.Bnd.mono (by omega) hSb
  set τ := (cmdStksP M b HX RX ρ s H)[j] with hτ
  have hF := cmdStksP_forall₂ (x := ([] : List Bool)) (s := s) (M := M) hσ hHσb hRσb hHσ hRσ ℓ
  have hkey : ∀ τ' ∈ cmdStksP M b' HX RX σ s H, keyAt b τ' = keyAt b τ := by
    intro τ' hτ'
    obtain ⟨cmd, -, hrel⟩ := forall₂_exists_of_mem_left hF hτ'
    have h1 : τ'.take b' = σ := hrel.2.1
    have g1 : ∀ i < b + 25, τ'.getD i 0 = τ.getD i 0 := by
      intro i hi
      have hτlen : τ.length = b + 25 := by
        rw [← hστ, List.length_take, hσ]; omega
      rw [← getD_take' (n := b') (by omega), h1, ← getD_take' (n := b + 25) hi, hστ]
    simp only [keyAt, g1 (b + 15) (by omega), g1 (b + 16) (by omega)]
  rw [out_cmdEnumP' hσ hHσb hRσb hHσ hRσ _ hSσb hSσ hs, List.length_flatMap]
  simp only [Gn.out_when, eval_beforeX]
  have : ((cmdStksP M b' HX RX σ s H).map fun τ' =>
      (if (if lexLt (keyAt b' τ') (keyAt b τ') = true then 1 else 0) ≠ 0 then g.out y τ'
        else []).length) =
      (cmdStksP M b' HX RX σ s H).map fun τ' =>
        if lexLt (keyAt b' τ') (keyAt b τ) then (g.out y τ').length else 0 := by
    refine List.map_congr_left fun τ' hτ' => ?_
    rw [hkey τ' hτ']
    by_cases hl : lexLt (keyAt b' τ') (keyAt b τ) <;> simp [hl]
  rw [this, sum_map_ite_filter]
  have hkeys := keys_cmdStksP (x := ([] : List Bool)) (s := s) (M := M) hσ hHσb hRσb hHσ hRσ ℓ
  have hkeys0 := keys_cmdStksP (x := ([] : List Bool)) (s := s) (M := M) hρ hHb hRb hH hR ℓ
  have hlen : (cmdStksP M b' HX RX σ s H).length = (cmdStksP M b HX RX ρ s H).length := by
    rw [← List.length_map (f := keyAt b'), hkeys, ← hkeys0, List.length_map]
  have hj' : j < (cmdStksP M b' HX RX σ s H).length := hlen ▸ hj
  have hkj : keyAt b τ = keyAt b' (cmdStksP M b' HX RX σ s H)[j] := by
    have e1 : keyAt b τ = (keyList M s ([] : List Bool) ℓ H)[j]'(by rw [← hkeys0, List.length_map]; exact hj) := by
      simp only [hτ, ← hkeys0, List.getElem_map]
    have e2 : keyAt b' (cmdStksP M b' HX RX σ s H)[j] =
        (keyList M s ([] : List Bool) ℓ H)[j]'(by rw [← hkeys, List.length_map]; exact hj') := by
      simp only [← hkeys, List.getElem_map]
    rw [e1, e2]
  rw [hkj, filter_lexLt_eq_take (keyAt b') _ (by
    rw [← List.pairwise_map (f := keyAt b') (R := fun p q => lexLt p q = true), hkeys]
    exact keyList_pairwise') j hj']

end Lax119563Proofs.Reduction

end Reduction_PkStk

/-! ### Formerly `Lax119563Proofs.Reduction.SchGen` -/

section Reduction_SchGen

/-!
# Blocks of the schema enumerator

The schema records and their generators: for a schema of the compiled code-ordered time
program, `SchRec` describes the record `[tern, u, v, en, msk, gk, g1, g2, g3]` (the numbers of
the schema in the sense of `SchMatch`, and its domain `guardDomain (toGuard g) true` for the
guard `g` described by `gk, g1, g2, g3`; `GDescQ`: `GDesc`, or the query guard `v = 0` for
`gk = 3`). `blkGen` emits the records of the schemas of a command (`out_blkGen`), built from
`slotX`, `assignBlk`, `forkBlk`, `gdX` and the determinism test `detGen`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

variable {M : Machine} {s : ℕ}

/-! ## Records -/

/-- The five numbers of a schema. -/
def SchNum.toL (n : SchNum) : List ℕ := [n.tern.toNat, n.u, n.v, n.en, n.msk]

/-- Expressions for the numbers of a gadget. -/
def gadgetX (X msk A B Z Y : Xp) : List (List Xp) :=
  [[const 0, X, A, A, msk], [const 0, X, B, B, msk], [const 1, A, B, Z, const 0],
    [const 0, Z, Y, Y, const 0]]

lemma eval_gadgetX (ρ : List ℕ) (X msk A B Z Y : Xp) :
    (gadgetX X msk A B Z Y).map (·.map (·.eval ρ)) =
      (gadgetN (X.eval ρ) (msk.eval ρ) (A.eval ρ) (B.eval ρ) (Z.eval ρ) (Y.eval ρ)).map
        SchNum.toL := by
  simp [gadgetX, gadgetN, binN, terN, SchNum.toL]

/-- Guard descriptions, including the query guard `v = 0` (kind `3`). -/
def GDescQ (M : Machine) (x : List Bool) (s ℓ H : ℕ) (g : Fin s → ℕ → Bool) (gd : List ℕ) :
    Prop :=
  GDesc M x s ℓ H g gd ∨ (gd.getD 0 0 = 3 ∧ g = fun _ v => decide (v = 0))

/-- The record `rec = [tern, u, v, en, msk, gk, g1, g2, g3]` describes the schema `sc`. -/
def SchRec (M : Machine) (x : List Bool) (s ℓ H : ℕ) {N : ℕ} (sc : Schema (s + 1) ℓ N)
    (rec : List ℕ) : Prop :=
  ∃ g, GDescQ M x s ℓ H g (rec.drop 5) ∧
    SchMatch (guardDomain (toGuard g) true) sc
      ⟨decide (rec.getD 0 0 = 1), rec.getD 1 0, rec.getD 2 0, rec.getD 3 0, rec.getD 4 0⟩

lemma schRec_of {x : List Bool} {ℓ H N : ℕ} {sc : Schema (s + 1) ℓ N} {n : SchNum}
    {D : Finset (Coord (s + 1) ℓ)} (h : SchMatch D sc n) {g : Fin s → ℕ → Bool} {gd : List ℕ}
    (hD : D = guardDomain (toGuard g) true) (hg : GDescQ M x s ℓ H g gd) :
    SchRec M x s ℓ H sc (n.toL ++ gd) := by
  refine ⟨g, by simpa [SchNum.toL] using hg, ?_⟩
  rw [← hD]
  obtain ⟨t, u, v, en, msk⟩ := n
  have e : (⟨decide ((SchNum.toL ⟨t, u, v, en, msk⟩ ++ gd).getD 0 0 = 1),
      (SchNum.toL ⟨t, u, v, en, msk⟩ ++ gd).getD 1 0, (SchNum.toL ⟨t, u, v, en, msk⟩ ++ gd).getD 2 0,
      (SchNum.toL ⟨t, u, v, en, msk⟩ ++ gd).getD 3 0, (SchNum.toL ⟨t, u, v, en, msk⟩ ++ gd).getD 4 0⟩ :
      SchNum) = ⟨t, u, v, en, msk⟩ := by
    cases t <;> simp [SchNum.toL]
  rw [e]; exact h

/-! ## Generators -/

namespace Gn

variable {x : List Bool} {ρ : List ℕ}

/-- Run `body` for each schema of a block, pushing its index `e0 + i`, its five numbers and
the guard numbers `gd`. -/
def blkGen (e0 : Xp) (gd : List Xp) (body : Gn) (blk : List (List Xp)) : Gn :=
  seqL (blk.zipIdx.map fun p => bindL (add e0 (const p.2) :: (p.1 ++ gd)) body)

/-- `n` emissions. -/
def emitN (n : ℕ) : Gn := seqL (List.replicate n (emit (const 0)))

lemma length_out_emitN (n : ℕ) : ((emitN n).out x ρ).length = n := by
  rw [emitN, out_seqL]
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, out, ih] <;> omega

lemma out_blkGen {n : ℕ} (hρ : ρ.length = n) (e0 : Xp) (gd : List Xp) (body : Gn)
    (blk : List (List Xp)) (he : e0.Bnd n) (hgd : ∀ e ∈ gd, e.Bnd n)
    (hblk : ∀ l ∈ blk, ∀ e ∈ l, e.Bnd n) :
    (blkGen e0 gd body blk).out x ρ = (blk.zipIdx.map fun p =>
      ρ ++ (e0.eval ρ + p.2) :: (p.1.map (·.eval ρ) ++ gd.map (·.eval ρ))).flatMap (body.out x) := by
  rw [blkGen, out_seqL, List.flatMap_map, List.flatMap_map]
  refine List.flatMap_congr fun p hp => ?_
  have hm : p.1 ∈ blk := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
  rw [out_bindL body _ hρ]
  · simp
  · intro e he'
    simp only [List.mem_cons, List.mem_append] at he'
    rcases he' with rfl | he' | he'
    · exact ⟨he, trivial⟩
    · exact hblk _ hm e he'
    · exact hgd e he'

end Gn

section Gens

variable (M s)

/-- The location number `N + t + 8 j` of slot `t` of command `j` (`j` at level `b + 25`). -/
def slotX (NX : Xp) (b t : ℕ) : Xp := add NX (add (const t) (mulC 8 (var (b + 25))))

/-- The numbers of the schemas of an assignment (record at levels `b + 17 …`). -/
def assignBlk (NX : Xp) (b : ℕ) : List (List Xp) :=
  gadgetX (var (b + 19)) (var (b + 18)) (slotX NX b 0) (slotX NX b 1) (slotX NX b 2) (var (b + 15))

/-- The numbers of the schemas of a fork. -/
def forkBlk (NX : Xp) (b : ℕ) : List (List Xp) :=
  gadgetX (var (b + 19)) (const 0) (slotX NX b 0) (slotX NX b 1) (slotX NX b 2) (slotX NX b 6) ++
  gadgetX (var (b + 20)) (const 0) (slotX NX b 3) (slotX NX b 4) (slotX NX b 5) (slotX NX b 7) ++
  [[const 1, slotX NX b 6, slotX NX b 7, var (b + 15), const 0]]

/-- The guard numbers of a command. -/
def gdX (b : ℕ) : List Xp := [var (b + 21), var (b + 22), var (b + 23), var (b + 24)]

/-- The location number `N + 8 r + t` of detector slot `t`. -/
def detX (NX rX : Xp) (t : ℕ) : Xp := add (add NX (mulC 8 rX)) (const t)

/-- The detector schemas (padded to the same depth). -/
def detGen (NX rX p0X EcX : Xp) (body : Gn) : Gn :=
  Gn.bindL (List.replicate 27 (const 0))
    (Gn.blkGen EcX [const 3, const 0, const 0, const 0] body
      (gadgetX p0X (const 0) (detX NX rX 0) (detX NX rX 1) (detX NX rX 2) (detX NX rX 3)))

end Gens

end Lax119563Proofs.Reduction

end Reduction_SchGen

/-! ### Formerly `Lax119563Proofs.Reduction.CostSch` -/

section Reduction_CostSch

/-!
# Fits and cost of the schema generators

Classes `numTys` of the record `[tern, u, v, en, msk]` of a schema and `gdTys` of the guard
numbers; the cost of the block generator (`hasCost_blkGen`) and of emitting numbers
(`hasCost_emitN`), and the class of the key comparison `beforeX` (`hasTy_beforeX`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Xp Ty Gn

variable {M : Machine} {s : ℕ}

/-- The classes of the five numbers of a schema. -/
def numTys : List Ty := [P 0 0, P 0 7, P 0 7, P 0 7, .big]

/-- The classes of the guard numbers. -/
def gdTys : List Ty := [P 0 0, P 0 1, P 0 0, P 0 0]

variable {Γ : List Ty}

/-- Typed lists of expressions. -/
abbrev TyBs (Γ : List Ty) (l : List Xp) (ts : List Ty) : Prop :=
  List.Forall₂ (fun a τ => TyB Γ a τ) l ts

lemma hasCost_blkGen {e0 : Xp} {gd : List Xp} {body : Gn} {blk : List (List Xp)} {e d : ℕ}
    (he0 : TyB Γ e0 (P 0 7)) (hgd : TyBs Γ gd gdTys) (hblk : ∀ l ∈ blk, TyBs Γ l numTys)
    (hbody : HasCost (Γ ++ P 0 7 :: (numTys ++ gdTys)) body e d) :
    HasCost Γ (blkGen e0 gd body blk) e d := by
  refine hasCost_seqL fun g hg => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  have hm : p.1 ∈ blk := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
  have h0 : TyB Γ (add e0 (const p.2)) (P 0 7) :=
    ⟨hasTy_add he0.1 ((hasTy_const _).le ⟨le_rfl, by omega⟩), he0.2, trivial⟩
  have hT : TyL (Γ ++ []) (add e0 (const p.2) :: (p.1 ++ gd)) (P 0 7 :: (numTys ++ gdTys)) :=
    tyL_of_forall₂ (.cons h0 (List.rel_append (hblk _ hm) hgd)) []
  exact hasCost_bindL (by simpa using hT) hbody

lemma gadgetX_ty {X msk A B Z Y : Xp} (hX : TyB Γ X (P 0 7)) (hm : TyB Γ msk .big)
    (hA : TyB Γ A (P 0 7)) (hB : TyB Γ B (P 0 7)) (hZ : TyB Γ Z (P 0 7))
    (hY : TyB Γ Y (P 0 7)) : ∀ l ∈ gadgetX X msk A B Z Y, TyBs Γ l numTys := by
  have c0 : TyB Γ (const 0) (P 0 0) := tyB_const 0
  have c1 : TyB Γ (const 1) (P 0 0) := tyB_const 1
  have cb : TyB Γ (const 0) .big := c0.le (Ty.le_big _)
  simp only [gadgetX, List.mem_cons, List.not_mem_nil, or_false]
  rintro l (rfl | rfl | rfl | rfl)
  · exact .cons c0 (.cons hX (.cons hA (.cons hA (.cons hm .nil))))
  · exact .cons c0 (.cons hX (.cons hB (.cons hB (.cons hm .nil))))
  · exact .cons c1 (.cons hA (.cons hB (.cons hZ (.cons cb .nil))))
  · exact .cons c0 (.cons hZ (.cons hY (.cons hY (.cons cb .nil))))

lemma tyL_zeros : ∀ (k : ℕ) (Γ : List Ty),
    TyL Γ (List.replicate k (const 0)) (List.replicate k (P 0 0))
  | 0, _ => trivial
  | k + 1, Γ => ⟨hasTy_const 0, tyL_zeros k _⟩

lemma tyB_get {τs l : List Ty} {j : ℕ} {τ τ' : Ty} (h : l.getD j (P 0 0) = τ) (hj : j < l.length)
    (hle : Ty.Le τ τ') : TyB (τs ++ l) (var (τs.length + j)) τ' := (tyB_var l h hj).le hle

lemma hasTy_beforeX (b b' : ℕ) : HasTy Γ (beforeX b b') (P 0 0) :=
  hasTy_or (hasTy_lt (hasTy_var _) (hasTy_var _))
    (hasTy_and (hasTy_eq (hasTy_var _) (hasTy_var _)) (hasTy_lt (hasTy_var _) (hasTy_var _)))

lemma hasCost_emitN (n : ℕ) : HasCost Γ (emitN n) 0 0 :=
  hasCost_seqL fun g hg => by
    rw [List.eq_of_mem_replicate hg]; exact hasCost_emit (hasTy_const 0)

end Lax119563Proofs.Reduction

end Reduction_CostSch

/-! ### Formerly `Lax119563Proofs.Reduction.GuardEval` -/

section Reduction_GuardEval

/-!
# Numeric evaluation of guards

`gEval x ℓ H gd i v`: the value of the guard described by the numbers `gd` (`GDescQ`) on
block `i < s` with register value `v`, in terms of numbers only (`gEval_spec`). The hit guard
reads the input through `initCV x ν v`, the number `encCV` of cell `v` of tape `ν` in the
initial configuration (`encCV_init`), which only needs `inBit x v`.

`mem_domain_of_schRec`: the domain of a schema with record `rec` is
`{(i, b) | i = s ∨ gEval x ℓ H (rec.drop 5) i (regVal b)}`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

variable {M : Machine} {s : ℕ}

/-- The field guard on a natural block number. -/
def fieldOK (ℓ k m q i v : ℕ) : Bool :=
  decide (∀ t < m, (k + t) / ℓ = i → v.testBit ((k + t) % ℓ) = q.testBit t)

/-- The number of cell `v` of tape `ν` in the initial configuration on input `x`. -/
def initCV (x : List Bool) (ν v : ℕ) : ℕ :=
  (if v = 0 then 1 else 0) + 2 * (if ν = 0 then inBit x v else 0)

lemma encCV_init (x : List Bool) (ν : Tape M) (v : ℕ) :
    encCV (cfgCell (init M x) ν (v : ℤ)) = initCV x ν.val v := by
  unfold encCV cfgCell initCV pack
  have hh : decide ((init M x).head ν = (v : ℤ)) = decide (v = 0) := by
    show decide ((0 : ℤ) = (v : ℤ)) = decide (v = 0)
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  rw [hh]
  congr 1
  · by_cases hv : v = 0 <;> simp [hv]
  · congr 1
    by_cases hν : ν.val = 0
    · have hν' : ν = 0 := Fin.ext hν
      rw [if_pos hν]
      simp only [init, hν', true_and, Int.natCast_nonneg, if_true, Int.toNat_natCast]
      unfold inBit
      rcases Nat.lt_or_ge v x.length with hv | hv
      · rw [List.getElem?_eq_getElem hv, List.drop_eq_getElem_cons hv]
        cases x[v] <;> simp [rdVal]
      · rw [List.getElem?_eq_none hv, List.drop_eq_nil_of_le hv]
        simp [rdVal]
    · have hν' : ν ≠ 0 := fun h => hν (by rw [h]; rfl)
      rw [if_neg hν]
      simp [init, hν']

/-- The numeric guard. -/
def gEval (x : List Bool) (ℓ H : ℕ) (gd : List ℕ) (i v : ℕ) : Bool :=
  match gd.getD 0 0 with
  | 0 => fieldOK ℓ (gd.getD 1 0) (gd.getD 2 0) (gd.getD 3 0) i v
  | 1 => if i = 0 then decide (initCV x (gd.getD 1 0) v = gd.getD 2 0)
      else decide (v = field (2 ^ H) (i * ℓ) ℓ)
  | 2 => if i = gd.getD 1 0 then decide (v ≠ field (2 ^ H) (i * ℓ) ℓ) else true
  | _ => decide (v = 0)

lemma gEval_spec {x : List Bool} {ℓ H : ℕ} {g : Fin s → ℕ → Bool} {gd : List ℕ}
    (h : GDescQ M x s ℓ H g gd) (i : Fin s) (v : ℕ) : g i v = gEval x ℓ H gd i.val v := by
  rcases h with (⟨h0, rfl⟩ | ⟨h0, ν, c, h1, h2, rfl⟩ | ⟨h0, i₀, h1, rfl⟩) | ⟨h0, rfl⟩
  · simp only [gEval, h0]; rfl
  · simp only [gEval, h0, hitGuard]
    split_ifs with hi
    · rw [← h1, ← h2, ← encCV_init]
      exact decide_eq_decide.mpr ⟨fun h => by rw [h], fun h => encCV_inj h⟩
    · rfl
  · simp only [gEval, h0, missGuard]
    by_cases hi : i = i₀
    · subst hi; rw [if_pos rfl, if_pos h1]
    · have : i.val ≠ gd.getD 1 0 := fun h => hi (Fin.ext (h.trans h1.symm))
      rw [if_neg hi, if_neg this]
  · simp only [gEval, h0]

/-- **Domains of schemas from their records.** -/
lemma mem_domain_of_schRec {x : List Bool} {ℓ H N : ℕ} {sc : Schema (s + 1) ℓ N}
    {rec : List ℕ} (h : SchRec M x s ℓ H sc rec) (c : Coord (s + 1) ℓ) :
    c ∈ sc.domain ↔ c.1.val = s ∨ gEval x ℓ H (rec.drop 5) c.1.val (regVal c.2) = true := by
  obtain ⟨g, hg, hm⟩ := h
  rw [hm.2.2.2.2.2.2.2, mem_guardDomain_toGuard]
  split_ifs with hc
  · rw [gEval_spec hg]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · omega
      · exact h
  · have : c.1.val = s := by have := c.1.isLt; omega
    simp [this]

end Lax119563Proofs.Reduction

end Reduction_GuardEval

/-! ### Formerly `Lax119563Proofs.Reduction.SchOut` -/

section Reduction_SchOut

/-!
# The stacks of the schemas

The stacks on which the body of the schema enumerator runs, per command (`cmdSchStks`,
`detStks`, with the index `e0Of` of the first schema of a command), bounds on the expressions
of the schema blocks (`bnd_gadgetX`, `bnd_slotX`, …) and the output of the determinism test
(`out_detGen`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

variable {M : Machine} {s : ℕ}

/-! ## List lemmas -/

lemma getD_drop' (τ : List ℕ) (k i : ℕ) : (τ.drop k).getD i 0 = τ.getD (k + i) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {f' : β → γ}
    (hf : ∀ a b, R a b → f a = f' b) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → l.map f = l'.map f'
  | [], [], List.Forall₂.nil => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h t => by
    rw [List.map_cons, List.map_cons, hf _ _ h, forall₂_map_eq hf t]

lemma forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      List.Forall₂ (fun a b => R a b ∧ b ∈ l') l l'
  | [], [], List.Forall₂.nil => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t =>
    List.Forall₂.cons ⟨h, List.mem_cons_self⟩
      ((forall₂_mem_right t).imp fun {_ _} h' => ⟨h'.1, List.mem_cons_of_mem _ h'.2⟩)

lemma forall₂_zipIdx_both {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ k,
      List.Forall₂ (fun p q => R p.1 q.1 ∧ p.2 = q.2) (l.zipIdx k) (l'.zipIdx k)
  | [], [], List.Forall₂.nil, _ => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t, k => by
    rw [List.zipIdx_cons, List.zipIdx_cons]
    exact List.Forall₂.cons ⟨h, rfl⟩ (forall₂_zipIdx_both t (k + 1))

lemma forall₂_self_zipIdx {α : Type} {R : α → (α × ℕ) → Prop} (h : ∀ a i, R a (a, i)) :
    ∀ (l : List α) (k : ℕ), List.Forall₂ R l (l.zipIdx k)
  | [], _ => List.Forall₂.nil
  | a :: l, k => by
    rw [List.zipIdx_cons]
    exact List.Forall₂.cons (h a k) (forall₂_self_zipIdx h l (k + 1))

lemma forall₂_comp {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop} :
    ∀ {a : List α} {b : List β} {c : List γ}, List.Forall₂ R a b → List.Forall₂ S b c →
      List.Forall₂ (fun x z => ∃ y, R x y ∧ S y z) a c
  | [], [], [], List.Forall₂.nil, List.Forall₂.nil => List.Forall₂.nil
  | _ :: _, _ :: _, _ :: _, List.Forall₂.cons h t, List.Forall₂.cons h' t' =>
    List.Forall₂.cons ⟨_, h, h'⟩ (forall₂_comp t t')

lemma flatMap_blocks' : ∀ (lens : List ℕ) (o k : ℕ),
    ((lens.zipIdx k).flatMap fun p => (List.range p.1).map fun i =>
      o + (lens.take (p.2 - k)).sum + i) = (List.range lens.sum).map (o + ·)
  | [], _, _ => rfl
  | a :: l, o, k => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.sum_cons, List.range_add, List.map_append,
      List.map_map]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · refine List.map_congr_left fun i _ => ?_
      simp
    · rw [List.flatMap_congr (fun p hp => List.map_congr_left (fun i _ =>
        (show o + ((a :: l).take (p.2 - k)).sum + i = o + a + (l.take (p.2 - (k + 1))).sum + i by
          have := List.le_snd_of_mem_zipIdx hp
          rw [show p.2 - k = p.2 - (k + 1) + 1 by omega, List.take_succ_cons, List.sum_cons]
          omega)))]
      rw [flatMap_blocks' l (o + a) (k + 1)]
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp]
      omega

/-- Consecutive blocks of indices. -/
lemma flatMap_blocks (lens : List ℕ) (o : ℕ) :
    (lens.zipIdx.flatMap fun p => (List.range p.1).map fun i => o + (lens.take p.2).sum + i) =
      (List.range lens.sum).map (o + ·) := by
  simpa using flatMap_blocks' lens o 0

lemma map_fst_zipIdx' {α : Type} : ∀ (l : List α) (k : ℕ), (l.zipIdx k).map Prod.fst = l
  | [], _ => rfl
  | a :: l, k => by rw [List.zipIdx_cons, List.map_cons, map_fst_zipIdx' l (k + 1)]

lemma eq_of_length_four {l : List ℕ} (h : l.length = 4) :
    l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0] := by
  match l, h with
  | [a, b, c, d], _ => rfl

/-! ## Sizes -/

/-- The number of schemas of a command. -/
def cmdSz {L : Type} : ACmd L s → ℕ
  | .assign .. => 4
  | .fork .. => 9

/-- The number of schemas of the command on the stack `τ` (at base `b`). -/
def szAt (b : ℕ) (τ : List ℕ) : ℕ := if τ.getD (b + 17) 0 ≠ 0 then 9 else 4

lemma szAt_of_stkCmd {x : List Bool} {ℓ H b : ℕ} {ρ τ : List ℕ} {cmd : ACmd (Loc M H) s}
    (h : StkCmd x s ℓ H b ρ τ cmd) : szAt b τ = cmdSz cmd := by
  obtain ⟨-, -, -, hd⟩ := h
  have e : τ.getD (b + 17) 0 = (τ.drop (b + 17)).getD 0 0 := by rw [getD_drop']
  cases cmd with
  | assign => simp only [szAt, cmdSz]; rw [e, hd.2.1] <;> simp
  | fork => simp only [szAt, cmdSz]; rw [e, hd.2.1] <;> simp

/-! ## Stacks -/

/-- The stacks of the schemas of the command on the stack `τ`, with index `j` and first
schema index `e0`. -/
def cmdSchStks (NX : Xp) (b : ℕ) (τ : List ℕ) (j e0 : ℕ) : List (List ℕ) :=
  ((if τ.getD (b + 17) 0 ≠ 0 then forkBlk NX b else assignBlk NX b).zipIdx.map fun p =>
    (τ ++ [j, e0]) ++ (e0 + p.2) :: (p.1.map (·.eval (τ ++ [j, e0])) ++
      (gdX b).map (·.eval (τ ++ [j, e0]))))

/-- The stacks of the detector schemas. -/
def detStks (NX rX p0X EcX : Xp) (ρ : List ℕ) : List (List ℕ) :=
  ((gadgetX p0X (const 0) (detX NX rX 0) (detX NX rX 1) (detX NX rX 2) (detX NX rX 3)).zipIdx.map
    fun p => (ρ ++ List.replicate 27 0) ++ (EcX.eval ρ + p.2) ::
      (p.1.map (·.eval ρ) ++ [3, 0, 0, 0]))

/-- The first schema index of command `j`. -/
noncomputable def e0Of (x : List Bool) (ℓ H j : ℕ) : ℕ :=
  (((verifierCmds' M x s ℓ H).take j).map cmdSz).sum

variable (M s) in
/-! ## Bounds -/

lemma bnd_var {i n : ℕ} (h : i < n) : (var i).Bnd n := h

lemma bnd_gadgetX {n : ℕ} {X msk A B Z Y : Xp} (h1 : X.Bnd n) (h2 : msk.Bnd n) (h3 : A.Bnd n)
    (h4 : B.Bnd n) (h5 : Z.Bnd n) (h6 : Y.Bnd n) :
    ∀ l ∈ gadgetX X msk A B Z Y, ∀ e ∈ l, e.Bnd n := by
  simp only [gadgetX, List.mem_cons, List.not_mem_nil, or_false]
  rintro l (rfl | rfl | rfl | rfl) e he <;> simp only [List.mem_cons, List.not_mem_nil,
    or_false] at he <;> rcases he with rfl | rfl | rfl | rfl | rfl <;> first | trivial | assumption

lemma bnd_slotX {NX : Xp} {b n : ℕ} (hN : NX.Bnd b) (hn : b + 26 ≤ n) (t : ℕ) :
    (slotX NX b t).Bnd n :=
  ⟨Xp.Bnd.mono (by omega) hN, trivial, Xp.bnd_mulC (bnd_var (show b + 25 < n by omega)) 8⟩

lemma bnd_assignBlk {NX : Xp} {b n : ℕ} (hN : NX.Bnd b) (hn : b + 26 ≤ n) :
    ∀ l ∈ assignBlk NX b, ∀ e ∈ l, e.Bnd n :=
  bnd_gadgetX (bnd_var (show b + 19 < n by omega)) (bnd_var (show b + 18 < n by omega)) (bnd_slotX hN hn 0)
    (bnd_slotX hN hn 1) (bnd_slotX hN hn 2) (bnd_var (show b + 15 < n by omega))

lemma bnd_forkBlk {NX : Xp} {b n : ℕ} (hN : NX.Bnd b) (hn : b + 26 ≤ n) :
    ∀ l ∈ forkBlk NX b, ∀ e ∈ l, e.Bnd n := by
  intro l hl
  simp only [forkBlk, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with (hl | hl) | rfl
  · exact bnd_gadgetX (bnd_var (show b + 19 < n by omega)) (show (const 0).Bnd n from trivial) (bnd_slotX hN hn 0)
      (bnd_slotX hN hn 1) (bnd_slotX hN hn 2) (bnd_slotX hN hn 6) l hl
  · exact bnd_gadgetX (bnd_var (show b + 20 < n by omega)) (show (const 0).Bnd n from trivial) (bnd_slotX hN hn 3)
      (bnd_slotX hN hn 4) (bnd_slotX hN hn 5) (bnd_slotX hN hn 7) l hl
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact bnd_slotX hN hn 6
    · exact bnd_slotX hN hn 7
    · show b + 15 < n; omega
    · trivial

lemma bnd_gdX {b n : ℕ} (hn : b + 25 ≤ n) : ∀ e ∈ gdX b, e.Bnd n := by
  simp only [gdX, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl) <;> show _ < n <;> omega

/-! ## Outputs -/

section Out

variable {x : List Bool} {ρ : List ℕ} {b H ℓ : ℕ} {HX RX NX rX p0X EcX : Xp}
  (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
  (hR : RX.eval ρ = radix M H)
include hρ hHb hRb hH hR

omit hHb hRb hH hR in
lemma out_detGen (hNb : NX.Bnd b) (hrb : rX.Bnd b) (hpb : p0X.Bnd b) (hEb : EcX.Bnd b)
    (body : Gn) : (detGen NX rX p0X EcX body).out x ρ =
      (detStks NX rX p0X EcX ρ).flatMap (body.out x) := by
  have hz : ∀ e ∈ List.replicate 27 (const 0), e.Bnd b := fun e he => by
    rw [List.eq_of_mem_replicate he]; trivial
  rw [detGen, Gn.out_bindL _ _ hρ hz]
  have hl : (ρ ++ (List.replicate 27 (const 0)).map fun e => e.eval ρ).length = b + 27 := by
    simp [hρ]
  have hdX : ∀ t, (detX NX rX t).Bnd (b + 27) := fun t =>
    ⟨⟨Xp.Bnd.mono (by omega) hNb, Xp.bnd_mulC (Xp.Bnd.mono (by omega) hrb) 8⟩, trivial⟩
  rw [Gn.out_blkGen hl _ _ _ _ (Xp.Bnd.mono (by omega) hEb) (by
      intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> trivial)
    (bnd_gadgetX (Xp.Bnd.mono (by omega) hpb) (show (const 0).Bnd (b + 27) from trivial) (hdX 0) (hdX 1) (hdX 2) (hdX 3))]
  have hrep : (List.replicate 27 (const 0)).map (fun e => e.eval ρ) = List.replicate 27 0 := by
    simp
  have hev : ∀ e : Xp, e.Bnd b → e.eval (ρ ++ List.replicate 27 0) = e.eval ρ :=
    fun e he => Xp.eval_append hρ _ he
  rw [hrep, detStks]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have hm : p.1 ∈ gadgetX p0X (const 0) (detX NX rX 0) (detX NX rX 1) (detX NX rX 2)
      (detX NX rX 3) := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
  have hb := bnd_gadgetX (n := b) hpb (show (const 0).Bnd b from trivial)
    (show (detX NX rX 0).Bnd b from ⟨⟨hNb, Xp.bnd_mulC hrb 8⟩, trivial⟩)
    (show (detX NX rX 1).Bnd b from ⟨⟨hNb, Xp.bnd_mulC hrb 8⟩, trivial⟩)
    (show (detX NX rX 2).Bnd b from ⟨⟨hNb, Xp.bnd_mulC hrb 8⟩, trivial⟩)
    (show (detX NX rX 3).Bnd b from ⟨⟨hNb, Xp.bnd_mulC hrb 8⟩, trivial⟩) _ hm
  simp only [hev EcX hEb, List.map_cons, List.map_nil, Xp.eval_const]
  congr 3
  exact List.map_congr_left fun e he => hev e (hb e he)

end Out

end Lax119563Proofs.Reduction

end Reduction_SchOut

/-! ### Formerly `Lax119563Proofs.Reduction.SchFinal` -/

section Reduction_SchFinal

/-!
# The schema stacks describe the schemas

`StkSch`: a stack of the schema enumerator has length `b + 37`, extends the globals `ρ`, has its
index at level `b + 27` and a record describing the schema (`SchRec`) from level `b + 28` on;
`stkSch_of`, `forall₂_stks`: the stacks of the commands correspond to the schemas of the
compiled code-ordered time program, in order.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

variable {M : Machine} {s : ℕ}

lemma forall₂_flip' {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → List.Forall₂ (fun b a => R a b) l' l
  | [], [], List.Forall₂.nil => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t => List.Forall₂.cons h (forall₂_flip' t)

lemma src_ne_of_mem {x : List Bool} {ℓ H : ℕ} {cmd : ACmd (Loc M H) s}
    (h : cmd ∈ verifierCmds' M x s ℓ H) : cmd.src ≠ Loc.accept ∧ cmd.src ≠ Loc.reject := by
  unfold verifierCmds' progCmds at h
  obtain ⟨L, -, hL⟩ := List.mem_flatMap.mp h
  obtain ⟨mv, hmv, rfl⟩ := List.mem_map.mp hL
  rw [src_toACmd]
  constructor <;> rintro rfl <;> simp [moves] at hmv

lemma regVal_zero (ℓ : ℕ) : regVal (0 : BlockCoord ℓ) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp [regVal, testBit_ofBits]

lemma queryGuard_zero (s ℓ : ℕ) :
    RegisterProgram.queryGuard (fun _ _ => 0 : Fin s → Fin ℓ → ZMod 2) =
      toGuard (fun _ v => decide (v = 0)) := by
  unfold RegisterProgram.queryGuard toGuard
  congr 1
  funext i
  ext b
  simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq]
  constructor
  · rintro rfl; exact regVal_zero ℓ
  · intro h
    apply regVal_injective
    rw [h]
    exact (regVal_zero ℓ).symm

section Final

variable {x : List Bool} {ρ : List ℕ} {b H ℓ : ℕ} {HX RX NX rX p0X EcX : Xp}

/-- The relation between a schema description `(domain, numbers)` and a stack. -/
def StkSch (M : Machine) (x : List Bool) (s ℓ H b : ℕ) (ρ : List ℕ)
    (Dn : Finset (Coord (s + 1) ℓ) × SchNum) (τ : List ℕ) : Prop :=
  τ.length = b + 37 ∧ τ.take b = ρ ∧ ∃ g gd, GDescQ M x s ℓ H g gd ∧
    Dn.1 = guardDomain (toGuard g) true ∧ τ.drop (b + 28) = Dn.2.toL ++ gd

lemma stkSch_of {σ : List ℕ} (hσ : σ.length = b + 27) (hσρ : σ.take b = ρ)
    {D : Finset (Coord (s + 1) ℓ)} {g : Fin s → ℕ → Bool} {gd : List ℕ}
    (hg : GDescQ M x s ℓ H g gd) (hD : D = guardDomain (toGuard g) true) (hgd : gd.length = 4)
    (n : SchNum) (e : ℕ) :
    StkSch M x s ℓ H b ρ (D, n) (σ ++ e :: (n.toL ++ gd)) := by
  refine ⟨by simp [hσ, hgd, SchNum.toL] <;> omega,
    by rw [List.take_append_of_le_length (by omega), hσρ], g, gd, hg, hD, ?_⟩
  rw [show σ ++ e :: (n.toL ++ gd) = (σ ++ [e]) ++ (n.toL ++ gd) by simp]
  rw [show b + 28 = (σ ++ [e]).length by simp [hσ]]
  exact List.drop_left

lemma forall₂_stks {σ σ' : List ℕ} (hσ : σ.length = b + 27) (hσρ : σ.take b = ρ)
    {D : Finset (Coord (s + 1) ℓ)} {g : Fin s → ℕ → Bool} {gd : List ℕ}
    (hg : GDescQ M x s ℓ H g gd) (hD : D = guardDomain (toGuard g) true) (hgd : gd.length = 4)
    (blk : List (List Xp)) (ns : List SchNum)
    (hns : blk.map (·.map (·.eval σ')) = ns.map SchNum.toL) (e0 : ℕ) :
    List.Forall₂ (StkSch M x s ℓ H b ρ) (ns.map (D, ·))
      (blk.zipIdx.map fun p => σ ++ (e0 + p.2) :: (p.1.map (·.eval σ') ++ gd)) := by
  have h1 : blk.zipIdx.map (fun p => σ ++ (e0 + p.2) :: (p.1.map (·.eval σ') ++ gd)) =
      (blk.map (·.map (·.eval σ'))).zipIdx.map fun p => σ ++ (e0 + p.2) :: (p.1 ++ gd) := by
    rw [List.zipIdx_map, List.map_map]; rfl
  rw [h1, hns, List.zipIdx_map, List.map_map, List.forall₂_map_left_iff,
    List.forall₂_map_right_iff]
  exact forall₂_self_zipIdx (fun n i => stkSch_of hσ hσρ hg hD hgd n (e0 + i)) ns 0

lemma executable_src {cmd : ACmd (Loc M H) s} (h : cmd ∈ verifierCmds' M x s ℓ H) :
    (AP (ℓ := ℓ) (N := numLoc M H) Loc.code Loc.accept Loc.reject code_accept_ne_reject
      (verifierCmds' M x s ℓ H)).executable (Loc.code cmd.src) = true := by
  obtain ⟨h1, h2⟩ := src_ne_of_mem h
  simp only [RegisterProgram.executable, decide_eq_true_eq]
  exact ⟨fun h' => h1 (Loc.code_injective h'), fun h' => h2 (Loc.code_injective h')⟩

variable (hρ : ρ.length = b)
include hρ

/-- The schemas of one command. -/
lemma cmd_forall₂ (hNb : NX.Bnd b) (hN : NX.eval ρ = numLoc M H) {τ : List ℕ}
    {cmd : ACmd (Loc M H) s} (hrel : StkCmd x s ℓ H b ρ τ cmd)
    (hmem : cmd ∈ verifierCmds' M x s ℓ H) (j e0 : ℕ) :
    List.Forall₂ (StkSch M x s ℓ H b ρ)
      ((cmdN (Loc.code (M := M) (H := H)) j cmd).map fun n =>
        (cmdDom (ℓ := ℓ) Loc.code Loc.accept Loc.reject code_accept_ne_reject
          (verifierCmds' M x s ℓ H) cmd, n))
      (cmdSchStks NX b τ j e0) := by
  obtain ⟨hτl, hτρ, hsrc, hd⟩ := hrel
  set σ := τ ++ [j, e0] with hσdef
  have hσl : σ.length = b + 27 := by simp [hσdef, hτl]
  have hσρ : σ.take b = ρ := by rw [hσdef, List.take_append_of_le_length (by omega), hτρ]
  have evr : ∀ i < 8, (var (b + 17 + i)).eval σ = (τ.drop (b + 17)).getD i 0 := fun i hi => by
    rw [getD_drop']; simp only [Xp.eval_var, hσdef]
    exact List.getD_append _ _ _ _ (by omega)
  have ev15 : (var (b + 15)).eval σ = τ.getD (b + 15) 0 := by
    simp only [Xp.eval_var, hσdef]; exact List.getD_append _ _ _ _ (by omega)
  have ev25 : (var (b + 25)).eval σ = j := by
    simp only [Xp.eval_var, hσdef]
    rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hτl]
  have evN : NX.eval σ = numLoc M H := by
    rw [show σ = ρ ++ σ.drop b by rw [← hσρ, List.take_append_drop]]
    exact (Xp.eval_append hρ _ hNb).trans hN
  have evS : ∀ t, (slotX NX b t).eval σ = numLoc M H + (t + 8 * j) := fun t => by
    simp [slotX, evN, ev25]
  set r := τ.drop (b + 17) with hr
  have hrl : r.length = 8 := CmdDesc.length hd
  have hgd : (gdX b).map (·.eval σ) = r.drop 4 := by
    rw [eq_of_length_four (l := r.drop 4) (by simp [hrl])]
    simp only [gdX, List.map_cons, List.map_nil, getD_drop']
    rw [show b + 21 = b + 17 + 4 by omega, show b + 22 = b + 17 + 5 by omega,
      show b + 23 = b + 17 + 6 by omega, show b + 24 = b + 17 + 7 by omega,
      evr 4 (by omega), evr 5 (by omega), evr 6 (by omega), evr 7 (by omega)]
  have h17 : τ.getD (b + 17) 0 = r.getD 0 0 := by rw [hr, getD_drop']
  unfold cmdSchStks
  rw [← hσdef, hgd]
  have hgdl : (r.drop 4).length = 4 := by simp [hrl]
  clear_value σ r
  cases cmd with
  | assign p g m q =>
    obtain ⟨-, h0, h1, h2, hg⟩ := hd
    rw [h17, h0, if_neg (by simp)]
    have hD : cmdDom (ℓ := ℓ) Loc.code Loc.accept Loc.reject code_accept_ne_reject
        (verifierCmds' M x s ℓ H) (ACmd.assign p g m q) = guardDomain (toGuard g) true := by
      unfold cmdDom; rw [executable_src hmem]; rfl
    refine forall₂_stks hσl hσρ (Or.inl hg) hD hgdl _ _ ?_ e0
    rw [assignBlk, eval_gadgetX]
    simp only [cmdN, evS, ev15, hsrc]
    have e18 := evr 1 (by omega)
    have e19 := evr 2 (by omega)
    rw [show b + 17 + 1 = b + 18 by omega] at e18
    rw [show b + 17 + 2 = b + 19 by omega] at e19
    rw [e18, e19, h1, h2]
    rfl
  | fork p g q q' =>
    obtain ⟨-, h0, h2, h3, hg⟩ := hd
    rw [h17, h0, if_pos (by simp)]
    have hD : cmdDom (ℓ := ℓ) Loc.code Loc.accept Loc.reject code_accept_ne_reject
        (verifierCmds' M x s ℓ H) (ACmd.fork p g q q') = guardDomain (toGuard g) true := by
      unfold cmdDom; rw [executable_src hmem]; rfl
    refine forall₂_stks hσl hσρ (Or.inl hg) hD hgdl _ _ ?_ e0
    have e19 := evr 2 (by omega)
    have e20 := evr 3 (by omega)
    rw [show b + 17 + 2 = b + 19 by omega] at e19
    rw [show b + 17 + 3 = b + 20 by omega] at e20
    have hs : (var (b + 15)).eval σ = (Loc.code p).val := ev15.trans hsrc
    simp only [forkBlk, List.map_append, eval_gadgetX, cmdN, evS, hs, e19, e20, h2, h3]
    simp [SchNum.toL, terN, evS, hs]

end Final

lemma map_getD_blk {α : Type} {σ : List ℕ} {n : ℕ} (hσ : σ.length = n) (e0 : ℕ) (blk : List α)
    (f : α × ℕ → List ℕ) :
    (blk.zipIdx.map fun p => σ ++ (e0 + p.2) :: f p).map (·.getD n 0) =
      (List.range blk.length).map (e0 + ·) := by
  rw [List.map_map, List.range_eq_range', ← map_zipIdx_snd (e0 + ·) blk 0]
  refine List.map_congr_left fun p _ => ?_
  simp [List.getD_append_right, hσ]

section Main

variable {x : List Bool} {ρ : List ℕ} {b H ℓ : ℕ} {HX RX NX rX p0X EcX : Xp}
  (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
  (hR : RX.eval ρ = radix M H)
  (hNb : NX.Bnd b) (hN : NX.eval ρ = numLoc M H)
  (hrb : rX.Bnd b) (hr : rX.eval ρ = (verifierCmds' M x s ℓ H).length)
  (hpb : p0X.Bnd b) (hp : p0X.eval ρ = (Loc.code (Loc.query : Loc M H)).val)
  (hEb : EcX.Bnd b) (hE : EcX.eval ρ = ((verifierCmds' M x s ℓ H).map cmdSz).sum)
include hρ hHb hRb hH hR hNb hN hrb hr hpb hp hEb hE

end Main

end Lax119563Proofs.Reduction

end Reduction_SchFinal

/-! ### Formerly `Lax119563Proofs.Reduction.DomGen` -/

section Reduction_DomGen

/-!
# Expressions for the domain test

The field expressions of the domain test of a schema: `fieldX` (a field of a register value),
`fieldBadX` (the field violates the guard; `fieldBad_iff`, `fieldOK_iff`) and `initCVX` (the
initial cell value), with their values, and further evaluation lemmas for the derived
expressions (`Xp.le`, `eval_and'`, `eval_or'`, `eval_not'`, `eval_shr`, `eval_xorM`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Xp

namespace Xp

variable {ρ : List ℕ}

/-- `a ≤ b`. -/
def le (a b : Xp) : Xp := not (lt b a)

lemma eval_bool {e : Xp} {P : Prop} [Decidable P] (h : e.eval ρ = if P then 1 else 0) :
    e.eval ρ ≤ 1 := by
  rw [h]; split_ifs <;> omega

lemma eval_and' {a b : Xp} {P Q : Prop} [Decidable P] [Decidable Q]
    (ha : a.eval ρ = if P then 1 else 0) (hb : b.eval ρ = if Q then 1 else 0) :
    (and a b).eval ρ = if P ∧ Q then 1 else 0 := by
  rw [eval_and (eval_bool ha) (eval_bool hb), ha, hb]
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

lemma eval_or' {a b : Xp} {P Q : Prop} [Decidable P] [Decidable Q]
    (ha : a.eval ρ = if P then 1 else 0) (hb : b.eval ρ = if Q then 1 else 0) :
    (or a b).eval ρ = if P ∨ Q then 1 else 0 := by
  rw [eval_or, ha, hb]
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

lemma eval_not' {a : Xp} {P : Prop} [Decidable P] (ha : a.eval ρ = if P then 1 else 0) :
    (not a).eval ρ = if ¬ P then 1 else 0 := by
  rw [eval_not, ha]
  by_cases hP : P <;> simp [hP]

lemma eval_le (a b : Xp) : (le a b).eval ρ = if a.eval ρ ≤ b.eval ρ then 1 else 0 := by
  rw [le, eval_not' (P := b.eval ρ < a.eval ρ) (by rw [eval_lt_eq])]
  by_cases h : a.eval ρ ≤ b.eval ρ
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

@[simp] lemma eval_odd (a : Xp) : (odd a).eval ρ = a.eval ρ % 2 := rfl
@[simp] lemma eval_shr (a k : Xp) : (shr a k).eval ρ = a.eval ρ / 2 ^ k.eval ρ := rfl
@[simp] lemma eval_xorM (a b k : Xp) :
    (xorM a b k).eval ρ = (a.eval ρ ^^^ b.eval ρ) % 2 ^ k.eval ρ := rfl

end Xp

/-! ## Arithmetic of the field guard -/

lemma div_eq_iff_window {a ℓ i : ℕ} (hℓ : 0 < ℓ) : a / ℓ = i ↔ i * ℓ ≤ a ∧ a < i * ℓ + ℓ := by
  constructor
  · rintro rfl
    exact ⟨Nat.div_mul_le_self a ℓ, by have := Nat.lt_div_mul_add (a := a) hℓ; linarith⟩
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 (by rw [Nat.succ_mul]; exact h2)

lemma testBit_eq_mod (v j : ℕ) : v.testBit j = decide (v / 2 ^ j % 2 = 1) :=
  Nat.testBit_eq_decide_div_mod_eq

lemma shift_bit (v a j : ℕ) : v * 2 ^ a / 2 ^ (a + j) = v / 2 ^ j := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (by positivity)]

/-- A violation of the field guard at offset `t`. -/
lemma fieldBad_iff {ℓ k t i v q : ℕ} (hℓ : 0 < ℓ) :
    ((k + t) / ℓ = i ∧ v.testBit ((k + t) % ℓ) ≠ q.testBit t) ↔
      (i * ℓ ≤ k + t ∧ k + t < i * ℓ + ℓ ∧ v * 2 ^ (i * ℓ) / 2 ^ (k + t) % 2 ≠ q / 2 ^ t % 2) := by
  rw [div_eq_iff_window hℓ]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, k + t = i * ℓ + j := ⟨k + t - i * ℓ, by omega⟩
    have hm : (k + t) % ℓ = j := by
      rw [hj, Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
    rw [hm, testBit_eq_mod, testBit_eq_mod] at h3
    rw [hj, shift_bit]
    intro h; apply h3; rw [h]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, k + t = i * ℓ + j := ⟨k + t - i * ℓ, by omega⟩
    have hm : (k + t) % ℓ = j := by
      rw [hj, Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
    rw [hm, testBit_eq_mod, testBit_eq_mod]
    rw [hj, shift_bit] at h3
    intro h
    apply h3
    have e1 := Nat.mod_two_eq_zero_or_one (v / 2 ^ j)
    have e2 := Nat.mod_two_eq_zero_or_one (q / 2 ^ t)
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> simp_all

lemma fieldOK_iff {ℓ k m q i v : ℕ} (hℓ : 0 < ℓ) :
    fieldOK ℓ k m q i v = true ↔ ∀ t < m, ¬ (i * ℓ ≤ k + t ∧ k + t < i * ℓ + ℓ ∧
      v * 2 ^ (i * ℓ) / 2 ^ (k + t) % 2 ≠ q / 2 ^ t % 2) := by
  simp only [fieldOK, decide_eq_true_eq]
  refine forall_congr' fun t => imp_congr_right fun _ => ?_
  rw [← fieldBad_iff hℓ]
  tauto

/-! ## The generator -/

/-- The field `field (2^H) (iℓ) ℓ`. -/
def fieldX (iℓX ℓX HX : Xp) : Xp := xorM (shr (pow2 HX) iℓX) (const 0) ℓX

/-- The number `initCV x ν v` from `xb = inBit x v`. -/
def initCVX (νX vX xbX : Xp) : Xp :=
  add (eq vX (const 0)) (mulC 2 (mul xbX (eq νX (const 0))))

/-- A violation of the field guard at offset `t`. -/
def fieldBadX (iℓX kX tX vX qX ℓX : Xp) : Xp :=
  and (and (le iℓX (add kX tX)) (lt (add kX tX) (add iℓX ℓX)))
    (not (eq (odd (shr (shl vX iℓX) (add kX tX))) (odd (shr qX tX))))

lemma eval_fieldX {ρ : List ℕ} (iℓX ℓX HX : Xp) :
    (fieldX iℓX ℓX HX).eval ρ = field (2 ^ HX.eval ρ) (iℓX.eval ρ) (ℓX.eval ρ) := by
  simp [fieldX, field]

lemma eval_initCVX {ρ : List ℕ} {x : List Bool} {ν v : ℕ} {νX vX xbX : Xp}
    (hν : νX.eval ρ = ν) (hv : vX.eval ρ = v) (hxb : xbX.eval ρ = inBit x v) :
    (initCVX νX vX xbX).eval ρ = initCV x ν v := by
  simp only [initCVX, initCV, Xp.eval_add, Xp.eval_eq, Xp.eval_const, Xp.eval_mulC, Xp.eval_mul,
    hν, hv, hxb]
  by_cases h : ν = 0 <;> simp [h]


end Lax119563Proofs.Reduction

end Reduction_DomGen

/-! ### Formerly `Lax119563Proofs.Reduction.CostDom` -/

section Reduction_CostDom

/-!
# Classes of the domain test expressions

Typing lemmas for the expressions of the domain test: `hasTy_mulCBig`, `hasTy_le`,
`hasTy_fieldX`, `hasTy_fieldBadX`.
-/

namespace Lax119563Proofs.Reduction

open Xp Ty Gn

variable {Γ : List Ty}

lemma hasTy_mulCBig {a : Xp} {τ : Ty} (ha : HasTy Γ a τ) : ∀ c, HasTy Γ (mulC c a) .big
  | 0 => (hasTy_const 0).big
  | c + 1 => hasTy_addBig (hasTy_mulCBig ha c) ha

lemma hasTy_le {a b : Xp} {τa τb : Ty} (ha : HasTy Γ a τa) (hb : HasTy Γ b τb) :
    HasTy Γ (Xp.le a b) (P 0 0) := hasTy_not (hasTy_lt hb ha)

lemma hasTy_fieldX {iℓX ℓX HX : Xp} (hi : HasTy Γ iℓX (P 0 1)) (hℓ : HasTy Γ ℓX (P 0 1))
    (hH : HasTy Γ HX (P 0 1)) : HasTy Γ (fieldX iℓX ℓX HX) .big :=
  hasTy_xorM (hasTy_shr (hasTy_pow2 hH) hi) (hasTy_const 0) hℓ

lemma hasTy_fieldBadX {iℓX kX tX vX qX ℓX : Xp} {τv τq : Ty} (hi : HasTy Γ iℓX (P 0 1))
    (hk : HasTy Γ kX (P 0 1)) (ht : HasTy Γ tX (P 0 1)) (hv : HasTy Γ vX τv)
    (hq : HasTy Γ qX τq) (hℓ : HasTy Γ ℓX (P 0 1)) :
    HasTy Γ (fieldBadX iℓX kX tX vX qX ℓX) (P 0 0) := by
  have hkt : HasTy Γ (add kX tX) (P 0 1) := hasTy_add hk ht
  exact hasTy_and (hasTy_and (hasTy_le hi hkt) (hasTy_lt hkt (hasTy_add hi hℓ)))
    (hasTy_not (hasTy_eq (hasTy_odd (hasTy_shr (hasTy_shl hv hi) hkt))
      (hasTy_odd (hasTy_shr hq ht))))

end Lax119563Proofs.Reduction

end Reduction_CostDom

/-! ### Formerly `Lax119563Proofs.Reduction.CostGlob` -/

section Reduction_CostGlob

/-!
# The minimum of two expressions

`Xp.minR a b` (the minimum, of the class of `b` whatever the class of `a`; `hasTy_minR`) is
used by the prelude to compute `2^ℓ` in class `P 1 0`.
-/

namespace Lax119563Proofs.Reduction

open Xp Ty

namespace Xp

/-- The minimum of `a` and `b`. -/
def minR (a b : Xp) : Xp :=
  add (mulB a (lt a b) (const 1)) (mulB b (Xp.not (lt a b)) (const 1))

lemma eval_minR (a b : Xp) (ρ : List ℕ) : (minR a b).eval ρ = min (a.eval ρ) (b.eval ρ) := by
  simp only [minR, eval, Xp.not]
  by_cases h : a.eval ρ < b.eval ρ
  · simp [h, min_eq_left h.le]
  · simp [h, min_eq_right (by omega : b.eval ρ ≤ a.eval ρ)]

/-- An expression whose value is bounded by that of a typed expression has its class. -/
lemma HasTy.of_eval_le {τs : List Ty} {a b : Xp} {τa τ : Ty} (ha : HasTy τs a τa)
    (hb : HasTy τs b τ) (h : ∀ ρ, a.eval ρ ≤ b.eval ρ) : HasTy τs a τ := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kb, hKb⟩ := hb K₀
  refine ⟨Ka + Kb, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, -, -⟩ := hKb ℓ ρ hA
  exact ⟨le_trans (h ρ) (le_trans b1 (Ty.bnd_mono (by omega) ℓ τ)),
    Fits.mono (two_pow_mono (by omega)) _ a2, le_trans a3 (Nat.mul_le_mul_right _ (by omega))⟩

lemma hasTy_minR {τs : List Ty} {a b : Xp} {τa τb : Ty} (ha : HasTy τs a τa)
    (hb : HasTy τs b τb) : HasTy τs (minR a b) τb := by
  have h1 : HasTy τs (const 1) (P 0 1) := (hasTy_const 1).le ⟨le_rfl, by omega⟩
  have hc : HasTy τs (lt a b) (P 0 0) := hasTy_lt ha hb
  have hbig : HasTy τs (minR a b) .big :=
    hasTy_addBig (hasTy_mulBBig ha hc h1) (hasTy_mulBBig hb (hasTy_not hc) h1)
  exact HasTy.of_eval_le hbig hb fun ρ => by rw [eval_minR]; exact min_le_right _ _

end Xp

end Lax119563Proofs.Reduction

end Reduction_CostGlob

/-! ### Formerly `Lax119563Proofs.Reduction.PassBase` -/

section Reduction_PassBase

/-!
# Infrastructure of the system generator

* `Iv M x s ℓ H`: the compiled code-ordered time program, the implicit parity system emitted
  by the generator;
* `SchCtx`: the context of the body of the schema enumerator at a schema index, and lemmas on
  `List.getD` and `flatMap` over ranges.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

/-! ## The system -/

/-- The code-ordered verifier program for the width `ℓ` and horizon `H`. -/
noncomputable abbrev APv (M : Machine) (x : List Bool) (s ℓ H : ℕ) : RegisterProgram s ℓ :=
  AP (ℓ := ℓ) (N := numLoc M H) Loc.code Loc.accept Loc.reject code_accept_ne_reject
    (verifierCmds' M x s ℓ H)

/-- Its compiled implicit parity system. -/
noncomputable def Iv (M : Machine) (x : List Bool) (s ℓ H : ℕ) :
    ImplicitParitySystem (s + 1) ℓ :=
  (APv M x s ℓ H).compile (Loc.query : Loc M H).code (fun _ _ => 0)

lemma Iv_schemas {M : Machine} {x : List Bool} {s ℓ H : ℕ} : (Iv M x s ℓ H).schemas =
    (APv M x s ℓ H).compiledSchemas (Loc.query : Loc M H).code (fun _ _ => 0) := rfl

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

/-! ## Stacks -/

lemma getD_app (τ l : List ℕ) (k : ℕ) : (τ ++ l).getD (τ.length + k) 0 = l.getD k 0 := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1; omega

/-! ## The schema enumerator as a loop over schema indices -/

/-- The context of the body of the schema enumerator for schema `e`. -/
def SchCtx (M : Machine) (x : List Bool) (s ℓ H b : ℕ) (ρ : List ℕ) (τ : List ℕ) (e : ℕ)
    (sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations) : Prop :=
  τ.length = b + 37 ∧ τ.take b = ρ ∧ τ.getD (b + 27) 0 = e ∧
    SchRec M x s ℓ H sc (τ.drop (b + 28))

lemma flatMap_eq_range {α β : Type} (l : List α) (d : α) (f : α → List β) :
    l.flatMap f = (List.range l.length).flatMap fun e => f (l.getD e d) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, ih, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp

lemma forall₂_getD {α β : Type} {R : α → β → Prop} (d : β) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ i (h₁ : i < l₁.length),
      R l₁[i] (l₂.getD i d)
  | _ :: _, _ :: _, List.Forall₂.cons h _, 0, _ => h
  | _ :: _, _ :: _, List.Forall₂.cons _ t, i + 1, h₁ => by
    simpa using forall₂_getD d t i (by simpa using h₁)

lemma getD_of_map_eq_range {α : Type} (f : α → ℕ) (d : α) {l : List α}
    (h : l.map f = List.range l.length) {i : ℕ} (hi : i < l.length) : f (l.getD i d) = i := by
  have := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_range hi, List.getElem?_eq_getElem hi,
    Option.map_some, Option.some.injEq] at this
  rw [List.getD_eq_getElem _ _ hi]
  exact this

/-! ## Register values of block coordinates -/

lemma regVal_toBlk {v : ℕ} (hv : v < 2 ^ ℓ) : Circuits.regVal (toBlk ℓ v) = v := by
  rw [toBlk, regVal_ofAddr]
  simp [Circuits.field, Nat.mod_eq_of_lt hv]

/-! ## The domain test -/

/-! ## The shift of a permutation described by a mask -/

end Lax119563Proofs.Reduction

end Reduction_PassBase

/-! ### Formerly `Lax119563Proofs.Reduction.CostPassBase` -/

section Reduction_CostPassBase

/-!
# Fits and cost of the system generator: tools

* `Tp Γ e`: `e` has *some* class (enough for emitted numbers and tests); rules `tp_*` and the
  tactic `tp`, which also closes the linear (`P 0 1`) side conditions of shifts and products
  for concrete contexts;
* the leaf tactics `tvb` (a variable read with its class and bound, for concrete contexts).
-/

namespace Lax119563Proofs.Reduction

open Xp Ty Gn

/-- Some class. -/
structure Tp (Γ : List Ty) (e : Xp) : Prop where
  intro ::
  ex : ∃ τ, HasTy Γ e τ

variable {Γ : List Ty}

lemma tp_var (i : ℕ) : Tp Γ (var i) := ⟨⟨_, hasTy_var i⟩⟩
lemma tp_const (c : ℕ) : Tp Γ (const c) := ⟨⟨_, hasTy_const c⟩⟩
lemma tp_add {a b : Xp} (ha : Tp Γ a) (hb : Tp Γ b) : Tp Γ (add a b) :=
  ⟨⟨_, hasTy_addBig ha.ex.choose_spec hb.ex.choose_spec⟩⟩
lemma tp_odd {a : Xp} (ha : Tp Γ a) : Tp Γ (odd a) := ⟨⟨_, hasTy_odd ha.ex.choose_spec⟩⟩
lemma tp_shl {a k : Xp} (ha : Tp Γ a) (hk : HasTy Γ k (P 0 1)) : Tp Γ (shl a k) :=
  ⟨⟨_, hasTy_shl ha.ex.choose_spec hk⟩⟩
lemma tp_shr {a k : Xp} (ha : Tp Γ a) (hk : HasTy Γ k (P 0 1)) : Tp Γ (shr a k) :=
  ⟨⟨_, hasTy_shr ha.ex.choose_spec hk⟩⟩
lemma hasTy_lin_const (c : ℕ) : HasTy Γ (const c) (P 0 1) :=
  (hasTy_const c).le ⟨le_rfl, Nat.zero_le _⟩
lemma tp_eq {a b : Xp} (ha : Tp Γ a) (hb : Tp Γ b) : Tp Γ (Xp.eq a b) :=
  ⟨⟨_, hasTy_eq ha.ex.choose_spec hb.ex.choose_spec⟩⟩
/-- Typing of the tests, numbers and linear side conditions (concrete contexts). -/
macro "tp" : tactic => `(tactic| repeat' (first
  | assumption
  | exact tp_var _
  | exact tp_const _
  | exact hasTy_var' rfl
  | exact hasTy_lin_const _
  | exact hasTy_var_lin rfl
  | apply tp_eq
  | apply tp_and
  | apply tp_or
  | apply tp_not
  | apply tp_mul
  | apply tp_add
  | apply tp_lt
  | apply tp_half
  | apply tp_odd
  | apply tp_shl
  | apply tp_shr
  | apply tp_xorM
  | apply tp_mulB
  | apply hasTy_lin_add
  | apply hasTy_lin_not
  | apply hasTy_lin_lt
  | apply hasTy_lin_mul0
  | apply tp_xfX
  | apply tp_mulC
  | apply hasTy_lin_mulC))

/-- A variable with its class and bound (concrete contexts). -/
macro "tvb" : tactic => `(tactic| exact ⟨hasTy_var _, by show _ < List.length _; decide⟩)

/-! ## Generators from `Tp` -/

lemma hasCost_emit' {a : Xp} (ha : Tp Γ a) : HasCost Γ (emit a) 0 0 :=
  hasCost_emit ha.ex.choose_spec

lemma hasCost_ite' {c : Xp} {g h : Gn} {e d : ℕ} (hc : Tp Γ c) (hg : HasCost Γ g e d)
    (hh : HasCost Γ h e d) : HasCost Γ (ite c g h) e d := hasCost_ite hc.ex.choose_spec hg hh

lemma hasCost_when' {c : Xp} {g : Gn} {e d : ℕ} (hc : Tp Γ c) (hg : HasCost Γ g e d) :
    HasCost Γ (when c g) e d := hasCost_when hc.ex.choose_spec hg

end Lax119563Proofs.Reduction

end Reduction_CostPassBase

/-! ### Formerly `Lax119563Proofs.Reduction.CostWF` -/

section Reduction_CostWF

/-!
# Well-formedness of the generators (`WFX`, `NoX`)

`Gn.Cl P`: a predicate on generators closed under `skip, emit, seq, ite, bind, loop, log, count`.
Both `NoX` and `WFX` are closed. For closed predicates: `seqL, when, dispatch, bindL, bindSub,
firstL, brGen, emitN, blkGen, cmdEnum, schEnum` preserve `P`; the domain test `violAt` is
`NoX`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Xp

namespace Gn

/-- Closure under the constructors other than `loopX` and `len`. -/
structure Cl (P : Gn → Prop) : Prop where
  skip : P .skip
  emit : ∀ e, P (.emit e)
  seq : ∀ {g h}, P g → P h → P (.seq g h)
  ite : ∀ c {g h}, P g → P h → P (.ite c g h)
  bind : ∀ e {g}, P g → P (.bind e g)
  loop : ∀ l {g}, P g → P (.loop l g)
  log : ∀ e {g}, P g → P (.log e g)
  count : ∀ {g h}, P g → P h → P (.count g h)

lemma cl_noX : Cl NoX :=
  ⟨trivial, fun _ => trivial, fun hg hh => ⟨hg, hh⟩, fun _ _ _ hg hh => ⟨hg, hh⟩,
    fun _ _ hg => hg, fun _ _ hg => hg, fun _ _ hg => hg, fun hg hh => ⟨hg, hh⟩⟩

lemma cl_wfx : Cl WFX :=
  ⟨trivial, fun _ => trivial, fun hg hh => ⟨hg, hh⟩, fun _ _ _ hg hh => ⟨hg, hh⟩,
    fun _ _ hg => hg, fun _ _ hg => hg, fun _ _ hg => hg, fun hg hh => ⟨hg, hh⟩⟩

variable {P : Gn → Prop} (hP : Cl P)
include hP

lemma Cl.seqL : ∀ {gs : List Gn}, (∀ g ∈ gs, P g) → P (seqL gs)
  | [], _ => hP.skip
  | g :: gs, h => hP.seq (h g (by simp)) (Cl.seqL fun g' hg' => h g' (by simp [hg']))

lemma Cl.when (c : Xp) {g : Gn} (hg : P g) : P (when c g) := hP.ite c hg hP.skip

lemma Cl.bindL {g : Gn} (hg : P g) : ∀ es : List Xp, P (bindL es g)
  | [] => hg
  | e :: es => hP.bind e (Cl.bindL hg es)

lemma Cl.bindSub (n : ℕ) (a b : Xp) {g : Gn} (hg : P g) : P (bindSub n a b g) :=
  hP.count (hP.loop _ (hP.when _ (hP.emit _))) hg

lemma Cl.firstL {α : Type} (c : α → Xp) {f : α → Gn} (hf : ∀ a, P (f a)) :
    ∀ l : List α, P (firstL c f l)
  | [] => hP.skip
  | a :: l => hP.ite _ (hf a) (Cl.firstL c hf l)

lemma Cl.brGen {M : Machine} {s : ℕ} (RX HX : Xp) {body : Gn} (hb : P body) :
    ∀ brs : List (Xp × List (SMv M s)), P (brGen RX HX body brs)
  | [] => hP.skip
  | (c, ms) :: rest => hP.ite c (hP.seqL fun g hg => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hg
      exact hP.bindL hb _) (Cl.brGen RX HX hb rest)

lemma Cl.emitN (n : ℕ) : P (emitN n) :=
  hP.seqL fun g hg => by
    rw [List.eq_of_mem_replicate hg]; exact hP.emit _

lemma Cl.blkGen (e0 : Xp) (gd : List Xp) {body : Gn} (hb : P body) (blk : List (List Xp)) :
    P (blkGen e0 gd body blk) :=
  hP.seqL fun g hg => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hg
    exact hP.bindL hb _

end Gn

namespace Gn

lemma wfx_of_noX {g : Gn} (h : NoX g) : WFX g := by
  induction g with
  | skip => trivial
  | emit _ => trivial
  | seq _ _ ig ih => exact ⟨ig h.1, ih h.2⟩
  | ite _ _ _ ig ih => exact ⟨ig h.1, ih h.2⟩
  | bind _ _ ig => exact ig h
  | loop _ _ ig => exact ig h
  | loopX _ _ _ => exact h.elim
  | len _ _ => exact h.elim
  | log _ _ ig => exact ig h
  | count _ _ ig ih => exact ⟨ig h.1, ih h.2⟩

end Gn

end Lax119563Proofs.Reduction

end Reduction_CostWF

/-! ### Formerly `Lax119563Proofs.Reduction.PkSch` -/

section Reduction_PkSch

/-!
# The schema enumerator for a runtime number of blocks

`schEnumP M b SX HX RX NX rX p0X EcX body` runs `body` once for every schema of the compiled
code-ordered time program, on the stacks `schStksP` (`out_schEnumP`): each has length `b + 37`,
carries its index at level `b + 27` and the record `SchRec` of the schema from `b + 28` on
(the blocks of `Reduction/SchGen`, the stacks of `Reduction/SchOut`, `Reduction/SchFinal`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

variable {M : Machine} {s : ℕ}

section Gens

variable (M)

/-- The body of the command enumerator: count `j` (level `b + 25`) and `e₀` (level
`b + 26`), then run `body` for the schemas of the command. -/
def cmdBodyP (b : ℕ) (SX HX RX NX : Xp) (body : Gn) : Gn :=
  .count (cmdEnumP M (b + 26) SX HX RX (Gn.when (beforeX b (b + 26)) (.emit (const 0))))
    (.count (cmdEnumP M (b + 27) SX HX RX (Gn.when (beforeX b (b + 27))
        (.ite (var (b + 27 + 17)) (Gn.emitN 9) (Gn.emitN 4))))
      (.ite (var (b + 17)) (Gn.blkGen (var (b + 26)) (gdX b) body (forkBlk NX b))
        (Gn.blkGen (var (b + 26)) (gdX b) body (assignBlk NX b))))

/-- **The schema enumerator** for a runtime number of blocks. -/
def schEnumP (b : ℕ) (SX HX RX NX rX p0X EcX : Xp) (body : Gn) : Gn :=
  .seq (cmdEnumP M b SX HX RX (cmdBodyP M b SX HX RX NX body)) (detGen NX rX p0X EcX body)

end Gens

variable (M s) in
/-- The stacks of all schemas. -/
noncomputable def schStksP (b : ℕ) (HX RX NX rX p0X EcX : Xp) (x : List Bool) (ρ : List ℕ)
    (ℓ H : ℕ) : List (List ℕ) :=
  (cmdStksP M b HX RX ρ s H).zipIdx.flatMap (fun p =>
    cmdSchStks NX b p.1 p.2 (e0Of (M := M) (s := s) x ℓ H p.2)) ++ detStks NX rX p0X EcX ρ

section Out

variable {x y : List Bool} {ρ : List ℕ} {b H ℓ : ℕ} {SX HX RX NX rX p0X EcX : Xp}
  (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hSb : SX.Bnd b) (hH : HX.eval ρ = H)
  (hR : RX.eval ρ = radix M H) (hS : SX.eval ρ = s) (hs : 1 ≤ s)
include hρ hHb hRb hH hR

lemma length_cmdStksP_eq {b' : ℕ} {σ : List ℕ} (hσ : σ.length = b') (hσρ : σ.take b = ρ)
    (hb' : b ≤ b') (ℓ : ℕ) :
    (cmdStksP M b' HX RX σ s H).length = (cmdStksP M b HX RX ρ s H).length := by
  have hσsplit : σ = ρ ++ σ.drop b := by rw [← hσρ, List.take_append_drop]
  have hHσ : HX.eval σ = H := by rw [hσsplit]; exact (Xp.eval_append hρ _ hHb).trans hH
  have hRσ : RX.eval σ = radix M H := by rw [hσsplit]; exact (Xp.eval_append hρ _ hRb).trans hR
  rw [(cmdStksP_forall₂ (x := ([] : List Bool)) (s := s) hσ (Xp.Bnd.mono hb' hHb) (Xp.Bnd.mono hb' hRb) hHσ hRσ
    ℓ).length_eq, (cmdStksP_forall₂ (x := ([] : List Bool)) (s := s) hρ hHb hRb hH hR ℓ).length_eq]

include hSb hS hs

/-- **The body of the command enumerator.** -/
theorem out_cmdBodyP (hNb : NX.Bnd b) (ℓ : ℕ) (body : Gn) {j : ℕ}
    (hj : j < (cmdStksP M b HX RX ρ s H).length) :
    (cmdBodyP M b SX HX RX NX body).out y (cmdStksP M b HX RX ρ s H)[j] =
      (cmdSchStks NX b (cmdStksP M b HX RX ρ s H)[j] j
        (e0Of (M := M) (s := s) x ℓ H j)).flatMap (body.out y) := by
  set C := cmdStksP M b HX RX ρ s H with hC
  set τ := C[j] with hτ
  have hF := cmdStksP_forall₂ (x := x) (s := s) hρ hHb hRb hH hR ℓ
  have hrel : StkCmd x s ℓ H b ρ τ ((verifierCmds' M x s ℓ H)[j]'(hF.length_eq ▸ hj)) :=
    List.forall₂_iff_get.mp hF |>.2 j hj _
  obtain ⟨hτl, hτρ, -, -⟩ := hrel
  -- the count of `j`
  have h1 : ((cmdEnumP M (b + 26) SX HX RX (Gn.when (beforeX b (b + 26))
      (.emit (const 0)))).out y (τ ++ [0])).length = j := by
    rw [length_out_beforeP ℓ hρ hHb hRb hSb hH hR hS hs (by omega) (by simp [hτl])
      (by rw [List.take_append_of_le_length (by omega), hτρ]) hj
      (by rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)])]
    have hl := length_cmdStksP_eq (s := s) hρ hHb hRb hH hR (b' := b + 26)
      (σ := τ ++ [0]) (by simp [hτl])
      (by rw [List.take_append_of_le_length (by omega), hτρ]) (by omega) ℓ
    simp only [Gn.out, List.length_singleton, List.map_const', List.sum_replicate, smul_eq_mul,
      mul_one, List.length_take]
    omega
  -- the count of `e₀`
  have h2 : ((cmdEnumP M (b + 27) SX HX RX (Gn.when (beforeX b (b + 27))
      (.ite (var (b + 27 + 17)) (Gn.emitN 9) (Gn.emitN 4)))).out y (τ ++ [j, 0])).length =
      e0Of (M := M) (s := s) x ℓ H j := by
    have hσl : (τ ++ [j, 0]).length = b + 27 := by simp [hτl]
    have hσρ : (τ ++ [j, 0]).take b = ρ := by
      rw [List.take_append_of_le_length (by omega), hτρ]
    rw [length_out_beforeP ℓ hρ hHb hRb hSb hH hR hS hs (by omega) hσl hσρ hj
      (by rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)])]
    have hσsplit : τ ++ [j, 0] = ρ ++ (τ ++ [j, 0]).drop b := by
      rw [← hσρ, List.take_append_drop]
    have hHσ : HX.eval (τ ++ [j, 0]) = H := by
      rw [hσsplit]; exact (Xp.eval_append hρ _ hHb).trans hH
    have hRσ : RX.eval (τ ++ [j, 0]) = radix M H := by
      rw [hσsplit]; exact (Xp.eval_append hρ _ hRb).trans hR
    have hF2 := cmdStksP_forall₂ (x := x) (s := s) hσl (Xp.Bnd.mono (by omega) hHb)
      (Xp.Bnd.mono (by omega) hRb) hHσ hRσ ℓ
    rw [e0Of]
    refine congrArg List.sum (forall₂_map_eq (R := StkCmd x s ℓ H (b + 27) (τ ++ [j, 0]))
      (fun τ' cmd h => ?_) (List.forall₂_take j hF2))
    have := szAt_of_stkCmd h
    simp only [szAt] at this
    simp only [Gn.out]
    split_ifs with hc
    · rw [Gn.length_out_emitN]; simp only [Xp.eval_var] at hc; rw [if_pos hc] at this; exact this
    · rw [Gn.length_out_emitN]; simp only [Xp.eval_var] at hc
      rw [if_neg (by simpa using hc)] at this; exact this
  simp only [cmdBodyP, Gn.out]
  rw [h1, show τ ++ [j] ++ [0] = τ ++ [j, 0] by simp, h2,
    show τ ++ [j] ++ [e0Of (M := M) (s := s) x ℓ H j] = τ ++ [j, e0Of (M := M) (s := s) x ℓ H j]
      by simp]
  have hlen : (τ ++ [j, e0Of (M := M) (s := s) x ℓ H j]).length = b + 27 := by simp [hτl]
  have e17 : (var (b + 17)).eval (τ ++ [j, e0Of (M := M) (s := s) x ℓ H j]) =
      τ.getD (b + 17) 0 := by
    simp only [Xp.eval_var]; exact List.getD_append _ _ _ _ (by omega)
  rw [e17, cmdSchStks]
  have e26 : (var (b + 26)).eval (τ ++ [j, e0Of (M := M) (s := s) x ℓ H j]) =
      e0Of (M := M) (s := s) x ℓ H j := by
    simp only [Xp.eval_var]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hτl]
  split_ifs with hc
  · rw [Gn.out_blkGen hlen _ _ _ _ (bnd_var (show b + 26 < b + 27 by omega)) (bnd_gdX (by omega))
      (bnd_forkBlk hNb (by omega)), e26]
  · rw [Gn.out_blkGen hlen _ _ _ _ (bnd_var (show b + 26 < b + 27 by omega)) (bnd_gdX (by omega))
      (bnd_assignBlk hNb (by omega)), e26]

/-- **The output of the schema enumerator, by stacks.** -/
theorem out_schEnumP_stks (hNb : NX.Bnd b) (hrb : rX.Bnd b) (hpb : p0X.Bnd b)
    (hEb : EcX.Bnd b) (ℓ : ℕ) (body : Gn) :
    (schEnumP M b SX HX RX NX rX p0X EcX body).out y ρ =
      (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).flatMap (body.out y) := by
  rw [schEnumP, Gn.out, out_cmdEnumP' hρ hHb hRb hH hR _ hSb hS hs,
    out_detGen hρ hNb hrb hpb hEb, schStksP, List.flatMap_append, List.flatMap_assoc]
  congr 1
  conv_lhs => rw [← map_fst_zipIdx' (cmdStksP M b HX RX ρ s H) 0, List.flatMap_map]
  refine List.flatMap_congr fun p hp => ?_
  have h := List.mem_zipIdx_iff_getElem?.mp hp
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp h
  rw [← hget]
  exact out_cmdBodyP hρ hHb hRb hSb hH hR hS hs hNb ℓ body hj

end Out

section Main

variable {x y : List Bool} {ρ : List ℕ} {b H ℓ : ℕ} {SX HX RX NX rX p0X EcX : Xp}
  (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
  (hR : RX.eval ρ = radix M H)
  (hNb : NX.Bnd b) (hN : NX.eval ρ = numLoc M H)
  (hrb : rX.Bnd b) (hr : rX.eval ρ = (verifierCmds' M x s ℓ H).length)
  (hpb : p0X.Bnd b) (hp : p0X.eval ρ = (Loc.code (Loc.query : Loc M H)).val)
  (hEb : EcX.Bnd b) (hE : EcX.eval ρ = ((verifierCmds' M x s ℓ H).map cmdSz).sum)
include hρ hHb hRb hH hR hNb hN hrb hr hpb hp hEb hE

lemma schStksP_forall₂ :
    List.Forall₂ (fun sc τ => τ.length = b + 37 ∧ τ.take b = ρ ∧
        SchRec M x s ℓ H sc (τ.drop (b + 28)))
      ((AP (ℓ := ℓ) (N := numLoc M H) Loc.code Loc.accept Loc.reject code_accept_ne_reject
        (verifierCmds' M x s ℓ H)).compiledSchemas (Loc.query : Loc M H).code (fun _ _ => 0))
      (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H) := by
  have hm := schemas_match (ℓ := ℓ) (Loc.code (M := M) (H := H)) Loc.accept Loc.reject
    code_accept_ne_reject (verifierCmds' M x s ℓ H) (Loc.query : Loc M H).code (fun _ _ => 0)
  refine (forall₂_comp hm (S := StkSch M x s ℓ H b ρ) ?_).imp ?_
  · rw [schStksP]
    refine List.rel_append (forall₂_flatMap ?_) ?_
    · have hF := forall₂_flip' (forall₂_mem_right
        (cmdStksP_forall₂ (x := x) (s := s) hρ hHb hRb hH hR ℓ))
      refine (forall₂_zipIdx_both hF 0).imp ?_
      rintro ⟨cmd, j⟩ ⟨τ, j'⟩ ⟨⟨hrel, hmem⟩, hjj⟩
      simp only at hjj
      subst hjj
      exact cmd_forall₂ hρ hNb hN hrel hmem j _
    · rw [detStks, queryGuard_zero]
      refine forall₂_stks (σ := ρ ++ List.replicate 27 0) (σ' := ρ) (by simp [hρ])
        (by simp [← hρ]) (g := fun _ v => decide (v = 0)) (gd := [3, 0, 0, 0])
        (Or.inr ⟨rfl, rfl⟩) rfl rfl
        (gadgetX p0X (const 0) (detX NX rX 0) (detX NX rX 1) (detX NX rX 2) (detX NX rX 3))
        (detN (N := numLoc M H) (verifierCmds' M x s ℓ H).length
          (Loc.code (Loc.query : Loc M H)).val) ?_ (EcX.eval ρ)
      rw [eval_gadgetX, detN]
      simp only [detX, Xp.eval_add, Xp.eval_mulC, Xp.eval_const, hN, hr, hp]
      rw [Nat.mul_comm 8]
  rintro sc τ ⟨⟨D, n⟩, hM, hl, ht, g, gd, hg, hD, hdrop⟩
  exact ⟨hl, ht, by rw [hdrop]; exact schRec_of hM hD hg⟩

lemma schStksP_idx :
    (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).map (·.getD (b + 27) 0) =
      List.range (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).length := by
  set lens := (verifierCmds' M x s ℓ H).map cmdSz with hlens
  have hF := cmdStksP_forall₂ (x := x) (s := s) hρ hHb hRb hH hR ℓ
  have hC : (cmdStksP M b HX RX ρ s H).map (szAt b) = lens :=
    forall₂_map_eq (fun τ cmd h => szAt_of_stkCmd h) hF
  have hblk : ∀ p ∈ (cmdStksP M b HX RX ρ s H).zipIdx,
      (cmdSchStks NX b p.1 p.2 (e0Of (M := M) (s := s) x ℓ H p.2)).map (·.getD (b + 27) 0) =
        (List.range (szAt b p.1)).map ((lens.take p.2).sum + ·) := by
    intro p hp
    have hm : p.1 ∈ cmdStksP M b HX RX ρ s H :=
      List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
    obtain ⟨cmd, -, hrel⟩ := forall₂_exists_of_mem_left hF hm
    have hσ : (p.1 ++ [p.2, e0Of (M := M) (s := s) x ℓ H p.2]).length = b + 27 := by
      simp [hrel.1]
    have he0 : e0Of (M := M) (s := s) x ℓ H p.2 = (lens.take p.2).sum := by
      rw [e0Of, hlens, List.map_take]
    rw [cmdSchStks, map_getD_blk hσ, he0]
    unfold szAt
    split_ifs <;> rfl
  have hb := flatMap_blocks lens 0
  simp only [zero_add] at hb
  have hdet : (detStks NX rX p0X EcX ρ).map (·.getD (b + 27) 0) =
      (List.range 4).map (lens.sum + ·) := by
    rw [detStks, map_getD_blk (σ := ρ ++ List.replicate 27 0) (n := b + 27) (by simp [hρ]), hE]
    rfl
  have hmap : (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).map (·.getD (b + 27) 0) =
      List.range (lens.sum + 4) := by
    rw [schStksP, List.map_append, List.map_flatMap, List.flatMap_congr hblk, hdet]
    have : ((cmdStksP M b HX RX ρ s H).zipIdx.flatMap fun p =>
        (List.range (szAt b p.1)).map ((lens.take p.2).sum + ·)) =
        ((cmdStksP M b HX RX ρ s H).map (szAt b)).zipIdx.flatMap fun p =>
          (List.range p.1).map ((lens.take p.2).sum + ·) := by
      rw [List.zipIdx_map, List.flatMap_map]; rfl
    rw [this, hC, hb, List.range_add, List.map_id']
  have hlen := congrArg List.length hmap
  simp only [List.length_map, List.length_range] at hlen
  rw [hmap, hlen]

/-- **The schema enumerator** for a runtime number of blocks. -/
theorem out_schEnumP (hSb : SX.Bnd b) (hS : SX.eval ρ = s) (hs : 1 ≤ s) (body : Gn) :
    List.Forall₂ (fun sc τ => τ.length = b + 37 ∧ τ.take b = ρ ∧
        SchRec M x s ℓ H sc (τ.drop (b + 28)))
      ((AP (ℓ := ℓ) (N := numLoc M H) Loc.code Loc.accept Loc.reject code_accept_ne_reject
        (verifierCmds' M x s ℓ H)).compiledSchemas (Loc.query : Loc M H).code (fun _ _ => 0))
      (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H) ∧
    (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).map (·.getD (b + 27) 0) =
      List.range (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).length ∧
    (schEnumP M b SX HX RX NX rX p0X EcX body).out y ρ =
      (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).flatMap (body.out y) :=
  ⟨schStksP_forall₂ hρ hHb hRb hH hR hNb hN hrb hr hpb hp hEb hE,
    schStksP_idx hρ hHb hRb hH hR hNb hN hrb hr hpb hp hEb hE,
    out_schEnumP_stks hρ hHb hRb hSb hH hR hS hs hNb hrb hpb hEb ℓ body⟩

end Main

end Lax119563Proofs.Reduction

end Reduction_PkSch

/-! ### Formerly `Lax119563Proofs.Reduction.PkPass` -/

section Reduction_PkPass

/-!
# Infrastructure of the packed system generator

The generator of `PkSys` runs on `19` globals (levels `0 … 18`):
`|y|, n, h, s, Λ, log₂(n + 1), ⌈(h + 2)/s⌉, ℓ, H, R, N, r, Ec, p0, acc, E, W, det, 2^ℓ`
where `y` is the (preprocessed) input and `Λ ≥ (s + 1) ℓ` bounds the bit positions
`i ℓ + t` in an address. `GlobP` records the values read by the body.

* `schEnum_ctxP`: the schema enumerator `schEnumP` as a loop over schema indices;
* `violGenP`: the domain test of a schema at a coordinate (emits nothing iff the coordinate
  lies in the domain), with the number `s` of data blocks and the bit position `i ℓ` of block
  `i` given by expressions (`violGenP_nil_iff_mem`);
* `xorFields_testBit`: the bits of the checksum shift as parities.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

/-! ## Globals -/

abbrev qS : Xp := var 3
abbrev qΛ : Xp := var 4
abbrev qℓ : Xp := var 7
abbrev qH : Xp := var 8
abbrev qR : Xp := var 9
abbrev qN : Xp := var 10
abbrev qr : Xp := var 11
abbrev qEc : Xp := var 12
abbrev qp0 : Xp := var 13
abbrev qacc : Xp := var 14
abbrev qE : Xp := var 15
abbrev qW : Xp := var 16
abbrev qdet : Xp := var 17
abbrev qP : Xp := var 18

/-- The globals read by the body of the packed generator. -/
structure GlobP (M : Machine) (x : List Bool) (s ℓ H : ℕ) (ρ : List ℕ) : Prop where
  len : 19 ≤ ρ.length
  en : ρ.getD 1 0 = x.length
  eS : ρ.getD 3 0 = s
  eΛ : (s + 1) * ℓ ≤ ρ.getD 4 0
  eℓ : ρ.getD 7 0 = ℓ
  eH : ρ.getD 8 0 = H
  eR : ρ.getD 9 0 = radix M H
  eN : ρ.getD 10 0 = numLoc M H
  er : ρ.getD 11 0 = (verifierCmds' M x s ℓ H).length
  eEc : ρ.getD 12 0 = ((verifierCmds' M x s ℓ H).map cmdSz).sum
  ep0 : ρ.getD 13 0 = (Loc.code (Loc.query : Loc M H)).val
  eacc : ρ.getD 14 0 = (Loc.code (Loc.accept : Loc M H)).val
  eE : ρ.getD 15 0 = (Iv M x s ℓ H).schemas.length
  eW : ρ.getD 16 0 = (Iv M x s ℓ H).numLocations
  edet : ρ.getD 17 0 = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3
  eP : ρ.getD 18 0 = 2 ^ ℓ

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

namespace GlobP

lemma of_prefix {ρ ρ' : List ℕ} (h : GlobP M x s ℓ H ρ) (hl : ρ.length ≤ ρ'.length)
    (hg : ∀ i < 19, ρ'.getD i 0 = ρ.getD i 0) : GlobP M x s ℓ H ρ' := by
  obtain ⟨h0, hn, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨by omega, by rw [hg 1 (by omega)]; exact hn, by rw [hg 3 (by omega)]; exact h1, by rw [hg 4 (by omega)]; exact h2,
    by rw [hg 7 (by omega)]; exact h3, by rw [hg 8 (by omega)]; exact h4,
    by rw [hg 9 (by omega)]; exact h5, by rw [hg 10 (by omega)]; exact h6,
    by rw [hg 11 (by omega)]; exact h7, by rw [hg 12 (by omega)]; exact h8,
    by rw [hg 13 (by omega)]; exact h9, by rw [hg 14 (by omega)]; exact h10,
    by rw [hg 15 (by omega)]; exact h11, by rw [hg 16 (by omega)]; exact h12,
    by rw [hg 17 (by omega)]; exact h13, by rw [hg 18 (by omega)]; exact h14⟩

lemma append {ρ : List ℕ} (h : GlobP M x s ℓ H ρ) (l : List ℕ) : GlobP M x s ℓ H (ρ ++ l) :=
  h.of_prefix (by simp) fun i hi => List.getD_append _ _ _ _ (by have := h.len; omega)

lemma of_take {ρ τ : List ℕ} {b : ℕ} (h : GlobP M x s ℓ H ρ) (hρ : ρ.length = b)
    (ht : τ.take b = ρ) : GlobP M x s ℓ H τ := by
  have hb := hρ ▸ h.len
  have hlen : ρ.length ≤ τ.length := by
    have := congrArg List.length ht; simp at this; omega
  refine h.of_prefix hlen fun i hi => ?_
  rw [← ht, getD_take' (by omega)]

variable {ρ : List ℕ} (h : GlobP M x s ℓ H ρ)
include h

lemma vS : qS.eval ρ = s := h.eS
lemma vℓ : qℓ.eval ρ = ℓ := h.eℓ
lemma vH : qH.eval ρ = H := h.eH
lemma vR : qR.eval ρ = radix M H := h.eR
lemma vN : qN.eval ρ = numLoc M H := h.eN
lemma vr : qr.eval ρ = (verifierCmds' M x s ℓ H).length := h.er
lemma vEc : qEc.eval ρ = ((verifierCmds' M x s ℓ H).map cmdSz).sum := h.eEc
lemma vp0 : qp0.eval ρ = (Loc.code (Loc.query : Loc M H)).val := h.ep0
lemma vacc : qacc.eval ρ = (Loc.code (Loc.accept : Loc M H)).val := h.eacc
lemma vE : qE.eval ρ = (Iv M x s ℓ H).schemas.length := h.eE
lemma vW : qW.eval ρ = (Iv M x s ℓ H).numLocations := h.eW
lemma vdet : qdet.eval ρ = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 := h.edet
lemma vP : qP.eval ρ = 2 ^ ℓ := h.eP

end GlobP

lemma bnd_globP {k b : ℕ} (hk : k < 19) (hb : 19 ≤ b) : (Xp.var k).Bnd b :=
  show k < b by omega

/-! ## The schema enumerator as a loop over schema indices -/

/-- **The schema enumerator**, indexed by schemas. -/
theorem schEnum_ctxP {ρ : List ℕ} {b : ℕ} (hρ : ρ.length = b) (hG : GlobP M x s ℓ H ρ)
    (hs : 1 ≤ s) :
    ∃ T : ℕ → List ℕ, (∀ (body : Gn) (y : List Bool),
        (schEnumP M b qS qH qR qN qr qp0 qEc body).out y ρ =
          (List.range (Iv M x s ℓ H).schemas.length).flatMap fun e => body.out y (T e)) ∧
      ∀ e (he : e < (Iv M x s ℓ H).schemas.length),
        SchCtx M x s ℓ H b ρ (T e) e (Iv M x s ℓ H).schemas[e] := by
  have hb : 19 ≤ b := hρ ▸ hG.len
  have hS := fun (body : Gn) (y : List Bool) => out_schEnumP (M := M) (s := s) (x := x)
    (y := y) (ℓ := ℓ) (H := H) hρ (bnd_globP (by omega) hb) (bnd_globP (by omega) hb) hG.vH
    hG.vR (bnd_globP (by omega) hb) hG.vN (bnd_globP (by omega) hb) hG.vr
    (bnd_globP (by omega) hb) hG.vp0 (bnd_globP (by omega) hb) hG.vEc
    (bnd_globP (by omega) hb) hG.vS hs body
  obtain ⟨hF, hidx, -⟩ := hS Gn.skip []
  have hlen := hF.length_eq
  refine ⟨fun e => (schStksP M s b qH qR qN qr qp0 qEc x ρ ℓ H).getD e [], fun body y => ?_,
    fun e he => ?_⟩
  · rw [(hS body y).2.2, flatMap_eq_range _ [], ← hlen]
    rfl
  · have he' : e < (schStksP M s b qH qR qN qr qp0 qEc x ρ ℓ H).length := by
      rw [← hlen]; exact he
    have hrel := forall₂_getD [] hF e he
    exact ⟨hrel.1, hrel.2.1, getD_of_map_eq_range _ [] hidx he', hrel.2.2⟩

/-! ## The domain test -/

/-- **The domain violations** (at depth `d`), with the number of data blocks `sX` and the
bit position `iℓX` of block `iX`. -/
def violGenP (d : ℕ) (sX iX iℓX vX xbX gkX g1X g2X g3X ℓX HX : Xp) : Gn :=
  Gn.when (Xp.not (eq iX sX))
    (.ite (eq gkX (const 0))
      (.loop g2X (Gn.when (fieldBadX iℓX g1X (var (d + 1)) vX g3X ℓX) (.emit (const 0))))
      (.ite (eq gkX (const 1))
        (Gn.when (Xp.not (or (and (eq iX (const 0)) (eq (initCVX g1X vX xbX) g2X))
            (and (Xp.not (eq iX (const 0))) (eq vX (fieldX iℓX ℓX HX)))))
          (.emit (const 0)))
        (.ite (eq gkX (const 2))
          (Gn.when (Xp.not (or (Xp.not (eq iX g1X)) (Xp.not (eq vX (fieldX iℓX ℓX HX)))))
            (.emit (const 0)))
          (Gn.when (Xp.not (eq vX (const 0))) (.emit (const 0))))))

theorem violGenP_out_eq_nil_iff {y : List Bool} {τ : List ℕ} {d : ℕ}
    {sX iX iℓX vX xbX gkX g1X g2X g3X ℓX HX : Xp} (hτ : τ.length = d)
    (hb : ∀ e ∈ [iX, iℓX, vX, xbX, gkX, g1X, g2X, g3X, ℓX, HX], e.Bnd d)
    {i v gk g1 g2 g3 : ℕ} (hsX : sX.eval τ = s) (hi : iX.eval τ = i)
    (hiℓ : iℓX.eval τ = i * ℓ) (hv : vX.eval τ = v)
    (hxb : xbX.eval τ = inBit x v) (hgk : gkX.eval τ = gk) (hg1 : g1X.eval τ = g1)
    (hg2 : g2X.eval τ = g2) (hg3 : g3X.eval τ = g3) (hℓX : ℓX.eval τ = ℓ) (hHX : HX.eval τ = H)
    (hℓ : 0 < ℓ) :
    (violGenP d sX iX iℓX vX xbX gkX g1X g2X g3X ℓX HX).out y τ = [] ↔
      (i = s ∨ gEval x ℓ H [gk, g1, g2, g3] i v = true) := by
  have hfx : (fieldX iℓX ℓX HX).eval τ = field (2 ^ H) (i * ℓ) ℓ := by
    rw [eval_fieldX, hiℓ, hℓX, hHX]
  have hB : ∀ e ∈ [iX, iℓX, vX, xbX, gkX, g1X, g2X, g3X, ℓX, HX], e.Bnd d := hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hB
  obtain ⟨bi, biℓ, bv, -, -, bg1, -, bg3, bℓ, -⟩ := hB
  have hns : (Xp.not (eq iX sX)).eval τ = if ¬ i = s then 1 else 0 :=
    Xp.eval_not' (by rw [Xp.eval_eq, hi, hsX])
  have e0 : (eq gkX (const 0)).eval τ = if gk = 0 then 1 else 0 := by
    rw [Xp.eval_eq, hgk, Xp.eval_const]
  have e1 : (eq gkX (const 1)).eval τ = if gk = 1 then 1 else 0 := by
    rw [Xp.eval_eq, hgk, Xp.eval_const]
  have e2 : (eq gkX (const 2)).eval τ = if gk = 2 then 1 else 0 := by
    rw [Xp.eval_eq, hgk, Xp.eval_const]
  have hbad : ∀ t, (fieldBadX iℓX g1X (var (d + 1)) vX g3X ℓX).eval (τ ++ [g2, t]) =
      if (i * ℓ ≤ g1 + t ∧ g1 + t < i * ℓ + ℓ) ∧
        ¬ v * 2 ^ (i * ℓ) / 2 ^ (g1 + t) % 2 = g3 / 2 ^ t % 2 then 1 else 0 := by
    intro t
    have hev : ∀ e : Xp, e.Bnd d → e.eval (τ ++ [g2, t]) = e.eval τ :=
      fun e he => Xp.eval_append hτ _ he
    have ht' : (var (d + 1)).eval (τ ++ [g2, t]) = t := by
      simp only [Xp.eval_var]
      rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hτ]
    have hm : iℓX.eval (τ ++ [g2, t]) = i * ℓ := by rw [hev _ biℓ, hiℓ]
    have hk : (add g1X (var (d + 1))).eval (τ ++ [g2, t]) = g1 + t := by
      rw [Xp.eval_add, hev _ bg1, ht', hg1]
    refine Xp.eval_and' (Xp.eval_and' ?_ ?_) (Xp.eval_not' ?_)
    · rw [Xp.eval_le, hm, hk]
    · rw [Xp.eval_lt_eq, hk, Xp.eval_add, hm, hev _ bℓ, hℓX]
    · rw [Xp.eval_eq]
      simp only [Xp.eval_odd, Xp.eval_shr, Xp.eval_shl, hm, hk, ht', hev _ bv, hev _ bg3, hv, hg3]
  have hhit : (Xp.not (or (and (eq iX (const 0)) (eq (initCVX g1X vX xbX) g2X))
      (and (Xp.not (eq iX (const 0))) (eq vX (fieldX iℓX ℓX HX))))).eval τ =
      if ¬ ((i = 0 ∧ initCV x g1 v = g2) ∨ (¬ i = 0 ∧ v = field (2 ^ H) (i * ℓ) ℓ)) then 1
        else 0 :=
    Xp.eval_not' (Xp.eval_or' (Xp.eval_and' (by rw [Xp.eval_eq, hi, Xp.eval_const])
        (by rw [Xp.eval_eq, eval_initCVX hg1 hv hxb, hg2]))
      (Xp.eval_and' (Xp.eval_not' (by rw [Xp.eval_eq, hi, Xp.eval_const]))
        (by rw [Xp.eval_eq, hv, hfx])))
  have hmiss : (Xp.not (or (Xp.not (eq iX g1X)) (Xp.not (eq vX (fieldX iℓX ℓX HX))))).eval τ =
      if ¬ (¬ i = g1 ∨ ¬ v = field (2 ^ H) (i * ℓ) ℓ) then 1 else 0 :=
    Xp.eval_not' (Xp.eval_or' (Xp.eval_not' (by rw [Xp.eval_eq, hi, hg1]))
      (Xp.eval_not' (by rw [Xp.eval_eq, hv, hfx])))
  have hz : (Xp.not (eq vX (const 0))).eval τ = if ¬ v = 0 then 1 else 0 :=
    Xp.eval_not' (by rw [Xp.eval_eq, hv, Xp.eval_const])
  simp only [violGenP, Gn.out_when, Gn.out, hns, e0, e1, e2, hhit, hmiss, hz, hg2, hbad]
  by_cases his : i = s
  · simp [his]
  · rcases (show gk = 0 ∨ gk = 1 ∨ gk = 2 ∨ 3 ≤ gk by omega) with h0 | h1 | h2 | h3
    · subst h0
      simp only [his, gEval, List.getD_cons_zero, List.getD_cons_succ, fieldOK_iff hℓ]
      simp only [not_false_eq_true, if_true, ne_eq, one_ne_zero, false_or,
        List.flatMap_eq_nil_iff, List.mem_range, ite_eq_right_iff, reduceCtorEq, imp_false,
        Decidable.not_not, if_false]
      refine forall_congr' fun t => imp_congr_right fun _ => ?_
      rw [and_assoc]
    · subst h1
      have c0 : (if ¬i = s then 1 else 0) ≠ 0 := by simp [his]
      rw [if_pos c0, if_neg (by simp), if_pos (by simp)]
      have : gEval x ℓ H [1, g1, g2, g3] i v = (if i = 0 then decide (initCV x g1 v = g2)
          else decide (v = field (2 ^ H) (i * ℓ) ℓ)) := rfl
      rw [this]
      generalize field (2 ^ H) (i * ℓ) ℓ = F
      generalize initCV x g1 v = C
      by_cases hi0 : i = 0 <;> by_cases hc : C = g2 <;> by_cases hF : v = F <;>
        simp [his, hi0, hc, hF] <;> omega
    · subst h2
      have c0 : (if ¬i = s then 1 else 0) ≠ 0 := by simp [his]
      rw [if_pos c0, if_neg (by simp), if_neg (by simp), if_pos (by simp)]
      have : gEval x ℓ H [2, g1, g2, g3] i v =
          (if i = g1 then decide (v ≠ field (2 ^ H) (i * ℓ) ℓ) else true) := rfl
      rw [this]
      generalize field (2 ^ H) (i * ℓ) ℓ = F
      by_cases hig : i = g1 <;> by_cases hF : v = F <;> simp [his, hig, hF] <;> omega
    · have : gEval x ℓ H [gk, g1, g2, g3] i v = decide (v = 0) := by
        unfold gEval
        simp only [List.getD_cons_zero]
        rcases gk with _ | _ | _ | gk
        · omega
        · omega
        · omega
        · rfl
      rw [this]
      have g0 : gk ≠ 0 := by omega
      have g1' : gk ≠ 1 := by omega
      have g2' : gk ≠ 2 := by omega
      by_cases hv0 : v = 0 <;> simp [his, hv0, g0, g1', g2']

/-- **The domain test on a schema stack.** -/
theorem violGenP_nil_iff_mem {y : List Bool} {N b d : ℕ}
    {sc : Schema (s + 1) ℓ N} {τ σ : List ℕ}
    (hτ : τ.length = b + 37) (hrec : SchRec M x s ℓ H sc (τ.drop (b + 28)))
    (hσ : σ.length = d) (hστ : σ.take (b + 37) = τ) (hd : b + 37 ≤ d)
    {sX iX iℓX vX xbX ℓX HX : Xp} (hb : ∀ e ∈ [iX, iℓX, vX, xbX, ℓX, HX], e.Bnd d)
    (c : Coord (s + 1) ℓ) (hsX : sX.eval σ = s)
    (hi : iX.eval σ = c.1.val) (hiℓ : iℓX.eval σ = c.1.val * ℓ) (hv : vX.eval σ = regVal c.2)
    (hxb : xbX.eval σ = inBit x (regVal c.2)) (hℓX : ℓX.eval σ = ℓ) (hHX : HX.eval σ = H)
    (hℓ : 0 < ℓ) :
    (violGenP d sX iX iℓX vX xbX (var (b + 33)) (var (b + 34)) (var (b + 35)) (var (b + 36))
      ℓX HX).out y σ = [] ↔ c ∈ sc.domain := by
  have hg : ∀ k < 4, (var (b + 33 + k)).eval σ = ((τ.drop (b + 28)).drop 5).getD k 0 := by
    intro k hk
    rw [getD_drop', getD_drop', Xp.eval_var, ← hστ, getD_take' (by omega)]
    congr 1; omega
  have hl : ((τ.drop (b + 28)).drop 5).length = 4 := by simp [hτ]
  have h4 := eq_of_length_four hl
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  rw [violGenP_out_eq_nil_iff hσ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, show b + 33 < d by omega,
        show b + 34 < d by omega, show b + 35 < d by omega, show b + 36 < d by omega,
        hb.2.2.2.2.1, hb.2.2.2.2.2⟩)
    hsX hi hiℓ hv hxb (hg 0 (by omega)) (hg 1 (by omega)) (hg 2 (by omega)) (hg 3 (by omega))
    hℓX hHX hℓ, mem_domain_of_schRec hrec, ← h4]

/-! ## The checksum shift bit by bit -/

/-- The number of blocks `i < k` whose field has bit `t` set. -/
def cntBits (ℓ m t : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cntBits ℓ m t k + (if m.testBit (k * ℓ + t) then 1 else 0)

lemma xorFields_testBit (m : ℕ) {t : ℕ} (ht : t < ℓ) :
    ∀ k, (xorFields ℓ k m).testBit t = decide (cntBits ℓ m t k % 2 = 1)
  | 0 => by simp [xorFields, cntBits]
  | k + 1 => by
    rw [xorFields, Nat.testBit_xor, xorFields_testBit m ht k, testBit_field, cntBits]
    simp only [ht, decide_true, Bool.true_and, Nat.add_comm t]
    by_cases hb : m.testBit (k * ℓ + t) <;> simp [hb, Nat.add_mod] <;>
      rcases Nat.mod_two_eq_zero_or_one (cntBits ℓ m t k) with h | h <;> simp [h]

lemma cntBits_eq (ℓ m t : ℕ) : ∀ k, cntBits ℓ m t k =
    ((List.range k).flatMap fun i => if m.testBit (i * ℓ + t) then [0] else []).length
  | 0 => rfl
  | k + 1 => by
    rw [cntBits, cntBits_eq ℓ m t k, List.range_succ, List.flatMap_append, List.length_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    split_ifs <;> simp

end Lax119563Proofs.Reduction

end Reduction_PkPass

/-! ### Formerly `Lax119563Proofs.Reduction.Prelude` -/

section Reduction_Prelude

/-!
# Facts for the prelude

Lemmas used to compute the globals of the packed generator (`Reduction/PkPre`): outputs of
`bind` and `count` steps (`out_bind_step`, `out_count_step`), the number of locations of the
compiled verifier program (`Iv_numLocations`), the codes of `query` (`2`) and `accept` (`0`)
(`code_query_val`, `code_accept_val`) and well-formedness of `Gn.len` (`Gn.wfx_len`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

namespace Gn

end Gn

/-! ## Steps -/

section Steps

variable {x : List Bool} {G : List ℕ}

lemma take_succ_getD {k : ℕ} (hk : k < G.length) : G.take k ++ [G.getD k 0] = G.take (k + 1) := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
  rfl

lemma out_bind_step {k : ℕ} (hk : k < G.length) {e : Xp} {g : Gn}
    (he : e.eval (G.take k) = G.getD k 0) :
    (Gn.bind e g).out x (G.take k) = g.out x (G.take (k + 1)) := by
  simp only [Gn.out, he, take_succ_getD hk]

lemma out_count_step {k : ℕ} (hk : k < G.length) {g h : Gn}
    (hl : (g.out x (G.take k ++ [0])).length = G.getD k 0) :
    (Gn.count g h).out x (G.take k) = h.out x (G.take (k + 1)) := by
  simp only [Gn.out, hl, take_succ_getD hk]

lemma getD_take_lt {l : List ℕ} {i k : ℕ} (h : i < k) : (l.take k).getD i 0 = l.getD i 0 :=
  getD_take' h

lemma getD_take_app {l : List ℕ} {i k : ℕ} (h : i < k) (hk : k ≤ l.length) (a : ℕ) :
    (l.take k ++ [a]).getD i 0 = l.getD i 0 := by
  rw [List.getD_append _ _ _ _ (by simp; omega), getD_take' h]

end Steps

/-! ## Values -/

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

lemma Iv_numLocations :
    (Iv M x s ℓ H).numLocations = numLoc M H + (verifierCmds' M x s ℓ H).length * 8 + 4 := by
  have hc : (APv M x s ℓ H).commands.length = (verifierCmds' M x s ℓ H).length := by
    simp only [AP_commands]; exact List.length_map _
  show (APv M x s ℓ H).numLocations + (APv M x s ℓ H).commands.length * 8 + 4 = _
  rw [hc]
  rfl

lemma code_query_val : (Loc.code (Loc.query : Loc M H)).val = 2 := by
  simp [Loc.code, Loc.tuple, pack]

lemma code_accept_val : (Loc.code (Loc.accept : Loc M H)).val = 0 := by
  simp [Loc.code, Loc.tuple, pack]

lemma sum_map_forall₂ {α β : Type} {R : α → β → Prop} {f : α → ℕ} {g : β → ℕ} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ a b, R a b → f a = g b) →
      (l₁.map f).sum = (l₂.map g).sum
  | _, _, .nil, _ => rfl
  | _, _, .cons h t, hf => by
    simp only [List.map_cons, List.sum_cons, hf _ _ h, sum_map_forall₂ t hf]

lemma length_flatMap_emit {α : Type} (l : List α) (f : α → List ℕ) (hf : ∀ a, (f a).length = 1) :
    (l.flatMap f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hf a, ih]; omega

/-! ## Fits, cost and well-formedness -/

lemma Gn.wfx_len {g : Gn} (h : WFX g) : WFX (len g) := h

end Lax119563Proofs.Reduction

end Reduction_Prelude

/-! ### Formerly `Lax119563Proofs.Reduction.Packed` -/

section Reduction_Packed

/-!
# The packed size of the time simulation system

The implicit parity system `Iv M x s ℓ H` (the compiled code-ordered verifier program, the
system that the reduction generator emits) has, under the standing hypotheses
`Params x s ℓ H` (`H + 2 ≤ s ℓ`, `0 < ℓ ≤ H`, `|x| < 2^ℓ`) and `s ≤ H + 2`,

* `O_M((H + 1)^2)` locations: the verifier locations are numbered densely enough
  (`numLoc M H = 16 cM^3 (H + 1 + cM)^2`, only the two depth fields `d, u` grow with `H`),
  and there are `O_M((H + 1)^2)` commands, each with at most eight private locations;
* `O_M((H + 1)^2)` schemas (at most nine per command, plus four);
* size parameter `S ≤ C_M (s + 1)^2 2^ℓ (ℓ + 1) (H + 1)^2`, from
  `S = O((s+1) 2^ℓ w + (s+1)^2 2^ℓ ℓ (r + 1))` (`sizeParameter_compile_le`).

The commands: every location has at most `movBound0 M` moves except the root cells
`cell 0 0 ν c`, which have `s` more (the tests `missGuard i`, one per register); there are
`(tapes + 1) · 2 (symbols + 3)` root cells and `s ≤ H + 2`. All constants depend on `M` only.

Correctness: if `M` halts on `x` within `2^H` steps, the system has a conflict iff `M`
accepts `x` (`verifier_accepts_iff`, `compile_accepts`, `conflictRound_compile_lt_top_iff`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563.MatrixCompiler

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

/-! ## Counting commands -/

/-- The root cells `cell 0 0 ν c`. -/
def rootLocs (M : Machine) (H : ℕ) : List (Loc M H) :=
  (List.finRange (M.tapes + 1) ×ˢ allCV M).map fun a => Loc.cell 0 0 a.1 a.2

lemma length_rootLocs : (rootLocs M H).length = (M.tapes + 1) * (2 * (M.symbols + 3)) := by
  simp [rootLocs, allCV, allBool, List.length_product]; ring

lemma mem_rootLocs_of_rootCount {L : Loc M H} (h : L.rootCount = 1) : L ∈ rootLocs M H := by
  cases L with
  | cell d θ ν c =>
    simp only [Loc.rootCount] at h
    split_ifs at h with hc
    have hd : d = 0 := Fin.ext hc.2
    have hθ : θ = 0 := Fin.ext hc.1
    rw [hd, hθ]
    exact List.mem_map.mpr ⟨(ν, c), List.mem_product.mpr ⟨List.mem_finRange _, mem_allCV c⟩, rfl⟩
  | _ => simp [Loc.rootCount] at h

lemma nodup_locsByCode : (locsByCode M H).Nodup := by
  refine (List.nodup_range).filterMap ?_
  intro a a' b ha ha'
  rw [← code_of_decodeLoc (Option.mem_def.mp ha), ← code_of_decodeLoc (Option.mem_def.mp ha')]

lemma sum_rootCount_eq (l : List (Loc M H)) :
    (l.map Loc.rootCount).sum = (l.filter fun L => decide (L.rootCount = 1)).length := by
  induction l with
  | nil => rfl
  | cons L l ih =>
    have := L.rootCount_le_one
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons]
    by_cases h : L.rootCount = 1
    · simp [h]; omega
    · have h0 : L.rootCount = 0 := by omega
      simp [h0]

lemma sum_rootCount_le {l : List (Loc M H)} (hl : l.Nodup) :
    (l.map Loc.rootCount).sum ≤ (M.tapes + 1) * (2 * (M.symbols + 3)) := by
  rw [sum_rootCount_eq, ← length_rootLocs (H := H)]
  refine ((hl.filter _).subperm fun L hL => ?_).length_le
  exact mem_rootLocs_of_rootCount (by simpa using (List.mem_filter.mp hL).2)

/-- The number of root cells. -/
def numRoot (M : Machine) : ℕ := (M.tapes + 1) * (2 * (M.symbols + 3))

/-- The commands: `movBound0 M` per location and `s` more per root cell. -/
lemma verifierCmds'_length_le :
    (verifierCmds' M x s ℓ H).length ≤ movBound0 M * numLoc M H + s * numRoot M := by
  have hlen : (verifierCmds' M x s ℓ H).length =
      ((locsByCode M H).map fun L => (moves M x s ℓ H L).length).sum := by
    simp [verifierCmds', progCmds, List.length_flatMap]
  rw [hlen]
  have h1 : ((locsByCode M H).map fun L => (moves M x s ℓ H L).length).sum ≤
      ((locsByCode M H).map fun L => movBound0 M + L.rootCount * s).sum :=
    List.sum_le_sum fun L _ => moves_length_le' x s ℓ L
  have h2 : ((locsByCode M H).map fun L => movBound0 M + L.rootCount * s).sum =
      movBound0 M * (locsByCode M H).length + ((locsByCode M H).map Loc.rootCount).sum * s := by
    rw [List.sum_map_add, List.sum_map_mul_right]
    simp [Nat.mul_comm]
  have h3 := sum_rootCount_le (M := M) (H := H) nodup_locsByCode
  have h4 : movBound0 M * (locsByCode M H).length ≤ movBound0 M * numLoc M H :=
    Nat.mul_le_mul_left _ length_locsByCode_le
  have h5 : ((locsByCode M H).map Loc.rootCount).sum * s ≤ s * numRoot M := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ h3
  omega

/-! ## The bounds -/

/-- `numLoc M H ≤ A_M (H + 1)^2`. -/
def locConst (M : Machine) : ℕ := 16 * cM M ^ 3 * (cM M + 1) ^ 2

lemma numLoc_le_sq : numLoc M H ≤ locConst M * (H + 1) ^ 2 := by
  rw [numLoc_eq, locConst]
  have : radix M H ≤ (cM M + 1) * (H + 1) := by unfold radix; nlinarith
  calc 16 * cM M ^ 3 * radix M H ^ 2 ≤ 16 * cM M ^ 3 * ((cM M + 1) * (H + 1)) ^ 2 := by gcongr
    _ = _ := by ring

/-- The constant of the command bound. -/
def cmdConst (M : Machine) : ℕ := movBound0 M * locConst M + 2 * numRoot M

lemma cmds_le_sq (hsH : s ≤ H + 2) :
    (verifierCmds' M x s ℓ H).length ≤ cmdConst M * (H + 1) ^ 2 := by
  have h := verifierCmds'_length_le (M := M) (x := x) (s := s) (ℓ := ℓ) (H := H)
  have h1 : movBound0 M * numLoc M H ≤ movBound0 M * (locConst M * (H + 1) ^ 2) :=
    Nat.mul_le_mul_left _ numLoc_le_sq
  have h2 : s * numRoot M ≤ 2 * numRoot M * (H + 1) ^ 2 := by
    have : s ≤ 2 * (H + 1) ^ 2 := by nlinarith
    calc s * numRoot M ≤ 2 * (H + 1) ^ 2 * numRoot M := Nat.mul_le_mul_right _ this
      _ = _ := by ring
  unfold cmdConst
  calc _ ≤ _ := h
    _ ≤ movBound0 M * (locConst M * (H + 1) ^ 2) + 2 * numRoot M * (H + 1) ^ 2 := by omega
    _ = _ := by ring

/-- Correctness of `Iv` for general parameters. -/
theorem Iv_conflict_iff (P : Params x s ℓ H) (hT : (runOn M x (2 ^ H)).answer.isSome) :
    (Iv M x s ℓ H).conflictRound < ⊤ ↔ Accepts M x := by
  have hmask : MasksBounded s ℓ (verifierCmds' M x s ℓ H) :=
    progCmds_masks P.hH fun src _ => moves_wf src
  refine (RegisterProgram.conflictRound_compile_lt_top_iff (APv M x s ℓ H)
    (Loc.query : Loc M H).code (fun _ _ => 0)).trans ?_
  rw [compile_accepts Loc.code_injective _ hmask, addr_zero]
  unfold verifierCmds'
  rw [verifier_accepts_iff P mem_locsByCode _ (by positivity)]
  rw [accepts_iff_answer hT]
  rfl

lemma packed_arith1 {N r A B E : ℕ} (hN : N ≤ A * E) (hr : r ≤ B * E) (hE : 1 ≤ E) :
    N + r * 8 + 4 ≤ 100 * (A + 9 * B + 4) * E := by nlinarith

lemma packed_arith2 {r B E A : ℕ} (hr : r ≤ B * E) (hE : 1 ≤ E) :
    9 * r + 4 ≤ 100 * (A + 9 * B + 4) * E := by nlinarith

/-- **Packed size of the time simulation system.** For a machine `M` there is a constant
`C` such that for every input `x` and parameters `s, ℓ, H` with `Params x s ℓ H`
(`H + 2 ≤ s ℓ`, `0 < ℓ ≤ H`, `|x| < 2^ℓ`) and `s ≤ H + 2`, the implicit parity system
`Iv M x s ℓ H` with `s + 1` blocks over `𝔽₂^ℓ` (the system emitted by the reduction
generator)
1. reaches a conflict iff `M` accepts `x`, provided `M` halts on `x` within `2^H` steps;
2. has at most `C (H + 1)^2` locations;
3. has at most `C (H + 1)^2` schemas;
4. has size parameter `S ≤ C (s + 1)^2 2^ℓ (ℓ + 1) (H + 1)^2`, i.e.
   `S = O(k w Q + k^2 Q ℓ e)` with `k = s + 1`, `Q = 2^ℓ`, `w, e = O((H+1)^2)`.
The constant `C` depends only on `M`. -/
theorem packed_bounds (M : Machine) : ∃ C : ℕ, ∀ (x : List Bool) (s ℓ H : ℕ),
    Params x s ℓ H → s ≤ H + 2 →
      ((runOn M x (2 ^ H)).answer.isSome → ((Iv M x s ℓ H).conflictRound < ⊤ ↔ Accepts M x)) ∧
      (Iv M x s ℓ H).numLocations ≤ C * (H + 1) ^ 2 ∧
      (Iv M x s ℓ H).schemas.length ≤ C * (H + 1) ^ 2 ∧
      matrixSize (Iv M x s ℓ H) ≤ C * (s + 1) ^ 2 * 2 ^ ℓ * (ℓ + 1) * (H + 1) ^ 2 := by
  refine ⟨100 * (locConst M + 9 * cmdConst M + 4), fun x s ℓ H P hsH => ?_⟩
  set A := locConst M
  set B := cmdConst M
  have hW := numLoc_le_sq (M := M) (H := H)
  have hr := cmds_le_sq (M := M) (x := x) (ℓ := ℓ) hsH
  set r := (verifierCmds' M x s ℓ H).length with hr_def
  set N := numLoc M H
  set E := (H + 1) ^ 2 with hE
  have hE1 : 1 ≤ E := Nat.one_le_pow _ _ (by omega)
  have hAE : A * E ≤ 100 * (A + 9 * B + 4) * E :=
    Nat.mul_le_mul_right _ (by omega)
  refine ⟨Iv_conflict_iff P, ?_, ?_, ?_⟩
  · rw [Iv_numLocations]
    exact packed_arith1 hW hr hE1
  · have hsch : (Iv M x s ℓ H).schemas.length ≤ 9 * (APv M x s ℓ H).commands.length + 4 :=
      RegisterProgram.compile_schemas_length _ _ _
    have hc : (APv M x s ℓ H).commands.length = r := by
      simp only [AP_commands]; exact List.length_map _
    rw [hc] at hsch
    exact hsch.trans (packed_arith2 hr hE1)
  · have hS := RegisterProgram.sizeParameter_compile_le (APv M x s ℓ H)
      (Loc.query : Loc M H).code (fun _ _ => 0) P.hℓ
    have hc : (APv M x s ℓ H).commands.length = r := by
      simp only [AP_commands]; exact List.length_map _
    have hn : (APv M x s ℓ H).numLocations = N := rfl
    rw [hc, hn] at hS
    change matrixSize (Iv M x s ℓ H) ≤ _ at hS
    refine hS.trans ?_
    set Q := 2 ^ ℓ
    set k := s + 1
    have hk : k ≤ k ^ 2 := by nlinarith
    have hl : 1 ≤ ℓ + 1 := by omega
    -- first term
    have t1 : k * Q * N ≤ A * (k ^ 2 * Q * (ℓ + 1) * E) := by
      calc k * Q * N ≤ k ^ 2 * Q * (A * E) := Nat.mul_le_mul (Nat.mul_le_mul_right _ hk) hW
        _ = A * (k ^ 2 * Q * 1 * E) := by ring
        _ ≤ A * (k ^ 2 * Q * (ℓ + 1) * E) := by gcongr
    have t2 : k ^ 2 * Q * ℓ * (r + 1) ≤ (B + 1) * (k ^ 2 * Q * (ℓ + 1) * E) := by
      have : r + 1 ≤ (B + 1) * E := by nlinarith
      calc k ^ 2 * Q * ℓ * (r + 1) ≤ k ^ 2 * Q * (ℓ + 1) * ((B + 1) * E) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) this
        _ = _ := by ring
    have : 100 * (k * Q * N + k ^ 2 * Q * ℓ * (r + 1)) ≤
        100 * (A + 9 * B + 4) * k ^ 2 * Q * (ℓ + 1) * E := by
      have e : 100 * (A + 9 * B + 4) * k ^ 2 * Q * (ℓ + 1) * E =
          100 * ((A + 9 * B + 4) * (k ^ 2 * Q * (ℓ + 1) * E)) := by ring
      rw [e]
      apply Nat.mul_le_mul_left
      have : (A + 9 * B + 4) * (k ^ 2 * Q * (ℓ + 1) * E) ≥
          A * (k ^ 2 * Q * (ℓ + 1) * E) + (B + 1) * (k ^ 2 * Q * (ℓ + 1) * E) := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    exact this

/-! ## The parameters of the packed representation

For a horizon exponent `h` and `s` data blocks, the width
`ℓ = max(⌈log₂(n + 2)⌉, ⌈(h + 2)/s⌉)` (`pkWidth`, as `packedWidth` of the concept
`PackedRepresentation`) and the horizon `H = max(h, ℓ) ≤ h + 1` satisfy `Params`, so the
bounds hold in terms of `h`. -/

/-- The block width `max(⌈log₂(n + 2)⌉, ⌈(h + 2)/s⌉)`. -/
def pkWidth (n h s : ℕ) : ℕ := max (Nat.clog 2 (n + 2)) ((h + 1 + s) / s)

/-- The simulated horizon `max(h, ℓ)`. -/
def pkHorizon (n h s : ℕ) : ℕ := max h (pkWidth n h s)

lemma pk_params {x : List Bool} {h s : ℕ} (hx : 2 ≤ x.length) (hh : 2 ≤ h)
    (hxh : x.length ≤ 2 ^ h) (hs : 2 ≤ s) :
    Params x s (pkWidth x.length h s) (pkHorizon x.length h s) ∧
      pkHorizon x.length h s ≤ h + 1 := by
  set n := x.length
  set ℓ := pkWidth n h s
  have hc2 : 2 ≤ Nat.clog 2 (n + 2) :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num; omega)
  have hcx : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) := Nat.le_pow_clog (by norm_num) _
  have hch : Nat.clog 2 (n + 2) ≤ h + 1 := by
    apply Nat.clog_le_of_le_pow
    have : 2 ≤ 2 ^ h := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]; omega
  have hq : (h + 1 + s) / s ≤ h + 1 := by
    apply Nat.div_le_of_le_mul; nlinarith
  have hsq : h + 2 ≤ s * ((h + 1 + s) / s) := by
    have := Nat.div_add_mod (h + 1 + s) s
    have := Nat.mod_lt (h + 1 + s) (show 0 < s by omega)
    omega
  have hℓ2 : 2 ≤ ℓ := le_trans hc2 (le_max_left _ _)
  have hℓh : ℓ ≤ h + 1 := max_le hch hq
  have hsl : s * ((h + 1 + s) / s) ≤ s * ℓ := Nat.mul_le_mul_left _ (le_max_right _ _)
  have hsl2 : 2 * ℓ ≤ s * ℓ := Nat.mul_le_mul_right _ hs
  have hxℓ : n < 2 ^ ℓ := lt_of_lt_of_le (by omega)
    (le_trans hcx (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)))
  refine ⟨⟨?_, by omega, le_max_right _ _, hxℓ⟩, max_le (by omega) hℓh⟩
  show max h ℓ + 2 ≤ s * ℓ
  rcases le_total h ℓ with hl | hl
  · rw [max_eq_right hl]; omega
  · rw [max_eq_left hl]; omega

/-- **The packed representation, size and correctness clauses.** For a machine `M` there is a
constant `C` such that for all inputs `x` with `2 ≤ |x| ≤ 2^h`, `2 ≤ h` and `2 ≤ s ≤ h + 2`,
the system `Iv M x s ℓ H` with `ℓ = pkWidth |x| h s` and `H = pkHorizon |x| h s` reaches a
conflict iff `M` accepts `x` (if `M` halts on `x` within `2^h` steps), and has at most
`C (h + 1)^2` locations and schemas and size parameter at most
`C (s + 1)^2 2^ℓ (ℓ + 1) (h + 1)^2`. -/
theorem packed_bounds_h (M : Machine) : ∃ C : ℕ, ∀ (x : List Bool) (h s : ℕ),
    2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s → s ≤ h + 2 →
      ((runOn M x (2 ^ h)).answer.isSome →
        ((Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s)).conflictRound < ⊤ ↔
          Accepts M x)) ∧
      (Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s)).numLocations ≤
        C * (h + 1) ^ 2 ∧
      (Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s)).schemas.length ≤
        C * (h + 1) ^ 2 ∧
      matrixSize (Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s)) ≤
        C * (s + 1) ^ 2 * 2 ^ pkWidth x.length h s * (pkWidth x.length h s + 1) *
          (h + 1) ^ 2 := by
  obtain ⟨C, hC⟩ := packed_bounds M
  refine ⟨4 * C, fun x h s hx hh hxh hs hsh => ?_⟩
  obtain ⟨P, hH⟩ := pk_params hx hh hxh hs
  set ℓ := pkWidth x.length h s
  set H := pkHorizon x.length h s
  have hhH : h ≤ H := le_max_left _ _
  obtain ⟨c1, c2, c3, c4⟩ := hC x s ℓ H P (by omega)
  have hsq : (H + 1) ^ 2 ≤ 4 * (h + 1) ^ 2 := by
    have : H + 1 ≤ 2 * (h + 1) := by omega
    calc (H + 1) ^ 2 ≤ (2 * (h + 1)) ^ 2 := Nat.pow_le_pow_left this 2
      _ = _ := by ring
  refine ⟨fun hT => c1 ?_, ?_, ?_, ?_⟩
  · have := runOn_halted x hT (2 ^ H - 2 ^ h)
    rw [Nat.add_sub_cancel' (Nat.pow_le_pow_right (by norm_num) hhH)] at this
    rw [this]; exact hT
  · calc _ ≤ C * (H + 1) ^ 2 := c2
      _ ≤ C * (4 * (h + 1) ^ 2) := Nat.mul_le_mul_left _ hsq
      _ = _ := by ring
  · calc _ ≤ C * (H + 1) ^ 2 := c3
      _ ≤ C * (4 * (h + 1) ^ 2) := Nat.mul_le_mul_left _ hsq
      _ = _ := by ring
  · calc _ ≤ C * (s + 1) ^ 2 * 2 ^ ℓ * (ℓ + 1) * (H + 1) ^ 2 := c4
      _ ≤ C * (s + 1) ^ 2 * 2 ^ ℓ * (ℓ + 1) * (4 * (h + 1) ^ 2) := Nat.mul_le_mul_left _ hsq
      _ = _ := by ring

end Lax119563Proofs.Reduction

end Reduction_Packed

/-! ### Formerly `Lax119563Proofs.Reduction.SysDesc` -/

section Reduction_SysDesc

/-!
# The description of the compiled system (mathematics)

Explicit forms of the parts of `systemDescription` for the compiled systems of register
programs, in terms that a generator can emit:
* `blockNum_eq_regVal`: block coordinates are numbered by `regVal`;
* `domainDescription_eq_domL`: the description of a coordinate domain is the list of the
  numbers `i 2^ℓ + v` of its members, enumerated by `i < k`, `v < 2^ℓ` (`domL`), preceded by its
  length; for the full domain this is `range (k 2^ℓ)`;
* `permDescription_of_permDesc`: the description of a permutation described by a mask;
* `schemaDescription_of_match`: the description of a schema matching its numbers;
* `locsDesc_compile`: the location part of the description of a compiled system.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563Proofs.Programs

variable {s ℓ : ℕ}

/-! ## Block coordinates -/

lemma map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n :=
  List.ext_getElem (by simp) fun i _ _ => by simp

lemma flatMap_finRange {β : Type} (n : ℕ) (f : ℕ → List β) :
    (List.finRange n).flatMap (fun v => f v.val) = (List.range n).flatMap f := by
  rw [← map_val_finRange, List.flatMap_map]


lemma ofBits_eq_sum : ∀ (n : ℕ) (f : ℕ → Bool),
    ofBits n f = ∑ t : Fin n, (f t).toNat * 2 ^ (t : ℕ)
  | 0, _ => rfl
  | n + 1, f => by
    rw [ofBits, ofBits_eq_sum n, Fin.sum_univ_succ, Nat.bit_val]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    rw [Finset.mul_sum]
    have : ∀ t : Fin n, 2 * ((f (t + 1)).toNat * 2 ^ (t : ℕ)) = (f (t + 1)).toNat * (2 ^ (t : ℕ) * 2) :=
      fun t => by ring
    simp only [this]
    ring

lemma blockNum_eq_regVal (b : BlockCoord ℓ) : blockNum b = regVal b := by
  rw [blockNum, regVal, ofBits_eq_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [dif_pos t.isLt]
  rcases zmod2_cases (b t) with h | h <;> simp [h] <;> rfl

lemma toBlk_regVal (b : BlockCoord ℓ) : toBlk ℓ (regVal b) = b :=
  regVal_injective (regVal_toBlk (regVal_lt b))

/-- The number of the coordinate `(i, toBlk v)`. -/
lemma coordNum_toBlk {k i v : ℕ} (hi : i < k) (hv : v < 2 ^ ℓ) :
    coordNum ((⟨i, hi⟩, toBlk ℓ v) : Coord k ℓ) = i * 2 ^ ℓ + v := by
  simp [coordNum, blockNum_eq_regVal, regVal_toBlk hv]

/-- The fixed-width binary digits `v_0, …, v_{ℓ-1}` of `v`. -/
def bitsL (ℓ v : ℕ) : List ℕ := (List.range ℓ).map fun t => if v.testBit t then 1 else 0

lemma blockDescription_eq (b : BlockCoord ℓ) : blockDescription b = bitsL ℓ (regVal b) := by
  refine List.ext_getElem (by simp [blockDescription, bitsL]) fun t h1 h2 => ?_
  have ht : t < ℓ := by simpa [blockDescription] using h1
  simp only [blockDescription, bitsL, List.getElem_map, List.getElem_finRange, List.getElem_range,
    regVal, testBit_ofBits, ht, decide_true, Bool.true_and, dif_pos]
  rcases zmod2_cases (b ⟨t, ht⟩) with h | h <;> simp [h] <;> rfl

lemma coordNumDescription_eq {i v : ℕ} (hv : v < 2 ^ ℓ) :
    coordNumDescription ℓ (i * 2 ^ ℓ + v) = i :: bitsL ℓ v := by
  have h1 : (i * 2 ^ ℓ + v) / 2 ^ ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv, zero_add]
  rw [coordNumDescription, h1, bitsL]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [List.mem_range] at ht
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hv, if_pos ht]

/-! ## Coordinate domains -/

lemma range_mul_flatMap {β : Type} (E N : ℕ) (g : ℕ → List β) :
    (List.range (E * N)).flatMap g =
      (List.range E).flatMap fun e => (List.range N).flatMap fun σ => g (e * N + σ) := by
  rw [Nat.mul_comm, Gn.flatMap_range_mul]
  refine List.flatMap_congr fun e _ => List.flatMap_congr fun σ _ => ?_
  congr 1; ring

/-- The numbers `i 2^ℓ + v` (`i < k`, `v < 2^ℓ`) with `m i v`, in increasing order. -/
def domL (k ℓ : ℕ) (m : ℕ → ℕ → Bool) : List ℕ :=
  (List.range k).flatMap fun i => (List.range (2 ^ ℓ)).flatMap fun v =>
    if m i v then [i * 2 ^ ℓ + v] else []

lemma flatMap_ite_singleton (l : List ℕ) (p : ℕ → Bool) :
    l.flatMap (fun n => if p n then [n] else []) = l.filter p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, ih, List.filter_cons]
    split_ifs <;> rfl

lemma domL_eq_filter (k ℓ : ℕ) (m : ℕ → ℕ → Bool) :
    domL k ℓ m = (List.range (k * 2 ^ ℓ)).filter fun n => m (n / 2 ^ ℓ) (n % 2 ^ ℓ) := by
  rw [← flatMap_ite_singleton, range_mul_flatMap]
  unfold domL
  refine List.flatMap_congr fun i _ => List.flatMap_congr fun v hv => ?_
  rw [List.mem_range] at hv
  have h1 : (i * 2 ^ ℓ + v) / 2 ^ ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv, zero_add]
  have h2 : (i * 2 ^ ℓ + v) % 2 ^ ℓ = v := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
  rw [h1, h2]

/-- The coordinate descriptions `i, bits v` of the members `(i, v)` with `m i v`. -/
def cdL (k ℓ : ℕ) (m : ℕ → ℕ → Bool) : List ℕ :=
  (List.range k).flatMap fun i => (List.range (2 ^ ℓ)).flatMap fun v =>
    if m i v then i :: bitsL ℓ v else []

lemma domL_flatMap (k ℓ : ℕ) (m : ℕ → ℕ → Bool) :
    (domL k ℓ m).flatMap (coordNumDescription ℓ) = cdL k ℓ m := by
  unfold domL cdL
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun i _ => ?_
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun v hv => ?_
  rw [List.mem_range] at hv
  split <;> simp [coordNumDescription_eq hv]

/-- **Descriptions of coordinate domains.** -/
theorem domainDescription_eq_domL {k : ℕ} (D : Finset (Coord k ℓ)) (m : ℕ → ℕ → Bool)
    (hm : ∀ i (hi : i < k), ∀ v < 2 ^ ℓ, m i v = true ↔ ((⟨i, hi⟩, toBlk ℓ v) : Coord k ℓ) ∈ D) :
    domainDescription D = (domL k ℓ m).length :: cdL k ℓ m := by
  have hsort : (D.image coordNum).sort (· ≤ ·) = domL k ℓ m := by
    have hnd : (domL k ℓ m).Nodup := by
      rw [domL_eq_filter]; exact (List.nodup_range).filter _
    have hpw : (domL k ℓ m).Pairwise (· ≤ ·) := by
      rw [domL_eq_filter]
      exact (List.pairwise_lt_range.imp le_of_lt).filter _
    have hfs : (domL k ℓ m).toFinset = D.image coordNum := by
      ext n
      rw [List.mem_toFinset, domL_eq_filter, List.mem_filter, List.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hn, hmn⟩
        have hq : n / 2 ^ ℓ < k := by
          rw [Nat.div_lt_iff_lt_mul (by positivity)]; exact hn
        have hr : n % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt _ (by positivity)
        refine ⟨_, (hm _ hq _ hr).mp hmn, ?_⟩
        rw [coordNum_toBlk hq hr, Nat.mul_comm]
        exact Nat.div_add_mod n (2 ^ ℓ)
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨⟨i, hi⟩, b⟩ := c
        have hb := regVal_lt b
        have e : ((⟨i, hi⟩, b) : Coord k ℓ) = (⟨i, hi⟩, toBlk ℓ (regVal b)) := by
          rw [toBlk_regVal]
        rw [e] at hc ⊢
        rw [coordNum_toBlk hi hb]
        have h1 : (i * 2 ^ ℓ + regVal b) / 2 ^ ℓ = i := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hb,
            zero_add]
        have h2 : (i * 2 ^ ℓ + regVal b) % 2 ^ ℓ = regVal b := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
        refine ⟨?_, ?_⟩
        · calc i * 2 ^ ℓ + regVal b < i * 2 ^ ℓ + 2 ^ ℓ := by omega
            _ = (i + 1) * 2 ^ ℓ := by ring
            _ ≤ k * 2 ^ ℓ := Nat.mul_le_mul_right _ hi
        · rw [h1, h2]; exact (hm i hi _ hb).mpr hc
    rw [← hfs]
    exact (List.toFinset_sort _ hnd).mpr hpw
  unfold domainDescription
  simp only
  rw [hsort, domL_flatMap]

/-- The full domain. -/
lemma domL_true (k ℓ : ℕ) : domL k ℓ (fun _ _ => true) = List.range (k * 2 ^ ℓ) := by
  rw [domL_eq_filter, List.filter_true]

lemma domainDescription_univ (k ℓ : ℕ) :
    domainDescription (Finset.univ : Finset (Coord k ℓ)) =
      (k * 2 ^ ℓ) :: (List.range k).flatMap fun i => (List.range (2 ^ ℓ)).flatMap fun v =>
        i :: bitsL ℓ v := by
  rw [domainDescription_eq_domL _ (fun _ _ => true) (fun _ _ _ _ => by simp), domL_true,
    List.length_range]
  simp [cdL]

/-! ## Permutations -/

/-- The description of a permutation keeping the blocks and shifting by the mask. -/
lemma permDescription_of_permDesc {π : BlockPerm (s + 1) ℓ} {msk : ℕ} (h : PermDesc π msk) :
    permDescription π =
      List.range (s + 1) ++
        (List.range (s + 1)).flatMap (fun i => bitsL ℓ (shiftVal s ℓ msk i)) := by
  have hp : ∀ i, (π.perm i : ℕ) = i := fun i => by
    have := (h (i, 0)).1
    simp only [BlockPerm.apply] at this
    rw [this]
  have hs : ∀ i, blockDescription (π.shift i) = bitsL ℓ (shiftVal s ℓ msk i) := fun i => by
    have := (h (i, 0)).2
    simp only [BlockPerm.apply, zero_add, regVal_zero, Nat.zero_xor] at this
    rw [blockDescription_eq, this]
  unfold permDescription
  simp only [hp, hs]
  rw [← map_val_finRange, List.flatMap_map]

lemma permDesc_of_permId {π : BlockPerm (s + 1) ℓ} (h : PermId π) : PermDesc π 0 := by
  intro c
  rw [h c, shiftVal_zero]
  simp

/-! ## Schemas -/

/-- The emitted description of a schema with numbers `n`, domain list `dl` and mask `msk`. -/
def schDescN (s : ℕ) (ℓ : ℕ) (n : SchNum) (dl cd : List ℕ) : List ℕ :=
  let pd := fun m => List.range (s + 1) ++
    (List.range (s + 1)).flatMap (fun i => bitsL ℓ (shiftVal s ℓ m i))
  if n.tern then [3, n.u, n.v, n.en] ++ (dl.length :: cd) ++ pd n.msk ++ pd 0 ++ pd 0
  else [2, n.u, n.v] ++ (dl.length :: cd) ++ pd n.msk ++ pd 0

/-- **The description of a schema** from its numbers and its domain. -/
theorem schemaDescription_of_match {N : ℕ} {D : Finset (Coord (s + 1) ℓ)}
    {e : Schema (s + 1) ℓ N} {n : SchNum} (h : SchMatch D e n) (m : ℕ → ℕ → Bool)
    (hm : ∀ i (hi : i < s + 1), ∀ v < 2 ^ ℓ,
      m i v = true ↔ ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) ∈ e.domain) :
    schemaDescription e = schDescN s ℓ n (domL (s + 1) ℓ m) (cdL (s + 1) ℓ m) := by
  obtain ⟨ht, hu, hv, hen, hpu, hpv, hpe, -⟩ := h
  have hpv' := permDescription_of_permDesc (permDesc_of_permId hpv)
  have hpe' := permDescription_of_permDesc (permDesc_of_permId hpe)
  have hpu' := permDescription_of_permDesc hpu
  cases e with
  | binary u v D' σ τ =>
    simp only [isTern] at ht
    simp only [locU, locV] at hu hv
    simp only [permU] at hpu'
    simp only [permV] at hpv'
    simp only [Schema.domain] at hm
    simp only [schemaDescription, schDescN, ← ht, Bool.false_eq_true, if_false, hu, hv,
      hpu', hpv', domainDescription_eq_domL D' m hm, List.append_assoc, List.cons_append,
      List.nil_append]
  | ternary u v w D' σ τ π =>
    simp only [isTern] at ht
    simp only [locU, locV, locEnd] at hu hv hen
    simp only [permU] at hpu'
    simp only [permV] at hpv'
    simp only [permEnd] at hpe'
    simp only [Schema.domain] at hm
    simp only [schemaDescription, schDescN, ← ht, if_true, hu, hv, hen,
      hpu', hpv', hpe', domainDescription_eq_domL D' m hm, List.append_assoc, List.cons_append,
      List.nil_append]

/-! ## Locations -/

/-- The location part of the description of a compiled system. -/
theorem locsDesc_compile (R : RegisterProgram s ℓ) (p₀ : Fin R.numLocations)
    (a₀ : Fin s → Fin ℓ → ZMod 2) :
    (List.finRange (R.compile p₀ a₀).numLocations).flatMap
        (fun v => initNum ((R.compile p₀ a₀).init v) :: domainDescription ((R.compile p₀ a₀).domain v)) =
      (List.range R.compiledSize).flatMap fun v =>
        ((if v = (R.loc (.prog R.accept)).val then 1 else 0) +
          2 * (if v = (R.loc (.det .out)).val then 1 else 0)) ::
          ((s + 1) * 2 ^ ℓ) :: (List.range (s + 1)).flatMap fun i =>
            (List.range (2 ^ ℓ)).flatMap fun w => i :: bitsL ℓ w := by
  have hne : (R.loc (.prog R.accept)).val ≠ (R.loc (.det .out)).val := fun h =>
    absurd (R.loc_inj.mp (Fin.ext h)) (by simp)
  show (List.finRange R.compiledSize).flatMap
        (fun v => initNum (R.compiledInit v) :: domainDescription (Finset.univ : Finset (Coord (s + 1) ℓ))) = _
  rw [← flatMap_finRange]
  refine List.flatMap_congr fun v _ => ?_
  rw [domainDescription_univ]
  congr 1
  unfold RegisterProgram.compiledInit
  by_cases h1 : v = R.loc (.prog R.accept)
  · have h2 : v.val ≠ (R.loc (.det .out)).val := by rw [h1]; exact hne
    rw [if_pos h1, if_pos (congrArg Fin.val h1), if_neg h2]
    rfl
  · have h1' : v.val ≠ (R.loc (.prog R.accept)).val := fun h => h1 (Fin.ext h)
    rw [if_neg h1, if_neg h1']
    by_cases h2 : v = R.loc (.det .out)
    · rw [if_pos h2, if_pos (congrArg Fin.val h2)]; rfl
    · have h2' : v.val ≠ (R.loc (.det .out)).val := fun h => h2 (Fin.ext h)
      rw [if_neg h2, if_neg h2']; rfl

end Lax119563Proofs.Reduction

end Reduction_SysDesc

/-! ### Formerly `Lax119563Proofs.Reduction.PkSys` -/

section Reduction_PkSys

/-!
# The packed system generator

`sysGenP M` (run on the globals `GlobP`, depth `19`) emits `systemDescription (Iv M x s ℓ H)`
(**`out_sysGenP`**), with the number `s` of data blocks read from
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

end Reduction_PkSys

/-! ### Formerly `Lax119563Proofs.Reduction.PkFmt` -/

section Reduction_PkFmt

/-!
# The preprocessed input of the packed generator

The packed generator reads `h, s` and `x` from the input `pkInput x h s`: for every position
`k < m = max(|x|, h, s, 2^⌈(h+2)/s⌉)` a record of two numbers with fixed binary lengths
(`8 + x_k + 2 [k < |x|] + 4 [k < h]` and `4 + [k < s]`), whose codes take `16` symbols, so
that the bit of position `16 k + j` is the bit `j` of the record `k` (`inBit_pkInput`):
`x_k` at `j = 1`, `[k < |x|]` at `j = 3`, `[k < h]` at `j = 5`, `[k < s]` at `j = 10`.
The counts of the flags are `|x|, h, s` (`count_pkInput`).
-/

namespace Lax119563Proofs.Reduction

open Lax119563.BinaryEncodings Xp

/-! ## The format -/

/-- The number of records. -/
def pkLen (n h s : ℕ) : ℕ := max (max n h) (max s (2 ^ ((h + 1 + s) / s)))

/-- The two numbers of record `k`. -/
def pkRec (x : List Bool) (h s k : ℕ) : List ℕ :=
  [8 + (x.getD k false).toNat + 2 * (decide (k < x.length)).toNat + 4 * (decide (k < h)).toNat,
    4 + (decide (k < s)).toNat]

/-- The preprocessed input. -/
def pkInput (x : List Bool) (h s : ℕ) : List Bool :=
  encodeNats ((List.range (pkLen x.length h s)).flatMap (pkRec x h s))

/-- The `16` symbols of a record. -/
def pkBlk (a b c d : Bool) : List Bool :=
  [true, a, true, b, true, c, true, true, false, true, d, true, false, true, true, false]

lemma encodeNats_rec (a b c d : Bool) :
    encodeNats [8 + a.toNat + 2 * b.toNat + 4 * c.toNat, 4 + d.toNat] = pkBlk a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

lemma pkInput_eq (x : List Bool) (h s : ℕ) :
    pkInput x h s = (List.range (pkLen x.length h s)).flatMap fun k =>
      pkBlk (x.getD k false) (decide (k < x.length)) (decide (k < h)) (decide (k < s)) := by
  rw [pkInput, encodeNats, List.flatMap_assoc]
  refine List.flatMap_congr fun k _ => ?_
  rw [← encodeNats_rec]
  rfl

lemma length_pkBlk (a b c d : Bool) : (pkBlk a b c d).length = 16 := rfl

lemma getElem?_blocks (blk : ℕ → List Bool) (hb : ∀ k, (blk k).length = 16) :
    ∀ m k j, j < 16 → ((List.range m).flatMap blk)[j + 16 * k]? =
      if k < m then (blk k)[j]? else none
  | 0, k, j, _ => by simp
  | m + 1, k, j, hj => by
    have hl : ((List.range m).flatMap blk).length = 16 * m := by
      rw [List.length_flatMap]; simp [hb, Nat.mul_comm]
    rw [List.range_succ, List.flatMap_append, List.getElem?_append]
    by_cases hk : k < m
    · rw [if_pos (by omega), getElem?_blocks blk hb m k j hj, if_pos hk, if_pos (by omega)]
    · rw [if_neg (by omega), List.flatMap_singleton, hl]
      by_cases hkm : k = m
      · subst hkm
        rw [if_pos (by omega), show j + 16 * k - 16 * k = j by omega]
      · rw [if_neg (by omega), List.getElem?_eq_none (by rw [hb]; omega)]

lemma inBit_eq_getElem? (l : List Bool) (p : ℕ) :
    inBit l p = (l[p]?).elim 0 (fun b => b.toNat + 1) := by
  unfold inBit
  rcases Nat.lt_or_ge p l.length with h | h
  · rw [List.drop_eq_getElem_cons h, List.getElem?_eq_getElem h]; rfl
  · rw [List.drop_eq_nil_of_le h, List.getElem?_eq_none h]; rfl

/-- **The bits of the preprocessed input.** -/
lemma inBit_pkInput (x : List Bool) (h s k j : ℕ) (hj : j < 16) :
    inBit (pkInput x h s) (j + 16 * k) =
      if k < pkLen x.length h s then
        ((pkBlk (x.getD k false) (decide (k < x.length)) (decide (k < h)) (decide (k < s)))[j]?).elim
          0 (fun b => b.toNat + 1)
      else 0 := by
  rw [inBit_eq_getElem?, pkInput_eq, getElem?_blocks _ (fun _ => length_pkBlk _ _ _ _) _ k j hj]
  split_ifs <;> rfl

lemma length_pkInput (x : List Bool) (h s : ℕ) :
    (pkInput x h s).length = 16 * pkLen x.length h s := by
  rw [pkInput_eq, List.length_flatMap]; simp [length_pkBlk, Nat.mul_comm]

/-- The bit of `x` at `16 v + 1`. -/
lemma inBit_pkInput_x (x : List Bool) (h s : ℕ) {v : ℕ} (hv : v < x.length) :
    inBit (pkInput x h s) (1 + 16 * v) = inBit x v := by
  have hm : v < pkLen x.length h s := by unfold pkLen; omega
  rw [inBit_pkInput x h s v 1 (by omega), if_pos hm, inBit_eq_getElem?, List.getElem?_eq_getElem hv,
    List.getD_eq_getElem _ _ hv]
  rfl

/-! ## Counting flags -/

/-- `k % 16 = t`. -/
def isMod (t : ℕ) (kX : Xp) : Xp := eq kX (add (shl (shr kX (const 4)) (const 4)) (const t))

lemma eval_isMod (t : ℕ) (kX : Xp) (ρ : List ℕ) :
    (isMod t kX).eval ρ = if kX.eval ρ = kX.eval ρ / 16 * 16 + t then 1 else 0 := by
  rw [isMod, Xp.eval_eq]
  simp only [Xp.eval_add, Xp.eval_shl, Xp.eval_shr, Xp.eval_const]
  norm_num

/-- The count of the positions `k ≡ t (mod 16)` with input bit `1`, by a generator at depth
`d` (inside a `loopX`: `k` at `d + 1`, the input value at `d + 2`). -/
def flagGen (t d : ℕ) : Gn :=
  Gn.when (and (isMod t (var (d + 1))) (eq (var (d + 2)) (const 2))) (.emit (const 0))

lemma count_blocks {m : ℕ} (F : ℕ → ℕ → List ℕ) (t : ℕ) (ht : t < 16)
    (hF : ∀ q r, r < 16 → F q r = if r = t then F q t else []) :
    ((List.range (16 * m)).flatMap fun k => F (k / 16) (k % 16)) =
      (List.range m).flatMap fun q => F q t := by
  rw [Gn.flatMap_range_mul]
  refine List.flatMap_congr fun q _ => ?_
  have e : ∀ r ∈ List.range 16, F ((r + 16 * q) / 16) ((r + 16 * q) % 16) =
      if t = r then F q r else [] := fun r hr => by
    rw [List.mem_range] at hr
    rw [show (r + 16 * q) / 16 = q by omega, show (r + 16 * q) % 16 = r by omega, hF q r hr]
    by_cases h : r = t
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [List.flatMap_congr e, Gn.flatMap_range_ite, if_pos ht]

lemma length_flatMap_lt : ∀ m n : ℕ,
    ((List.range m).flatMap fun q => if q < n then [0] else []).length = min m n
  | 0, n => by simp
  | m + 1, n => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_lt m n]
    by_cases h : m < n
    · simp [h]; omega
    · simp [h]; omega

end Lax119563Proofs.Reduction

end Reduction_PkFmt

/-! ### Formerly `Lax119563Proofs.Reduction.PkPre` -/

section Reduction_PkPre

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

/-- The part of the prelude after `|y|, n, h, s, Λ`. -/
def midP (M : Machine) (g : Gn) : Gn :=
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

/-- **The prelude of the packed generator.** -/
def preludeP (M : Machine) (g : Gn) : Gn :=
  len <|
  flagCount 3 1 <|
  flagCount 5 2 <|
  flagCount 10 3 <|
  bind (mul (add (var 2) (const 3)) (add (var 2) (const 3))) (midP M g)

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
  rw [Gn.midP, out_log_step (by omega) (by
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

end Reduction_PkPre
