import Lax119563Proofs.Reduction.SymMoves

/-!
# The command enumerator

`cmdEnum M s b HX RX body` runs `body` once for every command of the code-ordered verifier
program, in order: it loops over the digits `t5 < C, t4 < R, t3 < C, t2 < C, t1 < R` of the
location numbers (`R = radix M H`, the value of `RX`; `C = cM M`; `H` the value of `HX`), pushes
`t1 - 1`, `t4 - 1`, `H - t1 - 1`, `H + 2 - t1` and
`rest = t1 + R (t2 + C (t3 + C (t4 + R t5)))`, then for each
tag `t < 16` finds the kind whose location has number `t + 16 rest` (`matchX`), pushes that
number and, for each move of the location, its index `k` and the eight numbers of its command
(`SMv.recX`).

With `ρ.length = b` the body runs on the stack `stkL ρ L ++ r` for the records `r ∈ recsOf L`
(`out_cmdEnum`), and `desc_recsOf`: the records are `k :: rs[k]` where `rs` describes the
commands of the moves of `L` (`CmdDesc`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp

variable {M : Machine} {s : ℕ}

namespace Gn

variable {x : List Bool} {ρ : List ℕ}

/-- `f a` for the first `a ∈ l` with `c a ≠ 0`. -/
def firstL {α : Type} (c : α → Xp) (f : α → Gn) : List α → Gn
  | [] => skip
  | a :: l => ite (c a) (f a) (firstL c f l)

lemma out_firstL {α : Type} (c : α → Xp) (f : α → Gn) : ∀ l : List α,
    (firstL c f l).out x ρ =
      match l.find? (fun a => (c a).eval ρ ≠ 0) with
      | some a => (f a).out x ρ
      | none => []
  | [] => rfl
  | a :: l => by
    simp only [firstL, out, List.find?_cons]
    by_cases h : (c a).eval ρ ≠ 0
    · simp [h]
    · simp only [h, if_false, decide_false]
      exact out_firstL c f l

/-- The moves of the selected branch, each with its index and its command record. -/
def brGen (RX HX : Xp) (body : Gn) : List (Xp × List (SMv M s)) → Gn
  | [] => skip
  | (c, ms) :: rest => ite c (seqL (ms.zipIdx.map fun p =>
      bindL (Xp.const p.2 :: p.1.recX RX HX) body)) (brGen RX HX body rest)

lemma out_brGen {n : ℕ} (hρ : ρ.length = n) {RX HX : Xp} (hR : RX.Bnd n) (hH : HX.Bnd n)
    (body : Gn) :
    ∀ brs : List (Xp × List (SMv M s)), (∀ br ∈ brs, br.1.Bnd n ∧ ∀ m ∈ br.2, m.Bnd n) →
      (brGen RX HX body brs).out x ρ = (selBr ρ brs).zipIdx.flatMap fun p =>
        body.out x (ρ ++ (p.2 :: (p.1.recX RX HX).map fun e => e.eval ρ))
  | [] => fun _ => rfl
  | (c, ms) :: rest => fun h => by
    simp only [brGen, out, selBr]
    by_cases hc : c.eval ρ ≠ 0
    · simp only [hc, ne_eq, not_false_eq_true, if_true, out_seqL, List.flatMap_map]
      refine List.flatMap_congr fun p hp => ?_
      have hm : p.1 ∈ ms := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
      rw [out_bindL body _ hρ ?_]
      · simp
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · trivial
        · exact SMv.bnd_rec hR hH _ ((h (c, ms) (by simp)).2 _ hm) e he
    · simp only [hc, if_false]
      exact out_brGen hρ hR hH body rest fun br hbr => h br (by simp [hbr])

end Gn

/-! ## The enumerator -/

section Enum

variable (M s)

/-- The runtime values at base depth `b`. -/
def rvB (b : ℕ) (HX : Xp) : RVals :=
  ⟨var (b + 9), var (b + 3), var (b + 10), var (b + 11), var (b + 12), var (b + 13), HX⟩

/-- `t1 + R (t2 + C (t3 + C (t4 + R t5)))`. -/
def restX (C b : ℕ) (RX : Xp) : Xp :=
  add (var (b + 9)) (mul (add (var (b + 7)) (mulC C (add (var (b + 5)) (mulC C (add (var (b + 3))
    (mul (var (b + 1)) RX)))))) RX)

/-- The runtime values are in range. -/
def validX (b : ℕ) (HX : Xp) : SKind M → Xp
  | .cell .. | .state .. | .headSet .. | .restore .. | .gather .. =>
      lt (var (b + 9)) (add HX (const 1))
  | .headIn .. => and (lt (var (b + 9)) (add HX (const 1))) (lt (var (b + 3)) (add HX (const 1)))
  | _ => const 1

/-- The kind `K` has location number `tag + 16 rest`. -/
def matchX (b : ℕ) (HX RX : Xp) (K : SKind M) : Xp :=
  and (eq ((K.sloc (var (b + 9)) (var (b + 3))).codeX RX HX)
    (add (const (K.sloc (var (b + 9)) (var (b + 3))).tag) (mulC 16 (var (b + 14)))))
    (validX M b HX K)

/-- The commands of the location of kind `K`. -/
def kindGen (b : ℕ) (HX RX : Xp) (body : Gn) (K : SKind M) : Gn :=
  Gn.bind ((K.sloc (var (b + 9)) (var (b + 3))).codeX RX HX)
    (Gn.brGen RX HX body (K.brs (s := s) (rvB b HX)))

/-- The commands of the locations with given digits `t1, …, t5`, in order of the tag. -/
def tupleGen (b : ℕ) (HX RX : Xp) (body : Gn) : Gn :=
  Gn.seqL ((List.range 16).map fun t =>
    Gn.firstL (matchX M b HX RX) (kindGen M s b HX RX body) (kindsOfTag M t))

/-- **The command enumerator.** -/
def cmdEnum (b : ℕ) (HX RX : Xp) (body : Gn) : Gn :=
  .loop (const (cM M)) (.loop RX (.loop (const (cM M)) (.loop (const (cM M)) (.loop RX (
    Gn.bindSub (b + 10) (var (b + 9)) (const 1) (
    Gn.bindSub (b + 11) (var (b + 3)) (const 1) (
    Gn.bindSub (b + 12) HX (add (var (b + 9)) (const 1)) (
    Gn.bindSub (b + 13) (add HX (const 2)) (var (b + 9)) (
    .bind (restX (cM M) b RX) (tupleGen M s b HX RX body))))))))))

/-- The stack below the source number, for the digits `t = (tag, t1, …, t5)`. -/
def stkT (ρ : List ℕ) (H R C : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : List ℕ :=
  ρ ++ [C, t.2.2.2.2.2, R, t.2.2.2.2.1, C, t.2.2.2.1, C, t.2.2.1, R, t.2.1,
    t.2.1 - 1, t.2.2.2.2.1 - 1, H - (t.2.1 + 1), H + 2 - t.2.1,
    pack R t.2.1 (pack C t.2.2.1 (pack C t.2.2.2.1 (pack R t.2.2.2.2.1 t.2.2.2.2.2)))]

/-- The stack of the body for the location `L`, below the move records. -/
def stkL (ρ : List ℕ) (H : ℕ) (L : Loc M H) : List ℕ :=
  stkT ρ H (radix M H) (cM M) L.tuple ++ [(Loc.code L).val]

/-- The move records of `L`: the index of the move and the numbers of its command. -/
def recsOf (b : ℕ) (HX RX : Xp) (x : List Bool) (ρ : List ℕ) (H : ℕ) (L : Loc M H) :
    List (List ℕ) :=
  (selBr (stkL M ρ H L) (L.kind.brs (s := s) (rvB b HX))).zipIdx.map fun p =>
    p.2 :: (p.1.recX RX HX).map fun e => e.eval (stkL M ρ H L)

end Enum

/-! ## Digits of location numbers -/

lemma tuple_of_code {H : ℕ} {L : Loc M H} {t t1 t2 t3 t4 t5 : ℕ} (ht : t < 16)
    (h1 : t1 < radix M H) (h2 : t2 < cM M) (h3 : t3 < cM M) (h4 : t4 < radix M H)
    (h5 : t5 < cM M)
    (h : (Loc.code L).val = pack 16 t (pack (radix M H) t1 (pack (cM M) t2
      (pack (cM M) t3 (pack (radix M H) t4 t5))))) :
    L.tuple = (t, t1, t2, t3, t4, t5) := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := L.tuple_lt
  simp only [Loc.code] at h
  obtain ⟨e0, h⟩ := pack_inj a0 ht h
  obtain ⟨e1, h⟩ := pack_inj a1 h1 h
  obtain ⟨e2, h⟩ := pack_inj a2 h2 h
  obtain ⟨e3, h⟩ := pack_inj a3 h3 h
  obtain ⟨e4, e5⟩ := pack_inj a4 h4 h
  ext <;> assumption

lemma SKind.tag_sloc {H d u : ℕ} (dX uX : Xp) (K : SKind M) :
    (K.sloc dX uX).tag = (K.loc H d u).tuple.1 := by
  cases K <;> rfl

lemma SKind.kind_loc {H d u : ℕ} (K : SKind M) : (K.loc H d u).kind = K := by
  cases K <;> rfl

/-- Enumerating `16 R^2 C^3` numbers by digits below `C, R, C, C, R` and a tag below `16`. -/
lemma flatMap_range_digits {β : Type} (R C : ℕ) (F : ℕ → List β) :
    (List.range (16 * (R * (C * (C * (R * C)))))).flatMap F =
      (List.range C).flatMap fun t5 => (List.range R).flatMap fun t4 =>
      (List.range C).flatMap fun t3 => (List.range C).flatMap fun t2 =>
      (List.range R).flatMap fun t1 => (List.range 16).flatMap fun t =>
        F (pack 16 t (pack R t1 (pack C t2 (pack C t3 (pack R t4 t5))))) := by
  rw [Gn.flatMap_range_mul, Gn.flatMap_range_mul, Gn.flatMap_range_mul, Gn.flatMap_range_mul,
    Gn.flatMap_range_mul]
  rfl

end Lax119563Proofs.Reduction

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp

variable {M : Machine} {s : ℕ}

section Out

variable {x : List Bool} {ρ : List ℕ} {b H : ℕ} {HX RX : Xp} {body : Gn}

lemma eval_matchX {τ : List ℕ} (hH : HX.eval τ = H) (hR : RX.eval τ = radix M H)
    (K : SKind M) :
    (matchX M b HX RX K).eval τ ≠ 0 ↔
      K.Valid H (τ.getD (b + 9) 0) (τ.getD (b + 3) 0) ∧
      (Loc.code (K.loc H (τ.getD (b + 9) 0) (τ.getD (b + 3) 0))).val =
        (K.loc H (τ.getD (b + 9) 0) (τ.getD (b + 3) 0)).tuple.1 + 16 * τ.getD (b + 14) 0 := by
  have va : ∀ i, (lt (var (b + i)) (add HX (const 1))).eval τ =
      if τ.getD (b + i) 0 ≤ H then 1 else 0 := fun i => by
    simp only [Xp.eval_lt_eq, Xp.eval_add, Xp.eval_const, Xp.eval_var, hH]
    by_cases h : τ.getD (b + i) 0 ≤ H
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hv : (validX M b HX K).eval τ ≤ 1 ∧
      ((validX M b HX K).eval τ = 1 ↔ K.Valid H (τ.getD (b + 9) 0) (τ.getD (b + 3) 0)) := by
    have c1 : (const 1).eval τ ≤ 1 ∧ ((const 1).eval τ = 1 ↔ True) := ⟨le_rfl, iff_of_true rfl trivial⟩
    have c2 : (lt (var (b + 9)) (add HX (const 1))).eval τ ≤ 1 ∧
        ((lt (var (b + 9)) (add HX (const 1))).eval τ = 1 ↔ τ.getD (b + 9) 0 ≤ H) := by
      rw [va]
      by_cases h : τ.getD (b + 9) 0 ≤ H
      · rw [if_pos h]; exact ⟨le_rfl, iff_of_true rfl h⟩
      · rw [if_neg h]; exact ⟨by omega, iff_of_false (by omega) h⟩
    have c3 : (and (lt (var (b + 9)) (add HX (const 1))) (lt (var (b + 3)) (add HX (const 1)))).eval τ ≤ 1 ∧
        ((and (lt (var (b + 9)) (add HX (const 1))) (lt (var (b + 3)) (add HX (const 1)))).eval τ = 1 ↔
          τ.getD (b + 9) 0 ≤ H ∧ τ.getD (b + 3) 0 ≤ H) := by
      rw [Xp.eval_and (by rw [va]; split_ifs <;> omega) (by rw [va]; split_ifs <;> omega), va, va]
      by_cases h : τ.getD (b + 9) 0 ≤ H <;> by_cases h' : τ.getD (b + 3) 0 ≤ H <;>
        simp only [h, h', if_true, if_false] <;> simp
    cases K <;> simp only [validX, SKind.Valid] <;> first | exact c1 | exact c2 | exact c3
  have heq : (eq ((K.sloc (var (b + 9)) (var (b + 3))).codeX RX HX)
      (add (const (K.sloc (var (b + 9)) (var (b + 3))).tag) (mulC 16 (var (b + 14))))).eval τ ≤ 1 := by
    rw [Xp.eval_eq]; split_ifs <;> omega
  have hcx := SLoc.eval_codeX hR hH (K.sloc (var (b + 9)) (var (b + 3)))
  rw [SKind.eval_sloc] at hcx
  simp only [Xp.eval_var] at hcx
  have key : ((K.sloc (var (b + 9)) (var (b + 3))).codeX RX HX).eval τ =
      (add (const (K.sloc (var (b + 9)) (var (b + 3))).tag) (mulC 16 (var (b + 14)))).eval τ ↔
      (Loc.code (K.loc H (τ.getD (b + 9) 0) (τ.getD (b + 3) 0))).val =
        (K.loc H (τ.getD (b + 9) 0) (τ.getD (b + 3) 0)).tuple.1 + 16 * τ.getD (b + 14) 0 := by
    rw [hcx]
    simp only [Xp.eval_add, Xp.eval_const, Xp.eval_mulC, Xp.eval_var,
      SKind.tag_sloc (H := H) (d := τ.getD (b + 9) 0) (u := τ.getD (b + 3) 0)]
  unfold matchX
  rw [Xp.eval_and heq hv.1, Xp.eval_eq]
  by_cases hc : ((K.sloc (var (b + 9)) (var (b + 3))).codeX RX HX).eval τ =
      (add (const (K.sloc (var (b + 9)) (var (b + 3))).tag) (mulC 16 (var (b + 14)))).eval τ
  · rw [if_pos hc]
    by_cases hval : (validX M b HX K).eval τ = 1
    · rw [if_pos ⟨rfl, hval⟩]
      exact iff_of_true one_ne_zero ⟨hv.2.mp hval, key.mp hc⟩
    · rw [if_neg (fun h => hval h.2)]
      exact iff_of_false (fun h => h rfl) (fun h => hval (hv.2.mpr h.1))
  · rw [if_neg hc, if_neg (fun h => absurd h.1 (by norm_num))]
    exact iff_of_false (fun h => h rfl) (fun h => hc (key.mpr h.2))

lemma getD_stk {l : List ℕ} (hρ : ρ.length = b) (i : ℕ) : (ρ ++ l).getD (b + i) 0 = l.getD i 0 := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1; omega

lemma rvB_bnd (hHb : HX.Bnd b) : (rvB b HX).Bnd (b + 16) :=
  ⟨by show b + 9 < b + 16; omega, by show b + 3 < b + 16; omega,
    by show b + 10 < b + 16; omega, by show b + 11 < b + 16; omega,
    by show b + 12 < b + 16; omega, by show b + 13 < b + 16; omega,
    Xp.Bnd.mono (by omega) hHb⟩

lemma rvB_ok (hρ : ρ.length = b) (hH : HX.eval ρ = H) (hHb : HX.Bnd b) (R C : ℕ)
    (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (l : List ℕ) :
    (rvB b HX).Ok H (stkT ρ H R C t ++ l) t.2.1 t.2.2.2.2.1 := by
  have e : ∀ i, (stkT ρ H R C t ++ l).getD (b + i) 0 =
      ([C, t.2.2.2.2.2, R, t.2.2.2.2.1, C, t.2.2.2.1, C, t.2.2.1, R, t.2.1,
      t.2.1 - 1, t.2.2.2.2.1 - 1, H - (t.2.1 + 1), H + 2 - t.2.1,
      pack R t.2.1 (pack C t.2.2.1 (pack C t.2.2.2.1 (pack R t.2.2.2.2.1 t.2.2.2.2.2)))] ++
        l).getD i 0 := fun i => by
    rw [stkT, List.append_assoc, getD_stk hρ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp only [rvB, Xp.eval_var, e]; rfl)
    | (simp only [rvB]; rw [stkT, List.append_assoc]; exact (Xp.eval_append hρ _ hHb).trans hH)
    | (simp only [rvB, Xp.eval_var, e, List.cons_append, List.getD_cons_succ,
        List.getD_cons_zero]; omega)

lemma allB_map {α : Type} {n : ℕ} {l : List α} {f : α → SMv M s} (h : ∀ a ∈ l, (f a).Bnd n) :
    ∀ m ∈ l.map f, m.Bnd n := by
  intro m hm; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact h a ha

lemma allB_flatMap {α : Type} {n : ℕ} {l : List α} {f : α → List (SMv M s)}
    (h : ∀ a ∈ l, ∀ m ∈ f a, m.Bnd n) : ∀ m ∈ l.flatMap f, m.Bnd n := by
  intro m hm; obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hm; exact h a ha m hm

lemma allB_cons {n : ℕ} {m₀ : SMv M s} {l : List (SMv M s)} (h₀ : m₀.Bnd n)
    (h : ∀ m ∈ l, m.Bnd n) : ∀ m ∈ m₀ :: l, m.Bnd n := by
  intro m hm; rcases List.mem_cons.mp hm with rfl | hm
  · exact h₀
  · exact h m hm

lemma allB_nil {n : ℕ} : ∀ m ∈ ([] : List (SMv M s)), m.Bnd n := by simp

lemma allBr_cons {n : ℕ} {c : Xp} {l : List (SMv M s)} {rest : List (Xp × List (SMv M s))}
    (h₀ : c.Bnd n ∧ ∀ m ∈ l, m.Bnd n) (h : ∀ br ∈ rest, br.1.Bnd n ∧ ∀ m ∈ br.2, m.Bnd n) :
    ∀ br ∈ (c, l) :: rest, br.1.Bnd n ∧ ∀ m ∈ br.2, m.Bnd n := by
  intro br hbr; rcases List.mem_cons.mp hbr with rfl | hbr
  · exact h₀
  · exact h br hbr

lemma allBr_nil {n : ℕ} :
    ∀ br ∈ ([] : List (Xp × List (SMv M s))), br.1.Bnd n ∧ ∀ m ∈ br.2, m.Bnd n := by simp

/-- The branches read only levels below `n`. -/
lemma SKind.bnd_brs {n : ℕ} {V : RVals} (hV : V.Bnd n) (K : SKind M) :
    ∀ br ∈ K.brs (s := s) V, br.1.Bnd n ∧ ∀ m ∈ br.2, m.Bnd n := by
  have b1 := hV.d; have b2 := hV.u; have b3 := hV.dm1; have b4 := hV.um1; have b5 := hV.hd1
  have b6 := hV.hd2; have b7 := hV.H
  cases K <;> simp only [SKind.brs] <;> (try split_ifs) <;>
    repeat' (first | exact allBr_nil | refine allBr_cons ⟨?_, ?_⟩ ?_ | exact allB_nil |
      (refine allB_flatMap ?_; intro _ _) | (refine allB_map ?_; intro _ _) |
      refine allB_cons ?_ ?_)
  all_goals (try split_ifs) <;> (try simp only [SMv.Bnd, SMv.goto, SMv.fork']) <;>
    (try simp only [SLoc.Bnd]) <;> (try simp only [Xp.Bnd, Xp.eq, Xp.and]) <;>
    (try simp only [b1, b2, b3, b4, b5, b6, b7, and_self, and_true, true_and]) <;>
    (try trivial) <;> (try exact ⟨trivial, trivial⟩)

/-- The output for one tag and given digits. -/
lemma out_tag (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
    (hR : RX.eval ρ = radix M H) {t t1 t2 t3 t4 t5 : ℕ} (ht : t < 16)
    (h1 : t1 < radix M H) (h2 : t2 < cM M) (h3 : t3 < cM M) (h4 : t4 < radix M H)
    (h5 : t5 < cM M) :
    (Gn.firstL (matchX M b HX RX) (kindGen M s b HX RX body) (kindsOfTag M t)).out x
        (stkT ρ H (radix M H) (cM M) (t, t1, t2, t3, t4, t5)) =
      match decodeLoc M H (pack 16 t (pack (radix M H) t1 (pack (cM M) t2
          (pack (cM M) t3 (pack (radix M H) t4 t5))))) with
      | some L => (recsOf M s b HX RX x ρ H L).flatMap fun r => body.out x (stkL M ρ H L ++ r)
      | none => [] := by
  set τ := stkT ρ H (radix M H) (cM M) (t, t1, t2, t3, t4, t5) with hτ
  have hlen : τ.length = b + 15 := by simp [hτ, stkT, hρ]
  have g : ∀ i, τ.getD (b + i) 0 = ([cM M, t5, radix M H, t4, cM M, t3, cM M,
      t2, radix M H, t1, t1 - 1, t4 - 1, H - (t1 + 1), H + 2 - t1,
      pack (radix M H) t1 (pack (cM M) t2 (pack (cM M) t3
        (pack (radix M H) t4 t5)))]).getD i 0 := fun i => by
    rw [hτ, stkT, getD_stk hρ]
  have g9 : τ.getD (b + 9) 0 = t1 := by rw [g]; rfl
  have g3 : τ.getD (b + 3) 0 = t4 := by rw [g]; rfl
  have g14 : τ.getD (b + 14) 0 = pack (radix M H) t1 (pack (cM M) t2 (pack (cM M) t3
      (pack (radix M H) t4 t5))) := by rw [g]; rfl
  have hHτ : HX.eval τ = H := by rw [hτ, stkT]; exact (Xp.eval_append hρ _ hHb).trans hH
  have hRτ : RX.eval τ = radix M H := by rw [hτ, stkT]; exact (Xp.eval_append hρ _ hRb).trans hR
  rw [Gn.out_firstL]
  cases hf : (kindsOfTag M t).find? (fun K => (matchX M b HX RX K).eval τ ≠ 0) with
  | some K =>
    have hK := List.mem_of_find?_eq_some hf
    have hm := List.find?_some hf
    simp only [decide_eq_true_eq] at hm
    rw [eval_matchX hHτ hRτ, g9, g3, g14, tag_of_mem_kindsOfTag hK] at hm
    obtain ⟨hV, hc⟩ := hm
    set L := K.loc H t1 t4 with hL
    have hcode : (Loc.code L).val = pack 16 t (pack (radix M H) t1 (pack (cM M) t2
        (pack (cM M) t3 (pack (radix M H) t4 t5)))) := hc
    have htup := tuple_of_code ht h1 h2 h3 h4 h5 hcode
    rw [← hcode, decodeLoc_code]
    simp only
    have hstk : stkL M ρ H L = τ ++ [(Loc.code L).val] := by rw [stkL, htup]
    have hkind : L.kind = K := SKind.kind_loc K
    simp only [kindGen, Gn.out]
    have hcx : ((K.sloc (var (b + 9)) (var (b + 3))).codeX RX HX).eval τ = (Loc.code L).val := by
      rw [SLoc.eval_codeX hRτ hHτ, SKind.eval_sloc]
      simp only [Xp.eval_var, g9, g3, hL]
    rw [hcx, Gn.out_brGen (n := b + 16) (by simp [hlen]) (Xp.Bnd.mono (by omega) hRb)
      (Xp.Bnd.mono (by omega) hHb) body _
      (SKind.bnd_brs (rvB_bnd hHb) K)]
    rw [recsOf, List.flatMap_map, hstk, hkind]
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
      rw [eval_matchX hHτ hRτ, g9, g3, g14, hloc, htup]
      exact ⟨hval, hcode⟩

/-- **The output of the command enumerator.** -/
theorem out_cmdEnum (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b)
    (hH : HX.eval ρ = H) (hR : RX.eval ρ = radix M H) :
    (cmdEnum M s b HX RX body).out x ρ = (List.range (numLoc M H)).flatMap fun c =>
      match decodeLoc M H c with
      | some L => (recsOf M s b HX RX x ρ H L).flatMap fun r => body.out x (stkL M ρ H L ++ r)
      | none => [] := by
  rw [numLoc, flatMap_range_digits]
  have hCe : ∀ l, (const (cM M)).eval (ρ ++ l) = cM M := fun _ => rfl
  have hRe : ∀ l, RX.eval (ρ ++ l) = radix M H := fun l => (Xp.eval_append hρ l hRb).trans hR
  have hHe : ∀ l, HX.eval (ρ ++ l) = H := fun l => (Xp.eval_append hρ l hHb).trans hH
  simp only [cmdEnum, Gn.out, List.append_assoc, List.cons_append, List.nil_append, hRe, hR, hCe,
    Xp.eval_const]
  refine List.flatMap_congr fun t5 ht5 => List.flatMap_congr fun t4 ht4 =>
    List.flatMap_congr fun t3 ht3 => List.flatMap_congr fun t2 ht2 =>
    List.flatMap_congr fun t1 ht1 => ?_
  rw [List.mem_range] at ht5 ht4 ht3 ht2 ht1
  have hl : ∀ k (l : List ℕ), l.length = k → (ρ ++ l).length = b + k := fun k l h => by
    simp [hρ, h]
  rw [Gn.out_bindSub (a := var (b + 9)) (b := const 1) (hl 10 _ rfl)
    (by show b + 9 < b + 10; omega) trivial]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [Gn.out_bindSub (a := var (b + 3)) (b := const 1) (hl 11 _ rfl)
    (by show b + 3 < b + 11; omega) trivial]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [Gn.out_bindSub (a := HX) (b := add (var (b + 9)) (const 1)) (hl 12 _ rfl)
    (Xp.Bnd.mono (by omega) hHb)
    ⟨(by show b + 9 < b + 12; omega), trivial⟩]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [Gn.out_bindSub (a := add HX (const 2)) (b := var (b + 9)) (hl 13 _ rfl)
    ⟨Xp.Bnd.mono (by omega) hHb, trivial⟩
    (by show b + 9 < b + 13; omega)]
  simp only [Gn.out, tupleGen, Gn.out_seqL, List.flatMap_map, List.append_assoc,
    List.cons_append, List.nil_append]
  refine List.flatMap_congr fun t ht => ?_
  rw [List.mem_range] at ht
  rw [← out_tag hρ hHb hRb hH hR ht ht1 ht2 ht3 ht4 ht5]
  congr 1
  have hg : ∀ (l : List ℕ) (i : ℕ), (ρ ++ l).getD (b + i) 0 = l.getD i 0 :=
    fun l i => getD_stk hρ i
  simp only [stkT, restX, List.append_assoc, List.cons_append, List.nil_append, Xp.eval_var,
    Xp.eval_add, Xp.eval_mul, Xp.eval_mulC, Xp.eval_const, hg, hHe, hRe, List.getD_cons_succ,
    List.getD_cons_zero]
  simp only [List.cons.injEq, List.append_cancel_left_eq, and_true, true_and, pack]
  ring

/-- **The records describe the commands.** -/
theorem desc_recsOf (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b)
    (hH : HX.eval ρ = H) (hR : RX.eval ρ = radix M H) (ℓ : ℕ) (L : Loc M H) :
    ∃ rs : List (List ℕ), recsOf M s b HX RX x ρ H L = rs.zipIdx.map (fun p => p.2 :: p.1) ∧
      List.Forall₂ (fun mv r => CmdDesc M x s ℓ H (Move.toACmd ℓ L mv) r)
        (moves M x s ℓ H L) rs := by
  set σ := stkL M ρ H L with hσ
  have hV : (rvB b HX).Ok H σ L.tuple.2.1 L.tuple.2.2.2.2.1 := rvB_ok hρ hH hHb _ _ _ _
  have hRσ : RX.eval σ = radix M H := by
    rw [hσ, stkL, stkT, List.append_assoc]; exact (Xp.eval_append hρ _ hRb).trans hR
  obtain ⟨-, hval, hloc⟩ := L.kind_spec
  have hmv := moves_eq (s := s) (x := x) (ℓ := ℓ) hV L.kind hval
  rw [hloc] at hmv
  have hHσ : HX.eval σ = H := by
    rw [hσ, stkL, stkT, List.append_assoc]; exact (Xp.eval_append hρ _ hHb).trans hH
  refine ⟨(selBr σ (L.kind.brs (s := s) (rvB b HX))).map fun m => (m.recX RX HX).map
    fun e => e.eval σ, ?_, ?_⟩
  · rw [recsOf, List.zipIdx_map, List.map_map]
    rfl
  · rw [← hmv, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun m _ => SMv.desc hRσ hHσ L m

end Out

end Lax119563Proofs.Reduction
