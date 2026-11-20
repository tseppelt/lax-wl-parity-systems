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

lemma getD_stk {l : List ℕ} (hρ : ρ.length = b) (i : ℕ) : (ρ ++ l).getD (b + i) 0 = l.getD i 0 := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1; omega

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
