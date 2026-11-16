import Lax119563Proofs.Reduction.SymLoc

/-!
# The moves of the verifier as symbolic branch lists

For each location kind and constant fields, `brs V …` is a list of branches
`(condition, moves)`: the moves of the location are those of the first branch whose condition
evaluates to a nonzero value (`selBr`). The runtime values (depth `d`, head position `u`,
`d - 1`, `u - 1`, `H - d - 1`, `H + 2 - d`, `H`) are expressions `V : RVals`.

`moves_eq`: if `V` evaluates correctly (`RVals.Ok`), the selected branch, evaluated, is the
list of moves of the location (`Loc.ofS`); `ok_sel`: its targets have runtime fields `≤ H`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp

variable {M : Machine} {s : ℕ}

/-- Expressions for the runtime values of a location. -/
structure RVals where
  d : Xp
  u : Xp
  dm1 : Xp
  um1 : Xp
  hd1 : Xp
  hd2 : Xp
  H : Xp

/-- The expressions evaluate to `d, u, d - 1, u - 1, H - d - 1, H + 2 - d, H`. -/
structure RVals.Ok (V : RVals) (H₀ : ℕ) (ρ : List ℕ) (d₀ u₀ : ℕ) : Prop where
  d : V.d.eval ρ = d₀
  u : V.u.eval ρ = u₀
  dm1 : V.dm1.eval ρ = d₀ - 1
  um1 : V.um1.eval ρ = u₀ - 1
  hd1 : V.hd1.eval ρ = H₀ - d₀ - 1
  hd2 : V.hd2.eval ρ = H₀ + 2 - d₀
  H : V.H.eval ρ = H₀

/-- All expressions read only levels below `n`. -/
structure RVals.Bnd (V : RVals) (n : ℕ) : Prop where
  d : V.d.Bnd n
  u : V.u.Bnd n
  dm1 : V.dm1.Bnd n
  um1 : V.um1.Bnd n
  hd1 : V.hd1.Bnd n
  hd2 : V.hd2.Bnd n
  H : V.H.Bnd n

/-- The moves of the first branch whose condition holds. -/
def selBr {α : Type} (ρ : List ℕ) : List (Xp × List α) → List α
  | [] => []
  | (c, ms) :: rest => if c.eval ρ ≠ 0 then ms else selBr ρ rest

/-- The location kinds with their constant fields. -/
inductive SKind (M : Machine)
  | accept
  | reject
  | query
  | cell (θ : Fin 3) (ν : Tape M) (c : CellVal M)
  | state (θ : Fin 3) (p : ExtState M)
  | headIn (θ : Fin 2) (ν : Tape M)
  | headSet (θ : Fin 2) (ν : Tape M) (β : Fin 8)
  | restore (θ : Fin 2) (ν : Tape M) (c : CellVal M) (β : Fin 8)
  | gather (θ : Fin 2) (ν : Tape M) (c : CellVal M) (β : Fin 8)
  | baseCell (ν : Tape M) (ρ : Row M) (old : CellVal M) (k : Fin (M.tapes + 2))
  | baseState (ρ : Row M) (k : Fin (M.tapes + 2))
  | setJ (ν : Tape M) (h : Fin 4) (c : CellVal M)

/-- The location of a kind with runtime values `d, u`. -/
def SKind.loc (H d u : ℕ) : SKind M → Loc M H
  | accept => .accept
  | reject => .reject
  | query => .query
  | cell θ ν c => .cell (finH H d) θ ν c
  | state θ p => .state (finH H d) θ p
  | headIn θ ν => .headIn (finH H d) θ ν (finH H u)
  | headSet θ ν β => .headSet (finH H d) θ ν β
  | restore θ ν c β => .restore (finH H d) θ ν c β
  | gather θ ν c β => .gather (finH H d) θ ν c β
  | baseCell ν ρ old k => .baseCell ν ρ old k
  | baseState ρ k => .baseState ρ k
  | setJ ν h c => .setJ ν h c

/-- `goto` and unconditional forks. -/
def SMv.goto (dst : SLoc M) : SMv M s := .step (const 0) 0 0 0 dst
/-- An unconditional fork. -/
def SMv.fork' (l r : SLoc M) : SMv M s := .fork (const 0) 0 0 l r

/-- The branches of the moves of a kind. -/
def SKind.brs (V : RVals) : SKind M → List (Xp × List (SMv M s))
  | accept => []
  | reject => []
  | query => [(const 1, ((allExt M).filter fun p => decide (p.2 = some true)).map fun p =>
      SMv.goto (.state (const 0) 2 p))]
  | cell θ ν c =>
    if θ.val = 0 then
      [(eq V.d (const 0), SMv.hit ν c .accept ::
          (if c = (0, false) then
            ((List.finRange s).filter fun i => decide (i.val ≠ 0)).map fun i => SMv.miss i .accept
          else [])),
        (const 1, (List.finRange 2).flatMap fun (θ' : Fin 2) => (List.finRange 8).map fun β =>
          SMv.fork V.hd2 1 θ'.val (.headSet V.dm1 θ' ν β) (.gather V.dm1 θ' ν c β))]
    else
      [(lt V.d V.H, (List.finRange 8).map fun β =>
          SMv.fork' (.headSet V.d (ppred θ) ν β) (.restore V.d (ppred θ) ν c β)),
        (const 1, if θ.val = 2 then
          (allRows M).flatMap fun ρ => (allCV M).flatMap fun old =>
            ((List.finRange 4).filter fun jj =>
              decide (nextCell ρ.1 ρ.2.2 ν ((ρ.2.1 ν).val + 1 : ℤ) (jj.val : ℤ) old = c)).map
            fun jj => SMv.step (const 0) 2 jj.val jj.val (.baseCell ν ρ old 0)
          else [])]
  | state θ p =>
    if θ.val = 0 then
      [(eq V.d (const 0), if p = (0, none) then [SMv.goto .accept] else []),
        (const 1, (List.finRange 2).map fun (θ' : Fin 2) =>
          SMv.step V.hd2 1 θ'.val θ'.val (.state V.dm1 θ'.castSucc p))]
    else
      [(lt V.d V.H, (List.finRange 2).map fun (e : Fin 2) =>
          SMv.step (add V.hd1 (const 2)) 1 e.val (ppred θ).val
            (.state (add V.d (const 1)) 2 p)),
        (const 1, if θ.val = 2 then
          ((allRows M).filter fun ρ => decide (nextExt ρ.1 ρ.2.2 = p)).map fun ρ =>
            SMv.goto (.baseState ρ 0)
          else [])]
  | headIn θ ν =>
    [(and (lt (add V.u V.d) V.H) (eq V.u (const 0)),
        (List.finRange (M.symbols + 3)).map fun γ => SMv.goto (.cell V.d θ.castSucc ν (γ, true))),
      (lt (add V.u V.d) V.H, (List.finRange 2).flatMap fun (e : Fin 2) =>
        (List.finRange 2).map fun (e' : Fin 2) =>
          SMv.step V.um1 1 e.val e'.val (.headIn V.d θ ν V.um1))]
  | headSet θ ν β =>
    [(lt V.d V.H, (List.finRange 8).map fun (q : Fin 8) =>
        SMv.step V.hd1 3 q.val β.val (.headIn V.d θ ν V.hd1))]
  | restore θ ν c β =>
    [(lt V.d V.H, (List.finRange 8).map fun (q : Fin 8) =>
        if sel β ≤ q.val ∧ q.val < sel β + 4 then
          SMv.step V.hd1 3 q.val (4 * θ.val + (q.val - sel β)) (.cell (add V.d (const 1)) 2 ν c)
        else SMv.step V.hd1 3 q.val q.val (.cell V.d θ.castSucc ν c))]
  | gather θ ν c β =>
    [(lt V.d V.H, (List.finRange 4).map fun (c' : Fin 4) =>
        SMv.step V.hd1 3 (4 * θ.val + c'.val) (sel β + c'.val) (.cell V.d θ.castSucc ν c))]
  | baseCell ν ρ old k =>
    [(const 1, if h : k.val < M.tapes + 1 then
        [SMv.fork' (.setJ ⟨k.val, h⟩ ⟨(ρ.2.1 ⟨k.val, h⟩).val + 1, by omega⟩
          (ρ.2.2 ⟨k.val, h⟩, true)) (.baseCell ν ρ old ⟨k.val + 1, by omega⟩)]
      else [SMv.fork' (.state V.H 0 ρ.1) (.cell V.H 0 ν old)])]
  | baseState ρ k =>
    [(const 1, if h : k.val < M.tapes + 1 then
        [SMv.fork' (.setJ ⟨k.val, h⟩ ⟨(ρ.2.1 ⟨k.val, h⟩).val + 1, by omega⟩
          (ρ.2.2 ⟨k.val, h⟩, true)) (.baseState ρ ⟨k.val + 1, by omega⟩)]
      else [SMv.goto (.state V.H 0 ρ.1)])]
  | setJ ν h c =>
    [(const 1, (List.finRange 4).map fun (q : Fin 4) =>
        SMv.step (const 0) 2 q.val h.val (.cell V.H 0 ν c))]

/-- The kind has runtime values in range: `d ≤ H`, and `u ≤ H` for `headIn`. -/
def SKind.Valid (H d u : ℕ) : SKind M → Prop
  | cell .. | state .. | headSet .. | restore .. | gather .. => d ≤ H
  | headIn .. => d ≤ H ∧ u ≤ H
  | _ => True

/-- The symbolic location of a kind, with runtime values `dX, uX`. -/
def SKind.sloc (dX uX : Xp) : SKind M → SLoc M
  | accept => .accept
  | reject => .reject
  | query => .query
  | cell θ ν c => .cell dX θ ν c
  | state θ p => .state dX θ p
  | headIn θ ν => .headIn dX θ ν uX
  | headSet θ ν β => .headSet dX θ ν β
  | restore θ ν c β => .restore dX θ ν c β
  | gather θ ν c β => .gather dX θ ν c β
  | baseCell ν ρ old k => .baseCell ν ρ old k
  | baseState ρ k => .baseState ρ k
  | setJ ν h c => .setJ ν h c

lemma SKind.eval_sloc {H : ℕ} {ρ : List ℕ} (dX uX : Xp) (K : SKind M) :
    (K.sloc dX uX).eval H ρ = K.loc H (dX.eval ρ) (uX.eval ρ) := by
  cases K <;> rfl

lemma SKind.bnd_sloc {n : ℕ} {dX uX : Xp} (hd : dX.Bnd n) (hu : uX.Bnd n) (K : SKind M) :
    (K.sloc dX uX).Bnd n := by
  cases K
  all_goals first | trivial | exact hd | exact ⟨hd, hu⟩

/-- The kinds with tag `t`. -/
def kindsOfTag (M : Machine) : ℕ → List (SKind M)
  | 0 => [.accept]
  | 1 => [.reject]
  | 2 => [.query]
  | 3 => (List.finRange 3 ×ˢ (List.finRange (M.tapes + 1) ×ˢ allCV M)).map
      fun a => .cell a.1 a.2.1 a.2.2
  | 4 => (List.finRange 3 ×ˢ allExt M).map fun a => .state a.1 a.2
  | 5 => (List.finRange 2 ×ˢ List.finRange (M.tapes + 1)).map fun a => .headIn a.1 a.2
  | 6 => (List.finRange 2 ×ˢ (List.finRange (M.tapes + 1) ×ˢ List.finRange 8)).map
      fun a => .headSet a.1 a.2.1 a.2.2
  | 7 => (List.finRange 2 ×ˢ (List.finRange (M.tapes + 1) ×ˢ (allCV M ×ˢ List.finRange 8))).map
      fun a => .restore a.1 a.2.1 a.2.2.1 a.2.2.2
  | 8 => (List.finRange 2 ×ˢ (List.finRange (M.tapes + 1) ×ˢ (allCV M ×ˢ List.finRange 8))).map
      fun a => .gather a.1 a.2.1 a.2.2.1 a.2.2.2
  | 9 => (List.finRange (M.tapes + 1) ×ˢ (allRows M ×ˢ (allCV M ×ˢ
      List.finRange (M.tapes + 2)))).map fun a => .baseCell a.1 a.2.1 a.2.2.1 a.2.2.2
  | 10 => (allRows M ×ˢ List.finRange (M.tapes + 2)).map fun a => .baseState a.1 a.2
  | 11 => (List.finRange (M.tapes + 1) ×ˢ (List.finRange 4 ×ˢ allCV M)).map
      fun a => .setJ a.1 a.2.1 a.2.2
  | _ => []

/-- The kind of a location. -/
def _root_.Lax119563Proofs.Circuits.Loc.kind {H : ℕ} : Loc M H → SKind M
  | .accept => .accept
  | .reject => .reject
  | .query => .query
  | .cell _ θ ν c => .cell θ ν c
  | .state _ θ p => .state θ p
  | .headIn _ θ ν _ => .headIn θ ν
  | .headSet _ θ ν β => .headSet θ ν β
  | .restore _ θ ν c β => .restore θ ν c β
  | .gather _ θ ν c β => .gather θ ν c β
  | .baseCell ν ρ old k => .baseCell ν ρ old k
  | .baseState ρ k => .baseState ρ k
  | .setJ ν h c => .setJ ν h c

lemma _root_.Lax119563Proofs.Circuits.Loc.kind_spec {H : ℕ} (L : Loc M H) :
    L.kind ∈ kindsOfTag M L.tuple.1 ∧
      L.kind.Valid H L.tuple.2.1 L.tuple.2.2.2.2.1 ∧
      L.kind.loc H L.tuple.2.1 L.tuple.2.2.2.2.1 = L := by
  cases L with
  | accept => exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple], trivial, rfl⟩
  | reject => exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple], trivial, rfl⟩
  | query => exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple], trivial, rfl⟩
  | cell d θ ν c =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product],
      by have := d.isLt; simp only [Loc.kind, Loc.tuple, SKind.Valid]; omega,
      by simp only [Loc.kind, Loc.tuple, SKind.loc, finH_eq rfl]⟩
  | state d θ p =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product],
      by have := d.isLt; simp only [Loc.kind, Loc.tuple, SKind.Valid]; omega,
      by simp only [Loc.kind, Loc.tuple, SKind.loc, finH_eq rfl]⟩
  | headIn d θ ν u =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product],
      by have := d.isLt; have := u.isLt; simp only [Loc.kind, Loc.tuple, SKind.Valid]; omega,
      by simp only [Loc.kind, Loc.tuple, SKind.loc, finH_eq rfl]⟩
  | headSet d θ ν β =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product],
      by have := d.isLt; simp only [Loc.kind, Loc.tuple, SKind.Valid]; omega,
      by simp only [Loc.kind, Loc.tuple, SKind.loc, finH_eq rfl]⟩
  | restore d θ ν c β =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product],
      by have := d.isLt; simp only [Loc.kind, Loc.tuple, SKind.Valid]; omega,
      by simp only [Loc.kind, Loc.tuple, SKind.loc, finH_eq rfl]⟩
  | gather d θ ν c β =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product],
      by have := d.isLt; simp only [Loc.kind, Loc.tuple, SKind.Valid]; omega,
      by simp only [Loc.kind, Loc.tuple, SKind.loc, finH_eq rfl]⟩
  | baseCell ν ρ old k =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product], trivial, rfl⟩
  | baseState ρ k =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product], trivial, rfl⟩
  | setJ ν h c =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product], trivial, rfl⟩

lemma tag_of_mem_kindsOfTag {t : ℕ} {K : SKind M} (h : K ∈ kindsOfTag M t) {H d u : ℕ} :
    (K.loc H d u).tuple.1 = t := by
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | t <;>
    simp only [kindsOfTag, List.mem_map, List.mem_singleton, List.not_mem_nil] at h <;>
    first
    | (subst h; rfl)
    | (obtain ⟨a, -, rfl⟩ := h; rfl)
    | exact h.elim

section Correct

variable {x : List Bool} {ℓ H : ℕ} {ρ : List ℕ} {V : RVals} {d u : ℕ}

lemma finH_dpred (hd : d ≤ H) (_h0 : d ≠ 0) :
    finH H (d - 1) = dpred (finH H d) := Fin.ext (by simp [finH, dpred]; omega)

lemma finH_zero : finH H 0 = 0 := Fin.ext (by simp [finH])

lemma finH_dsucc (hd : d < H) :
    finH H (d + 1) = dsucc (finH H d) (by simp [finH]; omega) :=
  Fin.ext (by simp [finH, dsucc]; omega)

lemma finH_self : finH H H = ⟨H, by omega⟩ := Fin.ext (by simp [finH])

lemma selBr_cons {α : Type} (c : Xp) (ms : List α) (rest : List (Xp × List α)) :
    selBr ρ ((c, ms) :: rest) = if c.eval ρ ≠ 0 then ms else selBr ρ rest := rfl

/-- **The symbolic moves are the moves.** -/
theorem moves_eq (hV : V.Ok H ρ d u) (K : SKind M) (hK : K.Valid H d u) :
    (selBr ρ (K.brs (s := s) V)).map (SMv.eval M x s ℓ H ρ) = moves M x s ℓ H (K.loc H d u) := by
  have e1 := hV.d; have e2 := hV.u; have e3 := hV.dm1; have e4 := hV.um1; have e5 := hV.hd1
  have e6 := hV.hd2; have e7 := hV.H
  cases K with
  | accept => rfl
  | reject => rfl
  | query =>
    simp only [SKind.brs, SKind.loc, moves, selBr_cons, Xp.eval_const, ne_eq, one_ne_zero,
      not_false_eq_true, if_true, List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp [SMv.eval, SMv.goto, Move.goto, SLoc.eval, finH_zero]
  | cell θ ν c =>
    have hd : (finH H d).val = d := finH_val hK
    simp only [SKind.brs, SKind.loc, moves, hd]
    by_cases hθ : θ.val = 0
    · rw [if_pos hθ, if_pos hθ]
      by_cases h0 : d = 0
      · rw [if_pos h0, selBr_cons, if_pos (by simp [e1, h0])]
        by_cases hc : c = (0, false)
        · rw [if_pos hc, if_pos hc, List.map_cons, List.map_map]
          rfl
        · rw [if_neg hc, if_neg hc]
          simp [SMv.eval, SLoc.eval]
      · rw [if_neg h0, selBr_cons, if_neg (by simp [e1, h0]), selBr_cons, if_pos (by simp),
          List.map_flatMap]
        refine List.flatMap_congr fun θ' _ => ?_
        rw [List.map_map]
        refine List.map_congr_left fun β _ => ?_
        simp only [Function.comp, SMv.eval, SLoc.eval, e3, e6, finH_dpred hK h0, bpos]
        congr 1
        omega
    · rw [if_neg hθ, if_neg hθ]
      by_cases hlt : d < H
      · rw [dif_pos hlt, selBr_cons, if_pos (by simp [e1, e7, hlt]), List.map_map]
        refine List.map_congr_left fun β _ => ?_
        simp [SMv.eval, SMv.fork', Move.fork', SLoc.eval, e1]
      · rw [dif_neg hlt, selBr_cons, if_neg (by simp [e1, e7, hlt]), selBr_cons,
          if_pos (by simp)]
        by_cases h2 : θ.val = 2
        · rw [if_pos h2, if_pos h2, List.map_flatMap]
          refine List.flatMap_congr fun ρ' _ => ?_
          rw [List.map_flatMap]
          refine List.flatMap_congr fun old _ => ?_
          rw [List.map_map]
          refine List.map_congr_left fun jj _ => ?_
          rfl
        · rw [if_neg h2, if_neg h2]; rfl
  | state θ p =>
    have hd : (finH H d).val = d := finH_val hK
    simp only [SKind.brs, SKind.loc, moves, hd]
    by_cases hθ : θ.val = 0
    · rw [if_pos hθ, if_pos hθ]
      by_cases h0 : d = 0
      · rw [if_pos h0, selBr_cons, if_pos (by simp [e1, h0])]
        by_cases hp : p = (0, none)
        · rw [if_pos hp, if_pos hp]; rfl
        · rw [if_neg hp, if_neg hp]; rfl
      · rw [if_neg h0, selBr_cons, if_neg (by simp [e1, h0]), selBr_cons, if_pos (by simp),
          List.map_map]
        refine List.map_congr_left fun θ' _ => ?_
        simp only [Function.comp, SMv.eval, SLoc.eval, e3, e6, finH_dpred hK h0, bpos]
        congr 1
        omega
    · rw [if_neg hθ, if_neg hθ]
      by_cases hlt : d < H
      · rw [dif_pos hlt, selBr_cons, if_pos (by simp [e1, e7, hlt]), List.map_map]
        refine List.map_congr_left fun e _ => ?_
        simp only [Function.comp, SMv.eval, SLoc.eval, Xp.eval_add, Xp.eval_const, e1, e5, bpos,
          finH_dsucc hlt]
      · rw [dif_neg hlt, selBr_cons, if_neg (by simp [e1, e7, hlt]), selBr_cons,
          if_pos (by simp)]
        by_cases h2 : θ.val = 2
        · rw [if_pos h2, if_pos h2, List.map_map]
          refine List.map_congr_left fun ρ' _ => ?_
          rfl
        · rw [if_neg h2, if_neg h2]; rfl
  | headIn θ ν =>
    have hd : (finH H d).val = d := finH_val hK.1
    have hu : (finH H u).val = u := finH_val hK.2
    simp only [SKind.brs, SKind.loc, moves, hd, hu]
    have hand : ∀ a b : Xp, a.eval ρ ≤ 1 → b.eval ρ ≤ 1 →
        ((Xp.and a b).eval ρ ≠ 0 ↔ a.eval ρ = 1 ∧ b.eval ρ = 1) := fun a b ha hb => by
      rw [Xp.eval_and ha hb]; split_ifs <;> simp_all
    have l1 : (Xp.lt (Xp.add V.u V.d) V.H).eval ρ ≤ 1 := by simp only [Xp.eval_lt_eq]; split_ifs <;> omega
    have l2 : (Xp.eq V.u (Xp.const 0)).eval ρ ≤ 1 := by simp only [Xp.eval_eq]; split_ifs <;> omega
    by_cases hlt : u < H - d
    · rw [if_pos hlt]
      by_cases h0 : u = 0
      · rw [if_pos h0, selBr_cons, if_pos (by rw [hand _ _ l1 l2]; simp [e1, e2, e7, h0]; omega),
          List.map_map]
        refine List.map_congr_left fun γ _ => ?_
        simp [SMv.eval, SMv.goto, Move.goto, SLoc.eval, e1]
      · rw [if_neg h0, selBr_cons, if_neg (by rw [hand _ _ l1 l2]; simp [e2, h0]),
          selBr_cons, if_pos (by simp [e1, e2, e7]; omega), List.map_flatMap]
        refine List.flatMap_congr fun e _ => ?_
        rw [List.map_map]
        refine List.map_congr_left fun e' _ => ?_
        simp only [Function.comp, SMv.eval, SLoc.eval, e1, e4, finH_dpred hK.2 h0]
    · rw [if_neg hlt, selBr_cons, if_neg (by rw [hand _ _ l1 l2]; simp [e1, e2, e7]; omega),
        selBr_cons, if_neg (by simp [e1, e2, e7]; omega)]
      rfl
  | headSet θ ν β =>
    have hd : (finH H d).val = d := finH_val hK
    simp only [SKind.brs, SKind.loc, moves, hd]
    by_cases hlt : d < H
    · rw [if_pos hlt, selBr_cons, if_pos (by simp [e1, e7, hlt]), List.map_map]
      refine List.map_congr_left fun q _ => ?_
      simp only [Function.comp, SMv.eval, SLoc.eval, e1, e5, bpos]
      congr 2
      exact Fin.ext (by simp [finH]; omega)
    · rw [if_neg hlt, selBr_cons, if_neg (by simp [e1, e7, hlt])]; rfl
  | restore θ ν c β =>
    have hd : (finH H d).val = d := finH_val hK
    simp only [SKind.brs, SKind.loc, moves, hd]
    by_cases hlt : d < H
    · rw [dif_pos hlt, selBr_cons, if_pos (by simp [e1, e7, hlt]), List.map_map]
      refine List.map_congr_left fun q _ => ?_
      simp only [Function.comp]
      split_ifs
      · simp only [SMv.eval, SLoc.eval, Xp.eval_add, Xp.eval_const, e1, e5, bpos,
          finH_dsucc hlt]
      · simp only [SMv.eval, SLoc.eval, e1, e5, bpos]
    · rw [dif_neg hlt, selBr_cons, if_neg (by simp [e1, e7, hlt])]; rfl
  | gather θ ν c β =>
    have hd : (finH H d).val = d := finH_val hK
    simp only [SKind.brs, SKind.loc, moves, hd]
    by_cases hlt : d < H
    · rw [if_pos hlt, selBr_cons, if_pos (by simp [e1, e7, hlt]), List.map_map]
      refine List.map_congr_left fun c' _ => ?_
      simp only [Function.comp, SMv.eval, SLoc.eval, e1, e5, bpos]
    · rw [if_neg hlt, selBr_cons, if_neg (by simp [e1, e7, hlt])]; rfl
  | baseCell ν ρ' old k =>
    simp only [SKind.brs, SKind.loc, moves, selBr_cons, Xp.eval_const, ne_eq, one_ne_zero,
      not_false_eq_true, if_true]
    split_ifs
    · rfl
    · simp [SMv.eval, SMv.fork', Move.fork', SLoc.eval, e7, finH_self]
  | baseState ρ' k =>
    simp only [SKind.brs, SKind.loc, moves, selBr_cons, Xp.eval_const, ne_eq, one_ne_zero,
      not_false_eq_true, if_true]
    split_ifs
    · rfl
    · simp [SMv.eval, SMv.goto, Move.goto, SLoc.eval, e7, finH_self]
  | setJ ν h c =>
    simp only [SKind.brs, SKind.loc, moves, selBr_cons, Xp.eval_const, ne_eq, one_ne_zero,
      not_false_eq_true, if_true, List.map_map]
    refine List.map_congr_left fun q _ => ?_
    simp [SMv.eval, SLoc.eval, e7, finH_self]

end Correct

end Lax119563Proofs.Reduction
