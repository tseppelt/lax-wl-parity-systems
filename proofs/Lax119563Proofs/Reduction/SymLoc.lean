import Lax119563Proofs.Reduction.CodeOrder
import Lax119563Proofs.Reduction.GEnum

/-!
# Symbolic locations and moves

Locations and moves of the verifier whose runtime fields (depths `d`, `u`) are expressions
`Xp` over the generator stack, while the constant-size fields are Lean values.
* `SLoc M`, `SLoc.eval H ρ : Loc M H` (runtime fields clamped to `≤ H` by `finH`),
  `SLoc.codeX R HX`: an expression for the location number (runtime fields clamped by
  `minX`); `SLoc.eval_codeX`: it evaluates to `Loc.code` when `R, HX` evaluate to
  `radix M H, H`.
* `SMv M s`: symbolic moves (`step`, `fork`, and the two kinds of tests), `SMv.eval` to a
  `Move`, and `SMv.recX R HX`: the eight numbers describing the command of the move
  (`CmdDesc`): kind (`0` assign, `1` fork), mask, the target location number(s), and the
  guard (`GDesc`: `0, k, m, q` for `fieldGuard ℓ k m q`, `1, ν, encCV c` for
  `hitGuard ν c`, `2, i` for `missGuard i`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime

variable {M : Machine}

/-- A natural number clamped into `Fin (H + 1)`. -/
def finH (H v : ℕ) : Fin (H + 1) := ⟨min v H, by omega⟩

lemma finH_val {H v : ℕ} (h : v ≤ H) : (finH H v).val = v := by simp [finH, h]

lemma finH_eq {H : ℕ} {v : ℕ} {d : Fin (H + 1)} (h : v = d.val) : finH H v = d :=
  Fin.ext (by simp only [finH]; have := d.isLt; omega)

open Xp in
/-- `min a h`. -/
def minX (a h : Xp) : Xp :=
  add (mul a (lt a (add h (const 1)))) (mul h (Xp.not (lt a (add h (const 1)))))

@[simp] lemma eval_minX {ρ : List ℕ} (a h : Xp) : (minX a h).eval ρ = min (a.eval ρ) (h.eval ρ) := by
  simp only [minX, Xp.eval_add, Xp.eval_mul]
  show a.eval ρ * (if a.eval ρ < h.eval ρ + 1 then 1 else 0) +
    h.eval ρ * (if (if a.eval ρ < h.eval ρ + 1 then 1 else 0) < 1 then 1 else 0) = _
  by_cases hc : a.eval ρ < h.eval ρ + 1 <;> simp [hc] <;> omega

lemma bnd_minX {n : ℕ} {a h : Xp} (ha : a.Bnd n) (hh : h.Bnd n) : (minX a h).Bnd n :=
  ⟨Xp.bnd_mul ha ⟨ha, hh, trivial⟩, Xp.bnd_mul hh ⟨⟨ha, hh, trivial⟩, trivial⟩⟩

/-! ## Symbolic locations -/

/-- Locations with runtime depth fields given by expressions. -/
inductive SLoc (M : Machine)
  | accept
  | reject
  | query
  | cell (d : Xp) (θ : Fin 3) (ν : Tape M) (c : CellVal M)
  | state (d : Xp) (θ : Fin 3) (p : ExtState M)
  | headIn (d : Xp) (θ : Fin 2) (ν : Tape M) (u : Xp)
  | headSet (d : Xp) (θ : Fin 2) (ν : Tape M) (β : Fin 8)
  | restore (d : Xp) (θ : Fin 2) (ν : Tape M) (c : CellVal M) (β : Fin 8)
  | gather (d : Xp) (θ : Fin 2) (ν : Tape M) (c : CellVal M) (β : Fin 8)
  | baseCell (ν : Tape M) (ρ : Row M) (old : CellVal M) (k : Fin (M.tapes + 2))
  | baseState (ρ : Row M) (k : Fin (M.tapes + 2))
  | setJ (ν : Tape M) (h : Fin 4) (c : CellVal M)

namespace SLoc

/-- The location denoted on the stack `ρ`. -/
def eval (H : ℕ) (ρ : List ℕ) : SLoc M → Loc M H
  | accept => .accept
  | reject => .reject
  | query => .query
  | cell d θ ν c => .cell (finH H (d.eval ρ)) θ ν c
  | state d θ p => .state (finH H (d.eval ρ)) θ p
  | headIn d θ ν u => .headIn (finH H (d.eval ρ)) θ ν (finH H (u.eval ρ))
  | headSet d θ ν β => .headSet (finH H (d.eval ρ)) θ ν β
  | restore d θ ν c β => .restore (finH H (d.eval ρ)) θ ν c β
  | gather d θ ν c β => .gather (finH H (d.eval ρ)) θ ν c β
  | baseCell ν ρ' old k => .baseCell ν ρ' old k
  | baseState ρ' k => .baseState ρ' k
  | setJ ν h c => .setJ ν h c

/-- The expressions read only stack levels below `n`. -/
def Bnd (n : ℕ) : SLoc M → Prop
  | cell d .. => d.Bnd n
  | state d .. => d.Bnd n
  | headIn d _ _ u => d.Bnd n ∧ u.Bnd n
  | headSet d .. => d.Bnd n
  | restore d .. => d.Bnd n
  | gather d .. => d.Bnd n
  | _ => True

/-- The tag of the location number. -/
def tag : SLoc M → ℕ
  | accept => 0
  | reject => 1
  | query => 2
  | cell .. => 3
  | state .. => 4
  | headIn .. => 5
  | headSet .. => 6
  | restore .. => 7
  | gather .. => 8
  | baseCell .. => 9
  | baseState .. => 10
  | setJ .. => 11

open Xp in
/-- The five fields of the location number (runtime fields clamped to `≤ H`). -/
def flds (HX : Xp) : SLoc M → Xp × Xp × Xp × Xp × Xp
  | accept => (const 0, const 0, const 0, const 0, const 0)
  | reject => (const 0, const 0, const 0, const 0, const 0)
  | query => (const 0, const 0, const 0, const 0, const 0)
  | cell d θ ν c => (minX d HX, const θ, const ν, const (encCV c), const 0)
  | state d θ p => (minX d HX, const θ, const (encExt p), const 0, const 0)
  | headIn d θ ν u => (minX d HX, const θ, const ν, minX u HX, const 0)
  | headSet d θ ν β => (minX d HX, const θ, const ν, const β, const 0)
  | restore d θ ν c β => (minX d HX, const θ, const ν, const (encCV c), const β)
  | gather d θ ν c β => (minX d HX, const θ, const ν, const (encCV c), const β)
  | baseCell ν ρ old k => (const ν, const (encRow ρ), const (encCV old), const k, const 0)
  | baseState ρ k => (const (encRow ρ), const k, const 0, const 0, const 0)
  | setJ ν h c => (const ν, const h, const (encCV c), const 0, const 0)

open Xp in
/-- The location number in mixed radix `16, R, R, R, R, R`. -/
def codeX (R HX : Xp) (L : SLoc M) : Xp :=
  add (const L.tag) (mulC 16 (add (L.flds HX).1 (mul (add (L.flds HX).2.1 (mul (add
    (L.flds HX).2.2.1 (mul (add (L.flds HX).2.2.2.1 (mul (L.flds HX).2.2.2.2 R)) R)) R)) R)))

lemma bnd_codeX {n : ℕ} {R HX : Xp} (hR : R.Bnd n) (hH : HX.Bnd n) (L : SLoc M)
    (hL : L.Bnd n) : (codeX R HX L).Bnd n := by
  have h0 : ∀ c, (Xp.const c).Bnd n := fun _ => trivial
  have hm : ∀ {a : Xp}, a.Bnd n → (minX a HX).Bnd n := fun ha => bnd_minX ha hH
  refine ⟨trivial, Xp.bnd_mulC ?_ 16⟩
  cases L <;> simp only [flds, Bnd] at hL ⊢ <;>
    first
    | exact ⟨h0 _, Xp.bnd_mul ⟨h0 _, Xp.bnd_mul ⟨h0 _, Xp.bnd_mul ⟨h0 _, Xp.bnd_mul
        (h0 _) hR⟩ hR⟩ hR⟩ hR⟩
    | exact ⟨hm hL, Xp.bnd_mul ⟨h0 _, Xp.bnd_mul ⟨h0 _, Xp.bnd_mul ⟨h0 _, Xp.bnd_mul
        (h0 _) hR⟩ hR⟩ hR⟩ hR⟩
    | exact ⟨hm hL.1, Xp.bnd_mul ⟨h0 _, Xp.bnd_mul ⟨h0 _, Xp.bnd_mul ⟨hm hL.2, Xp.bnd_mul
        (h0 _) hR⟩ hR⟩ hR⟩ hR⟩

lemma eval_codeX {H : ℕ} {R HX : Xp} {ρ : List ℕ} (hR : R.eval ρ = radix M H)
    (hH : HX.eval ρ = H) (L : SLoc M) :
    (codeX R HX L).eval ρ = (Loc.code (L.eval H ρ)).val := by
  cases L <;>
    simp only [codeX, flds, tag, eval, Loc.code, Loc.tuple, pack, Xp.eval_add, eval_minX,
      Xp.eval_mulC, Xp.eval_mul, Xp.eval_const, hR, hH, finH] <;> ring

end SLoc

/-! ## Symbolic moves -/

/-- Moves with runtime field positions given by expressions. -/
inductive SMv (M : Machine) (s : ℕ)
  | step (k : Xp) (m q v : ℕ) (dst : SLoc M)
  | fork (k : Xp) (m q : ℕ) (l r : SLoc M)
  | hit (ν : Tape M) (c : CellVal M) (dst : SLoc M)
  | miss (i : Fin s) (dst : SLoc M)

namespace SMv

variable {s : ℕ}

/-- The move denoted on the stack `ρ`. -/
def eval (M : Machine) (x : List Bool) (s ℓ H : ℕ) (ρ : List ℕ) :
    SMv M s → Move (Loc M H) s
  | step k m q v dst => .step (k.eval ρ) m q v (dst.eval H ρ)
  | fork k m q l r => .fork (k.eval ρ) m q (l.eval H ρ) (r.eval H ρ)
  | hit ν c dst => .test (hitGuard M x s ℓ H ν c) (dst.eval H ρ)
  | miss i dst => .test (missGuard s ℓ H i) (dst.eval H ρ)

/-- The expressions read only stack levels below `n`. -/
def Bnd (n : ℕ) : SMv M s → Prop
  | step k _ _ _ dst => k.Bnd n ∧ dst.Bnd n
  | fork k _ _ l r => k.Bnd n ∧ l.Bnd n ∧ r.Bnd n
  | hit _ _ dst => dst.Bnd n
  | miss _ dst => dst.Bnd n

open Xp in
/-- The eight numbers of the command of a move. -/
def recX (R HX : Xp) : SMv M s → List Xp
  | step k m q v dst => [const 0, shl (const (q ^^^ v)) k, dst.codeX R HX, const 0,
      const 0, k, const m, const q]
  | fork k m q l r => [const 1, const 0, l.codeX R HX, r.codeX R HX, const 0, k, const m, const q]
  | hit ν c dst => [const 0, const 0, dst.codeX R HX, const 0, const 1, const ν, const (encCV c),
      const 0]
  | miss i dst => [const 0, const 0, dst.codeX R HX, const 0, const 2, const i, const 0, const 0]

lemma bnd_rec {n : ℕ} {R HX : Xp} (hR : R.Bnd n) (hH : HX.Bnd n) (m : SMv M s)
    (hm : m.Bnd n) : ∀ e ∈ m.recX R HX, e.Bnd n := by
  cases m with
  | step k m q v dst =>
    simp only [recX, List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | trivial | exact ⟨trivial, hm.1⟩ | exact SLoc.bnd_codeX hR hH _ hm.2 | exact hm.1
  | fork k m q l r =>
    simp only [recX, List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | trivial | exact SLoc.bnd_codeX hR hH _ hm.2.1 |
      exact SLoc.bnd_codeX hR hH _ hm.2.2 | exact hm.1
  | hit ν c dst =>
    simp only [recX, List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | trivial | exact SLoc.bnd_codeX hR hH _ hm
  | miss i dst =>
    simp only [recX, List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | trivial | exact SLoc.bnd_codeX hR hH _ hm

end SMv

/-! ## Numeric descriptions of commands -/

section Desc

variable (M : Machine) (x : List Bool) (s ℓ H : ℕ)

/-- The four numbers `gd` describe the guard `g`. -/
def GDesc (g : Fin s → ℕ → Bool) (gd : List ℕ) : Prop :=
  (gd.getD 0 0 = 0 ∧ g = fieldGuard ℓ (gd.getD 1 0) (gd.getD 2 0) (gd.getD 3 0)) ∨
  (gd.getD 0 0 = 1 ∧ ∃ (ν : Tape M) (c : CellVal M), ν.val = gd.getD 1 0 ∧
    encCV c = gd.getD 2 0 ∧ g = hitGuard M x s ℓ H ν c) ∨
  (gd.getD 0 0 = 2 ∧ ∃ i : Fin s, i.val = gd.getD 1 0 ∧ g = missGuard s ℓ H i)

/-- The eight numbers `r` describe the command (without its source). -/
def CmdDesc : ACmd (Loc M H) s → List ℕ → Prop
  | .assign _ g m q, r => r.length = 8 ∧ r.getD 0 0 = 0 ∧ r.getD 1 0 = m ∧
      r.getD 2 0 = (Loc.code q).val ∧ GDesc M x s ℓ H g (r.drop 4)
  | .fork _ g q q', r => r.length = 8 ∧ r.getD 0 0 = 1 ∧ r.getD 2 0 = (Loc.code q).val ∧
      r.getD 3 0 = (Loc.code q').val ∧ GDesc M x s ℓ H g (r.drop 4)

end Desc

lemma SMv.desc {s ℓ H : ℕ} {x : List Bool} {R HX : Xp} {ρ : List ℕ} (hR : R.eval ρ = radix M H)
    (hH : HX.eval ρ = H) (src : Loc M H) (m : SMv M s) :
    CmdDesc M x s ℓ H (Move.toACmd ℓ src (m.eval M x s ℓ H ρ)) ((m.recX R HX).map (·.eval ρ)) := by
  cases m with
  | step k m q v dst =>
    refine ⟨rfl, rfl, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
    · simp [recX, fieldMask, Nat.shiftLeft_eq]
    · simp [recX, SLoc.eval_codeX hR hH]
  | fork k m q l r =>
    exact ⟨rfl, rfl, by simp [recX, SLoc.eval_codeX hR hH],
      by simp [recX, SLoc.eval_codeX hR hH], Or.inl ⟨rfl, rfl⟩⟩
  | hit ν c dst =>
    exact ⟨rfl, rfl, rfl, by simp [recX, SLoc.eval_codeX hR hH],
      Or.inr (Or.inl ⟨rfl, ν, c, rfl, rfl, rfl⟩)⟩
  | miss i dst =>
    exact ⟨rfl, rfl, rfl, by simp [recX, SLoc.eval_codeX hR hH],
      Or.inr (Or.inr ⟨rfl, i, rfl, rfl⟩)⟩

end Lax119563Proofs.Reduction
