import Lax119563Proofs.Circuits.MoveProgram
import Lax119563Proofs.Circuits.Windows

/-!
# The verifier program

The control locations and moves of the register program simulating a machine `M` on input
`x`, for the horizon `H` (later `H = s ℓ - 2`). The address `A` of a claim at depth `d` holds
the call `ω = A / 2^(H - d + 2)` and the window position `j = A % 2^(H - d + 2)`. For a call
at depth `d < H`, the bits `H - d - 1, H - d, H - d + 1` of `A` form the block number of `j`
(blocks of size `2^(H - d - 1)`); the top one of them is the phase bit of a child claim.

Locations:
* `cell d θ ν c`, `state d θ p`, `headIn d θ ν u`: the claims (see `Sem`);
* `headSet`, `restore`, `gather`: the field rewrites of the head test, the restore rule and
  the gather rule, after the head block `β` has been guessed;
* `baseCell`, `baseState`, `setJ`: the fork chains of the base calls;
* `query`, `accept`, `reject`.

The input enters only through the guards `hitGuard` (membership tables of register `0`).
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

/-- A guessed row of a base call: the extended state, the head positions (`1` or `2`, stored
as `0` or `1`) and the scanned symbols. -/
abbrev Row (M : Machine) := ExtState M × (Tape M → Fin 2) × (Tape M → Sym M)

/-- Control locations of the verifier. -/
inductive Loc (M : Machine) (H : ℕ) where
  | accept
  | reject
  | query
  | cell (d : Fin (H + 1)) (θ : Fin 3) (ν : Tape M) (c : CellVal M)
  | state (d : Fin (H + 1)) (θ : Fin 3) (p : ExtState M)
  | headIn (d : Fin (H + 1)) (θ : Fin 2) (ν : Tape M) (u : Fin (H + 1))
  | headSet (d : Fin (H + 1)) (θ : Fin 2) (ν : Tape M) (β : Fin 8)
  | restore (d : Fin (H + 1)) (θ : Fin 2) (ν : Tape M) (c : CellVal M) (β : Fin 8)
  | gather (d : Fin (H + 1)) (θ : Fin 2) (ν : Tape M) (c : CellVal M) (β : Fin 8)
  | baseCell (ν : Tape M) (ρ : Row M) (old : CellVal M) (k : Fin (M.tapes + 2))
  | baseState (ρ : Row M) (k : Fin (M.tapes + 2))
  | setJ (ν : Tape M) (h : Fin 4) (c : CellVal M)

/-! ## Enumerations -/

/-- All Booleans. -/
def allBool : List Bool := [false, true]
/-- All optional Booleans. -/
def allOptBool : List (Option Bool) := [none, some false, some true]
/-- All cell values. -/
def allCV (M : Machine) : List (CellVal M) := List.finRange _ ×ˢ allBool
/-- All extended states. -/
def allExt (M : Machine) : List (ExtState M) := List.finRange _ ×ˢ allOptBool
/-- All functions `Fin m → Fin n`. -/
def allFun (m n : ℕ) : List (Fin m → Fin n) := (List.finRange _).map finFunctionFinEquiv.symm
/-- All rows. -/
def allRows (M : Machine) : List (Row M) :=
  allExt M ×ˢ (allFun (M.tapes + 1) 2 ×ˢ allFun (M.tapes + 1) (M.symbols + 3))

@[simp] lemma mem_allBool (b : Bool) : b ∈ allBool := by cases b <;> simp [allBool]
@[simp] lemma mem_allOptBool (b : Option Bool) : b ∈ allOptBool := by
  rcases b with _ | _ | _ <;> simp [allOptBool]
@[simp] lemma mem_allCV {M : Machine} (c : CellVal M) : c ∈ allCV M := by
  obtain ⟨a, b⟩ := c
  simp [allCV, List.mem_product]
@[simp] lemma mem_allExt {M : Machine} (p : ExtState M) : p ∈ allExt M := by
  obtain ⟨a, b⟩ := p
  simp [allExt, List.mem_product]
@[simp] lemma mem_allFun {m n : ℕ} (f : Fin m → Fin n) : f ∈ allFun m n := by
  simp only [allFun, List.mem_map, List.mem_finRange, true_and]
  exact ⟨_, Equiv.symm_apply_apply _ _⟩
@[simp] lemma mem_allRows {M : Machine} (ρ : Row M) : ρ ∈ allRows M := by
  obtain ⟨a, b, c⟩ := ρ
  simp [allRows, List.mem_product]

section Defs

variable (M : Machine) (x : List Bool) (s ℓ H : ℕ)

/-- The start of the block field of a call at depth `d < H`. -/
def bpos (d : ℕ) : ℕ := H - d - 1

/-- The guard of a root cell at a position `T + u` with `u < 2^ℓ` (register `0` holds `u`,
the other registers agree with `T = 2^H`) whose initial value is `c`. -/
def hitGuard (ν : Tape M) (c : CellVal M) : Fin s → ℕ → Bool :=
  fun i v => if i.val = 0 then decide (cfgCell (init M x) ν (v : ℤ) = c)
    else decide (v = field (2 ^ H) (i * ℓ) ℓ)

/-- The guard of a root cell outside `[T, T + 2^ℓ)`: register `i₀ ≠ 0` differs from `T`. -/
def missGuard (i₀ : Fin s) : Fin s → ℕ → Bool :=
  fun i v => if i = i₀ then decide (v ≠ field (2 ^ H) (i * ℓ) ℓ) else true

variable {M H}

/-- Depth `d + 1` for `d < H`. -/
def dsucc (d : Fin (H + 1)) (h : d.val < H) : Fin (H + 1) := ⟨d.val + 1, by omega⟩

/-- Depth `d - 1`. -/
def dpred (d : Fin (H + 1)) : Fin (H + 1) := ⟨d.val - 1, by omega⟩

/-- The previous phase `θ - 1` for `θ ∈ {1, 2}`. -/
def ppred (θ : Fin 3) : Fin 2 := ⟨(θ.val - 1) % 2, Nat.mod_lt _ (by norm_num)⟩

variable (M H)

/-- The moves at each location. -/
def moves : Loc M H → List (Move (Loc M H) s)
  | .accept => []
  | .reject => []
  | .query =>
    ((allExt M).filter fun p => decide (p.2 = some true)).map fun p => .goto (.state 0 2 p)
  | .cell d θ ν c =>
    if θ.val = 0 then
      if d.val = 0 then
        .test (hitGuard M x s ℓ H ν c) .accept ::
          (if c = (0, false) then
            ((List.finRange s).filter fun i => decide (i.val ≠ 0)).map fun i =>
              .test (missGuard s ℓ H i) .accept
          else [])
      else
        (List.finRange 2).flatMap fun (θ' : Fin 2) => (List.finRange 8).map fun β =>
          .fork (bpos H (d.val - 1) + 2) 1 θ'.val (.headSet (dpred d) θ' ν β)
            (.gather (dpred d) θ' ν c β)
    else if h : d.val < H then
      (List.finRange 8).map fun β =>
        .fork' (.headSet d (ppred θ) ν β) (.restore d (ppred θ) ν c β)
    else if θ.val = 2 then
      (allRows M).flatMap fun ρ => (allCV M).flatMap fun old =>
        ((List.finRange 4).filter fun jj =>
          decide (nextCell ρ.1 ρ.2.2 ν ((ρ.2.1 ν).val + 1 : ℤ) (jj.val : ℤ) old = c)).map
          fun jj => .step 0 2 jj.val jj.val (.baseCell ν ρ old 0)
    else []
  | .state d θ p =>
    if θ.val = 0 then
      if d.val = 0 then
        (if p = (0, none) then [.goto .accept] else [])
      else
        (List.finRange 2).map fun (θ' : Fin 2) =>
          .step (bpos H (d.val - 1) + 2) 1 θ'.val θ'.val (.state (dpred d) θ'.castSucc p)
    else if h : d.val < H then
      (List.finRange 2).map fun (e : Fin 2) =>
        .step (bpos H d + 2) 1 e.val (ppred θ).val (.state (dsucc d h) 2 p)
    else if θ.val = 2 then
      ((allRows M).filter fun ρ => decide (nextExt ρ.1 ρ.2.2 = p)).map fun ρ =>
        .goto (.baseState ρ 0)
    else []
  | .headIn d θ ν u =>
    if u.val < H - d.val then
      if u.val = 0 then
        (List.finRange (M.symbols + 3)).map fun γ => .goto (.cell d θ.castSucc ν (γ, true))
      else
        (List.finRange 2).flatMap fun (e : Fin 2) => (List.finRange 2).map fun (e' : Fin 2) =>
          .step (u.val - 1) 1 e.val e'.val (.headIn d θ ν (dpred u))
    else []
  | .headSet d θ ν β =>
    if d.val < H then
      (List.finRange 8).map fun (q : Fin 8) =>
        .step (bpos H d) 3 q.val β.val (.headIn d θ ν ⟨bpos H d, by unfold bpos; omega⟩)
    else []
  | .restore d θ ν c β =>
    if h : d.val < H then
      (List.finRange 8).map fun (q : Fin 8) =>
        if sel β ≤ q.val ∧ q.val < sel β + 4 then
          .step (bpos H d) 3 q.val (4 * θ.val + (q.val - sel β)) (.cell (dsucc d h) 2 ν c)
        else .step (bpos H d) 3 q.val q.val (.cell d θ.castSucc ν c)
    else []
  | .gather d θ ν c β =>
    if d.val < H then
      (List.finRange 4).map fun (c' : Fin 4) =>
        .step (bpos H d) 3 (4 * θ.val + c'.val) (sel β + c'.val) (.cell d θ.castSucc ν c)
    else []
  | .baseCell ν ρ old k =>
    if h : k.val < M.tapes + 1 then
      [.fork' (.setJ ⟨k.val, h⟩ ⟨(ρ.2.1 ⟨k.val, h⟩).val + 1, by omega⟩ (ρ.2.2 ⟨k.val, h⟩, true))
        (.baseCell ν ρ old ⟨k.val + 1, by omega⟩)]
    else [.fork' (.state ⟨H, by omega⟩ 0 ρ.1) (.cell ⟨H, by omega⟩ 0 ν old)]
  | .baseState ρ k =>
    if h : k.val < M.tapes + 1 then
      [.fork' (.setJ ⟨k.val, h⟩ ⟨(ρ.2.1 ⟨k.val, h⟩).val + 1, by omega⟩ (ρ.2.2 ⟨k.val, h⟩, true))
        (.baseState ρ ⟨k.val + 1, by omega⟩)]
    else [.goto (.state ⟨H, by omega⟩ 0 ρ.1)]
  | .setJ ν h c =>
    (List.finRange 4).map fun (q : Fin 4) => .step 0 2 q.val h.val (.cell ⟨H, by omega⟩ 0 ν c)

/-- All locations. -/
def allLocs : List (Loc M H) :=
  [.accept, .reject, .query] ++
  ((List.finRange (H + 1) ×ˢ (List.finRange 3 ×ˢ (List.finRange _ ×ˢ allCV M))).map
    fun a => .cell a.1 a.2.1 a.2.2.1 a.2.2.2) ++
  ((List.finRange (H + 1) ×ˢ (List.finRange 3 ×ˢ allExt M)).map
    fun a => .state a.1 a.2.1 a.2.2) ++
  ((List.finRange (H + 1) ×ˢ (List.finRange 2 ×ˢ (List.finRange _ ×ˢ List.finRange (H + 1)))).map
    fun a => .headIn a.1 a.2.1 a.2.2.1 a.2.2.2) ++
  ((List.finRange (H + 1) ×ˢ (List.finRange 2 ×ˢ (List.finRange _ ×ˢ List.finRange 8))).map
    fun a => .headSet a.1 a.2.1 a.2.2.1 a.2.2.2) ++
  ((List.finRange (H + 1) ×ˢ (List.finRange 2 ×ˢ (List.finRange _ ×ˢ
    (allCV M ×ˢ List.finRange 8)))).map
    fun a => .restore a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) ++
  ((List.finRange (H + 1) ×ˢ (List.finRange 2 ×ˢ (List.finRange _ ×ˢ
    (allCV M ×ˢ List.finRange 8)))).map
    fun a => .gather a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) ++
  ((List.finRange _ ×ˢ (allRows M ×ˢ (allCV M ×ˢ List.finRange _))).map
    fun a => .baseCell a.1 a.2.1 a.2.2.1 a.2.2.2) ++
  ((allRows M ×ˢ List.finRange _).map fun a => .baseState a.1 a.2) ++
  ((List.finRange _ ×ˢ (List.finRange 4 ×ˢ allCV M)).map fun a => .setJ a.1 a.2.1 a.2.2)

lemma mem_allLocs (L : Loc M H) : L ∈ allLocs M H := by
  cases L <;> simp [allLocs, List.mem_product]

end Defs

end Lax119563Proofs.Circuits
