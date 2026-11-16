import Lax119563Proofs.Reduction.CmdStk

/-!
# The schema enumerator

`schEnum M s b HX RX NX rX p0X EcX body` runs `body` once for every schema of the compiled
code-ordered time program, in order, on a stack of length `b + 37` extending `ρ` (the
globals, `ρ.length = b`), with the schema index at level `b + 27` and the record
`[tern, u, v, en, msk, gk, g1, g2, g3]` at levels `b + 28 … b + 36` (`SchRec`: the numbers
of the schema in the sense of `SchMatch`, and its domain `guardDomain (toGuard g) true` for
the guard `g` described by `gk, g1, g2, g3` (`GDescQ`: `GDesc`, or the query guard `v = 0`
for `gk = 3`)).

Inside the command enumerator, the index `j` of the command and the index `e₀` of its first
schema are computed by counting the commands with a smaller key (`length_out_before`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Matrix

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

/-- The body of the command enumerator: count `j` (level `b + 25`) and `e₀` (level
`b + 26`), then run `body` for the schemas of the command. -/
def cmdBody (b : ℕ) (HX RX NX : Xp) (body : Gn) : Gn :=
  .count (cmdEnum M s (b + 26) HX RX (Gn.when (beforeX b (b + 26)) (.emit (const 0))))
    (.count (cmdEnum M s (b + 27) HX RX (Gn.when (beforeX b (b + 27))
        (.ite (var (b + 27 + 17)) (Gn.emitN 9) (Gn.emitN 4))))
      (.ite (var (b + 17)) (Gn.blkGen (var (b + 26)) (gdX b) body (forkBlk NX b))
        (Gn.blkGen (var (b + 26)) (gdX b) body (assignBlk NX b))))

/-- The location number `N + 8 r + t` of detector slot `t`. -/
def detX (NX rX : Xp) (t : ℕ) : Xp := add (add NX (mulC 8 rX)) (const t)

/-- The detector schemas (padded to the same depth). -/
def detGen (NX rX p0X EcX : Xp) (body : Gn) : Gn :=
  Gn.bindL (List.replicate 27 (const 0))
    (Gn.blkGen EcX [const 3, const 0, const 0, const 0] body
      (gadgetX p0X (const 0) (detX NX rX 0) (detX NX rX 1) (detX NX rX 2) (detX NX rX 3)))

/-- **The schema enumerator.** -/
def schEnum (b : ℕ) (HX RX NX rX p0X EcX : Xp) (body : Gn) : Gn :=
  .seq (cmdEnum M s b HX RX (cmdBody M s b HX RX NX body)) (detGen NX rX p0X EcX body)

end Gens

end Lax119563Proofs.Reduction
