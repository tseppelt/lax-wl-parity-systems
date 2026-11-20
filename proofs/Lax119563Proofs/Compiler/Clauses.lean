import Lax119563Proofs.Matrix.Edges
import Lax119563Proofs.Compiler.Transfer

/-!
# The game and size clauses for reordered matrix graphs

For any reordering `L` of the vertex list of the matrix construction (a list with the same
entries as `vertexList I`), the graphs `reGraph I L ε` (vertex `i` is the `i`-th name of `L`,
adjacency `adjN I ε`, color the position of the first name of the class) satisfy the game,
size and edge clauses of the matrix compiler with the constants of `matrixGraph`
(`reGraph_spec`). This leaves the choice of the vertex order to the construction machine.

* `duplicatorSurvives_of_corr`: Duplicator's survival transfers along a correspondence
  (the transfer lemma `survivesFrom_transfer` is round by round);
* `reEquiv`: the renumbering between two orders, `reCorr`, `numEdges_reGraph`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.PebbleGame Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

set_option linter.unnecessarySimpa false

/-- **Round-bounded transfer.** Duplicator survives `r` rounds on corresponding pairs
simultaneously. -/
theorem duplicatorSurvives_of_corr {n n' m : ℕ} {P : JunkPair n} {Q : JunkPair n'}
    (C : Corr P Q) (r : ℕ) (h : DuplicatorSurvives m r P.G₀ P.G₁) :
    DuplicatorSurvives m r Q.G₀ Q.G₁ :=
  ⟨rfl, survivesFrom_transfer C r _ _
    (fun _ => ⟨fun _ _ h => (by simp at h), fun _ => Or.inl rfl⟩) h.2⟩

theorem duplicatorSurvives_iff_of_corr {n n' m : ℕ} {P : JunkPair n} {Q : JunkPair n'}
    (C : Corr P Q) (r : ℕ) :
    DuplicatorSurvives m r P.G₀ P.G₁ ↔ DuplicatorSurvives m r Q.G₀ Q.G₁ :=
  ⟨duplicatorSurvives_of_corr C r, duplicatorSurvives_of_corr C.symm r⟩

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The matrix graph `G_ε` with its vertices in the order of `L`. -/
abbrev reGraph (L : List (VName I)) (ε : ZMod 2) : ColoredGraph :=
  listGraph L (adjN I ε) (adjN_symm I ε) (adjN_irrefl I ε) Prod.fst

/-- The reordered graphs as a pair without junk. -/
noncomputable def rePair (L : List (VName I)) : JunkPair L.length where
  A₀ := (reGraph I L 0).graph
  A₁ := (reGraph I L 1).graph
  χ := (reGraph I L 0).color
  J := fun _ => False
  iso₀ := fun _ _ h => h.elim
  iso₁ := fun _ _ h => h.elim
  col := fun _ _ h => h.elim

variable {I}

/-- The renumbering between two duplicate-free orders of the same names. -/
noncomputable def reEquiv {L L' : List (VName I)} (hL : L.Nodup) (hL' : L'.Nodup)
    (hp : L.Perm L') : Fin L.length ≃ Fin L'.length :=
  (hL.getEquiv L).trans ((Equiv.subtypeEquivRight fun _ => hp.mem_iff).trans
    (hL'.getEquiv L').symm)

lemma reEquiv_get {L L' : List (VName I)} (hL : L.Nodup) (hL' : L'.Nodup) (hp : L.Perm L')
    (i : Fin L.length) : L'[(reEquiv hL hL' hp i : ℕ)] = L[(i : ℕ)] := by
  have h := (hL'.getEquiv L').apply_symm_apply
    ((Equiv.subtypeEquivRight fun _ => hp.mem_iff) (hL.getEquiv L i))
  have h' := congrArg Subtype.val h
  simpa [reEquiv, List.Nodup.getEquiv] using h'

/-- The correspondence between two orders. -/
noncomputable def reCorr {L L' : List (VName I)} (hL : L.Nodup) (hL' : L'.Nodup)
    (hp : L.Perm L') : Corr (rePair I L) (rePair I L') where
  f :=
    { toFun := fun u => ⟨reEquiv hL hL' hp u.1, not_false⟩
      invFun := fun v => ⟨(reEquiv hL hL' hp).symm v.1, not_false⟩
      left_inv := fun u => by simp
      right_inv := fun v => by simp }
  adj₀ u v := by
    show adjN I 0 L[(u.1 : ℕ)] L[(v.1 : ℕ)] ↔
      adjN I 0 L'[(reEquiv hL hL' hp u.1 : ℕ)] L'[(reEquiv hL hL' hp v.1 : ℕ)]
    rw [reEquiv_get, reEquiv_get]
  adj₁ u v := by
    show adjN I 1 L[(u.1 : ℕ)] L[(v.1 : ℕ)] ↔
      adjN I 1 L'[(reEquiv hL hL' hp u.1 : ℕ)] L'[(reEquiv hL hL' hp v.1 : ℕ)]
    rw [reEquiv_get, reEquiv_get]
  col u v := by
    show (reGraph I L 0).color u.1 = (reGraph I L 0).color v.1 ↔
      (reGraph I L' 0).color (reEquiv hL hL' hp u.1) =
        (reGraph I L' 0).color (reEquiv hL hL' hp v.1)
    rw [listGraph_color_eq_iff, listGraph_color_eq_iff, reEquiv_get, reEquiv_get]

/-- Reordering preserves the number of edges. -/
lemma numEdges_reGraph {L L' : List (VName I)} (hL : L.Nodup) (hL' : L'.Nodup)
    (hp : L.Perm L') (ε : ZMod 2) : (reGraph I L ε).numEdges = (reGraph I L' ε).numEdges := by
  let e : (reGraph I L ε).graph ≃g (reGraph I L' ε).graph :=
    { toEquiv := reEquiv hL hL' hp
      map_rel_iff' := by
        intro a b
        show adjN I ε L'[((reEquiv hL hL' hp) a : ℕ)] L'[((reEquiv hL hL' hp) b : ℕ)] ↔
          adjN I ε L[(a : ℕ)] L[(b : ℕ)]
        rw [reEquiv_get, reEquiv_get] }
  exact Nat.card_congr e.mapEdgeSet

/-- **The clauses for every reordering of the vertex list.** -/
theorem reGraph_spec (hk : 3 ≤ k) (L : List (VName I)) (hp : L.Perm (vertexList I)) :
    (∀ τ : ℕ, I.conflictRound = τ →
      SpoilerWinsWithin (k + 1) ((2 * k + stepConst k) * Λ I * (τ + 1))
        (reGraph I L 0) (reGraph I L 1)) ∧
    (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound →
      DuplicatorSurvives (k + 1) r (reGraph I L 0) (reGraph I L 1)) ∧
    (reGraph I L 0).n + (reGraph I L 1).n ≤ 32 * matrixSize I ∧
    (reGraph I L 0).numEdges + (reGraph I L 1).numEdges ≤
      3 * ((reGraph I L 0).n + (reGraph I L 1).n) := by
  have hV := nodup_vertexList I
  have hL : L.Nodup := hp.nodup_iff.mpr hV
  have C := reCorr hV hL hp.symm
  have hlen : L.length = nV I := hp.length_eq
  have hnV : nV I = (vertexList I).length := rfl
  refine ⟨fun τ hτ hD => spoilerWins (by omega) hτ ((duplicatorSurvives_iff_of_corr C _).mpr hD),
    fun r hr => (duplicatorSurvives_iff_of_corr C r).mp
      (duplicatorSurvives (by omega) (not_hasConflict_of_lt I hr)), ?_, ?_⟩
  · show L.length + L.length ≤ 32 * matrixSize I
    have := card_vertexList_le (I := I) (by omega)
    omega
  · rw [numEdges_reGraph hL hV hp 0, numEdges_reGraph hL hV hp 1]
    have h0 : (reGraph I (vertexList I) 0).numEdges ≤ 3 * nV I := numEdges_le (I := I) 0
    have h1 : (reGraph I (vertexList I) 1).numEdges ≤ 3 * nV I := numEdges_le (I := I) 1
    show _ ≤ 3 * (L.length + L.length)
    omega

end Lax119563Proofs.Compiler
