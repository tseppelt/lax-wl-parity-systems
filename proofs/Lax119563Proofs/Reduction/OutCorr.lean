import Lax119563Proofs.Reduction.OutGraph

/-!
# The output graphs and their correspondence with the matrix graphs

`outGraph I ε`: vertices `0, …, nOut I - 1`; the number of a valid name is adjacent to the
number of another valid name iff the names are adjacent in `G_ε`; all other numbers are
isolated padding vertices of color `1`; a valid number `z` has color `2 (z / 4) + 2`.

`distinguishes_outGraph_iff`: `(s+1)`-WL distinguishes the output graphs iff it
distinguishes the matrix graphs.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.PebbleGame
open Lax119563.ImplicitParitySystems Lax119563Proofs.Matrix

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ} (I : ImplicitParitySystem (s + 1) ℓ)

/-- A number is valid if it is the number of a valid name. -/
def OutValid (z : ℕ) : Prop := ∃ a : VName I, Valid I a ∧ num I a = z

/-- Adjacency of numbers in the output graph `G'_ε`. -/
def outAdj (ε : ZMod 2) (u v : ℕ) : Prop :=
  ∃ a b : VName I, Valid I a ∧ Valid I b ∧ num I a = u ∧ num I b = v ∧ adjN I ε a b

lemma outAdj_symm (ε : ZMod 2) {u v : ℕ} (h : outAdj I ε u v) : outAdj I ε v u := by
  obtain ⟨a, b, ha, hb, rfl, rfl, h⟩ := h
  exact ⟨b, a, hb, ha, rfl, rfl, adjN_symm I ε a b h⟩

lemma outAdj_irrefl (ε : ZMod 2) (u : ℕ) : ¬ outAdj I ε u u := by
  rintro ⟨a, b, ha, hb, rfl, hab, h⟩
  rw [num_injective I hb ha hab] at h
  exact adjN_irrefl I ε a h

open Classical in
/-- The color of a number. -/
noncomputable def outColor (z : ℕ) : ℕ := if OutValid I z then 2 * (z / 4) + 2 else 1

/-- **The output graph** `G'_ε`. -/
noncomputable def outGraph (ε : ZMod 2) : ColoredGraph where
  n := nOut I
  graph :=
    { Adj := fun u v => outAdj I ε u v
      symm := ⟨fun _ _ h => outAdj_symm I ε h⟩
      loopless := ⟨fun u h => outAdj_irrefl I ε u h⟩ }
  color := fun z => outColor I z

/-! ## The correspondence -/

/-- The matrix graphs as a pair without junk. -/
noncomputable def matrixPair : JunkPair (vertexList I).length where
  A₀ := (matrixGraph I 0).graph
  A₁ := (matrixGraph I 1).graph
  χ := (matrixGraph I 0).color
  J := fun _ => False
  iso₀ := fun _ _ h => h.elim
  iso₁ := fun _ _ h => h.elim
  col := fun _ _ h => h.elim

lemma outAdj_valid {ε : ZMod 2} {u v : ℕ} (h : outAdj I ε u v) : OutValid I u := by
  obtain ⟨a, b, ha, hb, rfl, rfl, -⟩ := h
  exact ⟨a, ha, rfl⟩

/-- The output graphs as a pair with the invalid numbers as junk. -/
noncomputable def outPair : JunkPair (nOut I) where
  A₀ := (outGraph I 0).graph
  A₁ := (outGraph I 1).graph
  χ := (outGraph I 0).color
  J := fun z => ¬ OutValid I z
  iso₀ := fun _ _ hu h => hu (outAdj_valid I h)
  iso₁ := fun _ _ hu h => hu (outAdj_valid I h)
  col := by
    intro u v hu hv
    simp only [outGraph, outColor, if_neg hu, if_pos (not_not.mp hv)]
    omega

lemma valid_getElem (i : Fin (vertexList I).length) : Valid I (vertexList I)[i] :=
  (mem_vertexList I _).mp (List.getElem_mem _)

lemma OutValid.lt {z : ℕ} (h : OutValid I z) : z < nOut I := by
  obtain ⟨a, ha, rfl⟩ := h
  exact num_lt I ha

/-- The bijection between the matrix vertices and the valid numbers. -/
noncomputable def corrEquiv :
    {u : Fin (vertexList I).length // ¬ (matrixPair I).J u} ≃
      {z : Fin (nOut I) // ¬ (outPair I).J z} :=
  Equiv.ofBijective
    (fun u => ⟨⟨num I (vertexList I)[u.1], num_lt I (valid_getElem I u.1)⟩,
      not_not.mpr ⟨_, valid_getElem I u.1, rfl⟩⟩)
    (by
      constructor
      · intro u v h
        have h' := congrArg (fun z : {z : Fin (nOut I) // ¬ (outPair I).J z} => (z.1 : ℕ)) h
        have := num_injective I (valid_getElem I u.1) (valid_getElem I v.1) h'
        have := (List.Nodup.getElem_inj_iff (nodup_vertexList I)).mp this
        exact Subtype.ext (Fin.ext (by simpa using this))
      · rintro ⟨z, hz⟩
        obtain ⟨a, ha, haz⟩ := not_not.mp hz
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((mem_vertexList I a).mpr ha)
        exact ⟨⟨⟨i, hi⟩, not_false⟩, Subtype.ext (Fin.ext haz)⟩)

lemma corrEquiv_apply (u : {u : Fin (vertexList I).length // ¬ (matrixPair I).J u}) :
    ((corrEquiv I u : Fin (nOut I)) : ℕ) = num I (vertexList I)[u.1] := rfl

lemma outAdj_num_iff (ε : ZMod 2) {a b : VName I} (ha : Valid I a) (hb : Valid I b) :
    outAdj I ε (num I a) (num I b) ↔ adjN I ε a b := by
  constructor
  · rintro ⟨a', b', ha', hb', h1, h2, h⟩
    rw [num_injective I ha' ha h1, num_injective I hb' hb h2] at h
    exact h
  · exact fun h => ⟨a, b, ha, hb, rfl, rfl, h⟩

lemma outColor_num {a : VName I} (ha : Valid I a) :
    outColor I (num I a) = 2 * classNum I a.1 + 2 := by
  rw [outColor, if_pos ⟨a, ha, rfl⟩, num_div_four]

/-- The correspondence between the matrix graphs and the output graphs. -/
noncomputable def corr : Corr (matrixPair I) (outPair I) where
  f := corrEquiv I
  adj₀ u v := by
    show (matrixGraph I 0).graph.Adj u.1 v.1 ↔ outAdj I 0 _ _
    rw [corrEquiv_apply, corrEquiv_apply, outAdj_num_iff I 0 (valid_getElem I _)
      (valid_getElem I _)]
  adj₁ u v := by
    show (matrixGraph I 1).graph.Adj u.1 v.1 ↔ outAdj I 1 _ _
    rw [corrEquiv_apply, corrEquiv_apply, outAdj_num_iff I 1 (valid_getElem I _)
      (valid_getElem I _)]
  col u v := by
    show (matrixGraph I 0).color u.1 = (matrixGraph I 0).color v.1 ↔
      outColor I _ = outColor I _
    rw [corrEquiv_apply, corrEquiv_apply, outColor_num I (valid_getElem I _),
      outColor_num I (valid_getElem I _), listGraph_color_eq_iff]
    have hu := valid_getElem I u.1
    have hv := valid_getElem I v.1
    simp only [Fin.getElem_fin] at hu hv ⊢
    constructor
    · intro h; rw [h]
    · intro h
      exact classNum_injective I hu.1 hv.1 (by omega)

/-- **Correctness of the renumbering.** -/
theorem distinguishes_outGraph_iff (hs : 1 ≤ s) :
    Distinguishes (s + 1) (outGraph I 0) (outGraph I 1) ↔
      Distinguishes (s + 1) (matrixGraph I 0) (matrixGraph I 1) := by
  have hk : 2 ≤ s + 1 := by omega
  have h := duplicatorWins_iff_of_corr (m := s + 1 + 1) (corr I)
  rw [← not_iff_not, ← Game.duplicatorWins_iff hk, ← Game.duplicatorWins_iff hk]
  exact h.symm

end Lax119563Proofs.Reduction
