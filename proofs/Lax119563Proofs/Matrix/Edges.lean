import Lax119563Proofs.Matrix.Size

/-!
# Edges of the matrix graphs

Every edge joins a hub (update, junction, link) with a non-hub, and a hub has at most one
neighbor in each of its at most three neighbor classes. Hence each graph has at most three
times as many edges as vertices.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-- The neighbor classes of a hub. -/
def slots : ICls I → Finset (ICls I)
  | .upd e σ c => {trackAt I e c σ, .track e σ c, .coef e σ}
  | .junc e c => {coordU e c, coordV e c, .sum e c}
  | .link e c => {trackAt I e c (numSteps k ℓ), endCls I e c}
  | _ => ∅

lemma card_slots_le (X : ICls I) : (slots X).card ≤ 3 := by
  cases X <;> simp only [slots] <;>
    first
    | exact (Finset.card_insert_le _ _).trans
        (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
    | exact (Finset.card_insert_le _ _).trans (by simp)
    | simp

lemma mem_slots {X Y : ICls I} {l m : Lab} (h : hubB I X l Y m = true) : Y ∈ slots X := by
  cases X with
  | upd e σ c =>
    rw [hubB_upd] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [slots]
  | junc e c =>
    rw [hubB_junc'] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [slots]
  | link e c =>
    rw [hubB_link] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [slots]
  | coord => simp [hubB] at h
  | sum => simp [hubB] at h
  | track => simp [hubB] at h
  | coef => simp [hubB] at h

/-- A hub prescribes the label of its neighbor in each neighbor class. -/
lemma hubB_label_unique {X Y : ICls I} (hX : ClsValid I X) {l m m' : Lab}
    (h : hubB I X l Y m = true) (h' : hubB I X l Y m' = true) : m.1 = m'.1 := by
  cases X with
  | upd e σ c =>
    rw [hubB_upd] at h h'
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    rcases h' with ⟨h1, h'⟩ | ⟨h1, h'⟩ | ⟨h1, h'⟩ <;>
    first
    | exact h.trans h'.symm
    | exact absurd h1 (trackAt_ne_track e c σ)
    | exact absurd h1.symm (trackAt_ne_track e c σ)
    | exact absurd h1 (trackAt_ne_coef e c σ σ)
    | exact absurd h1.symm (trackAt_ne_coef e c σ σ)
    | simp at h1
  | junc e c =>
    have ht : isTern (sch I e) = true := hX.1
    rw [hubB_junc'] at h h'
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    rcases h' with ⟨h1, h'⟩ | ⟨h1, h'⟩ | ⟨h1, h'⟩ <;>
    first
    | exact h.trans h'.symm
    | exact absurd h1 (coordU_ne_coordV ht c)
    | exact absurd h1.symm (coordU_ne_coordV ht c)
    | simp [coordU, coordV] at h1
  | link e c =>
    rw [hubB_link] at h h'
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    rcases h' with ⟨-, h'⟩ | ⟨-, h'⟩ <;> exact h.trans h'.symm
  | coord => simp [hubB] at h
  | sum => simp [hubB] at h
  | track => simp [hubB] at h
  | coef => simp [hubB] at h

lemma twoBit_of_not_hub {X : ICls I} (h : isHub I X = false) : twoBit I X = false := by
  cases X <;> simp_all [isHub, twoBit]

/-- A valid name of a non-hub class is determined by its effective label. -/
lemma name_unique (ε : ZMod 2) {x y : VName I} (hx : Valid I x) (hy : Valid I y)
    (hc : x.1 = y.1) (hhub : isHub I x.1 = false) (he : (eff I ε x).1 = (eff I ε y).1) :
    x = y := by
  obtain ⟨X, l⟩ := x
  obtain ⟨Y, m⟩ := y
  simp only at hc
  subst hc
  have h2 : l.2 = 0 := hx.2.1 (twoBit_of_not_hub hhub)
  have h2' : m.2 = 0 := hy.2.1 (twoBit_of_not_hub hhub)
  simp only [eff] at he
  have h1 : l.1 = m.1 := add_right_cancel he
  ext <;> simp [h1, h2, h2']

instance (ε : ZMod 2) : DecidableRel (matrixGraph I ε).graph.Adj := fun i j =>
  inferInstanceAs (Decidable (adjN I ε (nm i) (nm j)))

lemma degree_hub_le (ε : ZMod 2) (p : Fin (nV I)) (hp : isHub I (nm p).1 = true) :
    (matrixGraph I ε).graph.degree p ≤ 3 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine (Finset.card_le_card_of_injOn (fun q => (nm q).1) (fun q hq => ?_)
    (fun q hq q' hq' hqq => ?_)).trans (card_slots_le (nm p).1)
  · rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hq
    exact mem_slots ((adjN_iff_hub ε hp).mp hq)
  · rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hq hq'
    have h1 : hubB I (nm p).1 (eff I ε (nm p)) (nm q).1 (eff I ε (nm q)) = true :=
      (adjN_iff_hub ε hp).mp hq
    have h2 : hubB I (nm p).1 (eff I ε (nm p)) (nm q').1 (eff I ε (nm q')) = true :=
      (adjN_iff_hub ε hp).mp hq'
    simp only at hqq
    rw [hqq] at h1
    have hl := hubB_label_unique (nm_valid p).1 h1 h2
    have hnh := (hubB_hub I h2).2
    exact nm_injective (name_unique ε (nm_valid q) (nm_valid q') hqq (hqq ▸ hnh) hl)

/-- **Edge bound.** -/
theorem numEdges_le (ε : ZMod 2) : (matrixGraph I ε).numEdges ≤ 3 * nV I := by
  classical
  let G := (matrixGraph I ε).graph
  let hubs : Finset (Fin (nV I)) := Finset.univ.filter fun p => isHub I (nm p).1 = true
  have hsub : G.edgeFinset ⊆ hubs.biUnion fun p => G.incidenceFinset p := by
    intro s hs
    induction s using Sym2.ind with
    | h p q =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hs
      rw [Finset.mem_biUnion]
      rcases hs with h | h
      · have h' : hubB I (nm p).1 (eff I ε (nm p)) (nm q).1 (eff I ε (nm q)) = true := h
        refine ⟨p, by simp [hubs, (hubB_hub I h').1], ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨Or.inl h, Sym2.mem_mk_left _ _⟩
      · have h' : hubB I (nm q).1 (eff I ε (nm q)) (nm p).1 (eff I ε (nm p)) = true := h
        refine ⟨q, by simp [hubs, (hubB_hub I h').1], ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨Or.inr h, Sym2.mem_mk_right _ _⟩
  have : (matrixGraph I ε).numEdges = G.edgeFinset.card := by
    rw [ColoredGraph.numEdges, SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  rw [this]
  calc G.edgeFinset.card ≤ ∑ p ∈ hubs, (G.incidenceFinset p).card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ p ∈ hubs, 3 := Finset.sum_le_sum fun p hp => by
        rw [SimpleGraph.card_incidenceFinset_eq_degree]
        exact degree_hub_le ε p (Finset.mem_filter.mp hp).2
    _ ≤ 3 * nV I := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
        exact Nat.mul_le_mul_left _ ((Finset.card_le_univ _).trans (by simp))

end Lax119563Proofs.Matrix
