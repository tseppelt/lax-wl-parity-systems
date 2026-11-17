import Lax119563Proofs.Compiler.Order
import Lax119563Proofs.Matrix.SpoilerStrip

/-!
# Edges of the reordered graphs

In `ordL I` every hub comes before all its neighbors (`ordL_pairwise`: no name is a
`hubB`-neighbor of a later hub). Hence the edges `u < v` of `reGraph I (ordL I) ε` are exactly
the pairs with `hubB` from `u` to `v` (`adj_lt_iff`), and the edge list is, for each position
`u` in order, the increasing positions `v` with `hubB` from `L[u]` to `L[v]`
(`edgeList_ordL`).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- A `hubB`-neighbor lies in the schema of the hub or is a coordinate class. -/
lemma hubB_key {X Y : ICls I} {l m : Lab} (h : hubB I X l Y m = true) :
    keySchema I Y = keySchema I X ∨ tag I Y = 0 := by
  have htr : ∀ (e : Fin I.schemas.length) c σ,
      keySchema I (trackAt I e c σ) = some e ∨ tag I (trackAt I e c σ) = 0 := by
    intro e c σ
    rcases trackAt_cases e c σ with h | ⟨σ', -, h⟩ <;> rw [h]
    · rcases startCls_cases e c with h' | h' <;> rw [h'] <;> simp [keySchema, tag]
    · simp [keySchema]
  cases X with
  | upd e σ c =>
    simp only [hubB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩)
    · simpa [keySchema] using htr e c σ
    · simp [keySchema]
    · simp [keySchema]
  | junc e c =>
    simp only [hubB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩) <;> simp [keySchema, tag]
  | link e c =>
    simp only [hubB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with (⟨rfl, -⟩ | ⟨rfl, -⟩)
    · simpa [keySchema] using htr e c _
    · simp [endCls, tag]
  | coord => simp [hubB] at h
  | sum => simp [hubB] at h
  | track => simp [hubB] at h
  | coef => simp [hubB] at h

/-- `b` is not a `hubB`-hub of `a`. -/
def NoBack (a b : VName I) : Prop := ∀ l m, hubB I b.1 l a.1 m = false

lemma noBack_of {a b : VName I}
    (h : isHub I a.1 = true ∨ isHub I b.1 = false ∨
      ∃ e₁ e₂, keySchema I a.1 = some e₁ ∧ keySchema I b.1 = some e₂ ∧ e₁ ≠ e₂) :
    NoBack I a b := by
  intro l m
  by_contra hb
  rw [Bool.not_eq_false] at hb
  have h1 := hubB_hub I hb
  rcases h with h | h | ⟨e₁, e₂, h₁, h₂, hne⟩
  · rw [h] at h1; exact absurd h1.2 (by simp)
  · rw [h] at h1; exact absurd h1.1 (by simp)
  · rcases hubB_key I hb with h3 | h3
    · rw [h₁, h₂] at h3; exact hne (Option.some.inj h3)
    · rcases a with ⟨X, _⟩
      cases X <;> simp_all [tag, keySchema]

lemma keySchema_of_mem_block {e : Fin I.schemas.length} {x : VName I}
    (hx : x ∈ hubsE I e ++ nonhubsE I e) : keySchema I x.1 = some e := by
  rcases List.mem_append.mp hx with hx | hx
  · exact (isHub_of_mem_hubsE I hx).2
  · exact (not_hub_of_mem_nonhubsE I hx).2

lemma isHub_coordVerts {v : Fin I.numLocations} {x : VName I} (hx : x ∈ coordVerts I v) :
    isHub I x.1 = false := by
  obtain ⟨⟨c, h⟩, -⟩ := (mem_coordVerts I v x).mp hx
  rw [h]; rfl

/-- **Hubs come first.** No name is a `hubB`-neighbor of a later hub. -/
theorem ordL_pairwise : (ordL I).Pairwise (NoBack I) := by
  unfold ordL
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_flatMap]
    refine ⟨fun e _ => ?_, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨List.Pairwise.imp_of_mem ?_ (List.pairwise_of_forall (R := fun _ _ => True)
          (fun _ _ => trivial)), List.Pairwise.imp_of_mem ?_ (List.pairwise_of_forall
          (R := fun _ _ => True) (fun _ _ => trivial)), fun a ha b hb => ?_⟩
      · intro a b ha _ _
        exact noBack_of I (Or.inl (isHub_of_mem_hubsE I ha).1)
      · intro a b _ hb _
        exact noBack_of I (Or.inr (Or.inl (not_hub_of_mem_nonhubsE I hb).1))
      · exact noBack_of I (Or.inr (Or.inl (not_hub_of_mem_nonhubsE I hb).1))
    · refine (List.nodup_finRange _).imp_of_mem ?_
      intro e₁ e₂ _ _ hne a ha b hb
      exact noBack_of I (Or.inr (Or.inr ⟨e₁, e₂, keySchema_of_mem_block I ha,
        keySchema_of_mem_block I hb, hne⟩))
  · refine List.Pairwise.imp_of_mem ?_ (List.pairwise_of_forall (R := fun _ _ => True)
      (fun _ _ => trivial))
    intro a b _ hb _
    obtain ⟨v, -, hb⟩ := List.mem_flatMap.mp hb
    exact noBack_of I (Or.inr (Or.inl (isHub_coordVerts I hb)))
  · intro a _ b hb
    obtain ⟨v, -, hb⟩ := List.mem_flatMap.mp hb
    exact noBack_of I (Or.inr (Or.inl (isHub_coordVerts I hb)))

/-- The edges `u < v` of the reordered graph are the `hubB`-pairs. -/
theorem adj_lt_iff (ε : ZMod 2) (u v : Fin (ordL I).length) :
    (u < v ∧ adjN I ε (ordL I)[(u : ℕ)] (ordL I)[(v : ℕ)]) ↔
      hubB I (ordL I)[(u : ℕ)].1 (eff I ε (ordL I)[(u : ℕ)]) (ordL I)[(v : ℕ)].1
        (eff I ε (ordL I)[(v : ℕ)]) = true := by
  have hP := List.pairwise_iff_getElem.mp (ordL_pairwise I)
  constructor
  · rintro ⟨huv, h | h⟩
    · exact h
    · exact absurd h (by rw [hP u v u.2 v.2 huv]; simp)
  · intro h
    refine ⟨?_, Or.inl h⟩
    rcases lt_trichotomy u v with huv | rfl | hvu
    · exact huv
    · have := hubB_hub I h; rw [this.1] at this; exact absurd this.2 (by simp)
    · exact absurd h (by rw [hP v u v.2 u.2 hvu]; simp)

/-- **The edge list of the reordered graph.** -/
theorem edgeList_ordL (ε : ZMod 2) :
    edgeList (reGraph I (ordL I) ε) =
      (List.finRange (ordL I).length).flatMap fun (u : Fin (ordL I).length) =>
        ((List.finRange (ordL I).length).filter fun (v : Fin (ordL I).length) =>
          hubB I (ordL I)[(u : ℕ)].1 (eff I ε (ordL I)[(u : ℕ)]) (ordL I)[(v : ℕ)].1
            (eff I ε (ordL I)[(v : ℕ)])).map fun (v : Fin (ordL I).length) =>
              ((u : ℕ), (v : ℕ)) := by
  unfold edgeList
  refine List.flatMap_congr fun u _ => ?_
  rw [List.filter_congr (q := fun (v : Fin (ordL I).length) =>
    hubB I (ordL I)[(u : ℕ)].1 (eff I ε (ordL I)[(u : ℕ)]) (ordL I)[(v : ℕ)].1
      (eff I ε (ordL I)[(v : ℕ)])) (fun v _ => by
        rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; exact adj_lt_iff I ε u v)]
  simp only [List.map_eq_flatMap]
  change List.flatMap _ (List.flatMap (fun a : Fin (ordL I).length => [(a : ℕ)]) _) = _
  rw [List.flatMap_assoc]
  simp

end Lax119563Proofs.Compiler
