import Lax119563Proofs.HomTensors.LGraph
import Lax119563.ColoredHomomorphisms

/-!
# From a good labeled graph to a colored graph

A good labeled graph `F` whose homomorphism counts into `G` and `H` differ yields a colored
graph `F'` of treewidth at most `k` with at most `k + N` vertices and `hom F' G ≠ hom F' H`:

* identify `eqv`-equivalent vertices (the quotient has at most `k + N` vertices, and the bag
  tree pushes forward to a tree decomposition of width `k`);
* a loop forbids all homomorphisms, so there is none; parallel edges and edge orientations are
  irrelevant;
* `hom(F, ·)` is the sum of `hom(F_κ, ·)` over the colorings `κ` (with colors of `G` and `H`)
  compatible with the color predicates, so one `F_κ` distinguishes `G` and `H`.
-/

namespace Lax119563Proofs.HomTensors

open Lax119563.ColoredGraphs Lax119563.ColoredHomomorphisms Lax228581.Treewidth Relation

variable {k : ℕ}

lemma card_eq_sum_fiber {α β : Type} [Finite α] [Fintype β] (P : α → Prop) (f : α → β) :
    Nat.card {a // P a} = ∑ b, Nat.card {a // P a ∧ f a = b} := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr
    { toFun := fun a => ⟨f a.1, a.1, a.2, rfl⟩
      invFun := fun p => ⟨p.2.1, p.2.2.1⟩
      left_inv := fun a => rfl
      right_inv := by
        rintro ⟨b, a, h, rfl⟩
        rfl }

namespace LGraph

lemma IsHom.eqvGen {F : LGraph k} {G : ColoredGraph} {h : F.V → Fin G.n} (hh : F.IsHom G h)
    {a b : F.V} (hab : EqvGen F.eqv a b) : h a = h b := by
  induction hab with
  | rel x y hxy => exact hh.2.2 x y hxy
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- A good labeled graph distinguishing `G` and `H` by homomorphism counts yields a colored
graph of treewidth at most `k` with at most `k + N` vertices distinguishing them. -/
theorem exists_coloredGraph (F : LGraph k) {N : ℕ} (hF : F.Good N) (G H : ColoredGraph)
    (hne : F.homCount G ≠ F.homCount H) :
    ∃ F' : ColoredGraph, TreewidthAtMost F' k ∧ F'.n ≤ k + N ∧ hom F' G ≠ hom F' H := by
  classical
  obtain ⟨⟨D⟩, W, g, hW, hWc, hg⟩ := hF
  -- the quotient by `eqv`
  let Q := Quot F.eqv
  have : Finite Q := Finite.of_surjective (Quot.mk _) fun q => Quot.exists_rep q
  let n := Nat.card Q
  let e : Q ≃ Fin n := Finite.equivFin Q
  let π : F.V → Fin n := fun a => e (Quot.mk _ a)
  have hker : ∀ a b, π a = π b → EqvGen F.eqv a b := fun a b h =>
    Quot.eqvGen_exact (e.injective h)
  have hcompat' : ∀ a b, EqvGen F.eqv a b → π a = π b := fun a b h => by
    simp only [π, Quot.eqvGen_sound h]
  have hcompat : ∀ a b, F.eqv a b → π a = π b := fun a b h => hcompat' a b (EqvGen.rel _ _ h)
  have hsurj : Function.Surjective π := by
    intro x
    obtain ⟨a, ha⟩ := Quot.exists_rep (e.symm x)
    exact ⟨a, by simp [π, ha]⟩
  -- size
  have hn : n ≤ k + N := by
    have hs : Function.Surjective (Sum.elim (fun i => Quot.mk F.eqv (F.lab i))
        (fun w => Quot.mk F.eqv (g w))) := by
      intro q
      obtain ⟨a, rfl⟩ := Quot.exists_rep q
      rcases hg a with ⟨i, hi⟩ | ⟨w, hw⟩
      · exact ⟨.inl i, (Quot.eqvGen_sound hi).symm⟩
      · exact ⟨.inr w, (Quot.eqvGen_sound hw).symm⟩
    have := Nat.card_le_card_of_surjective _ hs
    have h3 : Nat.card (Quot F.eqv) ≤ k + Nat.card W := by simpa using this
    change Nat.card (Quot F.eqv) ≤ k + N
    omega
  -- loops forbid homomorphisms
  by_cases hloop : ∃ a b, F.adj a b ∧ π a = π b
  · exfalso
    obtain ⟨a, b, hab, hπ⟩ := hloop
    have hzero : ∀ G' : ColoredGraph, F.homCount G' = 0 := by
      intro G'
      rw [homCount, Nat.card_eq_zero]
      left
      refine ⟨fun ⟨h, hh⟩ => ?_⟩
      have h1 := hh.1 a b hab
      rw [hh.eqvGen (hker a b hπ)] at h1
      exact G'.graph.loopless.irrefl _ h1
    exact hne ((hzero G).trans (hzero H).symm)
  push Not at hloop
  -- the simple graph on the quotient
  let S : SimpleGraph (Fin n) := SimpleGraph.fromRel fun x y => ∃ a b, F.adj a b ∧ π a = x ∧ π b = y
  have htw : HasTreewidthAtMost S k := by
    refine D.T.hasTreewidthAtMost D.valid S π hsurj hker hcompat ?_ k D.width
    intro x y hxy
    rw [SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, ha, hb⟩
    · exact ⟨a, b, rfl, rfl, Or.inl hab⟩
    · exact ⟨b, a, hb, ha, Or.inr hab⟩
  -- colorings
  let C := Finset.image G.color Finset.univ ∪ Finset.image H.color Finset.univ
  let Fκ : (Fin n → C) → ColoredGraph := fun κ => ⟨n, S, fun x => (κ x : ℕ)⟩
  let ok : (Fin n → C) → Prop := fun κ => ∀ a c, F.pred a c → (κ (π a) : ℕ) = c
  have hcount : ∀ G' : ColoredGraph, (∀ v, G'.color v ∈ C) →
      F.homCount G' = ∑ κ : Fin n → C, if ok κ then hom (Fκ κ) G' else 0 := by
    intro G' hC
    let πinv := Function.surjInv hsurj
    have hπinv : ∀ x, π (πinv x) = x := Function.surjInv_eq hsurj
    let Padj : (Fin n → Fin G'.n) → Prop := fun h' => ∀ x y, S.Adj x y → G'.graph.Adj (h' x) (h' y)
    let Ppred : (Fin n → Fin G'.n) → Prop :=
      fun h' => ∀ a c, F.pred a c → G'.color (h' (π a)) = c
    have hback : ∀ h, F.IsHom G' h → ∀ a, h (πinv (π a)) = h a := fun h hh a =>
      hh.eqvGen (hker _ _ (hπinv (π a)))
    -- (a) homomorphisms factor through the quotient
    have ha : F.homCount G' = Nat.card {h' : Fin n → Fin G'.n // Padj h' ∧ Ppred h'} := by
      refine Nat.card_congr
        { toFun := fun h => ⟨h.1 ∘ πinv, ?_, ?_⟩
          invFun := fun h' => ⟨h'.1 ∘ π, ?_, ?_, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · intro x y hxy
        rw [SimpleGraph.fromRel_adj] at hxy
        rcases hxy.2 with ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
        · simp only [Function.comp_apply, hback h.1 h.2]
          exact h.2.1 a b hab
        · simp only [Function.comp_apply, hback h.1 h.2]
          exact (h.2.1 a b hab).symm
      · intro a c hac
        simp only [Function.comp_apply, hback h.1 h.2]
        exact h.2.2.1 a c hac
      · intro a b hab
        exact h'.2.1 _ _ ((SimpleGraph.fromRel_adj _ _ _).2
          ⟨hloop a b hab, Or.inl ⟨a, b, hab, rfl, rfl⟩⟩)
      · exact h'.2.2
      · intro a b hab
        simp only [Function.comp_apply, hcompat a b hab]
      · intro h
        apply Subtype.ext
        funext a
        exact hback h.1 h.2 a
      · intro h'
        apply Subtype.ext
        funext x
        simp only [Function.comp_apply, hπinv]
    -- (b) split by the coloring
    let col : (Fin n → Fin G'.n) → (Fin n → C) := fun h' x => ⟨G'.color (h' x), hC _⟩
    rw [ha, card_eq_sum_fiber _ col]
    refine Finset.sum_congr rfl fun κ _ => ?_
    have hcol : ∀ h', col h' = κ ↔ ∀ x, G'.color (h' x) = κ x := by
      intro h'
      simp only [col, funext_iff, Subtype.ext_iff]
    split_ifs with hok
    · -- (c), (d)
      refine Nat.card_congr
        { toFun := fun h => ⟨⟨h.1, fun hxy => h.2.1.1 _ _ hxy⟩, (hcol h.1).1 h.2.2⟩
          invFun := fun h => ⟨⇑h.1, ⟨fun x y hxy => h.1.map_rel hxy, ?_⟩, (hcol ⇑h.1).2 h.2⟩
          left_inv := fun h => rfl
          right_inv := fun h => rfl }
      intro a c hac
      rw [h.2 (π a)]
      exact hok a c hac
    · rw [Nat.card_eq_zero]
      left
      refine ⟨fun h => ?_⟩
      obtain ⟨h', ⟨-, hp⟩, hκ⟩ := h
      refine hok fun a c hac => ?_
      rw [← (hcol h').1 hκ (π a)]
      exact hp a c hac
  have hCG : ∀ v, G.color v ∈ C := fun v => by simp [C]
  have hCH : ∀ v, H.color v ∈ C := fun v => by simp [C]
  rw [hcount G hCG, hcount H hCH] at hne
  by_contra hall
  push Not at hall
  refine hne (Finset.sum_congr rfl fun κ _ => ?_)
  split_ifs
  · exact hall (Fκ κ) htw hn
  · rfl

end LGraph

end Lax119563Proofs.HomTensors
