import Lax119563.WitnessFromRounds
import Lax119563Proofs.HomTensors.Part1

/-!
# Homomorphism witnesses from rounds

Every round-`r` color-class indicator of `k`-WL lies in the span of the tensors of good labeled
graphs with at most `ν_r` vertices besides the labels (`ind_mem`). Summing over the tuples of `G`
and of `H` turns a class of different sizes into a good labeled graph with different
homomorphism counts, and unlabeling (`LGraph.exists_coloredGraph`) yields the witness.
-/

namespace Lax119563Proofs.HomTensors

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.ColoredHomomorphisms LGraph

variable {k : ℕ}

lemma nu_bound {M : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k) (r : ℕ) : k + nu k M r ≤ k * (k * M) ^ r := by
  induction r with
  | zero => simp [nu]
  | succ r ih =>
    obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    simp only [nu, Nat.add_sub_cancel]
    set P := (k * (m + 1)) ^ r with hP
    have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (Nat.mul_pos hk (by omega))
    have h1 : m * k * (nu k (m + 1) r + k) ≤ m * k * (k * P) := Nat.mul_le_mul_left _ (by omega)
    have hkk : 1 ≤ k * k := by nlinarith
    have h2 : k ≤ k * k * P := by nlinarith
    have h3 : m ≤ m * (k * k) := by nlinarith
    rw [pow_succ, ← hP]
    nlinarith

/-- The linear functional `f ↦ ∑_{v ∈ V(G)^k} f(v) - ∑_{v ∈ V(H)^k} f(v)`. -/
noncomputable def delta (G H : ColoredGraph) : (Tup k G H → ℚ) →ₗ[ℚ] ℚ where
  toFun f := ∑ v, f (.inl v) - ∑ v, f (.inr v)
  map_add' f g := by simp [Finset.sum_add_distrib]; ring
  map_smul' c f := by simp [Finset.mul_sum, mul_sub]

lemma delta_tens (G H : ColoredGraph) (F : LGraph k) :
    delta G H (tens G H F) = (F.homCount G : ℚ) - F.homCount H := by
  simp [delta, tens, ← sum_tensor]

lemma delta_ind (G H : ColoredGraph) (r : ℕ) (c : Color k r) :
    delta G H (ind G H r c) = (Nat.card {p : Fin k → Fin G.n // color G r p = c} : ℚ) -
      Nat.card {q : Fin k → Fin H.n // color H r q = c} := by
  classical
  have key : ∀ (n : ℕ) (f : (Fin k → Fin n) → Color k r) (inst : ∀ v, Decidable (f v = c)),
      (∑ v, @ite ℚ (f v = c) (inst v) 1 0) = Nat.card {p // f p = c} := by
    intro n f inst
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp_all
  simp only [delta, LinearMap.coe_mk, AddHom.coe_mk, ind, chi, Sum.elim_inl, Sum.elim_inr]
  congr 1
  · exact key _ _ _
  · exact key _ _ _

/--
---
conclusion: Lax119563.WitnessFromRounds.witness_from_rounds
---
Put `M = |V(G)|^k + |V(H)|^k`, the number of `k`-tuples of `G` and `H`. Labeled graphs carry
edges, color predicates, equality constraints and `k` labels; a good one has a rooted bag tree
of width `k` with all labels in the root bag. By induction on `r`, each round-`r` color-class
indicator of `k`-WL on `V(G)^k ⊔ V(H)^k` is a linear combination of tensors of good labeled
graphs with at most `ν_r` vertices besides the labels, where `ν_0 = 0` and
`ν_{r+1} = (M - 1)(1 + k ν_r)`: round zero and the step both use polynomial closure (degree at
most `M - 1`), with atoms for equalities, edges and colors in round zero, and gluing and
extension for the step. Applying the functional "sum over `V(G)^k` minus sum over `V(H)^k`" to
the indicator of a class of different sizes gives a good labeled graph with different
homomorphism counts into `G` and `H`. Taking the quotient by the equality constraints,
excluding loops, symmetrizing edges and splitting by the colorings compatible with the
predicates yields a colored graph of treewidth at most `k` with at most
`k + ν_r ≤ k (k M)^r` vertices distinguishing `G` and `H`.
-/
theorem witness_from_rounds {k : ℕ} (hk : 2 ≤ k) {r : ℕ} {G H : ColoredGraph}
    (h : DistinguishesAfter k r G H) :
    ∃ F : ColoredGraph, TreewidthAtMost F k ∧
      F.n ≤ k * (k * (G.n ^ k + H.n ^ k)) ^ r ∧ hom F G ≠ hom F H := by
  classical
  obtain ⟨c, hc⟩ := h
  have hcard : Fintype.card (Tup k G H) = G.n ^ k + H.n ^ k := by
    simp [Fintype.card_sum]
  have hM : 1 ≤ G.n ^ k + H.n ^ k := by
    by_contra h0
    have hG : G.n ^ k = 0 := by omega
    have hH : H.n ^ k = 0 := by omega
    have e : ∀ n : ℕ, n ^ k = 0 → ∀ P : (Fin k → Fin n) → Prop,
        Nat.card {p // P p} = 0 := by
      intro n hn P
      have : Fintype.card (Fin k → Fin n) = 0 := by simp [hn]
      rw [Nat.card_eq_fintype_card]
      exact Nat.eq_zero_of_le_zero ((Fintype.card_subtype_le _).trans this.le)
    exact hc (by rw [e _ hG, e _ hH])
  have hind := ind_mem (G := G) (H := H) (by omega) r c
  rw [hcard] at hind
  -- some good labeled graph has different homomorphism counts
  obtain ⟨F, hF, hFne⟩ : ∃ F : LGraph k, F.Good (nu k (G.n ^ k + H.n ^ k) r) ∧
      F.homCount G ≠ F.homCount H := by
    by_contra hall
    push Not at hall
    have hle : Vs (k := k) G H (nu k (G.n ^ k + H.n ^ k) r) ≤ LinearMap.ker (delta G H) := by
      apply Submodule.span_le.2
      rintro _ ⟨F, hF, rfl⟩
      simp [LinearMap.mem_ker, delta_tens, hall F hF]
    have := hle hind
    rw [LinearMap.mem_ker, delta_ind, sub_eq_zero] at this
    exact hc (by exact_mod_cast this)
  obtain ⟨F', htw, hn, hne⟩ := F.exists_coloredGraph hF G H hFne
  exact ⟨F', htw, hn.trans (nu_bound hM (by omega) r), hne⟩

end Lax119563Proofs.HomTensors
