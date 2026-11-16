import Lax119563.ColoredHomomorphisms
import Lax119563Proofs.HomChar.Det
import Lax119563Proofs.HomChar.Forest

/-!
# Homomorphism counts of bounded-treewidth graphs are determined by `k`-WL

Fix a colored graph `F` with a one-vertex forest `T` of width `k`. A map `h : V(F) → V(G)` is a
homomorphism if and only if every vertex `u` satisfies the local condition `Ok T G h u` (its color
is preserved, and so are its edges to `I T u`, the rest of its bag). For a vertex `c` and a map
`g`, `Z T G c g` counts the maps that agree with `g` outside the subtree of `c` and satisfy the
local conditions inside it. It satisfies the recursion
`Z c g = ∑_x w_c(g[x/c]) ∏_{d child of c} Z d (g[x/c])`, and `hom(F, G)` is the product over the
roots `ρ` of `Z ρ g`.

If the labels `ℓ : Fin k → V(F)` cover `I T c` and avoid the subtree of `c`, then `Z c g` is a
WL-determined tensor evaluated at `g ∘ ℓ` (`exists_det`): the sum over `x` is a WL extension,
where each child either does not see `c` (and keeps the labels `ℓ`) or sees `c` (and gets the
labels `ℓ[c/i]` for a position `i` not needed for the rest of its bag).
-/

namespace Lax119563Proofs.HomChar

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.ColoredHomomorphisms
open Lax119563Proofs.RowSpace

open scoped Classical

variable {k : ℕ} {F : ColoredGraph} (T : OneVertexForest F.graph k)

/-- The local homomorphism condition at `u`. -/
def Ok (G : ColoredGraph) (h : Fin F.n → Fin G.n) (u : Fin F.n) : Prop :=
  G.color (h u) = F.color u ∧ ∀ b ∈ I T u, F.graph.Adj u b → G.graph.Adj (h u) (h b)

/-- The indicator of the local condition. -/
noncomputable def w (G : ColoredGraph) (h : Fin F.n → Fin G.n) (u : Fin F.n) : ℕ :=
  if Ok T G h u then 1 else 0

/-- Homomorphisms from the subtree of `c`, with the rest given by `g`. -/
noncomputable def Z (G : ColoredGraph) (c : Fin F.n) (g : Fin F.n → Fin G.n) : ℕ :=
  ∑ h ∈ agreeOff (S T c) g, ∏ u ∈ S T c, w T G h u

lemma w_local (G : ColoredGraph) {h h' : Fin F.n → Fin G.n} {u : Fin F.n}
    (e : ∀ v ∈ T.bag u, h v = h' v) : w T G h u = w T G h' u := by
  have e1 : h u = h' u := e u (T.mem_bag u)
  have e2 : ∀ b ∈ I T u, h b = h' b := fun b hb => e b (mem_I.1 hb).2
  have : Ok T G h u ↔ Ok T G h' u := by
    unfold Ok
    constructor
    · rintro ⟨a, b⟩
      exact ⟨by rw [← e1]; exact a, fun x hx hadj => by rw [← e1, ← e2 x hx]; exact b x hx hadj⟩
    · rintro ⟨a, b⟩
      exact ⟨by rw [e1]; exact a, fun x hx hadj => by rw [e1, e2 x hx]; exact b x hx hadj⟩
  simp only [w, this]

lemma Z_rec (G : ColoredGraph) (c : Fin F.n) (g : Fin F.n → Fin G.n) :
    Z T G c g = ∑ x, w T G (Function.update g c x) c *
      ∏ d ∈ ch T c, Z T G d (Function.update g c x) := by
  have hc : c ∉ (ch T c).biUnion (S T) := by
    simp only [Finset.mem_biUnion, not_exists, not_and]
    exact fun d hd => not_mem_S_child hd
  unfold Z
  rw [S_eq_insert (T := T) c, sum_agreeOff_insert hc]
  refine Finset.sum_congr rfl fun x _ => ?_
  set g' := Function.update g c x
  have hdisj : (↑(ch T c) : Set (Fin F.n)).PairwiseDisjoint (S T) := fun d hd d' hd' hne =>
    disjoint_S_children hd hd' hne
  calc ∑ h ∈ agreeOff ((ch T c).biUnion (S T)) g',
        ∏ u ∈ insert c ((ch T c).biUnion (S T)), w T G h u
      = ∑ h ∈ agreeOff ((ch T c).biUnion (S T)) g',
          w T G g' c * ∏ d ∈ ch T c, ∏ u ∈ S T d, w T G h u := by
        refine Finset.sum_congr rfl fun h hh => ?_
        rw [Finset.prod_insert hc, Finset.prod_biUnion hdisj]
        congr 1
        refine w_local T G fun v hv => (mem_agreeOff.1 hh) v ?_
        simp only [Finset.mem_biUnion, not_exists, not_and]
        exact fun d hd hvd => Finset.disjoint_left.1 (disjoint_bag_S_child hd) hv hvd
    _ = w T G g' c * ∏ d ∈ ch T c, ∑ h ∈ agreeOff (S T d) g', ∏ u ∈ S T d, w T G h u := by
        rw [← Finset.mul_sum]
        congr 1
        refine sum_agreeOff_biUnion (ch T c) (S T) (fun d => S T d ∪ T.bag c) _ g'
          (fun d hd d' hd' hne => disjoint_S_children hd hd' hne)
          (fun d hd d' hd' hne => Finset.disjoint_union_left.2
            ⟨disjoint_S_children hd hd' hne, disjoint_bag_S_child hd'⟩)
          (fun d hd h h' e => Finset.prod_congr rfl fun u hu =>
            w_local T G fun v hv => e v (bag_subset_of_child hd hu hv))
    _ = _ := rfl

/-- Homomorphisms are the maps satisfying all local conditions. -/
lemma hom_eq_sum (G : ColoredGraph) : hom F G = ∑ h : Fin F.n → Fin G.n, ∏ u, w T G h u := by
  have e : {h : F.graph →g G.graph // ∀ v, G.color (h v) = F.color v} ≃
      {h : Fin F.n → Fin G.n // ∀ u, Ok T G h u} :=
    { toFun := fun φ => ⟨φ.1, fun u => ⟨φ.2 u, fun _ _ hadj => φ.1.map_rel hadj⟩⟩
      invFun := fun h => ⟨{ toFun := h.1
                            map_rel' := fun {a b} hab => by
                              rcases T.adj_mem a b hab with hb | ha
                              · exact (h.2 a).2 b hb hab
                              · exact ((h.2 b).2 a ha hab.symm).symm },
                          fun v => (h.2 v).1⟩
      left_inv := fun φ => rfl
      right_inv := fun h => rfl }
  rw [hom, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [w]
  rw [Finset.prod_boole]
  simp

lemma hom_eq_prod (G : ColoredGraph) (g : Fin F.n → Fin G.n) :
    hom F G = ∏ ρ ∈ roots T, Z T G ρ g := by
  rw [hom_eq_sum T G]
  have hdisj : (↑(roots T) : Set (Fin F.n)).PairwiseDisjoint (S T) := fun d hd d' hd' hne =>
    disjoint_S_roots hd hd' hne
  calc ∑ h : Fin F.n → Fin G.n, ∏ u, w T G h u
      = ∑ h ∈ agreeOff ((roots T).biUnion (S T)) g, ∏ ρ ∈ roots T, ∏ u ∈ S T ρ, w T G h u := by
        rw [← univ_eq_roots, agreeOff_univ]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [univ_eq_roots (T := T), Finset.prod_biUnion hdisj]
    _ = _ := sum_agreeOff_biUnion (roots T) (S T) (S T) _ g
          (fun d hd d' hd' hne => disjoint_S_roots hd hd' hne)
          (fun d hd d' hd' hne => disjoint_S_roots hd hd' hne)
          (fun ρ hρ h h' e => Finset.prod_congr rfl fun u hu =>
            w_local T G fun v hv => e v (bag_subset_of_root hρ hu hv))

/-- Some position of `ℓ` is not needed to cover a set of fewer than `k` labels. -/
lemma exists_free_pos {α : Type*} {ℓ : Fin k → α} {s : Finset α}
    (hs : ∀ b ∈ s, ∃ j, ℓ j = b) (hcard : s.card < k) : ∃ i, ∀ b ∈ s, ∃ j, j ≠ i ∧ ℓ j = b := by
  by_contra hcon
  push Not at hcon
  choose b hb hb' using hcon
  have hℓ : ∀ i, ℓ i = b i := by
    intro i
    obtain ⟨j, hj⟩ := hs (b i) (hb i)
    by_cases hji : j = i
    · subst hji; exact hj
    · exact absurd hj (hb' i j hji)
  have hinj : Function.Injective b := by
    intro i i' e
    by_contra hne
    exact hb' i i' (Ne.symm hne) ((hℓ i').trans e.symm)
  have h1 := Finset.card_image_of_injective Finset.univ hinj
  have h2 : Finset.univ.image b ⊆ s := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hb i
  have := Finset.card_le_card h2
  rw [h1, Finset.card_univ, Fintype.card_fin] at this
  omega

/-- Replace position `i` (if any) of a tuple by `x`. -/
def pos {α : Type*} : Option (Fin k) → (Fin k → α) → α → (Fin k → α)
  | none, p, _ => p
  | some i, p, x => Function.update p i x

lemma extAny_pos {φ : Fam k} (hφ : DetAny φ) (o : Option (Fin k)) :
    ExtAny (fun G p x => φ G (pos o p x)) := by
  cases o with
  | none => exact extAny_left hφ
  | some i => exact extAny_at hφ i

lemma det_color (i : Fin k) (a : ℕ) :
    DetAny (k := k) (fun G p => if G.color (p i) = a then 1 else 0) :=
  ⟨0, (det_atp (fun t => if t.color i = a then 1 else 0)).congr fun G p => by
    simp only [atp]; congr⟩

lemma det_adj (i j : Fin k) :
    DetAny (k := k) (fun G p => if G.graph.Adj (p i) (p j) then 1 else 0) :=
  ⟨0, (det_atp (fun t => if t.adj i j = true then 1 else 0)).congr fun G p => by simp [atp]⟩

lemma det_const_tuple (i0 : Fin k) :
    DetAny (k := k) (fun _ p => if ∀ i, p i = p i0 then 1 else 0) :=
  ⟨0, (det_atp (fun t => if ∀ i, t.eq i i0 = true then 1 else 0)).congr fun G p => by
    simp [atp]⟩

/-- The local condition at `c`, read off from the labels `p` (for `ℓ`) and the image `x` of `c`. -/
lemma extAny_local (hk : 2 ≤ k) (c : Fin F.n) (ℓ : Fin k → Fin F.n) :
    ExtAny (fun G (p : Fin k → Fin G.n) x => if (G.color x = F.color c ∧
      ∀ j, ℓ j ∈ I T c → F.graph.Adj c (ℓ j) → G.graph.Adj x (p j)) then 1 else 0) := by
  let i0 : Fin k := ⟨0, by omega⟩
  let other : Fin k → Fin k := fun j => if j = i0 then ⟨1, by omega⟩ else i0
  have hother : ∀ j, other j ≠ j := by
    intro j
    simp only [other]
    split_ifs with h
    · rw [h]; exact fun e => by simp [i0, Fin.ext_iff] at e
    · exact Ne.symm h
  have h1 : ExtAny (k := k) (fun G p x => if G.color x = F.color c then 1 else 0) :=
    (extAny_at (det_color i0 (F.color c)) i0).congr fun G p x => by simp
  have h2 : ∀ j, ExtAny (k := k) (fun G p x =>
      if (ℓ j ∈ I T c → F.graph.Adj c (ℓ j) → G.graph.Adj x (p j)) then 1 else 0) := by
    intro j
    by_cases hj : ℓ j ∈ I T c ∧ F.graph.Adj c (ℓ j)
    · refine (extAny_at (det_adj (other j) j) (other j)).congr fun G p x => ?_
      simp [hj, Function.update_of_ne (hother j).symm]
    · refine (extAny_const 1).congr fun G p x => ?_
      rw [if_pos]
      intro a b
      exact absurd ⟨a, b⟩ hj
  refine (h1.mul (ExtAny.prod Finset.univ fun j _ => h2 j)).congr fun G p x => ?_
  rw [Finset.prod_boole]
  by_cases ha : G.color x = F.color c <;>
    by_cases hb : ∀ j, ℓ j ∈ I T c → F.graph.Adj c (ℓ j) → G.graph.Adj x (p j) <;>
    simp [ha, hb]

lemma w_update (c : Fin F.n) (ℓ : Fin k → Fin F.n) (hcov : ∀ b ∈ I T c, ∃ i, ℓ i = b)
    (G : ColoredGraph) (g : Fin F.n → Fin G.n) (x : Fin G.n) :
    w T G (Function.update g c x) c = if (G.color x = F.color c ∧
      ∀ j, ℓ j ∈ I T c → F.graph.Adj c (ℓ j) → G.graph.Adj x ((g ∘ ℓ) j)) then 1 else 0 := by
  have : Ok T G (Function.update g c x) c ↔ (G.color x = F.color c ∧
      ∀ j, ℓ j ∈ I T c → F.graph.Adj c (ℓ j) → G.graph.Adj x ((g ∘ ℓ) j)) := by
    unfold Ok
    rw [Function.update_self]
    refine and_congr Iff.rfl ⟨fun h j hj hadj => ?_, fun h b hb hadj => ?_⟩
    · have := h _ hj hadj
      rwa [Function.update_of_ne (mem_I.1 hj).1] at this
    · obtain ⟨i, rfl⟩ := hcov b hb
      rw [Function.update_of_ne (mem_I.1 hb).1]
      exact h i hb hadj
  simp only [w, this]

/-- **Main lemma.** If `ℓ` covers `I T c` and avoids the subtree of `c`, then `Z c g` is a
WL-determined tensor evaluated at `g ∘ ℓ`. -/
theorem exists_det (hk : 2 ≤ k) (c : Fin F.n) (ℓ : Fin k → Fin F.n)
    (hcov : ∀ b ∈ I T c, ∃ i, ℓ i = b) (hout : ∀ i, ℓ i ∉ S T c) :
    ∃ φ : Fam k, DetAny φ ∧ ∀ G g, Z T G c g = φ G (g ∘ ℓ) := by
  induction hm : (S T c).card using Nat.strong_induction_on generalizing c ℓ with
  | _ m ih =>
  have hcS : c ∈ S T c := mem_S.2 (up_refl c)
  have hchild : ∀ d, ∃ (o : Option (Fin k)) (φ : Fam k), DetAny φ ∧ (d ∈ ch T c →
      ∀ G g x, Z T G d (Function.update g c x) = φ G (pos o (g ∘ ℓ) x)) := by
    intro d
    by_cases hd : d ∈ ch T c
    swap
    · exact ⟨none, fun _ _ => 0, ⟨0, det_const 0⟩, fun h => absurd h hd⟩
    have hlt : (S T d).card < m := by
      rw [← hm]
      refine Finset.card_lt_card ⟨S_child_subset hd, fun h => ?_⟩
      exact not_mem_S_child hd (h hcS)
    have hpar := mem_ch.1 hd
    have hout' : ∀ i, ℓ i ∉ S T d := fun i h => hout i (S_child_subset hd h)
    have hℓc : ∀ i, ℓ i ≠ c := fun i e => hout i (e ▸ hcS)
    by_cases hcI : c ∈ I T d
    · -- the child sees `c`: free a position for it
      have hs : ∀ b ∈ (I T d).erase c, ∃ j, ℓ j = b := by
        intro b hb
        obtain ⟨hbc, hb⟩ := Finset.mem_erase.1 hb
        exact hcov b (mem_I.2 ⟨hbc, I_subset_parent hpar hb⟩)
      have hcard : ((I T d).erase c).card < k := by
        rw [Finset.card_erase_of_mem hcI]
        have := card_I (T := T) d
        have := Finset.card_pos.2 ⟨c, hcI⟩
        omega
      obtain ⟨i, hi⟩ := exists_free_pos hs hcard
      obtain ⟨φ, hφ, hZ⟩ := ih _ hlt d (Function.update ℓ i c)
        (fun b hb => by
          by_cases hbc : b = c
          · exact ⟨i, by rw [hbc, Function.update_self]⟩
          · obtain ⟨j, hji, hj⟩ := hi b (Finset.mem_erase.2 ⟨hbc, hb⟩)
            exact ⟨j, by rw [Function.update_of_ne hji, hj]⟩)
        (fun j => by
          by_cases hji : j = i
          · rw [hji, Function.update_self]; exact not_mem_S_child hd
          · rw [Function.update_of_ne hji]; exact hout' j) rfl
      refine ⟨some i, φ, hφ, fun _ G g x => ?_⟩
      rw [hZ]
      congr 1
      funext j
      by_cases hji : j = i
      · subst hji; simp [pos]
      · simp [pos, Function.update_of_ne hji, Function.update_of_ne (hℓc j)]
    · -- the child does not see `c`: keep the labels
      obtain ⟨φ, hφ, hZ⟩ := ih _ hlt d ℓ
        (fun b hb => hcov b (mem_I.2 ⟨fun e => hcI (e ▸ hb), I_subset_parent hpar hb⟩))
        hout' rfl
      refine ⟨none, φ, hφ, fun _ G g x => ?_⟩
      rw [hZ]
      congr 1
      funext j
      simp [pos, Function.update_of_ne (hℓc j)]
  choose o φ hφ hZ using hchild
  refine ⟨fun G p => ∑ x, (if (G.color x = F.color c ∧
      ∀ j, ℓ j ∈ I T c → F.graph.Adj c (ℓ j) → G.graph.Adj x (p j)) then 1 else 0) *
        ∏ d ∈ ch T c, φ d G (pos (o d) p x), ?_, fun G g => ?_⟩
  · exact ((extAny_local T hk c ℓ).mul
      (ExtAny.prod (ch T c) fun d _ => extAny_pos (hφ d) (o d))).sum
  · rw [Z_rec]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [w_update T c ℓ hcov]
    congr 1
    exact Finset.prod_congr rfl fun d hd => hZ d hd G g x

/-- At a root, `Z` is the sum of a WL-determined tensor over all tuples. -/
theorem exists_det_root (hk : 2 ≤ k) (ρ : Fin F.n) (hρ : ρ ∈ roots T) :
    ∃ θ : Fam k, DetAny θ ∧ ∀ G g, Z T G ρ g = ∑ p, θ G p := by
  let i0 : Fin k := ⟨0, by omega⟩
  have hchild : ∀ d, ∃ φ : Fam k, DetAny φ ∧ (d ∈ ch T ρ →
      ∀ G g x, Z T G d (Function.update g ρ x) = φ G (fun _ => x)) := by
    intro d
    by_cases hd : d ∈ ch T ρ
    swap
    · exact ⟨fun _ _ => 0, ⟨0, det_const 0⟩, fun h => absurd h hd⟩
    obtain ⟨φ, hφ, hZ⟩ := exists_det T hk d (fun _ => ρ)
      (fun b hb => ⟨i0, (I_child_root hρ hd hb).symm⟩)
      (fun _ => not_mem_S_child hd)
    refine ⟨φ, hφ, fun _ G g x => ?_⟩
    rw [hZ]
    congr 1
    funext j
    simp
  choose φ hφ hZ using hchild
  let χ : Fam k := fun G p => (if G.color (p i0) = F.color ρ then 1 else 0) *
    ∏ d ∈ ch T ρ, φ d G p
  refine ⟨fun G p => (if ∀ i, p i = p i0 then 1 else 0) * χ G p,
    (det_const_tuple i0).mul ((det_color i0 _).mul (DetAny.prod _ fun d _ => hφ d)),
    fun G g => ?_⟩
  have hI : I T ρ = ∅ := I_eq_empty_of_root (mem_roots.1 hρ)
  have hsum : ∑ p : Fin k → Fin G.n, (if ∀ i, p i = p i0 then 1 else 0) * χ G p =
      ∑ x : Fin G.n, χ G (fun _ => x) := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    have himg : Finset.univ.filter (fun p : Fin k → Fin G.n => ∀ i, p i = p i0) =
        Finset.univ.image (fun x : Fin G.n => fun _ : Fin k => x) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        exact ⟨p i0, funext fun i => (h i).symm⟩
      · rintro ⟨x, rfl⟩ i
        rfl
    rw [himg, Finset.sum_image]
    intro x _ y _ e
    exact congrFun e i0
  rw [hsum, Z_rec]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [χ]
  congr 1
  · simp [w, Ok, hI]
  · exact Finset.prod_congr rfl fun d hd => hZ d hd G g x

end Lax119563Proofs.HomChar
