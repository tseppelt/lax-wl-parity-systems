import Lax119563.WLProblems
import Lax119563Proofs.Machines.Numbers

/-!
# Decoding WL instances, and fixed instances

* `encodeNats` is injective (`encodeNats_injective`), and the description of a colored graph
  determines the graph and is self-delimiting (`graphDescription_append_inj`). Hence
  `encodeWLInstance k G H ∈ WLDistinguishing ↔ Distinguishes k G H`
  (`encodeWLInstance_mem_iff`).
* The leading number of an encoded instance is its dimension (`leadingNat_encodeWLInstance`).
* Fixed instances: `k`-WL (`k ≥ 1`) distinguishes a one-vertex graph from the empty graph
  (`distinguishes_one_empty`) and never distinguishes a graph from itself
  (`not_distinguishes_self`).
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.WLProblems

namespace Lax119563Proofs.Hardness

/-! ## Numbers -/

/-- The code of a digit list. -/
def codeL (ds : List Bool) : List Bool := ds.flatMap (fun d => [true, d]) ++ [false]

lemma encodeNat_eq_codeL (m : ℕ) : encodeNat m = codeL (Nat.bits m) := rfl

lemma codeL_append_inj : ∀ {ds ds' : List Bool} {r r' : List Bool},
    codeL ds ++ r = codeL ds' ++ r' → ds = ds' ∧ r = r'
  | [], [], r, r', h => by simpa [codeL] using h
  | [], d' :: ds', r, r', h => by simp [codeL] at h
  | d :: ds, [], r, r', h => by simp [codeL] at h
  | d :: ds, d' :: ds', r, r', h => by
    simp only [codeL, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc,
      List.cons.injEq, true_and] at h
    obtain ⟨rfl, h⟩ := h
    have := codeL_append_inj (ds := ds) (ds' := ds') (r := r) (r' := r')
      (by simpa [codeL] using h)
    exact ⟨by rw [this.1], this.2⟩

lemma encodeNat_append_inj {a b : ℕ} {r r' : List Bool}
    (h : encodeNat a ++ r = encodeNat b ++ r') : a = b ∧ r = r' := by
  rw [encodeNat_eq_codeL, encodeNat_eq_codeL] at h
  obtain ⟨h1, h2⟩ := codeL_append_inj h
  exact ⟨Machines.bits_injective h1, h2⟩

/-- **`encodeNats` is injective.** -/
theorem encodeNats_injective : Function.Injective encodeNats := by
  intro l
  induction l with
  | nil =>
    intro l' h
    cases l' with
    | nil => rfl
    | cons b l' => simp [encodeNats, encodeNat] at h
  | cons a l ih =>
    intro l' h
    cases l' with
    | nil => simp [encodeNats, encodeNat] at h
    | cons b l' =>
      simp only [encodeNats, List.flatMap_cons] at h
      obtain ⟨rfl, h2⟩ := encodeNat_append_inj h
      rw [ih h2]

/-- The leading number of a code. -/
lemma leadingNat_codeL (ds : List Bool) (r : List Bool) :
    leadingNat (codeL ds ++ r) = Machines.valBits ds := by
  induction ds with
  | nil => simp [codeL, leadingNat, Machines.valBits]
  | cons d ds ih =>
    simp only [codeL, List.flatMap_cons, List.cons_append, List.nil_append,
      List.append_assoc] at ih ⊢
    rw [leadingNat, ih, Machines.valBits]
    cases d <;> rfl

lemma leadingNat_encodeNat_append (m : ℕ) (r : List Bool) :
    leadingNat (encodeNat m ++ r) = m := by
  rw [encodeNat_eq_codeL, leadingNat_codeL, Machines.valBits_bits]

/-- **The leading number of an encoded instance is its dimension.** -/
theorem leadingNat_encodeWLInstance (k : ℕ) (G H : ColoredGraph) :
    leadingNat (encodeWLInstance k G H) = k := by
  rw [encodeWLInstance, wlWord, encodeNats, List.flatMap_cons]
  exact leadingNat_encodeNat_append k _

/-! ## Graphs -/

lemma mem_edgeList {G : ColoredGraph} {u v : Fin G.n} :
    ((u : ℕ), (v : ℕ)) ∈ edgeList G ↔ u < v ∧ G.graph.Adj u v := by
  classical
  unfold edgeList
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map, Prod.mk.injEq]
  simp
  constructor
  · rintro ⟨a, ⟨b, hb, hv⟩, ha⟩
    rw [Fin.val_inj] at hv ha
    subst hv ha; exact hb
  · intro h; exact ⟨u, ⟨v, h, rfl⟩, rfl⟩

lemma flatMap_pair_inj : ∀ {l l' : List (ℕ × ℕ)},
    l.flatMap (fun e => [e.1, e.2]) = l'.flatMap (fun e => [e.1, e.2]) → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | (a, b) :: l, (a', b') :: l', h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl, h⟩ := h
    rw [flatMap_pair_inj h]

lemma graph_eq_of {G G' : ColoredGraph} (hn : G.n = G'.n)
    (hc : (List.finRange G.n).map G.color = (List.finRange G'.n).map G'.color)
    (he : edgeList G = edgeList G') : G = G' := by
  obtain ⟨n, g, c⟩ := G
  obtain ⟨n', g', c'⟩ := G'
  simp only at hn
  subst hn
  simp only at hc
  have hcol : c = c' := by
    funext i
    have := congrArg (fun l => l[(i : ℕ)]?) hc
    simpa using this
  subst hcol
  have hadj : ∀ u v : Fin n, u < v → (g.Adj u v ↔ g'.Adj u v) := by
    intro u v huv
    have h1 := @mem_edgeList ⟨n, g, c⟩ u v
    have h2 := @mem_edgeList ⟨n, g', c⟩ u v
    rw [he] at h1
    simp only at h1 h2
    constructor
    · intro h; exact (h2.mp (h1.mpr ⟨huv, h⟩)).2
    · intro h; exact (h1.mp (h2.mpr ⟨huv, h⟩)).2
  have : g = g' := by
    ext u v
    rcases lt_trichotomy u v with h | rfl | h
    · exact hadj u v h
    · simp
    · rw [g.adj_comm, g'.adj_comm]; exact hadj v u h
  subst this
  rfl

/-- **Graph descriptions are self-delimiting and determine the graph.** -/
theorem graphDescription_append_inj {G G' : ColoredGraph} {r r' : List ℕ}
    (h : graphDescription G ++ r = graphDescription G' ++ r') : G = G' ∧ r = r' := by
  unfold graphDescription at h
  simp only [List.cons_append, List.append_assoc, List.cons.injEq] at h
  obtain ⟨hn, h⟩ := h
  obtain ⟨hc, h⟩ := List.append_inj h (by simp [hn])
  simp only [List.cons.injEq] at h
  obtain ⟨hm, h⟩ := h
  obtain ⟨he, hr⟩ := List.append_inj h (by simp [hm])
  exact ⟨graph_eq_of hn hc (flatMap_pair_inj he), hr⟩

/-- **Membership of encoded instances.** -/
theorem encodeWLInstance_mem_iff (k : ℕ) (G H : ColoredGraph) :
    encodeWLInstance k G H ∈ WLDistinguishing ↔ Distinguishes k G H := by
  constructor
  · rintro ⟨k', G', H', heq, hd⟩
    have hw := encodeNats_injective heq
    simp only [wlWord, List.cons.injEq] at hw
    obtain ⟨rfl, hw⟩ := hw
    obtain ⟨rfl, hw⟩ := graphDescription_append_inj hw
    obtain ⟨rfl, -⟩ := graphDescription_append_inj (r := []) (r' := []) (by simpa using hw)
    exact hd
  · intro hd
    exact ⟨k, G, H, rfl, hd⟩

/-! ## Fixed instances -/

end Lax119563Proofs.Hardness
