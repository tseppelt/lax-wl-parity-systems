import Lax119563Proofs.RowSpace.Affine
import Lax119563Proofs.RowSpace.Duplicator
import Lax119563Proofs.RowSpace.OneVertex

/-!
# Local realization

Let `F` admit a homomorphism to `G₀` (which fixes the class `cl p` of every vertex) and a
one-vertex tree decomposition of width at most `k`. Values `α_p` on the variables exposed at
the bags, agreeing along the forest, satisfying the exposed equations and the initialization,
give a homomorphism `F → G₁` (paper, Lemma "Local realization"): top-down along the forest we
extend seed descriptions with the local extension lemma, and map every vertex to the image of
the zero vertex of its class under the description of its bag.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.ColoredHomomorphisms
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ} {F : ColoredGraph}

/-- The classes of a set of vertices. -/
def AS (cl : Fin F.n → ICls I) (S : Finset (Fin F.n)) : Finset (ICls I) := S.image cl

/-- The bag of `p` without `p`. -/
def bagm {F : ColoredGraph} (T : OneVertexForest F.graph k) (p : Fin F.n) : Finset (Fin F.n) :=
  (T.bag p).erase p

variable (T : OneVertexForest F.graph k) (cl : Fin F.n → ICls I)

lemma AS_bag (p : Fin F.n) : AS cl (T.bag p) = insert (cl p) (AS cl (bagm T p)) := by
  rw [AS, AS, bagm, ← Finset.image_insert, Finset.insert_erase (T.mem_bag p)]

lemma AS_bagm_sub {p q : Fin F.n} (h : T.parent p = some q) :
    AS cl (bagm T p) ⊆ AS cl (T.bag q) :=
  Finset.image_subset_image (T.bag_sub p q h)

lemma card_AS_bagm (p : Fin F.n) : (AS cl (bagm T p)).card ≤ k := by
  refine Finset.card_image_le.trans ?_
  rw [bagm, Finset.card_erase_of_mem (T.mem_bag p)]
  have := T.card_bag p
  omega

lemma bagm_root {p : Fin F.n} (h : T.parent p = none) : bagm T p = ∅ := T.bag_root p h

/-- The invariant of the descriptions at a vertex. -/
def RealInv (α : Fin F.n → Val I) (D : Fin F.n → RDesc I) (p : Fin F.n) : Prop :=
  DGood (AS cl (T.bag p)) (D p) ∧ Realizes (AS cl (T.bag p)) (D p) (α p) ∧
    ∀ q, T.parent p = some q → ∀ Y ∈ AS cl (bagm T p), rshift (D p) Y = rshift (D q) Y

section
variable {T cl}
variable (hk : 3 ≤ k) (hcl : ∀ p, cl p ∈ classes I) (α : Fin F.n → Val I)
  (hagree : ∀ p q, T.parent p = some q → ∀ v a, IsAddress a →
    supp a ⊆ Iloc (AS cl (bagm T p)) v → α p (v, a) = α q (v, a))
  (hsat : ∀ p, SatEqs (AS cl (T.bag p)) (α p))
  (hinit : ∀ p, InitAgree (AS cl (T.bag p)) (α p))
include hk hcl hagree hsat hinit

omit hk hagree hsat hinit in
lemma AS_sub (S : Finset (Fin F.n)) : AS cl S ⊆ classes I := by
  intro X hX
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hX
  exact hcl p

/-- One step: extending the description of the parent. -/
lemma real_step (p : Fin F.n) (Dq : RDesc I)
    (hq : ∀ q, T.parent p = some q →
      DGood (AS cl (T.bag q)) Dq ∧ Realizes (AS cl (T.bag q)) Dq (α q)) :
    ∃ Dp, DGood (AS cl (T.bag p)) Dp ∧ Realizes (AS cl (T.bag p)) Dp (α p) ∧
      (∀ q, T.parent p = some q → ∀ Y ∈ AS cl (bagm T p), rshift Dp Y = rshift Dq Y) := by
  have hA := AS_sub hcl (bagm T p)
  -- the base description on the classes of `bagm p`
  obtain ⟨D0, hG0, hR0, hsh⟩ : ∃ D0, DGood (AS cl (bagm T p)) D0 ∧
      Realizes (AS cl (bagm T p)) D0 (α p) ∧
      ∀ q, T.parent p = some q → D0 = Dq := by
    cases hp : T.parent p with
    | none =>
      have : AS cl (bagm T p) = ∅ := by rw [bagm_root T hp]; rfl
      rw [this]
      exact ⟨rdesc0 I, dgood_empty, realizes_empty (by omega) _ _, fun q h => by simp at h⟩
    | some q =>
      obtain ⟨hG, hR⟩ := hq q hp
      refine ⟨Dq, hG.mono (AS_bagm_sub T cl hp), fun v a ha hs => ?_, fun _ _ => rfl⟩
      rw [hR.mono (AS_bagm_sub T cl hp) v a ha hs, hagree p q hp v a ha hs]
  have hsat' := hsat p
  have hinit' := hinit p
  rw [AS_bag] at hsat' hinit' ⊢
  obtain ⟨D', h1, h2, h3⟩ := local_extend (by omega) hG0 hA (hcl p) (card_AS_bagm T cl p)
    (α p) hR0 hsat' hinit'
  exact ⟨D', h1, h2, fun q hq Y hY => (h3 Y hY).trans (by rw [hsh q hq])⟩

/-- Descriptions satisfying the invariant at all vertices of depth below `N`. -/
lemma real_upto (N : ℕ) : ∃ D : Fin F.n → RDesc I, ∀ p, T.depth p < N → RealInv T cl α D p := by
  induction N with
  | zero => exact ⟨fun _ => rdesc0 I, fun p h => absurd h (Nat.not_lt_zero _)⟩
  | succ N ih =>
    classical
    obtain ⟨D, hD⟩ := ih
    have hstep : ∀ p, ∃ Dp, T.depth p = N →
        DGood (AS cl (T.bag p)) Dp ∧ Realizes (AS cl (T.bag p)) Dp (α p) ∧
        (∀ q, T.parent p = some q → ∀ Y ∈ AS cl (bagm T p), rshift Dp Y = rshift (D q) Y) := by
      intro p
      by_cases hp : T.depth p = N
      · cases hpar : T.parent p with
        | none =>
          obtain ⟨Dp, h⟩ := real_step hk hcl α hagree hsat hinit p (rdesc0 I)
            (fun q h => by rw [hpar] at h; simp at h)
          exact ⟨Dp, fun _ => ⟨h.1, h.2.1, fun q h' => by simp at h'⟩⟩
        | some q =>
          have hq := hD q (by have := T.depth_lt p q hpar; omega)
          obtain ⟨Dp, h⟩ := real_step hk hcl α hagree hsat hinit p (D q)
            (fun q' h' => by rw [hpar] at h'; cases h'; exact ⟨hq.1, hq.2.1⟩)
          refine ⟨Dp, fun _ => ⟨h.1, h.2.1, fun q' h' => ?_⟩⟩
          cases Option.some.inj h'
          exact h.2.2 q hpar
      · exact ⟨D p, fun h => absurd h hp⟩
    choose Dn hDn using hstep
    refine ⟨fun p => if T.depth p < N then D p else Dn p, fun p hp => ?_⟩
    have hpar : ∀ q, T.parent p = some q → T.depth q < N := fun q h => by
      have := T.depth_lt p q h; omega
    by_cases hlt : T.depth p < N
    · obtain ⟨h1, h2, h3⟩ := hD p hlt
      refine ⟨by simpa [hlt] using h1, by simpa [hlt] using h2, fun q hq Y hY => ?_⟩
      simp only [hlt, if_true, hpar q hq]
      exact h3 q hq Y hY
    · obtain ⟨h1, h2, h3⟩ := hDn p (by omega)
      refine ⟨by simpa [hlt] using h1, by simpa [hlt] using h2, fun q hq Y hY => ?_⟩
      simp only [hlt, if_false, hpar q hq, if_true]
      exact h3 q hq Y hY

lemma real_all : ∃ D : Fin F.n → RDesc I, ∀ p, RealInv T cl α D p := by
  obtain ⟨D, hD⟩ := real_upto hk hcl α hagree hsat hinit (Finset.univ.sup T.depth + 1)
  exact ⟨D, fun p => hD p (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p)))⟩

end

/-- Translations of the classes of a bag agree with those at the vertex introducing them. -/
lemma rshift_chain {α : Fin F.n → Val I} {D : Fin F.n → RDesc I}
    (hD : ∀ p, RealInv T cl α D p) :
    ∀ n p r, T.depth p < n → r ∈ bagm T p → rshift (D p) (cl r) = rshift (D r) (cl r) := by
  intro n
  induction n with
  | zero => intro p r h; omega
  | succ n ih =>
    intro p r hp hr
    cases hpar : T.parent p with
    | none => rw [bagm_root T hpar] at hr; simp at hr
    | some q =>
      rw [(hD p).2.2 q hpar (cl r) (Finset.mem_image_of_mem _ hr)]
      have hrq : r ∈ T.bag q := T.bag_sub p q hpar hr
      by_cases hrq' : r = q
      · rw [hrq']
      · exact ih q r (by have := T.depth_lt p q hpar; omega) (Finset.mem_erase.mpr ⟨hrq', hrq⟩)

/-- **Local realization.** -/
theorem local_realization (hk : 3 ≤ k) (T : OneVertexForest F.graph k) (h₀ : RHom I F 0)
    (α : Fin F.n → Val I)
    (hagree : ∀ p q, T.parent p = some q → ∀ v a, IsAddress a →
      supp a ⊆ Iloc (AS (fun p => (vx (h₀.1 p)).1) (bagm T p)) v → α p (v, a) = α q (v, a))
    (hsat : ∀ p, SatEqs (AS (fun p => (vx (h₀.1 p)).1) (T.bag p)) (α p))
    (hinit : ∀ p, InitAgree (AS (fun p => (vx (h₀.1 p)).1) (T.bag p)) (α p)) :
    Nonempty (RHom I F 1) := by
  set cl : Fin F.n → ICls I := fun p => (vx (h₀.1 p)).1 with hcl_def
  have hcl : ∀ p, cl p ∈ classes I := fun p => (mem_verts_zero.mp (vx_mem (h₀.1 p))).1
  obtain ⟨D, hD⟩ := real_all hk hcl α hagree hsat hinit
  have hmem : ∀ p, tr (D p) (cl p, 0) ∈ verts I 1 := fun p =>
    tr_mem (D p) (hD p).1.init (hD p).1.mask
      ((mem_names I).mpr ⟨hcl p, zero_mem_labs (hcl p)⟩)
  let ψ : Fin F.n → Fin (rsGraph I 1).n := fun p => ix 1 _ (hmem p)
  have hAsub : ∀ p, AS cl (T.bag p) ⊆ classes I := fun p X hX => by
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hX
    exact hcl r
  -- the image of `r ∈ bagm p` is also given by the description of `p`
  have hchain : ∀ p r, r ∈ bagm T p → vx (ψ r) = tr (D p) (cl r, 0) := by
    intro p r hr
    simp only [ψ, vx_ix, tr]
    rw [rshift_chain T cl hD _ p r (Nat.lt_succ_self _) hr]
  have hadj : ∀ p r, r ∈ bagm T p → F.graph.Adj p r →
      (rsGraph I 1).graph.Adj (ψ p) (ψ r) := by
    intro p r hr hpr
    rw [rs_adj, hchain p r hr]
    have hp : vx (ψ p) = tr (D p) (cl p, 0) := by simp [ψ]
    rw [hp]
    have hpb : cl p ∈ AS cl (T.bag p) := Finset.mem_image_of_mem _ (T.mem_bag p)
    have hrb : cl r ∈ AS cl (T.bag p) :=
      Finset.mem_image_of_mem _ (Finset.mem_of_mem_erase hr)
    have h0 := (h₀.1.map_rel hpr : (rsGraph I 0).graph.Adj _ _)
    rw [rs_adj] at h0
    exact (radj_tr (D p) (x := (cl p, 0)) (y := (cl r, 0)) (edgeOK_of (hD p).1 (hAsub p) hpb)
      (edgeOK_of (hD p).1 (hAsub p) hrb)).mp (radj_zero h0)
  refine ⟨⟨⟨ψ, fun {p r} hpr => ?_⟩, fun p => ?_⟩⟩
  · rcases T.adj_mem p r hpr with h | h
    · exact hadj p r h hpr
    · exact (hadj r p h hpr.symm).symm
  · rw [← h₀.2 p, rs_color, rs_color]
    show code I (vx (ix 1 _ (hmem p))).1 = code I (vx (h₀.1 p)).1
    rw [vx_ix]
    rfl

end Lax119563Proofs.RowSpace
