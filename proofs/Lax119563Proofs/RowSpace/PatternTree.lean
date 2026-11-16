import Lax119563Proofs.RowSpace.Realize
import Lax119563Proofs.RowSpace.Exposed
import Lax119563Proofs.RowSpace.TreeLike
import Lax119563.ContradictionTrees

/-!
# Patterns give contradiction trees

Paper, Theorem "pattern-tree": if `F` has a one-vertex tree decomposition of width at most `k`
and `hom(F, G₀) ≠ hom(F, G₁)`, then `I` has a contradiction tree with at most `5|V(F)| + 1`
nodes.

By the affine dichotomy, `hom(F, G₁) = 0` and some homomorphism `F → G₀` fixes the class of
every vertex. The linear system `L` has as variables the pairs `top p γ`: the vertex closest to
the root from which the variable `γ`, exposed at the bag of `p`, is inherited. Its equations are
the equations newly exposed at the vertices (at most one per vertex) and the unit equations of
initialized variables at their top vertices (at most four per vertex). Ordering the vertices by
decreasing depth makes the equations tree-like; a solution of `L` would give a homomorphism
`F → G₁` by local realization, so `L` is unsolvable and yields a contradiction tree, which
projects to `I`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.ColoredHomomorphisms Lax119563.ParitySystems Lax119563.ContradictionTrees
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ} {F : ColoredGraph}

/-! ### Tree-like lists from pairwise conditions -/

lemma mem_unionAll {V : Type*} [DecidableEq V] {l : List (Finset V)} {x : V} :
    x ∈ unionAll l ↔ ∃ E ∈ l, x ∈ E := by
  induction l with
  | nil => simp [unionAll]
  | cons a l ih =>
    show x ∈ a ∪ unionAll l ↔ _
    rw [Finset.mem_union, ih]
    simp

lemma treeLike_flatMap {V β : Type*} [DecidableEq V] (R : β → β → Prop)
    (g : β → List (Finset V)) (S : β → Finset V → Finset V)
    (hlen : ∀ b, (g b).length ≤ 1)
    (hmeet : ∀ b E, E ∈ g b → ∀ b', R b b' → ∀ E' ∈ g b', E ∩ E' ⊆ S b E)
    (hS : ∀ b E, E ∈ g b → (S b E).card ≤ 1) :
    ∀ order : List β, order.Pairwise R → TreeLike (order.flatMap g) := by
  intro order
  induction order with
  | nil => intro _; exact TreeLike.nil
  | cons b rest ih =>
    intro hP
    rw [List.pairwise_cons] at hP
    rw [List.flatMap_cons]
    have hrest := ih hP.2
    match hg : g b, hlen b with
    | [], _ => simpa using hrest
    | [E], _ =>
      refine TreeLike.cons ?_ hrest
      refine (Finset.card_le_card fun x hx => ?_).trans (hS b E (by rw [hg]; simp))
      obtain ⟨hxE, hxU⟩ := Finset.mem_inter.mp hx
      obtain ⟨E', hE', hxE'⟩ := mem_unionAll.mp hxU
      obtain ⟨b', hb', hE'b'⟩ := List.mem_flatMap.mp hE'
      exact hmeet b E (by rw [hg]; simp) b' (hP.1 b' hb') E' hE'b'
        (Finset.mem_inter.mpr ⟨hxE, hxE'⟩)
    | _ :: _ :: _, h => simp at h

/-! ### The forest structure -/

/-- Variables of `I`. -/
abbrev IVar (I : ImplicitParitySystem k ℓ) := Fin I.numLocations × (Fin k → BlockCoord ℓ)

section
variable (T : OneVertexForest F.graph k) (cl : Fin F.n → ICls I)

/-- The variables exposed at the bag of `p`. -/
noncomputable def varB (p : Fin F.n) : Finset (IVar I) := varSet (AS cl (T.bag p))

/-- The variables exposed at the bag of `p` without `p`. -/
noncomputable def varM (p : Fin F.n) : Finset (IVar I) := varSet (AS cl (bagm T p))

open Classical in
/-- The vertex from which `γ` is inherited. -/
noncomputable def top (p : Fin F.n) (γ : IVar I) : Fin F.n × IVar I :=
  match h : T.parent p with
  | none => (p, γ)
  | some q => if γ ∈ varM T cl p then top q γ else (p, γ)
termination_by T.depth p
decreasing_by exact T.depth_lt p q h

lemma top_none {p : Fin F.n} (h : T.parent p = none) (γ : IVar I) : top T cl p γ = (p, γ) := by
  rw [top]; split <;> simp_all

lemma top_some {p q : Fin F.n} (h : T.parent p = some q) (γ : IVar I) :
    top T cl p γ = if γ ∈ varM T cl p then top T cl q γ else (p, γ) := by
  rw [top]; split
  · simp_all
  · next q' h' => rw [h] at h'; cases h'; rfl

lemma top_snd : ∀ n (p : Fin F.n), T.depth p < n → ∀ γ, (top T cl p γ).2 = γ := by
  intro n
  induction n with
  | zero => intro p h; omega
  | succ n ih =>
    intro p hp γ
    cases h : T.parent p with
    | none => rw [top_none T cl h]
    | some q =>
      rw [top_some T cl h]
      split
      · exact ih q (by have := T.depth_lt p q h; omega) γ
      · rfl

lemma top_snd' (p : Fin F.n) (γ : IVar I) : (top T cl p γ).2 = γ :=
  top_snd T cl _ p (Nat.lt_succ_self _) γ

lemma top_depth : ∀ n (p : Fin F.n), T.depth p < n → ∀ γ,
    T.depth (top T cl p γ).1 ≤ T.depth p ∧
      ((top T cl p γ).1 ≠ p → T.depth (top T cl p γ).1 < T.depth p) := by
  intro n
  induction n with
  | zero => intro p h; omega
  | succ n ih =>
    intro p hp γ
    cases h : T.parent p with
    | none => rw [top_none T cl h]; simp
    | some q =>
      have hq := T.depth_lt p q h
      rw [top_some T cl h]
      split
      · have := ih q (by omega) γ
        exact ⟨by omega, fun _ => by omega⟩
      · simp

lemma top_depth' (p : Fin F.n) (γ : IVar I) :
    T.depth (top T cl p γ).1 ≤ T.depth p ∧
      ((top T cl p γ).1 ≠ p → T.depth (top T cl p γ).1 < T.depth p) :=
  top_depth T cl _ p (Nat.lt_succ_self _) γ

lemma not_mem_varSet_empty (hk : 0 < k) (γ : IVar I) : γ ∉ varSet (∅ : Finset (ICls I)) := by
  intro h
  rw [mem_varSet] at h
  have : (supp γ.2).card = 0 := by
    rw [Finset.card_eq_zero]; simpa [Iloc] using h.2
  rw [card_supp] at this; omega

lemma varM_root (hk : 0 < k) {p : Fin F.n} (h : T.parent p = none) (γ : IVar I) :
    γ ∉ varM T cl p := by
  rw [varM, bagm_root T h]
  exact not_mem_varSet_empty hk γ

lemma varM_sub {p q : Fin F.n} (h : T.parent p = some q) : varM T cl p ⊆ varB T cl q := by
  intro γ hγ
  rw [varM, mem_varSet] at hγ
  rw [varB, mem_varSet]
  exact ⟨hγ.1, hγ.2.trans (Iloc_mono (AS_bagm_sub T cl h) _)⟩

/-- The top of an exposed variable: it is exposed there but not inherited. -/
lemma top_spec (hk : 0 < k) : ∀ n (p : Fin F.n), T.depth p < n → ∀ γ, γ ∈ varB T cl p →
    (top T cl p γ).2 = γ ∧ γ ∈ varB T cl (top T cl p γ).1 ∧ γ ∉ varM T cl (top T cl p γ).1 := by
  intro n
  induction n with
  | zero => intro p h; omega
  | succ n ih =>
    intro p hp γ hγ
    cases h : T.parent p with
    | none => rw [top_none T cl h]; exact ⟨rfl, hγ, varM_root T cl hk h γ⟩
    | some q =>
      rw [top_some T cl h]
      split
      · next hm => exact ih q (by have := T.depth_lt p q h; omega) γ (varM_sub T cl h hm)
      · next hm => exact ⟨rfl, hγ, hm⟩

/-! ### The system `L` -/

open Classical in
/-- The equations newly exposed at the bag of `p`, as schema and address. -/
noncomputable def newPairs (p : Fin F.n) : Finset (Fin I.schemas.length × (Fin k → BlockCoord ℓ)) :=
  Finset.univ.filter fun x => IsAddress x.2 ∧ supp x.2 ⊆ Isch (AS cl (T.bag p)) x.1 ∧
    ¬ supp x.2 ⊆ Isch (AS cl (bagm T p)) x.1

/-- The equation of `L` contributed at `p` by the schema equation `x`. -/
noncomputable def eqAt (p : Fin F.n) (x : Fin I.schemas.length × (Fin k → BlockCoord ℓ)) :
    Finset (Fin F.n × IVar I) :=
  ((sch I x.1).equation x.2).image (top T cl p)

/-- The new equations at `p`. -/
noncomputable def newEqs (p : Fin F.n) : Finset (Finset (Fin F.n × IVar I)) :=
  (newPairs T cl p).image (eqAt T cl p)

lemma mem_newPairs {p : Fin F.n} {x : Fin I.schemas.length × (Fin k → BlockCoord ℓ)} :
    x ∈ newPairs T cl p ↔ IsAddress x.2 ∧ supp x.2 ⊆ Isch (AS cl (T.bag p)) x.1 ∧
      ¬ supp x.2 ⊆ Isch (AS cl (bagm T p)) x.1 := by
  classical
  simp [newPairs]

lemma card_AS_bag (p : Fin F.n) : (AS cl (T.bag p)).card ≤ k + 1 :=
  Finset.card_image_le.trans (T.card_bag p)

lemma card_newEqs (hk : 3 ≤ k) (p : Fin F.n) : (newEqs T cl p).card ≤ 1 := by
  refine Finset.card_image_le.trans (Finset.card_le_one.mpr fun x hx y hy => ?_)
  rw [mem_newPairs] at hx hy
  obtain ⟨h1, h2⟩ := exposed_unique (by omega) (card_AS_bag T cl p) hx.1 hy.1 hx.2.1 hy.2.1
  exact Prod.ext h1 h2

lemma eqAt_eq (p : Fin F.n) (e : Fin I.schemas.length) (a : Fin k → BlockCoord ℓ) :
    eqAt T cl p (e, a) = Finset.univ.image fun i => top T cl p (argVar I e i a) := by
  rw [eqAt, equation_eq, Finset.image_image]
  rfl

lemma top_argVar_injective (p : Fin F.n) (e : Fin I.schemas.length) (a : Fin k → BlockCoord ℓ) :
    Function.Injective fun i => top T cl p (argVar I e i a) := by
  intro i j h
  have := congrArg Prod.snd h
  simp only [top_snd'] at this
  exact argVar_injective I e a this

/-- The variables of a new equation inherited from the parent: at most one. -/
noncomputable def inheritedPart (p : Fin F.n) (E : Finset (Fin F.n × IVar I)) :
    Finset (Fin F.n × IVar I) := by
  classical
  exact E.filter fun x => x.2 ∈ varM T cl p

lemma card_inheritedPart (hk : 3 ≤ k) {p : Fin F.n} {E : Finset (Fin F.n × IVar I)}
    (hE : E ∈ newEqs T cl p) : (inheritedPart T cl p E).card ≤ 1 := by
  classical
  obtain ⟨⟨e, a⟩, hx, rfl⟩ := Finset.mem_image.mp hE
  rw [mem_newPairs] at hx
  refine Finset.card_le_one.mpr fun x hx' y hy' => ?_
  simp only [inheritedPart, Finset.mem_filter, eqAt_eq, Finset.mem_image, Finset.mem_univ,
    true_and] at hx' hy'
  obtain ⟨⟨i, rfl⟩, hi⟩ := hx'
  obtain ⟨⟨j, rfl⟩, hj⟩ := hy'
  by_cases hij : i = j
  · rw [hij]
  exfalso
  rw [top_snd', varM, mem_varSet] at hi hj
  exact hx.2.2 (geometry ((card_AS_bagm T cl p).trans le_rfl) e hij hi.2 hj.2)

lemma meet_sub (hk : 3 ≤ k) {p q : Fin F.n} (hpq : p ≠ q) (hd : T.depth q ≤ T.depth p)
    {E E' : Finset (Fin F.n × IVar I)} (hE : E ∈ newEqs T cl p) (hE' : E' ∈ newEqs T cl q) :
    E ∩ E' ⊆ inheritedPart T cl p E := by
  classical
  intro x hx
  obtain ⟨hxE, hxE'⟩ := Finset.mem_inter.mp hx
  simp only [inheritedPart, Finset.mem_filter]
  refine ⟨hxE, ?_⟩
  obtain ⟨⟨e, a⟩, -, rfl⟩ := Finset.mem_image.mp hE
  obtain ⟨⟨e', a'⟩, -, rfl⟩ := Finset.mem_image.mp hE'
  rw [eqAt, Finset.mem_image] at hxE hxE'
  obtain ⟨γ, -, rfl⟩ := hxE
  obtain ⟨γ', -, hγ'⟩ := hxE'
  rw [top_snd']
  by_contra hm
  have htop : top T cl p γ = (p, γ) := by
    cases h : T.parent p with
    | none => exact top_none T cl h γ
    | some r => rw [top_some T cl h, if_neg hm]
  have h1 := top_depth' T cl q γ'
  rw [hγ', htop] at h1
  simp only at h1
  exact hpq (by by_contra hne; exact absurd (h1.2 hne) (by omega))

end

/-! ### The parity system `L` -/

section
variable (hk : 3 ≤ k) (T : OneVertexForest F.graph k) (cl : Fin F.n → ICls I)
  (hcl : ∀ p, cl p ∈ classes I)
include hk hcl

omit hk in
lemma newPairs_dom {p : Fin F.n} {x : Fin I.schemas.length × (Fin k → BlockCoord ℓ)}
    (hx : x ∈ newPairs T cl p) : supp x.2 ⊆ dom I x.1 := by
  rw [mem_newPairs] at hx
  refine hx.2.1.trans (Isch_sub_dom (fun X hX => ?_) _)
  obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hX
  exact hcl r

lemma newEqs_props {p : Fin F.n} {E : Finset (Fin F.n × IVar I)} (hE : E ∈ newEqs T cl p) :
    Set.InjOn Prod.snd (E : Set (Fin F.n × IVar I)) ∧
      E.image Prod.snd ∈ I.toParitySystem.equations := by
  obtain ⟨⟨e, a⟩, hx, rfl⟩ := Finset.mem_image.mp hE
  have hdom := newPairs_dom T cl hcl hx
  rw [mem_newPairs] at hx
  refine ⟨?_, ?_⟩
  · rintro x hx' y hy' h
    simp only [eqAt, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx' hy'
    obtain ⟨γ, -, rfl⟩ := hx'
    obtain ⟨δ, -, rfl⟩ := hy'
    simp only [top_snd'] at h
    rw [h]
  · rw [eqAt, Finset.image_image]
    have : Prod.snd ∘ top T cl p = id := funext fun γ => top_snd' T cl p γ
    rw [this, Finset.image_id]
    exact equation_mem I e hx.1 hdom

/-- The unit facts of `L`. -/
noncomputable def units : Finset ((Fin F.n × IVar I) × ZMod 2) := by
  classical
  exact (Finset.univ : Finset (Fin F.n)).biUnion fun q =>
    ((varB T cl q).filter fun γ => γ ∉ varM T cl q ∧ (I.init γ.1).isSome).image
      fun γ => ((q, γ), (I.init γ.1).getD 0)

omit hk hcl in
lemma mem_units {u : (Fin F.n × IVar I) × ZMod 2} :
    u ∈ units T cl ↔ u.1.2 ∈ varB T cl u.1.1 ∧ u.1.2 ∉ varM T cl u.1.1 ∧
      I.init u.1.2.1 = some u.2 := by
  classical
  obtain ⟨⟨q, γ⟩, b⟩ := u
  simp only [units, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨q', γ', ⟨h1, h2, h3⟩, ⟨rfl, rfl⟩, rfl⟩
    refine ⟨h1, h2, ?_⟩
    cases h : I.init γ'.1 with
    | none => rw [h] at h3; simp at h3
    | some b => simp
  · rintro ⟨h1, h2, h3⟩
    exact ⟨q, γ, ⟨h1, h2, by simp [h3]⟩, ⟨rfl, rfl⟩, by simp [h3]⟩

omit hcl in
lemma card_units : (units T cl).card ≤ 4 * F.n := by
  classical
  unfold units
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ q, _ ≤ ∑ _q : Fin F.n, 4 := Finset.sum_le_sum fun q _ =>
        Finset.card_image_le.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans
          (card_varSet_le hk (card_AS_bag T cl q)))
    _ = 4 * F.n := by simp [mul_comm]

/-- The parity system `L`. -/
noncomputable def Lsys : ParitySystem (Fin F.n × IVar I) where
  equations := {E | ∃ p, E ∈ newEqs T cl p}
  card_equation := by
    rintro E ⟨p, hE⟩
    obtain ⟨hinj, hmem⟩ := newEqs_props hk T cl hcl hE
    rw [← Finset.card_image_of_injOn hinj]
    exact I.toParitySystem.card_equation _ hmem
  initial := {u | u ∈ units T cl}

/-- The vertices ordered by decreasing depth. -/
noncomputable def order : List (Fin F.n) :=
  (List.finRange F.n).mergeSort fun p q => decide (T.depth q ≤ T.depth p)

omit hk hcl in
lemma order_pairwise :
    (order T).Pairwise fun p q => p ≠ q ∧ T.depth q ≤ T.depth p := by
  have h1 := List.pairwise_mergeSort (le := fun p q : Fin F.n => decide (T.depth q ≤ T.depth p))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega)
    (fun a b => by simp; omega) (List.finRange F.n)
  have h2 : (order T).Nodup := ((List.mergeSort_perm _ _).nodup_iff).mpr (List.nodup_finRange _)
  exact (h2.and h1).imp fun ⟨h, h'⟩ => ⟨h, by simpa using h'⟩

omit hk hcl in
lemma mem_order (p : Fin F.n) : p ∈ order T :=
  (List.mergeSort_perm _ _).mem_iff.mpr (List.mem_finRange p)

/-- The equations of `L`, in tree-like order. -/
noncomputable def eqList : List (Finset (Fin F.n × IVar I)) :=
  (order T).flatMap fun p => (newEqs T cl p).toList

omit hcl in
lemma eqList_treeLike : TreeLike (eqList T cl) := by
  classical
  refine treeLike_flatMap (fun p q => p ≠ q ∧ T.depth q ≤ T.depth p)
    (fun p => (newEqs T cl p).toList) (fun p E => inheritedPart T cl p E)
    (fun p => by rw [Finset.length_toList]; exact card_newEqs T cl hk p)
    (fun p E hE q hpq E' hE' => meet_sub T cl hk hpq.1 hpq.2 (Finset.mem_toList.mp hE)
      (Finset.mem_toList.mp hE'))
    (fun p E hE => card_inheritedPart T cl hk (Finset.mem_toList.mp hE)) _ (order_pairwise T)

omit hk hcl in
lemma length_flatMap_le {β γ : Type*} (l : List β) (g : β → List γ) (h : ∀ b, (g b).length ≤ 1) :
    (l.flatMap g).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons b l ih => rw [List.flatMap_cons, List.length_append, List.length_cons]; have := h b; omega

omit hcl in
lemma length_eqList : (eqList T cl).length ≤ F.n := by
  refine (length_flatMap_le _ _ fun p => ?_).trans ?_
  · rw [Finset.length_toList]; exact card_newEqs T cl hk p
  · rw [order, List.length_mergeSort, List.length_finRange]

end

instance (F : ColoredGraph) (ε : ZMod 2) : Finite (RHom I F ε) :=
  Finite.of_injective (fun φ : RHom I F ε => (φ.1 : Fin F.n → Fin (rsGraph I ε).n))
    fun a b h => Subtype.ext (RelHom.ext (congrFun h))

/-- **Patterns give contradiction trees** (paper, Theorem "pattern-tree"). -/
theorem pattern_tree (hk : 3 ≤ k) (T : OneVertexForest F.graph k)
    (hne : hom F (rsGraph I 0) ≠ hom F (rsGraph I 1)) :
    HasContradictionWithin I.toParitySystem (5 * F.n + 1) := by
  classical
  obtain ⟨hz, ⟨h₀⟩⟩ := hom_dichotomy F hne
  set cl : Fin F.n → ICls I := fun p => (vx (h₀.1 p)).1 with hcl_def
  have hcl : ∀ p, cl p ∈ classes I := fun p => (mem_verts_zero.mp (vx_mem (h₀.1 p))).1
  have hk0 : 0 < k := by omega
  have hmem : ∀ E ∈ eqList T cl, E ∈ (Lsys hk T cl hcl).equations := by
    intro E hE
    obtain ⟨p, -, hp⟩ := List.mem_flatMap.mp hE
    exact ⟨p, Finset.mem_toList.mp hp⟩
  have hun : ¬ ∃ y : Fin F.n × IVar I → ZMod 2,
      (∀ E ∈ eqList T cl, ∑ x ∈ E, y x = 0) ∧ ∀ u ∈ units T cl, y u.1 = u.2 := by
    rintro ⟨y, hy1, hy2⟩
    let α : Fin F.n → Val I := fun p γ => y (top T cl p γ)
    have hagree : ∀ p q, T.parent p = some q → ∀ v a, IsAddress a →
        supp a ⊆ Iloc (AS cl (bagm T p)) v → α p (v, a) = α q (v, a) := by
      intro p q hpq v a ha hs
      simp only [α]
      rw [top_some T cl hpq, if_pos (by rw [varM, mem_varSet]; exact ⟨ha, hs⟩)]
    have hsat : ∀ n p, T.depth p < n → SatEqs (AS cl (T.bag p)) (α p) := by
      intro n
      induction n with
      | zero => intro p h; omega
      | succ n ih =>
        intro p hp e a ha hs
        by_cases hold : supp a ⊆ Isch (AS cl (bagm T p)) e
        · cases hpar : T.parent p with
          | none =>
            exfalso
            rw [bagm_root T hpar] at hold
            have : (supp a).card = 0 := by
              rw [Finset.card_eq_zero]
              exact Finset.subset_empty.mp (hold.trans (by simp [AS, Isch]))
            rw [card_supp] at this; omega
          | some q =>
            have hq := T.depth_lt p q hpar
            have := ih q (by omega) e a ha (hold.trans (Isch_mono (AS_bagm_sub T cl hpar) e))
            rw [← this]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [α]
            rw [top_some T cl hpar, if_pos]
            rw [varM, mem_varSet]
            refine ⟨isAddress_act _ ha, ?_⟩
            simp only [argVar]
            rw [supp_act]
            intro d hd
            obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
            exact Isch_args (hold hc) i
        · have hx : (e, a) ∈ newPairs T cl p := (mem_newPairs T cl).mpr ⟨ha, hs, hold⟩
          have hE : eqAt T cl p (e, a) ∈ eqList T cl :=
            List.mem_flatMap.mpr ⟨p, mem_order T p,
              Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hx)⟩
          have := hy1 _ hE
          rw [eqAt_eq, Finset.sum_image fun i _ j _ h => top_argVar_injective T cl p e a h]
            at this
          exact this
    have hinit : ∀ p, InitAgree (AS cl (T.bag p)) (α p) := by
      intro p v a b hb ha hs
      have hγ : (v, a) ∈ varB T cl p := by rw [varB, mem_varSet]; exact ⟨ha, hs⟩
      obtain ⟨h1, h2, h3⟩ := top_spec T cl hk0 _ p (Nat.lt_succ_self _) _ hγ
      have hu : (((top T cl p (v, a)).1, (v, a)), b) ∈ units T cl :=
        (mem_units T cl).mpr ⟨h2, h3, hb⟩
      have := hy2 _ hu
      simp only [α]
      conv_lhs => rw [← Prod.mk.eta (p := top T cl p (v, a)), h1]
      exact this
    obtain ⟨ψ⟩ := local_realization hk T h₀ α hagree
      (fun p => hsat _ p (Nat.lt_succ_self _)) hinit
    have : Nonempty (RHom I F 1) := ⟨ψ⟩
    have : 0 < hom F (rsGraph I 1) := Nat.card_pos (α := RHom I F 1)
    omega
  have hL := hasContradiction_of_unsolvable (Lsys hk T cl hcl) (eqList_treeLike hk T cl)
    hmem (units T cl) (fun u hu => hu) hun
  have hI := HasContradictionWithin.map (Q := I.toParitySystem) Prod.snd
    (fun E hE => by obtain ⟨p, hE⟩ := hE; exact newEqs_props hk T cl hcl hE)
    (fun u hu => by
      obtain ⟨h1, -, h3⟩ := (mem_units T cl).mp hu
      rw [varB, mem_varSet] at h1
      exact ⟨u.2, h3, rfl, h1.1, h1.2.trans (Iloc_sub_dom (fun X hX => by
        obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hX; exact hcl r) _)⟩) hL
  refine HasContradictionWithin.mono hI ?_
  have := length_eqList hk T cl
  have := card_units hk T cl
  omega

end Lax119563Proofs.RowSpace
