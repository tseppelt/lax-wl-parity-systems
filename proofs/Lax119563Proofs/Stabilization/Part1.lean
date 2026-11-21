import Lax119563.ColoredHomomorphisms
import Lax119563.ContradictionTrees
import Lax119563.Stabilization
import Lax119563.WeisfeilerLeman
import Lax119563Proofs.Programs.Part1
import Lax119563Proofs.RowSpace.Part1
import Mathlib

/-! ### Formerly `Lax119563Proofs.RowSpace.PatternTree` -/

section RowSpace_PatternTree

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

end RowSpace_PatternTree

/-! ### Formerly `Lax119563Proofs.HomChar.Det` -/

section HomChar_Det

/-!
# Tensors determined by Weisfeiler–Leman colors

A *tensor family* assigns to every colored graph `G` a function `(Fin k → Fin G.n) → ℕ`. It is
*determined in round `r`* (`Det r φ`) if its value at `p̄` is a function of the round-`r` color
`χ^{(r)}_k[G](p̄)`, uniformly in `G` (colors are compared syntactically across graphs).

Determined families contain the atomic tensors (round `0`), are closed under products, and under
the *extension* `p̄ ↦ ∑_q ∏_i ψ_i(p̄[q/i])` (one more round). If `k`-WL does not distinguish `G`
and `H` after `r` rounds, then the sums over all tuples of a round-`r` determined family agree.
-/

namespace Lax119563Proofs.HomChar

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman

variable {k : ℕ}

/-- A tensor family: a function on the `k`-tuples of every colored graph. -/
abbrev Fam (k : ℕ) := (G : ColoredGraph) → (Fin k → Fin G.n) → ℕ

/-- `φ` is determined by the round-`r` colors of `k`-WL. -/
def Det (r : ℕ) (φ : Fam k) : Prop :=
  ∃ f : Color k r → ℕ, ∀ G p, φ G p = f (color G r p)

/-- `φ` is determined by the colors of some round. -/
def DetAny (φ : Fam k) : Prop := ∃ r, Det r φ

lemma Det.succ {r : ℕ} {φ : Fam k} (h : Det r φ) : Det (r + 1) φ := by
  obtain ⟨f, hf⟩ := h
  exact ⟨fun c => f c.1, fun G p => hf G p⟩

lemma Det.mono {r s : ℕ} {φ : Fam k} (h : Det r φ) (hrs : r ≤ s) : Det s φ := by
  induction s, hrs using Nat.le_induction with
  | base => exact h
  | succ s _ ih => exact ih.succ

lemma det_atp (F : AtomicType k → ℕ) : Det 0 (k := k) (fun G p => F (atp G p)) :=
  ⟨F, fun _ _ => rfl⟩

lemma det_const (a : ℕ) : Det 0 (k := k) (fun _ _ => a) := ⟨fun _ => a, fun _ _ => rfl⟩

lemma Det.mul {r : ℕ} {φ ψ : Fam k} (h1 : Det r φ) (h2 : Det r ψ) :
    Det r (fun G p => φ G p * ψ G p) := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  exact ⟨fun c => f c * g c, fun G p => by simp only [hf, hg]⟩

lemma DetAny.mul {φ ψ : Fam k} (h1 : DetAny φ) (h2 : DetAny ψ) :
    DetAny (fun G p => φ G p * ψ G p) := by
  obtain ⟨r, h1⟩ := h1
  obtain ⟨s, h2⟩ := h2
  exact ⟨max r s, (h1.mono (le_max_left _ _)).mul (h2.mono (le_max_right _ _))⟩

lemma Det.congr {r : ℕ} {φ ψ : Fam k} (h : Det r φ) (e : ∀ G p, ψ G p = φ G p) : Det r ψ := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun G p => (e G p).trans (hf G p)⟩

lemma DetAny.prod {ι : Type*} (s : Finset ι) {φ : ι → Fam k} (h : ∀ j ∈ s, DetAny (φ j)) :
    DetAny (fun G p => ∏ j ∈ s, φ j G p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact ⟨0, det_const 1⟩
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The extension `p̄ ↦ ∑_q ∏_i ψ_i(p̄[q/i])` of round-`r` determined families is determined in
round `r + 1`. -/
lemma det_ext {r : ℕ} {ψ : Fin k → Fam k} (h : ∀ i, Det r (ψ i)) :
    Det (r + 1) (fun G p => ∑ x, ∏ i, ψ i G (Function.update p i x)) := by
  choose f hf using h
  refine ⟨fun c => (c.2.map fun v => ∏ i, f i (v i)).sum, fun G p => ?_⟩
  simp only [color, Multiset.map_map, Function.comp_def]
  rw [Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun x _ => ?_
  exact Finset.prod_congr rfl fun i _ => hf i G _

/-! ### Extension-ready families

`Ext r Φ`: `Φ G p̄ x = χ(p̄) · ∏_i ψ_i(p̄[x/i])` with round-`r` determined `χ, ψ_i`. Summing over
`x` gives a family determined in round `r + 1`. -/

/-- A function of a tuple `p̄` and a vertex `x`. -/
abbrev Fam1 (k : ℕ) := (G : ColoredGraph) → (Fin k → Fin G.n) → Fin G.n → ℕ

/-- `Φ G p̄ x = χ(p̄) · ∏_i ψ_i(p̄[x/i])` for round-`r` determined `χ` and `ψ_i`. -/
def Ext (r : ℕ) (Φ : Fam1 k) : Prop :=
  ∃ (χ : Fam k) (ψ : Fin k → Fam k), Det r χ ∧ (∀ i, Det r (ψ i)) ∧
    ∀ G p x, Φ G p x = χ G p * ∏ i, ψ i G (Function.update p i x)

/-- `Ext r Φ` for some `r`. -/
def ExtAny (Φ : Fam1 k) : Prop := ∃ r, Ext r Φ

lemma Ext.mono {r s : ℕ} {Φ : Fam1 k} (h : Ext r Φ) (hrs : r ≤ s) : Ext s Φ := by
  obtain ⟨χ, ψ, h1, h2, h3⟩ := h
  exact ⟨χ, ψ, h1.mono hrs, fun i => (h2 i).mono hrs, h3⟩

lemma Ext.mul {r : ℕ} {Φ Ψ : Fam1 k} (h1 : Ext r Φ) (h2 : Ext r Ψ) :
    Ext r (fun G p x => Φ G p x * Ψ G p x) := by
  obtain ⟨χ, ψ, a1, a2, a3⟩ := h1
  obtain ⟨χ', ψ', b1, b2, b3⟩ := h2
  refine ⟨fun G p => χ G p * χ' G p, fun i G p => ψ i G p * ψ' i G p, a1.mul b1,
    fun i => (a2 i).mul (b2 i), fun G p x => ?_⟩
  simp only [a3, b3, Finset.prod_mul_distrib]
  ring

lemma ExtAny.congr {Φ Ψ : Fam1 k} (h : ExtAny Φ) (e : ∀ G p x, Ψ G p x = Φ G p x) :
    ExtAny Ψ := by
  obtain ⟨r, χ, ψ, h1, h2, h3⟩ := h
  exact ⟨r, χ, ψ, h1, h2, fun G p x => (e G p x).trans (h3 G p x)⟩

lemma ExtAny.mul {Φ Ψ : Fam1 k} (h1 : ExtAny Φ) (h2 : ExtAny Ψ) :
    ExtAny (fun G p x => Φ G p x * Ψ G p x) := by
  obtain ⟨r, h1⟩ := h1
  obtain ⟨s, h2⟩ := h2
  exact ⟨max r s, (h1.mono (le_max_left _ _)).mul (h2.mono (le_max_right _ _))⟩

lemma extAny_const (a : ℕ) : ExtAny (k := k) (fun _ _ _ => a) := by
  refine ⟨0, fun _ _ => a, fun _ _ _ => 1, det_const a, fun _ => det_const 1, ?_⟩
  intro G p x
  simp

lemma ExtAny.prod {ι : Type*} (s : Finset ι) {Φ : ι → Fam1 k} (h : ∀ j ∈ s, ExtAny (Φ j)) :
    ExtAny (fun G p x => ∏ j ∈ s, Φ j G p x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using extAny_const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma extAny_left {φ : Fam k} (h : DetAny φ) : ExtAny (fun G p (_ : Fin G.n) => φ G p) := by
  obtain ⟨r, h⟩ := h
  exact ⟨r, φ, fun _ _ _ => 1, h, fun _ => (det_const 1).mono (Nat.zero_le _),
    fun G p x => by simp⟩

lemma extAny_at {φ : Fam k} (h : DetAny φ) (i : Fin k) :
    ExtAny (fun G p x => φ G (Function.update p i x)) := by
  classical
  obtain ⟨r, h⟩ := h
  refine ⟨r, fun _ _ => 1, fun j G p => if j = i then φ G p else 1,
    (det_const 1).mono (Nat.zero_le _), fun j => ?_, fun G p x => ?_⟩
  · by_cases hj : j = i
    · simpa [hj] using h
    · simpa [hj] using (det_const 1).mono (Nat.zero_le r)
  · simp [Finset.prod_ite_eq']

lemma ExtAny.sum {Φ : Fam1 k} (h : ExtAny Φ) : DetAny (fun G p => ∑ x, Φ G p x) := by
  obtain ⟨r, χ, ψ, h1, h2, h3⟩ := h
  refine ⟨r + 1, ?_⟩
  have := (h1.succ).mul (det_ext h2)
  obtain ⟨f, hf⟩ := this
  refine ⟨f, fun G p => ?_⟩
  rw [← hf]
  simp only [h3, Finset.mul_sum]

/-! ### Equal histograms -/

lemma sum_eq_of_det {r : ℕ} {φ : Fam k} (h : Det r φ) {G H : ColoredGraph}
    (hGH : ¬ DistinguishesAfter k r G H) : ∑ p, φ G p = ∑ q, φ H q := by
  classical
  obtain ⟨f, hf⟩ := h
  simp only [hf]
  have hm : (Finset.univ : Finset (Fin k → Fin G.n)).val.map (color G r) =
      (Finset.univ : Finset (Fin k → Fin H.n)).val.map (color H r) := by
    ext c
    simp only [DistinguishesAfter, not_exists, not_not] at hGH
    have := hGH c
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Fintype.card_subtype] at this
    rw [Multiset.count_map, Multiset.count_map, ← Finset.filter_val, ← Finset.filter_val,
      ← Finset.card_def, ← Finset.card_def]
    convert this using 2 <;> ext <;> simp [eq_comm]
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum, ← Function.comp_def f,
    ← Multiset.map_map, hm, Multiset.map_map]
  rfl

end Lax119563Proofs.HomChar

end HomChar_Det

/-! ### Formerly `Lax119563Proofs.HomChar.Forest` -/

section HomChar_Forest

/-!
# Subtrees of one-vertex forests, and sums over partial assignments

For a one-vertex forest `T` (`RowSpace.OneVertexForest`) we write `Up T v a` when `a` is an
ancestor of `v` (reflexively), `S T c` for the vertices below `c` (the subtree of `c`),
`ch T c` for the children of `c` and `I T c` for the bag of `c` without `c` itself. Every vertex in
the bag of `v` is an ancestor of `v`, so the subtrees of the children of `c` are pairwise disjoint
and only see each other through the bag of `c`.

`agreeOff s g` is the set of maps that agree with `g` outside `s`. Sums over such sets split along
a vertex (`sum_agreeOff_insert`) and factor over disjoint blocks (`sum_agreeOff_biUnion`).
-/

namespace Lax119563Proofs.HomChar

open Lax119563Proofs.RowSpace Relation

section Forest

variable {n k : ℕ} {Γ : SimpleGraph (Fin n)} (T : OneVertexForest Γ k)

/-- `a` is an ancestor of `v` (or `v` itself). -/
def Up (v a : Fin n) : Prop := ReflTransGen (fun x y => T.parent x = some y) v a

/-- The bag of `v` without `v`. -/
def I (v : Fin n) : Finset (Fin n) := (T.bag v).erase v

/-- The vertices below `c` (including `c`). -/
noncomputable def S (c : Fin n) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun v => Up T v c

/-- The children of `c`. -/
noncomputable def ch (c : Fin n) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun v => T.parent v = some c

/-- The roots. -/
noncomputable def roots : Finset (Fin n) := by
  classical exact Finset.univ.filter fun v => T.parent v = none

variable {T}

@[simp] lemma mem_S {c v : Fin n} : v ∈ S T c ↔ Up T v c := by
  classical simp [S]

@[simp] lemma mem_ch {c v : Fin n} : v ∈ ch T c ↔ T.parent v = some c := by
  classical simp [ch]

@[simp] lemma mem_roots {v : Fin n} : v ∈ roots T ↔ T.parent v = none := by
  classical simp [roots]

lemma mem_I {v b : Fin n} : b ∈ I T v ↔ b ≠ v ∧ b ∈ T.bag v := Finset.mem_erase

lemma up_refl (v : Fin n) : Up T v v := ReflTransGen.refl

lemma up_single {v c : Fin n} (h : T.parent v = some c) : Up T v c := ReflTransGen.single h

lemma Up.trans {a b c : Fin n} (h1 : Up T a b) (h2 : Up T b c) : Up T a c :=
  ReflTransGen.trans h1 h2

lemma up_head {v c a : Fin n} (h : T.parent v = some c) (h2 : Up T c a) : Up T v a :=
  ReflTransGen.head h h2

lemma Up.depth_le {v a : Fin n} (h : Up T v a) : T.depth a ≤ T.depth v := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => exact (T.depth_lt _ _ h2).le.trans ih

lemma Up.ne_parent {v a : Fin n} (h : Up T v a) (hne : v ≠ a) :
    ∃ c, T.parent v = some c ∧ Up T c a := by
  rcases ReflTransGen.cases_head h with h | h
  · exact absurd h hne
  · exact h

lemma Up.last {v a : Fin n} (h : Up T v a) (hne : v ≠ a) :
    ∃ d, Up T v d ∧ T.parent d = some a := by
  rcases ReflTransGen.cases_tail h with h | h
  · exact absurd h.symm hne
  · exact h

lemma Up.total {u a b : Fin n} (ha : Up T u a) (hb : Up T u b) : Up T a b ∨ Up T b a :=
  ReflTransGen.total_of_right_unique (fun _ _ _ h1 h2 => Option.some_injective _ (h1.symm.trans h2))
    ha hb

lemma Up.eq_of_root {ρ a : Fin n} (h : Up T ρ a) (hρ : T.parent ρ = none) : ρ = a := by
  rcases ReflTransGen.cases_head h with h | ⟨c, hc, _⟩
  · exact h
  · rw [hρ] at hc; cases hc

lemma I_eq_empty_of_root {ρ : Fin n} (hρ : T.parent ρ = none) : I T ρ = ∅ := T.bag_root ρ hρ

lemma I_subset_parent {v c : Fin n} (h : T.parent v = some c) : I T v ⊆ T.bag c :=
  T.bag_sub v c h

lemma up_of_mem_bag {v a : Fin n} (ha : a ∈ T.bag v) : Up T v a := by
  induction hd : T.depth v using Nat.strong_induction_on generalizing v with
  | _ m ih =>
    by_cases hav : a = v
    · subst hav; exact up_refl _
    have haI : a ∈ I T v := mem_I.2 ⟨hav, ha⟩
    cases hp : T.parent v with
    | none => simp [I_eq_empty_of_root hp] at haI
    | some c =>
      exact up_head hp (ih _ (hd ▸ T.depth_lt _ _ hp) (I_subset_parent hp haI) rfl)

lemma exists_root (v : Fin n) : ∃ ρ, T.parent ρ = none ∧ Up T v ρ := by
  induction hd : T.depth v using Nat.strong_induction_on generalizing v with
  | _ m ih =>
    cases hp : T.parent v with
    | none => exact ⟨v, hp, up_refl _⟩
    | some c =>
      obtain ⟨ρ, h1, h2⟩ := ih _ (hd ▸ T.depth_lt _ _ hp) c rfl
      exact ⟨ρ, h1, up_head hp h2⟩

/-- A vertex in the bag of a vertex below `d` that is not itself below `d` is in `I d`. -/
lemma mem_I_of_up {u d a : Fin n} (hud : Up T u d) (ha : a ∈ T.bag u) (had : ¬ Up T a d) :
    a ∈ I T d := by
  induction hud using ReflTransGen.head_induction_on generalizing a with
  | refl =>
    refine mem_I.2 ⟨fun h => had (h ▸ up_refl _), ha⟩
  | head h hrest ih =>
    rename_i u u'
    have hau : a ≠ u := fun e => had (e ▸ up_head h hrest)
    exact ih (I_subset_parent h (mem_I.2 ⟨hau, ha⟩)) had

lemma S_eq_insert (c : Fin n) : S T c = insert c ((ch T c).biUnion (S T)) := by
  classical
  ext v
  simp only [mem_S, Finset.mem_insert, Finset.mem_biUnion, mem_ch]
  constructor
  · intro h
    by_cases hvc : v = c
    · exact Or.inl hvc
    · obtain ⟨d, h1, h2⟩ := h.last hvc
      exact Or.inr ⟨d, h2, h1⟩
  · rintro (rfl | ⟨d, h1, h2⟩)
    · exact up_refl _
    · exact h2.trans (up_single h1)

lemma not_up_child {c d : Fin n} (hd : T.parent d = some c) : ¬ Up T c d := fun h => by
  have := h.depth_le
  have := T.depth_lt _ _ hd
  omega

lemma not_mem_S_child {c d : Fin n} (hd : d ∈ ch T c) : c ∉ S T d := by
  rw [mem_S]; exact not_up_child (mem_ch.1 hd)

lemma S_child_subset {c d : Fin n} (hd : d ∈ ch T c) : S T d ⊆ S T c := fun v hv => by
  rw [mem_S] at hv ⊢; exact hv.trans (up_single (mem_ch.1 hd))

lemma disjoint_S_children {c d d' : Fin n} (hd : d ∈ ch T c) (hd' : d' ∈ ch T c) (hne : d ≠ d') :
    Disjoint (S T d) (S T d') := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  rw [mem_S] at hu hu'
  rw [mem_ch] at hd hd'
  have key : ∀ {e e' : Fin n}, T.parent e = some c → T.parent e' = some c → e ≠ e' →
      ¬ Up T e e' := by
    intro e e' he he' hne h
    obtain ⟨f, hf, hfe⟩ := h.ne_parent hne
    rw [he, Option.some_inj] at hf
    subst hf
    exact not_up_child he' hfe
  rcases hu.total hu' with h | h
  · exact key hd hd' hne h
  · exact key hd' hd (Ne.symm hne) h

lemma disjoint_bag_S_child {c d : Fin n} (hd : d ∈ ch T c) : Disjoint (T.bag c) (S T d) := by
  rw [Finset.disjoint_left]
  intro a ha haS
  rw [mem_S] at haS
  exact not_up_child (mem_ch.1 hd) ((up_of_mem_bag ha).trans haS)

lemma bag_subset_of_child {c d u : Fin n} (hd : d ∈ ch T c) (hu : u ∈ S T d) :
    T.bag u ⊆ S T d ∪ T.bag c := by
  intro a ha
  rw [Finset.mem_union, mem_S]
  by_cases had : Up T a d
  · exact Or.inl had
  · exact Or.inr (I_subset_parent (mem_ch.1 hd) (mem_I_of_up (mem_S.1 hu) ha had))

lemma univ_eq_roots : (Finset.univ : Finset (Fin n)) = (roots T).biUnion (S T) := by
  classical
  ext v
  simp only [Finset.mem_univ, Finset.mem_biUnion, mem_roots, mem_S, true_iff]
  exact exists_root v

lemma disjoint_S_roots {ρ ρ' : Fin n} (h : ρ ∈ roots T) (h' : ρ' ∈ roots T) (hne : ρ ≠ ρ') :
    Disjoint (S T ρ) (S T ρ') := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  rw [mem_S] at hu hu'
  rw [mem_roots] at h h'
  rcases hu.total hu' with e | e
  · exact hne (e.eq_of_root h)
  · exact hne (e.eq_of_root h').symm

lemma bag_subset_of_root {ρ u : Fin n} (hρ : ρ ∈ roots T) (hu : u ∈ S T ρ) : T.bag u ⊆ S T ρ := by
  intro a ha
  rw [mem_S]
  by_contra h
  have := mem_I_of_up (mem_S.1 hu) ha h
  rw [I_eq_empty_of_root (mem_roots.1 hρ)] at this
  simp at this

lemma I_child_root {ρ d : Fin n} (hρ : ρ ∈ roots T) (hd : d ∈ ch T ρ) {b : Fin n}
    (hb : b ∈ I T d) : b = ρ := by
  have hb' := I_subset_parent (mem_ch.1 hd) hb
  by_contra hne
  have : b ∈ I T ρ := mem_I.2 ⟨hne, hb'⟩
  rw [I_eq_empty_of_root (mem_roots.1 hρ)] at this
  simp at this

lemma card_I (v : Fin n) : (I T v).card ≤ k := by
  have := T.card_bag v
  have := Finset.card_erase_of_mem (T.mem_bag v)
  unfold I; omega

end Forest

/-! ### Sums over maps agreeing with a given map outside a set -/

section Sums

variable {V M : Type*} [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M]

/-- The maps that agree with `g` outside `s`. -/
noncomputable def agreeOff (s : Finset V) (g : V → M) : Finset (V → M) := by
  classical exact Finset.univ.filter fun h => ∀ v, v ∉ s → h v = g v

@[simp] lemma mem_agreeOff {s : Finset V} {g h : V → M} :
    h ∈ agreeOff s g ↔ ∀ v, v ∉ s → h v = g v := by
  classical simp [agreeOff]

lemma agreeOff_univ (g : V → M) : agreeOff Finset.univ g = Finset.univ := by
  ext h; simp

lemma sum_agreeOff_insert {c : V} {U : Finset V} (hc : c ∉ U) (g : V → M) (f : (V → M) → ℕ) :
    ∑ h ∈ agreeOff (insert c U) g, f h = ∑ x, ∑ h ∈ agreeOff U (Function.update g c x), f h := by
  rw [← Finset.sum_fiberwise (agreeOff (insert c U) g) (fun h => h c) f]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext h
  simp only [Finset.mem_filter, mem_agreeOff, Finset.mem_insert, not_or]
  constructor
  · rintro ⟨hh, rfl⟩ v hv
    by_cases hvc : v = c
    · subst hvc; simp
    · rw [Function.update_of_ne hvc]; exact hh v ⟨hvc, hv⟩
  · intro hh
    refine ⟨fun v ⟨hvc, hv⟩ => by rw [hh v hv, Function.update_of_ne hvc], ?_⟩
    rw [hh c hc, Function.update_self]

lemma sum_agreeOff_biUnion {ι : Type*} [DecidableEq ι] (A : Finset ι) (B D : ι → Finset V)
    (P : ι → (V → M) → ℕ) (g : V → M)
    (hB : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (B i) (B j))
    (hD : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (D i) (B j))
    (hP : ∀ i ∈ A, ∀ h h' : V → M, (∀ v ∈ D i, h v = h' v) → P i h = P i h') :
    ∑ h ∈ agreeOff (A.biUnion B) g, ∏ i ∈ A, P i h = ∏ i ∈ A, ∑ h ∈ agreeOff (B i) g, P i h := by
  induction A using Finset.induction_on with
  | empty =>
    simp only [Finset.biUnion_empty, Finset.prod_empty, Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.card_eq_one]
    refine ⟨g, ?_⟩
    ext h
    simp only [mem_agreeOff, Finset.notMem_empty, not_false_eq_true, forall_const,
      Finset.mem_singleton]
    exact ⟨funext, fun e v => by rw [e]⟩
  | insert a A ha ih =>
    have hB' : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (B i) (B j) := fun i hi j hj =>
      hB i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hD' : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (D i) (B j) := fun i hi j hj =>
      hD i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hP' : ∀ i ∈ A, ∀ h h' : V → M, (∀ v ∈ D i, h v = h' v) → P i h = P i h' :=
      fun i hi => hP i (Finset.mem_insert_of_mem hi)
    simp_rw [Finset.prod_insert ha]
    rw [← ih hB' hD' hP', Finset.sum_mul_sum, ← Finset.sum_product']
    set U := A.biUnion B
    have haA : ∀ j ∈ A, a ≠ j := fun j hj e => ha (e ▸ hj)
    have hdisj : ∀ v, v ∈ B a → v ∉ U := by
      intro v hv hvU
      obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.1 hvU
      exact Finset.disjoint_left.1 (hB a (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (haA j hj)) hv hvj
    have hDa : ∀ v, v ∈ D a → v ∉ U := by
      intro v hv hvU
      obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.1 hvU
      exact Finset.disjoint_left.1 (hD a (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (haA j hj)) hv hvj
    have hDj : ∀ j ∈ A, ∀ v, v ∈ D j → v ∉ B a := fun j hj v hv hva =>
      Finset.disjoint_left.1 (hD j (Finset.mem_insert_of_mem hj) a (Finset.mem_insert_self _ _)
        (haA j hj).symm) hv hva
    rw [Finset.biUnion_insert]
    refine Finset.sum_nbij' (fun h => ((fun v => if v ∈ B a then h v else g v),
      (fun v => if v ∈ U then h v else g v)))
      (fun p v => if v ∈ B a then p.1 v else p.2 v) ?_ ?_ ?_ ?_ ?_
    · intro h _
      simp only [Finset.mem_product, mem_agreeOff]
      exact ⟨fun v hv => by simp [hv], fun v hv => by simp [hv]⟩
    · rintro ⟨h1, h2⟩ hh
      simp only [Finset.mem_product, mem_agreeOff, Finset.mem_union, not_or] at hh ⊢
      intro v ⟨hva, hvU⟩
      simp [hva, hh.2 v hvU]
    · intro h hh
      simp only [mem_agreeOff, Finset.mem_union, not_or] at hh
      funext v
      by_cases hva : v ∈ B a
      · simp [hva]
      · by_cases hvU : v ∈ U
        · simp [hva, hvU]
        · simp [hva, hvU, hh v ⟨hva, hvU⟩]
    · rintro ⟨h1, h2⟩ hh
      simp only [Finset.mem_product, mem_agreeOff] at hh
      refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
      · by_cases hva : v ∈ B a
        · simp [hva]
        · simp [hva, hh.1 v hva]
      · by_cases hvU : v ∈ U
        · have hva : v ∉ B a := fun h => hdisj v h hvU
          simp [hvU, hva]
        · simp [hvU, hh.2 v hvU]
    · intro h hh
      simp only [mem_agreeOff, Finset.mem_union, not_or] at hh
      congr 1
      · refine hP a (Finset.mem_insert_self _ _) _ _ fun v hv => ?_
        by_cases hva : v ∈ B a
        · simp [hva]
        · simp [hva, hh v ⟨hva, hDa v hv⟩]
      · refine Finset.prod_congr rfl fun j hj => hP' j hj _ _ fun v hv => ?_
        by_cases hvU : v ∈ U
        · simp [hvU]
        · simp [hvU, hh v ⟨hDj j hj v hv, hvU⟩]

end Sums

end Lax119563Proofs.HomChar

end HomChar_Forest

/-! ### Formerly `Lax119563Proofs.HomChar.Tensor` -/

section HomChar_Tensor

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

end HomChar_Tensor

/-! ### Formerly `Lax119563Proofs.Stabilization.Defs` -/

section Stabilization_Defs

/-!
# Stabilization bound: shared definitions

Weak chains (the `A`-sequences of Döring–Neuen, without strictness), and invariant / simple
subspaces for a `⋆`-subalgebra of `End(E)`.
-/

open Module

namespace Lax119563Proofs.Stabilization

section Chains

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-- A weak chain of length `ℓ` in a star algebra `A`: `V 0 = ℂ 1`, every `V i` (`i ≤ ℓ`) is
closed under `star`, and `V i * V i ≤ V (i + 1)` for `i < ℓ`. -/
structure IsChain (V : ℕ → Submodule ℂ A) (ℓ : ℕ) : Prop where
  zero : V 0 = ℂ ∙ (1 : A)
  star_mem : ∀ i ≤ ℓ, ∀ x ∈ V i, star x ∈ V i
  mul_le : ∀ i < ℓ, V i * V i ≤ V (i + 1)

/-- The number of strict steps `V i ≠ V (i + 1)`, `i < ℓ`. -/
noncomputable def strictSteps (V : ℕ → Submodule ℂ A) (ℓ : ℕ) : ℕ := by
  classical
  exact ((Finset.range ℓ).filter fun i => V i ≠ V (i + 1)).card

variable (A) in
/-- Every weak chain in `A` has fewer than `N` strict steps. -/
def ChainBound (N : ℕ) : Prop :=
  ∀ (V : ℕ → Submodule ℂ A) (ℓ : ℕ), IsChain V ℓ → strictSteps V ℓ + 1 ≤ N

end Chains

section Structure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- `W` is invariant under every element of `S`. -/
def Invariant (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) (W : Submodule ℂ E) : Prop :=
  ∀ a ∈ S, ∀ x ∈ W, a x ∈ W

/-- `W` is a nonzero `S`-invariant subspace without nontrivial `S`-invariant subspaces. -/
def IsSimpleFor (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) (W : Submodule ℂ E) : Prop :=
  W ≠ ⊥ ∧ Invariant S W ∧ ∀ U : Submodule ℂ E, U ≤ W → Invariant S U → U = ⊥ ∨ U = W

end Structure

end Lax119563Proofs.Stabilization

end Stabilization_Defs

/-! ### Formerly `Lax119563Proofs.Stabilization.Chains` -/

section Stabilization_Chains

/-!
# Generic facts about weak chains

Counting strict steps, monotonicity of chains, powers of star-closed subspaces and the
generated algebra `alg V = ⨆ k, V ^ k` (`V ^ finrank A = alg V`), Observation 5.2 of
Döring–Neuen (`V s ^ 2 ^ j ≤ V (s + j)`), and transfer of `ChainBound` along injective
`⋆`-algebra homomorphisms and into star subalgebras.
-/

open Module

set_option linter.unusedSectionVars false

namespace Lax119563Proofs.Stabilization

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-! ### Counting strict steps -/

/-- `1` if `i` is a strict step of `V`, else `0`. -/
noncomputable def stepInd (V : ℕ → Submodule ℂ A) (i : ℕ) : ℕ := by
  classical
  exact if V i = V (i + 1) then 0 else 1

theorem stepInd_le_one (V : ℕ → Submodule ℂ A) (i : ℕ) : stepInd V i ≤ 1 := by
  unfold stepInd; split_ifs <;> simp

theorem stepInd_eq_zero {V : ℕ → Submodule ℂ A} {i : ℕ} (h : V i = V (i + 1)) :
    stepInd V i = 0 := by
  unfold stepInd; simp [h]

theorem stepInd_eq_one {V : ℕ → Submodule ℂ A} {i : ℕ} (h : V i ≠ V (i + 1)) :
    stepInd V i = 1 := by
  unfold stepInd; simp [h]

theorem strictSteps_eq_sum (V : ℕ → Submodule ℂ A) (ℓ : ℕ) :
    strictSteps V ℓ = ∑ i ∈ Finset.range ℓ, stepInd V i := by
  classical
  unfold strictSteps
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : V i = V (i + 1)
  · rw [stepInd_eq_zero h]; simp [h]
  · rw [stepInd_eq_one h]; simp [h]

theorem strictSteps_add (V : ℕ → Submodule ℂ A) (a b : ℕ) :
    strictSteps V (a + b) = strictSteps V a + ∑ i ∈ Finset.range b, stepInd V (a + i) := by
  rw [strictSteps_eq_sum, strictSteps_eq_sum, Finset.sum_range_add]

theorem sum_stepInd_le (V : ℕ → Submodule ℂ A) (a b : ℕ) :
    ∑ i ∈ Finset.range b, stepInd V (a + i) ≤ b := by
  calc ∑ i ∈ Finset.range b, stepInd V (a + i) ≤ ∑ _i ∈ Finset.range b, 1 :=
        Finset.sum_le_sum fun i _ => stepInd_le_one V _
    _ = b := by simp

theorem strictSteps_mono (V : ℕ → Submodule ℂ A) {a b : ℕ} (h : a ≤ b) :
    strictSteps V a ≤ strictSteps V b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [strictSteps_add]; omega

theorem strictSteps_le_add_sub (V : ℕ → Submodule ℂ A) {a b : ℕ} (h : a ≤ b) :
    strictSteps V b ≤ strictSteps V a + (b - a) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [strictSteps_add]
  have := sum_stepInd_le V a c
  omega

theorem strictSteps_le_add_sub' (V : ℕ → Submodule ℂ A) (a b : ℕ) :
    strictSteps V b ≤ strictSteps V a + (b - a) := by
  rcases le_total a b with h | h
  · exact strictSteps_le_add_sub V h
  · have := strictSteps_mono V h; omega

theorem strictSteps_congr {B : Type*} [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    {V : ℕ → Submodule ℂ A} {V' : ℕ → Submodule ℂ B} {ℓ : ℕ}
    (h : ∀ i < ℓ, (V i = V (i + 1) ↔ V' i = V' (i + 1))) :
    strictSteps V ℓ = strictSteps V' ℓ := by
  rw [strictSteps_eq_sum, strictSteps_eq_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi := Finset.mem_range.mp hi
  by_cases hV : V i = V (i + 1)
  · rw [stepInd_eq_zero hV, stepInd_eq_zero ((h i hi).mp hV)]
  · rw [stepInd_eq_one hV, stepInd_eq_one fun h' => hV ((h i hi).mpr h')]

/-! ### Basic chain facts -/

namespace IsChain

variable {V : ℕ → Submodule ℂ A} {ℓ : ℕ}

theorem one_mem (hV : IsChain V ℓ) : ∀ i ≤ ℓ, (1 : A) ∈ V i := by
  intro i
  induction i with
  | zero => intro _; rw [hV.zero]; exact Submodule.mem_span_singleton_self 1
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have := hV.mul_le i (by omega) (Submodule.mul_mem_mul h1 h1)
    simpa using this

theorem le_succ (hV : IsChain V ℓ) {i : ℕ} (hi : i < ℓ) : V i ≤ V (i + 1) := by
  intro x hx
  have := hV.mul_le i hi (Submodule.mul_mem_mul hx (hV.one_mem i hi.le))
  simpa using this

theorem mono (hV : IsChain V ℓ) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ ℓ) : V i ≤ V j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hV.le_succ (by omega))

/-- **Observation 5.2.** -/
theorem pow_two_pow_le (hV : IsChain V ℓ) {s j : ℕ} (h : s + j ≤ ℓ) :
    V s ^ (2 ^ j) ≤ V (s + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, sq, ← add_assoc]
    exact (mul_le_mul' (ih (by omega)) (ih (by omega))).trans
      (hV.mul_le _ (by omega))

/-- If the chain reaches `⊤` at `t`, there are at most `t - s` strict steps after `s`. -/
theorem strictSteps_le_of_top (hV : IsChain V ℓ) {s t : ℕ} (ht : t ≤ ℓ → V t = ⊤) :
    strictSteps V ℓ ≤ strictSteps V s + (t - s) := by
  rcases le_or_gt ℓ t with h | h
  · have := strictSteps_le_add_sub' V s ℓ; omega
  · have htop := ht h.le
    have key : strictSteps V ℓ = strictSteps V t := by
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h.le
      rw [strictSteps_add]
      suffices ∑ i ∈ Finset.range c, stepInd V (t + i) = 0 by omega
      refine Finset.sum_eq_zero fun i hi => stepInd_eq_zero ?_
      have hi := Finset.mem_range.mp hi
      have h1 : V t ≤ V (t + i) := hV.mono (by omega) (by omega)
      have h2 : V t ≤ V (t + i + 1) := hV.mono (by omega) (by omega)
      rw [htop] at h1 h2
      rw [top_le_iff.mp h1, top_le_iff.mp h2]
    have := strictSteps_le_add_sub' V s t
    omega

end IsChain

/-! ### Powers and the generated algebra -/

/-- `V` is closed under `star`. -/
def StarClosed (V : Submodule ℂ A) : Prop := ∀ x ∈ V, star x ∈ V

theorem StarClosed.pow {V : Submodule ℂ A} (hV : StarClosed V) : ∀ k, StarClosed (V ^ k) := by
  intro k
  induction k with
  | zero =>
    intro x hx
    rw [pow_zero, Submodule.mem_one] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨star c, by rw [algebraMap_star_comm]⟩
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    rw [pow_succ']
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [star_mul]; exact Submodule.mul_mem_mul (hV b hb) (ih a ha)
    · rw [star_add]; exact add_mem ha hb

theorem one_le_of_mem {V : Submodule ℂ A} (h1 : (1 : A) ∈ V) : (1 : Submodule ℂ A) ≤ V :=
  Submodule.one_le.mpr h1

theorem pow_le_pow_of_one_mem {V : Submodule ℂ A} (h1 : (1 : A) ∈ V) {a b : ℕ} (h : a ≤ b) :
    V ^ a ≤ V ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  calc V ^ a = V ^ a * 1 := (mul_one _).symm
    _ ≤ V ^ a * V ^ c := mul_le_mul' le_rfl (one_le_pow_of_one_le' (one_le_of_mem h1) c)

theorem one_mem_pow {V : Submodule ℂ A} (h1 : (1 : A) ∈ V) (k : ℕ) : (1 : A) ∈ V ^ k := by
  have := pow_le_pow_of_one_mem h1 (Nat.zero_le k)
  exact this (by rw [pow_zero]; exact Submodule.one_le.mp le_rfl)

/-- Once two consecutive powers agree, all later powers agree. -/
theorem pow_stable {V : Submodule ℂ A} {a : ℕ} (h : V ^ a = V ^ (a + 1)) :
    ∀ m, a ≤ m → V ^ m = V ^ a := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ih => rw [pow_succ, ih, ← pow_succ, ← h]

/-- The (unital) algebra generated by `V`, as a subspace. -/
def alg (V : Submodule ℂ A) : Submodule ℂ A := ⨆ k, V ^ k

theorem pow_le_alg (V : Submodule ℂ A) (k : ℕ) : V ^ k ≤ alg V :=
  le_iSup (fun k => V ^ k) k

theorem le_alg (V : Submodule ℂ A) : V ≤ alg V := by
  simpa using pow_le_alg V 1

theorem alg_mono {V V' : Submodule ℂ A} (h : V ≤ V') : alg V ≤ alg V' :=
  iSup_mono fun k => pow_le_pow_left' h k

theorem alg_eq_of_stable {V : Submodule ℂ A} (h1 : (1 : A) ∈ V) {a : ℕ}
    (h : V ^ a = V ^ (a + 1)) : alg V = V ^ a := by
  refine le_antisymm (iSup_le fun k => ?_) (pow_le_alg V a)
  calc V ^ k ≤ V ^ (max k a) := pow_le_pow_of_one_mem h1 (le_max_left k a)
    _ = V ^ a := pow_stable h _ (le_max_right k a)

section FinDim

variable [FiniteDimensional ℂ A]

theorem exists_stable_or_le (V : Submodule ℂ A) (h1 : (1 : A) ∈ V) (k : ℕ) :
    (∃ j ≤ k, V ^ j = V ^ (j + 1)) ∨ k ≤ finrank ℂ ↥(V ^ k) := by
  induction k with
  | zero => right; exact Nat.zero_le _
  | succ k ih =>
    by_cases hk : V ^ k = V ^ (k + 1)
    · exact Or.inl ⟨k, by omega, hk⟩
    · rcases ih with ⟨j, hj, hj'⟩ | ih
      · exact Or.inl ⟨j, by omega, hj'⟩
      · right
        have hlt : V ^ k < V ^ (k + 1) :=
          lt_of_le_of_ne (pow_le_pow_of_one_mem h1 (Nat.le_succ k)) hk
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega

/-- **Generation lemma.** `V ^ m = alg V` as soon as `m ≥ finrank A`. -/
theorem pow_eq_alg (V : Submodule ℂ A) (h1 : (1 : A) ∈ V) {m : ℕ} (hm : finrank ℂ A ≤ m) :
    V ^ m = alg V := by
  rcases exists_stable_or_le V h1 m with ⟨j, hj, hj'⟩ | h
  · rw [alg_eq_of_stable h1 hj', pow_stable hj' m hj]
  · have htop : V ^ m = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (hm.trans h))
    rw [htop]
    exact (top_le_iff.mp (htop ▸ pow_le_alg V m)).symm

theorem alg_mul_le (V : Submodule ℂ A) (h1 : (1 : A) ∈ V) : alg V * alg V ≤ alg V := by
  have h := pow_eq_alg V h1 (le_refl (finrank ℂ A))
  calc alg V * alg V = V ^ (finrank ℂ A + finrank ℂ A) := by rw [pow_add, h]
    _ = alg V := pow_eq_alg V h1 (by omega)
    _ ≤ alg V := le_rfl

theorem one_mem_alg (V : Submodule ℂ A) (h1 : (1 : A) ∈ V) : (1 : A) ∈ alg V :=
  le_alg V h1

theorem StarClosed.alg {V : Submodule ℂ A} (hV : StarClosed V) (h1 : (1 : A) ∈ V) :
    StarClosed (alg V) := by
  rw [← pow_eq_alg V h1 le_rfl]; exact hV.pow _

/-- The star subalgebra generated by a star-closed `V ∋ 1`; its carrier is `alg V`. -/
def algStar (V : Submodule ℂ A) (h1 : (1 : A) ∈ V) (hV : StarClosed V) :
    StarSubalgebra ℂ A where
  carrier := alg V
  mul_mem' {a b} ha hb := alg_mul_le V h1 (Submodule.mul_mem_mul ha hb)
  add_mem' := add_mem
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]; exact Submodule.smul_mem _ c (one_mem_alg V h1)
  star_mem' {a} ha := hV.alg h1 a ha

end FinDim

/-! ### Transfer of chain bounds -/

section Transfer

variable {B : Type*} [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

theorem ChainBound.mono {N M : ℕ} (h : ChainBound A N) (hNM : N ≤ M) : ChainBound A M :=
  fun V ℓ hV => (h V ℓ hV).trans hNM

/-- The image of a subspace under a `⋆`-algebra homomorphism. -/
def mapS (f : A →⋆ₐ[ℂ] B) (V : Submodule ℂ A) : Submodule ℂ B :=
  V.map f.toAlgHom.toLinearMap

theorem IsChain.map (f : A →⋆ₐ[ℂ] B) {V : ℕ → Submodule ℂ A} {ℓ : ℕ} (hV : IsChain V ℓ) :
    IsChain (fun i => mapS f (V i)) ℓ where
  zero := by
    simp only [mapS]
    rw [hV.zero, Submodule.map_span, Set.image_singleton]
    simp
  star_mem i hi y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨star x, hV.star_mem i hi x hx, map_star f x⟩
  mul_le i hi := by
    simp only [mapS]
    rw [← Submodule.map_mul]
    exact Submodule.map_mono (hV.mul_le i hi)

/-- `ChainBound` pulls back along injective unital `⋆`-algebra homomorphisms. -/
theorem ChainBound.of_injective (f : A →⋆ₐ[ℂ] B) (hf : Function.Injective f) {N : ℕ}
    (h : ChainBound B N) : ChainBound A N := by
  intro V ℓ hV
  have := h _ ℓ (hV.map f)
  rwa [strictSteps_congr (V := fun i => mapS f (V i)) (V' := V) fun i _ =>
    (Submodule.map_injective_of_injective (f := f.toAlgHom.toLinearMap) hf).eq_iff] at this

/-- A chain inside a star subalgebra `S` is bounded by any chain bound of `S`. -/
theorem IsChain.strictSteps_add_one_le_of_le (S : StarSubalgebra ℂ A) {N : ℕ}
    (hS : ChainBound S N) {V : ℕ → Submodule ℂ A} {ℓ : ℕ} (hV : IsChain V ℓ)
    (hle : ∀ i ≤ ℓ, ∀ x ∈ V i, x ∈ S) : strictSteps V ℓ + 1 ≤ N := by
  let V' : ℕ → Submodule ℂ S := fun i => (V i).comap S.subtype.toAlgHom.toLinearMap
  have hinj : Function.Injective (Submodule.map S.subtype.toAlgHom.toLinearMap) :=
    Submodule.map_injective_of_injective (f := S.subtype.toAlgHom.toLinearMap)
      Subtype.val_injective
  have hmap : ∀ i ≤ ℓ, mapS S.subtype (V' i) = V i := fun i hi => by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hle i hi x hx⟩, hx, rfl⟩
  have hV' : IsChain V' ℓ := by
    refine ⟨hinj ?_, fun i hi x hx => ?_, fun i hi => Submodule.mul_le.mpr fun x hx y hy => ?_⟩
    · change mapS S.subtype (V' 0) = mapS S.subtype _
      rw [hmap 0 (Nat.zero_le _), hV.zero, mapS, Submodule.map_span, Set.image_singleton]
      simp
    · show ((star x : S) : A) ∈ V i
      exact hV.star_mem i hi _ hx
    · show ((x * y : S) : A) ∈ V (i + 1)
      exact hV.mul_le i hi (Submodule.mul_mem_mul hx hy)
  have := hS V' ℓ hV'
  rwa [strictSteps_congr (V := V') (V' := V) fun i hi => ?_] at this
  constructor
  · intro h
    rw [← hmap i hi.le, ← hmap (i + 1) hi, h]
  · intro h
    simp only [V', h]

end Transfer

/-! ### Extending a chain by squares (replaces the surgery of Lemma 5.5) -/

/-- `V` up to `s`, then the squares `V s ^ 2 ^ (i - s)`. -/
def sqExt (V : ℕ → Submodule ℂ A) (s i : ℕ) : Submodule ℂ A :=
  if i ≤ s then V i else V s ^ (2 ^ (i - s))

theorem sqExt_of_le {V : ℕ → Submodule ℂ A} {s i : ℕ} (h : i ≤ s) : sqExt V s i = V i :=
  if_pos h

theorem sqExt_of_ge {V : ℕ → Submodule ℂ A} {s i : ℕ} (h : s ≤ i) :
    sqExt V s i = V s ^ (2 ^ (i - s)) := by
  unfold sqExt
  split_ifs with h'
  · obtain rfl : i = s := by omega
    simp
  · rfl

theorem pow_two_pow_ne_of_ne_alg {V : Submodule ℂ A} (h1 : (1 : A) ∈ V) {j : ℕ}
    (h : V ^ (2 ^ j) ≠ alg V) : V ^ (2 ^ j) ≠ V ^ (2 ^ (j + 1)) := by
  intro heq
  have hj := Nat.one_le_two_pow (n := j)
  have hle1 : V ^ (2 ^ j) ≤ V ^ (2 ^ j + 1) := pow_le_pow_of_one_mem h1 (by omega)
  have hle2 : V ^ (2 ^ j + 1) ≤ V ^ (2 ^ (j + 1)) :=
    pow_le_pow_of_one_mem h1 (by rw [pow_succ]; omega)
  exact h (alg_eq_of_stable h1 (le_antisymm hle1 (heq ▸ hle2))).symm

theorem IsChain.isChain_sqExt {V : ℕ → Submodule ℂ A} {ℓ s : ℕ} (hV : IsChain V ℓ) (hs : s ≤ ℓ)
    (r : ℕ) : IsChain (sqExt V s) (s + r) := by
  refine ⟨?_, fun i hi x hx => ?_, fun i hi => ?_⟩
  · rw [sqExt_of_le (Nat.zero_le _), hV.zero]
  · rcases le_total i s with h | h
    · rw [sqExt_of_le h] at hx ⊢; exact hV.star_mem i (by omega) x hx
    · rw [sqExt_of_ge h] at hx ⊢
      exact (StarClosed.pow (hV.star_mem s hs) _) x hx
  · rcases lt_or_ge i s with h | h
    · rw [sqExt_of_le h.le, sqExt_of_le h]; exact hV.mul_le i (by omega)
    · rw [sqExt_of_ge h, sqExt_of_ge (by omega : s ≤ i + 1), ← pow_add]
      apply le_of_eq; congr 1
      rw [show i + 1 - s = (i - s) + 1 by omega, pow_succ]; ring

theorem IsChain.strictSteps_sqExt {V : ℕ → Submodule ℂ A} {ℓ s r : ℕ} (hV : IsChain V ℓ)
    (hs : s ≤ ℓ) (hr : ∀ j < r, V s ^ (2 ^ j) ≠ alg (V s)) :
    strictSteps (sqExt V s) (s + r) = strictSteps V s + r := by
  rw [strictSteps_add, strictSteps_congr (V := sqExt V s) (V' := V) fun i hi => by
    rw [sqExt_of_le hi.le, sqExt_of_le hi]]
  congr 1
  calc ∑ i ∈ Finset.range r, stepInd (sqExt V s) (s + i) = ∑ _i ∈ Finset.range r, 1 := by
        refine Finset.sum_congr rfl fun i hi => stepInd_eq_one ?_
        rw [sqExt_of_ge (by omega), sqExt_of_ge (by omega),
          show s + i - s = i by omega, show s + i + 1 - s = i + 1 by omega]
        exact pow_two_pow_ne_of_ne_alg (hV.one_mem s hs) (hr i (Finset.mem_range.mp hi))
    _ = r := by simp

end Lax119563Proofs.Stabilization

end Stabilization_Chains

/-! ### Formerly `Lax119563Proofs.Stabilization.Corner` -/

section Stabilization_Corner

/-!
# The corner lemma (Döring–Neuen, Lemma 5.12), basis-free

`X` a star-closed subspace of `End E` with `1 ∈ X` generating `End E`, `W ≠ ⊥` a subspace with
`dim W < n` such that every operator with range in `W` vanishing on `Wᗮ` lies in `X`. Then
`X ^ (2 (n - dim W)) = ⊤`.

Proof: the orbit spaces `H t = span {a u | a ∈ X ^ t, u ∈ W}` grow strictly until they are
`⊤`, so `dim H (k - 1) ≥ n - 1` and `H k = ⊤` for `k = n - dim W`. Rank-one maps
`rk v w = ⟪w, ·⟫ v` satisfy `rk (a u) (b u') = a * rk u u' * star b`, hence
`rk v w ∈ X ^ (p + 1 + q)` for `v ∈ H p`, `w ∈ H q`. Every operator is a sum of rank-one maps;
a rank-one map with one argument in `H (k - 1)` is in `X ^ (2 k)`, and the remaining direction
`Hᗮ = ℂ z` is handled via `rk z z = 1 - (1 - rk z z)`.
-/

open Module

set_option linter.unusedSectionVars false

noncomputable section

namespace Lax119563Proofs.Stabilization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ### Rank-one maps -/

/-- The rank-one map `x ↦ ⟪w, x⟫ v`. -/
def rk (v w : E) : E →ₗ[ℂ] E where
  toFun x := inner ℂ w x • v
  map_add' x y := by simp [add_smul]
  map_smul' c x := by simp [mul_smul]

@[simp] theorem rk_apply (v w x : E) : rk v w x = inner ℂ w x • v := rfl

theorem mul_rk (a : E →ₗ[ℂ] E) (v w : E) : a * rk v w = rk (a v) w := by
  ext x; simp

theorem rk_mul_star (v w : E) (b : E →ₗ[ℂ] E) : rk v w * star b = rk v (b w) := by
  ext x
  simp [LinearMap.star_eq_adjoint, LinearMap.adjoint_inner_right]

theorem rk_add_left (v v' w : E) : rk (v + v') w = rk v w + rk v' w := by
  ext x; simp [smul_add]

theorem rk_smul_left (c : ℂ) (v w : E) : rk (c • v) w = c • rk v w := by
  ext x; simp [smul_smul, mul_comm]

theorem rk_add_right (v w w' : E) : rk v (w + w') = rk v w + rk v w' := by
  ext x; simp [add_smul]

theorem rk_smul_right (c : ℂ) (v w : E) : rk v (c • w) = (starRingEnd ℂ c) • rk v w := by
  ext x; simp [smul_smul, mul_comm]

/-- `v ↦ rk v w` as a linear map. -/
def rkLeft (w : E) : E →ₗ[ℂ] (E →ₗ[ℂ] E) where
  toFun v := rk v w
  map_add' v v' := rk_add_left v v' w
  map_smul' c v := rk_smul_left c v w

/-- `w ↦ rk v w` as a conjugate-linear map. -/
def rkRight (v : E) : E →ₗ⋆[ℂ] (E →ₗ[ℂ] E) where
  toFun w := rk v w
  map_add' w w' := rk_add_right v w w'
  map_smul' c w := rk_smul_right c v w

/-- Every operator is a sum of rank-one maps. -/
theorem eq_sum_rk (T : E →ₗ[ℂ] E) :
    T = ∑ i, rk (T (stdOrthonormalBasis ℂ E i)) (stdOrthonormalBasis ℂ E i) := by
  ext x
  rw [LinearMap.sum_apply]
  conv_lhs => rw [← (stdOrthonormalBasis ℂ E).sum_repr' x]
  simp [map_sum, map_smul]

/-! ### Orbit spaces -/

/-- `H t = span {a u | a ∈ X ^ t, u ∈ W}`. -/
def orbit (X : Submodule ℂ (E →ₗ[ℂ] E)) (W : Submodule ℂ E) (t : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ {v | ∃ a ∈ X ^ t, ∃ u ∈ W, a u = v}

variable {X : Submodule ℂ (E →ₗ[ℂ] E)} {W : Submodule ℂ E}

theorem mem_orbit_of {t : ℕ} {a : E →ₗ[ℂ] E} (ha : a ∈ X ^ t) {u : E} (hu : u ∈ W) :
    a u ∈ orbit X W t :=
  Submodule.subset_span ⟨a, ha, u, hu, rfl⟩

theorem orbit_map {p t : ℕ} {a : E →ₗ[ℂ] E} (ha : a ∈ X ^ p) {v : E} (hv : v ∈ orbit X W t) :
    a v ∈ orbit X W (p + t) := by
  have : orbit X W t ≤ (orbit X W (p + t)).comap a := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, u, hu, rfl⟩
    show a (b u) ∈ orbit X W (p + t)
    rw [← Module.End.mul_apply]
    exact mem_orbit_of ((pow_add X p t).ge (Submodule.mul_mem_mul ha hb)) hu
  exact this hv

theorem le_orbit_zero : W ≤ orbit X W 0 := by
  intro u hu
  have : (1 : E →ₗ[ℂ] E) ∈ X ^ 0 :=
    (pow_zero X).ge ⟨1, map_one (algebraMap ℂ (E →ₗ[ℂ] E))⟩
  simpa using mem_orbit_of this hu

theorem orbit_le_succ (h1 : (1 : E →ₗ[ℂ] E) ∈ X) (t : ℕ) : orbit X W t ≤ orbit X W (t + 1) := by
  intro v hv
  have := orbit_map ((pow_one X).ge h1) hv
  rw [add_comm] at this
  simpa using this

theorem orbit_invariant {t : ℕ} (hst : orbit X W t = orbit X W (t + 1)) :
    ∀ p, ∀ a ∈ X ^ p, ∀ v ∈ orbit X W t, a v ∈ orbit X W t := by
  intro p
  induction p with
  | zero =>
    intro a ha v hv
    replace ha := (pow_zero X).le ha
    rw [Submodule.mem_one] at ha
    obtain ⟨c, rfl⟩ := ha
    simpa [Algebra.algebraMap_eq_smul_one] using Submodule.smul_mem _ c hv
  | succ p ih =>
    intro a ha v hv
    replace ha := (pow_succ' X p).le ha
    refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) (fun x y hx hy => ?_)
    · rw [Module.End.mul_apply]
      have := orbit_map ((pow_one X).ge hb) (ih c hc v hv)
      rwa [add_comm, ← hst] at this
    · rw [LinearMap.add_apply]; exact add_mem hx hy

theorem le_orbit (h1 : (1 : E →ₗ[ℂ] E) ∈ X) : ∀ t, W ≤ orbit X W t
  | 0 => le_orbit_zero
  | t + 1 => (le_orbit h1 t).trans (orbit_le_succ h1 t)

theorem orbit_eq_top_of_stable (h1 : (1 : E →ₗ[ℂ] E) ∈ X) (halg : alg X = ⊤) (hW : W ≠ ⊥)
    {t : ℕ} (hst : orbit X W t = orbit X W (t + 1)) : orbit X W t = ⊤ := by
  have hall : ∀ a : E →ₗ[ℂ] E, ∀ v ∈ orbit X W t, a v ∈ orbit X W t := by
    intro a v hv
    have : a ∈ X ^ finrank ℂ (E →ₗ[ℂ] E) :=
      (pow_eq_alg X h1 le_rfl).ge (by rw [halg]; exact Submodule.mem_top)
    exact orbit_invariant hst _ a this v hv
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have huH : u ∈ orbit X W t := le_orbit h1 t hu
  have huu : inner ℂ u u ≠ 0 := inner_self_ne_zero.mpr hu0
  refine eq_top_iff.mpr fun y _ => ?_
  have := Submodule.smul_mem _ (inner ℂ u u)⁻¹ (hall (rk y u) u huH)
  rwa [rk_apply, smul_smul, inv_mul_cancel₀ huu, one_smul] at this

theorem finrank_orbit (h1 : (1 : E →ₗ[ℂ] E) ∈ X) (halg : alg X = ⊤) (hW : W ≠ ⊥) :
    ∀ t, min (finrank ℂ E) (finrank ℂ W + t) ≤ finrank ℂ (orbit X W t) := by
  intro t
  induction t with
  | zero => exact (min_le_right _ _).trans (Submodule.finrank_mono (le_orbit_zero))
  | succ t ih =>
    by_cases hst : orbit X W t = orbit X W (t + 1)
    · rw [← hst, orbit_eq_top_of_stable h1 halg hW hst, finrank_top]
      exact min_le_left _ _
    · have := Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne (orbit_le_succ h1 t) hst)
      omega

/-! ### Rank-one maps in powers of `X` -/

theorem rk_mem_of_mem_orbit (hX : StarClosed X)
    (hcorner : ∀ T : E →ₗ[ℂ] E, LinearMap.range T ≤ W → Wᗮ ≤ LinearMap.ker T → T ∈ X)
    {p q : ℕ} {v w : E} (hv : v ∈ orbit X W p) (hw : w ∈ orbit X W q) :
    rk v w ∈ X ^ (p + 1 + q) := by
  -- generators
  have hgen : ∀ a ∈ X ^ p, ∀ u ∈ W, ∀ b ∈ X ^ q, ∀ u' ∈ W, rk (a u) (b u') ∈ X ^ (p + 1 + q) := by
    intro a ha u hu b hb u' hu'
    have hc : rk u u' ∈ X := by
      refine hcorner _ ?_ ?_
      · rintro _ ⟨x, rfl⟩
        exact Submodule.smul_mem _ _ hu
      · intro x hx
        simp [LinearMap.mem_ker, Submodule.inner_right_of_mem_orthogonal hu' hx]
    rw [← mul_rk, ← rk_mul_star, ← mul_assoc]
    exact (pow_add X (p + 1) q).ge (Submodule.mul_mem_mul
      ((pow_succ X p).ge (Submodule.mul_mem_mul ha hc)) ((hX.pow q) b hb))
  -- extend in `v`
  have hleft : ∀ b ∈ X ^ q, ∀ u' ∈ W, rk v (b u') ∈ X ^ (p + 1 + q) := by
    intro b hb u' hu'
    have : orbit X W p ≤ (X ^ (p + 1 + q)).comap (rkLeft (b u')) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, ha, u, hu, rfl⟩
      exact hgen a ha u hu b hb u' hu'
    exact this hv
  have : orbit X W q ≤ (X ^ (p + 1 + q)).comap (rkRight v) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, u', hu', rfl⟩
    exact hleft b hb u' hu'
  exact this hw

/-! ### The corner lemma -/

/-- **Lemma 5.12.** -/
theorem corner_pow_eq_top (X : Submodule ℂ (E →ₗ[ℂ] E)) (h1 : (1 : E →ₗ[ℂ] E) ∈ X)
    (hX : StarClosed X) (halg : alg X = ⊤) (W : Submodule ℂ E) (hW : W ≠ ⊥)
    (hWn : finrank ℂ W < finrank ℂ E)
    (hcorner : ∀ T : E →ₗ[ℂ] E, LinearMap.range T ≤ W → Wᗮ ≤ LinearMap.ker T → T ∈ X) :
    X ^ (2 * (finrank ℂ E - finrank ℂ W)) = ⊤ := by
  set n := finrank ℂ E
  set k := n - finrank ℂ W with hk
  have hk1 : 1 ≤ k := by omega
  set H := orbit X W (k - 1) with hH
  set Y := X ^ (2 * k)
  have hHk : orbit X W k = ⊤ := by
    have := finrank_orbit h1 halg hW k
    exact Submodule.eq_top_of_finrank_eq
      (le_antisymm (Submodule.finrank_le _) (by omega))
  have hHdim : n - 1 ≤ finrank ℂ H := by
    have := finrank_orbit h1 halg hW (k - 1)
    rw [← hH] at this
    omega
  have hY1 : ∀ v ∈ H, ∀ w, rk v w ∈ Y := by
    intro v hv w
    have := rk_mem_of_mem_orbit hX hcorner hv (hHk ▸ Submodule.mem_top : w ∈ orbit X W k)
    rwa [show k - 1 + 1 + k = 2 * k by omega] at this
  have hY2 : ∀ v, ∀ w ∈ H, rk v w ∈ Y := by
    intro v w hw
    have := rk_mem_of_mem_orbit hX hcorner (hHk ▸ Submodule.mem_top : v ∈ orbit X W k) hw
    rwa [show k + 1 + (k - 1) = 2 * k by omega] at this
  have hsum : ∀ T : E →ₗ[ℂ] E, (∀ i, rk (T (stdOrthonormalBasis ℂ E i))
      (stdOrthonormalBasis ℂ E i) ∈ Y) → T ∈ Y := by
    intro T hT
    rw [eq_sum_rk T]
    exact Submodule.sum_mem _ fun i _ => hT i
  have hall : ∀ v w, rk v w ∈ Y := by
    by_cases hHtop : H = ⊤
    · intro v w; exact hY1 v (hHtop ▸ Submodule.mem_top) w
    have hperp : Hᗮ ≠ ⊥ := fun h => hHtop (Submodule.orthogonal_eq_bot_iff.mp h)
    obtain ⟨z0, hz0, hz00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
    set z : E := ((‖z0‖⁻¹ : ℝ) : ℂ) • z0
    have hzH : z ∈ Hᗮ := Submodule.smul_mem _ _ hz0
    have hzz : inner ℂ z z = 1 := by
      rw [inner_self_eq_norm_sq_to_K]
      have : ‖z‖ = 1 := by
        simp only [z]
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz00)]
      simp [this]
    have hz0' : z ≠ 0 := fun h => by simp [h] at hzz
    have hspan : Hᗮ = ℂ ∙ z := by
      refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hzH
      · rw [finrank_span_singleton hz0']
        have := Submodule.finrank_add_finrank_orthogonal H
        omega
    have hproj : ∀ v, v - inner ℂ z v • z ∈ H := by
      intro v
      rw [← Submodule.orthogonal_orthogonal H, Submodule.mem_orthogonal]
      intro u hu
      rw [hspan, Submodule.mem_span_singleton] at hu
      obtain ⟨c, rfl⟩ := hu
      rw [inner_smul_left, inner_sub_right, inner_smul_right, hzz]
      simp
    have hrkzz : rk z z ∈ Y := by
      have hQ : (1 - rk z z) ∈ Y := hsum _ fun i => hY1 _ (by
        simpa [sub_eq_add_neg] using hproj (stdOrthonormalBasis ℂ E i)) _
      have h1Y : (1 : E →ₗ[ℂ] E) ∈ Y := one_mem_pow h1 _
      simpa using sub_mem h1Y hQ
    intro v w
    have e1 : rk v w = rk (v - inner ℂ z v • z) w + inner ℂ z v • rk z w := by
      rw [← rk_smul_left, ← rk_add_left, sub_add_cancel]
    have e2 : rk z w = rk z (w - inner ℂ z w • z) + (starRingEnd ℂ (inner ℂ z w)) • rk z z := by
      rw [← rk_smul_right, ← rk_add_right, sub_add_cancel]
    rw [e1, e2]
    exact add_mem (hY1 _ (hproj v) _) (Submodule.smul_mem _ _
      (add_mem (hY2 _ _ (hproj w)) (Submodule.smul_mem _ _ hrkzz)))
  exact eq_top_iff.mpr fun T _ => hsum T fun i => hall _ _

end Lax119563Proofs.Stabilization

end

end Stabilization_Corner

/-! ### Formerly `Lax119563Proofs.Stabilization.Products` -/

section Stabilization_Products

/-!
# Chain bounds for products (Döring–Neuen, Lemmas 5.7 and 5.11)

`ChainBound A a → ChainBound B b → ChainBound (A × B) (a + b)`: for a weak chain `V` in `A × B`
let `P i = π_A (V i)`, `N i = V i ∩ ker π_A` and `T i = ℂ1 + π_B (N i)`. `P` and `T` are weak
chains; every strict step of `V` is a strict step of `P` or of `T`, or the unique step where
`(0, 1)` enters `V`. Lemma 5.11 iterates this over `Π i : Fin (m + 1), B i`.
-/

open Module

namespace Lax119563Proofs.Stabilization

/-- A monotone predicate becomes true at most once. -/
theorem sum_entry_le_one (p : ℕ → Prop) [DecidablePred p] (ℓ : ℕ)
    (hp : ∀ i < ℓ, p i → p (i + 1)) :
    ∑ i ∈ Finset.range ℓ, (if ¬ p i ∧ p (i + 1) then 1 else 0) ≤ 1 := by
  suffices h : ∀ m ≤ ℓ, (∑ i ∈ Finset.range m, (if ¬ p i ∧ p (i + 1) then 1 else 0)) +
      (if p 0 then 1 else 0) ≤ (if p m then 1 else 0) by
    have := h ℓ le_rfl
    split_ifs at this <;> omega
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h0 := ih (by omega)
    have hpm := hp m (by omega)
    by_cases h1 : p m
    · have h2 := hpm h1
      rw [if_pos h1] at h0
      rw [if_neg (fun h => h.1 h1), if_pos h2]; omega
    · rw [if_neg h1] at h0
      by_cases h2 : p (m + 1)
      · rw [if_pos ⟨h1, h2⟩, if_pos h2]; omega
      · rw [if_neg (fun h => h2 h.2), if_neg h2]; omega

theorem StarClosed.sup {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    {U W : Submodule ℂ A} (hU : StarClosed U) (hW : StarClosed W) : StarClosed (U ⊔ W) := by
  intro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  rw [star_add]
  exact Submodule.add_mem_sup (hU u hu) (hW w hw)

section Prod

variable {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

/-- **Lemma 5.7.** -/
theorem chainBound_prod {a b : ℕ} (hA : ChainBound A a) (hB : ChainBound B b) :
    ChainBound (A × B) (a + b) := by
  classical
  intro V ℓ hV
  let fst := StarAlgHom.fst ℂ A B
  let snd := StarAlgHom.snd ℂ A B
  let P : ℕ → Submodule ℂ A := fun i => mapS fst (V i)
  let N : ℕ → Submodule ℂ (A × B) := fun i => V i ⊓ LinearMap.ker fst.toAlgHom.toLinearMap
  have memN : ∀ i x, x ∈ N i ↔ x ∈ V i ∧ x.1 = 0 := fun i x => Iff.rfl
  let T : ℕ → Submodule ℂ B := fun i => 1 ⊔ mapS snd (N i)
  have hNmono : ∀ i < ℓ, N i ≤ N (i + 1) := fun i hi =>
    inf_le_inf_right _ (hV.le_succ hi)
  have hT : IsChain T ℓ := by
    refine ⟨?_, ?_, ?_⟩
    · show 1 ⊔ mapS snd (N 0) = _
      rw [Submodule.one_eq_span, ← Submodule.one_eq_span]
      refine sup_eq_left.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hx0, hx1⟩ := (memN 0 x).mp hx
      rw [hV.zero, Submodule.mem_span_singleton] at hx0
      obtain ⟨c, rfl⟩ := hx0
      rw [Submodule.mem_one]
      exact ⟨c, by simp [snd, Algebra.algebraMap_eq_smul_one]⟩
    · intro i hi
      refine StarClosed.sup ?_ ?_
      · simpa using (StarClosed.pow (V := (⊥ : Submodule ℂ B)) (fun x hx => by
          rw [Submodule.mem_bot] at hx ⊢; rw [hx, star_zero]) 0)
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨hx0, hx1⟩ := (memN i x).mp hx
        refine ⟨star x, (memN i _).mpr ⟨hV.star_mem i hi x hx0, ?_⟩, ?_⟩
        · simp [hx1]
        · simp [snd]
    · intro i hi
      have hM : mapS snd (N i) ≤ mapS snd (N (i + 1)) := Submodule.map_mono (hNmono i hi)
      have hMM : mapS snd (N i) * mapS snd (N i) ≤ mapS snd (N (i + 1)) := by
        simp only [mapS]
        rw [← Submodule.map_mul]
        refine Submodule.map_mono (Submodule.mul_le.mpr fun x hx y hy => ?_)
        obtain ⟨hx0, hx1⟩ := (memN i x).mp hx
        obtain ⟨hy0, hy1⟩ := (memN i y).mp hy
        exact (memN _ _).mpr ⟨hV.mul_le i hi (Submodule.mul_mem_mul hx0 hy0), by simp [hx1]⟩
      show (1 ⊔ mapS snd (N i)) * (1 ⊔ mapS snd (N i)) ≤ 1 ⊔ mapS snd (N (i + 1))
      rw [Submodule.mul_sup, Submodule.sup_mul, Submodule.sup_mul, one_mul, one_mul, mul_one]
      exact sup_le (sup_le le_sup_left (hM.trans le_sup_right))
        (sup_le (hM.trans le_sup_right) (hMM.trans le_sup_right))
  have hPb := hA P ℓ (hV.map fst)
  have hTb := hB T ℓ hT
  -- the step where `(0, 1)` enters
  let e : ℕ → Prop := fun i => ((0, 1) : A × B) ∈ V i
  have he := sum_entry_le_one e ℓ fun i hi h => hV.le_succ hi h
  have key : ∀ i < ℓ, stepInd V i ≤ stepInd P i + stepInd T i +
      (if ¬ e i ∧ e (i + 1) then 1 else 0) := by
    intro i hi
    by_cases hVi : V i = V (i + 1)
    · rw [stepInd_eq_zero hVi]; exact Nat.zero_le _
    by_cases hPi : P i = P (i + 1)
    · by_cases hTi : T i = T (i + 1)
      · by_cases hei : ¬ e i ∧ e (i + 1)
        · rw [if_pos hei]; have := stepInd_le_one V i; omega
        exfalso
        refine hVi (le_antisymm (hV.le_succ hi) fun x hx => ?_)
        have hx' : x.1 ∈ P (i + 1) := ⟨x, hx, rfl⟩
        rw [← hPi] at hx'
        obtain ⟨y, hy, hyx⟩ := hx'
        have hyx : y.1 = x.1 := hyx
        have hz : x - y ∈ N (i + 1) :=
          (memN _ _).mpr ⟨sub_mem hx (hV.le_succ hi hy), by simp [hyx]⟩
        have hz2 : (x - y).2 ∈ T i := by
          rw [hTi]; exact Submodule.mem_sup_right ⟨x - y, hz, rfl⟩
        obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hz2
        rw [Submodule.mem_one] at hu
        obtain ⟨c, rfl⟩ := hu
        obtain ⟨w', hw', rfl⟩ := hw
        obtain ⟨hw'0, hw'1⟩ := (memN i w').mp hw'
        have hdecomp : x - y = w' + c • ((0, 1) : A × B) := by
          ext
          · simp [hyx, hw'1]
          · have : (x - y).2 = algebraMap ℂ B c + w'.2 := huw.symm
            simp only [Prod.snd_add, Prod.smul_snd, Algebra.algebraMap_eq_smul_one] at this ⊢
            rw [this, add_comm]
        suffices hxy : x - y ∈ V i by simpa using add_mem hxy hy
        by_cases hc : c = 0
        · rw [hdecomp, hc, zero_smul, add_zero]; exact hw'0
        · have he1 : e (i + 1) := by
            have : c • ((0, 1) : A × B) ∈ V (i + 1) := by
              have := sub_mem hz.1 (hV.le_succ hi hw'0)
              rwa [hdecomp, add_sub_cancel_left] at this
            simpa [hc] using Submodule.smul_mem _ c⁻¹ this
          have he0 : e i := by_contra fun h => hei ⟨h, he1⟩
          rw [hdecomp]; exact add_mem hw'0 (Submodule.smul_mem _ c he0)
      · rw [stepInd_eq_one hTi]; have := stepInd_le_one V i; omega
    · rw [stepInd_eq_one hPi]; have := stepInd_le_one V i; omega
  have hsum : strictSteps V ℓ ≤ strictSteps P ℓ + strictSteps T ℓ + 1 := by
    rw [strictSteps_eq_sum, strictSteps_eq_sum, strictSteps_eq_sum]
    calc ∑ i ∈ Finset.range ℓ, stepInd V i
        ≤ ∑ i ∈ Finset.range ℓ, (stepInd P i + stepInd T i +
            (if ¬ e i ∧ e (i + 1) then 1 else 0)) :=
          Finset.sum_le_sum fun i hi => key i (Finset.mem_range.mp hi)
      _ ≤ _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]; omega
  omega

end Prod

section Pi

/-- `x ↦ (x 0, x ∘ succ)` as a `⋆`-algebra homomorphism. -/
def consHom {m : ℕ} (B : Fin (m + 1) → Type*) [∀ i, Ring (B i)] [∀ i, Algebra ℂ (B i)]
    [∀ i, StarRing (B i)] :
    ((i : Fin (m + 1)) → B i) →⋆ₐ[ℂ] (B 0 × ((i : Fin m) → B i.succ)) where
  toFun x := (x 0, fun i => x i.succ)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem consHom_injective {m : ℕ} (B : Fin (m + 1) → Type*) [∀ i, Ring (B i)]
    [∀ i, Algebra ℂ (B i)] [∀ i, StarRing (B i)] : Function.Injective (consHom B) := by
  intro x y h
  have h0 : x 0 = y 0 := congrArg Prod.fst h
  have h1 : ∀ i : Fin m, x i.succ = y i.succ := fun i => congrFun (congrArg Prod.snd h) i
  funext i
  exact Fin.cases h0 h1 i

/-- Evaluation at `0` on `Π i : Fin 1, B i`. -/
def evalZeroHom (B : Fin 1 → Type*) [∀ i, Ring (B i)] [∀ i, Algebra ℂ (B i)]
    [∀ i, StarRing (B i)] : ((i : Fin 1) → B i) →⋆ₐ[ℂ] B 0 where
  toFun x := x 0
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/-- **Lemma 5.11** (all multiplicities kept). -/
theorem chainBound_pi : ∀ (m : ℕ) (B : Fin (m + 1) → Type*) [∀ i, Ring (B i)]
    [∀ i, Algebra ℂ (B i)] [∀ i, StarRing (B i)] [∀ i, StarModule ℂ (B i)] (N : Fin (m + 1) → ℕ),
    (∀ i, ChainBound (B i) (N i)) → ChainBound ((i : Fin (m + 1)) → B i) (∑ i, N i)
  | 0, B, _, _, _, _, N, h => by
    rw [Fin.sum_univ_one]
    refine ChainBound.of_injective (evalZeroHom B) (fun x y hxy => ?_) (h 0)
    funext i
    rw [Subsingleton.elim i 0]
    exact hxy
  | m + 1, B, _, _, _, _, N, h => by
    rw [Fin.sum_univ_succ]
    exact ChainBound.of_injective (consHom B) (consHom_injective B)
      (chainBound_prod (h 0) (chainBound_pi m (fun i => B i.succ) (fun i => N i.succ)
        fun i => h i.succ))

end Pi

end Lax119563Proofs.Stabilization

end Stabilization_Products

/-! ### Formerly `Lax119563Proofs.Stabilization.Recursion` -/

section Stabilization_Recursion

/-!
# Arithmetic of the recursion (replaces Döring–Neuen, Lemmas 5.13 and Claim 5.14)

With `c = Nat.clog 2` and the weight `recW d = 2 c(d) + 9`, the bound `h(n) = 10 n - recW n`
satisfies the recursion of Theorem 5.15. Stated additively: for a list `L` of dimensions with
sum `n`,
* (some `d ∈ L` with `n < 2 d < 2 n`) `recW n + 2 + c(n - d) ≤ Σ_L recW`;
* (all `2 d ≤ n`, `2 ≤ n`) `recW n + 1 + c(n²) ≤ Σ_L recW`.
-/

namespace Lax119563Proofs.Stabilization

/-- The weight `2 ⌈log₂ d⌉ + 9`. -/
def recW (d : ℕ) : ℕ := 2 * Nat.clog 2 d + 9

theorem clog_le_of_le_two_pow_mul {n m k : ℕ} (h : n ≤ 2 ^ k * m) :
    Nat.clog 2 n ≤ Nat.clog 2 m + k := by
  apply Nat.clog_le_of_le_pow
  have hm := Nat.le_pow_clog (by norm_num : 1 < 2) m
  calc n ≤ 2 ^ k * m := h
    _ ≤ 2 ^ k * 2 ^ Nat.clog 2 m := Nat.mul_le_mul_left _ hm
    _ = 2 ^ (Nat.clog 2 m + k) := by rw [pow_add, mul_comm]

theorem clog_add_le (a b : ℕ) : Nat.clog 2 (a + b) ≤ Nat.clog 2 a + Nat.clog 2 b + 1 := by
  rcases le_total a b with h | h
  · have := clog_le_of_le_two_pow_mul (n := a + b) (m := b) (k := 1) (by omega)
    omega
  · have := clog_le_of_le_two_pow_mul (n := a + b) (m := a) (k := 1) (by omega)
    omega

theorem clog_mul_self_le (n : ℕ) : Nat.clog 2 (n * n) ≤ 2 * Nat.clog 2 n := by
  apply Nat.clog_le_of_le_pow
  have hn := Nat.le_pow_clog (by norm_num : 1 < 2) n
  calc n * n ≤ 2 ^ Nat.clog 2 n * 2 ^ Nat.clog 2 n := Nat.mul_le_mul hn hn
    _ = 2 ^ (2 * Nat.clog 2 n) := by rw [← pow_add, two_mul]

theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem recW_add (a b : ℕ) : recW (a + b) ≤ recW a + recW b := by
  unfold recW; have := clog_add_le a b; omega

/-- Subadditivity of `recW` over a list with positive sum. -/
theorem recW_sum_le (L : List ℕ) (h : 1 ≤ L.sum) : recW L.sum ≤ (L.map recW).sum := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    simp only [List.sum_cons, List.map_cons]
    by_cases hL : L.sum = 0
    · rw [hL, add_zero]; exact Nat.le_add_right _ _
    · have := ih (by omega)
      have := recW_add a L.sum
      omega

/-- Recursion, case of a large block `2 d > n`. -/
theorem recursion_big (L : List ℕ) (n d : ℕ) (hsum : L.sum = n) (hd : d ∈ L) (hdn : d < n)
    (h2 : n < 2 * d) : recW n + 2 + Nat.clog 2 (n - d) ≤ (L.map recW).sum := by
  have hp := List.perm_cons_erase hd
  have hs : L.sum = d + (L.erase d).sum := by rw [hp.sum_eq, List.sum_cons]
  have hs' : (L.map recW).sum = recW d + ((L.erase d).map recW).sum := by
    rw [(hp.map recW).sum_eq, List.map_cons, List.sum_cons]
  have hrest := recW_sum_le (L.erase d) (by omega)
  have hrest' : (L.erase d).sum = n - d := by omega
  rw [hrest'] at hrest
  have hc : Nat.clog 2 n ≤ Nat.clog 2 d + 1 := clog_le_of_le_two_pow_mul (by omega)
  rw [hs']
  unfold recW at hrest ⊢
  omega

/-- Recursion, case of only small blocks `2 d ≤ n` (two groups of sum `≥ n / 4`). -/
theorem recursion_small (L : List ℕ) (n : ℕ) (hn : 2 ≤ n) (hsum : L.sum = n)
    (hsmall : ∀ x ∈ L, 2 * x ≤ n) : recW n + 1 + Nat.clog 2 (n * n) ≤ (L.map recW).sum := by
  classical
  have hex : ∃ k, n ≤ 4 * (L.take k).sum := ⟨L.length, by rw [List.take_length]; omega⟩
  set k := Nat.find hex with hk
  have hk1 : n ≤ 4 * (L.take k).sum := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h; rw [h, List.take_zero, List.sum_nil] at hk1; omega
  have hk2 : ¬ n ≤ 4 * (L.take (k - 1)).sum := Nat.find_min hex (by omega)
  have hlen : k - 1 < L.length := by
    by_contra hcon
    rw [List.take_of_length_le (by omega)] at hk2
    omega
  have htk : (L.take k).sum = (L.take (k - 1)).sum + L[k - 1] := by
    rw [← List.sum_take_succ _ _ hlen, Nat.sub_add_cancel (by omega)]
  have hmem := hsmall _ (List.getElem_mem hlen)
  have hsplit := List.sum_take_add_sum_drop L k
  have hsplit' : (L.map recW).sum = ((L.take k).map recW).sum + ((L.drop k).map recW).sum := by
    rw [← List.sum_take_add_sum_drop (L.map recW) k, List.map_take, List.map_drop]
  have h1 := recW_sum_le (L.take k) (by omega)
  have h2 := recW_sum_le (L.drop k) (by omega)
  have c1 : Nat.clog 2 n ≤ Nat.clog 2 (L.take k).sum + 2 :=
    clog_le_of_le_two_pow_mul (by norm_num; omega)
  have c2 : Nat.clog 2 n ≤ Nat.clog 2 (L.drop k).sum + 2 :=
    clog_le_of_le_two_pow_mul (by norm_num; omega)
  have c3 := clog_mul_self_le n
  rw [hsplit']
  unfold recW at h1 h2 ⊢
  omega

end Lax119563Proofs.Stabilization

end Stabilization_Recursion

/-! ### Formerly `Lax119563Proofs.Stabilization.Structure` -/

section Stabilization_Structure

/-!
# Stabilization bound: structure of `⋆`-subalgebras of `End(E)`

`E` is a finite dimensional complex inner product space, `S` a `⋆`-subalgebra of `End(E)`
(star = adjoint). We show

* `E` is a semisimple `S`-module (orthogonal complements of invariant subspaces are invariant);
* `mem_of_corner'`: if `W` is `S`-simple with `2 dim W > dim E`, every operator with range in `W`
  vanishing on `Wᗮ` lies in `S` (Jacobson density / bicommutant theorem);
* `exists_decomposition'`: `E` splits into `S`-simple subspaces, and restriction to them is an
  injective unital `⋆`-algebra homomorphism.
-/

open Module

namespace Lax119563Proofs.Stabilization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

section Basic

variable (S : StarSubalgebra ℂ (E →ₗ[ℂ] E))

instance isScalarTower_starSubalgebra : IsScalarTower ℂ S E :=
  ⟨fun _ _ _ => rfl⟩

theorem invariant_orthogonal {W : Submodule ℂ E} (hW : Invariant S W) : Invariant S Wᗮ := by
  intro a ha x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← LinearMap.adjoint_inner_left]
  exact (Submodule.mem_orthogonal _ _).1 hx _ (hW _ (star_mem ha) u hu)

/-- The `S`-submodule of `E` given by an `S`-invariant subspace. -/
def toSSubmodule (W : Submodule ℂ E) (hW : Invariant S W) : Submodule S E where
  carrier := W
  add_mem' := W.add_mem
  zero_mem' := W.zero_mem
  smul_mem' a _ hx := hW a a.2 _ hx

theorem restrictScalars_toSSubmodule (W : Submodule ℂ E) (hW : Invariant S W) :
    (toSSubmodule S W hW).restrictScalars ℂ = W := rfl

theorem invariant_restrictScalars (p : Submodule S E) : Invariant S (p.restrictScalars ℂ) :=
  fun a ha _ hx => p.smul_mem ⟨a, ha⟩ hx

instance isSemisimpleModule : IsSemisimpleModule S E := by
  refine (isSemisimpleModule_iff S E).2 ⟨fun p =>
    ⟨toSSubmodule S _ (invariant_orthogonal S (invariant_restrictScalars S p)), ?_⟩⟩
  rw [← Submodule.isCompl_restrictScalars_iff ℂ, restrictScalars_toSSubmodule]
  exact Submodule.isCompl_orthogonal (K := p.restrictScalars ℂ)

end Basic

section Corner

variable {S : StarSubalgebra ℂ (E →ₗ[ℂ] E)}

/-- A map commuting with `S` preserves every big `S`-simple subspace. -/
theorem preserves_of_commute {W : Submodule ℂ E} (hW : IsSimpleFor S W)
    (h2 : finrank ℂ E < 2 * finrank ℂ W) (b : E →ₗ[ℂ] E) (hb : ∀ a ∈ S, b * a = a * b) :
    ∀ x ∈ W, b x ∈ W := by
  let U : Submodule ℂ E := W ⊓ W.comap b
  have hU : Invariant S U := by
    rintro a ha x ⟨hxW, hxb⟩
    refine ⟨hW.2.1 a ha x hxW, ?_⟩
    have h := LinearMap.congr_fun (hb a ha) x
    simp only [Module.End.mul_apply] at h
    show b (a x) ∈ W
    rw [h]
    exact hW.2.1 a ha _ hxb
  rcases hW.2.2 U inf_le_left hU with h | h
  · exfalso
    let f : W →ₗ[ℂ] E ⧸ W := W.mkQ ∘ₗ b ∘ₗ W.subtype
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      have hwU : (w : E) ∈ U := ⟨w.2, (Submodule.Quotient.mk_eq_zero W).1 hw⟩
      rw [h] at hwU
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 hwU)
    have h1 := LinearMap.finrank_le_finrank_of_injective hf
    have h3 := W.finrank_quotient_add_finrank
    omega
  · intro x hx
    have hxU : x ∈ U := h ▸ hx
    exact hxU.2

/-- A map commuting with `S` and preserving an `S`-simple subspace acts on it as a scalar. -/
theorem exists_scalar_of_commute {W : Submodule ℂ E} (hW : IsSimpleFor S W) (b : E →ₗ[ℂ] E)
    (hb : ∀ a ∈ S, b * a = a * b) (hbW : ∀ x ∈ W, b x ∈ W) :
    ∃ c : ℂ, ∀ x ∈ W, b x = c • x := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW.1
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (b.restrict hbW)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  let U : Submodule ℂ E := W ⊓ Module.End.eigenspace b c
  have hU : Invariant S U := by
    rintro a ha x ⟨hxW, hxk⟩
    refine ⟨hW.2.1 a ha x hxW, ?_⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hxk ⊢
    have h := LinearMap.congr_fun (hb a ha) x
    simp only [Module.End.mul_apply] at h
    rw [h, hxk, map_smul]
  rcases hW.2.2 U inf_le_left hU with h | h
  · exfalso
    have hvU : (v : E) ∈ U := by
      refine ⟨v.2, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      exact congrArg Subtype.val hv.apply_eq_smul
    rw [h] at hvU
    exact hv.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 hvU))
  · refine ⟨c, fun x hx => ?_⟩
    have hxU : x ∈ U := h ▸ hx
    exact Module.End.mem_eigenspace_iff.1 hxU.2

theorem star_commute {b : E →ₗ[ℂ] E} (hb : ∀ a ∈ S, b * a = a * b) :
    ∀ a ∈ S, star b * a = a * star b := by
  intro a ha
  have h := congrArg star (hb (star a) (star_mem ha))
  simp only [star_mul, star_star] at h
  exact h.symm

/-- **Corner lemma.** -/
theorem mem_of_corner' (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) (W : Submodule ℂ E)
    (hW : IsSimpleFor S W) (h2 : finrank ℂ E < 2 * finrank ℂ W) (T : E →ₗ[ℂ] E)
    (hT : LinearMap.range T ≤ W) (hT' : Wᗮ ≤ LinearMap.ker T) : T ∈ S := by
  classical
  -- every map commuting with `S` commutes with `T`
  have hcomm : ∀ b : E →ₗ[ℂ] E, (∀ a ∈ S, b * a = a * b) → ∀ x, T (b x) = b (T x) := by
    intro b hb x
    have hbW := preserves_of_commute hW h2 b hb
    have hbW' : ∀ y ∈ Wᗮ, b y ∈ Wᗮ := by
      intro y hy
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [← LinearMap.adjoint_inner_left]
      exact (Submodule.mem_orthogonal _ _).1 hy _
        (preserves_of_commute hW h2 (star b) (star_commute hb) u hu)
    obtain ⟨c, hc⟩ := exists_scalar_of_commute hW b hb hbW
    have hx : x ∈ W ⊔ Wᗮ := by
      rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have hTz : T z = 0 := hT' hz
    have hTbz : T (b z) = 0 := hT' (hbW' z hz)
    have hTy : T y ∈ W := hT ⟨y, rfl⟩
    rw [map_add b, map_add T, map_add T, hTz, hTbz, hc y hy, map_smul, add_zero, add_zero, hc _ hTy]
  let f : Module.End (Module.End S E) E :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun b x => hcomm (b.restrictScalars ℂ)
        (fun a ha => LinearMap.ext fun y => b.map_smul ⟨a, ha⟩ y) x }
  let s : Finset E := Finset.univ.image (Module.finBasis ℂ E)
  obtain ⟨r, hr⟩ := jacobson_density f s
  have hTr : T = (r : E →ₗ[ℂ] E) :=
    (Module.finBasis ℂ E).ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  rw [hTr]
  exact r.2

end Corner

section Decomposition

/-- Restriction of `a ∈ S` to an `S`-invariant subspace commutes with taking adjoints. -/
theorem star_restrict {W : Submodule ℂ E} (a : E →ₗ[ℂ] E) (ha : ∀ x ∈ W, a x ∈ W)
    (ha' : ∀ x ∈ W, star a x ∈ W) : (star a).restrict ha' = star (a.restrict ha) := by
  change _ = LinearMap.adjoint _
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  simp only [Submodule.coe_inner, LinearMap.coe_restrict_apply]
  exact LinearMap.adjoint_inner_left a y x

/-- **Decomposition.** -/
theorem exists_decomposition' (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) :
    ∃ (m : ℕ) (W : Fin m → Submodule ℂ E), (∀ j, IsSimpleFor S (W j)) ∧
      ∑ j, finrank ℂ (W j) = finrank ℂ E ∧
      ∃ ρ : S →⋆ₐ[ℂ] ((j : Fin m) → (W j →ₗ[ℂ] W j)), Function.Injective ρ := by
  classical
  obtain ⟨s, hind, htop, hsimple⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top S E
  have : IsNoetherian S E := isNoetherian_of_tower ℂ inferInstance
  have : Finite s := (WellFoundedGT.finite_of_sSupIndep hind).to_subtype
  obtain ⟨m, ⟨σ⟩⟩ := Finite.exists_equiv_fin s
  let p : Fin m → Submodule S E := fun j => (σ.symm j).1
  let W : Fin m → Submodule ℂ E := fun j => (p j).restrictScalars ℂ
  have hindS : iSupIndep p := ((sSupIndep_iff s).1 hind).comp σ.symm.injective
  have hindC : iSupIndep W := by
    intro j
    have h := (Submodule.disjoint_restrictScalars_iff (S := ℂ)).2 (hindS j)
    simp only [Submodule.restrictScalars_iSup] at h
    exact h
  have htopS : iSup p = ⊤ := by
    rw [← htop, sSup_eq_iSup']
    exact σ.symm.iSup_comp (g := fun x : s => (x : Submodule S E))
  have htopC : iSup W = ⊤ := by
    simp only [W, ← Submodule.restrictScalars_iSup, htopS, Submodule.restrictScalars_top]
  have hinv : ∀ j, Invariant S (W j) := fun j => invariant_restrictScalars S (p j)
  refine ⟨m, W, fun j => ?_, ?_, ?_⟩
  · have hat : IsAtom (p j) := (isSimpleModule_iff_isAtom).1 (hsimple _ (σ.symm j).2)
    refine ⟨?_, hinv j, fun U hU hUi => ?_⟩
    · simpa [W, Submodule.restrictScalars_eq_bot_iff] using hat.1
    · rcases (hat.le_iff).1 (show toSSubmodule S U hUi ≤ p j from hU) with h | h
      · left
        rw [← restrictScalars_toSSubmodule S U hUi, h, Submodule.restrictScalars_bot]
      · right
        rw [← restrictScalars_toSSubmodule S U hUi, h]
  · have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindC htopC
    rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hint).finrank_eq,
      Module.finrank_directSum]
  · let ρ : S →⋆ₐ[ℂ] ((j : Fin m) → (W j →ₗ[ℂ] W j)) :=
      { toFun := fun a j => (a : E →ₗ[ℂ] E).restrict (hinv j a a.2)
        map_one' := by ext j x; rfl
        map_mul' := by intro a b; ext j x; rfl
        map_zero' := by ext j x; rfl
        map_add' := by intro a b; ext j x; rfl
        commutes' := by intro c; ext j x; rfl
        map_star' := by
          intro a
          funext j
          exact star_restrict (a : E →ₗ[ℂ] E) _ _ }
    refine ⟨ρ, (injective_iff_map_eq_zero ρ).2 fun a ha => ?_⟩
    have hker : ∀ j, W j ≤ LinearMap.ker (a : E →ₗ[ℂ] E) := by
      intro j x hx
      have h := congrArg (fun f => ((f j ⟨x, hx⟩ : W j) : E)) ha
      exact h
    have h := iSup_le hker
    rw [htopC, top_le_iff, LinearMap.ker_eq_top] at h
    exact Subtype.ext h

end Decomposition

end Lax119563Proofs.Stabilization

end Stabilization_Structure

/-! ### Formerly `Lax119563Proofs.Stabilization.Interface` -/

section Stabilization_Interface

/-!
# Stabilization bound: structure of `⋆`-subalgebras of `End(E)`

The corner lemma and the decomposition into simple invariant subspaces, in the form used by the
two-dimensional bound (`TwoDim.lean`). Proofs in `Structure.lean`; definitions in `Defs.lean`.
-/

open Module

namespace Lax119563Proofs.Stabilization

section Structure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Corner lemma**. If `W` is `S`-simple and `2 dim W > dim E`, then `S`
contains every operator with range in `W` vanishing on `Wᗮ`. -/
theorem mem_of_corner (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) (W : Submodule ℂ E)
    (hW : IsSimpleFor S W) (h2 : finrank ℂ E < 2 * finrank ℂ W) (T : E →ₗ[ℂ] E)
    (hT : LinearMap.range T ≤ W) (hT' : Wᗮ ≤ LinearMap.ker T) : T ∈ S :=
  mem_of_corner' S W hW h2 T hT hT'

/-- **Decomposition**. `E` splits into `S`-simple subspaces, and restriction
to them is an injective unital `⋆`-algebra homomorphism. -/
theorem exists_decomposition (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) :
    ∃ (m : ℕ) (W : Fin m → Submodule ℂ E), (∀ j, IsSimpleFor S (W j)) ∧
      ∑ j, finrank ℂ (W j) = finrank ℂ E ∧
      ∃ ρ : S →⋆ₐ[ℂ] ((j : Fin m) → (W j →ₗ[ℂ] W j)), Function.Injective ρ :=
  exists_decomposition' S

end Structure

end Lax119563Proofs.Stabilization

end Stabilization_Interface

/-! ### Formerly `Lax119563Proofs.Stabilization.Colorings` -/

section Stabilization_Colorings

/-!
# Colorings produced by `k`-WL and their matrix spaces

Döring–Neuen §4 and §6.1, for the colorings `χ_r = color G r` of `k`-WL on a colored graph `G`
(the sequence is infinite; no termination index is needed):

* `χ_{r+1}` refines `χ_r`; `χ_r` is compatible with equality and shufflable for every
  `σ : Fin k → Fin k` (Lemma 4.2);
* the space `classSpace χ` of matrices constant on the color classes of a coloring `χ` of pairs
  (the span `⟨χ⟩` of the paper), and Lemmas 4.5–4.7;
* for `k = m + 2` and `v ∈ V^m` the projections `χ^v_r (a, b) = χ_r (v, a, b)`:
  multiplicativity (Lemma 6.2) and extendability (Lemma 6.4).
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman

namespace Lax119563Proofs.Stabilization

/-! ### Refinement, compatibility with equality, shufflability -/

section Basic

variable {G : ColoredGraph} {k : ℕ}

theorem color_succ (r : ℕ) (p : Fin k → Fin G.n) :
    color G (r + 1) p =
      (color G r p, (Finset.univ : Finset (Fin G.n)).val.map
        fun q i => color G r (Function.update p i q)) := rfl

/-- `χ_{r+1}` refines `χ_r`. -/
theorem color_eq_of_succ {r : ℕ} {p q : Fin k → Fin G.n}
    (h : color G (r + 1) p = color G (r + 1) q) : color G r p = color G r q := by
  rw [color_succ, color_succ] at h
  exact congrArg Prod.fst h

theorem color_eq_of_le {s r : ℕ} (hsr : s ≤ r) {p q : Fin k → Fin G.n}
    (h : color G r p = color G r q) : color G s p = color G s q := by
  induction r, hsr using Nat.le_induction with
  | base => exact h
  | succ r _ ih => exact ih (color_eq_of_succ h)

/-- `χ_r` is compatible with equality. -/
theorem eq_iff_of_color_eq {r : ℕ} {p q : Fin k → Fin G.n} (h : color G r p = color G r q)
    (i j : Fin k) : p i = p j ↔ q i = q j := by
  have h0 := congrArg AtomicType.eq (color_eq_of_le (Nat.zero_le r) h)
  have := congrFun (congrFun h0 i) j
  simpa [color, atp] using this

/-- Replacing coordinate `i` of `p ∘ σ` is replacing some coordinate of `p` and then
composing with some map: for injective `σ` take `σ i` and `σ`, otherwise a coordinate `j`
outside the range of `σ` and `σ` redirected to `j` at `i`. -/
theorem exists_update_comp {α : Type*} (σ : Fin k → Fin k) (i : Fin k) :
    ∃ (j : Fin k) (τ : Fin k → Fin k), ∀ (p : Fin k → α) (x : α),
      Function.update (p ∘ σ) i x = Function.update p j x ∘ τ := by
  classical
  by_cases hσ : Function.Injective σ
  · exact ⟨σ i, σ, fun p x => (Function.update_comp_eq_of_injective p hσ i x).symm⟩
  · have hs : ¬ Function.Surjective σ := fun hs => hσ (Finite.injective_iff_surjective.2 hs)
    simp only [Function.Surjective, not_forall, not_exists] at hs
    obtain ⟨j, hj⟩ := hs
    refine ⟨j, Function.update σ i j, fun p x => ?_⟩
    funext i'
    by_cases hi : i' = i
    · subst hi; simp
    · simp [Function.update_of_ne hi, Function.update_of_ne (hj i')]

/-- `χ_r` is shufflable, for every (not necessarily bijective) `σ : Fin k → Fin k`. -/
theorem color_comp_eq (r : ℕ) : ∀ (σ : Fin k → Fin k) {p q : Fin k → Fin G.n},
    color G r p = color G r q → color G r (p ∘ σ) = color G r (q ∘ σ) := by
  induction r with
  | zero =>
    intro σ p q h
    have he := congrArg AtomicType.eq h
    have ha := congrArg AtomicType.adj h
    have hc := congrArg AtomicType.color h
    have key : ∀ p : Fin k → Fin G.n, color G 0 (p ∘ σ) =
        ⟨fun i j => (atp G p).eq (σ i) (σ j), fun i j => (atp G p).adj (σ i) (σ j),
          fun i => (atp G p).color (σ i)⟩ := fun p => rfl
    rw [key p, key q]
    change (atp G p).eq = (atp G q).eq at he
    change (atp G p).adj = (atp G q).adj at ha
    change (atp G p).color = (atp G q).color at hc
    rw [he, ha, hc]
  | succ r ih =>
    intro σ p q h
    rw [color_succ, color_succ] at h ⊢
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    refine Prod.ext (ih σ h1) ?_
    refine UpperBound.multiset_map_eq_of_map_eq (fun a b hab => ?_) _ _ h2
    funext i
    obtain ⟨j, τ, hjτ⟩ := exists_update_comp (α := Fin G.n) σ i
    rw [hjτ p a, hjτ q b]
    exact ih τ (congrFun hab j)

end Basic

/-! ### Matrix spaces of colorings of pairs -/

section ClassSpace

variable {α β β' : Type*}

/-- The matrices constant on the color classes of `χ` (the span `⟨χ⟩` of the paper). -/
def classSpace (χ : α → α → β) : Submodule ℂ (Matrix α α ℂ) where
  carrier := {M | ∀ a b c d, χ a b = χ c d → M a b = M c d}
  add_mem' := by
    intro M N hM hN a b c d h
    simp [hM a b c d h, hN a b c d h]
  zero_mem' := by
    intro a b c d _
    rfl
  smul_mem' := by
    intro s M hM a b c d h
    simp [hM a b c d h]

/-- Lemma 4.7 (and Equation (5)): the space determines the partition. -/
theorem eq_of_classSpace_le {χ : α → α → β} {χ' : α → α → β'}
    (h : classSpace χ' ≤ classSpace χ) {a b c d : α} (hc : χ a b = χ c d) :
    χ' a b = χ' c d := by
  classical
  let M : Matrix α α ℂ := fun x y => if χ' x y = χ' a b then 1 else 0
  have hM : M ∈ classSpace χ' := by
    intro x y z w hxy
    simp only [M, hxy]
  have := h hM a b c d hc
  simp only [M, if_pos rfl] at this
  by_contra hne
  rw [if_neg (Ne.symm hne)] at this
  exact one_ne_zero this

/-- Lemma 4.5: compatibility with equality gives the identity. -/
theorem one_mem_classSpace [DecidableEq α] {χ : α → α → β}
    (h : ∀ a b c d, χ a b = χ c d → (a = b ↔ c = d)) : (1 : Matrix α α ℂ) ∈ classSpace χ := by
  intro a b c d hc
  simp only [Matrix.one_apply, h a b c d hc]

/-- Lemma 4.6: symmetric classes give closure under conjugate transposition. -/
theorem star_mem_classSpace {χ : α → α → β}
    (h : ∀ a b c d, χ a b = χ c d → χ b a = χ d c) {M : Matrix α α ℂ}
    (hM : M ∈ classSpace χ) : star M ∈ classSpace χ := by
  intro a b c d hc
  simp only [Matrix.star_apply, hM b a d c (h a b c d hc)]

end ClassSpace

/-! ### Projections `χ^v_r (a, b) = χ_r (v, a, b)` for `k = m + 2` -/

section Projections

variable {α : Type*} {m : ℕ}

/-- The tuple `(v, a, b)`. -/
def tup (v : Fin m → α) (a b : α) : Fin (m + 2) → α :=
  Fin.snoc (Fin.snoc v a : Fin (m + 1) → α) b

/-- The coordinate of `a` in `(v, a, b)`. -/
def penIdx (m : ℕ) : Fin (m + 2) := (Fin.last m).castSucc

/-- The coordinates of `v` in `(v, a, b)`. -/
def vIdx (m : ℕ) (i : Fin m) : Fin (m + 2) := i.castSucc.castSucc

@[simp] theorem tup_last (v : Fin m → α) (a b : α) : tup v a b (Fin.last (m + 1)) = b := by
  simp [tup]

@[simp] theorem tup_pen (v : Fin m → α) (a b : α) : tup v a b (penIdx m) = a := by
  simp [tup, penIdx]

@[simp] theorem tup_vIdx (v : Fin m → α) (a b : α) (i : Fin m) : tup v a b (vIdx m i) = v i := by
  simp [tup, vIdx]

theorem tup_eta (p : Fin (m + 2) → α) :
    tup (p ∘ vIdx m) (p (penIdx m)) (p (Fin.last (m + 1))) = p := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · exact tup_pen _ _ _
    · exact tup_vIdx _ _ _ j

theorem comp_tup {γ : Type*} (f : α → γ) (v : Fin m → α) (a b : α) :
    f ∘ tup v a b = tup (f ∘ v) (f a) (f b) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · exact (tup_pen (f ∘ v) (f a) (f b)).symm ▸ congrArg f (tup_pen v a b)
    · exact (tup_vIdx (f ∘ v) (f a) (f b) j).symm ▸ congrArg f (tup_vIdx v a b j)

theorem tup_comp_tup (v : Fin m → α) (a b : α) (x y : Fin (m + 2)) :
    tup v a b ∘ tup (vIdx m) x y = tup v (tup v a b x) (tup v a b y) := by
  rw [comp_tup]
  congr 1
  funext i
  simp

@[simp] theorem update_tup_last (v : Fin m → α) (a b w : α) :
    Function.update (tup v a b) (Fin.last (m + 1)) w = tup v a w := by
  simp [tup, Fin.update_snoc_last]

@[simp] theorem update_tup_pen (v : Fin m → α) (a b w : α) :
    Function.update (tup v a b) (penIdx m) w = tup v w b := by
  rw [tup, penIdx, ← Fin.snoc_update, Fin.update_snoc_last, tup]

end Projections

section WLProjections

variable {G : ColoredGraph} {m : ℕ}

/-- The projection `χ^v_r (a, b) = χ_r (v, a, b)`. -/
noncomputable def proj (G : ColoredGraph) (r : ℕ) (v : Fin m → Fin G.n) (a b : Fin G.n) :
    Color (m + 2) r :=
  color G r (tup v a b)

theorem proj_eq_of_succ {r : ℕ} {v w : Fin m → Fin G.n} {a b c d : Fin G.n}
    (h : proj G (r + 1) v a b = proj G (r + 1) w c d) : proj G r v a b = proj G r w c d :=
  color_eq_of_succ h

theorem proj_eq_iff {r : ℕ} {v w : Fin m → Fin G.n} {a b c d : Fin G.n}
    (h : proj G r v a b = proj G r w c d) : a = b ↔ c = d := by
  have := eq_iff_of_color_eq h (penIdx m) (Fin.last (m + 1))
  simpa using this

/-- Shuffling the coordinates of `(v, a, b)` by `(vIdx, x, y)`. -/
theorem proj_shuffle {r : ℕ} {v w : Fin m → Fin G.n} {a b c d : Fin G.n}
    (h : proj G r v a b = proj G r w c d) (x y : Fin (m + 2)) :
    proj G r v (tup v a b x) (tup v a b y) = proj G r w (tup w c d x) (tup w c d y) := by
  have := color_comp_eq r (tup (vIdx m) x y) h
  rwa [tup_comp_tup, tup_comp_tup] at this

theorem proj_swap {r : ℕ} {v w : Fin m → Fin G.n} {a b c d : Fin G.n}
    (h : proj G r v a b = proj G r w c d) : proj G r v b a = proj G r w d c := by
  simpa using proj_shuffle h (Fin.last (m + 1)) (penIdx m)

theorem one_mem_classSpace_proj (r : ℕ) (v : Fin m → Fin G.n) :
    (1 : Matrix (Fin G.n) (Fin G.n) ℂ) ∈ classSpace (proj G r v) :=
  one_mem_classSpace fun _ _ _ _ h => proj_eq_iff h

theorem star_mem_classSpace_proj (r : ℕ) (v : Fin m → Fin G.n)
    {M : Matrix (Fin G.n) (Fin G.n) ℂ} (hM : M ∈ classSpace (proj G r v)) :
    star M ∈ classSpace (proj G r v) :=
  star_mem_classSpace (fun _ _ _ _ h => proj_swap h) hM

/-- **Lemma 6.2** (multiplicativity): entry `(u, u')` of a product of two matrices constant on
the classes of `χ^v_r` is a sum over the multiset part of `χ_{r+1} (v, u, u')`. -/
theorem classSpace_proj_mul_le (r : ℕ) (v : Fin m → Fin G.n) :
    classSpace (proj G r v) * classSpace (proj G r v) ≤ classSpace (proj G (r + 1) v) := by
  rw [Submodule.mul_le]
  intro A hA B hB u u' c d h
  simp only [Matrix.mul_apply, Finset.sum_eq_multiset_sum]
  unfold proj at h
  rw [color_succ, color_succ] at h
  refine congrArg Multiset.sum
    (UpperBound.multiset_map_eq_of_map_eq (fun a b hab => ?_) _ _ (Prod.mk.inj h).2)
  have h1 := congrFun hab (Fin.last (m + 1))
  have h2 := congrFun hab (penIdx m)
  simp only [update_tup_last, update_tup_pen] at h1 h2
  rw [hA u a c b h1, hB a u' b d h2]

/-- **Lemma 6.4** (extendability). -/
theorem proj_succ_diag_ne {r : ℕ} {v w : Fin m → Fin G.n} {a b : Fin G.n}
    (h : ∀ x y, proj G r v a b ≠ proj G r w x y) (x : Fin G.n) :
    proj G (r + 1) v a a ≠ proj G (r + 1) w x x := by
  intro hx
  unfold proj at hx
  rw [color_succ, color_succ] at hx
  have h2 := (Prod.mk.inj hx).2
  have hmem : (fun i => color G r (Function.update (tup v a a) i b)) ∈
      (Finset.univ : Finset (Fin G.n)).val.map
        (fun q i => color G r (Function.update (tup v a a) i q)) :=
    Multiset.mem_map.2 ⟨b, Finset.mem_univ_val b, rfl⟩
  rw [h2] at hmem
  obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 hmem
  have := congrFun hy (Fin.last (m + 1))
  simp only [update_tup_last] at this
  exact h x y this.symm

end WLProjections

end Lax119563Proofs.Stabilization

end Stabilization_Colorings

/-! ### Formerly `Lax119563Proofs.Stabilization.TwoDim` -/

section Stabilization_TwoDim

/-!
# The two-dimensional bound (Döring–Neuen, Theorem 5.15)

By strong induction on `n = finrank E ≥ 1`: `ChainBound (End E) N` with `N + recW n ≤ 10 n`,
`recW n = 2 ⌈log₂ n⌉ + 9`. For a chain `V` of length `ℓ` let `s` be the last index with
`alg (V s) ≠ ⊤` and `S = alg (V s)`; decompose `E` into `S`-simple blocks of dimensions
`d j < n`. Let `r` be minimal with `V s ^ 2 ^ r = S`. The chain `V 0, …, V s, V s ^ 2, …,
V s ^ 2 ^ r` lies in `S` and has `strictSteps V s + r` strict steps, so by Lemma 5.11 and the
induction hypothesis `strictSteps V s + r + 1 ≤ Σ N j`. After `s`:
* (all `2 d j ≤ n`) `V (s + 1 + c(n²)) = ⊤` (Claim 5.16, via `V ^ n² = alg V`);
* (some `2 d j > n`) the corner maps of `W j` lie in `S = V s ^ 2 ^ r ≤ V (s + r + 1) =: X`,
  so `X ^ (2 (n - d j)) = ⊤` (Lemma 5.12) and `V (s + r + 2 + c(n - d j)) = ⊤` (Claim 5.17).

The `r` squaring steps replace the surgery of Lemma 5.5 (no maximal chains are needed).
-/

open Module

set_option linter.unusedSectionVars false

namespace Lax119563Proofs.Stabilization

/-- If `ℂ 1` is everything, chains have no strict steps. -/
theorem chainBound_one_of_span_eq_top {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    [StarModule ℂ A] (h : (ℂ ∙ (1 : A)) = ⊤) : ChainBound A 1 := by
  intro V ℓ hV
  suffices strictSteps V ℓ = 0 by omega
  rw [strictSteps_eq_sum]
  refine Finset.sum_eq_zero fun i hi => stepInd_eq_zero ?_
  have hi := Finset.mem_range.mp hi
  have a : V 0 ≤ V i := hV.mono (Nat.zero_le _) hi.le
  have b : V 0 ≤ V (i + 1) := hV.mono (Nat.zero_le _) hi
  rw [hV.zero, h, top_le_iff] at a b
  rw [a, b]

section Step

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem one_ne_zero_end (h : 1 ≤ finrank ℂ E) : (1 : E →ₗ[ℂ] E) ≠ 0 := by
  obtain ⟨x, hx⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := E)).mp (by omega)
  intro h1
  exact hx (by simpa using LinearMap.congr_fun h1 x)

theorem finrank_end : finrank ℂ (E →ₗ[ℂ] E) = finrank ℂ E * finrank ℂ E :=
  Module.finrank_linearMap ℂ ℂ E E

/-- The induction step of Theorem 5.15. -/
theorem chainBound_step (hn2 : 2 ≤ finrank ℂ E)
    (IH : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F],
      1 ≤ finrank ℂ F → finrank ℂ F < finrank ℂ E →
      ∃ N, ChainBound (F →ₗ[ℂ] F) N ∧ N + recW (finrank ℂ F) ≤ 10 * finrank ℂ F) :
    ChainBound (E →ₗ[ℂ] E) (10 * finrank ℂ E - recW (finrank ℂ E)) := by
  classical
  set n := finrank ℂ E with hn
  intro V ℓ hV
  have hfA : finrank ℂ (E →ₗ[ℂ] E) = n * n := finrank_end
  -- the last index `s` with `alg (V s) ≠ ⊤`
  have h0 : alg (V 0) ≠ ⊤ := by
    intro h
    have he : alg (V 0) = ℂ ∙ (1 : E →ₗ[ℂ] E) := by
      rw [← pow_eq_alg (V 0) (hV.one_mem 0 (Nat.zero_le _)) le_rfl, hV.zero,
        ← Submodule.one_eq_span, one_pow]
    rw [he] at h
    have := finrank_span_singleton (K := ℂ) (one_ne_zero_end (E := E) (by omega))
    rw [h, finrank_top, hfA] at this
    nlinarith
  set s := Nat.findGreatest (fun i => alg (V i) ≠ ⊤) ℓ with hs_def
  have hs : alg (V s) ≠ ⊤ := Nat.findGreatest_spec (P := fun i => alg (V i) ≠ ⊤)
    (Nat.zero_le ℓ) h0
  have hsℓ : s ≤ ℓ := Nat.findGreatest_le ℓ
  have hafter : ∀ i, s < i → i ≤ ℓ → alg (V i) = ⊤ := fun i h1 h2 =>
    not_not.mp (Nat.findGreatest_is_greatest h1 h2)
  have h1s : (1 : E →ₗ[ℂ] E) ∈ V s := hV.one_mem s hsℓ
  have hstar : StarClosed (V s) := hV.star_mem s hsℓ
  set S := algStar (V s) h1s hstar
  have hS : ∀ T : E →ₗ[ℂ] E, T ∈ S → T ∈ alg (V s) := fun T h => h
  have hSne : ∃ T : E →ₗ[ℂ] E, T ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hs (eq_top_iff.mpr fun T _ => hS T (hcon T))
  -- decomposition into simple blocks
  obtain ⟨m, W, hsimple, hsum, ρ, hρ⟩ := exists_decomposition S
  set d : Fin m → ℕ := fun j => finrank ℂ (W j) with hd
  have hd1 : ∀ j, 1 ≤ d j := fun j =>
    Nat.pos_of_ne_zero fun h => (hsimple j).1 (Submodule.finrank_eq_zero.mp h)
  have hdn : ∀ j, d j < n := by
    intro j
    refine lt_of_le_of_ne (Submodule.finrank_le _) fun h => ?_
    have htop : W j = ⊤ := Submodule.eq_top_of_finrank_eq h
    obtain ⟨T, hT⟩ := hSne
    refine hT (mem_of_corner S (W j) (hsimple j)
      (by have h' : finrank ℂ (W j) = n := h; omega) T
      (by rw [htop]; exact le_top) ?_)
    rw [htop, Submodule.top_orthogonal_eq_bot]; exact bot_le
  have hIH : ∀ j, ∃ N, ChainBound (W j →ₗ[ℂ] W j) N ∧ N + recW (d j) ≤ 10 * d j :=
    fun j => IH (W j) (hd1 j) (hdn j)
  choose Nj hNj hNj' using hIH
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun hm => ?_
    subst hm
    simp at hsum
    omega
  have hSb : ChainBound S (∑ j, Nj j) :=
    ChainBound.of_injective ρ hρ (chainBound_pi m' (fun j => W j →ₗ[ℂ] W j) Nj hNj)
  -- the squaring steps inside `S`
  have hexr : ∃ r, V s ^ (2 ^ r) = alg (V s) :=
    ⟨n * n, pow_eq_alg _ h1s (by rw [hfA]; exact Nat.lt_two_pow_self.le)⟩
  set r := Nat.find hexr
  have hr : V s ^ (2 ^ r) = alg (V s) := Nat.find_spec hexr
  have hrmin : ∀ j < r, V s ^ (2 ^ j) ≠ alg (V s) := fun j hj => Nat.find_min hexr hj
  have hbound1 : strictSteps V s + r + 1 ≤ ∑ j, Nj j := by
    have := (hV.isChain_sqExt hsℓ r).strictSteps_add_one_le_of_le S hSb fun i hi x hx => by
      show x ∈ alg (V s)
      rcases le_total i s with h | h
      · rw [sqExt_of_le h] at hx
        exact le_alg _ (hV.mono h hsℓ hx)
      · rw [sqExt_of_ge h] at hx
        exact pow_le_alg _ _ hx
    rwa [hV.strictSteps_sqExt hsℓ hrmin] at this
  -- the arithmetic
  have hsumd : (List.ofFn d).sum = n := by rw [List.sum_ofFn]; exact hsum
  have hmemd : ∀ x ∈ List.ofFn d, ∃ j, d j = x := fun x hx => List.mem_ofFn.mp hx
  have hrecW : ((List.ofFn d).map recW).sum = ∑ j, recW (d j) := by
    rw [List.map_ofFn, List.sum_ofFn]; rfl
  have hNsum : ∑ j, Nj j + ∑ j, recW (d j) ≤ 10 * n := by
    rw [← Finset.sum_add_distrib]
    calc ∑ j, (Nj j + recW (d j)) ≤ ∑ j, 10 * d j := Finset.sum_le_sum fun j _ => hNj' j
      _ = 10 * n := by rw [← Finset.mul_sum]; exact congrArg _ hsum
  by_cases hbig : ∃ j, n < 2 * d j
  · obtain ⟨j0, hj0⟩ := hbig
    have hrec := recursion_big (List.ofFn d) n (d j0) hsumd
      (List.mem_ofFn.mpr ⟨j0, rfl⟩) (hdn j0) hj0
    rw [hrecW] at hrec
    set c := Nat.clog 2 (n - d j0)
    have htop : s + r + 2 + c ≤ ℓ → V (s + r + 2 + c) = ⊤ := by
      intro ht
      set X := V (s + r + 1)
      have hX1 : (1 : E →ₗ[ℂ] E) ∈ X := hV.one_mem _ (by omega)
      have hXstar : StarClosed X := hV.star_mem _ (by omega)
      have halgX : alg X = ⊤ := by
        refine top_le_iff.mp ?_
        rw [← hafter (s + 1) (by omega) (by omega)]
        exact alg_mono (hV.mono (by omega) (by omega))
      have hcorner : ∀ T : E →ₗ[ℂ] E, LinearMap.range T ≤ W j0 → (W j0)ᗮ ≤ LinearMap.ker T →
          T ∈ X := by
        intro T hT hT'
        have hTS := hS T (mem_of_corner S (W j0) (hsimple j0) hj0 T hT hT')
        rw [← hr] at hTS
        exact hV.le_succ (by omega) (hV.pow_two_pow_le (by omega) hTS)
      have hXtop := corner_pow_eq_top X hX1 hXstar halgX (W j0) (hsimple j0).1 (hdn j0) hcorner
      have hle : 2 * (n - d j0) ≤ 2 ^ (1 + c) := by
        rw [pow_add, pow_one]
        exact Nat.mul_le_mul_left 2 (Nat.le_pow_clog (by norm_num) _)
      refine top_le_iff.mp ?_
      calc ⊤ = X ^ (2 * (n - d j0)) := hXtop.symm
        _ ≤ X ^ (2 ^ (1 + c)) := pow_le_pow_of_one_mem hX1 hle
        _ ≤ V (s + r + 1 + (1 + c)) := hV.pow_two_pow_le (by omega)
        _ = V (s + r + 2 + c) := by congr 1; omega
    have := hV.strictSteps_le_of_top (s := s) htop
    unfold recW at hrec hNsum ⊢
    omega
  · push Not at hbig
    have hrec := recursion_small (List.ofFn d) n hn2 hsumd fun x hx => by
      obtain ⟨j, rfl⟩ := hmemd x hx; exact hbig j
    rw [hrecW] at hrec
    set c := Nat.clog 2 (n * n)
    have htop : s + 1 + c ≤ ℓ → V (s + 1 + c) = ⊤ := by
      intro ht
      set X := V (s + 1)
      have hX1 : (1 : E →ₗ[ℂ] E) ∈ X := hV.one_mem _ (by omega)
      have halgX : alg X = ⊤ := hafter (s + 1) (by omega) (by omega)
      have hXtop : X ^ (n * n) = ⊤ := by rw [← halgX]; exact pow_eq_alg X hX1 hfA.le
      refine top_le_iff.mp ?_
      calc ⊤ = X ^ (n * n) := hXtop.symm
        _ ≤ X ^ (2 ^ c) := pow_le_pow_of_one_mem hX1 (Nat.le_pow_clog (by norm_num) _)
        _ ≤ V (s + 1 + c) := hV.pow_two_pow_le (by omega)
    have := hV.strictSteps_le_of_top (s := s) htop
    unfold recW at hrec hNsum ⊢
    omega

end Step

/-- **Theorem 5.15** (with constant 10): for every finite-dimensional complex inner product
space `E` of dimension `n ≥ 1`, weak chains in `End E` have fewer than `N` strict steps for
some `N` with `N + 2 ⌈log₂ n⌉ + 9 ≤ 10 n`. -/
theorem chainBound_end : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E], finrank ℂ E = n → 1 ≤ n →
    ∃ N, ChainBound (E →ₗ[ℂ] E) N ∧ N + 2 * Nat.clog 2 n + 9 ≤ 10 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro E _ _ _ hn hn1
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · refine ⟨1, chainBound_one_of_span_eq_top ?_, by simp⟩
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton (one_ne_zero_end (E := E) (by omega)), finrank_end, hn]
  · refine ⟨10 * n - recW n, ?_, ?_⟩
    · subst hn
      exact chainBound_step hn2 fun F _ _ _ hF1 hFn => by
        obtain ⟨N, hN, hN'⟩ := IH _ hFn F rfl hF1
        exact ⟨N, hN, by unfold recW; omega⟩
    · have := clog_le_self n
      unfold recW; omega

/-- **Two-dimensional bound** for matrices (Theorem 5.15 with constant 10): every weak chain
in `M_n(ℂ)` has at most `10 n` strict steps. -/
theorem matrix_chainBound (n : ℕ) : ChainBound (Matrix (Fin n) (Fin n) ℂ) (10 * n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (chainBound_one_of_span_eq_top ?_).mono (by norm_num)
    exact Subsingleton.elim _ _
  · obtain ⟨N, hN, hN'⟩ := chainBound_end n (EuclideanSpace ℂ (Fin n)) finrank_euclideanSpace_fin hn
    refine (ChainBound.of_injective
      ((LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin n) ℂ)).symm :
        Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] _)
      (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin n) ℂ)).symm.injective hN).mono
      (by omega)

end Lax119563Proofs.Stabilization

end Stabilization_TwoDim

/-! ### Formerly `Lax119563Proofs.Stabilization.HigherDim` -/

section Stabilization_HigherDim

/-!
# Reducing to dimension two (Döring–Neuen §6.2)

For `k = m + 2`, if `k`-WL does not stabilize after any of the rounds `0, …, r - 1` on `G`
with `n` vertices, then `r ≤ 10 n` (`k = 2`) resp. `r ≤ 3 n^(k-2) + 10 n^(k-1)` (`k ≥ 3`).

Differences to the paper: the WL sequence is infinite, so Claim 6.6 holds for every round `r`
with `χ_r ≻ χ_{r+1}` (no boundary terms); we take `S = V^(k-2)` (all prefixes) instead of the
sorted prefixes, so Claim 6.7 is not needed; Claim 6.6 is proved without the partition of the
split class, directly from Claim 6.5.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.Stabilization

namespace Lax119563Proofs.Stabilization

/-! ### Counting strict steps of monotone sequences -/

theorem card_filter_add_le (a : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hmono : ∀ i, a i ≤ a (i + 1)) (hstrict : ∀ i, P i → a i < a (i + 1)) (L : ℕ) :
    ((Finset.range L).filter P).card + a 0 ≤ a L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · have := Finset.card_insert_le L ((Finset.range L).filter P)
      have := hstrict L h
      omega
    · have := hmono L
      omega

/-- Shifting a filter by `c`. -/
theorem card_filter_shift_le (P : ℕ → Prop) [DecidablePred P] (r c : ℕ) :
    ((Finset.range r).filter fun i => P (i + c)).card ≤
      ((Finset.range (r + c)).filter P).card := by
  rw [← Finset.card_map (addRightEmbedding c)]
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_range, addRightEmbedding_apply] at hj ⊢
  obtain ⟨i, ⟨hi, hP⟩, rfl⟩ := hj
  exact ⟨by omega, hP⟩

variable {G : ColoredGraph} {m : ℕ}

/-! ### The projections `χ^v` -/

/-- `χ^v_r ≻ χ^v_{r+1}`. -/
def ProjSplits (G : ColoredGraph) (r : ℕ) (v : Fin m → Fin G.n) : Prop :=
  ∃ a b c d, proj G r v a b = proj G r v c d ∧ proj G (r + 1) v a b ≠ proj G (r + 1) v c d

/-- The weak chain `ℂ 1, ⟨χ^v_0⟩, ⟨χ^v_1⟩, …`. -/
noncomputable def projChain (G : ColoredGraph) (v : Fin m → Fin G.n) :
    ℕ → Submodule ℂ (Matrix (Fin G.n) (Fin G.n) ℂ)
  | 0 => ℂ ∙ 1
  | r + 1 => classSpace (proj G r v)

theorem isChain_projChain (v : Fin m → Fin G.n) (ℓ : ℕ) : IsChain (projChain G v) ℓ where
  zero := rfl
  star_mem := by
    intro i _ x hx
    cases i with
    | zero =>
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      exact Submodule.mem_span_singleton.2 ⟨star c, by simp [star_smul]⟩
    | succ i => exact star_mem_classSpace_proj i v hx
  mul_le := by
    intro i _
    cases i with
    | zero =>
      rw [Submodule.mul_le]
      intro x hx y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [smul_mul_smul_comm, one_mul]
      exact Submodule.smul_mem _ _ (one_mem_classSpace_proj 0 v)
    | succ i => exact classSpace_proj_mul_le i v

/-- `|I^v| ≤ 10 n`, from the two-dimensional bound applied to the chain of `χ^v`. -/
theorem card_projSplits_le (v : Fin m → Fin G.n) (r : ℕ) [DecidablePred fun i => ProjSplits G i v] :
    ((Finset.range r).filter fun i => ProjSplits G i v).card ≤ 10 * G.n := by
  classical
  have hb := matrix_chainBound G.n (projChain G v) (r + 1) (isChain_projChain v _)
  have : ((Finset.range r).filter fun i => ProjSplits G i v).card ≤
      strictSteps (projChain G v) (r + 1) := by
    unfold strictSteps
    rw [← Finset.card_map (addRightEmbedding 1)]
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_range,
      addRightEmbedding_apply] at hj ⊢
    obtain ⟨i, ⟨hi, a, b, c, d, h1, h2⟩, rfl⟩ := hj
    refine ⟨by omega, fun heq => h2 (eq_of_classSpace_le ?_ h1)⟩
    change classSpace (proj G i v) = classSpace (proj G (i + 1) v) at heq
    exact heq.symm.le
  omega

/-! ### The coloring `χ̄` of `(k-2)`-tuples (`k = m + 3`) -/

/-- `χ̄_r (v) = χ_r (ext v)`, `ext v = (v, v_last, v_last)`. -/
noncomputable def barColor (G : ColoredGraph) (r : ℕ) (v : Fin (m + 1) → Fin G.n) :
    Color (m + 1 + 2) r :=
  proj G r v (v (Fin.last m)) (v (Fin.last m))

/-- The round-`r` part of a round-`(r+1)` color. -/
def colorFst {k r : ℕ} (c : Color k (r + 1)) : Color k r :=
  Prod.fst (α := Color k r) (β := Multiset (Fin k → Color k r)) c

/-- `χ̄_r ≻ χ̄_{r+1}`. -/
def BarSplits (G : ColoredGraph) (m r : ℕ) : Prop :=
  ∃ v w : Fin (m + 1) → Fin G.n,
    barColor G r v = barColor G r w ∧ barColor G (r + 1) v ≠ barColor G (r + 1) w

/-- `|Ī| ≤ n^(k-2)`: the number of classes of `χ̄_r` grows strictly at every split. -/
theorem card_barSplits_le (L : ℕ) [DecidablePred (BarSplits G m)] :
    ((Finset.range L).filter (BarSplits G m)).card ≤ G.n ^ (m + 1) := by
  classical
  let F : ℕ → ℕ := fun r =>
    ((Finset.univ : Finset (Fin (m + 1) → Fin G.n)).image (barColor G r)).card
  have himage : ∀ r, (Finset.univ : Finset (Fin (m + 1) → Fin G.n)).image (barColor G r) =
      ((Finset.univ : Finset (Fin (m + 1) → Fin G.n)).image (barColor G (r + 1))).image
        colorFst := by
    intro r
    rw [Finset.image_image]
    rfl
  have hmono : ∀ r, F r ≤ F (r + 1) := by
    intro r
    simp only [F]
    rw [himage r]
    exact Finset.card_image_le
  have hstrict : ∀ r, BarSplits G m r → F r < F (r + 1) := by
    intro r ⟨v, w, h1, h2⟩
    refine lt_of_le_of_ne (hmono r) fun heq => h2 ?_
    simp only [F] at heq
    rw [himage r] at heq
    have hinj := Finset.card_image_iff.1 heq
    exact hinj (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ v)))
      (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ w))) h1
  have h := card_filter_add_le F (BarSplits G m) hmono hstrict L
  have hF : F L ≤ G.n ^ (m + 1) := by
    simp only [F]
    refine Finset.card_image_le.trans ?_
    simp
  omega

/-! ### Claims 6.5 and 6.6 -/

/-- **Claim 6.5.** -/
theorem barColor_ne {r : ℕ} {v w : Fin (m + 1) → Fin G.n} {a b : Fin G.n}
    (h : ∀ x y, proj G r v a b ≠ proj G r w x y) :
    barColor G (r + 2) v ≠ barColor G (r + 2) w := by
  -- (14)
  have h14 := proj_succ_diag_ne h
  -- (15)
  have h15 : ∀ y, proj G (r + 1) v (v (Fin.last m)) a ≠ proj G (r + 1) w (w (Fin.last m)) y := by
    intro y hy
    have := proj_shuffle hy (Fin.last (m + 1 + 1)) (Fin.last (m + 1 + 1))
    simp only [tup_last] at this
    exact h14 y this
  -- (16)
  have h16 : ∀ x y, proj G (r + 1) v (v (Fin.last m)) a ≠ proj G (r + 1) w x y := by
    intro x y hxy
    have := eq_iff_of_color_eq hxy (vIdx (m + 1) (Fin.last m)) (penIdx (m + 1))
    simp only [tup_vIdx, tup_pen, true_iff] at this
    rw [← this] at hxy
    exact h15 y hxy
  exact proj_succ_diag_ne h16 (w (Fin.last m))

/-- A failure of stability is a pair of tuples `(v, a, b)`, `(w, c, d)` split by round
`r + 1`. -/
theorem exists_split {r : ℕ} (hs : ¬ StabilizesAfter (m + 2) r G) :
    ∃ (v w : Fin m → Fin G.n) (a b c d : Fin G.n),
      proj G r v a b = proj G r w c d ∧ proj G (r + 1) v a b ≠ proj G (r + 1) w c d := by
  simp only [StabilizesAfter, not_forall] at hs
  obtain ⟨p, q, hpq⟩ := hs
  have h : color G r p = color G r q ∧ color G (r + 1) p ≠ color G (r + 1) q := by
    by_cases h1 : color G r p = color G r q
    · exact ⟨h1, fun h2 => hpq ⟨fun _ => h2, fun _ => h1⟩⟩
    · exact absurd (Iff.intro (fun h => absurd h h1) fun h2 => color_eq_of_succ h2) hpq
  refine ⟨p ∘ vIdx m, q ∘ vIdx m, p (penIdx m), p (Fin.last (m + 1)), q (penIdx m),
    q (Fin.last (m + 1)), ?_, ?_⟩
  · unfold proj; rw [tup_eta, tup_eta]; exact h.1
  · unfold proj; rw [tup_eta, tup_eta]; exact h.2

/-- **Claim 6.6**: if `χ_r ≻ χ_{r+1}` but no `χ^v` splits in round `r + 1`, then `χ̄` splits
in one of the rounds `r + 1, r + 2, r + 3`. -/
theorem barSplits_of_not_projSplits {r : ℕ} (hs : ¬ StabilizesAfter (m + 1 + 2) r G)
    (hv : ∀ v : Fin (m + 1) → Fin G.n, ¬ ProjSplits G r v) :
    BarSplits G m r ∨ BarSplits G m (r + 1) ∨ BarSplits G m (r + 2) := by
  obtain ⟨v, w, a, b, c, d, h1, h2⟩ := exists_split hs
  have h0 : barColor G r v = barColor G r w := by
    have := proj_shuffle h1 (vIdx (m + 1) (Fin.last m)) (vIdx (m + 1) (Fin.last m))
    simpa only [tup_vIdx, barColor] using this
  have h3 : barColor G (r + 1 + 2) v ≠ barColor G (r + 1 + 2) w := by
    refine barColor_ne (a := a) (b := b) fun x y hxy => h2 ?_
    have e1 : proj G r w c d = proj G r w x y := h1.symm.trans (proj_eq_of_succ hxy)
    have e2 : proj G (r + 1) w c d = proj G (r + 1) w x y := by
      by_contra hne
      exact hv w ⟨c, d, x, y, e1, hne⟩
    exact hxy.trans e2.symm
  simp only [BarSplits]
  by_contra hc
  simp only [not_or, not_exists, not_and, not_not] at hc
  obtain ⟨n0, n1, n2⟩ := hc
  exact h3 (n2 v w (n1 v w (n0 v w h0)))

/-! ### The count -/

/-- `k = 2`: `r ≤ 10 n`. -/
theorem rounds_le_two {r : ℕ} (hr : ∀ i < r, ¬ StabilizesAfter 2 i G) : r ≤ 10 * G.n := by
  classical
  have hsub : Finset.range r ⊆
      (Finset.range r).filter fun i => ProjSplits G i (Fin.elim0 : Fin 0 → Fin G.n) := by
    intro i hi
    obtain ⟨v, w, a, b, c, d, h1, h2⟩ := exists_split (m := 0) (hr i (Finset.mem_range.1 hi))
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst hv hw
    exact Finset.mem_filter.2 ⟨hi, a, b, c, d, h1, h2⟩
  have := (Finset.card_le_card hsub).trans (card_projSplits_le _ r)
  simpa using this

/-- `k = m + 3`: `r ≤ 3 n^(k-2) + 10 n^(k-1)`
(`r ≤ |{rounds where some χ^v splits}| + 3 |Ī|`). -/
theorem rounds_le {r : ℕ} (hr : ∀ i < r, ¬ StabilizesAfter (m + 1 + 2) i G) :
    r ≤ 3 * G.n ^ (m + 1) + 10 * G.n ^ (m + 2) := by
  classical
  set S := Finset.range r
  let A := S.filter fun i => ∃ v : Fin (m + 1) → Fin G.n, ProjSplits G i v
  let B : ℕ → Finset ℕ := fun c => S.filter fun i => BarSplits G m (i + c)
  have hcover : S ⊆ A ∪ (B 0 ∪ B 1 ∪ B 2) := by
    intro i hi
    by_cases hv : ∃ v : Fin (m + 1) → Fin G.n, ProjSplits G i v
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hi, hv⟩)
    · simp only [not_exists] at hv
      have := barSplits_of_not_projSplits (hr i (Finset.mem_range.1 hi)) hv
      simp only [Finset.mem_union, B, Finset.mem_filter, add_zero]
      tauto
  have hA : A.card ≤ G.n ^ (m + 1) * (10 * G.n) := by
    have hsub : A ⊆ (Finset.univ : Finset (Fin (m + 1) → Fin G.n)).biUnion
        fun v => S.filter fun i => ProjSplits G i v := by
      intro i hi
      obtain ⟨hi, v, hv⟩ := Finset.mem_filter.1 hi
      exact Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _, Finset.mem_filter.2 ⟨hi, hv⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    refine (Finset.sum_le_sum fun v _ => card_projSplits_le v r).trans ?_
    simp
  have hB : ∀ c, (B c).card ≤ G.n ^ (m + 1) := fun c =>
    (card_filter_shift_le (BarSplits G m) r c).trans (card_barSplits_le _)
  have hS : S.card ≤ A.card + ((B 0).card + (B 1).card + (B 2).card) := by
    refine (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans ?_)
    have := Finset.card_union_le (B 0 ∪ B 1) (B 2)
    have := Finset.card_union_le (B 0) (B 1)
    omega
  have h0 := hB 0
  have h1 := hB 1
  have h2 := hB 2
  have hpow : G.n ^ (m + 1) * (10 * G.n) = 10 * G.n ^ (m + 2) := by ring
  simp only [S, Finset.card_range] at hS
  omega

end Lax119563Proofs.Stabilization

end Stabilization_HigherDim
