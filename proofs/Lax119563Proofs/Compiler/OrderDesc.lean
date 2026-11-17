import Lax119563Proofs.Compiler.OrderEdges

/-!
# The description of the reordered graphs, numerically

The output of the compiler machine, as lists that a sequential program can emit.

* `ordCls I`: the classes of `ordL I` in order, each with its list of labels; `ordL I` is the
  concatenation of the blocks `labs.map (X, ·)` (`ordL_eq_flatMap`).
* **Colors** (`colors_reGraph`): the color list of `reGraph I (ordL I) ε` is `colorsOf 0` of
  the block sizes: each class contributes its start position, repeated once per label.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Colors of block lists -/

/-- Start positions repeated per block: blocks of sizes `ns` starting at `s`. -/
def colorsOf : ℕ → List ℕ → List ℕ
  | _, [] => []
  | s, n :: ns => List.replicate n s ++ colorsOf (s + n) ns

section Generic

variable {α β : Type*} [DecidableEq β] (cls : α → β)

lemma map_findIdx_blocks (blocks : List (List α))
    (hne : ∀ b ∈ blocks, b ≠ [])
    (hcls : ∀ b ∈ blocks, ∀ x ∈ b, ∀ y ∈ b, cls x = cls y)
    (hdis : blocks.Pairwise fun b b' => ∀ x ∈ b, ∀ y ∈ b', cls x ≠ cls y) :
    ∀ (pre : List α), (∀ x ∈ pre, ∀ b ∈ blocks, ∀ y ∈ b, cls x ≠ cls y) →
      blocks.flatten.map (fun y => (pre ++ blocks.flatten).findIdx
        fun x => decide (cls x = cls y)) = colorsOf pre.length (blocks.map List.length) := by
  induction blocks with
  | nil => intro _ _; rfl
  | cons b bs ih =>
    intro pre hpre
    simp only [List.flatten_cons, List.map_append, List.map_cons, colorsOf]
    obtain ⟨z, b', rfl⟩ : ∃ z b', b = z :: b' := by
      cases b with
      | nil => exact absurd rfl (hne _ List.mem_cons_self)
      | cons z b' => exact ⟨z, b', rfl⟩
    congr 1
    · apply List.eq_replicate_iff.mpr
      refine ⟨by simp, fun n hn => ?_⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hn
      rw [List.findIdx_append]
      have h1 : pre.findIdx (fun x => decide (cls x = cls y)) = pre.length :=
        List.findIdx_eq_length.mpr fun x hx => by
          simpa using hpre x hx _ List.mem_cons_self y hy
      rw [h1, if_neg (lt_irrefl _), List.cons_append, List.findIdx_cons]
      have : cls z = cls y := hcls _ List.mem_cons_self z List.mem_cons_self y hy
      simp [this]
    · have hih := ih (fun b hb => hne b (List.mem_cons_of_mem _ hb))
        (fun b hb => hcls b (List.mem_cons_of_mem _ hb)) (List.pairwise_cons.mp hdis).2
        (pre ++ z :: b') (by
          intro x hx b'' hb'' y hy
          rcases List.mem_append.mp hx with hx | hx
          · exact hpre x hx b'' (List.mem_cons_of_mem _ hb'') y hy
          · exact (List.pairwise_cons.mp hdis).1 b'' hb'' x hx y hy)
      rw [List.append_assoc] at hih
      rw [hih, List.length_append]

/-- **Colors of a list of class blocks.** -/
theorem colors_blocks (blocks : List (List α))
    (hne : ∀ b ∈ blocks, b ≠ [])
    (hcls : ∀ b ∈ blocks, ∀ x ∈ b, ∀ y ∈ b, cls x = cls y)
    (hdis : blocks.Pairwise fun b b' => ∀ x ∈ b, ∀ y ∈ b', cls x ≠ cls y) :
    (List.finRange blocks.flatten.length).map (fun i : Fin blocks.flatten.length =>
        blocks.flatten.findIdx fun x => decide (cls x = cls (blocks.flatten[(i : ℕ)]'i.2))) =
      colorsOf 0 (blocks.map List.length) := by
  have h := map_findIdx_blocks cls blocks hne hcls hdis [] (by simp)
  simp only [List.nil_append, List.length_nil] at h
  rw [← h]
  set L := blocks.flatten
  rw [show (fun i : Fin L.length => L.findIdx fun x => decide (cls x = cls (L[(i : ℕ)]'i.2))) =
      (fun y => L.findIdx fun x => decide (cls x = cls y)) ∘ L.get from rfl, ← List.map_map,
    List.map_get_finRange]

end Generic

/-! ## The classes of the order -/

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The block of names of a class with a list of labels. -/
def blk (p : ICls I × List Lab) : List (VName I) := p.2.map fun l => (p.1, l)

/-- The classes of the hubs of schema `e`, with their labels. -/
def hubsCls (e : Fin I.schemas.length) : List (ICls I × List Lab) :=
  (coordList (dom I e)).flatMap (fun c =>
      (if isTern (sch I e) then [(Cls.junc e c, bits2)] else []) ++ [(Cls.link e c, bits1)]) ++
    (coordList (dom I e)).flatMap fun c => (stepsC c).map fun σ => (Cls.upd e σ c, bits2)

/-- The classes of the non-hubs of schema `e`, with their labels. -/
noncomputable def nonhubsCls (e : Fin I.schemas.length) : List (ICls I × List Lab) :=
  (coordList (dom I e)).flatMap (fun c =>
      if isTern (sch I e) then [(Cls.sum e c, bits1)] else []) ++
    (coordList (dom I e)).flatMap (fun c => (stepsC c).map fun σ => (Cls.track e σ c, bits1)) ++
    (coefSteps I e).map fun σ => (Cls.coef e σ, bits1)

/-- The labels of the coordinate classes of location `v`. -/
def coordLabs (v : Fin I.numLocations) : List Lab :=
  if (I.init v).isSome then [((0 : ZMod 2), (0 : ZMod 2))] else bits1

/-- The classes of the order, with their labels. -/
noncomputable def ordCls : List (ICls I × List Lab) :=
  (List.finRange I.schemas.length).flatMap (fun e => hubsCls I e ++ nonhubsCls I e) ++
    (List.finRange I.numLocations).flatMap fun v =>
      (coordList (I.domain v)).map fun c => (Cls.coord v c, coordLabs I v)

lemma hubsE_eq (e : Fin I.schemas.length) : hubsE I e = (hubsCls I e).flatMap (blk I) := by
  simp only [hubsE, hubsCls, List.flatMap_append, List.flatMap_assoc]
  congr 1
  · refine List.flatMap_congr fun c _ => ?_
    split <;> simp [blk]
  · refine List.flatMap_congr fun c _ => ?_
    simp [blk, List.flatMap_map]

lemma nonhubsE_eq (e : Fin I.schemas.length) :
    nonhubsE I e = (nonhubsCls I e).flatMap (blk I) := by
  simp only [nonhubsE, nonhubsCls, List.flatMap_append, List.flatMap_assoc]
  congr 1
  · congr 1
    · refine List.flatMap_congr fun c _ => ?_
      split <;> simp [blk]
    · refine List.flatMap_congr fun c _ => ?_
      simp [blk, List.flatMap_map]
  · simp [blk, List.flatMap_map]

/-- **The order as blocks of classes.** -/
theorem ordL_eq_flatMap : ordL I = (ordCls I).flatMap (blk I) := by
  simp only [ordL, ordCls, List.flatMap_append, List.flatMap_assoc]
  congr 1
  · refine List.flatMap_congr fun e _ => ?_
    rw [hubsE_eq, nonhubsE_eq]
  · refine List.flatMap_congr fun v _ => ?_
    simp [coordVerts, coordLabs, blk, List.flatMap_map]

lemma mem_labs_zero {p : ICls I × List Lab} (hp : p ∈ ordCls I) :
    ((0 : ZMod 2), (0 : ZMod 2)) ∈ p.2 := by
  have h1 : ((0 : ZMod 2), (0 : ZMod 2)) ∈ bits1 := by simp
  have h2 : ((0 : ZMod 2), (0 : ZMod 2)) ∈ bits2 := by simp
  simp only [ordCls, hubsCls, nonhubsCls, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and] at hp
  rcases hp with ⟨e, (⟨c, -, hp⟩ | ⟨c, -, σ, -, rfl⟩) | (⟨c, -, hp⟩ | ⟨c, -, σ, -, rfl⟩) |
      ⟨σ, -, rfl⟩⟩ | ⟨v, c, -, rfl⟩
  · rcases hp with hp | hp
    · split at hp
      · simp only [List.mem_singleton] at hp; subst hp; exact h2
      · simp at hp
    · simp only [List.mem_singleton] at hp; subst hp; exact h1
  · exact h2
  · split at hp
    · simp only [List.mem_singleton] at hp; subst hp; exact h1
    · simp at hp
  · exact h1
  · exact h1
  · simp only [coordLabs]; split
    · simp
    · exact h1

/-- The blocks of the order. -/
noncomputable def ordBlocks : List (List (VName I)) := (ordCls I).map (blk I)

lemma ordL_eq_flatten : ordL I = (ordBlocks I).flatten := by
  rw [ordL_eq_flatMap, ordBlocks, List.flatMap_def]

lemma ordBlocks_pairwise :
    (ordBlocks I).Pairwise fun b b' => ∀ x ∈ b, ∀ y ∈ b', x.1 ≠ y.1 := by
  have hnd := nodup_ordL I
  rw [ordL_eq_flatten] at hnd
  have hdis := (List.nodup_flatten.mp hnd).2
  unfold ordBlocks at hdis ⊢
  rw [List.pairwise_map] at hdis ⊢
  refine List.Pairwise.imp_of_mem ?_ hdis
  intro p p' hp hp' hd x hx y hy hxy
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
  obtain ⟨l', -, rfl⟩ := List.mem_map.mp hy
  simp only at hxy
  have h0 : (p.1, ((0 : ZMod 2), (0 : ZMod 2))) ∈ blk I p :=
    List.mem_map.mpr ⟨_, mem_labs_zero I hp, rfl⟩
  have h0' : (p.1, ((0 : ZMod 2), (0 : ZMod 2))) ∈ blk I p' := by
    rw [hxy]; exact List.mem_map.mpr ⟨_, mem_labs_zero I hp', rfl⟩
  exact hd h0 h0'

/-- **The colors of the reordered graphs.** Each class of `ordCls I` contributes its start
position, repeated once per label. -/
theorem colors_reGraph (ε : ZMod 2) :
    (List.finRange (reGraph I (ordL I) ε).n).map (reGraph I (ordL I) ε).color =
      colorsOf 0 ((ordCls I).map fun p => p.2.length) := by
  have h := colors_blocks (fun x : VName I => x.1) (ordBlocks I)
    (fun b hb => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
      intro h; have := mem_labs_zero I hp
      simp [blk] at h; rw [h] at this; simp at this)
    (fun b hb x hx y hy => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hb
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
      obtain ⟨l', -, rfl⟩ := List.mem_map.mp hy
      rfl)
    (ordBlocks_pairwise I)
  have e1 : (ordBlocks I).map List.length = (ordCls I).map fun p => p.2.length := by
    simp [ordBlocks, blk, Function.comp_def]
  rw [← e1, ← h]
  have e2 := ordL_eq_flatten I
  simp only [listGraph_n]
  revert e2
  generalize ordL I = L
  rintro rfl
  simp only [Fin.getElem_fin]

end Lax119563Proofs.Compiler
