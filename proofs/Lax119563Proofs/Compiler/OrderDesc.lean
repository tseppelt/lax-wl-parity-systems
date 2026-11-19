import Lax119563Proofs.Compiler.OrderEdges

/-!
# The description of the reordered graphs, numerically

The output of the compiler machine, as lists that a sequential program can emit.

* `ordCls I`: the classes of `ordL I` in order, each with its list of labels; `ordL I` is the
  concatenation of the blocks `labs.map (X, ·)` (`ordL_eq_flatMap`).
* **Colors** (`colors_reGraph`): the color list of `reGraph I (ordL I) ε` is `colorsOf 0` of
  the block sizes: each class contributes its start position, repeated once per label.
* **Edges** (`edgeList_nbrPos`): for each position `u`, the edges `(u, v)`, `v` in
  `nbrPos ε L[u]`, the sorted positions of the names prescribed by the (at most three)
  neighbor slots `slotsOf` (class, required effective bit) of the hub; `posOpt` gives the
  position of the slot's name if present.
* **Positions** (`idxOf_ordL`): the name `(X, l)` sits at `clsStart X + ls.idxOf l`;
  `posOpt_bits1` (two-name classes: `clsStart Y + (b - ε·initBit Y)`), `posOpt_single`
  (initialized coordinate classes: present iff `b = ε·initBit Y`).
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

/-! ## Edges: neighbor slots of the hubs -/

/-- The neighbor slots of a hub class with (effective) label `l`: the neighbor class and the
first effective label bit required there. -/
def slotsOf : ICls I → Lab → List (ICls I × ZMod 2)
  | .upd e σ c, l => [(trackAt I e c σ, l.1), (.track e σ c, l.2), (.coef e σ, l.1 + l.2)]
  | .junc e c, l => [(coordU e c, l.1), (coordV e c, l.2), (.sum e c, l.1 + l.2)]
  | .link e c, l => [(trackAt I e c (numSteps k ℓ), l.1), (endCls I e c, l.1)]
  | _, _ => []

lemma hubB_iff_slotsOf (X Y : ICls I) (l m : Lab) :
    hubB I X l Y m = true ↔ (Y, m.1) ∈ slotsOf I X l := by
  cases X with
  | upd e σ c => rw [hubB_upd]; simp [slotsOf, Prod.ext_iff]
  | junc e c => rw [hubB_junc']; simp [slotsOf, Prod.ext_iff]
  | link e c => rw [hubB_link]; simp [slotsOf, Prod.ext_iff]
  | coord => simp [hubB, slotsOf]
  | sum => simp [hubB, slotsOf]
  | track => simp [hubB, slotsOf]
  | coef => simp [hubB, slotsOf]

/-- The classes of the slots of a hub in the order are distinct. -/
lemma nodup_slotsOf {x : VName I} (hx : x ∈ ordL I) :
    ((slotsOf I x.1 x.2).map Prod.fst).Nodup := by
  obtain ⟨X, l⟩ := x
  have hv := (mem_ordL I _).mp hx
  cases X with
  | upd e σ c =>
    simp only [slotsOf, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨trackAt_ne_track e c σ, trackAt_ne_coef e c σ σ⟩, by simp⟩
  | junc e c =>
    have ht : isTern (sch I e) = true := hv.1.1
    simp only [slotsOf, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨coordU_ne_coordV ht c, by simp [coordU]⟩, by simp [coordV]⟩
  | link e c =>
    simp only [slotsOf, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨trackAt_ne_endCls e c _, by simp⟩
  | coord => simp [slotsOf]
  | sum => simp [slotsOf]
  | track => simp [slotsOf]
  | coef => simp [slotsOf]

variable (ε : ZMod 2)

/-- The label of the name of class `Y` whose first effective bit in `G_ε` is `b`. -/
def labOf (Y : ICls I) (b : ZMod 2) : Lab := (b - ε * initBit I Y, 0)

open Classical in
/-- The position of the name of class `Y` with first effective bit `b`, if present. -/
noncomputable def posOpt (Y : ICls I) (b : ZMod 2) : Option ℕ :=
  if (Y, labOf I ε Y b) ∈ ordL I then some ((ordL I).idxOf (Y, labOf I ε Y b)) else none

/-- A non-hub name of the order is the one prescribed by its class and effective bit. -/
lemma eq_labOf {y : VName I} (hy : y ∈ ordL I) (hh : isHub I y.1 = false) :
    y = (y.1, labOf I ε y.1 (eff I ε y).1) := by
  obtain ⟨Y, m⟩ := y
  have h2 : m.2 = 0 := ((mem_ordL I _).mp hy).2.1 (twoBit_of_not_hub hh)
  ext <;> simp [labOf, eff, h2]

/-- The sorted positions of the neighbors of the name `x`. -/
noncomputable def nbrPos (x : VName I) : List ℕ :=
  ((slotsOf I x.1 (eff I ε x)).filterMap fun s => posOpt I ε s.1 s.2).mergeSort
    fun a b => decide (a ≤ b)

lemma eff_hub {x : VName I} (h : isHub I x.1 = true) : eff I ε x = x.2 := by
  obtain ⟨X, l⟩ := x
  cases X <;> simp_all [isHub, eff, initBit]

/-- The neighbor positions of a name of the order. -/
theorem filter_hubB_eq_nbrPos' (x : VName I) (hxL : x ∈ ordL I) :
    ((List.finRange (ordL I).length).filter (fun v : Fin (ordL I).length =>
        hubB I x.1 (eff I ε x) (ordL I)[(v : ℕ)].1 (eff I ε (ordL I)[(v : ℕ)]))).map Fin.val =
      nbrPos I ε x := by
  have hnd : (ordL I).Nodup := nodup_ordL I
  -- membership
  have hmem : ∀ v : ℕ, v ∈ ((List.finRange (ordL I).length).filter (fun v : Fin (ordL I).length =>
        hubB I x.1 (eff I ε x) (ordL I)[(v : ℕ)].1 (eff I ε (ordL I)[(v : ℕ)]))).map Fin.val ↔
      v ∈ nbrPos I ε x := by
    intro v
    simp only [nbrPos, List.mem_mergeSort, List.mem_filterMap, List.mem_map, List.mem_filter,
      List.mem_finRange, true_and]
    constructor
    · rintro ⟨v', hv', rfl⟩
      have hs := (hubB_iff_slotsOf I _ _ _ _).mp hv'
      have hnh := (hubB_hub I hv').2
      have hy : (ordL I)[(v' : ℕ)] ∈ ordL I := List.getElem_mem _
      refine ⟨_, hs, ?_⟩
      have he := eq_labOf I ε hy hnh
      simp only [posOpt]
      rw [← he, if_pos hy, hnd.idxOf_getElem]
    · rintro ⟨s, hs, hp⟩
      simp only [posOpt] at hp
      split_ifs at hp with hin
      cases hp
      refine ⟨⟨_, List.idxOf_lt_length_of_mem hin⟩, ?_, rfl⟩
      simp only [List.getElem_idxOf]
      rw [hubB_iff_slotsOf]
      convert hs using 2
      simp [eff, labOf]
  -- both sides are sorted and duplicate-free
  have hs₁ : (((List.finRange (ordL I).length).filter (fun v : Fin (ordL I).length =>
        hubB I x.1 (eff I ε x) (ordL I)[(v : ℕ)].1 (eff I ε (ordL I)[(v : ℕ)]))).map
          Fin.val).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact (List.pairwise_lt_finRange _).filter _
  have hs₂ : (nbrPos I ε x).Pairwise (· ≤ ·) := by
    have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c h₁ h₂ => by simp at *; omega) (fun a b => by simp; omega)
      ((slotsOf I x.1 (eff I ε x)).filterMap fun s => posOpt I ε s.1 s.2)
    simpa [nbrPos] using this
  have hnd₂ : (nbrPos I ε x).Nodup := by
    refine (List.mergeSort_perm _ _).nodup_iff.mpr ?_
    have hslots := nodup_slotsOf I hxL
    rw [show slotsOf I x.1 (eff I ε x) = slotsOf I x.1 x.2 by
      by_cases hh : isHub I x.1 = true
      · rw [eff_hub I ε hh]
      · cases hX : x.1 <;> simp_all [isHub, slotsOf]]
    refine List.Nodup.filterMap ?_ (List.Nodup.of_map _ hslots)
    intro s s' a ha ha'
    have key : ∀ t : ICls I × ZMod 2, a ∈ posOpt I ε t.1 t.2 →
        (t.1, labOf I ε t.1 t.2) ∈ ordL I ∧ (ordL I).idxOf (t.1, labOf I ε t.1 t.2) = a := by
      intro t ht
      unfold posOpt at ht
      split_ifs at ht with h
      · simp only [Option.mem_def, Option.some.injEq] at ht; exact ⟨h, ht⟩
      · simp at ht
    obtain ⟨h₁, e₁⟩ := key s ha
    obtain ⟨h₂, e₂⟩ := key s' ha'
    have := (List.idxOf_inj h₁).mp (e₁.trans e₂.symm)
    obtain ⟨hY, hb⟩ := Prod.mk.inj this
    simp only [labOf, Prod.mk.injEq] at hb
    rw [hY] at hb
    exact Prod.ext hY (sub_left_inj.mp hb.1)
  exact List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h1 h2) (hs₁.imp le_of_lt) hs₂
    ((List.perm_ext_iff_of_nodup (hs₁.imp ne_of_lt) hnd₂).mpr hmem)

/-- **The edge list of the reordered graphs, per hub.** For every position `u`, the edges
`(u, v)` with `v` in the sorted neighbor positions `nbrPos` of the name at `u` (empty for
non-hubs; at most three slots `slotsOf`, each giving the position of the name of the slot
class with the required effective bit, `posOpt`). -/
theorem edgeList_nbrPos :
    edgeList (reGraph I (ordL I) ε) =
      (List.finRange (ordL I).length).flatMap fun u : Fin (ordL I).length =>
        (nbrPos I ε (ordL I)[(u : ℕ)]).map fun v => ((u : ℕ), v) := by
  rw [edgeList_ordL]
  refine List.flatMap_congr fun u _ => ?_
  rw [← filter_hubB_eq_nbrPos' I ε _ (List.getElem_mem _), List.map_map]
  rfl

/-! ## Positions of names: class starts and label offsets -/

section Starts

variable {β γ : Type*} [DecidableEq β] [BEq γ] [LawfulBEq γ]

/-- The start position of the class `X` in a list of classes with labels. -/
def startIn (P : List (β × List γ)) (X : β) : ℕ :=
  ((P.takeWhile fun p => p.1 ≠ X).map fun p => p.2.length).sum

lemma idxOf_map_pair (X : β) (l : γ) : ∀ ls : List γ,
    (ls.map fun m => (X, m)).idxOf (X, l) = ls.idxOf l
  | [] => rfl
  | m :: ls => by
    by_cases h : m = l
    · subst h; simp
    · rw [List.map_cons, List.idxOf_cons_ne _ (by simp [h]), List.idxOf_cons_ne _ h,
        idxOf_map_pair X l ls]

/-- **Positions in a list of class blocks.** -/
theorem idxOf_flatMap_blocks : ∀ (P : List (β × List γ)), (P.map Prod.fst).Nodup →
    ∀ (X : β) (ls : List γ) (l : γ), (X, ls) ∈ P → l ∈ ls →
      (P.flatMap fun p => p.2.map fun m => (p.1, m)).idxOf (X, l) = startIn P X + ls.idxOf l
  | [], _, _, _, _, h, _ => by simp at h
  | (Y, ms) :: P, hnd, X, ls, l, hX, hl => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rw [List.flatMap_cons]
    by_cases hY : Y = X
    · subst hY
      have hls : ms = ls := by
        rcases List.mem_cons.mp hX with h | h
        · exact (Prod.mk.inj h).2.symm
        · exact absurd ⟨_, h, rfl⟩ hnd.1
      subst hls
      rw [List.idxOf_append_of_mem (List.mem_map.mpr ⟨l, hl, rfl⟩), idxOf_map_pair]
      simp [startIn]
    · have hX' : (X, ls) ∈ P := by
        rcases List.mem_cons.mp hX with h | h
        · exact absurd (Prod.mk.inj h).1.symm hY
        · exact h
      rw [List.idxOf_append_of_notMem (by simp [hY]),
        idxOf_flatMap_blocks P hnd.2 X ls l hX' hl]
      simp [startIn, hY]
      omega

end Starts

lemma nodup_ordCls_fst : ((ordCls I).map Prod.fst).Nodup := by
  have h := ordBlocks_pairwise I
  unfold ordBlocks at h
  rw [List.pairwise_map] at h
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ h
  intro p p' hp hp' hd heq
  exact hd _ (List.mem_map.mpr ⟨_, mem_labs_zero I hp, rfl⟩) _
    (List.mem_map.mpr ⟨_, mem_labs_zero I hp', rfl⟩) (by simpa using heq)

/-- The start position of a class in the order. -/
noncomputable def clsStart (X : ICls I) : ℕ := startIn (ordCls I) X

/-- **Positions of names.** The name `(X, l)` of a class `X` with labels `ls` in `ordCls I`
sits at `clsStart X + ls.idxOf l`. -/
theorem idxOf_ordL {X : ICls I} {ls : List Lab} (hX : (X, ls) ∈ ordCls I) {l : Lab}
    (hl : l ∈ ls) : (ordL I).idxOf (X, l) = clsStart I X + ls.idxOf l := by
  rw [ordL_eq_flatMap]
  exact idxOf_flatMap_blocks (ordCls I) (nodup_ordCls_fst I) X ls l hX hl

/-- The names of a class of `ordCls I` in the order are those with its labels. -/
lemma mem_ordL_iff_of_mem {X : ICls I} {ls : List Lab} (hX : (X, ls) ∈ ordCls I) (l : Lab) :
    (X, l) ∈ ordL I ↔ l ∈ ls := by
  rw [ordL_eq_flatMap, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hl⟩
    obtain ⟨m, hm, he⟩ := List.mem_map.mp hl
    obtain ⟨h1, rfl⟩ := Prod.mk.inj he
    have : p = (X, ls) := List.inj_on_of_nodup_map (nodup_ordCls_fst I) hp hX h1
    subst this; exact hm
  · intro hl; exact ⟨_, hX, List.mem_map.mpr ⟨l, hl, rfl⟩⟩

/-- **Slot positions.** For a class `Y` of `ordCls I` with labels `ls`, the slot `(Y, b)`
gives the name with label `labOf Y b` if that label is present. -/
theorem posOpt_of_mem {Y : ICls I} {ls : List Lab} (hY : (Y, ls) ∈ ordCls I) (b : ZMod 2) :
    posOpt I ε Y b =
      if labOf I ε Y b ∈ ls then some (clsStart I Y + ls.idxOf (labOf I ε Y b)) else none := by
  unfold posOpt
  by_cases h : labOf I ε Y b ∈ ls
  · rw [if_pos ((mem_ordL_iff_of_mem I hY _).mpr h), if_pos h, idxOf_ordL I hY h]
  · rw [if_neg (fun h' => h ((mem_ordL_iff_of_mem I hY _).mp h')), if_neg h]

lemma idxOf_bits1 (a : ZMod 2) : bits1.idxOf (a, (0 : ZMod 2)) = a.val := by
  fin_cases a <;> decide

/-- Slots of a two-name class (labels `bits1`): always present, offset the required label. -/
theorem posOpt_bits1 {Y : ICls I} (hY : (Y, bits1) ∈ ordCls I) (b : ZMod 2) :
    posOpt I ε Y b = some (clsStart I Y + (b - ε * initBit I Y).val) := by
  rw [posOpt_of_mem I ε hY, if_pos (by simp [labOf]), labOf, idxOf_bits1]

/-- Slots of a singleton class (an initialized coordinate class): present iff the required
bit is the effective label of its single name. -/
theorem posOpt_single {Y : ICls I} (hY : (Y, [((0 : ZMod 2), (0 : ZMod 2))]) ∈ ordCls I)
    (b : ZMod 2) :
    posOpt I ε Y b = if b = ε * initBit I Y then some (clsStart I Y) else none := by
  rw [posOpt_of_mem I ε hY]
  by_cases h : b = ε * initBit I Y
  · rw [if_pos (by simp [labOf, h]), if_pos h]; simp [labOf, h]
  · rw [if_neg (by simp [labOf, sub_eq_zero, h]), if_neg h]

end Lax119563Proofs.Compiler
