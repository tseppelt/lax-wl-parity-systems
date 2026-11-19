import Lax119563Proofs.Compiler.Clauses

/-!
# The vertex order of the compiler machine

`ordL I` lists the vertex names in the order in which the machine numbers them:
first, for each schema `e` (in list order), its *hubs* and then its *non-hubs*; finally, for
each location `v` (in order), its coordinate vertices (`coordVerts I v`). With
`D = coordList (dom I e)` (increasing coordinate numbers, as in the input):

* `hubsE e`: for `c ∈ D`: `junc e c` (labels `bits2`, ternary only), `link e c` (`bits1`);
  then for `c ∈ D` and its steps `σ ∈ stepsC c`: `upd e σ c` (`bits2`);
* `nonhubsE e`: for `c ∈ D`: `sum e c` (`bits1`, ternary only); for `c ∈ D`, `σ ∈ stepsC c`:
  `track e σ c` (`bits1`); then `coef e σ` (`bits1`) for `σ ∈ coefSteps e`.

`stepsC c` are the steps `σ < N` with `ent σ c ≠ 0` in increasing order; since `σ = q M + j`
(row `j = σ % M`, repetition `q = σ / M`), this is the *q-major* order of the entries `(q, j)`,
`q ≤ k`, `j` a nonzero row of column `c`. Likewise `coefSteps e` are the steps whose row is
nonzero on `𝔠_e`, in increasing (q-major) order, so `coef e (q M + j)` has index
`q |R_e| + rank_{R_e}(j)` in the coef section.

`ordL_perm`: `ordL I` is a permutation of `vertexList I`, so `reGraph_spec` applies to
`reGraph I (ordL I) ε`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The steps of column `c`, increasing. -/
def stepsC (c : Coord k ℓ) : List ℕ :=
  (List.range (numSteps k ℓ)).filter fun σ => ent σ c ≠ 0

open Classical in
/-- The steps whose row is nonzero on the domain of `e`, increasing. -/
noncomputable def coefSteps (e : Fin I.schemas.length) : List ℕ :=
  (List.range (numSteps k ℓ)).filter fun σ => ∃ c ∈ dom I e, ent σ c ≠ 0

/-- The hubs of schema `e`. -/
def hubsE (e : Fin I.schemas.length) : List (VName I) :=
  (coordList (dom I e)).flatMap (fun c =>
      (if isTern (sch I e) then bits2.map (fun l => (Cls.junc e c, l)) else []) ++
        bits1.map fun l => (Cls.link e c, l)) ++
    (coordList (dom I e)).flatMap fun c =>
      (stepsC c).flatMap fun σ => bits2.map fun l => (Cls.upd e σ c, l)

/-- The non-hubs of schema `e`. -/
noncomputable def nonhubsE (e : Fin I.schemas.length) : List (VName I) :=
  (coordList (dom I e)).flatMap (fun c =>
      if isTern (sch I e) then bits1.map (fun l => (Cls.sum e c, l)) else []) ++
    (coordList (dom I e)).flatMap (fun c =>
      (stepsC c).flatMap fun σ => bits1.map fun l => (Cls.track e σ c, l)) ++
    (coefSteps I e).flatMap fun σ => bits1.map fun l => (Cls.coef e σ, l)

/-- The vertex order of the machine. -/
noncomputable def ordL : List (VName I) :=
  (List.finRange I.schemas.length).flatMap (fun e => hubsE I e ++ nonhubsE I e) ++
    (List.finRange I.numLocations).flatMap (coordVerts I)

@[simp] lemma mem_stepsC {c : Coord k ℓ} {σ : ℕ} :
    σ ∈ stepsC c ↔ σ < numSteps k ℓ ∧ ent σ c ≠ 0 := by
  simp [stepsC]

@[simp] lemma mem_coefSteps {e : Fin I.schemas.length} {σ : ℕ} :
    σ ∈ coefSteps I e ↔ σ < numSteps k ℓ ∧ ∃ c ∈ dom I e, ent σ c ≠ 0 := by
  simp [coefSteps]

/-- The names of the order are the valid names. -/
theorem mem_ordL (x : VName I) : x ∈ ordL I ↔ Valid I x := by
  obtain ⟨X, l⟩ := x
  cases X with
  | coord v c =>
    simp only [ordL, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
      mem_coordVerts]
    constructor
    · rintro (⟨e, h⟩ | ⟨v', -, h⟩)
      · exfalso
        simp [hubsE, nonhubsE] at h
      · exact h
    · intro h; exact Or.inr ⟨v, ⟨c, rfl⟩, h⟩
  | _ =>
    simp only [ordL, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
      mem_coordVerts, hubsE, nonhubsE, List.mem_map, mem_stepsC, mem_coefSteps, mem_coordList,
      Valid, ClsValid, LabelOK, twoBit, isSingleton, Prod.mk.injEq, mem_bits1, mem_bits2]
    constructor
    · intro h
      rcases h with ⟨e, h⟩ | ⟨v, ⟨c, hc⟩, -⟩
      · split_ifs at h <;> aesop
      · cases hc
    · intro h
      left
      aesop

lemma nodup_stepsC (c : Coord k ℓ) : (stepsC c).Nodup := List.nodup_range.filter _

lemma nodup_coefSteps (e : Fin I.schemas.length) : (coefSteps I e).Nodup :=
  List.nodup_range.filter _

/-- The steps of the columns, each with the labels `L`, are duplicate-free. -/
lemma nodup_colSteps (L : List Lab) (hL : L.Nodup) (C : Coord k ℓ → ℕ → ICls I)
    (hC : ∀ c σ, keyCoord I (C c σ) = some c ∧ keyStep I (C c σ) = some σ)
    (D : List (Coord k ℓ)) (hD : D.Nodup) :
    (D.flatMap fun c => (stepsC c).flatMap fun σ => L.map fun l => (C c σ, l)).Nodup := by
  refine nodup_flatMap_of_key (fun x => keyCoord I x.1) hD (fun c _ => ?_) (fun c _ x hx => ?_)
  · refine nodup_flatMap_of_key (fun x => keyStep I x.1) (nodup_stepsC c)
      (fun σ _ => nodup_map_label I _ hL) (fun σ _ x hx => ?_)
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
    exact (hC c σ).2
  · obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
    exact (hC c σ).1

lemma isHub_of_mem_hubsE {e : Fin I.schemas.length} {x : VName I} (hx : x ∈ hubsE I e) :
    isHub I x.1 = true ∧ keySchema I x.1 = some e := by
  simp only [hubsE, List.mem_append, List.mem_flatMap] at hx
  rcases hx with ⟨c, -, hx⟩ | ⟨c, -, σ, -, hx⟩
  · rcases hx with hx | hx
    · split at hx
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; exact ⟨rfl, rfl⟩
      · simp at hx
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; exact ⟨rfl, rfl⟩
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; exact ⟨rfl, rfl⟩

lemma not_hub_of_mem_nonhubsE {e : Fin I.schemas.length} {x : VName I}
    (hx : x ∈ nonhubsE I e) : isHub I x.1 = false ∧ keySchema I x.1 = some e := by
  simp only [nonhubsE, List.mem_append, List.mem_flatMap] at hx
  rcases hx with (⟨c, -, hx⟩ | ⟨c, -, σ, -, hx⟩) | ⟨σ, -, hx⟩
  · split at hx
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; exact ⟨rfl, rfl⟩
    · simp at hx
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; exact ⟨rfl, rfl⟩
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; exact ⟨rfl, rfl⟩

lemma nodup_hubsE (e : Fin I.schemas.length) : (hubsE I e).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 ≠ 5) ?_
    (nodup_colSteps I bits2 nodup_bits2 (fun c σ => .upd e σ c) (fun _ _ => ⟨rfl, rfl⟩) _
      (nodup_coordList _)) ?_ ?_
  · refine nodup_flatMap_of_key (fun x => keyCoord I x.1) (nodup_coordList _) (fun c _ => ?_)
      (fun c _ x hx => ?_)
    · refine nodup_append_of_key (fun x => tag I x.1 = 2) ?_ (nodup_map_label I _ nodup_bits1)
        ?_ ?_
      · split
        · exact nodup_map_label I _ nodup_bits2
        · exact List.nodup_nil
      · intro x hx
        split at hx
        · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
        · simp at hx
      · intro x hx
        obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
    · rcases List.mem_append.mp hx with hx | hx
      · split at hx
        · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
        · simp at hx
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
  · intro x hx
    obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp hx with hx | hx
    · split at hx
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
      · simp at hx
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
  · intro x hx
    obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]

lemma nodup_nonhubsE (e : Fin I.schemas.length) : (nonhubsE I e).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 ≠ 6) ?_ ?_ ?_ ?_
  · refine nodup_append_of_key (fun x => tag I x.1 = 1) ?_
      (nodup_colSteps I bits1 nodup_bits1 (fun c σ => .track e σ c) (fun _ _ => ⟨rfl, rfl⟩) _
        (nodup_coordList _)) ?_ ?_
    · refine nodup_flatMap_of_key (fun x => keyCoord I x.1) (nodup_coordList _)
        (fun c _ => ?_) (fun c _ x hx => ?_)
      · split
        · exact nodup_map_label I _ nodup_bits1
        · exact List.nodup_nil
      · split at hx
        · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
        · simp at hx
    · intro x hx
      obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
      split at hx
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
      · simp at hx
    · intro x hx
      obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
  · refine nodup_flatMap_of_key (fun x => keyStep I x.1) (nodup_coefSteps I e)
      (fun σ _ => nodup_map_label I _ nodup_bits1) (fun σ _ x hx => ?_)
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
      split at hx
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
      · simp at hx
    · obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
  · intro x hx
    obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]

theorem nodup_ordL : (ordL I).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 ≠ 0) ?_ ?_ ?_ ?_
  · refine nodup_flatMap_of_key (fun x => keySchema I x.1) (List.nodup_finRange _)
      (fun e _ => ?_) (fun e _ x hx => ?_)
    · refine nodup_append_of_key (fun x => isHub I x.1 = true) (nodup_hubsE I e)
        (nodup_nonhubsE I e) (fun x hx => (isHub_of_mem_hubsE I hx).1) (fun x hx => ?_)
      rw [(not_hub_of_mem_nonhubsE I hx).1]; simp
    · rcases List.mem_append.mp hx with hx | hx
      · exact (isHub_of_mem_hubsE I hx).2
      · exact (not_hub_of_mem_nonhubsE I hx).2
  · refine nodup_flatMap_of_key (fun x => keyLoc I x.1) (List.nodup_finRange _)
      (fun v _ => nodup_coordVerts I v) (fun v _ x hx => ?_)
    obtain ⟨⟨c, h⟩, -⟩ := (mem_coordVerts I v x).mp hx
    rw [h]; rfl
  · intro x hx
    obtain ⟨e, -, hx⟩ := List.mem_flatMap.mp hx
    have : keySchema I x.1 = some e := by
      rcases List.mem_append.mp hx with hx | hx
      · exact (isHub_of_mem_hubsE I hx).2
      · exact (not_hub_of_mem_nonhubsE I hx).2
    intro h
    rcases x with ⟨X, l⟩
    cases X <;> simp_all [tag, keySchema]
  · intro x hx
    obtain ⟨v, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨⟨c, h⟩, -⟩ := (mem_coordVerts I v x).mp hx
    rw [h]; simp [tag]

/-- **The order is a permutation of the vertex list.** -/
theorem ordL_perm : (ordL I).Perm (vertexList I) :=
  (List.perm_ext_iff_of_nodup (nodup_ordL I) (nodup_vertexList I)).mpr fun x => by
    rw [mem_ordL, mem_vertexList]

end Lax119563Proofs.Compiler
