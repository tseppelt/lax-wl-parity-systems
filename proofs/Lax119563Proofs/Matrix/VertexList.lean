import Lax119563Proofs.Matrix.Construction

/-!
# The vertex list

`vertexList I` lists every valid vertex name exactly once.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ}

/-! ### Generic list facts -/

lemma nodup_flatMap_of_key {γ α : Type*} {l : List γ} {f : γ → List α} (key : α → Option γ)
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup) (hk : ∀ a ∈ l, ∀ x ∈ f a, key x = some a) :
    (l.flatMap f).Nodup := by
  refine List.nodup_flatMap.mpr ⟨hf, hl.imp_of_mem fun ha hb hab => ?_⟩
  intro x hxa hxb
  exact hab (Option.some.inj ((hk _ ha x hxa).symm.trans (hk _ hb x hxb)))

lemma nodup_append_of_key {α : Type*} {l₁ l₂ : List α} (key : α → Prop) (h₁ : l₁.Nodup)
    (h₂ : l₂.Nodup) (hk₁ : ∀ x ∈ l₁, key x) (hk₂ : ∀ x ∈ l₂, ¬ key x) : (l₁ ++ l₂).Nodup :=
  List.nodup_append.mpr ⟨h₁, h₂, fun a ha b hb hab => hk₂ b hb (hab ▸ hk₁ a ha)⟩

/-! ### Coordinates -/

lemma mem_allBlockCoords : ∀ {ℓ : ℕ} (b : BlockCoord ℓ), b ∈ allBlockCoords ℓ
  | 0, b => by
    simp only [allBlockCoords, List.mem_singleton]
    funext i; exact i.elim0
  | ℓ + 1, b => by
    simp only [allBlockCoords, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨Fin.tail b, mem_allBlockCoords _, ?_⟩
    rcases zmod2_eq_zero_or_one (b 0) with h | h
    · left; rw [← h]; exact (Fin.cons_self_tail b).symm
    · right; rw [← h]; exact (Fin.cons_self_tail b).symm

lemma nodup_allBlockCoords : ∀ ℓ : ℕ, (allBlockCoords ℓ).Nodup
  | 0 => List.nodup_singleton _
  | ℓ + 1 => by
    refine nodup_flatMap_of_key (fun b => some (Fin.tail b)) (nodup_allBlockCoords ℓ)
      (fun b _ => ?_) (fun b _ x hx => ?_)
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      simp only [List.mem_singleton]
      intro h
      have := congrFun h 0
      simp at this
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp

lemma mem_allCoords (c : Coord k ℓ) : c ∈ allCoords k ℓ := by
  simp only [allCoords, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨c.1, c.2, mem_allBlockCoords _, rfl⟩

lemma nodup_allCoords : (allCoords k ℓ).Nodup := by
  refine nodup_flatMap_of_key (fun c => some c.1) (List.nodup_finRange k)
    (fun i _ => (nodup_allBlockCoords ℓ).map fun b b' h => congrArg Prod.snd h) ?_
  intro i _ x hx
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
  rfl

@[simp] lemma mem_coordList {D : Finset (Coord k ℓ)} {c : Coord k ℓ} :
    c ∈ coordList D ↔ c ∈ D := by
  simp [coordList, mem_allCoords]

lemma nodup_coordList (D : Finset (Coord k ℓ)) : (coordList D).Nodup :=
  nodup_allCoords.filter _

lemma length_coordList (D : Finset (Coord k ℓ)) : (coordList D).length = D.card := by
  rw [← List.toFinset_card_of_nodup (nodup_coordList D)]
  congr 1
  ext c; simp

/-! ### Labels -/

@[simp] lemma mem_bits1 (l : Lab) : l ∈ bits1 ↔ l.2 = 0 := by
  obtain ⟨a, b⟩ := l
  simp only [bits1, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> simp

@[simp] lemma mem_bits2 (l : Lab) : l ∈ bits2 := by
  obtain ⟨a, b⟩ := l
  simp only [bits2, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one b with rfl | rfl <;> simp

lemma nodup_bits1 : bits1.Nodup := by decide

lemma nodup_bits2 : bits2.Nodup := by decide

/-! ### Membership -/

variable (I : ImplicitParitySystem k ℓ)

lemma mem_coordVerts (v : Fin I.numLocations) (x : VName I) :
    x ∈ coordVerts I v ↔ (∃ c, x.1 = .coord v c) ∧ Valid I x := by
  obtain ⟨X, l⟩ := x
  constructor
  · simp only [coordVerts, List.mem_flatMap, mem_coordList, List.mem_map]
    rintro ⟨c, hc, l', hl', he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨⟨c, rfl⟩, hc, fun _ => ?_, fun h => ?_⟩
    · split at hl'
      · simp at hl'; rw [hl']
      · exact (mem_bits1 _).mp hl'
    · simp only [isSingleton] at h
      rw [if_pos h] at hl'
      simp at hl'; rw [hl']
  · rintro ⟨⟨c, rfl⟩, hc, hl1, hl2⟩
    simp only [coordVerts, List.mem_flatMap, mem_coordList, List.mem_map]
    refine ⟨c, hc, l, ?_, rfl⟩
    have h2 : l.2 = 0 := hl1 rfl
    split
    · next h =>
      have h1 : l.1 = 0 := hl2 (by simpa [isSingleton] using h)
      simp [Prod.ext_iff, h1, h2]
    · exact (mem_bits1 _).mpr h2

lemma mem_columnVerts (e : Fin I.schemas.length) (c : Coord k ℓ) (x : VName I) :
    x ∈ columnVerts I e c ↔ (x.1 = .sum e c ∨ x.1 = .junc e c ∨ x.1 = .link e c) ∧
      (x.1 = .link e c ∨ isTern (sch I e) = true) ∧ LabelOK I x.1 x.2 := by
  obtain ⟨X, l⟩ := x
  by_cases ht : isTern (sch I e) = true
  · simp only [columnVerts, ht, if_true, List.mem_append, List.mem_map, mem_bits1, mem_bits2,
      Prod.mk.injEq, or_true]
    constructor
    · rintro ((⟨l', hl', rfl, rfl⟩ | ⟨l', -, rfl, rfl⟩) | ⟨l', hl', rfl, rfl⟩)
      · exact ⟨Or.inl rfl, trivial, fun _ => hl', fun h => by simp [isSingleton] at h⟩
      · exact ⟨Or.inr (Or.inl rfl), trivial, fun h => by simp [twoBit] at h,
          fun h => by simp [isSingleton] at h⟩
      · exact ⟨Or.inr (Or.inr rfl), trivial, fun _ => hl', fun h => by simp [isSingleton] at h⟩
    · rintro ⟨hX | hX | hX, -, hl1, -⟩ <;> subst hX
      · exact Or.inl (Or.inl ⟨l, hl1 rfl, rfl, rfl⟩)
      · exact Or.inl (Or.inr ⟨l, trivial, rfl, rfl⟩)
      · exact Or.inr ⟨l, hl1 rfl, rfl, rfl⟩
  · simp only [columnVerts, ht, Bool.false_eq_true, if_false, List.nil_append,
      List.mem_map, mem_bits1, Prod.mk.injEq, or_false]
    constructor
    · rintro ⟨l', hl', rfl, rfl⟩
      exact ⟨Or.inr (Or.inr rfl), rfl, fun _ => hl', fun h => by simp [isSingleton] at h⟩
    · rintro ⟨-, rfl, hl1, -⟩
      exact ⟨l, hl1 rfl, rfl, rfl⟩

lemma mem_stepVerts (e : Fin I.schemas.length) (σ : ℕ) (x : VName I) :
    x ∈ stepVerts I e σ ↔
      ((x.1 = .coef e σ ∧ ∃ c ∈ dom I e, ent σ c ≠ 0) ∨
        ∃ c ∈ dom I e, ent σ c ≠ 0 ∧ (x.1 = .track e σ c ∨ x.1 = .upd e σ c)) ∧
      LabelOK I x.1 x.2 := by
  obtain ⟨X, l⟩ := x
  simp only [stepVerts, List.mem_append, List.mem_flatMap, List.mem_filter, mem_coordList,
    List.mem_map, Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨c, ⟨hc, hent⟩, h⟩)
    · split at h
      · next hex =>
        obtain ⟨l', hl', rfl, rfl⟩ := List.mem_map.mp h
        exact ⟨Or.inl ⟨rfl, hex⟩, fun _ => (mem_bits1 _).mp hl', fun h => by
          simp [isSingleton] at h⟩
      · simp at h
    · rcases h with ⟨l', hl', rfl, rfl⟩ | ⟨l', hl', rfl, rfl⟩
      · exact ⟨Or.inr ⟨c, hc, hent, Or.inl rfl⟩, fun _ => (mem_bits1 _).mp hl', fun h => by
          simp [isSingleton] at h⟩
      · exact ⟨Or.inr ⟨c, hc, hent, Or.inr rfl⟩, fun h => by simp [twoBit] at h, fun h => by
          simp [isSingleton] at h⟩
  · rintro ⟨⟨rfl, hex⟩ | ⟨c, hc, hent, rfl | rfl⟩, hl1, -⟩
    · left
      rw [if_pos hex]
      exact List.mem_map.mpr ⟨l, (mem_bits1 _).mpr (hl1 rfl), rfl⟩
    · exact Or.inr ⟨c, ⟨hc, hent⟩, Or.inl ⟨l, (mem_bits1 _).mpr (hl1 rfl), rfl, rfl⟩⟩
    · exact Or.inr ⟨c, ⟨hc, hent⟩, Or.inr ⟨l, mem_bits2 _, rfl, rfl⟩⟩

/-- The vertex list consists of the valid names. -/
theorem mem_vertexList (x : VName I) : x ∈ vertexList I ↔ Valid I x := by
  obtain ⟨X, l⟩ := x
  simp only [vertexList, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
    mem_coordVerts, schemaVerts, mem_columnVerts, mem_coordList, List.mem_range,
    mem_stepVerts]
  constructor
  · rintro (⟨v, -, hv⟩ | ⟨e, ⟨c, hc, hX, ht, hl⟩ | ⟨σ, hσ, hX, hl⟩⟩)
    · exact hv
    · refine ⟨?_, hl⟩
      rcases hX with rfl | rfl | rfl
      · exact ⟨ht.resolve_left (by simp), hc⟩
      · exact ⟨ht.resolve_left (by simp), hc⟩
      · exact hc
    · refine ⟨?_, hl⟩
      rcases hX with ⟨rfl, hex⟩ | ⟨c, hc, hent, rfl | rfl⟩
      · exact ⟨hσ, hex⟩
      · exact ⟨hσ, hc, hent⟩
      · exact ⟨hσ, hc, hent⟩
  · rintro ⟨hX, hl⟩
    cases X with
    | coord v c => exact Or.inl ⟨v, ⟨c, rfl⟩, hX, hl⟩
    | sum e c => exact Or.inr ⟨e, Or.inl ⟨c, hX.2, Or.inl rfl, Or.inr hX.1, hl⟩⟩
    | junc e c => exact Or.inr ⟨e, Or.inl ⟨c, hX.2, Or.inr (Or.inl rfl), Or.inr hX.1, hl⟩⟩
    | link e c => exact Or.inr ⟨e, Or.inl ⟨c, hX, Or.inr (Or.inr rfl), Or.inl rfl, hl⟩⟩
    | track e σ c => exact Or.inr ⟨e, Or.inr ⟨σ, hX.1, Or.inr ⟨c, hX.2.1, hX.2.2, Or.inl rfl⟩, hl⟩⟩
    | upd e σ c => exact Or.inr ⟨e, Or.inr ⟨σ, hX.1, Or.inr ⟨c, hX.2.1, hX.2.2, Or.inr rfl⟩, hl⟩⟩
    | coef e σ => exact Or.inr ⟨e, Or.inr ⟨σ, hX.1, Or.inl ⟨rfl, hX.2⟩, hl⟩⟩

/-! ### No duplicates -/

/-- The location of a coordinate class. -/
def keyLoc : ICls I → Option (Fin I.numLocations)
  | .coord v _ => some v
  | _ => none

/-- The coordinate of a class. -/
def keyCoord : ICls I → Option (Coord k ℓ)
  | .coord _ c => some c
  | .sum _ c => some c
  | .junc _ c => some c
  | .link _ c => some c
  | .track _ _ c => some c
  | .upd _ _ c => some c
  | .coef _ _ => none

/-- The schema of a class. -/
def keySchema : ICls I → Option (Fin I.schemas.length)
  | .coord .. => none
  | .sum e _ => some e
  | .junc e _ => some e
  | .link e _ => some e
  | .track e _ _ => some e
  | .upd e _ _ => some e
  | .coef e _ => some e

/-- The step of a class. -/
def keyStep : ICls I → Option ℕ
  | .track _ σ _ => some σ
  | .upd _ σ _ => some σ
  | .coef _ σ => some σ
  | _ => none

/-- The constructor of a class. -/
def tag : ICls I → ℕ
  | .coord .. => 0
  | .sum .. => 1
  | .junc .. => 2
  | .link .. => 3
  | .track .. => 4
  | .upd .. => 5
  | .coef .. => 6

lemma nodup_map_label (X : ICls I) {L : List Lab} (h : L.Nodup) :
    (L.map fun l => (X, l)).Nodup :=
  h.map fun _ _ h => congrArg Prod.snd h

lemma nodup_coordVerts (v : Fin I.numLocations) : (coordVerts I v).Nodup := by
  refine nodup_flatMap_of_key (fun x => keyCoord I x.1) (nodup_coordList _) (fun c _ => ?_)
    (fun c _ x hx => ?_)
  · apply nodup_map_label
    split
    · exact List.nodup_singleton _
    · exact nodup_bits1
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
    rfl

lemma nodup_columnVerts (e : Fin I.schemas.length) (c : Coord k ℓ) :
    (columnVerts I e c).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 ≠ 3) ?_ (nodup_map_label I _ nodup_bits1)
    ?_ ?_
  · split
    · exact nodup_append_of_key (fun x => tag I x.1 = 1) (nodup_map_label I _ nodup_bits1)
        (nodup_map_label I _ nodup_bits2) (fun x hx => by
          obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl) (fun x hx => by
          obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag])
    · exact List.nodup_nil
  · intro x hx
    split at hx
    · rcases List.mem_append.mp hx with hx | hx <;>
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
    · simp at hx
  · intro x hx
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]

lemma nodup_stepVerts (e : Fin I.schemas.length) (σ : ℕ) : (stepVerts I e σ).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 = 6) ?_ ?_ ?_ ?_
  · split
    · exact nodup_map_label I _ nodup_bits1
    · exact List.nodup_nil
  · refine nodup_flatMap_of_key (fun x => keyCoord I x.1) ((nodup_coordList _).filter _)
      (fun c _ => ?_) (fun c _ x hx => ?_)
    · exact nodup_append_of_key (fun x => tag I x.1 = 4) (nodup_map_label I _ nodup_bits1)
        (nodup_map_label I _ nodup_bits2) (fun x hx => by
          obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl) (fun x hx => by
          obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag])
    · rcases List.mem_append.mp hx with hx | hx <;>
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
  · intro x hx
    split at hx
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
    · simp at hx
  · intro x hx
    obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp hx with hx | hx <;>
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]

lemma nodup_schemaVerts (e : Fin I.schemas.length) : (schemaVerts I e).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 = 1 ∨ tag I x.1 = 2 ∨ tag I x.1 = 3) ?_ ?_ ?_ ?_
  · refine nodup_flatMap_of_key (fun x => keyCoord I x.1) (nodup_coordList _)
      (fun c _ => nodup_columnVerts I e c) (fun c _ x hx => ?_)
    rcases ((mem_columnVerts I e c x).mp hx).1 with h | h | h <;> rw [h] <;> rfl
  · refine nodup_flatMap_of_key (fun x => keyStep I x.1) List.nodup_range
      (fun σ _ => nodup_stepVerts I e σ) (fun σ _ x hx => ?_)
    rcases ((mem_stepVerts I e σ x).mp hx).1 with ⟨h, -⟩ | ⟨c, -, -, h | h⟩ <;> rw [h] <;> rfl
  · intro x hx
    obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
    rcases ((mem_columnVerts I e c x).mp hx).1 with h | h | h <;> rw [h] <;> simp [tag]
  · intro x hx
    obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
    rcases ((mem_stepVerts I e σ x).mp hx).1 with ⟨h, -⟩ | ⟨c, -, -, h | h⟩ <;> rw [h] <;>
      simp [tag]

/-- Every valid name occurs exactly once in the vertex list. -/
theorem nodup_vertexList : (vertexList I).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 = 0) ?_ ?_ ?_ ?_
  · refine nodup_flatMap_of_key (fun x => keyLoc I x.1) (List.nodup_finRange _)
      (fun v _ => nodup_coordVerts I v) (fun v _ x hx => ?_)
    obtain ⟨⟨c, h⟩, -⟩ := (mem_coordVerts I v x).mp hx
    rw [h]; rfl
  · refine nodup_flatMap_of_key (fun x => keySchema I x.1) (List.nodup_finRange _)
      (fun e _ => nodup_schemaVerts I e) (fun e _ x hx => ?_)
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
      rcases ((mem_columnVerts I e c x).mp hx).1 with h | h | h <;> rw [h] <;> rfl
    · obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
      rcases ((mem_stepVerts I e σ x).mp hx).1 with ⟨h, -⟩ | ⟨c, -, -, h | h⟩ <;> rw [h] <;> rfl
  · intro x hx
    obtain ⟨v, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨⟨c, h⟩, -⟩ := (mem_coordVerts I v x).mp hx
    rw [h]; rfl
  · intro x hx
    obtain ⟨e, -, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
      rcases ((mem_columnVerts I e c x).mp hx).1 with h | h | h <;> rw [h] <;> simp [tag]
    · obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
      rcases ((mem_stepVerts I e σ x).mp hx).1 with ⟨h, -⟩ | ⟨c, -, -, h | h⟩ <;> rw [h] <;>
        simp [tag]

end Lax119563Proofs.Matrix
