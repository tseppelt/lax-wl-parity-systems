import Lax119563Proofs.Counter.System

/-!
# The counter as an implicit parity system

See `System.lean` for the layout of locations and schemas.
-/

open Lax119563.ImplicitParitySystems

namespace Lax119563Proofs.Counter

variable {K ℓ : ℕ}

/-- The number `3 + 2m` of locations. -/
abbrev numLoc (K ℓ : ℕ) : ℕ := 3 + 2 * (ℓ * K)

open Classical in
/-- The coordinate domain of location `n`. -/
noncomputable def domN (K ℓ n : ℕ) : Finset (Coord (K + 1) ℓ) :=
  if n = 0 then Finset.univ
  else if n = 1 then supp (0 : Arr K ℓ)
  else if n = 2 then supp (top K ℓ)
  else dom K ℓ ((n - 3) / 2)

theorem domN_p (j : ℕ) : domN K ℓ (3 + 2 * j) = dom K ℓ j := by
  rw [domN, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

theorem domN_q (j : ℕ) : domN K ℓ (4 + 2 * j) = dom K ℓ j := by
  rw [domN, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

/-- The main location. -/
def locMain : Fin (numLoc K ℓ) := ⟨0, by unfold numLoc; omega⟩
/-- The endpoint location initialized `0`. -/
def locZ0 : Fin (numLoc K ℓ) := ⟨1, by unfold numLoc; omega⟩
/-- The endpoint location initialized `1`. -/
def locZ1 : Fin (numLoc K ℓ) := ⟨2, by unfold numLoc; omega⟩
/-- The first private location of the increment at `j`. -/
def locP (j : Fin (ℓ * K)) : Fin (numLoc K ℓ) := ⟨3 + 2 * j, by unfold numLoc; omega⟩
/-- The second private location of the increment at `j`. -/
def locQ (j : Fin (ℓ * K)) : Fin (numLoc K ℓ) := ⟨4 + 2 * j, by unfold numLoc; omega⟩

/-- The identity block-induced permutation. -/
def idPerm : BlockPerm (K + 1) ℓ := ⟨1, 0, by simp⟩

/-- The increment `a ↦ a + δ_j`. -/
def incPerm (j : ℕ) : BlockPerm (K + 1) ℓ := ⟨1, shift K ℓ j, sum_shift j⟩

theorem idPerm_apply (c : Coord (K + 1) ℓ) : (idPerm : BlockPerm (K + 1) ℓ).apply c = c := by
  simp [idPerm, BlockPerm.apply]

theorem idPerm_act (a : Arr K ℓ) : (idPerm : BlockPerm (K + 1) ℓ).act a = a := by
  funext i
  simp [idPerm, BlockPerm.act]; rfl

theorem incPerm_act (j : ℕ) (a : Arr K ℓ) : (incPerm (K := K) (ℓ := ℓ) j).act a = a + shift K ℓ j := by
  funext i
  simp [incPerm, BlockPerm.act]; rfl

theorem image_idPerm (D : Finset (Coord (K + 1) ℓ)) :
    D.image (idPerm : BlockPerm (K + 1) ℓ).apply = D := by
  have : (idPerm : BlockPerm (K + 1) ℓ).apply = id := funext idPerm_apply
  rw [this, Finset.image_id]

/-- Indices of the schemas: the two endpoint schemas, and three schemas per increment. -/
abbrev SchIdx (K ℓ : ℕ) := Bool ⊕ (Fin (ℓ * K) × Fin 3)

/-- The schemas of the counter. -/
noncomputable def schemaOf : SchIdx K ℓ → Schema (K + 1) ℓ (numLoc K ℓ)
  | .inl false => .binary locZ0 locMain (supp 0) idPerm idPerm
  | .inl true => .binary locZ1 locMain (supp (top K ℓ)) idPerm idPerm
  | .inr (j, c) =>
    if c = 0 then .binary locMain (locP j) (dom K ℓ j) idPerm idPerm
    else if c = 1 then .binary (locP j) (locQ j) (dom K ℓ j) idPerm idPerm
    else .binary (locQ j) locMain (dom K ℓ j) idPerm (incPerm j)

/-- The two location values of each schema. -/
def locPair : SchIdx K ℓ → ℕ × ℕ
  | .inl false => (1, 0)
  | .inl true => (2, 0)
  | .inr (j, c) =>
    if c = 0 then (0, 3 + 2 * j) else if c = 1 then (3 + 2 * j, 4 + 2 * j) else (4 + 2 * j, 0)

theorem schemaOf_eq (x : SchIdx K ℓ) : ∃ (u v : Fin (numLoc K ℓ)) (D : Finset (Coord (K + 1) ℓ))
    (σ τ : BlockPerm (K + 1) ℓ), schemaOf x = .binary u v D σ τ ∧
      ((u : ℕ), (v : ℕ)) = locPair x := by
  rcases x with (_ | _) | ⟨j, c⟩
  · exact ⟨_, _, _, _, _, rfl, rfl⟩
  · exact ⟨_, _, _, _, _, rfl, rfl⟩
  · fin_cases c
    · exact ⟨_, _, _, _, _, rfl, rfl⟩
    · exact ⟨_, _, _, _, _, rfl, rfl⟩
    · exact ⟨_, _, _, _, _, rfl, rfl⟩

theorem locPair_ne (x : SchIdx K ℓ) : (locPair x).1 ≠ (locPair x).2 := by
  rcases x with (_ | _) | ⟨j, c⟩
  · simp [locPair]
  · simp [locPair]
  · fin_cases c <;> simp [locPair] <;> omega

theorem locPair_inj {x y : SchIdx K ℓ} (h : ({(locPair x).1, (locPair x).2} : Finset ℕ) =
    {(locPair y).1, (locPair y).2}) : x = y := by
  have h1 : (locPair x).1 ∈ ({(locPair y).1, (locPair y).2} : Finset ℕ) := h ▸ by simp
  have h2 : (locPair x).2 ∈ ({(locPair y).1, (locPair y).2} : Finset ℕ) := h ▸ by simp
  have h3 : (locPair y).1 ∈ ({(locPair x).1, (locPair x).2} : Finset ℕ) := h.symm ▸ by simp
  have h4 : (locPair y).2 ∈ ({(locPair x).1, (locPair x).2} : Finset ℕ) := h.symm ▸ by simp
  clear h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3 h4
  rcases x with b | ⟨j, c⟩ <;> rcases y with b' | ⟨j', c'⟩
  · cases b <;> cases b' <;> first | rfl | (simp [locPair] at h1 h2 h3 h4)
  · exfalso
    cases b <;> fin_cases c' <;> simp [locPair] at h1 h2 h3 h4 <;> omega
  · exfalso
    cases b' <;> fin_cases c <;> simp [locPair] at h1 h2 h3 h4 <;> omega
  · fin_cases c <;> fin_cases c' <;> simp [locPair] at h1 h2 h3 h4 ⊢ <;>
      first | (exfalso; omega) | (apply Fin.ext; omega)

theorem two_card_inter {α : Type*} [DecidableEq α] {s t : Finset α} (hs : s.card = 2)
    (ht : t.card = 2) (hne : s ≠ t) : (s ∩ t).card ≤ 1 := by
  by_contra h
  push Not at h
  have e1 : s ∩ t = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have e2 : s ∩ t = t := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  exact hne (e1.symm.trans e2)

theorem locations_schemaOf (x : SchIdx K ℓ) : ∃ u v : Fin (numLoc K ℓ),
    (schemaOf x).locations = {u, v} ∧ ((u : ℕ), (v : ℕ)) = locPair x := by
  obtain ⟨u, v, D, σ, τ, h, hp⟩ := schemaOf_eq x
  exact ⟨u, v, by rw [h]; rfl, hp⟩

theorem schemas_meet_aux : ((Finset.univ : Finset (SchIdx K ℓ)).toList.map schemaOf).Pairwise
    fun e e' => (e.locations ∩ e'.locations).card ≤ 1 := by
  rw [List.pairwise_map]
  refine (Finset.nodup_toList _).pairwise_of_forall_ne fun x _ y _ hxy => ?_
  obtain ⟨u, v, hl, hp⟩ := locations_schemaOf x
  obtain ⟨u', v', hl', hp'⟩ := locations_schemaOf y
  rw [hl, hl']
  have hne := locPair_ne x
  have hne' := locPair_ne y
  rw [← hp] at hne
  rw [← hp'] at hne'
  have huv : u ≠ v := fun h => hne (by simp [h])
  have huv' : u' ≠ v' := fun h => hne' (by simp [h])
  refine two_card_inter (Finset.card_pair huv) (Finset.card_pair huv') fun h => hxy (locPair_inj ?_)
  have := congrArg (Finset.image Fin.val) h
  simp only [Finset.image_insert, Finset.image_singleton] at this
  rw [← hp, ← hp']
  exact this

theorem schemaOf_wellFormed (x : SchIdx K ℓ) :
    (schemaOf x).WellFormed (fun v => domN K ℓ v) := by
  rcases x with b | ⟨j, c⟩
  · cases b
    · refine ⟨by simp [locZ0, locMain, Fin.ext_iff], ?_, ?_⟩ <;>
        simp [image_idPerm, domN, locZ0, locMain]
    · refine ⟨by simp [locZ1, locMain, Fin.ext_iff], ?_, ?_⟩ <;>
        simp [image_idPerm, domN, locZ1, locMain]
  · fin_cases c
    · refine ⟨by simp [locMain, locP, Fin.ext_iff] <;> omega, ?_, ?_⟩
      · simp [image_idPerm, domN, locMain]
      · show (dom K ℓ j).image idPerm.apply ⊆ domN K ℓ (3 + 2 * j)
        rw [image_idPerm, domN_p]
    · refine ⟨by simp [locQ, locP, Fin.ext_iff] <;> omega, ?_, ?_⟩
      · show (dom K ℓ j).image idPerm.apply ⊆ domN K ℓ (3 + 2 * j)
        rw [image_idPerm, domN_p]
      · show (dom K ℓ j).image idPerm.apply ⊆ domN K ℓ (4 + 2 * j)
        rw [image_idPerm, domN_q]
    · refine ⟨by simp [locQ, locMain, Fin.ext_iff] <;> omega, ?_, ?_⟩
      · show (dom K ℓ j).image idPerm.apply ⊆ domN K ℓ (4 + 2 * j)
        rw [image_idPerm, domN_q]
      · show _ ⊆ domN K ℓ 0
        simp [domN]

end Lax119563Proofs.Counter
