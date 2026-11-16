import Lax119563Proofs.Counter.Construction
import Lax119563Proofs.Counter.Propagation

/-!
# The conflict round of the counter

Unit propagation on the counter has a conflict, and its conflict round is at least `2^m`
for `m = ℓ K`:

* *Lower bound.* The potential `Φ(X_{v,a}) = 3 val(a) + 1` at the main location (with
  `+2`, `+3` at the private locations, `0` at `z₀` and `3 val(t) + 2` at `z₁`) changes by at
  most one along every equation, so `0`s spread up and `1`s spread down by one per round.
* *Finiteness.* Every address eventually receives the value `0` at the main location, by
  induction on its counter value: decrementing at the first one bit gives an address with
  data prefix `1^j 0`, from which the increment schemas propagate in three rounds.
-/

open Lax119563.ImplicitParitySystems Lax119563.ParitySystems

namespace Lax119563Proofs.Counter

variable {K ℓ : ℕ}

/-- The counter implicit parity system `𝓘_ctr^{K+1,ℓ}`. -/
noncomputable def counter (K ℓ : ℕ) : ImplicitParitySystem (K + 1) ℓ where
  numLocations := numLoc K ℓ
  domain v := domN K ℓ v
  schemas := (Finset.univ : Finset (SchIdx K ℓ)).toList.map schemaOf
  init v := if (v : ℕ) = 1 then some 0 else if (v : ℕ) = 2 then some 1 else none
  schema_wellFormed := by
    intro e he
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
    exact schemaOf_wellFormed x
  schemas_meet := schemas_meet_aux

/-- The parity system of the counter. -/
noncomputable abbrev ctrP (K ℓ : ℕ) := (counter K ℓ).toParitySystem

theorem schemaOf_mem (x : SchIdx K ℓ) : schemaOf x ∈ (counter K ℓ).schemas :=
  List.mem_map.mpr ⟨x, Finset.mem_toList.mpr (Finset.mem_univ x), rfl⟩

theorem equation_mem (x : SchIdx K ℓ) {a : Arr K ℓ} (ha : IsAddress a)
    (hs : supp a ⊆ (schemaOf x).domain) : (schemaOf x).equation a ∈ (ctrP K ℓ).equations :=
  ⟨schemaOf x, schemaOf_mem x, a, ha, hs, rfl⟩

/-! ### The lower bound -/

/-- The potential of a variable. -/
def pot (K ℓ : ℕ) (X : Fin (numLoc K ℓ) × Arr K ℓ) : ℕ :=
  if (X.1 : ℕ) = 0 then 3 * val X.2 + 1
  else if (X.1 : ℕ) = 1 then 0
  else if (X.1 : ℕ) = 2 then 3 * val (top K ℓ) + 2
  else if (X.1 : ℕ) % 2 = 1 then 3 * val X.2 + 2
  else 3 * val X.2 + 3

theorem pot_main (a : Arr K ℓ) : pot K ℓ (locMain, a) = 3 * val a + 1 := by
  simp [pot, locMain]

theorem pot_z0 (a : Arr K ℓ) : pot K ℓ (locZ0, a) = 0 := by
  simp [pot, locZ0]

theorem pot_z1 (a : Arr K ℓ) : pot K ℓ (locZ1, a) = 3 * val (top K ℓ) + 2 := by
  simp [pot, locZ1]

theorem pot_p (j : Fin (ℓ * K)) (a : Arr K ℓ) : pot K ℓ (locP j, a) = 3 * val a + 2 := by
  unfold pot
  have h : ((locP j, a).1 : ℕ) = 3 + 2 * (j : ℕ) := rfl
  have h' : (locP j, a).2 = a := rfl
  rw [h, h']
  split_ifs <;> omega

theorem pot_q (j : Fin (ℓ * K)) (a : Arr K ℓ) : pot K ℓ (locQ j, a) = 3 * val a + 3 := by
  unfold pot
  have h : ((locQ j, a).1 : ℕ) = 4 + 2 * (j : ℕ) := rfl
  have h' : (locQ j, a).2 = a := rfl
  rw [h, h']
  split_ifs <;> omega

theorem ne_of_val {X Y : Fin (numLoc K ℓ) × Arr K ℓ} (h : (X.1 : ℕ) ≠ (Y.1 : ℕ)) : X ≠ Y :=
  fun e => h (by rw [e])

theorem eqn_start (a : Arr K ℓ) :
    (schemaOf (K := K) (ℓ := ℓ) (.inl false)).equation a = {(locZ0, a), (locMain, a)} := by
  simp [schemaOf, Schema.equation, idPerm_act]

theorem eqn_stop (a : Arr K ℓ) :
    (schemaOf (K := K) (ℓ := ℓ) (.inl true)).equation a = {(locZ1, a), (locMain, a)} := by
  simp [schemaOf, Schema.equation, idPerm_act]

theorem eqn_up (j : Fin (ℓ * K)) (a : Arr K ℓ) :
    (schemaOf (K := K) (ℓ := ℓ) (.inr (j, 0))).equation a = {(locMain, a), (locP j, a)} := by
  simp [schemaOf, Schema.equation, idPerm_act]

theorem eqn_mid (j : Fin (ℓ * K)) (a : Arr K ℓ) :
    (schemaOf (K := K) (ℓ := ℓ) (.inr (j, 1))).equation a = {(locP j, a), (locQ j, a)} := by
  simp [schemaOf, Schema.equation, idPerm_act]

theorem eqn_down (j : Fin (ℓ * K)) (a : Arr K ℓ) :
    (schemaOf (K := K) (ℓ := ℓ) (.inr (j, 2))).equation a =
      {(locQ j, a), (locMain, a + shift K ℓ j)} := by
  simp [schemaOf, Schema.equation, idPerm_act, incPerm_act]

theorem pot_equations : ∀ h ∈ (ctrP K ℓ).equations, ∃ X Y : Fin (numLoc K ℓ) × Arr K ℓ, X ≠ Y ∧ h = {X, Y} ∧
    pot K ℓ X ≤ pot K ℓ Y + 1 ∧ pot K ℓ Y ≤ pot K ℓ X + 1 := by
  rintro h ⟨e, he, a, ha, hs, rfl⟩
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
  rcases x with (_ | _) | ⟨j, c⟩
  · have hs' : supp a ⊆ supp (0 : Arr K ℓ) := hs
    obtain rfl := eq_of_supp_subset hs'
    refine ⟨(locZ0, 0), (locMain, 0), ne_of_val (by show 1 ≠ 0; omega), eqn_start 0, ?_, ?_⟩
    · rw [pot_z0, pot_main, val_zero] <;> omega
    · rw [pot_z0, pot_main, val_zero] <;> omega
  · have hs' : supp a ⊆ supp (top K ℓ) := hs
    obtain rfl := eq_of_supp_subset hs'
    refine ⟨(locZ1, top K ℓ), (locMain, top K ℓ), ne_of_val (by show 2 ≠ 0; omega),
      eqn_stop _, ?_, ?_⟩
    · rw [pot_z1, pot_main] <;> omega
    · rw [pot_z1, pot_main] <;> omega
  · fin_cases c
    · refine ⟨(locMain, a), (locP j, a), ne_of_val (by show 0 ≠ 3 + 2 * (j : ℕ); omega),
        eqn_up j a, ?_, ?_⟩
      · rw [pot_p, pot_main] <;> omega
      · rw [pot_p, pot_main] <;> omega
    · refine ⟨(locP j, a), (locQ j, a), ne_of_val (by show 3 + 2 * (j : ℕ) ≠ 4 + 2 * j; omega),
        eqn_mid j a, ?_, ?_⟩
      · rw [pot_p, pot_q] <;> omega
      · rw [pot_p, pot_q] <;> omega
    · have hs' : supp a ⊆ dom K ℓ j := hs
      have hpre := (supp_subset_dom_iff ha).mp hs'
      have hv := val_add_shift j.2 hpre
      refine ⟨(locQ j, a), (locMain, a + shift K ℓ j),
        ne_of_val (by show 4 + 2 * (j : ℕ) ≠ 0; omega), eqn_down j a, ?_, ?_⟩
      · rw [pot_q, pot_main, hv] <;> omega
      · rw [pot_q, pot_main, hv] <;> omega

theorem pot_initial : ∀ f ∈ (ctrP K ℓ).initial,
    (f.2 = 0 ∧ pot K ℓ f.1 = 0) ∨ (f.2 = 1 ∧ 3 * val (top K ℓ) + 2 ≤ pot K ℓ f.1) := by
  rintro ⟨⟨v, a⟩, b⟩ ⟨b', hb', hbb, -, -⟩
  dsimp only at hbb
  subst hbb
  change (if (v : ℕ) = 1 then some 0 else if (v : ℕ) = 2 then some 1 else none) = some b at hb'
  split_ifs at hb' with h1 h2
  · cases hb'
    left
    exact ⟨rfl, by simp [pot, h1]⟩
  · cases hb'
    right
    exact ⟨rfl, by simp [pot, h2]⟩

/-- **Lower bound.** A conflict in round `r` needs `3 val(t) + 2 ≤ 2 r`. -/
theorem conflict_lower {r : ℕ} (hc : (ctrP K ℓ).HasConflict r) :
    3 * val (top K ℓ) + 2 ≤ 2 * r :=
  conflict_bound _ (pot K ℓ) _ pot_equations pot_initial hc

/-! ### A conflict occurs -/

theorem shift_add_shift (j : ℕ) : shift K ℓ j + shift K ℓ j = 0 := by
  funext i
  exact blockCoord_add_self _

theorem main_zero_known (n : ℕ) : ∀ a : Arr K ℓ, IsAddress a → val a = n →
    ∃ r, ((locMain, a), (0 : ZMod 2)) ∈ (ctrP K ℓ).known r := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a ha hn
  by_cases hz : ∀ p, dbit a p = 0
  · obtain rfl := eq_zero_of_dbit ha hz
    refine ⟨1, known_succ_of_pair _ (Y := (locZ0, 0)) (ne_of_val (by show 0 ≠ 1; omega)) ?_ ?_⟩
    · have := equation_mem (K := K) (ℓ := ℓ) (.inl false) (a := 0)
        (by simp [IsAddress]) (subset_refl _)
      rw [eqn_start, Finset.pair_comm] at this
      exact this
    · refine ⟨0, ?_, rfl, by simp [IsAddress], ?_⟩
      · simp [counter, locZ0]
      · show supp 0 ⊆ domN K ℓ 1
        simp [domN]
  · push Not at hz
    have hex : ∃ p : ℕ, ∃ hp : p < ℓ * K, dbit a ⟨p, hp⟩ ≠ 0 := by
      obtain ⟨p, hp⟩ := hz
      exact ⟨p, p.2, hp⟩
    classical
    set j := Nat.find hex with hjdef
    obtain ⟨hj, hj1⟩ := Nat.find_spec hex
    have hlow : ∀ p : Fin (ℓ * K), (p : ℕ) < j → dbit a p = 0 := by
      intro p hp
      by_contra hne
      exact Nat.find_min hex hp ⟨p.2, hne⟩
    set a' := a + shift K ℓ j with ha'def
    have ha' : IsAddress a' := isAddress_add ha (isAddress_shift j)
    have hpre : Prefix j a' := by
      intro p hp
      rw [dbit_add, dbit_shift, if_pos hp]
      rcases Nat.lt_or_eq_of_le hp with hlt | heq
      · rw [hlow p hlt, if_pos hlt]; decide
      · have : p = ⟨j, hj⟩ := Fin.ext heq
        subst this
        rw [zmod2_eq_one_of_ne_zero hj1, if_neg (lt_irrefl _)]; decide
    have hback : a' + shift K ℓ j = a := by
      rw [ha'def, add_assoc, shift_add_shift, add_zero]
    have hval := val_add_shift hj hpre
    rw [hback] at hval
    obtain ⟨r, hr⟩ := ih (val a') (by omega) a' ha' rfl
    have hsupp : supp a' ⊆ dom K ℓ j := (supp_subset_dom_iff ha').mpr hpre
    let jj : Fin (ℓ * K) := ⟨j, hj⟩
    have e0 := equation_mem (K := K) (ℓ := ℓ) (.inr (jj, 0)) ha' hsupp
    have e1 := equation_mem (K := K) (ℓ := ℓ) (.inr (jj, 1)) ha' hsupp
    have e2 := equation_mem (K := K) (ℓ := ℓ) (.inr (jj, 2)) ha' hsupp
    rw [eqn_up, Finset.pair_comm] at e0
    rw [eqn_mid, Finset.pair_comm] at e1
    rw [eqn_down, Finset.pair_comm] at e2
    have k1 : ((locP jj, a'), (0 : ZMod 2)) ∈ (ctrP K ℓ).known (r + 1) :=
      known_succ_of_pair _ (ne_of_val (by show 3 + 2 * j ≠ 0; omega)) e0 hr
    have k2 : ((locQ jj, a'), (0 : ZMod 2)) ∈ (ctrP K ℓ).known (r + 1 + 1) :=
      known_succ_of_pair _ (ne_of_val (by show 4 + 2 * j ≠ 3 + 2 * j; omega)) e1 k1
    have k3 := known_succ_of_pair _ (X := (locMain, a' + shift K ℓ j))
      (ne_of_val (by show 0 ≠ 4 + 2 * j; omega)) e2 k2
    rw [hback] at k3
    exact ⟨_, k3⟩

theorem exists_conflict : ∃ r, (ctrP K ℓ).HasConflict r := by
  obtain ⟨r, hr⟩ := main_zero_known (K := K) (ℓ := ℓ) _ (top K ℓ) isAddress_top rfl
  have e := equation_mem (K := K) (ℓ := ℓ) (.inl true) isAddress_top (subset_refl _)
  rw [eqn_stop] at e
  refine ⟨r + 1, (locZ1, top K ℓ),
    known_succ_of_pair _ (ne_of_val (by show 2 ≠ 0; omega)) e hr, ?_⟩
  · refine known_mono _ (Nat.zero_le _) ⟨1, ?_, rfl, isAddress_top, ?_⟩
    · simp [counter, locZ1]
    · show supp (top K ℓ) ⊆ domN K ℓ 2
      simp [domN]

/-- **The conflict round of the counter.** It is finite and at least `2^{ℓ K}`. -/
theorem counter_conflictRound : ∃ τ : ℕ, (counter K ℓ).conflictRound = τ ∧ 2 ^ (ℓ * K) ≤ τ := by
  classical
  refine ⟨Nat.find exists_conflict, conflictRound_eq_find _ exists_conflict, ?_⟩
  have h1 := conflict_lower (Nat.find_spec (exists_conflict (K := K) (ℓ := ℓ)))
  have h2 := val_top (K := K) (ℓ := ℓ)
  have h3 : 1 ≤ 2 ^ (ℓ * K) := Nat.one_le_two_pow
  omega

end Lax119563Proofs.Counter
