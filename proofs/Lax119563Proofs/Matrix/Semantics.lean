import Lax119563Proofs.Matrix.Construction

/-!
# Schemas, equations and unit propagation

Uniform access to the two or three arguments of a schema, and the facts about unit
propagation used by both players.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems

namespace Lax119563Proofs.Matrix

variable {k ℓ w : ℕ}

/-! ### Arguments of a schema -/

/-- The number of arguments of a schema. -/
@[reducible] def arity : Schema k ℓ w → ℕ
  | .binary .. => 2
  | .ternary .. => 3

/-- The argument locations. -/
def argLoc : (s : Schema k ℓ w) → Fin (arity s) → Fin w
  | .binary u v _ _ _ => ![u, v]
  | .ternary u v w' _ _ _ _ => ![u, v, w']

/-- The argument permutations. -/
def argPerm : (s : Schema k ℓ w) → Fin (arity s) → BlockPerm k ℓ
  | .binary _ _ _ σ τ => ![σ, τ]
  | .ternary _ _ _ _ σ τ π => ![σ, τ, π]

lemma equation_eq (s : Schema k ℓ w) (a : Fin k → BlockCoord ℓ) :
    s.equation a = Finset.univ.image fun i => (argLoc s i, (argPerm s i).act a) := by
  cases s with
  | binary u v D σ τ =>
    show _ = (Finset.univ : Finset (Fin 2)).image fun i => (![u, v] i, (![σ, τ] i).act a)
    ext x; simp [Schema.equation, Fin.exists_fin_two, eq_comm]
  | ternary u v w' D σ τ π =>
    show _ = (Finset.univ : Finset (Fin 3)).image fun i => (![u, v, w'] i, (![σ, τ, π] i).act a)
    ext x; simp [Schema.equation, Fin.exists_fin_succ, eq_comm]

lemma locations_eq (s : Schema k ℓ w) : s.locations = Finset.univ.image (argLoc s) := by
  cases s with
  | binary u v D σ τ =>
    show _ = (Finset.univ : Finset (Fin 2)).image ![u, v]
    ext x; simp [Schema.locations, Fin.exists_fin_two, eq_comm]
  | ternary u v w' D σ τ π =>
    show _ = (Finset.univ : Finset (Fin 3)).image ![u, v, w']
    ext x; simp [Schema.locations, Fin.exists_fin_succ, eq_comm]

lemma argLoc_injective {dom : Fin w → Finset (Coord k ℓ)} {s : Schema k ℓ w}
    (h : s.WellFormed dom) : Function.Injective (argLoc s) := by
  cases s with
  | binary u v D σ τ =>
    obtain ⟨huv, -⟩ := h
    show Function.Injective (![u, v] : Fin 2 → Fin w)
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exfalso; simp at hij; subst hij; simp_all)
  | ternary u v w' D σ τ π =>
    obtain ⟨huv, huw, hvw, -⟩ := h
    show Function.Injective (![u, v, w'] : Fin 3 → Fin w)
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exfalso; simp at hij; subst hij; simp_all)

lemma argPerm_mem {dom : Fin w → Finset (Coord k ℓ)} {s : Schema k ℓ w}
    (h : s.WellFormed dom) {c : Coord k ℓ} (hc : c ∈ s.domain) (i : Fin (arity s)) :
    (argPerm s i).apply c ∈ dom (argLoc s i) := by
  cases s with
  | binary u v D σ τ =>
    obtain ⟨-, h1, h2⟩ := h
    fin_cases i
    · exact h1 (Finset.mem_image_of_mem _ hc)
    · exact h2 (Finset.mem_image_of_mem _ hc)
  | ternary u v w' D σ τ π =>
    obtain ⟨-, -, -, h1, h2, h3⟩ := h
    fin_cases i
    · exact h1 (Finset.mem_image_of_mem _ hc)
    · exact h2 (Finset.mem_image_of_mem _ hc)
    · exact h3 (Finset.mem_image_of_mem _ hc)

/-- The sum of a function over the arguments: the start terms plus the end term. -/
lemma sum_args (s : Schema k ℓ w) (f : Fin w → BlockPerm k ℓ → ZMod 2) :
    ∑ i, f (argLoc s i) (argPerm s i) =
      f (locU s) (permU s) + (if isTern s then f (locV s) (permV s) else 0) +
        f (locEnd s) (permEnd s) := by
  cases s with
  | binary u v D σ τ =>
    show ∑ i : Fin 2, f (![u, v] i) (![σ, τ] i) = _
    simp [Fin.sum_univ_two, isTern, locU, permU, locEnd, permEnd]
  | ternary u v w' D σ τ π =>
    show ∑ i : Fin 3, f (![u, v, w'] i) (![σ, τ, π] i) = _
    simp [Fin.sum_univ_three, isTern, locU, permU, locV, permV, locEnd, permEnd]

/-! ### Schemas of an implicit parity system -/

variable (I : ImplicitParitySystem k ℓ)

lemma sch_mem (e : Fin I.schemas.length) : sch I e ∈ I.schemas := List.get_mem _ _

lemma sch_wf (e : Fin I.schemas.length) : (sch I e).WellFormed I.domain :=
  I.schema_wellFormed _ (sch_mem I e)

lemma exists_sch {s : Schema k ℓ I.numLocations} (hs : s ∈ I.schemas) :
    ∃ e, sch I e = s := List.mem_iff_get.mp hs

/-- Distinct schemas share at most one location. -/
lemma sch_meet {e e' : Fin I.schemas.length} (h : e ≠ e') :
    ((sch I e).locations ∩ (sch I e').locations).card ≤ 1 := by
  have hp := List.pairwise_iff_getElem.mp I.schemas_meet
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hlt | hlt
  · exact hp e e' e.2 e'.2 hlt
  · rw [Finset.inter_comm]; exact hp e' e e'.2 e.2 hlt

lemma sch_meet' {e e' : Fin I.schemas.length} (h : e ≠ e') {v v' : Fin I.numLocations}
    (hvv' : v ≠ v') (hv : v ∈ (sch I e).locations) (hv' : v' ∈ (sch I e).locations)
    (hv2 : v ∈ (sch I e').locations) (hv2' : v' ∈ (sch I e').locations) : False := by
  have := sch_meet I h
  have h2 : ({v, v'} : Finset _) ⊆ (sch I e).locations ∩ (sch I e').locations := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp_all
  have := (Finset.card_le_card h2).trans this
  rw [Finset.card_pair hvv'] at this
  omega

/-! ### Unit propagation -/

/-- The variable of argument `i` of schema `e` at address `a`. -/
def argVar (e : Fin I.schemas.length) (i : Fin (arity (sch I e))) (a : Fin k → BlockCoord ℓ) :
    Fin I.numLocations × (Fin k → BlockCoord ℓ) :=
  (argLoc (sch I e) i, (argPerm (sch I e) i).act a)

lemma argVar_injective (e : Fin I.schemas.length) (a : Fin k → BlockCoord ℓ) :
    Function.Injective fun i => argVar I e i a :=
  fun _ _ h => argLoc_injective (sch_wf I e) (congrArg Prod.fst h)

lemma known_mono {r r' : ℕ} (h : r ≤ r') : I.toParitySystem.known r ⊆ I.toParitySystem.known r' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Set.subset_union_left

lemma hasConflict_mono {r r' : ℕ} (h : r ≤ r') (hc : I.toParitySystem.HasConflict r) :
    I.toParitySystem.HasConflict r' := by
  obtain ⟨X, h0, h1⟩ := hc
  exact ⟨X, known_mono I h h0, known_mono I h h1⟩

lemma hasConflict_of_conflictRound {τ : ℕ} (h : I.conflictRound = τ) :
    I.toParitySystem.HasConflict τ := by
  classical
  by_contra hne
  have hex : ∃ r, I.toParitySystem.HasConflict r := by
    by_contra hno
    push Not at hno
    have : I.conflictRound = ⊤ := by
      simp [ImplicitParitySystem.conflictRound, ParitySystem.conflictRound, hno]
    rw [this] at h
    exact ENat.top_ne_natCast τ h
  let r₀ := Nat.find hex
  have hle : I.conflictRound ≤ r₀ := iInf₂_le r₀ (Nat.find_spec hex)
  have hge : (r₀ : ℕ∞) ≤ I.conflictRound := le_iInf₂ fun r hr => by
    exact_mod_cast Nat.find_min' hex hr
  have : (r₀ : ℕ∞) = τ := le_antisymm hge hle |>.symm ▸ h
  have hτ : r₀ = τ := by exact_mod_cast this
  exact hne (hτ ▸ Nat.find_spec hex)

lemma not_hasConflict_of_lt {r : ℕ} (h : (r : ℕ∞) + 1 ≤ I.conflictRound) :
    ¬ I.toParitySystem.HasConflict r := by
  intro hc
  have h1 : I.conflictRound ≤ r := iInf₂_le r hc
  have h2 : (r : ℕ∞) < r + 1 := by exact_mod_cast Nat.lt_succ_self r
  exact absurd (h.trans h1) (not_le.mpr h2)

/-- The equation of schema `e` at an allowed address is an equation of the parity system. -/
lemma equation_mem (e : Fin I.schemas.length) {a : Fin k → BlockCoord ℓ} (ha : IsAddress a)
    (hs : supp a ⊆ dom I e) : (sch I e).equation a ∈ I.toParitySystem.equations :=
  ⟨sch I e, sch_mem I e, a, ha, hs, rfl⟩

/-- One round of unit propagation along an equation of schema `e`. -/
lemma infer (e : Fin I.schemas.length) {a : Fin k → BlockCoord ℓ} (ha : IsAddress a)
    (hs : supp a ⊆ dom I e) (i₀ : Fin (arity (sch I e))) (b : Fin (arity (sch I e)) → ZMod 2)
    {r : ℕ} (hb : ∀ i, i ≠ i₀ → (argVar I e i a, b i) ∈ I.toParitySystem.known r) :
    (argVar I e i₀ a, ∑ i ∈ Finset.univ.erase i₀, b i) ∈ I.toParitySystem.known (r + 1) := by
  classical
  right
  refine ⟨_, equation_mem I e ha hs, ?_, ?_⟩
  · rw [equation_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · let bF : Fin I.numLocations × (Fin k → BlockCoord ℓ) → ZMod 2 := fun X =>
      if h : ∃ i, argVar I e i a = X then b h.choose else 0
    have hbF : ∀ i, bF (argVar I e i a) = b i := by
      intro i
      have h : ∃ i', argVar I e i' a = argVar I e i a := ⟨i, rfl⟩
      simp only [bF, dif_pos h]
      rw [argVar_injective I e a h.choose_spec]
    refine ⟨bF, fun Y hY hne => ?_, ?_⟩
    · rw [equation_eq] at hY
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hY
      rw [show (argLoc (sch I e) i, (argPerm (sch I e) i).act a) = argVar I e i a from rfl, hbF]
      exact hb i fun h => hne (by rw [h]; rfl)
    · rw [equation_eq]
      have : (Finset.univ.image fun i => argVar I e i a).erase (argVar I e i₀ a) =
          (Finset.univ.erase i₀).image fun i => argVar I e i a := by
        rw [Finset.image_erase (argVar_injective I e a)]
      simp only [show (fun i => (argLoc (sch I e) i, (argPerm (sch I e) i).act a)) =
        fun i => argVar I e i a from rfl]
      rw [this, Finset.sum_image fun x _ y _ h => argVar_injective I e a h]
      exact Finset.sum_congr rfl fun i _ => (hbF i).symm

/-- A fact derived in round `r + 1` was known before or is inferred along a schema equation
from facts of round `r`. -/
lemma known_succ_cases {r : ℕ} {X : Fin I.numLocations × (Fin k → BlockCoord ℓ)} {b : ZMod 2}
    (h : (X, b) ∈ I.toParitySystem.known (r + 1)) :
    (X, b) ∈ I.toParitySystem.known r ∨
      ∃ e a, IsAddress a ∧ supp a ⊆ dom I e ∧ ∃ i₀, X = argVar I e i₀ a ∧
        ∃ bf : Fin (arity (sch I e)) → ZMod 2,
          (∀ i, i ≠ i₀ → (argVar I e i a, bf i) ∈ I.toParitySystem.known r) ∧
          b = ∑ i ∈ Finset.univ.erase i₀, bf i := by
  classical
  rcases h with h | ⟨h, ⟨s, hs, a, ha, hsa, rfl⟩, hXh, bF, hbF, hsum⟩
  · exact Or.inl h
  right
  obtain ⟨e, rfl⟩ := exists_sch I hs
  change X ∈ (sch I e).equation a at hXh
  change ∀ Y ∈ (sch I e).equation a, Y ≠ X → (Y, bF Y) ∈ I.toParitySystem.known r at hbF
  rw [equation_eq] at hXh
  obtain ⟨i₀, -, hX⟩ := Finset.mem_image.mp hXh
  refine ⟨e, a, ha, hsa, i₀, hX.symm, fun i => bF (argVar I e i a), fun i hi => ?_, ?_⟩
  · apply hbF
    · rw [equation_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · intro h; apply hi
      exact argVar_injective I e a (h.trans hX.symm)
  · simp only at hsum
    rw [hsum, equation_eq]
    have : (Finset.univ.image fun i => argVar I e i a).erase (X) =
        (Finset.univ.erase i₀).image fun i => argVar I e i a := by
      rw [← hX]
      exact (Finset.image_erase (argVar_injective I e a) _ _).symm
    simp only [show (fun i => (argLoc (sch I e) i, (argPerm (sch I e) i).act a)) =
      fun i => argVar I e i a from rfl]
    rw [this, Finset.sum_image fun x _ y _ h => argVar_injective I e a h]

/-- Known facts concern addresses supported in the coordinate domain of their location. -/
lemma known_valid {r : ℕ} {X : Fin I.numLocations × (Fin k → BlockCoord ℓ)} {b : ZMod 2}
    (h : (X, b) ∈ I.toParitySystem.known r) : IsAddress X.2 ∧ supp X.2 ⊆ I.domain X.1 := by
  induction r generalizing X b with
  | zero =>
    obtain ⟨_, -, -, h1, h2⟩ := h
    exact ⟨h1, h2⟩
  | succ r ih =>
    rcases known_succ_cases I h with h | ⟨e, a, ha, hsa, i₀, rfl, -⟩
    · exact ih h
    · refine ⟨isAddress_act _ ha, ?_⟩
      simp only [argVar]
      rw [supp_act]
      intro c hc
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      exact argPerm_mem (sch_wf I e) (hsa hd) i₀

end Lax119563Proofs.Matrix
