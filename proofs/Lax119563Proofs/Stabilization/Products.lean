import Lax119563Proofs.Stabilization.Chains

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
