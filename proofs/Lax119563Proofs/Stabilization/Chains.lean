import Lax119563Proofs.Stabilization.Defs

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

theorem mem_algStar {V : Submodule ℂ A} {h1 : (1 : A) ∈ V} {hV : StarClosed V} {x : A} :
    x ∈ algStar V h1 hV ↔ x ∈ alg V := Iff.rfl

theorem algStar_toSubmodule (V : Submodule ℂ A) (h1 : (1 : A) ∈ V) (hV : StarClosed V) :
    Subalgebra.toSubmodule (algStar V h1 hV).toSubalgebra = alg V := rfl

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

end Lax119563Proofs.Stabilization
