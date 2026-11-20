import Lax119563Proofs.Matrix.Codes

/-!
# Block-induced permutations, partial seeds and row-space duality

* the action of block-induced permutations on vectors and addresses,
* the extension of partial seeds (Lemma "Extending partial seeds"),
* the duality between the row space of the check matrix and short codewords.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ}

/-! ### Block-induced permutations -/

/-- A block-induced permutation as an equivalence of coordinates. -/
def bpEquiv (P : BlockPerm k ℓ) : Coord k ℓ ≃ Coord k ℓ where
  toFun := P.apply
  invFun c := (P.perm.symm c.1, c.2 - P.shift (P.perm.symm c.1))
  left_inv c := by simp [BlockPerm.apply]
  right_inv c := by simp [BlockPerm.apply]

@[simp] lemma bpEquiv_apply (P : BlockPerm k ℓ) (c : Coord k ℓ) :
    bpEquiv P c = P.apply c := rfl

lemma bp_apply_injective (P : BlockPerm k ℓ) : Function.Injective P.apply :=
  (bpEquiv P).injective

/-- The image `P y` of a vector, `(P y)(P c) = y c`. -/
def permVec (P : BlockPerm k ℓ) (y : Vec k ℓ) : Vec k ℓ := fun c => y ((bpEquiv P).symm c)

lemma dot_permVec (P : BlockPerm k ℓ) (y z : Vec k ℓ) :
    dot (permVec P y) z = ∑ c, y c * z (P.apply c) := by
  rw [dot, ← Equiv.sum_comp (bpEquiv P)]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [permVec, bpEquiv_apply]
  rw [← bpEquiv_apply, Equiv.symm_apply_apply]

lemma blockSum_permVec (P : BlockPerm k ℓ) (y : Vec k ℓ) (i : Fin k) :
    blockSum (permVec P y) (P.perm i) = blockSum y i := by
  simp only [blockSum, permVec, bpEquiv, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply]
  exact Fintype.sum_equiv (Equiv.subRight (P.shift i)) _ _ (fun b => rfl)

lemma blockSum_permVec' (P : BlockPerm k ℓ) (y : Vec k ℓ) (i : Fin k) :
    blockSum (permVec P y) i = blockSum y (P.perm.symm i) := by
  rw [← blockSum_permVec P y (P.perm.symm i), Equiv.apply_symm_apply]

lemma isCode_permVec (hk : 0 < k) (P : BlockPerm k ℓ) {y : Vec k ℓ} (hy : IsCode y) :
    IsCode (permVec P y) := by
  rw [isCode_iff hk] at hy ⊢
  obtain ⟨h1, h2⟩ := hy
  refine ⟨fun i => by rw [blockSum_permVec', blockSum_permVec', h1 (P.perm.symm i), h1 (P.perm.symm _)], fun t => ?_⟩
  have e : ∑ c, permVec P y c * c.2 t = dot (permVec P y) (fun c => c.2 t) := rfl
  rw [e, dot_permVec]
  simp only [BlockPerm.apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, h2 t, zero_add]
  rw [sum_coord]
  have : ∀ i, ∑ b, y (i, b) * P.shift i t = blockSum y i * P.shift i t := by
    intro i; rw [blockSum, Finset.sum_mul]
  simp_rw [this, h1]
  rw [← Finset.mul_sum]
  have := congrFun P.sum_shift t
  simp only [Finset.sum_apply, Pi.zero_apply] at this
  rw [this, mul_zero]

lemma suppIn_permVec (P : BlockPerm k ℓ) {y : Vec k ℓ} {J : Finset (Coord k ℓ)}
    (hy : SuppIn y J) : SuppIn (permVec P y) (J.image P.apply) := by
  intro c hc
  apply hy
  intro hJ
  apply hc
  exact Finset.mem_image.mpr ⟨_, hJ, by simp [← bpEquiv_apply]⟩

lemma isAddress_act (P : BlockPerm k ℓ) {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) :
    IsAddress (P.act a) := by
  unfold IsAddress BlockPerm.act
  rw [Finset.sum_add_distrib]
  rw [Equiv.sum_comp P.perm.symm a, Equiv.sum_comp P.perm.symm P.shift, ha, P.sum_shift,
    add_zero]

lemma supp_act (P : BlockPerm k ℓ) (a : Fin k → BlockCoord ℓ) :
    supp (P.act a) = (supp a).image P.apply := by
  ext c
  simp only [mem_supp_iff, Finset.mem_image, BlockPerm.act, BlockPerm.apply]
  constructor
  · intro h
    refine ⟨(P.perm.symm c.1, a (P.perm.symm c.1)), rfl, ?_⟩
    ext <;> simp [← h]
  · rintro ⟨d, hd, rfl⟩
    simp [hd]

lemma ind_act (P : BlockPerm k ℓ) (a : Fin k → BlockCoord ℓ) :
    ind (P.act a) = permVec P (ind a) := by
  funext c
  simp only [ind, permVec, bpEquiv, Equiv.coe_fn_symm_mk, BlockPerm.act]
  congr 1
  apply propext
  constructor
  · intro h; rw [h]; simp
  · intro h; rw [← h]; simp

/-- The value `(P a) · z` of a permuted address as a sum over the support of `a`. -/
lemma dot_ind_act (P : BlockPerm k ℓ) (a : Fin k → BlockCoord ℓ) (z : Vec k ℓ) :
    dot (ind (P.act a)) z = ∑ i, z (P.apply (i, a i)) := by
  rw [ind_act, dot_permVec, sum_coord]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (a i)]
  · simp [ind]
  · intro b _ hb; simp [ind, hb]
  · simp

/-! ### Partial seeds -/

/-- The seed `z` annihilates every block-even codeword supported in `J`. -/
def EvenKills (z : Vec k ℓ) (J : Finset (Coord k ℓ)) : Prop :=
  ∀ y, IsCode y → (∀ i, blockSum y i = 0) → SuppIn y J → dot y z = 0

lemma EvenKills.mono {z : Vec k ℓ} {J J' : Finset (Coord k ℓ)} (h : EvenKills z J)
    (hJ : J' ⊆ J) : EvenKills z J' :=
  fun y hy he hs => h y hy he fun c hc => hs c fun h' => hc (hJ h')

lemma dot_update (y z : Vec k ℓ) (c : Coord k ℓ) (β : ZMod 2) :
    dot y (Function.update z c β) = dot y (Function.update z c 0) + y c * β := by
  simp only [dot]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), ← Finset.add_sum_erase _ _
    (Finset.mem_univ c)]
  simp only [Function.update_self]
  have : ∑ x ∈ Finset.univ.erase c, y x * Function.update z c β x =
      ∑ x ∈ Finset.univ.erase c, y x * Function.update z c 0 x :=
    Finset.sum_congr rfl fun x hx => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hx),
        Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this]; ring

lemma suppIn_insert_of_zero {y : Vec k ℓ} {J : Finset (Coord k ℓ)} {c : Coord k ℓ}
    (h : SuppIn y (insert c J)) (hc : y c = 0) : SuppIn y J := by
  intro d hd
  by_cases hdc : d = c
  · rw [hdc]; exact hc
  · exact h d (by simp [hdc, hd])

/-- **Extending partial seeds.** A seed on `J` annihilating block-even codewords extends to
`J ∪ {c}`, with any prescribed value on the address supported there that uses `c`. -/
lemma extend_seed (hk : 0 < k) {J : Finset (Coord k ℓ)} {c : Coord k ℓ} (hcJ : c ∉ J)
    (hcard : (insert c J).card ≤ k + 1) {z : Vec k ℓ} (hz : EvenKills z J) (p : ZMod 2) :
    ∃ β : ZMod 2, EvenKills (Function.update z c β) (insert c J) ∧
      ∀ a, IsAddress a → supp a ⊆ insert c J → c ∈ supp a →
        dot (ind a) (Function.update z c β) = p := by
  classical
  -- block-even codewords not using `c` are handled by `hz`
  have hold : ∀ β : ZMod 2, ∀ y, IsCode y → (∀ i, blockSum y i = 0) →
      SuppIn y (insert c J) → y c = 0 → dot y (Function.update z c β) = 0 := by
    intro β y hy he hs hc
    rw [dot_update, hc, zero_mul, add_zero]
    have hs' := suppIn_insert_of_zero hs hc
    rw [dot_congr_suppIn hs' (z' := z) fun d hd =>
      Function.update_of_ne (fun h => hcJ (by rw [← h]; exact hd)) _ _]
    exact hz y hy he hs'
  by_cases h0 : ∃ y0, IsCode y0 ∧ (∀ i, blockSum y0 i = 0) ∧ SuppIn y0 (insert c J) ∧ y0 c = 1
  · obtain ⟨y0, hy0, he0, hs0, hc0⟩ := h0
    refine ⟨dot y0 (Function.update z c 0), fun y hy he hs => ?_, fun a ha hsa hca => ?_⟩
    · rcases zmod2_eq_zero_or_one (y c) with hc | hc
      · exact hold _ y hy he hs hc
      · have hsum := hold (dot y0 (Function.update z c 0)) (y + y0) (hy.add hy0)
          (fun i => by rw [blockSum_add, he, he0, add_zero])
          (fun d hd => by simp [hs d hd, hs0 d hd]) (by simp [hc, hc0, zmod2_add_self])
        rw [dot_add_left] at hsum
        have h2 : dot y0 (Function.update z c (dot y0 (Function.update z c 0))) = 0 := by
          rw [dot_update, hc0, one_mul, zmod2_add_self]
        rw [h2, add_zero] at hsum
        exact hsum
    · exfalso
      obtain ⟨a', ha', he'⟩ := exists_address_of_odd hk (y := ind a + y0) (J := insert c J)
        ((isCode_ind hk ha).add hy0) (fun i => by rw [blockSum_add, blockSum_ind, he0, add_zero])
        (fun d hd => by
          have : ind a d = 0 := ind_apply_eq_zero.mpr fun h => hd (hsa h)
          simp [this, hs0 d hd]) hcard
      have hsa' : supp a' ⊆ insert c J := by
        rw [← suppIn_ind, ← he']
        intro d hd
        have : ind a d = 0 := ind_apply_eq_zero.mpr fun h => hd (hsa h)
        simp [this, hs0 d hd]
      have := address_unique ha ha' hcard hsa hsa'
      subst this
      have := congrFun he' c
      simp only [Pi.add_apply, hc0] at this
      have h' : ind a c + 1 = ind a c + 0 := by rw [this, add_zero]
      exact one_ne_zero (add_left_cancel h')
  · push Not at h0
    have heven : EvenKills (Function.update z c 0) (insert c J) ∧
        ∀ β, EvenKills (Function.update z c β) (insert c J) := by
      refine ⟨fun y hy he hs => hold 0 y hy he hs ?_, fun β y hy he hs => hold β y hy he hs ?_⟩
      · rcases zmod2_eq_zero_or_one (y c) with hc | hc
        · exact hc
        · exact absurd hc (h0 y hy he hs)
      · rcases zmod2_eq_zero_or_one (y c) with hc | hc
        · exact hc
        · exact absurd hc (h0 y hy he hs)
    by_cases h1 : ∃ a, IsAddress a ∧ supp a ⊆ insert c J ∧ c ∈ supp a
    · obtain ⟨a, ha, hsa, hca⟩ := h1
      refine ⟨p + dot (ind a) (Function.update z c 0), heven.2 _, fun a' ha' hsa' hca' => ?_⟩
      have := address_unique ha ha' hcard hsa hsa'
      subst this
      rw [dot_update, ind_apply_eq_one.mpr hca, one_mul, add_comm p, ← add_assoc,
        zmod2_add_self, zero_add]
    · push Not at h1
      exact ⟨0, heven.2 0, fun a ha hsa hca => absurd hca (h1 a ha hsa)⟩

/-! ### Duality between the row space and short codewords -/

/-- A vector orthogonal to all codewords supported in `J` agrees on `J` with a sum of rows of
the check matrix. -/
lemma exists_rowComb (J : Finset (Coord k ℓ)) (t : Vec k ℓ)
    (h : ∀ y, IsCode y → SuppIn y J → dot y t = 0) :
    ∃ μ : Row k ℓ → ZMod 2, ∀ c ∈ J, ∑ j, μ j * checkMatrix k ℓ j c = t c := by
  classical
  let f : (J → ZMod 2) →ₗ[ZMod 2] (Row k ℓ → ZMod 2) :=
    { toFun := fun x j => ∑ c : J, checkMatrix k ℓ j c * x c
      map_add' := fun x x' => by
        funext j; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        funext j; simp [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  let φ : Module.Dual (ZMod 2) (J → ZMod 2) :=
    { toFun := fun x => ∑ c : J, t c * x c
      map_add' := fun x x' => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  let ext : (J → ZMod 2) → Vec k ℓ := fun x c => if hc : c ∈ J then x ⟨c, hc⟩ else 0
  have hext_supp : ∀ x, SuppIn (ext x) J := fun x c hc => by simp [ext, hc]
  have hext_sum : ∀ (x : J → ZMod 2) (g : Coord k ℓ → ZMod 2),
      ∑ c : J, g c * x c = ∑ c, g c * ext x c := by
    intro x g
    rw [← Finset.sum_subset (Finset.subset_univ J) (fun c _ hc => by simp [ext, hc])]
    rw [← Finset.sum_coe_sort J]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [ext]
  have hφ : φ ∈ (LinearMap.ker f).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    have hcode : IsCode (ext x) := by
      intro j
      have := congrFun (LinearMap.mem_ker.mp hx) j
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      rw [hext_sum x (fun c => checkMatrix k ℓ j c)] at this
      exact this
    have := h _ hcode (hext_supp x)
    show ∑ c : J, t c * x c = 0
    rw [hext_sum x (fun c => t c)]
    rw [← this, dot]
    simp [mul_comm]
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hφ
  obtain ⟨ψ, hψ⟩ := hφ
  refine ⟨fun j => ψ (fun j' => if j = j' then 1 else 0), fun c hc => ?_⟩
  have h1 := LinearMap.congr_fun hψ (fun c' => if c' = ⟨c, hc⟩ then 1 else 0)
  rw [LinearMap.dualMap_apply] at h1
  have h2 : f (fun c' => if c' = ⟨c, hc⟩ then 1 else 0) = fun j => checkMatrix k ℓ j c := by
    funext j
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h2, LinearMap.pi_apply_eq_sum_univ] at h1
  change _ = ∑ c' : J, t c' * (if c' = ⟨c, hc⟩ then 1 else 0) at h1
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, mul_comm]

end Lax119563Proofs.Matrix
