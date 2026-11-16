import Lax119563Proofs.RowSpace.Shifts
import Lax119563Proofs.Matrix.ExtendSeeds

/-!
# Seed descriptions and the local extension lemma

`DGood A D`: the description `D` is a seed description for the set of classes `A`
(initialized seeds, masks in the row spaces, the mask-sum condition on the pebbled schema
coordinates, partial seeds annihilating block-even codewords). `Realizes A D val`: the
description realizes the values `val` on the variables exposed for `A`.

**Local extension** (paper, Lemma "Local extension"): if `|A| ≤ k` and `val` satisfies the
equations exposed for `A ∪ {X}` and agrees with the initialization, a description realizing
`val` on `A` extends to one on `A ∪ {X}` realizing `val` and keeping the translation of every
class of `A`. No propagation rounds are involved.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-! ### Classes -/

lemma mem_ite_empty {α : Type*} {p : Prop} [Decidable p] {s : Finset α} {x : α} :
    x ∈ (if p then s else ∅) ↔ p ∧ x ∈ s := by
  split <;> simp_all

lemma mem_classes_coord {v : Fin I.numLocations} {c : Coord k ℓ} :
    (Cls.coord v c : ICls I) ∈ classes I ↔ c ∈ I.domain v := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]

lemma mem_classes_sum {e : Fin I.schemas.length} {c : Coord k ℓ} :
    (Cls.sum e c : ICls I) ∈ classes I ↔ isTern (sch I e) = true ∧ c ∈ dom I e := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]

lemma mem_classes_junc {e : Fin I.schemas.length} {c : Coord k ℓ} :
    (Cls.junc e c : ICls I) ∈ classes I ↔ isTern (sch I e) = true ∧ c ∈ dom I e := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]

lemma mem_classes_track {e : Fin I.schemas.length} {h : ℕ} {c : Coord k ℓ} :
    (Cls.track e h c : ICls I) ∈ classes I ↔ (1 ≤ h ∧ h ≤ k + 1) ∧ c ∈ dom I e := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]
  constructor
  · rintro ⟨a, b, h, rfl⟩; exact h
  · intro h; exact ⟨c.1, c.2, h, rfl⟩

lemma mem_classes_upd {e : Fin I.schemas.length} {h : ℕ} {c : Coord k ℓ} :
    (Cls.upd e h c : ICls I) ∈ classes I ↔ (1 ≤ h ∧ h ≤ k + 2) ∧ c ∈ dom I e := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]
  constructor
  · rintro ⟨a, b, h, rfl⟩; exact h
  · intro h; exact ⟨c.1, c.2, h, rfl⟩

lemma mem_classes_coef {e : Fin I.schemas.length} {h : ℕ} :
    (Cls.coef e h : ICls I) ∈ classes I ↔ 1 ≤ h ∧ h ≤ k + 2 := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]

lemma link_not_mem {e : Fin I.schemas.length} {c : Coord k ℓ} :
    (Cls.link e c : ICls I) ∉ classes I := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]

lemma inner_dom {X : ICls I} (hX : X ∈ classes I) {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : Lax119563Proofs.Matrix.inner X = some (e, c)) : c ∈ dom I e := by
  cases X <;> simp only [Lax119563Proofs.Matrix.inner, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · exact (mem_classes_sum.mp hX).2
  · exact (mem_classes_junc.mp hX).2
  · exact absurd hX link_not_mem
  · exact (mem_classes_track.mp hX).2
  · exact (mem_classes_upd.mp hX).2

lemma Isch_sub_dom {A : Finset (ICls I)} (hA : A ⊆ classes I) (e : Fin I.schemas.length) :
    Isch A e ⊆ dom I e := by
  intro c hc
  obtain ⟨X, hX, h⟩ := mem_Isch.mp hc
  exact inner_dom (hA hX) h

lemma Iloc_sub_dom {A : Finset (ICls I)} (hA : A ⊆ classes I) (v : Fin I.numLocations) :
    Iloc A v ⊆ I.domain v := by
  intro d hd0
  obtain ⟨X, hX, hd⟩ := Finset.mem_biUnion.mp hd0
  cases hi : Lax119563Proofs.Matrix.inner X with
  | some p =>
    obtain ⟨e, c⟩ := p
    rw [locContrib_of_inner hi] at hd
    obtain ⟨i, rfl, rfl⟩ := mem_argContrib.mp hd
    exact argPerm_mem (sch_wf I e) (inner_dom (hA hX) hi) i
  | none =>
    rcases inner_none hi with ⟨v', c, rfl⟩ | ⟨e, σ, rfl⟩
    · simp only [locContrib] at hd
      split at hd
      · next h => subst h; rw [Finset.mem_singleton] at hd; subst hd
                  exact mem_classes_coord.mp (hA hX)
      · simp at hd
    · simp [locContrib] at hd

/-! ### Descriptions for sets of classes -/

/-- Values of the variables `X_{v,a}`. -/
abbrev Val (I : ImplicitParitySystem k ℓ) := Fin I.numLocations × (Fin k → BlockCoord ℓ) → ZMod 2

/-- `D` is a seed description for the classes `A`. -/
structure DGood (A : Finset (ICls I)) (D : RDesc I) : Prop where
  init : InitOK D
  mask : MaskOK D
  ms : ∀ e, ∀ c ∈ Isch A e, MS D e c
  even : ∀ v, EvenKills (D.z v) (Iloc A v)

/-- `D` realizes `val` on the variables exposed for `A`. -/
def Realizes (A : Finset (ICls I)) (D : RDesc I) (val : Val I) : Prop :=
  ∀ v a, IsAddress a → supp a ⊆ Iloc A v → dot (ind a) (D.z v) = val (v, a)

/-- `val` satisfies the equations exposed for `A`. -/
def SatEqs (A : Finset (ICls I)) (val : Val I) : Prop :=
  ∀ e a, IsAddress a → supp a ⊆ Isch A e → ∑ i, val (argVar I e i a) = 0

/-- `val` agrees with the initialization on the variables exposed for `A`. -/
def InitAgree (A : Finset (ICls I)) (val : Val I) : Prop :=
  ∀ v a b, I.init v = some b → IsAddress a → supp a ⊆ Iloc A v → val (v, a) = b

lemma DGood.mono {A B : Finset (ICls I)} {D : RDesc I} (h : DGood A D) (hB : B ⊆ A) :
    DGood B D where
  init := h.init
  mask := h.mask
  ms e c hc := h.ms e c (Isch_mono hB e hc)
  even v := (h.even v).mono (Iloc_mono hB v)

lemma Realizes.mono {A B : Finset (ICls I)} {D : RDesc I} {val : Val I} (h : Realizes A D val)
    (hB : B ⊆ A) : Realizes B D val :=
  fun v a ha hs => h v a ha (hs.trans (Iloc_mono hB v))

/-- The initial description. -/
def rdesc0 (I : ImplicitParitySystem k ℓ) : RDesc I where
  z v := initSeed I v
  x _ _ := 0

lemma dgood_empty : DGood (∅ : Finset (ICls I)) (rdesc0 I) where
  init _ _ := rfl
  mask _ _ := zero_mem_maskSet I _
  ms e c hc := by simp [Isch] at hc
  even v := initSeed_evenKills v _

lemma realizes_empty (hk : 0 < k) (D : RDesc I) (val : Val I) :
    Realizes (∅ : Finset (ICls I)) D val := by
  intro v a _ hs
  exfalso
  have : (supp a).card = 0 := by
    rw [Finset.card_eq_zero]; simpa [Iloc] using hs
  rw [card_supp] at this; omega

/-! ### Translations depend only on the pebbled coordinates -/

lemma arg_mem_Iloc {A : Finset (ICls I)} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hc : c ∈ Isch A e) : (permU (sch I e)).apply c ∈ Iloc A (locU (sch I e)) ∧
      (permV (sch I e)).apply c ∈ Iloc A (locV (sch I e)) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_U (sch I e)
  obtain ⟨j, h3, h4⟩ := exists_arg_V (sch I e)
  have := Isch_args hc i
  have := Isch_args hc j
  simp_all

lemma rt0_congr {D D' : RDesc I} {A : Finset (ICls I)}
    (hz : ∀ v, ∀ c ∈ Iloc A v, D'.z v c = D.z v c) {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hc : c ∈ Isch A e) : rt0 D' e c = rt0 D e c := by
  simp only [rt0, hz _ _ (arg_mem_Iloc hc).1, hz _ _ (arg_mem_Iloc hc).2]

lemma bsum_congr {D D' : RDesc I} {A : Finset (ICls I)}
    (hz : ∀ v, ∀ c ∈ Iloc A v, D'.z v c = D.z v c) {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hc : c ∈ Isch A e) : bsum D' e c = bsum D e c :=
  Finset.sum_congr rfl fun i _ => hz _ _ (Isch_args hc i)

lemma msum_congr {D D' : RDesc I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hx : ∀ h, D'.x e h c = D.x e h c) (n : ℕ) : msum D' e c n = msum D e c n :=
  Finset.sum_congr rfl fun i _ => hx _

lemma rshift_congr {A : Finset (ICls I)} {D D' : RDesc I}
    (hz : ∀ v, ∀ c ∈ Iloc A v, D'.z v c = D.z v c)
    (hx : ∀ e h, ∀ c ∈ Isch A e, D'.x e h c = D.x e h c)
    (hc : ∀ e h, Cls.coef e h ∈ A → D'.x e h = D.x e h) {Y : ICls I} (hY : Y ∈ A) :
    rshift D' Y = rshift D Y := by
  have hin : ∀ e c, Lax119563Proofs.Matrix.inner Y = some (e, c) → c ∈ Isch A e :=
    fun e c h => mem_Isch.mpr ⟨Y, hY, h⟩
  cases Y with
  | coord v c =>
    have : c ∈ Iloc A v := Finset.mem_biUnion.mpr ⟨_, hY, by simp [locContrib]⟩
    simp [rshift, hz v c this]
  | sum e c => simp [rshift, rt0_congr hz (hin e c rfl)]
  | junc e c =>
    have h := arg_mem_Iloc (hin e c rfl)
    simp [rshift, hz _ _ h.1, hz _ _ h.2]
  | track e h c =>
    have h' := hin e c rfl
    simp [rshift, TT, rt0_congr hz h', msum_congr (fun h => hx e h c h')]
  | upd e h c =>
    have h' := hin e c rfl
    simp [rshift, TT, rt0_congr hz h', msum_congr (fun h => hx e h c h')]
  | coef e h => simp [rshift, hc e h hY]
  | link => rfl

/-! ### Extending one seed -/

/-- Extending the seed of one location from `J` to `J' ⊇ J` with `|J' \ J| ≤ 1`, prescribing
the values `f` on the addresses supported in `J'`. -/
lemma extend_seed_loc (hk : 0 < k) {v : Fin I.numLocations} {J J' : Finset (Coord k ℓ)}
    (hJ : J ⊆ J') (hJ1 : (J' \ J).card ≤ 1) (hcard : J'.card ≤ k + 1) {z : Vec k ℓ}
    (hz : (I.init v).isSome → z = initSeed I v) (heven : EvenKills z J)
    (f : (Fin k → BlockCoord ℓ) → ZMod 2)
    (hreal : ∀ a, IsAddress a → supp a ⊆ J → dot (ind a) z = f a)
    (hinit : ∀ a b, I.init v = some b → IsAddress a → supp a ⊆ J' → f a = b) :
    ∃ z' : Vec k ℓ, (∀ c ∈ J, z' c = z c) ∧ ((I.init v).isSome → z' = initSeed I v) ∧
      EvenKills z' J' ∧ ∀ a, IsAddress a → supp a ⊆ J' → dot (ind a) z' = f a := by
  classical
  cases hv : I.init v with
  | some b =>
    have hz' := hz (by simp [hv])
    refine ⟨z, fun _ _ => rfl, fun _ => hz', hz' ▸ initSeed_evenKills v _, fun a ha hs => ?_⟩
    rw [hz', dot_initSeed hv hk, hinit a b hv ha hs]
  | none =>
    by_cases hJJ : J' ⊆ J
    · have : J' = J := Finset.Subset.antisymm hJJ hJ
      subst this
      exact ⟨z, fun _ _ => rfl, fun h => by simp [hv] at h, heven, hreal⟩
    obtain ⟨d, hdJ', hdJ⟩ := Finset.not_subset.mp hJJ
    have hJ'eq : J' = insert d J := by
      refine Finset.Subset.antisymm (fun c hc => ?_) (Finset.insert_subset hdJ' hJ)
      by_cases hcJ : c ∈ J
      · exact Finset.mem_insert_of_mem hcJ
      · have h1 : c ∈ J' \ J := Finset.mem_sdiff.mpr ⟨hc, hcJ⟩
        have h2 : d ∈ J' \ J := Finset.mem_sdiff.mpr ⟨hdJ', hdJ⟩
        rw [Finset.card_le_one.mp hJ1 c h1 d h2]
        exact Finset.mem_insert_self _ _
    subst hJ'eq
    let p : ZMod 2 := if h : ∃ a, IsAddress a ∧ supp a ⊆ insert d J ∧ d ∈ supp a
      then f h.choose else 0
    obtain ⟨β, hβ1, hβ2⟩ := extend_seed hk hdJ hcard heven p
    have hagree : ∀ c ∈ J, Function.update z d β c = z c :=
      fun c hc => Function.update_of_ne (fun h => hdJ (by rw [← h]; exact hc)) _ _
    refine ⟨Function.update z d β, hagree, fun h => by simp [hv] at h, hβ1, fun a ha hs => ?_⟩
    by_cases hda : d ∈ supp a
    · have hex : ∃ a, IsAddress a ∧ supp a ⊆ insert d J ∧ d ∈ supp a := ⟨a, ha, hs, hda⟩
      rw [hβ2 a ha hs hda]
      simp only [p, dif_pos hex]
      rw [address_unique hex.choose_spec.1 ha hcard hex.choose_spec.2.1 hs]
    · have hsJ : supp a ⊆ J := fun c hc => by
        rcases Finset.mem_insert.mp (hs hc) with rfl | h
        · exact absurd hc hda
        · exact h
      rw [dot_congr_suppIn (suppIn_ind.mpr hsJ) (z' := z) hagree]
      exact hreal a ha hsJ

/-! ### Exposed equations -/

lemma maskSet_dot {e : Fin I.schemas.length} {x : Vec k ℓ} (hx : x ∈ maskSet I e) (hk : 0 < k)
    {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) (hs : supp a ⊆ dom I e) :
    dot (ind a) x = 0 := by
  obtain ⟨μ, -, rfl⟩ := Finset.mem_image.mp hx
  rw [dot_ind_left]
  have : ∀ i, maskOf I e μ (i, a i) = ∑ j, μ j * checkMatrix k ℓ j (i, a i) := fun i => by
    have hi : ((i, a i) : Coord k ℓ) ∈ dom I e :=
      hs ((mem_supp_iff (a := a) (c := (i, a i))).mpr rfl)
    simp only [maskOf, if_pos hi]
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.mul_sum, sum_row_supp hk ha, mul_zero]

/-- The sum of the argument values at an address equals its sum of `bsum`. -/
lemma sum_args_dot (D : RDesc I) (e : Fin I.schemas.length) (a : Fin k → BlockCoord ℓ) :
    ∑ i, dot (ind ((argPerm (sch I e) i).act a)) (D.z (argLoc (sch I e) i)) =
      dot (ind a) (bsum D e) := by
  simp_rw [dot_ind_act, dot_ind_left, bsum]
  exact Finset.sum_comm

/-- A description satisfies the equations of the addresses at which the mask-sum condition
holds. -/
lemma eq_of_MS (hk : 0 < k) {D : RDesc I} (hM : MaskOK D) {e : Fin I.schemas.length}
    {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) (hs : supp a ⊆ dom I e)
    (hms : ∀ c ∈ supp a, MS D e c) :
    ∑ i, dot (ind ((argPerm (sch I e) i).act a)) (D.z (argLoc (sch I e) i)) = 0 := by
  rw [sum_args_dot, dot_ind_eq_sum_supp]
  rw [Finset.sum_congr rfl fun c hc => (hms c hc).symm]
  simp only [msum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← dot_ind_eq_sum_supp]
  exact maskSet_dot (hM e _) hk ha hs

/-- Realized values satisfy the equations exposed for `A`. -/
lemma Realizes.sat (hk : 0 < k) {A : Finset (ICls I)} {D : RDesc I} {val : Val I}
    (hG : DGood A D) (hA : A ⊆ classes I) (hR : Realizes A D val) : SatEqs A val := by
  intro e a ha hs
  rw [← eq_of_MS hk hG.mask ha (hs.trans (Isch_sub_dom hA e)) fun c hc => hG.ms e c (hs hc)]
  refine Finset.sum_congr rfl fun i _ => (hR _ _ (isAddress_act _ ha) ?_).symm
  rw [supp_act]
  intro d hd
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
  exact Isch_args (hs hc) i

/-! ### The mask repair -/

lemma isCode_even_or_odd (hk : 0 < k) {y : Vec k ℓ} (hy : IsCode y) :
    (∀ i, blockSum y i = 0) ∨ ∀ i, blockSum y i = 1 := by
  rcases zmod2_eq_zero_or_one (blockSum y ⟨0, hk⟩) with h | h
  · exact Or.inl fun i => (hy.blockSum_eq hk i ⟨0, hk⟩).trans h
  · exact Or.inr fun i => (hy.blockSum_eq hk i ⟨0, hk⟩).trans h

/-- `bsum` of the extended seeds is orthogonal to every codeword supported in the new schema
coordinate set. -/
lemma bsum_orth (hk : 0 < k) {A' : Finset (ICls I)} {D : RDesc I} {val : Val I}
    (heven : ∀ v, EvenKills (D.z v) (Iloc A' v)) (hR : Realizes A' D val) (hsat : SatEqs A' val)
    (e : Fin I.schemas.length) (hcard : (Isch A' e).card ≤ k + 1) :
    ∀ y, IsCode y → SuppIn y (Isch A' e) → dot y (bsum D e) = 0 := by
  intro y hy hs
  rcases isCode_even_or_odd hk hy with he | ho
  · have : dot y (bsum D e) =
        ∑ i, dot (permVec (argPerm (sch I e) i) y) (D.z (argLoc (sch I e) i)) := by
      simp_rw [dot_permVec, dot, bsum, Finset.mul_sum]
      exact Finset.sum_comm
    rw [this]
    refine Finset.sum_eq_zero fun i _ => heven _ _ (isCode_permVec hk _ hy)
      (fun i' => by rw [blockSum_permVec', he]) ?_
    intro d hd
    apply suppIn_permVec _ hs
    intro hd'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd'
    exact hd (Isch_args hc i)
  · obtain ⟨a, ha, rfl⟩ := exists_address_of_odd hk hy ho hs hcard
    have hsa := suppIn_ind.mp hs
    rw [← sum_args_dot, ← hsat e a ha hsa]
    refine Finset.sum_congr rfl fun i _ => hR _ _ (isAddress_act _ ha) ?_
    rw [supp_act]
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
    exact Isch_args (hsa hc) i

/-- A mask in the row space correcting the mask sum at the new coordinate. -/
lemma exists_gamma {e : Fin I.schemas.length} {J : Finset (Coord k ℓ)} {c : Coord k ℓ}
    (hJ : insert c J ⊆ dom I e) {D : RDesc I} (hM : MaskOK D)
    (hms : ∀ c' ∈ J, MS D e c')
    (horth : ∀ y, IsCode y → SuppIn y (insert c J) → dot y (bsum D e) = 0) :
    ∃ γ ∈ maskSet I e, (∀ c' ∈ J, γ c' = 0) ∧ γ c = bsum D e c + msum D e c (k + 2) := by
  obtain ⟨μ, hμ⟩ := exists_rowComb (insert c J) (bsum D e) horth
  let xs : Vec k ℓ := ∑ i ∈ Finset.range (k + 2), D.x e (i + 1)
  have hxs : xs ∈ maskSet I e := by
    simp only [xs]
    induction (k + 2) with
    | zero => simpa using zero_mem_maskSet I e
    | succ n ih => rw [Finset.sum_range_succ]; exact add_mem_maskSet I ih (hM e _)
  have hxs_apply : ∀ c', xs c' = msum D e c' (k + 2) := fun c' => by
    simp [xs, msum, Finset.sum_apply]
  have hmask : ∀ c' ∈ insert c J, maskOf I e μ c' = bsum D e c' := fun c' hc' => by
    simp [maskOf, hJ hc', hμ c' hc']
  refine ⟨maskOf I e μ + xs, add_mem_maskSet I (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    hxs, fun c' hc' => ?_, ?_⟩
  · rw [Pi.add_apply, hmask c' (Finset.mem_insert_of_mem hc'), hxs_apply, hms c' hc',
      zmod2_self_add]
  · rw [Pi.add_apply, hmask c (Finset.mem_insert_self _ _), hxs_apply]

/-- Some stage of `e` has no pebbled mask class. -/
lemma exists_free_stage {A : Finset (ICls I)} (hcard : A.card ≤ k) (e : Fin I.schemas.length) :
    ∃ h, 1 ≤ h ∧ h ≤ k + 2 ∧ Cls.coef e h ∉ A := by
  by_contra hno
  push Not at hno
  have hsub : (Finset.Icc 1 (k + 2)).image (Cls.coef e) ⊆ A := by
    intro X hX
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hh
    exact hno h h1 h2
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b h => by cases h; rfl)] at this
  simp at this
  omega

/-! ### Local extension -/

lemma card_Iloc_insert (A : Finset (ICls I)) (X : ICls I) (v : Fin I.numLocations) :
    (Iloc (insert X A) v \ Iloc A v).card ≤ 1 := by
  rw [Iloc_insert]
  refine (Finset.card_le_card fun d hd => ?_).trans (card_locContrib_le X v)
  rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hd).1 with h | h
  · exact h
  · exact absurd h (Finset.mem_sdiff.mp hd).2

/-- **Local extension.** -/
theorem local_extend (hk : 2 ≤ k) {A : Finset (ICls I)} {X : ICls I} {D : RDesc I}
    (hG : DGood A D) (hA : A ⊆ classes I) (hX : X ∈ classes I) (hcard : A.card ≤ k)
    (val : Val I) (hreal : Realizes A D val) (hsat : SatEqs (insert X A) val)
    (hinit : InitAgree (insert X A) val) :
    ∃ D', DGood (insert X A) D' ∧ Realizes (insert X A) D' val ∧
      ∀ Y ∈ A, rshift D' Y = rshift D Y := by
  classical
  have hk0 : 0 < k := by omega
  have hA' : insert X A ⊆ classes I := Finset.insert_subset hX hA
  have hcard' : (insert X A).card ≤ k + 1 := (Finset.card_insert_le _ _).trans (by omega)
  -- seeds
  have hseed := fun v => extend_seed_loc (I := I) (v := v) hk0 (Iloc_mono (Finset.subset_insert X A) v)
    (card_Iloc_insert A X v) ((card_Iloc_le _ v).trans hcard') (hG.init v) (hG.even v)
    (fun a => val (v, a)) (fun a ha hs => hreal v a ha hs) (fun a b hb ha hs => hinit v a b hb ha hs)
  choose z' hz1 hz2 hz3 hz4 using hseed
  let D1 : RDesc I := ⟨z', D.x⟩
  have hD1init : InitOK D1 := fun v hv => hz2 v hv
  have hR1 : Realizes (insert X A) D1 val := fun v a ha hs => hz4 v a ha hs
  -- old mask-sum conditions survive the seed extension
  have hms1 : ∀ e, ∀ c ∈ Isch A e, MS D1 e c := fun e c hc => by
    have := hG.ms e c hc
    simp only [MS] at this ⊢
    rw [bsum_congr (D := D) (D' := D1) hz1 hc]
    exact this
  -- does `X` add a new schema coordinate?
  by_cases hnew : ∃ e c, Lax119563Proofs.Matrix.inner X = some (e, c) ∧ c ∉ Isch A e
  · obtain ⟨e, c, hXi, hcA⟩ := hnew
    have hIsch : ∀ e', Isch (insert X A) e' = if e = e' then insert c (Isch A e') else Isch A e' := by
      intro e'
      rw [Isch_insert, schContrib_of_inner hXi]
      by_cases he : e = e'
      · subst he; rw [if_pos rfl, if_pos rfl, Finset.insert_eq]
      · rw [if_neg he, if_neg he, Finset.empty_union]
    have hJe : Isch (insert X A) e = insert c (Isch A e) := by rw [hIsch e, if_pos rfl]
    obtain ⟨γ, hγ, hγ0, hγc⟩ := exists_gamma (D := D1) (c := c) (J := Isch A e)
      (hJe ▸ Isch_sub_dom hA' e) hG.mask (hms1 e)
      (hJe ▸ bsum_orth hk0 hz3 hR1 hsat e (hJe ▸ (card_Isch_le _ e).trans hcard'))
    obtain ⟨h₀, h₀1, h₀2, h₀A⟩ := exists_free_stage hcard e
    let x' : Fin I.schemas.length → ℕ → Vec k ℓ :=
      Function.update D.x e (Function.update (D.x e) h₀ (D.x e h₀ + γ))
    let D' : RDesc I := ⟨z', x'⟩
    have hx'e : ∀ h c', x' e h c' = D.x e h c' + if h = h₀ then γ c' else 0 := by
      intro h c'
      by_cases hh : h = h₀
      · subst hh; simp [x']
      · simp [x', hh]
    have hx'ne : ∀ e', e' ≠ e → x' e' = D.x e' := fun e' he => by simp [x', he]
    have hmsum : ∀ c', msum D' e c' (k + 2) = msum D e c' (k + 2) + γ c' := by
      intro c'
      simp only [msum, D', hx'e, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single (h₀ - 1) (fun b _ hb => by rw [if_neg (by omega)])
        (fun h => by simp at h; omega), if_pos (by omega)]
    refine ⟨D', ⟨hD1init, fun e' h => ?_, fun e' c' hc' => ?_, hz3⟩, hR1, fun Y hY => ?_⟩
    · show x' e' h ∈ maskSet I e'
      by_cases he : e' = e
      · subst he
        by_cases hh : h = h₀
        · subst hh; simp only [x', Function.update_self]
          exact add_mem_maskSet I (hG.mask _ _) hγ
        · simp only [x', Function.update_self, Function.update_of_ne hh]; exact hG.mask _ _
      · rw [hx'ne e' he]; exact hG.mask _ _
    · rw [hIsch e'] at hc'
      by_cases he : e = e'
      · subst he
        rw [if_pos rfl] at hc'
        simp only [MS, hmsum]
        show _ = bsum D1 e c'
        rcases Finset.mem_insert.mp hc' with rfl | hc'
        · rw [hγc, ← add_assoc, show msum D e c' (k + 2) = msum D1 e c' (k + 2) from rfl,
            add_comm (msum D1 e c' (k + 2)), add_assoc, zmod2_self_add, add_zero]
        · rw [hγ0 c' hc', add_zero]
          exact hms1 e c' hc'
      · rw [if_neg he] at hc'
        have := hms1 e' c' hc'
        simp only [MS] at this ⊢
        rw [msum_congr (D := D1) (D' := D') (fun h => by simp [D', hx'ne e' (Ne.symm he), D1])]
        exact this
    · refine rshift_congr hz1 (fun e' h c' hc' => ?_) (fun e' h hc => ?_) hY
      · by_cases he : e' = e
        · subst he; show x' e' h c' = _; rw [hx'e, hγ0 c' hc']; simp
        · simp [D', hx'ne e' he]
      · by_cases he : e' = e
        · subst he
          have hh : h ≠ h₀ := fun hh => h₀A (hh ▸ hc)
          simp [D', x', hh]
        · simp [D', hx'ne e' he]
  · push Not at hnew
    have hIsch : ∀ e', Isch (insert X A) e' = Isch A e' := by
      intro e'
      rw [Isch_insert]
      cases hXi : Lax119563Proofs.Matrix.inner X with
      | none => rw [schContrib_of_inner_none hXi]; simp
      | some p =>
        obtain ⟨e, c⟩ := p
        rw [schContrib_of_inner hXi]
        split
        · next he => subst he; simp [hnew e c hXi]
        · simp
    refine ⟨D1, ⟨hD1init, hG.mask, fun e c hc => hms1 e c (hIsch e ▸ hc), hz3⟩, hR1,
      fun Y hY => rshift_congr (D := D) (D' := D1) hz1 (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) hY⟩

end Lax119563Proofs.RowSpace
