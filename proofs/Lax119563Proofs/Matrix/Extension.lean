import Lax119563Proofs.Matrix.ExtendSeeds

/-!
# The local extension lemma

From a description satisfying the invariant for the retained classes `A` (`|A| ≤ k`) and an
announced class `X`, we construct a description satisfying the invariant for `A ∪ {X}` with
one round less, without changing the translation of any retained class. For a new internal
coordinate the coefficients are repaired in a repetition untouched by `A`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-! ### Corrections of the coefficients in one repetition -/

/-- The correction of the coefficients: `μ` in repetition `h` of schema `e`. -/
def corrLam (hM : 0 < k - 1 + ℓ) (e : Fin I.schemas.length) (h : ℕ)
    (μ : Fin (k - 1) ⊕ Fin ℓ → ZMod 2) (e' : Fin I.schemas.length) (σ : ℕ) : ZMod 2 :=
  if e' = e ∧ σ / (k - 1 + ℓ) = h then μ (stepRow hM σ) else 0

lemma stepRow_add (hM : 0 < k - 1 + ℓ) (h j : ℕ) (hj : j < k - 1 + ℓ) :
    stepRow hM (h * (k - 1 + ℓ) + j) = finSumFinEquiv.symm ⟨j, hj⟩ := by
  simp only [stepRow]
  congr 2
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- The accumulated correction of column `c` up to stage `σ`. -/
lemma sum_corr (hk : 2 ≤ k) (e : Fin I.schemas.length) (h : ℕ)
    (μ : Fin (k - 1) ⊕ Fin ℓ → ZMod 2) (c : Coord k ℓ) (σ : ℕ) :
    (σ ≤ h * (k - 1 + ℓ) →
      ∑ σ' ∈ Finset.range σ, corrLam (I := I) (by omega) e h μ e σ' * ent σ' c = 0) ∧
    ((h + 1) * (k - 1 + ℓ) ≤ σ →
      ∑ σ' ∈ Finset.range σ, corrLam (I := I) (by omega) e h μ e σ' * ent σ' c =
        ∑ j, μ j * checkMatrix k ℓ j c) := by
  have hM : 0 < k - 1 + ℓ := by omega
  have hlow : ∀ σ' < h * (k - 1 + ℓ), corrLam (I := I) hM e h μ e σ' = 0 := by
    intro σ' hσ'
    simp only [corrLam, true_and]
    rw [if_neg]
    exact ((Nat.div_lt_iff_lt_mul hM).mpr hσ').ne
  have hhigh : ∀ σ', (h + 1) * (k - 1 + ℓ) ≤ σ' → corrLam (I := I) hM e h μ e σ' = 0 := by
    intro σ' hσ'
    simp only [corrLam, true_and]
    rw [if_neg]
    exact (Nat.lt_of_lt_of_le (Nat.lt_succ_self h) ((Nat.le_div_iff_mul_le hM).mpr hσ')).ne'
  constructor
  · intro hσ
    exact Finset.sum_eq_zero fun σ' hσ' => by
      rw [hlow σ' (lt_of_lt_of_le (Finset.mem_range.mp hσ') hσ), zero_mul]
  · intro hσ
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hσ
    rw [Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range t) fun x _ => by
      rw [hhigh _ (Nat.le_add_right _ _), zero_mul], add_zero]
    rw [show (h + 1) * (k - 1 + ℓ) = h * (k - 1 + ℓ) + (k - 1 + ℓ) by ring, Finset.sum_range_add,
      Finset.sum_eq_zero (s := Finset.range (h * (k - 1 + ℓ))) fun x hx => by
        rw [hlow _ (Finset.mem_range.mp hx), zero_mul], zero_add]
    rw [Finset.sum_range]
    have : ∀ j : Fin (k - 1 + ℓ),
        corrLam (I := I) hM e h μ e (h * (k - 1 + ℓ) + j) * ent (h * (k - 1 + ℓ) + j) c =
          μ (finSumFinEquiv.symm j) * checkMatrix k ℓ (finSumFinEquiv.symm j) c := by
      intro j
      have hdiv : (h * (k - 1 + ℓ) + j) / (k - 1 + ℓ) = h := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt j.2, zero_add]
      simp only [corrLam, true_and, ent_eq hk]
      rw [if_pos hdiv, stepRow_add hM h j j.2]
    simp_rw [this]
    exact Equiv.sum_comp finSumFinEquiv.symm fun j => μ j * checkMatrix k ℓ j c

/-! ### Untouched repetitions -/

/-- The schema and repetition touched by a class. -/
def touch : ICls I → Option (Fin I.schemas.length × ℕ)
  | .track e σ _ => some (e, σ / (k - 1 + ℓ))
  | .upd e σ _ => some (e, σ / (k - 1 + ℓ))
  | .coef e σ => some (e, σ / (k - 1 + ℓ))
  | _ => none

/-- The repetitions of schema `e` touched by a class. -/
def touchSet (e : Fin I.schemas.length) (Y : ICls I) : Finset ℕ :=
  match touch Y with
  | some (e', h) => if e' = e then {h} else ∅
  | none => ∅

lemma card_touchSet_le (e : Fin I.schemas.length) (Y : ICls I) : (touchSet e Y).card ≤ 1 := by
  unfold touchSet
  split
  · split <;> simp
  · simp

lemma exists_untouched {A : Finset (ICls I)} (hcard : A.card ≤ k) (e : Fin I.schemas.length) :
    ∃ h < k + 1, ∀ Y ∈ A, touch Y ≠ some (e, h) := by
  classical
  let S := A.biUnion (touchSet e)
  have hS : S.card ≤ k := by
    refine (Finset.card_biUnion_le).trans (le_trans ?_ hcard)
    simpa using Finset.sum_le_sum fun Y (_ : Y ∈ A) => card_touchSet_le e Y
  obtain ⟨h, hh, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := S) (t := Finset.range (k + 1)) (by simp; omega)
  refine ⟨h, Finset.mem_range.mp hh, fun Y hY hYt => hnot ?_⟩
  exact Finset.mem_biUnion.mpr ⟨Y, hY, by simp [touchSet, hYt]⟩

lemma lt_or_ge_of_div_ne {σ h M : ℕ} (hM : 0 < M) (hne : σ / M ≠ h) :
    σ + 1 ≤ h * M ∨ (h + 1) * M ≤ σ := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · left
    have := (Nat.div_lt_iff_lt_mul hM).mp hlt
    omega
  · right
    exact (Nat.le_div_iff_mul_le hM).mp hgt

/-! ### The extension lemma -/

variable {r : ℕ} {A : Finset (ICls I)} {D : Desc I}

lemma good_of_contrib (hG : Good (r + 1) A D) {X : ICls I}
    (hloc : ∀ v, locContrib X v ⊆ Iloc A v) (hsch : ∀ e, schContrib X e ⊆ Isch A e) :
    Good r (insert X A) D := by
  have h1 : ∀ v, Iloc (insert X A) v = Iloc A v := fun v => by
    rw [Iloc_insert, Finset.union_eq_right.mpr (hloc v)]
  have h2 : ∀ e, Isch (insert X A) e = Isch A e := fun e => by
    rw [Isch_insert, Finset.union_eq_right.mpr (hsch e)]
  have hG' := hG.mono (Nat.le_succ r) le_rfl
  exact ⟨hG'.init, fun e c hc => hG'.ms e c (h2 e ▸ hc), fun v => (h1 v).symm ▸ hG'.even v,
    fun v a b ha hs hb => hG'.agree v a b ha ((h1 v) ▸ hs) hb, hG'.noConflict⟩

/-- **Local extension.** -/
theorem extend (hk : 2 ≤ k) (hG : Good (r + 1) A D) (hA : AllValid A) (hcard : A.card ≤ k)
    {X : ICls I} (hX : ClsValid I X) :
    ∃ D' : Desc I, Good r (insert X A) D' ∧ ∀ Y ∈ A, shift D' Y = shift D Y := by
  classical
  have hM : 0 < k - 1 + ℓ := by omega
  have hnc : ¬ I.toParitySystem.HasConflict r :=
    fun h => hG.noConflict (hasConflict_mono I (Nat.le_succ r) h)
  cases hin : inner X with
  | none =>
    rcases inner_none hin with ⟨v, d, rfl⟩ | ⟨e, σ, rfl⟩
    swap
    · -- a coefficient class
      exact ⟨D, good_of_contrib hG (fun v => by simp [locContrib])
        (fun e => by simp [schContrib, inner]), fun _ _ => rfl⟩
    -- a coordinate class
    by_cases hd : d ∈ Iloc A v
    · refine ⟨D, good_of_contrib hG (fun v' => ?_) (fun e => by simp [schContrib, inner]),
        fun _ _ => rfl⟩
      simp only [locContrib]
      split
      · next h => subst h; simpa using hd
      · simp
    let NewFact : ZMod 2 → Prop := fun b => ∃ a, IsAddress a ∧
      supp a ⊆ insert d (Iloc A v) ∧ d ∈ supp a ∧ ((v, a), b) ∈ I.toParitySystem.known r
    let p : ZMod 2 := if h : ∃ b, NewFact b then h.choose else 0
    have hp : ∀ a b, IsAddress a → supp a ⊆ insert d (Iloc A v) → d ∈ supp a → d ∉ Iloc A v →
        ((v, a), b) ∈ I.toParitySystem.known r → p = b := by
      intro a b ha hs hda _ hb
      have h : ∃ b, NewFact b := ⟨b, a, ha, hs, hda, hb⟩
      simp only [p, dif_pos h]
      obtain ⟨a', ha', hs', -, hb'⟩ := h.choose_spec
      have := address_unique ha' ha (card_insert_Iloc hcard v d) hs' hs
      subst this
      exact fact_unique hnc hb' hb
    obtain ⟨zv, hz1, hz2, hz3, -, hz5⟩ := extend_loc (by omega) hG v d (card_insert_Iloc hcard v d)
      (Finset.insert_subset hX (Iloc_subset hA v)) p hp
    let D' : Desc I := ⟨Function.update D.z v zv, D.lam⟩
    have hIloc : ∀ v', Iloc (insert (Cls.coord v d) A) v' =
        if v = v' then insert d (Iloc A v') else Iloc A v' := by
      intro v'
      rw [Iloc_insert]
      simp only [locContrib]
      split
      · next h => subst h; rw [Finset.insert_eq]
      · simp
    have hzA : ∀ v', ∀ d' ∈ Iloc A v', D'.z v' d' = D.z v' d' := by
      intro v' d' hd'
      by_cases h : v' = v
      · subst h; simp [D', hz1 d' hd']
      · simp [D', Function.update_of_ne h]
    have hshift : ∀ Y ∈ A, shift D' Y = shift D Y := fun Y hY =>
      shift_eq_of_z Y (fun v' d' hd' => hzA v' d' (Finset.mem_biUnion.mpr ⟨Y, hY, hd'⟩)) rfl
    refine ⟨D', ⟨fun v' hv' => ?_, fun e c hc => ?_, fun v' => ?_, fun v' a b ha hs hb => ?_,
      hnc⟩, hshift⟩
    · by_cases h : v' = v
      · subst h; simp [D', hz2 hv']
      · simp [D', Function.update_of_ne h, hG.init v' hv']
    · have hc' : c ∈ Isch A e := by
        rw [Isch_insert] at hc
        simpa [schContrib, inner] using hc
      have hagree : ArgsAgree D D' e c := fun i => hzA _ _ (Isch_args hc' i)
      rw [MS, T_congr hagree fun _ _ => rfl, hagree.End]
      exact hG.ms e c hc'
    · rw [hIloc]
      split
      · next h => subst h; simpa [D'] using hz3
      · next h => simpa [D', Function.update_of_ne (Ne.symm h)] using hG.even v'
    · rw [hIloc] at hs
      split at hs
      · next h => subst h; simpa [D'] using hz5 a b ha hs hb
      · next h =>
        simp only [D', Function.update_of_ne (Ne.symm h)]
        exact hG.agree v' a b ha hs (known_mono I (Nat.le_succ r) hb)
  | some p =>
    obtain ⟨e, c⟩ := p
    by_cases hc : c ∈ Isch A e
    · -- the coordinate is already pebbled
      refine ⟨D, good_of_contrib hG (fun v => ?_) (fun e' => ?_), fun _ _ => rfl⟩
      · rw [locContrib_of_inner hin]
        intro d hd
        obtain ⟨i, rfl, rfl⟩ := mem_argContrib.mp hd
        exact Isch_args hc i
      · rw [schContrib_of_inner hin]
        split
        · next h => subst h; simpa using hc
        · simp
    have hcd : c ∈ dom I e := hX.inner_dom hin
    obtain ⟨z', hz1, hz2, hz3, hz4, hz5⟩ := extend_seeds hk hG hA hcard e hc hcd
    set s := sch I e
    set L := argLoc s
    set P := argPerm s
    let D1 : Desc I := ⟨z', D.lam⟩
    -- the new seeds agree with the old ones at all retained argument coordinates
    have hagree : ∀ c' ∈ Isch A e, ArgsAgree D D1 e c' := fun c' hc' i =>
      hz1 _ _ (Isch_args hc' i)
    let bsum : Coord k ℓ → ZMod 2 := fun c' => ∑ i, z' (L i) ((P i).apply c')
    let Λ : Coord k ℓ → ZMod 2 := fun c' =>
      ∑ σ ∈ Finset.range (numSteps k ℓ), D.lam e σ * ent σ c'
    have hbΛ : ∀ c' ∈ Isch A e, bsum c' + Λ c' = 0 := by
      intro c' hc'
      have hms := hG.ms e c' hc'
      rw [MS, T] at hms
      have h1 : bsum c' = t0 D e c' + D.z (locEnd s) ((permEnd s).apply c') := by
        rw [t0_add_end]
        exact Finset.sum_congr rfl fun i _ => hagree c' hc' i
      rw [h1, ← hms]
      simp only [Λ]
      rw [← add_assoc (t0 D e c'), zmod2_add_self, zero_add, zmod2_add_self]
    set J := insert c (Isch A e)
    let t : Vec k ℓ := fun c' => if c' = c then bsum c + Λ c else 0
    have ht : ∀ y, IsCode y → SuppIn y J → dot y t = 0 := by
      intro y hy hyJ
      have e1 : dot y t = ∑ c', y c' * (bsum c' + Λ c') := by
        refine Finset.sum_congr rfl fun c' _ => ?_
        by_cases h1 : c' = c
        · subst h1; simp [t]
        · by_cases h2 : c' ∈ Isch A e
          · simp [t, h1, hbΛ c' h2]
          · have : y c' = 0 := hyJ c' (by simp [J, h1, h2])
            simp [t, h1, this]
      rw [e1]
      simp only [mul_add, Finset.sum_add_distrib]
      have hΛ : ∑ c', y c' * Λ c' = 0 := by
        simp only [Λ, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun σ _ => ?_
        have := sum_ent_code hk hy σ
        rw [← mul_zero (D.lam e σ), ← this, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c' _ => by ring
      rw [hΛ, add_zero]
      have hb : ∑ c', y c' * bsum c' = ∑ i, dot (permVec (P i) y) (z' (L i)) := by
        simp only [bsum, Finset.mul_sum, dot_permVec]
        exact Finset.sum_comm
      rw [hb]
      have hpar := hy.blockSum_eq (by omega)
      rcases zmod2_eq_zero_or_one (blockSum y ⟨0, by omega⟩) with h0 | h1
      · refine Finset.sum_eq_zero fun i _ => hz3 (L i) _ (isCode_permVec (by omega) _ hy)
          (fun i' => by rw [blockSum_permVec', hpar _ ⟨0, by omega⟩, h0]) ?_
        intro d hd
        apply suppIn_permVec (P i) hyJ d
        intro hd'
        apply hd
        obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hd'
        rcases Finset.mem_insert.mp hc' with rfl | h
        · exact Finset.mem_union_left _ (by rw [argContrib_self]; exact Finset.mem_singleton_self _)
        · exact Finset.mem_union_right _ (Isch_args h i)
      · obtain ⟨a, ha, rfl⟩ := exists_address_of_odd (by omega) hy
          (fun i' => by rw [hpar i' ⟨0, by omega⟩, h1]) hyJ (card_insert_Isch hcard e c)
        simp_rw [← ind_act]
        exact hz5 a ha (suppIn_ind.mp hyJ)
    obtain ⟨μ, hμ⟩ := exists_rowComb J t ht
    obtain ⟨h, hh, huntouched⟩ := exists_untouched hcard e
    let D' : Desc I := ⟨z', fun e' σ => D.lam e' σ + corrLam (I := I) hM e h μ e' σ⟩
    have hT_other : ∀ e', e' ≠ e → ∀ c' σ, T D' e' c' σ = T D1 e' c' σ := by
      intro e' he' c' σ
      simp [T, D', D1, corrLam, he', Matrix.t0]
    have hT_e : ∀ c' σ, T D' e c' σ =
        T D1 e c' σ + ∑ σ' ∈ Finset.range σ, corrLam (I := I) hM e h μ e σ' * ent σ' c' := by
      intro c' σ
      simp only [T, D', D1, Matrix.t0, add_mul, Finset.sum_add_distrib, add_assoc]
    have hγ : ∀ c' ∈ J, ∑ j, μ j * checkMatrix k ℓ j c' = t c' := hμ
    have hN : (h + 1) * (k - 1 + ℓ) ≤ numSteps k ℓ := by
      unfold numSteps; exact Nat.mul_le_mul_right _ hh
    -- retained columns are unchanged at stages outside the repaired repetition
    have hT_keep : ∀ c' ∈ Isch A e, ∀ σ, (σ ≤ h * (k - 1 + ℓ) ∨ (h + 1) * (k - 1 + ℓ) ≤ σ) →
        T D' e c' σ = T D e c' σ := by
      intro c' hc' σ hσ
      rw [hT_e, T_congr (hagree c' hc') fun _ _ => rfl]
      rcases hσ with hσ | hσ
      · rw [(sum_corr hk e h μ c' σ).1 hσ, add_zero]
      · rw [(sum_corr hk e h μ c' σ).2 hσ, hγ c' (Finset.mem_insert_of_mem hc')]
        simp [t, show c' ≠ c from fun h' => hc (h' ▸ hc')]
    have hIloc : ∀ v, Iloc (insert X A) v = argContrib I e c v ∪ Iloc A v :=
      Iloc_insert_inner hin
    have hIsch : ∀ e', Isch (insert X A) e' = (if e = e' then {c} else ∅) ∪ Isch A e' := by
      intro e'; rw [Isch_insert, schContrib_of_inner hin]
    refine ⟨D', ⟨fun v hv => hz2 v hv, fun e' c' hc' => ?_, fun v => (hIloc v).symm ▸ hz3 v,
      fun v a b ha hs hb => hz4 v a b ha ((hIloc v) ▸ hs) hb, hnc⟩, fun Y hY => ?_⟩
    · -- the mask-sum conditions
      rw [hIsch] at hc'
      by_cases he : e = e'
      · subst he
        rcases Finset.mem_union.mp hc' with h1 | h1
        · rw [if_pos rfl, Finset.mem_singleton] at h1
          subst h1
          rw [MS, hT_e, (sum_corr hk e h μ c' _).2 hN, hγ c' (Finset.mem_insert_self _ _)]
          simp only [t, if_true]
          have hb : bsum c' = t0 D1 e c' + z' (locEnd s) ((permEnd s).apply c') := by
            rw [t0_add_end]
          rw [T, hb]
          show t0 D1 e c' + Λ c' + (t0 D1 e c' + z' (locEnd s) ((permEnd s).apply c') +
            Λ c') = _
          ring_nf
          rw [show (2 : ZMod 2) = 0 from rfl]
          ring
        · rw [MS, hT_keep c' h1 _ (Or.inr hN)]
          have := hG.ms e c' h1
          rw [MS] at this
          rw [this]
          exact ((hagree c' h1).End).symm
      · rw [if_neg he, Finset.empty_union] at hc'
        have ha' : ArgsAgree D D1 e' c' := fun i => hz1 _ _ (Isch_args hc' i)
        rw [MS, hT_other e' (Ne.symm he), T_congr ha' fun _ _ => rfl]
        have := hG.ms e' c' hc'
        rw [MS] at this
        rw [this]
        exact ha'.End.symm
    · -- retained translations
      have hzY : ∀ v, ∀ d ∈ locContrib Y v, z' v d = D.z v d :=
        fun v d hd => hz1 v d (Finset.mem_biUnion.mpr ⟨Y, hY, hd⟩)
      have hT : ∀ e' c' σ, inner Y = some (e', c') →
          (e' = e → σ ≤ h * (k - 1 + ℓ) ∨ (h + 1) * (k - 1 + ℓ) ≤ σ) →
          T D' e' c' σ = T D e' c' σ := by
        intro e' c' σ hY' hσ
        have ha := argsAgree_of (D := D) (D' := D1) hY' hzY
        by_cases he : e' = e
        · subst he
          exact hT_keep c' (mem_Isch.mpr ⟨Y, hY, hY'⟩) σ (hσ rfl)
        · rw [hT_other e' he, T_congr ha fun _ _ => rfl]
      have hrep : ∀ e' σ, touch Y = some (e', σ / (k - 1 + ℓ)) → e' = e →
          (σ + 1 ≤ h * (k - 1 + ℓ) ∨ (h + 1) * (k - 1 + ℓ) ≤ σ) := by
        rintro e' σ hYt rfl
        exact lt_or_ge_of_div_ne hM fun h' => huntouched Y hY (h' ▸ hYt)
      cases Y with
      | coord v d =>
        simp [shift, D', hzY v d (by simp [locContrib])]
      | sum e' c' =>
        have ha := argsAgree_of (D := D) (D' := D1) (rfl : inner (Cls.sum e' c' : ICls I) = _) hzY
        simp only [shift]
        rw [show t0 D' e' c' = t0 D1 e' c' from rfl, ha.t0]
      | junc e' c' =>
        have ha := argsAgree_of (D := D) (D' := D1) (rfl : inner (Cls.junc e' c' : ICls I) = _) hzY
        simp only [shift]
        exact Prod.ext ha.U ha.V
      | link e' c' =>
        simp only [shift]
        rw [hT e' c' _ rfl fun _ => Or.inr hN]
      | track e' σ c' =>
        simp only [shift]
        rw [hT e' c' _ rfl fun he => ?_]
        rcases hrep e' σ rfl he with h1 | h1
        · left; omega
        · right; omega
      | upd e' σ c' =>
        simp only [shift]
        rw [hT e' c' σ rfl fun he => ?_, hT e' c' (σ + 1) rfl fun he => ?_]
        · rcases hrep e' σ rfl he with h1 | h1
          · left; omega
          · right; omega
        · rcases hrep e' σ rfl he with h1 | h1
          · left; omega
          · right; omega
      | coef e' σ =>
        simp only [shift, D', corrLam]
        rw [if_neg, add_zero]
        rintro ⟨rfl, h'⟩
        exact huntouched _ hY (by simp [touch, h'])

end Lax119563Proofs.Matrix
