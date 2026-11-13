import Lax119563Proofs.Matrix.Invariant

/-!
# Extending exposed values and argument seeds

When a new internal coordinate `c` of schema `e` is pebbled, the argument locations gain at
most one coordinate each. We choose values for the newly exposed variables (Lemma
"Extending exposed values") and extend the argument seeds accordingly.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems

namespace Lax119563Proofs.Matrix

variable {k ℓ w : ℕ}

/-! ### Arguments and track bits -/

lemma exists_arg_U (s : Schema k ℓ w) : ∃ i, argLoc s i = locU s ∧ argPerm s i = permU s := by
  cases s
  · exact ⟨(0 : Fin 2), rfl, rfl⟩
  · exact ⟨(0 : Fin 3), rfl, rfl⟩

lemma exists_arg_V (s : Schema k ℓ w) : ∃ i, argLoc s i = locV s ∧ argPerm s i = permV s := by
  cases s
  · exact ⟨(1 : Fin 2), rfl, rfl⟩
  · exact ⟨(1 : Fin 3), rfl, rfl⟩

lemma exists_arg_End (s : Schema k ℓ w) :
    ∃ i, argLoc s i = locEnd s ∧ argPerm s i = permEnd s := by
  cases s
  · exact ⟨(1 : Fin 2), rfl, rfl⟩
  · exact ⟨(2 : Fin 3), rfl, rfl⟩

lemma arity_pos (s : Schema k ℓ w) : 0 < arity s := by
  cases s <;> simp [arity]

variable {I : ImplicitParitySystem k ℓ}

lemma t0_add_end (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) :
    t0 D e c + D.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c) =
      ∑ i, D.z (argLoc (sch I e) i) ((argPerm (sch I e) i).apply c) := by
  rw [sum_args (sch I e) fun v P => D.z v (P.apply c), t0]

/-- Agreement of two descriptions at the argument coordinates of `c`. -/
def ArgsAgree (D D' : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : Prop :=
  ∀ i, D'.z (argLoc (sch I e) i) ((argPerm (sch I e) i).apply c) =
    D.z (argLoc (sch I e) i) ((argPerm (sch I e) i).apply c)

lemma ArgsAgree.U {D D' : Desc I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : ArgsAgree D D' e c) :
    D'.z (locU (sch I e)) ((permU (sch I e)).apply c) =
      D.z (locU (sch I e)) ((permU (sch I e)).apply c) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_U (sch I e)
  rw [← h1, ← h2]; exact h i

lemma ArgsAgree.V {D D' : Desc I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : ArgsAgree D D' e c) :
    D'.z (locV (sch I e)) ((permV (sch I e)).apply c) =
      D.z (locV (sch I e)) ((permV (sch I e)).apply c) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_V (sch I e)
  rw [← h1, ← h2]; exact h i

lemma ArgsAgree.End {D D' : Desc I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : ArgsAgree D D' e c) :
    D'.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c) =
      D.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_End (sch I e)
  rw [← h1, ← h2]; exact h i

lemma ArgsAgree.t0 {D D' : Desc I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : ArgsAgree D D' e c) : t0 D' e c = t0 D e c := by
  simp only [Matrix.t0, h.U, h.V]

lemma T_congr {D D' : Desc I} {e : Fin I.schemas.length} {c : Coord k ℓ} (h : ArgsAgree D D' e c)
    {σ : ℕ} (hlam : ∀ σ' < σ, D'.lam e σ' = D.lam e σ') : T D' e c σ = T D e c σ := by
  simp only [T, h.t0]
  congr 1
  exact Finset.sum_congr rfl fun σ' hσ' => by rw [hlam σ' (Finset.mem_range.mp hσ')]

lemma argsAgree_of {D D' : Desc I} {Y : ICls I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hY : inner Y = some (e, c)) (hz : ∀ v, ∀ d ∈ locContrib Y v, D'.z v d = D.z v d) :
    ArgsAgree D D' e c := by
  intro i
  apply hz
  rw [locContrib_of_inner hY, argContrib_self]
  exact Finset.mem_singleton_self _

/-- Shifts only depend on the seeds at the contributed coordinates and on the coefficients. -/
lemma shift_eq_of_z {D D' : Desc I} (Y : ICls I)
    (hz : ∀ v, ∀ d ∈ locContrib Y v, D'.z v d = D.z v d) (hlam : D'.lam = D.lam) :
    shift D' Y = shift D Y := by
  cases Y with
  | coord v c =>
    have := hz v c (by simp [locContrib])
    simp [shift, this]
  | sum e c =>
    have h := argsAgree_of (rfl : inner (Cls.sum e c : ICls I) = _) hz
    simp [shift, h.t0]
  | junc e c =>
    have h := argsAgree_of (rfl : inner (Cls.junc e c : ICls I) = _) hz
    simp [shift, h.U, h.V]
  | link e c =>
    have h := argsAgree_of (rfl : inner (Cls.link e c : ICls I) = _) hz
    simp [shift, T_congr h fun σ' _ => by rw [hlam]]
  | track e σ c =>
    have h := argsAgree_of (rfl : inner (Cls.track e σ c : ICls I) = _) hz
    simp [shift, T_congr h fun σ' _ => by rw [hlam]]
  | upd e σ c =>
    have h := argsAgree_of (rfl : inner (Cls.upd e σ c : ICls I) = _) hz
    simp [shift, T_congr h fun σ' _ => by rw [hlam]]
  | coef e σ => simp [shift, hlam]

/-! ### Rows and addresses -/

lemma ent_eq (hk : 2 ≤ k) (σ : ℕ) (c : Coord k ℓ) :
    ent σ c = checkMatrix k ℓ (stepRow (by omega) σ) c := by
  simp only [ent, dif_pos (show 0 < k - 1 + ℓ by omega)]

lemma sum_ent_supp (hk : 2 ≤ k) {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) (σ : ℕ) :
    ∑ i, ent σ (i, a i) = 0 := by
  simp only [ent_eq hk]
  exact sum_row_supp (by omega) ha _

lemma sum_ent_code (hk : 2 ≤ k) {y : Vec k ℓ} (hy : IsCode y) (σ : ℕ) :
    ∑ c, y c * ent σ c = 0 := by
  have := hy (stepRow (by omega) σ)
  simp only [ent_eq hk]
  rw [← this]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/-- The equation of an address all of whose coordinates satisfy the mask-sum condition holds
for the seeds. -/
lemma eq_of_ms (hk : 2 ≤ k) (D : Desc I) (e : Fin I.schemas.length) {a : Fin k → BlockCoord ℓ}
    (ha : IsAddress a) (hms : ∀ c ∈ supp a, MS D e c) :
    ∑ i, dot (ind ((argPerm (sch I e) i).act a)) (D.z (argLoc (sch I e) i)) = 0 := by
  simp_rw [dot_ind_act]
  rw [Finset.sum_comm]
  have h : ∀ i', ∑ i, D.z (argLoc (sch I e) i) ((argPerm (sch I e) i).apply (i', a i')) =
      ∑ σ ∈ Finset.range (numSteps k ℓ), D.lam e σ * ent σ (i', a i') := by
    intro i'
    rw [← t0_add_end]
    have hm := hms (i', a i') (mem_supp_iff.mpr rfl)
    rw [MS, T] at hm
    rw [← hm]
    ring_nf
    rw [show (2 : ZMod 2) = 0 from rfl]
    ring
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [← Finset.mul_sum, sum_ent_supp hk ha, mul_zero]

/-! ### Choosing the values of new variables -/

variable {r : ℕ} {A : Finset (ICls I)} {D : Desc I}

lemma card_insert_Iloc (hcard : A.card ≤ k) (v : Fin I.numLocations) (d : Coord k ℓ) :
    (insert d (Iloc A v)).card ≤ k + 1 :=
  (Finset.card_insert_le _ _).trans (by have := card_Iloc_le A v; omega)

lemma card_insert_Isch (hcard : A.card ≤ k) (e : Fin I.schemas.length) (c : Coord k ℓ) :
    (insert c (Isch A e)).card ≤ k + 1 :=
  (Finset.card_insert_le _ _).trans (by have := card_Isch_le A e; omega)

/-- The address of the equation, as seen at an argument location. -/
lemma supp_arg_subset {e : Fin I.schemas.length} {c : Coord k ℓ} {a : Fin k → BlockCoord ℓ}
    (hs : supp a ⊆ insert c (Isch A e)) (i : Fin (arity (sch I e))) :
    supp ((argPerm (sch I e) i).act a) ⊆
      insert ((argPerm (sch I e) i).apply c) (Iloc A (argLoc (sch I e) i)) := by
  rw [supp_act]
  intro d hd
  obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hd
  rcases Finset.mem_insert.mp (hs hc') with rfl | h
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Isch_args h i)

lemma mem_supp_arg {e : Fin I.schemas.length} {c : Coord k ℓ} {a : Fin k → BlockCoord ℓ}
    (hc : c ∈ supp a) (i : Fin (arity (sch I e))) :
    (argPerm (sch I e) i).apply c ∈ supp ((argPerm (sch I e) i).act a) := by
  rw [supp_act]; exact Finset.mem_image_of_mem _ hc

/-- **Extending exposed values.** Values for the variables newly exposed at the argument
locations, consistent with `K_r` and with the newly exposed equation. -/
lemma choose_values (hG : Good (r + 1) A D) (hA : AllValid A)
    (hcard : A.card ≤ k) (e : Fin I.schemas.length) {c : Coord k ℓ} (hc : c ∉ Isch A e)
    (hcd : c ∈ dom I e) :
    ∃ p : Fin (arity (sch I e)) → ZMod 2,
      (∀ i a b, IsAddress a →
        supp a ⊆ insert ((argPerm (sch I e) i).apply c) (Iloc A (argLoc (sch I e) i)) →
        (argPerm (sch I e) i).apply c ∈ supp a →
        (argPerm (sch I e) i).apply c ∉ Iloc A (argLoc (sch I e) i) →
        ((argLoc (sch I e) i, a), b) ∈ I.toParitySystem.known r → p i = b) ∧
      (∀ a, IsAddress a → supp a ⊆ insert c (Isch A e) → c ∈ supp a →
        ∑ i, (if (argPerm (sch I e) i).apply c ∈ Iloc A (argLoc (sch I e) i) then
          dot (ind ((argPerm (sch I e) i).act a)) (D.z (argLoc (sch I e) i)) else p i) = 0) := by
  classical
  set s := sch I e
  set L := argLoc s
  set P := argPerm s
  set d : Fin (arity s) → Coord k ℓ := fun i => (P i).apply c
  set J : Fin (arity s) → Finset (Coord k ℓ) := fun i => Iloc A (L i)
  have hnc : ¬ I.toParitySystem.HasConflict r :=
    fun h => hG.noConflict (hasConflict_mono I (Nat.le_succ r) h)
  -- facts about new addresses
  let NewFact : Fin (arity s) → ZMod 2 → Prop := fun i b => ∃ a, IsAddress a ∧
    supp a ⊆ insert (d i) (J i) ∧ d i ∈ supp a ∧ ((L i, a), b) ∈ I.toParitySystem.known r
  have hnf_unique : ∀ i b b', NewFact i b → NewFact i b' → b = b' := by
    rintro i b b' ⟨a, ha, hs, -, hb⟩ ⟨a', ha', hs', -, hb'⟩
    have := address_unique ha ha' (card_insert_Iloc hcard _ _) hs hs'
    subst this
    exact fact_unique hnc hb hb'
  let p0 : Fin (arity s) → ZMod 2 := fun i => if h : ∃ b, NewFact i b then h.choose else 0
  have hp0 : ∀ i b, NewFact i b → p0 i = b := by
    intro i b hb
    have h : ∃ b, NewFact i b := ⟨b, hb⟩
    simp only [p0, dif_pos h]
    exact hnf_unique i _ _ h.choose_spec hb
  have hP1 : ∀ p : Fin (arity s) → ZMod 2, (∀ i, (∃ b, NewFact i b) → p i = p0 i) →
      ∀ i a b, IsAddress a → supp a ⊆ insert (d i) (J i) → d i ∈ supp a → d i ∉ J i →
        ((L i, a), b) ∈ I.toParitySystem.known r → p i = b := by
    intro p hp i a b ha hs hda _ hb
    have hnf : NewFact i b := ⟨a, ha, hs, hda, hb⟩
    rw [hp i ⟨b, hnf⟩, hp0 i b hnf]
  by_cases hex : ∃ a, IsAddress a ∧ supp a ⊆ insert c (Isch A e) ∧ c ∈ supp a
  swap
  · push Not at hex
    exact ⟨p0, hP1 p0 fun _ _ => rfl, fun a ha hs hca => absurd hca (hex a ha hs)⟩
  obtain ⟨a, ha, hsa, hca⟩ := hex
  have hJcard := card_insert_Isch hcard e c
  have hdom : insert c (Isch A e) ⊆ dom I e :=
    Finset.insert_subset hcd (Isch_subset hA e)
  -- the only address of the newly exposed equation
  have huniq : ∀ a', IsAddress a' → supp a' ⊆ insert c (Isch A e) → a' = a :=
    fun a' ha' hs' => address_unique ha' ha hJcard hs' hsa
  have hsi : ∀ i, supp ((P i).act a) ⊆ insert (d i) (J i) := fun i => supp_arg_subset hsa i
  have hdi : ∀ i, d i ∈ supp ((P i).act a) := fun i => mem_supp_arg hca i
  have hai : ∀ i, IsAddress ((P i).act a) := fun i => isAddress_act _ ha
  -- old variables are covered by the old coordinate set
  have hold_supp : ∀ i, d i ∈ J i → supp ((P i).act a) ⊆ J i := by
    intro i hi
    have := hsi i
    rwa [Finset.insert_eq_of_mem hi] at this
  -- at most one argument variable was exposed before
  have hone : ∀ i j, i ≠ j → d i ∈ J i → d j ∈ J j → False := by
    intro i j hij hi hj
    exact hc (geometry hcard e hij (hold_supp i hi) (hold_supp j hj) hca)
  -- a fact at a new location is a fact about the equation's variable
  have hnf_eq : ∀ i b, NewFact i b → ((L i, (P i).act a), b) ∈ I.toParitySystem.known r := by
    rintro i b ⟨a', ha', hs', -, hb⟩
    have := address_unique ha' (hai i) (card_insert_Iloc hcard _ _) hs' (hsi i)
    rwa [this] at hb
  let val : (Fin (arity s) → ZMod 2) → Fin (arity s) → ZMod 2 := fun p i =>
    if d i ∈ J i then dot (ind ((P i).act a)) (D.z (L i)) else p i
  have hP2 : ∀ p : Fin (arity s) → ZMod 2, ∑ i, val p i = 0 →
      ∀ a', IsAddress a' → supp a' ⊆ insert c (Isch A e) → c ∈ supp a' →
        ∑ i, (if d i ∈ J i then dot (ind ((P i).act a')) (D.z (L i)) else p i) = 0 := by
    intro p hp a' ha' hs' _
    rw [huniq a' ha' hs']
    exact hp
  by_cases hfree : ∃ i₀, d i₀ ∉ J i₀ ∧ ¬ ∃ b, NewFact i₀ b
  · obtain ⟨i₀, hi₀, hnf₀⟩ := hfree
    let p := Function.update p0 i₀ (∑ i ∈ Finset.univ.erase i₀, val p0 i)
    refine ⟨p, hP1 p fun i hi => ?_, hP2 p ?_⟩
    · have : i ≠ i₀ := by rintro rfl; exact hnf₀ hi
      simp [p, Function.update_of_ne this]
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      have h1 : val p i₀ = ∑ i ∈ Finset.univ.erase i₀, val p0 i := by
        simp [val, hi₀, p]
      have h2 : ∑ i ∈ Finset.univ.erase i₀, val p i = ∑ i ∈ Finset.univ.erase i₀, val p0 i :=
        Finset.sum_congr rfl fun i hi => by
          simp [val, p, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [h1, h2, zmod2_add_self]
  · push Not at hfree
    refine ⟨p0, hP1 p0 fun _ _ => rfl, hP2 p0 ?_⟩
    -- every new variable has a fact in `K_r`
    have hfacts : ∀ i, d i ∉ J i → ((L i, (P i).act a), p0 i) ∈ I.toParitySystem.known r := by
      intro i hi
      obtain ⟨b, hb⟩ := hfree i hi
      rw [hp0 i b hb]
      exact hnf_eq i b hb
    by_cases hold : ∃ i₁, d i₁ ∈ J i₁
    · obtain ⟨i₁, hi₁⟩ := hold
      have hnew : ∀ i, i ≠ i₁ → d i ∉ J i := fun i hi h => hone i i₁ hi h hi₁
      have hinf := infer I e ha (hsa.trans hdom) i₁ (val p0)
        (r := r) fun i hi => by
          simp only [val, if_neg (hnew i hi)]
          exact hfacts i (hnew i hi)
      have hval := hG.agree (L i₁) _ _ (hai i₁) (hold_supp i₁ hi₁) hinf
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₁)]
      have : val p0 i₁ = dot (ind ((P i₁).act a)) (D.z (L i₁)) := by simp [val, hi₁]
      rw [this, hval, zmod2_add_self]
    · push Not at hold
      let i₀ : Fin (arity s) := ⟨0, arity_pos s⟩
      have hinf := infer I e ha (hsa.trans hdom) i₀ (val p0) (r := r) fun i _ => by
        simp only [val, if_neg (hold i)]
        exact hfacts i (hold i)
      have h0 : ((L i₀, (P i₀).act a), val p0 i₀) ∈ I.toParitySystem.known (r + 1) := by
        simp only [val, if_neg (hold i₀)]
        exact known_mono I (Nat.le_succ r) (hfacts i₀ (hold i₀))
      have := fact_unique hG.noConflict hinf h0
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), ← this, zmod2_add_self]

lemma Iloc_insert_inner {X : ICls I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hX : inner X = some (e, c)) (v : Fin I.numLocations) :
    Iloc (insert X A) v = argContrib I e c v ∪ Iloc A v := by
  rw [Iloc_insert, locContrib_of_inner hX]

lemma argContrib_of_not_loc {e : Fin I.schemas.length} {c : Coord k ℓ} {v : Fin I.numLocations}
    (h : ∀ i, argLoc (sch I e) i ≠ v) : argContrib I e c v = ∅ := by
  ext d
  simp only [Finset.notMem_empty, iff_false]
  intro hd
  obtain ⟨i, hi, -⟩ := mem_argContrib.mp hd
  exact h i hi

lemma argContrib_union_loc (e : Fin I.schemas.length) (c : Coord k ℓ) (i : Fin (arity (sch I e))) :
    argContrib I e c (argLoc (sch I e) i) ∪ Iloc A (argLoc (sch I e) i) =
      insert ((argPerm (sch I e) i).apply c) (Iloc A (argLoc (sch I e) i)) := by
  rw [argContrib_self, Finset.insert_eq]

/-- Extension of the argument seeds for a new internal coordinate `c` of schema `e`. -/
lemma extend_seeds (hk : 2 ≤ k) (hG : Good (r + 1) A D) (hA : AllValid A) (hcard : A.card ≤ k)
    (e : Fin I.schemas.length) {c : Coord k ℓ} (hc : c ∉ Isch A e) (hcd : c ∈ dom I e) :
    ∃ z' : Fin I.numLocations → Vec k ℓ,
      (∀ v, ∀ d ∈ Iloc A v, z' v d = D.z v d) ∧
      (∀ v, (I.init v).isSome → z' v = initSeed I v) ∧
      (∀ v, EvenKills (z' v) (argContrib I e c v ∪ Iloc A v)) ∧
      (∀ v a b, IsAddress a → supp a ⊆ argContrib I e c v ∪ Iloc A v →
        ((v, a), b) ∈ I.toParitySystem.known r → dot (ind a) (z' v) = b) ∧
      (∀ a, IsAddress a → supp a ⊆ insert c (Isch A e) →
        ∑ i, dot (ind ((argPerm (sch I e) i).act a)) (z' (argLoc (sch I e) i)) = 0) := by
  classical
  set s := sch I e
  set L := argLoc s
  set P := argPerm s
  obtain ⟨p, hp1, hp2⟩ := choose_values hG hA hcard e hc hcd
  have hext : ∀ i, ∃ zv : Vec k ℓ, (∀ d' ∈ Iloc A (L i), zv d' = D.z (L i) d') ∧
      ((I.init (L i)).isSome → zv = initSeed I (L i)) ∧
      EvenKills zv (insert ((P i).apply c) (Iloc A (L i))) ∧
      (∀ a, IsAddress a → supp a ⊆ insert ((P i).apply c) (Iloc A (L i)) →
        (P i).apply c ∈ supp a → (P i).apply c ∉ Iloc A (L i) → dot (ind a) zv = p i) ∧
      (∀ a b, IsAddress a → supp a ⊆ insert ((P i).apply c) (Iloc A (L i)) →
        ((L i, a), b) ∈ I.toParitySystem.known r → dot (ind a) zv = b) := fun i =>
    extend_loc (by omega) hG (L i) ((P i).apply c) (card_insert_Iloc hcard _ _)
      (Finset.insert_subset (argPerm_mem (sch_wf I e) hcd i) (Iloc_subset hA _)) (p i)
      (fun a b ha hs hda hdn hb => hp1 i a b ha hs hda hdn hb)
  choose zv hzv1 hzv2 hzv3 hzv4 hzv5 using hext
  let z' : Fin I.numLocations → Vec k ℓ := fun v => if h : ∃ i, L i = v then zv h.choose else D.z v
  have hz'L : ∀ i, z' (L i) = zv i := by
    intro i
    have h : ∃ i', L i' = L i := ⟨i, rfl⟩
    simp only [z', dif_pos h]
    rw [argLoc_injective (sch_wf I e) h.choose_spec]
  have hz'N : ∀ v, (¬ ∃ i, L i = v) → z' v = D.z v := fun v h => by simp only [z', dif_neg h]
  refine ⟨z', fun v d hd => ?_, fun v hv => ?_, fun v => ?_, fun v a b ha hs hb => ?_,
    fun a ha hs => ?_⟩
  · by_cases h : ∃ i, L i = v
    · obtain ⟨i, rfl⟩ := h; rw [hz'L]; exact hzv1 i d hd
    · rw [hz'N v h]
  · by_cases h : ∃ i, L i = v
    · obtain ⟨i, rfl⟩ := h; rw [hz'L]; exact hzv2 i hv
    · rw [hz'N v h]; exact hG.init v hv
  · by_cases h : ∃ i, L i = v
    · obtain ⟨i, rfl⟩ := h; rw [hz'L, argContrib_union_loc]; exact hzv3 i
    · push Not at h
      rw [hz'N v (by push Not; exact h), argContrib_of_not_loc h, Finset.empty_union]
      exact hG.even v
  · by_cases h : ∃ i, L i = v
    · obtain ⟨i, rfl⟩ := h
      rw [hz'L]; rw [argContrib_union_loc] at hs; exact hzv5 i a b ha hs hb
    · push Not at h
      rw [hz'N v (by push Not; exact h)]
      rw [argContrib_of_not_loc h, Finset.empty_union] at hs
      exact hG.agree v a b ha hs (known_mono I (Nat.le_succ r) hb)
  · simp_rw [hz'L]
    by_cases hca : c ∈ supp a
    · rw [← hp2 a ha hs hca]
      refine Finset.sum_congr rfl fun i _ => ?_
      split
      · next hi =>
        have hsub : supp ((P i).act a) ⊆ Iloc A (L i) := by
          have := supp_arg_subset hs i
          rwa [Finset.insert_eq_of_mem hi] at this
        exact dot_congr_suppIn (suppIn_ind.mpr hsub) (hzv1 i)
      · next hi =>
        exact hzv4 i _ (isAddress_act _ ha) (supp_arg_subset hs i) (mem_supp_arg hca i) hi
    · have hsub : supp a ⊆ Isch A e := by
        intro x hx
        rcases Finset.mem_insert.mp (hs hx) with rfl | h
        · exact absurd hx hca
        · exact h
      rw [← eq_of_ms hk D e ha fun c' hc' => hG.ms e c' (hsub hc')]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsub' : supp ((P i).act a) ⊆ Iloc A (L i) := by
        rw [supp_act]
        intro d hd
        obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hd
        exact Isch_args (hsub hc') i
      exact dot_congr_suppIn (suppIn_ind.mpr hsub') (hzv1 i)

end Lax119563Proofs.Matrix
