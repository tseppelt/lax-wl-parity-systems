import Lax119563Proofs.RowSpace.Extension
import Lax119563Proofs.Matrix.GameLemmas

/-!
# Duplicator's strategy on the row-space graphs

Duplicator maintains a seed description `D` for the pebbled classes whose realized values agree
with `K_r` (`r` rounds remaining); the pebble pairs follow the translation `tr D`. After a lift,
for every class `X` the description is extended to `X` by the local extension lemma, after
choosing values for the newly exposed variables consistent with `K_{r-1}`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-! ### Agreement with known facts -/

/-- The values realized by `D` on the variables exposed for `A` agree with `K_r`. -/
def Agree (r : ℕ) (A : Finset (ICls I)) (D : RDesc I) : Prop :=
  ∀ v a b, IsAddress a → supp a ⊆ Iloc A v →
    ((v, a), b) ∈ I.toParitySystem.known r → dot (ind a) (D.z v) = b

lemma Agree.mono {r r' : ℕ} {A B : Finset (ICls I)} {D : RDesc I} (h : Agree r A D)
    (hr : r' ≤ r) (hB : B ⊆ A) : Agree r' B D :=
  fun v a b ha hs hb => h v a b ha (hs.trans (Iloc_mono hB v)) (known_mono I hr hb)

lemma agree_empty (hk : 0 < k) (r : ℕ) (D : RDesc I) : Agree r (∅ : Finset (ICls I)) D := by
  intro v a b _ hs _
  exfalso
  have : (supp a).card = 0 := by
    rw [Finset.card_eq_zero]; simpa [Iloc] using hs
  rw [card_supp] at this; omega

/-! ### Values for the newly exposed equation -/

/-- **Extending exposed values** (row-space version of `choose_values`): values for the
variables newly exposed at the argument locations, consistent with `K_r` and with the newly
exposed equation. -/
lemma choose_vals_rs {r : ℕ} {A : Finset (ICls I)} {D : RDesc I} (hag : Agree (r + 1) A D)
    (hnc1 : ¬ I.toParitySystem.HasConflict (r + 1)) (hA : A ⊆ classes I)
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
    fun h => hnc1 (hasConflict_mono I (Nat.le_succ r) h)
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
    Finset.insert_subset hcd (Isch_sub_dom hA e)
  -- the only address of the newly exposed equation
  have huniq : ∀ a', IsAddress a' → supp a' ⊆ insert c (Isch A e) → a' = a :=
    fun a' ha' hs' => address_unique ha' ha hJcard hs' hsa
  have hsi : ∀ i, supp ((P i).act a) ⊆ insert (d i) (J i) := fun i => supp_arg_subset hsa i
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
      have hval := hag (L i₁) _ _ (hai i₁) (hold_supp i₁ hi₁) hinf
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
      have := fact_unique hnc1 hinf h0
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), ← this, zmod2_add_self]

/-! ### Choosing values -/

lemma mem_Isch_insert {X : ICls I} {A : Finset (ICls I)} {e : Fin I.schemas.length}
    {c : Coord k ℓ} :
    c ∈ Isch (insert X A) e ↔ Lax119563Proofs.Matrix.inner X = some (e, c) ∨ c ∈ Isch A e := by
  rw [mem_Isch, mem_Isch]
  simp only [Finset.mem_insert, exists_eq_or_imp]

/-- The values realized by `D` on the variables exposed for `A`, and `q` elsewhere. -/
def mkVal (A : Finset (ICls I)) (D : RDesc I) (q : Val I) : Val I := fun x =>
  if supp x.2 ⊆ Iloc A x.1 then dot (ind x.2) (D.z x.1) else q x

lemma mkVal_argVar (A : Finset (ICls I)) (D : RDesc I) (q : Val I) (e : Fin I.schemas.length)
    (i : Fin (arity (sch I e))) (a : Fin k → BlockCoord ℓ) :
    mkVal A D q (argVar I e i a) =
      if supp ((argPerm (sch I e) i).act a) ⊆ Iloc A (argLoc (sch I e) i) then
        dot (ind ((argPerm (sch I e) i).act a)) (D.z (argLoc (sch I e) i))
      else q (argVar I e i a) := rfl

lemma mkVal_props (hk : 0 < k) {r : ℕ} {A : Finset (ICls I)} {D : RDesc I} {X : ICls I}
    (hG : DGood A D) (hA : A ⊆ classes I) (hX : X ∈ classes I) (hag : Agree (r + 1) A D)
    (q : Val I)
    (hq1 : ∀ v a b, IsAddress a → supp a ⊆ Iloc (insert X A) v → ¬ supp a ⊆ Iloc A v →
      ((v, a), b) ∈ I.toParitySystem.known r → q (v, a) = b)
    (hq2 : ∀ e a, IsAddress a → supp a ⊆ Isch (insert X A) e → ¬ supp a ⊆ Isch A e →
      ∑ i, mkVal A D q (argVar I e i a) = 0) :
    Realizes A D (mkVal A D q) ∧ SatEqs (insert X A) (mkVal A D q) ∧
      InitAgree (insert X A) (mkVal A D q) ∧
      ∀ v a b, IsAddress a → supp a ⊆ Iloc (insert X A) v →
        ((v, a), b) ∈ I.toParitySystem.known r → mkVal A D q (v, a) = b := by
  classical
  have hR : Realizes A D (mkVal A D q) := fun v a _ hs => by simp only [mkVal, if_pos hs]
  have hK : ∀ v a b, IsAddress a → supp a ⊆ Iloc (insert X A) v →
      ((v, a), b) ∈ I.toParitySystem.known r → mkVal A D q (v, a) = b := by
    intro v a b ha hs hb
    by_cases ho : supp a ⊆ Iloc A v
    · simp only [mkVal, if_pos ho]
      exact hag v a b ha ho (known_mono I (Nat.le_succ r) hb)
    · simp only [mkVal, if_neg ho]
      exact hq1 v a b ha hs ho hb
  refine ⟨hR, fun e a ha hs => ?_, fun v a b hv ha hs => ?_, hK⟩
  · by_cases ho : supp a ⊆ Isch A e
    · exact Realizes.sat hk hG hA hR e a ha ho
    · exact hq2 e a ha hs ho
  · have h0 : ((v, a), b) ∈ I.toParitySystem.known 0 :=
      ⟨b, hv, rfl, ha, hs.trans (Iloc_sub_dom (Finset.insert_subset hX hA) v)⟩
    exact hK v a b ha hs (known_mono I (Nat.zero_le r) h0)

/-- **Value choice.** Given a seed description of `A` whose realized values agree with
`K_{r+1}`, and a class `X`, there are values realizing `D` on `A`, satisfying the equations
and the initialization exposed for `A ∪ {X}`, and agreeing with `K_r` on the variables exposed
for `A ∪ {X}`. -/
theorem choose_val (hk : 0 < k) {r : ℕ} {A : Finset (ICls I)} {D : RDesc I} (hG : DGood A D)
    (hA : A ⊆ classes I) (hcard : A.card ≤ k) (hag : Agree (r + 1) A D)
    (hnc1 : ¬ I.toParitySystem.HasConflict (r + 1)) {X : ICls I} (hX : X ∈ classes I) :
    ∃ val : Val I, Realizes A D val ∧ SatEqs (insert X A) val ∧ InitAgree (insert X A) val ∧
      ∀ v a b, IsAddress a → supp a ⊆ Iloc (insert X A) v →
        ((v, a), b) ∈ I.toParitySystem.known r → val (v, a) = b := by
  classical
  have hnc : ¬ I.toParitySystem.HasConflict r :=
    fun h => hnc1 (hasConflict_mono I (Nat.le_succ r) h)
  let kr : Val I := fun x => if h : ∃ b, (x, b) ∈ I.toParitySystem.known r then h.choose else 0
  have hkr : ∀ x b, (x, b) ∈ I.toParitySystem.known r → kr x = b := by
    intro x b hb
    have h : ∃ b, (x, b) ∈ I.toParitySystem.known r := ⟨b, hb⟩
    simp only [kr, dif_pos h]
    exact fact_unique hnc h.choose_spec hb
  -- a newly exposed equation contains the schema coordinate of `X`
  have hnewc : ∀ e a, supp a ⊆ Isch (insert X A) e → ¬ supp a ⊆ Isch A e →
      ∃ c, Lax119563Proofs.Matrix.inner X = some (e, c) ∧ c ∉ Isch A e ∧
        supp a ⊆ insert c (Isch A e) ∧ c ∈ supp a := by
    intro e a hs ho
    obtain ⟨c, hca, hcA⟩ := Finset.not_subset.mp ho
    have hXc : Lax119563Proofs.Matrix.inner X = some (e, c) :=
      (mem_Isch_insert.mp (hs hca)).resolve_right hcA
    refine ⟨c, hXc, hcA, fun c' hc' => ?_, hca⟩
    rcases mem_Isch_insert.mp (hs hc') with h | h
    · rw [hXc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem h
  by_cases hnew : ∃ e c a, Lax119563Proofs.Matrix.inner X = some (e, c) ∧ c ∉ Isch A e ∧
      IsAddress a ∧ supp a ⊆ insert c (Isch A e) ∧ c ∈ supp a
  · obtain ⟨e, c, a, hXc, hcA, ha, hsa, hca⟩ := hnew
    have hcd : c ∈ dom I e := inner_dom hX hXc
    obtain ⟨p, hp1, hp2⟩ := choose_vals_rs hag hnc1 hA hcard e hcA hcd
    let q : Val I := fun x => if h : ∃ i, argVar I e i a = x then p h.choose else kr x
    have hqi : ∀ i, q (argVar I e i a) = p i := by
      intro i
      have h : ∃ i', argVar I e i' a = argVar I e i a := ⟨i, rfl⟩
      simp only [q, dif_pos h]
      rw [argVar_injective I e a h.choose_spec]
    refine ⟨mkVal A D q, mkVal_props hk hG hA hX hag q ?_ ?_⟩
    · intro v a' b ha' hs ho hb
      by_cases hi : ∃ i, argVar I e i a = (v, a')
      · obtain ⟨i, hi⟩ := hi
        rw [← hi, hqi]
        simp only [argVar, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        refine hp1 i _ b ha' (supp_arg_subset hsa i) (mem_supp_arg hca i) (fun hd => ho ?_) hb
        have := supp_arg_subset hsa i
        rwa [Finset.insert_eq_of_mem hd] at this
      · simp only [q, dif_neg hi]
        exact hkr _ b hb
    · intro e' a' ha' hs ho
      obtain ⟨c', hXc', hc'A, hs', hc'a⟩ := hnewc e' a' hs ho
      rw [hXc] at hXc'
      simp only [Option.some.injEq, Prod.mk.injEq] at hXc'
      obtain ⟨rfl, rfl⟩ := hXc'
      have : a' = a := address_unique ha' ha (card_insert_Isch hcard e c) hs' hsa
      subst this
      rw [← hp2 a' ha' hsa hca]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mkVal_argVar, hqi]
      by_cases hd : (argPerm (sch I e) i).apply c ∈ Iloc A (argLoc (sch I e) i)
      · have hsub : supp ((argPerm (sch I e) i).act a') ⊆ Iloc A (argLoc (sch I e) i) := by
          have := supp_arg_subset hsa i
          rwa [Finset.insert_eq_of_mem hd] at this
        rw [if_pos hd, if_pos hsub]
      · rw [if_neg hd, if_neg fun h => hd (h (mem_supp_arg hca i))]
  · refine ⟨mkVal A D kr, mkVal_props hk hG hA hX hag kr (fun v a b _ _ _ hb => hkr _ b hb) ?_⟩
    intro e a ha hs ho
    obtain ⟨c, hXc, hcA, hs', hca⟩ := hnewc e a hs ho
    exact absurd ⟨e, c, a, hXc, hcA, ha, hs', hca⟩ hnew

/-- **Extension by one class**, consistent with `K_r`. -/
theorem extend_cls (hk : 2 ≤ k) {r : ℕ} {A : Finset (ICls I)} {D : RDesc I} (hG : DGood A D)
    (hA : A ⊆ classes I) (hcard : A.card ≤ k) (hag : Agree (r + 1) A D)
    (hnc1 : ¬ I.toParitySystem.HasConflict (r + 1)) {X : ICls I} (hX : X ∈ classes I) :
    ∃ D', DGood (insert X A) D' ∧ Agree r (insert X A) D' ∧
      ∀ Y ∈ A, rshift D' Y = rshift D Y := by
  obtain ⟨val, hR, hsat, hinit, hK⟩ := choose_val (by omega) hG hA hcard hag hnc1 hX
  obtain ⟨D', hG', hR', hsh⟩ := local_extend hk hG hA hX hcard val hR hsat hinit
  exact ⟨D', hG', fun v a b ha hs hb => (hR' v a ha hs).trans (hK v a b ha hs hb), hsh⟩

/-! ### Game states -/

lemma vx_mem_names (p : Fin (rsGraph I 0).n) : vx p ∈ names I := by
  have := vx_mem p
  rwa [verts_zero] at this

lemma vx_cls (p : Fin (rsGraph I 0).n) : (vx p).1 ∈ classes I :=
  ((mem_names I).mp (vx_mem_names p)).1

/-- The classes of the vertices of `G₀` carrying a pebble. -/
noncomputable def rclsOf {m : ℕ} (S : GameState m (rsGraph I 0) (rsGraph I 1)) :
    Finset (ICls I) :=
  Finset.univ.biUnion fun j => match S j with
    | some (p, _) => {(vx p).1}
    | none => ∅

lemma mem_rclsOf {m : ℕ} {S : GameState m (rsGraph I 0) (rsGraph I 1)} {X : ICls I} :
    X ∈ rclsOf S ↔ ∃ j p q, S j = some (p, q) ∧ (vx p).1 = X := by
  simp only [rclsOf, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    split at hj
    · next p q h => exact ⟨j, p, q, h, (Finset.mem_singleton.mp hj).symm⟩
    · simp at hj
  · rintro ⟨j, p, q, h, rfl⟩
    exact ⟨j, by simp [h]⟩

lemma rclsOf_sub {m : ℕ} (S : GameState m (rsGraph I 0) (rsGraph I 1)) :
    rclsOf S ⊆ classes I := by
  intro X hX
  obtain ⟨j, p, q, -, rfl⟩ := mem_rclsOf.mp hX
  exact vx_cls p

lemma card_rclsOf_lift {m : ℕ} (S : GameState (m + 1) (rsGraph I 0) (rsGraph I 1))
    (i : Fin (m + 1)) : (rclsOf (Function.update S i none)).card ≤ m := by
  classical
  refine (Finset.card_biUnion_le).trans ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self, Finset.card_empty, zero_add]
  calc _ ≤ ∑ j ∈ Finset.univ.erase i, 1 := Finset.sum_le_sum fun j _ => by
          split <;> simp
    _ = m := by simp

lemma rclsOf_lift_subset {m : ℕ} (S : GameState m (rsGraph I 0) (rsGraph I 1)) (i : Fin m) :
    rclsOf (Function.update S i none) ⊆ rclsOf S := by
  intro X hX
  obtain ⟨j, p, q, h, rfl⟩ := mem_rclsOf.mp hX
  by_cases hji : j = i
  · subst hji; simp at h
  · rw [Function.update_of_ne hji] at h
    exact mem_rclsOf.mpr ⟨j, p, q, h, rfl⟩

lemma rclsOf_place {m : ℕ} (S : GameState m (rsGraph I 0) (rsGraph I 1)) (i : Fin m)
    (p : Fin (rsGraph I 0).n) (q : Fin (rsGraph I 1).n) :
    rclsOf (Function.update S i (some (p, q))) =
      insert (vx p).1 (rclsOf (Function.update S i none)) := by
  ext X
  simp only [mem_rclsOf, Finset.mem_insert]
  constructor
  · rintro ⟨j, p', q', h, rfl⟩
    by_cases hji : j = i
    · subst hji; simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inl rfl
    · rw [Function.update_of_ne hji] at h
      exact Or.inr ⟨j, p', q', by rw [Function.update_of_ne hji]; exact h, rfl⟩
  · rintro (rfl | ⟨j, p', q', h, rfl⟩)
    · exact ⟨i, p, q, by simp, rfl⟩
    · by_cases hji : j = i
      · subst hji; simp at h
      · exact ⟨j, p', q', by rw [Function.update_of_ne hji] at h ⊢; exact h, rfl⟩

/-- The pebble pairs follow the translation of `D`. -/
def RMatches {m : ℕ} (D : RDesc I) (S : GameState m (rsGraph I 0) (rsGraph I 1)) : Prop :=
  ∀ j p q, S j = some (p, q) → vx q = tr D (vx p)

lemma edgeOK_of {A : Finset (ICls I)} {D : RDesc I} (hG : DGood A D) (hA : A ⊆ classes I)
    {Y : ICls I} (hY : Y ∈ A) : EdgeOK D Y := by
  cases Y with
  | upd e h c =>
    obtain ⟨⟨h1, h2⟩, -⟩ := mem_classes_upd.mp (hA hY)
    exact ⟨h1, h2, hG.ms e c (mem_Isch.mpr ⟨_, hY, rfl⟩)⟩
  | junc e c => exact (mem_classes_junc.mp (hA hY)).1
  | coord => trivial
  | sum => trivial
  | link => trivial
  | track => trivial
  | coef => trivial

/-- Seed descriptions give partial isomorphisms. -/
lemma partialIso_of_rgood {m : ℕ} {D : RDesc I} {S : GameState m (rsGraph I 0) (rsGraph I 1)}
    (hG : DGood (rclsOf S) D) (hM : RMatches D S) :
    IsPartialIso (rsGraph I 0) (rsGraph I 1) S := by
  intro i j p q p' q' hi hj
  have hpA : (vx p).1 ∈ rclsOf S := mem_rclsOf.mpr ⟨i, p, q, hi, rfl⟩
  have hp'A : (vx p').1 ∈ rclsOf S := mem_rclsOf.mpr ⟨j, p', q', hj, rfl⟩
  have e1 := hM i p q hi
  have e2 := hM j p' q' hj
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · subst h; exact vx_injective (e1.trans e2.symm)
  · apply vx_injective
    calc vx p = tr D (tr D (vx p)) := (tr_tr D _).symm
      _ = tr D (vx q) := by rw [e1]
      _ = tr D (vx q') := by rw [h]
      _ = vx p' := by rw [e2, tr_tr]
  · show radj I (vx p) (vx p') ↔ radj I (vx q) (vx q')
    rw [e1, e2]
    exact radj_tr D (edgeOK_of hG (rclsOf_sub S) hpA) (edgeOK_of hG (rclsOf_sub S) hp'A)
  · exact (rs_color_eq p q).mpr (by rw [e1]; rfl)

/-- Duplicator's invariant on game states. -/
def RInv {m : ℕ} (r : ℕ) (S : GameState m (rsGraph I 0) (rsGraph I 1)) : Prop :=
  ∃ D : RDesc I, DGood (rclsOf S) D ∧ Agree r (rclsOf S) D ∧ RMatches D S

/-- **Duplicator's strategy.** -/
theorem rsurvivesFrom_of_inv (hk : 2 ≤ k) :
    ∀ (r : ℕ), ¬ I.toParitySystem.HasConflict r →
      ∀ (S : GameState (k + 1) (rsGraph I 0) (rsGraph I 1)), RInv r S →
        SurvivesFrom (rsGraph I 0) (rsGraph I 1) r S
  | 0, _, _, _ => trivial
  | r + 1, hnc, S, ⟨D, hG, hag, hM⟩ => by
    classical
    intro i
    set A₀ := rclsOf (Function.update S i none)
    have hsub := rclsOf_lift_subset S i
    have hG₀ : DGood A₀ D := hG.mono hsub
    have hag₀ : Agree (r + 1) A₀ D := hag.mono le_rfl hsub
    have hA₀ : A₀ ⊆ classes I := rclsOf_sub _
    have hcard := card_rclsOf_lift S i
    have hext : ∀ X : ICls I, ∃ D' : RDesc I, InitOK D' ∧ MaskOK D' ∧ (X ∈ classes I →
        DGood (insert X A₀) D' ∧ Agree r (insert X A₀) D' ∧
          ∀ Y ∈ A₀, rshift D' Y = rshift D Y) := by
      intro X
      by_cases hX : X ∈ classes I
      · obtain ⟨D', h1, h2, h3⟩ := extend_cls hk hG₀ hA₀ hcard hag₀ hnc hX
        exact ⟨D', h1.init, h1.mask, fun _ => ⟨h1, h2, h3⟩⟩
      · exact ⟨D, hG.init, hG.mask, fun h => absurd h hX⟩
    choose DX hDi hDm hDX using hext
    let f : Fin (rsGraph I 0).n → Fin (rsGraph I 1).n := fun p =>
      ix 1 (tr (DX (vx p).1) (vx p)) (tr_mem _ (hDi _) (hDm _) (vx_mem_names p))
    let g : Fin (rsGraph I 1).n → Fin (rsGraph I 0).n := fun q =>
      ix 0 (tr (DX (vx q).1) (vx q))
        (by rw [verts_zero]; exact tr_mem' _ (hDi _) (hDm _) (vx_mem q))
    have hfv : ∀ p, vx (f p) = tr (DX (vx p).1) (vx p) := fun p => vx_ix _ _
    have hgv : ∀ q, vx (g q) = tr (DX (vx q).1) (vx q) := fun q => vx_ix _ _
    let F : Fin (rsGraph I 0).n ≃ Fin (rsGraph I 1).n :=
      { toFun := f
        invFun := g
        left_inv := fun p => vx_injective (by rw [hgv, hfv, tr_fst, tr_tr])
        right_inv := fun q => vx_injective (by rw [hfv, hgv, tr_fst, tr_tr]) }
    refine ⟨F, fun p => ?_⟩
    have hp := hDX (vx p).1 (vx_cls p)
    set S' := Function.update S i (some (p, F p))
    have hcls : rclsOf S' = insert (vx p).1 A₀ := rclsOf_place S i p _
    have hM' : RMatches (DX (vx p).1) S' := by
      intro j p' q' hj
      by_cases hji : j = i
      · subst hji
        simp only [S', Function.update_self, Option.some.injEq, Prod.mk.injEq] at hj
        obtain ⟨rfl, rfl⟩ := hj
        exact hfv p
      · rw [show S' j = S j from Function.update_of_ne hji _ _] at hj
        have hY : (vx p').1 ∈ A₀ :=
          mem_rclsOf.mpr ⟨j, p', q', by rw [Function.update_of_ne hji]; exact hj, rfl⟩
        rw [hM j p' q' hj]
        simp only [tr, hp.2.2 _ hY]
    have hG' : DGood (rclsOf S') (DX (vx p).1) := hcls ▸ hp.1
    have hag' : Agree r (rclsOf S') (DX (vx p).1) := hcls ▸ hp.2.1
    exact ⟨partialIso_of_rgood hG' hM', rsurvivesFrom_of_inv hk r
      (fun h => hnc (hasConflict_mono I (Nat.le_succ r) h)) S' ⟨_, hG', hag', hM'⟩⟩

/-- **Part (2) of the row-space compiler.** Duplicator survives `r` rounds as long as `K_r` is
conflict-free. -/
theorem duplicatorSurvives (hk : 3 ≤ k) {r : ℕ} (hnc : ¬ I.toParitySystem.HasConflict r) :
    DuplicatorSurvives (k + 1) r (rsGraph I 0) (rsGraph I 1) := by
  have h0 : rclsOf (I := I) (fun _ : Fin (k + 1) => none) = ∅ := by
    ext X; simp [mem_rclsOf]
  refine ⟨(card_verts I 0).trans (card_verts I 1).symm,
    rsurvivesFrom_of_inv (by omega) r hnc _ ⟨rdesc0 I, ?_, ?_, fun _ _ _ h => by simp at h⟩⟩
  · rw [h0]; exact dgood_empty
  · rw [h0]; exact agree_empty (by omega) r _

end Lax119563Proofs.RowSpace
