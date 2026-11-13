import Lax119563Proofs.Matrix.Exposure

/-!
# Duplicator's invariant

`Good r A D`: the description `D` is consistent on the pebbled classes `A`, its partial seeds
annihilate block-even codewords, the exposed values agree with `K_r`, and `K_r` is
conflict-free. This file proves the basic properties of the invariant and the extension of a
single location seed.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-- Duplicator's invariant with `r` rounds remaining. -/
structure Good (r : ℕ) (A : Finset (ICls I)) (D : Desc I) : Prop where
  init : InitOK D
  ms : ∀ e, ∀ c ∈ Isch A e, MS D e c
  even : ∀ v, EvenKills (D.z v) (Iloc A v)
  agree : ∀ v a b, IsAddress a → supp a ⊆ Iloc A v →
    ((v, a), b) ∈ I.toParitySystem.known r → dot (ind a) (D.z v) = b
  noConflict : ¬ I.toParitySystem.HasConflict r

lemma Good.mono {r r' : ℕ} {A B : Finset (ICls I)} {D : Desc I} (h : Good r A D) (hr : r' ≤ r)
    (hB : B ⊆ A) : Good r' B D where
  init := h.init
  ms e c hc := h.ms e c (Isch_mono hB e hc)
  even v := (h.even v).mono (Iloc_mono hB v)
  agree v a b ha hs hb := h.agree v a b ha (hs.trans (Iloc_mono hB v)) (known_mono I hr hb)
  noConflict hc := h.noConflict (hasConflict_mono I hr hc)

lemma Good.ms_link {r : ℕ} {A : Finset (ICls I)} {D : Desc I} (h : Good r A D) {X : ICls I}
    (hX : X ∈ A) : ∀ e c, X = .link e c → MS D e c := by
  rintro e c rfl
  exact h.ms e c (mem_Isch.mpr ⟨_, hX, rfl⟩)

/-! ### Facts -/

lemma fact_unique {r : ℕ} (hnc : ¬ I.toParitySystem.HasConflict r)
    {X : Fin I.numLocations × (Fin k → BlockCoord ℓ)} {b b' : ZMod 2}
    (h : (X, b) ∈ I.toParitySystem.known r) (h' : (X, b') ∈ I.toParitySystem.known r) :
    b = b' := by
  by_contra hne
  apply hnc
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> rcases zmod2_eq_zero_or_one b' with rfl | rfl
  · exact absurd rfl hne
  · exact ⟨X, h, h'⟩
  · exact ⟨X, h', h⟩
  · exact absurd rfl hne

lemma initSeed_evenKills (v : Fin I.numLocations) (J : Finset (Coord k ℓ)) :
    EvenKills (initSeed I v) J := by
  intro y hy he _
  rw [dot, sum_coord]
  unfold initSeed
  split
  · next b _ =>
    have : ∀ i : Fin k, ∑ b', y (i, b') * (if ((i, b') : Coord k ℓ).1.val = 0 then b else 0) =
        if i.val = 0 then blockSum y i * b else 0 := by
      intro i
      split
      · simp [blockSum, Finset.sum_mul]
      · simp
    simp_rw [this, he, zero_mul]
    simp
  · simp

lemma dot_initSeed {v : Fin I.numLocations} {b : ZMod 2} (hv : I.init v = some b) (hk : 0 < k)
    (a : Fin k → BlockCoord ℓ) : dot (ind a) (initSeed I v) = b := by
  rw [dot_ind_left]
  simp only [initSeed, hv]
  rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
  · simp
  · intro i _ hi
    rw [if_neg]
    intro h; exact hi (Fin.ext h)
  · simp

/-- At an initialized location, all facts of a conflict-free round agree with the
initialization. -/
lemma fact_init {r : ℕ} (hnc : ¬ I.toParitySystem.HasConflict r) {v : Fin I.numLocations}
    {b ι : ZMod 2} (hv : I.init v = some ι) {a : Fin k → BlockCoord ℓ} (ha : IsAddress a)
    (hs : supp a ⊆ I.domain v) (h : ((v, a), b) ∈ I.toParitySystem.known r) : b = ι := by
  have h0 : ((v, a), ι) ∈ I.toParitySystem.known r :=
    known_mono I (Nat.zero_le r) ⟨ι, hv, rfl, ha, hs⟩
  exact fact_unique hnc h h0

/-- The initial description. -/
def desc0 (I : ImplicitParitySystem k ℓ) : Desc I where
  z v := initSeed I v
  lam _ _ := 0

lemma good_empty (hk : 0 < k) {r : ℕ} (hnc : ¬ I.toParitySystem.HasConflict r) :
    Good r ∅ (desc0 I) where
  init _ _ := rfl
  ms e c hc := by simp [Isch] at hc
  even v := initSeed_evenKills v _
  agree v a b ha hs _ := by
    exfalso
    have : (supp a).card = 0 := by
      rw [Finset.card_eq_zero]; simpa [Iloc] using hs
    rw [card_supp] at this; omega
  noConflict := hnc

/-! ### Extending the seed of one location -/

/-- Extending the seed of location `v` by the coordinate `d`, with prescribed value `p` on the
new address. -/
lemma extend_loc (hk : 0 < k) {r : ℕ} {A : Finset (ICls I)} {D : Desc I}
    (hG : Good (r + 1) A D) (v : Fin I.numLocations) (d : Coord k ℓ)
    (hcard : (insert d (Iloc A v)).card ≤ k + 1) (hdom : insert d (Iloc A v) ⊆ I.domain v)
    (p : ZMod 2)
    (hp : ∀ a b, IsAddress a → supp a ⊆ insert d (Iloc A v) → d ∈ supp a → d ∉ Iloc A v →
      ((v, a), b) ∈ I.toParitySystem.known r → p = b) :
    ∃ zv : Vec k ℓ, (∀ d' ∈ Iloc A v, zv d' = D.z v d') ∧
      ((I.init v).isSome → zv = initSeed I v) ∧
      EvenKills zv (insert d (Iloc A v)) ∧
      (∀ a, IsAddress a → supp a ⊆ insert d (Iloc A v) → d ∈ supp a → d ∉ Iloc A v →
        dot (ind a) zv = p) ∧
      (∀ a b, IsAddress a → supp a ⊆ insert d (Iloc A v) →
        ((v, a), b) ∈ I.toParitySystem.known r → dot (ind a) zv = b) := by
  have hnc : ¬ I.toParitySystem.HasConflict r :=
    fun h => hG.noConflict (hasConflict_mono I (Nat.le_succ r) h)
  -- old addresses keep their values
  have hold : ∀ zv : Vec k ℓ, (∀ d' ∈ Iloc A v, zv d' = D.z v d') →
      ∀ a b, IsAddress a → supp a ⊆ Iloc A v →
        ((v, a), b) ∈ I.toParitySystem.known r → dot (ind a) zv = b := by
    intro zv hzv a b ha hs hb
    rw [dot_congr_suppIn (suppIn_ind.mpr hs) (z' := D.z v) hzv]
    exact hG.agree v a b ha hs (known_mono I (Nat.le_succ r) hb)
  by_cases hd : d ∈ Iloc A v
  · rw [Finset.insert_eq_of_mem hd]
    exact ⟨D.z v, fun _ _ => rfl, hG.init v, hG.even v, fun _ _ _ _ h => absurd hd h,
      hold _ fun _ _ => rfl⟩
  · cases hv : I.init v with
    | some ι =>
      have hz := hG.init v (by simp [hv])
      refine ⟨D.z v, fun _ _ => rfl, fun _ => hz, hz ▸ initSeed_evenKills v _,
        fun a ha hs hda _ => ?_, fun a b ha hs hb => ?_⟩
      · have h0 : ((v, a), ι) ∈ I.toParitySystem.known r :=
          known_mono I (Nat.zero_le r) ⟨ι, hv, rfl, ha, hs.trans hdom⟩
        rw [hz, dot_initSeed hv hk, hp a ι ha hs hda hd h0]
      · rw [hz, dot_initSeed hv hk, fact_init hnc hv ha (hs.trans hdom) hb]
    | none =>
      obtain ⟨β, hβ1, hβ2⟩ := extend_seed hk hd hcard (hG.even v) p
      have hagree : ∀ d' ∈ Iloc A v, Function.update (D.z v) d β d' = D.z v d' :=
        fun d' hd' => Function.update_of_ne (fun h => hd (by rw [← h]; exact hd')) _ _
      refine ⟨Function.update (D.z v) d β, hagree, fun h => by simp at h, hβ1,
        fun a ha hs hda _ => hβ2 a ha hs hda, fun a b ha hs hb => ?_⟩
      by_cases hda : d ∈ supp a
      · rw [hβ2 a ha hs hda, hp a b ha hs hda hd hb]
      · refine hold _ hagree a b ha ?_ hb
        intro x hx
        rcases Finset.mem_insert.mp (hs hx) with rfl | h
        · exact absurd hx hda
        · exact h

end Lax119563Proofs.Matrix
