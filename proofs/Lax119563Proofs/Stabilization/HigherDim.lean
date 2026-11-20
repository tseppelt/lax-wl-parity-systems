import Lax119563.Stabilization
import Lax119563Proofs.Stabilization.Colorings
import Lax119563Proofs.Stabilization.TwoDim

/-!
# Reducing to dimension two (Döring–Neuen §6.2)

For `k = m + 2`, if `k`-WL does not stabilize after any of the rounds `0, …, r - 1` on `G`
with `n` vertices, then `r ≤ 10 n` (`k = 2`) resp. `r ≤ 3 n^(k-2) + 10 n^(k-1)` (`k ≥ 3`).

Differences to the paper: the WL sequence is infinite, so Claim 6.6 holds for every round `r`
with `χ_r ≻ χ_{r+1}` (no boundary terms); we take `S = V^(k-2)` (all prefixes) instead of the
sorted prefixes, so Claim 6.7 is not needed; Claim 6.6 is proved without the partition of the
split class, directly from Claim 6.5.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.Stabilization

namespace Lax119563Proofs.Stabilization

/-! ### Counting strict steps of monotone sequences -/

theorem card_filter_add_le (a : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hmono : ∀ i, a i ≤ a (i + 1)) (hstrict : ∀ i, P i → a i < a (i + 1)) (L : ℕ) :
    ((Finset.range L).filter P).card + a 0 ≤ a L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · have := Finset.card_insert_le L ((Finset.range L).filter P)
      have := hstrict L h
      omega
    · have := hmono L
      omega

/-- Shifting a filter by `c`. -/
theorem card_filter_shift_le (P : ℕ → Prop) [DecidablePred P] (r c : ℕ) :
    ((Finset.range r).filter fun i => P (i + c)).card ≤
      ((Finset.range (r + c)).filter P).card := by
  rw [← Finset.card_map (addRightEmbedding c)]
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_range, addRightEmbedding_apply] at hj ⊢
  obtain ⟨i, ⟨hi, hP⟩, rfl⟩ := hj
  exact ⟨by omega, hP⟩

variable {G : ColoredGraph} {m : ℕ}

/-! ### The projections `χ^v` -/

/-- `χ^v_r ≻ χ^v_{r+1}`. -/
def ProjSplits (G : ColoredGraph) (r : ℕ) (v : Fin m → Fin G.n) : Prop :=
  ∃ a b c d, proj G r v a b = proj G r v c d ∧ proj G (r + 1) v a b ≠ proj G (r + 1) v c d

/-- The weak chain `ℂ 1, ⟨χ^v_0⟩, ⟨χ^v_1⟩, …`. -/
noncomputable def projChain (G : ColoredGraph) (v : Fin m → Fin G.n) :
    ℕ → Submodule ℂ (Matrix (Fin G.n) (Fin G.n) ℂ)
  | 0 => ℂ ∙ 1
  | r + 1 => classSpace (proj G r v)

theorem isChain_projChain (v : Fin m → Fin G.n) (ℓ : ℕ) : IsChain (projChain G v) ℓ where
  zero := rfl
  star_mem := by
    intro i _ x hx
    cases i with
    | zero =>
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      exact Submodule.mem_span_singleton.2 ⟨star c, by simp [star_smul]⟩
    | succ i => exact star_mem_classSpace_proj i v hx
  mul_le := by
    intro i _
    cases i with
    | zero =>
      rw [Submodule.mul_le]
      intro x hx y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [smul_mul_smul_comm, one_mul]
      exact Submodule.smul_mem _ _ (one_mem_classSpace_proj 0 v)
    | succ i => exact classSpace_proj_mul_le i v

/-- `|I^v| ≤ 10 n`, from the two-dimensional bound applied to the chain of `χ^v`. -/
theorem card_projSplits_le (v : Fin m → Fin G.n) (r : ℕ) [DecidablePred fun i => ProjSplits G i v] :
    ((Finset.range r).filter fun i => ProjSplits G i v).card ≤ 10 * G.n := by
  classical
  have hb := matrix_chainBound G.n (projChain G v) (r + 1) (isChain_projChain v _)
  have : ((Finset.range r).filter fun i => ProjSplits G i v).card ≤
      strictSteps (projChain G v) (r + 1) := by
    unfold strictSteps
    rw [← Finset.card_map (addRightEmbedding 1)]
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_range,
      addRightEmbedding_apply] at hj ⊢
    obtain ⟨i, ⟨hi, a, b, c, d, h1, h2⟩, rfl⟩ := hj
    refine ⟨by omega, fun heq => h2 (eq_of_classSpace_le ?_ h1)⟩
    change classSpace (proj G i v) = classSpace (proj G (i + 1) v) at heq
    exact heq.symm.le
  omega

/-! ### The coloring `χ̄` of `(k-2)`-tuples (`k = m + 3`) -/

/-- `χ̄_r (v) = χ_r (ext v)`, `ext v = (v, v_last, v_last)`. -/
noncomputable def barColor (G : ColoredGraph) (r : ℕ) (v : Fin (m + 1) → Fin G.n) :
    Color (m + 1 + 2) r :=
  proj G r v (v (Fin.last m)) (v (Fin.last m))

/-- The round-`r` part of a round-`(r+1)` color. -/
def colorFst {k r : ℕ} (c : Color k (r + 1)) : Color k r :=
  Prod.fst (α := Color k r) (β := Multiset (Fin k → Color k r)) c

/-- `χ̄_r ≻ χ̄_{r+1}`. -/
def BarSplits (G : ColoredGraph) (m r : ℕ) : Prop :=
  ∃ v w : Fin (m + 1) → Fin G.n,
    barColor G r v = barColor G r w ∧ barColor G (r + 1) v ≠ barColor G (r + 1) w

/-- `|Ī| ≤ n^(k-2)`: the number of classes of `χ̄_r` grows strictly at every split. -/
theorem card_barSplits_le (L : ℕ) [DecidablePred (BarSplits G m)] :
    ((Finset.range L).filter (BarSplits G m)).card ≤ G.n ^ (m + 1) := by
  classical
  let F : ℕ → ℕ := fun r =>
    ((Finset.univ : Finset (Fin (m + 1) → Fin G.n)).image (barColor G r)).card
  have himage : ∀ r, (Finset.univ : Finset (Fin (m + 1) → Fin G.n)).image (barColor G r) =
      ((Finset.univ : Finset (Fin (m + 1) → Fin G.n)).image (barColor G (r + 1))).image
        colorFst := by
    intro r
    rw [Finset.image_image]
    rfl
  have hmono : ∀ r, F r ≤ F (r + 1) := by
    intro r
    simp only [F]
    rw [himage r]
    exact Finset.card_image_le
  have hstrict : ∀ r, BarSplits G m r → F r < F (r + 1) := by
    intro r ⟨v, w, h1, h2⟩
    refine lt_of_le_of_ne (hmono r) fun heq => h2 ?_
    simp only [F] at heq
    rw [himage r] at heq
    have hinj := Finset.card_image_iff.1 heq
    exact hinj (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ v)))
      (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ w))) h1
  have h := card_filter_add_le F (BarSplits G m) hmono hstrict L
  have hF : F L ≤ G.n ^ (m + 1) := by
    simp only [F]
    refine Finset.card_image_le.trans ?_
    simp
  omega

/-! ### Claims 6.5 and 6.6 -/

/-- **Claim 6.5.** -/
theorem barColor_ne {r : ℕ} {v w : Fin (m + 1) → Fin G.n} {a b : Fin G.n}
    (h : ∀ x y, proj G r v a b ≠ proj G r w x y) :
    barColor G (r + 2) v ≠ barColor G (r + 2) w := by
  -- (14)
  have h14 := proj_succ_diag_ne h
  -- (15)
  have h15 : ∀ y, proj G (r + 1) v (v (Fin.last m)) a ≠ proj G (r + 1) w (w (Fin.last m)) y := by
    intro y hy
    have := proj_shuffle hy (Fin.last (m + 1 + 1)) (Fin.last (m + 1 + 1))
    simp only [tup_last] at this
    exact h14 y this
  -- (16)
  have h16 : ∀ x y, proj G (r + 1) v (v (Fin.last m)) a ≠ proj G (r + 1) w x y := by
    intro x y hxy
    have := eq_iff_of_color_eq hxy (vIdx (m + 1) (Fin.last m)) (penIdx (m + 1))
    simp only [tup_vIdx, tup_pen, true_iff] at this
    rw [← this] at hxy
    exact h15 y hxy
  exact proj_succ_diag_ne h16 (w (Fin.last m))

/-- A failure of stability is a pair of tuples `(v, a, b)`, `(w, c, d)` split by round
`r + 1`. -/
theorem exists_split {r : ℕ} (hs : ¬ StabilizesAfter (m + 2) r G) :
    ∃ (v w : Fin m → Fin G.n) (a b c d : Fin G.n),
      proj G r v a b = proj G r w c d ∧ proj G (r + 1) v a b ≠ proj G (r + 1) w c d := by
  simp only [StabilizesAfter, not_forall] at hs
  obtain ⟨p, q, hpq⟩ := hs
  have h : color G r p = color G r q ∧ color G (r + 1) p ≠ color G (r + 1) q := by
    by_cases h1 : color G r p = color G r q
    · exact ⟨h1, fun h2 => hpq ⟨fun _ => h2, fun _ => h1⟩⟩
    · exact absurd (Iff.intro (fun h => absurd h h1) fun h2 => color_eq_of_succ h2) hpq
  refine ⟨p ∘ vIdx m, q ∘ vIdx m, p (penIdx m), p (Fin.last (m + 1)), q (penIdx m),
    q (Fin.last (m + 1)), ?_, ?_⟩
  · unfold proj; rw [tup_eta, tup_eta]; exact h.1
  · unfold proj; rw [tup_eta, tup_eta]; exact h.2

/-- **Claim 6.6**: if `χ_r ≻ χ_{r+1}` but no `χ^v` splits in round `r + 1`, then `χ̄` splits
in one of the rounds `r + 1, r + 2, r + 3`. -/
theorem barSplits_of_not_projSplits {r : ℕ} (hs : ¬ StabilizesAfter (m + 1 + 2) r G)
    (hv : ∀ v : Fin (m + 1) → Fin G.n, ¬ ProjSplits G r v) :
    BarSplits G m r ∨ BarSplits G m (r + 1) ∨ BarSplits G m (r + 2) := by
  obtain ⟨v, w, a, b, c, d, h1, h2⟩ := exists_split hs
  have h0 : barColor G r v = barColor G r w := by
    have := proj_shuffle h1 (vIdx (m + 1) (Fin.last m)) (vIdx (m + 1) (Fin.last m))
    simpa only [tup_vIdx, barColor] using this
  have h3 : barColor G (r + 1 + 2) v ≠ barColor G (r + 1 + 2) w := by
    refine barColor_ne (a := a) (b := b) fun x y hxy => h2 ?_
    have e1 : proj G r w c d = proj G r w x y := h1.symm.trans (proj_eq_of_succ hxy)
    have e2 : proj G (r + 1) w c d = proj G (r + 1) w x y := by
      by_contra hne
      exact hv w ⟨c, d, x, y, e1, hne⟩
    exact hxy.trans e2.symm
  simp only [BarSplits]
  by_contra hc
  simp only [not_or, not_exists, not_and, not_not] at hc
  obtain ⟨n0, n1, n2⟩ := hc
  exact h3 (n2 v w (n1 v w (n0 v w h0)))

/-! ### The count -/

/-- `k = 2`: `r ≤ 10 n`. -/
theorem rounds_le_two {r : ℕ} (hr : ∀ i < r, ¬ StabilizesAfter 2 i G) : r ≤ 10 * G.n := by
  classical
  have hsub : Finset.range r ⊆
      (Finset.range r).filter fun i => ProjSplits G i (Fin.elim0 : Fin 0 → Fin G.n) := by
    intro i hi
    obtain ⟨v, w, a, b, c, d, h1, h2⟩ := exists_split (m := 0) (hr i (Finset.mem_range.1 hi))
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst hv hw
    exact Finset.mem_filter.2 ⟨hi, a, b, c, d, h1, h2⟩
  have := (Finset.card_le_card hsub).trans (card_projSplits_le _ r)
  simpa using this

/-- `k = m + 3`: `r ≤ 3 n^(k-2) + 10 n^(k-1)`
(`r ≤ |{rounds where some χ^v splits}| + 3 |Ī|`). -/
theorem rounds_le {r : ℕ} (hr : ∀ i < r, ¬ StabilizesAfter (m + 1 + 2) i G) :
    r ≤ 3 * G.n ^ (m + 1) + 10 * G.n ^ (m + 2) := by
  classical
  set S := Finset.range r
  let A := S.filter fun i => ∃ v : Fin (m + 1) → Fin G.n, ProjSplits G i v
  let B : ℕ → Finset ℕ := fun c => S.filter fun i => BarSplits G m (i + c)
  have hcover : S ⊆ A ∪ (B 0 ∪ B 1 ∪ B 2) := by
    intro i hi
    by_cases hv : ∃ v : Fin (m + 1) → Fin G.n, ProjSplits G i v
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hi, hv⟩)
    · simp only [not_exists] at hv
      have := barSplits_of_not_projSplits (hr i (Finset.mem_range.1 hi)) hv
      simp only [Finset.mem_union, B, Finset.mem_filter, add_zero]
      tauto
  have hA : A.card ≤ G.n ^ (m + 1) * (10 * G.n) := by
    have hsub : A ⊆ (Finset.univ : Finset (Fin (m + 1) → Fin G.n)).biUnion
        fun v => S.filter fun i => ProjSplits G i v := by
      intro i hi
      obtain ⟨hi, v, hv⟩ := Finset.mem_filter.1 hi
      exact Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _, Finset.mem_filter.2 ⟨hi, hv⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    refine (Finset.sum_le_sum fun v _ => card_projSplits_le v r).trans ?_
    simp
  have hB : ∀ c, (B c).card ≤ G.n ^ (m + 1) := fun c =>
    (card_filter_shift_le (BarSplits G m) r c).trans (card_barSplits_le _)
  have hS : S.card ≤ A.card + ((B 0).card + (B 1).card + (B 2).card) := by
    refine (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans ?_)
    have := Finset.card_union_le (B 0 ∪ B 1) (B 2)
    have := Finset.card_union_le (B 0) (B 1)
    omega
  have h0 := hB 0
  have h1 := hB 1
  have h2 := hB 2
  have hpow : G.n ^ (m + 1) * (10 * G.n) = 10 * G.n ^ (m + 2) := by ring
  simp only [S, Finset.card_range] at hS
  omega

end Lax119563Proofs.Stabilization
