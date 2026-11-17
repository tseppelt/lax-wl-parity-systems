import Lax119563Proofs.Reduction.GEnum

/-!
# Basic facts about `Fits` and `cost`

* `Xp.Fits.mono`, `Gn.Fits.mono`: fitting below `B` is monotone in `B`;
* `Gn.lt_of_mem_out`: every emitted value of a fitting generator is `< B`;
* `Gn.length_out_le_cost`: a generator emits at most `cost` values.
-/

namespace Lax119563Proofs.Reduction

namespace Xp

lemma Fits.mono {B B' : ℕ} (hB : B ≤ B') {ρ : List ℕ} (e : Xp) : e.Fits B ρ → e.Fits B' ρ := by
  induction e with
  | var _ => exact fun h => lt_of_lt_of_le h hB
  | const _ => exact fun h => lt_of_lt_of_le h hB
  | add _ _ ia ib => exact fun h => ⟨ia h.1, ib h.2.1, lt_of_lt_of_le h.2.2 hB⟩
  | lt _ _ ia ib => exact fun h => ⟨ia h.1, ib h.2⟩
  | half _ ia => exact ia
  | odd _ ia => exact ia
  | mulB _ _ _ ia ib ik => exact fun h => ⟨ia h.1, ib h.2.1, ik h.2.2.1, lt_of_lt_of_le h.2.2.2 hB⟩
  | shl _ _ ia ik => exact fun h => ⟨ia h.1, ik h.2.1, lt_of_lt_of_le h.2.2 hB⟩
  | shr _ _ ia ik => exact fun h => ⟨ia h.1, ik h.2⟩
  | xorM _ _ _ ia ib ik => exact fun h => ⟨ia h.1, ib h.2.1, ik h.2.2.1, lt_of_lt_of_le h.2.2.2 hB⟩

end Xp

namespace Gn

variable {x : List Bool}

lemma Fits.mono {B B' : ℕ} (hB : B ≤ B') (g : Gn) : ∀ {ρ : List ℕ}, g.Fits x B ρ →
    g.Fits x B' ρ := by
  induction g with
  | skip => intro _ _; trivial
  | emit e => intro _ h; exact Xp.Fits.mono hB _ h
  | seq g h ihg ihh => intro _ H; exact ⟨ihg H.1, ihh H.2⟩
  | ite c g h ihg ihh =>
    intro ρ H
    refine ⟨Xp.Fits.mono hB _ H.1, ?_⟩
    have H2 := H.2
    split_ifs at H2 ⊢
    · exact ihg H2
    · exact ihh H2
  | bind e g ih => intro _ H; exact ⟨Xp.Fits.mono hB _ H.1, ih H.2⟩
  | loop lim g ih => intro _ H; exact ⟨Xp.Fits.mono hB _ H.1, fun k hk => ih (H.2 k hk)⟩
  | loopX lim g ih => intro _ H; exact ⟨Xp.Fits.mono hB _ H.1, fun k hk => ih (H.2 k hk)⟩
  | len g ih => intro _ H; exact ⟨lt_of_lt_of_le H.1 hB, ih H.2⟩
  | log e g ih => intro _ H; exact ⟨Xp.Fits.mono hB _ H.1, ih H.2⟩
  | count g h ihg ihh => intro _ H; exact ⟨lt_of_lt_of_le H.1 hB, ihg H.2.1, ihh H.2.2⟩

lemma lt_of_mem_out {B : ℕ} (g : Gn) : ∀ {ρ : List ℕ}, g.Fits x B ρ →
    ∀ v ∈ g.out x ρ, v < B := by
  induction g with
  | skip => intro _ _ v hv; simp [out] at hv
  | emit e =>
    intro ρ h v hv
    simp only [out, List.mem_singleton] at hv
    subst hv; exact Xp.eval_lt h
  | seq g h ihg ihh =>
    intro ρ H v hv
    simp only [out, List.mem_append] at hv
    rcases hv with hv | hv
    · exact ihg H.1 v hv
    · exact ihh H.2 v hv
  | ite c g h ihg ihh =>
    intro ρ H v hv
    have H2 := H.2
    simp only [out] at hv
    split_ifs at H2 hv
    · exact ihg H2 v hv
    · exact ihh H2 v hv
  | bind e g ih => intro ρ H v hv; exact ih H.2 v hv
  | loop lim g ih =>
    intro ρ H v hv
    simp only [out, List.mem_flatMap, List.mem_range] at hv
    obtain ⟨k, hk, hv⟩ := hv
    exact ih (H.2 k hk) v hv
  | loopX lim g ih =>
    intro ρ H v hv
    simp only [out, List.mem_flatMap, List.mem_range] at hv
    obtain ⟨k, hk, hv⟩ := hv
    exact ih (H.2 k hk) v hv
  | len g ih => intro ρ H v hv; exact ih H.2 v hv
  | log e g ih => intro ρ H v hv; exact ih H.2 v hv
  | count g h ihg ihh => intro ρ H v hv; exact ihh H.2.2 v hv

lemma length_flatMap_range_le {β : Type} (L : ℕ) (f : ℕ → List β) (c : ℕ → ℕ)
    (h : ∀ k < L, (f k).length ≤ c k) :
    ((List.range L).flatMap f).length ≤ ∑ k ∈ Finset.range L, c k := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, Finset.sum_range_succ]
    have := ih fun k hk => h k (by omega)
    have := h L (by omega)
    simp only [List.flatMap_singleton]
    omega

lemma length_out_le_cost (g : Gn) : ∀ ρ : List ℕ, (g.out x ρ).length ≤ g.cost x ρ := by
  induction g with
  | skip => intro _; simp [out, cost]
  | emit e => intro _; simp [out, cost]
  | seq g h ihg ihh =>
    intro ρ; have := ihg ρ; have := ihh ρ; simp only [out, cost, List.length_append]; omega
  | ite c g h ihg ihh =>
    intro ρ; have := ihg ρ; have := ihh ρ
    simp only [out, cost]
    split_ifs <;> omega
  | bind e g ih => intro ρ; have := ih (ρ ++ [e.eval ρ]); simp only [out, cost]; omega
  | loop lim g ih =>
    intro ρ
    simp only [out, cost]
    have := length_flatMap_range_le (lim.eval ρ) (fun k => g.out x (ρ ++ [lim.eval ρ, k]))
      (fun k => g.cost x (ρ ++ [lim.eval ρ, k]) + 1) fun k _ => by
        have := ih (ρ ++ [lim.eval ρ, k]); omega
    omega
  | loopX lim g ih =>
    intro ρ
    simp only [out, cost]
    have := length_flatMap_range_le (lim.eval ρ)
      (fun k => g.out x (ρ ++ [lim.eval ρ, k, inBit x k]))
      (fun k => g.cost x (ρ ++ [lim.eval ρ, k, inBit x k]) + 1) fun k _ => by
        have := ih (ρ ++ [lim.eval ρ, k, inBit x k]); omega
    omega
  | len g ih => intro ρ; have := ih (ρ ++ [x.length]); simp only [out, cost]; omega
  | log e g ih =>
    intro ρ; have := ih (ρ ++ [Nat.log 2 (e.eval ρ)]); simp only [out, cost]; omega
  | count g h ihg ihh =>
    intro ρ; have := ihh (ρ ++ [(g.out x (ρ ++ [0])).length]); simp only [out, cost]; omega

end Gn

end Lax119563Proofs.Reduction
