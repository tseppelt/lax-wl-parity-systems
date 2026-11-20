import Lax119563Proofs.Reduction.CostTy

/-!
# Generators with fits and cost bounds

`Gn.HasCost τs g e d`: on every stack agreeing with the classes `τs` (with any constant), and
every input with `|x| ≤ 2^ℓ`, the generator fits below `2^(K ((ℓ : ℕ) + 1))` and costs at most
`K · 2^(e ℓ) · ((ℓ : ℕ) + 1)^(d + 1)`, for a constant `K` depending only on the constant of the stack.
`Gn.HasLen τs g τ`: the output has length in class `τ` (used for the value pushed by `count`).

Rules for every constructor (`hasCost_skip/emit/seq/ite/bind/loop/loopX/len/log/count`), with
`HasCost.mono` (larger exponents) and `HasCost.ctx` (smaller context classes), and the derived
generators `seqL`, `when`, `bindL`, `bindSub`. The cost exponents add up along
nested loops: a loop over a linear range (`P 0 1`) adds `1` to `d`, a loop over a range linear in
`|x|` (`P 1 0`) adds `1` to `e`.
-/

namespace Lax119563Proofs.Reduction

open Ty Xp

namespace Ty

lemma bnd_P_mono {e e' d d' : ℕ} (he : e ≤ e') (hd : d ≤ d') (K : ℕ) (ℓ : Sc) :
    (P e d).bnd K ℓ ≤ (P e' d').bnd K ℓ := by
  simp only [bnd]
  have h1 : 2 ^ (e * ℓ.l) ≤ 2 ^ (e' * ℓ.l) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ he)
  have h2 : ((ℓ : ℕ) + 1) ^ d ≤ ((ℓ : ℕ) + 1) ^ d' := Nat.pow_le_pow_right (by omega) hd
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

lemma lin_le_bnd (e d K : ℕ) (ℓ : Sc) : K * ((ℓ : ℕ) + 1) ≤ (P e (d + 1)).bnd K ℓ := by
  have := bnd_P_mono (Nat.zero_le e) (show 1 ≤ d + 1 by omega) K ℓ
  simpa [bnd] using this

lemma two_pow_le_bnd {e : ℕ} (he : 1 ≤ e) (d : ℕ) (ℓ : Sc) : 2 ^ ℓ.l ≤ (P e d).bnd 1 ℓ := by
  have := bnd_P_mono he (Nat.zero_le d) 1 ℓ
  simpa [bnd] using this

end Ty

namespace Gn

/-- Fits below `2^(K (ℓ+1))` with cost `≤ K 2^(e ℓ) (ℓ+1)^(d+1)`. -/
def HasCost (τs : List Ty) (g : Gn) (e d : ℕ) : Prop :=
  ∀ K₀, ∃ K, ∀ (ℓ : Sc) (x : List Bool) ρ, x.length ≤ 2 ^ ℓ.l → Ag K₀ ℓ τs ρ →
    g.Fits x (2 ^ (K * ((ℓ : ℕ) + 1))) ρ ∧ g.cost x ρ ≤ (P e (d + 1)).bnd K ℓ

/-- The output has length in class `τ`. -/
def HasLen (τs : List Ty) (g : Gn) (τ : Ty) : Prop :=
  ∀ K₀, ∃ K, ∀ (ℓ : Sc) (x : List Bool) ρ, x.length ≤ 2 ^ ℓ.l → Ag K₀ ℓ τs ρ →
    (g.out x ρ).length ≤ τ.bnd K ℓ

variable {τs : List Ty}

lemma fits_up {x : List Bool} {g : Gn} {K K' ℓ : ℕ} {ρ : List ℕ} (h : K ≤ K')
    (hf : g.Fits x (2 ^ (K * ((ℓ : ℕ) + 1))) ρ) : g.Fits x (2 ^ (K' * ((ℓ : ℕ) + 1))) ρ :=
  Fits.mono (two_pow_mono h) g hf

lemma xfits_up {e : Xp} {K K' ℓ : ℕ} {ρ : List ℕ} (h : K ≤ K')
    (hf : e.Fits (2 ^ (K * ((ℓ : ℕ) + 1))) ρ) : e.Fits (2 ^ (K' * ((ℓ : ℕ) + 1))) ρ :=
  Xp.Fits.mono (two_pow_mono h) e hf

lemma HasCost.mono {g : Gn} {e d e' d' : ℕ} (h : HasCost τs g e d) (he : e ≤ e') (hd : d ≤ d') :
    HasCost τs g e' d' := by
  intro K₀
  obtain ⟨K, hK⟩ := h K₀
  exact ⟨K, fun ℓ x ρ hx hA => ⟨(hK ℓ x ρ hx hA).1,
    le_trans (hK ℓ x ρ hx hA).2 (Ty.bnd_P_mono he (by omega) K ℓ)⟩⟩

lemma HasCost.ctx {τs' : List Ty} {g : Gn} {e d : ℕ} (hle : TysLe τs τs')
    (h : HasCost τs' g e d) : HasCost τs g e d := by
  intro K₀
  obtain ⟨K, hK⟩ := h (K₀ + liftL τs)
  exact ⟨K, fun ℓ x ρ hx hA => hK ℓ x ρ hx (hA.of_le hle)⟩

lemma HasLen.le {g : Gn} {τ τ' : Ty} (h : HasLen τs g τ) (hτ : Ty.Le τ τ') : HasLen τs g τ' := by
  intro K₀
  obtain ⟨K, hK⟩ := h K₀
  exact ⟨K + τ.lift, fun ℓ x ρ hx hA => le_trans (hK ℓ x ρ hx hA) (Ty.bnd_le_of_le hτ K ℓ)⟩

lemma HasCost.len {g : Gn} {e d : ℕ} (h : HasCost τs g e d) : HasLen τs g (P e (d + 1)) := by
  intro K₀
  obtain ⟨K, hK⟩ := h K₀
  exact ⟨K, fun ℓ x ρ hx hA => le_trans (length_out_le_cost g ρ) (hK ℓ x ρ hx hA).2⟩

/-! ## Constructors -/

lemma hasCost_skip : HasCost τs skip 0 0 := by
  intro _
  refine ⟨1, fun ℓ x ρ _ _ => ⟨trivial, ?_⟩⟩
  simp only [cost]; exact Ty.one_le_bnd le_rfl ℓ _

lemma hasCost_emit {a : Xp} {τ : Ty} (ha : HasTy τs a τ) : HasCost τs (emit a) 0 0 := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  refine ⟨Ka + 1, fun ℓ x ρ _ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  refine ⟨xfits_up (by omega) a2, ?_⟩
  have := Ty.lin_le_bnd 0 0 (Ka + 1) ℓ
  simp only [cost]; nlinarith

lemma hasCost_seq {g h : Gn} {e d : ℕ} (hg : HasCost τs g e d) (hh : HasCost τs h e d) :
    HasCost τs (seq g h) e d := by
  intro K₀
  obtain ⟨Kg, hKg⟩ := hg K₀
  obtain ⟨Kh, hKh⟩ := hh K₀
  refine ⟨Kg + Kh, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨g1, g2⟩ := hKg ℓ x ρ hx hA
  obtain ⟨h1, h2⟩ := hKh ℓ x ρ hx hA
  refine ⟨⟨fits_up (by omega) g1, fits_up (by omega) h1⟩, ?_⟩
  simp only [cost]; rw [← Ty.bnd_add]; omega

lemma hasCost_ite {c : Xp} {τ : Ty} {g h : Gn} {e d : ℕ} (hc : HasTy τs c τ)
    (hg : HasCost τs g e d) (hh : HasCost τs h e d) : HasCost τs (ite c g h) e d := by
  intro K₀
  obtain ⟨Kc, hKc⟩ := hc K₀
  obtain ⟨Kg, hKg⟩ := hg K₀
  obtain ⟨Kh, hKh⟩ := hh K₀
  refine ⟨Kc + 1 + Kg + Kh, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨c1, c2, c3⟩ := hKc ℓ ρ hA
  obtain ⟨g1, g2⟩ := hKg ℓ x ρ hx hA
  obtain ⟨h1, h2⟩ := hKh ℓ x ρ hx hA
  have hl := Ty.lin_le_bnd e d (Kc + 1) ℓ
  have e1 := Ty.bnd_add e (d + 1) (Kc + 1) Kg ℓ
  have e2 := Ty.bnd_add e (d + 1) (Kc + 1 + Kg) Kh ℓ
  refine ⟨⟨xfits_up (by omega) c2, ?_⟩, ?_⟩
  · split_ifs
    · exact fits_up (by omega) g1
    · exact fits_up (by omega) h1
  · simp only [cost]
    have : (if c.eval ρ ≠ 0 then g.cost x ρ else h.cost x ρ) ≤
        (P e (d + 1)).bnd Kg ℓ + (P e (d + 1)).bnd Kh ℓ := by split_ifs <;> omega
    nlinarith

lemma hasCost_bind {a : Xp} {τ : Ty} {g : Gn} {e d : ℕ} (ha : HasTy τs a τ)
    (hg : HasCost (τs ++ [τ]) g e d) : HasCost τs (bind a g) e d := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kg, hKg⟩ := hg (K₀ + Ka)
  refine ⟨Ka + Kg, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  have hA' : Ag (K₀ + Ka) ℓ (τs ++ [τ]) (ρ ++ [a.eval ρ]) :=
    (hA.mono (by omega)).push (le_trans a1 (Ty.bnd_mono (by omega) ℓ τ))
  obtain ⟨g1, g2⟩ := hKg ℓ x _ hx hA'
  refine ⟨⟨xfits_up (by omega) a2, fits_up (by omega) g1⟩, ?_⟩
  have hl := Ty.lin_le_bnd e d Ka ℓ
  have e1 := Ty.bnd_add e (d + 1) Ka Kg ℓ
  simp only [cost]; omega

lemma sum_range_le_mul {L T : ℕ} (c : ℕ → ℕ) (h : ∀ k < L, c k ≤ T) :
    ∑ k ∈ Finset.range L, (c k + 1) ≤ L * (T + 1) := by
  have : ∑ k ∈ Finset.range L, (c k + 1) ≤ ∑ k ∈ Finset.range L, (T + 1) :=
    Finset.sum_le_sum fun k hk => by have := h k (Finset.mem_range.mp hk); omega
  simpa using this

/-- The arithmetic of a loop. -/
lemma loop_arith {Kl Kg ℓ L c0 S X Y : ℕ} (hX : 1 ≤ X) (hY : ℓ + 1 ≤ Y) (hL : L ≤ Kl * X)
    (hc0 : c0 ≤ Kl * ((ℓ : ℕ) + 1)) (hS : S ≤ L * (Kg * Y + 1)) :
    c0 + 1 + S ≤ (Kl * Kg + 2 * Kl + 1) * (X * Y) := by
  have hY1 : 1 ≤ Y := by omega
  have h1 : c0 ≤ Kl * (X * Y) := le_trans hc0 (Nat.mul_le_mul_left _ (by nlinarith))
  have h2 : 1 ≤ X * Y := by nlinarith
  have h3 : S ≤ Kl * X * (Kg * Y + 1) := le_trans hS (Nat.mul_le_mul_right _ hL)
  have h4 : Kl * X * (Kg * Y + 1) ≤ Kl * Kg * (X * Y) + Kl * (X * Y) := by
    have : Kl * X ≤ Kl * (X * Y) := Nat.mul_le_mul_left _ (by nlinarith)
    nlinarith
  nlinarith

lemma bnd_split (e₀ d₀ e d K : ℕ) (ℓ : Sc) :
    (P (e₀ + e) (d₀ + d + 1)).bnd K ℓ =
      K * ((2 ^ (e₀ * ℓ.l) * ((ℓ : ℕ) + 1) ^ d₀) * (2 ^ (e * ℓ.l) * ((ℓ : ℕ) + 1) ^ (d + 1))) := by
  simp only [Ty.bnd, Nat.add_mul, pow_add]; ring

lemma one_le_X (e d : ℕ) (ℓ : Sc) : 1 ≤ 2 ^ (e * ℓ.l) * ((ℓ : ℕ) + 1) ^ d :=
  Nat.one_le_iff_ne_zero.mpr (by positivity)

lemma succ_le_Y (e d : ℕ) (ℓ : Sc) : ↑ℓ + 1 ≤ 2 ^ (e * ℓ.l) * ((ℓ : ℕ) + 1) ^ (d + 1) := by
  have := Ty.lin_le_bnd e d 1 ℓ
  simpa [Ty.bnd] using this

lemma hasCost_loop {lim : Xp} {g : Gn} {e₀ d₀ e d : ℕ} (hl : HasTy τs lim (P e₀ d₀))
    (hg : HasCost (τs ++ [P e₀ d₀, P e₀ d₀]) g e d) :
    HasCost τs (loop lim g) (e₀ + e) (d₀ + d) := by
  intro K₀
  obtain ⟨Kl, hKl⟩ := hl K₀
  obtain ⟨Kg, hKg⟩ := hg (K₀ + Kl)
  refine ⟨Kl * Kg + 2 * Kl + 1 + Kg, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨l1, l2, l3⟩ := hKl ℓ ρ hA
  have hb : ∀ k < lim.eval ρ, Ag (K₀ + Kl) ℓ (τs ++ [P e₀ d₀, P e₀ d₀]) (ρ ++ [lim.eval ρ, k]) :=
    fun k hk => (hA.mono (by omega)).push2 (le_trans l1 (Ty.bnd_mono (by omega) ℓ _))
      (le_trans (le_trans hk.le l1) (Ty.bnd_mono (by omega) ℓ _))
  refine ⟨⟨xfits_up (by omega) l2, fun k hk => fits_up (by omega) (hKg ℓ x _ hx (hb k hk)).1⟩, ?_⟩
  simp only [cost]
  rw [bnd_split]
  have hS := sum_range_le_mul (L := lim.eval ρ) (T := (P e (d + 1)).bnd Kg ℓ)
    (fun k => g.cost x (ρ ++ [lim.eval ρ, k])) fun k hk => (hKg ℓ x _ hx (hb k hk)).2
  have key := loop_arith (Kl := Kl) (Kg := Kg) (one_le_X e₀ d₀ ℓ) (succ_le_Y e d ℓ)
    (by simpa [Ty.bnd, Nat.mul_assoc] using l1) l3
    (le_trans hS (by simp [Ty.bnd, Nat.mul_assoc]))
  refine le_trans key (Nat.mul_le_mul_right _ (by omega))

lemma hasCost_loopX {lim : Xp} {g : Gn} {e₀ d₀ e d : ℕ} (hl : HasTy τs lim (P e₀ d₀))
    (hg : HasCost (τs ++ [P e₀ d₀, P e₀ d₀, P 0 0]) g e d) :
    HasCost τs (loopX lim g) (max 1 (e₀ + e)) (d₀ + d) := by
  intro K₀
  obtain ⟨Kl, hKl⟩ := hl K₀
  obtain ⟨Kg, hKg⟩ := hg (K₀ + Kl + 2)
  refine ⟨Kl * Kg + 2 * Kl + 3 + Kg, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨l1, l2, l3⟩ := hKl ℓ ρ hA
  have hb : ∀ k < lim.eval ρ, Ag (K₀ + Kl + 2) ℓ (τs ++ [P e₀ d₀, P e₀ d₀, P 0 0])
      (ρ ++ [lim.eval ρ, k, inBit x k]) :=
    fun k hk => (hA.mono (by omega)).push3 (le_trans l1 (Ty.bnd_mono (by omega) ℓ _))
      (le_trans (le_trans hk.le l1) (Ty.bnd_mono (by omega) ℓ _))
      (by rw [Ty.bnd_P00]; have := inBit_le x k; omega)
  refine ⟨⟨xfits_up (by omega) l2, fun k hk => fits_up (by omega) (hKg ℓ x _ hx (hb k hk)).1⟩, ?_⟩
  simp only [cost]
  have hS := sum_range_le_mul (L := lim.eval ρ) (T := (P e (d + 1)).bnd Kg ℓ)
    (fun k => g.cost x (ρ ++ [lim.eval ρ, k, inBit x k])) fun k hk => (hKg ℓ x _ hx (hb k hk)).2
  have key := loop_arith (Kl := Kl) (Kg := Kg) (one_le_X e₀ d₀ ℓ) (succ_le_Y e d ℓ)
    (by simpa [Ty.bnd, Nat.mul_assoc] using l1) l3
    (le_trans hS (by simp [Ty.bnd, Nat.mul_assoc]))
  rw [← bnd_split] at key
  have k1 := Ty.bnd_P_mono (le_max_right 1 (e₀ + e)) le_rfl (Kl * Kg + 2 * Kl + 1) ℓ
    (d := d₀ + d + 1)
  have k2 := Ty.two_pow_le_bnd (le_max_left 1 (e₀ + e)) (d₀ + d + 1) ℓ
  have k2' : (P (max 1 (e₀ + e)) (d₀ + d + 1)).bnd 1 ℓ + (P (max 1 (e₀ + e)) (d₀ + d + 1)).bnd 1 ℓ
      = (P (max 1 (e₀ + e)) (d₀ + d + 1)).bnd 2 ℓ := Ty.bnd_add ..
  have k2'' := Nat.one_le_two_pow (n := ℓ.l)
  have k3 := Ty.bnd_add (max 1 (e₀ + e)) (d₀ + d + 1) (Kl * Kg + 2 * Kl + 1) 2 ℓ
  have k4 := Ty.bnd_mono (show Kl * Kg + 2 * Kl + 1 + 2 ≤ Kl * Kg + 2 * Kl + 3 + Kg by omega) ℓ
    (P (max 1 (e₀ + e)) (d₀ + d + 1))
  omega

lemma log_le_lin {v K : ℕ} {ℓ : Sc} {τ : Ty} (hv : v ≤ τ.bnd K ℓ) :
    Nat.log 2 v ≤ (P 0 1).bnd (K + τ.lift) ℓ := by
  have h := le_trans hv (Ty.bnd_le_big K ℓ τ)
  calc Nat.log 2 v ≤ Nat.log 2 (2 ^ ((K + τ.lift) * ((ℓ : ℕ) + 1))) := Nat.log_mono_right h
    _ = _ := by rw [Nat.log_pow (by norm_num)]; simp [Ty.bnd]

lemma hasCost_log {a : Xp} {g : Gn} {e₀ d₀ e d : ℕ} (ha : HasTy τs a (P e₀ d₀))
    (hg : HasCost (τs ++ [P 0 1]) g e d) : HasCost τs (log a g) (max e₀ e) (max d₀ d) := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kg, hKg⟩ := hg (K₀ + Ka + e₀ + d₀)
  refine ⟨2 * Ka + Kg + 2, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  have hA' : Ag (K₀ + Ka + e₀ + d₀) ℓ (τs ++ [P 0 1]) (ρ ++ [Nat.log 2 (a.eval ρ)]) :=
    (hA.mono (by omega)).push (le_trans (log_le_lin a1)
      (Ty.bnd_mono (by simp [Ty.lift]; omega) ℓ _))
  obtain ⟨g1, g2⟩ := hKg ℓ x _ hx hA'
  refine ⟨⟨xfits_up (by omega) a2, fits_up (by omega) g1⟩, ?_⟩
  simp only [cost]
  have k1 := Ty.bnd_P_mono (le_max_right e₀ e) (show d + 1 ≤ max d₀ d + 1 by omega) Kg ℓ
  have k2 := Ty.bnd_P_mono (le_max_left e₀ e) (show d₀ ≤ max d₀ d + 1 by omega) Ka ℓ
  have k3 := Ty.lin_le_bnd (max e₀ e) (max d₀ d) (Ka + 2) ℓ
  have k4 := Ty.bnd_add (max e₀ e) (max d₀ d + 1) Ka (Ka + 2) ℓ
  have k5 := Ty.bnd_add (max e₀ e) (max d₀ d + 1) (Ka + (Ka + 2)) Kg ℓ
  have k6 : 2 ≤ (Ka + 2) * ((ℓ : ℕ) + 1) := by nlinarith
  have k7 := Ty.bnd_mono (show Ka + (Ka + 2) + Kg ≤ 2 * Ka + Kg + 2 by omega) ℓ
    (P (max e₀ e) (max d₀ d + 1))
  nlinarith

lemma hasCost_count {g h : Gn} {τ : Ty} {e d : ℕ} (hg : HasCost (τs ++ [P 0 0]) g e d)
    (hl : HasLen (τs ++ [P 0 0]) g τ) (hh : HasCost (τs ++ [τ]) h e d) :
    HasCost τs (count g h) e d := by
  intro K₀
  obtain ⟨Kg, hKg⟩ := hg K₀
  obtain ⟨Kl, hKl⟩ := hl K₀
  obtain ⟨Kh, hKh⟩ := hh (K₀ + Kl)
  refine ⟨Kg + Kh + Kl + τ.lift + 2, fun ℓ x ρ hx hA => ?_⟩
  have hA0 : Ag K₀ ℓ (τs ++ [P 0 0]) (ρ ++ [0]) := hA.push (Nat.zero_le _)
  obtain ⟨g1, g2⟩ := hKg ℓ x _ hx hA0
  have l1 := hKl ℓ x _ hx hA0
  obtain ⟨h1, h2⟩ := hKh ℓ x _ hx ((hA.mono (by omega)).push
    (le_trans l1 (Ty.bnd_mono (by omega) ℓ τ)))
  refine ⟨⟨lt_of_le_of_lt l1 (lt_of_lt_of_le (Ty.bnd_lt_big Kl ℓ τ) (two_pow_mono (by omega))),
    fits_up (by omega) g1, fits_up (by omega) h1⟩, ?_⟩
  simp only [cost]
  have k1 := Ty.one_le_bnd (le_refl 1) ℓ (P e (d + 1))
  have k2 := Ty.bnd_add e (d + 1) Kg Kh ℓ
  have k3 := Ty.bnd_add e (d + 1) (Kg + Kh) 1 ℓ
  have k4 := Ty.bnd_mono (show Kg + Kh + 1 ≤ Kg + Kh + Kl + τ.lift + 2 by omega) ℓ (P e (d + 1))
  omega

/-! ## Output lengths -/

lemma hasLen_emit (a : Xp) : HasLen τs (emit a) (P 0 0) :=
  fun _ => ⟨1, fun _ _ _ _ _ => by simp [out, Ty.bnd]⟩

lemma hasLen_when (c : Xp) {g : Gn} {τ : Ty} (hg : HasLen τs g τ) : HasLen τs (when c g) τ := by
  intro K₀
  obtain ⟨K, hK⟩ := hg K₀
  refine ⟨K, fun ℓ x ρ hx hA => ?_⟩
  rw [out_when]
  split_ifs
  · exact hK ℓ x ρ hx hA
  · exact Nat.zero_le _

lemma hasLen_loop {lim : Xp} {g : Gn} {e₀ d₀ e d : ℕ} (hl : HasTy τs lim (P e₀ d₀))
    (hg : HasLen (τs ++ [P e₀ d₀, P e₀ d₀]) g (P e d)) :
    HasLen τs (loop lim g) (P (e₀ + e) (d₀ + d)) := by
  intro K₀
  obtain ⟨Kl, hKl⟩ := hl K₀
  obtain ⟨Kg, hKg⟩ := hg (K₀ + Kl)
  refine ⟨Kl * Kg, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨l1, -, -⟩ := hKl ℓ ρ hA
  have hb : ∀ k < lim.eval ρ, Ag (K₀ + Kl) ℓ (τs ++ [P e₀ d₀, P e₀ d₀]) (ρ ++ [lim.eval ρ, k]) :=
    fun k hk => (hA.mono (by omega)).push2 (le_trans l1 (Ty.bnd_mono (by omega) ℓ _))
      (le_trans (le_trans hk.le l1) (Ty.bnd_mono (by omega) ℓ _))
  simp only [out]
  have h1 := length_flatMap_range_le (lim.eval ρ) (fun k => g.out x (ρ ++ [lim.eval ρ, k]))
    (fun _ => (P e d).bnd Kg ℓ) fun k hk => hKg ℓ x _ hx (hb k hk)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h1
  rw [← Ty.bnd_mul]
  exact le_trans h1 (Nat.mul_le_mul_right _ l1)

/-! ## Derived generators -/

lemma hasCost_seqL {e d : ℕ} : ∀ {gs : List Gn}, (∀ g ∈ gs, HasCost τs g e d) →
    HasCost τs (seqL gs) e d
  | [], _ => hasCost_skip.mono (Nat.zero_le _) (Nat.zero_le _)
  | g :: gs, h => hasCost_seq (h g (by simp)) (hasCost_seqL fun g' hg' => h g' (by simp [hg']))

lemma hasCost_when {c : Xp} {τ : Ty} {g : Gn} {e d : ℕ} (hc : HasTy τs c τ)
    (hg : HasCost τs g e d) : HasCost τs (when c g) e d :=
  hasCost_ite hc hg (hasCost_skip.mono (Nat.zero_le _) (Nat.zero_le _))

/-- Classes of a list of expressions, each typed in the context extended by the previous
ones. -/
def TyL : List Ty → List Xp → List Ty → Prop
  | _, [], [] => True
  | τs, a :: as, τ :: ts => HasTy τs a τ ∧ TyL (τs ++ [τ]) as ts
  | _, _, _ => False

lemma hasCost_bindL {g : Gn} {e d : ℕ} : ∀ {τs : List Ty} {as : List Xp} {ts : List Ty},
    TyL τs as ts → HasCost (τs ++ ts) g e d → HasCost τs (bindL as g) e d
  | _, [], [], _, hg => by simpa [bindL] using hg
  | τs, a :: as, τ :: ts, h, hg =>
    hasCost_bind h.1 (hasCost_bindL h.2 (by simpa using hg))
  | _, [], _ :: _, h, _ => h.elim
  | _, _ :: _, [], h, _ => h.elim

/-- `TyL` for expressions reading only the base context. -/
lemma tyL_of_forall₂ : ∀ {τs : List Ty} {as : List Xp} {ts : List Ty},
    List.Forall₂ (fun a τ => HasTy τs a τ ∧ a.Bnd τs.length) as ts → ∀ us : List Ty,
      TyL (τs ++ us) as ts
  | _, [], [], _, _ => trivial
  | τs, a :: as, τ :: ts, List.Forall₂.cons h hr, us =>
    ⟨h.1.weaken h.2 us, by
      have := tyL_of_forall₂ hr (us ++ [τ])
      simpa using this⟩

lemma getD_append_len (τs us : List Ty) (τ : Ty) (j : ℕ) :
    (τs ++ τ :: us).getD (τs.length + j) (P 0 0) = (τ :: us).getD j (P 0 0) := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1; omega

lemma hasCost_bindSub {n : ℕ} {a b : Xp} {τb : Ty} {g : Gn} {e₀ d₀ e d : ℕ}
    (hn : τs.length = n) (ha : HasTy τs a (P e₀ d₀)) (hab : a.Bnd n) (hb : HasTy τs b τb)
    (hbb : b.Bnd n) (hg : HasCost (τs ++ [P e₀ d₀]) g e d) :
    HasCost τs (bindSub n a b g) (max e₀ e) (max d₀ d) := by
  have ha' := ha.weaken' hn hab [P 0 0]
  have hb' := hb.weaken' hn hbb ([P 0 0] ++ [P e₀ d₀, P e₀ d₀])
  have hv : HasTy ((τs ++ [P 0 0]) ++ [P e₀ d₀, P e₀ d₀]) (var (n + 2)) (P e₀ d₀) := by
    refine hasTy_var' ?_
    have := getD_append_len τs [P e₀ d₀, P e₀ d₀] (P 0 0) 2
    simpa [← hn] using this
  have hbody : HasCost ((τs ++ [P 0 0]) ++ [P e₀ d₀, P e₀ d₀])
      (when (Xp.lt b (Xp.add (Xp.var (n + 2)) (Xp.const 1))) (emit (Xp.const 0))) 0 0 := by
    refine hasCost_when (hasTy_lt (by simpa using hb') (hasTy_addBig hv (hasTy_const 1)))
      (hasCost_emit (hasTy_const 0))
  have hloop := hasCost_loop ha' hbody
  have hlen : HasLen (τs ++ [P 0 0]) (loop a (when (Xp.lt b (Xp.add (Xp.var (n + 2))
      (Xp.const 1))) (emit (Xp.const 0)))) (P e₀ d₀) := by
    have := hasLen_loop ha' (hasLen_when (Xp.lt b (Xp.add (Xp.var (n + 2)) (Xp.const 1)))
      (hasLen_emit (τs := (τs ++ [P 0 0]) ++
      [P e₀ d₀, P e₀ d₀]) (Xp.const 0)))
    simpa using this
  refine hasCost_count (hloop.mono (by omega) (by omega)) hlen
    (hg.mono (le_max_right _ _) (le_max_right _ _))

end Gn

end Lax119563Proofs.Reduction
