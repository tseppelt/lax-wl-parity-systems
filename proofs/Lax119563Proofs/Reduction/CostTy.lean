import Lax119563Proofs.Reduction.FitsBasic

/-!
# Growth classes of values and typed expressions

To bound the values and the costs of generators uniformly in the input, every value is
assigned a *growth class* `Ty` with respect to a pair of scales `ℓ = (l, L)` (`Sc`, `l ≤ L`; a
scale is coerced to `L`): `2^l` bounds the input length, `L` the linear quantities (for the
quasi-linear analysis both are `≈ log₂ |x|`, `Sc.diag`):
* `P e d`: values `≤ K · 2^(e l) · (L + 1)^d` (`P 0 1`: linear, `P 0 d`: polynomial in `L`,
  `P 1 0`: linear in `2^l`);
* `big`: values `≤ 2^(K (L + 1))`, where `K` is a constant depending on the syntax only.

`Ag K ℓ τs ρ`: the stack `ρ` agrees with the classes `τs` (with constant `K`).
`Xp.HasTy τs e τ`: for every constant of the stack there is a constant `K` such that the value
of `e` is in class `τ`, `e` fits below `2^(K (L + 1))` and costs at most `K (L + 1)`. The
loop-based operations `mulB, shl, shr, xorM` need a linear (`P 0 1`) iteration count.

Typing rules: `Xp.hasTy_var/const/add/addBig/lt/half/odd/mulB/mulBBig/shl/shr/xorM`, with
`HasTy.le` (subsumption), `HasTy.ctx` (smaller context classes) and `HasTy.weaken`
(appending levels the expression does not read).
-/

namespace Lax119563Proofs.Reduction

/-- A pair of scales `l ≤ L`: `2^l` bounds the input length and the values of the classes
`P 1 _`, `L` the linear quantities. A scale is coerced to `L`. -/
structure Sc where
  /-- The exponential scale. -/
  l : ℕ
  /-- The linear scale. -/
  L : ℕ
  le : l ≤ L

instance : CoeOut Sc ℕ := ⟨Sc.L⟩

/-- The scale `(ℓ, ℓ)`. -/
def Sc.diag (ℓ : ℕ) : Sc := ⟨ℓ, ℓ, le_rfl⟩

/-- Growth classes. -/
inductive Ty
  /-- At most `K · 2^(e ℓ) · ((ℓ : ℕ) + 1)^d`. -/
  | P (e d : ℕ)
  /-- At most `2^(K ((ℓ : ℕ) + 1))`. -/
  | big

namespace Ty

/-- The bound of a class with constant `K` at scale `ℓ`. -/
def bnd : Ty → ℕ → Sc → ℕ
  | P e d, K, ℓ => K * 2 ^ (e * ℓ.l) * ((ℓ : ℕ) + 1) ^ d
  | big, K, ℓ => 2 ^ (K * ((ℓ : ℕ) + 1))

/-- Inclusion of classes. -/
def Le : Ty → Ty → Prop
  | P e d, P e' d' => e ≤ e' ∧ d ≤ d'
  | _, big => True
  | big, P _ _ => False

/-- The increase of the constant when passing to a larger class. -/
def lift : Ty → ℕ
  | P e d => e + d
  | big => 0

lemma Le.refl : ∀ τ : Ty, Le τ τ
  | P _ _ => ⟨le_rfl, le_rfl⟩
  | big => trivial

lemma le_big (τ : Ty) : Le τ big := by cases τ <;> trivial

lemma bnd_mono {K K' : ℕ} (h : K ≤ K') (ℓ : Sc) : ∀ τ : Ty, τ.bnd K ℓ ≤ τ.bnd K' ℓ
  | P e d => by
    simp only [bnd]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)
  | big => Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h)

lemma succ_le_two_pow (ℓ : ℕ) : ℓ + 1 ≤ 2 ^ ℓ := Nat.lt_two_pow_self

lemma pow_succ_le (ℓ d : ℕ) : ((ℓ : ℕ) + 1) ^ d ≤ 2 ^ (d * ℓ) := by
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (succ_le_two_pow ℓ) d

lemma bnd_le_big (K : ℕ) (ℓ : Sc) : ∀ τ : Ty, τ.bnd K ℓ ≤ 2 ^ ((K + τ.lift) * ((ℓ : ℕ) + 1))
  | P e d => by
    simp only [bnd, lift]
    have h1 : K ≤ 2 ^ K := Nat.lt_two_pow_self.le
    have h3 := pow_succ_le ℓ d
    have h2 : 2 ^ (e * ℓ.l) ≤ 2 ^ (e * ℓ) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ ℓ.le)
    calc K * 2 ^ (e * ℓ.l) * (↑ℓ + 1) ^ d ≤ 2 ^ K * 2 ^ (e * ℓ) * 2 ^ (d * ℓ) :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      _ = 2 ^ (K + e * ℓ + d * ℓ) := by rw [pow_add, pow_add]
      _ ≤ 2 ^ ((K + (e + d)) * ((ℓ : ℕ) + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  | big => by simp [bnd, lift]

lemma bnd_lt_big (K : ℕ) (ℓ : Sc) (τ : Ty) : τ.bnd K ℓ < 2 ^ ((K + τ.lift + 1) * ((ℓ : ℕ) + 1)) :=
  lt_of_le_of_lt (bnd_le_big K ℓ τ) (Nat.pow_lt_pow_right (by norm_num) (by nlinarith))

lemma bnd_le_of_le {τ τ' : Ty} (h : Le τ τ') (K : ℕ) (ℓ : Sc) : τ.bnd K ℓ ≤ τ'.bnd (K + τ.lift) ℓ := by
  cases τ with
  | P e d =>
    cases τ' with
    | P e' d' =>
      simp only [bnd, lift]
      have h1 : 2 ^ (e * ℓ.l) ≤ 2 ^ (e' * ℓ.l) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h.1)
      have h2 : ((ℓ : ℕ) + 1) ^ d ≤ ((ℓ : ℕ) + 1) ^ d' := Nat.pow_le_pow_right (by omega) h.2
      exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) h1) h2
    | big => exact bnd_le_big K ℓ _
  | big =>
    cases τ' with
    | P _ _ => exact h.elim
    | big => simp [bnd, lift]

lemma one_le_bnd {K : ℕ} (hK : 1 ≤ K) (ℓ : Sc) : ∀ τ : Ty, 1 ≤ τ.bnd K ℓ
  | P e d => by
    simp only [bnd]
    have h1 : 1 ≤ 2 ^ (e * ℓ.l) := Nat.one_le_two_pow
    have h2 : 1 ≤ ((ℓ : ℕ) + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    exact Nat.mul_le_mul (Nat.mul_le_mul hK h1) h2
  | big => Nat.one_le_two_pow

lemma bnd_P00 (K : ℕ) (ℓ : Sc) : (P 0 0).bnd K ℓ = K := by simp [bnd]

lemma bnd_mul (e d e' d' K K' : ℕ) (ℓ : Sc) :
    (P e d).bnd K ℓ * (P e' d').bnd K' ℓ = (P (e + e') (d + d')).bnd (K * K') ℓ := by
  simp only [bnd, Nat.add_mul, pow_add]; ring

lemma bnd_add (e d K K' : ℕ) (ℓ : Sc) :
    (P e d).bnd K ℓ + (P e d).bnd K' ℓ = (P e d).bnd (K + K') ℓ := by
  simp only [bnd]; ring

end Ty

open Ty

/-- The stack `ρ` agrees with the classes `τs`, with constant `K` at scale `ℓ`. -/
def Ag (K : ℕ) (ℓ : Sc) (τs : List Ty) (ρ : List ℕ) : Prop :=
  List.Forall₂ (fun v τ => v ≤ τ.bnd K ℓ) ρ τs

/-- Pointwise inclusion of classes. -/
def TysLe (τs τs' : List Ty) : Prop := List.Forall₂ Ty.Le τs τs'

/-- The sum of the lifts. -/
def liftL (τs : List Ty) : ℕ := (τs.map Ty.lift).sum

namespace Ag

variable {K K' : ℕ} {ℓ : Sc} {τs : List Ty} {ρ : List ℕ}

lemma mono (h : K ≤ K') (hA : Ag K ℓ τs ρ) : Ag K' ℓ τs ρ :=
  hA.imp fun _ τ hv => le_trans hv (Ty.bnd_mono h ℓ τ)

lemma length_eq (hA : Ag K ℓ τs ρ) : ρ.length = τs.length := List.Forall₂.length_eq hA

lemma getD (hA : Ag K ℓ τs ρ) (i : ℕ) : ρ.getD i 0 ≤ (τs.getD i (P 0 0)).bnd K ℓ := by
  induction hA generalizing i with
  | nil => simp
  | cons h _ ih =>
    cases i with
    | zero => simpa using h
    | succ i => simpa using ih i

lemma append {τs' : List Ty} {ρ' : List ℕ} (hA : Ag K ℓ τs ρ) (hA' : Ag K ℓ τs' ρ') :
    Ag K ℓ (τs ++ τs') (ρ ++ ρ') := List.rel_append hA hA'

lemma push {τ : Ty} {v : ℕ} (hA : Ag K ℓ τs ρ) (hv : v ≤ τ.bnd K ℓ) :
    Ag K ℓ (τs ++ [τ]) (ρ ++ [v]) := hA.append (List.Forall₂.cons hv List.Forall₂.nil)

lemma push2 {τ τ' : Ty} {v v' : ℕ} (hA : Ag K ℓ τs ρ) (hv : v ≤ τ.bnd K ℓ)
    (hv' : v' ≤ τ'.bnd K ℓ) : Ag K ℓ (τs ++ [τ, τ']) (ρ ++ [v, v']) :=
  hA.append (List.Forall₂.cons hv (List.Forall₂.cons hv' List.Forall₂.nil))

lemma push3 {τ τ' τ'' : Ty} {v v' v'' : ℕ} (hA : Ag K ℓ τs ρ) (hv : v ≤ τ.bnd K ℓ)
    (hv' : v' ≤ τ'.bnd K ℓ) (hv'' : v'' ≤ τ''.bnd K ℓ) :
    Ag K ℓ (τs ++ [τ, τ', τ'']) (ρ ++ [v, v', v'']) :=
  hA.append (List.Forall₂.cons hv (List.Forall₂.cons hv' (List.Forall₂.cons hv''
    List.Forall₂.nil)))

lemma split {τs' : List Ty} {ρ : List ℕ} (hA : Ag K ℓ (τs ++ τs') ρ) :
    Ag K ℓ τs (ρ.take τs.length) ∧ ρ = ρ.take τs.length ++ ρ.drop τs.length := by
  refine ⟨?_, (List.take_append_drop _ _).symm⟩
  induction τs generalizing ρ with
  | nil => exact List.Forall₂.nil
  | cons τ τs ih =>
    cases hA with
    | cons hv hr => exact List.Forall₂.cons hv (ih hr)

lemma of_le {τs' : List Ty} (h : TysLe τs τs') (hA : Ag K ℓ τs ρ) :
    Ag (K + liftL τs) ℓ τs' ρ := by
  induction hA generalizing τs' with
  | nil => cases h; exact List.Forall₂.nil
  | @cons v τ ρ τs hv _ ih =>
    cases h with
    | cons hτ hr =>
      refine List.Forall₂.cons ?_ ((ih hr).mono ?_)
      · refine le_trans hv (le_trans (Ty.bnd_le_of_le hτ K ℓ) (Ty.bnd_mono ?_ ℓ _))
        simp [liftL]
      · simp [liftL]

end Ag

lemma TysLe.refl : ∀ τs : List Ty, TysLe τs τs
  | [] => List.Forall₂.nil
  | τ :: τs => List.Forall₂.cons (Ty.Le.refl τ) (TysLe.refl τs)

lemma TysLe.append {τs τs' us us' : List Ty} (h : TysLe τs τs') (h' : TysLe us us') :
    TysLe (τs ++ us) (τs' ++ us') := List.rel_append h h'

/-! ## Expressions that ignore appended levels -/

namespace Xp

lemma fits_append {n : ℕ} {ρ : List ℕ} (hρ : ρ.length = n) (l : List ℕ) {B : ℕ} {e : Xp}
    (he : e.Bnd n) : e.Fits B (ρ ++ l) ↔ e.Fits B ρ := by
  induction e with
  | var i =>
    simp only [Fits]
    rw [List.getD_append _ _ _ _ (by simp only [Bnd] at he; omega)]
  | const _ => rfl
  | add a b ia ib =>
    simp only [Fits, ia he.1, ib he.2, eval_append hρ l he.1, eval_append hρ l he.2]
  | lt a b ia ib => simp only [Fits, ia he.1, ib he.2]
  | half a ia => exact ia he
  | odd a ia => exact ia he
  | mulB a b k ia ib ik =>
    simp only [Fits, ia he.1, ib he.2.1, ik he.2.2, eval_append hρ l he.1,
      eval_append hρ l he.2.2]
  | shl a k ia ik =>
    simp only [Fits, ia he.1, ik he.2, eval_append hρ l he.1, eval_append hρ l he.2]
  | shr a k ia ik => simp only [Fits, ia he.1, ik he.2]
  | xorM a b k ia ib ik =>
    simp only [Fits, ia he.1, ib he.2.1, ik he.2.2, eval_append hρ l he.2.2]

lemma cost_append {n : ℕ} {ρ : List ℕ} (hρ : ρ.length = n) (l : List ℕ) {e : Xp}
    (he : e.Bnd n) : e.cost (ρ ++ l) = e.cost ρ := by
  induction e with
  | var _ => rfl
  | const _ => rfl
  | add a b ia ib => simp only [cost, ia he.1, ib he.2]
  | lt a b ia ib => simp only [cost, ia he.1, ib he.2]
  | half a ia => simp only [cost, ia he]
  | odd a ia => simp only [cost, ia he]
  | mulB a b k ia ib ik =>
    simp only [cost, ia he.1, ib he.2.1, ik he.2.2, eval_append hρ l he.2.2]
  | shl a k ia ik => simp only [cost, ia he.1, ik he.2, eval_append hρ l he.2]
  | shr a k ia ik => simp only [cost, ia he.1, ik he.2, eval_append hρ l he.2]
  | xorM a b k ia ib ik =>
    simp only [cost, ia he.1, ib he.2.1, ik he.2.2, eval_append hρ l he.2.2]

/-! ## Typed expressions -/

/-- `e` has values in class `τ`, fits below `2^(K (ℓ+1))` and costs at most `K ((ℓ : ℕ) + 1)`. -/
def HasTy (τs : List Ty) (e : Xp) (τ : Ty) : Prop :=
  ∀ K₀, ∃ K, ∀ (ℓ : Sc) ρ, Ag K₀ ℓ τs ρ →
    e.eval ρ ≤ τ.bnd K ℓ ∧ e.Fits (2 ^ (K * ((ℓ : ℕ) + 1))) ρ ∧ e.cost ρ ≤ K * ((ℓ : ℕ) + 1)

variable {τs : List Ty}

lemma two_pow_mono {K K' ℓ : ℕ} (h : K ≤ K') : 2 ^ (K * ((ℓ : ℕ) + 1)) ≤ 2 ^ (K' * ((ℓ : ℕ) + 1)) :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h)

lemma HasTy.le {e : Xp} {τ τ' : Ty} (h : HasTy τs e τ) (hτ : Ty.Le τ τ') : HasTy τs e τ' := by
  intro K₀
  obtain ⟨K, hK⟩ := h K₀
  refine ⟨K + τ.lift, fun ℓ ρ hA => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hK ℓ ρ hA
  exact ⟨le_trans h1 (Ty.bnd_le_of_le hτ K ℓ), Fits.mono (two_pow_mono (by omega)) _ h2,
    le_trans h3 (Nat.mul_le_mul_right _ (by omega))⟩

lemma HasTy.big {e : Xp} {τ : Ty} (h : HasTy τs e τ) : HasTy τs e .big := h.le (Ty.le_big τ)

lemma HasTy.weaken {e : Xp} {τ : Ty} (h : HasTy τs e τ) (hb : e.Bnd τs.length)
    (ts : List Ty) : HasTy (τs ++ ts) e τ := by
  intro K₀
  obtain ⟨K, hK⟩ := h K₀
  refine ⟨K, fun ℓ ρ hA => ?_⟩
  obtain ⟨hA1, hρ⟩ := hA.split
  have hl : (ρ.take τs.length).length = τs.length := hA1.length_eq
  rw [hρ, eval_append hl _ hb, fits_append hl _ hb, cost_append hl _ hb]
  exact hK ℓ _ hA1

lemma HasTy.weaken' {n : ℕ} {e : Xp} {τ : Ty} (h : HasTy τs e τ) (hn : τs.length = n)
    (hb : e.Bnd n) (ts : List Ty) : HasTy (τs ++ ts) e τ := h.weaken (hn ▸ hb) ts

lemma hasTy_var (i : ℕ) : HasTy τs (var i) (τs.getD i (P 0 0)) := by
  intro K₀
  refine ⟨K₀ + (τs.getD i (P 0 0)).lift + 1, fun ℓ ρ hA => ?_⟩
  have hv := hA.getD i
  refine ⟨le_trans hv (Ty.bnd_mono (by omega) ℓ _), ?_, ?_⟩
  · exact lt_of_le_of_lt hv (Ty.bnd_lt_big K₀ ℓ _)
  · simp only [cost]; nlinarith

lemma hasTy_var' {i : ℕ} {τ : Ty} (h : τs.getD i (P 0 0) = τ) : HasTy τs (var i) τ :=
  h ▸ hasTy_var i

lemma hasTy_const (c : ℕ) : HasTy τs (const c) (P 0 0) := by
  intro _
  refine ⟨c + 1, fun ℓ ρ _ => ⟨by simp [Ty.bnd, eval], ?_, by simp only [cost]; nlinarith⟩⟩
  show c < 2 ^ ((c + 1) * ((ℓ : ℕ) + 1))
  calc c < 2 ^ c := Nat.lt_two_pow_self
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

lemma two_pow_add_le (A B K ℓ : ℕ) (hA : A ≤ 2 ^ (K * ((ℓ : ℕ) + 1))) (hB : B ≤ 2 ^ (K * ((ℓ : ℕ) + 1))) :
    A + B < 2 ^ ((K + 2) * ((ℓ : ℕ) + 1)) := by
  have : 2 ^ (K * ((ℓ : ℕ) + 1)) * 2 ^ 2 ≤ 2 ^ ((K + 2) * ((ℓ : ℕ) + 1)) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have : 0 < 2 ^ (K * ((ℓ : ℕ) + 1)) := by positivity
  by_contra hc
  omega

lemma hasTy_add {a b : Xp} {e d : ℕ} (ha : HasTy τs a (P e d)) (hb : HasTy τs b (P e d)) :
    HasTy τs (add a b) (P e d) := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kb, hKb⟩ := hb K₀
  refine ⟨Ka + Kb + e + d + 2, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, b2, b3⟩ := hKb ℓ ρ hA
  have hs : a.eval ρ + b.eval ρ ≤ (P e d).bnd (Ka + Kb) ℓ := by
    rw [← Ty.bnd_add]; omega
  refine ⟨?_, ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ b2,
    ?_⟩, ?_⟩
  · exact le_trans hs (Ty.bnd_mono (by omega) ℓ _)
  · refine lt_of_le_of_lt hs (lt_of_lt_of_le (Ty.bnd_lt_big _ ℓ _) (two_pow_mono ?_))
    simp [Ty.lift]; omega
  · simp only [cost]; nlinarith

lemma hasTy_addBig {a b : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb) :
    HasTy τs (add a b) .big := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha.big K₀
  obtain ⟨Kb, hKb⟩ := hb.big K₀
  refine ⟨Ka + Kb + 3, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, b2, b3⟩ := hKb ℓ ρ hA
  have a1' : a.eval ρ ≤ 2 ^ ((Ka + Kb) * ((ℓ : ℕ) + 1)) := le_trans a1 (two_pow_mono (by omega))
  have b1' : b.eval ρ ≤ 2 ^ ((Ka + Kb) * ((ℓ : ℕ) + 1)) := le_trans b1 (two_pow_mono (by omega))
  have hs := two_pow_add_le _ _ _ ℓ a1' b1'
  refine ⟨le_trans hs.le (two_pow_mono (by omega)), ⟨Fits.mono (two_pow_mono (by omega)) _ a2,
    Fits.mono (two_pow_mono (by omega)) _ b2, lt_of_lt_of_le hs (two_pow_mono (by omega))⟩, ?_⟩
  simp only [cost]; nlinarith

lemma hasTy_lt {a b : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb) :
    HasTy τs (lt a b) (P 0 0) := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kb, hKb⟩ := hb K₀
  refine ⟨Ka + Kb + 2, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, b2, b3⟩ := hKb ℓ ρ hA
  refine ⟨?_, ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ b2⟩,
    ?_⟩
  · rw [Ty.bnd_P00]; simp only [eval]; split_ifs <;> omega
  · simp only [cost]; nlinarith

lemma hasTy_odd {a : Xp} {τ : Ty} (ha : HasTy τs a τ) : HasTy τs (odd a) (P 0 0) := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  refine ⟨Ka + 1, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  refine ⟨?_, Fits.mono (two_pow_mono (by omega)) a a2, ?_⟩
  · rw [Ty.bnd_P00]; simp only [eval]; have := Nat.mod_lt (a.eval ρ) (show 2 > 0 by omega); omega
  · simp only [cost]; nlinarith

/-- A linear iteration count: `2^k` is `big`. -/
lemma two_pow_lin {k K : ℕ} {ℓ : Sc} (hk : k ≤ (P 0 1).bnd K ℓ) : 2 ^ k ≤ 2 ^ (K * ((ℓ : ℕ) + 1)) :=
  Nat.pow_le_pow_right (by norm_num) (by simpa [Ty.bnd] using hk)

lemma lin_le {k K : ℕ} {ℓ : Sc} (hk : k ≤ (P 0 1).bnd K ℓ) : k ≤ K * ((ℓ : ℕ) + 1) := by
  simpa [Ty.bnd] using hk

lemma mul_two_pow_lt {a k Ka Kk : ℕ} {ℓ : Sc} {τ : Ty} (ha : a ≤ τ.bnd Ka ℓ)
    (hk : k ≤ (P 0 1).bnd Kk ℓ) : a * 2 ^ k < 2 ^ ((Ka + τ.lift + Kk + 1) * ((ℓ : ℕ) + 1)) := by
  have h1 := le_trans ha (Ty.bnd_le_big Ka ℓ τ)
  have h2 := two_pow_lin hk
  calc a * 2 ^ k ≤ 2 ^ ((Ka + τ.lift) * ((ℓ : ℕ) + 1)) * 2 ^ (Kk * ((ℓ : ℕ) + 1)) := Nat.mul_le_mul h1 h2
    _ = 2 ^ ((Ka + τ.lift + Kk) * ((ℓ : ℕ) + 1)) := by rw [← pow_add]; ring_nf
    _ < _ := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)

lemma hasTy_mulB {a b k : Xp} {e d e' d' : ℕ} (ha : HasTy τs a (P e d))
    (hb : HasTy τs b (P e' d')) (hk : HasTy τs k (P 0 1)) :
    HasTy τs (mulB a b k) (P (e + e') (d + d')) := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kb, hKb⟩ := hb K₀
  obtain ⟨Kk, hKk⟩ := hk K₀
  refine ⟨Ka * Kb + Ka + Kb + 2 * Kk + e + d + 3, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, b2, b3⟩ := hKb ℓ ρ hA
  obtain ⟨k1, k2, k3⟩ := hKk ℓ ρ hA
  refine ⟨?_, ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ b2,
    Fits.mono (two_pow_mono (by omega)) _ k2, ?_⟩, ?_⟩
  · simp only [eval]
    calc a.eval ρ * (b.eval ρ % 2 ^ k.eval ρ) ≤ (P e d).bnd Ka ℓ * (P e' d').bnd Kb ℓ :=
          Nat.mul_le_mul a1 (le_trans (Nat.mod_le _ _) b1)
      _ = _ := Ty.bnd_mul ..
      _ ≤ _ := Ty.bnd_mono (by nlinarith) ℓ _
  · exact lt_of_lt_of_le (mul_two_pow_lt a1 k1) (two_pow_mono (by simp [Ty.lift]; omega))
  · have := lin_le k1
    have key : (Ka + Kb + 2 * Kk + 2) * ((ℓ : ℕ) + 1) ≤
        (Ka * Kb + Ka + Kb + 2 * Kk + e + d + 3) * ((ℓ : ℕ) + 1) := Nat.mul_le_mul_right _ (by omega)
    simp only [cost]; nlinarith

lemma hasTy_mulBBig {a b k : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb)
    (hk : HasTy τs k (P 0 1)) : HasTy τs (mulB a b k) .big := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kb, hKb⟩ := hb K₀
  obtain ⟨Kk, hKk⟩ := hk K₀
  refine ⟨Ka + τa.lift + Kb + 2 * Kk + 3, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, b2, b3⟩ := hKb ℓ ρ hA
  obtain ⟨k1, k2, k3⟩ := hKk ℓ ρ hA
  have hm := mul_two_pow_lt a1 k1
  have hv : (mulB a b k).eval ρ ≤ a.eval ρ * 2 ^ k.eval ρ := by
    simp only [eval]
    exact Nat.mul_le_mul_left _ (Nat.mod_lt _ (by positivity)).le
  refine ⟨le_trans hv (le_trans hm.le (two_pow_mono (by omega))),
    ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ b2,
    Fits.mono (two_pow_mono (by omega)) _ k2, lt_of_lt_of_le hm (two_pow_mono (by omega))⟩, ?_⟩
  have := lin_le k1
  have key : (Ka + Kb + 2 * Kk + 2) * ((ℓ : ℕ) + 1) ≤
      (Ka + τa.lift + Kb + 2 * Kk + 3) * ((ℓ : ℕ) + 1) := Nat.mul_le_mul_right _ (by omega)
  simp only [cost]; nlinarith

lemma hasTy_shl {a k : Xp} {τ : Ty} (ha : HasTy τs a τ) (hk : HasTy τs k (P 0 1)) :
    HasTy τs (shl a k) .big := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kk, hKk⟩ := hk K₀
  refine ⟨Ka + τ.lift + 2 * Kk + 3, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨k1, k2, k3⟩ := hKk ℓ ρ hA
  have hm := mul_two_pow_lt a1 k1
  refine ⟨le_trans hm.le (two_pow_mono (by omega)),
    ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ k2,
      lt_of_lt_of_le hm (two_pow_mono (by omega))⟩, ?_⟩
  have := lin_le k1
  have key : (Ka + 2 * Kk + 2) * ((ℓ : ℕ) + 1) ≤
      (Ka + τ.lift + 2 * Kk + 3) * ((ℓ : ℕ) + 1) := Nat.mul_le_mul_right _ (by omega)
  simp only [cost]; nlinarith

lemma hasTy_shr {a k : Xp} {τ : Ty} (ha : HasTy τs a τ) (hk : HasTy τs k (P 0 1)) :
    HasTy τs (shr a k) τ := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kk, hKk⟩ := hk K₀
  refine ⟨Ka + 2 * Kk + 3, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨k1, k2, k3⟩ := hKk ℓ ρ hA
  refine ⟨?_, ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ k2⟩,
    ?_⟩
  · simp only [eval]
    exact le_trans (Nat.div_le_self _ _) (le_trans a1 (Ty.bnd_mono (by omega) ℓ _))
  · have := lin_le k1
    have key : (Ka + 2 * Kk + 2) * ((ℓ : ℕ) + 1) ≤
        (Ka + 2 * Kk + 3) * ((ℓ : ℕ) + 1) := Nat.mul_le_mul_right _ (by omega)
    simp only [cost]; nlinarith

lemma hasTy_xorM {a b k : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb)
    (hk : HasTy τs k (P 0 1)) : HasTy τs (xorM a b k) .big := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kb, hKb⟩ := hb K₀
  obtain ⟨Kk, hKk⟩ := hk K₀
  refine ⟨Ka + Kb + 2 * Kk + 4, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, b2, b3⟩ := hKb ℓ ρ hA
  obtain ⟨k1, k2, k3⟩ := hKk ℓ ρ hA
  have h2 := two_pow_lin k1
  have h2' : 2 ^ k.eval ρ < 2 ^ ((Ka + Kb + 2 * Kk + 4) * ((ℓ : ℕ) + 1)) :=
    lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by norm_num) (by nlinarith))
  refine ⟨?_, ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ b2,
    Fits.mono (two_pow_mono (by omega)) _ k2, h2'⟩, ?_⟩
  · simp only [eval, Ty.bnd]
    exact le_trans (Nat.mod_lt _ (by positivity)).le h2'.le
  · have := lin_le k1
    have key : (Ka + Kb + 2 * Kk + 3) * ((ℓ : ℕ) + 1) ≤
        (Ka + Kb + 2 * Kk + 4) * ((ℓ : ℕ) + 1) := Nat.mul_le_mul_right _ (by omega)
    simp only [cost]; nlinarith

/-! ### Derived expressions -/

lemma hasTy_eq {a b : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb) :
    HasTy τs (Xp.eq a b) (P 0 0) :=
  hasTy_lt (hasTy_add (hasTy_lt ha hb) (hasTy_lt hb ha)) (hasTy_const 1)

lemma hasTy_not {a : Xp} {τ : Ty} (ha : HasTy τs a τ) : HasTy τs (Xp.not a) (P 0 0) :=
  hasTy_lt ha (hasTy_const 1)

lemma hasTy_and {a b : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb) :
    HasTy τs (Xp.and a b) (P 0 0) := hasTy_lt (hasTy_const 1) (hasTy_addBig ha hb)

lemma hasTy_or {a b : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb) :
    HasTy τs (Xp.or a b) (P 0 0) := hasTy_lt (hasTy_const 0) (hasTy_addBig ha hb)

lemma hasTy_mulC {a : Xp} {e d : ℕ} (ha : HasTy τs a (P e d)) :
    ∀ c, HasTy τs (mulC c a) (P e d)
  | 0 => (hasTy_const 0).le ⟨Nat.zero_le _, Nat.zero_le _⟩
  | c + 1 => hasTy_add (hasTy_mulC ha c) ha

lemma hasTy_mul {a b : Xp} {e d d' : ℕ} (ha : HasTy τs a (P e d)) (hb : HasTy τs b (P 0 d'))
    (hb1 : HasTy τs b (P 0 1)) : HasTy τs (mul a b) (P e (d + d')) := by
  have := hasTy_mulB ha hb hb1
  simpa [mul] using this

lemma hasTy_pow2 {k : Xp} (hk : HasTy τs k (P 0 1)) : HasTy τs (pow2 k) .big :=
  hasTy_shl (hasTy_const 1) hk

end Xp

end Lax119563Proofs.Reduction
