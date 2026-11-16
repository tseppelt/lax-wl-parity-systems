import Lax119563Proofs.RowSpace.Construction

/-!
# Descriptions and translations

A *description* consists of total seeds `z_v` and masks `x_{e,h}`. It translates every class
(`rshift`); the translation `tr D` maps the vertices of `G₀` to those of `G₁` as soon as the
seeds of initialized locations are the initial seeds and the masks lie in the row spaces, and
it preserves adjacency between two classes as soon as the mask-sum condition holds at the
coordinates of the update classes of the last stage involved.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ}

variable (I : ImplicitParitySystem k ℓ) in
/-- A description: total seeds and masks. -/
structure RDesc where
  /-- The seed of each location. -/
  z : Fin I.numLocations → Vec k ℓ
  /-- The mask of stage `h` of schema `e`. -/
  x : Fin I.schemas.length → ℕ → Vec k ℓ

variable {I : ImplicitParitySystem k ℓ}

/-- The initial track bit `t_{e,0}(c)`. -/
def rt0 (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : ZMod 2 :=
  D.z (locU (sch I e)) ((permU (sch I e)).apply c) +
    if isTern (sch I e) then D.z (locV (sch I e)) ((permV (sch I e)).apply c) else 0

/-- The sum of the masks of stages `1, …, h` at `c`. -/
def msum (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) (h : ℕ) : ZMod 2 :=
  ∑ i ∈ Finset.range h, D.x e (i + 1) c

/-- The track bit `t_{e,h}(c)`. -/
def TT (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) (h : ℕ) : ZMod 2 :=
  rt0 D e c + msum D e c h

/-- The translation of each class. -/
def rshift (D : RDesc I) : ICls I → RLab k ℓ
  | .coord v c => (D.z v c, 0, 0)
  | .sum e c => (rt0 D e c, 0, 0)
  | .junc e c => (D.z (locU (sch I e)) ((permU (sch I e)).apply c),
      D.z (locV (sch I e)) ((permV (sch I e)).apply c), 0)
  | .track e h c => (TT D e c h, 0, 0)
  | .upd e h c => (TT D e c (h - 1), TT D e c h, 0)
  | .coef e h => (0, 0, D.x e h)
  | .link .. => 0

/-- The translation of a vertex. -/
def tr (D : RDesc I) (x : ICls I × RLab k ℓ) : ICls I × RLab k ℓ := (x.1, x.2 + rshift D x.1)

@[simp] lemma tr_fst (D : RDesc I) (x : ICls I × RLab k ℓ) : (tr D x).1 = x.1 := rfl

lemma tr_tr (D : RDesc I) (x : ICls I × RLab k ℓ) : tr D (tr D x) = x := by
  simp [tr, rlab_add_add_cancel]

/-- The seeds of initialized locations are the initial seeds. -/
def InitOK (D : RDesc I) : Prop := ∀ v, (I.init v).isSome → D.z v = initSeed I v

/-- The masks lie in the row spaces. -/
def MaskOK (D : RDesc I) : Prop := ∀ e h, D.x e h ∈ maskSet I e

/-- The sum of the seeds at the argument coordinates of `c`. -/
def bsum (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : ZMod 2 :=
  ∑ i, D.z (argLoc (sch I e) i) ((argPerm (sch I e) i).apply c)

/-- The mask-sum condition at column `c` of schema `e`. -/
def MS (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : Prop :=
  msum D e c (k + 2) = bsum D e c

lemma rt0_add_end (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) :
    rt0 D e c + D.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c) = bsum D e c := by
  rw [bsum, sum_args (sch I e) fun v P => D.z v (P.apply c), rt0]

lemma TT_last (D : RDesc I) {e : Fin I.schemas.length} {c : Coord k ℓ} (h : MS D e c) :
    TT D e c (k + 2) = D.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c) := by
  rw [TT, h, ← rt0_add_end, ← add_assoc, zmod2_self_add, zero_add]

lemma TT_succ (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) (h : ℕ) :
    TT D e c (h + 1) = TT D e c h + D.x e (h + 1) c := by
  simp [TT, msum, Finset.sum_range_succ, add_assoc]

lemma TT_zero (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) :
    TT D e c 0 = rt0 D e c := by simp [TT, msum]

/-! ### Labels -/

lemma mem_lab1 {l : RLab k ℓ} : l ∈ lab1 ↔ l.2.1 = 0 ∧ l.2.2 = 0 := by
  obtain ⟨a, b, x⟩ := l
  simp only [lab1, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Prod.fst_zero,
    Prod.snd_zero]
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> simp

lemma mem_lab2 {l : RLab k ℓ} : l ∈ lab2 ↔ l.2.2 = 0 := by
  obtain ⟨a, b, x⟩ := l
  simp only [lab2, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Prod.fst_zero,
    Prod.snd_zero]
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    simp

lemma initSeed_none {v : Fin I.numLocations} (h : I.init v = none) (c : Coord k ℓ) :
    initSeed I v c = 0 := by simp [initSeed, h]

/-- The translation maps the vertices of `G₀` to those of `G₁`. -/
lemma tr_mem (D : RDesc I) (hD : InitOK D) (hM : MaskOK D) {x : ICls I × RLab k ℓ}
    (hx : x ∈ names I) : tr D x ∈ verts I 1 := by
  rw [mem_verts, one_smul]
  rw [mem_names] at hx ⊢
  obtain ⟨X, l⟩ := x
  obtain ⟨hX, hl⟩ := hx
  refine ⟨hX, ?_⟩
  simp only [tr] at hl ⊢
  cases X with
  | coord v c =>
    simp only [labs] at hl ⊢
    cases hv : I.init v with
    | some b =>
      have hz := hD v (by simp [hv])
      simp only [hv, Option.isSome_some, if_true, Finset.mem_singleton] at hl ⊢
      subst hl
      simp [rshift, off, hz, zmod2_self_add]
    | none =>
      simp only [hv, Option.isSome_none, Bool.false_eq_true, if_false, mem_lab1] at hl ⊢
      simp [rshift, off, initSeed_none hv, hl]
  | sum e c => simp only [labs, mem_lab1] at hl ⊢; simp [rshift, off, hl]
  | track e h c => simp only [labs, mem_lab1] at hl ⊢; simp [rshift, off, hl]
  | junc e c => simp only [labs, mem_lab2] at hl ⊢; simp [rshift, off, hl]
  | upd e h c => simp only [labs, mem_lab2] at hl ⊢; simp [rshift, off, hl]
  | coef e h =>
    simp only [labs, Finset.mem_image] at hl ⊢
    obtain ⟨y, hy, rfl⟩ := hl
    exact ⟨y + D.x e h, add_mem_maskSet I hy (hM e h), by simp [rshift, off]⟩
  | link e c => simp [labs] at hl

lemma tr_mem' (D : RDesc I) (hD : InitOK D) (hM : MaskOK D) {x : ICls I × RLab k ℓ}
    (hx : x ∈ verts I 1) : tr D x ∈ names I := by
  rw [mem_verts, one_smul] at hx
  rw [mem_names] at hx ⊢
  obtain ⟨X, l⟩ := x
  obtain ⟨hX, hl⟩ := hx
  refine ⟨hX, ?_⟩
  simp only [tr] at hl ⊢
  cases X with
  | coord v c =>
    simp only [labs] at hl ⊢
    cases hv : I.init v with
    | some b =>
      have hz := hD v (by simp [hv])
      simp only [hv, Option.isSome_some, if_true, Finset.mem_singleton] at hl ⊢
      have : l = (initSeed I v c, 0, 0) := by
        have := congrArg (· + ((initSeed I v c, 0, 0) : RLab k ℓ)) hl
        simpa [off, rlab_add_add_cancel] using this
      subst this
      simp [rshift, hz, zmod2_self_add]
    | none =>
      simp only [hv, Option.isSome_none, Bool.false_eq_true, if_false, mem_lab1] at hl ⊢
      simpa [rshift, off, initSeed_none hv] using hl
  | sum e c => simp only [labs, mem_lab1] at hl ⊢; simpa [rshift, off] using hl
  | track e h c => simp only [labs, mem_lab1] at hl ⊢; simpa [rshift, off] using hl
  | junc e c => simp only [labs, mem_lab2] at hl ⊢; simpa [rshift, off] using hl
  | upd e h c => simp only [labs, mem_lab2] at hl ⊢; simpa [rshift, off] using hl
  | coef e h =>
    simp only [labs, Finset.mem_image] at hl ⊢
    obtain ⟨y, hy, hyl⟩ := hl
    simp only [off, add_zero] at hyl
    subst hyl
    exact ⟨y + D.x e h, add_mem_maskSet I hy (hM e h), by simp [rshift]⟩
  | link e c => simp [labs] at hl

/-! ### Adjacency -/

/-- The conditions on a description needed at a hub class. -/
def EdgeOK (D : RDesc I) : ICls I → Prop
  | .upd e h c => 1 ≤ h ∧ h ≤ k + 2 ∧ MS D e c
  | .junc e c => isTern (sch I e) = true
  | _ => True

lemma rshift_trackCls (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) {h : ℕ}
    (hh : h ≤ k + 2) (hms : h = k + 2 → MS D e c) :
    (rshift D (trackCls I e c h)).1 = TT D e c h := by
  unfold trackCls
  split_ifs with h0 h1
  · subst h0
    rw [TT_zero]
    unfold startCls rt0
    split <;> simp_all [rshift, rt0]
  · subst h1
    rw [TT_last D (hms rfl)]
    rfl
  · rfl

lemma add_iff_of_eq {a b c d : ZMod 2} (h : c = d) : a + c = b + d ↔ a = b := by
  subst h; exact add_left_inj c

lemma hubR_tr (D : RDesc I) {X Y : ICls I} (hX : EdgeOK D X) (l m : RLab k ℓ) :
    hubR I X l Y m ↔ hubR I X (l + rshift D X) Y (m + rshift D Y) := by
  cases X with
  | upd e h c =>
    obtain ⟨h1, h2, hms⟩ := hX
    simp only [hubR]
    apply or_congr
    · apply and_congr_right
      rintro rfl
      exact (add_iff_of_eq (rshift_trackCls D e c (by omega) (by omega))).symm
    apply or_congr
    · apply and_congr_right
      rintro rfl
      exact (add_iff_of_eq (rshift_trackCls D e c h2 fun _ => hms)).symm
    · apply and_congr_right
      rintro rfl
      have hx : D.x e h c = TT D e c (h - 1) + TT D e c h := by
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
        rw [Nat.add_sub_cancel, TT_succ, ← add_assoc, zmod2_self_add, zero_add]
      simp only [rshift, Prod.fst_add, Prod.snd_add, Pi.add_apply]
      rw [hx, show l.1 + TT D e c (h - 1) + (l.2.1 + TT D e c h) =
        l.1 + l.2.1 + (TT D e c (h - 1) + TT D e c h) by ring]
      exact (add_iff_of_eq rfl).symm
  | junc e c =>
    simp only [hubR]
    apply or_congr
    · apply and_congr_right
      rintro rfl
      exact (add_iff_of_eq rfl).symm
    apply or_congr
    · apply and_congr_right
      rintro rfl
      exact (add_iff_of_eq rfl).symm
    · apply and_congr_right
      rintro rfl
      simp only [rshift, Prod.fst_add, Prod.snd_add, rt0, show isTern (sch I e) = true from hX,
        if_true]
      rw [show l.1 + D.z (locU (sch I e)) ((permU (sch I e)).apply c) +
        (l.2.1 + D.z (locV (sch I e)) ((permV (sch I e)).apply c)) =
        l.1 + l.2.1 + (D.z (locU (sch I e)) ((permU (sch I e)).apply c) +
          D.z (locV (sch I e)) ((permV (sch I e)).apply c)) by ring]
      exact (add_iff_of_eq rfl).symm
  | coord => simp [hubR]
  | sum => simp [hubR]
  | link => simp [hubR]
  | track => simp [hubR]
  | coef => simp [hubR]

lemma radj_tr (D : RDesc I) {x y : ICls I × RLab k ℓ} (hx : EdgeOK D x.1) (hy : EdgeOK D y.1) :
    radj I x y ↔ radj I (tr D x) (tr D y) :=
  or_congr (hubR_tr D hx _ _) (hubR_tr D hy _ _)

end Lax119563Proofs.RowSpace
