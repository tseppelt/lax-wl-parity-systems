import Lax119563Proofs.RowSpace.SpoilerStage
import Lax119563.ColoredHomomorphisms

/-!
# The affine dichotomy

Adjacency in the row-space graphs is given by linear conditions on the labels, so labels of
homomorphisms can be added: if some homomorphism `F → G₁` exists, adding its labels is a
bijection from homomorphisms `F → G₀` to homomorphisms `F → G₁`. Hence
`hom(F, G₁) ∈ {0, hom(F, G₀)}`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.ColoredHomomorphisms
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-- Adjacency conditions add up (for hubs of valid classes). -/
lemma hubR_add {X Y : ICls I} (hX : X ∈ classes I) {l m l' m' : RLab k ℓ} (h : hubR I X l Y m)
    (h' : hubR I X l' Y m') : hubR I X (l + l') Y (m + m') := by
  cases X with
  | upd e σ c =>
    obtain ⟨⟨hσ, -⟩, -⟩ := mem_classes_upd.mp hX
    obtain ⟨n, rfl⟩ : ∃ n, σ = n + 1 := ⟨σ - 1, by omega⟩
    rw [hubR_upd_succ] at h h' ⊢
    have hne : trackCls I e c n ≠ trackCls I e c (n + 1) := fun h => by
      have := trackCls_injective e c h; omega
    have h1 := trackCls_ne_coef e c n (n + 1)
    have h2 := trackCls_ne_coef e c (n + 1) (n + 1)
    rcases h with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ⟨rfl, ha⟩ <;>
      rcases h' with ⟨hY, hb⟩ | ⟨hY, hb⟩ | ⟨hY, hb⟩ <;>
      first
        | exact absurd hY hne | exact absurd hY.symm hne | exact absurd hY h1
        | exact absurd hY.symm h1 | exact absurd hY h2 | exact absurd hY.symm h2
        | skip
    · exact Or.inl ⟨rfl, by simp only [Prod.fst_add, ha, hb]⟩
    · exact Or.inr (Or.inl ⟨rfl, by simp only [Prod.fst_add, Prod.snd_add, ha, hb]⟩)
    · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ha, hb]
      ring
  | junc e c =>
    have hne := coordU_ne_coordV (mem_classes_junc.mp hX).1 c
    have h1 : coordU e c ≠ (Cls.sum e c : ICls I) := by simp [coordU]
    have h2 : coordV e c ≠ (Cls.sum e c : ICls I) := by simp [coordV]
    rw [hubR_junc'] at h h' ⊢
    rcases h with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ⟨rfl, ha⟩ <;>
      rcases h' with ⟨hY, hb⟩ | ⟨hY, hb⟩ | ⟨hY, hb⟩ <;>
      first
        | exact absurd hY hne | exact absurd hY.symm hne | exact absurd hY h1
        | exact absurd hY.symm h1 | exact absurd hY h2 | exact absurd hY.symm h2
        | skip
    · exact Or.inl ⟨rfl, by simp only [Prod.fst_add, ha, hb]⟩
    · exact Or.inr (Or.inl ⟨rfl, by simp only [Prod.fst_add, Prod.snd_add, ha, hb]⟩)
    · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      simp only [Prod.fst_add, Prod.snd_add, ha, hb]
      ring
  | coord => exact h.elim
  | sum => exact h.elim
  | link => exact h.elim
  | track => exact h.elim
  | coef => exact h.elim

/-- Adjacency conditions hold for zero labels. -/
lemma hubR_zero {X Y : ICls I} {l m : RLab k ℓ} (h : hubR I X l Y m) : hubR I X 0 Y 0 := by
  cases X with
  | upd e σ c => rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [hubR]
  | junc e c => rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [hubR]
  | coord => exact h.elim
  | sum => exact h.elim
  | link => exact h.elim
  | track => exact h.elim
  | coef => exact h.elim

/-- Adjacent vertices have adjacent zero vertices. -/
lemma radj_zero {x y : ICls I × RLab k ℓ} (h : radj I x y) : radj I (x.1, 0) (y.1, 0) :=
  h.imp hubR_zero hubR_zero

/-- Adjacency of vertices of valid classes adds up. -/
lemma radj_add {X Y : ICls I} (hX : X ∈ classes I) (hY : Y ∈ classes I) {a b a' b' : RLab k ℓ}
    (h : radj I (X, a) (Y, b)) (h' : radj I (X, a') (Y, b')) :
    radj I (X, a + a') (Y, b + b') := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact Or.inl (hubR_add hX h h')
  · exact absurd (hubR_hub I h').1 (hubR_hub I h).2
  · exact absurd (hubR_hub I h').1 (hubR_hub I h).2
  · exact Or.inr (hubR_add hY h h')

/-- The label sets are closed under addition. -/
lemma labs_add {X : ICls I} {a b : RLab k ℓ} (ha : a ∈ labs I X) (hb : b ∈ labs I X) :
    a + b ∈ labs I X := by
  cases X with
  | coord v c =>
    simp only [labs] at ha hb ⊢
    by_cases hv : (I.init v).isSome
    · simp only [hv, if_true, Finset.mem_singleton] at ha hb ⊢; simp [ha, hb]
    · simp only [hv, Bool.false_eq_true, if_false, mem_lab1] at ha hb ⊢; simp [ha, hb]
  | sum => simp only [labs, mem_lab1] at ha hb ⊢; simp [ha, hb]
  | track => simp only [labs, mem_lab1] at ha hb ⊢; simp [ha, hb]
  | junc => simp only [labs, mem_lab2] at ha hb ⊢; simp [ha, hb]
  | upd => simp only [labs, mem_lab2] at ha hb ⊢; simp [ha, hb]
  | coef e h =>
    simp only [labs, Finset.mem_image] at ha hb ⊢
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x + y, add_mem_maskSet I hx hy, by simp⟩
  | link => simp [labs] at ha

lemma mem_verts_one {x : ICls I × RLab k ℓ} :
    x ∈ verts I 1 ↔ x.1 ∈ classes I ∧ x.2 + off I x.1 ∈ labs I x.1 := by
  rw [mem_verts, one_smul, mem_names]

lemma mem_verts_zero {x : ICls I × RLab k ℓ} :
    x ∈ verts I 0 ↔ x.1 ∈ classes I ∧ x.2 ∈ labs I x.1 := by
  rw [verts_zero, mem_names]


/-- Color-preserving homomorphisms into `G_ε`. -/
abbrev RHom (I : ImplicitParitySystem k ℓ) (F : ColoredGraph) (ε : ZMod 2) :=
  {h : F.graph →g (rsGraph I ε).graph // ∀ v, (rsGraph I ε).color (h v) = F.color v}

lemma rhom_cls {F : ColoredGraph} {ε ε' : ZMod 2} (φ : RHom I F ε) (ψ : RHom I F ε')
    (p : Fin F.n) : (vx (φ.1 p)).1 = (vx (ψ.1 p)).1 :=
  (rs_color_eq _ _).mp ((φ.2 p).trans (ψ.2 p).symm)

/-- Adding the labels of a fixed homomorphism `ψ : F → G₁`. -/
noncomputable def fwdHom {F : ColoredGraph} (ψ : RHom I F 1) (φ : RHom I F 0) : RHom I F 1 :=
  ⟨⟨fun p => ix 1 ((vx (φ.1 p)).1, (vx (φ.1 p)).2 + (vx (ψ.1 p)).2) (by
      have h0 := mem_verts_zero.mp (vx_mem (φ.1 p))
      have h1 := mem_verts_one.mp (vx_mem (ψ.1 p))
      rw [← rhom_cls φ ψ p] at h1
      refine mem_verts_one.mpr ⟨h0.1, ?_⟩
      simpa only [add_assoc] using labs_add h0.2 h1.2),
    fun {p q} hpq => by
      rw [rs_adj, vx_ix, vx_ix]
      have h0 := (φ.1.map_rel hpq : (rsGraph I 0).graph.Adj _ _)
      have h1 := (ψ.1.map_rel hpq : (rsGraph I 1).graph.Adj _ _)
      rw [rs_adj] at h0 h1
      have hcp := rhom_cls φ ψ p
      have hcq := rhom_cls φ ψ q
      have hp := (mem_verts_zero.mp (vx_mem (φ.1 p))).1
      have hq := (mem_verts_zero.mp (vx_mem (φ.1 q))).1
      rw [← Prod.mk.eta (p := vx (φ.1 p)), ← Prod.mk.eta (p := vx (φ.1 q))] at h0
      rw [← Prod.mk.eta (p := vx (ψ.1 p)), ← Prod.mk.eta (p := vx (ψ.1 q)), ← hcp, ← hcq] at h1
      exact radj_add hp hq h0 h1⟩,
    fun p => by
      rw [rs_color]; change code I (vx (ix _ _ _)).1 = _; rw [vx_ix]; exact φ.2 p⟩

/-- Subtracting the labels of a fixed homomorphism `ψ : F → G₁`. -/
noncomputable def bwdHom {F : ColoredGraph} (ψ : RHom I F 1) (φ : RHom I F 1) : RHom I F 0 :=
  ⟨⟨fun p => ix 0 ((vx (φ.1 p)).1, (vx (φ.1 p)).2 + (vx (ψ.1 p)).2) (by
      have h0 := mem_verts_one.mp (vx_mem (φ.1 p))
      have h1 := mem_verts_one.mp (vx_mem (ψ.1 p))
      rw [← rhom_cls φ ψ p] at h1
      refine mem_verts_zero.mpr ⟨h0.1, ?_⟩
      have := labs_add h0.2 h1.2
      have e : (vx (φ.1 p)).2 + off I (vx (φ.1 p)).1 + ((vx (ψ.1 p)).2 + off I (vx (φ.1 p)).1) =
          (vx (φ.1 p)).2 + (vx (ψ.1 p)).2 := by
        rw [add_comm (vx (ψ.1 p)).2, ← add_assoc, rlab_add_add_cancel]
      rwa [e] at this),
    fun {p q} hpq => by
      rw [rs_adj, vx_ix, vx_ix]
      have h0 := (φ.1.map_rel hpq : (rsGraph I 1).graph.Adj _ _)
      have h1 := (ψ.1.map_rel hpq : (rsGraph I 1).graph.Adj _ _)
      rw [rs_adj] at h0 h1
      have hcp := rhom_cls φ ψ p
      have hcq := rhom_cls φ ψ q
      have hp := (mem_verts_one.mp (vx_mem (φ.1 p))).1
      have hq := (mem_verts_one.mp (vx_mem (φ.1 q))).1
      rw [← Prod.mk.eta (p := vx (φ.1 p)), ← Prod.mk.eta (p := vx (φ.1 q))] at h0
      rw [← Prod.mk.eta (p := vx (ψ.1 p)), ← Prod.mk.eta (p := vx (ψ.1 q)), ← hcp, ← hcq] at h1
      exact radj_add hp hq h0 h1⟩,
    fun p => by
      rw [rs_color]; change code I (vx (ix _ _ _)).1 = _; rw [vx_ix]; exact φ.2 p⟩

/-- Adding the labels of a homomorphism `F → G₁` is a bijection. -/
noncomputable def addEquiv {F : ColoredGraph} (ψ : RHom I F 1) : RHom I F 0 ≃ RHom I F 1 where
  toFun := fwdHom ψ
  invFun := bwdHom ψ
  left_inv φ := by
    refine Subtype.ext (RelHom.ext fun p => vx_injective ?_)
    simp [bwdHom, fwdHom, rlab_add_add_cancel]
  right_inv φ := by
    refine Subtype.ext (RelHom.ext fun p => vx_injective ?_)
    simp [bwdHom, fwdHom, rlab_add_add_cancel]

/-- **Affine dichotomy.** -/
theorem hom_dichotomy (F : ColoredGraph) (hne : hom F (rsGraph I 0) ≠ hom F (rsGraph I 1)) :
    hom F (rsGraph I 1) = 0 ∧
      Nonempty {h : F.graph →g (rsGraph I 0).graph // ∀ v, (rsGraph I 0).color (h v) = F.color v} := by
  have h1 : hom F (rsGraph I 1) = 0 := by
    by_contra h
    obtain ⟨⟨ψ⟩, -⟩ := Nat.card_ne_zero.mp h
    exact hne (Nat.card_congr (addEquiv ψ))
  refine ⟨h1, (Nat.card_ne_zero.mp ?_).1⟩
  rw [h1] at hne
  exact hne

end Lax119563Proofs.RowSpace
