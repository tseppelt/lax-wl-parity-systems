import Lax119563Proofs.HomTensors.LGraph
import Lax119563Proofs.HomTensors.PolyClosure

/-!
# The spaces `𝒱_N` of homomorphism tensors

For colored graphs `G, H` let `Tup k G H = V(G)^k ⊔ V(H)^k`. The tensor of a labeled graph is
the concatenation of its homomorphism tensors on `G` and on `H`. `Vs G H N` is the span of the
tensors of good labeled graphs with at most `N` vertices besides the labels. It contains the
constant `1`, is closed under products (gluing: `Vs a * Vs b ≤ Vs (a + b)`), and under the
extension operator (`extOp` maps `Vs N ^ k` into `Vs (1 + k N)`).
-/

namespace Lax119563Proofs.HomTensors

open Lax119563.ColoredGraphs LGraph Finset

variable {k : ℕ} (G H : ColoredGraph)

/-- The `k`-tuples of `G` and of `H`. -/
abbrev Tup (k : ℕ) (G H : ColoredGraph) := (Fin k → Fin G.n) ⊕ (Fin k → Fin H.n)

/-- The tensor of a labeled graph on `Tup k G H`. -/
noncomputable def tens (F : LGraph k) : Tup k G H → ℚ :=
  Sum.elim (fun v => (F.tensor G v : ℚ)) (fun v => (F.tensor H v : ℚ))

/-- Tensors of good labeled graphs. -/
def tset (N : ℕ) : Set (Tup k G H → ℚ) := {f | ∃ F : LGraph k, F.Good N ∧ tens G H F = f}

/-- The span `𝒱_N`. -/
noncomputable def Vs (N : ℕ) : Submodule ℚ (Tup k G H → ℚ) := Submodule.span ℚ (tset G H N)

variable {G H}

lemma Vs_mono {N N' : ℕ} (h : N ≤ N') : Vs (k := k) G H N ≤ Vs G H N' :=
  Submodule.span_mono (by rintro f ⟨F, hF, rfl⟩; exact ⟨F, hF.mono h, rfl⟩)

lemma tens_mem {N : ℕ} {F : LGraph k} (hF : F.Good N) : tens G H F ∈ Vs G H N :=
  Submodule.subset_span ⟨F, hF, rfl⟩

/-! ### Atoms -/

open scoped Classical in
lemma tens_atom_inl (adj : Fin k → Fin k → Prop) (pred : Fin k → ℕ → Prop)
    (eqv : Fin k → Fin k → Prop) (v : Fin k → Fin G.n) :
    tens G H (atom adj pred eqv) (.inl v) = if (atom adj pred eqv).IsHom G v then 1 else 0 := by
  simp only [tens, Sum.elim_inl, tensor_atom]
  split_ifs <;> simp

open scoped Classical in
lemma tens_atom_inr (adj : Fin k → Fin k → Prop) (pred : Fin k → ℕ → Prop)
    (eqv : Fin k → Fin k → Prop) (v : Fin k → Fin H.n) :
    tens G H (atom adj pred eqv) (.inr v) = if (atom adj pred eqv).IsHom H v then 1 else 0 := by
  simp only [tens, Sum.elim_inr, tensor_atom]
  split_ifs <;> simp

lemma one_mem_Vs : (1 : Tup k G H → ℚ) ∈ Vs G H 0 := by
  have h := tens_mem (G := G) (H := H) (good_atom (k := k) (fun _ _ => False) (fun _ _ => False)
    (fun _ _ => False))
  convert h using 1
  funext x
  rcases x with v | v
  · rw [tens_atom_inl, if_pos (by simp [atom, IsHom])]; rfl
  · rw [tens_atom_inr, if_pos (by simp [atom, IsHom])]; rfl

/-! ### Products -/

/-- Gluing two labeled graphs along their labels. -/
def mul (F₁ F₂ : LGraph k) : LGraph k :=
  glue (Fin k) id Bool (fun b => cond b F₁ F₂) (fun _ => id)

lemma tensor_mul (F₁ F₂ : LGraph k) (G : ColoredGraph) (v : Fin k → Fin G.n) :
    (mul F₁ F₂).tensor G v = F₁.tensor G v * F₂.tensor G v := by
  rw [mul, tensor_glue]
  simp [Function.comp_id, Fintype.prod_bool]

lemma good_mul {F₁ F₂ : LGraph k} {a b : ℕ} (h₁ : F₁.Good a) (h₂ : F₂.Good b) :
    (mul F₁ F₂).Good (a + b) := by
  have := good_glue (L := Fin k) (lam := id) (J := Bool) (F := fun b => cond b F₁ F₂)
    (σ := fun _ => id) (fun c => cond c a b) (by rintro (_ | _) <;> assumption)
    (by simp)
  refine this.mono (le_of_eq ?_)
  have : Nat.card {l : Fin k // l ∉ Set.range (id : Fin k → Fin k)} = 0 := by
    rw [Nat.card_eq_zero]; left; exact ⟨fun ⟨l, hl⟩ => hl ⟨l, rfl⟩⟩
  simp [this, Fintype.sum_bool, add_comm]

lemma tens_mul (F₁ F₂ : LGraph k) : tens G H (mul F₁ F₂) = tens G H F₁ * tens G H F₂ := by
  funext x
  rcases x with v | v <;> simp [tens, tensor_mul]

lemma Vs_mul (a b : ℕ) : Vs (k := k) G H a * Vs G H b ≤ Vs G H (a + b) := by
  rw [Vs, Vs, Submodule.span_mul_span]
  apply Submodule.span_le.2
  rintro _ ⟨_, ⟨F₁, h₁, rfl⟩, _, ⟨F₂, h₂, rfl⟩, rfl⟩
  show tens G H F₁ * tens G H F₂ ∈ _
  rw [← tens_mul]
  exact tens_mem (good_mul h₁ h₂)

lemma list_prod_mem (a : ℕ) (l : List (Tup k G H → ℚ)) (hl : ∀ g ∈ l, g ∈ Vs G H a) :
    l.prod ∈ Vs G H (l.length * a) := by
  induction l with
  | nil => simpa using one_mem_Vs
  | cons g l ih =>
    rw [List.prod_cons, List.length_cons, add_mul, one_mul, add_comm]
    exact Vs_mul _ _ (Submodule.mul_mem_mul (hl g (by simp))
      (ih fun g' hg' => hl g' (by simp [hg'])))

lemma polySpan_le_Vs (𝒢 : Set (Tup k G H → ℚ)) (a d : ℕ)
    (h𝒢 : 𝒢 ⊆ (Vs (k := k) G H a : Set (Tup k G H → ℚ))) :
    polySpan 𝒢 d ≤ Vs G H (d * a) := by
  apply Submodule.span_le.2
  rintro _ ⟨l, hl, hg, rfl⟩
  exact Vs_mono (Nat.mul_le_mul_right a hl) (list_prod_mem a l fun g hg' => h𝒢 (hg g hg'))

/-! ### Extension -/

/-- The extension operator: `v ↦ ∑_x ∏_j f_j(v[x/j])`. -/
noncomputable def extOp (f : Fin k → Tup k G H → ℚ) : Tup k G H → ℚ :=
  Sum.elim (fun p => ∑ q, ∏ j, f j (.inl (Function.update p j q)))
    (fun p => ∑ q, ∏ j, f j (.inr (Function.update p j q)))

/-- Extension of `k` labeled graphs: a fresh vertex `w = none`, labels `b_i = some i`; the
`j`-th label of `F j` is glued to `w`, its other labels `i` to `b_i`. -/
def extG (F : Fin k → LGraph k) : LGraph k :=
  glue (Option (Fin k)) some (Fin k) F (fun j i => if i = j then none else some i)

lemma tensor_extG (F : Fin k → LGraph k) (G : ColoredGraph) (v : Fin k → Fin G.n) :
    (extG F).tensor G v = ∑ q, ∏ j, (F j).tensor G (Function.update v j q) := by
  classical
  rw [extG, tensor_glue]
  rw [← (Equiv.piOptionEquivProd (β := fun _ => Fin G.n)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hc : ∀ w : Fin k → Fin G.n,
      ((Equiv.piOptionEquivProd (β := fun _ => Fin G.n)).symm (q, w)) ∘ some = w := by
    intro w; funext i; rfl
  simp only [hc]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  funext i
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

lemma good_extG {F : Fin k → LGraph k} {N : ℕ} (hF : ∀ j, (F j).Good N) :
    (extG F).Good (1 + k * N) := by
  have := good_glue (L := Option (Fin k)) (lam := some) (J := Fin k) (F := F)
    (σ := fun j i => if i = j then none else some i) (fun _ => N) hF (by simp)
  refine this.mono (le_of_eq ?_)
  have : Nat.card {l : Option (Fin k) // l ∉ Set.range some} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨none, by simp⟩, ?_⟩
    rintro ⟨_ | l, hl⟩
    · rfl
    · exact absurd ⟨l, rfl⟩ hl
  rw [this]
  simp

lemma tens_extG (F : Fin k → LGraph k) :
    tens G H (extG F) = extOp (fun j => tens G H (F j)) := by
  funext x
  rcases x with v | v <;> simp [tens, extOp, tensor_extG]

lemma prod_update_apply {Y : Type} (f : Fin k → Y → ℚ) (j : Fin k) (x : Y → ℚ)
    (pt : Fin k → Y) :
    ∏ i, (Function.update f j x i) (pt i) = x (pt j) * ∏ i ∈ univ.erase j, f i (pt i) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

lemma extOp_update_add (f : Fin k → Tup k G H → ℚ) (j : Fin k) (x y : Tup k G H → ℚ) :
    extOp (Function.update f j (x + y)) =
      extOp (Function.update f j x) + extOp (Function.update f j y) := by
  funext z
  rcases z with p | p <;>
  · simp only [extOp, Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
    simp only [prod_update_apply (Y := Tup k G H) f j _
      (fun i => _), Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma extOp_update_smul (f : Fin k → Tup k G H → ℚ) (j : Fin k) (c : ℚ) (x : Tup k G H → ℚ) :
    extOp (Function.update f j (c • x)) = c • extOp (Function.update f j x) := by
  funext z
  rcases z with p | p <;>
  · simp only [extOp, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul]
    simp only [prod_update_apply (Y := Tup k G H) f j _
      (fun i => _), Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- A map that is additive and homogeneous in each argument sends a family of spans into a
submodule as soon as it does so for the generators. -/
lemma multilinear_mem {ι M N : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    [Module ℚ M] [AddCommGroup N] [Module ℚ N] (Φ : (ι → M) → N)
    (hadd : ∀ f j x y, Φ (Function.update f j (x + y)) =
      Φ (Function.update f j x) + Φ (Function.update f j y))
    (hsmul : ∀ f j (c : ℚ) x, Φ (Function.update f j (c • x)) = c • Φ (Function.update f j x))
    (S : ι → Set M) (V : Submodule ℚ N) (hS : ∀ f, (∀ j, f j ∈ S j) → Φ f ∈ V)
    (f : ι → M) (hf : ∀ j, f j ∈ Submodule.span ℚ (S j)) : Φ f ∈ V := by
  have key : ∀ s : Finset ι, ∀ f : ι → M, (∀ j ∈ s, f j ∈ Submodule.span ℚ (S j)) →
      (∀ j ∉ s, f j ∈ S j) → Φ f ∈ V := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun f _ h => hS f fun j => h j (Finset.notMem_empty j)
    | insert a s ha ih =>
      intro f h₁ h₂
      let U : Submodule ℚ M :=
        { carrier := {x | Φ (Function.update f a x) ∈ V}
          add_mem' := fun {x y} hx hy => by
            simp only [Set.mem_ofPred_eq, hadd] at *
            exact V.add_mem hx hy
          zero_mem' := by
            simp only [Set.mem_ofPred_eq]
            have := hsmul f a 0 0
            rw [zero_smul, zero_smul] at this
            rw [this]
            exact V.zero_mem
          smul_mem' := fun c x hx => by
            simp only [Set.mem_ofPred_eq, hsmul] at *
            exact V.smul_mem c hx }
      have hU : Submodule.span ℚ (S a) ≤ U := by
        apply Submodule.span_le.2
        intro x hx
        show Φ (Function.update f a x) ∈ V
        apply ih
        · intro j hj
          rw [Function.update_of_ne (by rintro rfl; exact ha hj)]
          exact h₁ j (Finset.mem_insert_of_mem hj)
        · intro j hj
          by_cases hja : j = a
          · subst hja; simpa using hx
          · rw [Function.update_of_ne hja]
            exact h₂ j (by simp [hja, hj])
      have hfa : f a ∈ U := hU (h₁ a (Finset.mem_insert_self a s))
      have : Φ (Function.update f a (f a)) ∈ V := hfa
      rwa [Function.update_eq_self] at this
  exact key univ f (fun j _ => hf j) (fun j hj => absurd (mem_univ j) hj)

lemma extOp_mem {N : ℕ} (f : Fin k → Tup k G H → ℚ) (hf : ∀ j, f j ∈ Vs G H N) :
    extOp f ∈ Vs G H (1 + k * N) := by
  classical
  refine multilinear_mem extOp extOp_update_add extOp_update_smul (fun _ => tset G H N) _ ?_ f hf
  intro f hf
  choose F hF hFf using hf
  have : f = fun j => tens G H (F j) := funext fun j => (hFf j).symm
  rw [this, ← tens_extG]
  exact tens_mem (good_extG hF)

end Lax119563Proofs.HomTensors
