import Lax119563Proofs.Reduction.PkCmd

/-!
# The stacks of the command enumerator for a runtime number of blocks

For the command enumerator `cmdEnumP`: `cmdStksP` (the stacks of the body, one per command,
in order),
`out_cmdEnumP'`, `cmdStksP_forall₂` (relation `StkCmd`), `keys_cmdStksP` (the keys are
`keyList`) and `length_out_beforeP` (counting the commands before a given one).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp

variable {M : Machine} {s : ℕ}

variable (M) in
/-- The stacks on which the body of the command enumerator runs, in order. -/
noncomputable def cmdStksP (b : ℕ) (HX RX : Xp) (ρ : List ℕ) (s H : ℕ) : List (List ℕ) :=
  (List.range (numLoc M H)).flatMap fun c =>
    match decodeLoc M H c with
    | some L => stksP M b HX RX ρ s H L
    | none => []

lemma forall₂_flipP {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → List.Forall₂ (fun b a => R a b) l' l
  | [], [], List.Forall₂.nil => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t => List.Forall₂.cons h (forall₂_flipP t)

lemma map_eq_of_forall₂P {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ a b, R a b → f a = g b) →
      l₁.map f = l₂.map g
  | [], [], List.Forall₂.nil, _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h t, hf => by
    rw [List.map_cons, List.map_cons, hf _ _ h, map_eq_of_forall₂P t hf]

section Stacks

variable {x y : List Bool} {ρ : List ℕ} {b H : ℕ} {SX HX RX : Xp}

lemma stksP_rel (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
    (hR : RX.eval ρ = radix M H) (ℓ : ℕ) (L : Loc M H) :
    List.Forall₂ (StkCmd x s ℓ H b ρ) (stksP M b HX RX ρ s H L)
      ((moves M x s ℓ H L).map (Move.toACmd ℓ L)) := by
  have h := stksP_spec (x := x) (s := s) hρ hHb hRb hH hR ℓ L
  rw [← map_fst_zipIdxP (moves M x s ℓ H L) 0, List.map_map, List.forall₂_map_right_iff]
  refine (forall₂_flipP h).imp fun {τ p} hp => ?_
  obtain ⟨h1, h2, h3, -, h5⟩ := hp
  exact ⟨h1, h2, by simp only [Function.comp, src_toACmd]; exact h3, h5⟩

lemma stksP_keys (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
    (hR : RX.eval ρ = radix M H) (ℓ : ℕ) (L : Loc M H) :
    (stksP M b HX RX ρ s H L).map (keyAt b) =
      (List.range (moves M x s ℓ H L).length).map ((Loc.code L).val, ·) := by
  have h := stksP_spec (x := x) (s := s) hρ hHb hRb hH hR ℓ L
  rw [List.range_eq_range', ← map_zipIdx_snd (fun k => ((Loc.code L).val, k))
    (moves M x s ℓ H L) 0]
  exact map_eq_of_forall₂P (forall₂_flipP h) fun τ p hp => by
    simp only [keyAt, hp.2.2.1, hp.2.2.2.1]

variable (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hSb : SX.Bnd b)
  (hH : HX.eval ρ = H) (hR : RX.eval ρ = radix M H) (hS : SX.eval ρ = s) (hs : 1 ≤ s)
include hρ hHb hRb hH hR

/-- **The output of the command enumerator, by stacks.** -/
theorem out_cmdEnumP' (body : Gn) (hSb : SX.Bnd b) (hS : SX.eval ρ = s) (hs : 1 ≤ s) :
    (cmdEnumP M b SX HX RX body).out y ρ = (cmdStksP M b HX RX ρ s H).flatMap (body.out y) := by
  rw [out_cmdEnumP hρ hHb hRb hSb hH hR hS hs, cmdStksP, List.flatMap_assoc]
  refine List.flatMap_congr fun c _ => ?_
  cases decodeLoc M H c with
  | none => rfl
  | some L => rfl

/-- **The stacks belong to the commands, in order.** -/
theorem cmdStksP_forall₂ (ℓ : ℕ) :
    List.Forall₂ (StkCmd x s ℓ H b ρ) (cmdStksP M b HX RX ρ s H) (verifierCmds' M x s ℓ H) := by
  rw [verifierCmds'_eq, cmdStksP]
  refine forall₂_flatMap (List.forall₂_same.mpr fun c _ => ?_)
  cases decodeLoc M H c with
  | none => exact List.Forall₂.nil
  | some L => exact stksP_rel hρ hHb hRb hH hR ℓ L

/-- **The keys of the stacks.** -/
theorem keys_cmdStksP (ℓ : ℕ) :
    (cmdStksP M b HX RX ρ s H).map (keyAt b) = keyList M s x ℓ H := by
  rw [cmdStksP, keyList, List.map_flatMap]
  refine List.flatMap_congr fun c _ => ?_
  cases decodeLoc M H c with
  | none => rfl
  | some L => exact stksP_keys hρ hHb hRb hH hR ℓ L

end Stacks

theorem keyList_pairwise' {x : List Bool} {ℓ H : ℕ} :
    (keyList M s x ℓ H).Pairwise (fun p q => lexLt p q = true) :=
  keyList_pairwise (M := M) (s := s) (x := x) (ρ := []) (b := 0) (HX := const H)
    (RX := const (radix M H)) rfl trivial trivial rfl rfl ℓ

variable {x y : List Bool} {b H : ℕ} {SX HX RX : Xp}

/-- **Counting before**: the length of the output of a nested enumerator whose body is
`when (beforeX b b') g` is a sum over the stacks before the outer one. -/
theorem length_out_beforeP {ρ σ : List ℕ} (ℓ : ℕ) (hρ : ρ.length = b) (hHb : HX.Bnd b)
    (hRb : RX.Bnd b) (hSb : SX.Bnd b) (hH : HX.eval ρ = H) (hR : RX.eval ρ = radix M H)
    (hS : SX.eval ρ = s) (hs : 1 ≤ s)
    {b' : ℕ} (hb' : b + 25 ≤ b') (hσ : σ.length = b') (hσρ : σ.take b = ρ)
    {j : ℕ} (hj : j < (cmdStksP M b HX RX ρ s H).length)
    (hστ : σ.take (b + 25) = (cmdStksP M b HX RX ρ s H)[j]) (g : Gn) :
    ((cmdEnumP M b' SX HX RX (Gn.when (beforeX b b') g)).out y σ).length =
      (((cmdStksP M b' HX RX σ s H).take j).map fun τ' => (g.out y τ').length).sum := by
  have hσsplit : σ = ρ ++ σ.drop b := by rw [← hσρ, List.take_append_drop]
  have hHσ : HX.eval σ = H := by rw [hσsplit]; exact (Xp.eval_append hρ _ hHb).trans hH
  have hRσ : RX.eval σ = radix M H := by rw [hσsplit]; exact (Xp.eval_append hρ _ hRb).trans hR
  have hSσ : SX.eval σ = s := by rw [hσsplit]; exact (Xp.eval_append hρ _ hSb).trans hS
  have hHσb : HX.Bnd b' := Xp.Bnd.mono (by omega) hHb
  have hRσb : RX.Bnd b' := Xp.Bnd.mono (by omega) hRb
  have hSσb : SX.Bnd b' := Xp.Bnd.mono (by omega) hSb
  set τ := (cmdStksP M b HX RX ρ s H)[j] with hτ
  have hF := cmdStksP_forall₂ (x := ([] : List Bool)) (s := s) (M := M) hσ hHσb hRσb hHσ hRσ ℓ
  have hkey : ∀ τ' ∈ cmdStksP M b' HX RX σ s H, keyAt b τ' = keyAt b τ := by
    intro τ' hτ'
    obtain ⟨cmd, -, hrel⟩ := forall₂_exists_of_mem_left hF hτ'
    have h1 : τ'.take b' = σ := hrel.2.1
    have g1 : ∀ i < b + 25, τ'.getD i 0 = τ.getD i 0 := by
      intro i hi
      have hτlen : τ.length = b + 25 := by
        rw [← hστ, List.length_take, hσ]; omega
      rw [← getD_take' (n := b') (by omega), h1, ← getD_take' (n := b + 25) hi, hστ]
    simp only [keyAt, g1 (b + 15) (by omega), g1 (b + 16) (by omega)]
  rw [out_cmdEnumP' hσ hHσb hRσb hHσ hRσ _ hSσb hSσ hs, List.length_flatMap]
  simp only [Gn.out_when, eval_beforeX]
  have : ((cmdStksP M b' HX RX σ s H).map fun τ' =>
      (if (if lexLt (keyAt b' τ') (keyAt b τ') = true then 1 else 0) ≠ 0 then g.out y τ'
        else []).length) =
      (cmdStksP M b' HX RX σ s H).map fun τ' =>
        if lexLt (keyAt b' τ') (keyAt b τ) then (g.out y τ').length else 0 := by
    refine List.map_congr_left fun τ' hτ' => ?_
    rw [hkey τ' hτ']
    by_cases hl : lexLt (keyAt b' τ') (keyAt b τ) <;> simp [hl]
  rw [this, sum_map_ite_filter]
  have hkeys := keys_cmdStksP (x := ([] : List Bool)) (s := s) (M := M) hσ hHσb hRσb hHσ hRσ ℓ
  have hkeys0 := keys_cmdStksP (x := ([] : List Bool)) (s := s) (M := M) hρ hHb hRb hH hR ℓ
  have hlen : (cmdStksP M b' HX RX σ s H).length = (cmdStksP M b HX RX ρ s H).length := by
    rw [← List.length_map (f := keyAt b'), hkeys, ← hkeys0, List.length_map]
  have hj' : j < (cmdStksP M b' HX RX σ s H).length := hlen ▸ hj
  have hkj : keyAt b τ = keyAt b' (cmdStksP M b' HX RX σ s H)[j] := by
    have e1 : keyAt b τ = (keyList M s ([] : List Bool) ℓ H)[j]'(by rw [← hkeys0, List.length_map]; exact hj) := by
      simp only [hτ, ← hkeys0, List.getElem_map]
    have e2 : keyAt b' (cmdStksP M b' HX RX σ s H)[j] =
        (keyList M s ([] : List Bool) ℓ H)[j]'(by rw [← hkeys, List.length_map]; exact hj') := by
      simp only [← hkeys, List.getElem_map]
    rw [e1, e2]
  rw [hkj, filter_lexLt_eq_take (keyAt b') _ (by
    rw [← List.pairwise_map (f := keyAt b') (R := fun p q => lexLt p q = true), hkeys]
    exact keyList_pairwise') j hj']

end Lax119563Proofs.Reduction
