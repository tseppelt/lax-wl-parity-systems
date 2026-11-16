import Lax119563Proofs.Reduction.SchEnum
import Lax119563Proofs.Reduction.SchList

/-!
# The stacks of the command enumerator

`cmdStks`: the stacks on which the body of `cmdEnum` runs, one per command, in order
(`out_cmdEnum'`: the output is `cmdStks.flatMap body.out`). They correspond to the commands
of `verifierCmds'` (`cmdStks_forall₂`, relation `StkCmd`: length `b + 25`, prefix `ρ`,
source number at level `b + 15`, `CmdDesc` of the levels from `b + 17` on), and their keys
(levels `b + 15, b + 16`) are the list `keyList` (independent of `b` and `ρ`), which strictly
increases.

`length_out_before`: the length of the output of a nested enumerator whose body is
`when (beforeX b b') g` (key smaller than the key of the outer stack) is a sum over the
first `j` stacks, `j` being the index of the outer stack.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp

variable {M : Machine} {s : ℕ}

section Defs

variable (M s)

/-- The stacks on which the body of the command enumerator runs, in order. -/
noncomputable def cmdStks (b : ℕ) (HX RX : Xp) (x : List Bool) (ρ : List ℕ) (H : ℕ) :
    List (List ℕ) :=
  (List.range (numLoc M H)).flatMap fun c =>
    match decodeLoc M H c with
    | some L => (recsOf M s b HX RX x ρ H L).map (stkL M ρ H L ++ ·)
    | none => []

/-- The keys `(location number, move index)` of the commands. -/
noncomputable def keyList (x : List Bool) (ℓ H : ℕ) : List (ℕ × ℕ) :=
  (List.range (numLoc M H)).flatMap fun c =>
    match decodeLoc M H c with
    | some L => (List.range (moves M x s ℓ H L).length).map ((Loc.code L).val, ·)
    | none => []

end Defs

/-- The key of a stack of the enumerator at base `b`. -/
def keyAt (b : ℕ) (τ : List ℕ) : ℕ × ℕ := (τ.getD (b + 15) 0, τ.getD (b + 16) 0)

lemma CmdDesc.length {x : List Bool} {ℓ H : ℕ} {cmd : ACmd (Loc M H) s} {r : List ℕ}
    (h : CmdDesc M x s ℓ H cmd r) : r.length = 8 := by
  cases cmd <;> exact h.1

lemma src_toACmd {L : Type} {ℓ : ℕ} (src : L) (mv : Move L s) : (mv.toACmd ℓ src).src = src := by
  cases mv <;> rfl

lemma forall₂_zipIdx {α β : Type} {P : α → β → Prop} :
    ∀ {l : List α} {rs : List β}, List.Forall₂ P l rs → ∀ k,
      List.Forall₂ (fun p a => P a p.1) (rs.zipIdx k) l
  | [], [], List.Forall₂.nil, _ => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t, k => by
    rw [List.zipIdx_cons]
    exact List.Forall₂.cons h (forall₂_zipIdx t (k + 1))

lemma map_zipIdx_snd {α β : Type} (f : ℕ → β) :
    ∀ (l : List α) (k : ℕ), (l.zipIdx k).map (fun p => f p.2) = (List.range' k l.length).map f
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, map_zipIdx_snd f l (k + 1)]
    simp [List.range'_succ]

lemma sum_map_ite_filter {α : Type} (p : α → Bool) (f : α → ℕ) (l : List α) :
    (l.map fun a => if p a then f a else 0).sum = ((l.filter p).map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a <;> simp [List.filter_cons, h, ih]

/-- With strictly increasing keys, the entries with a key below that of entry `i` are the
first `i` entries. -/
lemma filter_lexLt_eq_take {α : Type} (key : α → ℕ × ℕ) :
    ∀ (l : List α), l.Pairwise (fun a b => lexLt (key a) (key b) = true) →
      ∀ (i : ℕ) (hi : i < l.length),
        l.filter (fun a => lexLt (key a) (key l[i])) = l.take i
  | [], _, i, hi => by simp at hi
  | a :: l, h, i, hi => by
    rw [List.pairwise_cons] at h
    rcases i with _ | i
    · simp only [List.getElem_cons_zero, List.filter_cons, lexLt_irrefl, Bool.false_eq_true,
        if_false, List.take_zero]
      rw [List.filter_eq_nil_iff]
      intro b hb hlt
      rw [lexLt_asymm (h.1 b hb)] at hlt
      exact absurd hlt (by simp)
    · have hi' : i < l.length := by simpa using hi
      simp only [List.getElem_cons_succ, List.filter_cons, List.take_succ_cons]
      rw [if_pos (h.1 _ (List.getElem_mem hi')), filter_lexLt_eq_take key l h.2 i hi']

lemma forall₂_exists_of_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {a : α}, a ∈ l → ∃ b ∈ l', R a b
  | [], [], List.Forall₂.nil, _, h => by simp at h
  | _ :: _, _ :: _, List.Forall₂.cons h t, _, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_exists_of_mem_left t ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

lemma getD_take' {l : List ℕ} {i n : ℕ} (h : i < n) : (l.take n).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

section Stacks

variable {x : List Bool} {ρ : List ℕ} {b H : ℕ} {HX RX : Xp}

lemma length_stkL (hρ : ρ.length = b) (L : Loc M H) : (stkL M ρ H L).length = b + 16 := by
  simp [stkL, stkT, hρ]

lemma getD_stkL_code (hρ : ρ.length = b) (L : Loc M H) (l : List ℕ) :
    (stkL M ρ H L ++ l).getD (b + 15) 0 = (Loc.code L).val := by
  rw [List.getD_append _ _ _ _ (by rw [length_stkL hρ]; omega)]
  simp [stkL, stkT, List.getD_append_right, hρ]

lemma getD_stkL_succ (hρ : ρ.length = b) (L : Loc M H) (k : ℕ) (r : List ℕ) (i : ℕ) :
    (stkL M ρ H L ++ k :: r).getD (b + 16 + i) 0 = (k :: r).getD i 0 := by
  rw [List.getD_append_right _ _ _ _ (by rw [length_stkL hρ]; omega), length_stkL hρ]
  congr 1; omega

lemma getD_stkL_head (hρ : ρ.length = b) (L : Loc M H) (r : List ℕ) :
    (stkL M ρ H L ++ r).getD (b + 16) 0 = r.headD 0 := by
  rw [List.getD_append_right _ _ _ _ (by rw [length_stkL hρ]), length_stkL hρ]
  cases r <;> simp

lemma take_stkL (hρ : ρ.length = b) (L : Loc M H) (l : List ℕ) :
    (stkL M ρ H L ++ l).take b = ρ := by
  simp [stkL, stkT, ← hρ]

lemma drop_stkL (hρ : ρ.length = b) (L : Loc M H) (k : ℕ) (r : List ℕ) :
    (stkL M ρ H L ++ k :: r).drop (b + 17) = r := by
  rw [show stkL M ρ H L ++ k :: r = (stkL M ρ H L ++ [k]) ++ r by simp]
  rw [show b + 17 = (stkL M ρ H L ++ [k]).length by simp [length_stkL hρ]]
  exact List.drop_left

variable (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
  (hR : RX.eval ρ = radix M H)
include hρ hHb hRb hH hR

/-- **The output of the command enumerator, by stacks.** -/
theorem out_cmdEnum' (body : Gn) :
    (cmdEnum M s b HX RX body).out x ρ = (cmdStks M s b HX RX x ρ H).flatMap (body.out x) := by
  rw [out_cmdEnum hρ hHb hRb hH hR, cmdStks, List.flatMap_assoc]
  refine List.flatMap_congr fun c _ => ?_
  cases decodeLoc M H c with
  | none => rfl
  | some L => simp [List.flatMap_map]

/-- The stack `τ` of the enumerator belongs to the command `cmd`. -/
def StkCmd (x : List Bool) (s ℓ H b : ℕ) (ρ : List ℕ) (τ : List ℕ) (cmd : ACmd (Loc M H) s) :
    Prop :=
  τ.length = b + 25 ∧ τ.take b = ρ ∧ τ.getD (b + 15) 0 = (Loc.code cmd.src).val ∧
    CmdDesc M x s ℓ H cmd (τ.drop (b + 17))

omit hR in
lemma block_desc (hR : RX.eval ρ = radix M H) (ℓ : ℕ) (L : Loc M H) :
    ∃ rs : List (List ℕ), recsOf M s b HX RX x ρ H L = rs.zipIdx.map (fun p => p.2 :: p.1) ∧
      List.Forall₂ (fun mv r => CmdDesc M x s ℓ H (Move.toACmd ℓ L mv) r)
        (moves M x s ℓ H L) rs :=
  desc_recsOf hρ hHb hRb hH hR ℓ L

/-- **The stacks belong to the commands, in order.** -/
theorem cmdStks_forall₂ (ℓ : ℕ) :
    List.Forall₂ (StkCmd x s ℓ H b ρ) (cmdStks M s b HX RX x ρ H) (verifierCmds' M x s ℓ H) := by
  rw [verifierCmds'_eq, cmdStks]
  refine forall₂_flatMap (List.forall₂_same.mpr fun c _ => ?_)
  cases decodeLoc M H c with
  | none => exact List.Forall₂.nil
  | some L =>
    simp only
    obtain ⟨rs, hrs, hF⟩ := block_desc hρ hHb hRb hH hR ℓ L
    rw [hrs, List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine (forall₂_zipIdx hF 0).imp fun {p mv} h => ?_
    refine ⟨?_, take_stkL hρ L _, ?_, ?_⟩
    · simp [length_stkL hρ, CmdDesc.length h] <;> omega
    · simp only [Function.comp, src_toACmd]; exact getD_stkL_code hρ L _
    · simp only [Function.comp]; rw [drop_stkL hρ]; exact h

/-- **The keys of the stacks.** -/
theorem keys_cmdStks (ℓ : ℕ) :
    (cmdStks M s b HX RX x ρ H).map (keyAt b) = keyList M s x ℓ H := by
  rw [cmdStks, keyList, List.map_flatMap]
  refine List.flatMap_congr fun c _ => ?_
  cases decodeLoc M H c with
  | none => rfl
  | some L =>
    simp only
    obtain ⟨rs, hrs, hF⟩ := block_desc hρ hHb hRb hH hR ℓ L
    rw [hrs, List.map_map, List.map_map, hF.length_eq, List.range_eq_range']
    rw [← map_zipIdx_snd (fun k => ((Loc.code L).val, k)) rs 0]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp, keyAt, getD_stkL_code hρ]
    congr 1
    have := getD_stkL_succ hρ L p.2 p.1 0
    simpa using this

theorem keyList_pairwise (ℓ : ℕ) :
    (keyList M s x ℓ H).Pairwise (fun p q => lexLt p q = true) := by
  have hk : recKeys M s b HX RX x ρ H = (cmdStks M s b HX RX x ρ H).map (keyAt b) := by
    rw [cmdStks, recKeys, List.map_flatMap]
    refine List.flatMap_congr fun c _ => ?_
    cases decodeLoc M H c with
    | none => rfl
    | some L =>
      simp only [List.map_map]
      refine List.map_congr_left fun r _ => ?_
      simp only [Function.comp, keyAt, getD_stkL_code hρ, getD_stkL_head hρ]
  rw [keys_cmdStks hρ hHb hRb hH hR ℓ] at hk
  rw [← hk]
  exact keys_pairwise hρ hHb hRb hH hR

end Stacks

/-! ## Counting the commands before a given one -/

/-- The key at base `b'` is lexicographically below the key at base `b`. -/
def beforeX (b b' : ℕ) : Xp :=
  or (lt (var (b' + 15)) (var (b + 15)))
    (and (eq (var (b' + 15)) (var (b + 15))) (lt (var (b' + 16)) (var (b + 16))))

lemma eval_beforeX (b b' : ℕ) (τ : List ℕ) :
    (beforeX b b').eval τ = if lexLt (keyAt b' τ) (keyAt b τ) then 1 else 0 := by
  have e1 : (eq (var (b' + 15)) (var (b + 15))).eval τ ≤ 1 := by
    rw [Xp.eval_eq]; split_ifs <;> omega
  have e2 : (lt (var (b' + 16)) (var (b + 16))).eval τ ≤ 1 := by
    rw [Xp.eval_lt_eq]; split_ifs <;> omega
  unfold beforeX
  rw [Xp.eval_or, Xp.eval_and e1 e2]
  simp only [Xp.eval_eq, Xp.eval_lt_eq, Xp.eval_var, keyAt, lexLt]
  by_cases h1 : τ.getD (b' + 15) 0 < τ.getD (b + 15) 0 <;>
    by_cases h2 : τ.getD (b' + 15) 0 = τ.getD (b + 15) 0 <;>
    by_cases h3 : τ.getD (b' + 16) 0 < τ.getD (b + 16) 0 <;>
    simp [h1, h2, h3] <;> omega

variable {x : List Bool} {b H : ℕ} {HX RX : Xp}

/-- **Counting before.** For a stack `σ` of length `b'` extending the `j`-th stack `τ` of
an enumerator at base `b` (prefix `ρ`), a nested enumerator with body
`when (beforeX b b') g` outputs as much as `g` on the stacks of the first `j` commands. -/
theorem length_out_before {ρ σ : List ℕ} (ℓ : ℕ) (hρ : ρ.length = b) (hHb : HX.Bnd b)
    (hRb : RX.Bnd b) (hH : HX.eval ρ = H) (hR : RX.eval ρ = radix M H)
    {b' : ℕ} (hb' : b + 25 ≤ b') (hσ : σ.length = b') (hσρ : σ.take b = ρ)
    {j : ℕ} (hj : j < (cmdStks M s b HX RX x ρ H).length)
    (hστ : σ.take (b + 25) = (cmdStks M s b HX RX x ρ H)[j]) (g : Gn) :
    ((cmdEnum M s b' HX RX (Gn.when (beforeX b b') g)).out x σ).length =
      (((cmdStks M s b' HX RX x σ H).take j).map fun τ' => (g.out x τ').length).sum := by
  have hσsplit : σ = ρ ++ σ.drop b := by rw [← hσρ, List.take_append_drop]
  have hHσ : HX.eval σ = H := by rw [hσsplit]; exact (Xp.eval_append hρ _ hHb).trans hH
  have hRσ : RX.eval σ = radix M H := by rw [hσsplit]; exact (Xp.eval_append hρ _ hRb).trans hR
  have hHσb : HX.Bnd b' := Xp.Bnd.mono (by omega) hHb
  have hRσb : RX.Bnd b' := Xp.Bnd.mono (by omega) hRb
  set τ := (cmdStks M s b HX RX x ρ H)[j] with hτ
  -- the key of the outer stack, seen from inner stacks
  have hF := cmdStks_forall₂ (x := x) (s := s) (M := M) hσ hHσb hRσb hHσ hRσ ℓ
  have hkey : ∀ τ' ∈ cmdStks M s b' HX RX x σ H, keyAt b τ' = keyAt b τ := by
    intro τ' hτ'
    obtain ⟨cmd, -, hrel⟩ := forall₂_exists_of_mem_left hF hτ'
    have h1 : τ'.take b' = σ := hrel.2.1
    have g1 : ∀ i < b + 25, τ'.getD i 0 = τ.getD i 0 := by
      intro i hi
      have hτlen : τ.length = b + 25 := by
        rw [← hστ, List.length_take, hσ]; omega
      rw [← getD_take' (n := b') (by omega), h1, ← getD_take' (n := b + 25) hi, hστ]
    simp only [keyAt, g1 (b + 15) (by omega), g1 (b + 16) (by omega)]
  rw [out_cmdEnum' hσ hHσb hRσb hHσ hRσ, List.length_flatMap]
  simp only [Gn.out_when, eval_beforeX]
  have : ((cmdStks M s b' HX RX x σ H).map fun τ' =>
      (if (if lexLt (keyAt b' τ') (keyAt b τ') = true then 1 else 0) ≠ 0 then g.out x τ'
        else []).length) =
      (cmdStks M s b' HX RX x σ H).map fun τ' =>
        if lexLt (keyAt b' τ') (keyAt b τ) then (g.out x τ').length else 0 := by
    refine List.map_congr_left fun τ' hτ' => ?_
    rw [hkey τ' hτ']
    by_cases hl : lexLt (keyAt b' τ') (keyAt b τ) <;> simp [hl]
  rw [this, sum_map_ite_filter]
  have hkeys := keys_cmdStks (x := x) (s := s) (M := M) hσ hHσb hRσb hHσ hRσ ℓ
  have hkeys0 := keys_cmdStks (x := x) (s := s) (M := M) hρ hHb hRb hH hR ℓ
  have hlen : (cmdStks M s b' HX RX x σ H).length = (cmdStks M s b HX RX x ρ H).length := by
    rw [← List.length_map (f := keyAt b'), hkeys, ← hkeys0, List.length_map]
  have hj' : j < (cmdStks M s b' HX RX x σ H).length := hlen ▸ hj
  have hkj : keyAt b τ = keyAt b' (cmdStks M s b' HX RX x σ H)[j] := by
    have e1 : keyAt b τ = (keyList M s x ℓ H)[j]'(by rw [← hkeys0, List.length_map]; exact hj) := by
      simp only [hτ, ← hkeys0, List.getElem_map]
    have e2 : keyAt b' (cmdStks M s b' HX RX x σ H)[j] =
        (keyList M s x ℓ H)[j]'(by rw [← hkeys, List.length_map]; exact hj') := by
      simp only [← hkeys, List.getElem_map]
    rw [e1, e2]
  rw [hkj, filter_lexLt_eq_take (keyAt b') _ (by
    rw [← List.pairwise_map (f := keyAt b') (R := fun p q => lexLt p q = true), hkeys]
    exact keyList_pairwise hσ hHσb hRσb hHσ hRσ ℓ) j hj']

end Lax119563Proofs.Reduction
