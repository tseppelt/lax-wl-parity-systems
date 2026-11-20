import Lax119563Proofs.Reduction.PkStk
import Lax119563Proofs.Reduction.SchFinal

/-!
# The schema enumerator for a runtime number of blocks

`schEnumP M b SX HX RX NX rX p0X EcX body` runs `body` once for every schema of the compiled
code-ordered time program, on the stacks `schStksP` (`out_schEnumP`): each has length `b + 37`,
carries its index at level `b + 27` and the record `SchRec` of the schema from `b + 28` on
(the blocks of `Reduction/SchGen`, the stacks of `Reduction/SchOut`, `Reduction/SchFinal`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

variable {M : Machine} {s : ℕ}

section Gens

variable (M)

/-- The body of the command enumerator: count `j` (level `b + 25`) and `e₀` (level
`b + 26`), then run `body` for the schemas of the command. -/
def cmdBodyP (b : ℕ) (SX HX RX NX : Xp) (body : Gn) : Gn :=
  .count (cmdEnumP M (b + 26) SX HX RX (Gn.when (beforeX b (b + 26)) (.emit (const 0))))
    (.count (cmdEnumP M (b + 27) SX HX RX (Gn.when (beforeX b (b + 27))
        (.ite (var (b + 27 + 17)) (Gn.emitN 9) (Gn.emitN 4))))
      (.ite (var (b + 17)) (Gn.blkGen (var (b + 26)) (gdX b) body (forkBlk NX b))
        (Gn.blkGen (var (b + 26)) (gdX b) body (assignBlk NX b))))

/-- **The schema enumerator** for a runtime number of blocks. -/
def schEnumP (b : ℕ) (SX HX RX NX rX p0X EcX : Xp) (body : Gn) : Gn :=
  .seq (cmdEnumP M b SX HX RX (cmdBodyP M b SX HX RX NX body)) (detGen NX rX p0X EcX body)

end Gens

variable (M s) in
/-- The stacks of all schemas. -/
noncomputable def schStksP (b : ℕ) (HX RX NX rX p0X EcX : Xp) (x : List Bool) (ρ : List ℕ)
    (ℓ H : ℕ) : List (List ℕ) :=
  (cmdStksP M b HX RX ρ s H).zipIdx.flatMap (fun p =>
    cmdSchStks NX b p.1 p.2 (e0Of (M := M) (s := s) x ℓ H p.2)) ++ detStks NX rX p0X EcX ρ

section Out

variable {x y : List Bool} {ρ : List ℕ} {b H ℓ : ℕ} {SX HX RX NX rX p0X EcX : Xp}
  (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hSb : SX.Bnd b) (hH : HX.eval ρ = H)
  (hR : RX.eval ρ = radix M H) (hS : SX.eval ρ = s) (hs : 1 ≤ s)
include hρ hHb hRb hH hR

lemma length_cmdStksP_eq {b' : ℕ} {σ : List ℕ} (hσ : σ.length = b') (hσρ : σ.take b = ρ)
    (hb' : b ≤ b') (ℓ : ℕ) :
    (cmdStksP M b' HX RX σ s H).length = (cmdStksP M b HX RX ρ s H).length := by
  have hσsplit : σ = ρ ++ σ.drop b := by rw [← hσρ, List.take_append_drop]
  have hHσ : HX.eval σ = H := by rw [hσsplit]; exact (Xp.eval_append hρ _ hHb).trans hH
  have hRσ : RX.eval σ = radix M H := by rw [hσsplit]; exact (Xp.eval_append hρ _ hRb).trans hR
  rw [(cmdStksP_forall₂ (x := ([] : List Bool)) (s := s) hσ (Xp.Bnd.mono hb' hHb) (Xp.Bnd.mono hb' hRb) hHσ hRσ
    ℓ).length_eq, (cmdStksP_forall₂ (x := ([] : List Bool)) (s := s) hρ hHb hRb hH hR ℓ).length_eq]

include hSb hS hs

/-- **The body of the command enumerator.** -/
theorem out_cmdBodyP (hNb : NX.Bnd b) (ℓ : ℕ) (body : Gn) {j : ℕ}
    (hj : j < (cmdStksP M b HX RX ρ s H).length) :
    (cmdBodyP M b SX HX RX NX body).out y (cmdStksP M b HX RX ρ s H)[j] =
      (cmdSchStks NX b (cmdStksP M b HX RX ρ s H)[j] j
        (e0Of (M := M) (s := s) x ℓ H j)).flatMap (body.out y) := by
  set C := cmdStksP M b HX RX ρ s H with hC
  set τ := C[j] with hτ
  have hF := cmdStksP_forall₂ (x := x) (s := s) hρ hHb hRb hH hR ℓ
  have hrel : StkCmd x s ℓ H b ρ τ ((verifierCmds' M x s ℓ H)[j]'(hF.length_eq ▸ hj)) :=
    List.forall₂_iff_get.mp hF |>.2 j hj _
  obtain ⟨hτl, hτρ, -, -⟩ := hrel
  -- the count of `j`
  have h1 : ((cmdEnumP M (b + 26) SX HX RX (Gn.when (beforeX b (b + 26))
      (.emit (const 0)))).out y (τ ++ [0])).length = j := by
    rw [length_out_beforeP ℓ hρ hHb hRb hSb hH hR hS hs (by omega) (by simp [hτl])
      (by rw [List.take_append_of_le_length (by omega), hτρ]) hj
      (by rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)])]
    have hl := length_cmdStksP_eq (s := s) hρ hHb hRb hH hR (b' := b + 26)
      (σ := τ ++ [0]) (by simp [hτl])
      (by rw [List.take_append_of_le_length (by omega), hτρ]) (by omega) ℓ
    simp only [Gn.out, List.length_singleton, List.map_const', List.sum_replicate, smul_eq_mul,
      mul_one, List.length_take]
    omega
  -- the count of `e₀`
  have h2 : ((cmdEnumP M (b + 27) SX HX RX (Gn.when (beforeX b (b + 27))
      (.ite (var (b + 27 + 17)) (Gn.emitN 9) (Gn.emitN 4)))).out y (τ ++ [j, 0])).length =
      e0Of (M := M) (s := s) x ℓ H j := by
    have hσl : (τ ++ [j, 0]).length = b + 27 := by simp [hτl]
    have hσρ : (τ ++ [j, 0]).take b = ρ := by
      rw [List.take_append_of_le_length (by omega), hτρ]
    rw [length_out_beforeP ℓ hρ hHb hRb hSb hH hR hS hs (by omega) hσl hσρ hj
      (by rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)])]
    have hσsplit : τ ++ [j, 0] = ρ ++ (τ ++ [j, 0]).drop b := by
      rw [← hσρ, List.take_append_drop]
    have hHσ : HX.eval (τ ++ [j, 0]) = H := by
      rw [hσsplit]; exact (Xp.eval_append hρ _ hHb).trans hH
    have hRσ : RX.eval (τ ++ [j, 0]) = radix M H := by
      rw [hσsplit]; exact (Xp.eval_append hρ _ hRb).trans hR
    have hF2 := cmdStksP_forall₂ (x := x) (s := s) hσl (Xp.Bnd.mono (by omega) hHb)
      (Xp.Bnd.mono (by omega) hRb) hHσ hRσ ℓ
    rw [e0Of]
    refine congrArg List.sum (forall₂_map_eq (R := StkCmd x s ℓ H (b + 27) (τ ++ [j, 0]))
      (fun τ' cmd h => ?_) (List.forall₂_take j hF2))
    have := szAt_of_stkCmd h
    simp only [szAt] at this
    simp only [Gn.out]
    split_ifs with hc
    · rw [Gn.length_out_emitN]; simp only [Xp.eval_var] at hc; rw [if_pos hc] at this; exact this
    · rw [Gn.length_out_emitN]; simp only [Xp.eval_var] at hc
      rw [if_neg (by simpa using hc)] at this; exact this
  simp only [cmdBodyP, Gn.out]
  rw [h1, show τ ++ [j] ++ [0] = τ ++ [j, 0] by simp, h2,
    show τ ++ [j] ++ [e0Of (M := M) (s := s) x ℓ H j] = τ ++ [j, e0Of (M := M) (s := s) x ℓ H j]
      by simp]
  have hlen : (τ ++ [j, e0Of (M := M) (s := s) x ℓ H j]).length = b + 27 := by simp [hτl]
  have e17 : (var (b + 17)).eval (τ ++ [j, e0Of (M := M) (s := s) x ℓ H j]) =
      τ.getD (b + 17) 0 := by
    simp only [Xp.eval_var]; exact List.getD_append _ _ _ _ (by omega)
  rw [e17, cmdSchStks]
  have e26 : (var (b + 26)).eval (τ ++ [j, e0Of (M := M) (s := s) x ℓ H j]) =
      e0Of (M := M) (s := s) x ℓ H j := by
    simp only [Xp.eval_var]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hτl]
  split_ifs with hc
  · rw [Gn.out_blkGen hlen _ _ _ _ (bnd_var (show b + 26 < b + 27 by omega)) (bnd_gdX (by omega))
      (bnd_forkBlk hNb (by omega)), e26]
  · rw [Gn.out_blkGen hlen _ _ _ _ (bnd_var (show b + 26 < b + 27 by omega)) (bnd_gdX (by omega))
      (bnd_assignBlk hNb (by omega)), e26]

/-- **The output of the schema enumerator, by stacks.** -/
theorem out_schEnumP_stks (hNb : NX.Bnd b) (hrb : rX.Bnd b) (hpb : p0X.Bnd b)
    (hEb : EcX.Bnd b) (ℓ : ℕ) (body : Gn) :
    (schEnumP M b SX HX RX NX rX p0X EcX body).out y ρ =
      (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).flatMap (body.out y) := by
  rw [schEnumP, Gn.out, out_cmdEnumP' hρ hHb hRb hH hR _ hSb hS hs,
    out_detGen hρ hNb hrb hpb hEb, schStksP, List.flatMap_append, List.flatMap_assoc]
  congr 1
  conv_lhs => rw [← map_fst_zipIdx' (cmdStksP M b HX RX ρ s H) 0, List.flatMap_map]
  refine List.flatMap_congr fun p hp => ?_
  have h := List.mem_zipIdx_iff_getElem?.mp hp
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp h
  rw [← hget]
  exact out_cmdBodyP hρ hHb hRb hSb hH hR hS hs hNb ℓ body hj

end Out

section Main

variable {x y : List Bool} {ρ : List ℕ} {b H ℓ : ℕ} {SX HX RX NX rX p0X EcX : Xp}
  (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
  (hR : RX.eval ρ = radix M H)
  (hNb : NX.Bnd b) (hN : NX.eval ρ = numLoc M H)
  (hrb : rX.Bnd b) (hr : rX.eval ρ = (verifierCmds' M x s ℓ H).length)
  (hpb : p0X.Bnd b) (hp : p0X.eval ρ = (Loc.code (Loc.query : Loc M H)).val)
  (hEb : EcX.Bnd b) (hE : EcX.eval ρ = ((verifierCmds' M x s ℓ H).map cmdSz).sum)
include hρ hHb hRb hH hR hNb hN hrb hr hpb hp hEb hE

lemma schStksP_forall₂ :
    List.Forall₂ (fun sc τ => τ.length = b + 37 ∧ τ.take b = ρ ∧
        SchRec M x s ℓ H sc (τ.drop (b + 28)))
      ((AP (ℓ := ℓ) (N := numLoc M H) Loc.code Loc.accept Loc.reject code_accept_ne_reject
        (verifierCmds' M x s ℓ H)).compiledSchemas (Loc.query : Loc M H).code (fun _ _ => 0))
      (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H) := by
  have hm := schemas_match (ℓ := ℓ) (Loc.code (M := M) (H := H)) Loc.accept Loc.reject
    code_accept_ne_reject (verifierCmds' M x s ℓ H) (Loc.query : Loc M H).code (fun _ _ => 0)
  refine (forall₂_comp hm (S := StkSch M x s ℓ H b ρ) ?_).imp ?_
  · rw [schStksP]
    refine List.rel_append (forall₂_flatMap ?_) ?_
    · have hF := forall₂_flip' (forall₂_mem_right
        (cmdStksP_forall₂ (x := x) (s := s) hρ hHb hRb hH hR ℓ))
      refine (forall₂_zipIdx_both hF 0).imp ?_
      rintro ⟨cmd, j⟩ ⟨τ, j'⟩ ⟨⟨hrel, hmem⟩, hjj⟩
      simp only at hjj
      subst hjj
      exact cmd_forall₂ hρ hNb hN hrel hmem j _
    · rw [detStks, queryGuard_zero]
      refine forall₂_stks (σ := ρ ++ List.replicate 27 0) (σ' := ρ) (by simp [hρ])
        (by simp [← hρ]) (g := fun _ v => decide (v = 0)) (gd := [3, 0, 0, 0])
        (Or.inr ⟨rfl, rfl⟩) rfl rfl
        (gadgetX p0X (const 0) (detX NX rX 0) (detX NX rX 1) (detX NX rX 2) (detX NX rX 3))
        (detN (N := numLoc M H) (verifierCmds' M x s ℓ H).length
          (Loc.code (Loc.query : Loc M H)).val) ?_ (EcX.eval ρ)
      rw [eval_gadgetX, detN]
      simp only [detX, Xp.eval_add, Xp.eval_mulC, Xp.eval_const, hN, hr, hp]
      rw [Nat.mul_comm 8]
  rintro sc τ ⟨⟨D, n⟩, hM, hl, ht, g, gd, hg, hD, hdrop⟩
  exact ⟨hl, ht, by rw [hdrop]; exact schRec_of hM hD hg⟩

lemma schStksP_idx :
    (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).map (·.getD (b + 27) 0) =
      List.range (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).length := by
  set lens := (verifierCmds' M x s ℓ H).map cmdSz with hlens
  have hF := cmdStksP_forall₂ (x := x) (s := s) hρ hHb hRb hH hR ℓ
  have hC : (cmdStksP M b HX RX ρ s H).map (szAt b) = lens :=
    forall₂_map_eq (fun τ cmd h => szAt_of_stkCmd h) hF
  have hblk : ∀ p ∈ (cmdStksP M b HX RX ρ s H).zipIdx,
      (cmdSchStks NX b p.1 p.2 (e0Of (M := M) (s := s) x ℓ H p.2)).map (·.getD (b + 27) 0) =
        (List.range (szAt b p.1)).map ((lens.take p.2).sum + ·) := by
    intro p hp
    have hm : p.1 ∈ cmdStksP M b HX RX ρ s H :=
      List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
    obtain ⟨cmd, -, hrel⟩ := forall₂_exists_of_mem_left hF hm
    have hσ : (p.1 ++ [p.2, e0Of (M := M) (s := s) x ℓ H p.2]).length = b + 27 := by
      simp [hrel.1]
    have he0 : e0Of (M := M) (s := s) x ℓ H p.2 = (lens.take p.2).sum := by
      rw [e0Of, hlens, List.map_take]
    rw [cmdSchStks, map_getD_blk hσ, he0]
    unfold szAt
    split_ifs <;> rfl
  have hb := flatMap_blocks lens 0
  simp only [zero_add] at hb
  have hdet : (detStks NX rX p0X EcX ρ).map (·.getD (b + 27) 0) =
      (List.range 4).map (lens.sum + ·) := by
    rw [detStks, map_getD_blk (σ := ρ ++ List.replicate 27 0) (n := b + 27) (by simp [hρ]), hE]
    rfl
  have hmap : (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).map (·.getD (b + 27) 0) =
      List.range (lens.sum + 4) := by
    rw [schStksP, List.map_append, List.map_flatMap, List.flatMap_congr hblk, hdet]
    have : ((cmdStksP M b HX RX ρ s H).zipIdx.flatMap fun p =>
        (List.range (szAt b p.1)).map ((lens.take p.2).sum + ·)) =
        ((cmdStksP M b HX RX ρ s H).map (szAt b)).zipIdx.flatMap fun p =>
          (List.range p.1).map ((lens.take p.2).sum + ·) := by
      rw [List.zipIdx_map, List.flatMap_map]; rfl
    rw [this, hC, hb, List.range_add, List.map_id']
  have hlen := congrArg List.length hmap
  simp only [List.length_map, List.length_range] at hlen
  rw [hmap, hlen]

/-- **The schema enumerator** for a runtime number of blocks. -/
theorem out_schEnumP (hSb : SX.Bnd b) (hS : SX.eval ρ = s) (hs : 1 ≤ s) (body : Gn) :
    List.Forall₂ (fun sc τ => τ.length = b + 37 ∧ τ.take b = ρ ∧
        SchRec M x s ℓ H sc (τ.drop (b + 28)))
      ((AP (ℓ := ℓ) (N := numLoc M H) Loc.code Loc.accept Loc.reject code_accept_ne_reject
        (verifierCmds' M x s ℓ H)).compiledSchemas (Loc.query : Loc M H).code (fun _ _ => 0))
      (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H) ∧
    (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).map (·.getD (b + 27) 0) =
      List.range (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).length ∧
    (schEnumP M b SX HX RX NX rX p0X EcX body).out y ρ =
      (schStksP M s b HX RX NX rX p0X EcX x ρ ℓ H).flatMap (body.out y) :=
  ⟨schStksP_forall₂ hρ hHb hRb hH hR hNb hN hrb hr hpb hp hEb hE,
    schStksP_idx hρ hHb hRb hH hR hNb hN hrb hr hpb hp hEb hE,
    out_schEnumP_stks hρ hHb hRb hSb hH hR hS hs hNb hrb hpb hEb ℓ body⟩

end Main

end Lax119563Proofs.Reduction
