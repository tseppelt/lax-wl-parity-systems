import Lax119563Proofs.Reduction.SchOut

/-!
# The schema enumerator: correctness

`out_schEnum`: for the compiled code-ordered time program `I` (with `ℓ, H` arbitrary), the
schema enumerator runs its body on the stacks `schStks`, which correspond to the schemas of
`I` in order: each has length `b + 37`, extends the globals `ρ`, has its index at level
`b + 27` and a record describing the schema (`SchRec`) from level `b + 28` on.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

variable {M : Machine} {s : ℕ}

lemma forall₂_flip' {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → List.Forall₂ (fun b a => R a b) l' l
  | [], [], List.Forall₂.nil => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t => List.Forall₂.cons h (forall₂_flip' t)

lemma src_ne_of_mem {x : List Bool} {ℓ H : ℕ} {cmd : ACmd (Loc M H) s}
    (h : cmd ∈ verifierCmds' M x s ℓ H) : cmd.src ≠ Loc.accept ∧ cmd.src ≠ Loc.reject := by
  unfold verifierCmds' progCmds at h
  obtain ⟨L, -, hL⟩ := List.mem_flatMap.mp h
  obtain ⟨mv, hmv, rfl⟩ := List.mem_map.mp hL
  rw [src_toACmd]
  constructor <;> rintro rfl <;> simp [moves] at hmv

lemma regVal_zero (ℓ : ℕ) : regVal (0 : BlockCoord ℓ) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp [regVal, testBit_ofBits]

lemma queryGuard_zero (s ℓ : ℕ) :
    RegisterProgram.queryGuard (fun _ _ => 0 : Fin s → Fin ℓ → ZMod 2) =
      toGuard (fun _ v => decide (v = 0)) := by
  unfold RegisterProgram.queryGuard toGuard
  congr 1
  funext i
  ext b
  simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq]
  constructor
  · rintro rfl; exact regVal_zero ℓ
  · intro h
    apply regVal_injective
    rw [h]
    exact (regVal_zero ℓ).symm

section Final

variable {x : List Bool} {ρ : List ℕ} {b H ℓ : ℕ} {HX RX NX rX p0X EcX : Xp}

/-- The relation between a schema description `(domain, numbers)` and a stack. -/
def StkSch (M : Machine) (x : List Bool) (s ℓ H b : ℕ) (ρ : List ℕ)
    (Dn : Finset (Coord (s + 1) ℓ) × SchNum) (τ : List ℕ) : Prop :=
  τ.length = b + 37 ∧ τ.take b = ρ ∧ ∃ g gd, GDescQ M x s ℓ H g gd ∧
    Dn.1 = guardDomain (toGuard g) true ∧ τ.drop (b + 28) = Dn.2.toL ++ gd

lemma stkSch_of {σ : List ℕ} (hσ : σ.length = b + 27) (hσρ : σ.take b = ρ)
    {D : Finset (Coord (s + 1) ℓ)} {g : Fin s → ℕ → Bool} {gd : List ℕ}
    (hg : GDescQ M x s ℓ H g gd) (hD : D = guardDomain (toGuard g) true) (hgd : gd.length = 4)
    (n : SchNum) (e : ℕ) :
    StkSch M x s ℓ H b ρ (D, n) (σ ++ e :: (n.toL ++ gd)) := by
  refine ⟨by simp [hσ, hgd, SchNum.toL] <;> omega,
    by rw [List.take_append_of_le_length (by omega), hσρ], g, gd, hg, hD, ?_⟩
  rw [show σ ++ e :: (n.toL ++ gd) = (σ ++ [e]) ++ (n.toL ++ gd) by simp]
  rw [show b + 28 = (σ ++ [e]).length by simp [hσ]]
  exact List.drop_left

lemma forall₂_stks {σ σ' : List ℕ} (hσ : σ.length = b + 27) (hσρ : σ.take b = ρ)
    {D : Finset (Coord (s + 1) ℓ)} {g : Fin s → ℕ → Bool} {gd : List ℕ}
    (hg : GDescQ M x s ℓ H g gd) (hD : D = guardDomain (toGuard g) true) (hgd : gd.length = 4)
    (blk : List (List Xp)) (ns : List SchNum)
    (hns : blk.map (·.map (·.eval σ')) = ns.map SchNum.toL) (e0 : ℕ) :
    List.Forall₂ (StkSch M x s ℓ H b ρ) (ns.map (D, ·))
      (blk.zipIdx.map fun p => σ ++ (e0 + p.2) :: (p.1.map (·.eval σ') ++ gd)) := by
  have h1 : blk.zipIdx.map (fun p => σ ++ (e0 + p.2) :: (p.1.map (·.eval σ') ++ gd)) =
      (blk.map (·.map (·.eval σ'))).zipIdx.map fun p => σ ++ (e0 + p.2) :: (p.1 ++ gd) := by
    rw [List.zipIdx_map, List.map_map]; rfl
  rw [h1, hns, List.zipIdx_map, List.map_map, List.forall₂_map_left_iff,
    List.forall₂_map_right_iff]
  exact forall₂_self_zipIdx (fun n i => stkSch_of hσ hσρ hg hD hgd n (e0 + i)) ns 0

lemma executable_src {cmd : ACmd (Loc M H) s} (h : cmd ∈ verifierCmds' M x s ℓ H) :
    (AP (ℓ := ℓ) (N := numLoc M H) Loc.code Loc.accept Loc.reject code_accept_ne_reject
      (verifierCmds' M x s ℓ H)).executable (Loc.code cmd.src) = true := by
  obtain ⟨h1, h2⟩ := src_ne_of_mem h
  simp only [RegisterProgram.executable, decide_eq_true_eq]
  exact ⟨fun h' => h1 (Loc.code_injective h'), fun h' => h2 (Loc.code_injective h')⟩

variable (hρ : ρ.length = b)
include hρ

/-- The schemas of one command. -/
lemma cmd_forall₂ (hNb : NX.Bnd b) (hN : NX.eval ρ = numLoc M H) {τ : List ℕ}
    {cmd : ACmd (Loc M H) s} (hrel : StkCmd x s ℓ H b ρ τ cmd)
    (hmem : cmd ∈ verifierCmds' M x s ℓ H) (j e0 : ℕ) :
    List.Forall₂ (StkSch M x s ℓ H b ρ)
      ((cmdN (Loc.code (M := M) (H := H)) j cmd).map fun n =>
        (cmdDom (ℓ := ℓ) Loc.code Loc.accept Loc.reject code_accept_ne_reject
          (verifierCmds' M x s ℓ H) cmd, n))
      (cmdSchStks NX b τ j e0) := by
  obtain ⟨hτl, hτρ, hsrc, hd⟩ := hrel
  set σ := τ ++ [j, e0] with hσdef
  have hσl : σ.length = b + 27 := by simp [hσdef, hτl]
  have hσρ : σ.take b = ρ := by rw [hσdef, List.take_append_of_le_length (by omega), hτρ]
  have evr : ∀ i < 8, (var (b + 17 + i)).eval σ = (τ.drop (b + 17)).getD i 0 := fun i hi => by
    rw [getD_drop']; simp only [Xp.eval_var, hσdef]
    exact List.getD_append _ _ _ _ (by omega)
  have ev15 : (var (b + 15)).eval σ = τ.getD (b + 15) 0 := by
    simp only [Xp.eval_var, hσdef]; exact List.getD_append _ _ _ _ (by omega)
  have ev25 : (var (b + 25)).eval σ = j := by
    simp only [Xp.eval_var, hσdef]
    rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hτl]
  have evN : NX.eval σ = numLoc M H := by
    rw [show σ = ρ ++ σ.drop b by rw [← hσρ, List.take_append_drop]]
    exact (Xp.eval_append hρ _ hNb).trans hN
  have evS : ∀ t, (slotX NX b t).eval σ = numLoc M H + (t + 8 * j) := fun t => by
    simp [slotX, evN, ev25]
  set r := τ.drop (b + 17) with hr
  have hrl : r.length = 8 := CmdDesc.length hd
  have hgd : (gdX b).map (·.eval σ) = r.drop 4 := by
    rw [eq_of_length_four (l := r.drop 4) (by simp [hrl])]
    simp only [gdX, List.map_cons, List.map_nil, getD_drop']
    rw [show b + 21 = b + 17 + 4 by omega, show b + 22 = b + 17 + 5 by omega,
      show b + 23 = b + 17 + 6 by omega, show b + 24 = b + 17 + 7 by omega,
      evr 4 (by omega), evr 5 (by omega), evr 6 (by omega), evr 7 (by omega)]
  have h17 : τ.getD (b + 17) 0 = r.getD 0 0 := by rw [hr, getD_drop']
  unfold cmdSchStks
  rw [← hσdef, hgd]
  have hgdl : (r.drop 4).length = 4 := by simp [hrl]
  clear_value σ r
  cases cmd with
  | assign p g m q =>
    obtain ⟨-, h0, h1, h2, hg⟩ := hd
    rw [h17, h0, if_neg (by simp)]
    have hD : cmdDom (ℓ := ℓ) Loc.code Loc.accept Loc.reject code_accept_ne_reject
        (verifierCmds' M x s ℓ H) (ACmd.assign p g m q) = guardDomain (toGuard g) true := by
      unfold cmdDom; rw [executable_src hmem]; rfl
    refine forall₂_stks hσl hσρ (Or.inl hg) hD hgdl _ _ ?_ e0
    rw [assignBlk, eval_gadgetX]
    simp only [cmdN, evS, ev15, hsrc]
    have e18 := evr 1 (by omega)
    have e19 := evr 2 (by omega)
    rw [show b + 17 + 1 = b + 18 by omega] at e18
    rw [show b + 17 + 2 = b + 19 by omega] at e19
    rw [e18, e19, h1, h2]
    rfl
  | fork p g q q' =>
    obtain ⟨-, h0, h2, h3, hg⟩ := hd
    rw [h17, h0, if_pos (by simp)]
    have hD : cmdDom (ℓ := ℓ) Loc.code Loc.accept Loc.reject code_accept_ne_reject
        (verifierCmds' M x s ℓ H) (ACmd.fork p g q q') = guardDomain (toGuard g) true := by
      unfold cmdDom; rw [executable_src hmem]; rfl
    refine forall₂_stks hσl hσρ (Or.inl hg) hD hgdl _ _ ?_ e0
    have e19 := evr 2 (by omega)
    have e20 := evr 3 (by omega)
    rw [show b + 17 + 2 = b + 19 by omega] at e19
    rw [show b + 17 + 3 = b + 20 by omega] at e20
    have hs : (var (b + 15)).eval σ = (Loc.code p).val := ev15.trans hsrc
    simp only [forkBlk, List.map_append, eval_gadgetX, cmdN, evS, hs, e19, e20, h2, h3]
    simp [SchNum.toL, terN, evS, hs]

end Final

lemma map_getD_blk {α : Type} {σ : List ℕ} {n : ℕ} (hσ : σ.length = n) (e0 : ℕ) (blk : List α)
    (f : α × ℕ → List ℕ) :
    (blk.zipIdx.map fun p => σ ++ (e0 + p.2) :: f p).map (·.getD n 0) =
      (List.range blk.length).map (e0 + ·) := by
  rw [List.map_map, List.range_eq_range', ← map_zipIdx_snd (e0 + ·) blk 0]
  refine List.map_congr_left fun p _ => ?_
  simp [List.getD_append_right, hσ]

section Main

variable {x : List Bool} {ρ : List ℕ} {b H ℓ : ℕ} {HX RX NX rX p0X EcX : Xp}
  (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
  (hR : RX.eval ρ = radix M H)
  (hNb : NX.Bnd b) (hN : NX.eval ρ = numLoc M H)
  (hrb : rX.Bnd b) (hr : rX.eval ρ = (verifierCmds' M x s ℓ H).length)
  (hpb : p0X.Bnd b) (hp : p0X.eval ρ = (Loc.code (Loc.query : Loc M H)).val)
  (hEb : EcX.Bnd b) (hE : EcX.eval ρ = ((verifierCmds' M x s ℓ H).map cmdSz).sum)
include hρ hHb hRb hH hR hNb hN hrb hr hpb hp hEb hE

lemma schStks_forall₂ :
    List.Forall₂ (fun sc τ => τ.length = b + 37 ∧ τ.take b = ρ ∧
        SchRec M x s ℓ H sc (τ.drop (b + 28)))
      ((AP (ℓ := ℓ) (N := numLoc M H) Loc.code Loc.accept Loc.reject code_accept_ne_reject
        (verifierCmds' M x s ℓ H)).compiledSchemas (Loc.query : Loc M H).code (fun _ _ => 0))
      (schStks M s b HX RX NX rX p0X EcX x ρ ℓ H) := by
  have hm := schemas_match (ℓ := ℓ) (Loc.code (M := M) (H := H)) Loc.accept Loc.reject
    code_accept_ne_reject (verifierCmds' M x s ℓ H) (Loc.query : Loc M H).code (fun _ _ => 0)
  refine (forall₂_comp hm (S := StkSch M x s ℓ H b ρ) ?_).imp ?_
  · rw [schStks]
    refine List.rel_append (forall₂_flatMap ?_) ?_
    · have hF := forall₂_flip' (forall₂_mem_right
        (cmdStks_forall₂ (x := x) (s := s) hρ hHb hRb hH hR ℓ))
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
        (detN (N := numLoc M H) (verifierCmds' M x s ℓ H).length (Loc.code (Loc.query : Loc M H)).val)
        ?_ (EcX.eval ρ)
      rw [eval_gadgetX, detN]
      simp only [detX, Xp.eval_add, Xp.eval_mulC, Xp.eval_const, hN, hr, hp]
      rw [Nat.mul_comm 8]
  rintro sc τ ⟨⟨D, n⟩, hM, hl, ht, g, gd, hg, hD, hdrop⟩
  exact ⟨hl, ht, by rw [hdrop]; exact schRec_of hM hD hg⟩

lemma schStks_idx :
    (schStks M s b HX RX NX rX p0X EcX x ρ ℓ H).map (·.getD (b + 27) 0) =
      List.range (schStks M s b HX RX NX rX p0X EcX x ρ ℓ H).length := by
  set lens := (verifierCmds' M x s ℓ H).map cmdSz with hlens
  have hF := cmdStks_forall₂ (x := x) (s := s) hρ hHb hRb hH hR ℓ
  have hC : (cmdStks M s b HX RX x ρ H).map (szAt b) = lens :=
    forall₂_map_eq (fun τ cmd h => szAt_of_stkCmd h) hF
  have hblk : ∀ p ∈ (cmdStks M s b HX RX x ρ H).zipIdx,
      (cmdSchStks NX b p.1 p.2 (e0Of (M := M) (s := s) x ℓ H p.2)).map (·.getD (b + 27) 0) =
        (List.range (szAt b p.1)).map ((lens.take p.2).sum + ·) := by
    intro p hp
    have hm : p.1 ∈ cmdStks M s b HX RX x ρ H :=
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
  have hmap : (schStks M s b HX RX NX rX p0X EcX x ρ ℓ H).map (·.getD (b + 27) 0) =
      List.range (lens.sum + 4) := by
    rw [schStks, List.map_append, List.map_flatMap, List.flatMap_congr hblk, hdet]
    have : ((cmdStks M s b HX RX x ρ H).zipIdx.flatMap fun p =>
        (List.range (szAt b p.1)).map ((lens.take p.2).sum + ·)) =
        ((cmdStks M s b HX RX x ρ H).map (szAt b)).zipIdx.flatMap fun p =>
          (List.range p.1).map ((lens.take p.2).sum + ·) := by
      rw [List.zipIdx_map, List.flatMap_map]; rfl
    rw [this, hC, hb, List.range_add, List.map_id']
  have hlen := congrArg List.length hmap
  simp only [List.length_map, List.length_range] at hlen
  rw [hmap, hlen]

/-- **The schema enumerator.** It runs `body` on the stacks `schStks`, which correspond to the
schemas of the compiled code-ordered time program (`SchRec` from level `b + 28` on), carry
their index at level `b + 27`, have length `b + 37` and extend `ρ`. -/
theorem out_schEnum (body : Gn) :
    List.Forall₂ (fun sc τ => τ.length = b + 37 ∧ τ.take b = ρ ∧
        SchRec M x s ℓ H sc (τ.drop (b + 28)))
      ((AP (ℓ := ℓ) (N := numLoc M H) Loc.code Loc.accept Loc.reject code_accept_ne_reject
        (verifierCmds' M x s ℓ H)).compiledSchemas (Loc.query : Loc M H).code (fun _ _ => 0))
      (schStks M s b HX RX NX rX p0X EcX x ρ ℓ H) ∧
    (schStks M s b HX RX NX rX p0X EcX x ρ ℓ H).map (·.getD (b + 27) 0) =
      List.range (schStks M s b HX RX NX rX p0X EcX x ρ ℓ H).length ∧
    (schEnum M s b HX RX NX rX p0X EcX body).out x ρ =
      (schStks M s b HX RX NX rX p0X EcX x ρ ℓ H).flatMap (body.out x) :=
  ⟨schStks_forall₂ hρ hHb hRb hH hR hNb hN hrb hr hpb hp hEb hE,
    schStks_idx hρ hHb hRb hH hR hNb hN hrb hr hpb hp hEb hE,
    out_schEnum_stks hρ hHb hRb hH hR hNb hrb hpb hEb ℓ body⟩

end Main

end Lax119563Proofs.Reduction
