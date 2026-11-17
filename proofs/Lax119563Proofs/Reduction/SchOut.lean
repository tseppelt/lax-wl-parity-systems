import Lax119563Proofs.Reduction.SchGen

/-!
# The output of the schema enumerator

`out_schEnum`: the schema enumerator runs its body on the stacks `schStks`, one per schema of
the compiled code-ordered time program, in order; each extends the globals `ρ`, has length
`b + 37`, carries its index at level `b + 27` and a record describing the schema (`SchRec`)
from level `b + 28` on.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

variable {M : Machine} {s : ℕ}

/-! ## List lemmas -/

lemma getD_drop' (τ : List ℕ) (k i : ℕ) : (τ.drop k).getD i 0 = τ.getD (k + i) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {f' : β → γ}
    (hf : ∀ a b, R a b → f a = f' b) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → l.map f = l'.map f'
  | [], [], List.Forall₂.nil => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h t => by
    rw [List.map_cons, List.map_cons, hf _ _ h, forall₂_map_eq hf t]

lemma forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      List.Forall₂ (fun a b => R a b ∧ b ∈ l') l l'
  | [], [], List.Forall₂.nil => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t =>
    List.Forall₂.cons ⟨h, List.mem_cons_self⟩
      ((forall₂_mem_right t).imp fun {_ _} h' => ⟨h'.1, List.mem_cons_of_mem _ h'.2⟩)

lemma forall₂_zipIdx_both {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ k,
      List.Forall₂ (fun p q => R p.1 q.1 ∧ p.2 = q.2) (l.zipIdx k) (l'.zipIdx k)
  | [], [], List.Forall₂.nil, _ => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t, k => by
    rw [List.zipIdx_cons, List.zipIdx_cons]
    exact List.Forall₂.cons ⟨h, rfl⟩ (forall₂_zipIdx_both t (k + 1))

lemma forall₂_self_zipIdx {α : Type} {R : α → (α × ℕ) → Prop} (h : ∀ a i, R a (a, i)) :
    ∀ (l : List α) (k : ℕ), List.Forall₂ R l (l.zipIdx k)
  | [], _ => List.Forall₂.nil
  | a :: l, k => by
    rw [List.zipIdx_cons]
    exact List.Forall₂.cons (h a k) (forall₂_self_zipIdx h l (k + 1))

lemma forall₂_comp {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop} :
    ∀ {a : List α} {b : List β} {c : List γ}, List.Forall₂ R a b → List.Forall₂ S b c →
      List.Forall₂ (fun x z => ∃ y, R x y ∧ S y z) a c
  | [], [], [], List.Forall₂.nil, List.Forall₂.nil => List.Forall₂.nil
  | _ :: _, _ :: _, _ :: _, List.Forall₂.cons h t, List.Forall₂.cons h' t' =>
    List.Forall₂.cons ⟨_, h, h'⟩ (forall₂_comp t t')

lemma flatMap_blocks' : ∀ (lens : List ℕ) (o k : ℕ),
    ((lens.zipIdx k).flatMap fun p => (List.range p.1).map fun i =>
      o + (lens.take (p.2 - k)).sum + i) = (List.range lens.sum).map (o + ·)
  | [], _, _ => rfl
  | a :: l, o, k => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.sum_cons, List.range_add, List.map_append,
      List.map_map]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · refine List.map_congr_left fun i _ => ?_
      simp
    · rw [List.flatMap_congr (fun p hp => List.map_congr_left (fun i _ =>
        (show o + ((a :: l).take (p.2 - k)).sum + i = o + a + (l.take (p.2 - (k + 1))).sum + i by
          have := List.le_snd_of_mem_zipIdx hp
          rw [show p.2 - k = p.2 - (k + 1) + 1 by omega, List.take_succ_cons, List.sum_cons]
          omega)))]
      rw [flatMap_blocks' l (o + a) (k + 1)]
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp]
      omega

/-- Consecutive blocks of indices. -/
lemma flatMap_blocks (lens : List ℕ) (o : ℕ) :
    (lens.zipIdx.flatMap fun p => (List.range p.1).map fun i => o + (lens.take p.2).sum + i) =
      (List.range lens.sum).map (o + ·) := by
  simpa using flatMap_blocks' lens o 0

lemma map_fst_zipIdx' {α : Type} : ∀ (l : List α) (k : ℕ), (l.zipIdx k).map Prod.fst = l
  | [], _ => rfl
  | a :: l, k => by rw [List.zipIdx_cons, List.map_cons, map_fst_zipIdx' l (k + 1)]

lemma eq_of_length_four {l : List ℕ} (h : l.length = 4) :
    l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0] := by
  match l, h with
  | [a, b, c, d], _ => rfl

/-! ## Sizes -/

/-- The number of schemas of a command. -/
def cmdSz {L : Type} : ACmd L s → ℕ
  | .assign .. => 4
  | .fork .. => 9

/-- The number of schemas of the command on the stack `τ` (at base `b`). -/
def szAt (b : ℕ) (τ : List ℕ) : ℕ := if τ.getD (b + 17) 0 ≠ 0 then 9 else 4

lemma szAt_of_stkCmd {x : List Bool} {ℓ H b : ℕ} {ρ τ : List ℕ} {cmd : ACmd (Loc M H) s}
    (h : StkCmd x s ℓ H b ρ τ cmd) : szAt b τ = cmdSz cmd := by
  obtain ⟨-, -, -, hd⟩ := h
  have e : τ.getD (b + 17) 0 = (τ.drop (b + 17)).getD 0 0 := by rw [getD_drop']
  cases cmd with
  | assign => simp only [szAt, cmdSz]; rw [e, hd.2.1] <;> simp
  | fork => simp only [szAt, cmdSz]; rw [e, hd.2.1] <;> simp

/-! ## Stacks -/

/-- The stacks of the schemas of the command on the stack `τ`, with index `j` and first
schema index `e0`. -/
def cmdSchStks (NX : Xp) (b : ℕ) (τ : List ℕ) (j e0 : ℕ) : List (List ℕ) :=
  ((if τ.getD (b + 17) 0 ≠ 0 then forkBlk NX b else assignBlk NX b).zipIdx.map fun p =>
    (τ ++ [j, e0]) ++ (e0 + p.2) :: (p.1.map (·.eval (τ ++ [j, e0])) ++
      (gdX b).map (·.eval (τ ++ [j, e0]))))

/-- The stacks of the detector schemas. -/
def detStks (NX rX p0X EcX : Xp) (ρ : List ℕ) : List (List ℕ) :=
  ((gadgetX p0X (const 0) (detX NX rX 0) (detX NX rX 1) (detX NX rX 2) (detX NX rX 3)).zipIdx.map
    fun p => (ρ ++ List.replicate 27 0) ++ (EcX.eval ρ + p.2) ::
      (p.1.map (·.eval ρ) ++ [3, 0, 0, 0]))

/-- The first schema index of command `j`. -/
noncomputable def e0Of (x : List Bool) (ℓ H j : ℕ) : ℕ :=
  (((verifierCmds' M x s ℓ H).take j).map cmdSz).sum

variable (M s) in
/-- The stacks of all schemas. -/
noncomputable def schStks (b : ℕ) (HX RX NX rX p0X EcX : Xp) (x : List Bool) (ρ : List ℕ)
    (ℓ H : ℕ) : List (List ℕ) :=
  (cmdStks M s b HX RX x ρ H).zipIdx.flatMap (fun p =>
    cmdSchStks NX b p.1 p.2 (e0Of (M := M) (s := s) x ℓ H p.2)) ++ detStks NX rX p0X EcX ρ

/-! ## Bounds -/

lemma bnd_var {i n : ℕ} (h : i < n) : (var i).Bnd n := h

lemma bnd_gadgetX {n : ℕ} {X msk A B Z Y : Xp} (h1 : X.Bnd n) (h2 : msk.Bnd n) (h3 : A.Bnd n)
    (h4 : B.Bnd n) (h5 : Z.Bnd n) (h6 : Y.Bnd n) :
    ∀ l ∈ gadgetX X msk A B Z Y, ∀ e ∈ l, e.Bnd n := by
  simp only [gadgetX, List.mem_cons, List.not_mem_nil, or_false]
  rintro l (rfl | rfl | rfl | rfl) e he <;> simp only [List.mem_cons, List.not_mem_nil,
    or_false] at he <;> rcases he with rfl | rfl | rfl | rfl | rfl <;> first | trivial | assumption

lemma bnd_slotX {NX : Xp} {b n : ℕ} (hN : NX.Bnd b) (hn : b + 26 ≤ n) (t : ℕ) :
    (slotX NX b t).Bnd n :=
  ⟨Xp.Bnd.mono (by omega) hN, trivial, Xp.bnd_mulC (bnd_var (show b + 25 < n by omega)) 8⟩

lemma bnd_assignBlk {NX : Xp} {b n : ℕ} (hN : NX.Bnd b) (hn : b + 26 ≤ n) :
    ∀ l ∈ assignBlk NX b, ∀ e ∈ l, e.Bnd n :=
  bnd_gadgetX (bnd_var (show b + 19 < n by omega)) (bnd_var (show b + 18 < n by omega)) (bnd_slotX hN hn 0)
    (bnd_slotX hN hn 1) (bnd_slotX hN hn 2) (bnd_var (show b + 15 < n by omega))

lemma bnd_forkBlk {NX : Xp} {b n : ℕ} (hN : NX.Bnd b) (hn : b + 26 ≤ n) :
    ∀ l ∈ forkBlk NX b, ∀ e ∈ l, e.Bnd n := by
  intro l hl
  simp only [forkBlk, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with (hl | hl) | rfl
  · exact bnd_gadgetX (bnd_var (show b + 19 < n by omega)) (show (const 0).Bnd n from trivial) (bnd_slotX hN hn 0)
      (bnd_slotX hN hn 1) (bnd_slotX hN hn 2) (bnd_slotX hN hn 6) l hl
  · exact bnd_gadgetX (bnd_var (show b + 20 < n by omega)) (show (const 0).Bnd n from trivial) (bnd_slotX hN hn 3)
      (bnd_slotX hN hn 4) (bnd_slotX hN hn 5) (bnd_slotX hN hn 7) l hl
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact bnd_slotX hN hn 6
    · exact bnd_slotX hN hn 7
    · show b + 15 < n; omega
    · trivial

lemma bnd_gdX {b n : ℕ} (hn : b + 25 ≤ n) : ∀ e ∈ gdX b, e.Bnd n := by
  simp only [gdX, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl) <;> show _ < n <;> omega

/-! ## Outputs -/

section Out

variable {x : List Bool} {ρ : List ℕ} {b H ℓ : ℕ} {HX RX NX rX p0X EcX : Xp}
  (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
  (hR : RX.eval ρ = radix M H)
include hρ hHb hRb hH hR

lemma length_cmdStks_eq {b' : ℕ} {σ : List ℕ} (hσ : σ.length = b') (hσρ : σ.take b = ρ)
    (hb' : b ≤ b') (ℓ : ℕ) :
    (cmdStks M s b' HX RX x σ H).length = (cmdStks M s b HX RX x ρ H).length := by
  have hσsplit : σ = ρ ++ σ.drop b := by rw [← hσρ, List.take_append_drop]
  have hHσ : HX.eval σ = H := by rw [hσsplit]; exact (Xp.eval_append hρ _ hHb).trans hH
  have hRσ : RX.eval σ = radix M H := by rw [hσsplit]; exact (Xp.eval_append hρ _ hRb).trans hR
  rw [(cmdStks_forall₂ (x := x) hσ (Xp.Bnd.mono hb' hHb) (Xp.Bnd.mono hb' hRb) hHσ hRσ ℓ).length_eq,
    (cmdStks_forall₂ (x := x) hρ hHb hRb hH hR ℓ).length_eq]

/-- **The body of the command enumerator.** -/
theorem out_cmdBody (hNb : NX.Bnd b) (ℓ : ℕ) (body : Gn) {j : ℕ}
    (hj : j < (cmdStks M s b HX RX x ρ H).length) :
    (cmdBody M s b HX RX NX body).out x (cmdStks M s b HX RX x ρ H)[j] =
      (cmdSchStks NX b (cmdStks M s b HX RX x ρ H)[j] j
        (e0Of (M := M) (s := s) x ℓ H j)).flatMap (body.out x) := by
  set C := cmdStks M s b HX RX x ρ H with hC
  set τ := C[j] with hτ
  have hF := cmdStks_forall₂ (x := x) (s := s) hρ hHb hRb hH hR ℓ
  have hrel : StkCmd x s ℓ H b ρ τ ((verifierCmds' M x s ℓ H)[j]'(hF.length_eq ▸ hj)) :=
    List.forall₂_iff_get.mp hF |>.2 j hj _
  obtain ⟨hτl, hτρ, -, -⟩ := hrel
  -- the count of `j`
  have h1 : ((cmdEnum M s (b + 26) HX RX (Gn.when (beforeX b (b + 26)) (.emit (const 0)))).out
      x (τ ++ [0])).length = j := by
    rw [length_out_before ℓ hρ hHb hRb hH hR (by omega) (by simp [hτl])
      (by rw [List.take_append_of_le_length (by omega), hτρ]) hj
      (by rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)])]
    have hl := length_cmdStks_eq (x := x) (s := s) hρ hHb hRb hH hR (b' := b + 26)
      (σ := τ ++ [0]) (by simp [hτl])
      (by rw [List.take_append_of_le_length (by omega), hτρ]) (by omega) ℓ
    simp only [Gn.out, List.length_singleton, List.map_const', List.sum_replicate, smul_eq_mul,
      mul_one, List.length_take]
    omega
  -- the count of `e₀`
  have h2 : ((cmdEnum M s (b + 27) HX RX (Gn.when (beforeX b (b + 27))
      (.ite (var (b + 27 + 17)) (Gn.emitN 9) (Gn.emitN 4)))).out x (τ ++ [j, 0])).length =
      e0Of (M := M) (s := s) x ℓ H j := by
    have hσl : (τ ++ [j, 0]).length = b + 27 := by simp [hτl]
    have hσρ : (τ ++ [j, 0]).take b = ρ := by
      rw [List.take_append_of_le_length (by omega), hτρ]
    rw [length_out_before ℓ hρ hHb hRb hH hR (by omega) hσl hσρ hj
      (by rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)])]
    have hσsplit : τ ++ [j, 0] = ρ ++ (τ ++ [j, 0]).drop b := by
      rw [← hσρ, List.take_append_drop]
    have hHσ : HX.eval (τ ++ [j, 0]) = H := by
      rw [hσsplit]; exact (Xp.eval_append hρ _ hHb).trans hH
    have hRσ : RX.eval (τ ++ [j, 0]) = radix M H := by
      rw [hσsplit]; exact (Xp.eval_append hρ _ hRb).trans hR
    have hF2 := cmdStks_forall₂ (x := x) (s := s) hσl (Xp.Bnd.mono (by omega) hHb)
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
  simp only [cmdBody, Gn.out]
  rw [h1, show τ ++ [j] ++ [0] = τ ++ [j, 0] by simp, h2,
    show τ ++ [j] ++ [e0Of (M := M) (s := s) x ℓ H j] = τ ++ [j, e0Of (M := M) (s := s) x ℓ H j]
      by simp]
  have hlen : (τ ++ [j, e0Of (M := M) (s := s) x ℓ H j]).length = b + 27 := by simp [hτl]
  have e17 : (var (b + 17)).eval (τ ++ [j, e0Of (M := M) (s := s) x ℓ H j]) = τ.getD (b + 17) 0 := by
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

omit hHb hRb hH hR in
lemma out_detGen (hNb : NX.Bnd b) (hrb : rX.Bnd b) (hpb : p0X.Bnd b) (hEb : EcX.Bnd b)
    (body : Gn) : (detGen NX rX p0X EcX body).out x ρ =
      (detStks NX rX p0X EcX ρ).flatMap (body.out x) := by
  have hz : ∀ e ∈ List.replicate 27 (const 0), e.Bnd b := fun e he => by
    rw [List.eq_of_mem_replicate he]; trivial
  rw [detGen, Gn.out_bindL _ _ hρ hz]
  have hl : (ρ ++ (List.replicate 27 (const 0)).map fun e => e.eval ρ).length = b + 27 := by
    simp [hρ]
  have hdX : ∀ t, (detX NX rX t).Bnd (b + 27) := fun t =>
    ⟨⟨Xp.Bnd.mono (by omega) hNb, Xp.bnd_mulC (Xp.Bnd.mono (by omega) hrb) 8⟩, trivial⟩
  rw [Gn.out_blkGen hl _ _ _ _ (Xp.Bnd.mono (by omega) hEb) (by
      intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> trivial)
    (bnd_gadgetX (Xp.Bnd.mono (by omega) hpb) (show (const 0).Bnd (b + 27) from trivial) (hdX 0) (hdX 1) (hdX 2) (hdX 3))]
  have hrep : (List.replicate 27 (const 0)).map (fun e => e.eval ρ) = List.replicate 27 0 := by
    simp
  have hev : ∀ e : Xp, e.Bnd b → e.eval (ρ ++ List.replicate 27 0) = e.eval ρ :=
    fun e he => Xp.eval_append hρ _ he
  rw [hrep, detStks]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have hm : p.1 ∈ gadgetX p0X (const 0) (detX NX rX 0) (detX NX rX 1) (detX NX rX 2)
      (detX NX rX 3) := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
  have hb := bnd_gadgetX (n := b) hpb (show (const 0).Bnd b from trivial)
    (show (detX NX rX 0).Bnd b from ⟨⟨hNb, Xp.bnd_mulC hrb 8⟩, trivial⟩)
    (show (detX NX rX 1).Bnd b from ⟨⟨hNb, Xp.bnd_mulC hrb 8⟩, trivial⟩)
    (show (detX NX rX 2).Bnd b from ⟨⟨hNb, Xp.bnd_mulC hrb 8⟩, trivial⟩)
    (show (detX NX rX 3).Bnd b from ⟨⟨hNb, Xp.bnd_mulC hrb 8⟩, trivial⟩) _ hm
  simp only [hev EcX hEb, List.map_cons, List.map_nil, Xp.eval_const]
  congr 3
  exact List.map_congr_left fun e he => hev e (hb e he)

/-- **The output of the schema enumerator, by stacks.** -/
theorem out_schEnum_stks (hNb : NX.Bnd b) (hrb : rX.Bnd b) (hpb : p0X.Bnd b) (hEb : EcX.Bnd b)
    (ℓ : ℕ) (body : Gn) :
    (schEnum M s b HX RX NX rX p0X EcX body).out x ρ =
      (schStks M s b HX RX NX rX p0X EcX x ρ ℓ H).flatMap (body.out x) := by
  rw [schEnum, Gn.out, out_cmdEnum' hρ hHb hRb hH hR, out_detGen hρ hNb hrb hpb hEb,
    schStks, List.flatMap_append, List.flatMap_assoc]
  congr 1
  conv_lhs => rw [← map_fst_zipIdx' (cmdStks M s b HX RX x ρ H) 0, List.flatMap_map]
  refine List.flatMap_congr fun p hp => ?_
  have h := List.mem_zipIdx_iff_getElem?.mp hp
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp h
  rw [← hget]
  exact out_cmdBody hρ hHb hRb hH hR hNb ℓ body hj

end Out

end Lax119563Proofs.Reduction
