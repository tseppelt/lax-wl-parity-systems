import Lax119563Proofs.Bridges.TM2Sim.Defs

/-!
# Simulating archive multitape machines by mathlib stack machines: statement semantics

Stack contents are written as `mkStk io outRev tmp Ls Rs`. We compute the effect of the
compound statements (`pushOpt`, `scanAll`, `applyOne`, `applyAllStmt`, `popAll`) on such
stacks, and set up exact step counting (`Reaches`).
-/

open Lax489179.TuringMachine (Machine Config Move Instruction)
open Turing

namespace Lax119563Proofs.Bridges.TM2Sim

variable {R : Machine} {A : Type} {τi : InTransducer A} {τo : OutTransducer A}

/-- Stack contents. -/
def mkStk (io outR : List A) (tmp : List (G R)) (Ls Rs : Fin (R.tapes + 1) → List (G R)) :
    ∀ k, List (Γ' R A k)
  | .io => io
  | .outRev => outR
  | .tmp => tmp
  | .L j => Ls j
  | .R j => Rs j

section mkStk

variable (io outR : List A) (tmp : List (G R)) (Ls Rs : Fin (R.tapes + 1) → List (G R))

@[simp] lemma mkStk_io : mkStk io outR tmp Ls Rs .io = io := rfl
@[simp] lemma mkStk_outRev : mkStk io outR tmp Ls Rs .outRev = outR := rfl
@[simp] lemma mkStk_tmp : mkStk io outR tmp Ls Rs .tmp = tmp := rfl
@[simp] lemma mkStk_L (j) : mkStk io outR tmp Ls Rs (.L j) = Ls j := rfl
@[simp] lemma mkStk_R (j) : mkStk io outR tmp Ls Rs (.R j) = Rs j := rfl

@[simp] lemma update_io (x : List A) :
    Function.update (mkStk io outR tmp Ls Rs) Stk.io x = mkStk x outR tmp Ls Rs := by
  funext k; cases k <;> simp [Function.update, mkStk]

@[simp] lemma update_outRev (x : List A) :
    Function.update (mkStk io outR tmp Ls Rs) Stk.outRev x = mkStk io x tmp Ls Rs := by
  funext k; cases k <;> simp [Function.update, mkStk]

@[simp] lemma update_tmp (x : List (G R)) :
    Function.update (mkStk io outR tmp Ls Rs) Stk.tmp x = mkStk io outR x Ls Rs := by
  funext k; cases k <;> simp [Function.update, mkStk]

@[simp] lemma update_L (j) (x : List (G R)) :
    Function.update (mkStk io outR tmp Ls Rs) (Stk.L j) x =
      mkStk io outR tmp (Function.update Ls j x) Rs := by
  funext k; cases k with
  | L i =>
    by_cases h : i = j
    · subst h; simp [Function.update, mkStk]
    · simp [Function.update, mkStk, h]
  | _ => simp [Function.update, mkStk]

@[simp] lemma update_R (j) (x : List (G R)) :
    Function.update (mkStk io outR tmp Ls Rs) (Stk.R j) x =
      mkStk io outR tmp Ls (Function.update Rs j x) := by
  funext k; cases k with
  | R i =>
    by_cases h : i = j
    · subst h; simp [Function.update, mkStk]
    · simp [Function.update, mkStk, h]
  | _ => simp [Function.update, mkStk]

end mkStk

/-! ## Simple facts about the variables -/

@[simp] lemma wr_cell (v : Var R A τi τo) (o) (j) : wr { v with cell := o } j = wr v j := rfl
@[simp] lemma mv_cell (v : Var R A τi τo) (o) (j) : mv { v with cell := o } j = mv v j := rfl

/-- The entry of a bit. -/
def bitG (b : Bool) : G R := (bitSym R b, false)

/-! ## `pushOpt` -/

open TM2 in
lemma stepAux_pushOpt (g : Var R A τi τo → Option Bool) (next : Stmt' R A τi τo)
    (v : Var R A τi τo) (io outR : List A) (tmp : List (G R)) (Ls Rs) :
    stepAux (pushOpt g next) v (mkStk io outR tmp Ls Rs) =
      stepAux next v (mkStk io outR ((g v).toList.map bitG ++ tmp) Ls Rs) := by
  unfold pushOpt
  cases h : g v with
  | none => simp [h]
  | some b => simp [h, bitG]

lemma pushTwo_eq (l : List Bool) (hl : l.length ≤ 2) :
    l[1]?.toList.map (bitG (R := R)) ++ (l[0]?.toList.map bitG) = (l.map bitG).reverse := by
  match l, hl with
  | [], _ => rfl
  | [a], _ => rfl
  | [a, b], _ => rfl

/-! ## Scanning -/

/-- The scanned symbol of a right stack. -/
def top (l : List (G R)) : Sym R := (l.head?.getD (g0 R)).1

open TM2 in
lemma stepAux_scanAll (js : List (Fin (R.tapes + 1))) (next : Stmt' R A τi τo)
    (v : Var R A τi τo) (io outR : List A) (tmp : List (G R)) (Ls Rs) :
    stepAux (scanAll js next) v (mkStk io outR tmp Ls Rs) =
      stepAux next { v with scanned := fun i => if i ∈ js then top (Rs i) else v.scanned i }
        (mkStk io outR tmp Ls Rs) := by
  induction js generalizing v with
  | nil => simp [scanAll]
  | cons j js ih =>
    simp only [scanAll, stepAux, mkStk_R]
    rw [ih]
    congr 2
    funext i
    by_cases h₁ : i ∈ js
    · simp [h₁]
    · by_cases h₂ : i = j
      · subst h₂; simp [h₁, top]
      · simp [h₁, h₂]

/-! ## Writing and moving -/

/-- The effect of writing `w` and moving by `m` on a tape kept as stacks `L`, `Rl`. -/
def applyTape (L Rl : List (G R)) (w : Sym R) (m : Move) : List (G R) × List (G R) :=
  match m with
  | .right => ((w, (Rl.head?.map Prod.snd).getD false) :: L, Rl.tail)
  | .stay => (L, (w, (Rl.head?.map Prod.snd).getD false) :: Rl.tail)
  | .left => (L.tail, L.head?.getD (g0 R) :: (w, (Rl.head?.map Prod.snd).getD false) :: Rl.tail)

open TM2 in
lemma stepAux_applyOne (j : Fin (R.tapes + 1)) (next : Stmt' R A τi τo)
    (v : Var R A τi τo) (io outR : List A) (tmp : List (G R)) (Ls Rs) :
    ∃ o, stepAux (applyOne j next) v (mkStk io outR tmp Ls Rs) =
      stepAux next { v with cell := o }
        (mkStk io outR tmp (Function.update Ls j (applyTape (Ls j) (Rs j) (wr v j) (mv v j)).1)
          (Function.update Rs j (applyTape (Ls j) (Rs j) (wr v j) (mv v j)).2)) := by
  unfold applyOne
  cases h : mv v j with
  | right =>
    refine ⟨(Rs j).head?, ?_⟩
    simp [h, isRight, applyTape, newCell, Function.update_idem]
  | stay =>
    refine ⟨(Rs j).head?, ?_⟩
    simp [h, isRight, isLeft, applyTape, newCell, Function.update_idem]
  | left =>
    refine ⟨(Ls j).head?, ?_⟩
    simp [h, isRight, isLeft, applyTape, newCell, Function.update_idem]

/-- The tapes after applying the instruction to the tapes in `js`. -/
def applyLs (js : List (Fin (R.tapes + 1))) (v : Var R A τi τo) (Ls Rs : Fin (R.tapes + 1) → List (G R)) :
    Fin (R.tapes + 1) → List (G R) :=
  fun i => if i ∈ js then (applyTape (Ls i) (Rs i) (wr v i) (mv v i)).1 else Ls i

/-- The tapes after applying the instruction to the tapes in `js`. -/
def applyRs (js : List (Fin (R.tapes + 1))) (v : Var R A τi τo) (Ls Rs : Fin (R.tapes + 1) → List (G R)) :
    Fin (R.tapes + 1) → List (G R) :=
  fun i => if i ∈ js then (applyTape (Ls i) (Rs i) (wr v i) (mv v i)).2 else Rs i

open TM2 in
lemma stepAux_applyAll (js : List (Fin (R.tapes + 1))) (hjs : js.Nodup)
    (next : Stmt' R A τi τo)
    (v : Var R A τi τo) (io outR : List A) (tmp : List (G R)) (Ls Rs) :
    ∃ o, stepAux (applyAllStmt js next) v (mkStk io outR tmp Ls Rs) =
      stepAux next { v with cell := o }
        (mkStk io outR tmp (applyLs js v Ls Rs) (applyRs js v Ls Rs)) := by
  induction js generalizing v Ls Rs with
  | nil =>
    have h1 : applyLs [] v Ls Rs = Ls := by funext i; simp [applyLs]
    have h2 : applyRs [] v Ls Rs = Rs := by funext i; simp [applyRs]
    exact ⟨v.cell, by rw [h1, h2]; rfl⟩
  | cons j js ih =>
    rw [List.nodup_cons] at hjs
    obtain ⟨o₁, h₁⟩ := stepAux_applyOne j (applyAllStmt js next) v io outR tmp Ls Rs
    simp only [applyAllStmt]
    rw [h₁]
    obtain ⟨o₂, h₂⟩ := ih hjs.2 { v with cell := o₁ } _ _
    rw [h₂]
    refine ⟨o₂, ?_⟩
    congr 2
    · funext i
      simp only [applyLs, List.mem_cons, wr_cell, mv_cell]
      by_cases hi : i ∈ js
      · have hij : i ≠ j := fun e => hjs.1 (e ▸ hi)
        simp [hi, hij]
      · by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [hi, hij]
    · funext i
      simp only [applyRs, List.mem_cons, wr_cell, mv_cell]
      by_cases hi : i ∈ js
      · have hij : i ≠ j := fun e => hjs.1 (e ▸ hi)
        simp [hi, hij]
      · by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [hi, hij]

/-! ## Clearing -/

lemma any_congr' {α : Type} (l : List α) (p q : α → Bool) (h : ∀ i ∈ l, p i = q i) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun i hi => h i (by simp [hi]))]

open TM2 in
lemma stepAux_popAll (js : List (Fin (R.tapes + 1))) (hjs : js.Nodup)
    (next : Stmt' R A τi τo)
    (v : Var R A τi τo) (io outR : List A) (tmp : List (G R)) (Ls Rs) :
    stepAux (popAll js next) v (mkStk io outR tmp Ls Rs) =
      stepAux next { v with flag := v.flag || js.any (fun j => !(Ls j).isEmpty || !(Rs j).isEmpty) }
        (mkStk io outR tmp (fun i => if i ∈ js then (Ls i).tail else Ls i)
          (fun i => if i ∈ js then (Rs i).tail else Rs i)) := by
  induction js generalizing v Ls Rs with
  | nil => simp [popAll]
  | cons j js ih =>
    rw [List.nodup_cons] at hjs
    simp only [popAll, stepAux, mkStk_L, mkStk_R, update_L, update_R]
    rw [ih hjs.2]
    have hL : (Function.update Ls j (Ls j).tail) j = (Ls j).tail := by simp
    congr 2
    · simp only [List.any_cons]
      have e : ∀ i ∈ js, Function.update Ls j (Ls j).tail i = Ls i ∧
          Function.update Rs j (Rs j).tail i = Rs i := by
        intro i hi
        have hij : i ≠ j := fun e => hjs.1 (e ▸ hi)
        simp [hij]
      rw [any_congr' js _ _ (fun i hi => by rw [(e i hi).1, (e i hi).2])]
      rcases hLj : Ls j with _ | ⟨a, l⟩ <;> rcases hRj : Rs j with _ | ⟨b, l'⟩ <;>
        simp
    · funext i
      by_cases hi : i ∈ js
      · have hij : i ≠ j := fun e => hjs.1 (e ▸ hi)
        simp [hi, hij]
      · by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [hi, hij]
    · funext i
      by_cases hi : i ∈ js
      · have hij : i ≠ j := fun e => hjs.1 (e ▸ hi)
        simp [hi, hij]
      · by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [hi, hij]

end Lax119563Proofs.Bridges.TM2Sim
