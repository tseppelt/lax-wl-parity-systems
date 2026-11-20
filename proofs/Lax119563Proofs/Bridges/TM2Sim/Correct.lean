import Lax119563Proofs.Bridges.TM2Sim.Sim

/-!
# Simulating archive multitape machines by mathlib stack machines: the main theorem

`simulate`: if `R` computes `y` from `τi.run τi.start u` within `T` steps, then the stack
machine `tm R τi τo` outputs `τo.run τo.start y` on input `u` within `30 (|u| + T) + 30`
steps.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction step run init)
open Lax119563.DeterministicTime
open Turing

namespace Lax119563Proofs.Bridges.TM2Sim

variable {R : Machine} {A : Type} {τi : InTransducer A} {τo : OutTransducer A} [Inhabited A]

lemma getD_drop (l : List (G R)) (k i : ℕ) :
    (l.drop k).getD i (g0 R) = l.getD (k + i) (g0 R) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **Output phase.** From a simulated configuration in which `R` halts, with tape `0` holding
`y` as an input, the stack machine halts with `τo.run τo.start y` on `io` within
`5 B + 6` steps. -/
lemma output_run {c : Config R} {v : Var R A τi τo} {Ls Rs} {B : ℕ} (H : SimRel c v Ls Rs B)
    {b : Bool} (hI : R.transition c.state (scanOf c) false = .halt b) (y : List Bool)
    (hy : c.tape 0 = (init R y).tape 0) :
    ∃ n ≤ 5 * B + 6, Reaches R A τi τo n ⟨some .sim, v, mkStk [] [] [] Ls Rs⟩
      ⟨none, Var.init R A τi τo, mkStk (τo.run τo.start y) [] [] (fun _ => []) (fun _ => [])⟩ := by
  have hh : isHalt (instr (scanV v Rs)) = true := by rw [instr_scanV H, hI]; rfl
  have h1 := step_sim_halt v Ls Rs hh
  obtain ⟨-, hqo, hT, hO, hB⟩ := H
  obtain ⟨v₁, hqo₁, hr₁⟩ := gather_run (Ls 0) (scanV v Rs) Ls Rs rfl
  set Lst := (Ls 0).reverse ++ Rs 0 with hLst
  have hLen : Lst.length = (Ls 0).length + (Rs 0).length := by simp [hLst]
  have hO3 := hO.2.2.1
  have hO4 := hO.2.2.2
  set k : ℕ := ((Ls 0).length - c.head 0).toNat with hk
  have hkz : (k : ℤ) = (Ls 0).length - c.head 0 := by rw [hk]; omega
  have hkL : k < Lst.length := by rw [hLen]; omega
  have hsplit : Lst = Lst.take k ++ Lst[k] :: Lst.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hkL, List.take_append_drop]
  have hpre : ∀ x ∈ Lst.take k, x.2 = false := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_take, gathered_origin hO (i := i)]
    · simp only [List.length_take] at hi; simp; omega
  have hg : (Lst[k]).2 = true := by
    rw [gathered_origin hO]; simp; omega
  obtain ⟨v₂, hqo₂, hc₂, hr₂⟩ := seek_run (Lst.take k) v₁ (Function.update Ls 0 [])
    (Function.update Rs 0 Lst) Lst[k] (Lst.drop (k + 1)) hpre hg
    (by rw [Function.update_self]; exact hsplit)
  have hfeed : ∀ i : ℕ, ((v₂.cell.getD (g0 R) ::
      (Function.update (Function.update Rs 0 Lst) 0 (Lst.drop (k + 1))) 0).getD i (g0 R)).1 =
      cellSym R y i := by
    intro i
    rw [hc₂, Function.update_self, Option.getD_some, ← List.drop_eq_getElem_cons hkL,
      getD_drop, ← gathered_rep (hT 0) (k + i), hy]
    rw [show c.head 0 - ((Ls 0).length : ℤ) + ((k + i : ℕ) : ℤ) = (i : ℤ) by push_cast; omega]
    exact init_tape_zero y i
  have hylen : y.length ≤ Lst.length := by
    have := length_le_of_cellSym hfeed
    rw [Function.update_self] at this
    simp at this
    omega
  obtain ⟨v₃, rest, hrest, hr₃⟩ := feed_run y v₂ [] (Function.update Ls 0 [])
    (Function.update (Function.update Rs 0 Lst) 0 (Lst.drop (k + 1))) hfeed
  have hq₂ : v₂.qo = τo.start := by rw [hqo₂, hqo₁]; exact hqo
  rw [hq₂, List.append_nil] at hr₃
  obtain ⟨v₄, hr₄⟩ := outRev_run (τo.run τo.start y).reverse v₃ [] (Function.update Ls 0 [])
    (Function.update (Function.update (Function.update Rs 0 Lst) 0 (Lst.drop (k + 1))) 0 rest)
  rw [List.reverse_reverse, List.append_nil] at hr₄
  have hbounds : ∀ j, (Function.update Ls 0 [] j).length ≤ B ∧
      (Function.update (Function.update (Function.update Rs 0 Lst) 0 (Lst.drop (k + 1))) 0 rest
        j).length ≤ B := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp only [Function.update_self, List.length_nil, Nat.zero_le, true_and]
      simp only [Function.update_self, List.length_drop] at hrest
      have := hB 0; omega
    · simp only [Function.update_of_ne hj]
      have := hB j; omega
  obtain ⟨n, hn, v₅, hr₅⟩ := clear_run (τo.run τo.start y) B v₄ _ _ hbounds
  have hr₆ := reaches_one (step_done (τi := τi) (τo := τo) v₅
    (mkStk (τo.run τo.start y) [] [] (fun _ => []) (fun _ => [])))
  have hout := outRun_length (τo := τo) y τo.start
  have hL0 := hB 0
  refine ⟨_, ?_, reaches_succ h1 (reaches_trans hr₁ (reaches_trans hr₂ (reaches_trans hr₃
    (reaches_trans hr₄ (reaches_trans hr₅ hr₆)))))⟩
  simp only [List.length_take, List.length_reverse] at *
  omega


variable [Fintype A]

lemma initList_eq (u : List A) :
    initList (tm R τi τo) u =
      (⟨some .inPop, Var.init R A τi τo, mkStk u [] [] (fun _ => []) (fun _ => [])⟩ :
        Cfg' R A τi τo) := by
  unfold initList
  congr 1
  funext k
  cases k <;> rfl

lemma haltList_eq (l : List A) :
    haltList (tm R τi τo) l =
      (⟨none, Var.init R A τi τo, mkStk l [] [] (fun _ => []) (fun _ => [])⟩ :
        Cfg' R A τi τo) := by
  unfold haltList
  congr 1
  funext k
  cases k <;> rfl

lemma evals_of_reaches {u l : List A} {n : ℕ}
    (h : Reaches R A τi τo n
      ⟨some .inPop, Var.init R A τi τo, mkStk u [] [] (fun _ => []) (fun _ => [])⟩
      ⟨none, Var.init R A τi τo, mkStk l [] [] (fun _ => []) (fun _ => [])⟩) :
    (flip bind (tm R τi τo).step)^[n] (some (initList (tm R τi τo) u)) =
      Option.map (haltList (tm R τi τo)) (some l) := by
  have e1 := initList_eq (R := R) (τi := τi) (τo := τo) u
  have e2 := haltList_eq (R := R) (τi := τi) (τo := τo) l
  unfold Reaches at h
  exact (e1 ▸ e2 ▸ h : _)

/-- **Simulation by a stack machine.** If `R` computes `y` from the binary input
`τi.run τi.start u` within `T` steps, then `tm R τi τo` outputs `τo.run τo.start y` on input
`u` within `30 (|u| + T) + 30` steps. -/
theorem simulate (u : List A) (y : List Bool) (T : ℕ)
    (h : ComputesWithin R (τi.run τi.start u) y T) :
    Nonempty (TM2OutputsInTime (tm R τi τo) u (some (τo.run τo.start y))
      (30 * (u.length + T) + 30)) := by
  classical
  set x := τi.run τi.start u with hx
  -- input phase
  obtain ⟨v₁, hq₁, hqo₁, hr₁⟩ := inPop_run u (Var.init R A τi τo) [] (fun _ => []) (fun _ => [])
  obtain ⟨v₂, hq₂, hqo₂, hr₂⟩ := inRev_run ((x.map bitG).reverse ++ []) v₁
    (fun _ => []) (fun _ => [])
  have hm := reaches_one (step_mark v₂ (fun _ => [])
    (Function.update (fun _ => []) 0 ((((x.map bitG).reverse ++ []).reverse ++ []))))
  have hmk : Function.update (Function.update (fun _ : Fin (R.tapes + 1) => ([] : List (G R))) 0
      (((x.map bitG).reverse ++ []).reverse ++ [])) 0
      ((top ((Function.update (fun _ : Fin (R.tapes + 1) => ([] : List (G R))) 0
        (((x.map bitG).reverse ++ []).reverse ++ [])) 0), true) ::
        ((Function.update (fun _ : Fin (R.tapes + 1) => ([] : List (G R))) 0
          (((x.map bitG).reverse ++ []).reverse ++ [])) 0).tail) =
      Function.update (fun _ : Fin (R.tapes + 1) => ([] : List (G R))) 0 (markedInput x) := by
    simp [markedInput]
  rw [hmk] at hm
  have H₀ : SimRel (τo := τo) (runOn R x 0) { v₂ with cell := (Function.update (fun _ : Fin (R.tapes + 1) => ([] : List (G R))) 0
      (((x.map bitG).reverse ++ []).reverse ++ []) 0).head? } (fun _ => [])
      (Function.update (fun _ : Fin (R.tapes + 1) => ([] : List (G R))) 0 (markedInput x)) (x.length + 1) :=
    simRel_init x _ (by rw [hq₂, hq₁]; rfl) (by rw [hqo₂, hqo₁]; rfl)
  -- the halting time
  have hex : ∃ t, (runOn R x t).answer.isSome := ⟨T, h.1⟩
  have ht₀ : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    simp [runOn, run, init] at this
  set t₁ := Nat.find hex - 1 with ht₁
  have hle : Nat.find hex ≤ T := Nat.find_min' hex h.1
  have hnone : (runOn R x t₁).answer = none := by
    have := Nat.find_min hex (show t₁ < Nat.find hex by omega)
    simpa using this
  obtain ⟨v, Ls, Rs, hr, H⟩ := sim_run H₀ t₁ hnone
  have hsucc : Nat.find hex = t₁ + 1 := by omega
  have hspec := Nat.find_spec hex
  rw [hsucc, Lax119563Proofs.Main.runOn_succ] at hspec
  cases hI : R.transition (runOn R x t₁).state (scanOf (runOn R x t₁)) false with
  | next q w m => rw [lax_step_next _ hnone hI] at hspec; simp at hspec
  | halt b =>
    have hy : (runOn R x t₁).tape 0 = (init R y).tape 0 := by
      have e1 := Lax119563Proofs.Main.runOn_eq_of_le R x hle (Nat.find_spec hex)
      rw [hsucc, Lax119563Proofs.Main.runOn_succ, lax_step_halt _ hnone hI] at e1
      rw [← h.2, e1]
    obtain ⟨n, hn, hro⟩ := output_run H hI y hy
    have hall := reaches_trans hr₁ (reaches_trans hr₂ (reaches_trans hm (reaches_trans hr hro)))
    have hxl := inRun_length (τi := τi) u τi.start
    refine ⟨⟨⟨_, evals_of_reaches hall⟩, ?_⟩⟩
    · simp only [List.length_append, List.length_reverse, List.length_map, List.length_nil,
        add_zero] at hn ⊢
      rw [← hx] at hxl
      omega

end Lax119563Proofs.Bridges.TM2Sim
