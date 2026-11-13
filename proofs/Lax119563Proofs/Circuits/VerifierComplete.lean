import Lax119563Proofs.Circuits.VerifierSound

/-!
# Completeness of the verifier

Every true claim has a move firing into true claims of smaller rank.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

/-! ## Rank arithmetic -/

lemma rk_lt_time {t t' a b K : ℕ} (h : t < t') (ha : a < K) : t * K + a < t' * K + b := by
  have : (t + 1) * K ≤ t' * K := Nat.mul_le_mul_right _ h
  nlinarith

lemma wK_eq : wK M H = wG M * (H + 2) + 2 * (H + 1) * (H + 4) := rfl

lemma lvl0_lt {d : ℕ} (hd : d ≤ H) : wP M H + 2 * d * wQ H + H + 2 < wK M H := by
  simp only [wK, wP, wQ]
  nlinarith

lemma lvl1_lt_wP (d : ℕ) : wG M * (H - d) + wG M - 1 < wP M H := by
  simp only [wP, wG]
  have : H - d ≤ H := Nat.sub_le _ _
  have : (M.tapes + 4) * (H - d) ≤ (M.tapes + 4) * H := Nat.mul_le_mul_left _ this
  have : (M.tapes + 4) * (H + 2) = (M.tapes + 4) * H + 2 * (M.tapes + 4) := by ring
  omega

lemma wP_pos : 0 < wP M H := by simp only [wP, wG]; positivity

lemma ptime_lt_succ {d ω θ : ℕ} (hd : d < H) : ptime H d ω θ < ptime H d ω (θ + 1) := by
  rw [ptime_phase hd, ptime_phase hd]
  have := bsz_pos (H := H) d
  nlinarith

/-- The row of the true run of a base call. -/
noncomputable def trueRow (A : ℕ) : Row M :=
  (extT M x H H (A / 4) 0,
   fun i => ⟨((rel M x H H (A / 4) 0 i).toNat - 1) % 2, Nat.mod_lt _ (by norm_num)⟩,
   scanT M x (A / 4))

lemma trueRow_rows {A : ℕ} (hA : A < 2 ^ (H + 2)) :
    ∀ i : Tape M, semCell M x H H 0 i ((trueRow (x := x) (H := H) A).2.2 i, true)
      (setBits A 0 2 (((trueRow (x := x) (H := H) A).2.1 i).val + 1)) := by
  rw [baseRow_iff]
  refine ⟨fun i => ?_, rfl⟩
  have hω : A / 4 < 2 ^ H := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    rw [pow_add] at hA; simpa [Nat.mul_comm] using hA
  have := rel_mem (x := x) H le_rfl (A / 4) hω i
  simp only [Nat.sub_self, pow_zero] at this
  simp only [trueRow]
  have h1 : 1 ≤ (rel M x H H (A / 4) 0 i).toNat := by omega
  have h2 : (rel M x H H (A / 4) 0 i).toNat < 3 := by omega
  have : ((rel M x H H (A / 4) 0 i).toNat - 1) % 2 = (rel M x H H (A / 4) 0 i).toNat - 1 := by
    omega
  rw [this]
  omega

lemma blk_lt_eight {d ω θ : ℕ} (hd : d < H) (hω : ω < 2 ^ d) (hθ : θ < 2) (ν : Tape M) :
    blk M x H d ω θ ν < 8 := by
  have := (phase_facts (x := x) hd hθ ν (rel_mem d hd.le ω hω ν)).2.1
  omega

lemma complete_cell (P : Params x s ℓ H) (d : Fin (H + 1)) (θ : Fin 3) (ν : Tape M)
    (c : CellVal M) {A : ℕ} (hA : A < 2 ^ (s * ℓ)) (hS : Sem M x H (.cell d θ ν c) A) :
    ∃ mv ∈ moves M x s ℓ H (.cell d θ ν c),
      mv.Fires ℓ (Sem M x H) (rank M H) (.cell d θ ν c) A := by
  have hA2 := P.addr_lt hA
  change semCell M x H d θ ν c A at hS
  by_cases h0 : θ.val = 0
  · by_cases hd0 : d.val = 0
    · -- root input tests
      rw [hd0, h0, semCell_root hA2] at hS
      have hrk : rank M H .accept A < rank M H (.cell d θ ν c) A := by
        simp only [rank, h0, if_true]
        have := wP_pos (M := M) (H := H)
        omega
      by_cases hdiv : A / 2 ^ ℓ = 2 ^ H / 2 ^ ℓ
      · refine ⟨.test (hitGuard M x s ℓ H ν c) .accept, ?_, ?_, trivial, hrk⟩
        · simp [moves, h0, hd0]
        · intro i
          by_cases hi : i.val = 0
          · have : i = ⟨0, P.s_pos⟩ := Fin.ext hi
            subst this
            simp only [hitGuard, zero_mul, ↓reduceIte, decide_eq_true_eq, field_zero_eq_mod]
            rw [← root_hit P.hℓH hdiv, hS]
          · simp only [hitGuard, hi, ↓reduceIte, decide_eq_true_eq]
            exact (regs_agree_iff hA P.T_lt).mpr hdiv i hi
      · have hc : c = (0, false) := by rw [← hS, root_miss P.hℓH P.hx hdiv]
        obtain ⟨i₀, hi₀, hne⟩ : ∃ i₀ : Fin s, i₀.val ≠ 0 ∧
            field A (i₀ * ℓ) ℓ ≠ field (2 ^ H) (i₀ * ℓ) ℓ := by
          by_contra hcon
          push Not at hcon
          exact hdiv ((regs_agree_iff hA P.T_lt).mp hcon)
        refine ⟨.test (missGuard s ℓ H i₀) .accept, ?_, ?_, trivial, hrk⟩
        · simp only [moves, h0, hd0, ↓reduceIte, hc, List.mem_cons, List.mem_map,
            List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
          exact Or.inr ⟨i₀, hi₀, rfl⟩
        · intro i
          by_cases hi : i = i₀
          · subst hi; simpa [missGuard] using hne
          · simp [missGuard, hi]
    · -- gather from the parent
      have hdp : d.val - 1 < H := by omega
      have hdd : d.val = d.val - 1 + 1 := by omega
      set θ' : Fin 2 := ⟨field A (bpos H (d.val - 1) + 2) 1, field_lt _ _ _⟩ with hθ'
      have hω := cω_lt hdp.le hA2 (d := d.val - 1)
      set β : Fin 8 := ⟨blk M x H (d.val - 1) (cω H (d.val - 1) A) θ' ν,
        blk_lt_eight hdp hω θ'.isLt ν⟩
      have hc : cω H d A = 2 * cω H (d.val - 1) A + θ'.val := by
        have hc' : cω H (d.val - 1 + 1) A =
            2 * cω H (d.val - 1) A + field A (bpos H (d.val - 1) + 2) 1 := by
          rw [cω_child hdp, field_top_bit]
        conv_lhs => rw [hdd]
        exact hc'
      have hpt : ptime H d (2 * cω H (d.val - 1) A + θ'.val) 0 =
          ptime H (d.val - 1) (cω H (d.val - 1) A) θ' := by
        have := ptime_child_zero' (H := H) (d.val - 1) (cω H (d.val - 1) A) θ' hdp θ'.isLt
        rwa [← hdd] at this
      refine ⟨.fork (bpos H (d.val - 1) + 2) 1 θ' (.headSet (dpred d) θ' ν β)
        (.gather (dpred d) θ' ν c β), ?_, rfl, ?_, ?_, ?_, ?_⟩
      · simp only [moves, h0, hd0, ↓reduceIte, List.mem_flatMap, List.mem_map,
          List.mem_finRange, true_and]
        exact ⟨θ', β, rfl⟩
      · exact ⟨hdp, (headBlock_iff hdp hA2 θ'.isLt β.isLt ν).mpr rfl⟩
      · have hf : field A (bpos H (d.val - 1)) 3 / 4 = θ' := by
          rw [hθ', ← field_top_bit]
        refine ⟨hdp, hf, (gather_iff hdp θ'.isLt ν c rfl hf).mpr ?_⟩
        rw [← hdd, ← h0]; exact hS
      · simp only [rank, h0, ↓reduceIte, dpred_val]
        rw [hc, hpt]
        have key : 2 * (d.val - 1) * wQ H + H + 2 < 2 * d.val * wQ H := by
          obtain ⟨e, he⟩ : ∃ e, e = d.val - 1 := ⟨_, rfl⟩
          rw [← he, show d.val = e + 1 by omega]
          simp only [wQ]; nlinarith
        omega
      · simp only [rank, h0, ↓reduceIte, dpred_val]
        rw [hc, hpt]
        have key : 2 * (d.val - 1) * wQ H + H + 2 < 2 * d.val * wQ H := by
          obtain ⟨e, he⟩ : ∃ e, e = d.val - 1 := ⟨_, rfl⟩
          rw [← he, show d.val = e + 1 by omega]
          simp only [wQ]; nlinarith
        omega
  · by_cases hdH : d.val < H
    · -- restore after a phase
      have hω := cω_lt hdH.le hA2 (d := d.val)
      set β : Fin 8 := ⟨blk M x H d (cω H d A) (ppred θ) ν, blk_lt_eight hdH hω (ppred θ).isLt ν⟩
      have hθθ := ppred_val h0
      refine ⟨.fork' (.headSet d (ppred θ) ν β) (.restore d (ppred θ) ν c β), ?_, field_zero_width _ _,
        ?_, ?_, ?_, ?_⟩
      · simp only [moves, h0, ↓reduceIte, dif_pos hdH, List.mem_map, List.mem_finRange,
          true_and]
        exact ⟨β, rfl⟩
      · exact ⟨hdH, (headBlock_iff hdH hA2 (ppred θ).isLt β.isLt ν).mpr rfl⟩
      · refine ⟨hdH, (restore_iff hdH hA2 (ppred θ).isLt ν c rfl).mpr ?_⟩
        rw [hθθ]; exact hS
      · simp only [rank, h0, ↓reduceIte]
        rw [← hθθ]
        have h := rk_lt_time (b := wG M * (H - d) + wG M - 1)
          (ptime_lt_succ (ω := cω H d A) (θ := (ppred θ).val) hdH) (lvl0_lt (M := M) d.is_le)
        omega
      · simp only [rank, h0, ↓reduceIte]
        rw [← hθθ]
        have : 2 ≤ wG M := by simp [wG]
        omega
    · -- base call
      have hd : d.val = H := by omega
      have hθ2 : θ.val = 2 := by
        have := θ.isLt
        have h1 := hS.1
        by_contra h
        exact hdH (h1 (by omega))
      set ρ : Row M := trueRow (x := x) (H := H) A with hρ
      obtain ⟨hrel, -⟩ := (baseRow_iff A ρ).mp (trueRow_rows hA2)
      have hj : A % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have hfj : field A 0 2 = A % 4 := by rw [field_zero_eq_mod]; norm_num
      rw [hd, hθ2, semCell_base2] at hS
      have h20 : ((2 : ℕ) = 0) ↔ False := by simp
      refine ⟨.step 0 2 (A % 4) (A % 4)
        (.baseCell ν ρ (cellT M x H H (A / 4) 0 ν (A % 4)) 0), ?_, hfj, ?_, ?_⟩
      · simp only [moves, ↓reduceIte, dif_neg hdH, hθ2, h20, if_false, List.mem_flatMap,
          List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
        refine ⟨ρ, mem_allRows _, _, mem_allCV _, ⟨A % 4, hj⟩, ?_, rfl⟩
        have := hrel ν
        simp only [hρ, trueRow] at this ⊢
        rw [← this]
        exact hS
      · rw [setBits_self hfj]
        exact ⟨fun i _ => trueRow_rows hA2 i, (semState_base0 A _).mpr rfl,
          (semCell_base0 A ν _).mpr rfl⟩
      · simp only [rank, h0, ↓reduceIte, hd, hθ2, h20, if_false, Nat.sub_self, mul_zero,
          zero_add, Fin.val_zero]
        rw [setBits_self hfj]
        simp only [wG]
        omega

lemma cellT_of_rel {d ω θ : ℕ} {ν : Tape M} {j : ℕ} (h : rel M x H d ω θ ν = j) :
    cellT M x H d ω θ ν j =
      ((runOn M x (ptime H d ω θ)).tape ν (off M x H d ω ν + j), true) := by
  unfold cellT cfgCell
  unfold rel hd at h
  simp only [Prod.mk.injEq, decide_eq_true_eq, true_and]
  linarith

lemma complete_state (P : Params x s ℓ H) (d : Fin (H + 1)) (θ : Fin 3) (p : ExtState M)
    {A : ℕ} (hA : A < 2 ^ (s * ℓ)) (hS : Sem M x H (.state d θ p) A) :
    ∃ mv ∈ moves M x s ℓ H (.state d θ p),
      mv.Fires ℓ (Sem M x H) (rank M H) (.state d θ p) A := by
  have hA2 := P.addr_lt hA
  change semState M x H d θ p A at hS
  by_cases h0 : θ.val = 0
  · by_cases hd0 : d.val = 0
    · have h1 : cω H 0 A = 0 := by simp [cω, Nat.div_eq_of_lt hA2]
      have hp : p = (0, none) := by
        have := hS.2; rw [hd0, h0, h1, extT_root] at this; exact this.symm
      refine ⟨.goto .accept, ?_, field_zero_width _ _, trivial, ?_⟩
      · simp [moves, h0, hd0, hp]
      · simp only [rank, h0, ↓reduceIte]
        have := wP_pos (M := M) (H := H)
        omega
    · have hdp : d.val - 1 < H := by omega
      have hdd : d.val = d.val - 1 + 1 := by omega
      set θ' : Fin 2 := ⟨field A (bpos H (d.val - 1) + 2) 1, field_lt _ _ _⟩ with hθ'
      have hc : cω H d A = 2 * cω H (d.val - 1) A + θ'.val := by
        have hc' : cω H (d.val - 1 + 1) A =
            2 * cω H (d.val - 1) A + field A (bpos H (d.val - 1) + 2) 1 := by
          rw [cω_child hdp, field_top_bit]
        conv_lhs => rw [hdd]
        exact hc'
      have hpt : ptime H d (2 * cω H (d.val - 1) A + θ'.val) 0 =
          ptime H (d.val - 1) (cω H (d.val - 1) A) θ' := by
        have := ptime_child_zero' (H := H) (d.val - 1) (cω H (d.val - 1) A) θ' hdp θ'.isLt
        rwa [← hdd] at this
      refine ⟨.step (bpos H (d.val - 1) + 2) 1 θ' θ' (.state (dpred d) θ'.castSucc p), ?_,
        rfl, ?_, ?_⟩
      · simp only [moves, h0, hd0, ↓reduceIte, List.mem_map, List.mem_finRange, true_and]
        exact ⟨θ', rfl⟩
      · rw [setBits_self rfl]
        change semState M x H (d.val - 1) θ' p A
        refine (stateUp_iff hdp θ'.isLt p rfl).mpr ?_
        rw [← hdd, ← h0]; exact hS
      · rw [setBits_self rfl]
        simp only [rank, h0, ↓reduceIte, dpred_val, Fin.val_castSucc]
        rw [hc, hpt]
        have key : 2 * (d.val - 1) * wQ H + H + 2 < 2 * d.val * wQ H := by
          obtain ⟨e, he⟩ : ∃ e, e = d.val - 1 := ⟨_, rfl⟩
          rw [← he, show d.val = e + 1 by omega]
          simp only [wQ]; nlinarith
        have := lvl1_lt_wP (M := M) (H := H) (d.val - 1)
        split_ifs <;> omega
  · by_cases hdH : d.val < H
    · have hθθ := ppred_val h0
      set e : Fin 2 := ⟨field A (bpos H d + 2) 1, field_lt _ _ _⟩
      have hv : (ppred θ).val < 2 ^ 1 := (ppred θ).isLt
      refine ⟨.step (bpos H d + 2) 1 e (ppred θ) (.state (dsucc d hdH) 2 p), ?_, rfl, ?_, ?_⟩
      · simp only [moves, h0, ↓reduceIte, dif_pos hdH, List.mem_map, List.mem_finRange,
          true_and]
        exact ⟨e, rfl⟩
      · change semState M x H (d.val + 1) 2 p _
        refine (stateDown_iff hdH (ppred θ).isLt p).mpr ?_
        rw [hθθ]; exact hS
      · have hc : cω H (d.val + 1) (setBits A (bpos H d + 2) 1 (ppred θ)) =
            2 * cω H d A + (ppred θ).val := by
          rw [cω_child hdH, ← field_top_bit, field_setBits hv,
            cω_setBits hv (by rw [bpos_add_three hdH])]
        have h2v : ((2 : Fin 3) : ℕ) = 2 := rfl
        simp only [rank, h0, ↓reduceIte, dsucc_val, h2v, OfNat.ofNat_ne_zero]
        change ptime H (d.val + 1) (cω H (d.val + 1) (setBits A (bpos H d + 2) 1 (ppred θ))) 2 *
          wK M H + _ < _
        rw [hc, ptime_child_end _ _ _ hdH, hθθ]
        have : wG M * (H - (d.val + 1)) + wG M ≤ wG M * (H - d.val) := by
          rw [show H - d.val = H - (d.val + 1) + 1 by omega]; ring_nf; omega
        have : 2 ≤ wG M := by simp [wG]
        omega
    · have hd : d.val = H := by omega
      have hθ2 : θ.val = 2 := by
        have := θ.isLt
        have h1 := hS.1
        by_contra h
        exact hdH (h1 (by omega))
      set ρ : Row M := trueRow (x := x) (H := H) A with hρ
      have h20 : ((2 : ℕ) = 0) ↔ False := by simp
      rw [hd, hθ2, semState_base2] at hS
      refine ⟨.goto (.baseState ρ 0), ?_, field_zero_width _ _, ?_, ?_⟩
      · simp only [moves, ↓reduceIte, dif_neg hdH, hθ2, h20, List.mem_map, List.mem_filter,
          decide_eq_true_eq]
        exact ⟨ρ, ⟨mem_allRows _, hS⟩, rfl⟩
      · rw [setBits_zero_width]
        exact ⟨fun i _ => trueRow_rows hA2 i, (semState_base0 A _).mpr rfl⟩
      · simp only [rank, ↓reduceIte, hd, hθ2, h20, Nat.sub_self, mul_zero, zero_add,
          Fin.val_zero]
        rw [setBits_zero_width]
        simp only [wG]
        omega

lemma complete_headIn (d : Fin (H + 1)) (θ : Fin 2) (ν : Tape M)
    (u : Fin (H + 1)) {A : ℕ} (hS : Sem M x H (.headIn d θ ν u) A) :
    ∃ mv ∈ moves M x s ℓ H (.headIn d θ ν u),
      mv.Fires ℓ (Sem M x H) (rank M H) (.headIn d θ ν u) A := by
  obtain ⟨hu, y, hy, hrel⟩ := (show semHead M x H d θ ν u A from hS)
  by_cases hu0 : u.val = 0
  · have hy0 : y = 0 := by rw [hu0] at hy; simpa using hy
    subst hy0
    rw [hu0, setBits_zero_width] at hrel
    set γ := (runOn M x (ptime H d (cω H d A) θ)).tape ν (off M x H d (cω H d A) ν + cj H d A)
    refine ⟨.goto (.cell d θ.castSucc ν (γ, true)), ?_, field_zero_width _ _, ?_, ?_⟩
    · have h0d : 0 < H - d.val := by omega
      simp only [moves, hu0, h0d, ↓reduceIte, List.mem_map, List.mem_finRange, true_and]
      exact ⟨γ, rfl⟩
    · rw [setBits_zero_width]
      refine ⟨fun _ => by omega, ?_⟩
      exact cellT_of_rel hrel
    · rw [setBits_zero_width]
      simp only [rank, Fin.val_castSucc]
      have := lvl1_lt_wP (M := M) (H := H) d
      split_ifs <;> omega
  · have hu1 : u.val - 1 + 1 = u.val := by omega
    set e : Fin 2 := ⟨field A (u.val - 1) 1, field_lt _ _ _⟩
    set e' : Fin 2 := ⟨field y (u.val - 1) 1, field_lt _ _ _⟩
    have he' : e'.val < 2 ^ 1 := e'.isLt
    have hω : cω H d (setBits A (u.val - 1) 1 e') = cω H d A := cω_setBits he' (by omega)
    refine ⟨.step (u.val - 1) 1 e e' (.headIn d θ ν (dpred u)), ?_, rfl, ?_, ?_⟩
    · simp only [moves, hu, hu0, ↓reduceIte, List.mem_flatMap, List.mem_map,
        List.mem_finRange, true_and]
      exact ⟨e, e', rfl⟩
    · refine ⟨by simp only [dpred_val]; omega, y % 2 ^ (u.val - 1),
        Nat.mod_lt _ (by positivity), ?_⟩
      simp only [dpred_val]
      rw [hω, setBits_merge he' (Nat.mod_lt _ (by positivity)), hu1]
      have hy' : y < 2 ^ (u.val - 1 + 1) := by rwa [hu1]
      rw [show (e' : ℕ) = field y (u.val - 1) 1 from rfl, split_low hy']
      exact hrel
    · simp only [rank, dpred_val]
      rw [hω]
      omega

lemma moves_complete (P : Params x s ℓ H) (L : Loc M H) {A : ℕ} (hA : A < 2 ^ (s * ℓ))
    (hS : Sem M x H L A) :
    L = .accept ∨ ∃ mv ∈ moves M x s ℓ H L, mv.Fires ℓ (Sem M x H) (rank M H) L A := by
  have hA2 := P.addr_lt hA
  cases L with
  | accept => exact Or.inl rfl
  | reject => exact hS.elim
  | query =>
    right
    have hS' : (cfgExt (runOn M x (2 ^ H))).2 = some true := hS
    have h1 : cω H 0 A = 0 := by simp [cω, Nat.div_eq_of_lt hA2]
    refine ⟨.goto (.state 0 2 (cfgExt (runOn M x (2 ^ H)))), ?_, field_zero_width _ _, ?_, ?_⟩
    · simp only [moves, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨_, ⟨mem_allExt _, hS'⟩, rfl⟩
    · rw [setBits_zero_width]
      refine ⟨by simp, ?_⟩
      change extT M x H 0 (cω H 0 A) 2 = _
      rw [h1, extT_query]
    · rw [setBits_zero_width]
      have h2v : ((2 : Fin 3) : ℕ) = 2 := rfl
      simp only [rank, h2v, OfNat.ofNat_ne_zero, ↓reduceIte, Fin.val_zero]
      change ptime H 0 (cω H 0 A) 2 * wK M H + _ < _
      rw [h1]
      have hp : ptime H 0 0 2 = 2 ^ H := by simp [ptime]
      rw [hp]
      have := lvl1_lt_wP (M := M) (H := H) 0
      have := lvl0_lt (M := M) (H := H) (d := 0) (Nat.zero_le _)
      nlinarith
  | cell d θ ν c => exact Or.inr (complete_cell P d θ ν c hA hS)
  | state d θ p => exact Or.inr (complete_state P d θ p hA hS)
  | headIn d θ ν u => exact Or.inr (complete_headIn d θ ν u hS)
  | headSet d θ ν β =>
    right
    obtain ⟨hdH, hh⟩ := hS
    have hk : bpos H d < H + 1 := by unfold bpos; omega
    refine ⟨.step (bpos H d) 3 (field A (bpos H d) 3) β (.headIn d θ ν ⟨bpos H d, hk⟩), ?_, rfl,
      hh, ?_⟩
    · simp only [moves, hdH, ↓reduceIte, List.mem_map, List.mem_finRange, true_and]
      exact ⟨⟨_, field_lt _ _ _⟩, rfl⟩
    · simp only [rank]
      rw [cω_setBits β.isLt (by rw [bpos_add_three hdH])]
      have : bpos H d ≤ H := by unfold bpos; omega
      omega
  | restore d θ ν c β =>
    right
    obtain ⟨hdH, hr⟩ := hS
    set q : Fin 8 := ⟨field A (bpos H d) 3, field_lt _ _ _⟩
    by_cases hin : sel β ≤ q.val ∧ q.val < sel β + 4
    · rw [if_pos hin] at hr
      have hv : 4 * θ.val + (q.val - sel β) < 2 ^ 3 := by have := θ.isLt; norm_num; omega
      refine ⟨.step (bpos H d) 3 q (4 * θ.val + (q.val - sel β)) (.cell (dsucc d hdH) 2 ν c),
        ?_, rfl, hr, ?_⟩
      · simp only [moves, dif_pos hdH, List.mem_map, List.mem_finRange, true_and]
        exact ⟨q, by simp [hin]⟩
      · have hc : cω H (d.val + 1) (setBits A (bpos H d) 3 (4 * θ.val + (q.val - sel β))) =
            2 * cω H d A + θ.val := by
          rw [cω_child hdH, field_setBits hv, cω_setBits hv (by rw [bpos_add_three hdH])]
          congr 1; omega
        have h2v : ((2 : Fin 3) : ℕ) = 2 := rfl
        simp only [rank, dsucc_val, h2v, OfNat.ofNat_ne_zero, ↓reduceIte]
        change ptime H (d.val + 1) (cω H (d.val + 1) (setBits A (bpos H d) 3
          (4 * θ.val + (q.val - sel β)))) 2 * wK M H + _ < _
        rw [hc, ptime_child_end _ _ _ hdH]
        have : wG M * (H - (d.val + 1)) + wG M ≤ wG M * (H - d.val) := by
          rw [show H - d.val = H - (d.val + 1) + 1 by omega]; ring_nf; omega
        have : 2 ≤ wG M := by simp [wG]
        omega
    · rw [if_neg hin] at hr
      refine ⟨.step (bpos H d) 3 q q (.cell d θ.castSucc ν c), ?_, rfl, ?_, ?_⟩
      · simp only [moves, dif_pos hdH, List.mem_map, List.mem_finRange, true_and]
        exact ⟨q, by simp [hin]⟩
      · rw [setBits_self rfl]; exact hr
      · rw [setBits_self rfl]
        simp only [rank, Fin.val_castSucc]
        have h := rk_lt_time (b := wG M * (H - d) + wG M - 2)
          (ptime_lt_succ (ω := cω H d A) (θ := θ.val) hdH) (lvl0_lt (M := M) d.is_le)
        have := lvl1_lt_wP (M := M) (H := H) d
        split_ifs <;> omega
  | gather d θ ν c β =>
    right
    obtain ⟨hdH, hf, hg⟩ := hS
    set c' : Fin 4 := ⟨field A (bpos H d) 3 % 4, Nat.mod_lt _ (by norm_num)⟩
    have hfq : field A (bpos H d) 3 = 4 * θ.val + c'.val := by
      have := Nat.div_add_mod (field A (bpos H d) 3) 4
      simp only [c']; omega
    have hv : sel β + c'.val < 2 ^ 3 := by
      have := c'.isLt; have : sel β ≤ 4 := min_le_right _ _; norm_num; omega
    refine ⟨.step (bpos H d) 3 (4 * θ.val + c'.val) (sel β + c'.val) (.cell d θ.castSucc ν c),
      ?_, hfq, hg, ?_⟩
    · simp only [moves, hdH, ↓reduceIte, List.mem_map, List.mem_finRange, true_and]
      exact ⟨c', rfl⟩
    · simp only [rank, Fin.val_castSucc]
      rw [cω_setBits hv (by rw [bpos_add_three hdH])]
      have := lvl1_lt_wP (M := M) (H := H) d
      split_ifs <;> omega
  | baseCell ν ρ old k =>
    right
    obtain ⟨hrow, hst, hold⟩ := hS
    by_cases hk : k.val < M.tapes + 1
    · refine ⟨.fork' (.setJ ⟨k.val, hk⟩ ⟨(ρ.2.1 ⟨k.val, hk⟩).val + 1, by omega⟩
          (ρ.2.2 ⟨k.val, hk⟩, true)) (.baseCell ν ρ old ⟨k.val + 1, by omega⟩), ?_,
          field_zero_width _ _, hrow _ le_rfl, ⟨fun i hi => hrow i (by simp at hi; omega),
          hst, hold⟩, ?_, ?_⟩
      · simp [moves, hk, Move.fork']
      · simp only [rank]; omega
      · simp only [rank]; omega
    · refine ⟨.fork' (.state ⟨H, by omega⟩ 0 ρ.1) (.cell ⟨H, by omega⟩ 0 ν old), ?_,
          field_zero_width _ _, hst, hold, ?_, ?_⟩
      · simp [moves, hk, Move.fork']
      · simp only [rank, Fin.val_zero, ↓reduceIte]
        have h := lvl0_lt (M := M) (H := H) (d := H) le_rfl
        have hp : ptime H H (cω H H A) 0 < ptime H H (cω H H A) 2 := by
          rw [ptime_base, ptime_base]; omega
        have := rk_lt_time (b := 0) hp (show wP M H + 2 * H * wQ H < wK M H by omega)
        omega
      · simp only [rank, Fin.val_zero, ↓reduceIte]
        have h := lvl0_lt (M := M) (H := H) (d := H) le_rfl
        have hp : ptime H H (cω H H A) 0 < ptime H H (cω H H A) 2 := by
          rw [ptime_base, ptime_base]; omega
        have := rk_lt_time (b := 0) hp (show wP M H + 2 * H * wQ H < wK M H by omega)
        omega
  | baseState ρ k =>
    right
    obtain ⟨hrow, hst⟩ := hS
    by_cases hk : k.val < M.tapes + 1
    · refine ⟨.fork' (.setJ ⟨k.val, hk⟩ ⟨(ρ.2.1 ⟨k.val, hk⟩).val + 1, by omega⟩
          (ρ.2.2 ⟨k.val, hk⟩, true)) (.baseState ρ ⟨k.val + 1, by omega⟩), ?_,
          field_zero_width _ _, hrow _ le_rfl, ⟨fun i hi => hrow i (by simp at hi; omega),
          hst⟩, ?_, ?_⟩
      · simp [moves, hk, Move.fork']
      · simp only [rank]; omega
      · simp only [rank]; omega
    · refine ⟨.goto (.state ⟨H, by omega⟩ 0 ρ.1), ?_, field_zero_width _ _, ?_, ?_⟩
      · simp [moves, hk, Move.goto]
      · rw [setBits_zero_width]; exact hst
      · rw [setBits_zero_width]
        simp only [rank, Fin.val_zero, ↓reduceIte]
        have h := lvl0_lt (M := M) (H := H) (d := H) le_rfl
        have hp : ptime H H (cω H H A) 0 < ptime H H (cω H H A) 2 := by
          rw [ptime_base, ptime_base]; omega
        have := rk_lt_time (b := 0) hp (show wP M H + 2 * H * wQ H < wK M H by omega)
        omega
  | setJ ν h c =>
    right
    have hh : h.val < 2 ^ 2 := h.isLt
    refine ⟨.step 0 2 (field A 0 2) h (.cell ⟨H, by omega⟩ 0 ν c), ?_, rfl, hS, ?_⟩
    · simp only [moves, List.mem_map, List.mem_finRange, true_and]
      exact ⟨⟨_, field_lt _ _ _⟩, rfl⟩
    · simp only [rank, Fin.val_zero, ↓reduceIte]
      rw [cω_setBits hh (by omega)]
      have h := lvl0_lt (M := M) (H := H) (d := H) le_rfl
      have hp : ptime H H (cω H H A) 0 < ptime H H (cω H H A) 2 := by
        rw [ptime_base, ptime_base]; omega
      have := rk_lt_time (b := 0) hp (show wP M H + 2 * H * wQ H < wK M H by omega)
      omega

end Lax119563Proofs.Circuits

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

/-- The verifier accepts exactly the configurations whose assertion is true. -/
theorem verifier_accepts_iff (P : Params x s ℓ H) (L : Loc M H) {A : ℕ}
    (hA : A < 2 ^ (s * ℓ)) :
    AAccepts ℓ (verifierCmds M x s ℓ H) .accept .reject L A ↔ Sem M x H L A := by
  constructor
  · intro h
    exact progCmds_sound P.hℓ (fun src _ => moves_wf P.hH src)
      (fun src _ => moves_sound P src) (fun A => show Sem M x H .accept A from trivial) h hA
  · intro hS
    exact progCmds_complete P.hℓ (rank M H) (mem_allLocs M H)
      (fun src _ => moves_wf P.hH src) (fun _ h => h)
      (fun src _ hA hS => moves_complete P src hA hS) L A hA hS

end Lax119563Proofs.Circuits
