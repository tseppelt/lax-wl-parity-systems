import Lax119563Proofs.Circuits.VerifierLemmas

/-!
# Soundness of the verifier's moves

Every move of the verifier is well-formed (its fields lie inside the address) and sound for
`Sem`: if the targets' assertions hold, so does the source's.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

@[simp] lemma dpred_val (d : Fin (H + 1)) : (dpred d).val = d.val - 1 := rfl
@[simp] lemma dsucc_val (d : Fin (H + 1)) (h : d.val < H) : (dsucc d h).val = d.val + 1 := rfl
lemma ppred_val {θ : Fin 3} (h : θ.val ≠ 0) : (ppred θ).val + 1 = θ.val := by
  have := θ.isLt
  simp only [ppred]
  omega

lemma moves_wf (hH : s * ℓ = H + 2) (L : Loc M H) :
    ∀ mv ∈ moves M x s ℓ H L, mv.WF s ℓ := by
  have h8 : ∀ q : Fin 8, q.val < 2 ^ 3 := fun q => q.isLt
  have h4 : ∀ q : Fin 4, q.val < 2 ^ 2 := fun q => q.isLt
  have h2 : ∀ q : Fin 2, q.val < 2 ^ 1 := fun q => q.isLt
  cases L with
  | accept => simp [moves]
  | reject => simp [moves]
  | query => simp [moves, Move.goto, Move.WF]
  | cell d θ ν c =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with h0 hd0 hc hdH h2'
    · rcases List.mem_cons.mp hmv with rfl | hmv
      · trivial
      · simp only [List.mem_map, List.mem_filter] at hmv
        obtain ⟨i, -, rfl⟩ := hmv; trivial
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
      subst hmv; trivial
    · simp only [List.mem_flatMap, List.mem_map] at hmv
      obtain ⟨θ', -, β, -, rfl⟩ := hmv
      refine ⟨?_, h2 θ'⟩
      unfold bpos; omega
    · simp only [List.mem_map] at hmv
      obtain ⟨β, -, rfl⟩ := hmv
      simp [Move.fork', Move.WF]
    · simp only [List.mem_flatMap, List.mem_map, List.mem_filter] at hmv
      obtain ⟨ρ, -, old, -, jj, -, rfl⟩ := hmv
      exact ⟨by omega, h4 jj, h4 jj⟩
    · simp at hmv
  | state d θ p =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with h0 hd0 hp hdH h2'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
      subst hmv; simp [Move.goto, Move.WF]
    · simp at hmv
    · simp only [List.mem_map] at hmv
      obtain ⟨θ', -, rfl⟩ := hmv
      refine ⟨?_, h2 θ', h2 θ'⟩
      unfold bpos; omega
    · simp only [List.mem_map] at hmv
      obtain ⟨e, -, rfl⟩ := hmv
      refine ⟨?_, h2 e, h2 _⟩
      unfold bpos; omega
    · simp only [List.mem_map, List.mem_filter] at hmv
      obtain ⟨ρ, -, rfl⟩ := hmv
      simp [Move.goto, Move.WF]
    · simp at hmv
  | headIn d θ ν u =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hu hu0
    · simp only [List.mem_map] at hmv
      obtain ⟨γ, -, rfl⟩ := hmv
      simp [Move.goto, Move.WF]
    · simp only [List.mem_flatMap, List.mem_map] at hmv
      obtain ⟨e, -, e', -, rfl⟩ := hmv
      exact ⟨by omega, h2 e, h2 e'⟩
    · simp at hmv
  | headSet d θ ν β =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hdH
    · simp only [List.mem_map] at hmv
      obtain ⟨q, -, rfl⟩ := hmv
      exact ⟨by unfold bpos; omega, h8 q, h8 β⟩
    · simp at hmv
  | restore d θ ν c β =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hdH
    · simp only [List.mem_map] at hmv
      obtain ⟨q, -, rfl⟩ := hmv
      split_ifs with hq
      · refine ⟨by unfold bpos; omega, h8 q, ?_⟩
        have := θ.isLt; norm_num; omega
      · exact ⟨by unfold bpos; omega, h8 q, h8 q⟩
    · simp at hmv
  | gather d θ ν c β =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hdH
    · simp only [List.mem_map] at hmv
      obtain ⟨c', -, rfl⟩ := hmv
      have := θ.isLt
      have := c'.isLt
      have : sel β ≤ 4 := min_le_right _ _
      exact ⟨by unfold bpos; omega, by norm_num; omega, by norm_num; omega⟩
    · simp at hmv
  | baseCell ν ρ old k =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv <;>
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
      subst hmv; simp [Move.fork', Move.WF]
  | baseState ρ k =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv <;>
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
      subst hmv; simp [Move.fork', Move.goto, Move.WF]
  | setJ ν h c =>
    intro mv hmv
    simp only [moves, List.mem_map] at hmv
    obtain ⟨q, -, rfl⟩ := hmv
    exact ⟨by omega, h4 q, h4 h⟩

/-! ## Base and root claims -/

lemma semCell_base0 (A : ℕ) (ν : Tape M) (c : CellVal M) :
    semCell M x H H 0 ν c A ↔ cellT M x H H (A / 4) 0 ν (A % 4) = c := by
  simp [semCell, cω_base, cj_base]

lemma semState_base0 (A : ℕ) (p : ExtState M) :
    semState M x H H 0 p A ↔ extT M x H H (A / 4) 0 = p := by
  simp [semState, cω_base]

lemma semCell_base2 (A : ℕ) (ν : Tape M) (c : CellVal M) :
    semCell M x H H 2 ν c A ↔
      nextCell (extT M x H H (A / 4) 0) (scanT M x (A / 4)) ν (rel M x H H (A / 4) 0 ν)
        ((A % 4 : ℕ) : ℤ) (cellT M x H H (A / 4) 0 ν (A % 4)) = c := by
  simp [semCell, cω_base, cj_base, cellT_base]

lemma semState_base2 (A : ℕ) (p : ExtState M) :
    semState M x H H 2 p A ↔ nextExt (extT M x H H (A / 4) 0) (scanT M x (A / 4)) = p := by
  simp [semState, cω_base, extT_base]

lemma baseRow_iff (A : ℕ) (ρ : Row M) :
    (∀ i : Tape M, semCell M x H H 0 i (ρ.2.2 i, true) (setBits A 0 2 ((ρ.2.1 i).val + 1))) ↔
      (∀ i, rel M x H H (A / 4) 0 i = (ρ.2.1 i).val + 1) ∧ scanT M x (A / 4) = ρ.2.2 := by
  have hh : ∀ i, (ρ.2.1 i).val + 1 < 2 ^ 2 := fun i => by have := (ρ.2.1 i).isLt; norm_num; omega
  simp only [fun i => baseHead_iff (x := x) (H := H) (A := A) (hh i) i (ρ.2.2 i)]
  constructor
  · intro h
    exact ⟨fun i => by exact_mod_cast (h i).1, funext fun i => (h i).2⟩
  · rintro ⟨h1, h2⟩ i
    exact ⟨by rw [h1 i]; push_cast; ring, by rw [h2]⟩

lemma semCell_root {A : ℕ} (hA : A < 2 ^ (H + 2)) (ν : Tape M) (c : CellVal M) :
    semCell M x H 0 0 ν c A ↔ cfgCell (init M x) ν ((A : ℤ) - 2 ^ H) = c := by
  have h1 : cω H 0 A = 0 := by simp [cω, Nat.div_eq_of_lt hA]
  have h2 : cj H 0 A = A := by simp [cj, Nat.mod_eq_of_lt hA]
  simp [semCell, h1, h2, cellT_root]

lemma root_hit {A : ℕ} (hℓH : ℓ ≤ H) (h : A / 2 ^ ℓ = 2 ^ H / 2 ^ ℓ) :
    (A : ℤ) - 2 ^ H = ((A % 2 ^ ℓ : ℕ) : ℤ) := by
  have hd : 2 ^ ℓ ∣ 2 ^ H := pow_dvd_pow 2 hℓH
  have e1 := Nat.div_add_mod A (2 ^ ℓ)
  have e2 := Nat.div_mul_cancel hd
  rw [h] at e1
  have : A = 2 ^ H + A % 2 ^ ℓ := by rw [Nat.mul_comm] at e1; omega
  have h3 : (A : ℤ) = 2 ^ H + ((A % 2 ^ ℓ : ℕ) : ℤ) := by exact_mod_cast this
  linarith

lemma root_miss {A : ℕ} (hℓH : ℓ ≤ H) (hx : x.length < 2 ^ ℓ)
    (h : A / 2 ^ ℓ ≠ 2 ^ H / 2 ^ ℓ) (ν : Tape M) :
    cfgCell (init M x) ν ((A : ℤ) - 2 ^ H) = (0, false) := by
  apply init_cell_outside
  by_contra hc
  push Not at hc
  apply h
  have hd : 2 ^ ℓ ∣ 2 ^ H := pow_dvd_pow 2 hℓH
  have hx' : ((x.length : ℕ) : ℤ) < 2 ^ ℓ := by exact_mod_cast hx
  have hpos : (0 : ℤ) < 2 ^ ℓ := by positivity
  -- `A - 2^H ∈ [0, 2^ℓ)`
  have hge : 2 ^ H ≤ A := by
    by_contra hlt
    push Not at hlt
    have : (A : ℤ) < 2 ^ H := by exact_mod_cast hlt
    linarith [hc.1]
  have hlt : A - 2 ^ H < 2 ^ ℓ := by
    by_contra hnot
    have h1 : 2 ^ ℓ ≤ A - 2 ^ H := by omega
    have h2 : ((2 ^ ℓ : ℕ) : ℤ) ≤ ((A - 2 ^ H : ℕ) : ℤ) := by exact_mod_cast h1
    push_cast [hge] at h2
    have := hc.2 (by linarith)
    linarith
  obtain ⟨k, hk⟩ := hd
  have : A = 2 ^ ℓ * k + (A - 2 ^ H) := by omega
  rw [hk, this, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hlt, add_zero,
    Nat.mul_div_cancel_left _ (by positivity)]

/-! ## Soundness of the moves -/

/-- Standing hypotheses on the parameters: the address has `s ℓ = H + 2` bits, and the input
fits into register `0`. -/
structure Params (x : List Bool) (s ℓ H : ℕ) : Prop where
  hH : s * ℓ = H + 2
  hℓ : 0 < ℓ
  hℓH : ℓ ≤ H
  hx : x.length < 2 ^ ℓ

lemma Params.addr_lt (P : Params x s ℓ H) {A : ℕ} (hA : A < 2 ^ (s * ℓ)) : A < 2 ^ (H + 2) :=
  P.hH ▸ hA

lemma Params.s_pos (P : Params x s ℓ H) : 0 < s := by
  rcases Nat.eq_zero_or_pos s with h | h
  · have := P.hH; simp [h] at this
  · exact h

lemma Params.T_lt (P : Params x s ℓ H) : 2 ^ H < 2 ^ (s * ℓ) := by
  rw [P.hH]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)

lemma sound_cell (P : Params x s ℓ H) (d : Fin (H + 1)) (θ : Fin 3) (ν : Tape M)
    (c : CellVal M) : ∀ mv ∈ moves M x s ℓ H (.cell d θ ν c),
      mv.Sound ℓ (Sem M x H) (.cell d θ ν c) := by
  intro mv hmv
  simp only [moves] at hmv
  split_ifs at hmv with h0 hd0 hc hdH h2'
  · -- root, with the miss tests
    rcases List.mem_cons.mp hmv with rfl | hmv
    · intro A hA hen _
      have e0 := hen ⟨0, P.s_pos⟩
      simp only [hitGuard, zero_mul, ↓reduceIte, decide_eq_true_eq, field_zero_eq_mod] at e0
      have eo : ∀ i : Fin s, i.val ≠ 0 → field A (i * ℓ) ℓ = field (2 ^ H) (i * ℓ) ℓ :=
        fun i hi => by simpa [hitGuard, hi] using hen i
      have hdiv := (regs_agree_iff hA P.T_lt).mp eo
      show semCell M x H d θ ν c A
      rw [hd0, h0, semCell_root (P.addr_lt hA), root_hit P.hℓH hdiv, e0]
    · simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq] at hmv
      obtain ⟨i₀, hi₀, rfl⟩ := hmv
      intro A hA hen _
      have e := hen i₀
      simp only [missGuard, ↓reduceIte, decide_eq_true_eq] at e
      have hdiv : A / 2 ^ ℓ ≠ 2 ^ H / 2 ^ ℓ := fun h =>
        e ((regs_agree_iff hA P.T_lt).mpr h i₀ hi₀)
      show semCell M x H d θ ν c A
      rw [hd0, h0, semCell_root (P.addr_lt hA), root_miss P.hℓH P.hx hdiv, hc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
    subst hmv
    intro A hA hen _
    have e0 := hen ⟨0, P.s_pos⟩
    simp only [hitGuard, zero_mul, ↓reduceIte, decide_eq_true_eq, field_zero_eq_mod] at e0
    have eo : ∀ i : Fin s, i.val ≠ 0 → field A (i * ℓ) ℓ = field (2 ^ H) (i * ℓ) ℓ :=
      fun i hi => by simpa [hitGuard, hi] using hen i
    have hdiv := (regs_agree_iff hA P.T_lt).mp eo
    show semCell M x H d θ ν c A
    rw [hd0, h0, semCell_root (P.addr_lt hA), root_hit P.hℓH hdiv, e0]
  · -- gather from the parent
    simp only [List.mem_flatMap, List.mem_map] at hmv
    obtain ⟨θ', -, β, -, rfl⟩ := hmv
    intro A hA _ hS₁ hS₂
    have hdp : d.val - 1 < H := by omega
    obtain ⟨-, hh⟩ := hS₁
    obtain ⟨-, hf, hg⟩ := hS₂
    simp only [dpred_val] at hh hf hg
    have hblk := (headBlock_iff hdp (P.addr_lt hA) θ'.isLt β.isLt ν).mp hh
    have := (gather_iff hdp θ'.isLt ν c hblk hf).mp hg
    show semCell M x H d θ ν c A
    rwa [h0, show d.val = d.val - 1 + 1 by omega]
  · -- restore after a phase
    simp only [List.mem_map] at hmv
    obtain ⟨β, -, rfl⟩ := hmv
    intro A hA _ hS₁ hS₂
    obtain ⟨-, hh⟩ := hS₁
    obtain ⟨-, hr⟩ := hS₂
    have hblk := (headBlock_iff hdH (P.addr_lt hA) (ppred θ).isLt β.isLt ν).mp hh
    have := (restore_iff hdH (P.addr_lt hA) (ppred θ).isLt ν c hblk).mp hr
    show semCell M x H d θ ν c A
    rwa [ppred_val h0] at this
  · -- base call
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at hmv
    obtain ⟨ρ, -, old, -, jj, ⟨-, hnext⟩, rfl⟩ := hmv
    intro A hA hf hS
    rw [setBits_self hf] at hS
    obtain ⟨hrow, hst, hold⟩ := hS
    have hd : d.val = H := by omega
    have hθ : θ.val = 2 := by omega
    obtain ⟨hrel, hscan⟩ := (baseRow_iff A ρ).mp fun i => hrow i (Nat.zero_le _)
    rw [semState_base0] at hst
    have hj : A % 4 = jj.val := by rw [← hf, field_zero_eq_mod]; norm_num
    rw [semCell_base0, hj] at hold
    show semCell M x H d θ ν c A
    rw [hd, hθ, semCell_base2, hst, hscan, hrel ν, hj, hold]
    exact_mod_cast hnext
  · simp at hmv

end Lax119563Proofs.Circuits
