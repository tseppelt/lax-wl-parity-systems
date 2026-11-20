import Lax119563Proofs.Reduction.CostGn
import Lax119563Proofs.Reduction.CmdEnum

/-!
# Fits and cost of the command enumerator

* `LinX Γ a`: `a` is linear (`P 0 1`) and reads only the levels of `Γ`; `TyB Γ a τ` likewise for
  a class `τ`.
* `SLoc.codeX_tyB`: location numbers are `P 0 5` (two digits of a linear radix and three
  of a constant one, so in fact `P 0 3`), given linear
  runtime fields (`SLoc.Ok`); `SMv.recX_tyB`: the eight numbers of a move have the classes
  `recTys` (the mask is `big`); `SKind.brs_ok`: all branches of all kinds are typed.
* **`hasCost_cmdEnum`**: if the body has `HasCost (τs ++ cmdTys) body e d`, then the command
  enumerator has `HasCost τs (cmdEnum M s b HX RX body) e (d + 6)` (five loops over the
  digits and one counting loop for the subtractions), for linear `HX, RX`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Xp Ty Gn

variable {M : Machine} {s : ℕ}

/-- Typed in class `τ` and reading only the levels of `Γ`. -/
def TyB (Γ : List Ty) (a : Xp) (τ : Ty) : Prop := HasTy Γ a τ ∧ a.Bnd Γ.length

/-- Linear and reading only the levels of `Γ`. -/
abbrev LinX (Γ : List Ty) (a : Xp) : Prop := TyB Γ a (P 0 1)

variable {Γ : List Ty}

lemma TyB.le {a : Xp} {τ τ' : Ty} (h : TyB Γ a τ) (hτ : Ty.Le τ τ') : TyB Γ a τ' :=
  ⟨h.1.le hτ, h.2⟩

lemma TyB.weaken {a : Xp} {τ : Ty} (h : TyB Γ a τ) (us : List Ty) : TyB (Γ ++ us) a τ :=
  ⟨h.1.weaken h.2 us, Xp.Bnd.mono (by simp) h.2⟩

lemma tyB_const (c : ℕ) : TyB Γ (const c) (P 0 0) := ⟨hasTy_const c, trivial⟩

lemma linX_const (c : ℕ) : LinX Γ (const c) := (tyB_const c).le ⟨le_rfl, by omega⟩

lemma tyB_var {j : ℕ} {τ : Ty} (us : List Ty) (h : us.getD j (P 0 0) = τ) (hj : j < us.length) :
    TyB (Γ ++ us) (var (Γ.length + j)) τ := by
  refine ⟨hasTy_var' ?_, show Γ.length + j < (Γ ++ us).length by simp; omega⟩
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simpa using h

lemma linX_add_const {a : Xp} (h : LinX Γ a) (c : ℕ) : LinX Γ (add a (const c)) :=
  ⟨hasTy_add h.1 (linX_const c).1, h.2, trivial⟩

lemma linX_add {a b : Xp} (ha : LinX Γ a) (hb : LinX Γ b) : LinX Γ (add a b) :=
  ⟨hasTy_add ha.1 hb.1, ha.2, hb.2⟩

lemma tyB_lt {a b : Xp} {τa τb : Ty} (ha : TyB Γ a τa) (hb : TyB Γ b τb) :
    TyB Γ (Xp.lt a b) (P 0 0) := ⟨hasTy_lt ha.1 hb.1, ha.2, hb.2⟩

lemma tyB_eq {a b : Xp} {τa τb : Ty} (ha : TyB Γ a τa) (hb : TyB Γ b τb) :
    TyB Γ (Xp.eq a b) (P 0 0) :=
  ⟨hasTy_eq ha.1 hb.1, ⟨⟨⟨ha.2, hb.2⟩, ⟨hb.2, ha.2⟩⟩, trivial⟩⟩

lemma tyB_and {a b : Xp} {τa τb : Ty} (ha : TyB Γ a τa) (hb : TyB Γ b τb) :
    TyB Γ (Xp.and a b) (P 0 0) := ⟨hasTy_and ha.1 hb.1, trivial, ha.2, hb.2⟩

lemma tyB_not {a : Xp} {τ : Ty} (ha : TyB Γ a τ) : TyB Γ (Xp.not a) (P 0 0) :=
  ⟨hasTy_not ha.1, ha.2, trivial⟩

lemma tyB_mulC {a : Xp} {e d : ℕ} (ha : TyB Γ a (P e d)) (c : ℕ) : TyB Γ (mulC c a) (P e d) :=
  ⟨hasTy_mulC ha.1 c, Xp.bnd_mulC ha.2 c⟩

/-- `a + b R` with `a, R` linear and `b` of degree `d`. -/
lemma tyB_horner {a b R : Xp} {d : ℕ} (ha : LinX Γ a) (hb : TyB Γ b (P 0 d)) (hR : LinX Γ R)
    (hd : 1 ≤ d) : TyB Γ (add a (mul b R)) (P 0 (d + 1)) := by
  have hm : HasTy Γ (mul b R) (P 0 (d + 1)) := by
    simpa using hasTy_mul hb.1 hR.1 hR.1
  exact ⟨hasTy_add (ha.1.le ⟨le_rfl, by omega⟩) hm, ha.2, Xp.bnd_mul hb.2 hR.2⟩

/-- `a + c b` with `a` linear, `b` of degree `d ≥ 1` and a constant `c`. -/
lemma tyB_hornerC {a b : Xp} {d : ℕ} (ha : LinX Γ a) (hb : TyB Γ b (P 0 d)) (c : ℕ)
    (hd : 1 ≤ d) : TyB Γ (add a (mulC c b)) (P 0 d) :=
  ⟨hasTy_add (ha.1.le ⟨le_rfl, hd⟩) (tyB_mulC hb c).1, ha.2, (tyB_mulC hb c).2⟩

lemma linX_minX {a h : Xp} (ha : LinX Γ a) (hh : LinX Γ h) : LinX Γ (minX a h) := by
  have hc : TyB Γ (Xp.lt a (add h (const 1))) (P 0 0) := tyB_lt ha (linX_add_const hh 1)
  have hc' : TyB Γ (Xp.not (Xp.lt a (add h (const 1)))) (P 0 0) := tyB_not hc
  have m1 : HasTy Γ (mul a (Xp.lt a (add h (const 1)))) (P 0 1) := by
    simpa using hasTy_mul ha.1 hc.1 (hc.1.le ⟨le_rfl, by omega⟩)
  have m2 : HasTy Γ (mul h (Xp.not (Xp.lt a (add h (const 1))))) (P 0 1) := by
    simpa using hasTy_mul hh.1 hc'.1 (hc'.1.le ⟨le_rfl, by omega⟩)
  exact ⟨hasTy_add m1 m2, bnd_minX ha.2 hh.2⟩

/-! ## Locations and moves -/

namespace SLoc

/-- The runtime fields are linear. -/
def Ok (Γ : List Ty) : SLoc M → Prop
  | cell d .. => LinX Γ d
  | state d .. => LinX Γ d
  | headIn d _ _ u => LinX Γ d ∧ LinX Γ u
  | headSet d .. => LinX Γ d
  | restore d .. => LinX Γ d
  | gather d .. => LinX Γ d
  | _ => True

lemma flds_lin {HX : Xp} (hH : LinX Γ HX) {L : SLoc M} (h : L.Ok Γ) :
    LinX Γ (L.flds HX).1 ∧ LinX Γ (L.flds HX).2.1 ∧ LinX Γ (L.flds HX).2.2.1 ∧
      LinX Γ (L.flds HX).2.2.2.1 ∧ LinX Γ (L.flds HX).2.2.2.2 := by
  cases L <;> simp only [flds] <;>
    first
    | exact ⟨linX_const _, linX_const _, linX_const _, linX_const _, linX_const _⟩
    | exact ⟨linX_minX h hH, linX_const _, linX_const _, linX_const _, linX_const _⟩
    | exact ⟨linX_minX h.1 hH, linX_const _, linX_const _, linX_minX h.2 hH, linX_const _⟩

lemma codeX_tyB {R HX : Xp} (hR : LinX Γ R) (hH : LinX Γ HX) {L : SLoc M} (h : L.Ok Γ) :
    TyB Γ (L.codeX R HX) (P 0 5) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := flds_lin hH h
  have t4 := tyB_horner f4 f5 hR le_rfl
  have t3 := tyB_hornerC f3 t4 (cM M) (by omega)
  have t2 := tyB_hornerC f2 t3 (cM M) (by omega)
  have t1 := (tyB_horner f1 t2 hR (by omega)).le (show Ty.Le (P 0 3) (P 0 5) from ⟨le_rfl, by omega⟩)
  have := tyB_mulC t1 16
  exact ⟨hasTy_add ((hasTy_const _).le ⟨le_rfl, by omega⟩) this.1, trivial, this.2⟩

end SLoc

namespace SMv

/-- The iteration counts and the locations are linear. -/
def Ok (Γ : List Ty) : SMv M s → Prop
  | step k _ _ _ dst => LinX Γ k ∧ dst.Ok Γ
  | fork k _ _ l r => LinX Γ k ∧ l.Ok Γ ∧ r.Ok Γ
  | hit _ _ dst => dst.Ok Γ
  | miss _ dst => dst.Ok Γ

end SMv

/-- The classes of the eight numbers of a move. -/
def recTys : List Ty := [P 0 0, .big, P 0 5, P 0 5, P 0 0, P 0 1, P 0 0, P 0 0]

namespace SMv

lemma recX_tyB {R HX : Xp} (hR : LinX Γ R) (hH : LinX Γ HX) {m : SMv M s} (h : m.Ok Γ) :
    List.Forall₂ (fun a τ => TyB Γ a τ) (m.recX R HX) recTys := by
  have c0 : ∀ c, TyB Γ (const c) (P 0 0) := fun c => tyB_const c
  have c5 : ∀ c, TyB Γ (const c) (P 0 5) := fun c => (tyB_const c).le ⟨le_rfl, by omega⟩
  have c1 : ∀ c, TyB Γ (const c) (P 0 1) := fun c => linX_const c
  cases m with
  | step k m q v dst =>
    simp only [recX, recTys]
    exact .cons (c0 _) (.cons ⟨hasTy_shl (hasTy_const _) h.1.1, trivial, h.1.2⟩
      (.cons (SLoc.codeX_tyB hR hH h.2) (.cons (c5 _) (.cons (c0 _) (.cons h.1
        (.cons (c0 _) (.cons (c0 _) .nil)))))))
  | fork k m q l r =>
    simp only [recX, recTys]
    exact .cons (c0 _) (.cons ((tyB_const _).le (Ty.le_big _))
      (.cons (SLoc.codeX_tyB hR hH h.2.1) (.cons (SLoc.codeX_tyB hR hH h.2.2) (.cons (c0 _)
        (.cons h.1 (.cons (c0 _) (.cons (c0 _) .nil)))))))
  | hit ν c dst =>
    simp only [recX, recTys]
    exact .cons (c0 _) (.cons ((tyB_const _).le (Ty.le_big _))
      (.cons (SLoc.codeX_tyB hR hH h) (.cons (c5 _) (.cons (c0 _)
        (.cons (c1 _) (.cons (c0 _) (.cons (c0 _) .nil)))))))
  | miss i dst =>
    simp only [recX, recTys]
    exact .cons (c0 _) (.cons ((tyB_const _).le (Ty.le_big _))
      (.cons (SLoc.codeX_tyB hR hH h) (.cons (c5 _) (.cons (c0 _)
        (.cons (c1 _) (.cons (c0 _) (.cons (c0 _) .nil)))))))

end SMv

/-- The runtime values are linear. -/
structure RVals.Lin (Γ : List Ty) (V : RVals) : Prop where
  d : LinX Γ V.d
  u : LinX Γ V.u
  dm1 : LinX Γ V.dm1
  um1 : LinX Γ V.um1
  hd1 : LinX Γ V.hd1
  hd2 : LinX Γ V.hd2
  H : LinX Γ V.H

lemma SKind.brs_ok {V : RVals} (hV : V.Lin Γ) (K : SKind M) :
    ∀ br ∈ K.brs (s := s) V, TyB Γ br.1 (P 0 0) ∧ ∀ m ∈ br.2, SMv.Ok Γ m := by
  have c1 : TyB Γ (const 1) (P 0 0) := tyB_const 1
  have L0 : LinX Γ (const 0) := linX_const 0
  have Ld1 : LinX Γ (add V.d (const 1)) := linX_add_const hV.d 1
  have Lh2 : LinX Γ (add V.hd1 (const 2)) := linX_add_const hV.hd1 2
  cases K with
  | accept => simp [SKind.brs]
  | reject => simp [SKind.brs]
  | query =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨c1, fun m hm => ?_⟩
    simp only [List.mem_map] at hm
    obtain ⟨p, -, rfl⟩ := hm
    exact ⟨L0, L0⟩
  | cell θ ν c =>
    simp only [SKind.brs]
    by_cases hθ : θ.val = 0
    · rw [if_pos hθ]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro br (rfl | rfl)
      · refine ⟨tyB_eq hV.d (tyB_const 0), fun m hm => ?_⟩
        simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · trivial
        · by_cases hc : c = (0, false)
          · rw [if_pos hc] at hm
            simp only [List.mem_map] at hm
            obtain ⟨i, -, rfl⟩ := hm
            trivial
          · rw [if_neg hc] at hm; simp at hm
      · refine ⟨c1, fun m hm => ?_⟩
        simp only [List.mem_flatMap, List.mem_map] at hm
        obtain ⟨θ', -, β, -, rfl⟩ := hm
        exact ⟨hV.hd2, hV.dm1, hV.dm1⟩
    · rw [if_neg hθ]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro br (rfl | rfl)
      · refine ⟨tyB_lt hV.d hV.H, fun m hm => ?_⟩
        simp only [List.mem_map] at hm
        obtain ⟨β, -, rfl⟩ := hm
        exact ⟨L0, hV.d, hV.d⟩
      · refine ⟨c1, fun m hm => ?_⟩
        by_cases h2 : θ.val = 2
        · rw [if_pos h2] at hm
          simp only [List.mem_flatMap, List.mem_map] at hm
          obtain ⟨_, -, _, -, jj, -, rfl⟩ := hm
          exact ⟨L0, trivial⟩
        · rw [if_neg h2] at hm; simp at hm
  | state θ p =>
    simp only [SKind.brs]
    by_cases hθ : θ.val = 0
    · rw [if_pos hθ]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro br (rfl | rfl)
      · refine ⟨tyB_eq hV.d (tyB_const 0), fun m hm => ?_⟩
        by_cases hp : p = (0, none)
        · rw [if_pos hp] at hm
          simp only [List.mem_singleton] at hm; subst hm; exact ⟨L0, trivial⟩
        · rw [if_neg hp] at hm; simp at hm
      · refine ⟨c1, fun m hm => ?_⟩
        simp only [List.mem_map] at hm
        obtain ⟨θ', -, rfl⟩ := hm
        exact ⟨hV.hd2, hV.dm1⟩
    · rw [if_neg hθ]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro br (rfl | rfl)
      · refine ⟨tyB_lt hV.d hV.H, fun m hm => ?_⟩
        simp only [List.mem_map] at hm
        obtain ⟨e, -, rfl⟩ := hm
        exact ⟨Lh2, Ld1⟩
      · refine ⟨c1, fun m hm => ?_⟩
        by_cases h2 : θ.val = 2
        · rw [if_pos h2] at hm
          simp only [List.mem_map] at hm
          obtain ⟨_, -, rfl⟩ := hm
          exact ⟨L0, trivial⟩
        · rw [if_neg h2] at hm; simp at hm
  | headIn θ ν =>
    simp only [SKind.brs, List.mem_cons, List.not_mem_nil, or_false]
    rintro br (rfl | rfl)
    · refine ⟨tyB_and (tyB_lt (linX_add hV.u hV.d) hV.H) (tyB_eq hV.u (tyB_const 0)),
        fun m hm => ?_⟩
      simp only [List.mem_map] at hm
      obtain ⟨γ, -, rfl⟩ := hm
      exact ⟨L0, hV.d⟩
    · refine ⟨tyB_lt (linX_add hV.u hV.d) hV.H, fun m hm => ?_⟩
      simp only [List.mem_flatMap, List.mem_map] at hm
      obtain ⟨e, -, e', -, rfl⟩ := hm
      exact ⟨hV.um1, hV.d, hV.um1⟩
  | headSet θ ν β =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨tyB_lt hV.d hV.H, fun m hm => ?_⟩
    simp only [List.mem_map] at hm
    obtain ⟨q, -, rfl⟩ := hm
    exact ⟨hV.hd1, hV.d, hV.hd1⟩
  | restore θ ν c β =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨tyB_lt hV.d hV.H, fun m hm => ?_⟩
    simp only [List.mem_map] at hm
    obtain ⟨q, -, rfl⟩ := hm
    split_ifs
    · exact ⟨hV.hd1, Ld1⟩
    · exact ⟨hV.hd1, hV.d⟩
  | gather θ ν c β =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨tyB_lt hV.d hV.H, fun m hm => ?_⟩
    simp only [List.mem_map] at hm
    obtain ⟨q, -, rfl⟩ := hm
    exact ⟨hV.hd1, hV.d⟩
  | baseCell ν ρ old k =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨c1, fun m hm => ?_⟩
    split_ifs at hm
    · simp only [List.mem_singleton] at hm; subst hm; exact ⟨L0, trivial, trivial⟩
    · simp only [List.mem_singleton] at hm; subst hm; exact ⟨L0, hV.H, hV.H⟩
  | baseState ρ k =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨c1, fun m hm => ?_⟩
    split_ifs at hm
    · simp only [List.mem_singleton] at hm; subst hm; exact ⟨L0, trivial, trivial⟩
    · simp only [List.mem_singleton] at hm; subst hm; exact ⟨L0, hV.H⟩
  | setJ ν h c =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨c1, fun m hm => ?_⟩
    simp only [List.mem_map] at hm
    obtain ⟨q, -, rfl⟩ := hm
    exact ⟨L0, hV.H⟩


lemma SKind.sloc_ok {d u : Xp} (hd : LinX Γ d) (hu : LinX Γ u) (K : SKind M) :
    (K.sloc d u).Ok Γ := by
  cases K
  all_goals first | trivial | exact hd | exact ⟨hd, hu⟩

/-! ## The enumerator -/

namespace Gn

lemma hasCost_firstL {α : Type} {c : α → Xp} {f : α → Gn} {e d : ℕ} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ τ, HasTy Γ (c a) τ) → (∀ a ∈ l, HasCost Γ (f a) e d) →
      HasCost Γ (firstL c f l) e d
  | [], _, _ => hasCost_skip.mono (Nat.zero_le _) (Nat.zero_le _)
  | a :: l, hc, hf => by
    obtain ⟨τ, hτ⟩ := hc a (by simp)
    exact hasCost_ite hτ (hf a (by simp))
      (hasCost_firstL (fun a' ha' => hc a' (by simp [ha'])) fun a' ha' => hf a' (by simp [ha']))

lemma hasCost_brGen {RX HX : Xp} (hR : LinX Γ RX) (hH : LinX Γ HX) {body : Gn} {e d : ℕ}
    (hbody : HasCost (Γ ++ P 0 0 :: recTys) body e d) :
    ∀ brs : List (Xp × List (SMv M s)),
      (∀ br ∈ brs, TyB Γ br.1 (P 0 0) ∧ ∀ m ∈ br.2, SMv.Ok Γ m) →
      HasCost Γ (brGen RX HX body brs) e d
  | [], _ => hasCost_skip.mono (Nat.zero_le _) (Nat.zero_le _)
  | (c, ms) :: rest, h => by
    have h0 := h (c, ms) (by simp)
    refine hasCost_ite h0.1.1 (hasCost_seqL fun g hg => ?_)
      (hasCost_brGen hR hH hbody rest fun br hbr => h br (by simp [hbr]))
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    have hm : p.1 ∈ ms := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
    have hT : TyL (Γ ++ []) (const p.2 :: p.1.recX RX HX) (P 0 0 :: recTys) :=
      tyL_of_forall₂ (.cons (tyB_const p.2) (SMv.recX_tyB hR hH (h0.2 _ hm))) []
    exact hasCost_bindL (by simpa using hT) hbody

end Gn

/-- The classes of the digits and differences (levels `b, …, b + 13`). -/
def digTys : List Ty :=
  [P 0 1, P 0 1, P 0 1, P 0 1, P 0 1, P 0 1, P 0 1, P 0 1, P 0 1, P 0 1, P 0 1, P 0 1, P 0 1,
    P 0 1]

/-- The classes of the levels `b, …, b + 24` of the body of the command enumerator. -/
def cmdTys : List Ty := digTys ++ [P 0 5, P 0 5] ++ P 0 0 :: recTys

lemma hasCost_loop' {τs l : List Ty} {lim : Xp} {g : Gn} {e₀ d₀ e d : ℕ}
    (hl : HasTy (τs ++ l) lim (P e₀ d₀)) (hg : HasCost (τs ++ (l ++ [P e₀ d₀, P e₀ d₀])) g e d) :
    HasCost (τs ++ l) (Gn.loop lim g) (e₀ + e) (d₀ + d) :=
  hasCost_loop hl (by rwa [List.append_assoc])

end Lax119563Proofs.Reduction
