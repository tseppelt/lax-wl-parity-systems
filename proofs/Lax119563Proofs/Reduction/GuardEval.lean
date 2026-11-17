import Lax119563Proofs.Reduction.SchGen

/-!
# Numeric evaluation of guards

`gEval x ℓ H gd i v`: the value of the guard described by the numbers `gd` (`GDescQ`) on
block `i < s` with register value `v`, in terms of numbers only (`gEval_spec`). The hit guard
reads the input through `initCV x ν v`, the number `encCV` of cell `v` of tape `ν` in the
initial configuration (`encCV_init`), which only needs `inBit x v`.

`mem_domain_of_schRec`: the domain of a schema with record `rec` is
`{(i, b) | i = s ∨ gEval x ℓ H (rec.drop 5) i (regVal b)}`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

variable {M : Machine} {s : ℕ}

/-- The field guard on a natural block number. -/
def fieldOK (ℓ k m q i v : ℕ) : Bool :=
  decide (∀ t < m, (k + t) / ℓ = i → v.testBit ((k + t) % ℓ) = q.testBit t)

/-- The number of cell `v` of tape `ν` in the initial configuration on input `x`. -/
def initCV (x : List Bool) (ν v : ℕ) : ℕ :=
  (if v = 0 then 1 else 0) + 2 * (if ν = 0 then inBit x v else 0)

lemma encCV_init (x : List Bool) (ν : Tape M) (v : ℕ) :
    encCV (cfgCell (init M x) ν (v : ℤ)) = initCV x ν.val v := by
  unfold encCV cfgCell initCV pack
  have hh : decide ((init M x).head ν = (v : ℤ)) = decide (v = 0) := by
    show decide ((0 : ℤ) = (v : ℤ)) = decide (v = 0)
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  rw [hh]
  congr 1
  · by_cases hv : v = 0 <;> simp [hv]
  · congr 1
    by_cases hν : ν.val = 0
    · have hν' : ν = 0 := Fin.ext hν
      rw [if_pos hν]
      simp only [init, hν', true_and, Int.natCast_nonneg, if_true, Int.toNat_natCast]
      unfold inBit
      rcases Nat.lt_or_ge v x.length with hv | hv
      · rw [List.getElem?_eq_getElem hv, List.drop_eq_getElem_cons hv]
        cases x[v] <;> simp [rdVal]
      · rw [List.getElem?_eq_none hv, List.drop_eq_nil_of_le hv]
        simp [rdVal]
    · have hν' : ν ≠ 0 := fun h => hν (by rw [h]; rfl)
      rw [if_neg hν]
      simp [init, hν']

/-- The numeric guard. -/
def gEval (x : List Bool) (ℓ H : ℕ) (gd : List ℕ) (i v : ℕ) : Bool :=
  match gd.getD 0 0 with
  | 0 => fieldOK ℓ (gd.getD 1 0) (gd.getD 2 0) (gd.getD 3 0) i v
  | 1 => if i = 0 then decide (initCV x (gd.getD 1 0) v = gd.getD 2 0)
      else decide (v = field (2 ^ H) (i * ℓ) ℓ)
  | 2 => if i = gd.getD 1 0 then decide (v ≠ field (2 ^ H) (i * ℓ) ℓ) else true
  | _ => decide (v = 0)

lemma gEval_spec {x : List Bool} {ℓ H : ℕ} {g : Fin s → ℕ → Bool} {gd : List ℕ}
    (h : GDescQ M x s ℓ H g gd) (i : Fin s) (v : ℕ) : g i v = gEval x ℓ H gd i.val v := by
  rcases h with (⟨h0, rfl⟩ | ⟨h0, ν, c, h1, h2, rfl⟩ | ⟨h0, i₀, h1, rfl⟩) | ⟨h0, rfl⟩
  · simp only [gEval, h0]; rfl
  · simp only [gEval, h0, hitGuard]
    split_ifs with hi
    · rw [← h1, ← h2, ← encCV_init]
      exact decide_eq_decide.mpr ⟨fun h => by rw [h], fun h => encCV_inj h⟩
    · rfl
  · simp only [gEval, h0, missGuard]
    by_cases hi : i = i₀
    · subst hi; rw [if_pos rfl, if_pos h1]
    · have : i.val ≠ gd.getD 1 0 := fun h => hi (Fin.ext (h.trans h1.symm))
      rw [if_neg hi, if_neg this]
  · simp only [gEval, h0]

/-- **Domains of schemas from their records.** -/
lemma mem_domain_of_schRec {x : List Bool} {ℓ H N : ℕ} {sc : Schema (s + 1) ℓ N}
    {rec : List ℕ} (h : SchRec M x s ℓ H sc rec) (c : Coord (s + 1) ℓ) :
    c ∈ sc.domain ↔ c.1.val = s ∨ gEval x ℓ H (rec.drop 5) c.1.val (regVal c.2) = true := by
  obtain ⟨g, hg, hm⟩ := h
  rw [hm.2.2.2.2.2.2.2, mem_guardDomain_toGuard]
  split_ifs with hc
  · rw [gEval_spec hg]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · omega
      · exact h
  · have : c.1.val = s := by have := c.1.isLt; omega
    simp [this]

end Lax119563Proofs.Reduction
